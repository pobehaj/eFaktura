#!/usr/bin/env python3
"""
eFaktúry — Offline & Peppol desktopová aplikácia v jednom súbore.
Závislosti: pip install reportlab qrcode pillow
"""

from __future__ import annotations

import datetime
import decimal
import hashlib
import io
import json
import lzma
import os
import re
import sqlite3
import struct
import subprocess
import sys
import threading
import tkinter as tk
import urllib.error
import urllib.parse
import urllib.request
import uuid
import xml.etree.ElementTree as ET
import zlib
from decimal import Decimal, ROUND_HALF_UP
from pathlib import Path
from tkinter import filedialog, messagebox, ttk
from xml.sax.saxutils import escape as xml_escape

try:
    import qrcode
    from reportlab.lib import colors
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.styles import ParagraphStyle
    from reportlab.lib.units import mm
    from reportlab.lib.utils import ImageReader
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.pdfmetrics import registerFontFamily
    from reportlab.pdfbase.ttfonts import TTFont
    from reportlab.platypus import (
        Image as RLImage,
        Paragraph,
        SimpleDocTemplate,
        Spacer,
        Table,
        TableStyle,
    )

    HAS_PDF_LIBS = True
    PDF_IMPORT_ERROR = ""
except ImportError as exc:
    HAS_PDF_LIBS = False
    PDF_IMPORT_ERROR = str(exc)


DB_PATH = Path("efaktury.sqlite")
PDF_DIR = Path("pdf")
B32HEX_ALPHABET = "0123456789ABCDEFGHIJKLMNOPQRSTUV"


# ---------------------------------------------------------------------------
# Presné výpočty (Decimal)
# ---------------------------------------------------------------------------

def parse_dec(val: str | int | float | None) -> Decimal:
    if val is None:
        return Decimal("0")
    s = str(val).strip().replace(",", ".")
    if not s:
        return Decimal("0")
    try:
        return Decimal(s)
    except decimal.InvalidOperation:
        return Decimal("0")


def round_2(d: Decimal) -> Decimal:
    return d.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)


def compute_line_decimals(qty: str, unit_price: str, vat_rate: str, is_vat_payer: bool) -> tuple[Decimal, Decimal, Decimal]:
    q = parse_dec(qty)
    p = parse_dec(unit_price)
    net = round_2(q * p)
    if is_vat_payer and str(vat_rate).strip():
        r = parse_dec(vat_rate)
        vat = round_2(net * r / Decimal("100"))
    else:
        vat = Decimal("0.00")
    return net, vat, net + vat


def compute_invoice_vat_totals(items: list[dict], is_vat_payer: bool) -> dict:
    net_total = Decimal("0.00")
    vat_total = Decimal("0.00")
    gross_total = Decimal("0.00")
    groups: dict[tuple[str, str], list[Decimal]] = {}

    for it in items:
        net, vat, gross = compute_line_decimals(
            it.get("quantity", "1"),
            it.get("unit_price", "0"),
            it.get("vat_rate", "0"),
            is_vat_payer,
        )
        net_total += net
        vat_total += vat
        gross_total += gross

        cat = (it.get("tax_category") or ("S" if is_vat_payer else "O")).strip() or "S"
        rate = str(it.get("vat_rate") or "0").strip()
        key = (cat, rate)
        if key not in groups:
            groups[key] = [Decimal("0.00"), Decimal("0.00"), Decimal("0.00")]
        groups[key][0] += net
        groups[key][1] += vat
        groups[key][2] += gross

    vat_summary = []
    for (cat, rate), (taxable, tax, gross) in sorted(groups.items(), key=lambda kv: (kv[0][0], parse_dec(kv[0][1]))):
        vat_summary.append({
            "category": cat,
            "rate": rate,
            "taxable_amount": f"{taxable:.2f}",
            "tax_amount": f"{tax:.2f}",
            "gross_amount": f"{gross:.2f}",
        })

    return {
        "total_without_vat": f"{net_total:.2f}",
        "total_vat": f"{vat_total:.2f}",
        "total_amount": f"{gross_total:.2f}",
        "vat_summary": vat_summary,
    }


# ---------------------------------------------------------------------------
# PAY by square 1.2.0 enkóder (čistý Python: zlib + lzma)
# ---------------------------------------------------------------------------

def iban_valid(iban: str) -> bool:
    if not (15 <= len(iban) <= 34) or not iban.isalnum():
        return False
    rearranged = iban[4:] + iban[:4]
    rem = 0
    for ch in rearranged:
        if ch.isdigit():
            rem = (rem * 10 + int(ch)) % 97
        elif "A" <= ch <= "Z":
            v = ord(ch) - ord("A") + 10
            rem = (rem * 10 + v // 10) % 97
            rem = (rem * 10 + v % 10) % 97
        else:
            return False
    return rem == 1


def base32hex_encode(data: bytes) -> str:
    out = []
    acc = 0
    nbits = 0
    for b in data:
        acc = (acc << 8) | b
        nbits += 8
        while nbits >= 5:
            nbits -= 5
            out.append(B32HEX_ALPHABET[(acc >> nbits) & 31])
        acc &= (1 << nbits) - 1 if nbits > 0 else 0
    if nbits > 0:
        out.append(B32HEX_ALPHABET[(acc << (5 - nbits)) & 31])
    return "".join(out)


def encode_pay_by_square(
    iban_raw: str,
    beneficiary_raw: str,
    amount_raw: str,
    currency_raw: str = "EUR",
    due_raw: str | None = None,
    vs_raw: str | None = None,
    ks_raw: str | None = None,
    ss_raw: str | None = None,
    note_raw: str | None = None,
    invoice_raw: str | None = None,
) -> str:
    iban = re.sub(r"\s+", "", iban_raw or "").upper()
    if not iban or not iban_valid(iban):
        raise ValueError(f"Neplatný IBAN '{iban}'")

    beneficiary = (beneficiary_raw or "").strip()[:70]
    if not beneficiary:
        raise ValueError("Meno príjemcu je povinné")

    amt_dec = round_2(parse_dec(amount_raw))
    if amt_dec <= Decimal("0.00"):
        raise ValueError("Suma pre PAY by square musí byť väčšia ako 0")
    amount = f"{amt_dec:.2f}"

    currency = (currency_raw or "EUR").strip().upper()
    if len(currency) != 3 or not currency.isalpha():
        raise ValueError("Neplatná mena")

    due_yyyymmdd = ""
    if due_raw and due_raw.strip():
        d = due_raw.strip()
        if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", d):
            raise ValueError(f"Neplatná splatnosť '{d}'")
        due_yyyymmdd = d.replace("-", "")

    vs = (vs_raw or "").strip()
    ks = (ks_raw or "").strip()
    ss = (ss_raw or "").strip()
    for label, val, limit in [("VS", vs, 10), ("KS", ks, 4), ("SS", ss, 10)]:
        if len(val) > limit or (val and not val.isdigit()):
            raise ValueError(f"{label} musí mať max {limit} číslic")

    note = (note_raw or "").strip()[:140]
    inv = (invoice_raw or "").strip()[:10]

    def clean(s: str) -> str:
        return s.replace("\t", " ").replace("\r", " ").replace("\n", " ")

    fields = [
        clean(inv),
        "1",
        "1",
        amount,
        currency,
        due_yyyymmdd,
        vs,
        ks,
        ss,
        "",
        clean(note),
        "1",
        iban,
        "",
        "0",
        "0",
        clean(beneficiary),
        "",
        "",
    ]
    seq = "\t".join(fields)
    if len(seq) > 550:
        raise ValueError("Dáta pre QR kód sú príliš dlhé (max 550 znakov)")

    seq_bytes = seq.encode("utf-8")
    crc = zlib.crc32(seq_bytes) & 0xFFFFFFFF
    uncompressed = struct.pack("<I", crc) + seq_bytes

    compressed = lzma.compress(
        uncompressed,
        format=lzma.FORMAT_RAW,
        filters=[{"id": lzma.FILTER_LZMA1, "lc": 3, "lp": 0, "pb": 2, "dict_size": 1 << 17}],
    )
    framed = b"\x00\x00" + struct.pack("<H", len(uncompressed)) + compressed
    return base32hex_encode(framed)


def make_qr_png_bytes(pay_str: str) -> bytes:
    qr = qrcode.QRCode(
        version=None,
        error_correction=qrcode.constants.ERROR_CORRECT_L,
        box_size=8,
        border=2,
    )
    qr.add_data(pay_str)
    qr.make(fit=True)
    img = qr.make_image(fill_color="black", back_color="white")
    buf = io.BytesIO()
    img.save(buf, format="PNG")
    return buf.getvalue()


# ---------------------------------------------------------------------------
# Databáza (SQLite — kompatibilná so schémou eFaktúry)
# ---------------------------------------------------------------------------

class Database:
    def __init__(self, db_path: Path):
        self.db_path = db_path
        self._init_schema()

    def _connect(self) -> sqlite3.Connection:
        conn = sqlite3.connect(self.db_path)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA foreign_keys=ON")
        return conn

    def _init_schema(self) -> None:
        with self._connect() as conn:
            conn.executescript(
                """
                CREATE TABLE IF NOT EXISTS invoices (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    direction TEXT NOT NULL,
                    external_document_id TEXT,
                    invoice_number TEXT NOT NULL,
                    issue_date TEXT NOT NULL,
                    due_date TEXT,
                    currency TEXT NOT NULL DEFAULT 'EUR',
                    total_amount TEXT NOT NULL DEFAULT '0.00',
                    supplier_name TEXT NOT NULL,
                    supplier_ico TEXT,
                    supplier_dic TEXT,
                    supplier_icdph TEXT,
                    supplier_address TEXT,
                    supplier_iban TEXT,
                    customer_name TEXT NOT NULL,
                    customer_ico TEXT,
                    customer_dic TEXT,
                    customer_icdph TEXT,
                    customer_address TEXT,
                    customer_peppol_id TEXT,
                    variable_symbol TEXT,
                    constant_symbol TEXT,
                    specific_symbol TEXT,
                    payment_note TEXT,
                    include_qr INTEGER NOT NULL DEFAULT 1,
                    include_signature INTEGER NOT NULL DEFAULT 0,
                    is_vat_payer INTEGER NOT NULL DEFAULT 1,
                    document_type TEXT NOT NULL DEFAULT 'invoice',
                    delivery_date TEXT,
                    related_invoice_id INTEGER,
                    related_invoice_number TEXT,
                    related_invoice_date TEXT,
                    correction_reason TEXT,
                    buyer_reference TEXT,
                    customer_street TEXT,
                    customer_city TEXT,
                    customer_postal_zone TEXT,
                    customer_country_code TEXT DEFAULT 'SK',
                    total_without_vat TEXT NOT NULL DEFAULT '0.00',
                    total_vat TEXT NOT NULL DEFAULT '0.00',
                    status TEXT NOT NULL DEFAULT 'local',
                    sent_at TEXT,
                    raw_xml TEXT,
                    raw_json TEXT,
                    pdf_path TEXT,
                    pdf_template_name TEXT,
                    pdf_template_sha256 TEXT,
                    created_at TEXT NOT NULL DEFAULT (datetime('now')),
                    updated_at TEXT NOT NULL DEFAULT (datetime('now'))
                );

                CREATE TABLE IF NOT EXISTS invoice_items (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    invoice_id INTEGER NOT NULL REFERENCES invoices(id) ON DELETE CASCADE,
                    position INTEGER NOT NULL,
                    description TEXT NOT NULL,
                    quantity TEXT NOT NULL,
                    unit TEXT NOT NULL DEFAULT 'ks',
                    unit_price TEXT NOT NULL,
                    vat_rate TEXT NOT NULL DEFAULT '23',
                    tax_category TEXT NOT NULL DEFAULT 'S',
                    line_net TEXT NOT NULL DEFAULT '0.00',
                    line_vat TEXT NOT NULL DEFAULT '0.00',
                    line_total TEXT NOT NULL
                );

                CREATE TABLE IF NOT EXISTS invoice_events (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    invoice_id INTEGER NOT NULL REFERENCES invoices(id) ON DELETE CASCADE,
                    event_type TEXT NOT NULL,
                    details TEXT,
                    created_at TEXT NOT NULL DEFAULT (datetime('now'))
                );

                CREATE TABLE IF NOT EXISTS customers (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    name TEXT NOT NULL,
                    ico TEXT,
                    dic TEXT,
                    icdph TEXT,
                    street TEXT NOT NULL DEFAULT '',
                    city TEXT NOT NULL DEFAULT '',
                    postal_zone TEXT NOT NULL DEFAULT '',
                    country_code TEXT NOT NULL DEFAULT 'SK',
                    peppol_id TEXT,
                    email TEXT,
                    phone TEXT,
                    note TEXT,
                    verified_peppol INTEGER NOT NULL DEFAULT 0,
                    created_at TEXT NOT NULL DEFAULT (datetime('now')),
                    updated_at TEXT NOT NULL DEFAULT (datetime('now'))
                );

                CREATE TABLE IF NOT EXISTS settings (
                    key TEXT PRIMARY KEY,
                    value TEXT NOT NULL,
                    updated_at TEXT NOT NULL DEFAULT (datetime('now'))
                );

                CREATE TABLE IF NOT EXISTS sync_log (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    provider TEXT NOT NULL,
                    trigger_type TEXT NOT NULL,
                    status TEXT NOT NULL,
                    fetched_count INTEGER NOT NULL DEFAULT 0,
                    acknowledged_count INTEGER NOT NULL DEFAULT 0,
                    message TEXT,
                    created_at TEXT NOT NULL DEFAULT (datetime('now'))
                );
                """
            )
            # Dopĺňanie stĺpcov pri staršej databáze
            inv_cols = {r[1] for r in conn.execute("PRAGMA table_info(invoices)").fetchall()}
            extra_inv = [
                ("customer_peppol_id", "TEXT"),
                ("include_qr", "INTEGER NOT NULL DEFAULT 1"),
                ("include_signature", "INTEGER NOT NULL DEFAULT 0"),
                ("is_vat_payer", "INTEGER NOT NULL DEFAULT 1"),
                ("sent_at", "TEXT"),
                ("document_type", "TEXT NOT NULL DEFAULT 'invoice'"),
                ("delivery_date", "TEXT"),
                ("related_invoice_id", "INTEGER"),
                ("related_invoice_number", "TEXT"),
                ("related_invoice_date", "TEXT"),
                ("correction_reason", "TEXT"),
                ("buyer_reference", "TEXT"),
                ("customer_street", "TEXT"),
                ("customer_city", "TEXT"),
                ("customer_postal_zone", "TEXT"),
                ("customer_country_code", "TEXT DEFAULT 'SK'"),
                ("total_without_vat", "TEXT NOT NULL DEFAULT '0.00'"),
                ("total_vat", "TEXT NOT NULL DEFAULT '0.00'"),
            ]
            for col, col_def in extra_inv:
                if col not in inv_cols:
                    conn.execute(f"ALTER TABLE invoices ADD COLUMN {col} {col_def}")

            it_cols = {r[1] for r in conn.execute("PRAGMA table_info(invoice_items)").fetchall()}
            for col, col_def in [
                ("tax_category", "TEXT NOT NULL DEFAULT 'S'"),
                ("line_net", "TEXT NOT NULL DEFAULT '0.00'"),
                ("line_vat", "TEXT NOT NULL DEFAULT '0.00'"),
            ]:
                if col not in it_cols:
                    conn.execute(f"ALTER TABLE invoice_items ADD COLUMN {col} {col_def}")

    def list_invoices(self, direction: str) -> list[dict]:
        with self._connect() as conn:
            rows = conn.execute(
                "SELECT * FROM invoices WHERE direction = ? ORDER BY issue_date DESC, id DESC",
                (direction,),
            ).fetchall()
            return [dict(r) for r in rows]

    def get_invoice(self, invoice_id: int) -> tuple[dict, list[dict]] | None:
        with self._connect() as conn:
            inv = conn.execute("SELECT * FROM invoices WHERE id = ?", (invoice_id,)).fetchone()
            if not inv:
                return None
            items = conn.execute(
                "SELECT * FROM invoice_items WHERE invoice_id = ? ORDER BY position ASC",
                (invoice_id,),
            ).fetchall()
            return dict(inv), [dict(x) for x in items]

    def invoice_exists_by_external_id(self, ext_id: str) -> bool:
        with self._connect() as conn:
            cnt = conn.execute(
                "SELECT COUNT(*) FROM invoices WHERE external_document_id = ?",
                (ext_id,),
            ).fetchone()[0]
            return cnt > 0

    def insert_invoice(self, data: dict) -> int:
        doc_type = data.get("document_type") or "invoice"
        if doc_type != "invoice" and not (data.get("related_invoice_number") or "").strip():
            raise ValueError("Opravný doklad / dobropis musí mať vyplnené číslo pôvodného dokladu.")

        is_vat_payer = bool(data.get("is_vat_payer", True))
        items = data.get("items") or []

        net_total = Decimal("0.00")
        vat_total = Decimal("0.00")
        gross_total = Decimal("0.00")
        computed_items = []

        for item in items:
            if is_vat_payer:
                vat_rate_str = str(item.get("vat_rate") or "23")
                cat = (item.get("tax_category") or "S").strip() or "S"
                net, vat, gross = compute_line_decimals(
                    item.get("quantity", "1"),
                    item.get("unit_price", "0"),
                    vat_rate_str,
                    True,
                )
            else:
                vat_rate_str = "0"
                cat = "O"
                net, vat, gross = compute_line_decimals(
                    item.get("quantity", "1"),
                    item.get("unit_price", "0"),
                    "0",
                    False,
                )
                if net == Decimal("0.00") and parse_dec(item.get("line_total")) != Decimal("0.00"):
                    tot = round_2(parse_dec(item.get("line_total")))
                    net, vat, gross = tot, Decimal("0.00"), tot

            net_total += net
            vat_total += vat
            gross_total += gross
            computed_items.append((item, vat_rate_str, cat, net, vat, gross))

        if not items:
            gross_total = round_2(parse_dec(data.get("total_amount")))
            net_total = gross_total

        total_without_vat = f"{net_total:.2f}" if is_vat_payer else f"{gross_total:.2f}"
        total_vat = f"{vat_total:.2f}"
        total_amount = f"{gross_total:.2f}"

        with self._connect() as conn:
            cur = conn.execute(
                """
                INSERT INTO invoices (
                    direction, external_document_id, invoice_number, issue_date, due_date,
                    currency, total_amount, supplier_name, supplier_ico, supplier_dic,
                    supplier_icdph, supplier_address, supplier_iban, customer_name, customer_ico,
                    customer_dic, customer_icdph, customer_address, customer_peppol_id,
                    variable_symbol, constant_symbol, specific_symbol, payment_note,
                    include_qr, include_signature, is_vat_payer,
                    document_type, delivery_date, related_invoice_id, related_invoice_number,
                    related_invoice_date, correction_reason, buyer_reference,
                    customer_street, customer_city, customer_postal_zone, customer_country_code,
                    total_without_vat, total_vat, status, raw_xml, raw_json
                ) VALUES (
                    ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?,
                    ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?,
                    ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?
                )
                """,
                (
                    data.get("direction", "issued"),
                    data.get("external_document_id"),
                    data["invoice_number"],
                    data["issue_date"],
                    data.get("due_date"),
                    data.get("currency", "EUR"),
                    total_amount,
                    data.get("supplier_name", ""),
                    data.get("supplier_ico"),
                    data.get("supplier_dic"),
                    data.get("supplier_icdph"),
                    data.get("supplier_address"),
                    data.get("supplier_iban"),
                    data["customer_name"],
                    data.get("customer_ico"),
                    data.get("customer_dic"),
                    data.get("customer_icdph"),
                    data.get("customer_address"),
                    data.get("customer_peppol_id"),
                    data.get("variable_symbol"),
                    data.get("constant_symbol"),
                    data.get("specific_symbol"),
                    data.get("payment_note"),
                    1 if data.get("include_qr", True) else 0,
                    1 if data.get("include_signature", False) else 0,
                    1 if is_vat_payer else 0,
                    doc_type,
                    data.get("delivery_date"),
                    data.get("related_invoice_id"),
                    data.get("related_invoice_number"),
                    data.get("related_invoice_date"),
                    data.get("correction_reason"),
                    data.get("buyer_reference"),
                    data.get("customer_street"),
                    data.get("customer_city"),
                    data.get("customer_postal_zone"),
                    data.get("customer_country_code") or "SK",
                    total_without_vat,
                    total_vat,
                    data.get("status", "local"),
                    data.get("raw_xml"),
                    data.get("raw_json"),
                ),
            )
            inv_id = cur.lastrowid

            for idx, (item, vat_rate_str, cat, net, vat, gross) in enumerate(computed_items, start=1):
                conn.execute(
                    """
                    INSERT INTO invoice_items (
                        invoice_id, position, description, quantity, unit, unit_price,
                        vat_rate, tax_category, line_net, line_vat, line_total
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """,
                    (
                        inv_id,
                        idx,
                        item["description"],
                        str(item["quantity"]),
                        item.get("unit") or "ks",
                        str(item["unit_price"]),
                        vat_rate_str,
                        cat,
                        f"{net:.2f}",
                        f"{vat:.2f}",
                        f"{gross:.2f}",
                    ),
                )

            conn.execute(
                "INSERT INTO invoice_events (invoice_id, event_type, details) VALUES (?, 'created', ?)",
                (inv_id, f"Faktúra uložená ({data.get('direction', 'issued')})"),
            )
            return inv_id

    def mark_pdf_generated(self, invoice_id: int, pdf_path: str) -> None:
        with self._connect() as conn:
            conn.execute(
                "UPDATE invoices SET pdf_path = ?, pdf_template_name = 'reportlab', updated_at = datetime('now') WHERE id = ?",
                (pdf_path, invoice_id),
            )
            conn.execute(
                "INSERT INTO invoice_events (invoice_id, event_type, details) VALUES (?, 'pdf_generated', ?)",
                (invoice_id, pdf_path),
            )

    def mark_invoice_sent(self, invoice_id: int, ext_doc_id: str, raw_xml: str) -> None:
        with self._connect() as conn:
            conn.execute(
                """
                UPDATE invoices
                SET status = 'sent', external_document_id = ?, raw_xml = ?,
                    sent_at = datetime('now'), updated_at = datetime('now')
                WHERE id = ?
                """,
                (ext_doc_id, raw_xml, invoice_id),
            )
            conn.execute(
                "INSERT INTO invoice_events (invoice_id, event_type, details) VALUES (?, 'sent_to_web', ?)",
                (invoice_id, ext_doc_id),
            )

    def delete_local_invoice(self, invoice_id: int) -> str | None:
        with self._connect() as conn:
            row = conn.execute("SELECT status, pdf_path FROM invoices WHERE id = ?", (invoice_id,)).fetchone()
            if not row:
                return None
            if row["status"] == "sent":
                raise ValueError("Odoslanú faktúru nie je možné zmazať, použite dobropis alebo opravnú faktúru.")
            conn.execute("DELETE FROM invoices WHERE id = ?", (invoice_id,))
            return row["pdf_path"]

    def list_customers(self) -> list[dict]:
        with self._connect() as conn:
            return [dict(r) for r in conn.execute("SELECT * FROM customers ORDER BY name ASC").fetchall()]

    def upsert_customer(self, cust_id: int | None, data: dict) -> int:
        with self._connect() as conn:
            if cust_id is not None:
                conn.execute(
                    """
                    UPDATE customers SET
                        name = ?, ico = ?, dic = ?, icdph = ?,
                        street = ?, city = ?, postal_zone = ?, country_code = ?,
                        peppol_id = ?, email = ?, phone = ?, note = ?,
                        updated_at = datetime('now')
                    WHERE id = ?
                    """,
                    (
                        data["name"],
                        data.get("ico"),
                        data.get("dic"),
                        data.get("icdph"),
                        data.get("street") or "",
                        data.get("city") or "",
                        data.get("postal_zone") or "",
                        data.get("country_code") or "SK",
                        data.get("peppol_id"),
                        data.get("email"),
                        data.get("phone"),
                        data.get("note"),
                        cust_id,
                    ),
                )
                return cust_id
            cur = conn.execute(
                """
                INSERT INTO customers (
                    name, ico, dic, icdph, street, city, postal_zone, country_code,
                    peppol_id, email, phone, note
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    data["name"],
                    data.get("ico"),
                    data.get("dic"),
                    data.get("icdph"),
                    data.get("street") or "",
                    data.get("city") or "",
                    data.get("postal_zone") or "",
                    data.get("country_code") or "SK",
                    data.get("peppol_id"),
                    data.get("email"),
                    data.get("phone"),
                    data.get("note"),
                ),
            )
            return cur.lastrowid

    def delete_customer(self, cust_id: int) -> None:
        with self._connect() as conn:
            conn.execute("DELETE FROM customers WHERE id = ?", (cust_id,))

    def get_all_settings(self) -> dict[str, str]:
        with self._connect() as conn:
            rows = conn.execute("SELECT key, value FROM settings").fetchall()
            return {r["key"]: r["value"] for r in rows}

    def save_settings(self, mapping: dict[str, str]) -> None:
        with self._connect() as conn:
            for k, v in mapping.items():
                conn.execute(
                    """
                    INSERT INTO settings (key, value, updated_at) VALUES (?, ?, datetime('now'))
                    ON CONFLICT(key) DO UPDATE SET value = excluded.value, updated_at = datetime('now')
                    """,
                    (k, str(v)),
                )

    def record_sync_log(self, provider: str, trigger_type: str, status: str, fetched: int, acked: int, message: str) -> None:
        with self._connect() as conn:
            conn.execute(
                """
                INSERT INTO sync_log (provider, trigger_type, status, fetched_count, acknowledged_count, message)
                VALUES (?, ?, ?, ?, ?, ?)
                """,
                (provider, trigger_type, status, fetched, acked, message),
            )

    def list_sync_logs(self, limit: int = 30) -> list[dict]:
        with self._connect() as conn:
            rows = conn.execute("SELECT * FROM sync_log ORDER BY id DESC LIMIT ?", (limit,)).fetchall()
            return [dict(r) for r in rows]


# ---------------------------------------------------------------------------
# UBL 2.1 XML generátor a parser
# ---------------------------------------------------------------------------

UNIT_TO_UNECE = {
    "ks": "H87", "kus": "H87", "ks.": "H87",
    "hod": "HUR", "h": "HUR",
    "den": "DAY", "d": "DAY",
    "mes": "MON", "mesiac": "MON",
    "rok": "ANN", "r": "ANN",
    "km": "KMT",
    "kg": "KGM", "kg.": "KGM",
    "g": "GRM",
    "m": "MTR", "m.": "MTR",
    "l": "LTR", "l.": "LTR",
    "m2": "M2", "m²": "M2",
    "kWh": "KWH", "kwh": "KWH",
    "t": "TNE", "t.": "TNE",
}

UNECE_TO_UNIT = {
    "H87": "ks", "C62": "ks", "EA": "ks",
    "HUR": "hod", "DAY": "den", "MON": "mes", "ANN": "rok",
    "KMT": "km", "KGM": "kg", "GRM": "g", "MTR": "m",
    "LTR": "l", "M2": "m2", "MTK": "m2", "KWH": "kWh", "TNE": "t",
}


def build_ubl_invoice_xml(inv: dict, items: list[dict]) -> str:
    cur = inv.get("currency") or "EUR"
    issue = inv["issue_date"]
    due = inv.get("due_date") or issue
    num = inv["invoice_number"]
    doc_type = inv.get("document_type") or "invoice"
    is_credit = doc_type in ("credit_note", "credit_note_correction")
    is_vat = bool(inv.get("is_vat_payer", 1))

    type_code = "384" if doc_type == "corrective_invoice" else ("381" if is_credit else "380")
    root_tag = "CreditNote" if is_credit else "Invoice"
    type_tag = "CreditNoteTypeCode" if is_credit else "InvoiceTypeCode"
    tax_point = inv.get("delivery_date") or issue
    buyer_ref = (inv.get("buyer_reference") or "").strip() or num

    parts = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        f'<{root_tag} xmlns="urn:oasis:names:specification:ubl:schema:xsd:{root_tag}-2"',
        '         xmlns:cac="urn:oasis:names:specification:ubl:schema:xsd:CommonAggregateComponents-2"',
        '         xmlns:cbc="urn:oasis:names:specification:ubl:schema:xsd:CommonBasicComponents-2">',
        '  <cbc:CustomizationID>urn:cen.eu:en16931:2017#compliant#urn:fdc:peppol.eu:2017:poacc:billing:3.0</cbc:CustomizationID>',
        '  <cbc:ProfileID>urn:fdc:peppol.eu:2017:poacc:billing:01:1.0</cbc:ProfileID>',
        f'  <cbc:ID>{xml_escape(num)}</cbc:ID>',
        f'  <cbc:IssueDate>{xml_escape(issue)}</cbc:IssueDate>',
    ]
    if not is_credit:
        parts.append(f'  <cbc:DueDate>{xml_escape(due)}</cbc:DueDate>')
    parts.extend([
        f'  <cbc:{type_tag}>{type_code}</cbc:{type_tag}>',
        f'  <cbc:DocumentCurrencyCode>{xml_escape(cur)}</cbc:DocumentCurrencyCode>',
        f'  <cbc:BuyerReference>{xml_escape(buyer_ref)}</cbc:BuyerReference>',
        f'  <cbc:TaxPointDate>{xml_escape(tax_point)}</cbc:TaxPointDate>',
    ])

    rel_num = (inv.get("related_invoice_number") or "").strip()
    if rel_num:
        ref_tag = "CreditNoteDocumentReference" if doc_type == "credit_note_correction" else "InvoiceDocumentReference"
        rel_date = (inv.get("related_invoice_date") or "").strip()
        parts.append("  <cac:BillingReference>")
        parts.append(f"    <cac:{ref_tag}>")
        parts.append(f"      <cbc:ID>{xml_escape(rel_num)}</cbc:ID>")
        if rel_date:
            parts.append(f"      <cbc:IssueDate>{xml_escape(rel_date)}</cbc:IssueDate>")
        parts.append(f"    </cac:{ref_tag}>")
        parts.append("  </cac:BillingReference>")

    # Dodávateľ
    sup_dic = inv.get("supplier_dic") or "0000000000"
    sup_name = inv.get("supplier_name") or ""
    sup_addr = (inv.get("supplier_address") or "Slovensko").strip()
    sup_ico = inv.get("supplier_ico") or ""
    sup_icdph = inv.get("supplier_icdph") or ""
    parts.extend([
        "  <cac:AccountingSupplierParty>",
        "    <cac:Party>",
        f'      <cbc:EndpointID schemeID="0245">{xml_escape(sup_dic)}</cbc:EndpointID>',
        f'      <cac:PartyName><cbc:Name>{xml_escape(sup_name)}</cbc:Name></cac:PartyName>',
        "      <cac:PostalAddress>",
        f'        <cbc:StreetName>{xml_escape(sup_addr)}</cbc:StreetName>',
        "        <cac:Country><cbc:IdentificationCode>SK</cbc:IdentificationCode></cac:Country>",
        "      </cac:PostalAddress>",
        "      <cac:PartyLegalEntity>",
        f'        <cbc:RegistrationName>{xml_escape(sup_name)}</cbc:RegistrationName>',
        f'        <cbc:CompanyID schemeID="IC">{xml_escape(sup_ico)}</cbc:CompanyID>',
        "      </cac:PartyLegalEntity>",
    ])
    if is_vat and sup_icdph:
        parts.extend([
            "      <cac:PartyTaxScheme>",
            f'        <cbc:CompanyID>{xml_escape(sup_icdph)}</cbc:CompanyID>',
            "        <cac:TaxScheme><cbc:ID>VAT</cbc:ID></cac:TaxScheme>",
            "      </cac:PartyTaxScheme>",
        ])
    parts.extend(["    </cac:Party>", "  </cac:AccountingSupplierParty>"])

    # Odberateľ
    cust_dic = inv.get("customer_dic") or "0000000000"
    cust_name = inv.get("customer_name") or ""
    street = (inv.get("customer_street") or "").strip()
    city = (inv.get("customer_city") or "").strip()
    psc = (inv.get("customer_postal_zone") or "").strip()
    country = (inv.get("customer_country_code") or "SK").strip()
    if not street and not city:
        street = (inv.get("customer_address") or "Slovensko").strip()
    parts.extend([
        "  <cac:AccountingCustomerParty>",
        "    <cac:Party>",
        f'      <cbc:EndpointID schemeID="0245">{xml_escape(cust_dic)}</cbc:EndpointID>',
        f'      <cac:PartyName><cbc:Name>{xml_escape(cust_name)}</cbc:Name></cac:PartyName>',
        "      <cac:PostalAddress>",
        f'        <cbc:StreetName>{xml_escape(street)}</cbc:StreetName>',
        f'        <cbc:CityName>{xml_escape(city)}</cbc:CityName>',
        f'        <cbc:PostalZone>{xml_escape(psc)}</cbc:PostalZone>',
        f'        <cac:Country><cbc:IdentificationCode>{xml_escape(country)}</cbc:IdentificationCode></cac:Country>',
        "      </cac:PostalAddress>",
        "      <cac:PartyLegalEntity>",
        f'        <cbc:RegistrationName>{xml_escape(cust_name)}</cbc:RegistrationName>',
        f'        <cbc:CompanyID schemeID="IC">{xml_escape(inv.get("customer_ico") or "")}</cbc:CompanyID>',
        "      </cac:PartyLegalEntity>",
        "    </cac:Party>",
        "  </cac:AccountingCustomerParty>",
    ])

    # Platba
    vs = inv.get("variable_symbol") or num
    iban = inv.get("supplier_iban") or ""
    parts.append("  <cac:PaymentMeans>")
    parts.append("    <cbc:PaymentMeansCode>30</cbc:PaymentMeansCode>")
    if is_credit:
        parts.append(f"    <cbc:PaymentDueDate>{xml_escape(due)}</cbc:PaymentDueDate>")
    parts.append(f"    <cbc:PaymentID>{xml_escape(vs)}</cbc:PaymentID>")
    parts.append(f"    <cac:PayeeFinancialAccount><cbc:ID>{xml_escape(iban)}</cbc:ID></cac:PayeeFinancialAccount>")
    parts.append("  </cac:PaymentMeans>")

    # Dane
    totals = compute_invoice_vat_totals(items, is_vat)
    if not is_vat:
        parts.extend([
            "  <cac:TaxTotal>",
            f'    <cbc:TaxAmount currencyID="{xml_escape(cur)}">0.00</cbc:TaxAmount>',
            "    <cac:TaxSubtotal>",
            f'      <cbc:TaxableAmount currencyID="{xml_escape(cur)}">{xml_escape(inv["total_amount"])}</cbc:TaxableAmount>',
            f'      <cbc:TaxAmount currencyID="{xml_escape(cur)}">0.00</cbc:TaxAmount>',
            "      <cac:TaxCategory>",
            "        <cbc:ID>O</cbc:ID>",
            "        <cbc:TaxExemptionReason>Dodávateľ nie je platca DPH.</cbc:TaxExemptionReason>",
            "        <cac:TaxScheme><cbc:ID>VAT</cbc:ID></cac:TaxScheme>",
            "      </cac:TaxCategory>",
            "    </cac:TaxSubtotal>",
            "  </cac:TaxTotal>",
        ])
    else:
        parts.append("  <cac:TaxTotal>")
        parts.append(f'    <cbc:TaxAmount currencyID="{xml_escape(cur)}">{totals["total_vat"]}</cbc:TaxAmount>')
        for s in totals["vat_summary"]:
            parts.extend([
                "    <cac:TaxSubtotal>",
                f'      <cbc:TaxableAmount currencyID="{xml_escape(cur)}">{s["taxable_amount"]}</cbc:TaxableAmount>',
                f'      <cbc:TaxAmount currencyID="{xml_escape(cur)}">{s["tax_amount"]}</cbc:TaxAmount>',
                "      <cac:TaxCategory>",
                f'        <cbc:ID>{xml_escape(s["category"])}</cbc:ID>',
                f'        <cbc:Percent>{xml_escape(s["rate"])}</cbc:Percent>',
                "        <cac:TaxScheme><cbc:ID>VAT</cbc:ID></cac:TaxScheme>",
                "      </cac:TaxCategory>",
                "    </cac:TaxSubtotal>",
            ])
        parts.append("  </cac:TaxTotal>")

    net_tot = totals["total_without_vat"] if is_vat else inv["total_amount"]
    gross_tot = inv["total_amount"]
    parts.extend([
        "  <cac:LegalMonetaryTotal>",
        f'    <cbc:LineExtensionAmount currencyID="{xml_escape(cur)}">{xml_escape(net_tot)}</cbc:LineExtensionAmount>',
        f'    <cbc:TaxExclusiveAmount currencyID="{xml_escape(cur)}">{xml_escape(net_tot)}</cbc:TaxExclusiveAmount>',
        f'    <cbc:TaxInclusiveAmount currencyID="{xml_escape(cur)}">{xml_escape(gross_tot)}</cbc:TaxInclusiveAmount>',
        f'    <cbc:PayableAmount currencyID="{xml_escape(cur)}">{xml_escape(gross_tot)}</cbc:PayableAmount>',
        "  </cac:LegalMonetaryTotal>",
    ])

    line_tag = "CreditNoteLine" if is_credit else "InvoiceLine"
    qty_tag = "CreditedQuantity" if is_credit else "InvoicedQuantity"
    for it in items:
        ucode = UNIT_TO_UNECE.get((it.get("unit") or "ks").strip(), "EA")
        line_net = it["line_net"] if is_vat else it["line_total"]
        parts.extend([
            f"  <cac:{line_tag}>",
            f'    <cbc:ID>{it["position"]}</cbc:ID>',
            f'    <cbc:{qty_tag} unitCode="{ucode}">{xml_escape(str(it["quantity"]))}</cbc:{qty_tag}>',
            f'    <cbc:LineExtensionAmount currencyID="{xml_escape(cur)}">{xml_escape(str(line_net))}</cbc:LineExtensionAmount>',
            "    <cac:Item>",
            f'      <cbc:Name>{xml_escape(it["description"])}</cbc:Name>',
            "      <cac:ClassifiedTaxCategory>",
            f'        <cbc:ID>{"O" if not is_vat else xml_escape(it.get("tax_category") or "S")}</cbc:ID>',
            *([f'        <cbc:Percent>{xml_escape(str(it.get("vat_rate") or "0"))}</cbc:Percent>'] if is_vat else []),
            "        <cac:TaxScheme><cbc:ID>VAT</cbc:ID></cac:TaxScheme>",
            "      </cac:ClassifiedTaxCategory>",
            "    </cac:Item>",
            f'    <cac:Price><cbc:PriceAmount currencyID="{xml_escape(cur)}">{xml_escape(str(it["unit_price"]))}</cbc:PriceAmount></cac:Price>',
            f"  </cac:{line_tag}>",
        ])

    parts.append(f"</{root_tag}>")
    return "\n".join(parts) + "\n"


def _local(tag: str) -> str:
    return tag.split("}", 1)[-1]


def _find_text(elem: ET.Element | None, *rel_paths: str) -> str | None:
    if elem is None:
        return None
    for path in rel_paths:
        cur: ET.Element | None = elem
        for part in path.split("/"):
            nxt = None
            for child in cur:
                if _local(child.tag) == part:
                    nxt = child
                    break
            cur = nxt
            if cur is None:
                break
        if cur is not None and cur.text and cur.text.strip():
            return cur.text.strip()
    return None


def parse_ubl_invoice(external_doc_id: str, xml_str: str) -> dict:
    root = ET.fromstring(xml_str)
    root_name = _local(root.tag)
    is_credit = root_name == "CreditNote"

    inv_num = _find_text(root, "ID") or external_doc_id
    issue_date = _find_text(root, "IssueDate") or datetime.date.today().isoformat()
    due_date = _find_text(root, "DueDate", "PaymentMeans/PaymentDueDate")
    delivery_date = _find_text(root, "TaxPointDate", "Delivery/ActualDeliveryDate")
    buyer_ref = _find_text(root, "BuyerReference")
    note = _find_text(root, "Note")

    currency = "EUR"
    payable = _find_text(root, "LegalMonetaryTotal/PayableAmount") or "0.00"
    for el in root.iter():
        if _local(el.tag) == "PayableAmount" and el.attrib.get("currencyID"):
            currency = el.attrib["currencyID"]
            break

    sup_party = None
    cust_party = None
    for child in root:
        if _local(child.tag) == "AccountingSupplierParty":
            for sub in child:
                if _local(sub.tag) == "Party":
                    sup_party = sub
        elif _local(child.tag) == "AccountingCustomerParty":
            for sub in child:
                if _local(sub.tag) == "Party":
                    cust_party = sub

    sup_name = _find_text(sup_party, "PartyName/Name", "PartyLegalEntity/RegistrationName") or "Neznámy dodávateľ"
    sup_ico = _find_text(sup_party, "PartyLegalEntity/CompanyID")
    sup_tax_id = _find_text(sup_party, "PartyTaxScheme/CompanyID")
    sup_dic = None
    sup_icdph = None
    if sup_tax_id:
        if sup_tax_id[0].isalpha():
            sup_icdph = sup_tax_id
        else:
            sup_dic = sup_tax_id
    if not sup_dic:
        ep = _find_text(sup_party, "EndpointID")
        if ep:
            sup_dic = ep.split(":")[-1]

    s_street = _find_text(sup_party, "PostalAddress/StreetName")
    s_city = _find_text(sup_party, "PostalAddress/CityName")
    s_psc = _find_text(sup_party, "PostalAddress/PostalZone")
    sup_addr_parts = [p for p in [s_street, " ".join(x for x in [s_psc, s_city] if x)] if p]
    sup_addr = ", ".join(sup_addr_parts) if sup_addr_parts else None

    cust_name = _find_text(cust_party, "PartyName/Name", "PartyLegalEntity/RegistrationName") or "Odberateľ"
    cust_ico = _find_text(cust_party, "PartyLegalEntity/CompanyID")
    cust_dic = _find_text(cust_party, "PartyTaxScheme/CompanyID")
    c_street = _find_text(cust_party, "PostalAddress/StreetName")
    c_city = _find_text(cust_party, "PostalAddress/CityName")
    c_psc = _find_text(cust_party, "PostalAddress/PostalZone")
    c_country = _find_text(cust_party, "PostalAddress/Country/IdentificationCode") or "SK"

    iban = _find_text(root, "PaymentMeans/PayeeFinancialAccount/ID")
    vs = _find_text(root, "PaymentMeans/PaymentID")
    if not vs:
        digits = "".join(ch for ch in inv_num if ch.isdigit())
        if 0 < len(digits) <= 10:
            vs = digits

    rel_num = _find_text(
        root,
        "BillingReference/InvoiceDocumentReference/ID",
        "BillingReference/CreditNoteDocumentReference/ID",
    )
    rel_date = _find_text(
        root,
        "BillingReference/InvoiceDocumentReference/IssueDate",
        "BillingReference/CreditNoteDocumentReference/IssueDate",
    )

    items = []
    for child in root:
        ln = _local(child.tag)
        if ln in ("InvoiceLine", "CreditNoteLine"):
            qty_el = None
            for sub in child:
                if _local(sub.tag) in ("InvoicedQuantity", "CreditedQuantity"):
                    qty_el = sub
                    break
            qty = qty_el.text.strip() if (qty_el is not None and qty_el.text) else "1"
            unit_code = qty_el.attrib.get("unitCode", "H87") if qty_el is not None else "H87"
            unit = UNECE_TO_UNIT.get(unit_code, "ks")
            desc = _find_text(child, "Item/Name", "Item/Description") or "Položka"
            price = _find_text(child, "Price/PriceAmount") or _find_text(child, "LineExtensionAmount") or "0.00"
            cat = _find_text(child, "Item/ClassifiedTaxCategory/ID") or "S"
            rate = _find_text(child, "Item/ClassifiedTaxCategory/Percent") or "0"
            net_d, vat_d, gross_d = compute_line_decimals(qty, price, rate, cat != "O")
            items.append({
                "description": desc,
                "quantity": qty,
                "unit": unit,
                "unit_price": price,
                "vat_rate": rate,
                "tax_category": cat,
                "line_total": f"{gross_d:.2f}",
            })

    total_vat_xml = _find_text(root, "TaxTotal/TaxAmount")
    if items:
        is_vat_payer = not all(it["tax_category"] == "O" and parse_dec(it["vat_rate"]) == 0 for it in items)
    else:
        is_vat_payer = parse_dec(total_vat_xml) > 0 if total_vat_xml else True
        items = [{
            "description": f"Prijatý doklad č. {inv_num}",
            "quantity": "1",
            "unit": "ks",
            "unit_price": payable,
            "vat_rate": "0",
            "tax_category": "S" if is_vat_payer else "O",
            "line_total": payable,
        }]

    return {
        "direction": "received",
        "external_document_id": external_doc_id,
        "invoice_number": inv_num,
        "issue_date": issue_date,
        "due_date": due_date,
        "delivery_date": delivery_date,
        "currency": currency,
        "total_amount": payable,
        "supplier_name": sup_name,
        "supplier_ico": sup_ico,
        "supplier_dic": sup_dic,
        "supplier_icdph": sup_icdph,
        "supplier_address": sup_addr,
        "supplier_iban": iban,
        "customer_name": cust_name,
        "customer_ico": cust_ico,
        "customer_dic": cust_dic,
        "customer_street": c_street,
        "customer_city": c_city,
        "customer_postal_zone": c_psc,
        "customer_country_code": c_country,
        "variable_symbol": vs,
        "payment_note": note,
        "buyer_reference": buyer_ref,
        "document_type": "credit_note" if is_credit else "invoice",
        "related_invoice_number": rel_num,
        "related_invoice_date": rel_date,
        "include_qr": True,
        "include_signature": False,
        "is_vat_payer": is_vat_payer,
        "status": "received",
        "raw_xml": xml_str,
        "items": items,
    }


# ---------------------------------------------------------------------------
# PDF generátor (ReportLab — TTF fonty + neprepisuje existujúce PDF)
# ---------------------------------------------------------------------------

def _register_fonts() -> tuple[str, str]:
    """Registruje Roboto alebo systémový TTF font so slovenskou diakritikou."""
    candidates_reg = [
        Path("templates/invoice/fonts/Roboto-Regular.ttf"),
        Path("/usr/share/fonts/TTF/Roboto-Regular.ttf"),
        Path("/usr/share/fonts/truetype/roboto/Roboto-Regular.ttf"),
        Path("/usr/share/fonts/TTF/DejaVuSans.ttf"),
        Path("/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"),
        Path("/usr/share/fonts/liberation/LiberationSans-Regular.ttf"),
        Path("/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf"),
        Path("C:/Windows/Fonts/arial.ttf"),
    ]
    candidates_bold = [
        Path("templates/invoice/fonts/Roboto-Bold.ttf"),
        Path("/usr/share/fonts/TTF/Roboto-Bold.ttf"),
        Path("/usr/share/fonts/truetype/roboto/Roboto-Bold.ttf"),
        Path("/usr/share/fonts/TTF/DejaVuSans-Bold.ttf"),
        Path("/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf"),
        Path("/usr/share/fonts/liberation/LiberationSans-Bold.ttf"),
        Path("/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf"),
        Path("C:/Windows/Fonts/arialbd.ttf"),
    ]

    reg_path = next((p for p in candidates_reg if p.exists()), None)
    bold_path = next((p for p in candidates_bold if p.exists()), None)
    if not reg_path:
        # Fallback vyhľadanie v /usr/share/fonts
        for root_dir in [Path("/usr/share/fonts"), Path("/usr/local/share/fonts")]:
            if root_dir.exists():
                ttfs = list(root_dir.rglob("*.ttf"))
                if ttfs:
                    reg_path = ttfs[0]
                    break

    if not reg_path:
        return "Helvetica", "Helvetica-Bold"

    if not bold_path:
        bold_path = reg_path

    if "InvFont" not in pdfmetrics.getRegisteredFontNames():
        pdfmetrics.registerFont(TTFont("InvFont", str(reg_path)))
        pdfmetrics.registerFont(TTFont("InvFont-Bold", str(bold_path)))
        registerFontFamily("InvFont", normal="InvFont", bold="InvFont-Bold")
    return "InvFont", "InvFont-Bold"


def ensure_or_generate_pdf(db: Database, invoice_id: int, settings: dict[str, str], force: bool = False) -> Path:
    if not HAS_PDF_LIBS:
        raise RuntimeError(
            f"Chýbajú knižnice pre PDF ({PDF_IMPORT_ERROR}).\n"
            "Nainštaluj ich príkazom: pip install reportlab qrcode pillow"
        )

    res = db.get_invoice(invoice_id)
    if not res:
        raise ValueError(f"Faktúra {invoice_id} neexistuje")
    inv, items = res

    if not force and inv.get("pdf_path"):
        existing = Path(inv["pdf_path"])
        if existing.exists():
            return existing

    font_reg, font_bold = _register_fonts()
    PDF_DIR.mkdir(parents=True, exist_ok=True)
    safe_num = "".join(c if (c.isalnum() or c in "-_") else "_" for c in inv["invoice_number"])
    out_path = PDF_DIR / f"{safe_num}-{inv['id']}.pdf"

    is_vat = bool(inv.get("is_vat_payer", 1))
    cur = inv.get("currency") or "EUR"
    doc_type = inv.get("document_type") or "invoice"
    title = {
        "corrective_invoice": "OPRAVNÁ FAKTÚRA",
        "credit_note": "DOBROPIS",
        "credit_note_correction": "OPRAVA DOBROPISU",
    }.get(doc_type, "FAKTÚRA")

    pri = colors.HexColor("#1e3a5f")
    muted = colors.HexColor("#64748b")
    border = colors.HexColor("#cbd5e1")
    bg_light = colors.HexColor("#f8fafc")

    st_norm = ParagraphStyle("n", fontName=font_reg, fontSize=9, leading=12, textColor=colors.HexColor("#0f172a"))
    st_bold = ParagraphStyle("b", fontName=font_bold, fontSize=9, leading=12, textColor=colors.HexColor("#0f172a"))
    st_muted = ParagraphStyle("m", fontName=font_reg, fontSize=8, leading=10.5, textColor=muted)
    st_title = ParagraphStyle("t", fontName=font_bold, fontSize=18, leading=22, textColor=pri)
    st_th = ParagraphStyle("th", fontName=font_bold, fontSize=8.5, leading=11, textColor=colors.white)

    doc = SimpleDocTemplate(
        str(out_path),
        pagesize=A4,
        leftMargin=15 * mm,
        rightMargin=15 * mm,
        topMargin=14 * mm,
        bottomMargin=14 * mm,
    )
    story = []

    # Hlavička (+ voliteľné logo)
    logo_path_str = settings.get("pdf.logo_path", "").strip()
    if not logo_path_str:
        for cand in [Path("templates/invoice/assets/logo.png"), Path("templates/invoice/assets/logo.jpg")]:
            if cand.exists():
                logo_path_str = str(cand)
                break
    logo_flowable: object = ""
    if logo_path_str and Path(logo_path_str).exists():
        try:
            ir = ImageReader(logo_path_str)
            iw, ih = ir.getSize()
            h = 14 * mm
            w = h * (iw / ih) if ih else 25 * mm
            logo_flowable = RLImage(logo_path_str, width=w, height=h)
        except Exception:
            logo_flowable = ""

    head_tbl = Table(
        [[
            [Paragraph(xml_escape(title), st_title), Paragraph(f"Číslo dokladu: <b>{xml_escape(inv['invoice_number'])}</b>", st_bold)],
            logo_flowable,
        ]],
        colWidths=[125 * mm, 55 * mm],
    )
    head_tbl.setStyle(TableStyle([
        ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
        ("ALIGN", (1, 0), (1, 0), "RIGHT"),
        ("LINEBELOW", (0, 0), (-1, 0), 1.5, pri),
        ("BOTTOMPADDING", (0, 0), (-1, 0), 6),
    ]))
    story.append(head_tbl)
    story.append(Spacer(1, 5 * mm))

    # Väzba na pôvodný doklad
    rel_num = (inv.get("related_invoice_number") or "").strip()
    corr_reason = (inv.get("correction_reason") or "").strip()
    if rel_num or corr_reason:
        rel_lines = []
        if rel_num:
            rd = f" (zo dňa {xml_escape(inv['related_invoice_date'])})" if inv.get("related_invoice_date") else ""
            rel_lines.append(f"<b>Pôvodný doklad:</b> {xml_escape(rel_num)}{rd}")
        if corr_reason:
            rel_lines.append(f"<b>Dôvod opravy:</b> {xml_escape(corr_reason)}")
        rel_tbl = Table([[Paragraph("<br/>".join(rel_lines), st_norm)]], colWidths=[180 * mm])
        rel_tbl.setStyle(TableStyle([
            ("BACKGROUND", (0, 0), (-1, -1), colors.HexColor("#fffbeb")),
            ("BOX", (0, 0), (-1, -1), 0.75, colors.HexColor("#fcd34d")),
            ("TOPPADDING", (0, 0), (-1, -1), 5),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 5),
            ("LEFTPADDING", (0, 0), (-1, -1), 8),
        ]))
        story.append(rel_tbl)
        story.append(Spacer(1, 4 * mm))

    # Dodávateľ a Odberateľ
    sup_lines = ["<font size='8' color='#64748b'><b>DODÁVATEĽ</b></font>", f"<b>{xml_escape(inv['supplier_name'])}</b>"]
    if inv.get("supplier_address"):
        sup_lines.append(xml_escape(inv["supplier_address"]))
    if inv.get("supplier_ico"):
        sup_lines.append(f"IČO: {xml_escape(inv['supplier_ico'])}")
    if inv.get("supplier_dic"):
        sup_lines.append(f"DIČ: {xml_escape(inv['supplier_dic'])}")
    if is_vat and inv.get("supplier_icdph"):
        sup_lines.append(f"IČ DPH: {xml_escape(inv['supplier_icdph'])}")
    if not is_vat:
        sup_lines.append("<font size='8' color='#64748b'><i>Dodávateľ nie je platca DPH.</i></font>")

    cust_lines = ["<font size='8' color='#64748b'><b>ODBERATEĽ</b></font>", f"<b>{xml_escape(inv['customer_name'])}</b>"]
    c_street = (inv.get("customer_street") or "").strip()
    c_city_psc = " ".join(x for x in [(inv.get("customer_postal_zone") or "").strip(), (inv.get("customer_city") or "").strip()] if x)
    if c_street:
        cust_lines.append(xml_escape(c_street))
    if c_city_psc:
        cust_lines.append(xml_escape(c_city_psc))
    if not c_street and not c_city_psc and inv.get("customer_address"):
        cust_lines.append(xml_escape(inv["customer_address"]))
    if inv.get("customer_ico"):
        cust_lines.append(f"IČO: {xml_escape(inv['customer_ico'])}")
    if inv.get("customer_dic"):
        cust_lines.append(f"DIČ: {xml_escape(inv['customer_dic'])}")
    if inv.get("customer_icdph"):
        cust_lines.append(f"IČ DPH: {xml_escape(inv['customer_icdph'])}")

    party_tbl = Table(
        [[Paragraph("<br/>".join(sup_lines), st_norm), Paragraph("<br/>".join(cust_lines), st_norm)]],
        colWidths=[88 * mm, 88 * mm],
    )
    party_tbl.setStyle(TableStyle([
        ("VALIGN", (0, 0), (-1, -1), "TOP"),
        ("BACKGROUND", (0, 0), (-1, -1), bg_light),
        ("BOX", (0, 0), (0, 0), 0.75, border),
        ("BOX", (1, 0), (1, 0), 0.75, border),
        ("TOPPADDING", (0, 0), (-1, -1), 7),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 7),
        ("LEFTPADDING", (0, 0), (-1, -1), 8),
        ("RIGHTPADDING", (0, 0), (-1, -1), 8),
    ]))
    story.append(party_tbl)
    story.append(Spacer(1, 4 * mm))

    # Dátumy a platobné údaje
    col1 = [f"<font size='8' color='#64748b'>Dátum vystavenia:</font> <b>{xml_escape(inv['issue_date'])}</b>"]
    if inv.get("delivery_date"):
        col1.append(f"<font size='8' color='#64748b'>Dátum dodania:</font> <b>{xml_escape(inv['delivery_date'])}</b>")
    col2 = [f"<font size='8' color='#64748b'>Dátum splatnosti:</font> <b>{xml_escape(inv.get('due_date') or '-')}</b>"]
    if inv.get("variable_symbol"):
        col2.append(f"<font size='8' color='#64748b'>Variabilný symbol:</font> <b>{xml_escape(inv['variable_symbol'])}</b>")
    col3 = ["<font size='8' color='#64748b'>Spôsob úhrady:</font> <b>Bankový prevod</b>"]
    if inv.get("supplier_iban"):
        col3.append(f"<font size='8' color='#64748b'>IBAN:</font> <b>{xml_escape(inv['supplier_iban'])}</b>")

    meta_tbl = Table(
        [[Paragraph("<br/>".join(col1), st_norm), Paragraph("<br/>".join(col2), st_norm), Paragraph("<br/>".join(col3), st_norm)]],
        colWidths=[55 * mm, 55 * mm, 70 * mm],
    )
    meta_tbl.setStyle(TableStyle([
        ("VALIGN", (0, 0), (-1, -1), "TOP"),
        ("BOX", (0, 0), (-1, -1), 0.75, border),
        ("TOPPADDING", (0, 0), (-1, -1), 6),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 6),
        ("LEFTPADDING", (0, 0), (-1, -1), 7),
    ]))
    story.append(meta_tbl)

    if inv.get("payment_note"):
        story.append(Spacer(1, 2 * mm))
        story.append(Paragraph(f"Poznámka: {xml_escape(inv['payment_note'])}", st_muted))

    story.append(Spacer(1, 5 * mm))

    # Tabuľka položiek — všetky údaje v jednom riadku
    if is_vat:
        rows_data = [[
            Paragraph("#", st_th),
            Paragraph("Popis položky", st_th),
            Paragraph("Množ.", st_th),
            Paragraph("Jedn.", st_th),
            Paragraph("Cena/j. bez DPH", st_th),
            Paragraph("DPH", st_th),
            Paragraph("Spolu s DPH", st_th),
        ]]
        for it in items:
            rows_data.append([
                Paragraph(str(it["position"]), st_norm),
                Paragraph(xml_escape(it["description"]), st_norm),
                Paragraph(xml_escape(str(it["quantity"])), st_norm),
                Paragraph(xml_escape(it["unit"]), st_norm),
                Paragraph(f"{xml_escape(str(it['unit_price']))} {cur}", st_norm),
                Paragraph(f"{xml_escape(str(it['vat_rate']))} %", st_norm),
                Paragraph(f"<b>{xml_escape(str(it['line_total']))} {cur}</b>", st_bold),
            ])
        item_widths = [9 * mm, 69 * mm, 16 * mm, 14 * mm, 28 * mm, 15 * mm, 29 * mm]
    else:
        rows_data = [[
            Paragraph("#", st_th),
            Paragraph("Popis položky", st_th),
            Paragraph("Množstvo", st_th),
            Paragraph("Jedn.", st_th),
            Paragraph("Cena za 1 jedn.", st_th),
            Paragraph("Spolu", st_th),
        ]]
        for it in items:
            rows_data.append([
                Paragraph(str(it["position"]), st_norm),
                Paragraph(xml_escape(it["description"]), st_norm),
                Paragraph(xml_escape(str(it["quantity"])), st_norm),
                Paragraph(xml_escape(it["unit"]), st_norm),
                Paragraph(f"{xml_escape(str(it['unit_price']))} {cur}", st_norm),
                Paragraph(f"<b>{xml_escape(str(it['line_total']))} {cur}</b>", st_bold),
            ])
        item_widths = [10 * mm, 82 * mm, 20 * mm, 16 * mm, 26 * mm, 26 * mm]

    items_tbl = Table(rows_data, colWidths=item_widths, repeatRows=1)
    items_tbl.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, 0), pri),
        ("ROWBACKGROUNDS", (0, 1), (-1, -1), [colors.white, bg_light]),
        ("GRID", (0, 0), (-1, -1), 0.5, border),
        ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
        ("TOPPADDING", (0, 0), (-1, -1), 5),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 5),
        ("LEFTPADDING", (0, 0), (-1, -1), 5),
        ("RIGHTPADDING", (0, 0), (-1, -1), 5),
    ]))
    story.append(items_tbl)
    story.append(Spacer(1, 6 * mm))

    # Spodná časť: Rekapitulácia DPH + podpis vľavo | Celkom + QR vpravo
    left_flow: list = []
    totals = compute_invoice_vat_totals(items, is_vat)
    if is_vat and totals["vat_summary"]:
        left_flow.append(Paragraph("<b>REKAPITULÁCIA DPH</b>", st_muted))
        left_flow.append(Spacer(1, 2 * mm))
        v_rows = [["Sadzba", "Základ", "DPH", "Spolu"]]
        for v in totals["vat_summary"]:
            v_rows.append([f"{v['rate']} %", f"{v['taxable_amount']} {cur}", f"{v['tax_amount']} {cur}", f"{v['gross_amount']} {cur}"])
        vt = Table(v_rows, colWidths=[18 * mm, 26 * mm, 24 * mm, 26 * mm])
        vt.setStyle(TableStyle([
            ("FONTNAME", (0, 0), (-1, 0), font_bold),
            ("FONTNAME", (0, 1), (-1, -1), font_reg),
            ("FONTSIZE", (0, 0), (-1, -1), 8),
            ("BACKGROUND", (0, 0), (-1, 0), bg_light),
            ("GRID", (0, 0), (-1, -1), 0.5, border),
            ("ALIGN", (0, 0), (-1, -1), "RIGHT"),
        ]))
        left_flow.append(vt)
    elif not is_vat:
        left_flow.append(Paragraph("<i>Nie som platca DPH. Faktúra je bez DPH.</i>", st_muted))

    if inv.get("include_signature"):
        sig_path_str = settings.get("pdf.signature_path", "").strip()
        if not sig_path_str:
            for cand in [Path("templates/invoice/assets/signature.png"), Path("templates/invoice/assets/signature.jpg")]:
                if cand.exists():
                    sig_path_str = str(cand)
                    break
        if sig_path_str and Path(sig_path_str).exists():
            try:
                ir = ImageReader(sig_path_str)
                iw, ih = ir.getSize()
                sh = 18 * mm
                sw = sh * (iw / ih) if ih else 35 * mm
                left_flow.append(Spacer(1, 6 * mm))
                left_flow.append(RLImage(sig_path_str, width=sw, height=sh))
                left_flow.append(Paragraph("Podpis a pečiatka", st_muted))
            except Exception:
                pass

    right_flow: list = []
    tot_lines = []
    if is_vat:
        tot_lines.append(f"Základ bez DPH: <b>{totals['total_without_vat']} {cur}</b>")
        tot_lines.append(f"DPH celkom: <b>{totals['total_vat']} {cur}</b>")
    tot_lines.append("<font size='8' color='#64748b'>CELKOM K ÚHRADE</font>")
    tot_lines.append(f"<font size='14' color='#1e3a5f'><b>{xml_escape(inv['total_amount'])} {cur}</b></font>")

    sum_box = Table([[Paragraph("<br/>".join(tot_lines), st_norm)]], colWidths=[66 * mm])
    sum_box.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, -1), bg_light),
        ("BOX", (0, 0), (-1, -1), 1.2, pri),
        ("TOPPADDING", (0, 0), (-1, -1), 7),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 7),
        ("LEFTPADDING", (0, 0), (-1, -1), 9),
    ]))
    right_flow.append(sum_box)

    if inv.get("include_qr") and parse_dec(inv["total_amount"]) > Decimal("0") and (inv.get("supplier_iban") or "").strip():
        try:
            pay_str = encode_pay_by_square(
                iban_raw=inv["supplier_iban"],
                beneficiary_raw=inv["supplier_name"],
                amount_raw=inv["total_amount"],
                currency_raw=cur,
                due_raw=inv.get("due_date"),
                vs_raw=inv.get("variable_symbol"),
                ks_raw=inv.get("constant_symbol"),
                ss_raw=inv.get("specific_symbol"),
                note_raw=inv.get("payment_note"),
                invoice_raw=inv["invoice_number"],
            )
            qr_png = make_qr_png_bytes(pay_str)
            right_flow.append(Spacer(1, 4 * mm))
            right_flow.append(RLImage(io.BytesIO(qr_png), width=28 * mm, height=28 * mm))
            right_flow.append(Paragraph("<b>PAY by square</b>", ParagraphStyle("ql", fontName=font_bold, fontSize=8, textColor=pri)))
        except Exception as exc:
            print(f"QR kód pre faktúru {inv['invoice_number']} sa nevygeneroval: {exc}", file=sys.stderr)

    bottom_tbl = Table([[left_flow, right_flow]], colWidths=[110 * mm, 70 * mm])
    bottom_tbl.setStyle(TableStyle([
        ("VALIGN", (0, 0), (-1, -1), "TOP"),
        ("ALIGN", (1, 0), (1, 0), "RIGHT"),
    ]))
    story.append(bottom_tbl)

    footer_txt = settings.get("pdf.footer_text", "Ďakujeme za spoluprácu.").strip()
    if footer_txt:
        story.append(Spacer(1, 10 * mm))
        story.append(Paragraph(xml_escape(footer_txt), ParagraphStyle("ft", fontName=font_reg, fontSize=8.5, textColor=muted, alignment=1)))

    doc.build(story)
    db.mark_pdf_generated(invoice_id, str(out_path))
    return out_path


def open_file_externally(path: Path) -> None:
    if sys.platform.startswith("win"):
        os.startfile(str(path))  # type: ignore[attr-defined]
    elif sys.platform == "darwin":
        subprocess.Popen(["open", str(path)])
    else:
        subprocess.Popen(["xdg-open", str(path)])


# ---------------------------------------------------------------------------
# Externé API (RÚZ, Peppol Directory, SAPI-SK)
# ---------------------------------------------------------------------------

def http_json(url: str, method: str = "GET", headers: dict | None = None, payload: dict | None = None) -> dict:
    req_headers = {"Accept": "application/json"}
    if headers:
        req_headers.update(headers)
    data = None
    if payload is not None:
        data = json.dumps(payload).encode("utf-8")
        req_headers["Content-Type"] = "application/json"
    req = urllib.request.Request(url, data=data, headers=req_headers, method=method)
    with urllib.request.urlopen(req, timeout=20) as resp:
        raw = resp.read().decode("utf-8")
        return json.loads(raw) if raw.strip() else {}


def lookup_company_by_ico(ico: str) -> dict:
    ico = ico.strip()
    if len(ico) != 8 or not ico.isdigit():
        raise ValueError("IČO musí mať 8 číslic.")
    base = "https://www.registeruz.sk/cruz-public/api"
    list_val = http_json(f"{base}/uctovne-jednotky?zmenene-od=2000-01-01&max-zaznamov=1&ico={ico}")
    ids = list_val.get("id") or []
    if not ids:
        raise ValueError(f"V RÚZ sa nenašiel záznam pre IČO {ico}.")
    detail = http_json(f"{base}/uctovna-jednotka?id={ids[0]}")
    return {
        "name": (detail.get("nazovUJ") or "").strip(),
        "ico": ico,
        "dic": (detail.get("dic") or "").strip() or None,
        "icdph": (detail.get("icdph") or "").strip() or None,
        "street": (detail.get("ulica") or "").strip(),
        "city": (detail.get("mesto") or "").strip(),
        "postal_zone": (detail.get("psc") or "").strip(),
        "country_code": "SK",
    }


def lookup_peppol_participant(query_val: str) -> dict:
    q = query_val.strip()
    if not q:
        raise ValueError("Zadaj DIČ alebo Peppol ID.")
    for sandbox in (False, True):
        pid = q if ":" in q else f"{'9915' if sandbox else '0245'}:{q}"
        url = f"https://{'test-' if sandbox else ''}directory.peppol.eu/search/1.0/json?participant={urllib.parse.quote(pid)}"
        try:
            data = http_json(url)
            results = data.get("results") or []
            if results:
                return {"participant_id": pid, "registered": True, "name": results[0].get("legalRegistrationName")}
        except urllib.error.HTTPError as e:
            if e.code == 404:
                continue
            raise
    return {"participant_id": q if ":" in q else f"0245:{q}", "registered": False, "name": None}


def sapi_auth(settings: dict[str, str]) -> tuple[str, str, str, str]:
    base_url = (settings.get("sapi.base_url") or "https://api.efaktura.sk/sapi").rstrip("/")
    pid = (settings.get("sapi.participant_id") or "").strip()
    cid = (settings.get("sapi.client_id") or "").strip()
    csec = (settings.get("sapi.client_secret") or "").strip()
    if not pid or not cid or not csec:
        raise ValueError("Chýba Participant ID, Client ID alebo Client Secret v Nastaveniach.")
    tok = http_json(f"{base_url}/auth/token", method="POST", payload={"client_id": cid, "client_secret": csec})
    return base_url, pid, tok["access_token"], settings.get("sapi.environment", "sandbox")


def sapi_fetch_received(db: Database) -> str:
    settings = db.get_all_settings()
    base_url, pid, token, _ = sapi_auth(settings)
    headers = {"Authorization": f"Bearer {token}", "X-Peppol-Participant-Id": pid}
    fetched = 0
    acked = 0
    page_token = None
    while True:
        url = f"{base_url}/document/receive?status=RECEIVED&limit=100"
        if page_token:
            url += f"&pageToken={urllib.parse.quote(page_token)}"
        page = http_json(url, headers=headers)
        for doc in page.get("documents") or []:
            doc_id = doc["documentId"]
            if not db.invoice_exists_by_external_id(doc_id):
                detail = http_json(f"{base_url}/document/receive/{doc_id}", headers=headers)
                parsed = parse_ubl_invoice(doc_id, detail["payload"])
                parsed["raw_json"] = json.dumps(detail.get("metadata") or {})
                db.insert_invoice(parsed)
                fetched += 1
            http_json(f"{base_url}/document/receive/{doc_id}/acknowledge", method="POST", headers=headers)
            acked += 1
        page_token = page.get("nextPageToken")
        if not page_token:
            break
    msg = f"Načítané z webu: {fetched} nových, potvrdených {acked}."
    db.record_sync_log("sapi_sk", "manual", "ok", fetched, acked, msg)
    return msg


def sapi_send_invoice(db: Database, invoice_id: int) -> str:
    settings = db.get_all_settings()
    res = db.get_invoice(invoice_id)
    if not res:
        raise ValueError("Faktúra neexistuje.")
    inv, items = res
    if inv["direction"] != "issued":
        raise ValueError("Odoslať možno iba vystavenú faktúru.")

    base_url, sender_pid, token, _ = sapi_auth(settings)
    prefix = sender_pid.split(":")[0] if ":" in sender_pid else "9915"
    receiver_pid = (inv.get("customer_peppol_id") or "").strip() or (
        f"{prefix}:{inv['customer_dic'].strip()}" if (inv.get("customer_dic") or "").strip() else ""
    )
    if not receiver_pid:
        raise ValueError("Odberateľ musí mať vyplnené Peppol ID alebo DIČ.")

    ubl_xml = build_ubl_invoice_xml(inv, items)
    doc_id = inv.get("external_document_id") or f"INV-{inv['invoice_number']}-{inv['id']}"
    is_credit = (inv.get("document_type") or "") in ("credit_note", "credit_note_correction")
    doc_type_id = (
        "urn:oasis:names:specification:ubl:schema:xsd:CreditNote-2::CreditNote##urn:cen.eu:en16931:2017#compliant#urn:fdc:peppol.eu:2017:poacc:billing:3.0::2.1"
        if is_credit
        else "urn:oasis:names:specification:ubl:schema:xsd:Invoice-2::Invoice##urn:cen.eu:en16931:2017#compliant#urn:fdc:peppol.eu:2017:poacc:billing:3.0::2.1"
    )
    checksum = hashlib.sha256(ubl_xml.encode("utf-8")).hexdigest()
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    body = {
        "metadata": {
            "documentId": doc_id,
            "documentTypeId": doc_type_id,
            "processId": "urn:fdc:peppol.eu:2017:poacc:billing:01:1.0",
            "senderParticipantId": sender_pid,
            "receiverParticipantId": receiver_pid,
            "creationDateTime": now,
        },
        "payload": ubl_xml,
        "payloadFormat": "XML",
        "checksum": checksum,
    }
    headers = {
        "Authorization": f"Bearer {token}",
        "X-Peppol-Participant-Id": sender_pid,
        "Idempotency-Key": str(uuid.uuid4()),
    }
    http_json(f"{base_url}/document/send", method="POST", headers=headers, payload=body)
    db.mark_invoice_sent(invoice_id, doc_id, ubl_xml)
    return doc_id


# ---------------------------------------------------------------------------
# Desktopová GUI aplikácia (Tkinter)
# ---------------------------------------------------------------------------

class EFakturyApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("eFaktúry — Offline & Peppol")
        self.root.geometry("1120x700")
        self.db = Database(DB_PATH)

        style = ttk.Style()
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass

        self.status_var = tk.StringVar(value="Pripravené (lokálny offline režim)")

        self.notebook = ttk.Notebook(root)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=8, pady=(8, 0))

        self.tab_issued = ttk.Frame(self.notebook, padding=10)
        self.tab_received = ttk.Frame(self.notebook, padding=10)
        self.tab_customers = ttk.Frame(self.notebook, padding=10)
        self.tab_settings = ttk.Frame(self.notebook, padding=10)

        self.notebook.add(self.tab_issued, text="Odoslané faktúry")
        self.notebook.add(self.tab_received, text="Prijaté faktúry")
        self.notebook.add(self.tab_customers, text="Odberatelia")
        self.notebook.add(self.tab_settings, text="Nastavenia")

        self._build_issued_tab()
        self._build_received_tab()
        self._build_customers_tab()
        self._build_settings_tab()

        status_bar = ttk.Label(root, textvariable=self.status_var, relief=tk.SUNKEN, anchor=tk.W, padding=(8, 4))
        status_bar.pack(fill=tk.X, side=tk.BOTTOM)

        self.refresh_all()

    def set_status(self, text: str) -> None:
        self.status_var.set(text)

    def refresh_all(self) -> None:
        self.load_issued()
        self.load_received()
        self.load_customers()
        self.load_settings_ui()

    # ----- Odoslané faktúry -----

    def _build_issued_tab(self) -> None:
        bar = ttk.Frame(self.tab_issued)
        bar.pack(fill=tk.X, pady=(0, 8))
        ttk.Button(bar, text="+ Nová faktúra", command=self.open_new_invoice_dialog).pack(side=tk.LEFT, padx=(0, 6))
        ttk.Button(bar, text="Otvoriť / Generovať PDF", command=lambda: self.open_selected_pdf(self.tree_issued)).pack(side=tk.LEFT, padx=(0, 6))
        ttk.Button(bar, text="Exportovať UBL XML", command=self.export_selected_xml).pack(side=tk.LEFT, padx=(0, 6))
        ttk.Button(bar, text="Odoslať na web (SAPI-SK)", command=self.send_selected_to_web).pack(side=tk.LEFT, padx=(0, 6))
        ttk.Button(bar, text="Zmazať lokálnu", command=self.delete_selected_invoice).pack(side=tk.RIGHT)

        cols = ("id", "number", "customer", "issue", "delivery", "type", "total", "status")
        self.tree_issued = ttk.Treeview(self.tab_issued, columns=cols, show="headings", selectmode="browse")
        for c, h, w in [
            ("id", "ID", 45),
            ("number", "Číslo", 110),
            ("customer", "Odberateľ", 260),
            ("issue", "Vystavená", 95),
            ("delivery", "Dodanie", 95),
            ("type", "Typ", 120),
            ("total", "Suma", 110),
            ("status", "Stav", 130),
        ]:
            self.tree_issued.heading(c, text=h)
            self.tree_issued.column(c, width=w, anchor=tk.E if c in ("id", "total") else tk.W)
        self.tree_issued.pack(fill=tk.BOTH, expand=True)
        self.tree_issued.bind("<Double-1>", lambda _e: self.open_selected_pdf(self.tree_issued))

    def load_issued(self) -> None:
        self.tree_issued.delete(*self.tree_issued.get_children())
        type_map = {
            "invoice": "Faktúra",
            "corrective_invoice": "Opravná",
            "credit_note": "Dobropis",
            "credit_note_correction": "Oprava dobropisu",
        }
        for r in self.db.list_invoices("issued"):
            st = "Odoslaná na web" if r["status"] == "sent" else "Lokálna (offline)"
            self.tree_issued.insert("", tk.END, values=(
                r["id"],
                r["invoice_number"],
                r["customer_name"],
                r["issue_date"],
                r.get("delivery_date") or "—",
                type_map.get(r.get("document_type") or "invoice", "Faktúra"),
                f"{r['total_amount']} {r['currency']}",
                st,
            ))

    # ----- Prijaté faktúry -----

    def _build_received_tab(self) -> None:
        bar = ttk.Frame(self.tab_received)
        bar.pack(fill=tk.X, pady=(0, 8))
        ttk.Button(bar, text="Načítať z webu (SAPI-SK)", command=self.fetch_received_from_web).pack(side=tk.LEFT, padx=(0, 6))
        ttk.Button(bar, text="Importovať UBL XML zo súboru", command=self.import_ubl_file).pack(side=tk.LEFT, padx=(0, 6))
        ttk.Button(bar, text="Otvoriť / Generovať PDF", command=lambda: self.open_selected_pdf(self.tree_received)).pack(side=tk.LEFT)

        cols = ("id", "number", "supplier", "issue", "due", "total")
        self.tree_received = ttk.Treeview(self.tab_received, columns=cols, show="headings", selectmode="browse")
        for c, h, w in [
            ("id", "ID", 45),
            ("number", "Číslo", 130),
            ("supplier", "Dodávateľ", 320),
            ("issue", "Vystavená", 105),
            ("due", "Splatnosť", 105),
            ("total", "Suma", 120),
        ]:
            self.tree_received.heading(c, text=h)
            self.tree_received.column(c, width=w, anchor=tk.E if c in ("id", "total") else tk.W)
        self.tree_received.pack(fill=tk.BOTH, expand=True)
        self.tree_received.bind("<Double-1>", lambda _e: self.open_selected_pdf(self.tree_received))

    def load_received(self) -> None:
        self.tree_received.delete(*self.tree_received.get_children())
        for r in self.db.list_invoices("received"):
            self.tree_received.insert("", tk.END, values=(
                r["id"],
                r["invoice_number"],
                r["supplier_name"],
                r["issue_date"],
                r.get("due_date") or "—",
                f"{r['total_amount']} {r['currency']}",
            ))

    # ----- Odberatelia -----

    def _build_customers_tab(self) -> None:
        bar = ttk.Frame(self.tab_customers)
        bar.pack(fill=tk.X, pady=(0, 8))
        ttk.Button(bar, text="+ Nový odberateľ", command=lambda: self.open_customer_dialog(None)).pack(side=tk.LEFT, padx=(0, 6))
        ttk.Button(bar, text="Upraviť vybraného", command=self.edit_selected_customer).pack(side=tk.LEFT, padx=(0, 6))
        ttk.Button(bar, text="Zmazať vybraného", command=self.delete_selected_customer).pack(side=tk.RIGHT)

        cols = ("id", "name", "ico", "dic", "address", "peppol")
        self.tree_customers = ttk.Treeview(self.tab_customers, columns=cols, show="headings", selectmode="browse")
        for c, h, w in [
            ("id", "ID", 45),
            ("name", "Názov", 260),
            ("ico", "IČO", 95),
            ("dic", "DIČ", 110),
            ("address", "Adresa", 270),
            ("peppol", "Peppol ID", 150),
        ]:
            self.tree_customers.heading(c, text=h)
            self.tree_customers.column(c, width=w, anchor=tk.E if c == "id" else tk.W)
        self.tree_customers.pack(fill=tk.BOTH, expand=True)
        self.tree_customers.bind("<Double-1>", lambda _e: self.edit_selected_customer())

    def load_customers(self) -> None:
        self.tree_customers.delete(*self.tree_customers.get_children())
        for c in self.db.list_customers():
            addr = ", ".join(x for x in [c.get("street"), c.get("postal_zone"), c.get("city")] if x) or "—"
            self.tree_customers.insert("", tk.END, values=(
                c["id"],
                c["name"],
                c.get("ico") or "—",
                c.get("dic") or "—",
                addr,
                c.get("peppol_id") or "—",
            ))

    # ----- Nastavenia -----

    def _build_settings_tab(self) -> None:
        frm = ttk.Frame(self.tab_settings)
        frm.pack(fill=tk.BOTH, expand=True)

        left = ttk.LabelFrame(frm, text="Moja firma (predvolený dodávateľ)", padding=10)
        left.grid(row=0, column=0, sticky="nsew", padx=(0, 8))
        right = ttk.LabelFrame(frm, text="Integrácia SAPI-SK & PDF", padding=10)
        right.grid(row=0, column=1, sticky="nsew")
        frm.columnconfigure(0, weight=1)
        frm.columnconfigure(1, weight=1)

        self.set_vars: dict[str, tk.StringVar] = {}
        fields_left = [
            ("company.name", "Názov firmy"),
            ("company.ico", "IČO"),
            ("company.dic", "DIČ"),
            ("company.icdph", "IČ DPH"),
            ("company.address", "Adresa"),
            ("company.iban", "IBAN"),
        ]
        for idx, (k, label) in enumerate(fields_left):
            ttk.Label(left, text=label).grid(row=idx, column=0, sticky="w", pady=3)
            v = tk.StringVar()
            self.set_vars[k] = v
            ttk.Entry(left, textvariable=v, width=40).grid(row=idx, column=1, sticky="ew", pady=3, padx=(8, 0))
        left.columnconfigure(1, weight=1)

        self.var_comp_vat = tk.BooleanVar(value=False)
        ttk.Checkbutton(left, text="Som platca DPH", variable=self.var_comp_vat).grid(row=len(fields_left), column=1, sticky="w", pady=6)

        fields_right = [
            ("sapi.environment", "Prostredie (sandbox/production)"),
            ("sapi.base_url", "SAPI Base URL"),
            ("sapi.participant_id", "Peppol Participant ID"),
            ("sapi.client_id", "Client ID"),
            ("sapi.client_secret", "Client Secret"),
            ("pdf.footer_text", "Pätička PDF faktúry"),
            ("pdf.logo_path", "Cesta k logu (PNG/JPG)"),
            ("pdf.signature_path", "Cesta k podpisu (PNG/JPG)"),
        ]
        for idx, (k, label) in enumerate(fields_right):
            ttk.Label(right, text=label).grid(row=idx, column=0, sticky="w", pady=3)
            v = tk.StringVar()
            self.set_vars[k] = v
            show = "*" if "secret" in k else ""
            ttk.Entry(right, textvariable=v, width=40, show=show).grid(row=idx, column=1, sticky="ew", pady=3, padx=(8, 0))
        right.columnconfigure(1, weight=1)

        ttk.Button(frm, text="Uložiť nastavenia", command=self.save_settings_ui).grid(row=1, column=0, columnspan=2, pady=12, sticky="w")

        log_box = ttk.LabelFrame(frm, text="História komunikácie s webom", padding=8)
        log_box.grid(row=2, column=0, columnspan=2, sticky="nsew")
        frm.rowconfigure(2, weight=1)
        self.tree_logs = ttk.Treeview(log_box, columns=("time", "status", "count", "msg"), show="headings", height=6)
        for c, h, w in [("time", "Čas", 150), ("status", "Stav", 80), ("count", "Počet", 70), ("msg", "Správa", 550)]:
            self.tree_logs.heading(c, text=h)
            self.tree_logs.column(c, width=w)
        self.tree_logs.pack(fill=tk.BOTH, expand=True)

    def load_settings_ui(self) -> None:
        s = self.db.get_all_settings()
        for k, var in self.set_vars.items():
            default = ""
            if k == "sapi.base_url":
                default = "https://api.efaktura.sk/sapi"
            elif k == "sapi.environment":
                default = "sandbox"
            elif k == "pdf.footer_text":
                default = "Ďakujeme za spoluprácu."
            var.set(s.get(k, default))
        self.var_comp_vat.set(s.get("company.vat_payer") == "true")

        self.tree_logs.delete(*self.tree_logs.get_children())
        for l in self.db.list_sync_logs():
            self.tree_logs.insert("", tk.END, values=(l["created_at"], l["status"], l["fetched_count"], l.get("message") or ""))

    def save_settings_ui(self) -> None:
        mapping = {k: v.get().strip() for k, v in self.set_vars.items()}
        mapping["company.vat_payer"] = "true" if self.var_comp_vat.get() else "false"
        self.db.save_settings(mapping)
        self.set_status("Nastavenia boli uložené do SQLite.")
        messagebox.showinfo("Uložené", "Nastavenia boli uložené.")

    # ----- Akcie nad faktúrami -----

    def _selected_id(self, tree: ttk.Treeview) -> int | None:
        sel = tree.selection()
        if not sel:
            messagebox.showwarning("Výber", "Najprv vyber riadok v tabuľke.")
            return None
        return int(tree.item(sel[0], "values")[0])

    def open_selected_pdf(self, tree: ttk.Treeview) -> None:
        inv_id = self._selected_id(tree)
        if inv_id is None:
            return
        try:
            settings = self.db.get_all_settings()
            pdf_path = ensure_or_generate_pdf(self.db, inv_id, settings, force=False)
            self.set_status(f"PDF pripravené: {pdf_path}")
            open_file_externally(pdf_path)
        except Exception as exc:
            messagebox.showerror("Chyba PDF", str(exc))

    def export_selected_xml(self) -> None:
        inv_id = self._selected_id(self.tree_issued)
        if inv_id is None:
            return
        res = self.db.get_invoice(inv_id)
        if not res:
            return
        inv, items = res
        xml_str = build_ubl_invoice_xml(inv, items)
        path = filedialog.asksaveasfilename(
            defaultextension=".xml",
            initialfile=f"{inv['invoice_number']}.xml",
            filetypes=[("UBL XML", "*.xml")],
        )
        if path:
            Path(path).write_text(xml_str, encoding="utf-8")
            self.set_status(f"UBL XML uložené do {path}")

    def delete_selected_invoice(self) -> None:
        inv_id = self._selected_id(self.tree_issued)
        if inv_id is None:
            return
        if not messagebox.askyesno("Potvrdenie", "Naozaj zmazať túto lokálnu faktúru?"):
            return
        try:
            pdf_path = self.db.delete_local_invoice(inv_id)
            if pdf_path and Path(pdf_path).exists():
                Path(pdf_path).unlink()
            self.load_issued()
            self.set_status("Lokálna faktúra zmazaná.")
        except Exception as exc:
            messagebox.showerror("Chyba", str(exc))

    def import_ubl_file(self) -> None:
        path = filedialog.askopenfilename(filetypes=[("UBL XML súbory", "*.xml"), ("Všetky súbory", "*.*")])
        if not path:
            return
        try:
            xml_str = Path(path).read_text(encoding="utf-8")
            ext_id = f"LOCAL-{uuid.uuid4().hex[:10]}"
            parsed = parse_ubl_invoice(ext_id, xml_str)
            self.db.insert_invoice(parsed)
            self.load_received()
            self.set_status(f"Importovaný doklad {parsed['invoice_number']}")
        except Exception as exc:
            messagebox.showerror("Chyba importu XML", str(exc))

    def fetch_received_from_web(self) -> None:
        self.set_status("Sťahujem prijaté faktúry z webu...")

        def worker():
            try:
                msg = sapi_fetch_received(self.db)
                self.root.after(0, lambda: self._on_sync_done(msg, is_error=False))
            except Exception as exc:
                self.db.record_sync_log("sapi_sk", "manual", "error", 0, 0, str(exc))
                self.root.after(0, lambda m=str(exc): self._on_sync_done(m, is_error=True))

        threading.Thread(target=worker, daemon=True).start()

    def _on_sync_done(self, msg: str, is_error: bool) -> None:
        self.load_received()
        self.load_settings_ui()
        self.set_status(msg)
        if is_error:
            messagebox.showerror("Chyba SAPI-SK", msg)
        else:
            messagebox.showinfo("Synchronizácia", msg)

    def send_selected_to_web(self) -> None:
        inv_id = self._selected_id(self.tree_issued)
        if inv_id is None:
            return
        if not messagebox.askyesno("Odoslať na web", "Naozaj odoslať faktúru cez SAPI-SK?"):
            return
        self.set_status("Odosielam faktúru na web...")

        def worker():
            try:
                doc_id = sapi_send_invoice(self.db, inv_id)
                self.root.after(0, lambda: self._on_send_done(f"Faktúra odoslaná: {doc_id}", False))
            except Exception as exc:
                self.root.after(0, lambda m=str(exc): self._on_send_done(m, True))

        threading.Thread(target=worker, daemon=True).start()

    def _on_send_done(self, msg: str, is_error: bool) -> None:
        self.load_issued()
        self.set_status(msg)
        if is_error:
            messagebox.showerror("Chyba odoslania", msg)
        else:
            messagebox.showinfo("Odoslané", msg)

    # ----- Okno Odberateľa -----

    def edit_selected_customer(self) -> None:
        cid = self._selected_id(self.tree_customers)
        if cid is None:
            return
        cust = next((c for c in self.db.list_customers() if c["id"] == cid), None)
        if cust:
            self.open_customer_dialog(cust)

    def delete_selected_customer(self) -> None:
        cid = self._selected_id(self.tree_customers)
        if cid is None:
            return
        if messagebox.askyesno("Zmazať", "Naozaj zmazať vybraného odberateľa?"):
            self.db.delete_customer(cid)
            self.load_customers()

    def open_customer_dialog(self, existing: dict | None) -> None:
        win = tk.Toplevel(self.root)
        win.title("Odberateľ" if existing else "Nový odberateľ")
        win.geometry("520x470")
        win.grab_set()

        frm = ttk.Frame(win, padding=12)
        frm.pack(fill=tk.BOTH, expand=True)

        fields = [
            ("name", "Názov odberateľa *"),
            ("ico", "IČO (8 číslic)"),
            ("dic", "DIČ"),
            ("icdph", "IČ DPH"),
            ("street", "Ulica a číslo"),
            ("city", "Mesto"),
            ("postal_zone", "PSČ"),
            ("country_code", "Štát"),
            ("peppol_id", "Peppol ID"),
            ("email", "Email"),
            ("phone", "Telefón"),
            ("note", "Poznámka"),
        ]
        vars_map: dict[str, tk.StringVar] = {}
        for idx, (k, label) in enumerate(fields):
            ttk.Label(frm, text=label).grid(row=idx, column=0, sticky="w", pady=3)
            v = tk.StringVar(value=(existing.get(k) or "") if existing else ("SK" if k == "country_code" else ""))
            vars_map[k] = v
            ttk.Entry(frm, textvariable=v, width=36).grid(row=idx, column=1, sticky="ew", pady=3, padx=6)
            if k == "ico":
                ttk.Button(frm, text="Doplniť RÚZ", command=lambda: self._do_ico_lookup(vars_map, win)).grid(row=idx, column=2, padx=4)
            elif k == "peppol_id":
                ttk.Button(frm, text="Overiť Peppol", command=lambda: self._do_peppol_lookup(vars_map, win)).grid(row=idx, column=2, padx=4)
        frm.columnconfigure(1, weight=1)

        btns = ttk.Frame(frm)
        btns.grid(row=len(fields), column=0, columnspan=3, pady=12, sticky="e")
        ttk.Button(btns, text="Zrušiť", command=win.destroy).pack(side=tk.LEFT, padx=4)

        def save():
            name = vars_map["name"].get().strip()
            if not name:
                messagebox.showwarning("Chyba", "Názov odberateľa je povinný.", parent=win)
                return
            data = {k: (v.get().strip() or None) for k, v in vars_map.items()}
            data["name"] = name
            self.db.upsert_customer(existing["id"] if existing else None, data)
            self.load_customers()
            win.destroy()

        ttk.Button(btns, text="Uložiť odberateľa", command=save).pack(side=tk.LEFT)

    def _do_ico_lookup(self, vars_map: dict[str, tk.StringVar], parent: tk.Toplevel) -> None:
        ico = vars_map["ico"].get().strip()
        try:
            res = lookup_company_by_ico(ico)
            for k in ("name", "dic", "icdph", "street", "city", "postal_zone", "country_code"):
                vars_map[k].set(res.get(k) or "")
        except Exception as exc:
            messagebox.showerror("RÚZ Lookup", str(exc), parent=parent)

    def _do_peppol_lookup(self, vars_map: dict[str, tk.StringVar], parent: tk.Toplevel) -> None:
        q = vars_map["peppol_id"].get().strip() or vars_map["dic"].get().strip()
        try:
            res = lookup_peppol_participant(q)
            vars_map["peppol_id"].set(res["participant_id"])
            msg = (
                f"Peppol ID je registrovaný: {res['participant_id']}"
                if res["registered"]
                else f"Peppol ID {res['participant_id']} nie je v registri nájdený."
            )
            messagebox.showinfo("Peppol Directory", msg, parent=parent)
        except Exception as exc:
            messagebox.showerror("Peppol Lookup", str(exc), parent=parent)

    # ----- Okno Novej faktúry -----

    def open_new_invoice_dialog(self) -> None:
        settings = self.db.get_all_settings()
        customers = self.db.list_customers()
        today = datetime.date.today().isoformat()
        rand_num = f"{datetime.date.today().year}-{int(datetime.datetime.now().strftime('%H%M%S')) % 900 + 100}"

        win = tk.Toplevel(self.root)
        win.title("Nová faktúra (uloží sa lokálne)")
        win.geometry("880x700")
        win.grab_set()

        main = ttk.Frame(win, padding=12)
        main.pack(fill=tk.BOTH, expand=True)

        # Hlavička dokladu
        top = ttk.LabelFrame(main, text="Údaje dokladu", padding=8)
        top.pack(fill=tk.X, pady=(0, 8))

        v_num = tk.StringVar(value=rand_num)
        v_type = tk.StringVar(value="invoice")
        v_issue = tk.StringVar(value=today)
        v_delivery = tk.StringVar(value=today)
        v_due = tk.StringVar(value=today)
        v_vs = tk.StringVar(value="".join(ch for ch in rand_num if ch.isdigit()))
        v_rel_num = tk.StringVar()
        v_rel_date = tk.StringVar()
        v_reason = tk.StringVar()

        ttk.Label(top, text="Číslo faktúry").grid(row=0, column=0, sticky="w")
        ttk.Entry(top, textvariable=v_num, width=18).grid(row=0, column=1, padx=6, pady=2, sticky="ew")
        ttk.Label(top, text="Typ dokladu").grid(row=0, column=2, sticky="w")
        cb_type = ttk.Combobox(
            top,
            textvariable=v_type,
            values=["invoice", "corrective_invoice", "credit_note", "credit_note_correction"],
            state="readonly",
            width=22,
        )
        cb_type.grid(row=0, column=3, padx=6, pady=2, sticky="ew")
        ttk.Label(top, text="Variabilný symbol").grid(row=0, column=4, sticky="w")
        ttk.Entry(top, textvariable=v_vs, width=16).grid(row=0, column=5, padx=6, pady=2, sticky="ew")

        ttk.Label(top, text="Dátum vystavenia").grid(row=1, column=0, sticky="w")
        ttk.Entry(top, textvariable=v_issue, width=18).grid(row=1, column=1, padx=6, pady=2, sticky="ew")
        ttk.Label(top, text="Dátum dodania").grid(row=1, column=2, sticky="w")
        ttk.Entry(top, textvariable=v_delivery, width=18).grid(row=1, column=3, padx=6, pady=2, sticky="ew")
        ttk.Label(top, text="Dátum splatnosti").grid(row=1, column=4, sticky="w")
        ttk.Entry(top, textvariable=v_due, width=16).grid(row=1, column=5, padx=6, pady=2, sticky="ew")

        rel_frame = ttk.Frame(top)
        ttk.Label(rel_frame, text="Pôvodný doklad č.:").pack(side=tk.LEFT)
        ttk.Entry(rel_frame, textvariable=v_rel_num, width=16).pack(side=tk.LEFT, padx=6)
        ttk.Label(rel_frame, text="Dátum pôvodného:").pack(side=tk.LEFT)
        ttk.Entry(rel_frame, textvariable=v_rel_date, width=12).pack(side=tk.LEFT, padx=6)
        ttk.Label(rel_frame, text="Dôvod opravy:").pack(side=tk.LEFT)
        ttk.Entry(rel_frame, textvariable=v_reason, width=28).pack(side=tk.LEFT, padx=6, fill=tk.X, expand=True)

        def on_type_change(_e=None):
            if v_type.get() == "invoice":
                rel_frame.grid_forget()
            else:
                rel_frame.grid(row=2, column=0, columnspan=6, sticky="ew", pady=(6, 0))

        cb_type.bind("<<ComboboxSelected>>", on_type_change)

        # Odberateľ
        cust_box = ttk.LabelFrame(main, text="Odberateľ", padding=8)
        cust_box.pack(fill=tk.X, pady=(0, 8))

        v_cust_pick = tk.StringVar(value="— Nový / iný —")
        cust_names = ["— Nový / iný —"] + [f"{c['id']}: {c['name']}" for c in customers]
        cb_cust = ttk.Combobox(cust_box, textvariable=v_cust_pick, values=cust_names, state="readonly", width=45)
        cb_cust.grid(row=0, column=1, columnspan=3, sticky="ew", padx=6, pady=2)
        ttk.Label(cust_box, text="Vybrať uloženého:").grid(row=0, column=0, sticky="w")

        v_cname = tk.StringVar()
        v_cico = tk.StringVar()
        v_cdic = tk.StringVar()
        v_cpeppol = tk.StringVar()
        v_cstreet = tk.StringVar()
        v_ccity = tk.StringVar()
        v_cpsc = tk.StringVar()
        v_ccountry = tk.StringVar(value="SK")
        v_note = tk.StringVar()

        def on_pick_cust(_e=None):
            val = v_cust_pick.get()
            if ":" not in val:
                return
            cid = int(val.split(":", 1)[0])
            c = next((x for x in customers if x["id"] == cid), None)
            if not c:
                return
            v_cname.set(c["name"] or "")
            v_cico.set(c.get("ico") or "")
            v_cdic.set(c.get("dic") or "")
            v_cpeppol.set(c.get("peppol_id") or "")
            v_cstreet.set(c.get("street") or "")
            v_ccity.set(c.get("city") or "")
            v_cpsc.set(c.get("postal_zone") or "")
            v_ccountry.set(c.get("country_code") or "SK")

        cb_cust.bind("<<ComboboxSelected>>", on_pick_cust)

        cfields = [
            ("Názov *", v_cname, 1, 0),
            ("IČO", v_cico, 1, 2),
            ("DIČ", v_cdic, 1, 4),
            ("Ulica a č.", v_cstreet, 2, 0),
            ("Mesto", v_ccity, 2, 2),
            ("PSČ", v_cpsc, 2, 4),
            ("Peppol ID", v_cpeppol, 3, 0),
            ("Štát", v_ccountry, 3, 2),
            ("Poznámka", v_note, 3, 4),
        ]
        for lbl, var, r, col in cfields:
            ttk.Label(cust_box, text=lbl).grid(row=r, column=col, sticky="w")
            ttk.Entry(cust_box, textvariable=var, width=20).grid(row=r, column=col + 1, sticky="ew", padx=5, pady=2)
        for col in (1, 3, 5):
            cust_box.columnconfigure(col, weight=1)

        # Položky faktúry
        items_box = ttk.LabelFrame(main, text="Položky faktúry", padding=8)
        items_box.pack(fill=tk.BOTH, expand=True, pady=(0, 8))

        v_is_vat = tk.BooleanVar(value=(settings.get("company.vat_payer") == "true"))
        v_inc_qr = tk.BooleanVar(value=True)
        v_inc_sig = tk.BooleanVar(value=False)
        v_total_preview = tk.StringVar(value="0.00 EUR")

        hdr = ttk.Frame(items_box)
        hdr.pack(fill=tk.X, pady=(0, 4))
        ttk.Checkbutton(hdr, text="Som platca DPH", variable=v_is_vat, command=lambda: refresh_vat_visibility()).pack(side=tk.LEFT, padx=(0, 12))
        ttk.Checkbutton(hdr, text="Pridať QR kód do PDF", variable=v_inc_qr).pack(side=tk.LEFT, padx=(0, 12))
        ttk.Checkbutton(hdr, text="Pridať podpis/pečiatku", variable=v_inc_sig).pack(side=tk.LEFT)
        ttk.Button(hdr, text="+ Pridať položku", command=lambda: add_row()).pack(side=tk.RIGHT)

        canvas = tk.Canvas(items_box, height=180, highlightthickness=0)
        sb = ttk.Scrollbar(items_box, orient="vertical", command=canvas.yview)
        rows_container = ttk.Frame(canvas)
        rows_container.bind("<Configure>", lambda _e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas_win = canvas.create_window((0, 0), window=rows_container, anchor="nw")
        canvas.bind("<Configure>", lambda e: canvas.itemconfig(canvas_win, width=e.width))
        canvas.configure(yscrollcommand=sb.set)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sb.pack(side=tk.RIGHT, fill=tk.Y)

        item_rows: list[dict] = []

        def recalc(*_args):
            is_v = v_is_vat.get()
            tot = Decimal("0.00")
            for rw in item_rows:
                _, _, g = compute_line_decimals(
                    rw["qty"].get(),
                    rw["price"].get(),
                    rw["vat"].get() if is_v else "0",
                    is_v,
                )
                rw["line_tot"].set(f"{g:.2f}")
                tot += g
            v_total_preview.set(f"{tot:.2f} EUR")

        def refresh_vat_visibility():
            is_v = v_is_vat.get()
            for rw in item_rows:
                if is_v:
                    rw["vat_entry"].grid(row=0, column=4, padx=3)
                else:
                    rw["vat_entry"].grid_remove()
            recalc()

        def add_row(desc="Konzultácia / Služby", qty="1", unit="ks", price="100.00", vat="23"):
            rf = ttk.Frame(rows_container)
            rf.pack(fill=tk.X, pady=2)
            vd = tk.StringVar(value=desc)
            vq = tk.StringVar(value=qty)
            vu = tk.StringVar(value=unit)
            vp = tk.StringVar(value=price)
            vv = tk.StringVar(value=vat if v_is_vat.get() else "0")
            vt = tk.StringVar(value="0.00")

            for v in (vq, vp, vv):
                v.trace_add("write", recalc)

            ttk.Entry(rf, textvariable=vd, width=32).grid(row=0, column=0, sticky="ew", padx=3)
            ttk.Entry(rf, textvariable=vq, width=8).grid(row=0, column=1, padx=3)
            ttk.Entry(rf, textvariable=vu, width=6).grid(row=0, column=2, padx=3)
            ttk.Entry(rf, textvariable=vp, width=10).grid(row=0, column=3, padx=3)
            e_vat = ttk.Entry(rf, textvariable=vv, width=6)
            if v_is_vat.get():
                e_vat.grid(row=0, column=4, padx=3)
            ttk.Label(rf, textvariable=vt, width=10, anchor="e").grid(row=0, column=5, padx=4)

            row_obj = {
                "frame": rf, "desc": vd, "qty": vq, "unit": vu, "price": vp, "vat": vv, "line_tot": vt, "vat_entry": e_vat
            }
            item_rows.append(row_obj)

            def remove_row():
                item_rows.remove(row_obj)
                rf.destroy()
                recalc()

            ttk.Button(rf, text="✕", width=3, command=remove_row).grid(row=0, column=6, padx=2)
            rf.columnconfigure(0, weight=1)
            recalc()

        # Hlavička stĺpcov položiek
        col_hdr = ttk.Frame(rows_container)
        col_hdr.pack(fill=tk.X, pady=(0, 3))
        for txt, w, col in [
            ("Popis položky", 32, 0),
            ("Množstvo", 8, 1),
            ("Jedn.", 6, 2),
            ("Cena za 1 j.", 10, 3),
            ("DPH %", 6, 4),
            ("Spolu", 10, 5),
        ]:
            ttk.Label(col_hdr, text=txt, width=w).grid(row=0, column=col, padx=3, sticky="w")
        col_hdr.columnconfigure(0, weight=1)

        add_row()

        # Spodná lišta
        foot = ttk.Frame(main)
        foot.pack(fill=tk.X)
        ttk.Label(foot, text="Celkom:", font=("TkDefaultFont", 11, "bold")).pack(side=tk.LEFT)
        ttk.Label(foot, textvariable=v_total_preview, font=("TkDefaultFont", 12, "bold")).pack(side=tk.LEFT, padx=8)

        def save_invoice():
            if not v_num.get().strip() or not v_cname.get().strip():
                messagebox.showwarning("Chyba", "Číslo faktúry a názov odberateľa sú povinné.", parent=win)
                return
            is_v = v_is_vat.get()
            items_payload = []
            for rw in item_rows:
                desc = rw["desc"].get().strip()
                if not desc:
                    continue
                items_payload.append({
                    "description": desc,
                    "quantity": rw["qty"].get().strip() or "1",
                    "unit": rw["unit"].get().strip() or "ks",
                    "unit_price": f"{parse_dec(rw['price'].get()):.2f}",
                    "vat_rate": (rw["vat"].get().strip() or "0") if is_v else "0",
                    "tax_category": "S" if is_v else "O",
                    "line_total": rw["line_tot"].get(),
                })
            if not items_payload:
                messagebox.showwarning("Chyba", "Pridaj aspoň jednu položku s popisom.", parent=win)
                return

            payload = {
                "direction": "issued",
                "invoice_number": v_num.get().strip(),
                "document_type": v_type.get(),
                "issue_date": v_issue.get().strip(),
                "delivery_date": v_delivery.get().strip() or None,
                "due_date": v_due.get().strip() or None,
                "variable_symbol": v_vs.get().strip() or None,
                "related_invoice_number": v_rel_num.get().strip() or None,
                "related_invoice_date": v_rel_date.get().strip() or None,
                "correction_reason": v_reason.get().strip() or None,
                "currency": "EUR",
                "supplier_name": settings.get("company.name") or "Moja firma s. r. o.",
                "supplier_ico": settings.get("company.ico") or None,
                "supplier_dic": settings.get("company.dic") or None,
                "supplier_icdph": (settings.get("company.icdph") or None) if is_v else None,
                "supplier_address": settings.get("company.address") or None,
                "supplier_iban": settings.get("company.iban") or None,
                "customer_name": v_cname.get().strip(),
                "customer_ico": v_cico.get().strip() or None,
                "customer_dic": v_cdic.get().strip() or None,
                "customer_peppol_id": v_cpeppol.get().strip() or None,
                "customer_street": v_cstreet.get().strip() or None,
                "customer_city": v_ccity.get().strip() or None,
                "customer_postal_zone": v_cpsc.get().strip() or None,
                "customer_country_code": v_ccountry.get().strip() or "SK",
                "payment_note": v_note.get().strip() or None,
                "include_qr": v_inc_qr.get(),
                "include_signature": v_inc_sig.get(),
                "is_vat_payer": is_v,
                "status": "local",
                "items": items_payload,
            }
            try:
                self.db.insert_invoice(payload)
                self.load_issued()
                self.set_status(f"Faktúra {payload['invoice_number']} bola uložená.")
                win.destroy()
            except Exception as exc:
                messagebox.showerror("Chyba ukladania", str(exc), parent=win)

        ttk.Button(foot, text="Uložiť faktúru lokálne", command=save_invoice).pack(side=tk.RIGHT)
        ttk.Button(foot, text="Zrušiť", command=win.destroy).pack(side=tk.RIGHT, padx=6)


def main() -> None:
    root = tk.Tk()
    EFakturyApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
