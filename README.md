# eFaktúry (Desktop)

> ⚠️ **UPOZORNENIE / WARNING**
>
> **SK:** Toto je **testovacia, neprodukčná verzia v procese tvorenia (Work in Progress)**. Aplikácia nie je určená na ostré účtovné ani daňové nasadenie bez dôkladného overenia výstupov. Funkcionalita, databázová schéma aj používateľské rozhranie sa môžu priebežne meniť.
>
> **EN:** This is a **test, non-production version currently under active development (Work in Progress)**. Do not use this software in live accounting or tax production without thoroughly verifying all outputs. Features, database schema, and UI are subject to change.

---

## 🇸🇰 Slovenská verzia

Jednoduchá desktopová aplikácia na lokálnu (offline) správu faktúr, generovanie PDF s PAY by square QR kódom, prácu s UBL 2.1 XML a testovaciu komunikáciu so systémom SAPI-SK / Peppol.

### Aktuálne funkcie
- **Desktopové okno (`tkinter`)** — beží natívne na Linuxe aj Windows bez webového prehliadača.
- **Odoslané a prijaté faktúry** — ukladanie do lokálnej SQLite databázy (`efaktury.sqlite`).
- **Platca / neplatca DPH** — prepínanie režimu DPH v nastaveniach aj priamo pri vystavovaní faktúry.
- **Generovanie PDF (`reportlab`)** — položky v jednom riadku, rekapitulácia DPH, podpora TTF fontov (napr. Roboto, DejaVu Sans), voliteľné logo a podpis; už vytvorené PDF súbory sa neprepisujú.
- **PAY by square 1.2.0 QR kód** — generuje sa automaticky pri kladnej sume a platnom IBANe.
- **UBL 2.1 XML** — export odoslaných a import prijatých dokladov zo súboru.
- **Adresár odberateľov** — doplnenie údajov podľa IČO z registra RÚZ a overenie Peppol Participant ID.
- **SAPI-SK integrácia (testovacia)** — odosielanie a sťahovanie dokladov cez Peppol prístupový bod.

### Požiadavky a spustenie zo zdrojového kódu

Vyžaduje **Python 3.10+** (na Linuxe aj balík `tk` pre `tkinter`):

```bash
python -m venv .venv
source .venv/bin/activate   # Na Windows: .venv\Scripts\activate
pip install -r requirements.txt
python efaktury.py
```

### Vytvorenie samostatnej binárky

```bash
pip install pyinstaller
pyinstaller --onefile --windowed --name efaktury --hidden-import=PIL._tkinter_finder --collect-submodules reportlab efaktury.py
```

Výsledný spustiteľný súbor sa vytvorí v priečinku `dist/`. Automatické buildy pre Linux a Windows sú dostupné aj cez GitHub Actions.

### Bezpečnosť dát
Databáza `efaktury.sqlite` a priečinok `pdf/` obsahujú vaše lokálne faktúry, údaje o firme a prístupové údaje k API. Nikdy ich nenahrávajte do verejného repozitára (sú vylúčené v `.gitignore`).

---

## 🇬🇧 English Version

A simple desktop application for local (offline) invoice management, PDF generation with PAY by square QR codes, UBL 2.1 XML handling, and experimental SAPI-SK / Peppol integration.

### Current Features
- **Native desktop GUI (`tkinter`)** — runs locally on Linux and Windows without a web browser.
- **Issued & received invoices** — stored locally in an SQLite database (`efaktury.sqlite`).
- **VAT payer / non-VAT payer mode** — configurable globally in settings or per invoice.
- **PDF generation (`reportlab`)** — single-line item rows, VAT summary, TTF font support (e.g. Roboto, DejaVu Sans), optional logo and signature; existing PDFs are never overwritten.
- **PAY by square 1.2.0 QR code** — automatically generated for positive amounts with a valid IBAN.
- **UBL 2.1 XML** — export issued invoices and import received XML files.
- **Customer directory** — company lookup by IČO via the Slovak Register of Financial Statements (RÚZ) and Peppol Participant ID verification.
- **SAPI-SK integration (experimental)** — send and fetch documents via Peppol access point.

### Requirements & Running from Source

Requires **Python 3.10+** (and `tk` system package on Linux for `tkinter`):

```bash
python -m venv .venv
source .venv/bin/activate   # On Windows: .venv\Scripts\activate
pip install -r requirements.txt
python efaktury.py
```

### Building a Standalone Binary

```bash
pip install pyinstaller
pyinstaller --onefile --windowed --name efaktury --hidden-import=PIL._tkinter_finder --collect-submodules reportlab efaktury.py
```

The executable will be created inside the `dist/` directory. Automated builds for Linux and Windows are also configured via GitHub Actions.

### Data Security
The `efaktury.sqlite` database and `pdf/` directory contain your local invoices, company details, and API credentials. Never commit them to a public repository (they are excluded via `.gitignore`).
```
