# Item-7 PDF Retrieval Report

- Date: 2026-02-12 09:38:51Z
- Policy: strict all-citations attempt; no overwrite of existing SignedDigit/<Key>.pdf
- Total keys: 15

## Ambridge2024
- Status: skipped-existing
- Target: SignedDigit/Ambridge2024.pdf
- Reason: target-exists
- Bib URL: https://arxiv.org/abs/2401.09270
- Bib DOI: 10.48550/arXiv.2401.09270
- Bib eprint: 2401.09270

## TypeTopology
- Status: skipped-existing
- Target: SignedDigit/TypeTopology.pdf
- Reason: target-exists
- Bib URL: https://github.com/martinescardo/TypeTopology

## WiesnetKopp2022
- Status: skipped-existing
- Target: SignedDigit/WiesnetKopp2022.pdf
- Reason: target-exists
- Bib DOI: 10.46298/lmcs-18(3:24)2022

## Berger2011
- Status: corrected-mapping
- Target: SignedDigit/BergerSeisenberger2012.pdf
- Reason: canonical local filename differs from bib key
- Bib DOI: 10.2168/LMCS-7(1:8)2011

## Niqui2008
- Status: corrected-mapping
- Target: SignedDigit/0807.1669.pdf
- Reason: corrected key-to-file mapping after title audit
- Bib DOI: 10.2168/LMCS-4(3:6)2008

## Kaganovsky1998
- Status: unresolved
- Reason: non-pdf-response
- Source type: article
- Bib DOI: 10.1016/S1571-0661(05)80217-8
- Attempts:
  - https://doi.org/10.1016/S1571-0661(05)80217-8 :: HTTP 200 :: text/html;charset=UTF-8

## KoeppSchwichtenberg2022
- Status: skipped-existing
- Target: SignedDigit/KoeppSchwichtenberg2022.pdf
- Reason: target-exists
- Bib DOI: 10.1016/j.tcs.2022.10.003

## BoehmEtAl1986
- Status: skipped-existing
- Target: SignedDigit/BoehmEtAl1986.pdf
- Reason: target-exists
- Bib DOI: 10.1145/319838.319860

## LubarskyRichman2015
- Status: skipped-existing
- Target: SignedDigit/LubarskyRichman2015.pdf
- Reason: target-exists
- Bib URL: https://arxiv.org/abs/1510.00648
- Bib eprint: 1510.00648

## BooijLocators
- Status: corrected-mapping
- Target: SignedDigit/BooijLocators2021.pdf
- Reason: canonical local filename differs from bib key
- Bib URL: https://arxiv.org/abs/1805.06781
- Bib eprint: 1805.06781

## SchwichtenbergWiesnet2021
- Status: external-only
- Reason: withdrawn preprint; superseded by WiesnetKopp2022
- Bib URL: https://arxiv.org/abs/2103.15702
- Bib eprint: 2103.15702

## BergerSeisenberger2012
- Status: skipped-existing
- Target: SignedDigit/BergerSeisenberger2012.pdf
- Reason: target-exists
- Bib URL: https://arxiv.org/abs/1101.2162
- Bib eprint: 1101.2162

## BergerLloyd2009
- Status: skipped-existing
- Target: SignedDigit/BergerLloyd2009.pdf
- Reason: target-exists
- Bib URL: https://eceasst.org/index.php/eceasst/article/view/1598
- Bib DOI: 10.14279/tuj.eceasst.23.331

## EscardoSimpson2014
- Status: skipped-existing
- Target: SignedDigit/EscardoSimpson2014.pdf
- Reason: target-exists
- Bib URL: https://martinescardo.github.io/papers/realadt.pdf

## WikiSignedDigit
- Status: external-only
- Reason: local PDF title mismatch; canonical citation is the URL
- Bib URL: https://en.wikipedia.org/wiki/Signed-digit_representation

## Summary
- Downloaded: 0
- Verified local: 12
- External-only: 2
- Unresolved: 1
- Total: 15

## Post-Audit Corrections (2026-02-15)

The fetch report above is preserved as originally generated. A manual audit then corrected
key-to-file mapping for paper-ready citation tracking:

- `Berger2011` -> `SignedDigit/BergerSeisenberger2012.pdf` (same LMCS paper; canonical filename differs)
- `Niqui2008` -> `SignedDigit/0807.1669.pdf` (correct LMCS article; previous `Niqui2008.pdf` file title mismatch)
- `BooijLocators` -> `SignedDigit/BooijLocators2021.pdf` (canonical filename differs)
- `SchwichtenbergWiesnet2021` -> external URL only (`https://arxiv.org/abs/2103.15702`; withdrawn/superseded by `WiesnetKopp2022`)
- `WikiSignedDigit` -> external URL only (`https://en.wikipedia.org/wiki/Signed-digit_representation`; local PDF title mismatch)

The canonical source for current mapping status is now:
- `docs/signed-digit-reference-audit.json`
