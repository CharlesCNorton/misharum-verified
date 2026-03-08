# misharum-verified

Formalizing Old Babylonian debt remission.

This repository encodes Old Babylonian misharum as a total state transformer
over obligations, debt-servitude, pledged holdings, and collected payments.
Remissible agrarian debts are remitted, dependent bondage is released, pledged
holdings are restored, qualifying pre-edict collections are refunded, and
merchant-credit exceptions are preserved.

## Proven

- Exact transition laws for remittance, release, restoration, and refund.
- No remissible obligation survives a completed edict.
- Obligation identifiers, parties, debt kinds, and amounts are preserved.
- Referential integrity is preserved across obligations, bondages, pledges, and
  collections.
- Applying the edict twice is equivalent to applying it once.

## Build

```powershell
& 'C:\Coq-Platform~8.19~2024.10\bin\coqc.exe' .\Misharum.v
```

Compatible with Coq 8.19.x.
