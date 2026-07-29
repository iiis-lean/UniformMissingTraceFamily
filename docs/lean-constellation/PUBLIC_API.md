# Public API

- Repository completion: `graph_proved`
- Proof availability: `proved`
- Public declarations: `24` across `5` nodes

## Dependency graph

Consumers appear above the public declarations they depend on. Solid arrows are Statement dependencies; dashed arrows are Proof dependencies. Transitively implied edges are omitted for readability; each declaration page lists the complete direct dependency set. Mathlib and non-public project dependencies are not shown.

```mermaid
%%{init: {"flowchart": {"defaultRenderer": "elk", "nodeSpacing": 24, "rankSpacing": 36}}}%%
flowchart TB
  subgraph n0["Main.AnchoredPowersetEnumeration"]
    direction TB
    d0["anchoredPowerset_weightedSum<br/>eq_chooseSum"]
  end
  subgraph n1["Main.CountingAndMain"]
    direction TB
    d1["exists<br/>uniformMissingTraceFamily<br/>strictlyLargerThanStar"]
    d2["perturbedStarFamily_card"]
  end
  subgraph n2["Main.PerturbedPatternCancellation"]
    direction TB
    d3["perturbedPattern_properWeights<br/>add_full_eq_fullWeights"]
  end
  subgraph n3["Main.PerturbedStarCertificates"]
    direction TB
    d4["perturbedStar<br/>isUniformMissingTraceFamily"]
    d5["exists_perturbedStarBlocks"]
    d6["perturbedStarCertificate<br/>addedProper"]
    d7["perturbedStarCertificate<br/>finalAdded"]
    d8["perturbedStarCertificate<br/>largeAvoiding"]
    d9["perturbedStarCertificate<br/>largeMeeting"]
    d10["perturbedStarCertificate<br/>smallStar"]
    d11["perturbedStarFamily"]
    d12["perturbedStarFiller"]
    d13["perturbedStarFinalIntersection<br/>excluded"]
    d14["perturbedStarParameterBounds"]
    d15["perturbedStarPatterns"]
    d16["perturbedStarCore"]
    d17["perturbedStarTau"]
    d18["PerturbedStarBlocks"]
  end
  subgraph n4["Main.PatternCriterion"]
    direction TB
    d19["patternFamily<br/>isUniformMissingTraceFamily"]
    d20["IsUniformMissingTraceFamily"]
    d21["card_eq_of_mem_patternFamily"]
    d22["mem_patternFamily"]
    d23["patternFamily"]
  end
  d1 -.-> d2
  d1 -.-> d4
  d2 --> d11
  d21 -.-> d22
  d22 --> d23
  d19 --> d20
  d19 -.-> d21
  d3 --> d12
  d5 --> d18
  d6 --> d15
  d6 --> d17
  d7 -.-> d13
  d7 --> d17
  d8 --> d15
  d8 --> d17
  d9 --> d15
  d9 --> d17
  d10 --> d15
  d10 --> d17
  d16 --> d18
  d11 --> d23
  d11 --> d12
  d11 --> d15
  d12 --> d16
  d13 --> d15
  d15 --> d16
  d17 --> d18
  d4 -.-> d19
  d4 -.-> d5
  d4 -.-> d6
  d4 -.-> d7
  d4 -.-> d8
  d4 -.-> d9
  d4 -.-> d10
  d4 --> d11
  d4 -.-> d14
```

## Declarations

| Node | Declaration | Kind | Status |
| --- | --- | --- | --- |
| `Main.AnchoredPowersetEnumeration` | [`anchoredPowerset_weightedSum_eq_chooseSum`](public-api/main-anchoredpowersetenumeration-anchoredpowerset-weightedsum-eq-choosesum.md) | `theorem` | `proved` |
| `Main.CountingAndMain` | [`exists_uniformMissingTraceFamily_strictlyLargerThanStar`](public-api/main-countingandmain-exists-uniformmissingtracefamily-strictlylargerthanstar.md) | `theorem` | `proved` |
| `Main.CountingAndMain` | [`perturbedStarFamily_card`](public-api/main-countingandmain-perturbedstarfamily-card.md) | `theorem` | `proved` |
| `Main.PerturbedPatternCancellation` | [`perturbedPattern_properWeights_add_full_eq_fullWeights`](public-api/main-perturbedpatterncancellation-perturbedpattern-properweights-add-full-eq-fullweights.md) | `theorem` | `proved` |
| `Main.PerturbedStarCertificates` | [`perturbedStar_isUniformMissingTraceFamily`](public-api/main-perturbedstarcertificates-perturbedstar-isuniformmissingtracefamily.md) | `theorem` | `proved` |
| `Main.PerturbedStarCertificates` | [`exists_perturbedStarBlocks`](public-api/main-perturbedstarcertificates-exists-perturbedstarblocks.md) | `theorem` | `proved` |
| `Main.PerturbedStarCertificates` | [`perturbedStarCertificate_addedProper`](public-api/main-perturbedstarcertificates-perturbedstarcertificate-addedproper.md) | `theorem` | `proved` |
| `Main.PerturbedStarCertificates` | [`perturbedStarCertificate_finalAdded`](public-api/main-perturbedstarcertificates-perturbedstarcertificate-finaladded.md) | `theorem` | `proved` |
| `Main.PerturbedStarCertificates` | [`perturbedStarCertificate_largeAvoiding`](public-api/main-perturbedstarcertificates-perturbedstarcertificate-largeavoiding.md) | `theorem` | `proved` |
| `Main.PerturbedStarCertificates` | [`perturbedStarCertificate_largeMeeting`](public-api/main-perturbedstarcertificates-perturbedstarcertificate-largemeeting.md) | `theorem` | `proved` |
| `Main.PerturbedStarCertificates` | [`perturbedStarCertificate_smallStar`](public-api/main-perturbedstarcertificates-perturbedstarcertificate-smallstar.md) | `theorem` | `proved` |
| `Main.PerturbedStarCertificates` | [`perturbedStarFamily`](public-api/main-perturbedstarcertificates-perturbedstarfamily.md) | `definition` | `declared` |
| `Main.PerturbedStarCertificates` | [`perturbedStarFiller`](public-api/main-perturbedstarcertificates-perturbedstarfiller.md) | `definition` | `declared` |
| `Main.PerturbedStarCertificates` | [`perturbedStarFinalIntersection_excluded`](public-api/main-perturbedstarcertificates-perturbedstarfinalintersection-excluded.md) | `theorem` | `proved` |
| `Main.PerturbedStarCertificates` | [`perturbedStarParameterBounds`](public-api/main-perturbedstarcertificates-perturbedstarparameterbounds.md) | `theorem` | `proved` |
| `Main.PerturbedStarCertificates` | [`perturbedStarPatterns`](public-api/main-perturbedstarcertificates-perturbedstarpatterns.md) | `definition` | `declared` |
| `Main.PerturbedStarCertificates` | [`perturbedStarCore`](public-api/main-perturbedstarcertificates-perturbedstarcore.md) | `definition` | `declared` |
| `Main.PerturbedStarCertificates` | [`perturbedStarTau`](public-api/main-perturbedstarcertificates-perturbedstartau.md) | `definition` | `declared` |
| `Main.PerturbedStarCertificates` | [`PerturbedStarBlocks`](public-api/main-perturbedstarcertificates-perturbedstarblocks.md) | `structure` | `declared` |
| `Main.PatternCriterion` | [`patternFamily_isUniformMissingTraceFamily`](public-api/main-patterncriterion-patternfamily-isuniformmissingtracefamily.md) | `theorem` | `proved` |
| `Main.PatternCriterion` | [`IsUniformMissingTraceFamily`](public-api/main-patterncriterion-isuniformmissingtracefamily.md) | `definition` | `declared` |
| `Main.PatternCriterion` | [`card_eq_of_mem_patternFamily`](public-api/main-patterncriterion-card-eq-of-mem-patternfamily.md) | `theorem` | `proved` |
| `Main.PatternCriterion` | [`mem_patternFamily`](public-api/main-patterncriterion-mem-patternfamily.md) | `theorem` | `proved` |
| `Main.PatternCriterion` | [`patternFamily`](public-api/main-patterncriterion-patternfamily.md) | `definition` | `declared` |
