<!-- BEGIN Lean Constellation: project-summary -->
# Uniform Missing-Trace Families in Lean

![completion: graph proved](https://img.shields.io/badge/completion-graph%20proved-2f855a) ![proofs: proved](https://img.shields.io/badge/proofs-proved-2f855a) ![Lean: 4.32.0](https://img.shields.io/badge/Lean-4.32.0-0b6e4f) ![Lean Constellation: generated](https://img.shields.io/badge/Lean%20Constellation-generated-5b4b8a) [![source: arXiv 2606.24776](https://img.shields.io/badge/source-arXiv%202606.24776-b31b1b)](https://arxiv.org/abs/2606.24776) ![topic: lean4](https://img.shields.io/badge/topic-lean4-lightgrey) ![topic: mathlib](https://img.shields.io/badge/topic-mathlib-lightgrey) ![topic: formalization](https://img.shields.io/badge/topic-formalization-lightgrey) ![topic: lean-constellation](https://img.shields.io/badge/topic-lean-constellation-lightgrey) ![topic: extremal-set-theory](https://img.shields.io/badge/topic-extremal-set-theory-lightgrey)

A Lean 4 formalization of the uniform missing-trace family construction underlying the disproof of the uniform witness conjecture.

## Project status

| Property | Value |
| --- | --- |
| Completion | `graph_proved` |
| Proof availability | `proved` |

## Build

```sh
lake build
```

## Public declarations

| Declaration | Kind | Node | Status |
| --- | --- | --- | --- |
| [`anchoredPowerset_weightedSum_eq_chooseSum`](docs/lean-constellation/PUBLIC_API.md#anchoredpowerset_weightedsum_eq_choosesum) | `theorem` | `Main.AnchoredPowersetEnumeration` | `proved` |
| [`exists_uniformMissingTraceFamily_strictlyLargerThanStar`](docs/lean-constellation/PUBLIC_API.md#exists_uniformmissingtracefamily_strictlylargerthanstar) | `theorem` | `Main.CountingAndMain` | `proved` |
| [`perturbedStarFamily_card`](docs/lean-constellation/PUBLIC_API.md#perturbedstarfamily_card) | `theorem` | `Main.CountingAndMain` | `proved` |
| [`IsUniformMissingTraceFamily`](docs/lean-constellation/PUBLIC_API.md#isuniformmissingtracefamily) | `definition` | `Main.PatternCriterion` | `declared` |
| [`card_eq_of_mem_patternFamily`](docs/lean-constellation/PUBLIC_API.md#card_eq_of_mem_patternfamily) | `theorem` | `Main.PatternCriterion` | `proved` |
| [`mem_patternFamily`](docs/lean-constellation/PUBLIC_API.md#mem_patternfamily) | `theorem` | `Main.PatternCriterion` | `proved` |
| [`patternFamily`](docs/lean-constellation/PUBLIC_API.md#patternfamily) | `definition` | `Main.PatternCriterion` | `declared` |
| [`patternFamily_isUniformMissingTraceFamily`](docs/lean-constellation/PUBLIC_API.md#patternfamily_isuniformmissingtracefamily) | `theorem` | `Main.PatternCriterion` | `proved` |
| [`perturbedPattern_properWeights_add_full_eq_fullWeights`](docs/lean-constellation/PUBLIC_API.md#perturbedpattern_properweights_add_full_eq_fullweights) | `theorem` | `Main.PerturbedPatternCancellation` | `proved` |
| [`PerturbedStarBlocks`](docs/lean-constellation/PUBLIC_API.md#perturbedstarblocks) | `structure` | `Main.PerturbedStarCertificates` | `declared` |
| [`exists_perturbedStarBlocks`](docs/lean-constellation/PUBLIC_API.md#exists_perturbedstarblocks) | `theorem` | `Main.PerturbedStarCertificates` | `proved` |
| [`perturbedStarCertificate_addedProper`](docs/lean-constellation/PUBLIC_API.md#perturbedstarcertificate_addedproper) | `theorem` | `Main.PerturbedStarCertificates` | `proved` |
| [`perturbedStarCertificate_finalAdded`](docs/lean-constellation/PUBLIC_API.md#perturbedstarcertificate_finaladded) | `theorem` | `Main.PerturbedStarCertificates` | `proved` |
| [`perturbedStarCertificate_largeAvoiding`](docs/lean-constellation/PUBLIC_API.md#perturbedstarcertificate_largeavoiding) | `theorem` | `Main.PerturbedStarCertificates` | `proved` |
| [`perturbedStarCertificate_largeMeeting`](docs/lean-constellation/PUBLIC_API.md#perturbedstarcertificate_largemeeting) | `theorem` | `Main.PerturbedStarCertificates` | `proved` |
| [`perturbedStarCertificate_smallStar`](docs/lean-constellation/PUBLIC_API.md#perturbedstarcertificate_smallstar) | `theorem` | `Main.PerturbedStarCertificates` | `proved` |
| [`perturbedStarCore`](docs/lean-constellation/PUBLIC_API.md#perturbedstarcore) | `definition` | `Main.PerturbedStarCertificates` | `declared` |
| [`perturbedStarFamily`](docs/lean-constellation/PUBLIC_API.md#perturbedstarfamily) | `definition` | `Main.PerturbedStarCertificates` | `declared` |
| [`perturbedStarFiller`](docs/lean-constellation/PUBLIC_API.md#perturbedstarfiller) | `definition` | `Main.PerturbedStarCertificates` | `declared` |
| [`perturbedStarFinalIntersection_excluded`](docs/lean-constellation/PUBLIC_API.md#perturbedstarfinalintersection_excluded) | `theorem` | `Main.PerturbedStarCertificates` | `proved` |
| [`perturbedStarParameterBounds`](docs/lean-constellation/PUBLIC_API.md#perturbedstarparameterbounds) | `theorem` | `Main.PerturbedStarCertificates` | `proved` |
| [`perturbedStarPatterns`](docs/lean-constellation/PUBLIC_API.md#perturbedstarpatterns) | `definition` | `Main.PerturbedStarCertificates` | `declared` |
| [`perturbedStarTau`](docs/lean-constellation/PUBLIC_API.md#perturbedstartau) | `definition` | `Main.PerturbedStarCertificates` | `declared` |
| [`perturbedStar_isUniformMissingTraceFamily`](docs/lean-constellation/PUBLIC_API.md#perturbedstar_isuniformmissingtracefamily) | `theorem` | `Main.PerturbedStarCertificates` | `proved` |

See the [complete Public API](docs/lean-constellation/PUBLIC_API.md) for declaration summaries, final Lean code, dependencies, and sources.

## About this formalization

This repository contains an independent Lean 4 formalization of the main construction and theorem from:

> Zixiang Xu, *A disproof of the uniform witness conjecture*,
> arXiv:2606.24776v1 [math.CO], 2026.
> <https://arxiv.org/abs/2606.24776>

The original mathematical results and proof are due to Zixiang Xu. The Lean formalization was produced by IIIS Lean using Lean Constellation. It is not presented as work by, or endorsed by, the original author unless explicitly stated otherwise.

The article source retained under `.lean_constellation/source/article/` is based on the author's arXiv TeX source. It was reorganized into a structured SourceCorpus and checked against arXiv version 1; these organizational changes do not claim authorship of the mathematical content.

## Citation

If you use the mathematical result, cite the original paper:

```bibtex
@article{Xu2026UniformWitness,
  author        = {Zixiang Xu},
  title         = {A disproof of the uniform witness conjecture},
  journal       = {arXiv preprint},
  year          = {2026},
  eprint        = {2606.24776},
  archivePrefix = {arXiv},
  primaryClass  = {math.CO},
  doi           = {10.48550/arXiv.2606.24776},
  url           = {https://arxiv.org/abs/2606.24776}
}
```

If you use the Lean implementation, cite this repository in addition to the paper. Machine-readable citation metadata is available in [`CITATION.cff`](CITATION.cff).

## Licensing

- Lean source code, generated Lean Constellation metadata, and repository documentation outside the article SourceCorpus are licensed under the Apache License 2.0; see [`LICENSE`](LICENSE).
- The reproduced and reorganized article source under `.lean_constellation/source/article/` remains attributed to Zixiang Xu and is distributed under Creative Commons Attribution 4.0; see [`LICENSES/CC-BY-4.0.md`](LICENSES/CC-BY-4.0.md).

No repository license changes the authorship or attribution of the original paper.
<!-- END Lean Constellation: project-summary -->
