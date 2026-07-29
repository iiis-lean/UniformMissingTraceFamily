<!-- BEGIN Lean Constellation: project-summary -->
# UniformMissingTraceFamily

Publish the completed graph_proved UniformMissingTraceFamily repository after the controlled Main public Statement closure migration. Main contract v2 adds only the required public export of Main.PatternCriterion.IsUniformMissingTraceFamily@1; mathematical Decl truth and proof availability are unchanged.

## Build

```sh
lake build
```

Current Lean Constellation Release: `release_264b1a8d57364941b10df68dfd6631cf`.

## Public declarations

- `anchoredPowerset_weightedSum_eq_chooseSum` — theorem
- `exists_uniformMissingTraceFamily_strictlyLargerThanStar` — theorem
- `perturbedStarFamily_card` — theorem
- `IsUniformMissingTraceFamily` — definition
- `card_eq_of_mem_patternFamily` — theorem
- `mem_patternFamily` — theorem
- `patternFamily` — definition
- `patternFamily_isUniformMissingTraceFamily` — theorem
- `perturbedPattern_properWeights_add_full_eq_fullWeights` — theorem
- `PerturbedStarBlocks` — structure
- `exists_perturbedStarBlocks` — theorem
- `perturbedStarCertificate_addedProper` — theorem
- `perturbedStarCertificate_finalAdded` — theorem
- `perturbedStarCertificate_largeAvoiding` — theorem
- `perturbedStarCertificate_largeMeeting` — theorem
- `perturbedStarCertificate_smallStar` — theorem
- `perturbedStarCore` — definition
- `perturbedStarFamily` — definition
- `perturbedStarFiller` — definition
- `perturbedStarFinalIntersection_excluded` — theorem
- `perturbedStarParameterBounds` — theorem
- `perturbedStarPatterns` — definition
- `perturbedStarTau` — definition
- `perturbedStar_isUniformMissingTraceFamily` — theorem

Generated metadata is available in `docs/lean-constellation/`.
<!-- END Lean Constellation: project-summary -->

## About this formalization

This repository contains an independent Lean 4 formalization of the main
construction and theorem from:

> Zixiang Xu, *A disproof of the uniform witness conjecture*,
> arXiv:2606.24776v1 [math.CO], 2026.
> <https://arxiv.org/abs/2606.24776>

The original mathematical results and proof are due to Zixiang Xu. The Lean
formalization was produced by IIIS Lean using Lean Constellation. It is not
presented as work by, or endorsed by, the original author unless explicitly
stated otherwise.

The article source retained under `.lean_constellation/source/article/` is
based on the author's arXiv TeX source. It was reorganized into a structured
SourceCorpus and checked against arXiv version 1; these organizational changes
do not claim authorship of the mathematical content.

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

If you use the Lean implementation, cite this repository in addition to the
paper. Machine-readable citation metadata is available in `CITATION.cff`.

## Licensing

- Lean source code, generated Lean Constellation metadata, and repository
  documentation outside the article SourceCorpus are licensed under the
  Apache License 2.0; see `LICENSE`.
- The reproduced and reorganized article source under
  `.lean_constellation/source/article/` remains attributed to Zixiang Xu and
  is distributed under Creative Commons Attribution 4.0; see
  `LICENSES/CC-BY-4.0.md`.

No repository license changes the authorship or attribution of the original
paper.
