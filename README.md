<!-- BEGIN Lean Constellation: project-summary -->
<h1><img src="docs/lean-constellation/assets/lean-constellation-mark.svg" alt="Lean Constellation mark" width="42" align="absmiddle"> Uniform Missing Trace Family</h1>

![status: proved](https://img.shields.io/static/v1?label=status&message=proved&color=0f8f88&style=flat-square) ![Lean: 4.32.0](https://img.shields.io/static/v1?label=Lean&message=4.32.0&color=6b4fbb&style=flat-square) [![source: arXiv 2606.24776](https://img.shields.io/static/v1?label=source&message=arXiv+2606.24776&color=b31b1b&style=flat-square)](https://arxiv.org/abs/2606.24776) [![LC: Lean Constellation](https://img.shields.io/static/v1?label=LC&message=Lean+Constellation&color=092745&style=flat-square)](https://github.com/iiis-lean/lean-constellation) [![MCP: Lean Toolkit](https://img.shields.io/static/v1?label=MCP&message=Lean+Toolkit&color=e45132&style=flat-square)](https://github.com/iiis-lean/lean-mcp-toolkit)

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

## Public API

This repository exports **2 public declarations** across **2 nodes**.

Browse the [Public API index](docs/lean-constellation/PUBLIC_API.md) for the dependency graph, declaration index, final Lean code, dependencies, and sources. The [public boundary catalog](docs/lean-constellation/PUBLIC_BOUNDARIES.md) documents internal Content-public declarations and Scope propagation.

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

<p align="center">
  <img src="docs/lean-constellation/assets/lean-constellation-mark.svg" alt="Lean Constellation" width="72">
  <br>
  <sub>Generated with <strong>Lean Constellation</strong></sub>
</p>
<!-- END Lean Constellation: project-summary -->
