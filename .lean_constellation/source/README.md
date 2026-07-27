# Uniform Missing-trace Families

## Source provenance

The main material is a complete mathematical reconstruction of Zixiang Xu,
*A disproof of the uniform witness conjecture*, arXiv:2606.24776v1 (2026).
The reconstruction is based on the author's TeX source and was checked against
the five-page arXiv PDF.

## Reading order

1. Read or compile `article/main.tex`. It inputs the article sections in their
   original order and reproduces the complete article.
2. The original bibliography data is in `article/references.bib`; citation
   numbers retain the order of the source article.
3. Read `formal_target.lean` for the single constructive formal statement. It
   asks for a uniform finite family with a missing trace of fixed size on every
   member, the exact cardinality attained by the construction, and its strict
   excess over the corresponding star.

## Main material

The article contains the original abstract and introduction, the template
family and missing-trace criterion, the explicit pattern construction, its
exact count, all five certificate cases, the concluding parameter remarks,
acknowledgement, and bibliography.

The Lean file expresses the paper's construction on the finite type `Fin n`.
It does not assume the contextual VC-dimension results cited in the
introduction.

## Known gaps and extraction limits

No article page or proof case is intentionally omitted. The article cites
historical extremal-set-theory and VC-dimension results for context and for the
formulation of the conjecture. Their proofs are not reproduced because the
explicit counterexample construction and its verification do not depend on
them.

Journal-style running metadata, arXiv page furniture, and source comments are
not reproduced.
