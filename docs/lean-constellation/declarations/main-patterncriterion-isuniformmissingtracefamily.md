[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `IsUniformMissingTraceFamily`

A Finset family on Fin n is (d+1)-uniform and has an s-element missing intersection trace inside every member.

- Kind: `definition`
- Node: `Main.PatternCriterion`
- Module: `UniformMissingTraceFamily.Main.PatternCriterion.Defs.IsUniformMissingTraceFamily`
- State: `declared`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final statement projection

## Statement NL

For natural numbers `n`, `d`, and `s`, and a finite family `family : Finset (Finset (Fin n))`, `IsUniformMissingTraceFamily d s family` holds exactly when:

1. every member `F` of `family` has cardinality `d + 1`; and
2. every `F ∈ family` has a finite set `B : Finset (Fin n)` with `B ⊆ F` and `B.card = s` such that, for every `F' ∈ family`, the intersection trace `F ∩ F'` is not `B`.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PatternCriterion.Prelude
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `IsUniformMissingTraceFamily`

For natural numbers `n`, `d`, and `s`, and a finite family `family : Finset (Finset (Fin n))`,
`IsUniformMissingTraceFamily d s family` holds exactly when:

1. every member `F` of `family` has cardinality `d + 1`; and
2. every `F ∈ family` has a finite set `B : Finset (Fin n)` with `B ⊆ F` and `B.card = s` such that,
for every `F' ∈ family`, the intersection trace `F ∩ F'` is not `B`.

## Sources

- Source `formal_target.lean`, lines 3–9
-/
def IsUniformMissingTraceFamily {n : ℕ} (d s : ℕ)
    (family : Finset (Finset (Fin n))) : Prop :=
  (∀ F ∈ family, F.card = d + 1) ∧
    ∀ F ∈ family, ∃ B : Finset (Fin n), B ⊆ F ∧ B.card = s ∧
      ∀ F' ∈ family, B ≠ F ∩ F'
```

## Proof NL

Not recorded.

## Proof Formal

Not recorded.

## Sources

- `formal_target.lean:3-9`
