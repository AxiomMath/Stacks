module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute

/-!
# Factoring a morphism through a point

A morphism from a reduced scheme whose set-theoretic image is a single point factors through the
spectrum of the residue field at that point.

## Main results

* `AlgebraicGeometry.exists_comp_fromSpecResidueField_eq` gives the factorization through the
  canonical morphism from the residue field of the point.

## Implementation notes

Set-theoretic containment of the image is expressed using the underlying continuous map of the
morphism. The conclusion records the factorization by a morphism together with its composition
equation. The factorization is produced by base-changing along the residue-field point: the
first projection is then a surjective closed immersion out of a reduced scheme, hence an
isomorphism.

## References

* [Stacks Project, Tag 0H1M](https://stacks.math.columbia.edu/tag/0H1M)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0H1M.** A morphism from a reduced scheme whose image is contained in a
single point factors through the spectrum of the residue field of that point. -/
@[stacks 0H1M]
lemma exists_comp_fromSpecResidueField_eq {X Y : Scheme.{u}} (f : Y ⟶ X) (x : X)
    [IsReduced Y] (hf : Set.range f.base ⊆ {x}) :
    ∃ g : Y ⟶ Spec (.of (X.residueField x)), g ≫ X.fromSpecResidueField x = f := by
  let i := X.fromSpecResidueField x
  let p := Limits.pullback.fst f i
  have hp : Set.range p = Set.univ := by
    rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
    ext y
    simpa using hf ⟨y, rfl⟩
  have : Surjective p := ⟨Set.range_eq_univ.mp hp⟩
  have : IsClosedImmersion p := IsClosedImmersion.of_isPreimmersion p (hp ▸ isClosed_univ)
  have : IsIso p := isIso_of_isClosedImmersion_of_surjective p
  refine ⟨inv p ≫ Limits.pullback.snd f i, ?_⟩
  change (inv p ≫ Limits.pullback.snd f i) ≫ i = f
  rw [Category.assoc, ← Limits.pullback.condition, IsIso.inv_hom_id_assoc]

end AlgebraicGeometry
