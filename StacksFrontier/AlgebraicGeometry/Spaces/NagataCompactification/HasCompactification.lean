module

public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence

/-!
# Algebraic spaces having a compactification over a base

Let `Y` be an algebraic space over a scheme `S` and let `f : X ⟶ Y` be a morphism of algebraic
spaces. Then `X` *has a compactification over `Y`* (is *compactifyable over `Y`*) when `f`
factors as a quasi-compact open immersion `j : X ⟶ X̄` followed by a proper morphism
`X̄ ⟶ Y` of algebraic spaces. Since an open immersion is a separated morphism which is locally
of finite type, a compactifiable `X` is separated and of finite type over `Y`; Nagata's
compactification theorem for algebraic spaces is the converse over a quasi-compact and
quasi-separated base.

## Main definitions

* `AlgebraicGeometry.Space.HasCompactification`: the morphism `f : X ⟶ Y` factors as a
  quasi-compact open immersion into an algebraic space proper over `Y`.

## Main results

* `AlgebraicGeometry.Space.HasCompactification.isSeparated` and
  `AlgebraicGeometry.Space.HasCompactification.isFiniteType`: a compactifiable morphism is
  separated and of finite type.
* `AlgebraicGeometry.Space.HasCompactification.of_isOpenImmersion`: a quasi-compact open
  subspace of a compactifiable space is compactifiable.

## Implementation notes

The source fixes a quasi-compact and quasi-separated base before introducing the notion. The
notion makes sense over any base, and neither the definition nor the results of this file use
those hypotheses, so they are not imposed here; they are hypotheses of the theorems which need
them.

As elsewhere for algebraic spaces over `S`, morphisms are morphisms of presheaves on the big
fppf site of `S`. The ambient space `X̄` of a compactification is required to be an algebraic
space; algebraicity of `X` and `Y` is imposed by the results that use it.

This is the analogue for algebraic spaces of `AlgebraicGeometry.HasCompactification`.

## References

* [Stacks Project, Section 0F44](https://stacks.math.columbia.edu/tag/0F44)
* [Stacks Project, Tag 0F4D](https://stacks.math.columbia.edu/tag/0F4D)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`X` has a compactification over `Y`.** The morphism `f : X ⟶ Y` of algebraic spaces over
`S` factors as a quasi-compact open immersion of `X` into an algebraic space proper over `Y`. -/
def HasCompactification {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop :=
  ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (j : X ⟶ X') (p : X' ⟶ Y),
    IsAlgebraicSpace B S hS X' ∧ IsOpenImmersion B S hS j ∧ IsQuasiCompact B S hS j ∧
      IsProper B S hS p ∧ j ≫ p = f

namespace HasCompactification

variable {B S hS} {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Compactifiability transports along an equality of morphisms. -/
theorem of_eq {f f' : X ⟶ Y} (h : f = f') (hf : HasCompactification B S hS f) :
    HasCompactification B S hS f' := h ▸ hf

/-- A quasi-compact open immersion into an algebraic space proper over `Y` exhibits a
compactification of its source. -/
theorem of_isOpenImmersion_isProper {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (j : X ⟶ X')
    (p : X' ⟶ Y) (hX' : IsAlgebraicSpace B S hS X') (hj : IsOpenImmersion B S hS j)
    (hjqc : IsQuasiCompact B S hS j) (hp : IsProper B S hS p) :
    HasCompactification B S hS (j ≫ p) :=
  ⟨X', j, p, hX', hj, hjqc, hp, rfl⟩

/-- **A compactifiable morphism is separated**: it is the composite of an open immersion, which
is a monomorphism and so separated, with a proper morphism. -/
theorem isSeparated {f : X ⟶ Y} (hf : HasCompactification B S hS f) :
    IsSeparated B S hS f := by
  obtain ⟨X', j, p, -, hj, -, hp, rfl⟩ := hf
  exact isSeparated_comp B S hS j p
    (isSeparated_of_isImmersion B S hS (isImmersion_of_isOpenImmersion B S hS hj)) hp.1

/-- **A compactifiable morphism is of finite type**: it is the composite of a quasi-compact open
immersion, which is of finite type, with a proper morphism. -/
theorem isFiniteType {f : X ⟶ Y} (hY : IsAlgebraicSpace B S hS Y)
    (hf : HasCompactification B S hS f) : IsFiniteType B S hS f := by
  obtain ⟨X', j, p, hX', hj, hjqc, hp, rfl⟩ := hf
  exact isFiniteType_comp' B S hS j p hX' hY
    ⟨isLocallyOfFiniteType_of_isImmersion B S hS j (isImmersion_of_isOpenImmersion B S hS hj),
      hjqc⟩ hp.2.1

/-- **A quasi-compact open subspace of a compactifiable space is compactifiable**, in the same
ambient proper space: the composite of two quasi-compact open immersions is one. -/
theorem of_isOpenImmersion {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : U ⟶ X)
    (hX : IsAlgebraicSpace B S hS X) (hi : IsOpenImmersion B S hS i)
    (hiqc : IsQuasiCompact B S hS i) {f : X ⟶ Y} (hf : HasCompactification B S hS f) :
    HasCompactification B S hS (i ≫ f) := by
  obtain ⟨X', j, p, hX', hj, hjqc, hp, rfl⟩ := hf
  rw [← Category.assoc]
  exact of_isOpenImmersion_isProper (i ≫ j) p hX' (isOpenImmersion_comp B S hS i j hi hj)
    (IsQuasiCompact.comp B S hS hX hX' hiqc hjqc) hp

end HasCompactification

end AlgebraicGeometry.Space

end
