module

public import StacksFrontier.Deformation.Examples.Geometric.SpecialFibreIdealSheaf

/-!
# Recognizing the special fibre from its ideal sheaf

`Deformation.Examples.ker_eq_baseIdeal_of_isPullback` reads the ideal sheaf of a base change of
the closed point `Spec k ⟶ Spec A`: it is `𝔪 𝒪` for `𝔪` the maximal ideal of `A`. This file
proves the converse: a closed immersion into a scheme over `Spec A` whose ideal sheaf is `𝔪 𝒪`
*is* the special fibre, i.e. its square over the closed point is cartesian.

The essential-surjectivity direction of [Stacks, Tag 0E3X] constructs the target of a
deformation of a morphism as a thickening of `Y`, and so learns its ideal sheaf before it
knows anything about fibre products; what the deformation category asks of it is the cartesian
square. That is exactly the implication proved here.

## Main results

* `Deformation.Examples.isPullback_of_ker_eq_baseIdeal` — **a closed immersion cut out by
  `𝔪 𝒪` is the base change of the closed point.**
* `Deformation.Examples.isPullback_of_ker_eq_baseIdeal_of_eq` — the same with the commuting
  square presented as a factorization through the closed point, which is the shape a
  thickening over the base provides.

## Implementation notes

Both closed immersions into the ambient scheme — the given one and the first projection of the
canonical fibre product — are cut out by `𝔪 𝒪`: the second by
`Deformation.Examples.ker_eq_baseIdeal_of_isPullback` applied to the canonical square, the
first by hypothesis. Mathlib's `AlgebraicGeometry.IsClosedImmersion.isIso_of_ker_eq` turns the
equality of ideal sheaves into invertibility of the comparison morphism into the fibre product,
and `CategoryTheory.IsPullback.of_iso_pullback` transports the universal property across it.

Nothing here is specific to the structure sheaf or to flatness; the statement is about an
arbitrary scheme over the spectrum of an object of `𝒞_Λ`.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **A closed immersion cut out by `𝔪 𝒪` is the base change of the closed point.** Let
`pW : W ⟶ Spec A` be a scheme over an object of `𝒞_Λ` and let `i : Z ⟶ W` be a closed immersion
over the closed point `Spec k ⟶ Spec A` whose ideal sheaf is
`Stacks.BaseAdicFiltration.baseIdeal pW 𝔪`. Then the square exhibiting `i` over the closed
point is cartesian.

This is the converse of `Deformation.Examples.ker_eq_baseIdeal_of_isPullback`. -/
theorem isPullback_of_ker_eq_baseIdeal {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {W Z : Scheme.{u}} (pW : W ⟶ baseSpec A) (i : Z ⟶ W) [IsClosedImmersion i]
    (q : Z ⟶ Spec (.of k)) (hcomm : i ≫ pW = q ≫ residueSpecMap A)
    (hk : i.ker = Stacks.BaseAdicFiltration.baseIdeal pW (IsLocalRing.maximalIdeal A)) :
    IsPullback i q pW (residueSpecMap A) := by
  have := residueSpecMap_isClosedImmersion A
  have hp : IsPullback (pullback.fst pW (residueSpecMap A))
      (pullback.snd pW (residueSpecMap A)) pW (residueSpecMap A) :=
    IsPullback.of_hasPullback _ _
  have : IsClosedImmersion (pullback.fst pW (residueSpecMap A)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) hp.flip
      (residueSpecMap_isClosedImmersion A)
  have hkf : (pullback.fst pW (residueSpecMap A)).ker =
      Stacks.BaseAdicFiltration.baseIdeal pW (IsLocalRing.maximalIdeal A) :=
    ker_eq_baseIdeal_of_isPullback pW hp
  have : IsIso (pullback.lift i q hcomm) :=
    IsClosedImmersion.isIso_of_ker_eq i (pullback.fst pW (residueSpecMap A))
      (pullback.lift i q hcomm) (pullback.lift_fst _ _ _) (hk.trans hkf.symm)
  exact IsPullback.of_iso_pullback ⟨hcomm⟩ (asIso (pullback.lift i q hcomm))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-- **The same criterion with the square presented as a factorization over the base.** A
thickening of a scheme over the residue field into a scheme over `Spec A` comes with its
structure morphisms, and the commuting square is the statement that the thickening is a
morphism over `Spec A` once the lower scheme is read over `Spec A` through the closed point. -/
theorem isPullback_of_ker_eq_baseIdeal_of_eq {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {W Z : Scheme.{u}} (pW : W ⟶ baseSpec A) (i : Z ⟶ W) [IsClosedImmersion i]
    (q : Z ⟶ Spec (.of k)) {g : Z ⟶ baseSpec A} (hg : i ≫ pW = g)
    (hq : q ≫ residueSpecMap A = g)
    (hk : i.ker = Stacks.BaseAdicFiltration.baseIdeal pW (IsLocalRing.maximalIdeal A)) :
    IsPullback i q pW (residueSpecMap A) :=
  isPullback_of_ker_eq_baseIdeal pW i q (hg.trans hq.symm) hk

end Deformation.Examples

end
