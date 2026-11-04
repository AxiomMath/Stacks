module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleTorsionDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeUnconditional
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedUnitComposition

/-!
# Inverse image to the big étale topos and direct image along a proper morphism

Let `S` be a scheme and `f : Y ⟶ X` a proper morphism of algebraic spaces over `S`; write
`π_X : Sh((Spaces/X)_étale) ⟶ Sh(X_étale)` for the comparison of the big and the small étale
topoi. Stacks 0DGD says:

1. `π_X⁻¹ ∘ f_{small,*} = f_{big,*} ∘ π_Y⁻¹` as functors `Sh(Y_étale) ⥤ Sh((Spaces/X)_étale)`;
2. `π_X⁻¹ R f_{small,*} K = R f_{big,*} π_Y⁻¹ K` for `K ∈ D⁺(Y_étale)` with torsion cohomology
   sheaves;
3. `π_X⁻¹ R f_{small,*} K = R f_{big,*} π_Y⁻¹ K` for every `K ∈ D(Y_étale)` if `f` is finite.

In each part the identification is the canonical base change map, and the statement is that it is
an isomorphism.

## The argument

Part (1) is proper base change for sheaves of sets on algebraic spaces (Stacks 0DG0) applied to
each base change of `f` along an object `X' ⟶ X` of the big site
(`AlgebraicGeometry.BigEtaleSpaceSite.isIso_bigToSmallEtaleBaseChange_of_isProper`). Part (2)
restricts the derived base change map to the spaces-étale site of every such `X'`, where it becomes
the base change map of Stacks 0DG3
(`AlgebraicGeometry.BigEtaleSpaceSite.isIso_bigToSmallEtaleDerivedBaseChange_app`, with the proper
base change theorems for schemes, Stacks 0A3U and Stacks 095T, supplied here).
For part (3), both direct images are exact when `f` is finite (Stacks 0A4K, and Stacks 0DGA for
the big direct image), so both derived functors are computed by every complex, and the derived
base change map is then invertible because the underived one is, by part (1).

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.isIso_bigToSmallEtaleDerivedBaseChange_of_isFinite`: part
  (3).
* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtale_pushforward_baseChange_of_isProper`:
  **Stacks 0DGD**, all three parts.

## Implementation notes

Standard model: the derived base change map `bigToSmallEtaleDerivedBaseChange` and the reduction
of part (2) exist only for `HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 0DGD](https://stacks.math.columbia.edu/tag/0DGD)
* [Stacks Project, Tag 0DG0](https://stacks.math.columbia.edu/tag/0DG0)
* [Stacks Project, Tag 0DG3](https://stacks.math.columbia.edu/tag/0DG3)
* [Stacks Project, Tag 0DGA](https://stacks.math.columbia.edu/tag/0DGA)
* [Stacks Project, Tag 0A4K](https://stacks.math.columbia.edu/tag/0A4K)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Homology.DerivedSquare (totalRightDerived totalRightDerivedUnit derivedSquare)

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

attribute [local instance] HasDerivedCategory.standard bigToSmallAbelianInverseImage_additive
  smallEtaleAbelianInverseImage_additive

/-- **Stacks 0DGD, part (3), as invertibility of the base change map.** For a finite morphism
`f : Y ⟶ X` of algebraic spaces of the big étale site, the canonical base change map
`π_X⁻¹ R f_{small,*} ⟶ R f_{big,*} π_Y⁻¹` of functors on the unbounded derived category of
abelian sheaves on `Y_étale` is an isomorphism. -/
theorem isIso_bigToSmallEtaleDerivedBaseChange_of_isFinite {X Y : T.Spaces} (f : Y ⟶ X)
    (hf : Space.IsFinite T.fppfSite S T.fppf_mem f.hom) :
    IsIso (bigToSmallEtaleDerivedBaseChange T f) := by
  have hp : Space.IsProper T.fppfSite S T.fppf_mem f.hom :=
    ((Space.isFinite_iff_isAffineHom_and_isProper T.fppfSite S T.fppf_mem Y.2 X.2 f.hom).mp
      hf).2
  have := isIso_bigToSmallEtaleAbelianBaseChange T f hp
    isIso_smallEtaleSetBaseChange_of_isProper_forall
  have := smallEtalePushforward_preservesFiniteColimits_of_isFinite T f hf
  have := bigEtalePushforward_preservesFiniteColimits_of_isFinite T f hf
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  obtain ⟨M, hM⟩ := HomotopyCategory.quotient_obj_surjective (DerivedCategory.Qh.objPreimage K)
  let e : K ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M) :=
    (DerivedCategory.Qh.objObjPreimageIso K).symm ≪≫ eqToIso (by rw [← hM])
  rw [NatTrans.isIso_app_iff_of_iso _ e]
  exact (Stacks.Homology.DerivedSquare.isIso_derivedSquare_app_iff _ _
    (Stacks.Homology.DerivedSquare.isIso_totalRightDerivedUnit_app_of_exact _ M)).mpr
      (Stacks.Homology.DerivedSquare.isIso_totalRightDerivedUnit_app_of_exact
        (bigEtalePushforward T f) _)

/-- **Stacks 0DGD.** Let `S` be a scheme and `f : Y ⟶ X` a proper morphism of algebraic spaces
over `S` (objects of the big étale site `T` of algebraic spaces over `S`). Write
`π_X : Sh((Spaces/X)_étale) ⟶ Sh(X_étale)` (`bigToSmallEtaleMorphism T X`) for the comparison
of the big étale topos with the small étale topos `Sh(X_étale)` (the spaces-étale site of `X`).
Then:

1. the canonical base change map `π_X⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_Y⁻¹` of functors from
   sheaves of sets on `Y_étale` to sheaves of sets on `(Spaces/X)_étale`
   (`bigToSmallEtaleBaseChange T f`; its target `f_{big,*}` is restriction along
   `Y ×_X - : Spaces/X ⥤ Spaces/Y`) is an isomorphism;
2. for every `K` in `D⁺(Y_étale)` (`K.IsGE n` for some `n`) whose cohomology sheaves are torsion,
   the canonical base change map `π_X⁻¹ R f_{small,*} K ⟶ R f_{big,*} π_Y⁻¹ K` of Stacks 07A7
   (`bigToSmallEtaleDerivedBaseChange T f`, on the derived categories of abelian sheaves) is an
   isomorphism;
3. if `f` is finite, the canonical base change map `π_X⁻¹ R f_{small,*} K ⟶ R f_{big,*} π_Y⁻¹ K`
   is an isomorphism for every `K` in the unbounded derived category `D(Y_étale)`. -/
@[stacks 0DGD]
theorem bigToSmallEtale_pushforward_baseChange_of_isProper {X Y : T.Spaces} (f : Y ⟶ X)
    (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom) :
    IsIso (bigToSmallEtaleBaseChange T f) ∧
      (∀ (K : DerivedCategory
          (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})) (n : ℤ),
        K.IsGE n → HasTorsionCohomology T K →
          IsIso ((bigToSmallEtaleDerivedBaseChange T f).app K)) ∧
      (Space.IsFinite T.fppfSite S T.fppf_mem f.hom →
        ∀ K : DerivedCategory
          (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1}),
          IsIso ((bigToSmallEtaleDerivedBaseChange T f).app K)) :=
  ⟨isIso_bigToSmallEtaleBaseChange_of_isProper T f hf,
    fun K n hK hT ↦ isIso_bigToSmallEtaleDerivedBaseChange_app T f hf
      isIso_smallEtaleSetBaseChange_of_isProper_forall
      (fun f _ ↦ Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper f) K n hK hT,
    fun hfin K ↦ by
      have := isIso_bigToSmallEtaleDerivedBaseChange_of_isFinite T f hfin
      infer_instance⟩

end AlgebraicGeometry.BigEtaleSpaceSite

end
