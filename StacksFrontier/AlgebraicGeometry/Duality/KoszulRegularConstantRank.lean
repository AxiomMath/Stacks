module

public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularNormalExterior

/-!
# `⋀^r 𝒩 [-r]` for a normal sheaf of constant rank

Let `i : X ⟶ Y` be a Koszul-regular immersion whose normal sheaf `𝒩` has constant rank `r`. The
object `⋀^r 𝒩 [-r]` of [Stacks, Tag 0BR0], `Stacks.Duality.KoszulRegular.normalExteriorComplex`,
is defined for a locally constant rank, as a complex with zero differential whose degree-`n` term
is `⋀ⁿ𝒩` on the locus of rank `n`, extended by zero. When the rank is constant this is the single
complex `⋀^r 𝒩` placed in degree `r`.

## Main results

* `Stacks.Duality.KoszulRegular.isZero_normalExteriorTerm_of_ne`: the terms off degree `r` vanish.
* `Stacks.Duality.KoszulRegular.normalExteriorTermIsoOfConstantRank`: the degree-`r` term is
  `⋀^r 𝒩`.
* `Stacks.Duality.KoszulRegular.normalExteriorComplexIsoSingle`: `⋀^r 𝒩 [-r]` is `⋀^r 𝒩` in
  degree `r`.

## References

* [Stacks Project, Tag 0BR0](https://stacks.math.columbia.edu/tag/0BR0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace ExtensionByZeroModules

universe u

namespace Stacks.Duality.KoszulRegular

open Stacks.AlgebraicGeometry.RegularIdealSheaf

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsImmersion i] (hi : IsKoszulRegularImmersion i) (r : ℕ)
  (hr : ∀ x, normalRank i hi x = r)

include hr in
/-- If the normal sheaf has constant rank `r`, the terms of `⋀^r 𝒩 [-r]` off degree `r`
vanish. -/
theorem isZero_normalExteriorTerm_of_ne {n : ℤ} (hn : n ≠ r) :
    IsZero (normalExteriorTerm i hi n) := by
  have hU : ∀ x : X, x ∉ normalRankLocus i hi n := fun x hx =>
    hn (((mem_normalRankLocus i hi).1 hx).symm.trans (by rw [hr x]))
  have hz : ∀ x : X, IsZero (TopCat.Presheaf.stalk (X := X.toTopCat)
      (normalExteriorTerm i hi n).val.presheaf x) := fun x =>
    isZero_stalk_jShriek _ _ _ x (hU x)
  have : IsIso (0 : normalExteriorTerm i hi n ⟶ normalExteriorTerm i hi n) :=
    isIso_of_stalk_isIso _ _ fun x =>
      isIso_of_source_target_iso_zero _ (hz x).isoZero (hz x).isoZero
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← IsIso.hom_inv_id (0 : normalExteriorTerm i hi n ⟶ normalExteriorTerm i hi n),
    zero_comp]

include hr in
/-- If the normal sheaf has constant rank `r`, extension by zero from the rank-`r` locus does not
change `⋀^r 𝒩`: the counit of `j_! ⊣ j^*` there is an isomorphism, the locus being everything. -/
theorem isIso_counit_normalExteriorTerm :
    IsIso ((jShriekAdjunction (normalRankLocus i hi r)
      (structureSheaf X.toRingedSpace.sheaf)).counit.app
      (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf i) r)) :=
  counit_isIso_of_stalk_isZero _ _ _ fun x hx =>
    absurd ((mem_normalRankLocus i hi).2 (by rw [hr x])) hx

include hr in
/-- If the normal sheaf has constant rank `r`, the degree-`r` term of `⋀^r 𝒩 [-r]` is `⋀^r 𝒩`. -/
def normalExteriorTermIsoOfConstantRank :
    normalExteriorTerm i hi r ≅ Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf i) r :=
  @asIso _ _ _ _ _ (isIso_counit_normalExteriorTerm i hi r hr)

include hr in
/-- **`⋀^r 𝒩 [-r]` for a normal sheaf of constant rank `r`** is the single complex `⋀^r 𝒩` in
degree `r`. -/
def normalExteriorComplexIsoSingle :
    normalExteriorComplex i hi ≅ (HomologicalComplex.single _ (ComplexShape.up ℤ) (r : ℤ)).obj
      (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf i) r) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => if h : n = r then
        eqToIso (congrArg (normalExteriorTerm i hi) h) ≪≫
          normalExteriorTermIsoOfConstantRank i hi r hr ≪≫
            (HomologicalComplex.singleObjXIsoOfEq _ _ _ n h).symm
      else (isZero_normalExteriorTerm_of_ne i hi r hr h).iso
        (HomologicalComplex.isZero_single_obj_X _ _ _ n h))
    (fun a b hab => by
      have hab' : a + 1 = b := hab
      by_cases hb : b = r
      · exact (isZero_normalExteriorTerm_of_ne i hi r hr (n := a) (by omega)).eq_of_src _ _
      · exact (HomologicalComplex.isZero_single_obj_X _ _ _ b hb).eq_of_tgt _ _)

end Stacks.Duality.KoszulRegular
