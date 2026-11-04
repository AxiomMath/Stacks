module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.AdicStageKernel
public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.AdicStepHypotheses
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UniversalDirectImage
public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroPushforwardStep
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSourceLift

/-!
# The target of a deformation of a morphism of schemes

Given a family `p : U ⟶ Spec A` flat over an Artinian local base, a closed immersion
`i_X : X ⟶ U` cutting out its special fibre, and a morphism `f : X ⟶ Y` over the base with
`f_*𝒪_X = 𝒪_Y` and `R¹f_*𝒪_X = 0`, there is a scheme `V` over `Spec A` together with

* a morphism `g : U ⟶ V` over `Spec A` whose comparison of structure sheaves is invertible,
  that is, `𝒪_V = g_*𝒪_U`;
* a thickening `i_Y : Y ⟶ V` over `Spec A`;
* the square `i_X ≫ g = f ≫ i_Y`, so `g` restricts to `f` on special fibres.

## Main definitions

* `Deformation.Examples.schemeMorphismSourceTowerInvariant`: the property, at level `n` of the
  `𝔪`-adic tower of `p`, of a scheme `W` over `Spec A` that there are a morphism from the `n`-th
  stage to `W` and a thickening `Y ⟶ W` forming the square above.

## Main results

* `Deformation.Examples.schemeMorphismSourceTowerInvariant_zero`: the property holds at level `0`
  for `W = Y`.
* `Deformation.Examples.schemeMorphismSourceTowerInvariant_step`: the property passes from level
  `n` to level `n + 1` along a square-zero extension.
* `Deformation.Examples.exists_pushforwardTarget_of_specialFibre`: the existence of `V`, `g` and
  `i_Y` as above.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

open Stacks.BaseAdicFiltration

/-- Sheaves of modules on a scheme have finite biproducts. -/
local instance hasFiniteBiproducts_schemeModulesTower (W : Scheme.{u}) :
    HasFiniteBiproducts W.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {A : Type u} [CommRing A] [IsLocalRing A] {U X Y : Scheme.{u}}
  (p : U ⟶ Spec (CommRingCat.of A)) (iX : X ⟶ U) [IsClosedImmersion iX]
  (hkm : iX.ker = baseIdeal p (IsLocalRing.maximalIdeal A))
  (fXY : X ⟶ Y) (q₀ : Y ⟶ Spec (CommRingCat.of A))

/-- At level `n`, this asserts, of a scheme `W` over `Spec A`, that there is a morphism
`gₙ` from the stage `n` of the `𝔪`-adic tower of `p` to `W` with invertible comparison of
structure sheaves and lying over `Spec A`, and a thickening `i_{Y,n} : Y ⟶ W` over `Spec A`,
such that `gₙ` restricts to `f` on the special fibre. -/
def schemeMorphismSourceTowerInvariant :
    ℕ → (W : Scheme.{u}) → (W ⟶ Spec (CommRingCat.of A)) → Prop :=
  fun n W q =>
    ∃ (gn : adicStage p (IsLocalRing.maximalIdeal A) n ⟶ W) (iYn : Y ⟶ W),
      IsIso gn.c ∧ gn ≫ q = adicStageToBase p (IsLocalRing.maximalIdeal A) n ∧
        Stacks.Thickenings.IsThickening iYn ∧ iYn ≫ q = q₀ ∧
          adicStageLift p (IsLocalRing.maximalIdeal A) iX hkm n ≫ gn = fXY ≫ iYn

include hkm in
/-- If `i_X ≫ p = f ≫ q₀` and `𝒪_Y ⟶ f_*𝒪_X` is an isomorphism, then
`schemeMorphismSourceTowerInvariant` holds at level `0` for `Y` over `Spec A` via `q₀`. -/
theorem schemeMorphismSourceTowerInvariant_zero
    (hcomm : iX ≫ p = fXY ≫ q₀)
    (h0 : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit fXY)) :
    schemeMorphismSourceTowerInvariant p iX hkm fXY q₀ 0 Y q₀ := by
  refine ⟨(adicStageZeroIso p (IsLocalRing.maximalIdeal A) iX hkm).inv ≫ fXY, 𝟙 Y, ?_, ?_,
    Stacks.Thickenings.isThickening_of_isIso (𝟙 Y), Category.id_comp _, ?_⟩
  · exact Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_comp _ fXY
      (Scheme.isIso_c_of_isIso_app fXY
        (Scheme.isIso_app_of_isIso_unitToPushforwardUnit fXY h0))
  · rw [Category.assoc, ← hcomm, adicStageToBase, ← adicStageZeroIso_inv_comp
      p (IsLocalRing.maximalIdeal A) iX hkm, Category.assoc]
  · rw [adicStageLift_zero, ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]

include hkm in
/-- Let `A` be Artinian, `p` flat, `𝒪_Y ⟶ f_*𝒪_X` an isomorphism and `R¹f_*𝒪_X = 0`. If
`schemeMorphismSourceTowerInvariant` holds at level `n` for `W` over `Spec A`, then there are a
square-zero extension `E` of `W` and a realization `r` of `E` for which it holds at level `n + 1`
for the ambient scheme of `r`. -/
theorem schemeMorphismSourceTowerInvariant_step [IsArtinianRing A] [AlgebraicGeometry.Flat p]
    (h0 : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit fXY))
    (hR : IsZero (((Scheme.Modules.pushforward fXY).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    (n : ℕ) (W : Scheme.{u}) (q : W ⟶ Spec (CommRingCat.of A))
    (hPn : schemeMorphismSourceTowerInvariant p iX hkm fXY q₀ n W q) :
    ∃ E : Stacks.Thickenings.SquareZeroExtension q, ∃ r : Stacks.Thickenings.Realization E,
      schemeMorphismSourceTowerInvariant p iX hkm fXY q₀ (n + 1) r.ambient r.toBase := by
  obtain ⟨gn, iYn, hgc, hgq, hiYt, hiYq, hsq⟩ := hPn
  have : IsClosedImmersion iYn := hiYt.1
  have := isClosedImmersion_adicStageLift p (IsLocalRing.maximalIdeal A) iX hkm n
  obtain ⟨E, k, ⟨eI⟩, r₁, hamb, him, htb⟩ :=
    exists_isoDirectSum_squareZeroExtension_adicStage_unit_of_eq p iX hkm n hgq
  obtain ⟨amb, siso, imm, tb, hfo, hob, hie, hte⟩ := r₁
  subst hamb
  obtain rfl := eq_of_heq him
  obtain rfl := eq_of_heq htb
  have hbiq :=
    isZero_rightDerived_one_pushforward_biprod_unit_of_square fXY
      (adicStageLift p (IsLocalRing.maximalIdeal A) iX hkm n) iYn gn hsq hR k
  have hRE : IsZero (((Scheme.Modules.pushforward gn).rightDerived 1).obj E.I) :=
    hbiq.of_iso (((Scheme.Modules.pushforward gn).rightDerived 1).mapIso eI)
  have hbqc :=
    isQuasicoherent_pushforward_biprod_unit_of_square fXY
      (adicStageLift p (IsLocalRing.maximalIdeal A) iX hkm n) iYn gn hsq h0 k
  have hQC : ((Scheme.Modules.pushforward gn).obj E.I).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent W.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.pushforward gn).mapIso eI).symm hbqc
  obtain ⟨E₂, r₂, g', hg'c, hg'imm, hg'base⟩ :=
    E.exists_realization_pushforward_of_isZero_rightDerived gn q hRE hQC
      { ambient := adicStage p (IsLocalRing.maximalIdeal A) (n + 1)
        sheafedIso := siso
        immersion := adicStageSucc p (IsLocalRing.maximalIdeal A) n
        toBase := adicStageToBase p (IsLocalRing.maximalIdeal A) (n + 1)
        immersion_isFirstOrder := hfo
        over_base := hob
        inclusion_eq := hie
        toBase_eq := hte }
  refine ⟨E₂, r₂, g', iYn ≫ r₂.immersion, hg'c, hg'base, ?_, ?_, ?_⟩
  · exact Stacks.Thickenings.isThickening_comp hiYt r₂.immersion_isFirstOrder.isThickening
  · rw [Category.assoc, r₂.over_base, hiYq]
  · rw [← adicStageLift_comp_adicStageSucc p (IsLocalRing.maximalIdeal A) iX hkm n,
      Category.assoc, hg'imm, ← Category.assoc, hsq, Category.assoc]

include hkm in
/-- Let `p : U ⟶ Spec A` be flat over an Artinian local base, let `i_X : X ⟶ U` cut
out its special fibre, and let `f : X ⟶ Y` be a morphism over `Spec A` with `f_*𝒪_X = 𝒪_Y` and
`R¹f_*𝒪_X = 0`. Then there are a scheme `V` over `Spec A`, a morphism `g : U ⟶ V` over
`Spec A` with `𝒪_V = g_*𝒪_U`, and a thickening `i_Y : Y ⟶ V` over `Spec A`, such that `g`
restricts to `f` on special fibres. -/
theorem exists_pushforwardTarget_of_specialFibre [IsArtinianRing A] [AlgebraicGeometry.Flat p]
    (hcomm : iX ≫ p = fXY ≫ q₀)
    (h0 : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit fXY))
    (hR : IsZero (((Scheme.Modules.pushforward fXY).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    ∃ (V : Scheme.{u}) (pV : V ⟶ Spec (CommRingCat.of A)) (g : U ⟶ V) (iY : Y ⟶ V),
      IsIso g.c ∧ g ≫ pV = p ∧ Stacks.Thickenings.IsThickening iY ∧ iY ≫ pV = q₀ ∧
        iX ≫ g = fXY ≫ iY := by
  obtain ⟨N, hNiso⟩ := exists_isIso_adicStageι p
  obtain ⟨V, pV, -, hPN, -, -⟩ :=
    Stacks.Thickenings.exists_thickening_of_iterate N
      (schemeMorphismSourceTowerInvariant p iX hkm fXY q₀)
      (schemeMorphismSourceTowerInvariant_zero p iX hkm fXY q₀ hcomm h0)
      fun n W q _ h =>
        schemeMorphismSourceTowerInvariant_step p iX hkm fXY q₀ h0 hR n W q h
  obtain ⟨gN, iYN, hgc, hgq, hiYt, hiYq, hsq⟩ := hPN
  refine ⟨V, pV, inv (adicStageι p (IsLocalRing.maximalIdeal A) N) ≫ gN, iYN, ?_, ?_, hiYt,
    hiYq, ?_⟩
  · exact Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_comp _ gN hgc
  · rw [Category.assoc, hgq, adicStageToBase, IsIso.inv_hom_id_assoc]
  · rw [← Category.assoc, ← (IsIso.eq_comp_inv _).2
      (adicStageLift_comp_adicStageι p (IsLocalRing.maximalIdeal A) iX hkm N), hsq]

end Deformation.Examples

end
