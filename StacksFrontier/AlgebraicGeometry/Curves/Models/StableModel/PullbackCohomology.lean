module

public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.StableModel
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.AffineFromVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.GloballyGeneratedVanishing
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePushforwardPullback

/-!
# First cohomology of a pullback along a stable contraction

Let `c : X ⟶ Y` be a stable contraction of a curve `X` over a field ([Stacks, Tag 0E7Q]): `c` has
`𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0`. For an invertible `𝒪_Y`-module `𝒢`:

* `R¹c_*(c^*𝒢) = 0`, because the question is local on `Y`, and over an open `V` on which `𝒢` is
  trivial the restriction of `c^*𝒢` to `c⁻¹(V)` is the structure sheaf, whose first higher direct
  image along `c ∣_ V` is the restriction of `R¹c_*𝒪_X = 0` ([Stacks, Tag 01E5]);
* `c_*c^*𝒢 ≅ 𝒢` by the projection formula, `𝒪_Y = c_*𝒪_X` and `𝒢` being invertible;
* the low-degree Leray sequence `0 ⟶ H¹(Y, c_*ℱ) ⟶ H¹(X, ℱ) ⟶ H⁰(Y, R¹c_*ℱ)` at `ℱ = c^*𝒢`
  then puts `H¹(X, c^*𝒢)` between `H¹(Y, 𝒢)` and `0`.

So `H¹(X, c^*𝒢) = 0` as soon as `H¹(Y, 𝒢) = 0`. Only the low-degree part of the Leray sequence is
used, so neither properness of `c` nor the vanishing of the higher direct images in degrees `≥ 2`
is needed.

## Main results

* `Stacks.Curves.StableModel.isZero_rightDerived_one_of_isZero_pushforward`: the low-degree Leray
  sandwich `H¹(Y, g_*M) = 0`, `R¹g_*M = 0` ⟹ `H¹(X, M) = 0`, for any morphism of schemes.
* `Stacks.Curves.StableModel.isZero_rightDerived_one_pushforward_pullback`: `R¹c_*(c^*𝒢) = 0`
  for `𝒢` invertible when `R¹c_*𝒪_X = 0`.
* `Stacks.Curves.StableModel.IsStableContraction.isZero_rightDerived_one_pullback`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Curves.StableModel

open Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- **The low-degree Leray sandwich.** For a morphism of schemes `g : U ⟶ V` and an `𝒪_U`-module
`M`, if `H¹(V, g_*M) = 0` and `R¹g_*M = 0` then `H¹(U, M) = 0`: the low-degree Leray sequence puts
`H¹(U, M)` between `H¹(V, g_*M)` and `Γ(V, R¹g_*M)`. -/
theorem isZero_rightDerived_one_of_isZero_pushforward {U V : Scheme.{u}} (g : U ⟶ V)
    (M : U.Modules)
    (hH : IsZero (((moduleGlobalSections V).rightDerived 1).obj
      ((Scheme.Modules.pushforward g).obj M)))
    (hR : IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj M)) :
    IsZero (((moduleGlobalSections U).rightDerived 1).obj M) := by
  let gR := g.toLRSHom.toShHom
  let FAb := (SheafOfModules.toSheaf U.ringCatSheaf).obj M
  let L := Stacks.Cohomology.LerayLowDegree.abelianLerayLowDegreeData.{u, u} gR.hom.base
  have hSource : IsZero ((Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} gR.hom.base ⋙
      Stacks.Cohomology.LerayLowDegree.abelianCohomology.{u, u} V.toTopCat ⊤ 1).obj FAb) := by
    have hforget := Functor.map_isZero
      (forget₂ (ModuleCat.{u} (V.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u}) hH
    exact hforget.of_iso
      ((Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso
        V.ringCatSheaf ⊤ 1).app ((Scheme.Modules.pushforward g).obj M)).symm
  have hTarget : IsZero ((Stacks.Cohomology.LerayLowDegree.abelianSections.{u, u}
      V.toTopCat ⊤).obj
        (((Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u}
          gR.hom.base).rightDerived 1).obj FAb)) := by
    refine Functor.map_isZero
      (Stacks.Cohomology.LerayLowDegree.abelianSections.{u, u} V.toTopCat ⊤) ?_
    exact (Functor.map_isZero (SheafOfModules.toSheaf V.ringCatSheaf) hR).of_iso
      ((Stacks.Cohomology.ModulePushforwardComparison.rightDerived_modulePushforward_forget_iso
        gR 1).app M).symm
  have hAbH₁ : IsZero ((Stacks.Cohomology.LerayLowDegree.abelianCohomology.{u, u}
      U.toTopCat ⊤ 1).obj FAb) :=
    (L.exact FAb).isZero_of_both_zeros (hSource.eq_zero_of_src _) (hTarget.eq_zero_of_tgt _)
  refine (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
    U.ringCatSheaf ⊤ 1 _).2 ?_
  exact hAbH₁.of_iso
    (((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
        U.ringCatSheaf ⊤ 1).app M).symm ≪≫
      (Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso U.ringCatSheaf ⊤ 1).app M)

/-- **`R¹c_*(c^*𝒢) = 0` for an invertible `𝒢` when `R¹c_*𝒪_X = 0`.** The vanishing is local on
`Y`; over an open `V` trivializing `𝒢`, the restriction of `c^*𝒢` to `c⁻¹(V)` is
`(c ∣_ V)^*(𝒢|_V) ≅ (c ∣_ V)^*𝒪_V ≅ 𝒪_{c⁻¹V}`, and `R¹(c ∣_ V)_*𝒪_{c⁻¹V}` is the restriction of
`R¹c_*𝒪_X` ([Stacks, Tag 01E5]). -/
theorem isZero_rightDerived_one_pushforward_pullback {X Y : Scheme.{u}} (c : X ⟶ Y)
    (h0 : IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf))) (G : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property G] :
    IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      ((Scheme.Modules.pullback c).obj G)) := by
  let : ∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} Z.Modules := fun Z =>
    HasDerivedCategory.standard Z.Modules
  have h0' : IsZero (firstDirectImageStructureSheaf c) :=
    (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ 1 _).1 h0
  refine (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ 1 _).2 ?_
  obtain ⟨V, hV, e⟩ := Stacks.Modules.exists_restrict_iso_unit_of_isInvertible G
  refine isZero_of_isZero_restrict_cover V hV _ fun y => ?_
  have h1 : IsZero (((Scheme.Modules.pushforward (c ∣_ V y)).rightDerivedPlus ((1 : ℕ) : ℤ)).obj
      (SheafOfModules.unit (c ⁻¹ᵁ V y).toScheme.ringCatSheaf)) := by
    rw [Nat.cast_one]
    exact isZero_firstDirectImage_structureSheaf_restrict c (V y) h0'
  let e₁ : (Scheme.Modules.restrictFunctor (c ⁻¹ᵁ V y).ι).obj ((Scheme.Modules.pullback c).obj G) ≅
      SheafOfModules.unit (c ⁻¹ᵁ V y).toScheme.ringCatSheaf :=
    (pullbackRestrictComparison c (V y) G).symm ≪≫
      (Scheme.Modules.pullback (c ∣_ V y)).mapIso (e y).some ≪≫
      Scheme.Modules.pullbackUnitIso (c ∣_ V y)
  have h2 : IsZero (((Scheme.Modules.pushforward (c ∣_ V y)).rightDerivedPlus ((1 : ℕ) : ℤ)).obj
      ((Scheme.Modules.restrictFunctor (c ⁻¹ᵁ V y).ι).obj ((Scheme.Modules.pullback c).obj G))) :=
    h1.of_iso (((Scheme.Modules.pushforward (c ∣_ V y)).rightDerivedPlus ((1 : ℕ) : ℤ)).mapIso e₁)
  exact h2.of_iso
    (Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso c (V y) 1
      _).symm

namespace IsStableContraction

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  {g : Y ⟶ Spec (.of k)} {c : X ⟶ Y}

/-- **Vanishing of `H¹` of a pullback along a stable contraction.** If `c : X ⟶ Y` is a stable
contraction of a curve `X` of dimension at most one and `𝒢` is an invertible `𝒪_Y`-module with
`H¹(Y, 𝒢) = 0`, then `H¹(X, c^*𝒢) = 0`.

`R¹c_*(c^*𝒢) = 0` (`isZero_rightDerived_one_pushforward_pullback`) and `c_*c^*𝒢 ≅ 𝒢` (the
unit of `c^* ⊣ c_*` at an invertible module is an isomorphism when `𝒪_Y = c_*𝒪_X`,
`AlgebraicGeometry.Scheme.Modules.isIso_unit_app_of_isIso_c`), so the low-degree Leray sandwich
`isZero_rightDerived_one_of_isZero_pushforward` applies. The dimension hypothesis is not used. -/
theorem isZero_rightDerived_one_pullback (hc : IsStableContraction f g c)
    (_hdim : topologicalKrullDim X ≤ 1) (G : Y.Modules)
    [SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property G]
    (hG : IsZero (((moduleGlobalSections Y).rightDerived 1).obj G)) :
    IsZero (((moduleGlobalSections X).rightDerived 1).obj ((Scheme.Modules.pullback c).obj G)) := by
  have hGs : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property G :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ G).mpr ‹_›
  have hGa : Stacks.Ample.IsInvertibleModule Y G := ‹SheafOfModules.IsInvertible _ _ G›
  have hcc : IsIso c.c :=
    (NatTrans.isIso_iff_isIso_app _).2 fun W =>
      Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c
        hc.isIso_unitToPushforwardObjUnit W.unop
  have hu := Scheme.Modules.isIso_unit_app_of_isIso_c c G
  have hR : IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      ((Scheme.Modules.pullback c).obj G)) :=
    isZero_rightDerived_one_pushforward_pullback c hc.isZero_rightDerived_one G
  refine isZero_rightDerived_one_of_isZero_pushforward c _ ?_ hR
  exact hG.of_iso (((moduleGlobalSections Y).rightDerived 1).mapIso
    (asIso ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app G)).symm)

end IsStableContraction

end Stacks.Curves.StableModel

end
