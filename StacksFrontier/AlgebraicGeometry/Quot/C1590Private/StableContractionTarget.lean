module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.ContractionGenus
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.StableModelUniqueness
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.AmpleNoRationalBridge
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ProperFibreDimensionVanishing
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilies

/-!
# The target of a stable contraction

Let `c : X ⟶ Y` be a stable contraction (the conditions of Stacks 0E7Q) of a proper nodal curve
`X` of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k`. Then `c` changes neither the
cohomology of the structure sheaf nor the genus, and `Y` has neither rational tails nor rational
bridges. So if `X` has genus at least two, `Y` satisfies the fibre conditions of a stable family
of curves (Stacks 0E75).

## Main results

* `AlgebraicGeometry.C1590Private.contractionCohomologyObjIso`: `Hⁿ(X, 𝒪_X) ≅ Hⁿ(Y, 𝒪_Y)` for a
  proper morphism with `𝒪_Y = c_*𝒪_X`, `R¹c_*𝒪_X = 0` and fibres of dimension at most one.
* `AlgebraicGeometry.C1590Private.IsStableContraction.genus_eq`.
* `AlgebraicGeometry.C1590Private.IsStableContraction.hasGenusTwoNoRationalTailNoRationalBridge`.

## References

* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
* [Stacks Project, Tag 0E3P](https://stacks.math.columbia.edu/tag/0E3P)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Stacks.Cohomology.AffineBase

universe u

namespace AlgebraicGeometry.C1590Private

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

/-- **A contraction with `𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0` does not change the cohomology of the
structure sheaf**, when its fibres have dimension at most one: `Hⁿ(X, 𝒪_X) ≅ Hⁿ(Y, 𝒪_Y)` after
restriction of scalars along `c.appTop`. The higher direct images vanish (`R¹` by hypothesis,
`Rⁱ` for `i ≥ 2` by the fibre dimension, Stacks 0E7D), so the Leray collapse of Stacks 089W
applies. -/
def contractionCohomologyObjIso {X Y : Scheme.{u}} (c : X ⟶ Y) [IsProper c]
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (hR : IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    (hdim : ∀ y : Y, topologicalKrullDim (c.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞)) (n : ℕ) :
    (ModuleCat.restrictScalars c.appTop.hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (SheafOfModules.unit X.ringCatSheaf)) ≅
      ((moduleGlobalSections Y).rightDerived n).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  letI : HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
  letI : HasDerivedCategory.{u + 1} Y.Modules := HasDerivedCategory.standard _
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} Γ(Y, ⊤)) := HasDerivedCategory.standard _
  haveI : IsIso (structureSheafToPushforward c) := hO
  let R := ModuleCat.restrictScalars.{u} c.appTop.hom
  have _ : R.Additive := ⟨by intros; rfl⟩
  have _ : PreservesFiniteLimits R := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have _ : PreservesFiniteColimits R := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have _ : R.PreservesHomology := Functor.preservesHomologyOfExact R
  (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (moduleGlobalSections X) R
        (Scheme.Modules.pushforward c ⋙ moduleGlobalSections Y)
        (sectionsRestrictionIsoTop c) n).app (SheafOfModules.unit X.ringCatSheaf) ≪≫
    Stacks.AcyclicCollapse.objIso (Scheme.Modules.pushforward c) (moduleGlobalSections Y)
      (Stacks.Cohomology.ClosedImmersion.rightAcyclic_moduleGlobalSections_pushforward_injective c)
      (fun m hm => by
        rcases Nat.lt_or_ge m 2 with h | h
        · obtain rfl : m = 1 := by omega
          exact hR
        · have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
          exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ m _).2
            (open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
              isZero_rightDerivedPlus_pushforward_of_forall_fiber_dim_le c hdim _ (m : ℤ)
                (by exact_mod_cast h))) n ≪≫
    (((moduleGlobalSections Y).rightDerived n).mapIso
      (asIso (structureSheafToPushforward c))).symm

section Stable

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  {gY : Y ⟶ Spec (.of k)} {c : X ⟶ Y}

/-- The structure maps of `X` and `Y` over `k` are compatible with `c.appTop`. -/
private theorem comp_appTop_eq_of_isStableContraction
    (h : Stacks.Curves.StableModel.IsStableContraction f gY c) :
    ((Scheme.ΓSpecIso (.of k)).inv ≫ gY.appTop) ≫ c.appTop =
      (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop := by
  rw [Category.assoc, ← Scheme.Hom.comp_appTop, h.comp_eq]

/-- **A stable contraction does not change the genus.** -/
theorem IsStableContraction.genus_eq [IsProper f]
    (h : Stacks.Curves.StableModel.IsStableContraction f gY c)
    (hdim : topologicalKrullDim X = 1) : genus gY = genus f := by
  have : IsProper gY := h.isProper
  have : IsProper (c ≫ gY) := by
    rw [h.comp_eq]
    infer_instance
  have : IsProper c := IsProper.of_comp c gY
  have hcdim : ∀ y : Y, topologicalKrullDim (c.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) := fun y =>
    (Topology.IsInducing.topologicalKrullDim_le (c.fiberι y).isEmbedding.isInducing).trans
      hdim.le
  have hgf := congrArg CommRingCat.Hom.hom (comp_appTop_eq_of_isStableContraction h).symm
  rw [CommRingCat.hom_comp] at hgf
  have e : structureSheafCohomology f 1 ≅ structureSheafCohomology gY 1 :=
    Stacks.Curves.structureSheafCohomologyIsoRestrict k f 1 ≪≫
      ModuleCat.restrictScalarsComp'App _ _ _ hgf _ ≪≫
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ gY.appTop).hom).mapIso
        (contractionCohomologyObjIso c h.isIso_unitToPushforwardObjUnit h.isZero_rightDerived_one
          hcdim 1) ≪≫
      (Stacks.Curves.structureSheafCohomologyIsoRestrict k gY 1).symm
  rw [genus_eq_finrank_structureSheafCohomology, genus_eq_finrank_structureSheafCohomology]
  exact e.toLinearEquiv.finrank_eq.symm

/-- **The target of a stable contraction is a stable curve.** Let `X` be a proper curve of
dimension one over `k` with `H⁰(X, 𝒪_X) = k` and genus at least two, and `c : X ⟶ Y` a stable
contraction. Then `Y` has genus at least two and has neither rational tails (its dualizing sheaf
being ample, `AlgebraicGeometry.not_isRationalTail_of_isAmple_dualizingSheafOverField`) nor
rational bridges
(`AlgebraicGeometry.C1590Private.not_isRationalBridge_of_isAmple_dualizingSheafOverField`). -/
theorem IsStableContraction.hasGenusTwoNoRationalTailNoRationalBridge [IsProper f]
    (h : Stacks.Curves.StableModel.IsStableContraction f gY c)
    (hdim : topologicalKrullDim X = 1) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hg : 2 ≤ genus f) : HasGenusTwoNoRationalTailNoRationalBridge k gY := by
  let : Y.Over (Spec (.of k)) := ⟨gY⟩
  have : IsProper gY := h.isProper
  have : IsProper (Y ↘ Spec (.of k)) := h.isProper
  have : ConnectedSpace X := connectedSpace_of_isIso_globalSections k f
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ gY.appTop) := by
    have hc : IsIso c.appTop :=
      Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c
        h.isIso_unitToPushforwardObjUnit ⊤
    have : IsIso (((Scheme.ΓSpecIso (.of k)).inv ≫ gY.appTop) ≫ c.appTop) := by
      rw [comp_appTop_eq_of_isStableContraction h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ c.appTop
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop) :=
    inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ gY.appTop))
  have : IsReduced Y := h.isReduced
  obtain ⟨hω, hL⟩ := h.isAmple
  have : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k))) := hω
  have hL' : Scheme.Modules.IsAmple Y
      (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k))) := hL
  refine ⟨(IsStableContraction.genus_eq h hdim).symm ▸ hg, fun C hC => ?_,
    ⟨h.isProper, fun C => ?_⟩⟩
  · have : IsIntegral C.subscheme := hC.1
    exact not_isRationalTail_of_isAmple_dualizingSheafOverField k Y h.topologicalKrullDim_eq hL' C
      (h.isInvertible_dualizingSheafOverField_subscheme C hC.1
        (Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalTail k Y
          h.topologicalKrullDim_eq C hC)) hC
  · exact not_isRationalBridge_of_isAmple_dualizingSheafOverField k Y h.topologicalKrullDim_eq
      h.hasAtWorstNodalSingularities hL' C

end Stable

end AlgebraicGeometry.C1590Private

end
