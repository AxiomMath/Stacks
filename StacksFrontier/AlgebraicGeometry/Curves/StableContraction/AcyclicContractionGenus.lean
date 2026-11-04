module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.ContractionGenus
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.IsolatedPoints

/-!
# Acyclic morphisms preserve the cohomology of the structure sheaf

Let `c : X ⟶ Y` be a morphism of schemes with `𝒪_Y = c_*𝒪_X` and `Rⁱc_*𝒪_X = 0` for `i > 0`.
Then `Hⁿ(X, 𝒪_X) ≅ Hⁿ(Y, 𝒪_Y)` for every `n`, by the Leray spectral sequence, which here
collapses: `RΓ(X, -) = RΓ(Y, -) ∘ Rc_*` and `Rc_*𝒪_X = 𝒪_Y`. In particular, over a field `k`,
`X` and `Y` have the same genus and the same global functions. This is how the genus passes
along the contractions in the proof of [Stacks, Tag 0E97].

## Main results

* `Stacks.Curves.acyclicCohomologyObjIso`: `Hⁿ(X, 𝒪_X) ≅ Hⁿ(Y, 𝒪_Y)`.
* `Stacks.Curves.genus_eq_of_isIso_unitToPushforwardObjUnit`: the genera agree.
* `Stacks.Curves.isIso_globalSections_of_isIso_unitToPushforwardObjUnit` and
  `Stacks.Curves.isIso_globalSections_comp_of_isIso_unitToPushforwardObjUnit`: `H⁰(Y, 𝒪_Y) = k`
  exactly when `H⁰(X, 𝒪_X) = k`.

## References

* [Stacks Project, Tag 0E97](https://stacks.math.columbia.edu/tag/0E97)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Stacks.Curves

variable {X Y : Scheme.{u}}

/-- **An acyclic morphism does not change the cohomology of the structure sheaf**: for
`c : X ⟶ Y` with `𝒪_Y = c_*𝒪_X` and `Rᵐc_*𝒪_X = 0` for `m > 0`, and every `n`,
`Hⁿ(X, 𝒪_X) ≅ Hⁿ(Y, 𝒪_Y)`, the left side regarded as a `Γ(Y, ⊤)`-module along `c.appTop`. -/
def acyclicCohomologyObjIso (c : X ⟶ Y)
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (hR : ∀ m : ℕ, 0 < m → IsZero (((Scheme.Modules.pushforward c).rightDerived m).obj
      (SheafOfModules.unit X.ringCatSheaf))) (n : ℕ) :
    (ModuleCat.restrictScalars c.appTop.hom).obj
        (((Cohomology.AffineBase.moduleGlobalSections X).rightDerived n).obj
          (SheafOfModules.unit X.ringCatSheaf)) ≅
      ((Cohomology.AffineBase.moduleGlobalSections Y).rightDerived n).obj
        (SheafOfModules.unit Y.ringCatSheaf) :=
  letI : HasDerivedCategory.{u + 1} Y.Modules := HasDerivedCategory.standard _
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} Γ(Y, ⊤)) := HasDerivedCategory.standard _
  haveI : IsIso (structureSheafToPushforward c) := hO
  let R := ModuleCat.restrictScalars.{u} c.appTop.hom
  have _ : R.Additive := ⟨by intros; rfl⟩
  have _ : PreservesFiniteLimits R := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have _ : PreservesFiniteColimits R := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have _ : R.PreservesHomology := Functor.preservesHomologyOfExact R
  (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
        (Cohomology.AffineBase.moduleGlobalSections X) R
        (Scheme.Modules.pushforward c ⋙ Cohomology.AffineBase.moduleGlobalSections Y)
        (Cohomology.AffineBase.sectionsRestrictionIsoTop c) n).app
      (SheafOfModules.unit X.ringCatSheaf) ≪≫
    Stacks.AcyclicCollapse.objIso (Scheme.Modules.pushforward c)
      (Cohomology.AffineBase.moduleGlobalSections Y)
      (Stacks.Cohomology.ClosedImmersion.rightAcyclic_moduleGlobalSections_pushforward_injective c)
      hR n ≪≫
    (((Cohomology.AffineBase.moduleGlobalSections Y).rightDerived n).mapIso
      (asIso (structureSheafToPushforward c))).symm

/-- Precomposing `Γ(Spec k) ⟶ Γ(Y, ⊤)` with `c.appTop` gives the corresponding map for `f`. -/
private theorem appTop_comp_eq {k : Type u} [Field k] {f : X ⟶ Spec (.of k)}
    {g : Y ⟶ Spec (.of k)} (c : X ⟶ Y) (hcg : c ≫ g = f) :
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) ≫ c.appTop =
      (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop := by
  rw [Category.assoc, ← Scheme.Hom.comp_appTop, hcg]

/-- **An acyclic morphism over a field preserves the genus**: if `c : X ⟶ Y` has
`𝒪_Y = c_*𝒪_X` and `Rᵐc_*𝒪_X = 0` for `m > 0`, and `c ≫ g = f` over `k`, then
`genus g = genus f`. -/
theorem genus_eq_of_isIso_unitToPushforwardObjUnit {k : Type u} [Field k]
    {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)} (c : X ⟶ Y) (hcg : c ≫ g = f)
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (hR : ∀ m : ℕ, 0 < m → IsZero (((Scheme.Modules.pushforward c).rightDerived m).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    genus g = genus f := by
  have hgf := congrArg CommRingCat.Hom.hom (appTop_comp_eq c hcg).symm
  rw [CommRingCat.hom_comp] at hgf
  have e : structureSheafCohomology f 1 ≅ structureSheafCohomology g 1 :=
    structureSheafCohomologyIsoRestrict k f 1 ≪≫
      ModuleCat.restrictScalarsComp'App _ _ _ hgf _ ≪≫
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).mapIso
        (acyclicCohomologyObjIso c hO hR 1) ≪≫
      (structureSheafCohomologyIsoRestrict k g 1).symm
  rw [genus_eq_finrank_structureSheafCohomology, genus_eq_finrank_structureSheafCohomology]
  exact e.toLinearEquiv.finrank_eq.symm

/-- **Global functions along a morphism with `𝒪_Y = c_*𝒪_X`**: if `H⁰(X, 𝒪_X) = k` and
`c ≫ g = f`, then `H⁰(Y, 𝒪_Y) = k`, as `c.appTop` is an isomorphism. -/
theorem isIso_globalSections_of_isIso_unitToPushforwardObjUnit {k : Type u} [Field k]
    {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)} (c : X ⟶ Y) (hcg : c ≫ g = f)
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) := by
  have hc : IsIso c.appTop :=
    Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c hO ⊤
  have : IsIso (((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) ≫ c.appTop) := by
    rw [appTop_comp_eq c hcg]; infer_instance
  exact IsIso.of_isIso_comp_right _ c.appTop

/-- **Global functions of the source of a morphism with `𝒪_Y = c_*𝒪_X`**: if `H⁰(Y, 𝒪_Y) = k`
then `H⁰(X, 𝒪_X) = k`, as `c.appTop` is an isomorphism. -/
theorem isIso_globalSections_comp_of_isIso_unitToPushforwardObjUnit {k : Type u} [Field k]
    (c : X ⟶ Y) (g : Y ⟶ Spec (.of k))
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop)] :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (c ≫ g).appTop) := by
  have hc : IsIso c.appTop :=
    Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c hO ⊤
  rw [Scheme.Hom.comp_appTop, ← Category.assoc]
  infer_instance

end Stacks.Curves

end
