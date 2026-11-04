module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.ContractionTarget
public import StacksFrontier.AlgebraicGeometry.Curves.DirectImage.RationalTailCohomologyIso

/-!
# Contracting a rational bridge changes neither the cohomology of the structure sheaf nor the genus

Let `k` be a field, let `X` be a proper scheme over `k` of dimension one with `H⁰(X, 𝒪_X) = k`
and at-worst-nodal singularities, let `C ⊆ X` be a rational bridge (Tag 0E3M) and let
`c : X ⟶ Y` be a contraction of `C`. Then for every `n`

`H ⁿ(X, 𝒪_X) ≅ H ⁿ(Y, 𝒪_Y)`,

the two sides being modules over the different rings `Γ(X, ⊤)` and `Γ(Y, ⊤)`, so the comparison
is stated after restriction of scalars along `c.appTop : Γ(Y, ⊤) ⟶ Γ(X, ⊤)`. In degree one this
is the genus clause of [Stacks, Tag 0E3M].

## Main results

* `Stacks.Curves.bridgeContractionCohomologyObjIso` — the cohomology comparison in every degree.
* `Stacks.Curves.genus_eq_of_isContractionOfRationalBridge` — the target of a contraction has the
  genus of `X`.
* `Stacks.Curves.exists_isProper_structureMorphism_and_genus_eq_contraction_bridge` — the target
  of a contraction is a proper scheme over `k` of dimension one with `H⁰(Y, 𝒪_Y) = k` and the
  genus of `X`.

## References

* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.Curves

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- **Contracting a rational bridge does not change the cohomology of the structure sheaf**: for
a contraction `c : X ⟶ Y` of a rational bridge of a proper one-dimensional nodal curve over `k`
with only constant global functions, and every `n`,

`H ⁿ(X, 𝒪_X) ≅ H ⁿ(Y, 𝒪_Y)`,

the left side regarded as a `Γ(Y, ⊤)`-module along `c.appTop`. -/
def bridgeContractionCohomologyObjIso
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) (n : ℕ) :
    (ModuleCat.restrictScalars c.appTop.hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (SheafOfModules.unit X.ringCatSheaf)) ≅
      ((moduleGlobalSections Y).rightDerived n).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  letI : HasDerivedCategory.{u + 1} Y.Modules := HasDerivedCategory.standard _
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} Γ(Y, ⊤)) := HasDerivedCategory.standard _
  haveI : IsIso (structureSheafToPushforward c) :=
    isIso_structureSheafToPushforward_contraction_bridge hdim hnodal hc
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
      (fun m hm => rightAcyclic_pushforward_ambientStructureSheaf_bridge hdim hnodal hc m hm) n ≪≫
    (((moduleGlobalSections Y).rightDerived n).mapIso
      (asIso (structureSheafToPushforward c))).symm

/-- **Contracting a rational bridge does not change the genus.** The target of a contraction,
with any structure morphism over `k` through which the structure morphism of `X` factors, has
the genus of `X`. -/
theorem genus_eq_of_isContractionOfRationalBridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) {g : Y ⟶ Spec (.of k)}
    (hcg : c ≫ g = X ↘ Spec (.of k)) :
    genus g = genus (X ↘ Spec (.of k)) := by
  have hmap : ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) ≫ c.appTop =
      (Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop := by
    rw [Category.assoc, ← Scheme.Hom.comp_appTop, hcg]
  have hgf := congrArg CommRingCat.Hom.hom hmap.symm
  rw [CommRingCat.hom_comp] at hgf
  have e : structureSheafCohomology (X ↘ Spec (.of k)) 1 ≅ structureSheafCohomology g 1 :=
    structureSheafCohomologyIsoRestrict k (X ↘ Spec (.of k)) 1 ≪≫
      ModuleCat.restrictScalarsComp'App _ _ _ hgf _ ≪≫
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).mapIso
        (bridgeContractionCohomologyObjIso hdim hnodal hc 1) ≪≫
      (structureSheafCohomologyIsoRestrict k g 1).symm
  rw [genus_eq_finrank_structureSheafCohomology, genus_eq_finrank_structureSheafCohomology]
  exact e.toLinearEquiv.finrank_eq.symm

/-- **The target of a contraction of a rational bridge is a proper scheme over `k` of dimension
one with `H⁰(Y, 𝒪_Y) = k` and the genus of `X`.** That is, there is a morphism
`g : Y ⟶ Spec k` with `c ≫ g` the structure morphism of `X` which has these properties. -/
@[stacks 0E3M "Y is proper over k of dimension one with H⁰(Y, 𝒪_Y) = k and the genus of X"]
theorem exists_isProper_structureMorphism_and_genus_eq_contraction_bridge
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalBridge k X C)
    {Y : Scheme.{u}} (c : X ⟶ Y) (hc : IsContractionOfRationalBridge hC c) :
    ∃ g : Y ⟶ Spec (.of k), c ≫ g = X ↘ Spec (.of k) ∧ IsProper g ∧
      topologicalKrullDim Y = 1 ∧ IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) ∧
      genus g = genus (X ↘ Spec (.of k)) := by
  obtain ⟨g, hcg, hproper, hdimY, hglobal⟩ :=
    exists_isProper_structureMorphism_contraction_bridge hdim hnodal hc
  exact ⟨g, hcg, hproper, hdimY, hglobal,
    genus_eq_of_isContractionOfRationalBridge hdim hnodal hc hcg⟩

end Stacks.Curves

end
