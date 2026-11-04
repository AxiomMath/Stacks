module

public import StacksFrontier.AlgebraicGeometry.Cohomology.ExtFromStructureSheaf
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexLowerVanishing
public import StacksFrontier.AlgebraicGeometry.Duality.CohomologyHypercohomology
public import StacksFrontier.AlgebraicGeometry.Duality.SingleQuasiCoherent
import StacksCore.Tactic.StacksAttribute

/-!
# Serre duality for the dualizing sheaf of a proper curve

Let `k` be a field and `f : X ⟶ Spec k` a proper morphism with `X` of topological Krull dimension
at most one — the hypotheses of Situation [Stacks, Tag 0B5D]. The dualizing *complex* of
[Stacks, Tag 0BS2] is `ω_X^• = f^×(𝒪_{Spec k})` and the dualizing *sheaf* is its degree `-1`
cohomology sheaf

  `ω_X = H^{-1}(ω_X^•)`.

For a quasi-coherent `ℱ` with no global sections, `Ext^1_{𝒪_X}(ℱ, ω_X) = 0`.

## Main definitions

* `Stacks.Duality.dualizingModuleOverField`: the cohomology sheaf `H^{-m}(ω_X^•)`.
* `Stacks.Duality.dualizingSheafOverField`: the dualizing sheaf `ω_X = H^{-1}(ω_X^•)`.
* `Stacks.Duality.truncLEIsoSingleHomology`: `τ^{≤ n}(ω_X^•) ≅ H^n(ω_X^•)[-n]` for a dualizing
  complex with no cohomology below degree `n`, and
  `Stacks.Duality.singleShiftIsoTruncLEHomology` the same read with the shift on the left.
* `Stacks.Duality.truncLEIsoSingleDualizingSheaf`: `τ^{≤ -1}(ω_X^•) ≅ ω_X[1]`.

## Main results

* `Stacks.Duality.subsingleton_zExt_one_dualizingSheafOverField`: `Ext^1(ℱ, ω_X) = 0` for a
  quasi-coherent `ℱ` with `H⁰(X, ℱ) = 0`.
* `Stacks.Duality.eq_zero_of_comp_truncLEι_app_eq_zero`: a morphism into `τ^{≤ n}K` which the
  canonical map `τ^{≤ n}K ⟶ K` kills is zero, as soon as its source lies in `D^{≤ n+1}`.
* `Stacks.Duality.subsingleton_cohomologyOverField_of_subsingleton_zExt`: a vanishing
  `Ext^1(𝒪_X, ℱ)` is a vanishing `H^1(X, ℱ)`.

## Implementation notes

The objects of `AlgebraicGeometry.quasiCoherentDerivedCategory X` must be named with their
`X.Modules` ascription: a `_` in their position is read at `SheafOfModules X.ringCatSheaf`, where
the `HasDerivedCategory` instance is not found.

Everything up to `subsingleton_zExt_one_dualizingSheafOverField` is at the locally small
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, the model instance search picks for
`X.Modules`; `subsingleton_cohomologyOverField_of_subsingleton_zExt` crosses to
`CategoryTheory.HasDerivedCategory.standard`, where the comparison with sheaf cohomology is stated.

## References

* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS3](https://stacks.math.columbia.edu/tag/0BS3)
* [Stacks Project, Tag 0BS4](https://stacks.math.columbia.edu/tag/0BS4)
* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  CategoryTheory.Triangulated

universe u

namespace Stacks.Duality

/-! ### Morphisms into a truncation from above -/

/-- **A morphism into `τ^{≤ n}X` which the canonical map `τ^{≤ n}X ⟶ X` kills is zero**, as soon
as its source lies in `D^{≤ n+1}`. -/
theorem eq_zero_of_comp_truncLEι_app_eq_zero {C : Type*} [Category C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (t : TStructure C) {A X : C} (n m : ℤ) (hm : n + 1 = m) [t.IsLE A m]
    (g : A ⟶ (t.truncLE n).obj X) (hg : g ≫ (t.truncLEι n).app X = 0) : g = 0 := by
  subst hm
  obtain ⟨g', hg'⟩ := Pretriangulated.Triangle.coyoneda_exact₂ _
    (Pretriangulated.inv_rot_of_distTriang _ (t.triangleLEGE_distinguished n (n + 1) rfl X)) g hg
  rw [hg', t.zero_of_isLE_of_isGE g' (n + 1) (n + 2) (by omega) inferInstance
    (t.isGE_shift ((t.truncGE (n + 1)).obj X) (n + 1) (-1) (n + 2) (by ring))]
  exact Limits.zero_comp

/-! ### The dualizing sheaf -/

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- **The cohomology sheaf `H^{-m}(f^×(𝒪_{Spec k}))` of the dualizing complex.** For
`m = dim(X)` this is the *dualizing module* `ω_X` of [Stacks, Tag 0AWI] in the case where the
base is a field, and for `m = 1` it is the dualizing sheaf of a curve,
`Stacks.Duality.dualizingSheafOverField`. -/
def dualizingModuleOverField (m : ℤ) : X.Modules :=
  (DerivedCategory.homologyFunctor X.Modules (-m)).obj (dualizingComplexOverField f).obj

/-- **The dualizing sheaf `ω_X = H^{-1}(f^×(𝒪_{Spec k}))`** of [Stacks, Tag 0BS2]: the degree
`-1` cohomology sheaf of the dualizing complex `Stacks.Duality.dualizingComplexOverField`. -/
def dualizingSheafOverField : X.Modules :=
  dualizingModuleOverField f 1

/-- In degree `-dim(X)`, `dualizingModuleOverField` is the base's relative dualizing module
`Stacks.Duality.relativeDualizingModule` of [Stacks, Tag 0AWI] for `ω_{Spec k}^• = 𝒪_{Spec k}[0]`.
-/
theorem dualizingModuleOverField_dim_eq_relativeDualizingModule :
    dualizingModuleOverField f (ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ) =
      relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))) :=
  rfl

/-- **For a curve, `ω_X` is the relative dualizing module of [Stacks, Tag 0AWI]**: when `X` has
dimension one, the dualizing sheaf `H^{-1}(ω_X^•)` of [Stacks, Tag 0BS2] is
`Stacks.Duality.relativeDualizingModule` over `𝒪_{Spec k}[0]`. -/
theorem dualizingSheafOverField_eq_relativeDualizingModule (hX : topologicalKrullDim X = 1) :
    dualizingSheafOverField f =
      relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))) := by
  rw [← dualizingModuleOverField_dim_eq_relativeDualizingModule, hX]
  rfl

/-- **`τ^{≤ n}(ω_X^•) ≅ H^n(ω_X^•)[-n]`**: if the dualizing complex has no cohomology below
degree `n`, its truncation below degree `n+1` is the cohomology sheaf `H^n(ω_X^•)` placed in
degree `n`. -/
def truncLEIsoSingleHomology (n : ℤ) (hge : (dualizingComplexOverField f).obj.IsGE n) :
    (DerivedCategory.TStructure.t.truncLE n).obj (dualizingComplexOverField f).obj ≅
      (DerivedCategory.singleFunctor X.Modules n).obj
        ((DerivedCategory.homologyFunctor X.Modules n).obj
          (dualizingComplexOverField f).obj) := by
  have hY := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    ((DerivedCategory.TStructure.t.truncLE n).obj (dualizingComplexOverField f).obj) n
  set Y := hY.choose with hYdef
  have e := hY.choose_spec.some
  have hiso : IsIso ((DerivedCategory.homologyFunctor X.Modules n).map
      ((DerivedCategory.TStructure.t.truncLEι n).app (dualizingComplexOverField f).obj)) :=
    Stacks.DerivedTruncation.isIso_homologyMap_truncLEι
      (dualizingComplexOverField f).obj n n le_rfl
  refine e ≪≫ (DerivedCategory.singleFunctor X.Modules n).mapIso
    (((DerivedCategory.homologyFunctor X.Modules n).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules n).app Y).symm ≪≫
      @asIso _ _ _ _ _ hiso)

/-- **`H^{-m}(ω_X^•)[0]⟦m⟧ ≅ τ^{≤ -m}(ω_X^•)`**, the isomorphism of
`Stacks.Duality.truncLEIsoSingleHomology` read with the shift on the left. -/
def singleShiftIsoTruncLEHomology (m : ℤ)
    (hge : (dualizingComplexOverField f).obj.IsGE (-m)) :
    ((DerivedCategory.singleFunctor X.Modules 0).obj (dualizingModuleOverField f m))⟦m⟧ ≅
      (DerivedCategory.TStructure.t.truncLE (-m)).obj (dualizingComplexOverField f).obj :=
  ((DerivedCategory.singleFunctors X.Modules).shiftIso m (-m) 0 (by ring)).app
      (dualizingModuleOverField f m) ≪≫
    (truncLEIsoSingleHomology f (-m) hge).symm

/-- **`τ^{≤ -1}(ω_X^•) ≅ ω_X[1]`**: the truncation of the dualizing complex below degree zero is
the dualizing sheaf placed in degree `-1`. Compare [Stacks, Tag 0BS3], which identifies `ω_X^•`
itself with `ω_X[1]` under the additional hypothesis that `H^0(ω_X^•)` vanishes. -/
def truncLEIsoSingleDualizingSheaf (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    (DerivedCategory.TStructure.t.truncLE (-1)).obj (dualizingComplexOverField f).obj ≅
      (DerivedCategory.singleFunctor X.Modules (-1)).obj (dualizingSheafOverField f) :=
  truncLEIsoSingleHomology f (-1) (isGE_dualizingComplexOverField f hdim)

/-- **`ω_X[0]⟦1⟧ ≅ τ^{≤ -1}(ω_X^•)`**, the isomorphism of `truncLEIsoSingleDualizingSheaf` read
with the shift on the left. -/
def singleShiftOneIsoTruncLE (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    ((DerivedCategory.singleFunctor X.Modules 0).obj (dualizingSheafOverField f))⟦(1 : ℤ)⟧ ≅
      (DerivedCategory.TStructure.t.truncLE (-1)).obj (dualizingComplexOverField f).obj :=
  singleShiftIsoTruncLEHomology f 1 (isGE_dualizingComplexOverField f hdim)

/-! ### `Ext^1(ℱ, ω_X) = 0` for a module with no global sections -/

/-- **A morphism `ℱ[0] ⟶ ω_X^•` out of a quasi-coherent module with no global sections is
zero.** -/
theorem eq_zero_of_isZero_derivedCohomology (F : X.Modules) (hFq : F.IsQuasicoherent)
    (hH : IsZero (derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) 0))
    (g : (DerivedCategory.singleFunctor X.Modules 0).obj F ⟶
      (dualizingComplexOverField f).obj) : g = 0 :=
  (dualityAddEquivZero f (singleQuasiCoherent F hFq 0)).injective
    (Eq.trans (hH.eq_of_src _ _)
      (map_zero (dualityAddEquivZero f (singleQuasiCoherent F hFq 0))).symm)

/-- **`Ext^1_{𝒪_X}(ℱ, ω_X) = 0` for a quasi-coherent `ℱ` with no global sections**, on a proper
`X` of dimension at most one over a field ([Stacks, Tag 0BS4] with the dualizing sheaf of
[Stacks, Tag 0BS2]). The hypothesis is the vanishing of the sheaf cohomology
`AlgebraicGeometry.cohomologyOverField` in degree zero. -/
theorem subsingleton_zExt_one_dualizingSheafOverField
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) (F : X.Modules) (hFq : F.IsQuasicoherent)
    (hH : IsZero (cohomologyOverField k f F 0)) :
    Subsingleton (Abelian.zExt F (dualizingSheafOverField f) 1) := by
  refine subsingleton_of_forall_eq 0 fun g => (cancel_mono (singleShiftOneIsoTruncLE f hdim).hom).mp
    ((eq_zero_of_comp_truncLEι_app_eq_zero DerivedCategory.TStructure.t (-1) 0 (by ring) _
      (eq_zero_of_isZero_derivedCohomology f F hFq
        (IsZero.of_iso hH (cohomologyOverFieldIsoDerivedCohomologyOverField k f F 0).symm) _)).trans
      Limits.zero_comp.symm)

/-- **`H⁰(X, ℱ) = 0` when `ℱ` has no global sections.** -/
theorem isZero_cohomologyOverField_zero_of_subsingleton {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules) (h : Subsingleton Γ(F, ⊤)) :
    IsZero (cohomologyOverField k f F 0) :=
  let : Subsingleton ((restrictScalarsOverBase k f).obj
      ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj F)) := h
  IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) (cohomologyOverFieldZeroLinearIso k f F)

/-- **`Ext^1_{𝒪_X}(ℱ, ω_X) = 0` for a quasi-coherent `ℱ` with no global sections**, with the
hypothesis read directly on the module `Γ(ℱ, X)` of global sections. -/
theorem subsingleton_zExt_one_dualizingSheafOverField_of_subsingleton
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) (F : X.Modules) (hFq : F.IsQuasicoherent)
    (h : Subsingleton Γ(F, ⊤)) :
    Subsingleton (Abelian.zExt F (dualizingSheafOverField f) 1) :=
  subsingleton_zExt_one_dualizingSheafOverField f hdim F hFq
    (isZero_cohomologyOverField_zero_of_subsingleton f F h)

/-! ### From `Ext^1(𝒪_X, ℱ)` to `H^1(X, ℱ)` -/

/-- **A vanishing `Ext^1_{𝒪_X}(𝒪_X, ℱ)` is a vanishing `H^1(X, ℱ)`.** The morphism group
`Hom_{D(𝒪_X)}(𝒪_X[0], ℱ[0]⟦n⟧)` is the sheaf cohomology `H^n(X, ℱ)` by
`AlgebraicGeometry.derivedHomStructureSheafEquivCohomologyOverField`.

The hypothesis is at the model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` that instance
search picks, the comparison with sheaf cohomology at `CategoryTheory.HasDerivedCategory.standard`.
-/
theorem subsingleton_cohomologyOverField_of_subsingleton_zExt (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules) (n : ℕ)
    (h : Subsingleton (Abelian.zExt (C := X.Modules)
      (_root_.SheafOfModules.unit X.ringCatSheaf) F (n : ℤ))) :
    Subsingleton (cohomologyOverField k f F n) := by
  let : HasExt X.Modules := CategoryTheory.HasExt.standard _
  have hE : Subsingleton (Abelian.Ext (C := X.Modules)
      (_root_.SheafOfModules.unit X.ringCatSheaf) F n) :=
    (Equiv.subsingleton_congr Abelian.Ext.homEquiv).mpr h
  let := HasDerivedCategory.standard X.Modules
  have h' : Subsingleton (Abelian.zExt (C := X.Modules)
      (_root_.SheafOfModules.unit X.ringCatSheaf) F (n : ℤ)) :=
    (Equiv.subsingleton_congr Abelian.Ext.homEquiv).mp hE
  exact (Equiv.subsingleton_congr
    (derivedHomStructureSheafEquivCohomologyOverField k f F n).toEquiv).mp h'

end Stacks.Duality

end
