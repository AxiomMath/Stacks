module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.Duality
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.RingedSpaceTrace
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DualContractionCupProduct
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessUnconditional
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.TotalExtDimensionOverAField
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardBaseChangeCanonical
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.PerfectBoundedCoherent
public import StacksFrontier.Homology.DerivedCategory.Bridge.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Duality for perfect complexes on a proper scheme over a field

Let `X` be a proper scheme over a field `k`, with structure morphism `f : X ⟶ Spec k`, dualizing
complex `ω_X^• = a(𝒪_{Spec k})` of [Stacks, Tag 0FVV] and trace `t : H⁰(X, ω_X^•) ⟶ k` of
[Stacks, Tag 0FVW]. For a perfect object `E` of `D(𝒪_X)` the pairings

`Hⁱ(X, ω_X^• ⊗^𝐋 E^∨) × H⁻ⁱ(X, E) ⟶ k`, `(ξ, η) ↦ t((1 ⊗ ε)(ξ ∪ η))`,

are perfect for all `i` ([Stacks, Tag 0FVY]); here `∪` is the cup product of Cohomology,
Section 0FKU, and `ε : E^∨ ⊗^𝐋 E ⟶ 𝒪_X` is the evaluation of Cohomology, Example 0FPC.

## Main definitions

* `Stacks.Duality.traceStd` — the trace `t` of Tag 0FVW (`Stacks.Duality.traceOverField`), read on
  the `Γ(X, 𝒪_X)`-linear degree-zero cohomology at which the cup product is stated.
* `Stacks.Duality.dualityCupPairing` — the pairing, as a `k`-bilinear map.

## Main results

* `Stacks.Duality.bijective_traceStd_comp` — duality of [Stacks, Tag 0FVV] in degree zero, read at
  the standard model of `D(𝒪_X)`.
* `Stacks.Duality.isPerfPair_dualityCupPairing` — **[Stacks, Tag 0FVY]**.

## The proof

The source replaces `E` by a shift and identifies the pairing, through Cohomology, Lemma 0FVB,
with the pairing of Remark 0FVW. Here the shift is absorbed into a representing object: with
`Z₀ = L(A[-i])` the universal object of degree `i` (`A = Γ(X, 𝒪_X)`, `L` the left adjoint of
derived global sections from which the cup product is built) and `Y = Z₀ ⊗^𝐋 E`,
`Stacks.Cohomology.DerivedGlobalCupProduct.cupDualContraction_cupTestClassEquiv` writes the
pairing as `(ξ_β, η) ↦ t(H⁰(β)(z₀ ∪ η))` for `β : Y ⟶ ω_X^•`, where `β ↦ ξ_β` is a bijection
`Hom(Y, ω_X^•) ≃ Hⁱ(X, ω_X^• ⊗^𝐋 E^∨)` (the left duality of `E^∨`, Tag 0FPC, and the universal
property of `z₀`) and `η ↦ z₀ ∪ η` a bijection `H⁻ⁱ(X, E) ≃ H⁰(X, Y)`. Since `Y` is perfect it has
quasi-coherent cohomology, and duality in degree zero (part (5) of Tag 0FVV) makes
`β ↦ t ∘ H⁰(β)` a bijection onto `Hom_k(H⁰(X, Y), k)`. The finite dimensionality of `H⁻ⁱ(X, E)`
is that of `H⁰(X, Y)`, which is [Stacks, Tag 0D0B] for the bounded coherent `Y`
(`ProperSupportCoherent.moduleFinite_homologyZero_derivedGlobalSections_of_proper`).

## Implementation notes

The cup product of Section 0FKU, the derived dual and its evaluation, and the derived tensor
products exist at the standard model of `D(𝒪_X)`, in the ringed-space spelling of
`𝒪_X`-modules, and the cohomology groups are the `Γ(X, 𝒪_X)`-modules `cohomologyModule`; the
duality of Tag 0FVV and its trace exist at the locally small model and are `k`-linear. The two
are compared by `Stacks.Duality.sectionsComparison`, which is `Stacks.Duality.cohomologyBridge`
(file `RingedSpaceTrace`) in degree zero, read through the comparison of the two models of
`D(𝒪_X)` that is the identity on objects. The dualizing complex is the same object at both
models.

Standard model: uses `Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing`,
`Stacks.SheafOfModules.derivedDual` and `Stacks.SheafOfModules.derivedDualContraction`, which
exist only there.

## References

* [Stacks Project, Tag 0FVY](https://stacks.math.columbia.edu/tag/0FVY)
* [Stacks Project, Tag 0FVV](https://stacks.math.columbia.edu/tag/0FVV)
* [Stacks Project, Tag 0FVW](https://stacks.math.columbia.edu/tag/0FVW)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The dualizing complex `ω_X^• = a(𝒪_{Spec k})` of [Stacks, Tag 0FVV], as an object of the
locally small model of `D(𝒪_X)`. -/
abbrev dualizingComplexObjOverField : DerivedCategory X.Modules :=
  (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))).obj

/-- `H⁰(X, -) = H⁰ ∘ RΓ(X, -)` over `k`, at the locally small models. -/
abbrev globalSectionsZero : DerivedCategory X.Modules ⥤ ModuleCat.{u} k :=
  derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0

section Standard

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor
  Stacks.Topology.RingedSpaceSheafifyOpens.hasSheafifyOverOpen
  Stacks.Topology.RingedSpaceSheafifyOpens.wEqualsLocallyBijectiveOverOpen
attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  Stacks.SheafOfModules.Tensor.ringSheaf CategoryTheory.sheafCompose
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

open Stacks.Cohomology.DerivedGlobalCupProduct Stacks.Cohomology.GlobalKunneth

/-- The dualizing complex `ω_X^•` as an object of the standard model of `D(𝒪_X)`: the two models
have the same objects. -/
def dualizingComplexStd :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
  dualizingComplexObjOverField f

/-- **Degree-zero cohomology in the two spellings.** `Γ(X, 𝒪_X)`-linear `H⁰(X, -)` at the
standard model, with the scalars restricted to `k`, is `k`-linear `H⁰(X, -)` at the locally small
model, after the comparison of the two models of `D(𝒪_X)`. -/
def sectionsComparison :
    baseSections X.toRingedSpace ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) 0 ⋙
          ModuleCat.restrictScalars.{u} (globalRingHom f) ≅
      (StacksDraft.DerivedModel.schemeModulesComparison X).functor ⋙ globalSectionsZero f :=
  cohomologyBridge f 0 ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.schemeModulesComparisonFunctorIso X).symm
      (globalSectionsZero f)

/-- **The trace `t : H⁰(X, ω_X^•) ⟶ k` of [Stacks, Tag 0FVW]**, read on the `Γ(X, 𝒪_X)`-linear
degree-zero cohomology of `ω_X^•` at the standard model, with the scalars restricted to `k`: the
comparison `sectionsComparison` followed by `Stacks.Duality.traceOverField`. -/
def traceStd :
    (ModuleCat.restrictScalars.{u} (globalRingHom f)).obj
        (cohomologyModule (dualizingComplexStd f) 0) ⟶
      ModuleCat.of k k :=
  (sectionsComparison f).hom.app (dualizingComplexStd f) ≫ traceOverField f

/-- An object of the standard model of `D(𝒪_X)` with quasi-coherent cohomology sheaves has
quasi-coherent cohomology sheaves at the locally small model, after the comparison of the two
models. -/
theorem derivedCategoryB_schemeModulesComparison_obj
    (Y : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hY : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj Y).IsQuasicoherent) :
    @DerivedCategoryB.derivedCategoryB X.Modules _ _ (Scheme.Modules.hasDerivedCategory X)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((StacksDraft.DerivedModel.schemeModulesComparison X).functor.obj Y) := by
  have h := (StacksDraft.DerivedModel.derivedCategoryB_modelEquiv_functor_obj_iff
    (SheafOfModules.isQuasicoherent X.ringCatSheaf) (HasDerivedCategory.standard X.Modules)
    (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} X.Modules) Y).2 hY
  intro n
  exact ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    ((@DerivedCategory.homologyFunctor X.Modules _ _ (Scheme.Modules.hasDerivedCategory X) n).mapIso
      ((StacksDraft.DerivedModel.grothendieckModelEquivFunctorIso X.Modules).app Y).symm) (h n)

/-- **Duality of [Stacks, Tag 0FVV] in degree zero, at the standard model.** For `Y` in `D(𝒪_X)`
with quasi-coherent cohomology sheaves, a morphism `β : Y ⟶ ω_X^•` is determined by the linear form
`t ∘ H⁰(X, β)` on `H⁰(X, Y)`, and every linear form arises. -/
theorem bijective_traceStd_comp
    (Y : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hY : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj Y).IsQuasicoherent) :
    Function.Bijective (fun β : Y ⟶ dualizingComplexStd f ↦
      (ModuleCat.restrictScalars.{u} (globalRingHom f)).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) 0).map
            ((baseSections X.toRingedSpace).map β)) ≫ traceStd f) := by
  let L : @quasiCoherentDerivedCategory X (Scheme.Modules.hasDerivedCategory X) :=
    ⟨(StacksDraft.DerivedModel.schemeModulesComparison X).functor.obj Y,
      derivedCategoryB_schemeModulesComparison_obj Y hY⟩
  have h₃ : Function.Bijective (fun γ : (globalSectionsZero f).obj L.obj ⟶ ModuleCat.of k k ↦
      (sectionsComparison f).hom.app Y ≫ γ) :=
    ⟨fun _ _ e ↦ (Iso.cancel_iso_hom_left ((sectionsComparison f).app Y) _ _).1 e,
      fun γ ↦ ⟨(sectionsComparison f).inv.app Y ≫ γ, Iso.hom_inv_id_app_assoc _ _ _⟩⟩
  refine Eq.mpr (congrArg Function.Bijective (funext fun β ↦ ?_))
    (h₃.comp ((bijective_homologyFunctor_map_comp_traceOverField f L).comp
    ((StacksDraft.DerivedModel.schemeModulesComparison X).fullyFaithfulFunctor.map_bijective
      Y (dualizingComplexStd f))))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ traceOverField f) ((sectionsComparison f).hom.naturality β)).trans
      (Category.assoc _ _ _))

variable (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))

/-- **The pairing of [Stacks, Tag 0FVY]**

`Hⁱ(X, ω_X^• ⊗^𝐋 E^∨) × H⁻ⁱ(X, E) ⟶ k`, `(ξ, η) ↦ t((1 ⊗ ε)(ξ ∪ η))`,

as a `k`-bilinear map: `∪` is the cup product of Section 0FKU at the canonical global cup
product, `ε : E^∨ ⊗^𝐋 E ⟶ 𝒪_X` the evaluation of Stacks 0FPC, `t` the trace of [Stacks, Tag 0FVW]
(`traceStd`), and the cohomology groups are `Γ(X, 𝒪_X)`-modules with the scalars restricted to
`k`. -/
def dualityCupPairing (i : ℤ) :
    (ModuleCat.restrictScalars.{u} (globalRingHom f)).obj
        (cohomologyModule (tensorDual X.toRingedSpace (dualizingComplexStd f) E) i) →ₗ[k]
      (ModuleCat.restrictScalars.{u} (globalRingHom f)).obj (cohomologyModule E (-i)) →ₗ[k] k :=
  LinearMap.mk₂ k
    (fun ξ η ↦ (traceStd f).hom
      ((cupDualContraction X.toRingedSpace (dualizingComplexStd f) E i).hom
        ((ξ : cohomologyModule (tensorDual X.toRingedSpace (dualizingComplexStd f) E) i) ⊗ₜ
          (η : cohomologyModule E (-i)))))
    (fun ξ ξ' η ↦ by
      change (traceStd f).hom ((cupDualContraction X.toRingedSpace (dualizingComplexStd f) E i).hom
        ((@id (cohomologyModule (tensorDual X.toRingedSpace (dualizingComplexStd f) E) i) ξ +
          @id (cohomologyModule (tensorDual X.toRingedSpace (dualizingComplexStd f) E) i) ξ') ⊗ₜ
            @id (cohomologyModule E (-i)) η)) = _
      rw [TensorProduct.add_tmul, map_add]
      exact (traceStd f).hom.map_add _ _)
    (fun c ξ η ↦ by
      change (traceStd f).hom ((cupDualContraction X.toRingedSpace (dualizingComplexStd f) E i).hom
        ((globalRingHom f c •
          @id (cohomologyModule (tensorDual X.toRingedSpace (dualizingComplexStd f) E) i) ξ) ⊗ₜ
          @id (cohomologyModule E (-i)) η)) = _
      rw [← TensorProduct.smul_tmul', LinearMap.map_smul]
      exact (traceStd f).hom.map_smul c _)
    (fun ξ η η' ↦ by
      change (traceStd f).hom ((cupDualContraction X.toRingedSpace (dualizingComplexStd f) E i).hom
        (@id (cohomologyModule (tensorDual X.toRingedSpace (dualizingComplexStd f) E) i) ξ ⊗ₜ
          (@id (cohomologyModule E (-i)) η + @id (cohomologyModule E (-i)) η'))) = _
      rw [TensorProduct.tmul_add, map_add]
      exact (traceStd f).hom.map_add _ _)
    (fun c ξ η ↦ by
      change (traceStd f).hom ((cupDualContraction X.toRingedSpace (dualizingComplexStd f) E i).hom
        (@id (cohomologyModule (tensorDual X.toRingedSpace (dualizingComplexStd f) E) i) ξ ⊗ₜ
          (globalRingHom f c • @id (cohomologyModule E (-i)) η))) = _
      rw [TensorProduct.tmul_smul, LinearMap.map_smul]
      exact (traceStd f).hom.map_smul c _)

/-- The pairing at the class attached to `β : Y ⟶ ω_X^•` is the linear form `t ∘ H⁰(β)`, read
through the cup product with the universal class. -/
theorem dualityCupPairing_cupTestClassEquiv
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) (i : ℤ)
    (β : cupTestObject X.toRingedSpace E i ⟶ dualizingComplexStd f)
    (η : (ModuleCat.restrictScalars.{u} (globalRingHom f)).obj (cohomologyModule E (-i))) :
    dualityCupPairing f E i (cupTestClassEquiv X.toRingedSpace (dualizingComplexStd f) E hE i β) η =
      ((ModuleCat.restrictScalars.{u} (globalRingHom f)).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) 0).map
            ((baseSections X.toRingedSpace).map β)) ≫ traceStd f).hom
        (cupUniversalEquiv X.toRingedSpace E i η) :=
  congrArg (traceStd f).hom
    (cupDualContraction_cupTestClassEquiv X.toRingedSpace (dualizingComplexStd f) E hE i β η)

/-- `cupUniversalEquiv` with the scalars restricted to `k`. -/
def cupUniversalEquivOverField (i : ℤ) :
    (ModuleCat.restrictScalars.{u} (globalRingHom f)).obj (cohomologyModule E (-i)) ≃ₗ[k]
      (ModuleCat.restrictScalars.{u} (globalRingHom f)).obj
        (cohomologyModule (cupTestObject X.toRingedSpace E i) 0) :=
  { (cupUniversalEquiv X.toRingedSpace E i).toAddEquiv with
    map_smul' := fun c η ↦ (cupUniversalEquiv X.toRingedSpace E i).map_smul (globalRingHom f c) η }

/-- **[Stacks, Tag 0FVY]**, the left map: `Hⁱ(X, ω_X^• ⊗^𝐋 E^∨) ⟶ Hom_k(H⁻ⁱ(X, E), k)` is a
bijection. -/
theorem bijective_dualityCupPairing
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) (i : ℤ) :
    Function.Bijective (dualityCupPairing f E i) := by
  let Y := cupTestObject X.toRingedSpace E i
  let Γ := cupTestClassEquiv X.toRingedSpace (dualizingComplexStd f) E hE i
  let m := cupUniversalEquivOverField f E i
  have key : ⇑(dualityCupPairing f E i) =
      (fun φ ↦ φ ∘ₗ m.toLinearMap) ∘ (fun β ↦ ((ModuleCat.restrictScalars.{u} (globalRingHom f)).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) 0).map
            ((baseSections X.toRingedSpace).map β)) ≫ traceStd f).hom) ∘ Γ.symm := by
    funext ξ
    obtain ⟨β, rfl⟩ := Γ.surjective ξ
    ext η
    simp only [Function.comp_apply, Equiv.symm_apply_apply, LinearMap.coe_comp,
      LinearEquiv.coe_coe]
    exact dualityCupPairing_cupTestClassEquiv f E hE i β η
  rw [key]
  refine Function.Bijective.comp ?_ (Function.Bijective.comp ?_ Γ.symm.bijective)
  · exact ⟨fun φ ψ h ↦ by
      ext x
      simpa using LinearMap.congr_fun h (m.symm x),
      fun φ ↦ ⟨φ ∘ₗ m.symm.toLinearMap, by ext; simp⟩⟩
  · exact ModuleCat.homEquiv.bijective.comp (bijective_traceStd_comp f Y
      (AlgebraicGeometry.ProperFlatBaseChange.isQuasicoherent_homology_of_isPerfect Y
        (isPerfect_cupTestObject X.toRingedSpace E hE i)))

open Stacks.AlgebraicGeometry.ProperSupportCoherent in
/-- **`H⁻ⁱ(X, E)` is a finite-dimensional `k`-vector space**, for `E` perfect: it is `H⁰(X, Y)`
for the perfect, hence bounded coherent, `Y = Z₀ ⊗^𝐋 E`, and the cohomology of a bounded below
coherent complex on a scheme proper over a field is finite dimensional ([Stacks, Tag 0D0B]). -/
theorem finiteDimensional_cohomologyModule_of_isPerfect
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) (i : ℤ) :
    FiniteDimensional k
      ((ModuleCat.restrictScalars.{u} (globalRingHom f)).obj (cohomologyModule E (-i))) := by
  let Y := cupTestObject X.toRingedSpace E i
  have : IsProper (Over.mk f).hom := ‹IsProper f›
  have : IsNoetherian X := isNoetherian_of_isProper_over_field (Over.mk f)
  have hb := Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect X Y
    (isPerfect_cupTestObject X.toRingedSpace E hE i)
  have hfin := moduleFinite_homologyZero_derivedGlobalSections_of_proper (Over.mk f) Y
    ⟨hb.1.1, hb.2⟩
  have e : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
        ((derivedGlobalSectionsOver (Over.mk f).hom).obj Y) ≅
      (ModuleCat.restrictScalars.{u} (globalRingHom f)).obj
        (cohomologyModule (cupTestObject X.toRingedSpace E i) 0) :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).mapIso
        ((derivedGlobalSectionsOverStandardIso f).app Y) ≪≫
      (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (ModuleCat.restrictScalars.{u} (globalRingHom f)) 0).app
          ((baseSections X.toRingedSpace).obj Y)
  exact Module.Finite.equiv (e.toLinearEquiv ≪≫ₗ (cupUniversalEquivOverField f E i).symm)

/-- **[Stacks, Tag 0FVY].** Let `X` be a proper scheme over a field `k`, with structure morphism
`f : X ⟶ Spec k`, let `ω_X^•` be its dualizing complex of [Stacks, Tag 0FVV] and
`t : H⁰(X, ω_X^•) ⟶ k` the trace of [Stacks, Tag 0FVW]. Let `E ∈ D(𝒪_X)` be perfect. Then for
every `i` the pairing

`Hⁱ(X, ω_X^• ⊗^𝐋 E^∨) × H⁻ⁱ(X, E) ⟶ k`, `(ξ, η) ↦ t((1 ⊗ ε)(ξ ∪ η))`

is perfect: both spaces are finite-dimensional `k`-vector spaces and the pairing is a perfect
pairing (`LinearMap.IsPerfPair`: each side is identified with the `k`-linear dual of the other).
Here `∪` is the cup product of Cohomology, Section 0FKU (`cupPairing` at the canonical global cup
product), `E^∨ = R𝓗om(E, 𝒪_X)` and `ε : E^∨ ⊗^𝐋 E ⟶ 𝒪_X` is the evaluation of Cohomology,
Example 0FPC, and `1 ⊗ ε : (ω_X^• ⊗^𝐋 E^∨) ⊗^𝐋 E ⟶ ω_X^•` is followed by the unit constraint
(`dualityCupPairing`). The cohomology groups are the `Γ(X, 𝒪_X)`-modules of hypercohomology with
the scalars restricted along `k ⟶ Γ(X, 𝒪_X)`, and `t` is `Stacks.Duality.traceOverField` read on
them (`traceStd`). -/
@[stacks 0FVY, sga "4½ Fonctions_L 3.7" "special case"]
theorem isPerfPair_dualityCupPairing
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) (i : ℤ) :
    FiniteDimensional k ((ModuleCat.restrictScalars.{u} (globalRingHom f)).obj
        (cohomologyModule (tensorDual X.toRingedSpace (dualizingComplexStd f) E) i)) ∧
      FiniteDimensional k
        ((ModuleCat.restrictScalars.{u} (globalRingHom f)).obj (cohomologyModule E (-i))) ∧
      (dualityCupPairing f E i).IsPerfPair := by
  have := finiteDimensional_cohomologyModule_of_isPerfect f E hE i
  have hbij := bijective_dualityCupPairing f E hE i
  exact ⟨Module.Finite.equiv (LinearEquiv.ofBijective _ hbij).symm, inferInstance,
    .of_bijective _ hbij⟩

end Standard

end Stacks.Duality

end
