module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRhamPairFunctoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FormsRestrictionLocalizes
public import StacksFrontier.RingTheory.Localization.TensorComparison

/-!
# Localization of the de Rham terms over divided power rings with zero ideal

Let `A` be a ring and `f : B → C` a morphism of `A`-algebras between divided power rings whose
divided power ideals are zero, exhibiting `C` as the localization of `B` away from `s`.  Then the
module `Ω_{B/A, 0}` of divided power differentials is the module of Kähler differentials
`Ω_{B/A}` (the divided power relations are trivial), and for an `f`-semilinear map `μ : M → N`
which is a localization away from `s`, the map of de Rham terms

`M ⊗_B Ω^p_{B/A, 0} ⟶ N ⊗_C Ω^p_{C/A, 0}`,  `m ⊗ ω ↦ μ m ⊗ Ω_f(ω)`,

is a localization away from `s` as well (`Crystalline.DeRhamPair.isLocalizedModule_tensorMap`):
Kähler differentials, exterior powers and tensor products of localizations are localizations.

## Main results

* `Crystalline.DeRhamPair.dividedPowerDifferentialRelations_eq_bot` — over a zero divided power
  ideal the divided power relations vanish.
* `Crystalline.DeRhamPair.isLocalizedModule_oneFormsMap` — the map of divided power
  differentials along a localization is a localization.
* `Crystalline.DeRhamPair.isLocalizedModule_tensorMap` — the map of de Rham terms is.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Crystalline.DeRhamPair

variable {A : Type u} [CommRing A] {B C : DividedPowerRing.{u}} [Algebra A B] [Algebra A C]

/-- **Over a zero divided power ideal the divided power relations vanish**: the divided powers
of `0` in positive degree are `0`. -/
theorem dividedPowerDifferentialRelations_eq_bot (hB : B.ideal = ⊥) :
    dividedPowerDifferentialRelations (A := A) B.dividedPowers = ⊥ := by
  rw [dividedPowerDifferentialRelations, Submodule.span_eq_bot]
  rintro _ ⟨⟨x, n⟩, rfl⟩
  have hx : (x : (B : Type u)) = 0 := (Ideal.mem_bot).1 (hB ▸ x.2)
  change KaehlerDifferential.D A (B : Type u) (B.dividedPowers.dpow (n + 1) x) -
    B.dividedPowers.dpow n x • KaehlerDifferential.D A (B : Type u) x = 0
  rw [hx, DividedPowers.dpow_eval_zero _ n.succ_ne_zero, map_zero, smul_zero, sub_zero]

variable (f : (B : Type u) →ₐ[A] C)
  (hf : DividedPowers.IsDPMorphism B.dividedPowers C.dividedPowers f.toRingHom)

/-- A module over `C`, read over `B` through `f`. -/
@[instance_reducible]
def compHomModule (N : Type*) [AddCommGroup N] [Module (C : Type u) N] :
    Module (B : Type u) N :=
  Module.compHom N f.toRingHom

/-- An `f`-semilinear map, read as a `B`-linear map into its target read over `B`. -/
def toLinear {M N : Type*} [AddCommGroup M] [Module (B : Type u) M] [AddCommGroup N]
    [Module (C : Type u) N] (μ : M →+ N) (hμ : ∀ (b : (B : Type u)) m, μ (b • m) = f b • μ m) :
    letI := compHomModule f N
    M →ₗ[(B : Type u)] N :=
  letI := compHomModule f N
  { toFun := μ
    map_add' := map_add μ
    map_smul' := hμ }

/-- `toLinear` is the underlying map. -/
@[simp]
theorem toLinear_apply {M N : Type*} [AddCommGroup M] [Module (B : Type u) M] [AddCommGroup N]
    [Module (C : Type u) N] (μ : M →+ N) (hμ : ∀ (b : (B : Type u)) m, μ (b • m) = f b • μ m)
    (m : M) : toLinear f μ hμ m = μ m :=
  rfl

/-- `f` exhibits `C` as a `B`-algebra; the scalar towers this gives. -/
@[instance_reducible]
def algebraOf : Algebra (B : Type u) C :=
  f.toRingHom.toAlgebra

section Localization

variable (hB : B.ideal = ⊥) (hC : C.ideal = ⊥) (s : (B : Type u))
  (hloc : letI := algebraOf f; IsLocalization.Away s C)

/-- The map of divided power differentials, as a `B`-linear map. -/
def oneFormsLinear :
    letI := algebraOf f
    dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[(B : Type u)]
      dividedPowerDifferentials (A := A) C.dividedPowers :=
  letI := algebraOf f
  { toFun := oneFormsMap f hf
    map_add' := map_add _
    map_smul' := fun b ω ↦ ((oneFormsMap f hf).map_smulₛₗ b ω).trans
      (algebraMap_smul (C : Type u) b (oneFormsMap f hf ω)) }

/-- The map of divided power differential forms, as a `B`-linear map. -/
def formsLinear (p : ℕ) :
    letI := algebraOf f
    dividedPowerDifferentialForms (A := A) B.dividedPowers p →ₗ[(B : Type u)]
      dividedPowerDifferentialForms (A := A) C.dividedPowers p :=
  letI := algebraOf f
  { toFun := formsMap f hf p
    map_add' := map_add _
    map_smul' := fun b ω ↦ ((formsMap f hf p).map_smulₛₗ b ω).trans
      (algebraMap_smul (C : Type u) b (formsMap f hf p ω)) }

include hB hC hloc in
/-- **The map of divided power differentials along a localization, over zero divided power
ideals, is a localization**: it is the map of Kähler differentials, which is one. -/
theorem isLocalizedModule_oneFormsMap :
    letI := algebraOf f
    IsLocalizedModule (Submonoid.powers s) (oneFormsLinear f hf) := by
  let := algebraOf f
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a ↦ (f.commutes a).symm
  have := hloc
  let eB : Ω[(B : Type u)⁄A] ≃ₗ[(B : Type u)] dividedPowerDifferentials (A := A) B.dividedPowers :=
    (Submodule.quotEquivOfEqBot _ (dividedPowerDifferentialRelations_eq_bot hB)).symm
  let eC₀ : Ω[(C : Type u)⁄A] ≃ₗ[(C : Type u)]
      dividedPowerDifferentials (A := A) C.dividedPowers :=
    (Submodule.quotEquivOfEqBot _ (dividedPowerDifferentialRelations_eq_bot hC)).symm
  let eC : Ω[(C : Type u)⁄A] ≃ₗ[(B : Type u)]
      dividedPowerDifferentials (A := A) C.dividedPowers :=
    { eC₀.toAddEquiv with map_smul' := fun _ _ ↦ rfl }
  have h1 : IsLocalizedModule (Submonoid.powers s)
      (eC.toLinearMap ∘ₗ KaehlerDifferential.map A A (B : Type u) (C : Type u)) :=
    IsLocalizedModule.of_linearEquiv _ _ eC
  have hcomm : eC.toLinearMap ∘ₗ KaehlerDifferential.map A A (B : Type u) (C : Type u) =
      oneFormsLinear f hf ∘ₗ eB.toLinearMap := by
    refine LinearMap.ext fun ω ↦ ?_
    have hω : ω ∈ Submodule.span (B : Type u) (Set.range (KaehlerDifferential.D A (B : Type u))) :=
      (KaehlerDifferential.span_range_derivation A (B : Type u)).symm ▸ Submodule.mem_top
    induction hω using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      change eC₀ (KaehlerDifferential.map A A (B : Type u) (C : Type u)
          (KaehlerDifferential.D A (B : Type u) b)) =
        oneFormsMap f hf (dividedPowerDifferential (A := A) B.dividedPowers b)
      rw [KaehlerDifferential.map_D, oneFormsMap, mapDifferentialsOfDPMorphismₛₗ_apply,
        mapDifferentialsOfDPMorphism_d]
      rfl
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul b x _ hx => rw [LinearMap.map_smul, LinearMap.map_smul, hx]
  rw [hcomm] at h1
  exact (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers s) _
    eB.bijective).1 h1

include hB hC hloc in
/-- **The map of divided power differential forms along a localization, over zero divided power
ideals, is a localization**: exterior powers of a localization are localizations. -/
theorem isLocalizedModule_formsMap (p : ℕ) :
    letI := algebraOf f
    IsLocalizedModule (Submonoid.powers s) (formsLinear f hf p) := by
  let := algebraOf f
  have := hloc
  have := isLocalizedModule_oneFormsMap f hf hB hC s hloc
  exact IsLocalization.isLocalizedModule_of_exteriorPower (C : Type u) (oneFormsLinear f hf) p
    (Submonoid.powers s) (formsLinear f hf p) fun v ↦
      mapDifferentialFormsOfDPMorphism_ιMulti (A := A) B.ideal B.dividedPowers C.dividedPowers f
        hf p v

include hB hC hloc in
/-- **The map of de Rham terms along a localization, over zero divided power ideals, is a
localization**, for an `f`-semilinear map `μ : M → N` which is one: `m ⊗ ω ↦ μ m ⊗ Ω_f(ω)` is the
tensor product of two localizations. -/
theorem isLocalizedModule_tensorMap {M N : Type u} [AddCommGroup M] [Module (B : Type u) M]
    [AddCommGroup N] [Module (C : Type u) N] (μ : M →ₛₗ[f.toRingHom] N)
    (hμ : letI := compHomModule f N
      IsLocalizedModule (Submonoid.powers s) (toLinear f μ.toAddMonoidHom μ.map_smulₛₗ))
    (p : ℕ) :
    letI := compHomModule f (N ⊗[(C : Type u)]
      dividedPowerDifferentialForms (A := A) C.dividedPowers p)
    IsLocalizedModule (Submonoid.powers s)
      (toLinear f (tensorMap f μ (formsMap f hf p)) (tensorMap_smul f μ _)) := by
  let := algebraOf f
  have := hloc
  let := compHomModule f N
  have : IsScalarTower (B : Type u) (C : Type u) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have := hμ
  have := isLocalizedModule_formsMap f hf hB hC s hloc p
  have hsmul : ∀ (b : (B : Type u))
      (z : N ⊗[(C : Type u)] dividedPowerDifferentialForms (A := A) C.dividedPowers p),
      b • z = f b • z := fun b z ↦ by
    induction z using TensorProduct.induction_on with
    | zero => exact (smul_zero b).trans (smul_zero (f b)).symm
    | tmul n ω => rfl
    | add x y hx hy => exact (smul_add b x y).trans ((congrArg₂ (· + ·) hx hy).trans
        (smul_add (f b) x y).symm)
  let Φ : M ⊗[(B : Type u)] dividedPowerDifferentialForms (A := A) B.dividedPowers p
      →ₗ[(B : Type u)] N ⊗[(C : Type u)]
        dividedPowerDifferentialForms (A := A) C.dividedPowers p :=
    { toFun := tensorMap f μ (formsMap f hf p)
      map_add' := map_add _
      map_smul' := fun b z ↦ by
        rw [tensorMap_smul]
        exact (hsmul b _).symm }
  exact IsLocalizedModule.congr_module _ _ _ (Module.ext' _ _ hsmul) Φ _ (fun _ ↦ rfl)
    (IsLocalization.isLocalizedModule_of_tensor (Submonoid.powers s) (C : Type u)
      (toLinear f μ.toAddMonoidHom μ.map_smulₛₗ) (formsLinear f hf p) Φ fun _ _ ↦ rfl)

end Localization

end Crystalline.DeRhamPair
