module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.RingTensor
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.StalkComplexCriterion
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.KFlatTensor
public import StacksFrontier.AlgebraicGeometry.BaseChange.TensorFlatPushforwardBaseChange
public import StacksFrontier.Homology.KFlat.Flat

/-!
# The map of Stacks 0DJ7 at a complex flat over the base

Let `R → A`, `R → R'`, `A → A'`, `R' → A'` be a square of rings in which `A'` is a localization of
`A ⊗_R R'`, and let `N` be a complex of `A`-modules which, read over `R`, is K-flat — for instance
a bounded-above complex whose terms are flat over `R`.  Then for every isomorphism
`α : A' ⊗_A N ≅ Z` the map of Stacks 0DJ7

`H^n(N ⊗^L_R R') ⊗_{A ⊗_R R'} A' ⟶ H^n(Z)`

is an isomorphism in every degree: `N ⊗^L_R R'` is computed by `N ⊗_R R' = (A ⊗_R R') ⊗_A N`, and
cohomology commutes with the flat base change `A ⊗_R R' ⟶ A'`.  Read at the stalks of a cartesian
square of schemes this is the stalk check in the proof of Stacks 0A1D: for a bounded-above
complex `𝒢^•` of `𝒪_X`-modules flat over `S`, the derived-to-ordinary comparison
`L(g')^*𝒢^• ⟶ (g')^*𝒢^•` satisfies condition (1) of Stacks 0DJ8.

## Main results

* `RingTheory.TorIndependence.isLocalizedModule_modelTermMap`: the degreewise map of the model
  of a square of rings is a localization, for any model ring surjecting onto `R'`.
* `RingTheory.TorIndependence.quasiIso_modelUnitWhisker`: the part of the model map coming from
  the resolution of `R'` is a quasi-isomorphism at a complex K-flat over `R`.
* `RingTheory.TorIndependence.isIso_ringBaseChangeCohomologyMap_of_kFlat`: the ring-level
  statement.
* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_derivedPullbackNatTrans_of_isFlatOver`: the
  scheme-level statement.

## Implementation notes

The ring-level statement goes through the criterion
`RingTheory.TorIndependence.isIso_ringBaseChangeCohomologyMap_iff_isLocalizedModule`, with the
polynomial model `R₀ = R[R']`: the model map factors as `(B₀ ⊗_A N) ◁ ε`, a quasi-isomorphism
because `R₀ ⊗_R N` is K-flat over `R₀`, followed by a degreewise localization.

## References

* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard Algebra.TensorProduct.rightAlgebra

variable {R A R' A' R₀ : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [CommRing R₀]
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R R₀] [Algebra R₀ R'] [IsScalarTower R R₀ R']

local notation "B₀" => A ⊗[R] R₀

/-- **A localization transported along a surjective ring map.**  Let `σ : C₀ ⟶ C` be surjective,
`g : N ⟶ P` a localization of `C`-modules at `S`, and `h : M ⟶ P` a map of `C₀`-modules which
factors as `g` after an additive equivalence `Φ : M ≃ N` that is `σ`-semilinear, the `C₀`-action
on `P` being the one through `σ`.  Then `h` is the localization at the preimage of `S`. -/
theorem isLocalizedModule_comap_of_surjective {C₀ C M N P : Type*} [CommRing C₀] [CommRing C]
    (σ : C₀ →+* C) (hσ : Function.Surjective σ) (S : Submonoid C)
    [AddCommGroup M] [Module C₀ M] [AddCommGroup N] [Module C N] [AddCommGroup P] [Module C₀ P]
    [Module C P] (hP : ∀ (c : C₀) (p : P), c • p = σ c • p) (Φ : M ≃+ N)
    (hΦ : ∀ (c : C₀) (m : M), Φ (c • m) = σ c • Φ m) (g : N →ₗ[C] P) [IsLocalizedModule S g]
    (h : M →ₗ[C₀] P) (hh : ∀ m, h m = g (Φ m)) :
    IsLocalizedModule (S.comap σ) h := by
  constructor
  · rintro ⟨c, hc⟩
    have hu := IsLocalizedModule.map_units g (⟨σ c, hc⟩ : S)
    rw [Module.End.isUnit_iff] at hu ⊢
    convert hu using 1
    funext p
    exact hP c p
  · intro y
    obtain ⟨⟨z, ⟨s, hs⟩⟩, hz⟩ := IsLocalizedModule.surj S g y
    obtain ⟨c, rfl⟩ := hσ s
    refine ⟨⟨Φ.symm z, ⟨c, hs⟩⟩, ?_⟩
    simp only [Submonoid.smul_def] at hz ⊢
    rwa [hP, hh, AddEquiv.apply_symm_apply]
  · intro t₁ t₂ e
    rw [hh, hh] at e
    obtain ⟨⟨s, hs⟩, hst⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := g) e
    obtain ⟨c, rfl⟩ := hσ s
    refine ⟨⟨c, hs⟩, Φ.injective ?_⟩
    simp only [Submonoid.smul_def] at hst ⊢
    rwa [hΦ, hΦ]

section Term

variable (X : ModuleCat.{u} A)

/-- The identity of `X`, as an `A`-linear equivalence out of the restriction of `X` to `R` read
back over `A`. -/
def restrictScalarsAlgebraMapEquiv :
    (ModuleCat.restrictScalars (algebraMap R A)).obj X ≃ₗ[A] X where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The additive identification `(B₀ ⊗_A X) ⊗_{B₀} (B₀ ⊗_{R₀} R') ≃ (A ⊗_R R') ⊗_A X`,
`((a ⊗ r) ⊗ x) ⊗ (b ⊗ s) ↦ (1 ⊗ (r_b r) s) ⊗ a_b a x` for `b = a_b ⊗ r_b`. -/
def modelTermSourceEquiv :
    (B₀ ⊗[A] X) ⊗[B₀] (B₀ ⊗[R₀] R') ≃+ (A ⊗[R] R') ⊗[A] X :=
  (tensorBaseChangeAddEquiv X (ModuleCat.of R₀ R')).trans
    ((baseTensorLinearEquiv (R := R) (R₀ := R₀) (R' := R')
      ((ModuleCat.restrictScalars (algebraMap R A)).obj X)).toAddEquiv.trans
      ((baseChangeSwapAddEquiv (R := R) (A := A) (R₀ := R')
        ((ModuleCat.restrictScalars (algebraMap R A)).obj X)).symm.trans
        (TensorProduct.congr (LinearEquiv.refl A (A ⊗[R] R'))
          (restrictScalarsAlgebraMapEquiv (R := R) X)).toAddEquiv))

/-- `modelTermSourceEquiv` sends `((a ⊗ r) ⊗ x) ⊗ ((a₂ ⊗ r₂) ⊗ s)` to
`(1 ⊗ (r₂ r) s) ⊗ (a₂ a) x`. -/
theorem modelTermSourceEquiv_tmul (a : A) (r : R₀) (x : X) (a₂ : A) (r₂ : R₀) (s : R') :
    modelTermSourceEquiv X (((a ⊗ₜ[R] r) ⊗ₜ[A] x) ⊗ₜ[B₀] ((a₂ ⊗ₜ[R] r₂) ⊗ₜ[R₀] s)) =
      ((1 : A) ⊗ₜ[R] ((r₂ * r) • s)) ⊗ₜ[A] ((a₂ * a) • x) := by
  let X' := (ModuleCat.restrictScalars (algebraMap R A)).obj X
  let x' : X' := (a₂ * a) • x
  let t : (A ⊗[R] R') ⊗[A] X' := ((1 : A) ⊗ₜ[R] ((r₂ * r) • s)) ⊗ₜ[A] x'
  have h1 : baseChangeSwapAddEquiv (R := R) (A := A) (R₀ := R') X' t =
      ((r₂ * r) • s) ⊗ₜ[R] x' := by
    rw [baseChangeSwapAddEquiv_tmul, one_smul]
  have h2 : baseTensorLinearEquiv (R := R) (R₀ := R₀) (R' := R') X'
      (tensorBaseChangeAddEquiv X (ModuleCat.of R₀ R')
        (((a ⊗ₜ[R] r) ⊗ₜ[A] x) ⊗ₜ[B₀] ((a₂ ⊗ₜ[R] r₂) ⊗ₜ[R₀] s))) =
      ((r₂ * r) • s) ⊗ₜ[R] x' := by
    rw [tensorBaseChangeAddEquiv_tmul, TensorProduct.smul_tmul', smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul]
    exact baseTensorLinearEquiv_tmul (R := R) (R₀ := R₀) (R' := R') X' (r₂ * r) _ s
  have h3 : (baseChangeSwapAddEquiv (R := R) (A := A) (R₀ := R') X').symm
      (baseTensorLinearEquiv (R := R) (R₀ := R₀) (R' := R') X'
        (tensorBaseChangeAddEquiv X (ModuleCat.of R₀ R')
          (((a ⊗ₜ[R] r) ⊗ₜ[A] x) ⊗ₜ[B₀] ((a₂ ⊗ₜ[R] r₂) ⊗ₜ[R₀] s)))) = t :=
    (AddEquiv.symm_apply_eq _).2 (h2.trans h1.symm)
  change TensorProduct.congr (LinearEquiv.refl A (A ⊗[R] R'))
      (restrictScalarsAlgebraMapEquiv (R := R) X) ((baseChangeSwapAddEquiv (R := R) (A := A)
        (R₀ := R') X').symm (baseTensorLinearEquiv (R := R) (R₀ := R₀) (R' := R') X'
          (tensorBaseChangeAddEquiv X (ModuleCat.of R₀ R')
            (((a ⊗ₜ[R] r) ⊗ₜ[A] x) ⊗ₜ[B₀] ((a₂ ⊗ₜ[R] r₂) ⊗ₜ[R₀] s))))) = _
  rw [h3]
  exact TensorProduct.congr_tmul _ _ _ _

omit [Algebra R R'] [IsScalarTower R R₀ R'] in
/-- Additive maps out of `(B₀ ⊗_A X) ⊗_{B₀} (B₀ ⊗_{R₀} R')` agree as soon as they agree on the
elements `((a ⊗ r) ⊗ x) ⊗ ((a₂ ⊗ r₂) ⊗ s)`. -/
theorem modelSource_addHom_ext {Y : Type*} [AddCommGroup Y]
    {φ ψ : (B₀ ⊗[A] X) ⊗[B₀] (B₀ ⊗[R₀] R') →+ Y}
    (h : ∀ (a : A) (r : R₀) (x : X) (a₂ : A) (r₂ : R₀) (s : R'),
      φ (((a ⊗ₜ[R] r) ⊗ₜ[A] x) ⊗ₜ[B₀] ((a₂ ⊗ₜ[R] r₂) ⊗ₜ[R₀] s)) =
        ψ (((a ⊗ₜ[R] r) ⊗ₜ[A] x) ⊗ₜ[B₀] ((a₂ ⊗ₜ[R] r₂) ⊗ₜ[R₀] s))) : φ = ψ := by
  ext t
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul m w =>
    induction m using TensorProduct.inductionOn with
    | add m m' hm hm' => simp only [TensorProduct.add_tmul, map_add, hm, hm']
    | tmul b x =>
      induction b using TensorProduct.inductionOn with
      | add b b' hb hb' => simp only [TensorProduct.add_tmul, map_add, hb, hb']
      | tmul a r =>
        induction w using TensorProduct.inductionOn with
        | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add, hw, hw']
        | tmul b₂ s =>
          induction b₂ using TensorProduct.inductionOn with
          | add b₂ b₂' h₂ h₂' =>
            simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, h₂, h₂']
          | tmul a₂ r₂ => exact h a r x a₂ r₂ s

/-- `modelTermSourceEquiv` is linear over `B₀`, which acts on `(A ⊗_R R') ⊗_A X` through
`A ⊗_R R₀ ⟶ A ⊗_R R'`. -/
theorem modelTermSourceEquiv_smul (c : B₀) (t : (B₀ ⊗[A] X) ⊗[B₀] (B₀ ⊗[R₀] R')) :
    modelTermSourceEquiv X (c • t) =
      modelBaseRingMap R A R' R₀ c • modelTermSourceEquiv X t := by
  induction c using TensorProduct.inductionOn with
  | add c c' hc hc' => simp only [add_smul, map_add, hc, hc']
  | tmul a₃ r₃ =>
    let φ : (B₀ ⊗[A] X) ⊗[B₀] (B₀ ⊗[R₀] R') →+ (A ⊗[R] R') ⊗[A] X :=
      (modelTermSourceEquiv X).toAddMonoidHom.comp (DistribSMul.toAddMonoidHom _ (a₃ ⊗ₜ[R] r₃))
    let ψ : (B₀ ⊗[A] X) ⊗[B₀] (B₀ ⊗[R₀] R') →+ (A ⊗[R] R') ⊗[A] X :=
      (DistribSMul.toAddMonoidHom _ (modelBaseRingMap R A R' R₀ (a₃ ⊗ₜ[R] r₃))).comp
        (modelTermSourceEquiv X).toAddMonoidHom
    have key : φ = ψ := by
      refine modelSource_addHom_ext X fun a r x a₂ r₂ s => ?_
      simp only [φ, ψ, AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply,
        AddEquiv.coe_toAddMonoidHom]
      have e1 : ∀ (y : R') (z : X), ((a₃ ⊗ₜ[R] y) ⊗ₜ[A] z : (A ⊗[R] R') ⊗[A] X) =
          ((1 : A) ⊗ₜ[R] y) ⊗ₜ[A] (a₃ • z) := fun y z => by
        rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul,
        Algebra.TensorProduct.tmul_mul_tmul, modelTermSourceEquiv_tmul, modelTermSourceEquiv_tmul,
        show modelBaseRingMap R A R' R₀ (a₃ ⊗ₜ[R] r₃) = a₃ ⊗ₜ[R] algebraMap R₀ R' r₃ from rfl,
        TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, e1,
        smul_smul]
      have e2 : (r₂ * (r₃ * r)) • s = algebraMap R₀ R' r₃ * ((r₂ * r) • s) := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, map_mul]
        ring
      rw [mul_left_comm a₂ a₃ a, e2]
    exact DFunLike.congr_fun key t

/-- **The degreewise map of the model is a localization**, for any model `(R₀, F)` whose ring
`R₀` surjects onto `R'`: if `A'` is the localization of `A ⊗_R R'` at `S`, the map
`(B₀ ⊗_A X) ⊗_{B₀} (B₀ ⊗_{R₀} R') ⟶ A' ⊗_A X` is the localization at the preimage of `S` in
`B₀ = A ⊗_R R₀`.  Through `modelTermSourceEquiv` it is `(A ⊗_R R') ⊗_A X ⟶ A' ⊗_A X`. -/
theorem isLocalizedModule_modelTermMap (S : Submonoid (A ⊗[R] R'))
    (hloc : letI := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
      IsLocalization S A')
    (hsurj : Function.Surjective (algebraMap R₀ R')) :
    IsLocalizedModule (S.comap (modelBaseRingMap R A R' R₀))
      ((modelTermMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)).app X).hom := by
  let := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
  have : IsScalarTower A (A ⊗[R] R') A' := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A A' a = baseChangeTensorRingMap (a ⊗ₜ[R] 1)
    rw [baseChangeTensorRingMap_tmul, map_one, mul_one]
  have hσ : Function.Surjective (modelBaseRingMap R A R' R₀) :=
    TensorProduct.map_surjective Function.surjective_id hsurj
  let gX := TensorProduct.AlgebraTensorModule.rTensor A X (Algebra.linearMap (A ⊗[R] R') A')
  let Φ := modelTermSourceEquiv (R := R) (R' := R') (R₀ := R₀) X
  let h := ((modelTermMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)).app X).hom
  have hfac : ∀ t, h t = gX (Φ t) := by
    have key : h.toAddMonoidHom = gX.toAddMonoidHom.comp Φ.toAddMonoidHom := by
      refine modelSource_addHom_ext X fun a r x a₂ r₂ s => ?_
      change modelTermAdd (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X
          (((a ⊗ₜ[R] r) ⊗ₜ[A] x) ⊗ₜ[B₀] ((a₂ ⊗ₜ[R] r₂) ⊗ₜ[R₀] s)) = gX (Φ _)
      rw [modelTermAdd_tmul, modelUnitAddHom_tmul, modelRingMap_tmul, modelRingMap_tmul]
      change _ = gX (modelTermSourceEquiv X _)
      rw [modelTermSourceEquiv_tmul, TensorProduct.AlgebraTensorModule.rTensor_tmul,
        Algebra.linearMap_apply, ← TensorProduct.smul_tmul, Algebra.smul_def,
        RingHom.algebraMap_toAlgebra, baseChangeTensorRingMap_tmul, Algebra.smul_def, map_one,
        one_mul, map_mul, map_mul, map_mul, map_mul]
      congr 1
      ring
    exact DFunLike.congr_fun key
  let : Module (A ⊗[R] R')
      ((baseChangeFunctor A A' ⋙ ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj X) :=
    inferInstanceAs (Module (A ⊗[R] R') (A' ⊗[A] X))
  let i : A' ⊗[A] X →ₗ[A ⊗[R] R']
      ((baseChangeFunctor A A' ⋙ ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj X) :=
    { toFun := fun y => y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have : IsLocalizedModule S (i ∘ₗ gX) :=
    (IsLocalizedModule.comp_iff_of_bijective_left (S := S) i Function.bijective_id).2 inferInstance
  exact isLocalizedModule_comap_of_surjective
    (P := (baseChangeFunctor A A' ⋙ ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj X)
    (modelBaseRingMap R A R' R₀) hσ S
    (fun c p => (algebraMap_smul A' (modelBaseRingMap R A R' R₀ c) (show A' ⊗[A] X from p)).symm)
    Φ (modelTermSourceEquiv_smul X) (i ∘ₗ gX) h hfac

end Term

section Model

variable {F : CochainComplex (ModuleCat.{u} R₀) ℤ}
  (ε : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R'))
  [Module.Flat R R₀] (hF : F.KFlat) [QuasiIso ε]

omit [Algebra R R'] [IsScalarTower R R₀ R'] [Module.Flat R R₀] [QuasiIso ε] in
/-- The whiskering of the model complex by `ε`, written as the map induced on the total complex of
the model bifunctor. -/
theorem modelUnitWhisker_eq (N : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj N ◁
      ((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).map ε =
      HomologicalComplex.mapBifunctorMap (𝟙 N) ε (modelBifunctor (R := R) (A := A) (R₀ := R₀))
        (ComplexShape.up ℤ) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have h1 := HomologicalComplex.ι_mapBifunctorMap (𝟙 N) ε
    (modelBifunctor (R := R) (A := A) (R₀ := R₀)) (ComplexShape.up ℤ) p q n hpq
  have h2 := HomologicalComplex.ι_mapBifunctorMap
    (𝟙 (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
    (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).map ε)
    (curriedTensor (ModuleCat.{u} B₀)) (ComplexShape.up ℤ) p q n hpq
  refine h2.trans (Eq.trans ?_ h1.symm)
  simp only [modelBifunctor, Functor.comp_map, Functor.comp_obj, Functor.whiskeringLeft_obj_obj,
    HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Functor.mapHomologicalComplex_map_f]
  rfl

omit [Algebra R R'] [IsScalarTower R R₀ R'] [Module.Flat R R₀] [QuasiIso ε] in
/-- The whiskering of the model complex by `ε`, read over `R₀`, is `(R₀ ⊗_R N) ◁ ε`. -/
theorem modelUnitWhisker_restrict (N : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap (𝟙 N) ε (modelBifunctor (R := R) (A := A) (R₀ := R₀))
          (ComplexShape.up ℤ)) ≫
        (modelComplexRestrictIso N
          ((CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R'))).hom =
      (modelComplexRestrictIso N F).hom ≫
        (((Functor.mapHomologicalComplex
          (ModuleCat.restrictScalars (algebraMap R A) ⋙ baseChangeFunctor R R₀)
          (ComplexShape.up ℤ)).obj N) ◁
          (((𝟭 (ModuleCat.{u} R₀)).mapHomologicalComplex (ComplexShape.up ℤ)).map ε)) := by
  have nat := Functor.mapBifunctorTotalIso_hom_naturality
    (modelBifunctor (R := R) (A := A) (R₀ := R₀)) (curriedTensor (ModuleCat.{u} R₀))
    (ModuleCat.restrictScalars (algebraMap R A) ⋙ baseChangeFunctor R R₀) (𝟭 _)
    (ModuleCat.restrictScalars (algebraMap R₀ B₀)) modelBifunctorIso
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c := ComplexShape.up ℤ)
    modelBifunctorIso_naturality_left modelBifunctorIso_naturality_right N N F
    ((CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R')) (𝟙 N) ε
  rwa [CategoryTheory.Functor.map_id] at nat

omit [Algebra R R'] [IsScalarTower R R₀ R'] [Module.Flat R R₀] in
/-- The `ε`-part of the model map,
`(B₀ ⊗_A N) ⊗_{B₀} (B₀ ⊗_{R₀} F) ⟶ (B₀ ⊗_A N) ⊗_{B₀} (B₀ ⊗_{R₀} R')`, is a quasi-isomorphism
when `N`, read over `R`, is K-flat. -/
theorem quasiIso_modelUnitWhisker (N : CochainComplex (ModuleCat.{u} A) ℤ)
    (hN : CochainComplex.KFlat (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N)) :
    QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 N) ε
      (modelBifunctor (R := R) (A := A) (R₀ := R₀)) (ComplexShape.up ℤ)) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (ModuleCat.restrictScalars (algebraMap R₀ B₀))]
  refine (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk (modelComplexRestrictIso N F)
    (modelComplexRestrictIso N
      ((CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R')))
      (modelUnitWhisker_restrict ε N).symm)).2 ?_
  have hε : QuasiIso (((𝟭 (ModuleCat.{u} R₀)).mapHomologicalComplex (ComplexShape.up ℤ)).map ε) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology ε (𝟭 _)).2 inferInstance
  have hK : CochainComplex.KFlat
      (((ModuleCat.restrictScalars (algebraMap R A) ⋙ baseChangeFunctor R R₀).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N) :=
    CochainComplex.KFlat.of_iso ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (ModuleCat.restrictScalars (algebraMap R A) ⋙ baseChangeFunctor R R₀))
      (ComplexShape.up ℤ)).app N) (kFlat_baseChangeFunctor_obj R R₀ hN)
  exact StacksDraft.TorAmplitude.quasiIso_tensorLeft_map _ hK
    (((𝟭 (ModuleCat.{u} R₀)).mapHomologicalComplex (ComplexShape.up ℤ)).map ε)

/-- A quasi-isomorphism of cochain complexes of modules induces a bijection on the `n`-th
homology. -/
theorem bijective_homologyMap_of_quasiIso {B : Type u} [CommRing B]
    {K L : CochainComplex (ModuleCat.{u} B) ℤ} (φ : K ⟶ L) [QuasiIso φ] (n : ℤ) :
    Function.Bijective (HomologicalComplex.homologyMap φ n).hom :=
  ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap φ n)

/-- An isomorphism of cochain complexes of modules is bijective in every degree. -/
theorem bijective_f_of_isIso {B : Type u} [CommRing B]
    {K L : CochainComplex (ModuleCat.{u} B) ℤ} (φ : K ⟶ L) [IsIso φ] (i : ℤ) :
    Function.Bijective (φ.f i).hom := by
  have : IsIso (φ.f i) := (HomologicalComplex.eval _ _ i).map_isIso φ
  exact ConcreteCategory.bijective_of_isIso (φ.f i)

/-- The part of the model map after the whiskering by `ε`. -/
abbrev modelKappaRest (N : CochainComplex (ModuleCat.{u} A) ℤ)
    (Z : CochainComplex (ModuleCat.{u} A') ℤ)
    (α : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z) :=
  ((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj N ◁
      (HomologicalComplex.singleMapHomologicalComplex (baseChangeFunctor R₀ B₀)
        (ComplexShape.up ℤ) 0).hom.app (ModuleCat.of R₀ R') ≫
    ((tensorSingleIso ((baseChangeFunctor R₀ B₀).obj (ModuleCat.of R₀ R'))).inv.app
        (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≫
      (NatTrans.mapHomologicalComplex (modelTermMap (R := R) (A := A) (R' := R') (A' := A')
        (R₀ := R₀)) (ComplexShape.up ℤ)).app N) ≫
    (NatIso.mapHomologicalComplex (Functor.isoWhiskerRight (baseChangeIsoExtendScalars A A')
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))) (ComplexShape.up ℤ)).hom.app N ≫
    ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map α

omit [Module.Flat R R₀] [QuasiIso ε] in
/-- The model map is the whiskering by `ε` followed by `modelKappaRest`. -/
theorem modelKappa_eq (N : CochainComplex (ModuleCat.{u} A) ℤ)
    (Z : CochainComplex (ModuleCat.{u} A') ℤ)
    (α : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z) :
    modelKappa (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε N Z α =
      (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj N ◁
        ((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).map ε) ≫
        modelKappaRest (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) N Z α := by
  simp only [modelKappa, modelMapX, modelMapE, modelMap, MonoidalCategory.whiskerLeft_comp,
    Category.assoc]

omit [Module.Flat R R₀] in
/-- Each component of `modelKappaRest` is a localization. -/
theorem isLocalizedModule_modelKappaRest_f (S : Submonoid (A ⊗[R] R'))
    (hloc : letI := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
      IsLocalization S A')
    (hsurj : Function.Surjective (algebraMap R₀ R'))
    (N : CochainComplex (ModuleCat.{u} A) ℤ) (Z : CochainComplex (ModuleCat.{u} A') ℤ)
    (α : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z) [IsIso α] (i : ℤ) :
    IsLocalizedModule (S.comap (modelBaseRingMap R A R' R₀))
      ((modelKappaRest (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) N Z α).f i).hom := by
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp]
  refine (IsLocalizedModule.comp_iff_of_bijective_right _ _ (bijective_f_of_isIso _ i)).2 ?_
  refine (IsLocalizedModule.comp_iff_of_bijective_left _ _
    ((bijective_f_of_isIso _ i).comp (bijective_f_of_isIso _ i))).2 ?_
  refine (IsLocalizedModule.comp_iff_of_bijective_right _ _ (bijective_f_of_isIso _ i)).2 ?_
  exact isLocalizedModule_modelTermMap (N.X i) S hloc hsurj

include ε hF in
/-- **The map of Stacks 0DJ7 at a complex K-flat over the base, through a model.**  Let `A'` be
the localization of `A ⊗_R R'` at `S`, and let `(R₀, F, ε)` be a model whose ring surjects onto
`R'`.  For a complex `N` of `A`-modules which is K-flat over `R`, and an isomorphism
`α : A' ⊗_A N ≅ Z`, the map of Stacks 0DJ7 at `(N, Z, α)` is an isomorphism in every degree. -/
theorem isIso_ringBaseChangeCohomologyMap_of_kFlat_of_model (S : Submonoid (A ⊗[R] R'))
    (hloc : letI := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
      IsLocalization S A')
    (hsurj : Function.Surjective (algebraMap R₀ R'))
    (N : CochainComplex (ModuleCat.{u} A) ℤ)
    (hN : CochainComplex.KFlat (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N))
    (Z : CochainComplex (ModuleCat.{u} A') ℤ)
    (α : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z) [IsIso α] (n : ℤ) :
    IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') (DerivedCategory.Q.obj N)
      (DerivedCategory.Q.obj Z) (alphaH A A' N ≫ DerivedCategory.Q.map α) n) := by
  rw [isIso_ringBaseChangeCohomologyMap_iff_isLocalizedModule (R₀ := R₀) ε hF n S hloc hsurj N Z α,
    isLocalizedModule_homologyFunctor_map_Q_iff, modelKappa_eq,
    HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]
  have : QuasiIso (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj N ◁
      ((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).map ε) := by
    rw [modelUnitWhisker_eq]
    exact quasiIso_modelUnitWhisker ε N hN
  refine (IsLocalizedModule.comp_iff_of_bijective_right _ _
    (bijective_homologyMap_of_quasiIso _ n)).2 ?_
  exact CochainComplex.isLocalizedModule_homologyMap _ _
    (isLocalizedModule_modelKappaRest_f S hloc hsurj N Z α) n

end Model

section Unconditional

/-- **The map of Stacks 0DJ7 at a complex K-flat over the base, over rings.**  Let `A'` be the
localization of `A ⊗_R R'` at `S`.  For a complex `N` of `A`-modules which, read over `R`, is
K-flat, and an isomorphism `α : A' ⊗_A N ≅ Z`, the map of Stacks 0DJ7 at `(N, Z, α)` is an
isomorphism in every degree: `H^n(N ⊗^L_R R') = H^n(N ⊗_R R')` and
`H^n(N ⊗_R R') ⊗_{A ⊗_R R'} A' = H^n(A' ⊗_A N)`, `A'` being flat over `A ⊗_R R'`.  The model
is the polynomial one, `R₀ = R[R']`. -/
theorem isIso_ringBaseChangeCohomologyMap_of_kFlat (S : Submonoid (A ⊗[R] R'))
    (hloc : letI := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
      IsLocalization S A')
    (N : CochainComplex (ModuleCat.{u} A) ℤ)
    (hN : CochainComplex.KFlat (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N))
    (Z : CochainComplex (ModuleCat.{u} A') ℤ)
    (α : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z) [IsIso α] (n : ℤ) :
    IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') (DerivedCategory.Q.obj N)
      (DerivedCategory.Q.obj Z) (alphaH A A' N ≫ DerivedCategory.Q.map α) n) := by
  let : Algebra (MvPolynomial R' R) R' :=
    (MvPolynomial.aeval (R := R) (fun x : R' => x)).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial R' R) R' :=
    IsScalarTower.of_algebraMap_eq fun r =>
      ((MvPolynomial.aeval (R := R) (fun x : R' => x)).commutes r).symm
  have hsurj : Function.Surjective (algebraMap (MvPolynomial R' R) R') := fun x =>
    ⟨MvPolynomial.X x, MvPolynomial.aeval_X _ x⟩
  obtain ⟨F, ε, hF, -, hε, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u}
    ((CochainComplex.singleFunctor (ModuleCat.{u} (MvPolynomial R' R)) 0).obj
      (ModuleCat.of (MvPolynomial R' R) R'))
  exact isIso_ringBaseChangeCohomologyMap_of_kFlat_of_model (R₀ := MvPolynomial R' R) ε hF S hloc
    hsurj N hN Z α n

end Unconditional

end RingTheory.TorIndependence

namespace AlgebraicGeometry

open RingTheory.TorIndependence Stacks.Cohomology.DerivedPullbackTensor

attribute [local instance] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **The stalk check of Stacks 0DJ8 for a complex flat over the base, at one point.**  For a
cartesian square of schemes and a bounded-above complex `𝒢^•` of `𝒪_X`-modules whose terms are
flat over `S`, the map of Stacks 0DJ7 at the derived-to-ordinary comparison
`L(g')^*𝒢^• ⟶ (g')^*𝒢^•` is an isomorphism at `x'` in degree `n`. -/
@[stacks 0DJ8 "condition (1), at every point and in every degree, for the derived-to-ordinary \
comparison L(g')^*G ⟶ (g')^*G of a bounded-above complex G whose terms are flat over S, over a \
cartesian square: the stalk check the proof of Tag 0A1D performs"]
theorem isIso_baseChangeCohomologyMap_derivedPullbackNatTrans_of_isFlatOver
    (hpb : IsPullback g' f' f g) (w : g' ≫ f = f' ≫ g) (G : CochainComplex X.Modules ℤ)
    (hG : CochainComplex.minus X.Modules G)
    (hflat : ∀ n : ℤ, IsFlatOver f.toLRSHom.toShHom (G.X n)) (x' : X') (n : ℤ) :
    IsIso (baseChangeCohomologyMap f g f' g' w (DerivedCategory.Q.obj G)
      (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj G))
      ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app G) x' n) := by
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
    ((f.stalkMap (g' x')).hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
    (baseStalkMap f g f' g' w x').toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X'.presheaf.stalk x') :=
    (((g'.stalkMap x').hom).comp ((f.stalkMap (g' x')).hom)).toAlgebra
  let : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
    ((g'.stalkMap x').hom).toAlgebra
  let : Algebra (S'.presheaf.stalk (f' x')) (X'.presheaf.stalk x') :=
    ((f'.stalkMap x').hom).toAlgebra
  let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x'))
      (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x'))
      (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w x')
  obtain ⟨M, hM⟩ := exists_isLocalization_stalk hpb x'
  obtain ⟨d, hd⟩ := hG
  let P := ((ModuleCat.restrictScalars (algebraMap (S.presheaf.stalk (f (g' x')))
    (X.presheaf.stalk (g' x')))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((Stacks.ModuleSkyscraper.modulesStalkFunctor X (g' x')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G)
  have : CochainComplex.IsStrictlyLE P d := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact Functor.map_isZero (ModuleCat.restrictScalars (algebraMap (S.presheaf.stalk (f (g' x')))
      (X.presheaf.stalk (g' x')))) (Functor.map_isZero
        (Stacks.ModuleSkyscraper.modulesStalkFunctor X (g' x')) (G.isZero_of_isStrictlyLE d i hi))
  have : ∀ i : ℤ, Module.Flat (S.presheaf.stalk (f (g' x'))) (P.X i) := fun i =>
    hflat i (g' x')
  have hN : CochainComplex.KFlat P := CochainComplex.KFlat.kFlat_of_flat.{u, u} P d
  let 𝒵 := ((Scheme.Modules.pullback g').mapHomologicalComplex (ComplexShape.up ℤ)).obj G
  have : IsIso ((NatIso.mapHomologicalComplex (Stacks.ModuleSkyscraper.pullbackStalkIso g' x')
      (ComplexShape.up ℤ)).hom.app G ≫
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X' x').mapHomologicalComplex
        (ComplexShape.up ℤ)).map (𝟙 𝒵)) := by
    rw [CategoryTheory.Functor.map_id]
    exact IsIso.comp_isIso' ((NatIso.mapHomologicalComplex
      (Stacks.ModuleSkyscraper.pullbackStalkIso g' x') (ComplexShape.up ℤ)).app G).isIso_hom
      (IsIso.id _)
  have key := isIso_ringBaseChangeCohomologyMap_of_kFlat M hM
    (((Stacks.ModuleSkyscraper.modulesStalkFunctor X (g' x')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj G) hN
    (((Stacks.ModuleSkyscraper.modulesStalkFunctor X' x').mapHomologicalComplex
      (ComplexShape.up ℤ)).obj 𝒵)
    ((NatIso.mapHomologicalComplex (Stacks.ModuleSkyscraper.pullbackStalkIso g' x')
      (ComplexShape.up ℤ)).hom.app G ≫
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X' x').mapHomologicalComplex
        (ComplexShape.up ℤ)).map (𝟙 𝒵)) n
  have h := (isIso_baseChangeCohomologyMap_complex_iff f g f' g' w G 𝒵 (𝟙 𝒵) x' n).2 key
  exact isIso_baseChangeCohomologyMap_of_eq w _ _ _ _
    ((Category.comp_id _).symm.trans (congrArg _ (DerivedCategory.Q.map_id _).symm)) x' n h

end AlgebraicGeometry
