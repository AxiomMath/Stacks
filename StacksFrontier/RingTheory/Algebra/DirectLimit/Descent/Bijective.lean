module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent of bijectivity to a finite stage of a directed colimit

Here `A = colim_i Aᵢ` is `Ring.DirectLimit`, the base ring is the stage `A i₀`, and for
`i₀ ≤ i` the stage `A i` is an `A i₀`-algebra via the transition map `f i₀ i h`; since that
structure depends on `h`, it is supplied locally with `letI`. The base changes are
`φ = lTensor A φ₀` and `φᵢ = lTensor (A i) φ₀`, and an isomorphism of rings is a bijective
algebra homomorphism.

## Main results

* `Stacks.DirectLimit.FinitePresentationDescent.isIso_of_finitePresentation_colim`: if
  `id_A ⊗ φ₀` is bijective and `φ₀` is of finite presentation, then some `id_{Aᵢ} ⊗ φ₀` is
  bijective.

## References

* [Stacks Project, Tag 0C32](https://stacks.math.columbia.edu/tag/0C32)
-/

@[expose] public section

open Ring TensorProduct

namespace Stacks.DirectLimit.FinitePresentationDescent

variable {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
variable (A : ι → Type*) [∀ i, CommRing (A i)]
variable (f : (i j : ι) → i ≤ j → A i →+* A j)
variable [DirectedSystem A (fun i j h => (f i j h : A i → A j))]

/-- The directed colimit (direct limit) `A = colim_{i ∈ I} A_i` of the directed
system of commutative rings `A_i` with transition maps `f_{ij}`. -/
noncomputable abbrev Colim : Type _ :=
  Ring.DirectLimit A (fun i j h => (f i j h : A i → A j))

variable (i₀ : ι)
variable (B₀ C₀ : Type*) [CommRing B₀] [CommRing C₀]
variable [Algebra (A i₀) B₀] [Algebra (A i₀) C₀]
variable (φ₀ : B₀ →ₐ[A i₀] C₀)

/-- The colimit `A` is an `A i₀`-algebra via the canonical structure map
`Ring.DirectLimit.of A f i₀ : A i₀ →+* A`. -/
noncomputable instance algebraColim : Algebra (A i₀) (Colim A f) :=
  (Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) i₀).toAlgebra

/-- The base change `φ = id_A ⊗ φ₀ : A ⊗_{A i₀} B₀ → A ⊗_{A i₀} C₀`. -/
noncomputable def phiColim :
    TensorProduct (A i₀) (Colim A f) B₀ →ₐ[A i₀] TensorProduct (A i₀) (Colim A f) C₀ :=
  Algebra.TensorProduct.lTensor (Colim A f) φ₀

/-- The base change `φ_i = id_{A_i} ⊗ φ₀ : A_i ⊗_{A i₀} B₀ → A_i ⊗_{A i₀} C₀`,
where for `i₀ ≤ i` the object `A i` is given its `A i₀`-algebra structure via the
transition map `f i₀ i h`. -/
noncomputable def phiAt (i : ι) (h : i₀ ≤ i) :
    letI := (f i₀ i h).toAlgebra
    TensorProduct (A i₀) (A i) B₀ →ₐ[A i₀] TensorProduct (A i₀) (A i) C₀ :=
  letI := (f i₀ i h).toAlgebra
  Algebra.TensorProduct.lTensor (A i) φ₀

/-! ### The colimit as a module direct limit over the cofinal subtype

The underlying `A i₀`-module of the ring direct limit `Colim A f` is the module direct
limit of the system `(A j)_{i₀ ≤ j}` over the cofinal subtype `J = {i // i₀ ≤ i}`. The
`A i₀`-module structure on `A j.val` depends on the proof `i₀ ≤ j.val`, so it is passed
explicitly through `modJ`.
-/

open scoped Classical in
/-- The `A i₀`-module structure on `A j.val` for `j` in the cofinal subtype
`{i // i₀ ≤ i}`, via the transition ring map `f i₀ j.val`. -/
@[reducible] noncomputable def modJ (j : {i : ι // i₀ ≤ i}) : Module (A i₀) (A j.1) :=
  ((f i₀ j.val j.property).toAlgebra).toModule

open scoped Classical in
/-- Transition maps of the module direct system `(A j)_{i₀ ≤ j}`: the ring map
`f j.val k.val` viewed as an `A i₀`-linear map. -/
noncomputable def gJ (j k : {i : ι // i₀ ≤ i}) (h : j ≤ k) :
    @LinearMap (A i₀) (A i₀) _ _ (RingHom.id _) (A j.1) (A k.1) _ _ (modJ A f i₀ j) (modJ A f i₀ k)
        :=
  letI := (f i₀ j.val j.property).toAlgebra
  letI := (f i₀ k.val k.property).toAlgebra
  { toFun := f j.val k.val h
    map_add' := by simp
    map_smul' := by
      intro a x
      simp only [RingHom.id_apply]
      change (f j.val k.val h) ((f i₀ j.val j.property) a * x)
        = (f i₀ k.val k.property) a * (f j.val k.val h) x
      rw [map_mul]
      congr 1
      show (f j.val k.val h) ((f i₀ j.val j.property) a) = (f i₀ k.val k.property) a
      exact DirectedSystem.map_map (F := A)
        (f := fun i j h => (f i j h : A i → A j)) j.property h a }

omit [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
open scoped Classical in
/-- The transition map `gJ j k h` agrees with the ring map `f j.1 k.1 h` on elements. -/
@[simp] lemma gJ_apply (j k : {i : ι // i₀ ≤ i}) (h : j ≤ k) (x : A j.1) :
    gJ A f i₀ j k h x = f j.1 k.1 h x := rfl

open scoped Classical in
/-- The maps `gJ` make `(A j)_{i₀ ≤ j}` a directed system of `A i₀`-modules over the
cofinal subtype `{i // i₀ ≤ i}`. -/
instance dsJ : DirectedSystem (fun j : {i : ι // i₀ ≤ i} => A j.1)
    (fun j k h => (gJ A f i₀ j k h : A j.1 → A k.1)) := by
  constructor
  · intro j x
    simp only [gJ_apply]
    exact DirectedSystem.map_self (F := A) (f := fun i j h => (f i j h : A i → A j)) x
  · intro j k l hjk hkl x
    simp only [gJ_apply]
    exact DirectedSystem.map_map (F := A) (f := fun i j h => (f i j h : A i → A j)) hjk hkl x

/-- The cofinal subtype `{i // i₀ ≤ i}` of a directed preorder is directed. -/
private instance isDirected_subtype_le :
    IsDirected {i : ι // i₀ ≤ i} (· ≤ ·) where
  directed j k := by
    obtain ⟨m, hjm, hkm⟩ := directed_of (· ≤ ·) j.val k.val
    exact ⟨⟨m, le_trans j.property hjm⟩, hjm, hkm⟩

open scoped Classical in
/-- The module direct limit of the system `(A j)_{i₀ ≤ j}` over the cofinal subtype. -/
@[reducible] noncomputable def ModColim : Type _ :=
  @Module.DirectLimit (A i₀) _ {i : ι // i₀ ≤ i} _ (fun j => A j.val)
    (fun _ => inferInstance) (modJ A f i₀) (gJ A f i₀) _

open scoped Classical in
/-- The structure map `A j.val → ModColim` of the module direct limit. -/
noncomputable def ModColim.of (j : {i : ι // i₀ ≤ i}) :
    letI := modJ A f i₀ j
    A j.val →ₗ[A i₀] ModColim A f i₀ :=
  @Module.DirectLimit.of (A i₀) _ {i : ι // i₀ ≤ i} _ (fun j => A j.val)
    (fun _ => inferInstance) (modJ A f i₀) (gJ A f i₀) _ j

open scoped Classical in
/-- The underlying `A i₀`-module of the ring direct limit `Colim A f` is
`A i₀`-linearly isomorphic to the module direct limit, compatibly with the structure maps. -/
lemma exists_linearEquiv_modColim :
    ∃ Ψ : Colim A f ≃ₗ[A i₀] ModColim A f i₀,
      ∀ (j : {i : ι // i₀ ≤ i}) (x : A j.1),
        Ψ (Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) j.1 x)
          = ModColim.of A f i₀ j x := by
  classical
  let g : ∀ j : {i : ι // i₀ ≤ i},
      @LinearMap (A i₀) (A i₀) _ _ (RingHom.id _) (A j.val) (Colim A f) _ _
        (modJ A f i₀ j) (Algebra.toModule) := fun j =>
    let := (f i₀ j.val j.property).toAlgebra
    { toFun := Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) j.val
      map_add' := by simp
      map_smul' := by
        intro a x
        simp only [RingHom.id_apply]
        show Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) j.val
            ((f i₀ j.val j.property) a * x)
          = a • Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) j.val x
        rw [map_mul, Algebra.smul_def]
        show Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) j.val
              ((f i₀ j.val j.property) a)
            * Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) j.val x
          = Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) i₀ a
            * Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) j.val x
        congr 1
        exact Ring.DirectLimit.of_f (G := A)
          (f := fun i j h => (f i j h : A i → A j)) j.property a }
  have Hg : ∀ (j k : {i : ι // i₀ ≤ i}) (hjk : j ≤ k) (x : A j.val),
      g k (gJ A f i₀ j k hjk x) = g j x := by
    intro j k hjk x
    show Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) k.val (f j.val k.val hjk x)
      = Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) j.val x
    exact Ring.DirectLimit.of_f (G := A) (f := fun i j h => (f i j h : A i → A j)) hjk x
  let Φ : ModColim A f i₀ →ₗ[A i₀] Colim A f :=
    @Module.DirectLimit.lift (A i₀) _ {i : ι // i₀ ≤ i} _ (fun j => A j.val)
      (fun j => inferInstance) (modJ A f i₀) (gJ A f i₀) _ _ _ _ g Hg
  have hΦof : ∀ (j : {i : ι // i₀ ≤ i}) (x : A j.val),
      Φ (ModColim.of A f i₀ j x)
        = Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) j.val x := fun j x =>
    @Module.DirectLimit.lift_of (A i₀) _ {i : ι // i₀ ≤ i} _ (fun j => A j.val)
      (fun j => inferInstance) (modJ A f i₀) (gJ A f i₀) _ _ _ _ g Hg j x
  have hsurj : Function.Surjective Φ := by
    intro z
    refine Ring.DirectLimit.induction_on (G := A)
      (f := fun i j h => (f i j h : A i → A j)) z (fun i x => ?_)
    obtain ⟨k, hik, hi₀k⟩ := directed_of (· ≤ ·) i i₀
    refine ⟨ModColim.of A f i₀ ⟨k, hi₀k⟩ (f i k hik x), ?_⟩
    rw [hΦof ⟨k, hi₀k⟩ (f i k hik x)]
    exact Ring.DirectLimit.of_f (G := A) (f := fun i j h => (f i j h : A i → A j)) hik x
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨j, x, rfl⟩ := @Module.DirectLimit.exists_of (A i₀) _ {i : ι // i₀ ≤ i} _
      (fun j => A j.val) (fun j => inferInstance) (modJ A f i₀) (gJ A f i₀) _ _ _ z
    have hz' : Φ (ModColim.of A f i₀ j x) = 0 := hz
    rw [hΦof j x] at hz'
    obtain ⟨k, hjk, hk0⟩ := Ring.DirectLimit.of.zero_exact hz'
    have hjk' : j ≤ (⟨k, le_trans j.property hjk⟩ : {i : ι // i₀ ≤ i}) := hjk
    have hof : ModColim.of A f i₀ j x
        = ModColim.of A f i₀ ⟨k, le_trans j.property hjk⟩
            (gJ A f i₀ j ⟨k, le_trans j.property hjk⟩ hjk' x) :=
      (@Module.DirectLimit.of_f (A i₀) _ {i : ι // i₀ ≤ i} _ (fun j => A j.val)
        (fun j => inferInstance) (modJ A f i₀) (gJ A f i₀) _ j
          ⟨k, le_trans j.property hjk⟩ hjk' x).symm
    show ModColim.of A f i₀ j x = 0
    rw [hof]
    have : gJ A f i₀ j ⟨k, le_trans j.property hjk⟩ hjk' x = 0 := by
      show f j.val k hjk x = 0
      exact hk0
    rw [this, map_zero]
  let e : ModColim A f i₀ ≃ₗ[A i₀] Colim A f := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  refine ⟨e.symm, fun j x => ?_⟩
  rw [LinearEquiv.symm_apply_eq]
  show Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) j.val x
      = Φ (ModColim.of A f i₀ j x)
  rw [hΦof j x]

open scoped Classical in
/-- The `A i₀`-linear structure map `A j.val →ₗ[A i₀] Colim A f` for `j` in the
cofinal subtype, underlying `Ring.DirectLimit.of`. -/
noncomputable def ofColimLin (j : {i : ι // i₀ ≤ i}) :
    letI := modJ A f i₀ j
    A j.val →ₗ[A i₀] Colim A f :=
  letI := (f i₀ j.val j.property).toAlgebra
  { toFun := Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) j.val
    map_add' := by simp
    map_smul' := by
      intro a x
      simp only [RingHom.id_apply]
      change Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) j.val
          ((f i₀ j.val j.property) a * x)
        = a • Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) j.val x
      rw [map_mul, Algebra.smul_def]
      change Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) j.val
            ((f i₀ j.val j.property) a)
          * Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) j.val x
        = Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) i₀ a
          * Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) j.val x
      congr 1
      exact Ring.DirectLimit.of_f (G := A)
        (f := fun i j h => (f i j h : A i → A j)) j.property a }

omit [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] [DirectedSystem A fun i j h ↦ ⇑(f i j h)] in
open scoped Classical in
/-- The linear map `ofColimLin j` agrees with `Ring.DirectLimit.of` at `j.1` on elements. -/
@[simp] lemma ofColimLin_apply (j : {i : ι // i₀ ≤ i}) (x : A j.1) :
    ofColimLin A f i₀ j x = Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) j.1 x := rfl

/-- There is an `A i₀`-linear equivalence `Colim A f ≃ ModColim A f i₀` sending `ofColimLin j` to
`ModColim.of j`. -/
private lemma exists_linearEquiv_comp_ofColimLin :
    ∃ Ψ : Colim A f ≃ₗ[A i₀] ModColim A f i₀, ∀ j : {i : ι // i₀ ≤ i},
      letI := modJ A f i₀ j
      Ψ.toLinearMap ∘ₗ ofColimLin A f i₀ j = ModColim.of A f i₀ j := by
  obtain ⟨Ψ, hΨ⟩ := exists_linearEquiv_modColim A f i₀
  exact ⟨Ψ, fun j => by
    let := modJ A f i₀ j
    exact LinearMap.ext fun a => hΨ j a⟩

open scoped Classical in
/-- Every element of `Colim ⊗ M` comes from a finite stage: it is the image, under
`rTensor M (ofColimLin j)`, of some element of `A j.val ⊗ M`. -/
lemma exists_stage_tensor (M : Type*) [AddCommGroup M] [Module (A i₀) M]
    (z : TensorProduct (A i₀) (Colim A f) M) :
    ∃ (j : {i : ι // i₀ ≤ i}),
      letI := modJ A f i₀ j
      ∃ (y : TensorProduct (A i₀) (A j.val) M),
        LinearMap.rTensor M (ofColimLin A f i₀ j) y = z := by
  classical
  obtain ⟨Ψ, hΨ⟩ := exists_linearEquiv_comp_ofColimLin A f i₀
  set δ := @TensorProduct.directLimitLeft (A i₀) _ {i : ι // i₀ ≤ i} _ _
    (fun j => A j.val) (fun j => inferInstance) (modJ A f i₀) (gJ A f i₀) M _ _ with hδ
  set w := δ (LinearMap.rTensor M Ψ.toLinearMap z) with hw
  obtain ⟨j, y, hy⟩ := Module.DirectLimit.exists_of w
  let := modJ A f i₀ j
  refine ⟨j, y, ?_⟩
  have hdl := @TensorProduct.directLimitLeft_rTensor_of (A i₀) _ {i : ι // i₀ ≤ i} _ _
    (fun j => A j.val) (fun j => inferInstance) (modJ A f i₀) (gJ A f i₀) M _ _ j y
  have key : δ (LinearMap.rTensor M Ψ.toLinearMap
      (LinearMap.rTensor M (ofColimLin A f i₀ j) y)) = w := by
    rw [← LinearMap.rTensor_comp_apply, hΨ j]
    exact hdl.trans hy
  have hwz : δ (LinearMap.rTensor M Ψ.toLinearMap z) = w := hw.symm
  have h1 : δ (LinearMap.rTensor M Ψ.toLinearMap
      (LinearMap.rTensor M (ofColimLin A f i₀ j) y))
      = δ (LinearMap.rTensor M Ψ.toLinearMap z) := by rw [key, hwz]
  have h2 := δ.injective h1
  have hinj : Function.Injective (LinearMap.rTensor M Ψ.toLinearMap) := by
    rw [← LinearEquiv.coe_rTensor]; exact (Ψ.rTensor M).injective
  exact hinj h2

open scoped Classical in
/-- An element of a finite stage `A j₀.val ⊗ M` that maps to `0` in `Colim ⊗ M`
already dies at some higher finite stage. -/
lemma exists_stage_rTensor_eq_zero (M : Type*) [AddCommGroup M] [Module (A i₀) M]
    (j₀ : {i : ι // i₀ ≤ i}) :
    letI := modJ A f i₀ j₀
    ∀ (y : TensorProduct (A i₀) (A j₀.val) M),
      LinearMap.rTensor M (ofColimLin A f i₀ j₀) y = 0 →
      ∃ (k : {i : ι // i₀ ≤ i}) (hjk : j₀ ≤ k),
        letI := modJ A f i₀ k
        LinearMap.rTensor M (gJ A f i₀ j₀ k hjk) y = 0 := by
  classical
  let := modJ A f i₀ j₀
  intro y hy
  obtain ⟨Ψ, hΨ⟩ := exists_linearEquiv_comp_ofColimLin A f i₀
  set δ := @TensorProduct.directLimitLeft (A i₀) _ {i : ι // i₀ ≤ i} _ _
    (fun j => A j.val) (fun j => inferInstance) (modJ A f i₀) (gJ A f i₀) M _ _ with hδ
  have hcomp : (LinearMap.rTensor M Ψ.toLinearMap)
      (LinearMap.rTensor M (ofColimLin A f i₀ j₀) y) = 0 := by
    rw [hy, map_zero]
  have hstep : LinearMap.rTensor M (ModColim.of A f i₀ j₀) y = 0 := by
    rwa [← LinearMap.rTensor_comp_apply, hΨ j₀] at hcomp
  have hdl := @TensorProduct.directLimitLeft_rTensor_of (A i₀) _ {i : ι // i₀ ≤ i} _ _
    (fun j => A j.val) (fun j => inferInstance) (modJ A f i₀) (gJ A f i₀) M _ _ j₀ y
  have hstep' : LinearMap.rTensor M
      (@Module.DirectLimit.of (A i₀) _ {i : ι // i₀ ≤ i} _ (fun j => A j.val)
        (fun j => inferInstance) (modJ A f i₀) (gJ A f i₀) _ j₀) y = 0 := hstep
  rw [hstep', map_zero] at hdl
  obtain ⟨k, hjk, hk0⟩ := Module.DirectLimit.of.zero_exact hdl.symm
  exact ⟨k, hjk, hk0⟩

/-- Base changes along `g` and `ψ` in the two tensor factors commute. -/
private lemma rTensor_lTensor_comm {R M N P Q : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [Module R M] [Module R N] [Module R P]
    [Module R Q] (g : M →ₗ[R] N) (ψ : P →ₗ[R] Q) (b : TensorProduct R M P) :
    LinearMap.rTensor Q g (LinearMap.lTensor M ψ b)
      = LinearMap.lTensor N ψ (LinearMap.rTensor P g b) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
    LinearMap.lTensor_comp_rTensor]

open scoped Classical in
/-- Single-element descent for surjectivity: if the colimit base change is
surjective, then for every `c : C₀` there is a finite stage `j` at which
`(1 : A j.val) ⊗ c` is in the image of `φ_j`. -/
lemma exists_tmul_mem_range_phiAt
    (hφ : Function.Surjective (phiColim A f i₀ B₀ C₀ φ₀)) (c : C₀) :
    ∃ (j : {i : ι // i₀ ≤ i}),
      letI := (f i₀ j.val j.property).toAlgebra
      (1 : A j.val) ⊗ₜ[A i₀] c ∈ Set.range (phiAt A f i₀ B₀ C₀ φ₀ j.val j.property) := by
  classical
  obtain ⟨y, hy⟩ := hφ ((1 : Colim A f) ⊗ₜ[A i₀] c)
  obtain ⟨j₁, b₁, hb₁⟩ := exists_stage_tensor A f i₀ B₀ y
  let := modJ A f i₀ j₁
  set v : TensorProduct (A i₀) (A j₁.val) C₀ :=
    LinearMap.lTensor (A j₁.val) (φ₀.toLinearMap) b₁ with hv
  have hpushv : LinearMap.rTensor C₀ (ofColimLin A f i₀ j₁) v
      = (1 : Colim A f) ⊗ₜ[A i₀] c := by
    rw [hv, rTensor_lTensor_comm, hb₁]
    exact hy
  have hdiff : LinearMap.rTensor C₀ (ofColimLin A f i₀ j₁)
        (v - (1 : A j₁.val) ⊗ₜ[A i₀] c) = 0 := by
    rw [map_sub, hpushv, LinearMap.rTensor_tmul, ofColimLin_apply, map_one, sub_self]
  obtain ⟨k, hjk, hk0⟩ := exists_stage_rTensor_eq_zero A f i₀ C₀ j₁
    (v - (1 : A j₁.val) ⊗ₜ[A i₀] c) hdiff
  let := modJ A f i₀ k
  rw [map_sub, sub_eq_zero, LinearMap.rTensor_tmul, gJ_apply, map_one] at hk0
  exact ⟨k, LinearMap.rTensor B₀ (gJ A f i₀ j₁ k hjk) b₁,
    (rTensor_lTensor_comm _ _ b₁).symm.trans hk0⟩

omit [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
open scoped Classical in
/-- If `(1 : A j.val) ⊗ c` is in the image of `φ_j`, then for any larger stage `k`
the element `(1 : A k.val) ⊗ c` is in the image of `φ_k`. -/
lemma mem_range_mono {j k : {i : ι // i₀ ≤ i}} (hjk : j ≤ k) (c : C₀)
    (hj : letI := (f i₀ j.val j.property).toAlgebra
      (1 : A j.val) ⊗ₜ[A i₀] c ∈ Set.range (phiAt A f i₀ B₀ C₀ φ₀ j.val j.property)) :
    letI := (f i₀ k.val k.property).toAlgebra
    (1 : A k.val) ⊗ₜ[A i₀] c ∈ Set.range (phiAt A f i₀ B₀ C₀ φ₀ k.val k.property) := by
  classical
  let := modJ A f i₀ j
  let := modJ A f i₀ k
  obtain ⟨b, hb⟩ := hj
  refine ⟨LinearMap.rTensor B₀ (gJ A f i₀ j k hjk) b, ?_⟩
  have hnatT :
      (LinearMap.rTensor C₀ (gJ A f i₀ j k hjk)).comp
          (LinearMap.lTensor (A j.val) (φ₀.toLinearMap))
        = (LinearMap.lTensor (A k.val) (φ₀.toLinearMap)).comp
            (LinearMap.rTensor B₀ (gJ A f i₀ j k hjk)) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hφj_eq : ⇑(phiAt A f i₀ B₀ C₀ φ₀ j.val j.property) =
      ⇑(LinearMap.lTensor (A j.val) (φ₀.toLinearMap)) := rfl
  have hφk_eq : ⇑(phiAt A f i₀ B₀ C₀ φ₀ k.val k.property) =
      ⇑(LinearMap.lTensor (A k.val) (φ₀.toLinearMap)) := rfl
  rw [hφk_eq]
  have hkey := LinearMap.congr_fun hnatT b
  simp only [LinearMap.comp_apply] at hkey
  rw [← hkey]
  rw [hφj_eq] at hb
  rw [hb, LinearMap.rTensor_tmul, gJ_apply, map_one]

/-- If `φ₀` is of finite type and the colimit base change `φ = phiColim` is surjective, then
there is a stage `j ≥ i₀` at which the base change `φ_j = phiAt … j` is surjective. -/
lemma exists_surjective_phiAt_of_surjective
    (hft : (φ₀ : B₀ →+* C₀).FiniteType)
    (hφ : Function.Surjective (phiColim A f i₀ B₀ C₀ φ₀)) :
    ∃ j : ι, ∃ h : i₀ ≤ j, Function.Surjective (phiAt A f i₀ B₀ C₀ φ₀ j h) := by
  classical
  let : Algebra B₀ C₀ := (φ₀ : B₀ →+* C₀).toAlgebra
  have hC₀ft : Algebra.FiniteType B₀ C₀ := hft
  have hst : IsScalarTower (A i₀) B₀ C₀ :=
    IsScalarTower.of_algebraMap_eq (fun r => (φ₀.commutes r).symm)
  obtain ⟨t, ht_fin, ht⟩ := Subalgebra.fg_def.mp (Algebra.FiniteType.out (R := B₀) (A := C₀))
  have hgen : Algebra.adjoin (A i₀) (Set.range (φ₀ : B₀ → C₀) ∪ t) = ⊤ := by
    have h := Algebra.adjoin_eq_adjoin_union (A i₀) (Set.univ : Set B₀) t
      (by simp [Algebra.adjoin_univ])
    rw [ht] at h
    rw [Subalgebra.restrictScalars_top] at h
    have himg : (⇑(algebraMap B₀ C₀)) '' Set.univ = Set.range (φ₀ : B₀ → C₀) := by
      rw [Set.image_univ]; rfl
    rw [himg] at h
    exact h.symm
  have hstage : ∀ c : C₀, c ∈ t → ∃ (j : {i : ι // i₀ ≤ i}),
      let := (f i₀ j.val j.property).toAlgebra
      (1 : A j.val) ⊗ₜ[A i₀] c ∈ Set.range (phiAt A f i₀ B₀ C₀ φ₀ j.val j.property) :=
    fun c _ => exists_tmul_mem_range_phiAt A f i₀ B₀ C₀ φ₀ hφ c
  choose jc hjc using hstage
  set jc' : C₀ → {i : ι // i₀ ≤ i} :=
    fun c => if h : c ∈ t then jc c h else ⟨i₀, le_refl i₀⟩ with hjc'
  set tf := ht_fin.toFinset with htf
  obtain ⟨K, hK⟩ := Finset.exists_le (α := {i : ι // i₀ ≤ i})
    (insert ⟨i₀, le_refl i₀⟩ (tf.image jc'))
  let : Algebra (A i₀) (A K.val) := (f i₀ K.val K.property).toAlgebra
  refine ⟨K.val, K.property, ?_⟩
  rw [← AlgHom.range_eq_top]
  set R := (phiAt A f i₀ B₀ C₀ φ₀ K.val K.property).range with hR
  set D := R.comap (Algebra.TensorProduct.includeRight : C₀ →ₐ[A i₀] _) with hD
  have hmemD : ∀ c : C₀, c ∈ D ↔ (1 : A K.val) ⊗ₜ[A i₀] c ∈ R := by
    intro c
    rw [hD, Subalgebra.mem_comap, Algebra.TensorProduct.includeRight_apply]
  have hDrange : Set.range (φ₀ : B₀ → C₀) ⊆ (D : Set C₀) := by
    rintro _ ⟨b, rfl⟩
    rw [SetLike.mem_coe, hmemD]
    exact ⟨(1 : A K.val) ⊗ₜ[A i₀] b, by
      show (phiAt A f i₀ B₀ C₀ φ₀ K.val K.property) ((1 : A K.val) ⊗ₜ[A i₀] b) = _
      rfl⟩
  have hDt : t ⊆ (D : Set C₀) := by
    intro c hc
    rw [SetLike.mem_coe, hmemD]
    have hjcc := hjc c hc
    have hjc'eq : jc' c = jc c hc := by rw [hjc']; exact dite_eq_left hc
    have hle : jc c hc ≤ K := by
      have : jc' c ≤ K := by
        refine hK _ ?_
        refine Finset.mem_insert_of_mem ?_
        exact Finset.mem_image.mpr ⟨c, by rw [htf, Set.Finite.mem_toFinset]; exact hc, rfl⟩
      rwa [hjc'eq] at this
    exact mem_range_mono A f i₀ B₀ C₀ φ₀ hle c hjcc
  have hDtop : D = ⊤ := by
    rw [← top_le_iff, ← hgen, Algebra.adjoin_le_iff, Set.union_subset_iff]
    exact ⟨hDrange, hDt⟩
  rw [eq_top_iff, ← Algebra.TensorProduct.adjoin_tmul_eq_top, Algebra.adjoin_le_iff]
  rintro x ⟨a, c, rfl⟩
  have hac : (a ⊗ₜ[A i₀] c : TensorProduct (A i₀) (A K.val) C₀)
      = (a ⊗ₜ[A i₀] (1 : C₀)) * ((1 : A K.val) ⊗ₜ[A i₀] c) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [SetLike.mem_coe, hac]
  refine Subalgebra.mul_mem _ ?_ ?_
  · refine ⟨a ⊗ₜ[A i₀] (1 : B₀), ?_⟩
    show (phiAt A f i₀ B₀ C₀ φ₀ K.val K.property) (a ⊗ₜ[A i₀] (1 : B₀)) = a ⊗ₜ[A i₀] (1 : C₀)
    show (LinearMap.lTensor (A K.val) (φ₀.toLinearMap)) (a ⊗ₜ[A i₀] (1 : B₀))
      = a ⊗ₜ[A i₀] (1 : C₀)
    rw [LinearMap.lTensor_tmul]
    show a ⊗ₜ[A i₀] (φ₀ (1 : B₀)) = a ⊗ₜ[A i₀] (1 : C₀)
    rw [map_one]
  · have : c ∈ D := by rw [hDtop]; exact Algebra.mem_top
    rwa [hmemD] at this

omit [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
/-- If `φ_j = phiAt … j` is surjective and `j ≤ k`, then `φ_k = phiAt … k` is surjective. -/
lemma surjective_phiAt_of_le
    {j k : ι} (hj : i₀ ≤ j) (hk : i₀ ≤ k) (hjk : j ≤ k)
    (hsj : Function.Surjective (phiAt A f i₀ B₀ C₀ φ₀ j hj)) :
    Function.Surjective (phiAt A f i₀ B₀ C₀ φ₀ k hk) := by
  let : Algebra (A i₀) (A j) := (f i₀ j hj).toAlgebra
  let : Algebra (A i₀) (A k) := (f i₀ k hk).toAlgebra
  let : Algebra (A j) (A k) := (f j k hjk).toAlgebra
  have : IsScalarTower (A i₀) (A j) (A k) := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    show (f i₀ k hk) x = (f j k hjk) ((f i₀ j hj) x)
    exact (DirectedSystem.map_map (F := A) (f := fun i j h => (f i j h : A i → A j))
      hj hjk x).symm
  have hk_eq : ⇑(phiAt A f i₀ B₀ C₀ φ₀ k hk) =
      ⇑(LinearMap.lTensor (A k) (φ₀.toLinearMap)) := rfl
  have hj_eq : ⇑(phiAt A f i₀ B₀ C₀ φ₀ j hj) =
      ⇑(LinearMap.lTensor (A j) (φ₀.toLinearMap)) := rfl
  rw [hk_eq]
  rw [hj_eq] at hsj
  have hnat := TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange
    (A i₀) (A j) (A k) (M := A k) (N := B₀) (Q := C₀) (φ₀.toLinearMap)
  have hinner : ⇑(TensorProduct.AlgebraTensorModule.lTensor (A j) (A j) (φ₀.toLinearMap)) =
      ⇑(LinearMap.lTensor (A j) (φ₀.toLinearMap)) :=
    TensorProduct.AlgebraTensorModule.coe_lTensor (φ₀.toLinearMap)
  have hsj' : Function.Surjective
      ⇑(TensorProduct.AlgebraTensorModule.lTensor (A j) (A j) (φ₀.toLinearMap)) := by
    rwa [hinner]
  have hbase : Function.Surjective
      ⇑(TensorProduct.AlgebraTensorModule.lTensor (A k) (A k)
        (TensorProduct.AlgebraTensorModule.lTensor (A j) (A j) (φ₀.toLinearMap))) := by
    rw [TensorProduct.AlgebraTensorModule.coe_lTensor]
    exact LinearMap.lTensor_surjective (A k) hsj'
  have hRHS : Function.Surjective
      ⇑((TensorProduct.AlgebraTensorModule.cancelBaseChange (A i₀) (A j) (A k) (A k)
          C₀).toLinearMap ∘ₗ
        TensorProduct.AlgebraTensorModule.lTensor (A k) (A k)
          (TensorProduct.AlgebraTensorModule.lTensor (A j) (A j) (φ₀.toLinearMap))) := by
    rw [LinearMap.coe_comp]
    exact (TensorProduct.AlgebraTensorModule.cancelBaseChange
      (A i₀) (A j) (A k) (A k) C₀).surjective.comp hbase
  rw [← hnat] at hRHS
  rw [LinearMap.coe_comp] at hRHS
  have hLHS := Function.Surjective.of_comp hRHS
  rwa [TensorProduct.AlgebraTensorModule.coe_lTensor] at hLHS

omit [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] [DirectedSystem A fun i j h ↦ ⇑(f i j h)] in
/-- If the colimit base change `phiColim` is injective, every element `x` of the kernel of
the finite-stage base change `φ_{j₀}` maps to `0` in `Colim ⊗ B₀` under the
structure-map base change `rTensor B₀ (of j₀)`. -/
lemma rTensor_colim_ker_phiAt_eq_zero
    (h_inj : Function.Injective (phiColim A f i₀ B₀ C₀ φ₀))
    {j₀ : ι} (hj₀ : i₀ ≤ j₀) :
    letI : Algebra (A i₀) (A j₀) := (f i₀ j₀ hj₀).toAlgebra
    haveI : IsScalarTower (A i₀) (A j₀) (Colim A f) :=
      IsScalarTower.of_algebraMap_eq (fun x =>
        (Ring.DirectLimit.of_f (G := A)
          (f := fun i j h => (f i j h : A i → A j)) hj₀ x).symm)
    ∀ x ∈ RingHom.ker (phiAt A f i₀ B₀ C₀ φ₀ j₀ hj₀).toRingHom,
      LinearMap.rTensor B₀
        (IsScalarTower.toAlgHom (A i₀) (A j₀) (Colim A f)).toLinearMap x = 0 := by
  let : Algebra (A i₀) (A j₀) := (f i₀ j₀ hj₀).toAlgebra
  have : IsScalarTower (A i₀) (A j₀) (Colim A f) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (Ring.DirectLimit.of_f (G := A)
        (f := fun i j h => (f i j h : A i → A j)) hj₀ x).symm)
  intro x hx
  set ofL := (IsScalarTower.toAlgHom (A i₀) (A j₀) (Colim A f)).toLinearMap with hofL
  have hΦ_eq : ⇑(phiColim A f i₀ B₀ C₀ φ₀) =
      ⇑(LinearMap.lTensor (Colim A f) (φ₀.toLinearMap)) := rfl
  have hψ_eq : ⇑(phiAt A f i₀ B₀ C₀ φ₀ j₀ hj₀) =
      ⇑(LinearMap.lTensor (A j₀) (φ₀.toLinearMap)) := rfl
  rw [RingHom.mem_ker] at hx
  have hψx : (LinearMap.lTensor (A j₀) (φ₀.toLinearMap)) x = 0 := by
    have : (phiAt A f i₀ B₀ C₀ φ₀ j₀ hj₀) x = 0 := hx
    rwa [hψ_eq] at this
  have hnat :
      (LinearMap.lTensor (Colim A f) (φ₀.toLinearMap)).comp
          (LinearMap.rTensor B₀ ofL)
        = (LinearMap.rTensor C₀ ofL).comp
            (LinearMap.lTensor (A j₀) (φ₀.toLinearMap)) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have key : (LinearMap.lTensor (Colim A f) (φ₀.toLinearMap))
        (LinearMap.rTensor B₀ ofL x)
      = (LinearMap.rTensor C₀ ofL) ((LinearMap.lTensor (A j₀) (φ₀.toLinearMap)) x) := by
    have h := LinearMap.congr_fun hnat x
    simpa only [LinearMap.comp_apply] using h
  have hΦzero : (phiColim A f i₀ B₀ C₀ φ₀) (LinearMap.rTensor B₀ ofL x) = 0 := by
    rw [hΦ_eq, key, hψx, map_zero]
  have : (phiColim A f i₀ B₀ C₀ φ₀) (LinearMap.rTensor B₀ ofL x)
      = (phiColim A f i₀ B₀ C₀ φ₀) 0 := by rw [hΦzero, map_zero]
  exact h_inj this

/-- If the colimit base change `φ = phiColim` is injective and the kernel
`K = ker φ_{j₀}` is finitely generated, then there is a finite stage `i ≥ j₀` at
which the transition map `A_{j₀} ⊗ B₀ → A_i ⊗ B₀` (the base change of the
transition ring map `A_{j₀} → A_i`) annihilates every element of `K`. -/
lemma exists_rTensor_eq_zero_of_mem_ker_phiAt
    (h_inj : Function.Injective (phiColim A f i₀ B₀ C₀ φ₀))
    {j₀ : ι} (hj₀ : i₀ ≤ j₀)
    (hKfg :
      letI : Algebra (A i₀) (A j₀) := (f i₀ j₀ hj₀).toAlgebra
      (RingHom.ker (phiAt A f i₀ B₀ C₀ φ₀ j₀ hj₀).toRingHom).FG) :
    ∃ i : ι, ∃ hj₀i : j₀ ≤ i,
      letI : Algebra (A i₀) (A j₀) := (f i₀ j₀ hj₀).toAlgebra
      letI : Algebra (A i₀) (A i) := (f i₀ i (le_trans hj₀ hj₀i)).toAlgebra
      letI : Algebra (A j₀) (A i) := (f j₀ i hj₀i).toAlgebra
      haveI : IsScalarTower (A i₀) (A j₀) (A i) :=
        IsScalarTower.of_algebraMap_eq (fun x =>
          (DirectedSystem.map_map (F := A) (f := fun i j h => (f i j h : A i → A j))
            hj₀ hj₀i x).symm)
      ∀ x ∈ RingHom.ker (phiAt A f i₀ B₀ C₀ φ₀ j₀ hj₀).toRingHom,
        LinearMap.rTensor B₀
          (IsScalarTower.toAlgHom (A i₀) (A j₀) (A i)).toLinearMap x = 0 := by
  classical
  let : Algebra (A i₀) (A j₀) := (f i₀ j₀ hj₀).toAlgebra
  set j₀J : {i : ι // i₀ ≤ i} := ⟨j₀, hj₀⟩ with hj₀J
  have : IsScalarTower (A i₀) (A j₀) (Colim A f) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (Ring.DirectLimit.of_f (G := A)
        (f := fun i j h => (f i j h : A i → A j)) hj₀ x).symm)
  have hstar := rTensor_colim_ker_phiAt_eq_zero A f i₀ B₀ C₀ φ₀ h_inj hj₀
  have hsingle : ∀ x ∈ RingHom.ker (phiAt A f i₀ B₀ C₀ φ₀ j₀ hj₀).toRingHom,
      ∃ (k : {i : ι // i₀ ≤ i}) (hjk : j₀J ≤ k),
        let := modJ A f i₀ k
        LinearMap.rTensor B₀ (gJ A f i₀ j₀J k hjk) x = 0 :=
    fun x hx => exists_stage_rTensor_eq_zero A f i₀ B₀ j₀J x (hstar x hx)
  obtain ⟨s, hs⟩ := hKfg
  have hmem : ∀ g ∈ s, g ∈ RingHom.ker (phiAt A f i₀ B₀ C₀ φ₀ j₀ hj₀).toRingHom := by
    intro g hg
    rw [← hs]
    exact Ideal.subset_span hg
  choose kf hkf_le hkf_zero using fun g (hg : g ∈ s) => hsingle g (hmem g hg)
  set kf' : (TensorProduct (A i₀) (A j₀) B₀) → {i : ι // i₀ ≤ i} :=
    fun g => if h : g ∈ s then kf g h else j₀J with hkf'
  obtain ⟨K, hK⟩ := Finset.exists_le (α := {i : ι // i₀ ≤ i})
    (insert j₀J (s.image kf'))
  have hj₀K : j₀J ≤ K := hK j₀J (Finset.mem_insert_self _ _)
  refine ⟨K.val, hj₀K, ?_⟩
  let : Algebra (A i₀) (A K.val) := (f i₀ K.val (le_trans hj₀ hj₀K)).toAlgebra
  let : Algebra (A j₀) (A K.val) := (f j₀ K.val hj₀K).toAlgebra
  have : IsScalarTower (A i₀) (A j₀) (A K.val) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (DirectedSystem.map_map (F := A) (f := fun i j h => (f i j h : A i → A j))
        hj₀ hj₀K x).symm)
  set T : TensorProduct (A i₀) (A j₀) B₀ →ₐ[A i₀] TensorProduct (A i₀) (A K.val) B₀ :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom (A i₀) (A j₀) (A K.val))
      (AlgHom.id (A i₀) B₀) with hT
  have hTlin : LinearMap.rTensor B₀
      (IsScalarTower.toAlgHom (A i₀) (A j₀) (A K.val)).toLinearMap = T.toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    rfl
  have hTfun : ⇑(LinearMap.rTensor B₀
      (IsScalarTower.toAlgHom (A i₀) (A j₀) (A K.val)).toLinearMap) = ⇑T := by
    rw [hTlin]; rfl
  suffices hsub : RingHom.ker (phiAt A f i₀ B₀ C₀ φ₀ j₀ hj₀).toRingHom ≤
      RingHom.ker T.toRingHom by
    intro x hx
    rw [hTfun]
    exact hsub hx
  rw [← hs, Ideal.span_le]
  intro g hg
  rw [SetLike.mem_coe, RingHom.mem_ker]
  let := modJ A f i₀ (kf g hg)
  have hg0 : LinearMap.rTensor B₀ (gJ A f i₀ j₀J (kf g hg) (hkf_le g hg)) g = 0 :=
    hkf_zero g hg
  have hkf'eq : kf' g = kf g hg := by rw [hkf']; exact dite_eq_left hg
  have hkfK : kf g hg ≤ K := by
    have : kf' g ≤ K :=
      hK _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨g, hg, rfl⟩))
    rwa [hkf'eq] at this
  have hcocyc : LinearMap.rTensor B₀ (gJ A f i₀ j₀J K hj₀K)
      = (LinearMap.rTensor B₀ (gJ A f i₀ (kf g hg) K hkfK)) ∘ₗ
        (LinearMap.rTensor B₀ (gJ A f i₀ j₀J (kf g hg) (hkf_le g hg))) := by
    rw [← LinearMap.rTensor_comp]
    congr 1
    refine LinearMap.ext fun a => ?_
    show f j₀ K.val hj₀K a
        = f (kf g hg).val K.val hkfK (f j₀ (kf g hg).val (hkf_le g hg) a)
    exact (DirectedSystem.map_map (F := A) (f := fun i j h => (f i j h : A i → A j))
      (hkf_le g hg) hkfK a).symm
  have hgg : (IsScalarTower.toAlgHom (A i₀) (A j₀) (A K.val)).toLinearMap
      = gJ A f i₀ j₀J K hj₀K := by
    apply LinearMap.ext; intro a; rfl
  have hTg : T.toRingHom g
      = LinearMap.rTensor B₀ (gJ A f i₀ j₀J K hj₀K) g := by
    show T g = _
    rw [← hTfun, hgg]
  rw [hTg, hcocyc]
  simp only [LinearMap.coe_comp, Function.comp_apply, hg0, map_zero]

/-- If `φ₀` is of finite presentation, the colimit base change `φ` is injective, and
`φ_{j₀} = phiAt … j₀` is surjective at some stage `j₀ ≥ i₀`, then there is a stage `i ≥ j₀` at
which `φ_i = phiAt … i` is injective. -/
lemma exists_injective_phiAt_of_injective
    (hfp : (φ₀ : B₀ →+* C₀).FinitePresentation)
    (hφ : Function.Injective (phiColim A f i₀ B₀ C₀ φ₀))
    {j₀ : ι} (hj₀ : i₀ ≤ j₀) (hsurj : Function.Surjective (phiAt A f i₀ B₀ C₀ φ₀ j₀ hj₀)) :
    ∃ i : ι, ∃ h : i₀ ≤ i, j₀ ≤ i ∧ Function.Injective (phiAt A f i₀ B₀ C₀ φ₀ i h) := by
  classical
  let : Algebra (A i₀) (A j₀) := (f i₀ j₀ hj₀).toAlgebra
  have hKfg : (RingHom.ker (phiAt A f i₀ B₀ C₀ φ₀ j₀ hj₀).toRingHom).FG := by
    set ψ := phiAt A f i₀ B₀ C₀ φ₀ j₀ hj₀ with hψdef
    let : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    have hC₀fp : Algebra.FinitePresentation B₀ C₀ := hfp
    let : Algebra (TensorProduct (A i₀) (A j₀) B₀) (TensorProduct (A i₀) (A j₀) C₀) :=
      ψ.toRingHom.toAlgebra
    have hC'fp : Algebra.FinitePresentation
        (TensorProduct (A i₀) (A j₀) B₀) (TensorProduct (A i₀) (A j₀) C₀) := by
      have hψ : ψ = Algebra.TensorProduct.lTensor (A j₀) φ₀ := rfl
      let iB : Algebra B₀ (TensorProduct (A i₀) (A j₀) B₀) :=
        Algebra.TensorProduct.rightAlgebra
      let iC : Algebra C₀ (TensorProduct (A i₀) (A j₀) C₀) :=
        Algebra.TensorProduct.rightAlgebra
      have hbc : Algebra.FinitePresentation (TensorProduct (A i₀) (A j₀) B₀)
          ((TensorProduct (A i₀) (A j₀) B₀) ⊗[B₀] C₀) :=
        Algebra.FinitePresentation.baseChange (TensorProduct (A i₀) (A j₀) B₀)
      set e := Algebra.IsPushout.cancelBaseChangeAlg (A i₀) (A j₀) B₀
        (TensorProduct (A i₀) (A j₀) B₀) C₀ with he
      have key : ∀ x : (TensorProduct (A i₀) (A j₀) B₀),
          e (algebraMap (TensorProduct (A i₀) (A j₀) B₀)
              ((TensorProduct (A i₀) (A j₀) B₀) ⊗[B₀] C₀) x)
            = algebraMap (TensorProduct (A i₀) (A j₀) B₀)
              (TensorProduct (A i₀) (A j₀) C₀) x := by
        intro x
        have ha : algebraMap (TensorProduct (A i₀) (A j₀) B₀)
            ((TensorProduct (A i₀) (A j₀) B₀) ⊗[B₀] C₀) x = x ⊗ₜ[B₀] (1 : C₀) := rfl
        have hb : algebraMap (TensorProduct (A i₀) (A j₀) B₀)
            (TensorProduct (A i₀) (A j₀) C₀) x = ψ x := rfl
        rw [ha, hb]
        apply e.symm.injective
        rw [AlgEquiv.symm_apply_apply, hψ]
        clear ha hb
        induction x with
        | add a b iha ihb => simp only [add_tmul, map_add, iha, ihb]
        | tmul s b =>
            rw [Algebra.TensorProduct.map_tmul]
            simp only [AlgHom.coe_id, id_eq]
            rw [he, Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul]
            have h1 : (algebraMap (A j₀) (TensorProduct (A i₀) (A j₀) B₀)) s
                = s ⊗ₜ[A i₀] (1 : B₀) := rfl
            rw [h1]
            have h2 : (s ⊗ₜ[A i₀] b : TensorProduct (A i₀) (A j₀) B₀)
                = b • (s ⊗ₜ[A i₀] (1 : B₀)) := by
              rw [Algebra.smul_def]
              show s ⊗ₜ[A i₀] b = (1 ⊗ₜ[A i₀] b) * (s ⊗ₜ[A i₀] 1)
              rw [Algebra.TensorProduct.tmul_mul_tmul]; simp
            rw [h2, TensorProduct.smul_tmul]
            congr 1
            show b • (1 : C₀) = φ₀ b
            rw [Algebra.smul_def, mul_one]; rfl
      let e' : ((TensorProduct (A i₀) (A j₀) B₀) ⊗[B₀] C₀)
          ≃ₐ[(TensorProduct (A i₀) (A j₀) B₀)] (TensorProduct (A i₀) (A j₀) C₀) :=
        AlgEquiv.ofRingEquiv (f := e.toRingEquiv) key
      exact @Algebra.FinitePresentation.equiv (TensorProduct (A i₀) (A j₀) B₀)
        ((TensorProduct (A i₀) (A j₀) B₀) ⊗[B₀] C₀) (TensorProduct (A i₀) (A j₀) C₀)
        _ _ _ _ _ hbc e'
    have hB'fp : Algebra.FinitePresentation
        (TensorProduct (A i₀) (A j₀) B₀) (TensorProduct (A i₀) (A j₀) B₀) :=
      Algebra.FinitePresentation.self _
    have hsurj' : Function.Surjective
        ⇑(Algebra.ofId (TensorProduct (A i₀) (A j₀) B₀) (TensorProduct (A i₀) (A j₀) C₀)) :=
      hsurj
    have hker := Algebra.FinitePresentation.ker_fG_of_surjective
      (Algebra.ofId (TensorProduct (A i₀) (A j₀) B₀) (TensorProduct (A i₀) (A j₀) C₀)) hsurj'
    exact hker
  obtain ⟨i, hj₀i, hkill⟩ :
      ∃ i : ι, ∃ hj₀i : j₀ ≤ i,
        let : Algebra (A i₀) (A i) := (f i₀ i (le_trans hj₀ hj₀i)).toAlgebra
        let : Algebra (A j₀) (A i) := (f j₀ i hj₀i).toAlgebra
        have : IsScalarTower (A i₀) (A j₀) (A i) :=
          IsScalarTower.of_algebraMap_eq (fun x =>
            (DirectedSystem.map_map (F := A) (f := fun i j h => (f i j h : A i → A j))
              hj₀ hj₀i x).symm)
        ∀ x ∈ RingHom.ker (phiAt A f i₀ B₀ C₀ φ₀ j₀ hj₀).toRingHom,
          LinearMap.rTensor B₀
            (IsScalarTower.toAlgHom (A i₀) (A j₀) (A i)).toLinearMap x = 0 :=
    exists_rTensor_eq_zero_of_mem_ker_phiAt A f i₀ B₀ C₀ φ₀ hφ hj₀ hKfg
  refine ⟨i, le_trans hj₀ hj₀i, hj₀i, ?_⟩
  let : Algebra (A i₀) (A i) := (f i₀ i (le_trans hj₀ hj₀i)).toAlgebra
  let : Algebra (A j₀) (A i) := (f j₀ i hj₀i).toAlgebra
  have : IsScalarTower (A i₀) (A j₀) (A i) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (DirectedSystem.map_map (F := A) (f := fun i j h => (f i j h : A i → A j))
        hj₀ hj₀i x).symm)
  have hi_eq : ⇑(phiAt A f i₀ B₀ C₀ φ₀ i (le_trans hj₀ hj₀i)) =
      ⇑(LinearMap.lTensor (A i) (φ₀.toLinearMap)) := rfl
  rw [hi_eq]
  have hnat := TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange
    (A i₀) (A j₀) (A i) (M := A i) (N := B₀) (Q := C₀) (φ₀.toLinearMap)
  set ψ := TensorProduct.AlgebraTensorModule.lTensor (A j₀) (A j₀) (φ₀.toLinearMap) with hψ
  have hψfun : ⇑ψ = ⇑(LinearMap.lTensor (A j₀) (φ₀.toLinearMap)) :=
    TensorProduct.AlgebraTensorModule.coe_lTensor (φ₀.toLinearMap)
  have hsurjψ : Function.Surjective ⇑ψ := by
    rw [hψfun]
    have : ⇑(phiAt A f i₀ B₀ C₀ φ₀ j₀ hj₀) = ⇑(LinearMap.lTensor (A j₀) (φ₀.toLinearMap)) := rfl
    rwa [← this]
  have hinner_inj : Function.Injective ⇑(LinearMap.lTensor (A i) ψ) := by
    have hex := lTensor_exact (A i) (LinearMap.exact_subtype_ker_map ψ) hsurjψ
    have hkereq := hex.linearMap_ker_eq
    rw [← LinearMap.ker_eq_bot, hkereq, LinearMap.range_eq_bot]
    apply TensorProduct.ext'
    intro a k
    have hcbc :
        (TensorProduct.AlgebraTensorModule.cancelBaseChange (A i₀) (A j₀) (A i) (A i) B₀)
          ((1 : A i) ⊗ₜ[A j₀] (k.val))
        = LinearMap.rTensor B₀
            (IsScalarTower.toAlgHom (A i₀) (A j₀) (A i)).toLinearMap (k.val) := by
      induction k.val using TensorProduct.inductionOn with
      | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy]
      | tmul s b =>
          rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
            LinearMap.rTensor_tmul]
          show (s • (1 : A i)) ⊗ₜ[A i₀] b = (IsScalarTower.toAlgHom (A i₀) (A j₀) (A i)) s ⊗ₜ[A
              i₀] b
          rw [Algebra.smul_def, mul_one]
          rfl
    have hkmem : (k.val) ∈ RingHom.ker (phiAt A f i₀ B₀ C₀ φ₀ j₀ hj₀).toRingHom := by
      rw [RingHom.mem_ker]
      show (phiAt A f i₀ B₀ C₀ φ₀ j₀ hj₀) (k.val) = 0
      have : ⇑(phiAt A f i₀ B₀ C₀ φ₀ j₀ hj₀) = ⇑(LinearMap.lTensor (A j₀) (φ₀.toLinearMap)) := rfl
      rw [this, ← hψfun]
      exact k.property
    have h1k : ((1 : A i) ⊗ₜ[A j₀] (k.val)
        : TensorProduct (A j₀) (A i) (TensorProduct (A i₀) (A j₀) B₀)) = 0 := by
      apply (TensorProduct.AlgebraTensorModule.cancelBaseChange (A i₀) (A j₀) (A i) (A i)
          B₀).injective
      rw [map_zero, hcbc]
      exact hkill (k.val) hkmem
    show LinearMap.lTensor (A i) (LinearMap.ker ψ).subtype (a ⊗ₜ[A j₀] k) = 0
    rw [LinearMap.lTensor_tmul]
    show (a ⊗ₜ[A j₀] (k.val)
        : TensorProduct (A j₀) (A i) (TensorProduct (A i₀) (A j₀) B₀)) = 0
    rw [show (a ⊗ₜ[A j₀] (k.val)
        : TensorProduct (A j₀) (A i) (TensorProduct (A i₀) (A j₀) B₀))
        = a • ((1 : A i) ⊗ₜ[A j₀] (k.val)) by rw [smul_tmul', smul_eq_mul, mul_one]]
    rw [h1k, smul_zero]
  rw [← TensorProduct.AlgebraTensorModule.coe_lTensor (A := A i) (M := A i) (φ₀.toLinearMap)]
  have hRHS : Function.Injective
      ⇑((TensorProduct.AlgebraTensorModule.cancelBaseChange (A i₀) (A j₀) (A i) (A i)
          C₀).toLinearMap ∘ₗ
        TensorProduct.AlgebraTensorModule.lTensor (A i) (A i) ψ) := by
    rw [LinearMap.coe_comp]
    refine (TensorProduct.AlgebraTensorModule.cancelBaseChange
      (A i₀) (A j₀) (A i) (A i) C₀).injective.comp ?_
    rw [TensorProduct.AlgebraTensorModule.coe_lTensor]
    exact hinner_inj
  rw [← hnat] at hRHS
  rw [LinearMap.coe_comp] at hRHS
  exact hRHS.of_comp_right
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (A i₀) (A j₀) (A i) (A i) B₀).surjective

/-- Let `A = colim_{i ∈ I} A_i` be a directed colimit of commutative rings, fix an index
`i₀ ∈ I`, and let `φ₀ : B₀ → C₀` be a map of `A i₀`-algebras. If the base-changed map
`φ : A ⊗_{A i₀} B₀ → A ⊗_{A i₀} C₀` is bijective and `φ₀` is of finite presentation, then there
exists an index `i ≥ i₀` such that the base-changed map
`φ_i : A_i ⊗_{A i₀} B₀ → A_i ⊗_{A i₀} C₀` is bijective. -/
@[stacks 0C32]
theorem isIso_of_finitePresentation_colim
    (hfp : (φ₀ : B₀ →+* C₀).FinitePresentation)
    (hφ : Function.Bijective (phiColim A f i₀ B₀ C₀ φ₀)) :
    ∃ i : ι, ∃ h : i₀ ≤ i, Function.Bijective (phiAt A f i₀ B₀ C₀ φ₀ i h) := by
  obtain ⟨j₁, hj₁, hsurj₁⟩ :=
    exists_surjective_phiAt_of_surjective A f i₀ B₀ C₀ φ₀
      (RingHom.FiniteType.of_finitePresentation hfp) hφ.surjective
  obtain ⟨i, hi, hj₁i, hinj⟩ :=
    exists_injective_phiAt_of_injective A f i₀ B₀ C₀ φ₀ hfp hφ.injective hj₁ hsurj₁
  have hsurj : Function.Surjective (phiAt A f i₀ B₀ C₀ φ₀ i hi) :=
    surjective_phiAt_of_le A f i₀ B₀ C₀ φ₀ hj₁ hi hj₁i hsurj₁
  exact ⟨i, hi, hinj, hsurj⟩

end Stacks.DirectLimit.FinitePresentationDescent

end
