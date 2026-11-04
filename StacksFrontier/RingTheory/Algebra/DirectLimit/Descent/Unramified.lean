module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Unramified.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent of unramifiedness to a finite stage of a directed colimit

Here `A = colim_i Aᵢ` is `Ring.DirectLimit`, the base stage is `O` with `A₀ := G O`, and for
`O ≤ i` the stage `G i` is an `A₀`-algebra via `f O i h`. The base changes are
`Φ = id_A ⊗ φ₀` and `Φᵢ = id_{Aᵢ} ⊗ φ₀`. Unramified means `Algebra.Unramified`: formally
unramified and of finite type.

## Main results

* `Stacks.DirectLimit.UnramifiedDescent.colimit_unramified`: if `id_A ⊗ φ₀` is unramified and
  `φ₀` is of finite type, then some `id_{Aᵢ} ⊗ φ₀` is unramified.

## References

* [Stacks Project, Tag 0C4F](https://stacks.math.columbia.edu/tag/0C4F)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.DirectLimit.UnramifiedDescent

-- The index preorder is nonempty and directed; `G` is the family of rings and `f` the
-- transition ring homomorphisms forming a `DirectedSystem`.
variable {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
variable (G : ι → Type*) [∀ i, CommRing (G i)]
variable (f : (i j : ι) → i ≤ j → G i →+* G j)
variable [DirectedSystem G (fun i j h => f i j h)]

-- The distinguished base index `0 ∈ I`, written `O`, with `A_0 := G O`.
variable (O : ι)

-- `B₀` and `C₀` are commutative `A₀`-algebras and `φ₀` an `A₀`-algebra map.
variable (B₀ C₀ : Type*) [CommRing B₀] [CommRing C₀]
variable [Algebra (G O) B₀] [Algebra (G O) C₀]
variable (φ₀ : B₀ →ₐ[G O] C₀)

/-- The directed colimit `A = colim_i Aᵢ` of the system `G`. -/
abbrev A := Ring.DirectLimit G (fun i j h => f i j h)

/-- `A` is an `A₀ = G O`-algebra via the structure map `ι₀ = Ring.DirectLimit.of … O`. -/
noncomputable instance algA : Algebra (G O) (A G f) :=
  (Ring.DirectLimit.of G _ O).toAlgebra

/-- The base change of `φ₀` to the colimit: the `A`-algebra map
`Φ = id_A ⊗ φ₀ : A ⊗_{A₀} B₀ → A ⊗_{A₀} C₀`, characterized by `a ⊗ b ↦ a ⊗ φ₀ b`. -/
noncomputable def phiColim : (A G f) ⊗[G O] B₀ →ₐ[A G f] (A G f) ⊗[G O] C₀ :=
  Algebra.TensorProduct.map (AlgHom.id (A G f) (A G f)) φ₀

omit [IsDirected ι (· ≤ ·)] [Nonempty ι] [DirectedSystem G (fun i j h => f i j h)] in
/-- The map `Φ = id_A ⊗ φ₀` sends `a ⊗ b` to `a ⊗ φ₀ b`. -/
@[simp]
lemma phiColim_tmul (a : A G f) (b : B₀) :
    phiColim G f O B₀ C₀ φ₀ (a ⊗ₜ b) = a ⊗ₜ φ₀ b :=
  rfl

/-- For an `R`-algebra `S`, with `Φ_S = id_S ⊗ φ₀ : S ⊗[R] B₀ → S ⊗[R] C₀` giving
`S ⊗[R] C₀` its `(S ⊗[R] B₀)`-algebra structure, formal unramifiedness of `Φ_S` is
equivalent to the vanishing (as a subsingleton) of the base-changed module of
differentials `(S ⊗[R] C₀) ⊗[C₀] Ω[C₀⁄B₀]`, where `C₀` is a `B₀`-algebra via `φ₀`. -/
lemma formallyUnramified_baseChange_iff
    (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (B₀ C₀ : Type*) [CommRing B₀] [CommRing C₀] [Algebra R B₀] [Algebra R C₀]
    (φ₀ : B₀ →ₐ[R] C₀) :
    letI _ : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    letI φS : (S ⊗[R] B₀) →ₐ[S] (S ⊗[R] C₀) :=
      Algebra.TensorProduct.map (AlgHom.id S S) φ₀
    letI _ : Algebra (S ⊗[R] B₀) (S ⊗[R] C₀) := φS.toRingHom.toAlgebra
    letI _ : Algebra C₀ (S ⊗[R] C₀) :=
      (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := C₀)).toRingHom.toAlgebra
    (Algebra.FormallyUnramified (S ⊗[R] B₀) (S ⊗[R] C₀) ↔
      Subsingleton ((S ⊗[R] C₀) ⊗[C₀] (Ω[C₀⁄B₀]))) := by
  let algBC : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let φS : (S ⊗[R] B₀) →ₐ[S] (S ⊗[R] C₀) :=
    Algebra.TensorProduct.map (AlgHom.id S S) φ₀
  let algSBC : Algebra (S ⊗[R] B₀) (S ⊗[R] C₀) := φS.toRingHom.toAlgebra
  let algCSC : Algebra C₀ (S ⊗[R] C₀) :=
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := C₀)).toRingHom.toAlgebra
  have towerRBC : IsScalarTower R B₀ C₀ :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ₀.commutes x).symm)
  let algBSB : Algebra B₀ (S ⊗[R] B₀) :=
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := B₀)).toRingHom.toAlgebra
  let algBSC : Algebra B₀ (S ⊗[R] C₀) :=
    ((algebraMap C₀ (S ⊗[R] C₀)).comp (algebraMap B₀ C₀)).toAlgebra
  have tBCsc : IsScalarTower B₀ C₀ (S ⊗[R] C₀) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have tBSB : IsScalarTower B₀ (S ⊗[R] B₀) (S ⊗[R] C₀) := by
    apply IsScalarTower.of_algebraMap_eq
    intro b
    show (1 : S) ⊗ₜ[R] (φ₀ b) = φS ((1 : S) ⊗ₜ[R] b)
    simp [φS]
  have hCalg : Algebra C₀ ((S ⊗[R] B₀) ⊗[B₀] C₀) := Algebra.TensorProduct.rightAlgebra
  let g : ((S ⊗[R] B₀) ⊗[B₀] C₀) →ₐ[S ⊗[R] B₀] (S ⊗[R] C₀) :=
    Algebra.TensorProduct.lift (Algebra.ofId (S ⊗[R] B₀) (S ⊗[R] C₀))
      (IsScalarTower.toAlgHom B₀ C₀ (S ⊗[R] C₀)) (fun x y => Commute.all _ _)
  let fS : S →ₐ[R] ((S ⊗[R] B₀) ⊗[B₀] C₀) :=
    (Algebra.TensorProduct.includeLeft).comp
      (Algebra.TensorProduct.includeLeft (S := R) (R := R) (A := S) (B := B₀))
  let gC : C₀ →ₐ[R] ((S ⊗[R] B₀) ⊗[B₀] C₀) :=
    (Algebra.TensorProduct.includeRight).restrictScalars R
  let h : (S ⊗[R] C₀) →ₐ[R] ((S ⊗[R] B₀) ⊗[B₀] C₀) :=
    Algebra.TensorProduct.lift fS gC (fun x y => Commute.all _ _)
  have smulb : ∀ (s : S) (b : B₀), (b • (s ⊗ₜ[R] (1:B₀)) : S ⊗[R] B₀) = s ⊗ₜ[R] b := by
    intro s b
    rw [Algebra.smul_def]
    show ((1:S) ⊗ₜ[R] b) * (s ⊗ₜ[R] 1) = s ⊗ₜ[R] b
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have balance : ∀ (s : S) (b : B₀) (c : C₀),
      (((s ⊗ₜ[R] (1:B₀)) ⊗ₜ[B₀] ((φ₀ b) * c)) : (S ⊗[R] B₀) ⊗[B₀] C₀)
        = ((s ⊗ₜ[R] b) ⊗ₜ[B₀] c) := by
    intro s b c
    have hbc : (φ₀ b) * c = b • c := by rw [Algebra.smul_def]; rfl
    rw [hbc, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smulb]
  have gtmul : ∀ (a : S ⊗[R] B₀) (c : C₀), g (a ⊗ₜ[B₀] c) = φS a * ((1:S) ⊗ₜ[R] c) := by
    intro a c
    simp only [g, Algebra.TensorProduct.lift_tmul]
    rfl
  have hgh : ∀ z, g (h z) = z := by
    intro z
    induction z with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul x c =>
      show g (h (x ⊗ₜ[R] c)) = x ⊗ₜ[R] c
      have hh : h (x ⊗ₜ[R] c) = ((x ⊗ₜ[R] (1:B₀)) ⊗ₜ[B₀] c) := by
        simp only [h, Algebra.TensorProduct.lift_tmul, fS, gC, AlgHom.comp_apply,
          Algebra.TensorProduct.includeLeft_apply, AlgHom.restrictScalars_apply,
          Algebra.TensorProduct.includeRight_apply]
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [hh, gtmul]
      show φS (x ⊗ₜ[R] 1) * ((1:S) ⊗ₜ[R] c) = x ⊗ₜ[R] c
      simp only [φS, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, map_one,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have hhg : ∀ z, h (g z) = z := by
    intro z
    induction z with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul a c =>
      induction a with
      | zero => simp
      | add a₁ a₂ ha₁ ha₂ =>
        rw [TensorProduct.add_tmul, map_add, map_add, ha₁, ha₂, ← TensorProduct.add_tmul]
      | tmul s b =>
        show h (g ((s ⊗ₜ[R] b) ⊗ₜ[B₀] c)) = (s ⊗ₜ[R] b) ⊗ₜ[B₀] c
        rw [gtmul]
        show h (φS (s ⊗ₜ[R] b) * ((1:S) ⊗ₜ[R] c)) = (s ⊗ₜ[R] b) ⊗ₜ[B₀] c
        have hφ : φS (s ⊗ₜ[R] b) = s ⊗ₜ[R] (φ₀ b) := by
          simp only [φS, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
        rw [hφ, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        rw [show h (s ⊗ₜ[R] ((φ₀ b) * c)) = fS s * gC ((φ₀ b) * c) from by
          simp only [h, Algebra.TensorProduct.lift_tmul]]
        simp only [fS, gC, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
          AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [balance]
  let e : ((S ⊗[R] B₀) ⊗[B₀] C₀) ≃ₐ[S ⊗[R] B₀] (S ⊗[R] C₀) :=
    AlgEquiv.ofBijective g (Function.bijective_iff_has_inverse.mpr ⟨h, hhg, hgh⟩)
  have hpo : Algebra.IsPushout B₀ (S ⊗[R] B₀) C₀ (S ⊗[R] C₀) := by
    rw [Algebra.isPushout_iff]
    refine IsBaseChange.of_equiv e.toLinearEquiv ?_
    intro c
    have : e ((1 : S ⊗[R] B₀) ⊗ₜ[B₀] c) = g ((1 : S ⊗[R] B₀) ⊗ₜ[B₀] c) := rfl
    show e ((1 : S ⊗[R] B₀) ⊗ₜ[B₀] c) = (IsScalarTower.toAlgHom B₀ C₀ (S ⊗[R] C₀)).toLinearMap c
    rw [this, gtmul]
    show φS (1 : S ⊗[R] B₀) * ((1:S) ⊗ₜ[R] c) = algebraMap C₀ (S ⊗[R] C₀) c
    simp [φS]
    rfl
  let kE := KaehlerDifferential.tensorKaehlerEquiv B₀ (S ⊗[R] B₀) C₀ (S ⊗[R] C₀)
  rw [Algebra.formallyUnramified_iff (S ⊗[R] B₀) (S ⊗[R] C₀)]
  exact (kE.toEquiv.subsingleton_congr).symm

/-- If a `Module.DirectLimit` of `R`-modules `N i` is a subsingleton, and `hkill` makes `N i`
a subsingleton as soon as the images of a fixed finite set `s ⊆ N i₀` vanish there, then `N i`
is a subsingleton at some stage `i ≥ i₀`. -/
lemma generic_directLimit_descent'
    {R : Type*} [CommRing R]
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [DecidableEq ι]
    (N : ι → Type*) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (g : (i j : ι) → i ≤ j → N i →ₗ[R] N j)
    [DirectedSystem N (fun i j h => g i j h)]
    (hsub : Subsingleton (Module.DirectLimit N (fun i j h => g i j h)))
    (i₀ : ι) (s : Finset (N i₀))
    (hkill : ∀ i, ∀ (hi : i₀ ≤ i),
      (∀ x ∈ s, (g i₀ i hi) x = 0) → Subsingleton (N i)) :
    ∃ i, ∃ (_ : i₀ ≤ i), Subsingleton (N i) := by
  classical
  have hstage : ∀ x ∈ s, ∃ j, ∃ (hij : i₀ ≤ j), g i₀ j hij x = 0 := by
    intro x hx
    have hzero : (Module.DirectLimit.of R ι N (fun i j h => g i j h) i₀) x = 0 :=
      Subsingleton.elim _ _
    exact Module.DirectLimit.of.zero_exact hzero
  choose J hJ hJ0 using hstage
  let T : Finset ι := s.attach.image (fun x => J x.val x.property)
  obtain ⟨ub, hub⟩ := Finset.exists_le T
  obtain ⟨i, hubi, hi₀i⟩ := directed_of (· ≤ ·) ub i₀
  refine ⟨i, hi₀i, ?_⟩
  apply hkill i hi₀i
  intro x hx
  have hJxi : J x hx ≤ i :=
    (hub _ (Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨x, hx⟩))).trans hubi
  have hcomp := DirectedSystem.map_map (F := N) (f := fun i j h => g i j h)
    (i := i₀) (j := J x hx) (k := i) (hJ x hx) hJxi x
  rw [hJ0 x hx, map_zero] at hcomp
  rw [← hcomp]

/-- If a `C₀`-module `M` is spanned by a finset `T` and every generator `1 ⊗ m` with `m ∈ T`
vanishes in `B ⊗[C₀] M` for a `C₀`-algebra `B`, then `B ⊗[C₀] M` is trivial. -/
lemma tensorBaseChange_subsingleton_of_gens_vanish
    (C₀ : Type*) [CommRing C₀]
    (B : Type*) [CommRing B] [Algebra C₀ B]
    (M : Type*) [AddCommGroup M] [Module C₀ M]
    (T : Finset M) (hspanM : Submodule.span C₀ (↑T : Set M) = ⊤)
    (hkill : ∀ m ∈ T, ((1 : B) ⊗ₜ[C₀] m : B ⊗[C₀] M) = 0) :
    Subsingleton (B ⊗[C₀] M) := by
  rw [subsingleton_iff_forall_eq 0]
  have hpure : ∀ (b : B) (m : M), (b ⊗ₜ[C₀] m : B ⊗[C₀] M) = 0 := by
    intro b m
    have hm : m ∈ Submodule.span C₀ (↑T : Set M) := hspanM ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem x hx =>
      have : (b ⊗ₜ[C₀] x : B ⊗[C₀] M) = b • ((1 : B) ⊗ₜ[C₀] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, hkill x hx, smul_zero]
    | zero => simp
    | add x y hx hy ihx ihy => rw [TensorProduct.tmul_add, ihx, ihy, add_zero]
    | smul c x hx ih => rw [TensorProduct.tmul_smul, ih, smul_zero]
  intro y
  induction y using TensorProduct.induction_on with
  | zero => rfl
  | tmul b m => exact hpure b m
  | add x z hx hz => rw [hx, hz, add_zero]

/-- A ring homomorphism commuting with the structure maps from `C` is `C`-linear. -/
private theorem map_smul_of_map_algebraMap {C P Q : Type*} [CommRing C] [CommRing P] [CommRing Q]
    [Algebra C P] [Algebra C Q] (F : P →+* Q) (hF : ∀ c, F (algebraMap C P c) = algebraMap C Q c)
    (c : C) (x : P) : F (c • x) = c • F x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, hF]

/-- For a finite `C₀`-module `M`, if the base change to the colimit `(A ⊗_R C₀) ⊗[C₀] M` is a
subsingleton, then so is `(G i ⊗_R C₀) ⊗[C₀] M` at some finite stage `i ≥ O`. -/
lemma colimit_baseChange_descent
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type*) [∀ i, CommRing (G i)]
    (f : (i j : ι) → i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h => f i j h)]
    (O : ι)
    (C₀ : Type*) [CommRing C₀]
    [Algebra (G O) C₀]
    (M : Type*) [AddCommGroup M] [Module C₀ M] [Module.Finite C₀ M]
    (hcolim :
      letI _ : Algebra C₀ ((Ring.DirectLimit G (fun i j h => f i j h)) ⊗[G O] C₀) :=
        (Algebra.TensorProduct.includeRight (R := G O)
          (A := Ring.DirectLimit G (fun i j h => f i j h)) (B := C₀)).toRingHom.toAlgebra
      Subsingleton (((Ring.DirectLimit G (fun i j h => f i j h)) ⊗[G O] C₀) ⊗[C₀] M)) :
    ∃ i, ∃ (hOi : O ≤ i),
      letI _ : Algebra (G O) (G i) := (f O i hOi).toAlgebra
      letI _ : Algebra C₀ ((G i) ⊗[G O] C₀) :=
        (Algebra.TensorProduct.includeRight (R := G O) (A := G i) (B := C₀)).toRingHom.toAlgebra
      Subsingleton (((G i) ⊗[G O] C₀) ⊗[C₀] M) := by
  classical
  let J := {i : ι // O ≤ i}
  let hd : IsDirected J (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.val b.val
    exact ⟨⟨c, le_trans a.property hac⟩, hac, hbc⟩⟩
  let algGa : ∀ a : J, Algebra (G O) (G a.val) := fun a => (f O a.val a.property).toAlgebra
  let φAlg : (a b : J) → a ≤ b → (G a.val →ₐ[G O] G b.val) := fun a b hab =>
    { f a.val b.val hab with
      commutes' := by
        intro r
        show f a.val b.val hab (f O a.val a.property r) = f O b.val b.property r
        exact DirectedSystem.map_map (f := fun i j h => f i j h) a.property hab r }
  let gN : (a b : J) → a ≤ b → G a.val →ₗ[G O] G b.val := fun a b hab => (φAlg a b hab).toLinearMap
  have hgNcomp : ∀ (a b c : J) (hab : a ≤ b) (hbc : b ≤ c),
      (gN b c hbc).comp (gN a b hab) = gN a c (le_trans hab hbc) := by
    intro a b c hab hbc; ext y
    exact DirectedSystem.map_map (F := G) (f := fun i j h => f i j h) hab hbc y
  let dsN : DirectedSystem (fun a : J => G a.val) (fun a b h => gN a b h) := by
    refine ⟨?_, ?_⟩
    · intro a x; exact DirectedSystem.map_self (F := G) (f := fun i j h => f i j h) (i := a.val) x
    · intro a b c hab hbc x
      exact DirectedSystem.map_map (F := G) (f := fun i j h => f i j h) hab hbc x
  set A := Ring.DirectLimit G (fun i j h => f i j h) with hA
  let : Algebra (G O) A := (Ring.DirectLimit.of G _ O).toAlgebra
  set DL := Module.DirectLimit (fun a : J => G a.val) (fun a b h => gN a b h) with hDL
  let ofAlg : ∀ a : J, G a.val →ₐ[G O] A := fun a =>
    { Ring.DirectLimit.of G _ a.val with
      commutes' := by
        intro r
        show Ring.DirectLimit.of G _ a.val (f O a.val a.property r) = Ring.DirectLimit.of G _ O r
        exact Ring.DirectLimit.of_f a.property r }
  let ψ : ∀ a : J, G a.val →ₗ[G O] A := fun a => (ofAlg a).toLinearMap
  let H : DL →ₗ[G O] A := Module.DirectLimit.lift (G O) J (fun a : J => G a.val)
    (fun a b h => gN a b h) ψ (by
      intro a b hab x
      show Ring.DirectLimit.of G _ b.val (f a.val b.val hab x) = Ring.DirectLimit.of G _ a.val x
      exact Ring.DirectLimit.of_f (i := a.val) (j := b.val) hab x)
  have hHof : ∀ (a : J) (x : G a.val),
      H (Module.DirectLimit.of (G O) J _ _ a x) = Ring.DirectLimit.of G _ a.val x :=
    fun a x => Module.DirectLimit.lift_of ψ _ x
  have hsurj : Function.Surjective H := by
    intro z
    obtain ⟨i, x, hx⟩ := Ring.DirectLimit.exists_of z
    obtain ⟨j, hij, hOj⟩ := directed_of (· ≤ ·) i O
    refine ⟨Module.DirectLimit.of (G O) J _ _ ⟨j, hOj⟩ (f i j hij x), ?_⟩
    rw [hHof]; change Ring.DirectLimit.of G _ j (f i j hij x) = z
    rw [Ring.DirectLimit.of_f hij x, hx]
  have hinj : Function.Injective H := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨a, y, rfl⟩ := Module.DirectLimit.exists_of w
    rw [hHof] at hw
    obtain ⟨j, hij, hfj⟩ := Ring.DirectLimit.of.zero_exact hw
    obtain ⟨k, hjk, hOk⟩ := directed_of (· ≤ ·) j O
    have hak : a.val ≤ k := le_trans hij hjk
    have hfk : f a.val k hak y = 0 := by
      have hmm := DirectedSystem.map_map (F := G) (f := fun i j h => f i j h) hij hjk y
      rw [hfj, map_zero] at hmm; rw [← hmm]
    have hbk : a ≤ (⟨k, hOk⟩ : J) := hak
    have step : (gN a ⟨k,hOk⟩ hbk) y = 0 := hfk
    rw [← Module.DirectLimit.of_f (i := a) (j := ⟨k,hOk⟩) (hij := hbk), step, map_zero]
  let eA : A ≃ₗ[G O] DL := (LinearEquiv.ofBijective H ⟨hinj, hsurj⟩).symm
  have heA : ∀ (a : J) (x : G a.val),
      eA (Ring.DirectLimit.of G _ a.val x) = Module.DirectLimit.of (G O) J _ _ a x := by
    intro a x
    apply (LinearEquiv.ofBijective H ⟨hinj, hsurj⟩).injective
    show H (eA (Ring.DirectLimit.of G _ a.val x)) = H (Module.DirectLimit.of (G O) J _ _ a x)
    rw [hHof]
    show (LinearEquiv.ofBijective H ⟨hinj, hsurj⟩) (eA (Ring.DirectLimit.of G _ a.val x)) =
        Ring.DirectLimit.of G _ a.val x
    rw [LinearEquiv.apply_symm_apply]
  let algCAC : Algebra C₀ (A ⊗[G O] C₀) :=
    (Algebra.TensorProduct.includeRight (R := G O) (A := A) (B := C₀)).toRingHom.toAlgebra
  let algCa : ∀ a : J, Algebra C₀ (G a.val ⊗[G O] C₀) := fun a =>
    (Algebra.TensorProduct.includeRight (R := G O) (A := G a.val) (B := C₀)).toRingHom.toAlgebra
  let Φ2 : (A ⊗[G O] C₀) ≃ₗ[G O]
      Module.DirectLimit (fun a : J => G a.val ⊗[G O] C₀)
        (fun a b h => LinearMap.rTensor C₀ (gN a b h)) :=
    (LinearEquiv.rTensor C₀ eA).trans (TensorProduct.directLimitLeft (fun a b h => gN a b h) C₀)
  have hΦ2 : ∀ (a : J) (g : G a.val) (c : C₀),
      Φ2 ((Ring.DirectLimit.of G _ a.val g) ⊗ₜ[G O] c)
        = Module.DirectLimit.of (G O) J (fun a : J => G a.val ⊗[G O] C₀)
            (fun a b h => LinearMap.rTensor C₀ (gN a b h)) a (g ⊗ₜ[G O] c) := by
    intro a g c
    show (TensorProduct.directLimitLeft (fun a b h => gN a b h) C₀)
        ((LinearEquiv.rTensor C₀ eA) ((Ring.DirectLimit.of G _ a.val g) ⊗ₜ[G O] c)) = _
    rw [LinearEquiv.rTensor_tmul, heA]
    exact TensorProduct.directLimitLeft_tmul_of (fun a b h => gN a b h) C₀ g c
  let g1Alg : (a b : J) → a ≤ b →
      ((G a.val ⊗[G O] C₀) →ₐ[G O] (G b.val ⊗[G O] C₀)) := fun a b hab =>
    Algebra.TensorProduct.map (φAlg a b hab) (AlgHom.id (G O) C₀)
  let g1 : (a b : J) → a ≤ b → ((G a.val ⊗[G O] C₀) →ₗ[C₀] (G b.val ⊗[G O] C₀)) := fun a b hab =>
    { toFun := g1Alg a b hab
      map_add' := map_add _
      map_smul' := map_smul_of_map_algebraMap (g1Alg a b hab).toRingHom fun c => by
        change g1Alg a b hab ((1 : G a.val) ⊗ₜ[G O] c) = (1 : G b.val) ⊗ₜ[G O] c
        simp [g1Alg] }
  have hg1 : ∀ (a b : J) (hab : a ≤ b) (x : G a.val ⊗[G O] C₀),
      g1 a b hab x = LinearMap.rTensor C₀ (gN a b hab) x := by
    intro a b hab x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul g c =>
      show g1Alg a b hab (g ⊗ₜ[G O] c) = LinearMap.rTensor C₀ (gN a b hab) (g ⊗ₜ[G O] c)
      rw [LinearMap.rTensor_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  let dsC : DirectedSystem (fun a : J => G a.val ⊗[G O] C₀) (fun a b h => g1 a b h) := by
    refine ⟨?_, ?_⟩
    · intro a x
      show g1 a a (le_refl a) x = x
      rw [hg1]
      have hid : gN a a (le_refl a) = LinearMap.id := by
        ext y; exact DirectedSystem.map_self (F := G) (f := fun i j h => f i j h) (i := a.val) y
      rw [hid, LinearMap.rTensor_id]; rfl
    · intro a b c hab hbc x
      rw [hg1, hg1, hg1, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hgNcomp]
  set DLC := Module.DirectLimit (fun a : J => G a.val ⊗[G O] C₀) (fun a b h => g1 a b h) with hDLC
  let inclAlg : ∀ a : J, (G a.val ⊗[G O] C₀) →ₐ[G O] (A ⊗[G O] C₀) := fun a =>
    Algebra.TensorProduct.map (ofAlg a) (AlgHom.id (G O) C₀)
  let incl : ∀ a : J, (G a.val ⊗[G O] C₀) →ₗ[C₀] (A ⊗[G O] C₀) := fun a =>
    { toFun := inclAlg a
      map_add' := map_add _
      map_smul' := map_smul_of_map_algebraMap (inclAlg a).toRingHom fun c => by
        change inclAlg a ((1 : G a.val) ⊗ₜ[G O] c) = (1 : A) ⊗ₜ[G O] c
        simp [inclAlg, ofAlg] }
  have hincl : ∀ (a : J) (g : G a.val) (c : C₀),
      incl a (g ⊗ₜ[G O] c) = (Ring.DirectLimit.of G _ a.val g) ⊗ₜ[G O] c := by
    intro a g c
    show inclAlg a (g ⊗ₜ[G O] c) = (Ring.DirectLimit.of G _ a.val g) ⊗ₜ[G O] c
    simp only [inclAlg, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    rfl
  have hinclcompat : ∀ (a b : J) (hab : a ≤ b) (x : G a.val ⊗[G O] C₀),
      incl b (g1 a b hab x) = incl a x := by
    intro a b hab x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul g c =>
      show incl b (g1 a b hab (g ⊗ₜ[G O] c)) = incl a (g ⊗ₜ[G O] c)
      have : g1 a b hab (g ⊗ₜ[G O] c) = (f a.val b.val hab g) ⊗ₜ[G O] c := by
        show g1Alg a b hab (g ⊗ₜ[G O] c) = _
        simp [g1Alg, φAlg]
      rw [this, hincl, hincl]
      congr 1
      exact Ring.DirectLimit.of_f (i := a.val) (j := b.val) hab g
    | add x y hx hy => simp only [map_add]; rw [hx, hy]
  let Hb : DLC →ₗ[C₀] (A ⊗[G O] C₀) :=
    Module.DirectLimit.lift C₀ J (fun a : J => G a.val ⊗[G O] C₀)
      (fun a b h => g1 a b h) incl (fun a b hab x => hinclcompat a b hab x)
  have hHbof : ∀ (a : J) (x : G a.val ⊗[G O] C₀),
      Hb (Module.DirectLimit.of C₀ J _ _ a x) = incl a x := fun a x =>
    Module.DirectLimit.lift_of incl _ x
  have hΦ2Hb : ∀ (a : J) (x : G a.val ⊗[G O] C₀),
      Φ2 (incl a x) = Module.DirectLimit.of (G O) J (fun a : J => G a.val ⊗[G O] C₀)
        (fun a b h => LinearMap.rTensor C₀ (gN a b h)) a x := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul g c => rw [hincl, hΦ2]
    | add x y hx hy => simp only [map_add]; rw [hx, hy]
  have hHbsurj : Function.Surjective Hb := by
    intro z
    obtain ⟨a, x, hax⟩ := Module.DirectLimit.exists_of (Φ2 z)
    refine ⟨Module.DirectLimit.of C₀ J _ _ a x, ?_⟩
    rw [hHbof]
    apply Φ2.injective
    rw [hΦ2Hb, hax]
  have hHbinj : Function.Injective Hb := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨a, x, rfl⟩ := Module.DirectLimit.exists_of w
    rw [hHbof] at hw
    have hz : Φ2 (incl a x) = 0 := by rw [hw, map_zero]
    rw [hΦ2Hb] at hz
    obtain ⟨b, hab, hgb⟩ := Module.DirectLimit.of.zero_exact hz
    have hgb' : g1 a b hab x = 0 := by rwa [hg1]
    rw [← Module.DirectLimit.of_f (i := a) (j := b) (hij := hab), hgb', map_zero]
  let eB : (A ⊗[G O] C₀) ≃ₗ[C₀] DLC := (LinearEquiv.ofBijective Hb ⟨hHbinj, hHbsurj⟩).symm
  have hsubColim : Subsingleton ((A ⊗[G O] C₀) ⊗[C₀] M) := hcolim
  have hsubDLCM : Subsingleton (DLC ⊗[C₀] M) :=
    (LinearEquiv.rTensor M eB).toEquiv.subsingleton_congr.mp hsubColim
  have hsubN : Subsingleton (Module.DirectLimit
      (fun a : J => (G a.val ⊗[G O] C₀) ⊗[C₀] M)
      (fun a b h => LinearMap.rTensor M (g1 a b h))) :=
    (TensorProduct.directLimitLeft (fun a b h => g1 a b h) M).toEquiv.subsingleton_congr.mp hsubDLCM
  let g : (a b : J) → a ≤ b → ((G a.val ⊗[G O] C₀) ⊗[C₀] M) →ₗ[C₀] ((G b.val ⊗[G O] C₀) ⊗[C₀] M) :=
    fun a b h => LinearMap.rTensor M (g1 a b h)
  obtain ⟨T, hT⟩ := (Module.Finite.fg_top (R := C₀) (M := M))
  let i₀ : J := ⟨O, le_refl O⟩
  clear_value i₀
  let s : Finset ((G i₀.val ⊗[G O] C₀) ⊗[C₀] M) :=
    T.image (fun m => ((1 : G i₀.val ⊗[G O] C₀)) ⊗ₜ[C₀] m)
  obtain ⟨⟨i, hOi⟩, _, hSub⟩ := generic_directLimit_descent'
    (R := C₀) (ι := J)
    (fun a : J => (G a.val ⊗[G O] C₀) ⊗[C₀] M) (fun a b h => g a b h)
    hsubN i₀ s (by
      intro a hi hvanish
      apply tensorBaseChange_subsingleton_of_gens_vanish C₀ (G a.val ⊗[G O] C₀) M T hT
      intro m hm
      have hmem : ((1 : G i₀.val ⊗[G O] C₀) ⊗ₜ[C₀] m) ∈ s := Finset.mem_image_of_mem _ hm
      have hv := hvanish _ hmem
      have hgone : g i₀ a hi ((1 : G i₀.val ⊗[G O] C₀) ⊗ₜ[C₀] m)
          = (1 : G a.val ⊗[G O] C₀) ⊗ₜ[C₀] m := by
        show LinearMap.rTensor M (g1 i₀ a hi) ((1 : G i₀.val ⊗[G O] C₀) ⊗ₜ[C₀] m) = _
        rw [LinearMap.rTensor_tmul]
        congr 1
        show g1Alg i₀ a hi (1 : G i₀.val ⊗[G O] C₀) = (1 : G a.val ⊗[G O] C₀)
        exact map_one _
      rw [hgone] at hv
      exact hv)
  exact ⟨i, hOi, hSub⟩

/-- If `C₀` is of finite type over `B₀` via `φ₀`, then for any `R`-algebra `S` the base change
`id_S ⊗ φ₀ : S ⊗[R] B₀ → S ⊗[R] C₀` is of finite type. -/
lemma finiteType_baseChange_map
    (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (B₀ C₀ : Type*) [CommRing B₀] [CommRing C₀] [Algebra R B₀] [Algebra R C₀]
    (φ₀ : B₀ →ₐ[R] C₀)
    (hFT :
      letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
      Algebra.FiniteType B₀ C₀) :
    letI φS : (S ⊗[R] B₀) →ₐ[S] (S ⊗[R] C₀) :=
      Algebra.TensorProduct.map (AlgHom.id S S) φ₀
    letI : Algebra (S ⊗[R] B₀) (S ⊗[R] C₀) := φS.toRingHom.toAlgebra
    Algebra.FiniteType (S ⊗[R] B₀) (S ⊗[R] C₀) := by
  classical
  let _ : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let φS : (S ⊗[R] B₀) →ₐ[S] (S ⊗[R] C₀) := Algebra.TensorProduct.map (AlgHom.id S S) φ₀
  let _ : Algebra (S ⊗[R] B₀) (S ⊗[R] C₀) := φS.toRingHom.toAlgebra
  obtain ⟨s, hs⟩ := hFT.out
  refine ⟨⟨s.image fun c => (1 : S) ⊗ₜ[R] c, ?_⟩⟩
  set AdT := Algebra.adjoin (S ⊗[R] B₀) (↑(s.image fun c => (1 : S) ⊗ₜ[R] c) : Set (S ⊗[R] C₀))
  have hx1 (x : S) : x ⊗ₜ[R] (1 : C₀) ∈ AdT := by
    have : x ⊗ₜ[R] (1 : C₀) = algebraMap (S ⊗[R] B₀) _ (x ⊗ₜ[R] (1 : B₀)) := by
      simp [φS, RingHom.algebraMap_toAlgebra]
    exact this ▸ AdT.algebraMap_mem _
  let D : Subalgebra B₀ C₀ :=
    { carrier := {c | (1 : S) ⊗ₜ[R] c ∈ AdT}
      mul_mem' {a b} ha hb := by
        simpa [Algebra.TensorProduct.tmul_mul_tmul] using AdT.mul_mem ha hb
      add_mem' {a b} ha hb := by
        simpa [TensorProduct.tmul_add] using AdT.add_mem ha hb
      algebraMap_mem' b := by
        have : (1 : S) ⊗ₜ[R] algebraMap B₀ C₀ b = algebraMap (S ⊗[R] B₀) _ (1 ⊗ₜ[R] b) := by
          simp [φS, RingHom.algebraMap_toAlgebra]
        show _ ∈ AdT
        rw [this]
        exact AdT.algebraMap_mem _ }
  have hDtop : D = ⊤ := by
    rw [← top_le_iff, ← hs]
    refine Algebra.adjoin_le fun c hc => Algebra.subset_adjoin ?_
    simpa using ⟨c, hc, rfl⟩
  have h1c (c : C₀) : (1 : S) ⊗ₜ[R] c ∈ AdT := by
    show c ∈ D
    simp [hDtop]
  rw [eq_top_iff]
  rintro z -
  induction z with
  | zero => exact AdT.zero_mem
  | add a b ha hb => exact AdT.add_mem ha hb
  | tmul x c => simpa using AdT.mul_mem (hx1 x) (h1c c)

/-- If the base change `Φ = id_A ⊗ φ₀` of `φ₀` to the directed colimit `A = colim_i Aᵢ` is
unramified and `C₀` is of finite type over `B₀` via `φ₀`, then the base change
`Φᵢ = id_{Aᵢ} ⊗ φ₀` is unramified at some finite stage `i ≥ O`, where `G i` is an
`A₀`-algebra via `f O i h`. -/
@[stacks 0C4F]
theorem colimit_unramified
    (hΦ :
      letI : Algebra ((A G f) ⊗[G O] B₀) ((A G f) ⊗[G O] C₀) :=
        (phiColim G f O B₀ C₀ φ₀).toRingHom.toAlgebra
      Algebra.Unramified ((A G f) ⊗[G O] B₀) ((A G f) ⊗[G O] C₀))
    (hFT :
      letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
      Algebra.FiniteType B₀ C₀) :
    ∃ i, ∃ (h : O ≤ i),
      letI : Algebra (G O) (G i) := (f O i h).toAlgebra
      letI φᵢ : (G i) ⊗[G O] B₀ →ₐ[G i] (G i) ⊗[G O] C₀ :=
        Algebra.TensorProduct.map (AlgHom.id (G i) (G i)) φ₀
      letI : Algebra ((G i) ⊗[G O] B₀) ((G i) ⊗[G O] C₀) := φᵢ.toRingHom.toAlgebra
      Algebra.Unramified ((G i) ⊗[G O] B₀) ((G i) ⊗[G O] C₀) := by
  classical
  set R := G O with hR
  let algBC : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  have hΦFU := hΦ.formallyUnramified
  obtain ⟨i, hOi, hFUi⟩ :
      ∃ i, ∃ (h : O ≤ i),
        let : Algebra (G O) (G i) := (f O i h).toAlgebra
        let φᵢ : (G i) ⊗[G O] B₀ →ₐ[G i] (G i) ⊗[G O] C₀ :=
          Algebra.TensorProduct.map (AlgHom.id (G i) (G i)) φ₀
        let : Algebra ((G i) ⊗[G O] B₀) ((G i) ⊗[G O] C₀) := φᵢ.toRingHom.toAlgebra
        Algebra.FormallyUnramified ((G i) ⊗[G O] B₀) ((G i) ⊗[G O] C₀) := by
    have : Algebra.EssFiniteType B₀ C₀ := .of_finiteType B₀ C₀
    have hΩfin : Module.Finite C₀ (Ω[C₀⁄B₀]) := KaehlerDifferential.finite B₀ C₀
    have hcolimSub :
        let algCAC : Algebra C₀ ((A G f) ⊗[G O] C₀) :=
          (Algebra.TensorProduct.includeRight (R := G O) (A := A G f) (B := C₀)).toRingHom.toAlgebra
        Subsingleton (((A G f) ⊗[G O] C₀) ⊗[C₀] (Ω[C₀⁄B₀])) :=
      (formallyUnramified_baseChange_iff R (A G f) B₀ C₀ φ₀).mp hΦFU
    obtain ⟨i, hOi, hStageSub⟩ :=
      colimit_baseChange_descent G f O C₀ (Ω[C₀⁄B₀]) hcolimSub
    refine ⟨i, hOi, ?_⟩
    let _ : Algebra (G O) (G i) := (f O i hOi).toAlgebra
    exact (formallyUnramified_baseChange_iff R (G i) B₀ C₀ φ₀).mpr hStageSub
  refine ⟨i, hOi, ?_⟩
  let _ : Algebra (G O) (G i) := (f O i hOi).toAlgebra
  let φᵢ : (G i) ⊗[G O] B₀ →ₐ[G i] (G i) ⊗[G O] C₀ :=
    Algebra.TensorProduct.map (AlgHom.id (G i) (G i)) φ₀
  let _ : Algebra ((G i) ⊗[G O] B₀) ((G i) ⊗[G O] C₀) := φᵢ.toRingHom.toAlgebra
  exact ⟨hFUi, finiteType_baseChange_map (G O) (G i) B₀ C₀ φ₀ hFT⟩

end Stacks.DirectLimit.UnramifiedDescent

end
