module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Tactic.Abel
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.HigherTrace.Basic.PthRootDifferentials
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.TraceMapPositive.Basic
public import StacksFrontier.RingTheory.Kaehler.Basic
public import StacksFrontier.RingTheory.Kaehler.JacobiZariski

/-!
# The higher trace on differential forms

The relative trace of a `p`-th root extension, the exterior-algebra constructions used to build
the trace from a presentation, and the higher trace `KaehlerDifferential.higherTrace` with its
values, its vanishing on forms from the base, and its independence of the presentation.
-/

public noncomputable section

namespace KaehlerDifferential

open Polynomial
open scoped TensorProduct
open scoped KaehlerDifferential

variable {p t : ℕ} {Λ R S : Type*} [CommRing Λ] [CommRing R] [CommRing S]
  [Algebra Λ R] [Algebra Λ S] [Algebra R S] [IsScalarTower Λ R S]

/-- A nontrivial algebra over a ring of prime characteristic `p` has characteristic `p`. -/
private theorem charP_algebra_of_prime [Nontrivial R]
    (hp : p.Prime) [CharP Λ p] : CharP R p := by
  apply (CharP.charP_iff_prime_eq_zero hp).mpr
  simpa only [map_natCast, map_zero] using congrArg (algebraMap Λ R) (CharP.cast_eq_zero Λ p)

/-- The trace on relative differentials `Omega[S/R] -> Omega[R/Lambda]` attached to a presentation
of `S` by adjoining a `p`-th root, obtained from the trace of the adjoin-root algebra. -/
private noncomputable def rootDifferentialTrace [Nontrivial R]
    (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C a) ≃ₐ[R] S) :
    Ω[S⁄R] →ₗ[R] Ω[R⁄Λ] := by
  letI : CharP R p := charP_algebra_of_prime (Λ := Λ) hp
  letI : Fact p.Prime := ⟨hp⟩
  letI : Algebra S (AdjoinRoot (Polynomial.X ^ p - Polynomial.C a)) :=
    e.symm.toRingHom.toAlgebra
  letI : IsScalarTower R S (AdjoinRoot (Polynomial.X ^ p - Polynomial.C a)) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      exact (e.symm.commutes r).symm
  exact (KaehlerDifferential.map ℤ Λ R R).comp
    ((pthRootDifferentialTrace p a).1.comp
      ((KaehlerDifferential.map R R S
        (AdjoinRoot (Polynomial.X ^ p - Polynomial.C a))).restrictScalars R))

omit [Algebra Λ S] [IsScalarTower Λ R S] in
/-- The trace sends `x ^ i * dx` to `da` when `i = p - 1` and to zero otherwise. -/
private theorem rootDifferentialTrace_apply_root [Nontrivial R]
    (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C a) ≃ₐ[R] S) (i : ℕ)
    (hi : i < p) :
    rootDifferentialTrace (Λ := Λ) hp a e
      ((e (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C a))) ^ i •
        KaehlerDifferential.D R S
          (e (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C a)))) =
      if i = p - 1 then KaehlerDifferential.D Λ R a else 0 := by
  let A := AdjoinRoot (Polynomial.X ^ p - Polynomial.C a)
  let : CharP R p := charP_algebra_of_prime (Λ := Λ) hp
  let : Fact p.Prime := ⟨hp⟩
  let : Algebra S A := e.symm.toRingHom.toAlgebra
  let : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq fun r =>
    (e.symm.commutes r).symm
  let x := e (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C a))
  change (KaehlerDifferential.map ℤ Λ R R)
      ((pthRootDifferentialTrace p a).1
        (((KaehlerDifferential.map R R S A).restrictScalars R)
          (x ^ i • KaehlerDifferential.D R S x))) = _
  have hD := KaehlerDifferential.map_D R R S A x
  have hroot : algebraMap S A (e (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C a))) =
      AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C a) :=
    e.symm_apply_apply _
  have hinput : (KaehlerDifferential.map R R S A).restrictScalars R
      (x ^ i • KaehlerDifferential.D R S x) =
      (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C a)) ^ i •
        KaehlerDifferential.D R A (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C a)) := by
    change KaehlerDifferential.map R R S A (x ^ i • KaehlerDifferential.D R S x) = _
    rw [map_smul, hD, hroot,
      ← IsScalarTower.algebraMap_smul (R := S) (A := A) (r := x ^ i),
      map_pow, hroot]
  rw [hinput, (pthRootDifferentialTrace p a).2 i hi]
  split_ifs <;> simp

/-- The algebra map from the exterior algebra of a module to the exterior algebra of its base
change. -/
private noncomputable def exteriorScalarExtension {K A M : Type*} [CommRing K]
    [CommRing A] [Algebra K A] [AddCommGroup M] [Module K M] :
    ExteriorAlgebra A (A ⊗[K] M) →ₐ[A] A ⊗[K] ExteriorAlgebra K M := by
  let f := TensorProduct.AlgebraTensorModule.map
    (LinearMap.id : A →ₗ[A] A) (ExteriorAlgebra.ι K (M := M))
  have hanti (x y : A ⊗[K] M) : f x * f y + f y * f x = 0 := by
    induction x using TensorProduct.inductionOn with
    | tmul a m =>
      induction y using TensorProduct.inductionOn with
      | tmul b n =>
        simp only [f, TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply,
          Algebra.TensorProduct.tmul_mul_tmul]
        rw [mul_comm b a, ← TensorProduct.tmul_add, ExteriorAlgebra.ι_add_mul_swap]
        simp
      | add y z hy hz =>
        simp only [map_add, mul_add, add_mul]
        calc
          _ = (f (a ⊗ₜ[K] m) * f y + f y * f (a ⊗ₜ[K] m)) +
              (f (a ⊗ₜ[K] m) * f z + f z * f (a ⊗ₜ[K] m)) := by abel
          _ = 0 := by rw [hy, hz, add_zero]
    | add x z hx hz =>
      simp only [map_add, mul_add, add_mul]
      calc
        _ = (f x * f y + f y * f x) + (f z * f y + f y * f z) := by abel
        _ = 0 := by rw [hx, hz, add_zero]
  refine ExteriorAlgebra.lift A ⟨f, fun x => ?_⟩
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp [f, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy =>
    simp only [map_add, add_mul, mul_add]
    calc
      _ = (f x * f x) + (f y * f y) + (f x * f y + f y * f x) := by abel
      _ = 0 := by rw [hx, hy, hanti, add_zero, add_zero]

/-- The scalar extension of exterior algebras on a generator. -/
private theorem exteriorScalarExtension_ι {K A M : Type*} [CommRing K]
    [CommRing A] [Algebra K A] [AddCommGroup M] [Module K M] (a : A) (m : M) :
    exteriorScalarExtension (ExteriorAlgebra.ι A (a ⊗ₜ[K] m)) =
      a ⊗ₜ[K] ExteriorAlgebra.ι K m := by
  simp [exteriorScalarExtension, ExteriorAlgebra.lift_ι_apply]

/-- The scalar extension of exterior algebras on a wedge of generators. -/
private theorem exteriorScalarExtension_ιMulti {K A M : Type*} [CommRing K]
    [CommRing A] [Algebra K A] [AddCommGroup M] [Module K M]
    (n : ℕ) (v : Fin n → M) :
    exteriorScalarExtension (ExteriorAlgebra.ιMulti A n (fun i => (1 : A) ⊗ₜ[K] v i)) =
      (1 : A) ⊗ₜ[K] ExteriorAlgebra.ιMulti K n v := by
  induction n with
  | zero => simp [ExteriorAlgebra.ιMulti_zero_apply, Algebra.TensorProduct.one_def]
  | succ n ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul]
    rw [exteriorScalarExtension_ι]
    change _ * exteriorScalarExtension (ExteriorAlgebra.ιMulti A n
      (fun i => (1 : A) ⊗ₜ[K] v i.succ)) = _
    rw [ih, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ExteriorAlgebra.ιMulti_succ_apply]
    rfl

/-- Multiplication by a vector, as a map from the exterior algebra into the kernel of
multiplication by that vector. -/
private noncomputable def exteriorKernelAction {K M : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] (v : M) :
    M →ₗ[K] Module.End K (LinearMap.ker (LinearMap.mulLeft K (ExteriorAlgebra.ι K v))) where
  toFun m :=
    { toFun := fun z => ⟨ExteriorAlgebra.ι K m * z.val, by
        change ExteriorAlgebra.ι K v * (ExteriorAlgebra.ι K m * z.val) = 0
        rw [← mul_assoc, (eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap v m)),
          neg_mul, mul_assoc]
        have hz : ExteriorAlgebra.ι K v * z.val = 0 := z.property
        rw [hz, mul_zero, neg_zero]⟩
      map_add' := fun x y => Subtype.ext (mul_add _ _ _)
      map_smul' := fun r x => Subtype.ext (mul_smul_comm _ _ _) }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change ExteriorAlgebra.ι K (x+y) * z.val =
      ExteriorAlgebra.ι K x * z.val + ExteriorAlgebra.ι K y * z.val
    rw [map_add, add_mul]
  map_smul' r x := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change ExteriorAlgebra.ι K (r • x) * z.val = r • (ExteriorAlgebra.ι K x * z.val)
    rw [map_smul, smul_mul_assoc]

/-- The value of that multiplication map. -/
private theorem exteriorKernelAction_apply {K M : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] (v m : M)
    (z : LinearMap.ker (LinearMap.mulLeft K (ExteriorAlgebra.ι K v))) :
    (exteriorKernelAction v m z).val = ExteriorAlgebra.ι K m * z.val := rfl

/-- Multiplication by a vector kills the span of that vector. -/
private theorem exteriorKernelAction_span_le_ker {K M : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] (v : M) :
    Submodule.span K {v} ≤ LinearMap.ker (exteriorKernelAction v) := by
  rw [Submodule.span_le, Set.singleton_subset_iff]
  change exteriorKernelAction v v = 0
  exact LinearMap.ext fun z => Subtype.ext z.property

/-- The action of the quotient of a module by the span of a vector on the kernel of multiplication
by that vector. -/
private noncomputable def exteriorQuotientVectorAction {K M : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] (v : M) :
    (M ⧸ Submodule.span K {v}) →ₗ[K]
      Module.End K (LinearMap.ker (LinearMap.mulLeft K (ExteriorAlgebra.ι K v))) :=
  Submodule.liftQ (R := K) (R₂ := K) (τ₁₂ := RingHom.id K)
    (M₂ := Module.End K (LinearMap.ker (LinearMap.mulLeft K (ExteriorAlgebra.ι K v))))
    (Submodule.span K {v}) (exteriorKernelAction (K := K) v)
    (exteriorKernelAction_span_le_ker (K := K) v)

/-- The quotient action squares to zero, so it extends to the exterior algebra of the quotient. -/
private theorem exteriorQuotientVectorAction_sq {K M : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] (v : M) (m : M ⧸ Submodule.span K {v}) :
    exteriorQuotientVectorAction v m * exteriorQuotientVectorAction v m = 0 := by
  induction m using Submodule.Quotient.induction_on with
  | _ m =>
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change (exteriorKernelAction v m (exteriorKernelAction v m z)).val = 0
    rw [exteriorKernelAction_apply, exteriorKernelAction_apply, ← mul_assoc,
      ExteriorAlgebra.ι_sq_zero, zero_mul]

/-- The algebra map from the exterior algebra of the quotient by the span of a vector to the
endomorphisms of the kernel of multiplication by that vector. -/
private noncomputable def exteriorQuotientAction {K M : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] (v : M) :
    ExteriorAlgebra K (M ⧸ Submodule.span K {v}) →ₐ[K]
      Module.End K (LinearMap.ker (LinearMap.mulLeft K (ExteriorAlgebra.ι K v))) :=
  ExteriorAlgebra.lift K
    ⟨exteriorQuotientVectorAction v, exteriorQuotientVectorAction_sq (K := K) v⟩

/-- The value of that algebra map on a generator. -/
private theorem exteriorQuotientAction_ι_apply {K M : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] (v m : M)
    (z : LinearMap.ker (LinearMap.mulLeft K (ExteriorAlgebra.ι K v))) :
    ((exteriorQuotientAction v) (ExteriorAlgebra.ι K ((Submodule.span K {v}).mkQ m)) z).val =
      ExteriorAlgebra.ι K m * z.val := by
  simp only [exteriorQuotientAction, ExteriorAlgebra.lift_ι_apply]
  rfl

/-- Wedging with a vector, as a map from the exterior algebra of the quotient by its span. -/
private noncomputable def exteriorQuotientWedge {K M : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] (v : M) :
    ExteriorAlgebra K (M ⧸ Submodule.span K {v}) →ₗ[K] ExteriorAlgebra K M :=
  (LinearMap.ker (LinearMap.mulLeft K (ExteriorAlgebra.ι K v))).subtype.comp
    ((LinearMap.applyₗ (R := K) (M := LinearMap.ker (LinearMap.mulLeft K
      (ExteriorAlgebra.ι K v))) (⟨ExteriorAlgebra.ι K v, ExteriorAlgebra.ι_sq_zero v⟩ :
        LinearMap.ker (LinearMap.mulLeft K (ExteriorAlgebra.ι K v)))).comp
      (exteriorQuotientAction v).toLinearMap)

/-- The value of the wedging map on a wedge of generators. -/
private theorem exteriorQuotientWedge_ιMulti {K M : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] (v : M) (n : ℕ) (η : Fin n → M) :
    exteriorQuotientWedge v (ExteriorAlgebra.ιMulti K n
      (fun i => (Submodule.span K {v}).mkQ (η i))) =
      ExteriorAlgebra.ιMulti K n η * ExteriorAlgebra.ι K v := by
  have hact (n : ℕ) (η : Fin n → M)
      (z : LinearMap.ker (LinearMap.mulLeft K (ExteriorAlgebra.ι K v))) :
      ((exteriorQuotientAction v) (ExteriorAlgebra.ιMulti K n
        (fun i => (Submodule.span K {v}).mkQ (η i))) z).val =
        ExteriorAlgebra.ιMulti K n η * z.val := by
    induction n with
    | zero => simp [ExteriorAlgebra.ιMulti_zero_apply]
    | succ n ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul]
      change ((exteriorQuotientAction v) (ExteriorAlgebra.ι K
        ((Submodule.span K {v}).mkQ (η 0)))
        ((exteriorQuotientAction v) (ExteriorAlgebra.ιMulti K n
          (fun i => (Submodule.span K {v}).mkQ (η i.succ))) z)).val = _
      rw [exteriorQuotientAction_ι_apply]
      rw [ih, ExteriorAlgebra.ιMulti_succ_apply, mul_assoc]
      rfl
  exact hact n η _
/-- The projection of the exterior algebra onto its component of a fixed degree. -/
private noncomputable def exteriorDegreeProjection {K M : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] (n : ℕ) :
    ExteriorAlgebra K M →ₗ[K] ⋀[K]^n M where
  toFun x := DirectSum.decompose (fun i => ⋀[K]^i M) x n
  map_add' x y := by simp [DirectSum.decompose_add]
  map_smul' r x := by
    rw [DirectSum.decompose_smul]
    exact DFinsupp.smul_apply r _ n

/-- The degree projection on a wedge of the matching number of generators. -/
private theorem exteriorDegreeProjection_ιMulti {K M : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] (n : ℕ) (v : Fin n → M) :
    exteriorDegreeProjection n (ExteriorAlgebra.ιMulti K n v) =
      exteriorPower.ιMulti K n v :=
  Subtype.ext <| DirectSum.decompose_of_mem_same _
    (ExteriorAlgebra.ιMulti_range K n (Set.mem_range_self v))

/-- A wedge of vectors with one more appended is the product of the wedge and the last vector. -/
private theorem exterior_ιMulti_snoc {K M : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] (n : ℕ) (v : Fin n → M) (m : M) :
    ExteriorAlgebra.ιMulti K (n+1) (Fin.snoc v m) =
      ExteriorAlgebra.ιMulti K n v * ExteriorAlgebra.ι K m := by
  rw [Fin.snoc_eq_append]
  have h : Fin.cons m Fin.elim0 = (fun _ : Fin 1 => m) := by ext i; fin_cases i; rfl
  rw [h, ← ExteriorAlgebra.ιMulti_mul_ιMulti]
  simp [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply]
/-- The coefficient of `x ^ i` in a power of the adjoined root, as an element of the base. -/
private noncomputable def rootCoefficient {p : ℕ} {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] (hp : 0 < p) (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) : S →ₗ[R] R :=
  ((AdjoinRoot.powerBasis' (monic_X_pow_sub_C a (Nat.ne_of_gt hp))).basis.constr R
    (fun i => if (i : ℕ) = p - 1 then 1 else 0)).comp e.symm.toLinearMap

/-- The coefficients of `x ^ i` for `i` below the degree of the presentation. -/
private theorem rootCoefficient_pow {p : ℕ} {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Nontrivial R]
    (hp : 0 < p) (a : R) (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S)
    (i : ℕ) (hi : i < p) :
    rootCoefficient hp a e (e (AdjoinRoot.root (X ^ p - C a)) ^ i) =
      if i = p - 1 then 1 else 0 := by
  let PB := AdjoinRoot.powerBasis' (monic_X_pow_sub_C a (Nat.ne_of_gt hp))
  have hi' : i < PB.dim := by simpa [PB, natDegree_X_pow_sub_C] using hi
  let j : Fin PB.dim := ⟨i, hi'⟩
  have hb : e.symm (e (AdjoinRoot.root (X ^ p - C a)) ^ i) = PB.basis j := by
    rw [map_pow, AlgEquiv.symm_apply_apply, PB.basis_eq_pow]
    rfl
  change PB.basis.constr R _ (e.symm _) = _
  rw [hb, PB.basis.constr_basis]

/-- Appending a scalar multiple to a wedge multiplies the wedge by that scalar. -/
private theorem exterior_snoc_smul {K M : Type*} [CommRing K] [AddCommGroup M]
    [Module K M] (n : ℕ) (v : Fin n → M) (m : M) (s : K) :
    exteriorPower.ιMulti K (n+1) (Fin.snoc v (s • m)) =
      s • exteriorPower.ιMulti K (n+1) (Fin.snoc v m) :=
  (exteriorPower.ιMulti K (n+1)).toMultilinearMap.snoc_smul v s m

/-- Two `K`-linear maps out of an `A`-module agree once they agree on every `A`-multiple of a
spanning set. -/
private theorem linearMap_eq_of_span_smul {K A N P : Type*} [CommRing K] [CommRing A]
    [Algebra K A] [AddCommGroup N] [Module K N] [Module A N] [IsScalarTower K A N]
    [AddCommGroup P] [Module K P] (T : Set N) (hspan : Submodule.span A T = ⊤)
    (F G : N →ₗ[K] P) (h : ∀ s : A, ∀ z ∈ T, F (s • z) = G (s • z)) : F = G := by
  refine LinearMap.ext fun z => ?_
  have hz : z ∈ Submodule.span A T := hspan ▸ Submodule.mem_top
  suffices h : ∀ s : A, F (s • z) = G (s • z) by simpa using h 1
  induction hz using Submodule.span_induction with
  | mem z hz => exact fun s => h s z hz
  | zero => simp
  | add z w hz hw iz iw => intro s; simp [smul_add, iz, iw]
  | smul a z hz ih => intro s; simpa [smul_smul] using ih (s*a)

/-- Two linear maps out of the top exterior power agree once they agree on the wedges of base
vectors and on the wedges of base vectors with a scalar multiple of the extra generator appended,
provided those generate the module. -/
private theorem exterior_ext_of_span {K A M N P : Type*} [CommRing K] [CommRing A]
    [Algebra K A] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [Module A N] [IsScalarTower K A N]
    [AddCommGroup P] [Module K P] (n : ℕ) (u : M →ₗ[K] N) (x : N)
    (hspan : Submodule.span A (Set.range u ∪ {x}) = ⊤)
    (F G : (⋀[A]^(n + 1) N) →ₗ[K] P)
    (hbase : ∀ s : A, ∀ η : Fin (n+1) → M,
      F (s • exteriorPower.ιMulti A (n+1) (u ∘ η)) =
      G (s • exteriorPower.ιMulti A (n+1) (u ∘ η)))
    (hroot : ∀ s : A, ∀ η : Fin n → M,
      F (exteriorPower.ιMulti A (n+1) (Fin.snoc (u ∘ η) (s • x))) =
      G (exteriorPower.ιMulti A (n+1) (Fin.snoc (u ∘ η) (s • x)))) : F = G := by
  classical
  let : LinearOrder M := linearOrderOfSTO WellOrderingRel
  let v : WithTop M → N := WithTop.recTopCoe x u
  have hv : Submodule.span A (Set.range v) = ⊤ := by
    convert hspan using 2
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      induction i using WithTop.recTopCoe with
      | top => exact Or.inr rfl
      | coe i => exact Or.inl ⟨i, rfl⟩
    · rintro (⟨i, rfl⟩ | rfl)
      · exact ⟨(i : WithTop M), rfl⟩
      · exact ⟨⊤, rfl⟩
  have hw := exteriorPower.ιMulti_family_span_of_span A (n := n+1) hv
  have hgen (α : Fin (n+1) ↪o WithTop M) (s : A) :
      F (s • exteriorPower.ιMulti A (n+1) (v ∘ α)) =
      G (s • exteriorPower.ιMulti A (n+1) (v ∘ α)) := by
    have hne (j : Fin n) : α j.castSucc ≠ ⊤ :=
      ne_top_of_lt (α.strictMono (Fin.castSucc_lt_last j))
    let η : Fin n → M := fun j => (α j.castSucc).untop (hne j)
    have hη (j : Fin n) : v (α j.castSucc) = u (η j) := by
      rw [← WithTop.coe_untop (α j.castSucc) (hne j)]
      rfl
    by_cases hlast : α (Fin.last n) = ⊤
    · have heq : v ∘ α = Fin.snoc (u ∘ η) x := by
        ext j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp [Function.comp_def, hlast, v]
        · simpa using hη i
      rw [heq, ← exterior_snoc_smul]
      exact hroot s η
    · have hall (j : Fin (n+1)) : α j ≠ ⊤ := fun h =>
        hlast (top_unique (h ▸ α.monotone (Fin.le_last j)))
      let ζ : Fin (n+1) → M := fun j => (α j).untop (hall j)
      have heq : v ∘ α = u ∘ ζ := by
        ext j
        change v (α j) = u (ζ j)
        rw [← WithTop.coe_untop (α j) (hall j)]
        rfl
      rw [heq]
      exact hbase s ζ
  refine linearMap_eq_of_span_smul _ hw F G ?_
  rintro s _ ⟨z, rfl⟩
  exact hgen (Set.powersetCard.ofFinEmbEquiv.symm z) s
/-- The higher trace on differential forms attached to a chosen presentation of `S` by adjoining a
`p`-th root. -/
private noncomputable def traceFromPresentation [CharP R p]
    (hp : 0 < p) (a : R) (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) :
    (⋀[S]^(t + 1) Ω[S⁄Λ]) →ₗ[R] (⋀[R]^(t + 1) Ω[R⁄Λ]) := by
  let v := KaehlerDifferential.D Λ R a
  let Q := Ω[R⁄Λ] ⧸ Submodule.span R {v}
  let B := (S ⊗[R] Ω[R⁄Λ]) ⧸ Submodule.span S {(1 : S) ⊗ₜ[R] v}
  let proj : ((⋀[S]^t B) ⊗[S] (⋀[S]^1 S)) →ₗ[S] (⋀[S]^t B) :=
    (TensorProduct.rid S (⋀[S]^t B)).toLinearMap.comp
      (TensorProduct.map LinearMap.id (exteriorPower.oneEquiv S S).toLinearMap)
  let base : (⋀[S]^t B) →ₗ[S] S ⊗[R] ExteriorAlgebra R Q :=
    exteriorScalarExtension.toLinearMap.comp
      ((Submodule.subtype _).comp (exteriorPower.map t
        (tensorQuotientSpanEquiv (S := S) v).toLinearMap))
  let coeff : S ⊗[R] ExteriorAlgebra R Q →ₗ[R] ExteriorAlgebra R Ω[R⁄Λ] :=
    (TensorProduct.lid R (ExteriorAlgebra R Ω[R⁄Λ])).toLinearMap.comp
      (TensorProduct.map (rootCoefficient hp a e) (exteriorQuotientWedge v))
  exact (exteriorDegreeProjection (t+1)).comp <|
    coeff.comp <| (base.restrictScalars R).comp <|
      (proj.restrictScalars R).comp <| (rootExteriorComponent a e).restrictScalars R

/-- The value of the presentation trace on a wedge of base differentials with `x ^ i * dx`
appended. -/
private theorem traceFromPresentation_apply_snoc [CharP R p]
    (hp : 0 < p) (a : R) (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S)
    (s : S) (η : Fin t → Ω[R⁄Λ]) :
    traceFromPresentation (t := t) (Λ := Λ) hp a e
      (exteriorPower.ιMulti S (t+1)
        (Fin.snoc (fun j => KaehlerDifferential.map Λ Λ R S (η j))
          (s • KaehlerDifferential.D Λ S (e (AdjoinRoot.root (X ^ p - C a)))))) =
      rootCoefficient hp a e s • exteriorPower.ιMulti R (t+1)
        (Fin.snoc η (KaehlerDifferential.D Λ R a)) := by
  simp only [traceFromPresentation, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    rootExteriorComponent_apply_snoc, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe, exteriorPower.oneEquiv_ιMulti,
    TensorProduct.rid_tmul, map_smul, exteriorPower.map_apply_ιMulti]
  have ht : (tensorQuotientSpanEquiv (R := R) (S := S) (KaehlerDifferential.D Λ R a)) ∘
      (fun j : Fin t => (Submodule.span S {((1 : S) ⊗ₜ[R]
        KaehlerDifferential.D Λ R a)}).mkQ ((1 : S) ⊗ₜ[R] η j)) =
      (fun j => (1 : S) ⊗ₜ[R] (Submodule.span R
        {KaehlerDifferential.D Λ R a}).mkQ (η j)) := by
    funext j
    exact tensorQuotientSpanEquiv_apply_tmul (R := R) (S := S) (KaehlerDifferential.D Λ R a) (η j) 1
  rw [ht]
  change exteriorDegreeProjection (t+1)
    ((TensorProduct.lid R (ExteriorAlgebra R Ω[R⁄Λ]))
      ((TensorProduct.map (rootCoefficient hp a e)
        (exteriorQuotientWedge (KaehlerDifferential.D Λ R a)))
        (s • exteriorScalarExtension
          (ExteriorAlgebra.ιMulti S t (fun j => (1 : S) ⊗ₜ[R]
            (Submodule.span R {KaehlerDifferential.D Λ R a}).mkQ (η j)))))) = _
  rw [exteriorScalarExtension_ιMulti, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    TensorProduct.map_tmul, TensorProduct.lid_tmul, exteriorQuotientWedge_ιMulti,
    ← exterior_ιMulti_snoc, map_smul, exteriorDegreeProjection_ιMulti]

/-- The presentation trace annihilates any scalar multiple of a wedge of differentials pulled back
from the base. -/
private theorem traceFromPresentation_smul_baseForm [CharP R p]
    (hp : 0 < p) (a : R) (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S)
    (s : S) (η : Fin (t + 1) → Ω[R⁄Λ]) :
    traceFromPresentation (t := t) (Λ := Λ) hp a e
      (s • exteriorPower.ιMulti S (t+1)
        (fun j => KaehlerDifferential.map Λ Λ R S (η j))) = 0 := by
  simp [traceFromPresentation, rootExteriorComponent_apply_baseForm]


/-- The absolute differentials of the `p`-th root extension are generated over `S` by the pullbacks
of the differentials of `R` together with `dx`. -/
private theorem pthRootAbsoluteDifferentials_span [CharP R p]
    (a : R) (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) :
    Submodule.span S (Set.range (KaehlerDifferential.map Λ Λ R S) ∪
      {KaehlerDifferential.D Λ S (e (AdjoinRoot.root (X ^ p - C a)))}) = ⊤ := by
  let x := KaehlerDifferential.D Λ S (e (AdjoinRoot.root (X ^ p - C a)))
  let P := Submodule.span S (Set.range (KaehlerDifferential.map Λ Λ R S) ∪ {x})
  let B := (S ⊗[R] Ω[R⁄Λ]) ⧸
    Submodule.span S {(1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a}
  let E := pthRootAbsoluteDifferentialEquiv (Λ := Λ) a e
  let L : (S ⊗[R] Ω[R⁄Λ]) →ₗ[S] Ω[S⁄Λ] := E.symm.toLinearMap.comp
    ((LinearMap.inl S B S).comp
      (Submodule.span S {(1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a}).mkQ)
  have hL (η : Ω[R⁄Λ]) : L ((1 : S) ⊗ₜ[R] η) =
      KaehlerDifferential.map Λ Λ R S η := by
    apply E.injective
    change E (E.symm _) = _
    rw [E.apply_symm_apply, pthRootAbsoluteDifferentialEquiv_apply_base]
    rfl
  have hmem (z : S ⊗[R] Ω[R⁄Λ]) : L z ∈ P := by
    induction z using TensorProduct.inductionOn with
    | tmul s η =>
      have h : s ⊗ₜ[R] η = s • ((1 : S) ⊗ₜ[R] η) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h, map_smul, hL]
      exact P.smul_mem s (Submodule.subset_span (Or.inl ⟨η, rfl⟩))
    | add z w hz hw => simpa using P.add_mem hz hw
  have hx (s : S) : E.symm (0, s) = s • x := by
    apply E.injective
    rw [E.apply_symm_apply, map_smul]
    change (0, s) = s • E x
    rw [pthRootAbsoluteDifferentialEquiv_apply_root]
    simp
  apply top_unique
  intro ω _
  obtain ⟨⟨q, s⟩, rfl⟩ := E.symm.surjective ω
  obtain ⟨z, rfl⟩ := (Submodule.span S
    {(1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a}).mkQ_surjective q
  change E.symm (_, s) ∈ P
  have heq : E.symm ((Submodule.span S
      {(1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a}).mkQ z, s) = L z + s • x := by
    rw [← hx]
    change E.symm _ = E.symm (_, 0) + E.symm (0, s)
    rw [← map_add]
    congr 1
    simp
    rfl
  rw [heq]
  exact P.add_mem (hmem z) (P.smul_mem s (Submodule.subset_span (Or.inr rfl)))

/-- **The absolute differentials of the `p`-th root extension are generated over `S` by the
pullbacks of the differentials of `R` together with `dx`.**

This is what turns a statement about an arbitrary form on `S` into a statement about wedges of
forms pulled back from `R`, and about such wedges with `dx` appended: on the former
`KaehlerDifferential.higherTrace_smul_baseForm` gives zero, and on the latter
`KaehlerDifferential.higherTrace_apply_of_le` and `KaehlerDifferential.higherTrace_apply_top`
between them compute the trace. -/
alias pthRootAbsoluteDifferentials_span_eq_top := pthRootAbsoluteDifferentials_span

/-- Appending a differential to a fixed wedge, as a linear map. -/
private noncomputable def exteriorSnocLinear {K M : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] {n : ℕ} (η : Fin n → M) :
    M →ₗ[K] ⋀[K]^(n+1) M where
  toFun m := exteriorPower.ιMulti K (n+1) (Fin.snoc η m)
  map_add' m n := (exteriorPower.ιMulti K _).toMultilinearMap.snoc_add η m n
  map_smul' r m := (exteriorPower.ιMulti K _).toMultilinearMap.snoc_smul η r m

omit [Algebra Λ S] [IsScalarTower Λ R S] in
/-- The relative trace of the `p`-th root extension in terms of the coefficient of the top power of
the root. -/
private theorem rootDifferentialTrace_eq_coefficient [Nontrivial R]
    (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (s : S) :
    rootDifferentialTrace (Λ := Λ) hp a e
      (s • KaehlerDifferential.D R S (e (AdjoinRoot.root (X ^ p - C a)))) =
      rootCoefficient hp.pos a e s • KaehlerDifferential.D Λ R a := by
  let PB := AdjoinRoot.powerBasis' (monic_X_pow_sub_C a hp.ne_zero)
  let b := PB.basis.map e.toLinearEquiv
  have hlin : (rootDifferentialTrace (Λ := Λ) hp a e).comp
      ((LinearMap.toSpanSingleton S Ω[S⁄R]
        (KaehlerDifferential.D R S (e (AdjoinRoot.root (X ^ p - C a))))).restrictScalars R) =
      (rootCoefficient hp.pos a e).smulRight (KaehlerDifferential.D Λ R a) := by
    apply b.ext
    intro i
    dsimp only [b]
    rw [Module.Basis.map_apply]
    change rootDifferentialTrace (Λ := Λ) hp a e
      (e (PB.basis i) • KaehlerDifferential.D R S (e (AdjoinRoot.root (X ^ p - C a)))) =
      rootCoefficient hp.pos a e (e (PB.basis i)) • KaehlerDifferential.D Λ R a
    have hb : e (PB.basis i) = e (AdjoinRoot.root (X ^ p - C a)) ^ (i : ℕ) := by
      rw [PB.basis_eq_pow, map_pow]
      rfl
    have hi : (i : ℕ) < p := by simpa [PB, natDegree_X_pow_sub_C] using i.isLt
    rw [hb, rootDifferentialTrace_apply_root hp a e _ hi, rootCoefficient_pow hp.pos a e _ hi]
    split_ifs <;> simp
  exact DFunLike.congr_fun hlin s

omit [Algebra Λ S] [IsScalarTower Λ R S] in
/-- The relative trace of the `p`-th root extension does not depend on the chosen presentation. -/
private theorem rootDifferentialTrace_eq_of_presentations [Nontrivial R]
    (hp : p.Prime) [CharP Λ p] (a b : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S)
    (f : AdjoinRoot (X ^ p - C b) ≃ₐ[R] S) :
    rootDifferentialTrace (Λ := Λ) hp a e = rootDifferentialTrace (Λ := Λ) hp b f := by
  let : CharP R p := charP_algebra_of_prime (Λ := Λ) hp
  let : Fact p.Prime := ⟨hp⟩
  let A := AdjoinRoot (X ^ p - C a)
  let B := AdjoinRoot (X ^ p - C b)
  let : Algebra S A := e.symm.toRingHom.toAlgebra
  let : Algebra S B := f.symm.toRingHom.toAlgebra
  let : Algebra A B := (e.trans f.symm).toRingHom.toAlgebra
  let : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq fun r =>
    (e.symm.commutes r).symm
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq fun r =>
    (f.symm.commutes r).symm
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r =>
    ((e.trans f.symm).commutes r).symm
  let : IsScalarTower S A B := IsScalarTower.of_algebraMap_eq fun s => by
    change f.symm s = f.symm (e (e.symm s))
    rw [e.apply_symm_apply]
  have hm : ((KaehlerDifferential.map R R A B).restrictScalars S).comp
      (KaehlerDifferential.map R R S A) = KaehlerDifferential.map R R S B := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro s
    change KaehlerDifferential.map R R A B
      (KaehlerDifferential.map R R S A (KaehlerDifferential.D R S s)) =
      KaehlerDifferential.map R R S B (KaehlerDifferential.D R S s)
    simp only [KaehlerDifferential.map_D]
    rw [IsScalarTower.algebraMap_apply S A B]
  have hn := pthRootDifferentialTrace_eq_comp_map p a b (e.trans f.symm).toAlgHom
    (pthRootDifferentialTrace p a).val (pthRootDifferentialTrace p b).val
    (pthRootDifferentialTrace p a).property
    (pthRootDifferentialTrace p b).property
  apply LinearMap.ext
  intro z
  change KaehlerDifferential.map ℤ Λ R R
      ((pthRootDifferentialTrace p a).val (KaehlerDifferential.map R R S A z)) =
    KaehlerDifferential.map ℤ Λ R R
      ((pthRootDifferentialTrace p b).val (KaehlerDifferential.map R R S B z))
  rw [hn]
  exact congrArg (fun ω : Ω[B⁄R] => KaehlerDifferential.map ℤ Λ R R
    ((pthRootDifferentialTrace p b).val ω)) (DFunLike.congr_fun hm z)

/-- The value of the presentation trace on a wedge of base differentials with an arbitrary scalar
multiple of `dx` appended. -/
private theorem traceFromPresentation_snoc_arbitrary [Nontrivial R] [CharP R p]
    (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S)
    (η : Fin t → Ω[R⁄Λ]) (ω : Ω[S⁄Λ]) :
    traceFromPresentation hp.pos a e
      (exteriorPower.ιMulti S (t+1)
        (Fin.snoc (fun j => KaehlerDifferential.map Λ Λ R S (η j)) ω)) =
      exteriorPower.ιMulti R (t+1) (Fin.snoc η
        (rootDifferentialTrace hp a e (KaehlerDifferential.map Λ R S S ω))) := by
  let u := KaehlerDifferential.map Λ Λ R S
  let x := KaehlerDifferential.D Λ S (e (AdjoinRoot.root (X ^ p - C a)))
  let F : Ω[S⁄Λ] →ₗ[R] (⋀[R]^(t+1) Ω[R⁄Λ]) :=
    (traceFromPresentation hp.pos a e).comp
      ((exteriorSnocLinear (K := S) (u ∘ η)).restrictScalars R)
  let G : Ω[S⁄Λ] →ₗ[R] (⋀[R]^(t+1) Ω[R⁄Λ]) :=
    (exteriorSnocLinear (K := R) η).comp
      ((rootDifferentialTrace hp a e).comp
        ((KaehlerDifferential.map Λ R S S).restrictScalars R))
  have hb (ζ : Ω[R⁄Λ]) : KaehlerDifferential.map Λ R S S (u ζ) = 0 := by
    have h := (KaehlerDifferential.exact_mapBaseChange_map Λ R S
      (KaehlerDifferential.mapBaseChange Λ R S ((1 : S) ⊗ₜ[R] ζ))).mpr
        ⟨(1 : S) ⊗ₜ[R] ζ, rfl⟩
    simpa [KaehlerDifferential.mapBaseChange_tmul, u] using h
  have hbase (s : S) (ζ : Ω[R⁄Λ]) : F (s • u ζ) = G (s • u ζ) := by
    change traceFromPresentation hp.pos a e
      (exteriorPower.ιMulti S (t+1) (Fin.snoc (u ∘ η) (s • u ζ))) = _
    rw [exterior_snoc_smul]
    have heq : Fin.snoc (u ∘ η) (u ζ) = u ∘ Fin.snoc η ζ := (Fin.comp_snoc u η ζ).symm
    rw [heq]
    dsimp only [u, Function.comp_def]
    rw [traceFromPresentation_smul_baseForm]
    change 0 = exteriorSnocLinear η (rootDifferentialTrace hp a e
      (KaehlerDifferential.map Λ R S S (s • u ζ)))
    rw [map_smul, hb, smul_zero, map_zero, map_zero]
  have hroot (s : S) : F (s • x) = G (s • x) := by
    change traceFromPresentation hp.pos a e
      (exteriorPower.ιMulti S (t+1) (Fin.snoc (u ∘ η) (s • x))) = _
    dsimp only [u, x, Function.comp_def]
    rw [traceFromPresentation_apply_snoc]
    change _ = exteriorSnocLinear η (rootDifferentialTrace hp a e
      (KaehlerDifferential.map Λ R S S (s • x)))
    rw [map_smul, KaehlerDifferential.map_D, Algebra.algebraMap_self_apply]
    rw [rootDifferentialTrace_eq_coefficient, map_smul]
    rfl
  have hFG : F = G := by
    refine linearMap_eq_of_span_smul _ (pthRootAbsoluteDifferentials_span a e) F G ?_
    rintro s _ (⟨ζ, rfl⟩ | rfl)
    · exact hbase s ζ
    · exact hroot s
  exact DFunLike.congr_fun hFG ω

/-- An equality in an `R`-module may be checked when `R` is nontrivial of characteristic `p`. -/
private theorem eq_of_nontrivial_charP {M : Type*} [AddCommGroup M] [Module R M]
    (hp : p.Prime) [CharP Λ p] {x y : M} (h : ∀ [Nontrivial R] [CharP R p], x = y) : x = y := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact (Module.subsingleton R M).elim _ _
  · let : CharP R p := charP_algebra_of_prime (Λ := Λ) hp
    exact h

/-- The higher trace on differential forms for a presentation
`S ≅ R[X]/(X ^ p - a)`. -/
@[stacks 0AX5 "the trace map"]
public noncomputable def higherTrace (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C a) ≃ₐ[R] S) :
    (⋀[S]^(t + 1) (Ω[S⁄Λ])) →ₗ[R] (⋀[R]^(t + 1) (Ω[R⁄Λ]))  := by
  classical
  by_cases h : Nontrivial R
  · letI := h
    letI : CharP R p := charP_algebra_of_prime (Λ := Λ) hp
    exact traceFromPresentation hp.pos a e
  · exact 0

/-- Over a nontrivial base the higher trace is the trace attached to the given presentation. -/
private theorem higherTrace_eq_traceFromPresentation [Nontrivial R] [CharP R p]
    (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) :
    higherTrace (t := t) (Λ := Λ) hp a e = traceFromPresentation hp.pos a e := by
  classical
  simp only [higherTrace, dite_eq_left (inferInstance : Nontrivial R)]


/-- The higher trace of `η₁ ∧ ⋯ ∧ ηₜ ∧ xⁱ dx` vanishes for `i ≤ p - 2`. -/
@[stacks 0AX5 "values below the top power"]
public theorem higherTrace_apply_of_le (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C a) ≃ₐ[R] S) (i : ℕ)
    (hi : i ≤ p - 2) (η : Fin t → Ω[R⁄Λ]) :
    higherTrace (t := t) hp a e
      (exteriorPower.ιMulti S (t + 1)
        (Fin.snoc (fun j => KaehlerDifferential.map Λ Λ R S (η j))
          ((e (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C a))) ^ i •
            KaehlerDifferential.D Λ S
              (e (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C a)))))) = 0 := by
  refine eq_of_nontrivial_charP (R := R) (Λ := Λ) hp ?_
  intro _ _
  have hp2 := hp.two_le
  rw [higherTrace_eq_traceFromPresentation, traceFromPresentation_apply_snoc,
    rootCoefficient_pow hp.pos a e i (by omega)]
  simp [show i ≠ p - 1 by omega]

/-- The higher trace of `η₁ ∧ ⋯ ∧ ηₜ ∧ x^(p-1) dx` is
`η₁ ∧ ⋯ ∧ ηₜ ∧ da`. -/
@[stacks 0AX5 "value at the top power"]
public theorem higherTrace_apply_top (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C a) ≃ₐ[R] S)
    (η : Fin t → Ω[R⁄Λ]) :
    higherTrace (t := t) hp a e
      (exteriorPower.ιMulti S (t + 1)
        (Fin.snoc (fun j => KaehlerDifferential.map Λ Λ R S (η j))
          ((e (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C a))) ^ (p - 1) •
            KaehlerDifferential.D Λ S
              (e (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C a)))))) =
      exteriorPower.ιMulti R (t + 1)
        (Fin.snoc η (KaehlerDifferential.D Λ R a)) := by
  refine eq_of_nontrivial_charP (R := R) (Λ := Λ) hp ?_
  intro _ _
  rw [higherTrace_eq_traceFromPresentation, traceFromPresentation_apply_snoc,
    rootCoefficient_pow hp.pos a e (p-1) (by have := hp.pos; omega)]
  simp

/-- The higher trace annihilates the image of
`S ⊗[R] Ω^{t+1}_{R/Λ} → Ω^{t+1}_{S/Λ}`.  The displayed elements are a generating family for
that image. -/
@[stacks 0AX5 "vanishing on forms from the base"]
public theorem higherTrace_smul_baseForm (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C a) ≃ₐ[R] S) (s : S)
    (η : Fin (t + 1) → Ω[R⁄Λ]) :
    higherTrace (t := t) hp a e
      (s • exteriorPower.ιMulti S (t + 1)
        (fun j => KaehlerDifferential.map Λ Λ R S (η j))) = 0 := by
  refine eq_of_nontrivial_charP (R := R) (Λ := Λ) hp ?_
  intro _ _
  rw [higherTrace_eq_traceFromPresentation]
  exact traceFromPresentation_smul_baseForm hp.pos a e s η

/-- The higher trace is independent of the presentation of `S` as an algebra obtained by
adjoining a `p`-th root. In particular, changing the chosen generator does not change the
canonical trace on higher relative differential forms. -/
@[stacks 0AX5 "independence of presentation"]
public theorem higherTrace_eq_of_presentations (hp : p.Prime) [CharP Λ p]
    (a b : R)
    (e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C a) ≃ₐ[R] S)
    (f : AdjoinRoot (Polynomial.X ^ p - Polynomial.C b) ≃ₐ[R] S) :
    higherTrace (t := t) (Λ := Λ) hp a e =
      higherTrace (t := t) (Λ := Λ) hp b f := by
  refine eq_of_nontrivial_charP (R := R) (Λ := Λ) hp ?_
  intro _ _
  rw [higherTrace_eq_traceFromPresentation, higherTrace_eq_traceFromPresentation]
  apply exterior_ext_of_span t (KaehlerDifferential.map Λ Λ R S)
    (KaehlerDifferential.D Λ S (e (AdjoinRoot.root (X ^ p - C a))))
    (pthRootAbsoluteDifferentials_span a e)
  · intro s η
    dsimp only [Function.comp_def]
    rw [traceFromPresentation_smul_baseForm, traceFromPresentation_smul_baseForm]
  · intro s η
    dsimp only [Function.comp_def]
    rw [traceFromPresentation_snoc_arbitrary hp a e,
      traceFromPresentation_snoc_arbitrary hp b f,
      rootDifferentialTrace_eq_of_presentations hp a b e f]

end KaehlerDifferential

end
