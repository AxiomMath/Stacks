module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.Smooth.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Smooth.Conormal

/-!
# The naive cotangent complex and smoothness of a symmetric algebra

Let `A` be a commutative ring and `M` an `A`-module. This file computes the naive cotangent
complex of the symmetric algebra `C = Sym_A(M)` and deduces that `A → C` is smooth exactly when
`M` is finite projective.

Presenting `M` as the cokernel of `K → Aᵐ` gives a presentation `A[y_1, …, y_m] → C`, and the
computation identifies its conormal module with `C ⊗[A] K` and the differentials with `Cᵐ`, so
that `Ω[C⁄A] = C ⊗[A] M`. The smoothness criterion then falls out: the augmentation ideal `J` of
`C` has `J ⧸ J²  = M`, so smoothness forces `M` finite projective; conversely a finite projective
`M` splits `K → Aᵐ → M`, which makes the naive cotangent complex quasi-isomorphic to `C ⊗[A] M`
in degree zero.

## Main results

* `cotangentComplex_of_isSymmetricAlgebra`: the conormal module and the differentials of the
  polynomial presentation of a symmetric algebra, with the canonical maps pinned down.
* `symmetricAlgebra_smooth_iff_finite_projective`: `Sym_A(M)` is smooth over `A` if and only if
  `M` is a finite projective `A`-module.

## Implementation notes

The computation is graded: in degree `d` the kernel of `Sym^d(Aᵐ) → Sym^d(M)` is the image of
`K ⊗ Sym^{d-1}(Aᵐ)`, so the conormal module in degree `d` is `K ⊗ Sym^{d-1}(M)`, which assembles
to `C ⊗[A] K`. The two `open` groups below are kept in separate sections: the cotangent
computation works with `Module` open, while the smoothness criterion works with `Function` open,
and opening both at once makes `Surjective` ambiguous.

## References

* [Stacks Project, Tag 07EV](https://stacks.math.columbia.edu/tag/07EV)
* [Stacks Project, Tag 07M6](https://stacks.math.columbia.edu/tag/07M6)
-/

@[expose] public section

section CotangentComplex

open TensorProduct Module

universe uA uK uM uC

private noncomputable def symmetricDerivation
    {A : Type uA} {M : Type uM} {C : Type uC}
    [CommRing A] [AddCommGroup M] [Module A M] [CommRing C] [Algebra A C]
    (ι : M →ₗ[A] C) (hC : IsSymmetricAlgebra ι) :
    Derivation A C (C ⊗[A] M) := by
  let f : M →ₗ[A] TrivSqZeroExt C (C ⊗[A] M) :=
    (TrivSqZeroExt.inlAlgHom A C (C ⊗[A] M)).toLinearMap ∘ₗ ι +
      (TrivSqZeroExt.inrHom (R := C) (M := C ⊗[A] M)).restrictScalars A ∘ₗ
        (TensorProduct.mk A C M 1)
  let φ : C →ₐ[A] TrivSqZeroExt C (C ⊗[A] M) := hC.lift f
  have hfst (c : C) : (φ c).fst = c := by
    have heq : (TrivSqZeroExt.fstHom A C (C ⊗[A] M)).comp φ = AlgHom.id A C := by
      apply hC.algHom_ext
      ext x
      simp [φ, f]
    exact AlgHom.congr_fun heq c
  refine { toFun := fun c => (φ c).snd
           map_add' := ?_
           map_smul' := ?_
           map_one_eq_zero' := ?_
           leibniz' := ?_ }
  · intro x y
    simp only [map_add, TrivSqZeroExt.snd_add]
  · intro a x
    simp only [map_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply]
  · change (φ 1).snd = 0
    simp
  · intro x y
    change (φ (x * y)).snd = x • (φ y).snd + y • (φ x).snd
    simp only [map_mul, TrivSqZeroExt.snd_mul, hfst]
    simp only [op_smul_eq_smul]

private theorem symmetricDerivation_ι
    {A : Type uA} {M : Type uM} {C : Type uC}
    [CommRing A] [AddCommGroup M] [Module A M] [CommRing C] [Algebra A C]
    (ι : M →ₗ[A] C) (hC : IsSymmetricAlgebra ι) (x : M) :
    symmetricDerivation ι hC (ι x) = 1 ⊗ₜ[A] x := by
  simp [symmetricDerivation, IsSymmetricAlgebra.lift_eq,
    TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr]

private noncomputable def symmetricKaehlerEquiv
    {A : Type uA} {M : Type uM} {C : Type uC}
    [CommRing A] [AddCommGroup M] [Module A M] [CommRing C] [Algebra A C]
    (ι : M →ₗ[A] C) (hC : IsSymmetricAlgebra ι) :
    KaehlerDifferential A C ≃ₗ[C] C ⊗[A] M := by
  let dι : M →ₗ[A] KaehlerDifferential A C :=
    { toFun := fun x => KaehlerDifferential.D A C (ι x)
      map_add' x y := by simp
      map_smul' a x := by simp }
  let f : C ⊗[A] M →ₗ[C] KaehlerDifferential A C := dι.liftBaseChange C
  let g : KaehlerDifferential A C →ₗ[C] C ⊗[A] M :=
    (symmetricDerivation ι hC).liftKaehlerDifferential
  refine { __ := g, invFun := f, left_inv := ?_, right_inv := ?_ }
  · intro w
    let D := KaehlerDifferential.D A C
    have h : (f ∘ₗ g).compDer D = D := by
      apply Derivation.ext
      intro x
      induction x using hC.induction with
      | algebraMap a => simp [D]
      | ι x => simp [f, g, dι, D, symmetricDerivation_ι]
      | mul x y hx hy =>
        simp only [Derivation.leibniz, hx, hy]
      | add x y hx hy => simp only [map_add, hx, hy]
    have h' : f ∘ₗ g = LinearMap.id :=
      Derivation.liftKaehlerDifferential_unique _ _ (by
        ext x
        exact congrArg (fun d : Derivation A C (KaehlerDifferential A C) => d x) h)
    exact LinearMap.congr_fun h' w
  · intro w
    induction w using TensorProduct.induction_on with
    | zero => simp [f, g]
    | tmul c x =>
      simp [f, g, dι, symmetricDerivation_ι, TensorProduct.smul_tmul']
    | add x y hx hy =>
      change g (f (x + y)) = x + y
      rw [map_add, map_add]
      change g (f x) = x at hx
      change g (f y) = y at hy
      rw [hx, hy]

private noncomputable def freeLinear
    {A : Type uA} [CommRing A] (m : ℕ) :
    (Fin m → A) →ₗ[A] MvPolynomial (Fin m) A :=
  (Pi.basisFun A (Fin m)).constr A MvPolynomial.X

private theorem freeLinear_apply
    {A : Type uA} [CommRing A] (m : ℕ) (x : Fin m → A) :
    freeLinear m x = ∑ j, MvPolynomial.C (x j) * MvPolynomial.X j := by
  simp [freeLinear, Basis.constr_apply_fintype, Pi.basisFun_equivFun,
    Algebra.smul_def]

private theorem freeLinear_basis
    {A : Type uA} [CommRing A] (m : ℕ) (j : Fin m) :
    freeLinear m ((Pi.basisFun A (Fin m)) j) = MvPolynomial.X j := by
  simp [freeLinear]

private theorem ker_presentation_eq_span_linearRelations
    {A : Type uA} {K : Type uK} {M : Type uM} {C : Type uC}
    [CommRing A] [AddCommGroup K] [Module A K]
    [AddCommGroup M] [Module A M] [CommRing C] [Algebra A C]
    (m : ℕ) (i : K →ₗ[A] (Fin m → A)) (p : (Fin m → A) →ₗ[A] M)
    (hip : Function.Exact i p) (hp : Function.Surjective p)
    (ι : M →ₗ[A] C) (hC : IsSymmetricAlgebra ι)
    (α : MvPolynomial (Fin m) A →ₐ[A] C)
    (hαX : ∀ j, α (MvPolynomial.X j) = ι (p ((Pi.basisFun A (Fin m)) j))) :
    RingHom.ker α.toRingHom = Ideal.span (Set.range (fun k : K => freeLinear m (i k))) := by
  let J : Ideal (MvPolynomial (Fin m) A) :=
    Ideal.span (Set.range (fun k : K => freeLinear m (i k)))
  let q : MvPolynomial (Fin m) A →ₐ[A] MvPolynomial (Fin m) A ⧸ J :=
    Ideal.Quotient.mkₐ A J
  let qlin : (Fin m → A) →ₗ[A] MvPolynomial (Fin m) A ⧸ J :=
    q.toLinearMap ∘ₗ freeLinear m
  have hqi (k : K) : q (freeLinear m (i k)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨k, rfl⟩)
  have hker : p.ker ≤ qlin.ker := by
    rw [hip.linearMap_ker_eq]
    rintro x ⟨k, rfl⟩
    exact hqi k
  let g : M →ₗ[A] MvPolynomial (Fin m) A ⧸ J :=
    (p.ker.liftQ qlin hker) ∘ₗ (p.quotKerEquivOfSurjective hp).symm.toLinearMap
  have hg (x : Fin m → A) : g (p x) = q (freeLinear m x) := by
    simp [g, qlin]
  let φ : C →ₐ[A] MvPolynomial (Fin m) A ⧸ J := hC.lift g
  have hcomp : φ.comp α = q := by
    apply MvPolynomial.algHom_ext
    intro j
    show φ (α (MvPolynomial.X j)) = q (MvPolynomial.X j)
    rw [hαX, show φ (ι (p ((Pi.basisFun A (Fin m)) j))) =
      g (p ((Pi.basisFun A (Fin m)) j)) from hC.lift_eq g _, hg,
      freeLinear_basis]
  have hαL : α.toLinearMap ∘ₗ freeLinear m = ι ∘ₗ p := by
    apply (Pi.basisFun A (Fin m)).ext
    intro j
    show α (freeLinear m ((Pi.basisFun A (Fin m)) j)) =
      ι (p ((Pi.basisFun A (Fin m)) j))
    rw [freeLinear_basis, hαX]
  apply le_antisymm
  · intro x hx
    have : q x = 0 := by
      rw [← hcomp]
      exact map_zero φ ▸ congrArg φ (RingHom.mem_ker.mp hx)
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  · apply Ideal.span_le.mpr
    rintro x ⟨k, rfl⟩
    show α (freeLinear m (i k)) = 0
    have h := LinearMap.congr_fun hαL (i k)
    simpa [hip.apply_apply_eq_zero] using h

/-- **Stacks 07EV.** Let `0 → K → Aᵐ → M → 0` be exact and let `C` be the symmetric algebra on
`M`. For the induced polynomial presentation of `C`, there is a canonical surjection
`C ⊗[A] K → P.Cotangent` compatible with the map into `Cᵐ`, and `Ω[C⁄A]` is canonically
`C ⊗[A] M`. The last three conditions pin down the canonical maps: polynomial differentials go to
the standard basis, `1 ⊗ₜ k` goes to the conormal class of its linear relation, and the
differential of a symmetric-algebra generator goes to `1 ⊗ₜ x`. -/
@[stacks 07EV]
theorem cotangentComplex_of_isSymmetricAlgebra
    {A : Type uA} {K : Type uK} {M : Type uM} [CommRing A]
    [AddCommGroup K] [Module A K] [AddCommGroup M] [Module A M]
    (m : ℕ) (i : K →ₗ[A] (Fin m → A)) (p : (Fin m → A) →ₗ[A] M)
    (_hi : Function.Injective i) (hip : Function.Exact i p) (hp : Function.Surjective p)
    (C : Type uC) [CommRing C] [Algebra A C]
    (ι : M →ₗ[A] C) (hC : IsSymmetricAlgebra ι)
    (α : MvPolynomial (Fin m) A →ₐ[A] C) (hα : Function.Surjective α)
    (hαX : ∀ j, α (MvPolynomial.X j) = ι (p ((Pi.basisFun A (Fin m)) j))) :
    let P := Algebra.Extension.ofSurjective α hα
    ∃ (eK : C ⊗[A] K →ₗ[C] P.Cotangent)
      (eF : P.CotangentSpace ≃ₗ[C] (Fin m → C))
      (eΩ : KaehlerDifferential A C ≃ₗ[C] C ⊗[A] M),
      Function.Surjective eK ∧
        eF.toLinearMap ∘ₗ P.cotangentComplex ∘ₗ eK =
          (TensorProduct.piScalarRight A C C (Fin m)).toLinearMap ∘ₗ i.baseChange C ∧
        (∀ j, eF (1 ⊗ₜ[P.Ring]
          KaehlerDifferential.D A P.Ring (MvPolynomial.X j)) = Pi.single j 1) ∧
        (∀ k, ∃ hk : (∑ j, MvPolynomial.C (i k j) * MvPolynomial.X j) ∈ P.ker,
          eK (1 ⊗ₜ k) = Algebra.Extension.Cotangent.mk
            ⟨∑ j, MvPolynomial.C (i k j) * MvPolynomial.X j, hk⟩) ∧
        ∀ x, eΩ (KaehlerDifferential.D A C (ι x)) = 1 ⊗ₜ x := by
  let P := Algebra.Extension.ofSurjective α hα
  let : Algebra (MvPolynomial (Fin m) A) C := α.toAlgebra
  let b : Basis (Fin m) C P.CotangentSpace :=
    (KaehlerDifferential.mvPolynomialBasis A (Fin m)).baseChange C
  let eF : P.CotangentSpace ≃ₗ[C] (Fin m → C) :=
    b.repr.trans (Finsupp.linearEquivFunOnFinite C C (Fin m))
  have heF (j : Fin m) :
      eF (1 ⊗ₜ[P.Ring] KaehlerDifferential.D A P.Ring (MvPolynomial.X j)) =
        Pi.single j 1 := by
    have hb : b j = 1 ⊗ₜ[P.Ring] KaehlerDifferential.D A P.Ring (MvPolynomial.X j) := by
      show ((KaehlerDifferential.mvPolynomialBasis A (Fin m)).baseChange C) j = _
      rw [Basis.baseChange_apply, KaehlerDifferential.mvPolynomialBasis_apply]
      rfl
    rw [← hb]
    simp [eF]
  have hJ : Ideal.span (Set.range (fun k : K => freeLinear m (i k))) = P.ker :=
    (ker_presentation_eq_span_linearRelations m i p hip hp ι hC α hαX).symm
  let rel : K →ₗ[A] P.ker := {
    toFun := fun k => ⟨freeLinear m (i k), hJ.le (Ideal.subset_span ⟨k, rfl⟩)⟩
    map_add' := by intro x y; apply Subtype.ext; simp; rfl
    map_smul' := by intro a x; apply Subtype.ext; simp; rfl
  }
  let relCot : K →ₗ[A] P.Cotangent :=
    ((Algebra.Extension.Cotangent.mk (P := P)).restrictScalars A).comp rel
  let eK : C ⊗[A] K →ₗ[C] P.Cotangent := relCot.liftBaseChange C
  have heK (k : K) : eK (1 ⊗ₜ[A] k) = Algebra.Extension.Cotangent.mk (rel k) := by
    simp [eK, relCot]
  have hD (x : Fin m → A) :
      eF (1 ⊗ₜ[P.Ring] KaehlerDifferential.D A P.Ring (freeLinear m x)) =
        (TensorProduct.piScalarRight A C C (Fin m)) (1 ⊗ₜ[A] x) := by
    let lhs : (Fin m → A) →ₗ[A] (Fin m → C) :=
      (eF.toLinearMap.restrictScalars A).comp
        (((TensorProduct.mk P.Ring C (KaehlerDifferential A P.Ring) 1).restrictScalars A).comp
          ((KaehlerDifferential.D A P.Ring).toLinearMap.comp (freeLinear m)))
    let rhs : (Fin m → A) →ₗ[A] (Fin m → C) :=
      ((TensorProduct.piScalarRight A C C (Fin m)).toLinearMap.restrictScalars A).comp
        (TensorProduct.mk A C (Fin m → A) 1)
    have heq : lhs = rhs := by
      apply (Pi.basisFun A (Fin m)).ext
      intro j
      show eF (1 ⊗ₜ[P.Ring]
        KaehlerDifferential.D A P.Ring (freeLinear m ((Pi.basisFun A (Fin m)) j))) =
        (TensorProduct.piScalarRight A C C (Fin m))
          (1 ⊗ₜ[A] ((Pi.basisFun A (Fin m)) j))
      rw [freeLinear_basis, heF, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul]
      ext t
      simp [Pi.basisFun_apply, Pi.single_apply]
    exact LinearMap.congr_fun heq x
  refine ⟨eK, eF, symmetricKaehlerEquiv ι hC, ?_, ?_, heF, ?_, ?_⟩
  · have hspan : Submodule.span C
        (Set.range (fun k : K => Algebra.Extension.Cotangent.mk (rel k))) = ⊤ := by
      convert (Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker
        (P := P) (fun k : K => freeLinear m (i k)) hJ) using 1
    have hle : Submodule.span C
        (Set.range (fun k : K => Algebra.Extension.Cotangent.mk (rel k))) ≤
          eK.range := by
      apply Submodule.span_le.mpr
      rintro x ⟨k, rfl⟩
      exact ⟨1 ⊗ₜ[A] k, heK k⟩
    exact LinearMap.range_eq_top.mp (top_unique (hspan ▸ hle))
  · apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul c k =>
      have hbase :
          (eF.toLinearMap ∘ₗ P.cotangentComplex ∘ₗ eK) (1 ⊗ₜ[A] k) =
            ((TensorProduct.piScalarRight A C C (Fin m)).toLinearMap ∘ₗ i.baseChange C)
              (1 ⊗ₜ[A] k) := by
        show eF (P.cotangentComplex (eK (1 ⊗ₜ[A] k))) =
          (TensorProduct.piScalarRight A C C (Fin m))
            ((i.baseChange C) (1 ⊗ₜ[A] k))
        rw [heK, Algebra.Extension.cotangentComplex_mk, LinearMap.baseChange_tmul]
        exact hD (i k)
      have htmul : c ⊗ₜ[A] k = c • (1 ⊗ₜ[A] k) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [htmul]
      simpa only [map_smul] using congrArg (c • ·) hbase
  · intro k
    refine ⟨?_, ?_⟩
    · have hk' : freeLinear m (i k) ∈ P.ker := (rel k).property
      rwa [freeLinear_apply] at hk'
    · show eK (1 ⊗ₜ[A] k) = Algebra.Extension.Cotangent.mk (P := P)
        ⟨∑ j, MvPolynomial.C (i k j) * MvPolynomial.X j, _⟩
      convert heK k using 1
      congr 1
      apply Subtype.ext
      exact (freeLinear_apply m (i k)).symm
  · intro x
    simp [symmetricKaehlerEquiv, symmetricDerivation_ι]

end CotangentComplex

section Smooth

open Function

universe u v

@[ega "0 19.3.2", ega "0 19.5.4.4" "partial"]
private theorem symmetricAlgebra_formallySmooth_of_projective
    (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
    [Module.Projective A M] : Algebra.FormallySmooth A (SymmetricAlgebra A M) := by
  apply Algebra.FormallySmooth.of_comp_surjective
  intro B _ _ I hI f
  let q : B →ₗ[A] B ⧸ I := (Ideal.Quotient.mkₐ A I).toLinearMap
  obtain ⟨g, hg⟩ := Module.projective_lifting_property q
    (f.toLinearMap ∘ₗ SymmetricAlgebra.ι A M) Ideal.Quotient.mk_surjective
  exact ⟨SymmetricAlgebra.lift g, SymmetricAlgebra.algHom_ext <| LinearMap.ext fun x => by
    simpa [q] using LinearMap.congr_fun hg x⟩

set_option maxHeartbeats 800000 in
-- The induction on polynomials elaborates a large ideal-membership calculation.
private theorem symmetricAlgebra_finitePresentation_of_finite_projective
    (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] :
    Algebra.FinitePresentation A (SymmetricAlgebra A M) := by
  classical
  obtain ⟨n, p, i, hp, hi, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  let α : MvPolynomial (Fin n) A →ₐ[A] SymmetricAlgebra A M :=
    MvPolynomial.aeval (fun j => SymmetricAlgebra.ι A M (p ((Pi.basisFun A (Fin n)) j)))
  let β : SymmetricAlgebra A M →ₐ[A] MvPolynomial (Fin n) A :=
    SymmetricAlgebra.lift
      ((Pi.basisFun A (Fin n)).constr A MvPolynomial.X ∘ₗ i)
  have hαbasis : α.toLinearMap ∘ₗ (Pi.basisFun A (Fin n)).constr A MvPolynomial.X =
      SymmetricAlgebra.ι A M ∘ₗ p := by
    apply (Pi.basisFun A (Fin n)).ext
    intro j
    simp [α]
  have hαβ : α.comp β = AlgHom.id A _ := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply]
    show α (β (SymmetricAlgebra.ι A M x)) = SymmetricAlgebra.ι A M x
    rw [SymmetricAlgebra.lift_ι_apply]
    simp only [LinearMap.comp_apply]
    have hx := LinearMap.congr_fun hαbasis (i x)
    simp only [LinearMap.comp_apply] at hx
    calc
      α ((Pi.basisFun A (Fin n)).constr A MvPolynomial.X (i x)) =
          SymmetricAlgebra.ι A M (p (i x)) := hx
      _ = SymmetricAlgebra.ι A M x := by
        have := LinearMap.congr_fun hpi x
        simpa using congrArg (SymmetricAlgebra.ι A M) this
  have hα : Function.Surjective α := fun x => ⟨β x, AlgHom.congr_fun hαβ x⟩
  let e : MvPolynomial (Fin n) A →ₐ[A] MvPolynomial (Fin n) A := β.comp α
  let gens : Fin n → MvPolynomial (Fin n) A := fun j => MvPolynomial.X j - e (MvPolynomial.X j)
  have hker : RingHom.ker α.toRingHom = Ideal.span (Set.range gens) := by
    apply le_antisymm
    · intro x hx
      have hall : ∀ z : MvPolynomial (Fin n) A, z - e z ∈ Ideal.span (Set.range gens) := by
        intro z
        induction z using MvPolynomial.induction_on with
        | C a => simp [e, α, β]
        | add p q hp' hq' =>
            simpa [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              (Ideal.add_mem _ hp' hq')
        | mul_X p j hp' =>
            rw [map_mul]
            have hj : MvPolynomial.X j - e (MvPolynomial.X j) ∈
                Ideal.span (Set.range gens) := Ideal.subset_span ⟨j, rfl⟩
            have hdecomp : p * MvPolynomial.X j - e p * e (MvPolynomial.X j) =
                (p - e p) * MvPolynomial.X j + e p * (MvPolynomial.X j - e (MvPolynomial.X j)) := by
              ring
            rw [hdecomp]
            exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp') (Ideal.mul_mem_left _ _ hj)
      have he0 : e x = 0 := by
        change α x = 0 at hx
        simp [e, hx]
      simpa [he0] using hall x
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      show α (MvPolynomial.X j - e (MvPolynomial.X j)) = 0
      rw [map_sub]
      apply sub_eq_zero.mpr
      exact (AlgHom.congr_fun hαβ (α (MvPolynomial.X j))).symm
  refine ⟨n, α, hα, ?_⟩
  rw [hker]
  exact Submodule.fg_span (Set.finite_range gens)

-- The augmentation conormal is canonically the module of degree-one generators.
private theorem augmentation_conormal_finite_projective
    (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
    (h : Algebra.Smooth A (SymmetricAlgebra A M)) :
    Module.Finite A M ∧ Module.Projective A M := by
  let S := SymmetricAlgebra A M
  let σ : S →ₐ[A] A := SymmetricAlgebra.algebraMapInv
  let I : Ideal S := RingHom.ker σ
  let : Module Aᵐᵒᵖ M :=
    Module.compHom M (RingEquiv.toOpposite A).symm.toRingHom
  let : IsCentralScalar A M := ⟨fun _ _ => rfl⟩
  let τ : S →ₐ[A] TrivSqZeroExt A M :=
    SymmetricAlgebra.lift (TrivSqZeroExt.inrHom A M)
  have hfst : (TrivSqZeroExt.fstHom A A M).comp τ = σ :=
    SymmetricAlgebra.algHom_ext <| LinearMap.ext fun x => by
      simp [τ, σ, SymmetricAlgebra.algebraMapInv]
  let j : M →ₗ[A] I :=
    { toFun := fun x => ⟨SymmetricAlgebra.ι A M x, by
          show σ (SymmetricAlgebra.ι A M x) = 0
          exact SymmetricAlgebra.algebraMapInv_ι x⟩
      map_add' x y := Subtype.ext (by simp)
      map_smul' r x := Subtype.ext (by simp) }
  let d : I →ₗ[A] M :=
    (TrivSqZeroExt.sndHom A M).comp
      (τ.toLinearMap.comp (I.subtype.restrictScalars A))
  have hd (x y : I) : d (x * y) = 0 := by
    show (τ ((x : S) * (y : S))).snd = 0
    rw [map_mul, TrivSqZeroExt.snd_mul]
    have hx : (τ (x : S)).fst = 0 :=
      (AlgHom.congr_fun hfst (x : S)).trans (RingHom.mem_ker.mp x.property)
    have hy : (τ (y : S)).fst = 0 :=
      (AlgHom.congr_fun hfst (y : S)).trans (RingHom.mem_ker.mp y.property)
    simp [hx, hy]
  let fromC : I.Cotangent →ₗ[A] M := Ideal.Cotangent.lift d hd
  let toC : M →ₗ[A] I.Cotangent := I.toCotangent.restrictScalars A ∘ₗ j
  have hsplit : fromC ∘ₗ toC = LinearMap.id := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearMap.coe_mk, AddHom.coe_mk,
      comp_apply, Ideal.Cotangent.lift_toCotangent, AlgHom.coe_toLinearMap, Submodule.coe_subtype,
      TrivSqZeroExt.sndHom_apply, LinearMap.id_coe, id_eq, fromC, d, τ, toC, j]
    rw [SymmetricAlgebra.lift_ι_apply]
    rfl
  have hc := conormal_finite_projective σ h
  let : Module.Finite A I.Cotangent := hc.1
  let : Module.Projective A I.Cotangent := hc.2
  exact ⟨Module.Finite.of_surjective fromC fun x =>
      ⟨toC x, by simpa using LinearMap.congr_fun hsplit x⟩,
    Module.Projective.of_split toC fromC hsplit⟩

/-- **Stacks 07M6.** The symmetric algebra of an `A`-module `M` is smooth over `A` if and only if
`M` is finite projective. -/
@[stacks 07M6, ega "0 19.3.2" "special case"]
theorem symmetricAlgebra_smooth_iff_finite_projective
    (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M] :
    Algebra.Smooth A (SymmetricAlgebra A M) ↔
      Module.Finite A M ∧ Module.Projective A M := by
  constructor
  · exact augmentation_conormal_finite_projective A M
  · rintro ⟨_, _⟩
    exact
      { formallySmooth := symmetricAlgebra_formallySmooth_of_projective A M
        finitePresentation := symmetricAlgebra_finitePresentation_of_finite_projective A M }

end Smooth
