module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Substitution
public import StacksFrontier.RingTheory.DiscreteValuationRing.BaseChangeClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Galois action after extending the fraction field

For a finite normal extension `K₁ / K`, the automorphism group of `K₁ / K` acts compatibly on the
reduced base change and on the integral closures, transitively on maximal ideals (Tag 09EU).
-/

@[expose] public section

open scoped Pointwise TensorProduct

universe uk uA uB uK uL uK₁ uL₁ uA₁ uB₁ v u

namespace IsDiscreteValuationRing

/-! ### Galois action after extending fraction fields -/

private theorem nilradical_map_algEquiv {K T : Type*} [CommRing K] [CommRing T]
    [Algebra K T] (e : T ≃ₐ[K] T) :
    nilradical T = Ideal.map (e : T →+* T) (nilradical T) := by
  simp only [nilradical]
  rw [Ideal.map_radical_of_surjective e.surjective (by simp)]
  simp

private def quotientNilradicalAut {K T : Type*} [CommRing K] [CommRing T]
    [Algebra K T] (e : T ≃ₐ[K] T) :
    (T ⧸ nilradical T) ≃ₐ[K] (T ⧸ nilradical T) :=
  Ideal.quotientEquivAlg (nilradical T) (nilradical T) e (nilradical_map_algEquiv e)

private theorem quotientNilradicalAut_mk {K T : Type*} [CommRing K] [CommRing T]
    [Algebra K T] (e : T ≃ₐ[K] T) (x : T) :
    quotientNilradicalAut e (Ideal.Quotient.mk (nilradical T) x) =
      Ideal.Quotient.mk (nilradical T) (e x) :=
  Ideal.quotientEquivAlg_mk (nilradical T) e (nilradical_map_algEquiv e) x

private def quotientNilradicalAutHom {K T G : Type*} [CommRing K] [CommRing T]
    [Algebra K T] [Monoid G] (ρ : G →* (T ≃ₐ[K] T)) :
    G →* ((T ⧸ nilradical T) ≃ₐ[K] (T ⧸ nilradical T)) where
  toFun g := quotientNilradicalAut (ρ g)
  map_one' := by
    apply AlgEquiv.ext
    intro x
    induction x using Quotient.inductionOn with
    | _ x =>
      change quotientNilradicalAut (ρ 1) (Ideal.Quotient.mk (nilradical T) x) =
        Ideal.Quotient.mk (nilradical T) x
      simp [quotientNilradicalAut_mk]
  map_mul' g h := by
    apply AlgEquiv.ext
    intro x
    induction x using Quotient.inductionOn with
    | _ x =>
      change quotientNilradicalAut (ρ (g * h)) (Ideal.Quotient.mk (nilradical T) x) =
        quotientNilradicalAut (ρ g)
          (quotientNilradicalAut (ρ h) (Ideal.Quotient.mk (nilradical T) x))
      simp [quotientNilradicalAut_mk, map_mul]

private def tensorAut {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] (g : E ≃ₐ[K] E) :
    (L ⊗[K] E) ≃ₐ[L] (L ⊗[K] E) :=
  AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := L)) g).toRingEquiv)
    (by
      intro l
      rw [Algebra.TensorProduct.algebraMap_apply]
      simp [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul])

private theorem tensorAut_tmul {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] (g : E ≃ₐ[K] E) (l : L) (e : E) :
    tensorAut (L := L) g (l ⊗ₜ[K] e) = l ⊗ₜ[K] (g e) := by
  simp [tensorAut, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]

private def tensorAutHom {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] :
    (E ≃ₐ[K] E) →* ((L ⊗[K] E) ≃ₐ[L] (L ⊗[K] E)) where
  toFun := tensorAut (L := L)
  map_one' := by
    apply AlgEquiv.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l e => simp [tensorAut_tmul]
    | add x y hx hy => simp [hx, hy]
  map_mul' g h := by
    apply AlgEquiv.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l e => simp [tensorAut_tmul]
    | add x y hx hy => simp [hx, hy]

private def conjugateAlgEquivHom {R S T G : Type*} [CommSemiring R]
    [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]
    [Monoid G] (e : S ≃ₐ[R] T) (ρ : G →* (T ≃ₐ[R] T)) :
    G →* (S ≃ₐ[R] S) where
  toFun g := (e.trans (ρ g)).trans e.symm
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [map_mul]

private def integralClosureAutHom {R S G : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Monoid G] (ρ : G →* (S ≃ₐ[R] S)) :
    G →* ((integralClosure R S) ≃ₐ[R] (integralClosure R S)) where
  toFun g := (ρ g).mapIntegralClosure
  map_one' := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    simp [map_mul]

private def restrictAutHom {R K S G : Type*} [CommSemiring R] [CommSemiring K]
    [Semiring S] [Algebra R K] [Algebra K S] [Algebra R S]
    [IsScalarTower R K S] [Monoid G] (ρ : G →* (S ≃ₐ[K] S)) :
    G →* (S ≃ₐ[R] S) where
  toFun g := (ρ g).restrictScalars R
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [map_mul]

section Specific

variable (K L E M : Type*) [Field K] [Field L] [Field E] [CommRing M]
  [Algebra K L] [Algebra K E] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M]

private def reductionEquivOverL
    (e : M ≃ₐ[K] ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E)))
    (h : ∀ l : L, e (algebraMap L M l) = Ideal.Quotient.mk _
      ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] E) l)) :
    M ≃ₐ[L] ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E)) :=
  AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (by
    intro l
    calc
      e (algebraMap L M l) = Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] E) l) := h l
      _ = algebraMap L ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E)) l := rfl)

private def reductionAutHom
    (e : M ≃ₐ[K] ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E)))
    (h : ∀ l : L, e (algebraMap L M l) = Ideal.Quotient.mk _
      ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] E) l)) :
    (E ≃ₐ[K] E) →* (M ≃ₐ[L] M) :=
  conjugateAlgEquivHom (reductionEquivOverL K L E M e h)
    (quotientNilradicalAutHom (tensorAutHom (K := K) (L := L) (E := E)))

omit [IsScalarTower K L M] in
private theorem reductionAutHom_right
    [Algebra E M]
    (e : M ≃ₐ[K] ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E)))
    (hl : ∀ l : L, e (algebraMap L M l) = Ideal.Quotient.mk _
      ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] E) l))
    (hr : ∀ x : E, e (algebraMap E M x) = Ideal.Quotient.mk _
      ((Algebra.TensorProduct.includeRight : E →ₐ[K] L ⊗[K] E) x))
    (g : E ≃ₐ[K] E) (x : E) :
    reductionAutHom K L E M e hl g (algebraMap E M x) = algebraMap E M (g x) := by
  apply e.injective
  simp only [reductionAutHom, conjugateAlgEquivHom,
    MonoidHom.coe_mk, OneHom.coe_mk, AlgEquiv.trans_apply]
  have heq (y : M) : e y = reductionEquivOverL K L E M e hl y := rfl
  rw [heq, (reductionEquivOverL K L E M e hl).apply_symm_apply]
  change quotientNilradicalAut (tensorAut (L := L) g)
      (e (algebraMap E M x)) = e (algebraMap E M (g x))
  rw [hr x, hr (g x), quotientNilradicalAut_mk]
  exact congrArg (Ideal.Quotient.mk (nilradical (L ⊗[K] E)))
    (tensorAut_tmul g (1 : L) x)

end Specific

section IntegralActions

variable (A B K L E M A₁ B₁ : Type*) [CommRing A] [CommRing B]
  [Field K] [Field L] [Field E] [CommRing M] [CommRing A₁] [CommRing B₁]
  [Algebra A K] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
  [Algebra B L] [Algebra L M] [Algebra B M] [IsScalarTower B L M]
  [Algebra A A₁] [Algebra B B₁]

private def actionOnIntegralClosureA
    (eA : A₁ ≃ₐ[A] integralClosure A E) :
    (E ≃ₐ[K] E) →* (A₁ ≃ₐ[A] A₁) :=
  conjugateAlgEquivHom eA
    (integralClosureAutHom
      (restrictAutHom (R := A) (K := K) (MonoidHom.id (E ≃ₐ[K] E))))

private def actionOnIntegralClosureB
    (ρM : (E ≃ₐ[K] E) →* (M ≃ₐ[L] M))
    (eB : B₁ ≃ₐ[B] integralClosure B M) :
    (E ≃ₐ[K] E) →* (B₁ ≃ₐ[B] B₁) :=
  conjugateAlgEquivHom eB
    (integralClosureAutHom (restrictAutHom (R := B) (K := L) ρM))

private theorem actionOnIntegralClosureA_coe
    (eA : A₁ ≃ₐ[A] integralClosure A E)
    (g : E ≃ₐ[K] E) (x : A₁) :
    ((eA (actionOnIntegralClosureA A K E A₁ eA g x) : integralClosure A E) : E) =
      g ((eA x : integralClosure A E) : E) := by
  simp [actionOnIntegralClosureA, conjugateAlgEquivHom,
    integralClosureAutHom, restrictAutHom]

private theorem actionOnIntegralClosureB_coe
    (ρM : (E ≃ₐ[K] E) →* (M ≃ₐ[L] M))
    (eB : B₁ ≃ₐ[B] integralClosure B M)
    (g : E ≃ₐ[K] E) (x : B₁) :
    ((eB (actionOnIntegralClosureB (B := B) (K := K) (L := L) (E := E)
      (M := M) (B₁ := B₁) ρM eB g x) : integralClosure B M) : M) =
      ρM g ((eB x : integralClosure B M) : M) := by
  simp [actionOnIntegralClosureB, conjugateAlgEquivHom,
    integralClosureAutHom, restrictAutHom]

end IntegralActions

private theorem fixed_power_mem_range_of_normal
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [Module.Finite K E] [Normal K E] (x : E)
    (hx : ∀ g : E ≃ₐ[K] E, g x = x) :
    ∃ n : ℕ, x ^ (ringExpChar K) ^ n ∈ (algebraMap K E).range := by
  let F := separableClosure K E
  have : Algebra.IsAlgebraic K E := Normal.toIsAlgebraic
  have : IsPurelyInseparable F E := separableClosure.isPurelyInseparable K E
  have : IsGalois K F := separableClosure.isGalois K E
  have : ExpChar F (ringExpChar K) :=
    expChar_of_injective_ringHom (algebraMap K F).injective (ringExpChar K)
  obtain ⟨m, ⟨y, hy⟩⟩ := IsPurelyInseparable.pow_mem F (ringExpChar K) x
  have hfixed : ∀ σ : F ≃ₐ[K] F, σ y = y := by
    intro σ
    obtain ⟨g, hg⟩ :=
      AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := F) (E := E) σ
    apply (algebraMap F E).injective
    change ((σ y : F) : E) = (y : E)
    calc
      ((σ y : F) : E) =
          (((AlgEquiv.restrictNormalHom F g) y : F) : E) := by rw [hg]
      _ = g (y : E) := AlgEquiv.restrictNormalHom_apply F g y
      _ = (y : E) := by
        change g (algebraMap F E y) = algebraMap F E y
        rw [hy, map_pow, hx g]
  obtain ⟨z, hz⟩ := (IsGalois.mem_range_algebraMap_iff_fixed y).mpr hfixed
  refine ⟨m, ⟨z, ?_⟩⟩
  rw [← hy, ← hz]
  exact (IsScalarTower.algebraMap_apply K F E z).symm

private theorem tmul_mem_perfectClosure_of_pow_mem
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] (q : ℕ)
    [ExpChar (L ⊗[K] E) q] (l : L) (e : E)
    (he : ∃ n, e ^ q ^ n ∈ (algebraMap K E).range) :
    l ⊗ₜ[K] e ∈ Subalgebra.perfectClosure L (L ⊗[K] E) q := by
  rw [Subalgebra.mem_perfectClosure_iff]
  obtain ⟨n, a, ha⟩ := he
  refine ⟨n, ⟨l ^ q ^ n * algebraMap K L a, ?_⟩⟩
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_pow, ← ha]
  change (l ^ q ^ n * algebraMap K L a) ⊗ₜ[K] (1 : E) =
    (l ^ q ^ n) ⊗ₜ[K] (algebraMap K E a)
  simpa only [Algebra.smul_def, mul_one, one_mul, mul_comm] using
    (TensorProduct.smul_tmul (R := K) a (l ^ q ^ n) (1 : E))

private theorem fixed_tensor_mem_perfectClosure
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Module.Finite K E] [Normal K E]
    [ExpChar (L ⊗[K] E) (ringExpChar K)]
    (x : L ⊗[K] E)
    (hx : ∀ g : E ≃ₐ[K] E, tensorAut (L := L) g x = x) :
    x ∈ Subalgebra.perfectClosure L (L ⊗[K] E) (ringExpChar K) := by
  classical
  let q := ringExpChar K
  let b := Module.Basis.ofVectorSpace K L
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := E) b
  have hcoord (g : E ≃ₐ[K] E) (t : L ⊗[K] E) (i : Module.Basis.ofVectorSpaceIndex K L) :
      e (tensorAut (L := L) g t) i = g (e t i) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul l z =>
        simp only [tensorAut_tmul, e,
          TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
        simp
    | add x y hx hy => simp [map_add, hx, hy]
  have hfixed (i : Module.Basis.ofVectorSpaceIndex K L)
      (g : E ≃ₐ[K] E) : g (e x i) = e x i := by
    rw [← hcoord g x i, hx g]
  have hreconstruct : x = (e x).sum (fun i z => b i ⊗ₜ[K] z) :=
    (e.symm_apply_apply x).symm.trans (TensorProduct.equivFinsuppOfBasisLeft_symm_apply b (e x))
  rw [hreconstruct]
  change (∑ i ∈ (e x).support, b i ⊗ₜ[K] (e x i)) ∈
    Subalgebra.perfectClosure L (L ⊗[K] E) q
  exact Subalgebra.sum_mem _ fun i _ ↦ tmul_mem_perfectClosure_of_pow_mem q (b i) (e x i)
    (fixed_power_mem_range_of_normal (e x i) (hfixed i))

private theorem fixed_reduction_power_mem_range
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Module.Finite K E] [Normal K E]
    [ExpChar (L ⊗[K] E) (ringExpChar K)]
    (x : (L ⊗[K] E) ⧸ nilradical (L ⊗[K] E))
    (hx : ∀ g : E ≃ₐ[K] E,
      quotientNilradicalAut (tensorAut (L := L) g) x = x) :
    ∃ (a : L) (n : ℕ), 0 < n ∧
      algebraMap L ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E)) a = x ^ n := by
  classical
  let T := L ⊗[K] E
  let G := E ≃ₐ[K] E
  let : Fintype G := AlgEquiv.fintype K E
  let : MulSemiringAction G T :=
    MulSemiringAction.compHom T (tensorAutHom (K := K) (L := L) (E := E))
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  let z : T := ∏ g : G, g • y
  have hzfixed (g : G) : tensorAut (L := L) g z = z := by
    change g • z = z
    exact Finset.smul_prod_perm y g
  have hzimage :
      Ideal.Quotient.mk (nilradical T) z =
        (Ideal.Quotient.mk (nilradical T) y) ^ Fintype.card G := by
    change Ideal.Quotient.mk (nilradical T) (∏ g : G, g • y) = _
    rw [map_prod]
    simp only [show ∀ g : G,
      Ideal.Quotient.mk (nilradical T) (g • y) =
        Ideal.Quotient.mk (nilradical T) y from fun g => by
          rw [show g • y = tensorAut (L := L) g y from rfl,
            ← quotientNilradicalAut_mk]
          exact hx g]
    simp
  obtain ⟨m, ⟨a, ha⟩⟩ :=
    (Subalgebra.mem_perfectClosure_iff).mp
      (fixed_tensor_mem_perfectClosure z hzfixed)
  have hcard : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨1⟩
  refine ⟨a, Fintype.card G * (ringExpChar K) ^ m,
    Nat.mul_pos hcard (expChar_pow_pos K (ringExpChar K) m), ?_⟩
  calc
    algebraMap L ((L ⊗[K] E) ⧸ nilradical T) a =
        Ideal.Quotient.mk (nilradical T) (algebraMap L T a) := rfl
    _ = Ideal.Quotient.mk (nilradical T) (z ^ (ringExpChar K) ^ m) := by rw [ha]
    _ = (Ideal.Quotient.mk (nilradical T) y) ^
        (Fintype.card G * (ringExpChar K) ^ m) := by
      rw [map_pow, hzimage, pow_mul]

private theorem exists_smul_of_under_eq_of_fixed_pow
    (R S G : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    (hfixed : ∀ b : S, (∀ g : G, g • b = b) →
      ∃ (a : R) (n : ℕ), 0 < n ∧ algebraMap R S a = b ^ n)
    (P Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (hPQ : P.under R = Q.under R) : ∃ g : G, Q = g • P := by
  cases nonempty_fintype G
  have hstep : ∀ (P Q : Ideal S) [P.IsPrime] [Q.IsPrime], P.under R = Q.under R →
      ∃ g ∈ (⊤ : Finset G), Q ≤ g • P := by
    intro P Q hP hQ hPQ
    rw [← Ideal.subset_union_prime 1 1 (fun _ _ _ _ ↦ hP.smul _)]
    intro b hb
    suffices h : ∃ g ∈ Finset.univ, g • b ∈ P by
      obtain ⟨g, -, hg⟩ := h
      apply Set.mem_biUnion (Finset.mem_univ g⁻¹) (Ideal.mem_inv_pointwise_smul_iff.mpr hg)
    obtain ⟨a, n, hn, ha⟩ := hfixed (∏ g : G, g • b) (Finset.smul_prod_perm b)
    have hnormQ : (∏ g : G, g • b) ∈ Q :=
      (hQ.prod_mem_iff).2 ⟨1, Finset.mem_univ 1, by simpa using hb⟩
    have hpowQ : (∏ g : G, g • b) ^ n ∈ Q := Q.pow_mem_of_mem hnormQ n hn
    have haQ : a ∈ Q.under R := by
      simpa only [Ideal.under_def, Ideal.mem_comap, ha] using hpowQ
    have haP : a ∈ P.under R := hPQ.symm ▸ haQ
    have hprodP : (∏ g : G, g • b) ∈ P :=
      (show P.IsPrime from inferInstance).mem_of_pow_mem n (by
        rw [← ha]
        simpa only [Ideal.under_def, Ideal.mem_comap] using haP)
    exact hP.prod_mem_iff.mp hprodP
  obtain ⟨g, -, hg⟩ := hstep P Q hPQ
  obtain ⟨g', -, hg'⟩ := hstep Q (g • P) ((P.under_smul R g).trans hPQ).symm
  exact ⟨g, le_antisymm hg (smul_eq_of_le_smul (hg.trans hg') ▸ hg')⟩

/-- After a finite normal extension `K₁/K`, the automorphisms of `K₁` over `K` act
compatibly on the reduced base change `L₁`, on the integral closure `A₁` of `A` in `K₁`,
and on the integral closure `B₁` of `B` in `L₁`.  The resulting action on the maximal
ideals of `B₁` is transitive. -/
@[stacks 09EU]
theorem normal_extension_acts_transitively_on_maximalSpectrum_integralClosure
    (A B K L K₁ L₁ A₁ B₁ : Type u)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [CommRing L₁] [CommRing A₁] [CommRing B₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L] [Algebra K K₁]
    [Algebra A K₁] [Algebra K L₁] [Algebra B L₁] [Algebra L L₁] [Algebra K₁ L₁]
    [Algebra A A₁] [Algebra B B₁] [Algebra A B₁] [Algebra A₁ B₁] [Algebra B₁ L₁]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsScalarTower K L L₁] [IsScalarTower K K₁ L₁] [IsScalarTower B L L₁]
    [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁] [IsScalarTower B B₁ L₁]
    [IsFractionRing A K] [IsFractionRing B L] [Module.Finite K K₁] [Normal K K₁]
    (eL₁ : L₁ ≃ₐ[K] ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)))
    (eA₁ : A₁ ≃ₐ[A] integralClosure A K₁)
    (eB₁ : B₁ ≃ₐ[B] integralClosure B L₁)
    (eL₁_left : ∀ x : L,
      eL₁ (algebraMap L L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) x))
    (eL₁_right : ∀ x : K₁,
      eL₁ (algebraMap K₁ L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x))
    (eB₁_coe : ∀ x : B₁, ((eB₁ x : integralClosure B L₁) : L₁) = algebraMap B₁ L₁ x)
    (_hfieldSquare : ∀ x : K, algebraMap L L₁ (algebraMap K L x) =
      algebraMap K₁ L₁ (algebraMap K K₁ x))
    (hringSquare : ∀ x : A₁, algebraMap B₁ L₁ (algebraMap A₁ B₁ x) =
      algebraMap K₁ L₁ ((eA₁ x : integralClosure A K₁) : K₁)) :
    ∃ (ρL₁ : (K₁ ≃ₐ[K] K₁) →* (L₁ ≃ₐ[L] L₁))
        (ρA₁ : (K₁ ≃ₐ[K] K₁) →* (A₁ ≃ₐ[A] A₁))
        (ρB₁ : (K₁ ≃ₐ[K] K₁) →* (B₁ ≃ₐ[B] B₁)),
      (∀ (g : K₁ ≃ₐ[K] K₁) (x : K₁),
        ρL₁ g (algebraMap K₁ L₁ x) = algebraMap K₁ L₁ (g x)) ∧
      (∀ (g : K₁ ≃ₐ[K] K₁) (x : A₁),
        (((eA₁ (ρA₁ g x) : integralClosure A K₁) : K₁)) =
          g ((eA₁ x : integralClosure A K₁) : K₁)) ∧
      (∀ (g : K₁ ≃ₐ[K] K₁) (x : B₁),
        algebraMap B₁ L₁ (ρB₁ g x) = ρL₁ g (algebraMap B₁ L₁ x)) ∧
      (∀ (g : K₁ ≃ₐ[K] K₁) (x : A₁),
        ρB₁ g (algebraMap A₁ B₁ x) = algebraMap A₁ B₁ (ρA₁ g x)) ∧
      ∀ q q' : MaximalSpectrum B₁, ∃ g : K₁ ≃ₐ[K] K₁,
        q'.asIdeal = q.asIdeal.comap (ρB₁ g).symm.toRingHom := by
  let ρL₁ := reductionAutHom K L K₁ L₁ eL₁ eL₁_left
  let ρA₁ := actionOnIntegralClosureA A K K₁ A₁ eA₁
  let ρB₁ := actionOnIntegralClosureB (B := B) (K := K) (L := L)
    (E := K₁) (M := L₁) (B₁ := B₁) ρL₁ eB₁
  have hB_injective : Function.Injective (algebraMap B₁ L₁) := by
    intro x y h
    apply eB₁.injective
    apply Subtype.ext
    simpa only [eB₁_coe] using h
  have hρB (g : K₁ ≃ₐ[K] K₁) (x : B₁) :
      algebraMap B₁ L₁ (ρB₁ g x) = ρL₁ g (algebraMap B₁ L₁ x) := by
    rw [← eB₁_coe (ρB₁ g x),
      actionOnIntegralClosureB_coe (B := B) (K := K) (L := L)
        (E := K₁) (M := L₁) (B₁ := B₁) ρL₁ eB₁ g x,
      eB₁_coe]
  refine ⟨ρL₁, ρA₁, ρB₁, ?_, ?_, hρB, ?_, ?_⟩
  · exact reductionAutHom_right K L K₁ L₁ eL₁ eL₁_left eL₁_right
  · exact actionOnIntegralClosureA_coe A K K₁ A₁ eA₁
  · intro g x
    apply hB_injective
    rw [hρB, hringSquare, hringSquare,
      reductionAutHom_right K L K₁ L₁ eL₁ eL₁_left eL₁_right,
      actionOnIntegralClosureA_coe A K K₁ A₁ eA₁]
  · let T := L ⊗[K] K₁
    have hleft : Function.Injective
        (Algebra.TensorProduct.includeLeft : L →ₐ[K] T) :=
      Algebra.TensorProduct.includeLeft_injective (algebraMap K K₁).injective
    have : Nontrivial T := hleft.nontrivial
    obtain ⟨P, hP⟩ := Ideal.exists_maximal T
    have hnil : nilradical T ≠ ⊤ :=
      ne_top_of_le_ne_top hP.ne_top (nilradical_le_prime P)
    have : Nontrivial (T ⧸ nilradical T) := Ideal.Quotient.nontrivial_iff.mpr hnil
    have : Nontrivial L₁ := eL₁.symm.injective.nontrivial
    have hK : Function.Injective (algebraMap K T) := by
      change Function.Injective
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] T) ∘ algebraMap K L)
      exact hleft.comp (algebraMap K L).injective
    have hchar : ExpChar T (ringExpChar K) := expChar_of_injective_ringHom hK (ringExpChar K)
    have hfixed (b : B₁) (hb : ∀ g : K₁ ≃ₐ[K] K₁, ρB₁ g b = b) :
        ∃ (a : B) (n : ℕ), 0 < n ∧ algebraMap B B₁ a = b ^ n := by
      have hq (g : K₁ ≃ₐ[K] K₁) :
          quotientNilradicalAut (tensorAut (L := L) g)
            (eL₁ (algebraMap B₁ L₁ b)) = eL₁ (algebraMap B₁ L₁ b) := by
        have hL : ρL₁ g (algebraMap B₁ L₁ b) = algebraMap B₁ L₁ b := by
          rw [← hρB, hb]
        have h' := congrArg (reductionEquivOverL K L K₁ L₁ eL₁ eL₁_left) hL
        simp only [ρL₁, reductionAutHom, conjugateAlgEquivHom,
          MonoidHom.coe_mk, OneHom.coe_mk, AlgEquiv.trans_apply,
          AlgEquiv.apply_symm_apply, quotientNilradicalAutHom] at h'
        exact h'
      obtain ⟨a, n, hn, ha⟩ := fixed_reduction_power_mem_range
        (K := K) (L := L) (E := K₁) (eL₁ (algebraMap B₁ L₁ b)) hq
      have hm : algebraMap L L₁ a = algebraMap B₁ L₁ (b ^ n) := by
        apply eL₁.injective
        calc
          eL₁ (algebraMap L L₁ a) = algebraMap L (T ⧸ nilradical T) a := by
            rw [eL₁_left]
            rfl
          _ = eL₁ (algebraMap B₁ L₁ b) ^ n := ha
          _ = eL₁ (algebraMap B₁ L₁ (b ^ n)) := by simp
      have hint : IsIntegral B a := by
        apply (isIntegral_algHom_iff
          (IsScalarTower.toAlgHom B L L₁) (algebraMap L L₁).injective).mp
        change IsIntegral B (algebraMap L L₁ a)
        rw [hm, map_pow]
        have hbint : IsIntegral B (algebraMap B₁ L₁ b) := by
          rw [← eB₁_coe]
          exact (eB₁ b).property
        exact hbint.pow n
      obtain ⟨aB, haB⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
      refine ⟨aB, n, hn, hB_injective ?_⟩
      calc
        algebraMap B₁ L₁ (algebraMap B B₁ aB) = algebraMap B L₁ aB :=
          (IsScalarTower.algebraMap_apply B B₁ L₁ aB).symm
        _ = algebraMap L L₁ (algebraMap B L aB) :=
          IsScalarTower.algebraMap_apply B L L₁ aB
        _ = algebraMap B₁ L₁ (b ^ n) := by rw [haB, hm]
    let : MulSemiringAction (K₁ ≃ₐ[K] K₁) B₁ :=
      MulSemiringAction.compHom B₁ ρB₁
    have : SMulCommClass (K₁ ≃ₐ[K] K₁) B B₁ := ⟨fun g a b ↦ by
      change ρB₁ g (a • b) = a • ρB₁ g b
      simp only [Algebra.smul_def, map_mul, (ρB₁ g).commutes]⟩
    have : Algebra.IsIntegral B B₁ := (eB₁.isIntegral_iff).mpr inferInstance
    intro q q'
    have hunder : q.asIdeal.under B = q'.asIdeal.under B := by
      change q.asIdeal.comap (algebraMap B B₁) =
        q'.asIdeal.comap (algebraMap B B₁)
      exact (IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q.asIdeal)).trans
        (IsLocalRing.eq_maximalIdeal
          (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q'.asIdeal)).symm
    obtain ⟨g, hg⟩ := exists_smul_of_under_eq_of_fixed_pow B B₁
      (K₁ ≃ₐ[K] K₁) (fun b hb => hfixed b hb) q.asIdeal q'.asIdeal hunder
    refine ⟨g, ?_⟩
    rw [Ideal.pointwise_smul_eq_comap] at hg
    convert hg using 1
    ext x
    rfl

end IsDiscreteValuationRing
