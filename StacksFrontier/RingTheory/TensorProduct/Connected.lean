module

import StacksCore.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.RingTheory.GeometricallyConnected.Defs
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v w

/-!
# Connectedness of the spectrum of a tensor product over a separably closed field

Let `k` be a separably algebraically closed field and let `R` and `S` be `k`-algebras whose
spectra are connected. Then `Spec (R ⊗[k] S)` is connected as well. Some hypothesis on `k` is
needed: `Spec ℂ` is a point, yet `ℂ ⊗[ℝ] ℂ ≅ ℂ × ℂ` has a two-point spectrum.

Let `k` be a field, let `S` be a geometrically connected `k`-algebra and let `R` be an arbitrary
`k`-algebra. Then the structure map `R → R ⊗[k] S`, `r ↦ r ⊗ 1`, carries the idempotents of `R`
bijectively onto the idempotents of `R ⊗[k] S`, and the induced map of spectra
`Spec (R ⊗[k] S) → Spec R` is a bijection on connected components.

## Main results

* `Stacks.TensorProduct.ConnectedSpectrum.solution`: for `k` a separably closed field and `R`,
  `S` two `k`-algebras with `Spec R` and `Spec S` connected, `Spec (R ⊗[k] S)` is connected.
* `Algebra.TensorProduct.connectedSpace_primeSpectrum`: the same statement, as an instance.
* `Stacks.TensorProduct.IdempotentBijection.tensorProduct_map_injective`: over a field, the tensor
  product of two injective algebra maps is injective.
* `Stacks.TensorProduct.IdempotentBijection.solution`: for `S` geometrically connected over `k`,
  `R → R ⊗[k] S` is a bijection on idempotents and `Spec (R ⊗[k] S) → Spec R` is a bijection on
  connected components.
* `Algebra.TensorProduct.bijOn_isIdempotentElem_and_bijective_connectedComponentsMap`: the same
  statement, in the namespace `Algebra.TensorProduct`.

## References

* [Stacks 037R](https://stacks.math.columbia.edu/tag/037R)
* [Stacks 037W](https://stacks.math.columbia.edu/tag/037W)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.TensorProduct.ConnectedSpectrum

/-! ### Idempotents along an injective ring map -/

section Injective

variable {A B F : Type*} [CommRing A] [CommRing B] [FunLike F A B] [RingHomClass F A B] {f : F}

/-- An injective ring map reflects idempotency. -/
private theorem isIdempotentElem_map_iff (hf : Function.Injective f) {a : A} :
    IsIdempotentElem (f a) ↔ IsIdempotentElem a :=
  ⟨fun h ↦ hf (by rw [map_mul]; exact h), fun h ↦ h.map f⟩

/-- Having no idempotents besides `0` and `1` passes along an injective ring map from the target to
the source; in particular it passes to a subring. -/
theorem eq_zero_or_one_of_injective (hf : Function.Injective f)
    (h : ∀ z : B, IsIdempotentElem z → z = 0 ∨ z = 1) {a : A} (ha : IsIdempotentElem a) :
    a = 0 ∨ a = 1 :=
  (h (f a) (ha.map f)).imp (fun h₀ ↦ hf (by rw [h₀, map_zero]))
    fun h₁ ↦ hf (by rw [h₁, map_one])

/-- If `b = f a` is idempotent for an injective ring map `f` and `A` has no idempotents besides
`0` and `1`, then `b` is `0` or `1`. -/
private theorem eq_zero_or_one_of_map_eq (hf : Function.Injective f)
    (h : ∀ y : A, IsIdempotentElem y → y = 0 ∨ y = 1) {a : A} {b : B} (hab : f a = b)
    (hb : IsIdempotentElem b) : b = 0 ∨ b = 1 := by
  subst hab
  exact (h a ((isIdempotentElem_map_iff hf).mp hb)).imp (fun h ↦ by rw [h, map_zero])
    fun h ↦ by rw [h, map_one]

end Injective

/-! ### Connectedness of a spectrum and idempotents -/

section Idempotents

variable {T : Type*} [CommRing T]

/-- An idempotent of a commutative ring is determined by the basic open set it cuts out in the
spectrum: idempotents and clopen subsets correspond. -/
private theorem eq_of_basicOpen_eq {e f : T} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum T)) = PrimeSpectrum.basicOpen f) :
    e = f :=
  congrArg Subtype.val (PrimeSpectrum.isIdempotentElemEquivClopens.injective
    (a₁ := ⟨e, he⟩) (a₂ := ⟨f, hf⟩) (SetLike.coe_injective h))

/-- The spectrum of a nontrivial commutative ring is connected exactly when the
ring has no idempotents besides `0` and `1`. -/
private theorem connectedSpace_primeSpectrum_iff (T : Type*) [CommRing T] [Nontrivial T] :
    ConnectedSpace (PrimeSpectrum T) ↔ ∀ e : T, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  rw [connectedSpace_iff_clopen, and_iff_right (inferInstance : Nonempty (PrimeSpectrum T))]
  refine ⟨fun H e he ↦ (H _ (PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩)).imp
    (fun h ↦ eq_of_basicOpen_eq he .zero (by simp [h]))
    (fun h ↦ eq_of_basicOpen_eq he .one (by simp [h])), fun H s hs ↦ ?_⟩
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
  exact (H e he).imp (fun h ↦ by simp [h]) fun h ↦ by simp [h]

end Idempotents

/-! ### A partition of the spectrum of a Jacobson ring -/

/-- Let `S` be a Jacobson ring whose spectrum is connected and let `I`, `J` be ideals generating
the unit ideal such that every maximal ideal contains `I` or `J`. Then `I` or `J` consists of
nilpotents. -/
private theorem le_nilradical_or_le_nilradical {S : Type*} [CommRing S] [IsJacobsonRing S]
    [ConnectedSpace (PrimeSpectrum S)] {I J : Ideal S} (hsup : I ⊔ J = ⊤)
    (hmax : ∀ m : Ideal S, m.IsMaximal → I ≤ m ∨ J ≤ m) :
    I ≤ nilradical S ∨ J ≤ nilradical S := by
  have key : ∀ K : Ideal S, (∀ p : PrimeSpectrum S, K ≤ p.asIdeal) → K ≤ nilradical S :=
    fun K h _ ha ↦ nilpotent_iff_mem_prime.mpr fun p hp ↦ h ⟨p, hp⟩ ha
  have hIJ : I * J ≤ nilradical S := by
    refine le_trans ?_ (Ideal.radical_eq_jacobson (⊥ : Ideal S)).ge
    rw [Ideal.jacobson]
    exact le_sInf fun m hm ↦ (hmax m hm.2).elim (fun h ↦ Ideal.mul_le_left.trans h)
      fun h ↦ Ideal.mul_le_right.trans h
  have hcov : PrimeSpectrum.zeroLocus (J : Set S) = (PrimeSpectrum.zeroLocus (I : Set S))ᶜ := by
    ext p
    simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    refine ⟨fun h₂ h₁ ↦ p.isPrime.ne_top (top_le_iff.mp (hsup ▸ sup_le h₁ h₂)), fun h₁ ↦ ?_⟩
    exact (p.isPrime.mul_le.mp (hIJ.trans (nilradical_le_prime p.asIdeal))).resolve_left h₁
  have hclopen : IsClopen (PrimeSpectrum.zeroLocus (I : Set S)) :=
    ⟨PrimeSpectrum.isClosed_zeroLocus _, by
      rw [← compl_compl (PrimeSpectrum.zeroLocus (I : Set S)), ← hcov, isOpen_compl_iff]
      exact PrimeSpectrum.isClosed_zeroLocus _⟩
  rcases isClopen_iff.mp hclopen with h | h
  · refine Or.inr (key J fun p ↦ ?_)
    have hp : p ∈ PrimeSpectrum.zeroLocus (J : Set S) := by rw [hcov, h]; simp
    simpa only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] using hp
  · refine Or.inl (key I fun p ↦ ?_)
    have hp : p ∈ PrimeSpectrum.zeroLocus (I : Set S) := by rw [h]; trivial
    simpa only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] using hp

/-! ### A purely inseparable base change creates no idempotents -/

/-- Let `K / k` be a purely inseparable extension of fields and let `R` be a `k`-algebra with no
idempotents besides `0` and `1`. Then `K ⊗[k] R` has none either. -/
private theorem eq_zero_or_one_of_isPurelyInseparable {k K R : Type*} [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] [CommRing R] [Algebra k R]
    (hR : ∀ y : R, IsIdempotentElem y → y = 0 ∨ y = 1) {z : K ⊗[k] R}
    (hz : IsIdempotentElem z) : z = 0 ∨ z = 1 := by
  refine eq_zero_or_one_of_injective (Algebra.TensorProduct.comm k K R).injective
    (fun w hw ↦ ?_) hz
  have hinj : Function.Injective (algebraMap R (R ⊗[k] K)) :=
    Algebra.TensorProduct.includeLeft_injective (S := k) (algebraMap k K).injective
  obtain ⟨n, hn, r, hr⟩ := IsPurelyInseparable.exists_pow_mem_range_tensorProduct w
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [hw.pow_succ_eq m] at hr
  exact eq_zero_or_one_of_map_eq hinj hR hr hw

/-! ### The ideal generated by the coordinates in a basis of the right hand factor -/

section Coordinates

variable {k : Type u} {R : Type v} {ι : Type*} [Field k] [CommRing R] [Algebra k R]
  {S T : Type*} [CommRing S] [Algebra k S] [CommRing T] [Algebra k T]

/-- The ideal of `S` generated by the coordinates of `y : S ⊗[k] R` with respect to a `k`-basis `b`
of `R`, which is also an `S`-basis of `S ⊗[k] R`. -/
private noncomputable def coordIdeal (b : Module.Basis ι k R) (y : S ⊗[k] R) : Ideal S :=
  Ideal.span (Set.range ((b.baseChange S).repr y))

/-- Each coordinate of `y` lies in `coordIdeal b y`. -/
private theorem repr_mem_coordIdeal (b : Module.Basis ι k R) (y : S ⊗[k] R) (i : ι) :
    (b.baseChange S).repr y i ∈ coordIdeal b y :=
  Ideal.subset_span ⟨i, rfl⟩

/-- `coordIdeal b y` lies in an ideal `p` exactly when every coordinate of `y` does. -/
private theorem coordIdeal_le_iff (b : Module.Basis ι k R) (y : S ⊗[k] R) (p : Ideal S) :
    coordIdeal b y ≤ p ↔ ∀ i, (b.baseChange S).repr y i ∈ p := by
  rw [coordIdeal, Ideal.span_le, Set.range_subset_iff]; rfl

/-- The coordinates of `1 : S ⊗[k] R` are the images of the coordinates of `1 : R`. -/
private theorem repr_baseChange_one (b : Module.Basis ι k R) (i : ι) :
    (b.baseChange S).repr 1 i = algebraMap k S (b.repr (1 : R) i) := by
  rw [Algebra.TensorProduct.one_def, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]

/-- Base change of a `k`-algebra map `π : S →ₐ[k] T` acts on the coordinates of `S ⊗[k] R` by
applying `π` to each coordinate. -/
private theorem repr_rTensor (b : Module.Basis ι k R) (π : S →ₐ[k] T) (y : S ⊗[k] R) (i : ι) :
    (b.baseChange T).repr (Algebra.TensorProduct.rTensor R π y) i
      = π ((b.baseChange S).repr y i) := by
  induction y with
  | zero => simp
  | tmul s r => simp [Algebra.TensorProduct.map_tmul, map_smul]
  | add y z hy hz => simp [hy, hz]

/-- An element of `S ⊗[k] R` dies in `T ⊗[k] R` exactly when `π` kills all of its coordinates. -/
private theorem rTensor_eq_zero_iff (b : Module.Basis ι k R) (π : S →ₐ[k] T) (y : S ⊗[k] R) :
    Algebra.TensorProduct.rTensor R π y = 0 ↔ ∀ i, π ((b.baseChange S).repr y i) = 0 := by
  refine ⟨fun h i ↦ by rw [← repr_rTensor b π y i, h]; simp, fun h ↦ ?_⟩
  refine (b.baseChange T).repr.map_eq_zero_iff.mp (Finsupp.ext fun i ↦ ?_)
  simp [repr_rTensor b π y i, h i]

/-- An element of `S ⊗[k] R` all of whose coordinates are nilpotent is nilpotent. -/
private theorem isNilpotent_of_coordIdeal_le_nilradical (b : Module.Basis ι k R) {y : S ⊗[k] R}
    (h : coordIdeal b y ≤ nilradical S) : IsNilpotent y := by
  classical
  rw [← (b.baseChange S).linearCombination_repr y, Finsupp.linearCombination_apply, Finsupp.sum]
  refine isNilpotent_sum fun i _ ↦ ?_
  rw [Algebra.smul_def]
  exact (Commute.all _ _).isNilpotent_mul_right
    ((mem_nilradical.mp (h (repr_mem_coordIdeal b y i))).map (algebraMap S (S ⊗[k] R)))

end Coordinates

/-! ### The case of an algebra of finite type -/

section FiniteType

variable {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R]

/-- For `k` separably closed, `R` a `k`-algebra with no nontrivial idempotents and `S` of finite
type over `k` with connected spectrum, `S ⊗[k] R` has no nontrivial idempotents. -/
private theorem eq_zero_or_one_of_finiteType (S : Type w) [CommRing S] [Algebra k S]
    [IsSepClosed k] [Algebra.FiniteType k S] [ConnectedSpace (PrimeSpectrum S)] [Nontrivial R]
    (hR : ∀ y : R, IsIdempotentElem y → y = 0 ∨ y = 1) {x : S ⊗[k] R}
    (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
  classical
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := k)
  set b := Module.Basis.ofVectorSpace k R with hb
  have hsup : coordIdeal b x ⊔ coordIdeal b (x - 1) = ⊤ := by
    obtain ⟨i, hi⟩ : ∃ i, b.repr (1 : R) i ≠ 0 := by
      have h1 : b.repr (1 : R) ≠ 0 := by simp
      simpa using Finsupp.ne_iff.mp h1
    refine Ideal.eq_top_of_isUnit_mem _ ?_ ((Ne.isUnit hi).map (algebraMap k S))
    have hdiff : (b.baseChange S).repr x i - (b.baseChange S).repr (x - 1) i
        = algebraMap k S (b.repr (1 : R) i) := by
      simp [map_sub, repr_baseChange_one]
    rw [← hdiff]
    exact sub_mem (Ideal.mem_sup_left (repr_mem_coordIdeal b x i))
      (Ideal.mem_sup_right (repr_mem_coordIdeal b (x - 1) i))
  have hmax : ∀ m : Ideal S, m.IsMaximal →
      coordIdeal b x ≤ m ∨ coordIdeal b (x - 1) ≤ m := by
    intro m hm
    let _ : Field (S ⧸ m) := Ideal.Quotient.field m
    have : Algebra.FiniteType k (S ⧸ m) := Algebra.FiniteType.quotient k m
    have : Module.Finite k (S ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (S ⧸ m)
    have : Algebra.IsAlgebraic k (S ⧸ m) := Algebra.IsAlgebraic.of_finite k (S ⧸ m)
    have hmem : ∀ y : S ⊗[k] R,
        Algebra.TensorProduct.rTensor R (Ideal.Quotient.mkₐ k m) y = 0 → coordIdeal b y ≤ m :=
      fun y hy ↦ (coordIdeal_le_iff b y m).mpr fun i ↦
        (Submodule.Quotient.mk_eq_zero m).mp ((rTensor_eq_zero_iff b _ y).mp hy i)
    have hxm : IsIdempotentElem (Algebra.TensorProduct.rTensor R (Ideal.Quotient.mkₐ k m) x) :=
      hx.map _
    rcases eq_zero_or_one_of_isPurelyInseparable hR hxm with h | h
    · exact Or.inl (hmem x h)
    · exact Or.inr (hmem (x - 1) (by rw [map_sub, h, map_one, sub_self]))
  rcases le_nilradical_or_le_nilradical hsup hmax with h | h
  · exact Or.inl (hx.eq_zero_of_isNilpotent (isNilpotent_of_coordIdeal_le_nilradical b h))
  · refine Or.inr (sub_eq_zero.mp (hx.one_sub.eq_zero_of_isNilpotent ?_)).symm
    simpa using (isNilpotent_of_coordIdeal_le_nilradical b h).neg

end FiniteType

/-! ### Descent to a finitely generated subalgebra -/

/-- Base change along the inclusion of a subalgebra `S' ⊆ S` of `k`-algebras is injective. -/
private theorem baseChange_val_injective {k : Type u} (R : Type v) {S : Type w} [Field k]
    [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (S' : Subalgebra k S) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id R R) S'.val) := by
  have h : ∀ z : R ⊗[k] S', Algebra.TensorProduct.map (AlgHom.id R R) S'.val z
      = TensorProduct.map LinearMap.id S'.val.toLinearMap z := by
    intro z
    induction z with
    | zero => simp
    | tmul a s => simp
    | add z w hz hw => simp [hz, hw]
  intro z w hzw
  refine TensorProduct.map_injective_of_flat_flat (LinearMap.id (R := k) (M := R))
    S'.val.toLinearMap Function.injective_id Subtype.val_injective ?_
  rwa [← h, ← h]

/-! ### The theorem -/

/-- Let `k` be a separably algebraically closed field and let `R` and `S` be `k`-algebras. If
`Spec R` and `Spec S` are connected, then so is `Spec (R ⊗[k] S)`. -/
public theorem solution (k : Type u) (R : Type v) (S : Type w) [Field k]
    [IsSepClosed k] [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
    [ConnectedSpace (PrimeSpectrum R)] [ConnectedSpace (PrimeSpectrum S)] :
    ConnectedSpace (PrimeSpectrum (R ⊗[k] S)) := by
  have hRn : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  have hSn : Nontrivial S := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  have hRi := (connectedSpace_primeSpectrum_iff R).mp inferInstance
  have hSi := (connectedSpace_primeSpectrum_iff S).mp inferInstance
  have : Nontrivial (R ⊗[k] S) :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right k R).mpr hSn
  rw [connectedSpace_primeSpectrum_iff]
  intro e he
  obtain ⟨S', hfg, y, hy⟩ : ∃ (S' : Subalgebra k S) (_ : S'.FG) (y : R ⊗[k] S'),
      Algebra.TensorProduct.map (AlgHom.id R R) S'.val y = e := by
    obtain ⟨S', hfg, y, hy⟩ := exists_fg_and_mem_baseChange e
    exact ⟨S', hfg, y, hy⟩
  have : Algebra.FiniteType k S' := (Subalgebra.fg_iff_finiteType S').mp hfg
  have : ConnectedSpace (PrimeSpectrum S') := (connectedSpace_primeSpectrum_iff S').mpr
    fun _ hz ↦ eq_zero_or_one_of_injective (f := S'.val) Subtype.val_injective hSi hz
  exact eq_zero_or_one_of_map_eq (baseChange_val_injective R S')
    (fun _ hz ↦ eq_zero_or_one_of_injective (Algebra.TensorProduct.comm k R S').injective
      (fun _ hz ↦ eq_zero_or_one_of_finiteType (R := R) S' hRi hz) hz) hy he

end Stacks.TensorProduct.ConnectedSpectrum

@[expose] public section

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- **Connectedness of the spectrum of a tensor product over a separably closed field.** Let `k`
be a separably algebraically closed field and let `R` and `S` be `k`-algebras. If `Spec R` and
`Spec S` are connected, then so is `Spec (R ⊗[k] S)`. -/
@[stacks 037R "Connectedness of the spectra of two `k`-algebras over a separably closed field `k`
  is inherited by the spectrum of their tensor product over `k`. Stated as an instance, with
  `Spec` read as `PrimeSpectrum` and `connected` as `ConnectedSpace`, which includes
  nonemptiness as the source's notion of a connected space does.",
  sga "3 X 9.7.2" "affine case",
  sga "3 X 9.7.1" "affine case, i = 1"]
public instance connectedSpace_primeSpectrum (k : Type u) (R : Type v) (S : Type w) [Field k]
    [IsSepClosed k] [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
    [ConnectedSpace (PrimeSpectrum R)] [ConnectedSpace (PrimeSpectrum S)] :
    ConnectedSpace (PrimeSpectrum (R ⊗[k] S)) :=
  Stacks.TensorProduct.ConnectedSpectrum.solution k R S

end Algebra.TensorProduct

@[expose] public section

open scoped TensorProduct

namespace Stacks.TensorProduct.IdempotentBijection

/-! ### A quotient map with connected fibres is a bijection on idempotents -/

/-- If `Spec S → Spec R` is a quotient map with connected fibres, then `R → S` restricts to a
bijection from the idempotents of `R` onto the idempotents of `S`. -/
@[ega "IV 4.4.2" "special case"]
private theorem bijOn_isIdempotentElem_of_isQuotientMap {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hq : Topology.IsQuotientMap (PrimeSpectrum.comap f))
    (hfib : ∀ p, IsConnected (PrimeSpectrum.comap f ⁻¹' {p})) :
    Set.BijOn f {e | IsIdempotentElem e} {e | IsIdempotentElem e} := by
  have hbo : ∀ x : A, (PrimeSpectrum.basicOpen (f x) : Set (PrimeSpectrum B))
      = PrimeSpectrum.comap f ⁻¹' (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) :=
    fun x ↦ by rw [← PrimeSpectrum.comap_basicOpen]; rfl
  have hinj : Set.InjOn f {e : A | IsIdempotentElem e} := by
    intro e₁ h₁ e₂ h₂ h
    refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem h₁ h₂ (SetLike.coe_injective ?_)
    exact Set.preimage_injective.mpr hq.surjective (by rw [← hbo, ← hbo, h])
  refine ⟨fun e he ↦ he.map f, hinj, fun e he ↦ ?_⟩
  have hU : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum B)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  set T := PrimeSpectrum.comap f '' (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum B)) with hT
  have hpre : PrimeSpectrum.comap f ⁻¹' T
      = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum B)) := by
    refine subset_antisymm ?_ (Set.subset_preimage_image _ _)
    rintro q ⟨q', hq', hqq'⟩
    exact (hfib (PrimeSpectrum.comap f q)).isPreconnected.subset_isClopen hU ⟨q', hqq', hq'⟩ rfl
  have hTclopen : IsClopen T :=
    ⟨hq.isClosed_preimage.mp (hpre ▸ hU.1), hq.isOpen_preimage.mp (hpre ▸ hU.2)⟩
  obtain ⟨r, hr, hrT⟩ := PrimeSpectrum.isClopen_iff.mp hTclopen
  refine ⟨r, hr, PrimeSpectrum.basicOpen_injOn_isIdempotentElem (hr.map f) he
    (SetLike.coe_injective ?_)⟩
  rw [hbo, ← hrT, hpre]

/-! ### Geometric connectedness for a field extension in an arbitrary universe -/

/-- Over a field, the tensor product of two injective algebra maps is injective. -/
public theorem tensorProduct_map_injective {k A B C D : Type*} [Field k] [CommRing A]
    [CommRing B] [CommRing C] [CommRing D] [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k D]
    (f : A →ₐ[k] B) (g : C →ₐ[k] D) (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (Algebra.TensorProduct.map f g) := by
  have hcoe : (Algebra.TensorProduct.map f g).toLinearMap
      = TensorProduct.map f.toLinearMap g.toLinearMap := by ext a c; simp
  have h := TensorProduct.map_injective_of_flat_flat f.toLinearMap g.toLinearMap hf hg
  rwa [← hcoe] at h

/-- If `S` is geometrically connected over `k`, then `Spec (K ⊗[k] S)` is connected for every field
extension `K/k`, with `K` not required to lie in the universe of `k`. -/
private theorem connectedSpace_primeSpectrum_tensorProduct (k : Type u) (S : Type v) [Field k]
    [CommRing S] [Algebra k S] [Algebra.IsGeometricallyConnected k S] (K : Type w) [Field K]
    [Algebra k K] : ConnectedSpace (PrimeSpectrum (K ⊗[k] S)) := by
  have h0 : ConnectedSpace (PrimeSpectrum (k ⊗[k] S)) :=
    Algebra.IsGeometricallyConnected.connectedSpace_primeSpectrum_tensorProduct k
  have hS : Nontrivial S :=
    have : Nontrivial (k ⊗[k] S) := PrimeSpectrum.nonempty_iff_nontrivial.mp h0.toNonempty
    (Algebra.TensorProduct.lid k S).symm.toRingHom.domain_nontrivial
  have hsep : ConnectedSpace (PrimeSpectrum (SeparableClosure k ⊗[k] S)) :=
    Algebra.IsGeometricallyConnected.connectedSpace_primeSpectrum_tensorProduct (SeparableClosure k)
  set φ : SeparableClosure k →ₐ[k] AlgebraicClosure K := IsAlgClosed.lift
  let _ : Algebra (SeparableClosure k) (AlgebraicClosure K) := φ.toRingHom.toAlgebra
  have : IsScalarTower k (SeparableClosure k) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  set η := Algebra.TensorProduct.cancelBaseChange k (SeparableClosure k) (AlgebraicClosure K)
    (AlgebraicClosure K) S
  have hL : ∀ e : AlgebraicClosure K ⊗[k] S, IsIdempotentElem e → e = 0 ∨ e = 1 :=
    fun _ he ↦ ConnectedSpectrum.eq_zero_or_one_of_injective (f := η.symm.toRingHom)
      η.symm.injective (PrimeSpectrum.preconnectedSpace_iff_isIdempotentElem.mp inferInstance) he
  refine PrimeSpectrum.connectedSpace_iff_isIdempotentElem.mpr fun e he ↦ ?_
  refine ConnectedSpectrum.eq_zero_or_one_of_injective
    (f := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k K (AlgebraicClosure K))
      (AlgHom.id k S)).toRingHom)
    (tensorProduct_map_injective _ _ ?_ fun _ _ hab ↦ hab) hL he
  exact (algebraMap K (AlgebraicClosure K)).injective

/-! ### The fibres of `Spec (R ⊗[k] S) → Spec R` -/

/-- For `S` geometrically connected over `k`, the fibre of `Spec (R ⊗[k] S) → Spec R` over each
point `p` is connected. -/
private theorem isConnected_preimage_singleton (k : Type u) [Field k] (S : Type v) [CommRing S]
    [Algebra k S] [Algebra.IsGeometricallyConnected k S] (R : Type w) [CommRing R] [Algebra k R]
    (p : PrimeSpectrum R) :
    IsConnected (PrimeSpectrum.comap (algebraMap R (R ⊗[k] S)) ⁻¹' {p}) := by
  have : IsScalarTower k R p.asIdeal.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    rw [IsScalarTower.algebraMap_apply k (Localization.AtPrime p.asIdeal) p.asIdeal.ResidueField,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime p.asIdeal) p.asIdeal.ResidueField,
      IsScalarTower.algebraMap_apply k R (Localization.AtPrime p.asIdeal)]
  have hconn : ConnectedSpace (PrimeSpectrum (p.asIdeal.ResidueField ⊗[k] S)) :=
    connectedSpace_primeSpectrum_tensorProduct k S p.asIdeal.ResidueField
  have η : p.asIdeal.ResidueField ⊗[R] (R ⊗[k] S) ≃ₐ[R] p.asIdeal.ResidueField ⊗[k] S :=
    Algebra.TensorProduct.cancelBaseChange k R R p.asIdeal.ResidueField S
  have hfib : ConnectedSpace (PrimeSpectrum (p.asIdeal.Fiber (R ⊗[k] S))) :=
    (PrimeSpectrum.homeomorphOfRingEquiv η.toRingEquiv).connectedSpace_iff.mpr hconn
  exact isConnected_iff_connectedSpace.mpr
    ((PrimeSpectrum.preimageHomeomorphFiber R (R ⊗[k] S) p).connectedSpace_iff.mpr hfib)

/-! ### The lemma -/

/-- Let `k` be a field, let `S` be a geometrically connected `k`-algebra and let `R` be any
`k`-algebra. Then `R → R ⊗[k] S`, `r ↦ r ⊗ 1`, restricts to a bijection from the
idempotents of `R` onto the idempotents of `R ⊗[k] S`, and the induced map
`Spec (R ⊗[k] S) → Spec R` is a bijection on connected components. -/
public theorem solution (k : Type u) [Field k] (S : Type v) [CommRing S] [Algebra k S]
    [Algebra.IsGeometricallyConnected k S] (R : Type w) [CommRing R] [Algebra k R] :
    Set.BijOn (algebraMap R (R ⊗[k] S)) {e | IsIdempotentElem e} {e | IsIdempotentElem e} ∧
      Function.Bijective (PrimeSpectrum.continuous_comap
        (algebraMap R (R ⊗[k] S))).connectedComponentsMap := by
  have hfib := isConnected_preimage_singleton k S R
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R (R ⊗[k] S))) :=
    fun p ↦ (hfib p).nonempty
  have hq : Topology.IsQuotientMap (PrimeSpectrum.comap (algebraMap R (R ⊗[k] S))) :=
    PrimeSpectrum.isQuotientMap_of_generalizingMap hsurj
      (RingHom.Flat.generalizingMap_comap (RingHom.flat_algebraMap_iff.mpr inferInstance))
  exact ⟨bijOn_isIdempotentElem_of_isQuotientMap _ hq hfib,
    hq.isCoinducing.connectedComponentsMap_bijective hfib⟩

end Stacks.TensorProduct.IdempotentBijection

end

@[expose] public section

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- **Base change along a geometrically connected algebra.** Let `k` be a field, let `S` be a
geometrically connected `k`-algebra and let `R` be any `k`-algebra. Then `R → R ⊗[k] S`,
`r ↦ r ⊗ 1`, restricts to a bijection from the idempotents of `R` onto the idempotents of
`R ⊗[k] S`, and the induced map `Spec (R ⊗[k] S) → Spec R` is a bijection on connected
components. -/
@[stacks 037W "Base change of an arbitrary `k`-algebra `R` along a geometrically connected
  `k`-algebra `S` induces a bijection on idempotents and a bijection on connected components of
  the spectra. Both assertions of the lemma; the second is stated as a bijection, as in the
  source, rather than as the homeomorphism of Varieties, Lemma 0385."]
public theorem bijOn_isIdempotentElem_and_bijective_connectedComponentsMap
    (k : Type u) [Field k] (S : Type v) [CommRing S] [Algebra k S]
    [IsGeometricallyConnected k S] (R : Type w) [CommRing R] [Algebra k R] :
    Set.BijOn (algebraMap R (R ⊗[k] S)) {e | IsIdempotentElem e} {e | IsIdempotentElem e} ∧
      Function.Bijective (PrimeSpectrum.continuous_comap
        (algebraMap R (R ⊗[k] S))).connectedComponentsMap :=
  Stacks.TensorProduct.IdempotentBijection.solution k S R

end Algebra.TensorProduct

end
