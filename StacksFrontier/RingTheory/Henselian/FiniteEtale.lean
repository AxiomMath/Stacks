module

public import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.Topology.Sheaves.Presheaf

public import StacksFrontier.RingTheory.Etale.ResidueFieldExtension
import StacksFrontier.RingTheory.Henselian.FiniteType.Basic
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Ideal.JacobsonIntegral

@[expose] public section

universe u

/-!
# Finite étale algebras over a henselian local ring

Let `(R, 𝔪, κ)` be a henselian local ring. This file proves Lemma 04GK: base change along the
residue map `R → κ` is an equivalence from the category of finite étale `R`-algebras to the
category of finite étale `κ`-algebras.

The three halves of the statement are separated into algebra:

* *Faithfulness* is `algHom_ext_of_residue`: two `R`-algebra maps `S → T` out of an unramified
  `S` into a `T` integral over `R` which agree modulo `𝔪T` are equal. The proof is the diagonal
  idempotent. Unramifiedness makes the kernel of `S ⊗[R] S → S` an idempotent ideal
  (`Ideal.cotangent_subsingleton_iff`), finite generation
  (`KaehlerDifferential.ideal_fg`) turns that into a generating idempotent `δ`, and the two maps
  assemble into `H : S ⊗[R] S →ₐ[R] T`. Agreement mod `𝔪T` says `H δ ∈ 𝔪T`; as `𝔪T` lies in the
  Jacobson radical of `T` (every maximal ideal of `T` contracts to `𝔪`, `T` being integral over
  the local ring `R`) and `H δ` is idempotent, `H δ = 0`. So the whole of `ker(S ⊗[R] S → S)`
  dies under `H`, and `s ⊗ 1 - 1 ⊗ s` lies there. Note that henselianity is not used here.

* *Fullness* is `exists_algHom_of_residue`, and *essential surjectivity* is
  `exists_finiteEtale_residue`. These two are where henselianity enters, through the lifting of
  idempotents from
  the closed fibre of a finite algebra over a henselian local ring (Lemma 04GJ,
  `henselian_lift_single_idem`).

## Main results

* `Stacks.Henselian.FiniteEtaleEquivalence.solution`: the statement of Lemma 04GK.

## Implementation notes

The functor of the source, `S ↦ S/𝔪S`, is Mathlib's base change functor
`CommAlgCat.FiniteEtale.baseChange R κ`, `S ↦ κ ⊗[R] S`; the identification of the two is
`Algebra.TensorProduct.quotIdealMapEquivQuotTensor`, and it is that identification which carries
each of the three algebraic lemmas below to the corresponding categorical property. The lemmas are
therefore stated in the quotient picture `S ⧸ 𝔪S`, where the residue map is a ring quotient and
`Ideal.Quotient.mk` is available, and the equivalence is transported once.

`Functor.IsEquivalence` is assembled from `Full`, `Faithful` and `EssSurj`, which are produced by
`private` lemmas rather than instances so that nothing in this file leaks into its importers.

## References

* [StacksProject 04GK](https://stacks.math.columbia.edu/tag/04GK)
-/

@[expose] public section

namespace Stacks.Henselian.FiniteEtaleEquivalence

open TensorProduct CategoryTheory IsLocalRing CommAlgCat

/-! ### Idempotents and the Jacobson radical -/

/-- An idempotent in the Jacobson radical vanishes. -/
private lemma idem_eq_zero_of_mem_jacobson {T : Type*} [CommRing T] {x : T}
    (hx : IsIdempotentElem x) (hmem : x ∈ Ideal.jacobson (⊥ : Ideal T)) : x = 0 := by
  have hu : IsUnit (1 - x) :=
    Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (by simpa using neg_mem hmem)
  have h0 : x * (1 - x) = 0 := by rw [mul_sub, mul_one, hx.eq, sub_self]
  simpa using (hu.mul_left_eq_zero).mp h0

/-- Two `κ`-algebra maps out of a base change `κ ⊗[R] S` agree as soon as they agree on the
elements `1 ⊗ b`: those generate `κ ⊗[R] S` as a `κ`-algebra. -/
private lemma algHom_ext_one_tmul {R : Type*} [CommRing R] {κ : Type*} [CommRing κ] [Algebra R κ]
    {S : Type*} [CommRing S] [Algebra R S] {C : Type*} [CommRing C] [Algebra κ C] [Algebra R C]
    [IsScalarTower R κ C] (F G : (κ ⊗[R] S) →ₐ[κ] C)
    (h : ∀ b : S, F ((1 : κ) ⊗ₜ[R] b) = G ((1 : κ) ⊗ₜ[R] b)) : F = G := by
  refine AlgHom.restrictScalars_injective R ?_
  refine Algebra.TensorProduct.ext' fun a b => ?_
  have hsm : a ⊗ₜ[R] b = a • ((1 : κ) ⊗ₜ[R] b) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  change F (a ⊗ₜ[R] b) = G (a ⊗ₜ[R] b)
  rw [hsm, map_smul, map_smul, h b]

/-! ### Faithfulness -/

/-- Two `R`-algebra maps out of an unramified `R`-algebra `S` into an `R`-algebra `T` integral
over the local ring `R` which agree modulo `𝔪T` are equal.

This is the faithfulness half of Lemma 04GK, and it needs neither finiteness of `S` nor
henselianity of `R`. -/
@[ega "IV 18.5.15" "partial"]
private lemma algHom_ext_of_residue (R : Type u) [CommRing R] [IsLocalRing R] {S : Type*}
    [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    {T : Type*} [CommRing T] [Algebra R T] [Algebra.IsIntegral R T] {φ ψ : S →ₐ[R] T}
    (h :
      ∀ s : S,
        Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R T)) (φ s) =
          Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R T)) (ψ s)) :
    φ = ψ := by
  classical
  obtain ⟨δ, hδ, hspan⟩ :
    ∃ e, IsIdempotentElem e ∧ KaehlerDifferential.ideal R S = Ideal.span {e} :=
    (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg R S)).mp <|
      (Ideal.cotangent_subsingleton_iff _).mp <| inferInstanceAs <| Subsingleton (Ω[S⁄R])
  set I : Ideal T := (maximalIdeal R).map (algebraMap R T) with hI
  set H : S ⊗[R] S →ₐ[R] T := Algebra.TensorProduct.lift φ ψ (fun _ _ => Commute.all _ _) with hH
  have key :
    (Ideal.Quotient.mkₐ R I).comp H =
      ((Ideal.Quotient.mkₐ R I).comp φ).comp (Algebra.TensorProduct.lmul' R) := by
    refine Algebra.TensorProduct.ext' fun a b => ?_
    simp [hH, Algebra.TensorProduct.lift_tmul, h b]
  have hδmem : δ ∈ KaehlerDifferential.ideal R S := by
    rw [hspan]; exact Ideal.mem_span_singleton_self _
  have hHδ : H δ = 0 := by
    refine idem_eq_zero_of_mem_jacobson (hδ.map H) (map_maximalIdeal_le_jacobson R T ?_)
    have hcong := AlgHom.congr_fun key δ
    simp only [AlgHom.comp_apply] at hcong
    rw [show (Algebra.TensorProduct.lmul' R (S := S)) δ = 0 from hδmem] at hcong
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hcong
  ext s
  have hmem : s ⊗ₜ[R] (1 : S) - (1 : S) ⊗ₜ[R] s ∈ KaehlerDifferential.ideal R S := by
    simp [KaehlerDifferential.ideal, RingHom.mem_ker]
  rw [hspan, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hz : H (s ⊗ₜ[R] (1 : S) - (1 : S) ⊗ₜ[R] s) = 0 := by rw [hc, map_mul, hHδ, zero_mul]
  rw [map_sub, hH] at hz
  simp only [Algebra.TensorProduct.lift_tmul, map_one, mul_one, one_mul, sub_eq_zero] at hz
  exact hz

/-! ### Lifting units and idempotents from the closed fibre -/

/-- If `J` is contained in the Jacobson radical, a unit modulo `J` is a unit. -/
private lemma isUnit_of_isUnit_quotient {A : Type*} [CommRing A] {J : Ideal A}
    (hJ : J ≤ Ideal.jacobson (⊥ : Ideal A)) {x : A} (h : IsUnit (Ideal.Quotient.mk J x)) :
    IsUnit x := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (A ⧸ J)ˣ) : A ⧸ J)
  have hxy : Ideal.Quotient.mk J (x * y - 1) = 0 := by
    rw [map_sub, map_mul, hy, ← hu, map_one, u.mul_inv, sub_self]
  exact isUnit_of_mul_isUnit_left
    (Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hJ (Ideal.Quotient.eq_zero_iff_mem.mp hxy)))

/-! ### A monogenic étale algebra

Mathlib has the forward direction of Lemma 3.2 of [arXiv:2503.07846] — a finite étale extension
of local rings is `R[β]` with `f'(β)` a unit — in `Mathlib/RingTheory/LocalRing/Etale.lean`, and
lists the converse as future work. The converse is what the lift of a separable residue field
extension needs, so it is proved here. -/

/-- If `f` is monic and `f'` is a unit at the adjoined root, then `R[X]/(f)` is étale over `R`.

This is the converse of `IsLocalRing.isUnit_aeval_derivative_minpoly_of_adjoin_eq_top`, and holds
over an arbitrary commutative ring: `⟨f, f'⟩` is a `StandardEtalePair`, whose standard étale
algebra is `(R[X]/(f))[1/f'(x)]`, and localizing at a unit changes nothing. -/
private lemma etale_adjoinRoot_of_isUnit_aeval_derivative {R : Type*} [CommRing R]
    {f : Polynomial R} (hf : f.Monic)
    (hu : IsUnit (Polynomial.aeval (AdjoinRoot.root f) (Polynomial.derivative f))) :
    Algebra.Etale R (AdjoinRoot f) := by
  set P : StandardEtalePair R :=
    { f := f, monic_f := hf, g := Polynomial.derivative f, cond := ⟨1, 0, 1, by ring⟩ } with hP
  have hu' : IsUnit (AdjoinRoot.mk P.f P.g) := by simpa [hP, AdjoinRoot.aeval_eq] using hu
  have hle : Submonoid.powers (AdjoinRoot.mk P.f P.g) ≤ IsUnit.submonoid (AdjoinRoot P.f) := by
    rintro x ⟨n, rfl⟩
    exact hu'.pow n
  have e1 : AdjoinRoot P.f ≃ₐ[AdjoinRoot P.f] Localization.Away (AdjoinRoot.mk P.f P.g) :=
    IsLocalization.atUnits _ _ hle
  exact Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans (e1.restrictScalars R).symm)

/-- **Lifting a finite separable residue field extension.** Over a local ring `R` with residue
field `κ`, every finite separable field extension `L/κ` is the closed fibre of a finite étale
`R`-algebra: write `L = κ(β)`, lift the minimal polynomial `f̄ = minpoly κ β` to a monic `f ∈ R[X]`
of the same degree and take `A = R[X]/(f)`.

The comparison map `κ ⊗[R] A → L` is surjective because `β` generates `L`, and injective because
both sides have `κ`-dimension `deg f`; and `f'` is a unit in `A` because it is one in the fibre
`L` (separability) and `𝔪A` lies in the Jacobson radical of `A`. Henselianity of `R` is not
needed. -/
@[sga "3 VIA 1.2" "special case",
  sga "3 XXIV 3.9.1" "special case",
  sga "3 XXIV 8.1.2" "more general"]
private lemma exists_finiteEtale_of_isSeparable (R : Type u) [CommRing R] [IsLocalRing R]
    (L : Type u) [Field L] [Algebra (ResidueField R) L] [Module.Finite (ResidueField R) L]
    [Algebra.IsSeparable (ResidueField R) L] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A) (_ :
      Algebra.Etale R A), Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] L) := by
  classical
  let : Algebra R L :=
    ((algebraMap (ResidueField R) L).comp (algebraMap R (ResidueField R))).toAlgebra
  have : IsScalarTower R (ResidueField R) L := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional (ResidueField R) L := inferInstance
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element (ResidueField R) L
  have hi : IsIntegral (ResidueField R) β := Algebra.IsIntegral.isIntegral β
  have hadj : Algebra.adjoin (ResidueField R) {β} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic, hβ]; rfl
  have hrk : Module.finrank (ResidueField R) L = (minpoly (ResidueField R) β).natDegree := by
    rw [← IntermediateField.adjoin.finrank hi, hβ, IntermediateField.finrank_top']
  have hmonic : (minpoly (ResidueField R) β).Monic := minpoly.monic hi
  obtain ⟨f0, hf0⟩ :=
    Polynomial.map_surjective (algebraMap R (ResidueField R)) Ideal.Quotient.mk_surjective
      (minpoly (ResidueField R) β)
  obtain ⟨f, hfmap, hfdeg, hfmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic ((Polynomial.mem_lifts _).2 ⟨f0, hf0⟩) hmonic
  have hfin : Module.Finite R (AdjoinRoot f) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis' hfmonic).basis
  have hfree : Module.Free R (AdjoinRoot f) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hfmonic).basis
  have hroot : (Polynomial.aeval β) f = 0 := by
    rw [← Polynomial.aeval_map_algebraMap (ResidueField R) β f, hfmap]
    exact minpoly.aeval _ _
  set Φ : ResidueField R ⊗[R] AdjoinRoot f →ₐ[ResidueField R] L :=
    Algebra.TensorProduct.lift (Algebra.ofId (ResidueField R) L)
      (AdjoinRoot.liftAlgHom f (Algebra.ofId R L) β (by simpa [Polynomial.aeval_def] using hroot))
      (fun _ _ => Commute.all _ _) with
    hΦ
  have hΦmk :
    ∀ p : Polynomial R,
      Φ ((1 : ResidueField R) ⊗ₜ[R] AdjoinRoot.mk f p) = Polynomial.aeval β p := by
    intro p
    simp [hΦ, Algebra.TensorProduct.lift_tmul, Polynomial.aeval_def]
  have hsurj : Function.Surjective Φ := by
    rw [← AlgHom.range_eq_top, eq_top_iff, ← hadj]
    refine
      Algebra.adjoin_le
        (Set.singleton_subset_iff.2 ⟨(1 : ResidueField R) ⊗ₜ[R] AdjoinRoot.root f, ?_⟩)
    simpa using hΦmk Polynomial.X
  have hdim :
    Module.finrank (ResidueField R) (ResidueField R ⊗[R] AdjoinRoot f) =
      Module.finrank (ResidueField R) L := by
    rw [Module.finrank_baseChange, (AdjoinRoot.powerBasis' hfmonic).finrank, hrk,
      AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_eq_of_degree_eq hfdeg]
  have hbij : Function.Bijective Φ :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := Φ.toLinearMap)).2 hsurj,
      hsurj⟩
  set E : ResidueField R ⊗[R] AdjoinRoot f ≃ₐ[ResidueField R] L := AlgEquiv.ofBijective Φ hbij with
    hE
  -- `f'` is a unit at the root, because it is one in the closed fibre.
  have hsep :
    IsCoprime (minpoly (ResidueField R) β) (Polynomial.derivative (minpoly (ResidueField R) β)) :=
    Algebra.IsSeparable.isSeparable (ResidueField R) β
  obtain ⟨a, b, hab⟩ := hsep
  have hderiv :
    IsUnit (Polynomial.aeval β (Polynomial.derivative (minpoly (ResidueField R) β))) := by
    have h1 := congrArg (Polynomial.aeval (R := ResidueField R) β) hab
    simp only [map_add, map_mul, map_one, minpoly.aeval, mul_zero, zero_add] at h1
    exact
      isUnit_iff_exists_inv.2
        ⟨Polynomial.aeval β b, by
          rw [mul_comm]; exact h1⟩
  have hfibre :
    IsUnit
      (Φ
        ((1 : ResidueField R) ⊗ₜ[R]
          Polynomial.aeval (AdjoinRoot.root f) (Polynomial.derivative f))) := by
    rw [AdjoinRoot.aeval_eq, hΦmk]
    rw [← Polynomial.aeval_map_algebraMap (ResidueField R) β (Polynomial.derivative f), ←
      Polynomial.derivative_map, hfmap]
    exact hderiv
  have hunit1 :
    IsUnit
      ((1 : ResidueField R) ⊗ₜ[R]
        Polynomial.aeval (AdjoinRoot.root f) (Polynomial.derivative f)) := by
    have := hfibre.map E.symm
    simpa [hE] using this
  have hunit : IsUnit (Polynomial.aeval (AdjoinRoot.root f) (Polynomial.derivative f)) := by
    refine isUnit_of_isUnit_quotient (map_maximalIdeal_le_jacobson R (AdjoinRoot f)) ?_
    set Q := Algebra.TensorProduct.quotIdealMapEquivQuotTensor (AdjoinRoot f) (maximalIdeal R) with
      hQ
    have hx :
      Q
          (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R (AdjoinRoot f)))
            (Polynomial.aeval (AdjoinRoot.root f) (Polynomial.derivative f))) =
        (1 : R ⧸ maximalIdeal R) ⊗ₜ[R]
          Polynomial.aeval (AdjoinRoot.root f) (Polynomial.derivative f) :=
      Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk _ _ _
    have hunit1' :
      IsUnit
        ((1 : R ⧸ maximalIdeal R) ⊗ₜ[R]
          Polynomial.aeval (AdjoinRoot.root f) (Polynomial.derivative f)) :=
      hunit1
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hunit1'
    refine isUnit_iff_exists_inv.mpr ⟨Q.symm y, Q.injective ?_⟩
    rw [map_mul, map_one, hx, Q.apply_symm_apply]
    exact hy
  have := etale_adjoinRoot_of_isUnit_aeval_derivative hfmonic hunit
  exact ⟨AdjoinRoot f, inferInstance, inferInstance, hfin, inferInstance, ⟨E⟩⟩

/-! ### Kernels of retractions -/

/-- **The kernel of a retraction of a formally unramified algebra is an idempotent ideal.**
If `A` is a formally unramified `k`-algebra and `σ : A →ₐ[k] B` admits a section
`s : B →ₐ[k] A`, then `ker σ = (ker σ)²`.

Modulo `(ker σ)²` the two `k`-algebra maps `A → A ⧸ (ker σ)²` given by the quotient map and by
`s ∘ σ` followed by the quotient map differ by an element of the square-zero ideal
`ker σ / (ker σ)²`, so formal unramifiedness (`Algebra.FormallyUnramified.ext`) forces them to be
equal; evaluating at an element of `ker σ` gives the claim.

Geometrically this is the statement that a section of an unramified morphism is an open immersion:
combined with finite generation of `ker σ` (`Ideal.isIdempotentElem_iff_of_fg`) it exhibits
`ker σ` as generated by an idempotent, so that `A ≅ B × A/(ker σ)`. -/
private lemma isIdempotentElem_ker_of_formallyUnramified {k A B : Type*} [CommRing k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] [Algebra.FormallyUnramified k A] (σ : A →ₐ[k] B)
    (s : B →ₐ[k] A) (hs : ∀ b, σ (s b) = b) : IsIdempotentElem (RingHom.ker (σ : A →+* B)) := by
  set K : Ideal A := RingHom.ker (σ : A →+* B) with hKdef
  set I : Ideal (A ⧸ K ^ 2) := K.map (Ideal.Quotient.mk (K ^ 2)) with hIdef
  have hnil : IsNilpotent I := by
    have hmul : I * I ≤ ⊥ := by
      refine Ideal.mul_le.mpr fun a ha b hb => ?_
      obtain ⟨a', ha', rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp ha
      obtain ⟨b', hb', rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hb
      have hmm : a' * b' ∈ K ^ 2 := by
        rw [pow_two K]; exact Ideal.mul_mem_mul ha' hb'
      have h0 : (Ideal.Quotient.mk (K ^ 2)) (a' * b') = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmm
      rw [map_mul] at h0
      exact Ideal.mem_bot.mpr h0
    refine ⟨2, ?_⟩
    rw [Ideal.zero_eq_bot, show I ^ 2 = I * I from sq I]
    exact le_antisymm hmul bot_le
  have key : Ideal.Quotient.mkₐ k (K ^ 2) = (Ideal.Quotient.mkₐ k (K ^ 2)).comp (s.comp σ) := by
    refine Algebra.FormallyUnramified.ext I hnil fun a => ?_
    refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
    have hmem : a - s (σ a) ∈ K := by
      simp only [hKdef, RingHom.mem_ker, AlgHom.coe_toRingHom, map_sub, hs, sub_self]
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk (K ^ 2)) hmem
    rwa [map_sub] at this
  refine le_antisymm Ideal.mul_le_left fun x hx => ?_
  have hσx : σ x = 0 := hx
  have h1 := AlgHom.congr_fun key x
  rw [AlgHom.comp_apply, AlgHom.comp_apply, hσx, map_zero, map_zero] at h1
  have h2 : Ideal.Quotient.mk (K ^ 2) x = 0 := h1
  rw [show K * K = K ^ 2 from (sq K).symm]
  exact (Ideal.Quotient.eq_zero_iff_mem).mp h2

/-! ### Fullness -/

/-- **A retraction of the closed fibre lifts.** Let `R` be a henselian local ring, `T` a finite
étale `R`-algebra and `U` a `T`-algebra which is étale over `T` and module-finite over `R`. Then
every `R`-algebra map `h : U → T ⧸ 𝔪T` which is the identity on `T` is the reduction of a
`T`-algebra retraction `σ : U →ₐ[T] T`.

The kernel of the induced retraction `σ̄ : U ⧸ 𝔪U → T ⧸ 𝔪T` of the closed fibres is an idempotent
ideal (`isIdempotentElem_ker_of_formallyUnramified`, `U ⧸ 𝔪U` being étale over `κ`) of a
noetherian ring, hence `span {f̄}` for an idempotent `f̄`. Henselianity enters exactly once:
`henselian_lift_single_idem` lifts `f̄` to an idempotent `f ∈ U`, and `V = U ⧸ span {f}` is then a
finite étale `T`-algebra with `algebraMap T V` bijective — surjective by Nakayama
(`LinearMap.surjective_of_surjective_comp_mkQ`), and injective because its kernel `K` is
idempotent (`Algebra.FormallyEtale.iff_of_surjective`), contained in `𝔪T`, and finitely generated
(`Algebra.FinitePresentation.ker_fG_of_surjective`), so that `K = K·K ⊆ 𝔪T·K` and Nakayama
applies again (`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`, `map_maximalIdeal_le_jacobson`).
Inverting it gives `σ`. -/
@[sga "3 X 4.5" "special case"]
private lemma exists_algHom_of_retraction (R : Type u) [CommRing R] [HenselianLocalRing R]
    (T : Type u) [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T] (U : Type u)
    [CommRing U] [Algebra R U] [Algebra T U] [IsScalarTower R T U] [Module.Finite R U]
    [Algebra.Etale T U] (h : U →ₐ[R] T ⧸ (maximalIdeal R).map (algebraMap R T))
    (hh :
      ∀ t : T,
        h (algebraMap T U t) = Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R T)) t) :
    ∃ σ : U →ₐ[T] T,
      ∀ u : U, Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R T)) (σ u) = h u := by
  classical
  have : Algebra.Etale R U := Algebra.Etale.comp R T U
  have : Module.Finite T U := Module.Finite.of_restrictScalars_finite R T U
  have : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  have :
    Algebra.FormallyUnramified (R ⧸ maximalIdeal R) (U ⧸ (maximalIdeal R).map (algebraMap R U)) :=
    Algebra.FormallyUnramified.of_equiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor U (maximalIdeal R)).symm
  have : Module.Finite (R ⧸ maximalIdeal R) (U ⧸ (maximalIdeal R).map (algebraMap R U)) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor U (maximalIdeal R)).symm.toLinearEquiv
  have : IsNoetherianRing (R ⧸ maximalIdeal R) :=
    isNoetherianRing_of_ringEquiv (ResidueField R) (RingEquiv.refl _)
  have : IsNoetherianRing (U ⧸ (maximalIdeal R).map (algebraMap R U)) :=
    IsNoetherianRing.of_finite (R ⧸ maximalIdeal R) _
  -- The retraction of the closed fibres and its section.
  set sig :
    (U ⧸ (maximalIdeal R).map (algebraMap R U)) →ₐ[R ⧸ maximalIdeal R]
      (T ⧸ (maximalIdeal R).map (algebraMap R T)) :=
    (Algebra.TensorProduct.lift
          (Algebra.ofId (R ⧸ maximalIdeal R) (T ⧸ (maximalIdeal R).map (algebraMap R T))) h
          (fun _ _ => Commute.all _ _)).comp
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor U (maximalIdeal R)).toAlgHom with
    hsigdef
  have hsig :
    ∀ u : U, sig (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R U)) u) = h u := by
    intro u
    rw [hsigdef]
    simp [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk, Algebra.TensorProduct.lift_tmul]
  set sec :
    (T ⧸ (maximalIdeal R).map (algebraMap R T)) →ₐ[R ⧸ maximalIdeal R]
      (U ⧸ (maximalIdeal R).map (algebraMap R U)) :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor U (maximalIdeal R)).symm.toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id (R ⧸ maximalIdeal R) (R ⧸ maximalIdeal R))
            (IsScalarTower.toAlgHom R T U)).comp
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T (maximalIdeal R)).toAlgHom) with
    hsecdef
  have hsec :
    ∀ t : T,
      sec (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R T)) t) =
        Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R U)) (algebraMap T U t) := by
    intro t
    refine (Algebra.TensorProduct.quotIdealMapEquivQuotTensor U (maximalIdeal R)).injective ?_
    rw [hsecdef]
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.apply_symm_apply,
      Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, IsScalarTower.coe_toAlgHom']
  -- Its kernel is generated by an idempotent, which lifts by henselianity.
  obtain ⟨fb, hfb, hspan⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian _)).mp
      (isIdempotentElem_ker_of_formallyUnramified sig sec fun b => by
        obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective b
        rw [hsec, hsig, hh])
  obtain ⟨f, hf, hfmk⟩ := henselian_lift_single_idem R U fb hfb
  set J : Ideal U := Ideal.span {f} with hJdef
  have hkerJ :
    RingHom.ker
        (sig :
          (U ⧸ (maximalIdeal R).map (algebraMap R U)) →+*
            (T ⧸ (maximalIdeal R).map (algebraMap R T))) =
      J.map (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R U))) := by
    rw [hJdef, Ideal.map_span, Set.image_singleton, hfmk, hspan]
  -- Elements of `J` die under `h`, and `h u = mk t` puts `u - t` into `J + 𝔪U`.
  have hJh : ∀ x : U, x ∈ J → h x = 0 := fun x hx => by
    rw [← hsig x]
    exact hkerJ.ge (Ideal.mem_map_of_mem _ hx)
  have key :
    ∀ u : U, ∃ t : T, u - algebraMap T U t ∈ J ⊔ (maximalIdeal R).map (algebraMap R U) := by
    intro u
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (h u)
    refine ⟨t, ?_⟩
    have h1 :
      Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R U)) (u - algebraMap T U t) ∈
        RingHom.ker
          (sig :
            (U ⧸ (maximalIdeal R).map (algebraMap R U)) →+*
              (T ⧸ (maximalIdeal R).map (algebraMap R T))) := by
      rw [RingHom.mem_ker]
      change sig _ = 0
      rw [map_sub, map_sub, hsig, hsig, hh, ht, sub_self]
    rw [hkerJ] at h1
    obtain ⟨y, hy, hy'⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h1
    have h2 : u - algebraMap T U t - y ∈ (maximalIdeal R).map (algebraMap R U) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hy', sub_self]
    rw [show u - algebraMap T U t = y + (u - algebraMap T U t - y) by ring]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hy) (Ideal.mem_sup_right h2)
  -- `V = U ⧸ J` is a finite étale `T`-algebra.
  have : Algebra.FormallyEtale U (U ⧸ J) :=
    (Algebra.FormallyEtale.iff_of_surjective Ideal.Quotient.mk_surjective).mpr <| by
      change
        RingHom.ker (algebraMap U (U ⧸ J)) * RingHom.ker (algebraMap U (U ⧸ J)) =
          RingHom.ker (algebraMap U (U ⧸ J))
      rw [show RingHom.ker (algebraMap U (U ⧸ J)) = J from Ideal.mk_ker, hJdef,
        Ideal.span_singleton_mul_span_singleton, hf.eq]
  have : Algebra.FinitePresentation U (U ⧸ J) :=
    Algebra.FinitePresentation.quotient (hJdef ▸ Submodule.fg_span_singleton f)
  have : Algebra.Etale U (U ⧸ J) := ⟨inferInstance, inferInstance⟩
  have : Algebra.Etale T (U ⧸ J) := Algebra.Etale.comp T U (U ⧸ J)
  -- `algebraMap T (U ⧸ J)` is surjective, by Nakayama.
  have hmap :
    ∀ z : U,
      z ∈ (maximalIdeal R).map (algebraMap R U) →
        Ideal.Quotient.mk J z ∈
          ((maximalIdeal R).map (algebraMap R T)) • (⊤ : Submodule T (U ⧸ J)) := by
    intro z hz
    have h7 :
      ((maximalIdeal R).map (algebraMap R U)).map (Ideal.Quotient.mk J) =
        ((maximalIdeal R).map (algebraMap R T)).map (algebraMap T (U ⧸ J)) := by
      rw [Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq R T (U ⧸ J),
        show (Ideal.Quotient.mk J).comp (algebraMap R U) = algebraMap R (U ⧸ J) from rfl]
    have h8 := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hz
    rw [h7] at h8
    rw [Ideal.smul_top_eq_map]
    exact h8
  have hsurj : Function.Surjective (algebraMap T (U ⧸ J)) := by
    refine
      LinearMap.surjective_of_surjective_comp_mkQ (Algebra.linearMap T (U ⧸ J))
        ((maximalIdeal R).map (algebraMap R T)) (map_maximalIdeal_le_jacobson R T) ?_
    intro y
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective v
    obtain ⟨t, hts⟩ := key u
    obtain ⟨y₁, hy₁, z, hz, hsum⟩ := Submodule.mem_sup.mp hts
    refine ⟨t, ?_⟩
    have h3 : Ideal.Quotient.mk J u - algebraMap T (U ⧸ J) t = Ideal.Quotient.mk J z := by
      change Ideal.Quotient.mk J u - Ideal.Quotient.mk J (algebraMap T U t) = _
      rw [← map_sub, ← hsum, map_add, (Ideal.Quotient.eq_zero_iff_mem).mpr hy₁, zero_add]
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply,
      Submodule.mkQ_apply]
    refine (Submodule.Quotient.eq _).mpr ?_
    rw [show
        algebraMap T (U ⧸ J) t - Ideal.Quotient.mk J u =
          -(Ideal.Quotient.mk J u - algebraMap T (U ⧸ J) t)
        by ring,
      h3]
    exact neg_mem (hmap z hz)
  -- and injective, by Nakayama again.
  have hinj : Function.Injective (algebraMap T (U ⧸ J)) := by
    have hk2 : RingHom.ker (algebraMap T (U ⧸ J)) ≤ (maximalIdeal R).map (algebraMap R T) := by
      intro t ht
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hh t]
      exact hJh _ ((Ideal.Quotient.eq_zero_iff_mem).mp ht)
    have hk1 : IsIdempotentElem (RingHom.ker (algebraMap T (U ⧸ J))) :=
      (Algebra.FormallyEtale.iff_of_surjective hsurj).mp inferInstance
    have hk3 : (RingHom.ker (algebraMap T (U ⧸ J))).FG :=
      Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId T (U ⧸ J)) hsurj
    have hbot :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot ((maximalIdeal R).map (algebraMap R T))
        (RingHom.ker (algebraMap T (U ⧸ J))) hk3
        (by
          calc
            RingHom.ker (algebraMap T (U ⧸ J)) ≤
                RingHom.ker (algebraMap T (U ⧸ J)) * RingHom.ker (algebraMap T (U ⧸ J)) :=
              le_of_eq hk1.eq.symm
            _ ≤ (maximalIdeal R).map (algebraMap R T) * RingHom.ker (algebraMap T (U ⧸ J)) :=
              Ideal.mul_mono hk2 le_rfl
            _ = (maximalIdeal R).map (algebraMap R T) • RingHom.ker (algebraMap T (U ⧸ J)) :=
              (Ideal.smul_eq_mul _ _).symm)
        (map_maximalIdeal_le_jacobson R T)
    exact (RingHom.injective_iff_ker_eq_bot _).mpr hbot
  -- Invert and read off the retraction.
  set E : T ≃ₐ[T] (U ⧸ J) := AlgEquiv.ofBijective (Algebra.ofId T (U ⧸ J)) ⟨hinj, hsurj⟩ with hEdef
  refine ⟨(E.symm.toAlgHom).comp (Ideal.Quotient.mkₐ T J), fun u => ?_⟩
  have hEu : algebraMap T U (E.symm (Ideal.Quotient.mk J u)) - u ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    exact E.apply_symm_apply (Ideal.Quotient.mk J u)
  have h5 : h (algebraMap T U (E.symm (Ideal.Quotient.mk J u))) - h u = 0 := by
    rw [← map_sub]; exact hJh _ hEu
  change
    Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R T)) (E.symm (Ideal.Quotient.mk J u)) =
      h u
  rw [← hh (E.symm (Ideal.Quotient.mk J u))]
  exact sub_eq_zero.mp h5

/-- **Fullness** of `S ↦ κ ⊗[R] S` on finite étale algebras over a henselian local ring:
every `κ`-algebra map between the closed fibres is the reduction of an `R`-algebra map `S → T`.

An `R`-algebra map `S → T` is the same as a `T`-algebra retraction `T ⊗[R] S →ₐ[T] T`, and `g`
gives such a retraction of the closed fibres; `exists_algHom_of_retraction` lifts it. -/
@[ega "IV 18.5.15" "partial"]
private lemma exists_algHom_of_residue (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S] [Algebra.Etale R S] (T : Type u)
    [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T]
    (g : (ResidueField R ⊗[R] S) →ₐ[ResidueField R] (ResidueField R ⊗[R] T)) :
    ∃ φ : S →ₐ[R] T,
      ∀ s : S, (1 : ResidueField R) ⊗ₜ[R] φ s = g ((1 : ResidueField R) ⊗ₜ[R] s) := by
  classical
  -- `ResidueField R` is `R ⧸ 𝔪`; read `g` in the latter picture, where the quotient API lives.
  -- The two types are definitionally equal, so `g` itself serves; `hg'` records that.
  obtain ⟨g', hg'⟩ :
    ∃ φ : ((R ⧸ maximalIdeal R) ⊗[R] S) →ₐ[R ⧸ maximalIdeal R] ((R ⧸ maximalIdeal R) ⊗[R] T),
      ∀ (b : T) (s : S),
        (1 : R ⧸ maximalIdeal R) ⊗ₜ[R] b = φ ((1 : R ⧸ maximalIdeal R) ⊗ₜ[R] s) →
          (1 : ResidueField R) ⊗ₜ[R] b = g ((1 : ResidueField R) ⊗ₜ[R] s) :=
    ⟨g, fun _ _ hb => hb⟩
  set gbar :=
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor T (maximalIdeal R)).symm.toAlgHom.comp
          g').comp
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (maximalIdeal R)).toAlgHom with
    hgbar
  set h : (T ⊗[R] S) →ₐ[R] T ⧸ (maximalIdeal R).map (algebraMap R T) :=
    Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ R _)
      ((gbar.restrictScalars R).comp (Ideal.Quotient.mkₐ R _)) (fun _ _ => Commute.all _ _) with
    hhdef
  obtain ⟨σ, hσ⟩ :=
    exists_algHom_of_retraction R T (T ⊗[R] S) h
      (fun t => by
        rw [hhdef]
        simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.lift_tmul])
  refine ⟨(σ.restrictScalars R).comp Algebra.TensorProduct.includeRight, fun s => ?_⟩
  have h1 :
    Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R T)) (σ ((1 : T) ⊗ₜ[R] s)) =
      gbar (Ideal.Quotient.mk _ s) := by
    rw [hσ, hhdef]
    simp [Algebra.TensorProduct.lift_tmul]
  -- `gbar` computes `g` on the elements `1 ⊗ s`, which generate the closed fibre of `S`.
  have h3 :
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor T (maximalIdeal R)
        (gbar (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) s)) =
      g' ((1 : R ⧸ maximalIdeal R) ⊗ₜ[R] s) := by
    rw [hgbar]
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.apply_symm_apply,
      Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
  have hkey :
    (1 : R ⧸ maximalIdeal R) ⊗ₜ[R] σ ((1 : T) ⊗ₜ[R] s) =
      g' ((1 : R ⧸ maximalIdeal R) ⊗ₜ[R] s) := by
    rw [← h3, ← h1, Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
  have hphi :
    ((σ.restrictScalars R).comp Algebra.TensorProduct.includeRight) s = σ ((1 : T) ⊗ₜ[R] s) := by
    simp
  rw [hphi]
  exact hg' _ s hkey

/-- **Essential surjectivity** of `S ↦ κ ⊗[R] S` on finite étale algebras: over a local ring `R`
with residue field `κ`, every finite étale `κ`-algebra `Λ` is the closed fibre of a finite étale
`R`-algebra.

`Λ` is a finite product of finite separable field extensions of `κ`
(`Algebra.Etale.iff_exists_algEquiv_prod`), each of which is lifted by
`exists_finiteEtale_of_isSeparable`; the product of the lifts works because base change commutes
with finite products (`Algebra.TensorProduct.piRight`). Henselianity of `R` is not needed. -/
@[ega "IV 18.3.3" "partial",
  ega "IV 18.5.15" "partial",
  ega "IV 18.8.6" "more general",
  sga "1 IX 1.8" "partial",
  sga "3 VIA 1.2" "special case",
  sga "3 XXIV 8.1.2" "more general",
  sga "7 IX 2.2.4" "partial"]
private lemma exists_finiteEtale_residue (R : Type u) [CommRing R] [IsLocalRing R] (Λ : Type u)
    [CommRing Λ] [Algebra (ResidueField R) Λ] [Algebra.Etale (ResidueField R) Λ] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Module.Finite R S) (_ :
      Algebra.Etale R S), Nonempty ((ResidueField R) ⊗[R] S ≃ₐ[ResidueField R] Λ) := by
  classical
  obtain ⟨ι, hι, L, hLfield, hLalg, eΛ, hL⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (ResidueField R) Λ).mp inferInstance
  have := hι
  let := hLfield
  let := hLalg
  have : Fintype ι := Fintype.ofFinite ι
  have : ∀ i, Module.Finite (ResidueField R) (L i) := fun i => (hL i).1
  have : ∀ i, Algebra.IsSeparable (ResidueField R) (L i) := fun i => (hL i).2
  choose A hcomm halg hfin hetale hequiv using fun i => exists_finiteEtale_of_isSeparable R (L i)
  let := hcomm
  let := halg
  let := hfin
  let := hetale
  refine ⟨∀ i, A i, inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  refine (Algebra.TensorProduct.piRight R (ResidueField R) (ResidueField R) A).trans ?_
  exact (AlgEquiv.piCongrRight fun i => (hequiv i).some).trans eΛ.symm

/-! ### Transport to the category of finite étale algebras -/

section Transport

variable (R : Type u) [CommRing R] [HenselianLocalRing R]

private lemma faithful_baseChange : (FiniteEtale.baseChange.{u, u, u} R (ResidueField R)).Faithful
    where
  map_injective {X Y} {f g} h := by
    have h2 := congrArg (fun m => m.hom.hom) h
    simp only [FiniteEtale.baseChange] at h2
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    refine algHom_ext_of_residue R (φ := f.hom.hom) (ψ := g.hom.hom) fun s => ?_
    refine
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Y.obj.carrier (maximalIdeal R)).injective
        ?_
    have h4 := AlgHom.congr_fun h2 ((1 : ResidueField R) ⊗ₜ[R] s)
    simp only [] at h4
    rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk,
      Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
    exact h4

private lemma full_baseChange : (FiniteEtale.baseChange.{u, u, u} R (ResidueField R)).Full
    where
  map_surjective {X Y} f := by
    obtain ⟨φ, hφ⟩ := exists_algHom_of_residue R X.obj.carrier Y.obj.carrier f.hom.hom
    refine ⟨ObjectProperty.homMk (CommAlgCat.ofHom φ), ?_⟩
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    refine
      algHom_ext_one_tmul
        (Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) φ) f.hom.hom
        fun b => ?_
    rw [Algebra.TensorProduct.map_tmul]
    simpa using hφ b

private lemma essSurj_baseChange : (FiniteEtale.baseChange.{u, u, u} R (ResidueField R)).EssSurj
    where
  mem_essImage Λ := by
    obtain ⟨S, _, _, _, _, ⟨e⟩⟩ := exists_finiteEtale_residue R Λ.obj.carrier
    exact ⟨FiniteEtale.of R S, ⟨FiniteEtale.isoMk e⟩⟩

end Transport

open CategoryTheory IsLocalRing in
/-- **Stacks 04GK.** Let `(R, 𝔪, κ)` be a henselian local ring. Base change along the residue map
`R → κ`, which on objects is `S ↦ κ ⊗[R] S ≅ S/𝔪S`, is an equivalence from the category of finite
étale `R`-algebras to the category of finite étale `κ`-algebras. -/
@[ega "IV 18.5.15" "special case", sga "7 IX 2.2.4" "more general", sga "7 XIII 1.2.1"]
public theorem solution (R : Type u) [CommRing R] [HenselianLocalRing R] :
    (CommAlgCat.FiniteEtale.baseChange.{u, u, u} R (ResidueField R)).IsEquivalence := by
  have := faithful_baseChange R
  have := full_baseChange R
  have := essSurj_baseChange R
  exact {}

end Stacks.Henselian.FiniteEtaleEquivalence

end

/-!
# Finite étale algebras over a henselian local ring

Let `(R, 𝔪, κ)` be a henselian local ring. Reduction modulo the maximal ideal, `S ↦ S/𝔪S`, turns
a finite étale `R`-algebra into a finite étale `κ`-algebra, that is, by
`Algebra.Etale.iff_exists_algEquiv_prod`, into a finite product of finite separable extensions of
`κ`. Henselianity makes this construction an *equivalence* of categories: a finite étale
`R`-algebra is determined, together with all of its morphisms, by its fibre over the closed point,
and every finite étale `κ`-algebra lifts. Concretely, a finite étale `R`-algebra is a finite
product of local ones (Lemma 04GJ), each of which has a finite separable residue field extension
of `κ` (Lemma 00U4); the local factors match the factors of the fibre, `Hom`s in both categories
are counted by the same set of factors of `S₁ ⊗[R] S₂`, and a finite separable extension of `κ` is
lifted by an étale `R`-algebra realising it as a residue field extension (Lemma 00UD).

## Main results

* `CommAlgCat.FiniteEtale.isEquivalence_baseChange_residueField`: for a henselian local ring `R`,
  base change along the residue map `R → κ` is an equivalence from the category of finite étale
  `R`-algebras to the category of finite étale `κ`-algebras.

## Implementation notes

The Stacks Project writes the functor as `S ↦ S/𝔪S`; stated here is Mathlib's canonical base change
functor `CommAlgCat.FiniteEtale.baseChange R κ`, `S ↦ κ ⊗[R] S`. The two are the same functor: the
canonical `κ`-algebra isomorphism `S/𝔪S ≅ κ ⊗[R] S` is
`Algebra.TensorProduct.quotIdealMapEquivQuotTensor`, and `𝔪S` is `Ideal.map (algebraMap R S) 𝔪`.
Base change is the form that composes — it is the functor Mathlib's fibre functors are built from
(`CommAlgCat.FiniteEtale.fiberIsoBaseChangeFiber`) — and it is defined without choosing a model
for the quotient.

"Is equivalent to ... via the functor" is `CategoryTheory.Functor.IsEquivalence` applied to that
functor, i.e. it is full, faithful and essentially surjective. The weaker
`Nonempty (FiniteEtale R ≌ FiniteEtale κ)` would assert only that the two categories are abstractly
equivalent and would not pin the functor, which is the content of the lemma. It is stated as an
instance, the form Mathlib gives the sibling equivalence `FiniteEtale.fiber Ω Ω` over a separably
closed field, so that the inverse functor and the unit and counit isomorphisms are available
through `Functor.asEquivalence` without a `haveI`.

The object universe is pinned to that of `R`, as in Mathlib's sibling statements for a separably
closed field (`CommAlgCat.FiniteEtale.equivOfIsSepClosed` and the `IsEquivalence` instance for
`CommAlgCat.FiniteEtale.fiber.{u} Ω Ω`). This is forced rather than a convenience: base change out
of `FiniteEtale.{v} R` lands in `FiniteEtale.{max u v} κ`, and for `v < u` the functor is not
essentially surjective, since `κ` is an object of the target while a ring too large to have a model
in `Type v` — such as `R` itself — has no preimage.

The statement is not generalized from a henselian local ring to a henselian pair `(R, I)`, for
which the same conclusion holds with `R/I` in place of `κ`: that is a separate tag with a genuinely
different proof (Elkik--Gabber), whereas the route here is the local decomposition of Lemma 04GJ.

Faithfulness. (1) The only hypothesis, `HenselianLocalRing R`, is used by the conclusion: over the
local, non-henselian ring `ℤ_(5)` the finite étale algebras `ℤ_(5)[x]/(x² - 2)` and
`ℤ_(5)[x]/(x² - 3)` are not isomorphic — their fraction fields `ℚ(√2)` and `ℚ(√3)` are not — yet
both reduce to `𝔽₂₅`, since `2` and `3` are non-squares mod `5`, so base change to `𝔽₅` is not an
equivalence there. (2) The scalars and base are the source's: the functor is base change along the
residue map `R → κ` of `R` itself, so the target category is that of finite étale `κ`-algebras, and
finiteness on both sides is over the respective base. (3) The source's functor is pinned, not
merely asserted to exist: the equivalence is claimed of `FiniteEtale.baseChange R (ResidueField R)`
and of no other functor. (4) The instantiation is not degenerate: for `R = ℤ_[5]`, which is
henselian, and `κ = 𝔽₅`, both categories contain more than the terminal object — for instance
`𝔽₂₅` on the one side and the unramified quadratic extension `ℤ_[5][x]/(x² - 2)` on the other,
which correspond under the functor.

## References

* [StacksProject 04GK](https://stacks.math.columbia.edu/tag/04GK)
* [StacksProject 04GJ](https://stacks.math.columbia.edu/tag/04GJ)
* [StacksProject 00U4](https://stacks.math.columbia.edu/tag/00U4)
* [StacksProject 00UD](https://stacks.math.columbia.edu/tag/00UD)
-/

@[expose] public section

open CategoryTheory IsLocalRing in
/-- **Stacks 04GK.** Let `(R, 𝔪, κ)` be a henselian local ring. Base change along the residue map
`R → κ`, which on objects is `S ↦ κ ⊗[R] S ≅ S/𝔪S`, is an equivalence from the category of finite
étale `R`-algebras to the category of finite étale `κ`-algebras. -/
@[stacks 04GK "The functor `S ↦ S/𝔪S` of the source is Mathlib's base change functor
`CommAlgCat.FiniteEtale.baseChange R (IsLocalRing.ResidueField R)`, `S ↦ κ ⊗[R] S`; the canonical
identification of the two is `Algebra.TensorProduct.quotIdealMapEquivQuotTensor`. `Equivalent via
the functor` is `CategoryTheory.Functor.IsEquivalence` of that functor, stated as an instance as
Mathlib states the sibling `FiniteEtale.fiber Ω Ω`. The object universe is pinned to `R`'s, as in
Mathlib's `CommAlgCat.FiniteEtale.equivOfIsSepClosed`. See the module docstring.",
  sga "1 IX 1.8"
  "more general",
  sga "7 XIII 1.2.1" "the equivalence",
  ega "IV 18.3.2" "local, I = maximal ideal",
  ega "IV 18.5.15" "henselian local ring",
  sga "1 IX 1.8" "more general",
  sga "3 VIIB 1.6.E" "(b), special case",
  sga "7 IX 2.2.4" "more general"]
public instance CommAlgCat.FiniteEtale.isEquivalence_baseChange_residueField (R : Type u)
    [CommRing R] [HenselianLocalRing R] :
    (CommAlgCat.FiniteEtale.baseChange.{u, u, u} R (ResidueField R)).IsEquivalence := by
  apply Stacks.Henselian.FiniteEtaleEquivalence.solution

end
