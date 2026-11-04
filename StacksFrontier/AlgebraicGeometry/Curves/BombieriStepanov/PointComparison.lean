module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.TwistedModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantSheafCurve

/-!
# Frobenius-fixed points of a Dedekind model are points of the curve

Let `X` be a proper curve over a finite field `k` with discrete valuation rings at its places and
let `A` be a Dedekind domain of finite type over `k` with fraction field `R(X)`. A ring
homomorphism `ψ : A → Ω` over `k` into an algebraically closed field with `ψ ^ (q ^ m) = ψ` takes
values in the subfield `𝔽_{q^m}` of `Ω`; its kernel `P` gives a place `x_P` of `X` with
`κ(x_P) = A / P`, and `ψ` induces a `k`-embedding `κ(x_P) → 𝔽_{q^m}`, that is a point
`Spec 𝔽_{q^m} ⟶ X`. This is injective, so there are at most `#X(𝔽_{q^m})` such `ψ`.

## Main results

* `Stacks.BombieriStepanov.finite_fieldValuedPoints`: `X(K)` is finite for a finite field `K`.
* `Stacks.BombieriStepanov.ncard_frobFixed_le`: the bound above.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace Stacks.BombieriStepanov

open Stacks.EtaleCohomology in
/-- The points of a scheme of finite type over a finite field with values in a finite field are
finitely many. -/
theorem finite_fieldValuedPoints {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] (K : Type u) [Field K]
    [Algebra k K] [Finite K] : Finite (fieldValuedPoints f K) := by
  classical
  have hpos : 0 < Module.finrank k K := Module.finrank_pos
  set S := (closedPointsDegreeLE f (Module.finrank k K)).filter
    (fun x => residueDegree f x.1 ∣ Module.finrank k K)
  have hmem : ∀ (x : X) (σ : residueEmbeddings f K x),
      ∃ h : IsClosed ({x} : Set X), (⟨x, h⟩ : closedPoints X) ∈ S := by
    intro x σ
    obtain ⟨hc, hd⟩ := isClosed_and_dvd_of_residueEmbeddings f K x σ
    refine ⟨hc, Finset.mem_filter.2 ⟨?_, hd⟩⟩
    simp only [closedPointsDegreeLE, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact Nat.le_of_dvd hpos hd
  let e : (Σ x : X, residueEmbeddings f K x) ≃ Σ y : S, residueEmbeddings f K y.1.1 :=
    { toFun := fun c => ⟨⟨⟨c.1, (hmem c.1 c.2).1⟩, (hmem c.1 c.2).2⟩, c.2⟩
      invFun := fun c => ⟨c.1.1.1, c.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfin : ∀ y : S, Finite (residueEmbeddings f K y.1.1) := by
    intro y
    refine Nat.finite_of_card_ne_zero ?_
    have hd := (Finset.mem_filter.1 y.2).2
    rw [natCard_residueEmbeddings, if_pos hd]
    intro h0
    rw [h0, zero_dvd_iff] at hd
    omega
  exact Finite.of_equiv _ ((fieldValuedPointsEquiv f K).trans e).symm

section Residue

variable {M : Scheme.{u}} [IsIntegral M] {A : Type u} [CommRing A] [IsDedekindDomain A]
  [Algebra A M.functionField] [IsFractionRing A M.functionField]

/-- A homomorphism with kernel `P` factors through the residue field at the place of `P`. -/
theorem exists_residueField_ringHom {Ω : Type*} [Field Ω] (φ : A →+* Ω)
    [(RingHom.ker φ).IsMaximal] {x : M}
    (hx : ∀ f : M.functionField,
      (∃ s : M.presheaf.stalk x, algebraMap _ M.functionField s = f) ↔
        ∃ a t : A, t ∉ RingHom.ker φ ∧ f = algebraMap A M.functionField a *
          (algebraMap A _ t)⁻¹) :
    ∃ ψ : IsLocalRing.ResidueField (M.presheaf.stalk x) →+* Ω, ∀ a,
      ψ (IsLocalRing.residue _ (toStalk x (forall_exists_algebraMap_eq hx) a)) = φ a := by
  set θ : A →+* IsLocalRing.ResidueField (M.presheaf.stalk x) :=
    (IsLocalRing.residue (M.presheaf.stalk x)).comp (toStalk x (forall_exists_algebraMap_eq hx))
  have hker : RingHom.ker θ = RingHom.ker φ := ker_residue_comp_toStalk hx
  have hθs : Function.Surjective θ := surjective_residue_comp_toStalk hx
  let ψ₀ : A ⧸ RingHom.ker θ →+* Ω := Ideal.Quotient.lift _ φ (fun a ha => by rwa [hker] at ha)
  refine ⟨ψ₀.comp (RingHom.quotientKerEquivOfSurjective hθs).symm.toRingHom, fun a => ?_⟩
  have h1 : (RingHom.quotientKerEquivOfSurjective hθs).symm (θ a) = Ideal.Quotient.mk _ a := by
    rw [RingEquiv.symm_apply_eq, RingHom.quotientKerEquivOfSurjective_apply_mk]
  show ψ₀ ((RingHom.quotientKerEquivOfSurjective hθs).symm (θ a)) = φ a
  rw [h1]
  rfl

end Residue

/-- Points over a field determine the residue map: two residue embeddings at equal points that
are heterogeneously equal agree on the image of `A`. -/
theorem residueEmbeddings_apply_eq_of_heq {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (K : Type u) [Field K] [Algebra k K]
    {A : Type u} [CommRing A] [Algebra A X.functionField]
    {x x' : X} (h : x = x') (σ : Stacks.EtaleCohomology.residueEmbeddings f K x)
    (σ' : Stacks.EtaleCohomology.residueEmbeddings f K x') (hσ : HEq σ σ')
    (hA : ∀ a : A, ∃ s : X.presheaf.stalk x,
      algebraMap (X.presheaf.stalk x) X.functionField s = algebraMap A X.functionField a)
    (hA' : ∀ a : A, ∃ s : X.presheaf.stalk x',
      algebraMap (X.presheaf.stalk x') X.functionField s = algebraMap A X.functionField a)
    (a : A) :
    σ.1.hom (IsLocalRing.residue _ (toStalk x hA a)) =
      σ'.1.hom (IsLocalRing.residue _ (toStalk x' hA' a)) := by
  subst h
  rw [eq_of_heq hσ]

/-- A subfield of an algebraically closed field of characteristic `p` whose elements are exactly
those fixed by `z ↦ z ^ (p ^ N)` has `p ^ N` elements, being the root set of `z ^ (p ^ N) - z`. -/
private theorem natCard_eq_of_forall_mem_iff {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (pr : ℕ)
    [Fact pr.Prime] [CharP Ω pr] {K : Subfield Ω} {Q N : ℕ} (hQ : Q = pr ^ N) (hN : N ≠ 0)
    (hmemK : ∀ z, z ∈ K ↔ z ^ Q = z) : Nat.card K = Q := by
  have hset : (K : Set Ω) = {z : Ω | z ^ (pr ^ N) = z} := by
    ext z
    rw [SetLike.mem_coe, hmemK, hQ]
    rfl
  rw [hQ, ← ncard_setOf_pow_eq_self (Ω := Ω) pr hN, ← hset]
  exact Nat.card_coe_set_eq (K : Set Ω)

/-- A finite extension of a finite field `k` with `#k ^ m` elements has degree `m` over `k`. -/
private theorem finrank_eq_of_natCard_eq {k : Type u} [Field k] [Fintype k] {K : Type u} [Field K]
    [Algebra k K] [Finite K] {m Q : ℕ} (hQdef : Q = Fintype.card k ^ m) (hcardK : Nat.card K = Q) :
    Module.finrank k K = m := by
  let : Fintype K := Fintype.ofFinite _
  have h1 := Module.card_eq_pow_finrank (K := k) (V := K)
  rw [← Nat.card_eq_fintype_card, hcardK, hQdef] at h1
  exact (Nat.pow_right_injective (Fintype.one_lt_card (α := k))).eq_iff.mp h1.symm

/-- A homomorphism `ψ : A → Ω` all of whose values are fixed by `z ↦ z ^ Q`, only finitely many
elements of `Ω` being so, has nonzero kernel: otherwise `A`, and with it the function field of the
curve, would be finite, while a uniformizer at a place has valuation `1`. -/
private theorem ker_ne_bot_of_forall_pow_eq_self {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X]
    (hdvr : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))
    {A : Type u} [CommRing A] [IsDedekindDomain A] [Algebra A X.functionField]
    [IsFractionRing A X.functionField] {Ω : Type u} [Field Ω] {Q : ℕ}
    (hRfin : {z : Ω | z ^ Q = z}.Finite) (P₀ : CurvePlace X) (ψ : A →+* Ω)
    (hψ : ∀ a, ψ a ^ Q = ψ a) : RingHom.ker ψ ≠ ⊥ := by
  intro hker
  have : Finite A :=
    Finite.of_injective (β := hRfin.toFinset) (fun a => ⟨ψ a, hRfin.mem_toFinset.2 (hψ a)⟩)
      fun a b h => (RingHom.injective_iff_ker_eq_bot _).2 hker (congrArg Subtype.val h)
  have : Finite X.functionField := by
    refine Finite.of_surjective (fun ab : A × A => algebraMap A X.functionField ab.1 /
      algebraMap A X.functionField ab.2) fun f => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) f
    exact ⟨(a, b), rfl⟩
  let : Fintype X.functionField := Fintype.ofFinite _
  obtain ⟨π, hπ⟩ := exists_curveVal_eq_one hdvr P₀
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at hπ
  have h0 := val_algebraMap (k := X.functionField) (curveVal hdvr P₀) hπ0
  rw [Algebra.algebraMap_self, RingHom.id_apply, hπ] at h0
  exact absurd h0 (by decide)

open Stacks.EtaleCohomology in
/-- A homomorphism `ψ : A → Ω` with maximal kernel whose values are fixed by `z ↦ z ^ Q`, at a
place `x` of `X` whose local ring is the localization of `A` at that kernel, induces a
`k`-embedding of the residue field `κ(x)` into the fixed subfield `K` of `Ω`, recovering `ψ`. -/
private theorem exists_residueEmbeddings_apply_eq {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Spec (.of k)) {A : Type u} [CommRing A]
    [IsDedekindDomain A]
    [Algebra k A] [Algebra A X.functionField] [IsFractionRing A X.functionField]
    (hkA : ∀ c : k, algebraMap A X.functionField (algebraMap k A c) =
      (fieldToStalk p (genericPoint X)).hom c)
    {Ω : Type u} [Field Ω] {ι₀ : k →+* Ω} {Q : ℕ} (K : Subfield Ω) (hι₀K : ∀ c, ι₀ c ∈ K)
    (hmemK : ∀ z, z ∈ K ↔ z ^ Q = z) (ψ : PointsOver A ι₀) (hψ : ∀ a, ψ.1 a ^ Q = ψ.1 a)
    [(RingHom.ker ψ.1).IsMaximal] {x : X}
    (hx : ∀ f : X.functionField,
      (∃ s : X.presheaf.stalk x, algebraMap _ X.functionField s = f) ↔
        ∃ a t : A, t ∉ RingHom.ker ψ.1 ∧ f = algebraMap A X.functionField a *
          (algebraMap A _ t)⁻¹) :
    letI : Algebra k K := (ι₀.codRestrict K hι₀K).toAlgebra
    ∃ σ : residueEmbeddings p K x, ∀ a,
      (σ.1.hom (IsLocalRing.residue _ (toStalk x (forall_exists_algebraMap_eq hx) a)) : Ω) =
        ψ.1 a := by
  let : Algebra k K := (ι₀.codRestrict K hι₀K).toAlgebra
  obtain ⟨ψb, hψb⟩ := exists_residueField_ringHom ψ.1 hx
  have hval : ∀ z, ψb z ∈ K := by
    intro z
    obtain ⟨a, rfl⟩ := surjective_residue_comp_toStalk hx z
    rw [RingHom.comp_apply, hψb, hmemK]
    exact hψ a
  refine ⟨⟨CommRingCat.ofHom (ψb.codRestrict K hval), ?_⟩, hψb⟩
  ext c
  show ψb (IsLocalRing.residue _ ((fieldToStalk p x).hom c)) = ι₀ c
  rw [← toStalk_algebraMap p hkA x (forall_exists_algebraMap_eq hx), hψb]
  exact congrArg (fun F : k →+* Ω => F c) ψ.2

open Stacks.EtaleCohomology in
/-- **Frobenius-fixed homomorphisms are points of the curve.** For a proper curve `X` over `k`
with discrete valuation rings at its places and a Dedekind domain `A` of finite type over `k`
with fraction field `R(X)`, the homomorphisms `ψ : A → Ω` over `ι₀` whose values are fixed by
`z ↦ z ^ Q` inject into the `K`-valued points of `X`, `K` being the fixed subfield of `Ω`. -/
private theorem exists_injective_fieldValuedPoints {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsProper p] [IsCurve k p]
    (hdvr : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))
    {A : Type u} [CommRing A] [IsDedekindDomain A] [Algebra k A]
    [Algebra A X.functionField] [IsFractionRing A X.functionField]
    (hkA : ∀ c : k, algebraMap A X.functionField (algebraMap k A c) =
      (fieldToStalk p (genericPoint X)).hom c)
    {Ω : Type u} [Field Ω] (ι₀ : k →+* Ω) {Q : ℕ} (hQ1 : 1 < Q) (K : Subfield Ω)
    (hι₀K : ∀ c, ι₀ c ∈ K) (hmemK : ∀ z, z ∈ K ↔ z ^ Q = z) :
    letI : Algebra k K := (ι₀.codRestrict K hι₀K).toAlgebra
    ∃ Φ : {ψ : PointsOver A ι₀ | ∀ a, ψ.1 a ^ Q = ψ.1 a} → fieldValuedPoints p K,
      Function.Injective Φ := by
  classical
  let : Algebra k K := (ι₀.codRestrict K hι₀K).toAlgebra
  set T := {ψ : PointsOver A ι₀ | ∀ a, ψ.1 a ^ Q = ψ.1 a}
  obtain ⟨hRfin, -⟩ := setOf_pow_eq_self_finite_ncard_le (Ω := Ω) hQ1
  have hmax : ∀ ψ ∈ T, (RingHom.ker ψ.1).IsMaximal := fun ψ hψ =>
    isMaximal_ker_of_finite_range ψ.1 (hRfin.subset (Set.range_subset_iff.2 hψ))
  -- a place of `X`, hence `R(X)` is infinite
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨x₀, -, hx₀⟩ := (isClosed_univ (X := X)).exists_closed_singleton Set.univ_nonempty
  set P₀ : CurvePlace X := ⟨x₀, coheight_eq_one_of_isCurve k p hx₀⟩
  have hplace : ∀ ψ ∈ T, ∃ x : CurvePlace X, ∀ f : X.functionField,
      (∃ s : X.presheaf.stalk x.1, algebraMap _ X.functionField s = f) ↔
        ∃ a t : A, t ∉ RingHom.ker ψ.1 ∧ f = algebraMap A X.functionField a *
          (algebraMap A _ t)⁻¹ := by
    intro ψ hψ
    have := hmax ψ hψ
    exact exists_curvePlace_eq_localization p hdvr (fun c => ⟨_, hkA c⟩) _
      (ker_ne_bot_of_forall_pow_eq_self hdvr hRfin P₀ ψ.1 hψ)
  have : Nonempty (CurvePlace X) := ⟨P₀⟩
  choose! Xp hXp using hplace
  have hAx : ∀ ψ ∈ T, ∀ a : A, ∃ s : X.presheaf.stalk (Xp ψ).1,
      algebraMap (X.presheaf.stalk (Xp ψ).1) X.functionField s =
        algebraMap A X.functionField a := by
    intro ψ hψ
    have := hmax ψ hψ
    exact forall_exists_algebraMap_eq (hXp ψ hψ)
  -- the residue embedding of a Frobenius-fixed point
  have hemb : ∀ ψ : T, ∃ σ : residueEmbeddings p K (Xp ψ.1).1, ∀ a,
      (σ.1.hom (IsLocalRing.residue _ (toStalk (Xp ψ.1).1 (hAx ψ.1 ψ.2) a)) : Ω) =
        ψ.1.1 a := fun ψ => by
    have := hmax ψ.1 ψ.2
    exact exists_residueEmbeddings_apply_eq p hkA K hι₀K hmemK ψ.1 ψ.2 (hXp ψ.1 ψ.2)
  choose σψ hσψ using hemb
  refine ⟨fun ψ => (fieldValuedPointsEquiv p K).symm ⟨(Xp ψ.1).1, σψ ψ⟩, fun ψ ψ' h => ?_⟩
  obtain ⟨hx, hσ⟩ := Sigma.mk.inj_iff.1 ((fieldValuedPointsEquiv p K).symm.injective h)
  refine Subtype.ext (Subtype.ext (RingHom.ext fun a => ?_))
  rw [← hσψ ψ a, ← hσψ ψ' a]
  exact congrArg Subtype.val (residueEmbeddings_apply_eq_of_heq p K hx _ _ hσ _ _ a)

open Stacks.EtaleCohomology in
/-- **Frobenius-fixed points of a Dedekind model are points of the curve.** For a proper curve
`X` over `k` with discrete valuation rings at its places and a Dedekind domain `A` of finite type
over `k` with fraction field `R(X)`, the homomorphisms `ψ : A → Ω` over `k` into an
algebraically closed field with `ψ ^ (q ^ m) = ψ` number at most `#X(𝔽_{q^m})`. -/
theorem ncard_frobFixed_le {k : Type u} [Field k] [Fintype k] (pr : ℕ) [Fact pr.Prime]
    [CharP k pr] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsProper p]
    [IsCurve k p]
    (hdvr : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))
    {A : Type u} [CommRing A] [IsDedekindDomain A] [Algebra k A]
    [Algebra A X.functionField] [IsFractionRing A X.functionField]
    (hkA : ∀ c : k, algebraMap A X.functionField (algebraMap k A c) =
      (fieldToStalk p (genericPoint X)).hom c)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (ι₀ : k →+* Ω) {m : ℕ} (hm : m ≠ 0) (N : ℕ)
    (hN : ∀ (K : Type u) [Field K] [Algebra k K] [Finite K], Module.finrank k K = m →
      Nat.card (fieldValuedPoints p K) = N) :
    {ψ : PointsOver A ι₀ | ∀ a, ψ.1 a ^ (Fintype.card k ^ m) = ψ.1 a}.Finite ∧
      {ψ : PointsOver A ι₀ | ∀ a, ψ.1 a ^ (Fintype.card k ^ m) = ψ.1 a}.ncard ≤ N := by
  classical
  obtain ⟨n, -, hq⟩ := FiniteField.card k pr
  set Q := Fintype.card k ^ m with hQdef
  have hQ : Q = pr ^ ((n : ℕ) * m) := by rw [hQdef, hq, ← pow_mul]
  have : CharP Ω pr := by
    let : Algebra k Ω := ι₀.toAlgebra
    exact charP_of_injective_algebraMap (algebraMap k Ω).injective pr
  -- the field `𝔽_{q^m}` inside `Ω`
  set K'' : Subfield Ω := (iterateFrobenius Ω pr ((n : ℕ) * m)).eqLocusField (RingHom.id Ω)
  have hmemK : ∀ z, z ∈ K'' ↔ z ^ Q = z := by
    intro z
    rw [RingHom.mem_eqLocusField, iterateFrobenius_def, hQ]
    rfl
  have hι₀K : ∀ c, ι₀ c ∈ K'' := fun c => by
    rw [hmemK, ← map_pow, hQdef, FiniteField.pow_card_pow]
  let : Algebra k K'' := (ι₀.codRestrict K'' hι₀K).toAlgebra
  have hnm : (n : ℕ) * m ≠ 0 := Nat.mul_ne_zero n.ne_zero hm
  have hcardK : Nat.card K'' = Q := natCard_eq_of_forall_mem_iff pr hQ hnm hmemK
  have hQ1 : 1 < Q := by
    rw [hQ]
    exact Nat.one_lt_pow hnm (Fact.out : pr.Prime).one_lt
  have : Finite K'' := Nat.finite_of_card_ne_zero (by omega)
  have hfr : Module.finrank k K'' = m := finrank_eq_of_natCard_eq hQdef hcardK
  have := finite_fieldValuedPoints p K''
  set T := {ψ : PointsOver A ι₀ | ∀ a, ψ.1 a ^ Q = ψ.1 a}
  obtain ⟨Φ, hΦ⟩ := exists_injective_fieldValuedPoints p hdvr hkA ι₀ hQ1 K'' hι₀K hmemK
  have : Finite T := Finite.of_injective Φ hΦ
  refine ⟨Set.toFinite T, ?_⟩
  rw [← hN K'' hfr, ← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective Φ hΦ

end Stacks.BombieriStepanov

end
