module

public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.Lifting
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria

@[expose] public section

/-!
# Finite étale algebras over a henselian pair

For a henselian pair `(A, I)`, reduction modulo `I` is an equivalence from finite étale
`A`-algebras to finite étale `A ⧸ I`-algebras. Fully faithfulness comes from the lifting
criterion for étale algebras, and essential surjectivity from passing to the integral closure of
`A` in a lift of a finite étale algebra over the quotient.

## Main results

* `isEquivalence_baseChange_quotient`: base change along `A → A ⧸ I` is an equivalence on finite
  étale algebras.

## Implementation notes

The categories of finite étale algebras and the base change functor between them are Mathlib's
`CommAlgCat.FiniteEtale` and `CommAlgCat.FiniteEtale.baseChange`.

## References

* [Stacks: Tag 09ZL](https://stacks.math.columbia.edu/tag/09ZL)
-/

open CategoryTheory TensorProduct

universe u

section

/-- For a henselian pair `(A, I)` and an integral `A`-algebra `B`, `I B` induces a bijection on
idempotents. -/
private lemma inducesBijectionOnIdempotents_map_of_henselianPair {A : Type u} [CommRing A]
    {I : Ideal A} (hI : HenselianPair A I) (B : Type u) [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] : InducesBijectionOnIdempotents (I.map (algebraMap A B)) := by
  have h := ((henselianPair_tfae.{u, u} A I).out 1 4).mp hI
  exact h B

private lemma henselianPair_map_of_isIntegral {A : Type u} {B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (I : Ideal A)
    (hI : HenselianPair A I) :
    HenselianPair B (I.map (algebraMap A B)) := by
  apply ((henselianPair_tfae.{u, u} B (I.map (algebraMap A B))).out 4 1).mp
  intro C _ _ hC
  let _ : Algebra A C := (algebraMap B C).comp (algebraMap A B) |>.toAlgebra
  let _ : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra.IsIntegral A C := Algebra.IsIntegral.trans B
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A B C]
  exact inducesBijectionOnIdempotents_map_of_henselianPair hI C

private lemma idem_eq_zero_of_mem_jacobson {R : Type*} [CommRing R] {e : R}
    (he : IsIdempotentElem e) (hm : e ∈ (⊥ : Ideal R).jacobson) : e = 0 := by
  have hu : IsUnit (1 - e) := by
    have := Ideal.mem_jacobson_bot.mp hm (-1)
    simpa [sub_eq_add_neg, add_comm] using this
  have hz : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  simpa using (hu.mul_left_eq_zero).mp hz

private lemma map_le_jacobson_of_isIntegral {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (I : Ideal A)
    (hI : I ≤ (⊥ : Ideal A).jacobson) :
    I.map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson := by
  rw [Ideal.jacobson]
  refine le_sInf ?_
  rintro J ⟨-, hJ⟩
  rw [Ideal.map_le_iff_le_comap]
  apply hI.trans
  rw [Ideal.jacobson]
  exact sInf_le ⟨bot_le, Ideal.isMaximal_comap_of_isIntegral_of_isMaximal J⟩

private lemma algHom_ext_of_quotient
    {A : Type u} [CommRing A] {I : Ideal A} (hI : I ≤ (⊥ : Ideal A).jacobson)
    {S T : Type u} [CommRing S] [CommRing T] [Algebra A S] [Algebra A T]
    [Algebra.EssFiniteType A S] [Algebra.FormallyUnramified A S] [Algebra.IsIntegral A T]
    {f g : S →ₐ[A] T}
    (h : ∀ s, Ideal.Quotient.mk (I.map (algebraMap A T)) (f s) =
      Ideal.Quotient.mk (I.map (algebraMap A T)) (g s)) : f = g := by
  classical
  obtain ⟨e, he, heq⟩ :
      ∃ e, IsIdempotentElem e ∧ KaehlerDifferential.ideal A S = Ideal.span {e} :=
    (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg A S)).mp <|
      (Ideal.cotangent_subsingleton_iff _).mp <| inferInstanceAs <| Subsingleton (Ω[S⁄A])
  let H : S ⊗[A] S →ₐ[A] T := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  have hkey :
      (Ideal.Quotient.mkₐ A (I.map (algebraMap A T))).comp H =
        ((Ideal.Quotient.mkₐ A (I.map (algebraMap A T))).comp f).comp
          (Algebra.TensorProduct.lmul' A) := by
    refine Algebra.TensorProduct.ext' fun a b => ?_
    simp [H, Algebra.TensorProduct.lift_tmul, h b]
  have he_mem : e ∈ KaehlerDifferential.ideal A S := by
    rw [heq]
    exact Ideal.mem_span_singleton_self _
  have hmapI : I.map (algebraMap A T) ≤ (⊥ : Ideal T).jacobson :=
    map_le_jacobson_of_isIntegral I hI
  have hHe : H e = 0 := by
    refine idem_eq_zero_of_mem_jacobson (he.map H) (hmapI ?_)
    have hc := AlgHom.congr_fun hkey e
    simp only [AlgHom.comp_apply] at hc
    rw [show (Algebra.TensorProduct.lmul' A (S := S)) e = 0 from he_mem] at hc
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hc
  ext s
  have hm : s ⊗ₜ[A] (1 : S) - (1 : S) ⊗ₜ[A] s ∈ KaehlerDifferential.ideal A S := by
    simp [KaehlerDifferential.ideal, RingHom.mem_ker]
  rw [heq, Ideal.mem_span_singleton] at hm
  obtain ⟨c, hc⟩ := hm
  have hz : H (s ⊗ₜ[A] (1 : S) - (1 : S) ⊗ₜ[A] s) = 0 := by
    rw [hc, map_mul, hHe, zero_mul]
  rw [map_sub] at hz
  exact sub_eq_zero.mp (by simpa [H, Algebra.TensorProduct.lift_tmul] using hz)

private lemma algHom_ext_one_tmul {R : Type*} [CommRing R] {B : Type*} [CommRing B]
    [Algebra R B] {S : Type*} [CommRing S] [Algebra R S]
    {T : Type*} [CommRing T] [Algebra B T]
    (f g : (B ⊗[R] S) →ₐ[B] T)
    (h : ∀ s, f ((1 : B) ⊗ₜ[R] s) = g ((1 : B) ⊗ₜ[R] s)) : f = g := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul b s =>
      rw [show b ⊗ₜ[R] s = b • ((1 : B) ⊗ₜ[R] s) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, map_smul, h]

private lemma exists_algHom_of_quotient
    {A : Type u} [CommRing A] (I : Ideal A) (hI : HenselianPair A I)
    (S T : Type u) [CommRing S] [CommRing T] [Algebra A S] [Algebra A T]
    [Algebra.Etale A S] [Module.Finite A T]
    (g : ((A ⧸ I) ⊗[A] S) →ₐ[A ⧸ I] ((A ⧸ I) ⊗[A] T)) :
    ∃ f : S →ₐ[A] T, ∀ s, (1 : A ⧸ I) ⊗ₜ[A] f s = g ((1 : A ⧸ I) ⊗ₜ[A] s) := by
  classical
  let U := T ⊗[A] S
  let J := I.map (algebraMap A T)
  let E := Algebra.TensorProduct.quotIdealMapEquivQuotTensor T I
  let hbar : U →ₐ[T] T ⧸ J :=
    Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ T J)
      (((E.symm.toAlgHom.comp g).restrictScalars A).comp
        Algebra.TensorProduct.includeRight) (fun _ _ => Commute.all _ _)
  have hT : HenselianPair T J := henselianPair_map_of_isIntegral I hI
  have hU : Algebra.Etale T U := by dsimp [U]; infer_instance
  have hlift : ∀ (V : Type u) [CommRing V] [Algebra T V] [Algebra.Etale T V],
      ∀ q : V →ₐ[T] T ⧸ J, ∃ p : V →ₐ[T] T, (Ideal.Quotient.mkₐ T J).comp p = q :=
    ((henselianPair_tfae.{u, u} T J).out 1 2).mp hT
  obtain ⟨σ, hσ⟩ := @hlift U inferInstance inferInstance hU hbar
  let f : S →ₐ[A] T := (σ.restrictScalars A).comp Algebra.TensorProduct.includeRight
  refine ⟨f, fun s => ?_⟩
  have hs := AlgHom.congr_fun hσ ((1 : T) ⊗ₜ[A] s)
  change Ideal.Quotient.mk J (f s) = hbar ((1 : T) ⊗ₜ[A] s) at hs
  have hs' := congrArg E hs
  change E (Ideal.Quotient.mk J (f s)) = E (hbar ((1 : T) ⊗ₜ[A] s)) at hs'
  have hh : hbar ((1 : T) ⊗ₜ[A] s) = E.symm (g ((1 : A ⧸ I) ⊗ₜ[A] s)) := by
    show (Ideal.Quotient.mkₐ T J) 1 *
      (((E.symm.toAlgHom.comp g).restrictScalars A).comp
        Algebra.TensorProduct.includeRight) s = _
    rw [map_one, one_mul]
    rfl
  rw [hh, E.apply_symm_apply] at hs'
  have hmk : E (Ideal.Quotient.mk J (f s)) = (1 : A ⧸ I) ⊗ₜ[A] f s :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk T I (f s)
  rwa [hmk] at hs'

private lemma faithful_baseChange
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I ≤ (⊥ : Ideal A).jacobson) :
    (CommAlgCat.FiniteEtale.baseChange.{u, u, u} A (A ⧸ I)).Faithful where
  map_injective {X Y} {f g} hfg := by
    have hfg' := congrArg (fun q => q.hom.hom) hfg
    simp only [CommAlgCat.FiniteEtale.baseChange] at hfg'
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    apply algHom_ext_of_quotient hI
    intro s
    apply (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Y.obj.carrier I).injective
    rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk,
      Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
    exact AlgHom.congr_fun hfg' ((1 : A ⧸ I) ⊗ₜ[A] s)

private lemma full_baseChange
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I) :
    (CommAlgCat.FiniteEtale.baseChange.{u, u, u} A (A ⧸ I)).Full where
  map_surjective {X Y} g := by
    obtain ⟨f, hf⟩ := exists_algHom_of_quotient I hI X.obj.carrier Y.obj.carrier g.hom.hom
    refine ⟨ObjectProperty.homMk (CommAlgCat.ofHom f), ?_⟩
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    apply algHom_ext_one_tmul
    intro s
    show (Algebra.TensorProduct.map (AlgHom.id (A ⧸ I) (A ⧸ I)) f)
      ((1 : A ⧸ I) ⊗ₜ[A] s) = g.hom.hom ((1 : A ⧸ I) ⊗ₜ[A] s)
    rw [Algebra.TensorProduct.map_tmul]
    exact hf s

private lemma essSurj_baseChange
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I) :
    (CommAlgCat.FiniteEtale.baseChange.{u, u, u} A (A ⧸ I)).EssSurj := by
  classical
  refine ⟨fun X => ?_⟩
  let Q := A ⧸ I
  let Y := X.obj.carrier
  let : Algebra A Y := (algebraMap Q Y).comp (Ideal.Quotient.mk I) |>.toAlgebra
  let : IsScalarTower A Q Y := .of_algebraMap_eq fun _ => rfl
  obtain ⟨S, _, _, hS, ψ, hψ, hker⟩ :=
    etale_lift_along_surjection A Q Y Ideal.Quotient.mk_surjective
  let J := I.map (algebraMap A S)
  have hker' : RingHom.ker (ψ : S →+* Y) = J := by
    simpa [Q, J] using hker
  let eY : (S ⧸ J) ≃ₐ[A] Y := hker' ▸ Ideal.quotientKerAlgEquivOfSurjective hψ
  let e : (S ⧸ J) ≃+* Y × PUnit.{1} :=
    eY.toRingEquiv.trans
      { toFun := fun y => (y, PUnit.unit)
        invFun := Prod.fst
        left_inv := fun _ => rfl
        right_inv := fun p => by cases p with | mk a b => cases b; rfl
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl }
  have hfinite : ((RingHom.fst Y PUnit.{1}).comp
      (e.toRingHom.comp
        (Ideal.quotientMap J (algebraMap A S) Ideal.le_comap_map))).Finite := by
    have hm : (RingHom.fst Y PUnit.{1}).comp
        (e.toRingHom.comp
          (Ideal.quotientMap J (algebraMap A S) Ideal.le_comap_map)) = algebraMap Q Y := by
      ext a
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_ringHom_trans,
        AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp, RingHom.coe_fst, RingHom.coe_coe,
        RingEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply, Ideal.quotientMap_mk,
        Ideal.Quotient.mk_algebraMap, AlgEquiv.commutes, J, e, eY, Q]
      exact IsScalarTower.algebraMap_apply A Q Y a
    rw [hm]
    exact RingHom.finite_algebraMap.mpr inferInstance
  obtain ⟨D, _, e', f₂, he'compat, g, hg, haway⟩ :=
    exists_integralClosure_quotient_prod_and_awayMap_bijective I e hfinite
  let D₀ := integralClosure A S
  let K := I.map (algebraMap A D₀)
  let v : D₀ ⧸ K := e'.symm (1, 0)
  have hv : IsIdempotentElem v := by
    apply e'.injective
    simp [v]
  obtain ⟨⟨d, hd⟩, hdeq⟩ :=
    (inducesBijectionOnIdempotents_map_of_henselianPair hI D₀).2 (⟨v, hv⟩)
  have hmkd : Ideal.Quotient.mk K d = v := congrArg Subtype.val hdeq
  let D₁ := D₀ ⧸ Ideal.span {1 - d}
  let p : D₀ →ₐ[A] D₁ := Ideal.Quotient.mkₐ A (Ideal.span {1 - d})
  have hpK : ∀ x ∈ K, p x ∈ I.map (algebraMap A D₁) := fun x hx => by
    simpa [K, Ideal.map_map, ← IsScalarTower.algebraMap_eq A D₀ D₁] using
      Ideal.mem_map_of_mem (p : D₀ →+* D₁) hx
  have hpd : p d = 1 := by
    have hz : p (1 - d) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    have hp : (1 : D₁) - p d = 0 := by simpa only [map_sub, map_one] using hz
    exact (sub_eq_zero.mp hp).symm
  have hpg : IsUnit (p g) := by
    have hgd : Ideal.Quotient.mk K g = Ideal.Quotient.mk K d := by
      apply e'.injective
      simpa [hmkd, v] using hg
    have hmem : g - d ∈ K := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_sub] using sub_eq_zero.mpr hgd
    have hJ : I.map (algebraMap A D₁) ≤ (⊥ : Ideal D₁).jacobson :=
      map_le_jacobson_of_isIntegral I hI.1
    have hu := Ideal.mem_jacobson_bot.mp (hJ (hpK _ hmem)) 1
    simpa [map_sub, hpd] using hu
  have hD₁Etale : Algebra.Etale A D₁ := by
    let t : D₀ := d * g
    have : IsLocalization.Away d D₁ :=
      IsLocalization.Away.quotient_of_isIdempotentElem hd
    have : IsLocalization.Away t D₁ :=
      IsLocalization.Away.mul_of_isUnit d g hpg
    have hdiv : g ∣ t := ⟨d, by simp [t, mul_comm]⟩
    have hbij' : Function.Bijective (Localization.awayMapₐ D₀.val t) :=
      Localization.awayMap_bijective_of_dvd (D₀.val : D₀ →+* S) hdiv haway
    let E : Localization.Away t ≃ₐ[A] Localization.Away (D₀.val t) :=
      AlgEquiv.ofBijective (Localization.awayMapₐ D₀.val t) hbij'
    have hSaway : Algebra.Etale A (Localization.Away (D₀.val t)) := by infer_instance
    have hDaway : Algebra.Etale A (Localization.Away t) :=
      Algebra.Etale.of_equiv E.symm
    let F : Localization.Away t ≃ₐ[A] D₁ :=
      (IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t) D₁).restrictScalars A
    exact Algebra.Etale.of_equiv F
  have hD₁Finite : Module.Finite A D₁ := by
    let : Algebra.Etale A D₁ := hD₁Etale
    exact Algebra.IsIntegral.finite
  have heY : (Q ⊗[A] D₁) ≃ₐ[Q] Y := by
    have hKJ : K ≤ J.comap (D₀.val : D₀ →+* S) := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simpa using Ideal.mem_map_of_mem (algebraMap A S) ha
    let τ : (D₀ ⧸ K) →ₐ[A] (S ⧸ J) := Ideal.quotientMapₐ J D₀.val hKJ
    let rK : (D₀ ⧸ K) →ₐ[A] Y := eY.toAlgHom.comp τ
    have hrK (z : D₀ ⧸ K) : rK z = (e' z).1 := by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      calc
        rK (Ideal.Quotient.mk K x) = eY (Ideal.Quotient.mk J (D₀.val x)) := by
          show eY (τ (Ideal.Quotient.mk K x)) = _
          congr 1
        _ = (e' (Ideal.Quotient.mk K x)).1 := by
          have hc := congrArg Prod.fst (he'compat (Ideal.Quotient.mk K x))
          change eY ((Ideal.quotientMap J (D₀.val : D₀ →+* S) _) (Ideal.Quotient.mk K x)) =
            (e' (Ideal.Quotient.mk K x)).1 at hc
          rwa [Ideal.quotientMap_mk] at hc
    let q₀ : D₀ →ₐ[A] Y := rK.comp (Ideal.Quotient.mkₐ A K)
    have hqd : q₀ d = 1 := by
      show rK (Ideal.Quotient.mk K d) = 1
      rw [hmkd, hrK]
      simp [v]
    have hkill : ∀ x : D₀, x ∈ Ideal.span {1 - d} → q₀ x = 0 := by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hx
      simp [map_mul, hqd]
    let q : D₁ →ₐ[A] Y := Ideal.Quotient.liftₐ _ q₀ hkill
    have hqmk (x : D₀) : q (p x) = q₀ x := Ideal.Quotient.lift_mk _ _ _
    have hqsurj : Function.Surjective q := by
      intro y
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e'.symm (y, 0))
      refine ⟨p x, ?_⟩
      rw [hqmk]
      show rK (Ideal.Quotient.mk K x) = y
      rw [hx, hrK, e'.apply_symm_apply]
    have hkerq : RingHom.ker (q : D₁ →+* Y) = I.map (algebraMap A D₁) := by
      apply le_antisymm
      · intro x hx
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        have hfirst : (e' (Ideal.Quotient.mk K a)).1 = 0 := by
          have hh : q₀ a = 0 := by
            change q (p a) = 0 at hx
            rwa [hqmk] at hx
          change rK (Ideal.Quotient.mk K a) = 0 at hh
          rwa [hrK] at hh
        have hda : d * a ∈ K := by
          apply Ideal.Quotient.eq_zero_iff_mem.mp
          apply e'.injective
          have hdd : e' (Ideal.Quotient.mk K d) = (1, 0) := by rw [hmkd]; simp [v]
          simpa [map_mul, hdd, hfirst] using (show (1, 0) * e' (Ideal.Quotient.mk K a) =
            (0 : Y × D) by ext <;> simp [hfirst])
        have hpa : p a = p (d * a) := by simp [map_mul, hpd]
        show p a ∈ I.map (algebraMap A D₁)
        rw [hpa]
        exact hpK _ hda
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        show q (algebraMap A D₁ a) = 0
        rw [AlgHom.commutes]
        show (algebraMap Q Y) (Ideal.Quotient.mk I a) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
    let eA : (D₁ ⧸ I.map (algebraMap A D₁)) ≃ₐ[A] Y :=
      hkerq ▸ Ideal.quotientKerAlgEquivOfSurjective hqsurj
    let eQ : (D₁ ⧸ I.map (algebraMap A D₁)) ≃ₐ[Q] Y :=
      eA.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor D₁ I).symm.trans eQ
  exact ⟨CommAlgCat.FiniteEtale.of A D₁, ⟨CommAlgCat.FiniteEtale.isoMk heY⟩⟩

/-- For a henselian pair `(A, I)`, reduction modulo `I` is an equivalence between finite étale
`A`-algebras and finite étale `A ⧸ I`-algebras. -/
@[stacks 09ZL, ega "IV 18.3.2", ega "IV 18.5.15", sga "3 X 4.0" "ÉtCov(S)≃ÉtCov(S₀)"]
theorem isEquivalence_baseChange_quotient
    (A : Type u) [CommRing A] (I : Ideal A) (h : HenselianPair A I) :
    (CommAlgCat.FiniteEtale.baseChange.{u, u, u} A (A ⧸ I)).IsEquivalence := by
  have := faithful_baseChange A I h.1
  have := full_baseChange A I h
  have := essSurj_baseChange A I h
  exact {}

end

end
