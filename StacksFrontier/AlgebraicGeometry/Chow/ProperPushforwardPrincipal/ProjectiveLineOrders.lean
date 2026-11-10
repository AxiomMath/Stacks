module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeFormula
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineFunctionField

/-!
# The order of vanishing at a closed point of the affine line

Let `A` be a unique factorization domain, let `p ∈ A` be a normalized irreducible element and let
`R` be a localization of `A` at the prime `(p)`. The order of vanishing `ord_R` of Stacks 02MD is
defined through the length `length_R (R / (r))` of a quotient by a principal ideal, while the
multiplicity of `p` in a factorization is counted by
`UniqueFactorizationMonoid.normalizedFactors`. This file identifies the two, and reads the result
on the affine line `Spec k[X]`, where it says that the order of vanishing of a rational function
at the closed point cut out by a monic irreducible `p` is `Stacks.Chow.ordAt p`.

On the affine line the ring `R` is the stalk of `Spec k[X]` at the point `(p)`, a localization
of `k[X]` at that prime through `AlgebraicGeometry.Spec.stalkIso`, and the fraction field is the
function field, identified with `RatFunc k` by `AlgebraicGeometry.affineLineFunctionFieldEquiv`.

## Main results

* `Stacks.Chow.ord_eq_count_normalizedFactors`: in a localization of a unique factorization
  domain at a principal prime `(p)`, the order of vanishing of `a` is the multiplicity of `p`
  among the normalized factors of `a`.
* `Stacks.Chow.ordInt_eq_count_sub_count`: the same statement on the fraction field: the order
  of a fraction `a / b` is the difference of the two multiplicities.
* `AlgebraicGeometry.ord_spec_polynomial_eq_ordAt` and
  `AlgebraicGeometry.ord_spec_polynomial_span_eq_ordAt`: the order of vanishing of a rational
  function at a closed point of the affine line over a field is `Stacks.Chow.ordAt`.
* `AlgebraicGeometry.residueDegree_projectiveLineAffineStructureMorphism_eq_natDegree`: the
  residue degree over `k` at the closed point of `Spec k[X]` cut out by an irreducible `p` is
  `p.natDegree`.
* `AlgebraicGeometry.ord_projectiveLine_xChart_eq_ordAt`: the order of vanishing on the
  projective line at the closed point of the first chart cut out by a monic irreducible `p` is
  `Stacks.Chow.ordAt p`.

## Implementation notes

The hypotheses of `Stacks.Chow.ordInt_eq_count_sub_count` are two consequences of being a
localization at `(p)`, that elements prime to `p` become units and that `p` generates the maximal
ideal, rather than an `IsLocalization` instance, since the stalk of `Spec k[X]` carries no
`k[X]`-algebra instance; the ring map `k[X] → 𝒪_{X,x}` is an explicit argument, built from
`AlgebraicGeometry.Spec.stalkIso`.

## References

* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
-/

@[expose] public section

noncomputable section

open CategoryTheory UniqueFactorizationMonoid

universe u

namespace Stacks.Chow

/-! ### The order of vanishing in a localization of a unique factorization domain -/

variable {A : Type u} [CommRing A] [IsDomain A] [NormalizationMonoid A]
  [UniqueFactorizationMonoid A] [DecidableEq A] {p : A}
  {R : Type u} [CommRing R] [IsLocalRing R]

/-- In a local ring, an element generating the maximal ideal has order of vanishing one. -/
theorem ord_eq_one_of_span_eq_maximalIdeal {x : R}
    (hx : Ideal.span {x} = IsLocalRing.maximalIdeal R) : Ring.ord R x = 1 := by
  rw [Ring.ord, Module.length_eq_one_iff]
  have hmax : (Ideal.span {x}).IsMaximal := hx ▸ IsLocalRing.maximalIdeal.isMaximal R
  rw [isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
    (S := R ⧸ Ideal.span {x}) Ideal.Quotient.mk_surjective]
  let := Ideal.Quotient.field (Ideal.span {x})
  exact instIsSimpleModule _

omit [UniqueFactorizationMonoid A] [DecidableEq A] in
/-- Two distinct normalized irreducible elements do not divide one another. -/
theorem not_dvd_of_normalize_eq_of_ne {q : A} (hp : Irreducible p) (hq : Irreducible q)
    (hnp : normalize p = p) (hnq : normalize q = q) (hne : q ≠ p) : ¬ p ∣ q := by
  intro hdvd
  refine hne ?_
  rw [← hnq, ← hnp]
  exact (normalize_eq_normalize hdvd (hp.dvd_symm hq hdvd)).symm

/-- A ring isomorphism of local rings carries a generator of the maximal ideal to a generator of
the maximal ideal. -/
theorem span_singleton_eq_maximalIdeal_of_ringEquiv {S : Type u} [CommRing S] [IsLocalRing S]
    (e : R ≃+* S) {w : S} (hw : Ideal.span {w} = IsLocalRing.maximalIdeal S) :
    Ideal.span {e.symm w} = IsLocalRing.maximalIdeal R := by
  have hcomap : Ideal.span {e.symm w} = Ideal.comap (e : R →+* S) (Ideal.span {w}) := by
    ext y
    simp only [Ideal.mem_comap, Ideal.mem_span_singleton]
    refine ⟨fun ⟨c, hc⟩ => ⟨e c, by rw [hc]; simp⟩, fun ⟨c, hc⟩ => ⟨e.symm c, ?_⟩⟩
    have := congrArg e.symm hc
    simpa using this
  refine IsLocalRing.eq_maximalIdeal ?_
  rw [hcomap, hw]
  exact Ideal.comap_isMaximal_of_surjective (e : R →+* S) e.surjective

variable [IsDomain R]

omit [UniqueFactorizationMonoid A] in
/-- The order of vanishing of a product of normalized irreducible elements is the number of
factors equal to `p`. -/
theorem ord_multiset_prod_eq_count (hp : Irreducible p) (hnp : normalize p = p) (f : A →+* R)
    (hunit : ∀ q : A, ¬ (p ∣ q) → IsUnit (f q))
    (hmax : Ideal.span {f p} = IsLocalRing.maximalIdeal R)
    (hinj : Function.Injective f) (s : Multiset A)
    (hs : ∀ q ∈ s, Irreducible q ∧ normalize q = q) :
    Ring.ord R (f s.prod) = (s.count p : ℕ∞) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons q t ih =>
      have hq := hs q (Multiset.mem_cons_self q t)
      have ht : ∀ r ∈ t, Irreducible r ∧ normalize r = r := fun r hr =>
        hs r (Multiset.mem_cons_of_mem hr)
      have h0 : f t.prod ≠ 0 := (map_ne_zero_iff f hinj).2 fun hz =>
        (ht _ (Multiset.prod_eq_zero_iff.mp hz)).1.ne_zero rfl
      rw [Multiset.prod_cons, map_mul, Ring.ord_mul R (mem_nonZeroDivisors_of_ne_zero h0), ih ht,
        Multiset.count_cons]
      by_cases hqp : q = p
      · subst hqp
        rw [ord_eq_one_of_span_eq_maximalIdeal hmax]
        simp [add_comm]
      · rw [Ring.ord_of_isUnit (hunit q (not_dvd_of_normalize_eq_of_ne hp hq.1 hnp hq.2 hqp))]
        simp [Ne.symm hqp]

/-- In a localization `R` of a unique
factorization domain `A` at a principal prime `(p)` — presented by a ring map `f : A →+* R`
making every element prime to `p` a unit and `f p` a generator of the maximal ideal — the order
of vanishing of a nonzero `a ∈ A` is the multiplicity of `p` among the normalized factors of
`a`. -/
theorem ord_eq_count_normalizedFactors (hp : Irreducible p) (hnp : normalize p = p) (f : A →+* R)
    (hunit : ∀ q : A, ¬ (p ∣ q) → IsUnit (f q))
    (hmax : Ideal.span {f p} = IsLocalRing.maximalIdeal R)
    (hinj : Function.Injective f) {a : A} (ha : a ≠ 0) :
    Ring.ord R (f a) = ((normalizedFactors a).count p : ℕ∞) := by
  rw [← ord_multiset_prod_eq_count hp hnp f hunit hmax hinj (normalizedFactors a)
    (fun q hq => ⟨irreducible_of_normalized_factor q hq, normalize_normalized_factor q hq⟩)]
  exact (Ring.ord_eq_of_associated ((prod_normalizedFactors ha).map (f : A →* R))).symm

/-- The integer order of vanishing of an element of the fraction field depends only on that
element, not on the proof that it is nonzero. -/
theorem ordInt_eq_of_eq {R' : Type u} [CommRing R'] [IsNoetherianRing R'] [Ring.KrullDimLE 1 R']
    [Nontrivial R'] {K' : Type u} [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    (x y : K') (hx : x ≠ 0) (hy : y ≠ 0) (h : x = y) : ordInt R' x hx = ordInt R' y hy := by
  subst h; rfl

variable {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]

/-- With `R` a one-dimensional Noetherian localization of a unique factorization domain `A` at a
principal prime `(p)`, the order of a fraction `a / b` is the multiplicity of `p` in `a` minus its
multiplicity in `b`. -/
theorem ordInt_eq_count_sub_count [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (hp : Irreducible p) (hnp : normalize p = p) (f : A →+* R)
    (hunit : ∀ q : A, ¬ (p ∣ q) → IsUnit (f q))
    (hmax : Ideal.span {f p} = IsLocalRing.maximalIdeal R)
    (hinj : Function.Injective f) {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) {g : K} (hg : g ≠ 0)
    (hgab : g * algebraMap R K (f b) = algebraMap R K (f a)) :
    ordInt R g hg = ((normalizedFactors a).count p : ℤ)
      - ((normalizedFactors b).count p : ℤ) := by
  have hiA : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hf : ∀ {c : A}, c ≠ 0 → f c ≠ 0 := fun hc => (map_ne_zero_iff f hinj).2 hc
  have hK : ∀ {c : A}, c ≠ 0 → algebraMap R K (f c) ≠ 0 := fun hc =>
    (map_ne_zero_iff _ hiA).2 (hf hc)
  have count_eq : ∀ {c : A} (hc : c ≠ 0),
      ordInt R (algebraMap R K (f c)) (hK hc) = ((normalizedFactors c).count p : ℤ) := by
    intro c hc
    rw [ordInt_algebraMap R (f c) (hf hc) (hK hc),
      show Module.length R (R ⧸ Ideal.span {f c}) = Ring.ord R (f c) from rfl,
      ord_eq_count_normalizedFactors hp hnp f hunit hmax hinj hc]
    simp
  have key : ordInt R (algebraMap R K (f a)) (hK ha)
      = ordInt R g hg + ordInt R (algebraMap R K (f b)) (hK hb) :=
    (ordInt_eq_of_eq _ _ (hK ha) (mul_ne_zero hg (hK hb)) hgab.symm).trans
      (ordInt_mul R g _ hg (hK hb))
  rw [count_eq ha, count_eq hb] at key
  omega

end Stacks.Chow

namespace AlgebraicGeometry

variable (k : Type u) [Field k] [DecidableEq k]

/-- For `p` a monic irreducible polynomial over a field `k` and `x` the point of `Spec k[X]` cut
out by `p`, the order of vanishing at `x` of a rational function on the affine line is
`Stacks.Chow.ordAt p` of the corresponding element of `RatFunc k`. -/
theorem ord_spec_polynomial_eq_ordAt {p : Polynomial k} (hp : Irreducible p)
    (hpm : p.Monic) (x : Spec (.of (Polynomial k))) (hxId : x.asIdeal = Ideal.span {p})
    (g : (Spec (.of (Polynomial k))).functionField) :
    (Spec (.of (Polynomial k))).ord g x =
      Stacks.Chow.ordAt p (affineLineFunctionFieldEquiv k g) := by
  by_cases hg : g = 0
  · subst hg; simp
  have hxp : x.asIdeal.IsPrime := x.2
  have hxT : x ∈ (⊤ : (Spec (.of (Polynomial k))).Opens) := trivial
  have hcoh : Order.coheight x = 1 := by
    rw [← AlgebraicGeometry.idealHeight_eq_coheight, hxId]
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hp.ne_zero) hp.not_isUnit
  have : Ring.KrullDimLE 1 ((Spec (.of (Polynomial k))).presheaf.stalk x) :=
    AlgebraicGeometry.krullDimLE_of_coheight_le hcoh.le
  set e : ((Spec (.of (Polynomial k))).presheaf.stalk x) ≃+* Localization.AtPrime x.asIdeal :=
    (Spec.stalkIso (.of (Polynomial k)) x).commRingCatIsoToRingEquiv with hedef
  have hsymm : ∀ w : Localization.AtPrime x.asIdeal,
      e.symm w = (Spec.stalkIso (.of (Polynomial k)) x).inv w := fun _ => rfl
  set f : Polynomial k →+* ((Spec (.of (Polynomial k))).presheaf.stalk x) :=
    e.symm.toRingHom.comp (algebraMap (Polynomial k) (Localization.AtPrime x.asIdeal)) with hfdef
  have hfapp : ∀ a : Polynomial k,
      f a = e.symm (algebraMap (Polynomial k) (Localization.AtPrime x.asIdeal) a) :=
    fun _ => rfl
  have hinj : Function.Injective f :=
    e.symm.injective.comp (IsLocalization.injective (Localization.AtPrime x.asIdeal)
      (Ideal.primeCompl_le_nonZeroDivisors x.asIdeal))
  have hunit : ∀ q : Polynomial k, ¬ p ∣ q → IsUnit (f q) := by
    intro q hq
    have hmem : q ∈ x.asIdeal.primeCompl := by
      simp only [Ideal.primeCompl, Submonoid.mem_mk, hxId]
      simpa [Ideal.mem_span_singleton] using hq
    rw [hfapp]
    exact (IsLocalization.map_units (Localization.AtPrime x.asIdeal) ⟨q, hmem⟩).map e.symm
  have hmaxLoc : Ideal.span {algebraMap (Polynomial k) (Localization.AtPrime x.asIdeal) p}
      = IsLocalRing.maximalIdeal (Localization.AtPrime x.asIdeal) := by
    have hmapeq : Ideal.map (algebraMap (Polynomial k) (Localization.AtPrime x.asIdeal))
          x.asIdeal
        = Ideal.map (algebraMap (Polynomial k) (Localization.AtPrime x.asIdeal))
            (Ideal.span {p}) := congrArg _ hxId
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal x.asIdeal
      (Localization.AtPrime x.asIdeal), hmapeq, Ideal.map_span]
    simp
  have hmax : Ideal.span {f p}
      = IsLocalRing.maximalIdeal ((Spec (.of (Polynomial k))).presheaf.stalk x) := by
    rw [hfapp]
    exact Stacks.Chow.span_singleton_eq_maximalIdeal_of_ringEquiv e hmaxLoc
  have halg : ∀ a : Polynomial k,
      algebraMap ((Spec (.of (Polynomial k))).presheaf.stalk x)
          ((Spec (.of (Polynomial k))).functionField) (f a)
        = algebraMap (Polynomial k) ((Spec (.of (Polynomial k))).functionField) a := by
    intro a
    have h1 : f a = (Spec (.of (Polynomial k))).presheaf.germ ⊤ x hxT
        ((Scheme.ΓSpecIso (.of (Polynomial k))).inv a) := by
      have hmor := ConcreteCategory.congr_hom
        (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of (Polynomial k)) x) a
      rw [hfapp, hsymm]
      exact hmor
    rw [h1]
    change ((Spec (.of (Polynomial k))).presheaf.stalkSpecializes _).hom _ = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
    rfl
  obtain ⟨a, b, hb, habg⟩ := IsFractionRing.div_surjective (A := Polynomial k) g
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbK : algebraMap (Polynomial k) ((Spec (.of (Polynomial k))).functionField) b ≠ 0 := by
    simpa using (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (R := Polynomial k) (K := (Spec (.of (Polynomial k))).functionField) hb)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at habg
    simp at habg
    exact hg habg.symm
  have hE : affineLineFunctionFieldEquiv k g
      = algebraMap (Polynomial k) (RatFunc k) a / algebraMap (Polynomial k) (RatFunc k) b := by
    rw [← habg, map_div₀, AlgEquiv.commutes, AlgEquiv.commutes]
  rw [hE, Stacks.Chow.ordAt_div p ha0 hb0, Stacks.Chow.ord_eq_ordInt x hcoh g hg]
  refine Stacks.Chow.ordInt_eq_count_sub_count hp hpm.normalize_eq_self f hunit hmax hinj
    ha0 hb0 hg ?_
  rw [halg, halg, ← habg, div_mul_cancel₀ _ hbK]

/-- For `p` a monic irreducible polynomial over a field `k`, the order of vanishing of a rational
function on the affine line at the point of `Spec k[X]` with prime ideal `(p)` is
`Stacks.Chow.ordAt p` of the corresponding element of `RatFunc k`. -/
theorem ord_spec_polynomial_span_eq_ordAt {p : Polynomial k} (hp : Irreducible p)
    (hpm : p.Monic) (g : (Spec (.of (Polynomial k))).functionField) :
    (Spec (.of (Polynomial k))).ord g
        ⟨Ideal.span {p}, (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime⟩ =
      Stacks.Chow.ordAt p (affineLineFunctionFieldEquiv k g) :=
  ord_spec_polynomial_eq_ordAt k hp hpm _ rfl g

omit [DecidableEq k] in
/-- For `p` an irreducible polynomial over a field `k` and `x` the point of `Spec k[X]` cut out
by `p`, the residue degree of the structure morphism `Spec k[X] ⟶ Spec k` at `x` is
`p.natDegree`. -/
theorem residueDegree_projectiveLineAffineStructureMorphism_eq_natDegree
    {p : Polynomial k} (hp : Irreducible p) (x : Spec (.of (Polynomial k)))
    (hxId : x.asIdeal = Ideal.span {p}) :
    (projectiveLineAffineStructureMorphism k).residueDegree x = p.natDegree := by
  have hmax : (Ideal.span {p} : Ideal (Polynomial k)).IsMaximal := by
    simpa [← Ideal.submodule_span_eq] using PrincipalIdealRing.isMaximal_of_irreducible hp
  let _ : Field (Polynomial k ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  set φ : CommRingCat.of (Polynomial k) ⟶ CommRingCat.of (Polynomial k ⧸ Ideal.span {p}) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {p})) with hφ
  have _ : IsClosedImmersion (Spec.map φ) :=
    IsClosedImmersion.spec_of_surjective φ Ideal.Quotient.mk_surjective
  set z : Spec (.of (Polynomial k ⧸ Ideal.span {p})) := default with hzdef
  have hzb : z.asIdeal = ⊥ := by
    rcases Ideal.eq_bot_or_top z.asIdeal with h | h
    · exact h
    · exact absurd h z.2.ne_top
  have hbase : (Spec.map φ).base z = x := by
    refine PrimeSpectrum.ext ?_
    change z.asIdeal.comap (Ideal.Quotient.mk (Ideal.span {p})) = x.asIdeal
    rw [hzb, hxId, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hq := Stacks.Chow.residueDegree_of_bijective_residueFieldMap_comp (Spec.map φ)
    (projectiveLineAffineStructureMorphism k) z
    (Stacks.Chow.bijective_residueFieldMap_of_isClosedImmersion (Spec.map φ) z)
  rw [hbase] at hq
  let _ : Algebra k Γ(Spec (.of (Polynomial k ⧸ Ideal.span {p})), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec.map φ ≫ projectiveLineAffineStructureMorphism k).appTop).hom.toAlgebra
  rw [← hq, Stacks.Chow.residueDegree_eq_finrank_globalSections k _ z]
  refine Eq.trans (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl k)
    (Scheme.ΓSpecIso (.of (Polynomial k ⧸ Ideal.span {p}))).commRingCatIsoToRingEquiv ?_)
    finrank_quotient_span_eq_natDegree
  have hmor : (Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec.map φ ≫ projectiveLineAffineStructureMorphism k).appTop ≫
        (Scheme.ΓSpecIso (.of (Polynomial k ⧸ Ideal.span {p}))).hom
      = CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k) ≫ φ := by
    rw [show Spec.map φ ≫ projectiveLineAffineStructureMorphism k
        = Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k) ≫ φ) from
      (Spec.map_comp _ _).symm, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  ext a
  exact (ConcreteCategory.congr_hom hmor a).symm

/-- The order of vanishing of a rational function on the projective line at the closed point of
the first chart cut out by a monic irreducible `p` is `Stacks.Chow.ordAt p`. -/
theorem ord_projectiveLine_xChart_eq_ordAt {p : Polynomial k} (hp : Irreducible p) (hpm : p.Monic)
    (y : Spec (.of (Polynomial k))) (hyId : y.asIdeal = Ideal.span {p})
    (g : (projectiveLine k).functionField) :
    (projectiveLine k).ord g ((projectiveLineXChart k).base y) =
      Stacks.Chow.ordAt p (projectiveLineFunctionFieldEquiv k g) := by
  rw [ord_projectiveLine_xChart k g y, ord_spec_polynomial_eq_ordAt k hp hpm y hyId]
  rfl

end AlgebraicGeometry

end

end
