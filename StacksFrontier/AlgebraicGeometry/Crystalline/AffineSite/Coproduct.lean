module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineCrystallineSite.Basic
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow

/-!
# The completed envelope `D(n)` is the coproduct of `n + 1` copies of `D`

Work in an affine crystalline situation `(A, I, γ, C)` and choose a surjective polynomial
presentation `g : P = A[x_i] → C` with kernel `J`.  The `p`-adically completed divided power
envelope of `J` is the ring `D`, with divided power ideal `J̄` and divided powers `γ̄`; the same
construction applied to the `(n + 1)`-fold tensor power presentation `P ⊗_A … ⊗_A P → C`, whose
kernel is `J(n)`, gives `D(n)` with its divided power ideal `J̄(n)` and divided powers `γ̄(n)`.

This file proves the two assertions of Tag 07L4: that `(D, J̄, γ̄)` and `(D(n), J̄(n), γ̄(n))` are
objects of the completed affine crystalline site `Cris^∧(C/A)`, and that the `n + 1`
coprojections `D → D(n)` coming from the `n + 1` tensor factors exhibit

  `D(n) = ∐_{j = 0, …, n} D`

in `Cris^∧(C/A)`.

The coproduct property is the universal property of the divided power envelope combined with
that of a polynomial algebra: a morphism `D → B` in `Cris^∧(C/A)` is the same thing as a map of
pairs `(P, J) → (B, ker(B → C))` over `A`, and `P ⊗_A … ⊗_A P` is the coproduct of `n + 1`
copies of `P` over `A`.

## Main definitions

* `Crystalline.completedEnvelopeDPRing` — the divided power ring `(D, J̄, γ̄)`.
* `Crystalline.CompletedEnvelopeThickening` — a realisation of `(D, J̄, γ̄)` as an object of
  `Cris^∧(C/A)`, together with the comparison with the polynomial presentation.
* `Crystalline.completedEnvelopeThickening` — the canonical such realisation.
* `Crystalline.tensorPowerEnvelopeThickening` — the object `D(n)` of `Cris^∧(C/A)`, obtained by
  applying the previous construction to the tensor power presentation.
* `Crystalline.completedEnvelopeCoprojections`, `Crystalline.completedEnvelopeCoprojection` —
  the `n + 1` canonical morphisms `D → D(n)`, pinned down on the image of `P`.

## Main results

* `Crystalline.completedEnvelope_isCoproduct` — the canonical coprojections exhibit `D(n)` as
  the coproduct of `n + 1` copies of `D` in `Cris^∧(C/A)`.
* `Crystalline.completedEnvelope_hom_ext` — a morphism out of a realisation of the completed
  envelope is determined by its restriction along the map from the presentation algebra `P`.

## Implementation notes

The `(n + 1)`-fold tensor power of `P = A[x_i]` over `A` is presented as the polynomial algebra
on `Fin (n + 1) × ι`, the model used by `Crystalline.tensorPowerPresentation`; the `j`-th
coprojection of presentations is then `Crystalline.mvPolynomialCoprojection`, which renames the
variable `x_i` to `x_i(j)`.

A completed thickening does not determine its underlying divided power ring up to syntactic
equality, so `CompletedEnvelopeThickening` records the identification of that ring with
`completedEnvelopeDPRing` together with the comparison maps transported along it; this is what
makes the statement about the canonical `D` rather than about some abstract thickening.  The
map from `P` is part of the data because a morphism out of `D` in `Cris^∧(C/A)` is determined
by its restriction to the image of `P`, which is how the coprojections and the universal
property are pinned down.

Morphisms out of `D` are constructed by composing the universal property of the envelope with
a lift along the `p`-adic completion: a divided power map out of the envelope induces one out of
the completion by passing to the inverse limit of the finite levels, and the target is complete.

## References

* [Stacks Project, Tag 07L4](https://stacks.math.columbia.edu/tag/07L4)
* [Stacks Project, Equation 60.17.0.1, Tag 07J8](https://stacks.math.columbia.edu/tag/07J8)
* [Stacks Project, Equation 60.17.0.4, Tag 07JF](https://stacks.math.columbia.edu/tag/07JF)
* [Stacks Project, Tag 07KH](https://stacks.math.columbia.edu/tag/07KH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w r a

namespace Crystalline

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}

private theorem ringHom_heq_apply_of_eq
    {R S : DividedPowerRing.{r}} {A : Type a} [CommRing A]
    (hRS : R = S)
    (f : A →+* R ⧸ R.ideal) (g : A →+* S ⧸ S.ideal)
    (h : HEq f g) (x : A) :
    HEq (f x) (g x) := by
  cases hRS
  cases h
  rfl

/-- The divided power ring `(D, J̄, γ̄)` attached to a polynomial presentation: the `p`-adic
completion of the divided power envelope of the kernel, its completed divided power ideal, and
the unique extension of the divided powers to that ideal. -/
public noncomputable def completedEnvelopeDPRing
    (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g)
    (hp : let E := (polynomialDividedPowerEnvelope s g).object
      IsNilpotent (Ideal.Quotient.mk E.ideal (s.p : E))) :
    DividedPowerRing.{max u w} :=
  let E := (polynomialDividedPowerEnvelope s g).object
  DividedPowerRing.of (pAdicCompletedDividedPowerEnvelope s g hg)
    (DividedPowers.completionIdeal E.ideal s.p hp)
    (DividedPowers.completedDividedPowers E.ideal E.dividedPowers s.p hp).1

/-- A realisation of the divided power ring `(D, J̄, γ̄)` of a polynomial presentation as an
object of the completed affine crystalline site `Cris^∧(C/A)`.  Besides the object it records
the identification of its underlying divided power ring with `completedEnvelopeDPRing`, and the
map from the presentation algebra `P`, which determines every morphism out of the object. -/
public structure CompletedEnvelopeThickening
    (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g) where
  /-- The image of `p` is nilpotent modulo the divided power ideal of the envelope, so that the
  divided powers extend to the completion. -/
  hp : let E := (polynomialDividedPowerEnvelope s g).object
    IsNilpotent (Ideal.Quotient.mk E.ideal (s.p : E))
  /-- The object of `Cris^∧(C/A)`. -/
  thickening : CompletedCrystallineThickening.{u, v, max u w} s
  /-- Its underlying divided power ring is `(D, J̄, γ̄)`. -/
  ring_eq : thickening.ring = completedEnvelopeDPRing s g hg hp
  /-- The map from the presentation algebra `P` to `D`. -/
  presentationMap : MvPolynomial ι s.A →+* thickening.ring
  /-- That map is the canonical one. -/
  presentationMap_eq : HEq presentationMap (toPAdicCompletedDividedPowerEnvelope s g hg)
  /-- The structure map from the base `A` is the canonical one. -/
  fromBase_eq : HEq thickening.fromBase.toRingHom
    (algebraMap s.A (pAdicCompletedDividedPowerEnvelope s g hg))
  /-- The identification of `C` with `D / J̄` is the one induced by the presentation. -/
  quotient_compat (q : MvPolynomial ι s.A) :
    HEq (thickening.toQuotient (g q))
      (Ideal.Quotient.mk (completedEnvelopeDPRing s g hg hp).ideal
        (toPAdicCompletedDividedPowerEnvelope s g hg q))

/-- **Stacks Project, Tag 07L4**, first assertion.  The divided power ring `(D, J̄, γ̄)` of a
surjective polynomial presentation of `C` over `A` is an object of `Cris^∧(C/A)`.  Applied to
the tensor power presentation this is `(D(n), J̄(n), γ̄(n))`, see
`Crystalline.tensorPowerEnvelopeThickening`. -/
@[stacks 07L4 "the completed envelopes are objects of the site", no_expose]
public noncomputable def completedEnvelopeThickening
    (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g) :
    CompletedEnvelopeThickening s g hg := by
  classical
  let T := completedPolynomialEnvelopeThickening s g hg
  let X := T.1
  let hp := Classical.choose T.2
  have hspec := Classical.choose_spec T.2
  obtain ⟨hr, hbase, hquot⟩ := hspec
  change X.ring = _ at hr
  change HEq X.fromBase.toRingHom _ at hbase
  change HEq (X.toQuotient.comp g.toRingHom) _ at hquot
  have hr' : X.ring = completedEnvelopeDPRing s g hg hp := hr
  have hHom :
      (MvPolynomial ι s.A →+* X.ring) =
        (MvPolynomial ι s.A →+* completedEnvelopeDPRing s g hg hp) :=
    congrArg (fun R : DividedPowerRing => MvPolynomial ι s.A →+* R) hr'
  let presentationMap : MvPolynomial ι s.A →+* X.ring :=
    Eq.mp hHom.symm (toPAdicCompletedDividedPowerEnvelope s g hg)
  refine ⟨hp, X, hr', presentationMap, ?_, hbase, ?_⟩
  · exact cast_heq hHom.symm (toPAdicCompletedDividedPowerEnvelope s g hg)
  · let qcan :=
      (Ideal.Quotient.mk (completedEnvelopeDPRing s g hg hp).ideal).comp
        (toPAdicCompletedDividedPowerEnvelope s g hg)
    change HEq (X.toQuotient.comp g.toRingHom) qcan at hquot
    intro q
    exact ringHom_heq_apply_of_eq hr' (X.toQuotient.comp g.toRingHom) qcan hquot q

/-- The object `D(n)` of `Cris^∧(C/A)`: the realisation of the completed divided power envelope
of the `(n + 1)`-fold tensor power presentation `P ⊗_A … ⊗_A P → C`. -/
public noncomputable abbrev tensorPowerEnvelopeThickening
    (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g) (n : ℕ) :
    CompletedEnvelopeThickening s (tensorPowerPresentation s g n)
      (tensorPowerPresentation_surjective s g hg n) :=
  completedEnvelopeThickening s (tensorPowerPresentation s g n)
    (tensorPowerPresentation_surjective s g hg n)

private noncomputable abbrev completionRing (E : DividedPowerRing.{r}) (p : ℕ)
    (hp : IsNilpotent (Ideal.Quotient.mk E.ideal (p : E))) :
    DividedPowerRing.{r} :=
  ⟨AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E,
    DividedPowers.completionIdeal E.ideal p hp,
    (DividedPowers.completedDividedPowers E.ideal E.dividedPowers p hp).1⟩

/-- The quotient map to a finite level `A / (p)^e` is a divided power morphism for the
induced divided powers. -/
private theorem isDPMorphism_quotientDividedPowers_mk {A : Type*} [CommRing A] {I : Ideal A}
    (γ : DividedPowers I) (p e : ℕ) (hc : DividedPowers.pAdicIdeal (A := A) p ^ e ≤ I)
    (hs : γ.IsSubDPIdeal (DividedPowers.pAdicIdeal (A := A) p ^ e)) :
    γ.IsDPMorphism (DividedPowers.quotientDividedPowers I γ p e hc hs)
      (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := A) p ^ e)) := by
  simpa [DividedPowers.quotientDividedPowers] using
    DividedPowers.Quotient.isDPMorphism γ (by simpa [inf_eq_left.mpr hc] using hs)

/-- The image of `x` in the `p`-adic completion has image `x mod (p)^e` at level `e`. -/
private theorem evalₐ_algebraMap_pAdic {R : Type*} [CommRing R] (p e : ℕ) (x : R) :
    AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := R) p) e
      (algebraMap R (AdicCompletion (DividedPowers.pAdicIdeal (A := R) p) R) x) =
    Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := R) p ^ e) x := by
  rw [AdicCompletion.algebraMap_apply]
  exact AdicCompletion.evalₐ_of (DividedPowers.pAdicIdeal (A := R) p) e x

private noncomputable def completionMorphism
    (E : DividedPowerRing.{r}) (E' : DividedPowerRing.{a})
    (p : ℕ) [Fact p.Prime]
    [Algebra (DividedPowers.IntegersAtPrime p) E]
    [Algebra (DividedPowers.IntegersAtPrime p) E']
    (hp : IsNilpotent (Ideal.Quotient.mk E.ideal (p : E)))
    (hp' : IsNilpotent (Ideal.Quotient.mk E'.ideal (p : E')))
    (q : DividedPowers.DPMorphism E.dividedPowers E'.dividedPowers) :
    { qhat : DividedPowers.DPMorphism (completionRing E p hp).dividedPowers
        (completionRing E' p hp').dividedPowers //
      ∃ N, ∀ e (_he : N ≤ e) (x : E),
        AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := E') p) e
          (qhat.toRingHom (algebraMap E
            (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) x)) =
          Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := E') p ^ e) (q.toRingHom x) } := by
  classical
  let X := completionRing E p hp
  let Y := completionRing E' p hp'
  let hXexists :=
    DividedPowers.eventually_isDividedPowerCompletionLimit.{r, a}
      E.ideal E.dividedPowers p hp
  let Ns := Classical.choose hXexists
  let hXtail := Classical.choose_spec hXexists
  let hs := Classical.choose hXtail
  let hXs := Classical.choose_spec hXtail
  let hYexists :=
    DividedPowers.eventually_isDividedPowerCompletionLimit.{a, r}
      E'.ideal E'.dividedPowers p hp'
  let Nt := Classical.choose hYexists
  let hYtail := Classical.choose_spec hYexists
  let ht := Classical.choose hYtail
  let hYt := Classical.choose_spec hYtail
  change (∀ e (he : Ns ≤ e), X.dividedPowers.IsDPMorphism
      (DividedPowers.quotientDividedPowers E.ideal E.dividedPowers p e
        (hs e he).1 (hs e he).2)
      (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := E) p) e).toRingHom) ∧ _ at hXs
  change (∀ e (he : Nt ≤ e), Y.dividedPowers.IsDPMorphism
      (DividedPowers.quotientDividedPowers E'.ideal E'.dividedPowers p e
        (ht e he).1 (ht e he).2)
      (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := E') p) e).toRingHom) ∧ _ at hYt
  let qs (e : ℕ) (he : Ns ≤ e) :=
    DividedPowers.quotientDividedPowers E.ideal E.dividedPowers p e
      (hs e he).1 (hs e he).2
  let qt (e : ℕ) (he : Nt ≤ e) :=
    DividedPowers.quotientDividedPowers E'.ideal E'.dividedPowers p e
      (ht e he).1 (ht e he).2
  let Qs (e : ℕ) := DividedPowers.pAdicIdeal (A := E) p ^ e
  let Qt (e : ℕ) := DividedPowers.pAdicIdeal (A := E') p ^ e
  have hqpow (k e : ℕ) (hke : e ≤ k) : (Qs k).map q.toRingHom ≤ Qt e := by
    change (Ideal.span {(p : E)} ^ k).map q.toRingHom ≤
      Ideal.span {(p : E')} ^ e
    have hpmap : q.toRingHom (p : E) = (p : E') := by simp
    have hmap : (Ideal.span {(p : E)}).map q.toRingHom =
        Ideal.span {(p : E')} := by
      rw [Ideal.map_span, Set.image_singleton, hpmap]
    rw [Ideal.map_pow, hmap]
    exact Ideal.pow_le_pow_right hke
  let qbar (k e : ℕ) (hke : e ≤ k) : E ⧸ Qs k →+* E' ⧸ Qt e :=
    Ideal.quotientMap (Qt e) q.toRingHom
      (Ideal.map_le_iff_le_comap.mp (hqpow k e hke))
  have hqT (e : ℕ) (he : Nt ≤ e) :
      E'.dividedPowers.IsDPMorphism (qt e he) (Ideal.Quotient.mk (Qt e)) :=
    isDPMorphism_quotientDividedPowers_mk _ _ _ _ _
  have hqS (e : ℕ) (he : Ns ≤ e) :
      E.dividedPowers.IsDPMorphism (qs e he) (Ideal.Quotient.mk (Qs e)) :=
    isDPMorphism_quotientDividedPowers_mk _ _ _ _ _
  have hqbar (k e : ℕ) (hk : Ns ≤ k) (he : Nt ≤ e) (hke : e ≤ k) :
      DividedPowers.IsDPMorphism (qs k hk) (qt e he) (qbar k e hke) := by
    apply DividedPowers.IsDPMorphism.of_comp
      E.dividedPowers (qs k hk) (qt e he)
      (f := Ideal.Quotient.mk (Qs k)) (g := qbar k e hke) (heq := rfl) (hqS k hk)
    have hcomp : (qbar k e hke).comp (Ideal.Quotient.mk (Qs k)) =
        (Ideal.Quotient.mk (Qt e)).comp q.toRingHom := by
      ext x
      simp [qbar, Ideal.quotientMap_mk]
    rw [hcomp]
    exact DividedPowers.IsDPMorphism.comp (qt e he)
      (hqT e he) q.isDPMorphism
  let sourceLevel (e : ℕ) (_he : Nt ≤ e) := max Ns e
  let level (e : ℕ) (he : Nt ≤ e) :
      DividedPowers.DPMorphism X.dividedPowers (qt e he) := by
    let k := sourceLevel e he
    have hk : Ns ≤ k := le_max_left Ns e
    have hke : e ≤ k := le_max_right Ns e
    exact DividedPowers.DPMorphism.comp
      (DividedPowers.DPMorphism.mk' (hqbar k e hk he hke))
      (DividedPowers.DPMorphism.mk' (hXs.1 k hk))
  have hqbarCompat (m e : ℕ) (hm : Nt ≤ m) (he : Nt ≤ e) (hme : m ≤ e) :
      (Ideal.Quotient.factorPow (DividedPowers.pAdicIdeal (A := E') p) hme).comp
          (qbar (sourceLevel e he) e (le_max_right Ns e)) =
        (qbar (sourceLevel m hm) m (le_max_right Ns m)).comp
          (Ideal.Quotient.factorPow (DividedPowers.pAdicIdeal (A := E) p)
            (max_le_max le_rfl hme)) := by
    ext x
    simp [qbar, Qs, Qt, sourceLevel, DividedPowers.pAdicIdeal,
      Ideal.Quotient.factorPow, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]
  have hlevelCompat : ∀ (m e : ℕ) (hm : Nt ≤ m) (he : Nt ≤ e) (hme : m ≤ e),
      (Ideal.Quotient.factorPow (DividedPowers.pAdicIdeal (A := E') p) hme).comp
        (level e he).toRingHom = (level m hm).toRingHom := by
    intro m e hm he hme
    apply RingHom.ext
    intro x
    let ke := sourceLevel e he
    let km := sourceLevel m hm
    have hkm : km ≤ ke := max_le_max le_rfl hme
    let xE : AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E := by
      change AdicCompletion (Ideal.span {(p : E)}) E
      exact x
    have hnat := congrArg (fun f => f (AdicCompletion.evalₐ
      (DividedPowers.pAdicIdeal (A := E) p) ke xE))
      (hqbarCompat m e hm he hme)
    rw [RingHom.comp_apply] at hnat ⊢
    change (Ideal.Quotient.factorPow (DividedPowers.pAdicIdeal (A := E') p) hme)
        (qbar ke e (le_max_right Ns e)
          (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := E) p) ke xE)) =
      qbar km m (le_max_right Ns m)
        (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := E) p) km xE)
    change (Ideal.Quotient.factorPow (DividedPowers.pAdicIdeal (A := E') p) hme)
        (qbar ke e (le_max_right Ns e)
          (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := E) p) ke xE)) =
      qbar km m (le_max_right Ns m)
        (Ideal.Quotient.factorPow (DividedPowers.pAdicIdeal (A := E) p) hkm
          (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := E) p) ke xE)) at hnat
    rw [AdicCompletion.factorPow_evalₐ (DividedPowers.pAdicIdeal (A := E) p) hkm xE] at hnat
    exact hnat
  have hlimit := hYt.2 X.ideal X.dividedPowers level hlevelCompat
  refine ⟨Classical.choose hlimit, Nt, ?_⟩
  intro e he x
  have hmap := (Classical.choose_spec hlimit).1 e he
  have hval := congrArg (fun f : X →+* E' ⧸ Qt e => f
    (algebraMap E (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) x)) hmap
  change AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := E') p) e
      ((Classical.choose hlimit).toRingHom
        (algebraMap E (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) x)) =
    level e he (algebraMap E (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) x)
    at hval
  let k := max Ns e
  have hk : Ns ≤ k := le_max_left Ns e
  have hke : e ≤ k := le_max_right Ns e
  calc
    AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := E') p) e
        ((Classical.choose hlimit).toRingHom
          (algebraMap E (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) x)) =
        qbar k e hke (Ideal.Quotient.mk (Qs k) x) := by
            rw [hval]
            change qbar k e hke
              (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := E) p) k
                (algebraMap E
                  (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) x)) = _
            rw [evalₐ_algebraMap_pAdic]
    _ = Ideal.Quotient.mk (Qt e) (q.toRingHom x) := by
      simp [qbar, Ideal.quotientMap_mk]

private theorem completionMorphism_of
    (E : DividedPowerRing.{r}) (E' : DividedPowerRing.{a})
    (p : ℕ) [Fact p.Prime]
    [Algebra (DividedPowers.IntegersAtPrime p) E]
    [Algebra (DividedPowers.IntegersAtPrime p) E']
    (hp : IsNilpotent (Ideal.Quotient.mk E.ideal (p : E)))
    (hp' : IsNilpotent (Ideal.Quotient.mk E'.ideal (p : E')))
    (q : DividedPowers.DPMorphism E.dividedPowers E'.dividedPowers) (x : E) :
    (completionMorphism E E' p hp hp' q).1
        (algebraMap E (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) x) =
      algebraMap E' (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E') (q x) := by
  classical
  let r := completionMorphism E E' p hp hp' q
  rcases r.2 with ⟨N, hN⟩
  apply AdicCompletion.ext_evalₐ
  intro e
  let k := max N e
  have hk : N ≤ k := le_max_left N e
  have hke : e ≤ k := le_max_right N e
  calc
    AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := E') p) e
        (r.1.toRingHom (algebraMap E
          (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) x)) =
      Ideal.Quotient.factorPow (DividedPowers.pAdicIdeal (A := E') p) hke
        (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := E') p) k
          (r.1.toRingHom (algebraMap E
            (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) x))) :=
              (AdicCompletion.factorPow_evalₐ (DividedPowers.pAdicIdeal (A := E') p) hke _).symm
    _ = Ideal.Quotient.factorPow (DividedPowers.pAdicIdeal (A := E') p) hke
        (Ideal.Quotient.mk _ (q.toRingHom x)) := by rw [hN k hk x]
    _ = AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := E') p) e
        (algebraMap E'
          (AdicCompletion (DividedPowers.pAdicIdeal (A := E') p) E')
          (q.toRingHom x)) := by
            rw [evalₐ_algebraMap_pAdic]
            simp [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]

private theorem pIdeal_map {R S : Type*} [CommRing R] [CommRing S]
    (p : ℕ) (f : R →+* S) :
    (DividedPowers.pAdicIdeal (A := R) p).map f = DividedPowers.pAdicIdeal (A := S) p := by
  simp [DividedPowers.pAdicIdeal, Ideal.map_span, Set.image_singleton]

private theorem completion_mem_iff (E : DividedPowerRing.{r}) (p : ℕ)
    (hp : IsNilpotent (Ideal.Quotient.mk E.ideal (p : E))) (x : E) :
    algebraMap E (completionRing E p hp) x ∈ (completionRing E p hp).ideal ↔
      x ∈ E.ideal := by
  show DividedPowers.completionToQuotient E.ideal p hp
    (algebraMap E (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) x) = 0 ↔ _
  simp [DividedPowers.completionToQuotient, AdicCompletion.algebraMap_apply,
    AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem]

private noncomputable def toCompletion (E : DividedPowerRing.{r}) (p : ℕ)
    (hp : IsNilpotent (Ideal.Quotient.mk E.ideal (p : E))) :
    DividedPowers.DPMorphism E.dividedPowers (completionRing E p hp).dividedPowers := by
  refine DividedPowers.DPMorphism.mk' (f := algebraMap E (completionRing E p hp)) ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    exact fun x hx => (completion_mem_iff E p hp x).2 hx
  · intro n x hx
    exact ((DividedPowers.completedDividedPowers E.ideal E.dividedPowers p hp).2 n x hx
      ⟨_, (completion_mem_iff E p hp x).2 hx⟩ rfl)

private noncomputable def fromCompletion (E : DividedPowerRing.{r}) (p : ℕ)
    (hp : IsNilpotent (Ideal.Quotient.mk E.ideal (p : E)))
    [IsAdicComplete (DividedPowers.pAdicIdeal (A := E) p) E] :
    DividedPowers.DPMorphism (completionRing E p hp).dividedPowers E.dividedPowers := by
  let e := AdicCompletion.ofAlgEquiv (DividedPowers.pAdicIdeal (A := E) p)
  refine DividedPowers.DPMorphism.mk' (f := e.symm.toRingHom) ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨y, rfl⟩ := e.surjective x
    change e.symm (e y) ∈ E.ideal
    simpa using (completion_mem_iff E p hp y).1 hx
  · intro n x hx
    obtain ⟨y, rfl⟩ := e.surjective x
    have hy := (completion_mem_iff E p hp y).1 hx
    change E.dividedPowers.dpow n (e.symm (e y)) =
      e.symm ((completionRing E p hp).dividedPowers.dpow n (e y))
    have hd : (completionRing E p hp).dividedPowers.dpow n (e y) =
        e (E.dividedPowers.dpow n y) :=
      (toCompletion E p hp).isDPMorphism.2 y hy
    rw [hd, e.symm_apply_apply, e.symm_apply_apply]

private theorem completion_ringHom_ext {R S : Type*} [CommRing R] [CommRing S]
    (p : ℕ) [IsHausdorff (DividedPowers.pAdicIdeal (A := S) p) S]
    (f g : AdicCompletion (DividedPowers.pAdicIdeal (A := R) p) R →+* S)
    (h : ∀ x, f (algebraMap R _ x) = g (algebraMap R _ x)) : f = g := by
  let I := DividedPowers.pAdicIdeal (A := R) p
  let D := AdicCompletion I R
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' (DividedPowers.pAdicIdeal (A := S) p)
  intro n x
  obtain ⟨y, hy⟩ := (Submodule.mkQ_surjective (I ^ n • (⊤ : Submodule R R)))
    (AdicCompletion.eval I R n x)
  have hx : x - algebraMap R D y ∈ DividedPowers.pAdicIdeal (A := D) p ^ n := by
    have hm : x - algebraMap R D y ∈ I ^ n • (⊤ : Submodule R D) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _)]
      show AdicCompletion.eval I R n (x - algebraMap R D y) = 0
      rw [map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of,
        Algebra.algebraMap_self, RingHom.id_apply, hy, sub_self]
    rw [Ideal.smul_top_eq_map] at hm
    change x - algebraMap R D y ∈ (I ^ n).map (algebraMap R D) at hm
    simpa only [I, Ideal.map_pow, pIdeal_map] using hm
  have hf := Ideal.mem_map_of_mem f hx
  have hg := Ideal.mem_map_of_mem g hx
  rw [Ideal.map_pow, pIdeal_map, map_sub] at hf hg
  exact (Ideal.Quotient.eq.mpr hf).trans
    ((congrArg (Ideal.Quotient.mk _) (h y)).trans (Ideal.Quotient.eq.mpr hg).symm)

private theorem dpMorphism_ext {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} {J : Ideal S} {δ : DividedPowers I} {ε : DividedPowers J}
    {f g : DividedPowers.DPMorphism δ ε} (h : f.toRingHom = g.toRingHom) : f = g :=
  DividedPowers.DPMorphism.ext (congrArg (fun q : R →+* S => (q : R → S)) h)

private theorem presentationMap_base
    (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g)
    (X : CompletedEnvelopeThickening s g hg) :
    X.presentationMap.comp (algebraMap s.A _) = X.thickening.fromBase.toRingHom := by
  rcases X with ⟨hp, ⟨R, b, hc, t, ht, hbij⟩, hr, m, hm, ha, hq⟩
  dsimp only at hr hm ha ⊢
  subst R
  show m.comp (algebraMap s.A _) = b.toRingHom
  rw [eq_of_heq hm, eq_of_heq ha]
  let env := polynomialDividedPowerEnvelope s g
  exact RingHom.ext fun x => congrArg
    (algebraMap env.object (pAdicCompletedDividedPowerEnvelope s g hg))
    (RingHom.congr_fun env.algebraMap_comp x)

private theorem presentationMap_quotient
    (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g)
    (X : CompletedEnvelopeThickening s g hg) :
    (Ideal.Quotient.mk X.thickening.ring.ideal).comp X.presentationMap =
      X.thickening.toQuotient.comp g.toRingHom := by
  rcases X with ⟨hp, ⟨R, b, hc, t, ht, hbij⟩, hr, m, hm, ha, hq⟩
  dsimp only at hr hm hq ⊢
  subst R
  show (Ideal.Quotient.mk (completedEnvelopeDPRing s g hg hp).ideal).comp m =
    t.comp g.toRingHom
  rw [eq_of_heq hm]
  exact RingHom.ext fun x => (eq_of_heq (hq x)).symm

private theorem hom_presentationMap_base
    (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g)
    (X : CompletedEnvelopeThickening s g hg)
    (B : CompletedCrystallineThickening.{u, v, max u w} s)
    (k : X.thickening ⟶ B) :
    (k.hom.toRingHom.comp X.presentationMap).comp (algebraMap s.A _) =
      B.fromBase.toRingHom := by
  rw [RingHom.comp_assoc, presentationMap_base]
  exact congrArg DividedPowers.DPMorphism.toRingHom k.fromBase_comp

private theorem hom_presentationMap_quotient
    (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g)
    (X : CompletedEnvelopeThickening s g hg)
    (B : CompletedCrystallineThickening.{u, v, max u w} s)
    (k : X.thickening ⟶ B) :
    (Ideal.Quotient.mk B.ring.ideal).comp (k.hom.toRingHom.comp X.presentationMap) =
      B.toQuotient.comp g.toRingHom :=
  RingHom.ext fun x => (DividedPowerRing.quotientRingHom_mk
    (A := X.thickening.ring) (B := B.ring) k.hom (X.presentationMap x)).symm.trans
    ((congrArg
      (DividedPowerRing.quotientRingHom (A := X.thickening.ring) (B := B.ring) k.hom)
      (RingHom.congr_fun (presentationMap_quotient s g hg X) x)).trans
      (RingHom.congr_fun k.toQuotient_comp (g x)))

/-- A morphism out of the completed envelope in `Cris^∧(C/A)` is the same thing as a map from
the presentation algebra `P` over `A` which is compatible with the identifications of the
quotients with `C`: this is the universal property of the divided power envelope followed by the
completeness of the target. -/
private theorem existsUnique_completedEnvelope_hom
    (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g)
    (X : CompletedEnvelopeThickening s g hg)
    (B : CompletedCrystallineThickening.{u, v, max u w} s)
    (f : MvPolynomial ι s.A →+* B.ring)
    (hfA : f.comp (algebraMap s.A _) = B.fromBase.toRingHom)
    (hfC : (Ideal.Quotient.mk B.ring.ideal).comp f = B.toQuotient.comp g.toRingHom) :
    ∃! h : X.thickening ⟶ B, h.hom.toRingHom.comp X.presentationMap = f := by
  classical
  rcases X with ⟨hp, ⟨R, b, hc, t, ht, hbij⟩, hr, m, hm, ha, hq⟩
  dsimp only at hr hm ha hq ⊢
  subst R
  have hm' := eq_of_heq hm
  subst m
  have ha' := eq_of_heq ha
  have hq' (q : MvPolynomial ι s.A) := eq_of_heq (hq q)
  let env := polynomialDividedPowerEnvelope s g
  let E := env.object
  let D := completionRing E s.p hp
  let instAE : Algebra s.A E := env.structureMap.toRingHom.toAlgebra
  let instZE : Algebra (DividedPowers.IntegersAtPrime s.p) E :=
    (env.structureMap.toRingHom.comp
      (algebraMap (DividedPowers.IntegersAtPrime s.p) s.A)).toAlgebra
  let instZB : Algebra (DividedPowers.IntegersAtPrime s.p) B.ring :=
    (B.fromBase.toRingHom.comp
      (algebraMap (DividedPowers.IntegersAtPrime s.p) s.A)).toAlgebra
  let instCB : IsAdicComplete (DividedPowers.pAdicIdeal (A := B.ring) s.p) B.ring :=
    B.isComplete
  have hpB : IsNilpotent (Ideal.Quotient.mk B.ring.ideal (s.p : B.ring)) := by
    simpa using s.prime_nilpotent.map B.toQuotient
  have hfI : (RingHom.ker g.toRingHom).map f ≤ B.ring.ideal := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    show f x ∈ B.ring.ideal
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hx' : g x = 0 := hx
    simpa [hx'] using
      congrArg (fun k : MvPolynomial ι s.A →+* B.ring ⧸ B.ring.ideal => k x) hfC
  let pair : IdealPair.Hom (RingHom.ker g.toRingHom) B.ring.ideal := ⟨f, hfI⟩
  let q := (env.homEquiv B.ring B.fromBase).symm
    ⟨pair, IdealPair.Hom.ext_toRingHom _ _ (RingHom.ext fun x => RingHom.congr_fun hfA x)⟩
  have hqf : q.1.toRingHom.comp env.algebraMap.toRingHom = f := by
    have h := env.homEquiv_apply B.ring B.fromBase q
    have ht : (env.homEquiv B.ring B.fromBase q).1 = pair :=
      congrArg Subtype.val ((env.homEquiv B.ring B.fromBase).apply_symm_apply _)
    rw [ht] at h
    exact congrArg IdealPair.Hom.toRingHom h.symm
  let lift : DividedPowers.DPMorphism D.dividedPowers B.ring.dividedPowers :=
    (fromCompletion B.ring s.p hpB).comp (completionMorphism E B.ring s.p hp hpB q.1).1
  have hlift (x : E) : lift (algebraMap E D x) = q.1 x := by
    show (AdicCompletion.ofAlgEquiv (DividedPowers.pAdicIdeal (A := B.ring) s.p)).symm
      ((completionMorphism E B.ring s.p hp hpB q.1).1 (algebraMap E D x)) = _
    rw [completionMorphism_of, AdicCompletion.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, AdicCompletion.ofAlgEquiv_symm_of]
  have hliftA : lift.comp b = B.fromBase := by
    refine dpMorphism_ext (RingHom.ext fun x => ?_)
    show lift (b.toRingHom x) = B.fromBase.toRingHom x
    rw [ha']
    show lift (algebraMap E D (env.structureMap x)) = _
    rw [hlift]
    exact congrArg
      (fun k : DividedPowers.DPMorphism s.A.dividedPowers B.ring.dividedPowers => k x) q.2
  have hliftP : lift.toRingHom.comp (toPAdicCompletedDividedPowerEnvelope s g hg) = f := by
    refine RingHom.ext fun x => ?_
    show lift (algebraMap E D (env.algebraMap.toRingHom x)) = f x
    rw [hlift]
    exact RingHom.congr_fun hqf x
  let T : CompletedCrystallineThickening s :=
    ⟨completedEnvelopeDPRing s g hg hp, b, hc, t, ht, hbij⟩
  have hliftC :
      (DividedPowerRing.quotientRingHom (A := T.ring) (B := B.ring) lift).comp t =
        B.toQuotient := by
    ext c
    obtain ⟨x, rfl⟩ := hg c
    show (DividedPowerRing.quotientRingHom (A := T.ring) (B := B.ring) lift) (t (g x)) =
      B.toQuotient (g x)
    exact (congrArg
      (DividedPowerRing.quotientRingHom (A := T.ring) (B := B.ring) lift) (hq' x)).trans
      ((DividedPowerRing.quotientRingHom_mk (A := T.ring) (B := B.ring) lift _).trans
        ((congrArg (Ideal.Quotient.mk B.ring.ideal) (RingHom.congr_fun hliftP x)).trans
          (RingHom.congr_fun hfC x)))
  let h : T ⟶ B := ⟨lift, hliftA, hliftC⟩
  refine ⟨h, hliftP, fun k hk => ?_⟩
  apply CompletedCrystallineThickening.Hom.ext
  apply dpMorphism_ext
  apply completion_ringHom_ext s.p
  intro x
  let qk := k.hom.comp (toCompletion E s.p hp)
  have hqkA : qk.comp env.structureMap = B.fromBase := by
    refine dpMorphism_ext (RingHom.ext fun y => ?_)
    have hkA := congrArg
      (fun j : DividedPowers.DPMorphism s.A.dividedPowers B.ring.dividedPowers => j y)
      k.fromBase_comp
    change k.hom (b.toRingHom y) = _ at hkA
    rwa [ha'] at hkA
  have hqkeq :
      (⟨qk, hqkA⟩ : { j : DividedPowers.DPMorphism E.dividedPowers B.ring.dividedPowers //
        j.comp env.structureMap = B.fromBase }) = q := by
    apply (env.homEquiv B.ring B.fromBase).injective
    apply Subtype.ext
    rw [env.homEquiv_apply, env.homEquiv_apply]
    exact IdealPair.Hom.ext_toRingHom _ _
      (RingHom.ext fun y => (RingHom.congr_fun hk y).trans (RingHom.congr_fun hqf y).symm)
  show qk x = lift (algebraMap E D x)
  rw [show qk = q.1 from congrArg Subtype.val hqkeq, hlift]

/-- **A morphism out of a realisation of the completed divided power envelope in `Cris^∧(C/A)`
is determined by its restriction along the map from the presentation algebra `P`.**  This is the
uniqueness half of the universal property above, and it is the only handle there is on a map out
of `D` or `D(n)`: the underlying ring is produced by an essential-surjectivity argument, so
nothing about it reduces, and the image of `P` is the sole part of it that is named. -/
public theorem completedEnvelope_hom_ext
    (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g)
    (X : CompletedEnvelopeThickening s g hg)
    (B : CompletedCrystallineThickening.{u, v, max u w} s)
    (k l : X.thickening ⟶ B)
    (h : k.hom.toRingHom.comp X.presentationMap =
      l.hom.toRingHom.comp X.presentationMap) :
    k = l :=
  (existsUnique_completedEnvelope_hom s g hg X B
    (k.hom.toRingHom.comp X.presentationMap)
    (hom_presentationMap_base s g hg X B k) (hom_presentationMap_quotient s g hg X B k)).unique
    rfl h.symm

/-- The `n + 1` canonical morphisms `D → D(n)` in `Cris^∧(C/A)`, one for each tensor factor of
`P ⊗_A … ⊗_A P`.  The `j`-th one is the unique morphism which on the image of the presentation
algebra `P` is the `j`-th polynomial coprojection. -/
@[no_expose]
public noncomputable def completedEnvelopeCoprojections
    (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g) (n : ℕ) :
    { cop : Fin (n + 1) → ((completedEnvelopeThickening s g hg).thickening ⟶
        (tensorPowerEnvelopeThickening s g hg n).thickening) //
      ∀ (j : Fin (n + 1)) (q : MvPolynomial ι s.A),
        (cop j).hom.toRingHom ((completedEnvelopeThickening s g hg).presentationMap q) =
          (tensorPowerEnvelopeThickening s g hg n).presentationMap
            (mvPolynomialCoprojection s.A (n := n) j q) } := by
  classical
  let X := completedEnvelopeThickening s g hg
  let Y := tensorPowerEnvelopeThickening s g hg n
  have hex (j : Fin (n + 1)) : ∃! h : X.thickening ⟶ Y.thickening,
      h.hom.toRingHom.comp X.presentationMap =
        Y.presentationMap.comp (mvPolynomialCoprojection s.A (n := n) j).toRingHom := by
    apply existsUnique_completedEnvelope_hom s g hg X Y.thickening
    · calc
        _ = Y.presentationMap.comp (algebraMap s.A _) := by
          apply RingHom.ext
          intro x
          exact congrArg Y.presentationMap
            ((mvPolynomialCoprojection s.A (n := n) j).commutes x)
        _ = _ := presentationMap_base s _ _ Y
    · exact RingHom.ext fun x => (RingHom.congr_fun (presentationMap_quotient s _ _ Y)
        (mvPolynomialCoprojection s.A (n := n) j x)).trans
        (congrArg Y.thickening.toQuotient
          (DFunLike.congr_fun (tensorPowerPresentation_comp_coprojection s g j) x))
  exact ⟨fun j => Classical.choose (hex j), fun j x =>
    RingHom.congr_fun (Classical.choose_spec (hex j)).1 x⟩

/-- The `j`-th canonical morphism `D → D(n)` in `Cris^∧(C/A)`. -/
public noncomputable abbrev completedEnvelopeCoprojection
    (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g)
    (n : ℕ) (j : Fin (n + 1)) :
    (completedEnvelopeThickening s g hg).thickening ⟶
      (tensorPowerEnvelopeThickening s g hg n).thickening :=
  (completedEnvelopeCoprojections s g hg n).1 j

/-- **Stacks Project, Tag 07L4**, second assertion.  The canonical coprojections exhibit
`D(n)` as the coproduct `∐_{j = 0, …, n} D` of `n + 1` copies of `D` in `Cris^∧(C/A)`. -/
@[stacks 07L4 "the canonical coproduct"]
public theorem completedEnvelope_isCoproduct
    (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g) (n : ℕ) :
    Nonempty (IsColimit (Cofan.mk (tensorPowerEnvelopeThickening s g hg n).thickening
      (completedEnvelopeCoprojection s g hg n))) := by
  classical
  let X := completedEnvelopeThickening s g hg
  let Y := tensorPowerEnvelopeThickening s g hg n
  have hex (B : CompletedCrystallineThickening.{u, v, max u w} s)
      (k : Fin (n + 1) → (X.thickening ⟶ B)) :
      ∃! m : Y.thickening ⟶ B,
        ∀ j, completedEnvelopeCoprojection s g hg n j ≫ m = k j := by
    let instAB : Algebra s.A B.ring := B.fromBase.toRingHom.toAlgebra
    let F (j : Fin (n + 1)) : MvPolynomial ι s.A →ₐ[s.A] B.ring :=
      { __ := (k j).hom.toRingHom.comp X.presentationMap
        commutes' x := RingHom.congr_fun (hom_presentationMap_base s g hg X B (k j)) x }
    let f : MvPolynomial (Fin (n + 1) × ι) s.A →ₐ[s.A] B.ring :=
      MvPolynomial.aeval (fun ji => F ji.1 (MvPolynomial.X ji.2))
    have hfcomp (j : Fin (n + 1)) :
        f.comp (mvPolynomialCoprojection s.A (n := n) j) = F j := by
      ext i
      simp [f, mvPolynomialCoprojection]
    have hfA : f.toRingHom.comp (algebraMap s.A _) = B.fromBase.toRingHom :=
      RingHom.ext f.commutes
    have hfC : (Ideal.Quotient.mk B.ring.ideal).comp f.toRingHom =
        B.toQuotient.comp (tensorPowerPresentation s g n).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro x
        show Ideal.Quotient.mk B.ring.ideal (f (MvPolynomial.C x)) =
          B.toQuotient (tensorPowerPresentation s g n (MvPolynomial.C x))
        rw [show f (MvPolynomial.C x) = B.fromBase x from f.commutes x,
          show tensorPowerPresentation s g n (MvPolynomial.C x) = algebraMap s.A s.C x from
            (tensorPowerPresentation s g n).commutes x]
        exact RingHom.congr_fun B.commutes x
      · rintro ⟨j, i⟩
        have h := RingHom.congr_fun (hom_presentationMap_quotient s g hg X B (k j))
          (MvPolynomial.X i)
        simpa [f, F, tensorPowerPresentation] using h
    obtain ⟨m, hm, huniq⟩ :=
      existsUnique_completedEnvelope_hom s _ _ Y B f.toRingHom hfA hfC
    have hfac (j : Fin (n + 1)) : completedEnvelopeCoprojection s g hg n j ≫ m = k j := by
      refine completedEnvelope_hom_ext s g hg X B _ _ (RingHom.ext fun x => ?_)
      show m.hom.toRingHom
        ((completedEnvelopeCoprojection s g hg n j).hom.toRingHom (X.presentationMap x)) =
        (k j).hom.toRingHom (X.presentationMap x)
      rw [(completedEnvelopeCoprojections s g hg n).2 j x]
      exact (RingHom.congr_fun hm (mvPolynomialCoprojection s.A (n := n) j x)).trans
        (DFunLike.congr_fun (hfcomp j) x)
    refine ⟨m, hfac, fun l hl => ?_⟩
    apply huniq
    apply MvPolynomial.ringHom_ext
    · intro x
      exact (RingHom.congr_fun (hom_presentationMap_base s _ _ Y B l) x).trans
        (f.commutes x).symm
    · rintro ⟨j, i⟩
      have h := congrArg (fun c : X.thickening ⟶ B =>
        c.hom.toRingHom (X.presentationMap (MvPolynomial.X i))) (hl j)
      change l.hom.toRingHom ((completedEnvelopeCoprojection s g hg n j).hom.toRingHom
        (X.presentationMap (MvPolynomial.X i))) =
          (k j).hom.toRingHom (X.presentationMap (MvPolynomial.X i)) at h
      rw [(completedEnvelopeCoprojections s g hg n).2 j (MvPolynomial.X i)] at h
      simpa [mvPolynomialCoprojection, f, F] using h
  exact ⟨Cofan.IsColimit.mk _ (fun c => Classical.choose (hex c.pt c.inj))
    (fun c j => (Classical.choose_spec (hex c.pt c.inj)).1 j)
    (fun c m hm => (Classical.choose_spec (hex c.pt c.inj)).2 m hm)⟩

end Crystalline

end
