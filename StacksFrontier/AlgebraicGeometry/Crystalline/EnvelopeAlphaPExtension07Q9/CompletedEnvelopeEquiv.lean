module

public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeAlphaPExtension07Q9.AlphaPPresentation

/-!
# The completed envelope of an `α_p`-extension: the isomorphism

This file proves the assertion of the proof of [Stacks, Lemma 60.25.4, Tag 07Q9] that the
`p`-adically completed divided power envelope `D'` of `Ker(P[z] → C[z]/(z^p - c))` is isomorphic
to the `p`-adic completion of `D[z]⟨ξ⟩/(ξ - (z^p - λ))`.

## Main definitions

* `Crystalline.alphaPCompletedPrimeDPRing` — the `p`-adic completion of
  `D[z]⟨ξ⟩/(ξ - (z^p - λ))` with the completed divided powers of [Stacks, Tag 07KD].
* `Crystalline.alphaPCompletedEnvelopeEquiv` and `Crystalline.alphaPCompletedEnvelopeIso` — **the
  isomorphism `D' ≅ (D[z]⟨ξ⟩/(ξ - (z^p - λ)))^∧`**, of rings and of divided power rings, for any
  pair of presentations `P → C`, `P' → C'` whose variables are those of `P` and one more.

## Main results

* `Crystalline.isDPMorphism_alphaPCompletedEnvelopeEquiv` and
  `Crystalline.isDPMorphism_alphaPCompletedEnvelopeEquiv_symm` — both directions are divided power
  morphisms.
* `Crystalline.alphaPCompletedEnvelopeEquiv_envelopeMap` — the isomorphism is compatible with the
  two structure maps from `D`; `Crystalline.alphaPCompletedEnvelopeEquiv_root` — it sends `z` to
  `z`.

## Implementation notes

No identification of `Ker(P' → C')` with `Ker(P → C) P' + (z^p - c̃)` and no base change of
envelopes is needed: both maps are produced by universal properties and compared through them.
The map `D' → (D[z]⟨ξ⟩/⋯)^∧` is the completion of the map `E' → D[z]⟨ξ⟩/⋯` out of the uncompleted
envelope `E'` given by the universal property of `E'`: the reduction of `P' → D[z]⟨ξ⟩/⋯` modulo
the divided power ideal `J'` factors through `C'`, so it kills `Ker(P' → C')`.  The map back is the
extension to the completion ([Stacks, Tag 07KD]) of the map `D[z]⟨ξ⟩/⋯ → D'` given by `D → D'`,
`ξ ↦ z^p - λ` (the universal property of `D⟨ξ⟩`, [Stacks, Tag 07H6]) and `z ↦ z`; it is a divided
power morphism because `D⟨ξ⟩ → D⟨ξ⟩[z] → D[z]⟨ξ⟩/⋯` carry the divided power ideals onto each other.
Each composite is the identity because ring maps out of a `p`-adic completion into a `p`-adically
separated ring are determined on the uncompleted ring (`Crystalline.ringHom_ext_pAdicCompletion`),
and divided power morphisms out of an envelope or out of `D⟨ξ⟩` are determined on generators.

The lift `λ` of `c` is a lift in the *completed* `D`: it is required to be congruent, modulo the
divided power ideal of `D`, to the image of a lift `c̃ ∈ P` of `c`, which is what "a lift of `c`"
means, `D` modulo its divided power ideal being `C`.

## References

* [Stacks Project, Lemma 60.25.4, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
-/

@[expose] public section

noncomputable section

open CategoryTheory DividedPowers

universe u v w

namespace Crystalline

/-! ### The map `E' → B[z]⟨ξ⟩/(ξ - (z^p - λ))` -/

section Forward

open PthRootExtension MvPolynomial

variable (s : AffineCrystallineSituation.{u, v}) (c : s.C) {κ κ' : Type w}
  (g : MvPolynomial κ s.A →ₐ[s.A] s.C)
  (g' : MvPolynomial κ' s.A →ₐ[s.A] (alphaPSituation s c).C) (e : Option κ ≃ κ')

/-- The fixed prime of an affine crystalline situation is nonzero. -/
public theorem AffineCrystallineSituation.p_ne_zero : s.p ≠ 0 :=
  (Fact.out : s.p.Prime).ne_zero

variable (lam : envelopeCompletedDPRing s g)

/-- The divided power morphism `A → D → D[z]⟨ξ⟩/(ξ - (z^p - λ))` of the base. -/
public def alphaPBaseDP :
    DPMorphism s.A.dividedPowers (primeDividedPowers (envelopeCompletedDPRing s g) s.p lam
      s.p_ne_zero) :=
  (alphaPAlgebraMapDP (envelopeCompletedDPRing s g) s.p lam s.p_ne_zero).comp
    ((envelopeCompletionDP s g).comp (polynomialDividedPowerEnvelope s g).structureMap)

/-- The images of the variables of `P'`: the class of `z` for the new one, and the image of the
old variable in `D` for the old ones. -/
public def alphaPVariableValue (o : Option κ) :
    primeRing (envelopeCompletedDPRing s g) s.p lam :=
  o.elim (zElt _ s.p lam) fun k =>
    algebraMap (envelopeCompletedDPRing s g) (primeRing (envelopeCompletedDPRing s g) s.p lam)
      (AdicCompletion.of _ _ ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom (X k)))

/-- **The ring map `P' → D[z]⟨ξ⟩/(ξ - (z^p - λ))`** sending `z` to `z` and the old variables to
their images in `D`. -/
public def alphaPPolynomialMap :
    MvPolynomial κ' s.A →+* primeRing (envelopeCompletedDPRing s g) s.p lam :=
  eval₂Hom (alphaPBaseDP s g lam).toRingHom fun j => alphaPVariableValue s g lam (e.symm j)

/-- The map `P' → D[z]⟨ξ⟩/⋯` on constants is the structure map of the base. -/
@[simp] public theorem alphaPPolynomialMap_C (a : s.A) :
    alphaPPolynomialMap s g e lam (C a) = alphaPBaseDP s g lam a :=
  eval₂Hom_C _ _ _

/-- The map `P' → D[z]⟨ξ⟩/⋯` on the variables. -/
@[simp] public theorem alphaPPolynomialMap_X (o : Option κ) :
    alphaPPolynomialMap s g e lam (X (e o)) = alphaPVariableValue s g lam o := by
  rw [alphaPPolynomialMap, eval₂Hom_X', Equiv.symm_apply_apply]

/-- The map `P → E` of the envelope sends a constant to the image of the base. -/
private theorem envelope_algebraMap_C {S : AffineCrystallineSituation.{u, v}} {ι : Type w}
    (h : MvPolynomial ι S.A →ₐ[S.A] S.C) (a : S.A) :
    (polynomialDividedPowerEnvelope S h).algebraMap.toRingHom (C a) =
      (polynomialDividedPowerEnvelope S h).structureMap a :=
  RingHom.congr_fun (polynomialDividedPowerEnvelope S h).algebraMap_comp a

/-- On the old variables, the map `P' → D[z]⟨ξ⟩/(ξ - (z^p - λ))` is `P → E → D → D[z]⟨ξ⟩/⋯`. -/
public theorem alphaPPolynomialMap_rename (x : MvPolynomial κ s.A) :
    alphaPPolynomialMap s g e lam (rename (e ∘ some) x) =
      algebraMap (envelopeCompletedDPRing s g) (primeRing (envelopeCompletedDPRing s g) s.p lam)
        (AdicCompletion.of _ _ ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom x)) := by
  have h : (alphaPPolynomialMap s g e lam).comp (rename (e ∘ some)).toRingHom =
      ((algebraMap (envelopeCompletedDPRing s g)
        (primeRing (envelopeCompletedDPRing s g) s.p lam)).comp
        (algebraMap (polynomialDividedPowerEnvelope s g).object
          (envelopeCompletedDPRing s g))).comp
        (polynomialDividedPowerEnvelope s g).algebraMap.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        rename_C, alphaPPolynomialMap_C]
      rw [envelope_algebraMap_C]
      rfl
    · intro k
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X,
        Function.comp_apply, alphaPPolynomialMap_X]
      rfl
  exact RingHom.congr_fun h x

section Kernel

variable {s c g g' e} {lam}
variable (hg : Function.Surjective g) (hnone : g' (X (e none)) = alphaPRoot s c)
  (hsome : ∀ k, g' (X (e (some k))) = algebraMap s.C (alphaPSituation s c).C (g (X k)))
  {ct : MvPolynomial κ s.A} (hct : g ct = c)
  (hlam : lam - AdicCompletion.of _ _ ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom ct)
    ∈ (envelopeCompletedDPRing s g).ideal)

/-- The reduction `P → E → D → D[z]⟨ξ⟩/⋯ → (D[z]⟨ξ⟩/⋯)/J'`. -/
private def reductionOfP :
    MvPolynomial κ s.A →+* primeRing (envelopeCompletedDPRing s g) s.p lam ⧸
      primeIdeal (envelopeCompletedDPRing s g) s.p lam :=
  (Ideal.Quotient.mk _).comp (((algebraMap (envelopeCompletedDPRing s g)
    (primeRing (envelopeCompletedDPRing s g) s.p lam)).comp
    (algebraMap (polynomialDividedPowerEnvelope s g).object (envelopeCompletedDPRing s g))).comp
    (polynomialDividedPowerEnvelope s g).algebraMap.toRingHom)

private theorem reductionOfP_eq_zero (x : MvPolynomial κ s.A) (hx : g x = 0) :
    reductionOfP (g := g) (lam := lam) x = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have h1 := (polynomialDividedPowerEnvelope s g).algebraMap.ideal_comp
    (Ideal.mem_map_of_mem _ (show x ∈ RingHom.ker g.toRingHom from hx))
  have h2 := (envelopeCompletionDP s g).ideal_comp (Ideal.mem_map_of_mem _ h1)
  exact (alphaPAlgebraMapDP (envelopeCompletedDPRing s g) s.p lam s.p_ne_zero).ideal_comp
    (Ideal.mem_map_of_mem _ h2)

/-- The reduction `C → (D[z]⟨ξ⟩/⋯)/J'`, through `C = P / Ker(P → C)`. -/
private def reductionOfC :
    s.C →+* primeRing (envelopeCompletedDPRing s g) s.p lam ⧸
      primeIdeal (envelopeCompletedDPRing s g) s.p lam :=
  (Ideal.Quotient.lift (RingHom.ker g.toRingHom) (reductionOfP (g := g) (lam := lam))
    fun x hx => reductionOfP_eq_zero x hx).comp
    (RingHom.quotientKerEquivOfSurjective (f := g.toRingHom) hg).symm.toRingHom

private theorem reductionOfC_apply (x : MvPolynomial κ s.A) :
    reductionOfC (lam := lam) hg (g x) = reductionOfP (g := g) (lam := lam) x := by
  change Ideal.Quotient.lift (RingHom.ker g.toRingHom) (reductionOfP (g := g) (lam := lam))
    (fun x hx => reductionOfP_eq_zero x hx)
    ((RingHom.quotientKerEquivOfSurjective (f := g.toRingHom) hg).symm (g.toRingHom x)) = _
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.lift_mk]

include hct hlam in
private theorem reductionOfC_relation :
    Polynomial.eval₂RingHom (reductionOfC (lam := lam) hg)
        (Ideal.Quotient.mk _ (zElt _ s.p lam))
        (Polynomial.X ^ s.p - Polynomial.C c : Polynomial s.C) = 0 := by
  subst hct
  rw [map_sub, map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.eval₂_C,
    reductionOfC_apply, reductionOfP, ← map_pow, zElt_pow_prime, xiElt_zero_zero,
    Algebra.smul_def, mul_one]
  simp only [RingHom.comp_apply]
  rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem, add_sub_assoc, ← map_sub]
  refine add_mem (xiElt_one_zero_mem _ s.p lam s.p_ne_zero) ?_
  exact (alphaPAlgebraMapDP (envelopeCompletedDPRing s g) s.p lam s.p_ne_zero).ideal_comp
    (Ideal.mem_map_of_mem _ hlam)

/-- The reduction `C' = C[z]/(z^p - c) → (D[z]⟨ξ⟩/⋯)/J'` sending `z` to `z`. -/
private def reductionOfC' :
    (alphaPSituation s c).C →+* primeRing (envelopeCompletedDPRing s g) s.p lam ⧸
      primeIdeal (envelopeCompletedDPRing s g) s.p lam :=
  Ideal.Quotient.lift _ (Polynomial.eval₂RingHom (reductionOfC (lam := lam) hg)
      (Ideal.Quotient.mk _ (zElt _ s.p lam))) fun x hx => by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, reductionOfC_relation hg hct hlam, mul_zero]

include hnone hsome in
private theorem reductionOfC'_comp (x : MvPolynomial κ' s.A) :
    Ideal.Quotient.mk _ (alphaPPolynomialMap s g e lam x) =
      reductionOfC' hg hct hlam (g' x) := by
  have h : (Ideal.Quotient.mk _).comp (alphaPPolynomialMap s g e lam) =
      (reductionOfC' hg hct hlam).comp g'.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have hga : g' (C a) = Ideal.Quotient.mk _ (Polynomial.C (g (C a))) := by
        rw [show g (C a) = algebraMap s.A s.C a from g.commutes a,
          show g' (C a) = algebraMap s.A (alphaPSituation s c).C a from g'.commutes a]
        rfl
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [hga, reductionOfC', Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C, reductionOfC_apply, alphaPPolynomialMap_C, reductionOfP]
      simp only [RingHom.comp_apply]
      rw [envelope_algebraMap_C]
      rfl
    · intro j
      obtain ⟨o, rfl⟩ := e.surjective j
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        alphaPPolynomialMap_X]
      cases o with
      | none =>
        rw [hnone, reductionOfC', Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_X]
        rfl
      | some k =>
        rw [hsome k]
        change _ = reductionOfC' hg hct hlam (Ideal.Quotient.mk _ (Polynomial.C (g (X k))))
        rw [reductionOfC', Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_C, reductionOfC_apply]
        rfl
  exact RingHom.congr_fun h x

include hg hnone hsome hct hlam in
/-- The map `P' → D[z]⟨ξ⟩/(ξ - (z^p - λ))` carries the kernel of `P' → C'` into the divided power
ideal `J'`. -/
public theorem alphaPPolynomialMap_ker_le :
    (RingHom.ker g'.toRingHom).map (alphaPPolynomialMap s g e lam) ≤
      primeIdeal (envelopeCompletedDPRing s g) s.p lam := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change alphaPPolynomialMap s g e lam x ∈ primeIdeal (envelopeCompletedDPRing s g) s.p lam
  rw [← Ideal.Quotient.eq_zero_iff_mem, reductionOfC'_comp hg hnone hsome hct hlam,
    show g' x = 0 from hx, map_zero]

/-- `p` is nilpotent modulo the divided power ideal of the completed envelope. -/
public theorem envelopeCompletedDPRing_isNilpotent :
    IsNilpotent (Ideal.Quotient.mk (envelopeCompletedDPRing s g).ideal
      ((s.p : ℕ) : envelopeCompletedDPRing s g)) :=
  isNilpotent_mk_completionIdeal _ s.p _

variable (s g lam) in
/-- **The `p`-adic completion of `D[z]⟨ξ⟩/(ξ - (z^p - λ))`**, with the completed divided powers. -/
public abbrev alphaPCompletedPrimeDPRing : DividedPowerRing.{max u w} :=
  pAdicCompletedDPRing (primeDPRing (envelopeCompletedDPRing s g) s.p lam s.p_ne_zero) s.p
    (alphaP_isNilpotent_mk_primeIdeal _ s.p lam s.p_ne_zero
      (envelopeCompletedDPRing_isNilpotent (g := g)))

variable (s g lam) in
/-- The completion map of `D[z]⟨ξ⟩/(ξ - (z^p - λ))` as a divided power morphism. -/
public abbrev alphaPPrimeCompletionDP :
    DPMorphism (primeDividedPowers (envelopeCompletedDPRing s g) s.p lam s.p_ne_zero)
      (alphaPCompletedPrimeDPRing s g lam).dividedPowers :=
  completionDPMorphism (primeDPRing (envelopeCompletedDPRing s g) s.p lam s.p_ne_zero).ideal
    (primeDPRing (envelopeCompletedDPRing s g) s.p lam s.p_ne_zero).dividedPowers s.p _

/-- **The divided power morphism `E' → D[z]⟨ξ⟩/(ξ - (z^p - λ))`** given by the universal property
of the envelope `E'` of `Ker(P' → C')`. -/
public def alphaPEnvelopeToPrime :
    DPMorphism (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object.dividedPowers
      (primeDividedPowers (envelopeCompletedDPRing s g) s.p lam s.p_ne_zero) :=
  (polynomialDividedPowerEnvelope (alphaPSituation s c) g').liftDP
    (primeDPRing (envelopeCompletedDPRing s g) s.p lam s.p_ne_zero) (alphaPBaseDP s g lam)
    (alphaPPolynomialMap s g e lam) (alphaPPolynomialMap_ker_le hg hnone hsome hct hlam)
    (by
      ext a
      exact alphaPPolynomialMap_C s g e lam a)

/-- The map `E' → D[z]⟨ξ⟩/⋯` restricts to `Crystalline.alphaPPolynomialMap` on `P'`. -/
public theorem alphaPEnvelopeToPrime_algebraMap (x : MvPolynomial κ' s.A) :
    alphaPEnvelopeToPrime hg hnone hsome hct hlam
        ((polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom x) =
      alphaPPolynomialMap s g e lam x :=
  DividedPowerEnvelope.liftDP_algebraMap _ _ _ _ _ _ x

/-- **The map of completions `D' → (D[z]⟨ξ⟩/(ξ - (z^p - λ)))^∧`**. -/
public def alphaPCompletedEnvelopeToPrime :
    DPMorphism (envelopeCompletedDPRing (alphaPSituation s c) g').dividedPowers
      (alphaPCompletedPrimeDPRing s g lam).dividedPowers :=
  DPMorphism.mk' (adicCompletionRingMap_isDPMorphism _ _ s.p _ _
    (alphaPEnvelopeToPrime hg hnone hsome hct hlam))

/-- The map `D' → (D[z]⟨ξ⟩/⋯)^∧` is the completion of the map `E' → D[z]⟨ξ⟩/⋯`. -/
public theorem alphaPCompletedEnvelopeToPrime_of
    (x : (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object) :
    alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _ (alphaPEnvelopeToPrime hg hnone hsome hct hlam x) :=
  adicCompletionRingMap_of _ _ x

/-! ### The map back -/

variable (s c g' e) in
/-- The class of `z` in `D'`. -/
public abbrev alphaPCompletedRoot : envelopeCompletedDPRing (alphaPSituation s c) g' :=
  AdicCompletion.of _ _
    ((polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom (X (e none)))

include hnone hsome hct hlam in
/-- `z^p - λ` lies in the divided power ideal of `D'`. -/
public theorem alphaPCompletedRoot_pow_sub_mem :
    alphaPCompletedRoot s c g' e ^ s.p - alphaPCompletedEnvelopeMap hsome lam ∈
      (envelopeCompletedDPRing (alphaPSituation s c) g').ideal := by
  have hct' : alphaPCompletedEnvelopeMap hsome
      (AdicCompletion.of _ _ ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom ct)) =
      AdicCompletion.of _ _
        ((polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom
          (rename (e ∘ some) ct)) := by
    rw [alphaPCompletedEnvelopeMap_of, alphaPEnvelopeMap_algebraMap]
  have hdecomp : alphaPCompletedRoot s c g' e ^ s.p - alphaPCompletedEnvelopeMap hsome lam =
      AdicCompletion.of _ _
        ((polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom
          (X (e none) ^ s.p - rename (e ∘ some) ct)) -
        alphaPCompletedEnvelopeMap hsome (lam -
          AdicCompletion.of _ _
            ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom ct)) := by
    have hm : ∀ x y, alphaPCompletedEnvelopeMap hsome (x - y) =
        alphaPCompletedEnvelopeMap hsome x - alphaPCompletedEnvelopeMap hsome y :=
      fun x y => map_sub (alphaPCompletedEnvelopeMap hsome).toRingHom x y
    rw [hm, hct']
    simp only [AdicCompletion.of_eq_algebraMap, map_sub, map_pow]
    ring
  rw [hdecomp]
  refine sub_mem ?_ ((alphaPCompletedEnvelopeMap hsome).ideal_comp (Ideal.mem_map_of_mem _ hlam))
  refine (envelopeCompletionDP (alphaPSituation s c) g').ideal_comp (Ideal.mem_map_of_mem _ ?_)
  refine (polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.ideal_comp
    (Ideal.mem_map_of_mem _ ?_)
  change g' (X (e none) ^ s.p - rename (e ∘ some) ct) = 0
  rw [map_sub, map_pow, hnone, alphaP_rename_mem_ker hsome, hct, alphaPRoot]
  change Ideal.Quotient.mk _ (Polynomial.X ^ s.p) - Ideal.Quotient.mk _ (Polynomial.C c) = 0
  rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

/-- The divided power morphism `D⟨ξ⟩ → D'` sending `ξ` to `z^p - λ`. -/
public def xiToCompleted :
    DPMorphism (xiDPRing (envelopeCompletedDPRing s g)).dividedPowers
      (envelopeCompletedDPRing (alphaPSituation s c) g').dividedPowers :=
  (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial
    (envelopeCompletedDPRing s g) Unit (envelopeCompletedDPRing (alphaPSituation s c) g')
    (alphaPCompletedEnvelopeMap hsome)
    (fun _ => ⟨_, alphaPCompletedRoot_pow_sub_mem hnone hsome hct hlam⟩)).exists.choose

/-- The map `D⟨ξ⟩ → D'` extends `D → D'` and sends `ξ` to `z^p - λ`. -/
public theorem xiToCompleted_spec :
    (xiToCompleted hnone hsome hct hlam).comp
        (setIndexedDividedPowerPolynomialCoefficientDPMorphism _ Unit) =
      alphaPCompletedEnvelopeMap hsome ∧
    xiToCompleted hnone hsome hct hlam (xi (envelopeCompletedDPRing s g)) =
      alphaPCompletedRoot s c g' e ^ s.p - alphaPCompletedEnvelopeMap hsome lam :=
  let h := (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial
    (envelopeCompletedDPRing s g) Unit (envelopeCompletedDPRing (alphaPSituation s c) g')
    (alphaPCompletedEnvelopeMap hsome)
    (fun _ => ⟨_, alphaPCompletedRoot_pow_sub_mem hnone hsome hct hlam⟩)).exists.choose_spec
  ⟨h.1, h.2 ()⟩

/-- The map `D⟨ξ⟩ → D'` extends `D → D'`. -/
public theorem xiToCompleted_algebraMap (d : envelopeCompletedDPRing s g) :
    xiToCompleted hnone hsome hct hlam (algebraMap _ (XiAlg (envelopeCompletedDPRing s g)) d) =
      alphaPCompletedEnvelopeMap hsome d :=
  congrArg (fun q : DPMorphism _ _ => q d) (xiToCompleted_spec hnone hsome hct hlam).1

/-- The relation `z^p - ξ - λ` holds for `z` and `z^p - λ` in `D'`. -/
public theorem xiToCompleted_eval₂_primePoly :
    (primePoly (envelopeCompletedDPRing s g) s.p lam).eval₂
      (xiToCompleted hnone hsome hct hlam).toRingHom (alphaPCompletedRoot s c g' e) = 0 := by
  rw [primePoly, Polynomial.eval₂_sub, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_C]
  change _ - xiToCompleted hnone hsome hct hlam (xi _) -
    xiToCompleted hnone hsome hct hlam (algebraMap _ _ lam) = 0
  rw [(xiToCompleted_spec hnone hsome hct hlam).2, xiToCompleted_algebraMap]
  ring

/-- **The ring map `D[z]⟨ξ⟩/(ξ - (z^p - λ)) → D'`** sending `z` to `z`. -/
public def alphaPPrimeToCompleted :
    primeRing (envelopeCompletedDPRing s g) s.p lam →+*
      envelopeCompletedDPRing (alphaPSituation s c) g' :=
  AdjoinRoot.lift (xiToCompleted hnone hsome hct hlam).toRingHom (alphaPCompletedRoot s c g' e)
    (xiToCompleted_eval₂_primePoly hnone hsome hct hlam)

/-- The map back sends `z` to the class of `z`. -/
public theorem alphaPPrimeToCompleted_zElt :
    alphaPPrimeToCompleted hnone hsome hct hlam (zElt _ s.p lam) =
      alphaPCompletedRoot s c g' e :=
  AdjoinRoot.lift_root _

/-- The map back extends `D → D'`. -/
public theorem alphaPPrimeToCompleted_algebraMap (d : envelopeCompletedDPRing s g) :
    alphaPPrimeToCompleted hnone hsome hct hlam
        (algebraMap _ (primeRing (envelopeCompletedDPRing s g) s.p lam) d) =
      alphaPCompletedEnvelopeMap hsome d := by
  rw [IsScalarTower.algebraMap_apply (envelopeCompletedDPRing s g)
    (XiAlg (envelopeCompletedDPRing s g)) (primeRing (envelopeCompletedDPRing s g) s.p lam),
    AdjoinRoot.algebraMap_eq, alphaPPrimeToCompleted, AdjoinRoot.lift_of]
  exact xiToCompleted_algebraMap hnone hsome hct hlam d

/-- The map back is a divided power morphism. -/
public theorem alphaPPrimeToCompleted_isDPMorphism :
    IsDPMorphism (primeDividedPowers (envelopeCompletedDPRing s g) s.p lam s.p_ne_zero)
      (envelopeCompletedDPRing (alphaPSituation s c) g').dividedPowers
      (alphaPPrimeToCompleted hnone hsome hct hlam) := by
  have h0 : IsDPMorphism (zPolyDPRing (envelopeCompletedDPRing s g)).dividedPowers
      (envelopeCompletedDPRing (alphaPSituation s c) g').dividedPowers
      (Polynomial.eval₂RingHom (xiToCompleted hnone hsome hct hlam).toRingHom
        (alphaPCompletedRoot s c g' e)) :=
    IsDPMorphism.of_comp (hI := (xiDPRing (envelopeCompletedDPRing s g)).dividedPowers)
      (hJ := (zPolyDPRing (envelopeCompletedDPRing s g)).dividedPowers)
      (hK := (envelopeCompletedDPRing (alphaPSituation s c) g').dividedPowers)
      Polynomial.C _ rfl (isDPMorphism_C_polynomialDividedPowerRing _)
      (by
        convert (xiToCompleted hnone hsome hct hlam).isDPMorphism using 1
        exact RingHom.ext fun x => Polynomial.eval₂_C _ _)
  refine IsDPMorphism.of_comp (hI := (zPolyDPRing (envelopeCompletedDPRing s g)).dividedPowers)
    (hJ := primeDividedPowers (envelopeCompletedDPRing s g) s.p lam s.p_ne_zero)
    (hK := (envelopeCompletedDPRing (alphaPSituation s c) g').dividedPowers)
    (relationQuotientMk _ s.p lam) _ rfl (isDPMorphism_relationQuotientMk _ s.p lam s.p_ne_zero)
    ?_
  convert h0 using 1
  exact RingHom.ext fun x =>
    AdjoinRoot.lift_mk (xiToCompleted_eval₂_primePoly hnone hsome hct hlam) x

/-- The `ℤ_(p)`-algebra structure of `D[z]⟨ξ⟩/(ξ - (z^p - λ))` through the base. -/
@[instance_reducible]
public def alphaPPrimeAlgebraIntegers :
    Algebra (IntegersAtPrime s.p) (primeDPRing (envelopeCompletedDPRing s g) s.p lam s.p_ne_zero) :=
  ((alphaPBaseDP s g lam).toRingHom.comp (algebraMap (IntegersAtPrime s.p) s.A)).toAlgebra

/-- The `ℤ_(p)`-algebra structure of a completed envelope through the base. -/
@[instance_reducible]
public def envelopeCompletedAlgebraIntegers (s : AffineCrystallineSituation.{u, v}) {κ : Type w}
    (g : MvPolynomial κ s.A →ₐ[s.A] s.C) :
    Algebra (IntegersAtPrime s.p) (envelopeCompletedDPRing s g) :=
  ((envelopeCompletionDP s g).toRingHom.comp
    ((polynomialDividedPowerEnvelope s g).structureMap.toRingHom.comp
      (algebraMap (IntegersAtPrime s.p) s.A))).toAlgebra


/-- The existence of the completed map back. -/
public theorem exists_completedPrimeToEnvelope :
    ∃ q : DPMorphism (alphaPCompletedPrimeDPRing s g lam).dividedPowers
      (envelopeCompletedDPRing (alphaPSituation s c) g').dividedPowers,
      ∀ x, q (AdicCompletion.of _ _ x) = alphaPPrimeToCompleted hnone hsome hct hlam x := by
  let := alphaPPrimeAlgebraIntegers (s := s) (g := g) (lam := lam)
  let := envelopeCompletedAlgebraIntegers (alphaPSituation s c) g'
  have h1 := alphaP_isNilpotent_mk_primeIdeal _ s.p lam s.p_ne_zero
      (envelopeCompletedDPRing_isNilpotent (g := g))
  have h2 : IsNilpotent (Ideal.Quotient.mk (envelopeCompletedDPRing (alphaPSituation s c) g').ideal
      ((s.p : ℕ) : envelopeCompletedDPRing (alphaPSituation s c) g')) :=
    envelopeCompletedDPRing_isNilpotent (s := alphaPSituation s c) (g := g')
  have h3 : IsAdicComplete (pAdicIdeal (A := envelopeCompletedDPRing (alphaPSituation s c) g') s.p)
      (envelopeCompletedDPRing (alphaPSituation s c) g') :=
    pAdicCompletedDPRing.isAdicComplete _ _ _
  exact exists_dpMorphism_pAdicCompletedDPRing
    (primeDPRing (envelopeCompletedDPRing s g) s.p lam s.p_ne_zero)
    (envelopeCompletedDPRing (alphaPSituation s c) g') s.p h1 h2
    (DPMorphism.mk' (alphaPPrimeToCompleted_isDPMorphism hnone hsome hct hlam))

/-- **The completed map back `(D[z]⟨ξ⟩/(ξ - (z^p - λ)))^∧ → D'`**, the extension of the map back to
the completion by the universal property of [Stacks, Tag 07KD]. -/
public def alphaPCompletedPrimeToEnvelope :
    DPMorphism (alphaPCompletedPrimeDPRing s g lam).dividedPowers
      (envelopeCompletedDPRing (alphaPSituation s c) g').dividedPowers :=
  (exists_completedPrimeToEnvelope hnone hsome hct hlam).choose

/-- The completed map back extends the map back. -/
public theorem alphaPCompletedPrimeToEnvelope_of
    (x : primeRing (envelopeCompletedDPRing s g) s.p lam) :
    alphaPCompletedPrimeToEnvelope hnone hsome hct hlam (AdicCompletion.of _ _ x) =
      alphaPPrimeToCompleted hnone hsome hct hlam x :=
  (exists_completedPrimeToEnvelope hnone hsome hct hlam).choose_spec x

/-! ### The two composites -/

/-- On the old envelope `E`, the map `E → E' → D[z]⟨ξ⟩/⋯` is `E → D → D[z]⟨ξ⟩/⋯`. -/
public theorem alphaPEnvelopeToPrime_envelopeMap (x : (polynomialDividedPowerEnvelope s g).object) :
    alphaPEnvelopeToPrime hg hnone hsome hct hlam (alphaPEnvelopeMap hsome x) =
      algebraMap (envelopeCompletedDPRing s g) (primeRing (envelopeCompletedDPRing s g) s.p lam)
        (AdicCompletion.of _ _ x) := by
  have h := (polynomialDividedPowerEnvelope s g).dpMorphism_ext
    (T := primeDPRing (envelopeCompletedDPRing s g) s.p lam s.p_ne_zero)
    ((alphaPEnvelopeToPrime hg hnone hsome hct hlam).comp (alphaPEnvelopeMap hsome))
    ((alphaPAlgebraMapDP (envelopeCompletedDPRing s g) s.p lam s.p_ne_zero).comp
      (envelopeCompletionDP s g)) (fun y => by
      change alphaPEnvelopeToPrime hg hnone hsome hct hlam (alphaPEnvelopeMap hsome
        ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom y)) = _
      rw [alphaPEnvelopeMap_algebraMap, alphaPEnvelopeToPrime_algebraMap,
        alphaPPolynomialMap_rename]
      rfl)
  exact congrArg (fun q : DPMorphism _ _ => q x) h

/-- **The comparison is compatible with the structure maps from `D`**: `D → D' → (⋯)^∧` is
`D → D[z]⟨ξ⟩/⋯ → (⋯)^∧`. -/
public theorem alphaPCompletedEnvelopeToPrime_envelopeMap (d : envelopeCompletedDPRing s g) :
    alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam (alphaPCompletedEnvelopeMap hsome d) =
      AdicCompletion.of _ _
        (algebraMap (envelopeCompletedDPRing s g)
          (primeRing (envelopeCompletedDPRing s g) s.p lam) d) := by
  have h := ringHom_ext_pAdicCompletion s.p
    ((alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam).toRingHom.comp
      (alphaPCompletedEnvelopeMap hsome).toRingHom)
    ((algebraMap (primeRing (envelopeCompletedDPRing s g) s.p lam)
      (alphaPCompletedPrimeDPRing s g lam)).comp
      (algebraMap (envelopeCompletedDPRing s g)
        (primeRing (envelopeCompletedDPRing s g) s.p lam))) (fun x => by
      change alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam
        (alphaPCompletedEnvelopeMap hsome (AdicCompletion.of _ _ x)) = _
      rw [alphaPCompletedEnvelopeMap_of, alphaPCompletedEnvelopeToPrime_of,
        alphaPEnvelopeToPrime_envelopeMap]
      rfl)
  exact RingHom.congr_fun h d

/-- The comparison sends the class of `z` to the class of `z`. -/
public theorem alphaPCompletedEnvelopeToPrime_root :
    alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam (alphaPCompletedRoot s c g' e) =
      AdicCompletion.of _ _ (zElt (envelopeCompletedDPRing s g) s.p lam) := by
  rw [alphaPCompletedRoot, alphaPCompletedEnvelopeToPrime_of, alphaPEnvelopeToPrime_algebraMap,
    alphaPPolynomialMap_X]
  rfl

/-- The composite `E' → D[z]⟨ξ⟩/⋯ → D'` is the completion map of `E'`. -/
public theorem alphaPPrimeToCompleted_envelopeToPrime
    (x : (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object) :
    alphaPPrimeToCompleted hnone hsome hct hlam (alphaPEnvelopeToPrime hg hnone hsome hct hlam x) =
      AdicCompletion.of _ _ x := by
  have hP : (alphaPPrimeToCompleted hnone hsome hct hlam).comp (alphaPPolynomialMap s g e lam) =
      (algebraMap (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object
        (envelopeCompletedDPRing (alphaPSituation s c) g')).comp
        (polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, alphaPPolynomialMap_C]
      change alphaPPrimeToCompleted hnone hsome hct hlam
        (algebraMap (envelopeCompletedDPRing s g) _ (AdicCompletion.of _ _
          ((polynomialDividedPowerEnvelope s g).structureMap a))) = _
      rw [alphaPPrimeToCompleted_algebraMap, alphaPCompletedEnvelopeMap_of,
        alphaPEnvelopeMap_structureMap, envelope_algebraMap_C]
      rfl
    · intro j
      obtain ⟨o, rfl⟩ := e.surjective j
      simp only [RingHom.comp_apply, alphaPPolynomialMap_X]
      cases o with
      | none =>
        change alphaPPrimeToCompleted hnone hsome hct hlam (zElt _ s.p lam) = _
        rw [alphaPPrimeToCompleted_zElt]
        rfl
      | some k =>
        change alphaPPrimeToCompleted hnone hsome hct hlam
          (algebraMap (envelopeCompletedDPRing s g) _ (AdicCompletion.of _ _
            ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom (X k)))) = _
        rw [alphaPPrimeToCompleted_algebraMap, alphaPCompletedEnvelopeMap_of,
          alphaPEnvelopeMap_algebraMap, rename_X]
        rfl
  have h := (polynomialDividedPowerEnvelope (alphaPSituation s c) g').dpMorphism_ext
    (T := envelopeCompletedDPRing (alphaPSituation s c) g')
    ((DPMorphism.mk' (alphaPPrimeToCompleted_isDPMorphism hnone hsome hct hlam)).comp
      (alphaPEnvelopeToPrime hg hnone hsome hct hlam))
    (envelopeCompletionDP (alphaPSituation s c) g') (fun y => by
      change alphaPPrimeToCompleted hnone hsome hct hlam (alphaPEnvelopeToPrime hg hnone hsome hct
        hlam ((polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom y)) = _
      rw [alphaPEnvelopeToPrime_algebraMap]
      exact RingHom.congr_fun hP y)
  exact congrArg (fun q : DPMorphism _ _ => q x) h

/-- **The completed map back is a left inverse of the comparison.** -/
public theorem alphaPCompletedPrimeToEnvelope_comp
    (y : envelopeCompletedDPRing (alphaPSituation s c) g') :
    alphaPCompletedPrimeToEnvelope hnone hsome hct hlam
        (alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam y) = y := by
  have h := ringHom_ext_pAdicCompletion s.p
    ((alphaPCompletedPrimeToEnvelope hnone hsome hct hlam).toRingHom.comp
      (alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam).toRingHom)
    (RingHom.id _) (fun x => by
      change alphaPCompletedPrimeToEnvelope hnone hsome hct hlam
        (alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam (AdicCompletion.of _ _ x)) = _
      rw [alphaPCompletedEnvelopeToPrime_of, alphaPCompletedPrimeToEnvelope_of,
        alphaPPrimeToCompleted_envelopeToPrime]
      rfl)
  exact RingHom.congr_fun h y

/-- The comparison on `D⟨ξ⟩ ⊆ D[z]⟨ξ⟩/⋯`: `D⟨ξ⟩ → D' → (⋯)^∧` is the inclusion followed by the
completion map. -/
public theorem alphaPCompletedEnvelopeToPrime_xiToCompleted
    (y : XiAlg (envelopeCompletedDPRing s g)) :
    alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam (xiToCompleted hnone hsome hct hlam y) =
      AdicCompletion.of _ _
        (AdjoinRoot.of (primePoly (envelopeCompletedDPRing s g) s.p lam) y) := by
  have hmem : AdicCompletion.of _ _ (xiElt (envelopeCompletedDPRing s g) s.p lam 1 0) ∈
      (alphaPCompletedPrimeDPRing s g lam).ideal :=
    (alphaPPrimeCompletionDP s g lam).ideal_comp
      (Ideal.mem_map_of_mem _ (xiElt_one_zero_mem _ s.p lam s.p_ne_zero))
  have hU := existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial
    (envelopeCompletedDPRing s g) Unit (alphaPCompletedPrimeDPRing s g lam)
    ((alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam).comp
      (alphaPCompletedEnvelopeMap hsome)) (fun _ => ⟨_, hmem⟩)
  have hroot : alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam
      (alphaPCompletedRoot s c g' e ^ s.p - alphaPCompletedEnvelopeMap hsome lam) =
      AdicCompletion.of _ _ (xiElt (envelopeCompletedDPRing s g) s.p lam 1 0) := by
    have hm := map_sub (alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam).toRingHom
      (alphaPCompletedRoot s c g' e ^ s.p) (alphaPCompletedEnvelopeMap hsome lam)
    have hp := map_pow (alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam).toRingHom
      (alphaPCompletedRoot s c g' e) s.p
    simp only [DPMorphism.toRingHom_apply] at hm hp
    rw [hm, hp, alphaPCompletedEnvelopeToPrime_root, alphaPCompletedEnvelopeToPrime_envelopeMap,
      xiElt_one_zero, xi_eq, IsScalarTower.algebraMap_apply (envelopeCompletedDPRing s g)
        (XiAlg (envelopeCompletedDPRing s g)) (primeRing (envelopeCompletedDPRing s g) s.p lam),
      AdjoinRoot.algebraMap_eq]
    simp only [AdicCompletion.of_eq_algebraMap, map_sub, map_pow]
  have h1 : ((DPMorphism.mk'
      (alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam).isDPMorphism).comp
      (xiToCompleted hnone hsome hct hlam)).comp
        (setIndexedDividedPowerPolynomialCoefficientDPMorphism _ Unit) =
      (alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam).comp
        (alphaPCompletedEnvelopeMap hsome) ∧
      ∀ i : Unit, ((DPMorphism.mk'
        (alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam).isDPMorphism).comp
        (xiToCompleted hnone hsome hct hlam)) (dividedPowerPolynomialVariable _ i) =
        AdicCompletion.of _ _ (xiElt (envelopeCompletedDPRing s g) s.p lam 1 0) := by
    refine ⟨?_, fun _ => ?_⟩
    · apply DPMorphism.ext
      funext d
      change alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam
        (xiToCompleted hnone hsome hct hlam (algebraMap _ _ d)) = _
      rw [xiToCompleted_algebraMap]
      rfl
    · change alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam
        (xiToCompleted hnone hsome hct hlam (xi _)) = _
      rw [(xiToCompleted_spec hnone hsome hct hlam).2, hroot]
  have h2 : ((alphaPPrimeCompletionDP s g lam).comp
      ((DPMorphism.mk' (isDPMorphism_relationQuotientMk _ s.p lam s.p_ne_zero)).comp
        (DPMorphism.mk' (isDPMorphism_C_polynomialDividedPowerRing
          (xiDPRing (envelopeCompletedDPRing s g)))))).comp
        (setIndexedDividedPowerPolynomialCoefficientDPMorphism _ Unit) =
      (alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam).comp
        (alphaPCompletedEnvelopeMap hsome) ∧
      ∀ i : Unit, ((alphaPPrimeCompletionDP s g lam).comp
      ((DPMorphism.mk' (isDPMorphism_relationQuotientMk _ s.p lam s.p_ne_zero)).comp
        (DPMorphism.mk' (isDPMorphism_C_polynomialDividedPowerRing
          (xiDPRing (envelopeCompletedDPRing s g)))))) (dividedPowerPolynomialVariable _ i) =
        AdicCompletion.of _ _ (xiElt (envelopeCompletedDPRing s g) s.p lam 1 0) := by
    refine ⟨?_, fun _ => ?_⟩
    · apply DPMorphism.ext
      funext d
      change _ = alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam
        (alphaPCompletedEnvelopeMap hsome d)
      rw [alphaPCompletedEnvelopeToPrime_envelopeMap]
      rfl
    · rw [xiElt_one_zero_eq_mk]
      rfl
  have h := hU.unique h1 h2
  have := congrArg (fun q : DPMorphism _ _ => q y) h
  exact this

/-- **The comparison is a left inverse of the completed map back.** -/
public theorem alphaPCompletedEnvelopeToPrime_comp
    (y : alphaPCompletedPrimeDPRing s g lam) :
    alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam
        (alphaPCompletedPrimeToEnvelope hnone hsome hct hlam y) = y := by
  have hR : (alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam).toRingHom.comp
      (alphaPPrimeToCompleted hnone hsome hct hlam) =
      algebraMap (primeRing (envelopeCompletedDPRing s g) s.p lam)
        (alphaPCompletedPrimeDPRing s g lam) := by
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext
    · intro y
      change alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam
        (alphaPPrimeToCompleted hnone hsome hct hlam
          (AdjoinRoot.of (primePoly (envelopeCompletedDPRing s g) s.p lam) y)) = _
      rw [alphaPPrimeToCompleted, AdjoinRoot.lift_of]
      exact alphaPCompletedEnvelopeToPrime_xiToCompleted hg hnone hsome hct hlam y
    · change alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam
        (alphaPPrimeToCompleted hnone hsome hct hlam (zElt _ s.p lam)) = _
      rw [alphaPPrimeToCompleted_zElt, alphaPCompletedEnvelopeToPrime_root]
      rfl
  have h := ringHom_ext_pAdicCompletion s.p
    ((alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam).toRingHom.comp
      (alphaPCompletedPrimeToEnvelope hnone hsome hct hlam).toRingHom)
    (RingHom.id _) (fun x => by
      change alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam
        (alphaPCompletedPrimeToEnvelope hnone hsome hct hlam (AdicCompletion.of _ _ x)) = _
      rw [alphaPCompletedPrimeToEnvelope_of]
      exact RingHom.congr_fun hR x)
  exact RingHom.congr_fun h y

/-! ### The isomorphism -/

/-- **The completed envelope of the `α_p`-extension** ([Stacks, Tag 07Q9], proof): the
`p`-adically completed divided power envelope `D'` of `Ker(P' → C')` is isomorphic to the
`p`-adic completion of `D[z]⟨ξ⟩/(ξ - (z^p - λ))`. -/
public def alphaPCompletedEnvelopeEquiv :
    envelopeCompletedDPRing (alphaPSituation s c) g' ≃+* alphaPCompletedPrimeDPRing s g lam :=
  RingEquiv.ofRingHom (alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam).toRingHom
    (alphaPCompletedPrimeToEnvelope hnone hsome hct hlam).toRingHom
    (RingHom.ext (alphaPCompletedEnvelopeToPrime_comp hg hnone hsome hct hlam))
    (RingHom.ext (alphaPCompletedPrimeToEnvelope_comp hg hnone hsome hct hlam))

/-- The isomorphism is the comparison map. -/
public theorem alphaPCompletedEnvelopeEquiv_apply
    (x : envelopeCompletedDPRing (alphaPSituation s c) g') :
    alphaPCompletedEnvelopeEquiv hg hnone hsome hct hlam x =
      alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam x :=
  rfl

/-- The inverse of the isomorphism is the completed map back. -/
public theorem alphaPCompletedEnvelopeEquiv_symm_apply (y : alphaPCompletedPrimeDPRing s g lam) :
    (alphaPCompletedEnvelopeEquiv hg hnone hsome hct hlam).symm y =
      alphaPCompletedPrimeToEnvelope hnone hsome hct hlam y :=
  rfl

/-- The isomorphism is a divided power morphism. -/
public theorem isDPMorphism_alphaPCompletedEnvelopeEquiv :
    IsDPMorphism (envelopeCompletedDPRing (alphaPSituation s c) g').dividedPowers
      (alphaPCompletedPrimeDPRing s g lam).dividedPowers
      (alphaPCompletedEnvelopeEquiv hg hnone hsome hct hlam).toRingHom :=
  (alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam).isDPMorphism

/-- The inverse of the isomorphism is a divided power morphism. -/
public theorem isDPMorphism_alphaPCompletedEnvelopeEquiv_symm :
    IsDPMorphism (alphaPCompletedPrimeDPRing s g lam).dividedPowers
      (envelopeCompletedDPRing (alphaPSituation s c) g').dividedPowers
      (alphaPCompletedEnvelopeEquiv hg hnone hsome hct hlam).symm.toRingHom :=
  (alphaPCompletedPrimeToEnvelope hnone hsome hct hlam).isDPMorphism

/-- **The isomorphism is compatible with the structure maps from `D`**: on the image of
`D → D'` it is the structure map `D → (D[z]⟨ξ⟩/(ξ - (z^p - λ)))^∧`. -/
public theorem alphaPCompletedEnvelopeEquiv_envelopeMap (d : envelopeCompletedDPRing s g) :
    alphaPCompletedEnvelopeEquiv hg hnone hsome hct hlam (alphaPCompletedEnvelopeMap hsome d) =
      AdicCompletion.of _ _
        (algebraMap (envelopeCompletedDPRing s g)
          (primeRing (envelopeCompletedDPRing s g) s.p lam) d) :=
  alphaPCompletedEnvelopeToPrime_envelopeMap hg hnone hsome hct hlam d

/-- The isomorphism sends the class of `z` to the class of `z`. -/
public theorem alphaPCompletedEnvelopeEquiv_root :
    alphaPCompletedEnvelopeEquiv hg hnone hsome hct hlam (alphaPCompletedRoot s c g' e) =
      AdicCompletion.of _ _ (zElt (envelopeCompletedDPRing s g) s.p lam) :=
  alphaPCompletedEnvelopeToPrime_root hg hnone hsome hct hlam

/-- **The isomorphism of divided power rings** `D' ≅ (D[z]⟨ξ⟩/(ξ - (z^p - λ)))^∧`. -/
public def alphaPCompletedEnvelopeIso :
    envelopeCompletedDPRing (alphaPSituation s c) g' ≅ alphaPCompletedPrimeDPRing s g lam where
  hom := alphaPCompletedEnvelopeToPrime hg hnone hsome hct hlam
  inv := alphaPCompletedPrimeToEnvelope hnone hsome hct hlam
  hom_inv_id :=
    DPMorphism.ext <| funext <| alphaPCompletedPrimeToEnvelope_comp hg hnone hsome hct hlam
  inv_hom_id :=
    DPMorphism.ext <| funext <| alphaPCompletedEnvelopeToPrime_comp hg hnone hsome hct hlam

end Kernel

end Forward

end Crystalline

end

end
