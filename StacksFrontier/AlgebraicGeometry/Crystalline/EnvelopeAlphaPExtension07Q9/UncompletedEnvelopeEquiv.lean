module

public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeAlphaPExtension07Q9.CompletedEnvelopeEquiv

/-!
# The uncompleted envelope of an `α_p`-extension

The uncompleted form of the identification of the envelope of an `α_p`-extension in the proof of
[Stacks, Lemma 60.25.4, Tag 07Q9], its completion, the completed forms, and the same for degree
zero of the cosimplicial envelopes.

## Main definitions

* `Crystalline.alphaPEnvelopeDegreeZeroIso` — the isomorphism
  `Crystalline.alphaPCompletedEnvelopeIso` for degree zero of the cosimplicial envelopes
  `Crystalline.envelopeDPAlgebra` of `P → C` and of `P[z] → C'`.
* `Crystalline.alphaPEnvelopeEquiv₀` and `Crystalline.alphaPEnvelopeAlgEquiv₀` — the uncompleted
  form: the envelope `E'` of `Ker(P' → C')` is isomorphic, as a divided power ring and as an
  `A`-algebra, to `E[z]⟨ξ⟩/(ξ - (z^p - c̃))` for the uncompleted envelope `E` of `Ker(P → C)` and
  the image `c̃ ∈ E` of a lift of `c`.  This is the form to which the homotopy inverse of
  [Stacks, Tag 07N1] in `Crystalline.PthRootExtension` applies, its base being an uncompleted
  divided power ring.  `Crystalline.alphaPCompletedEnvelopeEquiv₀` is its completion
  `D' ≅ (E[z]⟨ξ⟩/(ξ - (z^p - c̃)))^∧`.
* `Crystalline.alphaPCompletedFormsIso₀` and `Crystalline.alphaPEnvelopeDegreeZeroFormsIso` — **the
  completed divided power forms of `D'` in every exterior degree are those of
  `E[z]⟨ξ⟩/(ξ - (z^p - c̃))`**, compatibly with the wedge products, the de Rham differentials and
  the universal differential, bundled as `Crystalline.CompletedFormsDPIso`, which is the input of
  the transport of completed de Rham complexes.

## References

* [Stacks Project, Lemma 60.25.4, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
-/

@[expose] public section

noncomputable section

open CategoryTheory DividedPowers

universe u v w

namespace Crystalline

/-! ### The uncompleted identification -/

section Uncompleted

open PthRootExtension MvPolynomial

variable {s : AffineCrystallineSituation.{u, v}} {c : s.C} {κ κ' : Type w}
  {g : MvPolynomial κ s.A →ₐ[s.A] s.C}
  {g' : MvPolynomial κ' s.A →ₐ[s.A] (alphaPSituation s c).C} {e : Option κ ≃ κ'}

variable (g) in
/-- The image `c̃ ∈ E` of a lift `c̃ ∈ P` of `c`. -/
public abbrev alphaPLift (ct : MvPolynomial κ s.A) : (polynomialDividedPowerEnvelope s g).object :=
  (polynomialDividedPowerEnvelope s g).algebraMap.toRingHom ct

variable (g) in
/-- The divided power morphism `A → E → E[z]⟨ξ⟩/(ξ - (z^p - c̃))` of the base. -/
public def alphaPBaseDP₀ (ct : MvPolynomial κ s.A) :
    DPMorphism s.A.dividedPowers (primeDividedPowers (polynomialDividedPowerEnvelope s g).object
      s.p (alphaPLift g ct) s.p_ne_zero) :=
  (alphaPAlgebraMapDP _ s.p _ s.p_ne_zero).comp (polynomialDividedPowerEnvelope s g).structureMap

variable (g) in
/-- The images of the variables of `P'` in `E[z]⟨ξ⟩/(ξ - (z^p - c̃))`. -/
public def alphaPVariableValue₀ (ct : MvPolynomial κ s.A) (o : Option κ) :
    primeRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct) :=
  o.elim (zElt _ s.p _) fun k =>
    algebraMap (polynomialDividedPowerEnvelope s g).object
      (primeRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct))
      ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom (X k))

variable (g e) in
/-- The ring map `P' → E[z]⟨ξ⟩/(ξ - (z^p - c̃))` sending `z` to `z`. -/
public def alphaPPolynomialMap₀ (ct : MvPolynomial κ s.A) :
    MvPolynomial κ' s.A →+* primeRing (polynomialDividedPowerEnvelope s g).object s.p
      (alphaPLift g ct) :=
  eval₂Hom (alphaPBaseDP₀ g ct).toRingHom fun j => alphaPVariableValue₀ g ct (e.symm j)

/-- The map `P' → E[z]⟨ξ⟩/⋯` on constants is the structure map of the base. -/
public theorem alphaPPolynomialMap₀_C (ct : MvPolynomial κ s.A) (a : s.A) :
    alphaPPolynomialMap₀ g e ct (C a) = alphaPBaseDP₀ g ct a :=
  eval₂Hom_C _ _ _

/-- The map `P' → E[z]⟨ξ⟩/⋯` on the variables. -/
public theorem alphaPPolynomialMap₀_X (ct : MvPolynomial κ s.A) (o : Option κ) :
    alphaPPolynomialMap₀ g e ct (X (e o)) = alphaPVariableValue₀ g ct o := by
  rw [alphaPPolynomialMap₀, eval₂Hom_X', Equiv.symm_apply_apply]

/-- On constants, the algebra map of the envelope is its structure map. -/
private theorem algebraMap_C_eq_structureMap (a : s.A) :
    (polynomialDividedPowerEnvelope s g).algebraMap.toRingHom (C a) =
      (polynomialDividedPowerEnvelope s g).structureMap a :=
  RingHom.congr_fun (polynomialDividedPowerEnvelope s g).algebraMap_comp a

/-- On the old variables, the map `P' → E[z]⟨ξ⟩/⋯` is `P → E → E[z]⟨ξ⟩/⋯`. -/
public theorem alphaPPolynomialMap₀_rename (ct x : MvPolynomial κ s.A) :
    alphaPPolynomialMap₀ g e ct (rename (e ∘ some) x) =
      algebraMap (polynomialDividedPowerEnvelope s g).object
        (primeRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct))
        ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom x) := by
  have h : (alphaPPolynomialMap₀ g e ct).comp (rename (e ∘ some)).toRingHom =
      (algebraMap (polynomialDividedPowerEnvelope s g).object
        (primeRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct))).comp
        (polynomialDividedPowerEnvelope s g).algebraMap.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        rename_C, alphaPPolynomialMap₀_C]
      rw [algebraMap_C_eq_structureMap]
      rfl
    · intro k
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X,
        Function.comp_apply, alphaPPolynomialMap₀_X]
      rfl
  exact RingHom.congr_fun h x

variable (hg : Function.Surjective g) (hnone : g' (X (e none)) = alphaPRoot s c)
  (hsome : ∀ k, g' (X (e (some k))) = algebraMap s.C (alphaPSituation s c).C (g (X k)))
  {ct : MvPolynomial κ s.A} (hct : g ct = c)

/-- The reduction `P → E → E[z]⟨ξ⟩/⋯ → (E[z]⟨ξ⟩/⋯)/J'`. -/
private def reductionOfP₀ (ct : MvPolynomial κ s.A) :
    MvPolynomial κ s.A →+* primeRing (polynomialDividedPowerEnvelope s g).object s.p
        (alphaPLift g ct) ⧸ primeIdeal (polynomialDividedPowerEnvelope s g).object s.p
        (alphaPLift g ct) :=
  (Ideal.Quotient.mk _).comp ((algebraMap (polynomialDividedPowerEnvelope s g).object
    (primeRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct))).comp
    (polynomialDividedPowerEnvelope s g).algebraMap.toRingHom)

private theorem reductionOfP₀_eq_zero (ct x : MvPolynomial κ s.A) (hx : g x = 0) :
    reductionOfP₀ (g := g) ct x = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have h1 := (polynomialDividedPowerEnvelope s g).algebraMap.ideal_comp
    (Ideal.mem_map_of_mem _ (show x ∈ RingHom.ker g.toRingHom from hx))
  exact (alphaPAlgebraMapDP _ s.p (alphaPLift g ct) s.p_ne_zero).ideal_comp
    (Ideal.mem_map_of_mem _ h1)

/-- The reduction `C → (E[z]⟨ξ⟩/⋯)/J'`. -/
private def reductionOfC₀ (ct : MvPolynomial κ s.A) :
    s.C →+* primeRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct) ⧸
      primeIdeal (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct) :=
  (Ideal.Quotient.lift (RingHom.ker g.toRingHom) (reductionOfP₀ (g := g) ct)
    fun x hx => reductionOfP₀_eq_zero ct x hx).comp
    (RingHom.quotientKerEquivOfSurjective (f := g.toRingHom) hg).symm.toRingHom

private theorem reductionOfC₀_apply (ct x : MvPolynomial κ s.A) :
    reductionOfC₀ hg ct (g x) = reductionOfP₀ (g := g) ct x := by
  show Ideal.Quotient.lift (RingHom.ker g.toRingHom) (reductionOfP₀ (g := g) ct)
    (fun x hx => reductionOfP₀_eq_zero ct x hx)
    ((RingHom.quotientKerEquivOfSurjective (f := g.toRingHom) hg).symm (g.toRingHom x)) = _
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.lift_mk]

include hct in
private theorem reductionOfC₀_relation :
    Polynomial.eval₂RingHom (reductionOfC₀ hg ct)
        (Ideal.Quotient.mk _ (zElt _ s.p (alphaPLift g ct)))
        (Polynomial.X ^ s.p - Polynomial.C c : Polynomial s.C) = 0 := by
  subst hct
  rw [map_sub, map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.eval₂_C,
    reductionOfC₀_apply, reductionOfP₀, ← map_pow, zElt_pow_prime, xiElt_zero_zero,
    Algebra.smul_def, mul_one]
  simp only [RingHom.comp_apply]
  rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem, add_sub_cancel_right]
  exact xiElt_one_zero_mem _ s.p _ s.p_ne_zero

/-- The reduction `C' → (E[z]⟨ξ⟩/⋯)/J'` sending `z` to `z`. -/
private def reductionOfC'₀ :
    (alphaPSituation s c).C →+* primeRing (polynomialDividedPowerEnvelope s g).object s.p
        (alphaPLift g ct) ⧸ primeIdeal (polynomialDividedPowerEnvelope s g).object s.p
        (alphaPLift g ct) :=
  Ideal.Quotient.lift _ (Polynomial.eval₂RingHom (reductionOfC₀ hg ct)
      (Ideal.Quotient.mk _ (zElt _ s.p _))) fun x hx => by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, reductionOfC₀_relation hg hct, mul_zero]

private theorem reductionOfC'₀_algebraMap (x : s.C) :
    reductionOfC'₀ hg hct (algebraMap s.C (alphaPSituation s c).C x) = reductionOfC₀ hg ct x := by
  show Ideal.Quotient.lift _ (Polynomial.eval₂RingHom (reductionOfC₀ hg ct)
      (Ideal.Quotient.mk _ (zElt _ s.p _))) _ (Ideal.Quotient.mk _ (Polynomial.C x)) = _
  rw [Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]

private theorem reductionOfC'₀_root :
    reductionOfC'₀ hg hct (alphaPRoot s c) =
      Ideal.Quotient.mk _ (zElt (polynomialDividedPowerEnvelope s g).object s.p
        (alphaPLift g ct)) := by
  show Ideal.Quotient.lift _ (Polynomial.eval₂RingHom (reductionOfC₀ hg ct)
      (Ideal.Quotient.mk _ (zElt _ s.p _))) _ (Ideal.Quotient.mk _ Polynomial.X) = _
  rw [Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

private theorem reductionOfC'₀_comp_C (a : s.A) :
    Ideal.Quotient.mk _ (alphaPPolynomialMap₀ g e ct (C a)) = reductionOfC'₀ hg hct (g' (C a)) := by
  rw [show g' (C a) = algebraMap s.C (alphaPSituation s c).C (g (C a)) by
      rw [show g (C a) = algebraMap s.A s.C a from g.commutes a,
        show g' (C a) = algebraMap s.A (alphaPSituation s c).C a from g'.commutes a]
      rfl,
    reductionOfC'₀_algebraMap, reductionOfC₀_apply, alphaPPolynomialMap₀_C, reductionOfP₀,
    RingHom.comp_apply, RingHom.comp_apply, algebraMap_C_eq_structureMap]
  rfl

include hnone hsome in
private theorem reductionOfC'₀_comp (x : MvPolynomial κ' s.A) :
    Ideal.Quotient.mk _ (alphaPPolynomialMap₀ g e ct x) = reductionOfC'₀ hg hct (g' x) := by
  have h : (Ideal.Quotient.mk _).comp (alphaPPolynomialMap₀ g e ct) =
      (reductionOfC'₀ hg hct).comp g'.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      exact reductionOfC'₀_comp_C hg hct a
    · intro j
      obtain ⟨o, rfl⟩ := e.surjective j
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        alphaPPolynomialMap₀_X]
      cases o with
      | none =>
        rw [hnone, reductionOfC'₀_root]
        rfl
      | some k =>
        rw [hsome k, reductionOfC'₀_algebraMap, reductionOfC₀_apply]
        rfl
  exact RingHom.congr_fun h x

include hg hnone hsome hct in
/-- The map `P' → E[z]⟨ξ⟩/(ξ - (z^p - c̃))` carries the kernel of `P' → C'` into `J'`. -/
public theorem alphaPPolynomialMap₀_ker_le :
    (RingHom.ker g'.toRingHom).map (alphaPPolynomialMap₀ g e ct) ≤
      primeIdeal (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  show alphaPPolynomialMap₀ g e ct x ∈
    primeIdeal (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct)
  rw [← Ideal.Quotient.eq_zero_iff_mem, reductionOfC'₀_comp hg hnone hsome hct,
    show g' x = 0 from hx, map_zero]

/-- **The divided power morphism `E' → E[z]⟨ξ⟩/(ξ - (z^p - c̃))`.** -/
public def alphaPEnvelopeToPrime₀ :
    DPMorphism (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object.dividedPowers
      (primeDividedPowers (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct)
        s.p_ne_zero) :=
  (polynomialDividedPowerEnvelope (alphaPSituation s c) g').liftDP
    (primeDPRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct) s.p_ne_zero)
    (alphaPBaseDP₀ g ct) (alphaPPolynomialMap₀ g e ct)
    (alphaPPolynomialMap₀_ker_le hg hnone hsome hct)
    (by
      ext a
      exact alphaPPolynomialMap₀_C ct a)

/-- The map `E' → E[z]⟨ξ⟩/⋯` restricts to `Crystalline.alphaPPolynomialMap₀` on `P'`. -/
public theorem alphaPEnvelopeToPrime₀_algebraMap (x : MvPolynomial κ' s.A) :
    alphaPEnvelopeToPrime₀ hg hnone hsome hct
        ((polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom x) =
      alphaPPolynomialMap₀ g e ct x :=
  DividedPowerEnvelope.liftDP_algebraMap _ _ _ _ _ _ x

/-- The map `E' → E[z]⟨ξ⟩/⋯` is a map over the base. -/
public theorem alphaPEnvelopeToPrime₀_structureMap (a : s.A) :
    alphaPEnvelopeToPrime₀ hg hnone hsome hct
        ((polynomialDividedPowerEnvelope (alphaPSituation s c) g').structureMap a) =
      alphaPBaseDP₀ g ct a :=
  congrArg (fun q : DPMorphism _ _ => q a)
    (DividedPowerEnvelope.liftDP_comp_structureMap _ _ _ _ _ _)

/-- On `E`, the map `E → E' → E[z]⟨ξ⟩/⋯` is the structure map. -/
public theorem alphaPEnvelopeToPrime₀_envelopeMap
    (x : (polynomialDividedPowerEnvelope s g).object) :
    alphaPEnvelopeToPrime₀ hg hnone hsome hct (alphaPEnvelopeMap hsome x) =
      algebraMap (polynomialDividedPowerEnvelope s g).object
        (primeRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct)) x := by
  have h := (polynomialDividedPowerEnvelope s g).dpMorphism_ext
    (T := primeDPRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct)
      s.p_ne_zero)
    ((alphaPEnvelopeToPrime₀ hg hnone hsome hct).comp (alphaPEnvelopeMap hsome))
    (alphaPAlgebraMapDP _ s.p (alphaPLift g ct) s.p_ne_zero) (fun y => by
      show alphaPEnvelopeToPrime₀ hg hnone hsome hct (alphaPEnvelopeMap hsome
        ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom y)) = _
      rw [alphaPEnvelopeMap_algebraMap, alphaPEnvelopeToPrime₀_algebraMap,
        alphaPPolynomialMap₀_rename]
      rfl)
  exact congrArg (fun q : DPMorphism _ _ => q x) h

/-! #### The map back -/

include hnone hsome hct in
/-- `z^p - c̃` lies in the divided power ideal of `E'`. -/
public theorem alphaPRoot_pow_sub_mem₀ :
    (polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom
        (X (e none) ^ s.p - rename (e ∘ some) ct) ∈
      (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object.ideal := by
  refine (polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.ideal_comp
    (Ideal.mem_map_of_mem _ ?_)
  show g' (X (e none) ^ s.p - rename (e ∘ some) ct) = 0
  rw [map_sub, map_pow, hnone, alphaP_rename_mem_ker hsome, hct, alphaPRoot]
  show Ideal.Quotient.mk _ (Polynomial.X ^ s.p) - Ideal.Quotient.mk _ (Polynomial.C c) = 0
  rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

/-- The divided power morphism `E⟨ξ⟩ → E'` sending `ξ` to `z^p - c̃`. -/
public def xiToEnvelope₀ :
    DPMorphism (xiDPRing (polynomialDividedPowerEnvelope s g).object).dividedPowers
      (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object.dividedPowers :=
  (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial
    (polynomialDividedPowerEnvelope s g).object Unit
    (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object
    (alphaPEnvelopeMap hsome) (fun _ => ⟨_, alphaPRoot_pow_sub_mem₀ hnone hsome hct⟩)).exists.choose

/-- The map `E⟨ξ⟩ → E'` extends `E → E'` and sends `ξ` to `z^p - c̃`. -/
public theorem xiToEnvelope₀_spec :
    (xiToEnvelope₀ hnone hsome hct).comp
        (setIndexedDividedPowerPolynomialCoefficientDPMorphism _ Unit) =
      alphaPEnvelopeMap hsome ∧
    xiToEnvelope₀ hnone hsome hct (xi (polynomialDividedPowerEnvelope s g).object) =
      (polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom
        (X (e none) ^ s.p - rename (e ∘ some) ct) :=
  let h := (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial
    (polynomialDividedPowerEnvelope s g).object Unit
    (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object
    (alphaPEnvelopeMap hsome)
    (fun _ => ⟨_, alphaPRoot_pow_sub_mem₀ hnone hsome hct⟩)).exists.choose_spec
  ⟨h.1, h.2 ()⟩

/-- The map `E⟨ξ⟩ → E'` extends `E → E'`. -/
public theorem xiToEnvelope₀_algebraMap (d : (polynomialDividedPowerEnvelope s g).object) :
    xiToEnvelope₀ hnone hsome hct
        (algebraMap _ (XiAlg (polynomialDividedPowerEnvelope s g).object) d) =
      alphaPEnvelopeMap hsome d :=
  congrArg (fun q : DPMorphism _ _ => q d) (xiToEnvelope₀_spec hnone hsome hct).1

/-- The relation `z^p - ξ - c̃` holds for `z` and `z^p - c̃` in `E'`. -/
public theorem xiToEnvelope₀_eval₂_primePoly :
    (primePoly (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct)).eval₂
      (xiToEnvelope₀ hnone hsome hct).toRingHom
      ((polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom
        (X (e none))) = 0 := by
  rw [primePoly, Polynomial.eval₂_sub, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_C]
  show _ - xiToEnvelope₀ hnone hsome hct (xi _) -
    xiToEnvelope₀ hnone hsome hct (algebraMap _ _ (alphaPLift g ct)) = 0
  rw [(xiToEnvelope₀_spec hnone hsome hct).2, xiToEnvelope₀_algebraMap,
    alphaPLift, alphaPEnvelopeMap_algebraMap, map_sub, map_pow]
  ring

/-- **The ring map `E[z]⟨ξ⟩/(ξ - (z^p - c̃)) → E'`** sending `z` to `z`. -/
public def alphaPPrimeToEnvelope₀ :
    primeRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct) →+*
      (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object :=
  AdjoinRoot.lift (xiToEnvelope₀ hnone hsome hct).toRingHom
    ((polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom (X (e none)))
    (xiToEnvelope₀_eval₂_primePoly hnone hsome hct)

/-- The map back sends `z` to the class of `z`. -/
public theorem alphaPPrimeToEnvelope₀_zElt :
    alphaPPrimeToEnvelope₀ hnone hsome hct (zElt _ s.p (alphaPLift g ct)) =
      (polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom
        (X (e none)) :=
  AdjoinRoot.lift_root _

/-- The structure map `E → E[z]⟨ξ⟩/⋯` factors through `E⟨ξ⟩`. -/
private theorem algebraMap_primeRing_eq_of (d : (polynomialDividedPowerEnvelope s g).object) :
    algebraMap (polynomialDividedPowerEnvelope s g).object
        (primeRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct)) d =
      AdjoinRoot.of _ (algebraMap _ (XiAlg (polynomialDividedPowerEnvelope s g).object) d) := by
  rw [IsScalarTower.algebraMap_apply (polynomialDividedPowerEnvelope s g).object
    (XiAlg (polynomialDividedPowerEnvelope s g).object)
    (primeRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct)),
    AdjoinRoot.algebraMap_eq]

/-- The map back extends `E → E'`. -/
public theorem alphaPPrimeToEnvelope₀_algebraMap (d : (polynomialDividedPowerEnvelope s g).object) :
    alphaPPrimeToEnvelope₀ hnone hsome hct
        (algebraMap _ (primeRing (polynomialDividedPowerEnvelope s g).object s.p
          (alphaPLift g ct)) d) =
      alphaPEnvelopeMap hsome d := by
  rw [algebraMap_primeRing_eq_of, alphaPPrimeToEnvelope₀, AdjoinRoot.lift_of]
  exact xiToEnvelope₀_algebraMap hnone hsome hct d

/-- The map back is a divided power morphism. -/
public theorem alphaPPrimeToEnvelope₀_isDPMorphism :
    IsDPMorphism (primeDividedPowers (polynomialDividedPowerEnvelope s g).object s.p
        (alphaPLift g ct) s.p_ne_zero)
      (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object.dividedPowers
      (alphaPPrimeToEnvelope₀ hnone hsome hct) := by
  have h0 : IsDPMorphism (zPolyDPRing (polynomialDividedPowerEnvelope s g).object).dividedPowers
      (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object.dividedPowers
      (Polynomial.eval₂RingHom (xiToEnvelope₀ hnone hsome hct).toRingHom
        ((polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom
          (X (e none)))) :=
    IsDPMorphism.of_comp
      (hI := (xiDPRing (polynomialDividedPowerEnvelope s g).object).dividedPowers)
      (hJ := (zPolyDPRing (polynomialDividedPowerEnvelope s g).object).dividedPowers)
      (hK := (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object.dividedPowers)
      Polynomial.C _ rfl (isDPMorphism_C_polynomialDividedPowerRing _)
      (by
        convert (xiToEnvelope₀ hnone hsome hct).isDPMorphism using 1
        exact RingHom.ext fun x => Polynomial.eval₂_C _ _)
  refine IsDPMorphism.of_comp
    (hI := (zPolyDPRing (polynomialDividedPowerEnvelope s g).object).dividedPowers)
    (hJ := primeDividedPowers (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct)
      s.p_ne_zero)
    (hK := (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object.dividedPowers)
    (relationQuotientMk _ s.p _) _ rfl (isDPMorphism_relationQuotientMk _ s.p _ s.p_ne_zero) ?_
  convert h0 using 1
  exact RingHom.ext fun x =>
    AdjoinRoot.lift_mk (xiToEnvelope₀_eval₂_primePoly hnone hsome hct) x

/-! #### The two composites -/

/-- **The map back is a left inverse of `E' → E[z]⟨ξ⟩/⋯`.** -/
public theorem alphaPPrimeToEnvelope₀_comp
    (x : (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object) :
    alphaPPrimeToEnvelope₀ hnone hsome hct (alphaPEnvelopeToPrime₀ hg hnone hsome hct x) = x := by
  have hP : (alphaPPrimeToEnvelope₀ hnone hsome hct).comp (alphaPPolynomialMap₀ g e ct) =
      (polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, alphaPPolynomialMap₀_C]
      show alphaPPrimeToEnvelope₀ hnone hsome hct
        (algebraMap (polynomialDividedPowerEnvelope s g).object _
          ((polynomialDividedPowerEnvelope s g).structureMap a)) = _
      rw [alphaPPrimeToEnvelope₀_algebraMap, alphaPEnvelopeMap_structureMap]
      exact (algebraMap_C_eq_structureMap (s := alphaPSituation s c) (g := g') a).symm
    · intro j
      obtain ⟨o, rfl⟩ := e.surjective j
      simp only [RingHom.comp_apply, alphaPPolynomialMap₀_X]
      cases o with
      | none =>
        show alphaPPrimeToEnvelope₀ hnone hsome hct (zElt _ s.p _) = _
        rw [alphaPPrimeToEnvelope₀_zElt]
      | some k =>
        show alphaPPrimeToEnvelope₀ hnone hsome hct
          (algebraMap (polynomialDividedPowerEnvelope s g).object _
            ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom (X k))) = _
        rw [alphaPPrimeToEnvelope₀_algebraMap, alphaPEnvelopeMap_algebraMap, rename_X]
        rfl
  have h := (polynomialDividedPowerEnvelope (alphaPSituation s c) g').dpMorphism_ext
    (T := (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object)
    ((DPMorphism.mk' (alphaPPrimeToEnvelope₀_isDPMorphism hnone hsome hct)).comp
      (alphaPEnvelopeToPrime₀ hg hnone hsome hct))
    (DPMorphism.id _) (fun y => by
      show alphaPPrimeToEnvelope₀ hnone hsome hct (alphaPEnvelopeToPrime₀ hg hnone hsome hct
        ((polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom y)) = _
      rw [alphaPEnvelopeToPrime₀_algebraMap]
      exact RingHom.congr_fun hP y)
  exact congrArg (fun q : DPMorphism _ _ => q x) h

/-- **`E' → E[z]⟨ξ⟩/⋯` is a left inverse of the map back.** -/
public theorem alphaPEnvelopeToPrime₀_comp
    (y : primeRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct)) :
    alphaPEnvelopeToPrime₀ hg hnone hsome hct (alphaPPrimeToEnvelope₀ hnone hsome hct y) = y := by
  have hxi : ∀ y : XiAlg (polynomialDividedPowerEnvelope s g).object,
      alphaPEnvelopeToPrime₀ hg hnone hsome hct (xiToEnvelope₀ hnone hsome hct y) =
        AdjoinRoot.of _ y := by
    have hU := existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial
      (polynomialDividedPowerEnvelope s g).object Unit
      (primeDPRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct) s.p_ne_zero)
      ((alphaPEnvelopeToPrime₀ hg hnone hsome hct).comp (alphaPEnvelopeMap hsome))
      (fun _ => ⟨_, xiElt_one_zero_mem _ s.p (alphaPLift g ct) s.p_ne_zero⟩)
    have h1 : ((alphaPEnvelopeToPrime₀ hg hnone hsome hct).comp
        (xiToEnvelope₀ hnone hsome hct)).comp
          (setIndexedDividedPowerPolynomialCoefficientDPMorphism _ Unit) =
        (alphaPEnvelopeToPrime₀ hg hnone hsome hct).comp (alphaPEnvelopeMap hsome) ∧
        ∀ i : Unit, ((alphaPEnvelopeToPrime₀ hg hnone hsome hct).comp
          (xiToEnvelope₀ hnone hsome hct)) (dividedPowerPolynomialVariable _ i) =
          xiElt (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct) 1 0 := by
      refine ⟨?_, fun _ => ?_⟩
      · apply DPMorphism.ext
        funext d
        show alphaPEnvelopeToPrime₀ hg hnone hsome hct
          (xiToEnvelope₀ hnone hsome hct (algebraMap _ _ d)) = _
        rw [xiToEnvelope₀_algebraMap]
        rfl
      · show alphaPEnvelopeToPrime₀ hg hnone hsome hct
          (xiToEnvelope₀ hnone hsome hct (xi _)) = _
        have hm := map_sub (alphaPEnvelopeToPrime₀ hg hnone hsome hct).toRingHom
          ((polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom
            (X (e none) ^ s.p))
          ((polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom
            (rename (e ∘ some) ct))
        simp only [DPMorphism.toRingHom_apply] at hm
        rw [(xiToEnvelope₀_spec hnone hsome hct).2, map_sub, hm,
          alphaPEnvelopeToPrime₀_algebraMap, alphaPEnvelopeToPrime₀_algebraMap, map_pow,
          alphaPPolynomialMap₀_X, alphaPPolynomialMap₀_rename, xiElt_one_zero, xi_eq,
          algebraMap_primeRing_eq_of]
        rfl
    have h2 : ((DPMorphism.mk' (isDPMorphism_relationQuotientMk _ s.p _ s.p_ne_zero)).comp
        (DPMorphism.mk' (isDPMorphism_C_polynomialDividedPowerRing
          (xiDPRing (polynomialDividedPowerEnvelope s g).object)))).comp
          (setIndexedDividedPowerPolynomialCoefficientDPMorphism _ Unit) =
        (alphaPEnvelopeToPrime₀ hg hnone hsome hct).comp (alphaPEnvelopeMap hsome) ∧
        ∀ i : Unit, ((DPMorphism.mk' (isDPMorphism_relationQuotientMk _ s.p _ s.p_ne_zero)).comp
          (DPMorphism.mk' (isDPMorphism_C_polynomialDividedPowerRing
            (xiDPRing (polynomialDividedPowerEnvelope s g).object))))
            (dividedPowerPolynomialVariable _ i) =
          xiElt (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct) 1 0 := by
      refine ⟨?_, fun _ => ?_⟩
      · apply DPMorphism.ext
        funext d
        show _ = alphaPEnvelopeToPrime₀ hg hnone hsome hct (alphaPEnvelopeMap hsome d)
        rw [alphaPEnvelopeToPrime₀_envelopeMap]
        rfl
      · rw [xiElt_one_zero_eq_mk]
        rfl
    intro y
    exact congrArg (fun q : DPMorphism _ _ => q y) (hU.unique h1 h2)
  have hR : (alphaPEnvelopeToPrime₀ hg hnone hsome hct).toRingHom.comp
      (alphaPPrimeToEnvelope₀ hnone hsome hct) = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext
    · intro y
      show alphaPEnvelopeToPrime₀ hg hnone hsome hct
        (alphaPPrimeToEnvelope₀ hnone hsome hct (AdjoinRoot.of _ y)) = AdjoinRoot.of _ y
      rw [alphaPPrimeToEnvelope₀, AdjoinRoot.lift_of]
      exact hxi y
    · show alphaPEnvelopeToPrime₀ hg hnone hsome hct
        (alphaPPrimeToEnvelope₀ hnone hsome hct (zElt _ s.p _)) = zElt _ s.p _
      rw [alphaPPrimeToEnvelope₀_zElt, alphaPEnvelopeToPrime₀_algebraMap,
        alphaPPolynomialMap₀_X]
      rfl
  exact RingHom.congr_fun hR y

/-! #### The completion of the uncompleted identification -/

/-- `p` is nilpotent modulo `J'` in `E[z]⟨ξ⟩/(ξ - (z^p - c̃))`. -/
public theorem alphaPPrime₀_isNilpotent :
    IsNilpotent (Ideal.Quotient.mk (primeDPRing (polynomialDividedPowerEnvelope s g).object s.p
        (alphaPLift g ct) s.p_ne_zero).ideal
      ((s.p : ℕ) : primeDPRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct)
        s.p_ne_zero)) :=
  alphaP_isNilpotent_mk_primeIdeal _ s.p _ s.p_ne_zero
    (polynomialDividedPowerEnvelope_prime_nilpotent s g)

/-- **The completion `D' ≅ (E[z]⟨ξ⟩/(ξ - (z^p - c̃)))^∧` of the uncompleted identification**, a
ring isomorphism which is a divided power morphism in both directions
(`Crystalline.isDPMorphism_alphaPCompletedEnvelopeEquiv₀`,
`Crystalline.isDPMorphism_alphaPCompletedEnvelopeEquiv₀_symm`). -/
public def alphaPCompletedEnvelopeEquiv₀ :
    envelopeCompletedDPRing (alphaPSituation s c) g' ≃+*
      pAdicCompletedDPRing (primeDPRing (polynomialDividedPowerEnvelope s g).object s.p
        (alphaPLift g ct) s.p_ne_zero) s.p (alphaPPrime₀_isNilpotent (g := g) (ct := ct)) :=
  RingEquiv.ofRingHom
    (adicCompletionRingMap (alphaPEnvelopeToPrime₀ hg hnone hsome hct).toRingHom
      (map_pAdicIdeal_le _ _))
    (adicCompletionRingMap (alphaPPrimeToEnvelope₀ hnone hsome hct) (map_pAdicIdeal_le _ _))
    (ringHom_ext_pAdicCompletion s.p _ _ fun y => by
      rw [RingHom.comp_apply, adicCompletionRingMap_of, adicCompletionRingMap_of]
      change AdicCompletion.of _ _ (alphaPEnvelopeToPrime₀ hg hnone hsome hct
        (alphaPPrimeToEnvelope₀ hnone hsome hct y)) = _
      rw [alphaPEnvelopeToPrime₀_comp]
      rfl)
    (ringHom_ext_pAdicCompletion s.p _ _ fun x => by
      rw [RingHom.comp_apply, adicCompletionRingMap_of, adicCompletionRingMap_of]
      change AdicCompletion.of _ _ (alphaPPrimeToEnvelope₀ hnone hsome hct
        (alphaPEnvelopeToPrime₀ hg hnone hsome hct x)) = _
      rw [alphaPPrimeToEnvelope₀_comp]
      rfl)

/-- The completed identification is the completion of the uncompleted one. -/
public theorem alphaPCompletedEnvelopeEquiv₀_of
    (x : (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object) :
    alphaPCompletedEnvelopeEquiv₀ hg hnone hsome hct (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _ (alphaPEnvelopeToPrime₀ hg hnone hsome hct x) :=
  adicCompletionRingMap_of _ _ x

/-- The completion of the uncompleted identification is a divided power morphism. -/
public theorem isDPMorphism_alphaPCompletedEnvelopeEquiv₀ :
    IsDPMorphism (envelopeCompletedDPRing (alphaPSituation s c) g').dividedPowers
      (pAdicCompletedDPRing (primeDPRing (polynomialDividedPowerEnvelope s g).object s.p
        (alphaPLift g ct) s.p_ne_zero) s.p
        (alphaPPrime₀_isNilpotent (g := g) (ct := ct))).dividedPowers
      (alphaPCompletedEnvelopeEquiv₀ hg hnone hsome hct).toRingHom :=
  adicCompletionRingMap_isDPMorphism _ _ s.p _ _ (alphaPEnvelopeToPrime₀ hg hnone hsome hct)

/-- The inverse of the completion of the uncompleted identification is a divided power
morphism. -/
public theorem isDPMorphism_alphaPCompletedEnvelopeEquiv₀_symm :
    IsDPMorphism
      (pAdicCompletedDPRing (primeDPRing (polynomialDividedPowerEnvelope s g).object s.p
        (alphaPLift g ct) s.p_ne_zero) s.p
        (alphaPPrime₀_isNilpotent (g := g) (ct := ct))).dividedPowers
      (envelopeCompletedDPRing (alphaPSituation s c) g').dividedPowers
      (alphaPCompletedEnvelopeEquiv₀ hg hnone hsome hct).symm.toRingHom :=
  adicCompletionRingMap_isDPMorphism _ _ s.p _ _
    (DPMorphism.mk' (alphaPPrimeToEnvelope₀_isDPMorphism hnone hsome hct))

/-- The completion of the uncompleted identification is compatible with the structure maps from
`D`: `D → D' → (E[z]⟨ξ⟩/⋯)^∧` is the completion of `E → E[z]⟨ξ⟩/⋯`. -/
public theorem alphaPCompletedEnvelopeEquiv₀_envelopeMap (d : envelopeCompletedDPRing s g) :
    alphaPCompletedEnvelopeEquiv₀ hg hnone hsome hct (alphaPCompletedEnvelopeMap hsome d) =
      adicCompletionRingMap (algebraMap (polynomialDividedPowerEnvelope s g).object
        (primeRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct)))
        (map_pAdicIdeal_le _ _) d := by
  have h := ringHom_ext_pAdicCompletion s.p
    ((alphaPCompletedEnvelopeEquiv₀ hg hnone hsome hct).toRingHom.comp
      (alphaPCompletedEnvelopeMap hsome).toRingHom)
    (adicCompletionRingMap (algebraMap (polynomialDividedPowerEnvelope s g).object
        (primeRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct)))
        (map_pAdicIdeal_le _ _)) (fun x => by
      show alphaPCompletedEnvelopeEquiv₀ hg hnone hsome hct
        (alphaPCompletedEnvelopeMap hsome (AdicCompletion.of _ _ x)) = _
      rw [alphaPCompletedEnvelopeMap_of, alphaPCompletedEnvelopeEquiv₀_of,
        alphaPEnvelopeToPrime₀_envelopeMap, adicCompletionRingMap_of])
  exact RingHom.congr_fun h d

/-! #### The identification as `A`-algebras, and of the completed forms -/

/-- **The uncompleted identification `E' ≅ E[z]⟨ξ⟩/(ξ - (z^p - c̃))`**, as a ring isomorphism. -/
public def alphaPEnvelopeEquiv₀ :
    (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object ≃+*
      primeRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct) :=
  RingEquiv.ofRingHom (alphaPEnvelopeToPrime₀ hg hnone hsome hct).toRingHom
    (alphaPPrimeToEnvelope₀ hnone hsome hct)
    (RingHom.ext (alphaPEnvelopeToPrime₀_comp hg hnone hsome hct))
    (RingHom.ext (alphaPPrimeToEnvelope₀_comp hg hnone hsome hct))

/-- The uncompleted identification is the map `E' → E[z]⟨ξ⟩/⋯`. -/
public theorem alphaPEnvelopeEquiv₀_apply
    (x : (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object) :
    alphaPEnvelopeEquiv₀ hg hnone hsome hct x = alphaPEnvelopeToPrime₀ hg hnone hsome hct x :=
  rfl

/-- The inverse of the uncompleted identification is the map back. -/
public theorem alphaPEnvelopeEquiv₀_symm_apply
    (y : primeRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct)) :
    (alphaPEnvelopeEquiv₀ hg hnone hsome hct).symm y = alphaPPrimeToEnvelope₀ hnone hsome hct y :=
  rfl

/-- The uncompleted identification is a divided power morphism. -/
public theorem isDPMorphism_alphaPEnvelopeEquiv₀ :
    IsDPMorphism (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object.dividedPowers
      (primeDividedPowers (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct)
        s.p_ne_zero)
      (alphaPEnvelopeEquiv₀ hg hnone hsome hct).toRingHom :=
  (alphaPEnvelopeToPrime₀ hg hnone hsome hct).isDPMorphism

/-- The inverse of the uncompleted identification is a divided power morphism. -/
public theorem isDPMorphism_alphaPEnvelopeEquiv₀_symm :
    IsDPMorphism (primeDividedPowers (polynomialDividedPowerEnvelope s g).object s.p
        (alphaPLift g ct) s.p_ne_zero)
      (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object.dividedPowers
      (alphaPEnvelopeEquiv₀ hg hnone hsome hct).symm.toRingHom :=
  alphaPPrimeToEnvelope₀_isDPMorphism hnone hsome hct

/-- The uncompleted identification is compatible with the structure maps from `E`. -/
public theorem alphaPEnvelopeEquiv₀_envelopeMap (x : (polynomialDividedPowerEnvelope s g).object) :
    alphaPEnvelopeEquiv₀ hg hnone hsome hct (alphaPEnvelopeMap hsome x) =
      algebraMap (polynomialDividedPowerEnvelope s g).object
        (primeRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct)) x :=
  alphaPEnvelopeToPrime₀_envelopeMap hg hnone hsome hct x

/-- The uncompleted identification sends the class of `z` to `z`. -/
public theorem alphaPEnvelopeEquiv₀_root :
    alphaPEnvelopeEquiv₀ hg hnone hsome hct
        ((polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom
          (X (e none))) =
      zElt (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct) := by
  rw [alphaPEnvelopeEquiv₀_apply, alphaPEnvelopeToPrime₀_algebraMap, alphaPPolynomialMap₀_X]
  rfl

variable [Algebra s.A (polynomialDividedPowerEnvelope s g).object]
  [Algebra s.A (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object]

/-- **The uncompleted identification as an isomorphism of `A`-algebras**, for the algebra
structures given by the structure maps of the two envelopes. -/
public def alphaPEnvelopeAlgEquiv₀
    (hA : ∀ a, algebraMap s.A (polynomialDividedPowerEnvelope s g).object a =
      (polynomialDividedPowerEnvelope s g).structureMap a)
    (hA' : ∀ a, algebraMap s.A (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object a =
      (polynomialDividedPowerEnvelope (alphaPSituation s c) g').structureMap a) :
    (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object ≃ₐ[s.A]
      primeRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct) :=
  AlgEquiv.ofRingEquiv (f := alphaPEnvelopeEquiv₀ hg hnone hsome hct) fun a => by
    rw [hA', alphaPEnvelopeEquiv₀_apply, alphaPEnvelopeToPrime₀_structureMap,
      IsScalarTower.algebraMap_apply s.A (polynomialDividedPowerEnvelope s g).object
        (primeRing (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct)), hA]
    rfl

/-- **The completed divided power forms of `E'` and of `E[z]⟨ξ⟩/(ξ - (z^p - c̃))` agree**, in
every exterior degree, compatibly with the wedge products, the de Rham differentials and the
universal differential: the bundle `Crystalline.CompletedFormsDPIso` of the uncompleted divided
power identification. -/
public def alphaPCompletedFormsIso₀
    (hA : ∀ a, algebraMap s.A (polynomialDividedPowerEnvelope s g).object a =
      (polynomialDividedPowerEnvelope s g).structureMap a)
    (hA' : ∀ a, algebraMap s.A (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object a =
      (polynomialDividedPowerEnvelope (alphaPSituation s c) g').structureMap a) :
    CompletedFormsDPIso s.p s.A
      (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object.dividedPowers
      (primeDividedPowers (polynomialDividedPowerEnvelope s g).object s.p (alphaPLift g ct)
        s.p_ne_zero) :=
  completedFormsDPIso s.p s.A _ _ (alphaPEnvelopeAlgEquiv₀ hg hnone hsome hct hA hA').toAlgHom
    (alphaPEnvelopeAlgEquiv₀ hg hnone hsome hct hA hA').symm.toAlgHom
    (isDPMorphism_alphaPEnvelopeEquiv₀ hg hnone hsome hct)
    (isDPMorphism_alphaPEnvelopeEquiv₀_symm hg hnone hsome hct)
    (AlgHom.ext fun x => ((alphaPEnvelopeAlgEquiv₀ hg hnone hsome hct hA hA').symm_apply_apply
      x).symm)
    (AlgHom.ext fun x => ((alphaPEnvelopeAlgEquiv₀ hg hnone hsome hct hA hA').apply_symm_apply
      x).symm)

/-- The comparison of completed forms of `Crystalline.alphaPCompletedFormsIso₀` is semilinear over
the uncompleted identification. -/
public theorem alphaPCompletedFormsIso₀_algHom
    (hA : ∀ a, algebraMap s.A (polynomialDividedPowerEnvelope s g).object a =
      (polynomialDividedPowerEnvelope s g).structureMap a)
    (hA' : ∀ a, algebraMap s.A (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object a =
      (polynomialDividedPowerEnvelope (alphaPSituation s c) g').structureMap a)
    (x : (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object) :
    (alphaPCompletedFormsIso₀ hg hnone hsome hct hA hA').algHom x =
      alphaPEnvelopeToPrime₀ hg hnone hsome hct x :=
  rfl

end Uncompleted

/-! ### Degree zero of the cosimplicial envelope -/

section DegreeZero

open PthRootExtension MvPolynomial

variable (s : AffineCrystallineSituation.{u, v}) (c : s.C) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

/-- The variables `Fin 1 × Option ι` of degree zero of the extended presentation are those of
the original one with one more. -/
public def alphaPDegreeZeroVariables : Option (Fin 1 × ι) ≃ Fin 1 × Option ι where
  toFun o := o.elim (0, none) fun q => (q.1, some q.2)
  invFun q := q.2.map fun i => (q.1, i)
  left_inv o := by cases o <;> rfl
  right_inv q := by
    obtain ⟨j, o⟩ := q
    cases o with
    | none => exact Prod.ext (Subsingleton.elim _ _) rfl
    | some i => rfl

/-- The degree zero presentation `P'(0) → C'` sends the new variable to the class of `z`. -/
public theorem alphaPDegreeZero_none :
    tensorPowerPresentation (alphaPSituation s c) (alphaPPresentation s c f) 0
      (X (alphaPDegreeZeroVariables none)) = alphaPRoot s c := by
  show alphaPPresentation s c f (rename Prod.snd (X ((0 : Fin 1), none))) = _
  rw [rename_X, alphaPPresentation_X_none]

/-- The degree zero presentation `P'(0) → C'` restricts to `P(0) → C → C'` on the old
variables. -/
public theorem alphaPDegreeZero_some (k : Fin 1 × ι) :
    tensorPowerPresentation (alphaPSituation s c) (alphaPPresentation s c f) 0
      (X (alphaPDegreeZeroVariables (some k))) =
      algebraMap s.C (alphaPSituation s c).C (tensorPowerPresentation s f 0 (X k)) := by
  show alphaPPresentation s c f (rename Prod.snd (X (k.1, some k.2))) =
    algebraMap s.C (alphaPSituation s c).C (f (rename Prod.snd (X k)))
  rw [rename_X, rename_X, alphaPPresentation_X_some]

/-- The completed envelope of degree zero is the ring `D̂(0)` of the cosimplicial envelope. -/
public theorem envelopeCompletedDPRing_degreeZero :
    (envelopeCompletedDPRing s (tensorPowerPresentation s f 0) : Type (max u w)) =
      completedDividedPowerRing s.p (B := (envelopeDPAlgebra s f).carrier 0) :=
  rfl

/-- The divided power ideal of the completed envelope of degree zero is the completed divided
power ideal of degree zero of the cosimplicial envelope. -/
public theorem envelopeCompletedDPRing_degreeZero_ideal :
    HEq (envelopeCompletedDPRing s (tensorPowerPresentation s f 0)).ideal
      (completionIdeal ((envelopeDPAlgebra s f).ideal 0) s.p
        (polynomialDividedPowerEnvelope_prime_nilpotent s (tensorPowerPresentation s f 0))) :=
  HEq.rfl

variable {f} (hf : Function.Surjective f) {ct : MvPolynomial (Fin 1 × ι) s.A}
  (hct : tensorPowerPresentation s f 0 ct = c)
  {lam : envelopeCompletedDPRing s (tensorPowerPresentation s f 0)}
  (hlam : lam - AdicCompletion.of _ _
      ((polynomialDividedPowerEnvelope s (tensorPowerPresentation s f 0)).algebraMap.toRingHom ct)
    ∈ (envelopeCompletedDPRing s (tensorPowerPresentation s f 0)).ideal)

/-- **[Stacks, Tag 07Q9], proof: the completed envelope of `C' = C[z]/(z^p - c)`.**  For a
surjective presentation `f : P → C`, its extension `P[z] → C'` by `z ↦ z` and a lift `λ ∈ D` of
`c` (congruent to the image of a lift `c̃ ∈ P` modulo the divided power ideal), the ring `D'(0)` of
the cosimplicial envelope of `P[z] → C'` is isomorphic, as a divided power ring, to the `p`-adic
completion of `D(0)[z]⟨ξ⟩/(ξ - (z^p - λ))`. -/
public def alphaPEnvelopeDegreeZeroIso :
    envelopeCompletedDPRing (alphaPSituation s c)
        (tensorPowerPresentation (alphaPSituation s c) (alphaPPresentation s c f) 0) ≅
      alphaPCompletedPrimeDPRing s (tensorPowerPresentation s f 0) lam :=
  alphaPCompletedEnvelopeIso (tensorPowerPresentation_surjective s f hf 0)
    (alphaPDegreeZero_none s c f) (alphaPDegreeZero_some s c f) hct hlam

/-- The isomorphism of `Crystalline.alphaPEnvelopeDegreeZeroIso` is compatible with the structure
maps from `D(0)`. -/
public theorem alphaPEnvelopeDegreeZeroIso_hom_envelopeMap
    (d : envelopeCompletedDPRing s (tensorPowerPresentation s f 0)) :
    (alphaPEnvelopeDegreeZeroIso s c hf hct hlam).hom
        (alphaPCompletedEnvelopeMap (alphaPDegreeZero_some s c f) d) =
      AdicCompletion.of _ _
        (algebraMap (envelopeCompletedDPRing s (tensorPowerPresentation s f 0))
          (primeRing (envelopeCompletedDPRing s (tensorPowerPresentation s f 0)) s.p lam) d) :=
  alphaPCompletedEnvelopeToPrime_envelopeMap _ _ _ hct hlam d

/-- The isomorphism of `Crystalline.alphaPEnvelopeDegreeZeroIso` sends the class of `z` to the
class of `z`. -/
public theorem alphaPEnvelopeDegreeZeroIso_hom_root :
    (alphaPEnvelopeDegreeZeroIso s c hf hct hlam).hom
        (alphaPCompletedRoot s c _ (alphaPDegreeZeroVariables (ι := ι))) =
      AdicCompletion.of _ _
        (zElt (envelopeCompletedDPRing s (tensorPowerPresentation s f 0)) s.p lam) :=
  alphaPCompletedEnvelopeToPrime_root _ _ _ hct hlam

/-- **The forms of `D'(0)` are the completed forms of `E(0)[z]⟨ξ⟩/(ξ - (z^p - c̃))`**: in every
exterior degree `a` the module `Ω^a_{D'(0)} = Crystalline.envelopeForms` of degree zero of the
cosimplicial envelope of `P[z] → C'` is identified with the completed divided power forms of
`E(0)[z]⟨ξ⟩/(ξ - (z^p - c̃))` over `A`, compatibly with wedge products, de Rham differentials and
the universal differential, where `E(0)` is the uncompleted envelope of degree zero of `P → C` and
`c̃` the image of a lift of `c`.  This is the identification
`Crystalline.alphaPCompletedFormsIso₀` of the uncompleted divided power isomorphism
`Crystalline.alphaPEnvelopeEquiv₀`. -/
public def alphaPEnvelopeDegreeZeroFormsIso :
    letI := tensorPowerEnvelopeAlgebraInstance s f 0
    CompletedFormsDPIso s.p s.A
      ((envelopeDPAlgebra (alphaPSituation s c) (alphaPPresentation s c f)).dividedPowers 0)
      (primeDividedPowers (tensorPowerEnvelope s f 0).object s.p
        (alphaPLift (tensorPowerPresentation s f 0) ct) s.p_ne_zero) :=
  letI := tensorPowerEnvelopeAlgebraInstance s f 0
  letI := tensorPowerEnvelopeAlgebraInstance (alphaPSituation s c) (alphaPPresentation s c f) 0
  alphaPCompletedFormsIso₀ (tensorPowerPresentation_surjective s f hf 0)
    (alphaPDegreeZero_none s c f) (alphaPDegreeZero_some s c f) hct (fun _ => rfl) (fun _ => rfl)

/-- The ring map of `Crystalline.alphaPEnvelopeDegreeZeroFormsIso` is the uncompleted
identification `E'(0) → E(0)[z]⟨ξ⟩/⋯`. -/
public theorem alphaPEnvelopeDegreeZeroFormsIso_algHom
    (x : (envelopeDPAlgebra (alphaPSituation s c) (alphaPPresentation s c f)).carrier 0) :
    (alphaPEnvelopeDegreeZeroFormsIso s c hf hct).algHom x =
      alphaPEnvelopeToPrime₀ (tensorPowerPresentation_surjective s f hf 0)
        (alphaPDegreeZero_none s c f) (alphaPDegreeZero_some s c f) hct x :=
  rfl

end DegreeZero

end Crystalline

end

end
