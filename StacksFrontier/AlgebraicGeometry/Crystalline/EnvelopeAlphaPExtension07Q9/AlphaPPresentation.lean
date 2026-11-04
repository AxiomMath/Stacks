module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AlphaPCover
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedFormsDPIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PthRootFormsDecomposition
public import StacksFrontier.RingTheory.DividedPowers.CompletionUniversalProperty
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.SetIndexedUniversalProperty

/-!
# The completed envelope of an `α_p`-extension: the situation and the map `D → D'`

The proof of [Stacks, Lemma 60.25.4, Tag 07Q9] works with `S = Spec(A)`, `X = Spec(C)` and
`X' = Spec(C')` for `C' = C[z]/(z^p - c)`.  It chooses a polynomial presentation `P → C`, with
`p`-adically completed divided power envelope `D`, sets `P' = P[z] → C'` with `z ↦ z`, chooses a
lift `λ ∈ D` of `c`, and asserts that the `p`-adically completed divided power envelope `D'` of
`Ker(P' → C')` is isomorphic to the `p`-adic completion of `D[z]⟨ξ⟩/(ξ - (z^p - λ))`, "see Lemma
07N1 and its proof".  This file sets up the objects of that assertion; it is proved in
`Crystalline.alphaPCompletedEnvelopeEquiv` (completed form) and `Crystalline.alphaPEnvelopeEquiv₀`
(uncompleted form).

## Main definitions

* `Crystalline.alphaPSituation` — the affine crystalline situation of `C'` over the same base.
* `Crystalline.alphaPPresentation` — the presentation `P[z] → C'`, surjective by
  `Crystalline.alphaPPresentation_surjective`.
* `Crystalline.envelopeCompletedDPRing` — the completed envelope `D` of a presentation as a divided
  power ring.
* `Crystalline.alphaPCompletedEnvelopeMap` — the map `D → D'` induced by `P → P'`.

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

/-! ### The universal property of a divided power envelope, as a lift and an extensionality -/

namespace DividedPowerEnvelope

variable {A : DividedPowerRing.{u}} {B : Type v} [CommRing B] {f : A →+* B} {J : Ideal B}
  {hJ : A.ideal.map f ≤ J} (env : DividedPowerEnvelope A f J hJ)

/-- **The divided power morphism out of an envelope** determined by a divided power morphism `a`
of the base and a ring map `h` of `B` carrying `J` into the divided power ideal and agreeing with
`a` on the base. -/
public def liftDP (T : DividedPowerRing.{max u v})
    (a : DPMorphism A.dividedPowers T.dividedPowers) (h : B →+* T) (hJT : J.map h ≤ T.ideal)
    (hcomm : h.comp f = a.toRingHom) :
    DPMorphism env.object.dividedPowers T.dividedPowers :=
  ((env.homEquiv T a).symm
    ⟨IdealPair.Hom.ofRingHom h hJT, IdealPair.Hom.ext_toRingHom _ _ hcomm⟩).1

/-- The lift restricts to the given ring map on `B`. -/
public theorem liftDP_algebraMap (T : DividedPowerRing.{max u v})
    (a : DPMorphism A.dividedPowers T.dividedPowers) (h : B →+* T) (hJT : J.map h ≤ T.ideal)
    (hcomm : h.comp f = a.toRingHom) (x : B) :
    env.liftDP T a h hJT hcomm (env.algebraMap.toRingHom x) = h x := by
  have hsymm := (env.homEquiv T a).apply_symm_apply
    ⟨IdealPair.Hom.ofRingHom h hJT, IdealPair.Hom.ext_toRingHom _ _ hcomm⟩
  have happly := env.homEquiv_apply T a ((env.homEquiv T a).symm
    ⟨IdealPair.Hom.ofRingHom h hJT, IdealPair.Hom.ext_toRingHom _ _ hcomm⟩)
  have hcomp := happly.symm.trans (congrArg Subtype.val hsymm)
  exact congrArg (fun z : IdealPair.Hom _ _ => z.toRingHom x) hcomp

/-- The lift restricts to the given divided power morphism on the base. -/
public theorem liftDP_comp_structureMap (T : DividedPowerRing.{max u v})
    (a : DPMorphism A.dividedPowers T.dividedPowers) (h : B →+* T) (hJT : J.map h ≤ T.ideal)
    (hcomm : h.comp f = a.toRingHom) :
    (env.liftDP T a h hJT hcomm).comp env.structureMap = a :=
  ((env.homEquiv T a).symm
    ⟨IdealPair.Hom.ofRingHom h hJT, IdealPair.Hom.ext_toRingHom _ _ hcomm⟩).2

/-- **Two divided power morphisms out of an envelope agreeing on `B` are equal.** -/
public theorem dpMorphism_ext {T : DividedPowerRing.{max u v}}
    (q₁ q₂ : DPMorphism env.object.dividedPowers T.dividedPowers)
    (h : ∀ x, q₁ (env.algebraMap.toRingHom x) = q₂ (env.algebraMap.toRingHom x)) :
    q₁ = q₂ := by
  have hs : ∀ y, env.structureMap y = env.algebraMap.toRingHom (f y) := fun y =>
    (RingHom.congr_fun env.algebraMap_comp y).symm
  have h₁ : q₁.comp env.structureMap = q₂.comp env.structureMap := by
    apply DPMorphism.ext
    ext y
    show q₁ (env.structureMap y) = q₂ (env.structureMap y)
    rw [hs, h]
  have key : env.homEquiv T (q₂.comp env.structureMap) ⟨q₁, h₁⟩ =
      env.homEquiv T (q₂.comp env.structureMap) ⟨q₂, rfl⟩ := by
    apply Subtype.ext
    rw [env.homEquiv_apply, env.homEquiv_apply]
    apply IdealPair.Hom.ext_toRingHom
    exact RingHom.ext h
  exact congrArg Subtype.val ((env.homEquiv T _).injective key)

end DividedPowerEnvelope

/-! ### Ring maps out of a `p`-adic completion -/

/-- **Two ring maps out of a `p`-adic completion agreeing on the uncompleted ring are equal**, for
a `p`-adically Hausdorff target.  No continuity is needed: a ring map carries `(p)^n` into
`(p)^n`. -/
public theorem ringHom_ext_pAdicCompletion {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    (p : ℕ) [IsHausdorff (pAdicIdeal (A := S) p) S]
    (g₁ g₂ : AdicCompletion (pAdicIdeal (A := R) p) R →+* S)
    (h : ∀ x, g₁ (AdicCompletion.of (pAdicIdeal (A := R) p) R x) =
      g₂ (AdicCompletion.of (pAdicIdeal (A := R) p) R x)) :
    g₁ = g₂ := by
  have key : ∀ (φ : AdicCompletion (pAdicIdeal (A := R) p) R →+* S) (n : ℕ)
      (z : AdicCompletion (pAdicIdeal (A := R) p) R),
      z ∈ (pAdicIdeal (A := R) p ^ n).map
          (algebraMap R (AdicCompletion (pAdicIdeal (A := R) p) R)) →
        φ z ∈ pAdicIdeal (A := S) p ^ n := by
    intro φ n z hz
    have h1 : φ z ∈ Ideal.map φ ((pAdicIdeal (A := R) p ^ n).map
        (algebraMap R (AdicCompletion (pAdicIdeal (A := R) p) R))) :=
      Ideal.mem_map_of_mem _ hz
    rw [Ideal.map_map, Ideal.map_pow,
      pAdicIdeal_map (φ.comp (algebraMap R
        (AdicCompletion (pAdicIdeal (A := R) p) R))) p] at h1
    exact h1
  ext z
  have hhaus : IsHausdorff (pAdicIdeal (A := S) p) S := ‹_›
  refine sub_eq_zero.mp (hhaus.haus _ fun n => ?_)
  obtain ⟨a, ha⟩ := AdicCompletion.exists_sub_mem_map_pow
    (pAdicIdeal (A := R) p) (pAdicIdeal_fg p) n z
  have h1 := key g₁ n _ ha
  have h2 := key g₂ n _ ha
  have ha' : g₁ (algebraMap R _ a) = g₂ (algebraMap R _ a) := h a
  have hsub := Submodule.sub_mem (pAdicIdeal (A := S) p ^ n : Ideal S) h1 h2
  rw [map_sub, map_sub, ha', sub_sub_sub_cancel_right] at hsub
  rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]
  exact hsub

/-- The canonical map to an adic completion is its algebra map. -/
public theorem _root_.AdicCompletion.of_eq_algebraMap {R : Type*} [CommRing R] (I : Ideal R)
    (x : R) : AdicCompletion.of I R x = algebraMap R (AdicCompletion I R) x :=
  rfl

/-- The `p`-adic completion of a divided power ring in which `p` is nilpotent modulo the divided
power ideal, with the completed divided powers of [Stacks, Tag 07KD]. -/
public abbrev pAdicCompletedDPRing (R : DividedPowerRing.{u}) (p : ℕ)
    (hp : IsNilpotent (Ideal.Quotient.mk R.ideal (p : R))) : DividedPowerRing.{u} :=
  .of (AdicCompletion (pAdicIdeal (A := R) p) R) (completionIdeal R.ideal p hp)
    (completedDividedPowers R.ideal R.dividedPowers p hp).1


/-! ### The extension ring over a divided power ring in which `p` is nilpotent -/

section PrimeRing

open PthRootExtension

variable (B : DividedPowerRing.{u}) (p : ℕ) (lam : (B : Type u)) (hp : p ≠ 0)

include hp in
/-- `p` is nilpotent modulo the divided power ideal `J'` of `B' = B[z]⟨ξ⟩/(ξ - (z^p - λ))` as soon
as it is nilpotent modulo that of `B`, the structure map being a divided power morphism. -/
public theorem alphaP_isNilpotent_mk_primeIdeal
    (hpnil : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u)))) :
    IsNilpotent (Ideal.Quotient.mk (primeDPRing B p lam hp).ideal
      ((p : ℕ) : primeDPRing B p lam hp)) := by
  obtain ⟨n, hn⟩ := hpnil
  refine ⟨n, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  have hcast : ((p : ℕ) : primeRing B p lam) ^ n =
      algebraMap (B : Type u) (primeRing B p lam) (((p : ℕ) : (B : Type u)) ^ n) := by
    rw [map_pow, map_natCast]
  show ((p : ℕ) : primeRing B p lam) ^ n ∈ primeIdeal B p lam
  rw [hcast]
  refine (isDPMorphism_algebraMap_primeDividedPowers B p lam hp).ideal_comp
    (Ideal.mem_map_of_mem _ ?_)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
  exact hn

/-- The structure map `B → B'` as a divided power morphism. -/
public def alphaPAlgebraMapDP :
    DPMorphism B.dividedPowers (primeDividedPowers B p lam hp) :=
  DPMorphism.mk' (isDPMorphism_algebraMap_primeDividedPowers B p lam hp)

end PrimeRing


/-- The `p`-adic completion of a divided power ring is `p`-adically complete. -/
public instance pAdicCompletedDPRing.isAdicComplete (R : DividedPowerRing.{u}) (p : ℕ)
    (hp : IsNilpotent (Ideal.Quotient.mk R.ideal (p : R))) :
    IsAdicComplete (pAdicIdeal (A := pAdicCompletedDPRing R p hp) p)
      (pAdicCompletedDPRing R p hp) :=
  isAdicComplete_pAdicIdeal_adicCompletion p

/-- **A divided power morphism into a `p`-adically complete divided power ring extends to the
completion** ([Stacks, Tag 07KD]), in the bundled form used below. -/
public theorem exists_dpMorphism_pAdicCompletedDPRing (R T : DividedPowerRing.{u}) (p : ℕ)
    [Fact p.Prime] [Algebra (IntegersAtPrime p) R] [Algebra (IntegersAtPrime p) T]
    (hR : IsNilpotent (Ideal.Quotient.mk R.ideal (p : R)))
    (hT : IsNilpotent (Ideal.Quotient.mk T.ideal (p : T)))
    [IsAdicComplete (pAdicIdeal (A := T) p) T]
    (f : DPMorphism R.dividedPowers T.dividedPowers) :
    ∃ g : DPMorphism (pAdicCompletedDPRing R p hR).dividedPowers T.dividedPowers,
      ∀ x, g (AdicCompletion.of _ _ x) = f x := by
  obtain ⟨g, hg⟩ := exists_dPMorphism_from_completion R.ideal R.dividedPowers T.ideal
    T.dividedPowers p hR hT f
  exact ⟨g, fun x => RingHom.congr_fun hg x⟩

/-! ### The `α_p`-extension of an affine crystalline situation -/

/-- An algebra map out of a polynomial ring, composed with a renaming of the variables, is
determined by its values on the variables. -/
private theorem aeval_rename_eq_algebraMap {A C C' κ κ' : Type*} [CommRing A] [CommRing C]
    [CommRing C'] [Algebra A C] [Algebra A C'] [Algebra C C'] [IsScalarTower A C C']
    (g' : MvPolynomial κ' A →ₐ[A] C') (g : MvPolynomial κ A →ₐ[A] C) (r : κ → κ')
    (hr : ∀ k, g' (MvPolynomial.X (r k)) = algebraMap C C' (g (MvPolynomial.X k)))
    (x : MvPolynomial κ A) : g' (MvPolynomial.rename r x) = algebraMap C C' (g x) := by
  have h : g'.comp (MvPolynomial.rename r) = (IsScalarTower.toAlgHom A C C').comp g := by
    ext k
    rw [AlgHom.comp_apply, MvPolynomial.rename_X, hr]
    rfl
  exact congrArg (fun q : MvPolynomial κ A →ₐ[A] _ => q x) h

section Situation

variable (s : AffineCrystallineSituation.{u, v}) (c : s.C)

/-- **The affine crystalline situation of `C' = C[z]/(z^p - c)`** over the same divided power
base: the ideal of the base still vanishes in `C'`, and `p` is still nilpotent there. -/
public abbrev alphaPSituation : AffineCrystallineSituation.{u, v} where
  p := s.p
  A := s.A
  C := AlgebraicGeometry.alphaPAlgebra s.p s.C c
  ideal_map_eq_bot := by
    rw [IsScalarTower.algebraMap_eq s.A s.C, ← Ideal.map_map, s.ideal_map_eq_bot,
      Ideal.map_bot]
  prime_nilpotent := by
    have h := s.prime_nilpotent.map (algebraMap s.C (AlgebraicGeometry.alphaPAlgebra s.p s.C c))
    simpa using h

/-- The class of `z` in `C' = C[z]/(z^p - c)`. -/
public abbrev alphaPRoot : (alphaPSituation s c).C :=
  Ideal.Quotient.mk _ Polynomial.X

variable {ι : Type w} (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

/-- **The presentation `P[z] → C'`** extending a presentation `P → C` by sending the new variable
to the class of `z`. -/
public def alphaPPresentation :
    MvPolynomial (Option ι) s.A →ₐ[s.A] (alphaPSituation s c).C :=
  MvPolynomial.aeval fun o => o.elim (alphaPRoot s c)
    (fun i => algebraMap s.C (alphaPSituation s c).C (f (MvPolynomial.X i)))

/-- The extended presentation sends the new variable to the class of `z`. -/
@[simp] public theorem alphaPPresentation_X_none :
    alphaPPresentation s c f (MvPolynomial.X none) = alphaPRoot s c := by
  simp [alphaPPresentation]

/-- The extended presentation sends an old variable to its image under `P → C → C'`. -/
@[simp] public theorem alphaPPresentation_X_some (i : ι) :
    alphaPPresentation s c f (MvPolynomial.X (some i)) =
      algebraMap s.C (alphaPSituation s c).C (f (MvPolynomial.X i)) := by
  simp [alphaPPresentation]

/-- On the old variables the extended presentation is the old one followed by `C → C'`. -/
public theorem alphaPPresentation_rename_some (x : MvPolynomial ι s.A) :
    alphaPPresentation s c f (MvPolynomial.rename some x) =
      algebraMap s.C (alphaPSituation s c).C (f x) := by
  exact aeval_rename_eq_algebraMap (alphaPPresentation s c f) f some
    (alphaPPresentation_X_some s c f) x

/-- The extended presentation is surjective when the original one is. -/
public theorem alphaPPresentation_surjective (hf : Function.Surjective f) :
    Function.Surjective (alphaPPresentation s c f) := by
  intro y
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction q using Polynomial.induction_on with
  | C a =>
    obtain ⟨x, rfl⟩ := hf a
    exact ⟨MvPolynomial.rename some x, alphaPPresentation_rename_some s c f x⟩
  | add q r hq hr =>
    obtain ⟨x, hx⟩ := hq
    obtain ⟨y, hy⟩ := hr
    exact ⟨x + y, by rw [map_add, hx, hy, map_add]⟩
  | monomial n a _ =>
    obtain ⟨x, hx⟩ := hf a
    refine ⟨MvPolynomial.rename some x * MvPolynomial.X none ^ (n + 1), ?_⟩
    rw [map_mul, map_pow, alphaPPresentation_rename_some, alphaPPresentation_X_none, hx,
      map_mul, map_pow]
    rfl

end Situation

/-! ### The comparison for a pair of presentations -/

section Core

open PthRootExtension MvPolynomial

variable (s : AffineCrystallineSituation.{u, v}) (c : s.C) {κ κ' : Type w}
  (g : MvPolynomial κ s.A →ₐ[s.A] s.C)
  (g' : MvPolynomial κ' s.A →ₐ[s.A] (alphaPSituation s c).C) (e : Option κ ≃ κ')

/-- **The completed envelope `D` of a polynomial presentation** as a divided power ring, with the
completed divided powers of [Stacks, Tag 07KD]. -/
public abbrev envelopeCompletedDPRing : DividedPowerRing.{max u w} :=
  pAdicCompletedDPRing (polynomialDividedPowerEnvelope s g).object s.p
    (polynomialDividedPowerEnvelope_prime_nilpotent s g)

/-- The structure map `E → D` of the completion of the envelope, as a divided power morphism. -/
public abbrev envelopeCompletionDP :
    DPMorphism (polynomialDividedPowerEnvelope s g).object.dividedPowers
      (envelopeCompletedDPRing s g).dividedPowers :=
  completionDPMorphism _ _ s.p (polynomialDividedPowerEnvelope_prime_nilpotent s g)

variable {s c g g' e}

/-- The renaming of the old variables carries the kernel of `P → C` into that of `P' → C'`. -/
public theorem alphaP_rename_mem_ker
    (hsome : ∀ k, g' (X (e (some k))) = algebraMap s.C (alphaPSituation s c).C (g (X k)))
    (x : MvPolynomial κ s.A) :
    g' (rename (e ∘ some) x) = algebraMap s.C (alphaPSituation s c).C (g x) :=
  aeval_rename_eq_algebraMap g' g (e ∘ some) hsome x

variable (hsome : ∀ k, g' (X (e (some k))) = algebraMap s.C (alphaPSituation s c).C (g (X k)))

/-- **The map of envelopes `E → E'`** induced by the inclusion `P → P'` of the presentations. -/
public def alphaPEnvelopeMap :
    DPMorphism (polynomialDividedPowerEnvelope s g).object.dividedPowers
      (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object.dividedPowers :=
  (polynomialDividedPowerEnvelope s g).liftDP
    (polynomialDividedPowerEnvelope (alphaPSituation s c) g').object
    (polynomialDividedPowerEnvelope (alphaPSituation s c) g').structureMap
    ((polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom.comp
      (rename (e ∘ some)).toRingHom)
    (by
      rw [← Ideal.map_map]
      refine le_trans (Ideal.map_mono ?_)
        (polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.ideal_comp
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      change g' (rename (e ∘ some) x) = 0
      rw [alphaP_rename_mem_ker hsome, show g x = 0 from hx, map_zero])
    (by
      ext a
      change (polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom
        (rename (e ∘ some) (algebraMap s.A (MvPolynomial κ s.A) a)) = _
      rw [AlgHom.commutes]
      exact RingHom.congr_fun
        (polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap_comp a)

/-- The map of envelopes `E → E'` restricts to the renaming of the variables on `P`. -/
public theorem alphaPEnvelopeMap_algebraMap (x : MvPolynomial κ s.A) :
    alphaPEnvelopeMap hsome ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom x) =
      (polynomialDividedPowerEnvelope (alphaPSituation s c) g').algebraMap.toRingHom
        (rename (e ∘ some) x) :=
  DividedPowerEnvelope.liftDP_algebraMap _ _ _ _ _ _ x

/-- The map of envelopes `E → E'` is a map over the base. -/
public theorem alphaPEnvelopeMap_structureMap (a : s.A) :
    alphaPEnvelopeMap hsome ((polynomialDividedPowerEnvelope s g).structureMap a) =
      (polynomialDividedPowerEnvelope (alphaPSituation s c) g').structureMap a :=
  congrArg (fun q : DPMorphism _ _ => q a)
    (DividedPowerEnvelope.liftDP_comp_structureMap _ _ _ _ _ _)

/-- **The map of completed envelopes `D → D'`** induced by the inclusion of the presentations. -/
public def alphaPCompletedEnvelopeMap :
    DPMorphism (envelopeCompletedDPRing s g).dividedPowers
      (envelopeCompletedDPRing (alphaPSituation s c) g').dividedPowers :=
  DPMorphism.mk' (adicCompletionRingMap_isDPMorphism _ _ s.p _ _ (alphaPEnvelopeMap hsome))

/-- The map `D → D'` is the completion of the map of envelopes `E → E'`. -/
public theorem alphaPCompletedEnvelopeMap_of
    (x : (polynomialDividedPowerEnvelope s g).object) :
    alphaPCompletedEnvelopeMap hsome (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _ (alphaPEnvelopeMap hsome x) :=
  adicCompletionRingMap_of _ _ x

end Core

end Crystalline

end

end
