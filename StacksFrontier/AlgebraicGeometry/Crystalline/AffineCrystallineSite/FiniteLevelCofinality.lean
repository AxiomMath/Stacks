module

public import Mathlib.CategoryTheory.Limits.Final
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite.ProObject

/-!
# Cofinality of the finite-level diagram over a completed thickening

Let `X` be a completed crystalline thickening and `T` a finite-level system for it, that is, a
presentation of `X` as the inverse limit of the ordinary crystalline thickenings
`X/(p)^(N + e)`. This module records the concrete inclusion of the ordinary affine crystalline
category in its completed counterpart, the projections from `X` onto the terms of `T`, and the
resulting diagram `ℕᵒᵖ ⥤ StructuredArrow X (crystallineToCompleted S)`, and proves that this
diagram is initial.

Initiality is what makes the finite-level system compute a right Kan extension along the
inclusion: for an abelian presheaf `F` on the ordinary crystalline category, the value at `X`
of the right Kan extension is the limit of `F` over the structured-arrow category, and
initiality cuts that limit down to `lim_e F(X/(p)^(N + e))`. That identification is the
computation half of [Stacks, Tag 07JL]; this module supplies its categorical input.

## Main definitions

* `Crystalline.crystallineToCompleted` — the inclusion `Cris(C/A) ⥤ Cris^∧(C/A)` written out
  directly, sending a thickening to itself read as a complete one.
* `Crystalline.finiteLevelProjection` — the projection `X ⟶ crystallineToCompleted (T.term e)`.
* `Crystalline.finiteLevelStructuredArrow` — the diagram `ℕᵒᵖ ⥤ StructuredArrow X
  (crystallineToCompleted S)` assembled from those projections.

## Main results

* `Crystalline.finiteLevel_factor_morphism` — every morphism from `X` to a thickening read as
  a complete one factors through some finite level.
* `Crystalline.finiteLevel_initial` — the finite-level diagram is initial in the
  structured-arrow category.

## Implementation notes

The factorization lemma is where the mathematics sits: `p` is nilpotent in the target, so the
target's structure map kills a power of the `p`-adic divided power ideal of `X`, hence factors
through the quotient defining a sufficiently deep level. The factorization is then upgraded to
a divided power morphism and checked to be compatible with the base and with the structure map
to `C`.

Initiality is reduced to connectedness of each costructured-arrow category. The arrow category
is cofiltered through `max`, and a morphism out of a finite level is unique because the
projections are epimorphisms and the inclusion is faithful; that makes the comparison between
any two objects automatic.

The declarations here are deliberately public rather than private: the right Kan extension
computation of [Stacks, Tag 07JL] is proved in a different module, and needs the diagram and
its initiality by name.

## References

* [Stacks Project, Tag 07JL](https://stacks.math.columbia.edu/tag/07JL)
* [Stacks Project, Tag 07KH](https://stacks.math.columbia.edu/tag/07KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Crystalline

/-- An ordinary crystalline thickening read as a completed one: the same divided power ring,
which is complete because the ideal it is completed at is nilpotent. -/
public def completedOfCrystalline
    {S : AffineCrystallineSituation.{u, v}} (Y : CrystallineThickening.{u, v, w} S) :
    CompletedCrystallineThickening.{u, v, w} S where
  ring := Y.obj.ring
  fromBase := Y.obj.fromBase
  isComplete := by
    have h := ((crystallineEquivalenceNilpotentCompleted S).1.functor.obj Y).obj.isComplete
    rwa [(crystallineEquivalenceNilpotentCompleted S).2.1 Y] at h
  toQuotient := Y.obj.toQuotient
  commutes := Y.obj.commutes
  toQuotient_bijective := Y.property

/-- The canonical inclusion of the ordinary affine crystalline category in its completed
counterpart, written out directly: an object goes to itself read as a complete thickening, and
a morphism to its underlying divided power map. -/
public def crystallineToCompleted (S : AffineCrystallineSituation.{u, v}) :
    CrystallineThickening.{u, v, w} S ⥤ CompletedCrystallineThickening.{u, v, w} S where
  obj := completedOfCrystalline
  map f :=
    { hom := f.hom.hom
      fromBase_comp := f.hom.fromBase_comp
      toQuotient_comp := f.hom.toQuotient_comp }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The projection of a completed thickening onto the `e`-th term of a finite-level system
for it, read as a morphism of completed thickenings. -/
public def finiteLevelProjection {S : AffineCrystallineSituation.{u, v}}
    {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X) (e : ℕ) :
    X ⟶ (crystallineToCompleted S).obj (T.term e) where
  hom := T.projection e
  fromBase_comp := T.projection_fromBase e
  toQuotient_comp := T.projection_toQuotient e

/-- The projections of a finite-level system are compatible with its transition maps. -/
public lemma finiteLevelProjection_transition {S : AffineCrystallineSituation.{u, v}}
    {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X)
    {e e' : ℕ} (h : e ≤ e') :
    finiteLevelProjection T e' ≫ (crystallineToCompleted S).map (T.transition h) =
      finiteLevelProjection T e :=
  CompletedCrystallineThickening.Hom.ext (T.transition_projection h)

/-- Every morphism from a completed thickening to an ordinary crystalline thickening, read as a
complete one, factors through some finite level of a finite-level system. Nilpotence of `p` in
the target bounds the level that suffices. -/
public lemma finiteLevel_factor_morphism
    {S : AffineCrystallineSituation.{u, v}}
    {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X)
    {Y : CrystallineThickening.{u, v, w} S} (f : X ⟶ (crystallineToCompleted S).obj Y) :
    ∃ (e : ℕ) (g : T.term e ⟶ Y),
      finiteLevelProjection T e ≫ (crystallineToCompleted S).map g = f := by
  obtain ⟨e, he⟩ := Y.obj.prime_nilpotent
  have hpow : (S.p : Y.obj.ring) ^ (T.cutoff + e) = 0 := by
    rw [pow_add, he, mul_zero]
  have hker : RingHom.ker (T.projection e).toRingHom ≤ RingHom.ker f.hom.toRingHom := by
    rw [T.projection_ker, DividedPowers.pAdicIdeal, Ideal.span_singleton_pow]
    refine Ideal.span_le.mpr ?_
    rintro x ⟨rfl⟩
    show f.hom.toRingHom ((S.p : X.ring) ^ (T.cutoff + e)) = 0
    rwa [map_pow, map_natCast]
  let lift := Ideal.Quotient.lift (RingHom.ker (T.projection e).toRingHom)
    f.hom.toRingHom (fun x hx => RingHom.mem_ker.mp (hker hx))
  let mRing := lift.comp
    (RingHom.quotientKerEquivOfSurjective (T.projection_surjective e)).symm.toRingHom
  have hmRing : mRing.comp (T.projection e).toRingHom = f.hom.toRingHom := by
    ext x
    exact congrArg lift
      (RingHom.quotientKerEquivOfSurjective_symm_apply
        (f := (T.projection e).toRingHom) (T.projection_surjective e) x)
  let qq := Ideal.quotientMap (T.term e).obj.ring.ideal (T.projection e).toRingHom
    (Ideal.map_le_iff_le_comap.mp (T.projection e).ideal_comp)
  have hIdeal : (T.term e).obj.ring.ideal =
      X.ring.ideal.map (T.projection e).toRingHom := by
    have hcomp : qq.comp X.toQuotient = (T.term e).obj.toQuotient :=
      T.projection_toQuotient e
    have hqq : Function.Injective qq := by
      intro a b hab
      obtain ⟨c, rfl⟩ := X.toQuotient_bijective.surjective a
      obtain ⟨d, rfl⟩ := X.toQuotient_bijective.surjective b
      apply congrArg X.toQuotient
      apply (T.term e).property.injective
      change (qq.comp X.toQuotient) c = (qq.comp X.toQuotient) d at hab
      rwa [hcomp] at hab
    refine le_antisymm (fun y hy => ?_) (T.projection e).ideal_comp
    obtain ⟨x, rfl⟩ := T.projection_surjective e y
    have hx : Ideal.Quotient.mk X.ring.ideal x = 0 := by
      apply hqq
      show Ideal.Quotient.mk (T.term e).obj.ring.ideal ((T.projection e) x) = qq 0
      rw [map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hy
    exact Ideal.mem_map_of_mem _ (Ideal.Quotient.eq_zero_iff_mem.mp hx)
  have hdp : X.ring.dividedPowers.IsDPMorphism Y.obj.ring.dividedPowers
      (mRing.comp (T.projection e).toRingHom) := by
    rw [hmRing]
    exact f.hom.isDPMorphism
  let m := DividedPowers.DPMorphism.mk'
    (DividedPowers.IsDPMorphism.of_comp X.ring.dividedPowers
      (T.term e).obj.ring.dividedPowers Y.obj.ring.dividedPowers
      (T.projection e).toRingHom mRing
      hIdeal
      (T.projection e).isDPMorphism hdp)
  have hm : m.comp (T.projection e) = f.hom :=
    DividedPowers.DPMorphism.ext (congrArg DFunLike.coe hmRing)
  have hb : m.comp (T.term e).obj.fromBase = Y.obj.fromBase := by
    rw [← T.projection_fromBase e]
    show (m.comp (T.projection e)).comp X.fromBase = _
    rw [hm]
    exact f.fromBase_comp
  let qm := DividedPowerRing.quotientRingHom
    (A := (T.term e).obj.ring) (B := Y.obj.ring) m
  have hq : qm.comp qq =
      DividedPowerRing.quotientRingHom f.hom := by
    refine RingHom.ext fun z => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    show Ideal.Quotient.mk Y.obj.ring.ideal (m ((T.projection e) x)) =
      Ideal.Quotient.mk Y.obj.ring.ideal (f.hom x)
    exact congrArg (Ideal.Quotient.mk Y.obj.ring.ideal) (DFunLike.congr_fun hm x)
  have hc : qm.comp (T.term e).obj.toQuotient = Y.obj.toQuotient := by
    rw [← T.projection_toQuotient e, ← RingHom.comp_assoc]
    show (qm.comp qq).comp X.toQuotient = _
    rw [hq]
    exact f.toQuotient_comp
  exact ⟨e, ⟨{ hom := m, fromBase_comp := hb, toQuotient_comp := hc }⟩,
    CompletedCrystallineThickening.Hom.ext hm⟩

/-- The projections of a finite-level system are epimorphisms, because they are surjective. -/
public lemma finiteLevelProjection_epi
    {S : AffineCrystallineSituation.{u, v}}
    {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X) (e : ℕ) :
    Epi (finiteLevelProjection T e) := by
  refine ⟨fun f g h => ?_⟩
  apply CompletedCrystallineThickening.Hom.ext
  apply DividedPowers.DPMorphism.ext
  funext y
  obtain ⟨x, rfl⟩ := T.projection_surjective e y
  exact congrArg (fun k => k.hom x) h

/-- The finite-level system of a completed thickening `X`, read as a diagram of objects of the
category of arrows out of `X` into the image of the concrete inclusion. -/
public def finiteLevelStructuredArrow
    {S : AffineCrystallineSituation.{u, v}}
    {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X) :
    ℕᵒᵖ ⥤ StructuredArrow X (crystallineToCompleted S) where
  obj e := StructuredArrow.mk (finiteLevelProjection T e.unop)
  map f := StructuredArrow.homMk (T.transition (leOfHom f.unop))
    (finiteLevelProjection_transition T (leOfHom f.unop))
  map_id e := StructuredArrow.hom_ext _ _ (T.transition_id e.unop)
  map_comp _ _ := StructuredArrow.hom_ext _ _ (T.transition_comp _ _).symm

/-- The concrete inclusion of the crystalline category in its completion is faithful. -/
public lemma crystallineToCompleted_faithful (S : AffineCrystallineSituation.{u, v}) :
    (crystallineToCompleted.{u, v, w} S).Faithful where
  map_injective h := by
    apply ObjectProperty.hom_ext
    apply DividedPowerThickening.Hom.ext
    exact congrArg (fun k => k.hom) h

/-- There is at most one morphism out of a finite level into any object of the structured-arrow
category: the projection is an epimorphism and the inclusion is faithful. -/
public lemma finiteLevel_arrow_subsingleton
    {S : AffineCrystallineSituation.{u, v}}
    {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X)
    (e : ℕᵒᵖ) (A : StructuredArrow X (crystallineToCompleted S)) :
    Subsingleton ((finiteLevelStructuredArrow T).obj e ⟶ A) := by
  have := crystallineToCompleted_faithful.{u, v, w} S
  have := finiteLevelProjection_epi T e.unop
  refine ⟨fun f g => ?_⟩
  apply StructuredArrow.hom_ext
  apply (crystallineToCompleted S).map_injective
  apply (cancel_epi (finiteLevelProjection T e.unop)).mp
  exact f.w.trans g.w.symm

/-- The finite-level diagram is initial in the category of arrows out of `X` into the image of
the concrete inclusion. This is the cofinality input to the right Kan extension computation of
[Stacks, Tag 07JL]. -/
public lemma finiteLevel_initial
    {S : AffineCrystallineSituation.{u, v}}
    {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X) :
    (finiteLevelStructuredArrow T).Initial := by
  refine ⟨fun A => ?_⟩
  obtain ⟨e, g, hg⟩ := finiteLevel_factor_morphism T A.hom
  have : Nonempty (CostructuredArrow (finiteLevelStructuredArrow T) A) :=
    ⟨CostructuredArrow.mk (Y := op e) (StructuredArrow.homMk g hg)⟩
  apply IsConnected.of_constant_of_preserves_morphisms
  intro α F hF a b
  let k := op (max a.left.unop b.left.unop)
  let ha : k ⟶ a.left := (homOfLE (Nat.le_max_left _ _)).op
  let hb : k ⟶ b.left := (homOfLE (Nat.le_max_right _ _)).op
  let c : CostructuredArrow (finiteLevelStructuredArrow T) A :=
    CostructuredArrow.mk ((finiteLevelStructuredArrow T).map ha ≫ a.hom)
  let fa : c ⟶ a := CostructuredArrow.homMk ha rfl
  let fb : c ⟶ b := CostructuredArrow.homMk hb
    ((finiteLevel_arrow_subsingleton T k A).elim _ _)
  exact (hF fa).symm.trans (hF fb)

end Crystalline

end
