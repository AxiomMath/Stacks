module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperFiniteCase
public import StacksFrontier.RingTheory.Henselian.Pair.LocalRing

/-!
# Finite étale covers after an extension of the ground field

Let `k'/k` be an extension of fields and let `f : X ⟶ Spec k` be a scheme over `k`. This file
studies the base-change functor `FÉt_X ⟶ FÉt_{X_{k'}}`, `U ↦ U_{k'}`, where
`X_{k'} = X ×_{Spec k} Spec k'`, and proves it to be an equivalence of categories for `X` proper
over `k` — the conclusion of Stacks Tag 0A49 — from two inputs taken as arguments, described
below.

The *faithful* half needs nothing: `Spec k'` is a one-point scheme over the one-point scheme
`Spec k`, so the projection `X_{k'} ⟶ X` is surjective, and
`AlgebraicGeometry.faithful_finiteEtaleBaseChange_of_forall_exists_specializes` applies with every
point of `X` specializing to itself.  By the same surjectivity the reduction of Tag 0GS2 in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperEquivalence` applies verbatim,
and the whole statement is reduced to *essential surjectivity over every finite étale cover of `X`*
(`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_essSurj`).

## The two inputs taken as arguments

This file takes two inputs of the source proof as arguments, so that it does not import the
modules proving them; both are proved in this library, and
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_isAlgClosed` (in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleAlgClosedEquivalence`) supplies both.

* `AlgebraicGeometry.ProperHenselianFiniteEtaleEquivalence` is the conclusion of Tag 0A48 for a
  **proper** scheme over a henselian local ring.  It is proved as
  `AlgebraicGeometry.properHenselianFiniteEtaleEquivalence`
  (`StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperHenselianLimit`), from
  Grothendieck existence (Tag 088C) and the reduction to Noetherian G-rings.

* `AlgebraicGeometry.FiniteEtaleDescendsToHenselianPoint` is the *spreading out* step: every scheme
  finite étale over `X_{k'}` is already the base change of one finite étale over `X_R`, for some
  henselian local `k`-algebra `R` with residue field `k` and some `k`-algebra map `R → k'`
  (an `AlgebraicGeometry.HenselianPoint`).  For `k ⊆ k'` algebraically closed this is what the
  source's filtered-colimit argument produces: write `k' = colim A_i` over the finite-type
  `k`-subalgebras of `k'` (`Stacks.RingTheory.FiniteTypeSubalgebra.iSup_eq_top` and the universal
  property beside it), present `X_{k'}` as the cofiltered limit of the `X_{A_i}`
  (`AlgebraicGeometry.isLimitPullbackConeLimitCone`, Tag 01YZ), descend the cover to one stage by
  Tag 01ZM (`AlgebraicGeometry.Scheme.exists_model_of_finitePresentation`) and make it finite and
  étale by Tags 01ZO and 07RP
  (`AlgebraicGeometry.exists_isFinite_baseChange_of_isLimit`,
  `AlgebraicGeometry.exists_etale_pullback_of_isLimit`); then take `R` to be the henselization of
  `A_i` at the maximal ideal of a `k`-point of `Spec A_i` — which exists because `k` is
  algebraically closed and `A_i` is of finite type
  (`finite_of_finite_type_of_isJacobsonRing` and `IsAlgClosed.lift`) — and obtain the map `R → k'`
  from the algebraicity of a henselization over its base (Tag 0A1W,
  `IsLocalRing.isAlgebraic_of_isHenselization`) together with `k'` being algebraically closed.
  That chain is carried out in
  `StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleSpreadingOut`, as
  `AlgebraicGeometry.finiteEtaleDescendsToHenselianPoint_of_isAlgClosed`.

Neither hypothesis is a restatement of the conclusion: the descent hypothesis produces a cover of
`X_R`, and bringing it down from `X_R` to `X` is exactly what the proper case of Tag 0A48 does
here.  It is, however, satisfied by the choice `R = k`, in which case it *is* essential
surjectivity; the content of this file is therefore the reduction of Tag 0A49 to descent to a
henselian local approximation, not the construction of that approximation.

## Main definitions

* `AlgebraicGeometry.HenselianPoint` — a henselian local `k`-algebra with residue field `k`,
  together with a `k`-algebra map to `k'`: the henselization `A_i^h` of the source proof, with the
  map to `k'` extending `A_i ⊂ k'`.
* `AlgebraicGeometry.HenselianPoint.baseChangeMap` — the resulting morphism `X_{k'} ⟶ X_R`.
* `AlgebraicGeometry.ProperHenselianFiniteEtaleEquivalence` — the conclusion of Tag 0A48 for a
  proper scheme over a henselian local ring.
* `AlgebraicGeometry.FiniteEtaleDescendsToHenselianPoint` — the spreading-out hypothesis.

## Main results

* `AlgebraicGeometry.faithful_finiteEtaleBaseChange_specMap_algebraMap` — the faithfulness half of
  Tag 0A49, for an arbitrary extension of fields and an arbitrary scheme over `k`, with nothing
  carried.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_essSurj` — Tag 0A49
  reduced to essential surjectivity over every finite étale cover.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_comp_eq_id` — base change along a
  retraction `g` is an equivalence as soon as base change along a section of `g` is.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_pullback_fst_of_isIso_comp` — the
  geometric step: when `a ≫ b` is an isomorphism, base change along `X ×_S Z ⟶ X` is an
  equivalence as soon as base change along the projection
  `(X ×_S Z) ×_Z W ⟶ X ×_S Z` is.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_henselianPoint` —
  for a henselian local `k`-algebra `R` with residue field `k`, base change along `X_R ⟶ X` is an
  equivalence on finite étale covers, granted Tag 0A48 for `X_R ⟶ Spec R`.
* `isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_henselianPoint_of_isFinite`, in the
  same namespace — the same with Tag 0A48 for a finite morphism supplied, when `X` is finite over
  `k`; the conclusion is near-trivial there, such an `X` being zero-dimensional.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_properHenselian` —
  the conclusion of Tag 0A49 from the two inputs above.

## Implementation notes

The identification of the closed fibre of `X_R ⟶ Spec R` with `X` is not made as an isomorphism of
schemes over `Spec R`; it is used only through the one consequence the argument needs, namely that
the closed-fibre projection `(X ×_{Spec k} Spec R) ×_{Spec R} Spec (R ⧸ 𝔪) ⟶ X ×_{Spec k} Spec R`
agrees, after an isomorphism of its source, with a **section** of the projection
`X ×_{Spec k} Spec R ⟶ X`.  That is the content of
`isEquivalence_finiteEtaleBaseChange_pullback_fst_of_isIso_comp`, whose hypothesis
`IsIso (a ≫ b)` is, for `a = Spec (R → R ⧸ 𝔪)` and `b = Spec (k → R)`, precisely the statement
that the residue field of `R` is `k`.  Stating the step this way avoids identifying the two
pullbacks as schemes and keeps the proof to `pullbackLeftPullbackSndIso` and the transport lemmas
of `StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperFiniteCase`.

`HenselianPoint` is a structure rather than a bundle of existential quantifiers so that its ring
and algebra instances can be registered with `attribute [instance]` and used in the statements
about `Spec R`.

## References

* [Stacks Project, Tag 0A49](https://stacks.math.columbia.edu/tag/0A49)
* [Stacks Project, Tag 0A48](https://stacks.math.columbia.edu/tag/0A48)
* [Stacks Project, Tag 0GS2](https://stacks.math.columbia.edu/tag/0GS2)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 0A1W](https://stacks.math.columbia.edu/tag/0A1W)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-! ### Faithfulness, and the reduction to essential surjectivity -/

section Field

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']

/-- Every point of `X` lies in the image of the projection `X ×_{Spec k} Spec k' ⟶ X`, hence
specializes into it: the image of that projection is the preimage under `X ⟶ Spec k` of the image
of `Spec k' ⟶ Spec k`, and `Spec k` has exactly one point. -/
theorem specializes_mem_range_pullback_fst_specMap_algebraMap {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    ∃ x' ∈ Set.range (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k k')))).base, x ⤳ x' := by
  refine ⟨x, ?_, specializes_rfl⟩
  rw [Scheme.Pullback.range_fst]
  exact ⟨default, Subsingleton.elim _ _⟩

/-- **The faithfulness half of Tag 0A49.** For an arbitrary extension of fields `k'/k` and an
arbitrary scheme `X` over `k`, base change to `X_{k'}` is faithful on finite étale covers.

This is `faithful_finiteEtaleBaseChange_of_forall_exists_specializes` applied to the projection
`X_{k'} ⟶ X`, which is surjective. -/
theorem faithful_finiteEtaleBaseChange_specMap_algebraMap {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) :
    (finiteEtaleBaseChange (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).Faithful :=
  faithful_finiteEtaleBaseChange_of_forall_exists_specializes _
    (specializes_mem_range_pullback_fst_specMap_algebraMap f)

/-- **Tag 0A49 reduced to essential surjectivity.** If base change along the projection
`Y_{k'} ⟶ Y` is essentially surjective on finite étale covers for every `Y` finite étale over `X`,
then base change along `X_{k'} ⟶ X` is an equivalence on finite étale covers.

This is the reduction of Tag 0GS2, `isEquivalence_finiteEtaleBaseChange_of_essSurjOver`, applied to
the projection `X_{k'} ⟶ X`: the specialization hypothesis it needs holds because that projection
is surjective, so no properness of `f` is required here. -/
theorem isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_essSurj {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k))
    (hes : ∀ P : FiniteEtaleOver X,
      (finiteEtaleBaseChange (pullback.fst (P.hom ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).EssSurj) :
    (finiteEtaleBaseChange (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).IsEquivalence := by
  refine isEquivalence_finiteEtaleBaseChange_of_essSurjOver _
    (specializes_mem_range_pullback_fst_specMap_algebraMap f) fun P => ?_
  refine finiteEtaleBaseChangeEssSurjOver_of_essSurj _ P ?_
  rw [← pullbackRightPullbackFstIso_hom_fst f
    (Spec.map (CommRingCat.ofHom (algebraMap k k'))) P.hom]
  exact essSurj_finiteEtaleBaseChange_comp_of_isIso _ _ (hes P)

end Field

/-! ### Descending a cover along a retraction -/

/-- Base change along `g : Y ⟶ X` is an equivalence on finite étale covers as soon as `g` admits a
section `ι` along which base change is an equivalence.

Indeed `finiteEtaleBaseChange g ⋙ finiteEtaleBaseChange ι` is isomorphic to the identity by
`finiteEtaleBaseChangeComp` and `finiteEtaleBaseChangeId`, hence is an equivalence, and a functor
whose composition with an equivalence is an equivalence is itself one. -/
theorem isEquivalence_finiteEtaleBaseChange_of_comp_eq_id {X Y : Scheme.{u}} (ι : X ⟶ Y)
    (g : Y ⟶ X) (h : ι ≫ g = 𝟙 X) (hι : (finiteEtaleBaseChange ι).IsEquivalence) :
    (finiteEtaleBaseChange g).IsEquivalence :=
  have : (finiteEtaleBaseChange g ⋙ finiteEtaleBaseChange ι).IsEquivalence :=
    Functor.isEquivalence_of_iso
      ((finiteEtaleBaseChangeComp ι g (𝟙 X) h.symm).symm.trans finiteEtaleBaseChangeId).symm
  Functor.isEquivalence_of_comp_right _ (finiteEtaleBaseChange ι)

/-- Let `f : X ⟶ S`, `b : Z ⟶ S` and `a : W ⟶ Z` be such that `a ≫ b` is an isomorphism. Then base
change along the projection `X ×_S Z ⟶ X` is an equivalence on finite étale covers as soon as base
change along the projection `(X ×_S Z) ×_Z W ⟶ X ×_S Z` is.

The point is that `pullbackLeftPullbackSndIso` identifies `(X ×_S Z) ×_Z W` with `X ×_S W`, whose
projection to `X` is an isomorphism because `a ≫ b` is; so the projection
`(X ×_S Z) ×_Z W ⟶ X ×_S Z` is an isomorphism followed by a section of `X ×_S Z ⟶ X`, and
`isEquivalence_finiteEtaleBaseChange_of_comp_eq_id` applies. -/
theorem isEquivalence_finiteEtaleBaseChange_pullback_fst_of_isIso_comp {X S Z W : Scheme.{u}}
    (f : X ⟶ S) (b : Z ⟶ S) (a : W ⟶ Z) [IsIso (a ≫ b)]
    (h : (finiteEtaleBaseChange (pullback.fst (pullback.snd f b) a)).IsEquivalence) :
    (finiteEtaleBaseChange (pullback.fst f b)).IsEquivalence := by
  have hfstiso : IsIso (pullback.fst f (a ≫ b)) :=
    (MorphismProperty.isomorphisms Scheme).pullback_fst _ _ ‹IsIso (a ≫ b)›
  have hθ : IsIso ((pullbackLeftPullbackSndIso f b a).hom ≫ pullback.fst f (a ≫ b)) :=
    inferInstance
  have hfac : pullback.fst (pullback.snd f b) a ≫ pullback.fst f b
      = (pullbackLeftPullbackSndIso f b a).hom ≫ pullback.fst f (a ≫ b) := by
    rw [← pullbackLeftPullbackSndIso_inv_fst f b a, Iso.hom_inv_id_assoc]
  refine isEquivalence_finiteEtaleBaseChange_of_comp_eq_id
    (inv ((pullbackLeftPullbackSndIso f b a).hom ≫ pullback.fst f (a ≫ b)) ≫
      pullback.fst (pullback.snd f b) a) (pullback.fst f b) ?_
    (isEquivalence_finiteEtaleBaseChange_isIso_comp _ _ h)
  rw [Category.assoc, hfac, IsIso.inv_hom_id]

/-! ### A henselian local approximation of the extension -/

/-- A **henselian point** of the extension `k'/k`: a henselian local `k`-algebra `R` whose residue
field is `k`, together with a `k`-algebra map `R → k'`.

This is the datum the source proof of Tag 0A49 produces from a finite-type `k`-subalgebra
`A ⊆ k'` with a `k`-point `t`: `R` is the henselization of `A` at the maximal ideal of `t`, whose
residue field is `k` because `t` is a `k`-point, and the map to `k'` exists because `R` is
algebraic over `A` and `k'` is algebraically closed. -/
structure HenselianPoint (k k' : Type u) [Field k] [Field k'] [Algebra k k'] where
  /-- The underlying ring `R`. -/
  carrier : Type u
  /-- Its ring structure. -/
  [commRing : CommRing carrier]
  /-- Its `k`-algebra structure. -/
  [algebra : Algebra k carrier]
  /-- The map `R → k'`. -/
  [algebraTo : Algebra carrier k']
  /-- The map `R → k'` is a map of `k`-algebras. -/
  [isScalarTower : IsScalarTower k carrier k']
  /-- `R` is a henselian local ring. -/
  [henselian : HenselianLocalRing carrier]
  /-- The residue field of `R` is `k`. -/
  residue_bijective : Function.Bijective
    ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal carrier)).comp (algebraMap k carrier))

attribute [instance] HenselianPoint.commRing HenselianPoint.algebra HenselianPoint.algebraTo
  HenselianPoint.isScalarTower HenselianPoint.henselian

section HenselianPoint

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']

/-- The morphism `X_{k'} ⟶ X_R` induced by the map `R → k'` of a henselian point. -/
noncomputable def HenselianPoint.baseChangeMap (T : HenselianPoint k k') {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap k T.carrier))) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap T.carrier k')))
    (by
      rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq])

/-- The morphism `X_{k'} ⟶ X_R` lies over `X`. -/
@[simp]
theorem HenselianPoint.baseChangeMap_comp_fst (T : HenselianPoint k k') {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) :
    T.baseChangeMap f ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k T.carrier)))
      = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :=
  pullback.lift_fst _ _ _

/-- **Base change from `X` to `X_R` is an equivalence on finite étale covers, granted Tag 0A48 for
`X_R ⟶ Spec R`.** Here `R` is a henselian local `k`-algebra with residue field `k`.

The closed fibre of `X_R ⟶ Spec R` is `X` itself, because the composite `k → R → R ⧸ 𝔪` is an
isomorphism; so the closed-fibre projection is, up to an isomorphism of its source, a section of
`X_R ⟶ X`, and `isEquivalence_finiteEtaleBaseChange_pullback_fst_of_isIso_comp` turns the
hypothesis into the conclusion. -/
theorem isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_henselianPoint
    (T : HenselianPoint k k') {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (h0A48 : (finiteEtaleBaseChange (pullback.fst
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k T.carrier))))
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal T.carrier)))))).IsEquivalence) :
    (finiteEtaleBaseChange (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k T.carrier))))).IsEquivalence := by
  have hres : IsIso (CommRingCat.ofHom
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal T.carrier)).comp
        (algebraMap k T.carrier))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 T.residue_bijective
  have hcomp : IsIso (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal T.carrier))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k T.carrier))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    infer_instance
  exact isEquivalence_finiteEtaleBaseChange_pullback_fst_of_isIso_comp f _ _ h0A48

/-- **The previous result with its hypothesis supplied by Tag 0A48 for a finite morphism**: `X`
*finite* over `k` rather than merely proper. Then `X_R ⟶ Spec R` is finite, so Tag
0A48 for a finite morphism applies to it, and base change along `X_R ⟶ X` is an equivalence on
finite étale covers with nothing carried.

The conclusion is of little interest for such an `X` — a scheme finite over a field is the spectrum
of a finite `k`-algebra, so it is zero-dimensional — and this is not Tag 0A49 (for which see
`isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_isAlgClosed`). Its purpose is to witness
that the geometric step above fires on an input this library proves. -/
theorem isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_henselianPoint_of_isFinite
    (T : HenselianPoint k k') {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsFinite f] :
    (finiteEtaleBaseChange (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k T.carrier))))).IsEquivalence :=
  isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_henselianPoint T f
    (isEquivalence_finiteEtaleBaseChange_of_isFinite_of_henselianPair T.carrier
      (IsLocalRing.maximalIdeal T.carrier) (henselianPair_maximalIdeal T.carrier)
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k T.carrier)))))

end HenselianPoint

/-! ### The two inputs, and the conclusion of Tag 0A49 -/

/-- **The conclusion of Stacks Tag 0A48 for a proper scheme over a henselian local ring**: for
every henselian local ring `R` and every proper `p : Y ⟶ Spec R`, base change to the closed fibre
`Y ×_{Spec R} Spec (R ⧸ 𝔪) ⟶ Y` is an equivalence on finite étale covers.

This library proves it as `properHenselianFiniteEtaleEquivalence` (Tag 0A48, in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperHenselianLimit`). -/
def ProperHenselianFiniteEtaleEquivalence : Prop :=
  ∀ (R : Type u) [CommRing R] [HenselianLocalRing R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R)),
    IsProper p →
      (finiteEtaleBaseChange (pullback.fst p (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)))))).IsEquivalence

section Descent

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']

/-- **The spreading-out hypothesis of Tag 0A49**: every scheme finite étale over `X_{k'}` is the
base change of a scheme finite étale over `X_R`, for some henselian point `R` of `k'/k`.

For `k ⊆ k'` algebraically closed this is supplied by the source's filtered-colimit argument; see
`finiteEtaleDescendsToHenselianPoint_of_isAlgClosed`. -/
def FiniteEtaleDescendsToHenselianPoint (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) : Prop :=
  ∀ Q : FiniteEtaleOver (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))),
    ∃ (T : HenselianPoint k k')
      (P : FiniteEtaleOver (pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k T.carrier))))),
      Nonempty ((finiteEtaleBaseChange (T.baseChangeMap f)).obj P ≅ Q)

/-- **Essential surjectivity of base change to `X_{k'}`**, for `X` proper over `k`, granted the
proper case of Tag 0A48 and the spreading-out hypothesis.

A cover `Q` of `X_{k'}` descends to a cover `P` of `X_R` for a henselian point `R`; base change
from `X` to `X_R` is an equivalence by
`isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_henselianPoint`, applied to the proper
morphism `X_R ⟶ Spec R`, so `P` is the base change of a cover `U` of `X`; and `X_{k'} ⟶ X` factors
through `X_R`, so `Q` is the base change of `U`. -/
theorem essSurj_finiteEtaleBaseChange_specMap_algebraMap_of_descends {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (h0A48 : ProperHenselianFiniteEtaleEquivalence.{u})
    (hdesc : FiniteEtaleDescendsToHenselianPoint k k' f) :
    (finiteEtaleBaseChange (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).EssSurj := by
  constructor
  intro Q
  obtain ⟨T, P, ⟨ε⟩⟩ := hdesc Q
  have hR : (finiteEtaleBaseChange (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k T.carrier))))).IsEquivalence :=
    isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_henselianPoint T f
      (h0A48 T.carrier (pullback.snd f _) inferInstance)
  have hess := hR.essSurj
  refine ⟨(finiteEtaleBaseChange (pullback.fst f
    (Spec.map (CommRingCat.ofHom (algebraMap k T.carrier))))).objPreimage P, ⟨?_⟩⟩
  refine (finiteEtaleBaseChangeComp (T.baseChangeMap f) (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k T.carrier)))) _
      (T.baseChangeMap_comp_fst f).symm).app _ ≪≫ ?_
  exact (finiteEtaleBaseChange (T.baseChangeMap f)).mapIso
    (Functor.objObjPreimageIso _ P) ≪≫ ε

/-- **The conclusion of Stacks Tag 0A49, from the proper case of Tag 0A48 and the spreading-out
property taken as arguments.** Let `k'/k` be an extension of fields and let `X` be proper over
`k`. Then base change `U ↦ U_{k'}` is an equivalence between the category of schemes finite étale
over `X` and the category of schemes finite étale over `X_{k'}`.

Faithfulness is unconditional
(`faithful_finiteEtaleBaseChange_specMap_algebraMap`); fullness and essential surjectivity come
from essential surjectivity over every finite étale cover `P` of `X`, each such `P` being again
proper over `k`, and that is what the two hypotheses provide. The source states this for `k ⊆ k'`
algebraically closed, which is the case in which its filtered-colimit argument supplies the
spreading-out hypothesis; the deduction below does not use algebraic closedness. Tag 0A49
itself is `isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_isAlgClosed`, which supplies
both arguments. -/
theorem isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_properHenselian {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (h0A48 : ProperHenselianFiniteEtaleEquivalence.{u})
    (hdesc : ∀ P : FiniteEtaleOver X, FiniteEtaleDescendsToHenselianPoint k k' (P.hom ≫ f)) :
    (finiteEtaleBaseChange (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).IsEquivalence :=
  isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_essSurj f fun P =>
    have : IsProper (P.hom ≫ f) := isProper_comp_of_finiteEtaleOver f P
    essSurj_finiteEtaleBaseChange_specMap_algebraMap_of_descends (P.hom ≫ f) h0A48 (hdesc P)

end Descent

end AlgebraicGeometry

end
