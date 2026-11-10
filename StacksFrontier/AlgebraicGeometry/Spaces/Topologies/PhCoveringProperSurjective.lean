module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Induction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Extension
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoverings

/-!
# A proper surjective morphism of algebraic spaces is a ph covering

Let `S` be a scheme of a big fppf site and let `f : Y ⟶ X` be a proper surjective morphism of
algebraic spaces over `S`. This file proves that the one-member family `{Y ⟶ X}` is a ph
covering in the sense of Stacks 0DFG.

## Main results

* `AlgebraicGeometry.Space.exists_properSurjective_schemeCover_of_isProper_toAffine`: an
  algebraic space proper over an affine object of the site is the target of a proper surjective
  morphism from a scheme of the site. This is Chow's lemma (**Stacks 089J**) read over the
  affine, and it is the geometric input of the main result.
* `AlgebraicGeometry.Space.isPHCovering_of_isProper_isSurjective`: **Stacks 0DFI**.

## Implementation notes

The proof is the source's. The condition to check is the one of
`AlgebraicGeometry.Space.IsPHCovering.affine_refinement`: for an affine object `U` of the site
and a point `a : h_U ⟶ X` one has to produce a standard ph covering of `U` refining the family
pulled back along `a`. The pullback `Q = Y ×_X h_U` is proper and surjective over `h_U` by
Stacks 04WP and Stacks 03MH, so the first bullet above hands over a scheme `V` of the site,
proper and surjective over `Q`; the composite `V ⟶ U` is then a proper surjection of *schemes*,
and a finite affine open covering of `V` — which exists because `V` is proper over an affine,
hence quasi-compact — is a standard ph covering of `U` by
`AlgebraicGeometry.StandardPHCovering.of_presentation`. Each of its members maps to `Q` and
hence to `Y`, which is the refinement datum.

Chow's lemma is stated over an affine base `Spec A`, while `Q` is an algebraic space over `S`.
The change of base is the equivalence of **Stacks 04SG**,
`AlgebraicGeometry.spacesOverSmallerBaseEquivalence`, between algebraic spaces over the smaller
base and algebraic spaces over `S` equipped with a morphism to the representable algebraic space
of that base: `Q` with its structural morphism to `h_U` is such an object, so it comes from an
algebraic space `Q̃` over the smaller base, whose own structural morphism is proper by
`AlgebraicGeometry.Space.isProper_relocalize_iff` and
`AlgebraicGeometry.Space.relocalizeToYoneda_eq_map_toYonedaId`. Chow's lemma applies to `Q̃`, and
the cover it produces is carried back to `S` by the lower-shriek extension of Stacks 03I5
part (2), whose value on a representable presheaf is representable
(`AlgebraicGeometry.relocalizedYonedaIso`, Stacks 03I4 part (2)).

Since Chow's lemma names the base `Spec A` for a ring `A`, the given affine object `U` is first
replaced by the isomorphic object of the site whose underlying scheme is literally
`Spec Γ(U, 𝒪)`; the comparison is `AlgebraicGeometry.Scheme.isoSpec`, and the size cutoff of
the site is insensitive to it.

## References

* [Stacks Project, Tag 0DFI](https://stacks.math.columbia.edu/tag/0DFI)
* [Stacks Project, Tag 0DFG](https://stacks.math.columbia.edu/tag/0DFG)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Chow's lemma over an affine object of the site, with the H-quasi-projectivity of the
cover.** An algebraic space `Q` over `S` which is proper over an affine object `U` of the site
admits a proper surjective morphism from an object
of the site, that is from a scheme, and that scheme is H-quasi-projective over an affine scheme
(the spectrum of the ring of functions on `U`).

The object `U` is replaced by the isomorphic object of the site whose underlying scheme is a
`Spec`, the pair `(Q, q)` is read as an algebraic space over that `Spec` through the equivalence
of **Stacks 04SG**, Chow's lemma (**Stacks 089J**) is applied there, and the resulting cover is
carried back to `S` by the lower-shriek extension of **Stacks 03I5** part (2). -/
theorem exists_properSurjective_hQuasiProjective_schemeCover_of_isProper_toAffine
    (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hQ : IsAlgebraicSpace B S hS Q)
    (q : Q ⟶ yoneda.obj U) (hq : IsProper B S hS q) :
    ∃ (V : BigFppfOver B S hS) (ρ : yoneda.obj V ⟶ Q),
      IsProper B S hS ρ ∧ IsSurjective B S hS ρ ∧
        ∃ (T : Scheme.{u}) (t : (BigFppfOver.toScheme B S hS).obj V ⟶ T),
          IsAffine T ∧ IsHQuasiProjective t := by
  classical
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  -- An isomorphic object of the site whose underlying scheme is literally a `Spec`.
  let A : CommRingCat.{u} := Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  let eT : Spec A ≅ (BigFppfOver.toScheme B S hS).obj U :=
    ((BigFppfOver.toScheme B S hS).obj U).isoSpec.symm
  have hA : B.Contains (Spec A) := (Scheme.size_congr eT).trans_lt U.left.property
  let εiso : B.obj hA ≅ U.left := B.inclusion.preimageIso eT
  let g₀ : B.obj hA ⟶ B.obj hS := εiso.hom ≫ U.hom
  let U' : BigFppfOver B S hS := Over.mk g₀
  let θ : U' ≅ U := Over.isoMk εiso rfl
  let yθ : yoneda.obj U ≅ yoneda.obj U' := yoneda.mapIso θ.symm
  let q' : Q ⟶ yoneda.obj U' := q ≫ yθ.hom
  have hq' : IsProper B S hS q' := (isProper_comp_isIso_iff B S hS q yθ.hom).mpr hq
  -- Read `(Q, q')` as an algebraic space over the smaller base `Spec A`.
  let P₀ : ObjectProperty
      (Over (yoneda.obj U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    fun Z => IsAlgebraicSpace B S hS Z.left
  let Qobj : SpacesOverSmallerBase B (Spec A) S hA hS g₀ := ⟨Over.mk q', hQ⟩
  let eqv := spacesOverSmallerBaseEquivalence B (Spec A) S hA hS g₀
  let Qt : AlgebraicSpaces B (Spec A) hA := eqv.inverse.obj Qobj
  let cIso : (spacesOverSmallerBaseFunctor B (Spec A) S hA hS g₀).obj Qt ≅ Qobj :=
    eqv.counitIso.app Qobj
  let cOver : ((spacesOverSmallerBaseFunctor B (Spec A) S hA hS g₀).obj Qt).1 ≅ (Over.mk q' :
      Over (yoneda.obj U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    (ObjectProperty.ι P₀).mapIso cIso
  let cLeft : ((spacesOverSmallerBaseFunctor B (Spec A) S hA hS g₀).obj Qt).1.left ≅ Q :=
    (Over.forget (yoneda.obj U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)).mapIso cOver
  have hcw : cLeft.hom ≫ q' =
      ((spacesOverSmallerBaseFunctor B (Spec A) S hA hS g₀).obj Qt).1.hom := Over.w cOver.hom
  -- The lower-shriek extension along `g₀`, and the comparison of `Λ Q̃` with `Q`.
  let fIso : (OverShriek.relocalizePresheafFunctor g₀).obj Qt.1 ≅
      ((spacesOverSmallerBaseFunctor B (Spec A) S hA hS g₀).obj Qt).1.left :=
    ((spacesOverSmallerBaseFunctorForgetIso B (Spec A) S hA hS g₀).app Qt).symm
  let lam : (OverShriek.relocalizePresheafFunctor g₀).obj Qt.1 ⟶ Q := (fIso ≪≫ cLeft).hom
  have : IsIso lam := (fIso ≪≫ cLeft).isIso_hom
  have hlam : lam ≫ q' = OverShriek.relocalizeToYoneda g₀ Qt.1 :=
    (Category.assoc fIso.hom cLeft.hom q').trans
      ((congrArg (fun z ↦ fIso.hom ≫ z) hcw).trans
        (relocalizeToYoneda_eq B (Spec A) S hA hS g₀ Qt))
  -- Properness of the structural morphism of `Q̃` over the smaller base.
  have hstructS : IsProper B S hS (OverShriek.relocalizeToYoneda g₀ Qt.1) := by
    rw [← hlam]
    exact (isProper_isIso_comp_iff B S hS lam q').mpr hq'
  have : IsIso (OverShriek.relocalizeToYoneda g₀
      (yoneda.obj (Over.mk (𝟙 (B.obj hA))) : (BigFppfOver B (Spec A) hA)ᵒᵖ ⥤ Type u)) :=
    isIso_relocalizeToYoneda_yonedaId B (Spec A) S hA hS g₀
  have hstruct : IsProper B (Spec A) hA (toYonedaId B (Spec A) hA Qt.1) := by
    refine (isProper_relocalize_iff B (Spec A) hA S hS g₀ Qt.2
      (isAlgebraicSpace_yoneda B (Spec A) hA (Over.mk (𝟙 (B.obj hA))))
      (toYonedaId B (Spec A) hA Qt.1)).mp ?_
    refine (isProper_comp_isIso_iff B S hS
      ((OverShriek.relocalizePresheafFunctor g₀).map (toYonedaId B (Spec A) hA Qt.1))
      (OverShriek.relocalizeToYoneda g₀
        (yoneda.obj (Over.mk (𝟙 (B.obj hA))) : (BigFppfOver B (Spec A) hA)ᵒᵖ ⥤ Type u))).mp ?_
    rw [relocalizeToYoneda_eq_map_toYonedaId B (Spec A) S hA hS g₀ Qt.1]
    exact hstructS
  -- Chow's lemma over `Spec A`.
  obtain ⟨V', p, hpProper, hpSurj, hpHqp⟩ :=
    hasChowSchemeCover_of_isSeparated_isFiniteType B A hA Qt.1 Qt.2
      (toYonedaId B (Spec A) hA Qt.1) hstruct.1 hstruct.2.1
  -- Carry the cover back to the base `S`.
  let yIso := relocalizedYonedaIso B (B.obj hA) (B.obj hS) g₀ V'
  refine ⟨(Over.map g₀).obj V',
    yIso.inv ≫ (OverShriek.relocalizePresheafFunctor g₀).map p ≫ lam, ?_, ?_,
    ⟨Spec A, B.inclusion.map V'.hom, inferInstance, hpHqp⟩⟩
  · have h1 : IsProper B S hS ((OverShriek.relocalizePresheafFunctor g₀).map p) :=
      (isProper_relocalize_iff B (Spec A) hA S hS g₀
        (isAlgebraicSpace_yoneda B (Spec A) hA V') Qt.2 p).mpr hpProper
    have h2 : IsProper B S hS ((OverShriek.relocalizePresheafFunctor g₀).map p ≫ lam) :=
      (isProper_comp_isIso_iff B S hS
        ((OverShriek.relocalizePresheafFunctor g₀).map p) lam).mpr h1
    exact (isProper_isIso_comp_iff B S hS yIso.inv
      ((OverShriek.relocalizePresheafFunctor g₀).map p ≫ lam)).mpr h2
  · have h1 : IsSurjective B S hS ((OverShriek.relocalizePresheafFunctor g₀).map p) :=
      isSurjective_relocalize B (Spec A) hA S hS g₀ p hpSurj
    exact isSurjective_comp B S hS (isSurjective_of_isIso B S hS yIso.inv)
      (isSurjective_comp B S hS h1 (isSurjective_of_isIso B S hS lam))

/-- **Chow's lemma over an affine object of the site.** An algebraic space `Q` over `S` which is
proper over an affine object `U` of the site admits a proper surjective morphism from an object
of the site, that is from a scheme.

The object `U` is replaced by the isomorphic object of the site whose underlying scheme is a
`Spec`, the pair `(Q, q)` is read as an algebraic space over that `Spec` through the equivalence
of **Stacks 04SG**, Chow's lemma (**Stacks 089J**) is applied there, and the resulting cover is
carried back to `S` by the lower-shriek extension of **Stacks 03I5** part (2). -/
theorem exists_properSurjective_schemeCover_of_isProper_toAffine
    (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hQ : IsAlgebraicSpace B S hS Q)
    (q : Q ⟶ yoneda.obj U) (hq : IsProper B S hS q) :
    ∃ (V : BigFppfOver B S hS) (ρ : yoneda.obj V ⟶ Q),
      IsProper B S hS ρ ∧ IsSurjective B S hS ρ := by
  obtain ⟨V, ρ, hρp, hρs, -⟩ :=
    exists_properSurjective_hQuasiProjective_schemeCover_of_isProper_toAffine B S hS U hU hQ q hq
  exact ⟨V, ρ, hρp, hρs⟩

/-- **Stacks 0DFI.** A proper surjective morphism of algebraic spaces over `S`, regarded as a
one-member family, is a ph covering.

Over an affine object `U` of the site the pullback `Y ×_X h_U` is proper and surjective over
`h_U`, so Chow's lemma over `U` — in the form
`AlgebraicGeometry.Space.exists_properSurjective_schemeCover_of_isProper_toAffine` — produces a
proper surjective morphism of schemes `V ⟶ U` which factors through that pullback. A finite
affine open covering of `V` is then a standard ph covering of `U`, and it refines the family
pulled back along `a` through the factorization. -/
@[stacks 0DFI]
theorem isPHCovering_of_isProper_isSurjective
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hp : IsProper B S hS f) (hs : IsSurjective B S hS f) :
    IsPHCovering B S hS (fun _ : Unit ↦ X') (fun _ ↦ f) := by
  classical
  refine ⟨hX, fun _ ↦ hX', fun _ ↦ hp.2.1.1, ?_⟩
  intro U hU a
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  -- The pullback of `f` along `a`, proper and surjective over `h_U`.
  let Xs : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Xs' : AlgebraicSpaces B S hS := ⟨X', hX'⟩
  let Us : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let fS : Xs' ⟶ Xs := ObjectProperty.homMk f
  let aS : Us ⟶ Xs := ObjectProperty.homMk a
  let Qs := AlgebraicSpaces.fiberProduct B S hS fS aS
  have hsq : IsPullback
      (ObjectProperty.homMk (pullback.fst fS.hom aS.hom) : Qs ⟶ Xs')
      (ObjectProperty.homMk (pullback.snd fS.hom aS.hom) : Qs ⟶ Us) fS aS :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS fS aS
  have hqProper : IsProper B S hS (pullback.snd f a) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃V W : AlgebraicSpaces B S hS⦄ (m : V ⟶ W) => IsProper B S hS m.hom)
      hsq hp
  have hqSurj : IsSurjective B S hS (pullback.snd f a) :=
    isSurjective_of_isPullback B S hS hsq hs
  -- Chow's lemma over `U`.
  obtain ⟨V, ρ, hρProper, hρSurj⟩ :=
    exists_properSurjective_schemeCover_of_isProper_toAffine B S hS U hU Qs.property
      (pullback.snd f a) hqProper
  -- The composite `V ⟶ U` is a proper surjection of schemes.
  let m : V ⟶ U := yoneda.preimage (ρ ≫ pullback.snd f a)
  have hm : yoneda.map m = ρ ≫ pullback.snd f a := yoneda.map_preimage _
  have hcompProper : IsProper B S hS (ρ ≫ pullback.snd f a) :=
    isProper_comp B S hS (isAlgebraicSpace_yoneda B S hS V) Qs.property Us.property
      ρ (pullback.snd f a) hρProper hqProper
  have hcompSurj : IsSurjective B S hS (ρ ≫ pullback.snd f a) :=
    isSurjective_comp B S hS hρSurj hqSurj
  have hmOf (P : MorphismProperty Scheme.{u})
      (hpre : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map m)) : P ((BigFppfOver.toScheme B S hS).map m) :=
  by
    have hrel : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).relative yoneda
        (yoneda.map m) := hpre
    have hpm := MorphismProperty.of_relative_map hrel
    exact hpm
  have hmProper : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map m) :=
    hmOf (@_root_.AlgebraicGeometry.IsProper.{u}) (by
      rw [hm]
      exact (presheaf_isProper_iff B S hS (ρ ≫ pullback.snd f a)
        (isAlgebraicSpace_yoneda B S hS V) Us.property
        (by rw [← hm]; exact Functor.relativelyRepresentable.map yoneda m)).mp hcompProper)
  have hmSurj : _root_.AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map m) :=
    hmOf (@_root_.AlgebraicGeometry.Surjective.{u}) (by
      rw [hm]
      exact (presheafSurjective_iff_isSurjective_yoneda B S hS Us.1 Us.property V
        (ρ ≫ pullback.snd f a)).mpr hcompSurj)
  -- A finite affine open covering of `V` is a standard ph covering of `U`.
  let : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map m) := hmProper
  let : CompactSpace ((BigFppfOver.toScheme B S hS).obj V) :=
    (quasiCompact_iff_compactSpace ((BigFppfOver.toScheme B S hS).map m)).mp inferInstance
  let VA := ((BigFppfOver.toScheme B S hS).obj V).affineCover.finiteSubcover
  have hVAff (i : VA.I₀) : IsAffine (VA.X i) := inferInstance
  have hVOpen (i : VA.I₀) : _root_.AlgebraicGeometry.IsOpenImmersion (VA.f i) := inferInstance
  have hVContained (i : VA.I₀) : B.Contains (VA.X i) :=
    Scheme.size_lt_of_isOpenImmersion (VA.f i) V.left.property
  let obj (i : VA.I₀) : BigFppfOver B S hS :=
    Over.mk ((B.inclusion.preimage
      (show B.inclusion.obj (B.obj (hVContained i)) ⟶
        B.inclusion.obj V.left from VA.f i)) ≫ V.hom)
  let r (i : VA.I₀) : obj i ⟶ V :=
    Over.homMk (B.inclusion.preimage
      (show B.inclusion.obj (B.obj (hVContained i)) ⟶
        B.inclusion.obj V.left from VA.f i)) (by simp [obj])
  have hr (i : VA.I₀) : (BigFppfOver.toScheme B S hS).map (r i) = VA.f i :=
    B.inclusion.map_preimage _
  let E : PreZeroHypercover.{u} U := ⟨VA.I₀, obj, fun i ↦ r i ≫ m⟩
  let : Finite ((E.map (BigFppfOver.toScheme B S hS)).I₀) := inferInstanceAs (Finite VA.I₀)
  have hstandard : StandardPHCovering (E.map (BigFppfOver.toScheme B S hS)).f := by
    refine StandardPHCovering.of_presentation
      (f := (E.map (BigFppfOver.toScheme B S hS)).f)
      hVAff ((BigFppfOver.toScheme B S hS).map m) (fun i ↦ VA.f i) hmProper hmSurj
      hVOpen VA.iUnion_range ?_
    intro i
    change VA.f i ≫ (BigFppfOver.toScheme B S hS).map m =
      (BigFppfOver.toScheme B S hS).map (r i) ≫ (BigFppfOver.toScheme B S hS).map m
    rw [hr i]
  have hpc : pullback.fst f a ≫ f = pullback.snd f a ≫ a := pullback.condition
  have hcond : (ρ ≫ pullback.fst f a) ≫ f = yoneda.map m ≫ a :=
    (Category.assoc ρ (pullback.fst f a) f).trans
      ((congrArg (fun z ↦ ρ ≫ z) hpc).trans
        ((Category.assoc ρ (pullback.snd f a) a).symm.trans
          (congrArg (fun z ↦ z ≫ a) hm.symm)))
  refine ⟨E, hstandard, ⟨⟨fun _ ↦ (), fun i ↦ yoneda.map (r i) ≫ ρ ≫ pullback.fst f a, ?_⟩⟩⟩
  intro i
  change (yoneda.map (r i) ≫ ρ ≫ pullback.fst f a) ≫ f = yoneda.map (r i ≫ m) ≫ a
  exact (Category.assoc (yoneda.map (r i)) (ρ ≫ pullback.fst f a) f).trans
    ((congrArg (fun z ↦ yoneda.map (r i) ≫ z) hcond).trans
      ((Category.assoc (yoneda.map (r i)) (yoneda.map m) a).symm.trans
        (congrArg (fun z ↦ z ≫ a) (yoneda.map_comp (r i) m).symm)))

end AlgebraicGeometry.Space

end
