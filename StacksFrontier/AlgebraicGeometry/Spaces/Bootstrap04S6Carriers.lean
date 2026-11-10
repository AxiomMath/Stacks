module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSheafSpaceCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.OpenRelationEtaleQuotient
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheafAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.GroupActionQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.InlineBootstrapForm
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SeparatedQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFppfCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlasCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackRepresentableDiagonal

/-!
# The forms of the bootstrap theorem carried in the library, from its condition (3)

[Stacks, Tag 04S6] lists conditions on a functor `F` on the big fppf site of a scheme `S`, each
of which makes `F` an algebraic space.  The library carries that theorem as a hypothesis in
several shapes.  The canonical one is condition (3),
`AlgebraicGeometry.Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection`: a sheaf which receives
a morphism from an algebraic space that is representable by algebraic spaces, surjective, flat
and locally of finite presentation is an algebraic space.  This module proves, for every other
shape, that condition (3) implies it.  Once condition (3) is proved, these implications
discharge every carried form of 04S6.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_of_relativelyRepresentable_of_isBootstrap`: the
  inline form, in which the chart is representable by objects of the site with surjective, flat,
  locally finitely presented represented base changes.  This is the `h04S6` binder of Stacks
  04SK, 04U0, 04TB and of the torsor and cohomology files.  It is proved in
  `StacksFrontier/AlgebraicGeometry/Spaces/Representable/Bootstrap/InlineBootstrapForm.lean`, which
  this module imports: that file sits below Stacks 04SK in the import graph, and this one above.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_isBootstrap_of_fppfLocalChart`: condition (3) for
  a chart whose base changes become surjective, flat and locally of finite presentation over an
  algebraic space after one fppf base change.
* `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_isBootstrap`: condition (1) for an
  equivalence relation of presheaves whose source and target are algebraic spaces and whose
  source map is flat and locally of finite presentation.

## Implementation notes

The inline form is condition (3) for a chart which happens to be representable by objects of the
site.  Such a chart is representable by algebraic spaces by Stacks 025Z.  Its represented base
changes are morphisms of schemes, so their surjectivity, flatness and local finite presentation
give the corresponding properties of Stacks 03XZ, via
`AlgebraicGeometry.Space.hasProperty_surjectiveMorphismProperty_of_presheaf` and the étale-chart
bridge of Stacks 03MJ.

Condition (1) follows from condition (3) applied to the quotient map `π : U ⟶ U/R`.  This is the
converse of the source's own reduction, which goes from (3) through (5) to (1).  The one
substantive point is that `π` is representable by algebraic spaces, with surjective, flat and
locally finitely presented base changes.  Fix a scheme-valued point `ξ : h_T ⟶ U/R`.  Since `π`
is a surjection of fppf sheaves, `ξ` lifts to `a : h_V ⟶ U` along a *single* surjective, flat,
locally finitely presented morphism `f : V ⟶ T` of the site:
`AlgebraicGeometry.Space.exists_single_fppf_lift_of_isLocallySurjective` refines a covering
family by a size-bounded one and takes its coproduct, which lies in the site.  Since
`R = U ×_{U/R} U` (`AlgebraicGeometry.Space.isPullback_toQuotientSheaf`), the base change of
`h_T ×_{U/R} U ⟶ h_T` along `f` is `h_V ×_{a, U, s} R ⟶ h_V`, a base change of the source map
`s`.  So `h_T ×_{U/R} U` receives from the algebraic space `h_V ×_U R` a base change of `f`,
which is representable by schemes, surjective, flat and locally of finite presentation.  The
inline form makes it an algebraic space.  The three properties then descend along the one-member
fppf covering `{h_V ⟶ h_T}`, because they are local on the base (Stacks 041Q, 041W, 06ET).
Surjectivity of `s` comes from reflexivity of the relation.

Nothing in this module carries a Stacks tag.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04S1](https://stacks.math.columbia.edu/tag/04S1)
* [Stacks Project, Tag 04SK](https://stacks.math.columbia.edu/tag/04SK)
* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 046O](https://stacks.math.columbia.edu/tag/046O)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Lifting a section along a single fppf covering morphism -/

/-- A morphism of schemes which agrees, up to an isomorphism of its source, with the map out of
the coproduct of an fppf covering is flat, locally of finite presentation and surjective. -/
theorem _root_.FppfCovering.flat_lfp_surjective_of_iso_sigmaDesc {Y Z : Scheme.{u}}
    (W : FppfCovering.{u} Y) (e : ∐ W.X ≅ Z) {φ : Z ⟶ Y} (hφ : e.hom ≫ φ = Sigma.desc W.f) :
    Flat φ ∧ LocallyOfFinitePresentation φ ∧ Surjective φ := by
  have : ∀ i, Flat (W.f i) := W.flat
  have : ∀ i, LocallyOfFinitePresentation (W.f i) := W.lfp
  have : MorphismProperty.RespectsIso (@Flat.{u}) := Flat.isStableUnderBaseChange.respectsIso
  have : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  have : MorphismProperty.RespectsIso (@LocallyOfFinitePresentation.{u}) :=
    locallyOfFinitePresentation_isStableUnderBaseChange.respectsIso
  refine ⟨?_, ?_, ?_⟩
  · apply (MorphismProperty.cancel_left_of_respectsIso (@Flat.{u}) e.hom _).mp
    rw [hφ]
    infer_instance
  · apply (MorphismProperty.cancel_left_of_respectsIso
      (@LocallyOfFinitePresentation.{u}) e.hom _).mp
    rw [hφ]
    exact IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFinitePresentation.{u}) W.lfp
  · constructor
    intro t
    obtain ⟨i, a, ha⟩ := W.jointly_surjective t
    refine ⟨e.hom ((Sigma.ι W.X i) a), ?_⟩
    exact (congrArg (fun q : W.X i ⟶ Y => q a)
      (show Sigma.ι W.X i ≫ e.hom ≫ φ = W.f i by rw [hφ, Sigma.ι_comp_desc])).trans ha

/-- **A section of a sheaf which is locally in the image of a map of sheaves lifts along a single
surjective, flat, locally finitely presented morphism of the site.**

Let `π : X ⟶ Q` be a locally surjective morphism of fppf sheaves on the big fppf site of `S` and
let `ξ` be a section of `Q` over `T`.  Then there is a morphism `f : V ⟶ T` of the site whose
underlying morphism of schemes is flat, locally of finite presentation and surjective, and over
which the restriction of `ξ` comes from a section of `X`.

The covering on which `ξ` lifts is refined to one of bounded size, whose coproduct lies in the
site.  The lifts glue over that coproduct because its members are disjoint. -/
theorem exists_single_fppf_lift_of_isLocallySurjective
    {X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hQ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q) (π : X ⟶ Q)
    (hπ : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) π)
    (T : BigFppfOver B S hS) (ξ : Q.obj (op T)) :
    ∃ (V : BigFppfOver B S hS) (f : V ⟶ T),
      Flat ((BigFppfOver.toScheme B S hS).map f) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map f) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map f) ∧
      ∃ a : X.obj (op V), π.app (op V) a = Q.map f.op ξ := by
  classical
  have hR := Presheaf.imageSieve_mem (BigFppfOver.topology B S hS) π ξ
  obtain ⟨W, hcard, hsize, hmem⟩ := Stack.exists_small_fppf_refinement_in_sieve B S hS hR
  have hW i : B.Contains (W.X i) := (hsize i).trans_lt T.left.property
  let wi i : B.obj (hW i) ⟶ T.left := B.inclusion.preimage (W.f i)
  let Wi i : BigFppfOver B S hS := Over.mk (wi i ≫ T.hom)
  let fi i : Wi i ⟶ T := Over.homMk (wi i)
  have hfi i : Presheaf.imageSieve π ξ (fi i) := by
    have hi := hmem i (hW i)
    rwa [Sieve.overEquiv_iff] at hi
  have hsum : B.Contains (∐ (fun i => (BigFppfOver.toScheme B S hS).obj (Wi i))) :=
    (schemeSize_coproduct_le W.X T.left.obj.size T.left.obj.aleph0_le_size hcard
      hsize).trans_lt T.left.property
  obtain ⟨V, j, ⟨hV⟩, e, he⟩ := Stack.exists_coproduct_of_contains B S hS Wi hsum
  obtain ⟨hm, hj, hd⟩ := Stack.coproduct_cover B S hS Wi V j e he
  let f : V ⟶ T := Cofan.IsColimit.desc hV fi
  have hfac i : j i ≫ f = fi i := Cofan.IsColimit.fac hV fi i
  have hmap : e.hom ≫ B.inclusion.map f.left = Sigma.desc W.f := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [← Category.assoc, he i]
    change B.inclusion.map (j i).left ≫ B.inclusion.map f.left = _
    rw [← B.inclusion.map_comp]
    change B.inclusion.map (j i ≫ f).left = _
    rw [hfac, Sigma.ι_comp_desc]
    exact B.inclusion.map_preimage (X := B.obj (hW i)) (Y := T.left) (W.f i)
  obtain ⟨hfFlat, hfLfp, hfSurj⟩ := W.flat_lfp_surjective_of_iso_sigmaDesc e hmap
  choose a ha using hfi
  obtain ⟨s, hs⟩ := Stack.exists_section_of_disjoint_cover (BigFppfOver.topology B S hS)
    Wi V j hm hj hd X hX a
  refine ⟨V, f, hfFlat, hfLfp, hfSurj, s, ?_⟩
  refine (((isSheaf_iff_isSheaf_of_type _ Q).1 hQ) _ hj).isSeparatedFor.ext fun Y g hg => ?_
  obtain ⟨_, h, _, ⟨i⟩, rfl⟩ := hg
  calc Q.map (h ≫ j i).op (π.app (op V) s)
      = Q.map h.op (π.app _ (X.map (j i).op s)) := by
        rw [op_comp, Functor.map_comp_apply, NatTrans.naturality_apply]
    _ = Q.map h.op (Q.map (fi i).op ξ) := by rw [hs i, ha i]
    _ = Q.map (h ≫ j i).op (Q.map f.op ξ) := by
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
          ← op_comp, Category.assoc, hfac]

/-! ### Condition (3) from a chart which is flat after one fppf base change -/

/-- Surjective, flat, locally finitely presented morphisms of schemes are stable under base
change. -/
theorem isStableUnderBaseChange_surjective_inf_flat_inf_lfp :
    MorphismProperty.IsStableUnderBaseChange
      (@Surjective.{u} ⊓ @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u} :
        MorphismProperty Scheme.{u}) := by
  have : MorphismProperty.IsStableUnderBaseChange
      (@Surjective.{u} ⊓ @Flat.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  exact MorphismProperty.IsStableUnderBaseChange.inf

/-- Surjectivity of morphisms of algebraic spaces is local on the base for the fppf topology. -/
instance isLocalAtTarget_fppf_surjectiveMorphismProperty :
    (surjectiveMorphismProperty B S hS).IsLocalAtTarget
      (Topology.fppf.precoverage.{u, 0} B S hS) :=
  (surjective_isLocalAtTarget_fpqc B S hS).of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

/-- Flatness of morphisms of algebraic spaces is local on the base for the fppf topology. -/
instance isLocalAtTarget_fppf_flatProperty :
    (flatProperty B S hS).IsLocalAtTarget (Topology.fppf.precoverage.{u, 0} B S hS) :=
  (isFlat_isLocalAtTarget_fpqc B S hS).of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

/-- Local finite presentation of morphisms of algebraic spaces is local on the base for the fppf
topology. -/
instance isLocalAtTarget_fppf_locallyOfFinitePresentationProperty :
    (locallyOfFinitePresentationProperty B S hS).IsLocalAtTarget
      (Topology.fppf.precoverage.{u, 0} B S hS) :=
  (isLocallyOfFinitePresentation_isLocalAtTarget_fpqc B S hS).of_le
    (fppfPrecoverage_le_fpqcPrecoverage B S hS)

/-- Granted condition (3), a base change `h_T ×_Y X` of a map of sheaves `π : X ⟶ Y` is an
algebraic space once it receives, from an algebraic space, a base change of a surjective, flat,
locally finitely presented morphism `f : V ⟶ T` of the site. -/
theorem isAlgebraicSpace_pullback_of_isPullback_fppf
    (hboot : IsBootstrapAlgebraicSpaceAlongFlatSurjection B S hS)
    {X Y P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : X ⟶ Y)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    {T V : BigFppfOver B S hS} (ξ : yoneda.obj T ⟶ Y) {f : V ⟶ T} {g : P ⟶ yoneda.obj V}
    {k : P ⟶ pullback ξ π} (hP : IsAlgebraicSpace B S hS P)
    (hfF : Flat ((BigFppfOver.toScheme B S hS).map f))
    (hfL : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map f))
    (hfS : Surjective ((BigFppfOver.toScheme B S hS).map f))
    (hsq : IsPullback k g (pullback.fst ξ π) (yoneda.map f)) :
    IsAlgebraicSpace B S hS (pullback ξ π) := by
  have := inverseImage_isStableUnderBaseChange B S hS
    isStableUnderBaseChange_surjective_inf_flat_inf_lfp
  have hf : (MorphismProperty.inverseImage
      (@Surjective.{u} ⊓ @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u} :
        MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map f) :=
    MorphismProperty.relative_map (F := yoneda) ⟨⟨hfS, hfF⟩, hfL⟩
  have hk := presheaf_of_isPullback B S hS hsq.flip hf
  exact isAlgebraicSpace_of_relativelyRepresentable_of_isBootstrap B S hS hboot _
    (Presheaf.isSheaf_pullback _ ξ π (isAlgebraicSpace_yoneda B S hS T).isSheaf hX hY)
    _ hP k hk.rep hk

/-- A property of morphisms of algebraic spaces which is local on the base for the fppf topology
holds for `q : P ⟶ h_T` once it holds for its base change along a surjective, flat, locally
finitely presented morphism `f : V ⟶ T` of the site. -/
theorem of_isPullback_yoneda_map_of_fppf (Q : MorphismProperty (AlgebraicSpaces B S hS))
    [Q.IsLocalAtTarget (Topology.fppf.precoverage.{u, 0} B S hS)]
    {T V : BigFppfOver B S hS} {f : V ⟶ T}
    (hfF : Flat ((BigFppfOver.toScheme B S hS).map f))
    (hfL : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map f))
    (hfS : Surjective ((BigFppfOver.toScheme B S hS).map f))
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    {PV : AlgebraicSpaces B S hS} {q : P ⟶ yoneda.obj T} {k : PV.obj ⟶ P}
    {g : PV.obj ⟶ yoneda.obj V} (hsq : IsPullback k g q (yoneda.map f))
    (hg : Q (ObjectProperty.homMk g :
      PV ⟶ ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)) :
    Q (ObjectProperty.homMk q : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) := by
  let To : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  let Vo : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  let Po : AlgebraicSpaces B S hS := ⟨P, hP⟩
  let qo : Po ⟶ To := ObjectProperty.homMk q
  let cover : Vo ⟶ To := ObjectProperty.homMk (yoneda.map f)
  let ko : PV ⟶ Po := ObjectProperty.homMk k
  let fo : PV ⟶ Vo := ObjectProperty.homMk g
  have hSquare : IsPullback ko fo qo cover :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι (fun Z => IsAlgebraicSpace B S hS Z)) hsq
  have hcov : Topology.IsCovering .fppf B S hS (I := PUnit.{1})
      (Yi := fun _ => yoneda.obj V) (g := fun _ => yoneda.map f) :=
    ⟨isAlgebraicSpace_yoneda B S hS T, fun _ => isAlgebraicSpace_yoneda B S hS V,
      isFppfCovering_yoneda_map B S hS (fun _ => V) (fun _ => f) (fun _ => hfF)
        (fun _ => hfL) (fun x => by
          obtain ⟨y, hy⟩ := hfS.surj x
          exact ⟨PUnit.unit, y, hy⟩)⟩
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := Q)
    (K := Topology.fppf.precoverage.{u, 0} B S hS) (f := qo)
    (R := Presieve.ofArrows (ι := PUnit.{1}) (fun _ => Vo) (fun _ => cover))
    ⟨PUnit.{1}, fun _ => Vo, fun _ => cover, rfl, hcov⟩
  rintro _ w _ ⟨i⟩
  exact (Q.cancel_left_of_respectsIso hSquare.isoPullback.hom (pullback.snd qo cover)).mp
    (by rwa [hSquare.isoPullback_hom_snd])

/-- **Stacks 04S6, condition (3), from a chart whose base changes are fppf-locally surjective,
flat and locally of finite presentation.**  Let `π : X ⟶ Y` be a morphism from an algebraic space
to an fppf sheaf on the big fppf site of `S`.  Suppose that every scheme-valued point
`ξ : h_T ⟶ Y`, after restriction along one surjective, flat, locally finitely presented
morphism `f : V ⟶ T` of the site, has as base change `h_V ×_Y X` an algebraic space `P` over `V`
whose structure map is surjective, flat and locally of finite presentation.  Granted
condition (3), `Y` is an algebraic space.

The base change `h_T ×_Y X` receives from `P` a base change of `f`, so it is an algebraic space by
the inline form of condition (3); its three properties descend along the one-member fppf covering
`{h_V ⟶ h_T}`, being local on the base (Stacks 041Q, 041W, 06ET).  So `π` is representable by
algebraic spaces, surjective, flat and locally of finite presentation, and condition (3) applies
to it. -/
theorem isAlgebraicSpace_of_isBootstrap_of_fppfLocalChart
    (hboot : IsBootstrapAlgebraicSpaceAlongFlatSurjection B S hS)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : X ⟶ Y)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y) (hX : IsAlgebraicSpace B S hS X)
    (key : ∀ (T : BigFppfOver B S hS) (ξ : yoneda.obj T ⟶ Y),
      ∃ (V : BigFppfOver B S hS) (f : V ⟶ T) (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
        (g : P ⟶ yoneda.obj V) (k : P ⟶ pullback ξ π),
        IsAlgebraicSpace B S hS P ∧
        Flat ((BigFppfOver.toScheme B S hS).map f) ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map f) ∧
        Surjective ((BigFppfOver.toScheme B S hS).map f) ∧
        IsPullback k g (pullback.fst ξ π) (yoneda.map f) ∧
        IsSurjective B S hS g ∧ IsFlat B S hS g ∧ IsLocallyOfFinitePresentation B S hS g) :
    IsAlgebraicSpace B S hS Y := by
  have hπrep : IsRepresentableByAlgebraicSpaces B S hS π := by
    intro T ξ
    obtain ⟨V, f, P, g, k, hPV, hfF, hfL, hfS, hsq, -, -, -⟩ := key T ξ
    exact isAlgebraicSpace_pullback_of_isPullback_fppf B S hS hboot π hY hX.isSheaf ξ hPV
      hfF hfL hfS hsq
  -- A property local on the base which the charts `g` have, `π` has too.
  have hprop : ∀ (Q : MorphismProperty (AlgebraicSpaces B S hS))
      [Q.IsLocalAtTarget (Topology.fppf.precoverage.{u, 0} B S hS)],
      (∀ {Pv : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Vv : BigFppfOver B S hS}
        (g : Pv ⟶ yoneda.obj Vv) (hPv : IsAlgebraicSpace B S hS Pv),
        IsSurjective B S hS g ∧ IsFlat B S hS g ∧ IsLocallyOfFinitePresentation B S hS g →
        Q (ObjectProperty.homMk g : (⟨Pv, hPv⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj Vv, isAlgebraicSpace_yoneda B S hS Vv⟩)) →
      HasProperty B S hS Q π hπrep := by
    intro Q _ hsel T ξ
    obtain ⟨V, f, P, g, k, hPV, hfF, hfL, hfS, hsq, hgS, hgF, hgL⟩ := key T ξ
    exact of_isPullback_yoneda_map_of_fppf B S hS Q hfF hfL hfS (hπrep T ξ) (PV := ⟨P, hPV⟩)
      hsq (hsel g hPV ⟨hgS, hgF, hgL⟩)
  exact hboot π hY hX hπrep
    (hprop (surjectiveMorphismProperty B S hS) fun _ _ h => h.1)
    (hprop (flatProperty B S hS) fun _ _ h => h.2.1)
    (hprop (locallyOfFinitePresentationProperty B S hS) fun _ _ h => h.2.2)

/-! ### Condition (1): the quotient of a flat equivalence relation -/

section Quotient

variable {B S hS} [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : Over Z}

/-- The base change of the quotient map `U ⟶ U/R` along a scheme-valued point `ξ : h_T ⟶ U/R`
becomes, after one surjective, flat, locally finitely presented morphism `f : V ⟶ T` of the
site, a base change `h_V ×_U R ⟶ h_V` of the source map of the relation. -/
theorem exists_fppf_isPullback_pullback_toQuotientSheaf (j : PreRelation R U)
    (hR : IsAlgebraicSpace B S hS R.left) (hU : IsAlgebraicSpace B S hS U.left)
    (hj : IsEquivalenceRelation j.target j.source) (T : BigFppfOver B S hS)
    (ξ : yoneda.obj T ⟶ (quotientSheaf j).obj) :
    ∃ (V : BigFppfOver B S hS) (f : V ⟶ T) (aV : yoneda.obj V ⟶ U.left)
      (k : pullback aV j.source.left ⟶ pullback ξ (toQuotientSheaf j)),
      Flat ((BigFppfOver.toScheme B S hS).map f) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map f) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map f) ∧
      IsPullback k (pullback.fst aV j.source.left) (pullback.fst ξ (toQuotientSheaf j))
        (yoneda.map f) := by
  have hpull : IsPullback j.source.left j.target.left (toQuotientSheaf j) (toQuotientSheaf j) :=
    isPullback_toQuotientSheaf j hj hR.isSheaf hU.isSheaf
  obtain ⟨V, f, hfF, hfL, hfS, a, ha⟩ := exists_single_fppf_lift_of_isLocallySurjective B S hS
    hU.isSheaf (quotientSheaf j).property (toQuotientSheaf j)
    (isLocallySurjective_toQuotientSheaf j) T (yonedaEquiv ξ)
  let aV : yoneda.obj V ⟶ U.left := yonedaEquiv.symm a
  have haV : aV ≫ toQuotientSheaf j = yoneda.map f ≫ ξ := by
    apply yonedaEquiv.injective
    rw [← yonedaEquiv_naturality, yonedaEquiv_comp]
    simpa only [aV, Equiv.apply_symm_apply] using ha
  have hpaste : IsPullback (pullback.snd aV j.source.left ≫ j.target.left)
      (pullback.fst aV j.source.left) (toQuotientSheaf j) (yoneda.map f ≫ ξ) := by
    rw [← haV]
    exact (IsPullback.of_hasPullback aV j.source.left).flip.paste_horiz hpull.flip
  exact ⟨V, f, aV, _, hfF, hfL, hfS,
    IsPullback.of_right' hpaste (IsPullback.of_hasPullback ξ (toQuotientSheaf j)).flip⟩

/-- **Stacks 04S6, condition (1), from condition (3).**  Let `j : R ⟶ U ×_Z U` be an equivalence
relation of presheaves on the big fppf site of `S` whose source and target are algebraic spaces,
and whose source map is flat and locally of finite presentation.  Granted condition (3), the
quotient sheaf `U/R` is an algebraic space.

The quotient map `U ⟶ U/R` is shown to be representable by algebraic spaces, surjective, flat
and locally of finite presentation, and condition (3) is applied to it; see the module
docstring.  Neither the base `Z` nor the target map of the relation needs a hypothesis: the
relation is symmetric. -/
theorem isAlgebraicSpace_quotientSheaf_of_isBootstrap
    (hboot : IsBootstrapAlgebraicSpaceAlongFlatSurjection B S hS) (j : PreRelation R U)
    (hR : IsAlgebraicSpace B S hS R.left) (hU : IsAlgebraicSpace B S hS U.left)
    (hj : IsEquivalenceRelation j.target j.source)
    (hsF : IsFlat B S hS j.source.left)
    (hsL : IsLocallyOfFinitePresentation B S hS j.source.left) :
    IsAlgebraicSpace B S hS (quotientSheaf j).obj := by
  -- Reflexivity of the relation makes its source map surjective.
  obtain ⟨E⟩ := hj.nonempty_equivalenceRelation
  have hrefl : E.r.left ≫ j.source.left = 𝟙 _ := by
    rw [← Over.comp_left, E.reflexivity₂, Over.id_left]
  have hsS : IsSurjective B S hS j.source.left := fun x =>
    ⟨pointsMap B S hS _ E.r.left x, by
      rw [← pointsMap_comp_apply, hrefl, pointsMap_id]
      rfl⟩
  -- A property stable under base change which the source map has, its base changes have too.
  have hprop : ∀ (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
      {V : BigFppfOver B S hS} (aV : yoneda.obj V ⟶ U.left),
      P (ObjectProperty.homMk j.source.left :
        (⟨R.left, hR⟩ : AlgebraicSpaces B S hS) ⟶ ⟨U.left, hU⟩) →
      P (ObjectProperty.homMk (pullback.fst aV j.source.left) :
        AlgebraicSpaces.fiberProduct B S hS (ObjectProperty.homMk aV :
          representedAlgebraicSpace B S hS V ⟶ ⟨U.left, hU⟩)
          (ObjectProperty.homMk j.source.left :
            (⟨R.left, hR⟩ : AlgebraicSpaces B S hS) ⟶ ⟨U.left, hU⟩) ⟶
        representedAlgebraicSpace B S hS V) := fun P _ V aV hPs =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS _ _).flip hPs
  -- The base change of `π` along a scheme-valued point, after one fppf covering morphism, is a
  -- base change of the source map.
  have key := exists_fppf_isPullback_pullback_toQuotientSheaf j hR hU hj
  refine isAlgebraicSpace_of_isBootstrap_of_fppfLocalChart B S hS hboot (toQuotientSheaf j)
    (quotientSheaf j).property hU fun T ξ => ?_
  obtain ⟨V, f, aV, k, hfF, hfL, hfS, hsq⟩ := key T ξ
  exact ⟨V, f, _, _, k, isAlgebraicSpace_pullback B S hS aV j.source.left
    (isAlgebraicSpace_yoneda B S hS V) hR hU, hfF, hfL, hfS, hsq,
    hprop (surjectiveMorphismProperty B S hS) aV hsS, hprop (flatProperty B S hS) aV hsF,
    hprop (locallyOfFinitePresentationProperty B S hS) aV hsL⟩

end Quotient

end AlgebraicGeometry.Space

end
