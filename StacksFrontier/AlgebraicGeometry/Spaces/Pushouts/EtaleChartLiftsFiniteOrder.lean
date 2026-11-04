module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralCoverByScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurjThickening

/-!
# Surjective étale scheme charts lift across finite-order thickenings

Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S` whose range is a thickening of
finite order, and let `p : U ⟶ X` be a surjective étale morphism from a scheme. Then there is a
surjective étale morphism `p' : U' ⟶ X'` from a scheme with `U = X ×_{X'} U'`, the morphism
`U ⟶ U'` being a thickening of schemes. This is the chart form of the essential surjectivity half
of [Stacks Project, Tag 05ZS], for thickenings of finite order.

## Main results

* `AlgebraicGeometry.Space.range_snd_eq_preimage_range_of_isPullback`: in a cartesian square of
  presheaves, the range of the projection to `Y` is the inverse image of the range of `X ⟶ Z`.
* `AlgebraicGeometry.Space.isFiniteOrderThickening_range_of_isPullback`: the base change of a
  thickening whose range has finite order has range of finite order.
* `AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_of_isFiniteOrderThickening`: a
  finite-order thickening of a scheme is a scheme, the finite-order case of
  [Stacks Project, Tag 05ZR].
* `AlgebraicGeometry.Space.isRepresentable_of_isFiniteOrderThickeningHom_of_isRepresentable`: the
  same in the morphism form.
* `AlgebraicGeometry.Space.exists_etaleChart_lift_of_isFiniteOrderThickening`: the lifting of
  surjective étale scheme charts across a thickening of finite order.

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 05ZP](https://stacks.math.columbia.edu/tag/05ZP)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 05ZS](https://stacks.math.columbia.edu/tag/05ZS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.Space

/-- In a cartesian square of presheaves of types, the range of the projection `P ⟶ Y` is the
inverse image along `g : Y ⟶ Z` of the range of `f : X ⟶ Z`. -/
theorem range_snd_eq_preimage_range_of_isPullback {C : Type u} [Category.{v} C]
    {P X Y Z : Cᵒᵖ ⥤ Type w} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) :
    Subfunctor.range snd = (Subfunctor.range f).preimage g := by
  ext U y
  exact Set.ext_iff.1 (Types.range_snd_of_isPullback (h.map ((evaluation _ _).obj U))) y

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The base change of a finite-order thickening has range of finite order.** In a cartesian
square of algebraic spaces over `S`, if the range of `f : F ⟶ H` is a thickening of finite order
of `H`, then the range of the projection `P ⟶ G` is a thickening of finite order of `G`. -/
theorem isFiniteOrderThickening_range_of_isPullback {F G H P : AlgebraicSpaces B S hS}
    {f : F ⟶ H} {g : G ⟶ H} {fst : P ⟶ F} {snd : P ⟶ G} (sq : IsPullback fst snd f g)
    (hf : IsFiniteOrderThickening B S hS H (Subfunctor.range f.hom)) :
    IsFiniteOrderThickening B S hS G (Subfunctor.range snd.hom) := by
  rw [range_snd_eq_preimage_range_of_isPullback (AlgebraicSpaces.isPullback_hom B S hS sq)]
  exact isFiniteOrderThickening_preimage B S hS _ g hf

attribute [local instance] pointTopology

/-- **A finite-order thickening of a scheme is a scheme.** Let `G ⊂ X'` be a thickening of
finite order of algebraic spaces over `S`. If `G` is (representable by) a scheme, then so is
`X'`. This is the case of finite order of [Stacks Project, Tag 05ZR]. -/
theorem isRepresentable_of_isRepresentable_of_isFiniteOrderThickening
    {X' : AlgebraicSpaces B S hS} {G : Subfunctor X'.1}
    (hG : IsFiniteOrderThickening B S hS X' G) (hGrep : G.toFunctor.IsRepresentable) :
    X'.1.IsRepresentable := by
  classical
  have hGt : IsThickening B S hS X' G := hG.choose_spec.1
  refine isRepresentable_of_forall_mem_isRepresentable_isOpenSubspace X'.2 fun x => ?_
  obtain ⟨g, rfl⟩ := hGt.2 x
  obtain ⟨p, rfl⟩ := Quot.exists_rep g
  obtain ⟨i, q, hq⟩ := exists_affineChart_pointsMap_eq B S hS (Functor.reprX G.toFunctor)
    (Functor.reprW G.toFunctor) p
  set V := affineChart B S hS (Functor.reprX G.toFunctor) i
  set α : yoneda.obj V ⟶ G.toFunctor :=
    yoneda.map (affineChartι B S hS (Functor.reprX G.toFunctor) i) ≫
      (Functor.reprW G.toFunctor).hom
  have hαopen : IsOpenImmersion B S hS α := by
    refine MorphismProperty.RespectsIso.postcomp _ (Functor.reprW G.toFunctor).hom _ ?_
    exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.IsOpenImmersion.{u}) _).2
      (isOpenImmersion_toScheme_map_affineChartι B S hS _ i)
  have _ : Mono α := mono_of_presheaf_isOpenImmersion hαopen
  set W := Subfunctor.range α
  have hW : IsOpenSubspace B S hS W := isOpenSubspace_range_of_isOpenImmersion V α hαopen
  obtain ⟨W', ⟨hW', hWW'⟩, -⟩ :=
    existsUnique_isOpenSubspace_preimage_eq_of_isThickening B S hS hGt W hW
  let W'sp : AlgebraicSpaces B S hS := ⟨W'.toFunctor, hW'.1⟩
  have hthick : IsFiniteOrderThickening B S hS W'sp (G.preimage W'.ι) :=
    isFiniteOrderThickening_preimage B S hS G (ObjectProperty.homMk W'.ι : W'sp ⟶ X') hG
  have e : (G.preimage W'.ι).toFunctor ≅ W.toFunctor := by
    rw [← hWW']
    exact IsPullback.isoIsPullback _ _ (Subfunctor.isPullback_preimage W'.ι G)
      (Subfunctor.isPullback_preimage G.ι W').flip
  have hWaff : IsAffineSpace B S hS W.toFunctor :=
    (isAffineSpace_yoneda B S hS V (isAffine_affineChart B S hS _ i)).of_iso
      (asIso (Subfunctor.toRange α))
  have hW'aff : IsAffineSpace B S hS W'.toFunctor :=
    isAffineSpace_of_isFiniteOrderThickening B S hS hthick (hWaff.of_iso e.symm)
  obtain ⟨T, -, ⟨eT⟩⟩ := hW'aff
  refine ⟨W', hW', isRepresentable_of_natIso _ eT.symm, ?_⟩
  obtain ⟨w, hw⟩ : Quot.mk _ p ∈
      Set.range (pointsMap B S hS (W'.preimage G.ι).toFunctor (W'.preimage G.ι).ι) := by
    rw [hWW', range_pointsMap_ι_range]
    exact ⟨_, hq⟩
  refine ⟨pointsMap B S hS _ (W'.fromPreimage G.ι) w, ?_⟩
  rw [← hw, ← pointsMap_comp_apply, ← pointsMap_comp_apply, Subfunctor.fromPreimage_ι]

/-- **A finite-order thickening of a scheme is a scheme, morphism form.** Let `i : X ⟶ X'` be a
thickening of algebraic spaces over `S` whose range is a thickening of finite order. If `X` is
(representable by) a scheme, then so is `X'`. -/
theorem isRepresentable_of_isFiniteOrderThickeningHom_of_isRepresentable
    {X X' : AlgebraicSpaces B S hS} (i : X ⟶ X') (hi : IsThickeningHom B S hS i)
    (hn : IsFiniteOrderThickening B S hS X' (Subfunctor.range i.hom))
    (hXrep : X.1.IsRepresentable) : X'.1.IsRepresentable := by
  have := hi.1
  obtain ⟨T, ⟨eT⟩⟩ := hXrep
  exact isRepresentable_of_isRepresentable_of_isFiniteOrderThickening B S hS hn
    (isRepresentable_of_natIso _
      (Functor.representableByEquiv eT ≪≫ asIso (Subfunctor.toRange i.hom)))

/-- **Surjective étale scheme charts lift across finite-order thickenings.** Every surjective
étale scheme chart `p : U ⟶ X` of an algebraic space lifts across a thickening `i : X ⟶ X'` of
algebraic spaces over `S` whose range has finite order, to a surjective étale scheme chart
`p' : U' ⟶ X'` with `U = X ×_{X'} U'`, the morphism of charts `U ⟶ U'` being a thickening of
schemes. -/
theorem exists_etaleChart_lift_of_isFiniteOrderThickening {X X' : AlgebraicSpaces B S hS}
    (i : X ⟶ X') (hi : IsThickeningHom B S hS i)
    (hn : IsFiniteOrderThickening B S hS X' (Subfunctor.range i.hom))
    {U : BigFppfOver B S hS} (p : yoneda.obj U ⟶ X.1)
    (hpsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p)
    (hpet : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p) :
    ∃ (U' : BigFppfOver B S hS) (p' : yoneda.obj U' ⟶ X'.1) (k : U ⟶ U'),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) p' ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) p' ∧
      IsPullback (yoneda.map k) p p' i.hom ∧
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k) := by
  have hmono := hi.mono
  let C : SpacesEtale B S hS X :=
    ⟨Over.mk (ObjectProperty.homMk p : representedAlgebraicSpace B S hS U ⟶ X),
      isEtale_of_presheaf_etale B S hS hpet⟩
  have := essSurj_spacesBaseChange_of_isThickeningHom B S hS i hi
  let V' := (spacesBaseChange B S hS i).functor.objPreimage C
  let ε := (SpacesEtale.toSpaces B S hS X).mapIso
    ((spacesBaseChange B S hS i).functor.objObjPreimageIso C)
  have sq : IsPullback (ε.inv ≫ (spacesBaseChange B S hS i).projection.app V')
      (ObjectProperty.homMk p : representedAlgebraicSpace B S hS U ⟶ X) V'.1.hom i := by
    refine IsPullback.of_iso ((spacesBaseChange B S hS i).isPullback V') ε (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp) ?_ (by simp) (by simp)
    rw [Iso.refl_hom, Category.comp_id]
    exact (Over.w ((spacesBaseChange B S hS i).functor.objObjPreimageIso C).hom.hom).symm
  have hthick := isThickeningHom_of_isPullback B S hS sq.flip hi
  have hthickn := isFiniteOrderThickening_range_of_isPullback B S hS sq.flip hn
  have hrep : V'.1.left.1.IsRepresentable :=
    isRepresentable_of_isFiniteOrderThickeningHom_of_isRepresentable B S hS _ hthick hthickn
      (inferInstance : (yoneda.obj U).IsRepresentable)
  let eU := Functor.reprW V'.1.left.1
  let p' : yoneda.obj (Functor.reprX V'.1.left.1) ⟶ X'.1 := eU.hom ≫ V'.1.hom.hom
  let top : yoneda.obj U ⟶ V'.1.left.1 :=
    (ε.inv ≫ (spacesBaseChange B S hS i).projection.app V').hom
  obtain ⟨k, hk0⟩ : ∃ k : U ⟶ Functor.reprX V'.1.left.1, yoneda.map k = top ≫ eU.inv :=
    ⟨_, Functor.map_preimage _ _⟩
  have sqP : IsPullback (yoneda.map k) p p' i.hom :=
    IsPullback.of_iso (AlgebraicSpaces.isPullback_hom B S hS sq) (Iso.refl _) eU.symm
      (Iso.refl _) (Iso.refl _) (by simp [hk0, top]) (by simp) (by simp [p']) (by simp)
  have hp'et : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p' :=
    V'.2 _ eU.hom (presheaf_etale_of_iso B S hS eU)
  refine ⟨Functor.reprX V'.1.left.1, p', k, ?_, hp'et, sqP, ?_⟩
  · refine (surjective_iff_pointsMap_surjective B S hS (isAlgebraicSpace_yoneda B S hS _)
      X'.2 p' hp'et.1).2 fun x' => ?_
    obtain ⟨x, rfl⟩ := hi.surjective_pointsMap x'
    obtain ⟨y, rfl⟩ := (surjective_iff_pointsMap_surjective B S hS
      (isAlgebraicSpace_yoneda B S hS _) X.2 p hpsurj.1).1 hpsurj x
    refine ⟨pointsMap B S hS _ (yoneda.map k) y, ?_⟩
    rw [← pointsMap_comp_apply, sqP.w, pointsMap_comp_apply]
  · obtain ⟨J, j, η, hpb, hjci, hjsurj⟩ :=
      exists_chart_isClosedImmersion_of_isThickening_range B S hS i hi.2 _ p'
    let φ := sqP.isoIsPullback _ _ hpb
    have hk : k = yoneda.preimage φ.hom ≫ j := by
      apply yoneda.map_injective
      rw [Functor.map_comp, Functor.map_preimage]
      exact (IsPullback.isoIsPullback_hom_fst _ _ sqP hpb).symm
    have : IsIso (yoneda.map (yoneda.preimage φ.hom)) := by
      rw [Functor.map_preimage]
      infer_instance
    have : IsIso (yoneda.preimage φ.hom) := Yoneda.fullyFaithful.isIso_of_isIso_map _
    have : Surjective ((BigFppfOver.toScheme B S hS).map j) := ⟨hjsurj⟩
    rw [hk, Functor.map_comp]
    exact ⟨inferInstance, (inferInstance : Surjective (_ ≫ _)).surj⟩

end AlgebraicGeometry.Space

end
