module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactQuasiSeparatedPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleIdealSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionAmbient

/-!
# The closed immersion of an algebraic space into the ambient space of a square-zero extension

Given a square-zero extension of an algebraic space `X` and a charted presentation of `X`, the
thickened charts present an algebraic space `X'`. This file constructs the morphism `X ⟶ X'`
induced by the inclusions of the charts into their thickenings, and shows that it is a first-order
thickening.

## Main definitions

* `incU`: The inclusion of the presenting chart into its thickening.
* `incR`: The inclusion of the relation chart into its thickening.
* `ambQuot`: The quotient map from the thickened presenting chart to `X'`.

## Main results

* `exists_ambientMap`: There is a morphism `X ⟶ X'` compatible with the charts.
* `isPullback_chart_ambient`: The presenting chart of `X` is the base change of the thickened
  chart along `X ⟶ X'`.
* `isThickeningHom_ambientMap`: The morphism `X ⟶ X'` is a thickening.
* `isFirstOrderThickening_range_ambientMap`: The morphism `X ⟶ X'` is a first-order thickening.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

namespace SquareZeroExtension

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
  (C : ChartedPresentation B S hS f)
  (hcU : B.Contains (chartThickening B S hS E (presentationChart C.P)))
  (hcR : B.Contains (chartThickening B S hS E (presentationRelationChart C.P)))

/-- The inclusion of the presenting chart into its thickening, as a morphism of the big fppf
site over `S`. -/
def incU : C.P.U ⟶ ambU E C hcU :=
  BigFppfOver.homMk B S hS hcU _ (chartImmersion B S hS E (presentationChart C.P))
    (chartImmersion_comp_presentationThickeningToBase E C)

/-- The inclusion of the relation chart into its thickening, as a morphism of the big fppf
site over `S`. -/
def incR : C.P.R ⟶ ambR E C hcR :=
  BigFppfOver.homMk B S hS hcR _ (chartImmersion B S hS E (presentationRelationChart C.P))
    (chartImmersion_comp_relationThickeningToBase E C)

/-- The inclusions of the charts into their thickenings commute with the source maps. -/
theorem incR_comp_ambSource :
    incR E C hcR ≫ ambSource E C hcU hcR = C.P.source ≫ incU E C hcU := by
  refine BigFppfOver.map_toScheme_injective B S hS ?_
  simp only [Functor.map_comp]
  exact chartImmersion_comp_chartThickeningMap B S hS E (presentationRelationSourceHom C.P)

/-- The inclusions of the charts into their thickenings commute with the target maps. -/
theorem incR_comp_ambTarget :
    incR E C hcR ≫ ambTarget E C hcU hcR = C.P.target ≫ incU E C hcU := by
  refine BigFppfOver.map_toScheme_injective B S hS ?_
  simp only [Functor.map_comp]
  exact chartImmersion_comp_chartThickeningMap B S hS E (presentationRelationTargetHom C.P)

/-- The relation chart is the restriction of the thickened relation chart along the source leg. -/
theorem isPullback_incR :
    IsPullback (incR E C hcR) C.P.source (ambSource E C hcU hcR) (incU E C hcU) :=
  IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS)
    (isPullback_chartImmersion_chartThickeningMap B S hS E (presentationRelationSourceHom C.P))

attribute [local instance] hasSheafify_bigFppfOver

/-- The quotient map of the thickened presentation. -/
abbrev ambQuot : yoneda.obj (ambU E C hcU) ⟶ (ambient E C hcU hcR).1 :=
  quotientMap B S hS (ambSource E C hcU hcR) (ambTarget E C hcU hcR)

/-- The thickened relation chart is the fibre product of the thickened presenting chart with
itself over the quotient. -/
theorem ambQuot_isPullback :
    IsPullback (yoneda.map (ambTarget E C hcU hcR)) (yoneda.map (ambSource E C hcU hcR))
      (ambQuot E C hcU hcR) (ambQuot E C hcU hcR) :=
  quotientMap_isPullback B S hS _ _

/-- **The morphism `X ⟶ X'`** exists: the composite of the inclusion of the presenting chart into
its thickening with the quotient map descends along the atlas of `X`. -/
theorem exists_ambientMap :
    ∃ φ : X.1 ⟶ (ambient E C hcU hcR).1,
      C.P.toSpace ≫ φ = yoneda.map (incU E C hcU) ≫ ambQuot E C hcU hcR := by
  obtain ⟨hRsh, hUsh, ⟨hc⟩⟩ := isCoequalizer_of_surjectiveEtale B S hS C.P.toSpace
    C.P.source C.P.target C.P.isPullback.flip X.2 C.P.surjective C.P.etale
  let g : (⟨yoneda.obj C.P.U, hUsh⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
      ⟨(ambient E C hcU hcR).1, (ambient E C hcU hcR).2.isSheaf⟩ :=
    ⟨yoneda.map (incU E C hcU) ≫ ambQuot E C hcU hcR⟩
  have hw : (⟨yoneda.map C.P.source⟩ : (⟨yoneda.obj C.P.R, hRsh⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨yoneda.obj C.P.U, hUsh⟩) ≫ g =
      (⟨yoneda.map C.P.target⟩ : (⟨yoneda.obj C.P.R, hRsh⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨yoneda.obj C.P.U, hUsh⟩) ≫ g := by
    apply Sheaf.hom_ext
    show yoneda.map C.P.source ≫ yoneda.map (incU E C hcU) ≫ ambQuot E C hcU hcR =
      yoneda.map C.P.target ≫ yoneda.map (incU E C hcU) ≫ ambQuot E C hcU hcR
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← incR_comp_ambSource E C hcU hcR,
      ← incR_comp_ambTarget E C hcU hcR, Functor.map_comp_assoc, Functor.map_comp_assoc,
      (ambQuot_isPullback E C hcU hcR).w]
  exact ⟨(hc.desc (Cofork.ofπ g hw)).hom,
    congrArg (fun k => k.hom) (hc.fac (Cofork.ofπ g hw) WalkingParallelPair.one)⟩

variable {E C hcU hcR} (i : X ⟶ ambient E C hcU hcR)
  (hi : C.P.toSpace ≫ i.hom = yoneda.map (incU E C hcU) ≫ ambQuot E C hcU hcR)

include hi in
/-- **The presenting chart of `X` is the base change of the thickened chart along `X ⟶ X'`.** -/
theorem isPullback_chart_ambient :
    IsPullback (yoneda.map (incU E C hcU)) C.P.toSpace (ambQuot E C hcU hcR) i.hom :=
  isPullback_chart_of_isPullback_source B S hS X.2.isSheaf (ambient E C hcU hcR).2.isSheaf
    C.P.toSpace (ambQuot E C hcU hcR) i.hom C.P.surjective C.P.etale
    (quotientMap_surjective_unconditional B S hS _ _)
    (quotientMap_etale_unconditional B S hS _ _)
    C.P.isPullback.flip (ambQuot_isPullback E C hcU hcR).flip
    (incR_comp_ambSource E C hcU hcR) (incR_comp_ambTarget E C hcU hcR)
    (isPullback_incR E C hcU hcR) hi

include hi in
/-- **`X ⟶ X'` is a thickening.** It is a closed immersion surjective on points, both of which
are read on the thickened presenting chart, over which it is the thickening `U ⟶ U'`. -/
theorem isThickeningHom_ambientMap : IsThickeningHom B S hS i := by
  have hbase := isPullback_chart_ambient i hi
  have hbT : Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map (incU E C hcU)) :=
    (isFirstOrderThickening_chartImmersion B S hS E (presentationChart C.P)).isThickening
  have hbCI : IsClosedImmersion B S hS (yoneda.map (incU E C hcU)) :=
    MorphismProperty.relative_map hbT.1
  have hbS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map (incU E C hcU)) :=
    MorphismProperty.relative_map (show (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (incU E C hcU) from ⟨hbT.2⟩)
  have hqmS := quotientMap_surjective_unconditional B S hS
    (ambSource E C hcU hcR) (ambTarget E C hcU hcR)
  have hqmE := quotientMap_etale_unconditional B S hS
    (ambSource E C hcU hcR) (ambTarget E C hcU hcR)
  have hsnd : IsClosedImmersion B S hS (pullback.snd i.hom (ambQuot E C hcU hcR)) := by
    rw [← show hbase.flip.isoPullback.inv ≫ yoneda.map (incU E C hcU) =
        pullback.snd i.hom (ambQuot E C hcU hcR) by simp]
    exact MorphismProperty.RespectsIso.precomp
      ((MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf) hbase.flip.isoPullback.inv _ hbCI
  have hclosed : IsClosedImmersion B S hS i.hom := by
    refine ((isClosedImmersion_tfae B S hS X.property (ambient E C hcU hcR).property
      i.hom).out 4 1).mp ?_
    exact ⟨ambU E C hcU, ambQuot E C hcU hcR, hqmS, hqmE, hsnd⟩
  have hbPts : Function.Surjective
      (pointsMap B S hS (yoneda.obj C.P.U) (yoneda.map (incU E C hcU))) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS (yoneda.obj (ambU E C hcU))
      (isAlgebraicSpace_yoneda B S hS (ambU E C hcU)) C.P.U (yoneda.map (incU E C hcU))).mp hbS
  have hqmPts : Function.Surjective
      (pointsMap B S hS (yoneda.obj (ambU E C hcU)) (ambQuot E C hcU hcR)) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS (ambient E C hcU hcR).1
      (ambient E C hcU hcR).property (ambU E C hcU) (ambQuot E C hcU hcR)).mp hqmS
  have hbSurj : Function.Surjective (pointsMap B S hS X.1 i.hom) := by
    intro e
    obtain ⟨z, hz⟩ := hqmPts e
    obtain ⟨v, hv⟩ := hbPts z
    refine ⟨pointsMap B S hS (yoneda.obj C.P.U) C.P.toSpace v, ?_⟩
    simpa only [pointsMap_comp, Function.comp_apply, hv, hz] using
      congrFun (congrArg (pointsMap B S hS _) hi) v
  exact (isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS i).mpr ⟨hclosed, hbSurj⟩

include hi in
/-- The inverse image of the image of `X ⟶ X'` along the thickened chart is the image of the
inclusion of the presenting chart into its thickening. -/
theorem preimage_range_ambientMap :
    (Subfunctor.range i.hom).preimage (ambQuot E C hcU hcR) =
      Subfunctor.range (yoneda.map (incU E C hcU)) := by
  have hbase := isPullback_chart_ambient i hi
  ext T x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, -⟩ :=
      Types.exists_of_isPullback (hbase.map ((evaluation _ (Type u)).obj T)) x y hy.symm
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨C.P.toSpace.app T z, (ConcreteCategory.congr_hom (NatTrans.congr_app hbase.w T) z).symm⟩

include hi in
/-- **`X ⟶ X'` is a first-order thickening.** The defining ideal is read on the base change of an
arbitrary étale chart of `X'` to the thickened presenting chart, which covers it, and there it is
the ideal of the first-order thickening of the presenting chart. -/
theorem isFirstOrderThickening_range_ambientMap :
    IsFirstOrderThickening B S hS (ambient E C hcU hcR) (Subfunctor.range i.hom) := by
  have hthick := isThickeningHom_ambientMap i hi
  refine ⟨hthick.2, fun U => ?_⟩
  have hqmE := quotientMap_etale_unconditional B S hS
    (ambSource E C hcU hcR) (ambTarget E C hcU hcR)
  let g := U.1.hom
  let a := hqmE.rep.snd g
  have hpb := hqmE.rep.isPullback g
  have ha_et : Etale ((BigFppfOver.toScheme B S hS).map a) := hqmE.property g _ _ hpb
  have ha_su : Surjective ((BigFppfOver.toScheme B S hS).map a) :=
    (quotientMap_surjective_unconditional B S hS _ _).property g _ _ hpb
  let b' := yoneda.preimage (hqmE.rep.fst g)
  have hpb' : IsPullback (yoneda.map a) (yoneda.map b') g (ambQuot E C hcU hcR) := by
    rw [Functor.map_preimage]
    exact hpb.flip
  have hb'et : Etale ((BigFppfOver.toScheme B S hS).map b') := U.2.property _ _ _ hpb'
  let V' : SmallEtale B S hS ((schemeSpaceFunctor B S hS).obj (ambU E C hcU)).1 :=
    ⟨CostructuredArrow.mk (yoneda.map b'),
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ b').2 hb'et⟩
  let φ : (schemeSpaceFunctor B S hS).obj (ambU E C hcU) ⟶ ambient E C hcU hcR :=
    ObjectProperty.homMk (ambQuot E C hcU hcR)
  have hφ : IsEtale B S hS φ.hom := (isEtale_iff_presheaf_of_yoneda B S hS _).2 hqmE
  let W := (smallEtalePostcomp B S hS φ hφ).obj V'
  let k : W ⟶ U := ObjectProperty.homMk (CostructuredArrow.homMk a hpb'.w)
  have hcov : Sieve.ofArrows (fun _ : PUnit.{u + 1} => W) (fun _ => k) ∈
      SmallEtale.topology B S hS (ambient E C hcU hcR).1 U :=
    SmallEtale.ofArrows_mem_topology B S hS _ _ _ ((Scheme.ofArrows_mem_precoverage_iff @Etale).2
      ⟨fun x => ⟨⟨⟩, ha_su.surj x⟩, fun _ => ha_et⟩)
  refine definingIdealAt_pow_eq_bot_of_ofArrows B S hS (ambient E C hcU hcR) _ 1 U
    (fun _ : PUnit.{u + 1} => W) (fun _ => k) hcov fun _ => ?_
  have hfo := isFirstOrderThickening_range_yoneda_map B S hS (incU E C hcU)
    (isFirstOrderThickening_chartImmersion B S hS E (presentationChart C.P))
  rw [← definingIdealAt_preimage_eq_definingIdealAt_postcomp B S hS φ hφ _ V']
  have hsub : (⟨(Subfunctor.range i.hom).preimage φ.hom,
      isClosedSubspace_preimage B S hS φ.hom _ (ambient E C hcU hcR).2
        ((schemeSpaceFunctor B S hS).obj (ambU E C hcU)).2 hthick.2.1⟩ :
        ClosedSubspaces B S hS ((schemeSpaceFunctor B S hS).obj (ambU E C hcU)).1) =
      ⟨Subfunctor.range (yoneda.map (incU E C hcU)), hfo.1.1⟩ :=
    Subtype.ext (preimage_range_ambientMap i hi)
  rw [hsub]
  exact hfo.2 V'

end SquareZeroExtension

end AlgebraicGeometry.Space

end
