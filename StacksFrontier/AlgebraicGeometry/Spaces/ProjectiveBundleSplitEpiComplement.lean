module

public import StacksFrontier.AlgebraicGeometry.Spaces.ComplementChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalComplementAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleMapOfSplitEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SubfunctorPreimageLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion

/-!
# The complement of the projective bundle of a split quotient, over the charts

Let `X` be an algebraic space and `u : ℰ ⟶ ℰ'` a split epimorphism of finite locally free
`𝒪_X`-modules, with closed immersion `i : 𝐏(ℰ') ⟶ 𝐏(ℰ)`
(`AlgebraicGeometry.Space.projectiveBundleMapOfSplitEpi`). This file names the open complement
`U = 𝐏(ℰ) ∖ i(𝐏(ℰ'))` and reads it over the étale charts of `X`: over a chart `V` with a morphism
to the presenting chart, `P_V = 𝐏(ℰ|_V)` is `P ×_X V`, the square formed by `i` and the closed
immersion of the chart bundles `𝐏(ℰ'|_V) ⟶ 𝐏(ℰ|_V)` is cartesian, and `U ×_X V` is the open
subscheme of `P_V` on the complement of the image of that closed immersion. For
`ℰ = ℰ'' ⊕ 𝒪_X` and the projection to `ℰ''` this is the open complement of the divisor at
infinity of the projective completion, which is where the vector bundle of `ℰ''` sits.

## Main definitions

* `AlgebraicGeometry.Space.projectiveBundleSplitEpiImage`: the image of `i`, a closed subspace.
* `AlgebraicGeometry.Space.projectiveBundleSplitEpiComplement`: its open complement `U`, with its
  inclusion `AlgebraicGeometry.Space.projectiveBundleSplitEpiComplementHom`.
* `AlgebraicGeometry.Space.splitEpiComplementChart`: the object `U ×_P P_V` of the site, with its
  morphisms to `U` and to `P_V`.

## Main results

* `AlgebraicGeometry.Space.isPullback_projectiveBundleChartOfHom_mapOfSplitEpi`: the square of
  `i` over a chart is cartesian.
* `AlgebraicGeometry.Space.isPullback_splitEpiComplementChart`: `U ×_P P_V` is the fibre product.
* `AlgebraicGeometry.Space.range_splitEpiComplementChartHom`: its image in `P_V` is the
  complement of the image of the closed immersion of the chart bundles.

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

variable (E E' : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  [hE' : E'.IsQuasicoherentOnSite] (u : E ⟶ E') (σ : E' ⟶ E) (hσ : σ ≫ u = 𝟙 E')
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)
  (hfree' : SheafOfModules.IsFiniteLocallyFreeOnSite E')

/-- **The image of the closed immersion `𝐏(ℰ') ⟶ 𝐏(ℰ)` of a split quotient**, a closed subspace
of `𝐏(ℰ)`. -/
def projectiveBundleSplitEpiImage : ClosedSubspaces B S hS (projectiveBundle E hfree).1 :=
  ⟨Subfunctor.range (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom,
    isClosedSubspace_range_of_isClosedImmersion B S hS _ (projectiveBundle E' hfree').2
      (isClosedImmersion_projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree')⟩

/-- **The open complement `U = 𝐏(ℰ) ∖ i(𝐏(ℰ'))`** of the projective bundle of a split
quotient. -/
abbrev projectiveBundleSplitEpiComplement : AlgebraicSpaces B S hS :=
  openComplementSpace B S hS (projectiveBundle E hfree)
    (projectiveBundleSplitEpiImage E E' u σ hσ hfree hfree')

/-- The inclusion `U ⟶ 𝐏(ℰ)` of the open complement. -/
abbrev projectiveBundleSplitEpiComplementHom :
    projectiveBundleSplitEpiComplement E E' u σ hσ hfree hfree' ⟶ projectiveBundle E hfree :=
  openComplementHom B S hS (projectiveBundle E hfree)
    (projectiveBundleSplitEpiImage E E' u σ hσ hfree hfree')

/-- The points of the image subfunctor of `i` are the points in the image of `i`. -/
theorem range_pointsMap_projectiveBundleSplitEpiImage :
    Set.range (pointsMap B S hS _ (projectiveBundleSplitEpiImage E E' u σ hσ hfree hfree').1.ι) =
      Set.range (pointsMap B S hS _
        (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom) := by
  have : Mono (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom :=
    mono_of_isClosedImmersion B S hS _
      (isClosedImmersion_projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree')
  have := Subfunctor.isIso_toRange_of_mono
    (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom
  have hι := Subfunctor.toRange_ι (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨pointsMap B S hS _
      (inv (Subfunctor.toRange (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom)) q, ?_⟩
    refine (pointsMap_comp_apply B S hS _ _ q).symm.trans ?_
    refine congrArg (fun f => pointsMap B S hS _ f q) ?_
    exact (IsIso.inv_comp_eq
      (Subfunctor.toRange (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom)).2 hι.symm
  · rintro ⟨q, rfl⟩
    refine ⟨pointsMap B S hS _
      (Subfunctor.toRange (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom) q, ?_⟩
    exact (pointsMap_comp_apply B S hS _ _ q).symm.trans
      (congrArg (fun f => pointsMap B S hS _ f q) hι)

/-- **The points of the open complement are the points of `𝐏(ℰ)` outside the image of
`𝐏(ℰ')`.** -/
theorem range_pointsMap_projectiveBundleSplitEpiComplementHom :
    Set.range (pointsMap B S hS _ (projectiveBundleSplitEpiComplementHom E E' u σ hσ hfree
        hfree').hom) =
      (Set.range (pointsMap B S hS _
        (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom))ᶜ :=
  (range_pointsMap_ι_openComplement B S hS _).trans
    (congrArg (·ᶜ) (range_pointsMap_projectiveBundleSplitEpiImage E E' u σ hσ hfree hfree'))

/-- The morphisms `P_V ⟶ P` over a chart intertwine the closed immersions of the chart bundles
with the closed immersion `i`. -/
theorem projectiveBundleChartOfHom_comp_mapOfSplitEpi {V : SmallEtale B S hS X.1}
    (m : V ⟶ bundleBaseChart X) :
    (projectiveBundleChartOfHom E' hfree' m).hom ≫
        (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom =
      yoneda.map ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp V) ≫
        (projectiveBundleChartOfHom E hfree m).hom := by
  have h₂ := congrArg yoneda.map
    ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteMap_siteApp m)
  rw [Functor.map_comp, Functor.map_comp] at h₂
  show yoneda.map ((projectiveBundleChartFamily E' hfree').siteMap m) ≫
      projectiveBundleChart E' hfree' ≫
        (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom =
    yoneda.map ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp V) ≫
      yoneda.map ((projectiveBundleChartFamily E hfree).siteMap m) ≫ projectiveBundleChart E hfree
  rw [projectiveBundleChart_comp_projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree',
    ← Category.assoc, h₂, Category.assoc]

/-- **The square of `i : 𝐏(ℰ') ⟶ 𝐏(ℰ)` over a chart `V` with a morphism to the presenting chart
is cartesian**: `𝐏(ℰ'|_V) = 𝐏(ℰ') ×_{𝐏(ℰ)} 𝐏(ℰ|_V)`. -/
theorem isPullback_projectiveBundleChartOfHom_mapOfSplitEpi {V : SmallEtale B S hS X.1}
    (m : V ⟶ bundleBaseChart X) :
    IsPullback (projectiveBundleChartOfHom E' hfree' m).hom
      (yoneda.map ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp V))
      (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom
      (projectiveBundleChartOfHom E hfree m).hom := by
  refine IsPullback.of_bot ?_ (projectiveBundleChartOfHom_comp_mapOfSplitEpi E E' u σ hσ hfree
    hfree' m) (isPullback_projectiveBundleChartOfHom E hfree m)
  have e : (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom ≫
      (projectiveBundleProj E hfree).hom = (projectiveBundleProj E' hfree').hom :=
    congrArg (fun f => f.hom)
      (projectiveBundleMapOfSplitEpi_comp_projectiveBundleProj E E' u σ hσ hfree hfree')
  rw [← Functor.map_comp, CartesianChartFamily.Hom.siteApp_siteToChart, e]
  exact isPullback_projectiveBundleChartOfHom E' hfree' m

/-! ### The complement over a chart -/

/-- The inclusion of the open complement is representable. -/
theorem relativelyRepresentable_projectiveBundleSplitEpiComplementHom :
    yoneda.relativelyRepresentable
      (projectiveBundleSplitEpiComplementHom E E' u σ hσ hfree hfree').hom :=
  (isOpenSubspace_openComplement B S hS (projectiveBundle E hfree).2 _
    (projectiveBundleSplitEpiImage E E' u σ hσ hfree hfree').2).2.rep

/-- A point of a represented presheaf lies in the image of a morphism of the site exactly when the
point of the scheme it is lies in the image of the underlying morphism of schemes. -/
theorem pointsToScheme_mem_range_iff {A A' : BigFppfOver B S hS} (f : A' ⟶ A)
    (p : points B S hS (yoneda.obj A)) :
    pointsToScheme B S hS A p ∈ Set.range ((BigFppfOver.toScheme B S hS).map f).base ↔
      p ∈ Set.range (pointsMap B S hS _ (yoneda.map f)) := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨t', ht'⟩ := surjective_pointsToScheme B S hS A' t
    refine ⟨t', injective_pointsToScheme B S hS A ?_⟩
    rw [pointsToScheme_pointsMap_yoneda, ht', ht]
  · rintro ⟨t, rfl⟩
    exact ⟨pointsToScheme B S hS A' t, (pointsToScheme_pointsMap_yoneda B S hS f t).symm⟩

/-- **The object `U ×_P P_U` of the site** over the atlas `P_U ⟶ P` of the presenting chart. -/
abbrev splitEpiComplementAtlasChart : BigFppfOver B S hS :=
  (relativelyRepresentable_projectiveBundleSplitEpiComplementHom E E' u σ hσ hfree hfree').pullback
    (projectiveBundleChart E hfree)

/-- The open immersion `U ×_P P_U ⟶ P_U`. -/
abbrev splitEpiComplementAtlasChartHom :
    splitEpiComplementAtlasChart E E' u σ hσ hfree hfree' ⟶
      (projectiveBundleChartPresentation E hfree).U :=
  (relativelyRepresentable_projectiveBundleSplitEpiComplementHom E E' u σ hσ hfree hfree').snd
    (projectiveBundleChart E hfree)

/-- The morphism `U ×_P P_U ⟶ U`. -/
abbrev splitEpiComplementAtlasChartToComplement :
    yoneda.obj (splitEpiComplementAtlasChart E E' u σ hσ hfree hfree') ⟶
      (projectiveBundleSplitEpiComplement E E' u σ hσ hfree hfree').1 :=
  (relativelyRepresentable_projectiveBundleSplitEpiComplementHom E E' u σ hσ hfree hfree').fst
    (projectiveBundleChart E hfree)

/-- `U ×_P P_U` is the fibre product. -/
theorem isPullback_splitEpiComplementAtlasChart :
    IsPullback (splitEpiComplementAtlasChartToComplement E E' u σ hσ hfree hfree')
      (yoneda.map (splitEpiComplementAtlasChartHom E E' u σ hσ hfree hfree'))
      (projectiveBundleSplitEpiComplementHom E E' u σ hσ hfree hfree').hom
      (projectiveBundleChart E hfree) :=
  (relativelyRepresentable_projectiveBundleSplitEpiComplementHom E E' u σ hσ hfree
    hfree').isPullback (projectiveBundleChart E hfree)

/-- **`U ×_P P_U ⟶ P_U` is an open immersion of schemes.** -/
theorem isOpenImmersion_splitEpiComplementAtlasChartHom :
    _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map
        (splitEpiComplementAtlasChartHom E E' u σ hσ hfree hfree')) :=
  (isOpenSubspace_openComplement B S hS (projectiveBundle E hfree).2 _
    (projectiveBundleSplitEpiImage E E' u σ hσ hfree hfree').2).2.property_snd _

/-- Over a chart `A` of `P` whose base change of `i` is `A' ⟶ A`, the image of `U ×_P A` in `A` is
the complement of the image of `A'`. -/
private theorem range_rep_snd_projectiveBundleSplitEpiComplementHom
    {A A' : BigFppfOver B S hS} {g : yoneda.obj A ⟶ (projectiveBundle E hfree).1}
    {a : yoneda.obj A' ⟶ (projectiveBundle E' hfree').1} {f : A' ⟶ A}
    (sq : IsPullback a (yoneda.map f)
      (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom g) :
    Set.range ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_projectiveBundleSplitEpiComplementHom E E' u σ hσ hfree
          hfree').snd g)).base =
      (Set.range ((BigFppfOver.toScheme B S hS).map f).base)ᶜ := by
  refine (range_rep_snd_openComplement_eq_compl B S hS (projectiveBundle E hfree).2 _
    (projectiveBundleSplitEpiImage E E' u σ hσ hfree hfree').2 _).trans ?_
  congr 1
  ext y
  obtain ⟨p, rfl⟩ := surjective_pointsToScheme B S hS _ y
  rw [mem_range_rep_snd_iff_pointsMap_mem_range B S hS
      (projectiveBundleSplitEpiImage E E' u σ hσ hfree hfree').2.2.rep,
    range_pointsMap_projectiveBundleSplitEpiImage, pointsToScheme_mem_range_iff,
    ← preimage_range_pointsMap_of_isPullback B S hS sq]
  rfl

/-- **The image of `U ×_P P_U` in `P_U` is the complement of the image of the closed immersion of
the chart bundles** over the presenting chart. -/
theorem range_splitEpiComplementAtlasChartHom :
    Set.range ((BigFppfOver.toScheme B S hS).map
        (splitEpiComplementAtlasChartHom E E' u σ hσ hfree hfree')).base =
      (Set.range ((BigFppfOver.toScheme B S hS).map
        ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          (presentationChart (projectiveBundlePresentation X)))).base)ᶜ :=
  range_rep_snd_projectiveBundleSplitEpiComplementHom E E' u σ hσ hfree hfree'
    (isPullback_projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree')

/-- The image of `U ×_P P_U` in `P_U` misses the image of `𝐏(ℰ'|_U) ⟶ 𝐏(ℰ|_U)`, with the closed
immersion written as `Stacks.RelativeProj.projectiveBundleMapOfEpi` of the reading of `u`. -/
theorem range_splitEpiComplementAtlasChartHom_subset :
    Set.range ((BigFppfOver.toScheme B S hS).map
        (splitEpiComplementAtlasChartHom E E' u σ hσ hfree hfree')).base ⊆
      (Set.range (@Stacks.RelativeProj.projectiveBundleMapOfEpi _ _ _ _ _
        (chartModuleMap u (presentationChart (projectiveBundlePresentation X)))
        (epi_chartModuleMap u σ hσ _)).base)ᶜ :=
  (range_splitEpiComplementAtlasChartHom E E' u σ hσ hfree hfree').le

variable {V : SmallEtale B S hS X.1} (m : V ⟶ bundleBaseChart X)

/-- **The object `U ×_P P_V` of the site**, over a chart `V` with a morphism to the presenting
chart: the representing object of the base change of `U ⟶ P` along `P_V ⟶ P`. -/
abbrev splitEpiComplementChart : BigFppfOver B S hS :=
  (relativelyRepresentable_projectiveBundleSplitEpiComplementHom E E' u σ hσ hfree hfree').pullback
    (projectiveBundleChartOfHom E hfree m).hom

/-- The morphism `U ×_P P_V ⟶ P_V`, an open immersion. -/
abbrev splitEpiComplementChartHom :
    splitEpiComplementChart E E' u σ hσ hfree hfree' m ⟶
      (projectiveBundleChartFamily E hfree).site V :=
  (relativelyRepresentable_projectiveBundleSplitEpiComplementHom E E' u σ hσ hfree hfree').snd
    (projectiveBundleChartOfHom E hfree m).hom

/-- The morphism `U ×_P P_V ⟶ U`. -/
abbrev splitEpiComplementChartToComplement :
    yoneda.obj (splitEpiComplementChart E E' u σ hσ hfree hfree' m) ⟶
      (projectiveBundleSplitEpiComplement E E' u σ hσ hfree hfree').1 :=
  (relativelyRepresentable_projectiveBundleSplitEpiComplementHom E E' u σ hσ hfree hfree').fst
    (projectiveBundleChartOfHom E hfree m).hom

/-- `U ×_P P_V` is the fibre product. -/
theorem isPullback_splitEpiComplementChart :
    IsPullback (splitEpiComplementChartToComplement E E' u σ hσ hfree hfree' m)
      (yoneda.map (splitEpiComplementChartHom E E' u σ hσ hfree hfree' m))
      (projectiveBundleSplitEpiComplementHom E E' u σ hσ hfree hfree').hom
      (projectiveBundleChartOfHom E hfree m).hom :=
  (relativelyRepresentable_projectiveBundleSplitEpiComplementHom E E' u σ hσ hfree
    hfree').isPullback (projectiveBundleChartOfHom E hfree m).hom

/-- **`U ×_X V` is `U ×_P P_V`**: the square formed by `U ×_P P_V ⟶ U`, the projection
`U ×_P P_V ⟶ P_V ⟶ V`, the morphism `U ⟶ P ⟶ X` and the chart `V ⟶ X` is cartesian. -/
theorem isPullback_splitEpiComplementChart_toChart :
    IsPullback (splitEpiComplementChartToComplement E E' u σ hσ hfree hfree' m)
      (yoneda.map (splitEpiComplementChartHom E E' u σ hσ hfree hfree' m ≫
        (projectiveBundleChartFamily E hfree).siteToChart V))
      ((projectiveBundleSplitEpiComplementHom E E' u σ hσ hfree hfree').hom ≫
        (projectiveBundleProj E hfree).hom) V.obj.hom := by
  have h := (isPullback_splitEpiComplementChart E E' u σ hσ hfree hfree' m).paste_vert
    (isPullback_projectiveBundleChartOfHom E hfree m)
  rwa [← Functor.map_comp] at h

/-- **`U ×_P P_V ⟶ P_V` is an open immersion of schemes.** -/
theorem isOpenImmersion_splitEpiComplementChartHom :
    _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (splitEpiComplementChartHom E E' u σ hσ hfree hfree' m)) :=
  (isOpenSubspace_openComplement B S hS (projectiveBundle E hfree).2 _
    (projectiveBundleSplitEpiImage E E' u σ hσ hfree hfree').2).2.property_snd _

/-- **The image of `U ×_P P_V` in `P_V` is the complement of the image of the closed immersion of
the chart bundles `𝐏(ℰ'|_V) ⟶ 𝐏(ℰ|_V)`.** -/
theorem range_splitEpiComplementChartHom :
    Set.range ((BigFppfOver.toScheme B S hS).map
        (splitEpiComplementChartHom E E' u σ hσ hfree hfree' m)).base =
      (Set.range ((BigFppfOver.toScheme B S hS).map
        ((projectiveBundleChartFamilyHomOfSplitEpi E E' u σ hσ hfree hfree').siteApp
          V)).base)ᶜ :=
  range_rep_snd_projectiveBundleSplitEpiComplementHom E E' u σ hσ hfree hfree'
    (isPullback_projectiveBundleChartOfHom_mapOfSplitEpi E E' u σ hσ hfree hfree' m)

end AlgebraicGeometry.Space

end
