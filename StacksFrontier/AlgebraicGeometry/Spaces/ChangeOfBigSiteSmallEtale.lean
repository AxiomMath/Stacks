module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteSmoothEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleIsoCongr
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.StandardCoveringSieves
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds
public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# The small étale site of an algebraic space after enlarging the big fppf site

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B`, let `X`
be an algebraic space over `S` defined using `B`, and let `X'` be the algebraic space over `S`
defined using `B'` that Stacks 03FP attaches to it
(`AlgebraicGeometry.changeBigSite`). An étale chart `U ⟶ X` with `U` an object of `B` is a
point of `X` with values in `U`; transporting that point along the bijection
`X(U) ≃ X'(U)` of Stacks 04W1 (`AlgebraicGeometry.changeBigSiteSectionEquiv`) gives a chart
`U ⟶ X'` with the same scheme, which is again étale. This is a functor

`AlgebraicGeometry.Space.changeBigSiteSmallEtale : X_{étale} ⥤ X'_{étale}`

between the small étale sites, and it is fully faithful.

## Main definitions

* `AlgebraicGeometry.Space.changeBigSiteChart`: the transported chart.
* `AlgebraicGeometry.Space.changeBigSiteSmallEtale`: the functor on small étale sites.

## Main results

* `AlgebraicGeometry.Space.isEtaleChart_changeBigSiteChart`: the transport of an étale chart is
  an étale chart.
* `AlgebraicGeometry.Space.changeBigSiteSmallEtale_full`,
  `AlgebraicGeometry.Space.changeBigSiteSmallEtale_faithful`: the functor is fully faithful.

## Implementation notes

The chart is defined through its point, by `CategoryTheory.yonedaEquiv`, rather than as a
composite of morphisms of presheaves, so that its functoriality is the naturality of the
bijection on points (`AlgebraicGeometry.changeBigSiteSectionEquiv_restrict`) and nothing else.
Its étaleness is read off a second description, as the canonical comparison
`AlgebraicGeometry.changeBigSiteYonedaHom` of Stacks 03FP, part (1), followed by the image of
the chart under the change of big site, which is étale by
`AlgebraicGeometry.changeBigSite_isEtale`; the two descriptions agree by
`AlgebraicGeometry.changeBigSiteSectionEquiv_map`.

## References

* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The point of `X` with values in the scheme of a chart. -/
abbrev chartElement {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : CostructuredArrow yoneda F) :
    F.obj (op U.left) :=
  yonedaEquiv U.hom

/-- **The transport of a scheme chart of `X` to the enlarged site.** Its scheme is the scheme of
the chart, read in `B'`, and its point is the transport of the point of the chart along the
bijection `X(U) ≃ X'(U)` of Stacks 04W1. -/
def changeBigSiteChart (U : CostructuredArrow yoneda X.obj) :
    CostructuredArrow yoneda ((changeBigSite B B' h S hS).obj X).obj :=
  CostructuredArrow.mk (Y := (inclusionOver h S hS).obj U.left)
    (yonedaEquiv.symm (changeBigSiteSectionEquiv B B' h S hS X U.left (chartElement B S hS U)))

/-- A chart `U` of `X`, read as a morphism of algebraic spaces from the space of its scheme. -/
private abbrev chartHomMk (U : CostructuredArrow yoneda X.obj) :=
  ObjectProperty.homMk (P := fun F => IsAlgebraicSpace B S hS F)
    (X := (schemeSpaceFunctor B S hS).obj U.left) (Y := X) U.hom

/-- The point of the transported chart is the transported point. -/
theorem chartElement_changeBigSiteChart (U : CostructuredArrow yoneda X.obj) :
    chartElement B' S (largerContains h hS) (changeBigSiteChart B B' h S hS X U) =
      changeBigSiteSectionEquiv B B' h S hS X U.left (chartElement B S hS U) :=
  yonedaEquiv.apply_symm_apply _

/-- The transported chart is the canonical comparison of Stacks 03FP, part (1), followed by the
image of the chart under the change of big site. -/
theorem changeBigSiteChart_hom (U : CostructuredArrow yoneda X.obj) :
    (changeBigSiteChart B B' h S hS X U).hom =
      changeBigSiteYonedaHom B B' h S hS U.left ≫
        ((changeBigSite B B' h S hS).map
          (ObjectProperty.homMk (P := fun F => IsAlgebraicSpace B S hS F)
            (X := (schemeSpaceFunctor B S hS).obj U.left) (Y := X) U.hom)).hom := by
  apply yonedaEquiv.injective
  refine (yonedaEquiv.apply_symm_apply _).trans ?_
  exact (changeBigSiteSectionEquiv_map B B' h S hS
    (chartHomMk B S hS X U) U.left (𝟙 U.left)).trans
    ((congrArg (((changeBigSite B B' h S hS).map (chartHomMk B S hS X U)).hom.app _)
        (yonedaEquiv.apply_symm_apply _).symm).trans
      (yonedaEquiv_comp (changeBigSiteYonedaHom B B' h S hS U.left) _).symm)


/-- An étale chart of an algebraic space, read as a morphism of algebraic spaces, is étale: its
composite with an étale chart of its source is an étale chart, étale charts being closed under
composition. -/
theorem isEtale_hom_of_isEtaleChart {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : CostructuredArrow yoneda F} (hU : IsEtaleChart B S hS F U) :
    IsEtale B S hS U.hom := by
  intro V ψ hψ
  have := inverseImage_isStableUnderBaseChange B S hS
    AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
  have := inverseImage_isStableUnderComposition B S hS
    etale_isStableUnderComposition.{u}
  exact MorphismProperty.comp_mem _ _ _ hψ hU

/-- **The transport of an étale chart is an étale chart.** -/
theorem isEtaleChart_changeBigSiteChart {U : CostructuredArrow yoneda X.obj}
    (hU : IsEtaleChart B S hS X.obj U) :
    IsEtaleChart B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj
      (changeBigSiteChart B B' h S hS X U) := by
  have hφ := changeBigSite_isEtale B B' h S hS (chartHomMk B S hS X U)
    (isEtale_hom_of_isEtaleChart B S hS hU)
  have hc : IsEtaleChart B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj ((schemeSpaceFunctor B S hS).obj U.left)).obj
      (CostructuredArrow.mk (𝟙 _ ≫ (changeBigSiteYonedaIso B B' h S hS U.left).hom)) :=
    (isEtaleChart_comp_iso_iff B' S (largerContains h hS)
      (changeBigSiteYonedaIso B B' h S hS U.left) (𝟙 _)).2
      (presheaf_etale_id B' S (largerContains h hS) _)
  change MorphismProperty.presheaf _ (changeBigSiteChart B B' h S hS X U).hom
  rw [changeBigSiteChart_hom]
  have hc' : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B' S (largerContains h hS)))
        (changeBigSiteYonedaHom B B' h S hS U.left) := by
    change MorphismProperty.presheaf _ (𝟙 _ ≫ changeBigSiteYonedaHom B B' h S hS U.left) at hc
    exact (congrArg (fun k => MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B' S (largerContains h hS))) k) (Category.id_comp _)).mp hc
  exact hφ _ _ hc'

/-- The transported chart of the source of a morphism of charts maps to the transported chart of
its target, by the same morphism of schemes. -/
theorem changeBigSiteChart_w {U V : CostructuredArrow yoneda X.obj} (g : U ⟶ V) :
    yoneda.map ((inclusionOver h S hS).map g.left) ≫ (changeBigSiteChart B B' h S hS X V).hom =
      (changeBigSiteChart B B' h S hS X U).hom := by
  apply yonedaEquiv.injective
  refine (yonedaEquiv_naturality _ _).symm.trans ?_
  change ((changeBigSite B B' h S hS).obj X).obj.map _
      (chartElement B' S (largerContains h hS) (changeBigSiteChart B B' h S hS X V)) =
    chartElement B' S (largerContains h hS) (changeBigSiteChart B B' h S hS X U)
  rw [chartElement_changeBigSiteChart, chartElement_changeBigSiteChart]
  refine (changeBigSiteSectionEquiv_restrict B B' h S hS X g.left _).symm.trans ?_
  refine congrArg (changeBigSiteSectionEquiv B B' h S hS X U.left) ?_
  change X.obj.map g.left.op (yonedaEquiv V.hom) = yonedaEquiv U.hom
  rw [yonedaEquiv_naturality, CostructuredArrow.w g]

/-- A morphism of schemes of `B` between charts whose image in `B'` is a morphism of the
transported charts is a morphism of the charts. -/
theorem w_of_changeBigSiteChart {U V : CostructuredArrow yoneda X.obj} (b : U.left ⟶ V.left)
    (hb : yoneda.map ((inclusionOver h S hS).map b) ≫ (changeBigSiteChart B B' h S hS X V).hom =
      (changeBigSiteChart B B' h S hS X U).hom) :
    yoneda.map b ≫ V.hom = U.hom := by
  apply yonedaEquiv.injective
  apply (changeBigSiteSectionEquiv B B' h S hS X U.left).injective
  refine (congrArg _ (yonedaEquiv_naturality _ _).symm).trans ?_
  rw [changeBigSiteSectionEquiv_restrict]
  have hb' := (yonedaEquiv_naturality _ _).trans (congrArg yonedaEquiv hb)
  change ((changeBigSite B B' h S hS).obj X).obj.map _
      (chartElement B' S (largerContains h hS) (changeBigSiteChart B B' h S hS X V)) =
    chartElement B' S (largerContains h hS) (changeBigSiteChart B B' h S hS X U) at hb'
  rwa [chartElement_changeBigSiteChart, chartElement_changeBigSiteChart] at hb'

/-- **The small étale site of `X` maps to the small étale site of `X'`.** An étale chart is sent
to its transport, and a morphism of charts to the same morphism of schemes. -/
def changeBigSiteSmallEtale :
    SmallEtale B S hS X.obj ⥤
      SmallEtale B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj where
  obj U := ⟨changeBigSiteChart B B' h S hS X U.obj,
    isEtaleChart_changeBigSiteChart B B' h S hS X U.property⟩
  map {U V} g := ObjectProperty.homMk
    (CostructuredArrow.homMk ((inclusionOver h S hS).map g.hom.left)
      (changeBigSiteChart_w B B' h S hS X g.hom))
  map_id U := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    exact (inclusionOver h S hS).map_id _
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    exact (inclusionOver h S hS).map_comp _ _

/-- The image of an étale chart `U` under `changeBigSiteSmallEtale` is the transported chart of
`U`. -/
@[simp]
theorem changeBigSiteSmallEtale_obj_obj (U : SmallEtale B S hS X.obj) :
    ((changeBigSiteSmallEtale B B' h S hS X).obj U).obj =
      changeBigSiteChart B B' h S hS X U.obj := rfl

/-- The image of a morphism of étale charts under `changeBigSiteSmallEtale` has as underlying
morphism the image of the original one under `inclusionOver`. -/
@[simp]
theorem changeBigSiteSmallEtale_map_hom_left {U V : SmallEtale B S hS X.obj} (g : U ⟶ V) :
    ((changeBigSiteSmallEtale B B' h S hS X).map g).hom.left =
      (inclusionOver h S hS).map g.hom.left := rfl

/-- The functor `changeBigSiteSmallEtale` is faithful. -/
instance changeBigSiteSmallEtale_faithful : (changeBigSiteSmallEtale B B' h S hS X).Faithful where
  map_injective {U V} f g hfg := by
    have : (inclusionOver h S hS).Faithful := inclusionOver_faithful h S hS
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    exact (inclusionOver h S hS).map_injective
      (congrArg (fun k => k.hom.left) hfg)

/-- The functor `changeBigSiteSmallEtale` is full. -/
instance changeBigSiteSmallEtale_full : (changeBigSiteSmallEtale B B' h S hS X).Full where
  map_surjective {U V} f := by
    have : (inclusionOver h S hS).Full := inclusionOver_full h S hS
    let b := (inclusionOver h S hS).preimage f.hom.left
    have hb : yoneda.map ((inclusionOver h S hS).map b) ≫
        (changeBigSiteChart B B' h S hS X V.obj).hom =
          (changeBigSiteChart B B' h S hS X U.obj).hom :=
      (congrArg (fun k => yoneda.map k ≫ (changeBigSiteChart B B' h S hS X V.obj).hom)
        (Functor.map_preimage _ _)).trans (CostructuredArrow.w f.hom)
    refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk b
      (w_of_changeBigSiteChart B B' h S hS X b hb)), ?_⟩
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    exact Functor.map_preimage (inclusionOver h S hS) f.hom.left


/-! ### Two constructions on small étale sites -/

namespace SmallEtale

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism of the big fppf site between the objects underlying two étale charts, which
factors a morphism of charts through a second one, is a morphism of charts. -/
def homOfFac {P Q R : SmallEtale B S hS F} (r : Q ⟶ R) (p : P ⟶ R)
    (l : P.obj.left ⟶ Q.obj.left) (hl : l ≫ r.hom.left = p.hom.left) : P ⟶ Q :=
  ObjectProperty.homMk (CostructuredArrow.homMk l (by
    rw [← CostructuredArrow.w r.hom, ← Category.assoc, ← Functor.map_comp, hl,
      CostructuredArrow.w p.hom]))

/-- The underlying morphism of `homOfFac r p l hl` is `l`. -/
@[simp]
theorem homOfFac_hom_left {P Q R : SmallEtale B S hS F} (r : Q ⟶ R) (p : P ⟶ R)
    (l : P.obj.left ⟶ Q.obj.left) (hl : l ≫ r.hom.left = p.hom.left) :
    (homOfFac r p l hl).hom.left = l := rfl

/-- A family of étale morphisms of `Sch_κ` into the scheme of an étale chart `U`, read as a
family of étale charts over `U`: each member is the composite of its morphism with the chart. -/
def liftFamily (U : SmallEtale B S hS F)
    (V : PreZeroHypercover.{u + 1} ((toSchemes B S hS F).obj U))
    (hV : ∀ j, Etale (B.inclusion.map (V.f j))) : PreZeroHypercover.{u + 1} U where
  I₀ := V.I₀
  X j := ⟨CostructuredArrow.mk
      (yoneda.map (Over.homMk (V.f j) rfl : Over.mk (V.f j ≫ U.obj.left.hom) ⟶ U.obj.left) ≫
        U.obj.hom),
    etale_comp_of_scheme B S hS _ U.obj.hom (hV j) U.property⟩
  f j := ObjectProperty.homMk (CostructuredArrow.homMk (Over.homMk (V.f j) rfl) rfl)

/-- The image of `liftFamily U V hV` under `toSchemes` is the family `V`. -/
theorem liftFamily_map (U : SmallEtale B S hS F)
    (V : PreZeroHypercover.{u + 1} ((toSchemes B S hS F).obj U))
    (hV : ∀ j, Etale (B.inclusion.map (V.f j))) :
    (liftFamily U V hV).map (toSchemes B S hS F) = V := by
  ext <;> simp [liftFamily, PreZeroHypercover.map]

/-- A chosen étale covering family of the scheme of an étale chart lifts to a covering family of
the chart. -/
theorem isCovering_liftFamily (U : SmallEtale B S hS F)
    (V : PreZeroHypercover.{u + 1} ((toSchemes B S hS F).obj U))
    (hV' : ∀ j, Etale (B.inclusion.map (V.f j))) (hV : B.etaleCovering ⟨_, V⟩) :
    IsCovering B S hS F ⟨U, liftFamily U V hV'⟩ := by
  change B.etaleCovering ⟨_, (liftFamily U V hV').map (toSchemes B S hS F)⟩
  rw [liftFamily_map]
  exact hV

end SmallEtale


/-! ### Covering families of the enlarged small étale site are refined by small ones -/

/-- The members of a chosen étale covering family are étale. -/
private theorem etale_inclusion_map_of_etaleCovering {B : BigFppfSite.{u}} {T : B.Schemes}
    {E : PreZeroHypercover.{u + 1} T} (hE : B.etaleCovering ⟨T, E⟩) (j : E.I₀) :
    Etale (B.inclusion.map (E.f j)) :=
  ((Scheme.presieve₀_mem_precoverage_iff (E.map B.inclusion)).mp hE.2).2 j

/-- A point in the image of a morphism lies in the image of an affine open of the source. -/
private theorem exists_affineOpens_ι_apply_eq {Z Y : Scheme.{u}} (p : Z ⟶ Y) {y : Z} {x : Y}
    (hy : p y = x) : ∃ A : Z.affineOpens, ∃ z : (A : Z.Opens), p (A.1.ι z) = x := by
  obtain ⟨A, hA, hyA, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens)
    (show y ∈ (⊤ : Z.Opens) from trivial)
  exact ⟨⟨A, hA⟩, ⟨y, hyA⟩, by simpa using hy⟩

/-- **A covering family of `X'_{étale}` pulled back to a transported chart is refined by a
covering family of `X_{étale}`.** Let `a : U' ⟶ V` be a morphism from the transport `U'` of an
étale chart `U` of `X` to an étale chart `V` of `X'`, and let `E` be a covering family of `V`.
Then there is a covering family of `U` in the small étale site of `X` whose members, transported
and composed with `a`, factor through members of `E`.

The base change of `E` along `a` is a covering family of `U` in `B'`, whose members may be too big
for `B`. Their affine opens are not: they are affine and étale over the scheme of `U`, which
belongs to `B` (`AlgebraicGeometry.size_lt_cutoff_of_isAffine_of_locallyOfFiniteType`). The family
of all those affine opens is an étale covering family of the scheme of `U` with members in `B`,
hence tautologically equivalent to a chosen étale covering family of `B`
(`AlgebraicGeometry.Space.exists_etaleCovering_tautologicallyEquivalent`), which is then lifted
to the small étale site of `X`. -/
theorem exists_isCovering_changeBigSiteSmallEtale_refinement (U : SmallEtale B S hS X.obj)
    {V : SmallEtale B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj}
    (a : (changeBigSiteSmallEtale B B' h S hS X).obj U ⟶ V)
    (E : PreZeroHypercover.{u + 1} V)
    (hE : SmallEtale.IsCovering B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj X).obj ⟨V, E⟩) :
    ∃ F : PreZeroHypercover.{u + 1} U, SmallEtale.IsCovering B S hS X.obj ⟨U, F⟩ ∧
      ∀ j, Sieve.generate E.presieve₀
        ((changeBigSiteSmallEtale B B' h S hS X).map (F.f j) ≫ a) := by
  let G := changeBigSiteSmallEtale B B' h S hS X
  let X' := ((changeBigSite B B' h S hS).obj X).obj
  let hS' : B'.Contains S := largerContains h hS
  let H' := SmallEtale.inclusion B' S hS' X'
  let L' := SmallEtale.toSchemes B' S hS' X'
  let L := SmallEtale.toSchemes B S hS X.obj
  let T := L.obj U
  let X₀ := L'.obj (G.obj U)
  let U₀ := L'.obj V
  let E₀ := E.map L'
  change B'.etaleCovering ⟨U₀, E₀⟩ at hE
  obtain ⟨P, π₁, π₂, hpb, hcov⟩ := B'.coverings_isSite.2.2
    ⟨U₀, E₀⟩ hE.1 X₀ (L'.map a)
  let P₀ : PreZeroHypercover X₀ := {
    I₀ := E₀.I₀
    X i := P i
    f i := π₂ i }
  have hP₀ : B'.IsCovering ⟨X₀, P₀⟩ := hcov
  have hEetale := etale_inclusion_map_of_etaleCovering hE
  have hpb' (i : E₀.I₀) : IsPullback (B'.inclusion.map (π₁ i)) (B'.inclusion.map (π₂ i))
      (B'.inclusion.map (E₀.f i)) (B'.inclusion.map (L'.map a)) :=
    Functor.map_isPullback B'.inclusion (hpb i)
  have hπ₂ (i : E₀.I₀) : Etale (B'.inclusion.map (π₂ i)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (hpb' i) (hEetale i)
  have hjoint : ∀ x : B'.inclusion.obj X₀, ∃ i, ∃ y, B'.inclusion.map (π₂ i) y = x := by
    have hfp0 : AlgebraicGeometry.IsFppfCovering ⟨X₀, P₀⟩ :=
      B'.isFppfCovering_of_isCovering hP₀
    have hfp : (P₀.map B'.inclusion).presieve₀ ∈
        Scheme.fppfPrecoverage (B'.inclusion.obj X₀) := by
      simpa [AlgebraicGeometry.IsFppfCovering, PreZeroHypercover.presieve₀_map] using hfp0
    exact ((Scheme.presieve₀_mem_precoverage_iff (P₀.map B'.inclusion)).mp hfp).1
  let W : PreZeroHypercover.{u + 1} (B.inclusion.obj T) := {
    I₀ := Σ i : E₀.I₀, (B'.inclusion.obj (P i)).affineOpens
    X j := (j.2 : (B'.inclusion.obj (P j.1)).Opens).toScheme
    f j := (j.2 : (B'.inclusion.obj (P j.1)).Opens).ι ≫ B'.inclusion.map (π₂ j.1) }
  have hWet (j : W.I₀) : Etale (W.f j) := by
    have := hπ₂ j.1
    change Etale ((j.2 : (B'.inclusion.obj (P j.1)).Opens).ι ≫ B'.inclusion.map (π₂ j.1))
    infer_instance
  have hW : W.presieve₀ ∈ Scheme.etalePrecoverage (B.inclusion.obj T) := by
    refine (Scheme.presieve₀_mem_precoverage_iff W).mpr ⟨fun x => ?_, hWet⟩
    obtain ⟨i, y, hy⟩ := hjoint x
    obtain ⟨A, z, hz⟩ := exists_affineOpens_ι_apply_eq (B'.inclusion.map (π₂ i)) hy
    exact ⟨⟨i, A⟩, z, hz⟩
  have hsize (j : W.I₀) : B.Contains (W.X j) := by
    have := hWet j
    have : IsAffine (W.X j) := j.2.2
    exact size_lt_cutoff_of_isAffine_of_locallyOfFiniteType .fppf B (W.f j) T.property
  obtain ⟨Vf, hV, hEq⟩ := exists_etaleCovering_tautologicallyEquivalent B T W hW hsize
  have hVet := etale_inclusion_map_of_etaleCovering hV
  let F := SmallEtale.liftFamily U Vf hVet
  refine ⟨F, SmallEtale.isCovering_liftFamily U Vf hVet hV, fun (j : Vf.I₀) => ?_⟩
  obtain ⟨β, hβ⟩ := hEq.2
  obtain ⟨e, he⟩ := hβ j
  let i := (β j).1
  let m : B.inclusion.obj (Vf.X j) ⟶ B'.inclusion.obj (E₀.X i) :=
    e.hom ≫ ((β j).2 : (B'.inclusion.obj (P i)).Opens).ι ≫ B'.inclusion.map (π₁ i)
  have hm : m ≫ B'.inclusion.map (E₀.f i) =
      B.inclusion.map (Vf.f j) ≫ B'.inclusion.map (L'.map a) := by
    have hw := (hpb' i).w
    have he' : e.hom ≫ ((β j).2 : (B'.inclusion.obj (P i)).Opens).ι ≫
        B'.inclusion.map (π₂ i) = B.inclusion.map (Vf.f j) := he
    change (e.hom ≫ ((β j).2 : (B'.inclusion.obj (P i)).Opens).ι ≫ B'.inclusion.map (π₁ i)) ≫
      B'.inclusion.map (E₀.f i) = _
    rw [← he']
    simp only [Category.assoc, hw]
    rfl
  have h1 : (E.f i).hom.left.left ≫ V.obj.left.hom = (E.X i).obj.left.hom :=
    Over.w (E.f i).hom.left
  have h2 : a.hom.left.left ≫ V.obj.left.hom = (G.obj U).obj.left.hom := Over.w a.hom.left
  have eq1 : B'.inclusion.map (E.X i).obj.left.hom =
      B'.inclusion.map (E₀.f i) ≫ B'.inclusion.map V.obj.left.hom := by
    rw [← h1]
    exact B'.inclusion.map_comp _ _
  have eq2 : B'.inclusion.map (L'.map a) ≫ B'.inclusion.map V.obj.left.hom =
      B'.inclusion.map (G.obj U).obj.left.hom := by
    rw [← h2]
    exact (B'.inclusion.map_comp _ _).symm
  have hstr : m ≫ B'.inclusion.map (E.X i).obj.left.hom =
      B.inclusion.map (Vf.f j) ≫ B'.inclusion.map (G.obj U).obj.left.hom :=
    (congrArg (m ≫ ·) eq1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ B'.inclusion.map V.obj.left.hom) hm).trans
        ((Category.assoc _ _ _).trans (congrArg (B.inclusion.map (Vf.f j) ≫ ·) eq2))))
  let lm : (G.obj (F.X j)).obj.left ⟶ (E.X i).obj.left :=
    Over.homMk (ObjectProperty.homMk m) (by
      apply ObjectProperty.hom_ext
      exact hstr)
  have hl : lm ≫ (E.f i).hom.left = (G.map (F.f j) ≫ a).hom.left := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hm
  refine ⟨_, SmallEtale.homOfFac (E.f i) (G.map (F.f j) ≫ a) lm hl, E.f i, ⟨i⟩, ?_⟩
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  exact hl


/-! ### The transport of a surjective étale chart -/

/-- The comparison of Stacks 03FP, part (1) is locally surjective, being an isomorphism. -/
theorem isLocallySurjective_changeBigSiteYonedaHom (T : BigFppfOver B S hS) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B' S (largerContains h hS))
      (changeBigSiteYonedaHom B B' h S hS T) :=
  @Presheaf.isLocallySurjective_of_iso _ _ _ _ _ _ _ _ _ _ _ _
    (isIso_changeBigSiteYonedaHom B B' h S hS T)

/-- **The transport of a surjective étale chart is locally surjective.** A surjective étale chart
presents `X` as the coequalizer of its kernel pair (Stacks 0262), so it is an epimorphism of
sheaves; the change of big site is a left adjoint, so its image is an epimorphism; and the
transported chart is that image preceded by the isomorphism of Stacks 03FP, part (1). -/
theorem isLocallySurjective_changeBigSiteChart {U : CostructuredArrow yoneda X.obj}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) U.hom)
    (he : IsEtaleChart B S hS X.obj U) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B' S (largerContains h hS))
      (changeBigSiteChart B B' h S hS X U).hom := by
  let hS' : B'.Contains S := largerContains h hS
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S hS'
  let i := inclusionOver h S hS
  let : i.IsContinuous J K :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  let : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  let : HasSheafify J (Type u) := hasSheafify_overTopology B S hS
  let : HasSheafify K (Type u) := hasSheafify_overTopology B' S hS'
  let : J.Subcanonical := subcanonical_overTopology B S hS
  let : K.Subcanonical := subcanonical_overTopology B' S hS'
  let L := i.sheafPullback (Type u) J K
  let : PreservesColimits L :=
    (i.sheafAdjunctionContinuous (Type u) J K).leftAdjoint_preservesColimits
  let R := he.rep.pullback U.hom
  let s : R ⟶ U.left := he.rep.fst' U.hom
  let t : R ⟶ U.left := he.rep.snd U.hom
  have hR : IsPullback (yoneda.map s) (yoneda.map t) U.hom U.hom := he.rep.isPullback' U.hom
  let A : Sheaf J (Type u) := ⟨X.obj, X.property.isSheaf⟩
  let qS : J.yoneda.obj U.left ⟶ A := ⟨U.hom⟩
  have hw : J.yoneda.map s ≫ qS = J.yoneda.map t ≫ qS := by
    apply Sheaf.hom_ext
    exact hR.w
  obtain ⟨_, _, ⟨hcoeq⟩⟩ :=
    Space.isCoequalizer_of_surjectiveEtale B S hS U.hom s t hR X.property hs he
  have hepi : Epi (L.map qS) :=
    Cofork.IsColimit.epi (isColimitCoforkMapOfIsColimit L hw hcoeq)
  have hls : Sheaf.IsLocallySurjective (L.map qS) :=
    (Sheaf.isLocallySurjective_iff_epi (L.map qS)).mpr hepi
  have hls' : Presheaf.IsLocallySurjective (BigFppfOver.topology B' S hS')
      ((changeBigSite B B' h S hS).map (chartHomMk B S hS X U)).hom := hls
  have h1 := isLocallySurjective_changeBigSiteYonedaHom B B' h S hS U.left
  rw [changeBigSiteChart_hom]
  exact @Presheaf.isLocallySurjective_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 hls'

/-- **The transport of a surjective étale chart is surjective**: every represented base change
of it is a surjective morphism of schemes. A base change of a locally surjective morphism is
locally surjective, and a locally surjective morphism between represented sheaves is
surjective (`AlgebraicGeometry.Space.surjective_of_isLocallySurjective`). -/
theorem presheaf_surjective_changeBigSiteChart {U : CostructuredArrow yoneda X.obj}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) U.hom)
    (he : IsEtaleChart B S hS X.obj U) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B' S (largerContains h hS))))
        (changeBigSiteChart B B' h S hS X U).hom := by
  have hloc := isLocallySurjective_changeBigSiteChart B B' h S hS X hs he
  refine ⟨(isEtaleChart_changeBigSiteChart B B' h S hS X he).rep, ?_⟩
  intro a b g fst snd hpb
  have : Presheaf.IsLocallySurjective (BigFppfOver.topology B' S (largerContains h hS))
      (yoneda.map snd) :=
    Presheaf.isLocallySurjective_of_isPullback _ hpb.flip
  exact Space.surjective_of_isLocallySurjective B' S (largerContains h hS) snd this


/-! ### Every étale chart of `X'` is covered by transported charts -/

/-- **Every étale chart of `X'` is covered by transported étale charts of `X`, indexed by a set
smaller than the cutoff of `B'`.**

Let `V` be an étale chart of `X'` and let `A` be a surjective étale chart of `X`. The transport of
`A` is a surjective étale chart of `X'`, so its base change `P` to `V` is a surjective étale
scheme over `V`, and an object of `B'`. Each affine open `W` of `P` is affine and étale over the
scheme of `A`, which belongs to `B`, so `W` belongs to `B`; composing with `A` makes `W` an étale
chart of `X`, whose transport maps to `V`. These maps, indexed by the affine opens of `P`, generate
a covering sieve of `V`, and there are fewer than `B'.cutoff` of them because `P` is an object of
`B'`. -/
theorem exists_ofArrows_mem_changeBigSiteSmallEtale
    (V : SmallEtale B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj) :
    ∃ (ι : Type u) (Y : ι → SmallEtale B S hS X.obj)
      (f : ∀ k, (changeBigSiteSmallEtale B B' h S hS X).obj (Y k) ⟶ V),
      Cardinal.mk ι < B'.cutoff ∧
      Sieve.ofArrows _ f ∈ SmallEtale.topology B' S (largerContains h hS)
        ((changeBigSite B B' h S hS).obj X).obj V := by
  let G := changeBigSiteSmallEtale B B' h S hS X
  let hS' : B'.Contains S := largerContains h hS
  let K' := BigFppfOver.toScheme B' S hS'
  obtain ⟨U₀, q, hqs, hqe⟩ := X.property.exists_atlas
  let A : SmallEtale B S hS X.obj := ⟨CostructuredArrow.mk q, hqe⟩
  let ψ := (G.obj A).obj.hom
  have hψe : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) K') ψ := (G.obj A).property
  have hψs : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) K') ψ :=
    presheaf_surjective_changeBigSiteChart B B' h S hS X (U := CostructuredArrow.mk q) hqs hqe
  let P := hψe.rep.pullback V.obj.hom
  let p₁ : P ⟶ (G.obj A).obj.left := hψe.rep.fst' V.obj.hom
  let p₂ : P ⟶ V.obj.left := hψe.rep.snd V.obj.hom
  have hpb : IsPullback (yoneda.map p₁) (yoneda.map p₂) ψ V.obj.hom :=
    hψe.rep.isPullback' V.obj.hom
  have hp₂e : Etale (K'.map p₂) := hψe.property V.obj.hom (yoneda.map p₁) p₂ hpb
  have hp₂s : Surjective (K'.map p₂) := hψs.property V.obj.hom (yoneda.map p₁) p₂ hpb
  have hp₁e : Etale (K'.map p₁) := V.property.property ψ (yoneda.map p₂) p₁ hpb.flip
  let Ps : Scheme.{u} := K'.obj P
  let ι : Type u := Ps.affineOpens
  have hsmall (k : ι) : B.Contains (k : Ps.Opens).toScheme := by
    have := hp₁e
    have : IsAffine (k : Ps.Opens).toScheme := k.2
    exact size_lt_cutoff_of_isAffine_of_locallyOfFiniteType .fppf B
      ((k : Ps.Opens).ι ≫ K'.map p₁) U₀.left.property
  let W₀ (k : ι) : BigFppfOver B S hS :=
    BigFppfOver.mk B S hS (hsmall k) ((k : Ps.Opens).ι ≫ K'.map p₁ ≫ B.inclusion.map U₀.hom)
  let w (k : ι) : W₀ k ⟶ U₀ :=
    BigFppfOver.homMk B S hS U₀.left.property (B.inclusion.map U₀.hom)
      ((k : Ps.Opens).ι ≫ K'.map p₁) (Category.assoc _ _ _) ≫ (by exact 𝟙 U₀)
  have hwe (k : ι) : Etale ((BigFppfOver.toScheme B S hS).map (w k)) := by
    have := hp₁e
    change Etale (((k : Ps.Opens).ι ≫ K'.map p₁) ≫ 𝟙 _)
    rw [Category.comp_id]
    infer_instance
  let Yc (k : ι) : SmallEtale B S hS X.obj :=
    ⟨CostructuredArrow.mk (yoneda.map (w k) ≫ q),
      etale_comp_of_scheme B S hS (w k) q (hwe k) hqe⟩
  let g (k : ι) : Yc k ⟶ A := ObjectProperty.homMk (CostructuredArrow.homMk (w k) rfl)
  have hPw {Y} (p : P ⟶ Y) : K'.map p ≫ B'.inclusion.map Y.hom = B'.inclusion.map P.hom :=
    (B'.inclusion.map_comp _ _).symm.trans (congrArg B'.inclusion.map (Over.w p))
  let ιk (k : ι) : (G.obj (Yc k)).obj.left ⟶ P :=
    Over.homMk (ObjectProperty.homMk (k : Ps.Opens).ι) (by
      apply ObjectProperty.hom_ext
      change (k : Ps.Opens).ι ≫ B'.inclusion.map P.hom =
        (k : Ps.Opens).ι ≫ K'.map p₁ ≫ B.inclusion.map U₀.hom
      exact (congrArg ((k : Ps.Opens).ι ≫ ·) (hPw p₁)).symm)
  have hιk (k : ι) : ιk k ≫ p₁ = (G.map (g k)).hom.left := by
    apply (BigFppfOver.toScheme B' S hS').map_injective
    change (k : Ps.Opens).ι ≫ K'.map p₁ = ((k : Ps.Opens).ι ≫ K'.map p₁) ≫ 𝟙 _
    exact (Category.comp_id _).symm
  let f (k : ι) : G.obj (Yc k) ⟶ V :=
    ObjectProperty.homMk (CostructuredArrow.homMk (ιk k ≫ p₂) (by
      refine (congrArg (· ≫ V.obj.hom) (yoneda.map_comp (ιk k) p₂)).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (yoneda.map (ιk k) ≫ ·) hpb.w.symm).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ ψ) (yoneda.map_comp (ιk k) p₁).symm).trans ?_
      refine (congrArg (fun m => yoneda.map m ≫ ψ) (hιk k)).trans ?_
      exact CostructuredArrow.w (G.map (g k)).hom))
  have hcard : Cardinal.mk ι < B'.cutoff :=
    (Scheme.mk_affineOpens_le_size Ps).trans_lt P.left.property
  let Vs := (SmallEtale.toSchemes B' S hS' ((changeBigSite B B' h S hS).obj X).obj).obj V
  let Wf : PreZeroHypercover.{u + 1} (B'.inclusion.obj Vs) := {
    I₀ := ULift.{u + 1} ι
    X k := (k.down : Ps.Opens).toScheme
    f k := (k.down : Ps.Opens).ι ≫ K'.map p₂ }
  have hWet (k : Wf.I₀) : Etale (Wf.f k) := by
    have := hp₂e
    change Etale ((k.down : Ps.Opens).ι ≫ K'.map p₂)
    infer_instance
  have hW : Wf.presieve₀ ∈ Scheme.etalePrecoverage (B'.inclusion.obj Vs) := by
    refine (Scheme.presieve₀_mem_precoverage_iff Wf).mpr ⟨fun x => ?_, hWet⟩
    obtain ⟨y, hy⟩ := hp₂s.surj x
    obtain ⟨A', z, hz⟩ := exists_affineOpens_ι_apply_eq (K'.map p₂) hy
    exact ⟨ULift.up A', z, hz⟩
  have hsize' (k : Wf.I₀) : B'.Contains (Wf.X k) := largerContains h (hsmall k.down)
  obtain ⟨Vc, hVc, hEq⟩ := exists_etaleCovering_tautologicallyEquivalent B' Vs Wf hW hsize'
  have hVce := etale_inclusion_map_of_etaleCovering hVc
  let F' := SmallEtale.liftFamily V Vc hVce
  have hgen : Sieve.generate F'.presieve₀ ∈ SmallEtale.topology B' S hS'
      ((changeBigSite B B' h S hS).obj X).obj V :=
    Precoverage.generate_mem_toGrothendieck
      ⟨F', rfl, SmallEtale.isCovering_liftFamily V Vc hVce hVc⟩
  refine ⟨ι, Yc, f, hcard, (SmallEtale.topology B' S hS' _).superset_covering ?_ hgen⟩
  rw [Sieve.generate_le_iff]
  rintro Z m ⟨j⟩
  obtain ⟨β, hβ⟩ := hEq.2
  obtain ⟨e, he⟩ := hβ j
  let k := (β j).down
  have he' : e.hom ≫ (k : Ps.Opens).ι ≫ K'.map p₂ = B'.inclusion.map (Vc.f j) := he
  let lleft : (F'.X j).obj.left ⟶ (G.obj (Yc k)).obj.left :=
    Over.homMk (ObjectProperty.homMk e.hom) (by
      apply ObjectProperty.hom_ext
      change e.hom ≫ (k : Ps.Opens).ι ≫ K'.map p₁ ≫ B.inclusion.map U₀.hom =
        B'.inclusion.map (Vc.f j) ≫ B'.inclusion.map V.obj.left.hom
      refine (congrArg (fun m => e.hom ≫ (k : Ps.Opens).ι ≫ m) (hPw p₁)).trans ?_
      refine (congrArg (fun m => e.hom ≫ (k : Ps.Opens).ι ≫ m) (hPw p₂).symm).trans ?_
      refine Eq.trans ?_ (congrArg (· ≫ B'.inclusion.map V.obj.left.hom) he')
      simp only [Category.assoc])
  have hl : lleft ≫ (f k).hom.left = (F'.f j).hom.left := by
    apply (BigFppfOver.toScheme B' S hS').map_injective
    exact (Category.assoc _ _ _).symm.trans he'
  refine ⟨_, SmallEtale.homOfFac (f k) (F'.f j) lleft hl, f k, ⟨k⟩, ?_⟩
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  exact hl


/-! ### The functor is a cocontinuous dense subsite inclusion -/

/-- A chosen covering family of an étale chart of `X` is carried to a chosen covering family of
its transport: the chosen covering families of `B` are chosen covering families of `B'`, and
being étale is a condition on the underlying schemes, which do not change. -/
theorem isCovering_map_changeBigSiteSmallEtale (U : SmallEtale B S hS X.obj)
    (E : PreZeroHypercover.{u + 1} U) (hE : SmallEtale.IsCovering B S hS X.obj ⟨U, E⟩) :
    SmallEtale.IsCovering B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj
      ⟨(changeBigSiteSmallEtale B B' h S hS X).obj U,
        E.map (changeBigSiteSmallEtale B B' h S hS X)⟩ :=
  ⟨(Classical.choose_spec h) _ hE.1, hE.2⟩

private theorem changeBigSiteSmallEtale_lifts_saturate :
    ∀ {V : SmallEtale B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj}
      {R : Sieve V},
      (SmallEtale.precoverage B' S (largerContains h hS)
        ((changeBigSite B B' h S hS).obj X).obj).Saturate V R →
      ∀ {U : SmallEtale B S hS X.obj} (a : (changeBigSiteSmallEtale B B' h S hS X).obj U ⟶ V),
        (R.pullback a).functorPullback (changeBigSiteSmallEtale B B' h S hS X) ∈
          SmallEtale.topology B S hS X.obj U := by
  intro V R hR
  induction hR with
  | of V P hP =>
      intro U a
      obtain ⟨E, hEq, hE⟩ := (SmallEtale.mem_precoverage_iff _ _ _ _).mp hP
      subst P
      obtain ⟨F, hF, hfactor⟩ :=
        exists_isCovering_changeBigSiteSmallEtale_refinement B B' h S hS X U a E hE
      have hgen : Sieve.generate F.presieve₀ ∈ SmallEtale.topology B S hS X.obj U :=
        Precoverage.generate_mem_toGrothendieck ⟨F, rfl, hF⟩
      refine (SmallEtale.topology B S hS X.obj).superset_covering ?_ hgen
      rw [Sieve.generate_le_iff]
      rintro Z m ⟨j⟩
      exact hfactor j
  | top V =>
      intro U a
      simpa only [Sieve.pullback_top, Sieve.functorPullback_top] using
        (SmallEtale.topology B S hS X.obj).top_mem U
  | pullback V R hR Y f ih =>
      intro U a
      simpa [Sieve.pullback_comp, Category.assoc] using ih (U := U) (a := a ≫ f)
  | transitive V R T hR hlocal ih ihlocal =>
      intro U a
      refine (SmallEtale.topology B S hS X.obj).transitive (ih a)
        ((T.pullback a).functorPullback (changeBigSiteSmallEtale B B' h S hS X)) ?_
      intro Z k hk
      have hk' : R ((changeBigSiteSmallEtale B B' h S hS X).map k ≫ a) := hk
      rw [← Sieve.functorPullback_pullback]
      simpa [Sieve.pullback_comp, Category.assoc] using ihlocal hk' (U := Z) (a := 𝟙 _)

/-- **The transport of étale charts is cocontinuous**: a covering sieve of a transported chart
pulls back to a covering sieve of the chart. -/
instance changeBigSiteSmallEtale_isCocontinuous :
    (changeBigSiteSmallEtale B B' h S hS X).IsCocontinuous (SmallEtale.topology B S hS X.obj)
      (SmallEtale.topology B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj) := by
  constructor
  intro U R hR
  simpa using changeBigSiteSmallEtale_lifts_saturate B B' h S hS X hR (𝟙 _)

/-- **The transported charts are cover-dense**: every étale chart of `X'` is covered by
transported étale charts of `X`. -/
instance changeBigSiteSmallEtale_isCoverDense :
    (changeBigSiteSmallEtale B B' h S hS X).IsCoverDense
      (SmallEtale.topology B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj) := by
  constructor
  intro V
  obtain ⟨ι, Y, f, -, hf⟩ := exists_ofArrows_mem_changeBigSiteSmallEtale B B' h S hS X V
  refine (SmallEtale.topology B' S (largerContains h hS) _).superset_covering ?_ hf
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro Z m ⟨k⟩
  exact Presieve.in_coverByImage _ (f k)

private theorem changeBigSiteSmallEtale_topology_eq_restricted :
    SmallEtale.topology B S hS X.obj =
      (changeBigSiteSmallEtale B B' h S hS X).restrictedTopology
        (SmallEtale.topology B' S (largerContains h hS)
        ((changeBigSite B B' h S hS).obj X).obj) := by
  let G := changeBigSiteSmallEtale B B' h S hS X
  let P := SmallEtale.precoverage B S hS X.obj
  let Q := SmallEtale.precoverage B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj
  let K := SmallEtale.topology B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj
  have hpre : P ≤ Q.comap G := by
    intro U R hR
    obtain ⟨E, hEq, hE⟩ := (SmallEtale.mem_precoverage_iff _ _ _ _).mp hR
    rw [Precoverage.mem_comap_iff, hEq, ← PreZeroHypercover.presieve₀_map]
    exact ⟨E.map G, rfl, isCovering_map_changeBigSiteSmallEtale B B' h S hS X U E hE⟩
  have hcomp : Q.comap G ≤ K.toPrecoverage.comap G := by
    intro U R hR
    apply Precoverage.mem_comap_iff.mpr
    apply Q.le_toPrecoverage_toGrothendieck
    exact Precoverage.mem_comap_iff.mp hR
  have hle : P.toGrothendieck ≤ G.restrictedTopology K := by
    change P.toGrothendieck ≤ (K.toPrecoverage.comap G).toGrothendieck
    exact (Precoverage.toGrothendieck_monotone hpre).trans
      (Precoverage.toGrothendieck_monotone hcomp)
  have hge : G.restrictedTopology K ≤ P.toGrothendieck := by
    intro U R hR
    rw [Functor.mem_restrictedTopology_iff] at hR
    have hsat : Q.Saturate (G.obj U) (R.functorPushforward G) := hR
    have hlift := changeBigSiteSmallEtale_lifts_saturate B B' h S hS X hsat (𝟙 _)
    rwa [Sieve.pullback_id, Sieve.functorPullback_functorPushforward_eq G] at hlift
  exact le_antisymm hle hge

/-- **The small étale site of `X` is a dense subsite of the small étale site of `X'`.** In
particular restriction along the transport of charts is an equivalence of small étale topoi
(`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`). -/
instance changeBigSiteSmallEtale_isDenseSubsite :
    (changeBigSiteSmallEtale B B' h S hS X).IsDenseSubsite (SmallEtale.topology B S hS X.obj)
      (SmallEtale.topology B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj) where
  functorPushforward_mem_iff {U R} := by
    rw [changeBigSiteSmallEtale_topology_eq_restricted B B' h S hS X]
    exact (Functor.mem_restrictedTopology_iff (G := changeBigSiteSmallEtale B B' h S hS X)).symm

end AlgebraicGeometry.Space

end
