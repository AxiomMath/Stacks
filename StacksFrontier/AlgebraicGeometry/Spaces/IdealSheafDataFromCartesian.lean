module

public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection

/-!
# A sheaf of ideals of `𝒪_X` descends to a sheaf of ideals on every étale chart

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`𝓘 ⊆ 𝒪_X` be a sheaf of ideals of its structure sheaf on the small étale ringed site of `X`.
A Zariski open `V` of the scheme underlying an étale chart `A` of `X` is itself an étale chart
of `X` — `AlgebraicGeometry.Space.openChart` — so `𝓘` has an ideal of sections over it, and
assigning that ideal to `V` is a candidate for an `AlgebraicGeometry.Scheme.IdealSheafData` on
the chart scheme.  This file shows that the candidate *is* one, and that the resulting sheaves
of ideals on the charts are compatible with inverse image along every morphism of charts, that
is, that they are pulled back from `X`.

The hypothesis is `AlgebraicGeometry.Space.IsCartesianOnAffineCharts`: for a morphism of
*affine* étale charts the sections over the smaller chart are the base change of the sections
over the larger one.  For a sheaf of ideals this says that restriction carries the ideal of
sections onto the ideal of sections,
`AlgebraicGeometry.Space.chartIdeal_map_of_isCartesianOnAffineCharts`.

For a surjective étale chart `φ : U ⟶ X`,
`AlgebraicGeometry.Space.exists_idealSheafData_of_isCartesianOnAffineCharts` produces an
*invariant* sheaf of ideals on the scheme `U` whose pullback cuts out `𝓘` over every affine
chart lying over `U`.

## Main definitions

* `AlgebraicGeometry.Space.chartIdeal` is the ideal of sections of a sheaf of ideals of `𝒪_X`
  over an étale chart, spelled as an ideal of `AlgebraicGeometry.Space.chartRing`.
* `AlgebraicGeometry.Space.openChartIdeal` is that ideal for the chart cut out by a Zariski
  open `V` of a chart scheme, transported to an ideal of the sections over `V`.
* `AlgebraicGeometry.Space.idealSheafDataOfChart` is the resulting sheaf of ideals on the
  scheme underlying an étale chart.

## Main results

* `AlgebraicGeometry.Space.chartIdeal_map_of_surjective_sectionsBaseChange` and
  `AlgebraicGeometry.Space.chartIdeal_map_of_isCartesianOnAffineCharts`: restriction between
  affine charts carries the ideal of sections onto the ideal of sections.
* `AlgebraicGeometry.Space.exists_openChartHom_resLE`: a morphism of charts restricts to a
  morphism of the charts cut out by an open of the target and an open of the source above it.
* `AlgebraicGeometry.Space.comap_idealSheafDataOfChart`: **the chartwise sheaves of ideals are
  pulled back from `X`.**
* `AlgebraicGeometry.Space.ker_appTop_subschemeι_idealSheafDataOfChart`: on an affine chart the
  closed subscheme cut out by the chartwise sheaf of ideals kills exactly the sections of `𝓘`.
* `AlgebraicGeometry.Space.exists_idealSheafData_of_isCartesianOnAffineCharts`: a sheaf of
  ideals cartesian on affine charts comes from an invariant sheaf of ideals on any surjective
  étale chart.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01QX](https://stacks.math.columbia.edu/tag/01QX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-! ### Global sections of open subschemes -/

/-- **The comparison `Γ(V, ⊤) ≅ Γ(Z, V)` is natural in the open `V`.** Restricting a global
function along the inclusion of a smaller open subscheme is restricting the corresponding
section.  This is the naturality of `AlgebraicGeometry.Scheme.restrictFunctorΓ`, read through
`AlgebraicGeometry.Scheme.Opens.topIso`. -/
theorem homOfLE_appTop_comp_topIso_hom {Z : Scheme.{u}} {V W : Z.Opens} (h : W ≤ V) :
    (Z.homOfLE h).appTop ≫ W.topIso.hom =
      V.topIso.hom ≫ Z.presheaf.map (homOfLE h).op :=
  Scheme.restrictFunctorΓ.hom.naturality (X := op V) (Y := op W) (homOfLE h).op

/-- **The comparison `Γ(V, ⊤) ≅ Γ(Z, V)` turns the restriction of a morphism to a pair of
opens into the induced map on sections.**  This is
`AlgebraicGeometry.Scheme.Hom.resLE_app_top` with the inverse comparison moved to the other
side. -/
theorem resLE_appTop_comp_topIso_hom {Y Z : Scheme.{u}} (g : Y ⟶ Z) {V : Z.Opens}
    {W : Y.Opens} (h : W ≤ g ⁻¹ᵁ V) :
    (g.resLE V W h).appTop ≫ W.topIso.hom = V.topIso.hom ≫ g.appLE V W h := by
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The inclusion of the whole of a scheme as an open subscheme induces, on global
functions, the inverse of the comparison `Γ(⊤, ⊤) ≅ Γ(Z, ⊤)`.** -/
theorem appTop_ι_top {Z : Scheme.{u}} :
    (⊤ : Z.Opens).ι.appTop = (⊤ : Z.Opens).topIso.inv := by
  rw [Scheme.Hom.appTop, Scheme.Opens.ι_app, Scheme.Opens.topIso_inv]
  exact congrArg Z.presheaf.map (Subsingleton.elim _ _)


/-- **A scheme over another is covered by affine opens each lying inside an affine open of the
target.**  The family is indexed by the points of the source. -/
theorem exists_affineOpens_le_preimage {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    ∃ (W : Y → Y.affineOpens) (V : Y → Z.affineOpens),
      (∀ x, (W x).1 ≤ g ⁻¹ᵁ (V x).1) ∧ ⨆ x, (W x).1 = ⊤ := by
  have hV : ∀ x : Y, ∃ V : Z.affineOpens, g.base x ∈ V.1 := fun x => by
    obtain ⟨V, hVmem, hxV, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
        (show g.base x ∈ (⊤ : Z.Opens) from trivial)
    exact ⟨⟨V, hVmem⟩, hxV⟩
  choose V hVx using hV
  have hW : ∀ x : Y, ∃ W : Y.affineOpens, x ∈ W.1 ∧ W.1 ≤ g ⁻¹ᵁ (V x).1 := fun x => by
    obtain ⟨W, hWmem, hxW, hsub⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
        (show x ∈ g ⁻¹ᵁ (V x).1 from hVx x)
    exact ⟨⟨W, hWmem⟩, hxW, hsub⟩
  choose W hWx hWle using hW
  exact ⟨W, V, hWle, top_le_iff.1 fun x _ =>
    TopologicalSpace.Opens.mem_iSup.2 ⟨x, hWx x⟩⟩

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Open subobjects of the site -/

/-- The structure morphism of the open subobject `AlgebraicGeometry.Space.openSub` cut out by
a Zariski open is the inclusion of the open followed by the structure morphism. -/
theorem inclusion_map_openSub_hom (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    B.inclusion.map (openSub A O).hom = O.ι ≫ B.inclusion.map A.hom := by
  rw [← Over.w (openSubHom A O), B.inclusion.map_comp]
  exact congrArg (· ≫ B.inclusion.map A.hom) (toScheme_map_openSubHom B S hS A O)

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.openChartHomOfLE` is the
inclusion of the smaller open, definitionally. -/
theorem toScheme_map_toOver_map_openChartHomOfLE (A : SmallEtale B S hS F)
    {O O' : (chartScheme A).Opens} (h : O ≤ O') :
    (BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (openChartHomOfLE B S hS F A h)) =
      (chartScheme A).homOfLE h :=
  rfl

/-- **A morphism of charts restricts to a morphism of the charts cut out by a pair of opens.**
If `m : A' ⟶ A` is a morphism of étale charts of `F` and `W` is a Zariski open of the chart
scheme of `A'` carried into a Zariski open `V` of the chart scheme of `A`, then the étale
charts `W` and `V` of `F` are related by a morphism of charts whose underlying morphism of
schemes is `AlgebraicGeometry.Scheme.Hom.resLE`. -/
theorem exists_openChartHom_resLE {A A' : SmallEtale B S hS F} (m : A' ⟶ A)
    (V : (chartScheme A).Opens) (W : (chartScheme A').Opens)
    (h : W ≤ (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map m) ⁻¹ᵁ V) :
    ∃ n : openChart B S hS F A' W ⟶ openChart B S hS F A V,
      (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map n) =
        ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS F).map m)).resLE V W h := by
  set ψ := (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map m) with hψ
  have hover : ψ ≫ B.inclusion.map ((SmallEtale.toOver B S hS F).obj A).hom =
      B.inclusion.map ((SmallEtale.toOver B S hS F).obj A').hom :=
    congrArg (fun q => B.inclusion.map q) (Over.w ((SmallEtale.toOver B S hS F).map m))
  have key : ψ.resLE V W h ≫ V.ι = W.ι ≫ ψ := Scheme.Hom.resLE_comp_ι ψ h
  obtain ⟨n, hn⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS (X := openSub _ W)
    (Y := openSub _ V) (ψ.resLE V W h) (by
      rw [inclusion_map_openSub_hom, inclusion_map_openSub_hom]
      calc ψ.resLE V W h ≫ V.ι ≫
            B.inclusion.map ((SmallEtale.toOver B S hS F).obj A).hom
          = (ψ.resLE V W h ≫ V.ι) ≫
            B.inclusion.map ((SmallEtale.toOver B S hS F).obj A).hom :=
            (Category.assoc _ _ _).symm
        _ = (W.ι ≫ ψ) ≫ B.inclusion.map ((SmallEtale.toOver B S hS F).obj A).hom := by
            rw [key]
        _ = W.ι ≫ ψ ≫ B.inclusion.map ((SmallEtale.toOver B S hS F).obj A).hom :=
            Category.assoc _ _ _
        _ = W.ι ≫ B.inclusion.map ((SmallEtale.toOver B S hS F).obj A').hom := by
            rw [hover])
  have hcomm : n ≫ openSubHom _ V = openSubHom _ W ≫ (SmallEtale.toOver B S hS F).map m := by
    refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp, Functor.map_comp, hn, toScheme_map_openSubHom,
      toScheme_map_openSubHom]
    exact key
  have hw : yoneda.map ((SmallEtale.toOver B S hS F).map m) ≫ A.1.hom = A'.1.hom :=
    CostructuredArrow.w m.1
  refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk n ?_), hn⟩
  show yoneda.map n ≫ yoneda.map (openSubHom _ V) ≫ A.1.hom =
    yoneda.map (openSubHom _ W) ≫ A'.1.hom
  rw [← Category.assoc, ← yoneda.map_comp, hcomm, yoneda.map_comp, Category.assoc, hw]


/-! ### The ideal of sections of a sheaf of ideals over a chart -/

variable (X : AlgebraicSpaces B S hS)

/-- The sections over an étale chart of a sheaf of ideals of the structure sheaf of an
algebraic space, read as an ideal of `AlgebraicGeometry.Space.chartRing`; it is `N.obj (op A)`. -/
noncomputable abbrev chartIdeal
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (A : SmallEtale B S hS X.1) : Ideal (chartRing B S hS X.1 X.2 A) :=
  N.obj (op A)

/-- The comparison isomorphism `Γ(V, ⊤) ≅ Γ(A, V)` of
`AlgebraicGeometry.Scheme.Opens.topIso`, read as a ring map out of
`AlgebraicGeometry.Space.chartRing` of the étale chart cut out by the open `V`. -/
noncomputable abbrev openChartTopRingHom (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) :
    chartRing B S hS X.1 X.2 (openChart B S hS X.1 A V) →+*
      Γ(chartScheme A, V) :=
  V.topIso.hom.hom

variable (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)

/-- **Where the base change comparison of a sheaf of ideals is surjective, restriction carries
the ideal of sections onto the ideal of sections.**  Surjectivity of
`AlgebraicGeometry.Space.sectionsBaseChange` says exactly that the sections over the smaller
chart are generated, as a module over the smaller ring, by the restrictions of the sections
over the larger chart; for a sheaf of *ideals* that generated module is the ideal image. -/
theorem chartIdeal_map_of_surjective_sectionsBaseChange
    {A A' : SmallEtale B S hS X.1} (m : A' ⟶ A)
    (hm : Function.Surjective (sectionsBaseChange N.toSheafOfModules m)) :
    Ideal.map (chartRestrict (hF := X.2) m) (chartIdeal B S hS X N A) =
      chartIdeal B S hS X N A' := by
  refine le_antisymm ?_ fun y hy => ?_
  · rw [Ideal.map_le_iff_le_comap]
    exact fun x hx => N.map_mem m.op hx
  · obtain ⟨z, hz⟩ := hm ⟨y, hy⟩
    rw [show y = (sectionsBaseChange N.toSheafOfModules m z).1 by rw [hz]]
    clear hz
    induction z using TensorProduct.induction_on with
    | zero =>
        rw [map_zero]
        exact Ideal.zero_mem _
    | tmul b x =>
        show b * chartRestrict (hF := X.2) m x.1 ∈ _
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ x.2)
    | add a b ha hb =>
        rw [map_add]
        exact Ideal.add_mem _ ha hb

/-- **For a sheaf of ideals cartesian on affine charts, restriction between affine charts
carries the ideal of sections onto the ideal of sections.** -/
theorem chartIdeal_map_of_isCartesianOnAffineCharts
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
    {A A' : SmallEtale B S hS X.1}
    (hA : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A))
    (hA' : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A'))
    (m : A' ⟶ A) :
    Ideal.map (chartRestrict (hF := X.2) m) (chartIdeal B S hS X N A) =
      chartIdeal B S hS X N A' :=
  chartIdeal_map_of_surjective_sectionsBaseChange B S hS X N m (hN A A' hA hA' m).2

/-- The ideal of sections of a sheaf of ideals of `𝒪_X` over a Zariski open `V` of an étale
chart `A`, read as an ideal of `Γ(A, V)`.

The open `V` is itself an étale chart of `X` — `AlgebraicGeometry.Space.openChart` — and the
ideal is the sections of the sheaf of ideals over that chart, transported along
`AlgebraicGeometry.Scheme.Opens.topIso`. -/
noncomputable def openChartIdeal (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) : Ideal Γ(chartScheme A, V) :=
  Ideal.map (openChartTopRingHom B S hS X A V)
    (chartIdeal B S hS X N (openChart B S hS X.1 A V))

/-- **For a sheaf of ideals cartesian on affine charts, the ideals of
`AlgebraicGeometry.Space.openChartIdeal` over affine opens are compatible with any morphism of
the charts cut out by those opens.**  A ring map `ρ` which corresponds to the morphism of charts
`n` under `AlgebraicGeometry.Scheme.Opens.topIso` carries the ideal over `V` onto the ideal
over `W`. -/
theorem openChartIdeal_map_of_chartHom
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
    {A A' : SmallEtale B S hS X.1}
    {V : (chartScheme A).Opens} {W : (chartScheme A').Opens}
    (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (n : openChart B S hS X.1 A' W ⟶ openChart B S hS X.1 A V)
    (ρ : Γ(chartScheme A, V) ⟶ Γ(chartScheme A', W))
    (hcomm : ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS X.1).map n)).appTop ≫ W.topIso.hom =
      V.topIso.hom ≫ ρ) :
    Ideal.map ρ.hom (openChartIdeal B S hS X N A V) =
      openChartIdeal B S hS X N A' W := by
  have hVa : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj
      (openChart B S hS X.1 A V)) := hV
  have hWa : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj
      (openChart B S hS X.1 A' W)) := hW
  have hρ : (CommRingCat.Hom.hom ρ).comp (openChartTopRingHom B S hS X A V)
      = (openChartTopRingHom B S hS X A' W).comp (chartRestrict (hF := X.2) n) :=
    (congrArg CommRingCat.Hom.hom hcomm).symm
  rw [openChartIdeal, openChartIdeal,
    ← chartIdeal_map_of_isCartesianOnAffineCharts B S hS X N hN hVa hWa n, Ideal.map_map,
    Ideal.map_map, hρ]


/-- **Restriction to a smaller open of the same chart carries the ideal of
`AlgebraicGeometry.Space.openChartIdeal` onto the ideal there.** -/
theorem openChartIdeal_map_presheaf_map
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules) (A : SmallEtale B S hS X.1)
    {V W : (chartScheme A).Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (h : W ≤ V) :
    Ideal.map ((chartScheme A).presheaf.map (homOfLE h).op).hom
        (openChartIdeal B S hS X N A V) =
      openChartIdeal B S hS X N A W :=
  openChartIdeal_map_of_chartHom B S hS X N hN hV hW
    (openChartHomOfLE B S hS X.1 A h) _ (by
      rw [toScheme_map_toOver_map_openChartHomOfLE]
      exact homOfLE_appTop_comp_topIso_hom h)

/-- **A morphism of charts carries the ideal of `AlgebraicGeometry.Space.openChartIdeal` over
an affine open of the target chart onto the ideal over an affine open of the source chart
lying above it**, along the induced map on sections. -/
theorem openChartIdeal_map_appLE
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
    {A A' : SmallEtale B S hS X.1} (m : A' ⟶ A)
    {V : (chartScheme A).Opens} {W : (chartScheme A').Opens}
    (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (h : W ≤ (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map m) ⁻¹ᵁ V) :
    Ideal.map (((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS X.1).map m)).appLE V W h).hom
        (openChartIdeal B S hS X N A V) =
      openChartIdeal B S hS X N A' W := by
  obtain ⟨n, hn⟩ := exists_openChartHom_resLE B S hS X.1 m V W h
  refine openChartIdeal_map_of_chartHom B S hS X N hN hV hW n _ ?_
  rw [hn]
  exact resLE_appTop_comp_topIso_hom _ h

/-- **A sheaf of ideals of `𝒪_X` cartesian on affine charts induces a sheaf of ideals on the
scheme underlying every étale chart.**  Its ideal over an affine open `V` of the chart is the
ideal of sections of the sheaf of ideals over `V` read as an étale chart of `X`,
`AlgebraicGeometry.Space.openChartIdeal`. -/
noncomputable def idealSheafDataOfChart
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules) (A : SmallEtale B S hS X.1) :
    (chartScheme A).IdealSheafData where
  ideal V := openChartIdeal B S hS X N A V.1
  map_ideal_basicOpen V f :=
    openChartIdeal_map_presheaf_map B S hS X N hN A V.2
      ((chartScheme A).affineBasicOpen f).2 _

/-- The ideal of `AlgebraicGeometry.Space.idealSheafDataOfChart` over an affine open of the
chart is `AlgebraicGeometry.Space.openChartIdeal`. -/
theorem ideal_idealSheafDataOfChart
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules) (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).affineOpens) :
    (idealSheafDataOfChart B S hS X N hN A).ideal V = openChartIdeal B S hS X N A V.1 :=
  rfl


/-- **The sheaves of ideals of `AlgebraicGeometry.Space.idealSheafDataOfChart` are compatible
with inverse image along a morphism of charts**: the chartwise sheaves of ideals constructed
from a sheaf of ideals of `𝒪_X` cartesian on affine charts are pulled back from `X`. -/
theorem comap_idealSheafDataOfChart
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
    {A A' : SmallEtale B S hS X.1} (m : A' ⟶ A) :
    (idealSheafDataOfChart B S hS X N hN A).comap
        ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map m)) =
      idealSheafDataOfChart B S hS X N hN A' := by
  obtain ⟨W, V, hle, hsup⟩ := exists_affineOpens_le_preimage
    ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map m))
  have key : ∀ x, ((idealSheafDataOfChart B S hS X N hN A).comap
        ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS X.1).map m))).ideal (W x) =
      (idealSheafDataOfChart B S hS X N hN A').ideal (W x) := by
    intro x
    rw [Stacks.IdealSheaf.ideal_comap_appLE _ _ (V x) (W x) (hle x),
      ideal_idealSheafDataOfChart, ideal_idealSheafDataOfChart]
    exact openChartIdeal_map_appLE B S hS X N hN m (V x).2 (W x).2 (hle x)
  exact le_antisymm
    (Scheme.IdealSheafData.le_of_iSup_eq_top W hsup fun x => (key x).le)
    (Scheme.IdealSheafData.le_of_iSup_eq_top W hsup fun x => (key x).ge)


/-! ### The closed subscheme cut out on an affine chart -/

/-- **On an affine chart, the closed subscheme cut out by
`AlgebraicGeometry.Space.idealSheafDataOfChart` kills exactly the sections of the sheaf of
ideals.** -/
theorem ker_appTop_subschemeι_idealSheafDataOfChart
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules) (A : SmallEtale B S hS X.1)
    (hA : IsAffine (chartScheme A)) :
    RingHom.ker ((idealSheafDataOfChart B S hS X N hN A).subschemeι.appTop).hom =
      chartIdeal B S hS X N A := by
  have hT : IsAffineOpen (⊤ : (chartScheme A).Opens) := isAffineOpen_top _
  have hTa : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj
      (openChart B S hS X.1 A ⊤)) := hT
  have hAa : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙
    BigFppfOver.toScheme B S hS).obj A) := hA
  have hring : ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map
        (openChartInclusion B S hS X.1 A ⊤))).appTop ≫
      (⊤ : (chartScheme A).Opens).topIso.hom =
      𝟙 Γ(chartScheme A, (⊤ : (chartScheme A).Opens)) := by
    rw [toScheme_map_toOver_map_openChartInclusion, appTop_ι_top]
    exact Iso.inv_hom_id _
  have hcart := chartIdeal_map_of_isCartesianOnAffineCharts B S hS X N hN hAa hTa
    (openChartInclusion B S hS X.1 A ⊤)
  have hker : RingHom.ker ((idealSheafDataOfChart B S hS X N hN A).subschemeι.appTop).hom =
      (idealSheafDataOfChart B S hS X N hN A).ideal ⟨⊤, hT⟩ :=
    Scheme.IdealSheafData.ker_subschemeι_app _ ⟨⊤, hT⟩
  rw [hker,
    ideal_idealSheafDataOfChart, openChartIdeal, ← hcart, Ideal.map_map,
    show (openChartTopRingHom B S hS X A ⊤).comp
          (chartRestrict (hF := X.2) (openChartInclusion B S hS X.1 A ⊤)) =
        RingHom.id (chartRing B S hS X.1 X.2 A) from congrArg CommRingCat.Hom.hom hring]
  exact Ideal.map_id _

/-! ### Invariant sheaves of ideals on a surjective étale chart -/

section Chart

variable {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X.1}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)

include hs he in
/-- The source leg of the relation `R = U ×_X U` of a chart is étale, for *the* presentation
of the relation that `AlgebraicGeometry.Space.atlasRelation` uses — which is the one chosen by
the surjectivity hypothesis, not by the étaleness hypothesis. -/
theorem etale_toScheme_map_atlasRelationSource :
    Etale ((BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs)) := by
  have hRI : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @Etale.{u})
  exact property_snd_of_isPullback B S hS hs.rep (he.rep.isPullback φ) (he.property_snd φ)

include hs he in
/-- The relation `R = U ×_X U` of a surjective étale chart `φ : U ⟶ X`, read as an étale chart
of `X` through its source leg. -/
theorem presheaf_etale_atlasRelation :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map (atlasRelationSource B S hS hs) ≫ φ) :=
  etale_comp_of_scheme B S hS (atlasRelationSource B S hS hs) φ
    (etale_toScheme_map_atlasRelationSource B S hS X hs he) he

include hs he in
/-- **A sheaf of ideals cartesian on affine charts comes from an invariant sheaf of ideals on
a surjective étale chart.**  A sheaf of ideals `𝓘 ⊆ 𝒪_X` on the small étale site of an
algebraic space which is cartesian on affine charts comes from a sheaf of ideals `J ⊆ 𝒪_U` on
the *scheme* underlying any surjective étale chart `φ : U ⟶ X`: the closed subscheme
`V(J) ⊆ U` is invariant under the relation `R = U ×_X U`, and over every affine étale chart `A`
of `X` lying over `U` the ideal of global functions cut out by the pullback of `J` is `𝓘(A)`. -/
theorem exists_idealSheafData_of_isCartesianOnAffineCharts
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hI : IsCartesianOnAffineCharts I.toSheafOfModules) :
    ∃ J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData,
      ∃ _ : IsInvariantSubscheme B S hS hs (Subobject.mk J.subschemeι),
        ∀ A : SmallEtale B S hS X.1,
          IsAffine ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS X.1).obj A)) →
          ∀ m : A ⟶ (⟨CostructuredArrow.mk φ, he⟩ : SmallEtale B S hS X.1),
            RingHom.ker ((J.comap ((BigFppfOver.toScheme B S hS).map
                ((SmallEtale.toOver B S hS X.1).map m))).subschemeι.appTop).hom =
              I.obj (op A) := by
  refine ⟨idealSheafDataOfChart B S hS X I hI ⟨CostructuredArrow.mk φ, he⟩, ?_, ?_⟩
  · have key : ∀ g : atlasRelation B S hS hs ⟶ U,
        yoneda.map g ≫ φ = yoneda.map (atlasRelationSource B S hS hs) ≫ φ →
        (idealSheafDataOfChart B S hS X I hI
          (⟨CostructuredArrow.mk φ, he⟩ : SmallEtale B S hS X.1)).comap
          ((BigFppfOver.toScheme B S hS).map g) =
        idealSheafDataOfChart B S hS X I hI
          ⟨CostructuredArrow.mk (yoneda.map (atlasRelationSource B S hS hs) ≫ φ),
            presheaf_etale_atlasRelation B S hS X hs he⟩ := fun g hg =>
      comap_idealSheafDataOfChart B S hS X I hI
        (A := ⟨CostructuredArrow.mk φ, he⟩)
        (A' := ⟨CostructuredArrow.mk (yoneda.map (atlasRelationSource B S hS hs) ≫ φ),
          presheaf_etale_atlasRelation B S hS X hs he⟩)
        (ObjectProperty.homMk (CostructuredArrow.homMk g hg))
    refine Eq.trans (Scheme.IdealSheafData.pullback_subobject_mk_subschemeι _ _) ?_
    refine Eq.trans ?_ (Scheme.IdealSheafData.pullback_subobject_mk_subschemeι _ _).symm
    rw [key _ (yoneda_map_atlasRelationSource_comp B S hS hs).symm,
      key (atlasRelationSource B S hS hs) rfl]
  · intro A hA m
    rw [comap_idealSheafDataOfChart B S hS X I hI m]
    exact ker_appTop_subschemeι_idealSheafDataOfChart B S hS X I hI A hA

end Chart

end Space

end AlgebraicGeometry

end
