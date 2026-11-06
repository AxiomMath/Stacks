module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.GenericallyFiniteDominant
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EqualDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteOverDenseOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericPointsFiniteComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralGenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace

/-!
# Generically finite dominant morphisms of integral algebraic spaces

Let `f : X ⟶ Y` be a dominant morphism locally of finite type of integral algebraic spaces
over a scheme `S`, and let `x` and `y` be the generic points of `|X|` and `|Y|`. **Stacks
0AD5** asserts the equivalence of five conditions on `f` — vanishing of the relative
transcendence degree at `x`, finiteness of the extension of residue fields there, finiteness
of `f` on a pair of nonempty affine open subspaces, quasi-finiteness of `f` at `x`, and `x`
being the only point of `|X|` above `y` — and, when `f` is separated or quasi-compact, their
equivalence with finiteness of `f` over a nonempty affine open subspace of `Y`.

## Main definitions

* `AlgebraicGeometry.Space.ExistsAffineOpenFiniteRestriction`: condition (3), finiteness of
  `f` on a pair of nonempty affine open subspaces `U ⊂ X`, `V ⊂ Y` with `f(U) ⊂ V`.
* `AlgebraicGeometry.Space.IsFiniteOverAffineOpen`: condition (6), finiteness of
  `f^{-1}(V) ⟶ V` over a nonempty affine open subspace `V ⊂ Y`.

Conditions (1), (2), (4) and (5) are the existing predicates
`AlgebraicGeometry.Space.HasTranscendenceDegreeAt` (Stacks 04NM),
`AlgebraicGeometry.Space.HasFiniteResidueFieldExtensionAt`,
`AlgebraicGeometry.Space.IsQuasiFiniteAt` (Stacks 03XJ) and the uniqueness statement about
the fibre of `|X| → |Y|` over `y`.

## Main results

* `AlgebraicGeometry.Space.tfae_hasTranscendenceDegreeAt_eq_zero_and_isFiniteOverAffineOpen`:
  **Stacks 0AD5** in full.
* `AlgebraicGeometry.Space.tfae_hasTranscendenceDegreeAt_eq_zero`: the equivalence of
  conditions (1)–(5), which needs no hypothesis of separatedness or quasi-compactness.
* `AlgebraicGeometry.Space.existsAffineOpenFiniteRestriction_of_hasFiniteResidueFieldExtensionAt`:
  condition (2) implies condition (3).
* `AlgebraicGeometry.Space.isQuasiFiniteAt_genericPoint_of_existsAffineOpenFiniteRestriction`:
  condition (3) implies condition (4).
* `AlgebraicGeometry.Space.isFiniteOverAffineOpen_of_forall_eq_of_pointsMap_eq`: condition (5)
  implies condition (6), for a separated or quasi-compact morphism.
* `AlgebraicGeometry.Space.isQuasiFiniteAt_genericPoint_of_isFiniteOverAffineOpen`: condition
  (6) implies condition (4), with no further hypothesis on `f`.

## Implementation notes

The cycle closing the equivalence is (1) ⟹ (2) ⟹ (3) ⟹ (4) ⟹ (1), together with
(4) ⟺ (5) and, under the extra hypothesis, (5) ⟹ (6) ⟹ (4). The implications
(1) ⟹ (2), (4) ⟹ (1) and (4) ⟺ (5) are already in this development
(`AlgebraicGeometry.Space.finite_residueFieldHom_genericPoint_of_hasTranscendenceDegreeAt_zero`,
`AlgebraicGeometry.Space.hasTranscendenceDegreeAt_zero_of_isQuasiFiniteAt` and
`AlgebraicGeometry.Space.isQuasiFiniteAt_iff_forall_eq_of_pointsMap_eq`); what is added here
is (2) ⟹ (3), (3) ⟹ (4) and the two implications involving (6).

The source reduces conditions (1), (2), (3) to the scheme case through the schematic loci of
`Y` and of `f^{-1}(Y')`. The reduction carried out here is by a pair of *representable open
charts* through the generic points, which exist by Stacks 086U and Stacks 03IE: the scheme of
such a chart is an integral scheme (it is reduced because reducedness is étale local and an
open immersion is étale, and irreducible because the chart point over the generic point is
dense in it), the chart point over the generic point *is* the generic point of that scheme,
and the induced morphism of charts is dominant and locally of finite type. Stacks 02NX, which
this development has in full as
`AlgebraicGeometry.tfae_trdeg_functionField_eq_zero`, then applies on the charts. The
extension of residue fields the morphism of charts induces at the chart generic point is
conjugate, by isomorphisms of fields, to the extension `f` induces at `x`: each chart
residue-field point is a monomorphic field-valued representative of the point below it,
because an open immersion is a monomorphism, so Stacks 0EMW identifies its field with the
residue field there.

An affine open of the scheme of a chart is an affine open subspace of the space: the site is
closed under passing to open subschemes (`AlgebraicGeometry.Space.openSubobject`), and the
restriction of the morphism of charts to a pair of such opens is a morphism of the site
because a morphism of the site is just a morphism of schemes over `S`. That is how condition
(3) is produced from condition (3) of Stacks 02NX, and conversely such a pair of affine opens
is a pointed pair of étale charts at the generic point, in which a finite morphism of schemes
is quasi-finite; chart independence (Stacks 04NC) then gives condition (4).

Condition (6) is obtained from condition (5) through Stacks 0BBC, whose hypotheses ask that
the codimension-zero points of `|X|` and `|Y|` be finite and correspond under `f`. For an
integral algebraic space the codimension-zero points are exactly the generic point, by
Stacks 0ADC read through decency, so both hypotheses are condition (5). Stacks 0BBC produces
only a dense *open subspace* of `Y`; an affine open subspace inside it comes from a
representable dense open subspace (Stacks 086U) and an affine open of its scheme, and
finiteness descends to it by base change. In the converse direction the image of the affine
open is an open subspace of `Y` isomorphic to it, so the inverse image of that open subspace
is finite over it, and finiteness over a nonempty open subspace of the target gives
quasi-finiteness at the generic point
(`AlgebraicGeometry.Space.isQuasiFiniteAt_of_isFinite_fromPreimage`).

## References

* [Stacks Project, Tag 0AD5](https://stacks.math.columbia.edu/tag/0AD5)
* [Stacks Project, Tag 02NX](https://stacks.math.columbia.edu/tag/02NX)
* [Stacks Project, Tag 0BBC](https://stacks.math.columbia.edu/tag/0BBC)
* [Stacks Project, Tag 0ADC](https://stacks.math.columbia.edu/tag/0ADC)
* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_IntegralGenericallyFiniteTfae :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- A pullback of presheaves on the big fppf site, found from the shape instance. -/
local instance (priority := high) hasPullback_presheaf_IntegralGenericallyFiniteTfae
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Small products of presheaves on the big fppf site (instance search times out without
this shortcut). -/
local instance hasLimitsOfShape_discrete_presheaf_IntegralGenericallyFiniteTfae (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-! ### Morphisms of the site from morphisms of schemes over `S` -/

/-- A morphism of schemes between the schemes of two objects of the big fppf site over `S`
which commutes with their structure morphisms, as a morphism of the site. -/
private noncomputable def siteHomOfSchemeHom (A C : BigFppfOver B S hS)
    (k : (BigFppfOver.toScheme B S hS).obj A ⟶ (BigFppfOver.toScheme B S hS).obj C)
    (w : k ≫ B.inclusion.map C.hom = B.inclusion.map A.hom) : A ⟶ C :=
  Over.homMk (B.inclusion.preimage k) (by
    refine B.inclusion.map_injective ?_
    rw [B.inclusion.map_comp, B.inclusion.map_preimage]
    exact w)

private theorem toScheme_map_siteHomOfSchemeHom (A C : BigFppfOver B S hS)
    (k : (BigFppfOver.toScheme B S hS).obj A ⟶ (BigFppfOver.toScheme B S hS).obj C)
    (w : k ≫ B.inclusion.map C.hom = B.inclusion.map A.hom) :
    (BigFppfOver.toScheme B S hS).map (siteHomOfSchemeHom B S hS A C k w) = k :=
  B.inclusion.map_preimage k

/-! ### The point of the space below a point of a representable chart -/

/-- The point of an algebraic space below a point of the scheme of a representable chart. -/
private noncomputable def chartPt (C : BigFppfOver B S hS) (β : yoneda.obj C ⟶ X)
    (u : (BigFppfOver.toScheme B S hS).obj C) : points B S hS X :=
  pointsMap B S hS (yoneda.obj C) β
    ((schemePointRepresentative B S hS C u).class B S hS (yoneda.obj C))

private theorem chartPt_eq_comp (C : BigFppfOver B S hS) (β : yoneda.obj C ⟶ X)
    (u : (BigFppfOver.toScheme B S hS).obj C) :
    chartPt B S hS C β u =
      pointsMap B S hS (yoneda.obj C) β ((schemePointsHomeomorph B S hS C).symm u) := by
  have : (schemePointsHomeomorph B S hS C).symm u =
      (schemePointRepresentative B S hS C u).class B S hS (yoneda.obj C) := by
    refine ((schemePointsHomeomorph B S hS C).symm_apply_eq).2 ?_
    rw [schemePointsHomeomorph_apply, pointsToScheme_class, schemePointRepresentative_point]
  rw [chartPt, this]

private theorem chartPt_injective (C : BigFppfOver B S hS) (β : yoneda.obj C ⟶ X)
    (hβ : IsOpenImmersion B S hS β) : Function.Injective (chartPt B S hS C β) := by
  have : Mono β := mono_of_isOpenImmersion B S hS β hβ
  intro a b hab
  rw [chartPt_eq_comp, chartPt_eq_comp] at hab
  exact (schemePointsHomeomorph B S hS C).symm.injective
    (pointsMap_injective_of_mono B S hS β hab)

private theorem isOpen_image_chartPt (C : BigFppfOver B S hS) (β : yoneda.obj C ⟶ X)
    (hβ : IsOpenImmersion B S hS β)
    {W : Set ((BigFppfOver.toScheme B S hS).obj C)} (hW : IsOpen W) :
    IsOpen (chartPt B S hS C β '' W) := by
  have himg : chartPt B S hS C β '' W =
      pointsMap B S hS (yoneda.obj C) β '' ((schemePointsHomeomorph B S hS C).symm '' W) := by
    rw [← Set.image_comp]
    exact Set.image_congr' (chartPt_eq_comp B S hS C β)
  rw [himg]
  exact isOpenMap_pointsMap_of_presheafEtale B S hS β
    (presheaf_etale_of_isOpenImmersion B S hS hβ) _
    ((schemePointsHomeomorph B S hS C).symm.isOpenMap W hW)

private theorem range_chartPt (C : BigFppfOver B S hS) (β : yoneda.obj C ⟶ X) :
    Set.range (chartPt B S hS C β) = Set.range (pointsMap B S hS (yoneda.obj C) β) := by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 fun u ↦ ⟨_, rfl⟩) ?_
  rintro z ⟨p, rfl⟩
  exact ⟨pointsToScheme B S hS C p, by
    rw [chartPt, class_schemePointRepresentative_pointsToScheme]⟩

/-- A morphism of the site sends the class of the representative of `u` to that of its image. -/
private theorem pointsMap_yoneda_map_class_schemePointRepresentative
    (A C : BigFppfOver B S hS) (k : A ⟶ C) (u : (BigFppfOver.toScheme B S hS).obj A) :
    pointsMap B S hS (yoneda.obj A) (yoneda.map k)
        ((schemePointRepresentative B S hS A u).class B S hS (yoneda.obj A)) =
      (schemePointRepresentative B S hS C ((BigFppfOver.toScheme B S hS).map k u)).class
        B S hS (yoneda.obj C) := by
  refine injective_pointsToScheme B S hS C ?_
  rw [pointsToScheme_pointsMap, pointsToScheme_class, schemePointRepresentative_point,
    pointsToScheme_class, schemePointRepresentative_point]

/-! ### Representable open charts of an integral algebraic space -/

private theorem closure_singleton_eq_univ_of_chartPt
    (hX : IsAlgebraicSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (C : BigFppfOver B S hS) (β : yoneda.obj C ⟶ X) (hβ : IsOpenImmersion B S hS β)
    (u : (BigFppfOver.toScheme B S hS).obj C)
    (hu : chartPt B S hS C β u = genericPoint B S hS hX hInt) :
    closure ({u} : Set ((BigFppfOver.toScheme B S hS).obj C)) = Set.univ := by
  rw [← dense_iff_closure_eq, dense_iff_inter_open]
  intro V hV hVne
  refine ⟨u, ?_, rfl⟩
  have hopen : IsOpen (chartPt B S hS C β '' V) :=
    isOpen_image_chartPt B S hS C β hβ hV
  have hmem : genericPoint B S hS hX hInt ∈ chartPt B S hS C β '' V :=
    ((isGenericPoint_genericPoint B S hS hX hInt).mem_open_set_iff hopen).2
      (by simpa using hVne.image (chartPt B S hS C β))
  obtain ⟨w, hwV, hw⟩ := hmem
  rwa [chartPt_injective B S hS C β hβ (hw.trans hu.symm)] at hwV

private theorem isIntegral_chart
    (hX : IsAlgebraicSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (C : BigFppfOver B S hS) (β : yoneda.obj C ⟶ X) (hβ : IsOpenImmersion B S hS β)
    (u : (BigFppfOver.toScheme B S hS).obj C)
    (hu : chartPt B S hS C β u = genericPoint B S hS hX hInt) :
    IsIntegral ((BigFppfOver.toScheme B S hS).obj C) := by
  have hred : IsReduced ((BigFppfOver.toScheme B S hS).obj C) :=
    (exists_atlas_iff_forall_etale B S hS X (fun Z : Scheme.{u} ↦ IsReduced Z) hX).1 hInt.1 C β
      (presheaf_etale_of_isOpenImmersion B S hS hβ)
  have hirr : IrreducibleSpace ((BigFppfOver.toScheme B S hS).obj C) := by
    refine (irreducibleSpace_def _).2 ?_
    have h := closure_singleton_eq_univ_of_chartPt B S hS hX hInt C β hβ u hu
    have : (⊤ : Set ((BigFppfOver.toScheme B S hS).obj C)) =
        closure ({u} : Set ((BigFppfOver.toScheme B S hS).obj C)) := by
      rw [h]; rfl
    rw [this]
    exact isIrreducible_singleton.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

private theorem eq_genericPoint_of_chartPt
    (hX : IsAlgebraicSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (C : BigFppfOver B S hS) (β : yoneda.obj C ⟶ X) (hβ : IsOpenImmersion B S hS β)
    (u : (BigFppfOver.toScheme B S hS).obj C)
    (hu : chartPt B S hS C β u = genericPoint B S hS hX hInt)
    [IsIntegral ((BigFppfOver.toScheme B S hS).obj C)] :
    u = _root_.genericPoint ((BigFppfOver.toScheme B S hS).obj C) := by
  have h : IsGenericPoint u (Set.univ : Set ((BigFppfOver.toScheme B S hS).obj C)) :=
    closure_singleton_eq_univ_of_chartPt B S hS hX hInt C β hβ u hu
  exact h.eq (_root_.genericPoint_spec ((BigFppfOver.toScheme B S hS).obj C))

/-! ### Quasi-finiteness read on one chart -/

private theorem isQuasiFiniteAt_of_chart (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hlft : IsLocallyOfFiniteType B S hS f)
    (x : points B S hS X) (c : EtaleChartAtPoint B S hS f x)
    (hc : quasiFiniteAt ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS)) :
    IsQuasiFiniteAt B S hS f x := by
  have hQ := MorphismOfGerms.hasRepresentativeWithProperty_isEtaleLocalOnSourceAndTarget
    ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget.{u}
  have hcl : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map c.h) :=
    hlft c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm
  have hall := (holdsOnEveryEtaleChartAtPoint_iff_some B S hS _ hQ hX hY f x).2
    ⟨c, (quasiFiniteAt_iff_hasRepresentativeWithProperty _ _).1 hc⟩
  refine (isQuasiFiniteAt_iff_forall_quasiFiniteAt_chart B S hS hX hY f hlft x).2 fun d ↦ ?_
  have hdl : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map d.h) :=
    hlft d.U d.V d.a d.b d.h d.a_etale d.b_etale d.comm
  exact (quasiFiniteAt_iff_hasRepresentativeWithProperty _ _).2 (hall d)

/-! ### The residue field extension read on a pair of open charts -/

/-- **The residue-field extension of a morphism of decent algebraic spaces, read on a pair of
representable open charts.** If `f` is induced on open charts `α` of `X` and `β` of `Y` by a
morphism `h` of the site, and `u` is a point of the source chart lying over `x`, then the
homomorphism of residue fields `f` induces at `x` is conjugate, by isomorphisms of fields, to
the homomorphism of residue fields `h` induces at `u`.

An open immersion is a monomorphism, so each chart residue-field point is a monomorphic
field-valued representative of the point below it, and its field is therefore the residue
field there through a bijective homomorphism. The two squares over `Y` obtained from the two
factorizations agree because the residue-field morphism of `Y` is a monomorphism. -/
private theorem exists_ringEquiv_residueFieldHom_chart
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X)
    (CX CY : BigFppfOver B S hS) (α : yoneda.obj CX ⟶ X) (β : yoneda.obj CY ⟶ Y)
    (hα : IsOpenImmersion B S hS α) (hβ : IsOpenImmersion B S hS β) (h : CX ⟶ CY)
    (hcomm : yoneda.map h ≫ β = α ≫ f)
    (u : (BigFppfOver.toScheme B S hS).obj CX)
    (hu : pointsMap B S hS (yoneda.obj CX) α
      ((schemePointRepresentative B S hS CX u).class B S hS (yoneda.obj CX)) = x) :
    ∃ (eX : residueField B S hS X hXdec x ≃+*
        ((BigFppfOver.toScheme B S hS).obj CX).residueField u)
      (eY : residueField B S hS Y hYdec (pointsMap B S hS X f x) ≃+*
        ((BigFppfOver.toScheme B S hS).obj CY).residueField
          ((BigFppfOver.toScheme B S hS).map h u)),
      ∀ a, eX (residueFieldHom B S hS X Y hY hXdec hYdec f x a) =
        (((BigFppfOver.toScheme B S hS).map h).residueFieldMap u).hom (eY a) := by
  classical
  set v := (BigFppfOver.toScheme B S hS).map h u with hvdef
  set qu := schemePointRepresentative B S hS CX u with hqudef
  set qv := schemePointRepresentative B S hS CY v with hqvdef
  -- the two chart residue-field points, as monomorphic representatives
  have hvclass : pointsMap B S hS (yoneda.obj CX) (yoneda.map h)
      (qu.class B S hS (yoneda.obj CX)) = qv.class B S hS (yoneda.obj CY) :=
    pointsMap_yoneda_map_class_schemePointRepresentative B S hS CX CY h u
  set qX := FieldValuedPoint.map B S hS (yoneda.obj CX) α qu with hqXdef
  set qY := FieldValuedPoint.map B S hS (yoneda.obj CY) β qv with hqYdef
  have hqXclass : qX.class B S hS X = x := hu
  have hqYclass : qY.class B S hS Y = pointsMap B S hS X f x := by
    have h1 : pointsMap B S hS X f x =
        pointsMap B S hS (yoneda.obj CX) (α ≫ f) (qu.class B S hS (yoneda.obj CX)) := by
      rw [pointsMap_comp, Function.comp_apply, hu]
    rw [h1, ← hcomm, pointsMap_comp, Function.comp_apply, hvclass]
    rfl
  have hmonoα : Mono α :=
    mono_of_isImmersion B S hS (isImmersion_of_isOpenImmersion B S hS hα)
  have hmonoβ : Mono β :=
    mono_of_isImmersion B S hS (isImmersion_of_isOpenImmersion B S hS hβ)
  have hmonoqu : Mono (yoneda.map qu.siteHom) := by
    rw [← fieldMorphism_yoneda B S hS qu, hqudef]
    exact mono_fieldMorphism_schemePointRepresentative B S hS CX u
  have hmonoqv : Mono (yoneda.map qv.siteHom) := by
    rw [← fieldMorphism_yoneda B S hS qv, hqvdef]
    exact mono_fieldMorphism_schemePointRepresentative B S hS CY v
  have hqXmor : fieldMorphism B S hS X qX = yoneda.map qu.siteHom ≫ α :=
    fieldMorphism_map_yoneda B S hS X α qu
  have hqYmor : fieldMorphism B S hS Y qY = yoneda.map qv.siteHom ≫ β :=
    fieldMorphism_map_yoneda B S hS Y β qv
  have hmonoqX : Mono (fieldMorphism B S hS X qX) := by
    rw [hqXmor]; exact mono_comp' hmonoqu hmonoα
  have hmonoqY : Mono (fieldMorphism B S hS Y qY) := by
    rw [hqYmor]; exact mono_comp' hmonoqv hmonoβ
  -- the two comparison homomorphisms with the residue fields of the spaces
  obtain ⟨φX, gX, hφXbij, hgXspec, hgXsq⟩ :=
    exists_bijective_residueFieldHom_of_mono B S hS hX hXdec x qX hqXclass hmonoqX
  obtain ⟨φY, gY, hφYbij, hgYspec, hgYsq⟩ :=
    exists_bijective_residueFieldHom_of_mono B S hS hY hYdec
      (pointsMap B S hS X f x) qY hqYclass hmonoqY
  -- the comparison morphism of the two chart residue-field points
  have hmonoqv' : Mono (yonedaEquiv.symm qv.value) := by
    rw [show yonedaEquiv.symm qv.value = yoneda.map qv.siteHom from
      fieldMorphism_yoneda B S hS qv]
    exact hmonoqv
  obtain ⟨gh, hgh, -⟩ := FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B S hS
    (yoneda.obj CY) (isAlgebraicSpace_yoneda B S hS CY) qv
    (FieldValuedPoint.map B S hS (yoneda.obj CX) (yoneda.map h) qu) hvclass.symm
  have hghsq : gh ≫ qv.siteHom = qu.siteHom ≫ h := hgh
  have e1 : (BigFppfOver.toScheme B S hS).map qu.siteHom =
      ((BigFppfOver.toScheme B S hS).obj CX).fromSpecResidueField u :=
    toScheme_map_siteHom_schemePointRepresentative B S hS CX u
  have e2 : (BigFppfOver.toScheme B S hS).map qv.siteHom =
      ((BigFppfOver.toScheme B S hS).obj CY).fromSpecResidueField v :=
    toScheme_map_siteHom_schemePointRepresentative B S hS CY v
  have hghspec : B.inclusion.map gh.left =
      Spec.map ((((BigFppfOver.toScheme B S hS).map h)).residueFieldMap u) := by
    have k1 : (BigFppfOver.toScheme B S hS).map gh ≫
          (BigFppfOver.toScheme B S hS).map qv.siteHom =
        (BigFppfOver.toScheme B S hS).map qu.siteHom ≫
          (BigFppfOver.toScheme B S hS).map h :=
      ((BigFppfOver.toScheme B S hS).map_comp gh qv.siteHom).symm.trans
        ((congrArg (fun k : qu.siteObject B S hS (yoneda.obj CX) ⟶ CY ↦
            (BigFppfOver.toScheme B S hS).map k) hghsq).trans
          ((BigFppfOver.toScheme B S hS).map_comp qu.siteHom h))
    have hcan : (BigFppfOver.toScheme B S hS).map gh ≫
          ((BigFppfOver.toScheme B S hS).obj CY).fromSpecResidueField v =
        ((BigFppfOver.toScheme B S hS).obj CX).fromSpecResidueField u ≫
          (BigFppfOver.toScheme B S hS).map h := by
      rw [← e2, ← e1]
      exact k1
    have hsqScheme :
        Spec.map ((((BigFppfOver.toScheme B S hS).map h)).residueFieldMap u) ≫
            ((BigFppfOver.toScheme B S hS).obj CY).fromSpecResidueField v =
          ((BigFppfOver.toScheme B S hS).obj CX).fromSpecResidueField u ≫
            (BigFppfOver.toScheme B S hS).map h :=
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ u
    show (BigFppfOver.toScheme B S hS).map gh = _
    exact (cancel_mono
      (((BigFppfOver.toScheme B S hS).obj CY).fromSpecResidueField v)).1
      (hcan.trans hsqScheme.symm)
  -- the square over `Y` identifies the composite with the induced homomorphism
  have hspec0 := residueFieldHom_spec B S hS X Y hY hXdec hYdec f x
  change ∃ g : _, _ ∧ _ at hspec0
  obtain ⟨g₀, hg₀spec, hg₀sq⟩ := hspec0
  have hmonoY : Mono (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X f x)) :=
    (residueFieldRepresentative B S hS Y hYdec (pointsMap B S hS X f x)).2.2
  have hsq1 : yoneda.map gX ≫ (yoneda.map g₀ ≫
        residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X f x)) =
      yoneda.map qu.siteHom ≫ (α ≫ f) :=
    (congrArg (fun k ↦ yoneda.map gX ≫ k) hg₀sq).trans
      (((Category.assoc _ _ _).symm.trans (congrArg (fun k ↦ k ≫ f) hgXsq)).trans
        ((congrArg (fun k ↦ k ≫ f) hqXmor).trans (Category.assoc _ _ _)))
  have hsq2 : yoneda.map gh ≫ (yoneda.map gY ≫
        residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X f x)) =
      yoneda.map qu.siteHom ≫ (α ≫ f) :=
    (congrArg (fun k ↦ yoneda.map gh ≫ k) (hgYsq.trans hqYmor)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k ↦ k ≫ β) (yoneda.map_comp gh qv.siteHom).symm).trans
          ((congrArg (fun k : qu.siteObject B S hS (yoneda.obj CX) ⟶ CY ↦
              yoneda.map k ≫ β) hghsq).trans
            ((congrArg (fun k ↦ k ≫ β) (yoneda.map_comp qu.siteHom h)).trans
              ((Category.assoc _ _ _).trans
                (congrArg (fun k ↦ yoneda.map qu.siteHom ≫ k) hcomm))))))
  have key : yoneda.map gX ≫ yoneda.map g₀ = yoneda.map gh ≫ yoneda.map gY :=
    (cancel_mono (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X f x))).1
      (((Category.assoc _ _ _).trans hsq1).trans ((Category.assoc _ _ _).trans hsq2).symm)
  have hm : gX ≫ g₀ = gh ≫ gY :=
    yoneda.map_injective
      ((yoneda.map_comp gX g₀).trans (key.trans (yoneda.map_comp gh gY).symm))
  have hA : B.inclusion.map gX.left ≫ B.inclusion.map g₀.left =
      B.inclusion.map gh.left ≫ B.inclusion.map gY.left := by
    have e := congrArg (fun k : qu.siteObject B S hS (yoneda.obj CX) ⟶
        (residueFieldRepresentative B S hS Y hYdec
          (pointsMap B S hS X f x)).1.siteObject B S hS Y ↦
      B.inclusion.map k.left) hm
    exact ((B.inclusion.map_comp gX.left g₀.left).symm.trans e).trans
      (B.inclusion.map_comp gh.left gY.left)
  have hA2 : Spec.map (CommRingCat.ofHom φX) ≫
        Spec.map (CommRingCat.ofHom (residueFieldHom B S hS X Y hY hXdec hYdec f x)) =
      Spec.map ((((BigFppfOver.toScheme B S hS).map h)).residueFieldMap u) ≫
        Spec.map (CommRingCat.ofHom φY) := by
    have eL : Spec.map (CommRingCat.ofHom φX) ≫
        Spec.map (CommRingCat.ofHom (residueFieldHom B S hS X Y hY hXdec hYdec f x)) =
        B.inclusion.map gX.left ≫ B.inclusion.map g₀.left := by
      rw [hgXspec, hg₀spec]
    have eR : Spec.map ((((BigFppfOver.toScheme B S hS).map h)).residueFieldMap u) ≫
        Spec.map (CommRingCat.ofHom φY) =
        B.inclusion.map gh.left ≫ B.inclusion.map gY.left :=
      (congrArg (fun k ↦ Spec.map
          ((((BigFppfOver.toScheme B S hS).map h)).residueFieldMap u) ≫ k)
          hgYspec.symm).trans
        (congrArg (fun k ↦ k ≫ B.inclusion.map gY.left) hghspec.symm)
    exact (eL.trans hA).trans eR.symm
  have h0 : CommRingCat.ofHom (residueFieldHom B S hS X Y hY hXdec hYdec f x) ≫
        CommRingCat.ofHom φX =
      CommRingCat.ofHom φY ≫
        (((BigFppfOver.toScheme B S hS).map h).residueFieldMap u) :=
    Spec.map_injective
      ((Spec.map_comp _ _).trans (hA2.trans (Spec.map_comp _ _).symm))
  have hpt : ∀ a, φX (residueFieldHom B S hS X Y hY hXdec hYdec f x a) =
      ((((BigFppfOver.toScheme B S hS).map h).residueFieldMap u).hom) (φY a) := fun a ↦
    RingHom.congr_fun (congrArg CommRingCat.Hom.hom h0) a
  exact ⟨RingEquiv.ofBijective φX hφXbij, RingEquiv.ofBijective φY hφYbij, hpt⟩

/-! ### Composites of open immersions -/

private theorem isOpenImmersion_comp' {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} {b : G ⟶ H} (ha : IsOpenImmersion B S hS a) (hb : IsOpenImmersion B S hS b) :
    IsOpenImmersion B S hS (a ≫ b) := by
  set P := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS) with hP
  have _hP1 : P.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage (BigFppfOver.toScheme B S hS)
  have _hP2 : P.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition P
  exact MorphismProperty.comp_mem _ _ _ ha hb

/-! ### The image of a point of a chart -/

private theorem chartPt_map (f : X ⟶ Y) (CX CY : BigFppfOver B S hS)
    (α : yoneda.obj CX ⟶ X) (β : yoneda.obj CY ⟶ Y) (h : CX ⟶ CY)
    (hcomm : yoneda.map h ≫ β = α ≫ f) (u : (BigFppfOver.toScheme B S hS).obj CX) :
    chartPt B S hS CY β ((BigFppfOver.toScheme B S hS).map h u) =
      pointsMap B S hS X f (chartPt B S hS CX α u) := by
  rw [chartPt, chartPt,
    ← pointsMap_yoneda_map_class_schemePointRepresentative B S hS CX CY h u, ← Function.comp_apply
      (f := pointsMap B S hS (yoneda.obj CY) β), ← pointsMap_comp, hcomm, pointsMap_comp,
    Function.comp_apply]

/-! ### Opens of the scheme of an object of the site -/

private theorem inclusion_map_hom_openSubobject (T : BigFppfOver B S hS) {A : Scheme.{u}}
    (j : A ⟶ (BigFppfOver.toScheme B S hS).obj T)
    (hj : _root_.AlgebraicGeometry.IsOpenImmersion j) :
    B.inclusion.map (openSubobject B S hS T j hj).hom = j ≫ B.inclusion.map T.hom := by
  have hw := Over.w (openSubobjectHom B S hS T j hj)
  have h2 := congrArg (fun k ↦ B.inclusion.map k) hw
  simp only [B.inclusion.map_comp] at h2
  rw [← h2]
  congr 1
  exact toScheme_map_openSubobjectHom B S hS T j hj

/-! ### Conditions (3) and (6) of Stacks 0AD5 -/

/-- **Condition (3) of Stacks 0AD5.** There are nonempty affine open subspaces `U ⊂ X` and
`V ⊂ Y` with `f(U) ⊂ V` such that the restriction `f|_U : U ⟶ V` is a finite morphism.

An affine open subspace is presented by an open immersion from the presheaf represented by an
object of the site whose scheme is affine, and the restriction of `f` is a morphism of the site
making the square of the two open immersions commute. -/
def ExistsAffineOpenFiniteRestriction (f : X ⟶ Y) : Prop :=
  ∃ (U V : BigFppfOver B S hS) (iU : yoneda.obj U ⟶ X) (iV : yoneda.obj V ⟶ Y) (g : U ⟶ V),
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      Nonempty ((BigFppfOver.toScheme B S hS).obj U) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      Nonempty ((BigFppfOver.toScheme B S hS).obj V) ∧
      IsOpenImmersion B S hS iU ∧ IsOpenImmersion B S hS iV ∧
      yoneda.map g ≫ iV = iU ≫ f ∧
      _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map g)

/-- **Condition (6) of Stacks 0AD5.** There is a nonempty affine open subspace `V ⊂ Y` such
that `f^{-1}(V) ⟶ V` is a finite morphism, the inverse image being the fibre product of `f`
along the open immersion presenting `V`. -/
def IsFiniteOverAffineOpen (f : X ⟶ Y) : Prop :=
  ∃ (V : BigFppfOver B S hS) (iV : yoneda.obj V ⟶ Y),
    IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      Nonempty ((BigFppfOver.toScheme B S hS).obj V) ∧
      IsOpenImmersion B S hS iV ∧
      IsFinite B S hS (Limits.pullback.snd f iV)

private theorem chartPt_comp (A C : BigFppfOver B S hS) (k : A ⟶ C)
    (β : yoneda.obj C ⟶ X) (u : (BigFppfOver.toScheme B S hS).obj A) :
    chartPt B S hS A (yoneda.map k ≫ β) u =
      chartPt B S hS C β ((BigFppfOver.toScheme B S hS).map k u) := by
  rw [chartPt, chartPt, ← pointsMap_yoneda_map_class_schemePointRepresentative B S hS A C k u,
    pointsMap_comp, Function.comp_apply]

/-! ### Condition (3) implies quasi-finiteness at the generic point -/

/-- **Stacks 0AD5, condition (3) implies condition (4).** If `f` is finite on a pair of
nonempty affine open subspaces, then it is quasi-finite at the generic point of an integral
source: the generic point lies in every nonempty open subspace, so the pair of affine opens is
a pointed pair of étale charts there, and a finite morphism of schemes is quasi-finite at every
point. -/
theorem isQuasiFiniteAt_genericPoint_of_existsAffineOpenFiniteRestriction
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXInt : IsIntegralSpace B S hS X) (f : X ⟶ Y)
    (hlft : IsLocallyOfFiniteType B S hS f)
    (hfin : ExistsAffineOpenFiniteRestriction B S hS f) :
    IsQuasiFiniteAt B S hS f (genericPoint B S hS hX hXInt) := by
  obtain ⟨U, V, iU, iV, g, hUaff, hUne, hVaff, hVne, hiU, hiV, hgcomm, hgfin⟩ := hfin
  have hopen : IsOpen (Set.range (chartPt B S hS U iU)) := by
    rw [← Set.image_univ]
    exact isOpen_image_chartPt B S hS U iU hiU isOpen_univ
  have hmem : genericPoint B S hS hX hXInt ∈ Set.range (chartPt B S hS U iU) :=
    ((isGenericPoint_genericPoint B S hS hX hXInt).mem_open_set_iff hopen).2
      (by simpa using Set.range_nonempty (chartPt B S hS U iU))
  obtain ⟨u, hu⟩ := hmem
  let c : EtaleChartAtPoint B S hS f (genericPoint B S hS hX hXInt) :=
    { U := U
      V := V
      a := iU
      b := iV
      h := g
      a_etale := presheaf_etale_of_isOpenImmersion B S hS hiU
      b_etale := presheaf_etale_of_isOpenImmersion B S hS hiV
      comm := hgcomm
      representative := schemePointRepresentative B S hS U u
      point := IsLocalRing.closedPoint _
      maps_to := hu }
  refine isQuasiFiniteAt_of_chart B S hS hX hY f hlft _ c ?_
  have hsource : c.sourcePoint B S hS = u := schemePointRepresentative_point B S hS U u
  rw [hsource]
  have hgf : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map g) := hgfin
  exact ⟨finiteTypeAt_of_locallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) u,
    Scheme.Hom.quasiFiniteAt ((BigFppfOver.toScheme B S hS).map g) u⟩

/-! ### Condition (3) from a pair of affine opens of a pair of charts -/

private theorem inclusion_map_hom_comp (A C : BigFppfOver B S hS) (k : A ⟶ C) :
    (BigFppfOver.toScheme B S hS).map k ≫ B.inclusion.map C.hom =
      B.inclusion.map A.hom := by
  have h2 := congrArg (fun m ↦ B.inclusion.map m) (Over.w k)
  rw [B.inclusion.map_comp] at h2
  exact h2

private theorem existsAffineOpenFiniteRestriction_of_chart (f : X ⟶ Y)
    (CX CY : BigFppfOver B S hS) (α : yoneda.obj CX ⟶ X) (β : yoneda.obj CY ⟶ Y)
    (hα : IsOpenImmersion B S hS α) (hβ : IsOpenImmersion B S hS β) (h : CX ⟶ CY)
    (hcomm : yoneda.map h ≫ β = α ≫ f)
    (U₀ : ((BigFppfOver.toScheme B S hS).obj CX).affineOpens)
    (V₀ : ((BigFppfOver.toScheme B S hS).obj CY).affineOpens)
    (hUV : U₀.1 ≤ (BigFppfOver.toScheme B S hS).map h ⁻¹ᵁ V₀.1)
    (hUne : (U₀.1 : Set ((BigFppfOver.toScheme B S hS).obj CX)).Nonempty)
    (hVne : (V₀.1 : Set ((BigFppfOver.toScheme B S hS).obj CY)).Nonempty)
    (hfin : _root_.AlgebraicGeometry.IsFinite
      (((BigFppfOver.toScheme B S hS).map h).resLE V₀.1 U₀.1 hUV)) :
    ExistsAffineOpenFiniteRestriction B S hS f := by
  have hjU : _root_.AlgebraicGeometry.IsOpenImmersion U₀.1.ι := inferInstance
  have hjV : _root_.AlgebraicGeometry.IsOpenImmersion V₀.1.ι := inferInstance
  set jU := openSubobjectHom B S hS CX U₀.1.ι hjU with hjUdef
  set jV := openSubobjectHom B S hS CY V₀.1.ι hjV with hjVdef
  have hmjU : (BigFppfOver.toScheme B S hS).map jU = U₀.1.ι :=
    toScheme_map_openSubobjectHom B S hS CX U₀.1.ι hjU
  have hmjV : (BigFppfOver.toScheme B S hS).map jV = V₀.1.ι :=
    toScheme_map_openSubobjectHom B S hS CY V₀.1.ι hjV
  have hw : ((BigFppfOver.toScheme B S hS).map h).resLE V₀.1 U₀.1 hUV ≫
      B.inclusion.map (openSubobject B S hS CY V₀.1.ι hjV).hom =
      B.inclusion.map (openSubobject B S hS CX U₀.1.ι hjU).hom := by
    rw [inclusion_map_hom_openSubobject, inclusion_map_hom_openSubobject,
      ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, inclusion_map_hom_comp]
  set g := siteHomOfSchemeHom B S hS (openSubobject B S hS CX U₀.1.ι hjU)
    (openSubobject B S hS CY V₀.1.ι hjV)
    (((BigFppfOver.toScheme B S hS).map h).resLE V₀.1 U₀.1 hUV) hw with hgdef
  have hmg : (BigFppfOver.toScheme B S hS).map g =
      ((BigFppfOver.toScheme B S hS).map h).resLE V₀.1 U₀.1 hUV :=
    toScheme_map_siteHomOfSchemeHom B S hS _ _ _ hw
  have hgjV : g ≫ jV = jU ≫ h := by
    refine BigFppfOver.map_toScheme_injective B S hS ?_
    show (BigFppfOver.toScheme B S hS).map (g ≫ jV) =
      (BigFppfOver.toScheme B S hS).map (jU ≫ h)
    rw [Functor.map_comp, Functor.map_comp, hmg, hmjU, hmjV]
    exact Scheme.Hom.resLE_comp_ι ..
  refine ⟨openSubobject B S hS CX U₀.1.ι hjU, openSubobject B S hS CY V₀.1.ι hjV,
    yoneda.map jU ≫ α, yoneda.map jV ≫ β, g, U₀.2, hUne.to_subtype, V₀.2, hVne.to_subtype,
    isOpenImmersion_comp' B S hS
      (isOpenImmersion_yoneda_map_openSubobjectHom B S hS CX U₀.1.ι hjU) hα,
    isOpenImmersion_comp' B S hS
      (isOpenImmersion_yoneda_map_openSubobjectHom B S hS CY V₀.1.ι hjV) hβ, ?_, ?_⟩
  · calc yoneda.map g ≫ yoneda.map jV ≫ β
        = yoneda.map (g ≫ jV) ≫ β := by rw [Functor.map_comp, Category.assoc]
      _ = yoneda.map (jU ≫ h) ≫ β := by rw [hgjV]
      _ = yoneda.map jU ≫ yoneda.map h ≫ β := by rw [Functor.map_comp, Category.assoc]
      _ = (yoneda.map jU ≫ α) ≫ f := by rw [hcomm, Category.assoc]
  · rw [hmg]; exact hfin

/-! ### Codimension-zero points of an integral algebraic space -/

private theorem range_pointsMap_iso_hom_comp' {A A' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : A ≅ A') (g : A' ⟶ X) :
    Set.range (pointsMap B S hS A (e.hom ≫ g)) = Set.range (pointsMap B S hS A' g) := by
  have hsurj : Function.Surjective (pointsMap B S hS A e.hom) :=
    (pointsHomeomorphOfIso B S hS e).surjective
  rw [pointsMap_comp, Set.range_comp, hsurj.range_eq, Set.image_univ]


private theorem setOf_localRingDimension_eq_zero
    (hX : IsAlgebraicSpace B S hS X) (hXInt : IsIntegralSpace B S hS X) :
    {z : points B S hS X | localRingDimension B S hS z = 0} =
      {genericPoint B S hS hX hXInt} := by
  let : T0Space (points B S hS X) := t0Space_points_of_isDecentSpace B S hS hX hXInt.2.1
  let : QuasiSober (points B S hS X) := quasiSober_points_of_isDecentSpace B S hS hX hXInt.2.1
  let : IrreducibleSpace (points B S hS X) := hXInt.2.2
  have h1 : {z : points B S hS X | localRingDimension B S hS z = 0} =
      genericPoints (points B S hS X) := by
    ext z
    exact (mem_genericPoints_iff_localRingDimension_eq_zero B S hS hX hXInt.2.1 z).symm
  have h2 : _root_.genericPoint (points B S hS X) = genericPoint B S hS hX hXInt :=
    (_root_.genericPoint_spec (points B S hS X)).eq
      (isGenericPoint_genericPoint B S hS hX hXInt)
  rw [h1, genericPoints_eq_singleton, h2]

/-! ### An affine open subspace inside a dense open subspace -/

private theorem exists_affine_open_le_of_dense
    (hY : IsAlgebraicSpace B S hS Y) (hYInt : IsIntegralSpace B S hS Y)
    (V₀ : Subfunctor Y) (hV₀ : IsOpenSubspace B S hS V₀)
    (hV₀dense : Dense (Set.range (pointsMap B S hS V₀.toFunctor V₀.ι))) :
    ∃ (VA : BigFppfOver B S hS) (iVA : yoneda.obj VA ⟶ Y)
      (k : yoneda.obj VA ⟶ V₀.toFunctor),
      IsAffine ((BigFppfOver.toScheme B S hS).obj VA) ∧
        Nonempty ((BigFppfOver.toScheme B S hS).obj VA) ∧
        IsOpenImmersion B S hS iVA ∧ k ≫ V₀.ι = iVA := by
  obtain ⟨H, hH, hHle, hHrep⟩ :=
    exists_isDenseOpenSubspace_isRepresentable_le B S hS hY hYInt (U := V₀) ⟨hV₀, hV₀dense⟩
  have hrep : H.toFunctor.IsRepresentable := hHrep
  have hβ : IsOpenImmersion B S hS (H.toFunctor.reprW.hom ≫ H.ι) :=
    MorphismProperty.RespectsIso.precomp _ H.toFunctor.reprW.hom H.ι hH.1.2
  have hmem0 : genericPoint B S hS hY hYInt ∈
      Set.range (pointsMap B S hS (yoneda.obj H.toFunctor.reprX)
        (H.toFunctor.reprW.hom ≫ H.ι)) := by
    rw [range_pointsMap_iso_hom_comp']
    exact genericPoint_mem_range_pointsMap_ι B S hS hY hYInt hH
  have hmem : genericPoint B S hS hY hYInt ∈
      Set.range (chartPt B S hS H.toFunctor.reprX (H.toFunctor.reprW.hom ≫ H.ι)) := by
    rw [range_chartPt]
    exact hmem0
  obtain ⟨v, -⟩ := hmem
  obtain ⟨W, hvW⟩ :
      ∃ W : ((BigFppfOver.toScheme B S hS).obj H.toFunctor.reprX).affineOpens, v ∈ W.1 := by
    have hbasis := ((BigFppfOver.toScheme B S hS).obj
      H.toFunctor.reprX).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ v) isOpen_univ
    obtain ⟨_, ⟨W, hW, rfl⟩, hvW, -⟩ := hbasis
    exact ⟨⟨W, hW⟩, hvW⟩
  have hjW : _root_.AlgebraicGeometry.IsOpenImmersion W.1.ι := inferInstance
  refine ⟨openSubobject B S hS H.toFunctor.reprX W.1.ι hjW,
    yoneda.map (openSubobjectHom B S hS H.toFunctor.reprX W.1.ι hjW) ≫
      (H.toFunctor.reprW.hom ≫ H.ι),
    yoneda.map (openSubobjectHom B S hS H.toFunctor.reprX W.1.ι hjW) ≫
      (H.toFunctor.reprW.hom ≫ Subfunctor.homOfLe hHle),
    W.2, ⟨⟨v, hvW⟩⟩,
    isOpenImmersion_comp' B S hS
      (isOpenImmersion_yoneda_map_openSubobjectHom B S hS H.toFunctor.reprX W.1.ι hjW) hβ, ?_⟩
  rw [Category.assoc, Category.assoc, Subfunctor.homOfLe_ι]

/-! ### Conditions (5) and (6) of Stacks 0AD5 -/

/-- **Stacks 0AD5, condition (5) implies condition (6).** Let `f` be a dominant morphism
locally of finite type of integral algebraic spaces over `S` which is separated or
quasi-compact. If the generic point of `|X|` is the only point above the generic point of
`|Y|`, then `f` is finite over a nonempty affine open subspace of `Y`.

The set of codimension-zero points of an integral algebraic space is the singleton of its
generic point, so the hypothesis says exactly that the codimension-zero points of `|X|` are
the inverse image of those of `|Y|`; Stacks 0BBC then makes `f` finite over a dense open
subspace of `Y`, and a nonempty affine open subspace inside it, obtained from a representable
dense open subspace by Stacks 086U, inherits that finiteness by base change. -/
theorem isFiniteOverAffineOpen_of_forall_eq_of_pointsMap_eq
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXInt : IsIntegralSpace B S hS X) (hYInt : IsIntegralSpace B S hS Y)
    (f : X ⟶ Y) (hlft : IsLocallyOfFiniteType B S hS f) (hdom : IsDominant B S hS f)
    (hsep_or_qc : IsSeparated B S hS f ∨ IsQuasiCompact B S hS f)
    (huniq : ∀ x' : points B S hS X,
      pointsMap B S hS X f x' = genericPoint B S hS hY hYInt →
        x' = genericPoint B S hS hX hXInt) :
    IsFiniteOverAffineOpen B S hS f := by
  have hX0 : {z : points B S hS X | localRingDimension B S hS z = 0} =
      {genericPoint B S hS hX hXInt} := setOf_localRingDimension_eq_zero B S hS hX hXInt
  have hY0 : {z : points B S hS Y | localRingDimension B S hS z = 0} =
      {genericPoint B S hS hY hYInt} := setOf_localRingDimension_eq_zero B S hS hY hYInt
  have hpre : pointsMap B S hS X f ⁻¹'
      {z : points B S hS Y | localRingDimension B S hS z = 0} =
      {z : points B S hS X | localRingDimension B S hS z = 0} := by
    rw [hX0, hY0]
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun hz ↦ huniq z hz, fun hz ↦ ?_⟩
    rw [hz]
    exact pointsMap_genericPoint_of_isDominant B S hS hX hY hXInt hYInt f hdom
  obtain ⟨V₀, hV₀, hV₀dense, hV₀fin⟩ :=
    exists_isDenseOpenSubspace_isFinite_pullback_snd B S hS hX hY f hlft hYInt.2.1
      (by rw [hX0]; exact Set.finite_singleton _)
      (by rw [hY0]; exact Set.finite_singleton _)
      hpre (hsep_or_qc.elim Or.inr Or.inl)
  obtain ⟨VA, iVA, k, hVAaff, hVAne, hiVA, hk⟩ :=
    exists_affine_open_le_of_dense B S hS hY hYInt V₀ hV₀ hV₀dense
  refine ⟨VA, iVA, hVAaff, hVAne, hiVA, ?_⟩
  have hcond : pullback.fst f iVA ≫ f = (pullback.snd f iVA ≫ k) ≫ V₀.ι := by
    rw [Category.assoc, hk]
    exact pullback.condition
  have sq : IsPullback
      (pullback.lift (pullback.fst f iVA) (pullback.snd f iVA ≫ k) hcond)
      (pullback.snd f iVA) (pullback.snd f V₀.ι) k := by
    refine IsPullback.of_right (h₁₂ := pullback.fst f V₀.ι) (h₂₂ := V₀.ι)
      (v₁₃ := f) ?_ ?_ ?_
    · simpa only [pullback.lift_fst, hk] using IsPullback.of_hasPullback f iVA
    · exact pullback.lift_snd _ _ _
    · exact IsPullback.of_hasPullback f V₀.ι
  exact isFinite_of_isPullback B S hS sq hV₀fin

/-- **Stacks 0AD5, condition (6) implies condition (4).** Finiteness over a nonempty affine
open subspace of the target makes a dominant morphism of integral algebraic spaces
quasi-finite at the generic point of its source, with no assumption of separatedness or
quasi-compactness.

The image of the affine open is an open subspace of `Y`, isomorphic to it, so the inverse
image of that open subspace is finite over it by base change along an isomorphism. -/
theorem isQuasiFiniteAt_genericPoint_of_isFiniteOverAffineOpen
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXInt : IsIntegralSpace B S hS X) (hYInt : IsIntegralSpace B S hS Y)
    (f : X ⟶ Y) (hdom : IsDominant B S hS f)
    (hfin : IsFiniteOverAffineOpen B S hS f) :
    IsQuasiFiniteAt B S hS f (genericPoint B S hS hX hXInt) := by
  obtain ⟨V, iV, hVaff, hVne, hiV, hfinV⟩ := hfin
  have hmonoiV : Mono iV := mono_of_isOpenImmersion B S hS iV hiV
  set W := Subfunctor.range iV with hWdef
  have hW : IsOpenSubspace B S hS W :=
    isOpenSubspace_range_of_isOpenImmersion V iV hiV
  set e := rangeIsoOfIsOpenImmersion V iV hiV with hedef
  have hefac : e.hom ≫ W.ι = iV := Subfunctor.toRange_ι iV
  have hPre : IsPullback (W.fromPreimage f) ((W.preimage f).ι) W.ι f :=
    Subfunctor.isPullback_fromPreimage W f
  have sqQ : IsPullback (pullback.fst f iV) (pullback.snd f iV ≫ e.hom) f W.ι := by
    refine (IsPullback.of_hasPullback f iV).of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simpa using hefac.symm
  set eQ : pullback f iV ≅ (W.preimage f).toFunctor :=
    sqQ.isoIsPullback _ _ hPre.flip with heQdef
  have hEsnd : eQ.hom ≫ W.fromPreimage f = pullback.snd f iV ≫ e.hom :=
    sqQ.isoIsPullback_hom_snd _ _ hPre.flip
  have hcommsq : eQ.inv ≫ pullback.snd f iV = W.fromPreimage f ≫ e.inv := by
    have h1 : eQ.inv ≫ eQ.hom ≫ W.fromPreimage f = W.fromPreimage f := by
      rw [Iso.inv_hom_id_assoc]
    rw [hEsnd] at h1
    rw [← h1, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hsq : IsPullback eQ.inv (W.fromPreimage f) (pullback.snd f iV) e.inv :=
    IsPullback.of_horiz_isIso ⟨hcommsq⟩
  have hfinPre : IsFinite B S hS (W.fromPreimage f) :=
    isFinite_of_isPullback B S hS hsq hfinV
  have hWne : Nonempty (points B S hS W.toFunctor) :=
    ⟨pointsMap B S hS (yoneda.obj V) e.hom
      ((schemePointRepresentative B S hS V hVne.some).class B S hS (yoneda.obj V))⟩
  exact isQuasiFiniteAt_of_isFinite_fromPreimage B S hS hX hY f
    (isGenericPoint_genericPoint B S hS hY hYInt)
    (pointsMap_genericPoint_of_isDominant B S hS hX hY hXInt hYInt f hdom) W hW hWne hfinPre

/-! ### Condition (2) implies condition (3) -/

/-- **Stacks 0AD5, condition (2) implies condition (3).** If the extension of residue fields
at the generic point is finite, then `f` is finite on a pair of nonempty affine open
subspaces.

Both spaces are read on representable open charts through their generic points, which exist
by Stacks 086U and Stacks 03IE; those charts are integral schemes and the induced morphism of
schemes is dominant and locally of finite type, with the given extension of residue fields at
their generic points. Stacks 02NX then supplies a pair of nonempty affine opens of the charts
over which that morphism is finite, and an affine open of a chart is an affine open subspace
of the space. -/
theorem existsAffineOpenFiniteRestriction_of_hasFiniteResidueFieldExtensionAt
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXInt : IsIntegralSpace B S hS X) (hYInt : IsIntegralSpace B S hS Y)
    (f : X ⟶ Y) (hlft : IsLocallyOfFiniteType B S hS f) (hdom : IsDominant B S hS f)
    (h2 : HasFiniteResidueFieldExtensionAt B S hS hY hXInt.2.1 hYInt.2.1 f
      (genericPoint B S hS hX hXInt)) :
    ExistsAffineOpenFiniteRestriction B S hS f := by
  obtain ⟨CY, β, hβ, hmemY⟩ := exists_chart B S hS hY hYInt
  have hgen : pointsMap B S hS X f (genericPoint B S hS hX hXInt) =
      genericPoint B S hS hY hYInt :=
    pointsMap_genericPoint_of_isDominant B S hS hX hY hXInt hYInt f hdom
  have hmem : pointsMap B S hS X f (genericPoint B S hS hX hXInt) ∈
      Set.range (pointsMap B S hS (yoneda.obj CY) β) := by
    rw [hgen]; exact hmemY
  obtain ⟨CX, α, h, u, hα, hcomm, hu⟩ :=
    exists_openImmersion_chart_of_mem_range B S hS hX hY hXInt f CY β hβ hmem
  have huchart : chartPt B S hS CX α u = genericPoint B S hS hX hXInt := hu
  have hIX : IsIntegral ((BigFppfOver.toScheme B S hS).obj CX) :=
    isIntegral_chart B S hS hX hXInt CX α hα u huchart
  have hvchart : chartPt B S hS CY β ((BigFppfOver.toScheme B S hS).map h u) =
      genericPoint B S hS hY hYInt := by
    rw [chartPt_map B S hS f CX CY α β h hcomm u, huchart, hgen]
  have hIY : IsIntegral ((BigFppfOver.toScheme B S hS).obj CY) :=
    isIntegral_chart B S hS hY hYInt CY β hβ _ hvchart
  have hugen : u = _root_.genericPoint ((BigFppfOver.toScheme B S hS).obj CX) :=
    eq_genericPoint_of_chartPt B S hS hX hXInt CX α hα u huchart
  have hvgen : (BigFppfOver.toScheme B S hS).map h u =
      _root_.genericPoint ((BigFppfOver.toScheme B S hS).obj CY) :=
    eq_genericPoint_of_chartPt B S hS hY hYInt CY β hβ _ hvchart
  have hplft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h) :=
    hlft CX CY α β h (presheaf_etale_of_isOpenImmersion B S hS hα)
      (presheaf_etale_of_isOpenImmersion B S hS hβ) hcomm
  have hpdom : _root_.AlgebraicGeometry.IsDominant
      ((BigFppfOver.toScheme B S hS).map h) :=
    ((tfae_isDominant_of_isIntegral ((BigFppfOver.toScheme B S hS).map h)).out 2 1).mp
      (by rw [← hugen]; exact hvgen)
  obtain ⟨eX, eY, hpt⟩ := exists_ringEquiv_residueFieldHom_chart B S hS hX hY hXInt.2.1
    hYInt.2.1 f (genericPoint B S hS hX hXInt) CX CY α β hα hβ h hcomm u hu
  have hrfh : (residueFieldHom B S hS X Y hY hXInt.2.1 hYInt.2.1 f
      (genericPoint B S hS hX hXInt)).Finite := h2
  have hchart : ((((BigFppfOver.toScheme B S hS).map h).residueFieldMap u).hom).Finite := by
    have hdecomp : ((((BigFppfOver.toScheme B S hS).map h).residueFieldMap u).hom) =
        eX.toRingHom.comp
          ((residueFieldHom B S hS X Y hY hXInt.2.1 hYInt.2.1 f
            (genericPoint B S hS hX hXInt)).comp eY.symm.toRingHom) := by
      refine RingHom.ext fun a ↦ ?_
      have hpa := hpt (eY.symm a)
      simp only [RingEquiv.apply_symm_apply] at hpa
      exact hpa.symm
    rw [hdecomp]
    exact RingHom.Finite.comp (RingEquiv.finite eX)
      (RingHom.Finite.comp hrfh (RingEquiv.finite eY.symm))
  have hfd : let := (((BigFppfOver.toScheme B S hS).map h).residueFieldMap
        (_root_.genericPoint ((BigFppfOver.toScheme B S hS).obj CX))).hom.toAlgebra
      Module.Finite
        (((BigFppfOver.toScheme B S hS).obj CY).residueField
          ((BigFppfOver.toScheme B S hS).map h
            (_root_.genericPoint ((BigFppfOver.toScheme B S hS).obj CX))))
        (((BigFppfOver.toScheme B S hS).obj CX).residueField
          (_root_.genericPoint ((BigFppfOver.toScheme B S hS).obj CX))) := by
    rw [← hugen]; exact hchart
  let : Algebra ((BigFppfOver.toScheme B S hS).obj CY).functionField
      ((BigFppfOver.toScheme B S hS).obj CX).functionField :=
    (dominantFunctionFieldMap ((BigFppfOver.toScheme B S hS).map h)).toAlgebra
  have h4 : ∀ z : (BigFppfOver.toScheme B S hS).obj CX,
      (BigFppfOver.toScheme B S hS).map h z =
        _root_.genericPoint ((BigFppfOver.toScheme B S hS).obj CY) →
      z = _root_.genericPoint ((BigFppfOver.toScheme B S hS).obj CX) :=
    eq_genericPoint_of_trdeg_functionField_eq_zero ((BigFppfOver.toScheme B S hS).map h)
      (trdeg_eq_zero_iff.mpr (isAlgebraic_functionField_of_finite_residueField_genericPoint
        ((BigFppfOver.toScheme B S hS).map h) hfd))
  obtain ⟨U₀, V₀, hUV, hUne, hVne, hfinres⟩ :=
    (exists_affineOpens_isFinite_iff_eq_genericPoint
      ((BigFppfOver.toScheme B S hS).map h)).2 h4
  exact existsAffineOpenFiniteRestriction_of_chart B S hS f CX CY α β hα hβ h hcomm
    U₀ V₀ hUV hUne hVne hfinres

/-! ### Stacks 0AD5 -/

/-- **Stacks 0AD5, conditions (1)–(5).** Let `X` and `Y` be integral algebraic spaces over a
scheme `S`, let `x` and `y` be the generic points of `|X|` and `|Y|`, and let `f : X ⟶ Y` be
dominant and locally of finite type. The following are equivalent: the transcendence degree
of `x` over `y` is zero; the extension `κ(x)/κ(y)` is finite; there are nonempty affine opens
`U ⊂ X` and `V ⊂ Y` with `f(U) ⊂ V` such that `f|_U : U ⟶ V` is finite; `f` is quasi-finite
at `x`; and `x` is the only point of `|X|` mapping to `y`. -/
theorem tfae_hasTranscendenceDegreeAt_eq_zero
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXInt : IsIntegralSpace B S hS X) (hYInt : IsIntegralSpace B S hS Y)
    (f : X ⟶ Y) (hlft : IsLocallyOfFiniteType B S hS f) (hdom : IsDominant B S hS f)
    {x : points B S hS X} (hx : IsGenericPoint x (Set.univ : Set (points B S hS X)))
    {y : points B S hS Y} (hy : IsGenericPoint y (Set.univ : Set (points B S hS Y))) :
    List.TFAE
      [HasTranscendenceDegreeAt B S hS f x 0,
        HasFiniteResidueFieldExtensionAt B S hS hY hXInt.2.1 hYInt.2.1 f x,
        ExistsAffineOpenFiniteRestriction B S hS f,
        IsQuasiFiniteAt B S hS f x,
        ∀ x' : points B S hS X, pointsMap B S hS X f x' = y → x' = x] := by
  let : T0Space (points B S hS X) := t0Space_points_of_isDecentSpace B S hS hX hXInt.2.1
  let : T0Space (points B S hS Y) := t0Space_points_of_isDecentSpace B S hS hY hYInt.2.1
  obtain rfl : x = genericPoint B S hS hX hXInt :=
    hx.eq (isGenericPoint_genericPoint B S hS hX hXInt)
  obtain rfl : y = genericPoint B S hS hY hYInt :=
    hy.eq (isGenericPoint_genericPoint B S hS hY hYInt)
  tfae_have 1 → 2 := fun h ↦
    finite_residueFieldHom_genericPoint_of_hasTranscendenceDegreeAt_zero B S hS hX hY
      hXInt hYInt f hlft hdom h
  tfae_have 2 → 3 := fun h ↦
    existsAffineOpenFiniteRestriction_of_hasFiniteResidueFieldExtensionAt B S hS hX hY
      hXInt hYInt f hlft hdom h
  tfae_have 3 → 4 := fun h ↦
    isQuasiFiniteAt_genericPoint_of_existsAffineOpenFiniteRestriction B S hS hX hY hXInt f
      hlft h
  tfae_have 4 → 1 := fun h ↦ hasTranscendenceDegreeAt_zero_of_isQuasiFiniteAt B S hS hX hY f h
  tfae_have 4 ↔ 5 :=
    isQuasiFiniteAt_iff_forall_eq_of_pointsMap_eq B S hS hX hY hYInt f hlft hdom
      (isGenericPoint_genericPoint B S hS hX hXInt)
      (isGenericPoint_genericPoint B S hS hY hYInt)
  tfae_finish

/-- **Stacks 0AD5.** Let `S` be a scheme, let `X` and `Y` be integral algebraic spaces over
`S`, let `x ∈ |X|` and `y ∈ |Y|` be the generic points, and let `f : X ⟶ Y` be locally of
finite type and dominant. The following are equivalent:

1. the transcendence degree of `x/y` is `0`;
2. the extension `κ(x)/κ(y)` is finite;
3. there exist nonempty affine opens `U ⊂ X` and `V ⊂ Y` such that `f(U) ⊂ V` and
   `f|_U : U ⟶ V` is finite;
4. `f` is quasi-finite at `x`;
5. `x` is the only point of `|X|` mapping to `y`.

If `f` is separated or if `f` is quasi-compact, then these are also equivalent to

6. there exists a nonempty affine open `V ⊂ Y` such that `f^{-1}(V) ⟶ V` is finite. -/
@[stacks 0AD5]
theorem tfae_hasTranscendenceDegreeAt_eq_zero_and_isFiniteOverAffineOpen
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXInt : IsIntegralSpace B S hS X) (hYInt : IsIntegralSpace B S hS Y)
    (f : X ⟶ Y) (hlft : IsLocallyOfFiniteType B S hS f) (hdom : IsDominant B S hS f)
    {x : points B S hS X} (hx : IsGenericPoint x (Set.univ : Set (points B S hS X)))
    {y : points B S hS Y} (hy : IsGenericPoint y (Set.univ : Set (points B S hS Y))) :
    List.TFAE
        [HasTranscendenceDegreeAt B S hS f x 0,
          HasFiniteResidueFieldExtensionAt B S hS hY hXInt.2.1 hYInt.2.1 f x,
          ExistsAffineOpenFiniteRestriction B S hS f,
          IsQuasiFiniteAt B S hS f x,
          ∀ x' : points B S hS X, pointsMap B S hS X f x' = y → x' = x] ∧
      ((IsSeparated B S hS f ∨ IsQuasiCompact B S hS f) →
        List.TFAE
          [HasTranscendenceDegreeAt B S hS f x 0,
            HasFiniteResidueFieldExtensionAt B S hS hY hXInt.2.1 hYInt.2.1 f x,
            ExistsAffineOpenFiniteRestriction B S hS f,
            IsQuasiFiniteAt B S hS f x,
            (∀ x' : points B S hS X, pointsMap B S hS X f x' = y → x' = x),
            IsFiniteOverAffineOpen B S hS f]) := by
  let : T0Space (points B S hS X) := t0Space_points_of_isDecentSpace B S hS hX hXInt.2.1
  let : T0Space (points B S hS Y) := t0Space_points_of_isDecentSpace B S hS hY hYInt.2.1
  obtain rfl : x = genericPoint B S hS hX hXInt :=
    hx.eq (isGenericPoint_genericPoint B S hS hX hXInt)
  obtain rfl : y = genericPoint B S hS hY hYInt :=
    hy.eq (isGenericPoint_genericPoint B S hS hY hYInt)
  have hmain := tfae_hasTranscendenceDegreeAt_eq_zero B S hS hX hY hXInt hYInt f hlft hdom hx hy
  refine ⟨hmain, fun hsq ↦ ?_⟩
  tfae_have 1 ↔ 4 := hmain.out 1 4
  tfae_have 2 ↔ 4 := hmain.out 2 4
  tfae_have 3 ↔ 4 := hmain.out 3 4
  tfae_have 4 ↔ 5 := hmain.out 4 5
  tfae_have 5 → 6 := fun h ↦
    isFiniteOverAffineOpen_of_forall_eq_of_pointsMap_eq B S hS hX hY hXInt hYInt f hlft hdom
      hsq h
  tfae_have 6 → 4 := fun h ↦
    isQuasiFiniteAt_genericPoint_of_isFiniteOverAffineOpen B S hS hX hY hXInt hYInt f hdom h
  tfae_finish

end AlgebraicGeometry.Space

end
