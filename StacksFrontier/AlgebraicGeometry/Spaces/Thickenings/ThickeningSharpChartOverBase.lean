module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartSchemeHom
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPullbackInverseImageSection

/-!
# The chart morphism attached to a comorphism through a thickening is a morphism over the base

Let `Z ⊆ X` be a thickening of algebraic spaces over a scheme `S` with inclusion `i : Z ⟶ X`,
let `c : X ⟶ W`, and let `a : 𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` be a morphism of sheaves of rings.
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpChartSchemeHom.lean` attaches
to `a` and an **affine** étale scheme chart `V` of `W` a morphism of *schemes* `V' ⟶ V`, where
`V'` is an étale scheme chart of `X` above `X ×_W V`.  Its implementation notes record what is
missing: to be a morphism of the big fppf category over `S`, and so to give a section of `W`
over `V'`, that morphism has to commute with the structure morphisms to `S`, and that triangle
is *not* automatic — the map of regular functions of an arbitrary morphism of sheaves of rings
need not be a map over the base.

This file proves the triangle from the one algebraic condition it needs, and lifts the morphism
to the site.

**The condition.**  `AlgebraicGeometry.Space.thickeningLiftChartAppTop` depends on `a` only
through the value `a_V : 𝒪_W(V) ⟶ ((i ≫ c)_*(i^{-1}𝒪_X))(V)` of `a` over `V`
(`AlgebraicGeometry.Space.thickeningLiftChartAppTop_congr`).  So the triangle holds as soon as
`a` agrees over `V` with the comorphism `c^♯` read through the thickening *on the regular
functions read from the base*, since the chart morphism of `c^♯` is the one `c` itself induces,
`AlgebraicGeometry.Space.chartBaseChangeMap`, which is a morphism of the site and hence over
`S`.

**Why no gluing on `S` is needed.**  `S` is an arbitrary scheme, so two morphisms `V' ⟶ S` are
*not* determined by their maps of global regular functions, and comparing them directly would
need an affine-local argument on `S`.  That is avoided: the chart `V` of `W` is affine, and what
is used here is that its structure morphism to `S` *factors* through an affine scheme — for
instance through an affine open of `S` containing its image, which
`AlgebraicGeometry.exists_comp_ι_eq_of_mapsTo_isAffineOpen` produces, and which the affine
atlas of [Stacks Project, Tag 03FX] provides for the charts it constructs
(`AlgebraicGeometry.IsAlgebraicSpace.exists_affine_coproduct_atlas`).  Over an affine
factorization the comparison is `AlgebraicGeometry.ext_of_isAffine` again, at the factor rather
than at `S`.

## Main results

* `AlgebraicGeometry.comp_eq_comp_of_appTop_comp_eq_of_isAffine`: two morphisms into a scheme
  carrying a morphism to an affine scheme agree after composition with that morphism's
  composite to anywhere, as soon as their maps of regular functions agree on the functions read
  from the affine scheme.
* `AlgebraicGeometry.exists_comp_ι_eq_of_mapsTo_isAffineOpen`: a morphism of schemes whose image
  lies in an affine open of the target factors through that open.
* `AlgebraicGeometry.Space.thickeningLiftChartAppTop_congr`: the map of regular functions
  attached to `a` over `V` depends on `a` only through the value of `a` over `V`.
* `AlgebraicGeometry.Space.thickeningLiftChartHom_comp_structureHom`: **the triangle** — the
  attached morphism of charts commutes with the structure morphisms to `S`.
* `AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom`: **the attached morphism of charts
  as a morphism of the big fppf category over `S`.**
* `AlgebraicGeometry.Space.generate_isAffine_hasAffineBaseFactorization_mem_topology`: the
  charts to which that applies are cover-dense.
* `Space.exists_thickeningLiftChartSiteHom_of_eq_on_structureSharpRingInverseImage`:
  **the same with the condition in its usable form** — `a` agrees with the comorphism of `c`
  read through the thickening on the functions read from a space `W'` under `W`, the chart `V`
  being the source chart of a diagram over `W ⟶ W'` with affine target chart.
* `AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom_of_index`: the same for a solution
  of the lifting problem indexed by a morphism `e` out of the thickening with `i ≫ c = e`, which
  is the index `AlgebraicGeometry.Space.liftRestrictedSharpThroughThickening` produces.

## Implementation notes

The affine factorization of the structure morphism of the chart is taken as data — an affine
scheme `T`, a morphism `V ⟶ T` and a morphism `T ⟶ S` composing to the structure morphism —
rather than as an affine open of `S`.  That is the form in which the hypothesis on `a` can be
stated without an `eqToHom` on the preimage of the open, and
`AlgebraicGeometry.exists_comp_ι_eq_of_mapsTo_isAffineOpen` produces it from an affine open
containing the image.

The condition on `a` is stated at the *sheaf* level, as agreement of the two values over `V` on
the functions read from `T`, rather than at the level of the attached maps of regular
functions: that is the side on which a consumer has information, the difference of two
comorphisms through a thickening being a derivation which kills the functions read from the
base.

**No `@[stacks]` attribute is placed.**  As in the files this one extends, what is proved is a
comparison internal to this development of two readings of [Stacks Project, Tag 03G8].

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX), affine atlases.
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK), thickenings.
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the correspondence
  between lifts and linear maps.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this step is an
  input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry

/-! ### Comparing two morphisms through an affine factorization -/

/-- **Two morphisms into a scheme agree after composition with a morphism factoring through an
affine scheme, as soon as their maps of regular functions agree on the functions read from that
affine scheme.**  The target of the two morphisms need not be affine, and neither need the
ultimate target `Y`: all that is used is the affineness of the intermediate `T`, where
`AlgebraicGeometry.ext_of_isAffine` applies. -/
theorem comp_eq_comp_of_appTop_comp_eq_of_isAffine {V' V T Y : Scheme.{u}} [IsAffine T]
    (p : V ⟶ T) (t : T ⟶ Y) {ψ χ : V' ⟶ V}
    (h : p.appTop ≫ ψ.appTop = p.appTop ≫ χ.appTop) :
    ψ ≫ p ≫ t = χ ≫ p ≫ t := by
  have hp : ψ ≫ p = χ ≫ p :=
    ext_of_isAffine
      ((Scheme.Hom.comp_appTop ψ p).trans (h.trans (Scheme.Hom.comp_appTop χ p).symm))
  rw [← Category.assoc, ← Category.assoc, hp]

/-- **A morphism of schemes whose image lies in an affine open of the target factors through
that open**, the factorization being a morphism into an affine scheme. -/
theorem exists_comp_ι_eq_of_mapsTo_isAffineOpen {V Y : Scheme.{u}} (p : V ⟶ Y) (U : Y.Opens)
    (hran : ∀ x : V, p.base x ∈ U) :
    ∃ q : V ⟶ U.toScheme, q ≫ U.ι = p :=
  ⟨IsOpenImmersion.lift U.ι p
      (by rw [Scheme.Opens.range_ι]; exact Set.range_subset_iff.2 hran),
    IsOpenImmersion.lift_fac _ _ _⟩

/-- A morphism of the big fppf category over `S` commutes, on underlying schemes, with the
structure morphisms to `S`: that is its own defining triangle, read through the inclusion of
the site into schemes. -/
theorem BigFppfOver.toScheme_map_comp_inclusion_map_structureHom (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {A C : BigFppfOver B S hS} (g : A ⟶ C) :
    (BigFppfOver.toScheme B S hS).map g ≫ B.inclusion.map C.hom = B.inclusion.map A.hom :=
  (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w g))

namespace Space

/-! ### The charts carrying an affine factorization of their structure morphism cover -/

/-- **The affine étale charts whose structure morphism factors through an affine scheme generate
a covering sieve of any étale chart.**  Through every point of a chart there is an affine open of
it mapping into an affine open of `S`, by
`AlgebraicGeometry.Scheme.exists_affineOpen_le_preimage_affineOpen`; an affine open of a chart is
an affine chart over it, `AlgebraicGeometry.Space.openChart`; and the structure morphism of such
a chart factors through the affine open of `S`.

So the hypothesis of `AlgebraicGeometry.Space.thickeningLiftChartHom_comp_structureHom` — an
affine factorization of the structure morphism of the chart — is available on a covering family,
which is what a gluing argument over the charts of a space needs. -/
theorem generate_isAffine_hasAffineBaseFactorization_mem_topology
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (A : SmallEtale B S hS F) :
    Sieve.generate (fun (C : SmallEtale B S hS F) (_ : C ⟶ A) ↦
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj C)) ∧
        ∃ (T : Scheme.{u}) (_ : IsAffine T)
          (p : (BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS F).obj C) ⟶ T) (t : T ⟶ S),
          p ≫ t = B.inclusion.map ((SmallEtale.toOver B S hS F).obj C).hom) ∈
      SmallEtale.topology B S hS F A := by
  refine smallEtale_sieve_of_pointwise_covering B S hS F A _ fun z ↦ ?_
  obtain ⟨O, N, hzO, hON⟩ :=
    Scheme.exists_affineOpen_le_preimage_affineOpen
      (B.inclusion.map ((SmallEtale.toOver B S hS F).obj A).hom) z
  have hstr : (BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (openChartInclusion B S hS F A O.1)) ≫
      B.inclusion.map ((SmallEtale.toOver B S hS F).obj A).hom =
        B.inclusion.map
          ((SmallEtale.toOver B S hS F).obj (openChart B S hS F A O.1)).hom :=
    BigFppfOver.toScheme_map_comp_inclusion_map_structureHom B S hS
      ((SmallEtale.toOver B S hS F).map (openChartInclusion B S hS F A O.1))
  have hfac : (B.inclusion.map ((SmallEtale.toOver B S hS F).obj A).hom).resLE N.1 O.1 hON ≫
      N.1.ι =
        B.inclusion.map
          ((SmallEtale.toOver B S hS F).obj (openChart B S hS F A O.1)).hom :=
    (Scheme.Hom.resLE_comp_ι _ hON).trans
      ((congrArg (fun m ↦ m ≫ B.inclusion.map ((SmallEtale.toOver B S hS F).obj A).hom)
        (toScheme_map_toOver_map_openChartInclusion B S hS F A O.1)).symm.trans hstr)
  refine ⟨openChart B S hS F A O.1, openChartInclusion B S hS F A O.1,
    ⟨openChart B S hS F A O.1, 𝟙 _, openChartInclusion B S hS F A O.1,
      ⟨O.2, N.1.toScheme, N.2, _, N.1.ι, hfac⟩, Category.id_comp _⟩, ⟨z, hzO⟩, ?_⟩
  rw [toScheme_map_toOver_map_openChartInclusion]
  rfl

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-! ### The map of regular functions depends only on the value of the comorphism over the chart -/

/-- **The map of regular functions attached to `a` over a chart depends on `a` only through the
value of `a` over that chart.**  By construction
`AlgebraicGeometry.Space.thickeningLiftChartAppTop` is the value of `a` over `V`, read on the
chart and brought back along the unit of the thickening; so two morphisms agreeing over `V` at
a regular function agree there on the attached map. -/
theorem thickeningLiftChartAppTop_congr (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a a' : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    (b : ToType ((structureRingSheaf B S hS W).obj.obj (op V)))
    (h : a.hom.app (op V) b = a'.hom.app (op V) b) :
    thickeningLiftChartAppTop B S hS Z hZ c a V j b =
      thickeningLiftChartAppTop B S hS Z hZ c a' V j b :=
  congrArg
    (fun z : ToType ((thickeningLiftRingSheaf B S hS Z c).obj.obj (op V)) ↦
      (thickeningRingUnitChartRingEquiv B S hS Z hZ j.right).symm
        ((thickeningLiftChartRingHom B S hS Z c V j).hom z))
    h

/-! ### The triangle over the base -/

/-- The morphism of charts induced by `c` acts on regular functions as the chartwise pullback,
by the definition of `AlgebraicGeometry.Space.chartPullbackRingHom`. -/
theorem toScheme_map_chartBaseChangeMap_appTop (c : X ⟶ W) (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    (b : ToType ((structureRingSheaf B S hS W).obj.obj (op V))) :
    ((BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS c V j)).appTop b =
      chartPullbackRingHom B S hS c V j b := rfl

/-- **The triangle over the base.**  The morphism of charts attached to `a` over an affine
chart `V` of `W` commutes with the structure morphisms to `S`, as soon as the structure
morphism of `V` factors through an affine scheme `T` and `a` agrees over `V` with the
comorphism of `c` read through the thickening on the regular functions read from `T`.

The comparison is made at `T`, where `AlgebraicGeometry.ext_of_isAffine` applies: the
competitor is the morphism of charts `c` itself induces, which is a morphism of the site and so
already over `S`. -/
theorem thickeningLiftChartHom_comp_structureHom
    (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
    {T : Scheme.{u}} [IsAffine T]
    (p : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V) ⟶ T)
    (t : T ⟶ S)
    (hpt : p ≫ t = B.inclusion.map ((SmallEtale.toOver B S hS W.1).obj V).hom)
    (hbase : ∀ y : Γ(T, (⊤ : T.Opens)),
      a.hom.app (op V) (p.appTop y) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op V) (p.appTop y)) :
    thickeningLiftChartHom B S hS Z hZ c a V j ≫
        B.inclusion.map ((SmallEtale.toOver B S hS W.1).obj V).hom =
      B.inclusion.map ((SmallEtale.toOver B S hS X.1).obj j.right.unop).hom := by
  have happ : p.appTop ≫ (thickeningLiftChartHom B S hS Z hZ c a V j).appTop =
      p.appTop ≫
        ((BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS c V j)).appTop := by
    refine CommRingCat.hom_ext (RingHom.ext fun y ↦ ?_)
    refine ((congrArg (fun φ ↦ φ (p.appTop y))
      (thickeningLiftChartHom_appTop B S hS Z hZ c a V j)).trans ?_).trans
      (toScheme_map_chartBaseChangeMap_appTop B S hS c V j (p.appTop y)).symm
    refine (thickeningLiftChartAppTop_congr B S hS Z hZ c a
      (structureSharpThroughThickening B S hS Z c) V j (p.appTop y) (hbase y)).trans ?_
    exact congrArg (fun φ : ToType ((structureRingSheaf B S hS W).obj.obj (op V)) →+*
        ToType ((structureRingSheaf B S hS X).obj.obj j.right) ↦ φ (p.appTop y))
      (thickeningLiftChartAppTop_structureSharpThroughThickening B S hS Z hZ c V j)
  have hcomp := comp_eq_comp_of_appTop_comp_eq_of_isAffine p t happ
  rw [hpt] at hcomp
  exact hcomp.trans
    (BigFppfOver.toScheme_map_comp_inclusion_map_structureHom B S hS
      (chartBaseChangeMap B S hS c V j))

/-- **The morphism of charts attached to `a` as a morphism of the big fppf category over
`S`.**  With the triangle over the base proved, the fullness of the functor to schemes on the
morphisms over `S`, `AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq`, lifts the morphism
of charts to the site; composed with the chart `V ⟶ W` it is then a section of `W` over `V'`. -/
theorem exists_thickeningLiftChartSiteHom
    (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
    {T : Scheme.{u}} [IsAffine T]
    (p : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V) ⟶ T)
    (t : T ⟶ S)
    (hpt : p ≫ t = B.inclusion.map ((SmallEtale.toOver B S hS W.1).obj V).hom)
    (hbase : ∀ y : Γ(T, (⊤ : T.Opens)),
      a.hom.app (op V) (p.appTop y) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op V) (p.appTop y)) :
    ∃ ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
        (SmallEtale.toOver B S hS W.1).obj V,
      (BigFppfOver.toScheme B S hS).map ψ = thickeningLiftChartHom B S hS Z hZ c a V j :=
  BigFppfOver.exists_hom_of_comp_eq B S hS _
    (thickeningLiftChartHom_comp_structureHom B S hS Z hZ c a V j p t hpt hbase)

/-! ### The triangle from agreement on the functions read from another space -/

/-- **The triangle, with the affine factorization read off a chart diagram.**  If the chart `V`
of `W` is the source chart of a diagram over a morphism `r : W ⟶ W'` whose target chart `V'` is
affine, then the structure morphism of `V` factors through the affine scheme `V'`, and the
condition on `a` is agreement with the comorphism of `c` read through the thickening on the
regular functions pulled back from `V'`. -/
theorem exists_thickeningLiftChartSiteHom_of_chartDiagram
    (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    {W' : AlgebraicSpaces B S hS} (r : W ⟶ W') (V' : SmallEtale B S hS W'.1)
    (m : StructuredArrow (op (chartBaseChange B S hS r V'))
      (comparisonFunctor B S hS W).op)
    (j : StructuredArrow (op (chartBaseChange B S hS c m.right.unop))
      (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS W.1).obj m.right.unop))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W'.1).obj V'))]
    (hbase : ∀ y : ToType ((structureRingSheaf B S hS W').obj.obj (op V')),
      a.hom.app (op m.right.unop) (chartPullbackRingHom B S hS r V' m y) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op m.right.unop)
          (chartPullbackRingHom B S hS r V' m y)) :
    ∃ ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
        (SmallEtale.toOver B S hS W.1).obj m.right.unop,
      (BigFppfOver.toScheme B S hS).map ψ =
        thickeningLiftChartHom B S hS Z hZ c a m.right.unop j :=
  exists_thickeningLiftChartSiteHom B S hS Z hZ c a m.right.unop j
    ((BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS r V' m))
    (B.inclusion.map ((SmallEtale.toOver B S hS W'.1).obj V').hom)
    (BigFppfOver.toScheme_map_comp_inclusion_map_structureHom B S hS
      (chartBaseChangeMap B S hS r V' m))
    hbase

/-- **The triangle from agreement on the functions read from another space.**  If `a` agrees
over the chart `V` with the comorphism of `c` read through the thickening on every value of the
inverse-image sharp `r^♯ : r^{-1}𝒪_{W'} ⟶ 𝒪_W` — which is what it means for the two to differ
by a map annihilating the functions read from `W'` — then the morphism of charts attached to `a`
is a morphism of the big fppf category over `S`.

The chart diagram supplies the affine factorization of the structure morphism of `V` *and*
exhibits each regular function pulled back from its target chart as a value of `r^♯`, by
`AlgebraicGeometry.Space.structureSharpRingInverseImage_chartPullbackInverseImageSection`. -/
theorem exists_thickeningLiftChartSiteHom_of_eq_on_structureSharpRingInverseImage
    (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    {W' : AlgebraicSpaces B S hS} (r : W ⟶ W') (V' : SmallEtale B S hS W'.1)
    (m : StructuredArrow (op (chartBaseChange B S hS r V'))
      (comparisonFunctor B S hS W).op)
    (j : StructuredArrow (op (chartBaseChange B S hS c m.right.unop))
      (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS W.1).obj m.right.unop))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W'.1).obj V'))]
    (hbase : ∀ s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj
        (op m.right.unop)),
      a.hom.app (op m.right.unop)
          ((structureSharpRingInverseImage B S hS r).hom.app (op m.right.unop) s) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op m.right.unop)
          ((structureSharpRingInverseImage B S hS r).hom.app (op m.right.unop) s)) :
    ∃ ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
        (SmallEtale.toOver B S hS W.1).obj m.right.unop,
      (BigFppfOver.toScheme B S hS).map ψ =
        thickeningLiftChartHom B S hS Z hZ c a m.right.unop j :=
  exists_thickeningLiftChartSiteHom_of_chartDiagram B S hS Z hZ c a r V' m j
    fun y ↦ by
      obtain ⟨s, hs⟩ :=
        exists_app_structureSharpRingInverseImage_eq_chartPullbackRingHom B S hS r V' m y
      rw [← hs]
      exact hbase s


/-! ### The index given by an equation -/

/-- **A morphism into the direct image along an `e` with `i ≫ c = e`, read at the index
`i ≫ c`.**  The target of `AlgebraicGeometry.Space.structureSharpThroughThickening` is indexed
by the composite `i ≫ c` on the nose, while a solution of the lifting problem arrives indexed by
the morphism `e` out of the thickening through which every competitor factors — the two sheaves
are equal, and this is the transport. -/
noncomputable def thickeningLiftOfIndex (c : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e)
    (a : structureRingSheaf B S hS W ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
        (smallToposMorphismTypeU B S hS e).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))) :
    structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c :=
  a ≫ eqToHom (congrArg (fun m : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W ↦
    pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
      (smallToposMorphismTypeU B S hS m).pushforward
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))) h.symm)

/-- **The transport carries the comorphism read at the index `e` to the comorphism read at the
composite**, the two being the same morphism read in two spellings of one sheaf. -/
theorem thickeningLiftOfIndex_structureSharpThroughThickeningAt (c : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e) :
    thickeningLiftOfIndex B S hS Z c e h
        (structureSharpThroughThickeningAt B S hS Z c e h) =
      structureSharpThroughThickening B S hS Z c := by
  subst h
  simp only [thickeningLiftOfIndex, structureSharpThroughThickeningAt, eqToHom_refl,
    Category.comp_id]

/-- The transport is injective on the value over a chart at a regular function: it composes with
an isomorphism of sheaves. -/
theorem app_thickeningLiftOfIndex_congr (c : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e)
    (a a' : structureRingSheaf B S hS W ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
        (smallToposMorphismTypeU B S hS e).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
    (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (b : ToType ((structureRingSheaf B S hS W).obj.obj V))
    (hb : a.hom.app V b = a'.hom.app V b) :
    (thickeningLiftOfIndex B S hS Z c e h a).hom.app V b =
      (thickeningLiftOfIndex B S hS Z c e h a').hom.app V b := by
  subst h
  simp only [thickeningLiftOfIndex, eqToHom_refl, Category.comp_id]
  exact hb

/-- **The attached morphism of charts as a morphism of the site, for a solution of the lifting
problem read at the index `e`.**  This is
`AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom_of_eq_on_structureSharpRingInverseImage`
with the index transported, so that it applies directly to
`AlgebraicGeometry.Space.liftRestrictedSharpThroughThickening`, whose target is indexed by the
morphism out of the thickening rather than by the composite. -/
theorem exists_thickeningLiftChartSiteHom_of_index
    (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e)
    (a : structureRingSheaf B S hS W ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
        (smallToposMorphismTypeU B S hS e).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
    {W' : AlgebraicSpaces B S hS} (r : W ⟶ W') (V' : SmallEtale B S hS W'.1)
    (m : StructuredArrow (op (chartBaseChange B S hS r V'))
      (comparisonFunctor B S hS W).op)
    (j : StructuredArrow (op (chartBaseChange B S hS c m.right.unop))
      (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS W.1).obj m.right.unop))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W'.1).obj V'))]
    (hbase : ∀ s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj
        (op m.right.unop)),
      a.hom.app (op m.right.unop)
          ((structureSharpRingInverseImage B S hS r).hom.app (op m.right.unop) s) =
        (structureSharpThroughThickeningAt B S hS Z c e h).hom.app (op m.right.unop)
          ((structureSharpRingInverseImage B S hS r).hom.app (op m.right.unop) s)) :
    ∃ ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
        (SmallEtale.toOver B S hS W.1).obj m.right.unop,
      (BigFppfOver.toScheme B S hS).map ψ =
        thickeningLiftChartHom B S hS Z hZ c (thickeningLiftOfIndex B S hS Z c e h a)
          m.right.unop j :=
  exists_thickeningLiftChartSiteHom_of_eq_on_structureSharpRingInverseImage B S hS Z hZ c
    (thickeningLiftOfIndex B S hS Z c e h a) r V' m j
    fun s ↦ (app_thickeningLiftOfIndex_congr B S hS Z c e h a
        (structureSharpThroughThickeningAt B S hS Z c e h) (op m.right.unop) _ (hbase s)).trans
      (congrArg (fun n : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c ↦
          n.hom.app (op m.right.unop)
            ((structureSharpRingInverseImage B S hS r).hom.app (op m.right.unop) s))
        (thickeningLiftOfIndex_structureSharpThroughThickeningAt B S hS Z c e h))


end Space

end AlgebraicGeometry

end
