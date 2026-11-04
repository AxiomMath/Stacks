module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.ComponentMultiplicity
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.ConstancyOfDimension
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.LocalDimensionComponents
public import StacksFrontier.AlgebraicGeometry.Stacks.Dimension
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionAtFiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.JacobsonAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.PseudoCatenaryAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionLocalConstancyStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace

/-!
# Constancy of the dimension of an algebraic stack with irreducible space of points

**Stacks 0DRX** says that on a Jacobson, pseudo-catenary, locally Noetherian algebraic stack `𝒳`
over `S` with `|𝒳|` irreducible the function `x ↦ dim_x(𝒳)` of Stacks 0AFN is constant. That is
proved here, from the dimension formula of Stacks 0DRJ along the universally catenary scheme chart
that pseudo-catenarity provides, the local constancy of the relative dimension in that formula
(Stacks 0DRQ (2)) and Stacks 0DRT at the irreducible components of the chart.

## Main results

* `AlgebraicGeometry.Stack.isConstant_dimensionAtPoint_of_irreducibleSpace`: **Stacks 0DRX**.
* `AlgebraicGeometry.Stack.isConstant_dimensionAtPoint`: the same conclusion from a smooth
  surjective scheme chart along which the dimension formula of Stacks 0DRJ holds and both of its
  terms are locally constant — the form of the argument that needs no hypothesis on `𝒳` beyond
  irreducibility of `|𝒳|`.
* `AlgebraicGeometry.Stack.isLocallyConstant_of_isLocallyConstant_comp`: a function is locally
  constant as soon as its composite with some surjective open map is.
* `AlgebraicGeometry.Stack.isLocallyConstant_topologicalKrullDimAt_of_irreducibleSpace`: the local
  dimension of an irreducible Jacobson catenary locally Noetherian scheme of finite dimension is
  locally constant, by Stacks 0DRT.
* `AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionAtPoint_of_irreducible_chart`: the
  dimension of Stacks 0AFN is the same at every point of a Jacobson, pseudo-catenary, locally
  Noetherian algebraic stack admitting an irreducible smooth chart of finite dimension, given the
  dimension formula of Stacks 0DRJ and the local constancy of Stacks 0DRQ (2). This is the case
  of **Stacks 0DRX** in which the comparison of the irreducible components of the chart is
  vacuous; the unconditional statement above covers it.
* `AlgebraicGeometry.Stack.continuous_pointsEquivScheme_symm`: the comparison of Stacks 03BV from
  the points of a scheme to the points of its represented presheaf is continuous.

## Implementation notes

The chart is a scheme `U` of the site read as an algebraic stack through
`AlgebraicGeometry.Stack.schemeStack`, so that its map on points is
`AlgebraicGeometry.Stack.AlgebraicStacks.chartPointMap`, a map out of the topological space of the
scheme itself, which is open by Stacks 06R7 — a smooth 1-morphism being flat and locally of finite
presentation — and surjective. Stacks 0DRJ speaks instead of a chart by an *algebraic space*, and
the two are compared by
`AlgebraicGeometry.Stack.exists_isSmooth_algebraicSpaceStack_hom_chartPointMap_eq`: the algebraic
space `U` represents has the same algebraic stack up to a smooth surjective 1-morphism, and the
two charts then induce the same map on points.

Where the source's proof shows that `u ↦ dim_u(U)` is locally constant on the chart, the proof
here does something weaker that suffices. The source computes `dim_u(U)` as the maximum of
`dim_u(T_i)` over the irreducible components of the chart through `u` and compares those
components with each other. What is used here instead is that, by
`AlgebraicGeometry.exists_isOpen_isIrreducible_topologicalKrullDimAt_eq`, each point `u` has a
nonempty open *irreducible* `V ⊆ U` with `u ∈ closure V` along which `dim_u(U)` is constantly the
dimension of `V`: the relative dimension is then constant on `closure V`, that set being
irreducible and hence connected, so the formula of Stacks 0DRJ gives `dim_x(𝒳)` the same value at
the image of `u` and on the image of `V`. The images of two such open sets are nonempty open
subsets of the irreducible `|𝒳|`, so they meet, and a common point identifies the two values.
Local constancy of `dim_x(𝒳)` on `|𝒳|` is never asserted.

The hypotheses on the chart are discharged as follows. Pseudo-catenarity (Stacks 0DRU) *is* the
existence of a smooth surjective scheme chart that is locally Noetherian and universally catenary,
so catenarity of the chart is `AlgebraicGeometry.Scheme.IsUniversallyCatenary.isCatenarySpace` at
its identity. The Jacobson condition passes from the stack to that chart by the universal scheme
criterion of Stacks 04YF, being local in the smooth topology. No finiteness of the dimension of
the chart is needed, because `AlgebraicGeometry.topologicalKrullDim_isOpen_eq_of_catenary` is the
form of Stacks 0DRT that does without it.

`h0DRJ` in `AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionAtPoint_of_irreducible_chart` is
**Stacks 0DRJ**, `dim_x(𝒳) = dim_u(U) - dim_u(U_x)` along a smooth 1-morphism from an algebraic
space, together with the finiteness of the relative dimension it asserts. Its formula is
`AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_of_isSmooth`, which needs that
finiteness as an input; by itself the dimension of Stacks 0AFN is an infimum over smooth charts,
so a chart gives only the inequality `AlgebraicGeometry.Stack.dimensionAtPoint_le`. The
subtraction is `AlgebraicGeometry.Stack.dimensionSubNat`, as in Stacks 0AFN itself, because the
values lie in `EInt` and that has no total subtraction. Its other hypothesis `h0DRQ` is
**Stacks 0DRQ (2)**, the local constancy of `u ↦ dim_u(U_x)`, which that statement of the library
keeps as it stands; `AlgebraicGeometry.Stack.isConstant_dimensionAtPoint_of_irreducibleSpace`
assumes neither, taking Stacks 0DRQ (2) for a stack target from
`AlgebraicGeometry.Stack.isLocallyConstant_relativeDimensionAt_of_isSmooth_of_stack`, which the
smoothness of the chart supplies.

## References

* [Stacks Project, Tag 03BV](https://stacks.math.columbia.edu/tag/03BV)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
* [Stacks Project, Tag 0AFM](https://stacks.math.columbia.edu/tag/0AFM)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
* [Stacks Project, Tag 0DRQ](https://stacks.math.columbia.edu/tag/0DRQ)
* [Stacks Project, Tag 0DRT](https://stacks.math.columbia.edu/tag/0DRT)
* [Stacks Project, Tag 0DRU](https://stacks.math.columbia.edu/tag/0DRU)
* [Stacks Project, Tag 0DRX](https://stacks.math.columbia.edu/tag/0DRX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopology

/-- The comparison bijection of Stacks 03BV from the points of a scheme to the points of its
represented presheaf is continuous for the point topology of Stacks 03BU: the preimage of a set
of points is its image under the comparison the other way, which is open exactly when the set
is. -/
theorem continuous_pointsEquivScheme_symm (U : BigFppfOver B S hS) :
    Continuous (Space.pointsEquivScheme B S hS U).symm := by
  refine continuous_def.2 fun W hW => ?_
  rw [← Equiv.image_eq_preimage_symm]
  exact (Space.isOpen_pointTopology_yoneda_iff_isOpen_image B S hS U W).1 hW

/-- A locally constant function takes the same value at any two points of an irreducible set. -/
private theorem apply_eq_of_isIrreducible {α γ : Type*} [TopologicalSpace α] {g : α → γ}
    (hg : IsLocallyConstant g) {s : Set α} (hs : IsIrreducible s) {a b : α} (ha : a ∈ s)
    (hb : b ∈ s) : g a = g b :=
  hg.apply_eq_of_isPreconnected hs.isPreirreducible.isPreconnected ha hb

/-- A smooth-local property of schemes that holds for the algebraic stack `𝒳` holds for the scheme
underlying any smooth chart of `𝒳` by an algebraic space represented by `U`. -/
private theorem property_of_isSmooth_of_algebraicSpaceStack (P : ObjectProperty Scheme.{u})
    [ObjectProperty.IsLocal P (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}))]
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS P 𝒳)
    (U : BigFppfOver B S hS)
    (a : algebraicSpaceStack.{u, w} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) ⟶ 𝒳)
    (hasm : AlgebraicStacks.IsSmooth B S hS a) : P ((BigFppfOver.toScheme B S hS).obj U) :=
  (Space.exists_atlas_iff_of_representable B S hS (yoneda.obj U) P U (Iso.refl _)).mp
    ((exists_space_atlas_iff_forall_space.{u, w} B S hS P 𝒳).mp
      ((exists_scheme_atlas_iff_exists_space_atlas.{u, w} B S hS P 𝒳).mp h𝒳)
      (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) a hasm)

/-- On a Jacobson, pseudo-catenary, locally Noetherian algebraic stack carrying a smooth chart
whose underlying scheme is irreducible, catenary and of finite dimension, the dimension of
Stacks 0AFN is the same at every point, given the dimension formula of Stacks 0DRJ and the local
constancy of Stacks 0DRQ (2) as the hypotheses `h0DRJ` and `h0DRQ`.

The chart's local dimension is constant by Stacks 0DRT, and its relative dimension is constant
because a locally constant function on the connected space of points of an irreducible scheme is
constant; Stacks 0DRJ turns the two into the constancy of `dim_x(𝒳)` on the image of the chart,
which is all of `|𝒳|`. The chart is Jacobson and locally Noetherian by the criteria of
Stacks 04YF, both properties being local in the smooth topology.

This is **not** Stacks 0DRX: with an irreducible chart the comparison of the irreducible
components of the chart, which is the content of the source's proof, is vacuous. -/
theorem dimensionAtPoint_eq_dimensionAtPoint_of_irreducible_chart
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (_h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (_h𝒳Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒳.val))
    (U : BigFppfOver B S hS)
    (a : algebraicSpaceStack.{u, w} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) ⟶ 𝒳)
    (hasm : AlgebraicStacks.IsSmooth B S hS a)
    (ha : AlgebraicStacks.IsLocallyOfFiniteType B S hS a)
    (hsurj : ∀ x : points B S hS 𝒳.val.val 𝒳.val.property,
      ∃ q : Space.points B S hS (yoneda.obj U),
        pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
          (fibredCategory B S hS (yoneda.obj U)).property 𝒳.val.property a.hom.hom
          (stackPointOfSpacePoint B S hS (yoneda.obj U) q) = x)
    (hUirreducible : IrreducibleSpace ((BigFppfOver.toScheme B S hS).obj U))
    (hUcatenary : IrreducibleClosedsCodim.IsCatenarySpace
      ((BigFppfOver.toScheme B S hS).obj U))
    (d : ℕ)
    (hUdim : topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) = d)
    (h0DRJ : ∀ q : Space.points B S hS (yoneda.obj U), ∃ m : ℕ,
      relativeDimensionAt.{u, w} B S hS (yoneda.obj U)
            (isAlgebraicSpace_yoneda B S hS U) 𝒳 a ha q = (m : WithBot ℕ∞) ∧
        dimensionAtPoint B S hS 𝒳 h𝒳
            (pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
              (fibredCategory B S hS (yoneda.obj U)).property 𝒳.val.property a.hom.hom
              (stackPointOfSpacePoint B S hS (yoneda.obj U) q)) =
          dimensionSubNat (Space.dimensionAtPoint B S hS (yoneda.obj U)
            (isAlgebraicSpace_yoneda B S hS U) q) m)
    (h0DRQ : IsLocallyConstant
      (relativeDimensionAt.{u, w} B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U) 𝒳 a ha)) :
    ∀ x y : points B S hS 𝒳.val.val 𝒳.val.property,
      dimensionAtPoint B S hS 𝒳 h𝒳 x = dimensionAtPoint B S hS 𝒳 h𝒳 y := by
  classical
  have _ := hUirreducible
  -- The chart is Jacobson by the criteria of Stacks 04YF, that property being smooth-local.
  have hUjacobson : JacobsonSpace ((BigFppfOver.toScheme B S hS).obj U) :=
    property_of_isSmooth_of_algebraicSpaceStack B S hS (fun X : Scheme.{u} => JacobsonSpace X)
      𝒳 h𝒳Jacobson U a hasm
  have _ := hUjacobson
  -- And locally Noetherian, for the same reason.
  have hUnoetherian : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
    have _ : ObjectProperty.IsLocal (fun X : Scheme.{u} => IsLocallyNoetherian X)
        (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
      ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
    property_of_isSmooth_of_algebraicSpaceStack B S hS
      (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳 h𝒳 U a hasm
  have _ := hUnoetherian
  have hid : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (𝟙 (yoneda.obj U)) :=
    Space.presheaf_etale_of_iso B S hS (Iso.refl (yoneda.obj U))
  have hat : ∀ q : Space.points B S hS (yoneda.obj U),
      Space.dimensionAtPoint B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) q =
        topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U)
          (Space.pointsToScheme B S hS U q) := by
    refine Quot.ind fun p => ?_
    exact Space.dimensionAtPoint_eq_of_etale_chart B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) _ U (𝟙 _) hid p
      (by rw [Space.pointsMap_id]; rfl)
  have hUconst : ∀ q q' : Space.points B S hS (yoneda.obj U),
      Space.dimensionAtPoint B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) q =
        Space.dimensionAtPoint B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) q' := by
    intro q q'
    rw [hat q, hat q']
    exact isConstant_topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U) hUcatenary d
      hUdim _ _
  have hrconst : ∀ q q' : Space.points B S hS (yoneda.obj U),
      relativeDimensionAt.{u, w} B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U) 𝒳 a ha q =
        relativeDimensionAt.{u, w} B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U) 𝒳 a ha q' := by
    intro q q'
    have hLC := h0DRQ.comp_continuous (continuous_pointsEquivScheme_symm B S hS U)
    have hq : (Space.pointsEquivScheme B S hS U).symm (Space.pointsToScheme B S hS U q) = q :=
      (Space.pointsEquivScheme B S hS U).symm_apply_apply q
    have hq' : (Space.pointsEquivScheme B S hS U).symm (Space.pointsToScheme B S hS U q') = q' :=
      (Space.pointsEquivScheme B S hS U).symm_apply_apply q'
    rw [← hq, ← hq']
    exact apply_eq_of_isIrreducible hLC (IrreducibleSpace.isIrreducible_univ _) trivial trivial
  intro x y
  obtain ⟨q, hq⟩ := hsurj x
  obtain ⟨q', hq'⟩ := hsurj y
  obtain ⟨m, hm, hxm⟩ := h0DRJ q
  obtain ⟨m', hm', hym'⟩ := h0DRJ q'
  have hmm : m = m' := by
    have hr := hrconst q q'
    rw [hm, hm'] at hr
    exact_mod_cast hr
  rw [← hq, ← hq', hxm, hym', hUconst q q', hmm]

/-- A function on a topological space is locally constant as soon as its composite with some
surjective open map onto that space is: the image of an open set on which the composite is
constant is an open set on which the function is constant. -/
theorem isLocallyConstant_of_isLocallyConstant_comp {α β γ : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {φ : α → β} (hopen : IsOpenMap φ) (hsurj : Function.Surjective φ)
    {g : β → γ} (h : IsLocallyConstant (g ∘ φ)) : IsLocallyConstant g := by
  rw [IsLocallyConstant.iff_exists_open] at h ⊢
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨W, hWopen, hxW, hWconst⟩ := h x
  refine ⟨φ '' W, hopen W hWopen, ⟨x, hxW, rfl⟩, ?_⟩
  rintro _ ⟨x', hx', rfl⟩
  exact hWconst x' hx'

/-- The local dimension of an irreducible, Jacobson, catenary, locally Noetherian scheme of finite
dimension is locally constant, being constant by Stacks 0DRT. -/
theorem isLocallyConstant_topologicalKrullDimAt_of_irreducibleSpace (X : Scheme.{u})
    [IrreducibleSpace X] [JacobsonSpace X]
    (hcat : IrreducibleClosedsCodim.IsCatenarySpace X) [IsLocallyNoetherian X]
    (d : ℕ) (hX : topologicalKrullDim X = d) :
    IsLocallyConstant fun x : X => topologicalKrullDimAt X x :=
  (IsLocallyConstant.iff_exists_open _).2 fun x =>
    ⟨Set.univ, isOpen_univ, Set.mem_univ x, fun y _ =>
      isConstant_topologicalKrullDimAt X hcat d hX y x⟩

/-- The dimension of Stacks 0AFN of an algebraic stack `𝒳` over `S` with `|𝒳|` irreducible is the
same at every point of `|𝒳|` as soon as some smooth surjective chart by a scheme `U` of the site
carries the dimension formula of Stacks 0DRJ with relative dimension `r` and has both `r` and its
own local dimension locally constant.

The formula exhibits `dim_x(𝒳)` at the image of `u ∈ U` as the difference of two locally constant
functions of `u`, hence as a locally constant function of `u`. A smooth 1-morphism is open on
points (Stacks 06R7), so the dimension is locally constant on `|𝒳|` itself, which is connected
because it is irreducible.

This is the form of the argument that reads the local dimension of the chart off the chart itself.
It is not how **Stacks 0DRX** is obtained in
`AlgebraicGeometry.Stack.isConstant_dimensionAtPoint_of_irreducibleSpace`, where no such global
local constancy is available: there the local dimension of the chart is only compared with the
dimension of one open irreducible subset at a time. -/
theorem isConstant_dimensionAtPoint (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (_h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (_h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒳Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒳.val))
    (U : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hsm : AlgebraicStacks.IsSmooth B S hS f) (hsurj : IsSurjective B S hS f)
    (r : (BigFppfOver.toScheme B S hS).obj U → ℕ) (hr : IsLocallyConstant r)
    (hdim : IsLocallyConstant fun u : (BigFppfOver.toScheme B S hS).obj U =>
      topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U) u)
    (hformula : ∀ u : (BigFppfOver.toScheme B S hS).obj U,
      dimensionAtPoint B S hS 𝒳 h𝒳 (AlgebraicStacks.chartPointMap B S hS U 𝒳 f u) =
        dimensionSubNat
          (topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U) u) (r u)) :
    ∀ x y : points B S hS 𝒳.val.val 𝒳.val.property,
      dimensionAtPoint B S hS 𝒳 h𝒳 x = dimensionAtPoint B S hS 𝒳 h𝒳 y := by
  let _ := pointTopology B S hS 𝒳.val
  have _ := h𝒳Irreducible
  have hcomp : IsLocallyConstant
      (dimensionAtPoint B S hS 𝒳 h𝒳 ∘ AlgebraicStacks.chartPointMap B S hS U 𝒳 f) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro u
    obtain ⟨W₁, hW₁, hu₁, hc₁⟩ := (IsLocallyConstant.iff_exists_open _).1 hdim u
    obtain ⟨W₂, hW₂, hu₂, hc₂⟩ := (IsLocallyConstant.iff_exists_open _).1 hr u
    refine ⟨W₁ ∩ W₂, hW₁.inter hW₂, ⟨hu₁, hu₂⟩, fun v hv => ?_⟩
    simp only [Function.comp_apply]
    rw [hformula v, hformula u, hc₁ v hv.1, hc₂ v hv.2]
  have hLC := isLocallyConstant_of_isLocallyConstant_comp
    (AlgebraicStacks.isOpenMap_chartPointMap B S hS U 𝒳 f hsm)
    (AlgebraicStacks.surjective_chartPointMap B S hS U 𝒳 f hsurj) hcomp
  intro x y
  exact apply_eq_of_isIrreducible hLC (IrreducibleSpace.isIrreducible_univ _) trivial trivial

/-- The dimension of Stacks 0AFN is the same at the images of any two points of a smooth
surjective scheme chart of a Jacobson, catenary, locally Noetherian source over an algebraic stack
with irreducible space of points, given the local constancy of the relative dimension of the
associated chart by an algebraic space.

This is the argument of **Stacks 0DRX**. At a point `u` of the chart `U`,
`AlgebraicGeometry.exists_isOpen_isIrreducible_topologicalKrullDimAt_eq` produces a nonempty open
irreducible `V ⊆ U` whose closure contains `u` and on which the local dimension of `U` is
constantly `dim_u(U)`. The relative dimension is constant on the closure of `V`, that set being
irreducible and hence connected, so the formula of Stacks 0DRJ makes `dim_x(𝒳)` the same at the
images of `u` and of every point of `V`. Two such open sets have nonempty open images in `|𝒳|`,
which meet because `|𝒳|` is irreducible, and a common point of the two images carries the two
values to each other. -/
private theorem isConstant_dimensionAtPoint_of_spaceChart
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒳Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒳.val))
    (U : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hfsm : AlgebraicStacks.IsSmooth B S hS f) (hfsurj : IsSurjective B S hS f)
    (hUjac : JacobsonSpace ((BigFppfOver.toScheme B S hS).obj U))
    (hUnoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U))
    (hUcat : IrreducibleClosedsCodim.IsCatenarySpace ((BigFppfOver.toScheme B S hS).obj U))
    (g : algebraicSpaceStack.{u, w} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) ⟶ 𝒳)
    (hgsm : AlgebraicStacks.IsSmooth B S hS g)
    (hgpt : ∀ q : Space.points B S hS (yoneda.obj U),
      pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
          (fibredCategory B S hS (yoneda.obj U)).property 𝒳.val.property g.hom.hom
          (stackPointOfSpacePoint B S hS (yoneda.obj U) q) =
        pointsMap B S hS (schemeFibredCategory B S hS U).val
          (schemeFibredCategory B S hS U).property 𝒳.val.property f.hom.hom
          (representedChartPointMap B S hS U q))
    (hgft : AlgebraicStacks.IsLocallyOfFiniteType B S hS g)
    (hrel : IsLocallyConstant
      (relativeDimensionAt.{u, w} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝒳 g
        hgft)) :
    ∀ x y : points B S hS 𝒳.val.val 𝒳.val.property,
      dimensionAtPoint B S hS 𝒳 h𝒳 x = dimensionAtPoint B S hS 𝒳 h𝒳 y := by
  classical
  let _ := pointTopology B S hS 𝒳.val
  let _ := pointTopology B S hS (schemeFibredCategory B S hS U)
  have _ := h𝒳Irreducible
  have _ := hUjac
  have _ := hUnoeth
  set Us := (BigFppfOver.toScheme B S hS).obj U with hUsdef
  set φ := AlgebraicStacks.chartPointMap B S hS U 𝒳 f with hφdef
  -- the relative dimension of the chart, read on the scheme
  set rr : Us → WithBot ℕ∞ := fun t =>
    relativeDimensionAt.{u, w} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝒳 g hgft
      ((Space.pointsEquivScheme B S hS U).symm t) with hrrdef
  have hrrlc : IsLocallyConstant rr :=
    hrel.comp_continuous (continuous_pointsEquivScheme_symm B S hS U)
  -- the map on points of the two charts agree
  have hptmap : ∀ q : Space.points B S hS (yoneda.obj U),
      φ (Space.pointsToScheme B S hS U q) =
        pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
          (fibredCategory B S hS (yoneda.obj U)).property 𝒳.val.property g.hom.hom
          (stackPointOfSpacePoint B S hS (yoneda.obj U) q) := by
    intro q
    have hsymm : (Stack.pointsHomeomorphScheme B S hS U).symm
        (Space.pointsToScheme B S hS U q) = representedChartPointMap B S hS U q :=
      (Stack.pointsHomeomorphScheme B S hS U).symm_apply_eq.mpr
        (pointsHomeomorphScheme_representedChartPointMap B S hS U q).symm
    rw [hgpt q, hφdef]
    exact congrArg (AlgebraicStacks.pointsMap B S hS f) hsymm
  -- the formula of Stacks 0DRJ at the chart, with its finite relative dimension
  have hform : ∀ t : Us, ∃ m : ℕ, rr t = (m : WithBot ℕ∞) ∧
      dimensionAtPoint B S hS 𝒳 h𝒳 (φ t) =
        dimensionSubNat (topologicalKrullDimAt Us t) m := by
    intro t
    obtain ⟨q, hq⟩ := Space.surjective_pointsToScheme B S hS U t
    subst hq
    have hqq : (Space.pointsEquivScheme B S hS U).symm (Space.pointsToScheme B S hS U q) = q :=
      (Space.pointsEquivScheme B S hS U).symm_apply_apply q
    obtain ⟨m, hm⟩ := exists_relativeDimensionAt_eq_natCast B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) 𝒳 g hgft q
    refine ⟨m, ?_, ?_⟩
    · simp only [hrrdef, hqq]
      exact hm
    · have h0DRJ := dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒳 h𝒳 _
        (isAlgebraicSpace_yoneda B S hS U) g hgsm hgft q rfl m hm
      rw [dimensionAtPoint_yoneda_eq_topologicalKrullDimAt] at h0DRJ
      rw [hptmap q]
      exact h0DRJ
  -- around every point of the chart, an open set on which the dimension of `𝒳` is that value
  have key : ∀ t : Us, ∃ V : Set Us, IsOpen V ∧ V.Nonempty ∧
      ∀ v ∈ V, dimensionAtPoint B S hS 𝒳 h𝒳 (φ v) = dimensionAtPoint B S hS 𝒳 h𝒳 (φ t) := by
    intro t
    obtain ⟨V, hVopen, hVirr, htV, hdimt, hdimv⟩ :=
      exists_isOpen_isIrreducible_topologicalKrullDimAt_eq Us hUcat t
    refine ⟨V, hVopen, hVirr.nonempty, fun v hv => ?_⟩
    obtain ⟨m, hmr, hmD⟩ := hform t
    obtain ⟨n, hnr, hnD⟩ := hform v
    have hrrv : rr v = rr t :=
      apply_eq_of_isIrreducible hrrlc hVirr.closure (subset_closure hv) htV
    have hmn : m = n := by
      have hcast : (n : WithBot ℕ∞) = (m : WithBot ℕ∞) := by rw [← hnr, hrrv, hmr]
      exact_mod_cast hcast.symm
    rw [hnD, hmD, hdimv v hv, hdimt, hmn]
  intro x y
  obtain ⟨u, hu⟩ := AlgebraicStacks.surjective_chartPointMap B S hS U 𝒳 f hfsurj x
  obtain ⟨u', hu'⟩ := AlgebraicStacks.surjective_chartPointMap B S hS U 𝒳 f hfsurj y
  obtain ⟨V, hVopen, ⟨w, hw⟩, hVconst⟩ := key u
  obtain ⟨V', hV'open, ⟨w', hw'⟩, hV'const⟩ := key u'
  have hφopen : IsOpenMap φ := AlgebraicStacks.isOpenMap_chartPointMap B S hS U 𝒳 f hfsm
  obtain ⟨z, -, hz, hz'⟩ :=
    (IrreducibleSpace.isIrreducible_univ
        (points B S hS 𝒳.val.val 𝒳.val.property)).isPreirreducible
      (φ '' V) (φ '' V') (hφopen V hVopen) (hφopen V' hV'open)
      ⟨φ w, trivial, w, hw, rfl⟩ ⟨φ w', trivial, w', hw', rfl⟩
  obtain ⟨v, hvV, hvz⟩ := hz
  obtain ⟨v', hv'V', hv'z⟩ := hz'
  rw [← hu, ← hu', ← hVconst v hvV, ← hV'const v' hv'V', hvz, hv'z]

/-- **Stacks 0DRX.** On a Jacobson, pseudo-catenary, locally Noetherian algebraic stack `𝒳`
over `S` whose space of points `|𝒳|` is irreducible, the dimension `dim_x(𝒳)` of Stacks 0AFN is
the same at every point of `|𝒳|`.

Pseudo-catenarity (Stacks 0DRU) provides a smooth surjective 1-morphism from the algebraic stack
of a scheme `U` of the site which is locally Noetherian and universally catenary; `U` is then
catenary, and Jacobson by the universal scheme criterion of Stacks 04YF. The dimension formula of
Stacks 0DRJ holds along that chart, read as a chart by the algebraic space `U` represents, and the
relative dimension occurring in it is locally constant by Stacks 0DRQ (2). Around each point of
`U` the local dimension of `U` is then the dimension of a nonempty open irreducible subset, by
Stacks 0DRT at the irreducible components, so `dim_x(𝒳)` takes on the image of that subset the
single value it has at the given point; two such images meet in `|𝒳|`, which is irreducible, and
that common point identifies any two values. -/
@[stacks 0DRX]
theorem isConstant_dimensionAtPoint_of_irreducibleSpace (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒳Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒳.val)) :
    ∀ x y : points B S hS 𝒳.val.val 𝒳.val.property,
      dimensionAtPoint B S hS 𝒳 h𝒳 x = dimensionAtPoint B S hS 𝒳 h𝒳 y := by
  obtain ⟨U, f, hfsurj, hfsm, hUnoeth, hUcat⟩ := h𝒳Catenary
  have hUjac : JacobsonSpace ((BigFppfOver.toScheme B S hS).obj U) :=
    (exists_scheme_atlas_iff_forall_scheme B S hS
      (fun X : Scheme.{u} => JacobsonSpace X) 𝒳).1 h𝒳Jacobson U f hfsm
  have hUcatsp : IrreducibleClosedsCodim.IsCatenarySpace
      ((BigFppfOver.toScheme B S hS).obj U) := hUcat.isCatenarySpace (𝟙 _)
  obtain ⟨g, hgsm, hgpt⟩ :=
    exists_isSmooth_algebraicSpaceStack_hom_chartPointMap_eq.{u, w} B S hS 𝒳 U f hfsm
  have hgft := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS g hgsm
  exact isConstant_dimensionAtPoint_of_spaceChart.{u, w} B S hS 𝒳 h𝒳 h𝒳Irreducible U f hfsm
    hfsurj hUjac hUnoeth hUcatsp g hgsm hgpt hgft
    (isLocallyConstant_relativeDimensionAt_of_isSmooth_of_stack.{u, w} B S hS
      (isAlgebraicSpace_yoneda B S hS U) 𝒳 g hgsm hgft)

end AlgebraicGeometry.Stack

end
