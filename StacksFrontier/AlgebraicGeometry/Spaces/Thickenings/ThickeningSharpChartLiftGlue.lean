module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartLiftRefine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheaf

/-!
# The chartwise morphisms attached to a comorphism through a thickening agree

Let `Z ⊆ X` be a thickening of algebraic spaces over a scheme `S` with inclusion `i : Z ⟶ X`,
let `c : X ⟶ W`, let `r : W ⟶ W''`, and let `a : 𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` be a morphism of
sheaves of rings agreeing with the comorphism of `c` read through the thickening on the regular
functions read from `W''`.

`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpChartOverBase.lean` attaches to
`a` and an affine chart diagram — an affine étale chart `V` of `W` carrying an affine chart
diagram over `r`, together with an étale scheme chart of `X` above `X ×_W V` — a morphism of the
big fppf category over `S`, hence a section of `W` over that chart of `X`.  That is a *chartwise*
construction, and this file proves that it is **independent of the chart diagram**: two affine
chart diagrams give one and the same section of `W` over any étale chart of `X` lying over both.

This is the compatibility a gluing argument needs, and it is what makes the chartwise solutions
of the lifting problem of [Stacks Project, Tag 0618] the restrictions of a single global one.

## The argument

Fix two affine chart diagrams, with charts `V₁`, `V₂` of `W` and indices `j₁`, `j₂`, and an
étale chart `K` of `X` mapping to the two charts of `X` they carry.  Above each point of `K`:

1. **One chart of `W` for both diagrams.**  The two index chart morphisms `K ⟶ V₁` and `K ⟶ V₂`
   compose to one and the same morphism `K ⟶ X --c--> W`, so they factor through the fibre
   product `V₁ ×_W V₂`, which is again an étale chart of `W`
   (`AlgebraicGeometry.Space.SmallEtale.prodObj`).  An affine chart `V₃` of `W` above it carrying
   an affine chart diagram over `r` exists through the image of the point
   (`AlgebraicGeometry.Space.exists_hasAffineChartDiagram`), and the factorization base changes
   to it after refining `K` (`AlgebraicGeometry.Space.exists_chart_pullback`).
2. **Both sections are the section over `V₃`.**  Over `V₃` the datum `a` has a morphism of the
   site of its own, and the index over `V₃` pushed along `V₃ ⟶ V` is the given index restricted
   to the refined chart — the two have the same chart morphism, and an index is determined by its
   chart morphism.  So the two compatibilities of
   `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpChartLiftRefine.lean`
   identify both restricted sections with it.
3. **Hence the two sections agree**, the morphisms from the étale charts of `X` into an algebraic
   space being a separated presheaf on the small étale site of `X` and the arrows produced in
   step 1 hitting every point.

## Main results

* `AlgebraicGeometry.Space.exists_affineChartDiagram_common_chartHom`: **two chart morphisms over
  `c` out of one chart of `X` factor, locally, through a common affine chart of `W` carrying an
  affine chart diagram over `r`.**
* `AlgebraicGeometry.Space.eq_of_pointwise_agreement`: two sections of `W` over a chart of `X`
  agreeing on a chart above every point are equal.
* `AlgebraicGeometry.Space.eq_chartBaseChange_map_of_chartBaseChangeMap_eq`: an index whose chart
  morphism is that of another index followed by a morphism of charts of `W` is the base-changed
  index.
* `AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom_of_hasAffineChartDiagram`: the
  morphism of the site attached to `a` over a chart carrying an affine chart diagram over `r`.
* `AlgebraicGeometry.Space.yoneda_map_thickeningLiftChartSiteHom_refine`: the section attached to
  `a` over a chart diagram, restricted to a chart whose index factors through a third affine
  chart of `W`, is the section attached there.
* `AlgebraicGeometry.Space.yoneda_map_thickeningLiftChartSiteHom_eq`: **the section of `W` over a
  chart of `X` attached to `a` does not depend on the affine chart diagram it is read on.**

## Implementation notes

`AlgebraicGeometry.Space.yoneda_map_thickeningLiftChartSiteHom_refine` quantifies over an
arbitrary index over the third chart together with the equation its chart morphism satisfies,
rather than over a chart diagram: the `right` field of an index is the chart of `X` the section
lives over, so an equality of indices cannot be rewritten inside the morphism attached to it —
the motive is not type correct.  Quantifying over the *arrow* of the index with its `right` field
fixed, which is what
`AlgebraicGeometry.Space.thickeningLiftChartHom_chart_map_of_chartBaseChangeMap_eq` does, keeps
every rewrite at a variable whose type does not mention it.  This is the device the implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpFaithful.lean` record.

The affineness of a chart produced by `AlgebraicGeometry.Space.HasAffineChartDiagram` is turned
into an instance by a `haveI` stated at exactly the spelling the consumer asks for: instance
resolution does not unfold `AlgebraicGeometry.Space.indexOfChartDiagram`, so an instance for the
chart itself is not found at the `right`-field spelling.  For the same reason the two
compatibilities are composed as explicit `Eq.trans` chains rather than by `rw`: a rewrite of
`CategoryTheory.Functor.map_comp` at a morphism of the small étale site is not found
by keyed matching here, while `congrArg` at the same equation is instant.

**No `@[stacks]` attribute is placed.**  As in the files this one extends, what is proved is a
comparison internal to this development of two readings of [Stacks Project, Tag 03G8].

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3), diagrams of charts.
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED), the small étale site.
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK), thickenings.
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the correspondence
  between lifts and linear maps.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this
  compatibility is an input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A common affine chart of the target for two chart morphisms -/

/-- **Two chart morphisms over `c` out of one étale chart of `X` factor, locally on that chart,
through a common affine étale chart of `W` carrying an affine chart diagram over `r`.**

The two chart morphisms `q₁ : K ⟶ V₁` and `q₂ : K ⟶ V₂` compose to the same morphism
`K ⟶ X --c--> W`, so they factor through the fibre product `V₁ ×_W V₂`, which is again an étale
chart of `W` by `AlgebraicGeometry.Space.SmallEtale.prodObj`.  Above the image of a point of `K`
in it there is an affine étale chart `V₃` carrying an affine chart diagram over `r`
(`AlgebraicGeometry.Space.exists_hasAffineChartDiagram`), and the chart morphism of `K` into the
fibre product can be base changed to `V₃` after refining `K`
(`AlgebraicGeometry.Space.exists_chart_pullback`), with the point still in the image. -/
theorem exists_affineChartDiagram_common_chartHom
    {X W W'' : AlgebraicSpaces B S hS} (c : X ⟶ W) (r : W ⟶ W'')
    (K : SmallEtale B S hS X.1) (V₁ V₂ : SmallEtale B S hS W.1)
    (q₁ : (SmallEtale.toOver B S hS X.1).obj K ⟶ (SmallEtale.toOver B S hS W.1).obj V₁)
    (q₂ : (SmallEtale.toOver B S hS X.1).obj K ⟶ (SmallEtale.toOver B S hS W.1).obj V₂)
    (hq₁ : yoneda.map q₁ ≫ V₁.1.hom = K.1.hom ≫ c.hom)
    (hq₂ : yoneda.map q₂ ≫ V₂.1.hom = K.1.hom ≫ c.hom)
    (z : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj K)) :
    ∃ (K₃ : SmallEtale B S hS X.1) (n : K₃ ⟶ K) (V₃ : SmallEtale B S hS W.1)
      (p₁ : V₃ ⟶ V₁) (p₂ : V₃ ⟶ V₂)
      (q₃ : (SmallEtale.toOver B S hS X.1).obj K₃ ⟶ (SmallEtale.toOver B S hS W.1).obj V₃),
      HasAffineChartDiagram B S hS r V₃ ∧
        yoneda.map q₃ ≫ V₃.1.hom = K₃.1.hom ≫ c.hom ∧
        q₃ ≫ (SmallEtale.toOver B S hS W.1).map p₁ =
          (SmallEtale.toOver B S hS X.1).map n ≫ q₁ ∧
        q₃ ≫ (SmallEtale.toOver B S hS W.1).map p₂ =
          (SmallEtale.toOver B S hS X.1).map n ≫ q₂ ∧
        ∃ z' : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj K₃),
          (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map n) z' = z := by
  have hfst : (SmallEtale.toOver B S hS W.1).map (SmallEtale.prodFst B S hS W.1 V₁ V₂) =
      V₁.property.rep.fst' V₂.1.hom := rfl
  have hsnd : (SmallEtale.toOver B S hS W.1).map (SmallEtale.prodSnd B S hS W.1 V₁ V₂) =
      V₁.property.rep.snd V₂.1.hom := rfl
  have hlift : yoneda.map q₁ ≫ V₁.1.hom = yoneda.map q₂ ≫ V₂.1.hom := hq₁.trans hq₂.symm
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : (SmallEtale.toOver B S hS X.1).obj K ⟶
      (SmallEtale.toOver B S hS W.1).obj (SmallEtale.prodObj B S hS W.1 V₁ V₂),
      t ≫ (SmallEtale.toOver B S hS W.1).map (SmallEtale.prodFst B S hS W.1 V₁ V₂) = q₁ ∧
        t ≫ (SmallEtale.toOver B S hS W.1).map (SmallEtale.prodSnd B S hS W.1 V₁ V₂) = q₂ :=
    ⟨V₁.property.rep.lift' q₁ q₂ hlift,
      Functor.relativelyRepresentable.lift'_fst _ _ _ _,
      Functor.relativelyRepresentable.lift'_snd _ _ _ _⟩
  have hPt : yoneda.map t ≫ (SmallEtale.prodObj B S hS W.1 V₁ V₂).1.hom =
      K.1.hom ≫ c.hom := by
    change yoneda.map t ≫ yoneda.map ((SmallEtale.toOver B S hS W.1).map
      (SmallEtale.prodSnd B S hS W.1 V₁ V₂)) ≫ V₂.1.hom = K.1.hom ≫ c.hom
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ V₂.1.hom)
        ((yoneda.map_comp t _).symm.trans (congrArg yoneda.map ht₂))).trans hq₂)
  obtain ⟨V₃, aa, hV₃, y, hy⟩ := exists_hasAffineChartDiagram B S hS r
    (SmallEtale.prodObj B S hS W.1 V₁ V₂) ((BigFppfOver.toScheme B S hS).map t z)
  obtain ⟨K₃, n, q₃, hq₃, hcomm, w', hw'₁, -⟩ :=
    exists_chart_pullback B S hS c K
      (U₀ := SmallEtale.prodObj B S hS W.1 V₁ V₂) t hPt aa z y hy.symm
  refine ⟨K₃, n, V₃, aa ≫ SmallEtale.prodFst B S hS W.1 V₁ V₂,
    aa ≫ SmallEtale.prodSnd B S hS W.1 V₁ V₂, q₃, hV₃, hq₃, ?_, ?_, w', hw'₁⟩
  · rw [CategoryTheory.Functor.map_comp, ← Category.assoc, hcomm, Category.assoc, ht₁]
  · rw [CategoryTheory.Functor.map_comp, ← Category.assoc, hcomm, Category.assoc, ht₂]

/-! ### Two sections of the target agreeing locally on a chart -/

/-- The sieve of the étale charts above `K` on which two sections of `W` over `K` agree. -/
private def sectionAgreementSieve {X W : AlgebraicSpaces B S hS} (K : SmallEtale B S hS X.1)
    (s₁ s₂ : yoneda.obj ((SmallEtale.toOver B S hS X.1).obj K) ⟶ W.1) : Sieve K where
  arrows _ n := yoneda.map ((SmallEtale.toOver B S hS X.1).map n) ≫ s₁ =
    yoneda.map ((SmallEtale.toOver B S hS X.1).map n) ≫ s₂
  downward_closed := by
    intro K' K'' n hn g
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
      Category.assoc, hn]

/-- **Two sections of `W` over an étale chart of `X` which agree on a chart above every point of
that chart are equal.**  The morphisms from the étale charts of `X` into an algebraic space form
a sheaf on the small étale site of `X`
(`AlgebraicGeometry.Space.SmallEtale.isSheaf_comp_toOver`), hence a separated presheaf, and a
sieve whose arrows hit every point is a covering sieve
(`AlgebraicGeometry.Space.smallEtale_sieve_of_pointwise_covering`). -/
theorem eq_of_pointwise_agreement {X W : AlgebraicSpaces B S hS} (K : SmallEtale B S hS X.1)
    (s₁ s₂ : yoneda.obj ((SmallEtale.toOver B S hS X.1).obj K) ⟶ W.1)
    (h : ∀ z : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj K),
      ∃ (K' : SmallEtale B S hS X.1) (n : K' ⟶ K),
        (yoneda.map ((SmallEtale.toOver B S hS X.1).map n) ≫ s₁ =
          yoneda.map ((SmallEtale.toOver B S hS X.1).map n) ≫ s₂) ∧
          ∃ z' : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj K'),
            (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map n) z' = z) :
    s₁ = s₂ := by
  have hsep : Presheaf.IsSeparated (SmallEtale.topology B S hS X.1)
      ((SmallEtale.toOver B S hS X.1).op ⋙ W.1) :=
    (SmallEtale.isSheaf_comp_toOver B S hS X.1 W.2.isSheaf).isSeparated
  have hR : sectionAgreementSieve B S hS K s₁ s₂ ∈ SmallEtale.topology B S hS X.1 K := by
    refine smallEtale_sieve_of_pointwise_covering B S hS X.1 K _ fun z ↦ ?_
    obtain ⟨K', n, hn, z', hz'⟩ := h z
    exact ⟨K', n, hn, z', hz'⟩
  refine yonedaEquiv.injective ?_
  refine hsep K (sectionAgreementSieve B S hS K s₁ s₂) hR _ _ ?_
  intro K' n hn
  change W.1.map ((SmallEtale.toOver B S hS X.1).map n).op (yonedaEquiv s₁) =
    W.1.map ((SmallEtale.toOver B S hS X.1).map n).op (yonedaEquiv s₂)
  rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
  exact congrArg yonedaEquiv hn

/-! ### An index described by its chart morphism -/

variable {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- **An index of the limit of chart sections over `V₂` whose chart morphism is the chart
morphism of an index over `V₁` followed by a morphism of charts `V₁ ⟶ V₂` is the base-changed
index.**  A morphism into the cartesian base change is determined by the chart morphism it
induces, `AlgebraicGeometry.Space.chartBaseChangeMap_injective`, and the chart morphism of the
base-changed index is computed by `AlgebraicGeometry.Space.chartBaseChangeMap_map`. -/
theorem eq_chartBaseChange_map_of_chartBaseChangeMap_eq (c : X ⟶ W)
    {V₁ V₂ : SmallEtale B S hS W.1} (m : V₁ ⟶ V₂)
    (j : StructuredArrow (op (chartBaseChange B S hS c V₁)) (comparisonFunctor B S hS X).op)
    (θ : op (chartBaseChange B S hS c V₂) ⟶ (comparisonFunctor B S hS X).op.obj j.right)
    (hθ : chartBaseChangeMap B S hS c V₂ (StructuredArrow.mk (Y := j.right) θ) =
      chartBaseChangeMap B S hS c V₁ j ≫ (SmallEtale.toOver B S hS W.1).map m) :
    θ = ((spacesBaseChange B S hS c).functor.map
      ((comparisonFunctor B S hS W).map m)).op ≫ j.hom :=
  congrArg Quiver.Hom.op (chartBaseChangeMap_injective B S hS c
    (hθ.trans (chartBaseChangeMap_map B S hS c m j).symm))

/-- `AlgebraicGeometry.Space.thickeningLiftChartHom_chart_map` with the base-changed index
described by its chart morphism rather than written out, which is the form in which two chart
diagrams refined to a common chart of `W` can be compared. -/
theorem thickeningLiftChartHom_chart_map_of_chartBaseChangeMap_eq
    (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    {V₁ V₂ : SmallEtale B S hS W.1} (m : V₁ ⟶ V₂)
    (j : StructuredArrow (op (chartBaseChange B S hS c V₁)) (comparisonFunctor B S hS X).op)
    (θ : op (chartBaseChange B S hS c V₂) ⟶ (comparisonFunctor B S hS X).op.obj j.right)
    (hθ : chartBaseChangeMap B S hS c V₂ (StructuredArrow.mk (Y := j.right) θ) =
      chartBaseChangeMap B S hS c V₁ j ≫ (SmallEtale.toOver B S hS W.1).map m)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V₁))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V₂))] :
    thickeningLiftChartHom B S hS Z hZ c a V₂ (StructuredArrow.mk (Y := j.right) θ) =
      thickeningLiftChartHom B S hS Z hZ c a V₁ j ≫
        (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS W.1).map m) := by
  rw [eq_chartBaseChange_map_of_chartBaseChangeMap_eq B S hS c m j θ hθ]
  exact thickeningLiftChartHom_chart_map B S hS Z hZ c a m j

/-! ### The morphism of the site over a chart carrying an affine chart diagram -/

/-- **The morphism of the site attached to `a` exists over any affine étale chart of `W`
carrying an affine chart diagram over `r`**, as soon as `a` agrees with the comorphism of `c`
read through the thickening on the functions read from `W''`.

This is
`AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom_of_eq_on_structureSharpRingInverseImage`
with the chart diagram supplied by `AlgebraicGeometry.Space.HasAffineChartDiagram`, so that the
chart of `W` is an ordinary variable rather than the `right` field of an index. -/
theorem exists_thickeningLiftChartSiteHom_of_hasAffineChartDiagram
    (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    {W'' : AlgebraicSpaces B S hS} (r : W ⟶ W'')
    (hbase : ∀ (V : SmallEtale B S hS W.1)
        (s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj (op V))),
      a.hom.app (op V) ((structureSharpRingInverseImage B S hS r).hom.app (op V) s) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op V)
          ((structureSharpRingInverseImage B S hS r).hom.app (op V) s))
    (V₃ : SmallEtale B S hS W.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V₃))]
    (V' : SmallEtale B S hS W''.1)
    (qq : (SmallEtale.toOver B S hS W.1).obj V₃ ⟶ (SmallEtale.toOver B S hS W''.1).obj V')
    (hqq : V₃.1.hom ≫ r.hom = yoneda.map qq ≫ V'.1.hom)
    (hV'aff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS W''.1).obj V')))
    (j₃ : StructuredArrow (op (chartBaseChange B S hS c V₃)) (comparisonFunctor B S hS X).op) :
    ∃ ψ₃ : (SmallEtale.toOver B S hS X.1).obj j₃.right.unop ⟶
        (SmallEtale.toOver B S hS W.1).obj V₃,
      (BigFppfOver.toScheme B S hS).map ψ₃ =
        thickeningLiftChartHom B S hS Z hZ c a V₃ j₃ := by
  have := hV'aff
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj
      (indexOfChartDiagram B S hS r (⟨V₃, V', qq, hqq⟩ :
        ChartDiagram B S hS W.1 W''.1 r.hom)).right.unop)) :=
    (inferInstance : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS W.1).obj V₃)))
  exact exists_thickeningLiftChartSiteHom_of_eq_on_structureSharpRingInverseImage
    B S hS Z hZ c a r V' (indexOfChartDiagram B S hS r ⟨V₃, V', qq, hqq⟩) j₃ fun s ↦ hbase _ s

/-! ### Two chart diagrams refined to a common one -/

/-- **A chart morphism attached to `a` over an affine chart diagram, read on a chart of `X`
whose index factors through a third affine chart `V₃` of `W`, is the chart morphism attached
over `V₃`.**

The index over `V` carried by that chart is both the given index restricted along the morphism
of charts of `X` and the index over `V₃` pushed along `V₃ ⟶ V`: the two have the same chart
morphism, and an index is determined by its chart morphism
(`AlgebraicGeometry.Space.chartBaseChangeMap_injective`).  So the two compatibilities of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpChartLiftRefine.lean` apply in
turn, and the resulting morphisms of the site differ by the morphism of charts of `W`, which
composes with the structure morphism of `V` to that of `V₃`. -/
theorem yoneda_map_thickeningLiftChartSiteHom_refine (hZ : IsThickening B S hS X Z.1)
    (c : X ⟶ W) (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    {V V₃ : SmallEtale B S hS W.1}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V₃))]
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    (j₃ : StructuredArrow (op (chartBaseChange B S hS c V₃)) (comparisonFunctor B S hS X).op)
    (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj V)
    (hψ : (BigFppfOver.toScheme B S hS).map ψ = thickeningLiftChartHom B S hS Z hZ c a V j)
    (ψ₃ : (SmallEtale.toOver B S hS X.1).obj j₃.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj V₃)
    (hψ₃ : (BigFppfOver.toScheme B S hS).map ψ₃ =
      thickeningLiftChartHom B S hS Z hZ c a V₃ j₃)
    (nn : j₃.right.unop ⟶ j.right.unop) (p : V₃ ⟶ V)
    (hcompat : chartBaseChangeMap B S hS c V₃ j₃ ≫ (SmallEtale.toOver B S hS W.1).map p =
      (SmallEtale.toOver B S hS X.1).map nn ≫ chartBaseChangeMap B S hS c V j) :
    yoneda.map ((SmallEtale.toOver B S hS X.1).map nn) ≫ yoneda.map ψ ≫ V.1.hom =
      yoneda.map ψ₃ ≫ V₃.1.hom := by
  have hwp : yoneda.map ((SmallEtale.toOver B S hS W.1).map p) ≫ V.1.hom = V₃.1.hom :=
    CostructuredArrow.w _
  have hjj : chartBaseChangeMap B S hS c V (StructuredArrow.mk (Y := j₃.right)
        (j.hom ≫ ((comparisonFunctor B S hS X).map nn).op)) =
      (SmallEtale.toOver B S hS X.1).map nn ≫ chartBaseChangeMap B S hS c V j :=
    chartBaseChangeMap_comp B S hS c V
      (StructuredArrow.homMk nn.op rfl :
        j ⟶ StructuredArrow.mk (Y := j₃.right)
          (j.hom ≫ ((comparisonFunctor B S hS X).map nn).op))
  have hind : thickeningLiftChartHom B S hS Z hZ c a V (StructuredArrow.mk (Y := j₃.right)
        (j.hom ≫ ((comparisonFunctor B S hS X).map nn).op)) =
      (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map nn) ≫
        thickeningLiftChartHom B S hS Z hZ c a V j :=
    thickeningLiftChartHom_index_comp B S hS Z hZ c a V
      (StructuredArrow.homMk nn.op rfl :
        j ⟶ StructuredArrow.mk (Y := j₃.right)
          (j.hom ≫ ((comparisonFunctor B S hS X).map nn).op))
  have hchart : thickeningLiftChartHom B S hS Z hZ c a V (StructuredArrow.mk (Y := j₃.right)
        (j.hom ≫ ((comparisonFunctor B S hS X).map nn).op)) =
      thickeningLiftChartHom B S hS Z hZ c a V₃ j₃ ≫
        (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS W.1).map p) :=
    thickeningLiftChartHom_chart_map_of_chartBaseChangeMap_eq B S hS Z hZ c a p j₃
      (j.hom ≫ ((comparisonFunctor B S hS X).map nn).op) (hjj.trans hcompat.symm)
  have hmaps : (BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS X.1).map nn ≫ ψ) =
      (BigFppfOver.toScheme B S hS).map
        (ψ₃ ≫ (SmallEtale.toOver B S hS W.1).map p) :=
    ((BigFppfOver.toScheme B S hS).map_comp _ _).trans
      ((congrArg (fun k ↦ (BigFppfOver.toScheme B S hS).map
            ((SmallEtale.toOver B S hS X.1).map nn) ≫ k) hψ).trans
        (hind.symm.trans (hchart.trans
          ((congrArg (fun k ↦ k ≫ (BigFppfOver.toScheme B S hS).map
              ((SmallEtale.toOver B S hS W.1).map p)) hψ₃).symm.trans
            ((BigFppfOver.toScheme B S hS).map_comp _ _).symm))))
  have hsite : (SmallEtale.toOver B S hS X.1).map nn ≫ ψ =
      ψ₃ ≫ (SmallEtale.toOver B S hS W.1).map p :=
    (BigFppfOver.toScheme B S hS).map_injective hmaps
  rw [← CategoryTheory.Functor.map_comp_assoc, hsite, CategoryTheory.Functor.map_comp_assoc, hwp]

/-! ### The transported comorphism read at the composite index -/

/-- **A solution of the lifting problem read at the index `e`, carried to the composite spelling,
still agrees with the comorphism of `c` read through the thickening on the regular functions read
from `W''`.**

The transport `AlgebraicGeometry.Space.thickeningLiftOfIndex` is composition with an isomorphism
of sheaves, so it is injective on the value over a chart at a regular function
(`AlgebraicGeometry.Space.app_thickeningLiftOfIndex_congr`), and it carries the comorphism read
at the index `e` to the comorphism read at the composite
(`AlgebraicGeometry.Space.thickeningLiftOfIndex_structureSharpThroughThickeningAt`).

This is the conversion `AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom_of_index`
performs on its hypothesis, stated once so that a consumer whose comorphism is a transported
solution can supply the hypothesis of
`AlgebraicGeometry.Space.yoneda_map_thickeningLiftChartSiteHom_eq`.  It is kept at abstract
arguments on purpose: the same composition at a written-out solution of the lifting problem is a
deterministic kernel timeout. -/
theorem app_thickeningLiftOfIndex_eq_structureSharpThroughThickening (c : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e)
    (A : structureRingSheaf B S hS W ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
        (smallToposMorphismTypeU B S hS e).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
    {W'' : AlgebraicSpaces B S hS} (r : W ⟶ W'')
    (hA : ∀ (V : SmallEtale B S hS W.1)
        (s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj (op V))),
      A.hom.app (op V) ((structureSharpRingInverseImage B S hS r).hom.app (op V) s) =
        (structureSharpThroughThickeningAt B S hS Z c e h).hom.app (op V)
          ((structureSharpRingInverseImage B S hS r).hom.app (op V) s))
    (V : SmallEtale B S hS W.1)
    (s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj (op V))) :
    (thickeningLiftOfIndex B S hS Z c e h A).hom.app (op V)
        ((structureSharpRingInverseImage B S hS r).hom.app (op V) s) =
      (structureSharpThroughThickening B S hS Z c).hom.app (op V)
        ((structureSharpRingInverseImage B S hS r).hom.app (op V) s) :=
  (app_thickeningLiftOfIndex_congr B S hS Z c e h A
        (structureSharpThroughThickeningAt B S hS Z c e h) (op V) _ (hA V s)).trans
    (congrArg
      (fun n : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c ↦
        n.hom.app (op V)
          ((structureSharpRingInverseImage B S hS r).hom.app (op V) s))
      (thickeningLiftOfIndex_structureSharpThroughThickeningAt B S hS Z c e h))

/-! ### Two affine chart diagrams give the same section -/

/-- A chart of `X` over the chart of `W` carried by an index lies over `c`. -/
private theorem yoneda_map_chartBaseChangeMap_comp_hom (c : X ⟶ W) {V : SmallEtale B S hS W.1}
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    {K : SmallEtale B S hS X.1} (n : K ⟶ j.right.unop) :
    yoneda.map ((SmallEtale.toOver B S hS X.1).map n ≫ chartBaseChangeMap B S hS c V j) ≫
      V.1.hom = K.1.hom ≫ c.hom := by
  have hw : yoneda.map ((SmallEtale.toOver B S hS X.1).map n) ≫ j.right.unop.1.hom =
    K.1.hom := CostructuredArrow.w _
  rw [CategoryTheory.Functor.map_comp_assoc]
  exact (congrArg (fun k ↦ yoneda.map ((SmallEtale.toOver B S hS X.1).map n) ≫ k)
    (chartDiagramOfIndex B S hS c V j).comm.symm).trans ((reassoc_of% hw) c.hom)

/-- Refining a section over a chart diagram to a chart of `X` above the chart diagram `(K₃, V₃)`
gives the section attached over `V₃`. -/
private theorem yoneda_map_comp_eq_of_chartDiagram_index (hZ : IsThickening B S hS X Z.1)
    (c : X ⟶ W) (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    {V V₃ : SmallEtale B S hS W.1}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V₃))]
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    {K₃ : SmallEtale B S hS X.1}
    (q₃ : (SmallEtale.toOver B S hS X.1).obj K₃ ⟶ (SmallEtale.toOver B S hS W.1).obj V₃)
    (hq₃ : yoneda.map q₃ ≫ V₃.1.hom = K₃.1.hom ≫ c.hom)
    (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj V)
    (hψ : (BigFppfOver.toScheme B S hS).map ψ = thickeningLiftChartHom B S hS Z hZ c a V j)
    (ψ₃ : (SmallEtale.toOver B S hS X.1).obj K₃ ⟶ (SmallEtale.toOver B S hS W.1).obj V₃)
    (hψ₃ : (BigFppfOver.toScheme B S hS).map ψ₃ = thickeningLiftChartHom B S hS Z hZ c a V₃
      (indexOfChartDiagram B S hS c (⟨K₃, V₃, q₃, hq₃.symm⟩ :
        ChartDiagram B S hS X.1 W.1 c.hom)))
    {K : SmallEtale B S hS X.1} (n : K₃ ⟶ K) (n₁ : K ⟶ j.right.unop) (p : V₃ ⟶ V)
    (hp : q₃ ≫ (SmallEtale.toOver B S hS W.1).map p =
      (SmallEtale.toOver B S hS X.1).map n ≫
        ((SmallEtale.toOver B S hS X.1).map n₁ ≫ chartBaseChangeMap B S hS c V j)) :
    yoneda.map ((SmallEtale.toOver B S hS X.1).map n) ≫
      yoneda.map ((SmallEtale.toOver B S hS X.1).map n₁) ≫ yoneda.map ψ ≫ V.1.hom =
      yoneda.map ψ₃ ≫ V₃.1.hom := by
  have hc : chartBaseChangeMap B S hS c V₃ (indexOfChartDiagram B S hS c
        (⟨K₃, V₃, q₃, hq₃.symm⟩ : ChartDiagram B S hS X.1 W.1 c.hom)) ≫
        (SmallEtale.toOver B S hS W.1).map p =
      (SmallEtale.toOver B S hS X.1).map (n ≫ n₁) ≫ chartBaseChangeMap B S hS c V j := by
    rw [chartBaseChangeMap_indexOfChartDiagram B S hS c
      (⟨K₃, V₃, q₃, hq₃.symm⟩ : ChartDiagram B S hS X.1 W.1 c.hom),
      CategoryTheory.Functor.map_comp, Category.assoc]
    exact hp
  refine Eq.trans ?_ (yoneda_map_thickeningLiftChartSiteHom_refine B S hS Z hZ c a j
    (indexOfChartDiagram B S hS c (⟨K₃, V₃, q₃, hq₃.symm⟩ :
      ChartDiagram B S hS X.1 W.1 c.hom)) ψ hψ ψ₃ hψ₃ (n ≫ n₁) p hc)
  rw [← Category.assoc, ← yoneda.map_comp, ← (SmallEtale.toOver B S hS X.1).map_comp]
  rfl

/-- **The section of `W` over an étale chart of `X` attached to `a` does not depend on the
affine chart diagram it is read on.**

Let `V₁`, `V₂` be affine étale charts of `W`, let `j₁`, `j₂` be indices of the limits of chart
sections above them, and let `ψ₁`, `ψ₂` be the morphisms of the site attached to `a` there.  For
any étale chart `K` of `X` lying over the charts the two indices carry, the two sections of `W`
over `K` obtained by restriction agree.

Above every point of `K` the two index chart morphisms factor through one affine chart `V₃` of
`W` carrying an affine chart diagram over `r`
(`AlgebraicGeometry.Space.exists_affineChartDiagram_common_chartHom`); there `a` has a morphism
of the site of its own
(`AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom_of_hasAffineChartDiagram`), and both
restricted sections are its section over that chart, by
`AlgebraicGeometry.Space.yoneda_map_thickeningLiftChartSiteHom_refine`.  The morphisms into an
algebraic space from the étale charts of `X` form a separated presheaf, so pointwise agreement
is agreement (`AlgebraicGeometry.Space.eq_of_pointwise_agreement`).

This is the compatibility that lets the chartwise morphisms attached to a single comorphism
`a` glue to a global section of the sheaf of lifts. -/
theorem yoneda_map_thickeningLiftChartSiteHom_eq (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    {W'' : AlgebraicSpaces B S hS} (r : W ⟶ W'')
    (hbase : ∀ (V : SmallEtale B S hS W.1)
        (s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj (op V))),
      a.hom.app (op V) ((structureSharpRingInverseImage B S hS r).hom.app (op V) s) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op V)
          ((structureSharpRingInverseImage B S hS r).hom.app (op V) s))
    {V₁ V₂ : SmallEtale B S hS W.1}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V₁))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V₂))]
    (j₁ : StructuredArrow (op (chartBaseChange B S hS c V₁)) (comparisonFunctor B S hS X).op)
    (j₂ : StructuredArrow (op (chartBaseChange B S hS c V₂)) (comparisonFunctor B S hS X).op)
    (ψ₁ : (SmallEtale.toOver B S hS X.1).obj j₁.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj V₁)
    (hψ₁ : (BigFppfOver.toScheme B S hS).map ψ₁ = thickeningLiftChartHom B S hS Z hZ c a V₁ j₁)
    (ψ₂ : (SmallEtale.toOver B S hS X.1).obj j₂.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj V₂)
    (hψ₂ : (BigFppfOver.toScheme B S hS).map ψ₂ = thickeningLiftChartHom B S hS Z hZ c a V₂ j₂)
    (K : SmallEtale B S hS X.1) (n₁ : K ⟶ j₁.right.unop) (n₂ : K ⟶ j₂.right.unop) :
    yoneda.map ((SmallEtale.toOver B S hS X.1).map n₁) ≫ yoneda.map ψ₁ ≫ V₁.1.hom =
      yoneda.map ((SmallEtale.toOver B S hS X.1).map n₂) ≫ yoneda.map ψ₂ ≫ V₂.1.hom := by
  refine eq_of_pointwise_agreement B S hS K _ _ fun z ↦ ?_
  obtain ⟨K₃, n, V₃, p₁, p₂, q₃, hV₃, hq₃, hp₁, hp₂, z', hz'⟩ :=
    exists_affineChartDiagram_common_chartHom B S hS c r K V₁ V₂
      ((SmallEtale.toOver B S hS X.1).map n₁ ≫ chartBaseChangeMap B S hS c V₁ j₁)
      ((SmallEtale.toOver B S hS X.1).map n₂ ≫ chartBaseChangeMap B S hS c V₂ j₂)
      (yoneda_map_chartBaseChangeMap_comp_hom B S hS c j₁ n₁)
      (yoneda_map_chartBaseChangeMap_comp_hom B S hS c j₂ n₂) z
  obtain ⟨hV₃aff, V', qq, hqq, hV'aff⟩ := hV₃
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS W.1).obj V₃)) := hV₃aff
  obtain ⟨ψ₃, hψ₃⟩ := exists_thickeningLiftChartSiteHom_of_hasAffineChartDiagram
    B S hS Z hZ c a r hbase V₃ V' qq hqq.symm hV'aff
    (indexOfChartDiagram B S hS c (⟨K₃, V₃, q₃, hq₃.symm⟩ :
      ChartDiagram B S hS X.1 W.1 c.hom))
  refine ⟨K₃, n, ?_, z', hz'⟩
  exact (yoneda_map_comp_eq_of_chartDiagram_index B S hS Z hZ c a j₁ q₃ hq₃ ψ₁ hψ₁ ψ₃ hψ₃ n n₁
    p₁ hp₁).trans (yoneda_map_comp_eq_of_chartDiagram_index B S hS Z hZ c a j₂ q₃ hq₃ ψ₂ hψ₂ ψ₃
    hψ₃ n n₂ p₂ hp₂).symm

end AlgebraicGeometry.Space

end
