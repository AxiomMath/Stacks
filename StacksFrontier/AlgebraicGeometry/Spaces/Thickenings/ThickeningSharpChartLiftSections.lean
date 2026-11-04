module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartLiftGlue
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafDescent
public import StacksFrontier.CategoryTheory.Sites.LocalFactorizationCriteria

/-!
# The chartwise morphisms attached to a comorphism through a thickening glue

Let `Z ⊆ X` be a thickening of algebraic spaces over a scheme `S`, let `c : X ⟶ W`, let
`r : W ⟶ W''`, and let `a : 𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` be a morphism of sheaves of rings
agreeing with the comorphism of `c` read through the thickening on the regular functions read
from `W''`.

`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpChartLiftGlue.lean` attaches to
`a` a section of `W` over each étale chart of `X` carrying an index over an affine chart of `W`
with an affine chart diagram over `r`, and proves that the section does not depend on the chart
diagram.  This file **glues those sections into one morphism `X ⟶ W`**.

## The argument

1. The charts of `X` admitting a chart morphism over `c` to an affine chart of `W` with an affine
   chart diagram over `r` — the property
   `AlgebraicGeometry.Space.HasChartHomToAffineChartDiagram` — are cover-dense: above every point
   of every chart there is one
   (`AlgebraicGeometry.Space.exists_hasChartHomToAffineChartDiagram`), so a sieve containing all
   arrows out of such charts is covering
   (`AlgebraicGeometry.Space.mem_topology_of_hasChartHomToAffineChartDiagram`).
2. Over such a chart `a` has one well-defined section
   (`AlgebraicGeometry.Space.exists_chartLiftSection`): one exists, by
   `AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom_of_hasAffineChartDiagram`, and any
   two readings of it agree, by
   `AlgebraicGeometry.Space.yoneda_map_thickeningLiftChartSiteHom_eq`.
3. Cover-density gives the two hypotheses of the comparison of global sections along the
   inclusion of the full subcategory of such charts: the factorization sieves are covering
   because the refining chart is itself in the subcategory, and the connecting sieves are
   covering for the same reason — the refined chart dominates both given morphisms through
   itself.  So restriction of global sections of the sheaf of lifts of [Stacks Project, Tag 061D]
   along that inclusion is bijective
   (`Stacks.Sites.bijective_sectionsPrecomp_of_hasLocallyConnectedFactorizations`), and the
   family of step 2 — compatible by step 2 again — is the restriction of a global section.
4. A global section of the sheaf of lifts is the family of restrictions of a single morphism
   `X ⟶ W` over the base agreeing with the given morphism on `Z`
   (`AlgebraicGeometry.Space.existsUnique_hom_of_isChartLift_family`).

## Main results

* `AlgebraicGeometry.Space.HasChartHomToAffineChartDiagram`: the property of an étale chart of
  `X` of admitting a chart morphism over `c` to an affine chart of `W` carrying an affine chart
  diagram over `r`.
* `AlgebraicGeometry.Space.exists_hasChartHomToAffineChartDiagram`: such charts lie above every
  point of every chart of `X`.
* `AlgebraicGeometry.Space.mem_topology_of_hasChartHomToAffineChartDiagram`: they are
  cover-dense.
* `AlgebraicGeometry.Space.exists_chartLiftSection`: **over such a chart the datum `a` has a
  section** which every reading computes — the restriction of the morphism of the site attached
  to any index over any affine chart of `W`.
* `AlgebraicGeometry.Space.exists_hom_eq_thickeningLiftChartSiteHom`: **the chartwise sections
  attached to `a` are the restrictions of a single morphism `X ⟶ W`** over the base and
  agreeing with the given morphism on `Z`.

## Implementation notes

The affineness of a chart is always passed as an instance argument rather than recovered from
`AlgebraicGeometry.Space.HasAffineChartDiagram` under a binder: a `letI` for affineness inside a
`∀` is a deterministic heartbeat timeout.

`AlgebraicGeometry.Space.exists_chartLiftSection` is stated as the existence of a section
which *every* reading computes, rather than as a construction plus a comparison lemma.  That one
statement is simultaneously the well-definedness of the chartwise section, its value, and — read
at a composite `K' ⟶ K ⟶ j.right.unop` — its compatibility with restriction, which is all the
gluing needs.

**No `@[stacks]` attribute is placed.**  As in the files this one extends, what is proved is a
comparison internal to this development of two readings of [Stacks Project, Tag 03G8].

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3), diagrams of charts.
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED), the small étale site.
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D), the sheaf of lifts.
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the correspondence
  between lifts and linear maps.
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK), the comparison of
  global sections along a functor of sites.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this gluing is
  an input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The charts carrying a chart morphism to an affine chart diagram -/

variable {X W W'' : AlgebraicSpaces B S hS}

/-- **An étale chart of `X` admitting a chart morphism over `c` to an affine chart of `W`
carrying an affine chart diagram over `r`.**

These are the charts of `X` over which the morphism of the site attached to a solution of the
lifting problem exists, by
`AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom_of_hasAffineChartDiagram`. -/
def HasChartHomToAffineChartDiagram (c : X ⟶ W) (r : W ⟶ W'')
    (K : SmallEtale B S hS X.1) : Prop :=
  ∃ (V : SmallEtale B S hS W.1)
    (q : (SmallEtale.toOver B S hS X.1).obj K ⟶ (SmallEtale.toOver B S hS W.1).obj V),
    yoneda.map q ≫ V.1.hom = K.1.hom ≫ c.hom ∧ HasAffineChartDiagram B S hS r V

/-- **Above every point of every étale chart of `X` there is a chart admitting a chart morphism
over `c` to an affine chart of `W` carrying an affine chart diagram over `r`.**

An affine chart diagram over `c` through the point supplies a chart morphism to *some* affine
chart of `W` (`AlgebraicGeometry.Space.exists_hasAffineChartDiagram`), and that chart morphism is
refined to one landing in a chart with an affine chart diagram over `r` by
`AlgebraicGeometry.Space.exists_affineChartDiagram_common_chartHom`, read with its two chart
morphisms equal. -/
theorem exists_hasChartHomToAffineChartDiagram (c : X ⟶ W) (r : W ⟶ W'')
    (K : SmallEtale B S hS X.1)
    (z : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj K)) :
    ∃ (K₃ : SmallEtale B S hS X.1) (n : K₃ ⟶ K),
      HasChartHomToAffineChartDiagram B S hS c r K₃ ∧
        ∃ z' : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj K₃),
          (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map n) z' = z := by
  obtain ⟨K₁, a₁, ⟨-, V₁, q₁, hq₁, -⟩, z₁, hz₁⟩ := exists_hasAffineChartDiagram B S hS c K z
  obtain ⟨K₃, n, V₃, -, -, q₃, hV₃, hq₃, -, -, z₃, hz₃⟩ :=
    exists_affineChartDiagram_common_chartHom B S hS c r K₁ V₁ V₁ q₁ q₁ hq₁ hq₁ z₁
  refine ⟨K₃, n ≫ a₁, ⟨V₃, q₃, hq₃, hV₃⟩, z₃, ?_⟩
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Scheme.Hom.comp_apply,
    hz₃, hz₁]

/-- **The charts of `X` admitting a chart morphism over `c` to an affine chart of `W` carrying an
affine chart diagram over `r` are cover-dense.**  A sieve of an étale chart of `X` containing
every morphism whose source is such a chart is a covering sieve of the small étale site.

A sieve whose arrows are jointly surjective on the scheme points of the chart is covering
(`AlgebraicGeometry.Space.smallEtale_sieve_of_pointwise_covering`), and
`AlgebraicGeometry.Space.exists_hasChartHomToAffineChartDiagram` supplies, above each point, an
arrow of the sieve. -/
theorem mem_topology_of_hasChartHomToAffineChartDiagram (c : X ⟶ W) (r : W ⟶ W'')
    (K : SmallEtale B S hS X.1) (R : Sieve K)
    (hR : ∀ ⦃K' : SmallEtale B S hS X.1⦄ (n : K' ⟶ K),
      HasChartHomToAffineChartDiagram B S hS c r K' → R n) :
    R ∈ SmallEtale.topology B S hS X.1 K := by
  refine smallEtale_sieve_of_pointwise_covering B S hS X.1 K R fun z ↦ ?_
  obtain ⟨K₃, n, hK₃, z', hz'⟩ := exists_hasChartHomToAffineChartDiagram B S hS c r K z
  exact ⟨K₃, n, hR n hK₃, z', hz'⟩

/-- **The inclusion of the charts admitting a chart morphism to an affine chart diagram has local
factorizations.**  The factorization sieve of a chart contains every arrow out of such a chart,
the chart itself being the object to which it maps, so it is covering by
`AlgebraicGeometry.Space.mem_topology_of_hasChartHomToAffineChartDiagram`. -/
theorem hasLocalFactorizations_hasChartHomToAffineChartDiagram (c : X ⟶ W) (r : W ⟶ W'') :
    Stacks.Sites.HasLocalFactorizations (SmallEtale.topology B S hS X.1)
      (ObjectProperty.ι (HasChartHomToAffineChartDiagram B S hS c r)) := by
  intro K
  refine mem_topology_of_hasChartHomToAffineChartDiagram B S hS c r K _ fun {K'} n hK' ↦ ?_
  exact ⟨⟨K', hK'⟩, ⟨𝟙 K'⟩⟩

/-- **The inclusion of the charts admitting a chart morphism to an affine chart diagram has
connected local factorizations.**  Two morphisms of charts of `X` out of a chart `K` into two
such charts are both dominated, after restriction to any such chart `K'` above `K`, by `K'`
itself: the composites `K' ⟶ K ⟶ Kᵢ` are the required morphisms, and the dominating morphism is
the identity.  So the connecting sieve contains every arrow out of such a chart and is covering
by `AlgebraicGeometry.Space.mem_topology_of_hasChartHomToAffineChartDiagram`. -/
theorem hasConnectedLocalFactorizations_hasChartHomToAffineChartDiagram (c : X ⟶ W)
    (r : W ⟶ W'') :
    Stacks.Sites.HasConnectedLocalFactorizations (SmallEtale.topology B S hS X.1)
      (ObjectProperty.ι (HasChartHomToAffineChartDiagram B S hS c r)) := by
  intro K d₁ d₂ φ₁ φ₂
  refine mem_topology_of_hasChartHomToAffineChartDiagram B S hS c r K _ fun {K'} n hK' ↦ ?_
  exact ⟨⟨K', hK'⟩, 𝟙 K', ObjectProperty.homMk (n ≫ φ₁), ObjectProperty.homMk (n ≫ φ₂),
    Category.id_comp _, Category.id_comp _⟩

/-- **The inclusion of the charts admitting a chart morphism to an affine chart diagram has
locally connected factorizations**, being the zigzag form of
`AlgebraicGeometry.Space.hasConnectedLocalFactorizations_hasChartHomToAffineChartDiagram`. -/
theorem hasLocallyConnectedFactorizations_hasChartHomToAffineChartDiagram (c : X ⟶ W)
    (r : W ⟶ W'') :
    Stacks.Sites.HasLocallyConnectedFactorizations (SmallEtale.topology B S hS X.1)
      (ObjectProperty.ι (HasChartHomToAffineChartDiagram B S hS c r)) :=
  Stacks.Sites.hasLocallyConnectedFactorizations_of_hasConnectedLocalFactorizations
    (hasConnectedLocalFactorizations_hasChartHomToAffineChartDiagram B S hS c r)

/-! ### The section over a chart carrying a chart morphism to an affine chart diagram -/

variable (Z : ClosedSubspaces B S hS X.1)

/-- **Over an étale chart of `X` admitting a chart morphism over `c` to an affine chart of `W`
carrying an affine chart diagram over `r`, the datum `a` has one section of `W`**, which

* is a lift of the given morphism on `Z` along the thickening, by the hypothesis `hlift`;
* is computed by the morphism of the site attached to `a` at *any* affine chart of `W` and any
  index above it, restricted along any morphism of charts of `X`, by
  `AlgebraicGeometry.Space.yoneda_map_thickeningLiftChartSiteHom_eq`;
* restricts, along any morphism of charts of `X`, to any section of a smaller chart computed the
  same way.

The three clauses are exactly what the gluing of these sections needs: the second is their
well-definedness and the third their compatibility with restriction.  They are stated together
because all three are read off one and the same morphism of the site, the one
`AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom_of_hasAffineChartDiagram` attaches to
the chart diagram the chart carries. -/
theorem exists_chartLiftSection {Bas : AlgebraicSpaces B S hS}
    (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c) (r : W ⟶ W'')
    (hbase : ∀ (V : SmallEtale B S hS W.1)
        (s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj (op V))),
      a.hom.app (op V) ((structureSharpRingInverseImage B S hS r).hom.app (op V) s) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op V)
          ((structureSharpRingInverseImage B S hS r).hom.app (op V) s))
    (p : X ⟶ Bas) (qb : W ⟶ Bas) {Zs : Subfunctor X.1} (az : Zs.toFunctor ⟶ W.1)
    (hlift : ∀ (V : SmallEtale B S hS W.1)
      [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
      (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
      (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
        (SmallEtale.toOver B S hS W.1).obj V),
      HasAffineChartDiagram B S hS r V →
      (BigFppfOver.toScheme B S hS).map ψ = thickeningLiftChartHom B S hS Z hZ c a V j →
      IsChartLift B S hS p qb az j.right.unop (yoneda.map ψ ≫ V.1.hom))
    (K : SmallEtale B S hS X.1) (hK : HasChartHomToAffineChartDiagram B S hS c r K) :
    ∃ s : yoneda.obj ((SmallEtale.toOver B S hS X.1).obj K) ⟶ W.1,
      IsChartLift B S hS p qb az K s ∧
      (∀ (V : SmallEtale B S hS W.1)
          [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
          (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
          (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
            (SmallEtale.toOver B S hS W.1).obj V) (n : K ⟶ j.right.unop),
        (BigFppfOver.toScheme B S hS).map ψ = thickeningLiftChartHom B S hS Z hZ c a V j →
        yoneda.map ((SmallEtale.toOver B S hS X.1).map n) ≫ yoneda.map ψ ≫ V.1.hom = s) ∧
      ∀ (K' : SmallEtale B S hS X.1) (m : K' ⟶ K)
        (s' : yoneda.obj ((SmallEtale.toOver B S hS X.1).obj K') ⟶ W.1),
        (∀ (V : SmallEtale B S hS W.1)
            [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
            (j : StructuredArrow (op (chartBaseChange B S hS c V))
              (comparisonFunctor B S hS X).op)
            (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
              (SmallEtale.toOver B S hS W.1).obj V) (n : K' ⟶ j.right.unop),
          (BigFppfOver.toScheme B S hS).map ψ = thickeningLiftChartHom B S hS Z hZ c a V j →
          yoneda.map ((SmallEtale.toOver B S hS X.1).map n) ≫ yoneda.map ψ ≫ V.1.hom = s') →
        yoneda.map ((SmallEtale.toOver B S hS X.1).map m) ≫ s = s' := by
  obtain ⟨V₀, q₀, hq₀, hV₀⟩ := hK
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS W.1).obj V₀)) := hV₀.1
  obtain ⟨V₀', qq₀, hqq₀, hV₀'aff⟩ := hV₀.2
  set j₀ := indexOfChartDiagram B S hS c
    (⟨K, V₀, q₀, hq₀.symm⟩ : ChartDiagram B S hS X.1 W.1 c.hom) with hj₀
  obtain ⟨ψ₀, hψ₀⟩ := exists_thickeningLiftChartSiteHom_of_hasAffineChartDiagram B S hS Z hZ c a
    r hbase V₀ V₀' qq₀ hqq₀.symm hV₀'aff j₀
  obtain ⟨n₀⟩ : Nonempty (K ⟶ j₀.right.unop) := ⟨𝟙 K⟩
  refine ⟨yoneda.map ((SmallEtale.toOver B S hS X.1).map n₀) ≫ yoneda.map ψ₀ ≫ V₀.1.hom,
    (hlift V₀ _ ψ₀ hV₀ hψ₀).restrict B S hS n₀, fun V _ j ψ n hψ ↦ ?_, fun K' m s' hs' ↦ ?_⟩
  · exact yoneda_map_thickeningLiftChartSiteHom_eq B S hS Z hZ c a r hbase j j₀ ψ hψ ψ₀ hψ₀ K n n₀
  · simpa using hs' V₀ _ ψ₀ (m ≫ n₀) hψ₀

/-! ### The glued morphism -/

/-- **The chartwise morphisms of the site attached to `a` are the restrictions of a single
morphism `X ⟶ W`.**

Let `a` be a solution of the lifting problem agreeing with the comorphism of `c` read through the
thickening on the functions read from `W''`, and suppose that over an affine chart of `W` with an
affine chart diagram over `r` the attached morphism of charts is a lift of `a₀ : Z ⟶ W` along the
thickening, that is a section of the sheaf of lifts of [Stacks Project, Tag 061D].  Then there is
a morphism `ε : X ⟶ W` over the base which restricts to `a₀` on `Z` and whose restriction to any
chart of `X` carrying an index over any affine chart of `W` is the attached morphism of charts.

The sections of `AlgebraicGeometry.Space.exists_chartLiftSection` are a compatible family on the
full subcategory of the charts admitting a chart morphism to an affine chart diagram; that
subcategory is cover-dense and its categories of factorizations are locally connected, so the
family is the restriction of a global section of the sheaf of lifts
(`Stacks.Sites.bijective_sectionsPrecomp_of_hasLocallyConnectedFactorizations`), and a global
section of the sheaf of lifts is the family of restrictions of one morphism
(`AlgebraicGeometry.Space.existsUnique_hom_of_isChartLift_family`).  Its restriction to an
arbitrary chart is computed by the chartwise sections above every point, and morphisms from the
charts of `X` into an algebraic space are a separated presheaf
(`AlgebraicGeometry.Space.eq_of_pointwise_agreement`). -/
theorem exists_hom_eq_thickeningLiftChartSiteHom {Bas : AlgebraicSpaces B S hS}
    (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c) (r : W ⟶ W'')
    (hbase : ∀ (V : SmallEtale B S hS W.1)
        (s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj (op V))),
      a.hom.app (op V) ((structureSharpRingInverseImage B S hS r).hom.app (op V) s) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op V)
          ((structureSharpRingInverseImage B S hS r).hom.app (op V) s))
    (p : X ⟶ Bas) (qb : W ⟶ Bas) {Zs : Subfunctor X.1} (az : Zs.toFunctor ⟶ W.1)
    (hlift : ∀ (V : SmallEtale B S hS W.1)
      [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
      (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
      (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
        (SmallEtale.toOver B S hS W.1).obj V),
      HasAffineChartDiagram B S hS r V →
      (BigFppfOver.toScheme B S hS).map ψ = thickeningLiftChartHom B S hS Z hZ c a V j →
      IsChartLift B S hS p qb az j.right.unop (yoneda.map ψ ≫ V.1.hom)) :
    ∃ ε : X.1 ⟶ W.1, ε ≫ qb.hom = p.hom ∧ Zs.ι ≫ ε = az ∧
      ∀ (V : SmallEtale B S hS W.1)
        [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
        (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
        (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
          (SmallEtale.toOver B S hS W.1).obj V),
        (BigFppfOver.toScheme B S hS).map ψ = thickeningLiftChartHom B S hS Z hZ c a V j →
        j.right.unop.1.hom ≫ ε = yoneda.map ψ ≫ V.1.hom := by
  classical
  choose sec hsecLift hsecEq hsecRestrict using
    fun d : ObjectProperty.FullSubcategory (HasChartHomToAffineChartDiagram B S hS c r) ↦
      exists_chartLiftSection B S hS Z hZ c a r hbase p qb az hlift d.obj d.property
  have hmem : ∀ d : ObjectProperty.FullSubcategory (HasChartHomToAffineChartDiagram B S hS c r),
      yonedaEquiv (sec d) ∈ (liftsSubfunctor B S hS p qb az).obj (op d.obj) := by
    intro d
    show IsChartLift B S hS p qb az d.obj (yonedaEquiv.symm (yonedaEquiv (sec d)))
    rw [Equiv.symm_apply_apply]
    exact hsecLift d
  have hprop : ∀ {d₁ d₂ : (ObjectProperty.FullSubcategory
        (HasChartHomToAffineChartDiagram B S hS c r))ᵒᵖ} (f : d₁ ⟶ d₂),
      ((ObjectProperty.ι (HasChartHomToAffineChartDiagram B S hS c r)).op ⋙
          (liftsSubfunctor B S hS p qb az).toFunctor).map f
            ⟨(yonedaEquiv (sec d₁.unop) :
              W.1.obj (op ((SmallEtale.toOver B S hS X.1).obj d₁.unop.obj))),
              hmem d₁.unop⟩ =
        ⟨(yonedaEquiv (sec d₂.unop) :
          W.1.obj (op ((SmallEtale.toOver B S hS X.1).obj d₂.unop.obj))), hmem d₂.unop⟩ := by
    intro d₁ d₂ f
    refine Subtype.ext ?_
    show W.1.map ((SmallEtale.toOver B S hS X.1).map f.unop.hom).op (yonedaEquiv (sec d₁.unop)) =
      yonedaEquiv (sec d₂.unop)
    rw [yonedaEquiv_naturality]
    exact congrArg yonedaEquiv
      (hsecRestrict d₁.unop d₂.unop.obj f.unop.hom (sec d₂.unop) (hsecEq d₂.unop))
  obtain ⟨α, hα⟩ := (Stacks.Sites.bijective_sectionsPrecomp_of_hasLocallyConnectedFactorizations
    (SmallEtale.topology B S hS X.1)
    ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_liftsSubfunctor B S hS p qb az))
    (hasLocalFactorizations_hasChartHomToAffineChartDiagram B S hS c r)
    (hasLocallyConnectedFactorizations_hasChartHomToAffineChartDiagram B S hS c r)).2
    ⟨fun d ↦ ⟨(yonedaEquiv (sec d.unop) :
      W.1.obj (op ((SmallEtale.toOver B S hS X.1).obj d.unop.obj))), hmem d.unop⟩, hprop⟩
  set β : ∀ Wc : SmallEtale B S hS X.1,
      yoneda.obj ((SmallEtale.toOver B S hS X.1).obj Wc) ⟶ W.1 :=
    fun Wc ↦ yonedaEquiv.symm ((α.val (op Wc)).1 :
      W.1.obj (op ((SmallEtale.toOver B S hS X.1).obj Wc))) with hβ
  have hβapp : ∀ Wc : SmallEtale B S hS X.1, yonedaEquiv (β Wc) = (α.val (op Wc)).1 :=
    fun Wc ↦ Equiv.apply_symm_apply _ _
  have hval : ∀ d : ObjectProperty.FullSubcategory
      (HasChartHomToAffineChartDiagram B S hS c r), β d.obj = sec d := by
    intro d
    refine yonedaEquiv.injective ?_
    rw [hβapp d.obj]
    exact congrArg Subtype.val (congrFun (Subtype.ext_iff.1 hα) (op d))
  have hcompat : ∀ {Wc Vc : SmallEtale B S hS X.1} (m : Vc ⟶ Wc),
      yoneda.map ((SmallEtale.toOver B S hS X.1).map m) ≫ β Wc = β Vc := by
    intro Wc Vc m
    have hα' : W.1.map ((SmallEtale.toOver B S hS X.1).map m).op (α.val (op Wc)).1 =
        (α.val (op Vc)).1 := Subtype.ext_iff.1 (α.property m.op)
    refine yonedaEquiv.injective ?_
    rw [← yonedaEquiv_naturality, hβapp, hα', hβapp]
  obtain ⟨ε, ⟨hall, hqbε, hresε⟩, -⟩ := existsUnique_hom_of_isChartLift_family B S hS p qb az
    β (fun Wc ↦ (α.val (op Wc)).2) hcompat
  refine ⟨ε, hqbε, hresε, fun V _ j ψ hψ ↦ ?_⟩
  refine eq_of_pointwise_agreement B S hS j.right.unop _ _ fun z ↦ ?_
  obtain ⟨K₃, n, hK₃, z', hz'⟩ :=
    exists_hasChartHomToAffineChartDiagram B S hS c r j.right.unop z
  refine ⟨K₃, n, ?_, z', hz'⟩
  have hw : yoneda.map ((SmallEtale.toOver B S hS X.1).map n) ≫ j.right.unop.1.hom =
      K₃.1.hom := CostructuredArrow.w _
  have hL : yoneda.map ((SmallEtale.toOver B S hS X.1).map n) ≫ j.right.unop.1.hom ≫ ε =
      sec ⟨K₃, hK₃⟩ := by
    rw [← Category.assoc, hw, hall K₃, hval ⟨K₃, hK₃⟩]
  exact hL.trans (hsecEq ⟨K₃, hK₃⟩ V j ψ n hψ).symm

end AlgebraicGeometry.Space

end
