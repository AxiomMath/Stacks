module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.CoproductChartPropertyDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.CoproductOneMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationTheorem
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsSurjectivityCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiDMChartAtFiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFlatCoverDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationSmallerBaseDMAndSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# The presentation theorems for DM and quasi-DM algebraic stacks (Stacks 06N3, 06MF)

**Stacks 06N3.** An algebraic stack is DM if and only if it is Deligne–Mumford, if and only if
there is a scheme with a surjective étale 1-morphism to it.

**Stacks 06MF.** An algebraic stack is quasi-DM if and only if there is a scheme with a
surjective, flat, locally finitely presented, locally quasi-finite 1-morphism to it.

Conditions (2) and (3) of Stacks 06N3 are the same condition here:
`AlgebraicGeometry.Stack.IsDeligneMumfordStack` (Stacks 03YO) is the existence of a 1-morphism
from a scheme of the site which is representable by algebraic spaces, surjective and étale.

This file proves both implications of Stacks 06MF and the implication (2) ⟹ (1) of Stacks 06N3,
and reduces the implication (1) ⟹ (2) of Stacks 06N3 to the chart construction
`AlgebraicGeometry.Stack.ExistsEtaleChartFamilyOfIsAbsolutelyDM`.

## Main definitions

* `AlgebraicGeometry.Stack.ExistsEtaleChartFamilyOfIsAbsolutelyDM`: every DM algebraic stack
  admits a family of relatively étale charts covering its finite type points, with its coproduct
  in the site.

## Main results

* `AlgebraicGeometry.Stack.isAbsolutelyDM_of_isDeligneMumfordStack`: the implication (2) ⟹ (1)
  of **Stacks 06N3**.
* `AlgebraicGeometry.Stack.isAbsolutelyQuasiDM_of_hasQuasiDMPresentation`: the implication
  (2) ⟹ (1) of **Stacks 06MF**.
* `AlgebraicGeometry.Stack.hasQuasiDMPresentation_iff_exists_finiteTypePoints_subset_range`:
  condition (2) of **Stacks 06MF** has only to be checked at the finite type points — a flat,
  locally finitely presented, locally quasi-finite chart whose image on points contains every
  finite type point is surjective.
* `AlgebraicGeometry.Stack.isAbsolutelyQuasiDM_of_finiteTypePoints_subset_range`: such a chart
  makes the stack quasi-DM.
* `AlgebraicGeometry.Stack.exists_isSurjective_stackMap_of_finiteTypePoints_subset_iUnion_range`:
  the coproduct of a family of flat, locally finitely presented charts whose images cover the
  finite type points of `𝒳` is a surjective 1-morphism `schemeStack (∐ᵢ Z i) ⟶ 𝒳` restricting
  to each of them.
* `AlgebraicGeometry.Stack.hasRelativeProperty_surjective_schemeStack_of_isSurjective`: such a
  chart is relatively surjective in the sense of Properties of Stacks, Section 04XB.
* `AlgebraicGeometry.Stack.isDeligneMumfordStack_of_forall_isRelativelyEtale`: a family of
  relatively étale charts covering the finite type points, with its coproduct in the site, makes
  `𝒳` a Deligne–Mumford stack; `...of_forall_size_le` and `...of_lt_cof` are the versions for a
  family of uniformly bounded size and for an index type below the cofinality of the cutoff.
* `AlgebraicGeometry.Stack.hasQuasiDMPresentation_of_forall_isLocallyQuasiFinite`: a family of
  flat, locally finitely presented, locally quasi-finite charts covering the finite type points,
  with its coproduct in the site, gives condition (2) of **Stacks 06MF**.
* `AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM_of_existsEtaleChartFamily`:
  the implication (1) ⟹ (2) of **Stacks 06N3** follows from the chart construction.
* `AlgebraicGeometry.Stack.hasQuasiDMPresentation_of_isAbsolutelyQuasiDM`: the implication
  (1) ⟹ (2) of **Stacks 06MF**.
* `AlgebraicGeometry.Stack.isAbsolutelyQuasiDM_iff_hasQuasiDMPresentation_unconditional`:
  **Stacks 06MF**.

## Implementation notes

The DM and quasi-DM properties are the *absolute* ones of **Stacks 050D**, parts (5) and (6); the
ambient big fppf site must therefore contain the terminal scheme, which is the hypothesis `hZ`.

A scheme of the site is read as an algebraic stack by `AlgebraicGeometry.Stack.schemeStack`.
Local quasi-finiteness of the chart is `AlgebraicGeometry.Stack.IsLocallyQuasiFinite`, the
Section 04XB notion, not the stack-level `...AlgebraicStacks.IsLocallyQuasiFinite` of
**Stacks 06PU**, because the source's condition is a condition on the chart as a representable
1-morphism.

## References

* [Stacks Project, Tag 03YO](https://stacks.math.columbia.edu/tag/03YO)
* [Stacks Project, Tag 0461](https://stacks.math.columbia.edu/tag/0461)
* [Stacks Project, Tag 04NQ](https://stacks.math.columbia.edu/tag/04NQ)
* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 0505](https://stacks.math.columbia.edu/tag/0505)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 06CR](https://stacks.math.columbia.edu/tag/06CR)
* [Stacks Project, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FF](https://stacks.math.columbia.edu/tag/06FF)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
* [Stacks Project, Tag 06FK](https://stacks.math.columbia.edu/tag/06FK)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06G2](https://stacks.math.columbia.edu/tag/06G2)
* [Stacks Project, Tag 06G3](https://stacks.math.columbia.edu/tag/06G3)
* [Stacks Project, Tag 06LQ](https://stacks.math.columbia.edu/tag/06LQ)
* [Stacks Project, Tag 06LU](https://stacks.math.columbia.edu/tag/06LU)
* [Stacks Project, Tag 06LW](https://stacks.math.columbia.edu/tag/06LW)
* [Stacks Project, Tag 06LZ](https://stacks.math.columbia.edu/tag/06LZ)
* [Stacks Project, Tag 06M1](https://stacks.math.columbia.edu/tag/06M1)
* [Stacks Project, Tag 06M3](https://stacks.math.columbia.edu/tag/06M3)
* [Stacks Project, Tag 06M5](https://stacks.math.columbia.edu/tag/06M5)
* [Stacks Project, Tag 06MB](https://stacks.math.columbia.edu/tag/06MB)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 06ME](https://stacks.math.columbia.edu/tag/06ME)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 06MM](https://stacks.math.columbia.edu/tag/06MM)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06MU](https://stacks.math.columbia.edu/tag/06MU)
* [Stacks Project, Tag 06MX](https://stacks.math.columbia.edu/tag/06MX)
* [Stacks Project, Tag 06N0](https://stacks.math.columbia.edu/tag/06N0)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A surjective 1-morphism from a scheme of the site to an algebraic stack is relatively
surjective**, in the longhand form of Properties of Stacks, Section 04XB that
`AlgebraicGeometry.Stack.IsDeligneMumfordStack` asks of its chart. -/
theorem hasRelativeProperty_surjective_schemeStack_of_isSurjective
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {W : BigFppfOver B S hS}
    (g : schemeStack.{u, w} B S hS W ⟶ 𝒳) (hg : IsSurjective B S hS g) :
    HasRelativeProperty B S hS (Space.surjectiveMorphismProperty B S hS) g.hom
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property
        (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W) g.hom) :=
  (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS g
    (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W) g.hom)).1 hg

/-- If `g` restricts up to 2-isomorphism to each `f i`, then `|g|` hits all the points hit by
some `|f i|`. -/
private theorem iUnion_range_pointsMap_subset_of_comp_iso
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {I : Type u} {Z : I → BigFppfOver B S hS}
    {W : BigFppfOver B S hS} (g : schemeStack.{u, w} B S hS W ⟶ 𝒳) {j : ∀ i, Z i ⟶ W}
    (f : ∀ i, schemeStack.{u, w} B S hS (Z i) ⟶ 𝒳)
    (hg : ∀ i, Nonempty (schemeStackMap.{u, w} B S hS (j i) ≫ g ≅ f i)) :
    (⋃ i, Set.range (AlgebraicStacks.pointsMap B S hS (f i))) ⊆
      Set.range (AlgebraicStacks.pointsMap B S hS g) := by
  refine Set.iUnion_subset fun i => ?_
  obtain ⟨e⟩ := hg i
  rw [← AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS e.hom, AlgebraicStacks.pointsMap_comp]
  exact Set.range_comp_subset_range _ _

/-- **The chart assembled out of charts at the finite type points is surjective.** Let `𝒳` be an
algebraic stack, let `Z : I → BigFppfOver B S hS` be a family of schemes of the site indexed by a
type below the cofinality of the site's size cutoff, and let `f i : schemeStack (Z i) ⟶ 𝒳` be a
family of 1-morphisms, each flat and locally of finite presentation, such that every finite type
point of `𝒳` lies in the image of some `|f i|`. Then the coproduct `W = ∐ᵢ Z i` of the family,
which is again a scheme of the site, carries a 1-morphism `g : schemeStack W ⟶ 𝒳` restricting up
to 2-isomorphism to each `f i` and **surjective**. -/
theorem exists_isSurjective_stackMap_of_finiteTypePoints_subset_iUnion_range
    (𝒳 : AlgebraicStacks.{u, w} B S hS) {I : Type u}
    (hI : Cardinal.mk I < B.cutoff.ord.cof) (Z : I → BigFppfOver B S hS)
    (f : ∀ i, schemeStack.{u, w} B S hS (Z i) ⟶ 𝒳)
    (hflat : ∀ i, AlgebraicStacks.IsFlat B S hS (f i))
    (hlfp : ∀ i, AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (f i))
    (hft : finiteTypePoints B S hS 𝒳 ⊆
      ⋃ i, Set.range (AlgebraicStacks.pointsMap B S hS (f i))) :
    ∃ (W : BigFppfOver B S hS) (g : schemeStack.{u, w} B S hS W ⟶ 𝒳),
      (∀ i, ∃ j : Z i ⟶ W, Nonempty (schemeStackMap.{u, w} B S hS j ≫ g ≅ f i)) ∧
        IsSurjective B S hS g := by
  let := pointTopology B S hS 𝒳.val
  obtain ⟨g, hg⟩ := exists_stackMap_comp_iso_sigmaOver_of_lt_cof.{u, w} B S hS hI Z f
  refine ⟨_, g, fun i => ⟨_, hg i⟩, ?_⟩
  have hopen : IsOpen (⋃ i, Set.range (AlgebraicStacks.pointsMap B S hS (f i))) := by
    refine isOpen_iUnion fun i => ?_
    let := pointTopology B S hS (schemeStack.{u, w} B S hS (Z i)).val
    exact (AlgebraicStacks.isOpenMap_pointsMap.{u, w} B S hS (f i) (hflat i)
      (hlfp i)).isOpen_range
  intro x
  exact iUnion_range_pointsMap_subset_of_comp_iso B S hS g f hg
    (eq_univ_of_finiteTypePoints_subset.{u, w} B S hS 𝒳 _ hopen hft ▸ Set.mem_univ x)

/-- A 1-morphism from a scheme of the site, representable by algebraic spaces and relatively
étale, is flat and locally of finite presentation. -/
private theorem isFlat_and_isLocallyOfFinitePresentation_of_relativeProperty_etale
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {W : BigFppfOver B S hS}
    (g : schemeStack.{u, w} B S hS W ⟶ 𝒳)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom)
    (hEt : RelativeProperty B S hS (Space.etaleMorphisms B S hS) g.hom) :
    AlgebraicStacks.IsFlat B S hS g ∧ AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g := by
  have hflatBC : (spaceProperty B S hS
      (fun _ _ k => Space.IsFlat B S hS k)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  have hflatLT : (spaceProperty B S hS
      (fun _ _ k => Space.IsFlat B S hS k)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.isFlat_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have hlfpBC : (spaceProperty B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  have hlfpLT : (spaceProperty B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isLocallyOfFinitePresentation_isLocalAtTarget_fppf.{u, u} B S hS
  refine ⟨(AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram.{u, w} B S hS g).2
      (hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
        (fun _ _ k => Space.IsFlat B S hS k) 𝒳.property g.hom hrep
        (fun V y hy F hF he => Space.isFlat_of_isEtale B S hS (hEt V y hy F hF he))),
    hasPropertyOnEverySmoothDiagram_of_hasPropertyOnSomeSmoothDiagram B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) g.hom
      (hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
        (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k) 𝒳.property g.hom hrep
        (fun V y hy F hF he =>
          Space.isLocallyOfFinitePresentation_of_isEtale B S hS (hEt V y hy F hF he)))⟩

/-- **Relatively étale charts covering the finite type points make a Deligne–Mumford stack.**
Let `𝒳` be an algebraic stack and let `f i : schemeStack (Z i) ⟶ 𝒳` be a family of *relatively
étale* 1-morphisms out of schemes of the site, whose coproduct `W = ∐ᵢ Z i` is again a scheme of
the site and whose images on points cover the finite type points of `𝒳`. Then `𝒳` is a
Deligne–Mumford stack: `W` carries a 1-morphism `schemeStack W ⟶ 𝒳` which is representable by
algebraic spaces, relatively surjective and relatively étale — the presentation **Stacks 03YO**
asks for. -/
theorem isDeligneMumfordStack_of_forall_isRelativelyEtale
    (𝒳 : AlgebraicStacks.{u, w} B S hS) {I : Type u} (Z : I → BigFppfOver B S hS)
    (hsum : B.Contains (∐ fun i => (BigFppfOver.toScheme B S hS).obj (Z i)))
    (f : ∀ i, schemeStack.{u, w} B S hS (Z i) ⟶ 𝒳)
    (hetale : ∀ i, IsRelativelyEtale B S hS (f i).hom)
    (hft : finiteTypePoints B S hS 𝒳 ⊆
      ⋃ i, Set.range (AlgebraicStacks.pointsMap B S hS (f i))) :
    IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val := by
  let := pointTopology B S hS 𝒳.val
  have hirep : ∀ i, IsRepresentableByAlgebraicSpaces B S hS (f i).hom.hom := fun i =>
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS (Z i)) (f i).hom
  have hEt : ∀ i, RelativeProperty B S hS (Space.etaleMorphisms B S hS) (f i).hom :=
    fun i => (hetale i).elim fun _ h => h
  have hfl := fun i => isFlat_and_isLocallyOfFinitePresentation_of_relativeProperty_etale
    B S hS (f i) (hirep i) (hEt i)
  obtain ⟨g, hg⟩ := exists_stackMap_comp_iso_sigmaOver.{u, w, u} B S hS Z hsum f
  have hWcolim := BigFppfOver.isColimit_toScheme_sigmaOver B S hS Z hsum
  have hgEt : IsRelativelyEtale B S hS g.hom :=
    isRelativelyEtale_of_isColimit_of_forall_isRelativelyEtale.{u, w} B S hS Z _ _ hWcolim g f
      hg hetale
  have hgFlat : AlgebraicStacks.IsFlat B S hS g :=
    AlgebraicStacks.isFlat_of_isColimit_of_forall_isFlat.{u, w} B S hS Z _ _ hWcolim g f hg
      fun i => (hfl i).1
  have hgLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g :=
    AlgebraicStacks.isLocallyOfFinitePresentation_of_isColimit_of_forall.{u, w} B S hS Z _ _
      hWcolim g f hg fun i => (hfl i).2
  have hgSurj : IsSurjective B S hS g :=
    isSurjective_of_finiteTypePoints_subset_range.{u, w} B S hS g hgFlat hgLfp
      (hft.trans (iUnion_range_pointsMap_subset_of_comp_iso B S hS g f hg))
  refine ⟨𝒳.property, 𝒳.val.property, _, g.hom,
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS _) g.hom,
    fun V y hy F hF he => ⟨?_, ?_⟩⟩
  · exact hasRelativeProperty_surjective_schemeStack_of_isSurjective.{u, w, u} B S hS g hgSurj
      V y hy F hF he
  · exact (hgEt.elim fun _ h => h) V y hy F hF he

/-- **Relatively étale charts of uniformly bounded size covering the finite type points make a
Deligne–Mumford stack.** Let `f i : schemeStack (Z i) ⟶ 𝒳` be a family of relatively étale
1-morphisms out of schemes of the site, indexed by a type of cardinality below the site's cutoff,
whose members have size at most a fixed cardinal `c` below the cutoff and whose images on points
cover the finite type points of `𝒳`. Then `𝒳` is a Deligne–Mumford stack. -/
theorem isDeligneMumfordStack_of_forall_isRelativelyEtale_of_forall_size_le
    (𝒳 : AlgebraicStacks.{u, w} B S hS) {I : Type u} (hI : Cardinal.mk I < B.cutoff)
    (Z : I → BigFppfOver B S hS) (c : Cardinal.{u}) (hc : c < B.cutoff)
    (hsize : ∀ i, ((BigFppfOver.toScheme B S hS).obj (Z i)).size ≤ c)
    (f : ∀ i, schemeStack.{u, w} B S hS (Z i) ⟶ 𝒳)
    (hetale : ∀ i, IsRelativelyEtale B S hS (f i).hom)
    (hft : finiteTypePoints B S hS 𝒳 ⊆
      ⋃ i, Set.range (AlgebraicStacks.pointsMap B S hS (f i))) :
    IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val :=
  isDeligneMumfordStack_of_forall_isRelativelyEtale.{u, w} B S hS 𝒳 Z
    (B.contains_sigma_of_forall_size_le hI _ c hc hsize) f hetale hft

/-- **Relatively étale charts covering the finite type points, indexed below the cofinality of
the site's cutoff, make a Deligne–Mumford stack.** Let `f i : schemeStack (Z i) ⟶ 𝒳` be a family
of relatively étale 1-morphisms out of schemes of the site, indexed by a type of cardinality below
the cofinality of the site's cutoff, whose images on points cover the finite type points of `𝒳`.
Then `𝒳` is a Deligne–Mumford stack. -/
theorem isDeligneMumfordStack_of_forall_isRelativelyEtale_of_lt_cof
    (𝒳 : AlgebraicStacks.{u, w} B S hS) {I : Type u}
    (hI : Cardinal.mk I < B.cutoff.ord.cof) (Z : I → BigFppfOver B S hS)
    (f : ∀ i, schemeStack.{u, w} B S hS (Z i) ⟶ 𝒳)
    (hetale : ∀ i, IsRelativelyEtale B S hS (f i).hom)
    (hft : finiteTypePoints B S hS 𝒳 ⊆
      ⋃ i, Set.range (AlgebraicStacks.pointsMap B S hS (f i))) :
    IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val :=
  isDeligneMumfordStack_of_forall_isRelativelyEtale.{u, w} B S hS 𝒳 Z
    (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2) f hetale hft

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The chart construction of Stacks 06N3.** Every DM algebraic stack admits a family of
relatively étale charts by schemes of the site whose images cover its finite type points and
whose coproduct is again a scheme of the site. -/
abbrev ExistsEtaleChartFamilyOfIsAbsolutelyDM : Prop :=
  ∀ 𝒳 : AlgebraicStacks.{u, w} B S hS, AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒳 →
    ∃ (I : Type u) (Z : I → BigFppfOver B S hS)
      (_hsum : B.Contains (∐ fun i => (BigFppfOver.toScheme B S hS).obj (Z i)))
      (f : ∀ i, schemeStack.{u, w} B S hS (Z i) ⟶ 𝒳),
      (∀ i, IsRelativelyEtale B S hS (f i).hom) ∧
        finiteTypePoints B S hS 𝒳 ⊆
          ⋃ i, Set.range (AlgebraicStacks.pointsMap B S hS (f i))

/-- **The substantial direction of Stacks 06N3 follows from the chart construction alone.** Given
`AlgebraicGeometry.Stack.ExistsEtaleChartFamilyOfIsAbsolutelyDM` — étale charts at the finite
type points, with their coproduct in the site — every DM algebraic stack is Deligne–Mumford. -/
theorem existsEtalePresentationOfIsAbsolutelyDM_of_existsEtaleChartFamily
    (hcharts : ExistsEtaleChartFamilyOfIsAbsolutelyDM.{u, w} B S hS hZ) :
    ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS hZ := by
  intro 𝒳 h𝒳
  obtain ⟨I, Z, hsum, f, hetale, hft⟩ := hcharts 𝒳 h𝒳
  exact isDeligneMumfordStack_of_forall_isRelativelyEtale.{u, w} B S hS 𝒳 Z hsum f hetale hft

/-- A Deligne–Mumford algebraic stack is DM: the implication (2) ⟹ (1), equivalently (3) ⟹ (1),
these being the same condition here. -/
@[stacks 06N3 "the implication (2) => (1), equivalently (3) => (1), these being the same \
condition here: an algebraic stack admitting a surjective etale presentation by a scheme is DM"]
theorem isAbsolutelyDM_of_isDeligneMumfordStack (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val) :
    AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒳 := by
  obtain ⟨-, hfib, U, f, hfrep, hprop⟩ := h𝒳
  let g : schemeStack.{u, w} B S hS U ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom f
  have hUrep : IsRepresentableByAlgebraicSpace B S hS
      (schemeStack.{u, w} B S hS U).val :=
    isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U
  have hgrep : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom := hfrep
  have hunrBC : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  have hunrLT : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.isUnramified_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have hgSurj : IsSurjective B S hS g :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS g hgrep).mpr
      (fun V y hy F hF he => (hprop V y hy F hF he).1)
  obtain ⟨hgFlat, hgLfp⟩ := isFlat_and_isLocallyOfFinitePresentation_of_relativeProperty_etale
    B S hS g hgrep fun V y hy F hF he => (hprop V y hy F hF he).2
  exact AlgebraicStacks.isAbsolutelyDM_of_isUnramified_flatCover.{u, w} B S hS hZ g hUrep
    hgSurj hgFlat hgLfp
    (fun V y hy F hF he => Space.isUnramified_of_isEtale B S hS (hprop V y hy F hF he).2)

/-- An algebraic stack with a surjective, flat, locally finitely presented, locally quasi-finite
presentation by a scheme of the site is quasi-DM: the implication (2) ⟹ (1). -/
@[stacks 06MF "the implication (2) implies (1): a surjective, flat, locally finitely presented, \
locally quasi-finite presentation by a scheme of the site makes an algebraic stack quasi-DM"]
theorem isAbsolutelyQuasiDM_of_hasQuasiDMPresentation (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h : HasQuasiDMPresentation.{u, w} B S hS 𝒳) :
    AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳 := by
  obtain ⟨W, f, hSurj, hFlat, hLfp, hQf⟩ := h
  exact AlgebraicStacks.isAbsolutelyQuasiDM_of_isLocallyQuasiFinite_flatCover B S hS hZ f
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W) hSurj hFlat hLfp hQf

/-- **Condition (2) of Stacks 06MF has only to be checked at the finite type points.** An
algebraic stack `𝒳` has a quasi-DM presentation exactly when there is a scheme `W` of the site
and a 1-morphism `f : schemeStack W ⟶ 𝒳` which is flat, locally of finite presentation and
locally quasi-finite and whose image on points merely *contains every finite type point* of `𝒳`.
-/
theorem hasQuasiDMPresentation_iff_exists_finiteTypePoints_subset_range
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    HasQuasiDMPresentation.{u, w} B S hS 𝒳 ↔
      ∃ (W : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS W ⟶ 𝒳),
        AlgebraicStacks.IsFlat B S hS f ∧
        AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f ∧
        IsLocallyQuasiFinite B S hS f.hom ∧
        finiteTypePoints B S hS 𝒳 ⊆ Set.range (AlgebraicStacks.pointsMap B S hS f) := by
  constructor
  · rintro ⟨W, f, hSurj, hFlat, hLfp, hQf⟩
    exact ⟨W, f, hFlat, hLfp, hQf, fun x _ => hSurj x⟩
  · rintro ⟨W, f, hFlat, hLfp, hQf, hft⟩
    exact ⟨W, f, isSurjective_of_finiteTypePoints_subset_range.{u, w} B S hS f hFlat hLfp hft,
      hFlat, hLfp, hQf⟩

/-- **One chart meeting every finite type point makes an algebraic stack quasi-DM.** If a scheme
`W` of the site carries a 1-morphism `f : schemeStack W ⟶ 𝒳` which is flat, locally of finite
presentation and locally quasi-finite and whose image on points contains every finite type point
of `𝒳`, then `𝒳` is quasi-DM. -/
theorem isAbsolutelyQuasiDM_of_finiteTypePoints_subset_range
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (W : BigFppfOver B S hS)
    (f : schemeStack.{u, w} B S hS W ⟶ 𝒳)
    (hFlat : AlgebraicStacks.IsFlat B S hS f)
    (hLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hQf : IsLocallyQuasiFinite B S hS f.hom)
    (hft : finiteTypePoints B S hS 𝒳 ⊆ Set.range (AlgebraicStacks.pointsMap B S hS f)) :
    AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳 :=
  isAbsolutelyQuasiDM_of_hasQuasiDMPresentation.{u, w} B S hS hZ 𝒳
    ((hasQuasiDMPresentation_iff_exists_finiteTypePoints_subset_range.{u, w} B S hS 𝒳).2
      ⟨W, f, hFlat, hLfp, hQf, hft⟩)

/-- **Quasi-finite charts covering the finite type points give a quasi-DM presentation.** A
family of flat, locally finitely presented, locally quasi-finite charts by schemes of the site
whose images on points cover the finite type points of `𝒳`, and whose coproduct is again a scheme
of the site, assembles into condition (2) of **Stacks 06MF**. -/
theorem hasQuasiDMPresentation_of_forall_isLocallyQuasiFinite
    (𝒳 : AlgebraicStacks.{u, w} B S hS) {I : Type u} (Z : I → BigFppfOver B S hS)
    (hsum : B.Contains (∐ fun i => (BigFppfOver.toScheme B S hS).obj (Z i)))
    (f : ∀ i, schemeStack.{u, w} B S hS (Z i) ⟶ 𝒳)
    (hflat : ∀ i, AlgebraicStacks.IsFlat B S hS (f i))
    (hlfp : ∀ i, AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (f i))
    (hqf : ∀ i, IsLocallyQuasiFinite B S hS (f i).hom)
    (hft : finiteTypePoints B S hS 𝒳 ⊆
      ⋃ i, Set.range (AlgebraicStacks.pointsMap B S hS (f i))) :
    HasQuasiDMPresentation.{u, w} B S hS 𝒳 := by
  let := pointTopology B S hS 𝒳.val
  obtain ⟨g, hg⟩ := exists_stackMap_comp_iso_sigmaOver.{u, w, u} B S hS Z hsum f
  have hWcolim := BigFppfOver.isColimit_toScheme_sigmaOver B S hS Z hsum
  refine (hasQuasiDMPresentation_iff_exists_finiteTypePoints_subset_range.{u, w} B S hS 𝒳).2
    ⟨_, g,
      AlgebraicStacks.isFlat_of_isColimit_of_forall_isFlat.{u, w} B S hS Z _ _ hWcolim g f hg
        hflat,
      AlgebraicStacks.isLocallyOfFinitePresentation_of_isColimit_of_forall.{u, w} B S hS Z _ _
        hWcolim g f hg hlfp,
      isLocallyQuasiFinite_of_isColimit_of_forall_isLocallyQuasiFinite.{u, w} B S hS Z _ _
        hWcolim g f hg hqf,
      hft.trans (iUnion_range_pointsMap_subset_of_comp_iso B S hS g f hg)⟩

/-- **The substantial direction of Stacks 06MF, (1) ⟹ (2).** A quasi-DM algebraic stack admits a
surjective, flat, locally finitely presented, locally quasi-finite presentation by a scheme of
the site. -/
theorem hasQuasiDMPresentation_of_isAbsolutelyQuasiDM (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳) :
    HasQuasiDMPresentation.{u, w} B S hS 𝒳 := by
  classical
  have h𝒳' : IsQuasiDMOver B S hS 𝒳 :=
    AlgebraicStacks.isQuasiDMOver_of_isAbsolutelyQuasiDM B S hS hZ 𝒳 h𝒳
  obtain ⟨U₀, a₀, ha₀sm, ha₀surj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  let := pointTopology B S hS (schemeFibredCategory B S hS U₀)
  have hU₀ : ((BigFppfOver.toScheme B S hS).obj U₀).size < B.cutoff := U₀.left.2
  have hc : (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
      ((BigFppfOver.toScheme B S hS).obj U₀).size < B.cutoff :=
    B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit hU₀)
  have hI : Cardinal.mk {v : (BigFppfOver.toScheme B S hS).obj U₀ //
      IsFiniteTypePoint.{u, w} B S hS 𝒳 (AlgebraicStacks.pointsMap B S hS a₀
        ((pointsHomeomorphScheme B S hS U₀).symm v))} < B.cutoff :=
    (Cardinal.mk_subtype_le _).trans_lt
      (((BigFppfOver.toScheme B S hS).obj U₀).mk_le_two_pow_size.trans_lt
        (B.cutoff_isStrongPrelimit hU₀))
  choose Z f hflat hlfp hlqf hmem hsize using fun
      (i : {v : (BigFppfOver.toScheme B S hS).obj U₀ //
        IsFiniteTypePoint.{u, w} B S hS 𝒳 (AlgebraicStacks.pointsMap B S hS a₀
          ((pointsHomeomorphScheme B S hS U₀).symm v))}) =>
    exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart_at_finiteTypePoint.{u, w}
      B S hS 𝒳 h𝒳' U₀ a₀ ha₀sm ha₀surj _ i.2
  refine hasQuasiDMPresentation_of_forall_isLocallyQuasiFinite.{u, w} B S hS 𝒳 Z
    (B.contains_sigma_of_forall_size_le hI _ _ hc hsize) f hflat hlfp hlqf fun x hx => ?_
  obtain ⟨wx, hwx⟩ := ha₀surj x
  have hwmem : IsFiniteTypePoint.{u, w} B S hS 𝒳 (AlgebraicStacks.pointsMap B S hS a₀
      ((pointsHomeomorphScheme B S hS U₀).symm (pointsHomeomorphScheme B S hS U₀ wx))) := by
    rw [Homeomorph.symm_apply_apply, hwx]
    exact hx
  refine Set.mem_iUnion.2 ⟨⟨pointsHomeomorphScheme B S hS U₀ wx, hwmem⟩, ?_⟩
  have := hmem ⟨pointsHomeomorphScheme B S hS U₀ wx, hwmem⟩
  rwa [Homeomorph.symm_apply_apply, hwx] at this

/-- An algebraic stack is quasi-DM exactly when there is a scheme of the site with a surjective,
flat, locally finitely presented, locally quasi-finite 1-morphism to it. -/
@[stacks 06MF "the equivalence of (1) quasi-DM with (2) the existence of a surjective, flat,
  locally finitely presented, locally quasi-finite presentation by a scheme. BOTH implications
  are proved and nothing is carried. (2) implies (1) is Stacks 06MB part (2),
  isAbsolutelyQuasiDM_of_hasQuasiDMPresentation; (1) implies (2) is the structure theorem,
  hasQuasiDMPresentation_of_isAbsolutelyQuasiDM, whose local half is the chart of
  exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart_at_finiteTypePoint --
  the smooth chart of 06FX with a closed point over the finite type point, the charted
  self-intersection of 04ZP and 04SW, the identity point of 04XH, and the slice cut out by a
  regular sequence in the etale local ring of a fibre (06LC, 06MD, 06LW) shrunk to be locally
  quasi-finite by 06M3 and 06ME -- and whose assembly is
  hasQuasiDMPresentation_of_forall_isLocallyQuasiFinite: the 1-morphism out of the coproduct
  W = coprod_x Z_x, the descent of the three properties along the summand inclusions, and
  surjectivity from the corollary of 06G2. The coproduct lies in the site by
  contains_sigma_of_forall_size_le, which the uniform bound 2 ^ 2 ^ size U_0 on the charts
  supplies -- the finite type points need not be below the cofinality of the site's cutoff, so
  contains_sigma_of_lt_cof does not apply"]
theorem isAbsolutelyQuasiDM_iff_hasQuasiDMPresentation_unconditional
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳 ↔
      HasQuasiDMPresentation.{u, w} B S hS 𝒳 :=
  ⟨hasQuasiDMPresentation_of_isAbsolutelyQuasiDM.{u, w} B S hS hZ 𝒳,
    isAbsolutelyQuasiDM_of_hasQuasiDMPresentation.{u, w} B S hS hZ 𝒳⟩

end AlgebraicGeometry.Stack

end
