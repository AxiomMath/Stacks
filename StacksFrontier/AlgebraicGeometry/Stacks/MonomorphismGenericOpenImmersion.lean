module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Stacks.Dimension
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.JacobsonAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismGenericOpenImmersionTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImageSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.PseudoCatenaryAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothMonomorphismOpenImmersion

/-!
# A monomorphism of stacks of equal dimension is generically an open immersion onto a component

**Stacks 0DS2** (Morphisms of Algebraic Stacks, Lemma 107.5.21) says the following. Let
`m : 𝒯 ⟶ 𝒳` be a monomorphism of algebraic stacks over `S` which is locally of finite type, with
`𝒳` Jacobson, pseudo-catenary and locally Noetherian; suppose `|𝒯|` is irreducible and `𝒯` has
finite dimension `d` in the sense of Stacks 0AFP, and suppose `𝒳` is reduced of dimension at
most `d`. Then some non-empty open substack `𝒱` of `𝒯` has `𝒱 ⟶ 𝒳` an open immersion which
identifies `𝒱` with an open subset of an irreducible component of `|𝒳|`.

## Main results

* `AlgebraicGeometry.Stack.exists_openSubstack_isOpenImmersion_subset_irreducibleComponent`
  is **Stacks 0DS2**.

## The conclusion

The open substack is `AlgebraicGeometry.Stack.OpenSubstack`, the notion of **Stacks 04YM**, so
`𝒱 ⟶ 𝒳` is the composite of its canonical inclusion with `m`, and "non-empty" is read on the set
of points `AlgebraicGeometry.Stack.OpenSubstack.pointSet` attached to it.

"Identifies `𝒱` with an open subset of an irreducible component of `𝒳`" is spelled in three
pieces. That `𝒱 ⟶ 𝒳` is an open immersion already makes `|𝒱| → |𝒳|` an open embedding, hence a
homeomorphism onto its range, which is the identification; the remaining content is that the
range lies inside an irreducible component `Z` of `|𝒳|` and is open in `|𝒳|`, and openness in
`|𝒳|` together with containment in `Z` gives openness in the subspace `Z`. The components are
`irreducibleComponents` of the space of points of **Stacks 04XG** and **Stacks 04XL**, whose
topology is `AlgebraicGeometry.Stack.pointTopology` (**Stacks 04Y8**).

The dimension is the one of **Stacks 0AFP**, `AlgebraicGeometry.Stack.dimension`, with values in
`EInt = WithBot (WithTop ℤ)`; a natural number `d` names the finite value the source gives `𝒯`,
and the bound on `𝒳` is an inequality in `EInt`.

## The carried input

The source's own hypotheses on `𝒯` are only that `|𝒯|` is irreducible and that its dimension is
`d`; that `𝒯` is Jacobson, pseudo-catenary and locally Noetherian the source derives from `𝒳`
being so and `m` being locally of finite type. Of those derived properties the statement needs
only local Noetherianity, because `AlgebraicGeometry.Stack.dimension` of `𝒯` is undefined
without it, and the derivation itself is not in this library, so `h𝒯N` appears as a hypothesis
for the statement to be formed at all.

**Stacks 05UP**, which turns the open part of a chart of `𝒯` into an open substack of `𝒯`, is
`AlgebraicGeometry.Stack.exists_openSubstack_isOpenImmersion_smooth_surjective` and its
construction `AlgebraicGeometry.Stack.openImageSubstack`, both unconditional; nothing about open
substacks is assumed here.

`hchart` is the chart-level conclusion of the source's own argument, the part of the proof that
the dimension hypotheses feed. Writing it out: there are an algebraic space `U'` with a smooth
1-morphism `f' : U' ⟶ 𝒯`, an open subspace `i : W ⟶ U'` with `|W|` non-empty, and `W ⟶ 𝒳` is
smooth. In the source `U'` is the base change `𝒯 ×_𝒳 U` of a smooth surjective chart `U ⟶ 𝒳` by
a reduced algebraic space, which is a scheme because `U' ⟶ U` is a locally finite type
monomorphism (**Stacks 0463** and **Stacks 0418**); `W` is the image in `U'` of the closed part
of the étale-local structure of the unramified morphism `U' ⟶ U` (**Stacks 04HJ**); and the
dimension inequality `dim_{u'}(U') ≥ dim_u(U)` of **Stacks 0DS3**, got from **Stacks 0DRN** and
**Stacks 0DRX**, forces that closed part to be an isomorphism, so that `W ⟶ U` is étale
(**Stacks 04N4** transporting pointwise dimension along étale maps) and `W ⟶ 𝒳`, being `W ⟶ U`
followed by the smooth chart, is smooth. Stacks 0DS3 is not in this library, so the chart-level
conclusion is carried.

## What is proved

Granted the above, what is proved is the source's last step, the passage from the chart to the
stack. Stacks 05UP applied to the smooth 1-morphism `W ⟶ 𝒯` produces the open substack `𝒱` of
`𝒯` covered by `|W|` together with a smooth surjective factorization `q : W ⟶ 𝒱` through it;
smoothness of `W ⟶ 𝒳` cancels along `q` (**Stacks 0AHD** on the source side) to give `𝒱 ⟶ 𝒳`
smooth, and `𝒱 ⟶ 𝒳` is a monomorphism by **Stacks 04ZY**, being `m` preceded by the open
immersion `𝒱 ⟶ 𝒯`, which is a monomorphism by **Stacks 0504**. A smooth monomorphism of
algebraic stacks is an open immersion (**Stacks 025G** for schemes, carried up to stacks in
`AlgebraicGeometry.Stack.AlgebraicStacks.isOpenImmersion_of_isSmooth_of_isMonomorphism`), which
is the first half of the conclusion. For the second, `|𝒱|` is a non-empty open subset of the
irreducible space `|𝒯|`, hence irreducible, so its image in `|𝒳|` is irreducible and therefore
contained in an irreducible component (**Stacks 004W**); and that image is open because
`𝒱 ⟶ 𝒳` is smooth (**Stacks 06R7**).

The locality at the target of the open immersions of algebraic spaces for the fppf precoverage,
which Stacks 05UP and the composition rule for open immersions ask for as an instance, is
**Stacks 041X** for the coarser fpqc precoverage together with
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`, and is discharged here rather than
assumed.

## References

* [Stacks Project, Tag 004W](https://stacks.math.columbia.edu/tag/004W)
* [Stacks Project, Tag 041X](https://stacks.math.columbia.edu/tag/041X)
* [Stacks Project, Tag 04ZY](https://stacks.math.columbia.edu/tag/04ZY)
* [Stacks Project, Tag 0504](https://stacks.math.columbia.edu/tag/0504)
* [Stacks Project, Tag 05UP](https://stacks.math.columbia.edu/tag/05UP)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 0AHD](https://stacks.math.columbia.edu/tag/0AHD)
* [Stacks Project, Tag 0DS2](https://stacks.math.columbia.edu/tag/0DS2)
* [Stacks Project, Tag 0DS3](https://stacks.math.columbia.edu/tag/0DS3)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DS2** (Morphisms of Algebraic Stacks, Lemma 107.5.21). Let `m : 𝒯 ⟶ 𝒳` be a
monomorphism of algebraic stacks over `S` which is locally of finite type, with `𝒳` Jacobson,
pseudo-catenary and locally Noetherian, with `|𝒯|` irreducible and `𝒯` of dimension `d` in the
sense of Stacks 0AFP, and with `𝒳` reduced of dimension at most `d`. Then there is a non-empty
open substack `𝒱` of `𝒯`, in the sense of **Stacks 04YM**, such that `𝒱 ⟶ 𝒳` is an open
immersion identifying `𝒱` with an open subset of an irreducible component of `|𝒳|`: its range
on points lies in an irreducible component `Z` and is open in `|𝒳|`, hence open in the subspace
`Z`, and the open immersion makes `|𝒱| → |𝒳|` a homeomorphism onto that range.

The source derives the Jacobson, pseudo-catenary and locally Noetherian properties of `𝒯` from
those of `𝒳`; of these only local Noetherianity is needed, and only so that the dimension of
`𝒯` is defined, and it is a hypothesis because the derivation is not in this library.

The dimension hypotheses enter the proof only through `hchart`: the source's argument on a
smooth surjective chart `U ⟶ 𝒳` by a reduced algebraic space, its base change `U' = 𝒯 ×_𝒳 U`,
and the étale-local structure of the unramified monomorphism `U' ⟶ U`, concludes that some
non-empty open `W ⊆ U'` has `W ⟶ U` étale and hence `W ⟶ 𝒳` smooth. That conclusion is carried,
Stacks 0DS3 being absent from this library; the module's "The carried input" names the tags it
rests on.

Granted it, the proof is the source's last step. Stacks 05UP
turns the smooth 1-morphism `W ⟶ 𝒯` into the open substack `𝒱` of `𝒯` covered by `|W|` with a
smooth surjective factorization `q : W ⟶ 𝒱` satisfying `q ≫ 𝒱.inclusion = W ⟶ 𝒯`; since
`q ≫ (𝒱.inclusion ≫ m)` is the smooth 1-morphism `W ⟶ 𝒳`, source-side cancellation of
smoothness along `q` gives `𝒱.inclusion ≫ m` smooth, and Stacks 04ZY makes it a monomorphism. A
smooth monomorphism of algebraic stacks is an open immersion. Finally `|𝒱|` is a non-empty open
subset of the irreducible `|𝒯|`, hence irreducible, so its continuous image in `|𝒳|` is
irreducible and lies in an irreducible component, and that image is open because `𝒱 ⟶ 𝒳` is
smooth.

This statement takes the chart-level conclusion `hchart` as a hypothesis, so it bears no tag.
**Stacks 0DS2** is registered on
`AlgebraicGeometry.Stack.exists_openSubstack_isOpenImmersion_subset_irreducibleComponent'`
below, which discharges it and is the form this library proves. -/
theorem exists_openSubstack_isOpenImmersion_subset_irreducibleComponent
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (m : 𝒯 ⟶ 𝒳)
    (hmono : AlgebraicStacks.IsMonomorphism B S hS m)
    (_hft : AlgebraicStacks.IsLocallyOfFiniteType B S hS m)
    (_h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (_h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒳N : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯N : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (d : ℕ) (_h𝒯dim : dimension B S hS 𝒯 h𝒯N = ((d : ℤ) : EInt))
    (_h𝒳red : IsReducedStack B S hS 𝒳)
    (_h𝒳dim : dimension B S hS 𝒳 h𝒳N ≤ ((d : ℤ) : EInt))
    (hchart : ∃ (U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU' : IsAlgebraicSpace B S hS U')
      (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B S hS W) (i : W ⟶ U')
      (f' : algebraicSpaceStack.{u, w} B S hS U' hU' ⟶ 𝒯),
      Space.IsOpenImmersion B S hS i ∧ AlgebraicStacks.IsSmooth B S hS f' ∧
        Nonempty (AlgebraicStacks.points B S hS (algebraicSpaceStack.{u, w} B S hS W hW)) ∧
          AlgebraicStacks.IsSmooth B S hS
            (algebraicSpaceStackMap.{u, w} B S hS hW hU' i ≫ f' ≫ m)) :
    ∃ 𝒱 : OpenSubstack 𝒯, (𝒱.pointSet B S hS).Nonempty ∧
      AlgebraicStacks.IsOpenImmersion B S hS (𝒱.inclusion ≫ m) ∧
        ∃ Z ∈ @irreducibleComponents _ (pointTopology B S hS 𝒳.val),
          Set.range (AlgebraicStacks.pointsMap B S hS (𝒱.inclusion ≫ m)) ⊆ Z ∧
            @IsOpen _ (pointTopology B S hS 𝒳.val)
              (Set.range (AlgebraicStacks.pointsMap B S hS (𝒱.inclusion ≫ m))) := by
  -- Stacks 041X for the fppf precoverage, from the fpqc one.
  let _h041X : (Space.openImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (L := Space.Topology.fpqc.precoverage.{u, u} B S hS)
      (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  obtain ⟨U', hU', W, hW, i, f', hi, hf', hWne, hW𝒳⟩ := hchart
  -- The smooth 1-morphism `W ⟶ 𝒯` cut out of the chart `U' ⟶ 𝒯` by the open part `W`.
  have hgsm : AlgebraicStacks.IsSmooth B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hW hU' i ≫ f') :=
    AlgebraicStacks.isSmooth_comp B S hS _ f'
      (isSmooth_algebraicSpaceStackMap_of_isOpenImmersion.{u, w} B S hS hW hU' hi) hf'
  -- Stacks 05UP: the open substack of `𝒯` that `|W|` covers.
  have hVne : ((openImageSubstack B S hS _ hgsm).pointSet B S hS).Nonempty := by
    rw [openImageSubstack_pointSet B S hS _ hgsm]
    exact ⟨_, Set.mem_range_self hWne.some⟩
  refine ⟨openImageSubstack B S hS _ hgsm, hVne, ?_⟩
  -- `𝒱 ⟶ 𝒳` is smooth, by source-side cancellation along the factorization of Stacks 05UP.
  have hq : openImageFactorization B S hS _ hgsm ≫
      (openImageSubstack B S hS _ hgsm).inclusion =
      algebraicSpaceStackMap.{u, w} B S hS hW hU' i ≫ f' := rfl
  have hWrep : IsRepresentableByAlgebraicSpace B S hS
      (algebraicSpaceStack.{u, w} B S hS W hW).val :=
    isRepresentableByAlgebraicSpace_fibredCategory B S hS W hW
  have hqrep : IsRepresentableByAlgebraicSpaces B S hS
      (openImageFactorization B S hS _ hgsm).hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS
      (openImageSubstack B S hS _ hgsm).toAlgebraicStack.property hWrep
      (openImageFactorization B S hS _ hgsm).hom
  have hcomp : AlgebraicStacks.IsSmooth B S hS
      (openImageFactorization B S hS _ hgsm ≫
        ((openImageSubstack B S hS _ hgsm).inclusion ≫ m)) := by
    rw [← Category.assoc, hq, Category.assoc]
    exact hW𝒳
  have hsm : AlgebraicStacks.IsSmooth B S hS
      ((openImageSubstack B S hS _ hgsm).inclusion ≫ m) :=
    AlgebraicStacks.isSmooth_of_comp_surjective B S hS _ _ hqrep
      (isSmooth_openImageFactorization B S hS _ hgsm hWrep)
      (isSurjective_openImageFactorization B S hS _ hgsm) hcomp
  -- `𝒱 ⟶ 𝒳` is a monomorphism: Stacks 0504 for the inclusion, then Stacks 04ZY.
  have hincMono : AlgebraicStacks.IsMonomorphism B S hS
      (openImageSubstack B S hS _ hgsm).inclusion :=
    AlgebraicStacks.isMonomorphism_of_isImmersion B S hS _
      ⟨(openImageSubstack B S hS _ hgsm).isOpenImmersion.1, fun U y hy F hF he =>
        Space.isImmersion_of_isOpenImmersion B S hS
          ((openImageSubstack B S hS _ hgsm).isOpenImmersion.2 U y hy F hF he)⟩
  -- A smooth monomorphism of algebraic stacks is an open immersion.
  have hoi : AlgebraicStacks.IsOpenImmersion B S hS
      ((openImageSubstack B S hS _ hgsm).inclusion ≫ m) :=
    AlgebraicStacks.isOpenImmersion_of_isSmooth_of_isMonomorphism B S hS _ hsm
      (AlgebraicStacks.isMonomorphism_comp B S hS _ m hincMono hmono)
  refine ⟨hoi, ?_⟩
  -- The range on points is open, and irreducible because `|𝒯|` is.
  have hopen := isOpen_range_pointsMap_of_isSmooth B S hS _ hsm
  let _ := pointTopology B S hS 𝒯.val
  let _ := pointTopology B S hS 𝒳.val
  have hVopen : IsOpen (Set.range (AlgebraicStacks.pointsMap B S hS
      (openImageSubstack B S hS _ hgsm).inclusion)) := by
    rw [← OpenSubstack.pointSet, openImageSubstack_pointSet B S hS _ hgsm]
    exact isOpen_range_pointsMap_of_isSmooth B S hS _ hgsm
  have hVirr : IsIrreducible (Set.range (AlgebraicStacks.pointsMap B S hS
      (openImageSubstack B S hS _ hgsm).inclusion)) :=
    ⟨hVne, (IrreducibleSpace.isIrreducible_univ _).isPreirreducible.open_subset hVopen
      (Set.subset_univ _)⟩
  have hrange : Set.range (AlgebraicStacks.pointsMap B S hS
      ((openImageSubstack B S hS _ hgsm).inclusion ≫ m)) =
      AlgebraicStacks.pointsMap B S hS m ''
        Set.range (AlgebraicStacks.pointsMap B S hS
          (openImageSubstack B S hS _ hgsm).inclusion) := by
    rw [AlgebraicStacks.pointsMap_comp, Set.range_comp]
  obtain ⟨Z, hZ, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (hrange ▸ hVirr.image _ (Continuous.continuousOn
      (continuous_pointsMap B S hS 𝒯.val 𝒳.val m.hom.hom)))
  exact ⟨Z, hZ, hsub, hopen⟩

/-- **Stacks 0DS2** (Morphisms of Algebraic Stacks, Lemma 107.5.21), with every input
discharged. Let `m : 𝒯 ⟶ 𝒳` be a
monomorphism of algebraic stacks over `S` which is locally of finite type, with `𝒳` Jacobson,
pseudo-catenary and locally Noetherian, with `|𝒯|` irreducible and `𝒯` of dimension `d` in the
sense of Stacks 0AFP, and with `𝒳` reduced of dimension at most `d`. Then there is a non-empty
open substack `𝒱` of `𝒯`, in the sense of **Stacks 04YM**, such that `𝒱 ⟶ 𝒳` is an open
immersion identifying `𝒱` with an open subset of an irreducible component of `|𝒳|`: its range
on points lies in an irreducible component `Z` and is open in `|𝒳|`, hence open in the subspace
`Z`, and the open immersion makes `|𝒱| → |𝒳|` a homeomorphism onto that range.

The source derives the Jacobson, pseudo-catenary and locally Noetherian properties of `𝒯` from
those of `𝒳`; of these only local Noetherianity is needed, and only so that the dimension of
`𝒯` is defined, and it is supplied in the statement of `h𝒯dim` by **Stacks 06R6** rather than
assumed.

The dimension hypotheses enter the proof only through the chart-level conclusion
`AlgebraicGeometry.Stack.exists_chart_openSubspace_isSmooth`: the source's argument on a smooth
surjective chart `U ⟶ 𝒳` by a reduced algebraic space, its base change `U' = 𝒯 ×_𝒳 U`, and the
étale-local structure of the unramified monomorphism `U' ⟶ U`, concludes that some non-empty open
`W ⊆ U'` has `W ⟶ U` étale and hence `W ⟶ 𝒳` smooth. The module's "The chart" says where that is
proved.

The rest, and the content of this module, is the source's last step. Stacks 05UP
turns the smooth 1-morphism `W ⟶ 𝒯` into the open substack `𝒱` of `𝒯` covered by `|W|` with a
smooth surjective factorization `q : W ⟶ 𝒱` satisfying `q ≫ 𝒱.inclusion = W ⟶ 𝒯`; since
`q ≫ (𝒱.inclusion ≫ m)` is the smooth 1-morphism `W ⟶ 𝒳`, source-side cancellation of
smoothness along `q` gives `𝒱.inclusion ≫ m` smooth, and Stacks 04ZY makes it a monomorphism. A
smooth monomorphism of algebraic stacks is an open immersion. Finally `|𝒱|` is a non-empty open
subset of the irreducible `|𝒯|`, hence irreducible, so its continuous image in `|𝒳|` is
irreducible and lies in an irreducible component, and that image is open because `𝒱 ⟶ 𝒳` is
smooth. -/
@[stacks 0DS2]
theorem exists_openSubstack_isOpenImmersion_subset_irreducibleComponent'
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (m : 𝒯 ⟶ 𝒳)
    (hmono : AlgebraicStacks.IsMonomorphism B S hS m)
    (hft : AlgebraicStacks.IsLocallyOfFiniteType B S hS m)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒳N : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (d : ℕ) (h𝒯dim : dimension B S hS 𝒯
      (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft h𝒳N) =
      ((d : ℤ) : EInt))
    (h𝒳red : IsReducedStack B S hS 𝒳)
    (h𝒳dim : dimension B S hS 𝒳 h𝒳N ≤ ((d : ℤ) : EInt)) :
    ∃ 𝒱 : OpenSubstack 𝒯, (𝒱.pointSet B S hS).Nonempty ∧
      AlgebraicStacks.IsOpenImmersion B S hS (𝒱.inclusion ≫ m) ∧
        ∃ Z ∈ @irreducibleComponents _ (pointTopology B S hS 𝒳.val),
          Set.range (AlgebraicStacks.pointsMap B S hS (𝒱.inclusion ≫ m)) ⊆ Z ∧
            @IsOpen _ (pointTopology B S hS 𝒳.val)
              (Set.range (AlgebraicStacks.pointsMap B S hS (𝒱.inclusion ≫ m))) := by
  exact exists_openSubstack_isOpenImmersion_subset_irreducibleComponent B S hS m hmono
    hft h𝒳Jacobson h𝒳Catenary h𝒳N
    (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft h𝒳N)
    h𝒯Irreducible d h𝒯dim h𝒳red h𝒳dim
    (exists_chart_openSubspace_isSmooth.{u, w} B S hS m hmono hft h𝒳Jacobson h𝒳Catenary h𝒳N
      h𝒯Irreducible d h𝒯dim h𝒳red h𝒳dim)

end AlgebraicGeometry.Stack

end
