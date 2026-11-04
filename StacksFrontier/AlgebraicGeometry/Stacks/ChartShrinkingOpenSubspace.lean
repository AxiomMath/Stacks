module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingQuasiFiniteEtaleUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubspaceOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsAlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedDiagonalCriterion

/-!
# Stacks 06ME and Stacks 06N2 read on an open subspace of the chart

**Stacks 06ME** and **Stacks 06N2** conclude that, after replacing the algebraic space `U` by an
open *subspace* containing the image of the given point of the fibre, the 1-morphism `U ⟶ 𝒳` is
locally quasi-finite, respectively étale.
`StacksFrontier/AlgebraicGeometry/Stacks/ChartShrinkingQuasiFiniteEtale.lean` proves both with the
replacement read as an open *substack* `W` of the algebraic stack of `U`: the property it asserts
is a property of `W.inclusion ≫ f`. This file carries each of those two conclusions across to the
composite of `f` with the 1-morphism of **Stacks 0458** induced by an open subspace of `U`, which
is the source's own reading.

The passage from the substack to the subspace is
`AlgebraicGeometry.Stack.exists_isOpenSubspace_property_eq_essImage`: for an open substack `W` of
the algebraic stack of `U` it produces an open subspace `V ⊆ U` in the sense of **Stacks 02YU**,
part (2), whose induced 1-morphism `i : S_V ⟶ S_U` has `W` for its essential image and whose point
set is `|W|`. What this file adds is the transport of the property from `W.inclusion` to `i`.

## Main results

* `AlgebraicGeometry.Stack.isLocallyQuasiFinite_comp_of_eq_essImage` and
  `AlgebraicGeometry.Stack.isEtale_comp_of_eq_essImage`: the transport itself, at
  `𝒫 = ` locally quasi-finite and at `𝒫 = ` étale. If an immersion `i : 𝒴 ⟶ 𝒳` of algebraic
  stacks has essential image the full subcategory cut out by `P`, and `f : 𝒳 ⟶ 𝒵` composed with
  the inclusion of that full subcategory has `𝒫`, then `i ≫ f` has `𝒫`.
* `AlgebraicGeometry.Stack.exists_isOpenSubspace_isLocallyQuasiFinite`: the conclusion of
  **Stacks 06ME** read on an open subspace of `U`, at the intermediate condition of the source's
  own proof. The registration of Stacks 06ME at the source's own hypothesis `dim_z(F) = 0` is
  `AlgebraicGeometry.Stack.exists_isOpenSubspace_isLocallyQuasiFinite_of_dimensionAtPoint_eq_zero`
  of `StacksFrontier/AlgebraicGeometry/Stacks/FibreQuasiFiniteNearSubstack.lean`, which is this
  statement composed with
  `AlgebraicGeometry.Stack.fibreIsLocallyQuasiFiniteNear_of_dimensionAtPoint_eq_zero`.
* `AlgebraicGeometry.Stack.exists_isOpenSubspace_isEtale`: **Stacks 06N2** with the conclusion
  read on an open subspace of `U`.

## How the transport is proved

**Stacks 0506** factors an immersion `i` through the full subcategory cut out by its essential
image by a 1-morphism whose underlying functor is an equivalence of categories; that is
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_isEquivalence_to_essImage`, whose factoring
1-morphism is `AlgebraicGeometry.Stack.AlgebraicStacks.toEssImageBased`, whose equivalence is
`AlgebraicGeometry.Stack.AlgebraicStacks.isEquivalence_toEssImageBased` and whose 2-isomorphism is
`AlgebraicGeometry.Stack.AlgebraicStacks.toEssImageBasedSquareIso`. Those three named pieces are
used rather than the existential, so that nothing has to be re-chosen. Whiskering that
2-isomorphism with `f` gives a square of equivalences — on the right the identity, since `f`'s
target is not moved — and the 2-category of categories over the site being strict, the whiskered
square has the required type on the nose.

Across that square the relative property of **Stacks 03YK** transports by **Stacks 0457**,
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences`. Each of the two properties is read
through its identification with that relative property:

* local quasi-finiteness of **Stacks 06PU** against the relative notion of **Stacks 04XB** by
  `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_iff_isLocallyQuasiFinite_hom`,
  which holds for a 1-morphism representable by algebraic spaces and is used in both directions;
* étaleness of **Stacks 0CIL** against the relative notion by
  `AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_iff_relative` forwards — the
  universal étale-smooth diagram test of **Stacks 0CIF** agrees with the relative property for a
  representable 1-morphism, étaleness being étale-smooth local on the source-and-target by
  **Stacks 0CG3** — and by
  `AlgebraicGeometry.Stack.AlgebraicStacks.isEtale_of_isRelativelyEtale` backwards, which needs no
  locality: the Deligne–Mumford conjunct of Stacks 0CIL is **Stacks 050E** at the
  representability of `i ≫ f`.

Both representability witnesses are composites: `i` is representable because it is an immersion
and the inclusion of the essential image is representable by
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_essImageInclusion`, and
`f` is representable by hypothesis — at the two applications below because its source is the
algebraic stack of an algebraic space
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source`).

The equality of object properties is taken as a hypothesis on a bare property rather than on
`AlgebraicGeometry.Stack.OpenSubstack.property`, so that it can be substituted: the algebraicity
witness of the full subcategory occurs in the type of the inclusion, and substituting the equality
carries that witness along with it.

## Implementation notes

The two statements below are the source's conclusions and nothing is carried; they are proved from
`AlgebraicGeometry.Stack.exists_openSubstack_isLocallyQuasiFinite_unconditional` and
`AlgebraicGeometry.Stack.exists_openSubstack_isEtale_unconditional` with no hypothesis added. The
point-set
clause is the same point of `|U|`, transported along the identification of `|U|` with the point
space of the algebraic stack of `U`
(`AlgebraicGeometry.Stack.pointsHomeomorphSpace`): "containing `p(z)`" says that the image of
`p(z)` under that identification lies in the image of the point set of `V`.

These are not the full residue of **Stacks 06N3**. What the chart construction of that lemma needs
further of the open subspace `V` produced above is that it be a scheme of the site carrying a
monomorphism into the chart; that is not proved here but in
`StacksFrontier/AlgebraicGeometry/Spaces/OpenSubspaceSiteObject.lean`, as
`AlgebraicGeometry.Space.exists_siteObject_iso_mono_of_isOpenSubspace`, for a chart which is
representable — which the chart of **Stacks 06FX** is. The identification of the **Stacks 06MD**
slice is proved in
`StacksFrontier/AlgebraicGeometry/Stacks/ZeroLocusSliceSiteObject.lean`, as
`AlgebraicGeometry.Stack.exists_siteObject_iso_mono_zeroLocusOnOpen`: over a representable chart
the slice `V(c₁, …, c_r) ∩ V` is itself a scheme of the site, with a monomorphism into the chart
and the same `2 ^ 2 ^ size U₀` bound, so the open subspace of *it* that Stacks 06N2 returns is a
scheme of the site as well, by the lemma just named read at that representation. The
identification of an étale chart of the fibre of the slice with the zero scheme of the
pulled-back functions is
proved in `StacksFrontier/AlgebraicGeometry/Spaces/FibreSliceChartZeroScheme.lean`: the fibre of the
slice is `V(g^*c₁, …, g^*c_r)` inside the fibre, base change of the zero locus being
`AlgebraicGeometry.Space.vanishingSubfunctor_globalFunctionsMap_eq_preimage` and
`AlgebraicGeometry.Stack.exists_iso_vanishingSubfunctor_chartBaseChange`, and an étale chart of
*that* is the scheme-theoretic zero scheme of the pullbacks `p^*c₁|_U, …, p^*c_r|_U` inside an
affine étale chart of the fibre, by
`AlgebraicGeometry.Space.exists_iso_zeroScheme_chartBaseChange_globalFunctionsMap`. The
unramifiedness that feeds `AlgebraicGeometry.Stack.fibreIsUnramifiedNear_of_unramifiedAt` is read
off it with nothing transported, the criterion of **Stacks 02GF** being applied at the base
changed closed immersion itself:
`AlgebraicGeometry.Space.unramifiedAt_chartBaseChangeHom_globalFunctionsMap_comp_over_field`.
Not yet formalized is the finite type point assembly, which is the plumbing of that chart and its
structure morphism over `Spec k` into an étale chart `N` of an algebraic space representing the
fibre of the slice, carrying the square
`N.obj.hom ≫ fibreSpaceStructureMorphism = yoneda.map q` that the consumer asks for. That
plumbing is *not* the identification named just above read at `Fsp`, and the reason — the open
subspace `V` which **Stacks 06MD** returns, which makes the slice a closed subspace of `V` and
only a locally closed subspace of `U`, so that the closed subspace in play lives in an algebraic
space representing `V ×_𝒳 Spec k` and not in `Fsp`, while the slicing sequence and the closed
point of **Stacks 056U** are produced on an affine étale chart of `Fsp` — is explained in the
module documentation of
`StacksFrontier/AlgebraicGeometry/Stacks/SliceChartUnramifiedSpacePoint.lean`, together with the
three steps of the assembly that are independent of it.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 0506](https://stacks.math.columbia.edu/tag/0506)
* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
* [Stacks Project, Tag 06ME](https://stacks.math.columbia.edu/tag/06ME)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 0CG3](https://stacks.math.columbia.edu/tag/0CG3)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIL](https://stacks.math.columbia.edu/tag/0CIL)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The transport across the Stacks 0506 factorization -/

section Transport

variable {𝒴 𝒳 𝒵 : AlgebraicStacks.{u, w} B S hS}

/-- **Local quasi-finiteness passes from the inclusion of the essential image of an immersion to
the immersion itself.** Let `i : 𝒴 ⟶ 𝒳` be an immersion of algebraic stacks over `S` whose
essential image cuts out the full subcategory selected by `P`, and let `f : 𝒳 ⟶ 𝒵` be
representable by algebraic spaces. If the inclusion of that full subcategory composed with `f` is
locally quasi-finite in the sense of **Stacks 06PU**, then so is `i ≫ f`.

The **Stacks 0506** factorization of `i` through the inclusion, whiskered with `f`, is a square of
equivalences, across which the relative property of **Stacks 03YK** transports by **Stacks 0457**;
local quasi-finiteness is read through that relative property in both directions, which is
available because both 1-morphisms are representable by algebraic spaces. See the module
documentation. -/
theorem isLocallyQuasiFinite_comp_of_eq_essImage (i : 𝒴 ⟶ 𝒳)
    (hi : AlgebraicStacks.IsImmersion B S hS i)
    (f : 𝒳 ⟶ 𝒵) (hfrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (P : ObjectProperty 𝒳.val.val.obj)
    (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hPeq : P = (CatFiberedInGroupoids.homFunctor i.hom).essImage)
    (h : AlgebraicStacks.IsLocallyQuasiFinite B S hS
      (fullSubcategoryInclusion 𝒳 P hPalg ≫ f)) :
    AlgebraicStacks.IsLocallyQuasiFinite B S hS (i ≫ f) := by
  subst hPeq
  have _ha : Functor.IsEquivalence (AlgebraicStacks.toEssImageBased i).toFunctor :=
    AlgebraicStacks.isEquivalence_toEssImageBased i hi
  have _hb : Functor.IsEquivalence (BasedFunctor.id 𝒵.val.val).toFunctor :=
    AlgebraicStacks.isEquivalence_basedFunctorId
  have hirep : IsRepresentableByAlgebraicSpaces B S hS (i ≫ f).hom.hom :=
    isRepresentableByAlgebraicSpaces_comp B S hS i.hom f.hom hi.1 hfrep
  have hinclrep : IsRepresentableByAlgebraicSpaces B S hS
      (fullSubcategoryInclusion 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage hPalg ≫
        f).hom.hom :=
    isRepresentableByAlgebraicSpaces_comp B S hS
      (fullSubcategoryInclusion 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage hPalg).hom
      f.hom (AlgebraicStacks.isRepresentableByAlgebraicSpaces_essImageInclusion i hi) hfrep
  have hsq : BasedFunctor.comp (AlgebraicStacks.toEssImageBased i)
        ((fullSubcategoryInclusion 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage hPalg ≫
          f).hom.hom) ≅
      BasedFunctor.comp ((i ≫ f).hom.hom) (BasedFunctor.id 𝒵.val.val) :=
    Bicategory.whiskerRightIso (AlgebraicStacks.toEssImageBasedSquareIso i) f.hom.hom
  refine (AlgebraicStacks.isLocallyQuasiFinite_iff_isLocallyQuasiFinite_hom B S hS (i ≫ f)
    hirep).2 ?_
  exact relativeProperty_of_equivalences B S hS (Space.locallyQuasiFiniteProperty B S hS)
    (i ≫ f).hom.hom
    (fullSubcategoryInclusion 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage hPalg ≫
      f).hom.hom
    (AlgebraicStacks.toEssImageBased i) (BasedFunctor.id 𝒵.val.val) hsq
    ((AlgebraicStacks.isLocallyQuasiFinite_iff_isLocallyQuasiFinite_hom B S hS _ hinclrep).1 h)

/-- **Étaleness passes from the inclusion of the essential image of an immersion to the immersion
itself.** Let `i : 𝒴 ⟶ 𝒳` be an immersion of algebraic stacks over `S` whose essential image cuts
out the full subcategory selected by `P`, and let `f : 𝒳 ⟶ 𝒵` be representable by algebraic
spaces. If the inclusion of that full subcategory composed with `f` is étale in the sense of
**Stacks 0CIL**, then so is `i ≫ f`.

The square of equivalences and the transport are those of
`AlgebraicGeometry.Stack.isLocallyQuasiFinite_comp_of_eq_essImage`. Étaleness is read through the
relative property of **Stacks 03YK** forwards by
`AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_iff_relative`, étaleness of
morphisms of algebraic spaces being étale-smooth local on the source-and-target by
**Stacks 0CG3**, and backwards by
`AlgebraicGeometry.Stack.AlgebraicStacks.isEtale_of_isRelativelyEtale`, whose Deligne–Mumford
conjunct is **Stacks 050E** at the representability of `i ≫ f`. -/
theorem isEtale_comp_of_eq_essImage (i : 𝒴 ⟶ 𝒳)
    (hi : AlgebraicStacks.IsImmersion B S hS i)
    (f : 𝒳 ⟶ 𝒵) (hfrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (P : ObjectProperty 𝒳.val.val.obj)
    (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hPeq : P = (CatFiberedInGroupoids.homFunctor i.hom).essImage)
    (h : IsEtale B S hS (fullSubcategoryInclusion 𝒳 P hPalg ≫ f)) :
    IsEtale B S hS (i ≫ f) := by
  subst hPeq
  have _ha : Functor.IsEquivalence (AlgebraicStacks.toEssImageBased i).toFunctor :=
    AlgebraicStacks.isEquivalence_toEssImageBased i hi
  have _hb : Functor.IsEquivalence (BasedFunctor.id 𝒵.val.val).toFunctor :=
    AlgebraicStacks.isEquivalence_basedFunctorId
  have hirep : IsRepresentableByAlgebraicSpaces B S hS (i ≫ f).hom.hom :=
    isRepresentableByAlgebraicSpaces_comp B S hS i.hom f.hom hi.1 hfrep
  have hinclrep : IsRepresentableByAlgebraicSpaces B S hS
      (fullSubcategoryInclusion 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage hPalg ≫
        f).hom.hom :=
    isRepresentableByAlgebraicSpaces_comp B S hS
      (fullSubcategoryInclusion 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage hPalg).hom
      f.hom (AlgebraicStacks.isRepresentableByAlgebraicSpaces_essImageInclusion i hi) hfrep
  have hsq : BasedFunctor.comp (AlgebraicStacks.toEssImageBased i)
        ((fullSubcategoryInclusion 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage hPalg ≫
          f).hom.hom) ≅
      BasedFunctor.comp ((i ≫ f).hom.hom) (BasedFunctor.id 𝒵.val.val) :=
    Bicategory.whiskerRightIso (AlgebraicStacks.toEssImageBasedSquareIso i) f.hom.hom
  refine AlgebraicStacks.isEtale_of_isRelativelyEtale B S hS (i ≫ f) ⟨hirep, ?_⟩
  exact relativeProperty_of_equivalences B S hS
    (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (q : X ⟶ Y) => Space.IsEtale B S hS q.hom)
    (i ≫ f).hom.hom
    (fullSubcategoryInclusion 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage hPalg ≫
      f).hom.hom
    (AlgebraicStacks.toEssImageBased i) (BasedFunctor.id 𝒵.val.val) hsq
    ((hasPropertyOnEveryEtaleSmoothDiagram_iff_relative.{u, u, w} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (q : X ⟶ Y) => Space.IsEtale B S hS q.hom)
      (Space.isEtale_isEtaleSmoothLocalOnSourceAndTarget B S hS) _ hinclrep).1 h.2)

end Transport

/-! ### Stacks 06ME and Stacks 06N2 on an open subspace of the chart -/

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)

/-- **An open subspace of the chart is an immersion of algebraic stacks.** The 1-morphism of
**Stacks 0458** attached to the inclusion of an open subspace is an open immersion of algebraic
stacks, hence an immersion, an open immersion of algebraic spaces being one. -/
theorem isImmersion_algebraicSpaceStackMap_of_isOpenSubspace
    {V : Subfunctor U} (hV : Space.IsOpenSubspace B S hS V) :
    AlgebraicStacks.IsImmersion B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hU V.ι) :=
  have hoi := isOpenImmersion_algebraicSpaceStackMap_of_isOpenImmersion.{u, w} B S hS hV.1 hU hV.2
  ⟨hoi.1, fun T y hy E hE he =>
    Space.isImmersion_of_isOpenImmersion B S hS (hoi.2 T y hy E hE he)⟩

/-- **The conclusion of Stacks 06ME read on an open subspace of the chart.** Let `𝒳` be an
algebraic stack, let `U` be an algebraic space with a 1-morphism `f : U ⟶ 𝒳` locally of finite
type, let `Spec k ⟶ 𝒳` be a field-valued point and let `F = U ×_𝒳 Spec k` with projection
`p : F ⟶ U`. If some open substack of `F` containing `z ∈ |F|` is locally quasi-finite over
`Spec k` then there is an open subspace `V ⊆ U`, in the sense of **Stacks 02YU**, part (2), whose
point set contains `p(z)` and for which the composite of the 1-morphism of **Stacks 0458**
induced by `V` with `f` is locally quasi-finite.

The conclusion is the source's own: the replacement of `U` is by an open *subspace*. The proof
is `AlgebraicGeometry.Stack.exists_openSubstack_isLocallyQuasiFinite_unconditional`, whose open
substack is carried to an open subspace by
`AlgebraicGeometry.Stack.exists_isOpenSubspace_property_eq_essImage` and whose local
quasi-finiteness is carried across the **Stacks 0506** factorization of the subspace's 1-morphism
by `AlgebraicGeometry.Stack.isLocallyQuasiFinite_comp_of_eq_essImage`; nothing is added to it.

The fibre hypothesis is `AlgebraicGeometry.Stack.FibreIsLocallyQuasiFiniteNear`, which is not the
source's `dim_z(F) = 0` but the condition the source's own proof extracts from it by
**Stacks 04NV**; the finite-type hypothesis is the source's. The `@[stacks 06ME]` registration
therefore sits not here but on
`AlgebraicGeometry.Stack.exists_isOpenSubspace_isLocallyQuasiFinite_of_dimensionAtPoint_eq_zero`
of `StacksFrontier/AlgebraicGeometry/Stacks/FibreQuasiFiniteNearSubstack.lean`, which is this
declaration composed with
`AlgebraicGeometry.Stack.fibreIsLocallyQuasiFiniteNear_of_dimensionAtPoint_eq_zero`. -/
theorem exists_isOpenSubspace_isLocallyQuasiFinite
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (z : AlgebraicStacks.points B S hS (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g))
    (hz : FibreIsLocallyQuasiFiniteNear.{u, w} B S hS 𝒳 U hU k hk toBase f g z) :
    ∃ (V : Subfunctor U) (hV : Space.IsOpenSubspace B S hS V),
      AlgebraicStacks.pointsMap B S hS
          (fibreProjection B S hS 𝒳 U hU k hk toBase f g) z ∈
        spacePointMap B S hS U (algebraicSpaceStack.{u, w} B S hS U hU).val
            (BasedFunctor.id (fibredCategory B S hS U).val) ''
          Set.range (Space.pointsMap B S hS V.toFunctor V.ι) ∧
        AlgebraicStacks.IsLocallyQuasiFinite B S hS
          (algebraicSpaceStackMap.{u, w} B S hS hV.1 hU V.ι ≫ f) := by
  obtain ⟨W, hzW, hWqf⟩ := exists_openSubstack_isLocallyQuasiFinite_unconditional.{u, w}
    B S hS 𝒳 U hU k hk toBase f g hf z hz
  obtain ⟨V, hV, hprop, hpts⟩ :=
    exists_isOpenSubspace_property_eq_essImage.{u, w} B S hS U hU W
  refine ⟨V, hV, hpts ▸ hzW, ?_⟩
  exact isLocallyQuasiFinite_comp_of_eq_essImage B S hS
    (algebraicSpaceStackMap.{u, w} B S hS hV.1 hU V.ι)
    (isImmersion_algebraicSpaceStackMap_of_isOpenSubspace.{u, w} B S hS U hU hV) f
    (isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source B S hS 𝒳 U hU f)
    W.property W.isAlgebraic hprop hWqf

/-- **Stacks 06N2, with the conclusion read on an open subspace of the chart.** Let `𝒳` be an
algebraic stack, let `U` be an algebraic space with a 1-morphism `f : U ⟶ 𝒳` which is flat and
locally of finite presentation, let `Spec k ⟶ 𝒳` be a field-valued point and let
`F = U ×_𝒳 Spec k` with projection `p : F ⟶ U`. If `F ⟶ Spec k` is unramified at `z ∈ |F|` then
there is an open subspace `V ⊆ U`, in the sense of **Stacks 02YU**, part (2), whose point set
contains `p(z)` and for which the composite of the 1-morphism of **Stacks 0458** induced by `V`
with `f` is étale.

This is the source's own conclusion, obtained from
`AlgebraicGeometry.Stack.exists_openSubstack_isEtale_unconditional` the way
`AlgebraicGeometry.Stack.exists_isOpenSubspace_isLocallyQuasiFinite` is obtained from
Stacks 06ME, with `AlgebraicGeometry.Stack.isEtale_comp_of_eq_essImage` for the transport. -/
@[stacks 06N2 "the conclusion read on an open subspace of the algebraic space, as the source \
reads it: the composite of the 1-morphism of Stacks 0458 induced by an open subspace containing \
the image of the given point of the fibre with the given 1-morphism is etale. Nothing is added \
to exists_openSubstack_isEtale_unconditional: its open substack is carried to an open subspace \
with the same \
point set by exists_isOpenSubspace_property_eq_essImage, and the etaleness is carried across the \
Stacks 0506 factorization of that subspace's 1-morphism through the substack's inclusion by \
isEtale_comp_of_eq_essImage"]
theorem exists_isOpenSubspace_isEtale
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (z : AlgebraicStacks.points B S hS (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g))
    (hz : FibreIsUnramifiedNear.{u, w} B S hS 𝒳 U hU k hk toBase f g z) :
    ∃ (V : Subfunctor U) (hV : Space.IsOpenSubspace B S hS V),
      AlgebraicStacks.pointsMap B S hS
          (fibreProjection B S hS 𝒳 U hU k hk toBase f g) z ∈
        spacePointMap B S hS U (algebraicSpaceStack.{u, w} B S hS U hU).val
            (BasedFunctor.id (fibredCategory B S hS U).val) ''
          Set.range (Space.pointsMap B S hS V.toFunctor V.ι) ∧
        IsEtale B S hS (algebraicSpaceStackMap.{u, w} B S hS hV.1 hU V.ι ≫ f) := by
  obtain ⟨W, hzW, hWet⟩ := exists_openSubstack_isEtale_unconditional.{u, w} B S hS 𝒳 U hU k hk
    toBase f g hflat hfp z hz
  obtain ⟨V, hV, hprop, hpts⟩ :=
    exists_isOpenSubspace_property_eq_essImage.{u, w} B S hS U hU W
  refine ⟨V, hV, hpts ▸ hzW, ?_⟩
  exact isEtale_comp_of_eq_essImage B S hS
    (algebraicSpaceStackMap.{u, w} B S hS hV.1 hU V.ι)
    (isImmersion_algebraicSpaceStackMap_of_isOpenSubspace.{u, w} B S hS U hU hV) f
    (isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source B S hS 𝒳 U hU f)
    W.property W.isAlgebraic hprop hWet

end AlgebraicGeometry.Stack

end
