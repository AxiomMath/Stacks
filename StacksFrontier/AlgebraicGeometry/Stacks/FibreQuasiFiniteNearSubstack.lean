module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreUnramifiedNearSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteNotionsAgree

/-!
# The fibre hypothesis of Stacks 06ME, from the source's hypothesis `dim_z(F) = 0`

**Stacks 06ME** asks of its point `z ∈ |F|` of the fibre `F = U ×_𝒳 Spec k` that
`dim_z(F) = 0`, and its proof uses that hypothesis in exactly one way: by **Stacks 04NV** it
says that `F ⟶ Spec k` is locally quasi-finite *at* `z`, which is what the base-change step of
Properties of Stacks, Remark 100.9.20 (2) consumes.

The library states Stacks 06ME at that intermediate condition,
`AlgebraicGeometry.Stack.FibreIsLocallyQuasiFiniteNear` — some open substack of `F` containing
`z` is locally quasi-finite over `Spec k` — and until now that predicate had no producer, so
nothing connected the registered hypothesis of Stacks 06ME to the source's. This file supplies
the connection, in the two steps the source takes:

* the passage from an open subspace of a representing algebraic space of `F`, locally
  quasi-finite over `Spec k`, to the open substack of `F` that the predicate asks for
  (the quasi-finite counterpart of
  `AlgebraicGeometry.Stack.fibreIsUnramifiedNear_of_isUnramified_isOpenSubspace`, which is why
  **Stacks 06N2** has a producer where Stacks 06ME had none);
* **Stacks 04NV**, which turns `dim_z(F) = 0` into such an open subspace.

## Main results

* `AlgebraicGeometry.Stack.relativeProperty_locallyQuasiFinite_openSubspaceFibreMap_comp`: the
  relative property of **Stacks 03YK** at local quasi-finiteness for the composite
  `S_W ⟶ F ⟶ Spec k`.
* `AlgebraicGeometry.Stack.fibreIsLocallyQuasiFiniteNear_of_isLocallyQuasiFinite_isOpenSubspace`:
  an open subspace of a representing algebraic space of the fibre which is locally quasi-finite
  over `Spec k` and contains a point produces
  `AlgebraicGeometry.Stack.FibreIsLocallyQuasiFiniteNear` at that point.
* `AlgebraicGeometry.Stack.fibreIsLocallyQuasiFiniteNear_of_dimensionAtPoint_eq_zero`: **the
  bridge**, from the source's hypothesis `dim_z(F) = 0` on a representing algebraic space of
  `F` to `AlgebraicGeometry.Stack.FibreIsLocallyQuasiFiniteNear` at that point. The only other
  hypothesis is the one Stacks 06ME already makes, that `f : U ⟶ 𝒳` is locally of finite type.
* `AlgebraicGeometry.Stack.exists_openSubstack_isLocallyQuasiFinite_of_dimensionAtPoint_eq_zero`
  and
  `...exists_isOpenSubspace_isLocallyQuasiFinite_of_dimensionAtPoint_eq_zero`: the two
  conclusions of **Stacks 06ME** that the library already has, restated at the source's own
  hypothesis `dim_z(F) = 0` by composing with the bridge. Both hypotheses and both conclusions
  are then the source's, and these two carry the `@[stacks 06ME]` registration.

## How it is proved

The open-substack construction is the one of
`StacksFrontier/AlgebraicGeometry/Stacks/FibreUnramifiedNearSubstack.lean` and is reused verbatim:
the open substack is the essential image of `AlgebraicGeometry.Stack.openSubspaceFibreMap`,
which is an open immersion by
`AlgebraicGeometry.Stack.isOpenImmersion_openSubspaceFibreMap`, and the membership clause is
`AlgebraicGeometry.Stack.mem_range_pointsMap_openSubspaceFibreMap`. Nothing in that
construction mentions the property being carried.

**The local quasi-finiteness clause.** Local quasi-finiteness of a 1-morphism of algebraic
stacks is **Stacks 06PU**, `AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyQuasiFinite`,
which is not a relative property; but for a 1-morphism representable by algebraic spaces it
agrees with the relative notion of **Stacks 04XB** by
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_iff_isLocallyQuasiFinite_hom`,
and the inclusion of this open substack composed with the structure 1-morphism is
representable: its source is represented by the open subspace, through
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_essImage_of_isImmersion`. The relative
notion is the relative property of **Stacks 03YK** at
`AlgebraicGeometry.Space.locallyQuasiFiniteProperty` on the nose, so what has to be produced is
that relative property, and it is produced exactly as the unramified case produces its own: the
bridge of **Stacks 04XB** for represented source and target,
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`, applied at `S_W` — whose
comparison with `W` is the identity — where
`AlgebraicGeometry.Stack.representingMap_openSubspaceFibreMap_comp` computes the induced
morphism of representing presheaves to be `W.ι ≫ q`. It is then transported to the open
substack along the **Stacks 0506** factorization by **Stacks 0457**,
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences_symm`.

**The bridge.** The structure morphism `q : Fsp ⟶ Spec k` of a representing algebraic space is
locally of finite type, being the morphism of representing presheaves
(`AlgebraicGeometry.Stack.isLocallyOfFiniteType_representingMap`) of the base change of `f`
along `g` (**Stacks 06FU**,
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_baseChange`); so the source's
finite-type hypothesis is all that is needed, and no finiteness is assumed of the fibre. Over a
base with at most one point the relative dimension of **Stacks 04NM** at a point is the
dimension of **Stacks 04N5** of the source there,
`AlgebraicGeometry.Space.hasRelativeDimensionAt_zero_iff_dimensionAtPoint_eq_zero`, which is
the only place the hypothesis that `k` is a field is used — the spectrum of a field has one
point. **Stacks 04NV** in its pointwise form,
`AlgebraicGeometry.Space.isQuasiFiniteAt_iff_hasRelativeDimensionAt_zero`, then turns relative
dimension zero at `z` into `AlgebraicGeometry.Space.IsQuasiFiniteAt`, which is by definition a
locally quasi-finite open subspace of `Fsp` containing `z`; the first step carries it to the
open substack of `F`.

## Implementation notes

The `@[stacks 06ME]` registration sits on the two restatements below, which are the covering
set of the lemma at the source's own hypothesis: one reads the conclusion on an open substack of
the stack of `U`, the other on an open subspace of `U` exactly as the source reads it, and each
assumes `dim_z(F) = 0` and the source's finite-type hypothesis and nothing else. It used to sit
on `AlgebraicGeometry.Stack.exists_openSubstack_isLocallyQuasiFinite_unconditional` and
`AlgebraicGeometry.Stack.exists_isOpenSubspace_isLocallyQuasiFinite`, which state the fibre
hypothesis as `AlgebraicGeometry.Stack.FibreIsLocallyQuasiFiniteNear` — the intermediate
condition the source's own proof extracts from `dim_z(F) = 0` — and those two are now untagged.
Also untagged, and superseded by the two restatements below, is the conditional twin
`AlgebraicGeometry.Stack.exists_openSubstack_isLocallyQuasiFinite` of
`StacksFrontier/AlgebraicGeometry/Stacks/ChartShrinkingQuasiFiniteEtale.lean`, which takes the
fibre hypothesis in the same intermediate form and in addition the two clauses of
**Stacks 06M5** as inputs — the locus `W` with `hW` and its compatibility `hBaseChange` with the
base change along the field-valued point. Those inputs cannot be discharged in that file: the
locus of **Stacks 06M3** is constructed in
`StacksFrontier/AlgebraicGeometry/Stacks/RelativePropertyLocus.lean`, which imports it.

Restating *those* two at `dim_z(F) = 0`, which would have left the registration where it was,
is not available: the bridge lives here, and this file is downstream of both of them —
`StacksFrontier/AlgebraicGeometry/Stacks/ChartShrinkingOpenSubspace.lean`, which this file imports,
itself imports `StacksFrontier/AlgebraicGeometry/Stacks/ChartShrinkingQuasiFiniteEtale.lean` — so a
call to the bridge from either would close an import cycle. Nor can the bridge be moved
upstream: it rests on the open-substack construction of
`StacksFrontier/AlgebraicGeometry/Stacks/FibreUnramifiedNearSubstack.lean`
(`AlgebraicGeometry.Stack.openSubspaceFibreMap`), and that file imports
`...ChartShrinkingQuasiFiniteEtale` too. Every other tag used below — Stacks 0457, 04N5, 04NM,
04NV, 04SW, 04XB, 0506, 06FU, 06PU, 06UA — is registered where it is proved.

The point of `|F|` at which the conclusion is stated is the image of the point `z` of `|Fsp|`
under the comparison `AlgebraicGeometry.Stack.spacePointMap` of the representing equivalence,
which is the shape
`AlgebraicGeometry.Stack.fibreIsUnramifiedNear_of_isUnramified_isOpenSubspace` already uses and
which `AlgebraicGeometry.Stack.bijective_spacePointMap_representing` makes a bijection, so no
point of `|F|` is excluded by stating the hypothesis on `|Fsp|`.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 04NV](https://stacks.math.columbia.edu/tag/04NV)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 0506](https://stacks.math.columbia.edu/tag/0506)
* [Stacks Project, Tag 06FU](https://stacks.math.columbia.edu/tag/06FU)
* [Stacks Project, Tag 06ME](https://stacks.math.columbia.edu/tag/06ME)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 06UA](https://stacks.math.columbia.edu/tag/06UA)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)

variable (Fsp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hFsp : IsAlgebraicSpace B S hS Fsp)
  (eF : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val.val.p
    (presheafOfCategories (Fsp ⋙ typeToCat)).p)

/-! ### From an open subspace of a representing algebraic space to an open substack -/

section OpenSubspace

variable (W : Subfunctor Fsp) (hWsp : IsAlgebraicSpace B S hS W.toFunctor)

/-- **The relative local quasi-finiteness of the open subspace over `Spec k`.** The 1-morphism
`S_W ⟶ F ⟶ Spec k` has the relative property of **Stacks 03YK** at local quasi-finiteness as
soon as the morphism of algebraic spaces `W ⟶ Spec k` is locally quasi-finite.

The bridge of **Stacks 04XB** for represented source and target,
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`, is applied at the
identity comparison of `S_W` with `W` and the representing equivalence `eF` of the fibre; the
morphism of representing presheaves it produces is computed by
`AlgebraicGeometry.Stack.representingMap_openSubspaceFibreMap_comp`. -/
theorem relativeProperty_locallyQuasiFinite_openSubspaceFibreMap_comp
    (hqf : Space.IsLocallyQuasiFinite B S hS
      (W.ι ≫ fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF)) :
    RelativeProperty B S hS (Space.locallyQuasiFiniteProperty B S hS)
      (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp ≫
        fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom := by
  have : (Space.locallyQuasiFiniteProperty B S hS).IsStableUnderBaseChange :=
    Space.locallyQuasiFiniteProperty_isStableUnderBaseChange B S hS
  have : (Space.locallyQuasiFiniteProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isLocallyQuasiFinite_isLocalAtTarget_fppf.{u, u} B S hS
  have ha : IsRepresentableByAlgebraicSpaces B S hS
      (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp ≫
        fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS _
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS W.toFunctor hWsp)
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS _)
  refine (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
    (Space.locallyQuasiFiniteProperty B S hS)
    (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp ≫
      fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom ha W.toFunctor
    (yoneda.obj (fieldPointObject B S hS k hk toBase)) hWsp
    (isAlgebraicSpace_yoneda B S hS _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (PresheafOfCategories.sliceElementsEquivalenceOver _)).mpr ?_
  rw [representingMap_openSubspaceFibreMap_comp.{u, w} B S hS 𝒳 U hU k hk toBase f g
    Fsp hFsp eF W hWsp]
  exact hqf

include hFsp hWsp in
/-- **The fibre hypothesis of Stacks 06ME, from a locally quasi-finite open subspace of a
representing algebraic space.** Let `Fsp` represent the fibre `F = U ×_𝒳 Spec k` through `eF`,
let `W` be an open subspace of `Fsp` whose structure morphism to `Spec k` is a locally
quasi-finite morphism of algebraic spaces, and let `z` be a point of `|Fsp|` lying in `W`. Then
`AlgebraicGeometry.Stack.FibreIsLocallyQuasiFiniteNear` holds at the point of `|F|` below `z`:
some open substack of `F` contains that point and is locally quasi-finite over `Spec k` in the
sense of **Stacks 06PU**.

The open substack is the essential image of
`AlgebraicGeometry.Stack.openSubspaceFibreMap`; see the module documentation. This is the
quasi-finite counterpart of
`AlgebraicGeometry.Stack.fibreIsUnramifiedNear_of_isUnramified_isOpenSubspace`. -/
theorem fibreIsLocallyQuasiFiniteNear_of_isLocallyQuasiFinite_isOpenSubspace
    (hWι : Space.IsOpenImmersion B S hS W.ι)
    (hqf : Space.IsLocallyQuasiFinite B S hS
      (W.ι ≫ fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF))
    (z : Space.points B S hS Fsp)
    (hz : z ∈ Set.range (Space.pointsMap B S hS W.toFunctor W.ι)) :
    FibreIsLocallyQuasiFiniteNear.{u, w} B S hS 𝒳 U hU k hk toBase f g
      (spacePointMap B S hS Fsp (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
        (representingEquivalence B S hS Fsp
          (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).functor z) := by
  have hi := isOpenImmersion_openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g
    Fsp hFsp eF W hWsp hWι
  have hiImm : AlgebraicStacks.IsImmersion B S hS
      (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp) :=
    ⟨hi.1, fun U' y hy E hE he =>
      Space.isImmersion_of_isOpenImmersion B S hS (hi.2 U' y hy E hE he)⟩
  have hP := AlgebraicStacks.isAlgebraicStack_essImage
    (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp) hiImm
  obtain ⟨c, hce, ⟨hcα⟩⟩ := AlgebraicStacks.exists_isEquivalence_to_essImage
    (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp) hiImm hP
  refine ⟨⟨(CatFiberedInGroupoids.homFunctor
      (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g
        Fsp hFsp eF W hWsp).hom).essImage, inferInstance, hP,
    AlgebraicStacks.isOpenImmersion_essImageInclusion
      (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp)
      hi hiImm hP⟩, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := mem_range_pointsMap_openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk
      toBase f g Fsp hFsp eF W hWsp z hz
    refine ⟨AlgebraicStacks.pointsMap B S hS c p, ?_⟩
    have h₁ : AlgebraicStacks.pointsMap B S hS (c ≫ fullSubcategoryInclusion
          (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g) _ hP) =
        AlgebraicStacks.pointsMap B S hS
          (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp) :=
      AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS hcα.hom
    refine Eq.trans ?_ hp
    exact (congrFun (AlgebraicStacks.pointsMap_comp B S hS c
      (fullSubcategoryInclusion
        (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g) _ hP)) p).symm.trans
      (congrFun h₁ p)
  · have h𝒱 := isRepresentableByAlgebraicSpace_essImage_of_isImmersion B S hS
      (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp)
      hiImm hP (isRepresentableByAlgebraicSpace_fibredCategory B S hS W.toFunctor hWsp)
    have hq : IsRepresentableByAlgebraicSpaces B S hS
        (fullSubcategoryInclusion
            (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g) _ hP ≫
          fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom.hom :=
      isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS _ h𝒱
        (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS _)
    refine (AlgebraicStacks.isLocallyQuasiFinite_iff_isLocallyQuasiFinite_hom B S hS
      (fullSubcategoryInclusion
          (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g) _ hP ≫
        fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g) hq).2 ?_
    have _ha : Functor.IsEquivalence (AlgebraicStacks.toEssImageBased
        (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g
          Fsp hFsp eF W hWsp)).toFunctor :=
      AlgebraicStacks.isEquivalence_toEssImageBased _ hiImm
    have _hb : Functor.IsEquivalence (BasedFunctor.id
        (schemeStack.{u, w} B S hS
          (fieldPointObject B S hS k hk toBase)).val.val).toFunctor :=
      AlgebraicStacks.isEquivalence_basedFunctorId
    have hsq : BasedFunctor.comp (AlgebraicStacks.toEssImageBased
          (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp))
          ((fullSubcategoryInclusion
              (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g) _ hP ≫
            fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom.hom) ≅
        BasedFunctor.comp
          ((openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp ≫
            fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom.hom)
          (BasedFunctor.id (schemeStack.{u, w} B S hS
            (fieldPointObject B S hS k hk toBase)).val.val) :=
      Bicategory.whiskerRightIso
        (AlgebraicStacks.toEssImageBasedSquareIso
          (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp))
        (fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom.hom
    exact relativeProperty_of_equivalences_symm B S hS
      (Space.locallyQuasiFiniteProperty B S hS)
      (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp ≫
        fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom.hom
      (fullSubcategoryInclusion
          (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g) _ hP ≫
        fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom.hom
      (AlgebraicStacks.toEssImageBased
        (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp))
      (BasedFunctor.id _) hsq
      (relativeProperty_locallyQuasiFinite_openSubspaceFibreMap_comp.{u, w} B S hS 𝒳 U hU k hk
        toBase f g Fsp hFsp eF W hWsp hqf)

end OpenSubspace

/-! ### Stacks 04NV: the bridge from the source's hypothesis `dim_z(F) = 0` -/

include hFsp in
/-- **The structure morphism of a representing algebraic space of the fibre is locally of finite
type.** For `f : U ⟶ 𝒳` locally of finite type, the morphism `Fsp ⟶ Spec k` of algebraic spaces
induced by the structure 1-morphism of `F = U ×_𝒳 Spec k` is locally of finite type.

The structure 1-morphism of `F` is the base change of `f` along `g`, so **Stacks 06FU** applies
to it, and `AlgebraicGeometry.Stack.isLocallyOfFiniteType_representingMap` reads local finite
type of a 1-morphism of algebraic stacks off the induced morphism of representing presheaves
of **Stacks 04SW**. -/
theorem isLocallyOfFiniteType_fibreSpaceStructureMorphism
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f) :
    Space.IsLocallyOfFiniteType B S hS
      (fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF) :=
  isLocallyOfFiniteType_representingMap.{u, w} B S hS
    (𝒳 := fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g)
    (𝒴 := schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase))
    Fsp (yoneda.obj (fieldPointObject B S hS k hk toBase)) hFsp
    (isAlgebraicSpace_yoneda B S hS _) eF
    (PresheafOfCategories.sliceElementsEquivalenceOver _)
    (fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g)
    (AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS f g
      (twoFibreProductSquareAlgebraicStacks B S hS f g).swap
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g)) hf)

include hFsp in
/-- **The fibre hypothesis of Stacks 06ME is the source's hypothesis `dim_z(F) = 0`.** Let
`𝒳` be an algebraic stack, let `f : U ⟶ 𝒳` be a 1-morphism from an algebraic space which is
locally of finite type, let `Spec k ⟶ 𝒳` be a field-valued point, let `Fsp` represent the fibre
`F = U ×_𝒳 Spec k` through `eF`, and let `z` be a point of `|Fsp|` at which the dimension of
**Stacks 04N5** of the algebraic space `Fsp` is zero. Then
`AlgebraicGeometry.Stack.FibreIsLocallyQuasiFiniteNear` holds at the point of `|F|`
corresponding to `z`.

This is the step the source's proof of **Stacks 06ME** takes with Morphisms of Spaces, Lemma
**Stacks 04NV**: the structure morphism `Fsp ⟶ Spec k` is locally of finite type, and over the
one-point base `Spec k` the relative dimension of **Stacks 04NM** at `z` is the dimension of
`Fsp` at `z`
(`AlgebraicGeometry.Space.hasRelativeDimensionAt_zero_iff_dimensionAtPoint_eq_zero`), so
Stacks 04NV in its pointwise form
(`AlgebraicGeometry.Space.isQuasiFiniteAt_iff_hasRelativeDimensionAt_zero`) makes
`Fsp ⟶ Spec k` quasi-finite at `z`, which is exactly a locally quasi-finite open subspace of
`Fsp` containing `z`;
`AlgebraicGeometry.Stack.fibreIsLocallyQuasiFiniteNear_of_isLocallyQuasiFinite_isOpenSubspace`
carries that to the open substack of `F`. -/
theorem fibreIsLocallyQuasiFiniteNear_of_dimensionAtPoint_eq_zero
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (z : Space.points B S hS Fsp)
    (hz : Space.dimensionAtPoint B S hS Fsp hFsp z = 0) :
    FibreIsLocallyQuasiFiniteNear.{u, w} B S hS 𝒳 U hU k hk toBase f g
      (spacePointMap B S hS Fsp (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
        (representingEquivalence B S hS Fsp
          (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).functor z) := by
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj
      (fieldPointObject B S hS k hk toBase)) := by
    change Subsingleton (Spec (CommRingCat.of k))
    infer_instance
  have hft := isLocallyOfFiniteType_fibreSpaceStructureMorphism.{u, w} B S hS 𝒳 U hU k hk
    toBase f g Fsp hFsp eF hf
  have hdim : Space.HasRelativeDimensionAt 0 B S hS
      (fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF) z :=
    (Space.hasRelativeDimensionAt_zero_iff_dimensionAtPoint_eq_zero B S hS hFsp hsub _ z).mpr hz
  obtain ⟨W, hW, z', hz', hqf⟩ :=
    (Space.isQuasiFiniteAt_iff_hasRelativeDimensionAt_zero B S hS hFsp
      (isAlgebraicSpace_yoneda B S hS _) _ hft z).mpr hdim
  exact fibreIsLocallyQuasiFiniteNear_of_isLocallyQuasiFinite_isOpenSubspace.{u, w} B S hS 𝒳 U hU
    k hk toBase f g Fsp hFsp eF W hW.1 hW.2 hqf z ⟨z', hz'⟩

/-! ### Stacks 06ME at the source's own hypothesis -/

include hFsp in
/-- **Stacks 06ME at the source's own hypothesis, with the conclusion read on an open substack.**
Let `𝒳` be an algebraic stack, let `U` be an algebraic space with a 1-morphism `f : U ⟶ 𝒳`
locally of finite type, let `Spec k ⟶ 𝒳` be a field-valued point, let `Fsp` represent the fibre
`F = U ×_𝒳 Spec k` through `eF`, and let `z` be a point of `|Fsp|` with `dim_z(F) = 0` — the
dimension of **Stacks 04N5** of the algebraic space `Fsp` at `z`. Then there is an open substack
`W` of the algebraic stack of `U` whose point set contains `p(z)` and for which `W.inclusion ≫ f`
is locally quasi-finite.

This is `AlgebraicGeometry.Stack.exists_openSubstack_isLocallyQuasiFinite_unconditional` with its
fibre
hypothesis `AlgebraicGeometry.Stack.FibreIsLocallyQuasiFiniteNear` replaced by the source's
`dim_z(F) = 0`, through
`AlgebraicGeometry.Stack.fibreIsLocallyQuasiFiniteNear_of_dimensionAtPoint_eq_zero`. Nothing is
added and nothing is weakened: the finite-type hypothesis is the source's, and the hypothesis on
`z` is the source's. The point of `|F|` is the image of `z` under the comparison
`AlgebraicGeometry.Stack.spacePointMap` of the representing equivalence, which is a bijection by
`AlgebraicGeometry.Stack.bijective_spacePointMap_representing`, so every point of `|F|` is
reached. -/
@[stacks 06ME "the source's own hypotheses, with the conclusion read on an open substack of the \
stack of the algebraic space: the 1-morphism is locally of finite type and the given point z of \
the fibre has dim_z(F) = 0, the dimension of Stacks 04N5 of a representing algebraic space Fsp \
of the fibre at z. Nothing is added and nothing is weakened. The proof is \
exists_openSubstack_isLocallyQuasiFinite_unconditional of \
ChartShrinkingQuasiFiniteEtaleUnconditional -- which states the same conclusion at the \
intermediate condition the source's own proof extracts from \
dim_z(F) = 0, that some open substack of the fibre containing z is locally quasi-finite over \
Spec k -- composed with the step the source's proof takes from dim_z(F) = 0 to that condition \
by Stacks 04NV, which is fibreIsLocallyQuasiFiniteNear_of_dimensionAtPoint_eq_zero above. The \
source's open subspace of the algebraic space is rendered here as an open substack of the stack \
of that space, with the same point set, both directions of that passage being proved as \
exists_openSubstack_algebraicSpaceStack_of_isOpenImmersion and \
exists_isOpenSubspace_property_eq_essImage; the conclusion read on an open subspace, as the \
source reads it, is exists_isOpenSubspace_isLocallyQuasiFinite_of_dimensionAtPoint_eq_zero \
below. The point of the fibre is the image of z under the comparison spacePointMap of the \
representing equivalence, which bijective_spacePointMap_representing makes a bijection, so no \
point of the fibre is excluded by stating the hypothesis on Fsp"]
theorem exists_openSubstack_isLocallyQuasiFinite_of_dimensionAtPoint_eq_zero
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (z : Space.points B S hS Fsp)
    (hz : Space.dimensionAtPoint B S hS Fsp hFsp z = 0) :
    ∃ W : OpenSubstack (algebraicSpaceStack.{u, w} B S hS U hU),
      AlgebraicStacks.pointsMap B S hS
          (fibreProjection B S hS 𝒳 U hU k hk toBase f g)
          (spacePointMap B S hS Fsp
            (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
            (representingEquivalence B S hS Fsp
              (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).functor z) ∈
        W.pointSet B S hS ∧
        AlgebraicStacks.IsLocallyQuasiFinite B S hS (W.inclusion ≫ f) :=
  exists_openSubstack_isLocallyQuasiFinite_unconditional.{u, w} B S hS 𝒳 U hU k hk toBase f g hf _
    (fibreIsLocallyQuasiFiniteNear_of_dimensionAtPoint_eq_zero.{u, w} B S hS 𝒳 U hU k hk toBase
      f g Fsp hFsp eF hf z hz)

include hFsp in
/-- **Stacks 06ME at the source's own hypothesis, with the conclusion read on an open subspace.**
The statement of the source: with `f : U ⟶ 𝒳` locally of finite type and `z` a point of the
fibre `F = U ×_𝒳 Spec k` at which the dimension of `F` is zero, there is an open subspace
`V ⊆ U` of **Stacks 02YU**, part (2), whose point set contains `p(z)` and for which the
composite of the 1-morphism of **Stacks 0458** induced by `V` with `f` is locally quasi-finite.

This is `AlgebraicGeometry.Stack.exists_isOpenSubspace_isLocallyQuasiFinite` with its fibre
hypothesis replaced by the source's, through
`AlgebraicGeometry.Stack.fibreIsLocallyQuasiFiniteNear_of_dimensionAtPoint_eq_zero`. Both
hypotheses are now the source's and the conclusion is the source's. -/
@[stacks 06ME "the statement of the source, hypotheses and conclusion: the 1-morphism out of \
the algebraic space is locally of finite type, the given point z of the fibre has \
dim_z(F) = 0 -- the dimension of Stacks 04N5 of a representing algebraic space Fsp of the fibre \
at z -- and after replacing the algebraic space by an open subspace of Stacks 02YU, part (2), \
containing the image of z, the 1-morphism is locally quasi-finite, the replacement read as the \
composite of the 1-morphism of Stacks 0458 induced by that open subspace. Nothing is added and \
nothing is weakened. The proof is exists_isOpenSubspace_isLocallyQuasiFinite of \
ChartShrinkingOpenSubspace -- the same conclusion at the intermediate condition the source's \
own proof extracts from dim_z(F) = 0 -- composed with the step the source's proof takes from \
dim_z(F) = 0 to that condition by Stacks 04NV, which is \
fibreIsLocallyQuasiFiniteNear_of_dimensionAtPoint_eq_zero above. The point of the fibre is the \
image of z under the comparison spacePointMap of the representing equivalence, which \
bijective_spacePointMap_representing makes a bijection, so no point of the fibre is excluded by \
stating the hypothesis on Fsp"]
theorem exists_isOpenSubspace_isLocallyQuasiFinite_of_dimensionAtPoint_eq_zero
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (z : Space.points B S hS Fsp)
    (hz : Space.dimensionAtPoint B S hS Fsp hFsp z = 0) :
    ∃ (V : Subfunctor U) (hV : Space.IsOpenSubspace B S hS V),
      AlgebraicStacks.pointsMap B S hS
          (fibreProjection B S hS 𝒳 U hU k hk toBase f g)
          (spacePointMap B S hS Fsp
            (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
            (representingEquivalence B S hS Fsp
              (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).functor z) ∈
        spacePointMap B S hS U (algebraicSpaceStack.{u, w} B S hS U hU).val
            (BasedFunctor.id (fibredCategory B S hS U).val) ''
          Set.range (Space.pointsMap B S hS V.toFunctor V.ι) ∧
        AlgebraicStacks.IsLocallyQuasiFinite B S hS
          (algebraicSpaceStackMap.{u, w} B S hS hV.1 hU V.ι ≫ f) :=
  exists_isOpenSubspace_isLocallyQuasiFinite.{u, w} B S hS 𝒳 U hU k hk toBase f g hf _
    (fibreIsLocallyQuasiFiniteNear_of_dimensionAtPoint_eq_zero.{u, w} B S hS 𝒳 U hU k hk toBase
      f g Fsp hFsp eF hf z hz)

end AlgebraicGeometry.Stack

end
