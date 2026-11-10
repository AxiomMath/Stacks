module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.EtaleLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UnramifiedLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Etale.FpqcDescentApplication.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedQuasiFinite

/-!
# Permanence properties of unramified morphisms of algebraic spaces

Unramifiedness of a morphism of algebraic spaces over a scheme `S`, in the sense of
Tag 03ZH, is the condition of Tag 03MJ that the underlying scheme morphism of every
commuting square of étale scheme charts be unramified. This file proves that the class of
such morphisms is stable under composition, under base change and under cancellation on the
right, compares it with G-unramifiedness, deduces local quasi-finiteness, and characterizes
unramifiedness among morphisms locally of finite type by the relative diagonal being an open
immersion.

Every one of those statements is the corresponding statement about unramified morphisms of
*schemes*, transported along the chart condition. What makes the transport possible is that
unramifiedness of scheme morphisms is étale local on the source and target in the sense of
Tag 04QZ, which is `AlgebraicGeometry.unramified_isEtaleLocalOnSourceAndTarget` in
`StacksFrontier/AlgebraicGeometry/Descent/EtaleLocal/UnramifiedLocalAtSource.lean`.

## Main results

* `AlgebraicGeometry.Space.isUnramified_comp`: **Stacks 03ZI**.
* `AlgebraicGeometry.Space.isUnramified_isStableUnderBaseChange`: **Stacks 03ZJ**.
* `AlgebraicGeometry.Space.isGUnramified_iff_isUnramified_and_isLocallyOfFinitePresentation`:
  **Stacks 04G1**.
* `AlgebraicGeometry.Space.isQuasiFiniteAt_of_isUnramifiedAt`: **Stacks 05W0**, the pointwise
  statement.
* `AlgebraicGeometry.Space.isUnramified_of_isImmersion`: **Stacks 06CQ**.
* `AlgebraicGeometry.Space.isUnramified_of_comp`: **Stacks 06G6**.
* `AlgebraicGeometry.Space.isUnramified_of_isOpenImmersion_pullbackDiagonal`: **Stacks 05W1**,
  the converse direction; the forward direction is
  `AlgebraicGeometry.Space.isOpenImmersion_diagonal_of_isUnramified`.
* `AlgebraicGeometry.Space.isUnramified_tfae`: **Stacks 03ZK**.
* `AlgebraicGeometry.Space.unramifiedLocus`: **Stacks 05W2**, part (1).

## Implementation notes

Inside the namespace `AlgebraicGeometry.Space` the scheme-morphism classes are written
`_root_.AlgebraicGeometry.Unramified` and `_root_.AlgebraicGeometry.GUnramified`, as in
`StacksFrontier/AlgebraicGeometry/Spaces/Unramified.lean`, because the unqualified names would
be read in the `Space` namespace.

No algebraic-space hypothesis is needed for Tag 04G1 or Tag 05W0: both are implications
between chart conditions, proved chart by chart, so they hold for arbitrary morphisms of
presheaves on the big fppf site. Tags 03ZI, 03ZJ, 06CQ and 06G6 do need them, because they
pass through the comparison of the every-chart condition with the one-surjective-chart
condition of Tag 03MJ, which takes atlases of the spaces involved.

Tag 05W1 is the one statement here which is not a chart-by-chart transport, because its two
sides live on different morphisms: the relative diagonal of `f` is a morphism of algebraic
spaces whose charts are not charts of `f`. What makes it work is that the relative diagonal is
relatively representable (part (1) of Tag 03HK), so that the every-chart condition of Tag 03MJ
for it is the plain relative morphism property, and that a commuting square of étale charts of
`f` produces one of its relative diagonal, namely the relative diagonal of the morphism of the
site on top of the square mapping to the fibre product of `f` with itself. That chart is
`AlgebraicGeometry.Space.diagonalChartMap`.

Tag 06CQ is reduced to the fact that an immersion of *schemes* is unramified, and that in turn
is Tag 02HE again: an immersion is a monomorphism, so its relative diagonal is an isomorphism
and hence an open immersion, which makes it formally unramified, and it is locally of finite
type. The source argues instead through the factorization of an immersion into a closed
immersion followed by an open immersion; the monomorphism argument needs neither factor.

## References

* [Stacks Project, Tag 02GE](https://stacks.math.columbia.edu/tag/02GE)
* [Stacks Project, Tag 02GG](https://stacks.math.columbia.edu/tag/02GG)
* [Stacks Project, Tag 02HE](https://stacks.math.columbia.edu/tag/02HE)
* [Stacks Project, Tag 02LC](https://stacks.math.columbia.edu/tag/02LC)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 03FS](https://stacks.math.columbia.edu/tag/03FS)
* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
* [Stacks Project, Tag 03HK](https://stacks.math.columbia.edu/tag/03HK)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 03ZI](https://stacks.math.columbia.edu/tag/03ZI)
* [Stacks Project, Tag 03ZJ](https://stacks.math.columbia.edu/tag/03ZJ)
* [Stacks Project, Tag 03ZK](https://stacks.math.columbia.edu/tag/03ZK)
* [Stacks Project, Tag 04G1](https://stacks.math.columbia.edu/tag/04G1)
* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 05W0](https://stacks.math.columbia.edu/tag/05W0)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 05W2](https://stacks.math.columbia.edu/tag/05W2)
* [Stacks Project, Tag 06CQ](https://stacks.math.columbia.edu/tag/06CQ)
* [Stacks Project, Tag 06G6](https://stacks.math.columbia.edu/tag/06G6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u u₁ v₁ u₂ v₂

namespace AlgebraicGeometry

/-- G-unramifiedness of a morphism of schemes is unramifiedness together with being locally
of finite presentation.

Both sides are split by [Stacks Project, Tag 02HE]; the only thing to check is that a
morphism which is locally of finite presentation is locally of finite type. -/
private lemma gUnramified_iff_unramified_and_locallyOfFinitePresentation {X Y : Scheme.{u}}
    (f : X ⟶ Y) : GUnramified f ↔ (Unramified f ∧ LocallyOfFinitePresentation f) := by
  constructor
  · intro hg
    obtain ⟨hpres, hform⟩ :=
      (gUnramified_iff_locallyOfFinitePresentation_and_formallyUnramified f).mp hg
    exact ⟨(unramified_iff_locallyOfFiniteType_and_formallyUnramified f).mpr
      ⟨inferInstance, hform⟩, hpres⟩
  · rintro ⟨hunr, hpres⟩
    exact (gUnramified_iff_locallyOfFinitePresentation_and_formallyUnramified f).mpr
      ⟨hpres, ((unramified_iff_locallyOfFiniteType_and_formallyUnramified f).mp hunr).2⟩

/-- An immersion of schemes is unramified.

An immersion is a monomorphism, so its relative diagonal is an isomorphism and it is formally
unramified, and it is locally of finite type; now apply [Stacks Project, Tag 02HE]. -/
@[ega "IV 17.1.3" "(i), special case", sga "1 I 3.5" "more general"]
private lemma unramified_of_isImmersion {X Y : Scheme.{u}} (g : X ⟶ Y) [IsImmersion g] :
    Unramified g :=
  (unramified_iff_locallyOfFiniteType_and_formallyUnramified g).mpr
    ⟨inferInstance, inferInstance⟩

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_Unramified :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_Unramified
    {X' Y' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ Z') (g : Y' ⟶ Z') :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_Unramified B S hS).has_limit _

/-! ### Composition, base change and cancellation -/

/-- **Stacks 03ZI.** The composite of two unramified morphisms of algebraic spaces over `S`
is unramified.

Unramifiedness of scheme morphisms is étale local on the source and target and stable under
composition, so this is the instance of [Stacks Project, Tag 0AML] at that property. -/
@[stacks 03ZI]
theorem isUnramified_comp (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsUnramified B S hS f) (hg : IsUnramified B S hS g) :
    IsUnramified B S hS (f ≫ g) :=
  holdsOnEveryEtaleChart_comp B S hS
    (@_root_.AlgebraicGeometry.Unramified.{u} : MorphismProperty Scheme.{u})
    unramified_isEtaleLocalOnSourceAndTarget hX hY hZ f g hf hg

/-- Unramifiedness, as a property of morphisms of the category of algebraic spaces over `S`, is
stable under composition. This is `AlgebraicGeometry.Space.isUnramified_comp` with the
algebraicity of the three objects supplied by the objects themselves. -/
theorem isUnramified_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsUnramified B S hS f.hom) where
  comp_mem {X Y Z} f g hf hg :=
    isUnramified_comp B S hS X.property Y.property Z.property f.hom g.hom hf hg

/-- **Stacks 03ZJ.** Unramified morphisms of algebraic spaces over `S` are stable under base
change.

Unramifiedness of scheme morphisms is étale local on the source and target and stable under
base change, so this is the instance of [Stacks Project, Tag 0AMM] at that property. -/
@[stacks 03ZJ, sga "1 I 3.5" "(iii)"]
theorem isUnramified_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsUnramified B S hS f.hom) :=
  holdsOnEveryEtaleChart_isStableUnderBaseChange B S hS
    (@_root_.AlgebraicGeometry.Unramified.{u} : MorphismProperty Scheme.{u})
    unramified_isEtaleLocalOnSourceAndTarget

/-- **Stacks 06G6.** If a composite of morphisms of algebraic spaces over `S` is unramified,
then so is its first factor.

Lift a surjective étale atlas of `Z` through `g` and the resulting chart of `Y` through `f`,
by [Stacks Project, Tag 02X1]. The scheme morphism on top of the outer square is unramified
by hypothesis, hence so is its first factor by [Stacks Project, Tag 02GG]; that is one
surjective étale square for `f`, which suffices by [Stacks Project, Tag 03MJ]. -/
@[stacks 06G6]
theorem isUnramified_of_comp (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : IsUnramified B S hS (f ≫ g)) : IsUnramified B S hS f := by
  obtain ⟨W, qW, hWSurj, hWEtale⟩ := hZ.exists_atlas
  obtain ⟨V, qV, α, hV, hVSurj, hVEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hY hZ g W qW hWSurj hWEtale
  obtain ⟨U, pU, β, hU, hUSurj, hUEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V qV hVSurj hVEtale
  have hcomm : yoneda.map (β ≫ α) ≫ qW = pU ≫ (f ≫ g) := by
    simp only [Functor.map_comp, Category.assoc, ← hV]
    rw [← Category.assoc, ← hU, Category.assoc]
  have hβ : _root_.AlgebraicGeometry.Unramified
      ((BigFppfOver.toScheme B S hS).map β) := by
    have : _root_.AlgebraicGeometry.Unramified
        ((BigFppfOver.toScheme B S hS).map β ≫ (BigFppfOver.toScheme B S hS).map α) := by
      simpa only [Functor.map_comp] using hfg U W pU qW (β ≫ α) hUEtale hWEtale hcomm
    exact unramified_of_comp ((BigFppfOver.toScheme B S hS).map β)
      ((BigFppfOver.toScheme B S hS).map α)
  exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@_root_.AlgebraicGeometry.Unramified.{u} : MorphismProperty Scheme.{u})
    unramified_isEtaleLocalOnSourceAndTarget hX hY f).2
      ⟨U, V, pU, qV, β, hUEtale, hVEtale, hUSurj, hU.symm, hβ⟩

/-- **Stacks 06CQ.** An immersion of algebraic spaces over `S` is unramified.

An immersion is representable, so an atlas `b` of the target pulls back to a surjective étale
chart `a` of the source over an immersion `α` of schemes; `α` is unramified, and that one
surjective étale square suffices by [Stacks Project, Tag 03MJ]. -/
@[stacks 06CQ]
theorem isUnramified_of_isImmersion (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y} (hf : IsImmersion B S hS f) :
    IsUnramified B S hS f := by
  let T := BigFppfOver.toScheme B S hS
  let QSurj : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) T
  let QEtale : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T
  have : QSurj.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS inferInstance
  have : QEtale.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS
      _root_.AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
  have : QSurj.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange QSurj
  have : QEtale.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange QEtale
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
  obtain ⟨hfRep, hfProp⟩ := hf
  obtain ⟨U, α, a, hpb⟩ := hfRep b
  have : _root_.AlgebraicGeometry.IsImmersion (T.map α) := hfProp b a α hpb
  have haSurj : QSurj.presheaf a :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hbSurj
  have haEtale : QEtale.presheaf a :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hbEtale
  exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@_root_.AlgebraicGeometry.Unramified.{u} : MorphismProperty Scheme.{u})
    unramified_isEtaleLocalOnSourceAndTarget hX hY f).2
      ⟨U, V, a, b, α, haEtale, hbEtale, haSurj, hpb.w.symm, unramified_of_isImmersion (T.map α)⟩

/-! ### G-unramifiedness and local quasi-finiteness -/

/-- **Stacks 04G1.** A morphism of algebraic spaces over `S` is G-unramified exactly when it
is unramified and locally of finite presentation.

All three properties are conditions on every commuting square of étale charts, so the
statement is the scheme-level equivalence
`AlgebraicGeometry.gUnramified_iff_unramified_and_locallyOfFinitePresentation` quantified over
the charts, together with the distribution of a universal quantifier over a conjunction. -/
@[stacks 04G1]
theorem isGUnramified_iff_isUnramified_and_isLocallyOfFinitePresentation (f : X ⟶ Y) :
    IsGUnramified B S hS f ↔
      (IsUnramified B S hS f ∧ IsLocallyOfFinitePresentation B S hS f) := by
  constructor
  · intro hf
    exact ⟨fun U V a b h ha hb hsq =>
        ((gUnramified_iff_unramified_and_locallyOfFinitePresentation _).mp
          (hf U V a b h ha hb hsq)).1,
      fun U V a b h ha hb hsq =>
        ((gUnramified_iff_unramified_and_locallyOfFinitePresentation _).mp
          (hf U V a b h ha hb hsq)).2⟩
  · intro ⟨hunr, hpres⟩ U V a b h ha hb hsq
    exact (gUnramified_iff_unramified_and_locallyOfFinitePresentation _).mpr
      ⟨hunr U V a b h ha hb hsq, hpres U V a b h ha hb hsq⟩

/-- **Stacks 05W0**, the pointwise statement: a morphism of algebraic spaces over `S` which is
unramified at a point of its source is quasi-finite at that point.

The open subspace witnessing unramifiedness at the point witnesses quasi-finiteness there, by
the global statement applied to the restriction of the morphism. -/
@[stacks 05W0 "pointwise statement"]
theorem isQuasiFiniteAt_of_isUnramifiedAt {f : X ⟶ Y} {x : points B S hS X}
    (hf : IsUnramifiedAt B S hS f x) : IsQuasiFiniteAt B S hS f x := by
  obtain ⟨U, hU, x', hx', hunr⟩ := hf
  exact ⟨U, hU, x', hx', isLocallyQuasiFinite_of_isUnramified B S hS _ hunr⟩

/-! ### The relative diagonal -/

/-- If the morphism of representables induced by `α` is étale, then so is the morphism of
schemes underlying `α`. -/
private theorem etale_map_of_isEtale_yoneda_map {U V : BigFppfOver B S hS} (α : U ⟶ V)
    (h : IsEtale B S hS (yoneda.map α)) :
    _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map α) := by
  let _ := isMultiplicative_presheaf_etale B S hS
  have hmap := h U (𝟙 _) (MorphismProperty.id_mem _ _)
  simp only [Category.id_comp] at hmap
  exact MorphismProperty.of_relative_map
    (P := MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) hmap

/-- Étaleness of a morphism of algebraic spaces over `S` which is relatively representable is
étaleness of each of its represented base changes.

Étaleness of scheme morphisms is étale local on the source and target, stable under base
change and local on the base for the fppf topology, so the every-chart condition of
[Stacks Project, Tag 03MJ] for a relatively representable morphism is exactly the relative
morphism property. The every-chart condition follows from the chart condition defining
`AlgebraicGeometry.Space.IsEtale` by [Stacks Project, Tag 03FV]: the morphism of charts is a
morphism over the target, both of whose legs are étale. -/
private theorem presheaf_etale_of_relativelyRepresentable (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f) (hf : IsEtale B S hS f) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  let _ := _root_.AlgebraicGeometry.Etale.etale_isStableUnderBaseChange.{u}
  let P := (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf
  let _ := isMultiplicative_presheaf_etale B S hS
  refine (holdsOnEveryEtaleChart_iff_relative B S hS
    (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    _root_.AlgebraicGeometry.etale_isEtaleLocalOnSourceAndTarget hX hY f hrep).mp ?_
  intro U V a b α ha hb heq
  exact etale_map_of_isEtale_yoneda_map B S hS α
    (isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_yoneda B S hS V) hY (yoneda.map α) (a ≫ f) b
      (isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS ha) hf)
      (isEtale_of_presheaf_etale B S hS hb) heq)

/-- The relative diagonal of an étale chart of an algebraic space over `S` is étale.

The chart is étale after every represented base change, hence so are the two projections of
its fibre product with itself and their common composite with the chart; the relative
diagonal is a morphism over that composite with étale legs, so
[Stacks Project, Tag 03FV] applies. -/
private theorem isEtale_pullbackDiagonal_of_presheaf_etale
    (hY : IsAlgebraicSpace B S hS Y) (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ Y)
    (hv : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf v) :
    IsEtale B S hS (pullback.diagonal v) := by
  let P := (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf
  let _ := isMultiplicative_presheaf_etale B S hS
  let _ : P.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hcomp : P (pullback.fst v v ≫ v) :=
    P.comp_mem (pullback.fst v v) v (P.pullback_fst v v hv) hv
  exact isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS V)
    (isAlgebraicSpace_pullback B S hS v v (isAlgebraicSpace_yoneda B S hS V)
      (isAlgebraicSpace_yoneda B S hS V) hY)
    hY (pullback.diagonal v) v (pullback.fst v v ≫ v) (isEtale_of_presheaf_etale B S hS hv)
    (isEtale_of_presheaf_etale B S hS hcomp) (by simp)

/-- A functor preserving fibre products carries the relative diagonal of a morphism to the
relative diagonal of its image, up to the comparison isomorphism of fibre products. -/
private theorem map_pullbackDiagonal {C : Type u₁} [Category.{v₁} C] [HasPullbacks C]
    {D : Type u₂} [Category.{v₂} D] [HasPullbacks D] (F : C ⥤ D)
    [PreservesLimitsOfShape WalkingCospan F] {U V : C} (α : U ⟶ V) :
    F.map (pullback.diagonal α) ≫ (PreservesPullback.iso F α α).hom =
      pullback.diagonal (F.map α) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, PreservesPullback.iso_hom_fst, ← F.map_comp,
      pullback.diagonal_fst, F.map_id]
  · simp only [Category.assoc, PreservesPullback.iso_hom_snd, ← F.map_comp,
      pullback.diagonal_snd, F.map_id]

/-- The relative diagonal of a morphism of the big fppf site of `S` and the relative diagonal
of the underlying morphism of schemes are open immersions together: the functor to schemes
preserves fibre products, so the two differ by the comparison isomorphism. -/
private theorem isOpenImmersion_diagonal_map_iff {U V : BigFppfOver B S hS} (α : U ⟶ V) :
    _root_.AlgebraicGeometry.IsOpenImmersion
        (pullback.diagonal ((BigFppfOver.toScheme B S hS).map α)) ↔
      _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (pullback.diagonal α)) := by
  let _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  rw [← map_pullbackDiagonal (BigFppfOver.toScheme B S hS) α]
  exact MorphismProperty.cancel_right_of_respectsIso
    @_root_.AlgebraicGeometry.IsOpenImmersion _ _

/-- The chart of the relative diagonal of `f : X ⟶ Y` cut out by a commuting square of charts
`p` of `X` over `q` of `Y`: the fibre product of the morphism `α` of the site with itself maps
to the fibre product of `f` with itself. -/
private noncomputable def diagonalChartMap (f : X ⟶ Y) {U V : BigFppfOver B S hS}
    (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (α : U ⟶ V)
    (h : p ≫ f = yoneda.map α ≫ q) :
    yoneda.obj (pullback α α) ⟶ pullback f f :=
  pullback.lift (yoneda.map (pullback.fst α α) ≫ p) (yoneda.map (pullback.snd α α) ≫ p)
    (by
      calc (yoneda.map (pullback.fst α α) ≫ p) ≫ f
          = yoneda.map (pullback.fst α α) ≫ yoneda.map α ≫ q := by
            rw [Category.assoc, h]
        _ = yoneda.map (pullback.snd α α) ≫ yoneda.map α ≫ q := by
            rw [← Category.assoc, ← Category.assoc, ← yoneda.map_comp, ← yoneda.map_comp,
              pullback.condition]
        _ = (yoneda.map (pullback.snd α α) ≫ p) ≫ f := by rw [Category.assoc, h])

/-- The chart of the relative diagonal is étale after every represented base change.

It factors as the comparison isomorphism of fibre products, the base change of the relative
diagonal of the chart `q` of the target, and the base change of the chart `p` of the source
along `f`; all three are étale after every represented base change. -/
private theorem presheaf_etale_diagonalChartMap (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {U V : BigFppfOver B S hS} (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (α : U ⟶ V)
    (h : p ≫ f = yoneda.map α ≫ q)
    (hp : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hq : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (diagonalChartMap B S hS f p q α h) := by
  let P := (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf
  let _ := isMultiplicative_presheaf_etale B S hS
  let _ : P.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hd : P (pullback.diagonal q) :=
    presheaf_etale_of_relativelyRepresentable B S hS (isAlgebraicSpace_yoneda B S hS V)
      (isAlgebraicSpace_pullback B S hS q q (isAlgebraicSpace_yoneda B S hS V)
        (isAlgebraicSpace_yoneda B S hS V) hY)
      (pullback.diagonal q) (relativelyRepresentable_pullbackDiagonal B S hS q
        (isAlgebraicSpace_yoneda B S hS V))
      (isEtale_pullbackDiagonal_of_presheaf_etale B S hS hY V q hq)
  have heq : (PreservesPullback.iso yoneda α α).hom ≫
      pullback.map (yoneda.map α) (yoneda.map α) (yoneda.map α ≫ q) (yoneda.map α ≫ q)
          (𝟙 _) (𝟙 _) q (Category.id_comp _).symm (Category.id_comp _).symm ≫
        (pullback.congrHom h.symm h.symm).hom ≫
          pullback.map (p ≫ f) (p ≫ f) f f p p (𝟙 Y) (by simp) (by simp) =
      diagonalChartMap B S hS f p q α h := by
    apply pullback.hom_ext
    · simp only [diagonalChartMap, pullback.congrHom_hom, pullback.map, Category.assoc,
        pullback.lift_fst_assoc, pullback.lift_fst, Category.comp_id]
      rw [← Category.assoc, PreservesPullback.iso_hom_fst]
    · simp only [diagonalChartMap, pullback.congrHom_hom, pullback.map, Category.assoc,
        pullback.lift_snd_assoc, pullback.lift_snd, Category.comp_id]
      rw [← Category.assoc, PreservesPullback.iso_hom_snd]
  rw [← heq]
  exact P.comp_mem _ _ (P.of_isIso _)
    (P.comp_mem _ _ (P.of_isPullback (pullback_map_diagonal_isPullback
        (yoneda.map α) (yoneda.map α) q) hd)
      (P.comp_mem _ _ (P.of_isIso _) (P.pullbackMap hp hp (by simp) (by simp))))

/-- The square exhibiting the chart of the relative diagonal as a chart: the relative diagonal
of the morphism `α` of the site sits over the relative diagonal of `f`. -/
private theorem diagonalChartMap_comm (f : X ⟶ Y) {U V : BigFppfOver B S hS}
    (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (α : U ⟶ V)
    (h : p ≫ f = yoneda.map α ≫ q) :
    yoneda.map (pullback.diagonal α) ≫ diagonalChartMap B S hS f p q α h =
      p ≫ pullback.diagonal f := by
  apply pullback.hom_ext
  · dsimp [diagonalChartMap]
    rw [Category.assoc, pullback.lift_fst]
    simp only [← Category.assoc, ← yoneda.map_comp, pullback.diagonal_fst, yoneda.map_id,
      Category.id_comp]
    rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
  · dsimp [diagonalChartMap]
    rw [Category.assoc, pullback.lift_snd]
    simp only [← Category.assoc, ← yoneda.map_comp, pullback.diagonal_snd, yoneda.map_id,
      Category.id_comp]
    rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]

/-- A commuting square of surjective étale charts of a morphism of algebraic spaces over `S`,
with the chart of the target an atlas: an atlas of the target lifts through the morphism by
[Stacks Project, Tag 02X1]. -/
private theorem exists_etale_chart_square (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    ∃ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (α : U ⟶ V),
      p ≫ f = yoneda.map α ≫ q ∧
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q := by
  obtain ⟨V, q, hqSurj, hqEtale⟩ := hY.exists_atlas
  obtain ⟨U, p, α, h, hpSurj, hpEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V q hqSurj hqEtale
  exact ⟨U, V, p, q, α, h, hpSurj, hpEtale, hqEtale⟩

/-- **Stacks 05W1, part (2).** A morphism of algebraic spaces over `S` which is locally of
finite type and whose relative diagonal is an open immersion is unramified.

On a commuting square of surjective étale charts the relative diagonal of the morphism `α` of
the site sits over the relative diagonal of `f`, which is étale after every represented base
change because it is an open immersion after every such base change. Both legs of that square
are therefore étale, so the relative diagonal of `α` is étale by
[Stacks Project, Tag 03FV]; it is also a split monomorphism, hence universally injective, so
it is an open immersion by [Stacks Project, Tag 02LC]. Now `α` is unramified by
[Stacks Project, Tag 02GE], and one surjective étale square suffices by
[Stacks Project, Tag 03MJ]. -/
@[stacks 05W1 "part (2)"]
theorem isUnramified_of_isOpenImmersion_pullbackDiagonal (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hft : IsLocallyOfFiniteType B S hS f)
    (hdiag : IsOpenImmersion B S hS (pullback.diagonal f)) :
    IsUnramified B S hS f := by
  obtain ⟨U, V, p, q, α, h, hpSurj, hpEtale, hqEtale⟩ :=
    exists_etale_chart_square B S hS hX hY f
  set T := BigFppfOver.toScheme B S hS
  let P := (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf
  let _ := isMultiplicative_presheaf_etale B S hS
  let _ : _root_.AlgebraicGeometry.LocallyOfFiniteType (T.map α) :=
    hft U V p q α hpEtale hqEtale h.symm
  have hdiagEtale : P (pullback.diagonal f) :=
    MorphismProperty.relative_monotone (F := yoneda)
      (P := MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) T)
      (P' := MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T)
      (by
        intro A C g hg
        have : _root_.AlgebraicGeometry.IsOpenImmersion (T.map g) := hg
        change _root_.AlgebraicGeometry.Etale (T.map g)
        infer_instance) _ hdiag
  have hbEtale := presheaf_etale_diagonalChartMap B S hS hY f p q α h hpEtale hqEtale
  have hMapSpace : IsEtale B S hS (yoneda.map (pullback.diagonal α)) :=
    isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_yoneda B S hS (pullback α α))
      (isAlgebraicSpace_pullback B S hS f f hX hX hY)
      (yoneda.map (pullback.diagonal α)) (p ≫ pullback.diagonal f)
      (diagonalChartMap B S hS f p q α h)
      (isEtale_of_presheaf_etale B S hS (P.comp_mem p _ hpEtale hdiagEtale))
      (isEtale_of_presheaf_etale B S hS hbEtale)
      (diagonalChartMap_comm B S hS f p q α h)
  let _ := etale_map_of_isEtale_yoneda_map B S hS (pullback.diagonal α) hMapSpace
  let _ : IsSplitMono (T.map (pullback.diagonal α)) :=
    ⟨⟨⟨T.map (pullback.fst α α), by rw [← T.map_comp, pullback.diagonal_fst, T.map_id]⟩⟩⟩
  let _ : _root_.AlgebraicGeometry.IsOpenImmersion (pullback.diagonal (T.map α)) :=
    (isOpenImmersion_diagonal_map_iff B S hS α).mpr
      (_root_.AlgebraicGeometry.isOpenImmersion_of_etale_universallyInjective
        (T.map (pullback.diagonal α)))
  exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@_root_.AlgebraicGeometry.Unramified.{u} : MorphismProperty Scheme.{u})
    unramified_isEtaleLocalOnSourceAndTarget hX hY f).2
      ⟨U, V, p, q, α, hpEtale, hqEtale, hpSurj, h.symm,
        _root_.AlgebraicGeometry.Unramified.of_isOpenImmersion_diagonal (T.map α)⟩

/-! ### The local criteria -/

/-- **Stacks 03ZK.** Nine criteria for a morphism of algebraic spaces over `S` to be
unramified: pointwise unramifiedness, unramifiedness of every base change to a scheme or to an
affine scheme or to one surjective étale chart of the target, unramifiedness of the composite
with one surjective étale chart of the source, unramifiedness of the morphism of schemes in
every — or in one surjective — commuting square of étale charts, or over a pair of Zariski
coverings.

Unramifiedness of morphisms of schemes is étale local on the source and target
([Stacks Project, Tag 04R3]), stable under composition ([Stacks Project, Tag 02G9]) and under
base change ([Stacks Project, Tag 02GA]), and implied by étaleness, so this is the instance of
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_tfae` — Stacks 03MM for an arbitrary such
property — at that property. Condition (2) is `AlgebraicGeometry.Space.IsUnramifiedAt`, which
is by definition condition (2) of that theorem. -/
@[stacks 03ZK]
theorem isUnramified_tfae (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) :
    List.TFAE [
      IsUnramified B S hS f,
      ∀ x : points B S hS X, IsUnramifiedAt B S hS f x,
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsUnramified B S hS (pullback.fst g f),
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) → IsUnramified B S hS (pullback.fst g f),
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        IsSurjective B S hS g ∧ IsEtale B S hS g ∧ IsUnramified B S hS (pullback.fst g f),
      ∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
        IsSurjective B S hS p ∧ IsEtale B S hS p ∧ IsUnramified B S hS (p ≫ f),
      ∀ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p → IsEtale B S hS q → p ≫ f = yoneda.map a ≫ q →
          IsUnramified B S hS (yoneda.map a),
      ∃ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p ∧ IsEtale B S hS q ∧ IsSurjective B S hS p ∧
          p ≫ f = yoneda.map a ≫ q ∧ IsUnramified B S hS (yoneda.map a),
      ∃ (I : Type u) (Yopen : I → Subfunctor Y) (J : I → Type u)
        (Xopen : ∀ i, J i → Subfunctor (pullback f (Yopen i).ι)),
        IsZariskiCover B S hS I Yopen ∧ (∀ i, IsZariskiCover B S hS (J i) (Xopen i)) ∧
          ∀ i j, IsUnramified B S hS ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι)
    ] :=
  holdsOnEveryEtaleChart_tfae B S hS
    (@_root_.AlgebraicGeometry.Unramified.{u} : MorphismProperty Scheme.{u})
    unramified_isEtaleLocalOnSourceAndTarget inferInstance inferInstance
    (fun g _ => _root_.AlgebraicGeometry.unramified_of_etale g) hX hY f

/-! ### The unramified locus -/

section UnramifiedLocus

attribute [local instance] pointTopology

/-- The set of points at which a morphism of algebraic spaces over `S` is unramified is open.

By the definition of `AlgebraicGeometry.Space.IsUnramifiedAt` that set is the union, over the
open subspaces of the source along which the morphism becomes unramified, of their point sets,
and the point set of an open subspace is open by part (1) of [Stacks Project, Tag 03BZ]. -/
theorem isOpen_setOf_isUnramifiedAt (f : X ⟶ Y) :
    IsOpen {x : points B S hS X | IsUnramifiedAt B S hS f x} := by
  have hunion : {x : points B S hS X | IsUnramifiedAt B S hS f x} =
      ⋃ U : {U : Subfunctor X // IsOpenSubspace B S hS U ∧ IsUnramified B S hS (U.ι ≫ f)},
        Set.range (pointsMap B S hS U.1.toFunctor U.1.ι) := by
    ext x
    constructor
    · rintro ⟨U, hU, x', hx', hUf⟩
      exact Set.mem_iUnion.mpr ⟨⟨U, hU, hUf⟩, x', hx'⟩
    · intro hx
      obtain ⟨U, x', hx'⟩ := Set.mem_iUnion.mp hx
      exact ⟨U.1, U.2.1, x', hx', U.2.2⟩
  rw [hunion]
  exact isOpen_iUnion fun U =>
    isOpen_range_pointsMap_of_isOpenImmersion B S hS U.1.ι U.2.1.2

/-- **Stacks 05W2, part (1).** The open subspace of the source of a morphism of algebraic
spaces over `S` cut out by the points at which the morphism is unramified.

Openness of that set of points is `AlgebraicGeometry.Space.isOpen_setOf_isUnramifiedAt`, and
the open subspace realizing it is produced by the correspondence of part (1) of
[Stacks Project, Tag 03BZ] between the open subspaces of an algebraic space and the open
subsets of its point space. No finiteness hypothesis is needed, because unramifiedness at a
point is stated as the existence of an open subspace on which the morphism is unramified; the
source's local-finite-type assumption is only used for its part (2). -/
@[stacks 05W2 "part (1): the open unramified locus"]
noncomputable def unramifiedLocus (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    {U : Subfunctor X // IsOpenSubspace B S hS U} :=
  (openSubspacesOrderIso B S hS X hX).symm
    ⟨{x | IsUnramifiedAt B S hS f x}, isOpen_setOf_isUnramifiedAt B S hS f⟩

/-- **Stacks 05W2, part (1).** The points of `AlgebraicGeometry.Space.unramifiedLocus` are
exactly the points at which the morphism is unramified. -/
@[stacks 05W2 "part (1): the points of the open unramified locus"]
theorem range_pointsMap_unramifiedLocus (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    Set.range (pointsMap B S hS (unramifiedLocus B S hS hX f).1.toFunctor
        (unramifiedLocus B S hS hX f).1.ι) =
      {x : points B S hS X | IsUnramifiedAt B S hS f x} := by
  rw [← openSubspacesOrderIso_apply B S hS X hX (unramifiedLocus B S hS hX f)]
  simp only [unramifiedLocus, OrderIso.apply_symm_apply]

end UnramifiedLocus

end Space

end AlgebraicGeometry

end
