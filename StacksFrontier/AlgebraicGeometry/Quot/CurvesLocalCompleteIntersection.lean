module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOfProperMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Syntomic
public import StacksFrontier.AlgebraicGeometry.Stacks.SubstackFactorizationPresentation

/-!
# Local complete intersection families of curves (Stacks 0DZV)

Stacks 0DZV produces the open substack `Curves^{lci} ⊂ Curves` of those families of curves whose
structure morphism is a local complete intersection morphism, and characterizes it in two ways:
on an arbitrary family of curves, by that condition and equivalently by syntomicity of the
structure morphism; and on a proper scheme of dimension at most one over a field, by the scheme
being a local complete intersection over the field.

The unconditional ingredients of that statement are proved here. For a family of curves the
structure morphism is flat, so being a local complete intersection morphism and being syntomic
are the same condition on it; that condition is stable under base change along a morphism of
families, so it cuts a strictly full subcategory out of the category of families of curves; and
for the family attached to a proper flat morphism of schemes of finite presentation whose source
has dimension at most one, it is the local complete intersection property of that morphism of
schemes — in particular, over a field, of the proper scheme over that field.

## Main definitions

* `AlgebraicGeometry.IsLciFamily`: the defining condition of `Curves^{lci}`, condition (b) of
  part (1) of the source.
* `AlgebraicGeometry.CurvesLci`: the strictly full subcategory `Curves^{lci}` of families of
  curves cut out by that condition.

## Main results

* `AlgebraicGeometry.isLciFamily_iff_isSyntomicFamily`: **Stacks 0DZV**, part (1), the
  equivalence of (b) and (c).
* `AlgebraicGeometry.curvesLci_isStrictlyFull`: **Stacks 0DZV**, strict fullness of
  `Curves^{lci}`.
* `AlgebraicGeometry.isLciFamily_curveFamilyOfSchemeMorphism_iff`: **Stacks 0DZV**, part (2),
  condition (b) read on the family of curves attached to a morphism of schemes.
* `AlgebraicGeometry.factorsThroughCurvesLci_iff`: the factorization criterion of Stacks 0507
  for an open substack of an algebraic stack over families of curves cut out by the condition.
* `AlgebraicGeometry.factorsThroughCurvesLci_over_field_iff`: its instance over a field.

The open substack `Curves^{lci}` of the algebraic stack of curves and the two parts of Stacks
0DZV on it are in `StacksFrontier.AlgebraicGeometry.Quot.CurvesLocalCompleteIntersectionOpenSubstack`
(`AlgebraicGeometry.exists_openSubstack_curvesLci`).

## Implementation notes

The two factorization criteria below are stated for an arbitrary algebraic stack `𝒳` with a
functor `Φ` to families of curves and an open substack `V` of `𝒳` whose objects are those sent to
families with the condition, all three given as arguments. What they add to
`AlgebraicGeometry.Stack.exists_based_factorization_iff` of Stacks 0507 is the translation of
membership of the substack into the condition on the corresponding family. They do not construct
`Curves^{lci}`; that is done, on the algebraic stack of curves of Stacks 0D5A
(`AlgebraicGeometry.curvesFiberedCategory_isAlgebraicStack`), in
`AlgebraicGeometry.curvesLci`. The remaining declarations are unconditional.

The equivalence of (1)(b) and (1)(c) is the source's first step. Syntomicity of a morphism of
algebraic spaces is flatness together with the local complete intersection property, which is
`AlgebraicGeometry.Space.isSyntomic_iff_isFlat_and_isLocalCompleteIntersection` of Stacks 06C9 —
the space-level form of More on Morphisms of Spaces, Lemma 76.48.6 cited in the source — and the
structure morphism of a family of curves is flat by `AlgebraicGeometry.CurveFamily.flat`. The
flatness hypothesis is therefore discharged from the family and the equivalence is not a
restatement of either definition.

Strict fullness goes through syntomicity rather than directly. The local complete intersection
property of morphisms of algebraic spaces is stable under base change only along a flat morphism
(Stacks 069I), and the base morphism of a morphism of families of curves is not assumed flat;
syntomicity, on the other hand, is stable under arbitrary base change by Stacks 03Z9, and for a
family of curves the two conditions agree. This is also what makes the condition invariant under
isomorphism of families, an isomorphism being in particular a morphism of families.

Part (2) is read on `AlgebraicGeometry.curveFamilyOfSchemeMorphism`, the family of curves
attached to a proper flat morphism of schemes of finite presentation whose source has dimension
at most one, exactly as part (2) of Tag 0DZZ is. Its proof again passes through syntomicity: the
every-étale-chart condition of Stacks 03MJ at a morphism of the site is the scheme-level
condition itself for a property étale local on the source and target, which syntomicity is by
Stacks 04R3, and at the scheme level syntomicity is flatness together with the local complete
intersection property by Stacks 069K. Being a local complete intersection over a field is, in the
source as here, the local complete intersection property of the structure morphism to the
spectrum of that field; `AlgebraicGeometry.isLciFamily_curveFamilyOfSchemeMorphism_iff` holds over
an arbitrary base scheme of the site, the field playing no role, and
`AlgebraicGeometry.factorsThroughCurvesLci_over_field_iff` is the instance over a field that the
source states.

The two conditions making `Curves^{lci}` an open substack beyond strict fullness — that the full
subcategory is an algebraic stack and that its inclusion is an open immersion — are not proved in
this file. The source deduces them from Stacks 06CE, the openness and base-change compatibility of
the locus in the base over which a family is a local complete intersection morphism
(`AlgebraicGeometry.Space.exists_isOpenSubspace_factorsThrough_iff_isLocalCompleteIntersection`),
which gives condition (o) of Section 0E0E (`AlgebraicGeometry.isOpenCurvesLocus_isLciFamily`);
the open substack is `AlgebraicGeometry.curvesLci`.

## References

* [Stacks Project, Tag 0DZV](https://stacks.math.columbia.edu/tag/0DZV)
* [Stacks Project, Tag 03Z9](https://stacks.math.columbia.edu/tag/03Z9)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
* [Stacks Project, Tag 069K](https://stacks.math.columbia.edu/tag/069K)
* [Stacks Project, Tag 06C4](https://stacks.math.columbia.edu/tag/06C4)
* [Stacks Project, Tag 06C9](https://stacks.math.columbia.edu/tag/06C9)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0DZZ](https://stacks.math.columbia.edu/tag/0DZZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The defining condition of `Curves^{lci}`: the structure morphism of the family of curves is a
local complete intersection morphism in the sense of part (1) of Tag 06C4. This is condition (b)
of part (1) of Tag 0DZV. -/
abbrev IsLciFamily (X : CurveFamily B hZ) : Prop :=
  Space.IsLocalCompleteIntersection B integerBase hZ X.toBase.hom

/-- **Stacks 0DZV, part (1).** The equivalence of conditions (b) and (c): a family of curves has
a local complete intersection structure morphism exactly when its structure morphism is syntomic.

A syntomic morphism of algebraic spaces is one which is flat and a local complete intersection
morphism, by Tag 06C9, and the structure morphism of a family of curves is flat, so the flatness
half of that conjunction is supplied by the family itself. -/
@[stacks 0DZV "part (1), the equivalence of (b) and (c) for a family of curves: its structure \
morphism is a local complete intersection morphism if and only if it is syntomic"]
theorem isLciFamily_iff_isSyntomicFamily (X : CurveFamily B hZ) :
    IsLciFamily B hZ X ↔ Space.IsSyntomic B integerBase hZ X.toBase.hom := by
  have h := Space.isSyntomic_iff_isFlat_and_isLocalCompleteIntersection B integerBase hZ
    X.toBase.hom
  exact ⟨fun hX => h.mpr ⟨X.flat, hX⟩, fun hX => (h.mp hX).2⟩

/-- A family of curves mapping to a family of curves with local complete intersection structure
morphism has one too: it is a base change of it, and for families of curves the condition is
syntomicity, which is stable under arbitrary base change by Tag 03Z9.

The detour through syntomicity is what makes this unconditional: the local complete intersection
property of morphisms of algebraic spaces is stable under base change along a *flat* morphism,
and the morphism of base schemes of a morphism of families of curves is not assumed flat. -/
theorem CurveFamily.isLciFamily_of_hom {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hY : IsLciFamily B hZ Y) : IsLciFamily B hZ X :=
  have h : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B integerBase hZ⦄ (k : F ⟶ G) =>
        Space.IsSyntomic B integerBase hZ k.hom) :=
    Space.isSyntomic_isStableUnderBaseChange B integerBase hZ
  (isLciFamily_iff_isSyntomicFamily B hZ X).mpr
    (h.of_isPullback φ.cartesian ((isLciFamily_iff_isSyntomicFamily B hZ Y).mp hY))

/-- A family of curves has a local complete intersection structure morphism exactly when every
family of curves mapping to it does; that is, exactly when every base change of it does. -/
theorem isLciFamily_iff_forall_hom (X : CurveFamily B hZ) :
    IsLciFamily B hZ X ↔ ∀ Y : CurveFamily B hZ, (Y ⟶ X) → IsLciFamily B hZ Y :=
  ⟨fun hX _ φ => CurveFamily.isLciFamily_of_hom B hZ φ hX, fun h => h X (𝟙 X)⟩

/-- **Stacks 0DZV.** The condition that a family of curves have a local complete intersection
structure morphism is invariant under isomorphism, so `Curves^{lci}` is a strictly full
subcategory of the category of families of curves: the first of the three conditions making it an
open substack.

An isomorphism of families of curves is a morphism of families, so this is base-change invariance
of the condition applied to the inverse isomorphism. -/
@[stacks 0DZV "strict fullness of the local complete intersection subcategory of the category of \
families of curves, which is the first of the three conditions of Tag 04YM making it an open \
substack"]
theorem curvesLci_isStrictlyFull :
    (show ObjectProperty (CurveFamily B hZ) from
      IsLciFamily B hZ).IsClosedUnderIsomorphisms :=
  ⟨fun ee hX => CurveFamily.isLciFamily_of_hom B hZ ee.inv hX⟩

/-- The subcategory `Curves^{lci}` of the category of families of curves: the strictly full
subcategory of families of curves whose structure morphism is a local complete intersection
morphism. The open substack `Curves^{lci}` of the algebraic stack of curves of Stacks 0DZV is
`AlgebraicGeometry.curvesLci`. -/
abbrev CurvesLci :=
  (show ObjectProperty (CurveFamily B hZ) from IsLciFamily B hZ).FullSubcategory

/-! ### The condition on a proper scheme over a field -/

/-- **Stacks 0DZV, part (2).** Condition (b) read on the family of curves attached to a proper
flat morphism of schemes of finite presentation whose source has dimension at most one: that
family has a local complete intersection structure morphism exactly when the morphism of schemes
is a local complete intersection morphism.

Over the spectrum of a field the right-hand side is the condition that the proper scheme be a
local complete intersection over that field, which is condition (b) of part (2) of the source;
see `AlgebraicGeometry.factorsThroughCurvesLci_over_field_iff`. No hypothesis on the base is
needed, so the statement is proved over an arbitrary base scheme of the site.

Both sides pass through syntomicity. The every-étale-chart condition of Tag 03MJ at a morphism of
the site is the scheme-level condition itself for a property étale local on the source and target,
which syntomicity is by Tag 04R3; at the level of schemes syntomicity is flatness together with
the local complete intersection property by Tag 069K, and the morphism is flat by hypothesis; at
the level of algebraic spaces it is the same conjunction by Tag 06C9, whose flatness half the
family supplies. -/
@[stacks 0DZV "part (2), condition (b): for the family of curves attached to a proper flat \
morphism of schemes of finite presentation whose source has dimension at most one, the structure \
morphism of the family is a local complete intersection morphism if and only if that morphism of \
schemes is one, i.e. — over the spectrum of a field — if and only if the proper scheme is a local \
complete intersection over the field"]
theorem isLciFamily_curveFamilyOfSchemeMorphism_iff
    {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    IsLciFamily B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      IsLocalCompleteIntersectionMorphism
        ((BigFppfOver.toScheme B integerBase hZ).map g) := by
  change Space.IsLocalCompleteIntersection B integerBase hZ (schemeSpaceMap g).hom ↔ _
  have hspace := Space.isSyntomic_iff_isFlat_and_isLocalCompleteIntersection B integerBase hZ
    (schemeSpaceMap g).hom
  have hchart : Space.IsSyntomic B integerBase hZ (schemeSpaceMap g).hom ↔
      Syntomic ((BigFppfOver.toScheme B integerBase hZ).map g) :=
    Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      syntomic_isEtaleLocalOnSourceAndTarget g
  have hscheme := syntomic_iff_flat_and_isLocalCompleteIntersectionMorphism
    ((BigFppfOver.toScheme B integerBase hZ).map g)
  have hflatSpace : Space.IsFlat B integerBase hZ (schemeSpaceMap g).hom :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      Flat.isEtaleLocalOnSourceAndTarget g).2 hflat
  exact ⟨fun h => (hscheme.mp (hchart.mp (hspace.mpr ⟨hflatSpace, h⟩))).2,
    fun h => (hspace.mp (hchart.mpr (hscheme.mpr ⟨hflat, h⟩))).2⟩

/-! ### The factorization criteria -/

/-- **The factorization criterion for an open substack cut out by the condition.** Let `𝒳` be
an algebraic stack over the big fppf site of the integers whose objects are identified with
families of curves by `Φ`, and let `V` be an open substack of `𝒳` whose objects are exactly those
identified with families having a local complete intersection structure morphism. Then a
1-morphism into `𝒳` from a category over the site factors through `V`, over the site and up to a
2-isomorphism, if and only if every family of curves in its image has a local complete
intersection structure morphism.

The algebraic stack `𝒳`, the functor `Φ` and the open substack `V` with its specification `hV`
are arguments, so this does not construct an open substack; it is the criterion of Stacks 0507
together with the translation of membership of `V` into the condition on the corresponding
family. Part (1) of Stacks 0DZV on the open substack `Curves^{lci}` of the algebraic stack of
curves is `AlgebraicGeometry.factorsThrough_curvesLci_tfae`. -/
theorem factorsThroughCurvesLci_iff
    {𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ}
    (Φ : 𝒳.val.val.obj ⥤ CurveFamily B hZ) (V : Stack.OpenSubstack 𝒳)
    (hV : ∀ Z : 𝒳.val.val.obj, V.property Z ↔ IsLciFamily B hZ (Φ.obj Z))
    {𝒟 : BasedCategory.{u, u + 1} (BigFppfOver B integerBase hZ)} (f : 𝒟 ⥤ᵇ 𝒳.val.val) :
    (∃ q : 𝒟 ⥤ᵇ Stack.fullSubcategoryBased 𝒳 V.property,
        Nonempty (q.comp (Stack.fullSubcategoryBasedInclusion 𝒳 V.property) ≅ f)) ↔
      ∀ Y : 𝒟.obj, IsLciFamily B hZ (Φ.obj (f.obj Y)) := by
  have := V.strictlyFull
  exact (Stack.exists_based_factorization_iff f).trans (forall_congr' fun Y => hV (f.obj Y))

/-- **The factorization criterion over a field.** The instance of
`AlgebraicGeometry.factorsThroughCurvesLci_iff` for a proper scheme over a field of dimension at
most one. Let `X → Spec(k)` be a proper flat morphism of schemes of finite
presentation over a field `k` whose source has dimension at most one, and let `f` be a 1-morphism
into the stack of curves all of whose objects classify the attached family of curves. Then `f`
factors through the local complete intersection open substack exactly when `X` is a local complete
intersection over `k`, that is, exactly when `X → Spec(k)` is a local complete intersection
morphism.

The hypothesis `_hk` that the base be the spectrum of a field is what makes this the statement of
part (2) of the source rather than a statement over an arbitrary base, and it is deliberately kept
although the argument does not use it: the underlying equivalence
`AlgebraicGeometry.isLciFamily_curveFamilyOfSchemeMorphism_iff` holds over an arbitrary base
scheme of the site, so this statement is a strict instance of it and nothing is weakened by its
presence. Nonemptiness of the source category of `f` is used, to convert the universally
quantified right-hand side of `AlgebraicGeometry.factorsThroughCurvesLci_iff` into the single
condition the source states. Properness, finite presentation, flatness and the dimension bound are
the hypotheses of `AlgebraicGeometry.curveFamilyOfSchemeMorphism` and are all used, through it.

Like `AlgebraicGeometry.factorsThroughCurvesLci_iff` this takes the algebraic stack, the functor
to families of curves and the open substack as arguments. Part (2) of Stacks 0DZV on the open
substack `Curves^{lci}` of the algebraic stack of curves is
`AlgebraicGeometry.factorsThrough_curvesLci_over_field_iff`. -/
theorem factorsThroughCurvesLci_over_field_iff
    {𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ}
    (Φ : 𝒳.val.val.obj ⥤ CurveFamily B hZ) (V : Stack.OpenSubstack 𝒳)
    (hV : ∀ Z : 𝒳.val.val.obj, V.property Z ↔ IsLciFamily B hZ (Φ.obj Z))
    {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (k : Type u) [Field k]
    (_hk : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    {𝒟 : BasedCategory.{u, u + 1} (BigFppfOver B integerBase hZ)} (f : 𝒟 ⥤ᵇ 𝒳.val.val)
    (hne : Nonempty 𝒟.obj)
    (hf : ∀ Y : 𝒟.obj, Φ.obj (f.obj Y) =
      curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) :
    (∃ q : 𝒟 ⥤ᵇ Stack.fullSubcategoryBased 𝒳 V.property,
        Nonempty (q.comp (Stack.fullSubcategoryBasedInclusion 𝒳 V.property) ≅ f)) ↔
      IsLocalCompleteIntersectionMorphism
        ((BigFppfOver.toScheme B integerBase hZ).map g) := by
  rw [factorsThroughCurvesLci_iff B hZ Φ V hV f,
    ← isLciFamily_curveFamilyOfSchemeMorphism_iff B hZ g hflat hproper hlfp hqc hsep hqsep hdim]
  refine ⟨fun h => ?_, fun h Y => ?_⟩
  · obtain ⟨Y⟩ := hne
    rw [← hf Y]
    exact h Y
  · rw [hf Y]
    exact h

end AlgebraicGeometry

end
