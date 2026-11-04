module

public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismFullyFaithful
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeFromMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeLocallyOfFiniteType

/-!
# Finite type points and residual gerbes: the implications (1) ⟹ (2) and (1) ⟹ (3) of Stacks 06G3

Let `𝒳` be an algebraic stack over `S` and let `x ∈ |𝒳|`. **Stacks 06G3** says that the
following are equivalent:

1. `x` is a finite type point;
2. there is an algebraic stack `𝒵` with a one-point space and a locally-of-finite-type
   1-morphism `𝒵 ⟶ 𝒳` whose image on points is `{x}`;
3. the residual gerbe `𝒵_x` of `𝒳` at `x` exists and the inclusion `𝒵_x ⟶ 𝒳` is locally of
   finite type.

`StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointResidualGerbe` states the three conditions
and proves (3) ⟹ (2) and (2) ⟹ (1). This module adds two further steps.

* **(1) ⟹ (2)**,
  `AlgebraicGeometry.Stack.hasSingletonLocallyOfFiniteTypeCoverAt_of_isFiniteTypePoint`. The
  definition of a finite type point used here — `AlgebraicGeometry.Stack.IsFiniteTypePoint`,
  condition (1) of **Stacks 06FX** — hands out a field-valued point representing `x` whose
  1-morphism `Spec k ⟶ 𝒳` is locally of finite type, and the algebraic stack of the spectrum of a
  field has exactly one point. So `Spec k` itself is the one-point algebraic stack condition (2)
  asks for, and no residual gerbe is needed.

* **The half of (1) ⟹ (3) that follows the construction of `𝒵`**,
  `AlgebraicGeometry.Stack.hasLocallyOfFiniteTypeResidualGerbeAt_of_full_of_faithful`: condition
  (3) from a fully faithful `f : 𝒵 ⟶ 𝒳` with image `{x}` whose source carries the cover `z` of
  condition (2) of **Stacks 06MP** and for which `z ≫ f` is locally of finite type. Existence of
  the gerbe from such an `f` is **Stacks 06MX**,
  `AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_full_of_faithful`; local finite type of
  the inclusion is `AlgebraicGeometry.Stack.isLocallyOfFiniteType_of_fieldSpectrumCover_comp`,
  which descends it along the field-spectrum cover of the gerbe, by **Stacks 06U8** at a
  1-morphism that is surjective and flat by **Stacks 06MM** and locally of finite presentation by
  **Stacks 0DQJ**.
  `AlgebraicGeometry.Stack.hasLocallyOfFiniteTypeResidualGerbeAt_of_isMonomorphism` is the same
  statement at a locally-of-finite-type monomorphism.

The construction of such an `f` at a finite type point, and with it the whole of (1) ⟹ (3) and
**Stacks 06G3** itself, is in
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointResidualGerbeExistence`.

## Main results

* `AlgebraicGeometry.Stack.hasSingletonLocallyOfFiniteTypeCoverAt_of_isFiniteTypePoint`:
  (1) ⟹ (2).
* `AlgebraicGeometry.Stack.hasLocallyOfFiniteTypeResidualGerbeAt_of_full_of_faithful`: condition
  (3) from a fully faithful 1-morphism with image `{x}` out of an algebraic stack carrying the
  cover of condition (2) of **Stacks 06MP**, whose composite with that cover is locally of finite
  type.
* `AlgebraicGeometry.Stack.hasLocallyOfFiniteTypeResidualGerbeAt_of_isMonomorphism`: the same at
  a locally-of-finite-type monomorphism, which is the shape the source's proof produces.

## References

* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 05UK](https://stacks.math.columbia.edu/tag/05UK)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06FY](https://stacks.math.columbia.edu/tag/06FY)
* [Stacks Project, Tag 06G3](https://stacks.math.columbia.edu/tag/06G3)
* [Stacks Project, Tag 06MM](https://stacks.math.columbia.edu/tag/06MM)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06MX](https://stacks.math.columbia.edu/tag/06MX)
* [Stacks Project, Tag 06U8](https://stacks.math.columbia.edu/tag/06U8)
* [Stacks Project, Tag 0DQJ](https://stacks.math.columbia.edu/tag/0DQJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Condition (1) of Stacks 06G3 implies its condition (2).** A finite type point is, by the
definition `AlgebraicGeometry.Stack.IsFiniteTypePoint` of **Stacks 06FY**, represented by a
field-valued point whose 1-morphism out of the algebraic stack of the spectrum of its field is
locally of finite type. The spectrum of a field has exactly one point, and that point is carried
to the point the field-valued point represents, so this 1-morphism is already of the kind
condition (2) asks for: no residual gerbe is involved.

The source proves (2) by way of (3) and does not isolate this implication; taking the
field-valued point of condition (1) of **Stacks 06FX** as the one-point algebraic stack avoids
the detour. With
`AlgebraicGeometry.Stack.isFiniteTypePoint_of_hasSingletonLocallyOfFiniteTypeCoverAt` this makes
conditions (1) and (2) of Stacks 06G3 equivalent unconditionally. -/
theorem hasSingletonLocallyOfFiniteTypeCoverAt_of_isFiniteTypePoint
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) :
    HasSingletonLocallyOfFiniteTypeCoverAt.{u, w} B S hS 𝒳 x := by
  obtain ⟨p, hpx, hplft⟩ := hx
  have hsub : Subsingleton (points B S hS (schemeStack.{u, w} B S hS p.base).val.val
      (schemeStack.{u, w} B S hS p.base).val.property) :=
    subsingleton_points_fieldValuedPointBaseStack.{u, w} B S hS p
  have hkey : pointsMap B S hS (schemeStack.{u, w} B S hS p.base).val.val
      (schemeStack.{u, w} B S hS p.base).val.property 𝒳.val.property
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p).hom.hom
      (pointClass B S hS (schemeStack.{u, w} B S hS p.base).val.val
        (schemeStack.{u, w} B S hS p.base).val.property p.atBase) = x :=
    (pointClass_fieldValuedPointMap_atBase B S hS 𝒳.val p).trans hpx
  refine ⟨schemeStack.{u, w} B S hS p.base, fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p,
    ⟨pointClass B S hS (schemeStack.{u, w} B S hS p.base).val.val
      (schemeStack.{u, w} B S hS p.base).val.property p.atBase⟩, hsub, hplft, ?_⟩
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, hkey⟩, ?_⟩
  rintro - ⟨a, rfl⟩
  exact hsub.elim a _ ▸ hkey

/-- **The whole of Stacks 06G3's implication (1) ⟹ (3) after the construction of `𝒵`, from a
fully faithful 1-morphism.** Let `𝒳` be an algebraic stack over `S`, let `𝒵` be an algebraic
stack over `S`, let `z₀ : Spec k ⟶ 𝒵` be a 1-morphism from the algebraic stack of the spectrum of
a field which is locally of finite presentation, surjective and flat — the data of condition (2)
of **Stacks 06MP** — and let `f : 𝒵 ⟶ 𝒳` be a 1-morphism whose underlying functor is full and
faithful, whose image on points is exactly `{x}`, and for which the composite `z₀ ≫ f` is locally
of finite type. Then condition (3) of Stacks 06G3 holds at `x`.

This is `AlgebraicGeometry.Stack.hasLocallyOfFiniteTypeResidualGerbeAt_of_isMonomorphism` with
both of its hypotheses on `f` weakened to what the proof consumes, and both weakenings matter for
the construction of `f` at a finite type point:

* full faithfulness rather than monomorphy, because **Stacks 06MX** uses monomorphy of `f` only
  through **Stacks 05UK**, which turns it into full faithfulness — see
  `AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_full_of_faithful`. The converse
  implication (2) ⟹ (1) of **Stacks 04ZZ** is what needs representability by algebraic spaces,
  hence the bootstrap theorem **Stacks 04S6** part (3); a producer of a *fully faithful*
  1-morphism, such as **Stacks 04T4 (6)** for the canonical 1-morphism out of a quotient stack,
  feeds this statement without it.
* local finite type of `z₀ ≫ f` rather than of `f` itself, because that composite is all that
  `AlgebraicGeometry.Stack.isLocallyOfFiniteType_of_fieldSpectrumCover_comp` descends from. In
  the source's construction `𝒵 = [u/R]` and `z₀` is the projection `u ⟶ [u/R]`, so `z₀ ≫ f` is
  2-isomorphic to the field-valued point `u ⟶ 𝒳` of condition (1) of **Stacks 06FX**, which is
  locally of finite type by the definition of a finite type point. Local finite type of `f` is
  then a *conclusion* of this lemma rather than an input, exactly as in the source, where it is
  the last step of the proof. -/
theorem hasLocallyOfFiniteTypeResidualGerbeAt_of_full_of_faithful
    (𝒳 𝒵 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵 ⟶ 𝒳)
    (hfull : (CatFiberedInGroupoids.homFunctor f.hom).Full)
    (hfaith : (CatFiberedInGroupoids.homFunctor f.hom).Faithful)
    (F : FieldSpectrum B S hS) (z₀ : schemeStack.{u, w} B S hS F.base ⟶ 𝒵)
    (hz₀lfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS z₀)
    (hz₀surj : IsSurjective B S hS z₀)
    (hz₀flat : AlgebraicStacks.IsFlat B S hS z₀)
    (hz₀f : AlgebraicStacks.IsLocallyOfFiniteType B S hS (z₀ ≫ f))
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (himg : Set.range (AlgebraicStacks.pointsMap B S hS f) = {x}) :
    HasLocallyOfFiniteTypeResidualGerbeAt.{u, w} B S hS 𝒳 x := by
  obtain ⟨P, hP, hres, g, -, ⟨α⟩⟩ :=
    exists_isResidualGerbeAt_of_full_of_faithful.{u, w} B S hS 𝒳 𝒵 f hfull hfaith
      ⟨F, z₀, hz₀lfp, hz₀surj, hz₀flat⟩ x himg
  refine ⟨P, hP, hres, ?_⟩
  obtain ⟨-, hP', hredS, hnoeth, z, huniq, -⟩ := hres
  have hredU : IsReducedWithUniquePoint B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP) :=
    ⟨hredS, ⟨z⟩, ⟨fun a b => (huniq a).trans (huniq b).symm⟩⟩
  have hzilft : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      ((z₀ ≫ g) ≫ fullSubcategoryInclusion 𝒳 P hP) :=
    AlgebraicStacks.isLocallyOfFiniteType_of_twoIso B S hS
      (Bicategory.InducedBicategory.isoHom
        ((Bicategory.associator z₀ g (fullSubcategoryInclusion 𝒳 P hP)).trans
          (Bicategory.whiskerLeftIso z₀ α)).symm) hz₀f
  exact isLocallyOfFiniteType_of_fieldSpectrumCover_comp.{u, w} B S hS
    (fullSubcategoryInclusion 𝒳 P hP) hredU hnoeth F (z₀ ≫ g) hzilft

/-- **The whole of Stacks 06G3's implication (1) ⟹ (3) after the construction of `𝒵`.** Let `𝒳`
be an algebraic stack over `S`, let `𝒵` be an algebraic stack over `S` satisfying condition (2)
of **Stacks 06MP**, and let `f : 𝒵 ⟶ 𝒳` be a monomorphism which is locally of finite type and
whose image on points is exactly `{x}`. Then condition (3) of Stacks 06G3 holds at `x`: the
residual gerbe of `𝒳` at `x` exists and its inclusion is locally of finite type.

Existence of the residual gerbe is **Stacks 06MX**
(`AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_isMonomorphism`), which also factors `f`
through the inclusion by a 1-morphism `g`. Local finite type of the inclusion is then
`AlgebraicGeometry.Stack.isLocallyOfFiniteType_of_fieldSpectrumCover_comp` at the field-spectrum
1-morphism `z₀ ≫ g`, where `z₀` is the cover of condition (2) of Stacks 06MP: the composite of
`z₀ ≫ g` with the inclusion is 2-isomorphic to `z₀ ≫ f`, which is locally of finite type because
`z₀` is locally of finite presentation and `f` is locally of finite type by hypothesis.

This is exactly the part of the source's proof of (1) ⟹ (3) that follows the construction of
`𝒵 = [u/R]`: the residual gerbe and the local finite type of its inclusion. What it does not
supply is the monomorphism `f` itself at a finite type point; that construction is
`AlgebraicGeometry.Stack.hasFullyFaithfulFiniteTypeFieldPointPresentations`, which produces a
fully faithful 1-morphism rather than a monomorphism and so feeds
`AlgebraicGeometry.Stack.hasLocallyOfFiniteTypeResidualGerbeAt_of_full_of_faithful` instead. -/
theorem hasLocallyOfFiniteTypeResidualGerbeAt_of_isMonomorphism
    (𝒳 𝒵 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsMonomorphism B S hS f)
    (h𝒵 : HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS 𝒵)
    (hflft : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (himg : Set.range (AlgebraicStacks.pointsMap B S hS f) = {x}) :
    HasLocallyOfFiniteTypeResidualGerbeAt.{u, w} B S hS 𝒳 x := by
  obtain ⟨F, z₀, hz₀lfp, hz₀surj, hz₀flat⟩ := h𝒵
  obtain ⟨hfull, hfaith⟩ :=
    AlgebraicStacks.full_and_faithful_homFunctor_of_isMonomorphism B S hS f hf
  exact hasLocallyOfFiniteTypeResidualGerbeAt_of_full_of_faithful.{u, w} B S hS 𝒳 𝒵 f
    hfull hfaith F z₀ hz₀lfp hz₀surj hz₀flat
    (AlgebraicStacks.isLocallyOfFiniteType_comp B S hS z₀ f
      (AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hz₀lfp)
      hflft) x himg


end AlgebraicGeometry.Stack

end
