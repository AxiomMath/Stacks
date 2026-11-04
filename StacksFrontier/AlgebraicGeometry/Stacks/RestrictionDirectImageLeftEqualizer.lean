module

public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionDirectImageComparison
public import
  StacksFrontier.AlgebraicGeometry.Stacks.RestrictionDirectImageTwoFibreProductRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionFunctorLimits
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.EqualizerOverAnAtlas
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.OneMorphismContinuity

/-!
# The left-hand side of equation 075M at a chart, as an equalizer

Equation 075M of the source asserts `(f_*ℱ)|_{G_étale} = f_{small,*}(ℱ|_{F_étale})`, and
`StacksFrontier/AlgebraicGeometry/Stacks/RestrictionDirectImageComparison.lean` builds the canonical
comparison map between the two sides and reduces its invertibility to bijectivity on sections over
one étale scheme chart `V` of `G` at a time
(`AlgebraicGeometry.Space.isIso_restrictedDirectImageComparison_of_bijective`). The *right*-hand
side is already presented at such a chart as an equalizer of sections over two étale scheme charts
of `F`, by `AlgebraicGeometry.Space.exists_restrictedDirectImageComparisonTarget_equalizer`
(Properties of Spaces 03H7). This file presents the **left**-hand side as an equalizer of the same
shape, so that the comparison becomes a map between two equalizer diagrams.

The left-hand side at `V` is, by `AlgebraicGeometry.Space.restrictedDirectImageChartEquiv`, the
global sections of the pullback of `ℱ` to the 2-fibre product `(Sch/V)_{fppf} ×_𝒴 𝒳`. Turning
global sections into an equalizer over a single object is
`CategoryTheory.Presheaf.globalSectionsEquivEqualizer`, which asks three things of that 2-fibre
product, read as a site for its inherited étale topology:

* that the pullback of `ℱ` along the second projection is a **sheaf** there;
* that a single object `A` **covers the final object**;
* that the two morphisms of the relation **factor pairs** (`CategoryTheory.Presheaf.FactorsPairs`),
  i.e. that their source is a product of `A` with itself.

All three are supplied here. The first is continuity of the second projection, which is a
1-morphism of fibred categories over the big fppf site of `S` because
`CategoryTheory.TwoFibreProductOver.snd_comp_eq` says so, together with Stacks 06NW in the
fibre-product-free form of
`CategoryTheory.Functor.IsFibredOneMorphism.isContinuous_inheritedTopology`. The second is
`AlgebraicGeometry.Space.exists_restrictionFunctor_coversTop_singleton`, Stacks 073M by a single
chart. The third is formal: `AlgebraicGeometry.Space.restrictionFunctor_preservesBinaryProducts`
says the functor from the small étale site of the representing algebraic space preserves binary
products, so the image of `A ⨯ A` is a product of `A` with itself in the 2-fibre product, and
`FactorsPairs` is the existence half of that universal property.

## Main definitions

* `CategoryTheory.Presheaf.factorsPairs_of_isLimit`: `FactorsPairs` holds for the two legs of a
  binary product cone — it *is* the existence half of the universal property.

## Main results

* `CategoryTheory.Functor.isStronglyCartesian_of_isFiberedInGroupoids`: in a category fibred in
  groupoids a morphism is strongly cartesian over every morphism of the base it lifts.
* `AlgebraicGeometry.Space.isFibredOneMorphism_twoFibreProductSnd`: the second projection of the
  2-fibre product of equation 075M is a 1-morphism of fibred categories over the big fppf site
  of `S`.
* `AlgebraicGeometry.Space.isSheaf_comp_twoFibreProductSnd`: the pullback of a sheaf on `𝒳` along
  that projection is a sheaf for the inherited étale topology of the 2-fibre product.
* `AlgebraicGeometry.Space.exists_factorsPairs_restrictionFunctor`: for every étale chart `A` of an
  algebraic space representing a category fibred in groupoids, the image of `A` under the functor
  of Stacks 073M admits a `FactorsPairs` pair, namely the two projections of the image of `A ⨯ A`.
* `Space.exists_restrictedDirectImageComparisonSource_equalizer_of_equivalenceOver`: the
  equalizer presentation for a given presentation of the 2-fibre product.
* `AlgebraicGeometry.Space.exists_isAlgebraicSpace_twoFibreProductStructureFunctor`: the 2-fibre
  product of equation 075M at a chart is represented by an algebraic space over `S`.
* `AlgebraicGeometry.Space.exists_restrictedDirectImageComparisonSource_equalizer`:
  **equation 075M, the left-hand side at a chart, as an equalizer.**

## Implementation notes

**No topology is transported.** The source's proof of Stacks 073N identifies the 2-fibre product
`(Sch/V)_{fppf} ×_𝒴 𝒳` with the split category fibred in groupoids of the algebraic space
`V ×_G F`. No transport of the inherited étale site across that
`CategoryTheory.StacksRepresentableCFG.EquivalenceOver` is needed to state the left-hand side, and
the reason is `CategoryTheory.TwoFibreProductOver.structureFunctor`: the first leg of the cospan of
equation 075M is `CategoryTheory.Over.forget` of a chart, so the structure functor of the 2-fibre
product lands in `AlgebraicGeometry.BigFppfOver B S hS` **itself**, not in a slice of it. The
inherited étale topology of the 2-fibre product is therefore already a topology over the same base
site as the one on `𝒳`, and `AlgebraicGeometry.Space.exists_restrictionFunctor_coversTop_singleton`
— which quantifies over an arbitrary structure functor to `BigFppfOver B S hS` together with the
representing equivalence — applies to it directly. No comparison of two topologies arises anywhere
below.

**The identification of the 2-fibre product is constructed, not assumed.** Representability of the
2-fibre product by an algebraic space over `S` is what the equalizer presentation needs, and it is
`AlgebraicGeometry.Space.exists_isAlgebraicSpace_twoFibreProductStructureFunctor` below, built
from the presentations of `𝒳` and `𝒴` alone by
`AlgebraicGeometry.Space.exists_isAlgebraicSpace_nonempty_equivalenceOver_overForget` of
`StacksFrontier/AlgebraicGeometry/Stacks/RestrictionDirectImageTwoFibreProductRepresentable.lean`.
The identification of the split category fibred in groupoids of a presheaf viewed over a larger
base with that of the presheaf's `CategoryTheory.OverShriek.relocalizePresheafFunctor` is
`CategoryTheory.PresheafOfCategories.relocalizeElementsEquivalenceOver`, and
`CategoryTheory.TwoFibreProductOver.precomposeFst` is the comparison that moves the first factor
of the 2-fibre product from the slice at the chart, over which `CategoryTheory.Over.forget`
presents it here, to the big fppf site of the chart's scheme, over which
`CategoryTheory.PresheafOfCategories.nonempty_equivalenceOver_twoFibreProductPresheaf` presents
the base change.

`AlgebraicGeometry.Space.exists_restrictedDirectImageComparisonSource_equalizer_of_equivalenceOver`
keeps the presentation as a hypothesis, so that the equalizer is still available for an arbitrary
`𝒳` carrying no representability assumption of its own; equation 075M's own statement takes the
hypotheses of 075M — presentations of `𝒳` and `𝒴` by algebraic spaces `F` and `G` — and
constructs the presentation of the 2-fibre product from them.

**Why `FactorsPairs` needs a product and not a fibre product.**
`CategoryTheory.Presheaf.FactorsPairs a b` asks that *every* pair of morphisms into the common
target factor through the common source, with no compatibility required of the pair. That is the
universal property of a binary product, not of a fibre product over the final object of the site —
the two agree here only because the site of charts of an algebraic space has the space itself as
its final object. Stating it through `CategoryTheory.Limits.IsLimit` of a
`CategoryTheory.Limits.BinaryFan`, as `factorsPairs_of_isLimit` does, keeps the proof independent
of that coincidence.

## References

* [Stacks Project, Tag 075M](https://stacks.math.columbia.edu/tag/075M)
* [Stacks Project, Tag 073N](https://stacks.math.columbia.edu/tag/073N)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
* [Stacks Project, Tag 0792](https://stacks.math.columbia.edu/tag/0792)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor

/-- **In a category fibred in groupoids a morphism is strongly cartesian over every morphism of
the base that it lifts.** Every morphism is strongly cartesian over its own image, and the base
morphism is determined by the lifting up to the two identifications of its source and target. -/
theorem isStronglyCartesian_of_isFiberedInGroupoids {𝒞 : Type*} [Category 𝒞] {𝒳 : Type*}
    [Category 𝒳] {p : 𝒳 ⥤ 𝒞} (hp : p.IsFiberedInGroupoids) {R T : 𝒞} (k : R ⟶ T) {a b : 𝒳}
    (φ : a ⟶ b) (h : p.IsHomLift k φ) : p.IsStronglyCartesian k φ := by
  have hsc := hp.isStronglyCartesian φ
  have h' := h
  subst_hom_lift p k φ
  exact hsc

end CategoryTheory.Functor

namespace CategoryTheory.Presheaf

/-- **The two legs of a binary product cone factor pairs.** `FactorsPairs a b` asks of
`a b : V ⟶ U` that every pair of morphisms `f g : Z ⟶ U` be `h ≫ a` and `h ≫ b` for a common
`h : Z ⟶ V`, which is exactly the existence half of the universal property exhibiting `V` as a
product of `U` with itself. -/
theorem factorsPairs_of_isLimit {C : Type*} [Category C] {U V : C} {a b : V ⟶ U}
    (h : IsLimit (BinaryFan.mk a b)) : FactorsPairs a b := fun _ f g =>
  ⟨h.lift (BinaryFan.mk f g), h.fac (BinaryFan.mk f g) ⟨WalkingPair.left⟩,
    h.fac (BinaryFan.mk f g) ⟨WalkingPair.right⟩⟩

end CategoryTheory.Presheaf

namespace AlgebraicGeometry.Space

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (eG : StacksRepresentableCFG.EquivalenceOver q (presheafOfCategories (G ⋙ typeToCat)).p)
  (f : 𝒳 ⥤ 𝒴) (c : q.ChoiceOfPullbacks)

/-- The 2-fibre product `(Sch/V)_{fppf} ×_𝒴 𝒳` of equation 075M at a chart `V` of `G`, as a
category over the big fppf site of `S`: its structure functor. The first leg of the cospan is
`CategoryTheory.Over.forget` of the chart, so this lands in `AlgebraicGeometry.BigFppfOver B S hS`
and not in a slice of it. -/
noncomputable abbrev twoFibreProductStructureFunctor (V : SmallEtale B S hS G) :=
  TwoFibreProductOver.structureFunctor (Over.forget ((SmallEtale.toOver B S hS G).obj V)) p q
    (c.sliceFunctor (chartFiberObj B S hS G q eG V)) f

/-- The second projection of the 2-fibre product `(Sch/V)_{fppf} ×_𝒴 𝒳` of equation 075M, the
functor along which `ℱ` is pulled back to compute the left-hand side. -/
noncomputable abbrev twoFibreProductSnd (V : SmallEtale B S hS G) :=
  TwoFibreProductOver.snd (Over.forget ((SmallEtale.toOver B S hS G).obj V)) p q
    (c.sliceFunctor (chartFiberObj B S hS G q eG V)) f

include hp in
/-- **The second projection of the 2-fibre product is a 1-morphism of fibred categories over the
big fppf site of `S`.** Strictness over the base is
`CategoryTheory.TwoFibreProductOver.snd_comp_eq`, and preservation of strongly cartesian morphisms
is free because `𝒳` is fibred in groupoids, where every morphism is strongly cartesian over every
base morphism it lifts. -/
theorem isFibredOneMorphism_twoFibreProductSnd (V : SmallEtale B S hS G) :
    (twoFibreProductStructureFunctor B S hS G p q eG f c V).IsFibredOneMorphism p
      (twoFibreProductSnd B S hS G p q eG f c V) := by
  refine ⟨TwoFibreProductOver.snd_comp_eq, ?_⟩
  intro R T k a b φ hφ
  have := hφ.toIsHomLift
  exact CategoryTheory.Functor.isStronglyCartesian_of_isFiberedInGroupoids hp k _
    (CategoryTheory.Functor.isHomLift_map_of_comp_eq
      (TwoFibreProductOver.snd_comp_eq (p𝒳 := Over.forget ((SmallEtale.toOver B S hS G).obj V))
        (p𝒴 := p) (p𝒮 := q) (F := c.sliceFunctor (chartFiberObj B S hS G q eG V)) (G := f))
      k φ)

include hp hq in
/-- **The 2-fibre product of equation 075M is fibred in groupoids over the big fppf site of `S`.**
This is Stacks 02XQ, `CategoryTheory.TwoFibreProductOver.isFiberedInGroupoids`, at the cospan of
equation 075M: the slice over the chart is fibred in groupoids by
`CategoryTheory.Functor.IsFiberedInGroupoids.over_forget`, the two other legs are `p` and `q`, and
the two strictness conditions are
`CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor_comp` and the `comp_eq` of the
1-morphism. -/
theorem isFiberedInGroupoids_twoFibreProductStructureFunctor
    (hf : p.IsFibredOneMorphism q f) (V : SmallEtale B S hS G) :
    (twoFibreProductStructureFunctor B S hS G p q eG f c V).IsFiberedInGroupoids :=
  TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
    (CategoryTheory.Functor.IsFiberedInGroupoids.over_forget _) hp hq
    (CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor_comp _ _) hf.comp_eq

include hp hq in
/-- **The pullback of a sheaf along the second projection of the 2-fibre product is a sheaf** for
the inherited étale topology of the 2-fibre product. The projection is a 1-morphism of fibred
categories over the big fppf site of `S`, hence continuous for the two inherited topologies by
Stacks 06NW in the form that assumes no fibre products in the base,
`CategoryTheory.Functor.IsFibredOneMorphism.isContinuous_inheritedTopology`; and a continuous
functor pulls sheaves back to sheaves. -/
theorem isSheaf_comp_twoFibreProductSnd (hf : p.IsFibredOneMorphism q f)
    (V : SmallEtale B S hS G)
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u)) :
    Presheaf.IsSheaf
      (BigFppfOver.associatedTopology B S hS
        (twoFibreProductStructureFunctor B S hS G p q eG f c V) .etale)
      ((twoFibreProductSnd B S hS G p q eG f c V).op ⋙ ℱ.obj) := by
  have : (twoFibreProductStructureFunctor B S hS G p q eG f c V).IsFibered :=
    (isFiberedInGroupoids_twoFibreProductStructureFunctor B S hS G p q hp hq eG f c hf V).isFibered
  have := CategoryTheory.Functor.IsFibredOneMorphism.isContinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS .etale)
    (isFibredOneMorphism_twoFibreProductSnd B S hS G p q hp eG f c V)
  exact (twoFibreProductSnd B S hS G p q eG f c V).op_comp_isSheaf
    (BigFppfOver.associatedTopology B S hS
      (twoFibreProductStructureFunctor B S hS G p q eG f c V) .etale)
    (BigFppfOver.associatedTopology B S hS p .etale) ℱ

/-- **The two projections of a self-product of an étale chart factor pairs.** Let `𝒵` be a category
fibred in groupoids over the big fppf site of `S` which an algebraic space `T` represents, and let
`A` be an étale scheme chart of `T`. The functor `T_étale ⥤ 𝒵` of Stacks 073M preserves binary
products, so it carries the fibre product `A ×_T A` to a product of the image of `A` with itself in
`𝒵`, and `CategoryTheory.Presheaf.FactorsPairs` is the existence half of that universal
property. -/
theorem exists_factorsPairs_restrictionFunctor {𝒵 : Type v} [Category.{w} 𝒵]
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (r : 𝒵 ⥤ BigFppfOver B S hS)
    (eT : StacksRepresentableCFG.EquivalenceOver r (presheafOfCategories (T ⋙ typeToCat)).p)
    (A : SmallEtale B S hS T) :
    ∃ (A' : 𝒵) (a b : A' ⟶ (restrictionFunctor B S hS T r eT).obj A),
      CategoryTheory.Presheaf.FactorsPairs a b := by
  let := SmallEtale.instHasBinaryProducts B S hS T
  refine ⟨(restrictionFunctor B S hS T r eT).obj (A ⨯ A),
    (restrictionFunctor B S hS T r eT).map (Limits.prod.fst (X := A) (Y := A)),
    (restrictionFunctor B S hS T r eT).map (Limits.prod.snd (X := A) (Y := A)), ?_⟩
  exact CategoryTheory.Presheaf.factorsPairs_of_isLimit
    ((isLimitMapConeBinaryFanEquiv (restrictionFunctor B S hS T r eT) _ _)
      (isLimitOfPreserves (restrictionFunctor B S hS T r eT) (prodIsProd A A)))

include hp hq in
/-- **Equation 075M, the left-hand side at a chart, as an equalizer, for a given presentation of
the 2-fibre product.** The sections of `(f_*ℱ)|_{G_étale}` over an étale scheme chart `V` of `G`
are the equalizer of the sections of `ℱ` over two objects of the 2-fibre product
`(Sch/V)_{fppf} ×_𝒴 𝒳`, namely an object `A` coming from an étale scheme chart of an algebraic
space `T` representing that 2-fibre product and the object presenting the self-product of `A`.

The presentation of the 2-fibre product is a hypothesis here, so that the statement holds for an
arbitrary `𝒳` with no representability assumption of its own. Equation 075M's own form of the
statement, in which the presentation is constructed instead of assumed, is
`AlgebraicGeometry.Space.exists_restrictedDirectImageComparisonSource_equalizer`; it is this
result with the presentation supplied by
`AlgebraicGeometry.Space.exists_isAlgebraicSpace_twoFibreProductStructureFunctor`.

The chain is `AlgebraicGeometry.Space.restrictedDirectImageChartEquiv` — equation 075M's left-hand
side as global sections over the 2-fibre product — followed by
`CategoryTheory.Presheaf.globalSectionsEquivEqualizer`, whose three hypotheses are
`AlgebraicGeometry.Space.isSheaf_comp_twoFibreProductSnd`,
`AlgebraicGeometry.Space.exists_restrictionFunctor_coversTop_singleton` (Stacks 073M by a single
chart) and `AlgebraicGeometry.Space.exists_factorsPairs_restrictionFunctor`. -/
theorem exists_restrictedDirectImageComparisonSource_equalizer_of_equivalenceOver
    (hf : p.IsFibredOneMorphism q f)
    [∀ H : 𝒳ᵒᵖ ⥤ Type u, f.op.HasPointwiseRightKanExtension H]
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u))
    (V : SmallEtale B S hS G)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (eT : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductStructureFunctor B S hS G p q eG f c V)
      (presheafOfCategories (T ⋙ typeToCat)).p) :
    ∃ (A A' : TwoFibreProductOver (Over.forget ((SmallEtale.toOver B S hS G).obj V)) p q
          (c.sliceFunctor (chartFiberObj B S hS G q eG V)) f) (a b : A' ⟶ A),
      Nonempty (((restrictionSheafFunctor B S hS G q hq eG).obj
            ((etaleDirectImage B S hS p q hp f hf).obj ℱ)).obj.obj (op V) ≃
        {y : ℱ.obj.obj (op ((twoFibreProductSnd B S hS G p q eG f c V).obj A)) //
          ℱ.obj.map ((twoFibreProductSnd B S hS G p q eG f c V).map a).op y =
            ℱ.obj.map ((twoFibreProductSnd B S hS G p q eG f c V).map b).op y}) := by
  obtain ⟨A₀, hA₀⟩ := exists_restrictionFunctor_coversTop_singleton B S hS T
    (twoFibreProductStructureFunctor B S hS G p q eG f c V) hT
    (isFiberedInGroupoids_twoFibreProductStructureFunctor B S hS G p q hp hq eG f c hf V) eT
  obtain ⟨A', a, b, hrel⟩ := exists_factorsPairs_restrictionFunctor B S hS T
    (twoFibreProductStructureFunctor B S hS G p q eG f c V) eT A₀
  refine ⟨(restrictionFunctor B S hS T
    (twoFibreProductStructureFunctor B S hS G p q eG f c V) eT).obj A₀, A', a, b, ⟨?_⟩⟩
  refine (restrictedDirectImageChartEquiv B S hS G p q hp hq eG f hf c ℱ V).trans ?_
  exact CategoryTheory.Presheaf.globalSectionsEquivEqualizer
    ((twoFibreProductSnd B S hS G p q eG f c V).op ⋙ ℱ.obj)
    (isSheaf_comp_twoFibreProductSnd B S hS G p q hp hq eG f c hf V ℱ) hA₀ hrel

include hp hq in
/-- **The 2-fibre product `(Sch/V)_{fppf} ×_𝒴 𝒳` of equation 075M at a chart is represented by an
algebraic space over `S`.** For every étale scheme chart `V` of the algebraic space `G` presenting
`𝒴` there are an algebraic space `T` over `S` and an equivalence over the big fppf site of `S`
between that 2-fibre product and the category of elements of `T`.

This is the identification the source makes in its proof of Stacks 073N, where `T` is the
algebraic space `V ×_G F`. It is
`AlgebraicGeometry.Space.exists_isAlgebraicSpace_nonempty_equivalenceOver_overForget` at the
cospan of equation 075M, whose first leg is the 1-morphism attached by the choice of pullbacks to
the object `u_G V` of `𝒴`; its strictness over the base is
`CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor_comp`. -/
theorem exists_isAlgebraicSpace_twoFibreProductStructureFunctor
    (Fpsh : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hFpsh : IsAlgebraicSpace B S hS Fpsh)
    (eFpsh : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (Fpsh ⋙ typeToCat)).p)
    (hG : IsAlgebraicSpace B S hS G) (hf : p.IsFibredOneMorphism q f)
    (V : SmallEtale B S hS G) :
    ∃ T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS T ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (twoFibreProductStructureFunctor B S hS G p q eG f c V)
        (presheafOfCategories (T ⋙ typeToCat)).p) :=
  exists_isAlgebraicSpace_nonempty_equivalenceOver_overForget B S hS Fpsh G p q hp hq eFpsh eG f
    hFpsh hG hf ((SmallEtale.toOver B S hS G).obj V)
    (c.sliceFunctor (chartFiberObj B S hS G q eG V))
    (Functor.ChoiceOfPullbacks.sliceFunctor_comp _ _)

include hp hq in
/-- **Equation 075M, the left-hand side at a chart, as an equalizer.** The sections of
`(f_*ℱ)|_{G_étale}` over an étale scheme chart `V` of `G` are the equalizer of the sections of `ℱ`
over two objects of the 2-fibre product `(Sch/V)_{fppf} ×_𝒴 𝒳`, namely an object `A` coming from
an étale scheme chart of an algebraic space representing that 2-fibre product and the object
presenting the self-product of `A`.

This is the counterpart of
`AlgebraicGeometry.Space.exists_restrictedDirectImageComparisonTarget_equalizer`, which presents
the *right*-hand side at the same chart as an equalizer of sections of `ℱ|_{F_étale}` over two
étale scheme charts of `F`. With both sides presented, the comparison map of equation 075M is a map
between two equalizer diagrams, which is the shape in which the source proves it invertible.

The hypotheses are those of equation 075M itself: `𝒳` and `𝒴` are presented by the algebraic
spaces `F` and `G` and `f` is a 1-morphism of fibred categories between them. The
representability of the 2-fibre product that the equalizer presentation needs — the identification
the source makes in its proof of Stacks 073N — is supplied by
`AlgebraicGeometry.Space.exists_isAlgebraicSpace_twoFibreProductStructureFunctor`, and the
equalizer itself by `exists_restrictedDirectImageComparisonSource_equalizer_of_equivalenceOver`.
-/
@[stacks 075M "the left-hand side (f_*F)|_{G_etale}, as an equalizer of sections of F over two \
objects of the 2-fibre product (Sch/V)_fppf x_Y X, at a chart V of G. This is the counterpart of \
exists_restrictedDirectImageComparisonTarget_equalizer, which is the right-hand side at the same \
chart; with both sides presented the comparison map is a map of equalizer diagrams. The \
representability of the 2-fibre product by an algebraic space over S -- the identification of \
(Sch/V)_fppf x_Y X with the split category fibred in groupoids of V x_G F that the source's proof \
of Tag 073N makes -- is supplied by \
exists_isAlgebraicSpace_twoFibreProductStructureFunctor from the presentations of X and Y alone"]
theorem exists_restrictedDirectImageComparisonSource_equalizer
    (Fpsh : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hFpsh : IsAlgebraicSpace B S hS Fpsh)
    (eFpsh : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (Fpsh ⋙ typeToCat)).p)
    (hG : IsAlgebraicSpace B S hS G) (hf : p.IsFibredOneMorphism q f)
    [∀ H : 𝒳ᵒᵖ ⥤ Type u, f.op.HasPointwiseRightKanExtension H]
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u))
    (V : SmallEtale B S hS G) :
    ∃ (A A' : TwoFibreProductOver (Over.forget ((SmallEtale.toOver B S hS G).obj V)) p q
          (c.sliceFunctor (chartFiberObj B S hS G q eG V)) f) (a b : A' ⟶ A),
      Nonempty (((restrictionSheafFunctor B S hS G q hq eG).obj
            ((etaleDirectImage B S hS p q hp f hf).obj ℱ)).obj.obj (op V) ≃
        {y : ℱ.obj.obj (op ((twoFibreProductSnd B S hS G p q eG f c V).obj A)) //
          ℱ.obj.map ((twoFibreProductSnd B S hS G p q eG f c V).map a).op y =
            ℱ.obj.map ((twoFibreProductSnd B S hS G p q eG f c V).map b).op y}) := by
  obtain ⟨T, hT, ⟨eT⟩⟩ := exists_isAlgebraicSpace_twoFibreProductStructureFunctor B S hS G p q
    hp hq eG f c Fpsh hFpsh eFpsh hG hf V
  exact exists_restrictedDirectImageComparisonSource_equalizer_of_equivalenceOver B S hS G p q
    hp hq eG f c hf ℱ V T hT eT

end AlgebraicGeometry.Space

end
