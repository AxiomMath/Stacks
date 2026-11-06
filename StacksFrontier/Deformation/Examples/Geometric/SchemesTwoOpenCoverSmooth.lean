module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Cofibered.FactorChange
public import StacksFrontier.Deformation.Cofibered.Product
public import StacksFrontier.Deformation.Examples.Geometric.SchemeChartEquivalence
public import StacksFrontier.Deformation.Examples.Geometric.Schemes
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTwoOpenCoverGlue
public import StacksFrontier.Deformation.Examples.RingsSmooth
public import StacksFrontier.Deformation.Examples.RingsUnobstructed
public import StacksFrontier.Deformation.RimSchlessinger.FibreProduct.Deformations
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison

/-!
# Unobstructed deformation problems for a scheme with a two-element affine cover

In Situation 0DYY a scheme `X` over `k` is covered by two affine opens `U₁`, `U₂` whose
intersection `U₁₂` is affine, and the three affines are presented as the spectra of `k`-algebras
`P₁`, `P₂`, `P₁₂`. Tag 0DZN makes two assertions about the deformation category `Def_X` of `X`:

1. if `U₁₂ → Spec(k)` is smooth, then `Def_X ⟶ Def_{P₁} × Def_{P₂}` is smooth;
2. if moreover `U₁` is a local complete intersection over `k`, then `Def_X ⟶ Def_{P₂}` is
   smooth.

The product `Def_{P₁} × Def_{P₂}` is the product of two categories cofibered in groupoids over
`𝒞_Λ`, that is — item (14) of Remarks 06GK, separately tagged 0DZJ — their `2`-fibre product
over `𝒞_Λ`: `Deformation.cofiberedProduct`.

## Main definitions

* `Deformation.Examples.ringDeformationCategoryOver`: `Def_P`, the deformation category of a
  `k`-algebra, read as a category over `𝒞_Λ`.
* `Deformation.Examples.schemeDeformationCategoryOver`: `Def_X`, the deformation category of a
  scheme over `k`, read as a category over `𝒞_Λ`.
* `Deformation.Examples.GluingSituation.toChartProductOfCover`: the morphism
  `Def_X ⟶ Def_{P₁} × Def_{P₂}` of Tag 0DZN, built out of the two-chart cover.
* `Deformation.Examples.GluingSituation.toChartProduct`: the same morphism assembled instead
  from restriction and comparison morphisms carried as hypotheses.

## Main results

* `Deformation.Examples.GluingSituation.isSmooth_toChartProductOfCover`: **Stacks 0DZN**, first
  clause, at the source's own hypotheses.
* `Deformation.Examples.GluingSituation.isSmooth_toChartProductOfCover_comp_snd`:
  **Stacks 0DZN**, second clause, at the source's own hypotheses.
* `Deformation.Examples.GluingSituation.isSmooth_toChartProduct` and
  `Deformation.Examples.GluingSituation.isSmooth_toChartProduct_comp_snd`: the same two clauses
  for a comparison morphism carried as a hypothesis, retained for developments stated against
  that form and carrying no Stacks attribute.

## Implementation notes

### How the morphism is built

The source writes `Def_X ⟶ Def_{P₁} × Def_{P₂}` and proves it smooth in three steps; here the
morphism is literally the composite of those steps, each a morphism over `𝒞_Λ`:

* `Deformation.Examples.twoOpenComparisonBasedFunctor`, the comparison morphism of Tag 0DYZ into
  the `2`-fibre product `Def_{U₁} ×_{Def_{U₁₂}} Def_{U₂}`, which is smooth by
  `Deformation.Examples.isSmooth_twoOpenComparisonBasedFunctor` — the glueing construction of
  the proof of 0DYZ, including the two steps whose verification the source omits;
* `Deformation.mapBaseBasedFunctor` applied to the identification `Def_{U₁₂} = Def_{P₁₂}` of
  Tag 0DYX, which replaces the deformation category in the middle of the `2`-fibre product by
  the *ring* one. This is what makes the next step available: Tag 0DYN needs the middle category
  to be a deformation category, which is Tag 0DY2 for `Def_{P₁₂}` and is not known here for
  `Def_{U₁₂}`;
* `Deformation.mapTwoFibreProductBaseChange`, the canonical functor of Tag 0DYN from that
  `2`-fibre product to the `2`-fibre product over `𝒞_Λ`, whose target *is* the product
  `Def_{U₁} × Def_{U₂}` by
  `Deformation.twoFibreProductBasedCategory_comp_baseProjection`. Its tangent hypothesis is the
  vanishing `T Def_{P₁₂} = 0` of Tag 0DZL for the smooth algebra `P₁₂` and its
  infinitesimal-automorphism hypothesis is vacuous, the fibres of the identity functor on `𝒞_Λ`
  being one-object, one-morphism categories;
* `Deformation.cofiberedProductMap` applied to the identifications `Def_{U_i} = Def_{P_i}` of
  Tag 0DYX, which is the source's equality `Def_{U₁} × Def_{U₂} = Def_{P₁} × Def_{P₂}`.

For the second clause, `Def_{P₁} × Def_{P₂} ⟶ Def_{P₂}` is a base change of `Def_{P₁} ⟶ 𝒞_Λ`,
which is smooth by Tag 0DZH because `P₁` is a local complete intersection, so Tag 06HM applies
again.

Tag 0DYN's hypothesis on its two outer factors, that they are cofibered in groupoids, is
`Deformation.Examples.isCofiberedInGroupoids_chart`: it is transported from the ring side along
Tag 0DYX, there being no scheme-side proof of it in this repository. Its hypothesis on the
target, that `𝒞_Λ` read through the identity functor is a *deformation* category, is
`Deformation.isDeformationCategory_id`, whose Rim–Schlessinger condition
(`Deformation.satisfiesRS_id`) is the existence of fibre products in `𝒞_Λ` along a surjection
(Tag 06GH).

### The hypotheses on `U₁₂` and on `U₁`

They are stated for the coordinate rings, as `Algebra.Smooth k S.P₁₂` and
`IsLocalCompleteIntersection k S.P₁`. For an affine scheme these are the source's hypotheses
read through the presentations `S.affine₁₂` and `S.affine₁` of Situation 0DYY, and they are the
form in which the source's own proof uses them: it applies Tag 0DZL to `P₁₂` and Tag 0DZH to
`P₁`. Transporting them across those presentations would need the affine-local
characterizations of smoothness and of being a local complete intersection, which play no part
in the proof route.

### The two models of the tangent space

Tag 0DZL is stated for the fibre over `Deformation.artinianDualNumbers`, the *lifted* dual
numbers built from `ULift k`, whereas the differential of Tag 0DYN has
`Deformation.artinianTangentSpace`, the *unlifted* model built from `k`. The two are compared
by applying the functor of isomorphism classes to the isomorphism of dual-number objects
induced by `Deformation.fgModuleCatULiftSelfIso`; only subsingletonness is transported, so no
linearity is needed.

## References

* [Stacks Project, Tag 0DZN](https://stacks.math.columbia.edu/tag/0DZN)
* [Stacks Project, Tag 0DYY](https://stacks.math.columbia.edu/tag/0DYY)
* [Stacks Project, Tag 0DYZ](https://stacks.math.columbia.edu/tag/0DYZ)
* [Stacks Project, Tag 0DYX](https://stacks.math.columbia.edu/tag/0DYX)
* [Stacks Project, Tag 0DYN](https://stacks.math.columbia.edu/tag/0DYN)
* [Stacks Project, Tag 0DZJ](https://stacks.math.columbia.edu/tag/0DZJ)
* [Stacks Project, Tag 0DZL](https://stacks.math.columbia.edu/tag/0DZL)
* [Stacks Project, Tag 0DZH](https://stacks.math.columbia.edu/tag/0DZH)
* [Stacks Project, Tag 06HM](https://stacks.math.columbia.edu/tag/06HM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Examples

universe u u₁ v₁ u₂ v₂

/-! ### The two deformation categories as categories over `𝒞_Λ` -/

/-- `Def_P`, the deformation category of a `k`-algebra `P` of Tag 0DY1, read as a category over
`𝒞_Λ` through its structure functor. -/
abbrev ringDeformationCategoryOver (Λ k P : Type u) [CommRing Λ] [Field k] [Algebra Λ k]
    [CommRing P] [Algebra k P] : BasedCategory (ArtinianLocalAlgCat.{u, u, u} Λ k) :=
  BasedCategory.ofFunctor (objectsOverFunctor (FlatAlgebraCategory.projection (Λ := Λ) (k := k))
    (residueFieldAlgebra (Λ := Λ) (k := k) P))

/-- `Def_X`, the deformation category of a scheme `X` over `k` of Tag 0DY7, read as a category
over `𝒞_Λ` through its structure functor. -/
abbrev schemeDeformationCategoryOver (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (CommRingCat.of k))) : BasedCategory (ArtinianLocalAlgCat.{u, u, u} Λ k) :=
  BasedCategory.ofFunctor (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X)

section

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### Transporting a morphism along an equality of based categories -/

/-- A morphism of categories over `𝒞_Λ`, read into an equal target. -/
def basedFunctorCast
    {𝓐 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, u, u} Λ k)}
    {𝓑 𝓑' : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, u, u} Λ k)}
    (h : 𝓑 = 𝓑') (φ : BasedFunctor 𝓐 𝓑) : BasedFunctor 𝓐 𝓑' :=
  h ▸ φ

/-- Reading a smooth morphism of categories over `𝒞_Λ` into an equal target leaves it smooth. -/
private theorem isSmooth_basedFunctorCast
    {𝓐 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, u, u} Λ k)}
    {𝓑 𝓑' : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, u, u} Λ k)}
    (h : 𝓑 = 𝓑') (φ : BasedFunctor 𝓐 𝓑) (hφ : IsSmooth φ) :
    IsSmooth (basedFunctorCast h φ) := by
  subst h
  exact hφ

/-! ### Vanishing of the tangent space of `Def_P` for a smooth algebra -/

/-- Subsingletonness of a value of a set-valued functor transports along an isomorphism of the
objects at which it is evaluated. -/
private theorem subsingleton_functor_obj_of_iso {C : Type u₁} [Category.{v₁} C]
    (F : C ⥤ Type u₂) {A B : C} (e : A ≅ B) (h : Subsingleton (F.obj A)) :
    Subsingleton (F.obj B) :=
  ⟨fun _ _ => (F.mapIso e).toEquiv.symm.injective (h.elim _ _)⟩

/-- The comparison of the two dual-number objects of `𝒞_Λ`: the one built from `ULift k`, used
by `Deformation.tangentSpaceArtinian`, and the one built from `k`, used by
`Deformation.artinianTangentSpace`. -/
private def dualNumbersModelIso :
    artinianDualNumbers.{u, u, u} Λ k ≅ augmentedDualNumbers (Λ := Λ) (k := k) :=
  (squareZeroExtensionArtinian Λ k).mapIso (fgModuleCatULiftSelfIso (k := k))

/-- **Stacks 0DZL** in the unlifted tangent-space model: for a smooth `k`-algebra `P` the
tangent space of `Def_P` has at most one element. -/
private theorem subsingleton_artinianTangentSpace_ringDeformation (P : Type u) [CommRing P]
    [Algebra k P] (hsmooth : Algebra.Smooth k P)
    (h : IsCofiberedInGroupoids (ringDeformationCategoryOver Λ k P).p) :
    Subsingleton (artinianTangentSpace Λ k
      (isomorphismClasses (ringDeformationCategoryOver Λ k P) h)) := by
  let _ := hsmooth
  refine subsingleton_functor_obj_of_iso
    (isomorphismClasses (ringDeformationCategoryOver Λ k P) h)
    (dualNumbersModelIso (Λ := Λ) (k := k)) ?_
  obtain ⟨x, hx⟩ :=
    existsUnique_ringDeformationClass_artinianDualNumbers_of_smooth (Λ := Λ) (k := k) (P := P)
  refine ⟨fun _ _ => ?_⟩
  refine (Equiv.cast
    (isomorphismClasses_obj (ringDeformationCategoryOver Λ k P) h _)).injective ?_
  exact (hx _).trans (hx _).symm

/-- A morphism of categories cofibered in groupoids whose source has a subsingleton tangent
space is injective on tangent spaces. -/
private theorem injective_differential_of_subsingleton
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, u, u} Λ k)}
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, u, u} Λ k)}
    (h𝓖 : IsCofiberedInGroupoids 𝓖.p) (h𝓕 : IsCofiberedInGroupoids 𝓕.p)
    (q : BasedFunctor 𝓖 𝓕)
    (h : Subsingleton (artinianTangentSpace Λ k (isomorphismClasses 𝓖 h𝓖))) :
    Function.Injective (differential h𝓖 h𝓕 q) :=
  fun _ _ _ => h.elim _ _

/-! ### Infinitesimal automorphisms over `𝒞_Λ`-over-itself are trivial -/

/-- The relative infinitesimal automorphisms of `𝒞_Λ` over itself along a lifting arrow are
trivial, every fibre of the identity functor having exactly one morphism between any two of its
objects; so the structure morphism of a category cofibered in groupoids over `𝒞_Λ` is
surjective on relative infinitesimal automorphisms. -/
private theorem surjective_mapRelativeInfinitesimalAutomorphisms_baseProjection
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, u, u} Λ k)}
    (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (h𝓕 : IsCofiberedInGroupoids (𝟭 (ArtinianLocalAlgCat.{u, u, u} Λ k)))
    {B A : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : B ⟶ A)
    {z : 𝓖.p.Fiber B} {t : 𝓖.p.Fiber A} (r : z.1 ⟶ t.1) (hr : 𝓖.p.IsHomLift f r) :
    Function.Surjective
      (mapRelativeInfinitesimalAutomorphisms (baseProjection 𝓖.p) h𝓖 h𝓕 f r hr) := by
  intro y
  have hsub : Subsingleton (Aut ((fiberFunctor (baseProjection 𝓖.p) B).obj z)) := by
    obtain ⟨hu⟩ := unique_hom_fiber_id B ((fiberFunctor (baseProjection 𝓖.p) B).obj z)
      ((fiberFunctor (baseProjection 𝓖.p) B).obj z)
    exact ⟨fun a b => Aut.ext (Iso.ext ((hu.uniq a.asIso.hom).trans (hu.uniq b.asIso.hom).symm))⟩
  exact ⟨1, Subtype.ext (hsub.elim _ _)⟩

/-! ### Smoothness over the product of the two chart deformation categories -/

namespace GluingSituation

variable (S : GluingSituation Λ k)
  (p₁ : BasedFunctor (ringDeformationCategoryOver Λ k S.P₁)
    (ringDeformationCategoryOver Λ k S.P₁₂))
  (p₂ : BasedFunctor (ringDeformationCategoryOver Λ k S.P₂)
    (ringDeformationCategoryOver Λ k S.P₁₂))
  (comparison : BasedFunctor (schemeDeformationCategoryOver Λ k S.X)
    (twoFibreProductBasedCategory p₁ p₂))

/-! #### The five morphisms the composite is built from -/

/-- Restriction `Def_{U₁} ⟶ Def_{U₁₂}` of Tag 0DYW. -/
abbrev restrictLeft :
    BasedFunctor
      (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (S.U₁.ι ≫ S.X.hom))))
      (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k)
          (Over.mk ((S.U₁ ⊓ S.U₂).ι ≫ S.X.hom)))) :=
  openRestrictionLEBasedFunctor S.X (inf_le_left : S.U₁ ⊓ S.U₂ ≤ S.U₁)

/-- Restriction `Def_{U₂} ⟶ Def_{U₁₂}` of Tag 0DYW. -/
abbrev restrictRight :
    BasedFunctor
      (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (S.U₂.ι ≫ S.X.hom))))
      (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k)
          (Over.mk ((S.U₁ ⊓ S.U₂).ι ≫ S.X.hom)))) :=
  openRestrictionLEBasedFunctor S.X (inf_le_right : S.U₁ ⊓ S.U₂ ≤ S.U₂)

/-- The identification `Def_{U₁} = Def_{P₁}` of Tag 0DYX. -/
abbrev chartLeft :
    BasedFunctor
      (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (S.U₁.ι ≫ S.X.hom))))
      (ringDeformationCategoryOver Λ k S.P₁) :=
  chartBasedFunctor (Λ := Λ) S.P₁ S.affine₁

/-- The identification `Def_{U₂} = Def_{P₂}` of Tag 0DYX. -/
abbrev chartRight :
    BasedFunctor
      (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (S.U₂.ι ≫ S.X.hom))))
      (ringDeformationCategoryOver Λ k S.P₂) :=
  chartBasedFunctor (Λ := Λ) S.P₂ S.affine₂

/-- The identification `Def_{U₁₂} = Def_{P₁₂}` of Tag 0DYX. -/
abbrev chartOverlap :
    BasedFunctor
      (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k)
          (Over.mk ((S.U₁ ⊓ S.U₂).ι ≫ S.X.hom))))
      (ringDeformationCategoryOver Λ k S.P₁₂) :=
  chartBasedFunctor (Λ := Λ) S.P₁₂ S.affine₁₂

/-- **The restriction morphism `Def_{P₁} ⟶ Def_{P₁₂}` over `𝒞_Λ`**, which the source obtains
from the localization `P₁ → P₁₂`. Here it is read through the identifications of Tag 0DYX: take
spectra, restrict the deformation of the open subscheme `U₁` to `U₁ ⊓ U₂`, and take global
sections again. The proof of Tag 0DZN below does not use it — it changes the middle category of
the `2`-fibre product by `Deformation.mapBaseBasedFunctor` instead of changing the two outer
ones — but it is the morphism the source names, and it is what makes the `2`-fibre product
`Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}` of 0DYZ expressible. -/
abbrev chartRestrictLeft :
    BasedFunctor (ringDeformationCategoryOver Λ k S.P₁)
      (ringDeformationCategoryOver Λ k S.P₁₂) :=
  BasedFunctor.comp
    (BasedFunctor.comp
      ⟨(chartEquivalenceOver (Λ := Λ) S.P₁ S.affine₁).inv.functor,
        (chartEquivalenceOver (Λ := Λ) S.P₁ S.affine₁).inv.w⟩
      (restrictLeft S))
    (chartOverlap S)

/-- The restriction morphism `Def_{P₂} ⟶ Def_{P₁₂}` over `𝒞_Λ`. -/
abbrev chartRestrictRight :
    BasedFunctor (ringDeformationCategoryOver Λ k S.P₂)
      (ringDeformationCategoryOver Λ k S.P₁₂) :=
  BasedFunctor.comp
    (BasedFunctor.comp
      ⟨(chartEquivalenceOver (Λ := Λ) S.P₂ S.affine₂).inv.functor,
        (chartEquivalenceOver (Λ := Λ) S.P₂ S.affine₂).inv.w⟩
      (restrictRight S))
    (chartOverlap S)

/-! #### The morphism `Def_X ⟶ Def_{P₁} × Def_{P₂}` -/

/-- **The morphism `Def_X ⟶ Def_{P₁} × Def_{P₂}` of Tag 0DZN.** It is the composite of four
morphisms over `𝒞_Λ`:

* the comparison morphism of Tag 0DYZ into the `2`-fibre product
  `Def_{U₁} ×_{Def_{U₁₂}} Def_{U₂}`;
* the identification `Def_{U₁₂} = Def_{P₁₂}` of Tag 0DYX applied to the target of the two legs,
  which is what puts the *ring* deformation category of the intersection in the middle;
* the canonical functor of Tag 0DYN from that `2`-fibre product to the `2`-fibre product over
  `𝒞_Λ`, whose target *is* the product `Def_{U₁} × Def_{U₂}` by
  `Deformation.twoFibreProductBasedCategory_comp_baseProjection`;
* the identifications `Def_{U_i} = Def_{P_i}` of Tag 0DYX on the two factors. -/
def toChartProductOfCover :
    BasedFunctor (schemeDeformationCategoryOver Λ k S.X)
      (cofiberedProduct (ringDeformationCategoryOver Λ k S.P₁)
        (ringDeformationCategoryOver Λ k S.P₂)) :=
  BasedFunctor.comp
    (basedFunctorCast
      (twoFibreProductBasedCategory_comp_baseProjection
        (BasedFunctor.comp (restrictLeft S) (chartOverlap S))
        (BasedFunctor.comp (restrictRight S) (chartOverlap S)))
      (BasedFunctor.comp
        (BasedFunctor.comp (twoOpenComparisonBasedFunctor S.X S.U₁ S.U₂)
          (mapBaseBasedFunctor (restrictLeft S) (restrictRight S) (chartOverlap S)))
        (mapTwoFibreProductBaseChange
          (BasedFunctor.comp (restrictLeft S) (chartOverlap S))
          (BasedFunctor.comp (restrictRight S) (chartOverlap S))
          (baseProjection (ringDeformationCategoryOver Λ k S.P₁₂).p))))
    (cofiberedProductMap (chartLeft S) (chartRight S))

/-- The canonical functor from the `2`-fibre product over `Def_{P₁₂}` to the one over `𝒞_Λ` is
smooth when `P₁₂` is a smooth algebra (the key step of Tag 0DZN). -/
private theorem isSmooth_mapTwoFibreProductBaseChange_ringDeformation
    {𝓗₁ : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, u, u} Λ k)}
    {𝓗₂ : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, u, u} Λ k)}
    (q₁ : BasedFunctor 𝓗₁ (ringDeformationCategoryOver Λ k S.P₁₂))
    (q₂ : BasedFunctor 𝓗₂ (ringDeformationCategoryOver Λ k S.P₁₂))
    (h𝓗₁ : IsCofiberedInGroupoids 𝓗₁.p) (h𝓗₂ : IsCofiberedInGroupoids 𝓗₂.p)
    (hΛ : IsDeformationCategory.{u, u, u} (𝟭 (ArtinianLocalAlgCat.{u, u, u} Λ k)))
    (hU₁₂ : Algebra.Smooth k S.P₁₂) :
    IsSmooth (mapTwoFibreProductBaseChange q₁ q₂
      (baseProjection (ringDeformationCategoryOver Λ k S.P₁₂).p)) :=
  isSmooth_mapTwoFibreProductBaseChange q₁ q₂ _ h𝓗₁ h𝓗₂
    (ringDeformationCategory_isDeformationCategory S.P₁₂) hΛ
    (injective_differential_of_subsingleton _ _ _
      (subsingleton_artinianTangentSpace_ringDeformation S.P₁₂ hU₁₂ _))
    (fun f _ _ _ _ r hr =>
      surjective_mapRelativeInfinitesimalAutomorphisms_baseProjection _ _ f r hr)

/-- The projection `Def_{P₁} × Def_{P₂} ⟶ Def_{P₂}` is smooth when `P₁` is a local complete
intersection (Tags 0DZH and 06HM). -/
private theorem isSmooth_cofiberedProductSnd_ringDeformation
    (hU₁ : IsLocalCompleteIntersection k S.P₁) :
    IsSmooth (cofiberedProductSnd (ringDeformationCategoryOver Λ k S.P₁)
      (ringDeformationCategoryOver Λ k S.P₂)) :=
  isSmooth_twoFibreProductSnd isCofiberedInGroupoids_id
    (baseProjection (ringDeformationCategoryOver Λ k S.P₁).p)
    (baseProjection (ringDeformationCategoryOver Λ k S.P₂).p)
    (ringDeformationCategory_isSmooth_of_isLocalCompleteIntersection hU₁)

/-- **Stacks Project, Tag 0DZN**, first clause. In Situation 0DYY, if `U₁₂ → Spec(k)` is smooth
then `Def_X ⟶ Def_{U₁} × Def_{U₂} = Def_{P₁} × Def_{P₂}` is smooth. -/
@[stacks 0DZN "clause 1: Def_X ⟶ Def_{P_1} × Def_{P_2} is smooth when U_12 is smooth over k; \
unconditional, the hypothesis on P_12 being the source's own"]
theorem isSmooth_toChartProductOfCover (hU₁₂ : Algebra.Smooth k S.P₁₂) :
    IsSmooth (toChartProductOfCover S) := by
  have hfullL := full_chartBasedFunctor (Λ := Λ) S.P₁ S.affine₁
  have hfullR := full_chartBasedFunctor (Λ := Λ) S.P₂ S.affine₂
  have hfullO := full_chartBasedFunctor (Λ := Λ) S.P₁₂ S.affine₁₂
  have hfaithO := faithful_chartBasedFunctor (Λ := Λ) S.P₁₂ S.affine₁₂
  refine isSmooth_comp _ _ ?_
    (isSmooth_cofiberedProductMap (chartLeft S) (chartRight S)
      (exists_vertical_chartBasedFunctor (Λ := Λ) S.P₁ S.affine₁)
      (exists_vertical_chartBasedFunctor (Λ := Λ) S.P₂ S.affine₂))
  refine isSmooth_basedFunctorCast _ _ (isSmooth_comp _ _ ?_ ?_)
  · exact isSmooth_comp _ _ (isSmooth_twoOpenComparisonBasedFunctor S.X S.U₁ S.U₂ S.cover)
      (isSmooth_mapBaseBasedFunctor (restrictLeft S) (restrictRight S) (chartOverlap S))
  · exact isSmooth_mapTwoFibreProductBaseChange_ringDeformation S _ _
      (isCofiberedInGroupoids_chart (Λ := Λ) S.P₁ S.affine₁)
      (isCofiberedInGroupoids_chart (Λ := Λ) S.P₂ S.affine₂) (isDeformationCategory_id Λ k) hU₁₂

/-- **Stacks Project, Tag 0DZN**, second clause. In Situation 0DYY, if `U₁₂ → Spec(k)` is smooth
and `U₁` is in addition a local complete intersection over `k`, then
`Def_X ⟶ Def_{U₂} = Def_{P₂}` is smooth. -/
@[stacks 0DZN "clause 2: Def_X ⟶ Def_{P_2} is smooth when U_12 is smooth over k and U_1 is a \
local complete intersection over k; unconditional, the hypotheses on P_12 and P_1 being the \
source's own"]
theorem isSmooth_toChartProductOfCover_comp_snd (hU₁₂ : Algebra.Smooth k S.P₁₂)
    (hU₁ : IsLocalCompleteIntersection k S.P₁) :
    IsSmooth (BasedFunctor.comp (toChartProductOfCover S)
      (cofiberedProductSnd (ringDeformationCategoryOver Λ k S.P₁)
        (ringDeformationCategoryOver Λ k S.P₂))) :=
  isSmooth_comp _ _ (isSmooth_toChartProductOfCover S hU₁₂)
    (isSmooth_cofiberedProductSnd_ringDeformation S hU₁)

/-! #### The same three objects for morphisms carried as hypotheses

The three declarations below are the earlier, weaker forms of the three above: instead of
building the restriction morphisms and the comparison morphism of Tag 0DYZ out of the cover,
they take them as hypotheses `p₁`, `p₂`, `comparison` and assume `comparison` smooth. They are
retained unchanged because other developments are stated against them, and they carry no
`@[stacks 0DZN]` attribute — the tag belongs on the unconditional forms above, which assume only
what the source assumes. -/

section Carried

/-- The morphism `Def_X ⟶ Def_{P₁} × Def_{P₂}` of Tag 0DZN: the comparison morphism of
Tag 0DYZ into the `2`-fibre product `Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}`, followed by the
canonical functor of Tag 0DYN into the `2`-fibre product over `𝒞_Λ`, whose target *is* the
product `Def_{P₁} × Def_{P₂}` by
`Deformation.twoFibreProductBasedCategory_comp_baseProjection`. -/
def toChartProduct :
    BasedFunctor (schemeDeformationCategoryOver Λ k S.X)
      (cofiberedProduct (ringDeformationCategoryOver Λ k S.P₁)
        (ringDeformationCategoryOver Λ k S.P₂)) :=
  basedFunctorCast (twoFibreProductBasedCategory_comp_baseProjection p₁ p₂)
    (BasedFunctor.comp comparison
      (mapTwoFibreProductBaseChange p₁ p₂
        (baseProjection (ringDeformationCategoryOver Λ k S.P₁₂).p)))

/-- The first clause of Tag 0DZN for morphisms carried as hypotheses. In Situation 0DYY, if
`U₁₂ → Spec(k)` is smooth then `Def_X ⟶ Def_{P₁} × Def_{P₂}` is smooth.

This is `Deformation.Examples.GluingSituation.isSmooth_toChartProductOfCover` with the
restriction morphisms, the comparison morphism of Tag 0DYZ and its smoothness, and the
Rim–Schlessinger condition for `𝒞_Λ` over itself all carried as hypotheses. -/
theorem isSmooth_toChartProduct
    (hΛ : IsDeformationCategory.{u, u, u} (𝟭 (ArtinianLocalAlgCat.{u, u, u} Λ k)))
    (hU₁₂ : Algebra.Smooth k S.P₁₂) (hcomparison : IsSmooth comparison) :
    IsSmooth (toChartProduct S p₁ p₂ comparison) := by
  refine isSmooth_basedFunctorCast _ _ (isSmooth_comp comparison _ hcomparison ?_)
  exact isSmooth_mapTwoFibreProductBaseChange_ringDeformation S p₁ p₂
    (ringDeformationCategory_isDeformationCategory S.P₁).predeformation.cofibered
    (ringDeformationCategory_isDeformationCategory S.P₂).predeformation.cofibered hΛ hU₁₂

/-- The second clause of Tag 0DZN for morphisms carried as hypotheses. In Situation 0DYY, if
`U₁₂ → Spec(k)` is smooth and `U₁` is in addition a local complete intersection over `k`, then
`Def_X ⟶ Def_{P₂}` is smooth.

This is `Deformation.Examples.GluingSituation.isSmooth_toChartProductOfCover_comp_snd` with the
same four hypotheses carried as in
`Deformation.Examples.GluingSituation.isSmooth_toChartProduct`. -/
theorem isSmooth_toChartProduct_comp_snd
    (hΛ : IsDeformationCategory.{u, u, u} (𝟭 (ArtinianLocalAlgCat.{u, u, u} Λ k)))
    (hU₁₂ : Algebra.Smooth k S.P₁₂) (hcomparison : IsSmooth comparison)
    (hU₁ : IsLocalCompleteIntersection k S.P₁) :
    IsSmooth (BasedFunctor.comp (toChartProduct S p₁ p₂ comparison)
      (cofiberedProductSnd (ringDeformationCategoryOver Λ k S.P₁)
        (ringDeformationCategoryOver Λ k S.P₂))) :=
  isSmooth_comp _ _ (isSmooth_toChartProduct S p₁ p₂ comparison hΛ hU₁₂ hcomparison)
    (isSmooth_cofiberedProductSnd_ringDeformation S hU₁)

end Carried

end GluingSituation

end

end Deformation.Examples

end
