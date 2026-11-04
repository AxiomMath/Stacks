module

public import StacksFrontier.AlgebraicGeometry.RelativeSpec.BaseChangeOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecBaseChange

/-!
# Functoriality in the chart of the relative spectrum of an algebra on an algebraic space

Let `X` be an algebraic space over `S` and `A` a quasi-coherent sheaf of commutative
`𝒪_X`-algebras on its small étale site.  `AlgebraicGeometry.Space.chartRelativeSpecChartMap`
attaches to a morphism `h : V' ⟶ V` of étale scheme charts a morphism of schemes
`\underline{Spec}_{V'}(A|_{V'}) ⟶ \underline{Spec}_{V}(A|_V)` over `chartSchemeMap h`.  This file
proves that this assignment is **functorial**: it takes a composite of morphisms of charts to the
composite of the morphisms of relative spectra, and an identity to an identity.

That is the cocycle condition the atlas construction of Stacks 081V needs, and it is the input
`hrel` of `AlgebraicGeometry.Space.isEtaleEquivalenceRelation_chartRelativeSpecSiteMap` asks for.

## Main results

* `AlgebraicGeometry.Space.openChartRestrict_comp`: the restriction of a composite of morphisms
  of charts to an open and its preimage is the composite of the restrictions.  This is
  `AlgebraicGeometry.morphismRestrict_comp` carried through the two subcategory inclusions.
* `AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardComparison_comp`: the direct-image chart
  comparison of `A` is functorial in the chart.  It is the restriction map of `A` on every open,
  so this is functoriality of `A` itself.
* `AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardHom`: the chart comparison as a morphism
  of *algebra sheaves* `A|_V ⟶ (chartSchemeMap h)_* (A|_{V'})`, namely the adjunct of
  `AlgebraicGeometry.Space.chartSchemeAlgebraBaseChangeHom` under the adjunction of Stacks 01SA,
  with `AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardHom_right` identifying its
  underlying map of sheaves of rings with the direct-image comparison and
  `AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardHom_comp` its functoriality.
* `AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardComparison_naturality` and
  `AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardHom_naturality`: the chart comparison is
  **natural in the algebra sheaf**, so that at a fixed morphism of charts it is a natural
  transformation `chartSchemeAlgebraFunctor V ⟶ chartSchemeAlgebraFunctor V' ⋙
  algebraPushforward (chartSchemeMap h)`.  Over a Zariski open both composites are a component of
  the given morphism of algebra sheaves against a restriction map of it, so this is naturality of
  that morphism.
* `AlgebraicGeometry.Space.chartRelativeSpecChartMap_eq`: **the morphism of relative spectra over
  a morphism of charts is the rigid one.**  It is the morphism
  `Stacks.AffineAlgebraEquivalence.relativeSpecMapOverBase` attached to the algebra map
  `A|_V ⟶ (chartSchemeMap h)_*(A|_{V'})`, so it is determined by that algebra map.
* `AlgebraicGeometry.Space.chartRelativeSpecChartMap_comp` and
  `AlgebraicGeometry.Space.chartRelativeSpecChartMap_id`: **the cocycle condition.**

## Implementation notes

**Why this is not read off the cartesian squares.**
`AlgebraicGeometry.Space.isPullback_chartRelativeSpecChartMap` says each square of
`chartRelativeSpecChartMap h` over `chartSchemeMap h` is cartesian, and that is *not* enough: a
cartesian square determines its top edge only up to an automorphism of
`\underline{Spec}_{V'}(A|_{V'})` over `chartScheme V'`, and an affine morphism has such
automorphisms.  At `h = 𝟙 V` the square says only that `chartRelativeSpecChartMap (𝟙 V)` lies
*over* the identity of `chartScheme V`, not that it *is* the identity, and the uniqueness clause
of the lift is circular in exactly that statement.  The cocycle is extra information and it comes
from the algebra side, which is what
`Stacks.AffineAlgebraEquivalence.relativeSpecMapOverBase_comp` supplies.

**The identity law is derived, not proved directly.**  `chartRelativeSpecChartMap (𝟙 V)` is
idempotent by the composition law, and invertible because it is a base change of
`chartSchemeMap (𝟙 V) = 𝟙`, which is an isomorphism; an idempotent isomorphism is the identity.
Proving it from the algebra side instead would need the identity law for
`Stacks.AffineAlgebraEquivalence.relativeSpecMapOverBase`, which cannot even be stated in the
obvious way: the direct image of algebra sheaves along an identity is not the identity functor on
the nose.

**What makes the composition law type-check without transport.**  `chartSchemeMap` is
`BigFppfOver.toScheme` applied to `SmallEtale.toOver`, and both functors act on morphisms by
forgetting structure, so `chartSchemeMap (h' ≫ h) = chartSchemeMap h' ≫ chartSchemeMap h` and
`chartSchemeMap (𝟙 V) = 𝟙` hold by `rfl`.  Every statement below that mentions the composite base
morphism therefore needs no transport along a propositional equality of base morphisms, and the
`eqToHom` such a transport would introduce never appears.

**No `stacks` attribute is carried.**  What is proved here is the cocycle condition of one step of
the atlas construction of Stacks 081V, not a numbered assertion of the source; Stacks 01LX (2)
and 01SA are registered where they are proved, and Definition 0822 is not reached — the morphism
`ν` and the factorization of `f` through it are not constructed here.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AffineAlgebraEquivalence

universe u

namespace AlgebraicGeometry.Space

/-! ### Composition of restrictions of charts to an open -/

section OpenRestrict

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The restriction to an open and its preimage of a composite of morphisms of the big fppf
category over `S` is the composite of the restrictions, on underlying schemes.  This is
`AlgebraicGeometry.morphismRestrict_comp`. -/
theorem openSubSchemeHomOfRestrict_comp {A A' A'' : BigFppfOver B S hS}
    (τ : A'' ⟶ A') (σ : A' ⟶ A) (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    openSubSchemeHomOfRestrict (τ ≫ σ) O =
      openSubSchemeHomOfRestrict τ ((BigFppfOver.toScheme B S hS).map σ ⁻¹ᵁ O) ≫
        openSubSchemeHomOfRestrict σ O :=
  B.inclusion.map_injective (morphismRestrict_comp ((BigFppfOver.toScheme B S hS).map τ)
    ((BigFppfOver.toScheme B S hS).map σ) O)

/-- The restriction to an open and its preimage of a composite of morphisms of the big fppf
category over `S` is the composite of the restrictions. -/
theorem openSubHomOfRestrict_comp {A A' A'' : BigFppfOver B S hS}
    (τ : A'' ⟶ A') (σ : A' ⟶ A) (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    openSubHomOfRestrict (τ ≫ σ) O =
      openSubHomOfRestrict τ ((BigFppfOver.toScheme B S hS).map σ ⁻¹ᵁ O) ≫
        openSubHomOfRestrict σ O :=
  Over.OverMorphism.ext (openSubSchemeHomOfRestrict_comp τ σ O)

/-- **The restriction of a composite of morphisms of étale charts to an open and its preimage is
the composite of the restrictions.** -/
theorem openChartRestrict_comp {U V W : SmallEtale B S hS F} (h' : W ⟶ V) (h : V ⟶ U)
    (O : (chartScheme U).Opens) :
    openChartRestrict B S hS F (h' ≫ h) O =
      openChartRestrict B S hS F h' (chartSchemeMap h ⁻¹ᵁ O) ≫
        openChartRestrict B S hS F h O :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (openSubHomOfRestrict_comp
    ((SmallEtale.toOver B S hS F).map h') ((SmallEtale.toOver B S hS F).map h) O))

end OpenRestrict

/-! ### Functoriality of the chart comparison of an algebra sheaf -/

section Comparison

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    {V'' V' V : SmallEtale B S hS X.1} (h' : V'' ⟶ V') (h : V' ⟶ V)

/-- **The direct-image chart comparison of an algebra sheaf is functorial in the chart.**  Over
a Zariski open the comparison is the restriction map of `A` along the morphism of étale charts
that open determines (`AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardComparison_app`), so
this is functoriality of `A` together with
`AlgebraicGeometry.Space.openChartRestrict_comp`. -/
theorem chartSchemeAlgebraPushforwardComparison_comp :
    chartSchemeAlgebraPushforwardComparison B S hS X A (h' ≫ h) =
      chartSchemeAlgebraPushforwardComparison B S hS X A h ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} (chartSchemeMap h).base).map
          (chartSchemeAlgebraPushforwardComparison B S hS X A h') := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun Oop => ?_))
  obtain ⟨O⟩ := Oop
  change A.right.obj.map ((openChartRestrictNatTrans B S hS X.1 (h' ≫ h)).app O).op =
    A.right.obj.map ((openChartRestrictNatTrans B S hS X.1 h).app O).op ≫
      A.right.obj.map ((openChartRestrictNatTrans B S hS X.1 h').app
        (chartSchemeMap h ⁻¹ᵁ O)).op
  rw [show (openChartRestrictNatTrans B S hS X.1 (h' ≫ h)).app O =
      openChartRestrict B S hS X.1 h' (chartSchemeMap h ⁻¹ᵁ O) ≫
        openChartRestrict B S hS X.1 h O from openChartRestrict_comp h' h O]
  exact A.right.obj.map_comp _ _

/-- **The chart comparison of an algebra sheaf as a morphism of algebra sheaves**
`A|_V ⟶ (chartSchemeMap h)_* (A|_{V'})`: the adjunct of
`AlgebraicGeometry.Space.chartSchemeAlgebraBaseChangeHom` under the adjunction of Stacks 01SA
between base change and direct image of algebra sheaves.

This is the algebra map which, by
`AlgebraicGeometry.Space.chartRelativeSpecChartMap_eq`, determines the morphism of relative
spectra over `chartSchemeMap h`. -/
def chartSchemeAlgebraPushforwardHom :
    chartSchemeAlgebra B S hS X A V ⟶
      (algebraPushforward (chartSchemeMap h)).obj (chartSchemeAlgebra B S hS X A V') :=
  (algebraPullbackPushforwardAdjunction (chartSchemeMap h)).homEquiv _ _
    (chartSchemeAlgebraBaseChangeHom B S hS X A h)

/-- **The underlying map of sheaves of rings of the algebra-level chart comparison is the
direct-image comparison.**

The adjunction of Stacks 01SA is computed on underlying sheaves of rings by
`Stacks.AffineAlgebraEquivalence.homEquiv_right`: it restricts the given map along the canonical
map from the inverse image into the base change and then transposes for sheaves of rings.  That
restriction is `AlgebraicGeometry.Space.chartSchemeAlgebraPullbackComparison` by
`AlgebraicGeometry.Space.algebraPullbackMap_comp_chartSchemeAlgebraBaseChangeHom`, and that in
turn is by definition the transpose of the direct-image comparison, so the two transpositions
cancel. -/
theorem chartSchemeAlgebraPushforwardHom_right :
    (chartSchemeAlgebraPushforwardHom B S hS X A h).right =
      chartSchemeAlgebraPushforwardComparison B S hS X A h :=
  Eq.trans
    (homEquiv_right (chartSchemeMap h) (chartSchemeAlgebra B S hS X A V)
      (chartSchemeAlgebra B S hS X A V') (chartSchemeAlgebraBaseChangeHom B S hS X A h))
    (Eq.trans
      (congrArg (fun z ↦ (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
            (chartSchemeMap h).base).homEquiv _ _ z)
        (algebraPullbackMap_comp_chartSchemeAlgebraBaseChangeHom B S hS X A h))
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        (chartSchemeMap h).base).homEquiv _ _).apply_symm_apply _))

/-- **The algebra-level chart comparison is functorial in the chart.**  A morphism of algebra
sheaves is determined by its underlying map of sheaves of rings, and there this is
`AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardComparison_comp`. -/
theorem chartSchemeAlgebraPushforwardHom_comp :
    chartSchemeAlgebraPushforwardHom B S hS X A (h' ≫ h) =
      chartSchemeAlgebraPushforwardHom B S hS X A h ≫
        (algebraPushforward (chartSchemeMap h)).map
          (chartSchemeAlgebraPushforwardHom B S hS X A h') := by
  ext1
  rw [chartSchemeAlgebraPushforwardHom_right]
  exact (chartSchemeAlgebraPushforwardComparison_comp B S hS X A h' h).trans
    (by rw [← chartSchemeAlgebraPushforwardHom_right,
      ← chartSchemeAlgebraPushforwardHom_right]; rfl)

end Comparison

/-! ### Naturality of the chart comparison in the algebra sheaf -/

section ComparisonNaturality

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) {A C : AlgebraSheaf.{u, u} B S hS X.1 X.2} (α : A ⟶ C)
    {V' V : SmallEtale B S hS X.1} (h : V' ⟶ V)

/-- **The direct-image chart comparison is natural in the algebra sheaf.**  Over a Zariski open
both composites are the component of `α` at an étale chart of `X` followed by, or preceded by,
a restriction map, so this is the naturality of `α` itself. -/
theorem chartSchemeAlgebraPushforwardComparison_naturality :
    (chartSchemeCommRingRestriction B S hS X V).map α.right ≫
        chartSchemeAlgebraPushforwardComparison B S hS X C h =
      chartSchemeAlgebraPushforwardComparison B S hS X A h ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} (chartSchemeMap h).base).map
          ((chartSchemeCommRingRestriction B S hS X V').map α.right) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun Oop => ?_))
  obtain ⟨O⟩ := Oop
  change α.right.hom.app (op ((openChartFunctor B S hS X.1 V).obj O)) ≫
      C.right.obj.map ((openChartRestrictNatTrans B S hS X.1 h).app O).op =
    A.right.obj.map ((openChartRestrictNatTrans B S hS X.1 h).app O).op ≫
      α.right.hom.app (op ((openChartFunctor B S hS X.1 V').obj
        ((Opens.map (chartSchemeMap h).base).obj O)))
  exact (α.right.hom.naturality ((openChartRestrictNatTrans B S hS X.1 h).app O).op).symm

/-- **The algebra-level chart comparison is natural in the algebra sheaf.**

For a morphism `α : A ⟶ C` of sheaves of commutative `𝒪_X`-algebras and a morphism
`h : V' ⟶ V` of étale scheme charts of `X`, the chart restriction of `α` at `V` followed by the
chart comparison of `C` is the chart comparison of `A` followed by the direct image along
`chartSchemeMap h` of the chart restriction of `α` at `V'`.  That is to say,
`AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardHom` at `h` is a natural transformation
`chartSchemeAlgebraFunctor V ⟶ chartSchemeAlgebraFunctor V' ⋙ algebraPushforward
(chartSchemeMap h)`.

A morphism of algebra sheaves is determined by its underlying map of sheaves of rings, and there
this is `AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardComparison_naturality`.  Nothing is
assumed of `A`, `C` or `α`: no quasi-coherence, and no condition on the chart. -/
theorem chartSchemeAlgebraPushforwardHom_naturality :
    (chartSchemeAlgebraFunctor B S hS X V).map α ≫
        chartSchemeAlgebraPushforwardHom B S hS X C h =
      chartSchemeAlgebraPushforwardHom B S hS X A h ≫
        (algebraPushforward (chartSchemeMap h)).map
          ((chartSchemeAlgebraFunctor B S hS X V').map α) := by
  ext1
  change ((chartSchemeAlgebraFunctor B S hS X V).map α).right ≫
      (chartSchemeAlgebraPushforwardHom B S hS X C h).right =
    (chartSchemeAlgebraPushforwardHom B S hS X A h).right ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} (chartSchemeMap h).base).map
        ((chartSchemeAlgebraFunctor B S hS X V').map α).right
  rw [chartSchemeAlgebraPushforwardHom_right, chartSchemeAlgebraPushforwardHom_right,
    chartSchemeAlgebraFunctor_map_right, chartSchemeAlgebraFunctor_map_right]
  exact chartSchemeAlgebraPushforwardComparison_naturality B S hS X α h

end ComparisonNaturality

/-! ### The cocycle condition -/

section Cocycle

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent)

/-- **The morphism of relative spectra attached to a morphism of étale charts is the rigid
morphism over `chartSchemeMap h` determined by the algebra-level chart comparison.**

`AlgebraicGeometry.Space.chartRelativeSpecChartMap` is built from contravariance of the relative
spectrum in the algebra followed by the comparison of Stacks 01LX (2) and the projection of the
fibre product; by
`Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeMap_eq_relativeSpecMapOverBase` that
composite is the morphism which the universal property of the relative spectrum over a varying
base attaches to the adjunct of the algebra comparison, and the adjunct is
`AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardHom` by definition. -/
theorem chartRelativeSpecChartMap_eq {V' V : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    haveI := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V
    haveI := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V'
    chartRelativeSpecChartMap B S hS X A hA h =
      relativeSpecMapOverBase (chartSchemeMap h) (chartSchemeAlgebra B S hS X A V)
        (chartSchemeAlgebra B S hS X A V')
        (chartSchemeAlgebraPushforwardHom B S hS X A h) :=
  have := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V
  have := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V'
  relativeSpecBaseChangeMap_eq_relativeSpecMapOverBase (chartSchemeMap h)
    (chartSchemeAlgebra B S hS X A V) (chartSchemeAlgebra B S hS X A V')
    (chartSchemeAlgebraBaseChangeHom B S hS X A h)

/-- **The cocycle condition: the morphism of relative spectra attached to a composite of
morphisms of étale charts is the composite of the morphisms attached to the factors.**

This is the identity the atlas construction of Stacks 081V needs and which the cartesian squares
of `AlgebraicGeometry.Space.isPullback_chartRelativeSpecChartMap` cannot supply; see the
implementation notes.  Nothing beyond quasi-coherence of `A` is assumed. -/
theorem chartRelativeSpecChartMap_comp {V'' V' V : SmallEtale B S hS X.1}
    (h' : V'' ⟶ V') (h : V' ⟶ V) :
    chartRelativeSpecChartMap B S hS X A hA (h' ≫ h) =
      chartRelativeSpecChartMap B S hS X A hA h' ≫
        chartRelativeSpecChartMap B S hS X A hA h := by
  have := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V
  have := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V'
  have := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V''
  rw [chartRelativeSpecChartMap_eq B S hS X A hA h',
    chartRelativeSpecChartMap_eq B S hS X A hA h]
  refine Eq.trans ?_ (relativeSpecMapOverBase_comp (chartSchemeMap h') (chartSchemeMap h)
    (chartSchemeAlgebra B S hS X A V) (chartSchemeAlgebra B S hS X A V')
    (chartSchemeAlgebra B S hS X A V'')
    (chartSchemeAlgebraPushforwardHom B S hS X A h)
    (chartSchemeAlgebraPushforwardHom B S hS X A h')).symm
  exact Eq.trans (chartRelativeSpecChartMap_eq B S hS X A hA (h' ≫ h))
    (congrArg (relativeSpecMapOverBase (chartSchemeMap (h' ≫ h))
        (chartSchemeAlgebra B S hS X A V) (chartSchemeAlgebra B S hS X A V''))
      (chartSchemeAlgebraPushforwardHom_comp B S hS X A h' h))

/-- **The morphism of relative spectra attached to the identity of an étale chart is the
identity.**

It is idempotent by `AlgebraicGeometry.Space.chartRelativeSpecChartMap_comp` and invertible
because `AlgebraicGeometry.Space.chartRelativeSpecChartMap_of_isStableUnderBaseChange` makes it a
base change of `chartSchemeMap (𝟙 V) = 𝟙`, and an idempotent isomorphism is the identity. -/
theorem chartRelativeSpecChartMap_id (V : SmallEtale B S hS X.1) :
    chartRelativeSpecChartMap B S hS X A hA (𝟙 V) =
      𝟙 (chartRelativeSpec B S hS X A hA V) := by
  have : IsIso (chartRelativeSpecChartMap B S hS X A hA (𝟙 V)) :=
    chartRelativeSpecChartMap_of_isStableUnderBaseChange B S hS X A hA (𝟙 V)
      (MorphismProperty.isomorphisms Scheme.{u})
      (show IsIso (chartSchemeMap (𝟙 V)) from
        show IsIso (𝟙 (chartScheme V)) from inferInstance)
  have hidem := chartRelativeSpecChartMap_comp B S hS X A hA (𝟙 V) (𝟙 V)
  rw [Category.comp_id] at hidem
  refine ((cancel_epi (chartRelativeSpecChartMap B S hS X A hA (𝟙 V))).mp ?_).symm
  rw [Category.comp_id]
  exact hidem

end Cocycle

end AlgebraicGeometry.Space

end
