module

public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePrimedConnectedFactorizations
import StacksCore.Tactic.StacksAttribute

/-!
# The pushforward identity of Stacks 07AT, with its site-theoretic inputs discharged

Let `f : 𝒳 ⟶ 𝒴` be a flat (respectively smooth) 1-morphism of algebraic stacks over `S`, let
`g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` and `g' : Sh(𝒴_{flat,fppf}) ⟶ Sh(𝒴_{fppf})` be the
comparison morphisms of topoi of **Stacks 0788** (2) (respectively the lisse-étale ones of
**Stacks 0788** (1)), and let `f'` be the restriction of `f` to the two subsites, which is the
continuous and cocontinuous site functor of the *first* assertion of **Stacks 07AT**. Beyond that
first assertion the source asserts two identities:

`f'_*(g')^{-1} = g^{-1}f_*`  and  `g'_!(f')^{-1} = f^{-1}g_!`.

This file states and proves the **first of those two identities, objectwise**, with no hypothesis
beyond the sheaf condition on the presheaf the identity is applied to: for every object `y` of the
subsite of `𝒴` and every sheaf `ℱ` of sets on `𝒳_{fppf}` (respectively `𝒳_{étale}`), the value at
`y` of `f'_*` of the restriction of `ℱ` is the value at `y` of `f_*ℱ`.

## What this adds to the registrations already in the tree

`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfSiteFunctor.lean` and
`StacksFrontier/AlgebraicGeometry/Stacks/LisseEtaleSiteFunctor.lean` register **Stacks 07AT** on the
site functor and on its continuity and cocontinuity — the first assertion only. The identity
above is a separate assertion, and
`AlgebraicGeometry.Stack.FlatFppf.primedPushforwardAmbientEquiv` of
`StacksFrontier/AlgebraicGeometry/Stacks/SubsitePushforwardAmbientComparison.lean` states it with
four inputs supplied by the caller: a topology on the 2-fibre product `V ×_{y, 𝒴} 𝒳`, the sheaf
condition for `pr^{-1}ℱ` on it, and the two local-factorization conditions of **Stacks 07AK** for
the inclusion of the primed subcategory. All four are now theorems:

* the topology is `AlgebraicGeometry.Stack.ambientTwoFibreProductTopology`, and the sheaf
  condition is `AlgebraicGeometry.Stack.isSheaf_comp_ambientProjection`;
* the local-factorization condition is
  `AlgebraicGeometry.Stack.FlatFppf.hasLocalFactorizations_primedInclusion` and its lisse-étale
  sibling;
* local connectedness of the factorizations is
  `AlgebraicGeometry.Stack.FlatFppf.hasLocallyConnectedFactorizations_primedInclusion` and its
  lisse-étale sibling.

The declarations below are the instances of the conditional statements at those theorems, in the
style of `StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfDerivedLowerShriekUnconditional.lean`. The
conditional statements keep their exact interfaces.

## What is in scope and what is not

Only the first of the two identities, and only objectwise, for a sheaf of sets. Three further
pieces of the source's assertion are not reached here and are not claimed:

* **Naturality in `y`.** The identity is a bijection for each object `y` of the subsite of `𝒴`
  separately; the source reads it as an equality of sheaves on that subsite, which in addition
  asks that the bijections commute with the restriction maps. Naturality of the first of the three
  comparisons composing the bijection is
  `AlgebraicGeometry.Stack.FlatFppf.primedPushforwardSectionsEquiv_naturality` in
  `StacksFrontier/AlgebraicGeometry/Stacks/SubsitePushforwardFormulaNaturality.lean`; the other two
  have no naturality statement in either tree, in `y` or in `ℱ`.
* **Abelian and module coefficients.** The bijection is for presheaves of sets, the generality
  `CategoryTheory.SubsitePushforward.primedPushforwardAmbientEquiv` is proved in. The source's
  `f'_*` and `g^{-1}` act on sheaves of abelian groups as well, and no `AddCommGrpCat`-valued form
  of the comparison exists.
* **The second identity `g'_!(f')^{-1} = f^{-1}g_!`.** Nothing in either tree states it.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.primedPushforwardAmbientEquiv'`: **Stacks 07AT** (2), the
  identity `f'_*(g')^{-1} = g^{-1}f_*` at one flat object of `𝒴`, for a sheaf of sets.
* `AlgebraicGeometry.Stack.LisseEtale.primedPushforwardAmbientEquiv'`: **Stacks 07AT** (1), the
  same at one smooth object of `𝒴`.

## Implementation notes

The coefficient universe is `Type (u + 1)`, the universe in which the two sites of an algebraic
stack are essentially small; that is what discharges the three pointwise-right-Kan-extension
instance arguments of the conditional statements, by the argument of
`AlgebraicGeometry.Stack.FlatFppf.hasPointwiseRightKanExtension_inclusion_ab`. The three are
proved below rather than assumed, and installed as local instances so that the statements can name
`Functor.ran`.

This file is not `FlatFppfSiteFunctor.lean` or `LisseEtaleSiteFunctor.lean`, where the first
assertion of 07AT is registered, because the comparison it instantiates is downstream of both:
`StacksFrontier/AlgebraicGeometry/Stacks/SubsitePushforwardFormula.lean` imports them, and
`SubsitePushforwardAmbientComparison.lean` imports that.

## References

* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 06W6](https://stacks.math.columbia.edu/tag/06W6)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
* [Stacks Project, Tag 07AU](https://stacks.math.columbia.edu/tag/07AU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- Restriction of presheaves of sets along the underlying functor of a 1-morphism of algebraic
stacks admits a pointwise right Kan extension, at coefficients in `Type (u + 1)`: the comma
categories are essentially small in that universe, the two sites having objects there and
morphisms in `Type u`. -/
theorem hasPointwiseRightKanExtension_homFunctor :
    ∀ G : (𝒳.val.val.obj)ᵒᵖ ⥤ Type (u + 1),
      f.hom.hom.toFunctor.op.HasPointwiseRightKanExtension G := fun _ Y => by
  have := hasLimitsOfShape_of_essentiallySmall.{u + 1}
    (StructuredArrow Y f.hom.hom.toFunctor.op) (Type (u + 1))
  infer_instance

attribute [local instance] hasPointwiseRightKanExtension_homFunctor

namespace FlatFppf

/-- Restriction of presheaves of sets along the inclusion of the flat objects of `𝒳` followed by
the underlying functor of `f` admits a pointwise right Kan extension, by the same essential
smallness as `AlgebraicGeometry.Stack.hasPointwiseRightKanExtension_homFunctor`. -/
theorem hasPointwiseRightKanExtension_inclusion_comp_homFunctor :
    ∀ G : (FlatFppf B S hS 𝒳)ᵒᵖ ⥤ Type (u + 1),
      (inclusion B S hS 𝒳 ⋙ f.hom.hom.toFunctor).op.HasPointwiseRightKanExtension G :=
  fun _ Y => by
  have := hasLimitsOfShape_of_essentiallySmall.{u + 1}
    (StructuredArrow Y (inclusion B S hS 𝒳 ⋙ f.hom.hom.toFunctor).op) (Type (u + 1))
  infer_instance

/-- Restriction of presheaves of sets along the site functor of **Stacks 07AT** (2) between the
flat-fppf sites admits a pointwise right Kan extension, by the same essential smallness. This is
what makes `f'_*` available on presheaves of sets with sections in `Type (u + 1)`. -/
theorem hasPointwiseRightKanExtension_primedSiteFunctor
    (hf : AlgebraicStacks.IsFlat B S hS f) :
    ∀ G : (FlatFppf B S hS 𝒳)ᵒᵖ ⥤ Type (u + 1),
      (primedSiteFunctor B S hS f hf).op.HasPointwiseRightKanExtension G := fun _ Y => by
  have := hasLimitsOfShape_of_essentiallySmall.{u + 1}
    (StructuredArrow Y (primedSiteFunctor B S hS f hf).op) (Type (u + 1))
  infer_instance

attribute [local instance] hasPointwiseRightKanExtension_inclusion_comp_homFunctor
  hasPointwiseRightKanExtension_primedSiteFunctor

/-- **Stacks 07AT (2), the identity `f'_*(g')^{-1} = g^{-1}f_*`, at one flat object of `𝒴` and
for a sheaf of sets, with no further hypothesis.** For a flat 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks, a flat object `y` of `𝒴` and a sheaf `ℱ` of sets on the fppf site of `𝒳`, the value at
`y` of the pushforward along the restriction `f'` of `f` to the flat-fppf sites of the restriction
of `ℱ` to the flat-fppf site of `𝒳` is the value at `y` of the pushforward of `ℱ` along `f`.

This is `AlgebraicGeometry.Stack.FlatFppf.primedPushforwardAmbientEquiv` at the topology of
`AlgebraicGeometry.Stack.ambientTwoFibreProductTopology`, whose three remaining inputs are
`AlgebraicGeometry.Stack.isSheaf_comp_ambientProjection`,
`AlgebraicGeometry.Stack.FlatFppf.hasLocalFactorizations_primedInclusion` and
`AlgebraicGeometry.Stack.FlatFppf.hasLocallyConnectedFactorizations_primedInclusion`. -/
@[stacks 07AT "part (2), the identity `f'_*(g')^{-1} = g^{-1}f_*` for the flat-fppf site, at one \
flat object `y` of `𝒴` and for a sheaf of sets, with NO hypothesis beyond the sheaf condition on \
`ℱ`: the topology on the 2-fibre product `V ×_{y, 𝒴} 𝒳` that \
`AlgebraicGeometry.Stack.FlatFppf.primedPushforwardAmbientEquiv` takes as `J` is \
`AlgebraicGeometry.Stack.ambientTwoFibreProductTopology`, and its arguments `hℱ`, `hfac` and \
`hconn` are the theorems `AlgebraicGeometry.Stack.isSheaf_comp_ambientProjection`, \
`AlgebraicGeometry.Stack.FlatFppf.hasLocalFactorizations_primedInclusion` and \
`AlgebraicGeometry.Stack.FlatFppf.hasLocallyConnectedFactorizations_primedInclusion`, each proved \
for every algebraic stack. The site functor itself and its continuity and cocontinuity, which are \
the first assertion of the tag, are registered in \
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfSiteFunctor.lean`. Three pieces of the tag are \
not \
covered here: naturality of the bijection in `y`, so that it \
becomes an equality of sheaves on `𝒴_{flat,fppf}` rather than a family of bijections; the same \
identity at abelian rather than set coefficients; and the second identity \
`g'_!(f')^{-1} = f^{-1}g_!`. The first and the third are registered in \
`StacksFrontier/AlgebraicGeometry/Stacks/SubsiteSheafPushforwardBaseChange.lean`; the abelian form \
is claimed nowhere in the tree, and the tag does not ask for it -- the source's `ℱ` is a sheaf \
of sets, which is what the functors of a morphism of topoi act on"]
def primedPushforwardAmbientEquiv' (hf : AlgebraicStacks.IsFlat B S hS f)
    (y : FlatFppf B S hS 𝒴) (ℱ : (𝒳.val.val.obj)ᵒᵖ ⥤ Type (u + 1))
    (hℱ : Presieve.IsSheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) ℱ) :
    ((primedSiteFunctor B S hS f hf).op.ran.obj ((inclusion B S hS 𝒳).op ⋙ ℱ)).obj (op y) ≃
      (f.hom.hom.toFunctor.op.ran.obj ℱ).obj (op y.obj) :=
  primedPushforwardAmbientEquiv B S hS f hf y ℱ
    (ambientTwoFibreProductTopology B S hS f y .fppf)
    (isSheaf_comp_ambientProjection B S hS f y .fppf ℱ hℱ)
    (hasLocalFactorizations_primedInclusion B S hS f y)
    (hasLocallyConnectedFactorizations_primedInclusion B S hS f y)

end FlatFppf

namespace LisseEtale

/-- Restriction of presheaves of sets along the inclusion of the smooth objects of `𝒳` followed
by the underlying functor of `f` admits a pointwise right Kan extension, by the same essential
smallness as `AlgebraicGeometry.Stack.hasPointwiseRightKanExtension_homFunctor`. -/
theorem hasPointwiseRightKanExtension_inclusion_comp_homFunctor :
    ∀ G : (LisseEtale.{u, w} B S hS 𝒳)ᵒᵖ ⥤ Type (u + 1),
      (inclusion.{u, w} B S hS 𝒳 ⋙ f.hom.hom.toFunctor).op.HasPointwiseRightKanExtension G :=
  fun _ Y => by
  have := hasLimitsOfShape_of_essentiallySmall.{u + 1}
    (StructuredArrow Y (inclusion.{u, w} B S hS 𝒳 ⋙ f.hom.hom.toFunctor).op) (Type (u + 1))
  infer_instance

/-- Restriction of presheaves of sets along the site functor of **Stacks 07AT** (1) between the
lisse-étale sites admits a pointwise right Kan extension, by the same essential smallness. This
is what makes `f'_*` available on presheaves of sets with sections in `Type (u + 1)`. -/
theorem hasPointwiseRightKanExtension_primedSiteFunctor
    (hf : AlgebraicStacks.IsSmooth B S hS f) :
    ∀ G : (LisseEtale.{u, w} B S hS 𝒳)ᵒᵖ ⥤ Type (u + 1),
      (primedSiteFunctor.{u, w} B S hS f hf).op.HasPointwiseRightKanExtension G := fun _ Y => by
  have := hasLimitsOfShape_of_essentiallySmall.{u + 1}
    (StructuredArrow Y (primedSiteFunctor.{u, w} B S hS f hf).op) (Type (u + 1))
  infer_instance

attribute [local instance] hasPointwiseRightKanExtension_inclusion_comp_homFunctor
  hasPointwiseRightKanExtension_primedSiteFunctor

/-- **Stacks 07AT (1), the identity `f'_*(g')^{-1} = g^{-1}f_*`, at one smooth object of `𝒴` and
for a sheaf of sets, with no further hypothesis.** For a smooth 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks, a smooth object `y` of `𝒴` and a sheaf `ℱ` of sets on the étale site of `𝒳`,
the value at `y` of the pushforward along the restriction `f'` of `f` to the lisse-étale sites of
the restriction of `ℱ` to the lisse-étale site of `𝒳` is the value at `y` of the pushforward of
`ℱ` along `f`.

This is `AlgebraicGeometry.Stack.LisseEtale.primedPushforwardAmbientEquiv` at the topology of
`AlgebraicGeometry.Stack.ambientTwoFibreProductTopology`, whose three remaining inputs are
`AlgebraicGeometry.Stack.isSheaf_comp_ambientProjection`,
`AlgebraicGeometry.Stack.LisseEtale.hasLocalFactorizations_primedInclusion` and
`AlgebraicGeometry.Stack.LisseEtale.hasLocallyConnectedFactorizations_primedInclusion`. -/
@[stacks 07AT "part (1), the identity `f'_*(g')^{-1} = g^{-1}f_*` for the lisse-étale site, at \
one smooth object `y` of `𝒴` and for a sheaf of sets, with NO hypothesis beyond the sheaf \
condition on `ℱ`: the topology on the 2-fibre product `V ×_{y, 𝒴} 𝒳` that \
`AlgebraicGeometry.Stack.LisseEtale.primedPushforwardAmbientEquiv` takes as `J` is \
`AlgebraicGeometry.Stack.ambientTwoFibreProductTopology`, and its arguments `hℱ`, `hfac` and \
`hconn` are the theorems `AlgebraicGeometry.Stack.isSheaf_comp_ambientProjection`, \
`AlgebraicGeometry.Stack.LisseEtale.hasLocalFactorizations_primedInclusion` and \
`AlgebraicGeometry.Stack.LisseEtale.hasLocallyConnectedFactorizations_primedInclusion`, each \
proved for every algebraic stack. The site functor itself and its continuity and cocontinuity, \
which are the first assertion of the tag, are registered in \
`StacksFrontier/AlgebraicGeometry/Stacks/LisseEtaleSiteFunctor.lean`. Three pieces of the tag are \
not covered here: naturality of the bijection in `y`, so \
that it becomes an equality of sheaves on `𝒴_{lisse,étale}` rather than a family of bijections; \
the same identity at abelian rather than set coefficients; and the second identity \
`g'_!(f')^{-1} = f^{-1}g_!`. The first and the third are registered in \
`StacksFrontier/AlgebraicGeometry/Stacks/SubsiteSheafPushforwardBaseChange.lean`; the abelian form \
is claimed nowhere in the tree, and the tag does not ask for it -- the source's `ℱ` is a sheaf \
of sets, which is what the functors of a morphism of topoi act on"]
def primedPushforwardAmbientEquiv' (hf : AlgebraicStacks.IsSmooth B S hS f)
    (y : LisseEtale.{u, w} B S hS 𝒴) (ℱ : (𝒳.val.val.obj)ᵒᵖ ⥤ Type (u + 1))
    (hℱ : Presieve.IsSheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale) ℱ) :
    ((primedSiteFunctor.{u, w} B S hS f hf).op.ran.obj
        ((inclusion.{u, w} B S hS 𝒳).op ⋙ ℱ)).obj (op y) ≃
      (f.hom.hom.toFunctor.op.ran.obj ℱ).obj (op y.obj) :=
  primedPushforwardAmbientEquiv B S hS f hf y ℱ
    (ambientTwoFibreProductTopology B S hS f y .etale)
    (isSheaf_comp_ambientProjection B S hS f y .etale ℱ hℱ)
    (hasLocalFactorizations_primedInclusion B S hS f y)
    (hasLocallyConnectedFactorizations_primedInclusion B S hS f y)

end LisseEtale

end AlgebraicGeometry.Stack

end
