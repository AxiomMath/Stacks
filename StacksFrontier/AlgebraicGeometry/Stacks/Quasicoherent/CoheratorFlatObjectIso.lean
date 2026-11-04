module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorCanonical
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorFlatObjectRestriction

/-!
# The coherator is the identity on the small étale site of a flat object (Stacks 0GQK)

Let `𝒳` be an algebraic stack and `x` an object of `𝒳` lying over a scheme `U` with
`x : U → 𝒳` flat.  **Stacks 0GQK** says that for `𝓕` in `LQCoh^fbc(𝒪_𝒳)` the coherator `Q` of
**Stacks 0778** satisfies `Q(𝓕)|_{U_ét} = 𝓕|_{U_ét}`.  The identification is the restriction to
`U_ét` of the adjunction map `Q(𝓕) ⟶ 𝓕`, whose kernel and cokernel are parasitic by
**Stacks 0779** part (2); a map with parasitic kernel and cokernel restricts to an isomorphism on
the small étale site of a flat object, since that site only sees flat objects.

The source writes `QCoh^{fbc}(𝒪_𝒳)`; the coherator is defined on `LQCoh^{fbc}(𝒪_𝒳)`, the
category the proof quotes **Stacks 0779** for, and that is the reading taken here, with the
corrected flat base change property of **Stacks 0762**.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isIso_restrict_coheratorAdjunction_counit`:
  **Stacks 0GQK**.

## References

* [Stacks Project, Tag 0GQK](https://stacks.math.columbia.edu/tag/0GQK)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 0GQK.** Let `x` be an object of an algebraic stack `𝒳` lying over a scheme `U` such
that `x : U → 𝒳` is flat, and let `𝓕` be in `LQCoh^fbc(𝒪_𝒳)`.  Then `Q(𝓕)|_{U_ét} = 𝓕|_{U_ét}`:
the restriction to the small étale site of `U` of the adjunction map `Q(𝓕) ⟶ 𝓕` of the coherator
of **Stacks 0778** is an isomorphism. -/
@[stacks 0GQK "Q(F)|_{U_ét} = F|_{U_ét} for x : U → 𝒳 flat and F in LQCoh^fbc(𝒪_𝒳): the \
  restriction of the adjunction map Q(F) → F to U_ét is an isomorphism"]
theorem isIso_restrict_coheratorAdjunction_counit (F : Stack.fppfModules B S hS 𝒳)
    (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F)
    (x : 𝒳.val.val.obj) (hx : flatObject B S hS 𝒳.val x) :
    IsIso ((restrictModuleFunctorToSmallEtale B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids x (etaleTopology B) (etaleTopology_le_topology B)).map
        ((coheratorAdjunction B S hS 𝒳).counit.app F).val) :=
  isIso_restrictModuleFunctorToSmallEtale_map_of_isParasitic_sheaf B S hS E h _
    (isParasitic_kernel_and_cokernel_coheratorAdjunction_counit B S hS 𝒳 E h F hF).1
    (isParasitic_kernel_and_cokernel_coheratorAdjunction_counit B S hS 𝒳 E h F hF).2 x hx

end AlgebraicGeometry.Stack.AlgebraicStacks
