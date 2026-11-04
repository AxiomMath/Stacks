module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.BeckChevalley

/-!
# The small pro-étale direct image as an embedding of topoi

Let `f : T ⟶ S` be a morphism in a chosen big pro-étale site. Stacks 09AA asserts three things
about the morphism of topoi `AlgebraicGeometry.ProEtale.smallProetaleMorphism` attached to a
*closed immersion* `i : Z ⟶ X`:

1. the inverse image `i⁻¹` commutes with limits;
2. the direct image `i_*` is fully faithful;
3. the counit `i⁻¹ i_* ⟹ id` is a natural isomorphism.

This file supplies the three implications that turn the one affine input of the source, Stacks
09BL, into those three conclusions, and it records which of them are formal and which are not.

**Clauses (2) and (3) are equivalent, and the equivalence is formal.** It holds for any
adjunction whatsoever, by Sites 04D6 (h), and for the pro-étale morphism it is
`AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_iff_pushforward_fullyFaithful`
below. So neither of (2) and (3) can be *proved* from the other: a derivation of (2) from (3)
together with a derivation of (3) from (2) proves nothing at all, and an argument of that shape
is the one fallacy this file exists to make visible. Both clauses have a single source, namely the
invertibility of the counit over the members of a covering family, which is
`AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_coversTop_of_counit`
(Zariski locality on the target, with its Beck–Chevalley input discharged). Clause (2) is
derived from that hub here; it is not derived from clause (3) in the abstract.

**Clause (1) is not formal and does not follow from (2) or (3).** The inverse image is a left
adjoint, so it preserves colimits for free, and it preserves *finite* limits by the
`MorphismOfTopoi.preservesFiniteLimits` field of
`AlgebraicGeometry.ProEtale.smallProetaleMorphism`. Preservation of arbitrary limits is a
genuinely different assertion: it holds because `i⁻¹` is itself a *right* adjoint, the left
adjoint being the functor `i^{Sh}_!` of Stacks 09BL (3). A left adjoint whose right adjoint is
fully faithful need not preserve limits — a reflector onto a reflective subcategory is rarely
continuous — so no rearrangement of (2) and (3) yields (1); the left adjoint is an extra input.
Clause (1) is therefore stated here with that adjunction as an explicit hypothesis.

## Main results

All four live in the namespace `AlgebraicGeometry.ProEtale`.

* `smallProetaleMorphism_counit_isIso_iff_pushforward_fullyFaithful`: clauses (2) and (3) are
  equivalent. Unconditional.
* `smallProetaleMorphism_pushforward_fullyFaithful_of_coversTop_of_counit`: clause (2), from the
  same covering hypothesis that gives clause (3).
* `smallProetaleMorphism_inverseImage_preservesLimits_of_leftAdjoint`: clause (1), from a left
  adjoint to the inverse image. Unconditional in that hypothesis.
* `smallProetaleMorphism_preservesLimits_fullyFaithful_counit_isIso`: the three clauses
  together, from the two inputs of Stacks 09BL.

## What this supplies for Stacks 09AA, and what it does not

No `stacks` attribute is attached to any declaration here: 09AA is a statement about closed
immersions, and the closed-immersion hypothesis is used nowhere below. The statements are made
for an arbitrary morphism `f` of the chosen big site, which is the generality the arguments have.

What remains between the results below and 09AA is **Stacks 09BL**, the affine case, which is
absent from the library. Concretely, for a closed immersion `i : Z ⟶ X` one has to produce:

1. a family `U : ι → SmallProetale B X.obj X.property` covering the final object of the small
   pro-étale site of `X` whose members are affine. This is available: the affine objects of that
   site do cover its final object, by
   `AlgebraicGeometry.ProEtale.SmallProetale.coversTop_affine`. The index bound `B.coveringBound`
   carried by `AlgebraicGeometry.ProEtale.SmallProetale.IsCovering` is no obstruction, because by
   `AlgebraicGeometry.ProEtale.SmallProetale.precoverage_eq_comap` it imposes no condition on the
   covering *presieves* of the small site;
2. the hypothesis `hcounit` over such a family, which is the third assertion of clause (5) of
   09BL for the base-changed closed immersions `Z ×_X U i ⟶ U i` of affine schemes. The reduction
   of clauses (2) and (3) to exactly this hypothesis, over the affine objects, is
   `AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_affineCounit`;
3. the hypothesis `hshriek`, which is clause (3) of 09BL, the left adjoint `i^{Sh}_!`.

For clause (1) there is a second route, which does not need a *global* left adjoint and is the
one the source's "local on `X`" remark suggests: limits of sheaves of sets are detected by
evaluation on a cover-dense family of objects, so it suffices that `i⁻¹` preserve limits after
evaluation at the objects factoring through an affine open of `X`, where 09BL applies. That
route needs, beyond 09BL (3), the evaluation of `i⁻¹` on weakly contractible objects, which is
09BL (2), and the fact that the small pro-étale site has enough affine, quasi-compact, weakly
contractible objects, which is Stacks 0990; neither is in the library.

## References

* [Stacks Project, Tag 09AA](https://stacks.math.columbia.edu/tag/09AA)
* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 04D6](https://stacks.math.columbia.edu/tag/04D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

/-- **Sites 04D6 (h) for the small pro-étale direct image.** The counit of the direct-image
adjunction along `f` is a natural isomorphism if and only if the direct image is fully faithful.

Both directions are formal consequences of the adjunction
`(smallProetaleMorphism B T S f).adj` and hold for any adjoint pair: invertibility of the counit
of an adjunction `L ⊣ R` is equivalent to `R` being fully faithful. In particular this
equivalence is *not* a proof of either of the two clauses of Stacks 09AA that it relates; see
the module docstring. -/
theorem smallProetaleMorphism_counit_isIso_iff_pushforward_fullyFaithful :
    IsIso (smallProetaleMorphism B T S f).adj.counit ↔
      Nonempty (smallProetaleMorphism B T S f).pushforward.FullyFaithful := by
  refine ⟨fun _ => ⟨(smallProetaleMorphism B T S f).adj.fullyFaithfulROfIsIsoCounit⟩, ?_⟩
  rintro ⟨hff⟩
  have := hff.full
  have := hff.faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful
    (h := (smallProetaleMorphism B T S f).adj)

/-- **Clause (2) of Stacks 09AA from Stacks 09BL.** The direct image along `f` on small
pro-étale sheaves of sets is fully faithful as soon as, over the members `U i` of a family
covering the final object of the small pro-étale site of `S`, the counit of the direct-image
adjunction along the base-changed morphism is invertible.

This is the hub
`AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_coversTop_of_counit`, which
is clause (3) under the same hypotheses, followed by
`AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_iff_pushforward_fullyFaithful`.
For a closed immersion and an affine cover of the target the hypothesis `hcounit` is the third
assertion of clause (5) of Stacks 09BL. -/
theorem smallProetaleMorphism_pushforward_fullyFaithful_of_coversTop_of_counit {ι : Type*}
    {U : ι → SmallProetale B S.obj S.property}
    (hU : (SmallProetale.topology B S.obj S.property).CoversTop U)
    (hcounit : ∀ i, IsIso (smallProetaleMorphism B
      ((smallProetaleBaseChange B T S f).obj (U i)).obj.left (U i).obj.left
      (pullback.fst (U i).obj.hom f)).adj.counit) :
    Nonempty (smallProetaleMorphism B T S f).pushforward.FullyFaithful :=
  (smallProetaleMorphism_counit_isIso_iff_pushforward_fullyFaithful B T S f).mp
    (smallProetaleMorphism_counit_isIso_of_coversTop_of_counit B T S f hU hcounit)

/-- **Clause (1) of Stacks 09AA from Stacks 09BL (3).** The inverse image along `f` on small
pro-étale sheaves of sets commutes with limits as soon as it admits a left adjoint.

The inverse image is then a right adjoint, and a right adjoint preserves limits. The intended
left adjoint is the functor `f^{Sh}_!` of Stacks 09BL (3), which for a closed immersion of
affine schemes is constructed from the fully faithful cocontinuous lift of weakly étale affines
of Stacks 09BK. Note that the hypothesis is not implied by invertibility of the counit: a left
adjoint whose right adjoint is fully faithful need not preserve limits. -/
theorem smallProetaleMorphism_inverseImage_preservesLimits_of_leftAdjoint
    {L : Sheaf (SmallProetale.topology B T.obj T.property) (Type (u + 1)) ⥤
      Sheaf (SmallProetale.topology B S.obj S.property) (Type (u + 1))}
    (hshriek : L ⊣ (smallProetaleMorphism B T S f).inverseImage) :
    PreservesLimits (smallProetaleMorphism B T S f).inverseImage :=
  hshriek.rightAdjoint_preservesLimits

/-- **The three clauses of Stacks 09AA from Stacks 09BL.** For a morphism `f : T ⟶ S` of a
chosen big pro-étale site, a family `U` covering the final object of the small pro-étale site of
`S` over whose members the base-changed direct-image counit is invertible, and a left adjoint to
the inverse image along `f`:

1. the inverse image commutes with limits;
2. the direct image is fully faithful;
3. the counit of the direct-image adjunction is a natural isomorphism.

The three conclusions are those of Stacks 09AA, in the source's order. The two hypotheses are
the two conclusions of Stacks 09BL that the source uses, so this is the whole of 09AA except
for 09BL itself and the Zariski reduction producing an affine covering family; see the module
docstring, which is also why no `stacks` attribute is attached. -/
theorem smallProetaleMorphism_preservesLimits_fullyFaithful_counit_isIso {ι : Type*}
    {U : ι → SmallProetale B S.obj S.property}
    (hU : (SmallProetale.topology B S.obj S.property).CoversTop U)
    (hcounit : ∀ i, IsIso (smallProetaleMorphism B
      ((smallProetaleBaseChange B T S f).obj (U i)).obj.left (U i).obj.left
      (pullback.fst (U i).obj.hom f)).adj.counit)
    {L : Sheaf (SmallProetale.topology B T.obj T.property) (Type (u + 1)) ⥤
      Sheaf (SmallProetale.topology B S.obj S.property) (Type (u + 1))}
    (hshriek : L ⊣ (smallProetaleMorphism B T S f).inverseImage) :
    PreservesLimits (smallProetaleMorphism B T S f).inverseImage ∧
      Nonempty (smallProetaleMorphism B T S f).pushforward.FullyFaithful ∧
      IsIso (smallProetaleMorphism B T S f).adj.counit :=
  ⟨smallProetaleMorphism_inverseImage_preservesLimits_of_leftAdjoint B T S f hshriek,
    smallProetaleMorphism_pushforward_fullyFaithful_of_coversTop_of_counit B T S f hU hcounit,
    smallProetaleMorphism_counit_isIso_of_coversTop_of_counit B T S f hU hcounit⟩

end AlgebraicGeometry.ProEtale

end
