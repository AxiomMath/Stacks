module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniJacobianDivisorGlobal
public import StacksFrontier.AlgebraicGeometry.SmoothAtFiber.Locality

/-!
# Smoothness of a zero scheme glued from an open piece and a germ condition off it

`AlgebraicGeometry.smooth_zeroScheme_of_forall_notMem_maximalSqSmul` proves `Z(t)` smooth over a
perfect field from the Jacobian criterion imposed at **every** point of `|Z(t)|`. The
Bertini step of [Stacks, Tag 0FH7] does not have the criterion everywhere: it has

* smoothness of `Z(t)` over the open complement `X ∖ Z` of a closed subscheme, which is where the
  smoothness conclusion of [Stacks, Tag 0FD6] lives, because the linear system of
  [Stacks, Tag 0FD5] generates `ℒ ^⊗ n` only off `Z`; and
* the germ condition at the points of `Z` alone, which is what the general-position opens of that
  proof produce.

This module glues the two. Smoothness at a point of the source is unchanged by passing to an open
subscheme through that point (`InfinitesimalLifting.smoothAt_of_smooth_comp`), and the open piece
of `Z(t)` sitting over `X ∖ Z` *is* the zero scheme of the restricted section
(`Stacks.Divisors.zeroScheme_pullback`, [Stacks, Tag 0B6Y]); so at a point of `|Z(t)|` inside the
open the smoothness hypothesis applies, and at a point outside it the pointwise Jacobian criterion
`AlgebraicGeometry.smoothAt_zeroScheme_of_notMem_maximalSqSmul_of_perfectField` does.

## Main results

* `AlgebraicGeometry.smooth_zeroScheme_of_smooth_comap_of_forall_notMem_maximalSqSmul`: **the zero
  scheme of a section is smooth over a perfect field** when its inverse image in an
  open subscheme is smooth and the section nowhere vanishes to second order off that open, the
  local rings of the ambient scheme being regular.

## Implementation notes

The open subscheme enters as an arbitrary open immersion `u : W ⟶ X` rather than as the inclusion
of an `X.Opens`: the consumer's open is the complement of the support of an ideal sheaf and its
inclusion is already presented as a morphism, and nothing below uses more than that `u` is an open
immersion. The condition "off the open" is accordingly `y ∉ Set.range u`.

The inverse image of `Z(t)` in `W` is taken as a *variable* `J` with an equation
`J = Z(t).comap u`, so that the identification of it with the zero scheme of the restricted
section can be made by `subst` at the call site. That is the device
`AlgebraicGeometry.isRegularLocalRing_stalk_subscheme_of_eq_comap_zeroScheme` uses, and it is used
for the same reason: `Stacks.Divisors.zeroScheme_pullback` is not a `rfl`, and the smoothness
hypothesis is a statement about a morphism out of the subscheme of that ideal sheaf, so rewriting
with the equation inside it would have to transport the morphism. The section is likewise taken
through `Stacks.SheafOfModules.sectionsOfTopOfRingSheaf`, as in
`AlgebraicGeometry.smooth_zeroScheme_of_forall_notMem_maximalSqSmul`, because the pointwise
criterion is stated for a `PresheafOfModules.sections`.

The identification of the open piece uses the cartesian square of
[Stacks, Tag 0B6Y]: `AlgebraicGeometry.Scheme.IdealSheafData.comapIso_inv_subschemeι` turns the
first projection of `W ×_X Z(t)` into the closed immersion of `J`, and
`AlgebraicGeometry.Scheme.Pullback.range_snd` says the second projection has the preimage of
`Set.range u` for its range, which is what makes the case division exhaustive.

No `@[stacks]` attribute is attached: this is a step inside the proofs of [Stacks, Tag 0FD6] and
[Stacks, Tag 0FH7], asserted by neither tag.

## References

* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 0FD5](https://stacks.math.columbia.edu/tag/0FD5)
* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.ImmersionEvaluationSurjective

universe u

namespace AlgebraicGeometry

open Stacks.Divisors

variable {X : Scheme.{u}} (L : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **A zero scheme smooth over an open and nowhere vanishing to second order off it is smooth.**
Let `ℒ` be an invertible module on a scheme `X` all of whose local rings are regular, let `t` be a
global section of `ℒ`, let `k` be a perfect field and let `Z(t)` be locally of finite
type over `k`. Let `u : W ⟶ X` be an open immersion and let `J` be the inverse image of `Z(t)` in
`W`. If `J` is smooth over `k` and the germ of `t` at every point of the support of `Z(t)` outside
the range of `u` avoids `𝔪_y²ℒ_y`, then `Z(t)` is smooth over `k`.

A morphism is smooth exactly when it is smooth at every point of its source
(`InfinitesimalLifting.smooth_of_forall_smoothAt`). At a point `z` of `Z(t)` whose image lies in
the range of `u`, the second projection of `W ×_X Z(t)` hits `z`
(`AlgebraicGeometry.Scheme.Pullback.range_snd`), that projection is an open immersion, and its
composite with the structure morphism of `Z(t)` is the smooth morphism of the hypothesis read
through the cartesian square of [Stacks, Tag 0B6Y], so smoothness at `z` follows from locality of
smoothness on the source (`InfinitesimalLifting.smoothAt_of_smooth_comp`). At a point whose image
lies outside, the germ hypothesis applies and the pointwise Jacobian criterion
`AlgebraicGeometry.smoothAt_zeroScheme_of_notMem_maximalSqSmul_of_perfectField` gives smoothness
there. -/
theorem smooth_zeroScheme_of_smooth_comap_of_forall_notMem_maximalSqSmul {k : Type u} [Field k]
    [PerfectField k] {W : Scheme.{u}} (t : Γ(L, ⊤)) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType ((zeroScheme X L t).subschemeι ≫ f)]
    (u : W ⟶ X) [IsOpenImmersion u]
    {J : W.IdealSheafData} (hJ : J = (zeroScheme X L t).comap u)
    (hsm : Smooth (J.subschemeι ≫ u ≫ f))
    (hreg : ∀ y : X, IsRegularLocalRing (X.presheaf.stalk y))
    (ht : ∀ y : X, y ∈ (zeroScheme X L t).support → y ∉ Set.range u →
      (L.presheaf.Γgerm y).hom t ∉ maximalSqSmul L y) :
    Smooth ((zeroScheme X L t).subschemeι ≫ f) := by
  obtain ⟨s, hs⟩ : ∃ s : L.sections, s.eval (op ⊤) = t :=
    ⟨Stacks.SheafOfModules.sectionsOfTopOfRingSheaf L t,
      Stacks.SheafOfModules.sectionsOfTopOfRingSheaf_eval_top L t⟩
  subst hs
  subst hJ
  refine InfinitesimalLifting.smooth_of_forall_smoothAt _ fun z => ?_
  by_cases hmem : (zeroScheme X L (s.eval (op ⊤))).subschemeι z ∈ Set.range u
  · have hz : z ∈ Set.range (pullback.snd u (zeroScheme X L (s.eval (op ⊤))).subschemeι) := by
      rw [Scheme.Pullback.range_snd]
      exact hmem
    obtain ⟨z', hz'⟩ := hz
    have hsmooth : Smooth (pullback.snd u (zeroScheme X L (s.eval (op ⊤))).subschemeι ≫
        (zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f) := by
      rw [← Category.assoc, ← pullback.condition, Category.assoc,
        ← Scheme.IdealSheafData.comapIso_inv_subschemeι (zeroScheme X L (s.eval (op ⊤))) u,
        Category.assoc]
      exact MorphismProperty.comp_mem (W := @Smooth) _ _ inferInstance hsm
    have hat := InfinitesimalLifting.smoothAt_of_smooth_comp
      (pullback.snd u (zeroScheme X L (s.eval (op ⊤))).subschemeι)
      ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f) hsmooth z'
    rwa [hz'] at hat
  · have := hreg ((zeroScheme X L (s.eval (op ⊤))).subschemeι z)
    refine smoothAt_zeroScheme_of_notMem_maximalSqSmul_of_perfectField L s _ z (ht _ ?_ hmem)
    have hrange : (zeroScheme X L (s.eval (op ⊤))).subschemeι z ∈
        Set.range (zeroScheme X L (s.eval (op ⊤))).subschemeι := Set.mem_range_self z
    rwa [Scheme.IdealSheafData.range_subschemeι] at hrange

end AlgebraicGeometry

end
