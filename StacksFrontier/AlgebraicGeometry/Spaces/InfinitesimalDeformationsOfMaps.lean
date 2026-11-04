module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftActionNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftActionSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftCartesianTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftEtaleCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftTrivialTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivationsIntoDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivationMovedLiftConormal

/-!
# Infinitesimal deformations of maps of algebraic spaces

[Stacks Project, Tag 0617] is the section "Infinitesimal deformations of maps" of the chapter
More on Morphisms of Spaces.  Its introduction is prose: it explains how a derivation moves a
map infinitesimally, using that a sheaf on a thickening `X'` of `X` is a sheaf on `X`
(Equations (05ZL) and (05ZM)).  Its content is the ten numbered results

* Lemma 0618 (two morphisms of first order thickenings with the same reduction and the same
  map of conormal modules differ by an `𝒪_B`-derivation),
* Equation 0619 (`D = d_{Y/B} ∘ θ`),
* Lemma 04D0 (every `θ : a^*Ω_{Y/B} ⟶ 𝒞_{X/X'}` moves `(a, a')` to a unique `(b, b')`),
* Remark 0CK6 (the notation `θ · a'`),
* Lemma 061A and Equation 061B (the sheaf of lifts),
* Lemma 061C (the simply transitive action of `SheafHom(a^*Ω_{Y/B}, 𝒞_{X/X'})`),
* Remarks 061D and 0CK7 (the two special cases), and
* Lemma 0CK8 (compatibility of the action with étale localization).

The section is registered as a covering set: each of those results, once it is formalized
faithfully and unconditionally, carries `stacks 0617` in addition to its own tag, with a comment
naming which result of the section it is.  The registrations of declarations which live in
other modules are made here with `add_to_stacks`, so that those modules are not edited.

## Registered here

* Lemma 0618: `AlgebraicGeometry.Space.exists_derivation_of_conormalMap_eq`, the `𝒪_B`-derivation
  `D : 𝒪_Y ⟶ a_*𝒞_{X/X'}` with `(a')^♯ − (b')^♯ = ι ∘ D ∘ (𝒪_{Y'} → 𝒪_Y)`.

* Equation 0619: `AlgebraicGeometry.Space.derivationDirectImageEquiv`, the bijection
  `θ ↔ D = d_{Y/B} ∘ θ` between `𝒪_X`-linear maps `a^*Ω_{Y/B} ⟶ C` and `𝒪_B`-derivations
  `𝒪_Y ⟶ a_*C`, at an arbitrary target module `C` (the section takes `C = 𝒞_{X/X'}`), and
  `AlgebraicGeometry.Space.derivationDirectImageEquiv_apply`, the equation itself.
* Remark 0CK6: `AlgebraicGeometry.Space.derivationMove_spec`, the action
  `θ · a' = AlgebraicGeometry.Space.derivationMove` and what it means: `(a')^♯` and `(θ · a')^♯`
  differ by the derivation related to `θ` by Equation 0619.
* Lemma 04D0: `AlgebraicGeometry.Space.existsUnique_hom_conormalMap_eq_derivation_eq`, the unique
  morphism of thickenings `(a, b')` over the base with the same map of conormal modules as
  `(a, a')` and with `(a')^♯ − (b')^♯ = ι ∘ D ∘ j^♯`, `D = d_{Y/B} ∘ θ`.
* Equation 061B: `AlgebraicGeometry.Space.conormalLiftSubfunctor`, the rule
  `U' ↦ {a' : U' ⟶ Y' satisfying (1), (2), (3)}` on the spaces-étale site of `X'`, with
  restriction `a' ↦ a'|_{V'}`, for arbitrary thickenings, `a` and `A`.
* Lemma 061C: `AlgebraicGeometry.Space.isSheaf_conormalLiftActingPresheaf` (the acting sheaf
  `SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` read on `X'` through 05ZL),
  `AlgebraicGeometry.Space.conormalLiftSheafAddAction` (its action over each `U'`),
  `AlgebraicGeometry.Space.conormalLiftAction_map` (compatibility with restriction) and
  `AlgebraicGeometry.Space.conormalLiftSheafAddAction_bijective` (simple transitivity).
* Lemma 061A: `AlgebraicGeometry.Space.isSheaf_conormalLiftSubfunctor`, that rule is a sheaf of
  sets.
* Remark 061D: `AlgebraicGeometry.Space.liftSubfunctor_remark_of_eq_top`, the case `Y = Y'`: `A`
  is zero, the sheaf of 061A is `U' ↦ {a' : U' ⟶ Y over B with a'|_U = a|_U}`, and
  `SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` acts on it
  (`AlgebraicGeometry.Space.liftSheafAddActionOfEqTop`).
* Remark 0CK7: `AlgebraicGeometry.Space.liftSubfunctor_remark_of_cartesian`, the case of a base
  thickening `Z ⊂ Z' = B` with `Y = Z ×_{Z'} Y'`: `A` is determined by `a`, the sheaf of 061A is
  `U' ↦ {a' : U' ⟶ Y' over Z' with a'|_U = a|_U}`, and `SheafHom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})`
  acts on it (`AlgebraicGeometry.Space.cartesianLiftSheafAddAction`).
* Lemma 0CK8: `AlgebraicGeometry.Space.derivationMove_comp_of_etale`, for a commutative diagram of
  first order thickenings `(h, h')`, `(a_i, a_i')`, `(f, f')` and a square `X₂' → B₂`, `X₁' → B₁`
  with `X₂ → X₁` and `B₂ → B₁` étale: `(θ₂ · a₂') ≫ f' = h' ≫ (θ₁ · a₁')`, where `θ₂` is
  `a₂^*Ω_{X₂/B₂} = h^*a₁^*Ω_{X₁/B₁} → h^*𝒞_{T₁/T₁'} → 𝒞_{T₂/T₂'}`
  (`AlgebraicGeometry.Space.etaleLocalizedDerivationDatum`).

## References

* [Stacks Project, Tag 0617](https://stacks.math.columbia.edu/tag/0617)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
* [Stacks Project, Tag 061A](https://stacks.math.columbia.edu/tag/061A)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 0CK7](https://stacks.math.columbia.edu/tag/0CK7)
* [Stacks Project, Tag 0CK8](https://stacks.math.columbia.edu/tag/0CK8)
-/

@[expose] public section

add_to_stacks 0617 "Lemma 0618 of the section: two morphisms of first order thickenings over B \
  with a = b and the same map of conormal modules differ by an 𝒪_B-derivation D"
  AlgebraicGeometry.Space.exists_derivation_of_conormalMap_eq

add_to_stacks 0617 "Equation 0619 of the section: the bijection θ ↔ D = d_{Y/B} ∘ θ between \
  maps a^*Ω_{Y/B} ⟶ C and 𝒪_B-derivations 𝒪_Y ⟶ a_*C"
  AlgebraicGeometry.Space.derivationDirectImageEquiv

add_to_stacks 0617 "Equation 0619 of the section: the derivation attached to θ is d_{Y/B} \
  followed by the transpose of θ"
  AlgebraicGeometry.Space.derivationDirectImageEquiv_apply

add_to_stacks 0617 "Lemma 04D0 of the section: θ moves (a, a') to a unique morphism of pairs \
  (a, b') with the same map of conormal modules and D = d_{Y/B} ∘ θ"
  AlgebraicGeometry.Space.existsUnique_hom_conormalMap_eq_derivation_eq

add_to_stacks 0617 "Remark 0CK6 of the section: the action θ · a', whose comorphism differs from \
  that of a' by the derivation related to θ by Equation 0619"
  AlgebraicGeometry.Space.derivationMove_spec

add_to_stacks 0617 "Equation 061B of the section: the rule U' ↦ {a' : U' → Y' such that (1), \
  (2), (3) hold} on (X')_{spaces, étale}, with restriction a' ↦ a'|_{V'}"
  AlgebraicGeometry.Space.conormalLiftSubfunctor

add_to_stacks 0617 "Lemma 061A of the section: the rule of Equation 061B is a sheaf of sets on \
  (X')_{spaces, étale}"
  AlgebraicGeometry.Space.isSheaf_conormalLiftSubfunctor

add_to_stacks 0617 "Lemma 061C of the section: the sheaf SheafHom_{O_X}(a^*Ω_{Y/B}, C_{X/X'}), \
  read on (X')_{spaces, étale} through 05ZL, which acts"
  AlgebraicGeometry.Space.isSheaf_conormalLiftActingPresheaf

add_to_stacks 0617 "Lemma 061C of the section: the action on the sections of the sheaf 061B"
  AlgebraicGeometry.Space.conormalLiftSheafAddAction

add_to_stacks 0617 "Lemma 061C of the section: the action commutes with restriction"
  AlgebraicGeometry.Space.conormalLiftAction_map

add_to_stacks 0617 "Lemma 061C of the section: the action is simply transitive over every U' over \
  which the sheaf 061B has a section"
  AlgebraicGeometry.Space.conormalLiftSheafAddAction_bijective

add_to_stacks 0617 "Remark 061D of the section: for Y = Y' the map A is zero, the sheaf of 061A is \
  U' ↦ {a' : U' → Y over B with a'|_U = a|_U}, and SheafHom_{O_X}(a^*Ω_{Y/B}, C_{X/X'}) acts on it"
  AlgebraicGeometry.Space.liftSubfunctor_remark_of_eq_top

add_to_stacks 0617 "Remark 0CK7 of the section: for a base thickening Z ⊂ Z' and Y = Z ×_{Z'} Y' \
  the map A is determined by a, the sheaf of 061A is U' ↦ {a' : U' → Y' over Z' with \
  a'|_U = a|_U}, and SheafHom_{O_X}(a^*Ω_{Y/Z}, C_{X/X'}) acts on it"
  AlgebraicGeometry.Space.liftSubfunctor_remark_of_cartesian

add_to_stacks 0617 "Lemma 0CK8 of the section: for X₂ → X₁ and B₂ → B₁ étale the action is \
  compatible with étale localization, (θ₂ · a₂') ≫ f' = h' ≫ (θ₁ · a₁')"
  AlgebraicGeometry.Space.derivationMove_comp_of_etale

end
