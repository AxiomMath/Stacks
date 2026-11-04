module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationThickenedBaseGlobalLift
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobalBijective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derivations are the lifts over a thickened base, and they compose

Let `i : X ⟶ X'` be a first-order thickening, let `j : Y ⟶ Y'` and `k : Z ⟶ Z'` be immersions,
let `h : Y ⟶ Z`, `h' : Y' ⟶ Z'` and `g' : X' ⟶ Z'`, and suppose the square of `j` over `k` is
cartesian. [Stacks Project, Tag 0CK2] then makes `Hom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})` act simply
transitively on the lifts of `a : X ⟶ Y` over `Z'`, with **no conormal datum in the statement**:
the datum is determined by `a` (`Stacks.Thickenings.eq_of_isBaseCompatibleConormalMap`) and any
lift produces it (`Stacks.Thickenings.isBaseCompatibleConormalMap_of_globalLift`).

This file reads `Stacks.Thickenings.derivationActionGlobalEquiv` in that situation. The two
conditions of [Stacks Project, Tag 04FG] that the general bijection carries are then *both*
discharged — the conormal-sheaf condition because the two lifts are over the base, and the
differentials are taken relative to `Z` rather than `Z'` by
`Stacks.Thickenings.pullbackCotangentSheafIsoOfBase` — so the bijection becomes

`Hom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'}) ≃ { b' : X' ⟶ Y' // b' ≫ h' = g' ∧ i ≫ b' = a ≫ j }`,

the derivations and the plain lifts of `a` over `Z'`.

In the **self-map** case — `Y' = X'`, `j = i`, `a = 𝟙_X` and `a' = 𝟙_{X'}` — the lifts are
self-maps of `X'` over the base fixing `X`, and they compose: the bijection carries addition of
derivations to composition of self-maps, by
`Stacks.Thickenings.derivationActionGlobal_comp_derivationActionGlobal`. That is the statement
that makes the identification of [Stacks Project, Tag 04FJ] an isomorphism of groups rather than
a bijection of sets.

## Main definitions

* `Stacks.Thickenings.homPrecompIsoEquiv`: precomposition with an isomorphism of the source.
* `Stacks.Thickenings.derivationActionGlobalEquivOfBase`: **the derivations are the lifts over
  the base.**

## Main results

* `Stacks.Thickenings.derivationActionGlobalEquivOfBase_comp`: **in the self-map case the
  bijection carries addition to composition.**

## Implementation notes

The conormal-sheaf condition is discharged in the backward direction of a
`Equiv.subtypeEquivRight`: a lift over the base produces a base-compatible conormal datum, so
the data of `a'` and of `b'` agree, and that equality *is* the condition. In the forward
direction the condition is simply forgotten. The commuting square itself is kept as the
existential of the general statement and re-supplied, which costs nothing since it is a
proposition.

The differentials relative to `Z` and relative to `Z'` are compared by precomposition rather
than by transporting the whole bijection, so the comparison isomorphism stays outside the terms
the kernel unfolds — the device the restricted statements of this directory use as well.

Self-map multiplicativity is read off the forward map directly: the three constituent
equivalences leave the underlying morphism alone, so the composite's value is
`Stacks.Thickenings.derivationActionGlobal` of the precomposed datum, precomposition is additive,
and the composition law is the one already proved.

## References

* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Immersion

universe u

namespace Stacks.Thickenings

/-- **Precomposition with an isomorphism of the source**, as a bijection of hom sets. -/
def homPrecompIsoEquiv {W : Scheme.{u}} {P Q N : W.Modules} (e : P ≅ Q) :
    (Q ⟶ N) ≃ (P ⟶ N) where
  toFun g := e.hom ≫ g
  invFun g := e.inv ≫ g
  left_inv g := Iso.inv_hom_id_assoc e g
  right_inv g := Iso.hom_inv_id_assoc e g

section Base

variable {X X' Y Y' Z Z' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {k : Z ⟶ Z'}
  [IsClosedImmersion i] [IsImmersion j] [IsImmersion k]
  {h : Y ⟶ Z} {h' : Y' ⟶ Z'} {g' : X' ⟶ Z'} {a : X ⟶ Y} {a' : X' ⟶ Y'}

/-- **The derivations are the lifts over a thickened base.** For a first-order thickening
`i : X ⟶ X'`, a cartesian square identifying the special fibre of `j : Y ⟶ Y'` over `k`, and a
lift `a'` of `a` over `Z'`, the group `Hom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})` is in bijection with the
morphisms `X' ⟶ Y'` over `Z'` restricting to `a` along `i`, by `θ ↦ θ ⬝ a'`.

Neither condition of [Stacks Project, Tag 04FG] survives in the statement. The conormal-sheaf
condition holds for any two lifts over the base, because each produces a base-compatible datum
(`Stacks.Thickenings.isBaseCompatibleConormalMap_of_globalLift`) and such a datum is unique
(`Stacks.Thickenings.eq_of_isBaseCompatibleConormalMap`); and the differentials are taken
relative to `Z`, as [Stacks Project, Tag 0CK2] states them, by precomposition with
`Stacks.Thickenings.pullbackCotangentSheafIsoOfBase`. -/
@[sga "3 III 4.8" "partial"]
def derivationActionGlobalEquivOfBase (hsq : i.ker ^ 2 = ⊥) (sq : IsPullback j h h' k)
    (ci : i ≫ g' = (a ≫ h) ≫ k) (comm_a : i ≫ a' = a ≫ j) (ha : a' ≫ h' = g') :
    (Stacks.Smooth.pullbackCotangentSheaf h a ⟶ conormalModules i) ≃
      { b' : X' ⟶ Y' // b' ≫ h' = g' ∧ i ≫ b' = a ≫ j } :=
  (homPrecompIsoEquiv (pullbackCotangentSheafIsoOfBase sq a)).trans
    ((derivationActionGlobalEquiv hsq h' comm_a).trans
      (Equiv.subtypeEquivRight fun _ =>
        ⟨fun hb => ⟨hb.choose_spec.1.trans ha, hb.choose⟩,
          fun hb => ⟨hb.2, hb.1.trans ha.symm,
            eq_of_isBaseCompatibleConormalMap sq ci
              (isBaseCompatibleConormalMap_of_globalLift sq ci ha comm_a)
              (isBaseCompatibleConormalMap_of_globalLift sq ci hb.1 hb.2)⟩⟩))

/-- The bijection is the modified-lift construction, read through the comparison of the
differentials relative to `Z` and relative to `Z'`. -/
theorem derivationActionGlobalEquivOfBase_apply (hsq : i.ker ^ 2 = ⊥)
    (sq : IsPullback j h h' k) (ci : i ≫ g' = (a ≫ h) ≫ k) (comm_a : i ≫ a' = a ≫ j)
    (ha : a' ≫ h' = g')
    (θ : Stacks.Smooth.pullbackCotangentSheaf h a ⟶ conormalModules i) :
    (derivationActionGlobalEquivOfBase hsq sq ci comm_a ha θ).1
      = derivationActionGlobal hsq ((pullbackCotangentSheafIsoOfBase sq a).hom ≫ θ) comm_a :=
  rfl

end Base

section SelfMaps

variable {X X' Z Z' : Scheme.{u}} {i : X ⟶ X'} {k : Z ⟶ Z'}
  [IsClosedImmersion i] [IsImmersion k] {h : X ⟶ Z} {pX' : X' ⟶ Z'}

/-- **In the self-map case the bijection carries addition of derivations to composition of
self-maps.**

Taking `Y' = X'`, `j = i`, `a = 𝟙_X` and `a' = 𝟙_{X'}` in
`Stacks.Thickenings.derivationActionGlobalEquivOfBase`, the lifts are the self-maps of `X'` over
the base restricting to the identity of `X`, and `θ ↦ θ ⬝ 𝟙` takes `θ + η` to the composite of
the two self-maps.

This is what makes the simply transitive action of [Stacks Project, Tag 04FJ] on those self-maps
an isomorphism of groups: it is
`Stacks.Thickenings.derivationActionGlobal_comp_derivationActionGlobal` read through the
bijection, the three constituent equivalences leaving the underlying morphism alone and
precomposition with the comparison of differentials being additive. -/
theorem derivationActionGlobalEquivOfBase_comp (hsq : i.ker ^ 2 = ⊥)
    (sq : IsPullback i h pX' k) (ci : i ≫ pX' = ((𝟙 X : X ⟶ X) ≫ h) ≫ k)
    (comm : i ≫ (𝟙 X' : X' ⟶ X') = (𝟙 X : X ⟶ X) ≫ i)
    (ha : (𝟙 X' : X' ⟶ X') ≫ pX' = pX')
    (θ η : Stacks.Smooth.pullbackCotangentSheaf h (𝟙 X) ⟶ conormalModules i) :
    (derivationActionGlobalEquivOfBase hsq sq ci comm ha (θ + η)).1
      = (derivationActionGlobalEquivOfBase hsq sq ci comm ha θ).1
          ≫ (derivationActionGlobalEquivOfBase hsq sq ci comm ha η).1 := by
  rw [derivationActionGlobalEquivOfBase_apply, derivationActionGlobalEquivOfBase_apply,
    derivationActionGlobalEquivOfBase_apply, Preadditive.comp_add]
  exact (derivationActionGlobal_comp_derivationActionGlobal hsq comm _ _).symm

end SelfMaps

end Stacks.Thickenings

end
