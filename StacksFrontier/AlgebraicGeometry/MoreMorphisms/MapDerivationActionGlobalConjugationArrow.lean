module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobalConjugation

/-!
# The derivation by which conjugating a lift displaces it

Let `kk : Z ⟶ Z'` be an immersion of a base, let `i : X ⟶ X'` and `j : Y ⟶ Y'` be first-order
thickenings with `j` cartesian over `kk`, and let `a' : X' ⟶ Y'` be a lift of `a : X ⟶ Y` over
`Z'`. [Stacks Project, Tag 0CK2] presents the lifts of `a` over `Z'` as the group
`Hom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})`, by `θ ↦ θ ⬝ a'`; that is
`Stacks.Thickenings.derivationActionGlobalEquivOfBase`.

A second, independent way to move a lift is to **conjugate** it: precompose by a self-map of
`X'` over `Z'` fixing `X` and postcompose by a self-map of `Y'` over `Z'` fixing `Y`. Those
self-maps are again presented by derivations — `u ⬝ 𝟙_{X'}` and `v ⬝ 𝟙_{Y'}` — and that
presentation carries addition to composition
(`Stacks.Thickenings.derivationActionGlobal_comp_derivationActionGlobal`), so the pairs `(u, v)`
form the conjugating group.

**This file builds the map that compares the two.** Conjugating `a'` by `(u, v)` is again a lift
of `a` over `Z'`, so exactly one derivation `θ` carries `a'` there; that `θ` is
`Stacks.Thickenings.conjugationDerivation`. It is the arrow `b` of the six-term exact sequence
of [Stacks Project, Tag 0E3V], at the level of thickenings and with no deformation category in
sight: in the source's notation the conjugated lift is `β⁻¹ ∘ f' ∘ α` and `b(α, β)` is the
derivation by which it differs from `f'`.

## Main definitions

* `Stacks.Thickenings.conjugateBaseLift`: the conjugate `(u ⬝ 𝟙_{X'}) ≫ a' ≫ (v ⬝ 𝟙_{Y'})` of a
  lift by a pair of modified self-maps.
* `Stacks.Thickenings.conjugationDerivation`: **the arrow `b`** — the unique derivation carrying
  `a'` to its conjugate.

## Main results

* `Stacks.Thickenings.comm_conjugateBaseLift` and
  `Stacks.Thickenings.conjugateBaseLift_comp`: the conjugate is again a lift of `a` over `Z'`.
  These are what make `Stacks.Thickenings.conjugationDerivation` definable at all.
* `Stacks.Thickenings.derivationActionGlobalEquivOfBase_conjugationDerivation`: **the
  characterising property of `b`**, `(b (u, v)) ⬝ a' = (u ⬝ 𝟙) ≫ a' ≫ (v ⬝ 𝟙)`. This is the
  hypothesis `hb` of `Deformation.map_add_of_simplyTransitive`,
  `Deformation.map_smul_of_simplyTransitive` and
  `Deformation.exact_triple_of_simplyTransitive`.
* `Stacks.Thickenings.eq_conjugationDerivation`: no other derivation has that property.
* `Stacks.Thickenings.conjugationDerivation_add`: **`b` is additive**, the two conjugating
  derivations adding independently.
* `Stacks.Thickenings.conjugationDerivation_zero`: `b` kills the trivial pair.

## Implementation notes

The conjugating group is taken to be the pairs of **derivations** `(u, v)` rather than the pairs
of self-maps they present. Nothing is lost — `θ ↦ θ ⬝ 𝟙` is a bijection onto the self-maps over
the base, by `Stacks.Thickenings.derivationActionGlobalEquivOfBase` in its self-map case — and
two things are gained. The group structure is the one on a group of morphisms of sheaves of
modules, so additivity of `b` is an equation between derivations rather than between self-maps;
and the two commutation lemmas
`Stacks.Thickenings.derivationActionGlobal_comp_targetSelfMap` and
`Stacks.Thickenings.sourceSelfMap_comp_derivationActionGlobal` are already stated for self-maps
of exactly this form, so they apply with no bridge.

The two derivations `u` and `v` are taken relative to the **thickened** base `Z'`, which is the
form those two commutation lemmas consume, while the moving derivation `θ` is relative to `Z`,
which is the form [Stacks Project, Tag 0CK2] and
`Stacks.Thickenings.derivationActionGlobalEquivOfBase` are stated at. The asymmetry is the
source's: a self-map of `X'` over `Z'` is a lift of `𝟙_X` along `i` over the *thickened* base,
and the comparison `Stacks.Thickenings.pullbackCotangentSheafIsoOfBase` that turns `Ω_{Y/Z'}`
into `Ω_{Y/Z}` is available only where the square is cartesian over `kk`, which is assumed of
`j` and not of `i`.

Additivity is proved directly rather than through `Deformation.map_add_of_simplyTransitive`.
That abstract lemma wants the conjugation as an `AddAction` of the pairs on the whole set of
lifts; here only the orbit of `a'` is needed, and supplying the action on every lift would mean
proving `0 ⬝ 𝟙 = 𝟙` and the action law at an arbitrary lift, neither of which is used. The
direct route is the uniqueness statement
`Stacks.Thickenings.eq_conjugationDerivation` applied to the sum, with the two commutation
lemmas moving each conjugation past the other translation.

## References

* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-! ### The zero derivation does not move the lift -/

section Zero

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y} {q : Y' ⟶ S}
  [IsClosedImmersion i]

/-- **The perturbation attached to the zero derivation is zero.** This is
`Stacks.Thickenings.derivationSection_add_hom` at `θ = η = 0`; the companion
`Stacks.Thickenings.derivationSection_zero` says instead that the perturbation kills the zero
*section*. -/
theorem derivationSection_zero_hom (hsq : i.ker ^ 2 = ⊥) (W : Y'.Opens) (V : X'.Opens)
    (hU : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W)) (g : Γ(Y', W)) :
    derivationSection hsq
        (0 : Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i) W V hU g = 0 := by
  have h := derivationSection_add_hom (hsq := hsq)
    (0 : Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i) 0 W V hU g
  rw [zero_add] at h
  exact left_eq_add.mp h

/-- **The zero derivation does not move the lift**, `0 ⬝ a' = a'`. This is the `act 0 = id` law
of the simply transitive action of [Stacks Project, Tag 04FJ], at the level of the lift itself
rather than of the torsor bijection.

Taken at `Y' = X'`, `j = i`, `a = 𝟙_X` and `a' = 𝟙_{X'}` it says that the modified self-map
attached to the zero derivation is the identity, which is what relates the parametrisation
`u ↦ u ⬝ 𝟙` of the conjugating self-maps used by
`Stacks.Thickenings.conjugateBaseLift` to one that inverts the source factor, as
`Deformation.Examples.globalLiftsOverBaseConj` does. -/
theorem derivationActionGlobal_zero (hsq : i.ker ^ 2 = ⊥) (a' : X' ⟶ Y')
    (comm_a : i ≫ a' = a ≫ j) :
    derivationActionGlobal hsq
        (0 : Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i) comm_a = a' :=
  (eq_derivationActionGlobal hsq 0 comm_a comm_a fun W V hA g => by
    rw [derivationSection_zero_hom hsq W V (preimage_le_of_comm comm_a hA) g, add_zero]).symm

end Zero

variable {X X' Y Y' Z Z' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {kk : Z ⟶ Z'}
  [IsClosedImmersion i] [IsClosedImmersion j] [IsImmersion kk]
  {h : Y ⟶ Z} {h' : Y' ⟶ Z'} {g' : X' ⟶ Z'} {a : X ⟶ Y}

/-! ### The conjugate of a lift -/

section Conjugate

variable (hsq : i.ker ^ 2 = ⊥) (hsqj : j.ker ^ 2 = ⊥) (a' : X' ⟶ Y')
  (u : Stacks.Smooth.pullbackCotangentSheaf (i ≫ g') (𝟙 X) ⟶ conormalModules i)
  (v : Stacks.Smooth.pullbackCotangentSheaf (j ≫ h') (𝟙 Y) ⟶ conormalModules j)
  (comm_i : i ≫ (𝟙 X' : X' ⟶ X') = (𝟙 X : X ⟶ X) ≫ i)
  (comm_j : j ≫ (𝟙 Y' : Y' ⟶ Y') = (𝟙 Y : Y ⟶ Y) ≫ j)

/-- **The conjugate of a lift by a pair of modified self-maps**,
`(u ⬝ 𝟙_{X'}) ≫ a' ≫ (v ⬝ 𝟙_{Y'})`. In the notation of [Stacks Project, Tag 0E3V] this is
`β⁻¹ ∘ f' ∘ α` for the pair `(α, β)` of infinitesimal automorphisms of the two endpoints. -/
def conjugateBaseLift : X' ⟶ Y' :=
  derivationActionGlobal hsq u comm_i ≫ a' ≫ derivationActionGlobal hsqj v comm_j

/-- A modified self-map of a first-order thickening restricts to the identity on the closed
subscheme, `i ≫ (u ⬝ 𝟙_{X'}) = i`. This is
`Stacks.Thickenings.comm_derivationActionGlobal` in the self-map case, with the identity of `X`
cancelled. -/
theorem comp_derivationActionGlobal_self :
    i ≫ derivationActionGlobal hsq u comm_i = i := by
  rw [comm_derivationActionGlobal hsq u comm_i, Category.id_comp]

/-- A modified self-map of a first-order thickening is a morphism over the base,
`(u ⬝ 𝟙_{X'}) ≫ g' = g'`. This is `Stacks.Thickenings.comp_derivationActionGlobal` in the
self-map case. -/
theorem derivationActionGlobal_self_comp_base :
    derivationActionGlobal hsq u comm_i ≫ g' = g' :=
  comp_derivationActionGlobal hsq u comm_i (Category.id_comp g')

/-- Restricting `a' ≫ (v ⬝ 𝟙_{Y'})` along `i` gives the same as restricting `a'`. -/
private theorem comp_comp_derivationActionGlobal_self {i : X ⟶ X'} (comm_a : i ≫ a' = a ≫ j) :
    i ≫ (a' ≫ derivationActionGlobal hsqj v comm_j) = a ≫ j := by
  rw [← Category.assoc, comm_a, Category.assoc, comp_derivationActionGlobal_self hsqj v comm_j]

/-- **The conjugate of a lift of `a` is again a lift of `a`.** Both modified self-maps restrict
to the identity on the closed subscheme, so the restriction of the conjugate along `i` is the
restriction of the lift. -/
theorem comm_conjugateBaseLift (comm_a : i ≫ a' = a ≫ j) :
    i ≫ conjugateBaseLift hsq hsqj a' u v comm_i comm_j = a ≫ j := by
  rw [conjugateBaseLift, ← Category.assoc, comp_derivationActionGlobal_self hsq u comm_i,
    comp_comp_derivationActionGlobal_self hsqj a' v comm_j comm_a]

/-- **The conjugate of a lift over the base is again over the base.** Both modified self-maps
are morphisms over `Z'`. -/
theorem conjugateBaseLift_comp (ha : a' ≫ h' = g') :
    conjugateBaseLift hsq hsqj a' u v comm_i comm_j ≫ h' = g' := by
  rw [conjugateBaseLift, Category.assoc, Category.assoc,
    derivationActionGlobal_self_comp_base hsqj v comm_j, ha,
    derivationActionGlobal_self_comp_base hsq u comm_i]

end Conjugate

omit [IsClosedImmersion j] in
/-- **The modified lift depends on the base lift only through the morphism.** The second
argument of `Stacks.Thickenings.derivationActionGlobal` is a proof that the base lift is a lift,
so two base lifts that are equal as morphisms give the same modified lift whatever proofs are
supplied. This is what lets the base point of the torsor of [Stacks Project, Tag 0CK2] be moved
along an equation between morphisms. -/
theorem derivationActionGlobal_congr_base {b' c' : X' ⟶ Y'} (hsq : i.ker ^ 2 = ⊥)
    (θ : Stacks.Smooth.pullbackCotangentSheaf (j ≫ h') a ⟶ conormalModules i)
    (comm_b : i ≫ b' = a ≫ j) (comm_c : i ≫ c' = a ≫ j) (hbc : b' = c') :
    derivationActionGlobal (a' := b') hsq θ comm_b =
      derivationActionGlobal (a' := c') hsq θ comm_c := by
  subst hbc
  rfl

/-! ### The arrow `b`: the derivation by which conjugation displaces the lift -/

section Arrow

variable (hsq : i.ker ^ 2 = ⊥) (hsqj : j.ker ^ 2 = ⊥) (sq : IsPullback j h h' kk)
  (ci : i ≫ g' = (a ≫ h) ≫ kk) (a' : X' ⟶ Y') (comm_a : i ≫ a' = a ≫ j) (ha : a' ≫ h' = g')
  (u : Stacks.Smooth.pullbackCotangentSheaf (i ≫ g') (𝟙 X) ⟶ conormalModules i)
  (v : Stacks.Smooth.pullbackCotangentSheaf (j ≫ h') (𝟙 Y) ⟶ conormalModules j)
  (comm_i : i ≫ (𝟙 X' : X' ⟶ X') = (𝟙 X : X ⟶ X) ≫ i)
  (comm_j : j ≫ (𝟙 Y' : Y' ⟶ Y') = (𝟙 Y : Y ⟶ Y) ≫ j)

/-- **The arrow `b` of [Stacks Project, Tag 0E3V], at the level of thickenings.** The conjugate
of the lift `a'` by the pair `(u, v)` of modified self-maps is again a lift of `a` over `Z'`, and
[Stacks Project, Tag 0CK2] makes the derivations act simply transitively on those lifts, so
exactly one derivation carries `a'` to its conjugate. This is that derivation.

In the source's notation: a pair of infinitesimal automorphisms of the two endpoint deformations
differs from compatibility with `f` by a derivation, and `b` is that difference. -/
def conjugationDerivation : Stacks.Smooth.pullbackCotangentSheaf h a ⟶ conormalModules i :=
  (derivationActionGlobalEquivOfBase hsq sq ci comm_a ha).symm
    ⟨conjugateBaseLift hsq hsqj a' u v comm_i comm_j,
      conjugateBaseLift_comp hsq hsqj a' u v comm_i comm_j ha,
      comm_conjugateBaseLift hsq hsqj a' u v comm_i comm_j comm_a⟩

/-- **The characterising property of the arrow `b`**: translating `a'` by `b (u, v)` carries it
exactly where conjugating it by `(u, v)` carries it.

This is the hypothesis `hb` of `Deformation.exact_triple_of_simplyTransitive`,
`Deformation.map_add_of_simplyTransitive` and
`Deformation.map_smul_of_simplyTransitive`, read through the torsor bijection of
[Stacks Project, Tag 0CK2]. -/
theorem derivationActionGlobalEquivOfBase_conjugationDerivation :
    (derivationActionGlobalEquivOfBase hsq sq ci comm_a ha
        (conjugationDerivation hsq hsqj sq ci a' comm_a ha u v comm_i comm_j)).1 =
      conjugateBaseLift hsq hsqj a' u v comm_i comm_j :=
  congrArg Subtype.val
    (Equiv.apply_symm_apply (derivationActionGlobalEquivOfBase hsq sq ci comm_a ha) _)

/-- **The characterising property of `b`, with the torsor bijection unfolded** to the
modified-lift construction of [Stacks Project, Tag 0CK1]:
`(b (u, v)) ⬝ a' = (u ⬝ 𝟙_{X'}) ≫ a' ≫ (v ⬝ 𝟙_{Y'})`, the moving derivation being read through
the comparison `Stacks.Thickenings.pullbackCotangentSheafIsoOfBase` of the differentials
relative to `Z` and relative to `Z'`. -/
theorem derivationActionGlobal_conjugationDerivation :
    derivationActionGlobal hsq ((pullbackCotangentSheafIsoOfBase sq a).hom ≫
        conjugationDerivation hsq hsqj sq ci a' comm_a ha u v comm_i comm_j) comm_a =
      derivationActionGlobal hsq u comm_i ≫ a' ≫ derivationActionGlobal hsqj v comm_j :=
  (derivationActionGlobalEquivOfBase_apply hsq sq ci comm_a ha _).symm.trans
    (derivationActionGlobalEquivOfBase_conjugationDerivation hsq hsqj sq ci a' comm_a ha u v
      comm_i comm_j)

/-- **No other derivation displaces the lift the way conjugation does.** Simple transitivity of
the action of [Stacks Project, Tag 0CK2] pins `b (u, v)`, so a derivation carrying `a'` to the
conjugate of `a'` by `(u, v)` is `b (u, v)`. -/
theorem eq_conjugationDerivation
    (θ : Stacks.Smooth.pullbackCotangentSheaf h a ⟶ conormalModules i)
    (hθ : (derivationActionGlobalEquivOfBase hsq sq ci comm_a ha θ).1 =
      conjugateBaseLift hsq hsqj a' u v comm_i comm_j) :
    θ = conjugationDerivation hsq hsqj sq ci a' comm_a ha u v comm_i comm_j := by
  refine (derivationActionGlobalEquivOfBase hsq sq ci comm_a ha).injective (Subtype.ext ?_)
  rw [hθ, derivationActionGlobalEquivOfBase_conjugationDerivation]

/-! ### Additivity of the arrow `b` -/

/-- **The arrow `b` is additive.** Conjugating by the sum of two pairs of self-map derivations
displaces the lift by the sum of the two derivations.

Both perturbations are of order `ε` on a base where `ε² = 0`, so they are independent
operations; concretely, the conjugating self-maps compose when their derivations add
(`Stacks.Thickenings.derivationActionGlobal_comp_derivationActionGlobal`), the translations
compose when their derivations add
(`Stacks.Thickenings.derivationActionGlobal_derivationActionGlobal`), and conjugation commutes
with translation on each side
(`Stacks.Thickenings.sourceSelfMap_comp_derivationActionGlobal` and
`Stacks.Thickenings.derivationActionGlobal_comp_targetSelfMap`). Uniqueness of the displacing
derivation then forces the sum. -/
theorem conjugationDerivation_add
    (u₂ : Stacks.Smooth.pullbackCotangentSheaf (i ≫ g') (𝟙 X) ⟶ conormalModules i)
    (v₂ : Stacks.Smooth.pullbackCotangentSheaf (j ≫ h') (𝟙 Y) ⟶ conormalModules j) :
    conjugationDerivation hsq hsqj sq ci a' comm_a ha (u + u₂) (v + v₂) comm_i comm_j =
      conjugationDerivation hsq hsqj sq ci a' comm_a ha u v comm_i comm_j +
        conjugationDerivation hsq hsqj sq ci a' comm_a ha u₂ v₂ comm_i comm_j := by
  -- the two conjugated lifts, and the proofs that the second one is a lift over the base
  have hD := comp_comp_derivationActionGlobal_self hsqj a' v₂ comm_j comm_a
  have hC : i ≫ (derivationActionGlobal hsq u₂ comm_i ≫
      a' ≫ derivationActionGlobal hsqj v₂ comm_j) = a ≫ j :=
    comm_conjugateBaseLift hsq hsqj a' u₂ v₂ comm_i comm_j comm_a
  refine (eq_conjugationDerivation hsq hsqj sq ci a' comm_a ha (u + u₂) (v + v₂) comm_i comm_j
    _ ?_).symm
  rw [derivationActionGlobalEquivOfBase_apply, Preadditive.comp_add]
  change derivationActionGlobal hsq
      (((pullbackCotangentSheafIsoOfBase sq a).hom ≫
          conjugationDerivation hsq hsqj sq ci a' comm_a ha u v comm_i comm_j) +
        ((pullbackCotangentSheafIsoOfBase sq a).hom ≫
          conjugationDerivation hsq hsqj sq ci a' comm_a ha u₂ v₂ comm_i comm_j)) comm_a =
    derivationActionGlobal hsq (u + u₂) comm_i ≫
      a' ≫ derivationActionGlobal hsqj (v + v₂) comm_j
  rw [← derivationActionGlobal_derivationActionGlobal hsq _ _ comm_a,
    derivationActionGlobal_congr_base hsq _ (comm_derivationActionGlobal hsq _ comm_a) hC
      (derivationActionGlobal_conjugationDerivation hsq hsqj sq ci a' comm_a ha u₂ v₂
        comm_i comm_j),
    ← sourceSelfMap_comp_derivationActionGlobal hsq _ u₂ hD comm_i hC,
    ← derivationActionGlobal_comp_targetSelfMap hsq hsqj _ v₂ comm_a comm_j hD,
    derivationActionGlobal_conjugationDerivation hsq hsqj sq ci a' comm_a ha u v comm_i comm_j,
    add_comm u u₂, ← derivationActionGlobal_comp_derivationActionGlobal hsq comm_i u₂ u,
    ← derivationActionGlobal_comp_derivationActionGlobal hsqj comm_j v v₂]
  simp only [Category.assoc]

/-- **The arrow `b` kills the trivial pair.** Immediate from additivity, the target being a
group. -/
theorem conjugationDerivation_zero :
    conjugationDerivation hsq hsqj sq ci a' comm_a ha 0 0 comm_i comm_j = 0 := by
  have h := conjugationDerivation_add hsq hsqj sq ci a' comm_a ha 0 0 comm_i comm_j 0 0
  rw [zero_add, zero_add] at h
  exact left_eq_add.mp h

end Arrow

end Stacks.Thickenings

end
