module

public import StacksFrontier.AlgebraicGeometry.Curves.SheafDerivationDescent

/-!
# Descending a vector field is a condition on stalks

Let `ν : Y ⟶ X` be a morphism of schemes over a field `k` whose comorphism is injective on
sections, and let `D'` be a vector field on `Y`. The condition
`Stacks.Curves.Preserves ν D'` — that `D'` carry `ν^♯ Γ(X, U)` into itself for every open `U` of
`X` — was shown in `Stacks.Curves.preserves_of_forall_mem_exists` to be local on `X`. This file
takes the last step and makes it a condition on *stalks*: it is enough that the germ at every
point `x` of `X` of `D' (ν^♯ s)`, as an element of the stalk `(ν_* 𝒪_Y)_x`, lie in the image of
the local ring `𝒪_{X, x}`.

That is the shape in which the remaining input of Tag 0E68 is available. At a node the image of
`𝒪_{X, x}` in `(ν_* 𝒪_{X^ν})_x` is cut out by the equality of the two branch residues
(`Stacks.Curves.range_algebraMap_integralClosure_eq_equalizer`), and a derivation fixing the two
points above the node carries it into itself
(`Stacks.Curves.mem_range_algebraMap_of_fixes`) — statements about the local ring and its
normalization, not about sections over an open.

## Main definitions

There are no definitions.

## Main results

* `Stacks.Curves.preserves_of_germ_mem_range` — if the germ of `D' (ν^♯ s)` at each point lies
  in the image of the stalk of `𝒪_X`, then `D'` preserves `ν^♯ 𝒪_X`.
* `Stacks.Curves.preserves_normalization_of_germ_mem_range` — for the normalization of a reduced
  scheme the condition is purely ring-theoretic: it is enough that each such germ, read in the
  integral closure of the local ring in its total ring of fractions, come from the local ring.

## Implementation notes

The passage from the stalk to a neighbourhood is the filtered-colimit argument, in two steps.
An element of `𝒪_{X, x}` whose image is the germ of `D' (ν^♯ s)` is itself the germ of a section
`t₀` over some `W ∋ x` (`TopCat.Presheaf.exists_germ_eq`), and the comparison map of stalks
sends that germ to the germ of `ν^♯ t₀` (`TopCat.Presheaf.stalkFunctor_map_germ_apply`); two
sections of `ν_* 𝒪_Y` with the same germ at `x` agree on a neighbourhood
(`TopCat.Presheaf.germ_eq`). On that neighbourhood `ν^♯ t₀` is the required witness, because
restriction commutes with `ν^♯` (`Stacks.Curves.app_restrict`) and with `D'`
(`Stacks.Curves.SheafDerivationOf.onSections_restrict`).

`TopCat.Presheaf.germ_eq` returns the two inclusions as morphisms of the category `X.Opens`
rather than as inequalities. Morphisms there are a subsingleton
(`CategoryTheory.subsingleton_hom`, `X.Opens` being a preorder), so each is replaced by
`CategoryTheory.homOfLE` of its own `le` before the restriction lemmas, which are stated for
`homOfLE`, are applied.

For the normalization the comparison map of stalks *is* the structure map of
`Stacks.NormalizationStalkAmbient.normalizationPushforwardStalkAlgebra`, by definition, and
`Stacks.AlgebraicGeometry.NormalizationQuotient.normalizationStalkAlgEquivIntegralClosureSelf`
— Tag 0C3B(2) for a reduced scheme — carries that stalk to `integralClosure A (Frac A)` over
`A = 𝒪_{X, x}`. Since that comparison is an `A`-algebra isomorphism it matches the two images
elementwise, so no computation is needed beyond `AlgEquiv.commutes`.

## References

* [Stacks Project, Tag 0E66](https://stacks.math.columbia.edu/tag/0E66)
* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.NormalizationQuotient
open scoped AlgebraicGeometry

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {hX : X ⟶ Spec (.of k)}

/-- **Preserving the pulled-back sections is a condition on stalks.** Let `ν : Y ⟶ X` be
injective on sections of the structure sheaves and let `D'` be a vector field on `Y`. If for
every local section `s` of `𝒪_X` and every point `x` of its domain the germ at `x` of
`D' (ν^♯ s)` lies in the image of the stalk `𝒪_{X, x}` under the comparison map
`𝒪_{X, x} ⟶ (ν_* 𝒪_Y)_x`, then `D'` preserves `ν^♯ Γ(X, U)` for every open `U` of `X`, and
hence descends.

This reduces the remaining hypothesis of `Stacks.Curves.existsUnique_descend_iff_preserves` to a
statement about local rings. -/
theorem preserves_of_germ_mem_range {ν : Y ⟶ X} (D' : SheafDerivationOf (ν ≫ hX))
    (hinj : ∀ U : X.Opens, Function.Injective (ν.app U).hom)
    (hst : ∀ (U : X.Opens) (s : Γ(X, U)) (x : X) (hx : x ∈ U),
      ∃ a : X.presheaf.stalk x,
        ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map ν.c) a =
          (ν.base _* Y.presheaf).germ U x hx (D'.onSections ((ν.app U).hom s))) :
    Preserves ν D' := by
  refine preserves_of_forall_mem_exists D' hinj fun U s x hx => ?_
  obtain ⟨a, ha⟩ := hst U s x hx
  obtain ⟨W, hxW, t₀, ht₀⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf a
  rw [← ht₀, TopCat.Presheaf.stalkFunctor_map_germ_apply] at ha
  obtain ⟨V, hxV, iW, iU, heq⟩ := (ν.base _* Y.presheaf).germ_eq x hxW hx _ _ ha
  have hiW : iW = homOfLE iW.le := Subsingleton.elim _ _
  have hiU : iU = homOfLE iU.le := Subsingleton.elim _ _
  rw [hiW, hiU] at heq
  have hpreW : ν ⁻¹ᵁ V ≤ ν ⁻¹ᵁ W := ((Opens.map ν.base).map (homOfLE iW.le)).le
  have hpreU : ν ⁻¹ᵁ V ≤ ν ⁻¹ᵁ U := ((Opens.map ν.base).map (homOfLE iU.le)).le
  refine ⟨V, iU.le, hxV, (X.presheaf.map (homOfLE iW.le).op).hom t₀, ?_⟩
  have hL : (ν.app V).hom ((X.presheaf.map (homOfLE iW.le).op).hom t₀) =
      (Y.presheaf.map (homOfLE hpreW).op).hom ((ν.app W).hom t₀) :=
    app_restrict ν iW.le hpreW t₀
  have hR : (Y.presheaf.map (homOfLE hpreU).op).hom (D'.onSections ((ν.app U).hom s)) =
      D'.onSections ((ν.app V).hom ((X.presheaf.map (homOfLE iU.le).op).hom s)) := by
    rw [← SheafDerivationOf.onSections_restrict D' hpreU ((ν.app U).hom s),
      app_restrict ν iU.le hpreU s]
  rw [hL, ← hR]
  exact heq

/-- **Descending along a normalization is a ring-theoretic condition on the local rings.** Let
`X` be a reduced scheme over `k` and `ν : X^ν ⟶ X` its normalization. A vector field `D'` on
`X^ν` preserves `ν^♯ 𝒪_X`, and hence descends, as soon as for every local section `s` of `𝒪_X`
and every point `x` of its domain the germ at `x` of `D' (ν^♯ s)` — an element of
`(ν_* 𝒪_{X^ν})_x`, read through Tag 0C3B(2) as an element of the integral closure of
`𝒪_{X, x}` in its total ring of fractions — lies in the image of `𝒪_{X, x}`.

The injectivity hypothesis is discharged by
`Stacks.Curves.app_normalization_injective`. The remaining condition is exactly what
`Stacks.Curves.mem_range_algebraMap_of_fixes` establishes at a node, once a vector field on
`X^ν` is known to induce a derivation of that integral closure fixing the two branch points. -/
theorem preserves_normalization_of_germ_mem_range [IsReduced X]
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (D' : SheafDerivationOf (Scheme.normalization X hfin ≫ hX))
    (hgerm : ∀ (U : X.Opens) (s : Γ(X, U)) (x : X) (hx : x ∈ U),
      normalizationStalkAlgEquivIntegralClosureSelf X hfin x
          (((Scheme.normalization X hfin).base _*
            (Scheme.normalizationScheme X hfin).presheaf).germ U x hx
            (D'.onSections (((Scheme.normalization X hfin).app U).hom s))) ∈
        Set.range (algebraMap (X.presheaf.stalk x)
          ↥(integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))))) :
    Preserves (Scheme.normalization X hfin) D' := by
  refine preserves_of_germ_mem_range D' (app_normalization_injective X hfin) fun U s x hx => ?_
  let := NormalizationStalkAmbient.normalizationPushforwardStalkAlgebra X hfin x
  obtain ⟨a, ha⟩ := hgerm U s x hx
  exact ⟨a, (normalizationStalkAlgEquivIntegralClosureSelf X hfin x).injective
    (((normalizationStalkAlgEquivIntegralClosureSelf X hfin x).commutes a).trans ha)⟩

end Stacks.Curves

end
