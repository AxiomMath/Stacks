module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomMapLeftConjugate

/-!
# Changing the adjunction an inverse adjoint transpose is taken along

Let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be adjunctions and `α : L₂ ⟶ L₁` a comparison of their
left adjoints. A morphism `g : X ⟶ R₁.obj Y` has an inverse adjoint transpose along `adj₁`, a
morphism `L₁.obj X ⟶ Y`; it has none along `adj₂`, whose transposes come out of `L₂.obj X`. What
it has along `adj₂` is a transpose of `g` followed by the conjugate of `α`, and this file records
that the two transposes differ by `α` and by nothing else:

`(adj₂.homEquiv X Y).symm (g ≫ (conjugateEquiv adj₁ adj₂ α).app Y) = α.app X ≫
  (adj₁.homEquiv X Y).symm g`.

This is the step that a transpose has to be put through whenever the adjunction it was produced by
is not the one a criterion consumes — for instance when a composite of two pullback–pushforward
adjunctions of schemes has to be exchanged for the adjunction of the composite morphism, whose
right adjoint is the composite's pushforward rather than the composite of the pushforwards. The
two left adjoints are then isomorphic, so the corollary below moves invertibility across.

## Main results

* `CategoryTheory.homEquiv_symm_conjugateEquiv`: **the identity.** It is
  `CategoryTheory.homEquiv_comp_conjugateEquiv` read on inverse transposes rather than on
  transposes, and so needs only the units of the two adjunctions.
* `CategoryTheory.isIso_homEquiv_symm_conjugateEquiv_iff`: **invertibility is independent of
  which of two adjunctions with isomorphic left adjoints the transpose is taken along.**

## Implementation notes

The identity is stated with the conjugate `CategoryTheory.conjugateEquiv adj₁ adj₂ α` applied to
`g` rather than with an arbitrary natural transformation of right adjoints, because the conjugate
is the only transformation for which it holds —
`CategoryTheory.conjugateEquiv_eq_of_homEquiv` is that converse.

No triangle identity is used, and neither counit appears: `conjugateEquiv` is pinned down on the
nose by its compatibility with the units.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

/-- **The inverse adjoint transposes along two adjunctions whose left adjoints are comparable
differ by the comparison.** For `α : L₂ ⟶ L₁` and `g : X ⟶ R₁.obj Y`, the transpose along `adj₂`
of `g` followed by the conjugate of `α` is the transpose along `adj₁` of `g`, preceded by `α`.

This is `CategoryTheory.homEquiv_comp_conjugateEquiv` with both sides read through the inverse of
the hom-equivalence. -/
public theorem homEquiv_symm_conjugateEquiv (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {X : C} {Y : D} (g : X ⟶ R₁.obj Y) :
    (adj₂.homEquiv X Y).symm (g ≫ (conjugateEquiv adj₁ adj₂ α).app Y) =
      α.app X ≫ (adj₁.homEquiv X Y).symm g := by
  have h := homEquiv_comp_conjugateEquiv adj₁ adj₂ α X Y ((adj₁.homEquiv X Y).symm g)
  rw [Equiv.apply_symm_apply] at h
  rw [h, Equiv.symm_apply_apply]

/-- **Invertibility of an inverse adjoint transpose does not depend on which of two adjunctions
with isomorphic left adjoints it is taken along.** The two transposes differ by the component of
the comparison isomorphism, by `CategoryTheory.homEquiv_symm_conjugateEquiv`. -/
public theorem isIso_homEquiv_symm_conjugateEquiv_iff (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : L₂ ≅ L₁) {X : C} {Y : D} (g : X ⟶ R₁.obj Y) :
    IsIso ((adj₂.homEquiv X Y).symm (g ≫ (conjugateEquiv adj₁ adj₂ α.hom).app Y)) ↔
      IsIso ((adj₁.homEquiv X Y).symm g) := by
  rw [homEquiv_symm_conjugateEquiv adj₁ adj₂ α.hom g]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact let := h; IsIso.of_isIso_comp_left (α.hom.app X) _
  · exact let := h; inferInstance

end CategoryTheory

end
