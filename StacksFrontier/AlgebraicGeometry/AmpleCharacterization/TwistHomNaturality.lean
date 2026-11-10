module

public import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.ClauseFive
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.UnitScalar

/-!
# The morphism attached to a section of a twist is natural in the module

`Stacks.AmpleCharacterization.twistHom L F n m : L ^⊗ (-n) ⟶ F` is the morphism out of a negative
twist attached to a global section `m` of `F ⊗ L ^⊗ n`. This file proves that the construction is
natural in `F`: pushing the section forward along `φ : F ⟶ G` and then taking `twistHom` is the
same as taking `twistHom` and then composing with `φ`.

This is what converts a statement about *sections* of the twists of a family of modules into a
statement about *morphisms out of the negative twist*. It is the step that lets a compatible
family of sections of the twisted terms of an inverse system be read as a compatible family of
morphisms into those terms, which is the form in which such a family assembles into a single
morphism out of a direct sum of negative twists.

## Main results

* `Stacks.AmpleCharacterization.unitHom_comp` — a global section read as a morphism out of the
  monoidal unit is natural: `unitHom N (ψ m) = unitHom M m ≫ ψ`.
* `Stacks.AmpleCharacterization.twistHom_app_comp` — **the naturality of `twistHom`**.

## Implementation notes

`Stacks.AmpleCharacterization.unitHom` is definitionally the inverse of
`Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv`, which is what makes `unitHom_comp` a
calculation with `Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv_apply` rather than an
excursion through the three spellings of a global section.

Naturality of `twistHom` is then forced rather than computed: tensoring by `L ^⊗ n` is an
equivalence, hence faithful, and `Stacks.AmpleCharacterization.whiskerRight_twistHom` identifies
both sides after tensoring, where the only remaining content is naturality of `unitHom`.

## References

* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AmpleCharacterization

attribute [local instance] Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}}

/-- **A global section read as a morphism out of the monoidal unit is natural.** Pushing a global
section of `M` forward along `ψ : M ⟶ N` and then reading it as a morphism out of the unit is
composing with `ψ`.

`Stacks.AmpleCharacterization.unitHom` is the inverse of
`Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv`, and that equivalence evaluates a
morphism out of the unit at the canonical section, so naturality in this direction is the
statement that evaluation commutes with composition. -/
public theorem unitHom_comp {M N : X.Modules} (ψ : M ⟶ N) (m : Γ(M, ⊤)) :
    unitHom N (ψ.app ⊤ m) = unitHom M m ≫ ψ := by
  change (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X N).symm (ψ.app ⊤ m) =
    (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X M).symm m ≫ ψ
  rw [AddEquiv.symm_apply_eq,
    Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv_apply, ← Category.assoc,
    Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    ← Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv_apply,
    AddEquiv.apply_symm_apply]

/-- **`Stacks.AmpleCharacterization.twistHom` is natural in the module.** For `φ : F ⟶ G` and a
global section `m` of `F ⊗ L ^⊗ n`, the morphism `L ^⊗ (-n) ⟶ G` attached to the pushforward of
`m` along `φ ▷ L ^⊗ n` is the morphism attached to `m` followed by `φ`.

Tensoring by `L ^⊗ n` is an equivalence, hence faithful, so it is enough to check the identity
after tensoring; there `Stacks.AmpleCharacterization.whiskerRight_twistHom` reduces it to
`Stacks.AmpleCharacterization.unitHom_comp`. -/
public theorem twistHom_app_comp (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    {F G : X.Modules} (φ : F ⟶ G) (n : ℤ)
    (m : Γ(F ⊗ Stacks.Ample.tensorPowModule X L n, ⊤)) :
    twistHom L G n ((φ ▷ Stacks.Ample.tensorPowModule X L n).app ⊤ m) =
      twistHom L F n m ≫ φ := by
  have := Stacks.AmpleGlobalGeneration.isEquivalence_tensorRight L n
  refine (CategoryTheory.MonoidalCategory.tensorRight
    (Stacks.Ample.tensorPowModule X L n)).map_injective ?_
  change twistHom L G n _ ▷ _ = (twistHom L F n m ≫ φ) ▷ _
  rw [whiskerRight_twistHom, comp_whiskerRight, whiskerRight_twistHom, Category.assoc,
    unitHom_comp]

end Stacks.AmpleCharacterization

end
