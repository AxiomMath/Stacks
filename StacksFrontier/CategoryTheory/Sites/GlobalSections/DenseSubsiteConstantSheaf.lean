module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# A global-sections functor travels up the inclusion of a dense subsite

Let `v : C ⥤ D` exhibit `(C, J)` as a dense subsite of `(D, K)`
(`CategoryTheory.Functor.IsDenseSubsite`) and let `A` be a coefficient category in which the
right Kan extensions along `v.op` exist, so that restriction of sheaves
`v⁻¹ = v.sheafPushforwardContinuous A J K` is an equivalence. Then

* the restriction of a constant sheaf is the constant sheaf, `v⁻¹ ∘ M_D ≅ M_C`, and
* `(D, K)` admits a global-sections functor for `A`-valued sheaves as soon as `(C, J)` does.

The second statement is the one that is not otherwise available. `CategoryTheory.Sheaf.Γ` is
the right adjoint of the constant sheaf functor, and Mathlib produces that adjoint in exactly
two ways: from a terminal object of the site
(`CategoryTheory.hasGlobalSectionsFunctor_of_hasTerminal`) or from limits of shape `Dᵒᵖ` in the
coefficients (`CategoryTheory.hasGlobalSectionsFunctor_of_hasLimitsOfShape`). On a site whose
objects live one universe above its morphisms — the small étale site of an algebraic space, the
spaces-étale site, the fppf and lisse-étale sites of an algebraic stack — neither applies at the
universe of the morphisms unless the site happens to be essentially small; and when it is, the
route through the small model is this statement.

## Main results

* `Stacks.DenseSubsiteGlobalSections.constantSheafRestrictIso`: **the restriction of a constant
  sheaf to a dense subsite is the constant sheaf.**
* `Stacks.DenseSubsiteGlobalSections.hasGlobalSectionsFunctor_of_isDenseSubsite`: **a
  global-sections functor on a dense subsite produces one on the ambient site.**

## Implementation notes

The four universes of the two sites and the two universes of the coefficients are free and
independent; that is the point, since the intended use has `C : Type u` small and
`D : Type (u + 1)`. This is why
`Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso`
(`HigherDirectImage/DenseSubsiteGlobalCohomology.lean` under
`StacksFrontier/CategoryTheory/Sites/Cohomology/`)
is not reused here even though its statement is the same: it is seated at `{C D : Type u}` with
`[Category.{v} C] [Category.{v} D]`, both sites in one pair of universes, and it takes
cocontinuity of `v` as a hypothesis in place of the dense-subsite condition. The construction
below goes instead through Mathlib's
`CategoryTheory.Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility`, which needs only
`CategoryTheory.Functor.IsDenseSubsite` together with the invertibility of restriction that the
right Kan extensions supply.

The same construction appears as the local `let a` inside
`Stacks.Cohomology.ColimitsOfCohomology.denseSubsite_globalSectionsIso`
(`FilteredColimits/GlobalCohomologyOnALargeSite.lean` under
`StacksFrontier/CategoryTheory/Sites/Cohomology/`),
which is the companion statement that the two global-sections functors *agree*,
`v⁻¹ ⋙ Γ(C, -) ≅ Γ(D, -)`. That statement assumes `HasGlobalSectionsFunctor` on both sites; it
is the consumer of the theorem below rather than a substitute for it, and it is not duplicated
here.

## References

* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU), the Comparison Lemma
* [Stacks Project, Tag 03CG](https://stacks.math.columbia.edu/tag/03CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DenseSubsiteGlobalSections

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (v : C ⥤ D)
  (A : Type u₃) [Category.{v₃} A] [v.IsDenseSubsite J K]
  [∀ X, HasLimitsOfShape (StructuredArrow X v.op) A]
  [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- **The restriction of a constant sheaf to a dense subsite is the constant sheaf.**

On presheaves the restriction of a constant presheaf along `v.op` is the constant presheaf on
the nose, and restriction of sheaves along the inclusion of a dense subsite commutes with
sheafification by
`CategoryTheory.Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility`. -/
def constantSheafRestrictIso :
    constantSheaf K A ⋙ v.sheafPushforwardContinuous A J K ≅ constantSheaf J A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.const Dᵒᵖ)
      (Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility J K v A).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Iso.refl (Functor.const Dᵒᵖ ⋙ (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj v.op))
      (presheafToSheaf J A)

/-- The constant sheaf functor of the ambient site, read through the subsite: it is the constant
sheaf functor of the subsite followed by the inverse of restriction. -/
def constantSheafIsoCompInverse :
    constantSheaf J A ⋙ (v.sheafPushforwardContinuous A J K).asEquivalence.inverse ≅
      constantSheaf K A :=
  Functor.isoWhiskerRight (constantSheafRestrictIso J K v A).symm
      (v.sheafPushforwardContinuous A J K).asEquivalence.inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (constantSheaf K A)
      (v.sheafPushforwardContinuous A J K).asEquivalence.unitIso.symm ≪≫
    Functor.rightUnitor _

include v in
/-- **A global-sections functor on a dense subsite produces one on the ambient site.**

The constant sheaf functor of `(D, K)` is the constant sheaf functor of `(C, J)` followed by the
inverse of restriction (`constantSheafIsoCompInverse`), and both of those are left adjoints — the
first by hypothesis, the second because restriction is an equivalence. Its right adjoint is
therefore restriction followed by `Γ(C, -)`, which is the isomorphism
`Stacks.Cohomology.ColimitsOfCohomology.denseSubsite_globalSectionsIso` once both sides exist. -/
theorem hasGlobalSectionsFunctor_of_isDenseSubsite [HasGlobalSectionsFunctor J A] :
    HasGlobalSectionsFunctor K A :=
  ⟨v.sheafPushforwardContinuous A J K ⋙ Sheaf.Γ J A,
    ⟨((constantSheafΓAdj J A).comp
        (v.sheafPushforwardContinuous A J K).asEquivalence.symm.toAdjunction).ofNatIsoLeft
      (constantSheafIsoCompInverse J K v A)⟩⟩

end Stacks.DenseSubsiteGlobalSections

end
