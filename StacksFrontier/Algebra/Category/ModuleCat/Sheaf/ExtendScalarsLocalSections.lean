module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

/-!
# A section of an extension of scalars is locally a sectionwise tensor

Let `θ : A₁ ⟶ A₂` be a morphism of presheaves of commutative rings on a site whose underlying
presheaves of rings are sheaves, and let `L` be a sheaf of `A₁`-modules.  Extension of scalars
`Stacks.Sheaves.RingedToposModules.extendScalars` is the *sheafification* of the sectionwise
tensor product `V ↦ A₂(V) ⊗_{A₁(V)} L(V)`, so a section of `A₂ ⊗_{A₁} L` over an object `V` need
not be a sectionwise tensor there; but it becomes one on a covering sieve of `V`, the
sheafification unit being locally surjective.

## Why this is here

This is the extension-of-scalars half of the local description of sections that the **general**
converse of Stacks 08HD needs — the one for an arbitrary `𝒪_S`-module, which this development has
only for a quasi-coherent one.  Along the factorization of `ε^*` into `ε⁻¹` followed by extension
of scalars, the source's proof of that converse writes a generating section of `ε^*𝓕` as a finite
sum of elementary tensors `Σ bᵢ ⊗ tᵢ` after shrinking the étale object; the shrinking is this
statement and the `tᵢ` are produced by
`AlgebraicGeometry.SmallEtale.exists_sieve_imageOpen_section`.

Every statement in the library relating `extendScalars` to generation goes the other way —
`Stacks.Sheaves.RingedToposModules.extendScalars_exists_finite_generators`,
`extendScalars_isLocallyGeneratedBy`, `generatingSections_leftAdjoint_restrictScalars` are all
left-adjoint formal nonsense and preserve only.  What is below is not about generation at all: it
is the one fact about *sections* of the sheafification that the descent of generators needs, and
it was not named.

## Main results

* `Stacks.Sheaves.RingedToposModules.isLocallySurjective_toSheafifyExtendScalars`: the
  sheafification unit `A₂ ⊗_{A₁} L ⟶ extendScalars L` is locally surjective.
* `Stacks.Sheaves.RingedToposModules.exists_sieve_changeOfRings_section`: the elementwise form —
  **a section of `extendScalars L` over `V` is, on a covering sieve of `V`, the image of a
  sectionwise tensor.**  Each such section of `A₂(W) ⊗_{A₁(W)} L(W)` is a finite sum of elementary
  tensors, by the construction of the tensor product.

## Implementation notes

`CategoryTheory.PresheafOfModules.isLocallySurjective_sheafificationAdjunction_unit_app` has to be
applied by hand rather than found by instance search: the sheaf of rings it is indexed by occurs
in its statement only under a projection applied to the identity, so nothing determines it.  This
is the same obstruction that forces `Stacks.SheafOfModules.isLocallySurjective_toSheafify` to
exist as a separate name.  Restating the conclusion as an instance at the `extendScalars`
spelling is what makes it available to the elementwise form below.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 08HD](https://stacks.math.columbia.edu/tag/08HD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.PresheafOfModules.ChangeOfRings

namespace Stacks.Sheaves.RingedToposModules

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
variable (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))
variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The sheafification unit of the sectionwise tensor product**, whose target is the extension
of scalars of Stacks 03CZ by definition of
`Stacks.Sheaves.RingedToposModules.extendScalars`. -/
noncomputable abbrev toSheafifyExtendScalars
    (L : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) :=
  (PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
    ((changeOfRings θ).obj L.val)

/-- **The sheafification unit `A₂ ⊗_{A₁} L ⟶ extendScalars L` is locally surjective.** -/
instance isLocallySurjective_toSheafifyExtendScalars
    (L : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) :
    PresheafOfModules.IsLocallySurjective J (toSheafifyExtendScalars J θ h₁ h₂ L) :=
  PresheafOfModules.isLocallySurjective_sheafificationAdjunction_unit_app
    (α := (𝟙 (commRingSheaf J A₂ h₂).obj)) _

/-- **A section of an extension of scalars is locally a sectionwise tensor.**  There is a covering
sieve of `V` over each member `W` of which the restricted section is the image of a section of
`A₂(W) ⊗_{A₁(W)} L(W)`.

This is the shrinking step of Stacks' proof of the converse of Stacks 08HD: a generating section
of `ε^*𝓕` becomes a finite sum of elementary tensors after passing to a further étale object. -/
theorem exists_sieve_changeOfRings_section
    (L : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) {V : C}
    (x : ((PresheafOfModules.toPresheaf (commRingSheaf J A₂ h₂).obj).obj
      ((extendScalars J θ h₁ h₂).obj L).val).obj (op V)) :
    ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (g : W ⟶ V), T g →
      ∃ y : ((PresheafOfModules.toPresheaf (commRingSheaf J A₂ h₂).obj).obj
          ((changeOfRings θ).obj L.val)).obj (op W),
        ((PresheafOfModules.toPresheaf (commRingSheaf J A₂ h₂).obj).map
            (toSheafifyExtendScalars J θ h₁ h₂ L)).app (op W) y =
          ((PresheafOfModules.toPresheaf (commRingSheaf J A₂ h₂).obj).obj
            ((extendScalars J θ h₁ h₂).obj L).val).map g.op x :=
  ⟨Presheaf.imageSieve ((PresheafOfModules.toPresheaf (commRingSheaf J A₂ h₂).obj).map
      (toSheafifyExtendScalars J θ h₁ h₂ L)) x,
    (isLocallySurjective_toSheafifyExtendScalars J θ h₁ h₂ L).imageSieve_mem x,
    fun _ _ hg => hg⟩

end Stacks.Sheaves.RingedToposModules

end
