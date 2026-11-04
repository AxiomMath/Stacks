module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules

/-!
# Extension of scalars along a composite, and along an isomorphism

`Stacks.Sheaves.RingedToposModules.extendScalars` is the change-of-rings functor of
Stacks 03CZ for sheaves of modules on a fixed site, defined as the sheafified sectionwise tensor
product and characterised by
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction` as the left adjoint of
restriction of scalars.  Two consequences of that characterisation are recorded here, both at
the universes the construction is stated at — arbitrary object and morphism universes for the
site, and an arbitrary universe for the sections.

*Composition.*  Restriction of scalars along a composite is restriction along the two factors in
turn, on the nose, so the composite of the two adjunctions is an adjunction with the same right
adjoint as the adjunction of the composite; uniqueness of left adjoints identifies the two left
adjoints.

*Isomorphisms.*  When the morphism of sheaves of rings is invertible, restriction of scalars
along it is an equivalence
(`Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso`), whose own left adjoint is its
inverse; so extension of scalars along it is an equivalence, and in particular left exact.  Note
that *no* flatness hypothesis is needed, and none would help: an isomorphism is flat, but the
flatness predicate for sheaves of commutative rings is stated after a universe lift of the
sections, and the transport of flatness through that lift is exactly what this avoids.

Together the two let a morphism of sheaves of commutative rings be replaced by any morphism it
differs from by an isomorphism, when what is wanted is left exactness of extension of scalars
along it.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.extendScalarsCompIso`: extension of scalars along a
  composite is the composite of the extensions of scalars.

## Main results

* `Stacks.Sheaves.RingedToposModules.preservesFiniteLimits_extendScalars_of_iso`: extension of
  scalars along a morphism of sheaves of commutative rings whose underlying morphism of sheaves
  of rings is invertible is left exact.
* `Stacks.Sheaves.RingedToposModules.preservesFiniteLimits_extendScalars_comp_iso`: left
  exactness of extension of scalars is unaffected by precomposing the morphism with an
  isomorphism.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.Sheaves.RingedToposModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {A₁ A₂ A₃ : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- **Extension of scalars along a composite is the composite of the extensions of scalars.**
Both are left adjoint to restriction of scalars along the composite, restriction of scalars
along a composite being restriction along the two factors in turn on the nose. -/
public noncomputable def extendScalarsCompIso (θ₁ : A₁ ⟶ A₂) (θ₂ : A₂ ⟶ A₃)
    (h₁ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁))
    (h₂ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂))
    (h₃ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₃)) :
    extendScalars J (θ₁ ≫ θ₂) h₁ h₃ ≅
      extendScalars J θ₁ h₁ h₂ ⋙ extendScalars J θ₂ h₂ h₃ :=
  Adjunction.leftAdjointUniq (extendRestrictScalarsAdjunction J (θ₁ ≫ θ₂) h₁ h₃)
    ((extendRestrictScalarsAdjunction J θ₁ h₁ h₂).comp
      (extendRestrictScalarsAdjunction J θ₂ h₂ h₃))

/-- **Extension of scalars along an invertible morphism of sheaves of commutative rings is left
exact.**  Restriction of scalars along the isomorphism is an equivalence, so its own left
adjoint is the inverse equivalence; extension of scalars, being a left adjoint of the same
functor, is isomorphic to that inverse and hence preserves all limits. -/
public theorem preservesFiniteLimits_extendScalars_of_iso (θ : A₁ ⟶ A₂)
    (h₁ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁))
    (h₂ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂))
    (e : commRingSheaf J A₁ h₁ ≅ commRingSheaf J A₂ h₂)
    (he : e.hom = commRingSheafMap J θ h₁ h₂) :
    PreservesFiniteLimits (extendScalars J θ h₁ h₂) := by
  have adj₂ : (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso e).functor ⊣
      SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂) :=
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso e).toAdjunction.ofNatIsoRight
      (eqToIso (congrArg SheafOfModules.restrictScalars he))
  have hpres : PreservesFiniteLimits
      (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso e).functor := inferInstance
  exact preservesFiniteLimits_of_natIso
    (Adjunction.leftAdjointUniq (extendRestrictScalarsAdjunction J θ h₁ h₂) adj₂).symm

/-- **Left exactness of extension of scalars is unaffected by precomposing with an
isomorphism.**  Extension of scalars along the composite is the composite of the two extensions
of scalars, and the one along the isomorphism is left exact for free. -/
public theorem preservesFiniteLimits_extendScalars_comp_iso (θ₁ : A₁ ⟶ A₂) (θ₂ : A₂ ⟶ A₃)
    (h₁ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁))
    (h₂ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂))
    (h₃ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₃))
    (e : commRingSheaf J A₁ h₁ ≅ commRingSheaf J A₂ h₂)
    (he : e.hom = commRingSheafMap J θ₁ h₁ h₂)
    (h : PreservesFiniteLimits (extendScalars J θ₂ h₂ h₃)) :
    PreservesFiniteLimits (extendScalars J (θ₁ ≫ θ₂) h₁ h₃) := by
  have h₀ : PreservesFiniteLimits (extendScalars J θ₁ h₁ h₂) :=
    preservesFiniteLimits_extendScalars_of_iso J θ₁ h₁ h₂ e he
  have : PreservesFiniteLimits (extendScalars J θ₁ h₁ h₂ ⋙ extendScalars J θ₂ h₂ h₃) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).symm

end Stacks.Sheaves.RingedToposModules

end
