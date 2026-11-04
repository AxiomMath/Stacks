module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensorSheafify

/-!
# The stalk of an extension of scalars of sheaves of modules at a point of a site

Let `(C, J)` be a site, `Φ` a point of it, and `θ : A₁ ⟶ A₂` a morphism of presheaves of
commutative rings on `C` whose two underlying presheaves of rings are sheaves. Extension of
scalars for sheaves of modules along `θ` (Stacks 03CZ) is the sectionwise tensor product
`A₂ ⊗_{A₁} -` followed by sheafification.

Taking the stalk at `Φ` does not see that sheafification (Stacks 04EQ part (3)), so the stalkwise
formula for the sectionwise tensor product persists at the sheaf level:

`(A₂ ⊗_{A₁} F)_Φ ≅ A₂,Φ ⊗_{A₁,Φ} F_Φ`

for a sheaf of `A₁`-modules `F`, naturally in `F`.

## Main results

* `Stacks.SitePointBaseChange.extendScalarsSheafStalkNatIso`: **the base-change colimit
  interchange at a point of a site, for sheaves of modules**, as a natural isomorphism of stalk
  functors. The stalk functor carries extension of scalars along `θ` to extension of scalars
  along the stalk of `θ`.

## Implementation notes

The stalk functor on sheaves of modules is spelled
`Stacks.SitePointBaseChange.sheafStalk`, the forgetful functor to presheaves of modules
followed by `Stacks.presheafModuleFiberOfCommRing`. This is the same functor as
`Stacks.sheafModuleFiberOfCommRing` for a sheaf of commutative rings, but it is phrased over a
presheaf of commutative rings whose underlying presheaf of rings is a sheaf, which is the datum
that extension of scalars for sheaves of modules consumes.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.SitePointBaseChange

open Stacks.PresheafOfModules.ChangeOfRings Stacks.Sheaves.RingedToposModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} (Φ : J.Point.{u})

/-- The stalk functor at `Φ` on sheaves of modules over a presheaf of commutative rings whose
underlying presheaf of rings is a sheaf, valued in modules over the `CommRingCat`-valued stalk
of that presheaf. -/
abbrev sheafStalk (A : Cᵒᵖ ⥤ CommRingCat.{u}) (h : Presheaf.IsSheaf J (ringPresheaf A)) :
    SheafOfModules.{u} (commRingSheaf J A h) ⥤ ModuleCat.{u} (ringFiber Φ A) :=
  SheafOfModules.forget (commRingSheaf J A h) ⋙ presheafModuleFiberOfCommRing Φ A

variable {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The base-change colimit interchange at a point of a site, for sheaves of modules.**
Taking stalks at `Φ` carries extension of scalars of sheaves of modules along `θ` to extension
of scalars along the stalk of `θ`.

It is the presheaf-level interchange
`Stacks.SitePointBaseChange.extendScalarsStalkNatIso` composed with the statement that the
stalk does not see the sheafification that extension of scalars of sheaves of modules performs
after the sectionwise tensor product. -/
def extendScalarsSheafStalkNatIso :
    Stacks.Sheaves.RingedToposModules.extendScalars J θ h₁ h₂ ⋙ sheafStalk Φ A₂ h₂ ≅
      sheafStalk Φ A₁ h₁ ⋙ ModuleCat.extendScalars (stalkRingHom θ Φ) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (SheafOfModules.forget (commRingSheaf J A₁ h₁) ⋙ changeOfRings θ)
        (Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.fiberSheafifyNatIso Φ
          (commRingSheaf J A₂ h₂)).symm)
      (ModuleCat.restrictScalars.{u} (toRingFiber Φ A₂)) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.forget (commRingSheaf J A₁ h₁))
      (extendScalarsStalkNatIso θ Φ).symm

end Stacks.SitePointBaseChange

end
