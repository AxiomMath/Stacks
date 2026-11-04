module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.ToposThickening.ComplexMapLift

/-!
# Lifts of a bounded above complex across a square-zero extension of sheaves of rings

Let `f : O ⟶ O₀` be a surjection of sheaves of commutative rings on a site whose kernel is an
ideal sheaf of square zero, and let `K₀` be a bounded above object of the derived category of
`O₀`-modules. A *lift* of `K₀` is a bounded above object `K` of the derived category of
`O`-modules together with an isomorphism `K ⊗_O^L O₀ ≅ K₀`.

The derived base change `- ⊗_O^L O₀` is the left derived functor of the degreewise
extension-of-scalars functor `Deformation.ComplexLift.extensionOfScalarsCochainComplex` of
Tag 0DIX, which is the sheaf-level form of `O₀ ⊗_O -`. A choice of such a left derived functor
is recorded by `Deformation.ComplexLift.DerivedExtensionOfScalars`, and a lift is defined
relative to one. Any two choices are canonically isomorphic
(`Deformation.ComplexLift.DerivedExtensionOfScalars.baseChangeIso`), and lifts transport along
that isomorphism, so the notion of a lift does not depend on the choice.

## Main definitions

* `Deformation.ComplexLift.DerivedExtensionOfScalars`: a derived base change along `f`, i.e. a
  functor on the unbounded derived categories exhibited as the left derived functor of
  degreewise extension of scalars.
* `Deformation.ComplexLift.DerivedLift`: **Stacks 0DIZ**, a lift of a bounded above object of
  the derived category of `O₀`-modules.

## Main results

* `Deformation.ComplexLift.DerivedExtensionOfScalars.baseChangeIso`: two derived base changes
  along `f` are canonically isomorphic, by uniqueness of left derived functors.
* `Deformation.ComplexLift.DerivedLift.transport`: a lift for one derived base change is a lift
  for any other.
* `Deformation.ComplexLift.DerivedLift.ofIso`: a lift of `K₀` is a lift of anything isomorphic
  to `K₀`.

## Implementation notes

The source states the isomorphism `α₀ : K ⊗_O^L O₀ ⟶ K₀` in `D(O₀)`, and bounds both `K` and
`K₀` above; that is what is written here, with `DerivedCategory.Minus` for the bounded above
derived category and the isomorphism taken in the ambient unbounded derived category of
`O₀`-modules, into which `DerivedCategory.Minus` is a full subcategory.

Derived base change is taken as data rather than constructed. Tag 0DIZ is a statement about
lifts, not about the existence of `- ⊗_O^L O₀`; making the functor a parameter also records
that the notion of a lift uses nothing about it beyond its universal property, and the
uniqueness result below turns that parameter into a harmless one. The two derived categories
have independent hom universes, as `HasDerivedCategory.{d}` and `HasDerivedCategory.{d₀}`.

## References

* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
* [Stacks Project, Tag 0DIX](https://stacks.math.columbia.edu/tag/0DIX)
-/

@[expose] public section

open CategoryTheory

universe d d₀ v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)
variable [HasDerivedCategory.{d}
  (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))]
variable [HasDerivedCategory.{d₀}
  (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))]

/-- Derived base change `- ⊗_O^L O₀` along a morphism `f : O ⟶ O₀` of sheaves of commutative
rings: a functor between the unbounded derived categories of sheaves of modules, exhibited by
`comparison` as the left derived functor of the degreewise extension-of-scalars functor
`Deformation.ComplexLift.extensionOfScalarsCochainComplex` along the localization of cochain
complexes at the quasi-isomorphisms. -/
structure DerivedExtensionOfScalars where
  /-- The derived base change functor. -/
  baseChange : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))) ⥤
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))
  /-- Its comparison with degreewise extension of scalars. -/
  comparison : DerivedCategory.Q ⋙ baseChange ⟶
    extensionOfScalarsCochainComplex J f ⋙ DerivedCategory.Q
  /-- The comparison exhibits `baseChange` as a left derived functor. -/
  isLeftDerived : baseChange.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))
      (ComplexShape.up ℤ))

attribute [instance] DerivedExtensionOfScalars.isLeftDerived

variable {f}

namespace DerivedExtensionOfScalars

/-- Any two derived base changes along `f` are canonically isomorphic: both are left derived
functors of the same degreewise extension-of-scalars functor. -/
noncomputable def baseChangeIso (T T' : DerivedExtensionOfScalars f) :
    T.baseChange ≅ T'.baseChange :=
  Functor.leftDerivedUnique T'.baseChange T.baseChange T.comparison T'.comparison
    (HomologicalComplex.quasiIso (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))
      (ComplexShape.up ℤ))

end DerivedExtensionOfScalars

/-- **Stacks 0DIZ.** A lift of a bounded above object `K₀` of the derived category of
`O₀`-modules across the derived base change `T` along `f : O ⟶ O₀`: a bounded above object `K`
of the derived category of `O`-modules together with an isomorphism
`K ⊗_O^L O₀ ≅ K₀` in the derived category of `O₀`-modules. -/
@[stacks 0DIZ "a lift of a bounded above derived complex"]
structure DerivedLift (T : DerivedExtensionOfScalars f)
    (K₀ : DerivedCategory.Minus
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))) where
  /-- The bounded above object of the derived category of `O`-modules. -/
  K : DerivedCategory.Minus (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))
  /-- Its derived base change is identified with `K₀`. -/
  identification : T.baseChange.obj K.obj ≅ K₀.obj

namespace DerivedLift

/-- A lift of `K₀` is a lift of any object isomorphic to `K₀`. -/
@[simps]
noncomputable def ofIso {T : DerivedExtensionOfScalars f}
    {K₀ K₀' : DerivedCategory.Minus
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))}
    (L : DerivedLift T K₀) (e : K₀.obj ≅ K₀'.obj) : DerivedLift T K₀' where
  K := L.K
  identification := L.identification ≪≫ e

/-- A lift for one derived base change along `f` is a lift for any other, by uniqueness of
left derived functors. -/
@[simps]
noncomputable def transport {T T' : DerivedExtensionOfScalars f}
    {K₀ : DerivedCategory.Minus
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))}
    (L : DerivedLift T K₀) : DerivedLift T' K₀ where
  K := L.K
  identification :=
    ((DerivedExtensionOfScalars.baseChangeIso T' T).app L.K.obj) ≪≫ L.identification

end DerivedLift

end Deformation.ComplexLift

end
