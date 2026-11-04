module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.FiniteTypeExtendedCech
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.GlobalCechReflector
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ReflectorCompletion
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 099F: the derived completion functor for a sheaf of ideals of finite type

Let `(𝒞, 𝒪)` be a ringed site and `ℐ ⊂ 𝒪` a sheaf of ideals of finite type. [Stacks, Tag 099F]
asserts that the inclusion `D_comp(𝒪, ℐ) ⥤ D(𝒪)` has a left adjoint, and its proof exhibits it
as `E ↦ R𝑆heafHom_𝒪(K, E)` for the map `K ⟶ 𝒪` of [Stacks, Tag 099E]. This file proves the tag,
as an instance, and identifies the derived completion functor
`AlgebraicGeometry.RingedSite.derivedCompletion` of `ReflectorCompletion.lean` — an arbitrary
choice of left adjoint — with that formula, compatibly with the units.

## Main results

* `AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete`: **[Stacks, Tag 099F]** — for
  `ℐ` of finite type the inclusion of the derived-complete objects has a left adjoint.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedCompletionIsoOfIsGlobalExtendedCech`: for any
  `a : K ⟶ 𝒪` with the property of [Stacks, Tag 099E], the derived completion functor is
  `R𝑆heafHom_𝒪(K, -)`.
* `AlgebraicGeometry.RingedSite.derivedCompletionIsoFiniteTypeCech`: the same at the complex
  `AlgebraicGeometry.RingedSite.finiteTypeCech` which [Stacks, Tag 099E] constructs.

## Further results

* `RingedSite.derivedCompletionUnit_comp_derivedCompletionIsoOfIsGlobalExtendedCech_hom`: that
  isomorphism carries the unit `E ⟶ E^∧` to the map `E ⟶ R𝑆heafHom_𝒪(K, E)` induced by `a`.

## References

* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

section Formula

variable [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).IsRightAdjoint]
  [I.toSheafOfModules.IsFiniteType]
  {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
  {a : K ⟶ structureSheafComplex X}

/-- **The derived completion functor is `R𝑆heafHom_𝒪(K, -)`** for any map `a : K ⟶ 𝒪` with the
property of [Stacks, Tag 099E]: the three clauses of
`GlobalCechReflector.lean` make `(R𝑆heafHom_𝒪(K, -), a^*)` a reflection onto the
derived-complete objects, and two left adjoints of one functor are isomorphic. -/
def derivedCompletionIsoOfIsGlobalExtendedCech (ha : IsGlobalExtendedCech X I K a) :
    derivedCompletion X I ≅ completionFunctorOfComplex X K :=
  have hI := Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteType I.toSheafOfModules
    inferInstance
  Stacks.Algebraization.leftAdjointCompιIsoOfCompletionFunctor (completionUnitOfComplex X a)
    (fun E => isDerivedComplete_completionFunctorOfComplex X I ha hI E)
    (fun Z hZ => isIso_completionUnitOfComplex_app_of_isDerivedComplete X I ha hI Z hZ)
    (fun E => isIso_completionFunctorOfComplex_map_completionUnitOfComplex_app X I ha hI E)

/-- **The identification of the derived completion with `R𝑆heafHom_𝒪(K, -)` carries the unit
`E ⟶ E^∧` to the map `E ⟶ R𝑆heafHom_𝒪(K, E)` induced by `a : K ⟶ 𝒪`.** -/
theorem derivedCompletionUnit_comp_derivedCompletionIsoOfIsGlobalExtendedCech_hom
    (ha : IsGlobalExtendedCech X I K a) :
    derivedCompletionUnit X I ≫ (derivedCompletionIsoOfIsGlobalExtendedCech X I ha).hom =
      completionUnitOfComplex X a :=
  Stacks.Algebraization.unit_comp_leftAdjointCompιIsoOfCompletionFunctor_hom _ _ _ _

/-- The componentwise form of
`derivedCompletionUnit_comp_derivedCompletionIsoOfIsGlobalExtendedCech_hom`. -/
theorem derivedCompletionUnit_app_comp_derivedCompletionIsoOfIsGlobalExtendedCech_hom_app
    (ha : IsGlobalExtendedCech X I K a)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedCompletionUnit X I).app E ≫
        (derivedCompletionIsoOfIsGlobalExtendedCech X I ha).hom.app E =
      (completionUnitOfComplex X a).app E :=
  Stacks.Algebraization.unit_app_comp_leftAdjointCompιIsoOfCompletionFunctor_hom_app _ _ _ _ E

end Formula

section Reflector

variable [I.toSheafOfModules.IsFiniteType]

/-- **[Stacks, Tag 099F].** Let `(𝒞, 𝒪)` be a ringed site and `ℐ ⊂ 𝒪` a sheaf of ideals of
finite type. Then the inclusion `D_comp(𝒪, ℐ) ⥤ D(𝒪)` of the objects derived complete along `ℐ`
has a left adjoint.

As in the source, the left adjoint is `E ↦ R𝑆heafHom_𝒪(K, E)` for the map `K ⟶ 𝒪` of
[Stacks, Tag 099E], `AlgebraicGeometry.RingedSite.finiteTypeCechAugmentation`: the three clauses
of the universal property are checked on the slices of a covering family over which `ℐ` is
generated by finitely many sections, in
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_of_isGlobalExtendedCech`; and
`derivedCompletionIsoFiniteTypeCech` below identifies the derived completion functor with that
formula. -/
@[stacks 099F]
instance isRightAdjoint_ι_isDerivedComplete :
    (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).IsRightAdjoint :=
  isRightAdjoint_ι_isDerivedComplete_of_isGlobalExtendedCech X I
    (isGlobalExtendedCech_finiteTypeCech X I)
    (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteType I.toSheafOfModules
      inferInstance)

/-- **The derived completion along a sheaf of ideals of finite type is
`R𝑆heafHom_𝒪(K, -)`**, for the complex `K ⟶ 𝒪` which [Stacks, Tag 099E] constructs. -/
def derivedCompletionIsoFiniteTypeCech :
    derivedCompletion X I ≅ completionFunctorOfComplex X (finiteTypeCech X I) :=
  derivedCompletionIsoOfIsGlobalExtendedCech X I (isGlobalExtendedCech_finiteTypeCech X I)

/-- The identification `derivedCompletionIsoFiniteTypeCech` carries the unit `E ⟶ E^∧` to the
map `E ⟶ R𝑆heafHom_𝒪(K, E)` induced by `K ⟶ 𝒪`. -/
theorem derivedCompletionUnit_comp_derivedCompletionIsoFiniteTypeCech_hom :
    derivedCompletionUnit X I ≫ (derivedCompletionIsoFiniteTypeCech X I).hom =
      completionUnitOfComplex X (finiteTypeCechAugmentation X I) :=
  derivedCompletionUnit_comp_derivedCompletionIsoOfIsGlobalExtendedCech_hom X I _

end Reflector

end AlgebraicGeometry.RingedSite

end
