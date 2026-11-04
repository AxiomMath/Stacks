module

public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.DGAUniqueness.OverRing

/-!
# Moving the construction of Tag 09M5 to an arbitrary model of `D(𝒪_X)`

The derived tensor products of Tag 09LX are formed at the standard model
`CategoryTheory.HasDerivedCategory.standard` of the derived category of `𝒪_X`-modules. This file
transports the `R`-linear exact equivalence `D(E, d) ≌ D_QCoh(𝒪_X)` of
`AlgebraicGeometry.dgaModelEquivalence` to an arbitrary chosen model, through the comparison
`StacksDraft.DerivedModel.derivedCategoryBModelEquiv`, and records that the
comparison is `R`-linear and exact.

## Main results

* `StacksDraft.DerivedModel.modelEquiv_functor_linear`: the comparison of two models of `D(𝒜)` is
  `R`-linear for an `R`-linear abelian category `𝒜`.
* `AlgebraicGeometry.dgaModelEquivalenceAt`: the equivalence `D_QCoh(𝒪_X) ≌ D(E, d)` at an
  arbitrary model, with its linearity and exactness instances.

## References

* [Stacks Project, Tag 09M5](https://stacks.math.columbia.edu/tag/09M5)
* [Stacks Project, Tag 09SU](https://stacks.math.columbia.edu/tag/09SU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Duality.CompactBoundedness StacksDraft.DerivedModel

universe u w z

namespace StacksDraft.DerivedModel

variable {C : Type*} [Category* C] [Abelian C] (R : Type*) [Ring R] [Linear R C]
  (h₁ : HasDerivedCategory.{w} C) (h₂ : HasDerivedCategory.{z} C)

/-- **The comparison of two models of the derived category is `R`-linear**, for an `R`-linear
abelian category: it is the lift, along the localization of the first model, of the localization
of the second, which is `R`-linear. -/
theorem modelEquiv_functor_linear : (modelEquiv h₁ h₂).functor.Linear R := by
  let : Localization.Lifting (@DerivedCategory.Q C _ _ h₁)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (@DerivedCategory.Q C _ _ h₂)
      (modelEquiv h₁ h₂).functor := ⟨modelCompQIso h₁ h₂⟩
  exact (Localization.functor_linear_iff (@DerivedCategory.Q C _ _ h₁)
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) R (@DerivedCategory.Q C _ _ h₂)
    (modelEquiv h₁ h₂).functor).1 inferInstance

/-- The inverse comparison of two models of the derived category is `R`-linear. -/
theorem modelEquiv_inverse_linear : (modelEquiv h₁ h₂).inverse.Linear R :=
  let := modelEquiv_functor_linear R h₁ h₂
  Equivalence.inverseLinear R (modelEquiv h₁ h₂)

end StacksDraft.DerivedModel

namespace AlgebraicGeometry

/-- The scheme read as a ringed site. -/
local notation "𝒮" X => Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite X

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

/-- An `R`-linear structure on the `𝒪_X`-modules of the site of opens, read on `X.Modules`, which
is the same category. -/
@[instance_reducible]
def modulesLinearOfSite (X : Scheme.{u}) (R : Type u) [CommRing R]
    [Linear R (RingedSite.TensorModO.{u, u, u, u, u} (𝒮 X))] : Linear R X.Modules :=
  inferInstanceAs (Linear R (RingedSite.TensorModO.{u, u, u, u, u} (𝒮 X)))

attribute [local instance] modulesLinearOfSite

/-- `D_QCoh(𝒪_X)` at an arbitrary model of `D(𝒪_X)`. -/
abbrev qcohDerivedAt (X : Scheme.{u}) (h : HasDerivedCategory.{w} X.Modules) :
    ObjectProperty (@DerivedCategory X.Modules _ _ h) :=
  @DerivedCategoryB.derivedCategoryB X.Modules _ _ h (SheafOfModules.isQuasicoherent X.ringCatSheaf)

/-- `D_QCoh(𝒪_X)` at an arbitrary model is closed under isomorphisms. -/
instance (X : Scheme.{u}) (h : HasDerivedCategory.{w} X.Modules) :
    (qcohDerivedAt X h).IsClosedUnderIsomorphisms :=
  @DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms X.Modules _ _ h _
    (isWeakSerre_isQuasicoherent X)

/-- `D_QCoh(𝒪_X)` at an arbitrary model is a triangulated subcategory. -/
instance (X : Scheme.{u}) (h : HasDerivedCategory.{w} X.Modules) :
    (qcohDerivedAt X h).IsTriangulated :=
  @DerivedCategoryB.derivedCategoryB_isTriangulated X.Modules _ _ h _
    (isWeakSerre_isQuasicoherent X)

/-- The comparison of `D_QCoh(𝒪_X)` at the standard model with `D_QCoh(𝒪_X)` at a model `h`. -/
abbrev qcohModelEquiv (X : Scheme.{u}) (h : HasDerivedCategory.{w} X.Modules) :
    (qcohDerivedProperty X).FullSubcategory ≌ (qcohDerivedAt X h).FullSubcategory :=
  derivedCategoryBModelEquiv (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (HasDerivedCategory.standard X.Modules) h

/-- The comparison of a model `h` of `D(𝒪_X)` with the standard model, on `D_QCoh(𝒪_X)`, with
values in the standard model read on the site of opens. -/
def qcohModelInverseAux (X : Scheme.{u}) (h : HasDerivedCategory.{w} X.Modules) :
    (qcohDerivedAt X h).FullSubcategory ⥤ stdDerived X :=
  (qcohDerivedAt X h).ι ⋙ (modelEquiv (HasDerivedCategory.standard X.Modules) h).inverse

/-- `qcohModelInverseAux X h` commutes with the shifts by `ℤ`. -/
instance (X : Scheme.{u}) (h : HasDerivedCategory.{w} X.Modules) :
    (qcohModelInverseAux X h).CommShift ℤ :=
  (inferInstance : ((qcohDerivedAt X h).ι ⋙
    (modelEquiv (HasDerivedCategory.standard X.Modules) h).inverse).CommShift ℤ)

/-- `qcohModelInverseAux X h` is a triangulated functor. -/
instance (X : Scheme.{u}) (h : HasDerivedCategory.{w} X.Modules) :
    (qcohModelInverseAux X h).IsTriangulated :=
  (inferInstance : ((qcohDerivedAt X h).ι ⋙
    (modelEquiv (HasDerivedCategory.standard X.Modules) h).inverse).IsTriangulated)

/-- `qcohModelInverseAux X h` takes values in `D_QCoh(𝒪_X)` at the standard model. -/
theorem qcohModelInverseAux_mem (X : Scheme.{u}) (h : HasDerivedCategory.{w} X.Modules)
    (Y : (qcohDerivedAt X h).FullSubcategory) :
    qcohDerivedProperty X ((qcohModelInverseAux X h).obj Y) :=
  ((qcohModelEquiv X h).inverse.obj Y).property

section

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (R : Type u) [CommRing R] [Linear R (RingedSite.TensorModO.{u, u, u, u, u} (𝒮 X))]
  [RingedSite.ScalarSections.{u, u, u, u, u, u} (𝒮 X) R]
  {K : CochainComplex (RingedSite.ModO.{u, u, u, u} (𝒮 X)) ℤ}
  (hK : IsPerfectGeneratorRepresentative X K) (h : HasDerivedCategory.{w} X.Modules)

/-- **The equivalence `D_QCoh(𝒪_X) ≌ D(E, d)` of the construction of Tag 09M5 at the model
`h`**: the quasi-inverse of `- ⊗_E^𝐋 K`, preceded by the comparison of `h` with the standard
model. -/
def dgaModelEquivalenceAt :
    (qcohDerivedAt X h).FullSubcategory ≌
      DifferentialGradedModule.derivedCategory.{u, u, u}
        (RingedSite.Rep.{u, u, u, u, u, u} (𝒮 X) R K).algebra :=
  (qcohModelEquiv X h).symm.trans (dgaModelEquivalence R hK).symm

/-- **The equivalence of the construction is `R`-linear**, at every model. -/
instance dgaModelEquivalenceAt_functor_linear :
    (dgaModelEquivalenceAt R hK h).functor.Linear R := by
  let := modelEquiv_inverse_linear R (HasDerivedCategory.standard X.Modules) h
  have : (qcohModelEquiv X h).inverse.Linear R :=
    ⟨fun {M N} g r => ObjectProperty.hom_ext _
      ((modelEquiv (HasDerivedCategory.standard X.Modules) h).inverse.map_smul r g.hom)⟩
  let := Equivalence.inverseLinear R (dgaModelEquivalence R hK)
  exact (inferInstance :
    ((qcohModelEquiv X h).inverse ⋙ (dgaModelEquivalence R hK).inverse).Linear R)

/-- **The equivalence of the construction is an exact equivalence**, at every model: its functor
commutes with the translations and carries distinguished triangles to distinguished triangles. -/
theorem dgaModelEquivalenceAt_isTriangulated :
    ∃ _ : (dgaModelEquivalenceAt R hK h).functor.CommShift ℤ,
      (dgaModelEquivalenceAt R hK h).functor.IsTriangulated := by
  let hc : (qcohModelEquiv X h).inverse.CommShift ℤ :=
    (inferInstance : ((qcohDerivedProperty X).lift (qcohModelInverseAux X h)
        (qcohModelInverseAux_mem X h)).CommShift ℤ)
  have : (qcohModelEquiv X h).inverse.IsTriangulated :=
    (inferInstance : ((qcohDerivedProperty X).lift (qcohModelInverseAux X h)
        (qcohModelInverseAux_mem X h)).IsTriangulated)
  let := (dgaModelEquivalence R hK).commShiftInverse ℤ
  let : (dgaModelEquivalence R hK).CommShift ℤ := (dgaModelEquivalence R hK).commShift_of_functor ℤ
  have : (dgaModelEquivalence R hK).IsTriangulated :=
    Equivalence.IsTriangulated.mk' _ (inferInstance :
      (dgaModelEquivalence R hK).functor.IsTriangulated)
  exact ⟨(inferInstance : ((qcohModelEquiv X h).inverse ⋙
      (dgaModelEquivalence R hK).inverse).CommShift ℤ),
    (inferInstance : ((qcohModelEquiv X h).inverse ⋙
      (dgaModelEquivalence R hK).inverse).IsTriangulated)⟩

end

end AlgebraicGeometry

end
