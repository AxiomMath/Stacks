module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualizingUniqueness.Model
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsClauseThree
public import Mathlib.CategoryTheory.Monoidal.Transport

/-!
# The derived tensor product of `D(𝒪_X)` for an algebraic space `X`

The derived tensor product of Stacks 0FPT is built for ringed sites whose objects, morphisms and
sections lie in one universe, and the small étale ringed site of an algebraic space is not one.
Its `𝒪_X`-modules are those of the equi-universe model of the small étale site
(`AlgebraicGeometry.Space.modulesEquivModelModules`), so `D(𝒪_X)` is equivalent to the derived
category of the model, and the symmetric monoidal structure of the model is carried to `D(𝒪_X)`
along that equivalence: `K ⊗^L L` is the derived tensor product of the transports of `K` and `L`
to the model, carried back. This is the device the development uses for the derived tensor–Hom
statements on an algebraic space (Stacks 0E4Q).

## Main definitions

* `AlgebraicGeometry.Space.derivedMonoidalOfModel`: the derived tensor product of `D(𝒪_X)`.

## Main results

* `AlgebraicGeometry.Space.exists_isInvertible_tensor_iso_of_model`: an identification
  `K' ≅ K ⊗^L L` on the model with `L` invertible there gives one on `D(𝒪_X)`.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The derived tensor product `⊗^L_{𝒪_X}` of `D(𝒪_X)`**: the symmetric monoidal structure of
Stacks 0FPT on the derived category of the equi-universe model of the small étale ringed site,
carried to `D(𝒪_X)` along the equivalence induced by
`AlgebraicGeometry.Space.modulesEquivModelModules`. Its unit is the structure sheaf placed in
degree zero, carried back from the model. -/
@[instance_reducible]
def derivedMonoidalOfModel :
    MonoidalCategory (@DerivedCategory (Modules.{u, u} B S hS F hF) _ _
      (HasDerivedCategory.standard _)) :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS F hF)
  letI := HasDerivedCategory.standard (ModelModules B S hS F hF)
  letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal
    (smallEtaleModelRingedSite B S hS F hF).O
  Monoidal.transport (modelDerivedEquivalence B S hS F hF).symm

/-- **An invertible twist on the model is an invertible twist on `D(𝒪_X)`.** If the transports
of `K` and `K'` to the equi-universe model satisfy `K' ≅ K ⊗^L L` with `L` invertible there, then
`K' ≅ K ⊗^L L'` in `D(𝒪_X)` with `L'` invertible for `derivedMonoidalOfModel`: `L'` is `L` carried
back. -/
theorem exists_isInvertible_tensor_iso_of_model
    (K K' : @DerivedCategory (Modules.{u, u} B S hS F hF) _ _ (HasDerivedCategory.standard _))
    (h : letI := HasDerivedCategory.standard (ModelModules B S hS F hF)
      letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal
        (smallEtaleModelRingedSite B S hS F hF).O
      ∃ L, RingedSite.InvertibleDerived.IsInvertibleObject
          (smallEtaleModelRingedSite B S hS F hF) L ∧
        Nonempty ((modelDerivedEquivalence B S hS F hF).functor.obj K' ≅
          (modelDerivedEquivalence B S hS F hF).functor.obj K ⊗ L)) :
    letI := derivedMonoidalOfModel B S hS F hF
    ∃ L, IsInvertible L ∧ Nonempty (K' ≅ K ⊗ L) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS F hF)
  let := HasDerivedCategory.standard (ModelModules B S hS F hF)
  let DM := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal
    (smallEtaleModelRingedSite B S hS F hF).O
  let E := modelDerivedEquivalence B S hS F hF
  obtain ⟨L, ⟨H⟩, ⟨e⟩⟩ := h
  let DX := derivedMonoidalOfModel B S hS F hF
  -- the tensor product and unit of `D(𝒪_X)` are those of the model, carried back
  have hunit : (𝟙_ (DerivedCategory (Modules.{u, u} B S hS F hF))) =
      E.inverse.obj (@MonoidalCategoryStruct.tensorUnit _ _ DM.toMonoidalCategoryStruct) := rfl
  let tI : ∀ {A A' : DerivedCategory (Modules.{u, u} B S hS F hF)}
      {M M' : DerivedCategory (ModelModules B S hS F hF)},
      (E.functor.obj A ≅ M) → (E.functor.obj A' ≅ M') →
        (A ⊗ A' ≅ E.inverse.obj (@MonoidalCategoryStruct.tensorObj _ _
          DM.toMonoidalCategoryStruct M M')) := fun a a' =>
    E.inverse.mapIso (@tensorIso _ _ DM _ _ _ _ a a')
  refine ⟨E.inverse.obj L, ⟨⟨E.inverse.obj H.inv, ?_, ?_⟩⟩, ⟨?_⟩⟩
  · exact tI (E.counitIso.app L) (E.counitIso.app H.inv) ≪≫ E.inverse.mapIso H.isoLeft ≪≫
      eqToIso hunit.symm
  · exact tI (E.counitIso.app H.inv) (E.counitIso.app L) ≪≫ E.inverse.mapIso H.isoRight ≪≫
      eqToIso hunit.symm
  · exact E.unitIso.app K' ≪≫ E.inverse.mapIso e ≪≫
      (tI (Iso.refl (E.functor.obj K)) (E.counitIso.app L)).symm

end AlgebraicGeometry.Space
