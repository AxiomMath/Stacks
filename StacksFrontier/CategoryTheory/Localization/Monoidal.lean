module

public import Mathlib.CategoryTheory.Localization.Monoidal.Braided

/-!
# Monoidal structures on a localization

Let `L : C ⥤ D` be a localization functor for a monoidal morphism property `W` of a monoidal
category `C`, and let `L.obj (𝟙_ C) ≅ u` for an object `u` of `D`. This file equips `D` itself
with the monoidal structure for which `L` is monoidal with unit `u`, together with the braided
and symmetric structures induced from those of `C`.

## Main definitions

* `CategoryTheory.Localization.monoidalCategoryStruct`: the tensor product, unit, associator and
  unitors on `D` induced by `L`.
* `CategoryTheory.Localization.monoidalCategory`: the monoidal category structure on `D`.
* `CategoryTheory.Localization.coreMonoidal`: the monoidal structure on the functor `L`.
* `CategoryTheory.Localization.braidedCategory`: the braiding on `D` induced by a braiding on `C`.
* `CategoryTheory.Localization.symmetricCategory`: the symmetric structure on `D` induced by a
  symmetric structure on `C`.

## Implementation notes

The tensor, unitors, associator and their coherence come from the canonical localization
construction. They are assembled directly on `D`, without an instance cast from its
`LocalizedMonoidal` synonym, and are definitions rather than instances. The ordinary definitions
`monoidalCategoryStruct` and `coreMonoidal` keep the computational data exposed when specialized
to large concrete categories. The same construction supplies braided and symmetric structures
without another tensor product.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Localization

open MonoidalCategory

variable {Source Target : Type*} [Category Source] [Category Target] [MonoidalCategory Source]
  (localizingFunctor : Source ⥤ Target) (localIsomorphisms : MorphismProperty Source)
  [monoidalLocalIsomorphisms : localIsomorphisms.IsMonoidal]
  [localizingFunctor.IsLocalization localIsomorphisms]
  {unit : Target} (unitIso : localizingFunctor.obj (𝟙_ Source) ≅ unit)

/-- The tensor product, tensor unit, associator and unitors on the target of a localization
`localizingFunctor` for a monoidal morphism property, with tensor unit `unit`, induced by the
monoidal structure of the source. -/
@[instance_reducible]
def monoidalCategoryStruct : MonoidalCategoryStruct Target where
  tensorObj leftObject rightObject :=
    ((Monoidal.tensorBifunctor localizingFunctor localIsomorphisms unitIso).obj leftObject).obj
      rightObject
  whiskerLeft leftObject _ _ rightMap :=
    ((Monoidal.tensorBifunctor localizingFunctor localIsomorphisms unitIso).obj leftObject).map
      rightMap
  whiskerRight leftMap rightObject :=
    ((Monoidal.tensorBifunctor localizingFunctor localIsomorphisms unitIso).map leftMap).app
      rightObject
  tensorUnit := unit
  associator leftObject middleObject rightObject :=
    (((Monoidal.associator localizingFunctor localIsomorphisms unitIso).app leftObject).app
      middleObject).app rightObject
  leftUnitor object := (Monoidal.leftUnitor localizingFunctor localIsomorphisms unitIso).app object
  rightUnitor object :=
    (Monoidal.rightUnitor localizingFunctor localIsomorphisms unitIso).app object

/-- The monoidal category structure on the target of a localization `localizingFunctor` for a
monoidal morphism property, with tensor unit `unit`, induced by the monoidal structure of the
source. -/
@[instance_reducible]
def monoidalCategory : MonoidalCategory Target where
  toMonoidalCategoryStruct := monoidalCategoryStruct localizingFunctor localIsomorphisms unitIso
  tensorHom_def _ _ := rfl
  id_tensorHom_id := Monoidal.id_tensorHom_id localizingFunctor localIsomorphisms unitIso
  tensorHom_comp_tensorHom leftMap rightMap nextLeftMap nextRightMap :=
    (Monoidal.tensor_comp localizingFunctor localIsomorphisms unitIso
      leftMap rightMap nextLeftMap nextRightMap).symm
  whiskerLeft_id := Monoidal.whiskerLeft_id localizingFunctor localIsomorphisms unitIso
  id_whiskerRight := Monoidal.whiskerRight_id localizingFunctor localIsomorphisms unitIso
  associator_naturality :=
    Monoidal.associator_naturality localizingFunctor localIsomorphisms unitIso
  leftUnitor_naturality :=
    Monoidal.leftUnitor_naturality localizingFunctor localIsomorphisms unitIso
  rightUnitor_naturality :=
    Monoidal.rightUnitor_naturality localizingFunctor localIsomorphisms unitIso
  pentagon := Monoidal.pentagon (L := localizingFunctor) (W := localIsomorphisms) (ε := unitIso)
  triangle := Monoidal.triangle (L := localizingFunctor) (W := localIsomorphisms) (ε := unitIso)

/-- The localization functor `localizingFunctor` is monoidal for the monoidal structure
`monoidalCategory` on its target, with unit isomorphism given by `unitIso`. -/
def coreMonoidal :
    letI := monoidalCategory localizingFunctor localIsomorphisms unitIso
    localizingFunctor.CoreMonoidal :=
  letI := monoidalCategory localizingFunctor localIsomorphisms unitIso
  { εIso := unitIso.symm
    μIso := Monoidal.μ localizingFunctor localIsomorphisms unitIso
    μIso_hom_natural_left := Monoidal.μ_natural_left localizingFunctor localIsomorphisms unitIso
    μIso_hom_natural_right leftObject rightMap :=
      Monoidal.μ_natural_right localizingFunctor localIsomorphisms unitIso leftObject rightMap
    associativity leftObject middleObject rightObject :=
      Functor.LaxMonoidal.associativity
        (Monoidal.toMonoidalCategory localizingFunctor localIsomorphisms unitIso)
        leftObject middleObject rightObject
    left_unitality := Monoidal.leftUnitor_hom_app localizingFunctor localIsomorphisms unitIso
    right_unitality := Monoidal.rightUnitor_hom_app localizingFunctor localIsomorphisms unitIso }

/-- A braiding on the source induces a braiding on the target of the localization for the
monoidal structure `monoidalCategory`. -/
@[instance_reducible]
def braidedCategory [sourceBraided : BraidedCategory Source] :
    letI := monoidalCategory localizingFunctor localIsomorphisms unitIso
    BraidedCategory Target := by
  letI := monoidalCategory localizingFunctor localIsomorphisms unitIso
  refine .ofBifunctor (Monoidal.braidingNatIso localizingFunctor localIsomorphisms unitIso) ?_ ?_
  · apply natTrans₃_ext localizingFunctor localizingFunctor localizingFunctor
      localIsomorphisms localIsomorphisms localIsomorphisms
    simpa using! Monoidal.map_hexagon_forward localizingFunctor localIsomorphisms unitIso
  · apply natTrans₃_ext localizingFunctor localizingFunctor localizingFunctor
      localIsomorphisms localIsomorphisms localIsomorphisms
    simpa using! Monoidal.map_hexagon_reverse localizingFunctor localIsomorphisms unitIso

/-- A symmetric monoidal structure on the source induces a symmetric monoidal structure on the
target of the localization, extending `braidedCategory`. -/
@[instance_reducible]
def symmetricCategory [sourceSymmetric : SymmetricCategory Source] :
    letI := monoidalCategory localizingFunctor localIsomorphisms unitIso
    SymmetricCategory Target :=
  letI := monoidalCategory localizingFunctor localIsomorphisms unitIso
  { toBraidedCategory := braidedCategory localizingFunctor localIsomorphisms unitIso
    symmetry leftObject rightObject := SymmetricCategory.symmetry
      (C := LocalizedMonoidal localizingFunctor localIsomorphisms unitIso) leftObject rightObject }

end CategoryTheory.Localization

end
