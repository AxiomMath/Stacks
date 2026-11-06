module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk

/-!
# Morphisms of algebraic spaces with `c_*𝒪_X = 𝒪_Y` and `R¹c_*𝒪_X = 0`

Let `c : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`. Several statements of the chapter on moduli of curves (for instance Stacks 0E88 and
Stacks 0E8A) are about morphisms for which the canonical map `𝒪_Y ⟶ c_*𝒪_X` is an isomorphism
and the first higher direct image `R¹c_*𝒪_X` vanishes. This file names that condition.

## Main definitions

* `AlgebraicGeometry.Space.IsStructureContraction`: the structure map
  `c♯ : 𝒪_Y ⟶ c_*𝒪_X` of Stacks 03G8 is an isomorphism and `R¹c_*𝒪_X = 0`, where `R¹c_*` is
  the first right derived functor of the direct image of modules on small étale sites
  (Stacks 03LU).
* `AlgebraicGeometry.Space.structureContractionBaseChange`: for morphisms `f : X ⟶ Z` and
  `g : Y ⟶ Z` and a morphism `c : X ⟶ Y` over `Z`, the morphism `X ×_Z Z' ⟶ Y ×_Z Z'` it
  induces on base changes along `h : Z' ⟶ Z`.

## Implementation notes

The direct image `c_*𝒪_X` is `AlgebraicGeometry.Space.structureRingSheafDirectImage`, and the
canonical map is the structure map `AlgebraicGeometry.Space.structureSharp` as a morphism of
sheaves of rings; it is an isomorphism exactly when the corresponding morphism of
`𝒪_Y`-modules is, the module structure of `c_*𝒪_X` being transported along it.

The first higher direct image is computed in the injective-resolution convention
`CategoryTheory.Functor.rightDerived`, at the structure sheaf
`AlgebraicGeometry.Space.structureSheafModule` of `X`, which is the convention of
`AlgebraicGeometry.Space.moduleHigherPushforwardEtaleBaseChangeIso` (Stacks 03LX).

## References

* [Stacks Project, Tag 0E88](https://stacks.math.columbia.edu/tag/0E88)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section StructureContraction

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- **`c_*𝒪_X = 𝒪_Y` and `R¹c_*𝒪_X = 0`.** For a morphism `c : X ⟶ Y` of algebraic spaces, the
structure map `c♯ : 𝒪_Y ⟶ c_*𝒪_X` of Stacks 03G8 is an isomorphism and the first higher direct
image `R¹c_*𝒪_X` of the structure sheaf vanishes. -/
def IsStructureContraction {X Y : AlgebraicSpaces B S hS} (c : X ⟶ Y) : Prop :=
  IsIso (structureSharp B S hS c) ∧
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsZero (((modulePushforward B S hS c).rightDerived 1).obj (structureSheafModule B S hS X))

end StructureContraction

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **The base change of a morphism over `Z`.** For morphisms `f : X ⟶ Z`, `g : Y ⟶ Z` and
`c : X ⟶ Y` with `c ≫ g = f`, the morphism `X ×_Z Z' ⟶ Y ×_Z Z'` induced by `c` on the fibre
products along `h : Z' ⟶ Z`. -/
def structureContractionBaseChange {X Y Z Z' : AlgebraicSpaces B S hS} {f : X ⟶ Z}
    {g : Y ⟶ Z} (c : X ⟶ Y) (hc : c ≫ g = f) (h : Z' ⟶ Z) :
    AlgebraicSpaces.fiberProduct B S hS f h ⟶ AlgebraicSpaces.fiberProduct B S hS g h :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS g h).lift
    ((ObjectProperty.homMk (pullback.fst f.hom h.hom) :
      AlgebraicSpaces.fiberProduct B S hS f h ⟶ X) ≫ c)
    (ObjectProperty.homMk (pullback.snd f.hom h.hom))
    (by
      rw [Category.assoc, hc]
      exact (AlgebraicSpaces.isPullback_fiberProduct B S hS f h).w)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- The base change of `c` followed by the projection to `Y` is the projection to `X` followed
by `c`. -/
@[reassoc (attr := simp)]
theorem structureContractionBaseChange_fst {X Y Z Z' : AlgebraicSpaces B S hS} {f : X ⟶ Z}
    {g : Y ⟶ Z} (c : X ⟶ Y) (hc : c ≫ g = f) (h : Z' ⟶ Z) :
    structureContractionBaseChange B S hS c hc h ≫
        (ObjectProperty.homMk (pullback.fst g.hom h.hom) :
          AlgebraicSpaces.fiberProduct B S hS g h ⟶ Y) =
      (ObjectProperty.homMk (pullback.fst f.hom h.hom) :
        AlgebraicSpaces.fiberProduct B S hS f h ⟶ X) ≫ c :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS g h).lift_fst _ _ _

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- The base change of `c` lies over `Z'`. -/
@[reassoc (attr := simp)]
theorem structureContractionBaseChange_snd {X Y Z Z' : AlgebraicSpaces B S hS} {f : X ⟶ Z}
    {g : Y ⟶ Z} (c : X ⟶ Y) (hc : c ≫ g = f) (h : Z' ⟶ Z) :
    structureContractionBaseChange B S hS c hc h ≫
        (ObjectProperty.homMk (pullback.snd g.hom h.hom) :
          AlgebraicSpaces.fiberProduct B S hS g h ⟶ Z') =
      (ObjectProperty.homMk (pullback.snd f.hom h.hom) :
        AlgebraicSpaces.fiberProduct B S hS f h ⟶ Z') :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS g h).lift_snd _ _ _

end AlgebraicGeometry.Space

end
