module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor

/-!
# Derived direct image and the derived internal Hom of algebraic spaces

Let `g : X' ⟶ X` be a morphism of algebraic spaces and `M ∈ D(𝒪_X)`. Then

`Rg_* R𝓗om(Lg^*M, L) ≅ R𝓗om(M, Rg_*L)`

naturally in `L ∈ D(𝒪_{X'})`. Both sides are right adjoints: the left one of
`T ↦ Lg^*T ⊗^L Lg^*M` (Stacks 07A6 and Stacks 08J8 on `X'`), the right one of
`T ↦ Lg^*(T ⊗^L M)` (Stacks 08J8 on `X` and Stacks 07A6), and the two left adjoints are
identified by Stacks 07A4. The isomorphism is the conjugate of that identification.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackTensorRightIso`: `Lg^*(- ⊗^L M) ≅
  Lg^*(-) ⊗^L Lg^*M`, Stacks 07A4 in the first variable.
* `AlgebraicGeometry.Space.derivedModulePushforwardSheafHomIso`:
  `Rg_* R𝓗om(Lg^*M, -) ≅ R𝓗om(M, Rg_* -)`.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X X' : AlgebraicSpaces B S hS}

/-- **Stacks 07A4 in the first variable**: `Lg^*(T ⊗^L M) ≅ Lg^*T ⊗^L Lg^*M`, naturally in `T`,
read off the bifunctorial isomorphism `smallEtaleDerivedPullbackTensorIso`. -/
def smallEtaleDerivedPullbackTensorRightIso (g : X' ⟶ X)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedTensor B S hS X).flip.obj M ⋙ smallEtaleDerivedModulePullback B S hS g ≅
      smallEtaleDerivedModulePullback B S hS g ⋙
        (smallEtaleDerivedTensor B S hS X').flip.obj
          ((smallEtaleDerivedModulePullback B S hS g).obj M) :=
  NatIso.ofComponents
    (fun T => (smallEtaleDerivedPullbackTensorIso g).app (T, M)) fun {T T'} t => by
    have h := (smallEtaleDerivedPullbackTensorIso g).hom.naturality (X := (T, M)) (Y := (T', M))
      (t, 𝟙 M)
    simp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map, Functor.prod_obj,
      CategoryTheory.Functor.map_id, Category.comp_id] at h
    simp only [Functor.comp_map, Functor.flip_obj_map]
    exact h

/-- **`Rg_* R𝓗om(Lg^*M, -) ≅ R𝓗om(M, Rg_* -)`** for a morphism `g : X' ⟶ X` of algebraic
spaces: the conjugate, along the composite adjunctions
`Lg^* ⋙ (- ⊗^L Lg^*M) ⊣ R𝓗om(Lg^*M, -) ⋙ Rg_*` and `(- ⊗^L M) ⋙ Lg^* ⊣ Rg_* ⋙ R𝓗om(M, -)`,
of the isomorphism of left adjoints of Stacks 07A4. -/
def derivedModulePushforwardSheafHomIso (g : X' ⟶ X)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedSheafHom B S hS X').obj
        (op ((smallEtaleDerivedModulePullback B S hS g).obj M)) ⋙
        derivedPushforward (X := smallEtaleRingedTopos B S hS X')
          (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g) ≅
      derivedPushforward (X := smallEtaleRingedTopos B S hS X')
          (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g) ⋙
        (smallEtaleDerivedSheafHom B S hS X).obj (op M) :=
  (conjugateIsoEquiv
    ((smallEtaleDerivedModuleAdjunction B S hS g).comp
      (smallEtaleDerivedTensorSheafHomAdjunction B S hS X'
        ((smallEtaleDerivedModulePullback B S hS g).obj M)))
    ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X M).comp
      (smallEtaleDerivedModuleAdjunction B S hS g))
    (smallEtaleDerivedPullbackTensorRightIso g M))

end AlgebraicGeometry.Space

end
