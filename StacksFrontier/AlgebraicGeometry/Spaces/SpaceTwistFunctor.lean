module

public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleModuleTriviality
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveTwistHigherDirectImageVanishing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorUnitSmul
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear

/-!
# Twisting by the powers of an invertible module, as functors

For an invertible `𝒪_X`-module `ℒ` on an algebraic space `X`, the twists `M ↦ M ⊗ ℒ^{⊗ d}` as
endofunctors of the `𝒪_X`-modules: iterates of `− ⊗ ℒ`.  Each is an equivalence (Stacks 01CS), so
exact, and each commutes with multiplication by global functions.  On objects the `d`-th iterate
is `M ⊗ AlgebraicGeometry.Space.tensorPow ℒ d`, the twist of the statement of Stacks 0D39.

## Main definitions

* `AlgebraicGeometry.Space.modulesTensorRightFunctor`: `− ⊗ ℒ`.
* `AlgebraicGeometry.Space.twistPowFunctor`: its `d`-th iterate.
* `AlgebraicGeometry.Space.twistPowFunctorObjIso`: `(− ⊗ ℒ)^{∘ d} M ≅ M ⊗ ℒ^{⊗ d}`.

## Main results

* `AlgebraicGeometry.Space.twistPowLinear`: the twists commute with
  multiplication by global functions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules (globalSmul)

universe u

namespace AlgebraicGeometry.Space


variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- **Twisting by `ℒ`**, `M ↦ M ⊗ ℒ`, in the spelling of the tensor bifunctor. -/
def modulesTensorRightFunctor (L : Modules.{u, u} B S hS X.1 X.2) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS X.1 X.2 :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (structureSheaf B S hS X.1 X.2)).flip.obj L

/-- The `d`-th iterate of twisting by `ℒ`. -/
def twistPowFunctor (L : Modules.{u, u} B S hS X.1 X.2) :
    ℕ → (Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS X.1 X.2)
  | 0 => 𝟭 _
  | d + 1 => twistPowFunctor L d ⋙ modulesTensorRightFunctor L

variable (L : Modules.{u, u} B S hS X.1 X.2)

/-- An endofunctor of the `𝒪_X`-modules which commutes with multiplication by global functions,
bundled with that commutation. -/
structure GlobalLinearEndofunctor (X : AlgebraicSpaces B S hS) where
  /-- The functor. -/
  functor : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS X.1 X.2
  /-- It commutes with multiplication by global functions. -/
  map_globalSmul : ∀ (a : RingCat.sectionsSubring
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj) (M : Modules.{u, u} B S hS X.1 X.2),
    functor.map (globalSmul _ a M) = globalSmul _ a (functor.obj M)

/-- Twisting `M` by `ℒ` is the tensor product `M ⊗ ℒ`. -/
theorem modulesTensorRightFunctor_obj (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulesTensorRightFunctor L).obj M =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS X.1 X.2)).obj M).obj L :=
  rfl

/-- On objects, the `(d + 1)`-st iterated twist is the twist by `ℒ` of the `d`-th. -/
theorem twistPowFunctor_obj_succ (M : Modules.{u, u} B S hS X.1 X.2) (d : ℕ) :
    (twistPowFunctor L (d + 1)).obj M =
      (modulesTensorRightFunctor L).obj ((twistPowFunctor L d).obj M) :=
  rfl

/-- On morphisms, the `(d + 1)`-st iterated twist is the twist by `ℒ` of the `d`-th. -/
theorem twistPowFunctor_map_succ {M N : Modules.{u, u} B S hS X.1 X.2} (g : M ⟶ N) (d : ℕ) :
    (twistPowFunctor L (d + 1)).map g =
      (modulesTensorRightFunctor L).map ((twistPowFunctor L d).map g) :=
  rfl

/-- **The iterated twist, as a functor commuting with global functions.** The functor
`twistPowFunctor L d`, bundled with the fact that it commutes with multiplication by global
sections: twisting commutes with multiplication by a global section
(`AlgebraicGeometry.SheafOfModules.sheafTensorRight_map_globalSectionToEnd`). -/
def twistPowLinear (d : ℕ) : GlobalLinearEndofunctor (X := X) where
  functor := twistPowFunctor L d
  map_globalSmul a M := by
    induction d with
    | zero => rfl
    | succ d ih =>
      change (modulesTensorRightFunctor L).map ((twistPowFunctor L d).map (globalSmul _ a M)) = _
      rw [ih]
      exact AlgebraicGeometry.SheafOfModules.sheafTensorRight_map_globalSectionToEnd.{u, u + 1, u}
        (smallEtaleRingedSite B S hS X.1 X.2).O L ⟨a.1, a.2⟩ _

variable [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
  (structureRingPresheaf_isSheaf B S hS X.1 X.2) L]

/-- For invertible `ℒ`, twisting by `ℒ` is an equivalence. -/
instance isEquivalence_modulesTensorRightFunctor : (modulesTensorRightFunctor L).IsEquivalence :=
  isEquivalence_tensorRightFunctor B S hS X.1 X.2 L

/-- For invertible `ℒ`, every iterated twist by `ℒ` is an equivalence. -/
instance isEquivalence_twistPowFunctor : ∀ d, (twistPowFunctor L d).IsEquivalence
  | 0 => inferInstanceAs (𝟭 _).IsEquivalence
  | d + 1 => by
    have := isEquivalence_twistPowFunctor d
    exact inferInstanceAs (twistPowFunctor L d ⋙ modulesTensorRightFunctor L).IsEquivalence

attribute [local instance] modulesMonoidalCategory

omit [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
  (structureRingPresheaf_isSheaf B S hS X.1 X.2) L] in
/-- `ℒ^{⊗ (d + 2)} = ℒ^{⊗ (d + 1)} ⊗ ℒ`. -/
theorem tensorPow_add_two (d : ℕ) :
    tensorPow B S hS L (d + 2) = tensorPow B S hS L (d + 1) ⊗ L :=
  rfl

omit [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
  (structureRingPresheaf_isSheaf B S hS X.1 X.2) L] in
/-- On objects, the `(d + 1)`-st iterated twist of `M` is the tensor product of the `d`-th
iterated twist of `M` with `ℒ`. -/
theorem twistPowFunctor_succ_obj (M : Modules.{u, u} B S hS X.1 X.2) (d : ℕ) :
    (twistPowFunctor L (d + 1)).obj M =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS X.1 X.2)).obj ((twistPowFunctor L d).obj M)).obj L :=
  rfl

/-- One step of `AlgebraicGeometry.Space.twistPowFunctorObjIso`. -/
def twistPowFunctorObjIsoStep (M : Modules.{u, u} B S hS X.1 X.2) (d : ℕ)
    (e : (twistPowFunctor L (d + 1)).obj M ≅ M ⊗ tensorPow B S hS L (d + 1)) :
    (twistPowFunctor L (d + 2)).obj M ≅ M ⊗ (tensorPow B S hS L (d + 1) ⊗ L) :=
  eqToIso (twistPowFunctor_succ_obj L M (d + 1)) ≪≫
    (modulesTensorObjIso B S hS X.1 X.2 ((twistPowFunctor L (d + 1)).obj M) L).symm ≪≫
    whiskerRightIso e L ≪≫ α_ M (tensorPow B S hS L (d + 1)) L

/-- **The `d`-th iterated twist is the tensor product with `ℒ^{⊗ d}`.** -/
def twistPowFunctorObjIso (M : Modules.{u, u} B S hS X.1 X.2) :
    ∀ d, (twistPowFunctor L d).obj M ≅ M ⊗ tensorPow B S hS L d
  | 0 => (ρ_ M).symm
  | 1 => eqToIso (twistPowFunctor_succ_obj L M 0) ≪≫ (modulesTensorObjIso B S hS X.1 X.2 M L).symm
  | d + 2 => twistPowFunctorObjIsoStep L M d (twistPowFunctorObjIso M (d + 1))

end AlgebraicGeometry.Space

end
