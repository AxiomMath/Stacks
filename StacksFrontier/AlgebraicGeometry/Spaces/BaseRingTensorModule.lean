module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSmallModel
public import StacksFrontier.CategoryTheory.Sites.Modules.BaseRingTensorInverseLimit

/-!
# The module `𝒪_X ⊗_R M` on an algebraic space

Let `X` be an algebraic space over a scheme `S` of universe `u` and let `R` be a commutative ring
with a ring map `φ` into the global functions of `X`.  For an `R`-module `M` the `𝒪_X`-module
`𝒪_X ⊗_R M` of [Stacks Project, Tag 0D3F] is the sheafification of `U ↦ 𝒪_X(U) ⊗_R M`.

`Stacks.Cohomology.SiteModules.baseRingTensorFunctor` constructs it on an arbitrary site, with
module sections in the universe `max u r w` where `u` is the universe of the objects of the site
and `r` that of the rings of sections.  On the small étale site of an algebraic space the objects
lie in `Type (u + 1)` and the rings in `Type u`, so the construction there does not land in the
`𝒪_X`-modules `AlgebraicGeometry.Space.Modules.{u, u}`.  On the `Type u`-presented model
`AlgebraicGeometry.Space.smallEtaleModelRingedTopos` of the small étale site the two universes
agree, and the Comparison Lemma `AlgebraicGeometry.Space.smallEtaleModelModulesEquiv` carries the
module constructed there back to `X`.

## Main definitions

* `AlgebraicGeometry.Space.modelGlobalFunctions`: the global functions of the model of the small
  étale site of `X`, the base-ring datum of the construction, and
  `AlgebraicGeometry.Space.modelGlobalFunctionsHom` the restriction to it of the global functions
  of `X`.
* `AlgebraicGeometry.Space.baseRingTensorModule`: **the functor `M ↦ 𝒪_X ⊗_R M`** from
  `R`-modules to `𝒪_X`-modules.
* `AlgebraicGeometry.Space.baseRingGlobalSectionsModule`: its right adjoint, global sections read
  on the model as an `R`-module.

## Main results

* `AlgebraicGeometry.Space.baseRingTensorModuleAdjunction`: `M ↦ 𝒪_X ⊗_R M` is left adjoint to
  global sections read as `R`-modules, which characterises it up to unique isomorphism.

## References

* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The ring of global functions of the model of the small étale site of `X`: the compatible
families of sections of its structure sheaf.  A ring map into it is the base-ring datum of the
module `𝒪_X ⊗_R M`. -/
abbrev modelGlobalFunctions : Type u :=
  GlobalFunctionRing (smallEtaleModelStructureSheaf B S hS X)

/-- **The global functions of `X` restrict to global functions of the model.**  A compatible
family of sections of `𝒪_X` over the objects of the small étale site is read at the objects of
the model through the comparison.  So a ring map `R →+* Γ(X, 𝒪_X)` — the datum of a morphism
`X ⟶ Spec(R)` — gives the base-ring datum of `AlgebraicGeometry.Space.baseRingTensorModule`. -/
def modelGlobalFunctionsHom :
    GlobalFunctionRing (structureSheaf B S hS X.1 X.2) →+* modelGlobalFunctions B S hS X where
  toFun s := ⟨fun V => s.1 (Opposite.op ((smallEtaleModelEquiv B S hS X).inverse.obj V.unop)),
    fun f => s.2 ((smallEtaleModelEquiv B S hS X).inverse.op.map f)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable {R : Type u} [CommRing R] (φ : R →+* modelGlobalFunctions B S hS X)

/-- **The module `𝒪_X ⊗_R M` of Stacks 0D3F on an algebraic space `X`**: the base-ring tensor
product constructed on the model of the small étale site, carried back to `X` by the Comparison
Lemma. -/
def baseRingTensorModule : ModuleCat.{u} R ⥤ Modules.{u, u} B S hS X.1 X.2 :=
  baseRingTensorFunctor.{u, u, u, u} φ ⋙ (smallEtaleModelModulesEquiv B S hS X).inverse

/-- Global sections of an `𝒪_X`-module read as an `R`-module: restrict to the model, take the
compatible families of sections there, and restrict scalars along `φ`. -/
def baseRingGlobalSectionsModule : Modules.{u, u} B S hS X.1 X.2 ⥤ ModuleCat.{u} R :=
  (smallEtaleModelModulesEquiv B S hS X).functor ⋙ baseRingGlobalSectionsFunctor.{u, u, u, u} φ

/-- **The mapping property of `𝒪_X ⊗_R M`**, Tag 01BH for a base ring: morphisms of
`𝒪_X`-modules `𝒪_X ⊗_R M ⟶ F` are the `R`-linear maps from `M` to the global sections of `F`.
It is the adjunction of the base-ring tensor product on the model composed with the Comparison
Lemma. -/
def baseRingTensorModuleAdjunction :
    baseRingTensorModule B S hS X φ ⊣ baseRingGlobalSectionsModule B S hS X φ :=
  (baseRingTensorAdjunction.{u, u, u, u} φ).comp
    (smallEtaleModelModulesEquiv B S hS X).symm.toAdjunction

end AlgebraicGeometry.Space

end
