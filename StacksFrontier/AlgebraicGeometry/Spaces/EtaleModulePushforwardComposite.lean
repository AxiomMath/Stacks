module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.MayerVietorisDegreeOne

/-!
# The direct image along an étale morphism, and the higher direct images of a composite

Let `g : U ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  The direct image of modules `g_*` is right adjoint to restriction along `g`
(`AlgebraicGeometry.Space.etaleModulePullbackAdjunction`, Stacks 03LU), and restriction is
exact; so `g_*` carries injective modules to injective modules
(`AlgebraicGeometry.Space.preservesInjectiveObjects_modulePushforward_of_isEtale`).  Consequently,
for a further morphism `f : X ⟶ Y` and an `𝒪_U`-module `𝓗` with `R^q g_*𝓗 = 0` for `q > 0`, the
relative Leray spectral sequence of Stacks 0734 for `f ∘ g` collapses:

`R^n (f ∘ g)_* 𝓗 ≅ R^n f_*(g_* 𝓗)`  for every `n`.

This is the form in which the source's proof of Stacks 0720 uses the Leray spectral sequence of
an affine étale cover `g : U ⟶ X` when `g` is affine (Stacks 073H then supplies the vanishing of
`R^q g_*`).

## Main results

* `AlgebraicGeometry.Space.rightDerivedModulePushforwardCompIsoOfIsEtale`: the collapse
  `R^n (f ∘ g)_* 𝓗 ≅ R^n f_*(g_* 𝓗)` for `g` étale and `𝓗` acyclic for `g_*`.

## Implementation notes

The module universe is the universe `u` of the structure rings, where
`AlgebraicGeometry.Space.modulePushforward` lives; enough injectives there is supplied by name,
`AlgebraicGeometry.Space.enoughInjectives_modules`, and `SheafOfModules.instAbelian` is a local
instance of raised priority, since instance search for `CategoryTheory.Abelian` on these modules
otherwise fails on the module universe.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The Leray spectral sequence of a composite with an étale morphism collapses at a module
acyclic for the étale direct image.**  Let `g : U ⟶ X` be étale, let `f : X ⟶ Y` be any morphism
of algebraic spaces and let `𝓗` be an `𝒪_U`-module with `R^q g_*𝓗 = 0` for every `q > 0`.
Then `R^n (f ∘ g)_*𝓗 ≅ R^n f_*(g_*𝓗)` for every `n`. -/
noncomputable def rightDerivedModulePushforwardCompIsoOfIsEtale
    {U X Y : AlgebraicSpaces B S hS} (g : U ⟶ X) (hg : IsEtale B S hS g.hom) (f : X ⟶ Y)
    (H : Modules.{u, u} B S hS U.1 U.2)
    (hH : have := hasInjectiveResolutions_modules B S hS U.1 U.2
      ∀ q, 0 < q → IsZero (((modulePushforward B S hS g).rightDerived q).obj H)) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS U.1 U.2
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    ((modulePushforward B S hS (g ≫ f)).rightDerived n).obj H ≅
      ((modulePushforward B S hS f).rightDerived n).obj ((modulePushforward B S hS g).obj H) :=
  have := hasInjectiveResolutions_modules B S hS U.1 U.2
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS U.1 U.2
  have := enoughInjectives_modules B S hS X.1 X.2
  have := preservesInjectiveObjects_modulePushforward_of_isEtale B S hS g hg
  (@Functor.rightDerivedIsoOfNatIso (Modules.{u, u} B S hS U.1 U.2) _ _
      (hasInjectiveResolutions_modules B S hS U.1 U.2) (Modules.{u, u} B S hS Y.1 Y.2) _ _ _ _
      (modulePushforward_additive B S hS (g ≫ f)) inferInstance
      (modulePushforwardCompIso B S hS g f).symm n).app H ≪≫
    Stacks.RightDerivedComp.objIso (modulePushforward B S hS g) (injectiveResolution H) hH
      (modulePushforward B S hS f) n

end AlgebraicGeometry.Space

end
