module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleEtaleBaseChangeHFace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleEtaleBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleBaseChangeComparison
public import StacksFrontier.CategoryTheory.Adjunction.MateConjugateEquivalence

/-!
# Étale base change for the derived direct image on algebraic spaces

For a cartesian square of algebraic spaces
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
with `g` étale and representable (for instance the inclusion of an étale chart), the base change
map `g^* f_* ⟶ f'_* (g')^*` of modules, built from the étale adjunctions of Stacks 03LU, is
invertible: on underlying sheaves of sets it is the base change map of sheaves of sets, which is
Stacks 03LR, part (1).  Consequently the canonical base change map
`Lg^* Rf_* K ⟶ Rf'_* L(g')^* K` of the derived categories of the small étale ringed topoi is
invertible for every `K`, with no hypothesis on `f`.

## Main results

* `AlgebraicGeometry.Space.isIso_etaleModuleBaseChangeMate`
* `AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_of_isEtale`
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeMap_of_isEtale`
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- **The base change map of modules across the étale adjunctions of Stacks 03LU is invertible**
for a cartesian square whose bottom arrow is étale and representable. -/
theorem isIso_etaleModuleBaseChangeMate (sq : IsPullback g' f' f g) (hg : IsEtale B S hS g.hom)
    (hrep : yoneda.relativelyRepresentable g.hom) :
    IsIso ((mateEquiv (etaleModulePullbackAdjunction B S hS g'
          (isEtale_of_isPullback B S hS f' g' g f sq.flip hg))
        (etaleModulePullbackAdjunction B S hS g hg)).symm
      (TwoSquare.mk _ _ _ _ ((modulePushforwardCompIso B S hS g' f).hom ≫
        eqToHom (congrArg (fun k : X' ⟶ Y => modulePushforward B S hS k) sq.w) ≫
        (modulePushforwardCompIso B S hS f' g).inv))).natTrans :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun K =>
    Stacks.Sheaves.PushforwardEssentialImage.isIso_of_isIso_moduleSheafFunctor_map
      (R := structureRingSheaf B S hS Y') _
      (isIso_moduleSheafFunctor_map_etaleModuleBaseChangeMate_app B S hS g' f' f g sq hg hrep K)

/-- **Étale base change for the derived direct image**: for a cartesian square of algebraic
spaces whose bottom arrow `g` is étale and representable, the canonical base change map
`Lg^* Rf_* K ⟶ Rf'_* L(g')^* K` is an isomorphism for every object `K` of `D(𝒪_X)`. -/
theorem isIso_smallEtaleDerivedBaseChangeMap_of_isEtale (sq : IsPullback g' f' f g)
    (hg : IsEtale B S hS g.hom) (_hrep : yoneda.relativelyRepresentable g.hom)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w K) :=
  isIso_smallEtaleDerivedBaseChangeMap_of_isIso_underived B S hS f g f' g' sq.w hg
    (isEtale_of_isPullback B S hS f' g' g f sq.flip hg)
    (isIso_smallEtaleUnderivedBaseChangeMap_of_isIso B S hS f g f' g' sq.w
      (isIso_smallEtaleModuleBaseChangeMap_of_isIso_moduleBaseChangeMap B S hS f g f' g' sq.w
        (isIso_moduleBaseChangeMap_of_isEtale B S hS g' f' f g sq hg))) K

end AlgebraicGeometry.Space

end
