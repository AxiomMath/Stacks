module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangePseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedPullbackSheafHomMap

/-!
# Cohomology and base change for the derived internal Hom

Let `f : X ⟶ Y` be a morphism of finite presentation of algebraic spaces, `E` a perfect object
of `D(𝒪_X)` and `𝒢^•` a bounded complex of `𝒪_X`-modules of finite presentation, flat over `Y`,
with support proper over `Y`. Since `R𝓗om(E, 𝒢^•) ≅ E^∨ ⊗^L 𝒢^•` with `E^∨` perfect (Stacks
08JJ), perfectness of `Rf_*R𝓗om(E, 𝒢^•)` (Stacks 0A1R) follows from Stacks 0A1P for `E^∨`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackQComparison`: the comparison
  `Lg^*𝒢^• ⟶ g^*𝒢^•` from the derived to the degreewise pullback of a complex.
* `AlgebraicGeometry.Space.smallEtaleDerivedSheafHomBaseChangeMap`: the base change map of
  Stacks 08JQ, `Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)`.

## Main results

* `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_derivedSheafHom_of_perfectness`
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackSheafHomMap_eq_homEquiv_counit`: the map of
  Stacks 08JF of the base, as the adjoint of the comparison of Stacks 07A4 followed by the derived
  pullback of the evaluation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **`Rf_*R𝓗om(E, 𝒢^•)` is perfect when `Rf_*(E^∨ ⊗^L 𝒢^•)` is**, for `E` perfect: the two are
isomorphic by Stacks 08JJ. With Stacks 0A1P for `E^∨` this is the perfectness part of Stacks
0A1R. -/
theorem isPerfect_derivedModulePushforward_derivedSheafHom_of_perfectness
    (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (h0A1P : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj
          (DerivedCategory.Q.obj G)))) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj (DerivedCategory.Q.obj G))) :=
  RingedSite.IsPerfect.of_iso _ h0A1P ((derivedModulePushforward B S hS f).mapIso
    (smallEtaleDerivedSheafHomIsoTensorDual B S hS X E (DerivedCategory.Q.obj G) hE).symm)

section BaseChange

variable {X' Y' : AlgebraicSpaces B S hS}

/-- **The map of Stacks 08JF for a morphism of algebraic spaces**,
`Lg^*R𝓗om(E, K) ⟶ R𝓗om(Lg^*E, Lg^*K)`
(`AlgebraicGeometry.Space.smallEtaleDerivedPullbackSheafHomMap`), is adjoint, under Stacks 08J8
on the source, to `Lg^*R𝓗om(E, K) ⊗^L Lg^*E ≅ Lg^*(R𝓗om(E, K) ⊗^L E) ⟶ Lg^*K`, the inverse of
the isomorphism of Stacks 07A4 followed by `Lg^*` of the evaluation map. -/
theorem smallEtaleDerivedPullbackSheafHomMap_eq_homEquiv_counit (g : X' ⟶ X)
    (E K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    smallEtaleDerivedPullbackSheafHomMap g E K =
      ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X'
          ((smallEtaleDerivedModulePullback B S hS g).obj E)).homEquiv
        ((smallEtaleDerivedModulePullback B S hS g).obj
          (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj K))
        ((smallEtaleDerivedModulePullback B S hS g).obj K))
        ((smallEtaleDerivedPullbackTensorIso g).inv.app
            (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj K, E) ≫
          (smallEtaleDerivedModulePullback B S hS g).map
            ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X E).counit.app K)) := by
  apply (smallEtaleTensorHomEquiv B S hS X' _ _ _).injective
  rw [smallEtaleTensorHomEquiv_smallEtaleDerivedPullbackSheafHomMap]
  dsimp only [smallEtaleTensorHomEquiv]
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  simp

/-- **The comparison from the derived to the degreewise pullback of a complex**,
`Lg^*𝒢^• ⟶ g^*𝒢^•`, with the degreewise pullback that of the morphism of small étale ringed
topoi: the canonical map of the left derived functor `Lg^*` at `𝒢^•`. -/
def smallEtaleDerivedPullbackQComparison (g : X' ⟶ X)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (smallEtaleDerivedModulePullback B S hS g).obj (DerivedCategory.Q.obj G) ⟶
      DerivedCategory.Q.obj
        (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposHom B S hS g).toModulesHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G) :=
  (smallEtaleDerivedModulePullback B S hS g).map
      ((DerivedCategory.quotientCompQhIso _).inv.app G) ≫
    (smallEtaleDerivedModulePullbackComparison B S hS g).app
      ((HomotopyCategory.quotient _ _).obj G) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app _

/-- **The comparison from the derived to the degreewise pullback of a complex**,
`Lg^*𝒢^• ⟶ g^*𝒢^•`: the canonical map of the left derived functor `Lg^*` at `𝒢^•`, followed by
the identification of the degreewise pullback of the morphism of small étale ringed topoi with
`AlgebraicGeometry.Space.modulePullback`. -/
def smallEtaleDerivedModulePullbackQComparison (g : X' ⟶ X)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (smallEtaleDerivedModulePullback B S hS g).obj (DerivedCategory.Q.obj G) ⟶
      DerivedCategory.Q.obj
        (((modulePullback B S hS g).mapHomologicalComplex (ComplexShape.up ℤ)).obj G) :=
  let F := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
    (smallEtaleRingedToposHom B S hS g).toModulesHom
  let G' : type_of% F := modulePullback B S hS g
  haveI : G'.Additive := modulePullback_additive g
  smallEtaleDerivedPullbackQComparison g G ≫
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (F := F) (G := G')
      (pullbackModulesIsoModulePullback B S hS g) (ComplexShape.up ℤ)).hom.app G)

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- **The base change map of Stacks 08JQ**,
`Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)`: the base change map of Stacks 07A7 at
`R𝓗om(E, 𝒢^•)` followed by `Rf'_*` of the map of Stacks 08JF and of the comparison
`L(g')^*𝒢^• ⟶ (g')^*𝒢^•` (the composite of Stacks 0DKH and 0DKI (2)). The pullback of `𝒢^•` on
the right is not derived. -/
def smallEtaleDerivedSheafHomBaseChangeMap (w : g' ≫ f = f' ≫ g)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (smallEtaleDerivedModulePullback B S hS g).obj ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj (DerivedCategory.Q.obj G))) ⟶
      (derivedModulePushforward B S hS f').obj
        (((smallEtaleDerivedSheafHom B S hS X').obj
          (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).obj
          (DerivedCategory.Q.obj
            (((modulePullback B S hS g').mapHomologicalComplex (ComplexShape.up ℤ)).obj G))) :=
  smallEtaleDerivedBaseChangeComp B S hS f g f' g' w _ _
    (smallEtaleDerivedPullbackSheafHomMap g' E (DerivedCategory.Q.obj G) ≫
      ((smallEtaleDerivedSheafHom B S hS X').obj
        (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).map
        (smallEtaleDerivedModulePullbackQComparison g' G))

end BaseChange

end AlgebraicGeometry.Space

end
