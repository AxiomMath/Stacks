module

public import StacksFrontier.AlgebraicGeometry.Modules.ZariskiRingedToposHomModules
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiPullbackSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackModulesIsoDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional

/-!
# `ε^*` commutes with derived pullback along a morphism of representable algebraic spaces

Let `g : T' ⟶ T` be a morphism of the big fppf site over `S`, with underlying morphism of
schemes `g_0 : X'_0 ⟶ X_0`, and let `f = h_g` be the morphism of representable algebraic spaces
it represents.  The square of morphisms of ringed topoi

```
  X'_étale --ε--> X'_{0,Zar}
     |f              |g_0
     v               v
  X_étale  --ε--> X_{0,Zar}
```

commutes up to the isomorphism of pullbacks of modules
`AlgebraicGeometry.Space.representedZariskiPullbackModulesCompIso`, so by Stacks 0D6D the
derived pullbacks satisfy `Lε^* ⋙ Lf^* ≅ Lg_0^* ⋙ Lε^*`, and by uniqueness of adjoints the
derived direct images satisfy `Rf_* ⋙ Rε_* ≅ Rε_* ⋙ Rg_{0,*}`.  These are the two squares of
Stacks 08GH on the unbounded derived categories, with `g_0` read as a morphism of Zariski ringed
topoi and `D(𝒪_{X_0})` at the standard model.

## Main definitions

* `AlgebraicGeometry.Space.representedZariskiPullbackModulesCompIso`: the square on pullbacks of
  modules.
* `AlgebraicGeometry.Space.representedZariskiToposDerivedPullbackCompIso`:
  `Lε_T^* ⋙ Lf^* ≅ Lg_0^* ⋙ Lε_{T'}^*`.
* `AlgebraicGeometry.Space.representedZariskiToposDerivedPushforwardCompIso`:
  `Rf_* ⋙ Rε_{T,*} ≅ Rε_{T',*} ⋙ Rg_{0,*}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {T' T : BigFppfOver B S hS}
  (g : T' ⟶ T)

/-- The composite `ε_T ∘ f : X'_étale ⟶ X_{0,Zar}`. -/
abbrev representedZariskiCompSmallEtaleHom :
    RingedToposHom (smallEtaleRingedTopos B S hS (representedSpace T'))
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos :=
  RingedToposHom.comp (X := smallEtaleRingedTopos B S hS (representedSpace T'))
    (Y := smallEtaleRingedTopos B S hS (representedSpace T))
    (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T)
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))

/-- The composite `g_0 ∘ ε_{T'} : X'_étale ⟶ X_{0,Zar}`. -/
abbrev zariskiCompRepresentedZariskiHom :
    RingedToposHom (smallEtaleRingedTopos B S hS (representedSpace T'))
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos :=
  RingedToposHom.comp (X := smallEtaleRingedTopos B S hS (representedSpace T'))
    (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
    (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
    (B.inclusion.map g.left).zariskiRingedToposHom
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T')

/-- **The square of ringed topoi of Stacks 08GH commutes on pullbacks of modules**:
`(ε_T ∘ f)^* ≅ (g_0 ∘ ε_{T'})^*`. -/
def representedZariskiPullbackModulesCompIso :
    Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS (representedSpace T'))
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
        (representedZariskiCompSmallEtaleHom B S hS g).toModulesHom ≅
      Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS (representedSpace T'))
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
        (zariskiCompRepresentedZariskiHom B S hS g).toModulesHom :=
  RingedToposHom.pullbackModulesCompIso
      (X := smallEtaleRingedTopos B S hS (representedSpace T'))
      (Y := smallEtaleRingedTopos B S hS (representedSpace T))
      (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T) ≪≫
    Functor.isoWhiskerLeft _
      (pullbackModulesIsoModulePullback B S hS (representedSpaceMap B S hS g)) ≪≫
    representedZariskiModulePullbackCompIso B S hS g ≪≫
    Functor.isoWhiskerRight
      (B.inclusion.map g.left).zariskiPullbackModulesIsoSchemeModules.symm _ ≪≫
    (RingedToposHom.pullbackModulesCompIso
      (X := smallEtaleRingedTopos B S hS (representedSpace T'))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
      (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T')
      (B.inclusion.map g.left).zariskiRingedToposHom).symm

section Derived

attribute [local instance 10000] HasDerivedCategory.standard

/-- The derived pullback along `g_0`, read as a morphism of Zariski ringed topoi, exists. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_representedSchemeMap :
    (pullbackOnHomotopy
      (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
      (B.inclusion.map g.left).zariskiRingedToposHom).HasLeftDerivedFunctor
      (quasiIsoTarget
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy
    (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
    (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
    (B.inclusion.map g.left).zariskiRingedToposHom

/-- The derived pullback along the composite `ε_T ∘ f` exists. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_representedZariskiCompSmallEtaleHom :
    (pullbackOnHomotopy (X := smallEtaleRingedTopos B S hS (representedSpace T'))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
      (representedZariskiCompSmallEtaleHom B S hS g)).HasLeftDerivedFunctor
      (quasiIsoTarget
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy
    (X := smallEtaleRingedTopos B S hS (representedSpace T'))
    (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
    (representedZariskiCompSmallEtaleHom B S hS g)

/-- The derived pullback along the composite `g_0 ∘ ε_{T'}` exists. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_zariskiCompRepresentedZariskiHom :
    (pullbackOnHomotopy (X := smallEtaleRingedTopos B S hS (representedSpace T'))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
      (zariskiCompRepresentedZariskiHom B S hS g)).HasLeftDerivedFunctor
      (quasiIsoTarget
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy
    (X := smallEtaleRingedTopos B S hS (representedSpace T'))
    (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
    (zariskiCompRepresentedZariskiHom B S hS g)

/-- The derived pullbacks along the two composites of the square agree. -/
def representedZariskiCompDerivedPullbackIso :
    derivedPullback (X := smallEtaleRingedTopos B S hS (representedSpace T'))
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
        (representedZariskiCompSmallEtaleHom B S hS g) ≅
      derivedPullback (X := smallEtaleRingedTopos B S hS (representedSpace T'))
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
        (zariskiCompRepresentedZariskiHom B S hS g) :=
  derivedPullbackIsoOfPullbackModulesIso
    (X := smallEtaleRingedTopos B S hS (representedSpace T'))
    (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
    (representedZariskiPullbackModulesCompIso B S hS g)

/-- Stacks 0D6D for `ε_T ∘ f`. -/
def representedZariskiCompSmallEtaleDerivedPullbackIso :
    representedZariskiDerivedPullback B S hS T ⋙
        smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g) ≅
      derivedPullback (X := smallEtaleRingedTopos B S hS (representedSpace T'))
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
        (representedZariskiCompSmallEtaleHom B S hS g) :=
  derivedPullbackCompIso
      (X := smallEtaleRingedTopos B S hS (representedSpace T'))
      (Y := smallEtaleRingedTopos B S hS (representedSpace T))
      (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T)

/-- Stacks 0D6D for `g_0 ∘ ε_{T'}`. -/
def zariskiCompRepresentedZariskiDerivedPullbackIso :
    derivedPullback
          (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
          (B.inclusion.map g.left).zariskiRingedToposHom ⋙
        representedZariskiDerivedPullback B S hS T' ≅
      derivedPullback (X := smallEtaleRingedTopos B S hS (representedSpace T'))
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
        (zariskiCompRepresentedZariskiHom B S hS g) :=
  derivedPullbackCompIso
      (X := smallEtaleRingedTopos B S hS (representedSpace T'))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
      (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T')
      (B.inclusion.map g.left).zariskiRingedToposHom

/-- **The first square of Stacks 08GH on unbounded derived categories, at the Zariski topos**:
`Lε_T^* ⋙ Lf^* ≅ Lg_0^* ⋙ Lε_{T'}^*`, with `g_0` read as a morphism of Zariski ringed topoi.
Both sides are derived pullbacks along the two composites of the square (Stacks 0D6D), which
agree because their pullbacks of modules do. -/
def representedZariskiToposDerivedPullbackCompIso :
    representedZariskiDerivedPullback B S hS T ⋙
        smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g) ≅
      derivedPullback
          (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
          (B.inclusion.map g.left).zariskiRingedToposHom ⋙
        representedZariskiDerivedPullback B S hS T' :=
  representedZariskiCompSmallEtaleDerivedPullbackIso B S hS g ≪≫
    representedZariskiCompDerivedPullbackIso B S hS g ≪≫
    (zariskiCompRepresentedZariskiDerivedPullbackIso B S hS g).symm

/-- **The second square of Stacks 08GH on unbounded derived categories, at the Zariski topos**:
`Rf_* ⋙ Rε_{T,*} ≅ Rε_{T',*} ⋙ Rg_{0,*}`.  The two composites are right adjoint to the two
sides of `representedZariskiToposDerivedPullbackCompIso`, so this is its conjugate. -/
def representedZariskiToposDerivedPushforwardCompIso :
    Stacks.Cohomology.DerivedPushforward.derivedPushforward
        (X := smallEtaleRingedTopos B S hS (representedSpace T'))
        (Y := smallEtaleRingedTopos B S hS (representedSpace T))
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)) ⋙
        representedZariskiDerivedPushforward B S hS T ≅
      representedZariskiDerivedPushforward B S hS T' ⋙
        Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
          (B.inclusion.map g.left).zariskiRingedToposHom :=
  conjugateIsoEquiv
    ((representedZariskiDerivedAdjunction B S hS T).comp
      (smallEtaleDerivedModuleAdjunction B S hS (representedSpaceMap B S hS g)))
    ((derivedAdjunction
        (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
        (B.inclusion.map g.left).zariskiRingedToposHom).comp
      (representedZariskiDerivedAdjunction B S hS T'))
    (representedZariskiToposDerivedPullbackCompIso B S hS g).symm

end Derived

end AlgebraicGeometry.Space
