module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.DerivedSectionsOfAPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.DerivedGlobalSections
public import StacksFrontier.Topology.Sheaves.Cohomology.RecoveryA.DerivedDirectImageComposition
public import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of derived global sections along an `f`-map

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, let `𝒢` be an `𝒪_Y`-module and
let `ℱ` be an `𝒪_X`-module.  An `f`-map from `𝒢` to `ℱ` is a morphism `φ : 𝒢 ⟶ f_* ℱ`, or
equivalently a morphism `f^* 𝒢 ⟶ ℱ`.  [Stacks, Tag 01F9] is the arrow

```
φ : RΓ(Y, 𝒢) ⟶ RΓ(X, ℱ)
```

of `D⁺(Γ(Y, 𝒪_Y))` that such a datum induces, the target being the derived global sections on
`X` with scalars restricted along `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`.  It is constructed as the
composite of the morphism `𝒢[0] ⟶ Rf_* (ℱ[0])` of [Stacks, Tag 01F8], followed
by `RΓ(Y, -)`, followed by the identification `RΓ(Y, Rf_* ℱ) ≅ RΓ(X, ℱ)` of
[Stacks, Tag 01EZ].

## Main definitions

* `Stacks.Cohomology.singleRightDerivedUnit` is the canonical transformation
  `Φ(-)[0] ⟶ RΦ((-)[0])` attached to an additive functor `Φ`, that is, the unit of its
  bounded-below right derived functor read on complexes concentrated in degree `0`.
* `Stacks.Cohomology.toDerivedPushforward` is the morphism `𝒢[0] ⟶ Rf_*(ℱ[0])` of
  [Stacks, Tag 01F8] attached to an `f`-map `φ : 𝒢 ⟶ f_* ℱ`.
* `Stacks.Cohomology.derivedGlobalSectionsComparison` is the identification
  `RΓ(X, -) ≅ RΓ(Y, Rf_*(-))`.
* `Stacks.Cohomology.derivedGlobalSectionsMap` is the arrow of [Stacks, Tag 01F9], and
  `Stacks.Cohomology.derivedGlobalSectionsMapOfPullback` is the same arrow for an `f`-map
  presented in its adjoint form `f^* 𝒢 ⟶ ℱ`.

## Main results

* `Stacks.Cohomology.isIso_singleRightDerivedUnit_app`: the canonical map
  `Φ(I)[0] ⟶ RΦ(I[0])` is invertible for an injective object `I`.
* `Stacks.Cohomology.derivedGlobalSectionsMap_comp_left` and
  `Stacks.Cohomology.derivedGlobalSectionsMap_comp_right`: the arrow is functorial in the
  triple `(𝒢, ℱ, φ)`, which is the functoriality clause of the source.
* `Stacks.Cohomology.isIso_derivedGlobalSectionsMap`: the arrow attached to an invertible
  `f`-map into an injective module is itself invertible.

## Implementation notes

The target of the arrow is `Stacks.Cohomology.derivedModuleGlobalSectionsAlong f`, the
bounded-below right derived functor of `Γ(X, -)` followed by restriction of scalars along
`Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`.  The composite of underived functors
`f_* ⋙ Γ(Y, -)` and `Γ(X, -) ⋙ restrictScalars` are *equal*, not merely isomorphic: the
preimage `f^{-1}(⊤)` is `⊤` and the structure map `f^♯` at `⊤` is the map on global sections, so
no comparison functor appears here and
`Stacks.Cohomology.derivedGlobalSectionsComparison` is literally the canonical map of
[Stacks, Tag 015M] for the composition `Γ(Y, -) ∘ f_*`.  Its invertibility is the acyclicity
input [Stacks, Tag 01EX] part (2), in the packaging
`Stacks.Cohomology.DerivedPushforwardSections.rightAcyclic_modulePushforward_obj`.

The transformation `singleRightDerivedUnit` is assembled by whiskering from the two coherence
isomorphisms `CategoryTheory.Functor.mapSingleFunctorCompQhIso` (an additive functor carries
`M[0]` to `Φ(M)[0]`) and `CategoryTheory.Functor.singleFunctorPlusIsoCompQh` (the single functor
into `D⁺` factors through `K⁺`), so its naturality is formal.

Everything is stated for `RingedSpace.{u, u}` and `SheafOfModules.{u}`, the universe constraint
imposed by Mathlib's adjunction for the pushforward of presheaves of modules, and the spelling
`Stacks.Cohomology.Modules` of `StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors` agrees
on the nose with the `SheafOfModules.{u} (structureSheafRing X)` of
`StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace`.

## References

* [Stacks Project, Tag 01F9](https://stacks.math.columbia.edu/tag/01F9)
* [Stacks Project, Tag 01F8](https://stacks.math.columbia.edu/tag/01F8)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedPushforwardSections

universe u

namespace Stacks.Cohomology

attribute [local instance] HasDerivedCategory.standard

-- As in
-- `StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.DerivedSectionsOfAPushforward`:
-- this file mentions `Functor.rightDerivedFunctorPlus`
-- throughout, so the cheap instance that gets pointwise right derivability from
-- `EnoughInjectives` is given precedence over the one that would embark on proving termwise
-- injectivity of an unknown complex.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Sheaves of modules on a ringed space form an abelian category. -/
noncomputable local instance abelianModules (X : RingedSpace.{u, u}) :
    Abelian (Modules X) := inferInstance

/-- Sheaves of modules on a ringed space have enough injectives. -/
local instance enoughInjectivesModules (X : RingedSpace.{u, u}) :
    EnoughInjectives (Modules X) :=
  IsGrothendieckAbelian.enoughInjectives

/-! ### The unit of a bounded-below right derived functor on complexes in degree zero -/

section Unit

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (Φ : A ⥤ B) [Φ.Additive] [EnoughInjectives A]

/-- The canonical transformation `Φ(-)[0] ⟶ RΦ((-)[0])` of functors `𝒜 ⥤ D⁺(ℬ)` attached to an
additive functor `Φ : 𝒜 ⥤ ℬ` with `𝒜` having enough injectives: the unit of the bounded-below
right derived functor of `Φ`, read on the complexes concentrated in degree `0` through the two
coherence isomorphisms `CategoryTheory.Functor.mapSingleFunctorCompQhIso` and
`CategoryTheory.Functor.singleFunctorPlusIsoCompQh`. -/
noncomputable def singleRightDerivedUnit :
    Φ ⋙ DerivedCategory.Plus.singleFunctor B 0 ⟶
      DerivedCategory.Plus.singleFunctor A 0 ⋙ Φ.rightDerivedFunctorPlus :=
  (Functor.mapSingleFunctorCompQhIso Φ).inv ≫
    Functor.whiskerLeft (HomotopyCategory.Plus.singleFunctor A 0)
      Φ.rightDerivedFunctorPlusUnit ≫
    Functor.whiskerRight (Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv
      Φ.rightDerivedFunctorPlus

/-- The component of `Stacks.Cohomology.singleRightDerivedUnit` at an object. -/
lemma singleRightDerivedUnit_app (M : A) :
    (singleRightDerivedUnit Φ).app M =
      ((Functor.mapSingleFunctorCompQhIso Φ).app M).inv ≫
        Φ.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.singleFunctor A 0).obj M) ≫
        Φ.rightDerivedFunctorPlus.map
          ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app M) :=
  rfl

/-- **An injective object computes the right derived functor.**  For `I` injective the canonical
map `Φ(I)[0] ⟶ RΦ(I[0])` is invertible: `I[0]` is a bounded-below complex of injective objects,
so the unit of `RΦ` is invertible there, and the two coherence maps are isomorphisms. -/
instance isIso_singleRightDerivedUnit_app (I : A) [Injective I] :
    IsIso ((singleRightDerivedUnit Φ).app I) := by
  have hX : ∀ m : ℤ,
      Injective (((HomotopyCategory.Plus.singleFunctor A 0).obj I).obj.as.X m) :=
    fun m ↦ inferInstanceAs
      (Injective (((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj I).X m))
  have : IsIso (Φ.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj I)) := inferInstance
  rw [singleRightDerivedUnit_app]
  infer_instance

end Unit

/-! ### The arrow of Stacks 01F9 -/

section Main

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- Sections over an open subset of a ringed space form an additive functor. -/
local instance additiveEvaluation (Z : RingedSpace.{u, u}) (V : Opens Z.carrier) :
    (SheafOfModules.evaluation (structureSheafRing Z) (op V)).Additive := by
  unfold SheafOfModules.evaluation
  infer_instance

/-- **Stacks 01F8** in the form [Stacks, Tag 01F9] consumes it: an `f`-map `φ : 𝒢 ⟶ f_* ℱ`
induces a morphism `𝒢[0] ⟶ Rf_*(ℱ[0])` in `D⁺(Mod 𝒪_Y)`, namely `φ[0]` followed by the
canonical map `(f_* ℱ)[0] ⟶ Rf_*(ℱ[0])`. -/
noncomputable def toDerivedPushforward {G : Modules Y} {F : Modules X}
    (phi : G ⟶ (pushforward f).obj F) :
    (DerivedCategory.Plus.singleFunctor (Modules Y) 0).obj G ⟶
      (pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F) :=
  (DerivedCategory.Plus.singleFunctor (Modules Y) 0).map phi ≫
    (singleRightDerivedUnit (pushforward f)).app F

/-- `Stacks.Cohomology.toDerivedPushforward` is natural in the module downstairs: precomposing
the `f`-map with `g : 𝒢' ⟶ 𝒢` precomposes the morphism with `g[0]`. -/
lemma toDerivedPushforward_comp_left {G G' : Modules Y} {F : Modules X}
    (g : G' ⟶ G) (phi : G ⟶ (pushforward f).obj F) :
    (DerivedCategory.Plus.singleFunctor (Modules Y) 0).map g ≫ toDerivedPushforward f phi =
      toDerivedPushforward f (g ≫ phi) := by
  simp [toDerivedPushforward]

/-- `Stacks.Cohomology.toDerivedPushforward` is natural in the module upstairs. -/
lemma toDerivedPushforward_comp_right {G : Modules Y} {F F' : Modules X}
    (phi : G ⟶ (pushforward f).obj F) (k : F ⟶ F') :
    toDerivedPushforward f phi ≫
        (pushforward f).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor (Modules X) 0).map k) =
      toDerivedPushforward f (phi ≫ (pushforward f).map k) := by
  have h : (DerivedCategory.Plus.singleFunctor (Modules Y) 0).map ((pushforward f).map k) ≫
        (singleRightDerivedUnit (pushforward f)).app F' =
      (singleRightDerivedUnit (pushforward f)).app F ≫
        (pushforward f).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor (Modules X) 0).map k) :=
    (singleRightDerivedUnit (pushforward f)).naturality k
  simp only [toDerivedPushforward, Functor.map_comp, Category.assoc, h]

/-- **The identification `RΓ(X, -) ≅ RΓ(Y, Rf_*(-))`.**  The composite of underived functors
`Γ(Y, -) ∘ f_*` is `Γ(X, -)` with scalars restricted along `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`, so this is
the canonical comparison of [Stacks, Tag 015M] for that composition; it is an isomorphism
because the pushforward of an injective module has acyclic global sections, which is
[Stacks, Tag 01EX] part (2). -/
noncomputable def derivedGlobalSectionsComparison :
    derivedModuleGlobalSectionsAlong f ≅
      (pushforward f).rightDerivedFunctorPlus ⋙ derivedModuleGlobalSections Y :=
  compIso (pushforward f) (moduleGlobalSections Y)
    (rightAcyclic_modulePushforward_obj f ⊤)

/-- **Stacks 01F9.**  An `f`-map `φ : 𝒢 ⟶ f_* ℱ` from an `𝒪_Y`-module `𝒢` to an `𝒪_X`-module
`ℱ` induces the morphism

```
φ : RΓ(Y, 𝒢) ⟶ RΓ(X, ℱ)
```

of `D⁺(Γ(Y, 𝒪_Y))`, the target carrying its `Γ(Y, 𝒪_Y)`-module structure by restriction of
scalars along `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`.  It is `RΓ(Y, -)` applied to the morphism
`𝒢[0] ⟶ Rf_*(ℱ[0])` of [Stacks, Tag 01F8], followed by the identification
`RΓ(Y, Rf_* ℱ) ≅ RΓ(X, ℱ)` of [Stacks, Tag 01EZ]. -/
@[stacks 01F9]
noncomputable def derivedGlobalSectionsMap {G : Modules Y} {F : Modules X}
    (phi : G ⟶ (pushforward f).obj F) :
    (derivedModuleGlobalSections Y).obj
        ((DerivedCategory.Plus.singleFunctor (Modules Y) 0).obj G) ⟶
      (derivedModuleGlobalSectionsAlong f).obj
        ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F) :=
  (derivedModuleGlobalSections Y).map (toDerivedPushforward f phi) ≫
    (derivedGlobalSectionsComparison f).inv.app
      ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F)

/-- **The arrow of [Stacks, Tag 01F9] split off from the `f`-map.**  The `f`-map enters only
through `RΓ(Y, φ[0])`, the remaining two factors depending on `ℱ` alone: the canonical map
`(f_* ℱ)[0] ⟶ Rf_*(ℱ[0])` of [Stacks, Tag 01F8] and the identification of [Stacks, Tag 01EZ]. -/
lemma derivedGlobalSectionsMap_eq {G : Modules Y} {F : Modules X}
    (phi : G ⟶ (pushforward f).obj F) :
    derivedGlobalSectionsMap f phi =
      (derivedModuleGlobalSections Y).map
          ((DerivedCategory.Plus.singleFunctor (Modules Y) 0).map phi) ≫
        ((derivedModuleGlobalSections Y).map
            ((singleRightDerivedUnit (pushforward f)).app F) ≫
          (derivedGlobalSectionsComparison f).inv.app
            ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F)) := by
  rw [derivedGlobalSectionsMap, toDerivedPushforward, Functor.map_comp, Category.assoc]

/-- **The identity law for [Stacks, Tag 01F9], reduced to the cancellation of its two factors.**
For `f = 𝟙 X` an `f`-map is a morphism `φ : 𝒢 ⟶ ℱ` of `𝒪_X`-modules; granted that the canonical
map `ℱ[0] ⟶ R(𝟙_X)_*(ℱ[0])` of [Stacks, Tag 01F8] cancels against the identification of
[Stacks, Tag 01EZ], the arrow of [Stacks, Tag 01F9] along `𝟙 X` is `RΓ(X, φ[0])`. -/
lemma derivedGlobalSectionsMap_id_of_cancel {Z : RingedSpace.{u, u}} {G F : Modules Z}
    (phi : G ⟶ F)
    (h : (derivedModuleGlobalSections Z).map
          ((singleRightDerivedUnit (pushforward (𝟙 Z))).app F) ≫
        (derivedGlobalSectionsComparison (𝟙 Z)).inv.app
          ((DerivedCategory.Plus.singleFunctor (Modules Z) 0).obj F) = 𝟙 _) :
    derivedGlobalSectionsMap (𝟙 Z) phi =
      (derivedModuleGlobalSections Z).map
        ((DerivedCategory.Plus.singleFunctor (Modules Z) 0).map phi) :=
  (derivedGlobalSectionsMap_eq (𝟙 Z) phi).trans
    ((congrArg (fun t => (derivedModuleGlobalSections Z).map
        ((DerivedCategory.Plus.singleFunctor (Modules Z) 0).map phi) ≫ t) h).trans
      (Category.comp_id _))

/-- **Functoriality in the module downstairs.**  Precomposing the `f`-map with `g : 𝒢' ⟶ 𝒢`
precomposes the arrow of [Stacks, Tag 01F9] with `RΓ(Y, g[0])`. -/
lemma derivedGlobalSectionsMap_comp_left {G G' : Modules Y} {F : Modules X}
    (g : G' ⟶ G) (phi : G ⟶ (pushforward f).obj F) :
    (derivedModuleGlobalSections Y).map
          ((DerivedCategory.Plus.singleFunctor (Modules Y) 0).map g) ≫
        derivedGlobalSectionsMap f phi =
      derivedGlobalSectionsMap f (g ≫ phi) := by
  rw [derivedGlobalSectionsMap, derivedGlobalSectionsMap, ← Category.assoc,
    ← Functor.map_comp, toDerivedPushforward_comp_left]

/-- **Functoriality in the module upstairs.**  Postcomposing the `f`-map with `f_*(k)` for
`k : ℱ ⟶ ℱ'` postcomposes the arrow of [Stacks, Tag 01F9] with `RΓ(X, k[0])`. -/
lemma derivedGlobalSectionsMap_comp_right {G : Modules Y} {F F' : Modules X}
    (phi : G ⟶ (pushforward f).obj F) (k : F ⟶ F') :
    derivedGlobalSectionsMap f phi ≫
        (derivedModuleGlobalSectionsAlong f).map
          ((DerivedCategory.Plus.singleFunctor (Modules X) 0).map k) =
      derivedGlobalSectionsMap f (phi ≫ (pushforward f).map k) := by
  have hc : (derivedModuleGlobalSections Y).map
          ((pushforward f).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor (Modules X) 0).map k)) ≫
        (derivedGlobalSectionsComparison f).inv.app
          ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F') =
      (derivedGlobalSectionsComparison f).inv.app
          ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F) ≫
        (derivedModuleGlobalSectionsAlong f).map
          ((DerivedCategory.Plus.singleFunctor (Modules X) 0).map k) :=
    (derivedGlobalSectionsComparison f).inv.naturality
      ((DerivedCategory.Plus.singleFunctor (Modules X) 0).map k)
  rw [derivedGlobalSectionsMap, derivedGlobalSectionsMap, Category.assoc, ← hc,
    ← Category.assoc, ← Functor.map_comp, toDerivedPushforward_comp_right]

/-- **The arrow of [Stacks, Tag 01F9] is not degenerate.**  For an injective `𝒪_X`-module `ℱ`
and an invertible `f`-map `φ : 𝒢 ⟶ f_* ℱ`, the induced morphism
`RΓ(Y, 𝒢) ⟶ RΓ(X, ℱ)` is an isomorphism. -/
instance isIso_derivedGlobalSectionsMap {G : Modules Y} {F : Modules X} [Injective F]
    (phi : G ⟶ (pushforward f).obj F) [IsIso phi] :
    IsIso (derivedGlobalSectionsMap f phi) := by
  have : IsIso (toDerivedPushforward f phi) := by
    rw [toDerivedPushforward]
    infer_instance
  rw [derivedGlobalSectionsMap]
  infer_instance

/-- The arrow of [Stacks, Tag 01F9] for an `f`-map presented in its adjoint form
`f^* 𝒢 ⟶ ℱ`, the two presentations being interchanged by the adjunction `f^* ⊣ f_*` of
[Stacks, Tag 0096]. -/
noncomputable def derivedGlobalSectionsMapOfPullback {G : Modules Y} {F : Modules X}
    (psi : (_root_.pullback f).obj G ⟶ F) :
    (derivedModuleGlobalSections Y).obj
        ((DerivedCategory.Plus.singleFunctor (Modules Y) 0).obj G) ⟶
      (derivedModuleGlobalSectionsAlong f).obj
        ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F) :=
  derivedGlobalSectionsMap f ((_root_.pullbackPushforwardAdjunction f).homEquiv G F psi)

end Main

end Stacks.Cohomology

end
