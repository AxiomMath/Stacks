module

public import StacksFrontier.Topology.Sheaves.Modules.StalkSkyscraperAdjunction
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
public import Mathlib.Algebra.Homology.Additive
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk of a pullback of sheaves of modules

Let `(f, f^♯) : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `x : X`. This file
identifies the stalk at `x` of the pullback `f^* A` of a sheaf of `𝒪_Y`-modules with the base
change of the stalk of `A` at `f x`:

`(f^* A)_x ≅ A_{f(x)} ⊗_{𝒪_{Y,f(x)}} 𝒪_{X,x}`,

naturally in `A`, at universe `u`, and for
`RingedSpaceModuleAdjunction.modulePullback f` itself.

## Main results

* `Stacks.RingedSpace.stalkRingMap`: the germ map `𝒪_{Y,f(x)} ⟶ 𝒪_{X,x}` of the morphism.
* `Stacks.RingedSpace.pushforwardSkyscraperIso`: pushing a skyscraper at `x` forward along `f`
  is the skyscraper at `f x` of the restriction of scalars along `stalkRingMap`.
* `Stacks.RingedSpace.stalkBaseChange`: the base-change functor
  `N ↦ 𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} N` on stalk modules.
* `Stacks.RingedSpace.stalkModulePullbackFunctorIso`: the isomorphism of functors
  `f^* ⋙ (-)_x ≅ (-)_{f(x)} ⋙ (𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} -)`.
* `Stacks.RingedSpace.stalkModulePullbackIso`: its value at a sheaf of modules `A`.
* `Stacks.RingedSpace.stalkModulePullbackComplexIso`: the same isomorphism degreewise on complexes.

## Implementation notes

The `𝒪_{X,x}`-side and `𝒪_{Y,f(x)}`-side stalk rings are the `RingCat`-valued stalks of
`structureSheafRing`, because that is where `SheafOfModules` and hence
`modulePullback` live. `ModuleCat.extendRestrictScalarsAdj` needs both rings commutative, which
they are, but not by an instance: `stalkCommRing` transports commutativity along
`SemilinearStalk.commStalkRingEquiv`.

That commutativity is not declared as an instance. A `RingCat` object already carries a `Ring`
instance, so a `CommRing` instance in scope gives a second `Ring` instance reachable through
`CommRing.toRing`; the two are definitionally equal but not syntactically, and `ModuleCat` of the
stalk then elaborates two ways, so that an instance found at one spelling is not found at the
other. The commutativity is seated with `letI` inside the declarations that need it, and
`stalkBaseChange` fixes the `RingCat` spelling once: its statement uses the `RingCat` `Ring`
instances and its body is `ModuleCat.extendScalars`.

`pushforwardSkyscraperIso` is built from the *identity* morphism of underlying presheaves of
abelian groups. The two presheaves are definitionally equal: `x ∈ (Opens.map g).obj V` unfolds
to `g x ∈ V`, so `PLift (x ∈ f^{-1} V) → N` and `PLift (f x ∈ V) → N` are the same type, and
both restriction maps are precomposition with the implication between those propositions. Only
the two `𝒪_Y(V)`-module structures differ, and the germ square identifies them. Writing it this
way is what makes `hom_inv_id` and `inv_hom_id` hold by `rfl`.

Universes are written out as `RingedSpace.{u, u}` and `SheafOfModules.{u}` throughout. That
restriction is forced by `PresheafOfModules.instIsRightAdjointPushforward`, which produces
`modulePullback`.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

noncomputable section

namespace Stacks.RingedSpace

open RingedSpaceModuleAdjunction AlgebraicGeometry.SheafOfModules

section StalkRingMap

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y) (x : X.carrier)

/-- The germ map of a morphism of ringed spaces on structure sheaves, `𝒪_{Y,f(x)} ⟶ 𝒪_{X,x}`,
read for the `RingCat`-valued structure sheaves that `SheafOfModules` is stated for: take the
stalk at `f x` of `f^♯ : 𝒪_Y ⟶ f_* 𝒪_X`, then the canonical map from the stalk of a
pushforward. -/
def stalkRingMap :
    TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Y.carrier)
        (structureSheafRing Y).obj (f.hom.base x) ⟶
      TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X.carrier) (structureSheafRing X).obj x :=
  (TopCat.Presheaf.stalkFunctor RingCat.{u} (f.hom.base x)).map (structureSheafHom f).hom ≫
    TopCat.Presheaf.stalkPushforward RingCat.{u} f.hom.base (structureSheafRing X).obj x

/-- **The germ square of a morphism of ringed spaces.** The germ at `x` of the image of a
section of `𝒪_Y` over `V` under `f^♯` is the image under `stalkRingMap` of its germ at `f x`. -/
theorem stalkRingMap_germ (V : Opens Y.carrier) (hV : f.hom.base x ∈ V)
    (r : (structureSheafRing Y).obj.obj (op V)) :
    (stalkRingMap f x).hom
        ((TopCat.Presheaf.germ (C := RingCat.{u}) (X := Y.carrier)
          (structureSheafRing Y).obj V (f.hom.base x) hV).hom r) =
      (TopCat.Presheaf.germ (C := RingCat.{u}) (X := X.carrier)
          (structureSheafRing X).obj ((opensMap f).obj V) x hV).hom
        ((structureSheafHom f).hom.app (op V) r) := by
  have h1 := TopCat.Presheaf.stalkFunctor_map_germ_apply (C := RingCat.{u}) V (f.hom.base x) hV
    (structureSheafHom f).hom r
  have h2 := TopCat.Presheaf.stalkPushforward_germ_apply RingCat.{u} f.hom.base
    (structureSheafRing X).obj V x hV ((structureSheafHom f).hom.app (op V) r)
  exact (congrArg (TopCat.Presheaf.stalkPushforward RingCat.{u} f.hom.base
    (structureSheafRing X).obj x).hom h1).trans h2

end StalkRingMap

section StalkCommRing

variable {X : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} X) (x : X)

/-- Multiplication on the `RingCat`-valued stalk of a presheaf of *commutative* rings is
commutative. -/
theorem stalk_mul_comm
    (a b : ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X)
      (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x)) : a * b = b * a :=
  (SemilinearStalk.commStalkRingEquiv R x).injective <| by rw [map_mul, map_mul, mul_comm]

/-- The `RingCat`-valued stalk of a presheaf of commutative rings, as a commutative ring. Its
`Ring` part is the one carried by the `RingCat` object, so the category `ModuleCat` of the stalk
is unchanged by having this in scope. -/
@[instance_reducible]
def stalkCommRing :
    CommRing (ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X)
      (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x)) :=
  { (inferInstance : Ring _) with mul_comm := stalk_mul_comm R x }

end StalkCommRing

section PushforwardSkyscraper

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y) (x : X.carrier)

attribute [local instance] AlgebraicGeometry.SheafOfModules.skyscraperModule

/-- **Pushing a skyscraper forward.** The direct image along `f` of the skyscraper sheaf at `x`
with value an `𝒪_{X,x}`-module `N` is the skyscraper sheaf at `f x` with value `N` regarded as
an `𝒪_{Y,f(x)}`-module through `stalkRingMap`. -/
def pushforwardSkyscraperObjIso
    (N : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X.carrier)
      (structureSheafRing X).obj x)) :
    (modulePushforward f).obj (skyscraperObj (structureSheafRing X) x N) ≅
      skyscraperObj (structureSheafRing Y) (f.hom.base x)
        ((ModuleCat.restrictScalars.{u, u, u} (stalkRingMap f x).hom).obj N) where
  hom := ⟨PresheafOfModules.homMk (𝟙 _) (fun V r m => funext fun h =>
    congrArg (fun t => t • m h) (stalkRingMap_germ f x V.unop h.down r).symm)⟩
  inv := ⟨PresheafOfModules.homMk (𝟙 _) (fun V r m => funext fun h =>
    congrArg (fun t => t • m h) (stalkRingMap_germ f x V.unop h.down r))⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- `pushforwardSkyscraperObjIso` as an isomorphism of functors
`i_{x,*} ⋙ f_* ≅ restrictScalars ⋙ i_{f(x),*}`. -/
def pushforwardSkyscraperIso :
    skyscraperFunctor (structureSheafRing X) x ⋙ modulePushforward f ≅
      ModuleCat.restrictScalars.{u, u, u} (stalkRingMap f x).hom ⋙
        skyscraperFunctor (structureSheafRing Y) (f.hom.base x) :=
  NatIso.ofComponents (fun N => pushforwardSkyscraperObjIso f x N) (fun _ => by ext; rfl)

end PushforwardSkyscraper

section Main

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y) (x : X.carrier)

/-- The stalk of the structure sheaf of a ringed space, as a commutative ring. -/
@[instance_reducible]
def structureStalkCommRing (Z : AlgebraicGeometry.RingedSpace.{u, u}) (z : Z.carrier) :
    CommRing (ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Z.carrier)
      (structureSheafRing Z).obj z)) :=
  stalkCommRing Z.presheaf z

/-- **Base change of stalk modules along the germ map** of a morphism of ringed spaces:
`N ↦ 𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} N`. This is `ModuleCat.extendScalars` of `stalkRingMap`, stated at
the `Ring` instances the `RingCat`-valued stalks carry; its carrier is
`ModuleCat.ExtendScalars.obj'`, that is `𝒪_{X,x} ⊗[𝒪_{Y,f(x)}] N`. -/
def stalkBaseChange :
    ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Y.carrier)
        (structureSheafRing Y).obj (f.hom.base x)) ⥤
      ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X.carrier)
        (structureSheafRing X).obj x) :=
  letI := structureStalkCommRing Y (f.hom.base x)
  letI := structureStalkCommRing X x
  ModuleCat.extendScalars.{u, u, u} (stalkRingMap f x).hom

/-- `f^*` followed by the stalk at `x` is left adjoint to the skyscraper at `x` followed by
`f_*`: a composite of two adjunctions. -/
def stalkPullbackAdjunction :
    modulePullback f ⋙ stalkFunctor (structureSheafRing X) x ⊣
      skyscraperFunctor (structureSheafRing X) x ⋙ modulePushforward f :=
  (modulePullbackPushforwardAdjunction f).comp (stalkSkyscraperAdjunction (structureSheafRing X) x)

/-- The stalk at `f x` followed by base change along `stalkRingMap` is left adjoint to
restriction of scalars followed by the skyscraper at `f x`: a composite of the stalk--skyscraper
adjunction on `Y` with `ModuleCat.extendRestrictScalarsAdj`. -/
def stalkBaseChangeAdjunction :
    stalkFunctor (structureSheafRing Y) (f.hom.base x) ⋙ stalkBaseChange f x ⊣
      ModuleCat.restrictScalars.{u, u, u} (stalkRingMap f x).hom ⋙
        skyscraperFunctor (structureSheafRing Y) (f.hom.base x) :=
  letI := structureStalkCommRing Y (f.hom.base x)
  letI := structureStalkCommRing X x
  (stalkSkyscraperAdjunction (structureSheafRing Y) (f.hom.base x)).comp
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (stalkRingMap f x).hom)

/-- The stalk at `x` of the pullback `RingedSpaceModuleAdjunction.modulePullback f` of a sheaf of
`𝒪_Y`-modules along a morphism of ringed spaces `f` is the base change along the germ map of the
stalk at `f x`, naturally in the sheaf of modules (Stacks 0098):

`f^* ⋙ (-)_x ≅ (-)_{f(x)} ⋙ (𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} -)`. -/
@[sga "6 VI 2.3.1" "partial"]
def stalkModulePullbackFunctorIso :
    modulePullback f ⋙ stalkFunctor (structureSheafRing X) x ≅
      stalkFunctor (structureSheafRing Y) (f.hom.base x) ⋙ stalkBaseChange f x :=
  ((conjugateIsoEquiv (stalkPullbackAdjunction f x) (stalkBaseChangeAdjunction f x)).symm
    (pushforwardSkyscraperIso f x)).symm

/-- The stalk of a pullback: `(f^* A)_x ≅ 𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} A_{f(x)}` (Stacks 0098).

This is `stalkModulePullbackFunctorIso` at `A`. -/
def stalkModulePullbackIso (A : _root_.SheafOfModules.{u} (structureSheafRing Y)) :
    stalkObj (structureSheafRing X) x ((modulePullback f).obj A) ≅
      (stalkBaseChange f x).obj (stalkObj (structureSheafRing Y) (f.hom.base x) A) :=
  (stalkModulePullbackFunctorIso f x).app A

/-- Base change of stalk modules is additive. -/
instance stalkBaseChange_additive : (stalkBaseChange f x).Additive :=
  haveI : Limits.PreservesColimits (stalkBaseChange f x) :=
    letI := structureStalkCommRing Y (f.hom.base x)
    letI := structureStalkCommRing X x
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (stalkRingMap f x).hom).leftAdjoint_preservesColimits
  haveI := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts (stalkBaseChange f x)
  Functor.additive_of_preservesBinaryBiproducts _

/-- For any complex shape, applying `f^*` to a complex of sheaves of `𝒪_Y`-modules degreewise and
then taking stalks at `x` degreewise is taking stalks at `f x` degreewise and then base changing
degreewise. -/
def stalkModulePullbackComplexIso {ι : Type*} (c : ComplexShape ι) :
    (modulePullback f).mapHomologicalComplex c ⋙
        (stalkFunctor (structureSheafRing X) x).mapHomologicalComplex c ≅
      (stalkFunctor (structureSheafRing Y) (f.hom.base x)).mapHomologicalComplex c ⋙
        (stalkBaseChange f x).mapHomologicalComplex c :=
  Functor.mapHomologicalComplexCompIso (Iso.refl _) c ≪≫
    NatIso.mapHomologicalComplex (stalkModulePullbackFunctorIso f x) c ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) c).symm

end Main

end Stacks.RingedSpace

end
