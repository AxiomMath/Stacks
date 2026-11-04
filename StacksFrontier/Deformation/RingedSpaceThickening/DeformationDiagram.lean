module

public import StacksFrontier.Topology.Sheaves.RingedSpace.Thickening
import StacksCore.Tactic.StacksAttribute

/-!
# The first order deformation problem for ringed spaces (Stacks 08U7)

Fix a first order thickening `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` with ideal `𝒥`, a morphism
`f : (X, 𝒪_X) ⟶ (S, 𝒪_S)`, an `𝒪_X`-module `𝒢`, and a map `c : f^* 𝒥 ⟶ 𝒢`. The problem of
Tag 08U7 is to fill in the diagram

    0 ⟶ 𝒢 ⟶  ?  ⟶ 𝒪_X  ⟶ 0
          ↑ c      ↑        ↑
    0 ⟶ 𝒥 ⟶ 𝒪_{S'} ⟶ 𝒪_S ⟶ 0

that is: to produce a first order thickening `i : X ⟶ X'` and a morphism `f' : X' ⟶ S'`
restricting to `f`, whose ideal is identified with `𝒢` in such a way that the induced vertical
map on ideals is the prescribed `c`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution`: a solution of the displayed
  problem — the deformed space, the thickening, the morphism over `S'`, the identification of
  the ideal of the thickening with the pushforward of `𝒢`, and the compatibility equation.
* `DeformationSolution.toMorphismOfThickenings`: the morphism of thickenings underlying a
  solution.
* `AlgebraicGeometry.RingedSpaceThickening.DeformationCube`: the commutative diagram of ringed
  spaces comparing two deformation situations, without an arrow between the deformed spaces.
* `DeformationCube.IsCompatibleLift`: the two faces a candidate arrow between the deformed
  spaces must fill.
* `AlgebraicGeometry.RingedSpaceThickening.DeformationIdealDiagram`: the commutative diagram of
  the four short exact ideal rows attached to such a cube, with front and back solutions of the
  deformation problem and a comparison `ν` of their ideals.

## References

* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
* [Stacks Project, Tag 08U9](https://stacks.math.columbia.edu/tag/08U9)
* [Stacks Project, Tag 08UA](https://stacks.math.columbia.edu/tag/08UA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-- A solution of the first order deformation problem for a fixed
first order thickening `t : S ⟶ S'`, morphism `f : X ⟶ S`, `𝒪_X`-module `𝒢` and prescribed map
`c : f^* t^* 𝒥 ⟶ 𝒢`: a first order thickening `i : X ⟶ X'` and a morphism `f' : X' ⟶ S'` over
`t`, together with an identification of the ideal of `i` with `𝒢` under which the vertical map
on ideals induced by `f'` is exactly `c`. -/
@[stacks 08U7 "the deformation problem to solve",
  stacks 08UY "the same displayed deformation problem for ringed spaces"]
structure DeformationSolution {X S S' : RingedSpace.{u, u}} (t : S ⟶ S')
    (ht : IsFirstOrderThickening t) (f : X ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing X))
    (c : (modulePullback f).obj
      ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G) where
  /-- The deformed ringed space. -/
  X' : RingedSpace.{u, u}
  /-- Its thickening of `X`. -/
  i : X ⟶ X'
  /-- The extension of `f` over `S'`. -/
  f' : X' ⟶ S'
  /-- The upper row is a first order thickening. -/
  i_firstOrder : IsFirstOrderThickening i
  /-- The square of ringed spaces commutes, i.e. `f'` restricts to `f`. -/
  comm : i ≫ f' = f ≫ t
  /-- Identification of the ideal of `i` with the prescribed module. -/
  kernelIso :
    AlgebraicGeometry.SheafOfModules.idealSheaf i ≅ (modulePushforward i).obj G
  /-- The vertical map on ideals induced by `f'` is the prescribed map `c`. -/
  compatibility :
    let D : MorphismOfThickenings.{u} :=
      { X := X, X' := X', S := S, S' := S', i := i, t := t, f := f, f' := f',
        i_isThickening := i_firstOrder.1, t_isThickening := ht.1, comm := comm }
    (D.firstOrderIdealMap i_firstOrder ht).1 ≫ kernelIso.hom =
      (modulePushforward i).map c

/-- The morphism of thickenings underlying a solution of the deformation problem. -/
def DeformationSolution.toMorphismOfThickenings {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'}
    {ht : IsFirstOrderThickening t} {f : X ⟶ S} {G : SheafOfModules.{u} (structureSheafRing X)}
    {c : (modulePullback f).obj
      ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}
    (Q : DeformationSolution t ht f G c) : MorphismOfThickenings.{u} where
  X := X
  X' := Q.X'
  S := S
  S' := S'
  i := Q.i
  t := t
  f := f
  f' := Q.f'
  i_isThickening := Q.i_firstOrder.1
  t_isThickening := ht.1
  comm := Q.comm

/-- The commutative diagram of morphisms of ringed spaces
comparing two deformation situations: a square `i₂ : X₂ ⟶ X₂'` over `t₂ : S₂ ⟶ S₂'` at the
back, a square `i₁ : X₁ ⟶ X₁'` over `t₁ : S₁ ⟶ S₁'` at the front, and comparison morphisms
`g : X₂ ⟶ X₁`, `h : S₂ ⟶ S₁`, `h' : S₂' ⟶ S₁'` making the four closed faces commute. There
is no comparison `X₂' ⟶ X₁'`. -/
@[stacks 08U9 "the displayed commutative diagram of ringed spaces"]
structure DeformationCube where
  /-- The reduced source space of the front square. -/
  X₁ : RingedSpace.{u, u}
  /-- The deformed source space of the front square. -/
  X₁' : RingedSpace.{u, u}
  /-- The reduced base of the front square. -/
  S₁ : RingedSpace.{u, u}
  /-- The deformed base of the front square. -/
  S₁' : RingedSpace.{u, u}
  /-- The reduced source space of the back square. -/
  X₂ : RingedSpace.{u, u}
  /-- The deformed source space of the back square. -/
  X₂' : RingedSpace.{u, u}
  /-- The reduced base of the back square. -/
  S₂ : RingedSpace.{u, u}
  /-- The deformed base of the back square. -/
  S₂' : RingedSpace.{u, u}
  /-- The front thickening of source spaces. -/
  i₁ : X₁ ⟶ X₁'
  /-- The front structure morphism. -/
  f₁ : X₁ ⟶ S₁
  /-- The front deformed structure morphism. -/
  f₁' : X₁' ⟶ S₁'
  /-- The front thickening of bases. -/
  t₁ : S₁ ⟶ S₁'
  /-- The back thickening of source spaces. -/
  i₂ : X₂ ⟶ X₂'
  /-- The back structure morphism. -/
  f₂ : X₂ ⟶ S₂
  /-- The back deformed structure morphism. -/
  f₂' : X₂' ⟶ S₂'
  /-- The back thickening of bases. -/
  t₂ : S₂ ⟶ S₂'
  /-- The comparison of reduced source spaces. -/
  g : X₂ ⟶ X₁
  /-- The comparison of reduced bases. -/
  h : S₂ ⟶ S₁
  /-- The comparison of deformed bases. -/
  h' : S₂' ⟶ S₁'
  /-- The back square commutes. -/
  back_comm : i₂ ≫ f₂' = f₂ ≫ t₂
  /-- The front square commutes. -/
  front_comm : i₁ ≫ f₁' = f₁ ≫ t₁
  /-- The comparison of source spaces lies over the comparison of bases. -/
  source_comm : g ≫ f₁ = f₂ ≫ h
  /-- The square of bases commutes. -/
  base_comm : h ≫ t₁ = t₂ ≫ h'

namespace DeformationCube

variable (C : DeformationCube.{u})

/-- The square of bases of the cube, as a morphism of thickenings: the back thickening `t₂`
over the front thickening `t₁`. -/
def baseSquare (ht₁ : IsThickening C.t₁) (ht₂ : IsThickening C.t₂) :
    MorphismOfThickenings.{u} where
  X := C.S₂
  X' := C.S₂'
  S := C.S₁
  S' := C.S₁'
  i := C.t₂
  t := C.t₁
  f := C.h
  f' := C.h'
  i_isThickening := ht₂
  t_isThickening := ht₁
  comm := C.base_comm.symm

/-- The comparison `g^* f₁^* t₁^* 𝒥₁ ⟶ f₂^* t₂^* 𝒥₂` of the pulled back ideals of the two
bases: the canonical ideal map of `baseSquare`, pulled back along `f₂` and transported through
the two commuting squares of the cube. -/
noncomputable def baseIdealMap (ht₁ : IsThickening C.t₁) (ht₂ : IsThickening C.t₂) :
    (modulePullback C.g).obj
        ((modulePullback C.f₁).obj
          ((modulePullback C.t₁).obj (AlgebraicGeometry.SheafOfModules.idealSheaf C.t₁))) ⟶
      (modulePullback C.f₂).obj
        ((modulePullback C.t₂).obj (AlgebraicGeometry.SheafOfModules.idealSheaf C.t₂)) :=
  (modulePullbackCompUniq C.g C.f₁).inv.app _ ≫
    eqToHom (congrArg
      (fun k : C.X₂ ⟶ C.S₁ =>
        (modulePullback k).obj
          ((modulePullback C.t₁).obj (AlgebraicGeometry.SheafOfModules.idealSheaf C.t₁)))
      C.source_comm) ≫
    (modulePullbackCompUniq C.f₂ C.h).hom.app _ ≫
    (modulePullback C.f₂).map
      ((modulePullbackCompUniq C.h C.t₁).inv.app _ ≫
        eqToHom (congrArg
          (fun k : C.S₂ ⟶ C.S₁' =>
            (modulePullback k).obj (AlgebraicGeometry.SheafOfModules.idealSheaf C.t₁))
          C.base_comm) ≫
        (modulePullbackCompUniq C.t₂ C.h').hom.app _ ≫
        (modulePullback C.t₂).map (C.baseSquare ht₁ ht₂).idealMap.1)

/-- A morphism `g' : X₂' ⟶ X₁'` fills the two remaining faces of the cube: the square of
thickenings of source spaces, and the square over the comparison of deformed bases. -/
def IsCompatibleLift (g' : C.X₂' ⟶ C.X₁') : Prop :=
  C.i₂ ≫ g' = C.g ≫ C.i₁ ∧ g' ≫ C.f₁' = C.f₂' ≫ C.h'

end DeformationCube

/-- The commutative diagram of the four short exact ideal rows attached to a deformation cube
whose horizontal arrows are first order thickenings: modules `𝒢₁`, `𝒢₂` identifying the ideals
of `i₁` and `i₂`, prescribed maps `c₁`, `c₂` making front and back solutions of the deformation
problem, and a `g`-map `ν : 𝒢₁ ⟶ 𝒢₂` compatible with the
comparison `DeformationCube.baseIdealMap` of the ideals of `t₁` and `t₂`. -/
@[stacks 08UA "the displayed commutative diagram of the four ideal rows"]
structure DeformationIdealDiagram where
  /-- The underlying cube of ringed spaces. -/
  cube : DeformationCube.{u}
  /-- The front thickening of source spaces is first order. -/
  i₁_firstOrder : IsFirstOrderThickening cube.i₁
  /-- The back thickening of source spaces is first order. -/
  i₂_firstOrder : IsFirstOrderThickening cube.i₂
  /-- The front thickening of bases is first order. -/
  t₁_firstOrder : IsFirstOrderThickening cube.t₁
  /-- The back thickening of bases is first order. -/
  t₂_firstOrder : IsFirstOrderThickening cube.t₂
  /-- The module on `X₁` identified with the ideal of the front thickening. -/
  G₁ : SheafOfModules.{u} (structureSheafRing cube.X₁)
  /-- The module on `X₂` identified with the ideal of the back thickening. -/
  G₂ : SheafOfModules.{u} (structureSheafRing cube.X₂)
  /-- Identification of the ideal of `i₁` with `𝒢₁`. -/
  kernelIso₁ :
    AlgebraicGeometry.SheafOfModules.idealSheaf cube.i₁ ≅ (modulePushforward cube.i₁).obj G₁
  /-- Identification of the ideal of `i₂` with `𝒢₂`. -/
  kernelIso₂ :
    AlgebraicGeometry.SheafOfModules.idealSheaf cube.i₂ ≅ (modulePushforward cube.i₂).obj G₂
  /-- The prescribed vertical map on ideals of the front square. -/
  c₁ : (modulePullback cube.f₁).obj
    ((modulePullback cube.t₁).obj (AlgebraicGeometry.SheafOfModules.idealSheaf cube.t₁)) ⟶ G₁
  /-- The prescribed vertical map on ideals of the back square. -/
  c₂ : (modulePullback cube.f₂).obj
    ((modulePullback cube.t₂).obj (AlgebraicGeometry.SheafOfModules.idealSheaf cube.t₂)) ⟶ G₂
  /-- The front square, with `c₁`, is a solution of the deformation problem. -/
  front_isSolution :
    let D : MorphismOfThickenings.{u} :=
      { X := cube.X₁, X' := cube.X₁', S := cube.S₁, S' := cube.S₁',
        i := cube.i₁, t := cube.t₁, f := cube.f₁, f' := cube.f₁',
        i_isThickening := i₁_firstOrder.1, t_isThickening := t₁_firstOrder.1,
        comm := cube.front_comm }
    (D.firstOrderIdealMap i₁_firstOrder t₁_firstOrder).1 ≫ kernelIso₁.hom =
      (modulePushforward cube.i₁).map c₁
  /-- The back square, with `c₂`, is a solution of the deformation problem. -/
  back_isSolution :
    let D : MorphismOfThickenings.{u} :=
      { X := cube.X₂, X' := cube.X₂', S := cube.S₂, S' := cube.S₂',
        i := cube.i₂, t := cube.t₂, f := cube.f₂, f' := cube.f₂',
        i_isThickening := i₂_firstOrder.1, t_isThickening := t₂_firstOrder.1,
        comm := cube.back_comm }
    (D.firstOrderIdealMap i₂_firstOrder t₂_firstOrder).1 ≫ kernelIso₂.hom =
      (modulePushforward cube.i₂).map c₂
  /-- The `g`-map `ν : 𝒢₁ ⟶ 𝒢₂` comparing the two upper ideals. -/
  nu : (modulePullback cube.g).obj G₁ ⟶ G₂
  /-- The square relating `ν` to the comparison of the two lower ideals commutes. -/
  nu_comm :
    (modulePullback cube.g).map c₁ ≫ nu =
      cube.baseIdealMap t₁_firstOrder.1 t₂_firstOrder.1 ≫ c₂

namespace DeformationIdealDiagram

variable (D : DeformationIdealDiagram.{u})

/-- The front of the ideal diagram, as a solution of the deformation problem. -/
noncomputable def front : DeformationSolution D.cube.t₁ D.t₁_firstOrder D.cube.f₁ D.G₁ D.c₁ where
  X' := D.cube.X₁'
  i := D.cube.i₁
  f' := D.cube.f₁'
  i_firstOrder := D.i₁_firstOrder
  comm := D.cube.front_comm
  kernelIso := D.kernelIso₁
  compatibility := D.front_isSolution

/-- The back of the ideal diagram, as a solution of the deformation problem. -/
noncomputable def back : DeformationSolution D.cube.t₂ D.t₂_firstOrder D.cube.f₂ D.G₂ D.c₂ where
  X' := D.cube.X₂'
  i := D.cube.i₂
  f' := D.cube.f₂'
  i_firstOrder := D.i₂_firstOrder
  comm := D.cube.back_comm
  kernelIso := D.kernelIso₂
  compatibility := D.back_isSolution

end DeformationIdealDiagram

end AlgebraicGeometry.RingedSpaceThickening

end
