module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleToposRingedHom
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedDerivedPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedSmallEtaleTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleSubsites
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The morphism `ε : (X_étale, 𝒪_X) ⟶ (X_{0,Zar}, 𝒪_{X_0})` of a representable algebraic space

Let `U` be an object of the big fppf site over `S`, with underlying scheme `X_0`, and let
`X = yoneda.obj U` be the algebraic space it represents.  The small étale site of `X` is
equivalent to the small étale site of `X_0` (Stacks 04M0,
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`), and the morphism of ringed topoi
`ε = id_{small, étale, Zar} : X_{0,étale} ⟶ X_{0,Zar}` of Stacks 070R gives, after composing
with that equivalence, the morphism of ringed topoi

`ε : (X_étale, 𝒪_X) ⟶ (X_{0,Zar}, 𝒪_{X_0})`

whose inverse image computes the equivalence of Stacks 071Q.

## Main definitions

* `representedSmallEtaleToposMorphismRepresentedZariskiRingedToposHom`: the equivalence of small
  étale sites as a morphism of topoi.
* `representedSmallEtaleRingedToposHomRepresentedZariskiRingedToposHom`: the same as a morphism of
  ringed topoi `(X_étale, 𝒪_X) ⟶ (X_{0,étale}, 𝒪)`, with identity structure map.
* `representedZariskiRingedToposHomRepresentedZariskiRingedToposHom`: `ε`, its composite with
  `AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom`.

## Main results

* `representedZariskiRingedToposHom_pushforward_representedZariskiRingedToposHom`: the direct image
  of sheaves of sets along `ε` is restriction along the functor `X_{0,Zar} ⥤ X_étale` sending an
  open `V ⊆ X_0` to the étale chart `V ⟶ X`, on the nose.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The scheme underlying an object `U` of the big fppf site over `S`. -/
abbrev representedSchemeRepresentedZariskiRingedToposHom : Scheme.{u} :=
  (BigFppfOver.toScheme B S hS).obj U

/-- The comparison of the small étale site of `yoneda.obj U` with the small étale site of the
scheme underlying `U` is continuous at its `symm` spelling. -/
instance
    isContinuous_representedSmallEtaleEquivalence_symm_functor_representedZariskiRingedToposHom :
    (representedSmallEtaleEquivalence B S hS U).symm.functor.IsContinuous
      (representedSchemeSmallEtaleTopology B S hS U)
      (SmallEtale.topology B S hS (yoneda.obj U)) :=
  isContinuous_representedSmallEtaleEquivalence_inverse B S hS U

/-- The comparison, read backwards, is continuous at its `symm` spelling. -/
instance
    isContinuous_representedSmallEtaleEquivalence_symm_inverse_representedZariskiRingedToposHom :
    (representedSmallEtaleEquivalence B S hS U).symm.inverse.IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSchemeSmallEtaleTopology B S hS U) :=
  isContinuous_representedSmallEtaleEquivalence_functor B S hS U

/-- The comparison of small étale sites, at its `symm.inverse` spelling, is a dense subsite. -/
instance
    isDenseSubsite_representedSmallEtaleEquivalence_symm_inverse_representedZariskiRingedToposHom :
    (representedSmallEtaleEquivalence B S hS U).symm.inverse.IsDenseSubsite
      (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSchemeSmallEtaleTopology B S hS U) :=
  isDenseSubsite_representedSmallEtaleEquivalence_functor B S hS U

/-- **The equivalence of small étale sites of Stacks 04M0 as a morphism of topoi**
`Sh(X_étale) ⟶ Sh(X_{0,étale})`.  Its direct image is restriction along the inverse of the
comparison and its inverse image restriction along the comparison; the adjunction is Mathlib's
equivalence of sheaf categories. -/
def representedSmallEtaleToposMorphismRepresentedZariskiRingedToposHom :
    MorphismOfTopoi (Sheaf (SmallEtale.topology B S hS (yoneda.obj U)) (Type u))
      (Sheaf (representedSchemeSmallEtaleTopology B S hS U) (Type u)) where
  inverseImage := (representedSmallEtaleEquivalence B S hS U).functor.sheafPushforwardContinuous
    (Type u) (SmallEtale.topology B S hS (yoneda.obj U))
    (representedSchemeSmallEtaleTopology B S hS U)
  pushforward := (representedSmallEtaleEquivalence B S hS U).inverse.sheafPushforwardContinuous
    (Type u) (representedSchemeSmallEtaleTopology B S hS U)
    (SmallEtale.topology B S hS (yoneda.obj U))
  adj := (Equivalence.sheafCongr (representedSchemeSmallEtaleTopology B S hS U)
    (SmallEtale.topology B S hS (yoneda.obj U))
    (representedSmallEtaleEquivalence B S hS U).symm (Type u)).toAdjunction
  preservesFiniteLimits := Functor.preservesFiniteLimits_sheafPushforwardContinuous
    (SmallEtale.topology B S hS (yoneda.obj U)) (representedSchemeSmallEtaleTopology B S hS U)
    (representedSmallEtaleEquivalence B S hS U).functor (Type u)

/-- **The structure sheaf of the small étale site of the scheme underlying `U` is the
restriction of the structure sheaf of `yoneda.obj U` along the inverse comparison.**  Both send
an étale chart to the global regular functions on the same scheme, so the comparison is the
identity on sections. -/
def representedCommRingStructureMapRepresentedZariskiRingedToposHom :
    (representedSchemeRingedTopos B S hS U).O ⟶
      ((representedSmallEtaleEquivalence B S hS U).inverse.sheafPushforwardContinuous
          CommRingCat.{u} (representedSchemeSmallEtaleTopology B S hS U)
          (SmallEtale.topology B S hS (yoneda.obj U))).obj
        (smallEtaleRingedTopos B S hS (representedSpace U)).O where
  hom := 𝟙 _

/-- **The equivalence of small étale sites as a morphism of ringed topoi**
`(X_étale, 𝒪_X) ⟶ (X_{0,étale}, 𝒪)`, for `X = yoneda.obj U` and `X_0` the scheme underlying
`U`; its structure map is the identity on sections. -/
def representedSmallEtaleRingedToposHomRepresentedZariskiRingedToposHom :
    RingedToposHom (smallEtaleRingedTopos B S hS (representedSpace U))
      (representedSchemeRingedTopos B S hS U) where
  toToposHom := representedSmallEtaleToposMorphismRepresentedZariskiRingedToposHom B S hS U
  fSharp := representedCommRingStructureMapRepresentedZariskiRingedToposHom B S hS U ≫
    (restrictionCommRingIso (representedSchemeSmallEtaleTopology B S hS U)
      (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U).inverse
      (smallEtaleRingedTopos B S hS (representedSpace U)).O).inv

/-- **The morphism of ringed topoi `ε : (X_étale, 𝒪_X) ⟶ (X_{0,Zar}, 𝒪_{X_0})`** of a
representable algebraic space `X = yoneda.obj U` with underlying scheme `X_0`: the equivalence
of small étale sites followed by `ε = id_{small, étale, Zar}` of Stacks 070R. -/
@[sga "4 VII 4.2.2"]
abbrev representedZariskiRingedToposHomRepresentedZariskiRingedToposHom :
    RingedToposHom (smallEtaleRingedTopos B S hS (representedSpace U))
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos :=
  RingedToposHom.comp (X := smallEtaleRingedTopos B S hS (representedSpace U))
    (Y := representedSchemeRingedTopos B S hS U)
    (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
    (_root_.AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom (associatedBigEtaleSite B)
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U) U.left.property)
    (representedSmallEtaleRingedToposHomRepresentedZariskiRingedToposHom B S hS U)

/-- The functor `X_{0,Zar} ⥤ X_étale` sending an open `V ⊆ X_0` to the étale chart `V ⟶ X`. -/
abbrev representedSchemeOpensToSmallEtaleRepresentedZariskiRingedToposHom :
    (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Opens ⥤
      SmallEtale B S hS (yoneda.obj U) :=
  _root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U) U.left.property ⋙
    (representedSmallEtaleEquivalence B S hS U).inverse

/-- **The direct image of sheaves of sets along `ε` is restriction along
`representedSchemeOpensToSmallEtaleRepresentedZariskiRingedToposHom`**, on the nose. -/
theorem representedZariskiRingedToposHom_pushforward_representedZariskiRingedToposHom :
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom
        B S hS U).toToposHom.pushforward =
      (representedSmallEtaleEquivalence B S hS U).inverse.sheafPushforwardContinuous (Type u)
          (representedSchemeSmallEtaleTopology B S hS U)
          (SmallEtale.topology B S hS (yoneda.obj U)) ⋙
        (_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
          (representedSchemeRepresentedZariskiRingedToposHom B S hS U)
            U.left.property).sheafPushforwardContinuous (Type u)
          (Opens.grothendieckTopology ↥(representedSchemeRepresentedZariskiRingedToposHom B S hS U))
          (representedSchemeSmallEtaleTopology B S hS U) :=
  rfl

end AlgebraicGeometry.Space
