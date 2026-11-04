module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeDerived

/-!
# The relocalization of derived categories and the derived tensor product

Let `g : T ⟶ S` be a morphism of a big fppf site and `X` an algebraic space over `T`, with
lower-shriek extension `Λ X` over `S`. The derived equivalence `ρ : D(𝒪_X) ≌ D(𝒪_{Λ X})` of
`AlgebraicGeometry.Space.relocalizeDerivedFunctor` is the derived pullback along the morphism of
ringed topoi given by the equivalence of small étale sites, so Stacks 07A4 makes it compatible
with the derived tensor product: `ρ(K ⊗^L L) ≅ ρ K ⊗^L ρ L`.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeRingedToposHom`: the morphism of small étale ringed topoi
  `(Λ X)_{étale} ⟶ X_{étale}` given by the equivalence of sites.
* `AlgebraicGeometry.Space.relocalizeDerivedPullbackIso`: its derived pullback is `ρ`.
* `AlgebraicGeometry.Space.relocalizeDerivedTensorIso`: `ρ(K ⊗^L L) ≅ ρ K ⊗^L ρ L`, naturally in
  `(K, L)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS) (X : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B T hT X)

/-- The equivalence of small étale sites `(Λ X)_{étale} ⟶ X_{étale}`, as a morphism of ringed
sites: the functor is that of the equivalence and the structure map is the counit. -/
def relocalizeRingedSiteHom :
    RingedSite.HomGeneral
      (smallEtaleRingedSite B S hS _ (isAlgebraicSpace_relocalize' B hT hS g X hX))
      (smallEtaleRingedSite B T hT X hX) :=
  Stacks.SheafOfModules.reindexRingedSiteHom (SmallEtale.topology B S hS _)
    (SmallEtale.relocalize B hT hS g X hX).symm (structureSheaf B T hT X hX)

/-- The morphism of small étale ringed topoi underlying `relocalizeRingedSiteHom`. -/
abbrev relocalizeRingedToposHom :
    RingedToposHom (smallEtaleRingedTopos B S hS
          ⟨_, isAlgebraicSpace_relocalize' B hT hS g X hX⟩)
      (smallEtaleRingedTopos B T hT ⟨X, hX⟩) :=
  (relocalizeRingedSiteHom B hT hS g X hX).toRingedToposHom

/-- The pushforward of modules along `relocalizeRingedToposHom` is the inverse of the
relocalization of modules. -/
def relocalizePushforwardModulesIso :
    (relocalizeRingedToposHom B hT hS g X hX).pushforwardModules ≅
      ((relocalizeModulesEquivalenceSymm B hT hS g X hX).inverse :
        SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          ⟨_, isAlgebraicSpace_relocalize' B hT hS g X hX⟩) ⥤
          SheafOfModules.{u} (ringedToposStructureRingSheaf B T hT ⟨X, hX⟩)) :=
  (relocalizeRingedSiteHom B hT hS g X hX).pushforwardToposIsoGeneral ≪≫ Iso.refl _

/-- The pullback of modules along `relocalizeRingedToposHom` is the relocalization of modules:
both are left adjoint to its inverse. -/
def relocalizePullbackModulesIso :
    Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS
          ⟨_, isAlgebraicSpace_relocalize' B hT hS g X hX⟩)
        (Y := smallEtaleRingedTopos B T hT ⟨X, hX⟩)
        (relocalizeRingedToposHom B hT hS g X hX).toModulesHom ≅
      (relocalizeModulesEquivalence B hT hS g X hX).functor :=
  Adjunction.leftAdjointUniq
    ((RingedToposHom.pullbackAdjPushforwardModules
      (relocalizeRingedToposHom B hT hS g X hX)).ofNatIsoRight
        (relocalizePushforwardModulesIso B hT hS g X hX))
    (relocalizeModulesEquivalenceSymm B hT hS g X hX).toAdjunction ≪≫
  relocalizeModulesEquivalenceSymmFunctorIso B hT hS g X hX

open Stacks.Cohomology.DerivedPullbackOfToposHom in
/-- The derived pullback along `relocalizeRingedToposHom` exists (Stacks 06YY). -/
instance hasLeftDerivedFunctor_relocalizePullbackOnHomotopy :
    (pullbackOnHomotopy (relocalizeRingedToposHom B hT hS g X hX)).HasLeftDerivedFunctor
    (quasiIsoTarget (Y := smallEtaleRingedTopos B T hT ⟨X, hX⟩)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy
    (X := smallEtaleRingedTopos B S hS
          ⟨_, isAlgebraicSpace_relocalize' B hT hS g X hX⟩)
    (Y := smallEtaleRingedTopos B T hT ⟨X, hX⟩) (relocalizeRingedToposHom B hT hS g X hX)

open Stacks.Cohomology.DerivedPullbackOfToposHom in
/-- **The relocalization of derived categories is a derived pullback**: the derived pullback
along `relocalizeRingedToposHom` is `relocalizeDerivedFunctor`, the pullback of modules being
exact. -/
def relocalizeDerivedPullbackIso :
    derivedPullback (X := smallEtaleRingedTopos B S hS
          ⟨_, isAlgebraicSpace_relocalize' B hT hS g X hX⟩)
        (Y := smallEtaleRingedTopos B T hT ⟨X, hX⟩) (relocalizeRingedToposHom B hT hS g X hX) ≅
      relocalizeDerivedFunctor B hT hS g X hX :=
  @Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso _ _ _ _ _ _ _ _ _
    (relocalizeModulesEquivalence B hT hS g X hX).functor
    (RingedToposHom.pullbackModules_additive (relocalizeRingedToposHom B hT hS g X hX))
    (Functor.additive_of_preserves_binary_products _)
    _ _ _
    (derivedPullbackComparison (relocalizeRingedToposHom B hT hS g X hX))
    (inferInstanceAs
      ((derivedPullback (relocalizeRingedToposHom B hT hS g X hX)).IsLeftDerivedFunctor
        (derivedPullbackComparison (relocalizeRingedToposHom B hT hS g X hX))
        (quasiIsoTarget (Y := smallEtaleRingedTopos B T hT ⟨X, hX⟩))))
    (relocalizePullbackModulesIso B hT hS g X hX)

open Stacks.Cohomology.DerivedPullbackOfToposHom in
/-- **The relocalization of derived categories carries the derived tensor product to the derived
tensor product**, `ρ(K ⊗^L L) ≅ ρ K ⊗^L ρ L` naturally in `(K, L)`. This is Stacks 07A4 for
`relocalizeRingedToposHom`, read through `relocalizeDerivedPullbackIso`. -/
def relocalizeDerivedTensorIso :
    Functor.uncurry.obj (smallEtaleDerivedTensor B T hT ⟨X, hX⟩) ⋙
        relocalizeDerivedFunctor B hT hS g X hX ≅
      (relocalizeDerivedFunctor B hT hS g X hX).prod (relocalizeDerivedFunctor B hT hS g X hX) ⋙
        Functor.uncurry.obj
          (smallEtaleDerivedTensor B S hS
          ⟨_, isAlgebraicSpace_relocalize' B hT hS g X hX⟩) :=
  Functor.isoWhiskerLeft _ (relocalizeDerivedPullbackIso B hT hS g X hX).symm ≪≫
    derivedPullbackTensorIso (relocalizeRingedToposHom B hT hS g X hX)
      (smallEtaleDerivedTensorProduct B S hS
        ⟨_, isAlgebraicSpace_relocalize' B hT hS g X hX⟩)
      (smallEtaleDerivedTensorProduct B T hT ⟨X, hX⟩) ≪≫
    Functor.isoWhiskerRight (NatIso.prod (relocalizeDerivedPullbackIso B hT hS g X hX)
      (relocalizeDerivedPullbackIso B hT hS g X hX)) _

/-- `relocalizeDerivedTensorIso` at one pair of objects. -/
def relocalizeDerivedTensorObjIso (K L : DerivedCategory (Modules.{u, u} B T hT X hX)) :
    (relocalizeDerivedFunctor B hT hS g X hX).obj
        (((smallEtaleDerivedTensor B T hT ⟨X, hX⟩).obj K).obj L) ≅
      ((smallEtaleDerivedTensor B S hS
          ⟨_, isAlgebraicSpace_relocalize' B hT hS g X hX⟩).obj
        ((relocalizeDerivedFunctor B hT hS g X hX).obj K)).obj
          ((relocalizeDerivedFunctor B hT hS g X hX).obj L) :=
  (relocalizeDerivedTensorIso B hT hS g X hX).app (K, L)

end AlgebraicGeometry.Space

end
