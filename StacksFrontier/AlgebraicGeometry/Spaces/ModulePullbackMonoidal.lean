module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrict
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallSiteMonoidalClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLeftDualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.CategoryTheory.Monoidal.Rigid
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeDualShortExact
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankLocalOnCover

/-!
# The inverse image of modules on algebraic spaces is a monoidal functor

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. The inverse image
`f^* = AlgebraicGeometry.Space.modulePullback B S hS f` of `𝒪`-modules on the small étale sites
(Stacks 03LU) is a **monoidal functor** for the tensor products
`AlgebraicGeometry.Space.modulesMonoidalCategory` on both sides: the comparison
`f^*(G ⊗ G') ≅ f^*G ⊗ f^*G'` of Stacks 03EL and `f^*𝒪_Y ≅ 𝒪_X` satisfy the coherence conditions.

As a consequence `f^*` carries duals to duals. If `ℰ` is a finite locally free `𝒪_Y`-module, then
`ℰ` has a dual in the monoidal category of `𝒪_Y`-modules, the dual `ℰ^∨ = 𝓗om(ℰ, 𝒪_Y)`
(Stacks 0FNY), and so the inverse image of the dual is the dual of the inverse image:

  `f^*(ℰ^∨) ≅ (f^*ℰ)^∨`.

## Main definitions

* `AlgebraicGeometry.Space.idMonoidalStrictToModules` and
  `AlgebraicGeometry.Space.idMonoidalModulesToStrict`: the identity functor of the `𝒪_X`-modules
  is monoidal in both directions between `AlgebraicGeometry.Space.modulesMonoidalCategory` and
  the strict monoidal structure `Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf` of
  Stacks 01CA, whose tensor product is the tensor product sheaf on the nose.
* `AlgebraicGeometry.Space.modulePullbackMonoidal`: **the inverse image along a morphism of
  algebraic spaces is a monoidal functor**.
* `AlgebraicGeometry.Space.modulePullbackDualIso`: **`f^*(ℰ^∨) ≅ (f^*ℰ)^∨`** for `ℰ` finite
  locally free.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_modulePullback_dual`: if `f^*ℰ` has rank `r`,
  so has `f^*(ℰ^∨)`.

## Implementation notes

The monoidal structure of Stacks 03EL is proved, with its coherences, for the pullback of modules
along an arbitrary morphism of ringed topoi,
`Stacks.SheafOfModules.RingedToposPullback.pullbackMonoidal`, and
`AlgebraicGeometry.Space.modulePullback` is that pullback for the morphism of small étale ringed
topoi of Stacks 03G8. That structure is stated for the strict monoidal structure of Stacks 01CA,
whereas the `𝒪_X`-modules on an algebraic space carry the localized one,
`AlgebraicGeometry.Space.modulesMonoidalCategory`, whose tensor product is only isomorphic to the
tensor product sheaf. The strict structure is *induced* from the localized one along the identity
functor (`CategoryTheory.Monoidal.induced`), which makes the identity monoidal from the strict to
the localized structure, and its inverse is monoidal in the other direction. The monoidal
structure on `f^*` is the composite `𝟭 ⋙ f^* ⋙ 𝟭` of the three.

The dual is the internal Hom `(ihom ℰ).obj (𝟙_ _)` of
`AlgebraicGeometry.Space.modulesMonoidalClosed`, which is
`AlgebraicGeometry.Space.smallEtaleInternalHomSmall B S hS F hF ℰ 𝒪_F` on the nose. For a finite
locally free `ℰ` it is identified with the right dual of
`AlgebraicGeometry.Space.hasRightDual_of_isFiniteLocallyFreeOnSite` by
`CategoryTheory.rightDualIsoIhomUnit`, and a monoidal functor carries the exact pairing of `ℰ` and
its right dual to an exact pairing (`CategoryTheory.ExactPairing.map`).

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The identity functor between the strict and the localized tensor products -/

/-- The identity functor of the `𝒪_X`-modules on an algebraic space is monoidal from the strict
monoidal structure of Stacks 01CA to `AlgebraicGeometry.Space.modulesMonoidalCategory`: the strict
structure is induced from the other one along it. -/
@[instance_reducible]
def idMonoidalStrictToModules (X : AlgebraicSpaces B S hS) :
    @Functor.Monoidal (Modules.{u, u} B S hS X.1 X.2) _
      (Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (smallEtaleRingedTopos B S hS X).O)
      (Modules.{u, u} B S hS X.1 X.2) _ (modulesMonoidalCategory B S hS X.1 X.2) (𝟭 _) :=
  letI := Stacks.SheafOfModules.Strict.monoidalCategory (smallEtaleRingedSite B S hS X.1 X.2).O.obj
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)
  letI := Stacks.SheafOfModules.Strict.monoidalCategoryStruct
    (smallEtaleRingedSite B S hS X.1 X.2).O.obj
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)
  (Monoidal.fromInducedCoreMonoidal (Stacks.SheafOfModules.Strict.toLocalizedMonoidal _ _)
    (Stacks.SheafOfModules.Strict.inducingFunctorData _ _)).toMonoidal

/-- The identity functor of the `𝒪_X`-modules on an algebraic space is monoidal from
`AlgebraicGeometry.Space.modulesMonoidalCategory` to the strict monoidal structure of
Stacks 01CA: it is the inverse of the identity equivalence, whose forward functor is
`AlgebraicGeometry.Space.idMonoidalStrictToModules`. -/
@[instance_reducible]
def idMonoidalModulesToStrict (X : AlgebraicSpaces B S hS) :
    @Functor.Monoidal (Modules.{u, u} B S hS X.1 X.2) _ (modulesMonoidalCategory B S hS X.1 X.2)
      (Modules.{u, u} B S hS X.1 X.2) _
      (Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (smallEtaleRingedTopos B S hS X).O)
      (𝟭 _) :=
  @CategoryTheory.Equivalence.inverseMonoidal _ _
    (Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (smallEtaleRingedTopos B S hS X).O)
    _ _ (modulesMonoidalCategory B S hS X.1 X.2) CategoryTheory.Equivalence.refl
    (idMonoidalStrictToModules X)

/-! ### The inverse image is monoidal -/

variable {X Y : AlgebraicSpaces B S hS}

/-- **The inverse image of `𝒪`-modules along a morphism of algebraic spaces is a monoidal
functor** for `AlgebraicGeometry.Space.modulesMonoidalCategory` on both sides. This is Stacks 03EL
with its coherences, `Stacks.SheafOfModules.RingedToposPullback.pullbackMonoidal`, read through the
identity functors between the strict and the localized tensor products. -/
@[instance_reducible]
def modulePullbackMonoidal (f : X ⟶ Y) :
    @Functor.Monoidal _ _ (modulesMonoidalCategory B S hS Y.1 Y.2) _ _
      (modulesMonoidalCategory B S hS X.1 X.2) (modulePullback B S hS f) :=
  @Functor.Monoidal.instComp _ _ (modulesMonoidalCategory B S hS Y.1 Y.2) _ _
    (Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (smallEtaleRingedTopos B S hS X).O)
    _ _ (modulesMonoidalCategory B S hS X.1 X.2) (𝟭 _ ⋙ modulePullback B S hS f) (𝟭 _)
    (@Functor.Monoidal.instComp _ _ (modulesMonoidalCategory B S hS Y.1 Y.2) _ _
      (Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (smallEtaleRingedTopos B S hS Y).O)
      _ _
      (Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (smallEtaleRingedTopos B S hS X).O)
      (𝟭 _) (modulePullback B S hS f) (idMonoidalModulesToStrict Y)
      (Stacks.SheafOfModules.RingedToposPullback.pullbackMonoidal
        (smallEtaleRingedToposModulesHom B S hS f)))
    (idMonoidalStrictToModules X)

/-! ### The inverse image of a dual -/

attribute [local instance] modulesMonoidalCategory modulesMonoidalClosed

/-- **The inverse image of the dual of a finite locally free module is the dual of its inverse
image**: `f^*(ℰ^∨) ≅ (f^*ℰ)^∨` for a morphism `f : X ⟶ Y` of algebraic spaces and a finite locally
free `𝒪_Y`-module `ℰ`, the dual being the internal Hom `𝓗om(ℰ, 𝒪)` into the structure sheaf. -/
def modulePullbackDualIso (f : X ⟶ Y) (E : Modules.{u, u} B S hS Y.1 Y.2)
    (hE : SheafOfModules.IsFiniteLocallyFreeOnSite E) :
    (modulePullback B S hS f).obj ((ihom E).obj (𝟙_ _)) ≅
      (ihom ((modulePullback B S hS f).obj E)).obj (𝟙_ _) :=
  letI : BraidedCategory (Modules.{u, u} B S hS X.1 X.2) :=
    RingedSite.modulesBraided (smallEtaleRingedSite B S hS X.1 X.2)
  letI : BraidedCategory (Modules.{u, u} B S hS Y.1 Y.2) :=
    RingedSite.modulesBraided (smallEtaleRingedSite B S hS Y.1 Y.2)
  letI := hasRightDual_of_isFiniteLocallyFreeOnSite B S hS Y.1 Y.2 E hE
  letI := modulePullbackMonoidal f
  letI := ExactPairing.map (modulePullback B S hS f) E Eᘁ
  (modulePullback B S hS f).mapIso (rightDualIsoIhomUnit E Eᘁ).symm ≪≫
    rightDualIsoIhomUnit _ _

/-- **The inverse image of the dual of a finite locally free module has the rank of the inverse
image of the module**: if `f^*ℰ` has rank `r`, so has `f^*(ℰ^∨) ≅ (f^*ℰ)^∨`. -/
theorem isFiniteLocallyFreeOfRank_modulePullback_dual (f : X ⟶ Y)
    (E : Modules.{u, u} B S hS Y.1 Y.2) (hE : SheafOfModules.IsFiniteLocallyFreeOnSite E) {r : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2)
      ((modulePullback B S hS f).obj E) r) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2)
      ((modulePullback B S hS f).obj ((ihom E).obj (𝟙_ _))) r :=
  RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _ (modulePullbackDualIso f E hE).symm
    (isFiniteLocallyFreeOfRank_dual B S hS X.1 X.2 _ hr)

end AlgebraicGeometry.Space

end
