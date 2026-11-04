module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived pullback of modules on algebraic spaces exists and is computed by K-flat complexes

For a morphism `f : X ⟶ Y` of algebraic spaces, `Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` of Stacks 06YY exists
with no hypothesis on `f`, is triangulated, and is computed by degreewise pullback on K-flat
complexes with flat terms.

## Main results

* `AlgebraicGeometry.Space.hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy_mk`: `Lf^*`
  exists for every morphism of algebraic spaces written as pairs `⟨F, hF⟩`; the general instance
  is `AlgebraicGeometry.Space.hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy`.
* `Lf^*` is a triangulated functor: the base's
  `AlgebraicGeometry.Space.isTriangulated_smallEtaleDerivedModulePullback`, imported here.
* `AlgebraicGeometry.Space.smallEtaleModuleKFlat_hasResolutions`: Stacks 06YS, every complex of
  `𝒪_Y`-modules receives a quasi-isomorphism from a K-flat complex with flat terms.
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedModulePullbackComparison_app`: the computation
  clause of Stacks 06YY, `Lf^*K = f^*K` for `K` K-flat with flat terms.
* `AlgebraicGeometry.Space.smallEtaleModuleKFlat_of_isStrictlyLE`: a bounded above complex of flat
  modules is in that class.
* `AlgebraicGeometry.Space.smallEtaleModuleKFlat_pullbackMapHomotopy`: Stacks 0G7E, degreewise
  pullback preserves the class.

## Implementation notes

The derived pullback along a morphism of ringed topoi exists with no hypothesis,
`Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy`: the
resolving half is Stacks 06YS at a site whose objects lie above the module universe,
`Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution_ofSize`, which resolves by flat
modules and so needs no smallness of the site; the exactness half is
`Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat`.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat hasResolutions_isKFlat)

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-- **The derived pullback exists along every morphism of algebraic spaces**, for spaces written
as pairs `⟨F, hF⟩`.  This is `hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy`; it is
stated again so that instance search finds it at objects such as `⟨yoneda.obj U, _⟩`, where the
reducible unfolding of the goal exposes `F` in place of a projection of the space. -/
instance hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy_mk
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    {hG : IsAlgebraicSpace B S hS G} (f : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩) :
    (smallEtaleModulePullbackOnHomotopy B S hS f).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS ⟨G, hG⟩) :=
  hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS f

variable (Y) in
/-- The K-flat complexes of `𝒪_Y`-modules with flat terms, as a property of objects of the
unbounded homotopy category: the class
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat` of the small étale ringed
topos of `Y`, on which the derived pullback is computed by degreewise pullback. -/
abbrev smallEtaleModuleKFlat :
    ObjectProperty (HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ)) :=
  IsKFlat (Y := smallEtaleRingedTopos B S hS Y)

variable (Y) in
/-- **Stacks 06YS for an algebraic space.**  Every complex of `𝒪_Y`-modules on the small étale
site receives a quasi-isomorphism from a K-flat complex with flat terms. -/
theorem smallEtaleModuleKFlat_hasResolutions
    (M : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ)) :
    ∃ (K : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ)) (_ : smallEtaleModuleKFlat B S hS Y K) (s : K ⟶ M),
      smallEtaleModuleQuasiIso B S hS Y s :=
  hasResolutions_isKFlat (Y := smallEtaleRingedTopos B S hS Y) M

/-- **Stacks 06YY, the computation, for a morphism of algebraic spaces.**  The canonical
comparison `Lf^*K ⟶ f^*K` is an isomorphism at a K-flat complex `K` of `𝒪_Y`-modules with flat
terms: such a complex computes the derived pullback. -/
theorem isIso_smallEtaleDerivedModulePullbackComparison_app (f : X ⟶ Y)
    (K : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ))
    (hK : smallEtaleModuleKFlat B S hS Y K) :
    IsIso ((smallEtaleDerivedModulePullbackComparison B S hS f).app K) :=
  isIso_derivedPullbackComparison_app (smallEtaleRingedToposHom B S hS f)
    (IsKFlat (Y := smallEtaleRingedTopos B S hS Y))
    (hasResolutions_isKFlat (Y := smallEtaleRingedTopos B S hS Y))
    (pullbackInvertsQuasiIso_isKFlat (smallEtaleRingedToposHom B S hS f)) K hK

attribute [local instance] Stacks.SheafOfModules.KFlatResolution.hasTotal_ofSize in
variable (Y) in
/-- **A bounded above complex of flat `𝒪_Y`-modules is K-flat with flat terms** (Stacks 06YQ):
it lies in the class `smallEtaleModuleKFlat`, so it computes the derived pullback. -/
theorem smallEtaleModuleKFlat_of_isStrictlyLE
    (K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ) (n : ℤ)
    [K.IsStrictlyLE n]
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Y).O) (K.X i)) :
    smallEtaleModuleKFlat B S hS Y ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) :=
  ⟨CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE _ K n
    (Stacks.SheafOfModules.KFlatResolution.hF_sheafTensor_ofSize _)
    (Stacks.SheafOfModules.KFlatResolution.hexact_sheafOfModules_ofSize _) fun q ↦
      Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat_ofSize _ _ (hflat q) q,
    hflat⟩

/-- **Stacks 0G7E for a morphism of algebraic spaces.**  Degreewise pullback along `f` carries a
K-flat complex of `𝒪_Y`-modules with flat terms to a K-flat complex of `𝒪_X`-modules with flat
terms. -/
theorem smallEtaleModuleKFlat_pullbackMapHomotopy (f : X ⟶ Y)
    (K : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ))
    (hK : smallEtaleModuleKFlat B S hS Y K) :
    smallEtaleModuleKFlat B S hS X
      ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
        (smallEtaleRingedToposHom B S hS f)).obj K) :=
  Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy
    (smallEtaleRingedToposHom B S hS f) K hK

end AlgebraicGeometry.Space

end
