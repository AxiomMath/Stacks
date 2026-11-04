module

public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleNatIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The abelian sheaf underlying a direct image of modules

Let `f : X ⟶ Y` be a relatively representable morphism of algebraic spaces over a scheme `S`.
The direct image of `𝒪_X`-modules, `AlgebraicGeometry.Space.modulePushforward`, and the direct
image of abelian sheaves on the small étale sites,
`AlgebraicGeometry.Space.smallEtaleAbelianPushforward`, are built from unrelated data: the first
transports the internal module structure along the direct image of *sheaves of sets* of
Stacks 03G2, part (1) and then restricts scalars along the structure map `f♯` of Stacks 03G8,
while the second is restriction of sections along base change of étale charts.  This file
identifies the abelian sheaf underlying the first with the second applied to the abelian sheaf
underlying the module:

`(f_*M)^{ab} ≅ f_*(M^{ab})`.

This is the compatibility of Stacks 03D1 with the forgetful functor to abelian sheaves, read on
the small étale sites of algebraic spaces, for any relatively representable `f`.

## Main results

* `Stacks.Sheaves.ToposPullback.pullbackModuleCompToSheafIso`: the sites-level statement.  For a
  finite-product-preserving functor `Φ` of sheaves of sets isomorphic to restriction along a
  continuous functor `G` of sites, the abelian sheaf underlying the inverse image of a sheaf of
  modules along `Φ` is the restriction along `G` of the abelian sheaf underlying the module.
* `AlgebraicGeometry.Space.modulePushforwardCompToSheafIso`: the same for
  `AlgebraicGeometry.Space.modulePushforward` against
  `AlgebraicGeometry.Space.smallEtaleAbelianPushforward`.
* `AlgebraicGeometry.Space.modulePullbackCompToSheafIso`: the companion for the pullback of
  modules along an *étale* morphism, against restriction of abelian sheaves along
  postcomposition of étale charts.

## Implementation notes

The pullback companion is stated against restriction along postcomposition of étale charts,
which is what the pullback of modules *is* along an étale morphism by Stacks Equation 03LW, and
not against `AlgebraicGeometry.Space.smallEtaleAbelianInverseImage`, the left adjoint of
restriction along chart base change.

## References

* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sheaves.ToposPullback

universe ww vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww})]
  (G : C ⥤ D) [G.IsContinuous J K] (O : Sheaf K RingCat.{ww})
  (Φ : Sheaf K (Type ww) ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]

/-- **The abelian sheaf underlying an inverse image of modules.**  Let `Φ` be a
finite-product-preserving functor of categories of sheaves of sets which is isomorphic to
restriction along a continuous functor `G` of sites.  Then the abelian sheaf underlying the
inverse image along `Φ` of a sheaf of `O`-modules is the restriction along `G` of the abelian
sheaf underlying that module.

This is the compatibility of Stacks 03D1 with the forgetful functor to abelian sheaves. -/
def pullbackModuleCompToSheafIso (ε : Φ ≅ G.sheafPushforwardContinuous (Type ww) J K) :
    pullbackModuleFunctor J Φ O ⋙ SheafOfModules.toSheaf.{ww} (pullbackRingSheaf J Φ O) ≅
      SheafOfModules.toSheaf.{ww} O ⋙ G.sheafPushforwardContinuous AddCommGrpCat.{ww} J K :=
  Functor.isoWhiskerRight
      (pullbackModuleFunctorIsoOfNatIso J O ε (pullbackRingSheafMapOfNatTrans J O ε.hom)
        (ringSheafMap_pullbackRingSheafMapOfNatTrans J O ε.hom))
      (SheafOfModules.toSheaf.{ww} (pullbackRingSheaf J Φ O)) ≪≫
    Functor.isoWhiskerRight (restrictionModuleIso J K G O)
      (SheafOfModules.toSheaf.{ww}
        (pullbackRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K) O))

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The abelian sheaf underlying the direct image of an `𝒪_X`-module is the direct image of
the abelian sheaf underlying it.**  For a relatively representable morphism `f : X ⟶ Y` of
algebraic spaces over `S`, the direct image of `𝒪_X`-modules of Stacks 03LU followed by the
forgetful functor to abelian sheaves on the small étale site of `Y` is the forgetful functor
followed by the direct image of abelian sheaves.

This is the compatibility of Stacks 03D1 with the forgetful functor to abelian sheaves. -/
@[sga "4 IV 13.2.3" "special case"]
def modulePushforwardCompToSheafIso (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    modulePushforward B S hS f ⋙ SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y) ≅
      SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X) ⋙
        smallEtaleAbelianPushforward.{u} B S hS f hf :=
  letI := (smallBaseChange_isMorphismOfSites B S hS f hf).toIsContinuous
  Stacks.Sheaves.ToposPullback.pullbackModuleCompToSheafIso
    (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)
    (smallBaseChange B S hS f hf) (structureRingSheaf B S hS X)
    (smallEtaleDirectImage B S hS f) (smallEtaleDirectImageIsoSheafPushforward B S hS f hf)

/-- **The abelian sheaf underlying the pullback of an `𝒪_Y`-module along an étale morphism is
the restriction of the abelian sheaf underlying it.**  For an étale morphism `f : X ⟶ Y` of
algebraic spaces over `S`, the pullback of `𝒪_Y`-modules of Stacks 03LU followed by the
forgetful functor to abelian sheaves on the small étale site of `X` is the forgetful functor
followed by restriction of abelian sheaves along postcomposition of étale charts with `f`. -/
def modulePullbackCompToSheafIso (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    modulePullback B S hS f ⋙ SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X) ≅
      SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y) ⋙
        (smallEtalePostcomp B S hS f hf).sheafPushforwardContinuous AddCommGrpCat.{u}
          (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) :=
  Functor.isoWhiskerRight (modulePullbackIsoEtaleModulePullback B S hS f hf)
    (SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X))

end AlgebraicGeometry.Space

end
