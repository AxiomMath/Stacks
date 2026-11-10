module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToSheafPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSliceSiteInverse
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence

/-!
# Quasi-coherent coefficients read on the spaces-étale site of an étale object

Let `X` be an algebraic space over a scheme `S` and let `Q` be an object of its spaces-étale
site, that is, an algebraic space étale over `X`.  A quasi-coherent `𝒪_X`-module `ℳ` restricts
to the localization at `Q` and, through the identification of that localization with the
spaces-étale site of `Q`
(`AlgebraicGeometry.Space.SpacesEtale.sheafOverEquivSmall`), is read there as a quasi-coherent
`𝒪_Q`-module.  This file performs that reading, both for the module and for its underlying
abelian sheaf.

No comparison of structure sheaves intervenes.  The two composites
`sliceToSmall ⋙ toSpaces` and `Over.forget ⋙ toSpaces` are equal functors on the nose
(`AlgebraicGeometry.Space.SpacesEtale.sliceToSmall_comp_toSpaces`), and the round trip
`smallToSlice ⋙ sliceToSmall` is the identity on the nose
(`AlgebraicGeometry.Space.SpacesEtale.smallToSlice_comp_sliceToSmall`); since the structure
sheaf of the ringed spaces-étale site is the sheaf of global regular functions of the underlying
algebraic space, the transported structure sheaf is the structure sheaf of `Q` *by definition*.
So the reindexing of [Stacks, Tag 03DM] applies with the identity as its comparison of rings,
and the invariance of quasi-coherence under restriction of scalars along an isomorphism of
sheaves of rings — which this library does not have — is not needed.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.moduleToSmall` reads a module on the ringed spaces-étale
  site of `X` as a module on that of `Q`.
* `AlgebraicGeometry.Space.SpacesEtale.abelianToSmall` is the same reading for abelian sheaves,
  by restriction along `smallToSlice`.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isQuasicoherentOnSite_moduleToSmall`: **the reading of a
  quasi-coherent module is quasi-coherent.**
* `AlgebraicGeometry.Space.SpacesEtale.abelianRestrictToSmallIso`: restriction along
  `smallToSlice` computes the identification of sheaves on the localization with sheaves on the
  spaces-étale site of `Q`.
* `AlgebraicGeometry.Space.SpacesEtale.exists_isQuasicoherentOnSite_toSheaf_iso`: **the
  coefficients carried to the spaces-étale site of `Q` are again the underlying abelian sheaf of
  a quasi-coherent module**, which is the form the alternating Čech recursion of
  [Stacks, Tag 0728] consumes.

## References

* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 04LZ](https://stacks.math.columbia.edu/tag/04LZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (Q : SpacesEtale B S hS X)

/-- The structure sheaf of the ringed spaces-étale site, with commutativity forgotten. -/
abbrev spacesEtaleRing : Sheaf (topology B S hS X) RingCat.{u + 1} :=
  ringSheaf (spacesEtaleRingedSite B S hS X).O

/-- **A module on the ringed spaces-étale site of `X`, read on that of `Q`.**  It is the
restriction of the module to the localization at `Q`, reindexed along the identification of that
localization with the spaces-étale site of `Q`; the transported structure sheaf is the structure
sheaf of `Q` by definition, so no comparison of rings intervenes. -/
abbrev moduleToSmall (M : SheafOfModules.{u + 1} (spacesEtaleRing B S hS X)) :
    SheafOfModules.{u + 1} (spacesEtaleRing B S hS Q.obj.left) :=
  (SheafOfModules.pushforward.{u + 1} (𝟙 (Stacks.SheafOfModules.reindexRing
      (topology B S hS Q.obj.left) (sliceEquivSmall B S hS Q).symm
      ((spacesEtaleRing B S hS X).over Q)))).obj (M.over Q)

/-- **The reading of a quasi-coherent module is quasi-coherent.**  Restriction to a slice
preserves quasi-coherence, and so does reindexing along an equivalence of ringed sites. -/
theorem isQuasicoherentOnSite_moduleToSmall
    (M : SheafOfModules.{u + 1} (spacesEtaleRing B S hS X)) (hM : M.IsQuasicoherentOnSite) :
    (moduleToSmall B S hS X Q M).IsQuasicoherentOnSite :=
  have : (M.over Q).IsQuasicoherentOnSite :=
    Stacks.SheafOfModules.isQuasicoherentOnSite_over M hM Q
  Stacks.SheafOfModules.isQuasicoherentOnSite_reindex (sliceEquivSmall B S hS Q).symm
    ((spacesEtaleRing B S hS X).over Q) (M.over Q)

/-- Restriction of abelian sheaves along `smallToSlice`: the reading on the spaces-étale site of
`Q` of a sheaf on the localization at `Q`. -/
abbrev abelianRestrictToSmall :
    Sheaf ((topology B S hS X).over Q) AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology B S hS Q.obj.left) AddCommGrpCat.{u + 1} :=
  (smallToSlice B S hS Q).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (topology B S hS Q.obj.left) ((topology B S hS X).over Q)

/-- An abelian sheaf on the spaces-étale site of `X`, read on that of `Q`. -/
abbrev abelianToSmall (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    Sheaf (topology B S hS Q.obj.left) AddCommGrpCat.{u + 1} :=
  (abelianRestrictToSmall B S hS X Q).obj
    (((topology B S hS X).overPullback AddCommGrpCat.{u + 1} Q).obj F)

/-- **Restriction along `smallToSlice` computes the identification of sheaves on the
localization at `Q` with sheaves on the spaces-étale site of `Q`.**  Restricting along
`sliceToSmall` and then along `smallToSlice` is restriction along the identity, so the composite
of the identification with that restriction is the identity functor; the comparison is therefore
the restriction of the unit. -/
theorem abelianRestrictToSmall_obj_inverse_obj
    (A : Sheaf (topology B S hS Q.obj.left) AddCommGrpCat.{u + 1}) :
    (abelianRestrictToSmall B S hS X Q).obj
        ((sheafOverEquivSmall B S hS Q AddCommGrpCat.{u + 1}).inverse.obj A) = A :=
  rfl

/-- **Restriction along `smallToSlice` computes the identification.** -/
def abelianRestrictToSmallIso
    (Z : Sheaf ((topology B S hS X).over Q) AddCommGrpCat.{u + 1}) :
    (abelianRestrictToSmall B S hS X Q).obj Z ≅
      (sheafOverEquivSmall B S hS Q AddCommGrpCat.{u + 1}).functor.obj Z :=
  ((abelianRestrictToSmall B S hS X Q).mapIso
      ((sheafOverEquivSmall B S hS Q AddCommGrpCat.{u + 1}).unitIso.app Z)).trans
    (eqToIso (abelianRestrictToSmall_obj_inverse_obj B S hS X Q
      ((sheafOverEquivSmall B S hS Q AddCommGrpCat.{u + 1}).functor.obj Z)))

/-- **The abelian reading of a module is the reading of the module, read as an abelian sheaf.**
Both are the restriction of the underlying abelian presheaf along `smallToSlice ⋙ Over.forget`;
the comparison is built from the sheaf-level forgetful comparison
`Stacks.SheafOfModules.toSheafPushforwardIso` rather than asserted. -/
def abelianToSmallToSheafIso (M : SheafOfModules.{u + 1} (spacesEtaleRing B S hS X)) :
    abelianToSmall B S hS X Q
        ((SheafOfModules.toSheaf.{u + 1} (spacesEtaleRing B S hS X)).obj M) ≅
      (SheafOfModules.toSheaf.{u + 1} (spacesEtaleRing B S hS Q.obj.left)).obj
        (moduleToSmall B S hS X Q M) :=
  ((abelianRestrictToSmall B S hS X Q).mapIso
      (Stacks.SheafOfModules.toSheafPushforwardIso
        (𝟙 ((spacesEtaleRing B S hS X).over Q)) M).symm).trans
    (Stacks.SheafOfModules.toSheafPushforwardIso
      (𝟙 (Stacks.SheafOfModules.reindexRing (topology B S hS Q.obj.left)
        (sliceEquivSmall B S hS Q).symm ((spacesEtaleRing B S hS X).over Q)))
      (M.over Q)).symm

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for sheaves of modules on the slice and small spaces-étale sites is heavy
/-- **The coefficients carried to the spaces-étale site of `Q` are again the underlying abelian
sheaf of a quasi-coherent module**, which is the form the alternating Čech recursion of
[Stacks, Tag 0728] consumes. -/
theorem exists_isQuasicoherentOnSite_toSheaf_iso
    (M : SheafOfModules.{u + 1} (spacesEtaleRing B S hS X)) (hM : M.IsQuasicoherentOnSite) :
    ∃ M' : SheafOfModules.{u + 1} (spacesEtaleRing B S hS Q.obj.left),
      M'.IsQuasicoherentOnSite ∧
        Nonempty ((sheafOverEquivSmall B S hS Q AddCommGrpCat.{u + 1}).functor.obj
          (((topology B S hS X).overPullback AddCommGrpCat.{u + 1} Q).obj
            ((SheafOfModules.toSheaf.{u + 1} (spacesEtaleRing B S hS X)).obj M)) ≅
          (SheafOfModules.toSheaf.{u + 1} (spacesEtaleRing B S hS Q.obj.left)).obj M') :=
  ⟨moduleToSmall B S hS X Q M, isQuasicoherentOnSite_moduleToSmall B S hS X Q M hM,
    ⟨(abelianRestrictToSmallIso B S hS X Q
        (((topology B S hS X).overPullback AddCommGrpCat.{u + 1} Q).obj
          ((SheafOfModules.toSheaf.{u + 1} (spacesEtaleRing B S hS X)).obj M))).symm.trans
      (abelianToSmallToSheafIso B S hS X Q M)⟩⟩

end AlgebraicGeometry.Space.SpacesEtale

end
