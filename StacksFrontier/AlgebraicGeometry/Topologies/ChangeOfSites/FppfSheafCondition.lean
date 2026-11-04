module

public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfToEtaleSquares

/-!
# When a big étale sheaf is already an fppf sheaf

Let `B` be a chosen big fppf site, let `S` be one of its schemes, and let `ε_S` be the
change-of-topology morphism from the big fppf topos over `S` to the big étale topos over `S`.
The two sites share their slice category over `S` and the direct image of `ε_S` is restriction
along the identity functor, so it is fully faithful. Consequently the unit of
`ε_S⁻¹ ⊣ ε_{S,*}` at a big étale sheaf `G` is an isomorphism exactly when the underlying
presheaf of `G` already satisfies the fppf sheaf condition.

For `G = π_S⁻¹ℱ` the inverse image of a sheaf on the small étale site of `S`, whose sections
over `f : X ⟶ S` are the global sections of `f_small⁻¹ℱ` by Stacks 09XN, this says that the
rule `X ↦ Γ(X, f_small⁻¹ℱ)` is `ε_S⁻¹π_S⁻¹ℱ` precisely when it is an fppf sheaf.

## Main results

* `Stacks.Sites.sheafPushforwardIdFullyFaithful` — restriction of sheaves along the identity
  functor between two topologies on one category is fully faithful.
* `Stacks.Sites.isIso_sheafAdjunctionContinuousId_unit_app_iff` — the unit of the associated
  adjunction is invertible at a sheaf for the coarser topology exactly when that sheaf is a
  sheaf for the finer one.
* `AlgebraicGeometry.fppfToBigEtale_pushforwardFullyFaithful` and
  `AlgebraicGeometry.isIso_fppfToBigEtale_unit_app_iff` — the two statements for `ε_S`.
* `AlgebraicGeometry.fppfToBigEtale_inverseImageObjIso` — a big étale sheaf over `S` which is an
  fppf sheaf has the same underlying presheaf as its inverse image under `ε_S`.

## Implementation notes

A sheaf is a presheaf together with a property, so a morphism of sheaves is a morphism of the
underlying presheaves; restriction along the identity functor changes neither, which is why it
is fully faithful. The equivalence with the fppf sheaf condition is then the standard
description of the unit of a reflection: it is invertible exactly on the essential image of the
fully faithful right adjoint, and a presheaf lies in that image exactly when it satisfies the
finer sheaf condition.

## References

* [Stacks Project, Tag 0DDL](https://stacks.math.columbia.edu/tag/0DDL)
* [Stacks Project, Tag 0DDM](https://stacks.math.columbia.edu/tag/0DDM)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.Sites

variable {C : Type (u + 1)} [Category.{u} C] (J K : GrothendieckTopology C)
  [(𝟭 C).IsContinuous J K]

/-- Restriction of `K`-sheaves along the identity functor, viewed as `J`-sheaves, is fully
faithful: a morphism of the restrictions is a morphism of the underlying presheaves. -/
public def sheafPushforwardIdFullyFaithful :
    ((𝟭 C).sheafPushforwardContinuous (Type (u + 1)) J K).FullyFaithful where
  preimage {_G _H} f := ObjectProperty.homMk f.hom

/-- The unit of the adjunction attached to the identity functor is invertible at a `J`-sheaf
exactly when that sheaf already satisfies the `K`-sheaf condition. -/
public theorem isIso_sheafAdjunctionContinuousId_unit_app_iff
    [((𝟭 C).sheafPushforwardContinuous (Type (u + 1)) J K).IsRightAdjoint]
    (G : Sheaf J (Type (u + 1))) :
    IsIso (((𝟭 C).sheafAdjunctionContinuous (Type (u + 1)) J K).unit.app G) ↔
      Presheaf.IsSheaf K G.obj := by
  have := (sheafPushforwardIdFullyFaithful J K).full
  have := (sheafPushforwardIdFullyFaithful J K).faithful
  rw [Adjunction.isIso_unit_app_iff_mem_essImage]
  refine ⟨fun ⟨H, ⟨e⟩⟩ => ?_, fun h => ⟨⟨G.obj, h⟩, ⟨Iso.refl _⟩⟩⟩
  exact (Presheaf.isSheaf_of_iso_iff ((sheafToPresheaf J (Type (u + 1))).mapIso e)).1 H.property

end Stacks.Sites

namespace AlgebraicGeometry

open Stacks.Sites

variable (B : BigFppfSite.{u}) (S : B.Schemes)

/-- The direct image of `ε_S` is fully faithful: the big fppf and big étale sites share their
slice over `S`, so a morphism of big étale sheaves is a morphism of the underlying
presheaves. -/
public def fppfToBigEtale_pushforwardFullyFaithful :
    (fppfToBigEtaleMorphism B S).pushforward.FullyFaithful := by
  dsimp only [fppfToBigEtaleMorphism]
  exact sheafPushforwardIdFullyFaithful _ _

/-- The unit of `ε_S⁻¹ ⊣ ε_{S,*}` at a big étale sheaf `G` over `S` is an isomorphism exactly
when the underlying presheaf of `G` satisfies the fppf sheaf condition. -/
public theorem isIso_fppfToBigEtale_unit_app_iff
    (G : Sheaf (BigEtaleOver.topology (associatedBigEtaleSite B) S.1 S.2)
      (Type (u + 1))) :
    IsIso ((fppfToBigEtaleMorphism B S).adj.unit.app G) ↔
      Presheaf.IsSheaf (B.topology.over S) G.obj := by
  dsimp only [fppfToBigEtaleMorphism]
  exact isIso_sheafAdjunctionContinuousId_unit_app_iff _ _ G

/-- A big étale sheaf over `S` whose underlying presheaf is an fppf sheaf is its own inverse
image under `ε_S`: the comparison is the unit of `ε_S⁻¹ ⊣ ε_{S,*}`. -/
public def fppfToBigEtale_inverseImageObjIso
    (G : Sheaf (BigEtaleOver.topology (associatedBigEtaleSite B) S.1 S.2)
      (Type (u + 1)))
    (hG : Presheaf.IsSheaf (B.topology.over S) G.obj) :
    G.obj ≅ ((fppfToBigEtaleMorphism B S).inverseImage.obj G).obj :=
  have := (isIso_fppfToBigEtale_unit_app_iff B S G).2 hG
  (sheafToPresheaf (BigEtaleOver.topology (associatedBigEtaleSite B) S.1 S.2)
    (Type (u + 1))).mapIso (asIso ((fppfToBigEtaleMorphism B S).adj.unit.app G))

end AlgebraicGeometry

end
