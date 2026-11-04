module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalContinuousFunctor
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RingedMorphismSituation

/-!
# Morphisms between ringed simplicial sites, continuous case

A ringed simplicial site is a simplicial site together with a sheaf of rings on its total site.
A morphism between two of them is a morphism `h` of the underlying simplicial sites together
with a homomorphism of sheaves of rings from the inverse image of the target ring sheaf to the
source ring sheaf, taken along the induced map of total sites. Equivalently, it is a
homomorphism from the target ring sheaf to the direct image of the source ring sheaf.

This file treats case (A) of Stacks 09WE, where the map of total sites is a continuous functor.
The direct image `h_{total, *}` of a sheaf of rings is restriction along that functor, and the
inverse image `h_{total}^{-1}` is its left adjoint, the sheafified left Kan extension of Stacks
00YV; the homomorphism of sheaves of rings is stored in inverse-image form. The sheaves of rings
are sheaves of not necessarily commutative rings, all at the universe of the total sites.

## Main definitions

* `CategoryTheory.SimplicialSite.Morphism.totalInverseImageRing` and `.totalPushforwardRing`:
  the inverse image and the direct image of a sheaf of rings along the total functor.
* `CategoryTheory.SimplicialSite.RingedMorphism`: a morphism between ringed simplicial sites,
  with the homomorphism of sheaves of rings in inverse-image form.
* `CategoryTheory.SimplicialSite.RingedMorphism.toSimplicialSiteMorphism`: its underlying
  morphism between the simplicial-site situations.
* `CategoryTheory.SimplicialSite.RingedMorphism.ringHomEquiv`: the bijection between the
  inverse-image and the direct-image form of that homomorphism.
* `CategoryTheory.SimplicialSite.RingedMorphism.ringHomPushforward`: the homomorphism of
  sheaves of rings in direct-image form.
* `CategoryTheory.SimplicialSite.RingedMorphism.ofPushforward`: the morphism between ringed
  simplicial sites determined by a homomorphism in direct-image form.

## Main results

* `CategoryTheory.SimplicialSite.RingedMorphism.ringHomPushforward_eq`: the direct-image form
  is the unit of the ring-level adjunction followed by the direct image of the inverse-image
  form.

## References

* [Stacks Project, Tag 0DGZ](https://stacks.math.columbia.edu/tag/0DGZ)
* [Stacks Project, Tag 0D95](https://stacks.math.columbia.edu/tag/0D95)
* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace CategoryTheory

namespace SimplicialSite

namespace Morphism

variable {C C' : SimplicialSite.{u}}

/-- The direct image, along the total functor of a morphism between simplicial sites, of a
sheaf of rings on the total site of the source. -/
abbrev totalPushforwardRing (h : SimplicialSite.Morphism C C')
    (O : Sheaf C.totalTopology RingCat.{u}) :
    Sheaf C'.totalTopology RingCat.{u} :=
  (h.totalFunctor.sheafPushforwardContinuous RingCat.{u} C'.totalTopology C.totalTopology).obj O

/-- The inverse image, along the total functor of a morphism between simplicial sites, of a
sheaf of rings on the total site of the target: the left adjoint of the direct image. -/
abbrev totalInverseImageRing (h : SimplicialSite.Morphism C C')
    (O' : Sheaf C'.totalTopology RingCat.{u}) :
    Sheaf C.totalTopology RingCat.{u} :=
  (Functor.sheafPullbackConstruction.sheafPullback h.totalFunctor RingCat.{u}
    C'.totalTopology C.totalTopology).obj O'

/-- The adjunction between the inverse image and the direct image of sheaves of rings along the
total functor. -/
def totalRingImageAdjunction (h : SimplicialSite.Morphism C C') :
    Functor.sheafPullbackConstruction.sheafPullback h.totalFunctor RingCat.{u}
        C'.totalTopology C.totalTopology ⊣
      h.totalFunctor.sheafPushforwardContinuous RingCat.{u}
        C'.totalTopology C.totalTopology :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous h.totalFunctor RingCat.{u}
    C'.totalTopology C.totalTopology

/-! ### The two adjunctions of sheaves of rings along the total functor agree

The morphism of total topoi has a direct image of sheaves of rings, got by transporting the ring
structure along restriction of sheaves of *sets*; restriction of sheaves of rings along the total
functor is a different functor with the same underlying sheaf of sets. The two are identified
below, and the identification carries the two adjunctions onto each other. -/

/-- The direct image of a sheaf of rings along the morphism of total topoi *is* its restriction
along the total functor: the sections agree on the nose, and the ring structure transported
along restriction of sheaves of sets is the original one. The comparison is the identity on
underlying sheaves of sets. -/
def totalPushforwardRingIso (h : SimplicialSite.Morphism C C') :
    (SimplicialSiteMorphism.ofMorphismOfSites h).totalPushforwardRingFunctor ≅
      h.totalFunctor.sheafPushforwardContinuous RingCat.{u}
        C'.totalTopology C.totalTopology :=
  NatIso.ofComponents
    (fun O => restrictionRingIso C'.totalTopology C.totalTopology h.totalFunctor O)
    (fun a => restrictionRingIso_naturality C'.totalTopology C.totalTopology h.totalFunctor a)

/-- The adjunction of the morphism of total topoi, read with restriction of sheaves of rings
along the total functor as its right adjoint. -/
def totalRestrictRingAdjunction (h : SimplicialSite.Morphism C C') :
    (SimplicialSiteMorphism.ofMorphismOfSites h).totalInverseImageRingFunctor ⊣
      h.totalFunctor.sheafPushforwardContinuous RingCat.{u}
        C'.totalTopology C.totalTopology :=
  (ringImageAdjunction
    (SimplicialSiteMorphism.ofMorphismOfSites h).totalMorphism).ofNatIsoRight
      h.totalPushforwardRingIso

/-- The inverse image of sheaves of rings along the morphism of total topoi is the sheafified
left Kan extension of sheaves of rings along the total functor: both are left adjoint to
restriction, by `totalRestrictRingAdjunction` and by `totalRingImageAdjunction`. -/
def totalInverseImageRingIso (h : SimplicialSite.Morphism C C') :
    (SimplicialSiteMorphism.ofMorphismOfSites h).totalInverseImageRingFunctor ≅
      Functor.sheafPullbackConstruction.sheafPullback h.totalFunctor RingCat.{u}
        C'.totalTopology C.totalTopology :=
  Adjunction.leftAdjointUniq h.totalRestrictRingAdjunction h.totalRingImageAdjunction

/-- The hom-bijection of the adjunction of sheaves of rings along the total functor is the
hom-bijection of the adjunction of the morphism of total topoi, conjugated by the comparisons
`totalInverseImageRingIso` and `totalPushforwardRingIso`. -/
theorem totalRingImageAdjunction_homEquiv (h : SimplicialSite.Morphism C C')
    (O' : Sheaf C'.totalTopology RingCat.{u}) (O : Sheaf C.totalTopology RingCat.{u})
    (φ : (Functor.sheafPullbackConstruction.sheafPullback h.totalFunctor RingCat.{u}
      C'.totalTopology C.totalTopology).obj O' ⟶ O) :
    h.totalRingImageAdjunction.homEquiv O' O φ =
      (SimplicialSiteMorphism.ofMorphismOfSites h).ringHomEquiv O O'
          (h.totalInverseImageRingIso.hom.app O' ≫ φ) ≫
        h.totalPushforwardRingIso.hom.app O :=
  ((Adjunction.homEquiv_ofNatIsoRight_apply _ _ _).symm.trans
    (Adjunction.homEquiv_leftAdjointUniq_hom_app_comp
      h.totalRestrictRingAdjunction h.totalRingImageAdjunction φ)).symm

end Morphism

/-- **Stacks 0DGZ**, case (A). A morphism between ringed simplicial sites: a morphism `h`
between the underlying simplicial sites, together with a homomorphism of sheaves of rings
`h♯ : h_total⁻¹ 𝒪' ⟶ 𝒪` on the total site. -/
@[stacks 0DGZ "ringed simplicial site morphism, case (A) of Situation 09WE"]
structure RingedMorphism (C C' : SimplicialSite.{u})
    (O : Sheaf C.totalTopology RingCat.{u})
    (O' : Sheaf C'.totalTopology RingCat.{u}) where
  /-- The underlying morphism between the simplicial sites. -/
  hom : SimplicialSite.Morphism C C'
  /-- The homomorphism of sheaves of rings `h_total⁻¹ 𝒪' ⟶ 𝒪`. -/
  ringHom : hom.totalInverseImageRing O' ⟶ O

namespace RingedMorphism

variable {C C' : SimplicialSite.{u}}
  {O : Sheaf C.totalTopology RingCat.{u}}
  {O' : Sheaf C'.totalTopology RingCat.{u}}

/-- The underlying morphism between the simplicial sites, read as a morphism between the
simplicial-site situations of case (A). -/
def toSimplicialSiteMorphism (h : RingedMorphism C C' O O') :
    SimplicialSiteMorphism (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u})
      (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) :=
  SimplicialSiteMorphism.ofMorphismOfSites h.hom

/-- **Stacks 0DGZ**, case (A). A homomorphism of sheaves of rings `h_total⁻¹ 𝒪' ⟶ 𝒪` is the
same thing as a homomorphism `𝒪' ⟶ h_{total, *} 𝒪`: the two are exchanged by the adjunction
between the inverse image and the direct image of sheaves of rings along the total functor. -/
@[stacks 0DGZ "the two equivalent forms of the ring map, case (A)",
  sga "4 XVII 0.2.1" "ringed simplicial sites"]
def ringHomEquiv (h : SimplicialSite.Morphism C C')
    (O : Sheaf C.totalTopology RingCat.{u})
    (O' : Sheaf C'.totalTopology RingCat.{u}) :
    (h.totalInverseImageRing O' ⟶ O) ≃ (O' ⟶ h.totalPushforwardRing O) :=
  h.totalRingImageAdjunction.homEquiv O' O

/-- The homomorphism of sheaves of rings of a morphism between ringed simplicial sites, in its
direct-image form `𝒪' ⟶ h_{total, *} 𝒪`. -/
def ringHomPushforward (h : RingedMorphism C C' O O') :
    O' ⟶ h.hom.totalPushforwardRing O :=
  ringHomEquiv h.hom O O' h.ringHom

/-- The bijection `ringHomEquiv` sends the inverse-image form of the homomorphism of sheaves of
rings to its direct-image form. -/
@[simp]
theorem ringHomEquiv_ringHom (h : RingedMorphism C C' O O') :
    ringHomEquiv h.hom O O' h.ringHom = h.ringHomPushforward :=
  rfl

/-- The inverse of `ringHomEquiv` sends the direct-image form of the homomorphism of sheaves of
rings back to its inverse-image form. -/
@[simp]
theorem ringHomEquiv_symm_ringHomPushforward (h : RingedMorphism C C' O O') :
    (ringHomEquiv h.hom O O').symm h.ringHomPushforward = h.ringHom :=
  (ringHomEquiv h.hom O O').symm_apply_apply h.ringHom

/-- The direct-image form of the homomorphism of sheaves of rings is the unit of the ring-level
adjunction followed by the direct image of the inverse-image form. -/
theorem ringHomPushforward_eq (h : RingedMorphism C C' O O') :
    h.ringHomPushforward = h.hom.totalRingImageAdjunction.unit.app O' ≫
      (h.hom.totalFunctor.sheafPushforwardContinuous RingCat.{u}
        C'.totalTopology C.totalTopology).map h.ringHom :=
  h.hom.totalRingImageAdjunction.homEquiv_unit O' O h.ringHom

/-- A morphism between ringed simplicial sites given by the direct-image form
`𝒪' ⟶ h_{total, *} 𝒪` of its homomorphism of sheaves of rings. -/
def ofPushforward (h : SimplicialSite.Morphism C C')
    (φ : O' ⟶ h.totalPushforwardRing O) : RingedMorphism C C' O O' where
  hom := h
  ringHom := (ringHomEquiv h O O').symm φ

/-- The underlying morphism of simplicial sites of `ofPushforward h φ` is `h`. -/
@[simp]
theorem ofPushforward_hom (h : SimplicialSite.Morphism C C')
    (φ : O' ⟶ h.totalPushforwardRing O) :
    (ofPushforward h φ).hom = h :=
  rfl

/-- The inverse-image form of the homomorphism of sheaves of rings of `ofPushforward h φ` is the
image of `φ` under the inverse of `ringHomEquiv`. -/
@[simp]
theorem ofPushforward_ringHom (h : SimplicialSite.Morphism C C')
    (φ : O' ⟶ h.totalPushforwardRing O) :
    (ofPushforward h φ).ringHom = (ringHomEquiv h O O').symm φ :=
  rfl

/-- The direct-image form of the homomorphism of sheaves of rings of `ofPushforward h φ` is
`φ`. -/
@[simp]
theorem ringHomPushforward_ofPushforward (h : SimplicialSite.Morphism C C')
    (φ : O' ⟶ h.totalPushforwardRing O) :
    (ofPushforward h φ).ringHomPushforward = φ :=
  (ringHomEquiv h O O').apply_symm_apply φ

end RingedMorphism

end SimplicialSite

end CategoryTheory

end
