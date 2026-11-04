module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageAdjunction
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalMorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms between ringed simplicial sites

A ringed simplicial site is a simplicial site together with a sheaf of rings on its total site.
A morphism between two of them is a morphism `h` of the underlying simplicial sites together
with a homomorphism of sheaves of rings from the inverse image of the target ring sheaf to the
source ring sheaf, taken along the induced morphism of total topoi. Equivalently, it is a
homomorphism from the target ring sheaf to the direct image of the source ring sheaf.

## Main definitions

* `CategoryTheory.CocontinuousSimplicialSite.Morphism.totalInverseImageRing` and
  `.totalPushforwardRing`: the inverse image and the direct image of a sheaf of rings along the
  morphism of total topoi.
* `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism`: a morphism between ringed
  simplicial sites, with the homomorphism of sheaves of rings in inverse-image form.
* `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism.toSimplicialSiteMorphism`: its
  underlying morphism between the simplicial-site situations.
* `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism.ringHomEquiv`: the bijection
  between the inverse-image and the direct-image form of that homomorphism.
* `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism.ringHomPushforward`: the
  homomorphism of sheaves of rings in direct-image form.
* `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism.ofPushforward`: the morphism
  between ringed simplicial sites determined by a homomorphism in direct-image form.

## Main results

* `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism.ringHomPushforward_eq`: the
  direct-image form is the unit of the ring-level adjunction followed by the direct image of the
  inverse-image form.

## Implementation notes

The homomorphism of sheaves of rings is stored in the inverse-image form in which the source
states it first, and its direct-image form is the value of an adjunction bijection, namely
`Stacks.Sheaves.ToposPushforward.ringImageAdjunction` for the morphism of total topoi. So no
new comparison of the two forms is needed, and either form determines a morphism.

This file treats case (B) of the simplicial-site situation; case (A) is
`StacksFrontier/CategoryTheory/Sites/Simplicial/RingedMorphismContinuous.lean`.

The universe is a single `u`: the morphism of total topoi is a morphism of topoi of sheaves of
sets valued in `Type u`, and this pins the universe of the sheaves of rings on both total sites.
The inverse and direct images of a sheaf of rings are given their own names above because their
universe parameters are not determined by their arguments alone.

## References

* [Stacks Project, Tag 0DGZ](https://stacks.math.columbia.edu/tag/0DGZ)
* [Stacks Project, Tag 0D95](https://stacks.math.columbia.edu/tag/0D95)
* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Sheaves.ToposPushforward

universe u

namespace CategoryTheory

namespace CocontinuousSimplicialSite

namespace Morphism

variable {C C' : CocontinuousSimplicialSite.{u}}

/-- The inverse image, along the morphism of total topoi of a morphism between simplicial
sites, of a sheaf of rings on the total site of the target. -/
abbrev totalInverseImageRing (h : CocontinuousSimplicialSite.Morphism C C')
    (O' : Sheaf (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}).totalTopology RingCat.{u}) :
    Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology RingCat.{u} :=
  (inverseImageRingFunctor h.totalMorphism).obj O'

/-- The direct image, along the morphism of total topoi of a morphism between simplicial sites,
of a sheaf of rings on the total site of the source. -/
abbrev totalPushforwardRing (h : CocontinuousSimplicialSite.Morphism C C')
    (O : Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology RingCat.{u}) :
    Sheaf (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}).totalTopology RingCat.{u} :=
  (pushforwardRingFunctor h.totalMorphism).obj O

end Morphism

/-- **Stacks 0DGZ**, case (B). A morphism between ringed simplicial sites: a morphism `h`
between the underlying simplicial sites, together with a homomorphism of sheaves of rings
`h♯ : h_total⁻¹ 𝒪' ⟶ 𝒪` on the total site. -/
@[stacks 0DGZ "ringed simplicial site morphism, case (B) of Situation 09WE"]
structure RingedMorphism (C C' : CocontinuousSimplicialSite.{u})
    (O : Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology RingCat.{u})
    (O' : Sheaf (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}).totalTopology RingCat.{u}) where
  /-- The underlying morphism between the simplicial sites. -/
  hom : CocontinuousSimplicialSite.Morphism C C'
  /-- The homomorphism of sheaves of rings `h_total⁻¹ 𝒪' ⟶ 𝒪`. -/
  ringHom : hom.totalInverseImageRing O' ⟶ O

namespace RingedMorphism

variable {C C' : CocontinuousSimplicialSite.{u}}
  {O : Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology RingCat.{u}}
  {O' : Sheaf (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}).totalTopology RingCat.{u}}

/-- The underlying morphism between the simplicial sites, read as a morphism between the
simplicial-site situations of case (B). -/
def toSimplicialSiteMorphism (h : RingedMorphism C C' O O') :
    SimplicialSiteMorphism (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u})
      (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) :=
  SimplicialSiteMorphism.ofCocontinuous h.hom

/-- **Stacks 0DGZ**, case (B). A homomorphism of sheaves of rings `h_total⁻¹ 𝒪' ⟶ 𝒪` is the
same thing as a homomorphism `𝒪' ⟶ h_{total, *} 𝒪`: the two are exchanged by the adjunction
between the inverse image and the direct image of sheaves of rings along the morphism of total
topoi. -/
@[stacks 0DGZ "the two equivalent forms of the ring map, case (B)",
  sga "4 XVII 0.2.1" "ringed simplicial sites"]
def ringHomEquiv (h : CocontinuousSimplicialSite.Morphism C C')
    (O : Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology RingCat.{u})
    (O' : Sheaf (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}).totalTopology RingCat.{u}) :
    (h.totalInverseImageRing O' ⟶ O) ≃ (O' ⟶ h.totalPushforwardRing O) :=
  (ringImageAdjunction h.totalMorphism).homEquiv O' O

/-- The homomorphism of sheaves of rings of a morphism between ringed simplicial sites, in its
direct-image form `𝒪' ⟶ h_{total, *} 𝒪`. -/
def ringHomPushforward (h : RingedMorphism C C' O O') :
    O' ⟶ h.hom.totalPushforwardRing O :=
  ringHomEquiv h.hom O O' h.ringHom

/-- The bijection `ringHomEquiv` carries the homomorphism of sheaves of rings of a morphism to its
direct-image form. -/
@[simp]
theorem ringHomEquiv_ringHom (h : RingedMorphism C C' O O') :
    ringHomEquiv h.hom O O' h.ringHom = h.ringHomPushforward :=
  rfl

/-- The inverse of `ringHomEquiv` carries the direct-image form of the homomorphism of sheaves of
rings back to the homomorphism itself. -/
@[simp]
theorem ringHomEquiv_symm_ringHomPushforward (h : RingedMorphism C C' O O') :
    (ringHomEquiv h.hom O O').symm h.ringHomPushforward = h.ringHom :=
  (ringHomEquiv h.hom O O').symm_apply_apply h.ringHom

/-- The direct-image form of the homomorphism of sheaves of rings is the unit of the ring-level
adjunction followed by the direct image of the inverse-image form. -/
theorem ringHomPushforward_eq (h : RingedMorphism C C' O O') :
    h.ringHomPushforward = ringUnit h.hom.totalMorphism O' ≫
      (pushforwardRingFunctor h.hom.totalMorphism).map h.ringHom :=
  (ringImageAdjunction h.hom.totalMorphism).homEquiv_unit O' O h.ringHom

/-- A morphism between ringed simplicial sites given by the direct-image form
`𝒪' ⟶ h_{total, *} 𝒪` of its homomorphism of sheaves of rings. -/
def ofPushforward (h : CocontinuousSimplicialSite.Morphism C C')
    (φ : O' ⟶ h.totalPushforwardRing O) : RingedMorphism C C' O O' where
  hom := h
  ringHom := (ringHomEquiv h O O').symm φ

/-- The underlying morphism of `ofPushforward h φ` is `h`. -/
@[simp]
theorem ofPushforward_hom (h : CocontinuousSimplicialSite.Morphism C C')
    (φ : O' ⟶ h.totalPushforwardRing O) :
    (ofPushforward h φ).hom = h :=
  rfl

/-- The homomorphism of sheaves of rings of `ofPushforward h φ` is the inverse-image form of
`φ`. -/
@[simp]
theorem ofPushforward_ringHom (h : CocontinuousSimplicialSite.Morphism C C')
    (φ : O' ⟶ h.totalPushforwardRing O) :
    (ofPushforward h φ).ringHom = (ringHomEquiv h O O').symm φ :=
  rfl

/-- The direct-image form of the homomorphism of sheaves of rings of `ofPushforward h φ` is `φ`. -/
@[simp]
theorem ringHomPushforward_ofPushforward (h : CocontinuousSimplicialSite.Morphism C C')
    (φ : O' ⟶ h.totalPushforwardRing O) :
    (ofPushforward h φ).ringHomPushforward = φ :=
  (ringHomEquiv h O O').apply_symm_apply φ

end RingedMorphism

end CocontinuousSimplicialSite

end CategoryTheory

end
