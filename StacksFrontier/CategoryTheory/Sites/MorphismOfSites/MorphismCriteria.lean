module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs

/-!
# Ways of recognising a morphism of sites

`IsMorphismOfSites F J K` asks for a left exact left adjoint of the pushforward on sheaves. These
are the four situations in which such an adjoint is available for free: between small sites, where
the bundled `CategoryTheory.Functor.IsMorphismOfSites` of Tag 00X1 already carries one; for the two
functors of an equivalence of sites, where the sheaf categories are equivalent; and along an
isomorphism of the underlying functor, which transports an adjoint.

## Main results

* `rootMorphismOfSites_of_small`: between small sites, the bundled notion gives the
  universe-polymorphic one.
* `rootMorphismOfSites_of_equivalence` and `rootMorphismOfSites_of_equivalence_inverse`: both
  functors of an equivalence of sites are morphisms of sites.
* `rootMorphismOfSites_of_iso`: being a morphism of sites is invariant under isomorphism of the
  underlying functor.
-/

@[expose] public section

open CategoryTheory

universe w u₁ u₂ v₁ v₂

/-- A continuous functor whose sheaf pushforward has a left exact left adjoint is a morphism of
sites. -/
private lemma rootMorphismOfSites_of_adjunction
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K]
    {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
    (adj : L ⊣ F.sheafPushforwardContinuous (Type w) J K) [Limits.PreservesFiniteLimits L] :
    _root_.IsMorphismOfSites.{w} F J K :=
  { hasExactLeftAdjoint := ⟨L, ⟨adj⟩, inferInstance⟩ }

/-- Between small sites, the bundled notion of a morphism of sites gives the universe-polymorphic
one. -/
public lemma rootMorphismOfSites_of_small
    {C D : Type w} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (h : F.IsMorphismOfSites J K) : _root_.IsMorphismOfSites.{w} F J K := by
  have := h.isContinuous
  have := h.preservesFiniteLimits
  exact rootMorphismOfSites_of_adjunction F J K (F.sheafAdjunctionContinuous (Type w) J K)

/-- The functor of an equivalence of sites, for an induced topology, is a morphism of sites. -/
public lemma rootMorphismOfSites_of_equivalence
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (e : C ≌ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [e.inverse.IsDenseSubsite K J] : _root_.IsMorphismOfSites.{w} e.functor J K := by
  let E := e.sheafCongr J K (Type w)
  exact rootMorphismOfSites_of_adjunction e.functor J K (E.toAdjunction.ofNatIsoRight (Iso.refl _))

/-- The inverse of an equivalence of sites is a morphism of sites. -/
public lemma rootMorphismOfSites_of_equivalence_inverse
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (e : C ≌ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [e.inverse.IsDenseSubsite K J] [e.inverse.IsContinuous K J] :
    _root_.IsMorphismOfSites.{w} e.inverse K J := by
  let E := e.sheafCongr J K (Type w)
  exact rootMorphismOfSites_of_adjunction e.inverse K J
    (E.symm.toAdjunction.ofNatIsoRight (Iso.refl _))

/-- Being a morphism of sites is invariant under isomorphism of the underlying functor. -/
public lemma rootMorphismOfSites_of_iso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (e : F ≅ G) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [G.IsContinuous J K] (hG : _root_.IsMorphismOfSites.{w} G J K) :
    _root_.IsMorphismOfSites.{w} F J K := by
  have : F.IsContinuous J K := Functor.isContinuous_of_iso e.symm J K
  obtain ⟨L, ⟨adj⟩, hL⟩ := hG.hasExactLeftAdjoint
  let ePush := Functor.sheafPushforwardContinuousIso e (Type w) J K
  exact rootMorphismOfSites_of_adjunction F J K (adj.ofNatIsoRight ePush.symm)

end
