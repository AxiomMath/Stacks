module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.RingInternalization
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.SectionRelocalizationFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Locally constant sheaves of rings and the inverse image of a morphism of topoi

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi between the topoi of sheaves of sets on two small
sites — an adjoint pair with left exact inverse image, and no functor between the sites. Tag 093R
asserts that `f⁻¹` carries a locally constant sheaf of sets, groups, abelian groups, rings or
modules over a fixed ring to a locally constant sheaf of the same kind. This file proves the
assertion for sheaves of **rings**, with no commutativity and no finiteness assumption on the
local values, and no final object in either site.

The route is the one the sets case takes, read on internal ring objects. Local constancy of `G`
is a property of a family of objects of `D`, namely those over which `G` becomes constant, and
that family is the same whatever the coefficients are: so the covering of an object `U` of `C` is
again the one `Stacks.Topos.exists_cover_inverseImage_sections` produces for the sheaves
represented by those objects, and on a member `V` of it one has a section
`σ : h_V^# ⟶ f⁻¹h_Y^#` of one of them. What has to be upgraded is the transport of a
trivialization along `σ`. For sheaves of sets that is
`MorphismOfTopoi.constantIsoOverPullbackInverseImageOfSection`, an isomorphism of sheaves of
sets, and it does not by itself carry the ring operations: a bijection between the trivializing
values is not a ring homomorphism, and indeed the underlying sheaf of sets of a locally constant
sheaf of rings being locally constant does not make the sheaf of rings locally constant.

The upgrade is `MorphismOfTopoi.ringSectionRelocalization`: the relocalization along `σ` is a
functor between sheaves of sets which *preserves finite products*
(`MorphismOfTopoi.preservesFiniteProducts_sectionRelocalization`), so it acts on internal ring
objects, and the two compatibilities it satisfies —
`MorphismOfTopoi.sectionRelocalizationOverPullbackIso` and
`MorphismOfTopoi.sectionRelocalizationConstantSheafIso` — are natural isomorphisms of
finite-product-preserving functors, hence lift to ring objects by
`CategoryTheory.Functor.mapRingNatIso`. Neither additivity nor multiplicativity is ever checked
by hand. The two comparisons which make the lifted statements say something about *sheaves of
rings* rather than about internal ring objects are
`Stacks.Sites.RingPullback.overPullbackInternalIso` and
`Stacks.Sites.RingPullback.constantSheafInternalIso`.

## Main definitions

* `MorphismOfTopoi.ringSectionRelocalization` — the relocalization along a section, acting on
  sheaves of rings.
* `MorphismOfTopoi.ringSectionRelocalizationOverPullbackIso` — it carries the restriction of a
  sheaf of rings to `Y` to the restriction of its inverse image to `V`.
* `MorphismOfTopoi.ringSectionRelocalizationConstantSheafIso` — it carries the constant sheaf of
  rings on a ring to the constant sheaf of rings on the same ring.
* `MorphismOfTopoi.ringConstantIsoOverPullbackInverseImageOfSection` — a trivialization of `G`
  over `Y` plus a section `h_V^# ⟶ f⁻¹h_Y^#` give a trivialization of the inverse image of `G`
  over `V`, with the same value.

## Main results

* `MorphismOfTopoi.isLocallyConstant_ringInverseImage_of_smallSites` — **Tag 093R** for locally
  constant sheaves of rings: the inverse image of a locally constant sheaf of rings along an
  arbitrary morphism of topoi between the topoi of sheaves of sets on two small sites is locally
  constant.

With this the whole of the source's list is carried: sheaves of sets by
`MorphismOfTopoi.isLocallyConstant_inverseImage_of_smallSites`, of groups by
`MorphismOfTopoi.isLocallyConstant_grpInverseImage_of_smallSites`, of abelian groups by
`MorphismOfTopoi.isLocallyConstant_abelianInverseImage_of_smallSites`, of modules over a fixed
ring by `MorphismOfTopoi.isLocallyConstant_moduleInverseImage_of_smallSites`, and of rings below.

## Implementation notes

The sheaf of rings is a sheaf of *not necessarily commutative* rings, matching the rest of this
development's topos-level ring theory and the `GrpCat` rather than `AddCommGrpCat` reading of the
source's "groups".

The inverse image used is `CategoryTheory.Sites.ringInverseImage`, whose underlying sheaf of sets
is the geometric inverse image on the nose
(`CategoryTheory.Sites.ringInverseImage_forgetIso`, which is `Iso.refl`): the statement below is
therefore about the inverse image of `G` and not about a neighbouring functor.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public noncomputable section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Sites CategoryTheory.Sites.RingSheaf Opposite
open Stacks.ConstantSheaf Stacks.Sites.RingPullback

universe w

namespace MorphismOfTopoi

attribute [local instance] Stacks.Sites.AbelianPullback.cartesianPresheafTypes
  Stacks.Sites.AbelianPullback.braidedPresheafTypes Stacks.Sites.AbelianPullback.cartesianSheafTypes
  Stacks.Sites.AbelianPullback.braidedSheafTypes
  Stacks.Sites.AbelianPullback.braidedSheafToPresheafTypes

variable {C : Type w} [SmallCategory C] {D : Type w} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))

section Relocalization

variable {V : C} {Y : D}
  (σ : (presheafToSheaf J (Type w)).obj (yoneda.obj V) ⟶
    f.inverseImage.obj ((presheafToSheaf K (Type w)).obj (yoneda.obj Y)))

/-- **The relocalization along a section, acting on sheaves of rings.** The ring operations of a
sheaf of rings on `D/Y` are read as the operations of an internal ring object in sheaves of sets,
the finite-product-preserving `MorphismOfTopoi.sectionRelocalization` carries those to operations
again, and the result is read back sectionwise. -/
public def ringSectionRelocalization :
    Sheaf (K.over Y) RingCat.{w} ⥤ Sheaf (J.over V) RingCat.{w} :=
  letI : (sectionRelocalization J K f σ).Braided := .ofChosenFiniteProducts _
  internalSheaf (K.over Y) ⋙ (sectionRelocalization J K f σ).mapRing ⋙
    externalSheaf (J.over V)

/-- **The relocalization carries the restriction of a sheaf of rings to `Y` to the restriction of
its inverse image to `V`**, naturally in the sheaf.

This is `MorphismOfTopoi.sectionRelocalizationOverPullbackIso` lifted to internal ring objects by
`CategoryTheory.Functor.mapRingNatIso`, with the two restrictions read on internal rings by
`Stacks.Sites.RingPullback.overPullbackInternalIso` and `.overPullbackExternalIso`. -/
public def ringSectionRelocalizationOverPullbackIso :
    K.overPullback RingCat.{w} Y ⋙ ringSectionRelocalization J K f σ ≅
      CategoryTheory.Sites.ringInverseImage f ⋙ J.overPullback RingCat.{w} V := by
  haveI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  letI : f.inverseImage.Braided := .ofChosenFiniteProducts _
  letI : (sectionRelocalization J K f σ).Braided := .ofChosenFiniteProducts _
  letI : (K.overPullback (Type w) Y).Braided := .ofChosenFiniteProducts _
  letI : (J.overPullback (Type w) V).Braided := .ofChosenFiniteProducts _
  exact Functor.isoWhiskerRight (overPullbackInternalIso K Y)
      ((sectionRelocalization J K f σ).mapRing ⋙ externalSheaf (J.over V)) ≪≫
    Functor.isoWhiskerLeft (internalSheaf K)
      (Functor.isoWhiskerRight (Functor.mapRingCompIso
        (F := K.overPullback (Type w) Y) (G := sectionRelocalization J K f σ)).symm
          (externalSheaf (J.over V))) ≪≫
    Functor.isoWhiskerLeft (internalSheaf K)
      (Functor.isoWhiskerRight (Functor.mapRingNatIso
        (sectionRelocalizationOverPullbackIso J K f σ)) (externalSheaf (J.over V))) ≪≫
    Functor.isoWhiskerLeft (internalSheaf K)
      (Functor.isoWhiskerRight (Functor.mapRingCompIso
        (F := f.inverseImage) (G := J.overPullback (Type w) V)) (externalSheaf (J.over V))) ≪≫
    Functor.isoWhiskerLeft (internalSheaf K ⋙ f.inverseImage.mapRing)
      (overPullbackExternalIso J V).symm

/-- **The relocalization carries the constant sheaf of rings on a ring to the constant sheaf of
rings on the same ring**, naturally in the ring.

This is `MorphismOfTopoi.sectionRelocalizationConstantSheafIso` lifted to internal ring objects
by `CategoryTheory.Functor.mapRingNatIso`, with the two constant sheaves read on internal rings
by `Stacks.Sites.RingPullback.constantSheafInternalIso` and `.constantSheafExternalIso`. The
trivializing ring is unchanged. -/
public def ringSectionRelocalizationConstantSheafIso :
    constantSheaf (K.over Y) RingCat.{w} ⋙ ringSectionRelocalization J K f σ ≅
      constantSheaf (J.over V) RingCat.{w} := by
  letI : (sectionRelocalization J K f σ).Braided := .ofChosenFiniteProducts _
  letI : (constantSheaf (K.over Y) (Type w)).Braided := .ofChosenFiniteProducts _
  letI : (constantSheaf (J.over V) (Type w)).Braided := .ofChosenFiniteProducts _
  exact Functor.isoWhiskerRight (constantSheafInternalIso (K.over Y))
      ((sectionRelocalization J K f σ).mapRing ⋙ externalSheaf (J.over V)) ≪≫
    Functor.isoWhiskerLeft ringTypeEquivalenceRing.inverse
      (Functor.isoWhiskerRight (Functor.mapRingCompIso
        (F := constantSheaf (K.over Y) (Type w)) (G := sectionRelocalization J K f σ)).symm
          (externalSheaf (J.over V))) ≪≫
    Functor.isoWhiskerLeft ringTypeEquivalenceRing.inverse
      (Functor.isoWhiskerRight (Functor.mapRingNatIso
        (sectionRelocalizationConstantSheafIso J K f σ)) (externalSheaf (J.over V))) ≪≫
    constantSheafExternalIso (J.over V)

/-- **A trivialization of a sheaf of rings survives the inverse image along a section, with the
same value.** If `G` restricted to `Y` is the constant sheaf of rings on a ring `E`, and `V`
carries a section of `f⁻¹h_Y^#`, then the inverse image of `G` restricted to `V` is the constant
sheaf of rings on the same `E`.

Apply `MorphismOfTopoi.ringSectionRelocalization` to the trivialization and read the two sides
with `MorphismOfTopoi.ringSectionRelocalizationConstantSheafIso` and
`MorphismOfTopoi.ringSectionRelocalizationOverPullbackIso`. -/
public def ringConstantIsoOverPullbackInverseImageOfSection
    (G : Sheaf K RingCat.{w}) (E : RingCat.{w})
    (c : (constantSheaf (K.over Y) RingCat.{w}).obj E ≅
      (K.overPullback RingCat.{w} Y).obj G) :
    (constantSheaf (J.over V) RingCat.{w}).obj E ≅
      (J.overPullback RingCat.{w} V).obj
        ((CategoryTheory.Sites.ringInverseImage f).obj G) :=
  ((ringSectionRelocalizationConstantSheafIso J K f σ).app E).symm ≪≫
    (ringSectionRelocalization J K f σ).mapIso c ≪≫
    (ringSectionRelocalizationOverPullbackIso J K f σ).app G

end Relocalization

/-- **Tag 093R for locally constant sheaves of rings.** The inverse image of a locally constant
sheaf of rings along an arbitrary morphism of topoi between the topoi of sheaves of sets on two
small sites is locally constant.

No functor between the two sites, no final object in either, no commutativity of the local
values and no finiteness of them is assumed. The covering of an object `U` of `C` is the one
`Stacks.Topos.exists_cover_inverseImage_sections` produces for the family of sheaves represented
by the objects of `D` over which `G` is trivialized as a sheaf of rings, and on a member `V` of
it the section it carries trivializes the inverse image over `V`, with the same trivializing
ring, by `MorphismOfTopoi.ringConstantIsoOverPullbackInverseImageOfSection`. -/
@[stacks 093R "locally constant sheaves of rings, for an arbitrary morphism of topoi between \
  the topoi of sheaves of sets on two small sites"]
public lemma isLocallyConstant_ringInverseImage_of_smallSites
    (G : Sheaf K RingCat.{w}) [hG : IsLocallyConstant K G] :
    IsLocallyConstant J ((CategoryTheory.Sites.ringInverseImage f).obj G) where
  exists_cover U := by
    obtain ⟨T, hT⟩ := Stacks.Topos.exists_cover_inverseImage_sections f
      (Stacks.Topos.representedFamily K
        fun Y => Sheaf.IsConstant (K.over Y)
          ((K.overPullback RingCat.{w} Y).obj G))
      (Stacks.Topos.jointlyLocallyInhabited_representedFamily K _
        fun W => by
          obtain ⟨I, Z, g, hg, hc⟩ := hG.exists_cover W
          exact ⟨I, Z, g, hg, hc⟩) U
    refine ⟨Σ V : C, {g : V ⟶ U // T.1.arrows g}, fun p => p.1, fun p => p.2.1,
      sieve_ofArrows_arrows_mem J _ T.2, fun p => ?_⟩
    obtain ⟨i, ⟨x⟩⟩ := hT p.1 p.2.1 p.2.2
    have := i.2
    obtain ⟨E, ⟨c⟩⟩ := Sheaf.mem_essImage_of_isConstant (K.over i.1)
      ((K.overPullback RingCat.{w} i.1).obj G)
    exact ⟨E, ⟨ringConstantIsoOverPullbackInverseImageOfSection J K f
      (Stacks.Topos.sectionHom J _ x) G E c⟩⟩

end MorphismOfTopoi

end
