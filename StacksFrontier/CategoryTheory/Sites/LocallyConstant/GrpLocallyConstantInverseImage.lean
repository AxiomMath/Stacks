module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.GrpInternalization
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.SectionRelocalizationFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Locally constant sheaves of groups and the inverse image of a morphism of topoi

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi between the topoi of sheaves of sets on two small
sites — an adjoint pair with left exact inverse image, and no functor between the sites. Tag 093R
asserts that `f⁻¹` carries a locally constant sheaf of sets, groups, abelian groups, rings or
modules over a fixed ring to a locally constant sheaf of the same kind. This file proves the
assertion for sheaves of **groups**, with no commutativity and no finiteness assumption on the
local values, and no final object in either site.

The route is the one the sets case takes, read on internal group objects. Local constancy of `G`
is a property of a family of objects of `D`, namely those over which `G` becomes constant, and
that family is the same whatever the coefficients are: so the covering of an object `U` of `C` is
again the one `Stacks.Topos.exists_cover_inverseImage_sections` produces for the sheaves
represented by those objects, and on a member `V` of it one has a section
`σ : h_V^# ⟶ f⁻¹h_Y^#` of one of them. What has to be upgraded is the transport of a
trivialization along `σ`. For sheaves of sets that is
`MorphismOfTopoi.constantIsoOverPullbackInverseImageOfSection`, an isomorphism of sheaves of
sets, and it does not by itself carry the group operations: a bijection between the trivializing
values is not a homomorphism, and indeed the underlying sheaf of sets of a locally constant sheaf
of groups being locally constant does not make the sheaf of groups locally constant.

The upgrade is `MorphismOfTopoi.grpSectionRelocalization`: the relocalization along `σ` is a
functor between sheaves of sets which *preserves finite products*
(`MorphismOfTopoi.preservesFiniteProducts_sectionRelocalization`), so it acts on internal group
objects, and the two compatibilities it satisfies —
`MorphismOfTopoi.sectionRelocalizationOverPullbackIso` and
`MorphismOfTopoi.sectionRelocalizationConstantSheafIso` — are natural isomorphisms of
finite-product-preserving functors, hence lift to group objects by
`CategoryTheory.Functor.mapGrpNatIso`. No multiplicativity is ever checked by hand. The two
comparisons which make the lifted statements say something about *sheaves of groups* rather than
about internal group objects are `Stacks.Sites.GrpPullback.overPullbackInternalIso` and
`Stacks.Sites.GrpPullback.constantSheafInternalIso`.

## Main definitions

* `MorphismOfTopoi.grpSectionRelocalization` — the relocalization along a section, acting on
  sheaves of groups.
* `MorphismOfTopoi.grpSectionRelocalizationOverPullbackIso` — it carries the restriction of a
  sheaf of groups to `Y` to the restriction of its inverse image to `V`.
* `MorphismOfTopoi.grpSectionRelocalizationConstantSheafIso` — it carries the constant sheaf of
  groups on a group to the constant sheaf of groups on the same group.
* `MorphismOfTopoi.grpConstantIsoOverPullbackInverseImageOfSection` — a trivialization of `G`
  over `Y` plus a section `h_V^# ⟶ f⁻¹h_Y^#` give a trivialization of the inverse image of `G`
  over `V`, with the same value.

## Main results

* `MorphismOfTopoi.isLocallyConstant_grpInverseImage_of_smallSites` — **Tag 093R** for locally
  constant sheaves of groups: the inverse image of a locally constant sheaf of groups along an
  arbitrary morphism of topoi between the topoi of sheaves of sets on two small sites is locally
  constant.

## The other coefficients of Tag 093R

The source's list is "sets, groups, abelian groups, rings, modules over a fixed ring `Λ`, etc".
The sets case is `MorphismOfTopoi.isLocallyConstant_inverseImage_of_smallSites`, the abelian case
is `MorphismOfTopoi.isLocallyConstant_abelianInverseImage_of_smallSites`, the case of modules
over a fixed ring is `MorphismOfTopoi.isLocallyConstant_moduleInverseImage_of_smallSites`, the
case of rings is `MorphismOfTopoi.isLocallyConstant_ringInverseImage_of_smallSites`, and the case
of sheaves of groups is below. What the argument below consumes is the identification of sheaves
of groups with group objects in sheaves of sets
(`CategoryTheory.Sites.GrpSheaf.equivalence`) together with the two internalization comparisons
of `StacksFrontier/CategoryTheory/Sites/LocallyConstant/GrpInternalization.lean`; the ring case runs
on the same pattern with `CategoryTheory.Sites.RingSheaf.equivalence` and
`CategoryTheory.Functor.mapRing` in place of them.

For an arbitrary coefficient category the library also has the weaker
`Stacks.ConstantSheaf.isLocallyConstant_sheafPullback`, which holds for an arbitrary coefficient
category but only for the inverse image along a *morphism of sites*, i.e. along a continuous left
exact cover-preserving functor between the two sites; a morphism of topoi need not be induced by
one.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public noncomputable section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Sites CategoryTheory.Sites.GrpSheaf Opposite
open Stacks.ConstantSheaf Stacks.Sites.GrpPullback

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

/-- **The relocalization along a section, acting on sheaves of groups.** The group operations of
a sheaf of groups on `D/Y` are read as the operations of an internal group object in sheaves of
sets, the finite-product-preserving `MorphismOfTopoi.sectionRelocalization` carries those to
operations again, and the result is read back sectionwise. -/
public def grpSectionRelocalization :
    Sheaf (K.over Y) GrpCat.{w} ⥤ Sheaf (J.over V) GrpCat.{w} :=
  letI : (sectionRelocalization J K f σ).Monoidal := .ofChosenFiniteProducts _
  internalSheaf (K.over Y) ⋙ (sectionRelocalization J K f σ).mapGrp ⋙
    externalSheaf (J.over V)

/-- **The relocalization carries the restriction of a sheaf of groups to `Y` to the restriction
of its inverse image to `V`**, naturally in the sheaf.

This is `MorphismOfTopoi.sectionRelocalizationOverPullbackIso` lifted to internal group objects
by `CategoryTheory.Functor.mapGrpNatIso`, with the two restrictions read on internal groups by
`Stacks.Sites.GrpPullback.overPullbackInternalIso` and `.overPullbackExternalIso`. -/
public def grpSectionRelocalizationOverPullbackIso :
    K.overPullback GrpCat.{w} Y ⋙ grpSectionRelocalization J K f σ ≅
      CategoryTheory.Sites.grpInverseImage f ⋙ J.overPullback GrpCat.{w} V := by
  haveI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  letI : f.inverseImage.Monoidal := .ofChosenFiniteProducts _
  letI : (sectionRelocalization J K f σ).Monoidal := .ofChosenFiniteProducts _
  letI : (K.overPullback (Type w) Y).Monoidal := .ofChosenFiniteProducts _
  letI : (J.overPullback (Type w) V).Monoidal := .ofChosenFiniteProducts _
  exact Functor.isoWhiskerRight (overPullbackInternalIso K Y)
      ((sectionRelocalization J K f σ).mapGrp ⋙ externalSheaf (J.over V)) ≪≫
    Functor.isoWhiskerLeft (internalSheaf K)
      (Functor.isoWhiskerRight (Functor.mapGrpCompIso
        (F := K.overPullback (Type w) Y) (G := sectionRelocalization J K f σ)).symm
          (externalSheaf (J.over V))) ≪≫
    Functor.isoWhiskerLeft (internalSheaf K)
      (Functor.isoWhiskerRight (Functor.mapGrpNatIso
        (sectionRelocalizationOverPullbackIso J K f σ)) (externalSheaf (J.over V))) ≪≫
    Functor.isoWhiskerLeft (internalSheaf K)
      (Functor.isoWhiskerRight (Functor.mapGrpCompIso
        (F := f.inverseImage) (G := J.overPullback (Type w) V)) (externalSheaf (J.over V))) ≪≫
    Functor.isoWhiskerLeft (internalSheaf K ⋙ f.inverseImage.mapGrp)
      (overPullbackExternalIso J V).symm

/-- **The relocalization carries the constant sheaf of groups on a group to the constant sheaf of
groups on the same group**, naturally in the group.

This is `MorphismOfTopoi.sectionRelocalizationConstantSheafIso` lifted to internal group objects
by `CategoryTheory.Functor.mapGrpNatIso`, with the two constant sheaves read on internal groups
by `Stacks.Sites.GrpPullback.constantSheafInternalIso` and `.constantSheafExternalIso`. The
trivializing group is unchanged. -/
public def grpSectionRelocalizationConstantSheafIso :
    constantSheaf (K.over Y) GrpCat.{w} ⋙ grpSectionRelocalization J K f σ ≅
      constantSheaf (J.over V) GrpCat.{w} := by
  letI : (sectionRelocalization J K f σ).Monoidal := .ofChosenFiniteProducts _
  letI : (constantSheaf (K.over Y) (Type w)).Monoidal := .ofChosenFiniteProducts _
  letI : (constantSheaf (J.over V) (Type w)).Monoidal := .ofChosenFiniteProducts _
  exact Functor.isoWhiskerRight (constantSheafInternalIso (K.over Y))
      ((sectionRelocalization J K f σ).mapGrp ⋙ externalSheaf (J.over V)) ≪≫
    Functor.isoWhiskerLeft grpTypeEquivalenceGrp.inverse
      (Functor.isoWhiskerRight (Functor.mapGrpCompIso
        (F := constantSheaf (K.over Y) (Type w)) (G := sectionRelocalization J K f σ)).symm
          (externalSheaf (J.over V))) ≪≫
    Functor.isoWhiskerLeft grpTypeEquivalenceGrp.inverse
      (Functor.isoWhiskerRight (Functor.mapGrpNatIso
        (sectionRelocalizationConstantSheafIso J K f σ)) (externalSheaf (J.over V))) ≪≫
    constantSheafExternalIso (J.over V)

/-- **A trivialization of a sheaf of groups survives the inverse image along a section, with the
same value.** If `G` restricted to `Y` is the constant sheaf of groups on a group `E`, and `V`
carries a section of `f⁻¹h_Y^#`, then the inverse image of `G` restricted to `V` is the constant
sheaf of groups on the same `E`.

Apply `MorphismOfTopoi.grpSectionRelocalization` to the trivialization and read the two sides
with `MorphismOfTopoi.grpSectionRelocalizationConstantSheafIso` and
`MorphismOfTopoi.grpSectionRelocalizationOverPullbackIso`. -/
public def grpConstantIsoOverPullbackInverseImageOfSection
    (G : Sheaf K GrpCat.{w}) (E : GrpCat.{w})
    (c : (constantSheaf (K.over Y) GrpCat.{w}).obj E ≅
      (K.overPullback GrpCat.{w} Y).obj G) :
    (constantSheaf (J.over V) GrpCat.{w}).obj E ≅
      (J.overPullback GrpCat.{w} V).obj
        ((CategoryTheory.Sites.grpInverseImage f).obj G) :=
  ((grpSectionRelocalizationConstantSheafIso J K f σ).app E).symm ≪≫
    (grpSectionRelocalization J K f σ).mapIso c ≪≫
    (grpSectionRelocalizationOverPullbackIso J K f σ).app G

end Relocalization

/-- **Tag 093R for locally constant sheaves of groups.** The inverse image of a locally constant
sheaf of groups along an arbitrary morphism of topoi between the topoi of sheaves of sets on two
small sites is locally constant.

No functor between the two sites, no final object in either, no commutativity of the local
values and no finiteness of them is assumed. The covering of an object `U` of `C` is the one
`Stacks.Topos.exists_cover_inverseImage_sections` produces for the family of sheaves represented
by the objects of `D` over which `G` is trivialized as a sheaf of groups, and on a member `V` of
it the section it carries trivializes the inverse image over `V`, with the same trivializing
group, by `MorphismOfTopoi.grpConstantIsoOverPullbackInverseImageOfSection`. -/
@[stacks 093R "locally constant sheaves of groups, for an arbitrary morphism of topoi between \
  the topoi of sheaves of sets on two small sites"]
public lemma isLocallyConstant_grpInverseImage_of_smallSites
    (G : Sheaf K GrpCat.{w}) [hG : IsLocallyConstant K G] :
    IsLocallyConstant J ((CategoryTheory.Sites.grpInverseImage f).obj G) where
  exists_cover U := by
    obtain ⟨T, hT⟩ := Stacks.Topos.exists_cover_inverseImage_sections f
      (Stacks.Topos.representedFamily K
        fun Y => Sheaf.IsConstant (K.over Y)
          ((K.overPullback GrpCat.{w} Y).obj G))
      (Stacks.Topos.jointlyLocallyInhabited_representedFamily K _
        fun W => by
          obtain ⟨I, Z, g, hg, hc⟩ := hG.exists_cover W
          exact ⟨I, Z, g, hg, hc⟩) U
    refine ⟨Σ V : C, {g : V ⟶ U // T.1.arrows g}, fun p => p.1, fun p => p.2.1,
      sieve_ofArrows_arrows_mem J _ T.2, fun p => ?_⟩
    obtain ⟨i, ⟨x⟩⟩ := hT p.1 p.2.1 p.2.2
    have := i.2
    obtain ⟨E, ⟨c⟩⟩ := Sheaf.mem_essImage_of_isConstant (K.over i.1)
      ((K.overPullback GrpCat.{w} i.1).obj G)
    exact ⟨E, ⟨grpConstantIsoOverPullbackInverseImageOfSection J K f
      (Stacks.Topos.sectionHom J _ x) G E c⟩⟩

end MorphismOfTopoi

end
