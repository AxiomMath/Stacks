module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianInternalization
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.SectionRelocalizationFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Locally constant sheaves of abelian groups and the inverse image of a morphism of topoi

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi between the topoi of sheaves of sets on two small
sites — an adjoint pair with left exact inverse image, and no functor between the sites. Tag 093R
asserts that `f⁻¹` carries a locally constant sheaf of sets, groups, abelian groups, rings or
modules over a fixed ring to a locally constant sheaf of the same kind. This file proves the
assertion for sheaves of **abelian groups**, with no finiteness assumption on the local values
and no final object in either site.

The route is the one the sets case takes, read on internal commutative group objects. Local
constancy of `G` is a property of a family of objects of `D`, namely those over which `G`
becomes constant, and that family is the same whatever the coefficients are: so the covering of
an object `U` of `C` is again the one
`Stacks.Topos.exists_cover_inverseImage_sections` produces for the sheaves represented by those
objects, and on a member `V` of it one has a section `σ : h_V^# ⟶ f⁻¹h_Y^#` of one of them. What
has to be upgraded is the transport of a trivialization along `σ`. For sheaves of sets that is
`MorphismOfTopoi.constantIsoOverPullbackInverseImageOfSection`, an isomorphism of sheaves of
sets, and it does not by itself carry the group operations: a bijection between the trivializing
values is not a homomorphism, and indeed the underlying sheaf of sets of a locally constant
abelian sheaf being locally constant does not make the abelian sheaf locally constant.

The upgrade is `MorphismOfTopoi.abelianSectionRelocalization`: the relocalization along `σ` is a
functor between sheaves of sets which *preserves finite products*
(`MorphismOfTopoi.preservesFiniteProducts_sectionRelocalization`), so it acts on internal
commutative group objects, and the two compatibilities it satisfies —
`MorphismOfTopoi.sectionRelocalizationOverPullbackIso` and
`MorphismOfTopoi.sectionRelocalizationConstantSheafIso` — are natural isomorphisms of
finite-product-preserving functors, hence lift to commutative group objects by
`CategoryTheory.Functor.mapCommGrpNatIso`. No additivity is ever checked by hand. The two
comparisons which make the lifted statements say something about abelian *sheaves* rather than
about internal commutative groups are
`Stacks.Sites.AbelianPullback.overPullbackInternalIso` and
`Stacks.Sites.AbelianPullback.constantSheafInternalIso`.

## Main definitions

* `MorphismOfTopoi.abelianSectionRelocalization` — the relocalization along a section, acting on
  sheaves of abelian groups.
* `MorphismOfTopoi.abelianSectionRelocalizationOverPullbackIso` — it carries the restriction of
  an abelian sheaf to `Y` to the restriction of its abelian inverse image to `V`.
* `MorphismOfTopoi.abelianSectionRelocalizationConstantSheafIso` — it carries the constant
  abelian sheaf on an abelian group to the constant abelian sheaf on the same group.
* `MorphismOfTopoi.abelianConstantIsoOverPullbackInverseImageOfSection` — a trivialization of `G`
  over `Y` plus a section `h_V^# ⟶ f⁻¹h_Y^#` give a trivialization of the abelian inverse image
  of `G` over `V`, with the same value.

## Main results

* `MorphismOfTopoi.isLocallyConstant_abelianInverseImage_of_smallSites` — **Tag 093R** for
  locally constant sheaves of abelian groups: the inverse image of a locally constant sheaf of
  abelian groups along an arbitrary morphism of topoi between the topoi of sheaves of sets on two
  small sites is locally constant.

The *constant* case of the same assertion is already carried, for an arbitrary morphism of topoi
between sites with final objects, by `MorphismOfTopoi.isConstant_abelianInverseImage`; it is not
restated here.

## The other coefficients of Tag 093R

The source's list is "sets, groups, abelian groups, rings, modules over a fixed ring `Λ`, etc".
The sets case is
`MorphismOfTopoi.isLocallyConstant_inverseImage_of_smallSites`, and the abelian case is below.
The case of sheaves of **groups** is
`MorphismOfTopoi.isLocallyConstant_grpInverseImage_of_smallSites`, which transcribes the argument
below at `GrpCat`; the case of **modules over a fixed ring** is
`MorphismOfTopoi.isLocallyConstant_moduleInverseImage_of_smallSites`; and the case of **rings**
is `MorphismOfTopoi.isLocallyConstant_ringInverseImage_of_smallSites`, which transcribes the
argument below at `RingCat`, using the identification of sheaves of rings with internal ring
objects (`CategoryTheory.Sites.RingSheaf.equivalence`) where the argument below uses
`CategoryTheory.Sites.AbelianSheaf.equivalence`. Nothing in the argument is special to
commutativity or to the absence of a second operation.

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

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Sites CategoryTheory.Sites.AbelianSheaf Opposite
open Stacks.ConstantSheaf Stacks.Sites.AbelianPullback Stacks.Topos.Skyscraper

universe w

namespace MorphismOfTopoi

attribute [local instance] cartesianPresheafTypes braidedPresheafTypes cartesianSheafTypes
  braidedSheafTypes braidedSheafToPresheafTypes

variable {C : Type w} [SmallCategory C] {D : Type w} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))

section Relocalization

variable {V : C} {Y : D}
  (σ : (presheafToSheaf J (Type w)).obj (yoneda.obj V) ⟶
    f.inverseImage.obj ((presheafToSheaf K (Type w)).obj (yoneda.obj Y)))

/-- **The relocalization along a section, acting on sheaves of abelian groups.** The group
operations of an abelian sheaf on `D/Y` are read as the operations of an internal commutative
group object in sheaves of sets, the finite-product-preserving
`MorphismOfTopoi.sectionRelocalization` carries those to operations again, and the result is read
back sectionwise. -/
public def abelianSectionRelocalization :
    Sheaf (K.over Y) AddCommGrpCat.{w} ⥤ Sheaf (J.over V) AddCommGrpCat.{w} :=
  letI : (sectionRelocalization J K f σ).Braided := .ofChosenFiniteProducts _
  internalSheaf (K.over Y) ⋙ (sectionRelocalization J K f σ).mapCommGrp ⋙
    externalSheaf (J.over V)

/-- **The relocalization carries the restriction of an abelian sheaf to `Y` to the restriction of
its abelian inverse image to `V`**, naturally in the sheaf.

This is `MorphismOfTopoi.sectionRelocalizationOverPullbackIso` lifted to internal commutative
group objects by `CategoryTheory.Functor.mapCommGrpNatIso`, with the two restrictions read on
internal commutative groups by `Stacks.Sites.AbelianPullback.overPullbackInternalIso` and
`.overPullbackExternalIso`. -/
public def abelianSectionRelocalizationOverPullbackIso :
    K.overPullback AddCommGrpCat.{w} Y ⋙ abelianSectionRelocalization J K f σ ≅
      CategoryTheory.Sites.abelianInverseImage f ⋙ J.overPullback AddCommGrpCat.{w} V := by
  haveI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  letI : f.inverseImage.Braided := .ofChosenFiniteProducts _
  letI : (sectionRelocalization J K f σ).Braided := .ofChosenFiniteProducts _
  letI : (K.overPullback (Type w) Y).Braided := .ofChosenFiniteProducts _
  letI : (J.overPullback (Type w) V).Braided := .ofChosenFiniteProducts _
  exact Functor.isoWhiskerRight (overPullbackInternalIso K Y)
      ((sectionRelocalization J K f σ).mapCommGrp ⋙ externalSheaf (J.over V)) ≪≫
    Functor.isoWhiskerLeft (internalSheaf K)
      (Functor.isoWhiskerRight (Functor.mapCommGrpCompIso
        (F := K.overPullback (Type w) Y) (G := sectionRelocalization J K f σ)).symm
          (externalSheaf (J.over V))) ≪≫
    Functor.isoWhiskerLeft (internalSheaf K)
      (Functor.isoWhiskerRight (Functor.mapCommGrpNatIso
        (sectionRelocalizationOverPullbackIso J K f σ)) (externalSheaf (J.over V))) ≪≫
    Functor.isoWhiskerLeft (internalSheaf K)
      (Functor.isoWhiskerRight (Functor.mapCommGrpCompIso
        (F := f.inverseImage) (G := J.overPullback (Type w) V)) (externalSheaf (J.over V))) ≪≫
    Functor.isoWhiskerLeft (internalSheaf K ⋙ f.inverseImage.mapCommGrp)
      (overPullbackExternalIso J V).symm

/-- **The relocalization carries the constant sheaf of abelian groups on an abelian group to the
constant sheaf of abelian groups on the same group**, naturally in the group.

This is `MorphismOfTopoi.sectionRelocalizationConstantSheafIso` lifted to internal commutative
group objects by `CategoryTheory.Functor.mapCommGrpNatIso`, with the two constant sheaves read on
internal commutative groups by `Stacks.Sites.AbelianPullback.constantSheafInternalIso` and
`.constantSheafExternalIso`. The trivializing group is unchanged. -/
public def abelianSectionRelocalizationConstantSheafIso :
    constantSheaf (K.over Y) AddCommGrpCat.{w} ⋙ abelianSectionRelocalization J K f σ ≅
      constantSheaf (J.over V) AddCommGrpCat.{w} := by
  letI : (sectionRelocalization J K f σ).Braided := .ofChosenFiniteProducts _
  letI : (constantSheaf (K.over Y) (Type w)).Braided := .ofChosenFiniteProducts _
  letI : (constantSheaf (J.over V) (Type w)).Braided := .ofChosenFiniteProducts _
  exact Functor.isoWhiskerRight (constantSheafInternalIso (K.over Y))
      ((sectionRelocalization J K f σ).mapCommGrp ⋙ externalSheaf (J.over V)) ≪≫
    Functor.isoWhiskerLeft commGrpAddEquivalence.inverse
      (Functor.isoWhiskerRight (Functor.mapCommGrpCompIso
        (F := constantSheaf (K.over Y) (Type w)) (G := sectionRelocalization J K f σ)).symm
          (externalSheaf (J.over V))) ≪≫
    Functor.isoWhiskerLeft commGrpAddEquivalence.inverse
      (Functor.isoWhiskerRight (Functor.mapCommGrpNatIso
        (sectionRelocalizationConstantSheafIso J K f σ)) (externalSheaf (J.over V))) ≪≫
    constantSheafExternalIso (J.over V)

/-- **A trivialization of an abelian sheaf survives the abelian inverse image along a section,
with the same value.** If `G` restricted to `Y` is the constant sheaf of abelian groups on an
abelian group `E`, and `V` carries a section of `f⁻¹h_Y^#`, then the abelian inverse image of `G`
restricted to `V` is the constant sheaf of abelian groups on the same `E`.

Apply `MorphismOfTopoi.abelianSectionRelocalization` to the trivialization and read the two sides
with `MorphismOfTopoi.abelianSectionRelocalizationConstantSheafIso` and
`MorphismOfTopoi.abelianSectionRelocalizationOverPullbackIso`. -/
public def abelianConstantIsoOverPullbackInverseImageOfSection
    (G : Sheaf K AddCommGrpCat.{w}) (E : AddCommGrpCat.{w})
    (c : (constantSheaf (K.over Y) AddCommGrpCat.{w}).obj E ≅
      (K.overPullback AddCommGrpCat.{w} Y).obj G) :
    (constantSheaf (J.over V) AddCommGrpCat.{w}).obj E ≅
      (J.overPullback AddCommGrpCat.{w} V).obj
        ((CategoryTheory.Sites.abelianInverseImage f).obj G) :=
  ((abelianSectionRelocalizationConstantSheafIso J K f σ).app E).symm ≪≫
    (abelianSectionRelocalization J K f σ).mapIso c ≪≫
    (abelianSectionRelocalizationOverPullbackIso J K f σ).app G

end Relocalization

/-- **Tag 093R for locally constant sheaves of abelian groups.** The inverse image of a locally
constant sheaf of abelian groups along an arbitrary morphism of topoi between the topoi of
sheaves of sets on two small sites is locally constant.

No functor between the two sites, no final object in either, and no finiteness of the local
values is assumed. The covering of an object `U` of `C` is the one
`Stacks.Topos.exists_cover_inverseImage_sections` produces for the family of sheaves represented
by the objects of `D` over which `G` is trivialized as an abelian sheaf, and on a member `V` of
it the section it carries trivializes the abelian inverse image over `V`, with the same
trivializing group, by
`MorphismOfTopoi.abelianConstantIsoOverPullbackInverseImageOfSection`. -/
@[stacks 093R "locally constant sheaves of abelian groups, for an arbitrary morphism of topoi \
  between the topoi of sheaves of sets on two small sites"]
public lemma isLocallyConstant_abelianInverseImage_of_smallSites
    (G : Sheaf K AddCommGrpCat.{w}) [hG : IsLocallyConstant K G] :
    IsLocallyConstant J ((CategoryTheory.Sites.abelianInverseImage f).obj G) where
  exists_cover U := by
    obtain ⟨T, hT⟩ := Stacks.Topos.exists_cover_inverseImage_sections f
      (Stacks.Topos.representedFamily K
        fun Y => Sheaf.IsConstant (K.over Y)
          ((K.overPullback AddCommGrpCat.{w} Y).obj G))
      (Stacks.Topos.jointlyLocallyInhabited_representedFamily K _
        fun W => by
          obtain ⟨I, Z, g, hg, hc⟩ := hG.exists_cover W
          exact ⟨I, Z, g, hg, hc⟩) U
    refine ⟨Σ V : C, {g : V ⟶ U // T.1.arrows g}, fun p => p.1, fun p => p.2.1,
      sieve_ofArrows_arrows_mem J _ T.2, fun p => ?_⟩
    obtain ⟨i, ⟨x⟩⟩ := hT p.1 p.2.1 p.2.2
    have := i.2
    obtain ⟨E, ⟨c⟩⟩ := Sheaf.mem_essImage_of_isConstant (K.over i.1)
      ((K.overPullback AddCommGrpCat.{w} i.1).obj G)
    exact ⟨E, ⟨abelianConstantIsoOverPullbackInverseImageOfSection J K f
      (Stacks.Topos.sectionHom J _ x) G E c⟩⟩

end MorphismOfTopoi

end
