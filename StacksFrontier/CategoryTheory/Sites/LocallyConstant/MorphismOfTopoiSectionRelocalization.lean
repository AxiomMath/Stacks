module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantSheafGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import StacksFrontier.CategoryTheory.Sites.Topos.JointlyLocallyInhabited
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.InverseImageFiniteLocallyConstant
import StacksCore.Tactic.StacksAttribute

/-!
# Relocalization of a morphism of topoi along a section, and Tag 093R for sheaves of sets

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi between the topoi of sheaves of sets on two
small sites `(C, J)` and `(D, K)` — an adjoint pair with left exact inverse image, and nothing
more: no functor between the two sites is assumed. Tag 093R asserts that `f⁻¹` carries locally
constant sheaves of sets, of groups, of abelian groups, of rings and of modules over a fixed
ring to locally constant sheaves. This file proves the assertion for sheaves of **sets**
(`MorphismOfTopoi.isLocallyConstant_inverseImage_of_smallSites`), together with the finite
version; the algebraic coefficients are a separate matter, and the last section of this
docstring says where they stand.

Local constancy is a statement about *restrictions* `G|_V`, so what the proof needs is a
comparison of `f⁻¹` with restriction, and the only data available for one is a section. The two
steps are:

**A covering carrying sections.** If `G` is locally constant on `D`, then the sheaves `h_Y^#`
represented by the objects `Y` over which `G` becomes constant are *jointly locally inhabited*:
every object of `D` is covered by objects admitting a section of one of them, since a
trivializing covering of `W` is made of such objects. Joint local inhabitedness is preserved by
inverse image (`Stacks.Topos.exists_cover_inverseImage_sections`), so every object `U` of `C`
has a covering each member `V` of which carries a section of some `f⁻¹h_Y^#`, that is, a
morphism `σ : h_V^# ⟶ f⁻¹h_Y^#`.

**Relocalization along that section.** Restriction to an object is, read in the slice topos
through Stacks 00Y1 (`CategoryTheory.OverShriek.sheafEquivalence`), the product with the
represented sheaf: `j_{V!}(G|_V) = G × h_V^#` over `h_V^#`
(`CategoryTheory.OverShriek.starObjIso`, the right adjoint half of 00Y1, obtained from
uniqueness of right adjoints). A section `σ : h_V^# ⟶ f⁻¹h_Y^#` therefore relocalizes: applying
`f⁻¹` to an object over `h_Y^#` and then base changing along `σ` carries `G × h_Y^#` to
`f⁻¹G × h_V^#` (`MorphismOfTopoi.sectionRelocalizationIso`), because `f⁻¹` is left exact and
base change along `σ` carries a product projection to a product projection
(`CategoryTheory.Over.starPullbackIsoStar`). Transporting a trivialization of `G|_Y` through
this chain gives a trivialization of `(f⁻¹G)|_V` with the *same* value
(`MorphismOfTopoi.constantIsoOverPullbackInverseImageOfSection`), the constant sheaves being
matched by `Stacks.ConstantSheaf.inverseImageConstantSheafIsoOfSmallSites` on `C` and by
`Stacks.ConstantSheaf.overPullbackConstantSheafIsoOfSmallSite` on `D` — neither of which asks
for a final object in either site.

No adjoint of the base change along `σ` is constructed, and so no localized morphism of topoi
`Sh(C/V) ⟶ Sh(D/Y)`: the argument transports *objects* along the relocalization and never needs
the relocalization to be a morphism of topoi. That is what replaces the localization datum of
`MorphismOfTopoi.LocalizationDatum`, which the sites-free case of the tag could not produce.

The restriction to *small* sites is where the represented sheaves `h_V^#` live in the same
category of sheaves of sets as `G`, and is the setting of the source.

## Main definitions

* `CategoryTheory.OverShriek.starCompInverseIsoOverPullback` and
  `CategoryTheory.OverShriek.starObjIso` — restriction to `U` is the product with `h_U^#`, read
  in `Sh(C/U)` through Stacks 00Y1.
* `Stacks.Topos.representedFamily` — the family of sheaves represented by the objects with a
  given property, with `Stacks.Topos.jointlyLocallyInhabited_representedFamily` for when it is
  jointly locally inhabited.
* `MorphismOfTopoi.sectionRelocalizationIso` — **the relocalization square along a section**
  `σ : h_V^# ⟶ f⁻¹h_Y^#`: base change along `σ` after `f⁻¹` carries `M × h_Y^#` to
  `f⁻¹M × h_V^#`.
* `MorphismOfTopoi.constantIsoOverPullbackInverseImageOfSection` — a trivialization of `G` over
  `Y` plus a section `h_V^# ⟶ f⁻¹h_Y^#` give a trivialization of `f⁻¹G` over `V`, with the same
  value.

## Main results

* `MorphismOfTopoi.isLocallyConstant_inverseImage_of_smallSites` — **Tag 093R**: the inverse
  image of a locally constant sheaf of sets along an arbitrary morphism of topoi between the
  topoi of sheaves of sets on two small sites is locally constant.
* `MorphismOfTopoi.isFiniteLocallyConstant_inverseImage_of_smallSites` — the same for a finite
  locally constant sheaf of sets, the constant values being unchanged.

## What of Tag 093R is *not* proved here

Only the sheaves of sets of the tag's list. The inverse image of an abelian sheaf along a
morphism of topoi is `CategoryTheory.Sites.abelianInverseImage`, got by carrying the group
operations through the left exact `f⁻¹` as operations on internal commutative group objects, and
the trivializations produced below are isomorphisms of sheaves of *sets*: lifting them to the
abelian inverse image means reading the whole relocalization on internal commutative group
objects.

That is done elsewhere, not here: the relocalization is recast as a single
finite-product-preserving functor in
`StacksFrontier/CategoryTheory/Sites/LocallyConstant/SectionRelocalizationFunctor.lean`, and
`MorphismOfTopoi.isLocallyConstant_abelianInverseImage_of_smallSites` in
`StacksFrontier/CategoryTheory/Sites/LocallyConstant/AbelianLocallyConstantInverseImage.lean` is the
abelian case of the tag at this file's generality. Two weaker abelian statements are also
available: the *constant* one, by `MorphismOfTopoi.isConstant_abelianInverseImage`, and the
*finite* locally constant one, by
`MorphismOfTopoi.isFiniteLocallyConstant_abelianInverseImage_of_smallSites`, because finite local
constancy of an abelian sheaf is a property of its underlying sheaf of sets.

The cases of sheaves of groups, of rings and of modules over a fixed ring remain open: the
abelian argument consumes the identification of abelian sheaves with commutative group objects
in sheaves of sets, and the library has it for `AddCommGrpCat` only. What it has for those
coefficients is `Stacks.ConstantSheaf.isLocallyConstant_sheafPullback`, which holds for an
arbitrary coefficient category but only along a *morphism of sites* — a continuous left exact
cover-preserving functor between the two sites — and so is strictly less general in `f` than the
statements below.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf

universe wc w

namespace CategoryTheory.OverShriek

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C) (U : C)

/-- **Restriction to `U` is the product with `h_U^#`**, read in `Sh(C/U)` through the
equivalence `Sh(C/U) ≌ Sh(C)/h_U^#` of Stacks 00Y1.

This is the right adjoint half of that equivalence: `j_{U!}` is the equivalence followed by
`Over.forget` (`CategoryTheory.OverShriek.sheafFunctorToOverForgetIso`), and `Over.forget` is
left adjoint to `Over.star`, so the right adjoint `j_U^{-1}` of `j_{U!}` is `Over.star h_U^#`
followed by the inverse of the equivalence. -/
public def starCompInverseIsoOverPullback :
    Over.star ((presheafToSheaf J (Type w)).obj (yoneda.obj U)) ⋙
        (sheafEquivalence (U := U) J).inverse ≅
      J.overPullback (Type w) U :=
  Adjunction.rightAdjointUniq
    (((sheafEquivalence (U := U) J).toAdjunction.comp
      (Over.forgetAdjStar _)).ofNatIsoLeft (sheafFunctorToOverForgetIso J))
    ((Over.forget U).sheafAdjunctionContinuous (Type w) (J.over U) J)

/-- **`h_U^# × M` is `j_{U!}` of the restriction of `M` to `U`**, the object form of
`CategoryTheory.OverShriek.starCompInverseIsoOverPullback`. -/
public def starObjIso (M : Sheaf J (Type w)) :
    (Over.star ((presheafToSheaf J (Type w)).obj (yoneda.obj U))).obj M ≅
      (sheafFunctorToOver (U := U) J).obj ((J.overPullback (Type w) U).obj M) :=
  ((sheafEquivalence (U := U) J).counitIso.app _).symm ≪≫
    (sheafEquivalence (U := U) J).functor.mapIso ((starCompInverseIsoOverPullback J U).app M)

end CategoryTheory.OverShriek

namespace Stacks.Topos

variable {D : Type w} [SmallCategory D] (K : GrothendieckTopology D)

/-- **The family of sheaves represented by the objects with a given property.** -/
public def representedFamily (P : D → Prop) : { Y : D // P Y } → Sheaf K (Type w) :=
  fun i => (presheafToSheaf K (Type w)).obj (yoneda.obj i.1)

/-- **The represented family of a property is jointly locally inhabited** as soon as every
object of the site is covered by objects having the property: a member `Z i` of such a covering
carries the section of `h_{Z i}^#` given by its own identity, and every object above `Z i`
carries the induced one. -/
public lemma jointlyLocallyInhabited_representedFamily (P : D → Prop)
    (h : ∀ W : D, ∃ (I : Type w) (Z : I → D) (g : ∀ i, Z i ⟶ W),
      Sieve.ofArrows Z g ∈ K W ∧ ∀ i, P (Z i)) :
    JointlyLocallyInhabited K (representedFamily K P) := by
  intro W
  obtain ⟨I, Z, g, hg, hP⟩ := h W
  refine K.superset_covering ?_ hg
  intro V k hk
  obtain ⟨i, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hk
  exact ⟨⟨Z i, hP i⟩, ⟨yonedaEquiv (yoneda.map b ≫ toSheafify K (yoneda.obj (Z i)))⟩⟩

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)

/-- A section of a sheaf over `V`, read as a morphism from the sheaf represented by `V`: the
sheafification adjunction turns it into a morphism of presheaves out of `h_V`, which the Yoneda
lemma identifies with the section. -/
public def sectionHom (N : Sheaf J (Type w)) {V : C} (x : N.obj.obj (op V)) :
    (presheafToSheaf J (Type w)).obj (yoneda.obj V) ⟶ N :=
  ((sheafificationAdjunction J (Type w)).homEquiv _ _).symm (yonedaEquiv.symm x)

end Stacks.Topos

namespace MorphismOfTopoi

variable {C : Type w} [SmallCategory C] {D : Type w} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))

/-- **The relocalization square along a section** `σ : h_V^# ⟶ f⁻¹h_Y^#`. Taking the inverse
image of an object over `h_Y^#` and then base changing along `σ` carries `M × h_Y^#` to
`f⁻¹M × h_V^#`.

The first factor is `Stacks.ConstantSheaf.starPostIso`, left exactness of `f⁻¹`; the second is
`CategoryTheory.Over.starPullbackIsoStar`, base change of a product projection. -/
public def sectionRelocalizationIso {V : C} {Y : D}
    (σ : (presheafToSheaf J (Type w)).obj (yoneda.obj V) ⟶
      f.inverseImage.obj ((presheafToSheaf K (Type w)).obj (yoneda.obj Y)))
    (M : Sheaf K (Type w)) :
    (Over.pullback σ).obj ((Over.post f.inverseImage).obj
        ((Over.star ((presheafToSheaf K (Type w)).obj (yoneda.obj Y))).obj M)) ≅
      (Over.star ((presheafToSheaf J (Type w)).obj (yoneda.obj V))).obj
        (f.inverseImage.obj M) :=
  haveI := f.preservesFiniteLimits
  (Over.pullback σ).mapIso ((starPostIso f.inverseImage _).app M) ≪≫
    (Over.starPullbackIsoStar σ).app (f.inverseImage.obj M)

/-- **A trivialization survives inverse image along a section, with the same value.** If `G`
restricted to `Y` is the constant sheaf on a set `E`, and `V` carries a section of `f⁻¹h_Y^#`,
then `f⁻¹G` restricted to `V` is the constant sheaf on the same `E`.

Read in the slice topoi through Stacks 00Y1, the trivialization says `G × h_Y^# ≅ C_E × h_Y^#`
over `h_Y^#`, where `C_E` is the constant sheaf on `E`; the relocalization square
`MorphismOfTopoi.sectionRelocalizationIso` turns this into
`f⁻¹G × h_V^# ≅ f⁻¹C_E × h_V^#` over `h_V^#`, and `f⁻¹C_E` is again the constant sheaf on `E`
because `f⁻¹` is a left exact left adjoint
(`Stacks.ConstantSheaf.inverseImageConstantSheafIsoOfSmallSites`). Reading back gives the
trivialization of `(f⁻¹G)|_V`. The two restrictions of constant sheaves are matched by
`Stacks.ConstantSheaf.overPullbackConstantSheafIsoOfSmallSite`, so no final object of either
site is used. -/
public def constantIsoOverPullbackInverseImageOfSection {V : C} {Y : D}
    (σ : (presheafToSheaf J (Type w)).obj (yoneda.obj V) ⟶
      f.inverseImage.obj ((presheafToSheaf K (Type w)).obj (yoneda.obj Y)))
    (G : Sheaf K (Type w)) (E : Type w)
    (c : (constantSheaf (K.over Y) (Type w)).obj E ≅ (K.overPullback (Type w) Y).obj G) :
    (constantSheaf (J.over V) (Type w)).obj E ≅
      (J.overPullback (Type w) V).obj (f.inverseImage.obj G) :=
  haveI := f.preservesFiniteLimits
  let Ξ : Over ((presheafToSheaf K (Type w)).obj (yoneda.obj Y)) ⥤
      Over ((presheafToSheaf J (Type w)).obj (yoneda.obj V)) :=
    Over.post f.inverseImage ⋙ Over.pullback σ
  let β : (K.overPullback (Type w) Y).obj ((constantSheaf K (Type w)).obj E) ≅
      (K.overPullback (Type w) Y).obj G :=
    (overPullbackConstantSheafIsoOfSmallSite K Y).app E ≪≫ c
  let γ : (Over.star ((presheafToSheaf K (Type w)).obj (yoneda.obj Y))).obj
        ((constantSheaf K (Type w)).obj E) ≅
      (Over.star ((presheafToSheaf K (Type w)).obj (yoneda.obj Y))).obj G :=
    OverShriek.starObjIso K Y _ ≪≫
      (OverShriek.sheafFunctorToOver (U := Y) K).mapIso β ≪≫
      (OverShriek.starObjIso K Y G).symm
  let κ : f.inverseImage.obj ((constantSheaf K (Type w)).obj E) ≅
      (constantSheaf J (Type w)).obj E :=
    (inverseImageConstantSheafIsoOfSmallSites f.adj).app E
  let ε : (Over.star ((presheafToSheaf J (Type w)).obj (yoneda.obj V))).obj
        ((constantSheaf J (Type w)).obj E) ≅
      (Over.star ((presheafToSheaf J (Type w)).obj (yoneda.obj V))).obj
        (f.inverseImage.obj G) :=
    (Over.star _).mapIso κ.symm ≪≫ (sectionRelocalizationIso J K f σ _).symm ≪≫
      Ξ.mapIso γ ≪≫ sectionRelocalizationIso J K f σ G
  ((overPullbackConstantSheafIsoOfSmallSite J V).app E).symm ≪≫
    (OverShriek.sheafEquivalence (U := V) J).fullyFaithfulFunctor.preimageIso
      ((OverShriek.starObjIso J V _).symm ≪≫ ε ≪≫ OverShriek.starObjIso J V _)

/-- **Tag 093R.** The inverse image of a locally constant sheaf of sets along an arbitrary
morphism of topoi between the topoi of sheaves of sets on two small sites is locally constant.

No functor between the two sites, and no final object in either, is assumed: the covering of an
object `U` of `C` is the one `Stacks.Topos.exists_cover_inverseImage_sections` produces for the
family of sheaves represented by the objects over which `G` is trivialized, and on a member of
it the section it carries trivializes `(f⁻¹G)|_V` by
`MorphismOfTopoi.constantIsoOverPullbackInverseImageOfSection`. -/
@[stacks 093R "locally constant sheaves of sets, for an arbitrary morphism of topoi between the \
  topoi of sheaves of sets on two small sites", sga "3 X 9.2.1" "(4)"]
public lemma isLocallyConstant_inverseImage_of_smallSites (G : Sheaf K (Type w))
    [hG : IsLocallyConstant K G] : IsLocallyConstant J (f.inverseImage.obj G) where
  exists_cover U := by
    obtain ⟨T, hT⟩ := Stacks.Topos.exists_cover_inverseImage_sections f
      (Stacks.Topos.representedFamily K
        fun Y => Sheaf.IsConstant (K.over Y) ((K.overPullback (Type w) Y).obj G))
      (Stacks.Topos.jointlyLocallyInhabited_representedFamily K _
        fun W => by
          obtain ⟨I, Z, g, hg, hc⟩ := hG.exists_cover W
          exact ⟨I, Z, g, hg, hc⟩) U
    refine ⟨Σ V : C, {g : V ⟶ U // T.1.arrows g}, fun p => p.1, fun p => p.2.1,
      sieve_ofArrows_arrows_mem J _ T.2, fun p => ?_⟩
    obtain ⟨i, ⟨x⟩⟩ := hT p.1 p.2.1 p.2.2
    have := i.2
    obtain ⟨E, ⟨c⟩⟩ := Sheaf.mem_essImage_of_isConstant (K.over i.1)
      ((K.overPullback (Type w) i.1).obj G)
    exact ⟨E, ⟨constantIsoOverPullbackInverseImageOfSection J K f
      (Stacks.Topos.sectionHom J _ x) G E c⟩⟩

/-- **Tag 093R.** The inverse image of a *finite* locally constant sheaf of sets along an
arbitrary morphism of topoi between the topoi of sheaves of sets on two small sites is finite
locally constant.

The constant values are unchanged by
`MorphismOfTopoi.constantIsoOverPullbackInverseImageOfSection`, so their finiteness needs no
argument; the covering is the one of
`MorphismOfTopoi.isLocallyConstant_inverseImage_of_smallSites`, taken for the objects over which
`G` becomes constant with a finite value. -/
@[stacks 093R "finite locally constant sheaves of sets, for an arbitrary morphism of topoi \
  between the topoi of sheaves of sets on two small sites"]
public lemma isFiniteLocallyConstant_inverseImage_of_smallSites {FA : Type w → Type w → Type*}
    {CA : Type w → Type wc} [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)]
    [ConcreteCategory.{wc} (Type w) FA] (G : Sheaf K (Type w))
    [hG : IsFiniteLocallyConstant (FD := FA) (CD := CA) K G] :
    IsFiniteLocallyConstant (FD := FA) (CD := CA) J (f.inverseImage.obj G) where
  exists_finite_cover U := by
    obtain ⟨T, hT⟩ := Stacks.Topos.exists_cover_inverseImage_sections f
      (Stacks.Topos.representedFamily K
        fun Y => ∃ E : Type w, Finite (CA E) ∧ Nonempty
          ((constantSheaf (K.over Y) (Type w)).obj E ≅ (K.overPullback (Type w) Y).obj G))
      (Stacks.Topos.jointlyLocallyInhabited_representedFamily K _
        fun W => by
          obtain ⟨I, Z, g, hg, hc⟩ := hG.exists_finite_cover W
          exact ⟨I, Z, g, hg, hc⟩) U
    refine ⟨Σ V : C, {g : V ⟶ U // T.1.arrows g}, fun p => p.1, fun p => p.2.1,
      sieve_ofArrows_arrows_mem J _ T.2, fun p => ?_⟩
    obtain ⟨i, ⟨x⟩⟩ := hT p.1 p.2.1 p.2.2
    obtain ⟨E, hE, ⟨c⟩⟩ := i.2
    exact ⟨E, hE, ⟨constantIsoOverPullbackInverseImageOfSection J K f
      (Stacks.Topos.sectionHom J _ x) G E c⟩⟩

end MorphismOfTopoi

end
