module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Sheaf.HasSheafComposeForgetRing
public import StacksFrontier.CategoryTheory.Sites.Topos.LocalizationOfTopoi

/-!
# Localization of a ringed topos at a sheaf

Let `X` be a ringed topos, presented by a site `(C, J)` with a structure sheaf `O` of
commutative rings, and let `F` be a sheaf of sets on `C`. The *site of elements* of `F` is the
category `CostructuredArrow yoneda F.obj` of pairs `(U, s)` with `s` a section of `F` over `U`,
equipped with the topology restricted along its projection to `C`; by Stacks 0791 its topos of
sheaves is the slice topos `Sh(C)/F`. Giving it the restriction of `O` along that projection as
structure sheaf makes it a ringed topos, and the projection becomes a morphism of ringed topoi
onto `X`.

This file supplies those four objects — the site of elements, its projection and topology, the
localized ringed topos — together with the localization morphism, both as a morphism of topoi
and as a morphism of ringed topoi. The structure map is the canonical identification of the
inverse image `π⁻¹O` of the structure sheaf with its restriction to the site of elements,
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, carried into direct-image form by the
adjunction `Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`.

## Main definitions

* `AlgebraicGeometry.RingedTopos.elementSite`: the site of elements of `F`.
* `AlgebraicGeometry.RingedTopos.elementProjection`: its projection to the site of `X`.
* `AlgebraicGeometry.RingedTopos.elementTopology`: the topology on the site of elements, as the
  topology of `X` restricted along the projection.
* `AlgebraicGeometry.RingedTopos.localizedRingedTopos`: the localization of `X` at `F`.
* `AlgebraicGeometry.RingedTopos.localizationToposMorphism`: the localization as a morphism of
  topoi, with restriction as inverse image.
* `AlgebraicGeometry.RingedTopos.localizationInverseImageCommRingIso`: the identification of
  the canonical inverse image of `O` with its restriction to the site of elements.
* `AlgebraicGeometry.RingedTopos.localizationMorphism`: the localization as a morphism of
  ringed topoi.

## Main results

* `AlgebraicGeometry.RingedTopos.localization_fSharp_inverseImage`: the structure map of the
  localization, in inverse-image form, is that identification.

## Implementation notes

This is the `AlgebraicGeometry.RingedTopos` form of the localization, i.e. the one whose site
objects, site morphisms and structure-sheaf sections have **independent** universes (Stacks
01D3 part (1)). It is not interchangeable with
`Stacks.Sheaves.LocalizedRingedTopos.localizedRingedTopos` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocalizedRingedTopos.lean`, which builds the same
four objects over the ten-field `Stacks.Sheaves.LocallyRingedTopos.RingedTopos`, a
single-universe structure carrying the units identification as data. The two are definitions of
different types, so neither can be
substituted for the other; what that file adds beyond these objects is the transfer of the two
locally-ringed conditions, which is Stacks 04IH and is not repeated here.

Continuity and cocontinuity of the projection are extracted from
`Presheaf.IsSheaf.exists_sheafEquivalence_costructuredArrow_yoneda`, the sheaf-level form of
Stacks 0791, rather than reproved. Left exactness of the inverse image is the instance
`CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous` (Stacks 04J4), so the
morphism of topoi needs no new argument.

The morphism of ringed topoi is the two-field `AlgebraicGeometry.RingedToposHom` of Stacks 01D3
part (2): it takes only the direct-image form `O ⟶ π_*O_F` of the structure map, and the
inverse-image form is derived from it through `commRingImageAdjunction`. That is why the
structure map is given here as the adjunct of the comparison and
`localization_fSharp_inverseImage` recovers the comparison itself.

Universes: the site morphisms and the sections of `O` are taken in one universe `v`, as a
representable presheaf must be a presheaf of sets of that size, while the site objects live in an
independent universe `u`. The site of elements of a sheaf on a `Type u` site with
`Category.{v}` homs is a `Type (max u v)` category with `Category.{v}` homs, so the localization
of a `RingedTopos.{v, u, v}` is a `RingedTopos.{v, max u v, v}`. The independent object universe
is what lets the small étale ringed topos of an algebraic space, a `RingedTopos.{u, u + 1, u}`,
be localized.

## References

* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe v u u'

namespace AlgebraicGeometry.RingedTopos

variable (X : RingedTopos.{v, u, v}) [EssentiallySmall.{v} X.C] (F : X.Topos)

/-- The site of elements of `F`: pairs `(U, s)` with `U` an object of the site of `X` and `s` a
section of `F` over `U`. -/
abbrev elementSite := CostructuredArrow yoneda F.obj

/-- The projection from the site of elements of `F` to the site of `X`. -/
abbrev elementProjection : elementSite X F ⥤ X.C :=
  CostructuredArrow.proj yoneda F.obj

/-- The topology on the site of elements: the topology of `X`, restricted along the projection.
By Stacks 0791 its covering sieves are the coverings of the source. -/
abbrev elementTopology : GrothendieckTopology (elementSite X F) :=
  (elementProjection X F).restrictedTopology X.J

omit [EssentiallySmall.{v} X.C] in
/-- Presheaves of sets on an essentially small category form a locally small category: the
presheaf category is equivalent to the presheaf category of a small model. -/
@[sga "4 IV 1.1.2" "special case"]
instance locallySmall_presheaf {C : Type u} [Category.{v} C] [EssentiallySmall.{v} C] :
    LocallySmall.{v} (Cᵒᵖ ⥤ Type v) :=
  (locallySmall_congr (equivSmallModel.{v} C).op.congrLeft).mpr inferInstance

/-- The site of elements of a sheaf on an essentially small site is essentially small. -/
instance essentiallySmall_elementSite : EssentiallySmall.{v} (elementSite X F) :=
  CostructuredArrow.essentiallySmall

omit [EssentiallySmall.{v} X.C] in
/-- A functor out of an essentially small category into a locally small one admits pointwise
right Kan extensions of presheaves of sets: the indexing categories are essentially small. -/
theorem hasPointwiseRightKanExtension_of_essentiallySmall {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v} B] [EssentiallySmall.{v} A] [LocallySmall.{v} B] (L : A ⥤ B)
    (P : A ⥤ Type v) : L.HasPointwiseRightKanExtension P := fun Y ↦
  have := hasLimitsOfShape_of_essentiallySmall.{v} (StructuredArrow Y L) (Type v)
  inferInstance

attribute [local instance] hasPointwiseRightKanExtension_of_essentiallySmall

/-- The projection from the site of elements of `F` to the site of `X` is continuous for the
restricted topology. -/
noncomputable instance elementProjection_isContinuous :
    (elementProjection X F).IsContinuous (elementTopology X F) X.J := by
  obtain ⟨h, _, _, _⟩ :=
    (Presheaf.IsSheaf.exists_sheafEquivalence_costructuredArrow_yoneda F.property).2.2
  exact h

/-- The projection from the site of elements of `F` to the site of `X` is cocontinuous for the
restricted topology. -/
noncomputable instance elementProjection_isCocontinuous :
    (elementProjection X F).IsCocontinuous (elementTopology X F) X.J := by
  obtain ⟨_, h, _, _⟩ :=
    (Presheaf.IsSheaf.exists_sheafEquivalence_costructuredArrow_yoneda F.property).2.2
  exact h

/-- The **localization of the ringed topos `X` at the sheaf `F`**: the site of elements of `F`,
with the restricted topology, and with the restriction of `O` along the projection as structure
sheaf. -/
@[stacks 04IE "the localized ringed topos",
  stacks 04J2 "part (1): the localization of the ringed topos at F", sga "4 IV 11.2.1" "(E/X, A|X)"]
noncomputable abbrev localizedRingedTopos : RingedTopos.{v, max u v, v} where
  C := elementSite X F
  J := elementTopology X F
  O := ((elementProjection X F).sheafPushforwardContinuous CommRingCat
    (elementTopology X F) X.J).obj X.O

/-- The localization as a morphism of topoi: its inverse image is restriction along the
projection from the site of elements, its direct image the right adjoint supplied by
cocontinuity of that projection. -/
noncomputable def localizationToposMorphism :
    MorphismOfTopoi (localizedRingedTopos X F).Topos X.Topos where
  inverseImage := (elementProjection X F).sheafPushforwardContinuous (Type v)
    (elementTopology X F) X.J
  pushforward := (elementProjection X F).sheafPushforwardCocontinuous (Type v)
    (elementTopology X F) X.J
  adj := (elementProjection X F).sheafAdjunctionCocontinuous (Type v)
    (elementTopology X F) X.J
  preservesFiniteLimits :=
    CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous
      (elementTopology X F) X.J (elementProjection X F) (Type v)

/-- The canonical inverse image of the structure sheaf along the localization is its restriction
to the site of elements, which is by definition the structure sheaf of the localization. -/
noncomputable def localizationInverseImageCommRingIso :
    (inverseImageCommRingFunctor.{v, v, v, max u v, v, u} (localizationToposMorphism X F)).obj
        X.O ≅
      (localizedRingedTopos X F).O :=
  restrictionCommRingIso.{v, v, max u v, v, u} (elementTopology X F) X.J (elementProjection X F)
    X.O

/-- The localization as a morphism of ringed topoi: the morphism of topoi above, with the
identification of the inverse image of `O` with the localized structure sheaf as structure
map. -/
@[stacks 04IE "canonical morphism of ringed topoi",
  stacks 04J2 "part (2): the localization morphism", sga "4 IV 11.2.1" "localization morphism"]
noncomputable def localizationMorphism :
    RingedToposHom (localizedRingedTopos X F) X where
  toToposHom := localizationToposMorphism X F
  fSharp := (commRingImageAdjunction (localizationToposMorphism X F)).homEquiv _ _
    (localizationInverseImageCommRingIso X F).hom

/-- The structure map of the localization, in inverse-image form, is the identification of the
inverse image of `O` with its restriction to the site of elements. -/
theorem localization_fSharp_inverseImage :
    (localizationMorphism X F).fSharpInverseImage =
      (localizationInverseImageCommRingIso X F).hom := by
  change ((commRingImageAdjunction (localizationToposMorphism X F)).homEquiv _ _).symm
      ((commRingImageAdjunction (localizationToposMorphism X F)).homEquiv _ _
        (localizationInverseImageCommRingIso X F).hom) = _
  rw [Equiv.symm_apply_apply]

end AlgebraicGeometry.RingedTopos
