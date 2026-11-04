module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import StacksCore.Tactic.StacksAttribute

/-!
# Relocalization of a ringed topos along a morphism of sheaves

Let `X = (Sh(C), O)` be a ringed topos and let `s : G ⟶ F` be a morphism of sheaves of sets
on its site. Localizing `X` at `G` and at `F` gives the two ringed topoi
`Stacks.Sheaves.LocalizedRingedTopos.localizedRingedTopos X G` and
`localizedRingedTopos X F`, whose sites are the sites of elements of `G` and of `F`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocalizedRingedTopos.lean`). Stacks 04J4 says
that `s` induces a morphism between them, that its inverse image is base change along `s`
once the two localizations are identified with the slice topoi, and that the resulting
triangle over `X` commutes, maps of structure sheaves included.

This file builds the *geometric* morphism and the *structure-sheaf* half of that assertion,
and the inverse-image half of the triangle. It does not treat the identification with the
slice topoi, which is the content of Stacks 04IE and is not available here.

## Main definitions

* `Stacks.Sheaves.LocalizedRingedTopos.localizationToposMorphism` — the geometric morphism
  `Sh(C/F) ⟶ Sh(C)` of the localization of `X` at `F`: restriction along the projection from
  the site of elements, with its cocontinuous partner.
* `Stacks.Sheaves.LocalizedRingedTopos.relocalizationToposMorphism` — the geometric morphism
  induced by `s : G ⟶ F`, i.e. restriction along postcomposition of sections with `s`.
* `Stacks.Sheaves.LocalizedRingedTopos.canonicalRelocalizationComparison` — the comparison of
  direct images induced by the equality of the inverse images in the triangle.
* `Stacks.Sheaves.LocalizedRingedTopos.relocalizationRingInverseImage` and
  `relocalizationRingPushforward` — restriction and its cocontinuous partner on sheaves of
  commutative rings, the ring-level image functors of the relocalization morphism.
* `Stacks.Sheaves.LocalizedRingedTopos.relocalizationRingAdjunction` — the adjunction between
  them.
* `Stacks.Sheaves.LocalizedRingedTopos.relocalizationFSharp` — the structure map of the
  relocalization morphism of ringed topoi, in its direct-image form `O_F ⟶ f_* O_G`.

## Main results

* `Stacks.Sheaves.LocalizedRingedTopos.relocalizationRingIso` — **Stacks 04J4**: restricting
  the structure sheaf of the localization at `F` along postcomposition with `s` gives the
  structure sheaf of the localization at `G`. Both are the restriction of `O` along a
  projection from a site of elements, and the two projections agree, so this is the identity
  isomorphism: the identification holds on the nose, which is the strongest form the statement
  can take.
* `Stacks.Sheaves.LocalizedRingedTopos.comp_inverseImage` — **Stacks 04J4**: the inverse image
  of the composite `Sh(C/G) ⟶ Sh(C/F) ⟶ Sh(C)` is *equal* to the inverse image of the
  localization at `G`, again because the two functors of sites agree. This is the
  inverse-image half of the commutative triangle, and it is what makes
  `canonicalRelocalizationComparison` available.
* `Stacks.Sheaves.LocalizedRingedTopos.relocalizationRingAdjunction_homEquiv_symm_fSharp` —
  **Stacks 04J4**: the structure map of the relocalization morphism, read in its
  inverse-image form `f⁻¹O_F ⟶ O_G` through the ring-level adjunction, is the canonical
  identification `relocalizationRingIso`.

## Implementation notes

* **Which ring-level inverse image.** Stacks 01D3 takes a morphism of ringed topoi to carry
  only the direct-image form `f♯ : O_F ⟶ f_*O_G` of its structure map, the inverse-image form
  being recovered through the adjunction on sheaves of *rings* induced by the geometric
  morphism, which is Stacks 00YV. That instance of 00YV is not available in this development
  (see the implementation notes of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposModules.lean`, which carries both
  forms as data for exactly this reason). Here the geometric morphism *is* restriction along a
  functor of sites, so its ring-level images are available directly and with no appeal to
  00YV: they are Mathlib's `Functor.sheafPushforwardContinuous` and
  `Functor.sheafPushforwardCocontinuous` at the value category `CommRingCat`, adjoint by
  `Functor.sheafAdjunctionCocontinuous`. The structure map is defined as the adjunct of
  `relocalizationRingIso` through that adjunction, and
  `relocalizationRingAdjunction_homEquiv_symm_fSharp` is the characterization of it. When the
  00YV comparison between the lift of the set-level inverse image and restriction of ring
  sheaves lands, the 01D3-shaped statement follows by composing with it; nothing here has to
  change.
* **Nothing is transported.** `relocalizationRingIso` and `comp_inverseImage` are `Iso.refl`
  and `rfl`. The reason is that `elementPostcomp s` followed by the projection from the site
  of elements of `F` is the projection from the site of elements of `G` — postcomposition with
  `s` does not move the underlying object of the site — and restriction along a composite is
  the composite of the restrictions on the nose. In particular the equality of inverse images
  needed by `Adjunction.rightAdjointUniq` is definitional, so no coherence is left over.
* **Universes.** `Stacks.Sheaves.LocallyRingedTopos.RingedTopos` keeps the objects, the morphisms
  and the sections of
  the structure sheaf in a single universe `u`, as the library's definition of the localized
  ringed topos does. Nothing here narrows that further: the site of elements of a sheaf on a
  `Type u` site with `Category.{u}` homs is again such a site, so every construction below
  stays inside `RingedTopos.{u}`, and the source's statement is universe-free.
* The three site-theoretic ingredients of the geometric morphism — continuity and cocontinuity
  of `elementPostcomp` and left exactness of restriction along it — are
  `elementPostcomp_isContinuous`, `elementPostcomp_isCocontinuous`
  (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardRightExact.lean`) and
  `elementPostcomp_preservesFiniteLimits`, each of which already carries the `04J4` tag for
  its own clause. They are consumed here, not reproved.

## References

* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sheaves.LocalizedRingedTopos

open Stacks.Sheaves.LocallyRingedTopos

universe u

variable {X : RingedTopos.{u}} {G F : X.Topos}

/-- The geometric morphism `Sh(C/F) ⟶ Sh(C)` underlying the localization of a ringed topos at
a sheaf: its inverse image is restriction along the projection from the site of elements of
`F`, its direct image is the cocontinuous partner of that restriction, and the restriction is
left exact. -/
noncomputable def localizationToposMorphism (X : RingedTopos.{u}) (F : X.Topos) :
    MorphismOfTopoi (localizedRingedTopos X F).Topos X.Topos where
  inverseImage := (elementProjection X F).sheafPushforwardContinuous
    (Type u) (elementTopology X F) X.J
  pushforward := (elementProjection X F).sheafPushforwardCocontinuous
    (Type u) (elementTopology X F) X.J
  adj := (elementProjection X F).sheafAdjunctionCocontinuous
    (Type u) (elementTopology X F) X.J
  preservesFiniteLimits :=
    Functor.preservesFiniteLimits_sheafPushforwardContinuous
      (elementTopology X F) X.J (elementProjection X F) (Type u)

/-- **Stacks 04J4**, the geometric morphism of the relocalization. A morphism of sheaves
`s : G ⟶ F` postcomposes sections, giving a functor between the sites of elements which is
continuous and cocontinuous and whose restriction functor is left exact; those three facts are
exactly the data of a morphism of topoi `Sh(C/G) ⟶ Sh(C/F)`. -/
@[stacks 04J4 "the relocalization geometric morphism"]
noncomputable def relocalizationToposMorphism (s : G ⟶ F) :
    MorphismOfTopoi (localizedRingedTopos X G).Topos (localizedRingedTopos X F).Topos where
  inverseImage := (elementPostcomp s).sheafPushforwardContinuous
    (Type u) (elementTopology X G) (elementTopology X F)
  pushforward := (elementPostcomp s).sheafPushforwardCocontinuous
    (Type u) (elementTopology X G) (elementTopology X F)
  adj := (elementPostcomp s).sheafAdjunctionCocontinuous
    (Type u) (elementTopology X G) (elementTopology X F)
  preservesFiniteLimits := elementPostcomp_preservesFiniteLimits s

/-- **Stacks 04J4**, the inverse-image half of the relocalization triangle: localizing at `F`
and then relocalizing along `s : G ⟶ F` has the same inverse image as localizing at `G`
directly, on the nose. Postcomposition with `s` leaves the underlying object of the site
unchanged, so the two functors of sites to `C` are equal, and restriction along a composite is
the composite of the restrictions. -/
@[stacks 04J4 "the relocalization triangle of topoi, on inverse images"]
theorem comp_inverseImage (s : G ⟶ F) :
    ((localizationToposMorphism X F).comp (relocalizationToposMorphism s)).inverseImage =
      (localizationToposMorphism X G).inverseImage :=
  rfl

/-- The comparison of the direct images in the relocalization triangle, obtained from
`comp_inverseImage` by uniqueness of right adjoints. -/
noncomputable def canonicalRelocalizationComparison (s : G ⟶ F) :
    (localizationToposMorphism X G).pushforward ≅
      ((localizationToposMorphism X F).comp (relocalizationToposMorphism s)).pushforward :=
  Adjunction.rightAdjointUniq ((comp_inverseImage s).symm ▸ (localizationToposMorphism X G).adj)
    ((localizationToposMorphism X F).comp (relocalizationToposMorphism s)).adj

/-- Restriction of sheaves of commutative rings along postcomposition of sections: the
ring-level inverse image of the relocalization morphism. -/
noncomputable abbrev relocalizationRingInverseImage (s : G ⟶ F) :
    Sheaf (elementTopology X F) CommRingCat.{u} ⥤
      Sheaf (elementTopology X G) CommRingCat.{u} :=
  (elementPostcomp s).sheafPushforwardContinuous CommRingCat.{u}
    (elementTopology X G) (elementTopology X F)

/-- The cocontinuous partner of `relocalizationRingInverseImage`: the ring-level direct image
of the relocalization morphism. -/
noncomputable abbrev relocalizationRingPushforward (s : G ⟶ F) :
    Sheaf (elementTopology X G) CommRingCat.{u} ⥤
      Sheaf (elementTopology X F) CommRingCat.{u} :=
  (elementPostcomp s).sheafPushforwardCocontinuous CommRingCat.{u}
    (elementTopology X G) (elementTopology X F)

/-- The ring-level adjunction of the relocalization morphism. Because the geometric morphism is
restriction along a continuous and cocontinuous functor of sites, this is Mathlib's
`CategoryTheory.Functor.sheafAdjunctionCocontinuous` at the value category `CommRingCat`, and
needs no appeal to Stacks 00YV. -/
noncomputable def relocalizationRingAdjunction (s : G ⟶ F) :
    relocalizationRingInverseImage s ⊣ relocalizationRingPushforward s :=
  (elementPostcomp s).sheafAdjunctionCocontinuous CommRingCat.{u}
    (elementTopology X G) (elementTopology X F)

/-- **Stacks 04J4**, the identification of the localized structure sheaves: restricting the
structure sheaf of the localization at `F` along postcomposition with `s : G ⟶ F` gives the
structure sheaf of the localization at `G`. Both are the restriction of `O` along a projection
from a site of elements and the two projections agree, so the identification is the identity
isomorphism. -/
@[stacks 04J4 "identification of the localized structure sheaves"]
noncomputable def relocalizationRingIso (s : G ⟶ F) :
    (relocalizationRingInverseImage s).obj (localizedRingedTopos X F).O ≅
      (localizedRingedTopos X G).O :=
  Iso.refl _

/-- The structure map of the relocalization morphism of ringed topoi, in the direct-image form
`O_F ⟶ f_*O_G` that Stacks 01D3 takes as the data of a morphism of ringed topoi: the adjunct of
the canonical identification `relocalizationRingIso`. -/
noncomputable def relocalizationFSharp (s : G ⟶ F) :
    (localizedRingedTopos X F).O ⟶
      (relocalizationRingPushforward s).obj (localizedRingedTopos X G).O :=
  (relocalizationRingAdjunction s).homEquiv _ _ (relocalizationRingIso s).hom

/-- **Stacks 04J4**, the canonical structure-sheaf map: the structure map of the relocalization
morphism, read in its inverse-image form `f⁻¹O_F ⟶ O_G` through the ring-level adjunction, is
the canonical identification of the restriction of `O_F` with `O_G`. -/
@[stacks 04J4 "canonical structure-sheaf map"]
theorem relocalizationRingAdjunction_homEquiv_symm_fSharp (s : G ⟶ F) :
    ((relocalizationRingAdjunction s).homEquiv _ _).symm (relocalizationFSharp s) =
      (relocalizationRingIso s).hom :=
  Equiv.symm_apply_apply _ _

end Stacks.Sheaves.LocalizedRingedTopos

end
