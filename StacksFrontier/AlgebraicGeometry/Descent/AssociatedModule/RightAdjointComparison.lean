module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.PseudonaturalityClosure
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousCompCoherence

/-!
# The two right adjoints of restriction to an object of the big fppf site

Restriction `𝒢 ↦ 𝒢|_{(Sch/X)_fppf}` to the big fppf site of the scheme `X` of an object `T` of
the big fppf category over `S` is a left adjoint in two ways, both unconditionally:
`AlgebraicGeometry.BigFppfOver.objRestrictAdjunction`, whose right adjoint is the pushforward
along `SheafOfModules.pushforwardOver` of `T` preceded by the inverse of the reindexing
equivalence of Stacks 06WI, and
`AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction`, whose right adjoint is
`SheafOfModules.overPullback` along the structure morphism of `T`.  A mate is taken with respect
to a chosen adjunction, and the pentagon that
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso_comp_of_pentagon` reduces the
coherence of Stacks 03DV to mixes the two: the mates of the comparison of Stacks 03DV and of the
reindexing of Stacks 06WI are naturally taken with respect to the first, and the mate of
`AlgebraicGeometry.BigFppfOver.objRestrictComp` proved in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/PseudonaturalityClosure.lean` only exists
with respect to the second.

This file builds the comparison of those two right adjoints and the algebra that makes it usable.
Two right adjoints of one and the same functor are canonically isomorphic, by
`CategoryTheory.Adjunction.rightAdjointUniq`, which *is* the mate of the identity — so the
isomorphism that `Stacks.Mates.conjugateIsoEquiv_congr_source` and
`Stacks.Mates.conjugateIsoEquiv_congr_target` conjure out of a change of adjunction, and which
nothing computed, is that canonical comparison.  What the pentagon needs of it is not a formula
but a *coherence*: that the comparison attached to a composite of restrictions is built from the
comparisons attached to the factors.  That is
`Stacks.Mates.rightAdjointUniq_comp`, and with it the fourth entry of the pentagon is rewritten
with respect to the first family of adjunctions, which is what makes it composable with the other
three.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso`: **the comparison of the two right
  adjoints of restriction to an object of the big fppf site**, the canonical isomorphism between
  the reindexed pushforward along `SheafOfModules.pushforwardOver` of `T` and
  `SheafOfModules.overPullback` along the structure morphism of `T`.

## Main results

* `Stacks.Mates.conjugateIsoEquiv_refl`: **the mate of the identity of a functor that is a left
  adjoint in two ways is `CategoryTheory.Adjunction.rightAdjointUniq`.**  This is what discharges
  the opaque isomorphism in `Stacks.Mates.conjugateIsoEquiv_congr_source` and
  `Stacks.Mates.conjugateIsoEquiv_congr_target`.
* `Stacks.Mates.rightAdjointUniq_comp`: **the comparison of the two right adjoints of a composite
  is the composite of the two comparisons.**  This is the coherence a pentagon consumes, and
  Mathlib has it only one factor at a time.
* `Stacks.Mates.rightAdjointUniq_eq_of_counit` and
  `Stacks.Mates.rightAdjointUniq_eq_of_whiskerRight_counit`: **a comparison of two right adjoints
  compatible with the counits is the canonical one.**  Mathlib proves that the canonical
  comparison has this property but not that the property determines it; this is the converse, and
  it is the tool for identifying the canonical comparison with an explicit isomorphism.
* `Stacks.Mates.rightAdjointUniq_hom_app`: **the components of the comparison of two right
  adjoints**, the unit of one adjunction followed by the image of the counit of the other.
* `AlgebraicGeometry.BigFppfOver.conjugateIsoEquiv_refl_objRestrict`: **the comparison of the two
  right adjoints of restriction to an object is the mate of the identity of restriction.**
* `AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso_eq_rightAdjointUniq`: **the
  comparison with the transport between the two spellings of restriction stripped off**, so that
  both adjunctions involved are adjunctions of `SheafOfModules.overMap`.
* `AlgebraicGeometry.BigFppfOver.conjugateIsoEquiv_objRestrictComp_objRestrictAdjunction`: **the
  mate of the functoriality of restriction to an object with respect to
  `AlgebraicGeometry.BigFppfOver.objRestrictAdjunction`**, which is the fourth entry of the
  pentagon of
  `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso_comp_of_pentagon` in the
  spelling the other three entries use.

## Implementation notes

Nothing here carries a `stacks` attribute: the comparison this file is about is a step
Stacks 03DV leaves implicit and carries no tag of its own.

Nothing here unfolds `AlgebraicGeometry.BigFppfOver.objRestrict`, a reducible abbreviation whose
body is the structure sheaf of the big fppf site, and nothing here evaluates a functor between
categories of sheaves of modules at an object.  Both are elaboration constraints rather than
stylistic ones: the component formula
`Stacks.Mates.rightAdjointUniq_hom_app` and the counit characterisation
`Stacks.Mates.rightAdjointUniq_eq_of_counit` both exceed the heartbeat budget when specialised to
restriction to an object, because the unit and the counit of the two adjunctions at a concrete
module force the structure sheaf to be unfolded.  That is why
`AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso_eq_of_counit` is stated with a whiskered
equality of natural transformations and no object appears in it.

**What the comparison is, and what is not proved about it.**  The two right adjoints are the same
pushforward written twice.  The first is the pushforward along `CategoryTheory.Over.star` of `T`
inside the big fppf category over `S`, read on the big fppf site of the scheme of `T` through the
equivalence of Stacks 06WI; the second is the pushforward along `CategoryTheory.Over.pullback` of
the structure morphism of `T`.  Identifying them *as pushforwards* would mean producing the
isomorphism of functors of sites

    `Over.star T ⋙ (objEquiv B S hS T).inverse ≅ Over.pullback T.hom`

— the statement that the product with `T` in the big fppf category over `S` is the fibre product
over `S` — together with the compatibility of the two morphisms of structure sheaves that
`SheafOfModules.pushforwardCongr₂` requires, and only then assembling with
`SheafOfModules.pushforwardComp`.  That isomorphism of functors of sites does not exist in the
trees, and it is a construction on the big site rather than a computation; the comparison here is
instead pinned by its universal property, which is what the pentagon consumes.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₀ v₁ v₂ u₀ u₁ u₂ u

namespace Stacks.Mates

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]

/-- **The mate of the identity of a functor that is a left adjoint in two ways is the canonical
comparison of the two right adjoints.**  `CategoryTheory.Adjunction.rightAdjointUniq` *is*
`CategoryTheory.conjugateIsoEquiv` of `CategoryTheory.Iso.refl`, so this is a reading of a
definition rather than a computation; but it is the reading that matters, because it brings the
whole uniqueness-of-right-adjoints API of `Mathlib.CategoryTheory.Adjunction.Unique` to bear on
the isomorphism of right adjoints that `Stacks.Mates.conjugateIsoEquiv_congr_source` and
`Stacks.Mates.conjugateIsoEquiv_congr_target` produce out of thin air when a mate is transported
from one adjunction of `L` to another. -/
public theorem conjugateIsoEquiv_refl {L : C₀ ⥤ C₁} {R₁ R₂ : C₁ ⥤ C₀} (adj₁ : L ⊣ R₁)
    (adj₂ : L ⊣ R₂) :
    conjugateIsoEquiv adj₁ adj₂ (Iso.refl L) = Adjunction.rightAdjointUniq adj₁ adj₂ :=
  rfl

/-- **The comparison of the two right adjoints of a composite is the composite of the two
comparisons.**  Let `L₁` be a left adjoint in two ways, with right adjoints `R₁` and `R₁'`, and
likewise `L₂` with `R₂` and `R₂'`.  Then `L₁ ⋙ L₂` is a left adjoint in two ways, and the
canonical comparison `R₂ ⋙ R₁ ≅ R₂' ⋙ R₁'` of its two right adjoints is the comparison at `L₂`
whiskered by `R₁` followed by the comparison at `L₁` whiskered by `R₂'`.

This is the coherence that makes such a comparison usable in a pentagon: the comparison attached
to a composite is determined by the comparisons attached to the factors, so the transport of a
mate from one family of adjunctions to another is compatible with composition.  It is
`CategoryTheory.Adjunction.whiskerRight_rightAdjointUniq_hom` and
`CategoryTheory.Adjunction.whiskerLeft_rightAdjointUniq_hom` joined by
`CategoryTheory.Adjunction.rightAdjointUniq_trans`. -/
public theorem rightAdjointUniq_comp {L₁ : C₀ ⥤ C₁} {R₁ R₁' : C₁ ⥤ C₀} {L₂ : C₁ ⥤ C₂}
    {R₂ R₂' : C₂ ⥤ C₁} (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁ ⊣ R₁') (adj₂ : L₂ ⊣ R₂)
    (adj₂' : L₂ ⊣ R₂') :
    Adjunction.rightAdjointUniq (adj₁.comp adj₂) (adj₁'.comp adj₂') =
      Functor.isoWhiskerRight (Adjunction.rightAdjointUniq adj₂ adj₂') R₁ ≪≫
        Functor.isoWhiskerLeft R₂' (Adjunction.rightAdjointUniq adj₁ adj₁') := by
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  rw [Adjunction.whiskerRight_rightAdjointUniq_hom, Adjunction.whiskerLeft_rightAdjointUniq_hom,
    Adjunction.rightAdjointUniq_trans]

/-- **The comparison of two right adjoints read in the other direction.**  Conjugation is
contravariant, so the inverse of the comparison of `R₁` with `R₂` is the comparison of `R₂` with
`R₁`; the two are the same isomorphism, and this is the bookkeeping that lets a comparison
recorded on one orientation be used on the other. -/
public theorem rightAdjointUniq_symm {L : C₀ ⥤ C₁} {R₁ R₂ : C₁ ⥤ C₀} (adj₁ : L ⊣ R₁)
    (adj₂ : L ⊣ R₂) :
    (Adjunction.rightAdjointUniq adj₁ adj₂).symm = Adjunction.rightAdjointUniq adj₂ adj₁ :=
  rfl

/-- **The components of the comparison of two right adjoints.**  At `X` the comparison is the
unit of the second adjunction at `R₁.obj X` followed by `R₂` applied to the counit of the first
adjunction at `X`.  This is the only formula there is for such a comparison, and it is what a
computation of it in terms of explicitly given isomorphisms has to match. -/
public theorem rightAdjointUniq_hom_app {L : C₀ ⥤ C₁} {R₁ R₂ : C₁ ⥤ C₀} (adj₁ : L ⊣ R₁)
    (adj₂ : L ⊣ R₂) (X : C₁) :
    (Adjunction.rightAdjointUniq adj₁ adj₂).hom.app X =
      adj₂.unit.app (R₁.obj X) ≫ R₂.map (adj₁.counit.app X) := by
  rw [Adjunction.rightAdjointUniq_hom_eq_conjugateEquiv, conjugateEquiv_apply_app]
  rw [NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp]

/-- **A comparison of two right adjoints compatible with the counits is the canonical one.**  If
`φ : R₁ ≅ R₂` satisfies `L.map (φ.hom.app X) ≫ ε₂.app X = ε₁.app X` for every `X`, then `φ` is
`CategoryTheory.Adjunction.rightAdjointUniq`.  Mathlib records that the canonical comparison has
this property, in `CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit`, but not that the
property determines it; this is the converse, and it is the tool for identifying the canonical
comparison with an isomorphism built by hand. -/
public theorem rightAdjointUniq_eq_of_counit {L : C₀ ⥤ C₁} {R₁ R₂ : C₁ ⥤ C₀} (adj₁ : L ⊣ R₁)
    (adj₂ : L ⊣ R₂) (φ : R₁ ≅ R₂)
    (h : ∀ X, L.map (φ.hom.app X) ≫ adj₂.counit.app X = adj₁.counit.app X) :
    φ = Adjunction.rightAdjointUniq adj₁ adj₂ := by
  refine Iso.ext ?_
  ext X
  refine (adj₂.homEquiv (R₁.obj X) X).symm.injective ?_
  rw [Adjunction.homEquiv_counit, h X,
    Adjunction.homEquiv_symm_rightAdjointUniq_hom_app adj₁ adj₂ X]

/-- **A comparison of two right adjoints compatible with the counits is the canonical one**, in
the form that mentions no object of the categories.  This is
`Stacks.Mates.rightAdjointUniq_eq_of_counit` with the hypothesis read as an equality of natural
transformations `R₁ ⋙ L ⟶ 𝟭`, which is the form in which it can be applied where the categories
are categories of sheaves of modules on a concrete site and evaluating a functor at an object is
not affordable. -/
public theorem rightAdjointUniq_eq_of_whiskerRight_counit {L : C₀ ⥤ C₁} {R₁ R₂ : C₁ ⥤ C₀}
    (adj₁ : L ⊣ R₁) (adj₂ : L ⊣ R₂) (φ : R₁ ≅ R₂)
    (h : Functor.whiskerRight φ.hom L ≫ adj₂.counit = adj₁.counit) :
    φ = Adjunction.rightAdjointUniq adj₁ adj₂ :=
  rightAdjointUniq_eq_of_counit adj₁ adj₂ φ fun X => by
    simpa using NatTrans.congr_app h X

/-- **Conjugating the identity by a transport along an equality of functors gives the identity.**
For `h : F = G` the composite of `CategoryTheory.eqToIso h`, the identity of `G` and
`CategoryTheory.eqToIso h.symm` is the identity of `F`.  This is the shape of isomorphism that
`Stacks.Mates.conjugateIsoEquiv_of_heq_adjunction` takes as its argument, so this is what feeds
that lemma when the isomorphism being transported is the identity. -/
public theorem eqToIso_conj_refl {F G : C₀ ⥤ C₁} (h : F = G) :
    eqToIso h ≪≫ Iso.refl G ≪≫ eqToIso h.symm = Iso.refl F := by
  subst h
  simp

end Stacks.Mates

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparison of the two right adjoints of restriction to an object of the big fppf
site.**  Restriction `𝒢 ↦ 𝒢|_{(Sch/X)_fppf}` to the big fppf site of the scheme `X` of `T` is a
left adjoint in two ways — by
`AlgebraicGeometry.BigFppfOver.objRestrictAdjunction`, whose right adjoint is the pushforward
along `SheafOfModules.pushforwardOver` of `T` preceded by the inverse of the reindexing
equivalence of Stacks 06WI, and by
`AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction`, whose right adjoint is
`SheafOfModules.overPullback` along the structure morphism of `T`.  Two right adjoints of one and
the same functor are canonically isomorphic, and this is that isomorphism.

Geometrically the two right adjoints are the same pushforward written twice: the first is the
pushforward along taking the product with `T` inside the big fppf category over `S`, read on the
big fppf site of `X` through Stacks 06WI, and the second is the pushforward along the fibre
product over `S` with `X`.  This isomorphism is what identifies them, and it is forced: it is
determined by the counits, by
`AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso_eq_of_counit`. -/
public noncomputable def objRestrictRightAdjointIso (T : BigFppfOver B S hS) :
    (Stacks.SheafOfModules.reindexEquivalence
          (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
          (objEquiv B S hS T) ((structureSheaf B S hS).over T)).inverse ⋙
        SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver T) ≅
      SheafOfModules.overPullback.{u} B.structureSheaf T.hom :=
  Adjunction.rightAdjointUniq (objRestrictAdjunction B S hS T)
    (objRestrictOverPullbackAdjunction B S hS T)

/-- **The comparison of the two right adjoints of restriction to an object is the mate of the
identity.**  `Stacks.Mates.conjugateIsoEquiv_congr_source` and
`Stacks.Mates.conjugateIsoEquiv_congr_target` transport a mate from one adjunction of
`AlgebraicGeometry.BigFppfOver.objRestrict` to the other by composing with the mate of the
identity of `objRestrict`, and name no isomorphism for it; this says that isomorphism is
`AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso`, which is where the uniqueness API of
right adjoints applies. -/
public theorem conjugateIsoEquiv_refl_objRestrict (T : BigFppfOver B S hS) :
    conjugateIsoEquiv (objRestrictAdjunction B S hS T)
        (objRestrictOverPullbackAdjunction B S hS T)
        (Iso.refl (objRestrict B S hS T)) =
      objRestrictRightAdjointIso B S hS T :=
  Stacks.Mates.conjugateIsoEquiv_refl _ _

/-- **The comparison of the two right adjoints of restriction to an object is determined by the
counits.**  An isomorphism between the right adjoint of
`AlgebraicGeometry.BigFppfOver.objRestrictAdjunction` and
`SheafOfModules.overPullback` along the structure morphism of `T` that is compatible with the two
counits *is* `AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso`.

This is the statement to use to identify the comparison with an explicitly constructed
isomorphism: the only thing to check about a candidate is one equality of natural transformations
of functors, with no object of either category of sheaves of modules appearing. -/
public theorem objRestrictRightAdjointIso_eq_of_counit (T : BigFppfOver B S hS)
    (φ : (Stacks.SheafOfModules.reindexEquivalence
            (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
            (objEquiv B S hS T) ((structureSheaf B S hS).over T)).inverse ⋙
          SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver T) ≅
        SheafOfModules.overPullback.{u} B.structureSheaf T.hom)
    (h : Functor.whiskerRight φ.hom (objRestrict B S hS T) ≫
        (objRestrictOverPullbackAdjunction B S hS T).counit =
      (objRestrictAdjunction B S hS T).counit) :
    φ = objRestrictRightAdjointIso B S hS T :=
  Stacks.Mates.rightAdjointUniq_eq_of_whiskerRight_counit _ _ φ h

/-- **The comparison of the two right adjoints, with the transport between the two spellings of
restriction stripped off.**  `AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction` is
built by rewriting along `AlgebraicGeometry.BigFppfOver.objRestrict_eq_overMap`, so its value is
a `cast`, and so therefore is the comparison.  Given the adjunction obtained by transporting
`AlgebraicGeometry.BigFppfOver.objRestrictAdjunction` along the same equality — which is what the
`HEq` hypothesis says — the comparison is the canonical comparison of right adjoints of
`SheafOfModules.overMap`, one of them `SheafOfModules.overMapPushforwardAdj` itself.

This is the form in which the comparison can be computed: both adjunctions are then adjunctions
of one of Mathlib's own functors, and neither involves the transport.  The two casts are stripped
simultaneously by `Stacks.Mates.conjugateIsoEquiv_of_heq_adjunction`. -/
public theorem objRestrictRightAdjointIso_eq_rightAdjointUniq (T : BigFppfOver B S hS)
    {adj : SheafOfModules.overMap.{u} B.structureSheaf T.hom ⊣
      (Stacks.SheafOfModules.reindexEquivalence
          (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
          (objEquiv B S hS T) ((structureSheaf B S hS).over T)).inverse ⋙
        SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver T)}
    (e : HEq (objRestrictAdjunction B S hS T) adj) :
    objRestrictRightAdjointIso B S hS T =
      Adjunction.rightAdjointUniq adj
        (SheafOfModules.overMapPushforwardAdj.{u} B.structureSheaf T.hom) := by
  refine Eq.trans ?_ (Stacks.Mates.conjugateIsoEquiv_of_heq_adjunction
    (objRestrict_eq_overMap B S hS T) (objRestrict_eq_overMap B S hS T)
    (objRestrictAdjunction B S hS T) adj (objRestrictOverPullbackAdjunction B S hS T)
    (SheafOfModules.overMapPushforwardAdj.{u} B.structureSheaf T.hom) e
    (objRestrictOverPullbackAdjunction_heq B S hS T)
    (Iso.refl (SheafOfModules.overMap.{u} B.structureSheaf T.hom)))
  exact Eq.trans (conjugateIsoEquiv_refl_objRestrict B S hS T).symm
    (congrArg (fun α => conjugateIsoEquiv (objRestrictAdjunction B S hS T)
        (objRestrictOverPullbackAdjunction B S hS T) α)
      (Stacks.Mates.eqToIso_conj_refl (objRestrict_eq_overMap B S hS T)).symm)

/-- **The comparison of the two right adjoints of an iterated restriction is the composite of
the two comparisons.**  For `g : T' ⟶ T` the functor
`objRestrict T ⋙ objRestrict (Over.mk g.left)` is a left adjoint in two ways, once for each
family of adjunctions, and the comparison of its two right adjoints is built from the comparisons
at `T` and at `Over.mk g.left` by whiskering.

This is `Stacks.Mates.rightAdjointUniq_comp` at restriction to an object, and it is the coherence
that the pentagon of
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso_comp_of_pentagon` needs: the
comparison is multiplicative, so transporting the mate of a composite is transporting the mates
of the factors. -/
public theorem rightAdjointUniq_objRestrictComp {T T' : BigFppfOver B S hS} (g : T' ⟶ T) :
    Adjunction.rightAdjointUniq
        ((objRestrictOverPullbackAdjunction B S hS T).comp
          (objRestrictOverPullbackAdjunction B (objScheme B S hS T)
            (contains_objScheme B S hS T) (Over.mk g.left)))
        ((objRestrictAdjunction B S hS T).comp
          (objRestrictAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T)
            (Over.mk g.left))) =
      Functor.isoWhiskerRight (objRestrictRightAdjointIso B (objScheme B S hS T)
            (contains_objScheme B S hS T) (Over.mk g.left)).symm
          (SheafOfModules.overPullback.{u} B.structureSheaf T.hom) ≪≫
        Functor.isoWhiskerLeft _ (objRestrictRightAdjointIso B S hS T).symm :=
  Stacks.Mates.rightAdjointUniq_comp _ _ _ _

/-- **The mate of the functoriality of restriction to an object, with respect to
`AlgebraicGeometry.BigFppfOver.objRestrictAdjunction`.**  The mate with respect to the other
family of adjunctions is computed by
`AlgebraicGeometry.BigFppfOver.conjugateIsoEquiv_objRestrictComp`, with respect to
`AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction`, where restriction to an object
is the left adjoint of `SheafOfModules.overPullback`; this is the same mate with respect to the
other family of adjunctions, the one with respect to which the comparison of Stacks 03DV and the
reindexing of Stacks 06WI have their mates.  The two differ by the comparison
`AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso` of the two right adjoints, at `T'` on
one side and at `T` and `Over.mk g.left` on the other.

This is the identity that makes the fourth entry of the pentagon of
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso_comp_of_pentagon` composable
with the other three: all four are now mates with respect to one and the same family of
adjunctions of restriction to an object. -/
public theorem conjugateIsoEquiv_objRestrictComp_objRestrictAdjunction
    {T T' : BigFppfOver B S hS} (g : T' ⟶ T) :
    conjugateIsoEquiv (objRestrictAdjunction B S hS T')
        ((objRestrictAdjunction B S hS T).comp
          (objRestrictAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T)
            (Over.mk g.left)))
        (objRestrictComp B S hS g) =
      objRestrictRightAdjointIso B S hS T' ≪≫
        (Stacks.SheafOfModules.overPullbackCongr B.structureSheaf (Over.w g).symm ≪≫
            Stacks.SheafOfModules.overPullbackComp B.structureSheaf T.hom g.left) ≪≫
          (Functor.isoWhiskerRight (objRestrictRightAdjointIso B (objScheme B S hS T)
                (contains_objScheme B S hS T) (Over.mk g.left)).symm
              (SheafOfModules.overPullback.{u} B.structureSheaf T.hom) ≪≫
            Functor.isoWhiskerLeft _ (objRestrictRightAdjointIso B S hS T).symm) := by
  refine Eq.trans (Stacks.Mates.conjugateIsoEquiv_congr_target
    (objRestrictOverPullbackAdjunction B S hS T') (objRestrictAdjunction B S hS T') _
    (objRestrictComp B S hS g)) ?_
  refine Eq.trans (congrArg
    (fun x => conjugateIsoEquiv (objRestrictAdjunction B S hS T')
        (objRestrictOverPullbackAdjunction B S hS T')
        (Iso.refl (objRestrict B S hS T')) ≪≫ x)
    (Stacks.Mates.conjugateIsoEquiv_congr_source
      (objRestrictOverPullbackAdjunction B S hS T')
      ((objRestrictOverPullbackAdjunction B S hS T).comp
        (objRestrictOverPullbackAdjunction B (objScheme B S hS T)
          (contains_objScheme B S hS T) (Over.mk g.left))) _
      (objRestrictComp B S hS g))) ?_
  exact congrArg₂ (fun a b => a ≪≫ b) (conjugateIsoEquiv_refl_objRestrict B S hS T')
    (congrArg₂ (fun a b => a ≪≫ b) (conjugateIsoEquiv_objRestrictComp B S hS g)
      (Eq.trans (Stacks.Mates.conjugateIsoEquiv_refl _ _)
        (rightAdjointUniq_objRestrictComp B S hS g)))

end AlgebraicGeometry.BigFppfOver

end
