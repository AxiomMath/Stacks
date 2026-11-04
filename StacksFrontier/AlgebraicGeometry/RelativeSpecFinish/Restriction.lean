module

public import StacksFrontier.AlgebraicGeometry.AffineQcohEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.RestrictionExact.MateFree

/-!
# Restriction to an open subscheme of the quasi-inverse of Stacks Tag 01SB

Let `f : X ⟶ S` be a morphism of schemes, `A = f_* 𝒪_X` the direct image of the structure
sheaf, and `V` an open of `S` with preimage `U = f ⁻¹ᵁ V`.  The three hypotheses of
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isEquivalence_affineQuasicoherentPushforward`
are local on `S`, so each of them needs a comparison of the quasi-inverse
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackModules` with restriction to `V`.

This file carries out the *reformulation* of that comparison which the docstring of
`StacksFrontier/AlgebraicGeometry/RestrictionExact/MateFree.lean` recommends: `V` and `U` are
taken as open subschemes rather than as slice sites, so that every functor involved is an
`Opens.map` or a `Topology.IsOpenEmbedding.functor`, and no `CategoryTheory.Over.star` or
`CategoryTheory.Over.post` appears.  The two obstructions recorded there do not
arise:

* the continuity of the site functor of a restriction is
  `Topology.IsOpenEmbedding.functor_isContinuous`, which pinned Mathlib has as a lemma (it is
  made a local instance below); no `CategoryTheory.CoverPreserving.overPost` and no
  `Functor.PreservesOneHypercovers` is involved;
* the two composite site functors are `TopologicalSpace.Opens.map` of the two *equal*
  composites `U ⟶ X ⟶ S` and `U ⟶ V ⟶ S`, so they are equal by `congrArg` rather than only
  isomorphic, and the identification carries no `CategoryTheory.Limits.prod` bookkeeping.

## Main results

* `restrictOpensFunctor_comp_eq`: the two composite site functors `Opens ↥V ⥤ Opens ↥X`,
  namely `V.ι ''ᵁ · ` followed by `f ⁻¹ᵁ ·` and `(f ∣_ V) ⁻¹ᵁ ·` followed by `U.ι ''ᵁ ·`, are
  **equal**.
* `restrictPushforwardRing_eq`: `A|_V = (f|_U)_* 𝒪_U` as sheaves of rings on `V`, where the
  left side is the restriction of `A` to the open subscheme `V` and the right side is
  `Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardRing` of the restricted morphism.
  This is an **equality**, so `SheafOfModules (A|_V)` and the category of modules over
  `(f|_U)_* 𝒪_U` are literally the same category.
* `isRightAdjoint_pushforwardModules_resLE`: the direct image over `(f|_U)_* 𝒪_U` has a left
  adjoint, which is the restricted quasi-inverse; it is
  `Stacks.AlgebraicGeometry.AffineQcohEquivalence.isRightAdjoint_pushforwardModules` at the
  restricted morphism, so no new work is needed for it.
* `restrictOverAdjunction`: restriction of `A`-modules to `V` is left adjoint to a direct
  image, for an arbitrary sheaf of rings `A` on `S`.  Mathlib's
  `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` is the same statement for the structure
  sheaf only, and its proof goes through `AlgebraicGeometry.Scheme.Hom.appIso`, which has no
  analogue for a general sheaf of rings.

## Route

`restrictOpensFunctor_comp_eq` is `CategoryTheory.Functor.ext`: the opens of a space form a
thin category, so only the action on objects has content, and that is
`AlgebraicGeometry.Scheme.Hom.resLE_preimage` together with
`AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf` and the containment
`U.ι ''ᵁ W ≤ U`.  `restrictPushforwardRing_eq` is then `congrArg` on the underlying presheaf,
using that a sheaf is a `CategoryTheory.ObjectProperty.FullSubcategory` object, whose second
field is a proposition (`fullSubcategory_eq_of_obj_eq`).  Both sides unfold to a precomposition
of `X.ringCatSheaf.obj` with the opposite of one of the two composite functors; that unfolding
holds by `rfl`, including `(↥U).ringCatSheaf = 𝒪_X|_U`.

`restrictOverAdjunction` is `SheafOfModules.pushforwardPushforwardAdj` for
`TopologicalSpace.IsOpenMap.adjunction`; because the morphism of sheaves of rings on the
restricted side is the identity, its two hypotheses reduce to the statement that two parallel
morphisms of opens agree, which is `Subsingleton.elim`.

## Transparency gotchas

`Topology.IsOpenEmbedding.functor_isContinuous` is a lemma, not an instance, and is needed
already to *state* the restriction of a sheaf; it is therefore a `local instance` for the whole
file.  The equality `restrictPushforwardRing_eq` is proved with `congrArg` at
`X.ringCatSheaf.obj`, not at `X.presheaf`: the latter is `CommRingCat`-valued and the resulting
term is rejected.

## What is not done

**This file does not prove the equivalence assertion of [Stacks, Tag 01SB]**, and no `stacks`
attribute is attached.  What it supplies is the substrate of the restriction
comparison, in the shape the reformulation calls for.  Still missing, in order:

* a transport across `restrictPushforwardRing_eq`.  This is the one new friction the
  reformulation introduces: `restrictOver V A` lands in
  `SheafOfModules (restrictRing V A)`, while
  `Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackModules` at the restricted morphism
  starts from `SheafOfModules ((f|_U)_* 𝒪_U)`.  The two sheaves of rings are equal, so the two
  categories are the same *type*, but the equality is not definitional (the open-set identity
  behind it needs `inf_eq_right`), so the two functors do not compose as written.  The cheapest
  repair is to feed `eqToHom (restrictPushforwardRing_eq f V)` to
  `SheafOfModules.pushforward` in place of the identity that `restrictOver` uses, and to
  re-prove the two hypotheses of `restrictOverAdjunction` with that morphism;
* the isomorphism `R₁ ⋙ R₂ ≅ R₃ ⋙ R₄` of the two composite direct images
  `SheafOfModules 𝒪_U ⥤ SheafOfModules A`, which by `SheafOfModules.pushforwardComp` (an
  `Iso.refl`) is a single application of `SheafOfModules.pushforwardCongr₂` to the natural
  isomorphism of the two equal composite `Opens.map` functors — equal because
  `Opens.map (a ≫ b) = Opens.map b ⋙ Opens.map a` holds by `rfl` and
  `U.ι ≫ f = (f|_U) ≫ V.ι` is `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι` — with the
  compatibility of the two composite morphisms of sheaves of rings as its side goal;
* the comparison itself, which is then
  `Stacks.CategoryTheory.leftAdjointsCommOfRightAdjointsComm` applied to the four adjunctions
  `restrictOverAdjunction`, `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`, and the two
  `Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackPushforwardAdjunction`s;
* the three hypotheses `hL`, `hunit`, `hcounit` of
  `isEquivalence_affineQuasicoherentPushforward`, which are separate work on top of the
  comparison: each is local on `S`, and over an affine open `V` with affine `U` one feeds
  `Stacks.AlgebraicGeometry.QcohLimits.presentationOverAffine` into
  `isQuasicoherent_pullbackModules_of_presentation`.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

noncomputable section

namespace Stacks

/-! ### A generality about full subcategories -/

namespace CategoryTheory

/-- Two objects of a full subcategory with the same underlying object are equal: the second
field of `CategoryTheory.ObjectProperty.FullSubcategory` is a proposition.  This is what turns
an equality of underlying presheaves into an equality of sheaves. -/
public theorem fullSubcategory_eq_of_obj_eq {C : Type*} [Category C]
    {P : ObjectProperty C} {A B : P.FullSubcategory} (h : A.obj = B.obj) : A = B := by
  obtain ⟨a, ha⟩ := A
  obtain ⟨b, hb⟩ := B
  subst h
  rfl

end CategoryTheory

namespace AlgebraicGeometry.AffineQcohRestriction

open Stacks.AlgebraicGeometry.AffineQcohPushforward

attribute [local instance] Topology.IsOpenEmbedding.functor_isContinuous

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)

/-! ### The restriction functor on sheaves over an open subscheme -/

/-- The site functor of restriction to an open subscheme: an open of `V` is sent to the
corresponding open of `S`. -/
public abbrev opensImageFunctor : Opens (V : S.Opens) ⥤ Opens S :=
  Topology.IsOpenEmbedding.functor V.ι.isOpenEmbedding

/-- The restriction to an open subscheme `V` of a sheaf of rings on `S`. -/
public abbrev restrictRing (A : Sheaf (Opens.grothendieckTopology S) RingCat.{u}) :
    Sheaf (Opens.grothendieckTopology (V : S.Opens)) RingCat.{u} :=
  ((opensImageFunctor V).sheafPushforwardContinuous RingCat.{u} _ _).obj A

/-- Restriction of sheaves of modules to an open subscheme `V`, over an arbitrary sheaf of
rings `A` on `S`.  For `A = 𝒪_S` this is `AlgebraicGeometry.Scheme.Modules.restrictFunctor`. -/
public def restrictOver (A : Sheaf (Opens.grothendieckTopology S) RingCat.{u}) :
    SheafOfModules.{u} A ⥤ SheafOfModules.{u} (restrictRing V A) :=
  SheafOfModules.pushforward.{u} (𝟙 (restrictRing V A))

/-- The morphism of sheaves of rings from `A` to the direct image of its restriction to `V`:
over an open `W` of `S` it is the restriction map `A(W) ⟶ A(W ⊓ V)`. -/
public def toPushforwardRestrictRing (A : Sheaf (Opens.grothendieckTopology S) RingCat.{u}) :
    A ⟶ ((Opens.map V.ι.base).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology S) (Opens.grothendieckTopology (V : S.Opens))).obj
      (restrictRing V A) :=
  ⟨{ app W := A.obj.map (V.ι.isOpenEmbedding.isOpenMap.adjunction.counit.app W.unop).op
     naturality U W i := by
       change A.obj.map i ≫ A.obj.map _ = A.obj.map _ ≫ A.obj.map _
       rw [← A.obj.map_comp, ← A.obj.map_comp]
       exact congrArg A.obj.map (Subsingleton.elim _ _) }⟩

/-- **Restriction to an open subscheme is left adjoint to a direct image**, over an arbitrary
sheaf of rings on `S`. -/
public def restrictOverAdjunction (A : Sheaf (Opens.grothendieckTopology S) RingCat.{u}) :
    restrictOver V A ⊣ SheafOfModules.pushforward.{u} (toPushforwardRestrictRing V A) := by
  refine SheafOfModules.pushforwardPushforwardAdj
    (by exact V.ι.isOpenEmbedding.isOpenMap.adjunction) (𝟙 (restrictRing V A)) _ ?_ ?_
  · refine CategoryTheory.NatTrans.ext (funext fun W => ?_)
    exact (Category.comp_id _).symm
  · refine CategoryTheory.NatTrans.ext (funext fun W => ?_)
    refine Eq.trans ?_ ((restrictRing V A).obj.map_id W)
    change (𝟙 _) ≫ A.obj.map _ ≫ A.obj.map _ = _
    rw [Category.id_comp, ← A.obj.map_comp]
    exact congrArg A.obj.map (Subsingleton.elim _ _)

/-! ### The two composite site functors agree -/

/-- The restricted morphism `f|_U : U ⟶ V` for `U = f ⁻¹ᵁ V`. -/
public abbrev resPreimage : (f ⁻¹ᵁ V).toScheme ⟶ (V : S.Opens).toScheme :=
  f.resLE V (f ⁻¹ᵁ V) le_rfl

/-- The two routes from an open of `V` to an open of `X` agree: taking the image in `S` and
then the preimage under `f` is taking the preimage under `f|_U` and then the image in `X`. -/
public theorem preimage_image_eq_image_resLE_preimage (W : Opens (V : S.Opens)) :
    f ⁻¹ᵁ (V.ι ''ᵁ W) = (f ⁻¹ᵁ V).ι ''ᵁ ((resPreimage f V) ⁻¹ᵁ W) := by
  rw [Scheme.Hom.resLE_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]
  exact (inf_eq_right.mpr ((Opens.map f.base).monotone (V.ι_image_le W))).symm

/-- **The two composite site functors `Opens ↥V ⥤ Opens ↥X` are equal.**  The opens of a space
form a thin category, so only the action on objects has content. -/
public theorem restrictOpensFunctor_comp_eq :
    opensImageFunctor V ⋙ Opens.map f.base =
      Opens.map (resPreimage f V).base ⋙ opensImageFunctor (f ⁻¹ᵁ V) :=
  CategoryTheory.Functor.ext (preimage_image_eq_image_resLE_preimage f V)
    fun _ _ _ => Subsingleton.elim _ _

/-- **`A|_V = (f|_U)_* 𝒪_U`.**  The restriction to `V` of the direct image of the structure
sheaf of `X` is the direct image of the structure sheaf of `U = f ⁻¹ᵁ V` along the restricted
morphism.  This is an equality of sheaves of rings on `V`, so the two categories of modules
over them are the same category. -/
public theorem restrictPushforwardRing_eq :
    restrictRing V (pushforwardRing f.base X.ringCatSheaf) =
      pushforwardRing (resPreimage f V).base (f ⁻¹ᵁ V).toScheme.ringCatSheaf :=
  Stacks.CategoryTheory.fullSubcategory_eq_of_obj_eq
    (congrArg (fun G : Opens (V : S.Opens) ⥤ Opens X => G.op ⋙ X.ringCatSheaf.obj)
      (restrictOpensFunctor_comp_eq f V))

/-! ### The restricted quasi-inverse exists -/

/-- The direct image over `(f|_U)_* 𝒪_U` has a left adjoint, namely the quasi-inverse of
Stacks Tag 01SB for the restricted morphism.  This is the existing instance at `f|_U`; the
reformulation needs nothing new for it. -/
public instance isRightAdjoint_pushforwardModules_resLE :
    (pushforwardModules.{u} (resPreimage f V).base
      (f ⁻¹ᵁ V).toScheme.ringCatSheaf).IsRightAdjoint :=
  AffineQcohEquivalence.isRightAdjoint_pushforwardModules (resPreimage f V)

end AlgebraicGeometry.AffineQcohRestriction

end Stacks

end

end
