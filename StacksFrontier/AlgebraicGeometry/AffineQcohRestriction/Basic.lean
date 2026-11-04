module

public import StacksFrontier.AlgebraicGeometry.RelativeSpecFinish.Restriction
public import StacksFrontier.AlgebraicGeometry.RestrictionExact.MateFree

/-!
# The restriction comparison for the left adjoint of a direct image

Let `f : X ⟶ S` be a morphism of schemes, `A = f_* 𝒪_X`, and `V` an open of `S` with preimage
`U = f ⁻¹ᵁ V`.  `Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackModules` is the left
adjoint of the direct image of `𝒪_X`-modules regarded as a functor to `A`-modules; this file
proves that it commutes with restriction to `V`.

The square of *left* adjoints is obtained from the square of *right* adjoints by
`Stacks.CategoryTheory.leftAdjointsCommOfRightAdjointsComm`, so no Beck--Chevalley condition is
involved.  The square of right adjoints is a square of `SheafOfModules.pushforward`s along the
two equal composite site functors `Opens S ⥤ Opens ↥U`, and is therefore a single
`SheafOfModules.pushforwardCongr₂` between two `SheafOfModules.pushforwardComp`s (both of which
are `Iso.refl`).

## Main definitions and results

* `Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictCompareRing`: the morphism of sheaves
  of rings `(f|_U)_* 𝒪_U ⟶ (V.ι ''ᵁ ·)_* A` whose `SheafOfModules.pushforward` is restriction to
  `V` of `A`-modules, retyped as a functor to modules over `(f|_U)_* 𝒪_U`.  Over an open `W` of
  `V` it is the identification `𝒪_X(U.ι ''ᵁ (f|_U) ⁻¹ᵁ W) = 𝒪_X(f ⁻¹ᵁ (V.ι ''ᵁ W))`.  The
  identity would not typecheck here: the two sheaves of rings on `V` are equal by
  `Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictPushforwardRing_eq`, but that equality
  is not definitional.
* `Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictCompareRing_eq_eqToHom`: that morphism
  **is** `CategoryTheory.eqToHom` of that equality, so the retyped restriction functor is
  literally the transport of
  `Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictOver` across it.
* `Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictCompareAdjunction`: the retyped
  restriction functor has the expected right adjoint, a direct image; this is
  `SheafOfModules.pushforwardPushforwardAdj`, re-proved for the retyped morphism.
* `Stacks.AlgebraicGeometry.AffineQcohRestriction.opensMapComp_eq`: the two composite site
  functors `Opens S ⥤ Opens ↥U` are **equal**, because
  `(f|_U) ≫ V.ι = U.ι ≫ f` and `TopologicalSpace.Opens.map` of a composite is the composite of
  the `TopologicalSpace.Opens.map`s, on the nose.
* `Stacks.AlgebraicGeometry.AffineQcohRestriction.rightSquare`: **the square of right adjoints
  commutes**, i.e. direct image along `f|_U` followed by direct image along `V.ι` agrees with
  direct image along `U.ι` followed by direct image along `f`.
* `Stacks.AlgebraicGeometry.AffineQcohRestriction.leftSquare`: **the comparison square for the
  left adjoints**, i.e. restriction to `V` followed by the quasi-inverse at `f|_U` agrees with
  the quasi-inverse at `f` followed by restriction to `U`.

## Route

Every morphism of sheaves of rings appearing here has all of its components of the form
`X.ringCatSheaf.obj.map g` for `g` a morphism of the thin category `(Opens ↥X)ᵒᵖ`, so all the
coherence conditions (two naturality squares, the two hypotheses of
`SheafOfModules.pushforwardPushforwardAdj`, and the compatibility required by
`SheafOfModules.pushforwardCongr₂`) are instances of the three `Subsingleton.elim` lemmas in the
`Stacks.CategoryTheory` section below.

## Implementation notes

One transparency gotcha shapes the whole file. Inside a tactic proof,
`rw [← X.ringCatSheaf.obj.map_comp]` is rejected with *the target expression is not type-correct
under the `implicit` transparency level*: the structure sheaf is reached as a
`TopCat.Sheaf RingCat` while the rewrite motive wants the
`CategoryTheory.ObjectProperty.FullSubcategory` spelling of the sheaf condition, and the two
agree only after unfolding. Every rewrite is therefore performed once, in a standalone lemma
about an abstract functor `P` out of a thin category — the four `Stacks.CategoryTheory.map_*`
lemmas below — and the concrete goals are closed by `exact`, where the identification is
checked at the transparency of term elaboration.

`Topology.IsOpenEmbedding.functor_isContinuous` is a lemma rather than an instance, so it is
introduced as a section-confined local instance, as in
`StacksFrontier/AlgebraicGeometry/RelativeSpecFinish/Restriction.lean`.

`restrictRing (f ⁻¹ᵁ V) X.ringCatSheaf = (f ⁻¹ᵁ V).toScheme.ringCatSheaf` holds by `rfl`, which
is why `restrictOverAdjunction (f ⁻¹ᵁ V) X.ringCatSheaf` can be used directly as the third
adjunction and only one transport is needed, on the other side of the square.

## What is not done

**This file does not prove the equivalence assertion of [Stacks, Tag 01SB]**;
no `stacks` attribute is attached.  What it supplies is the restriction comparison for the
quasi-inverse, which the three hypotheses `hL`, `hunit`, `hcounit` of
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isEquivalence_affineQuasicoherentPushforward`
need.  Deducing those three from `leftSquare` — by covering `S` with affine opens having affine
preimage and feeding `Stacks.AlgebraicGeometry.QcohLimits.presentationOverAffine` into
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_pullbackModules_of_presentation`
— is separate work, not carried out here.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks

/-! ### Composites of a functor out of a thin category -/

namespace CategoryTheory

/-- In a thin source category, any two composites of a functor's images between the same two
objects agree. -/
public theorem map_comp_eq_map_comp {C : Type*} {D : Type*} [Category C] [Category D]
    [Quiver.IsThin C] (P : C ⥤ D) {a b c d : C} (g₁ : a ⟶ b) (g₂ : b ⟶ d) (g₃ : a ⟶ c)
    (g₄ : c ⟶ d) : P.map g₁ ≫ P.map g₂ = P.map g₃ ≫ P.map g₄ := by
  rw [← P.map_comp, ← P.map_comp]
  exact congrArg P.map (Subsingleton.elim _ _)

/-- In a thin source category, a functor's image of a morphism is the composite of its images of
any factorisation of that morphism. -/
public theorem map_eq_map_comp {C : Type*} {D : Type*} [Category C] [Category D]
    [Quiver.IsThin C] (P : C ⥤ D) {a c d : C} (g₁ : a ⟶ d) (g₃ : a ⟶ c) (g₄ : c ⟶ d) :
    P.map g₁ = P.map g₃ ≫ P.map g₄ := by
  simpa using map_comp_eq_map_comp P g₁ (𝟙 d) g₃ g₄

/-- A variant of `Stacks.CategoryTheory.map_comp_eq_map_comp` with identity morphisms inserted,
in the shape in which a square of pushforwards along a thin site presents itself. -/
public theorem map_comp_id_comp_eq {C : Type*} {D : Type*} [Category C] [Category D]
    [Quiver.IsThin C] (P : C ⥤ D) {a b c : C} (g₁ : a ⟶ b) (g₂ : b ⟶ c) (g₃ : a ⟶ c) :
    (P.map g₁ ≫ 𝟙 (P.obj b)) ≫ P.map g₂ = 𝟙 (P.obj a) ≫ P.map g₃ := by
  rw [Category.comp_id, Category.id_comp]
  exact (map_eq_map_comp P g₃ g₁ g₂).symm

/-- In a thin source category, a functor's images of a triple of morphisms returning to the
starting object compose to the identity. -/
public theorem map_comp_comp_eq_id {C : Type*} {D : Type*} [Category C] [Category D]
    [Quiver.IsThin C] (P : C ⥤ D) {a b c : C} (g₁ : a ⟶ b) (g₂ : b ⟶ c) (g₃ : c ⟶ a) :
    P.map g₁ ≫ P.map g₂ ≫ P.map g₃ = 𝟙 (P.obj a) := by
  simpa using (map_eq_map_comp P (𝟙 a) g₁ (g₂ ≫ g₃)).symm

/-- `CategoryTheory.eqToHom` in a full subcategory of a functor category is, at each object,
`CategoryTheory.eqToHom` of the equality of the underlying functors. -/
public theorem fullSubcategory_eqToHom_hom_app {C : Type*} {D : Type*} [Category C] [Category D]
    {P : ObjectProperty (C ⥤ D)} {A B : P.FullSubcategory} (h : A = B) (W : C) :
    (eqToHom h).hom.app W = (eqToHom (congrArg ObjectProperty.FullSubcategory.obj h)).app W := by
  subst h
  rfl

/-- `CategoryTheory.eqToHom` of an equality of functors obtained by precomposing a fixed functor
with equal ones is, at each object, that fixed functor's image of a `CategoryTheory.eqToHom`. -/
public theorem eqToHom_op_comp_app {C : Type*} {D : Type*} {E : Type*} [Category C] [Category D]
    [Category E] {H₁ H₂ : C ⥤ D} (P : Dᵒᵖ ⥤ E) (hH : H₁ = H₂) (W : Cᵒᵖ) :
    (eqToHom (congrArg (fun H : C ⥤ D => H.op ⋙ P) hH)).app W =
      P.map (eqToHom (congrArg (fun H : C ⥤ D => H.obj W.unop) hH).symm).op := by
  subst hH
  exact (P.map_id _).symm

end CategoryTheory

namespace AlgebraicGeometry.AffineQcohRestriction

open Stacks.AlgebraicGeometry.AffineQcohPushforward

attribute [local instance] Topology.IsOpenEmbedding.functor_isContinuous

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)

/-! ### Restriction to `V`, over the sheaf of rings `(f|_U)_* 𝒪_U` -/

/-- `(f|_U)_* 𝒪_U` as a sheaf of rings on `V`, for `U = f ⁻¹ᵁ V`.  By
`Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictPushforwardRing_eq` this is the
restriction of `f_* 𝒪_X` to `V`, but not definitionally so. -/
public abbrev resPushforwardRing :
    Sheaf (Opens.grothendieckTopology (V : S.Opens)) RingCat.{u} :=
  pushforwardRing (resPreimage f V).base (f ⁻¹ᵁ V).toScheme.ringCatSheaf

/-- The morphism of sheaves of rings on `V` which restriction to the open subscheme `V` is a
pushforward along: over an open `W` of `V` it is the identification
`𝒪_X(U.ι ''ᵁ (f|_U) ⁻¹ᵁ W) = 𝒪_X(f ⁻¹ᵁ (V.ι ''ᵁ W))` of
`Stacks.AlgebraicGeometry.AffineQcohRestriction.preimage_image_eq_image_resLE_preimage`.  This
is the retyping of the identity that
`Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictOver` uses. -/
public def restrictCompareRing :
    resPushforwardRing f V ⟶ ((opensImageFunctor V).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (V : S.Opens)) (Opens.grothendieckTopology S)).obj
      (pushforwardRing f.base X.ringCatSheaf) :=
  ⟨{ app W := X.ringCatSheaf.obj.map
       (eqToHom (preimage_image_eq_image_resLE_preimage f V W.unop)).op
     naturality _ _ _ :=
       Stacks.CategoryTheory.map_comp_eq_map_comp X.ringCatSheaf.obj _ _ _ _ }⟩

/-- The morphism of sheaves of rings from `f_* 𝒪_X` to the direct image of `(f|_U)_* 𝒪_U` along
`V.ι`: over an open `W` of `S` it is the restriction map
`𝒪_X(f ⁻¹ᵁ W) ⟶ 𝒪_X(U.ι ''ᵁ (f|_U) ⁻¹ᵁ V.ι ⁻¹ᵁ W)`.  This is the retyping of
`Stacks.AlgebraicGeometry.AffineQcohRestriction.toPushforwardRestrictRing`. -/
public def toResPushforwardRing :
    pushforwardRing f.base X.ringCatSheaf ⟶
      ((Opens.map V.ι.base).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology S)
        (Opens.grothendieckTopology (V : S.Opens))).obj (resPushforwardRing f V) :=
  ⟨{ app W := X.ringCatSheaf.obj.map (homOfLE
       ((preimage_image_eq_image_resLE_preimage f V (V.ι ⁻¹ᵁ W.unop)).symm.trans_le
         ((Opens.map f.base).monotone
           (leOfHom (V.ι.isOpenEmbedding.isOpenMap.adjunction.counit.app W.unop))))).op
     naturality _ _ _ :=
       Stacks.CategoryTheory.map_comp_eq_map_comp X.ringCatSheaf.obj _ _ _ _ }⟩

/-- `Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictCompareRing` **is** the transport of
the identity across
`Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictPushforwardRing_eq`, so the direct image
along it is the transport of
`Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictOver`. -/
public theorem restrictCompareRing_eq_eqToHom :
    restrictCompareRing f V = eqToHom (restrictPushforwardRing_eq f V).symm := by
  ext : 2
  funext W
  exact ((Stacks.CategoryTheory.fullSubcategory_eqToHom_hom_app _ W).trans
    (Stacks.CategoryTheory.eqToHom_op_comp_app X.ringCatSheaf.obj
      (restrictOpensFunctor_comp_eq f V).symm W)).symm

/-- **Restriction to `V` of `f_* 𝒪_X`-modules, as a functor to `(f|_U)_* 𝒪_U`-modules, is left
adjoint to a direct image.**  This is
`Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictOverAdjunction` with the identity
replaced by `Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictCompareRing`. -/
public def restrictCompareAdjunction :
    SheafOfModules.pushforward.{u} (restrictCompareRing f V) ⊣
      SheafOfModules.pushforward.{u} (toResPushforwardRing f V) := by
  refine SheafOfModules.pushforwardPushforwardAdj
    (by exact V.ι.isOpenEmbedding.isOpenMap.adjunction) (restrictCompareRing f V)
    (toResPushforwardRing f V) ?_ ?_
  · refine CategoryTheory.NatTrans.ext (funext fun _ => ?_)
    exact Stacks.CategoryTheory.map_eq_map_comp X.ringCatSheaf.obj _ _ _
  · refine CategoryTheory.NatTrans.ext (funext fun _ => ?_)
    exact Stacks.CategoryTheory.map_comp_comp_eq_id X.ringCatSheaf.obj _ _ _

/-! ### The square of direct images -/

/-- **The two composite site functors `Opens ↥S ⥤ Opens ↥U` are equal**: taking the preimage
under `V.ι` and then under `f|_U` is taking the preimage under `f` and then under `U.ι`.  Both
are `TopologicalSpace.Opens.map` of one of the two equal composites `U ⟶ V ⟶ S` and
`U ⟶ X ⟶ S`. -/
public theorem opensMapComp_eq :
    Opens.map V.ι.base ⋙ Opens.map (resPreimage f V).base =
      Opens.map f.base ⋙ Opens.map (f ⁻¹ᵁ V).ι.base :=
  CategoryTheory.Functor.ext (fun W => by
      show (resPreimage f V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W) = (f ⁻¹ᵁ V).ι ⁻¹ᵁ (f ⁻¹ᵁ W)
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι])
    fun _ _ _ => Subsingleton.elim _ _

/-- **The square of direct images commutes.**  Direct image along `f|_U` followed by direct
image along `V.ι` is the direct image along `U.ι` followed by the direct image along `f`: both
are direct images along the two equal composite site functors of
`Stacks.AlgebraicGeometry.AffineQcohRestriction.opensMapComp_eq`. -/
public def rightSquare :
    pushforwardModules.{u} (resPreimage f V).base (f ⁻¹ᵁ V).toScheme.ringCatSheaf ⋙
        SheafOfModules.pushforward.{u} (toResPushforwardRing f V) ≅
      SheafOfModules.pushforward.{u} (toPushforwardRestrictRing (f ⁻¹ᵁ V) X.ringCatSheaf) ⋙
        pushforwardModules.{u} f.base X.ringCatSheaf := by
  refine SheafOfModules.pushforwardComp (toResPushforwardRing f V) (𝟙 _) ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp (AffineQcohEquivalence.idPushforwardRing f)
      (toPushforwardRestrictRing (f ⁻¹ᵁ V) X.ringCatSheaf)).symm
  refine SheafOfModules.pushforwardCongr₂ _ (eqToIso (opensMapComp_eq f V).symm) ?_
  ext : 2
  funext _
  exact Stacks.CategoryTheory.map_comp_id_comp_eq X.ringCatSheaf.obj _ _ _

/-! ### The comparison square for the left adjoints -/

/-- **The quasi-inverse of Stacks Tag 01SB commutes with restriction to an open `V ⊆ S`.**
Restriction of `f_* 𝒪_X`-modules to `V` followed by the quasi-inverse at `f|_U` agrees with the
quasi-inverse at `f` followed by restriction of `𝒪_X`-modules to `U = f ⁻¹ᵁ V`.  The square of
right adjoints is
`Stacks.AlgebraicGeometry.AffineQcohRestriction.rightSquare`, and a commuting square of right
adjoints gives a commuting square of left adjoints by
`Stacks.CategoryTheory.leftAdjointsCommOfRightAdjointsComm`. -/
public def leftSquare :
    SheafOfModules.pushforward.{u} (restrictCompareRing f V) ⋙
        AffineQcohEquivalence.pullbackModules (resPreimage f V) ≅
      AffineQcohEquivalence.pullbackModules f ⋙ restrictOver (f ⁻¹ᵁ V) X.ringCatSheaf :=
  Stacks.CategoryTheory.leftAdjointsCommOfRightAdjointsComm
    (AffineQcohEquivalence.pullbackPushforwardAdjunction (resPreimage f V))
    (restrictCompareAdjunction f V)
    (restrictOverAdjunction (f ⁻¹ᵁ V) X.ringCatSheaf)
    (AffineQcohEquivalence.pullbackPushforwardAdjunction f)
    (rightSquare f V)

end AlgebraicGeometry.AffineQcohRestriction

end Stacks

end
