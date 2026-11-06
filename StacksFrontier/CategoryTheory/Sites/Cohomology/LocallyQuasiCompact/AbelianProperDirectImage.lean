module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.MorphismOfSites
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ImageSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ProperBaseChangeSurjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ProperDerivedImage

/-!
# Proper base change for the Zariski comparison, with abelian coefficients

`ProperBaseChangeSurjective.lean` proves the direct image clause of Stacks 0DCU for sheaves of
**sets**: for a proper `f` the base-change map `π_Y^{-1} g_* ⟶ f_{Zar,*} π_X^{-1}` is an
isomorphism. The derived clause consumes that statement for **abelian** coefficients, and the two
are not the same statement: `π^{-1}` is a chosen left adjoint, so nothing identifies the inverse
image of an abelian sheaf with the inverse image of its underlying sheaf of sets for free.

This file makes that identification and transfers the result. The route is Stacks 04JC: an abelian
sheaf is a commutative group object in sheaves of sets, the inverse image of a morphism of topoi is
left exact and therefore carries group objects to group objects, and the underlying sheaf of sets
of the result is *definitionally* the inverse image of the underlying sheaf of sets
(`CategoryTheory.Sites.abelianInverseImage_forgetIso`, which is `Iso.refl`). Uniqueness of left
adjoints identifies that functor with `abelianComparisonInverseImage`, the chosen left adjoint of
the abelian direct image, once the two right adjoints are identified — and that identification is
`Stacks.Sites.AbelianPullback.abelianSheafPushforwardIso`, generalised for this purpose from
small sites to the three independent universes of Stacks 0DCU.

## The transfer

Forgetting the group operations commutes with the comparison *direct* image on the nose, both being
restriction along the open-subset functor, so there is a square of functors whose natural
transformation is the identity. The mate of that square is a transformation

`π_Y^{-1}(F ⋙ forget) ⟶ (π_Y^{-1,Ab}F) ⋙ forget`

and it is an isomorphism for a reason that needs no description of either inverse image: it factors
as the unit of the abelian adjunction, which is invertible, followed by the *set-level* counit at
an object of the image of `π_Y^{-1}`, where it is invertible by
`Stacks.SiteImageSections.isIso_counit_app_obj`. The mates correspondence then compares the two
counits (`counit_app_sheafCompose_eq`), and since `sheafCompose J (forget AddCommGrpCat)` reflects
isomorphisms, invertibility of the set-level counit gives invertibility of the abelian one.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonTopoi`: the Zariski comparison
  as a morphism of topoi.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.abelianComparisonInverseImageForgetIso`:
  forgetting the group operations after taking the abelian comparison inverse image is taking the
  comparison inverse image of the underlying sheaf of sets.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.isIso_internalAbelianCounit_of_forget`:
  the abelian counit is invertible wherever the set-level counit is.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.isIso_zariskiBaseChange_of_properMap`:
  **the underived clause of Stacks 0DCU for abelian coefficients**, which is the first of the two
  hypotheses of `isIso_properDerivedImageComparison`.
* `…LocallyQuasiCompactZariskiSituation.isIso_properDerivedImageComparison_of_properMap`:
  the derived clause with its one remaining input isolated — properness now gives the base-change
  hypothesis, and only the acyclicity of `π_X^{-1}` of a complex of injectives is assumed.

These declarations carry no tag: Stacks 0DCU has eight claim-sites and the eighth,
`proper_derived_image`, still needs that acyclicity, so the covering set of the tag is not
complete.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Lemma 18.31.2 (Tag 04JC)](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sites TopologicalSpace

attribute [local instance] Stacks.Sites.AbelianPullback.cartesianMonoidalCategorySheaf
  Stacks.Sites.AbelianPullback.braidedCategorySheaf
  Stacks.Sites.AbelianPullback.braidedSheafToPresheaf
  Stacks.Sites.AbelianPullback.preservesFiniteLimitsSheafPushforward
  Stacks.Sites.AbelianPullback.braidedSheafPushforward
  Stacks.Sites.AbelianPullback.braidedInverseImageOfTopoi
  Stacks.Sites.AbelianPullback.braidedPushforwardOfTopoi

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v u₁ u₂ v₁ v₂

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

/-- Replacing the argument of a counit by an isomorphic object does not change whether it is
invertible. -/
private lemma isIso_counit_app_of_arg_iso {A : Type u₁} [Category.{v₁} A] {B : Type u₂}
    [Category.{v₂} B] {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) {M N : B} (e : M ≅ N)
    (h : IsIso (adj.counit.app N)) : IsIso (adj.counit.app M) := by
  have := h
  have hnat : adj.counit.app M ≫ e.hom = L.map (R.map e.hom) ≫ adj.counit.app N :=
    (adj.counit_naturality e.hom).symm
  have h2 : IsIso (adj.counit.app M ≫ e.hom) := by
    rw [hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right (adj.counit.app M) e.hom

/-- **The Zariski comparison as a morphism of topoi** `Sh(LC_Zar/X) → Sh(X_Zar)`: the inverse
image is left exact by `comparisonInverseImage_preservesFiniteLimits`. -/
def comparisonTopoiOfSize.{t} (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category) :
    MorphismOfTopoi (Sheaf (S.zariskiTopology.over X) (Type (max u t)))
      (Sheaf (Opens.grothendieckTopology X.obj) (Type (max u t))) where
  pushforward := S.comparisonDirectImage X (Type (max u t))
  inverseImage := S.comparisonInverseImage.{u, w, t} X
  adj := S.comparisonAdjunction.{u, w, t} X
  preservesFiniteLimits :=
    S.comparisonInverseImage_preservesFiniteLimits.{u, w, t} X

/-- **The Zariski comparison as a morphism of topoi** `Sh(LC_Zar/X) → Sh(X_Zar)`: the inverse
image is left exact by `comparisonInverseImage_preservesFiniteLimits`. -/
def comparisonTopoi (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    MorphismOfTopoi (Sheaf (S.zariskiTopology.over X) (Type (max (u + 1) v)))
      (Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v))) where
  pushforward := S.comparisonDirectImage X (Type (max (u + 1) v))
  inverseImage := S.comparisonInverseImage.{u, w, max (u + 1) v} X
  adj := S.comparisonAdjunction.{u, w, max (u + 1) v} X
  preservesFiniteLimits :=
    S.comparisonInverseImage_preservesFiniteLimits.{u, w, max (u + 1) v} X

variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

/-- The inverse image of abelian sheaves along the comparison morphism, built from the group
operations of the sheaf by Stacks 04JC. Its underlying sheaf of sets is the comparison inverse
image of the underlying sheaf of sets, definitionally. -/
abbrev internalAbelianComparisonInverseImageOfSize.{t} (X : S.category) :
    Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max u t} ⥤
      Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max u t} :=
  abelianInverseImage (comparisonTopoiOfSize.{u, w, t} S X)

/-- The inverse image of abelian sheaves along the comparison morphism, built from the group
operations of the sheaf by Stacks 04JC. Its underlying sheaf of sets is the comparison inverse
image of the underlying sheaf of sets, definitionally. -/
abbrev internalAbelianComparisonInverseImage (X : S.category) :
    Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v} :=
  abelianInverseImage (comparisonTopoi.{u, w, v} S X)

/-- The abelian inverse image of Stacks 04JC is left adjoint to the abelian comparison direct
image: it is left adjoint to the direct image read off through the group-object equivalence, and
that is the abelian direct image by `abelianSheafPushforwardIso`. -/
def internalAbelianComparisonAdjunctionOfSize.{t} (X : S.category) :
    internalAbelianComparisonInverseImageOfSize.{u, w, t} S X ⊣
      S.comparisonDirectImage X AddCommGrpCat.{max u t} :=
  letI := S.opensToSlice_isContinuous X
  letI : ((S.opensToSlice X).1.sheafPushforwardContinuous (Type (max u t))
      (Opens.grothendieckTopology X.obj) (S.zariskiTopology.over X)).IsRightAdjoint :=
    S.comparisonDirectImage_isRightAdjoint.{u, w, t} X
  (Stacks.Sites.AbelianPullback.abelianAdjunctionOfMorphismOfTopoi
      (comparisonTopoiOfSize.{u, w, t} S X)).ofNatIsoRight
    (Stacks.Sites.AbelianPullback.abelianSheafPushforwardIso (S.opensToSlice X).1
      (Opens.grothendieckTopology X.obj) (S.zariskiTopology.over X))

/-- The abelian inverse image of Stacks 04JC is left adjoint to the abelian comparison direct
image: it is left adjoint to the direct image read off through the group-object equivalence, and
that is the abelian direct image by `abelianSheafPushforwardIso`. -/
def internalAbelianComparisonAdjunction (X : S.category) :
    internalAbelianComparisonInverseImage.{u, w, v} S X ⊣
      S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v} :=
  letI := S.opensToSlice_isContinuous X
  letI : ((S.opensToSlice X).1.sheafPushforwardContinuous (Type (max (u + 1) v))
      (Opens.grothendieckTopology X.obj) (S.zariskiTopology.over X)).IsRightAdjoint :=
    S.comparisonDirectImage_isRightAdjoint.{u, w, max (u + 1) v} X
  (Stacks.Sites.AbelianPullback.abelianAdjunctionOfMorphismOfTopoi
      (comparisonTopoi.{u, w, v} S X)).ofNatIsoRight
    (Stacks.Sites.AbelianPullback.abelianSheafPushforwardIso (S.opensToSlice X).1
      (Opens.grothendieckTopology X.obj) (S.zariskiTopology.over X))

/-- The chosen abelian comparison inverse image is the one built from the group operations: both
are left adjoint to the abelian comparison direct image. -/
def abelianComparisonInverseImageIsoOfSize.{t} (X : S.category) :
    S.abelianComparisonInverseImageOfSize.{u, w, t} X ≅
      internalAbelianComparisonInverseImageOfSize.{u, w, t} S X :=
  Adjunction.leftAdjointUniq (S.abelianComparisonAdjunctionOfSize.{u, w, t} X)
    (internalAbelianComparisonAdjunctionOfSize.{u, w, t} S X)

/-- The chosen abelian comparison inverse image is the one built from the group operations: both
are left adjoint to the abelian comparison direct image. -/
def abelianComparisonInverseImageIso (X : S.category) :
    S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X ≅
      internalAbelianComparisonInverseImage.{u, w, v} S X :=
  Adjunction.leftAdjointUniq (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X)
    (internalAbelianComparisonAdjunction.{u, w, v} S X)

/-- **Forgetting the group operations commutes with the abelian comparison inverse image.** This
is the identification the derived clause of Stacks 0DCU needs: it is what lets the direct image
clause, proved for sheaves of sets, be used for abelian coefficients. -/
def abelianComparisonInverseImageForgetIsoOfSize.{t} (X : S.category) :
    S.abelianComparisonInverseImageOfSize.{u, w, t} X ⋙
        sheafCompose (S.zariskiTopology.over X) (forget AddCommGrpCat.{max u t}) ≅
      sheafCompose (Opens.grothendieckTopology X.obj)
          (forget AddCommGrpCat.{max u t}) ⋙
        S.comparisonInverseImage.{u, w, t} X :=
  Functor.isoWhiskerRight (abelianComparisonInverseImageIsoOfSize.{u, w, t} S X)
      (sheafCompose (S.zariskiTopology.over X) (forget AddCommGrpCat.{max u t})) ≪≫
    abelianInverseImage_forgetIso (comparisonTopoiOfSize.{u, w, t} S X)

/-- **Forgetting the group operations commutes with the abelian comparison inverse image.** This
is the identification the derived clause of Stacks 0DCU needs: it is what lets the direct image
clause, proved for sheaves of sets, be used for abelian coefficients. -/
def abelianComparisonInverseImageForgetIso (X : S.category) :
    S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X ⋙
        sheafCompose (S.zariskiTopology.over X) (forget AddCommGrpCat.{max (u + 1) v}) ≅
      sheafCompose (Opens.grothendieckTopology X.obj)
          (forget AddCommGrpCat.{max (u + 1) v}) ⋙
        S.comparisonInverseImage.{u, w, max (u + 1) v} X :=
  Functor.isoWhiskerRight (abelianComparisonInverseImageIso.{u, w, v} S X)
      (sheafCompose (S.zariskiTopology.over X) (forget AddCommGrpCat.{max (u + 1) v})) ≪≫
    abelianInverseImage_forgetIso (comparisonTopoi.{u, w, v} S X)

/-- The unit of `internalAbelianComparisonAdjunction` is invertible, because the unit of the
chosen adjunction is and the two differ by an isomorphism of left adjoints. -/
theorem internalAbelianComparisonAdjunction_unit_isIso (X : S.category) :
    IsIso (internalAbelianComparisonAdjunction.{u, w, v} S X).unit := by
  have h := abelianComparisonAdjunction_unit_isIso.{u, w, v} S X
  rw [← Adjunction.unit_leftAdjointUniq_hom (S.abelianComparisonAdjunction.{u, w,
    max (u + 1) v} X) (internalAbelianComparisonAdjunction.{u, w, v} S X)]
  infer_instance

/-- Forgetting the group operations commutes with the comparison direct image **on the nose**:
both are restriction along the open-subset functor. This is the square whose mate transfers the
proper base-change statement from sheaves of sets to abelian sheaves. -/
def forgetDirectImageSquare (X : S.category) :
    TwoSquare (S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v})
      (sheafCompose (S.zariskiTopology.over X) (forget AddCommGrpCat.{max (u + 1) v}))
      (sheafCompose (Opens.grothendieckTopology X.obj)
        (forget AddCommGrpCat.{max (u + 1) v}))
      (S.comparisonDirectImage X (Type (max (u + 1) v))) :=
  TwoSquare.mk _ _ _ _ (𝟙 _)

/-- The mate of `forgetDirectImageSquare`: the canonical comparison between the comparison
inverse image of an underlying sheaf of sets and the underlying sheaf of sets of the abelian
comparison inverse image. -/
def forgetInverseImageMate (X : S.category) :
    TwoSquare (sheafCompose (Opens.grothendieckTopology X.obj)
        (forget AddCommGrpCat.{max (u + 1) v}))
      (internalAbelianComparisonInverseImage.{u, w, v} S X)
      (S.comparisonInverseImage.{u, w, max (u + 1) v} X)
      (sheafCompose (S.zariskiTopology.over X) (forget AddCommGrpCat.{max (u + 1) v})) :=
  (mateEquiv (internalAbelianComparisonAdjunction.{u, w, v} S X)
    (S.comparisonAdjunction.{u, w, max (u + 1) v} X)).symm (forgetDirectImageSquare.{u, w, v} S X)

/-- The mate is an isomorphism, with no description of either inverse image: it factors as the
unit of the abelian adjunction, invertible by `internalAbelianComparisonAdjunction_unit_isIso`,
followed by the set-level counit at an object in the image of `π_X^{-1}`, invertible by
`Stacks.SiteImageSections.isIso_counit_app_obj`. -/
theorem isIso_forgetInverseImageMate_app (X : S.category)
    (B : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((forgetInverseImageMate.{u, w, v} S X).app B) := by
  have hu := internalAbelianComparisonAdjunction_unit_isIso.{u, w, v} S X
  have := comparisonAdjunction_unit_isIso.{u, w, max (u + 1) v} S X
  have h := unit_mateEquiv_symm (internalAbelianComparisonAdjunction.{u, w, v} S X)
    (S.comparisonAdjunction.{u, w, max (u + 1) v} X) (forgetDirectImageSquare.{u, w, v} S X) B
  have h2 : (S.comparisonAdjunction.{u, w, max (u + 1) v} X).homEquiv _ _
      ((forgetInverseImageMate.{u, w, v} S X).app B) =
      (sheafCompose (Opens.grothendieckTopology X.obj)
        (forget AddCommGrpCat.{max (u + 1) v})).map
        ((internalAbelianComparisonAdjunction.{u, w, v} S X).unit.app B) := by
    rw [Adjunction.homEquiv_unit]
    exact h.symm.trans (Category.comp_id _)
  have hce := (S.comparisonAdjunction.{u, w, max (u + 1) v} X).homEquiv_counit
    (X := (sheafCompose (Opens.grothendieckTopology X.obj)
      (forget AddCommGrpCat.{max (u + 1) v})).obj B)
    (Y := (internalAbelianComparisonInverseImage.{u, w, v} S X ⋙
      sheafCompose (S.zariskiTopology.over X)
        (forget AddCommGrpCat.{max (u + 1) v})).obj B)
    (g := (sheafCompose (Opens.grothendieckTopology X.obj)
      (forget AddCommGrpCat.{max (u + 1) v})).map
      ((internalAbelianComparisonAdjunction.{u, w, v} S X).unit.app B))
  have hfac := (((Equiv.symm_apply_eq _).2 h2.symm).symm).trans hce
  have hunitB : IsIso ((internalAbelianComparisonAdjunction.{u, w, v} S X).unit.app B) :=
    NatIso.isIso_app_of_isIso _ B
  have hcounit : IsIso ((S.comparisonAdjunction.{u, w, max (u + 1) v} X).counit.app
      ((internalAbelianComparisonInverseImage.{u, w, v} S X ⋙
        sheafCompose (S.zariskiTopology.over X)
          (forget AddCommGrpCat.{max (u + 1) v})).obj B)) :=
    Stacks.SiteImageSections.isIso_counit_app_obj (S.comparisonAdjunction.{u, w, max (u + 1) v} X)
      ((sheafCompose (Opens.grothendieckTopology X.obj)
        (forget AddCommGrpCat.{max (u + 1) v})).obj B)
  have hG : IsIso ((sheafCompose (Opens.grothendieckTopology X.obj)
      (forget AddCommGrpCat.{max (u + 1) v})).map
      ((internalAbelianComparisonAdjunction.{u, w, v} S X).unit.app B)) :=
    Functor.map_isIso _ _
  have hA : IsIso ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).map
      ((sheafCompose (Opens.grothendieckTopology X.obj)
        (forget AddCommGrpCat.{max (u + 1) v})).map
        ((internalAbelianComparisonAdjunction.{u, w, v} S X).unit.app B))) :=
    Functor.map_isIso _ _
  have hcomp := IsIso.comp_isIso' hA hcounit
  rw [hfac]
  exact hcomp

/-- **The comparison of the two counits.** The set-level counit at the underlying sheaf of sets of
`A` is the mate followed by the abelian counit, forgotten. -/
theorem counit_app_sheafCompose_eq (X : S.category)
    (A : Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}) :
    (S.comparisonAdjunction.{u, w, max (u + 1) v} X).counit.app
        ((sheafCompose (S.zariskiTopology.over X)
          (forget AddCommGrpCat.{max (u + 1) v})).obj A) =
      (forgetInverseImageMate.{u, w, v} S X).app
          ((S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}).obj A) ≫
        (sheafCompose (S.zariskiTopology.over X)
            (forget AddCommGrpCat.{max (u + 1) v})).map
          ((internalAbelianComparisonAdjunction.{u, w, v} S X).counit.app A) := by
  have key := mateEquiv_counit_symm (internalAbelianComparisonAdjunction.{u, w, v} S X)
    (S.comparisonAdjunction.{u, w, max (u + 1) v} X) (forgetDirectImageSquare.{u, w, v} S X) A
  have h0 : (S.comparisonInverseImage.{u, w, max (u + 1) v} X).map
      ((forgetDirectImageSquare.{u, w, v} S X).app A) = 𝟙 _ :=
    (S.comparisonInverseImage.{u, w, max (u + 1) v} X).map_id _
  have hid : (S.comparisonInverseImage.{u, w, max (u + 1) v} X).map
        ((forgetDirectImageSquare.{u, w, v} S X).app A) ≫
      (S.comparisonAdjunction.{u, w, max (u + 1) v} X).counit.app
        ((sheafCompose (S.zariskiTopology.over X)
          (forget AddCommGrpCat.{max (u + 1) v})).obj A) =
      (S.comparisonAdjunction.{u, w, max (u + 1) v} X).counit.app
        ((sheafCompose (S.zariskiTopology.over X)
          (forget AddCommGrpCat.{max (u + 1) v})).obj A) :=
    (congrArg (fun t => t ≫ (S.comparisonAdjunction.{u, w, max (u + 1) v} X).counit.app
        ((sheafCompose (S.zariskiTopology.over X)
          (forget AddCommGrpCat.{max (u + 1) v})).obj A)) h0).trans (Category.id_comp _)
  exact hid.symm.trans key

/-- **The abelian counit is invertible wherever the set-level counit is.** -/
theorem isIso_internalAbelianCounit_of_forget (X : S.category)
    (A : Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})
    (h : IsIso ((S.comparisonAdjunction.{u, w, max (u + 1) v} X).counit.app
      ((sheafCompose (S.zariskiTopology.over X)
        (forget AddCommGrpCat.{max (u + 1) v})).obj A))) :
    IsIso ((internalAbelianComparisonAdjunction.{u, w, v} S X).counit.app A) := by
  have hmate := isIso_forgetInverseImageMate_app.{u, w, v} S X
    ((S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}).obj A)
  rw [counit_app_sheafCompose_eq.{u, w, v} S X A] at h
  have hforget : IsIso ((sheafCompose (S.zariskiTopology.over X)
      (forget AddCommGrpCat.{max (u + 1) v})).map
        ((internalAbelianComparisonAdjunction.{u, w, v} S X).counit.app A)) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _ ((forgetInverseImageMate.{u, w, v} S X).app
        ((S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}).obj A))
      ((sheafCompose (S.zariskiTopology.over X)
        (forget AddCommGrpCat.{max (u + 1) v})).map
        ((internalAbelianComparisonAdjunction.{u, w, v} S X).counit.app A)) hmate h
  exact (isIso_iff_of_reflects_iso
    ((internalAbelianComparisonAdjunction.{u, w, v} S X).counit.app A)
    (sheafCompose (S.zariskiTopology.over X)
      (forget AddCommGrpCat.{max (u + 1) v}))).1 hforget

variable {X Y : S.category} (f : X ⟶ Y)

/-- **The abelian base-change map is an isomorphism for a proper map**: the underived clause of
Stacks 0DCU for abelian coefficients.

Its set-level counterpart is `isIso_properBaseChangeCounit`, and the objects at which the two
counits are taken agree definitionally, because the slice direct image and the Stacks 04JC
abelian comparison inverse image both commute with forgetting the group operations. -/
theorem isIso_abelianProperDirectImageComparison
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u}
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj)) :
    IsIso (abelianProperDirectImageComparison.{u, w, v} S f) := by
  rw [isIso_abelianProperDirectImageComparison_iff.{u, w, v} S f]
  intro F
  refine isIso_counit_app_of_arg_iso (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} Y)
    (((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
      (S.zariskiTopology.over Y) (S.zariskiTopology.over X)).mapIso
        ((abelianComparisonInverseImageIso.{u, w, v} S X).app F)) ?_
  rw [← Adjunction.leftAdjointUniq_hom_app_counit
    (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} Y)
    (internalAbelianComparisonAdjunction.{u, w, v} S Y)]
  have hmain : IsIso ((internalAbelianComparisonAdjunction.{u, w, v} S Y).counit.app
      (((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
          (S.zariskiTopology.over Y) (S.zariskiTopology.over X)).obj
        ((internalAbelianComparisonInverseImage.{u, w, v} S X).obj F))) := by
    refine isIso_internalAbelianCounit_of_forget.{u, w, v} S Y _ ?_
    exact isIso_properBaseChangeCounit.{u, w, v} S f (isProperMap_site S f hf)
      ((sheafCompose (Opens.grothendieckTopology X.obj)
        (forget AddCommGrpCat.{max (u + 1) v})).obj F)
  infer_instance

/-- **The hypothesis `hbc` of `isIso_properDerivedImageComparison`, discharged for a proper
map.** -/
theorem isIso_zariskiBaseChange_of_properMap
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u}
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj)) :
    IsIso (zariskiBaseChange.{u, w, v} S f) :=
  (isIso_zariskiBaseChange_iff.{u, w, v} S f).2
    (isIso_abelianProperDirectImageComparison.{u, w, v} S f hf)

section Derived

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]

/-- **Stacks 0DCU, the derived clause, with its remaining input isolated.** For a proper map the
derived Zariski base-change map is invertible as soon as `π_X^{-1}` carries a bounded-below complex
of injective abelian sheaves on the small site of `X` to an `f_{Zar,*}`-acyclic complex.

The first hypothesis of `isIso_properDerivedImageComparison` is now discharged from properness
alone, by `isIso_zariskiBaseChange_of_properMap`; the acyclicity is the only thing the derived
clause still needs, and it cannot be dropped: the derived unit of `f_{Zar,*}` is not invertible at
a general `π_X^{-1}F`, since `R^i f_{Zar,*}(π_X^{-1}F) = π_Y^{-1}(R^i g_*F)` is nonzero for
`i > 0`. -/
theorem isIso_properDerivedImageComparison_of_properMap
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u}
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj))
    (hac : ∀ K : HomotopyCategory.Plus (InjectiveObject
        (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})),
      IsIso (((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
          (S.zariskiTopology.over Y)
          (S.zariskiTopology.over X)).rightDerivedFunctorPlusUnith.app
        ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).mapHomotopyCategoryPlus.obj
          ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj K)))) :
    IsIso (properDerivedImageComparison.{u, w, v} S f) :=
  isIso_properDerivedImageComparison.{u, w, v} S f
    (isIso_zariskiBaseChange_of_properMap.{u, w, v} S f hf) hac

end Derived

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
