module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverBaseChangeFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPushforwardAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalenceProof
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismLimitPresentation
public import Mathlib.CategoryTheory.Comma.Presheaf.Basic

/-!
# The direct image of the structure sheaf detects limits of spaces affine over the base

If a cone of algebraic spaces affine over an algebraic space `Y` is sent by the direct-image
functor `f ↦ f_* 𝒪` of Stacks 081V to a colimit of algebra sheaves, then its underlying cone of
presheaves over `Y` is a limit.

This is the step "`X = lim X_i` by construction" in the proof of Stacks 0870, where
`X_i = \underline{Spec}_Y(𝒜_i)` for a directed colimit `f_* 𝒪_X = colim 𝒜_i`.

## Main definitions

* `AlgebraicGeometry.Space.affineOverSectionsIso`: for a representable `T ⟶ Y`, the points
  `T ⟶ Z` over `Y` of a space `Z` affine over `Y` are the sections of `T ×_Y Z ⟶ T`, naturally
  in `Z`.

## Main results

* `AlgebraicGeometry.Space.isLimitAffineOverBaseChangeMapCone`: base change preserves such a
  limit, since algebra pullback is a left adjoint
  (`AlgebraicGeometry.Space.algebraPullbackPushforwardAdjunction`), the direct image commutes
  with base change (`AlgebraicGeometry.Space.quasicoherentAffineOverBaseChangeNatIso`) and is
  fully faithful (`AlgebraicGeometry.Space.full_affinePushforwardAlgebraFunctor`,
  `AlgebraicGeometry.Space.faithful_affinePushforwardAlgebraFunctor`).
* `AlgebraicGeometry.Space.isLimitOfCoyonedaToOver`: a cone in the slice of presheaves over `A`
  is a limit once every representable object over `A` sees it as a limit.
* `AlgebraicGeometry.Space.isLimitAffineOverToOverMapCone`: the underlying cone of presheaves
  over `Y` is a limit.

## Implementation notes

The colimit is asked for in the category of all algebra sheaves, not only among the
quasi-coherent ones: algebra pullback is a left adjoint there, and the quasi-coherent algebras
form a full subcategory, which reflects but need not create colimits.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 0870](https://stacks.math.columbia.edu/tag/0870)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)

/-- **Base change of algebraic spaces affine over `X` preserves a limit whose image under the
direct-image functor is a colimit of algebra sheaves.**  Algebra pullback is a left adjoint, so it
preserves that colimit; the direct image commutes with base change, and it is fully faithful, so
it reflects the colimit back to the base change of the limit. -/
def isLimitAffineOverBaseChangeMapCone {J : Type u} [SmallCategory J]
    {F : J ⥤ (AffineOver B S hS X)ᵒᵖ} (K : Cocone F)
    (hK : IsColimit ((quasicoherentAlgebraInclusion B S hS X).mapCocone
      ((quasicoherentPushforwardAlgebraFunctor B S hS X).mapCocone K))) :
    IsLimit ((affineOverBaseChangeFunctor B S hS g).mapCone (coneLeftOpOfCocone K)) := by
  haveI := (algebraPullbackPushforwardAdjunction B S hS g).isLeftAdjoint
  have h1 : IsColimit ((algebraPullback B S hS g).mapCocone
      ((quasicoherentAlgebraInclusion B S hS X).mapCocone
        ((quasicoherentPushforwardAlgebraFunctor B S hS X).mapCocone K))) :=
    isColimitOfPreserves (algebraPullback B S hS g) hK
  have h2 : IsColimit ((quasicoherentAlgebraPullback B S hS g).mapCocone
      ((quasicoherentPushforwardAlgebraFunctor B S hS X).mapCocone K)) :=
    isColimitOfReflects (quasicoherentAlgebraInclusion B S hS Y) h1
  have h3 : IsColimit ((quasicoherentPushforwardAlgebraFunctor B S hS X ⋙
      quasicoherentAlgebraPullback B S hS g).mapCocone K) := h2
  have h4 : IsColimit (((affineOverBaseChangeFunctor B S hS g).op ⋙
      quasicoherentPushforwardAlgebraFunctor B S hS Y).mapCocone K) :=
    IsColimit.mapCoconeEquiv (quasicoherentAffineOverBaseChangeNatIso B S hS g) h3
  haveI := full_affinePushforwardAlgebraFunctor B S hS Y
  haveI := faithful_affinePushforwardAlgebraFunctor B S hS Y
  have h5 : IsColimit ((affineOverBaseChangeFunctor B S hS g).op.mapCocone K) :=
    isColimitOfReflects (quasicoherentPushforwardAlgebraFunctor B S hS Y) h4
  exact isLimitConeLeftOpOfCocone _ h5

/-! ### Limits in a slice of presheaves, tested on representable objects -/

section OverLimit

variable {𝒞 : Type*} [Category.{u} 𝒞] {A : 𝒞ᵒᵖ ⥤ Type u} {J : Type*} [Category J]

/-- A cone in the slice `Over A` of presheaves is a limit as soon as every representable object
over `A` turns it into a limit of hom-sets: `Over A` is equivalent to the presheaves on
`CostructuredArrow yoneda A`, where limits are computed objectwise, and the value at an object
is the hom-set out of the corresponding representable object over `A`. -/
def isLimitOfCoyonedaToOver {K : J ⥤ Over A} (c : Cone K)
    (h : ∀ T : CostructuredArrow yoneda A,
      IsLimit ((coyoneda.obj (op ((CostructuredArrow.toOver yoneda A).obj T))).mapCone c)) :
    IsLimit c := by
  let e := overEquivPresheafCostructuredArrow A
  refine isLimitOfReflects e.functor (evaluationJointlyReflectsLimits _ fun T => ?_)
  let iso2 : coyoneda.obj (op (yoneda.obj T.unop)) ≅
      (evaluation _ (Type u)).obj T ⋙ uliftFunctor.{u_1, u} :=
    NatIso.ofComponents (fun P => Equiv.toIso (yonedaEquiv.trans Equiv.ulift.symm))
      (fun f => by
        ext x
        exact congrArg ULift.up (yonedaEquiv_comp x f))
  let iso1 : coyoneda.obj (op ((CostructuredArrow.toOver yoneda A).obj T.unop)) ≅
      e.functor ⋙ coyoneda.obj (op (yoneda.obj T.unop)) :=
    (CostructuredArrow.toOverCompCoyoneda A).app T
  have h' : IsLimit ((e.functor ⋙ (evaluation _ (Type u)).obj T ⋙ uliftFunctor.{u_1, u}).mapCone
      c) := IsLimit.mapConeEquiv (iso1 ≪≫ Functor.isoWhiskerLeft e.functor iso2) (h T.unop)
  exact isLimitOfReflects uliftFunctor.{u_1, u} h'

end OverLimit

variable {Y : AlgebraicSpaces B S hS}

/-- The representable algebraic space of a test object over `Y`. -/
abbrev affineOverTestSpace (T : CostructuredArrow yoneda Y.obj) : AlgebraicSpaces B S hS :=
  schemeSpace T.left

/-- The structure morphism of a test object over `Y`, as a morphism of algebraic spaces. -/
abbrev affineOverTestMap (T : CostructuredArrow yoneda Y.obj) : affineOverTestSpace T ⟶ Y :=
  ObjectProperty.homMk T.hom

/-- **Points of an affine space over `Y` with values in a test object are sections of its base
change.**  For `T ⟶ Y` with `T` representable, a morphism `T ⟶ Z` over `Y` is the same thing as a
section of the base change `T ×_Y Z ⟶ T`, naturally in `Z`. -/
def affineOverSectionsIso (T : CostructuredArrow yoneda Y.obj) :
    affineOverBaseChangeFunctor B S hS (affineOverTestMap T) ⋙
        coyoneda.obj (op (idAffineOver B S hS (affineOverTestSpace T))) ≅
      affineOverToOver B S hS Y ⋙
        coyoneda.obj (op ((CostructuredArrow.toOver yoneda Y.obj).obj T)) :=
  NatIso.ofComponents (fun Z => Equiv.toIso (show
    (idAffineOver B S hS (affineOverTestSpace T) ⟶
        affineOverBaseChange B S hS (affineOverTestMap T) Z) ≃
      ((CostructuredArrow.toOver yoneda Y.obj).obj T ⟶ (affineOverToOver B S hS Y).obj Z) from
    { toFun := fun σ => Over.homMk
        (σ.hom.left.hom ≫ (affineOverBaseChangeProjection B S hS (affineOverTestMap T) Z).hom) (by
          have h1 := congrArg (fun k => k.hom)
            (affineOverBaseChange_isPullback B S hS (affineOverTestMap T) Z).w
          have h2 := congrArg (fun k => k.hom) (Over.w σ.hom)
          simp only [ObjectProperty.FullSubcategory.comp_hom] at h1 h2
          change (σ.hom.left.hom ≫
              (affineOverBaseChangeProjection B S hS (affineOverTestMap T) Z).hom) ≫
            Z.obj.hom.hom = T.hom
          rw [Category.assoc, h1, ← Category.assoc, h2]
          exact Category.id_comp _)
      invFun := fun x => ObjectProperty.homMk (Over.homMk
        ((affineOverBaseChange_isPullback B S hS (affineOverTestMap T) Z).lift
          (ObjectProperty.homMk (CommaMorphism.left x))
          (𝟙 _) (by
            ext1
            exact (Over.w x).trans (Category.id_comp _).symm))
        ((affineOverBaseChange_isPullback B S hS (affineOverTestMap T) Z).lift_snd _ _ _))
      left_inv := fun σ => by
        refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
        refine (affineOverBaseChange_isPullback B S hS (affineOverTestMap T) Z).hom_ext ?_ ?_
        · exact ((affineOverBaseChange_isPullback B S hS (affineOverTestMap T) Z).lift_fst
            _ _ _).trans
            (ObjectProperty.hom_ext _ rfl)
        · exact ((affineOverBaseChange_isPullback B S hS (affineOverTestMap T) Z).lift_snd
            _ _ _).trans
            (Over.w σ.hom).symm
      right_inv := fun x => by
        refine Over.OverMorphism.ext ?_
        exact congrArg (fun k : (affineOverTestSpace T) ⟶ Z.obj.left => k.hom)
          ((affineOverBaseChange_isPullback B S hS (affineOverTestMap T) Z).lift_fst
            (ObjectProperty.homMk (CommaMorphism.left x)) (𝟙 _) _) }))
    (fun {Z Z'} f => by
      ext σ
      have h := congrArg
        (fun k : (affineOverBaseChange B S hS (affineOverTestMap T) Z).obj.left ⟶ Z'.obj.left =>
          k.hom)
        (affineOverBaseChangeMap_comp_projection B S hS (affineOverTestMap T) f)
      simp only [ObjectProperty.FullSubcategory.comp_hom] at h
      refine Over.OverMorphism.ext ?_
      change (σ.hom.left.hom ≫ (affineOverBaseChangeMap B S hS
          (affineOverTestMap T) f).hom.left.hom) ≫
          (affineOverBaseChangeProjection B S hS (affineOverTestMap T) Z').hom =
        (σ.hom.left.hom ≫ (affineOverBaseChangeProjection B S hS (affineOverTestMap T) Z).hom) ≫
          f.hom.left.hom
      exact (Category.assoc _ _ _).trans
        ((congrArg (σ.hom.left.hom ≫ ·) h).trans (Category.assoc _ _ _).symm))

/-- **The relative spectrum turns a colimit of algebra sheaves into a limit of presheaves.**  If a
cone of algebraic spaces affine over `Y` is sent by the direct-image functor of Stacks 081V to a
colimit of algebra sheaves, then its underlying cone of presheaves over `Y` is a limit.  This is
tested on representable objects `T ⟶ Y`, where it is the preservation of the limit by base change
along `T ⟶ Y`. -/
def isLimitAffineOverToOverMapCone {J : Type u} [SmallCategory J]
    {F : J ⥤ (AffineOver B S hS Y)ᵒᵖ} (K : Cocone F)
    (hK : IsColimit ((quasicoherentAlgebraInclusion B S hS Y).mapCocone
      ((quasicoherentPushforwardAlgebraFunctor B S hS Y).mapCocone K))) :
    IsLimit ((affineOverToOver B S hS Y).mapCone (coneLeftOpOfCocone K)) :=
  isLimitOfCoyonedaToOver _ fun T =>
    IsLimit.mapConeEquiv (affineOverSectionsIso T)
      (isLimitOfPreserves (coyoneda.obj (op (idAffineOver B S hS (affineOverTestSpace T))))
        (isLimitAffineOverBaseChangeMapCone (affineOverTestMap T) K hK))

end AlgebraicGeometry.Space
