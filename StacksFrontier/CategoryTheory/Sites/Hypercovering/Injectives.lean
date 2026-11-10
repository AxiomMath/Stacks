module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Cohomology
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SectionsComplex

/-!
# Čech cohomology of an injective sheaf on a hypercovering of a presheaf

Let `C` be a category with equalizers and fibre products, equipped with a pretopology `J`, let
`G` be a presheaf of sets on `C` and let `K` be a hypercovering of `G` (Tag 09VU). If `I` is an
*injective* sheaf of abelian groups on the associated site, then the Čech cohomology of `I` on
`K` (Tag 09VV) vanishes in every positive degree, and in degree zero it is the degree-zero
cohomology of `G`.

The proof is the one of the source. The complex of sections of `I` on `K` is, by Tag 01GX, the
complex `Hom(s(**Z**_{F(K)}^♯), I)`; since `I` is injective the functor `Hom(-, I)` is exact, so
that complex is exact wherever `s(**Z**_{F(K)}^♯)` is, and Tag 01GE says the latter is exact in
every positive degree because the augmentation of `F(K)` towards `G` satisfies the three local
surjectivity conditions of a hypercovering.

Supplying Tag 01GE's third hypothesis is the only real work: it asks for local surjectivity of
the unit of the `n`-coskeleton adjunction computed *in presheaves*, whereas a hypercovering
provides local surjectivity of the matching maps `higherMatchingMap`, which are the images under
`F` of the unit of the `n`-coskeleton adjunction computed in semi-representable objects. The two
agree because `F` preserves the pointwise right Kan extensions defining those coskeleta, and
that in turn is because `FormalCoproduct.uliftYoneda` preserves limits.

## Main definitions

* `CategoryTheory.Limits.FormalCoproduct.uliftYonedaObjObjIso` and
  `CategoryTheory.Limits.FormalCoproduct.uliftYonedaCompEvaluationIso`: the presheaf represented
  by a semi-representable object, evaluated at a fixed object of `C`, is the set of morphisms
  out of that object in `FormalCoproduct.{w} C`, up to one universe lift.
* `Stacks.CategoryTheory.Hypercovering.HypercoveringOf.toAugmentedULiftLeftIso`: the simplicial
  presheaf underlying `HypercoveringOf.toAugmentedULift` is the associated simplicial presheaf
  of Tag 09VU taken at the common universe of the statement.

## Main results

* `CategoryTheory.Limits.FormalCoproduct.preservesLimitsOfSize_uliftYoneda`: the semi-representable
  Yoneda embedding `FormalCoproduct.uliftYoneda` preserves all limits, because each of its
  evaluations is corepresentable.
* `CategoryTheory.Functor.whiskerRight_eq_of_isRightKanExtension`: a functor that preserves a
  right Kan extension carries the unit of that extension to the unit of the extension of the
  image, through the canonical comparison of the two extensions.
* `Stacks.CategoryTheory.Hypercovering.isLocallySurjective_coskAdj_unit_app_comp`: transporting
  local surjectivity of the image under a limit-preserving functor of a coskeleton unit to the
  coskeleton unit of the image.
* `Stacks.CategoryTheory.Hypercovering.isLocallySurjective_coskAdj_unit_app_toAugmentedULift`:
  condition (3) of a hypercovering of a presheaf, read as local surjectivity of the coskeleton
  units of `HypercoveringOf.toAugmentedULift`, which is the form Tag 01GE asks for.
* `Stacks.CategoryTheory.Hypercovering.cechCohomology_isZero_of_injective`: the positive-degree
  vanishing half of **Tag 09VW**.
* `Stacks.CategoryTheory.Hypercovering.cechCohomologyIsoOfInjective`: **Tag 09VW** in full, as a
  single `p`-indexed isomorphism — `Ȟᵖ(K, I)` is `H⁰(G, I)` when `p = 0` and zero when `p > 0`.

## Implementation notes

The degree-zero identification of the source is Tag 09VV's
`Stacks.CategoryTheory.Hypercovering.cechCohomologyZeroIso`, which holds for every sheaf of
abelian groups and needs no injectivity hypothesis, so only the positive-degree assertion is
*proved* here; `cechCohomologyIsoOfInjective` then assembles the two branches into the single
`p`-indexed statement that the source makes.

Four universes occur and none of them is specialised: `C : Type u` with `Category.{v} C`, the
index types of the semi-representable objects live in `Type w`, and the presheaf `G` being
covered takes values in `Type q`. The sheaf of abelian groups is valued in
`AddCommGrpCat.{max (max u v) (max q w)}`, so the statement covers coefficients in any universe
at least `max u v w`, and every `max` in it is load-bearing: the presheaf represented by a
semi-representable object has values in `Type (max w v)`, the augmentation target has values in
`Type q`, and the two must be lifted into one universe before they can be compared. This is
inherited verbatim from Tags 09VU, 09VV and 01GX and nothing here narrows it.

Sheafification of `AddCommGrpCat.{max (max u v) (max q w)}`-valued presheaves is not a
hypothesis of the statement — Tag 09VV's Čech cohomology is defined without it — so it is
supplied inside the proof by Tag 09VV's `hasSheafify_addCommGrpCat`, which obtains it from a
small model of the site.

Two transparency decisions are forced rather than chosen.

First, `uliftYonedaCompEvaluationIso` states its naturality square after an explicit `show`
that spells the two objects involved as `(∐ ..).obj K` rather than as
`(FormalCoproduct.uliftYoneda ⋙ evaluation ..).obj X`, and its component is a separate
declaration `uliftYonedaObjObjIso` whose codomain is written as the target functor applied to
`X`. Both are needed. `FormalCoproduct.eval` is semireducible, so the two spellings of the
object are equal only at default transparency, and without the `show` every `rw` and `simp` on
the naturality goal is rejected by the type-correctness check on its motive — which is what the
`backward` transparency option of the original proof was hiding. The
same holds for `uliftFunctor.obj` against `ULift`, which is why the component's codomain is not
written as a bare `ULift`.

Second, `isLocallySurjective_coskAdj_unit_app_comp` states the hypothesis under a `letI`
supplying `hasPositiveCoskeleta`: the coskeleton of a simplicial semi-representable object is
only available once equalizers and fibre products have been turned into the relevant pointwise
right Kan extensions, exactly as in Tag 09VU's `higherMatchingMap`.

`isLocallySurjective_coskAdj_unit_app_comp` is stated for an arbitrary limit-preserving functor
into presheaves of sets rather than only for Tag 09VU's `associatedPresheafFunctor`. That is
more general, and it is also what makes it applicable directly to the universe-lifted functor
`associatedPresheafFunctor ⋙ presheafULiftFunctor` whose composition with the hypercovering is
`HypercoveringOf.toAugmentedULift.left`, so no further transport along a universe comparison is
needed to meet Tag 01GE.

## References

* [Stacks Project, Tag 09VW](https://stacks.math.columbia.edu/tag/09VW)
* [Stacks Project, Tag 09VV](https://stacks.math.columbia.edu/tag/09VV)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
* [Stacks Project, Tag 01GE](https://stacks.math.columbia.edu/tag/01GE)
* [Stacks Project, Tag 01GX](https://stacks.math.columbia.edu/tag/01GX)
-/

@[expose] public section

universe q w v u t

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor

/-- Let `Y` be a right Kan extension of `L ⋙ X` along `L` with unit `η₀`, let `Z` be a right Kan
extension of `L ⋙ X ⋙ G` along `L` with unit `η`, and let `e : Y ⋙ G ≅ Z` be a comparison of the
two extensions compatible with their counits.  Then `G` carries `η₀` to `η`.

This is the statement that a functor preserving the right Kan extension defining a coskeleton
carries the unit of that coskeleton to the unit of the coskeleton of the image. -/
lemma whiskerRight_eq_of_isRightKanExtension
    {A : Type*} {B : Type*} {D : Type*} {E : Type*}
    [Category A] [Category B] [Category D] [Category E]
    (L : A ⥤ D) (Y : D ⥤ B) (X : D ⥤ B) (G : B ⥤ E)
    (α : L ⋙ Y ⟶ L ⋙ X) [Y.IsRightKanExtension α]
    (η₀ : X ⟶ Y) (hη₀ : L.whiskerLeft η₀ ≫ α = 𝟙 (L ⋙ X))
    (Z : D ⥤ E) (ε : L ⋙ Z ⟶ L ⋙ X ⋙ G) [Z.IsRightKanExtension ε]
    (η : X ⋙ G ⟶ Z) (hη : L.whiskerLeft η ≫ ε = 𝟙 (L ⋙ X ⋙ G))
    (e : Y ⋙ G ≅ Z)
    (he : L.whiskerLeft e.hom ≫ ε =
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight α G) :
    Functor.whiskerRight η₀ G ≫ e.hom = η := by
  apply Functor.hom_ext_of_isRightKanExtension Z ε _ _
  ext a
  have heapp : e.hom.app (L.obj a) ≫ ε.app a =
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α G).app a := by
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app] using NatTrans.congr_app he a
  simp only [Functor.whiskerLeft_app, NatTrans.comp_app]
  rw [Category.assoc, heapp]
  simp only [Functor.associator_inv_app, Functor.whiskerRight_app,
    NatTrans.comp_app, Category.id_comp]
  rw [← G.map_comp]
  have h₀ := NatTrans.congr_app hη₀ a
  have h₁ := NatTrans.congr_app hη a
  simp only [Functor.whiskerLeft_app, NatTrans.comp_app] at h₀ h₁
  rw [h₀]
  simpa using h₁.symm

end CategoryTheory.Functor

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C]

/-- The presheaf represented by a semi-representable object `X`, evaluated at `K`, is the set of
morphisms `incl(K) ⟶ X` of semi-representable objects, up to one universe lift.

The codomain is written as the comparison functor applied to `X` rather than as a bare `ULift`
because `uliftFunctor.obj` is only equal to `ULift` at default transparency, and the naturality
proof of `uliftYonedaCompEvaluationIso` needs the two spellings to agree syntactically. -/
noncomputable def uliftYonedaObjObjIso (K : Cᵒᵖ) (X : FormalCoproduct.{w} C) :
    (∐ fun i : X.I => uliftYoneda.{w}.obj (X.obj i)).obj K ≅
      (coyoneda.obj (op ((FormalCoproduct.incl C).obj K.unop)) ⋙
        uliftFunctor.{w, max w v}).obj X :=
  sigmaObjIso (fun i : X.I => uliftYoneda.{w}.obj (X.obj i)) K ≪≫
    Types.coproductIso (fun i : X.I => (uliftYoneda.{w}.obj (X.obj i)).obj K) ≪≫
      Equiv.toIso
        { toFun := fun z : (i : X.I) × ULift.{w} (K.unop ⟶ X.obj i) =>
            ULift.up ((FormalCoproduct.inclHomEquiv K.unop X).symm ⟨z.1, z.2.down⟩)
          invFun := fun z : ULift.{w} ((FormalCoproduct.incl C).obj K.unop ⟶ X) =>
            ⟨(FormalCoproduct.inclHomEquiv K.unop X z.down).1,
              ULift.up (FormalCoproduct.inclHomEquiv K.unop X z.down).2⟩
          left_inv := by intro z; cases z with | mk i h => cases h; rfl
          right_inv := by
            intro z
            cases z with
            | up g =>
              exact congrArg ULift.up
                ((FormalCoproduct.inclHomEquiv K.unop X).symm_apply_apply g) }

/-- Each evaluation of the semi-representable Yoneda embedding is corepresented by the image of
the object of evaluation under `FormalCoproduct.incl`, up to one universe lift. -/
noncomputable def uliftYonedaCompEvaluationIso (K : Cᵒᵖ) :
    FormalCoproduct.uliftYoneda.{w} (C := C) ⋙
        (evaluation Cᵒᵖ (Type (max w v))).obj K ≅
      coyoneda.obj (op ((FormalCoproduct.incl C).obj K.unop)) ⋙
        uliftFunctor.{w, max w v} :=
  NatIso.ofComponents (fun X => uliftYonedaObjObjIso.{w} K X) (fun {X Y} f => by
    change (Sigma.desc fun j : X.I => uliftYoneda.{w}.map (f.φ j) ≫
          Sigma.ι (fun i : Y.I => uliftYoneda.{w}.obj (Y.obj i)) (f.f j)).app K ≫
            (uliftYonedaObjObjIso.{w} K Y).hom =
        (uliftYonedaObjObjIso.{w} K X).hom ≫
          uliftFunctor.{w, max w v}.map
            ((coyoneda.obj (op ((FormalCoproduct.incl C).obj K.unop))).map f)
    apply (cancel_epi (sigmaObjIso (fun i : X.I => uliftYoneda.{w}.obj (X.obj i)) K).inv).1
    apply Sigma.hom_ext
    intro i
    rw [ι_comp_sigmaObjIso_inv_assoc, ← Category.assoc, ← NatTrans.comp_app, Sigma.ι_comp_desc,
      NatTrans.comp_app, Category.assoc]
    simp only [uliftYonedaObjObjIso, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc,
      ι_comp_sigmaObjIso_hom_assoc]
    ext g
    simp [FormalCoproduct.inclHomEquiv, FormalCoproduct.Hom.fromIncl,
      FormalCoproduct.Hom.asSigma]
    rfl)

/-- The semi-representable Yoneda embedding preserves all limits: limits of presheaves are
computed pointwise and each of its evaluations is corepresentable. -/
noncomputable instance preservesLimitsOfSize_uliftYoneda :
    PreservesLimitsOfSize (FormalCoproduct.uliftYoneda.{w} (C := C)) := by
  apply preservesLimits_of_evaluation
  intro K
  exact (preservesLimitsOfSize_iff_of_natIso
    (uliftYonedaCompEvaluationIso.{w} (C := C) K)).2 inferInstance

end CategoryTheory.Limits.FormalCoproduct

namespace Stacks.CategoryTheory.Hypercovering

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]

/-- If a limit-preserving functor `F` into presheaves of sets takes the degree-`n + 1` component
of the unit of the `n`-coskeleton adjunction of a simplicial semi-representable object `K` to a
locally surjective map, then the corresponding component of the unit of the `n`-coskeleton
adjunction of `K ⋙ F`, computed in presheaves, is locally surjective.

This is the comparison that turns condition (3) of a hypercovering of a presheaf, which is
stated in terms of coskeleta of semi-representable objects, into the hypothesis of Tag 01GE,
which is stated in terms of coskeleta of simplicial presheaves. -/
theorem isLocallySurjective_coskAdj_unit_app_comp (J : GrothendieckTopology C)
    (F : FormalCoproduct.{w} C ⥤ Cᵒᵖ ⥤ Type t) [PreservesLimitsOfSize.{0, 0} F]
    (K : SimplicialObject (FormalCoproduct.{w} C)) (n : ℕ) (hn : 1 ≤ n)
    (hsource : letI := hasPositiveCoskeleta.{w} (C := C) n hn
      Presheaf.IsLocallySurjective J
        (F.map (((SimplicialObject.coskAdj n).unit.app K).app
          (op (SimplexCategory.mk (n + 1)))))) :
    Presheaf.IsLocallySurjective J
      (((SimplicialObject.coskAdj n).unit.app (K ⋙ F)).app
        (op (SimplexCategory.mk (n + 1)))) := by
  let A := (SimplexCategory.Truncated n)ᵒᵖ
  let D := SimplexCategoryᵒᵖ
  let B := FormalCoproduct.{w} C
  let E := Cᵒᵖ ⥤ Type t
  let L : A ⥤ D := (SimplexCategory.Truncated.inclusion n).op
  let X : D ⥤ B := K
  let _ : ∀ Z : A ⥤ B, L.HasPointwiseRightKanExtension Z :=
    fun Z => hasPositiveCoskeleta.{w} (C := C) n hn Z
  let _ : ∀ Z : A ⥤ B, L.HasRightKanExtension Z := fun Z =>
    (L.isPointwiseRightKanExtensionRanCounit Z).hasRightKanExtension
  let _ : ∀ Z : A ⥤ E, L.HasPointwiseRightKanExtension Z := by
    intro Z c
    infer_instance
  let _ : ∀ Z : A ⥤ E, L.HasRightKanExtension Z := fun Z =>
    (L.isPointwiseRightKanExtensionRanCounit Z).hasRightKanExtension
  let _ : F.PreservesPointwiseRightKanExtension (L ⋙ X) L := by
    intro c
    infer_instance
  let _ : F.PreservesRightKanExtension (L ⋙ X) L := inferInstance
  let XF : D ⥤ E := X ⋙ F
  let Y : D ⥤ B :=
    (SimplicialObject.Truncated.cosk n).obj ((SimplicialObject.truncation n).obj X)
  let α : L ⋙ Y ⟶ L ⋙ X :=
    (SimplicialObject.coskAdj n).counit.app ((SimplicialObject.truncation n).obj X)
  let η₀ : X ⟶ Y := (SimplicialObject.coskAdj n).unit.app X
  let _ : Y.IsRightKanExtension α := by
    change ((SimplicialObject.cosk n).obj X).IsRightKanExtension
      ((SimplicialObject.coskAdj n).counit.app ((SimplicialObject.truncation n).obj X))
    infer_instance
  let εs := (Functor.associator _ _ _).inv ≫ Functor.whiskerRight α F
  let XFtr := (SimplicialObject.truncation n).obj XF
  let Z : D ⥤ E := (SimplicialObject.cosk n).obj XF
  let ε : L ⋙ Z ⟶ L ⋙ X ⋙ F := (SimplicialObject.coskAdj n).counit.app XFtr
  let η : X ⋙ F ⟶ Z := (SimplicialObject.coskAdj n).unit.app XF
  let _ : Z.IsRightKanExtension ε := by
    change ((SimplicialObject.cosk n).obj XF).IsRightKanExtension
      ((SimplicialObject.coskAdj n).counit.app XFtr)
    infer_instance
  let e := Functor.rightKanExtensionUnique (Y ⋙ F) εs Z ε
  have he : L.whiskerLeft e.hom ≫ ε = εs := by
    simp [e, Functor.rightKanExtensionUnique, Functor.liftOfIsRightKanExtension_fac, εs]
  have hη₀ : L.whiskerLeft η₀ ≫ α = 𝟙 (L ⋙ X) := by
    change (SimplicialObject.truncation n).map
        ((SimplicialObject.coskAdj n).unit.app X) ≫
      (SimplicialObject.coskAdj n).counit.app ((SimplicialObject.truncation n).obj X) =
        𝟙 ((SimplicialObject.truncation n).obj X)
    exact (SimplicialObject.coskAdj n).left_triangle_components X
  have hη : L.whiskerLeft η ≫ ε = 𝟙 (L ⋙ X ⋙ F) := by
    change (SimplicialObject.truncation n).map
        ((SimplicialObject.coskAdj n).unit.app XF) ≫
      (SimplicialObject.coskAdj n).counit.app XFtr = 𝟙 XFtr
    exact (SimplicialObject.coskAdj n).left_triangle_components XF
  have hunit := Functor.whiskerRight_eq_of_isRightKanExtension
    L Y X F α η₀ hη₀ Z ε η hη e he
  let x := op (SimplexCategory.mk (n + 1))
  have hmap :
      F.map (((SimplicialObject.coskAdj n).unit.app X).app x) ≫ e.hom.app x =
        ((SimplicialObject.coskAdj n).unit.app (X ⋙ F)).app x := by
    simpa [η₀, η, X] using NatTrans.congr_app hunit x
  let _ : Presheaf.IsLocallySurjective J
      (F.map (((SimplicialObject.coskAdj n).unit.app K).app x)) := hsource
  rw [← hmap]
  exact inferInstance

/-- Condition (3) of a hypercovering of a presheaf, read as local surjectivity of the units of
the coskeleton adjunctions of the simplicial presheaf underlying
`HypercoveringOf.toAugmentedULift`.  This is the third hypothesis of Tag 01GE. -/
theorem isLocallySurjective_coskAdj_unit_app_toAugmentedULift (J : Pretopology C)
    (G : Cᵒᵖ ⥤ Type q) (K : HypercoveringOf.{q, w} J G) (n : ℕ) (hn : 1 ≤ n) :
    Presheaf.IsLocallySurjective J.toGrothendieck
      (((SimplicialObject.coskAdj n).unit.app
        (K.toAugmentedULift.{q, w, v, u} J G).left).app
          (op (SimplexCategory.mk (n + 1)))) := by
  let W := presheafULiftFunctor.{max q w v, max (max u v) (max q w)} (C := C)
  let F := associatedPresheafFunctor.{q, w, v, u} (C := C) ⋙ W
  let _ : PreservesLimitsOfSize.{0, 0} F := inferInstance
  have hsource : letI := hasPositiveCoskeleta.{w} (C := C) n hn
      Presheaf.IsLocallySurjective J.toGrothendieck
        (F.map (((SimplicialObject.coskAdj n).unit.app K.toSimplicialObject).app
          (op (SimplexCategory.mk (n + 1))))) := by
    have _ : Presheaf.IsLocallySurjective J.toGrothendieck
        (higherMatchingMap.{q} K.toSimplicialObject n hn) :=
      K.locallySurjective_succ n hn
    exact isLocallySurjective_presheafULiftFunctor_map.{max q w v, max (max u v) (max q w)}
      (C := C) J.toGrothendieck (higherMatchingMap.{q} K.toSimplicialObject n hn)
  exact isLocallySurjective_coskAdj_unit_app_comp J.toGrothendieck F
    K.toSimplicialObject n hn hsource

/-- The simplicial presheaf underlying `HypercoveringOf.toAugmentedULift` is the associated
simplicial presheaf of Tag 09VU taken at the common universe of the statement. -/
noncomputable def HypercoveringOf.toAugmentedULiftLeftIso (J : Pretopology C)
    (G : Cᵒᵖ ⥤ Type q) (K : HypercoveringOf.{q, w} J G) :
    (K.toAugmentedULift.{q, w, v, u} J G).left ≅
      associatedSimplicialPresheaf.{max (max u v) (max q w)} K.toSimplicialObject := by
  change (K.toSimplicialObject ⋙ associatedPresheafFunctor.{q} ⋙
      presheafULiftFunctor.{max q w v, max (max u v) (max q w)}) ≅
    (K.toSimplicialObject ⋙ associatedPresheafFunctor.{max (max u v) (max q w)})
  exact Functor.isoWhiskerLeft K.toSimplicialObject
    (associatedPresheafFunctorULiftIso.{q, w, v, u} (C := C))

/-- **Stacks Project, Tag 09VW (positive degrees).** Positive-degree Čech cohomology of an
injective abelian sheaf on a hypercovering of a presheaf vanishes. -/
@[stacks 09VW "positive degrees"]
theorem cechCohomology_isZero_of_injective (J : Pretopology C)
    (G : Cᵒᵖ ⥤ Type q) (K : HypercoveringOf.{q, w} J G)
    (I : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})
    [Injective I] (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology.{q, w, v, u} J G K I p) := by
  let J' := J.toGrothendieck
  let _ : HasSheafify J' AddCommGrpCat.{max (max u v) (max q w)} :=
    hasSheafify_addCommGrpCat.{max q w} J'
  let _ : PreservesLimits (forget AddCommGrpCat.{max (max u v) (max q w)}) :=
    AddCommGrpCat.forget_preservesLimits
  have hULift : IsZero (SimplicialObject.sheafHomology J'
      (K.toAugmentedULift.{q, w, v, u} J G).left p) :=
    SimplicialObject.Augmented.isZero_sheafHomology_of_isLocallySurjective_matchingMaps
      J' (K.toAugmentedULift.{q, w, v, u} J G)
      (isLocallySurjective_toAugmentedULift_hom_app_zero.{q, w, v, u} J G K)
      (isLocallySurjective_edgesToFiberProduct_toAugmentedULift.{q, w, v, u} J G K)
      (fun n hn => isLocallySurjective_coskAdj_unit_app_toAugmentedULift.{q, w, v, u}
        J G K n hn) p hp
  let S : ChainComplex (Sheaf J' AddCommGrpCat.{max (max u v) (max q w)}) ℕ :=
    (SimplicialObject.freeAbelianSheafComplexFunctor J').obj
      (associatedSimplicialPresheaf.{max (max u v) (max q w)} K.toSimplicialObject)
  have hS : IsZero (S.homology p) :=
    IsZero.of_iso hULift ((SimplicialObject.sheafHomologyFunctor J' p).mapIso
      (K.toAugmentedULiftLeftIso.{q, w, v, u} J G).symm)
  have hExactOp : S.op.ExactAt p :=
    (HomologicalComplex.exactAt_iff_isZero_homology S.op p).2
      (IsZero.of_iso hS.op (S.homologyOp p))
  let Hom := preadditiveYonedaObj I ⋙ forget₂ (ModuleCat (End I)) AddCommGrpCat
  let U : CochainComplex AddCommGrpCat.{max (max u v) (max q w)} ℕ :=
    (Hom.mapHomologicalComplex (ComplexShape.up ℕ)).obj S.op
  have hU : IsZero (U.homology p) := by
    refine (HomologicalComplex.exactAt_iff_isZero_homology U p).1 ?_
    rw [HomologicalComplex.exactAt_iff]
    rw [HomologicalComplex.exactAt_iff] at hExactOp
    exact (hExactOp.map (preadditiveYonedaObj I)).map
      (forget₂ (ModuleCat (End I)) AddCommGrpCat.{max (max u v) (max q w)})
  let eU : U ≅ SemiRepresentable.homFreeAbelianSheafComplex.{q, w, v, u}
      J' K.toSimplicialObject I := by
    refine HomologicalComplex.Hom.isoOfComponents (fun n => ?_) ?_
    · dsimp [U, Hom, S, SemiRepresentable.homFreeAbelianSheafComplex,
        SimplicialObject.freeAbelianSheafComplexFunctor]
      rfl
    intro i j hij
    simp only [Functor.mapHomologicalComplex_obj_d, HomologicalComplex.unop_d,
      Functor.rightOp_map]
    rfl
  change IsZero ((SemiRepresentable.sectionsComplex.{q, w, v, u}
    J' K.toSimplicialObject I).homology p)
  exact IsZero.of_iso hU ((HomologicalComplex.homologyFunctor AddCommGrpCat
    (ComplexShape.up ℕ) p).mapIso
    ((SemiRepresentable.sectionsComplexIsoHomFreeAbelianSheafComplex.{q, w, v, u}
      J' K.toSimplicialObject I).trans eU.symm))

open ZeroObject in
/-- **Stacks Project, Tag 09VW.** For a hypercovering `K` of a presheaf `G` and an injective
abelian sheaf `I`, the Čech cohomology `Ȟᵖ(K, I)` is the degree-zero cohomology `H⁰(G, I)` of `G`
when `p = 0` and is zero when `p > 0`.

The degree-zero branch is Tag 09VV's `cechCohomologyZeroIso`, which holds for every abelian sheaf
and needs no injectivity; the positive-degree branch is `cechCohomology_isZero_of_injective`. -/
@[stacks 09VW]
noncomputable def cechCohomologyIsoOfInjective (J : Pretopology C)
    (G : Cᵒᵖ ⥤ Type q) (K : HypercoveringOf.{q, w} J G)
    (I : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})
    [Injective I] (p : ℕ) :
    cechCohomology.{q, w, v, u} J G K I p ≅
      if p = 0 then presheafCohomologyZero.{q, w, v, u} J G I else 0 := by
  cases p with
  | zero =>
    exact (cechCohomologyZeroIso.{q, w, v, u} J G K I).trans
      (eqToIso (ite_eq_left rfl).symm)
  | succ n =>
    exact (cechCohomology_isZero_of_injective.{q, w, v, u} J G K I (n + 1)
      (by omega)).isoZero.trans (eqToIso (ite_eq_right (by omega)).symm)

end Stacks.CategoryTheory.Hypercovering

end
