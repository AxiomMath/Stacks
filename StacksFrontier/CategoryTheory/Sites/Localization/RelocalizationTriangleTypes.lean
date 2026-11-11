module

public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizationTriangle
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Relocalization for sheaves of sets (Stacks 03EH)

Let `(C, J)` be a site and `f : V ⟶ U` a morphism of `C`. Stacks 03EH states that the
localization functors `j_V : C/V ⥤ C`, `j_U : C/U ⥤ C` and the relocalization functor
`j = Over.map f : C/V ⥤ C/U` form a commutative triangle of continuous and cocontinuous functors,
that `j` is the localization functor `j_{V/U}` under `(C/U)/(V/U) = C/V`, and that on sheaves of
sets `j_{V!} = j_{U!} ∘ j_!`, `j_V^{-1} = j^{-1} ∘ j_U^{-1}` and `j_{V*} = j_{U*} ∘ j_*`.

The pieces are proved in `StacksFrontier.CategoryTheory.Sites.Localization.RelocalizationTriangle`
for sheaves with values in any category `A` admitting the adjoints involved. Here `A` is the
category `Type (max u v)` of sets of a site `C : Type u` with `Category.{v} C`; for it every lower
shriek `j_!` (a left adjoint of `sheafPushforwardContinuous`, built from a left Kan extension and
sheafification) and every direct image `j_*` (`sheafPushforwardCocontinuous`, a right Kan
extension) exists, so the statement below carries no hypothesis beyond those of Stacks.
-/

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {U V : C} (f : V ⟶ U)

/-- **Stacks 03EH.** For a morphism `f : V ⟶ U` of a site `(C, J)`:
* the triangle `j_U ∘ j = j_V` of `j = Over.map f`, `j_U = Over.forget U`, `j_V = Over.forget V`
  commutes (`comp_forget_eq_forget`);
* the three functors are continuous and cocontinuous for the localized topologies;
* under the identification `(C/U)/(V/U) ≌ C/V` (`Over.iteratedSliceEquiv`), `j` is the
  localization functor `j_{V/U} = Over.forget (V/U)` (`map_eq_forget_iteratedSlice`);
* on sheaves of sets, `j_V^{-1} = j^{-1} ∘ j_U^{-1}` strictly (`inverseImage_eq`),
  `j_{V!} ≅ j_{U!} ∘ j_!` (`leftAdjointIso`) and `j_{V*} ≅ j_{U*} ∘ j_*` (`rightAdjointIso`),
  the last two being the canonical isomorphisms between adjoints of the same functor. -/
@[stacks 03EH]
theorem relocalization_triangle_sheaf_types :
    Over.map f ⋙ Over.forget U = Over.forget V ∧
      ((Over.forget V).IsContinuous (J.over V) J ∧ (Over.forget V).IsCocontinuous (J.over V) J) ∧
      ((Over.forget U).IsContinuous (J.over U) J ∧ (Over.forget U).IsCocontinuous (J.over U) J) ∧
      ((Over.map f).IsContinuous (J.over V) (J.over U) ∧
        (Over.map f).IsCocontinuous (J.over V) (J.over U)) ∧
      (Over.iteratedSliceEquiv (Over.mk f)).functor ⋙ Over.map f = Over.forget (Over.mk f) ∧
      Nonempty ((Over.forget V).sheafPullback (Type max u v) (J.over V) J ≅
        (Over.map f).sheafPullback (Type max u v) (J.over V) (J.over U) ⋙
          (Over.forget U).sheafPullback (Type max u v) (J.over U) J) ∧
      (Over.forget V).sheafPushforwardContinuous (Type max u v) (J.over V) J =
        (Over.forget U).sheafPushforwardContinuous (Type max u v) (J.over U) J ⋙
          (Over.map f).sheafPushforwardContinuous (Type max u v) (J.over V) (J.over U) ∧
      Nonempty ((Over.forget V).sheafPushforwardCocontinuous (Type max u v) (J.over V) J ≅
        (Over.map f).sheafPushforwardCocontinuous (Type max u v) (J.over V) (J.over U) ⋙
          (Over.forget U).sheafPushforwardCocontinuous (Type max u v) (J.over U) J) :=
  ⟨comp_forget_eq_forget f, ⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩,
    ⟨map_isContinuous J f, map_isCocontinuous J f⟩, map_eq_forget_iteratedSlice f,
    ⟨leftAdjointIso J f _⟩, inverseImage_eq J f _, ⟨rightAdjointIso J f _⟩⟩
