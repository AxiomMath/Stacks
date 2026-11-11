module

public import StacksFrontier.CategoryTheory.Sites.Topos.PushforwardEquality
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Pushforward along a cover-dense functor reflects injections and surjections of sheaves of sets

Let `u : C ⥤ D` be a continuous functor between sites such that every object of `D` is covered by
images of objects of `C`, and let `f_* = u.sheafPushforwardContinuous (Type w) J K`. For a map `α`
of sheaves of sets on `D`, Stacks 00WM calls `α` injective when it is injective on sections over
every object and surjective when every section is locally in the image (Mathlib's
`CategoryTheory.Sheaf.IsLocallySurjective`).

## Main results

* `injective_app_of_injective_sheafPushforwardContinuous_map`: `f_*` reflects injections.
* `isLocallySurjective_of_isLocallySurjective_sheafPushforwardContinuous_map`: `f_*` reflects
  surjections.

The forms for monomorphisms and epimorphisms of sheaves with values in any category are
`sheafPushforwardContinuous_reflectsMonomorphisms_of_isCoverDense` and
`sheafPushforwardContinuous_reflectsEpimorphisms_of_isCoverDense`.

## References

* [Stacks Project, Tag 04D9](https://stacks.math.columbia.edu/tag/04D9)
-/

@[expose] public section

open CategoryTheory Opposite

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D)
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- **Stacks 04D9, injections.** Let `u : C ⥤ D` be a continuous functor between sites such that
every object of `D` is covered by images of objects of `C`. If `α : 𝓕 ⟶ 𝓖` is a map of sheaves of
sets on `D` such that `f_* α` is injective (Stacks 00WM: injective on sections over every object
of `C`), then `α` is injective on sections over every object of `D`. -/
@[stacks 04D9 "f_* reflects injections, in the sense of Stacks 00WM"]
theorem injective_app_of_injective_sheafPushforwardContinuous_map
    [u.IsContinuous J K] [u.IsCoverDense K] {X Y : Sheaf K (Type w)} (α : X ⟶ Y)
    (hα : ∀ U : C, Function.Injective
      (((u.sheafPushforwardContinuous (Type w) J K).map α).hom.app (op U)))
    (V : D) : Function.Injective (α.hom.app (op V)) := by
  intro x y hxy
  have hX := (isSheaf_iff_isSheaf_of_type K X.obj).1 X.property
  refine (hX _ (Functor.IsCoverDense.is_cover (G := u) V)).isSeparatedFor.ext ?_
  rintro W φ ⟨t⟩
  rw [show φ = t.lift ≫ t.map from t.fac.symm, op_comp, Functor.map_comp_apply,
    Functor.map_comp_apply]
  congr 1
  apply hα t.obj
  change α.hom.app (op (u.obj t.obj)) (X.obj.map t.map.op x) =
    α.hom.app (op (u.obj t.obj)) (X.obj.map t.map.op y)
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]

/-- **Stacks 04D9, surjections.** Let `u : C ⥤ D` be a continuous functor between sites such that
every object of `D` is covered by images of objects of `C`. If `α : 𝓕 ⟶ 𝓖` is a map of sheaves of
sets on `D` such that `f_* α` is surjective (Stacks 00WM: every section is locally in the image),
then `α` is surjective. -/
@[stacks 04D9 "f_* reflects surjections, in the sense of Stacks 00WM"]
theorem isLocallySurjective_of_isLocallySurjective_sheafPushforwardContinuous_map
    [u.IsContinuous J K] [u.IsCoverDense K] {X Y : Sheaf K (Type w)} (α : X ⟶ Y)
    (hα : Sheaf.IsLocallySurjective ((u.sheafPushforwardContinuous (Type w) J K).map α)) :
    Sheaf.IsLocallySurjective α := by
  constructor
  intro V s
  apply K.transitive (Functor.IsCoverDense.is_cover (G := u) V)
  rintro W φ ⟨t⟩
  rw [show φ = t.lift ≫ t.map from t.fac.symm, Sieve.pullback_comp]
  apply K.pullback_stable
  have h1 := hα.imageSieve_mem (U := t.obj) (Y.obj.map t.map.op s)
  refine K.superset_covering ?_ ((CoverPreserving.of_isContinuous u J K).cover_preserve h1)
  rintro Z g ⟨Z', g', k, ⟨x, hx⟩, rfl⟩
  refine ⟨X.obj.map k.op x, ?_⟩
  change α.hom.app (op (u.obj Z')) x = Y.obj.map (u.map g').op (Y.obj.map t.map.op s) at hx
  refine (NatTrans.naturality_apply α.hom k.op x).trans ?_
  rw [hx]
  simp only [op_comp, Functor.map_comp_apply]
