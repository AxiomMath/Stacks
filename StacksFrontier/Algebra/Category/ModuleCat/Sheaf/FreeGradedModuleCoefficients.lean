module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModule

/-!
# Functoriality of the free graded module in its coefficients

Let `R` be a sheaf of rings on a site, let `S` be a sheaf of graded sets and let
`X : ℤ → SheafOfModules R` be a graded sheaf of `R`-modules. The free graded module `X[S]` on `S`
with coefficients in `X`, whose degree-`n` piece is the sheafification of

`U ↦ ⨁_{s ∈ S(U), deg s = i} s · X^{n - i}(U)`,

is constructed in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedModule.lean` together
with the free graded `A`-module `A[S]`, which is the case `X = A.piece`. This file makes the
construction functorial in the coefficients, degree by degree: a degreewise morphism `X ⟶ Y`
induces a morphism of the presentations and one of their sheafifications.

## Main definitions

* `SheafOfModules.coeffPresAddHom` is the additive map on the sections of the presentations
  induced by a degreewise morphism of the coefficients, and `SheafOfModules.coeffPresMap` is it
  as a morphism of presheaves of modules.
* `SheafOfModules.coeffPieceMap` is the induced morphism of the degree-`n` pieces of `X[S]` and
  `Y[S]`.

## Main results

* `SheafOfModules.coeffPresMap_id` and `SheafOfModules.coeffPresMap_comp`: the presentation is
  functorial in the coefficients.
* `SheafOfModules.coeffPieceMap_id` and `SheafOfModules.coeffPieceMap_comp`: so is `X[S]`,
  degree by degree.

## Implementation notes

The induced map is defined on the summands and extended additively, so
`SheafOfModules.coeffPresAddHom_coeffOf` is its one computation rule; `R`-linearity and
compatibility with restriction are proved by induction on a section of the presentation. The
morphism of the sheafifications is the image of the morphism of presentations under
`PresheafOfModules.sheafification`, so its functoriality is that of a functor.

## References

* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits DirectSum

universe w t a v u

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

section Functoriality

variable [HasWeakSheafify J (Type w)] (S : SheafOfGradedSets.{w} J)
  {X Y Z : ℤ → SheafOfModules.{a} R}

/-- The morphism of presentations induced by a degreewise morphism of the coefficients. -/
noncomputable def coeffPresAddHom (g : ∀ k : ℤ, X k ⟶ Y k) (n : ℤ) (U : Cᵒᵖ) :
    coeffSections S X n U →+ coeffSections S Y n U :=
  _root_.DirectSum.toAddMonoid fun p =>
    (_root_.DirectSum.of (fun q : S.Index U => ((Y (n - q.1)).val.obj U : Type a))
      p).comp (homSections (g (n - p.1)) U)

/-- The map `coeffPresAddHom S g n U` sends the section `x` in the summand indexed by `s` of
degree `i` to `homSections (g (n - i)) U x` in the same summand. -/
@[simp] theorem coeffPresAddHom_coeffOf (g : ∀ k : ℤ, X k ⟶ Y k) (n : ℤ) (U : Cᵒᵖ) (i : ℤ)
    (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s i) (x : (X (n - i)).val.obj U) :
    coeffPresAddHom S g n U (coeffOf S X n U i s hs x) =
      coeffOf S Y n U i s hs (homSections (g (n - i)) U x) :=
  _root_.DirectSum.toAddMonoid_of _ _ _

/-- The map `coeffPresAddHom S g n U` is `R(U)`-linear. -/
theorem coeffPresAddHom_smul (g : ∀ k : ℤ, X k ⟶ Y k) (n : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U)
    (m : coeffSections S X n U) :
    coeffPresAddHom S g n U (r • m) = r • coeffPresAddHom S g n U m := by
  induction m using coeffSections_induction with
  | hzero => simp
  | hof i s hs x =>
    rw [← coeffOf_smul, coeffPresAddHom_coeffOf, coeffPresAddHom_coeffOf, homSections_smul,
      coeffOf_smul]
  | hadd m m' hm hm' => rw [smul_add, map_add, map_add, hm, hm', smul_add]

/-- The maps `coeffPresAddHom S g n U` commute with restriction along `f : U ⟶ V`. -/
theorem coeffPresAddHom_naturality (g : ∀ k : ℤ, X k ⟶ Y k) (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (m : coeffSections S X n U) :
    coeffPresAddHom S g n V (coeffRestrict S X n f m) =
      coeffRestrict S Y n f (coeffPresAddHom S g n U m) := by
  induction m using coeffSections_induction with
  | hzero => simp
  | hof i s hs x =>
    rw [coeffRestrict_coeffOf, coeffPresAddHom_coeffOf, coeffPresAddHom_coeffOf,
      coeffRestrict_coeffOf]
    exact coeffOf_congr S Y n V i _ _ rfl
      (homSections_naturality (g (n - i)) f x).symm
  | hadd m m' hm hm' => rw [map_add, map_add, map_add, map_add, hm, hm']

/-- The morphism of the presentations of `X[S]` and `Y[S]` induced by a degreewise morphism of
the coefficients. -/
noncomputable def coeffPresMap (g : ∀ k : ℤ, X k ⟶ Y k) (n : ℤ) :
    coeffPres S X n ⟶ coeffPres S Y n :=
  PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (coeffPresAddHom S g n U)
      naturality := fun {U V} f => by
        ext m; exact coeffPresAddHom_naturality S g n f m }
    fun U r m => coeffPresAddHom_smul S g n U r m

/-- On the sections over `U`, `coeffPresMap S g n` is `coeffPresAddHom S g n U`. -/
@[simp] theorem coeffPresMap_app (g : ∀ k : ℤ, X k ⟶ Y k) (n : ℤ) (U : Cᵒᵖ)
    (m : coeffSections S X n U) :
    (coeffPresMap S g n).app U m = coeffPresAddHom S g n U m :=
  rfl

/-- The identity of the coefficients induces the identity of the presentation. -/
theorem coeffPresMap_id (n : ℤ) : coeffPresMap S (fun k => 𝟙 (X k)) n = 𝟙 _ := by
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  show coeffPresAddHom S (fun k => 𝟙 (X k)) n U m = m
  induction m using coeffSections_induction with
  | hzero => simp
  | hof i s hs x => rw [coeffPresAddHom_coeffOf]; rfl
  | hadd m m' hm hm' => rw [map_add, hm, hm']

/-- The morphism of presentations induced by a composite `g ≫ h` of degreewise morphisms is the
composite of the induced morphisms. -/
theorem coeffPresMap_comp (g : ∀ k : ℤ, X k ⟶ Y k) (h : ∀ k : ℤ, Y k ⟶ Z k) (n : ℤ) :
    coeffPresMap S (fun k => g k ≫ h k) n = coeffPresMap S g n ≫ coeffPresMap S h n := by
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  show coeffPresAddHom S (fun k => g k ≫ h k) n U m =
    coeffPresAddHom S h n U (coeffPresAddHom S g n U m)
  induction m using coeffSections_induction with
  | hzero => simp
  | hof i s hs x =>
    rw [coeffPresAddHom_coeffOf, coeffPresAddHom_coeffOf, coeffPresAddHom_coeffOf]
    rfl
  | hadd m m' hm hm' => rw [map_add, map_add, map_add, hm, hm']

end Functoriality

section Sheafify

variable [HasWeakSheafify J (Type w)] [HasWeakSheafify J AddCommGrpCat.{max w a}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w a}] (S : SheafOfGradedSets.{w} J)
  {X Y Z : ℤ → SheafOfModules.{a} R}

/-- The morphism of the degree-`n` pieces of `X[S]` and `Y[S]` induced by a degreewise morphism
of the coefficients. -/
noncomputable def coeffPieceMap (g : ∀ k : ℤ, X k ⟶ Y k) (n : ℤ) :
    coeffPiece S X n ⟶ coeffPiece S Y n :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map (coeffPresMap S g n)

/-- The identity of the coefficients induces the identity of the degree-`n` piece of `X[S]`. -/
theorem coeffPieceMap_id (n : ℤ) : coeffPieceMap S (fun k => 𝟙 (X k)) n = 𝟙 _ := by
  rw [coeffPieceMap, coeffPresMap_id]
  exact (PresheafOfModules.sheafification (𝟙 R.obj)).map_id _

/-- The morphism of degree-`n` pieces induced by a composite `g ≫ h` of degreewise morphisms is
the composite of the induced morphisms. -/
theorem coeffPieceMap_comp (g : ∀ k : ℤ, X k ⟶ Y k) (h : ∀ k : ℤ, Y k ⟶ Z k) (n : ℤ) :
    coeffPieceMap S (fun k => g k ≫ h k) n = coeffPieceMap S g n ≫ coeffPieceMap S h n := by
  rw [coeffPieceMap, coeffPresMap_comp, coeffPieceMap, coeffPieceMap]
  exact (PresheafOfModules.sheafification (𝟙 R.obj)).map_comp _ _

end Sheafify

end SheafOfModules
