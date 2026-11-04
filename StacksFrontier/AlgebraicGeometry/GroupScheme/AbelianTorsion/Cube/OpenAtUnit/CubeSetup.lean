module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.CubeRelation
public import StacksFrontier.AlgebraicGeometry.Cohomology.KunnethLowDegree.DirectImage

/-!
# The cube over an affine neighbourhood of the unit

Let `A` be a group scheme over a field `k`, `P = A × A × A = W × Z` (`W = A × A`, `Z = A`) and
`φ : T ⟶ Z` a morphism with a point `e' : Spec k ⟶ T` over the unit `e` of `Z`. This file
sets up the base change `P' = P ×_Z T` of the third projection, the section `s : W ⟶ P'`
(`w ↦ (w, e')`), the two faces `jᵢ : F ⟶ P'` (`F = (A × A) ×_Z T`, the base changes of the faces
`e × A × A` and `A × e × A`) with their sections `s' : A ⟶ F` (`x ↦ (x, e')`), and the maps
`aᵢ : A ⟶ W` with `aᵢ ≫ s = s' ≫ jᵢ`, and proves the pullback squares that identify `s` and
`s'` as the base changes of `e'`.

## Main definitions

* `Stacks.CubeOpenAtUnit.cubeBase`, `cubeSection`, `cubeFace`, `faceSection`, `faceToW`.

## Main results

* `Stacks.CubeOpenAtUnit.isPullback_cubeSection` and `isPullback_faceSection`.
* `Stacks.CubeOpenAtUnit.faceToW_cubeSection`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.CubeOpenAtUnit

/-! ### Two pullback squares -/

section Squares

variable {C : Type*} [Category* C] [HasPullbacks C] {X Z S T : C} (xh : X ⟶ S) (zh : Z ⟶ S)
  (e : S ⟶ Z) (he : e ≫ zh = 𝟙 S)

/-- `X ⟶ X ×_S Z`, `x ↦ (x, e)`, is the base change of `e : S ⟶ Z` along the projection. -/
theorem isPullback_lift_id :
    IsPullback (pullback.lift (𝟙 X) (xh ≫ e) (by simp [he])) xh (pullback.snd xh zh) e := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback xh zh)
  rw [pullback.lift_fst, he]
  exact IsPullback.id_horiz xh

variable (φ : T ⟶ Z) (e' : S ⟶ T) (he' : e' ≫ φ = e)

include he he' in
/-- `X ⟶ (X ×_S Z) ×_Z T`, `x ↦ (x, e')`, is the base change of `e' : S ⟶ T`. -/
theorem isPullback_lift_lift_id :
    IsPullback (pullback.lift (pullback.lift (𝟙 X) (xh ≫ e) (by simp [he])) (xh ≫ e')
        (by rw [pullback.lift_snd, Category.assoc, he']))
      xh (pullback.snd (pullback.snd xh zh) φ) e' := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback (pullback.snd xh zh) φ)
  rw [pullback.lift_fst, he']
  exact isPullback_lift_id xh zh e he

/-- A section of `(X ×_S Z) ×_Z T ⟶ X` with coordinates `(x, e, e')` is a base change of `e'`. -/
private theorem isPullback_of_comp_eq_lift_lift (he : e ≫ zh = 𝟙 S) (he' : e' ≫ φ = e)
    (s : X ⟶ pullback (pullback.snd xh zh) φ)
    (h₁ : s ≫ pullback.fst _ _ = pullback.lift (𝟙 X) (xh ≫ e) (by simp [he]))
    (h₂ : s ≫ pullback.snd _ _ = xh ≫ e') :
    IsPullback s xh (pullback.snd (pullback.snd xh zh) φ) e' := by
  convert isPullback_lift_lift_id xh zh e he φ e' he' using 1
  exact pullback.hom_ext (h₁.trans (pullback.lift_fst _ _ _).symm)
    (h₂.trans (pullback.lift_snd _ _ _).symm)

end Squares

/-! ### The cube over `T` -/

open Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- The unit `e : Spec k ⟶ A` of the group scheme. -/
abbrev unitPt : Spec (.of k) ⟶ A.left := η[A].left

/-- The unit `e : Spec k ⟶ A` is a section of the structure map `A ⟶ Spec k`. -/
theorem unitPt_hom : unitPt A ≫ A.hom = 𝟙 _ := Over.w η[A]

/-- The underlying morphism of the constant map `1 : B ⟶ A` is `B ⟶ Spec k ⟶ A` via the unit. -/
theorem one_left {B : Over (Spec (.of k))} : (1 : B ⟶ A).left = B.hom ≫ unitPt A := by
  rw [Hom.one_def, Over.comp_left]
  rfl

/-- The face `X ⟶ X × X`, `x ↦ (x, e)`, as a morphism over `k`. -/
abbrev faceRight : A ⟶ A ⊗ A := lift (𝟙 A) 1

/-- The face `X ⟶ X × X`, `x ↦ (e, x)`, as a morphism over `k`. -/
abbrev faceLeft : A ⟶ A ⊗ A := lift 1 (𝟙 A)

/-- The underlying morphism of `faceRight` is `x ↦ (x, e)` into the fibre product over `k`. -/
theorem faceRight_left : (faceRight A).left =
    pullback.lift (𝟙 A.left) (A.hom ≫ unitPt A) (by simp) := by
  apply pullback.hom_ext <;> simp [Over.lift_left, one_left]

/-- The underlying morphism of `faceLeft` is `x ↦ (e, x)` into the fibre product over `k`. -/
theorem faceLeft_left : (faceLeft A).left =
    pullback.lift (A.hom ≫ unitPt A) (𝟙 A.left) (by simp) := by
  apply pullback.hom_ext <;> simp [Over.lift_left, one_left]

/-- The underlying morphism of `cubeFace₃` is `w ↦ (w, e)` into the fibre product over `k`. -/
theorem cubeFace₃_left : (cubeFace₃ A).left =
    pullback.lift (𝟙 (A ⊗ A).left) ((A ⊗ A).hom ≫ unitPt A) (by simp) := by
  apply pullback.hom_ext
  · simp only [cubeFace₃, Over.lift_left, pullback.lift_fst, lift_fst_snd, Over.id_left]
  · simp [cubeFace₃, Over.lift_left, one_left]

/-- Both composites are the map `x ↦ (e, x, e)` of `A` into `A × A × A`. -/
theorem faceLeft_cubeFace₃ : faceLeft A ≫ cubeFace₃ A = faceRight A ≫ cubeFace₁ A := by
  ext <;> simp [cubeFace₁, cubeFace₃]

/-- Both composites are the map `x ↦ (x, e, e)` of `A` into `A × A × A`. -/
theorem faceRight_cubeFace₃ : faceRight A ≫ cubeFace₃ A = faceRight A ≫ cubeFace₂ A := by
  ext <;> simp [cubeFace₂, cubeFace₃]

variable {T : Scheme.{u}} (φ : T ⟶ A.left) (e' : Spec (.of k) ⟶ T)

/-- `P' = (A × A × A) ×_A T`, the cube over `T` along the third projection. -/
abbrev cubeT : Scheme.{u} := pullback (cubeProj₃ A).left φ

/-- The structure map `P' ⟶ T`. -/
abbrev cubeBase : cubeT A φ ⟶ T := pullback.snd _ _

/-- `P' ⟶ A × A × A`. -/
abbrev cubeFst : cubeT A φ ⟶ (cubeObj A).left := pullback.fst _ _

variable {e'} (he' : e' ≫ φ = unitPt A)

include he' in
/-- The face `w ↦ (w, e)` followed by the third projection equals `A × A ⟶ Spec k ⟶ T ⟶ A`. -/
theorem cubeFace₃_comm :
    (cubeFace₃ A).left ≫ (cubeProj₃ A).left = ((A ⊗ A).hom ≫ e') ≫ φ := by
  rw [Category.assoc, he', ← one_left, ← Over.comp_left, cubeFace₃_cubeProj₃]

/-- The section `s : A × A ⟶ P'`, `w ↦ (w, e', e')`. -/
def cubeSection : (A ⊗ A).left ⟶ cubeT A φ :=
  pullback.lift (cubeFace₃ A).left ((A ⊗ A).hom ≫ e') (cubeFace₃_comm A φ he')

/-- The section `s` followed by `P' ⟶ A × A × A` is the face `w ↦ (w, e)`. -/
@[reassoc (attr := simp)]
theorem cubeSection_fst : cubeSection A φ he' ≫ cubeFst A φ = (cubeFace₃ A).left :=
  pullback.lift_fst _ _ _

/-- The section `s` followed by `P' ⟶ T` is the constant map `A × A ⟶ Spec k ⟶ T` at `e'`. -/
@[reassoc (attr := simp)]
theorem cubeSection_base : cubeSection A φ he' ≫ cubeBase A φ = (A ⊗ A).hom ≫ e' :=
  pullback.lift_snd _ _ _

/-- **`s` is the base change of `e' : Spec k ⟶ T` along `P' ⟶ T`.** -/
theorem isPullback_cubeSection :
    IsPullback (cubeSection A φ he') (A ⊗ A).hom (cubeBase A φ) e' := by
  refine isPullback_of_comp_eq_lift_lift (A ⊗ A).hom A.hom (unitPt A) φ e' (unitPt_hom A) he' _
    ?_ (cubeSection_base A φ he')
  rw [← cubeFace₃_left A]
  exact cubeSection_fst A φ he'

/-- The faces `e × A × A` (`i = 0`) and `A × e × A` (`i = 1`) of the cube. -/
def faceOf (i : Fin 2) : A ⊗ A ⟶ cubeObj A := ![cubeFace₁ A, cubeFace₂ A] i

/-- Each face followed by the third projection of the cube is the second projection. -/
theorem faceOf_cubeProj₃ (i : Fin 2) : faceOf A i ≫ cubeProj₃ A = snd A A := by
  fin_cases i <;> simp [faceOf]

/-- The face scheme `F = (A × A) ×_A T` over `T`, along the second projection. -/
abbrev faceT : Scheme.{u} := pullback (snd A A).left φ

/-- The structure map `F ⟶ T`. -/
abbrev faceBase : faceT A φ ⟶ T := pullback.snd _ _

/-- The face `jᵢ : F ⟶ P'`. -/
def cubeFace (i : Fin 2) : faceT A φ ⟶ cubeT A φ :=
  pullback.map _ _ _ _ (faceOf A i).left (𝟙 T) (𝟙 A.left)
    (by rw [Category.comp_id, ← Over.comp_left, faceOf_cubeProj₃]) (by simp)

/-- The face `jᵢ` commutes with the structure maps `F ⟶ T` and `P' ⟶ T`. -/
@[reassoc (attr := simp)]
theorem cubeFace_base (i : Fin 2) : cubeFace A φ i ≫ cubeBase A φ = faceBase A φ := by
  unfold cubeFace
  rw [pullback.lift_snd, Category.comp_id]

/-- The face `jᵢ` followed by `P' ⟶ A × A × A` is `F ⟶ A × A` followed by the face `faceOf i`. -/
@[reassoc (attr := simp)]
theorem cubeFace_fst (i : Fin 2) :
    cubeFace A φ i ≫ cubeFst A φ = pullback.fst _ _ ≫ (faceOf A i).left := by
  unfold cubeFace
  rw [pullback.lift_fst]

/-- **The face `jᵢ` is the base change of the face `A × A ⟶ A × A × A`.** -/
theorem isPullback_cubeFace (i : Fin 2) :
    IsPullback (cubeFace A φ i) (pullback.fst _ _) (cubeFst A φ) (faceOf A i).left := by
  refine IsPullback.of_right (h₁₂ := cubeBase A φ) (v₁₃ := φ) (h₂₂ := (cubeProj₃ A).left) ?_
    (cubeFace_fst A φ i) (IsPullback.of_hasPullback (cubeProj₃ A).left φ).flip
  rw [cubeFace_base, ← Over.comp_left, faceOf_cubeProj₃]
  exact (IsPullback.of_hasPullback (snd A A).left φ).flip

/-- The section `s' : A ⟶ F`, `x ↦ (x, e, e')`. -/
def faceSection : A.left ⟶ faceT A φ :=
  pullback.lift (faceRight A).left (A.hom ≫ e')
    (by rw [Category.assoc, he', ← one_left, ← Over.comp_left]; simp)

/-- The section `s'` followed by `F ⟶ A × A` is `x ↦ (x, e)`. -/
@[reassoc (attr := simp)]
theorem faceSection_fst : faceSection A φ he' ≫ pullback.fst _ _ = (faceRight A).left :=
  pullback.lift_fst _ _ _

/-- The section `s'` followed by `F ⟶ T` is the constant map `A ⟶ Spec k ⟶ T` at `e'`. -/
@[reassoc (attr := simp)]
theorem faceSection_base : faceSection A φ he' ≫ faceBase A φ = A.hom ≫ e' :=
  pullback.lift_snd _ _ _

/-- **`s'` is the base change of `e'` along `F ⟶ T`.** -/
theorem isPullback_faceSection :
    IsPullback (faceSection A φ he') A.hom (faceBase A φ) e' := by
  refine isPullback_of_comp_eq_lift_lift A.hom A.hom (unitPt A) φ e' (unitPt_hom A) he' _
    ?_ (faceSection_base A φ he')
  rw [← faceRight_left A]
  exact faceSection_fst A φ he'

/-- The maps `aᵢ : A ⟶ A × A`: `x ↦ (e, x)` for the face `e × A × A` and `x ↦ (x, e)` for the
face `A × e × A`. -/
def faceToW (i : Fin 2) : A ⟶ A ⊗ A := ![faceLeft A, faceRight A] i

/-- **`aᵢ ≫ s = s' ≫ jᵢ`.** -/
theorem faceToW_cubeSection (i : Fin 2) :
    (faceToW A i).left ≫ cubeSection A φ he' = faceSection A φ he' ≫ cubeFace A φ i := by
  apply pullback.hom_ext
  · rw [Category.assoc, cubeSection_fst, Category.assoc, cubeFace_fst, faceSection_fst_assoc,
      ← Over.comp_left, ← Over.comp_left]
    fin_cases i
    · exact congrArg Over.Hom.left (faceLeft_cubeFace₃ A)
    · exact congrArg Over.Hom.left (faceRight_cubeFace₃ A)
  · rw [Category.assoc, cubeSection_base, Category.assoc, cubeFace_base, faceSection_base,
      ← Category.assoc]
    congr 1
    exact Over.w (faceToW A i)

/-! ### Morphism properties -/

/-- The retraction of the face `faceOf i`, forgetting the coordinate set to `e`. -/
def faceRetract (i : Fin 2) : cubeObj A ⟶ A ⊗ A :=
  ![lift (cubeProj₂ A) (cubeProj₃ A), lift (cubeProj₁ A) (cubeProj₃ A)] i

/-- `faceRetract i` is a retraction of the face `faceOf i`. -/
theorem faceOf_faceRetract (i : Fin 2) : faceOf A i ≫ faceRetract A i = 𝟙 _ := by
  fin_cases i <;> ext <;> simp [faceOf, faceRetract]

/-- If `A` is separated over `k`, then so is `A × A`. -/
instance isSeparated_tensorObj_hom [IsSeparated A.hom] : IsSeparated (A ⊗ A).hom := by
  change IsSeparated (pullback.fst A.hom A.hom ≫ A.hom)
  infer_instance

/-- If `A` is separated over `k`, then so is `A × A × A`. -/
instance isSeparated_cubeObj_hom [IsSeparated A.hom] : IsSeparated (cubeObj A).hom := by
  change IsSeparated (pullback.fst (A ⊗ A).hom A.hom ≫ (A ⊗ A).hom)
  infer_instance

/-- If `A` is separated over `k`, each face `A × A ⟶ A × A × A` is a closed immersion. -/
instance isClosedImmersion_faceOf [IsSeparated A.hom] (i : Fin 2) :
    IsClosedImmersion (faceOf A i).left := by
  have : IsSeparated ((faceRetract A i).left ≫ (A ⊗ A).hom) := by
    rw [Over.w]
    infer_instance
  have : IsSeparated (faceRetract A i).left := IsSeparated.of_comp _ (A ⊗ A).hom
  have : IsClosedImmersion ((faceOf A i).left ≫ (faceRetract A i).left) := by
    rw [← Over.comp_left, faceOf_faceRetract, Over.id_left]
    infer_instance
  exact IsClosedImmersion.of_comp _ (faceRetract A i).left

/-- If `A` is separated over `k`, each face `jᵢ : F ⟶ P'` is a closed immersion. -/
instance isClosedImmersion_cubeFace [IsSeparated A.hom] (i : Fin 2) :
    IsClosedImmersion (cubeFace A φ i) :=
  MorphismProperty.of_isPullback (isPullback_cubeFace A φ i).flip inferInstance

/-- `A × A` is flat over `k`. -/
instance flat_tensorObj_hom : Flat (A ⊗ A).hom := Stacks.KunnethLowDegree.flat_of_spec_field _

/-- The third projection `A × A × A ⟶ A` is flat. -/
instance flat_cubeProj₃ : Flat (cubeProj₃ A).left := by
  change Flat (pullback.snd (A ⊗ A).hom A.hom)
  infer_instance

/-- The structure map `P' ⟶ T` is flat. -/
instance flat_cubeBase : Flat (cubeBase A φ) := by
  change Flat (pullback.snd (cubeProj₃ A).left φ)
  infer_instance

/-- The structure map `F ⟶ T` is flat. -/
instance flat_faceBase : Flat (faceBase A φ) := by
  have : Flat A.hom := Stacks.KunnethLowDegree.flat_of_spec_field _
  change Flat (pullback.snd (pullback.snd A.hom A.hom) φ)
  infer_instance

/-- If `A` is proper over `k`, the structure map `P' ⟶ T` is proper. -/
instance isProper_cubeBase [IsProper A.hom] : IsProper (cubeBase A φ) := by
  have : IsProper (A ⊗ A).hom := by
    change IsProper (pullback.fst A.hom A.hom ≫ A.hom)
    infer_instance
  have : IsProper (cubeProj₃ A).left := by
    change IsProper (pullback.snd (A ⊗ A).hom A.hom)
    infer_instance
  change IsProper (pullback.snd (cubeProj₃ A).left φ)
  infer_instance

omit [GrpObj A] in
/-- **The face scheme is `A ×_k T`.** -/
theorem isPullback_faceT :
    IsPullback (pullback.fst _ _ ≫ pullback.fst A.hom A.hom) (faceBase A φ) A.hom (φ ≫ A.hom) :=
  IsPullback.paste_horiz (IsPullback.of_hasPullback (pullback.snd A.hom A.hom) φ)
    (IsPullback.of_hasPullback A.hom A.hom)

end Stacks.CubeOpenAtUnit

end
