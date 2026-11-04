module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Pullback
public import StacksFrontier.AlgebraicGeometry.PicardUFD.Affine
public import StacksCore.Tactic.StacksAttribute

/-!
# The cube relation for an invertible module on an abelian variety

Let `A` be an abelian variety over a field `k` and let `L` be an invertible `𝒪_A`-module. Write
`m_I : A × A × A ⟶ A` for the sum of the coordinates indexed by a nonempty `I ⊆ {1, 2, 3}`.
Assuming the theorem of the cube for `A × A × A`,

`m₁₂₃^*L ⊗ m₁^*L ⊗ m₂^*L ⊗ m₃^*L ≅ m₁₂^*L ⊗ m₁₃^*L ⊗ m₂₃^*L`

as invertible modules on `A × A × A`.

## Main definitions

* `Stacks.Groupoids.cubeObj`: the triple product `A × A × A` over the ground field.
* `Stacks.Groupoids.cubeProj₁`, `cubeProj₂`, `cubeProj₃`: its three coordinates. The coordinate
  sum `m_I` is the product of the coordinates indexed by `I` in the group `A × A × A ⟶ A`.
* `Stacks.Groupoids.cubeFace₁`, `cubeFace₂`, `cubeFace₃`: the three faces
  `e × A × A`, `A × e × A` and `A × A × e`.
* `Stacks.Groupoids.pullbackOver`: pullback of a module along a morphism of schemes over `k`.
* `Stacks.Groupoids.HasTheoremOfTheCube`: the theorem of the cube for `A × A × A`.
* `Stacks.Groupoids.cubeModule`: the invertible module whose triviality is the cube relation.

## Main results

* `Stacks.Groupoids.nonempty_cubeRelation`: the cube relation, assuming
  `HasTheoremOfTheCube A`.

## Implementation notes

The argument runs in the Picard group of `A × A × A`: two invertible modules are isomorphic
exactly when their Picard classes agree (`Stacks.SheafOfModules.picardClass_eq_iff`), and the
restriction of a coordinate sum to a face is computed in the group `A × A ⟶ A` of morphisms into
the group object (`CategoryTheory.MonObj.comp_mul`).

## References

* [Stacks Project, Tag 0BFE](https://stacks.math.columbia.edu/tag/0BFE)
* [Stacks Project, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 03RO](https://stacks.math.columbia.edu/tag/03RO)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open RingedSpaceModuleAdjunction TopologicalSpace
open Stacks.SheafOfModules (schemeTensor picardClass pullbackPicardClass)
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-! ### The triple product, its coordinates and its faces -/

/-- `A × A × A`, the triple product of a group scheme over `k` with itself over `k`. -/
noncomputable abbrev cubeObj : Over (Spec (.of k)) := (A ⊗ A) ⊗ A

/-- The first coordinate `(x₁, x₂, x₃) ↦ x₁` of `A × A × A`. -/
noncomputable def cubeProj₁ : cubeObj A ⟶ A := fst (A ⊗ A) A ≫ fst A A

/-- The second coordinate `(x₁, x₂, x₃) ↦ x₂` of `A × A × A`. -/
noncomputable def cubeProj₂ : cubeObj A ⟶ A := fst (A ⊗ A) A ≫ snd A A

/-- The third coordinate `(x₁, x₂, x₃) ↦ x₃` of `A × A × A`. -/
noncomputable def cubeProj₃ : cubeObj A ⟶ A := snd (A ⊗ A) A

/-- The face `e × A × A`, that is `(x₂, x₃) ↦ (e, x₂, x₃)`. -/
noncomputable def cubeFace₁ : A ⊗ A ⟶ cubeObj A := lift (lift 1 (fst A A)) (snd A A)

/-- The face `A × e × A`, that is `(x₁, x₃) ↦ (x₁, e, x₃)`. -/
noncomputable def cubeFace₂ : A ⊗ A ⟶ cubeObj A := lift (lift (fst A A) 1) (snd A A)

/-- The face `A × A × e`, that is `(x₁, x₂) ↦ (x₁, x₂, e)`. -/
noncomputable def cubeFace₃ : A ⊗ A ⟶ cubeObj A := lift (lift (fst A A) (snd A A)) 1

/-- The first coordinate of the face `e × A × A` is `e`. -/
@[simp] theorem cubeFace₁_cubeProj₁ : cubeFace₁ A ≫ cubeProj₁ A = 1 := by
  simp [cubeFace₁, cubeProj₁]

/-- The second coordinate of the face `e × A × A` is the first projection. -/
@[simp] theorem cubeFace₁_cubeProj₂ : cubeFace₁ A ≫ cubeProj₂ A = fst A A := by
  simp [cubeFace₁, cubeProj₂]

/-- The third coordinate of the face `e × A × A` is the second projection. -/
@[simp] theorem cubeFace₁_cubeProj₃ : cubeFace₁ A ≫ cubeProj₃ A = snd A A := by
  simp [cubeFace₁, cubeProj₃]

/-- The first coordinate of the face `A × e × A` is the first projection. -/
@[simp] theorem cubeFace₂_cubeProj₁ : cubeFace₂ A ≫ cubeProj₁ A = fst A A := by
  simp [cubeFace₂, cubeProj₁]

/-- The second coordinate of the face `A × e × A` is `e`. -/
@[simp] theorem cubeFace₂_cubeProj₂ : cubeFace₂ A ≫ cubeProj₂ A = 1 := by
  simp [cubeFace₂, cubeProj₂]

/-- The third coordinate of the face `A × e × A` is the second projection. -/
@[simp] theorem cubeFace₂_cubeProj₃ : cubeFace₂ A ≫ cubeProj₃ A = snd A A := by
  simp [cubeFace₂, cubeProj₃]

/-- The first coordinate of the face `A × A × e` is the first projection. -/
@[simp] theorem cubeFace₃_cubeProj₁ : cubeFace₃ A ≫ cubeProj₁ A = fst A A := by
  simp [cubeFace₃, cubeProj₁]

/-- The second coordinate of the face `A × A × e` is the second projection. -/
@[simp] theorem cubeFace₃_cubeProj₂ : cubeFace₃ A ≫ cubeProj₂ A = snd A A := by
  simp [cubeFace₃, cubeProj₂]

/-- The third coordinate of the face `A × A × e` is `e`. -/
@[simp] theorem cubeFace₃_cubeProj₃ : cubeFace₃ A ≫ cubeProj₃ A = 1 := by
  simp [cubeFace₃, cubeProj₃]

/-! ### Pullbacks of modules along morphisms over the ground field -/

variable {A}

/-- The pullback of a sheaf of modules along a morphism of schemes over the ground field. -/
noncomputable abbrev pullbackOver {B C : Over (Spec (.of k))} (f : B ⟶ C)
    (L : SheafOfModules.{u} (structureSheafRing C.left.toRingedSpace)) :
    SheafOfModules.{u} (structureSheafRing B.left.toRingedSpace) :=
  (modulePullback f.left.toLRSHom.toShHom).obj L

/-- The pullback of an invertible module is invertible. -/
theorem isInvertible_pullbackOver {B C : Over (Spec (.of k))} (f : B ⟶ C)
    (L : SheafOfModules.{u} (structureSheafRing C.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible C.left.presheaf C.left.ringCatIsSheaf L) :
    Stacks.SheafOfModules.IsInvertible B.left.presheaf B.left.ringCatIsSheaf
      (pullbackOver f L) :=
  have := hL
  Stacks.RingedSpace.modulePullback_isInvertible _ L

/-- The pullback class of an invertible module along the constant morphism `1 : B ⟶ A` to the
identity section vanishes. -/
theorem pullbackPicardClass_one {A : Over (Spec (.of k))} [GrpObj A]
    {B : Over (Spec (.of k))}
    (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L) :
    pullbackPicardClass (1 : B ⟶ A).left L hL = 0 := by
  have hη := isInvertible_pullbackOver (η[A] : 𝟙_ (Over (Spec (.of k))) ⟶ A) L hL
  have hηtriv : Stacks.SheafOfModules.IsTrivial
      (𝟙_ (Over (Spec (.of k)))).left.presheaf (𝟙_ (Over (Spec (.of k)))).left.ringCatIsSheaf
      (pullbackOver (η[A] : 𝟙_ (Over (Spec (.of k))) ⟶ A) L) :=
    have := hη
    Stacks.PicardUFD.isTrivial_of_isInvertible_spec k _
  rw [Stacks.SheafOfModules.pullbackPicardClass_eq_zero_iff]
  exact ⟨(RingedSpaceModuleAdjunction.modulePullbackComp
      (toUnit B : B ⟶ 𝟙_ (Over (Spec (.of k)))).left.toLRSHom.toShHom
      (η[A] : 𝟙_ (Over (Spec (.of k))) ⟶ A).left.toLRSHom.toShHom).app L ≪≫
    (modulePullback (toUnit B : B ⟶ 𝟙_ (Over (Spec (.of k)))).left.toLRSHom.toShHom).mapIso
      hηtriv.some ≪≫
    modulePullbackObjUnitIso
      (toUnit B : B ⟶ 𝟙_ (Over (Spec (.of k)))).left.toLRSHom.toShHom⟩

/-! ### The module of the theorem of the cube -/

variable (A)

/-- The theorem of the cube for the triple self-product of `A`: an invertible module on
`A × A × A` whose pullbacks along the three faces `e × A × A`, `A × e × A` and `A × A × e` are
trivial is itself trivial. -/
def HasTheoremOfTheCube : Prop :=
  ∀ N : SheafOfModules.{u} (structureSheafRing (cubeObj A).left.toRingedSpace),
    Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
        (cubeObj A).left.ringCatIsSheaf N →
      Stacks.SheafOfModules.IsTrivial (A ⊗ A).left.presheaf (A ⊗ A).left.ringCatIsSheaf
        (pullbackOver (cubeFace₁ A) N) →
      Stacks.SheafOfModules.IsTrivial (A ⊗ A).left.presheaf (A ⊗ A).left.ringCatIsSheaf
        (pullbackOver (cubeFace₂ A) N) →
      Stacks.SheafOfModules.IsTrivial (A ⊗ A).left.presheaf (A ⊗ A).left.ringCatIsSheaf
        (pullbackOver (cubeFace₃ A) N) →
      Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
        (cubeObj A).left.ringCatIsSheaf N

/-- The module on `A × A × A` whose triviality is the cube relation: the tensor product of the
pullbacks of `L` along the four coordinate sums `m₁₂₃`, `m₁`, `m₂`, `m₃` with the given tensor
inverses `N₁₂`, `N₁₃`, `N₂₃` of the pullbacks along `m₁₂`, `m₁₃`, `m₂₃`. -/
noncomputable def cubeModule
    (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (N₁₂ N₁₃ N₂₃ : SheafOfModules.{u} (structureSheafRing (cubeObj A).left.toRingedSpace)) :
    SheafOfModules.{u} (structureSheafRing (cubeObj A).left.toRingedSpace) :=
  schemeTensor (cubeObj A).left
    (schemeTensor (cubeObj A).left
      (schemeTensor (cubeObj A).left
        (schemeTensor (cubeObj A).left
          (pullbackOver (cubeProj₁ A * cubeProj₂ A * cubeProj₃ A) L)
          (pullbackOver (cubeProj₁ A) L))
        (pullbackOver (cubeProj₂ A) L))
      (pullbackOver (cubeProj₃ A) L))
    (schemeTensor (cubeObj A).left (schemeTensor (cubeObj A).left N₁₂ N₁₃) N₂₃)

/-- The cube module is invertible. -/
theorem isInvertible_cubeModule
    (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L)
    (N₁₂ N₁₃ N₂₃ : SheafOfModules.{u} (structureSheafRing (cubeObj A).left.toRingedSpace))
    (h₁₂ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₂)
    (h₁₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₃)
    (h₂₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₂₃) :
    Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf (cubeObj A).left.ringCatIsSheaf
      (cubeModule A L N₁₂ N₁₃ N₂₃) :=
  Stacks.SheafOfModules.isInvertible_schemeTensor (cubeObj A).left _ _
    (Stacks.SheafOfModules.isInvertible_schemeTensor₄ (cubeObj A).left _ _ _ _
      (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₂ A * cubeProj₃ A) L hL)
      (isInvertible_pullbackOver (cubeProj₁ A) L hL)
      (isInvertible_pullbackOver (cubeProj₂ A) L hL)
      (isInvertible_pullbackOver (cubeProj₃ A) L hL))
    (Stacks.SheafOfModules.isInvertible_schemeTensor₃ (cubeObj A).left _ _ _ h₁₂ h₁₃ h₂₃)

/-- The Picard class of the cube module, expanded into the classes of its seven factors. -/
theorem picardClass_cubeModule
    (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L)
    (N₁₂ N₁₃ N₂₃ : SheafOfModules.{u} (structureSheafRing (cubeObj A).left.toRingedSpace))
    (h₁₂ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₂)
    (h₁₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₃)
    (h₂₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₂₃) :
    picardClass (cubeObj A).left.presheaf (cubeObj A).left.ringCatIsSheaf
        (cubeModule A L N₁₂ N₁₃ N₂₃) (isInvertible_cubeModule A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃) =
      (picardClass (cubeObj A).left.presheaf (cubeObj A).left.ringCatIsSheaf
            (pullbackOver (cubeProj₁ A * cubeProj₂ A * cubeProj₃ A) L)
            (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₂ A * cubeProj₃ A) L hL) +
          picardClass (cubeObj A).left.presheaf (cubeObj A).left.ringCatIsSheaf
            (pullbackOver (cubeProj₁ A) L) (isInvertible_pullbackOver (cubeProj₁ A) L hL) +
          picardClass (cubeObj A).left.presheaf (cubeObj A).left.ringCatIsSheaf
            (pullbackOver (cubeProj₂ A) L) (isInvertible_pullbackOver (cubeProj₂ A) L hL) +
          picardClass (cubeObj A).left.presheaf (cubeObj A).left.ringCatIsSheaf
            (pullbackOver (cubeProj₃ A) L) (isInvertible_pullbackOver (cubeProj₃ A) L hL)) +
        (picardClass (cubeObj A).left.presheaf (cubeObj A).left.ringCatIsSheaf N₁₂ h₁₂ +
          picardClass (cubeObj A).left.presheaf (cubeObj A).left.ringCatIsSheaf N₁₃ h₁₃ +
          picardClass (cubeObj A).left.presheaf (cubeObj A).left.ringCatIsSheaf N₂₃ h₂₃) := by
  rw [← Stacks.SheafOfModules.picardClass_schemeTensor₄,
    ← Stacks.SheafOfModules.picardClass_schemeTensor₃]
  exact Stacks.SheafOfModules.picardClass_schemeTensor _ _ _ _ _

/-- The pullback class of the cube module along a morphism `φ` into `A × A × A`, expanded into
the classes of the pullbacks of `L` along the four coordinate sums composed with `φ` and
pullback classes of the three tensor inverses. -/
theorem pullbackPicardClass_cubeModule
    (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L)
    (N₁₂ N₁₃ N₂₃ : SheafOfModules.{u} (structureSheafRing (cubeObj A).left.toRingedSpace))
    (h₁₂ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₂)
    (h₁₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₃)
    (h₂₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₂₃)
    {B : Over (Spec (.of k))} (φ : B ⟶ cubeObj A) :
    pullbackPicardClass φ.left (cubeModule A L N₁₂ N₁₃ N₂₃)
        (isInvertible_cubeModule A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃) =
      (pullbackPicardClass (φ ≫ (cubeProj₁ A * cubeProj₂ A * cubeProj₃ A)).left L hL +
          pullbackPicardClass (φ ≫ cubeProj₁ A).left L hL +
          pullbackPicardClass (φ ≫ cubeProj₂ A).left L hL +
          pullbackPicardClass (φ ≫ cubeProj₃ A).left L hL) +
        (pullbackPicardClass φ.left N₁₂ h₁₂ + pullbackPicardClass φ.left N₁₃ h₁₃ +
          pullbackPicardClass φ.left N₂₃ h₂₃) := by
  simp only [Over.comp_left]
  rw [Stacks.SheafOfModules.pullbackPicardClass_comp φ.left _ L hL
      (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₂ A * cubeProj₃ A) L hL),
    Stacks.SheafOfModules.pullbackPicardClass_comp φ.left _ L hL
      (isInvertible_pullbackOver (cubeProj₁ A) L hL),
    Stacks.SheafOfModules.pullbackPicardClass_comp φ.left _ L hL
      (isInvertible_pullbackOver (cubeProj₂ A) L hL),
    Stacks.SheafOfModules.pullbackPicardClass_comp φ.left _ L hL
      (isInvertible_pullbackOver (cubeProj₃ A) L hL),
    ← Stacks.SheafOfModules.pullbackPicardClass_schemeTensor₄,
    ← Stacks.SheafOfModules.pullbackPicardClass_schemeTensor₃]
  exact Stacks.SheafOfModules.pullbackPicardClass_schemeTensor _ _ _ _ _

/-! ### The three faces -/

/-- If `L` pulled back along `m` tensored with `N` is trivial, then the class of `N` is the negative
of the class of the pullback of `L` along `m`. -/
private theorem picardClass_eq_neg_pullbackOver
    (A : Over (Spec (.of k))) (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L)
    (m : cubeObj A ⟶ A)
    (N : SheafOfModules.{u} (structureSheafRing (cubeObj A).left.toRingedSpace))
    (h : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N)
    (t : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left (pullbackOver m L) N)) :
    picardClass (cubeObj A).left.presheaf (cubeObj A).left.ringCatIsSheaf N h =
      -picardClass (cubeObj A).left.presheaf (cubeObj A).left.ringCatIsSheaf
        (pullbackOver m L) (isInvertible_pullbackOver m L hL) :=
  Stacks.SheafOfModules.picardClass_eq_neg_of_isTrivial_tensorSheaf (cubeObj A).left
    (pullbackOver m L) N (isInvertible_pullbackOver m L hL) h
    (Stacks.SheafOfModules.isInvertible_schemeTensor (cubeObj A).left _ _
      (isInvertible_pullbackOver m L hL) h) t

/-- The pullback-class version of `picardClass_eq_neg_pullbackOver`. -/
private theorem pullbackPicardClass_eq_neg_pullbackOver
    (A : Over (Spec (.of k))) (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L)
    (m : cubeObj A ⟶ A)
    (N : SheafOfModules.{u} (structureSheafRing (cubeObj A).left.toRingedSpace))
    (h : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N)
    (t : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left (pullbackOver m L) N))
    {B : Over (Spec (.of k))} (φ : B ⟶ cubeObj A) :
    pullbackPicardClass φ.left N h = -pullbackPicardClass (φ ≫ m).left L hL := by
  rw [Over.comp_left, Stacks.SheafOfModules.pullbackPicardClass_comp φ.left m.left L hL
    (isInvertible_pullbackOver m L hL)]
  exact Stacks.SheafOfModules.pullbackPicardClass_eq_neg_of_isTrivial_tensorSheaf φ.left
    (pullbackOver m L) N (isInvertible_pullbackOver m L hL) h
    (Stacks.SheafOfModules.isInvertible_schemeTensor (cubeObj A).left _ _
      (isInvertible_pullbackOver m L hL) h) t

/-- The pullback class of the cube module along a morphism into `A × A × A`, with the three
tensor inverses replaced by the negatives of the classes they invert. -/
theorem pullbackPicardClass_cubeModule_alternating
    (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L)
    (N₁₂ N₁₃ N₂₃ : SheafOfModules.{u} (structureSheafRing (cubeObj A).left.toRingedSpace))
    (h₁₂ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₂)
    (h₁₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₃)
    (h₂₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₂₃)
    (t₁₂ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₁ A * cubeProj₂ A) L) N₁₂))
    (t₁₃ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₁ A * cubeProj₃ A) L) N₁₃))
    (t₂₃ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₂ A * cubeProj₃ A) L) N₂₃))
    {B : Over (Spec (.of k))} (φ : B ⟶ cubeObj A) :
    pullbackPicardClass φ.left (cubeModule A L N₁₂ N₁₃ N₂₃)
        (isInvertible_cubeModule A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃) =
      pullbackPicardClass (φ ≫ (cubeProj₁ A * cubeProj₂ A * cubeProj₃ A)).left L hL +
        pullbackPicardClass (φ ≫ cubeProj₁ A).left L hL +
        pullbackPicardClass (φ ≫ cubeProj₂ A).left L hL +
        pullbackPicardClass (φ ≫ cubeProj₃ A).left L hL +
        -pullbackPicardClass (φ ≫ (cubeProj₁ A * cubeProj₂ A)).left L hL +
        -pullbackPicardClass (φ ≫ (cubeProj₁ A * cubeProj₃ A)).left L hL +
        -pullbackPicardClass (φ ≫ (cubeProj₂ A * cubeProj₃ A)).left L hL := by
  have n₁₂ : pullbackPicardClass φ.left N₁₂ h₁₂ =
      -pullbackPicardClass (φ ≫ (cubeProj₁ A * cubeProj₂ A)).left L hL := by
    exact pullbackPicardClass_eq_neg_pullbackOver A L hL _ N₁₂ h₁₂ t₁₂ φ
  have n₁₃ : pullbackPicardClass φ.left N₁₃ h₁₃ =
      -pullbackPicardClass (φ ≫ (cubeProj₁ A * cubeProj₃ A)).left L hL := by
    exact pullbackPicardClass_eq_neg_pullbackOver A L hL _ N₁₃ h₁₃ t₁₃ φ
  have n₂₃ : pullbackPicardClass φ.left N₂₃ h₂₃ =
      -pullbackPicardClass (φ ≫ (cubeProj₂ A * cubeProj₃ A)).left L hL := by
    exact pullbackPicardClass_eq_neg_pullbackOver A L hL _ N₂₃ h₂₃ t₂₃ φ
  rw [pullbackPicardClass_cubeModule A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃ φ, n₁₂, n₁₃, n₂₃]
  abel

/-- The cube module is trivial on the face `e × A × A`. -/
theorem isTrivial_cubeModule_cubeFace₁
    (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L)
    (N₁₂ N₁₃ N₂₃ : SheafOfModules.{u} (structureSheafRing (cubeObj A).left.toRingedSpace))
    (h₁₂ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₂)
    (h₁₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₃)
    (h₂₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₂₃)
    (t₁₂ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₁ A * cubeProj₂ A) L) N₁₂))
    (t₁₃ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₁ A * cubeProj₃ A) L) N₁₃))
    (t₂₃ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₂ A * cubeProj₃ A) L) N₂₃)) :
    Stacks.SheafOfModules.IsTrivial (A ⊗ A).left.presheaf (A ⊗ A).left.ringCatIsSheaf
      (pullbackOver (cubeFace₁ A) (cubeModule A L N₁₂ N₁₃ N₂₃)) := by
  rw [← Stacks.SheafOfModules.pullbackPicardClass_eq_zero_iff (cubeFace₁ A).left
      (cubeModule A L N₁₂ N₁₃ N₂₃) (isInvertible_cubeModule A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃),
    pullbackPicardClass_cubeModule_alternating A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃
      t₁₂ t₁₃ t₂₃ (cubeFace₁ A)]
  simp only [MonObj.comp_mul, cubeFace₁_cubeProj₁, cubeFace₁_cubeProj₂, cubeFace₁_cubeProj₃,
    one_mul, pullbackPicardClass_one L hL]
  abel

/-- The cube module is trivial on the face `A × e × A`. -/
theorem isTrivial_cubeModule_cubeFace₂
    (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L)
    (N₁₂ N₁₃ N₂₃ : SheafOfModules.{u} (structureSheafRing (cubeObj A).left.toRingedSpace))
    (h₁₂ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₂)
    (h₁₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₃)
    (h₂₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₂₃)
    (t₁₂ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₁ A * cubeProj₂ A) L) N₁₂))
    (t₁₃ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₁ A * cubeProj₃ A) L) N₁₃))
    (t₂₃ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₂ A * cubeProj₃ A) L) N₂₃)) :
    Stacks.SheafOfModules.IsTrivial (A ⊗ A).left.presheaf (A ⊗ A).left.ringCatIsSheaf
      (pullbackOver (cubeFace₂ A) (cubeModule A L N₁₂ N₁₃ N₂₃)) := by
  rw [← Stacks.SheafOfModules.pullbackPicardClass_eq_zero_iff (cubeFace₂ A).left
      (cubeModule A L N₁₂ N₁₃ N₂₃) (isInvertible_cubeModule A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃),
    pullbackPicardClass_cubeModule_alternating A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃
      t₁₂ t₁₃ t₂₃ (cubeFace₂ A)]
  simp only [MonObj.comp_mul, cubeFace₂_cubeProj₁, cubeFace₂_cubeProj₂, cubeFace₂_cubeProj₃,
    one_mul, mul_one, pullbackPicardClass_one L hL]
  abel

/-- The cube module is trivial on the face `A × A × e`. -/
theorem isTrivial_cubeModule_cubeFace₃
    (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L)
    (N₁₂ N₁₃ N₂₃ : SheafOfModules.{u} (structureSheafRing (cubeObj A).left.toRingedSpace))
    (h₁₂ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₂)
    (h₁₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₃)
    (h₂₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₂₃)
    (t₁₂ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₁ A * cubeProj₂ A) L) N₁₂))
    (t₁₃ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₁ A * cubeProj₃ A) L) N₁₃))
    (t₂₃ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₂ A * cubeProj₃ A) L) N₂₃)) :
    Stacks.SheafOfModules.IsTrivial (A ⊗ A).left.presheaf (A ⊗ A).left.ringCatIsSheaf
      (pullbackOver (cubeFace₃ A) (cubeModule A L N₁₂ N₁₃ N₂₃)) := by
  rw [← Stacks.SheafOfModules.pullbackPicardClass_eq_zero_iff (cubeFace₃ A).left
      (cubeModule A L N₁₂ N₁₃ N₂₃) (isInvertible_cubeModule A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃),
    pullbackPicardClass_cubeModule_alternating A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃
      t₁₂ t₁₃ t₂₃ (cubeFace₃ A)]
  simp only [MonObj.comp_mul, cubeFace₃_cubeProj₁, cubeFace₃_cubeProj₂, cubeFace₃_cubeProj₃,
    mul_one, pullbackPicardClass_one L hL]
  abel

/-! ### The cube relation -/

/-- Let `A` be an abelian variety over a field `k` satisfying the theorem of the cube
`HasTheoremOfTheCube A`, and let `L` be an invertible `𝒪_A`-module. Then

`m₁₂₃^*L ⊗ m₁^*L ⊗ m₂^*L ⊗ m₃^*L ≅ m₁₂^*L ⊗ m₁₃^*L ⊗ m₂₃^*L`

as invertible modules on `A × A × A`, where `m_I` is the product of the coordinates indexed by
`I` in the group `A × A × A ⟶ A`. -/
@[stacks 0BFE "assuming the theorem of the cube (Tag 0BF4) for the triple self-product of A"]
theorem nonempty_cubeRelation [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A)
    (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L) :
    Nonempty
      (schemeTensor (cubeObj A).left
          (schemeTensor (cubeObj A).left
            (schemeTensor (cubeObj A).left
              (pullbackOver (cubeProj₁ A * cubeProj₂ A * cubeProj₃ A) L)
              (pullbackOver (cubeProj₁ A) L))
            (pullbackOver (cubeProj₂ A) L))
          (pullbackOver (cubeProj₃ A) L) ≅
        schemeTensor (cubeObj A).left
          (schemeTensor (cubeObj A).left
            (pullbackOver (cubeProj₁ A * cubeProj₂ A) L)
            (pullbackOver (cubeProj₁ A * cubeProj₃ A) L))
          (pullbackOver (cubeProj₂ A * cubeProj₃ A) L)) := by
  obtain ⟨N₁₂, h₁₂, t₁₂⟩ := Stacks.SheafOfModules.exists_invertible_isTrivial_tensorSheaf
    (pullbackOver (cubeProj₁ A * cubeProj₂ A) L)
    (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₂ A) L hL)
  obtain ⟨N₁₃, h₁₃, t₁₃⟩ := Stacks.SheafOfModules.exists_invertible_isTrivial_tensorSheaf
    (pullbackOver (cubeProj₁ A * cubeProj₃ A) L)
    (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₃ A) L hL)
  obtain ⟨N₂₃, h₂₃, t₂₃⟩ := Stacks.SheafOfModules.exists_invertible_isTrivial_tensorSheaf
    (pullbackOver (cubeProj₂ A * cubeProj₃ A) L)
    (isInvertible_pullbackOver (cubeProj₂ A * cubeProj₃ A) L hL)
  have hMtriv := hcube (cubeModule A L N₁₂ N₁₃ N₂₃)
    (isInvertible_cubeModule A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃)
    (isTrivial_cubeModule_cubeFace₁ A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃ t₁₂ t₁₃ t₂₃)
    (isTrivial_cubeModule_cubeFace₂ A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃ t₁₂ t₁₃ t₂₃)
    (isTrivial_cubeModule_cubeFace₃ A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃ t₁₂ t₁₃ t₂₃)
  have hexp := picardClass_cubeModule A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃
  rw [(Stacks.SheafOfModules.picardClass_eq_zero_iff _ _ _ _).mpr hMtriv,
    picardClass_eq_neg_pullbackOver A L hL _ N₁₂ h₁₂ t₁₂,
    picardClass_eq_neg_pullbackOver A L hL _ N₁₃ h₁₃ t₁₃,
    picardClass_eq_neg_pullbackOver A L hL _ N₂₃ h₂₃ t₂₃] at hexp
  refine (Stacks.SheafOfModules.picardClass_eq_iff (cubeObj A).left.presheaf
    (cubeObj A).left.ringCatIsSheaf _ _
    (Stacks.SheafOfModules.isInvertible_schemeTensor₄ (cubeObj A).left _ _ _ _
      (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₂ A * cubeProj₃ A) L hL)
      (isInvertible_pullbackOver (cubeProj₁ A) L hL)
      (isInvertible_pullbackOver (cubeProj₂ A) L hL)
      (isInvertible_pullbackOver (cubeProj₃ A) L hL))
    (Stacks.SheafOfModules.isInvertible_schemeTensor₃ (cubeObj A).left _ _ _
      (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₂ A) L hL)
      (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₃ A) L hL)
      (isInvertible_pullbackOver (cubeProj₂ A * cubeProj₃ A) L hL))).mp ?_
  rw [Stacks.SheafOfModules.picardClass_schemeTensor₄ (cubeObj A).left _ _ _ _
      (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₂ A * cubeProj₃ A) L hL)
      (isInvertible_pullbackOver (cubeProj₁ A) L hL)
      (isInvertible_pullbackOver (cubeProj₂ A) L hL)
      (isInvertible_pullbackOver (cubeProj₃ A) L hL),
    Stacks.SheafOfModules.picardClass_schemeTensor₃ (cubeObj A).left _ _ _
      (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₂ A) L hL)
      (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₃ A) L hL)
      (isInvertible_pullbackOver (cubeProj₂ A * cubeProj₃ A) L hL), ← sub_eq_zero, hexp]
  abel

end Stacks.Groupoids

end
