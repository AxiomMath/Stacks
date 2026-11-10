module

public import StacksFrontier.CategoryTheory.Shift.ShiftSequenceDegreeZeroTransport

/-!
# Transporting a degree-zero zigzag along two shift sequences

Let `U` and `V` be functors out of a category `C` with a shift by `ℤ`, each with a
`CategoryTheory.Functor.ShiftSequence`, and let `W : C ⥤ A` be a third functor. Two natural
transformations `α : U.shift 0 ⟶ W` and `β : V.shift 0 ⟶ W` give, at every object `X` at which
`β` is invertible after shifting by `n`, a morphism in degree `n`:

`U.shift n X ≅ U.shift 0 (X⟦n⟧) ⟶ W (X⟦n⟧) ≅ V.shift 0 (X⟦n⟧) ≅ V.shift n X`.

These morphisms commute with the connecting morphisms `CategoryTheory.Functor.homologySequenceδ`
of every triangle; no compatibility of `α` or `β` with the shift is needed.

## Main definitions

* `CategoryTheory.Functor.zigzagShiftTransport`: the degree-`n` morphism at an object.

## Main results

* `CategoryTheory.Functor.zigzagShiftTransport_naturality`: it is natural in the object.
* `CategoryTheory.Functor.zigzagShiftTransport_comp_homologySequenceδ`: **it commutes with the
  connecting morphisms.**
* `CategoryTheory.Functor.homologySequenceδ_leftComp`: the connecting morphisms of `π ⋙ H` are
  those of `H` at the image triangles.
* `CategoryTheory.Functor.compZigzagTransport` and
  `CategoryTheory.Functor.compZigzagTransport_comp_homologySequenceδ`: the same transport for
  `U = π₁ ⋙ H₁` and `V = π₂ ⋙ H₂`, stated with the connecting morphisms of `H₁` and `H₂` at the
  images of a triangle under `π₁` and `π₂`.
-/

@[expose] public noncomputable section

open CategoryTheory Category Pretriangulated

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {A : Type u₂} [Category.{v₂} A] [HasShift C ℤ]
  (U V : C ⥤ A) [U.ShiftSequence ℤ] [V.ShiftSequence ℤ] {W : C ⥤ A}
  (α : U.shift (0 : ℤ) ⟶ W) (β : V.shift (0 : ℤ) ⟶ W)

/-- **The degree-`n` morphism determined by a degree-zero zigzag** `U.shift 0 ⟶ W ⟵ V.shift 0`,
at an object `X` at which the second leg is invertible after shifting by `n`. -/
def zigzagShiftTransport (n : ℤ) (X : C) [IsIso (β.app (X⟦n⟧))] :
    (U.shift n).obj X ⟶ (V.shift n).obj X :=
  (U.shiftIso n 0 n (add_zero n)).inv.app X ≫ α.app (X⟦n⟧) ≫ CategoryTheory.inv (β.app (X⟦n⟧)) ≫
    (V.shiftIso n 0 n (add_zero n)).hom.app X

/-- The morphism `zigzagShiftTransport U V α β n X` is an isomorphism when both `α` and `β` are
invertible at `X⟦n⟧`. -/
instance isIso_zigzagShiftTransport (n : ℤ) (X : C) [IsIso (α.app (X⟦n⟧))]
    [IsIso (β.app (X⟦n⟧))] : IsIso (zigzagShiftTransport U V α β n X) := by
  dsimp only [zigzagShiftTransport]
  infer_instance

/-- Naturality of the inverse of `β` at two objects where it is invertible. -/
private theorem inv_comp_map_eq_map_comp_inv {X Y : C} (f : X ⟶ Y) [IsIso (β.app X)]
    [IsIso (β.app Y)] :
    CategoryTheory.inv (β.app X) ≫ (V.shift 0).map f =
      W.map f ≫ CategoryTheory.inv (β.app Y) := by
  rw [IsIso.eq_comp_inv, assoc, β.naturality, IsIso.inv_hom_id_assoc]

/-- **The transported morphisms are natural.** -/
@[reassoc]
theorem zigzagShiftTransport_naturality (n : ℤ) {X Y : C} (φ : X ⟶ Y)
    [IsIso (β.app (X⟦n⟧))] [IsIso (β.app (Y⟦n⟧))] :
    (U.shift n).map φ ≫ zigzagShiftTransport U V α β n Y =
      zigzagShiftTransport U V α β n X ≫ (V.shift n).map φ := by
  dsimp only [zigzagShiftTransport]
  have hU := (U.shiftIso n 0 n (add_zero n)).inv.naturality φ
  have hV := (V.shiftIso n 0 n (add_zero n)).hom.naturality φ
  have hα := α.naturality (φ⟦n⟧')
  have hβ := inv_comp_map_eq_map_comp_inv V β (φ⟦n⟧')
  simp only [Functor.comp_map] at hU hV
  rw [reassoc_of% hU, reassoc_of% hα, ← reassoc_of% hβ, hV]
  simp only [Category.assoc]

/-- **The transported morphisms commute with the connecting morphisms.**  For every triangle
`T` of `C` and `n₀ + 1 = n₁` such that `β` is invertible at `T.obj₃⟦n₀⟧` and `T.obj₁⟦n₁⟧`, the
square formed by the transported morphisms and the connecting morphisms of `U` and `V`
commutes. -/
@[reassoc]
theorem zigzagShiftTransport_comp_homologySequenceδ (T : Triangle C) (n₀ n₁ : ℤ)
    (h : n₀ + 1 = n₁) [IsIso (β.app (T.obj₃⟦n₀⟧))] [IsIso (β.app (T.obj₁⟦n₁⟧))] :
    zigzagShiftTransport U V α β n₀ T.obj₃ ≫ V.homologySequenceδ T n₀ n₁ h =
      U.homologySequenceδ T n₀ n₁ h ≫ zigzagShiftTransport U V α β n₁ T.obj₁ := by
  rw [homologySequenceδ_eq_shiftIso V, homologySequenceδ_eq_shiftIso U]
  dsimp only [zigzagShiftTransport]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  set g := T.mor₃⟦n₀⟧' ≫ (shiftFunctorAdd' C 1 n₀ n₁ (by rw [add_comm 1, h])).inv.app T.obj₁
  have hα := α.naturality g
  have hβ := inv_comp_map_eq_map_comp_inv V β g
  rw [reassoc_of% hβ, ← reassoc_of% hα]

section Composite

variable {D : Type*} [Category* D] [HasShift D ℤ]
  (π : C ⥤ D) [π.CommShift ℤ] (H : D ⥤ A) [H.ShiftSequence ℤ]

/-- **The connecting morphisms of `π ⋙ H` are those of `H` at the image triangles**, for the
shift sequence `CategoryTheory.Functor.ShiftSequence.leftComp` of `π ⋙ H`. -/
theorem homologySequenceδ_leftComp (T : Triangle C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (π ⋙ H).homologySequenceδ T n₀ n₁ h =
      H.homologySequenceδ (π.mapTriangle.obj T) n₀ n₁ h := by
  simp only [homologySequenceδ, shiftMap]
  change (H.shift n₀).map (π.map T.mor₃) ≫ (𝟙 _ ≫ (H.shift n₀).map ((π.commShiftIso 1).hom.app _) ≫
      𝟙 _ ≫ (H.shiftIso 1 n₀ n₁ _).hom.app _) = _
  simp only [Category.id_comp]
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

end Composite

section CompositeZigzag

variable {D₁ D₂ : Type*} [Category* D₁] [Category* D₂] [HasShift D₁ ℤ] [HasShift D₂ ℤ]
  (π₁ : C ⥤ D₁) [π₁.CommShift ℤ] (H₁ : D₁ ⥤ A) [H₁.ShiftSequence ℤ]
  (π₂ : C ⥤ D₂) [π₂.CommShift ℤ] (H₂ : D₂ ⥤ A) [H₂.ShiftSequence ℤ]
  {W' : C ⥤ A} (α' : π₁ ⋙ H₁ ⟶ W') (β' : π₂ ⋙ H₂ ⟶ W')

/-- The second leg of a composite zigzag, read on the degree-zero functor of `π₂ ⋙ H₂`. -/
abbrev compLeg₂ : (π₂ ⋙ H₂).shift (0 : ℤ) ⟶ W' := ((π₂ ⋙ H₂).isoShiftZero ℤ).hom ≫ β'

/-- The first leg of a composite zigzag, read on the degree-zero functor of `π₁ ⋙ H₁`. -/
abbrev compLeg₁ : (π₁ ⋙ H₁).shift (0 : ℤ) ⟶ W' := ((π₁ ⋙ H₁).isoShiftZero ℤ).hom ≫ α'

/-- The component of `compLeg₂ π₂ H₂ β'` at `X` is an isomorphism when `β'` is invertible
at `X`. -/
instance isIso_compLeg₂_app (X : C) [IsIso (β'.app X)] :
    IsIso ((compLeg₂ π₂ H₂ β').app X) := by
  dsimp only [compLeg₂, NatTrans.comp_app]
  infer_instance

/-- **The degree-`n` morphism of a composite zigzag**
`H₁^n(π₁ X) ⟶ H₂^n(π₂ X)`, at an object `X` at which `β'` is invertible after shifting by `n`. -/
def compZigzagTransport (n : ℤ) (X : C) [IsIso (β'.app (X⟦n⟧))] :
    (H₁.shift n).obj (π₁.obj X) ⟶ (H₂.shift n).obj (π₂.obj X) :=
  zigzagShiftTransport (π₁ ⋙ H₁) (π₂ ⋙ H₂) (compLeg₁ π₁ H₁ α') (compLeg₂ π₂ H₂ β') n X

/-- The morphism `compZigzagTransport π₁ H₁ π₂ H₂ α' β' n X` is an isomorphism when both `α'` and
`β'` are invertible at `X⟦n⟧`. -/
instance isIso_compZigzagTransport (n : ℤ) (X : C) [IsIso (α'.app (X⟦n⟧))]
    [IsIso (β'.app (X⟦n⟧))] : IsIso (compZigzagTransport π₁ H₁ π₂ H₂ α' β' n X) := by
  have : IsIso ((compLeg₁ π₁ H₁ α').app (X⟦n⟧)) := by
    dsimp only [compLeg₁, NatTrans.comp_app]
    infer_instance
  exact isIso_zigzagShiftTransport (π₁ ⋙ H₁) (π₂ ⋙ H₂) _ _ n X

/-- **The degree-`n` morphisms of a composite zigzag are natural.** -/
@[reassoc]
theorem compZigzagTransport_naturality (n : ℤ) {X Y : C} (φ : X ⟶ Y)
    [IsIso (β'.app (X⟦n⟧))] [IsIso (β'.app (Y⟦n⟧))] :
    (H₁.shift n).map (π₁.map φ) ≫ compZigzagTransport π₁ H₁ π₂ H₂ α' β' n Y =
      compZigzagTransport π₁ H₁ π₂ H₂ α' β' n X ≫ (H₂.shift n).map (π₂.map φ) :=
  zigzagShiftTransport_naturality (π₁ ⋙ H₁) (π₂ ⋙ H₂) (compLeg₁ π₁ H₁ α') (compLeg₂ π₂ H₂ β') n φ

/-- **The degree-`n` morphisms of a composite zigzag commute with the connecting morphisms**
of `H₁` and `H₂` at the images of a triangle under `π₁` and `π₂`. -/
@[reassoc]
theorem compZigzagTransport_comp_homologySequenceδ (T : Triangle C) (n₀ n₁ : ℤ)
    (h : n₀ + 1 = n₁) [IsIso (β'.app (T.obj₃⟦n₀⟧))] [IsIso (β'.app (T.obj₁⟦n₁⟧))] :
    compZigzagTransport π₁ H₁ π₂ H₂ α' β' n₀ T.obj₃ ≫
        H₂.homologySequenceδ (π₂.mapTriangle.obj T) n₀ n₁ h =
      H₁.homologySequenceδ (π₁.mapTriangle.obj T) n₀ n₁ h ≫
        compZigzagTransport π₁ H₁ π₂ H₂ α' β' n₁ T.obj₁ := by
  rw [← homologySequenceδ_leftComp π₂ H₂, ← homologySequenceδ_leftComp π₁ H₁]
  exact zigzagShiftTransport_comp_homologySequenceδ (π₁ ⋙ H₁) (π₂ ⋙ H₂) (compLeg₁ π₁ H₁ α')
    (compLeg₂ π₂ H₂ β') T n₀ n₁ h

end CompositeZigzag

end CategoryTheory.Functor

end
