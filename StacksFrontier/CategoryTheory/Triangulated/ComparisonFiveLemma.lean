module

public import StacksFrontier.CategoryTheory.Triangulated.ComponentwiseInvertibility

/-!
# The five lemma for comparisons through a natural transformation

Let `α : F ⟶ G ⋙ Θ` be a natural transformation, with `F` and `Θ` taking values in a
triangulated category and all three functors commuting with the shifts. For a morphism
`r : G E ⟶ E'` the comparison `F E ⟶ Θ E'` is `α_E ≫ Θ r`. This file proves the five lemma for
such comparisons along a morphism of triangles `G T ⟶ T'`, in the form needed when the
comparison is known to be invertible at every shift of the outer vertices
(`allShifts_hom₂`), together with the invariance of the comparisons under maps inverted by `F`
and `Θ`. No compatibility of `α` with the shifts is required.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.CategoryTheory.ComparisonFiveLemma

section Comparison

variable {𝒦 𝒦' 𝒟 : Type*} [Category* 𝒦] [Category* 𝒦'] [Category* 𝒟]
  [HasShift 𝒦 ℤ] [HasShift 𝒦' ℤ] [HasShift 𝒟 ℤ]
  {F : 𝒦 ⥤ 𝒟} {G : 𝒦 ⥤ 𝒦'} {Θ : 𝒦' ⥤ 𝒟} [F.CommShift ℤ] [G.CommShift ℤ] [Θ.CommShift ℤ]

variable (G) in
/-- The shift of a comparison `G E ⟶ E'`: the morphism `G (E⟦n⟧) ⟶ E'⟦n⟧` obtained through the
commutation of `G` with the shift. -/
def shiftData {E : 𝒦} {E' : 𝒦'} (r : G.obj E ⟶ E') (n : ℤ) : G.obj (E⟦n⟧) ⟶ E'⟦n⟧ :=
  (G.commShiftIso n).hom.app E ≫ r⟦n⟧'

variable (α : F ⟶ G ⋙ Θ)

/-- The comparison `F E ⟶ Θ E'` made of `α` at `E` and of `Θ` of a morphism `G E ⟶ E'`. -/
def comparison {E : 𝒦} {E' : 𝒦'} (r : G.obj E ⟶ E') : F.obj E ⟶ Θ.obj E' :=
  α.app E ≫ Θ.map r

/-- The comparison is invertible at every shift. -/
def AllShifts {E : 𝒦} {E' : 𝒦'} (r : G.obj E ⟶ E') : Prop :=
  ∀ n : ℤ, IsIso (comparison α (shiftData G r n))

/-- The comparisons are natural: a morphism `e` of the data, sent to `e'`, commutes with them. -/
private theorem map_comp_comparison {C C' D : Type*} [Category* C] [Category* C'] [Category* D]
    {F' : C ⥤ D} {G' : C ⥤ C'} {Θ' : C' ⥤ D} (α' : F' ⟶ G' ⋙ Θ') {E₁ E₂ : C} {E₁' E₂' : C'}
    (r₁ : G'.obj E₁ ⟶ E₁') (r₂ : G'.obj E₂ ⟶ E₂') (e : E₁ ⟶ E₂) (e' : E₁' ⟶ E₂')
    (h : G'.map e ≫ r₂ = r₁ ≫ e') :
    F'.map e ≫ comparison α' r₂ = comparison α' r₁ ≫ Θ'.map e' := by
  dsimp only [comparison]
  rw [← Category.assoc, α'.naturality, Category.assoc, Category.assoc, Functor.comp_map,
    ← Θ'.map_comp, ← Θ'.map_comp, h]

omit [HasShift 𝒦 ℤ] [HasShift 𝒦' ℤ] [HasShift 𝒟 ℤ] [F.CommShift ℤ] [G.CommShift ℤ]
  [Θ.CommShift ℤ] in
/-- **Invariance of the comparison** under morphisms of the data inverted by `F` and by `Θ`. -/
theorem isIso_comparison_iff_of_hom {E₁ E₂ : 𝒦} {E₁' E₂' : 𝒦'} (r₁ : G.obj E₁ ⟶ E₁')
    (r₂ : G.obj E₂ ⟶ E₂') (e : E₁ ⟶ E₂) (e' : E₁' ⟶ E₂') [hF : IsIso (F.map e)]
    [hΘ : IsIso (Θ.map e')] (h : G.map e ≫ r₂ = r₁ ≫ e') :
    IsIso (comparison α r₁) ↔ IsIso (comparison α r₂) := by
  have key := map_comp_comparison α r₁ r₂ e e' h
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · have : IsIso (F.map e ≫ comparison α r₂) := by
      rw [key]
      infer_instance
    exact IsIso.of_isIso_comp_left (F.map e) _
  · have : IsIso (comparison α r₁ ≫ Θ.map e') := by
      rw [← key]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (Θ.map e')

variable (G) in
/-- Shifting a comparison twice is shifting it once by the sum, through `shiftFunctorAdd`. -/
theorem map_shiftFunctorAdd_hom_comp_shiftData_shiftData {E : 𝒦} {E' : 𝒦'}
    (r : G.obj E ⟶ E') (m n : ℤ) :
    G.map ((shiftFunctorAdd 𝒦 m n).hom.app E) ≫ shiftData G (shiftData G r m) n =
      shiftData G r (m + n) ≫ (shiftFunctorAdd 𝒦' m n).hom.app E' := by
  dsimp only [shiftData]
  rw [G.commShiftIso_add, Functor.CommShift.isoAdd_hom_app]
  have := (shiftFunctorAdd 𝒦' m n).hom.naturality r
  dsimp only [Functor.comp_map] at this
  simp only [Category.assoc, this, Iso.inv_hom_id_app_assoc, Functor.map_comp]

omit [HasShift 𝒟 ℤ] [F.CommShift ℤ] [Θ.CommShift ℤ] in
/-- The comparison at a double shift is invertible exactly when it is at the single shift by
the sum. -/
theorem isIso_comparison_shiftData_shiftData_iff {E : 𝒦} {E' : 𝒦'} (r : G.obj E ⟶ E')
    (m n : ℤ) :
    IsIso (comparison α (shiftData G (shiftData G r m) n)) ↔
      IsIso (comparison α (shiftData G r (m + n))) :=
  (isIso_comparison_iff_of_hom α _ _ ((shiftFunctorAdd 𝒦 m n).hom.app E)
    ((shiftFunctorAdd 𝒦' m n).hom.app E')
    (map_shiftFunctorAdd_hom_comp_shiftData_shiftData G r m n)).symm

variable (G) in
/-- Shifting a comparison by zero is the comparison, through `shiftFunctorZero`. -/
theorem map_shiftFunctorZero_hom_comp {E : 𝒦} {E' : 𝒦'} (r : G.obj E ⟶ E') :
    G.map ((shiftFunctorZero 𝒦 ℤ).hom.app E) ≫ r =
      shiftData G r 0 ≫ (shiftFunctorZero 𝒦' ℤ).hom.app E' := by
  dsimp only [shiftData]
  rw [G.commShiftIso_zero, Functor.CommShift.isoZero_hom_app, Category.assoc, Category.assoc,
    (shiftFunctorZero 𝒦' ℤ).hom.naturality r, Functor.id_map, Iso.inv_hom_id_app_assoc]

omit [HasShift 𝒟 ℤ] [F.CommShift ℤ] [Θ.CommShift ℤ] in
/-- A comparison invertible at every shift is invertible. -/
theorem AllShifts.isIso {E : 𝒦} {E' : 𝒦'} {r : G.obj E ⟶ E'} (h : AllShifts α r) :
    IsIso (comparison α r) :=
  (isIso_comparison_iff_of_hom α _ _ ((shiftFunctorZero 𝒦 ℤ).hom.app E)
    ((shiftFunctorZero 𝒦' ℤ).hom.app E') (map_shiftFunctorZero_hom_comp G r)).1 (h 0)

omit [HasShift 𝒟 ℤ] [F.CommShift ℤ] [Θ.CommShift ℤ] in
/-- The shifts of a comparison invertible at every shift are invertible at every shift. -/
theorem AllShifts.shiftData {E : 𝒦} {E' : 𝒦'} {r : G.obj E ⟶ E'} (h : AllShifts α r)
    (m : ℤ) : AllShifts α (shiftData G r m) := fun n =>
  (isIso_comparison_shiftData_shiftData_iff α r m n).2 (h (m + n))

/-- **Invariance of the comparisons at all shifts** under morphisms of the data inverted by `F`
and by `Θ`. -/
theorem allShifts_iff_of_hom {E₁ E₂ : 𝒦} {E₁' E₂' : 𝒦'} (r₁ : G.obj E₁ ⟶ E₁')
    (r₂ : G.obj E₂ ⟶ E₂') (e : E₁ ⟶ E₂) (e' : E₁' ⟶ E₂') [hF : IsIso (F.map e)]
    [hΘ : IsIso (Θ.map e')] (h : G.map e ≫ r₂ = r₁ ≫ e') :
    AllShifts α r₁ ↔ AllShifts α r₂ := by
  refine forall_congr' fun n => ?_
  have hF' : IsIso (F.map (e⟦n⟧')) :=
    (NatIso.isIso_map_iff (F.commShiftIso n) e).2 (inferInstanceAs (IsIso ((F.map e)⟦n⟧')))
  have hΘ' : IsIso (Θ.map (e'⟦n⟧')) :=
    (NatIso.isIso_map_iff (Θ.commShiftIso n) e').2 (inferInstanceAs (IsIso ((Θ.map e')⟦n⟧')))
  refine isIso_comparison_iff_of_hom α _ _ (e⟦n⟧') (e'⟦n⟧') ?_
  dsimp only [shiftData]
  rw [G.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, h, Functor.map_comp,
    Category.assoc]

/-- A comparison between objects that `F` and `Θ` send to zero is invertible at every shift. -/
theorem allShifts_of_isZero {E : 𝒦} {E' : 𝒦'} (r : G.obj E ⟶ E') (hE : IsZero (F.obj E))
    (hE' : IsZero (Θ.obj E')) [HasZeroMorphisms 𝒟]
    [∀ n : ℤ, (shiftFunctor 𝒟 n).PreservesZeroMorphisms] :
    AllShifts α r := fun n =>
  IsZero.isIso (IsZero.of_iso (Functor.map_isZero _ hE) ((F.commShiftIso n).app E))
    (IsZero.of_iso (Functor.map_isZero _ hE') ((Θ.commShiftIso n).app E')) _

section Whisker

variable {𝒟' : Type*} [Category* 𝒟'] [HasShift 𝒟' ℤ] (P : 𝒟 ⥤ 𝒟') [P.CommShift ℤ]

/-- The comparison `α : F ⟶ G ⋙ Θ` followed by a functor `P`. -/
def whiskerComparison : F ⋙ P ⟶ G ⋙ (Θ ⋙ P) :=
  Functor.whiskerRight α P ≫ (Functor.associator G Θ P).hom

omit [HasShift 𝒦 ℤ] [HasShift 𝒦' ℤ] [HasShift 𝒟 ℤ] [F.CommShift ℤ] [G.CommShift ℤ]
  [Θ.CommShift ℤ] [HasShift 𝒟' ℤ] [P.CommShift ℤ] in
/-- The comparison of `whiskerComparison α P` is the image by `P` of the comparison of `α`. -/
theorem comparison_whiskerComparison {E : 𝒦} {E' : 𝒦'} (r : G.obj E ⟶ E') :
    comparison (whiskerComparison α P) r = P.map (comparison α r) := by
  simp [comparison, whiskerComparison]

omit [HasShift 𝒟 ℤ] [F.CommShift ℤ] [Θ.CommShift ℤ] [HasShift 𝒟' ℤ] [P.CommShift ℤ] in
/-- A comparison invertible at every shift stays so after applying a functor. -/
theorem AllShifts.whisker {E : 𝒦} {E' : 𝒦'} {r : G.obj E ⟶ E'} (h : AllShifts α r) :
    AllShifts (whiskerComparison α P) r := fun n => by
  rw [comparison_whiskerComparison]
  have := h n
  infer_instance

end Whisker

end Comparison

section Triangles

/-- A functor whose image of a triangle is distinguished, followed by a triangulated functor,
sends that triangle to a distinguished triangle. -/
theorem mapTriangle_comp_distinguished {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [Preadditive D] [Preadditive E]
    [HasZeroObject D] [HasZeroObject E] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated D] [Pretriangulated E]
    (A : C ⥤ D) (B : D ⥤ E) [A.CommShift ℤ] [B.CommShift ℤ] [B.IsTriangulated]
    (T : Triangle C) (hT : A.mapTriangle.obj T ∈ distTriang D) :
    (A ⋙ B).mapTriangle.obj T ∈ distTriang E :=
  isomorphic_distinguished _ (B.map_distinguished _ hT) _ ((Functor.mapTriangleCompIso A B).app T)

variable {𝒦 𝒦' 𝒟 : Type*} [Category* 𝒦] [Category* 𝒦'] [Category* 𝒟]
  [HasShift 𝒦 ℤ] [HasShift 𝒦' ℤ] [HasShift 𝒟 ℤ] [Preadditive 𝒦] [Preadditive 𝒦']
  [Preadditive 𝒟] [HasZeroObject 𝒟]
  [∀ n : ℤ, (shiftFunctor 𝒦 n).Additive] [∀ n : ℤ, (shiftFunctor 𝒦' n).Additive]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]
  {F : 𝒦 ⥤ 𝒟} {G : 𝒦 ⥤ 𝒦'} {Θ : 𝒦' ⥤ 𝒟} [F.CommShift ℤ] [G.CommShift ℤ] [Θ.CommShift ℤ]
  (α : F ⟶ G ⋙ Θ)

omit [Preadditive 𝒦] [Preadditive 𝒦'] [∀ (n : ℤ), (shiftFunctor 𝒦 n).Additive]
  [∀ (n : ℤ), (shiftFunctor 𝒦' n).Additive] in
/-- **The five lemma for comparisons, third vertex.** Let `T` and `T'` be triangles sent to
distinguished triangles by `F` and by `Θ`, and `ρ : G T ⟶ T'` a morphism of triangles, given by
its components. If the comparisons along `ρ` are
invertible at the first two vertices and at their shifts by one, then so is the comparison at
the third vertex. -/
theorem isIso_comparison_hom₃ (T : Triangle 𝒦) (T' : Triangle 𝒦')
    (hT : F.mapTriangle.obj T ∈ distTriang 𝒟) (hT' : Θ.mapTriangle.obj T' ∈ distTriang 𝒟) (ρ₁ :
        G.obj T.obj₁ ⟶ T'.obj₁) (ρ₂ : G.obj T.obj₂ ⟶ T'.obj₂)
    (ρ₃ : G.obj T.obj₃ ⟶ T'.obj₃) (c₁ : G.map T.mor₁ ≫ ρ₂ = ρ₁ ≫ T'.mor₁)
    (c₂ : G.map T.mor₂ ≫ ρ₃ = ρ₂ ≫ T'.mor₂)
    (c₃ : (G.map T.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫ ρ₁⟦(1 : ℤ)⟧' =
      ρ₃ ≫ T'.mor₃)
    (h₁ : IsIso (comparison α ρ₁)) (h₂ : IsIso (comparison α ρ₂))
    (h₁' : IsIso (comparison α (shiftData G ρ₁ 1)))
    (h₂' : IsIso (comparison α (shiftData G ρ₂ 1))) :
    IsIso (comparison α ρ₃) := by
  refine ComponentwiseInvertibility.isIso_of_five
    (F.mapTriangle.obj T) (Θ.mapTriangle.obj T') hT hT' (comparison α ρ₁) (comparison α ρ₂)
    (comparison α ρ₃)
    ((F.commShiftIso (1 : ℤ)).inv.app T.obj₁ ≫ comparison α (shiftData G ρ₁ 1) ≫
        (Θ.commShiftIso (1 : ℤ)).hom.app T'.obj₁)
    ((F.commShiftIso (1 : ℤ)).inv.app T.obj₂ ≫ comparison α (shiftData G ρ₂ 1) ≫
        (Θ.commShiftIso (1 : ℤ)).hom.app T'.obj₂) h₁ h₂
    (IsIso.comp_isIso' ((F.commShiftIso (1 : ℤ)).app T.obj₁).isIso_inv
      (IsIso.comp_isIso' h₁' ((Θ.commShiftIso (1 : ℤ)).app T'.obj₁).isIso_hom))
    (IsIso.comp_isIso' ((F.commShiftIso (1 : ℤ)).app T.obj₂).isIso_inv
      (IsIso.comp_isIso' h₂' ((Θ.commShiftIso (1 : ℤ)).app T'.obj₂).isIso_hom)) ?_ ?_ ?_ ?_
  · exact map_comp_comparison α _ _ _ _ c₁
  · exact map_comp_comparison α _ _ _ _ c₂
  · have := map_comp_comparison α _ (shiftData G ρ₁ 1) T.mor₃ T'.mor₃
      (by rw [shiftData, ← Category.assoc, c₃])
    change (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
        (F.commShiftIso (1 : ℤ)).inv.app T.obj₁ ≫ comparison α (shiftData G ρ₁ 1) ≫
          (Θ.commShiftIso (1 : ℤ)).hom.app T'.obj₁ =
      comparison α ρ₃ ≫ Θ.map T'.mor₃ ≫ (Θ.commShiftIso (1 : ℤ)).hom.app T'.obj₁
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [reassoc_of% this]
  · have := map_comp_comparison α (shiftData G ρ₁ 1) (shiftData G ρ₂ 1) (T.mor₁⟦(1 : ℤ)⟧')
      (T'.mor₁⟦(1 : ℤ)⟧') (by
        rw [shiftData, shiftData, G.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, c₁,
          Functor.map_comp, Category.assoc])
    change F.map T.mor₁⟦(1 : ℤ)⟧' ≫ (F.commShiftIso (1 : ℤ)).inv.app T.obj₂ ≫
          comparison α (shiftData G ρ₂ 1) ≫ (Θ.commShiftIso (1 : ℤ)).hom.app T'.obj₂ =
      ((F.commShiftIso (1 : ℤ)).inv.app T.obj₁ ≫ comparison α (shiftData G ρ₁ 1) ≫
          (Θ.commShiftIso (1 : ℤ)).hom.app T'.obj₁) ≫ (Θ.map T'.mor₁)⟦(1 : ℤ)⟧'
    simp only [Category.assoc]
    rw [F.commShiftIso_inv_naturality_assoc, reassoc_of% this, Θ.commShiftIso_hom_naturality]

variable [F.Additive] [G.Additive] [Θ.Additive]

omit [∀ (n : ℤ), (shiftFunctor 𝒦 n).Additive] in
/-- A triangle sent to a distinguished triangle by an additive functor commuting with the
shifts has all its shifts sent to distinguished triangles. -/
theorem mapTriangle_shift_distinguished (H : 𝒦 ⥤ 𝒟) [H.CommShift ℤ] [H.Additive]
    (T : Triangle 𝒦) (hT : H.mapTriangle.obj T ∈ distTriang 𝒟) (n : ℤ) :
    H.mapTriangle.obj ((Triangle.shiftFunctor 𝒦 n).obj T) ∈ distTriang 𝒟 :=
  isomorphic_distinguished _ (Triangle.shift_distinguished _ hT n) _
    ((H.mapTriangleCommShiftIso n).app T)

omit [∀ (n : ℤ), (shiftFunctor 𝒦 n).Additive] in
/-- A triangle sent to a distinguished triangle by an additive functor commuting with the
shifts has its inverse rotation sent to a distinguished triangle. -/
theorem mapTriangle_invRotate_distinguished (H : 𝒦 ⥤ 𝒟) [H.CommShift ℤ] [H.Additive]
    (T : Triangle 𝒦) (hT : H.mapTriangle.obj T ∈ distTriang 𝒟) :
    H.mapTriangle.obj T.invRotate ∈ distTriang 𝒟 :=
  isomorphic_distinguished _ (inv_rot_of_distTriang _ hT) _
    (H.mapTriangleInvRotateIso.app T).symm

omit [∀ (n : ℤ), (shiftFunctor 𝒦 n).Additive] [∀ (n : ℤ), (shiftFunctor 𝒦' n).Additive] in
/-- **The five lemma for comparisons, middle vertex, at every shift.** Let `T` and `T'` be
triangles sent to distinguished triangles by `F` and by `Θ`, and `ρ : G T ⟶ T'` a morphism of
triangles. If the comparisons along `ρ` are invertible at every shift of the first and third
vertices, then so are they at every shift of the middle vertex. -/
theorem allShifts_hom₂ (T : Triangle 𝒦) (T' : Triangle 𝒦')
    (hT : F.mapTriangle.obj T ∈ distTriang 𝒟) (hT' : Θ.mapTriangle.obj T' ∈ distTriang 𝒟)
    (ρ : G.mapTriangle.obj T ⟶ T') (h₁ : AllShifts α (E := T.obj₁) ρ.hom₁)
    (h₃ : AllShifts α (E := T.obj₃) ρ.hom₃) :
    AllShifts α (E := T.obj₂) ρ.hom₂ := by
  intro n
  let S := (Triangle.shiftFunctor 𝒦 n).obj T
  let S' := (Triangle.shiftFunctor 𝒦' n).obj T'
  let ρn : G.mapTriangle.obj S ⟶ S' :=
    (G.mapTriangleCommShiftIso n).hom.app T ≫ (Triangle.shiftFunctor 𝒦' n).map ρ
  let ρ' : G.mapTriangle.obj S.invRotate ⟶ S'.invRotate :=
    (G.mapTriangleInvRotateIso.inv.app S) ≫ (invRotate 𝒦').map ρn
  have hS := mapTriangle_invRotate_distinguished F S (mapTriangle_shift_distinguished F T hT n)
  have hS' := mapTriangle_invRotate_distinguished Θ S'
    (mapTriangle_shift_distinguished Θ T' hT' n)
  have e₂ : ρ'.hom₂ = shiftData G (E := T.obj₁) ρ.hom₁ n := Category.id_comp _
  have e₃ : ρ'.hom₃ = shiftData G (E := T.obj₂) ρ.hom₂ n := Category.id_comp _
  have h := isIso_comparison_hom₃ α S.invRotate S'.invRotate hS hS' ρ'.hom₁ ρ'.hom₂ ρ'.hom₃
    ρ'.comm₁ ρ'.comm₂ ρ'.comm₃
    ((h₃.shiftData α n).shiftData α (-1)).isIso
    (by rw [e₂]; exact h₁ n)
    ((h₃.shiftData α n).shiftData α (-1) 1)
    (by rw [e₂]; exact (h₁.shiftData α n) 1)
  rwa [e₃] at h

end Triangles

end Stacks.CategoryTheory.ComparisonFiveLemma
