module

public import Mathlib.CategoryTheory.Quotient.Preadditive
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.MappingConeAdmissible
public import StacksFrontier.Algebra.DifferentialGraded.Module.MappingConeFunctorial
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyRectification

/-!
# Homotopy equivalence of the cones of a homotopy-commutative square

Let a square of homomorphisms of differential graded modules commute up to homotopy, and let it
be extended to a homomorphism `c` between the mapping cones of its two horizontal arrows. If the
two vertical arrows become isomorphisms in the homotopy category, so does `c`. The proof builds a
homomorphism in the opposite direction from the homotopy inverses of the vertical arrows, and
shows that each of the two composites differs from the identity by an endomorphism of a cone
which is null-homotopic after composing with the cone inclusion and with the cone projection, and
hence squares to zero in the homotopy category.

## Main results

* `DifferentialGradedModule.isIso_mappingConeMap_of_isIso`: the map on cones induced by a
  homotopy-commutative square with homotopy-invertible vertical arrows is invertible in the
  homotopy category.

## Implementation notes

Morphisms of the homotopy category are represented by homomorphisms of differential graded
modules rather than by a chosen model of triangles, so the three squares of the morphism of cone
triangles appear as homotopies of composites and invertibility is stated in the quotient
category. The preadditive structure of the homotopy category is only needed inside the proof, so
it is supplied locally rather than registered as an instance.

## References

* [Stacks Project, Tag 09KE](https://stacks.math.columbia.edu/tag/09KE)
-/

@[expose] public section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
variable {K₁ L₁ K₂ L₂ : DifferentialGradedModule A}

private theorem homotopic_sub_zero {M N : DifferentialGradedModule A}
    {f g : Hom M N} (h : Homotopic f g) : Homotopic (f - g) 0 := by
  obtain ⟨h⟩ := h
  exact ⟨h.toLinearMap, h.map_grading, fun x => by simpa using h.homotopy_eq x⟩

private theorem homotopic_add {M N : DifferentialGradedModule A}
    {f₁ f₂ g₁ g₂ : Hom M N} (h₁ : Homotopic f₁ f₂) (h₂ : Homotopic g₁ g₂) :
    Homotopic (f₁ + g₁) (f₂ + g₂) := by
  obtain ⟨h₁⟩ := h₁
  obtain ⟨h₂⟩ := h₂
  refine ⟨h₁.toLinearMap + h₂.toLinearMap,
    fun n x hx => (N.grading (n - 1)).add_mem (h₁.map_grading n x hx) (h₂.map_grading n x hx),
    fun x => ?_⟩
  calc
    (f₁.toFun x + g₁.toFun x) - (f₂.toFun x + g₂.toFun x) =
        (f₁.toFun x - f₂.toFun x) + (g₁.toFun x - g₂.toFun x) := by abel
    _ = _ := by
      rw [h₁.homotopy_eq x, h₂.homotopy_eq x]
      simp
      abel

private theorem homotopic_shiftMap {M N : DifferentialGradedModule A}
    {f g : Hom M N} (h : Homotopy f g) :
    Homotopic (shiftMap f 1) (shiftMap g 1) := by
  refine ⟨{ toLinearMap := -h.toLinearMap, map_grading := ?_, homotopy_eq := ?_ }⟩
  · intro n x hx
    have hidx : n + 1 - 1 = n - 1 + 1 := by omega
    exact (N.grading (n - 1 + 1)).neg_mem
      (by simpa only [hidx] using h.map_grading (n + 1) x (by simpa using hx))
  · intro x
    simp [shiftMap_toFun, shift_d, Int.negOnePow_one, Units.smul_def, h.homotopy_eq x]

private theorem isIso_of_square_zero_perturbation
    {C : Type*} [Category C] [Preadditive C] {X : C} (f e : X ⟶ X)
    (hf : f = 𝟙 X + e) (he : e ≫ e = 0) : IsIso f := by
  subst hf
  exact ⟨⟨𝟙 X - e, by simp [he], by simp [he]⟩⟩

private theorem isIso_of_homotopic_identity_on_cone (f : K₁ ⟶ L₁)
    (d : coneModule f ⟶ coneModule f)
    (hI : Homotopic (Hom.comp d (coneInclusion f)) (coneInclusion f))
    (hP : Homotopic (Hom.comp (coneProjection f) d) (coneProjection f)) :
    IsIso ((toHomotopyCategory A).map d) := by
  let δ : coneModule f ⟶ coneModule f := d - 𝟙 _
  have hI0 : Homotopic (coneInclusion f ≫ δ) 0 := by
    simpa only [δ, Preadditive.comp_sub, Category.comp_id] using
      (homotopic_sub_zero hI : Homotopic (coneInclusion f ≫ d - coneInclusion f) 0)
  have hP0 : Homotopic (δ ≫ coneProjection f) 0 := by
    simpa only [δ, Preadditive.sub_comp, Category.id_comp] using
      (homotopic_sub_zero hP : Homotopic (d ≫ coneProjection f - coneProjection f) 0)
  have hsq := comp_homotopic_zero_of_isAdmissibleShortExact
    (coneInclusion f) (coneProjection f)
    (mappingCone_isAdmissibleShortExact f) δ δ hP0 hI0
  let r := homotopyRel A
  let hAdd : ∀ ⦃X Y : DifferentialGradedModule A⦄
      (f₁ f₂ g₁ g₂ : X ⟶ Y), r f₁ f₂ → r g₁ g₂ → r (f₁ + g₁) (f₂ + g₂) :=
    fun _ _ _ _ _ _ h₁ h₂ => homotopic_add h₁ h₂
  let _ : Preadditive (HomotopyCategory A) := CategoryTheory.Quotient.preadditive r hAdd
  let _ : (toHomotopyCategory A).Additive := CategoryTheory.Quotient.functor_additive r hAdd
  let e : (toHomotopyCategory A).obj (coneModule f) ⟶
      (toHomotopyCategory A).obj (coneModule f) := (toHomotopyCategory A).map δ
  have he : e ≫ e = 0 := by
    have hq := (CategoryTheory.Quotient.functor_map_eq_iff r (Hom.comp δ δ) 0).2 hsq
    change (toHomotopyCategory A).map (Hom.comp δ δ) = _ at hq
    refine ((toHomotopyCategory A).map_comp δ δ).symm.trans ?_
    convert hq using 1
    · rfl
    · simp
  apply isIso_of_square_zero_perturbation _ e ?_ he
  have he' : e = (toHomotopyCategory A).map d - 𝟙 _ := by
    show (toHomotopyCategory A).map (d - 𝟙 _) = _
    rw [Functor.map_sub, CategoryTheory.Functor.map_id]
  rw [he']
  abel

/-- In a morphism of cone triangles, if the maps on the source and the target of the two
original arrows are homotopy equivalences, then so is the induced map on the cones. -/
@[stacks 09KE]
theorem isIso_mappingConeMap_of_isIso
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (c : coneModule f₁ ⟶ coneModule f₂)
    (h₁ : Homotopic (a ≫ f₂) (f₁ ≫ b))
    (h₂ : Homotopic (b ≫ coneInclusion f₂) (coneInclusion f₁ ≫ c))
    (h₃ : Homotopic (c ≫ coneProjection f₂)
      (coneProjection f₁ ≫ shiftMap a 1))
    [IsIso ((toHomotopyCategory A).map a)]
    [IsIso ((toHomotopyCategory A).map b)] :
    IsIso ((toHomotopyCategory A).map c) := by
  let Q := toHomotopyCategory A
  have qeq : ∀ {X Y : DifferentialGradedModule A} {g h : X ⟶ Y},
      Homotopic g h → Q.map g = Q.map h := fun hh =>
    (CategoryTheory.Quotient.functor_map_eq_iff _ _ _).2 hh
  have hom : ∀ {X Y : DifferentialGradedModule A} {g h : X ⟶ Y},
      Q.map g = Q.map h → Homotopic g h := fun hh =>
    (CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) _ _).1 hh
  have hshift : ∀ {M N : DifferentialGradedModule A} {u : M ⟶ N} {v : N ⟶ M},
      Homotopic (u ≫ v) (Hom.id M) →
        Q.map (shiftMap u 1) ≫ Q.map (shiftMap v 1) = 𝟙 _ := by
    intro M N u v h
    have hl : shiftMap (u ≫ v) 1 = Hom.comp (shiftMap v 1) (shiftMap u 1) := by
      apply Hom.ext
      rfl
    have hr : shiftMap (Hom.id M) 1 = Hom.id (shift M 1) := by
      apply Hom.ext
      rfl
    have hs := homotopic_shiftMap h.some
    rw [hl, hr] at hs
    rw [← Q.map_comp]
    exact (qeq hs).trans (Q.map_id _)
  have key : ∀ {X₁ Y₁ X₂ Y₂ : DifferentialGradedModule A} (g₁ : X₁ ⟶ Y₁) (g₂ : X₂ ⟶ Y₂)
      {p : X₁ ⟶ X₂} {p' : X₂ ⟶ X₁} {q : Y₁ ⟶ Y₂} {q' : Y₂ ⟶ Y₁}
      (e : coneModule g₁ ⟶ coneModule g₂) (e' : coneModule g₂ ⟶ coneModule g₁),
      Q.map q ≫ Q.map q' = 𝟙 _ → Q.map (shiftMap p 1) ≫ Q.map (shiftMap p' 1) = 𝟙 _ →
      Q.map (q ≫ coneInclusion g₂) = Q.map (coneInclusion g₁ ≫ e) →
      Q.map (e ≫ coneProjection g₂) = Q.map (coneProjection g₁ ≫ shiftMap p 1) →
      Q.map (coneInclusion g₂ ≫ e') = Q.map (q' ≫ coneInclusion g₁) →
      Q.map (e' ≫ coneProjection g₁) = Q.map (coneProjection g₂ ≫ shiftMap p' 1) →
      IsIso (Q.map e ≫ Q.map e') := by
    intro X₁ Y₁ X₂ Y₂ g₁ g₂ p p' q q' e e' hq hp hi hπ hi' hπ'
    simp only [Functor.map_comp] at hi hπ hi' hπ'
    rw [← Functor.map_comp]
    refine isIso_of_homotopic_identity_on_cone g₁ (e ≫ e') (hom ?_) (hom ?_)
    · show Q.map (coneInclusion g₁) ≫ Q.map e ≫ Q.map e' = _
      rw [← Category.assoc, ← hi, Category.assoc, hi', ← Category.assoc, hq, Category.id_comp]
    · show Q.map e ≫ Q.map e' ≫ Q.map (coneProjection g₁) = _
      rw [hπ', ← Category.assoc, hπ, Category.assoc, hp, Category.comp_id]
  obtain ⟨aInv, haInv⟩ := Q.map_surjective (inv (Q.map a))
  obtain ⟨bInv, hbInv⟩ := Q.map_surjective (inv (Q.map b))
  have hB₁ : Q.map b ≫ Q.map bInv = 𝟙 _ := by rw [hbInv, IsIso.hom_inv_id]
  have hB₂ : Q.map bInv ≫ Q.map b = 𝟙 _ := by rw [hbInv, IsIso.inv_hom_id]
  have hA₁ : Homotopic (a ≫ aInv) (Hom.id K₁) := hom (by
    rw [Q.map_comp, haInv, IsIso.hom_inv_id]
    exact (Q.map_id K₁).symm)
  have hA₂ : Homotopic (aInv ≫ a) (Hom.id K₂) := hom (by
    rw [Q.map_comp, haInv, IsIso.inv_hom_id]
    exact (Q.map_id K₂).symm)
  have hsq : Q.map a ≫ Q.map f₂ = Q.map f₁ ≫ Q.map b := by
    rw [← Q.map_comp, ← Q.map_comp]
    exact qeq h₁
  have hRev : Homotopic (f₂ ≫ bInv) (aInv ≫ f₁) := hom (by
    rw [Q.map_comp, Q.map_comp, haInv, hbInv, IsIso.eq_inv_comp, ← Category.assoc, hsq,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id])
  obtain ⟨c', hcInc, hcProj⟩ :=
    exists_mappingConeMap_of_homotopic_square f₂ f₁ aInv bInv hRev
  have hcc' : IsIso (Q.map c ≫ Q.map c') := key f₁ f₂ c c' hB₁ (hshift hA₁)
    (qeq h₂) (qeq h₃) (congrArg Q.map hcInc) (congrArg Q.map hcProj)
  have hc'c : IsIso (Q.map c' ≫ Q.map c) := key f₂ f₁ c' c hB₂ (hshift hA₂)
    (congrArg Q.map hcInc).symm (congrArg Q.map hcProj) (qeq h₂).symm (qeq h₃)
  have : IsSplitMono (Q.map c) :=
    IsSplitMono.mk' ⟨Q.map c' ≫ inv (Q.map c ≫ Q.map c'), by
      rw [← Category.assoc, IsIso.hom_inv_id]⟩
  have : IsSplitEpi (Q.map c) :=
    IsSplitEpi.mk' ⟨inv (Q.map c' ≫ Q.map c) ≫ Q.map c', by
      rw [Category.assoc, IsIso.inv_hom_id]⟩
  exact isIso_of_mono_of_isSplitEpi _

end DifferentialGradedModule
