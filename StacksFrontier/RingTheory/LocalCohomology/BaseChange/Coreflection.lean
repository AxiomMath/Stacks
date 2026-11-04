module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksCore.Tactic.StacksAttribute

/-!
# Coreflection along a finite family of idempotent localizations, and its transport

Let `𝒞` be a pretriangulated category and let `F i`, for `i` in a finite set, be exact
endofunctors equipped with natural transformations `η i : 𝟭 ⟶ F i` which are *idempotent
localizations*: `η i` is invertible on objects in the image of `F i`, and `F i` inverts
`η i`. Iterating the fibre of `η i` produces, for every object `X`, the universal object `Y`
with all `F i Y = 0` mapping to `X`.

The point of this file is that the construction is carried along any exact functor
`L : 𝒞 ⥤ 𝒟` which intertwines the two families: if `L (F i X) ≅ G i (L X)` for a second such
family `G i` on `𝒟`, then `L Y → L X` is again the universal object with all `G i` vanishing.
No compatibility of `L` with the units is needed, because the universal property of the fibre
only uses that the third object of the triangle lies in the image of the localization.

## Main results

* `Stacks.LocalCohomology.bijective_of_fiber` — the universal property of the first object of
  a distinguished triangle whose third object is in the image of an idempotent localization.
* `Stacks.LocalCohomology.exists_coreflection_transport` — the coreflection and its transport.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.LocalCohomology

/-- A morphism from an object killed by an idempotent localization `F` into an object in the
image of `F` vanishes. -/
lemma hom_eq_zero_of_localization {C : Type*} [Category C] [HasZeroMorphisms C]
    (F : C ⥤ C) (η : 𝟭 C ⟶ F) (hη : ∀ X, IsIso (η.app (F.obj X)))
    {T X : C} (hT : IsZero (F.obj T)) (g : T ⟶ F.obj X) : g = 0 := by
  have := hη X
  apply (cancel_mono (η.app (F.obj X))).1
  rw [zero_comp, ← Functor.id_map (f := g), η.naturality]
  rw [hT.eq_of_tgt (η.app T) 0, zero_comp]

section Fibre

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **The universal property of a fibre.** If the third object of a distinguished triangle is
isomorphic to an object in the image of an idempotent localization `F`, then its first object
is universal among objects killed by `F` mapping to its second object. -/
lemma bijective_of_fiber (F : C ⥤ C) [F.Additive] [F.CommShift ℤ] (η : 𝟭 C ⟶ F)
    (hη : ∀ X, IsIso (η.app (F.obj X))) (T : Triangle C) (hT : T ∈ distTriang C)
    (X : C) (e : T.obj₃ ≅ F.obj X) (W : C) (hW : IsZero (F.obj W)) :
    Function.Bijective (fun g : W ⟶ T.obj₁ => g ≫ T.mor₁) := by
  have hz : ∀ k : W ⟶ T.obj₃, k = 0 := fun k =>
    (cancel_mono e.hom).1 (by rw [zero_comp]; exact hom_eq_zero_of_localization F η hη hW _)
  have hz' : ∀ k : W ⟶ T.obj₃⟦(-1 : ℤ)⟧, k = 0 := by
    intro k
    apply (cancel_mono ((shiftFunctor C (-1 : ℤ)).map e.hom)).1
    apply (cancel_mono ((F.commShiftIso (-1 : ℤ)).inv.app X)).1
    rw [zero_comp, zero_comp]
    exact hom_eq_zero_of_localization F η hη hW _
  have hker : ∀ k : W ⟶ T.obj₁, k ≫ T.mor₁ = 0 → k = 0 := by
    intro k hk
    obtain ⟨k', hk'⟩ := Triangle.coyoneda_exact₂ T.invRotate
      (inv_rot_of_distTriang _ hT) k hk
    rw [hk', hz' k']
    exact zero_comp
  refine ⟨?_, ?_⟩
  · intro k l hkl
    rw [← sub_eq_zero]
    apply hker
    change k ≫ T.mor₁ = l ≫ T.mor₁ at hkl
    rw [Preadditive.sub_comp, hkl, sub_self]
  · intro k
    obtain ⟨l, hl⟩ := Triangle.coyoneda_exact₂ T hT k (hz _)
    exact ⟨l, hl.symm⟩

/-- The fibre of the localization unit at `X`, as a distinguished triangle whose third object
is `F X` and whose first object is killed by `F`. -/
lemma exists_fiber_triangle (F : C ⥤ C) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (η : 𝟭 C ⟶ F) (hFη : ∀ X, IsIso (F.map (η.app X))) (X : C) :
    ∃ T : Triangle C, T ∈ distTriang C ∧ T.obj₂ = X ∧ T.obj₃ = F.obj X ∧
      IsZero (F.obj T.obj₁) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (η.app X)
  have hT' := inv_rot_of_distTriang _ hT
  exact ⟨_, hT', rfl, rfl, Triangle.isZero₁_of_isIso₂ _ (F.map_distinguished _ hT') (hFη X)⟩

end Fibre

section Transport

variable {C D : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [Category D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **The coreflection along a finite family of idempotent localizations, transported along an
exact functor.** For every object `X` there is a universal object `Y ⟶ X` with all `F i Y`
vanishing, and its image `L Y ⟶ L X` is again universal with all `G i` vanishing. -/
lemma exists_coreflection_transport
    {ι : Type*} (F : ι → C ⥤ C) [∀ i, (F i).Additive] [∀ i, (F i).CommShift ℤ]
    [∀ i, (F i).IsTriangulated]
    (η : ∀ i, 𝟭 C ⟶ F i) (hη : ∀ i X, IsIso ((η i).app ((F i).obj X)))
    (hFη : ∀ i X, IsIso ((F i).map ((η i).app X)))
    (hpres : ∀ i j X, IsZero ((F j).obj X) → IsZero ((F j).obj ((F i).obj X)))
    (G : ι → D ⥤ D) [∀ i, (G i).Additive] [∀ i, (G i).CommShift ℤ]
    (θ : ∀ i, 𝟭 D ⟶ G i) (hθ : ∀ i Y, IsIso ((θ i).app ((G i).obj Y)))
    (L : C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
    (comm : ∀ i X, L.obj ((F i).obj X) ≅ (G i).obj (L.obj X))
    (s : Finset ι) (X : C) :
    ∃ (Y : C) (c : Y ⟶ X),
      (∀ i ∈ s, IsZero ((F i).obj Y)) ∧
      (∀ W, (∀ i ∈ s, IsZero ((F i).obj W)) →
        Function.Bijective (fun g : W ⟶ Y => g ≫ c)) ∧
      (∀ i ∈ s, IsZero ((G i).obj (L.obj Y))) ∧
      (∀ W, (∀ i ∈ s, IsZero ((G i).obj W)) →
        Function.Bijective (fun g : W ⟶ L.obj Y => g ≫ L.map c)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨X, 𝟙 X, by simp, ?_, by simp, ?_⟩
      · intro W _
        exact ⟨fun _ _ h => by simpa only [Category.comp_id] using h,
          fun g => ⟨g, Category.comp_id g⟩⟩
      · intro W _
        rw [L.map_id]
        exact ⟨fun _ _ h => by simpa only [Category.comp_id] using h,
          fun g => ⟨g, Category.comp_id g⟩⟩
  | @insert i s _ ih =>
      obtain ⟨U, b, hU, hb, _, hGb⟩ := ih
      obtain ⟨T, hT, h₂, h₃, hFT⟩ := exists_fiber_triangle (F i) (η i) (hFη i) U
      let e : T.obj₂ ≅ U := eqToIso h₂
      have hY : ∀ j ∈ insert i s, IsZero ((F j).obj T.obj₁) := by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hFT
        · apply Triangle.isZero₁_of_isZero₂₃ _ ((F j).map_distinguished _ hT)
          · exact (hU j hj).of_iso ((F j).mapIso e)
          · rw [show ((F j).mapTriangle.obj T).obj₃ = (F j).obj T.obj₃ from rfl, h₃]
            exact hpres i j U (hU j hj)
      refine ⟨T.obj₁, T.mor₁ ≫ e.hom ≫ b, hY, ?_, ?_, ?_⟩
      · intro W hW
        have k₁ := bijective_of_fiber (F i) (η i) (hη i) T hT U (eqToIso h₃) W
          (hW i (Finset.mem_insert_self _ _))
        have k₂ : Function.Bijective (fun g : W ⟶ T.obj₂ => g ≫ e.hom) :=
          ⟨fun _ _ h => (cancel_mono e.hom).1 h, fun g => ⟨g ≫ e.inv, by simp⟩⟩
        have k₃ := hb W (fun j hj => hW j (Finset.mem_insert_of_mem hj))
        simpa only [Function.comp_def, Category.assoc] using k₃.comp (k₂.comp k₁)
      · intro j hj
        exact (L.map_isZero (hY j hj)).of_iso (comm j T.obj₁).symm
      · intro W hW
        have k₁ : Function.Bijective (fun g : W ⟶ L.obj T.obj₁ => g ≫ L.map T.mor₁) :=
          bijective_of_fiber (G i) (θ i) (hθ i) (L.mapTriangle.obj T)
            (L.map_distinguished T hT) (L.obj U)
            (L.mapIso (eqToIso h₃) ≪≫ comm i U) W (hW i (Finset.mem_insert_self _ _))
        have k₂ : Function.Bijective (fun g : W ⟶ L.obj T.obj₂ => g ≫ L.map e.hom) :=
          ⟨fun _ _ h => (cancel_mono (L.map e.hom)).1 h,
            fun g => ⟨g ≫ L.map e.inv, by
              simp only [Category.assoc, ← L.map_comp, e.inv_hom_id, L.map_id,
                Category.comp_id]⟩⟩
        have k₃ := hGb W (fun j hj => hW j (Finset.mem_insert_of_mem hj))
        simpa only [Function.comp_def, Category.assoc, Functor.map_comp] using
          k₃.comp (k₂.comp k₁)

end Transport

end Stacks.LocalCohomology

end
