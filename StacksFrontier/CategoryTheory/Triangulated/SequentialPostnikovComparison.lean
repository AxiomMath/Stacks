module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import StacksFrontier.CategoryTheory.Triangulated.SequentialPostnikovSystems

/-!
# Comparing the images of two sequential Postnikov systems

Let `Φ : C₁ ⥤ D` and `Ψ : C₂ ⥤ D` be triangulated functors, and let `P` and `Q` be sequential
Postnikov systems in `C₁` and `C₂` for complexes `… ⟶ X₁ ⟶ X₀` and `… ⟶ X'₁ ⟶ X'₀`. If the
images `Φ Xₙ` and `Ψ X'ₙ` are isomorphic compatibly with the differentials, and every
`Hom(Φ Xᵢ[t], Ψ X'ⱼ)` with `t > 0` vanishes, then the two systems `n ↦ Φ(Yₙ)[n]` and
`n ↦ Ψ(Y'ₙ)[n]` over `ℕ` are isomorphic. This is the uniqueness half of [Stacks, Tag 0D83],
applied to the images of the two systems, and it is the step of the construction of
[Stacks, Section 0G07] that identifies the transform of the totalization of
`ℰᵢ ⊠ F(𝒢ᵢ)` with the image under `F` of the transform of the totalization of `ℰᵢ ⊠ 𝒢ᵢ`.

The second construction lifts a sequential Postnikov system all of whose objects lie in a
triangulated subcategory into that subcategory; it is what lets a functor defined only on the
subcategory, such as a functor on perfect complexes, be applied to it.

## Main definitions

* `CategoryTheory.Triangulated.SequentialPostnikovSystem.lift`: a sequential Postnikov system
  with all terms and objects in a triangulated subcategory, read in that subcategory.

## Main results

* `CategoryTheory.Triangulated.SequentialPostnikovSystem.nonempty_sequence_comp_iso`: the
  comparison of the images of two sequential Postnikov systems.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.Triangulated

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C₁ : Type u₁} [Category.{v₁} C₁] [HasZeroObject C₁] [Preadditive C₁] [HasShift C₁ ℤ]
  [∀ t : ℤ, (shiftFunctor C₁ t).Additive] [Pretriangulated C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [HasZeroObject C₂] [Preadditive C₂] [HasShift C₂ ℤ]
  [∀ t : ℤ, (shiftFunctor C₂ t).Additive] [Pretriangulated C₂]
  {D : Type u₃} [Category.{v₃} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ t : ℤ, (shiftFunctor D t).Additive] [Pretriangulated D]

/-- **The images of two sequential Postnikov systems over isomorphic image complexes are
isomorphic systems.** For triangulated functors `Φ` and `Ψ`, sequential Postnikov systems `P` and
`Q`, isomorphisms `e n : Φ Xₙ ≅ Ψ X'ₙ` compatible with the differentials, and the vanishing of
every `Hom(Φ Xᵢ[t], Ψ X'ⱼ)` with `t > 0`, the systems `n ↦ Φ(Yₙ[n])` and `n ↦ Ψ(Y'ₙ[n])` over
`ℕ` are isomorphic. -/
theorem SequentialPostnikovSystem.nonempty_sequence_comp_iso {X : ℕ → C₁}
    {d : ∀ n, X (n + 1) ⟶ X n} {X' : ℕ → C₂} {d' : ∀ n, X' (n + 1) ⟶ X' n}
    (P : SequentialPostnikovSystem X d) (Q : SequentialPostnikovSystem X' d')
    (Φ : C₁ ⥤ D) [Φ.Additive] [Φ.CommShift ℤ] [Φ.IsTriangulated]
    (Ψ : C₂ ⥤ D) [Ψ.Additive] [Ψ.CommShift ℤ] [Ψ.IsTriangulated]
    (e : ∀ n, Φ.obj (X n) ≅ Ψ.obj (X' n))
    (he : ∀ n, Φ.map (d n) ≫ (e n).hom = (e (n + 1)).hom ≫ Ψ.map (d' n))
    (h : ∀ (i j t : ℕ), 0 < t → ∀ f : (Φ.obj (X i))⟦(t : ℤ)⟧ ⟶ Ψ.obj (X' j), f = 0) :
    Nonempty (P.sequence ⋙ Φ ≅ Q.sequence ⋙ Ψ) := by
  obtain ⟨γ, -, -, hγ⟩ := (P.map Φ).exists_iso (Q.map Ψ) h e he
  exact ⟨P.sequenceMapIso Φ ≪≫ (P.map Φ).sequenceIso (Q.map Ψ) γ hγ ≪≫
    (Q.sequenceMapIso Ψ).symm⟩

/-- **A sequential Postnikov system whose terms and objects lie in a triangulated subcategory**
`S` is a sequential Postnikov system in `S`: a triangle of `S` is distinguished exactly when its
image in the ambient category is. -/
noncomputable def SequentialPostnikovSystem.lift (S : ObjectProperty C₁) [S.IsTriangulated]
    {X : ℕ → C₁} {d : ∀ n, X (n + 1) ⟶ X n} (P : SequentialPostnikovSystem X d)
    (hX : ∀ n, S (X n)) (hY : ∀ n, S (P.obj n)) :
    SequentialPostnikovSystem (fun n => (⟨X n, hX n⟩ : S.FullSubcategory))
      (fun n => ObjectProperty.homMk (d n)) where
  obj n := ⟨P.obj n, hY n⟩
  π n := ObjectProperty.homMk (P.π n)
  isIso_π_zero := by
    have : IsIso ((S.ι).map (ObjectProperty.homMk (P.π 0) :
        (⟨P.obj 0, hY 0⟩ : S.FullSubcategory) ⟶ ⟨X 0, hX 0⟩)) := by
      change IsIso (P.π 0)
      infer_instance
    exact isIso_of_fully_faithful S.ι _
  p n := ObjectProperty.homMk (P.p n)
  δ n := ObjectProperty.homMk (P.δ n ≫ ((S.ι.commShiftIso (1 : ℤ)).app
    (⟨P.obj (n + 1), hY (n + 1)⟩ : S.FullSubcategory)).inv)
  distinguished n := by
    change S.ι.mapTriangle.obj _ ∈ distTriang C₁
    refine isomorphic_distinguished _ (P.distinguished n) _
      (Triangle.isoMk _ _ (Iso.refl (P.obj (n + 1))) (Iso.refl (X (n + 1))) (Iso.refl (P.obj n))
        ?_ ?_ ?_)
    · exact (Category.comp_id _).trans (Category.id_comp (P.π (n + 1))).symm
    · exact (Category.comp_id _).trans (Category.id_comp (P.p n)).symm
    · simp [Functor.mapTriangle]
  p_comp_π n := by
    ext
    exact P.p_comp_π n

end CategoryTheory.Triangulated
