module

public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit

/-!
# Carrying a pinned derived-limit triangle through a composite of exact functors

A derived limit `L = R lim Xₙ` in a pre-triangulated category is witnessed by a distinguished
triangle `L ⟶ ∏ Xₙ ⟶ ∏ Xₙ ⟶ L⟦1⟧` whose middle map is the difference map.  This file records how
such a triangle, with its first map pinned, is carried

* through a triangulated functor `G` preserving the product, then through the right derived
  functor `RF` of a product-preserving additive functor (Stacks 08U1): the new first map is the
  image of the old one followed by the product comparison of `G ⋙ RF`;
* along a map `ε : K ⟶ L` which becomes invertible after `G ⋙ RF`, so that `RF(G(K))` is again a
  derived limit, with first map the image of `ε ≫ p` followed by the product comparison.

## Main results

* `Stacks.Injectives.derivedLimitTriangle_precomp_iso`
* `Stacks.Injectives.derivedLimitTriangle_map_comp_rightDerivedFunctor`

## References

* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 0CTE](https://stacks.math.columbia.edu/tag/0CTE)
-/

@[expose] public section

namespace Stacks.Injectives

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w w₁ w₂ v₁ v₂ u₁ u₂

/-- **A derived-limit triangle may be precomposed with an isomorphism.**  If
`L ⟶ ∏ Xₙ ⟶ ∏ Xₙ ⟶ L⟦1⟧` is distinguished with first map `q`, then for `e : K ≅ L` the triangle
with first map `e.hom ≫ q`, the same middle map and connecting map `δ ≫ e.inv⟦1⟧'` is
distinguished. -/
theorem derivedLimitTriangle_precomp_iso {D : Type u₂} [Category.{v₂} D] [HasZeroObject D]
    [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {P : D} {K L : D} (e : K ≅ L) (q : L ⟶ P) (d : P ⟶ P) (δ : P ⟶ L⟦(1 : ℤ)⟧)
    (h : Triangle.mk q d δ ∈ distTriang D) :
    Triangle.mk (e.hom ≫ q) d (δ ≫ (shiftFunctor D (1 : ℤ)).map e.inv) ∈ distTriang D := by
  refine isomorphic_distinguished _ h _ (Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · simp
  · simp
  · simp [← Functor.map_comp]

section Composite

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [IsGrothendieckAbelian.{w} A]
  [HasProductsOfShape ℕ B] [HasExactLimitsOfShape (Discrete ℕ) B]
  (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

include F α in
/-- **A pinned derived-limit triangle through `G` and then a right derived functor, precomposed
with a map inverted by the composite.**  Let `L ⟶ ∏ Xₙ` be the first map `p` of a derived-limit
triangle in `C`, let `G : C ⥤ D(A)` be triangulated and preserve the product, let `RF` be the
right derived functor of a product-preserving additive functor `F : A ⥤ B` (Stacks 08U1), and let
`ε : K ⟶ L` become invertible after `G ⋙ RF`.  Then `RF(G(K))` is a derived limit of the system
`X ⋙ G ⋙ RF`, with first map `(G ⋙ RF)(ε ≫ p)` followed by the product comparison of `G ⋙ RF`. -/
theorem derivedLimitTriangle_map_comp_rightDerivedFunctor
    (G : C ⥤ DerivedCategory A) [G.CommShift ℤ] [G.IsTriangulated]
    (X : ℕᵒᵖ ⥤ C) [HasProduct fun n : ℕ ↦ X.obj ⟨n⟩]
    [PreservesLimit (Discrete.functor (fun n : ℕ ↦ X.obj ⟨n⟩)) G]
    [HasProduct fun n : ℕ ↦ G.obj (X.obj ⟨n⟩)]
    {K L : C} (ε : K ⟶ L) [IsIso (RF.map (G.map ε))]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ X.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ ↦ X.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ X.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ X.obj ⟨n⟩) (n + 1) ≫
          X.map (homOfLE (Nat.le_succ n)).op) δ ∈ distTriang C) :
    ∃ h : HasProduct (fun n : ℕ ↦ RF.obj (G.obj (X.obj ⟨n⟩))),
      letI := h
      ∃ δ : (∏ᶜ fun n : ℕ ↦ RF.obj (G.obj (X.obj ⟨n⟩))) ⟶ (RF.obj (G.obj K))⟦(1 : ℤ)⟧,
        Triangle.mk (RF.map (G.map (ε ≫ p)) ≫
            Pi.lift fun n : ℕ ↦ RF.map (G.map (Pi.π (fun n : ℕ ↦ X.obj ⟨n⟩) n)))
          (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ RF.obj (G.obj (X.obj ⟨n⟩))) n -
            Pi.π (fun n : ℕ ↦ RF.obj (G.obj (X.obj ⟨n⟩))) (n + 1) ≫
              RF.map (G.map (X.map (homOfLE (Nat.le_succ n)).op))) δ ∈
          distTriang (DerivedCategory B) := by
  obtain ⟨δ₁, h₁⟩ := isDerivedLimit_map_of_preservesProduct G X L p hp
  have : HasProduct fun n : ℕ ↦ (X ⋙ G).obj ⟨n⟩ :=
    inferInstanceAs (HasProduct fun n : ℕ ↦ G.obj (X.obj ⟨n⟩))
  obtain ⟨h, δ₂, h₂⟩ := isDerivedLimit_map_rightDerivedFunctor F RF α (X ⋙ G) (G.obj L)
    (G.map p ≫ piComparison G (fun n : ℕ ↦ X.obj ⟨n⟩)) ⟨δ₁, h₁⟩
  let := h
  have h' : HasProduct fun n : ℕ ↦ RF.obj (G.obj (X.obj ⟨n⟩)) := h
  refine ⟨h', δ₂ ≫ (shiftFunctor _ (1 : ℤ)).map (asIso (RF.map (G.map ε))).inv, ?_⟩
  have hc : RF.map (G.map (ε ≫ p)) ≫
        (Pi.lift fun n : ℕ ↦ RF.map (G.map (Pi.π (fun n : ℕ ↦ X.obj ⟨n⟩) n))) =
      (asIso (RF.map (G.map ε))).hom ≫
        (RF.map (G.map p ≫ piComparison G (fun n : ℕ ↦ X.obj ⟨n⟩)) ≫
          piComparison RF (fun n : ℕ ↦ (X ⋙ G).obj ⟨n⟩)) := by
    refine Pi.hom_ext _ _ fun n => ?_
    simp only [Functor.map_comp, Category.assoc, asIso_hom, Pi.lift_comp_π, piComparison_comp_π,
      Functor.comp_obj]
    rw [← RF.map_comp (piComparison G _), piComparison_comp_π, ← RF.map_comp]
  rw [hc]
  exact derivedLimitTriangle_precomp_iso _ _ _ _ h₂

end Composite

section Orthogonal

variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **The cone of a coreflection-type map is right orthogonal.**  Let `P` be a class of objects
stable under shifts and `ε : K ⟶ L` a map through which every map from an object of `P` to `L`
factors uniquely.  Then the third object `C` of a distinguished triangle `K ⟶ L ⟶ C ⟶ K⟦1⟧` on
`ε` receives only the zero map from every shift of every object of `P`. -/
theorem eq_zero_of_isUniversal_of_distTriang (P : D → Prop) (hP : ∀ (M : D) (n : ℤ), P M → P (M⟦n⟧))
    {K L : D} (ε : K ⟶ L) (hε : ∀ M : D, P M → Function.Bijective fun g : M ⟶ K => g ≫ ε)
    (T : Triangle D) (hT : T ∈ distTriang D) (h₁ : T.obj₁ = K) (h₂ : T.obj₂ = L)
    (hmor : T.mor₁ = eqToHom h₁ ≫ ε ≫ eqToHom h₂.symm)
    {M : D} (hM : P M) (n : ℤ) (φ : M ⟶ T.obj₃⟦n⟧) : φ = 0 := by
  subst h₁ h₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hmor
  subst hmor
  -- first, every map `M ⟶ T.obj₃` from an object of `P` vanishes
  have key : ∀ (M : D), P M → ∀ ψ : M ⟶ T.obj₃, ψ = 0 := by
    intro M hM ψ
    -- `ψ ≫ T.mor₃ : M ⟶ K⟦1⟧` vanishes, by the universal property at `M⟦-1⟧`
    have h₃ : ψ ≫ T.mor₃ = 0 := by
      set a := ψ ≫ T.mor₃
      have ha : a ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 := by
        simp only [a, Category.assoc, comp_distTriang_mor_zero₃₁ T hT, Limits.comp_zero]
      let i := shiftFunctorCompIsoId D (1 : ℤ) (-1) (by omega)
      let b : M⟦(-1 : ℤ)⟧ ⟶ T.obj₁ := (shiftFunctor D (-1 : ℤ)).map a ≫ i.hom.app T.obj₁
      have hb : b ≫ T.mor₁ = 0 ≫ T.mor₁ := by
        rw [Limits.zero_comp]
        have hn : i.hom.app T.obj₁ ≫ T.mor₁ =
            (shiftFunctor D (-1 : ℤ)).map ((shiftFunctor D (1 : ℤ)).map T.mor₁) ≫
              i.hom.app T.obj₂ := (i.hom.naturality T.mor₁).symm
        simp only [b, Category.assoc]
        rw [hn, ← Functor.map_comp_assoc, ha, Functor.map_zero, Limits.zero_comp]
      have hb0 : b = 0 := (hε _ (hP M (-1) hM)).1 hb
      rwa [Preadditive.IsIso.comp_right_eq_zero, Functor.map_eq_zero_iff] at hb0
    obtain ⟨χ, hχ⟩ := Triangle.coyoneda_exact₃ T hT ψ h₃
    obtain ⟨χ', rfl⟩ := (hε M hM).2 χ
    rw [hχ, Category.assoc, comp_distTriang_mor_zero₁₂ T hT, Limits.comp_zero]
  -- then shift back
  have h0 := key _ (hP M (-n) hM)
    ((shiftFunctor D (-n)).map φ ≫ (shiftFunctorCompIsoId D n (-n) (by omega)).hom.app T.obj₃)
  rwa [Preadditive.IsIso.comp_right_eq_zero, Functor.map_eq_zero_iff] at h0

end Orthogonal

end Stacks.Injectives
