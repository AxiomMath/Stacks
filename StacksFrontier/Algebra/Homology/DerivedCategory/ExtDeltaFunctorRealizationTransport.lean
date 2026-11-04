module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExtDeltaFunctorRealization
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Realizing a map of `Ext` `δ`-functors through a fully faithful exact functor

Let `F : C₁ ⥤ C₂` be an exact functor of abelian categories whose derived functor
`F̃ : D(C₁) ⥤ D(C₂)` is fully faithful, and let `B` be the property of objects of `C₂` that are
isomorphic to some `F(M)` (for `C₁ = Mod(A)`, `C₂ = Mod(𝒪_{Spec A})` and `F` the functor
`M ↦ M^~`, the quasi-coherent modules). This file transports
`Stacks.ExtDeltaFunctorRealization.exists_isIso_eq_comp_of_isLE` along `F̃`: if `L ≅ F̃(L₀)` and
`L' ≅ F̃(L₀')` with `L₀`, `L₀'` bounded above, then every family of bijections
`Hom_{D(C₂)}(L, G[n]) → Hom_{D(C₂)}(L', G[n])`, for `G` satisfying `B`, natural in `G` and
compatible with the connecting morphisms of short exact sequences whose outer terms satisfy `B`,
is composition with an isomorphism `L' ≅ L`.

The family is pulled back to `C₁` through the bijections
`Hom_{D(C₁)}(L₀, M[n]) ≃ Hom_{D(C₂)}(L, F(M)[n])` given by `F̃`, the comparison
`F̃(M[0]) ≅ F(M)[0]` (`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`) and the
commutation of `F̃` with the shift; the connecting morphisms correspond by
`CategoryTheory.ShortComplex.ShortExact.mapShiftedHom_singleδ`.

## Main results

* `Stacks.ExtDeltaFunctorRealization.exists_isIso_eq_comp_of_fullyFaithful_mapDerivedCategory`
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Preadditive Pretriangulated DerivedCategory

namespace Stacks.ExtDeltaFunctorRealization

section ShiftedHomAlgebra

variable {D : Type*} [Category D] [HasShift D ℤ]

/-- Precomposing a shifted morphism `y : X ⟶ Y⟦a⟧` with `u : X' ⟶ X` commutes with the composition
of shifted morphisms: `(u ≫ y).comp z h = u ≫ y.comp z h`. -/
lemma shiftedHom_comp_comp_left {X X' Y Z : D} {a b c : ℤ} (u : X' ⟶ X) (y : ShiftedHom X Y a)
    (z : ShiftedHom Y Z b) (h : b + a = c) :
    ShiftedHom.comp (u ≫ y : ShiftedHom X' Y a) z h = u ≫ ShiftedHom.comp y z h := by
  simp [ShiftedHom.comp]

/-- For shifted morphisms `y : X ⟶ Y⟦a⟧`, `z : Y ⟶ Z⟦b⟧` and `w : Z ⟶ Z'`, postcomposing
`y.comp z h` with `w⟦c⟧'` is the composition of `y` with `z ≫ w⟦b⟧'`. -/
lemma shiftedHom_comp_comp_shift {X Y Z Z' : D} {a b c : ℤ} (y : ShiftedHom X Y a)
    (z : ShiftedHom Y Z b) (h : b + a = c) (w : Z ⟶ Z') :
    ShiftedHom.comp y z h ≫ w⟦c⟧' = ShiftedHom.comp y (z ≫ w⟦b⟧' : ShiftedHom Y Z' b) h := by
  simp only [ShiftedHom.comp, assoc, Functor.map_comp]
  congr 2
  exact ((shiftFunctorAdd' D b a c h).inv.naturality w).symm

/-- For shifted morphisms `y : X ⟶ Y⟦a⟧`, `z : Y' ⟶ Z⟦b⟧` and `v : Y ⟶ Y'`, the composition of
`y` with `v ≫ z` is the composition of `y ≫ v⟦a⟧'` with `z`. -/
lemma shiftedHom_comp_shift_comp {X Y Y' Z : D} {a b c : ℤ} (y : ShiftedHom X Y a) (v : Y ⟶ Y')
    (z : ShiftedHom Y' Z b) (h : b + a = c) :
    ShiftedHom.comp y (v ≫ z : ShiftedHom Y Z b) h =
      ShiftedHom.comp (y ≫ v⟦a⟧' : ShiftedHom X Y' a) z h := by
  simp [ShiftedHom.comp]

end ShiftedHomAlgebra

variable {C₁ C₂ : Type*} [Category C₁] [Abelian C₁] [Category C₂] [Abelian C₂]
  [hC₁ : HasDerivedCategory C₁] [hC₂ : HasDerivedCategory C₂]

/-- **Transport of the realization along a fully faithful derived functor.** Let `F : C₁ ⥤ C₂` be
exact with `F̃ : D(C₁) ⥤ D(C₂)` fully faithful, `C₁` with enough projectives and injectives, and
`B` a property of objects of `C₂` satisfied exactly by the objects isomorphic to some `F(M)`.
Let `L ≅ F̃(L₀)`, `L' ≅ F̃(L₀')` with `L₀`, `L₀'` bounded above. Then a family of bijections
`φ_n(G) : Hom(L, G[n]) → Hom(L', G[n])` for `G` satisfying `B`, natural in `G` and compatible
with the connecting morphisms of short exact sequences whose outer terms satisfy `B`, is
composition with an isomorphism `L' ⟶ L`. -/
theorem exists_isIso_eq_comp_of_fullyFaithful_mapDerivedCategory
    [EnoughProjectives C₁] [EnoughInjectives C₁]
    (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : F.mapDerivedCategory.FullyFaithful)
    (B : ObjectProperty C₂) (hB : ∀ M : C₁, B (F.obj M))
    (hB' : ∀ G : C₂, B G → ∃ M : C₁, Nonempty (F.obj M ≅ G))
    {L L' : DerivedCategory C₂} {L₀ L₀' : DerivedCategory C₁} (a a' : ℤ) [L₀.IsLE a]
    [L₀'.IsLE a'] (e : L ≅ F.mapDerivedCategory.obj L₀) (e' : L' ≅ F.mapDerivedCategory.obj L₀')
    (φ : ∀ (n : ℤ) (G : C₂), B G → (L ⟶ ((singleFunctor C₂ 0).obj G)⟦n⟧) →
      (L' ⟶ ((singleFunctor C₂ 0).obj G)⟦n⟧))
    (hnat : ∀ (n : ℤ) {G G' : C₂} (hG : B G) (hG' : B G') (f : G ⟶ G')
      (x : L ⟶ ((singleFunctor C₂ 0).obj G)⟦n⟧),
      φ n G' hG' (x ≫ ((singleFunctor C₂ 0).map f)⟦n⟧') =
        φ n G hG x ≫ ((singleFunctor C₂ 0).map f)⟦n⟧')
    (hδ : ∀ {S : ShortComplex C₂} (hS : S.ShortExact) (h₁ : B S.X₁) (h₃ : B S.X₃) (n m : ℤ)
      (hnm : 1 + n = m) (x : ShiftedHom L ((singleFunctor C₂ 0).obj S.X₃) n),
      φ m S.X₁ h₁ (x.comp hS.singleδ hnm) = ShiftedHom.comp (φ n S.X₃ h₃ x) hS.singleδ hnm)
    (hbij : ∀ (n : ℤ) (G : C₂) (hG : B G), Function.Bijective (φ n G hG)) :
    ∃ g : L' ⟶ L, IsIso g ∧ ∀ (n : ℤ) (G : C₂) (hG : B G)
      (x : L ⟶ ((singleFunctor C₂ 0).obj G)⟦n⟧), φ n G hG x = g ≫ x := by
  -- the translation of morphism groups
  let up₀ : ∀ {K : DerivedCategory C₁} (n : ℤ) (M : C₁),
      (K ⟶ ((singleFunctor C₁ 0).obj M)⟦n⟧) →
        (F.mapDerivedCategory.obj K ⟶ ((singleFunctor C₂ 0).obj (F.obj M))⟦n⟧) :=
    fun n M x ↦ (ShiftedHom.map (x : ShiftedHom _ _ n) F.mapDerivedCategory :
        F.mapDerivedCategory.obj _ ⟶ _) ≫ ((F.mapDerivedCategorySingleFunctor 0).hom.app M)⟦n⟧'
  have up₀_bij : ∀ {K : DerivedCategory C₁} (n : ℤ) (M : C₁),
      Function.Bijective (up₀ (K := K) n M) := by
    intro K n M
    refine ⟨fun x y hxy ↦ ?_, fun z ↦ ?_⟩
    · simp only [up₀, ShiftedHom.map, cancel_mono] at hxy
      exact hF.map_injective hxy
    · obtain ⟨x, hx⟩ := hF.map_surjective (z ≫
        ((F.mapDerivedCategorySingleFunctor 0).inv.app M)⟦n⟧' ≫
          (F.mapDerivedCategory.commShiftIso n).inv.app _)
      refine ⟨x, ?_⟩
      simp only [up₀, ShiftedHom.map]
      rw [hx, assoc, assoc, assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
        Iso.inv_hom_id_app]
      simp
  let up : ∀ {L : DerivedCategory C₂} {K : DerivedCategory C₁}
      (_ : L ≅ F.mapDerivedCategory.obj K) (n : ℤ) (M : C₁),
      (K ⟶ ((singleFunctor C₁ 0).obj M)⟦n⟧) ≃ (L ⟶ ((singleFunctor C₂ 0).obj (F.obj M))⟦n⟧) :=
    fun e n M ↦ (Equiv.ofBijective _ (up₀_bij n M)).trans (e.homCongr (Iso.refl _)).symm
  have up_apply : ∀ {L K} (e : L ≅ F.mapDerivedCategory.obj K) n M x,
      up e n M x = e.hom ≫ up₀ n M x := fun e n M x ↦ by
    simp [up, Iso.homCongr]
  have up_nat : ∀ {L K} (e : L ≅ F.mapDerivedCategory.obj K) (n : ℤ) {M M' : C₁} (f : M ⟶ M')
      (x : K ⟶ ((singleFunctor C₁ 0).obj M)⟦n⟧),
      up e n M' (x ≫ ((singleFunctor C₁ 0).map f)⟦n⟧') =
        up e n M x ≫ ((singleFunctor C₂ 0).map (F.map f))⟦n⟧' := by
    intro L K e n M M' f x
    simp only [up_apply, up₀, ShiftedHom.map, Functor.map_comp, assoc]
    rw [Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, ← Functor.map_comp]
    congr 4
    exact (F.mapDerivedCategorySingleFunctor 0).hom.naturality f
  have up_δ : ∀ {L K} (e : L ≅ F.mapDerivedCategory.obj K) {S : ShortComplex C₁}
      (hS : S.ShortExact) (n m : ℤ) (hnm : 1 + n = m) (x : K ⟶ ((singleFunctor C₁ 0).obj S.X₃)⟦n⟧),
      up e m S.X₁ (ShiftedHom.comp (x : ShiftedHom _ _ n) hS.singleδ hnm) =
        ShiftedHom.comp (up e n S.X₃ x : ShiftedHom _ _ n) (hS.map_of_exact F).singleδ hnm := by
    intro L K e S hS n m hnm x
    have hinner : ((F.mapDerivedCategorySingleFunctor 0).hom.app S.X₃ ≫
        (hS.map_of_exact F).singleδ ≫
          ((F.mapDerivedCategorySingleFunctor 0).inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app S.X₁)⟦(1 : ℤ)⟧' =
        (F.mapDerivedCategorySingleFunctor 0).hom.app S.X₃ ≫ (hS.map_of_exact F).singleδ := by
      simp only [assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
      simp
    simp only [up_apply, up₀]
    rw [ShiftedHom.map_comp, hS.mapShiftedHom_singleδ,
      shiftedHom_comp_comp_shift, hinner, shiftedHom_comp_shift_comp,
      ← shiftedHom_comp_comp_left]
  let ψ : ∀ (n : ℤ) (M : C₁), (L₀ ⟶ ((singleFunctor C₁ 0).obj M)⟦n⟧) →
      (L₀' ⟶ ((singleFunctor C₁ 0).obj M)⟦n⟧) :=
    fun n M x ↦ (up e' n M).symm (φ n (F.obj M) (hB M) (up e n M x))
  have hψ : ∀ n M x, up e' n M (ψ n M x) = φ n (F.obj M) (hB M) (up e n M x) :=
    fun n M x ↦ Equiv.apply_symm_apply _ _
  obtain ⟨g₀, hg₀, hg₀ψ⟩ := exists_isIso_eq_comp_of_isLE L₀ L₀' a a' ψ
    (fun n M M' f x ↦ (up e' n M').injective (by
      rw [hψ, up_nat, hnat n (hB M) (hB M'), up_nat, hψ]))
    (fun {S} hS n m hnm x ↦ (up e' m S.X₁).injective (by
      rw [hψ, up_δ]
      refine (hδ (hS.map_of_exact F) (hB _) (hB _) n m hnm _).trans ?_
      rw [up_δ, hψ]
      rfl))
    (fun n M _ ↦ (up e' n M).symm.bijective.comp ((hbij n _ _).comp (up e n M).bijective))
  let g : L' ⟶ L := e'.hom ≫ F.mapDerivedCategory.map g₀ ≫ e.inv
  have hg : ∀ n M (x : L ⟶ ((singleFunctor C₂ 0).obj (F.obj M))⟦n⟧),
      φ n (F.obj M) (hB M) x = g ≫ x := by
    intro n M x
    obtain ⟨x, rfl⟩ := (up e n M).surjective x
    rw [← hψ, hg₀ψ, up_apply, up_apply]
    simp [g, up₀, ShiftedHom.map]
  refine ⟨g, inferInstance, fun n G hG x ↦ ?_⟩
  obtain ⟨M, ⟨α⟩⟩ := hB' G hG
  have hx : x = (x ≫ ((singleFunctor C₂ 0).map α.inv)⟦n⟧') ≫
      ((singleFunctor C₂ 0).map α.hom)⟦n⟧' := by
    rw [assoc, ← Functor.map_comp, ← Functor.map_comp, α.inv_hom_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, comp_id]
  rw [hx, hnat n (hB M) hG, hg, assoc]

end Stacks.ExtDeltaFunctorRealization
