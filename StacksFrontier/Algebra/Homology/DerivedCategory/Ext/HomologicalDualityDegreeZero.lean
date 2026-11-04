module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.HomologicalDualityExt
public import StacksFrontier.Algebra.Homology.DerivedCategory.TopTruncationExtDegreeZero
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial

/-!
# Duality pairings through a triangulated functor which is exact in degree zero

Let `Φ : D⁺(𝒜) ⥤ D⁺(ℬ)` be a triangulated functor carrying every `X[0]` to an object living in
degree `0` only, and `G ≅ H⁰(Φ((-)[0]))` the induced exact functor `𝒜 ⥤ ℬ` (for instance `Φ = Rj_!`
and `G = j_!` for an open immersion `j`). Then `Φ(X[0]) ≅ G(X)[0]`
(`Stacks.HomologicalDuality.degreeZeroIso`), and this identification carries `Φ` of the class of
`e ∈ Ext^m_𝒜(X, Y)` to the class of `G(e)` (`Stacks.HomologicalDuality.extPlus_map_degreeZeroIso`,
the case `n = 0` of `Stacks.TopTruncationExt.map_comp_topProj`).

So if `G` induces bijections `Ext^m_𝒜(F, D₀) ≅ Ext^m_ℬ(G F, G D₀)`, the duality pairing of
`Hom_{D⁺(ℬ)}(O[0], Φ(-))` at `F[0]`, with dualizing object `D₀[0]`, is the Yoneda pairing
`Ext^i_ℬ(O, G F) × Ext^j_ℬ(G F, G D₀) → Ext^N_ℬ(O, G D₀) → B`
(`Stacks.HomologicalDuality.isPerfect_degreeZero_iff`,
`Stacks.HomologicalDuality.isDualityPerfect_of_isPerfect_degreeZero`,
`Stacks.HomologicalDuality.isPerfect_degreeZero_of_isDualityPerfect`). For a compactification
`j : V → X̄` this reads Poincaré duality on `V`, for complexes, as Yoneda duality of sheaves on
`X̄`, in the fibration step of Poincaré duality in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.HomologicalDuality.extPlusAddEquiv`.
* `Stacks.HomologicalDuality.degreeZeroIso`.
* `Stacks.HomologicalDuality.degreeZeroTheta`.

## Main results

* `Stacks.HomologicalDuality.extPlus_map_degreeZeroIso`.
* `Stacks.HomologicalDuality.bijective_transferMap_degreeZero`.
* `Stacks.HomologicalDuality.isPerfect_degreeZero_iff`.
* `Stacks.HomologicalDuality.isDualityPerfect_of_isPerfect_degreeZero`.
* `Stacks.HomologicalDuality.isPerfect_degreeZero_of_isDualityPerfect`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w w'

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.HomologicalDuality

open Stacks.TopTruncationExt

/-- `extPlus` as an additive equivalence `Ext^m(X, Y) ≃+ Hom_{D⁺}(X[0], Y[0][m])`. -/
def extPlusAddEquiv {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜] [HasExt.{w} 𝒜]
    (X Y : 𝒜) (m : ℕ) :
    Ext.{w} X Y m ≃+ ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj X ⟶
      ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj Y)⟦(m : ℤ)⟧) :=
  AddEquiv.ofBijective (extPlusHom X Y m) (extPlus_bijective X Y m)

/-- `extPlusAddEquiv X Y m` sends `x ∈ Ext^m(X, Y)` to `extPlus x`. -/
lemma extPlusAddEquiv_apply {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]
    [HasExt.{w} 𝒜] {X Y : 𝒜} {m : ℕ} (x : Ext.{w} X Y m) :
    extPlusAddEquiv X Y m x = extPlus x :=
  rfl

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [HasExt.{w} A]
  [EnoughInjectives A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B] [HasExt.{w'} B]
  (Φ : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) [Φ.CommShift ℤ] [Φ.IsTriangulated]
  (hΦ : ∀ X : A, ((Φ ⋙ DerivedCategory.Plus.ι).obj
    ((DerivedCategory.Plus.singleFunctor A 0).obj X)).IsLE 0)
  (hΦ' : ∀ X : A, ((Φ ⋙ DerivedCategory.Plus.ι).obj
    ((DerivedCategory.Plus.singleFunctor A 0).obj X)).IsGE 0)
  (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (η : topHomology (Φ ⋙ DerivedCategory.Plus.ι) 0 ≅ G)

include hΦ hΦ' η

/-- **`Φ(X[0]) ≅ G(X)[0]`**: the top-degree projection of `Φ(X[0])`, which lives in degree `0`
only, followed by `η : H⁰(Φ((-)[0])) ≅ G`. -/
def degreeZeroIso (X : A) :
    Φ.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≅
      (DerivedCategory.Plus.singleFunctor B 0).obj (G.obj X) :=
  DerivedCategory.Plus.ι.preimageIso (X := Φ.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))
    (Y := (DerivedCategory.Plus.singleFunctor B 0).obj (G.obj X))
    (@asIso _ _ _ _ (topProj _ 0 (hΦ X)) (@isIso_topProj_zero B _ _ _ _ (hΦ X) (hΦ' X)) ≪≫
      (shiftFunctorZero' (DerivedCategory B) (-0 : ℤ) (by simp)).app _ ≪≫
        (DerivedCategory.singleFunctor B 0).mapIso (η.app X))

omit [HasExt A] [EnoughInjectives A] [HasExt B] [Φ.CommShift ℤ] [Φ.IsTriangulated] [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] in
/-- In `D(ℬ)`, the morphism `Φ(X[0]) ⟶ G(X)[0]` of `degreeZeroIso` is the top-degree projection,
followed by the identification `M[-0] ≅ M` and the image of `η.hom.app X` under `(-)[0]`. -/
lemma ι_map_degreeZeroIso_hom (X : A) :
    DerivedCategory.Plus.ι.map (degreeZeroIso Φ hΦ hΦ' G η X).hom =
      topProj _ 0 (hΦ X) ≫
        (shiftFunctorZero' (DerivedCategory B) (-0 : ℤ) (by simp)).hom.app _ ≫
          (DerivedCategory.singleFunctor B 0).map (η.hom.app X) := by
  rw [degreeZeroIso, Functor.preimageIso_hom, Functor.map_preimage]
  rfl

/-- **`Φ(X[0]) ≅ G(X)[0]` carries `Φ(e)` to `G(e)`**: for `e ∈ Ext^m_𝒜(X, Y)`,
`(Φ(Y[0]) ≅ G(Y)[0])[m] ∘ Φ(e) = G(e) ∘ (Φ(X[0]) ≅ G(X)[0])` as morphisms
`Φ(X[0]) ⟶ G(Y)[0][m]`. -/
theorem extPlus_map_degreeZeroIso {X Y : A} {m : ℕ} (e : Ext.{w} X Y m) :
    (extPlus e).map Φ ≫ ((degreeZeroIso Φ hΦ hΦ' G η Y).hom)⟦(m : ℤ)⟧' =
      (degreeZeroIso Φ hΦ hΦ' G η X).hom ≫
        extPlus (e.mapExactFunctor G : Ext.{w'} _ _ m) := by
  have : PreservesFiniteLimits (topHomology (Φ ⋙ DerivedCategory.Plus.ι) 0) :=
    preservesFiniteLimits_of_natIso η.symm
  have : PreservesFiniteColimits (topHomology (Φ ⋙ DerivedCategory.Plus.ι) 0) :=
    preservesFiniteColimits_of_natIso η.symm
  have key := map_comp_topProj (Φ ⋙ DerivedCategory.Plus.ι) 0 hΦ e (m : ℤ)
    (show -0 + (m : ℤ) = m by simp) (show (m : ℤ) + -0 = m by simp)
  rw [zero_mul, Int.negOnePow_zero, one_smul] at key
  have hp : ∀ Z : A, topProj _ 0 (hΦ Z) = ShiftedHom.mk₀ (-0 : ℤ) (by simp)
      (topProj _ 0 (hΦ Z) ≫
        (shiftFunctorZero' (DerivedCategory B) (-0 : ℤ) (by simp)).hom.app _) :=
    fun Z => by simp [ShiftedHom.mk₀]
  rw [hp X, hp Y, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at key
  have hη := congrArg Ext.hom (Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor η.hom X m e)
  rw [Ext.comp_hom, Ext.comp_hom, Ext.mk₀_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    ShiftedHom.comp_mk₀] at hη
  apply DerivedCategory.Plus.ι.map_injective
  apply (cancel_mono ((DerivedCategory.Plus.ι.commShiftIso (m : ℤ)).hom.app
    ((DerivedCategory.Plus.singleFunctor B 0).obj (G.obj Y)))).1
  have h₁ : (extPlus e).map (Φ ⋙ DerivedCategory.Plus.ι) =
      DerivedCategory.Plus.ι.map ((extPlus e).map Φ) ≫
        (DerivedCategory.Plus.ι.commShiftIso (m : ℤ)).hom.app _ := by
    rw [ShiftedHom.comp_map]
    rfl
  have h₂ := extPlus_map_ι (e.mapExactFunctor G : Ext.{w'} _ _ m)
  simp only [ShiftedHom.map] at h₂
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, h₂,
    Functor.commShiftIso_hom_naturality, ← Category.assoc, ← h₁]
  have e₁ : (shiftFunctor (DerivedCategory B) (m : ℤ)).map
      (DerivedCategory.Plus.ι.map (degreeZeroIso Φ hΦ hΦ' G η Y).hom) =
      (shiftFunctor (DerivedCategory B) (m : ℤ)).map (topProj _ 0 (hΦ Y) ≫
        (shiftFunctorZero' (DerivedCategory B) (-0 : ℤ) (by simp)).hom.app _) ≫
      (shiftFunctor (DerivedCategory B) (m : ℤ)).map
        ((DerivedCategory.singleFunctor B 0).map (η.hom.app Y)) := by
    rw [ι_map_degreeZeroIso_hom, ← Functor.map_comp, Category.assoc]
    rfl
  rw [e₁]
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) key).trans ?_)
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hη.symm).trans ?_)
  rw [ι_map_degreeZeroIso_hom]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Category.assoc _ _ _))

variable [Φ.Additive] (D₀ : A)

/-- The comparison `θ : Φ(D₀[0]) ⟶ G(D₀)[0][0]` along which duality is transferred through `Φ`:
`Stacks.HomologicalDuality.degreeZeroIso` followed by `M ≅ M[0]`. -/
def degreeZeroTheta :
    Φ.obj ((DerivedCategory.Plus.singleFunctor A 0).obj D₀) ⟶
      ((DerivedCategory.Plus.singleFunctor B 0).obj (G.obj D₀))⟦(0 : ℤ)⟧ :=
  (degreeZeroIso Φ hΦ hΦ' G η D₀).hom ≫
    (shiftFunctorZero (DerivedCategory.Plus B) ℤ).inv.app _

/-- **`Φ` is bijective on morphisms `F[0] ⟶ D₀[0][j]`, read through `θ`**, when `G` is bijective
on `Ext^m(F, D₀)` for every `m`: in negative degrees both sides vanish, and in degree `m ≥ 0` the
map is `G` on `Ext^m` (`Stacks.HomologicalDuality.extPlus_map_degreeZeroIso`). -/
theorem bijective_transferMap_degreeZero (F : A)
    (hG : ∀ m : ℕ, Function.Bijective
      (fun e : Ext.{w} F D₀ m => (e.mapExactFunctor G : Ext.{w'} _ _ m)))
    (j : ℤ) :
    Function.Bijective (transferMap Φ (degreeZeroTheta Φ hΦ hΦ' G η D₀)
      ((DerivedCategory.Plus.singleFunctor A 0).obj F) j) := by
  let D' := (DerivedCategory.Plus.singleFunctor B 0).obj (G.obj D₀)
  let γ : D'⟦j⟧ ⟶ D'⟦j + 0⟧ :=
    ((shiftFunctorZero (DerivedCategory.Plus B) ℤ).inv.app D')⟦j⟧' ≫
      (shiftFunctorAdd' (DerivedCategory.Plus B) 0 j (j + 0) (add_comm 0 j)).inv.app D'
  have hfac : ⇑(transferMap Φ (degreeZeroTheta Φ hΦ hΦ' G η D₀)
      ((DerivedCategory.Plus.singleFunctor A 0).obj F) j) =
      (fun z => z ≫ γ) ∘ (fun y : (DerivedCategory.Plus.singleFunctor A 0).obj F ⟶
          ((DerivedCategory.Plus.singleFunctor A 0).obj D₀)⟦j⟧ =>
        ShiftedHom.map (y : ShiftedHom _ _ _) Φ ≫ ((degreeZeroIso Φ hΦ hΦ' G η D₀).hom)⟦j⟧') := by
    funext y
    simp only [Function.comp_apply, transferMap_apply, degreeZeroTheta, ShiftedHom.map,
      Category.assoc, γ]
    congr 2
    exact Functor.map_comp_assoc _ _ _ _
  rw [hfac]
  refine Function.Bijective.comp ((isIso_iff_yoneda_map_bijective γ).1 inferInstance _) ?_
  rcases lt_or_ge j 0 with hj | hj
  · have := subsingleton_hom_single_shift_of_neg F D₀ hj
    have : Subsingleton ((DerivedCategory.Plus.singleFunctor B 0).obj (G.obj F) ⟶ D'⟦j⟧) :=
      subsingleton_hom_single_shift_of_neg (G.obj F) (G.obj D₀) hj
    have : Subsingleton (Φ.obj ((DerivedCategory.Plus.singleFunctor A 0).obj F) ⟶ D'⟦j⟧) :=
      ((degreeZeroIso Φ hΦ hΦ' G η F).homCongr (Iso.refl _)).subsingleton
    exact bijective_of_subsingleton (X := (DerivedCategory.Plus.singleFunctor A 0).obj F ⟶
      ((DerivedCategory.Plus.singleFunctor A 0).obj D₀)⟦j⟧) _ 0
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    have hcomp : (fun y : (DerivedCategory.Plus.singleFunctor A 0).obj F ⟶
          ((DerivedCategory.Plus.singleFunctor A 0).obj D₀)⟦(m : ℤ)⟧ =>
        ShiftedHom.map (y : ShiftedHom _ _ _) Φ ≫ ((degreeZeroIso Φ hΦ hΦ' G η D₀).hom)⟦(m : ℤ)⟧') ∘
          (extPlus : Ext.{w} F D₀ m → _) =
        (fun x => (degreeZeroIso Φ hΦ hΦ' G η F).hom ≫ x) ∘
          (extPlus : Ext.{w'} (G.obj F) (G.obj D₀) m → _) ∘
            (fun e : Ext.{w} F D₀ m => (e.mapExactFunctor G : Ext.{w'} _ _ m)) :=
      funext fun e => extPlus_map_degreeZeroIso Φ hΦ hΦ' G η e
    rw [← Function.Bijective.of_comp_iff _ (extPlus_bijective F D₀ m), hcomp]
    exact Function.Bijective.comp
      ((isIso_iff_coyoneda_map_bijective (degreeZeroIso Φ hΦ hΦ' G η F).hom).1 inferInstance _)
      ((extPlus_bijective _ _ m).comp (hG m))

variable (O : B) (N : ℕ) {B' : Type*} [AddCommGroup B']
  (τ : (preadditiveCoyoneda.obj (op ((DerivedCategory.Plus.singleFunctor B 0).obj O))).obj
    (((DerivedCategory.Plus.singleFunctor B 0).obj (G.obj D₀))⟦(N : ℤ)⟧) →+ B')

/-- **Duality through `Φ`**: when `G` is bijective on `Ext^m(F, D₀)` for every `m`, duality for
`Hom(O[0], Φ(-))` at `F[0]`, with dualizing object `D₀[0]` and the trace `τ ∘ θ_*`, is duality for
`Hom(O[0], -)` at `G(F)[0]`, with dualizing object `G(D₀)[0]` and the trace `τ`. -/
theorem isPerfect_degreeZero_iff (F : A)
    (hG : ∀ m : ℕ, Function.Bijective
      (fun e : Ext.{w} F D₀ m => (e.mapExactFunctor G : Ext.{w'} _ _ m))) :
    IsPerfect (Φ ⋙ preadditiveCoyoneda.obj (op ((DerivedCategory.Plus.singleFunctor B 0).obj O)))
        ((DerivedCategory.Plus.singleFunctor A 0).obj D₀) (N : ℤ)
        (transferTrace Φ (Iso.refl _) (degreeZeroTheta Φ hΦ hΦ' G η D₀) (add_zero (N : ℤ)) τ)
        ((DerivedCategory.Plus.singleFunctor A 0).obj F) ↔
      IsPerfect (preadditiveCoyoneda.obj (op ((DerivedCategory.Plus.singleFunctor B 0).obj O)))
        ((DerivedCategory.Plus.singleFunctor B 0).obj (G.obj D₀)) (N : ℤ) τ
        ((DerivedCategory.Plus.singleFunctor B 0).obj (G.obj F)) :=
  (isPerfect_iff_of_transfer Φ (Iso.refl _) (degreeZeroTheta Φ hΦ hΦ' G η D₀) (add_zero _) τ _
    (bijective_transferMap_degreeZero Φ hΦ hΦ' G η D₀ F hG)).trans
      (isPerfect_iff_of_iso (degreeZeroIso Φ hΦ hΦ' G η F))

variable (t : Ext.{w'} O (G.obj D₀) N →+ B')
  (hτ : ∀ x : Ext.{w'} O (G.obj D₀) N, τ (extPlus x) = t x)

include hτ in
/-- **Duality through `Φ` gives Yoneda duality in `ℬ`**: duality for `Hom(O[0], Φ(-))` at `F[0]`
gives `Ext^i(O, G F) × Ext^j(G F, G D₀) → Ext^N(O, G D₀) → B` perfect, for `t = τ ∘ extPlus`. -/
theorem isDualityPerfect_of_isPerfect_degreeZero (F : A)
    (hG : ∀ m : ℕ, Function.Bijective
      (fun e : Ext.{w} F D₀ m => (e.mapExactFunctor G : Ext.{w'} _ _ m)))
    (h : IsPerfect
      (Φ ⋙ preadditiveCoyoneda.obj (op ((DerivedCategory.Plus.singleFunctor B 0).obj O)))
      ((DerivedCategory.Plus.singleFunctor A 0).obj D₀) (N : ℤ)
      (transferTrace Φ (Iso.refl _) (degreeZeroTheta Φ hΦ hΦ' G η D₀) (add_zero (N : ℤ)) τ)
      ((DerivedCategory.Plus.singleFunctor A 0).obj F)) :
    Ext.IsDualityPerfect O (G.obj D₀) N t (G.obj F) :=
  isDualityPerfect_of_isPerfect_coyoneda O (G.obj D₀) N t τ hτ (G.obj F)
    ((isPerfect_degreeZero_iff Φ hΦ hΦ' G η D₀ O N τ F hG).1 h)

include hτ in
/-- **Yoneda duality in `ℬ` gives duality through `Φ`**, when moreover `Ext^q(O, G F) = 0` and
`Ext^q(G F, G D₀) = 0` for `q > N`. -/
theorem isPerfect_degreeZero_of_isDualityPerfect (F : A)
    (hG : ∀ m : ℕ, Function.Bijective
      (fun e : Ext.{w} F D₀ m => (e.mapExactFunctor G : Ext.{w'} _ _ m)))
    (hF : Ext.IsDualityPerfect O (G.obj D₀) N t (G.obj F))
    (hO : ∀ q : ℕ, N < q → Subsingleton (Ext.{w'} O (G.obj F) q))
    (hD : ∀ q : ℕ, N < q → Subsingleton (Ext.{w'} (G.obj F) (G.obj D₀) q)) :
    IsPerfect (Φ ⋙ preadditiveCoyoneda.obj (op ((DerivedCategory.Plus.singleFunctor B 0).obj O)))
      ((DerivedCategory.Plus.singleFunctor A 0).obj D₀) (N : ℤ)
      (transferTrace Φ (Iso.refl _) (degreeZeroTheta Φ hΦ hΦ' G η D₀) (add_zero (N : ℤ)) τ)
      ((DerivedCategory.Plus.singleFunctor A 0).obj F) :=
  (isPerfect_degreeZero_iff Φ hΦ hΦ' G η D₀ O N τ F hG).2
    (isPerfect_coyoneda_of_isDualityPerfect O (G.obj D₀) N t τ hτ (G.obj F) hF hO hD)

end Stacks.HomologicalDuality

end
