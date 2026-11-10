module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TopTruncationExt
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial

/-!
# The top-degree projection after an exact functor, and classes in `Ext`

Let `F : 𝒜 ⥤ 𝒜'` be an exact functor and `Φ : D⁺(𝒜') ⥤ D(ℬ)` a triangulated functor such that
`Φ(F(X)[0])` lives in degrees `≤ n` for every object `X` of `𝒜`, and such that
`H = Hⁿ(Φ(F(-)[0])) : 𝒜 ⥤ ℬ` is exact. Then for every class `e ∈ Ext^m_𝒜(X, Y)` the top-degree
projections `θ` (`Stacks.TopTruncationExt.topProj`) satisfy
`θ_{Φ F Y}[m] ∘ Φ(F(e)) = (-1)^{nm} H(e)[-n] ∘ θ_{Φ F X}`
(`Stacks.TopTruncationExt.map_comp_topProj_of_exact`). Only `H`, not `Hⁿ(Φ((-)[0]))` on all of
`𝒜'`, need be exact. With an identification `H ≅ 𝟭` this reads
`t_Y[m] ∘ Φ(F(e)) = (-1)^{nm} e[-n] ∘ t_X` for `t = θ` followed by the identification
(`Stacks.TopTruncationExt.map_comp_topTrace`).

The case of interest is `F = f⁻¹`, `Φ = Rf_!` for a family of curves `f : U → S` and `n = 2`, with
`H = R²f_! f⁻¹ ≅ 𝟭`: the top-degree trace `Rf_! f⁻¹ ⟶ (-)[-2]` commutes with classes in `Ext`
(proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)). The proof is that of
`Stacks.TopTruncationExt.map_comp_topProj`, run on the classes `F(e)`.

## Main results

* `Stacks.TopTruncationExt.map_comp_topProj_of_exact`: the top-degree projections after `F` are
  compatible with classes in `Ext`.
* `Stacks.TopTruncationExt.map_comp_topTrace`: the top-degree trace commutes with classes in `Ext`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian CategoryTheory.Pretriangulated

namespace Stacks.TopTruncationExt

universe w w' w''

variable {A : Type*} [Category* A] [Abelian A] [HasExt.{w} A]
  {A' : Type*} [Category* A'] [Abelian A'] [HasDerivedCategory A'] [HasExt.{w''} A']
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B] [HasExt.{w'} B]
  (F : A ⥤ A') [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (Φ : DerivedCategory.Plus A' ⥤ DerivedCategory B) [Φ.CommShift ℤ] [Φ.IsTriangulated] (n : ℤ)

/-- `H = Hⁿ(Φ(F(-)[0])) : 𝒜 ⥤ ℬ`. -/
abbrev topHomologyOf : A ⥤ B :=
  F ⋙ DerivedCategory.Plus.singleFunctor A' 0 ⋙ Φ ⋙ DerivedCategory.homologyFunctor B n

variable (hΦ : ∀ X : A, (Φ.obj ((DerivedCategory.Plus.singleFunctor A' 0).obj (F.obj X))).IsLE n)
  [PreservesFiniteLimits (topHomologyOf F Φ n)] [PreservesFiniteColimits (topHomologyOf F Φ n)]

/-- The compatibility of the top-degree projections with the image under `F` of one class
`e ∈ Ext^m_𝒜(X, Y)`. -/
def IsCompatibleOf {X Y : A} {m : ℕ} (e : Ext.{w} X Y m) : Prop :=
  ∀ (c : ℤ) (h₁ : -n + (m : ℤ) = c) (h₂ : (m : ℤ) + -n = c),
    ((extPlus (e.mapExactFunctor F : Ext.{w''} _ _ m)).map Φ).comp (topProj _ n (hΦ Y)) h₁ =
      (n * m).negOnePow • (topProj _ n (hΦ X)).comp
        ((e.mapExactFunctor (topHomologyOf F Φ n) : Ext.{w'} _ _ m)).hom h₂

/-- The compatibility `IsCompatibleOf` holds for the class `Ext.mk₀ f` of a morphism
`f : X ⟶ Y`. -/
theorem isCompatibleOf_mk₀ {X Y : A} (f : X ⟶ Y) : IsCompatibleOf F Φ n hΦ (Ext.mk₀ f) := by
  intro c h₁ h₂
  obtain rfl : c = -n := by simpa using h₁.symm
  rw [Ext.mapExactFunctor_mk₀, extPlus_mk₀, ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp,
    Ext.mapExactFunctor_mk₀, Ext.mk₀_hom, ShiftedHom.comp_mk₀]
  simp only [Nat.cast_zero, mul_zero, Int.negOnePow_zero, one_smul]
  exact comp_topProj n (hΦ X) (hΦ Y) _

/-- The compatibility `IsCompatibleOf` holds for the class `hS.extClass ∈ Ext¹(S.X₃, S.X₁)` of a
short exact sequence `S`. -/
theorem isCompatibleOf_extClass {S : ShortComplex A} (hS : S.ShortExact) :
    IsCompatibleOf F Φ n hΦ (hS.extClass : Ext.{w} _ _ 1) := by
  intro c h₁ h₂
  have hSF := hS.map_of_exact F
  have hS' := hS.map_of_exact (topHomologyOf F Φ n)
  let T := Φ.mapTriangle.obj (plusSingleTriangle hSF)
  have hT : T ∈ distTriang _ := Φ.map_distinguished _ (plusSingleTriangle_distinguished hSF)
  let T' := (Triangle.shiftFunctor (DerivedCategory B) (-n)).obj hS'.singleTriangle
  have hT' : T' ∈ distTriang _ :=
    Triangle.shift_distinguished _ hS'.singleTriangle_distinguished (-n)
  have : DerivedCategory.TStructure.t.IsLE T.obj₁ n := hΦ S.X₁
  have : DerivedCategory.TStructure.t.IsGE T'.obj₃ n := isGE_shift_single _ n
  have key := Stacks.Triangulated.mor₃_comp_shift_map_eq_of_isLE DerivedCategory.TStructure.t n
    hT hT' (topProj _ n (hΦ S.X₁)) ((-n).negOnePow • topProj _ n (hΦ S.X₂))
    (topProj _ n (hΦ S.X₃)) (by
      change Φ.map ((DerivedCategory.Plus.singleFunctor A' 0).map (F.map S.f)) ≫
          ((-n).negOnePow • topProj _ n (hΦ S.X₂)) = topProj _ n (hΦ S.X₁) ≫
        ((-n).negOnePow • ((DerivedCategory.singleFunctor B 0).map
          ((topHomologyOf F Φ n).map S.f))⟦-n⟧')
      rw [Linear.comp_units_smul, Linear.comp_units_smul, comp_topProj n (hΦ _) (hΦ _)]
      rfl) (by
      change Φ.map ((DerivedCategory.Plus.singleFunctor A' 0).map (F.map S.g)) ≫
          topProj _ n (hΦ S.X₃) = ((-n).negOnePow • topProj _ n (hΦ S.X₂)) ≫
        ((-n).negOnePow • ((DerivedCategory.singleFunctor B 0).map
          ((topHomologyOf F Φ n).map S.g))⟦-n⟧')
      rw [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, Int.units_mul_self,
        one_smul, comp_topProj n (hΦ _) (hΦ _)]
      rfl)
  rw [Ext.mapExactFunctor_extClass, Ext.mapExactFunctor_extClass,
    ShortComplex.ShortExact.extClass_hom, show (n * ((1 : ℕ) : ℤ)).negOnePow = (-n).negOnePow by
      rw [Int.negOnePow_neg, Nat.cast_one, mul_one]]
  exact comp_eq_units_smul_comp_of_comp_shift _ _ _ _ _ key h₁ h₂

/-- The compatibility `IsCompatibleOf` is preserved by the composition of classes in `Ext`. -/
theorem IsCompatibleOf.comp {X Y Z : A} {a b d : ℕ} {α : Ext.{w} X Y a} {β : Ext.{w} Y Z b}
    (h : a + b = d) (hα : IsCompatibleOf F Φ n hΦ α) (hβ : IsCompatibleOf F Φ n hΦ β) :
    IsCompatibleOf F Φ n hΦ (α.comp β h) := by
  intro c h₁ h₂
  rw [Ext.mapExactFunctor_comp, extPlus_comp, ShiftedHom.map_comp, Ext.mapExactFunctor_comp,
    Ext.comp_hom,
    ShiftedHom.comp_assoc _ _ _ _ (show -n + (b : ℤ) = b - n by omega)
      (show -n + (b : ℤ) + a = c by omega),
    hβ (b - n) (by omega) (by omega), shiftedHom_comp_units_smul,
    ← ShiftedHom.comp_assoc _ _ _ (show -n + (a : ℤ) = a - n by omega)
      (show (b : ℤ) + -n = b - n by omega) (show (b : ℤ) + -n + a = c by omega),
    hα (a - n) (by omega) (by omega), shiftedHom_units_smul_comp, smul_smul,
    ShiftedHom.comp_assoc _ _ _ (show (a : ℤ) + -n = a - n by omega)
      (show (b : ℤ) + a = d by omega) (show (b : ℤ) + a + -n = c by omega),
    ← Int.negOnePow_add]
  congr 2
  push_cast [← h]
  ring

/-- **The top-degree projection after an exact functor is compatible with classes in `Ext`.**
Let `F : 𝒜 ⥤ 𝒜'` be exact and `Φ : D⁺(𝒜') ⥤ D(ℬ)` triangulated with `Φ(F(X)[0])` in degrees `≤ n`
for every `X`, such that `H = Hⁿ(Φ(F(-)[0]))` is exact. For every class `e ∈ Ext^m_𝒜(X, Y)`,
`θ_{Φ F Y}[m] ∘ Φ(F(e)) = (-1)^{nm} H(e)[-n] ∘ θ_{Φ F X}`. -/
theorem map_comp_topProj_of_exact [EnoughInjectives A] {X Y : A} {m : ℕ} (e : Ext.{w} X Y m)
    (c : ℤ) (h₁ : -n + (m : ℤ) = c) (h₂ : (m : ℤ) + -n = c) :
    ((extPlus (e.mapExactFunctor F : Ext.{w''} _ _ m)).map Φ).comp (topProj _ n (hΦ Y)) h₁ =
      (n * m).negOnePow • (topProj _ n (hΦ X)).comp
        ((e.mapExactFunctor (topHomologyOf F Φ n) : Ext.{w'} _ _ m)).hom h₂ := by
  suffices H : ∀ (m : ℕ) {Y : A} (e : Ext.{w} X Y m), IsCompatibleOf F Φ n hΦ e from
    H m e c h₁ h₂
  intro m
  induction m with
  | zero =>
      intro Y e
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X Y).surjective e
      exact isCompatibleOf_mk₀ F Φ n hΦ f
  | succ m ih =>
      intro Y e
      let I : InjectivePresentation Y := Classical.arbitrary _
      have hS : (ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)).ShortExact :=
        { exact := ShortComplex.exact_cokernel I.f }
      obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ X hS e (Ext.eq_zero_of_injective _) rfl
      exact (ih x₃).comp F Φ n hΦ rfl (isCompatibleOf_extClass F Φ n hΦ hS)

/-! ### Through an identification `H ≅ 𝟭` -/

section Trace

variable {B' : Type*} [Category* B'] [Abelian B'] [HasDerivedCategory B'] [HasExt.{w} B']
  (F' : B' ⥤ A') [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  (Φ' : DerivedCategory.Plus A' ⥤ DerivedCategory B') [Φ'.CommShift ℤ] [Φ'.IsTriangulated]
  (hΦ' : ∀ X : B', (Φ'.obj ((DerivedCategory.Plus.singleFunctor A' 0).obj (F'.obj X))).IsLE n)
  (ν : topHomologyOf F' Φ' n ≅ 𝟭 B')

/-- **The top-degree trace** `t_X : Φ(F(X)[0]) ⟶ X[0][-n]`: the top-degree projection followed by
an identification `ν : Hⁿ(Φ(F(-)[0])) ≅ 𝟭`. -/
def topTrace (X : B') :
    ShiftedHom (Φ'.obj ((DerivedCategory.Plus.singleFunctor A' 0).obj (F'.obj X)))
      ((DerivedCategory.singleFunctor B' 0).obj X) (-n) :=
  topProj _ n (hΦ' X) ≫ ((DerivedCategory.singleFunctor B' 0).map (ν.hom.app X))⟦-n⟧'

/-- **The top-degree trace commutes with classes in `Ext`.** With `F`, `Φ` as in
`Stacks.TopTruncationExt.map_comp_topProj_of_exact` and an identification
`ν : Hⁿ(Φ(F(-)[0])) ≅ 𝟭`, for every class `e ∈ Ext^m(X, Y)`,
`t_Y[m] ∘ Φ(F(e)) = (-1)^{nm} e[-n] ∘ t_X`. -/
theorem map_comp_topTrace [EnoughInjectives B'] {X Y : B'} {m : ℕ} (e : Ext.{w} X Y m)
    (c : ℤ) (h₁ : -n + (m : ℤ) = c) (h₂ : (m : ℤ) + -n = c) :
    ((extPlus (e.mapExactFunctor F' : Ext.{w''} _ _ m)).map Φ').comp
        (topTrace n F' Φ' hΦ' ν Y) h₁ =
      (n * m).negOnePow • (topTrace n F' Φ' hΦ' ν X).comp e.hom h₂ := by
  have : PreservesFiniteLimits (topHomologyOf F' Φ' n) :=
    preservesFiniteLimits_of_natIso ν.symm
  have : PreservesFiniteColimits (topHomologyOf F' Φ' n) :=
    preservesFiniteColimits_of_natIso ν.symm
  have htr (Z : B') : topTrace n F' Φ' hΦ' ν Z = (topProj _ n (hΦ' Z)).comp
      (Ext.mk₀ (ν.hom.app Z) : Ext.{w} _ _ 0).hom (by simp) := by
    rw [Ext.mk₀_hom, ShiftedHom.comp_mk₀]
    rfl
  have hnat := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor ν.hom X m e
  rw [Stacks.ExtFunctorial.mapExactFunctor_id] at hnat
  rw [htr Y, htr X, ← ShiftedHom.comp_assoc _ _ _ h₁ (show (0 : ℕ) + -n = -n by simp)
      (show ((0 : ℕ) : ℤ) + -n + (m : ℤ) = c by omega),
    map_comp_topProj_of_exact F' Φ' n hΦ' e c h₁ h₂, shiftedHom_units_smul_comp,
    ShiftedHom.comp_assoc _ _ _ h₂ (show ((0 : ℕ) : ℤ) + (m : ℤ) = m by simp)
      (show ((0 : ℕ) : ℤ) + (m : ℤ) + -n = c by omega),
    ShiftedHom.comp_assoc _ _ _ (show ((0 : ℕ) : ℤ) + -n = -n by simp)
      (show (m : ℤ) + ((0 : ℕ) : ℤ) = m by simp)
      (show (m : ℤ) + ((0 : ℕ) : ℤ) + -n = c by omega),
    ← Ext.comp_hom, ← Ext.comp_hom, hnat]
  all_goals omega

end Trace

end Stacks.TopTruncationExt
