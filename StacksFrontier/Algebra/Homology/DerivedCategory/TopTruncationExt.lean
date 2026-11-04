module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.CategoryTheory.Triangulated.ThirdMorphismOrthogonal

/-!
# The top-degree truncation of a triangulated functor and classes in `Ext`

Let `Φ : D⁺(𝒜) ⥤ D(ℬ)` be a triangulated functor such that `Φ(X[0])` lives in degrees `≤ n` for
every object `X` of `𝒜`, and let `H = Hⁿ(Φ((-)[0])) : 𝒜 ⥤ ℬ`. Every object `K` of `D(ℬ)` living in
degrees `≤ n` has a canonical morphism `θ_K : K ⟶ Hⁿ(K)[-n]`, the unique one inducing the
identity on `Hⁿ` (`Stacks.TopTruncationExt.topProj`); it is the truncation `K ⟶ τ_{≥ n} K`.

If `H` is exact, `θ` is compatible with classes in `Ext`: for `e ∈ Ext^m_𝒜(X, Y)`,
`θ_{Φ Y}[m] ∘ Φ(e) = (-1)^{nm} H(e)[-n] ∘ θ_{Φ X}` as morphisms `Φ(X[0]) ⟶ H(Y)[m - n]`
(`Stacks.TopTruncationExt.map_comp_topProj`), where `H(e) = Ext.mapExactFunctor H e`.

## Main definitions

* `Stacks.TopTruncationExt.topProj`: `θ_K : K ⟶ Hⁿ(K)[-n]` for `K` in degrees `≤ n`.
* `Stacks.TopTruncationExt.extPlus`: an `Ext` class read as a shifted morphism of `D⁺(𝒜)`.

## Main results

* `Stacks.TopTruncationExt.map_comp_topProj`: `θ_{Φ Y}[m] ∘ Φ(e) = (-1)^{nm} H(e)[-n] ∘ θ_{Φ X}`
  for every `e ∈ Ext^m_𝒜(X, Y)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian CategoryTheory.Pretriangulated

namespace Stacks.TopTruncationExt

/-! ### Morphisms into a shifted single object -/

section TopProj

variable {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]

/-- `Hⁿ(M[0][-n]) ≅ M`, naturally in `M`. -/
def singleShiftHomologyIso (n : ℤ) :
    DerivedCategory.singleFunctor B 0 ⋙ shiftFunctor (DerivedCategory B) (-n) ⋙
      DerivedCategory.homologyFunctor B n ≅ 𝟭 B :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((DerivedCategory.singleFunctors B).shiftIso (-n) n 0 (by omega)) _ ≪≫
      DerivedCategory.singleFunctorCompHomologyFunctorIso B n

/-- The object `M[0][-n]` lives in degrees `≥ n`. -/
instance isGE_shift_single (M : B) (n : ℤ) :
    (((DerivedCategory.singleFunctor B 0).obj M)⟦-n⟧).IsGE n :=
  DerivedCategory.TStructure.t.isGE_shift _ 0 (-n) n (by omega)

/-- Taking `Hⁿ` identifies morphisms `K ⟶ M[0][-n]` with morphisms `Hⁿ(K) ⟶ M` when `K` lives in
degrees `≤ n`. -/
theorem bijective_homologyFunctor_map (K : DerivedCategory B) (n : ℤ) (hK : K.IsLE n) (M : B) :
    Function.Bijective (fun f : ShiftedHom K ((DerivedCategory.singleFunctor B 0).obj M) (-n) ↦
      (DerivedCategory.homologyFunctor B n).map f ≫ (singleShiftHomologyIso n).hom.app M) :=
  (show Function.Bijective (fun g : (DerivedCategory.homologyFunctor B n).obj K ⟶
      (DerivedCategory.homologyFunctor B n).obj (((DerivedCategory.singleFunctor B 0).obj M)⟦-n⟧) ↦
        g ≫ (singleShiftHomologyIso n).hom.app M) from
    ⟨fun a b h => by simpa using congrArg (· ≫ (singleShiftHomologyIso (B := B) n).inv.app M) h,
      fun g => ⟨g ≫ (singleShiftHomologyIso n).inv.app M, by simp⟩⟩).comp
    (DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE K _ n)

/-- **The top-degree projection** `θ_K : K ⟶ Hⁿ(K)[-n]` of an object `K` living in degrees `≤ n`:
the unique morphism inducing the identity on `Hⁿ`. -/
def topProj (K : DerivedCategory B) (n : ℤ) (hK : K.IsLE n) :
    ShiftedHom K ((DerivedCategory.singleFunctor B 0).obj
      ((DerivedCategory.homologyFunctor B n).obj K)) (-n) :=
  (Equiv.ofBijective _ (bijective_homologyFunctor_map K n hK _)).symm (𝟙 _)

/-- The morphism `θ_K` induces the identity on `Hⁿ(K)`. -/
theorem homologyFunctor_map_topProj (K : DerivedCategory B) (n : ℤ) (hK : K.IsLE n) :
    (DerivedCategory.homologyFunctor B n).map (topProj K n hK) ≫
        (singleShiftHomologyIso n).hom.app _ = 𝟙 _ :=
  (Equiv.ofBijective _ (bijective_homologyFunctor_map K n hK _)).apply_symm_apply (𝟙 _)

/-- **Naturality of the top-degree projection.** -/
theorem comp_topProj {K L : DerivedCategory B} (n : ℤ) (hK : K.IsLE n) (hL : L.IsLE n)
    (u : K ⟶ L) :
    u ≫ topProj L n hL = topProj K n hK ≫
      ((DerivedCategory.singleFunctor B 0).map
        ((DerivedCategory.homologyFunctor B n).map u))⟦-n⟧' := by
  apply (bijective_homologyFunctor_map K n hK _).injective
  have h := (singleShiftHomologyIso (B := B) n).hom.naturality
    ((DerivedCategory.homologyFunctor B n).map u)
  dsimp at h
  dsimp only
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, h,
    homologyFunctor_map_topProj, reassoc_of% (homologyFunctor_map_topProj K n hK)]
  simp

end TopProj

/-! ### Signs -/

section Signs

variable {C : Type*} [Category* C] [Preadditive C] [HasShift C ℤ]
  [∀ a : ℤ, (shiftFunctor C a).Additive]

omit [∀ a : ℤ, (shiftFunctor C a).Additive] in
/-- Composition of shifted morphisms commutes with the action of a unit on the first factor. -/
theorem shiftedHom_units_smul_comp {X Y Z : C} {a b c : ℤ} (u : ℤˣ) (α : ShiftedHom X Y a)
    (β : ShiftedHom Y Z b) (h : b + a = c) : (u • α).comp β h = u • α.comp β h := by
  simp only [ShiftedHom.comp, Linear.units_smul_comp]

/-- Composition of shifted morphisms commutes with the action of a unit on the second factor. -/
theorem shiftedHom_comp_units_smul {X Y Z : C} {a b c : ℤ} (α : ShiftedHom X Y a) (u : ℤˣ)
    (β : ShiftedHom Y Z b) (h : b + a = c) : α.comp (u • β) h = u • α.comp β h := by
  simp only [ShiftedHom.comp, Functor.map_units_smul, Linear.units_smul_comp,
    Linear.comp_units_smul]

omit [∀ a : ℤ, (shiftFunctor C a).Additive] in
/-- If `f ≫ θY⟦a⟧' = θX ≫ u • (g⟦b⟧' ≫ comm)`, then `f.comp θY = u • θX.comp g` as composites of
shifted morphisms. -/
theorem comp_eq_units_smul_comp_of_comp_shift {X Y Z W : C} {a b c : ℤ} (f : ShiftedHom X Y a)
    (θY : ShiftedHom Y Z b) (θX : ShiftedHom X W b) (g : ShiftedHom W Z a) (u : ℤˣ)
    (h : f ≫ θY⟦a⟧' = θX ≫ (u • (g⟦b⟧' ≫ (shiftFunctorComm C a b).hom.app Z)))
    (h₁ : b + a = c) (h₂ : a + b = c) : f.comp θY h₁ = u • θX.comp g h₂ := by
  rw [ShiftedHom.comp, ShiftedHom.comp, reassoc_of% h, shiftFunctorComm_eq C a b c h₂]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Linear.units_smul_comp,
    Linear.comp_units_smul, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

end Signs

/-! ### `Ext` classes read in `D⁺(𝒜)` -/

section ExtPlus

universe w

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [HasExt.{w} A]

/-- An `Ext` class `e ∈ Ext^m_𝒜(X, Y)`, read as a morphism `X[0] ⟶ Y[0][m]` of `D⁺(𝒜)`. -/
def extPlus {X Y : A} {m : ℕ} (e : Ext.{w} X Y m) :
    ShiftedHom ((DerivedCategory.Plus.singleFunctor A 0).obj X)
      ((DerivedCategory.Plus.singleFunctor A 0).obj Y) (m : ℤ) :=
  DerivedCategory.Plus.ι.preimage
    (e.hom ≫ (DerivedCategory.Plus.ι.commShiftIso (m : ℤ)).inv.app
      ((DerivedCategory.Plus.singleFunctor A 0).obj Y))

/-- The image of `extPlus e` in `D(𝒜)` is the morphism `e.hom`. -/
theorem extPlus_map_ι {X Y : A} {m : ℕ} (e : Ext.{w} X Y m) :
    (extPlus e).map DerivedCategory.Plus.ι = e.hom := by
  simp only [ShiftedHom.map, extPlus, Functor.map_preimage]
  exact (Category.assoc _ _ _).trans
    ((congrArg (e.hom ≫ ·) (Iso.inv_hom_id_app (DerivedCategory.Plus.ι.commShiftIso (m : ℤ))
      ((DerivedCategory.Plus.singleFunctor A 0).obj Y))).trans (Category.comp_id _))

omit [HasExt.{w} A] in
/-- The inclusion `D⁺(𝒜) ⥤ D(𝒜)` is injective on shifted morphisms. -/
theorem map_ι_injective {P Q : DerivedCategory.Plus A} {a : ℤ} :
    Function.Injective (fun f : ShiftedHom P Q a ↦ f.map DerivedCategory.Plus.ι) :=
  fun _ _ h ↦ DerivedCategory.Plus.ι.map_injective
    ((cancel_mono ((DerivedCategory.Plus.ι.commShiftIso a).hom.app Q)).1 h)

/-- `extPlus` sends the Yoneda product of `Ext` classes to the composite of shifted morphisms. -/
theorem extPlus_comp {X Y Z : A} {a b c : ℕ} (α : Ext.{w} X Y a) (β : Ext.{w} Y Z b)
    (h : a + b = c) : extPlus (α.comp β h) = (extPlus α).comp (extPlus β) (by omega) := by
  apply map_ι_injective
  dsimp only
  rw [ShiftedHom.map_comp, extPlus_map_ι, extPlus_map_ι, extPlus_map_ι, Ext.comp_hom]
  rfl

/-- The class of a morphism `f : X ⟶ Y` in degree `0` is the morphism `f[0]` of `D⁺(𝒜)`. -/
theorem extPlus_mk₀ {X Y : A} (f : X ⟶ Y) :
    extPlus (Ext.mk₀ f) = ShiftedHom.mk₀ _ (by simp)
      ((DerivedCategory.Plus.singleFunctor A 0).map f) := by
  apply map_ι_injective
  dsimp only
  rw [extPlus_map_ι, ShiftedHom.map_mk₀, Ext.mk₀_hom]
  rfl

/-- The triangle `X₁[0] ⟶ X₂[0] ⟶ X₃[0] ⟶ X₁[0][1]` of a short exact sequence, in `D⁺(𝒜)`. -/
def plusSingleTriangle {S : ShortComplex A} (hS : S.ShortExact) :
    Triangle (DerivedCategory.Plus A) :=
  Triangle.mk ((DerivedCategory.Plus.singleFunctor A 0).map S.f)
    ((DerivedCategory.Plus.singleFunctor A 0).map S.g) (extPlus hS.extClass)

/-- The triangle of a short exact sequence in `D⁺(𝒜)` is distinguished. -/
theorem plusSingleTriangle_distinguished {S : ShortComplex A} (hS : S.ShortExact) :
    plusSingleTriangle hS ∈ distTriang (DerivedCategory.Plus A) := by
  change DerivedCategory.Plus.ι.mapTriangle.obj _ ∈ distTriang (DerivedCategory A)
  have e : DerivedCategory.Plus.ι.mapTriangle.obj (plusSingleTriangle hS) = hS.singleTriangle :=
    congrArg (Triangle.mk _ _)
      ((extPlus_map_ι (hS.extClass : Ext.{w} _ _ 1)).trans hS.extClass_hom)
  rw [e]
  exact hS.singleTriangle_distinguished

end ExtPlus

/-! ### The compatibility -/

section Main

universe w w'

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [HasExt.{w} A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B] [HasExt.{w'} B]
  (Φ : DerivedCategory.Plus A ⥤ DerivedCategory B) [Φ.CommShift ℤ] [Φ.IsTriangulated] (n : ℤ)

/-- `H = Hⁿ(Φ((-)[0])) : 𝒜 ⥤ ℬ`. -/
abbrev topHomology : A ⥤ B :=
  DerivedCategory.Plus.singleFunctor A 0 ⋙ Φ ⋙ DerivedCategory.homologyFunctor B n

variable (hΦ : ∀ X : A, (Φ.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)).IsLE n)
  [PreservesFiniteLimits (topHomology Φ n)] [PreservesFiniteColimits (topHomology Φ n)]

/-- The compatibility of the top-degree projections with one class `e ∈ Ext^m_𝒜(X, Y)`:
`θ_{Φ Y}[m] ∘ Φ(e) = (-1)^{nm} H(e)[-n] ∘ θ_{Φ X}`. -/
def IsCompatible {X Y : A} {m : ℕ} (e : Ext.{w} X Y m) : Prop :=
  ∀ (c : ℤ) (h₁ : -n + (m : ℤ) = c) (h₂ : (m : ℤ) + -n = c),
    ((extPlus e).map Φ).comp (topProj _ n (hΦ Y)) h₁ =
      (n * m).negOnePow • (topProj _ n (hΦ X)).comp
        ((e.mapExactFunctor (topHomology Φ n) : Ext.{w'} _ _ m)).hom h₂

/-- The class `Ext.mk₀ f` of a morphism `f : X ⟶ Y` satisfies the compatibility. -/
theorem isCompatible_mk₀ {X Y : A} (f : X ⟶ Y) : IsCompatible Φ n hΦ (Ext.mk₀ f) := by
  intro c h₁ h₂
  obtain rfl : c = -n := by simpa using h₁.symm
  rw [extPlus_mk₀, ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_hom, ShiftedHom.comp_mk₀]
  simp only [Nat.cast_zero, mul_zero, Int.negOnePow_zero, one_smul]
  exact comp_topProj n (hΦ X) (hΦ Y) _

/-- The class `hS.extClass ∈ Ext^1_𝒜(X₃, X₁)` of a short exact sequence satisfies the
compatibility. -/
theorem isCompatible_extClass {S : ShortComplex A} (hS : S.ShortExact) :
    IsCompatible Φ n hΦ (hS.extClass : Ext.{w} _ _ 1) := by
  intro c h₁ h₂
  have hS' := hS.map_of_exact (topHomology Φ n)
  let T := Φ.mapTriangle.obj (plusSingleTriangle hS)
  have hT : T ∈ distTriang _ := Φ.map_distinguished _ (plusSingleTriangle_distinguished hS)
  let T' := (Triangle.shiftFunctor (DerivedCategory B) (-n)).obj hS'.singleTriangle
  have hT' : T' ∈ distTriang _ :=
    Triangle.shift_distinguished _ hS'.singleTriangle_distinguished (-n)
  have : DerivedCategory.TStructure.t.IsLE T.obj₁ n := hΦ S.X₁
  have : DerivedCategory.TStructure.t.IsGE T'.obj₃ n := isGE_shift_single _ n
  have key := Stacks.Triangulated.mor₃_comp_shift_map_eq_of_isLE DerivedCategory.TStructure.t n
    hT hT' (topProj _ n (hΦ S.X₁)) ((-n).negOnePow • topProj _ n (hΦ S.X₂))
    (topProj _ n (hΦ S.X₃)) (by
      change Φ.map ((DerivedCategory.Plus.singleFunctor A 0).map S.f) ≫
          ((-n).negOnePow • topProj _ n (hΦ S.X₂)) = topProj _ n (hΦ S.X₁) ≫
        ((-n).negOnePow • ((DerivedCategory.singleFunctor B 0).map
          ((topHomology Φ n).map S.f))⟦-n⟧')
      rw [Linear.comp_units_smul, Linear.comp_units_smul, comp_topProj n (hΦ _) (hΦ _)]
      rfl) (by
      change Φ.map ((DerivedCategory.Plus.singleFunctor A 0).map S.g) ≫
          topProj _ n (hΦ S.X₃) = ((-n).negOnePow • topProj _ n (hΦ S.X₂)) ≫
        ((-n).negOnePow • ((DerivedCategory.singleFunctor B 0).map
          ((topHomology Φ n).map S.g))⟦-n⟧')
      rw [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, Int.units_mul_self,
        one_smul, comp_topProj n (hΦ _) (hΦ _)]
      rfl)
  rw [Ext.mapExactFunctor_extClass, ShortComplex.ShortExact.extClass_hom,
    show (n * ((1 : ℕ) : ℤ)).negOnePow = (-n).negOnePow by
      rw [Int.negOnePow_neg, Nat.cast_one, mul_one]]
  exact comp_eq_units_smul_comp_of_comp_shift _ _ _ _ _ key h₁ h₂

/-- The compatibility is stable under composition of classes. -/
theorem IsCompatible.comp {X Y Z : A} {a b d : ℕ} {α : Ext.{w} X Y a} {β : Ext.{w} Y Z b}
    (h : a + b = d) (hα : IsCompatible Φ n hΦ α) (hβ : IsCompatible Φ n hΦ β) :
    IsCompatible Φ n hΦ (α.comp β h) := by
  intro c h₁ h₂
  rw [extPlus_comp, ShiftedHom.map_comp, Ext.mapExactFunctor_comp, Ext.comp_hom,
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

/-- **The top-degree projection is compatible with classes in `Ext`.** Let `Φ : D⁺(𝒜) ⥤ D(ℬ)` be
triangulated with `Φ(X[0])` in degrees `≤ n` for every `X`, such that `H = Hⁿ(Φ((-)[0]))` is
exact, and let `θ_K : K ⟶ Hⁿ(K)[-n]` be the top-degree projection. For every class
`e ∈ Ext^m_𝒜(X, Y)`, `θ_{Φ Y}[m] ∘ Φ(e) = (-1)^{nm} H(e)[-n] ∘ θ_{Φ X}`. -/
theorem map_comp_topProj [EnoughInjectives A] {X Y : A} {m : ℕ} (e : Ext.{w} X Y m) (c : ℤ)
    (h₁ : -n + (m : ℤ) = c) (h₂ : (m : ℤ) + -n = c) :
    ((extPlus e).map Φ).comp (topProj _ n (hΦ Y)) h₁ =
      (n * m).negOnePow • (topProj _ n (hΦ X)).comp
        ((e.mapExactFunctor (topHomology Φ n) : Ext.{w'} _ _ m)).hom h₂ := by
  suffices H : ∀ (m : ℕ) {Y : A} (e : Ext.{w} X Y m), IsCompatible Φ n hΦ e from H m e c h₁ h₂
  intro m
  induction m with
  | zero =>
      intro Y e
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X Y).surjective e
      exact isCompatible_mk₀ Φ n hΦ f
  | succ m ih =>
      intro Y e
      let I : InjectivePresentation Y := Classical.arbitrary _
      have hS : (ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)).ShortExact :=
        { exact := ShortComplex.exact_cokernel I.f }
      obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ X hS e (Ext.eq_zero_of_injective _) rfl
      exact (ih x₃).comp Φ n hΦ rfl (isCompatible_extClass Φ n hΦ hS)

end Main

end Stacks.TopTruncationExt
