module

public import StacksFrontier.CategoryTheory.Triangulated.PostnikovSystems
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Postnikov systems for complexes of small length

Let `D` be a pretriangulated category. This file records how Postnikov systems
(`CategoryTheory.Triangulated.PostnikovSystem`) and their morphisms behave for complexes
`Xₙ ⟶ ⋯ ⟶ X₀` of small length `n`.

## Main definitions

* `CategoryTheory.Triangulated.PostnikovSystem.IsHomOver`: a family `g i : Yᵢ ⟶ Y'ᵢ` is a
  morphism of Postnikov systems lying over a family `f i : Xᵢ ⟶ X'ᵢ`.

## Main results

* `CategoryTheory.Triangulated.postnikovSystem_small_cases`: Postnikov systems exist for `n ≤ 2`;
  a morphism of complexes extends uniquely to a morphism of Postnikov systems for `n = 0` and
  extends for `n = 1`; and, in the homotopy category of `ℤ`-modules, the extension for `n = 1` is
  not unique, a morphism of complexes of length `2` does not extend, and for every `n > 2` some
  complex of length `n` has no Postnikov system.

## Implementation notes

The counterexamples rest on two observations valid in any pretriangulated category. A nonzero
object `A` gives a distinguished triangle `Y ⟶ A ⟶ A⟦1⟧ ⟶ Y⟦1⟧` with zero middle morphism, and
the nonzero morphisms `A ⟶ Y` killed by `Y ⟶ A` make extensions non-unique in length `1` and
impossible in length `2`. A distinguished triangle `A ⟶ B ⟶ C ⟶ A⟦1⟧` gives the complex
`⋯ ⟶ A ⟶ A ⟶ B ⟶ C ⟶ A⟦1⟧`, and a Postnikov system for it forces `h : C ⟶ A⟦1⟧` to satisfy
`h ≫ s ≫ h = h` for some `s`; in the homotopy category of `ℤ`-modules the morphism `2 : ℤ ⟶ ℤ`
placed in the third position violates this.

## References

* [Stacks project, Tag 0D81](https://stacks.math.columbia.edu/tag/0D81)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe v u

namespace CategoryTheory.Triangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-! ### Morphisms of Postnikov systems in low length -/

/-- Let `S`, `S'` be Postnikov systems for complexes `Xₙ ⟶ ⋯ ⟶ X₀` and `X'ₙ ⟶ ⋯ ⟶ X'₀`, with
objects `Yᵢ`, `Y'ᵢ`, and let `f i : Xᵢ ⟶ X'ᵢ`. A family `g i : Yᵢ ⟶ Y'ᵢ` is a *morphism of
Postnikov systems over `f`* if it is compatible with the morphisms `Yᵢ ⟶ Xᵢ`, `Xᵢ₊₁ ⟶ Yᵢ` and
`Yᵢ ⟶ Yᵢ₊₁⟦1⟧` of the two systems. -/
def PostnikovSystem.IsHomOver {n : ℕ} {X X' : Fin (n + 1) → D}
    {d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc} {d' : ∀ i : Fin n, X' i.succ ⟶ X' i.castSucc}
    (S : PostnikovSystem X d) (S' : PostnikovSystem X' d') (f : ∀ i, X i ⟶ X' i)
    (g : ∀ i, S.obj i ⟶ S'.obj i) : Prop :=
  (∀ i, g i ≫ S'.π i = S.π i ≫ f i) ∧
    (∀ i : Fin n, S.p i ≫ g i.castSucc = f i.succ ≫ S'.p i) ∧
    (∀ i : Fin n, S.δ i ≫ (g i.succ)⟦(1 : ℤ)⟧' = g i.castSucc ≫ S'.δ i)

/-- For complexes of length `0` every family `f₀ : X₀ ⟶ X'₀` extends to a unique morphism of
Postnikov systems. -/
private lemma existsUnique_isHomOver_of_length_zero {X X' : Fin 1 → D}
    {d : ∀ i : Fin 0, X i.succ ⟶ X i.castSucc} {d' : ∀ i : Fin 0, X' i.succ ⟶ X' i.castSucc}
    (S : PostnikovSystem X d) (S' : PostnikovSystem X' d') (f : ∀ i, X i ⟶ X' i) :
    ∃! g : ∀ i, S.obj i ⟶ S'.obj i, S.IsHomOver S' f g := by
  refine ⟨Fin.cases (motive := fun i => S.obj i ⟶ S'.obj i) (S.π 0 ≫ f 0 ≫ inv (S'.π 0))
    (fun j => j.elim0), ⟨fun i => ?_, fun i => i.elim0, fun i => i.elim0⟩, fun g hg => ?_⟩
  · obtain rfl : i = 0 := Fin.ext (by omega)
    simp
  · funext i
    obtain rfl : i = 0 := Fin.ext (by omega)
    rw [Fin.cases_zero, ← cancel_mono (S'.π 0), hg.1 0]
    simp

/-- Let `A` be a nonzero object. A distinguished triangle `Y ⟶ A ⟶ A⟦1⟧ ⟶ Y⟦1⟧` whose second
morphism is zero comes with a section `s : A ⟶ Y` of `Y ⟶ A` and with a nonzero morphism
`j : A ⟶ Y` killed by `Y ⟶ A`. -/
private lemma exists_triangle_zero_mor₂ (A : D) (hA : 𝟙 A ≠ 0) :
    ∃ (Y : D) (π : Y ⟶ A) (δ : A⟦(1 : ℤ)⟧ ⟶ Y⟦(1 : ℤ)⟧) (j : A ⟶ Y) (s : A ⟶ Y),
      Triangle.mk π (0 : A ⟶ A⟦(1 : ℤ)⟧) δ ∈ distTriang D ∧ j ≫ π = 0 ∧ j ≠ 0 ∧
        s ≫ π = 𝟙 A := by
  obtain ⟨Y, π, δ, hT⟩ := distinguished_cocone_triangle₁ (0 : A ⟶ A⟦(1 : ℤ)⟧)
  have hT' := inv_rot_of_distTriang _ hT
  obtain ⟨s, hs⟩ := (Triangle.mk π (0 : A ⟶ A⟦(1 : ℤ)⟧) δ).coyoneda_exact₂ hT (𝟙 A) comp_zero
  obtain ⟨ι, hmono, h12⟩ : ∃ ι : (A⟦(1 : ℤ)⟧)⟦(-1 : ℤ)⟧ ⟶ Y, Mono ι ∧ ι ≫ π = 0 :=
    ⟨_, Triangle.mono₁ _ hT' zero_comp, comp_distTriang_mor_zero₁₂ _ hT'⟩
  let e : A ≅ (A⟦(1 : ℤ)⟧)⟦(-1 : ℤ)⟧ :=
    ((shiftFunctorCompIsoId D (1 : ℤ) (-1) (by norm_num)).app A).symm
  refine ⟨Y, π, δ, e.hom ≫ ι, s, hT,
    by rw [Category.assoc, h12, comp_zero], fun h => hA ?_, hs.symm⟩
  have he : e.hom = 0 := (cancel_mono _).1 (h.trans zero_comp.symm)
  rw [← e.hom_inv_id, he, zero_comp]

/-- In a pretriangulated category with a nonzero object, there is a complex `X₁ ⟶ X₀` of length
`1`, a Postnikov system for it and a morphism of complexes extending to two different morphisms of
Postnikov systems. -/
private lemma exists_isHomOver_ne_of_length_one (A : D) (hA : 𝟙 A ≠ 0) :
    ∃ (X : Fin 2 → D) (d : ∀ i : Fin 1, X i.succ ⟶ X i.castSucc) (S : PostnikovSystem X d)
      (f : ∀ i, X i ⟶ X i), (∀ i : Fin 1, d i ≫ f i.castSucc = f i.succ ≫ d i) ∧
      ∃ g g' : ∀ i, S.obj i ⟶ S.obj i, S.IsHomOver S f g ∧ S.IsHomOver S f g' ∧ g ≠ g' := by
  obtain ⟨Y, π, δ, j, s, hT, hj, hj0, hs⟩ := exists_triangle_zero_mor₂ A hA
  let S : PostnikovSystem ![A⟦(1 : ℤ)⟧, A] (fun _ => 0) :=
    { obj := ![A⟦(1 : ℤ)⟧, Y]
      π := fun i => match i with
        | ⟨0, _⟩ => 𝟙 _
        | ⟨1, _⟩ => π
      isIso_π_zero := inferInstanceAs (IsIso (𝟙 (A⟦(1 : ℤ)⟧)))
      p := fun _ => 0
      δ := fun i => match i with
        | ⟨0, _⟩ => δ
      distinguished := fun i => match i with
        | ⟨0, _⟩ => hT
      p_comp_π := fun _ => zero_comp }
  refine ⟨_, _, S, 0, fun _ => by simp, 0, fun i => match i with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => π ≫ j, ⟨fun _ => by simp, fun _ => by simp, fun _ => by simp⟩,
    ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩, fun h => hj0 ?_⟩
  · match i with
    | ⟨0, _⟩ =>
      change (0 : A⟦(1 : ℤ)⟧ ⟶ A⟦(1 : ℤ)⟧) ≫ 𝟙 _ = 𝟙 _ ≫ 0
      simp
    | ⟨1, _⟩ =>
      change (π ≫ j) ≫ π = π ≫ (0 : A ⟶ A)
      simp only [Category.assoc, hj, comp_zero]
  · match i with
    | ⟨0, _⟩ =>
      change (0 : A ⟶ A⟦(1 : ℤ)⟧) ≫ (0 : A⟦(1 : ℤ)⟧ ⟶ A⟦(1 : ℤ)⟧) = (0 : A ⟶ A) ≫ 0
      simp
  · match i with
    | ⟨0, _⟩ =>
      have h31 : δ ≫ π⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
      change δ ≫ (π ≫ j)⟦(1 : ℤ)⟧' = (0 : A⟦(1 : ℤ)⟧ ⟶ A⟦(1 : ℤ)⟧) ≫ δ
      rw [Functor.map_comp, ← Category.assoc, h31, zero_comp, zero_comp]
  · have h1 := congrFun h ⟨1, by norm_num⟩
    change (0 : Y ⟶ Y) = π ≫ j at h1
    rw [← Category.id_comp j, ← hs, Category.assoc, ← h1, comp_zero]

/-- In a pretriangulated category with a nonzero object, there is a complex `X₂ ⟶ X₁ ⟶ X₀` of
length `2` with two Postnikov systems such that the identity of the complex does not extend to a
morphism of Postnikov systems between them. -/
private lemma not_exists_isHomOver_of_length_two (A : D) (hA : 𝟙 A ≠ 0) :
    ∃ (X : Fin 3 → D) (d : ∀ i : Fin 2, X i.succ ⟶ X i.castSucc), d 1 ≫ d 0 = 0 ∧
      ∃ S S' : PostnikovSystem X d, ¬ ∃ g, S.IsHomOver S' (fun i => 𝟙 (X i)) g := by
  obtain ⟨Y, π, δ, j, s, hT, hj, hj0, -⟩ := exists_triangle_zero_mor₂ A hA
  obtain ⟨Y₂, π₂, δ₂, hT₂⟩ := distinguished_cocone_triangle₁ (0 : A ⟶ Y)
  obtain ⟨Y₂', π₂', δ₂', hT₂'⟩ := distinguished_cocone_triangle₁ j
  let S : PostnikovSystem ![A⟦(1 : ℤ)⟧, A, A] (fun _ => 0) :=
    { obj := ![A⟦(1 : ℤ)⟧, Y, Y₂]
      π := fun i => match i with
        | ⟨0, _⟩ => 𝟙 _
        | ⟨1, _⟩ => π
        | ⟨2, _⟩ => π₂
      isIso_π_zero := inferInstanceAs (IsIso (𝟙 (A⟦(1 : ℤ)⟧)))
      p := fun _ => 0
      δ := fun i => match i with
        | ⟨0, _⟩ => δ
        | ⟨1, _⟩ => δ₂
      distinguished := fun i => match i with
        | ⟨0, _⟩ => hT
        | ⟨1, _⟩ => hT₂
      p_comp_π := fun _ => zero_comp }
  let S' : PostnikovSystem ![A⟦(1 : ℤ)⟧, A, A] (fun _ => 0) :=
    { obj := ![A⟦(1 : ℤ)⟧, Y, Y₂']
      π := fun i => match i with
        | ⟨0, _⟩ => 𝟙 _
        | ⟨1, _⟩ => π
        | ⟨2, _⟩ => π₂'
      isIso_π_zero := inferInstanceAs (IsIso (𝟙 (A⟦(1 : ℤ)⟧)))
      p := fun i => match i with
        | ⟨0, _⟩ => 0
        | ⟨1, _⟩ => j
      δ := fun i => match i with
        | ⟨0, _⟩ => δ
        | ⟨1, _⟩ => δ₂'
      distinguished := fun i => match i with
        | ⟨0, _⟩ => hT
        | ⟨1, _⟩ => hT₂'
      p_comp_π := fun i => match i with
        | ⟨0, _⟩ => zero_comp
        | ⟨1, _⟩ => hj }
  refine ⟨_, _, comp_zero, S, S', fun ⟨g, _, hp, _⟩ => hj0 ?_⟩
  have h := hp ⟨1, by norm_num⟩
  change (0 : A ⟶ Y) ≫ g ⟨1, by norm_num⟩ = 𝟙 A ≫ j at h
  exact ((Category.id_comp j).symm.trans h.symm).trans zero_comp

/-! ### Nonexistence of Postnikov systems in length `n > 2` -/

/-- The terms of the complex `⋯ ⟶ A ⟶ A ⟶ B ⟶ C ⟶ A⟦1⟧` attached to a triangle
`A ⟶ B ⟶ C ⟶ A⟦1⟧`, indexed downwards from `X₀ = A⟦1⟧`. -/
private def triangleComplexObj (T : Triangle D) : ℕ → D
  | 0 => T.obj₁⟦(1 : ℤ)⟧
  | 1 => T.obj₃
  | 2 => T.obj₂
  | _ + 3 => T.obj₁

/-- The morphisms `Xₖ₊₁ ⟶ Xₖ` of the complex `⋯ ⟶ A ⟶ A ⟶ B ⟶ C ⟶ A⟦1⟧`: the three morphisms of
the triangle, followed by zeros. -/
private def triangleComplexHom (T : Triangle D) :
    ∀ k : ℕ, triangleComplexObj T (k + 1) ⟶ triangleComplexObj T k
  | 0 => T.mor₃
  | 1 => T.mor₂
  | 2 => T.mor₁
  | _ + 3 => 0

/-- Consecutive morphisms of the complex attached to a distinguished triangle compose to zero. -/
private lemma triangleComplexHom_comp {T : Triangle D} (hT : T ∈ distTriang D) :
    ∀ k : ℕ, triangleComplexHom T (k + 1) ≫ triangleComplexHom T k = 0
  | 0 => comp_distTriang_mor_zero₂₃ _ hT
  | 1 => comp_distTriang_mor_zero₁₂ _ hT
  | 2 => zero_comp
  | _ + 3 => zero_comp

/-- Let `A ⟶ B ⟶ C ⟶ A⟦1⟧` be a distinguished triangle and `n ≥ 3`. If the complex
`Xₙ ⟶ ⋯ ⟶ X₀` given by `⋯ ⟶ A ⟶ A ⟶ B ⟶ C ⟶ A⟦1⟧` admits a Postnikov system, then the morphism
`h : C ⟶ A⟦1⟧` is von Neumann regular: `h ≫ s ≫ h = h` for some `s`. -/
private lemma exists_comp_comp_eq_of_postnikovSystem {T : Triangle D} (hT : T ∈ distTriang D)
    {n : ℕ} (hn : 3 ≤ n)
    (S : PostnikovSystem (fun i : Fin (n + 1) => triangleComplexObj T i)
      (fun i => triangleComplexHom T i)) :
    ∃ s : T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₃, T.mor₃ ≫ s ≫ T.mor₃ = T.mor₃ := by
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  let i₂ : Fin n := ⟨2, by omega⟩
  have key : ∀ {Y₀ Y₁ Y₂ : D} (π₁ : Y₁ ⟶ T.obj₃) (π₂ : Y₂ ⟶ T.obj₂) (π₀ : Y₀ ⟶ T.obj₁⟦(1 : ℤ)⟧)
      (p₀ : T.obj₃ ⟶ Y₀) (p₁ : T.obj₂ ⟶ Y₁) (p₂ : T.obj₁ ⟶ Y₂), π₁ ≫ p₀ = 0 → π₂ ≫ p₁ = 0 →
      p₀ ≫ π₀ = T.mor₃ → p₁ ≫ π₁ = T.mor₂ → p₂ ≫ π₂ = T.mor₁ →
      ∃ s : T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₃, T.mor₃ ≫ s ≫ T.mor₃ = T.mor₃ := by
    intro Y₀ Y₁ Y₂ π₁ π₂ π₀ p₀ p₁ p₂ h₀ h₁ hp₀ hp₁ hp₂
    have hfq : T.mor₁ ≫ p₁ = 0 := by rw [← hp₂, Category.assoc, h₁, comp_zero]
    obtain ⟨r, hr⟩ := T.yoneda_exact₂ hT p₁ hfq
    obtain ⟨s, hs⟩ := T.yoneda_exact₃ hT (𝟙 _ - r ≫ π₁) (by
      rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, ← hr, hp₁, sub_self])
    refine ⟨s, ?_⟩
    have hπh : π₁ ≫ T.mor₃ = 0 := by rw [← hp₀, ← Category.assoc, h₀, zero_comp]
    rw [← Category.assoc, ← hs, Preadditive.sub_comp, Category.id_comp, Category.assoc, hπh,
      comp_zero, sub_zero]
  exact key (S.π i₁.castSucc) (S.π i₂.castSucc) (S.π i₀.castSucc) (S.p i₀) (S.p i₁) (S.p i₂)
    (comp_distTriang_mor_zero₁₂ _ (S.distinguished i₀))
    (comp_distTriang_mor_zero₁₂ _ (S.distinguished i₁))
    (S.p_comp_π i₀) (S.p_comp_π i₁) (S.p_comp_π i₂)

/-- In the homotopy category of `ℤ`-modules, let `Z` be `ℤ` placed in degree `0`. Then
`2 • 𝟙 Z` is not divisible by `4`. -/
private lemma four_smul_ne_two_smul_id
    (t : (HomotopyCategory.quotient _ _).obj ((HomologicalComplex.single (ModuleCat.{0} ℤ)
      (ComplexShape.up ℤ) 0).obj (ModuleCat.of ℤ ℤ)) ⟶
      (HomotopyCategory.quotient _ _).obj ((HomologicalComplex.single (ModuleCat.{0} ℤ)
      (ComplexShape.up ℤ) 0).obj (ModuleCat.of ℤ ℤ))) :
    (4 : ℤ) • t ≠ (2 : ℤ) • 𝟙 _ := by
  intro h
  let H := HomotopyCategory.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℤ) 0
  let E := (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} ℤ) (ComplexShape.up ℤ) 0).app
      ((HomologicalComplex.single (ModuleCat.{0} ℤ) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of ℤ ℤ)) ≪≫
    (HomologicalComplex.homologyFunctorSingleIso (ModuleCat.{0} ℤ) (ComplexShape.up ℤ) 0).app
      (ModuleCat.of ℤ ℤ)
  have h' := congrArg (fun u => E.inv ≫ H.map u ≫ E.hom) h
  simp only [Functor.map_zsmul, Functor.map_id, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul] at h'
  have h1 := congrArg (fun u : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ => u.hom (1 : ℤ)) h'
  simp at h1
  omega

/-- In the homotopy category of `ℤ`-modules, for every `n > 2` there is a complex
`Xₙ ⟶ ⋯ ⟶ X₀` of length `n` admitting no Postnikov system. -/
private lemma exists_isEmpty_postnikovSystem_homotopyCategory {n : ℕ} (hn : 2 < n) :
    ∃ (X : Fin (n + 1) → HomotopyCategory (ModuleCat.{0} ℤ) (ComplexShape.up ℤ))
      (d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc),
      (∀ (i : Fin n) (h : (i : ℕ) + 1 < n), d ⟨(i : ℕ) + 1, h⟩ ≫ d i = 0) ∧
        IsEmpty (PostnikovSystem X d) := by
  let Z := (HomotopyCategory.quotient _ _).obj ((HomologicalComplex.single (ModuleCat.{0} ℤ)
    (ComplexShape.up ℤ) 0).obj (ModuleCat.of ℤ ℤ))
  let e : Z ≅ (Z⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧ :=
    ((shiftFunctorCompIsoId _ (-1 : ℤ) (1 : ℤ) (by norm_num)).app Z).symm
  obtain ⟨Y, f, g, hT⟩ := distinguished_cocone_triangle₂ ((2 : ℤ) • e.hom)
  refine ⟨fun i => triangleComplexObj (Triangle.mk f g ((2 : ℤ) • e.hom)) i,
    fun i => triangleComplexHom (Triangle.mk f g ((2 : ℤ) • e.hom)) i,
    fun i _ => triangleComplexHom_comp hT i, ⟨fun S => ?_⟩⟩
  obtain ⟨s, hs⟩ := exists_comp_comp_eq_of_postnikovSystem hT (by omega) S
  apply four_smul_ne_two_smul_id (e.hom ≫ s)
  have hs' := congrArg (· ≫ e.inv) hs
  simp only [Triangle.mk_obj₁, Triangle.mk_obj₃, Triangle.mk_mor₃, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul, Category.assoc, e.hom_inv_id, Category.comp_id, smul_smul] at hs'
  norm_num at hs'
  exact hs'

/-- Let `D` be a pretriangulated category and consider Postnikov systems for complexes
`Xₙ ⟶ ⋯ ⟶ X₀` of length `n`, with morphisms of Postnikov systems in the sense of
`PostnikovSystem.IsHomOver`.

1. For `n = 0` Postnikov systems always exist and any morphism of complexes extends to a unique
   morphism of Postnikov systems.
2. For `n = 1` Postnikov systems always exist and any morphism of complexes extends to a morphism
   of Postnikov systems; this extension is not unique in general.
3. For `n = 2` Postnikov systems always exist, but morphisms of complexes do not extend to
   morphisms of Postnikov systems in general.
4. For `n > 2` Postnikov systems do not always exist.

The failures in (2), (3) and (4) are exhibited in the homotopy category of `ℤ`-modules, which is
triangulated. -/
@[stacks 0D81 "existence in (1)–(3), the unique extension of morphisms in (1) and the extension \
in (2) hold in every pretriangulated category; the non-uniqueness in (2), the non-extension in (3) \
and the non-existence in (4), for every n > 2, are witnessed in the triangulated homotopy category \
K(ℤ-Mod)."]
theorem postnikovSystem_small_cases :
    ((∀ (X : Fin 1 → D) (d : ∀ i : Fin 0, X i.succ ⟶ X i.castSucc),
        Nonempty (PostnikovSystem X d)) ∧
      ∀ {X X' : Fin 1 → D} {d : ∀ i : Fin 0, X i.succ ⟶ X i.castSucc}
        {d' : ∀ i : Fin 0, X' i.succ ⟶ X' i.castSucc} (S : PostnikovSystem X d)
        (S' : PostnikovSystem X' d') (f : ∀ i, X i ⟶ X' i),
        (∀ i : Fin 0, d i ≫ f i.castSucc = f i.succ ≫ d' i) →
        ∃! g : ∀ i, S.obj i ⟶ S'.obj i, S.IsHomOver S' f g) ∧
    ((∀ (X : Fin 2 → D) (d : ∀ i : Fin 1, X i.succ ⟶ X i.castSucc),
        Nonempty (PostnikovSystem X d)) ∧
      (∀ {X X' : Fin 2 → D} {d : ∀ i : Fin 1, X i.succ ⟶ X i.castSucc}
        {d' : ∀ i : Fin 1, X' i.succ ⟶ X' i.castSucc} (S : PostnikovSystem X d)
        (S' : PostnikovSystem X' d') (f : ∀ i, X i ⟶ X' i),
        (∀ i : Fin 1, d i ≫ f i.castSucc = f i.succ ≫ d' i) →
        ∃ g : ∀ i, S.obj i ⟶ S'.obj i, S.IsHomOver S' f g) ∧
      ∃ (X : Fin 2 → HomotopyCategory (ModuleCat.{0} ℤ) (ComplexShape.up ℤ))
        (d : ∀ i : Fin 1, X i.succ ⟶ X i.castSucc) (S : PostnikovSystem X d)
        (f : ∀ i, X i ⟶ X i), (∀ i : Fin 1, d i ≫ f i.castSucc = f i.succ ≫ d i) ∧
        ∃ g g' : ∀ i, S.obj i ⟶ S.obj i, S.IsHomOver S f g ∧ S.IsHomOver S f g' ∧ g ≠ g') ∧
    ((∀ (X : Fin 3 → D) (d : ∀ i : Fin 2, X i.succ ⟶ X i.castSucc), d 1 ≫ d 0 = 0 →
        Nonempty (PostnikovSystem X d)) ∧
      ∃ (X : Fin 3 → HomotopyCategory (ModuleCat.{0} ℤ) (ComplexShape.up ℤ))
        (d : ∀ i : Fin 2, X i.succ ⟶ X i.castSucc), d 1 ≫ d 0 = 0 ∧
        ∃ S S' : PostnikovSystem X d, ¬ ∃ g, S.IsHomOver S' (fun i => 𝟙 (X i)) g) ∧
    (∀ n : ℕ, 2 < n → ∃ (X : Fin (n + 1) → HomotopyCategory (ModuleCat.{0} ℤ) (ComplexShape.up ℤ))
      (d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc),
      (∀ (i : Fin n) (h : (i : ℕ) + 1 < n), d ⟨(i : ℕ) + 1, h⟩ ≫ d i = 0) ∧
        IsEmpty (PostnikovSystem X d)) ∧
    IsTriangulated (HomotopyCategory (ModuleCat.{0} ℤ) (ComplexShape.up ℤ)) := by
  have hZ : 𝟙 ((HomotopyCategory.quotient _ _).obj ((HomologicalComplex.single
      (ModuleCat.{0} ℤ) (ComplexShape.up ℤ) 0).obj (ModuleCat.of ℤ ℤ))) ≠ 0 := fun h =>
    four_smul_ne_two_smul_id 0 (by rw [h, smul_zero, smul_zero])
  refine ⟨⟨fun X d => nonempty_postnikovSystem_of_length_le_two (by norm_num) X d
      (fun i => i.elim0), fun S S' f _ => existsUnique_isHomOver_of_length_zero S S' f⟩,
    ⟨fun X d => nonempty_postnikovSystem_of_length_le_two (by norm_num) X d
      (fun i h => absurd h (by omega)), fun {X X' d d'} S S' f hf =>
      (PostnikovSystem.hom_shift_obj_eq_zero_and_exists_hom X d S'
        (fun i j hij => absurd hij (by omega))).2 S f hf,
      exists_isHomOver_ne_of_length_one _ hZ⟩,
    ⟨fun X d hd => nonempty_postnikovSystem_of_length_le_two le_rfl X d (fun i h => ?_),
      not_exists_isHomOver_of_length_two _ hZ⟩,
    fun n hn => exists_isEmpty_postnikovSystem_homotopyCategory hn, inferInstance⟩
  obtain rfl : i = 0 := Fin.ext (by omega)
  exact hd

end CategoryTheory.Triangulated

end
