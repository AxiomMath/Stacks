module

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# The five lemma for morphisms out of a shift-stable class of objects

Let `φ : T₁ ⟶ T₂` be a morphism of distinguished triangles in a pretriangulated category and let
`P` be a property of objects stable under all shifts. If composing with `φ.hom₂` and with
`φ.hom₃` is bijective on morphisms out of every object satisfying `P`, then so is composing with
`φ.hom₁`. This is the five lemma for the homological functors `Hom(E, -)`, proved by the usual
diagram chase on the long exact sequences of a distinguished triangle.

## Main results

* `CategoryTheory.Pretriangulated.injective_comp_hom₂` and
  `CategoryTheory.Pretriangulated.surjective_comp_hom₂`: the two four lemmas at the second vertex.
* `CategoryTheory.Pretriangulated.bijective_comp_shift_map`: bijectivity of composition with
  `g` on morphisms out of a shift-stable class is inherited by `g⟦n⟧'`.
* `CategoryTheory.Pretriangulated.bijective_comp_hom₁`: the five lemma at the first vertex.
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Limits Preadditive

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
    [Pretriangulated C] in
/-- Composition with a morphism is injective as soon as only `0` is sent to `0`. -/
lemma injective_comp_of_eq_zero {E X Y : C} (g : X ⟶ Y)
    (h : ∀ x : E ⟶ X, x ≫ g = 0 → x = 0) : Function.Injective (fun x : E ⟶ X => x ≫ g) := by
  intro x y hxy
  have : (x - y) ≫ g = 0 := by
    simp only at hxy
    rw [sub_comp, hxy, sub_self]
  exact sub_eq_zero.1 (h _ this)

/-- If composition with `g` is injective, a morphism whose composite with `g` vanishes is zero. -/
private lemma eq_zero_of_injective_comp {D : Type*} [Category D] [Preadditive D]
    {E X Y : D} (g : X ⟶ Y)
    (hg : Function.Injective (fun x : E ⟶ X => x ≫ g)) {x : E ⟶ X} (hx : x ≫ g = 0) : x = 0 :=
  hg (by simpa using hx)

/-- **The four lemma (monomorphism half) at the second vertex.** -/
lemma injective_comp_hom₂ {T₁ T₂ : Triangle C} (φ : T₁ ⟶ T₂) (h₁ : T₁ ∈ distTriang C)
    (h₂ : T₂ ∈ distTriang C) (E : C)
    (ha : Function.Injective (fun x : E ⟶ T₁.obj₁ => x ≫ φ.hom₁))
    (hc : Function.Injective (fun x : E ⟶ T₁.obj₃ => x ≫ φ.hom₃))
    (hd : Function.Surjective (fun x : E ⟶ T₁.obj₃⟦(-1 : ℤ)⟧ => x ≫ φ.hom₃⟦(-1 : ℤ)⟧')) :
    Function.Injective (fun x : E ⟶ T₁.obj₂ => x ≫ φ.hom₂) := by
  refine injective_comp_of_eq_zero _ fun x hx => ?_
  have hx₂ : x ≫ T₁.mor₂ = 0 :=
    eq_zero_of_injective_comp _ hc
      (by rw [Category.assoc, φ.comm₂, ← Category.assoc, hx, zero_comp])
  obtain ⟨y, rfl⟩ := Triangle.coyoneda_exact₂ T₁ h₁ x hx₂
  have hy : (y ≫ φ.hom₁) ≫ T₂.mor₁ = 0 := by
    rw [Category.assoc, ← φ.comm₁, ← Category.assoc, hx]
  obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ h₂) (y ≫ φ.hom₁) hy
  obtain ⟨w, rfl⟩ := hd z
  obtain rfl : y = w ≫ (Triangle.invRotate T₁).mor₁ :=
    ha (hz.trans ((Category.assoc _ _ _).trans
      ((congrArg (w ≫ ·) ((invRotate C).map φ).comm₁.symm).trans
        (Category.assoc _ _ _).symm)))
  exact (Category.assoc _ _ _).trans
    ((congrArg (w ≫ ·) (comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang _ h₁))).trans comp_zero)

/-- **The four lemma (epimorphism half) at the second vertex.** -/
lemma surjective_comp_hom₂ {T₁ T₂ : Triangle C} (φ : T₁ ⟶ T₂) (h₁ : T₁ ∈ distTriang C)
    (h₂ : T₂ ∈ distTriang C) (E : C)
    (ha : Function.Surjective (fun x : E ⟶ T₁.obj₁ => x ≫ φ.hom₁))
    (hc : Function.Surjective (fun x : E ⟶ T₁.obj₃ => x ≫ φ.hom₃))
    (hd : Function.Injective (fun x : E ⟶ T₁.obj₁⟦(1 : ℤ)⟧ => x ≫ φ.hom₁⟦(1 : ℤ)⟧')) :
    Function.Surjective (fun x : E ⟶ T₁.obj₂ => x ≫ φ.hom₂) := by
  intro x
  obtain ⟨y, hy⟩ := hc (x ≫ T₂.mor₂)
  simp only at hy
  have hy₃ : y ≫ T₁.mor₃ = 0 := by
    refine eq_zero_of_injective_comp _ hd ?_
    rw [Category.assoc, φ.comm₃, ← Category.assoc, hy, Category.assoc,
      comp_distTriang_mor_zero₂₃ _ h₂, comp_zero]
  obtain ⟨z, rfl⟩ := Triangle.coyoneda_exact₃ T₁ h₁ y hy₃
  have hw : (x - z ≫ φ.hom₂) ≫ T₂.mor₂ = 0 := by
    rw [sub_comp, ← hy, Category.assoc, Category.assoc, φ.comm₂, sub_self]
  obtain ⟨w, hw'⟩ := Triangle.coyoneda_exact₂ T₂ h₂ _ hw
  obtain ⟨w', rfl⟩ := ha w
  refine ⟨z + w' ≫ T₁.mor₁, ?_⟩
  simp only at hw' ⊢
  rw [add_comp, Category.assoc, φ.comm₁, ← Category.assoc, ← hw', add_sub_cancel]

omit [Preadditive C] [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
    [Pretriangulated C] in
/-- Bijectivity of composition with `g` on morphisms out of a shift-stable class of objects is
inherited by every shift `g⟦n⟧'`. -/
lemma bijective_comp_shift_map (P : C → Prop) (hP : ∀ (E : C) (n : ℤ), P E → P (E⟦n⟧))
    {X Y : C} (g : X ⟶ Y)
    (hg : ∀ E, P E → Function.Bijective (fun x : E ⟶ X => x ≫ g)) (n : ℤ) :
    ∀ E, P E → Function.Bijective (fun x : E ⟶ X⟦n⟧ => x ≫ g⟦n⟧') := by
  intro E hE
  let e : E ≅ (E⟦-n⟧)⟦n⟧ := (shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).symm.app E
  have hF : Function.Bijective
      (fun x : (E⟦-n⟧)⟦n⟧ ⟶ X⟦n⟧ => x ≫ g⟦n⟧') := by
    have h := hg _ (hP E (-n) hE)
    have hpre : Function.Bijective
        (fun x : (E⟦-n⟧)⟦n⟧ ⟶ X⟦n⟧ => (shiftFunctor C n).preimage x) :=
      ⟨fun a b hab => by simpa using congrArg (shiftFunctor C n).map hab,
        fun y => ⟨(shiftFunctor C n).map y, by simp⟩⟩
    have hmap : Function.Bijective (fun y : E⟦-n⟧ ⟶ Y => (shiftFunctor C n).map y) :=
      ⟨(shiftFunctor C n).map_injective, (shiftFunctor C n).map_surjective⟩
    have heq : (fun x : (E⟦-n⟧)⟦n⟧ ⟶ X⟦n⟧ => x ≫ g⟦n⟧') =
        (fun y : E⟦-n⟧ ⟶ Y => (shiftFunctor C n).map y) ∘ (fun x : E⟦-n⟧ ⟶ X => x ≫ g) ∘
          (fun x : (E⟦-n⟧)⟦n⟧ ⟶ X⟦n⟧ => (shiftFunctor C n).preimage x) := by
      funext x
      simp
    rw [heq]
    exact hmap.comp (h.comp hpre)
  have hi : ∀ {A B : C} (e : A ≅ B) (Z : C), Function.Bijective (fun y : B ⟶ Z => e.hom ≫ y) :=
    fun e Z => ⟨fun a b hab => by simpa using congrArg (e.inv ≫ ·) hab,
      fun y => ⟨e.inv ≫ y, by simp⟩⟩
  have h₁ := hi e (Y⟦n⟧)
  have h₂ := hi e.symm (X⟦n⟧)
  have heq : (fun x : E ⟶ X⟦n⟧ => x ≫ g⟦n⟧') =
      (fun y : (E⟦-n⟧)⟦n⟧ ⟶ Y⟦n⟧ => e.hom ≫ y) ∘ (fun x : (E⟦-n⟧)⟦n⟧ ⟶ X⟦n⟧ => x ≫ g⟦n⟧') ∘
        (fun x : E ⟶ X⟦n⟧ => e.inv ≫ x) := by
    funext x
    simp
  rw [heq]
  exact h₁.comp (hF.comp h₂)

/-- **The five lemma for `Hom` out of a shift-stable class.** For a morphism `φ` of distinguished
triangles, if composing with `φ.hom₂` and with `φ.hom₃` is bijective on morphisms out of every
object satisfying `P`, and `P` is stable under shifts, then so is composing with `φ.hom₁`. -/
theorem bijective_comp_hom₁ {T₁ T₂ : Triangle C} (φ : T₁ ⟶ T₂) (h₁ : T₁ ∈ distTriang C)
    (h₂ : T₂ ∈ distTriang C) (P : C → Prop) (hP : ∀ (E : C) (n : ℤ), P E → P (E⟦n⟧))
    (hb : ∀ E, P E → Function.Bijective (fun x : E ⟶ T₁.obj₂ => x ≫ φ.hom₂))
    (hc : ∀ E, P E → Function.Bijective (fun x : E ⟶ T₁.obj₃ => x ≫ φ.hom₃)) :
    ∀ E, P E → Function.Bijective (fun x : E ⟶ T₁.obj₁ => x ≫ φ.hom₁) := by
  intro E hE
  let ψ := (invRotate C).map φ
  have h₁' := inv_rot_of_distTriang _ h₁
  have h₂' := inv_rot_of_distTriang _ h₂
  have hc₁ := bijective_comp_shift_map P hP φ.hom₃ hc (-1)
  exact ⟨injective_comp_hom₂ ψ h₁' h₂' E (hc₁ E hE).1 (hb E hE).1
      (bijective_comp_shift_map P hP φ.hom₂ hb (-1) E hE).2,
    surjective_comp_hom₂ ψ h₁' h₂' E (hc₁ E hE).2 (hb E hE).2
      (bijective_comp_shift_map P hP (φ.hom₃⟦(-1 : ℤ)⟧') hc₁ 1 E hE).1⟩

/-- Bijectivity of composition with a morphism is invariant under isomorphisms of the source
object and of the arrow. -/
lemma bijective_comp_iff_of_iso {D : Type*} [Category D] {E E' A B A' B' : D} (e : E ≅ E')
    (g : A ⟶ B) (g' : A' ⟶ B') (eA : A ≅ A') (eB : B ≅ B') (w : g ≫ eB.hom = eA.hom ≫ g') :
    Function.Bijective (fun x : E ⟶ A => x ≫ g) ↔
      Function.Bijective (fun x : E' ⟶ A' => x ≫ g') := by
  have heq : (fun x : E ⟶ A => x ≫ g) =
      (fun y : E' ⟶ B' => e.hom ≫ y ≫ eB.inv) ∘ (fun x : E' ⟶ A' => x ≫ g') ∘
        (fun x : E ⟶ A => e.inv ≫ x ≫ eA.hom) := by
    funext x
    simp only [Function.comp_apply, Category.assoc, ← reassoc_of% w, Iso.hom_inv_id,
      Category.comp_id, Iso.hom_inv_id_assoc]
  have h₁ : Function.Bijective (fun y : E' ⟶ B' => e.hom ≫ y ≫ eB.inv) :=
    ((e.homCongr eB).symm).bijective
  have h₂ : Function.Bijective (fun x : E ⟶ A => e.inv ≫ x ≫ eA.hom) :=
    (e.homCongr eA).bijective
  rw [heq]
  exact ⟨fun h =>
    (Function.Bijective.of_comp_iff _ h₂).1 ((Function.Bijective.of_comp_iff' h₁ _).1 h),
    fun h => h₁.comp (h.comp h₂)⟩

/-- **A morphism inducing bijections on `Hom` out of a shift-stable class has a cone receiving
no morphism from that class.** For a distinguished triangle `A ⟶ B ⟶ C ⟶ A⟦1⟧` whose first
morphism induces bijections on morphisms out of every object satisfying the shift-stable
property `P`, every morphism from such an object to `C` is zero. -/
lemma eq_zero_of_bijective_comp_mor₁ (T : Triangle C) (hT : T ∈ distTriang C) (P : C → Prop)
    (hP : ∀ (E : C) (n : ℤ), P E → P (E⟦n⟧))
    (h : ∀ E, P E → Function.Bijective (fun x : E ⟶ T.obj₁ => x ≫ T.mor₁))
    (E : C) (hE : P E) (w : E ⟶ T.obj₃) : w = 0 := by
  have hinj := (bijective_comp_shift_map P hP T.mor₁ h 1 E hE).1
  have hv : w ≫ T.mor₃ = 0 := by
    refine eq_zero_of_injective_comp _ hinj ?_
    simp only [Category.assoc, comp_distTriang_mor_zero₃₁ _ hT, comp_zero]
  obtain ⟨u, rfl⟩ := Triangle.coyoneda_exact₃ T hT w hv
  obtain ⟨x, rfl⟩ := (h E hE).2 u
  simp only [Category.assoc, comp_distTriang_mor_zero₁₂ _ hT, comp_zero]

/-- **Conversely, if `C` receives no morphism from `E` nor from `E⟦1⟧`, the first morphism of the
triangle induces a bijection on morphisms out of `E`.** -/
lemma bijective_comp_mor₁_of_eq_zero (T : Triangle C) (hT : T ∈ distTriang C) (E : C)
    (h₀ : ∀ w : E ⟶ T.obj₃, w = 0) (h₁ : ∀ w : E⟦(1 : ℤ)⟧ ⟶ T.obj₃, w = 0) :
    Function.Bijective (fun x : E ⟶ T.obj₁ => x ≫ T.mor₁) := by
  refine ⟨injective_comp_of_eq_zero _ fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨z, rfl⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hT) x hx
    obtain rfl : z = 0 := by
      apply (shiftFunctor C (1 : ℤ)).map_injective
      rw [Functor.map_zero]
      exact (cancel_mono ((shiftFunctorCompIsoId C (-1 : ℤ) 1 (by omega)).app T.obj₃).hom).1
        ((h₁ (z⟦(1 : ℤ)⟧' ≫ (shiftFunctorCompIsoId C (-1 : ℤ) 1 (by omega)).hom.app T.obj₃)).trans
          zero_comp.symm)
    exact zero_comp
  · obtain ⟨x, hx⟩ := Triangle.coyoneda_exact₂ T hT y (h₀ _)
    exact ⟨x, hx.symm⟩

end CategoryTheory.Pretriangulated
