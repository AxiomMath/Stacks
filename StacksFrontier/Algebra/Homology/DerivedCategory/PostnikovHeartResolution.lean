module

public import StacksFrontier.CategoryTheory.Triangulated.SequentialPostnikovSystems
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ShiftedDegreeZero
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# The Postnikov system of a resolution placed in degree zero

Let `C` be an abelian category and `⋯ ⟶ X₂ ⟶ X₁ ⟶ X₀` a complex in `D(C)` whose terms lie in
the heart, i.e. have cohomology only in degree `0`, and whose complex of `H⁰`'s is exact in
every positive degree, with `H⁰(X₀) ⟶ O` a cokernel of `H⁰(X₁) ⟶ H⁰(X₀)`. This is what a
resolution `⋯ → M₁ → M₀ → O → 0` of an object of `C` becomes when each `Mᵢ` is placed in
degree zero. For any sequential Postnikov system `Y₀, Y₁, …` of that complex the objects
`Yₙ⟦n⟧` have cohomology only in degrees `-n` and `0`, and `H⁰(Yₙ⟦n⟧) ≅ O` for `n ≥ 1`.

Consequently `Yₙ⟦n⟧` sits, for `n ≥ 1`, in a distinguished triangle
`W ⟶ Yₙ⟦n⟧ ⟶ O[0] ⟶ W⟦1⟧` with `W` concentrated in degree `-n`. For the brutal truncations of
the resolution this is the statement that `(Mₙ → ⋯ → M₀)` has cohomology `O` in degree `0` and
`Ker(Mₙ → Mₙ₋₁)` in degree `-n`, which is how it is used in [Stacks, Section 0G07]; the proof
here uses only the triangles of the Postnikov system and the long exact cohomology sequence, so
it applies to every Postnikov system of the complex.

## Main results

* `CategoryTheory.Triangulated.SequentialPostnikovSystem.isZero_homology_obj_of_lt_zero`,
  `.isZero_homology_obj_of_lt`, `.isZero_homology_obj_of_pos_of_lt`: the vanishing of
  `Hⁱ(Yₙ)` for `i < 0`, `i > n` and `0 < i < n`.
* `CategoryTheory.Triangulated.SequentialPostnikovSystem.nonempty_homology_obj_iso`:
  `Hⁿ(Yₙ) ≅ O` for `n ≥ 1`.
* `CategoryTheory.Triangulated.SequentialPostnikovSystem.exists_distTriang_shift_obj`: the
  triangle `W ⟶ Yₙ⟦n⟧ ⟶ O[0] ⟶ W⟦1⟧`.

## References

* [Stacks Project, Section 0G07](https://stacks.math.columbia.edu/tag/0G07)
* [Stacks Project, Tag 0D8Z](https://stacks.math.columbia.edu/tag/0D8Z)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Pretriangulated

universe w v u

namespace CategoryTheory.Triangulated.SequentialPostnikovSystem

section Step

variable {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ t : ℤ, (shiftFunctor D t).Additive] [Pretriangulated D]
  {X : ℕ → D} {d : ∀ n, X (n + 1) ⟶ X n} (P : SequentialPostnikovSystem X d)

/-- An isomorphism scaled by an integer of square one. -/
def zsmulIso {A B : D} (a : A ≅ B) (ε : ℤ) (hε : ε * ε = 1) : A ≅ B where
  hom := ε • a.hom
  inv := ε • a.inv
  hom_inv_id := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, hε, one_smul, a.hom_inv_id]
  inv_hom_id := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, hε, one_smul, a.inv_hom_id]

/-- **The transition maps `Yₙ⟦n⟧ ⟶ Yₙ₊₁⟦n+1⟧` have cone `Xₙ₊₁⟦1⟧⟦n⟧`**: they are the first
morphisms of distinguished triangles `Yₙ⟦n⟧ ⟶ Yₙ₊₁⟦n+1⟧ ⟶ Xₙ₊₁⟦1⟧⟦n⟧ ⟶ Yₙ⟦n⟧⟦1⟧`, the `n`-th
triangle of the system rotated twice and shifted by `n`. -/
theorem exists_distTriang_sequenceStep (n : ℕ) :
    ∃ (u : (P.obj (n + 1))⟦((n + 1 : ℕ) : ℤ)⟧ ⟶ ((X (n + 1))⟦(1 : ℤ)⟧)⟦(n : ℤ)⟧)
      (w : ((X (n + 1))⟦(1 : ℤ)⟧)⟦(n : ℤ)⟧ ⟶ ((P.obj n)⟦(n : ℤ)⟧)⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk (P.sequenceStep n) u w ∈ distTriang D := by
  let T := (Pretriangulated.Triangle.mk (P.π (n + 1)) (P.p n) (P.δ n)).rotate.rotate
  have hT : T ∈ distTriang D :=
    Pretriangulated.rot_of_distTriang _ (Pretriangulated.rot_of_distTriang _ (P.distinguished n))
  let T' := (Pretriangulated.Triangle.shiftFunctor D (n : ℤ)).obj T
  have hT' : T' ∈ distTriang D := Pretriangulated.Triangle.shift_distinguished T hT (n : ℤ)
  let ε : ℤ := ((n : ℤ).negOnePow : ℤ)
  have hε : ε * ε = 1 := by
    simp only [ε, ← Units.val_mul, Int.units_mul_self, Units.val_one]
  let a := ((shiftFunctorAdd' D 1 (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)).app (P.obj (n + 1)))
  let e := zsmulIso a.symm ε hε
  refine ⟨e.inv ≫ T'.mor₂, T'.mor₃, isomorphic_distinguished _ hT' _ ?_⟩
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_
  · change P.sequenceStep n ≫ (ε • a.hom) = 𝟙 _ ≫ ((n : ℤ).negOnePow • ((P.δ n)⟦(n : ℤ)⟧'))
    rw [Units.smul_def, Category.id_comp, Preadditive.comp_zsmul,
      SequentialPostnikovSystem.sequenceStep, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · change (e.inv ≫ T'.mor₂) ≫ 𝟙 _ = e.inv ≫ T'.mor₂
    rw [Category.comp_id]
  · change T'.mor₃ ≫ (𝟙 _)⟦(1 : ℤ)⟧' = 𝟙 _ ≫ T'.mor₃
    rw [Functor.map_id, Category.comp_id, Category.id_comp]

end Step

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {X : ℕ → DerivedCategory C} {d : ∀ n, X (n + 1) ⟶ X n}
  (P : SequentialPostnikovSystem X d)

/-- The `n`-th triangle `Yₙ₊₁ ⟶ Xₙ₊₁ ⟶ Yₙ ⟶ Yₙ₊₁⟦1⟧` of the system. -/
abbrev triangle (n : ℕ) : Triangle (DerivedCategory C) :=
  Triangle.mk (P.π (n + 1)) (P.p n) (P.δ n)

omit [HasDerivedCategory.{w} C] in
/-- A map `q` through which a map `dₙ` with image `ker b` factors, along the kernel `a` of `b`, is
an epimorphism. -/
private theorem epi_of_factor {Z Y Xn Xm : C} (a : Y ⟶ Xn) (b : Xn ⟶ Xm) (hab : a ≫ b = 0)
    [Mono a] (h₁ : (ShortComplex.mk a b hab).Exact) (dn : Z ⟶ Xn) (hdb : dn ≫ b = 0)
    (h₂ : (ShortComplex.mk dn b hdb).Exact) (q : Z ⟶ Y) (hq : q ≫ a = dn) : Epi q := by
  have : Epi (kernel.lift b a hab) := h₁.epi_kernelLift
  have : Mono (kernel.lift b a hab) := mono_of_mono_fac (kernel.lift_ι b a hab)
  have : IsIso (kernel.lift b a hab) := isIso_of_mono_of_epi _
  have hl : kernel.lift b dn hdb = q ≫ kernel.lift b a hab := by
    ext
    rw [kernel.lift_ι, Category.assoc, kernel.lift_ι, hq]
  have : Epi (kernel.lift b dn hdb) := h₂.epi_kernelLift
  rw [show q = kernel.lift b dn hdb ≫ inv (kernel.lift b a hab) by simp [hl]]
  infer_instance

omit [HasDerivedCategory.{w} C] in
/-- `H⁰` of a complex is a complex. -/
theorem _root_.CategoryTheory.Triangulated.homologyMap_comp_eq_zero [HasDerivedCategory.{w} C]
    {X : ℕ → DerivedCategory C} {d : ∀ n, X (n + 1) ⟶ X n} (hd : ∀ n, d (n + 1) ≫ d n = 0)
    (n : ℕ) :
    (DerivedCategory.homologyFunctor C 0).map (d (n + 1)) ≫
      (DerivedCategory.homologyFunctor C 0).map (d n) = 0 := by
  rw [← Functor.map_comp, hd, Functor.map_zero]

/-- `H⁰(Yₙ₊₁) ⟶ H⁰(Xₙ₊₁) ⟶ H⁰(Xₙ)` composes to zero. -/
theorem homologyMap_π_comp_eq_zero (n : ℕ) :
    (DerivedCategory.homologyFunctor C 0).map (P.π (n + 1)) ≫
      (DerivedCategory.homologyFunctor C 0).map (d n) = 0 := by
  rw [← Functor.map_comp, ← P.p_comp_π, ← Category.assoc,
    show P.π (n + 1) ≫ P.p n = 0 from comp_distTriang_mor_zero₁₂ _ (P.distinguished n),
    zero_comp, Functor.map_zero]

/-- `Hⁱ(Y₀)` vanishes if `Hⁱ(X₀)` does. -/
private theorem isZero_homology_obj_zero_of_isZero (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor C i).obj (X 0))) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj (P.obj 0)) :=
  h.of_iso ((DerivedCategory.homologyFunctor C i).mapIso (asIso (P.π 0)))

/-- `Hⁱ(Yₙ₊₁)` vanishes if `Hⁱ⁻¹(Yₙ)` and `Hⁱ(Xₙ₊₁)` do. -/
private theorem isZero_homology_obj_succ_of_isZero (n : ℕ) (i : ℤ)
    (h₁ : IsZero ((DerivedCategory.homologyFunctor C (i - 1)).obj (P.obj n)))
    (h₂ : IsZero ((DerivedCategory.homologyFunctor C i).obj (X (n + 1)))) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj (P.obj (n + 1))) :=
  (DerivedCategory.HomologySequence.exact₁ (P.triangle n) (P.distinguished n) (i - 1) i
    (by omega)).isZero_of_both_isZero h₁ h₂

/-- `Hⁱ(Yₙ⟦n⟧)` vanishes if `Hⁿ⁺ⁱ(Yₙ)` does. -/
private theorem isZero_homology_shift_obj_of_isZero (n : ℕ) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor C ((n : ℤ) + i)).obj (P.obj n))) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj ((P.obj n)⟦(n : ℤ)⟧)) :=
  h.of_iso ((Stacks.HomologyShift.homologyShiftIso C (n : ℤ) i ((n : ℤ) + i) rfl).app (P.obj n))

section Bounds

/-- **Upper bound**: if every term lies in degrees `≤ m`, then `Yₙ` lies in degrees `≤ m + n`. -/
theorem isZero_homology_obj_of_lt_of_isLE (m : ℤ)
    (hX : ∀ (n : ℕ) (i : ℤ), m < i → IsZero ((DerivedCategory.homologyFunctor C i).obj (X n)))
    (n : ℕ) (i : ℤ) (hi : m + n < i) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj (P.obj n)) := by
  induction n generalizing i with
  | zero => exact P.isZero_homology_obj_zero_of_isZero i (hX 0 i (by omega))
  | succ n ih =>
    exact P.isZero_homology_obj_succ_of_isZero n i (ih (i - 1) (by omega)) (hX (n + 1) i (by omega))

/-- **Lower bound**: if every term lies in degrees `≥ a`, so does every `Yₙ`. -/
theorem isZero_homology_obj_of_lt_of_isGE (a : ℤ)
    (hX : ∀ (n : ℕ) (i : ℤ), i < a → IsZero ((DerivedCategory.homologyFunctor C i).obj (X n)))
    (n : ℕ) (i : ℤ) (hi : i < a) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj (P.obj n)) := by
  induction n generalizing i with
  | zero => exact P.isZero_homology_obj_zero_of_isZero i (hX 0 i hi)
  | succ n ih =>
    exact P.isZero_homology_obj_succ_of_isZero n i (ih (i - 1) (by omega)) (hX (n + 1) i hi)

/-- If every term lies in degrees `≤ m`, so does every `Yₙ⟦n⟧`. -/
theorem isLE_shift_obj_of_isLE (m : ℤ) (hX : ∀ n, (X n).IsLE m) (n : ℕ) :
    ((P.obj n)⟦(n : ℤ)⟧).IsLE m := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  refine P.isZero_homology_shift_obj_of_isZero n i ?_
  exact P.isZero_homology_obj_of_lt_of_isLE m
    (fun n i hi => DerivedCategory.isZero_of_isLE _ m i hi) n _ (by omega)

/-- If every term lies in degrees `≥ a`, then `Yₙ⟦n⟧` lies in degrees `≥ a - n`. -/
theorem isGE_shift_obj_of_isGE (a : ℤ) (hX : ∀ n, (X n).IsGE a) (n : ℕ) :
    ((P.obj n)⟦(n : ℤ)⟧).IsGE (a - n) := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  refine P.isZero_homology_shift_obj_of_isZero n i ?_
  exact P.isZero_homology_obj_of_lt_of_isGE a
    (fun n i hi => DerivedCategory.isZero_of_isGE _ a i hi) n _ (by omega)

end Bounds

section Vanishing

variable (hX : ∀ (n : ℕ) (i : ℤ), i ≠ 0 →
  IsZero ((DerivedCategory.homologyFunctor C i).obj (X n)))
include hX

/-- **The cohomology of `Yₙ` vanishes in negative degrees.** -/
theorem isZero_homology_obj_of_lt_zero (n : ℕ) (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj (P.obj n)) :=
  P.isZero_homology_obj_of_lt_of_isGE 0 (fun n i hi => hX n i (by omega)) n i hi

/-- **The cohomology of `Yₙ` vanishes above degree `n`.** -/
theorem isZero_homology_obj_of_lt (n : ℕ) (i : ℤ) (hi : (n : ℤ) < i) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj (P.obj n)) :=
  P.isZero_homology_obj_of_lt_of_isLE 0 (fun n i hi => hX n i (by omega)) n i (by omega)

/-- `H⁰(Yₙ) ⟶ H⁰(Xₙ)` is a monomorphism. -/
theorem mono_homologyMap_π (n : ℕ) :
    Mono ((DerivedCategory.homologyFunctor C 0).map (P.π n)) := by
  cases n with
  | zero => infer_instance
  | succ n =>
    exact (DerivedCategory.HomologySequence.exact₁ (P.triangle n) (P.distinguished n)
      (-1) 0 (by omega)).mono_g
        ((P.isZero_homology_obj_of_lt_zero hX n (-1) (by omega)).eq_of_src _ _)

/-- `0 ⟶ H⁰(Yₙ₊₁) ⟶ H⁰(Xₙ₊₁) ⟶ H⁰(Xₙ)` is exact. -/
theorem exact_homologyMap_π (n : ℕ) :
    (ShortComplex.mk ((DerivedCategory.homologyFunctor C 0).map (P.π (n + 1)))
      ((DerivedCategory.homologyFunctor C 0).map (d n))
      (P.homologyMap_π_comp_eq_zero n)).Exact := by
  have := P.mono_homologyMap_π hX n
  let φ : ShortComplex.mk ((DerivedCategory.homologyFunctor C 0).map (P.π (n + 1)))
      ((DerivedCategory.homologyFunctor C 0).map (P.p n))
      (by rw [← Functor.map_comp,
        show P.π (n + 1) ≫ P.p n = 0 from comp_distTriang_mor_zero₁₂ _ (P.distinguished n),
        Functor.map_zero]) ⟶
      ShortComplex.mk ((DerivedCategory.homologyFunctor C 0).map (P.π (n + 1)))
        ((DerivedCategory.homologyFunctor C 0).map (d n))
        (P.homologyMap_π_comp_eq_zero n) :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := (DerivedCategory.homologyFunctor C 0).map (P.π n)
      comm₁₂ := by simp
      comm₂₃ := by
        dsimp
        rw [Category.id_comp, ← Functor.map_comp, P.p_comp_π] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
    (DerivedCategory.HomologySequence.exact₂ (P.triangle n) (P.distinguished n) 0)

variable (hd : ∀ n, d (n + 1) ≫ d n = 0)
  (hexact : ∀ n, (ShortComplex.mk ((DerivedCategory.homologyFunctor C 0).map (d (n + 1)))
    ((DerivedCategory.homologyFunctor C 0).map (d n))
    (homologyMap_comp_eq_zero hd n)).Exact)
include hexact

/-- For `n ≥ 1` the map `H⁰(Xₙ₊₁) ⟶ H⁰(Yₙ)` is an epimorphism. -/
theorem epi_homologyMap_p (n : ℕ) :
    Epi ((DerivedCategory.homologyFunctor C 0).map (P.p (n + 1))) := by
  have := P.mono_homologyMap_π hX (n + 1)
  exact epi_of_factor _ _ _ (P.exact_homologyMap_π hX n) _ _ (hexact n) _
    (by rw [← Functor.map_comp, P.p_comp_π])

/-- **The cohomology of `Yₙ` vanishes strictly between degrees `0` and `n`.** -/
theorem isZero_homology_obj_of_pos_of_lt (n : ℕ) (i : ℤ) (hi₀ : 0 < i) (hi : i < n) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj (P.obj n)) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rcases eq_or_lt_of_le (show (1 : ℤ) ≤ i by omega) with rfl | hi₁
    · obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have := P.epi_homologyMap_p hX hd hexact n
      have h₃ := DerivedCategory.HomologySequence.exact₃ (P.triangle (n + 1))
        (P.distinguished (n + 1)) 0 1 (by omega)
      exact (DerivedCategory.HomologySequence.exact₁ (P.triangle (n + 1))
        (P.distinguished (n + 1)) 0 1 (by omega)).isZero_X₂ (h₃.epi_f_iff.1 this)
        ((hX (n + 2) 1 (by omega)).eq_of_tgt _ _)
    · exact P.isZero_homology_obj_succ_of_isZero n i (ih (i - 1) (by omega) (by omega))
        (hX (n + 1) i (by omega))

omit hexact in
/-- `Hⁿ(Yₙ) ⟶ Hⁿ⁺¹(Yₙ₊₁)` is an isomorphism for `n ≥ 1`. -/
theorem isIso_homologySequenceδ (n : ℕ) (hn : 1 ≤ n) :
    IsIso (DerivedCategory.HomologySequence.δ (P.triangle n) (n : ℤ) ((n + 1 : ℕ) : ℤ)
      (by omega)) := by
  have : Mono (DerivedCategory.HomologySequence.δ (P.triangle n) (n : ℤ) ((n + 1 : ℕ) : ℤ)
      (by omega)) :=
    (DerivedCategory.HomologySequence.exact₃ (P.triangle n) (P.distinguished n) (n : ℤ)
      ((n + 1 : ℕ) : ℤ) (Nat.cast_succ n).symm).mono_g ((hX (n + 1) n (by omega)).eq_of_src _ _)
  have : Epi (DerivedCategory.HomologySequence.δ (P.triangle n) (n : ℤ) ((n + 1 : ℕ) : ℤ)
      (by omega)) :=
    (DerivedCategory.HomologySequence.exact₁ (P.triangle n) (P.distinguished n) (n : ℤ)
      ((n + 1 : ℕ) : ℤ) (Nat.cast_succ n).symm).epi_f
        ((hX (n + 1) ((n + 1 : ℕ) : ℤ) (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end Vanishing

section Top

variable (hX : ∀ (n : ℕ) (i : ℤ), i ≠ 0 →
  IsZero ((DerivedCategory.homologyFunctor C i).obj (X n)))
  {O : C} (ε : (DerivedCategory.homologyFunctor C 0).obj (X 0) ⟶ O)
  (hε : (DerivedCategory.homologyFunctor C 0).map (d 0) ≫ ε = 0)
  (hεexact : (ShortComplex.mk _ _ hε).Exact) [Epi ε]
include hX hεexact

/-- `H¹(Y₁) ≅ O`: both are cokernels of `H⁰(X₁) ⟶ H⁰(X₀)`. -/
private theorem nonempty_homology_obj_one_iso :
    Nonempty ((DerivedCategory.homologyFunctor C 1).obj (P.obj 1) ≅ O) := by
  have h₃ := DerivedCategory.HomologySequence.exact₃ (P.triangle 0) (P.distinguished 0) 0 1
    (by omega)
  have : Epi (DerivedCategory.HomologySequence.δ (P.triangle 0) 0 1 (by omega)) :=
    (DerivedCategory.HomologySequence.exact₁ (P.triangle 0) (P.distinguished 0) 0 1
      (by omega)).epi_f ((hX 1 1 (by omega)).eq_of_tgt _ _)
  have hcomp : (DerivedCategory.homologyFunctor C 0).map (P.p 0) ≫
      (DerivedCategory.homologyFunctor C 0).map (P.π 0) ≫ ε = 0 := by
    rw [← Category.assoc, ← Functor.map_comp, P.p_comp_π, hε]
  let φ : ShortComplex.mk ((DerivedCategory.homologyFunctor C 0).map (P.p 0))
      ((DerivedCategory.homologyFunctor C 0).map (P.π 0) ≫ ε) hcomp ⟶ ShortComplex.mk _ _ hε :=
    { τ₁ := 𝟙 _, τ₂ := (DerivedCategory.homologyFunctor C 0).map (P.π 0), τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp
        rw [Category.id_comp, ← Functor.map_comp, P.p_comp_π]
      comm₂₃ := by simp }
  have : Epi ((DerivedCategory.homologyFunctor C 0).map (P.π 0) ≫ ε) := epi_comp _ _
  exact ⟨IsColimit.coconePointUniqueUpToIso h₃.gIsCokernel
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hεexact).gIsCokernel⟩

/-- **`Hⁿ(Yₙ) ≅ O` for `n ≥ 1`.** -/
theorem nonempty_homology_obj_iso (n : ℕ) (hn : 1 ≤ n) :
    Nonempty ((DerivedCategory.homologyFunctor C n).obj (P.obj n) ≅ O) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · exact P.nonempty_homology_obj_one_iso hX ε hε hεexact
    · obtain ⟨e⟩ := ih hn'
      have := P.isIso_homologySequenceδ hX n hn'
      exact ⟨(asIso (DerivedCategory.HomologySequence.δ (P.triangle n) (n : ℤ)
        ((n + 1 : ℕ) : ℤ) (Nat.cast_succ n).symm)).symm ≪≫ e⟩

end Top

section Triangle

variable (hX : ∀ (n : ℕ) (i : ℤ), i ≠ 0 →
  IsZero ((DerivedCategory.homologyFunctor C i).obj (X n)))
  (hd : ∀ n, d (n + 1) ≫ d n = 0)
  (hexact : ∀ n, (ShortComplex.mk ((DerivedCategory.homologyFunctor C 0).map (d (n + 1)))
    ((DerivedCategory.homologyFunctor C 0).map (d n))
    (homologyMap_comp_eq_zero hd n)).Exact)
include hX hexact

/-- `Hⁱ(Yₙ⟦n⟧) = Hⁿ⁺ⁱ(Yₙ)`. -/
abbrev homologyShiftObjIso (n : ℕ) (i j : ℤ) (h : (n : ℤ) + i = j) :
    (DerivedCategory.homologyFunctor C i).obj ((P.obj n)⟦(n : ℤ)⟧) ≅
      (DerivedCategory.homologyFunctor C j).obj (P.obj n) :=
  (Stacks.HomologyShift.homologyShiftIso C (n : ℤ) i j h).app (P.obj n)

/-- **The cohomology of `Yₙ⟦n⟧` is concentrated in degrees `-n` and `0`.** -/
theorem isZero_homology_shift_obj (n : ℕ) (i : ℤ) (hi : i ≠ 0) (hi' : i ≠ -(n : ℤ)) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj ((P.obj n)⟦(n : ℤ)⟧)) := by
  refine P.isZero_homology_shift_obj_of_isZero n i ?_
  rcases lt_trichotomy ((n : ℤ) + i) 0 with h | h | h
  · exact P.isZero_homology_obj_of_lt_zero hX n _ h
  · omega
  · rcases lt_or_gt_of_ne (show (n : ℤ) + i ≠ n by omega) with h' | h'
    · exact P.isZero_homology_obj_of_pos_of_lt hX hd hexact n _ h h'
    · exact P.isZero_homology_obj_of_lt hX n _ h'

/-- `Yₙ⟦n⟧` lies in degrees `≤ 0`. -/
theorem isLE_shift_obj (n : ℕ) : ((P.obj n)⟦(n : ℤ)⟧).IsLE 0 := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact P.isZero_homology_shift_obj hX hd hexact n i (by omega) (by omega)

/-- `Yₙ⟦n⟧` lies in degrees `≥ -n`. -/
theorem isGE_shift_obj (n : ℕ) : ((P.obj n)⟦(n : ℤ)⟧).IsGE (-(n : ℤ)) := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact P.isZero_homology_shift_obj hX hd hexact n i (by omega) (by omega)

variable {O : C} (ε : (DerivedCategory.homologyFunctor C 0).obj (X 0) ⟶ O)
  (hε : (DerivedCategory.homologyFunctor C 0).map (d 0) ≫ ε = 0)
  (hεexact : (ShortComplex.mk _ _ hε).Exact) [Epi ε]
include hεexact

/-- **For `n ≥ 1`, `Yₙ⟦n⟧` is an extension of `O[0]` by an object concentrated in degree `-n`**:
there is a distinguished triangle `W ⟶ Yₙ⟦n⟧ ⟶ O[0] ⟶ W⟦1⟧` with `W ∈ D^{[-n, -n]}`. It is the
truncation triangle `τ^{≤ -n} ⟶ 𝟭 ⟶ τ^{≥ -n+1}`, whose third vertex has cohomology only in
degree `0`, where it is `H⁰(Yₙ⟦n⟧) = Hⁿ(Yₙ) ≅ O`. -/
theorem exists_distTriang_shift_obj (n : ℕ) (hn : 1 ≤ n) :
    ∃ T : Triangle (DerivedCategory C), T ∈ distTriang _ ∧
      Nonempty (T.obj₂ ≅ (P.obj n)⟦(n : ℤ)⟧) ∧ T.obj₁.IsLE (-(n : ℤ)) ∧
        T.obj₁.IsGE (-(n : ℤ)) ∧
        Nonempty (T.obj₃ ≅ (DerivedCategory.singleFunctor C 0).obj O) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let Z := (P.obj n)⟦(n : ℤ)⟧
  have hZLE := P.isLE_shift_obj hX hd hexact n
  have hZGE := P.isGE_shift_obj hX hd hexact n
  let T := (t.triangleLEGE (-(n : ℤ)) (-(n : ℤ) + 1) rfl).obj Z
  have hT : T ∈ distTriang _ := t.triangleLEGE_distinguished _ _ rfl Z
  have h₃GE : T.obj₃.IsGE (-(n : ℤ) + 1) :=
    inferInstanceAs (t.IsGE ((t.truncGE (-(n : ℤ) + 1)).obj Z) (-(n : ℤ) + 1))
  have h₁LE : T.obj₁.IsLE (-(n : ℤ)) :=
    inferInstanceAs (t.IsLE ((t.truncLE (-(n : ℤ))).obj Z) (-(n : ℤ)))
  have hiso : ∀ j : ℤ, -(n : ℤ) < j →
      IsIso ((DerivedCategory.homologyFunctor C j).map T.mor₂) := by
    intro j hj
    have : Mono ((DerivedCategory.homologyFunctor C j).map T.mor₂) :=
      (DerivedCategory.HomologySequence.exact₂ T hT j).mono_g
        ((DerivedCategory.isZero_of_isLE _ (-(n : ℤ)) j hj).eq_of_src _ _)
    have : Epi ((DerivedCategory.homologyFunctor C j).map T.mor₂) :=
      (DerivedCategory.HomologySequence.exact₃ T hT j (j + 1) rfl).epi_f
        ((DerivedCategory.isZero_of_isLE _ (-(n : ℤ)) (j + 1) (by omega)).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _
  have h₃GE0 : T.obj₃.IsGE 0 := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    by_cases hin : -(n : ℤ) < i
    · have := hiso i hin
      exact (P.isZero_homology_shift_obj hX hd hexact n i (by omega) (by omega)).of_iso
        (asIso ((DerivedCategory.homologyFunctor C i).map T.mor₂)).symm
    · exact DerivedCategory.isZero_of_isGE _ (-(n : ℤ) + 1) i (by omega)
  have h₃LE0 : T.obj₃.IsLE 0 := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    have := hiso i (by omega)
    exact (DerivedCategory.isZero_of_isLE Z 0 i hi).of_iso
      (asIso ((DerivedCategory.homologyFunctor C i).map T.mor₂)).symm
  obtain ⟨Y, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₃ 0
  obtain ⟨eO⟩ := P.nonempty_homology_obj_iso hX ε hε hεexact n hn
  have := hiso 0 (by omega)
  let eH : Y ≅ O :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app Y).symm ≪≫
      (DerivedCategory.homologyFunctor C 0).mapIso eY.symm ≪≫
      (asIso ((DerivedCategory.homologyFunctor C 0).map T.mor₂)).symm ≪≫
      P.homologyShiftObjIso n 0 n (by simp) ≪≫ eO
  refine ⟨T, hT, ⟨Iso.refl _⟩, h₁LE, ?_, ⟨eY ≪≫ (DerivedCategory.singleFunctor C 0).mapIso eH⟩⟩
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact (DerivedCategory.HomologySequence.exact₁ T hT (i - 1) i (by omega)).isZero_of_both_isZero
      (DerivedCategory.isZero_of_isGE _ 0 (i - 1) (by omega))
      (DerivedCategory.isZero_of_isGE Z (-(n : ℤ)) i hi)

end Triangle

end CategoryTheory.Triangulated.SequentialPostnikovSystem
