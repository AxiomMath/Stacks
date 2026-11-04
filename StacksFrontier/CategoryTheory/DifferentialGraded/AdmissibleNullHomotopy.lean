module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.Triangulated

/-!
# Consecutive maps through an admissible short exact sequence

Let `x → y → z` be an admissible short exact sequence in a differential graded category and let
two closed degree-zero morphisms pass through its middle object `y`. If the first becomes
null-homotopic after projection to `z` and the second is null-homotopic on `x`, then their
composite is null-homotopic.

## Main results

* `DGCategory.comp_homotopic_zero_of_gradedSplitShortExact`: the null-homotopy of the composite.

## Implementation notes

An admissible short exact sequence is represented by its graded splitting,
`DGCategory.GradedSplitShortExact`. Only the right square of the first diagram and the left square
of the second enter the conclusion, and the statement holds for arbitrary objects of a
differential graded category.

## References

* [Stacks Project, Tag 09QP](https://stacks.math.columbia.edu/tag/09QP)
-/

@[expose] public section

namespace DGCategory

universe u v w

variable {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}

private lemma d'_neg {x y : A.Obj} (f : A.Hom x y (-1)) :
    A.d' (show (-1 : ℤ) + 1 = 0 by omega) (-f) =
      -A.d' (show (-1 : ℤ) + 1 = 0 by omega) f := by
  show A.d (-f) = -A.d f
  rw [show -f = (-1 : R) • f by rw [neg_one_smul], A.d_smul, neg_one_smul]

/-- Adding the boundary of `-q` to a cocycle gives a homotopic cocycle. -/
private lemma exists_homotopic_add_d'_neg {x y : A.Obj} (b : A.Cocycle x y) (q : A.Hom x y (-1)) :
    ∃ b₀ : A.Cocycle x y, A.Homotopic b b₀ ∧
      b₀.1 = b.1 + A.d' (show (-1 : ℤ) + 1 = 0 by omega) (-q) := by
  refine ⟨⟨b.1 + A.d' (show (-1 : ℤ) + 1 = 0 by omega) (-q), ?_⟩, ⟨q, ?_⟩, rfl⟩
  · rw [A.d_add, b.2]
    simpa [DGCategory.d'] using A.d_d (-q)
  · show b.1 - (b.1 + A.d' (show (-1 : ℤ) + 1 = 0 by omega) (-q)) =
      A.d' (show (-1 : ℤ) + 1 = 0 by omega) q
    rw [d'_neg]
    abel

/-- A morphism whose composite with a split epimorphism is null-homotopic is homotopic to one
whose composite with it vanishes. -/
private lemma exists_homotopic_comp_right_zero {x y z : A.Obj}
    (f : A.Cocycle y z) (s : A.Hom z y 0)
    (hfs : A.comp (show (0 : ℤ) + 0 = 0 by omega) f.1 s = A.id z)
    (b : A.Cocycle x y) (hb : A.Homotopic (A.compCocycle f b) ⟨0, A.d_zero⟩) :
    ∃ b₀ : A.Cocycle x y, A.Homotopic b b₀ ∧
      A.comp (show (0 : ℤ) + 0 = 0 by omega) f.1 b₀.1 = 0 := by
  obtain ⟨k, hk⟩ := hb
  have hkb : A.comp (show (0 : ℤ) + 0 = 0 by omega) f.1 b.1 =
      A.d' (show (-1 : ℤ) + 1 = 0 by omega) k := by
    simpa only [DGCategory.Homotopic, DGCategory.compCocycle, Subtype.coe_mk, sub_zero] using hk
  let q := A.comp (show (0 : ℤ) + (-1) = -1 by omega) s k
  have hq : A.comp (show (0 : ℤ) + (-1) = -1 by omega) f.1 q = k := by
    dsimp [q]
    rw [A.assoc (l := 0) (m := 0) (n := -1) (p := -1) (q := 0) (r := -1)
      (by omega) (by omega) (by omega) (by omega), hfs, A.id_comp]
  obtain ⟨b₀, hb₀, hv⟩ := exists_homotopic_add_d'_neg b q
  refine ⟨b₀, hb₀, ?_⟩
  · rw [hv]
    have hqneg : A.comp (show (0 : ℤ) + (-1) = -1 by omega) f.1 (-q) = -k := by
      rw [show -q = (-1 : R) • q by rw [neg_one_smul], A.comp_smul_right, neg_one_smul, hq]
    rw [A.comp_add_right, A.comp_dboundary_right f.1 f.2 (-q), hqneg, d'_neg, hkb]
    abel

/-- A morphism whose composite with a split monomorphism is null-homotopic is homotopic to one
whose composite with it vanishes. -/
private lemma exists_homotopic_comp_left_zero {x y z : A.Obj}
    (a : A.Cocycle x y) (π : A.Hom y x 0)
    (hπa : A.comp (show (0 : ℤ) + 0 = 0 by omega) π a.1 = A.id x)
    (g : A.Cocycle y z) (hg : A.Homotopic (A.compCocycle g a) ⟨0, A.d_zero⟩) :
    ∃ g₀ : A.Cocycle y z, A.Homotopic g g₀ ∧
      A.comp (show (0 : ℤ) + 0 = 0 by omega) g₀.1 a.1 = 0 := by
  obtain ⟨k, hk⟩ := hg
  have hkg : A.comp (show (0 : ℤ) + 0 = 0 by omega) g.1 a.1 =
      A.d' (show (-1 : ℤ) + 1 = 0 by omega) k := by
    simpa only [DGCategory.Homotopic, DGCategory.compCocycle, Subtype.coe_mk, sub_zero] using hk
  let q := A.comp (show (-1 : ℤ) + 0 = -1 by omega) k π
  have hq : A.comp (show (-1 : ℤ) + 0 = -1 by omega) q a.1 = k := by
    dsimp [q]
    rw [← A.assoc (l := -1) (m := 0) (n := 0) (p := 0) (q := -1) (r := -1)
      (by omega) (by omega) (by omega) (by omega), hπa, A.comp_id]
  obtain ⟨g₀, hg₀, hv⟩ := exists_homotopic_add_d'_neg g q
  refine ⟨g₀, hg₀, ?_⟩
  · rw [hv]
    have hqneg : A.comp (show (-1 : ℤ) + 0 = -1 by omega) (-q) a.1 = -k := by
      rw [show -q = (-1 : R) • q by rw [neg_one_smul], A.comp_smul_left, neg_one_smul, hq]
    rw [A.comp_add_left, A.comp_dboundary_left a.1 a.2 (-q), hqneg, d'_neg, hkg]
    abel

/-- Two morphisms whose composites with opposite sides of an admissible short exact sequence
vanish up to homotopy have null-homotopic composite. -/
@[stacks 09QP]
theorem comp_homotopic_zero_of_gradedSplitShortExact {x y z y₁ y₃ : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z)
    (b : A.Cocycle y₁ y) (b' : A.Cocycle y y₃)
    (hb : A.Homotopic (A.compCocycle E.b b) ⟨0, A.d_zero⟩)
    (hb' : A.Homotopic (A.compCocycle b' E.a) ⟨0, A.d_zero⟩) :
    A.Homotopic (A.compCocycle b' b) ⟨0, A.d_zero⟩ := by
  obtain ⟨b₀, hb₀, hbb₀⟩ := exists_homotopic_comp_right_zero E.b E.s E.b_s b hb
  obtain ⟨b'₀, hb'₀, hb'₀a⟩ := exists_homotopic_comp_left_zero E.a E.π E.π_a b' hb'
  have hzero : A.compCocycle b'₀ b₀ = ⟨0, A.d_zero⟩ := by
    apply Subtype.ext
    show A.comp (show (0 : ℤ) + 0 = 0 by omega) b'₀.1 b₀.1 = 0
    have hfirst : A.comp (show (0 : ℤ) + 0 = 0 by omega) b'₀.1
        (A.comp (show (0 : ℤ) + 0 = 0 by omega)
          (A.comp (show (0 : ℤ) + 0 = 0 by omega) E.a.1 E.π) b₀.1) = 0 := by
      rw [← A.assoc (l := 0) (m := 0) (n := 0) (p := 0) (q := 0) (r := 0)
        (by omega) (by omega) (by omega) (by omega),
        A.assoc (l := 0) (m := 0) (n := 0) (p := 0) (q := 0) (r := 0)
        (by omega) (by omega) (by omega) (by omega), hb'₀a]
      simp
    have hsecond : A.comp (show (0 : ℤ) + 0 = 0 by omega) b'₀.1
        (A.comp (show (0 : ℤ) + 0 = 0 by omega)
          (A.comp (show (0 : ℤ) + 0 = 0 by omega) E.s E.b.1) b₀.1) = 0 := by
      rw [← A.assoc (l := 0) (m := 0) (n := 0) (p := 0) (q := 0) (r := 0)
        (by omega) (by omega) (by omega) (by omega), hbb₀]
      simp
    calc
      A.comp (show (0 : ℤ) + 0 = 0 by omega) b'₀.1 b₀.1 =
          A.comp (show (0 : ℤ) + 0 = 0 by omega) b'₀.1
            (A.comp (show (0 : ℤ) + 0 = 0 by omega)
              (A.comp (show (0 : ℤ) + 0 = 0 by omega) E.a.1 E.π +
                A.comp (show (0 : ℤ) + 0 = 0 by omega) E.s E.b.1) b₀.1) := by
          rw [E.a_π_add_s_b, A.id_comp]
      _ = 0 := by rw [A.comp_add_left, A.comp_add_right, hfirst, hsecond, add_zero]
  simpa only [hzero] using A.homotopic_trans
    (A.compCocycle_homotopic_left b hb'₀) (A.compCocycle_homotopic_right b'₀ hb₀)

end DGCategory
