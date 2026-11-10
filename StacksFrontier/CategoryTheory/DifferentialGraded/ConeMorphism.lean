module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.ConeSituationIso

/-!
# Morphisms between cone triangles

In a differential graded category with cones, a square of closed degree-zero morphisms which
commutes in the homotopy category extends to a morphism between the associated cone triangles,
and the map between the two cones is itself represented by a closed degree-zero morphism. The
cone of an identity morphism is contractible: its identity is homotopic to zero.

## Main results

* `DGCategory.exists_coneTriangleMorphism`: the cone map and the two remaining commutative
  squares of the morphism of triangles.
* `DGCategory.id_cone_homotopic_zero`: the identity of the chosen cone of an identity cocycle is
  homotopic to zero.

## Implementation notes

The homotopy-commutative square is an equality in the homotopy category, while the conclusion
provides an actual cocycle between the chosen cones rather than merely its homotopy class.

## References

* [Stacks Project, Tag 09P7](https://stacks.math.columbia.edu/tag/09P7)
* [Stacks Project, Tag 09QK](https://stacks.math.columbia.edu/tag/09QK)
-/

@[expose] public section

namespace DGCategory

open CategoryTheory

universe u v w

variable {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}

theorem comp_neg_left {x y z : A.Obj} {m n k : ℤ}
    (e : m + n = k) (g : A.Hom y z m) (f : A.Hom x y n) :
    A.comp e (-g) f = -A.comp e g f := by
  rw [show -g = (-1 : R) • g by rw [neg_one_smul], A.comp_smul_left, neg_one_smul]

/-- Composition in a differential graded category is compatible with negation in its right
argument. -/
theorem comp_neg_right {x y z : A.Obj} {m n k : ℤ}
    (e : m + n = k) (g : A.Hom y z m) (f : A.Hom x y n) :
    A.comp e g (-f) = -A.comp e g f := by
  rw [show -f = (-1 : R) • f by rw [neg_one_smul], A.comp_smul_right, neg_one_smul]

/-- The obstruction to commutativity of the shifted square is a coboundary. -/
private theorem shifted_obstruction_is_boundary (S : ConeSituationIso A)
    {x₁ y₁ x₂ y₂ : A.Obj}
    (f₁ : A.Cocycle x₁ y₁) (f₂ : A.Cocycle x₂ y₂)
    (a : A.Cocycle x₁ x₂) (b : A.Cocycle y₁ y₂)
    (hcomm : A.compK (Quotient.mk (A.homotopySetoid y₁ y₂) b)
        (Quotient.mk (A.homotopySetoid x₁ y₁) f₁) =
      A.compK (Quotient.mk (A.homotopySetoid x₂ y₂) f₂)
        (Quotient.mk (A.homotopySetoid x₁ x₂) a)) :
    let X₁ := (S.shift.shiftFunctor 1).obj x₁
    let X₂ := (S.shift.shiftFunctor 1).obj x₂
    let a' : A.Cocycle X₁ X₂ := (S.shift.shiftFunctor 1).mapCocycle a
    let g₁ : A.Hom X₁ y₁ (0 + 1) :=
      (S.shift.toShift 1 X₁ y₁ 0).symm ((S.shift.shiftFunctor 1).mapCocycle f₁).1
    let g₂ : A.Hom X₂ y₂ (0 + 1) :=
      (S.shift.toShift 1 X₂ y₂ 0).symm ((S.shift.shiftFunctor 1).mapCocycle f₂).1
    ∃ H : A.Hom X₁ y₂ (-1 + 1),
      A.d' (by omega : (-1 + 1 : ℤ) + 1 = 1) H =
        A.comp (by omega : (0 : ℤ) + (0 + 1) = 1) b.1 g₁ -
          A.comp (by omega : (0 + 1 : ℤ) + 0 = 1) g₂ a'.1 := by
  dsimp
  let X₁ : A.Obj := (S.shift.shiftFunctor 1).obj x₁
  let X₂ : A.Obj := (S.shift.shiftFunctor 1).obj x₂
  let Y₁ : A.Obj := (S.shift.shiftFunctor 1).obj y₁
  let Y₂ : A.Obj := (S.shift.shiftFunctor 1).obj y₂
  let a' : A.Cocycle X₁ X₂ := (S.shift.shiftFunctor 1).mapCocycle a
  let b' : A.Cocycle Y₁ Y₂ := (S.shift.shiftFunctor 1).mapCocycle b
  let f₁' : A.Cocycle X₁ Y₁ := (S.shift.shiftFunctor 1).mapCocycle f₁
  let f₂' : A.Cocycle X₂ Y₂ := (S.shift.shiftFunctor 1).mapCocycle f₂
  let g₁ : A.Hom X₁ y₁ (0 + 1) := (S.shift.toShift 1 X₁ y₁ 0).symm f₁'.1
  let g₂ : A.Hom X₂ y₂ (0 + 1) := (S.shift.toShift 1 X₂ y₂ 0).symm f₂'.1
  obtain ⟨h, hh⟩ : A.Homotopic (A.compCocycle b f₁) (A.compCocycle f₂ a) :=
    Quotient.exact (by simpa [DGCategory.compK] using hcomm)
  let F := S.shift.shiftFunctor 1
  have hhom : A.Homotopic (A.compCocycle b' f₁') (A.compCocycle f₂' a') := by
    refine ⟨F.map h, ?_⟩
    have hmap_sub {u v : A.Hom x₁ y₂ 0} : F.map (u - v) = F.map u - F.map v := by
      rw [sub_eq_add_neg, ← neg_one_smul R v, F.map_add, F.map_smul, neg_one_smul,
        ← sub_eq_add_neg]
    calc
      (A.compCocycle b' f₁').1 - (A.compCocycle f₂' a').1 =
          F.map (A.comp (by omega : (0 : ℤ) + 0 = 0) b.1 f₁.1) -
            F.map (A.comp (by omega : (0 : ℤ) + 0 = 0) f₂.1 a.1) := by
        change A.comp (by omega : (0 : ℤ) + 0 = 0) (F.map b.1) (F.map f₁.1) -
          A.comp (by omega : (0 : ℤ) + 0 = 0) (F.map f₂.1) (F.map a.1) = _
        rw [F.map_comp, F.map_comp]
      _ = F.map ((A.compCocycle b f₁).1 - (A.compCocycle f₂ a).1) := by
        rw [hmap_sub]
        rfl
      _ = F.map (A.d' (by omega : (-1 : ℤ) + 1 = 0) h) := by rw [hh]
      _ = A.d' (by omega : (-1 : ℤ) + 1 = 0) (F.map h) := by
        simp only [DGCategory.d']
        rw [F.map_d]
  obtain ⟨H₀, hH₀⟩ := hhom
  let H : A.Hom X₁ y₂ (-1 + 1) := -((S.shift.toShift 1 X₁ y₂ (-1)).symm H₀)
  refine ⟨H, ?_⟩
  apply (S.shift.toShift 1 X₁ y₂ 0).injective
  have hinv : S.shift.toShift 1 X₁ y₂ (-1) H = -H₀ := by simp [H]
  have hdiff :
      S.shift.toShift 1 X₁ y₂ 0 (A.d' (by omega : (-1 + 1 : ℤ) + 1 = 1) H) = A.d H₀ := by
    have ht := S.shift.toShift_d 1 X₁ y₂ (-1) H
    rw [hinv] at ht
    have ht' : S.shift.toShift 1 X₁ y₂ 0
        (A.d' (by omega : (-1 + 1 : ℤ) + 1 = 1) H) = -A.d (-H₀) := by
      simpa [DGCategory.d', pow_one, neg_smul, one_smul] using ht
    rwa [← neg_one_smul R H₀, A.d_smul, neg_one_smul, neg_neg] at ht'
  have hq :
      S.shift.toShift 1 X₁ y₂ 0
        (A.comp (by omega : (0 : ℤ) + (0 + 1) = 1) b.1 g₁ -
          A.comp (by omega : (0 + 1 : ℤ) + 0 = 1) g₂ a'.1) = A.d H₀ := by
    rw [map_sub]
    have h₂ := S.shift.toShift_comp_right (n := 1) (m := 0) (l := 0)
      (show A.Hom X₂ y₂ (0 + 1) from g₂) a'.1
    have h₁ := S.shift.toShift_comp_left (n := 1) (m := 0) (l := 0)
      b.1 (show A.Hom X₁ y₁ (0 + 1) from g₁)
    dsimp [g₁, g₂, a', b', f₁', f₂'] at h₂ h₁
    simp only [LinearEquiv.apply_symm_apply, pow_zero, one_smul] at h₂ h₁
    rw [h₂, h₁]
    have hrep : A.comp (by omega : (0 : ℤ) + 0 = 0) b'.1 f₁'.1 -
        A.comp (by omega : (0 : ℤ) + 0 = 0) f₂'.1 a'.1 = A.d H₀ := by
      simpa [DGCategory.compCocycle, DGCategory.d'] using hH₀
    dsimp [a', b', f₁', f₂', DGCategory.DGFunctor.mapCocycle] at hrep ⊢
    rw [hrep]
  rw [hdiff, hq]

/-- For a shift additive up to isomorphism, a homotopy-commutative square of complexes induces a
morphism of their cone triangles, whose cone component has a representative in the category of
complexes. -/
theorem ConeSituationIso.exists_coneTriangleMorphism (S : ConeSituationIso A)
    {x₁ y₁ x₂ y₂ : A.Obj}
    (f₁ : A.Cocycle x₁ y₁) (f₂ : A.Cocycle x₂ y₂)
    (a : A.Cocycle x₁ x₂) (b : A.Cocycle y₁ y₂)
    (hcomm : A.compK (Quotient.mk (A.homotopySetoid y₁ y₂) b)
        (Quotient.mk (A.homotopySetoid x₁ y₁) f₁) =
      A.compK (Quotient.mk (A.homotopySetoid x₂ y₂) f₂)
        (Quotient.mk (A.homotopySetoid x₁ x₂) a)) :
    ∃ c : A.Cocycle (S.cone f₁) (S.cone f₂),
      (A.compK
          (Quotient.mk (A.homotopySetoid (S.cone f₁) (S.cone f₂)) c)
          (Quotient.mk (A.homotopySetoid y₁ (S.cone f₁)) (S.coneSequence f₁).a) =
        A.compK
          (Quotient.mk (A.homotopySetoid y₂ (S.cone f₂)) (S.coneSequence f₂).a)
          (Quotient.mk (A.homotopySetoid y₁ y₂) b)) ∧
      (A.compK
          (Quotient.mk (A.homotopySetoid (S.cone f₂)
            ((S.shift.shiftFunctor 1).obj x₂)) (S.coneSequence f₂).b)
          (Quotient.mk (A.homotopySetoid (S.cone f₁) (S.cone f₂)) c) =
        A.compK
          (Quotient.mk (A.homotopySetoid ((S.shift.shiftFunctor 1).obj x₁)
            ((S.shift.shiftFunctor 1).obj x₂))
            ((S.shift.shiftFunctor 1).mapCocycle a))
          (Quotient.mk (A.homotopySetoid (S.cone f₁)
            ((S.shift.shiftFunctor 1).obj x₁)) (S.coneSequence f₁).b)) := by
  let E₁ := S.coneSequence f₁
  let E₂ := S.coneSequence f₂
  let a' := (S.shift.shiftFunctor 1).mapCocycle a
  let g₁ := GradedSplitShortExact.connectingHom E₁
  let g₂ := GradedSplitShortExact.connectingHom E₂
  obtain ⟨H, hH⟩ := shifted_obstruction_is_boundary S f₁ f₂ a b hcomm
  let c₀ : A.Hom (S.cone f₁) (S.cone f₂) 0 :=
    A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.a.1
        (A.comp (by omega : (0 : ℤ) + 0 = 0) b.1 E₁.π) +
      A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.s
        (A.comp (by omega : (0 : ℤ) + 0 = 0) a'.1 E₁.b.1) +
      A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.a.1
        (A.comp (by omega : (0 : ℤ) + (-1 + 1) = 0) H E₁.b.1)
  have hg : ∀ {x y : A.Obj} (f : A.Cocycle x y),
      GradedSplitShortExact.connectingHom (S.coneSequence f) =
        (S.shift.toShift 1 ((S.shift.shiftFunctor 1).obj x) y 0).symm
          ((S.shift.shiftFunctor 1).mapCocycle f).1 := by
    intro x y f
    apply (S.shift.toShift 1 ((S.shift.shiftFunctor 1).obj x) y 0).injective
    simpa [ShiftAxiomBIso.connectingCocycle] using
      congrArg Subtype.val (S.cone_connecting f)
  have hg₁ : g₁ = _ := hg f₁
  have hg₂ : g₂ = _ := hg f₂
  rw [← hg₁, ← hg₂] at hH
  have hpi : A.d E₁.π = -A.comp (by omega : (1 : ℤ) + 0 = 1) g₁ E₁.b.1 := by
    have heq := GradedSplitShortExact.connectingHom_comp E₁
    rw [← neg_one_smul R E₁.π, A.d_smul, neg_one_smul] at heq
    exact (neg_eq_iff_eq_neg.mp heq.symm)
  simp only [DGCategory.d'] at hH
  have hc : A.d c₀ = 0 := by
    rw [A.d_add, A.d_add]
    have h₁ : A.d (A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.a.1
        (A.comp (by omega : (0 : ℤ) + 0 = 0) b.1 E₁.π)) =
        A.comp (by omega : (0 : ℤ) + 1 = 1) E₂.a.1
          (A.comp (by omega : (0 : ℤ) + 1 = 1) b.1 (A.d E₁.π)) := by
      simp [A.leibniz, E₂.a.2, b.2, pow_zero, one_smul]
    have h₂ : A.d (A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.s
        (A.comp (by omega : (0 : ℤ) + 0 = 0) a'.1 E₁.b.1)) =
        A.comp (by omega : (1 : ℤ) + 0 = 1) (A.d E₂.s)
          (A.comp (by omega : (0 : ℤ) + 0 = 0) a'.1 E₁.b.1) := by
      simp [A.leibniz, a'.2, E₁.b.2, pow_zero, A.comp_zero_right, A.comp_zero_left]
    have h₃ : A.d (A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.a.1
        (A.comp (by omega : (0 : ℤ) + 0 = 0) H E₁.b.1)) =
        A.comp (by omega : (0 : ℤ) + 1 = 1) E₂.a.1
          (A.comp (by omega : ((-1 + 1 : ℤ) + 1) + 0 = 1) (A.d H) E₁.b.1) := by
      simp [A.leibniz, E₂.a.2, E₁.b.2, pow_zero, A.comp_zero_right, A.comp_zero_left]
    rw [h₁, h₂, h₃, hpi, ← GradedSplitShortExact.comp_connectingHom E₂, hH]
    simp only [sub_eq_add_neg, comp_neg_left, comp_neg_right, A.comp_add_left, A.comp_add_right]
    have hBGb := A.assoc (by omega : (1 : ℤ) + 0 = 1) (by omega : (0 : ℤ) + 1 = 1)
      (by omega : (0 : ℤ) + 1 = 1) (by omega : (1 : ℤ) + 0 = 1) b.1 g₁ E₁.b.1
    have hABGb := A.assoc (by omega : (0 : ℤ) + 1 = 1) (by omega : (0 : ℤ) + 1 = 1)
      (by omega : (0 : ℤ) + 0 = 0) (by omega : (0 : ℤ) + 1 = 1) E₂.a.1 b.1 g₁
    have hABGbb := A.assoc (by omega : (1 : ℤ) + 0 = 1) (by omega : (0 : ℤ) + 1 = 1)
      (by omega : (0 : ℤ) + 1 = 1) (by omega : (1 : ℤ) + 0 = 1) E₂.a.1
      (A.comp (by omega : (0 : ℤ) + 1 = 1) b.1 g₁) E₁.b.1
    have hA2G2A'b := A.assoc (by omega : (0 : ℤ) + 0 = 0) (by omega : (1 : ℤ) + 0 = 1)
      (by omega : (1 : ℤ) + 0 = 1) (by omega : (1 : ℤ) + 0 = 1)
      (A.comp (by omega : (0 : ℤ) + 1 = 1) E₂.a.1 g₂) a'.1 E₁.b.1
    have hG2A'b := A.assoc (by omega : (1 : ℤ) + 0 = 1) (by omega : (0 : ℤ) + 1 = 1)
      (by omega : (0 : ℤ) + 1 = 1) (by omega : (1 : ℤ) + 0 = 1) E₂.a.1
      (A.comp (by omega : (1 : ℤ) + 0 = 1) g₂ a'.1) E₁.b.1
    have hAG2A' := A.assoc (by omega : (1 : ℤ) + 0 = 1) (by omega : (0 : ℤ) + 1 = 1)
      (by omega : (0 : ℤ) + 1 = 1) (by omega : (1 : ℤ) + 0 = 1) E₂.a.1 g₂ a'.1
    rw [hBGb, hABGbb, hABGb, hA2G2A'b, hG2A'b, hAG2A']
    abel_nf
  let c : A.Cocycle (S.cone f₁) (S.cone f₂) := ⟨c₀, hc⟩
  refine ⟨c, ?_, ?_⟩
  · change A.compK (Quotient.mk (A.homotopySetoid (S.cone f₁) (S.cone f₂)) c)
      (Quotient.mk (A.homotopySetoid y₁ (S.cone f₁)) E₁.a) = _
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    change A.comp (by omega : (0 : ℤ) + 0 = 0) c₀ E₁.a.1 =
      A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.a.1 b.1
    simp [c₀, A.comp_add_left, ← A.assoc, E₁.π_a,
      GradedSplitShortExact.comp_zero E₁, A.comp_id]
  · change A.compK (Quotient.mk (A.homotopySetoid (S.cone f₂) _) E₂.b)
      (Quotient.mk (A.homotopySetoid (S.cone f₁) (S.cone f₂)) c) = _
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    change A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.b.1 c₀ =
      A.comp (by omega : (0 : ℤ) + 0 = 0) a'.1 E₁.b.1
    simp [c₀, A.comp_add_right, A.assoc, E₂.b_s,
      GradedSplitShortExact.comp_zero E₂, A.id_comp]

/-- A homotopy-commutative square of complexes induces a morphism of their cone triangles, whose
cone component has a representative in the category of complexes. -/
@[stacks 09P7]
theorem exists_coneTriangleMorphism (S : ConeSituation A)
    {x₁ y₁ x₂ y₂ : A.Obj}
    (f₁ : A.Cocycle x₁ y₁) (f₂ : A.Cocycle x₂ y₂)
    (a : A.Cocycle x₁ x₂) (b : A.Cocycle y₁ y₂)
    (hcomm : A.compK (Quotient.mk (A.homotopySetoid y₁ y₂) b)
        (Quotient.mk (A.homotopySetoid x₁ y₁) f₁) =
      A.compK (Quotient.mk (A.homotopySetoid x₂ y₂) f₂)
        (Quotient.mk (A.homotopySetoid x₁ x₂) a)) :
    ∃ c : A.Cocycle (S.cone f₁) (S.cone f₂),
      (A.compK
          (Quotient.mk (A.homotopySetoid (S.cone f₁) (S.cone f₂)) c)
          (Quotient.mk (A.homotopySetoid y₁ (S.cone f₁)) (S.coneSequence f₁).a) =
        A.compK
          (Quotient.mk (A.homotopySetoid y₂ (S.cone f₂)) (S.coneSequence f₂).a)
          (Quotient.mk (A.homotopySetoid y₁ y₂) b)) ∧
      (A.compK
          (Quotient.mk (A.homotopySetoid (S.cone f₂)
            ((S.shift.shiftFunctor 1).obj x₂)) (S.coneSequence f₂).b)
          (Quotient.mk (A.homotopySetoid (S.cone f₁) (S.cone f₂)) c) =
        A.compK
          (Quotient.mk (A.homotopySetoid ((S.shift.shiftFunctor 1).obj x₁)
            ((S.shift.shiftFunctor 1).obj x₂))
            ((S.shift.shiftFunctor 1).mapCocycle a))
          (Quotient.mk (A.homotopySetoid (S.cone f₁)
            ((S.shift.shiftFunctor 1).obj x₁)) (S.coneSequence f₁).b)) :=
  ConeSituationIso.exists_coneTriangleMorphism S.toConeSituationIso f₁ f₂ a b hcomm

/-- For a shift additive up to isomorphism, the identity of the cone of an identity morphism is
homotopic to zero. -/
theorem ConeSituationIso.id_cone_homotopic_zero (S : ConeSituationIso A) (x : A.Obj) :
    let c := S.cone (⟨A.id x, A.d_id x⟩ : A.Cocycle x x)
    A.Homotopic (⟨A.id c, A.d_id c⟩ : A.Cocycle c c) (⟨0, A.d_zero⟩ : A.Cocycle c c) := by
  classical
  let f : A.Cocycle x x := ⟨A.id x, A.d_id x⟩
  let c := S.cone f
  let z := (S.shift.shiftFunctor 1).obj x
  let E := S.coneSequence f
  let p : A.Hom c z (-1) := (S.shift.toShift 1 c x (-1)) E.π
  let D : A.Hom z c 1 := A.d E.s
  let Q : A.Hom c z 0 := A.d p
  have hc : S.shift.toShift 1 z x 0 (GradedSplitShortExact.connectingHom E) = A.id z := by
    rw [← (S.shift.shiftFunctor 1).map_id x]
    exact congrArg Subtype.val (S.cone_connecting f)
  have htoD : S.shift.toShift 1 c x 0 (A.d E.π) = -Q := by
    have h := S.shift.toShift_d 1 c x (-1)
      (show A.Hom c x ((-1 : ℤ) + 1) from by simpa using E.π)
    simpa [p, Q, DGCategory.d'] using h
  have hQs : A.comp (show (0 : ℤ) + 0 = 0 by omega) Q E.s = A.id z := by
    have hcomp' : S.shift.toShift 1 z x 0
        (A.comp (show (1 : ℤ) + 0 = 1 by omega) (A.d E.π) E.s) =
          A.comp (show (0 : ℤ) + 0 = 0 by omega)
            (S.shift.toShift 1 c x 0 (A.d E.π)) E.s := by
      simpa [DGCategory.d'] using
        S.shift.toShift_comp_right (n := 1) (m := 0) (g := A.d E.π) (f := E.s)
    have h := hc
    rw [GradedSplitShortExact.connectingHom_eq_neg_d_comp, map_neg, hcomp', htoD, comp_neg_left,
      neg_neg] at h
    exact h
  have hδp : A.comp (show (1 : ℤ) + (-1) = 0 by omega)
      (GradedSplitShortExact.connectingHom E) p = E.π := by
    apply (S.shift.toShift 1 c x (-1)).injective
    have hcomp := S.shift.toShift_comp_right (n := 1) (m := 0)
      (g := GradedSplitShortExact.connectingHom E) (f := p)
    calc
      S.shift.toShift 1 c x (-1)
          (A.comp (show (1 : ℤ) + (-1) = 0 by omega)
            (GradedSplitShortExact.connectingHom E) p) =
          A.comp (show (0 : ℤ) + (-1) = -1 by omega)
            (S.shift.toShift 1 z x 0 (GradedSplitShortExact.connectingHom E)) p := hcomp
      _ = p := by rw [hc, A.id_comp]
  have hbD : A.comp (show (0 : ℤ) + 1 = 1 by omega) E.b.1 D = 0 := by
    have h := A.leibniz (show (0 : ℤ) + 0 = 0 by omega) E.b.1 E.s
    rw [E.b_s, A.d_id] at h
    simpa [E.b.2] using h.symm
  have hπa : A.comp (show (1 : ℤ) + 0 = 1 by omega) (A.d E.π) E.a.1 = 0 := by
    have h := A.leibniz (show (0 : ℤ) + 0 = 0 by omega) E.π E.a.1
    rw [E.π_a, A.d_id] at h
    simpa [E.a.2] using h.symm
  have hQa : A.comp (show (0 : ℤ) + 0 = 0 by omega) Q E.a.1 = 0 := by
    have hcomp := S.shift.toShift_comp_right (n := 1) (m := 0) (g := A.d E.π) (f := E.a.1)
    rw [hπa, map_zero, htoD, comp_neg_left] at hcomp
    exact neg_eq_zero.mp hcomp.symm
  have hDp : A.comp (show (1 : ℤ) + (-1) = 0 by omega) D p =
      A.comp (show (0 : ℤ) + 0 = 0 by omega) E.a.1 E.π := by
    have hleft : A.comp (show (0 : ℤ) + 0 = 0 by omega) E.b.1
        (A.comp (show (1 : ℤ) + (-1) = 0 by omega) D p) = 0 := by
      rw [A.assoc (show (1 : ℤ) + (-1) = 0 by omega) (show (0 : ℤ) + 0 = 0 by omega)
        (show (0 : ℤ) + 1 = 1 by omega) (show (1 : ℤ) + (-1) = 0 by omega) E.b.1 D p, hbD]
      simp
    have hπDp : A.comp (show (0 : ℤ) + 0 = 0 by omega) E.π
        (A.comp (show (1 : ℤ) + (-1) = 0 by omega) D p) = E.π := by
      rw [A.assoc (show (1 : ℤ) + (-1) = 0 by omega) (show (0 : ℤ) + 0 = 0 by omega)
        (show (0 : ℤ) + 1 = 1 by omega) (show (1 : ℤ) + (-1) = 0 by omega) E.π D p]
      simpa [GradedSplitShortExact.connectingHom] using hδp
    have hsleft : A.comp (show (0 : ℤ) + 0 = 0 by omega)
        (A.comp (show (0 : ℤ) + 0 = 0 by omega) E.s E.b.1)
        (A.comp (show (1 : ℤ) + (-1) = 0 by omega) D p) = 0 := by
      rw [← A.assoc (show (0 : ℤ) + 0 = 0 by omega) (show (0 : ℤ) + 0 = 0 by omega)
        (show (0 : ℤ) + 0 = 0 by omega) (show (0 : ℤ) + 0 = 0 by omega) E.s E.b.1
        (A.comp (show (1 : ℤ) + (-1) = 0 by omega) D p), hleft]
      simp
    calc
      A.comp (show (1 : ℤ) + (-1) = 0 by omega) D p =
          A.comp (show (0 : ℤ) + 0 = 0 by omega) (A.id c)
            (A.comp (show (1 : ℤ) + (-1) = 0 by omega) D p) := by rw [A.id_comp]
      _ = A.comp (show (0 : ℤ) + 0 = 0 by omega)
            (A.comp (show (0 : ℤ) + 0 = 0 by omega) E.a.1 E.π +
              A.comp (show (0 : ℤ) + 0 = 0 by omega) E.s E.b.1)
            (A.comp (show (1 : ℤ) + (-1) = 0 by omega) D p) := by rw [E.a_π_add_s_b]
      _ = A.comp (show (0 : ℤ) + 0 = 0 by omega)
            (A.comp (show (0 : ℤ) + 0 = 0 by omega) E.a.1 E.π)
            (A.comp (show (1 : ℤ) + (-1) = 0 by omega) D p) := by
              rw [A.comp_add_left, hsleft, add_zero]
      _ = A.comp (show (0 : ℤ) + 0 = 0 by omega) E.a.1 E.π := by
            have hfactor := A.assoc (show (0 : ℤ) + 0 = 0 by omega)
              (show (0 : ℤ) + 0 = 0 by omega) (show (0 : ℤ) + 0 = 0 by omega)
              (show (0 : ℤ) + 0 = 0 by omega) E.a.1 E.π
              (A.comp (show (1 : ℤ) + (-1) = 0 by omega) D p)
            rw [← hfactor, hπDp]
  have hQb : A.comp (show (0 : ℤ) + 0 = 0 by omega) Q (A.id c) = E.b.1 := by
    calc
      A.comp (show (0 : ℤ) + 0 = 0 by omega) Q (A.id c) =
          A.comp (show (0 : ℤ) + 0 = 0 by omega) Q
            (A.comp (show (0 : ℤ) + 0 = 0 by omega) E.a.1 E.π +
              A.comp (show (0 : ℤ) + 0 = 0 by omega) E.s E.b.1) :=
            (congrArg (A.comp (show (0 : ℤ) + 0 = 0 by omega) Q) E.a_π_add_s_b).symm
      _ = A.comp (show (0 : ℤ) + 0 = 0 by omega)
            Q (A.comp (show (0 : ℤ) + 0 = 0 by omega) E.a.1 E.π) +
          A.comp (show (0 : ℤ) + 0 = 0 by omega)
            Q (A.comp (show (0 : ℤ) + 0 = 0 by omega) E.s E.b.1) := by rw [A.comp_add_right]
      _ = A.comp (show (0 : ℤ) + 0 = 0 by omega) (A.id z) E.b.1 := by
            rw [A.assoc (show (0 : ℤ) + 0 = 0 by omega) (show (0 : ℤ) + 0 = 0 by omega)
              (show (0 : ℤ) + 0 = 0 by omega) (show (0 : ℤ) + 0 = 0 by omega) Q E.a.1 E.π, hQa]
            rw [A.assoc (show (0 : ℤ) + 0 = 0 by omega) (show (0 : ℤ) + 0 = 0 by omega)
              (show (0 : ℤ) + 0 = 0 by omega) (show (0 : ℤ) + 0 = 0 by omega) Q E.s E.b.1, hQs]
            simp only [A.comp_zero_left, zero_add]
      _ = E.b.1 := A.id_comp E.b.1
  have hdQ : A.d p = E.b.1 := by rw [← hQb, A.comp_id]
  change A.Homotopic (⟨A.id c, A.d_id c⟩ : A.Cocycle c c) (⟨0, A.d_zero⟩ : A.Cocycle c c)
  change ∃ h : A.Hom c c (-1), (A.id c - 0) = A.d' (show (-1 : ℤ) + 1 = 0 by omega) h
  refine ⟨A.comp (show (0 : ℤ) + (-1) = -1 by omega) E.s p, ?_⟩
  rw [sub_zero]
  change A.id c = A.d (A.comp (show (0 : ℤ) + (-1) = -1 by omega) E.s p)
  rw [A.leibniz (show (0 : ℤ) + (-1) = -1 by omega) E.s p]
  simp only [show (-1 : R) ^ (Int.natAbs 0) = 1 by norm_num, one_smul]
  rw [hDp, hdQ]
  exact E.a_π_add_s_b.symm

/-- The identity of the cone of an identity morphism is homotopic to zero. -/
@[stacks 09QK]
theorem id_cone_homotopic_zero (S : ConeSituation A) (x : A.Obj) :
    let c := S.cone (⟨A.id x, A.d_id x⟩ : A.Cocycle x x)
    A.Homotopic (⟨A.id c, A.d_id c⟩ : A.Cocycle c c) (⟨0, A.d_zero⟩ : A.Cocycle c c) :=
  ConeSituationIso.id_cone_homotopic_zero S.toConeSituationIso x

end DGCategory
