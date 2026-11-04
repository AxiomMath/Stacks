module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.ConeMorphism

/-!
# Replacing morphisms of complexes by admissible monomorphisms

In a differential graded category with direct sums, shifts and cones, every closed degree-zero
morphism factors as an admissible monomorphism followed by a morphism with a strict section which
is a homotopy equivalence; the admissible monomorphism is the first arrow of a graded-split short
exact sequence. Applying this repeatedly replaces a whole finite chain of morphisms by a chain of
admissible monomorphisms, with a homotopy equivalence at each vertex.

## Main results

* `DGCategory.exists_admissibleMono_factorization`: the factorization of a single morphism.
* `DGCategory.exists_admissibleMono_sequence`: the simultaneous replacement of all terms and
  arrows of a finite chain.

## References

* [Stacks Project, Tag 09QM](https://stacks.math.columbia.edu/tag/09QM)
* [Stacks Project, Tag 09QN](https://stacks.math.columbia.edu/tag/09QN)
-/

@[expose] public section

open CategoryTheory

namespace DGCategory

universe u v w

/-- For a cone situation whose shift is additive up to isomorphism, every morphism in the category
of complexes factors through an admissible monomorphism followed by a retraction admitting a
strict section and a homotopy inverse. -/
public theorem ConeSituationIso.exists_admissibleMono_factorization
    {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}
    (S : ConeSituationIso A) {x y : A.Obj} (α : A.Cocycle x y) :
    ∃ (y' z : A.Obj) (E : GradedSplitShortExact (A := A) x y' z)
      (π : A.Cocycle y' y) (s : A.Cocycle y y'),
      (A.compCocycle π E.a = α) ∧
      (A.compCocycle π s = (⟨A.id y, A.d_id y⟩ : A.Cocycle y y)) ∧
      A.Homotopic (A.compCocycle s π)
        (⟨A.id y', A.d_id y'⟩ : A.Cocycle y' y') := by
  classical
  let X := (S.shift.shiftFunctor 1).obj x
  let U : A.Cocycle x x := ⟨A.id x, A.d_id x⟩
  let E₁ := S.coneSequence U
  let E₂ := S.coneSequence α
  let C := S.cone U
  let Z := S.cone α
  let F := S.shift.shiftFunctor 1
  have hshiftid : (F.mapCocycle U).1 = A.id X := by
    simpa [F, U, DGCategory.DGFunctor.mapCocycle] using F.map_id x
  have hto {w : A.Obj} (β : A.Cocycle x w) :
      (S.shift.toShift 1 X w 0) (GradedSplitShortExact.connectingHom (S.coneSequence β)) =
        (F.mapCocycle β).1 := by
    simpa [ShiftAxiomBIso.connectingCocycle] using
      congrArg Subtype.val (S.cone_connecting β)
  have hg : A.comp (by omega : (0 : ℤ) + 1 = 1) α.1
        (GradedSplitShortExact.connectingHom E₁) = GradedSplitShortExact.connectingHom E₂ := by
    apply (S.shift.toShift 1 X y 0).injective
    have hleft := S.shift.toShift_comp_left (n := 1) (m := 0) (l := 0)
      α.1 (GradedSplitShortExact.connectingHom E₁)
    rw [hto U, hshiftid, A.comp_id] at hleft
    refine Eq.trans ?_ (hto α).symm
    simpa [F, X, DGCategory.DGFunctor.mapCocycle] using hleft
  have hpi : A.d E₁.π =
      -A.comp (by omega : (1 : ℤ) + 0 = 1)
        (GradedSplitShortExact.connectingHom E₁) E₁.b.1 := by
    have hh := GradedSplitShortExact.connectingHom_comp E₁
    rw [show -E₁.π = (-1 : R) • E₁.π by rw [neg_one_smul], A.d_smul, neg_one_smul] at hh
    rw [hh, neg_neg]
  have hds : A.d E₂.s =
      A.comp (by omega : (0 : ℤ) + 1 = 1) E₂.a.1
        (GradedSplitShortExact.connectingHom E₂) :=
    (GradedSplitShortExact.comp_connectingHom E₂).symm
  let c₀ : A.Hom C Z 0 :=
    A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.a.1
        (A.comp (by omega : (0 : ℤ) + 0 = 0) α.1 E₁.π) +
      A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.s
        E₁.b.1
  have hc₀ : A.d c₀ = 0 := by
    dsimp [c₀]
    rw [A.d_add]
    have h₁ : A.d (A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.a.1
        (A.comp (by omega : (0 : ℤ) + 0 = 0) α.1 E₁.π)) =
        A.comp (by omega : (0 : ℤ) + 1 = 1) E₂.a.1
          (A.comp (by omega : (0 : ℤ) + 1 = 1)
            α.1 (A.d E₁.π)) := by
      simp [A.leibniz, E₂.a.2, α.2, pow_zero, one_smul,
        A.comp_zero_left]
    have h₂ : A.d (A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.s
        E₁.b.1) =
        A.comp (by omega : (1 : ℤ) + 0 = 1) (A.d E₂.s)
          E₁.b.1 := by
      simp [A.leibniz, E₁.b.2, pow_zero,
        A.comp_zero_right]
    rw [h₁, h₂, hpi, hds]
    have hterm₁ : A.comp (by omega : (0 : ℤ) + 1 = 1) E₂.a.1
        (A.comp (by omega : (0 : ℤ) + 1 = 1) α.1
          (-A.comp (by omega : (1 : ℤ) + 0 = 1)
            (GradedSplitShortExact.connectingHom E₁) E₁.b.1)) =
        -A.comp (by omega : (0 : ℤ) + 1 = 1) E₂.a.1
          (A.comp (by omega : (1 : ℤ) + 0 = 1)
            (GradedSplitShortExact.connectingHom E₂) E₁.b.1) := by
      have ha : A.comp (by omega : (0 : ℤ) + 1 = 1) α.1
          (A.comp (by omega : (1 : ℤ) + 0 = 1)
            (GradedSplitShortExact.connectingHom E₁) E₁.b.1) =
          A.comp (by omega : (1 : ℤ) + 0 = 1)
            (A.comp (by omega : (0 : ℤ) + 1 = 1) α.1
              (GradedSplitShortExact.connectingHom E₁)) E₁.b.1 :=
        A.assoc (by omega : (1 : ℤ) + 0 = 1)
          (by omega : (0 : ℤ) + 1 = 1)
          (by omega : (0 : ℤ) + 1 = 1)
          (by omega : (1 : ℤ) + 0 = 1)
          α.1 (GradedSplitShortExact.connectingHom E₁) E₁.b.1
      rw [comp_neg_right, comp_neg_right, ha, hg]
    have hterm₂ : A.comp (by omega : (1 : ℤ) + 0 = 1)
        (A.comp (by omega : (0 : ℤ) + 1 = 1) E₂.a.1
          (GradedSplitShortExact.connectingHom E₂)) E₁.b.1 =
        A.comp (by omega : (0 : ℤ) + 1 = 1) E₂.a.1
          (A.comp (by omega : (1 : ℤ) + 0 = 1)
            (GradedSplitShortExact.connectingHom E₂) E₁.b.1) :=
      (A.assoc (by omega : (1 : ℤ) + 0 = 1)
        (by omega : (0 : ℤ) + 1 = 1)
        (by omega : (0 : ℤ) + 1 = 1)
        (by omega : (1 : ℤ) + 0 = 1)
        E₂.a.1 (GradedSplitShortExact.connectingHom E₂) E₁.b.1).symm
    rw [hterm₁, hterm₂]
    abel
  let D := Classical.choice (S.directSum.binaryBiproduct C y)
  let ι₁ : A.Cocycle C D.pt := ⟨D.inl, D.inl_closed⟩
  let ι₂ : A.Cocycle y D.pt := ⟨D.inr, D.inr_closed⟩
  let p₁ : A.Cocycle D.pt C := ⟨D.fst, D.fst_closed⟩
  let p₂ : A.Cocycle D.pt y := ⟨D.snd, D.snd_closed⟩
  have assoc₀ {W V Y Z₀ : A.Obj} (e : A.Hom Y Z₀ 0)
      (g : A.Hom V Y 0) (f : A.Hom W V 0) :
      A.comp (by omega : (0 : ℤ) + 0 = 0) e
        (A.comp (by omega : (0 : ℤ) + 0 = 0) g f) =
      A.comp (by omega : (0 : ℤ) + 0 = 0)
        (A.comp (by omega : (0 : ℤ) + 0 = 0) e g) f :=
    A.assoc (by omega : (0 : ℤ) + 0 = 0)
      (by omega : (0 : ℤ) + 0 = 0)
      (by omega : (0 : ℤ) + 0 = 0)
      (by omega : (0 : ℤ) + 0 = 0) e g f
  have fst_inr_comp {W : A.Obj} (f : A.Hom W y 0) :
      A.comp (by omega : (0 : ℤ) + 0 = 0) D.fst
        (A.comp (by omega : (0 : ℤ) + 0 = 0) D.inr f) = 0 := by
    rw [assoc₀, D.inr_fst]
    simp
  have fst_inl_comp {W : A.Obj} (f : A.Hom W C 0) :
      A.comp (by omega : (0 : ℤ) + 0 = 0) D.fst
        (A.comp (by omega : (0 : ℤ) + 0 = 0) D.inl f) = f := by
    rw [assoc₀, D.inl_fst, A.id_comp]
  have snd_inl_comp {W : A.Obj} (f : A.Hom W C 0) :
      A.comp (by omega : (0 : ℤ) + 0 = 0) D.snd
        (A.comp (by omega : (0 : ℤ) + 0 = 0) D.inl f) = 0 := by
    rw [assoc₀, D.inl_snd]
    simp
  have snd_inr_comp {W : A.Obj} (f : A.Hom W y 0) :
      A.comp (by omega : (0 : ℤ) + 0 = 0) D.snd
        (A.comp (by omega : (0 : ℤ) + 0 = 0) D.inr f) = f := by
    rw [assoc₀, D.inr_snd, A.id_comp]
  have e1pi_s {W : A.Obj} (f : A.Hom W X 0) :
      A.comp (by omega : (0 : ℤ) + 0 = 0) E₁.π
        (A.comp (by omega : (0 : ℤ) + 0 = 0) E₁.s f) = 0 := by
    rw [assoc₀, E₁.π_s]
    simp
  have e2pi_a {W : A.Obj} (f : A.Hom W y 0) :
      A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.π
        (A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.a.1 f) = f := by
    rw [assoc₀, E₂.π_a, A.id_comp]
  have e2pi_s {W : A.Obj} (f : A.Hom W X 0) :
      A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.π
        (A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.s f) = 0 := by
    rw [assoc₀, E₂.π_s]
    simp
  let a₀ : A.Hom x D.pt 0 :=
    A.comp (by omega : (0 : ℤ) + 0 = 0) D.inr α.1 +
      A.comp (by omega : (0 : ℤ) + 0 = 0) D.inl E₁.a.1
  let b₀ : A.Hom D.pt Z 0 :=
    A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.a.1 D.snd -
      A.comp (by omega : (0 : ℤ) + 0 = 0) c₀ D.fst
  let pi₀ : A.Hom D.pt x 0 :=
    A.comp (by omega : (0 : ℤ) + 0 = 0) E₁.π D.fst
  let s₀ : A.Hom Z D.pt 0 :=
    A.comp (by omega : (0 : ℤ) + 0 = 0) D.inr E₂.π -
      A.comp (by omega : (0 : ℤ) + 0 = 0) D.inl
        (A.comp (by omega : (0 : ℤ) + 0 = 0) E₁.s E₂.b.1)
  let aa : A.Cocycle x D.pt := ⟨a₀, by
    dsimp [a₀]
    rw [A.d_add]
    simp [A.leibniz, α.2, E₁.a.2, D.inr_closed, D.inl_closed,
      pow_zero, A.comp_zero_left, A.comp_zero_right]⟩
  let bb : A.Cocycle D.pt Z := ⟨b₀, by
    dsimp [b₀]
    have dsub {m : ℤ} (f g : A.Hom D.pt Z m) :
        A.d (f - g) = A.d f - A.d g := by
      rw [sub_eq_add_neg, A.d_add,
        show -g = (-1 : R) • g by rw [neg_one_smul],
        A.d_smul, neg_one_smul, ← sub_eq_add_neg]
    have hfirst : A.d (A.comp (by omega : (0 : ℤ) + 0 = 0)
        E₂.a.1 D.snd) = 0 := by
      simp [A.leibniz, E₂.a.2, D.snd_closed, pow_zero,
        A.comp_zero_left, A.comp_zero_right]
    have hsecond : A.d (A.comp (by omega : (0 : ℤ) + 0 = 0)
        c₀ D.fst) = 0 := by
      simp [A.leibniz, hc₀, D.fst_closed, pow_zero,
        A.comp_zero_left, A.comp_zero_right]
    rw [dsub, hfirst, hsecond]
    simp⟩
  have hc_a : A.comp (by omega : (0 : ℤ) + 0 = 0) c₀ E₁.a.1 =
      A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.a.1 α.1 := by
    dsimp [c₀]
    rw [A.comp_add_left]
    simp [← A.assoc, E₁.π_a, GradedSplitShortExact.comp_zero E₁,
      A.comp_id,
      A.comp_zero_right]
  have hpi_c : A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.π c₀ =
      A.comp (by omega : (0 : ℤ) + 0 = 0) α.1 E₁.π := by
    dsimp [c₀]
    rw [A.comp_add_right]
    simp [e2pi_a, e2pi_s]
  have hc_b : A.comp (by omega : (0 : ℤ) + 0 = 0) E₂.b.1 c₀ =
      E₁.b.1 := by
    dsimp [c₀]
    rw [A.comp_add_right]
    simp [A.assoc, GradedSplitShortExact.comp_zero E₂, E₂.b_s,
      A.comp_zero_left, A.id_comp]
  have hc_s : A.comp (by omega : (0 : ℤ) + 0 = 0) c₀ E₁.s = E₂.s := by
    dsimp [c₀]
    rw [A.comp_add_left]
    simp [← A.assoc, E₁.π_s, E₁.b_s,
      A.comp_zero_right, A.comp_id]
  have hcancel :
      A.comp (by omega : (0 : ℤ) + 0 = 0)
          (A.comp (by omega : (0 : ℤ) + 0 = 0)
            (A.comp (by omega : (0 : ℤ) + 0 = 0) D.inr α.1) E₁.π) D.fst =
        A.comp (by omega : (0 : ℤ) + 0 = 0)
          (A.comp (by omega : (0 : ℤ) + 0 = 0)
            (A.comp (by omega : (0 : ℤ) + 0 = 0) D.inr E₂.π) c₀) D.fst := by
    rw [← assoc₀ D.inr α.1 E₁.π, ← hpi_c, assoc₀ D.inr E₂.π c₀]
  have hterm₂ :
      A.comp (by omega : (0 : ℤ) + 0 = 0)
          (A.comp (by omega : (0 : ℤ) + 0 = 0)
            (A.comp (by omega : (0 : ℤ) + 0 = 0) D.inr E₂.π) E₂.a.1) D.snd =
        A.comp (by omega : (0 : ℤ) + 0 = 0) D.inr D.snd := by
    rw [← assoc₀ D.inr E₂.π E₂.a.1, E₂.π_a]
    simp [A.comp_id]
  have hterm₃ :
      A.comp (by omega : (0 : ℤ) + 0 = 0)
          (A.comp (by omega : (0 : ℤ) + 0 = 0)
            (A.comp (by omega : (0 : ℤ) + 0 = 0)
              (A.comp (by omega : (0 : ℤ) + 0 = 0) D.inl E₁.s) E₂.b.1) E₂.a.1) D.snd = 0 := by
    rw [← assoc₀ D.inl E₁.s E₂.b.1,
      ← assoc₀ D.inl (A.comp (by omega : (0 : ℤ) + 0 = 0) E₁.s E₂.b.1) E₂.a.1,
      ← assoc₀ E₁.s E₂.b.1 E₂.a.1, GradedSplitShortExact.comp_zero E₂]
    simp
  have hterm₄ :
      A.comp (by omega : (0 : ℤ) + 0 = 0)
          (A.comp (by omega : (0 : ℤ) + 0 = 0)
            (A.comp (by omega : (0 : ℤ) + 0 = 0)
              (A.comp (by omega : (0 : ℤ) + 0 = 0) D.inl E₁.s) E₂.b.1) c₀) D.fst =
        A.comp (by omega : (0 : ℤ) + 0 = 0)
          (A.comp (by omega : (0 : ℤ) + 0 = 0)
            (A.comp (by omega : (0 : ℤ) + 0 = 0) D.inl E₁.s) E₁.b.1) D.fst := by
    rw [← assoc₀ D.inl E₁.s E₂.b.1,
      ← assoc₀ D.inl (A.comp (by omega : (0 : ℤ) + 0 = 0) E₁.s E₂.b.1) c₀,
      ← assoc₀ E₁.s E₂.b.1 c₀, hc_b, assoc₀ D.inl E₁.s E₁.b.1]
  have hsum :
      A.comp (by omega : (0 : ℤ) + 0 = 0)
          (A.comp (by omega : (0 : ℤ) + 0 = 0)
            (A.comp (by omega : (0 : ℤ) + 0 = 0) D.inl E₁.a.1) E₁.π) D.fst +
        A.comp (by omega : (0 : ℤ) + 0 = 0)
          (A.comp (by omega : (0 : ℤ) + 0 = 0)
            (A.comp (by omega : (0 : ℤ) + 0 = 0) D.inl E₁.s) E₁.b.1) D.fst =
      A.comp (by omega : (0 : ℤ) + 0 = 0) D.inl D.fst := by
    rw [← assoc₀ D.inl E₁.a.1 E₁.π, ← assoc₀ D.inl E₁.s E₁.b.1, ← A.comp_add_left,
      ← A.comp_add_right, E₁.a_π_add_s_b]
    simp [A.comp_id]
  let E : GradedSplitShortExact (A := A) x D.pt Z := {
    a := aa
    b := bb
    π := pi₀
    s := s₀
    π_a := by
      dsimp [pi₀, a₀]
      rw [A.comp_add_right, ← assoc₀ E₁.π D.fst (A.comp (by omega : (0 : ℤ) + 0 = 0) D.inr α.1),
        ← assoc₀ E₁.π D.fst (A.comp (by omega : (0 : ℤ) + 0 = 0) D.inl E₁.a.1), fst_inr_comp,
        fst_inl_comp, E₁.π_a]
      simp [A.comp_zero_right]
    b_s := by
      dsimp [b₀, s₀, bb]
      simp only [A.comp_sub_left, ← assoc₀, A.comp_sub_right, snd_inr_comp, snd_inl_comp,
        sub_zero, fst_inr_comp, fst_inl_comp, zero_sub, comp_neg_right, sub_neg_eq_add]
      rw [assoc₀ c₀ E₁.s E₂.b.1, hc_s, E₂.a_π_add_s_b]
    π_s := by
      dsimp [pi₀, s₀]
      rw [A.comp_sub_right, ← assoc₀ E₁.π D.fst (A.comp (by omega : (0 : ℤ) + 0 = 0) D.inr E₂.π),
        ← assoc₀ E₁.π D.fst (A.comp (by omega : (0 : ℤ) + 0 = 0) D.inl
          (A.comp (by omega : (0 : ℤ) + 0 = 0) E₁.s E₂.b.1)), fst_inr_comp, fst_inl_comp, e1pi_s]
      simp
    a_π_add_s_b := by
      dsimp [a₀, pi₀, s₀, b₀, aa, bb]
      simp only [assoc₀, A.comp_add_left, hcancel, A.comp_sub_left, A.comp_sub_right]
      rw [hterm₂, hterm₃, hterm₄]
      abel_nf
      rw [add_comm (A.comp (by omega : (0 : ℤ) + 0 = 0) D.inr D.snd)
          (A.comp (by omega : (0 : ℤ) + 0 = 0)
            (A.comp (by omega : (0 : ℤ) + 0 = 0)
              (A.comp (by omega : (0 : ℤ) + 0 = 0) D.inl E₁.s) E₁.b.1) D.fst),
        ← add_assoc, hsum, D.fst_inl_add_snd_inr]
  }
  refine ⟨D.pt, Z, E, p₂, ι₂, ?_, ?_, ?_⟩
  · apply Subtype.ext
    dsimp [DGCategory.compCocycle, p₂, aa, a₀]
    rw [A.comp_add_right, snd_inr_comp, snd_inl_comp]
    simp
  · apply Subtype.ext
    dsimp [DGCategory.compCocycle, p₂, ι₂]
    simp [D.inr_snd]
  · have hnull' : A.Homotopic (⟨A.id C, A.d_id C⟩ : A.Cocycle C C)
        (⟨0, A.d_zero⟩ : A.Cocycle C C) := by
      simpa [C, U] using id_cone_homotopic_zero S x
    have hproj : A.Homotopic (A.compCocycle ι₁ p₁)
        (⟨0, A.d_zero⟩ : A.Cocycle D.pt D.pt) := by
      have hleft := A.compCocycle_homotopic_right ι₁ hnull'
      have hright := A.compCocycle_homotopic_left p₁ hleft
      simpa [DGCategory.compCocycle, A.id_comp, A.comp_id,
        A.comp_zero_right] using hright
    have hid : A.id D.pt -
        A.comp (by omega : (0 : ℤ) + 0 = 0) D.inr D.snd =
          A.comp (by omega : (0 : ℤ) + 0 = 0) D.inl D.fst := by
      rw [← D.fst_inl_add_snd_inr]
      abel
    apply A.homotopic_symm
    obtain ⟨h, hh⟩ := hproj
    refine ⟨h, ?_⟩
    show (A.id D.pt - A.comp (by omega : (0 : ℤ) + 0 = 0) D.inr D.snd) =
      A.d' (by omega : (-1 : ℤ) + 1 = 0) h
    rw [hid]
    simpa [DGCategory.compCocycle] using hh


/-- Every morphism in the category of complexes factors through an admissible monomorphism
followed by a retraction admitting a strict section and a homotopy inverse. -/
@[stacks 09QM]
public theorem exists_admissibleMono_factorization
    {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}
    (S : ConeSituation A) {x y : A.Obj} (α : A.Cocycle x y) :
    ∃ (y' z : A.Obj) (E : GradedSplitShortExact (A := A) x y' z)
      (π : A.Cocycle y' y) (s : A.Cocycle y y'),
      (A.compCocycle π E.a = α) ∧
      (A.compCocycle π s = (⟨A.id y, A.d_id y⟩ : A.Cocycle y y)) ∧
      A.Homotopic (A.compCocycle s π)
        (⟨A.id y', A.d_id y'⟩ : A.Cocycle y' y') :=
  ConeSituationIso.exists_admissibleMono_factorization S.toConeSituationIso α
private def transportGradedSplitShortExact
    {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}
    {x x' y y' z : A.Obj} (hx : x' = x) (hy : y' = y)
    (E : GradedSplitShortExact (A := A) x y z) :
    GradedSplitShortExact (A := A) x' y' z := by
  cases hx; cases hy; exact E

section ObjectCategory

variable {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}

local instance : Category A.Obj := DGCategory.instCategoryComp (A := A)

private theorem transportGradedSplitShortExact_a
    {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}
    {x x' y y' z : A.Obj} (hx : x' = x) (hy : y' = y)
    (E : GradedSplitShortExact (A := A) x y z) :
    (transportGradedSplitShortExact hx hy E).a =
      eqToHom hx ≫ E.a ≫ eqToHom hy.symm := by
  cases hx; cases hy; simp [transportGradedSplitShortExact]

end ObjectCategory

/-- For a cone situation whose shift is additive up to isomorphism, a finite chain of maps in the
category of complexes has a commuting replacement by admissible monomorphisms, with a homotopy
equivalence at every vertex. -/
public theorem ConeSituationIso.exists_admissibleMono_sequence {R : Type w} [CommRing R]
    (A : DGCategory.{v, u} R) (S : ConeSituationIso A) (n : ℕ)
    (x : Fin (n + 1) → A.Comp)
    (f : ∀ i : Fin n, x i.castSucc ⟶ x i.succ) :
    ∃ (y : Fin (n + 1) → A.Comp)
      (g : ∀ i : Fin n, y i.castSucc ⟶ y i.succ)
      (p : ∀ i : Fin (n + 1), y i ⟶ x i),
      (∀ i : Fin n,
        ∃ z : A.Obj, ∃ E : GradedSplitShortExact (A := A)
          (y i.castSucc) (y i.succ) z, E.a = g i) ∧
      (∀ i : Fin (n + 1), IsIso ((A.compToK).map (p i))) ∧
      (∀ i : Fin n, g i ≫ p i.succ = p i.castSucc ≫ f i) := by
  induction n with
  | zero =>
      exact ⟨x, (fun i => i.elim0), (fun i => 𝟙 (x i)),
        (fun i => i.elim0), (fun _ => inferInstance), (fun i => i.elim0)⟩
  | succ n ih =>
      let x₀ : Fin (n + 1) → A.Comp := fun i => x i.castSucc
      let f₀ : ∀ i : Fin n, x₀ i.castSucc ⟶ x₀ i.succ := fun i => f i.castSucc
      obtain ⟨y₀, g₀, p₀, hE₀, hp₀, hcomm₀⟩ := ih x₀ f₀
      let α : y₀ (Fin.last n) ⟶ x (Fin.last n).succ := p₀ (Fin.last n) ≫ f (Fin.last n)
      obtain ⟨y₁, z₁, E₁, π, s, hfactor, hsπ, hπs⟩ :=
        ConeSituationIso.exists_admissibleMono_factorization S α
      let y₁c : A.Comp := y₁
      let a₁ : y₀ (Fin.last n) ⟶ y₁c := E₁.a
      let πc : y₁c ⟶ x (Fin.last n).succ := π
      let sc : x (Fin.last n).succ ⟶ y₁c := s
      let y : Fin (n + 2) → A.Comp := Fin.lastCases y₁c (fun i => y₀ i)
      have hycast (i : Fin (n + 1)) : y i.castSucc = y₀ i := Fin.lastCases_castSucc i
      have hylast : y (Fin.last (n + 1)) = y₁c := Fin.lastCases_last
      have hysucc (i : Fin n) : y i.castSucc.succ = y₀ i.succ := by
        rw [Fin.succ_castSucc]; exact hycast i.succ
      have hylastSucc : y (Fin.last n).succ = y₁c := by
        rw [Fin.succ_last]; exact hylast
      have hxlast : x (Fin.last n).succ = x (Fin.last (n + 1)) := by
        rw [Fin.succ_last]
      let g : ∀ i : Fin (n + 1), y i.castSucc ⟶ y i.succ :=
        Fin.lastCases
          (eqToHom (hycast (Fin.last n)) ≫ a₁ ≫ eqToHom hylastSucc.symm)
          (fun i => eqToHom (hycast i.castSucc) ≫ g₀ i ≫ eqToHom (hysucc i).symm)
      let p : ∀ i : Fin (n + 2), y i ⟶ x i :=
        Fin.lastCases (eqToHom hylast ≫ πc ≫ eqToHom hxlast)
          (fun i => eqToHom (hycast i) ≫ p₀ i)
      have hfactorC : a₁ ≫ πc = α := by
        show A.compCocycle π E₁.a = α; exact hfactor
      have hg_last : g (Fin.last n) =
          eqToHom (hycast (Fin.last n)) ≫ a₁ ≫ eqToHom hylastSucc.symm := by
        unfold g; rw [Fin.lastCases_last]
      have hg_cast (i : Fin n) :
          g i.castSucc = eqToHom (hycast i.castSucc) ≫ g₀ i ≫ eqToHom (hysucc i).symm := by
        unfold g; rw [Fin.lastCases_castSucc]
      have hp_last : p (Fin.last (n + 1)) = eqToHom hylast ≫ πc ≫ eqToHom hxlast := by
        unfold p; rw [Fin.lastCases_last]
      have hp_cast (i : Fin (n + 1)) : p i.castSucc = eqToHom (hycast i) ≫ p₀ i := by
        unfold p; rw [Fin.lastCases_castSucc]
      refine ⟨y, g, p, ?_, ?_, ?_⟩
      · intro i; induction i using Fin.lastCases with
        | last =>
            rw [hg_last]
            have hx : (y (Fin.last n).castSucc : A.Obj) = y₀ (Fin.last n) :=
              hycast (Fin.last n)
            have hy : (y (Fin.last n).succ : A.Obj) = y₁ := hylastSucc
            refine ⟨z₁, transportGradedSplitShortExact hx hy E₁, ?_⟩
            rw [transportGradedSplitShortExact_a hx hy E₁]
            rfl
        | cast i =>
            obtain ⟨z, E, hEa⟩ := hE₀ i
            rw [hg_cast]
            have hx : (y i.castSucc.castSucc : A.Obj) = y₀ i.castSucc := hycast i.castSucc
            have hy : (y i.castSucc.succ : A.Obj) = y₀ i.succ := hysucc i
            refine ⟨z, transportGradedSplitShortExact hx hy E, ?_⟩
            rw [transportGradedSplitShortExact_a hx hy E]
            show eqToHom (hycast i.castSucc) ≫ E.a ≫ eqToHom (hysucc i).symm =
              eqToHom (hycast i.castSucc) ≫ g₀ i ≫ eqToHom (hysucc i).symm
            rw [hEa]
      · intro i; induction i using Fin.lastCases with
        | last =>
            rw [hp_last]
            let _ : IsIso (A.compToK.map πc) := by
              refine ⟨⟨A.compToK.map sc, ?_, ?_⟩⟩
              · show Quotient.mk _ (A.compCocycle s π) = Quotient.mk _ _
                exact Quotient.sound hπs
              · show Quotient.mk _ (A.compCocycle π s) = Quotient.mk _ _
                exact Quotient.sound (by rw [hsπ]; exact A.homotopic_refl _)
            rw [Functor.map_comp, Functor.map_comp]
            infer_instance
        | cast i =>
            rw [hp_cast]
            let _ := hp₀ i
            rw [Functor.map_comp]
            infer_instance
      · intro i; induction i using Fin.lastCases with
        | last =>
            have hidx : (Fin.last n).succ = Fin.last (n + 1) := Fin.succ_last n
            have hpidx : p (Fin.last n).succ = p (Fin.last (n + 1)) := by cases hidx; rfl
            rw [hpidx]
            calc
              _ = eqToHom (hycast (Fin.last n)) ≫
                  (a₁ ≫ πc) ≫ eqToHom hxlast := by
                cases hidx
                rw [hg_last, hp_last]
                show (eqToHom (hycast (Fin.last n)) ≫ a₁ ≫
                    eqToHom hylastSucc.symm) ≫
                    (eqToHom hylast ≫ πc ≫ eqToHom hxlast) =
                  (eqToHom (hycast (Fin.last n)) ≫ (a₁ ≫ πc) ≫ eqToHom hxlast)
                simp [Category.assoc]
              _ = eqToHom (hycast (Fin.last n)) ≫ α ≫ eqToHom hxlast := by
                rw [hfactorC]
              _ = p (Fin.last n).castSucc ≫ f (Fin.last n) := by
                rw [hp_cast]
                simp [α, Category.assoc]
        | cast i =>
            calc
              _ = eqToHom (hycast i.castSucc) ≫ (g₀ i ≫ p₀ i.succ) := by
                have hpt : p i.castSucc.succ = eqToHom (hycast i.succ) ≫ p₀ i.succ := by
                  unfold p; simp only [Fin.succ_castSucc, Fin.lastCases_castSucc]
                rw [hg_cast, hpt]
                simp [Category.assoc]
              _ = eqToHom (hycast i.castSucc) ≫ (p₀ i.castSucc ≫ f i.castSucc) := by
                rw [hcomm₀ i]
              _ = p i.castSucc.castSucc ≫ f i.castSucc := by
                rw [hp_cast]
                simp [Category.assoc]


/-- A finite chain of maps in the category of complexes has a commuting replacement by
admissible monomorphisms, with a homotopy equivalence at every vertex. -/
@[stacks 09QN]
public theorem exists_admissibleMono_sequence {R : Type w} [CommRing R]
    (A : DGCategory.{v, u} R) (S : ConeSituation A) (n : ℕ)
    (x : Fin (n + 1) → A.Comp)
    (f : ∀ i : Fin n, x i.castSucc ⟶ x i.succ) :
    ∃ (y : Fin (n + 1) → A.Comp)
      (g : ∀ i : Fin n, y i.castSucc ⟶ y i.succ)
      (p : ∀ i : Fin (n + 1), y i ⟶ x i),
      (∀ i : Fin n,
        ∃ z : A.Obj, ∃ E : GradedSplitShortExact (A := A)
          (y i.castSucc) (y i.succ) z, E.a = g i) ∧
      (∀ i : Fin (n + 1), IsIso ((A.compToK).map (p i))) ∧
      (∀ i : Fin n, g i ≫ p i.succ = p i.castSucc ≫ f i) :=
  ConeSituationIso.exists_admissibleMono_sequence A S.toConeSituationIso n x f
end DGCategory
