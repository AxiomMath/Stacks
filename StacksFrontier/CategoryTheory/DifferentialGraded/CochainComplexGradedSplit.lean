module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexDGCategory
public import StacksFrontier.CategoryTheory.DifferentialGraded.Triangulated

/-!
# Degreewise split short exact sequences are the graded-split sequences of complexes

A short complex `S` of cochain complexes in a preadditive category `B`, together with a splitting
`σ n` of each degree, is exactly a `DGCategory.GradedSplitShortExact` in the differential graded
category `CochainComplex.dgCategory B` of Tag 09L9: the two closed arrows are `S.f` and `S.g`,
read as closed degree-zero cochains, and the two unclosed ones are the families `σ n` of
retractions and sections, read as degree-zero cochains — which are not chain maps, which is
precisely why the connecting morphism is nonzero.

The connecting morphism `π d(s)` of that graded splitting is Mathlib's
`CochainComplex.cocycleOfDegreewiseSplit`, the degree-one cocycle whose component is
`(σ p).s ≫ S.X₂.d p q ≫ (σ q).r`. Since
`CategoryTheory.HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit` describes the
distinguished triangles of `K(B)` by degreewise split sequences, this is what lets a functor out
of `K(B)` be shown exact by transporting graded splittings.

## Main definitions

* `CochainComplex.gradedSplitOfDegreewiseSplit`: the graded-split short exact sequence of
  `CochainComplex.dgCategory B` attached to a degreewise split short complex.

## Main results

* `CochainComplex.connectingHom_gradedSplitOfDegreewiseSplit`: its connecting morphism is
  `CochainComplex.cocycleOfDegreewiseSplit`.

## Implementation notes

The identities of a graded splitting are the fields of `CategoryTheory.ShortComplex.Splitting`
read in the opposite composition order, since `DGCategory.comp h g f` is `g` after `f`; the
remaining one, `π ∘ s = 0`, is `CategoryTheory.ShortComplex.Splitting.s_r`. All of them are
checked componentwise on `CochainComplex.HomComplex.Cochain.ofHoms`.

The computation of the connecting morphism is the one place where the Hom differential enters:
`d(s)` has the two terms of the graded commutator, and the second one is killed after composing
with `π`, again by `π ∘ s = 0`.

## References

* [Stacks Project, Tag 09L9](https://stacks.math.columbia.edu/tag/09L9), the differential graded
  category of complexes, and [Tag 09P6](https://stacks.math.columbia.edu/tag/09P6), the
  connecting morphism of a graded splitting.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex

open CochainComplex.HomComplex HomologicalComplex

variable {B : Type u} [Category.{v} B] [Preadditive B]

/-- Two degree-zero cochains given by families of maps compose to a third exactly when their
families do. -/
private theorem comp_ofHoms_eq {F G K : CochainComplex B ℤ}
    (φ : ∀ p, F.X p ⟶ G.X p) (ψ : ∀ p, G.X p ⟶ K.X p) (χ : ∀ p, F.X p ⟶ K.X p)
    (h : ∀ p, φ p ≫ ψ p = χ p) :
    (dgCategory B).comp (show (0 : ℤ) + 0 = 0 from rfl)
        (Cochain.ofHoms ψ) (Cochain.ofHoms φ) = Cochain.ofHoms χ := by
  ext p q hpq
  obtain rfl : p = q := by omega
  rw [dgCategory_comp_v (B := B) (show (0 : ℤ) + 0 = 0 from rfl) (Cochain.ofHoms ψ)
      (Cochain.ofHoms φ) p p p (add_zero p) (add_zero p),
    Cochain.ofHoms_v, Cochain.ofHoms_v, Cochain.ofHoms_v, h p]

section

variable (S : ShortComplex (CochainComplex B ℤ))
  (σ : ∀ n, (S.map (eval B (ComplexShape.up ℤ) n)).Splitting)

/-- The degree-zero cochain of the retractions `σ n`, a graded splitting of `S.f`. -/
def gradedRetractionOfSplit : (dgCategory B).Hom S.X₂ S.X₁ 0 :=
  Cochain.ofHoms (fun p => (σ p).r)

/-- The degree-zero cochain of the sections `σ n`, a graded splitting of `S.g`. -/
def gradedSectionOfSplit : (dgCategory B).Hom S.X₃ S.X₂ 0 :=
  Cochain.ofHoms (fun p => (σ p).s)

/-- The closed degree-zero cochain of `S.f`. -/
def cocycleOfSplitF : (dgCategory B).Cocycle S.X₁ S.X₂ :=
  ⟨Cochain.ofHom S.f, by change δ 0 1 (Cochain.ofHom S.f) = 0; simp⟩

/-- The closed degree-zero cochain of `S.g`. -/
def cocycleOfSplitG : (dgCategory B).Cocycle S.X₂ S.X₃ :=
  ⟨Cochain.ofHom S.g, by change δ 0 1 (Cochain.ofHom S.g) = 0; simp⟩

/-- **A degreewise split short complex of cochain complexes is a graded-split short exact
sequence of the differential graded category of complexes.** -/
@[stacks 09P6 "a degreewise split short exact sequence of complexes"]
def gradedSplitOfDegreewiseSplit :
    DGCategory.GradedSplitShortExact (A := dgCategory B) S.X₁ S.X₂ S.X₃ where
  a := cocycleOfSplitF S
  b := cocycleOfSplitG S
  π := gradedRetractionOfSplit S σ
  s := gradedSectionOfSplit S σ
  π_a := by
    refine comp_ofHoms_eq (fun p => S.f.f p) (fun p => (σ p).r) (fun p => 𝟙 _) ?_
    intro p
    have h := (σ p).f_r
    dsimp at h
    exact h
  b_s := by
    refine comp_ofHoms_eq (fun p => (σ p).s) (fun p => S.g.f p) (fun p => 𝟙 _) ?_
    intro p
    have h := (σ p).s_g
    dsimp at h
    exact h
  π_s := by
    refine (comp_ofHoms_eq (fun p => (σ p).s) (fun p => (σ p).r) (fun _ => 0) ?_).trans ?_
    · intro p
      have h := (σ p).s_r
      dsimp at h
      exact h
    · exact Cochain.ofHoms_zero
  a_π_add_s_b := by
    ext p q hpq
    obtain rfl : p = q := by omega
    have h := (σ p).id
    dsimp at h
    rw [Cochain.add_v,
      dgCategory_comp_v (B := B) (show (0 : ℤ) + 0 = 0 from rfl)
        (cocycleOfSplitF S).1 (gradedRetractionOfSplit S σ) p p p (add_zero p) (add_zero p),
      dgCategory_comp_v (B := B) (show (0 : ℤ) + 0 = 0 from rfl)
        (gradedSectionOfSplit S σ) (cocycleOfSplitG S).1 p p p (add_zero p) (add_zero p),
      dgCategory_id_v]
    simp only [cocycleOfSplitF, cocycleOfSplitG, gradedRetractionOfSplit, gradedSectionOfSplit,
      Cochain.ofHoms_v, Cochain.ofHom_v]
    exact h

/-- The retraction of the graded splitting. -/
@[simp] theorem gradedSplitOfDegreewiseSplit_π :
    (gradedSplitOfDegreewiseSplit S σ).π = gradedRetractionOfSplit S σ := rfl

/-- The section of the graded splitting. -/
@[simp] theorem gradedSplitOfDegreewiseSplit_s :
    (gradedSplitOfDegreewiseSplit S σ).s = gradedSectionOfSplit S σ := rfl

/-- The inclusion of the graded splitting. -/
@[simp] theorem gradedSplitOfDegreewiseSplit_a :
    (gradedSplitOfDegreewiseSplit S σ).a = cocycleOfSplitF S := rfl

/-- The surjection of the graded splitting. -/
@[simp] theorem gradedSplitOfDegreewiseSplit_b :
    (gradedSplitOfDegreewiseSplit S σ).b = cocycleOfSplitG S := rfl

/-- **The connecting morphism of a degreewise split sequence of complexes is Mathlib's
`CochainComplex.cocycleOfDegreewiseSplit`.** The Hom differential of `s` is the graded
commutator `s ≫ d - d ≫ s`, and its second term dies against `π` because `π ∘ s = 0`, leaving
`(σ p).s ≫ d ≫ (σ q).r`. -/
@[stacks 09P6 "the connecting morphism of a degreewise split sequence of complexes"]
theorem connectingHom_gradedSplitOfDegreewiseSplit :
    DGCategory.GradedSplitShortExact.connectingHom (gradedSplitOfDegreewiseSplit S σ) =
      (cocycleOfDegreewiseSplit S σ).1 := by
  ext p q hpq
  obtain rfl : q = p + 1 := by omega
  have hsr : (σ (p + 1)).s ≫ (σ (p + 1)).r = 0 := (σ (p + 1)).s_r
  rw [DGCategory.GradedSplitShortExact.connectingHom, gradedSplitOfDegreewiseSplit_π,
    gradedSplitOfDegreewiseSplit_s,
    dgCategory_comp_v (B := B) (show (0 : ℤ) + (0 + 1) = 1 from rfl)
      (gradedRetractionOfSplit S σ)
      ((dgCategory B).d (gradedSectionOfSplit S σ)) p (p + 1) (p + 1) rfl (add_zero _),
    dgCategory_d_v (B := B) (gradedSectionOfSplit S σ) p (p + 1) (by omega) p (p + 1)
      (by omega) rfl]
  simp only [gradedRetractionOfSplit, gradedSectionOfSplit, Cochain.ofHoms_v,
    cocycleOfDegreewiseSplit, Cocycle.mk_coe, Cochain.mk_v, Preadditive.add_comp,
    Category.assoc, Int.reduceAdd, Int.negOnePow_one, Units.neg_smul,
    one_smul, Preadditive.neg_comp]
  rw [hsr, comp_zero, neg_zero, add_zero]

end

end CochainComplex
