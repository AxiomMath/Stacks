module

public import StacksFrontier.Algebra.DGA.Abelian
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.KFlat.Basic
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Iso
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.FreeResolution.FreeDGA
import all StacksFrontier.Algebra.DGA.FreeResolution.FreeDGA

/-!
# Cell stages of the free graded resolution

The free graded resolution of a differential graded algebra `B` is built as a sequence of cell
stages: free differential graded algebras mapping to `B`, each obtained from the previous one
by a free extension adjoining generators that kill cycles. This file constructs the free
extensions, the cell stages and their transition maps, and the directed colimit of the stages
with its differential, its grading and the maps from the stages to the graded pieces.

## References

* [Stacks Project, Tag 0BZ7](https://stacks.math.columbia.edu/tag/0BZ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits


universe u v

namespace Stacks.DGA

variable {R : Type u} [CommRing R]

set_option linter.checkUnivs false in
private abbrev freeExtensionAlphabet (S T : Type (max u v)) : Type (max u v) :=
  Sum.{max u v, max u v} S T

private def freeExtensionDegree {S T : Type (max u v)}
    (degreeS : S → ℤ) (degreeT : T → ℤ) : freeExtensionAlphabet.{u, v} S T → ℤ
  | .inl s => degreeS s
  | .inr t => degreeT t

private noncomputable def freeExtensionDifferential {S T : Type (max u v)}
    (δS : S → AddMonoidAlgebra R (Additive (FreeMonoid S)))
    (x : T → AddMonoidAlgebra R (Additive (FreeMonoid S))) :
    freeExtensionAlphabet.{u, v} S T →
      AddMonoidAlgebra R (Additive (FreeMonoid (freeExtensionAlphabet.{u, v} S T)))
  | .inl s => freeWordMap (R := R)
      (Sum.inl : S → freeExtensionAlphabet.{u, v} S T) (δS s)
  | .inr t => freeWordMap (R := R)
      (Sum.inl : S → freeExtensionAlphabet.{u, v} S T) (x t)

private theorem freeExtensionDifferential_mem_grade {S T : Type (max u v)}
    (degreeS : S → ℤ) (degreeT : T → ℤ)
    (δS : S → AddMonoidAlgebra R (Additive (FreeMonoid S)))
    (x : T → AddMonoidAlgebra R (Additive (FreeMonoid S)))
    (hδS : ∀ s, δS s ∈ AddMonoidAlgebra.gradeBy R (freeWordDegree degreeS)
      (degreeS s + 1))
    (hx : ∀ t, x t ∈ AddMonoidAlgebra.gradeBy R (freeWordDegree degreeS)
      (degreeT t + 1))
    (q : freeExtensionAlphabet.{u, v} S T) :
    freeExtensionDifferential.{u, v} (R := R) (S := S) (T := T) δS x q ∈
      AddMonoidAlgebra.gradeBy R
        (freeWordDegree (freeExtensionDegree.{u, v} (S := S) (T := T) degreeS degreeT))
        (freeExtensionDegree.{u, v} (S := S) (T := T) degreeS degreeT q + 1) := by
  cases q with
  | inl s =>
      exact freeWordMap_mem_grade (R := R)
        (Sum.inl : S → freeExtensionAlphabet.{u, v} S T) degreeS
        (freeExtensionDegree.{u, v} (S := S) (T := T) degreeS degreeT)
        (fun _ => rfl) _ _ (hδS s)
  | inr t =>
      exact freeWordMap_mem_grade (R := R)
        (Sum.inl : S → freeExtensionAlphabet.{u, v} S T) degreeS
        (freeExtensionDegree.{u, v} (S := S) (T := T) degreeS degreeT)
        (fun _ => rfl) _ _ (hx t)

/-- The inclusion of the old generators commutes with the differentials. -/
private theorem freeExtension_commutes_d {S T : Type (max u v)}
    (degreeS : S → ℤ) (degreeT : T → ℤ)
    (δS : S → AddMonoidAlgebra R (Additive (FreeMonoid S)))
    (x : T → AddMonoidAlgebra R (Additive (FreeMonoid S)))
    (a : AddMonoidAlgebra R (Additive (FreeMonoid S))) :
    freeWordDifferentialLinear (freeExtensionDegree.{u, v} (S := S) (T := T) degreeS degreeT)
      (freeExtensionDifferential.{u, v} (R := R) (S := S) (T := T) δS x)
      (freeWordMap (R := R) (Sum.inl : S → freeExtensionAlphabet.{u, v} S T) a) =
    freeWordMap (R := R) (Sum.inl : S → freeExtensionAlphabet.{u, v} S T)
      (freeWordDifferentialLinear degreeS δS a) :=
  freeWordMap_commutes_d (Sum.inl : S → freeExtensionAlphabet.{u, v} S T) degreeS
    (freeExtensionDegree.{u, v} (S := S) (T := T) degreeS degreeT) δS
    (freeExtensionDifferential.{u, v} (R := R) (S := S) (T := T) δS x)
    (fun _ => rfl) (fun _ => rfl) a

private theorem freeExtensionDifferential_cycle {S T : Type (max u v)}
    (degreeS : S → ℤ) (degreeT : T → ℤ)
    (δS : S → AddMonoidAlgebra R (Additive (FreeMonoid S)))
    (x : T → AddMonoidAlgebra R (Additive (FreeMonoid S)))
    (hδScycle : ∀ s, freeWordDifferentialLinear degreeS δS (δS s) = 0)
    (hxcycle : ∀ t, freeWordDifferentialLinear degreeS δS (x t) = 0)
    (q : freeExtensionAlphabet.{u, v} S T) :
    freeWordDifferentialLinear (freeExtensionDegree.{u, v} (S := S) (T := T) degreeS degreeT)
      (freeExtensionDifferential.{u, v} (R := R) (S := S) (T := T) δS x)
      (freeExtensionDifferential.{u, v} (R := R) (S := S) (T := T) δS x q) = 0 := by
  cases q with
  | inl s =>
      change freeWordDifferentialLinear _ _
        (freeWordMap (R := R) (Sum.inl : S → freeExtensionAlphabet.{u, v} S T)
          (δS s)) = 0
      rw [freeExtension_commutes_d, hδScycle, map_zero]
  | inr t =>
      change freeWordDifferentialLinear _ _
        (freeWordMap (R := R) (Sum.inl : S → freeExtensionAlphabet.{u, v} S T)
          (x t)) = 0
      rw [freeExtension_commutes_d, hxcycle, map_zero]

private noncomputable abbrev freeExtension {S T : Type (max u v)}
    (degreeS : S → ℤ) (degreeT : T → ℤ)
    (δS : S → AddMonoidAlgebra R (Additive (FreeMonoid S)))
    (x : T → AddMonoidAlgebra R (Additive (FreeMonoid S)))
    (hδS : ∀ s, δS s ∈ AddMonoidAlgebra.gradeBy R (freeWordDegree degreeS)
      (degreeS s + 1))
    (hδScycle : ∀ s, freeWordDifferentialLinear degreeS δS (δS s) = 0)
    (hx : ∀ t, x t ∈ AddMonoidAlgebra.gradeBy R (freeWordDegree degreeS)
      (degreeT t + 1))
    (hxcycle : ∀ t, freeWordDifferentialLinear degreeS δS (x t) = 0) :
    DifferentialGradedAlgebra.{u, max u v} R :=
  freeDGA (R := R) (freeExtensionDegree.{u, v} (S := S) (T := T) degreeS degreeT)
    (freeExtensionDifferential.{u, v} (R := R) (S := S) (T := T) δS x)
    (freeExtensionDifferential_mem_grade degreeS degreeT δS x hδS hx)
    (freeExtensionDifferential_cycle degreeS degreeT δS x hδScycle hxcycle)

private theorem freeExtension_new_generator_boundary {S T : Type (max u v)}
    (degreeS : S → ℤ) (degreeT : T → ℤ)
    (δS : S → AddMonoidAlgebra R (Additive (FreeMonoid S)))
    (x : T → AddMonoidAlgebra R (Additive (FreeMonoid S)))
    (t : T) :
    freeWordDifferentialLinear
      (freeExtensionDegree.{u, v} degreeS degreeT)
      (freeExtensionDifferential.{u, v} (R := R) δS x)
      (monoidWord [Sum.inr t]) =
      freeWordMap (R := R) (Sum.inl : S → freeExtensionAlphabet.{u, v} S T) (x t) := by
  rw [freeWordDifferentialLinear_monoidWord]
  simp only [monoidWordDifferential, freeExtensionDifferential, monoidWord, FreeMonoid.ofList_nil,
    ofMul_one, FreeMonoid.ofList_cons, mul_one, mul_zero, smul_zero, add_zero]
  rw [← AddMonoidAlgebra.one_def, mul_one]

private theorem freeExtension_inclusion_isDGAMorphism {S T : Type (max u v)}
    (degreeS : S → ℤ) (degreeT : T → ℤ)
    (δS : S → AddMonoidAlgebra R (Additive (FreeMonoid S)))
    (x : T → AddMonoidAlgebra R (Additive (FreeMonoid S)))
    (hδS : ∀ s, δS s ∈ AddMonoidAlgebra.gradeBy R (freeWordDegree degreeS)
      (degreeS s + 1))
    (hδScycle : ∀ s, freeWordDifferentialLinear degreeS δS (δS s) = 0)
    (hx : ∀ t, x t ∈ AddMonoidAlgebra.gradeBy R (freeWordDegree degreeS)
      (degreeT t + 1))
    (hxcycle : ∀ t, freeWordDifferentialLinear degreeS δS (x t) = 0) :
    IsDGAMorphism (freeDGA (R := R) degreeS δS hδS hδScycle)
      (freeExtension (R := R) degreeS degreeT δS x hδS hδScycle hx hxcycle)
      (freeWordMap (R := R) (Sum.inl : S → freeExtensionAlphabet.{u, v} S T)) := by
  exact ⟨freeWordMap_mem_grade (R := R) (Sum.inl : S → freeExtensionAlphabet.{u, v} S T) degreeS
      (freeExtensionDegree.{u, v} (S := S) (T := T) degreeS degreeT) fun _ => rfl,
    fun a => (freeExtension_commutes_d degreeS degreeT δS x a).symm⟩

/-- Evaluating at `Sum.elim b bT` after including the old generators is evaluating at `b`. -/
private theorem freeZeroDGA_map_elim_inl {S T : Type (max u v)}
    (B : DifferentialGradedAlgebra.{u, max u v} R) (degreeS : S → ℤ) (degreeT : T → ℤ)
    (b : S → B.A) (bT : T → B.A) (a : AddMonoidAlgebra R (Additive (FreeMonoid S))) :
    freeZeroDGA_map B (freeExtensionDegree.{u, v} degreeS degreeT) (Sum.elim b bT)
      (freeWordMap (R := R) (Sum.inl : S → freeExtensionAlphabet.{u, v} S T) a) =
      freeZeroDGA_map B degreeS b a :=
  freeZeroDGA_map_comp_freeWordMap B Sum.inl degreeS
    (freeExtensionDegree.{u, v} degreeS degreeT) b (Sum.elim b bT) (fun _ => rfl) a

private theorem exists_kernel_cells
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    {S : Type (max u v)} (degree : S → ℤ)
    (δ : S → AddMonoidAlgebra R (Additive (FreeMonoid S)))
    (b : S → B.A) :
    ∃ (T : Type (max u v)) (degreeT : T → ℤ)
      (boundary : T → AddMonoidAlgebra R (Additive (FreeMonoid S)))
      (primitive : T → B.A),
      (∀ t, boundary t ∈ AddMonoidAlgebra.gradeBy R (freeWordDegree degree)
        (degreeT t + 1)) ∧
      (∀ t, freeWordDifferentialLinear degree δ (boundary t) = 0) ∧
      (∀ t, primitive t ∈ B.grading (degreeT t)) ∧
      (∀ t, freeZeroDGA_map B degree b (boundary t) = B.d (primitive t)) ∧
      (∀ (n : ℤ) (a : AddMonoidAlgebra R (Additive (FreeMonoid S))),
        a ∈ AddMonoidAlgebra.gradeBy R (freeWordDegree degree) n →
        freeWordDifferentialLinear degree δ a = 0 →
        (∃ y : B.A, y ∈ B.grading (n - 1) ∧
          B.d y = freeZeroDGA_map B degree b a) →
        ∃ t : T, degreeT t = n - 1 ∧ boundary t = a) := by
  let T : Type (max u v) :=
    Σ n : ℤ, {p : AddMonoidAlgebra R (Additive (FreeMonoid S)) × B.A //
      p.1 ∈ AddMonoidAlgebra.gradeBy R (freeWordDegree degree) n ∧
      freeWordDifferentialLinear degree δ p.1 = 0 ∧
      p.2 ∈ B.grading (n - 1) ∧
      B.d p.2 = freeZeroDGA_map B degree b p.1}
  let degreeT : T → ℤ := fun t => t.1 - 1
  let boundary : T → AddMonoidAlgebra R (Additive (FreeMonoid S)) :=
    fun t => t.2.1.1
  let primitive : T → B.A := fun t => t.2.1.2
  refine ⟨T, degreeT, boundary, primitive, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    simpa only [degreeT, sub_add_cancel] using t.2.2.1
  · intro t
    exact t.2.2.2.1
  · intro t
    exact t.2.2.2.2.1
  · intro t
    exact (t.2.2.2.2.2).symm
  · intro n a ha hda hbound
    obtain ⟨y, hy, hdy⟩ := hbound
    refine ⟨⟨n, ⟨(a, y), ha, hda, hy, hdy⟩⟩, rfl, rfl⟩

theorem isDGAMorphism_comp
    {A B C : DifferentialGradedAlgebra.{u, max u v} R}
    (f : A.A →ₐ[R] B.A) (g : B.A →ₐ[R] C.A)
    (hf : IsDGAMorphism A B f) (hg : IsDGAMorphism B C g) :
    IsDGAMorphism A C (g.comp f) := by
  constructor
  · intro n a ha
    exact hg.1 n (f a) (hf.1 n a ha)
  · intro a
    change g (f (A.d a)) = C.d (g (f a))
    rw [hf.2, hg.2]

theorem isDGAMorphism_id
    (A : DifferentialGradedAlgebra.{u, max u v} R) :
    IsDGAMorphism A A (AlgHom.id R A.A) := by
  constructor
  · intro n a ha
    exact ha
  · intro a
    rfl

private structure CellStage (B : DifferentialGradedAlgebra.{u, max u v} R) where
  S : Type (max u v)
  degree : S → ℤ
  δ : S → AddMonoidAlgebra R (Additive (FreeMonoid S))
  δ_mem : ∀ s, δ s ∈ AddMonoidAlgebra.gradeBy R (freeWordDegree degree)
    (degree s + 1)
  δ_cycle : ∀ s, freeWordDifferentialLinear degree δ (δ s) = 0
  b : S → B.A
  b_mem : ∀ s, b s ∈ B.grading (degree s)
  b_d : ∀ s, freeZeroDGA_map B degree b (δ s) = B.d (b s)

private noncomputable abbrev CellStage.dga
    {B : DifferentialGradedAlgebra.{u, max u v} R} (P : CellStage B) :
    DifferentialGradedAlgebra.{u, max u v} R :=
  freeDGA (R := R) P.degree P.δ P.δ_mem P.δ_cycle

private noncomputable abbrev CellStage.toTarget
    {B : DifferentialGradedAlgebra.{u, max u v} R} (P : CellStage B) :
    P.dga.A →ₐ[R] B.A :=
  freeZeroDGA_map B P.degree P.b

private theorem CellStage.toTarget_isDGAMorphism
    {B : DifferentialGradedAlgebra.{u, max u v} R} (P : CellStage B) :
    IsDGAMorphism P.dga B P.toTarget :=
  freeDGA_map_isDGAMorphism B P.degree P.δ P.δ_mem P.δ_cycle
    P.b P.b_mem P.b_d

private noncomputable abbrev CellStage.nextAlphabet
    (B : DifferentialGradedAlgebra.{u, max u v} R) (P : CellStage B) :
    Type (max u v) :=
  Classical.choose (exists_kernel_cells B P.degree P.δ P.b)

private noncomputable def CellStage.next
    (B : DifferentialGradedAlgebra.{u, max u v} R) (P : CellStage B) :
    CellStage B := by
  classical
  let T := CellStage.nextAlphabet B P
  let c₀ := Classical.choose_spec (exists_kernel_cells B P.degree P.δ P.b)
  let degreeT := Classical.choose c₀
  let c₁ := Classical.choose_spec c₀
  let x := Classical.choose c₁
  let c₂ := Classical.choose_spec c₁
  let bT := Classical.choose c₂
  let c₃ := Classical.choose_spec c₂
  have hx := c₃.1
  have hxcycle := c₃.2.1
  have hbT := c₃.2.2.1
  have hdbT := c₃.2.2.2.1
  refine {
    S := freeExtensionAlphabet.{u, v} P.S T
    degree := freeExtensionDegree.{u, v} P.degree degreeT
    δ := freeExtensionDifferential.{u, v} (R := R) P.δ x
    δ_mem := freeExtensionDifferential_mem_grade P.degree degreeT P.δ x P.δ_mem hx
    δ_cycle := freeExtensionDifferential_cycle P.degree degreeT P.δ x
      P.δ_cycle hxcycle
    b := Sum.elim P.b bT
    b_mem := ?_
    b_d := ?_ }
  · intro q
    cases q with
    | inl s => exact P.b_mem s
    | inr t => exact hbT t
  · intro q
    cases q with
    | inl s => exact (freeZeroDGA_map_elim_inl B P.degree degreeT P.b bT _).trans (P.b_d s)
    | inr t => exact (freeZeroDGA_map_elim_inl B P.degree degreeT P.b bT _).trans (hdbT t)

private noncomputable def CellStage.inclusion
    (B : DifferentialGradedAlgebra.{u, max u v} R) (P : CellStage B) :
    P.dga.A →ₐ[R] (CellStage.next B P).dga.A :=
  freeWordMap (R := R)
    (Sum.inl : P.S → freeExtensionAlphabet.{u, v} P.S (CellStage.nextAlphabet B P))

private theorem CellStage.inclusion_isDGAMorphism
    (B : DifferentialGradedAlgebra.{u, max u v} R) (P : CellStage B) :
    IsDGAMorphism P.dga (CellStage.next B P).dga (CellStage.inclusion B P) := by
  classical
  let c₀ := Classical.choose_spec (exists_kernel_cells B P.degree P.δ P.b)
  let c₁ := Classical.choose_spec c₀
  let c₂ := Classical.choose_spec c₁
  let c₃ := Classical.choose_spec c₂
  exact freeExtension_inclusion_isDGAMorphism P.degree _ P.δ _ P.δ_mem P.δ_cycle c₃.1 c₃.2.1

private theorem CellStage.toTarget_inclusion
    (B : DifferentialGradedAlgebra.{u, max u v} R) (P : CellStage B)
    (a : P.dga.A) :
    (CellStage.next B P).toTarget (CellStage.inclusion B P a) =
      P.toTarget a := by
  exact freeZeroDGA_map_elim_inl B _ _ _ _ a

private theorem CellStage.next_kills_kernel
    (B : DifferentialGradedAlgebra.{u, max u v} R) (P : CellStage B)
    (n : ℤ) (a : P.dga.A)
    (ha : a ∈ P.dga.grading n) (hda : P.dga.d a = 0)
    (hbound : ∃ y : B.A, y ∈ B.grading (n - 1) ∧
      B.d y = P.toTarget a) :
    ∃ z : (CellStage.next B P).dga.A,
      z ∈ (CellStage.next B P).dga.grading (n - 1) ∧
      (CellStage.next B P).dga.d z = CellStage.inclusion B P a := by
  classical
  let T := CellStage.nextAlphabet B P
  let c₀ := Classical.choose_spec (exists_kernel_cells B P.degree P.δ P.b)
  let degreeT := Classical.choose c₀
  let c₁ := Classical.choose_spec c₀
  let x := Classical.choose c₁
  let c₂ := Classical.choose_spec c₁
  let c₃ := Classical.choose_spec c₂
  obtain ⟨t, ht, hxt⟩ := c₃.2.2.2.2 n a ha hda hbound
  let z : (CellStage.next B P).dga.A := monoidWord [Sum.inr t]
  refine ⟨z, ?_, ?_⟩
  · change z ∈ AddMonoidAlgebra.gradeBy R
      (freeWordDegree (freeExtensionDegree.{u, v} P.degree degreeT)) (n - 1)
    have hs : ([Sum.inr t].map
        (freeExtensionDegree.{u, v} P.degree degreeT)).sum = n - 1 := by
      simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, freeExtensionDegree] using ht
    exact hs ▸ monoidWord_mem_grade (R := R)
      (freeExtensionDegree.{u, v} P.degree degreeT) [Sum.inr t]
  · change freeWordDifferentialLinear
      (freeExtensionDegree.{u, v} P.degree degreeT)
      (freeExtensionDifferential.{u, v} (R := R) P.δ x) z =
      freeWordMap (R := R) (Sum.inl : P.S → freeExtensionAlphabet.{u, v} P.S T) a
    have hb := freeExtension_new_generator_boundary P.degree degreeT P.δ x t
    change x t = a at hxt
    rw [hxt] at hb
    exact hb

private noncomputable def CellStage.initial
    (B : DifferentialGradedAlgebra.{u, max u v} R) : CellStage B := by
  let S : Type (max u v) :=
    Σ n : ℤ, {y : B.A // y ∈ B.grading n ∧ B.d y = 0}
  refine {
    S := S
    degree := fun s => s.1
    δ := fun _ => 0
    δ_mem := ?_
    δ_cycle := ?_
    b := fun s => s.2.1
    b_mem := ?_
    b_d := ?_ }
  · intro s
    exact Submodule.zero_mem _
  · intro s
    exact map_zero _
  · intro s
    exact s.2.2.1
  · intro s
    simpa only [map_zero] using s.2.2.2.symm

private noncomputable def CellStage.at
    (B : DifferentialGradedAlgebra.{u, max u v} R) : ℕ → CellStage B
  | 0 => CellStage.initial B
  | n + 1 => CellStage.next B (CellStage.at B n)

/-- `CellStage.next_kills_kernel` restated at the stage `CellStage.at B (j + 1)`, which is
definitionally `CellStage.next B (CellStage.at B j)`; the two spellings are interchangeable
for the elaborator but not for `rw`. -/
private theorem CellStage.next_kills_kernel_at
    (B : DifferentialGradedAlgebra.{u, max u v} R) (j : ℕ)
    (n : ℤ) (a : (CellStage.at B j).dga.A)
    (ha : a ∈ (CellStage.at B j).dga.grading n)
    (hda : (CellStage.at B j).dga.d a = 0)
    (hbound : ∃ y : B.A, y ∈ B.grading (n - 1) ∧
      B.d y = (CellStage.at B j).toTarget a) :
    ∃ z : (CellStage.at B (j + 1)).dga.A,
      z ∈ (CellStage.at B (j + 1)).dga.grading (n - 1) ∧
      (CellStage.at B (j + 1)).dga.d z =
        CellStage.inclusion B (CellStage.at B j) a :=
  CellStage.next_kills_kernel B (CellStage.at B j) n a ha hda hbound

private noncomputable def CellStage.transition
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (i j : ℕ) (hij : i ≤ j) :
    (CellStage.at B i).dga.A →ₐ[R] (CellStage.at B j).dga.A :=
  Nat.leRec
    (motive := fun j _ => (CellStage.at B i).dga.A →ₐ[R] (CellStage.at B j).dga.A)
    (AlgHom.id R _)
    (fun {k} _ f => (CellStage.inclusion B (CellStage.at B k)).comp f) hij

private theorem CellStage.transition_step
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (i j : ℕ) (hij : i ≤ j) :
    CellStage.transition B i (j + 1) (Nat.le_succ_of_le hij) =
      (CellStage.inclusion B (CellStage.at B j)).comp
        (CellStage.transition B i j hij) :=
  Nat.leRec_succ _ _ hij

private theorem CellStage.transition_self
    (B : DifferentialGradedAlgebra.{u, max u v} R) (i : ℕ) :
    CellStage.transition B i i (le_refl i) = AlgHom.id R _ :=
  Nat.leRec_self _ _

private theorem CellStage.transition_isDGAMorphism
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (i j : ℕ) (hij : i ≤ j) :
    IsDGAMorphism (CellStage.at B i).dga (CellStage.at B j).dga
      (CellStage.transition B i j hij) := by
  induction j, hij using Nat.le_induction with
  | base =>
      rw [CellStage.transition_self]
      exact isDGAMorphism_id _
  | succ j h ih =>
      rw [CellStage.transition_step B i j h]
      exact isDGAMorphism_comp _ _ ih
        (CellStage.inclusion_isDGAMorphism B (CellStage.at B j))

private theorem CellStage.transition_toTarget
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (i j : ℕ) (hij : i ≤ j) (a : (CellStage.at B i).dga.A) :
    (CellStage.at B j).toTarget (CellStage.transition B i j hij a) =
      (CellStage.at B i).toTarget a := by
  induction j, hij using Nat.le_induction with
  | base =>
      rw [CellStage.transition_self]
      rfl
  | succ j h ih =>
      rw [CellStage.transition_step B i j h]
      change (CellStage.next B (CellStage.at B j)).toTarget
        (CellStage.inclusion B (CellStage.at B j)
          (CellStage.transition B i j h a)) = _
      rw [CellStage.toTarget_inclusion, ih]

private theorem CellStage.transition_comp
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) :
    (CellStage.transition B j k hjk).comp
      (CellStage.transition B i j hij) =
      CellStage.transition B i k (hij.trans hjk) := by
  induction k, hjk using Nat.le_induction with
  | base =>
      rw [CellStage.transition_self]
      rfl
  | succ k h ih =>
      rw [CellStage.transition_step B j k h,
        CellStage.transition_step B i k (hij.trans h), ← ih]
      ext a
      rfl

private theorem CellStage.transition_injective
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (i j : ℕ) (hij : i ≤ j) :
    Function.Injective (CellStage.transition B i j hij) := by
  induction j, hij using Nat.le_induction with
  | base =>
      rw [CellStage.transition_self]
      exact Function.injective_id
  | succ j h ih =>
      rw [CellStage.transition_step B i j h]
      exact (freeWordMap_injective (R := R) Sum.inl Sum.inl_injective).comp ih

private theorem CellStage.directedSystem
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    DirectedSystem (fun i : ℕ => (CellStage.at B i).dga.A)
      (fun _ _ h => CellStage.transition B _ _ h) := by
  constructor
  · intro i x
    rw [CellStage.transition_self]
    rfl
  · intro k j i hij hjk x
    exact congrArg (fun f => f x)
      (CellStage.transition_comp B i j k hij hjk)

private theorem CellStage.limitOf_injective
    (B : DifferentialGradedAlgebra.{u, max u v} R) (i : ℕ) :
    letI := CellStage.directedSystem B
    Function.Injective (DirectLimit.Module.of R ℕ
      (fun j : ℕ => (CellStage.at B j).dga.A)
      (fun j k h => CellStage.transition B j k h) i) := by
  let := CellStage.directedSystem B
  intro a b hab
  have hzero : (⟦⟨i, a - b⟩⟧ :
      DirectLimit (fun j : ℕ => (CellStage.at B j).dga.A)
        (fun j k h => CellStage.transition B j k h)) = 0 := by
    change (DirectLimit.Module.of R ℕ
      (fun j : ℕ => (CellStage.at B j).dga.A)
      (fun j k h => CellStage.transition B j k h) i) (a - b) = 0
    rw [map_sub, hab, sub_self]
  obtain ⟨j, hij, hj⟩ := (DirectLimit.exists_eq_zero
    (f := fun j k h => CellStage.transition B j k h) ⟨i, a - b⟩).mp hzero
  apply sub_eq_zero.mp
  apply CellStage.transition_injective B i j hij
  simpa using hj

private noncomputable def CellStage.limitToTarget
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    (letI := CellStage.directedSystem B
     DirectLimit (fun i : ℕ => (CellStage.at B i).dga.A)
       (fun _ _ h => CellStage.transition B _ _ h)) →ₐ[R] B.A := by
  letI := CellStage.directedSystem B
  exact DirectLimit.Algebra.lift
    (fun i : ℕ => (CellStage.at B i).dga.A)
    (fun _ _ h => CellStage.transition B _ _ h)
    B.A (fun i => (CellStage.at B i).toTarget)
    (fun i j h x => CellStage.transition_toTarget B i j h x)

private noncomputable def CellStage.limitDifferential
    (B : DifferentialGradedAlgebra.{u, max u v} R) := by
  letI := CellStage.directedSystem B
  let G : ℕ → Type (max u v) := fun i => (CellStage.at B i).dga.A
  let f : ∀ i j : ℕ, i ≤ j → G i →ₐ[R] G j :=
    fun i j h => CellStage.transition B i j h
  exact DirectLimit.Module.lift R ℕ G f
    (fun i => (DirectLimit.Module.of R ℕ G f i).comp (CellStage.at B i).dga.d)
    (by
      intro i j h x
      change (DirectLimit.Module.of R ℕ G f j)
        ((CellStage.at B j).dga.d (CellStage.transition B i j h x)) =
        (DirectLimit.Module.of R ℕ G f i) ((CellStage.at B i).dga.d x)
      rw [← (CellStage.transition_isDGAMorphism B i j h).2 x]
      exact DirectLimit.Module.of_f (hij := h))

private theorem CellStage.limitDifferential_of
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (i : ℕ) (x : (CellStage.at B i).dga.A) :
    letI := CellStage.directedSystem B
    CellStage.limitDifferential B
      (DirectLimit.Module.of R ℕ
        (fun i => (CellStage.at B i).dga.A)
        (fun i j h => CellStage.transition B i j h) i x) =
      DirectLimit.Module.of R ℕ
        (fun i => (CellStage.at B i).dga.A)
        (fun i j h => CellStage.transition B i j h) i
        ((CellStage.at B i).dga.d x) := by
  let := CellStage.directedSystem B
  simp only [CellStage.limitDifferential, DirectLimit.Module.lift_of,
    LinearMap.comp_apply]

private theorem CellStage.limitDifferential_sq_zero
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    letI := CellStage.directedSystem B
    (CellStage.limitDifferential B) ∘ₗ (CellStage.limitDifferential B) = 0 := by
  let := CellStage.directedSystem B
  apply LinearMap.ext
  intro z
  induction z using DirectLimit.induction with
  | _ i x =>
      change (CellStage.limitDifferential B) ((CellStage.limitDifferential B)
        (DirectLimit.Module.of R ℕ
          (fun i => (CellStage.at B i).dga.A)
          (fun i j h => CellStage.transition B i j h) i x)) = 0
      rw [CellStage.limitDifferential_of, CellStage.limitDifferential_of]
      have hs := LinearMap.congr_fun (CellStage.at B i).dga.d_comp_d x
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hs
      rw [hs, map_zero]

private theorem CellStage.limitToTarget_commutes_d
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    letI := CellStage.directedSystem B
    ∀ z : DirectLimit (fun i : ℕ => (CellStage.at B i).dga.A)
      (fun _ _ h => CellStage.transition B _ _ h),
      CellStage.limitToTarget B (CellStage.limitDifferential B z) =
        B.d (CellStage.limitToTarget B z) := by
  let := CellStage.directedSystem B
  intro z
  induction z using DirectLimit.induction with
  | _ i x =>
      change CellStage.limitToTarget B
        (CellStage.limitDifferential B
          (DirectLimit.Module.of R ℕ
            (fun i => (CellStage.at B i).dga.A)
            (fun i j h => CellStage.transition B i j h) i x)) =
        B.d (CellStage.limitToTarget B
          (DirectLimit.Algebra.of
            (fun i : ℕ => (CellStage.at B i).dga.A)
            (fun i j h => CellStage.transition B i j h) i x))
      rw [CellStage.limitDifferential_of]
      simp only [CellStage.limitToTarget, DirectLimit.Algebra.lift_of]
      exact (CellStage.at B i).toTarget_isDGAMorphism.2 x

private noncomputable def CellStage.limitGrading
    (B : DifferentialGradedAlgebra.{u, max u v} R) (n : ℤ) :
    letI := CellStage.directedSystem B
    Submodule R (DirectLimit (fun i : ℕ => (CellStage.at B i).dga.A)
      (fun _ _ h => CellStage.transition B _ _ h)) := by
  letI := CellStage.directedSystem B
  exact Submodule.span R
    {z | ∃ (i : ℕ) (x : (CellStage.at B i).dga.A),
      x ∈ (CellStage.at B i).dga.grading n ∧
      DirectLimit.Module.of R ℕ
        (fun i => (CellStage.at B i).dga.A)
        (fun i j h => CellStage.transition B i j h) i x = z}

private theorem CellStage.limitGrading_of_mem
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (n : ℤ) (i : ℕ) (x : (CellStage.at B i).dga.A)
    (hx : x ∈ (CellStage.at B i).dga.grading n) :
    letI := CellStage.directedSystem B
    DirectLimit.Module.of R ℕ
      (fun i => (CellStage.at B i).dga.A)
      (fun i j h => CellStage.transition B i j h) i x ∈
      CellStage.limitGrading B n := by
  let := CellStage.directedSystem B
  exact Submodule.subset_span ⟨i, x, hx, rfl⟩

private theorem CellStage.limitGrading_exists_of
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (n : ℤ) (z : letI := CellStage.directedSystem B
      DirectLimit (fun i : ℕ => (CellStage.at B i).dga.A)
        (fun _ _ h => CellStage.transition B _ _ h))
    (hz : z ∈ CellStage.limitGrading B n) :
    letI := CellStage.directedSystem B
    ∃ (i : ℕ) (x : (CellStage.at B i).dga.A),
      x ∈ (CellStage.at B i).dga.grading n ∧
        DirectLimit.Module.of R ℕ
          (fun i : ℕ => (CellStage.at B i).dga.A)
          (fun i j h => CellStage.transition B i j h) i x = z := by
  let := CellStage.directedSystem B
  unfold CellStage.limitGrading at hz
  induction hz using Submodule.span_induction with
  | mem z h => exact h
  | zero =>
      exact ⟨0, 0, (CellStage.at B 0).dga.grading n |>.zero_mem, map_zero _⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨i, a, ha, rfl⟩ := ihx
      obtain ⟨j, b, hb, rfl⟩ := ihy
      let k := max i j
      have hik : i ≤ k := le_max_left i j
      have hjk : j ≤ k := le_max_right i j
      let a' := CellStage.transition B i k hik a
      let b' := CellStage.transition B j k hjk b
      refine ⟨k, a' + b', ?_, ?_⟩
      · exact Submodule.add_mem _
          ((CellStage.transition_isDGAMorphism B i k hik).1 n a ha)
          ((CellStage.transition_isDGAMorphism B j k hjk).1 n b hb)
      · rw [map_add, ← DirectLimit.Module.of_f (hij := hik),
          ← DirectLimit.Module.of_f (hij := hjk)]
  | smul r x hx ih =>
      obtain ⟨i, a, ha, rfl⟩ := ih
      exact ⟨i, r • a, Submodule.smul_mem _ r ha, map_smul _ _ _⟩

private noncomputable def CellStage.limitGradingMap
    (B : DifferentialGradedAlgebra.{u, max u v} R) (i : ℕ) (n : ℤ) :
    (CellStage.at B i).dga.grading n →ₗ[R] CellStage.limitGrading B n := by
  letI := CellStage.directedSystem B
  exact ((DirectLimit.Module.of R ℕ
    (fun j : ℕ => (CellStage.at B j).dga.A)
    (fun j k h => CellStage.transition B j k h) i).comp
    ((CellStage.at B i).dga.grading n).subtype).codRestrict _
    (fun x => CellStage.limitGrading_of_mem B n i x.1 x.2)

private noncomputable def CellStage.limitDecomposeStage
    (B : DifferentialGradedAlgebra.{u, max u v} R) (i : ℕ) :
    (CellStage.at B i).dga.A →ₗ[R]
      DirectSum ℤ (fun n : ℤ => ↥(CellStage.limitGrading B n)) := by
  letI := CellStage.directedSystem B
  exact (DirectSum.lmap (fun n => CellStage.limitGradingMap B i n)).comp
    (DirectSum.decomposeLinearEquiv (CellStage.at B i).dga.grading).toLinearMap

private theorem CellStage.limitDecomposeStage_of_mem
    (B : DifferentialGradedAlgebra.{u, max u v} R) (i : ℕ) (n : ℤ)
    (x : (CellStage.at B i).dga.A)
    (hx : x ∈ (CellStage.at B i).dga.grading n) :
    CellStage.limitDecomposeStage B i x =
      DirectSum.lof R ℤ (fun n : ℤ => ↥(CellStage.limitGrading B n)) n
        ⟨_, CellStage.limitGrading_of_mem B n i x hx⟩ := by
  change (DirectSum.lmap (fun n => CellStage.limitGradingMap B i n))
    (DirectSum.decompose (CellStage.at B i).dga.grading x) = _
  rw [DirectSum.decompose_of_mem (CellStage.at B i).dga.grading hx,
    DirectSum.lmap_of]
  rfl

private theorem CellStage.limitDecomposeStage_transition
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (i j : ℕ) (hij : i ≤ j) (x : (CellStage.at B i).dga.A) :
    CellStage.limitDecomposeStage B j (CellStage.transition B i j hij x) =
      CellStage.limitDecomposeStage B i x := by
  let := CellStage.directedSystem B
  induction x using DirectSum.Decomposition.inductionOn
      (CellStage.at B i).dga.grading with
  | zero => simp
  | @homogeneous n x =>
      rw [CellStage.limitDecomposeStage_of_mem B j n _
          ((CellStage.transition_isDGAMorphism B i j hij).1 n x x.property),
        CellStage.limitDecomposeStage_of_mem B i n x x.property]
      congr 1
      apply Subtype.ext
      exact DirectLimit.Module.of_f
        (R := R) (G := fun k : ℕ => (CellStage.at B k).dga.A)
        (f := fun k l h => CellStage.transition B k l h)
        (hij := hij)
  | add x y hx hy =>
      simp only [map_add, hx, hy]

end Stacks.DGA

end
