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
public import StacksFrontier.Algebra.DGA.FreeResolution.CellStage
public import StacksFrontier.Algebra.DGA.FreeResolution.LimitQuasiIso
import all StacksFrontier.Algebra.DGA.FreeResolution.FreeDGA
import all StacksFrontier.Algebra.DGA.FreeResolution.CellStage
import all StacksFrontier.Algebra.DGA.FreeResolution.LimitQuasiIso

/-!
# K-flat free graded resolutions of differential graded algebras

Every differential graded algebra over a commutative ring admits a quasi-isomorphic
differential graded algebra which is K-flat over the base and free as a graded algebra.

## Main results

* `Stacks.DGA.exists_kFlat_freeGraded_resolution` constructs a K-flat, free graded
  differential graded algebra mapping quasi-isomorphically to the given one.

## Implementation notes

The limit of the cell stages is free as a graded algebra on the generators of all stages.
For K-flatness, each cell stage carries a natural-number weight on its generators,
extended additively to words, which strictly decreases under the differential.
Words whose degree plus weight is at most a fixed bound span a bounded above free
subcomplex. These subcomplexes exhaust each stage, so filtered colimits give
K-flatness of the stages and of their limit.

## References

* [Stacks Project, Tag 0BZ7](https://stacks.math.columbia.edu/tag/0BZ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits


universe u v

namespace Stacks.DGA

variable {R : Type u} [CommRing R]

private noncomputable def CellStage.limitFreeInv
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    (letI := CellStage.directedSystem B
     DirectLimit (fun i : ℕ => (CellStage.at B i).dga.A)
       (fun i j h => CellStage.transition B i j h)) →ₐ[R]
      FreeAlgebra R (CellStage.limitAlphabet B) := by
  letI := CellStage.directedSystem B
  exact DirectLimit.Algebra.lift
    (fun i : ℕ => (CellStage.at B i).dga.A)
    (fun i j h => CellStage.transition B i j h)
    (FreeAlgebra R (CellStage.limitAlphabet B))
    (fun i => CellStage.stageFreeMap B i)
    (fun i j h x => CellStage.stageFreeMap_transition B i j h x)

/-- `DirectLimit.Algebra.lift_of` restated for `CellStage.limitFreeInv`, whose definition hides
the `lift` behind a tactic block; the two spellings agree definitionally. -/
private theorem CellStage.limitFreeInv_of
    (B : DifferentialGradedAlgebra.{u, max u v} R) (i : ℕ)
    (x : (CellStage.at B i).dga.A) :
    letI := CellStage.directedSystem B
    CellStage.limitFreeInv B
        (DirectLimit.Algebra.of
          (fun j : ℕ => (CellStage.at B j).dga.A)
          (fun j k h => CellStage.transition B j k h) i x) =
      CellStage.stageFreeMap B i x :=
  rfl

private theorem CellStage.limitLetter_stage
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (i : ℕ) (s : (CellStage.at B i).S) :
    CellStage.limitLetter B (CellStage.stageLetter B i s) =
      (letI := CellStage.directedSystem B
       DirectLimit.Algebra.of
         (fun j : ℕ => (CellStage.at B j).dga.A)
         (fun j k h => CellStage.transition B j k h) i (monoidWord [s])) := by
  let := CellStage.directedSystem B
  induction i with
  | zero => rfl
  | succ i ih =>
      cases s with
      | inl s =>
          rw [CellStage.stageLetter_inclusion, ih]
          calc
            DirectLimit.Algebra.of
                (fun j : ℕ => (CellStage.at B j).dga.A)
                (fun j k h => CellStage.transition B j k h) i (monoidWord [s]) =
              DirectLimit.Algebra.of
                (fun j : ℕ => (CellStage.at B j).dga.A)
                (fun j k h => CellStage.transition B j k h) (i + 1)
                (CellStage.transition B i (i + 1) (Nat.le_succ i)
                  (monoidWord [s])) :=
              (DirectLimit.Algebra.of_f
                (G := fun j : ℕ => (CellStage.at B j).dga.A)
                (f := fun j k h => CellStage.transition B j k h)
                (Nat.le_succ i) (monoidWord [s])).symm
            _ = DirectLimit.Algebra.of
                (fun j : ℕ => (CellStage.at B j).dga.A)
                (fun j k h => CellStage.transition B j k h) (i + 1)
                (monoidWord [Sum.inl s]) := by
              congr 1
              rw [CellStage.transition_step B i i le_rfl,
                CellStage.transition_self]
              exact freeWordMap_monoidWord (R := R) Sum.inl [s]
      | inr t => rfl

private theorem CellStage.limitFreeMap_stage_word
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (i : ℕ) (w : List (CellStage.at B i).S) :
    CellStage.limitFreeMap B (word (w.map (CellStage.stageLetter B i))) =
      (letI := CellStage.directedSystem B
       DirectLimit.Algebra.of
         (fun j : ℕ => (CellStage.at B j).dga.A)
         (fun j k h => CellStage.transition B j k h) i (monoidWord w)) := by
  let := CellStage.directedSystem B
  induction w using List.reverseRecOn with
  | nil =>
      simp only [List.map_nil, word, List.foldl_nil, map_one]
      rw [show monoidWord (R := R) ([] : List (CellStage.at B i).S) = 1 by
        simp [monoidWord, AddMonoidAlgebra.one_def]]
      exact (map_one (DirectLimit.Algebra.of
        (fun j : ℕ => (CellStage.at B j).dga.A)
        (fun j k h => CellStage.transition B j k h) i)).symm
  | @append_singleton w s ih =>
      have hs : CellStage.limitFreeMap B
          (word (List.map (CellStage.stageLetter B i) [s])) =
          DirectLimit.Algebra.of
            (fun j : ℕ => (CellStage.at B j).dga.A)
            (fun j k h => CellStage.transition B j k h) i
            (monoidWord [s]) := by
        simp only [List.map_cons, List.map_nil, word, List.foldl_cons,
          List.foldl_nil, one_mul]
        simp only [CellStage.limitFreeMap, FreeAlgebra.lift_ι_apply]
        exact CellStage.limitLetter_stage B i s
      rw [List.map_append, word_append, monoidWord_append, map_mul, ih, hs]
      exact (map_mul _ (monoidWord w) (monoidWord [s])).symm

private theorem CellStage.limitFreeMap_stageFreeMap
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (i : ℕ) (x : (CellStage.at B i).dga.A) :
    letI := CellStage.directedSystem B
    CellStage.limitFreeMap B (CellStage.stageFreeMap B i x) =
      DirectLimit.Algebra.of
        (fun j : ℕ => (CellStage.at B j).dga.A)
        (fun j k h => CellStage.transition B j k h) i x := by
  let := CellStage.directedSystem B
  apply hom_eq_on_monoidWord (R := R)
    ((CellStage.limitFreeMap B).comp (CellStage.stageFreeMap B i))
    (DirectLimit.Algebra.of
      (fun j : ℕ => (CellStage.at B j).dga.A)
      (fun j k h => CellStage.transition B j k h) i) _ x
  intro w
  calc
    CellStage.limitFreeMap B (CellStage.stageFreeMap B i (monoidWord w)) =
        CellStage.limitFreeMap B
          (word (w.map (CellStage.stageLetter B i))) :=
      congrArg _ (CellStage.stageFreeMap_monoidWord B i w)
    _ = _ := CellStage.limitFreeMap_stage_word B i w

private theorem CellStage.limitFreeMap_limitFreeInv
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (x : letI := CellStage.directedSystem B
      DirectLimit (fun i : ℕ => (CellStage.at B i).dga.A)
        (fun i j h => CellStage.transition B i j h)) :
    CellStage.limitFreeMap B (CellStage.limitFreeInv B x) = x := by
  let := CellStage.directedSystem B
  induction x using DirectLimit.induction with
  | ih i x =>
      change CellStage.limitFreeMap B
        (CellStage.stageFreeMap B i x) = _
      exact CellStage.limitFreeMap_stageFreeMap B i x

private theorem CellStage.limitFreeInv_limitFreeMap
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (x : FreeAlgebra R (CellStage.limitAlphabet B)) :
    CellStage.limitFreeInv B (CellStage.limitFreeMap B x) = x := by
  let := CellStage.directedSystem B
  have h : (CellStage.limitFreeInv B).comp (CellStage.limitFreeMap B) =
      AlgHom.id R (FreeAlgebra R (CellStage.limitAlphabet B)) := by
    apply FreeAlgebra.hom_ext
    funext s
    have key (i : ℕ) (t : (CellStage.at B i).S) :
        CellStage.limitFreeInv B (CellStage.limitFreeMap B
          (FreeAlgebra.ι R (CellStage.stageLetter B i t))) =
        FreeAlgebra.ι R (CellStage.stageLetter B i t) := by
      let x0 : (CellStage.at B i).dga.A := monoidWord [t]
      have h1 : CellStage.limitFreeMap B (FreeAlgebra.ι R (CellStage.stageLetter B i t)) =
          DirectLimit.Algebra.of
            (fun j : ℕ => (CellStage.at B j).dga.A)
            (fun j k h => CellStage.transition B j k h) i x0 := by
        simp only [CellStage.limitFreeMap, FreeAlgebra.lift_ι_apply]
        exact CellStage.limitLetter_stage B i t
      rw [h1, CellStage.limitFreeInv_of B i x0]
      exact (CellStage.stageFreeMap_monoidWord B i [t]).trans (one_mul _)
    simp only [Function.comp_apply, AlgHom.coe_comp, AlgHom.coe_id, id_eq]
    rcases s with s | ⟨i, t⟩
    · exact key 0 s
    · exact key (i + 1) (Sum.inr t)
  exact congrArg (fun f : FreeAlgebra R (CellStage.limitAlphabet B) →ₐ[R]
    FreeAlgebra R (CellStage.limitAlphabet B) => f x) h

private noncomputable def CellStage.limitFreeEquiv
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    FreeAlgebra R (CellStage.limitAlphabet B) ≃ₐ[R] (CellStage.limitDGA B).A :=
  AlgEquiv.ofAlgHom (CellStage.limitFreeMap B) (CellStage.limitFreeInv B)
    (AlgHom.ext (CellStage.limitFreeMap_limitFreeInv B))
    (AlgHom.ext (CellStage.limitFreeInv_limitFreeMap B))

private theorem CellStage.limitLetter_mem_grading
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (s : CellStage.limitAlphabet B) :
    CellStage.limitLetter B s ∈
      (CellStage.limitDGA B).grading (CellStage.limitDegree B s) := by
  let := CellStage.directedSystem B
  have key (i : ℕ) (s : (CellStage.at B i).S) :
      DirectLimit.Module.of R ℕ (fun j => (CellStage.at B j).dga.A)
        (fun j k h => CellStage.transition B j k h) i (monoidWord [s]) ∈
        CellStage.limitGrading B ((CellStage.at B i).degree s) := by
    apply CellStage.limitGrading_of_mem B _ i
    change monoidWord (R := R) [s] ∈
      AddMonoidAlgebra.gradeBy R (freeWordDegree (CellStage.at B i).degree)
        ((CellStage.at B i).degree s)
    have hidx : (List.map (CellStage.at B i).degree [s]).sum = (CellStage.at B i).degree s :=
      add_zero _
    rw [← hidx]
    exact monoidWord_mem_grade (R := R) (CellStage.at B i).degree [s]
  rcases s with s | ⟨i, t⟩
  · exact key 0 s
  · exact key (i + 1) (Sum.inr t)

private theorem CellStage.limitFreeMap_word_mem_grading
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (w : List (CellStage.limitAlphabet B)) :
    CellStage.limitFreeMap B (word w) ∈
      (CellStage.limitDGA B).grading
        ((w.map (CellStage.limitDegree B)).sum) := by
  let := CellStage.directedSystem B
  exact freeAlgebra_lift_word_mem_grade (CellStage.limitDGA B)
    (CellStage.limitDegree B) (CellStage.limitLetter B)
    (CellStage.limitLetter_mem_grading B) w

private theorem CellStage.limitStage_mem_wordSpan
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (i : ℕ) (n : ℤ) (x : (CellStage.at B i).dga.A)
    (hx : x ∈ (CellStage.at B i).dga.grading n) :
    (letI := CellStage.directedSystem B
     DirectLimit.Algebra.of
       (fun j : ℕ => (CellStage.at B j).dga.A)
       (fun j k h => CellStage.transition B j k h) i x) ∈
      Submodule.span R
        {a : (CellStage.limitDGA B).A |
          ∃ w : List (CellStage.limitAlphabet B),
            (w.map (CellStage.limitDegree B)).sum = n ∧
              CellStage.limitFreeEquiv B (word w) = a} := by
  let := CellStage.directedSystem B
  have hx' : x ∈ Submodule.span R
      {a : AddMonoidAlgebra R (Additive (FreeMonoid (CellStage.at B i).S)) |
        ∃ w : List (CellStage.at B i).S,
          (w.map (CellStage.at B i).degree).sum = n ∧
            monoidWord w = a} := by
    change x ∈ (freeZeroDGA (R := R) (CellStage.at B i).degree).grading n at hx
    rw [freeZeroDGA_grading_eq_span] at hx
    change x ∈ Submodule.span R
      {a : AddMonoidAlgebra R (Additive (FreeMonoid (CellStage.at B i).S)) |
        ∃ w : List (CellStage.at B i).S,
          (w.map (CellStage.at B i).degree).sum = n ∧
            freeAlgebraWordEquiv (R := R) (S := (CellStage.at B i).S)
              (word w) = a} at hx
    simpa only [freeAlgebraWordEquiv_word, monoidWord] using hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨w, hw, rfl⟩ := ha
      rw [← CellStage.limitFreeMap_stage_word]
      apply Submodule.subset_span
      refine ⟨w.map (CellStage.stageLetter B i), ?_, ?_⟩
      · rw [List.map_map]
        have heq : CellStage.limitDegree B ∘ CellStage.stageLetter B i =
            (CellStage.at B i).degree :=
          funext (CellStage.limitDegree_stageLetter B i)
        rw [heq]
        exact hw
      · rfl
  | zero =>
      change (DirectLimit.Algebra.of
        (fun j : ℕ => (CellStage.at B j).dga.A)
        (fun j k h => CellStage.transition B j k h) i)
        (0 : (CellStage.at B i).dga.A) ∈ _
      rw [map_zero]
      exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
      change (DirectLimit.Algebra.of
        (fun j : ℕ => (CellStage.at B j).dga.A)
        (fun j k h => CellStage.transition B j k h) i)
        (x + y : (CellStage.at B i).dga.A) ∈ _
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul r x hx ih =>
      change (DirectLimit.Algebra.of
        (fun j : ℕ => (CellStage.at B j).dga.A)
        (fun j k h => CellStage.transition B j k h) i)
        (r • x : (CellStage.at B i).dga.A) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ r ih

private theorem CellStage.limit_isFreeGradedAlgebra
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    IsFreeGradedAlgebra (CellStage.limitDGA B) := by
  let := CellStage.directedSystem B
  refine ⟨CellStage.limitAlphabet B, CellStage.limitDegree B,
    CellStage.limitFreeEquiv B, ?_⟩
  intro n
  apply le_antisymm
  · intro z hz
    obtain ⟨i, x, hx, rfl⟩ := CellStage.limitGrading_exists_of B n z hz
    exact CellStage.limitStage_mem_wordSpan B i n x hx
  · apply Submodule.span_le.mpr
    rintro z ⟨w, hw, rfl⟩
    rw [← hw]
    exact CellStage.limitFreeMap_word_mem_grading B w

private noncomputable def submoduleComplex
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (F : ∀ i, Submodule R (K.X i))
    (hd : ∀ i x, x ∈ F i → K.d i (i + 1) x ∈ F (i + 1)) :
    CochainComplex (ModuleCat.{max u v} R) ℤ :=
  CochainComplex.of (fun i => ModuleCat.of R (F i))
    (fun i => ModuleCat.ofHom ((K.d i (i + 1)).hom.restrict (hd i))) (by
      intro i
      apply ModuleCat.hom_ext
      ext x
      exact ConcreteCategory.congr_hom (K.d_comp_d i (i + 1) (i + 1 + 1)) x.val)

private noncomputable def submoduleComplexMap
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    {F G : ∀ i, Submodule R (K.X i)}
    (hdF : ∀ i x, x ∈ F i → K.d i (i + 1) x ∈ F (i + 1))
    (hdG : ∀ i x, x ∈ G i → K.d i (i + 1) x ∈ G (i + 1))
    (h : ∀ i, F i ≤ G i) : submoduleComplex K F hdF ⟶ submoduleComplex K G hdG :=
  CochainComplex.ofHom (fun i => ModuleCat.ofHom (Submodule.inclusion (h i))) (by
    intro i
    apply ModuleCat.hom_ext
    ext x
    simp only [submoduleComplex, CochainComplex.of_d]
    rfl)

private noncomputable def submoduleComplexι
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (F : ∀ i, Submodule R (K.X i))
    (hd : ∀ i x, x ∈ F i → K.d i (i + 1) x ∈ F (i + 1)) :
    submoduleComplex K F hd ⟶ K :=
  CochainComplex.ofHom (fun i => ModuleCat.ofHom (F i).subtype) (by
    intro i
    apply ModuleCat.hom_ext
    ext x
    simp only [submoduleComplex, CochainComplex.of_d]
    rfl)

/-- A cocone over an `ℕ`-indexed diagram of complexes is a colimit when, in each degree, its
legs are jointly surjective and individually injective. -/
private noncomputable def isColimit_of_surjective_injective
    {D : ℕ ⥤ CochainComplex (ModuleCat.{max u v} R) ℤ} (c : Cocone D)
    (hsurj : ∀ i (x : c.pt.X i), ∃ (n : ℕ) (y : (D.obj n).X i), (c.ι.app n).f i y = x)
    (hinj : ∀ (n : ℕ) i, Function.Injective ((c.ι.app n).f i)) : IsColimit c := by
  apply HomologicalComplex.isColimitOfEval
  intro i
  have : PreservesFilteredColimitsOfSize.{0, 0}
      (forget AddCommGrpCat.{max u v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v, max u v, 0, 0} _
  have : PreservesColimitsOfShape ℕ (forget (ModuleCat.{max u v} R)) :=
    inferInstanceAs (PreservesColimitsOfShape ℕ
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v} ⋙
        forget AddCommGrpCat.{max u v}))
  have : ReflectsColimit (D ⋙ HomologicalComplex.eval (ModuleCat.{max u v} R)
      (ComplexShape.up ℤ) i) (forget (ModuleCat.{max u v} R)) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget (ModuleCat.{max u v} R))
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨n, y, hy⟩ := hsurj i x
    exact ⟨n, y, hy.symm⟩
  · intro n x y h
    obtain rfl := hinj n i h
    exact ⟨n, 𝟙 n, rfl⟩

private theorem kFlat_of_exhaustive_submodules
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (F : ℕ → ∀ i, Submodule R (K.X i))
    (hm : ∀ i, Monotone (fun n => F n i))
    (hd : ∀ n i x, x ∈ F n i → K.d i (i + 1) x ∈ F n (i + 1))
    (hex : ∀ i (x : K.X i), ∃ n, x ∈ F n i)
    (hflat : ∀ n i, Module.Flat R (F n i))
    (hb : ∀ n, ∃ b : ℤ, ∀ i, b < i → F n i = ⊥) : K.KFlat := by
  let D : ℕ ⥤ CochainComplex (ModuleCat.{max u v} R) ℤ := {
    obj n := submoduleComplex K (F n) (hd n)
    map {n m} f := submoduleComplexMap K (hd n) (hd m) (fun i => hm i (leOfHom f))
    map_id n := by
      apply HomologicalComplex.Hom.ext
      funext i
      apply ModuleCat.hom_ext
      ext x
      rfl
    map_comp f g := by
      apply HomologicalComplex.Hom.ext
      funext i
      apply ModuleCat.hom_ext
      ext x
      rfl }
  let c : Cocone D := {
    pt := K
    ι := {
      app n := submoduleComplexι K (F n) (hd n)
      naturality n m f := by
        apply HomologicalComplex.Hom.ext
        funext i
        apply ModuleCat.hom_ext
        ext x
        rfl } }
  have hc : IsColimit c := isColimit_of_surjective_injective c
    (fun i x => let ⟨n, hn⟩ := hex i x; ⟨n, ⟨x, hn⟩, rfl⟩)
    (fun n i => Subtype.val_injective)
  have hD : ∀ n, (D.obj n).KFlat := by
    intro n
    obtain ⟨b, hb⟩ := hb n
    have hbound : (D.obj n).IsStrictlyLE b := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      apply ModuleCat.isZero_iff_subsingleton.mpr
      change Subsingleton (F n i)
      rw [hb i hi]
      infer_instance
    let (i : ℤ) : Module.Flat R ((D.obj n).X i) := hflat n i
    exact CochainComplex.KFlat.kFlat_of_flat (D.obj n) b
  have hcol := CochainComplex.KFlat.kFlat_colimit D hD
  let e := (colimit.isColimit D).coconePointUniqueUpToIso hc
  exact CochainComplex.KFlat.of_iso e hcol

/-- A basis whose differential strictly lowers a natural-number weight gives an
exhaustion by bounded above free subcomplexes, using degree plus weight as the bound. -/
private theorem gradedComplex_kFlat_of_weight
    (A : DifferentialGradedAlgebra.{u, max u v} R) {I : Type (max u v)}
    (b : Module.Basis I R A.A) (degree : I → ℤ) (weight : I → ℕ)
    (hgrade : ∀ i, A.grading i = Submodule.span R (b '' {j | degree j = i}))
    (hd : ∀ j, A.d (b j) ∈ Submodule.span R (b '' {k | weight k < weight j})) :
    (gradedComplex A).KFlat := by
  classical
  let P (n : ℕ) (i : ℤ) : Submodule R A.A :=
    Submodule.span R (b '' {j | degree j = i ∧ i + (weight j : ℤ) ≤ n})
  have hP (n : ℕ) (i : ℤ) : P n i ≤ A.grading i := by
    rw [hgrade i]
    exact Submodule.span_mono (Set.image_mono (fun j hj => hj.1))
  let F (n : ℕ) (i : ℤ) : Submodule R ((gradedComplex A).X i) :=
    (P n i).comap (A.grading i).subtype
  apply kFlat_of_exhaustive_submodules (gradedComplex A) F
  · intro i n m hnm
    exact Submodule.comap_mono <| Submodule.span_mono <|
      Set.image_mono (fun j hj => ⟨hj.1, hj.2.trans (by exact_mod_cast hnm)⟩)
  · intro n i x hx
    change x.val ∈ P n i at hx
    have hp : A.d x.val ∈ P n (i + 1) := by
      generalize x.val = y at hx ⊢
      induction hx using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨j, ⟨hj, hw⟩, rfl⟩ := hy
          apply b.mem_span_image.mpr
          have hhom : A.d (b j) ∈ A.grading (i + 1) := by
            apply A.d_mem
            rw [hgrade i]
            exact Submodule.subset_span ⟨j, hj, rfl⟩
          rw [hgrade (i + 1)] at hhom
          intro k hk
          have hkdeg := b.mem_span_image.mp hhom hk
          have hkwt : weight k < weight j := b.mem_span_image.mp (hd j) hk
          exact ⟨hkdeg, by omega⟩
      | zero => simpa only [map_zero] using (P n (i + 1)).zero_mem
      | add y z hy hz ihy ihz =>
          simpa only [map_add] using (P n (i + 1)).add_mem ihy ihz
      | smul r y hy ih =>
          simpa only [map_smul] using (P n (i + 1)).smul_mem r ih
    refine Submodule.mem_comap.mpr ?_
    simp only [gradedComplex, CochainComplex.of_d, ModuleCat.hom_ofHom]
    exact hp
  · intro i x
    refine ⟨i.toNat + (b.repr x.val).support.sup weight, ?_⟩
    change x.val ∈ P _ i
    apply b.mem_span_image.mpr
    have hx : x.val ∈ Submodule.span R (b '' {j | degree j = i}) := by
      simpa only [hgrade i] using x.property
    intro j hj
    have hdeg := b.mem_span_image.mp hx hj
    have hw := Finset.le_sup (f := weight) hj
    have hi := Int.self_le_toNat i
    refine ⟨hdeg, ?_⟩
    push_cast
    omega
  · intro n i
    have hfree : Module.Free R (P n i) :=
      Module.Free.of_basis
        ((Module.Basis.span (b.linearIndepOn
          {j | degree j = i ∧ i + (weight j : ℤ) ≤ n}).linearIndependent).map
            (LinearEquiv.ofEq _ _ (congrArg (Submodule.span R) (Set.image_eq_range b _)).symm))
    have : Module.Free R (F n i) :=
      Module.Free.of_equiv (Submodule.comapSubtypeEquivOfLe (hP n i)).symm
    exact Module.Flat.of_free
  · intro n
    refine ⟨n, fun i hi => ?_⟩
    have he : {j | degree j = i ∧ i + (weight j : ℤ) ≤ n} = (∅ : Set I) := by
      ext j
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ hj
      omega
    have hp : P n i = ⊥ := by simp only [P, he, Set.image_empty, Submodule.span_empty]
    apply le_antisymm _ bot_le
    intro x hx
    change x.val ∈ P n i at hx
    rw [hp, Submodule.mem_bot] at hx
    exact Subtype.ext hx

private noncomputable def wordWeightSpan {S : Type (max u v)} (weight : S → ℕ)
    (n : ℕ) : Submodule R (AddMonoidAlgebra R (Additive (FreeMonoid S))) :=
  Submodule.span R {a | ∃ w : List S, (w.map weight).sum < n ∧ monoidWord w = a}

private theorem wordWeightSpan_mono {S : Type (max u v)} (weight : S → ℕ) :
    Monotone (wordWeightSpan (R := R) weight) := by
  intro n m hnm
  exact Submodule.span_mono fun _ ⟨w, hw, h⟩ => ⟨w, hw.trans_le hnm, h⟩

private theorem exists_mem_wordWeightSpan {S : Type (max u v)} (weight : S → ℕ)
    (a : AddMonoidAlgebra R (Additive (FreeMonoid S))) :
    ∃ n, a ∈ wordWeightSpan weight n := by
  have ha : a ∈ Submodule.span R (Set.range (monoidWord (R := R) (S := S))) := by
    rw [monoidWord_span_eq_top]
    trivial
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨w, rfl⟩ := ha
      exact ⟨(w.map weight).sum + 1, Submodule.subset_span ⟨w, Nat.lt_succ_self _, rfl⟩⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add a b ha hb iha ihb =>
      obtain ⟨n, hn⟩ := iha
      obtain ⟨m, hm⟩ := ihb
      exact ⟨max n m, Submodule.add_mem _
        (wordWeightSpan_mono weight (le_max_left _ _) hn)
        (wordWeightSpan_mono weight (le_max_right _ _) hm)⟩
  | smul r a ha ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n, Submodule.smul_mem _ r hn⟩

/-- A linear map sending short words into a weight span sends the span of short words there. -/
private theorem linearMap_mem_wordWeightSpan {S T : Type (max u v)} (ws : S → ℕ) (wt : T → ℕ)
    {n m : ℕ} (f : AddMonoidAlgebra R (Additive (FreeMonoid S)) →ₗ[R]
      AddMonoidAlgebra R (Additive (FreeMonoid T)))
    (hf : ∀ w : List S, (w.map ws).sum < n → f (monoidWord w) ∈ wordWeightSpan wt m)
    {a : AddMonoidAlgebra R (Additive (FreeMonoid S))} (ha : a ∈ wordWeightSpan ws n) :
    f a ∈ wordWeightSpan wt m := by
  have : wordWeightSpan ws n ≤ (wordWeightSpan wt m).comap f :=
    Submodule.span_le.mpr fun _ ⟨w, hw, h⟩ => h ▸ hf w hw
  exact this ha

private theorem freeWordMap_mem_weightSpan {S T : Type (max u v)}
    (α : S → T) (ws : S → ℕ) (wt : T → ℕ) (h : ∀ s, wt (α s) = ws s)
    {n : ℕ} {a : AddMonoidAlgebra R (Additive (FreeMonoid S))}
    (ha : a ∈ wordWeightSpan ws n) : freeWordMap α a ∈ wordWeightSpan wt n := by
  refine linearMap_mem_wordWeightSpan ws wt (freeWordMap (R := R) α).toLinearMap
    (fun w hw => ?_) ha
  rw [AlgHom.toLinearMap_apply, freeWordMap_monoidWord]
  refine Submodule.subset_span ⟨w.map α, ?_, rfl⟩
  simpa only [List.map_map, show wt ∘ α = ws from funext h] using hw

private theorem wordWeightSpan_mul_word {S : Type (max u v)} (weight : S → ℕ)
    {n : ℕ} {a : AddMonoidAlgebra R (Additive (FreeMonoid S))}
    (ha : a ∈ wordWeightSpan weight n) (w : List S) :
    a * monoidWord w ∈ wordWeightSpan weight (n + (w.map weight).sum) := by
  refine linearMap_mem_wordWeightSpan weight weight (LinearMap.mulRight R (monoidWord w))
    (fun w' hw' => ?_) ha
  rw [LinearMap.mulRight_apply, ← monoidWord_append]
  exact Submodule.subset_span ⟨w' ++ w, by simpa using hw', rfl⟩

private theorem word_mul_wordWeightSpan {S : Type (max u v)} (weight : S → ℕ)
    {n : ℕ} {a : AddMonoidAlgebra R (Additive (FreeMonoid S))}
    (w : List S) (ha : a ∈ wordWeightSpan weight n) :
    monoidWord w * a ∈ wordWeightSpan weight ((w.map weight).sum + n) := by
  refine linearMap_mem_wordWeightSpan weight weight (LinearMap.mulLeft R (monoidWord w))
    (fun w' hw' => ?_) ha
  rw [LinearMap.mulLeft_apply, ← monoidWord_append]
  exact Submodule.subset_span ⟨w ++ w', by simpa using hw', rfl⟩

private theorem monoidWordDifferential_mem_weightSpan {S : Type (max u v)}
    (degree : S → ℤ) (weight : S → ℕ)
    (δ : S → AddMonoidAlgebra R (Additive (FreeMonoid S)))
    (hδ : ∀ s, δ s ∈ wordWeightSpan weight (weight s)) (w : List S) :
    monoidWordDifferential degree δ w ∈ wordWeightSpan weight (w.map weight).sum := by
  induction w with
  | nil => exact Submodule.zero_mem _
  | cons s w ih =>
      apply Submodule.add_mem
      · exact wordWeightSpan_mul_word weight (hδ s) w
      · simpa only [List.map_cons, List.sum_cons, Submodule.mem_toAddSubgroup] using
          (wordWeightSpan (R := R) weight (weight s + (w.map weight).sum)).toAddSubgroup.zsmul_mem
            (word_mul_wordWeightSpan weight [s] ih) ((degree s).negOnePow : ℤ)

private noncomputable def CellStage.nextBoundary
    (B : DifferentialGradedAlgebra.{u, max u v} R) (P : CellStage B) :
    CellStage.nextAlphabet B P → AddMonoidAlgebra R (Additive (FreeMonoid P.S)) :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec (exists_kernel_cells B P.degree P.δ P.b)))

private noncomputable def CellStage.weight
    (B : DifferentialGradedAlgebra.{u, max u v} R) : (n : ℕ) → (CellStage.at B n).S → ℕ
  | 0 => fun _ => 0
  | n + 1 => Sum.elim (CellStage.weight B n)
      (fun t => Classical.choose (exists_mem_wordWeightSpan (CellStage.weight B n)
        (CellStage.nextBoundary B (CellStage.at B n) t)))

private theorem CellStage.differential_mem_weightSpan
    (B : DifferentialGradedAlgebra.{u, max u v} R) (n : ℕ)
    (s : (CellStage.at B n).S) :
    (CellStage.at B n).δ s ∈ wordWeightSpan (CellStage.weight B n) (CellStage.weight B n s) := by
  induction n with
  | zero => exact Submodule.zero_mem _
  | succ n ih =>
      cases s with
      | inl s =>
          change freeWordMap Sum.inl ((CellStage.at B n).δ s) ∈
            wordWeightSpan (CellStage.weight B (n + 1)) (CellStage.weight B n s)
          exact freeWordMap_mem_weightSpan Sum.inl _ _ (fun _ => rfl) (ih s)
      | inr t =>
          change freeWordMap Sum.inl (CellStage.nextBoundary B (CellStage.at B n) t) ∈
            wordWeightSpan (CellStage.weight B (n + 1)) _
          apply freeWordMap_mem_weightSpan Sum.inl (CellStage.weight B n) _ (fun _ => rfl)
          exact Classical.choose_spec (exists_mem_wordWeightSpan (CellStage.weight B n)
            (CellStage.nextBoundary B (CellStage.at B n) t))

private theorem CellStage.at_kFlat
    (B : DifferentialGradedAlgebra.{u, max u v} R) (n : ℕ) :
    (gradedComplex (CellStage.at B n).dga).KFlat := by
  let P := CellStage.at B n
  let b := AddMonoidAlgebra.basis (Additive (FreeMonoid P.S)) R
  apply gradedComplex_kFlat_of_weight P.dga b (freeWordDegree P.degree)
    (fun w => ((FreeMonoid.toList w.toMul).map (CellStage.weight B n)).sum)
  · intro i
    change (freeZeroDGA (R := R) P.degree).grading i = _
    rw [freeZeroDGA_grading_eq_span]
    congr 1
    ext a
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨Additive.ofMul (FreeMonoid.ofList w), hw, (freeAlgebraWordEquiv_word w).symm⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨FreeMonoid.toList w.toMul, hw,
        freeAlgebraWordEquiv_word (FreeMonoid.toList w.toMul)⟩
  · intro w
    change freeWordDifferentialLinear P.degree P.δ
      (monoidWord (FreeMonoid.toList w.toMul)) ∈ _
    rw [freeWordDifferentialLinear_monoidWord]
    exact monoidWordDifferential_mem_weightSpan P.degree (CellStage.weight B n) P.δ
      (CellStage.differential_mem_weightSpan B n) _

private theorem CellStage.limitInclusion_isDGAMorphism
    (B : DifferentialGradedAlgebra.{u, max u v} R) (n : ℕ) :
    letI := CellStage.directedSystem B
    IsDGAMorphism (CellStage.at B n).dga (CellStage.limitDGA B)
      (DirectLimit.Algebra.of
        (fun i : ℕ => (CellStage.at B i).dga.A)
        (fun i j h => CellStage.transition B i j h) n) := by
  let := CellStage.directedSystem B
  exact ⟨fun i x hx => CellStage.limitGrading_of_mem B i n x hx,
    fun x => (CellStage.limitDifferential_of B n x).symm⟩

private theorem CellStage.limit_kFlat
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    (gradedComplex (CellStage.limitDGA B)).KFlat := by
  let := CellStage.directedSystem B
  let D : ℕ ⥤ CochainComplex (ModuleCat.{max u v} R) ℤ := {
    obj n := gradedComplex (CellStage.at B n).dga
    map {n m} f := gradedComplexMap (CellStage.transition B n m (leOfHom f))
      (CellStage.transition_isDGAMorphism B n m (leOfHom f))
    map_id n := by
      apply HomologicalComplex.Hom.ext
      funext i
      apply ModuleCat.hom_ext
      ext x
      apply Subtype.ext
      change (CellStage.transition B n n le_rfl) x.val = x.val
      rw [CellStage.transition_self]
      rfl
    map_comp {n m k} f g := by
      apply HomologicalComplex.Hom.ext
      funext i
      apply ModuleCat.hom_ext
      ext x
      apply Subtype.ext
      change CellStage.transition B n k _ x.val =
        CellStage.transition B m k _ (CellStage.transition B n m _ x.val)
      exact congrArg (fun f => f x.val)
        (CellStage.transition_comp B n m k (leOfHom f) (leOfHom g)).symm }
  let c : Cocone D := {
    pt := gradedComplex (CellStage.limitDGA B)
    ι := {
      app n := gradedComplexMap
        (DirectLimit.Algebra.of
          (fun i : ℕ => (CellStage.at B i).dga.A)
          (fun i j h => CellStage.transition B i j h) n)
        (CellStage.limitInclusion_isDGAMorphism B n)
      naturality n m f := by
        apply HomologicalComplex.Hom.ext
        funext i
        apply ModuleCat.hom_ext
        ext x
        apply Subtype.ext
        change DirectLimit.Algebra.of
          (fun i : ℕ => (CellStage.at B i).dga.A)
          (fun i j h => CellStage.transition B i j h) m
          (CellStage.transition B n m (leOfHom f) x.val) =
          DirectLimit.Algebra.of
            (fun i : ℕ => (CellStage.at B i).dga.A)
            (fun i j h => CellStage.transition B i j h) n x.val
        exact DirectLimit.Algebra.of_f
          (G := fun i : ℕ => (CellStage.at B i).dga.A)
          (f := fun i j h => CellStage.transition B i j h) (leOfHom f) x.val } }
  have hc : IsColimit c := isColimit_of_surjective_injective c
    (fun i x => let ⟨n, y, hy, heq⟩ := CellStage.limitGrading_exists_of B i x.val x.property
      ⟨n, ⟨y, hy⟩, Subtype.ext heq⟩)
    (fun n i x y h => Subtype.ext (CellStage.limitOf_injective B n (congrArg Subtype.val h)))
  exact CochainComplex.KFlat.of_iso ((colimit.isColimit D).coconePointUniqueUpToIso hc)
    (CochainComplex.KFlat.kFlat_colimit D (CellStage.at_kFlat B))

/-- Every differential graded algebra has a quasi-isomorphic K-flat resolution
which is free as a graded algebra. -/
@[stacks 0BZ7]
public theorem exists_kFlat_freeGraded_resolution
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    ∃ (A : DifferentialGradedAlgebra.{u, max u v} R)
      (f : A.A →ₐ[R] B.A)
      (CA CB : CochainComplex (ModuleCat.{max u v} R) ℤ)
      (eA : ModelsComplex A CA) (eB : ModelsComplex B CB)
      (g : CA ⟶ CB),
      IsFreeGradedAlgebra A ∧
        CA.KFlat ∧
      IsDGAMorphism A B f ∧
        (∀ (n : ℤ) (x : CA.X n),
          (eB.equiv n (g.f n x)).1 = f ((eA.equiv n x).1)) ∧
        QuasiIso g := by
  suffices h : ∃ (A : DifferentialGradedAlgebra.{u, max u v} R)
      (f : A.A →ₐ[R] B.A) (hf : IsDGAMorphism A B f),
      IsFreeGradedAlgebra A ∧ (gradedComplex A).KFlat ∧
        QuasiIso (gradedComplexMap f hf) by
    rcases h with ⟨A, f, hf, hfree, hflat, hq⟩
    exact resolution_witnesses_of_gradedComplex B A f hfree hflat hf hq
  exact ⟨CellStage.limitDGA B, CellStage.limitToTarget B,
    CellStage.limitToTarget_isDGAMorphism B, CellStage.limit_isFreeGradedAlgebra B,
    CellStage.limit_kFlat B, CellStage.limitToTarget_quasiIso B⟩

end Stacks.DGA

end
