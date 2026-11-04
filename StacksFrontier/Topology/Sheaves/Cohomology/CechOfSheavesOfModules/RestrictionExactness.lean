module

public import StacksFrontier.Algebra.Homology.CechFinsuppHomotopy
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.InjectiveVanishing

/-!
# Exactness of a Čech complex read off the restrictions to a common open

Let `I` be a sheaf of modules on a space, `U` a cover of an open `V` and `W` an open contained in
every member of the cover. Restricting the components of a Čech cochain to `W` turns it into a
family of sections over the single open `W`, and the Čech differential becomes the Čech
coboundary `Stacks.CechFinsupp.cechCoboundary` of families. If restriction to `W` is injective on
the sections over every intersection of members of the cover, a Čech cochain is determined by
these restrictions, and the Čech complex is exact in a positive degree as soon as the complex of
families with values in the images of these restrictions is.

This is how the cohomology of a module whose sections over the intersections of the cover all
embed into the sections over one dense open is computed: the computation takes place inside the
sections over that open, where it becomes combinatorics.

## Main results

* `Stacks.Cohomology.CechSheaf.isZero_cechComplex_homology_of_res_injective`: **positive-degree
  exactness of the module-valued Čech complex from exactness of the restricted families.**
-/

@[expose] public noncomputable section

universe uX uR uM uI

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.Basis (res res_id res_res res_zero res_sum res_zsmul)

namespace Stacks.Cohomology.CechSheaf

/-- An open contained in every member of a cover is contained in each of their nonempty
intersections. -/
theorem le_inter_of_forall_le {X : Type uX} [TopologicalSpace X] {ι : Type uI}
    (U : ι → Opens X) {W : Opens X} (hW : ∀ i, W ≤ U i) {m : ℕ} (x : Fin (m + 1) → ι) :
    W ≤ inter U x := by
  rw [inter_eq_iInf]
  exact le_iInf fun a => hW (x a)

variable {X : Type uX} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{uR}}
  {ι : Type uI} [UnivLE.{uI, uM}]
  (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i) (I : SheafOfModules.{uM} R)
  {W : Opens X} (hW : ∀ i, W ≤ U i)


/-- **Positive-degree exactness from the restrictions to a common open.** Suppose an open `W` is
contained in every member of the cover, restriction to `W` is injective on the sections of `I`
over every nonempty intersection of members, and every Čech cocycle of degree `p + 1` of families
of sections over `W` with values in those images is the Čech coboundary of such a family. Then the
module-valued Čech complex of `I` is exact in degree `p + 1`. -/
theorem isZero_cechComplex_homology_of_res_injective (p : ℕ)
    (hinj : ∀ (m : ℕ) (x : Fin (m + 1) → ι),
      Function.Injective (res (abSections I) (le_inter_of_forall_le U hW x)))
    (hexact : ∀ c : (Fin (p + 2) → ι) → ToType ((abSections I).obj (op W)),
      (∀ x, c x ∈ Set.range (res (abSections I) (le_inter_of_forall_le U hW x))) →
      (∀ y : Fin (p + 3) → ι, Stacks.CechFinsupp.cechCoboundary c y = 0) →
      ∃ b : (Fin (p + 1) → ι) → ToType ((abSections I).obj (op W)),
        (∀ x, b x ∈ Set.range (res (abSections I) (le_inter_of_forall_le U hW x))) ∧
          ∀ x, Stacks.CechFinsupp.cechCoboundary b x = c x) :
    IsZero ((cechComplex V U hU I).homology (p + 1)) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro s hs
  change md V U hU I s = 0 at hs
  let c : (Fin (p + 2) → ι) → ToType ((abSections I).obj (op W)) := fun x =>
    res (abSections I) (le_inter_of_forall_le U hW x) (mcomp V U hU I s x)
  have hcoc : ∀ y : Fin (p + 3) → ι, Stacks.CechFinsupp.cechCoboundary c y = 0 := fun y =>
    sum_res_mcomp_eq_zero V U hU I s hs y (le_inter_of_forall_le U hW y)
  obtain ⟨b, hb, hbc⟩ := hexact c (fun x => ⟨_, rfl⟩) hcoc
  choose b' hb' using hb
  refine ⟨mmk V U hU I b', ?_⟩
  refine mcech_ext V U hU I _ _ fun x => hinj _ x ?_
  change res (abSections I) _ (mcomp V U hU I (md V U hU I (mmk V U hU I b')) x) = c x
  rw [mcomp_md, res_sum, ← hbc x]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [res_zsmul, res_res, mcomp_mmk, ← hb' (x ∘ a.succAbove)]

end Stacks.Cohomology.CechSheaf

end
