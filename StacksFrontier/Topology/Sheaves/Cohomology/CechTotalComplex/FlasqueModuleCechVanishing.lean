module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.InjectiveVanishing

/-!
# Čech cohomology of a flasque sheaf of modules, in positive degrees

Let `(X, O_X)` be a ringed space, let `V` be an open subset and let `U : ι → Opens X` be a family
of opens with `V = ⨆ i, U i`.  If the abelian sheaf underlying a sheaf of `O_X`-modules `F` is
flasque, then the positive-degree cohomology of the module-valued Čech complex
`Č^•(U, F)` of the cover vanishes.

## Main results

* `Stacks.Cohomology.CechSheaf.exists_md_eq_of_isFlasque`: a positive-degree cocycle of the
  module-valued Čech complex of a flasque sheaf of modules is a coboundary.
* `Stacks.Cohomology.CechSheaf.isZero_cechComplex_homology_of_isFlasque`: consequently the
  positive-degree module-valued Čech cohomology vanishes.

## Implementation notes

This is the module-valued form of [Stacks, Tag 09SZ], whose abelian-sheaf form is
`Stacks.Cohomology.FlasqueCech.isZero_cechComplex_homology_of_isFlasque`. The flasqueness
hypothesis is on the underlying abelian sheaf, and the index type of the cover is tied to the
universe of the coefficients by `UnivLE`.

## References

* [Stacks Project, Tag 09SZ](https://stacks.math.columbia.edu/tag/09SZ)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex (inter)
open Stacks.Cohomology.Basis (res res_id res_res res_sum res_zsmul)

universe uX uR uM uI

attribute [local instance] ModuleCat.hasLimitsOfSize
attribute [local instance] AddCommGrpCat.hasLimitsOfSize

namespace Stacks.Cohomology.CechSheaf

variable {X : Type uX} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{uR}}
  {ι : Type uI} [UnivLE.{uI, uM}]
  (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i) (F : SheafOfModules.{uM} R)

/-- **Every positive-degree cocycle is a coboundary.**  For a sheaf of modules whose underlying
abelian sheaf is flasque, a cocycle of the module-valued Čech complex in a positive degree is the
differential of a cochain one degree down. -/
theorem exists_md_eq_of_isFlasque (hF : (abSheaf F).IsFlasque) {n : ℕ}
    (s : ToType
      (((CategoryTheory.cechComplexFunctor (coverObject U hU)).obj
        (sectionsPresheaf V F)).X (n + 1)))
    (hs : md V U hU F s = 0) :
    ∃ b, md V U hU F b = s := by
  obtain ⟨κ, τ, σ, hστ⟩ : ∃ (κ : Type uM) (τ : ι → κ) (σ : κ → ι), ∀ i, σ (τ i) = i :=
    ⟨Shrink.{uM} ι, equivShrink ι, (equivShrink ι).symm,
      fun i => (equivShrink ι).symm_apply_apply i⟩
  have hcomp : ∀ {m : ℕ} (y : Fin m → ι), σ ∘ (τ ∘ y) = y :=
    fun y => funext fun a => hστ (y a)
  have hint : ∀ {m : ℕ} (y : Fin m → ι), inter (fun k => U (σ k)) (τ ∘ y) = inter U y :=
    fun y => congrArg (inter U) (hcomp y)
  obtain ⟨g, hg⟩ := exists_sum_res_eq (T := TopCat.of X) (fun k => U (σ k)) (abSheaf F) n
    (fun y => mcomp V U hU F s (σ ∘ y))
    (fun y => sum_res_mcomp_eq_zero V U hU F s hs (σ ∘ y) le_rfl)
  refine ⟨mmk V U hU F (fun y => res (abSections F) (hint y).ge (g (τ ∘ y))), ?_⟩
  refine mcech_ext V U hU F _ _ fun x => ?_
  rw [mcomp_md V U hU F]
  have key : ∑ a : Fin (n + 2), (-1 : ℤ) ^ (a : ℕ) •
      res (abSections F) (inter_le_reindex (fun k => U (σ k)) (τ ∘ x) a.succAbove)
        (g (τ ∘ (x ∘ a.succAbove))) = mcomp V U hU F s (σ ∘ (τ ∘ x)) := hg (τ ∘ x)
  have key2 := congrArg (res (abSections F) (hint x).ge) key
  rw [res_sum] at key2
  refine Eq.trans ?_ (key2.trans ?_)
  · exact Finset.sum_congr rfl fun a _ => by
      rw [mcomp_mmk V U hU F, res_zsmul, res_res, res_res]
  · exact (res_mcomp_congr V U hU F s (hcomp x) _ le_rfl).trans (res_id _ _)

/-- **The positive-degree module-valued Čech cohomology of a flasque sheaf of modules
vanishes.** -/
theorem isZero_cechComplex_homology_of_isFlasque (hF : (abSheaf F).IsFlasque)
    (p : ℕ) (hp : 0 < p) :
    IsZero ((cechComplex V U hU F).homology p) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne'
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  exact fun s hs => exists_md_eq_of_isFlasque V U hU F hF s hs

end Stacks.Cohomology.CechSheaf

end
