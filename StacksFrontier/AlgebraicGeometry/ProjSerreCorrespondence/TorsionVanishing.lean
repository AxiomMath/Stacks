module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StructureMorphism
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Basic

/-!
# The associated sheaf of a torsion graded module on `Proj` vanishes

Let `S = ⨁_{n ≥ 0} 𝒜 n` be a nonnegatively graded ring, let `X = Proj 𝒜`, and let `M` be a
`ℤ`-graded `S`-module. This file proves that the associated sheaf `M̃` is a zero object when `M`
is torsion, in either of two forms: `M` is `𝒜₊`-power torsion, that is,
`IsIPowerTorsion S M (HomogeneousIdeal.irrelevant 𝒜).toIdeal` (every element of `M` is
annihilated by a positive power of the irrelevant ideal, More on Algebra, Definition 05E6), or the
homogeneous components of `M` vanish in all large degrees. No finiteness, degree-one generation or
Noetherian hypothesis is used.

## Main results

* `subsingleton_moduleFiber_of_isIPowerTorsion`: the fiber of a torsion module at a point of
  `Proj` is trivial.
* `isZero_associatedModuleSheaf_of_isIPowerTorsion` and `isZero_associatedModuleSheafFunctor_obj`:
  the associated sheaf of an `𝒜₊`-power torsion graded module is a zero object, in the bare form
  and for the bundled functor `M ↦ M̃`.
* `exists_homogeneous_pos_degree_notMem`: a point of `Proj 𝒜` admits a homogeneous element of
  positive degree outside its prime.
* `isZero_associatedModuleSheaf_of_eventually_eq_zero`: the associated sheaf of a graded module
  whose homogeneous components vanish in all large degrees is a zero object.

## References

* [Stacks Project, Tag 0BXD](https://stacks.math.columbia.edu/tag/0BXD)
* [Stacks Project, Tag 05E6](https://stacks.math.columbia.edu/tag/05E6)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u v w t

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [SetLike.GradedSMul 𝒜 𝒨]

/-- The fiber at a point of `Proj` of an `𝒜₊`-power torsion module is trivial. -/
theorem subsingleton_moduleFiber_of_isIPowerTorsion
    (htor : IsIPowerTorsion S M (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    (x : ProjectiveSpectrum.top 𝒜) :
    Subsingleton (ModuleFiber (M := M) 𝒜 x) := by
  obtain ⟨f, hfI, hfx⟩ := SetLike.not_le_iff_exists.mp x.not_irrelevant_le
  refine LocalizedModule.subsingleton_iff.mpr fun m => ?_
  obtain ⟨n, -, hn⟩ := htor m
  exact ⟨f ^ n, x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hfx n,
    hn _ (Ideal.pow_mem_pow hfI n)⟩

/-- If every fiber is trivial then so is every section group of the associated sheaf. -/
theorem subsingleton_moduleSections_of_subsingleton_moduleFiber
    (hfib : ∀ x : ProjectiveSpectrum.top 𝒜, Subsingleton (ModuleFiber (M := M) 𝒜 x))
    (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    Subsingleton (moduleSections 𝒜 𝒨 U) :=
  ⟨fun _ _ => Subtype.ext (funext fun x => (hfib x.1).elim _ _)⟩

/-- If every fiber is trivial then the associated sheaf is a zero object. -/
theorem isZero_associatedModuleSheaf_of_subsingleton_moduleFiber
    (hfib : ∀ x : ProjectiveSpectrum.top 𝒜, Subsingleton (ModuleFiber (M := M) 𝒜 x)) :
    Limits.IsZero (associatedModuleSheaf 𝒜 𝒨) := by
  rw [Limits.IsZero.iff_id_eq_zero]
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext ?_)
  ext a
  exact @Subsingleton.elim _
    (subsingleton_moduleSections_of_subsingleton_moduleFiber 𝒜 𝒨 hfib U.unop) _ _

/-- The associated sheaf `M̃` of an `𝒜₊`-power torsion graded module `M` is a zero object. -/
@[stacks 0BXD "the functor M ↦ M~ kills the torsion modules, the step that lets it be \
defined on the quotient category; stated for 𝒜₊-power torsion modules, with no finiteness, \
Noetherian or degree-one generation hypothesis", ega "II 2.5.6" "sufficiency clause"]
theorem isZero_associatedModuleSheaf_of_isIPowerTorsion
    (htor : IsIPowerTorsion S M (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :
    Limits.IsZero (associatedModuleSheaf 𝒜 𝒨) :=
  isZero_associatedModuleSheaf_of_subsingleton_moduleFiber 𝒜 𝒨
    (subsingleton_moduleFiber_of_isIPowerTorsion 𝒜 htor)

/-- Every point of `Proj 𝒜` has a homogeneous element of strictly positive degree outside its
homogeneous prime. -/
theorem exists_homogeneous_pos_degree_notMem (x : ProjectiveSpectrum.top 𝒜) :
    ∃ (k : ℕ) (_ : 0 < k) (g : S), g ∈ 𝒜 k ∧ g ∉ x.asHomogeneousIdeal := by
  by_contra! h
  exact x.not_irrelevant_le ((HomogeneousIdeal.irrelevant_le 𝒜).mpr fun k hk g hg => h k hk g hg)

/-- The fiber at a point of `Proj` of a graded module whose homogeneous components vanish in all
degrees `≥ N` is trivial. -/
theorem subsingleton_moduleFiber_of_eventually_eq_zero [DirectSum.Decomposition 𝒨] {N : ℤ}
    (hN : ∀ n : ℤ, N ≤ n → ∀ m : M, m ∈ 𝒨 n → m = 0) (x : ProjectiveSpectrum.top 𝒜) :
    Subsingleton (ModuleFiber (M := M) 𝒜 x) := by
  obtain ⟨d, hd, g, hg, hgx⟩ := exists_homogeneous_pos_degree_notMem 𝒜 x
  refine LocalizedModule.subsingleton_iff.mpr fun m => ?_
  suffices hkill : ∃ k : ℕ, g ^ k • m = 0 by
    obtain ⟨k, hk⟩ := hkill
    exact ⟨g ^ k, x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hgx k, hk⟩
  induction m using DirectSum.Decomposition.inductionOn 𝒨 with
  | zero => exact ⟨0, smul_zero _⟩
  | homogeneous m =>
      rename_i i
      refine ⟨(N - i).toNat, hN ((((N - i).toNat * d : ℕ) : ℤ) + i) ?_ _ ?_⟩
      · have hd1 : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
        have h0 : (0 : ℤ) ≤ ((N - i).toNat : ℤ) := by positivity
        have h1 : N - i ≤ ((N - i).toNat : ℤ) := Int.self_le_toNat _
        rw [Nat.cast_mul]
        nlinarith
      · have hpow : g ^ (N - i).toNat ∈ 𝒜 ((N - i).toNat • d) :=
          SetLike.pow_mem_graded _ hg
        have hmem := SetLike.GradedSMul.smul_mem (A := 𝒜) (B := 𝒨) hpow m.2
        rw [smul_eq_mul] at hmem
        exact hmem
  | add m m' hm hm' =>
      obtain ⟨k, hk⟩ := hm
      obtain ⟨k', hk'⟩ := hm'
      have h1 : g ^ (k + k') • m = 0 := by
        rw [add_comm k k', pow_add, mul_smul, hk, smul_zero]
      have h2 : g ^ (k + k') • m' = 0 := by
        rw [pow_add, mul_smul, hk', smul_zero]
      exact ⟨k + k', by rw [smul_add, h1, h2, add_zero]⟩

/-- A graded module whose homogeneous components vanish in all sufficiently large degrees has zero
associated sheaf. -/
@[stacks 0BXD "the functor M ↦ M~ kills the torsion subcategory, with torsion in the form the \
source defines the subcategory Mod^fg_{A,torsion}: the homogeneous components vanish in all \
large degrees; no finiteness hypothesis is used",
  ega "II 2.5.6" "sufficiency clause",
  ega "II 2.7.2" "If M satisfies (TN)",
  ega "II 2.7.3" "(ii)",
  ega "II 3.4.2" "special case"]
theorem isZero_associatedModuleSheaf_of_eventually_eq_zero [DirectSum.Decomposition 𝒨] {N : ℤ}
    (hN : ∀ n : ℤ, N ≤ n → ∀ m : M, m ∈ 𝒨 n → m = 0) :
    Limits.IsZero (associatedModuleSheaf 𝒜 𝒨) :=
  isZero_associatedModuleSheaf_of_subsingleton_moduleFiber 𝒜 𝒨
    (subsingleton_moduleFiber_of_eventually_eq_zero 𝒜 𝒨 hN)

open Stacks.AlgebraicGeometry.ProjSheafFunctoriality in
/-- The associated-sheaf functor `M ↦ M̃` sends an `𝒜₊`-power torsion graded module to a zero
object. -/
@[stacks 0BXD "the bundled functor M ↦ M~ sends torsion graded modules to zero objects, the \
step that lets it be defined on the quotient category"]
theorem isZero_associatedModuleSheafFunctor_obj (X : GradedModuleCat.{u, v, w} 𝒜)
    (htor : IsIPowerTorsion S X.carrier (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :
    Limits.IsZero ((associatedModuleSheafFunctor 𝒜).obj X) :=
  isZero_associatedModuleSheaf_of_isIPowerTorsion 𝒜 X.grade htor

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
