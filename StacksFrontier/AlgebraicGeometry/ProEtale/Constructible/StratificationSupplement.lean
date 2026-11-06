module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.Stratification

/-!
# Supplement to `StacksFrontier/AlgebraicGeometry/ProEtale/Constructible/Stratification`

Declarations used by the pro-étale comparison of Stacks 09B1 and 09A6, kept in their own module
so that `StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.Stratification` is unchanged.
-/


@[expose] public noncomputable section
open CategoryTheory
universe u

namespace AlgebraicGeometry

namespace Scheme.ConstructibleStratification

variable {X : Scheme.{u}} {U : X.Opens}

/-- The partition of an open subscheme `U` with the single stratum `U`, immersed by its open
immersion. -/
public def single (X : Scheme.{u}) (U : X.Opens) : ConstructibleStratification X U where
  n := 1
  piece _ := U
  inclusion _ := U.ι
  isImmersion _ := inferInstance
  contained _ := by rw [Scheme.Opens.range_ι]
  constructible _ := by
    rw [Scheme.Opens.range_ι, show U.ι.base ⁻¹' (U : Set X) = Set.univ from
      Set.eq_univ_of_forall fun x => x.2]
    exact Topology.IsConstructible.univ
  pairwise_disjoint i j hij := absurd (Subsingleton.elim i j) hij
  covers := by simp only [Scheme.Opens.range_ι, Set.iUnion_const]

/-- `r.Refines s` says that every stratum of `r` is immersed in some stratum of `s`, compatibly
with the two inclusions into the ambient scheme. -/
public def Refines (r s : ConstructibleStratification X U) : Prop :=
  ∀ k : Fin r.n, ∃ (i : Fin s.n) (a : r.piece k ⟶ s.piece i),
    IsImmersion a ∧ a ≫ s.inclusion i = r.inclusion k

/-- Every partition refines itself. -/
@[refl]
public theorem Refines.refl (s : ConstructibleStratification X U) : s.Refines s := fun k =>
  ⟨k, 𝟙 _, inferInstance, Category.id_comp _⟩

/-- Refinement is transitive: an immersed stratum of an immersed stratum is immersed. -/
@[trans]
public theorem Refines.trans {r s t : ConstructibleStratification X U}
    (hrs : r.Refines s) (hst : s.Refines t) : r.Refines t := by
  intro k
  obtain ⟨i, a, hai, hfa⟩ := hrs k
  obtain ⟨j, b, hbj, hfb⟩ := hst i
  exact ⟨j, a ≫ b, inferInstance, by rw [Category.assoc, hfb, hfa]⟩

variable (s t : ConstructibleStratification X U)

/-- The image of the fibre product of a stratum of `s` with a stratum of `t` is the intersection
of the images of the two strata. -/
public theorem range_pullback_fst_comp (i : Fin s.n) (j : Fin t.n) :
    Set.range (Limits.pullback.fst (s.inclusion i) (t.inclusion j) ≫ s.inclusion i).base =
      Set.range (s.inclusion i).base ∩ Set.range (t.inclusion j).base :=
  Scheme.Pullback.range_fst_comp (s.inclusion i) (t.inclusion j)

/-- The projection of the fibre product of two strata onto a stratum of `s` is an immersion, as a
base change of the immersion of the stratum of `t`. -/
public theorem isImmersion_pullback_fst (i : Fin s.n) (j : Fin t.n) :
    IsImmersion (Limits.pullback.fst (s.inclusion i) (t.inclusion j)) := by
  have := t.isImmersion j
  infer_instance

/-- The projection of the fibre product of two strata onto a stratum of `t` is an immersion, as a
base change of the immersion of the stratum of `s`. -/
public theorem isImmersion_pullback_snd (i : Fin s.n) (j : Fin t.n) :
    IsImmersion (Limits.pullback.snd (s.inclusion i) (t.inclusion j)) := by
  have := s.isImmersion i
  infer_instance

/-- **The common refinement of two partitions of the same open subscheme.** Its strata are the
fibre products of a stratum of `s` with a stratum of `t`. -/
public def inf : ConstructibleStratification X U where
  n := s.n * t.n
  piece k := Limits.pullback (s.inclusion (finProdFinEquiv.symm k).1)
    (t.inclusion (finProdFinEquiv.symm k).2)
  inclusion k := Limits.pullback.fst (s.inclusion (finProdFinEquiv.symm k).1)
    (t.inclusion (finProdFinEquiv.symm k).2) ≫ s.inclusion (finProdFinEquiv.symm k).1
  isImmersion k := by
    have := s.isImmersion (finProdFinEquiv.symm k).1
    have := t.isImmersion (finProdFinEquiv.symm k).2
    infer_instance
  contained k := by
    rw [range_pullback_fst_comp]
    exact Set.inter_subset_left.trans (s.contained _)
  constructible k := by
    rw [range_pullback_fst_comp, Set.preimage_inter]
    exact (s.constructible _).inter (t.constructible _)
  pairwise_disjoint k l hkl := by
    rw [range_pullback_fst_comp, range_pullback_fst_comp]
    have hne : finProdFinEquiv.symm k ≠ finProdFinEquiv.symm l := fun h =>
      hkl (finProdFinEquiv.symm.injective h)
    by_cases h₁ : (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm l).1
    · have h₂ : (finProdFinEquiv.symm k).2 ≠ (finProdFinEquiv.symm l).2 := fun h₂ =>
        hne (Prod.ext h₁ h₂)
      exact (t.pairwise_disjoint _ _ h₂).mono Set.inter_subset_right Set.inter_subset_right
    · exact (s.pairwise_disjoint _ _ h₁).mono Set.inter_subset_left Set.inter_subset_left
  covers := by
    refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (s.covers ▸ hx)
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (t.covers ▸ hx)
      refine Set.mem_iUnion.mpr ⟨finProdFinEquiv (i, j), ?_⟩
      rw [range_pullback_fst_comp, Equiv.symm_apply_apply]
      exact ⟨hi, hj⟩
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      rw [range_pullback_fst_comp] at hk
      exact s.contained _ hk.1

/-- The common refinement refines its first argument, by the first projection of each fibre
product, which is an immersion as a base change of one. -/
public theorem inf_refines_left : (s.inf t).Refines s := fun k => by
  exact ⟨_, Limits.pullback.fst _ _, isImmersion_pullback_fst s t _ _, rfl⟩

/-- The common refinement refines its second argument, by the second projection of each fibre
product, which is an immersion as a base change of one. -/
public theorem inf_refines_right : (s.inf t).Refines t := fun k => by
  exact ⟨_, Limits.pullback.snd _ _, isImmersion_pullback_snd s t _ _,
    Limits.pullback.condition.symm⟩

/-- **A finite family of partitions of one open subscheme has a common refinement.** The empty
family is refined by `AlgebraicGeometry.Scheme.ConstructibleStratification.single`, and a family
of length `n + 1` by the common refinement of its first member with one of its tail. -/
public theorem exists_refines_forall :
    ∀ {n : ℕ} (s : Fin n → ConstructibleStratification X U),
      ∃ r : ConstructibleStratification X U, ∀ i, r.Refines (s i)
  | 0, _ => ⟨single X U, fun i => i.elim0⟩
  | _ + 1, s => by
    obtain ⟨r, hr⟩ := exists_refines_forall fun i => s i.succ
    exact ⟨(s 0).inf r, Fin.cases (inf_refines_left _ _)
      fun j => (inf_refines_right (s 0) r).trans (hr j)⟩

end Scheme.ConstructibleStratification


end AlgebraicGeometry
end
