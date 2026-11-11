module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.Recovery21.FiniteCoveringsWithIntersections

/-!
# Iterated fibre products of a covering from its pairwise fibre products

Stacks 0739 and 0G22 ask of a finite covering family that all of its nonempty iterated fibre
products lie in a collection `B` of objects (`Stacks.Cohomology.HasIntersectionsIn`). Stacks
09JC states its hypothesis (3) for the pairwise fibre products `U_i ×_U U_j` only. This file
shows that the pairwise condition, imposed on every finite covering of a member of `B` by members
of `B`, gives the iterated one.

## Main results

* `Stacks.Cohomology.hasIntersectionsIn_of_exists_pullback`: if every finite covering of an
  object of `B` by objects of `B` has its pairwise fibre products in `B`, then so are all of its
  iterated fibre products.

## References

* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
* [Stacks Project, Tag 09JC](https://stacks.math.columbia.edu/tag/09JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.Cohomology

/-- **Pairwise fibre products give all iterated fibre products.** Let `B` be a collection of
objects of a site, and assume that whenever `{Xᵢ ⟶ U}` is a finite covering of an object of `B`
by objects of `B`, every fibre product `Xᵢ ×_U Xⱼ` exists and lies in `B`. Then every such
covering has all of its nonempty iterated fibre products in `B`, that is
`Stacks.Cohomology.HasIntersectionsIn B` holds for it.

The proof is by induction on the number of factors: `X_{a₀} ×_U ⋯ ×_U X_{aₙ₊₁}` is the iterated
fibre product over `X_{a₀}` of the base change `{Xᵢ ×_U X_{a₀} ⟶ X_{a₀}}`, which is again a finite
covering of an object of `B` by objects of `B`. -/
theorem hasIntersectionsIn_of_exists_pullback {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (B : Set C)
    (hpb : ∀ (U : C) (E : PreZeroHypercover.{w} U), Finite E.I₀ → B U → (∀ i, B (E.X i)) →
      E.sieve₀ ∈ J U → ∀ i j, ∃ t : PullbackCone (E.f i) (E.f j), Nonempty (IsLimit t) ∧ B t.pt)
    {U : C} (E : PreZeroHypercover.{w} U) (hfin : Finite E.I₀) (hU : B U)
    (hX : ∀ i, B (E.X i)) (hE : E.sieve₀ ∈ J U) : HasIntersectionsIn B E := by
  refine ⟨hfin, hU, hX, fun n ↦ ?_⟩
  induction n generalizing U E with
  | zero =>
    intro a
    have e : ∀ k : Fin 1, E.X (a 0) = E.X (a k) := fun k ↦ by rw [Fin.fin_one_eq_zero k]
    have hc : ∀ k : Fin 1, eqToHom (e k) ≫ E.f (a k) = E.f (a 0) := fun k ↦ by
      obtain rfl := Fin.fin_one_eq_zero k
      simp
    refine ⟨WidePullbackCone.mk (E.f (a 0)) (fun k ↦ eqToHom (e k)) hc,
      ⟨WidePullbackCone.IsLimit.mk _ (fun r ↦ r.π 0) (fun r ↦ r.condition 0)
        (fun r k ↦ ?_) (fun r m _ hm ↦ ?_)⟩, hX _⟩
    · obtain rfl := Fin.fin_one_eq_zero k
      rw [WidePullbackCone.mk_π, eqToHom_refl]
      exact Category.comp_id _
    · have h := hm 0
      rw [WidePullbackCone.mk_π, eqToHom_refl] at h
      exact (Category.comp_id m).symm.trans h
  | succ n ih =>
    intro a
    choose t ht hBt using fun i ↦ hpb U E hfin hU hX hE i (a 0)
    let E' : PreZeroHypercover.{w} (E.X (a 0)) :=
      { I₀ := E.I₀, X := fun i ↦ (t i).pt, f := fun i ↦ (t i).snd }
    have hE' : E'.sieve₀ ∈ J (E.X (a 0)) := by
      refine J.superset_covering (fun W g hg ↦ ?_) (J.pullback_stable (E.f (a 0)) hE)
      obtain ⟨i, h, hh⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
      exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨i,
        PullbackCone.IsLimit.lift (ht i).some h g hh.symm,
        (PullbackCone.IsLimit.lift_snd _ _ _ _).symm⟩
    obtain ⟨s, ⟨hs⟩, hBs⟩ :=
      ih (U := E.X (a 0)) (E := E') hfin (hX _) hBt hE' fun k ↦ a k.succ
    let π : ∀ k : Fin (n + 1 + 1), s.pt ⟶ E.X (a k) :=
      Fin.cases s.base fun k ↦ s.π k ≫ (t (a k.succ)).fst
    have hπ : ∀ k, π k ≫ E.f (a k) = s.base ≫ E.f (a 0) := by
      refine Fin.cases (by simp [π]) fun k ↦ ?_
      simp only [π, Fin.cases_succ, Category.assoc, (t (a k.succ)).condition]
      exact s.condition_assoc k _
    let lift (r : WidePullbackCone fun k : Fin (n + 1 + 1) ↦ E.f (a k)) : r.pt ⟶ s.pt :=
      WidePullbackCone.IsLimit.lift hs (r.π 0)
        (fun k ↦ PullbackCone.IsLimit.lift (ht (a k.succ)).some (r.π k.succ) (r.π 0)
          (by rw [r.condition, r.condition]))
        fun k ↦ PullbackCone.IsLimit.lift_snd _ _ _ _
    have hlift (r : WidePullbackCone fun k : Fin (n + 1 + 1) ↦ E.f (a k)) (k : Fin (n + 1 + 1)) :
        lift r ≫ π k = r.π k := by
      refine Fin.cases ?_ (fun k ↦ ?_) k
      · simp [π, lift]
      · simp [π, lift]
    have hπ0 : π 0 = s.base := rfl
    have hπs : ∀ k : Fin (n + 1), π k.succ = s.π k ≫ (t (a k.succ)).fst := fun _ ↦ rfl
    refine ⟨WidePullbackCone.mk (s.base ≫ E.f (a 0)) π hπ,
      ⟨WidePullbackCone.IsLimit.mk _ lift (fun r ↦ ?_) (fun r k ↦ hlift r k)
        (fun r m _ hm ↦ ?_)⟩, hBs⟩
    · have h := hlift r 0
      rw [hπ0] at h
      exact ((Category.assoc _ _ _).symm.trans (h =≫ E.f (a 0))).trans (r.condition 0)
    · simp only [WidePullbackCone.mk_π] at hm
      have h0 : m ≫ s.base = lift r ≫ s.base := by
        have h1 := hm 0
        have h2 := hlift r 0
        rw [hπ0] at h1 h2
        exact h1.trans h2.symm
      refine WidePullbackCone.IsLimit.hom_ext hs h0 fun k ↦ ?_
      have hc : s.π k ≫ (t (a k.succ)).snd = s.base := s.condition k
      refine PullbackCone.IsLimit.hom_ext (ht (a k.succ)).some ?_ ?_
      · have h1 := hm k.succ
        have h2 := hlift r k.succ
        rw [hπs] at h1 h2
        exact (Category.assoc _ _ _).trans ((h1.trans h2.symm).trans (Category.assoc _ _ _).symm)
      · exact (Category.assoc _ _ _).trans ((m ≫= hc).trans
          (h0.trans ((lift r ≫= hc).symm.trans (Category.assoc _ _ _).symm)))

end Stacks.Cohomology

end
