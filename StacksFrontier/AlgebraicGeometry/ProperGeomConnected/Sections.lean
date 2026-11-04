module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksCore.Tactic.StacksAttribute

/-!
# Idempotent sections and disjoint open covers

Two facts about the structure sheaf of a scheme `X`, both instances of the correspondence
between idempotents of `Γ(X, U)` and decompositions of `U` into two disjoint opens.

* An idempotent section over a preconnected nonempty open is `0` or `1`.
* If `U : ι → X.Opens` is a pairwise disjoint family of opens covering `X`, then restriction is a
  bijection `Γ(X, ⊤) ≃ ∀ i, Γ(X, U i)`.

## Main results

* `Stacks.AlgebraicGeometry.ProperGeomConnected.eq_zero_of_isIdempotentElem_of_basicOpen_eq_bot`:
  an idempotent section with empty nonvanishing locus is `0`.
* `Stacks.AlgebraicGeometry.ProperGeomConnected.isIdempotentElem_eq_zero_or_one`: an idempotent
  section over a preconnected open is `0` or `1`.
* `Stacks.AlgebraicGeometry.ProperGeomConnected.bijective_piRestrict`: for a pairwise disjoint
  open cover, restriction of global sections to the members is bijective.

## References

* [Stacks Project, Tag 0FD1](https://stacks.math.columbia.edu/tag/0FD1)
* [Stacks Project, Tag 00EE](https://stacks.math.columbia.edu/tag/00EE)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProperGeomConnected

variable {X : Scheme.{u}}

/-- An idempotent section whose nonvanishing locus is empty is `0`. -/
theorem eq_zero_of_isIdempotentElem_of_basicOpen_eq_bot {U : X.Opens} {e : Γ(X, U)}
    (he : IsIdempotentElem e) (h : X.basicOpen e = ⊥) : e = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf U e 0 fun x hx ↦ ?_
  set a := X.presheaf.germ U x hx e with ha
  have hidem : a * a = a := by rw [ha, ← map_mul]; exact congrArg _ he
  have hnot : ¬ IsUnit a := by
    rw [ha, ← Scheme.mem_basicOpen X e x hx, h]
    exact fun hmem ↦ hmem
  have hone : IsUnit (1 - a) := (IsLocalRing.isUnit_or_isUnit_one_sub_self a).resolve_left hnot
  obtain ⟨w, hw⟩ : ∃ w, (1 - a) * w = 1 := ⟨hone.unit.inv, hone.unit.val_inv⟩
  have : a * ((1 - a) * w) = 0 := by
    rw [← mul_assoc, IsIdempotentElem.mul_one_sub_self hidem, zero_mul]
  rw [hw, mul_one] at this
  rwa [map_zero]

/-- If a section's nonvanishing locus does not meet `U`, the locus is empty. -/
private theorem basicOpen_eq_bot_of_not_nonempty {U : X.Opens} (f : Γ(X, U))
    (h : ¬ ((U : Set X) ∩ (X.basicOpen f : Set X)).Nonempty) : X.basicOpen f = ⊥ := by
  rw [← TopologicalSpace.Opens.coe_eq_empty, ← Set.not_nonempty_iff_eq_empty]
  exact fun hc ↦ h (hc.mono (Set.subset_inter (X.basicOpen_le f) le_rfl))

/-- An idempotent section over a preconnected nonempty open is `0` or `1`. -/
theorem isIdempotentElem_eq_zero_or_one {U : X.Opens} (hconn : _root_.IsPreconnected (U : Set X))
    {e : Γ(X, U)} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hdisj : (X.basicOpen e : Set X) ∩ (X.basicOpen (1 - e) : Set X) = ∅ := by
    have : X.basicOpen e ⊓ X.basicOpen (1 - e) = ⊥ := by
      rw [← Scheme.basicOpen_mul, he.mul_one_sub_self, Scheme.basicOpen_zero]
    simpa [← TopologicalSpace.Opens.coe_inf] using congrArg (fun V : X.Opens ↦ (V : Set X)) this
  have hsub : (U : Set X) ⊆ (X.basicOpen e : Set X) ∪ (X.basicOpen (1 - e) : Set X) := by
    intro x hx
    obtain h | h := IsLocalRing.isUnit_or_isUnit_one_sub_self (X.presheaf.germ U x hx e)
    · exact Or.inl ((Scheme.mem_basicOpen X e x hx).mpr h)
    · refine Or.inr ((Scheme.mem_basicOpen X (1 - e) x hx).mpr ?_)
      rwa [map_sub, map_one]
  have key : ¬ ((U : Set X) ∩ (X.basicOpen e : Set X)).Nonempty ∨
      ¬ ((U : Set X) ∩ (X.basicOpen (1 - e) : Set X)).Nonempty := by
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    obtain ⟨y, hy⟩ := hconn _ _ (X.basicOpen e).isOpen (X.basicOpen (1 - e)).isOpen hsub
      hc.1 hc.2
    rw [hdisj] at hy
    exact hy.2.elim
  obtain h | h := key
  · exact Or.inl (eq_zero_of_isIdempotentElem_of_basicOpen_eq_bot he
      (basicOpen_eq_bot_of_not_nonempty e h))
  · exact Or.inr (sub_eq_zero.mp (eq_zero_of_isIdempotentElem_of_basicOpen_eq_bot he.one_sub
      (basicOpen_eq_bot_of_not_nonempty _ h)) |>.symm)

/-- For a pairwise disjoint family of opens covering `X`, restriction is a bijection from the
global sections onto the product of the sections over the members of the family. -/
theorem bijective_piRestrict {ι : Type u} (U : ι → X.Opens) (hcover : ⊤ ≤ ⨆ i, U i)
    (hdisj : ∀ i j, i ≠ j → U i ⊓ U j = ⊥) :
    Function.Bijective
      (RingHom.pi fun i ↦ (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom) := by
  have hcompat : ∀ sf : ∀ i, Γ(X, U i),
      TopCat.Presheaf.IsCompatible X.presheaf U sf := by
    intro sf i j
    by_cases h : i = j
    · subst h; rfl
    · have hsub : Subsingleton Γ(X, U i ⊓ U j) := by rw [hdisj i j h]; infer_instance
      exact Subsingleton.elim _ _
  refine ⟨fun s t hst ↦ TopCat.Sheaf.eq_of_locally_eq' X.sheaf U ⊤ (fun i ↦ homOfLE le_top)
    hcover s t fun i ↦ congrFun hst i, fun sf ↦ ?_⟩
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf U ⊤
    (fun i ↦ homOfLE le_top) hcover sf (hcompat sf)
  exact ⟨s, funext hs⟩

end Stacks.AlgebraicGeometry.ProperGeomConnected
