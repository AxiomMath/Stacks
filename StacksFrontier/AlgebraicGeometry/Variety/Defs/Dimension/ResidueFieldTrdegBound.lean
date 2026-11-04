module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.SpecializationTrdeg

/-!
# A uniform bound on the transcendence degrees of the residue fields

Let `X` be a scheme of finite type over a field `K`. Then the transcendence degrees
`trdeg_K κ(x)` of the residue fields of `X` are bounded: there is `d` with
`trdeg_K κ(x) ≤ d` for every point `x`.

Every point specializes from a generic point of an irreducible component of `X`, there are
finitely many of those because `X` is Noetherian, transcendence degree does not increase along
specialization ([Stacks, Tag 0A21]), and each residue field has finite transcendence degree.

In the notation of [Stacks, Tag 0F0X], this says `E_d(X) = X`. That is how it enters the proof
of [Stacks, Tag 0F10]: a sheaf on `X` always has support in `E_d(X)`.

## Main results

* `AlgebraicGeometry.exists_trdeg_residueField_le`: the uniform bound.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 0F0X](https://stacks.math.columbia.edu/tag/0F0X)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The transcendence degrees of the residue fields of a scheme of finite type over a field are
uniformly bounded.** -/
theorem exists_trdeg_residueField_le (K : Type u) [Field K] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of K)) [LocallyOfFiniteType g] [QuasiCompact g] :
    ∃ d : ℕ, ∀ x : X,
      letI : Algebra K (X.residueField x) :=
        ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Algebra.trdeg K (X.residueField x) ≤ d := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsNoetherian X := ⟨⟩
  have : Finite (genericPoints X) :=
    genericPoints.finite finite_irreducibleComponents_of_isNoetherian
  have : Fintype (genericPoints X) := Fintype.ofFinite _
  let : ∀ y : X, Algebra K (X.residueField y) := fun y =>
    ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop ≫ X.Γevaluation y).hom.toAlgebra
  let trdegNat : genericPoints X → ℕ := fun η =>
    Cardinal.toNat (Algebra.trdeg K (X.residueField η.1))
  refine ⟨Finset.univ.sup trdegNat, fun x => ?_⟩
  obtain ⟨η, hηx⟩ : ∃ η : genericPoints X, η.1 ⤳ x := by
    let C : irreducibleComponents X :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    exact ⟨genericPoints.ofComponent C,
      (genericPoints.isGenericPoint_ofComponent C).specializes mem_irreducibleComponent⟩
  have : FinTrdeg K (X.residueField η.1) := residueField_finTrdeg K g η.1
  have hηlt : Algebra.trdeg K (X.residueField η.1) < Cardinal.aleph0 :=
    trdeg_lt_aleph0 K (X.residueField η.1)
  have hle : Algebra.trdeg K (X.residueField x) ≤ Algebra.trdeg K (X.residueField η.1) := by
    by_cases hne : η.1 = x
    · subst x
      exact le_rfl
    · exact (trdeg_residueField_lt_of_specialization K X g hηx hne).le
  have hs : (Cardinal.toNat (Algebra.trdeg K (X.residueField η.1)) : Cardinal) ≤
      (Finset.univ.sup trdegNat : ℕ) := by
    exact_mod_cast (Finset.le_sup (f := trdegNat) (Finset.mem_univ η))
  rw [Cardinal.cast_toNat_of_lt_aleph0 hηlt] at hs
  exact hle.trans hs

end AlgebraicGeometry

end
