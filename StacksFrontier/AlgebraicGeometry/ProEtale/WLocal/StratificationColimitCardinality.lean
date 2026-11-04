module

public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationColimit
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import Mathlib.SetTheory.Cardinal.Finite
public import StacksCore.Tactic.StacksAttribute

/-!
# Cardinality of the w-localization

Let `A` be a commutative ring and let `κ` be an infinite cardinal at least as large as the
underlying set of `A`. Each finite stratification ring `A_E` has cardinality at most `κ`. Since
there are at most `κ` finite subsets of `A`, the colimit ring `A_w` also has cardinality at most
`κ`.

## Main results

* `AlgebraicGeometry.ProEtale.mk_finset_le` bounds the number of finite subsets of `A`.
* `AlgebraicGeometry.ProEtale.mk_stratificationRing_le` bounds each ring `A_E`.
* `AlgebraicGeometry.ProEtale.mk_stratificationColimitRing_le` bounds `A_w`.

## Implementation notes

The three declarations record respectively the bound on the indexing set, the bound on every
finite stage, and the resulting bound on the direct limit.

## References

* [Stacks Project, Tag 0976](https://stacks.math.columbia.edu/tag/0976)
-/

@[expose] public section

universe u

open Cardinal

namespace AlgebraicGeometry.ProEtale

/-- Finite subsets of a type of size at most an infinite cardinal themselves
form a type of size at most that cardinal. -/
@[stacks 0976 "finite subsets"]
theorem mk_finset_le {A : Type u} (κ : Cardinal.{u})
    (hκ : ℵ₀ ≤ κ) (hA : Cardinal.mk A ≤ κ) :
    Cardinal.mk (Finset A) ≤ κ := by
  classical
  rcases finite_or_infinite A with _ | _
  · exact Cardinal.mk_le_aleph0.trans hκ
  · simpa using hA

/-- Each finite stratification ring `A_E` has cardinality at most `κ`. -/
@[stacks 0976 "finite stages"]
theorem mk_stratificationRing_le {A : Type u} [CommRing A]
    (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hA : Cardinal.mk A ≤ κ)
    (E : Finset A) :
    Cardinal.mk (stratificationRing E) ≤ κ := by
  classical
  let index := {E' : Finset A // E' ⊆ E}
  have : Finite index :=
    Finite.of_injective
      (fun E' : index => (⟨E'.val, Finset.mem_powerset.mpr E'.property⟩ :
        {s : Finset A // s ∈ E.powerset}))
      fun _ _ h => Subtype.ext
        (congrArg (fun z : {s : Finset A // s ∈ E.powerset} => z.val) h)
  let : Fintype index := Fintype.ofFinite index
  have hfactor : ∀ E' : index,
      Cardinal.mk (localizationRing (stratumIdeal E E')
        (stratumOpenElement E'.val)) ≤ κ := fun E' =>
    (Cardinal.mk_le_of_isLocalization (R := A)
      (localizationSubmonoid (stratumIdeal E E') (stratumOpenElement E'.val))
      (localizationRing (stratumIdeal E E')
        (stratumOpenElement E'.val))).trans (max_le hκ hA)
  rw [Cardinal.mk_pi, Cardinal.prod_eq_of_fintype]
  simpa using (Cardinal.prod_le_of_le_of_aleph0_le
    (Finset.univ : Finset index)
    (fun E' => Cardinal.mk (localizationRing
      (stratumIdeal E E') (stratumOpenElement E'.val))) κ hκ
    (fun E' _ => hfactor E'))

/-- The ring `A_w` has cardinality at most every infinite cardinal bounding
the cardinality of `A`. -/
@[stacks 0976]
theorem mk_stratificationColimitRing_le {A : Type u} [CommRing A]
    (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hA : Cardinal.mk A ≤ κ) :
    Cardinal.mk (stratificationColimitRing (A := A)) ≤ κ := by
  classical
  let stages := fun E : Finset A => stratificationRing E
  have hsurj : Function.Surjective
      (fun x : Σ E : Finset A, stages E =>
        stratificationColimitMap (A := A) x.1 x.2) := by
    intro z
    obtain ⟨E, x, hx⟩ := Ring.DirectLimit.exists_of
      (G := stages) (f := fun E₁ E₂ h => stratificationRingMap E₁ E₂ h) z
    exact ⟨⟨E, x⟩, hx⟩
  calc
    Cardinal.mk (stratificationColimitRing (A := A))
        ≤ Cardinal.mk (Σ E : Finset A, stages E) := Cardinal.mk_le_of_surjective hsurj
    _ = Cardinal.sum (fun E : Finset A => Cardinal.mk (stages E)) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : Finset A => κ) :=
      Cardinal.sum_le_sum _ _ (fun E => mk_stratificationRing_le κ hκ hA E)
    _ = Cardinal.mk (Finset A) * κ := Cardinal.sum_const' _ _
    _ ≤ κ * κ := mul_le_mul' (mk_finset_le κ hκ hA) le_rfl
    _ = κ := Cardinal.mul_eq_self hκ

end AlgebraicGeometry.ProEtale

end
