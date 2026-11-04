module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Recognising a sequential colimit of modules from its legs

Let `D : ℕ ⥤ ModuleCat R` be a sequence of modules and let `c` be a cocone on it.  Two
elementwise conditions on the legs of `c` already force `c` to be a colimit:

* every element of `c.pt` is the image of an element of some `D.obj n`;
* an element of `D.obj n` killed by the `n`-th leg is killed by some transition map
  `D.obj n ⟶ D.obj m`.

No compatibility beyond the ones packaged in the cocone has to be checked.

## Main results

* `AlgebraicGeometry.isColimitOfJointlySurjectiveOfKer`: **a cocone on an `ℕ`-indexed sequence of
  modules whose legs are jointly surjective and which detects vanishing one stage later is a
  colimit cocone**.

## Implementation notes

The statement is reflected along the forgetful functor `forget (ModuleCat R)`, which preserves
filtered colimits and reflects isomorphisms, to
`CategoryTheory.Limits.Types.FilteredColimit.isColimitOf'`. The modules live in an arbitrary
universe `u`, independent of the universe of the index `ℕ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {R : Type u} [Ring R] {D : ℕ ⥤ ModuleCat.{u} R}

/-- A cocone on an `ℕ`-indexed sequence of modules is a colimit as soon as its legs are
jointly surjective and every element killed by a leg is killed by some transition. -/
noncomputable def isColimitOfJointlySurjectiveOfKer (c : Limits.Cocone D)
    (hsurj : ∀ w : c.pt, ∃ (n : ℕ) (u : D.obj n), (c.ι.app n).hom u = w)
    (hker : ∀ (n : ℕ) (u : D.obj n), (c.ι.app n).hom u = 0 →
      ∃ (m : ℕ) (h : n ≤ m), (D.map (homOfLE h)).hom u = 0) :
    Limits.IsColimit c := by
  have instP : PreservesFilteredColimits (forget (ModuleCat.{u} R)) := inferInstance
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} R)) :=
    @preservesSmallestFilteredColimits_of_preservesFilteredColimits _ _ _ _
      (forget (ModuleCat.{u} R)) instP
  have : ReflectsColimit D (forget (ModuleCat.{u} R)) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget (ModuleCat.{u} R))
    (Types.FilteredColimit.isColimitOf' _ _ (fun w => ?_) fun n (v v' : D.obj n) h => ?_)
  · obtain ⟨n, v, hv⟩ := hsurj w
    exact ⟨n, v, hv.symm⟩
  · obtain ⟨m, hnm, hm⟩ := hker n (v - v') (by rwa [map_sub, sub_eq_zero])
    exact ⟨m, homOfLE hnm, by rwa [map_sub, sub_eq_zero] at hm⟩

end AlgebraicGeometry

end
