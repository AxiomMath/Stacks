module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimitHomologySequence
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit

/-!
# The upper bound at a derived limit, without exactness of countable products

Let `A` be an abelian category with countable products and a derived category, let `(Kₙ)` be an
inverse system in `D(A)` indexed by `ℕ`, and let `L` be a derived limit of it, presented as
usual by a distinguished triangle `L ⟶ ∏ₙ Kₙ ⟶ ∏ₙ Kₙ ⟶ L⟦1⟧` whose middle map is the Milnor
difference `1 - shift`.  This file gives the upper bound `L ∈ D^{≤ d}` from two hypotheses that
do *not* require the countable products of `A` to be exact:

* the comparison `Hⁱ(∏ₙ Kₙ) ⟶ ∏ₙ Hⁱ(Kₙ)` is invertible in degrees `i ≥ d`;
* the cokernel of the Milnor difference of the degree-`d` cohomology system `n ↦ H^d(Kₙ)`
  vanishes, i.e. `R¹lim H^d(Kₙ) = 0`.

## Main results

* `Stacks.DerivedLimit.isLE_of_isDerivedLimit_of_isZero_cokernel`: the upper bound at the
  derived limit.

## Implementation notes

`Stacks.DerivedLimit.isLE_of_isDerivedLimit_of_isMittagLeffler` has the same conclusion from a
Mittag-Leffler hypothesis alone, but it is stated for `D(Ab)` and it is `Ab`-specific twice
over: the Mittag-Leffler condition is a condition on the *underlying sets* of the cohomology
systems, and its proof uses the Milnor short exact sequence
`DerivedCategory.exists_milnor_shortExact_of_distTriang`, which carries
`CategoryTheory.Limits.HasExactLimitsOfShape (Discrete ℕ) A` as a hypothesis — the identification
`Hⁱ(∏ₙ Kₙ) ≅ ∏ₙ Hⁱ(Kₙ)` of [Stacks, Tag 07KC] part (3) is only available there.  Countable
products of sheaves are not exact, so neither the hypothesis nor the ingredient is available in
`D(Mod(𝒪))` on a site.

The two hypotheses here isolate what that exactness is used for: the first *is* the conclusion
of Tag 07KC (3) in the degrees that matter, taken as an assumption instead of derived from exact
products, and the second is the vanishing of the first derived inverse limit of the top
cohomology system, which the Mittag-Leffler condition supplies in `Ab` through
`Stacks.DerivedLimit.epi_delta_of_isMittagLeffler`.  Neither statement implies the other.

The proof is the long exact homology sequence of the defining triangle and nothing else, so no
abelian-category hypothesis beyond `CategoryTheory.Limits.HasProductsOfShape ℕ A` enters.  In
degree `i > d` the two Mathlib equivalences
`DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff` and
`DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff` turn surjectivity of the Milnor
difference on `H^{i-1}` into injectivity of `Hⁱ(L) ⟶ Hⁱ(∏ₙ Kₙ)`, and the target vanishes; so
`Hⁱ(L) = 0`.  Above `d + 1` the difference map is automatically surjective because its source
already vanishes, and at `i = d + 1` it is surjective by the second hypothesis read through the
product comparison, using
`Stacks.DerivedLimit.map_inverseSystemDifference_comp_piComparison`.

The product comparison is only assumed invertible in degrees `≥ d`, which is all the argument
sees: the degrees `< d` of the system are untouched.

## References

* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC)
* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace Stacks.DerivedLimit

variable {A : Type u} [Category.{v} A] [Abelian A] [HasProductsOfShape ℕ A]
  [HasDerivedCategory.{w} A]

/-- **A derived limit of a tower with a common upper bound `d` keeps that upper bound, once the
cohomology of the product is the product of the cohomologies in degrees `≥ d` and the first
derived inverse limit of the degree-`d` cohomology system vanishes.**

Let `L` be a derived limit of `(Kₙ)` and let every `Kₙ` lie in degrees `≤ d`.  In degree
`i > d` the long exact sequence of the defining triangle
`L ⟶ ∏ₙ Kₙ ⟶ ∏ₙ Kₙ ⟶ L⟦1⟧` makes `Hⁱ(L)` an extension of a subobject of `Hⁱ(∏ₙ Kₙ)` by the
cokernel of the Milnor difference on `H^{i-1}(∏ₙ Kₙ)`.  The first hypothesis makes
`Hⁱ(∏ₙ Kₙ) ≅ ∏ₙ Hⁱ(Kₙ)` vanish for `i > d`, which kills the subobject and also the difference
map's source when `i > d + 1`; the one remaining case `i = d + 1` is the second hypothesis,
`R¹lim H^d(Kₙ) = 0`.

Unlike `Stacks.DerivedLimit.isLE_of_isDerivedLimit_of_isMittagLeffler` this needs no exactness
of the countable products of `A`, so it applies to modules on a site; see the module
documentation. -/
public theorem isLE_of_isDerivedLimit_of_isZero_cokernel
    (E : ℕᵒᵖ ⥤ DerivedCategory A) [HasProduct fun n : ℕ ↦ E.obj ⟨n⟩]
    (L : DerivedCategory A) (hL : IsDerivedLimit E L) (d : ℤ)
    (hE : ∀ n : ℕ, (E.obj ⟨n⟩).IsLE d)
    (hpi : ∀ i : ℤ, d ≤ i →
      IsIso (piComparison (DerivedCategory.homologyFunctor A i) fun n : ℕ ↦ E.obj ⟨n⟩))
    (hR1 : IsZero (cokernel (inverseSystemDifference
      (E ⋙ DerivedCategory.homologyFunctor A d)))) :
    L.IsLE d := by
  obtain ⟨p, q, hT⟩ := hL
  have hT' : Triangle.mk p (inverseSystemDifference E) q ∈ distTriang (DerivedCategory A) := hT
  have hzero : ∀ i : ℤ, d < i →
      IsZero ((DerivedCategory.homologyFunctor A i).obj (∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩)) := by
    intro i hi
    have := hpi i hi.le
    refine IsZero.of_iso ?_ (asIso (piComparison (DerivedCategory.homologyFunctor A i)
      fun n : ℕ ↦ E.obj ⟨n⟩))
    rw [IsZero.iff_id_eq_zero]
    refine Pi.hom_ext _ _ fun n ↦ ?_
    have := hE n
    exact (DerivedCategory.isZero_of_isLE (E.obj ⟨n⟩) d i hi).eq_of_tgt _ _
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have hdiff : Epi ((DerivedCategory.homologyFunctor A (i - 1)).map
      (inverseSystemDifference E)) := by
    rcases eq_or_lt_of_le (show d ≤ i - 1 by omega) with heq | hlt
    · have := hpi d le_rfl
      have : Epi (inverseSystemDifference (E ⋙ DerivedCategory.homologyFunctor A d)) :=
        (Preadditive.epi_iff_isZero_cokernel _).2 hR1
      have key : (DerivedCategory.homologyFunctor A d).map (inverseSystemDifference E) =
          piComparison (DerivedCategory.homologyFunctor A d) (fun n : ℕ ↦ E.obj ⟨n⟩) ≫
            inverseSystemDifference (E ⋙ DerivedCategory.homologyFunctor A d) ≫
              inv (piComparison (DerivedCategory.homologyFunctor A d)
                (fun n : ℕ ↦ E.obj ⟨n⟩)) := by
        rw [← Category.assoc, ← map_inverseSystemDifference_comp_piComparison
          (DerivedCategory.homologyFunctor A d) E, Category.assoc, IsIso.hom_inv_id,
          Category.comp_id]
      rw [← heq, key]
      infer_instance
    · exact ⟨fun g h _ ↦ (hzero (i - 1) hlt).eq_of_src g h⟩
  have : Mono ((DerivedCategory.homologyFunctor A i).map
      (Triangle.mk p (inverseSystemDifference E) q).mor₁) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT' (i - 1) i (by omega),
      ← DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT' (i - 1) i (by omega)]
    exact hdiff
  rw [IsZero.iff_id_eq_zero, ← cancel_mono ((DerivedCategory.homologyFunctor A i).map
    (Triangle.mk p (inverseSystemDifference E) q).mor₁)]
  exact (hzero i hi).eq_of_tgt _ _

end Stacks.DerivedLimit

end
