module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.RestrictionGeneral
import StacksCore.Tactic.StacksAttribute

/-!
# An `m`-pseudo-coherent object of `D(O)` is locally bounded above

Let `(C, O)` be a ringed site and let `E` be an `m`-pseudo-coherent object of `D(O)`. Then every
object `U` of `C` admits a covering over each member `V` of which the cohomology of `E|_V`
vanishes in all sufficiently large degrees.

This is the ringed-site form of
`AlgebraicGeometry.RingedSpace.exists_isZero_homology_gt_derivedRestrict`
(`StacksFrontier/AlgebraicGeometry/PseudoCoherent/BoundedAbove.lean`), which is stated for a ringed
*space* and produces an open neighbourhood of a point; on a site the "neighbourhood of a point"
becomes a member of a covering presieve. It is the reduction "after shrinking we may assume `E`
is bounded above" of the proof of Stacks 09VA, which is what lets an induction on the
cohomological gap start.

The argument is the one of the source: a strictly perfect approximation `𝒫 ⟶ E|_V` is an
isomorphism on cohomology in every degree above `m`, and `𝒫` has only finitely many nonzero
terms, so the cohomology of `E|_V` vanishes above the larger of `m` and the top degree of `𝒫`.

## Main results

* `AlgebraicGeometry.RingedSite.exists_forall_gt_isZero_X`: a strictly perfect complex has
  vanishing terms in all sufficiently large degrees.
* `AlgebraicGeometry.RingedSite.exists_local_isZero_homology_gt_general`: the local bound on an
  `m`-pseudo-coherent object.

## References

* [Stacks Project, Tag 09VA](https://stacks.math.columbia.edu/tag/09VA)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d d'

namespace AlgebraicGeometry.RingedSite

/-- **A strictly perfect complex has vanishing terms in all sufficiently large degrees.** Only
finitely many of its terms are nonzero, and a finite set of integers is bounded above. -/
theorem exists_forall_gt_isZero_X {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) [HasSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {P : CochainComplex (SheafOfModules.{w} R) ℤ}
    (hP : IsStrictlyPerfect R P) : ∃ a : ℤ, ∀ j : ℤ, a < j → IsZero (P.X j) := by
  obtain ⟨a, ha⟩ := hP.bounded.bddAbove
  refine ⟨a, fun j hj => ?_⟩
  by_contra hne
  exact absurd (ha (show j ∈ {i : ℤ | ¬ IsZero (P.X i)} from hne)) (by omega)

section Main

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

-- Restriction to a slice of the site preserves finite limits and finite colimits. Both are
-- `local instance`s of
-- `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/LocalNature.lean`, so the
-- declarations are imported and only the instance attribute has to be re-enabled here.
attribute [local instance] ovFunctorLimits ovFunctorColimits

/-- **An `m`-pseudo-coherent object of `D(O)` is bounded above locally.** Every object `U` of the
site admits a covering presieve over each member `V` of which there is an integer `b` with
`H^j(E)|_V = 0` for every `j > b`.

The strictly perfect approximation `𝒫 ⟶ E|_V` that `m`-pseudo-coherence supplies over a member of
a covering of `U` is an isomorphism on cohomology above `m`, and `𝒫` has vanishing terms above
some degree `a` (`AlgebraicGeometry.RingedSite.exists_forall_gt_isZero_X`); so `b = max a m`
works.

The conclusion is stated as vanishing of the *restriction of the cohomology sheaf* rather than of
the cohomology of the restriction — the two agree because restriction to a slice is exact — so
that no derived category of a slice enters, and hence no derived-category model has to be
hypothesised on the slices. -/
theorem exists_local_isZero_homology_gt_general
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (m : ℤ)
    (hE : X.IsPseudoCoherentFrom E m) (U : X.C) :
    ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f → ∃ b : ℤ, ∀ j : ℤ, b < j →
        IsZero ((((DerivedCategory.homologyFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).obj E)).over V) := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := hE
  obtain ⟨S, hS, hdata⟩ := hK U
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  obtain ⟨P, hP, α, hα, -⟩ := hdata f hf
  obtain ⟨a, ha⟩ :=
    exists_forall_gt_isZero_X ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) hP
  refine ⟨max a m, fun j hj => ?_⟩
  have hPj : IsZero (P.homology j) :=
    ShortComplex.isZero_homology_of_isZero_X₂ (P.sc j)
      (ha j (lt_of_le_of_lt (le_max_left a m) hj))
  have hKj : IsZero ((X.restrictComplex K V).homology j) := by
    have := hα j (lt_of_le_of_lt (le_max_right a m) hj)
    exact hPj.of_iso (asIso (HomologicalComplex.homologyMap α j)).symm
  refine hKj.of_iso ?_
  refine
    (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapIso ?_ ≪≫
      (ShortComplex.mapHomologyIso (K.sc j)
        (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V)).symm
  exact ((DerivedCategory.homologyFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).mapIso eK).symm ≪≫
    (DerivedCategory.homologyFunctorFactors
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).app K

end Main

end AlgebraicGeometry.RingedSite

end
