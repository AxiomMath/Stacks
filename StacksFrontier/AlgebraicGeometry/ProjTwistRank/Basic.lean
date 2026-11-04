module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.Basic
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic

/-!
# The line bundles on projective space have rank one

Let `R` be a commutative ring and write `ℙⁿ_R = Proj R[T₀, …, Tₙ]` for the total-degree grading.
The Serre twist `𝒪(d)` is invertible for every `d : ℤ`, because the standard opens `D₊(Tᵢ)` are
attached to the degree-one elements `Tᵢ` and cover `ℙⁿ_R`; on a scheme an invertible sheaf of
modules is finite locally free of rank one, the stalks of a scheme being local rings. The same
rank-one statement for the structure sheaf `𝒪` is the free sheaf on a one-element index type.

The point of the file is the *spelling*: rank-one-ness is recorded as
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`, which is the class the
exterior-power machinery consumes. With it the exterior powers `⋀^q 𝒪(d)` above the rank vanish:
the rank of `⋀^q` of a rank-one sheaf is `binom(1, q) = 0` for `q ≥ 2`, a sheaf of rank zero has
one-element stalks, and a sheaf of modules with one-element stalks has vanishing identity, hence
is a zero object.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistRank.degreeOneCover_polyGrading`: the standard opens of
  `ℙⁿ_R` are attached to elements of degree one, the hypothesis under which the twists are
  invertible.
* `Stacks.AlgebraicGeometry.ProjTwistRank.isFiniteLocallyFreeOfRank_twistingSheaf`: `𝒪(d)` is
  finite locally free of rank one on `ℙⁿ_R`, for every `d : ℤ`.
* `Stacks.AlgebraicGeometry.ProjTwistRank.isFiniteLocallyFreeOfRank_unit`: the structure sheaf of
  `ℙⁿ_R` is finite locally free of rank one.
* `Stacks.AlgebraicGeometry.ProjTwistRank.exteriorPower_twistingSheaf_eq_zero`: for `q ≥ 2` every
  local section of `⋀^q 𝒪(d)` is zero.
* `Stacks.AlgebraicGeometry.ProjTwistRank.isZero_exteriorPower_twistingSheaf`: for `q ≥ 2` the
  sheaf `⋀^q 𝒪(d)` is a zero object.

## Implementation notes

The two rank-one facts are plain theorems, not instances. Finite local freeness of a fixed rank
quantifies over the objects of the site through its local-generator data, so declaring it as an
instance makes instance search traverse the site; the vanishing statements below therefore name
it as a local hypothesis, as `StacksFrontier/AlgebraicGeometry/ProjKoszulComplex/LocallyFree.lean`
records.

Those local hypotheses carry an explicit `R :=` ascription, because the sheaf of rings of
`ℙⁿ_R` has three definitionally equal spellings — the `sheafCompose` of the `Proj` structure
sheaf that `twistingSheaf` is indexed by, `AlgebraicGeometry.Scheme.ringCatSheaf`, and
`CategoryTheory.Sheaf.toRingCat` — and instance search matches the head syntactically. This is
the discipline of `StacksFrontier/AlgebraicGeometry/DeRham/KunnethDegreewise.lean`.

## References

* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.AlgebraicGeometry.ProjTwistRank

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTrivialization

variable (R : Type u) [CommRing R] (n : ℕ)

/-- **The standard opens `D₊(Tᵢ)` of `ℙⁿ_R` are attached to elements of degree one**, so `ℙⁿ_R`
satisfies the hypothesis of [Stacks, Tag 01MT] under which the Serre twists are invertible. -/
theorem degreeOneCover_polyGrading :
    Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.DegreeOneCover (polyGrading R n) := by
  refine top_le_iff.1 ?_
  rw [← iSup_basicOpen_X_eq_top R n]
  exact iSup_le fun i => le_iSup_of_le ⟨MvPolynomial.X i, X_mem_one R n i⟩ le_rfl

/-- **The Serre twist `𝒪(d)` on `ℙⁿ_R` is finite locally free of rank one**, for every `d : ℤ`.
It is invertible by [Stacks, Tag 01MT], the trivializing section on `D₊(Tᵢ)` being `(Tᵢ/1)^d`,
and on a scheme an invertible sheaf of modules has rank one by clause 2 of [Stacks, Tag 0B8M]. -/
theorem isFiniteLocallyFreeOfRank_twistingSheaf (d : ℤ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) 1 :=
  have := Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertible_twistingSheaf
    (polyGrading R n) (degreeOneCover_polyGrading R n) d
  Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme
    (_root_.AlgebraicGeometry.Proj (polyGrading R n))
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)

/-- **The structure sheaf of `ℙⁿ_R` is finite locally free of rank one**: it is the free sheaf of
modules on a one-element index type. -/
theorem isFiniteLocallyFreeOfRank_unit :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (_root_.SheafOfModules.unit (projRingSheaf (polyGrading R n))) 1 :=
  SheafOfModules.isFiniteLocallyFreeOfRank_unit
    (_root_.AlgebraicGeometry.Proj (polyGrading R n))

/-- **Every local section of `⋀^q 𝒪(d)` vanishes for `q ≥ 2`.** The rank of the degree-`q`
exterior power of a sheaf of rank one is `binom(1, q) = 0`, and a sheaf of modules of rank zero
has one-element stalks, hence only the zero section over every open. -/
theorem exteriorPower_twistingSheaf_eq_zero (d : ℤ) {q : ℕ} (hq : 1 < q)
    (U : (Opens ↥(_root_.AlgebraicGeometry.Proj (polyGrading R n)))ᵒᵖ)
    (z : (Scheme.Modules.exteriorPower
      (X := _root_.AlgebraicGeometry.Proj (polyGrading R n))
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) (q : ℤ)).val.obj U) :
    z = 0 :=
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Sheaf.toRingCat (Opens.grothendieckTopology
          ↥(_root_.AlgebraicGeometry.Proj (polyGrading R n)))
        (_root_.AlgebraicGeometry.Proj (polyGrading R n)).sheaf)
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) 1 :=
    isFiniteLocallyFreeOfRank_twistingSheaf R n d
  Stacks.SheafOfModules.TopWedge.exteriorPower_eq_zero_of_lt
    (Osharp := (_root_.AlgebraicGeometry.Proj (polyGrading R n)).sheaf)
    (_root_.SheafOfModules.algebras _
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)) 1 q hq U z

/-- **`⋀^q 𝒪(d) = 0` on `ℙⁿ_R` for `q ≥ 2`.** The exterior power has rank `binom(1, q) = 0`, so
all its stalks are free of rank zero and in particular have a single element; a sheaf of modules
with that property has vanishing identity, hence is a zero object. -/
theorem isZero_exteriorPower_twistingSheaf (d : ℤ) {q : ℕ} (hq : 1 < q) :
    IsZero (Scheme.Modules.exteriorPower
      (X := _root_.AlgebraicGeometry.Proj (polyGrading R n))
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) (q : ℤ)) := by
  have h1 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := (_root_.AlgebraicGeometry.Proj (polyGrading R n)).ringCatSheaf)
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) 1 :=
    isFiniteLocallyFreeOfRank_twistingSheaf R n d
  have h0 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Sheaf.toRingCat (Opens.grothendieckTopology
          ↥(_root_.AlgebraicGeometry.Proj (polyGrading R n)))
        (_root_.AlgebraicGeometry.Proj (polyGrading R n)).sheaf)
      (Scheme.Modules.exteriorPower
        (X := _root_.AlgebraicGeometry.Proj (polyGrading R n))
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) (q : ℤ)) 0 := by
    have h := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower
      (X := _root_.AlgebraicGeometry.Proj (polyGrading R n))
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) 1 q
    rwa [Nat.choose_eq_zero_of_lt hq] at h
  rw [IsZero.iff_id_eq_zero]
  refine Stacks.SheafOfModules.TopWedge.id_eq_zero_of_subsingleton_stalk _ fun x => ?_
  obtain ⟨e⟩ := Stacks.SheafOfModules.TopWedge.nonempty_stalkLinearEquiv_finsupp
    (Scheme.Modules.exteriorPower
      (X := _root_.AlgebraicGeometry.Proj (polyGrading R n))
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) (q : ℤ)) 0 x
  have : Subsingleton (Fin 0 →₀ ↑(TopCat.Presheaf.stalk
      (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)).obj x)) :=
    ⟨fun a b => Finsupp.ext fun i => i.elim0⟩
  exact e.toEquiv.subsingleton

end Stacks.AlgebraicGeometry.ProjTwistRank

end
