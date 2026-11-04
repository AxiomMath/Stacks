module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingGenericPointField
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingFlatnessChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricLengthStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentChartStalkLocalization

/-!
# The length of a module of rank `r` at a geometric point

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `F` be a quasi-coherent
`𝒪_X`-module which is finite locally free of rank `r` in the sense of the rank clause of Stacks
0409, `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank`. At a geometric point `x̄` of `X`
the length of Stacks 0EE1 of `F` is `r` times the length of the structure sheaf, and so is **`r`
itself** at a geometric point whose étale local ring is a field — in particular at a geometric
point over a generic point of an integral algebraic space. Applied to `f_*𝒪_X` for a finite locally
free morphism `f : X ⟶ Y` of degree `d` (Stacks 03ZV), and to its pullbacks, this gives length `d`.

## Main results

* `length_localizedModule_eq_rankAtStalk_mul`: for a finite flat module over a commutative ring,
  the length of the localization at a prime is the rank at that prime times the length of the local
  ring.
* `exists_affine_smallEtaleNeighborhood_isFiniteLocallyFreeOfRank_sections`: a geometric point has
  a small étale neighbourhood whose chart is affine and over which the sections of a module of rank
  `r` are finite locally free of rank `r`.
* `geometricLength_eq_mul_geometricLength_unit_of_sections` and
  `geometricLength_eq_of_sections_of_isField`: the same two computations from one affine chart on
  which the sections are finite locally free of rank `r`, with no rank condition anywhere else on
  `X`.
* `geometricLength_eq_mul_geometricLength_unit_of_isFiniteLocallyFreeOfRank`: the length of a
  module of rank `r` at a geometric point is `r` times the length of the structure sheaf there.
* `geometricLength_eq_of_isFiniteLocallyFreeOfRank_of_isField`: the length is `r` at a geometric
  point whose étale local ring is a field.
* `geometricLength_eq_of_isFiniteLocallyFreeOfRank_of_mem_genericPoints`: the same on an integral
  algebraic space at a geometric point over a generic point.
* `geometricLength_pushforwardStructureModule_eq_of_isFiniteLocallyFreeOfRank`: a finite locally
  free morphism of degree `d` has `f_*𝒪_X` of length `d` at a geometric point of the target whose
  étale local ring is a field.
* `isFiniteLocallyFreeOfRank_modulePullback_pushforwardStructureModule`: `g^*(f_*𝒪_X)` is finite
  locally free of rank `d` for an arbitrary `g : W ⟶ Y`.
* `geometricLength_modulePullback_pushforwardStructureModule_eq_of_isFiniteLocallyFreeOfRank` and
  `geometricLength_modulePullback_pushforwardStructureModule_eq_of_mem_genericPoints`:
  `g^*(f_*𝒪_X)` has length `d` at a geometric point of `W` whose étale local ring is a field, and
  at a geometric point over a generic point of an integral `W`.

## References

* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The length of a localization of a finite flat module -/

/-- **The length of the localization of a finite flat module at a prime** is the rank there times
the length of the local ring. -/
theorem length_localizedModule_eq_rankAtStalk_mul {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] (p : Ideal R)
    [hp : p.IsPrime] :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M) =
      Module.rankAtStalk M ⟨p, hp⟩ *
        Module.length (Localization.AtPrime p) (Localization.AtPrime p) :=
  have : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  Module.length_of_free_of_finite _ _

/-! ### A chart trivialising a module of rank `r` at a geometric point -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **A geometric point has an affine chart over which the sections of a module of rank `r` are
finite locally free of rank `r`.** -/
theorem exists_affine_smallEtaleNeighborhood_isFiniteLocallyFreeOfRank_sections
    (F : Modules.{u, u} B S hS X.1 X.2) (r : ℕ)
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) F r)
    (xbar : GeometricPoint B S hS X.1) :
    ∃ N : SmallEtaleNeighborhood xbar, IsAffine (chartScheme N.chart) ∧
      Module.IsFiniteLocallyFreeOfRank (chartRing B S hS X.1 X.2 N.chart)
        (F.val.obj (op N.chart)) r := by
  obtain ⟨N₀⟩ := (isCofiltered_smallEtaleNeighborhood B S hS X.1 X.2 xbar).nonempty
  obtain ⟨V, f, hf, q, -⟩ := (etaleSitePoint B S hS X.1 xbar X.2).jointly_surjective
    (Sieve.generate (fun (W : SmallEtale B S hS X.1) (_ : W ⟶ N₀.chart) =>
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) ∧
        Module.IsFiniteLocallyFreeOfRank (chartRing B S hS X.1 X.2 W)
          (F.val.obj (op W)) r))
    (freeRankPresieve_mem_topology_of_isFiniteLocallyFreeOfRank B S hS X.1 X.2 F r hr N₀.chart)
    (show GeometricFiber B S hS X.1 xbar N₀.chart from ⟨N₀.point, N₀.point_comp⟩)
  obtain ⟨Z, g, -, ⟨haff, hfree⟩, -⟩ := hf
  exact ⟨⟨Z, ((geometricFiber B S hS X.1 xbar).map g q).1,
    ((geometricFiber B S hS X.1 xbar).map g q).2⟩, haff, hfree⟩

/-! ### The length of a module of rank `r` -/

/-- **One affine chart on which the sections are finite locally free of rank `r` computes the
length.**  For a quasi-coherent `𝒪_X`-module `F` and a geometric point `x̄` of `X` admitting a
small étale neighbourhood whose chart is affine and over which the sections of `F` are finite
locally free of rank `r`,

`length_{x̄}(F) = r · length_{x̄}(𝒪_X)`. -/
theorem geometricLength_eq_mul_geometricLength_unit_of_sections
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (r : ℕ)
    (xbar : GeometricPoint B S hS X.1) (N : SmallEtaleNeighborhood xbar)
    (haff : IsAffine (chartScheme N.chart))
    (hfree : Module.IsFiniteLocallyFreeOfRank (chartRing B S hS X.1 X.2 N.chart)
      (F.val.obj (op N.chart)) r) :
    geometricLength B S hS X xbar F =
      r * geometricLength B S hS X xbar (SheafOfModules.unit _) := by
  have hu : chartSchemeToPoints B S hS X.1 N.chart (chartPoint B S hS X.1 N) = xbar.image := by
    rw [chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm]
    exact (chartPoint_iff_pointOfEtaleChart_eq B S hS N.chart _ _).mp
      (chartPoint_isChartPoint B S hS xbar N)
  have := Module.finite_of_isFiniteLocallyFreeOfRank hfree
  have := Module.flat_of_isFiniteLocallyFreeOfRank hfree
  have : Module.Finite (chartRing B S hS X.1 X.2 N.chart)
      ((structureSheafModule B S hS X).val.obj (op N.chart)) :=
    inferInstanceAs (Module.Finite (chartRing B S hS X.1 X.2 N.chart)
      (chartRing B S hS X.1 X.2 N.chart))
  have : Module.Flat (chartRing B S hS X.1 X.2 N.chart)
      ((structureSheafModule B S hS X).val.obj (op N.chart)) :=
    inferInstanceAs (Module.Flat (chartRing B S hS X.1 X.2 N.chart)
      (chartRing B S hS X.1 X.2 N.chart))
  rw [geometricLength_eq_length_localizedModule_chartPrimeAt B S hS X F xbar N.chart haff _ hu,
    geometricLength_eq_length_localizedModule_chartPrimeAt B S hS X
      (structureSheafModule B S hS X) xbar N.chart haff _ hu,
    length_localizedModule_eq_rankAtStalk_mul (M := (F.val.obj (op N.chart) : Type u)),
    length_localizedModule_eq_rankAtStalk_mul
      (M := ((structureSheafModule B S hS X).val.obj (op N.chart) : Type u)),
    Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank r hfree]
  have : Nontrivial (chartRing B S hS X.1 X.2 N.chart) := by
    rcases subsingleton_or_nontrivial (chartRing B S hS X.1 X.2 N.chart) with hs | hs
    · exact absurd ((Ideal.eq_top_iff_one _).mpr
        (by rw [Subsingleton.elim (1 : chartRing B S hS X.1 X.2 N.chart) 0]
            exact Submodule.zero_mem _))
        (chartPrimeAt_isPrime B S hS X.2 N.chart (chartPoint B S hS X.1 N)).ne_top
    · exact hs
  rw [show Module.rankAtStalk (R := chartRing B S hS X.1 X.2 N.chart)
      ((structureSheafModule B S hS X).val.obj (op N.chart))
      ⟨chartPrimeAt B S hS X.2 N.chart (chartPoint B S hS X.1 N), inferInstance⟩ = 1 from
    congrFun Module.rankAtStalk_self _]
  rw [Nat.cast_one, one_mul]

/-- **The length of a module of rank `r` at a geometric point is `r` times the length of the
structure sheaf there.**  For a quasi-coherent `𝒪_X`-module `F` which is finite locally free of
rank `r` in the sense of the rank clause of Stacks 0409 and a geometric point `x̄` of `X`,

`length_{x̄}(F) = r · length_{x̄}(𝒪_X)`. -/
theorem geometricLength_eq_mul_geometricLength_unit_of_isFiniteLocallyFreeOfRank
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (r : ℕ)
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) F r)
    (xbar : GeometricPoint B S hS X.1) :
    geometricLength B S hS X xbar F =
      r * geometricLength B S hS X xbar (SheafOfModules.unit _) :=
  let ⟨N, haff, hfree⟩ :=
    exists_affine_smallEtaleNeighborhood_isFiniteLocallyFreeOfRank_sections B S hS X F r hr xbar
  geometricLength_eq_mul_geometricLength_unit_of_sections B S hS X F r xbar N haff hfree

/-- **One affine chart with sections finite locally free of rank `r` gives length `r` at a
geometric point whose étale local ring is a field.** -/
theorem geometricLength_eq_of_sections_of_isField
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (r : ℕ)
    (xbar : GeometricPoint B S hS X.1) (N : SmallEtaleNeighborhood xbar)
    (haff : IsAffine (chartScheme N.chart))
    (hfree : Module.IsFiniteLocallyFreeOfRank (chartRing B S hS X.1 X.2 N.chart)
      (F.val.obj (op N.chart)) r)
    (hfield : IsField (etaleLocalRing B S hS X.1 xbar)) :
    geometricLength B S hS X xbar F = r := by
  rw [geometricLength_eq_mul_geometricLength_unit_of_sections B S hS X F r xbar N haff hfree,
    geometricLength_structureSheafModule_eq_one_of_isField B S hS X xbar hfield, mul_one]

/-- **A module of rank `r` has length `r` at a geometric point whose étale local ring is a
field.** -/
theorem geometricLength_eq_of_isFiniteLocallyFreeOfRank_of_isField
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (r : ℕ)
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) F r)
    (xbar : GeometricPoint B S hS X.1)
    (hfield : IsField (etaleLocalRing B S hS X.1 xbar)) :
    geometricLength B S hS X xbar F = r := by
  rw [geometricLength_eq_mul_geometricLength_unit_of_isFiniteLocallyFreeOfRank B S hS X F r hr
      xbar,
    geometricLength_structureSheafModule_eq_one_of_isField B S hS X xbar hfield, mul_one]

/-- **On an integral algebraic space a module of rank `r` has length `r` at every geometric point
over a generic point.** -/
theorem geometricLength_eq_of_isFiniteLocallyFreeOfRank_of_mem_genericPoints
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (r : ℕ)
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) F r)
    (hint : IsIntegralSpace B S hS X.1) (xbar : GeometricPoint B S hS X.1)
    (hgen : xbar.image ∈ genericPoints (points B S hS X.1)) :
    geometricLength B S hS X xbar F = r :=
  geometricLength_eq_of_isFiniteLocallyFreeOfRank_of_isField B S hS X F r hr xbar
    (isField_etaleLocalRing_of_mem_genericPoints_of_isIntegralSpace B S hS X.2 hint xbar hgen)

/-! ### The direct image of the structure sheaf along a finite locally free morphism -/

/-- **A finite locally free morphism of degree `d` has `f_*𝒪_X` of length `d`** at a geometric
point of the target whose étale local ring is a field. -/
theorem geometricLength_pushforwardStructureModule_eq_of_isFiniteLocallyFreeOfRank
    {Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (d : ℕ)
    (hf : IsFiniteLocallyFreeOfRank B S hS f d) (ybar : GeometricPoint B S hS Y.1)
    (hfield : IsField (etaleLocalRing B S hS Y.1 ybar)) :
    geometricLength B S hS Y ybar (pushforwardStructureModule B S hS f) = d :=
  have : (pushforwardStructureModule B S hS f).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS f hf.1.1 _
      inferInstance
  geometricLength_eq_of_isFiniteLocallyFreeOfRank_of_isField B S hS Y
    (pushforwardStructureModule B S hS f) d hf.2 ybar hfield

/-! ### After an arbitrary base change of the target -/

section BaseChange

variable {Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (d : ℕ)
    (hf : IsFiniteLocallyFreeOfRank B S hS f d) {W : AlgebraicSpaces B S hS} (g : W ⟶ Y)

include hf in
/-- **The direct image of the structure sheaf along a finite locally free morphism of degree `d`
still has rank `d` after an arbitrary pullback of the target.**  For `f : X ⟶ Y` finite locally
free of degree `d` in the sense of Stacks 03ZV and an arbitrary `g : W ⟶ Y`, the pullback
`g^*(f_*𝒪_X)` is finite locally free of rank `d` on the small étale site of `W`. -/
theorem isFiniteLocallyFreeOfRank_modulePullback_pushforwardStructureModule :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS W.1 W.2)
      ((modulePullback B S hS g).obj (pushforwardStructureModule B S hS f)) d :=
  isFiniteLocallyFreeOfRank_modulePullback_of_isQuasicoherentOnSite B S hS g
    (pushforwardStructureModule B S hS f)
    (isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS f hf.1.1 _
      inferInstance) d hf.2

include hf in
/-- **`g^*(f_*𝒪_X)` has length `d`** at a geometric point of `W` whose étale local ring is a
field, for `f` finite locally free of degree `d` and an arbitrary `g : W ⟶ Y`. -/
theorem geometricLength_modulePullback_pushforwardStructureModule_eq_of_isFiniteLocallyFreeOfRank
    (wbar : GeometricPoint B S hS W.1)
    (hfield : IsField (etaleLocalRing B S hS W.1 wbar)) :
    geometricLength B S hS W wbar
        ((modulePullback B S hS g).obj (pushforwardStructureModule B S hS f)) = d :=
  have : ((modulePullback B S hS g).obj
      (pushforwardStructureModule B S hS f)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g _
      (isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS f hf.1.1 _
        inferInstance)
  geometricLength_eq_of_isFiniteLocallyFreeOfRank_of_isField B S hS W _ d
    (isFiniteLocallyFreeOfRank_modulePullback_pushforwardStructureModule B S hS X f d hf g)
    wbar hfield

include hf in
/-- **On an integral `W` the length of `g^*(f_*𝒪_X)` at a geometric point over a generic point
is `d`.** -/
theorem geometricLength_modulePullback_pushforwardStructureModule_eq_of_mem_genericPoints
    (hint : IsIntegralSpace B S hS W.1) (wbar : GeometricPoint B S hS W.1)
    (hgen : wbar.image ∈ genericPoints (points B S hS W.1)) :
    geometricLength B S hS W wbar
        ((modulePullback B S hS g).obj (pushforwardStructureModule B S hS f)) = d :=
  geometricLength_modulePullback_pushforwardStructureModule_eq_of_isFiniteLocallyFreeOfRank
    B S hS X f d hf g wbar
    (isField_etaleLocalRing_of_mem_genericPoints_of_isIntegralSpace B S hS W.2 hint wbar hgen)

end BaseChange

end AlgebraicGeometry.Space

end
