module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.BoundedComplexChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.WhitneyChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneyInvertible
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# Chern classes along an invertible subsheaf, in the Chow cohomology ring

Let `(S, δ)` be as in Situation 02QL and let `X` be locally of finite type over `S`. For a
finite locally free `𝒪_X`-module `ℱ` of rank `r` write `c_j(ℱ) ∈ A^j(X)` for its bivariant Chern
classes (Stacks 0B7H) and `c(ℱ) = c_0(ℱ) + ⋯ + c_r(ℱ)` for its total Chern class in the Chow
cohomology ring `A^*(X) = ⨁_p A^p(X)` (Stacks 0B7E). This file proves the two steps of the
additivity of Chern classes:

* [Stacks, Tag 02UG](https://stacks.math.columbia.edu/tag/02UG): for a short exact sequence
  `0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℱ ⟶ 0` with `ℰ`, `ℱ` finite locally free of ranks `r`, `r - 1`,

    `c_r(ℰ) = 0`  and  `c_j(ℰ) = c_j(ℱ)` for `j = 0, …, r - 1`   in `A^*(X)`;

* [Stacks, Tag 02UH](https://stacks.math.columbia.edu/tag/02UH): for a short exact sequence
  `0 ⟶ ℒ ⟶ ℰ ⟶ ℱ ⟶ 0` with `ℒ` invertible and `ℰ`, `ℱ` finite locally free of ranks `r`, `r - 1`,

    `c(ℰ) = c(ℒ) c(ℱ)`   in `A^*(X)`.

Both are instances of the Whitney sum formula, Stacks 02UI
(`Stacks.Chow.totalChernClassCohomology_eq_mul_of_shortExact_of_rank` and
`Stacks.Chow.totalChern_eq_mul_of_shortExact`), for a subsheaf of rank one. For Stacks 02UG the
additional input is that the total Chern class of `𝒪_X` is `1`: on every test scheme `g : T ⟶ X`
the pullback `g^*𝒪_X` is `𝒪_T`, whose first Chern class cap product vanishes (Stacks 02SP).

## Main results

* `Stacks.Chow.totalChern_eq_one_of_iso_unit` — the total Chern class of a module isomorphic to
  `𝒪_X` is `1`.
* `Stacks.Chow.totalChern_eq_of_shortExact_of_iso_unit` — `c(ℰ) = c(ℱ)` in `∏_{p ≥ 0} A^p(X)`
  for `0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℱ ⟶ 0`.
* `Stacks.Chow.chernClass_eq_of_shortExact_of_iso_unit` — **Stacks 02UG**.
* `Stacks.Chow.totalChernClassCohomology_eq_mul_of_shortExact_of_isInvertible` —
  **Stacks 02UH**.

## References

* [Stacks Project, Tag 02UG](https://stacks.math.columbia.edu/tag/02UG)
* [Stacks Project, Tag 02UH](https://stacks.math.columbia.edu/tag/02UH)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- **The total Chern class of `𝒪_X` is `1`.** For a module `M` isomorphic to the structure
sheaf, `c(M) = 1` in `∏_{p ≥ 0} A^p(X)`: on a test scheme `g : T ⟶ X` the pullback `g^*M` is
isomorphic to `𝒪_T`, whose total Chern class is `1` by Stacks 02SP. -/
theorem totalChern_eq_one_of_iso_unit (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1]
    (e : M ≅ SheafOfModules.unit Y.ringCatSheaf) : totalChern C sY M 1 = 1 := by
  refine TotalChowClass.ext_op fun g _ ↦ ?_
  rw [op_totalChern, TotalChowClass.op_one]
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj M) 1 :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g M 1
  exact GenuineChern.chernFamily_eq_one_of_iso_unit C (g ≫ sY) _
    ((Scheme.Modules.pullback g).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso g)

/-- A module isomorphic to `𝒪_X` is finite locally free of rank one. -/
private theorem isFiniteLocallyFreeOfRank_one_of_iso_unit {M : Y.Modules}
    (e : M ≅ SheafOfModules.unit Y.ringCatSheaf) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1 :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e.symm
    (GenuineChern.isFiniteLocallyFreeOfRank_one_of_isInvertible _)

/-- In `0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℱ ⟶ 0` with `ℰ`, `ℱ` of ranks `r`, `r - 1`, the rank `r` is `1 + (r - 1)`. -/
private theorem rank_eq_one_add_of_iso_unit (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    (e : S.X₁ ≅ SheafOfModules.unit Y.ringCatSheaf) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ (r - 1)] (y : Y) :
    r = 1 + (r - 1) := by
  have := isFiniteLocallyFreeOfRank_one_of_iso_unit e
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_unique S.X₂ ‹_›
    (GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact S hS 1 (r - 1) ‹_› ‹_›) y

/-- **`c(ℰ) = c(ℱ)` along a trivial subsheaf**, in the ring `∏_{p ≥ 0} A^p(X)` of total classes.
For a short exact sequence `0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℱ ⟶ 0` with `ℰ`, `ℱ` finite locally free of ranks `r`,
`r - 1`, the total Chern classes of `ℰ` and `ℱ` agree. -/
theorem totalChern_eq_of_shortExact_of_iso_unit (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    (e : S.X₁ ≅ SheafOfModules.unit Y.ringCatSheaf) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ (r - 1)] :
    totalChern C sY S.X₂ r = totalChern C sY S.X₃ (r - 1) := by
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y⟩⟩
  · have := TotalChowClass.subsingleton_of_isEmpty (C := C) sY
    exact Subsingleton.elim _ _
  have := isFiniteLocallyFreeOfRank_one_of_iso_unit e
  have h₂ := GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact S hS 1 (r - 1) ‹_› ‹_›
  have hr := rank_eq_one_add_of_iso_unit S hS e r y
  calc totalChern C sY S.X₂ r = totalChern C sY S.X₂ (1 + (r - 1)) :=
        totalChern_congr C sY (Iso.refl _) hr
    _ = totalChern C sY S.X₁ 1 * totalChern C sY S.X₃ (r - 1) :=
        totalChern_eq_mul_of_shortExact C sY S hS 1 (r - 1)
    _ = totalChern C sY S.X₃ (r - 1) := by
        rw [totalChern_eq_one_of_iso_unit C sY S.X₁ e, one_mul]

/-- **`c_r(ℰ) = 0` along a trivial subsheaf.** For a short exact sequence
`0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℱ ⟶ 0` with `ℰ`, `ℱ` finite locally free of ranks `r`, `r - 1`, the top Chern
class `c_r(ℰ) ∈ A^r(X)` vanishes. -/
theorem chernClass_last_eq_zero_of_shortExact_of_iso_unit (S : ShortComplex Y.Modules)
    (hS : S.ShortExact) (e : S.X₁ ≅ SheafOfModules.unit Y.ringCatSheaf) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ (r - 1)] :
    GenuineChern.chernClass C sY S.X₂ r (Fin.last r) = 0 := by
  rw [← totalChern_apply C sY S.X₂ r (Fin.last r)]
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y⟩⟩
  · have := TotalChowClass.subsingleton_of_isEmpty (C := C) sY
    rw [Subsingleton.elim (totalChern C sY S.X₂ r) 0]
    rfl
  have := isFiniteLocallyFreeOfRank_one_of_iso_unit e
  have hr := rank_eq_one_add_of_iso_unit S hS e r y
  rw [totalChern_eq_of_shortExact_of_iso_unit C sY S hS e r]
  exact totalChern_apply_of_lt C sY S.X₃ (r - 1) (by simp only [Fin.val_last]; omega)

/-- **`c_j(ℰ) = c_j(ℱ)` along a trivial subsheaf.** For a short exact sequence
`0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℱ ⟶ 0` with `ℰ`, `ℱ` finite locally free of ranks `r`, `r - 1`, the Chern classes
`c_j(ℰ)` and `c_j(ℱ)` agree in `A^j(X)` for `j = 0, …, r - 1`. -/
theorem chernClass_castSucc_eq_of_shortExact_of_iso_unit (S : ShortComplex Y.Modules)
    (hS : S.ShortExact) (e : S.X₁ ≅ SheafOfModules.unit Y.ringCatSheaf) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ (r - 1)]
    (j : Fin r) :
    GenuineChern.chernClass C sY S.X₂ r j.castSucc =
      GenuineChern.chernClass C sY S.X₃ (r - 1) ⟨j, by omega⟩ := by
  rw [← totalChern_apply C sY S.X₂ r j.castSucc,
    ← totalChern_apply C sY S.X₃ (r - 1) ⟨j, by omega⟩,
    totalChern_eq_of_shortExact_of_iso_unit C sY S hS e r]
  rfl

/-- **Stacks 02UG.** Let `X` be locally of finite type over the base and let
`0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℱ ⟶ 0` be a short exact sequence of `𝒪_X`-modules with `ℰ`, `ℱ` finite locally
free of ranks `r`, `r - 1`. Then

  `c_r(ℰ) = 0`,  `c_j(ℰ) = c_j(ℱ)`, `j = 0, …, r - 1`,

in the Chow cohomology ring `A^*(X) = ⨁_p A^p(X)` of Stacks 0B7E, the `c_j` being the bivariant
Chern classes of Stacks 0B7H placed in their degree. No hypothesis beyond the source's is taken.
The equivalent form on cap products is
`Stacks.Chow.GenuineChern.chernCap_eq_of_shortExact_of_iso_unit`. -/
@[stacks 02UG "c_r(E) = 0 and c_j(E) = c_j(F) for j = 0, ..., r - 1 in the Chow cohomology ring \
  A^*(X) of Stacks 0B7E, for a short exact sequence 0 -> O_X -> E -> F -> 0 on X locally of finite \
  type over the base with E, F finite locally free of ranks r, r - 1; c_j is the bivariant Chern \
  class of Stacks 0B7H in A^j(X); unconditional, under exactly the source's hypotheses"]
theorem chernClass_eq_of_shortExact_of_iso_unit (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    (e : S.X₁ ≅ SheafOfModules.unit Y.ringCatSheaf) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ (r - 1)] :
    DirectSum.of (fun p ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) (r : ℤ)
        (GenuineChern.chernClass C sY S.X₂ r (Fin.last r)) = 0 ∧
      ∀ j : Fin r,
        DirectSum.of (fun p ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sY p)
            (j : ℤ) (GenuineChern.chernClass C sY S.X₂ r j.castSucc) =
          DirectSum.of (fun p ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sY p)
            (j : ℤ) (GenuineChern.chernClass C sY S.X₃ (r - 1) ⟨j, by omega⟩) := by
  refine ⟨?_, fun j ↦ ?_⟩
  · rw [chernClass_last_eq_zero_of_shortExact_of_iso_unit C sY S hS e r, map_zero]
  · rw [chernClass_castSucc_eq_of_shortExact_of_iso_unit C sY S hS e r j]

/-- **Stacks 02UH.** Let `X` be locally of finite type over the base and let
`0 ⟶ ℒ ⟶ ℰ ⟶ ℱ ⟶ 0` be a short exact sequence of `𝒪_X`-modules with `ℒ` invertible and `ℰ`, `ℱ`
finite locally free of ranks `r`, `r - 1`. Then

  `c(ℰ) = c(ℒ) c(ℱ)`

in the Chow cohomology ring `A^*(X)` of Stacks 0B7E, `ℒ` being finite locally free of rank one
(Stacks 0B8M). This is the Whitney sum formula, Stacks 02UI, for a subsheaf of rank one. -/
@[stacks 02UH "c(E) = c(L) c(F) in the Chow cohomology ring A^*(X) of Stacks 0B7E, for a short \
  exact sequence 0 -> L -> E -> F -> 0 on X locally of finite type over the base with L \
  invertible and E, F finite locally free of ranks r, r - 1; c(G) is the sum in A^*(X) of the \
  bivariant Chern classes c_j(G) of Stacks 0B7H"]
theorem totalChernClassCohomology_eq_mul_of_shortExact_of_isInvertible
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property S.X₁]
    (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ (r - 1)] :
    letI := chowCohomologyRingOfInvertible C sY
    haveI := GenuineChern.isFiniteLocallyFreeOfRank_one_of_isInvertible S.X₁
    totalChernClassCohomology C sY S.X₂ r =
      totalChernClassCohomology C sY S.X₁ 1 * totalChernClassCohomology C sY S.X₃ (r - 1) := by
  have := GenuineChern.isFiniteLocallyFreeOfRank_one_of_isInvertible S.X₁
  exact totalChernClassCohomology_eq_mul_of_shortExact_of_rank C sY S hS 1 r (r - 1)

end Stacks.Chow

end
