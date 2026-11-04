module

public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietorisAndLimits.DerivedLimitLocalBound

/-!
# Convergence of the truncation tower from a cohomological dimension bound on a basis

Let `(X, 𝒪_X)` be a ringed space and `E` an object of `D(𝒪_X)`. If there are an integer `d ≥ 0`
and a basis `𝔅` for the topology of `X` on whose members `Hᵖ(U, Hᵠ(E))` vanishes whenever `p > d`
and `q < 0`, then the canonical map from `E` to a derived limit of its tower of truncations
`τ_{≥ -n} E` is an isomorphism in `D(𝒪_X)`.

## Main results

* `Stacks.Cohomology.DerivedLimitStalk.isIso_to_isDerivedLimit_truncGETower_of_dimension_bound`:
  Tag 0D64.

## Implementation notes

This is Tag 0D63 with `dₓ = d` and `𝔘ₓ = {U ∈ 𝔅 | x ∈ U}`: the members of a basis that contain a
given point form a fundamental system of open neighbourhoods of that point.

## References

* [Stacks Project, Tag 0D63](https://stacks.math.columbia.edu/tag/0D63)
* [Stacks Project, Tag 0D64](https://stacks.math.columbia.edu/tag/0D64)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open Stacks.Cohomology.CohomologyPresheaf

universe wX wP u

namespace Stacks.Cohomology.DerivedLimitStalk

/-- The members of a basis for the topology of `X` that contain a point `x` form a fundamental
system of open neighbourhoods of `x`. -/
private lemma hasBasis_nhds_of_opensIsBasis {X : TopCat.{u}} (x : X) (𝔅 : Set (Opens X))
    (h𝔅 : Opens.IsBasis 𝔅) :
    (nhds x).HasBasis (fun U : Opens X ↦ U ∈ {U : Opens X | U ∈ 𝔅 ∧ x ∈ U})
      (fun U ↦ (U : Set X)) := by
  refine ⟨fun t ↦ ⟨fun ht ↦ ?_, ?_⟩⟩
  · obtain ⟨V, hVt, hVopen, hxV⟩ := mem_nhds_iff.mp ht
    obtain ⟨U, hU𝔅, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.mp h𝔅 (U := ⟨V, hVopen⟩) hxV
    exact ⟨U, ⟨hU𝔅, hxU⟩, subset_trans hUV hVt⟩
  · rintro ⟨U, ⟨-, hxU⟩, hUt⟩
    exact mem_nhds_iff.mpr ⟨U, hUt, U.isOpen, hxU⟩

/-- **Convergence of the truncation tower, at a given derived limit, from a dimension bound on a
basis.** Let `E` be an object of the derived category of sheaves of `𝒪_X`-modules on a ringed
space, and suppose there are an integer `d ≥ 0` and a basis `𝔅` for the topology of `X` on whose
members `Hᵖ(U, Hᵠ(E))` vanishes whenever `p > d` and `q < 0`. Then for every derived limit `L`
of the tower of truncations `τ_{≥ -n} E`, presented by `pr` and `hL`, every canonical map
`c : E ⟶ L` is an isomorphism. -/
public theorem isIso_to_isDerivedLimit_truncGETower_of_dimension_bound {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)]
    (E : DerivedCategory (SheafOfModules.{u} O))
    (d : ℕ) (𝔅 : Set (Opens X)) (h𝔅 : Opens.IsBasis 𝔅)
    (hvanishing : ∀ U ∈ 𝔅, ∀ (p : ℕ) (q : ℤ), (d : ℤ) < (p : ℤ) → q < 0 →
      IsZero ((PresheafOfModules.evaluation O.obj (Opposite.op U)).obj
        (cohomologyPresheaf O
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) 0).obj
            ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) q).obj E))
          (p : ℤ))))
    (L : DerivedCategory (SheafOfModules.{u} O)) (c : E ⟶ L)
    (pr : L ⟶ ∏ᶜ fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk pr (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) (n + 1) ≫
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).map
              (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{u} O)))
    (hc : ∀ n : ℕ, c ≫ pr ≫ Pi.π
      (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n =
      (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c :=
  isIso_to_isDerivedLimit_truncGETower_of_local_bound.{wX, wP, u} O E
    (fun x ↦ ⟨d, {U : Opens X | U ∈ 𝔅 ∧ x ∈ U}, hasBasis_nhds_of_opensIsBasis x 𝔅 h𝔅,
      fun U hU ↦ hvanishing U hU.1⟩) L c pr hL hc

/-- **Stacks Project, Tag 0D64.** Let `E` be an object of the derived category of sheaves of
`𝒪_X`-modules on a ringed space, and suppose there are an integer `d ≥ 0` and a basis `𝔅` for the
topology of `X` on whose members `Hᵖ(U, Hᵠ(E))` vanishes whenever `p > d` and `q < 0`. Then the
tower of truncations `τ_{≥ -n} E` from below has a derived limit `R lim τ_{≥ -n} E` with a
canonical map of Remark 0H72 from `E`, and every such canonical map to every derived limit of the
tower is an isomorphism. -/
@[stacks 0D64 "the derived limit and the canonical map of Remark 0H72 exist, and every such \
canonical map is an isomorphism"]
public theorem exists_and_forall_isIso_to_derivedLimit_truncGETower_of_dimension_bound
    {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)]
    (E : DerivedCategory (SheafOfModules.{u} O))
    (d : ℕ) (𝔅 : Set (Opens X)) (h𝔅 : Opens.IsBasis 𝔅)
    (hvanishing : ∀ U ∈ 𝔅, ∀ (p : ℕ) (q : ℤ), (d : ℤ) < (p : ℤ) → q < 0 →
      IsZero ((PresheafOfModules.evaluation O.obj (Opposite.op U)).obj
        (cohomologyPresheaf O
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) 0).obj
            ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) q).obj E))
          (p : ℤ)))) :
    (∃ (_ : HasProduct fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩)
      (L : DerivedCategory (SheafOfModules.{u} O)) (c : E ⟶ L)
      (pr : L ⟶ ∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩),
      (∃ δ : (∏ᶜ fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
        Triangle.mk pr (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦
              (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) (n + 1) ≫
              (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).map
                (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang (DerivedCategory (SheafOfModules.{u} O))) ∧
      (∀ n : ℕ, c ≫ pr ≫ Pi.π
        (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E)) ∧
    ∀ (L : DerivedCategory (SheafOfModules.{u} O)) (c : E ⟶ L)
      (pr : L ⟶ ∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩),
      (∃ δ : (∏ᶜ fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
        Triangle.mk pr (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦
              (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) (n + 1) ≫
              (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).map
                (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang (DerivedCategory (SheafOfModules.{u} O))) →
      (∀ n : ℕ, c ≫ pr ≫ Pi.π
        (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) →
      IsIso c :=
  ⟨exists_presented_derivedLimit_truncGETower O E, fun L c pr hL hc ↦
    isIso_to_isDerivedLimit_truncGETower_of_dimension_bound O E d 𝔅 h𝔅 hvanishing L c pr hL hc⟩

end Stacks.Cohomology.DerivedLimitStalk

end
