module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupVanishingUniverseLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.TorsionGaloisVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.HighDegreeVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of the Galois cohomology of the multiplicative group in every positive degree

Let `K` be a field and `Ω` a separably closed Galois extension of `K`, and assume that
`Br(K') = 0` for every finite extension `K'/K`. Then `H^q(Gal(Ω/K), Ωˣ) = 0` for every `q ≥ 1`,
the groups being the continuous group cohomology of the discrete Galois module
`Stacks.GaloisCohomology.unitsContinuousGModule`.

## Main results

* `isProfiniteTop_galGroup`: the Galois group of a Galois extension is profinite for the Krull
  topology.
* `isZero_continuousGroupCohomology_units_of_forall_brauer`: `H^q(Gal(Ω/K), Ωˣ) = 0` for every
  `q ≥ 1` when `Br(K') = 0` for every finite extension `K'/K`.
* `isZero_continuousGroupCohomology_unitsLift_of_forall_brauer`: the same statement with
  coefficients in `unitsContinuousGModuleLift`, in a raised coefficient universe.
* `isZero_continuousGroupCohomology_separableClosureUnits_of_forall_brauer`: the statement at
  `Ω = Kˢᵉᵖ`.

## References

* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8)
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.GaloisCohomology

/-- The Galois group of a Galois extension is profinite: for the Krull topology it is compact,
Hausdorff and totally disconnected. -/
theorem isProfiniteTop_galGroup (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] :
    Stacks.Chapter05.Tag_0BR1.IsProfiniteTop Gal(Ω/K) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- Let `Ω` be a separably closed Galois extension of a field `K` and assume `Br(K') = 0` for
every finite extension `K'/K`. Then `H^q(Gal(Ω/K), Ωˣ) = 0` for every `q ≥ 1`, the group being
the continuous group cohomology of the discrete Galois module
`Stacks.GaloisCohomology.unitsContinuousGModule`. -/
@[stacks 03R8 "part (1) IN FULL, for the DERIVED-FUNCTOR groups continuousGroupCohomology of
Stacks 04JR: H^q(Gal(Ω/K), Ωˣ) = 0 for EVERY q ≥ 1, where Ω is any separably closed field Galois
over K, so at Ω = K^sep this is exactly the tag's part (1). The Brauer hypothesis is the source's
own -- Br(K') = 0 for every finite extension K'/K -- and the degree range is the source's.
Degrees one and two are the two earlier registrations in
MultiplicativeGroupVanishingCriterion (Hilbert 90 through the degree-one comparison, and the
crossed-product argument through the degree-two comparison, the latter needing only Br(K) = 0).
Degrees q ≥ 3 are part (2), the registration in TorsionGaloisVanishing, through
isZero_continuousGroupCohomology_of_forall_isAddTorsion: multiplication by a positive integer n
on a discrete module has kernel and cokernel killed by n, so part (2) and two passes of the long
exact sequence of the δ-functor of Stacks 010Q make it injective on H^q for q ≥ 3, while every
class is killed by some positive integer by Stacks 0DV3 part (1). This registration is part (1);
part (2) is the registration in TorsionGaloisVanishing and the degree-one and degree-two
statements keep their own registrations in MultiplicativeGroupVanishingCriterion",
  sga "4½ Arcata 3.1.6"]
theorem isZero_continuousGroupCohomology_units_of_forall_brauer (K Ω : Type u) [Field K]
    [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
    (hBr : ∀ (K' : Type u) [Field K'] [Algebra K K'] [Module.Finite K K']
      (y : BrauerGroup K'), y = 1)
    (q : ℕ) (hq : 1 ≤ q) :
    IsZero (continuousGroupCohomology.{u, u} Gal(Ω/K) q (unitsContinuousGModule K Ω)) := by
  rcases (by omega : q = 1 ∨ q = 2 ∨ 3 ≤ q) with rfl | rfl | h3
  · exact isZero_continuousGroupCohomology_units_one K Ω
  · exact isZero_continuousGroupCohomology_units_two K Ω (hBr K)
  · exact Stacks.GroupCohomology.isZero_continuousGroupCohomology_of_forall_isAddTorsion.{u, u}
      (isProfiniteTop_galGroup K Ω) (fun N hN r hr ↦
        isZero_continuousGroupCohomology_of_isAddTorsion.{u, u} K Ω
          (fun L hL y ↦ by have := hL; exact hBr ↥L y) N hN r hr)
      (unitsContinuousGModule K Ω) q h3

/-- Let `Ω` be a separably closed Galois extension of a field `K` and assume `Br(K') = 0` for
every finite extension `K'/K`. Then `H^q(Gal(Ω/K), -) = 0` for every `q ≥ 1` with coefficients in
`Stacks.GaloisCohomology.unitsContinuousGModuleLift`, whose carrier is `ULift (Additive Ωˣ)`. -/
theorem isZero_continuousGroupCohomology_unitsLift_of_forall_brauer.{w, x} (K Ω : Type w)
    [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
    (hBr : ∀ (K' : Type w) [Field K'] [Algebra K K'] [Module.Finite K K']
      (y : BrauerGroup K'), y = 1)
    (q : ℕ) (hq : 1 ≤ q) :
    IsZero (continuousGroupCohomology.{w, x} Gal(Ω/K) q
      (unitsContinuousGModuleLift.{w, x} K Ω)) := by
  rcases (by omega : q = 1 ∨ q = 2 ∨ 3 ≤ q) with rfl | rfl | h3
  · exact isZero_continuousGroupCohomology_unitsLift_one.{w, x} K Ω
  · exact isZero_continuousGroupCohomology_unitsLift_two.{w, x} K Ω (hBr K)
  · exact Stacks.GroupCohomology.isZero_continuousGroupCohomology_of_forall_isAddTorsion.{w, x}
      (isProfiniteTop_galGroup K Ω) (fun N hN r hr ↦
        isZero_continuousGroupCohomology_of_isAddTorsion.{w, x} K Ω
          (fun L hL y ↦ by have := hL; exact hBr ↥L y) N hN r hr)
      (unitsContinuousGModuleLift.{w, x} K Ω) q h3

/-- If `Br(K') = 0` for every finite extension `K'/K` then the continuous cohomology of the
absolute Galois group of `K` with coefficients in `(Kˢᵉᵖ)ˣ` vanishes in every degree `q ≥ 1`. -/
@[sga "4½ Arcata 3.1.6"]
theorem isZero_continuousGroupCohomology_separableClosureUnits_of_forall_brauer (K : Type u)
    [Field K]
    (hBr : ∀ (K' : Type u) [Field K'] [Algebra K K'] [Module.Finite K K']
      (y : BrauerGroup K'), y = 1)
    (q : ℕ) (hq : 1 ≤ q) :
    IsZero (continuousGroupCohomology.{u, u} Gal(SeparableClosure K/K) q
      (unitsContinuousGModule K (SeparableClosure K))) :=
  isZero_continuousGroupCohomology_units_of_forall_brauer K (SeparableClosure K) hBr q hq

end Stacks.GaloisCohomology

end
