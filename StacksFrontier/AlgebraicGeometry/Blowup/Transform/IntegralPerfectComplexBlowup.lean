module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.PerfectComplexAdmissibleBlowup
public import StacksFrontier.Homology.Perfect.BoundedComplexGenericFreeness

/-!
# A perfect complex on an integral scheme after a blowup

Let `X` be an integral scheme and `E ∈ D(𝒪_X)` perfect. Stacks 0ESR produces a nonempty open
`U ⊆ X` on which every `H^i(E|_U)` is finite locally free of a constant rank `r_i`, and a
`U`-admissible blowup after which every `H^i(Lb^*E)` is perfect of Tor dimension at most one.
No finiteness hypothesis on `X` is needed.

## Main results

* `AlgebraicGeometry.exists_nonempty_open_forall_isFiniteLocallyFreeOfRank`: the nonempty open
  of constant ranks.
* `AlgebraicGeometry.exists_nonempty_open_admissibleBlowup_forall_isHomologyPerfectTorLEOne`:
  **Stacks 0ESR**.

## Implementation notes

The source finds `U` through the derived fibre at the generic point and Stacks 0DI8. Here `U` is
read off an affine chart `(V, M^•)` of `E` through the generic point: `Γ(X, V)` is a domain, so
for each differential of `M^•` there is a size `ρ` with a nonzero `ρ × ρ` minor and no nonzero
larger minor; after inverting the product `δ` of such minors the cohomology of
`M^• ⊗ Γ(X, V)_δ` is finite locally free of constant ranks
(`BoundedComplex.exists_isFiniteLocallyFreeOfRank_homology_of_isLocalization_away`), and the
chart identifies the cohomology sheaves of `E` on `D(δ)` with the associated sheaves. The second
half is Stacks 0ESQ, a nonempty open of an integral scheme being scheme-theoretically dense.

## References

* [Stacks Project, Tag 0ESR](https://stacks.math.columbia.edu/tag/0ESR)
* [Stacks Project, Tag 0ESQ](https://stacks.math.columbia.edu/tag/0ESQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect
open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.TorAmplitude
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry

open ComplexAndDivisorSituation

/-- **The first half of Stacks 0ESR.** On an integral scheme a perfect object has a nonempty open
on which every cohomology sheaf is finite locally free of a constant rank. -/
theorem exists_nonempty_open_forall_isFiniteLocallyFreeOfRank (X : Scheme.{u}) [IsIntegral X]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (perfect : IsPerfect.{u, u, u + 1} E) :
    ∃ (U : X.Opens) (r : ℤ → ℕ), (U : Set X).Nonempty ∧
      ∀ i : ℤ, SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} U.toScheme.toRingedSpace) i).obj
          ((derivedPullback U.ι.toLRSHom.toShHom).obj E)) (r i) := by
  obtain ⟨C, hηC⟩ := ofPerfect_cover perfect (genericPoint X)
  have : Nonempty (C.U : X.Opens) := ⟨⟨_, hηC⟩⟩
  obtain ⟨δ, hδ, s, -, hs⟩ :=
    C.complex.exists_isFiniteLocallyFreeOfRank_homology_of_isLocalization_away
  let V : X.affineOpens := X.affineBasicOpen δ
  have hVne : ((V : X.Opens) : Set X).Nonempty := Set.nonempty_iff_ne_empty.2 fun h =>
    hδ ((basicOpen_eq_bot_iff δ).mp (TopologicalSpace.Opens.ext h))
  have hVC : (V : X.Opens) ≤ (C.U : X.Opens) := X.basicOpen_le δ
  let C' := C.restrict V hVC
  let : Algebra Γ(X, C.U) Γ(X, C'.U) := (X.presheaf.map (homOfLE hVC).op).hom.toAlgebra
  have : IsLocalization.Away δ Γ(X, C'.U) := C.U.2.isLocalization_basicOpen δ
  refine ⟨V, s, hVne, fun i => ?_⟩
  have h₁ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (tilde (R := CommRingCat.of Γ(X, C'.U))
        (ModuleCat.of Γ(X, C'.U) (C'.complex.toCochainComplex.homology i))) (s i) :=
    (Stacks.Modules.tilde_isFiniteLocallyFreeOfRank_iff_module (R := Γ(X, C'.U))
      (M := C'.complex.toCochainComplex.homology i) (s i)).2 (hs Γ(X, C'.U) i)
  have h₂ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((AffineChart.chartTilde C').obj
        ((HomologicalComplex.homologyFunctor (ModuleCat Γ(X, C'.U)) (ComplexShape.up ℤ) i).obj
          C'.complex.toCochainComplex)) (s i) :=
    (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ (s i)).1
      (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ (s i)).2 h₁).restrict C'.U.2.isoSpec.hom)
  have h₃ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.restrictFunctor (V : X.Opens).ι).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj E)) (s i) :=
    Scheme.Modules.isFiniteLocallyFreeOfRankSheaf_of_iso
      (AffineChart.chartHomologyIso C' i).symm h₂
  exact Scheme.Modules.isFiniteLocallyFreeOfRankSheaf_of_iso
    (homologyDerivedPullbackIsoRestrict X V i E).symm h₃

/-- **Stacks Project, Tag 0ESR.** Let `X` be an integral scheme and let `E ∈ D(𝒪_X)` be perfect.
Then there is a nonempty open `U ⊆ X` such that `H^i(E|_U)` is finite locally free of constant
rank `r_i` for every `i`, and a `U`-admissible blowup `b : X' ⟶ X` such that `H^i(Lb^*E)` is a
perfect `𝒪_{X'}`-module of Tor dimension at most one for every `i`. -/
@[stacks 0ESR]
theorem exists_nonempty_open_admissibleBlowup_forall_isHomologyPerfectTorLEOne
    (X : Scheme.{u}) [IsIntegral X] (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (perfect : IsPerfect.{u, u, u + 1} E) :
    ∃ (U : X.Opens) (r : ℤ → ℕ), (U : Set X).Nonempty ∧
      (∀ i : ℤ, SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} U.toScheme.toRingedSpace) i).obj
          ((derivedPullback U.ι.toLRSHom.toShHom).obj E)) (r i)) ∧
      ∃ (X' : Scheme.{u}) (b : X' ⟶ X),
        Stacks.Blowup.IsAdmissibleBlowup U b ∧ ∀ i : ℤ, IsHomologyPerfectTorLEOne E b i := by
  obtain ⟨U, r, hne, hrank⟩ := exists_nonempty_open_forall_isFiniteLocallyFreeOfRank X E perfect
  exact ⟨U, r, hne, hrank, exists_admissibleBlowup_forall_isHomologyPerfectTorLEOne E U
    (isSchemeTheoreticallyDense_of_nonempty hne) perfect r hrank⟩

end AlgebraicGeometry
