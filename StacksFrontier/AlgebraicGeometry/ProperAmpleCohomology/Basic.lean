module

public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.AmpleTwistAcyclicity.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of a coherent module on a proper scheme carrying an ample invertible module

Let `X` be a scheme carrying an ample invertible module `ℒ` and let `ℱ` be a coherent
`𝒪_X`-module. Then `ℱ` is a quotient of a finite direct sum `⨁_{j ∈ ι} ℒ ^⊗ dⱼ` of integer tensor
powers of `ℒ`. If moreover `X` is proper over `Spec R` with `R` a Noetherian ring, then there is
a `d₀` with `H ᵖ(X, ℱ ⊗ ℒ ^⊗ d) = 0` for every `d ≥ d₀` and every `p > 0`.

## Main results

* `Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_epi_biproduct_tensorPowModule_of_isAmple`:
  on a scheme with an ample invertible module `ℒ`, every coherent module is a quotient of a
  finite direct sum of integer tensor powers of `ℒ`.
* `Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_epi_biproduct_tensorPowModule`:
  the same statement for a scheme proper over a Noetherian scheme.
* `Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist`: for `X`
  proper over `Spec R` with `R` Noetherian, the higher cohomology of `ℱ ⊗ ℒ ^⊗ d` vanishes for
  all large `d`, with one bound serving every positive degree.

## References

* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 0B5V](https://stacks.math.columbia.edu/tag/0B5V)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample

universe u

namespace Stacks.AlgebraicGeometry.ProperAmpleCohomology

/-! ### Coherent modules as quotients of sums of tensor powers -/

/-- On a scheme carrying an ample invertible module `ℒ`, every coherent module `ℱ` is a quotient
of a finite direct sum `⨁_{j ∈ ι} ℒ ^⊗ dⱼ` of integer tensor powers of `ℒ`. -/
theorem exists_epi_biproduct_tensorPowModule_of_isAmple {X : Scheme.{u}} (F L : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] [IsInvertibleModule X L] (hL : IsAmple X L) :
    ∃ (ι : Type u) (_ : Finite ι) (d : ι → ℤ)
      (b : Bicone fun j : ι => tensorPowModule X L (d j)) (_ : b.IsBilimit)
      (p : b.pt ⟶ F), Epi p := by
  obtain ⟨-, hquot⟩ :=
    Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_exists_epi_biproduct_of_isAmple L hL
  obtain ⟨n, ι, hfin, -, b, hb, p, hp⟩ :=
    hquot F (_root_.isQuasicoherent_of_isCoherent F)
      _root_.SheafOfModules.IsCoherent.isFiniteType
  exact ⟨ι, hfin, fun _ => -n, b, hb, p, hp⟩

/-- Let `f : X ⟶ S` be proper with `S` Noetherian, let `ℒ` be an ample invertible `𝒪_X`-module
and let `ℱ` be a coherent `𝒪_X`-module. Then there are a finite index type `ι`, exponents
`d : ι → ℤ` and a surjection `⨁_{j ∈ ι} ℒ ^⊗ dⱼ ↠ ℱ`. -/
@[stacks 0B5T
  "clause (2), the surjection from a finite direct sum of tensor powers; \
   clauses (1), (3), (4) and (5) are not covered"]
theorem exists_epi_biproduct_tensorPowModule {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.IsNoetherian S] [IsProper f] (F L : X.Modules)
    [_root_.SheafOfModules.IsCoherent F]
    [IsInvertibleModule X L] (hL : IsAmple X L) :
    ∃ (ι : Type u) (_ : Finite ι) (d : ι → ℤ)
      (b : Bicone fun j : ι => tensorPowModule X L (d j)) (_ : b.IsBilimit)
      (p : b.pt ⟶ F), Epi p :=
  exists_epi_biproduct_tensorPowModule_of_isAmple F L hL

/-! ### Vanishing of the higher cohomology of high twists -/

/-- Let `R` be a Noetherian ring, let `f : X ⟶ Spec R` be proper, let `ℒ` be an ample invertible
`𝒪_X`-module and let `ℱ` be a coherent `𝒪_X`-module. Then there is a `d₀` with

`H ᵖ(X, ℱ ⊗ ℒ ^⊗ d) = 0` for every `d ≥ d₀` and every `p > 0`. -/
@[stacks 0B5T "clause (4), the eventual vanishing of the higher cohomology of the high twists \
  of a coherent module, with one exponent serving every positive degree"]
theorem exists_isZero_Hgroup_tensorPowTwist {X : Scheme.{u}} {R : Type u}
    [CommRing R] [IsNoetherianRing R] (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (F L : X.Modules) [_root_.SheafOfModules.IsCoherent F] [IsInvertibleModule X L]
    (hL : IsAmple X L) :
    ∃ d₀ : ℕ, ∀ d p : ℕ, d₀ ≤ d → 0 < p →
      IsZero (Hgroup X.ringCatSheaf ⊤ p
        (Stacks.RelativeVeryAmple.tensorModules X F (tensorPowModule X L (d : ℤ)))) := by
  classical
  have hNoeth : IsLocallyNoetherian (Spec (CommRingCat.of R)) :=
    AlgebraicGeometry.isLocallyNoetherian_Spec.mpr inferInstance
  obtain ⟨e, he⟩ :=
    Stacks.AlgebraicGeometry.RelativeSerreVanishing.exists_isZero_hgroup_tensorPowTwist_of_lt
      f L
  have key : ∀ i : Fin e, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      IsZero (Hgroup X.ringCatSheaf ⊤ ((i : ℕ) + 1)
        (Stacks.RelativeVeryAmple.tensorModules X F (tensorPowModule X L (d : ℤ)))) := fun i =>
    Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.absoluteVanishingOverAffineBase
      X _ f inferInstance hNoeth inferInstance L hL F inferInstance ((i : ℕ) + 1)
      (Nat.succ_pos _)
  choose k hk using key
  refine ⟨Finset.univ.sup k, fun d p hd hp => ?_⟩
  by_cases hpe : e < p
  · exact he p hpe F inferInstance (d : ℤ)
  · have hlt : p - 1 < e := by lia
    have hidx : ((⟨p - 1, hlt⟩ : Fin e) : ℕ) + 1 = p := Nat.sub_add_cancel hp
    exact hidx ▸ hk ⟨p - 1, hlt⟩ d
      (le_trans (Finset.le_sup (f := k) (Finset.mem_univ (⟨p - 1, hlt⟩ : Fin e))) hd)

end Stacks.AlgebraicGeometry.ProperAmpleCohomology

end
