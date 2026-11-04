module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingFirstCohomologyDimension
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafClauseFive
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GlobalSectionsGeneration
import StacksCore.Tactic.StacksAttribute

/-!
# Extensions of the dualizing sheaf `ω_X` of a proper curve

In Situation [Stacks, Tag 0B5D] — a field `k` and a proper one-dimensional `k`-scheme `X` with
`H⁰(X, 𝒪_X) = k` — let `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` be the dualizing sheaf of
[Stacks, Tag 0BS2], `Stacks.Duality.dualizingSheafOverField`. This file states
[Stacks, Tag 0B5E] for that sheaf: for an exact sequence `ω_X ⟶ ℱ ⟶ 𝒬 ⟶ 0` with
`H¹(X, 𝒬) = 0`, either `H¹(X, ℱ) = 0` or `ℱ ≅ ω_X ⊕ 𝒬`.

## Main results

The elided prefix is `AlgebraicGeometry.CohenMacaulayCurveSituation`.

* `isZero_firstCohomology_or_iso_biprod_dualizingSheafOverField`: **[Stacks, Tag 0B5E]**.
* `isZero_firstCohomology_or_iso_biprod_dualizingSheafOverField_of_supp_dim_le_zero`:
  the parenthetical example of [Stacks, Tag 0B5E], where `𝒬` is coherent with support of
  dimension at most zero.

## The inputs

`AlgebraicGeometry.CohenMacaulayCurveSituation.isZero_firstCohomology_or_iso_biprod` proves the
splitting for any quasi-coherent `ω` from three properties of it, all of which are proved for
`ω_X` (names in the namespace `AlgebraicGeometry.CohenMacaulayCurveSituation` unless qualified):

* the representability of `ℱ ↦ Hom_k(H¹(X, ℱ), k)` by `ω_X`, clause (5) of [Stacks, Tag 0BS2]
  (the form [Stacks, Tag 0AWP] that the source cites), with its naturality, is
  `firstCohomologyDuality_dualizingSheafOverField`, derived from clause (4);
* `dim_k H¹(X, ω_X) = 1`, which the source reads off the duality of `H⁰(X, 𝒪_X) = k` with
  `H¹(X, ω_X)` of Section [Stacks, Tag 0B5B], is
  `finrank_cohomologyOverField_one_dualizingSheafOverField_eq_one`;
* the vanishing of `H²(X, -)`, [Stacks, Tag 02UZ] on the one-dimensional `X`, is
  `secondCohomologyVanishing`; it is needed because `ω_X ⟶ ℱ` need not be injective;
* quasi-coherence of `ω_X` is `Stacks.Duality.isQuasicoherent_dualizingSheafOverField`.

The parenthetical example uses the vanishing clause of [Stacks, Tag 0B3J],
`isZero_firstCohomology_of_supp_dim_le_zero`.

## References

* [Stacks Project, Tag 0B5E](https://stacks.math.columbia.edu/tag/0B5E)
* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0AWP](https://stacks.math.columbia.edu/tag/0AWP)
* [Stacks Project, Tag 0B5B](https://stacks.math.columbia.edu/tag/0B5B)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 0B3J](https://stacks.math.columbia.edu/tag/0B3J)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace CohenMacaulayCurveSituation

variable {S : CohenMacaulayCurveSituation.{u}}

/-- **Stacks Project, Tag 0B5E.** In Situation [Stacks, Tag 0B5D], let
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))` be the dualizing sheaf of `X` ([Stacks, Tag 0BS2]) and let
`ω_X ⟶ ℱ ⟶ 𝒬 ⟶ 0` be an exact sequence of `𝒪_X`-modules with `H¹(X, 𝒬) = 0`. Then either
`H¹(X, ℱ) = 0`, or `ℱ ≅ ω_X ⊕ 𝒬` compatibly with both arrows of the sequence.

The source asks `ℱ` and `𝒬` to be coherent; only the quasi-coherence of `ℱ` is used. This is
`isZero_firstCohomology_or_iso_biprod` at `ω_X`, whose three inputs — clause (5) of
[Stacks, Tag 0BS2], `dim_k H¹(X, ω_X) = 1` and the vanishing of `H²(X, -)` — are proved; see
the module documentation. -/
@[stacks 0B5E]
public theorem isZero_firstCohomology_or_iso_biprod_dualizingSheafOverField {F Q : S.X.Modules}
    (hFq : F.IsQuasicoherent) (α : Stacks.Duality.dualizingSheafOverField S.f ⟶ F) (β : F ⟶ Q)
    (hαβ : α ≫ β = 0) (hex : (ShortComplex.mk α β hαβ).Exact) [Epi β]
    (hQ : IsZero (cohomologyOverField S.k S.f Q 1)) :
    IsZero (cohomologyOverField S.k S.f F 1) ∨
      ∃ e : F ≅ Stacks.Duality.dualizingSheafOverField S.f ⊞ Q,
        α ≫ e.hom = biprod.inl ∧ e.hom ≫ biprod.snd = β :=
  isZero_firstCohomology_or_iso_biprod
    (Stacks.Duality.isQuasicoherent_dualizingSheafOverField S.f) hFq
    (firstCohomologyDuality_dualizingSheafOverField S) S.secondCohomologyVanishing
    (finrank_cohomologyOverField_one_dualizingSheafOverField_eq_one S) α β hαβ hex hQ

/-- **Stacks Project, Tag 0B5E, the parenthetical example.** In Situation [Stacks, Tag 0B5D],
for an exact sequence `ω_X ⟶ ℱ ⟶ 𝒬 ⟶ 0` of `𝒪_X`-modules with `𝒬` coherent and
`dim(Supp(𝒬)) ≤ 0`, either `H¹(X, ℱ) = 0` or `ℱ ≅ ω_X ⊕ 𝒬` compatibly with both arrows.

The vanishing `H¹(X, 𝒬) = 0` is [Stacks, Tag 0B3J], as the source says, and the rest is
`isZero_firstCohomology_or_iso_biprod_dualizingSheafOverField`. -/
@[stacks 0B5E "the parenthetical example: Q coherent with dim(Supp(Q)) = 0, where \
H¹(X, Q) = 0 by Tag 0B3J"]
public theorem isZero_firstCohomology_or_iso_biprod_dualizingSheafOverField_of_supp_dim_le_zero
    {F Q : S.X.Modules} (hFq : F.IsQuasicoherent) (hQ : Q.IsCoherent)
    (hQdim : topologicalKrullDim (SheafOfModules.supp Q) ≤ 0)
    (α : Stacks.Duality.dualizingSheafOverField S.f ⟶ F) (β : F ⟶ Q)
    (hαβ : α ≫ β = 0) (hex : (ShortComplex.mk α β hαβ).Exact) [Epi β] :
    IsZero (cohomologyOverField S.k S.f F 1) ∨
      ∃ e : F ≅ Stacks.Duality.dualizingSheafOverField S.f ⊞ Q,
        α ≫ e.hom = biprod.inl ∧ e.hom ≫ biprod.snd = β :=
  isZero_firstCohomology_or_iso_biprod_dualizingSheafOverField hFq α β hαβ hex
    (isZero_firstCohomology_of_supp_dim_le_zero hQ hQdim)

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
