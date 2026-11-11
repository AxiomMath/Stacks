module

public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.IsolatedPoints
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.DualizingDegree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Characterization

/-!
# Pulling back the dualizing sheaf along a contraction of Gorenstein curves

Let `k` be a field and `c : X ⟶ Y` a morphism of proper `k`-schemes with `𝒪_Y = c_*𝒪_X` and
`R^1 c_*𝒪_X = 0`, where `X` and `Y` are reduced, Gorenstein and of dimension one. If for some
`m ≥ 1` the module `ω_X^{⊗ m}` has `H^1(X, ω_X^{⊗ m}) = 0` and is globally generated, then
`c^*ω_Y ≅ ω_X` ([Stacks, Tag 0E7P]).

## Main results

* `Stacks.Curves.DualizingPullback.nonempty_pullback_dualizingSheafOverField_iso`:
  [Stacks, Tag 0E7P].

## Implementation notes

Away from the isolated points, a Gorenstein proper scheme of dimension at most one has
one-dimensional local rings at its closed points, so its dualizing sheaf is invertible
(`AlgebraicGeometry.isInvertible_dualizingSheafOverField`). This is the input of
`Stacks.Curves.DualizingPullback.nonempty_pullback_iso_of_isolatedPoints`.

## References

* [Stacks Project, Tag 0E7P](https://stacks.math.columbia.edu/tag/0E7P)
* [Stacks Project, Tag 0C19](https://stacks.math.columbia.edu/tag/0C19)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Curves.DualizingPullback

open Stacks.Duality

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- **Stacks Project, Tag 0E7P.** Let `c : X ⟶ Y` be a morphism of proper schemes over a field
`k` with `𝒪_Y = c_*𝒪_X` and `R^1 c_*𝒪_X = 0`, where `X` and `Y` are reduced, Gorenstein and of
dimension one. If `H^1(X, ω_X^{⊗ m}) = 0` and `ω_X^{⊗ m}` is globally generated for some
`m ≥ 1`, then `c^*ω_Y ≅ ω_X`. The source allows any `m ∈ ℤ`, which is false for `m ≤ 0`. -/
@[stacks 0E7P "The corrected statement, with `m ≥ 1` (errata.md, 2026-11-06). Stacks allows any
`m ∈ ℤ`, and is false for every `m ≤ 0`: for `X = V(xy) ⊆ ℙ²_k` and `c` contracting one line `C`
to a point, (1)–(3) hold with any `m ≤ 0`, but `ω_X|_C ≅ 𝒪_C(-1)` while `(c^*ω_Y)|_C ≅ 𝒪_C`."]
theorem nonempty_pullback_dualizingSheafOverField_iso
    (c : X ⟶ Y) (g : Y ⟶ Spec (.of k)) [IsProper (c ≫ g)] [IsProper g]
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (hR1 : IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    [IsReduced X] [IsReduced Y] [IsGorenstein X] [IsGorenstein Y]
    (hdimX : topologicalKrullDim X = 1) (hdimY : topologicalKrullDim Y = 1)
    (m : ℕ) (hm : 1 ≤ m)
    (hH1 : IsZero (cohomologyOverField k (c ≫ g)
      (tensorSheafNPow X.toRingedSpace (dualizingSheafOverField (c ≫ g)) m) 1))
    (hgen : SheafOfModules.IsGeneratedByGlobalSections
      (tensorSheafNPow X.toRingedSpace (dualizingSheafOverField (c ≫ g)) m : X.Modules)) :
    Nonempty ((Scheme.Modules.pullback c).obj (dualizingSheafOverField g) ≅
      dualizingSheafOverField (c ≫ g)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have : IsProper c := IsProper.of_comp c g
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (c ≫ g)
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType g
  obtain ⟨UX, ZX, hdisjX, hcovX, hZX⟩ : ∃ U Z : X.Opens, U ⊓ Z = ⊥ ∧ U ⊔ Z = ⊤ ∧
      (Z : Set X) = isolatedPoints X := exists_isolatedPoints_decomposition
  obtain ⟨VY, ZY, hdisjY, hcovY, hZY⟩ : ∃ U Z : Y.Opens, U ⊓ Z = ⊥ ∧ U ⊔ Z = ⊤ ∧
      (Z : Set Y) = isolatedPoints Y := exists_isolatedPoints_decomposition
  have : IsClosedImmersion UX.ι := isClosedImmersion_ι_of_inf_eq_bot hdisjX hcovX
  have : IsClosedImmersion VY.ι := isClosedImmersion_ι_of_inf_eq_bot hdisjY hcovY
  have : IsGorenstein UX.toScheme := isGorenstein_of_isOpenImmersion UX.ι
  have : IsGorenstein VY.toScheme := isGorenstein_of_isOpenImmersion VY.ι
  have hdimU : topologicalKrullDim UX.toScheme ≤ 1 :=
    (Topology.IsEmbedding.subtypeVal.isInducing.topologicalKrullDim_le).trans hdimX.le
  have hdimV : topologicalKrullDim VY.toScheme ≤ 1 :=
    (Topology.IsEmbedding.subtypeVal.isInducing.topologicalKrullDim_le).trans hdimY.le
  have hωU := isInvertible_dualizingSheafOverField k (UX.ι ≫ c ≫ g) hdimU
    (ringKrullDim_stalk_eq_one_of_forall_not_isClopen (UX.ι ≫ c ≫ g) hdimU
      (not_isClopen_singleton_of_isolatedPoints hdisjX hcovX hZX))
  have hωV := isInvertible_dualizingSheafOverField k (VY.ι ≫ g) hdimV
    (ringKrullDim_stalk_eq_one_of_forall_not_isClopen (VY.ι ≫ g) hdimV
      (not_isClopen_singleton_of_isolatedPoints hdisjY hcovY hZY))
  have := (Stacks.SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one_algebraicGeometry
    _).mp hωU
  have := (Stacks.SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one_algebraicGeometry
    _).mp hωV
  exact nonempty_pullback_iso_of_isolatedPoints c g hdimX.le hdimY.le hO hR1 hdisjX hcovX hZX
    hdisjY hcovY hZY n hH1 hgen.some

end Stacks.Curves.DualizingPullback
