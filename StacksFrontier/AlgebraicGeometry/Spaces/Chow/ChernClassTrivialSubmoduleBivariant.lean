module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassBivariantComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassTrivialSubmodule
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackUnitShortExact

/-!
# Chern classes of an extension of a finite locally free module by `𝒪_X`, in `A^*(X)`

In Situation 0EDT let `X/B` be good and let `0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℱ ⟶ 0` be a short exact sequence of
`𝒪_X`-modules with `ℰ`, `ℱ` finite locally free of ranks `r + 1` and `r`. **Stacks 0ES7** asserts

  `c_{r+1}(ℰ) = 0`   and   `c_j(ℰ) = c_j(ℱ)` for `j = 0, …, r`

in `A^*(X)`, for the Chern classes `c_j(ℰ) ∈ A^j(X)` of Stacks 0ERZ
(`AlgebraicGeometry.Space.chernClass`, the bivariant classes of Stacks 0ERY).

Two bivariant classes agree when their cap operations agree on every good test space
`g : X' ⟶ X` (`AlgebraicGeometry.Space.BivariantClassCanonical.ext`), and the cap operation of
`c_j(ℰ)` on `X'` is `c_j(ℰ) ∩ - : CH_k(X') ⟶ CH_{k-j}(X')`
(`AlgebraicGeometry.Space.chernCap`), which is `c_j(g^*ℰ) ∩ -` on `CH_*(X')` for the Chern
classes of the inverse image
(`AlgebraicGeometry.Space.chowGroupCanonicalToChowHomology_chernCap`). The
inverse image `0 ⟶ 𝒪_{X'} ⟶ g^*ℰ ⟶ g^*ℱ ⟶ 0` is again short exact with the same ranks
(`AlgebraicGeometry.Space.exists_shortExact_modulePullback_of_tensorUnit`), so the identities on
`X'` are the case of the good space `X'`
(`AlgebraicGeometry.Space.chernCap_eq_of_shortExact_tensorUnit`, which follows the proof of the
source through Stacks 0ES8 and the vanishing of Chern classes above the rank).

## Main results

* `AlgebraicGeometry.Space.chernCap_eq_of_shortExact_tensorUnit_testSpace`: the identities for
  the cap operations on every good test space.
* `AlgebraicGeometry.Space.chernClass_eq_of_shortExact_tensorUnit`: **Stacks 0ES7** in `A^*(X)`.

## References

* [Stacks Project, Tag 0ES7](https://stacks.math.columbia.edu/tag/0ES7)
* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}

/-- The inclusion of `CH_k(X)` as a summand of `CH_*(X)` is injective. -/
theorem chowGroupCanonicalToChowHomology_injective {Z : D.Ambient} (sZ : Z ⟶ D.space)
    (hZ : D.IsGood sZ) (k : ℤ) :
    Function.Injective (chowGroupCanonicalToChowHomology D sZ hZ k) :=
  (DirectSum.of_injective (β := fun k => chowGroup.{u + 1} D sZ hZ k) k).comp
    (chowGroupCanonicalEquivChowGroup.{u + 1} D sZ hZ k).injective

/-- **The identities of Stacks 0ES7 on a test space.** For `0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℱ ⟶ 0` short exact with
`ℰ`, `ℱ` finite locally free of ranks `r + 1` and `r`, on every good test space `g : X' ⟶ X` and
for every `α ∈ CH_k(X')`: `c_{r+1}(ℰ) ∩ α = 0` and `c_j(ℰ) ∩ α = c_j(ℱ) ∩ α` for `j ≤ r`, the
maps being those of Stacks 0ERY (`AlgebraicGeometry.Space.chernCap`). -/
theorem chernCap_eq_of_shortExact_tensorUnit_testSpace (hX : D.IsGood sX)
    {E F : Modules.{u, u} D.site D.base D.base_mem X hX.1}
    (i : 𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1) ⟶ E) (q : E ⟶ F) (hiq : i ≫ q = 0)
    (hC : (ShortComplex.mk i q hiq).ShortExact) (r : ℕ)
    (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E (r + 1))
    (hF : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) F r)
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    chernCap D sX hX E (r + 1) hE g hY (Fin.last (r + 1)) k α = 0 ∧
      ∀ (j : ℕ) (hj : j ≤ r), chernCap D sX hX E (r + 1) hE g hY ⟨j, by omega⟩ k α =
        chernCap D sX hX F r hF g hY ⟨j, by omega⟩ k α := by
  have h1 : SheafOfModules.IsFiniteLocallyFreeOnSite
      (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1)) :=
    (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (PrivateChern.goodSpace hX)
      (isInvertibleModule_tensorUnit hX)).isFiniteLocallyFreeOnSite
  obtain ⟨i', hiq', hC'⟩ := exists_shortExact_modulePullback_of_tensorUnit
    (goodSpaceHom D sX hX g hY) i q hiq hC h1 hE.isFiniteLocallyFreeOnSite
    hF.isFiniteLocallyFreeOnSite
  have hE' := isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
    (goodSpaceHom D sX hX g hY) E (r + 1) hE
  have hF' := isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
    (goodSpaceHom D sX hX g hY) F r hF
  obtain ⟨hlast, hlow⟩ := chernCap_eq_of_shortExact_tensorUnit hY i' _ hiq' hC' r hE' hF'
  refine ⟨?_, fun j hj => ?_⟩
  · refine chowGroupCanonicalToChowHomology_injective (g ≫ sX) hY _ ?_
    rw [chowGroupCanonicalToChowHomology_chernCap D sX hX E (r + 1) hE g hY hE', map_zero,
      Fin.val_last, hlast]
    rfl
  · refine chowGroupCanonicalToChowHomology_injective (g ≫ sX) hY _ ?_
    have h₁ := chowGroupCanonicalToChowHomology_chernCap D sX hX E (r + 1) hE g hY hE'
      ⟨j, by omega⟩ k α
    have h₂ := chowGroupCanonicalToChowHomology_chernCap D sX hX F r hF g hY hF' ⟨j, by omega⟩ k α
    refine h₁.trans (Eq.trans ?_ h₂.symm)
    exact congrArg (fun φ => φ (chowGroupCanonicalToChowHomology D (g ≫ sX) hY k α)) (hlow j hj)

/-- **Stacks 0ES7.** In Situation 0EDT let `X/B` be good and let `ℰ`, `ℱ` be finite locally free
`𝒪_X`-modules of ranks `r + 1` and `r` which fit into a short exact sequence
`0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℱ ⟶ 0`. Then

  `c_{r+1}(ℰ) = 0`   and   `c_j(ℰ) = c_j(ℱ)`, `j = 0, …, r`,

in `A^*(X)`: equalities of the Chern classes of Stacks 0ERZ (`AlgebraicGeometry.Space.chernClass`),
bivariant classes in `A^j(X) = A^j(X → X)` over the Chow groups of Stacks 0EQ6
(`AlgebraicGeometry.Space.chowCohomologyComponentCanonical`). The ranks `r`, `r - 1` of the source
are written `r + 1`, `r` here, and `𝒪_X` is the unit of the tensor product of `𝒪_X`-modules
(`AlgebraicGeometry.Space.modulesTensorUnit_eq`). -/
@[stacks 0ES7 "c_r(E) = 0 and c_j(E) = c_j(F), j = 0, ..., r - 1, in A^*(X), for the bivariant \
Chern classes chernClass of Lemma 0ERZ in A^j(X) = A^j(X → X) over chowGroupCanonical; the ranks \
r, r - 1 are written r + 1, r"]
theorem chernClass_eq_of_shortExact_tensorUnit (hX : D.IsGood sX)
    {E F : Modules.{u, u} D.site D.base D.base_mem X hX.1}
    (i : 𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1) ⟶ E) (q : E ⟶ F) (hiq : i ≫ q = 0)
    (hC : (ShortComplex.mk i q hiq).ShortExact) (r : ℕ)
    (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E (r + 1))
    (hF : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) F r) :
    chernClass D sX hX E (r + 1) hE (Fin.last (r + 1)) = 0 ∧
      ∀ (j : ℕ) (hj : j ≤ r),
        chernClass D sX hX E (r + 1) hE ⟨j, by omega⟩ = chernClass D sX hX F r hF ⟨j, by omega⟩ :=
            by
  refine ⟨?_, fun j hj => ?_⟩
  · ext Y g hY hXg k α
    rw [chernClass_cap, (chernCap_eq_of_shortExact_tensorUnit_testSpace hX i q hiq hC r hE hF g hY k
      α).1, map_zero, BivariantClassCanonical.zero_cap]
  · ext Y g hY hXg k α
    rw [chernClass_cap, chernClass_cap,
      (chernCap_eq_of_shortExact_tensorUnit_testSpace hX i q hiq hC r hE hF g hY k α).2 j hj]

end AlgebraicGeometry.Space

end
