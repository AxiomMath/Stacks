module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.FirstChernCapChowTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ProjectiveBundleSegreZero
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleMapClosedFibre

/-!
# The first Chern class of an invertible module

In Situation 0EDT let `X/B` be good and let `ℒ` be an invertible `𝒪_X`-module, a finite locally
free module of rank `1`. Its first Chern class `c₁(ℒ)` of Stacks 0ERZ, defined through the
projective bundle `(π : P = 𝐏(ℒ) ⟶ X, 𝒪_P(1))` as the Segre operation
`t_1(ℒ) ∩ α = π_*(c₁(𝒪_P(1)) ∩ π^*α)`, is the cap product `c₁(ℒ) ∩ -` of Stacks 0EQJ:

  `c₁(ℒ) ∩ - = c₁(ℒ) ∩ -`   on `CH_*(X)`.

Indeed the tautological surjection `π^*ℒ ⟶ 𝒪_P(1)` is a surjection of invertible modules, hence an
isomorphism, so `c₁(𝒪_P(1)) ∩ π^*α = c₁(π^*ℒ) ∩ π^*α = π^*(c₁(ℒ) ∩ α)` (Stacks 0EQR), and
`π_*π^* = t_0(ℒ)` is the identity (Stacks 0ERU, top degree, the relative dimension being `0`).

Consequently `c₁(ℒ ⊗ 𝒩) = c₁(ℒ) + c₁(𝒩)` for modules of rank one and `c₁(𝒪_X) = 0`, by
Stacks 0EQK.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.chernCap_one_eq_firstChernCapChow`: `c₁(ℒ)` of
  Stacks 0ERZ is the cap product with the first Chern class.
* `AlgebraicGeometry.Space.PrivateChern.chernCap_one_tensorObj`:
  `c₁(ℒ ⊗ 𝒩) = c₁(ℒ) + c₁(𝒩)` for modules of rank one.
* `AlgebraicGeometry.Space.PrivateChern.chernCap_one_tensorUnit`: `c₁(𝒪_X) = 0`.

## Implementation notes

The Chow groups are those whose rational equivalences are indexed in the universe `u + 1`, at
which flat pullback, proper pushforward and the cap product with a first Chern class are known to
respect rational equivalence.

## References

* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
* [Stacks Project, Tag 0EQK](https://stacks.math.columbia.edu/tag/0EQK)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] modulesMonoidalCategory

/-- **The tautological surjection `π^*ℒ ⟶ 𝒪_P(1)` of the projective bundle of an invertible
module is an isomorphism**, a surjection of invertible modules. -/
theorem isIso_projectiveBundleTautological {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {Z : AlgebraicSpaces B S hS} (L : Modules.{u, u} B S hS Z.1 Z.2)
    [L.IsQuasicoherentOnSite] (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite L)
    (hL : IsInvertibleModule Z L) : IsIso (projectiveBundleTautological L hfree).hom :=
  @isIso_of_epi_of_isInvertibleModule _ _ _ _ _ _
    (modulePullbackInvertible (projectiveBundleProj L hfree) L hL)
    (isInvertibleModule_projectiveBundleTwist L hfree) _ (epi_projectiveBundleTautological L hfree)

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX}

/-- The first Chern class of a module of rank one is its first Segre operation. -/
theorem chernCap_one_eq_segreCapOfModule (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (h : IsFiniteLocallyFreeOfRank D sX hX L 1) :
    chernCap.{u, u + 1} L 1 h 1 = segreCapOfModule.{u, u + 1} L 1 h 1 := by
  rw [chernCap, chernSeq_succ, Fin.sum_univ_one]
  simp only [Fin.val_zero, chernSeq_zero, Nat.sub_zero, zero_add, pow_zero, one_mul, mul_one]

/-- **The first Chern class of Stacks 0ERZ of an invertible module is the cap product with its
first Chern class**: `c₁(ℒ) ∩ - = c₁(ℒ) ∩ -` on `CH_*(X)`, the left side defined through the
projective bundle of `ℒ` as `t_1(ℒ)`, the right side the operation of Stacks 0EQJ. -/
theorem chernCap_one_eq_firstChernCapChow (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (h : IsFiniteLocallyFreeOfRank D sX hX L 1) (hL : IsInvertibleModule (goodSpace hX) L) :
    chernCap.{u, u + 1} L 1 h 1 = firstChernCapChow.{u, u + 1} D sX hX L hL := by
  rw [chernCap_one_eq_segreCapOfModule]
  let := isQuasicoherentOnSite_of_rank L h
  have hfree := isFiniteLocallyFreeOnSite_of_rank L h
  let P := projectiveBundleDatum L 0 h
  have hπL := modulePullbackInvertible
    (ObjectProperty.homMk P.proj : (⟨P.space, P.isGood.1⟩ : AlgebraicSpaces D.site D.base
      D.base_mem) ⟶ ⟨X, hX.1⟩) L hL
  have := isIso_projectiveBundleTautological (Z := goodSpace hX) L hfree hL
  have e : P.twist ≅ (modulePullback D.site D.base D.base_mem
      (ObjectProperty.homMk P.proj : (⟨P.space, P.isGood.1⟩ : AlgebraicSpaces D.site D.base
        D.base_mem) ⟶ ⟨X, hX.1⟩)).obj L :=
    (asIso (projectiveBundleTautological (X := goodSpace hX) L hfree).hom).symm
  have e1 : P.twistCap = firstChernCapChow.{u, u + 1} D P.toBase P.isGood
      (pullbackLine D P.toBase P.isGood sX hX P.proj L) hπL :=
    firstChernCapChow_congr_iso D P.toBase P.isGood _ _ _ hπL e
  change P.segreCap 1 = _
  refine AddMonoidHom.ext fun α => ?_
  calc P.pushforwardChow ((P.twistCap ^ (0 + 1)) (P.pullbackChow α))
      = P.pushforwardChow (P.twistCap (P.pullbackChow α)) := by rw [zero_add, pow_one]
    _ = P.pushforwardChow (P.pullbackChow (firstChernCapChow.{u, u + 1} D sX hX L hL α)) := by
      rw [e1]
      exact congrArg _ (flatPullbackChow_firstChernCapChow D P.toBase P.isGood sX hX P.proj
        P.proj_comp 0 P.isFlat P.hasRelativeDimension L hL α).symm
    _ = firstChernCapChow.{u, u + 1} D sX hX L hL α :=
      DFunLike.congr_fun (segreCapOfModule_succ_zero L 0 h) _

/-- The first Chern class of a module of rank one is the cap product with its first Chern class. -/
private theorem chernCap_one_eq_firstChernCapChow_of_rank {P : D.Ambient} {sP : P ⟶ D.space}
    {hP : D.IsGood sP} {L : Modules.{u, u} D.site D.base D.base_mem P hP.1}
    (h : IsFiniteLocallyFreeOfRank D sP hP L 1) :
    chernCap.{u, u + 1} L 1 h 1 = firstChernCapChow.{u, u + 1} D sP hP L
      ((isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one (Z := goodSpace hP) L).2 h) :=
  chernCap_one_eq_firstChernCapChow L h _

/-- **`c₁(ℒ ⊗ 𝒩) = c₁(ℒ) + c₁(𝒩)`** for modules `ℒ`, `𝒩` of rank one on a good space, the first
Chern classes being those of Stacks 0ERZ (Stacks 0EQK). -/
theorem chernCap_one_tensorObj {P : D.Ambient} {sP : P ⟶ D.space} (hP : D.IsGood sP)
    (L M : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsFiniteLocallyFreeOfRank D sP hP L 1) (hM : IsFiniteLocallyFreeOfRank D sP hP M 1)
    (hLM : IsFiniteLocallyFreeOfRank D sP hP (L ⊗ M) 1) :
    chernCap.{u, u + 1} (hX := hP) (L ⊗ M) 1 hLM 1 =
      chernCap.{u, u + 1} (hX := hP) L 1 hL 1 + chernCap.{u, u + 1} (hX := hP) M 1 hM 1 := by
  rw [chernCap_one_eq_firstChernCapChow_of_rank hLM, chernCap_one_eq_firstChernCapChow_of_rank hL,
    chernCap_one_eq_firstChernCapChow_of_rank hM, firstChernCapChow_tensorObj hP L M _ _ _]
  rfl

/-- **`c₁(𝒪_X) = 0`** for the first Chern class of Stacks 0ERZ (Stacks 0EQK). -/
theorem chernCap_one_tensorUnit {P : D.Ambient} {sP : P ⟶ D.space} (hP : D.IsGood sP)
    (h : IsFiniteLocallyFreeOfRank D sP hP (𝟙_ (Modules.{u, u} D.site D.base D.base_mem P hP.1))
      1) :
    chernCap.{u, u + 1} (hX := hP) (𝟙_ (Modules.{u, u} D.site D.base D.base_mem P hP.1)) 1 h 1 =
      0 := by
  rw [chernCap_one_eq_firstChernCapChow_of_rank h, firstChernCapChow_tensorUnit hP]
  rfl

end AlgebraicGeometry.Space.PrivateChern

end
