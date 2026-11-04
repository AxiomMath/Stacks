module

public import Mathlib.Algebra.Group.Hom.End
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChowOperations
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SegreInverse

/-!
# Segre and Chern operations attached to a projective bundle

In Situation 0EDT let `X/B` be good, let `ℰ` be a finite locally free `𝒪_X`-module of rank
`r = d + 1` and let `(π : P ⟶ X, 𝒪_P(1))` be its projective bundle (Section 0ERT): `P` is good,
`π` is proper and flat of relative dimension `d`, and `𝒪_P(1)` is invertible. The proof of
Stacks 0ERY attaches to these data the operations

`t_i ∩ - : CH_k(X) ⟶ CH_{k-i}(X)`,   `α ↦ π_*(c₁(𝒪_P(1))^{d+i} ∩ π^*α)`   (`i ≥ 0`),

which up to sign are the Segre classes of `ℰ`, and the Chern classes `c_n(ℰ)` of Stacks 0ERZ are
the coefficients of the inverse series: `c₀ = 1` and `c_n = ∑_{j<n} (-1)^{n-j+1} t_{n-j} c_j`
(`AlgebraicGeometry.Space.PrivateChern.chernSeq`). This file defines both from the bare data of a
projective bundle, collected in `AlgebraicGeometry.Space.PrivateChern.ProjectiveBundleDatum`.

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.ProjectiveBundleDatum`: a good algebraic space `P` with a
  proper flat morphism `π : P ⟶ X` of relative dimension `d` and an invertible module on `P`.
* `AlgebraicGeometry.Space.PrivateChern.ProjectiveBundleDatum.segreCap`: the operation `t_i ∩ -`
  on `CH_*(X)`.
* `AlgebraicGeometry.Space.PrivateChern.ProjectiveBundleDatum.chernCap`: the operation
  `c_n ∩ -` on `CH_*(X)`.

## References

* [Stacks Project, Tag 0ERT](https://stacks.math.columbia.edu/tag/0ERT)
* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
* W. Fulton, *Intersection theory*, Section 3.1 and 3.2.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space.PrivateChern

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient}

/-- **The data of a projective bundle of fibre dimension `d` over a good algebraic space**: a good
algebraic space `P` over the base with a morphism `π : P ⟶ X` over the base which is proper and
flat of relative dimension `d`, together with an invertible `𝒪_P`-module, the twist `𝒪_P(1)`. -/
structure ProjectiveBundleDatum (sX : X ⟶ D.space) (hX : D.IsGood sX) (d : ℕ) where
  /-- The total space `P`. -/
  space : D.Ambient
  /-- Its structure morphism to the base. -/
  toBase : space ⟶ D.space
  /-- `P` is good over the base. -/
  isGood : D.IsGood toBase
  /-- The projection `π : P ⟶ X`. -/
  proj : space ⟶ X
  /-- The projection is a morphism over the base. -/
  proj_comp : proj ≫ sX = toBase
  /-- The projection is proper. -/
  isProper : IsProper D.site D.base D.base_mem proj
  /-- The projection is flat. -/
  isFlat : IsFlat D.site D.base D.base_mem proj
  /-- The projection has relative dimension `d`. -/
  hasRelativeDimension : HasRelativeDimension d D.site D.base D.base_mem proj
  /-- The twist `𝒪_P(1)`. -/
  twist : Modules.{u, u} D.site D.base D.base_mem space isGood.1
  /-- The twist is invertible. -/
  isInvertible_twist :
    IsInvertibleModule (⟨space, isGood.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) twist

namespace ProjectiveBundleDatum

variable {D} {sX : X ⟶ D.space} {hX : D.IsGood sX} {d : ℕ}
  (P : ProjectiveBundleDatum D sX hX d)

/-- Flat pullback `π^* : CH_*(X) ⟶ CH_{*+d}(P)` along the projection. -/
abbrev pullbackChow : chowHomology.{u, v} D sX hX →+ chowHomology.{u, v} D P.toBase P.isGood :=
  flatPullbackChow.{u, v} D P.toBase P.isGood sX hX P.proj P.proj_comp d P.isFlat
    P.hasRelativeDimension

/-- Proper pushforward `π_* : CH_*(P) ⟶ CH_*(X)` along the projection. -/
abbrev pushforwardChow : chowHomology.{u, v} D P.toBase P.isGood →+ chowHomology.{u, v} D sX hX :=
  properPushforwardChow.{u, v} D P.toBase P.isGood sX hX P.proj P.proj_comp P.isProper

/-- The cap product `c₁(𝒪_P(1)) ∩ -` on `CH_*(P)`. -/
abbrev twistCap : AddMonoid.End (chowHomology.{u, v} D P.toBase P.isGood) :=
  firstChernCapChow.{u, v} D P.toBase P.isGood P.twist P.isInvertible_twist

/-- **The Segre operations** of the proof of Stacks 0ERY: for `i ≥ 0`,
`t_i ∩ - : CH_k(X) ⟶ CH_{k-i}(X)`, `α ↦ π_*(c₁(𝒪_P(1))^{d+i} ∩ π^*α)`. -/
def segreCap (i : ℕ) : AddMonoid.End (chowHomology.{u, v} D sX hX) :=
  P.pushforwardChow.comp ((P.twistCap ^ (d + i)).comp P.pullbackChow)

/-- **The Chern operations** of the projective bundle: `c_n ∩ -` on `CH_*(X)`, the coefficients of
the inverse of the Segre series, `c₀ = 1` and `c_n = ∑_{j<n} (-1)^{n-j+1} t_{n-j} c_j`. -/
def chernCap (n : ℕ) : AddMonoid.End (chowHomology.{u, v} D sX hX) :=
  chernSeq P.segreCap n

end ProjectiveBundleDatum

end AlgebraicGeometry.Space.PrivateChern

end
