module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SegreClasses
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyPushforwardSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# Chern classes of finite locally free modules on good algebraic spaces

In Situation 0EDT let `X/B` be good and let `ℰ` be a finite locally free `𝒪_X`-module of rank
`r` (the rank clause of Stacks 0409). For `r = d + 1 ≥ 1` its projective bundle
`(π : P = 𝐏(ℰ) ⟶ X, 𝒪_P(1))` of Section 0ERT is a good algebraic space, with `π` proper and
flat of relative dimension `d` and `𝒪_P(1)` invertible
(`AlgebraicGeometry.Space.PrivateChern.projectiveBundleDatum`). The Chern classes of `ℰ` are the
operations on `CH_*(X)` attached to it: with the Segre operations
`t_i(ℰ) ∩ α = π_*(c₁(𝒪_P(1))^{d+i} ∩ π^*α)` of the proof of Stacks 0ERY,

`c₀(ℰ) = 1`,   `c_n(ℰ) = ∑_{j<n} (-1)^{n-j+1} t_{n-j}(ℰ) c_j(ℰ)`   (`n ≥ 1`).

Pushing the defining relation `∑_{i=0}^r (-1)^i c₁(𝒪_{P'}(1))^i ∩ π'^*(c_{r-i}(ℰ) ∩ α) = 0` of
Stacks 0ERY forward after capping with `c₁(𝒪_{P'}(1))^m` gives exactly this recursion, so these
are the Chern classes `c_n(ℰ)` of Stacks 0ERZ (for `n > r` they vanish, Stacks' convention). For
`r = 0` the projective bundle is empty and `c(ℰ) = 1`.

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.projectiveBundleDatum`: the projective bundle of `ℰ` as a
  `ProjectiveBundleDatum`.
* `AlgebraicGeometry.Space.PrivateChern.segreCapOfModule`: the Segre operations `t_i(ℰ) ∩ -`.
* `AlgebraicGeometry.Space.PrivateChern.chernCap`: **the Chern classes** `c_n(ℰ) ∩ -` on
  `CH_*(X)`.
* `AlgebraicGeometry.Space.PrivateChern.totalChernCap`: the total Chern class
  `c(ℰ) = c₀(ℰ) + ⋯ + c_r(ℰ)`.

## References

* [Stacks Project, Tag 0ERT](https://stacks.math.columbia.edu/tag/0ERT)
* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
* W. Fulton, *Intersection theory*, Section 3.2.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space.PrivateChern

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (sX : X ⟶ D.space)
  (hX : D.IsGood sX)

/-- A module of rank `r` on a good space, in the sense of the rank clause of Stacks 0409 on its
small étale ringed site. -/
abbrev IsFiniteLocallyFreeOfRank (E : Modules.{u, u} D.site D.base D.base_mem X hX.1) (r : ℕ) :
    Prop :=
  RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E r

variable {D sX hX}

/-- The good space `X`, as an algebraic space. -/
abbrev goodSpace (hX : D.IsGood sX) : AlgebraicSpaces D.site D.base D.base_mem := ⟨X, hX.1⟩

variable (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)

/-- A module of rank `r` on a good space is finite locally free on its small étale site. -/
theorem isFiniteLocallyFreeOnSite_of_rank {r : ℕ} (hr : IsFiniteLocallyFreeOfRank D sX hX E r) :
    SheafOfModules.IsFiniteLocallyFreeOnSite E :=
  hr.isFiniteLocallyFreeOnSite

/-- A module of rank `r` on a good space is quasi-coherent on its small étale site. -/
theorem isQuasicoherentOnSite_of_rank {r : ℕ} (hr : IsFiniteLocallyFreeOfRank D sX hX E r) :
    E.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isFiniteLocallyFreeOnSite (X := goodSpace hX) E
    (isFiniteLocallyFreeOnSite_of_rank E hr)

/-- **The projective bundle of a module of rank `d + 1` on a good space**, as a projective bundle
datum of fibre dimension `d`: `P = 𝐏(ℰ)` with the projection `π`, proper and flat of relative
dimension `d`, and the twist `𝒪_P(1)`. -/
def projectiveBundleDatum (d : ℕ) (hr : IsFiniteLocallyFreeOfRank D sX hX E (d + 1)) :
    ProjectiveBundleDatum D sX hX d :=
  letI := isQuasicoherentOnSite_of_rank E hr
  have hfree := isFiniteLocallyFreeOnSite_of_rank E hr
  have hP := isProper_projectiveBundleProj (X := goodSpace hX) E hfree
  { space := (projectiveBundle (X := goodSpace hX) E hfree).1
    toBase := (projectiveBundleProj (X := goodSpace hX) E hfree).hom ≫ sX
    isGood :=
      ⟨(projectiveBundle (X := goodSpace hX) E hfree).2,
        isQuasiSeparated_comp D.site D.base D.base_mem
          (projectiveBundle (X := goodSpace hX) E hfree).2 hX.1 _ sX
          (isQuasiSeparated_of_isSeparated D.site D.base D.base_mem hP.1) hX.2.1,
        isLocallyOfFiniteType_comp' D.site D.base D.base_mem _ sX hX.1 D.isAlgebraicSpace
          hP.2.1.1 hX.2.2⟩
    proj := (projectiveBundleProj (X := goodSpace hX) E hfree).hom
    proj_comp := rfl
    isProper := hP
    isFlat := isFlat_projectiveBundleProj (X := goodSpace hX) E d hr hfree
    hasRelativeDimension :=
      hasRelativeDimension_projectiveBundleProj (X := goodSpace hX) E d hr hfree
    twist := (projectiveBundleTwist (X := goodSpace hX) E hfree).obj
    isInvertible_twist := isInvertibleModule_projectiveBundleTwist (X := goodSpace hX) E hfree }

/-- **The Segre operations** `t_i(ℰ) ∩ -` of a module of rank `r` on a good space: for `r = d + 1`
those of its projective bundle (`ProjectiveBundleDatum.segreCap`), and zero for `r = 0`. -/
def segreCapOfModule : ∀ (r : ℕ), IsFiniteLocallyFreeOfRank D sX hX E r → ℕ →
    AddMonoid.End (chowHomology.{u, v} D sX hX)
  | 0, _ => fun _ => 0
  | d + 1, hr => (projectiveBundleDatum E d hr).segreCap

/-- **Stacks 0ERZ, the Chern classes.** The `n`-th Chern class `c_n(ℰ) ∩ -` of a finite locally
free module `ℰ` of rank `r` on a good space `X`, as an operation on `CH_*(X) = ⨁_k CH_k(X)`
carrying `CH_k(X)` to `CH_{k-n}(X)`: `c₀(ℰ) = 1` and, for `n ≥ 1`,
`c_n(ℰ) = ∑_{j<n} (-1)^{n-j+1} t_{n-j}(ℰ) c_j(ℰ)`, where
`t_i(ℰ) ∩ α = π_*(c₁(𝒪_P(1))^{r-1+i} ∩ π^*α)` for the projective bundle `(π : P ⟶ X, 𝒪_P(1))` of
`ℰ` (Section 0ERT). This recursion is the one obtained in the proof of Stacks 0ERY by pushing the
defining relation `∑_{i=0}^r (-1)^i c₁(𝒪_{P}(1))^i ∩ π^*(c_{r-i}(ℰ) ∩ α) = 0` forward after capping
with powers of `c₁(𝒪_P(1))`, so `c_n(ℰ)` is the class of Stacks 0ERY (the coefficient of the
inverse of the Segre series, Fulton's definition); for `n > r` it vanishes, which is the
convention `c_n(ℰ) = 0` of the source. For `r = 0`, `c(ℰ) = 1`. -/
def chernCap (r : ℕ) (hr : IsFiniteLocallyFreeOfRank D sX hX E r) (n : ℕ) :
    AddMonoid.End (chowHomology.{u, v} D sX hX) :=
  chernSeq (segreCapOfModule.{u, v} E r hr) n

/-- **Stacks 0ERZ, the total Chern class** `c(ℰ) = c₀(ℰ) + c₁(ℰ) + ⋯ + c_r(ℰ)` of a finite locally
free module of rank `r`, as an operation on `CH_*(X)`. -/
def totalChernCap (r : ℕ) (hr : IsFiniteLocallyFreeOfRank D sX hX E r) :
    AddMonoid.End (chowHomology.{u, v} D sX hX) :=
  ∑ n ∈ Finset.range (r + 1), chernCap.{u, v} E r hr n

/-- The zeroth Chern class is the identity: `c₀(ℰ) ∩ α = α`. -/
theorem chernCap_zero (r : ℕ) (hr : IsFiniteLocallyFreeOfRank D sX hX E r) :
    chernCap.{u, v} E r hr 0 = 1 :=
  chernSeq_zero _

end AlgebraicGeometry.Space.PrivateChern

end
