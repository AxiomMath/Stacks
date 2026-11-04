module

import StacksFrontier.RingTheory.Depth.Dimension
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Presheaf

public import StacksFrontier.RingTheory.ProjectiveDimension.AuslanderBuchsbaum

@[expose] public section

universe v u

/-!
# Finite projective dimension is bounded by the dimension of a Noetherian local ring

Let `(R, 𝔪)` be a Noetherian local ring and let `M` be a finite `R`-module of finite projective
dimension. This file proves `pd_R M ≤ dim R` as the composition of two inequalities, each a
statement about one invariant of `R`:

* `pd_R M ≤ depth_𝔪(R)`, because the Auslander-Buchsbaum formula
  `pd_R M + depth_𝔪(M) = depth_𝔪(R)` (Stacks 090V) exhibits `pd_R M` as a summand of
  `depth_𝔪(R)`;
* `depth_𝔪(R) ≤ dim Supp(R) = dim R` (Stacks 00LK).

## Main results

* `Stacks.ProjectiveDimension.KrullBound.solution`: Stacks 00OB, `pd_R M ≤ dim R` over a Noetherian
  local ring.

## Implementation notes

The source proves the case `M = κ` directly: a minimal finite free resolution
`0 → F_n → ⋯ → F₀ → κ → 0` (Stacks 0CXF, Stacks 00MT) has `I(φ_n) ≠ R` by minimality, so the
determinantal exactness criterion (Stacks 00N1) gives `depth_{I(φ_n)}(R) ≥ n`, and
Stacks 00LK turns that into `dim R ≥ n`. The route taken here replaces the first three of
those citations by the single Proposition 090V, whose own proof is that same argument run for
an arbitrary `M` (minimal resolution, Stacks 00MT, Stacks 00N1). Two things are gained: the
statement holds for every finite module rather than for `κ` alone, and no minimal resolution has
to be manipulated here. The dependency is acyclic
— Proposition 090V uses Stacks 00MT, 00N1, 00LX and 090R, not Stacks 00OB.

The first inequality is `projectiveDimension_le_depth_self` below. It carries no nontriviality
hypothesis, although 090V does: the zero module has `pd_R M = ⊥`, which is below everything, so
the case split on `M` belongs inside that lemma rather than in the theorem it serves. The step
"a summand is at most the sum" is `WithBot.le_self_add`, whose hypothesis that the added summand
is not `⊥` is met because that summand is a coercion of a depth: both
`Module.projectiveDimension` and `ringKrullDim` are valued in `WithBot ℕ∞`, where `⊥` is the
value of the invariant on the zero module, while `Module.depth` is valued in `ℕ∞`.

The second inequality is `depth_le_ringKrullDim` below: Stacks 00LK read at `I = 𝔪` and `M = R`,
whose hypothesis `𝔪 • (⊤ : Submodule R R) ≠ ⊤` is `𝔪 ≠ ⊤`, together with
`Module.supportDim_self_eq_ringKrullDim`. It is stated without Noetherian hypothesis because
Stacks 00LK needs none.

## References

* [StacksProject 00OB](https://stacks.math.columbia.edu/tag/00OB)
* [StacksProject 090V](https://stacks.math.columbia.edu/tag/090V)
* [StacksProject 00LK](https://stacks.math.columbia.edu/tag/00LK)
-/

namespace Stacks.ProjectiveDimension.KrullBound



/-- The zero module has projective dimension `⊥`: `CategoryTheory.projectiveDimension_eq_bot_iff`
read for `Module.projectiveDimension`. -/
private lemma projectiveDimension_eq_bot_of_subsingleton (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M] [Subsingleton M] : Module.projectiveDimension R M = ⊥ :=
  (CategoryTheory.projectiveDimension_eq_bot_iff _).2 (ModuleCat.isZero_of_subsingleton _)

/-- **Projective dimension is at most the depth of the ring.** For `M` a finite module of finite
projective dimension over a Noetherian local ring, the Auslander-Buchsbaum formula
`pd_R M + depth_𝔪(M) = depth_𝔪(R)` (Stacks 090V) exhibits `pd_R M` as a summand of
`depth_𝔪(R)`, hence bounds it by `depth_𝔪(R)`. Unlike 090V this needs no nontriviality of `M`,
the zero module having `pd_R M = ⊥`. -/
private lemma projectiveDimension_le_depth_self {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Module.projectiveDimension R M ≠ ⊤) :
    Module.projectiveDimension R M ≤
      (Module.depth R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) := by
  rcases subsingleton_or_nontrivial M with _ | _
  · simp [projectiveDimension_eq_bot_of_subsingleton R M]
  · calc Module.projectiveDimension R M
        ≤ Module.projectiveDimension R M +
          (Module.depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) :=
          WithBot.le_self_add WithBot.coe_ne_bot _
      _ = (Module.depth R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) :=
          Module.projectiveDimension_add_depth_eq_depth_self M hM

/-- **Depth is at most the dimension**, for a local ring along its maximal ideal. -/
private alias depth_le_ringKrullDim := Module.depth_le_ringKrullDim

/-- **Stacks 00OB.** Over a Noetherian local ring `R`, a finite module of finite projective
dimension has projective dimension at most `dim R`: `pd_R M ≤ depth_𝔪(R) ≤ dim R`. -/
public theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Module.projectiveDimension R M ≠ ⊤) :
    Module.projectiveDimension R M ≤ ringKrullDim R :=
  (projectiveDimension_le_depth_self M hM).trans (depth_le_ringKrullDim R)

end Stacks.ProjectiveDimension.KrullBound

/-!
# Finite projective dimension is bounded by the dimension of a Noetherian local ring

Let `(R, 𝔪, κ)` be a Noetherian local ring and let `M` be a finite `R`-module of finite
projective dimension. Then `pd_R M ≤ dim R`.

The source's proof, for `M = κ`, runs as follows. Choose a finite resolution of `M` by finite
free modules (Lemma 0CXF) and, using Lemma 00MT, arrange that `Im(F_i → F_{i-1}) ⊆ 𝔪 F_{i-1}`,
which is possible because splitting off a trivial summand can only shorten the resolution. Say
`F_n ≠ 0` and `F_i = 0` for `i > n`, so that `n = pd_R M`. Proposition 00N1 applied to the exact
complex `0 → F_n → ⋯ → F_0` gives `depth_{I(φ_n)}(R) ≥ n`, the ideal `I(φ_n)` of maximal minors
of the last map being contained in `𝔪`, hence `≠ R`, by minimality; a fortiori
`depth_𝔪(R) ≥ n`. Lemma 00LK applied to the nonzero finite module `R` then gives
`dim R = dim Supp(R) ≥ depth_𝔪(R) ≥ n`.

Together with Lemma 00OA (`dim_κ 𝔪/𝔪² ≤ pd_R κ`) the case `M = κ` is what makes a Noetherian
local ring of finite global dimension regular, Proposition 00OC.

## Main results

* `Module.projectiveDimension_le_ringKrullDim`: over a Noetherian local ring, a finite module of
  finite projective dimension has projective dimension at most the Krull dimension of the ring.

## Implementation notes

The statement is for an arbitrary finite module `M`, where the source writes the residue field
`κ`. This is a genuine generalization and not a reshaping: the source's argument uses only that
`M` is a finite module over a Noetherian local ring, through the existence of a minimal finite
free resolution, and the dependent Proposition 00OC needs exactly the instance
`M = IsLocalRing.ResidueField R`, which the abbreviation `Module.projectiveDimension` makes
literally the source's `pd_R κ`. The generalization is the standard consequence of the
Auslander-Buchsbaum formula 090V, `pd_R M + depth_𝔪(M) = depth_𝔪(R)`, together with
`depth_𝔪(R) ≤ dim R` (Lemma 00LK).

`pd_R M` is `Module.projectiveDimension R M` (Tag 00O4), valued in `WithBot ℕ∞`, and `dim R` is
`ringKrullDim R`, valued in the same order, so the inequality is read there. The hypothesis
`pd_R M ≠ ⊤` is the source's "finite projective dimension"
(`CategoryTheory.projectiveDimension_ne_top_iff`), and it cannot be dropped: for
`R = k[x]/(x²)` one has `dim R = 0` while `pd_R κ = ⊤`. No nontriviality of `M` is needed,
`pd_R 0 = ⊥` being below everything, so the hypothesis `M ≠ 0` carried by the source's `κ` and
by 090V is absent here.

`[Small.{v} R]` is the smallness assumption under which `Module.projectiveDimension R M` is the
source's invariant, computed by resolutions of `M` by modules in `M`'s own universe (Lemma 00O5,
Lemma 0CXC); it is the hypothesis 090V carries, and the case `M : Type u` for `R : Type u` needs
no instance beyond the ones Mathlib provides.

Faithfulness. (1) No hypothesis is dead: `IsLocalRing R` gives `𝔪`, `IsNoetherianRing R` and
`Module.Finite R M` give the minimal finite free resolution the bound is read off, and
`pd_R M ≠ ⊤` is what makes the conclusion true rather than vacuous, as `R = k[x]/(x²)` shows.
(2) The scalars and base are the source's: the projective dimension is that of `M` over `R`, and
`dim R` is the Krull dimension of `R` itself, not of a localization or a quotient.
(3) No canonical map is at issue; both sides are invariants pinned by name, and the source's
`n` is pinned as the value `pd_R M` rather than merely bounded by it.
(4) The instantiation is not degenerate: for a discrete valuation ring and `M = κ` both sides
equal `1`, from `0 → R → R → κ → 0` and `dim R = 1`, so the inequality is attained; for
`M = R` it reads `0 ≤ dim R`; and both sides are unbounded over the local ring
of `k[x₁, …, x_d]` at the origin, where `pd_R κ = d = dim R`.

## References

* [StacksProject 00OB](https://stacks.math.columbia.edu/tag/00OB)

## Tags

projective dimension, Krull dimension, Noetherian local ring, residue field, depth,
minimal free resolution, regular local ring
-/

@[expose] public section



namespace Module

/-- **Finite projective dimension is bounded by the dimension.** Let `(R, 𝔪)` be a Noetherian
local ring and let `M` be a finite `R`-module of finite projective dimension. Then
`pd_R M ≤ dim R`. The source states the case `M = κ`, for which the inequality is an equality
(Proposition 00OC). -/
@[stacks 00OB "Stated for an arbitrary finite module `M` rather than only for `κ`, the source's
proof using nothing else; `pd_R M` is `Module.projectiveDimension` (Tag 00O4) and finiteness of
it is `≠ ⊤`. See the module docstring."]
public theorem projectiveDimension_le_ringKrullDim {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : projectiveDimension R M ≠ ⊤) :
    projectiveDimension R M ≤ ringKrullDim R :=
  Stacks.ProjectiveDimension.KrullBound.solution M hM

end Module

end
