module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernSeqIntertwining
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernClasses

/-!
# Chern classes along maps compatible with the projective bundles

Let `(π : P ⟶ X, 𝒪_P(1))` and `(π' : P' ⟶ Y, 𝒪_{P'}(1))` be projective bundle data of the same
fibre dimension over good algebraic spaces `X` and `Y`, and let `g : CH_*(X) ⟶ CH_*(Y)` and
`g' : CH_*(P) ⟶ CH_*(P')` be additive maps compatible with the three operations entering the
Segre operations:

  `g ∘ π_* = π'_* ∘ g'`,   `g' ∘ (c_1(𝒪_P(1)) ∩ -) = (c_1(𝒪_{P'}(1)) ∩ -) ∘ g'`,
  `g' ∘ π^* = π'^* ∘ g`.

Then `g` intertwines the Segre operations `t_i`, hence the Chern operations `c_n`
(`AlgebraicGeometry.Space.PrivateChern.map_chernSeq_of_intertwines`). For a flat morphism
`f : Y ⟶ X` with `P' = P ×_X Y`, the flat pullbacks `g = f^*` and `g' = f'^*` satisfy the three
conditions (flat base change of proper pushforward, compatibility of the first Chern class with
flat pullback, and composition of flat pullbacks), and this gives the compatibility of Chern
classes with flat pullback, part of the bivariance assertion of Stacks 0ERY.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.ProjectiveBundleDatum.segreCap_apply_of_compatible`: the
  Segre operations are intertwined.
* `AlgebraicGeometry.Space.PrivateChern.ProjectiveBundleDatum.chernCap_apply_of_compatible`: the
  Chern operations are intertwined.
* `AlgebraicGeometry.Space.PrivateChern.chernCap_apply_of_compatible`: the same for the Chern
  classes of finite locally free modules.

## References

* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space.PrivateChern

variable {D : BaseSpaceDimensionSituation.{u}} {X Y : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX} {sY : Y ⟶ D.space} {hY : D.IsGood sY}

namespace ProjectiveBundleDatum

variable {d : ℕ} (P : ProjectiveBundleDatum D sX hX d) (P' : ProjectiveBundleDatum D sY hY d)
  (g : chowHomology.{u, v} D sX hX →+ chowHomology.{u, v} D sY hY)
  (g' : chowHomology.{u, v} D P.toBase P.isGood →+ chowHomology.{u, v} D P'.toBase P'.isGood)
  (hpush : ∀ β, g (P.pushforwardChow β) = P'.pushforwardChow (g' β))
  (htwist : ∀ β, g' (P.twistCap β) = P'.twistCap (g' β))
  (hpull : ∀ α, g' (P.pullbackChow α) = P'.pullbackChow (g α))
include hpush htwist hpull

/-- **The Segre operations are intertwined** by maps compatible with pushforward, the twist and
pullback. -/
theorem segreCap_apply_of_compatible (i : ℕ) (α : chowHomology.{u, v} D sX hX) :
    P'.segreCap i (g α) = g (P.segreCap i α) := by
  have hpow : ∀ (k : ℕ) β, g' ((P.twistCap ^ k) β) = (P'.twistCap ^ k) (g' β) := by
    intro k
    induction k with
    | zero => intro β; rfl
    | succ k ih =>
      intro β
      rw [pow_succ, pow_succ]
      show g' ((P.twistCap ^ k) (P.twistCap β)) = (P'.twistCap ^ k) (P'.twistCap (g' β))
      rw [ih, htwist]
  show P'.pushforwardChow ((P'.twistCap ^ (d + i)) (P'.pullbackChow (g α))) =
    g (P.pushforwardChow ((P.twistCap ^ (d + i)) (P.pullbackChow α)))
  rw [hpush, hpow, hpull]

/-- **The Chern operations are intertwined** by maps compatible with pushforward, the twist and
pullback. -/
theorem chernCap_apply_of_compatible (n : ℕ) (α : chowHomology.{u, v} D sX hX) :
    P'.chernCap n (g α) = g (P.chernCap n α) :=
  (map_chernSeq_of_intertwines g
    (fun i α ↦ (segreCap_apply_of_compatible P P' g g' hpush htwist hpull i α).symm) n α).symm

end ProjectiveBundleDatum

/-- **The Chern classes are intertwined** by a map `g : CH_*(X) ⟶ CH_*(Y)` compatible, through
some `g' : CH_*(𝐏(ℰ)) ⟶ CH_*(𝐏(ℰ'))`, with pushforward, the twist and pullback of the projective
bundles of modules `ℰ`, `ℰ'` of rank `d + 1`. -/
theorem chernCap_apply_of_compatible {d : ℕ} (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (E' : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hE : IsFiniteLocallyFreeOfRank D sX hX E (d + 1))
    (hE' : IsFiniteLocallyFreeOfRank D sY hY E' (d + 1))
    (g : chowHomology.{u, v} D sX hX →+ chowHomology.{u, v} D sY hY)
    (g' : chowHomology.{u, v} D (projectiveBundleDatum E d hE).toBase
        (projectiveBundleDatum E d hE).isGood →+
      chowHomology.{u, v} D (projectiveBundleDatum E' d hE').toBase
        (projectiveBundleDatum E' d hE').isGood)
    (hpush : ∀ β, g ((projectiveBundleDatum E d hE).pushforwardChow β) =
      (projectiveBundleDatum E' d hE').pushforwardChow (g' β))
    (htwist : ∀ β, g' ((projectiveBundleDatum E d hE).twistCap β) =
      (projectiveBundleDatum E' d hE').twistCap (g' β))
    (hpull : ∀ α, g' ((projectiveBundleDatum E d hE).pullbackChow α) =
      (projectiveBundleDatum E' d hE').pullbackChow (g α))
    (n : ℕ) (α : chowHomology.{u, v} D sX hX) :
    chernCap.{u, v} E' (d + 1) hE' n (g α) = g (chernCap.{u, v} E (d + 1) hE n α) :=
  ProjectiveBundleDatum.chernCap_apply_of_compatible _ _ g g' hpush htwist hpull n α

/-- The Chern classes of modules of rank `0` are intertwined by every additive map. -/
theorem chernCap_apply_of_rank_zero (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (E' : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hE : IsFiniteLocallyFreeOfRank D sX hX E 0) (hE' : IsFiniteLocallyFreeOfRank D sY hY E' 0)
    (g : chowHomology.{u, v} D sX hX →+ chowHomology.{u, v} D sY hY) (n : ℕ)
    (α : chowHomology.{u, v} D sX hX) :
    chernCap.{u, v} E' 0 hE' n (g α) = g (chernCap.{u, v} E 0 hE n α) :=
  (map_chernSeq_of_intertwines g (fun _ _ ↦ map_zero g) n α).symm

end AlgebraicGeometry.Space.PrivateChern

end
