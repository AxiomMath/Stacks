module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicQuotientSystemOfCompleteLocal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SquareZeroQuotientImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.TowerLift

/-!
# The adic tower of square-zero thickenings of a quotient system

Let `R` be a topological ring carrying the `I`-adic topology, with a quotient system over a
base scheme `S`. The positive powers of `I` are weak ideals of definition, so they are stages
of the system, and the transition `Spec (R ⧸ Iⁿ⁺¹) ↪ Spec (R ⧸ Iⁿ⁺²)` is a closed immersion
defined by a square-zero ideal, because `Iⁿ⁺¹` squares into `Iⁿ⁺²`. These stages therefore
form a tower of square-zero thickenings of affine objects of the site, which is the tower a
formally étale transformation lifts compatible families along.

For the maximal ideal of a Noetherian complete local ring the powers of `I` are moreover
cofinal among all weak ideals of definition, so the tower exhausts the formal spectrum.

## Main definitions

* `AlgebraicGeometry.FormalSpace.adicStage`: the `n`-th positive power of the defining ideal,
  as a weak ideal of definition.
* `AlgebraicGeometry.FormalSpace.adicTowerMap`: the transition of the system between
  consecutive adic stages, as a morphism of the big fppf site.

## Main results

* `AlgebraicGeometry.FormalSpace.isSquareZeroClosedImmersion_transition`: a transition of the
  system is a square-zero closed immersion as soon as the larger ideal squares into the
  smaller one.
* `AlgebraicGeometry.FormalSpace.isSquareZeroClosedImmersion_adicTowerMap`: the transitions of
  the adic tower are square-zero closed immersions.
* `AlgebraicGeometry.FormalSpace.exists_compatible_lifts_adicTower_of_formallyEtale`: a
  formally étale transformation lifts a compatible family of sections along the adic tower.

## References

* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace AlgebraicGeometry.FormalSpace

universe v u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {R : Type u} [CommRing R] [TopologicalSpace R]

/-- The underlying scheme morphism of a transition of a quotient system is the comparison map
of the quotient rings. -/
public theorem toScheme_map_transition (D : QuotientSystem B S hS R)
    {J L : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }} (h : J.1 ≤ L.1) :
    (BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map (D.transition h)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) :=
  rfl

/-- The quotient stage of a weak ideal of definition is affine. -/
public theorem isAffine_stageObj (D : QuotientSystem B S hS R)
    (J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj (D.stage J))) := by
  change IsAffine (Spec (.of (R ⧸ J.1)))
  infer_instance

/-- **A transition of a quotient system is a square-zero closed immersion** as soon as the
larger ideal of definition squares into the smaller one. -/
public theorem isSquareZeroClosedImmersion_transition (D : QuotientSystem B S hS R)
    {J L : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }} (h : J.1 ≤ L.1)
    (hsq : L.1 ^ 2 ≤ J.1) :
    Space.IsSquareZeroClosedImmersion B S hS
      ((BigAffineFppf.inclusion B S hS).map (D.transition h)) := by
  refine ⟨?_, ?_⟩
  · rw [toScheme_map_transition]
    exact isClosedImmersion_spec_map_quotientFactor h
  · rw [toScheme_map_transition]
    exact ker_sq_spec_map_quotientFactor_eq_bot h hsq

section Adic

variable {I : Ideal R}

/-- The `(n+1)`-st power of an ideal defining the topology, as a weak ideal of definition. -/
public def adicStage (hadic : IsAdic I) (n : ℕ) :
    { K : Ideal R // TopologicalRing.IsWeakIdealOfDefinition K } :=
  ⟨I ^ (n + 1), isWeakIdealOfDefinition_pow_of_isAdic hadic (Nat.succ_ne_zero n)⟩

/-- Consecutive adic stages are nested. -/
public theorem adicStage_le_succ (hadic : IsAdic I) (n : ℕ) :
    (adicStage hadic (n + 1)).1 ≤ (adicStage hadic n).1 :=
  Ideal.pow_le_pow_right (Nat.le_succ _)

/-- An adic stage squares into the next one. -/
public theorem adicStage_sq_le_succ (hadic : IsAdic I) (n : ℕ) :
    (adicStage hadic n).1 ^ 2 ≤ (adicStage hadic (n + 1)).1 := by
  rw [adicStage, adicStage, ← pow_mul]
  exact Ideal.pow_le_pow_right (by omega)

/-- The transition of the system from one adic stage to the next, as a morphism of the big
fppf site over `S`. -/
public def adicTowerMap (D : QuotientSystem B S hS R) (hadic : IsAdic I) (n : ℕ) :
    (BigAffineFppf.inclusion B S hS).obj (D.stage (adicStage hadic n)) ⟶
      (BigAffineFppf.inclusion B S hS).obj (D.stage (adicStage hadic (n + 1))) :=
  (BigAffineFppf.inclusion B S hS).map (D.transition (adicStage_le_succ hadic n))

/-- **The transitions of the adic tower are square-zero closed immersions.** -/
public theorem isSquareZeroClosedImmersion_adicTowerMap (D : QuotientSystem B S hS R)
    (hadic : IsAdic I) (n : ℕ) :
    Space.IsSquareZeroClosedImmersion B S hS (adicTowerMap D hadic n) :=
  isSquareZeroClosedImmersion_transition D (adicStage_le_succ hadic n)
    (adicStage_sq_le_succ hadic n)

/-- **A formally étale transformation lifts a compatible family of sections along the adic
tower of a quotient system.** Given sections `x n` of `G` over the quotient stages `Spec
(R ⧸ Iⁿ⁺¹)` compatible with the tower, and a lift of `x 0` to `F`, there are compatible lifts
at every stage extending it. -/
public theorem exists_compatible_lifts_adicTower_of_formallyEtale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (a : F ⟶ G) (ha : Space.FormallyEtale a)
    (D : QuotientSystem B S hS R) (hadic : IsAdic I)
    (x : ∀ n : ℕ, G.obj (op ((BigAffineFppf.inclusion B S hS).obj
      (D.stage (adicStage hadic n)))))
    (hx : ∀ n : ℕ, G.map (adicTowerMap D hadic n).op (x (n + 1)) = x n)
    (z₀ : F.obj (op ((BigAffineFppf.inclusion B S hS).obj (D.stage (adicStage hadic 0)))))
    (hz₀ : a.app (op ((BigAffineFppf.inclusion B S hS).obj
      (D.stage (adicStage hadic 0)))) z₀ = x 0) :
    ∃ z : ∀ n : ℕ, F.obj (op ((BigAffineFppf.inclusion B S hS).obj
        (D.stage (adicStage hadic n)))),
      z 0 = z₀ ∧ (∀ n : ℕ, F.map (adicTowerMap D hadic n).op (z (n + 1)) = z n) ∧
        (∀ n : ℕ, a.app (op ((BigAffineFppf.inclusion B S hS).obj
          (D.stage (adicStage hadic n)))) (z n) = x n) :=
  Space.exists_compatible_lifts_of_formallyEtale a ha
    (fun n => (BigAffineFppf.inclusion B S hS).obj (D.stage (adicStage hadic n)))
    (fun n => adicTowerMap D hadic n)
    (fun n => isAffine_stageObj D (adicStage hadic n))
    (fun n => isSquareZeroClosedImmersion_adicTowerMap D hadic n) x hx z₀ hz₀

end Adic

end AlgebraicGeometry.FormalSpace

end
