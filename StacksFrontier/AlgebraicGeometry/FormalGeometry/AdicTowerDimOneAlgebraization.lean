module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleNoetherianDimensionOne.Tower
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicTowerDimOneTwistVanishing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemTheorem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicFiniteAlgebraizationTags

/-!
# Algebraization of a tower of schemes whose closed member is a proper curve

Let `A` be a Noetherian ring complete with respect to an ideal `I`, write `Sₙ = Spec (A / Iⁿ⁺¹)`,
and let `X₀ ⟶ X₁ ⟶ ⋯` be a tower of schemes over the `Sₙ` with cartesian squares, `X₀` proper
over `S₀` of dimension at most one. Then there is a projective morphism `X ⟶ Spec A` with
`Xₙ ≅ X ×_{Spec A} Sₙ` compatibly with the transition maps. This is the scheme case of
[Stacks, Tag 0E7R] (where `A` is local and `I` its maximal ideal), proved as the source proves
it:

1. `X₀` carries an ample invertible module, which lifts to a compatible system `(ℒₙ)` along the
   tower (`Stacks.AmpleNoetherianDimensionOne.exists_ampleInvertibleTower_of_isProper`, the first
   two paragraphs of the source's proof, with [Stacks, Tag 0A26] for the ampleness);
2. Grothendieck's algebraization theorem [Stacks, Tag 089A] in its geometric half
   (`Stacks.AmpleFormalSystemAlgebraization.exists_isProjectiveMorphism_of_isAmple`) produces
   `X`. Its input is the surjectivity of the transition maps on global sections of the
   `ℒₙ ^⊗ d`, which is the long exact sequence step
   `Stacks.AmpleFormalSystemTheorem.surjective_transitionSections_of_isZero_h1` fed by the
   uniform vanishing of the twisted `H¹` in dimension at most one
   (`Stacks.AdicTowerDimOne.exists_uniform_isZero_rightDerived_one_idealSheafTensor`).

No input is carried: the two inputs of the geometric half at the ambient projective space,
[Stacks, Tag 0899] (through [Stacks, Tag 09ZT]) and the uniqueness clause of [Stacks, Tag 0A42],
are discharged by `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_holds` and
`Stacks.AdicClosedSubschemeRigidity.adicRigidity`.

## Main results

* `Stacks.AdicTowerDimOneAlgebraization.exists_isProjectiveMorphism_of_topologicalKrullDim_le_one`
  — the algebraization.

## Implementation notes

The source requires `A` local and `I` its maximal ideal; neither is used, so the statement is for
an arbitrary ideal of a Noetherian complete ring. Properness of `X₀ ⟶ S₀` is part of the
conventions of the source's section on Grothendieck's algebraization theorem and is asked
explicitly.

## References

* [Stacks Project, Tag 0E7R](https://stacks.math.columbia.edu/tag/0E7R)
* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 0A26](https://stacks.math.columbia.edu/tag/0A26)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AdicTowerDimOneAlgebraization

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)

/-- **Algebraization of a tower of schemes whose closed member is a proper curve.** Let `A` be a
Noetherian ring complete with respect to `I` and let `Xₙ` be schemes over
`Sₙ = Spec (A / Iⁿ⁺¹)` forming a tower `iₙ : Xₙ ⟶ Xₙ₊₁` with cartesian squares over the
thickenings `Sₙ ⟶ Sₙ₊₁`. If `X₀ ⟶ S₀` is proper and `dim X₀ ≤ 1`, there are an H-projective
morphism `X ⟶ Spec A` and morphisms `kₙ : Xₙ ⟶ X`, compatible with the `iₙ`, exhibiting every
`Xₙ` as `X ×_{Spec A} Sₙ`. See the module documentation for the proof. -/
public theorem exists_isProjectiveMorphism_of_topologicalKrullDim_le_one
    (hcomplete : IsAdicComplete I A)
    {Xn : ℕ → Scheme.{u}} (q : ∀ n, Xn n ⟶ adicThickening A I n)
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hcart : ∀ n, IsPullback (i n) (q n) (q (n + 1)) (adicThickeningSucc A I n))
    (hproper : IsProper (q 0)) (hdim : topologicalKrullDim (Xn 0 : Type u) ≤ 1) :
    ∃ (X : Scheme.{u}) (fX : X ⟶ Spec (.of A)), IsProjectiveMorphism fX ∧
      ∃ k : ∀ n, Xn n ⟶ X, (∀ n, i n ≫ k (n + 1) = k n) ∧
        ∀ n, IsPullback (k n) (q n) fX (adicThickeningι A I n) := by
  have := hproper
  have : ∀ n, IsClosedImmersion (i n) := fun n =>
    Stacks.AdicTower.isClosedImmersion_transition q i hcart n
  have : ∀ n, AlgebraicGeometry.Surjective (i n) := fun n =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (hcart n).flip inferInstance
  have : IsLocallyNoetherian (Xn 0) := LocallyOfFiniteType.isLocallyNoetherian (q 0)
  have : CompactSpace (Xn 0 : Type u) := QuasiCompact.compactSpace_of_compactSpace (q 0)
  have : AlgebraicGeometry.IsNoetherian (Xn 0) := ⟨⟩
  have hnoeth : ∀ n, NoetherianSpace (Xn n : Type u) := by
    intro n
    induction n with
    | zero => exact AlgebraicGeometry.IsNoetherian.noetherianSpace
    | succ n ih =>
      exact noetherianSpace_of_surjective _ (i n).continuous (i n).surjective
  obtain ⟨L, hL, φ, hample⟩ :=
    Stacks.AmpleNoetherianDimensionOne.exists_ampleInvertibleTower_of_isProper i (q 0) hdim
  have hvan := Stacks.AdicTowerDimOne.exists_uniform_isZero_rightDerived_one_idealSheafTensor
    q i hcart L hL φ hample hdim
  exact Stacks.AmpleFormalSystemAlgebraization.exists_isProjectiveMorphism_of_isAmple A I hcomplete
    (fun N =>
      AmpleFormalSystemTheorem.adicFiniteSystemAlgebraization_of_adicFiniteAlgebraAlgebraization
        A I (Stacks.AmpleFormalSystemAmbient.ambientHom A N)
        (AlgebraicGeometry.adicFiniteAlgebraAlgebraization_holds A I
          (Stacks.AmpleFormalSystemAmbient.ambientHom A N)))
    (Stacks.AmpleFormalSystemTheorem.adicMorphismRigidity_of_adicRigidity A I
      (Stacks.AdicClosedSubschemeRigidity.adicRigidity A I))
    q i hcart L hL hproper hample
    (fun d₁ => by
      obtain ⟨d, hdd, hv⟩ := hvan d₁
      exact ⟨d, hdd, Stacks.AmpleFormalSystemTheorem.powTransitionIso i L hL φ d, fun n =>
        Stacks.AmpleFormalSystemTheorem.surjective_transitionSections_of_isZero_h1 A I q i L hL φ
          hcart d n (hv n)⟩)

end Stacks.AdicTowerDimOneAlgebraization

end
