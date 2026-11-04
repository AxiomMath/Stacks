module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.FiniteTateTower
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.HomDifferential

/-! # Mapping the degreewise finite Tate tower into a differential graded algebra

`DividedPowers.TateResolution.finiteTateColimit_exists_gradedDPHom` maps the colimit of the
degreewise finite tower into a graded divided power algebra, given a value for every variable
**chosen in advance**. Tate's lifting argument of Tag 0GZ4 cannot use it: the value it must give
to a variable of degree `n + 1` is an element whose boundary is the image of the cycle that the
variable kills, and that image depends on the map already constructed out of the stage `n`. The
values therefore have to be chosen *during* the recursion, and the map has to commute with the
differentials for the choice at the next stage to be possible at all.

This file provides the two halves of that recursion, decoupled so that the consumer supplies its
own induction and its own invariant:

* one step — given a morphism out of the stage `k` which commutes with the differentials, and a
  homogeneous value of degree `k + 1` for each new variable whose boundary is the image of the
  cycle that variable kills, there is a morphism out of the stage `k + 1` restricting to it,
  taking the prescribed values, and again commuting with the differentials;
* the colimit — a family of morphisms out of all the stages, compatible with the steps and each
  commuting with the differentials, assembles into a morphism out of the colimit commuting with
  its differential.

The first is `DividedPowers.TateResolution.IsSetVariableExtension.existsUnique_ringHom` for the
algebra structure and
`DividedPowers.TateResolution.IsSetVariableExtension.algHom_comm_differential` for the
differential. The second is
`DividedPowers.TateResolution.chainColimit_existsUnique_lift` together with the fact that every
element of the colimit comes from a stage, so that commuting with the differential is checked one
stage at a time.

## Main results

* `DividedPowers.TateResolution.finiteTateStep_exists_gradedDPHom_comm_differential` — the
  inductive step.
* `DividedPowers.TateResolution.finiteTateColimit_exists_gradedDPHom_of_family` — the colimit.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 0GZ4](https://stacks.math.columbia.edu/tag/0GZ4)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v y

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

section Lift

variable {R : Type u} [CommRing R] (A₀ : TateStageData.{u, v} R 0)

/-- **The inductive step of Tate's lifting argument.** Let `G` be a morphism of graded divided
power algebras from the stage `k` of the degreewise finite tower into a differential graded algebra
`E` with divided powers compatible with its differential, and suppose `G` commutes with the two
differentials. Suppose given, for each variable `j` of degree `k + 1`, an element `t j` of `E`
homogeneous of degree `k + 1` whose boundary is the image under `G` of the degree-`k` cycle that
`j` kills. Then `G` extends to a morphism out of the stage `k + 1` sending each variable `j` to
`t j`, and the extension again commutes with the differentials.

The hypothesis on `t` is exactly what the vanishing of a transition map on homology provides in
Tag 0GZ4: the image of the cycle is a boundary, and `t j` is a chosen primitive. -/
public theorem finiteTateStep_exists_gradedDPHom_comm_differential (k : ℕ)
    (E : GradedDPAlgebra.{u, y} R) (dE : E.carrier →ₗ[R] E.carrier)
    (hdgaE : IsDifferentialGradedAlgebra E.grade dE)
    (hcompE : IsCompatibleWithDifferential E.gamma dE)
    (G : GradedDPHom (finiteTateAlgebra A₀ k) E)
    (hGd : ∀ a : (finiteTateAlgebra A₀ k).carrier,
      G.hom (finiteTateDifferential A₀ k a) = dE (G.hom a))
    (t : finiteTateIndex A₀ k → E.carrier)
    (ht : ∀ j : finiteTateIndex A₀ k, t j ∈ E.grade (k + 1))
    (hdt : ∀ j : finiteTateIndex A₀ k, dE (t j) = G.hom (finiteTateCycle A₀ k j)) :
    ∃ G' : GradedDPHom (finiteTateAlgebra A₀ (k + 1)) E,
      (∀ x : (finiteTateAlgebra A₀ k).carrier,
          G'.hom ((finiteTateStep A₀ k).hom x) = G.hom x) ∧
        (∀ j : finiteTateIndex A₀ k, G'.hom (finiteTateGenerator A₀ k j) = t j) ∧
          ∀ a : (finiteTateAlgebra A₀ (k + 1)).carrier,
            G'.hom (finiteTateDifferential A₀ (k + 1) a) = dE (G'.hom a) := by
  classical
  obtain ⟨g1, hg1, -⟩ := (finiteTateStage_isSetVariableExtension A₀ k).existsUnique_ringHom
    E.grade E.gamma G.hom.toRingHom t G.map_grade G.map_dpow ht
  have hcomm : ∀ c : R, g1 (algebraMap R (finiteTateAlgebra A₀ (k + 1)).carrier c) =
      algebraMap R E.carrier c := by
    intro c
    rw [← (finiteTateStep A₀ k).hom.commutes c, hg1.1]
    exact G.hom.commutes c
  let G' : GradedDPHom (finiteTateAlgebra A₀ (k + 1)) E :=
    ⟨{ toRingHom := g1, commutes' := hcomm }, hg1.2.2.1, hg1.2.2.2⟩
  have hG'coeff : ∀ x : (finiteTateAlgebra A₀ k).carrier,
      G'.hom ((finiteTateStep A₀ k).hom x) = G.hom x := hg1.1
  have hG'gen : ∀ j : finiteTateIndex A₀ k, G'.hom (finiteTateGenerator A₀ k j) = t j :=
    hg1.2.1
  refine ⟨G', hG'coeff, hG'gen, ?_⟩
  refine (finiteTateStage_isSetVariableExtension A₀ k).algHom_comm_differential
    (finiteTateDga A₀ (k + 1)) hdgaE (finiteTateCompatible A₀ (k + 1)) hcompE G'.hom
    G'.map_grade G'.map_dpow (fun a => ?_) (fun j => ?_)
  · rw [finiteTateStep_differential A₀ k, hG'coeff, hG'coeff, hGd]
  · rw [finiteTateGenerator_differential A₀ k j, hG'coeff, hG'gen, hdt j]

/-- **A compatible family of morphisms out of the stages which commute with the differentials
assembles into a morphism out of the colimit commuting with its differential.** Commuting with the
differential is a condition on single elements, and every element of the colimit comes from a
stage, so it is enough to know it stage by stage. -/
public theorem finiteTateColimit_exists_gradedDPHom_of_family
    (E : GradedDPAlgebra.{u, y} R) (dE : E.carrier →ₗ[R] E.carrier)
    (G : ∀ n : ℕ, GradedDPHom (finiteTateAlgebra A₀ n) E)
    (hGstep : ∀ (n : ℕ) (x : (finiteTateAlgebra A₀ n).carrier),
      (G (n + 1)).hom ((finiteTateStep A₀ n).hom x) = (G n).hom x)
    (hGd : ∀ (n : ℕ) (a : (finiteTateAlgebra A₀ n).carrier),
      (G n).hom (finiteTateDifferential A₀ n a) = dE ((G n).hom a)) :
    ∃ F : GradedDPHom (finiteTateColimit A₀) E,
      (∀ (n : ℕ) (x : (finiteTateAlgebra A₀ n).carrier),
          F.hom ((finiteTateInclusion A₀ n).hom x) = (G n).hom x) ∧
        ∀ a : (finiteTateColimit A₀).carrier,
          F.hom (finiteTateColimitDifferential A₀ a) = dE (F.hom a) := by
  obtain ⟨F, hF, -⟩ := chainColimit_existsUnique_lift (finiteTateAlgebra A₀)
    (finiteTateStep A₀) E G hGstep
  refine ⟨F, hF, fun a => ?_⟩
  obtain ⟨n, x, rfl⟩ :=
    chainColimit_exists_stage (finiteTateAlgebra A₀) (finiteTateStep A₀) a
  rw [finiteTateColimitDifferential_inclusion, hF, hF, hGd]

end Lift

end DividedPowers.TateResolution

end
