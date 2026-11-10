module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionColimit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionStepMap
public import StacksCore.Tactic.StacksAttribute

/-!
# The tower of a flat resolution, and the resolution it produces

Let `(C, O)` be a ringed site, let `A` be a sheaf of differential graded `O`-algebras on it and
let `M` be a right differential graded `A`-module. This file builds the tower

`P₀ ⟶ P₁ ⟶ P₂ ⟶ ⋯ ⟶ M`

of the first proof of Tag 0FSH and passes to its colimit.

* `P₀` is the free differential graded module on the sheaf of graded sets of closed sections of
  `M`, with the homomorphism to `M` sending the generator named by a cocycle to that cocycle
  (`SheafOfModules.freeOnClosedSectionsHom`); the induced maps `Hⁿ(P₀) ⟶ Hⁿ(M)` are
  epimorphisms.
* `Pᵢ₊₁` is `SheafOfModules.DifferentialGradedModule.towerStep` of the homomorphism
  `Pᵢ ⟶ M`: the twisted extension of `Pᵢ` by the free module on the sheaf of graded sets whose
  degree-`n` part is the fibre product `Ker(d_{Pᵢ}^n) ×_{Mⁿ, d} M^{n-1}`, with the homomorphism
  to `M` of `SheafOfModules.DifferentialGradedModule.towerStepMap`.
* every stage is flat as a graded module and K-flat, and the kernel of `Hⁿ(Pᵢ) ⟶ Hⁿ(M)` is
  annihilated by `Hⁿ(Pᵢ) ⟶ Hⁿ(Pᵢ₊₁)`.

## Main results

* `SheafOfModules.DifferentialGradedModule.exists_flat_quasiIso`: **every right differential
  graded `A`-module receives a quasi-isomorphism from a right differential graded `A`-module
  which is flat as a graded module and K-flat.** No tower, no generating family and no
  resolution datum is an argument: the sequence is built by recursion from `M` alone.

The same tower, run over a ringed topos and with
`SheafOfModules.IsGoodToposBaseChange` in place of flatness at every stage, gives Tag 0FSH with
the full goodness of Tag 0FSA; that is
`SheafOfModules.DifferentialGradedModule.exists_good_quasiIso` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodDifferentialGradedResolutionToposTower.lean`.

## Implementation notes

The recursion is over the type of *stages*: a right differential graded `A`-module which is flat
as a graded module and K-flat, together with a homomorphism to `M`. One step of the recursion is
`SheafOfModules.DifferentialGradedModule.exists_towerStep`, which produces the next stage, the
transition homomorphism, the compatibility with the homomorphisms to `M`, and the annihilation
of the kernel on cohomology. `Nat.rec` then iterates it from the base stage, and
`CategoryTheory.Functor.ofSequence` and `CategoryTheory.NatTrans.ofSequence` assemble the result
into a functor `ℕ ⥤ DifferentialGradedModule A` with a cocone whose point is `M`, which is the
input of `SheafOfModules.DifferentialGradedModule.exists_quasiIso_of_tower`.

Only the surjectivity of `Hⁿ(P₀) ⟶ Hⁿ(M)` at the first stage is needed: the colimit argument
reads surjectivity at stage `0` and the kernel-annihilation condition at every stage.

**What Tag 0FSH asks, and where the goodness-carrying tower lives.** The source concludes that
the resolving module is *good*, and goodness is the definition of Tag 0FSA,
`SheafOfModules.IsGoodToposBaseChange` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeDifferentialGradedModuleToposPullback.lean` —
conditions (1) and (2) together with condition (3), read over morphisms of ringed topoi. That is
what `SheafOfModules.DifferentialGradedModule.exists_good_quasiIso` of
`GoodDifferentialGradedResolutionToposTower.lean` concludes, running this same tower with
`IsGoodToposBaseChange` at every stage, out of three ingredients:

* `SheafOfModules.freeDGModule_isGoodToposBaseChange` (Tag 0FSG) for the base stage;
* `SheafOfModules.cone_freeDGModule_isGoodToposBaseChange` of
  `ConeFreeDifferentialGradedModuleToposPullback.lean` for each further stage, `towerStep τ`
  being by definition the cone of a homomorphism out of the free module on the boundary pairs of
  `τ`;
* `SheafOfModules.isGoodToposBaseChange_of_isColimit_nat` of
  `GoodDifferentialGradedToposColimit.lean` at the sequential colimit that closes the tower.

The statement in *this* file concludes the quasi-isomorphism together with conditions (1) and
(2), and does so over a bare ringed site with the ring universe and the module universe
independent, which is the shape its consumers use —
`SheafOfModules.DifferentialGradedModule.exists_leftFlat_quasiIso`,
`SheafOfModules.DifferentialGradedModule.GoodResolutionData.flat` and the derived pushforward.
It stays here, rather than being replaced, because `IsGoodToposBaseChange` identifies the two
universes and because the closure lemma for the stages lies downstream of this file: its own
file reaches `DifferentialGradedGoodResolutionDataConstruction.lean`, which imports this one.

## References

* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FSD](https://stacks.math.columbia.edu/tag/0FSD)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules.DifferentialGradedModule

open Stacks Stacks.SheafOfGradedSets

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasWeakSheafify J (Type m)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {Osharp : Sheaf J CommRingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

/-! ### One step of the tower -/

/-- **One step of the tower of the first proof of Tag 0FSH.** From a right differential graded
`A`-module `P` which is flat as a graded module and K-flat, with a homomorphism `τ : P ⟶ M`,
the twisted extension of `P` by the free module on the boundary pairs of `τ` is again flat as a
graded module and K-flat, receives `P`, carries a homomorphism to `M` extending `τ`, and
annihilates every class of `Hⁿ(P)` which dies in `Hⁿ(M)`. -/
theorem exists_towerStep {M P : DifferentialGradedModule.{t, m, m} A} (τ : P ⟶ M)
    (hP : RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) ∧
      RelativeTensor.IsKFlat P) :
    ∃ (Q : DifferentialGradedModule.{t, m, m} A) (σ : Q ⟶ M) (i : P ⟶ Q),
      (RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded Q) ∧
          RelativeTensor.IsKFlat Q) ∧
        i ≫ σ = τ ∧
          ∀ (n : ℤ) (Z : SheafOfModules.{m} (toRingCat J Osharp))
            (g : Z ⟶ P.complex.homology n),
            g ≫ HomologicalComplex.homologyMap τ.toHomologicalComplex n = 0 →
              g ≫ HomologicalComplex.homologyMap i.toHomologicalComplex n = 0 :=
  ⟨towerStep τ, towerStepMap τ, towerStepInclusion τ,
    ⟨twistedExtension_isGradedFlat (boundaryPairs τ.toHomologicalComplex) P (boundaryPairFamily τ)
        (boundaryPairFamily_closed τ) hP.1,
      twistedExtension_isKFlat (boundaryPairs τ.toHomologicalComplex) P (boundaryPairFamily τ)
        (boundaryPairFamily_closed τ) hP.2⟩,
    twistedExtensionInclusion_towerStepMap τ,
    fun n _ g hg ↦ comp_homologyMap_towerStepInclusion_eq_zero τ n g hg⟩

/-! ### The resolution -/

/-- **Every right differential graded `A`-module receives a quasi-isomorphism from a right
differential graded `A`-module which is flat as a graded module and K-flat.**

The source's tower is built here rather than assumed: the first stage is the free differential
graded module on the sheaf of graded sets of closed sections of `M`, each further stage is the
twisted extension of the previous one by the free module on the boundary pairs of its
homomorphism to `M`, and the resolution is the colimit of the resulting sequence. -/
@[stacks 0FSH "the tower of the first proof, built from M alone: the free differential graded \
module on the sheaf of graded sets of closed sections of M, then the twisted extensions by the \
free modules on the boundary pairs of each stage, then the colimit. The ring universe and the \
module universe stay independent here; at a common universe the same tower reaches the full \
goodness of Section 0FSA in \
SheafOfModules.DifferentialGradedModule.exists_good_quasiIso"]
theorem exists_flat_quasiIso (M : DifferentialGradedModule.{t, m, m} A) :
    ∃ (Q : DifferentialGradedModule.{t, m, m} A) (f : Q ⟶ M),
      QuasiIso f.toHomologicalComplex ∧
        RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded Q) ∧
          RelativeTensor.IsKFlat Q := by
  classical
  let Stage := {p : Σ P : DifferentialGradedModule.{t, m, m} A, P ⟶ M //
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded p.1) ∧
      RelativeTensor.IsKFlat p.1}
  have step : ∀ r : Stage, ∃ (r' : Stage) (i : r.1.1 ⟶ r'.1.1),
      i ≫ r'.1.2 = r.1.2 ∧
        ∀ (n : ℤ) (Z : SheafOfModules.{m} (toRingCat J Osharp))
          (g : Z ⟶ (r.1.1).complex.homology n),
          g ≫ HomologicalComplex.homologyMap r.1.2.toHomologicalComplex n = 0 →
            g ≫ HomologicalComplex.homologyMap i.toHomologicalComplex n = 0 := by
    rintro ⟨⟨P, τ⟩, hP⟩
    obtain ⟨Q, σ, i, hQ, hcomm, hkill⟩ := exists_towerStep τ hP
    exact ⟨⟨⟨Q, σ⟩, hQ⟩, i, hcomm, hkill⟩
  choose next transition hcomm hkill using step
  let r₀ : Stage := ⟨⟨freeDGModule (closedSections M.complex) A, freeOnClosedSectionsHom M⟩,
    freeDGModule_isGradedFlat A (closedSections M.complex),
    freeDGModule_isKFlat (closedSections M.complex) A⟩
  let r : ℕ → Stage := Nat.rec r₀ fun _ x ↦ next x
  let gg (n : ℕ) : (r n).1.1 ⟶ (r (n + 1)).1.1 := transition (r n)
  let F : ℕ ⥤ DifferentialGradedModule.{t, m, m} A := Functor.ofSequence gg
  have hF (n : ℕ) : F.map (homOfLE n.le_succ) = gg n := Functor.ofSequence_map_homOfLE_succ gg n
  let c : Cocone F := ⟨M, NatTrans.ofSequence (F := F) (fun n ↦ (r n).1.2) fun n ↦ by
    change F.map (homOfLE n.le_succ) ≫ (r (n + 1)).1.2 = (r n).1.2 ≫ 𝟙 M
    rw [hF, Category.comp_id]
    exact hcomm (r n)⟩
  refine exists_quasiIso_of_tower F c (fun i ↦ (r i).2)
    (fun n ↦ epi_homologyMap_freeOnClosedSectionsHom M n) fun n i Z g hg ↦ ?_
  rw [hF]
  exact hkill (r i) n _ g hg

end SheafOfModules.DifferentialGradedModule

end
