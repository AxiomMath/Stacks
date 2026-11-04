module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConeFreeDifferentialGradedModuleToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedToposColimit
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0FSH: every differential graded module receives a quasi-isomorphism from a good one

Let `Y` be a ringed topos, let `A` be a sheaf of differential graded `O_Y`-algebras on it and let
`M` be a right differential graded `A`-module. **There is a quasi-isomorphism `Q ⟶ M` with `Q`
good**, goodness being `SheafOfModules.IsGoodToposBaseChange`: conditions (1), (2) and (3) of
Tag 0FSA, the last at the source's own quantifier over morphisms of ringed topoi.

The tower is the one of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodDifferentialGradedResolutionTower.lean`,
rebuilt here with goodness in place of flatness alone at each stage:

* the base stage is the free differential graded module on the sheaf of graded sets of closed
  sections of `M`, which is good by Tag 0FSG
  (`SheafOfModules.freeDGModule_isGoodToposBaseChange`);
* each further stage is `SheafOfModules.DifferentialGradedModule.towerStep` of the current
  homomorphism to `M`, which is a twisted extension, hence *by definition* the cone of
  `SheafOfModules.dgLiftHom` — a homomorphism whose source is a free module — and therefore good
  by `SheafOfModules.cone_freeDGModule_isGoodToposBaseChange`;
* the resolution is the colimit of the resulting sequence, good by
  `SheafOfModules.isGoodToposBaseChange_of_isColimit_nat`, and the map to `M` is a
  quasi-isomorphism by
  `SheafOfModules.DifferentialGradedModule.quasiIso_desc_of_tower`.

## Main results

* `SheafOfModules.DifferentialGradedModule.exists_towerStep_isGoodToposBaseChange`: one step of
  the tower, carrying goodness in and out.
* `SheafOfModules.DifferentialGradedModule.exists_good_quasiIso`: **Tag 0FSH.**

## Implementation notes

**Why this is a second file and not an edit to the tower.** The closure lemma
`SheafOfModules.cone_freeDGModule_isGoodToposBaseChange` lives downstream of
`GoodDifferentialGradedResolutionTower.lean`: its file imports
`ConeIdentityFreeDifferentialGradedModuleToposPullback.lean`, which imports
`DifferentialGradedGoodResolutionDataConstruction.lean`, which imports the tower. So the tower
file cannot reach the closure lemma, and the goodness-carrying tower is built here instead.
`SheafOfModules.DifferentialGradedModule.exists_flat_quasiIso` in the tower file keeps its own
statement, which is the one its consumers use and which is polymorphic in the ring universe and
the module universe independently.

**Why the universes collapse.** `SheafOfModules.IsGoodToposBaseChange` is stated for a sheaf of
differential graded algebras `A : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)` over a
ringed topos `Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}`, so the ring universe and the
module universe are one and the same; that boundary comes from the differential graded transport
along a morphism of ringed topoi and is recorded in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedToposDirectImage.lean`. The
tower itself has no such restriction, which is why both statements exist.

**Why no pushout appears.** `SheafOfModules.isGoodToposBaseChange_of_isColimit` covers only
shapes whose colimits of sheaves of modules are exact — filtered ones by AB5, discrete ones by
AB4 — because K-flatness of the base change is read off exactness. A pushout is not such a
shape, and the goodness of a stage is accordingly not obtained from the pushout presentation of
its cone: it comes from the admissible short exact sequence of that cone, inside
`SheafOfModules.cone_freeDGModule_isGoodToposBaseChange`. The only colimit taken here is the
sequential one closing the tower, which is filtered.

## References

* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FSD](https://stacks.math.columbia.edu/tag/0FSD)
* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks Stacks.SheafOfGradedSets Stacks.Sheaves.RingedToposModules

universe w v₁ u₁ v₂ u₂

namespace SheafOfModules.DifferentialGradedModule

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasSheafify Y.J (Type w)]
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)}

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-! ### One step of the tower, at the source's own notion of goodness -/

/-- **One step of the tower of the first proof of Tag 0FSH, carrying goodness.** From a good
right differential graded `A`-module `P` with a homomorphism `τ : P ⟶ M`, the twisted extension
of `P` by the free module on the boundary pairs of `τ` is again good, receives `P`, carries a
homomorphism to `M` extending `τ`, and annihilates every class of `Hⁿ(P)` which dies in `Hⁿ(M)`.

Goodness of the new stage is the only clause that is not already in
`SheafOfModules.DifferentialGradedModule.exists_towerStep`, and it is immediate once the stage
is *named* as a cone: `SheafOfModules.DifferentialGradedModule.twistedExtension` is by definition
the cone of `SheafOfModules.dgLiftHom`, whose source is the free module on the boundary pairs, so
`SheafOfModules.cone_freeDGModule_isGoodToposBaseChange` applies on the nose. -/
theorem exists_towerStep_isGoodToposBaseChange [HasWeakSheafify Y.J (Type w)]
    {M P : DifferentialGradedModule.{w, w, w} A} (τ : P ⟶ M)
    (hP : IsGoodToposBaseChange.{w, v₁, u₁} P) :
    ∃ (Q : DifferentialGradedModule.{w, w, w} A) (σ : Q ⟶ M) (i : P ⟶ Q),
      IsGoodToposBaseChange.{w, v₁, u₁} Q ∧
        i ≫ σ = τ ∧
          ∀ (n : ℤ) (Z : SheafOfModules.{w} (toRingCat Y.J Y.O))
            (g : Z ⟶ P.complex.homology n),
            g ≫ HomologicalComplex.homologyMap τ.toHomologicalComplex n = 0 →
              g ≫ HomologicalComplex.homologyMap i.toHomologicalComplex n = 0 :=
  ⟨towerStep τ, towerStepMap τ, towerStepInclusion τ,
    cone_freeDGModule_isGoodToposBaseChange (boundaryPairs τ.toHomologicalComplex) hP
      (dgLiftHom (boundaryPairs τ.toHomologicalComplex) A P (boundaryPairFamily τ)
        (boundaryPairFamily_closed τ)),
    twistedExtensionInclusion_towerStepMap τ,
    fun n _ g hg ↦ comp_homologyMap_towerStepInclusion_eq_zero τ n g hg⟩

/-! ### The resolution -/

/-- **Tag 0FSH: every right differential graded `A`-module receives a quasi-isomorphism from a
good one.** Goodness is `SheafOfModules.IsGoodToposBaseChange`: flat as a graded module, K-flat,
and a pullback exists and is again flat and K-flat along every morphism of ringed topoi out of
the base, every sheaf of differential graded algebras on its source and every unital
homomorphism over it.

The source's tower is built here rather than assumed: the first stage is the free differential
graded module on the sheaf of graded sets of closed sections of `M`, good by Tag 0FSG; each
further stage is the twisted extension of the previous one by the free module on the boundary
pairs of its homomorphism to `M`, good by
`SheafOfModules.cone_freeDGModule_isGoodToposBaseChange` since a twisted extension is the cone of
a homomorphism out of a free module; and the resolution is the colimit of the resulting sequence,
good by `SheafOfModules.isGoodToposBaseChange_of_isColimit_nat`, the sequential shape being
filtered. -/
@[stacks 0FSH]
theorem exists_good_quasiIso [HasWeakSheafify Y.J (Type w)]
    (M : DifferentialGradedModule.{w, w, w} A) :
    ∃ (Q : DifferentialGradedModule.{w, w, w} A) (f : Q ⟶ M),
      QuasiIso f.toHomologicalComplex ∧ IsGoodToposBaseChange.{w, v₁, u₁} Q := by
  classical
  let Stage := {p : Σ P : DifferentialGradedModule.{w, w, w} A, P ⟶ M //
    IsGoodToposBaseChange.{w, v₁, u₁} p.1}
  have step : ∀ r : Stage, ∃ (r' : Stage) (i : r.1.1 ⟶ r'.1.1),
      i ≫ r'.1.2 = r.1.2 ∧
        ∀ (n : ℤ) (Z : SheafOfModules.{w} (toRingCat Y.J Y.O))
          (g : Z ⟶ (r.1.1).complex.homology n),
          g ≫ HomologicalComplex.homologyMap r.1.2.toHomologicalComplex n = 0 →
            g ≫ HomologicalComplex.homologyMap i.toHomologicalComplex n = 0 := by
    rintro ⟨⟨P, τ⟩, hP⟩
    obtain ⟨Q, σ, i, hQ, hcomm, hkill⟩ := exists_towerStep_isGoodToposBaseChange τ hP
    exact ⟨⟨⟨Q, σ⟩, hQ⟩, i, hcomm, hkill⟩
  choose next transition hcomm hkill using step
  let r₀ : Stage := ⟨⟨freeDGModule (closedSections M.complex) A, freeOnClosedSectionsHom M⟩,
    freeDGModule_isGoodToposBaseChange (closedSections M.complex)⟩
  let r : ℕ → Stage := Nat.rec r₀ fun _ x ↦ next x
  let gg (n : ℕ) : (r n).1.1 ⟶ (r (n + 1)).1.1 := transition (r n)
  let F : ℕ ⥤ DifferentialGradedModule.{w, w, w} A := Functor.ofSequence gg
  let c : Cocone F := ⟨M, NatTrans.ofSequence (F := F) (fun n ↦ (r n).1.2) fun n ↦ by
    show F.map (homOfLE (Nat.le_succ n)) ≫ (r (n + 1)).1.2 = (r n).1.2 ≫ 𝟙 M
    rw [show F.map (homOfLE (Nat.le_succ n)) = gg n from
      Functor.ofSequence_map_homOfLE_succ gg n, Category.comp_id]
    exact hcomm (r n)⟩
  have hcol : HasColimitsOfShape ℕ (DifferentialGradedModule.{w, w, w} A) :=
    hasColimitsOfShape_nat (A := A)
  refine ⟨colimit F, (colimit.isColimit F).desc c,
    quasiIso_desc_of_tower F (colimit.isColimit F) c
      (fun n ↦ epi_homologyMap_freeOnClosedSectionsHom M n) (fun n i Z g hg ↦ ?_),
    isGoodToposBaseChange_of_isColimit_nat (colimit.isColimit F) fun n ↦ (r n).2⟩
  rw [show F.map (homOfLE i.le_succ) = gg i from Functor.ofSequence_map_homOfLE_succ gg i]
  exact hkill (r i) n _ g hg

end SheafOfModules.DifferentialGradedModule

end
