module

public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalitiesBootstrap
public import StacksFrontier.AlgebraicGeometry.Algebraization.StalkOfIdealOnOpen

/-!
# The bootstrap situation Stacks 0EJ4 (3) produces, with its local hypotheses discharged

`Stacks.Algebraization.satisfiesDepthInequalities_iff_bootstrapSituation` delivers, at a point
`y` of `U ∩ Y`, a bootstrap situation whose data are *identified* with the completed local data
at `y`: the ring and the ideal by an equality of types and a heterogeneous equality of the
structures on them, and the locus `T` by a heterogeneous equality with the set of primes whose
ideal is `𝔪_y^∧`. The bootstrap theorems over such a situation — among them
`Stacks.Algebraization.isIso_localCohomologyToAdicQuotientLimit_and_exists_pow_le_annihilator`
— do not ask for that identification. They ask for `[IsLocalRing B.A]`,
`[IsAdicComplete B.I B.A]` and `B.T = {closedPoint B.A}`, and nothing turns the one into the
other.

This file does that. The three facts about the *concrete* completed data are isolated first, and
then the identifications are transported.

## Main results

* `Stacks.Algebraization.isLocalRing_completedLocalRing` — `𝒪_{U,y}^∧` is local.
* `Stacks.Algebraization.isAdicComplete_completedLocalIdeal` — it is `I𝒪_{U,y}^∧`-adically
  complete.
* `Stacks.Algebraization.completedMaximalIdeal_eq_maximalIdeal` — `𝔪_y^∧` *is* its maximal
  ideal.
* `Stacks.Algebraization.setOf_asIdeal_eq_maximalIdeal` — over a local ring, the primes whose
  ideal is the maximal ideal are the closed point.
* `Stacks.Algebraization.exists_bootstrapSituation_closedPoint` — the transport: the bundle of
  Stacks 0EJ4 (3) yields a bootstrap situation carrying the three hypotheses.

## Implementation notes

`IsLocalRing` of the completion needs the point to lie on `Y`, and that is the only use of `z`
and `hyz`: without them the stalk ideal need not be contained in the maximal ideal of the stalk,
and the completion can be the zero ring. Adic completeness, by contrast, is unconditional —
`AdicCompletion.isAdicComplete_self` — so
`Stacks.Algebraization.isAdicComplete_completedLocalIdeal` takes no point of `Y`.

The ring `Stacks.Algebraization.completedLocalRing` here is the `I`-adic completion of the
stalk, *not* `AlgebraicGeometry.Scheme.completedLocalRing`, which is the `𝔪`-adic one. The two
are different rings away from the generic points of `Y`, and only the `I`-adic one is what
Stacks 0EJ4 (3) produces; `IsAdicComplete` below is accordingly adic completeness for
`I𝒪_{U,y}^∧` and says nothing about `𝔪`.

The transport is stated as a dependent existential, `∃ B, ∃ hlocal : IsLocalRing B.A, …`, with
the closed point of `B.A` spelled against `hlocal`: the locus statement the bootstrap theorems
want cannot even be written down before the local-ring instance is produced, so it cannot be a
separate conjunct of a non-dependent tuple.

## References

* [Stacks Project, Tag 0EJ4](https://stacks.math.columbia.edu/tag/0EJ4), part (3).
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU), the situation.
* [Stacks Project, Tag 0EHB](https://stacks.math.columbia.edu/tag/0EHB), the consumer.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open Stacks.AdicCompletionDimension

universe u v

namespace Stacks.Algebraization

/-- **Over a local ring the primes whose ideal is the maximal ideal are the closed point.** -/
public theorem setOf_asIdeal_eq_maximalIdeal (A : Type u) [CommRing A] [IsLocalRing A] :
    {q : PrimeSpectrum A | q.asIdeal = maximalIdeal A} = {closedPoint A} := by
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact ⟨fun h => PrimeSpectrum.ext h, fun h => by rw [h]; rfl⟩

variable (S : AlgebraizationSituation.{u})

/-- The stalk of the ideal sheaf at any point of `U` is a finitely generated ideal. -/
private theorem fg_stalk_idealOnOpen (y : S.U.toScheme) :
    (IdealSheafData.stalk (idealOnOpen S) y).FG := by
  let : IsLocallyNoetherian S.U.toScheme := isLocallyNoetherian_of_isOpenImmersion S.U.ι
  exact Ideal.fg_of_isNoetherianRing _

/-- **The completed local ring at a point of `U ∩ Y` is a local ring.** The stalk of the ideal
sheaf at a point lying on `Y` is contained in the maximal ideal of the stalk, and the adic
completion of a Noetherian local ring at such an ideal is local. -/
public theorem isLocalRing_completedLocalRing (y : S.U.toScheme) (z : S.Y)
    (hyz : S.U.ι.base y = S.Yι.base z) :
    IsLocalRing (completedLocalRing (idealOnOpen S) y) := by
  let : IsLocallyNoetherian S.U.toScheme := isLocallyNoetherian_of_isOpenImmersion S.U.ι
  exact isLocalRing_adicCompletion_of_le_maximalIdeal _
    (stalk_idealOnOpen_le_maximalIdeal S y z hyz)

/-- **The completed local ring is `I𝒪^∧`-adically complete.** This is
`AdicCompletion.isAdicComplete_self`: the completion of a ring at a finitely generated ideal is
complete for the image of that ideal. No point of `Y` is needed. -/
public theorem isAdicComplete_completedLocalIdeal (y : S.U.toScheme) :
    IsAdicComplete (completedLocalIdeal (idealOnOpen S) y)
      (completedLocalRing (idealOnOpen S) y) := by
  exact AdicCompletion.isAdicComplete_self _ (fg_stalk_idealOnOpen S y)

/-- **`𝔪_y^∧` is the maximal ideal of the completed local ring.** The image of a maximal ideal
containing the completion ideal is maximal, `AdicCompletion.isMaximal_map_of_le`, and over a
local ring a maximal ideal is *the* maximal ideal. -/
public theorem completedMaximalIdeal_eq_maximalIdeal (y : S.U.toScheme) (z : S.Y)
    (hyz : S.U.ι.base y = S.Yι.base z)
    [IsLocalRing (completedLocalRing (idealOnOpen S) y)] :
    completedMaximalIdeal (idealOnOpen S) y =
      maximalIdeal (completedLocalRing (idealOnOpen S) y) := by
  exact IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le _ _
    (stalk_idealOnOpen_le_maximalIdeal S y z hyz) (fg_stalk_idealOnOpen S y))

/-- **The hypotheses the bootstrap theorems carry, discharged from Stacks 0EJ4 (3).** The bundle
that `Stacks.Algebraization.satisfiesDepthInequalities_iff_bootstrapSituation` produces at a
point `y` of `U ∩ Y` yields a bootstrap situation which is local, adically complete, and whose
locus is the closed point — the three inputs of
`Stacks.Algebraization.isEssentiallyConstantInverseSystem_adicQuotientLocalCohomology_bootstrap`
— with every identification of the bundle retained except the one for `T`, which the locus
statement replaces.

The transport is the substitution of the type equality and the heterogeneous equalities of the
ring, ideal and module structures, after which the three facts are the concrete statements about
`𝒪_{U,y}^∧` proved above. -/
public theorem exists_bootstrapSituation_closedPoint
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (s d : ℤ)
    (y : S.U.toScheme) (z : S.Y) (hyz : S.U.ι.base y = S.Yι.base z)
    (hB : ∃ B : BootstrapSituation.{u, u, v},
      B.A = completedLocalRing (idealOnOpen S) y ∧
      HEq B.commRing
        (inferInstance : CommRing (completedLocalRing (idealOnOpen S) y)) ∧
      HEq B.I (completedLocalIdeal (idealOnOpen S) y) ∧
      B.M = completedStalk (idealOnOpen S) F y ∧
      HEq B.addCommGroup
        (inferInstance : AddCommGroup (completedStalk (idealOnOpen S) F y)) ∧
      HEq B.module (inferInstance : Module (completedLocalRing (idealOnOpen S) y)
        (completedStalk (idealOnOpen S) F y)) ∧
      HEq B.T {q : PrimeSpectrum (completedLocalRing (idealOnOpen S) y) |
        q.asIdeal = completedMaximalIdeal (idealOnOpen S) y} ∧
      B.s = s - ((S.distanceToZ z).toNat : ℤ) ∧ B.d = d) :
    ∃ (B : BootstrapSituation.{u, u, v}) (hlocal : IsLocalRing B.A)
      (_ : IsAdicComplete B.I B.A),
      B.T = {@IsLocalRing.closedPoint B.A B.commRing.toCommSemiring hlocal} ∧
      B.A = completedLocalRing (idealOnOpen S) y ∧
      HEq B.commRing
        (inferInstance : CommRing (completedLocalRing (idealOnOpen S) y)) ∧
      HEq B.I (completedLocalIdeal (idealOnOpen S) y) ∧
      B.M = completedStalk (idealOnOpen S) F y ∧
      HEq B.addCommGroup
        (inferInstance : AddCommGroup (completedStalk (idealOnOpen S) F y)) ∧
      HEq B.module (inferInstance : Module (completedLocalRing (idealOnOpen S) y)
        (completedStalk (idealOnOpen S) F y)) ∧
      B.s = s - ((S.distanceToZ z).toNat : ℤ) ∧ B.d = d := by
  have hlocal : IsLocalRing (completedLocalRing (idealOnOpen S) y) :=
    isLocalRing_completedLocalRing S y z hyz
  obtain ⟨B, hBA, hBcomm, hBI, hBM, hBadd, hBmod, hBT, hBs, hBd⟩ := hB
  cases B
  rename_i A bc bn bI bM ba bmod bf bT bsub bstable bs bd bdual bcd bdepth bcomp
  cases hBA
  cases hBcomm
  cases hBI
  cases hBM
  cases hBadd
  cases hBmod
  refine ⟨{ A := completedLocalRing (idealOnOpen S) y
            commRing := inferInstance
            isNoetherianRing := bn
            I := completedLocalIdeal (idealOnOpen S) y
            M := completedStalk (idealOnOpen S) F y
            addCommGroup := inferInstance
            module := inferInstance
            finite := bf
            T := bT
            subset_adicLocus := bsub
            stableUnderSpecialization := bstable
            s := bs
            d := bd
            dualizing := bdual
            cohomologicalDimension_le := bcd
            depth_or_depth_add_dimension := bdepth
            completedLocalDepth := bcomp },
    hlocal, isAdicComplete_completedLocalIdeal S y, ?_, rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl,
    HEq.rfl, hBs, hBd⟩
  have hT : bT = {q : PrimeSpectrum (completedLocalRing (idealOnOpen S) y) |
      q.asIdeal = completedMaximalIdeal (idealOnOpen S) y} := eq_of_heq hBT
  change bT = {closedPoint (completedLocalRing (idealOnOpen S) y)}
  rw [hT, completedMaximalIdeal_eq_maximalIdeal S y z hyz]
  exact setOf_asIdeal_eq_maximalIdeal _

end Stacks.Algebraization

end
