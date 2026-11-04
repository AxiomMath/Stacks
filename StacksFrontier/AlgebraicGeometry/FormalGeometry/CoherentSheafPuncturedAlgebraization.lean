module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentSheafHypothesisTranslation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonAtAdicLimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.OpenCohomologyBaseTower
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedNeighbourhoodWhole
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.TildeAdicQuotientTower

/-!
# Stacks 0DXQ, for an arbitrary coherent sheaf on the punctured spectrum

Let `(A, 𝔪)` be a Noetherian local ring which has a dualizing complex and is complete with
respect to an ideal `I`.  Set `X = Spec A`, `Y = V(I)` and `U = X ∖ {𝔪}`, and let `ℱ` be a
coherent sheaf on `U`.  Assume

1. `cd(A, I) ≤ d`;
2. for every `x ∈ X ∖ Y` whose closure in `X` meets `U ∩ Y`, either `depth(ℱ_x) ≥ s` or
   `depth(ℱ_x) + dim(closure of x) > d + s`;

Then there is an open `V₀ ⊆ U` containing `U ∩ Y` such that for every open `V ⊆ V₀` containing
`U ∩ Y` and every `i < s` the map

`H^i(V, ℱ) ⟶ lim_n H^i(U, ℱ/Iⁿℱ)`

is an isomorphism; and if in addition `depth(ℱ_x) + dim(closure of x) > s` for every
`x ∈ U ∩ Y`, then those cohomology groups are finite `A`-modules.  This file proves that
theorem, with the finiteness clause an implication from the extra bound, as in the source.

## Main results

* `Stacks.Algebraization.idealPowerQuotientTowerIsoAdicQuotientModuleSystem` — the two spellings
  of the tower `n ↦ M/IⁿM` in this development agree.
* `Stacks.Algebraization.coherentFormalAlgebraization` — **Stacks 0DXQ**.

## How the statement is read

The theorem's two numbered hypotheses and its extra finiteness hypothesis are stated on the
stalks of `ℱ` itself, by `Stacks.Algebraization.StalkDepthOrDimensionBound` and
`Stacks.Algebraization.StalkDepthAddDimGt`.  The source quantifies hypothesis (2) over the points
of `X ∖ V(I)`, while `ℱ` is only defined on `U`; the two quantifications agree because `I` is
proper, which is `Stacks.Algebraization.mem_complementZeroLocus_maximalIdeal_of_notMem_zeroLocus`
and is proved, not assumed.

The conclusion is read through the finite `A`-module `M` that the first move of the source proof
produces — "choose a finite `A`-module `M` such that `ℱ` is the restriction to `U` of the
coherent module associated to `M`", which is Stacks 0BK0 (1).  The statement below exhibits that
`M` together with

* an isomorphism `ℱ ≅ M̃|_U`, so that the left-hand group `H^i(V, ℱ)` is the group
  `H^i(V, M̃)` that the comparison is stated for, and
* an isomorphism of the tower `n ↦ ℱ/Iⁿℱ` with the tower `n ↦ (M/IⁿM)~|_U`, so that the
  right-hand limit `lim_n H^i(U, ℱ/Iⁿℱ)` is the limit
  `lim_n H^i(U, (M/IⁿM)~)` the comparison is stated for.

Both identifications are then carried out inside the statement rather than left as a step for the
reader: a further conjunct gives `H^i(V, ℱ|_V) ≅ H^i(V, M̃)` for each `V` and each degree, and
another gives the isomorphism of towers `(n ↦ H^i(U, ℱ/Iⁿℱ)) ≅ (n ↦ H^i(U, (M/IⁿM)~))`.  So the
groups the registered comparison is about are, inside Lean, the groups the source names.

The opens `V ⊆ V₀` containing `U ∩ Y` are quantified as ideals `J ⊆ J₀` with
`V(J) ∩ V(I) = {𝔪}`, exactly as the source does: with `V = X ∖ V(J)`, the condition `V ⊆ U` says
`𝔪 ∈ V(J)` and the condition `U ∩ Y ⊆ V` says `V(J) ∩ V(I) ⊆ {𝔪}`.

## Implementation notes

The cohomology groups and the comparison map are the ones of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/PuncturedNeighbourhoodWhole.lean`:
`Stacks.Algebraization.PuncturedNeighbourhood.neighbourhoodToPuncturedLimit` is the canonical map
`H^i(V, M̃) ⟶ lim_n H^i(U, (M/IⁿM)~)`, with the limit on the punctured spectrum as the source
takes it, and `Stacks.LocalCohomologySequence.complementCohomologyBase` is `H^i(V, M̃)` read as an
`A`-module.  That file holds the theorem for `ℱ = M̃|_U`, which is one of the two moves of the
source proof; the other — the choice of `M` — is Stacks 0BK0 (1),
`Stacks.LocalCohomology.exists_finiteModule_iso_restrict_tilde`, and the two are combined here.
The `@[stacks 0DXQ]` attribute therefore belongs on this file's theorem and on no statement of
either move alone.

The cohomology of `ℱ` itself is
`Stacks.Algebraization.openCohomologyBase` on the open subscheme `V`, and
`Stacks.Algebraization.openCohomologyBaseFunctor` in its functor form for the tower; the
comparisons with the module-level groups are
`Stacks.Algebraization.openCohomologyBaseRestrictIso` and
`Stacks.Algebraization.quotientSystemOpenCohomologyNatIso`.  The restriction of `ℱ` to
`V = X ∖ V(J)` needs `J ⊆ 𝔪`, which is a reading of `V(J) ∩ V(I) = {𝔪}`:
`Stacks.Algebraization.PuncturedNeighbourhood.le_maximalIdeal_of_zeroLocus_inter`.

Two spellings of the tower `n ↦ M/IⁿM` meet here.  The comparison map is built on
`AlgebraicGeometry.ProEtale.adicQuotientModuleSystem`, while the identification of `ℱ/Iⁿℱ` with
`(M/IⁿM)~|_U` in `StacksFrontier/AlgebraicGeometry/FormalGeometry/TildeAdicQuotientTower.lean` is
built on `Stacks.LocalCohomology.idealPowerQuotientTower`.  The two have the same objects and,
by `Stacks.LocalCohomology.idealPowerQuotientTower_map` and
`Dualizing.adicQuotientModuleSystem_map`, the same transition maps — both are Mathlib's
`AdicCompletion.transitionMap` — so the identity maps assemble into an isomorphism of towers,
which is `Stacks.Algebraization.idealPowerQuotientTowerIsoAdicQuotientModuleSystem` below.  Every
morphism of `ℕᵒᵖ` is the opposite of a `homOfLE`, and there is at most one morphism between two
objects, so the two functors need only be compared on those.

## References

* [Stacks Project, Tag 0DXQ](https://stacks.math.columbia.edu/tag/0DXQ)
* [Stacks Project, Tag 0DXP](https://stacks.math.columbia.edu/tag/0DXP)
* [Stacks Project, Tag 0DXN](https://stacks.math.columbia.edu/tag/0DXN)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Opposite
open AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology Stacks.LocalCohomologySequence

/-! ### The two spellings of the tower `n ↦ M/IⁿM` -/

variable {A : Type u} [CommRing A]

/-- **The two spellings of the tower `n ↦ M/IⁿM` in this development agree.**
`Stacks.LocalCohomology.idealPowerQuotientTower` and
`AlgebraicGeometry.ProEtale.adicQuotientModuleSystem` have the same objects, and on every
morphism of `ℕᵒᵖ` — each of which is the opposite of a `homOfLE`, uniquely — both give Mathlib's
`AdicCompletion.transitionMap`, so the identity maps assemble into an isomorphism of towers. -/
def idealPowerQuotientTowerIsoAdicQuotientModuleSystem (I : Ideal A) (M : ModuleCat.{u} A) :
    idealPowerQuotientTower.{u, u} I M ≅ adicQuotientModuleSystem A I M :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro m n g
    obtain ⟨m⟩ := m
    obtain ⟨n⟩ := n
    have hmn : n ≤ m := leOfHom g.unop
    have hg : g = (homOfLE hmn).op := Subsingleton.elim _ _
    subst hg
    have h1 : (idealPowerQuotientTower.{u, u} I M).map (homOfLE hmn).op =
        (adicQuotientModuleSystem A I M).map (homOfLE hmn).op := by
      rw [Stacks.Algebraization.idealPowerQuotientTower_map I M hmn,
        Dualizing.adicQuotientModuleSystem_map A I M hmn]
    exact (Category.comp_id _).trans (h1.trans (Category.id_comp _).symm))

/-- The identification of the tower `n ↦ ℱ/Iⁿℱ` of a coherent module on `U` presented as `M̃|_U`
with the tower `n ↦ (M/IⁿM)~|_U`, with the module tower in the spelling
`AlgebraicGeometry.ProEtale.adicQuotientModuleSystem` that the comparison map of Stacks 0DXQ is
built on. -/
def quotientSystemNearVanishingAdicTowerIso (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules) (M : ModuleCat.{u} A)
    (e : F ≅ ((tilde.functor (CommRingCat.of A)).obj M).restrict
      (complementZeroLocus A a).ι) :
    quotientSystemNearVanishing A I a F ≅
      (adicQuotientModuleSystem A I M ⋙ tilde.functor (CommRingCat.of A)) ⋙
        Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι :=
  quotientSystemNearVanishingTowerIso A I a F M e ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (idealPowerQuotientTowerIsoAdicQuotientModuleSystem I M)
        (tilde.functor (CommRingCat.of A)))
      (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι)

/-! ### Stacks 0DXQ -/

variable [IsNoetherianRing A] [IsLocalRing A]

/-- **Stacks 0DXQ.**  Let `(A, 𝔪)` be a Noetherian local ring which has a dualizing complex and
is complete with respect to an ideal `I`.  Set `X = Spec A`, `Y = V(I)` and `U = X ∖ {𝔪}`, and
let `ℱ` be a coherent sheaf on `U`.  Assume

1. `cd(A, I) ≤ d`, and
2. for any `x ∈ X ∖ Y` whose closure in `X` meets `U ∩ Y`,
   `depth(ℱ_x) ≥ s` or `depth(ℱ_x) + dim(closure of x) > d + s`,

Then there is an open `V₀ ⊆ U` containing `U ∩ Y` such that for any open `V ⊆ V₀` containing
`U ∩ Y` the map

`H^i(V, ℱ) ⟶ lim_n H^i(U, ℱ/Iⁿℱ)`

is an isomorphism for `i < s`.  If in addition `depth(ℱ_x) + dim(closure of x) > s` for all
`x ∈ U ∩ Y`, then these cohomology groups are finite `A`-modules.

Concretely: there is a finite `A`-module `M` with `ℱ ≅ M̃|_U` and `ℱ/Iⁿℱ ≅ (M/IⁿM)~|_U` as
towers, and an ideal `J₀` with `V(J₀) ∩ V(I) = {𝔪}` — that is, the open
`V₀ = X ∖ V(J₀) ⊆ U` containing `U ∩ Y` — such that for every ideal `J ⊆ J₀` with
`V(J) ∩ V(I) = {𝔪}` — that is, for every open `V = X ∖ V(J) ⊆ V₀` containing `U ∩ Y` — and every
degree `i < s`, the canonical map `H^i(V, M̃) ⟶ lim_n H^i(U, (M/IⁿM)~)` is an isomorphism, and
`H^i(V, M̃)` is a finite `A`-module whenever the extra depth bound holds.

Both groups of that map are identified with the source's own, so that nothing is left to the
reader:

* `H^i(V, M̃)` is `H^i(V, ℱ|_V)`, the cohomology on `V` of the sheaf `ℱ` itself, by the conjunct
  built from `Stacks.Algebraization.openCohomologyBaseRestrictIso`;
* the tower `n ↦ H^i(U, (M/IⁿM)~)` whose limit the map lands in is the tower
  `n ↦ H^i(U, ℱ/Iⁿℱ)`, transition maps included, by the conjunct built from
  `Stacks.Algebraization.quotientSystemOpenCohomologyNatIso`.  An isomorphism of towers is
  stronger than the isomorphism of limits it induces, so this pins the right-hand side without
  either limit having to be formed again.

The division of the two clauses is the source's.  The comparison is asserted under assumptions
(1) and (2) alone; the extra bound `depth(ℱ_x) + dim(closure of x) > s` on `U ∩ Y` appears only
as the hypothesis of the finiteness clause, where the source puts it ("If in addition …").  One
ideal `J₀` serves both, by the case distinction carried out in
`Stacks.Algebraization.PuncturedNeighbourhood.comparison_and_finiteness`.

Nothing beyond the hypotheses of the theorem is assumed.  The module `M` is produced by Stacks
0BK0 (1), the ideal `J₀` by Stacks 0DXP and Stacks 0DXN, the stabilizing data of Stacks 0EFI and
the bound `0 ≤ d` from assumption (1), and the localization triangle data of the degree-zero case
from a finite generating family of `J`.  Properness of `I` — the source's standing `𝔪 ∈ V(I)`,
without which `V(I)` is empty — is derived too, not assumed: over a local ring `I = A` would make
`A` `⊤`-adically Hausdorff, hence zero.

The two cohomology groups of the conclusion are named through the presentation `ℱ ≅ M̃|_U` and
the tower isomorphism `ℱ/Iⁿℱ ≅ (M/IⁿM)~|_U`, both of which the statement exhibits; this is the
reading the source itself uses, its proof opening with the choice of such an `M`.  The statement
also carries out that reading, exhibiting each of the two groups of the comparison map as the
corresponding group of `ℱ` — see the two conjuncts described above. -/
@[stacks 0DXQ]
theorem coherentFormalAlgebraization (I : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (hcomplete : IsAdicComplete I A)
    (hdualizing : Dualizing.IsDualizingComplex omega)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension A I
      (Ideal.fg_of_isNoetherianRing I) ≤ d)
    (F : (complementZeroLocus A (maximalIdeal A) : Scheme).Modules) [F.IsCoherent]
    (h2 : StalkDepthOrDimensionBound I F s d) :
    ∃ M : ModuleCat.{u} A, Module.Finite A M ∧
      Nonempty (F ≅ ((tilde.functor (CommRingCat.of A)).obj M).restrict
        (complementZeroLocus A (maximalIdeal A)).ι) ∧
      Nonempty (quotientSystemNearVanishing A I (maximalIdeal A) F ≅
        (adicQuotientModuleSystem A I M ⋙ tilde.functor (CommRingCat.of A)) ⋙
          Scheme.Modules.restrictFunctor (complementZeroLocus A (maximalIdeal A)).ι) ∧
      (∀ i : ℕ, Nonempty (quotientSystemNearVanishing A I (maximalIdeal A) F ⋙
          openCohomologyBaseFunctor A (complementZeroLocus A (maximalIdeal A)) i ≅
        adicQuotientModuleSystem A I M ⋙
          complementCohomologyBaseFunctor (A := CommRingCat.of A) (maximalIdeal A) i)) ∧
      ∃ J₀ : Ideal A,
        PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
            {closedPoint A} ∧
          ∀ J : Ideal A, J ≤ J₀ →
            ∀ hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
              {closedPoint A},
            ∀ i : ℕ, (i : ℤ) < s →
              IsIso (PuncturedNeighbourhood.neighbourhoodToPuncturedLimit I J M hV i) ∧
                Nonempty (openCohomologyBase A (complementZeroLocus A J)
                    ((Scheme.Modules.restrictFunctor
                      ((Spec (CommRingCat.of A)).homOfLE
                        (le_complementZeroLocus_maximalIdeal
                          (PuncturedNeighbourhood.le_maximalIdeal_of_zeroLocus_inter hV)))).obj F)
                      i ≅
                  complementCohomologyBase (A := CommRingCat.of A) J M i) ∧
                (StalkDepthAddDimGt I F s →
                  Module.Finite A
                    (complementCohomologyBase (A := CommRingCat.of A) J M i)) := by
  have := hcomplete
  -- Properness of `I` is not a hypothesis: over a local ring `I = A` would force `A = 0`.
  have hI : I ≠ ⊤ := by
    rintro rfl
    refine one_ne_zero (α := A) (hcomplete.toIsHausdorff.haus 1 fun n => ?_)
    have htop : ((⊤ : Ideal A) ^ n • (⊤ : Submodule A A)) = ⊤ := by simp
    rw [SModEq.sub_mem, htop]
    exact Submodule.mem_top
  obtain ⟨M, hMfin, ⟨e⟩⟩ :=
    Stacks.LocalCohomology.exists_finiteModule_iso_restrict_tilde A (maximalIdeal A) F
  have := hMfin
  have hH : PuncturedNeighbourhood.Hypotheses (M := (M : Type u)) I s d omega :=
    hypotheses_of_stalkDepthOrDimensionBound I s d omega hI hcomplete hdualizing hcd e h2
  refine ⟨M, hMfin, ⟨e⟩, ⟨quotientSystemNearVanishingAdicTowerIso I (maximalIdeal A) F M e⟩,
    fun i => ⟨quotientSystemOpenCohomologyNatIso I (maximalIdeal A) F M
      (quotientSystemNearVanishingAdicTowerIso I (maximalIdeal A) F M e) i⟩, ?_⟩
  obtain ⟨J₀, hJ₀, hmain⟩ :=
    PuncturedNeighbourhood.comparison_and_finiteness (M := (M : Type u)) I s d omega hH
  exact ⟨J₀, hJ₀, fun J hJ hV i hi =>
    ⟨(hmain J hJ hV i hi).1,
      ⟨openCohomologyBaseRestrictIso
        (PuncturedNeighbourhood.le_maximalIdeal_of_zeroLocus_inter hV) M e i⟩,
      fun hfin => (hmain J hJ hV i hi).2
        (depthAddDimGtAtMaximalIdeal_of_stalkDepthAddDimGt I s e hfin)⟩⟩

end Stacks.Algebraization

end
