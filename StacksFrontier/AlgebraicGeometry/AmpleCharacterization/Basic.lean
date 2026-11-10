module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingProjImmersion.ProjBasis
public import StacksFrontier.AlgebraicGeometry.SectionExtension.AmpleConsumers
public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The remaining clauses of Stacks Tag 01Q3

Stacks Tag 01Q3 characterises ampleness of an invertible `𝒪_X`-module `L` on a quasi-compact
scheme `X` by nine equivalent conditions, stated over the graded section ring
`S = Γ_*(X, L)`. This file supplies clause (2) — the open immersion into `Proj S` — in both
directions, clause (9), and the converse of the implication `(1) ⇒ (3) ∧ (4)` that
`Stacks.SheafOfModules.Invertible.exists_sections_mem_nonvanishingOpen_le_of_isAmple` records.
Clauses (5) and (6) are in `./ClauseFive.lean`.

## Main results

* `Stacks.AmpleCharacterization.exists_nvUnion_eq_top_and_isOpenImmersion_of_isAmple`:
  **clause (2) of Stacks Tag 01Q3** — for `L` ample the opens `X_s`, with `s ∈ S₊` homogeneous,
  cover `X`, and the morphism `X ⟶ Proj S` they determine is an open immersion.
* `Stacks.AmpleCharacterization.isAmple_of_isOpenImmersion_projHomOfCovers`: **clause (2) implies
  clause (1)**, the converse, for a quasi-compact `X`;
  `Stacks.AmpleCharacterization.isAmple_iff_exists_nvUnion_eq_top_and_isOpenImmersion` is the
  resulting equivalence.
* `Stacks.AmpleCharacterization.isAmple_of_isBasisNonvanishing_and_isBasisAffineNonvanishing`:
  **clauses (3) and (4) imply clause (1)**, the converse of the implication already registered.
* `Stacks.AmpleCharacterization.isAmple_of_isBasisNonvanishing`: **clause (3) alone implies clause
  (1)**, which is the converse from clause (3) as the tag states it — the conjunction above
  consumes only its clause (4) conjunct, so it does not supply this. Stacks Tag 01PX bridges the
  two clauses. The content is the `mpr` of
  `Stacks.SectionExtension.isAmple_iff_compactSpace_and_isBasisNonvanishing`, which is the
  resulting equivalence and was already proved there; this states the implication on its own and
  registers it beside the tag's other clauses.
* `Stacks.AmpleCharacterization.quasiSeparatedSpace_and_exists_epi_biproduct_ideal_of_isAmple`:
  **clause (9)**, clause (8) with its quantifier restricted to the finite-type sheaves of
  ideals.

## The route taken for `(2) ⇒ (1)`

The source proves `(2) ⇒ (1)` by citing Lemmas 01PT and 01Q2 — the invariance of ampleness under
positive tensor powers, and the ampleness of a pullback of `𝒪_{Proj S}(d)` along an open immersion.
Composing those two needs the comparison `j^*𝒪_{Proj S}(d) ≅ L^{⊗ d}`, which does not exist in this
repository (`../SectionRingProjQuasicoherent/TwistCompatibility.lean` records exactly that).

What is used instead is the source's own alternative route, `(2) ⇒ (4) ⇒ (1)`, which the source
calls "clear from Constructions, Section 01M3": the basic opens `D₊(a)` of the homogeneous elements
of positive degree form a basis of `Proj S` (`Stacks.AlgebraicGeometry.ProjBasis`
`.exists_pos_basicOpen_le`) and are affine (`AlgebraicGeometry.Proj.isAffineOpen_basicOpen`). Pulled
back along the open immersion, and using that `j ⁻¹ᵁ D₊(a) = X_a` is clause (1) of Tag 01PZ
(`Stacks.SectionRingProjMorphism.projHomOfCovers_preimage_projBasicOpen`), they give an affine `X_a`
through every point — which is clause (1) outright, by
`AlgebraicGeometry.IsAffineOpen.preimage_of_isOpenImmersion`. No twisting sheaf is needed, and no
part of Tag 01Q2 or Tag 01PT.

## Implementation notes

**Clause (2) is a dependent pair, not a conjunction.** The morphism `X ⟶ Proj S` of Stacks Tag
01PZ is only defined once the `X_s` cover `X` — `Stacks.SectionRingProjMorphism.projHomOfCovers`
takes that covering as an argument — so the second conjunct cannot be stated before the first is
available. `∃ h : nvUnion L = ⊤, IsOpenImmersion (projHomOfCovers L h)` is the faithful reading:
the covering is a `Prop`, so by proof irrelevance the statement is exactly "the `X_s` cover `X`
and the resulting morphism is an open immersion".

**The two spellings of a global section of a tensor power.**
`Stacks.AmpleFiniteAvoidance.nvOpen` is the nonvanishing open of a homogeneous element of the
section ring, which is a morphism `𝟙 ⟶ L ^⊗ n` out of the monoidal unit, while
`Stacks.Ample.IsAmple` is stated with honest global sections of
`Stacks.Ample.tensorPowModule`. `Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq` is the
bridge in one direction; `Stacks.AmpleCharacterization.exists_tensorPow_nvLocus_eq` below is the
other, an alias of `Stacks.FinGenFromCover.exists_global_nonvanishingLocus_eq`, which transports
along `Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow`.

## References

* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01Q1](https://stacks.math.columbia.edu/tag/01Q1)
* [Stacks Project, Tag 01M3](https://stacks.math.columbia.edu/tag/01M3)
* [Stacks Project, Tag 01PX](https://stacks.math.columbia.edu/tag/01PX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.Ample
open Stacks.GradedSections (powSections)
open Stacks.SectionProduct (globalSection)
open Stacks.AmpleFiniteAvoidance (nvOpen nvLocus grading coe_nvOpen)

universe u

namespace Stacks.AmpleCharacterization

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-! ### The vocabulary bridge -/

/-- **The converse vocabulary bridge of `Stacks.AmpleFiniteAvoidance`
`.exists_powSections_nvLocus_eq`.** A homogeneous element of the section ring of degree `n` is the
honest global section of the `n`-th integer tensor power of `L`, with the same nonvanishing
locus. -/
alias exists_tensorPow_nvLocus_eq := Stacks.FinGenFromCover.exists_global_nonvanishingLocus_eq

/-! ### Clause (2) of Stacks Tag 01Q3 -/

/-- **Clause (2) of [Stacks, Tag 01Q3]** — the clause labelled 01Q5: for `L` ample the open sets
`X_s`, with `s ∈ S₊` homogeneous, cover `X`, and the associated morphism `X ⟶ Proj S` is an open
immersion.

The covering is `Stacks.SectionRingProjMorphism.nvUnion_eq_top_of_isAmple`; it is also what makes
the morphism `Stacks.SectionRingProjMorphism.projHomOfCovers` of Stacks Tag 01PZ exist at all. The
open immersion is Stacks Tag 01Q1,
`Stacks.SectionRingProjImmersion.isOpenImmersion_projHomOfIsAmple`. -/
@[stacks 01Q3 "clause (2)", ega "II 4.5.2" "(a) ⇒ (a'')"]
theorem exists_nvUnion_eq_top_and_isOpenImmersion_of_isAmple (hL : IsAmple X L) :
    ∃ h : Stacks.SectionRingProjMorphism.nvUnion L = ⊤,
      IsOpenImmersion (Stacks.SectionRingProjMorphism.projHomOfCovers L h) :=
  ⟨Stacks.SectionRingProjMorphism.nvUnion_eq_top_of_isAmple L hL,
    Stacks.SectionRingProjImmersion.isOpenImmersion_projHomOfIsAmple L hL⟩

/-- **Clause (2) of [Stacks, Tag 01Q3] implies clause (1).** If the opens `X_s` cover the
quasi-compact scheme `X` and the resulting morphism `j : X ⟶ Proj Γ_*(X, L)` is an open immersion,
then `L` is ample.

This is the source's implication `(2) ⇒ (4) ⇒ (1)` in one step: the basic opens `D₊(a)` of the
homogeneous elements of positive degree are a basis of `Proj S` and are affine, so every point of
`X` has one of them around its image inside the (open) range of `j`; its preimage is `X_a`, is
affine because `j` is an open immersion, and contains the point. That is clause (1) of Stacks
Tag 01PS verbatim. -/
@[stacks 01Q3 "clause (2) implies (1)", ega "II 4.5.2" "(a) ⇐ (a'')"]
theorem isAmple_of_isOpenImmersion_projHomOfCovers [CompactSpace X]
    (h : Stacks.SectionRingProjMorphism.nvUnion L = ⊤)
    (hj : IsOpenImmersion (Stacks.SectionRingProjMorphism.projHomOfCovers L h)) :
    IsAmple X L := by
  have hj' := hj
  refine ⟨‹CompactSpace X›, fun x => ?_⟩
  obtain ⟨d, g, hd, hg, hmem, hle⟩ :=
    Stacks.AlgebraicGeometry.ProjBasis.exists_pos_basicOpen_le (grading L)
      (Stacks.SectionRingProjMorphism.projHomOfCovers L h).opensRange
      (x := (Stacks.SectionRingProjMorphism.projHomOfCovers L h).base x) ⟨x, rfl⟩
  obtain ⟨a, rfl⟩ := Stacks.ExternalGrading.mem_summand_iff.mp hg
  have hpre := Stacks.SectionRingProjMorphism.projHomOfCovers_preimage_projBasicOpen L h a hd
  have haff : IsAffineOpen (nvOpen L a) := by
    rw [← hpre]
    exact (Proj.isAffineOpen_basicOpen (grading L) _ (Stacks.ExternalGrading.of_mem_summand d a)
      hd).preimage_of_isOpenImmersion _ hle
  have hx : x ∈ nvOpen L a := by rw [← hpre]; exact hmem
  obtain ⟨s, hs⟩ := exists_tensorPow_nvLocus_eq L d a
  exact ⟨d, hd, s, nvOpen L a, by rw [coe_nvOpen, hs], hx, haff⟩

/-- **Clause (2) of [Stacks, Tag 01Q3] is equivalent to clause (1)**, for a quasi-compact
scheme. -/
theorem isAmple_iff_exists_nvUnion_eq_top_and_isOpenImmersion [CompactSpace X] :
    IsAmple X L ↔ ∃ h : Stacks.SectionRingProjMorphism.nvUnion L = ⊤,
      IsOpenImmersion (Stacks.SectionRingProjMorphism.projHomOfCovers L h) :=
  ⟨exists_nvUnion_eq_top_and_isOpenImmersion_of_isAmple L,
    fun ⟨h, hj⟩ => isAmple_of_isOpenImmersion_projHomOfCovers L h hj⟩

end Monoidal

/-! ### The converse of `(1) ⇒ (3) ∧ (4)` -/

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- **Clauses (3) and (4) of [Stacks, Tag 01Q3] imply clause (1)** — the converse of
`Stacks.SheafOfModules.Invertible.exists_sections_mem_nonvanishingOpen_le_of_isAmple`, which is the
implication `(1) ⇒ (3) ∧ (4)`.

Either clause alone suffices on a quasi-compact scheme: clause (4) applied at the ambient open `⊤`
is condition (2) of Stacks Tag 01PS, and clause (3) yields clause (4) by Stacks Tag 01PX, which is
unconditional here because Tag 01PV is proved. Both are stated so that the conjunction the forward
implication produces can be fed back verbatim. -/
@[stacks 01Q3 "(3) and (4) imply (1)", ega "II 4.5.2" "(a) ⇐ (a')"]
theorem isAmple_of_isBasisNonvanishing_and_isBasisAffineNonvanishing [CompactSpace X]
    (h : Stacks.AmpleTheory.IsBasisNonvanishing X L ∧
      Stacks.AmpleTheory.IsBasisAffineNonvanishing X L) :
    IsAmple X L :=
  Stacks.AmpleTheory.isAmple_of_isBasisAffineNonvanishing X L ‹CompactSpace X› h.2

/-- **Clause (1) if and only if clauses (3) and (4)**, with no hypothesis beyond
invertibility. -/
theorem isAmple_iff_compactSpace_and_isBasisNonvanishing_and_isBasisAffineNonvanishing :
    IsAmple X L ↔ CompactSpace X ∧ Stacks.AmpleTheory.IsBasisNonvanishing X L ∧
      Stacks.AmpleTheory.IsBasisAffineNonvanishing X L :=
  ⟨fun hL => ⟨hL.1, Stacks.SectionExtension.isBasisNonvanishing_of_isAmple X L hL,
      Stacks.SectionExtension.isBasisAffineNonvanishing_of_isAmple X L hL⟩,
    fun h => Stacks.AmpleTheory.isAmple_of_isBasisAffineNonvanishing X L h.1 h.2.2⟩

/-- **Clause (3) of [Stacks, Tag 01Q3] implies clause (1)**, from clause (3) alone: on a
quasi-compact scheme, an invertible `L` whose nonvanishing opens `X_s` — for `s` a global section
of a positive tensor power of `L` — form a basis for the topology is ample.

This is the implication the conjunction above does not give, since that one consumes only its
clause (4) conjunct. Stacks Tag 01PX supplies the step clause (3) ⇒ clause (4): the affine opens
are themselves a basis, so the prescribed open may be shrunk to an affine one before clause (3) is
applied, and the resulting `X_s`, sitting inside an affine open, is affine by Stacks Tag 01PV.
Clause (4) at the ambient open `⊤` is then condition (2) of Stacks Tag 01PS.

The implication was already proved, as the `mpr` of
`Stacks.SectionExtension.isAmple_iff_compactSpace_and_isBasisNonvanishing`, and that is what is
invoked here rather than a second derivation; what this declaration adds is the standalone
statement of the clause, and its registration, beside the other clauses of the tag. Tag 01PX is
likewise already proved and registered — as
`AlgebraicGeometry.Scheme.Modules.isBasis_affine_nonvanishingOpens`, in the Tag 01PS vocabulary —
and in the vocabulary these clauses are stated in it is
`Stacks.NonvanishingAffineIntersection.isBasisAffineNonvanishing_of_isBasisNonvanishing`, which
carries no hypothesis beyond invertibility because Tag 01PV is proved
(`AlgebraicGeometry.Scheme.Modules.isAffineOpen_inf_nonvanishingOpen`).

The hypotheses are exactly clause (3) and the quasi-compactness standing over the whole source
Proposition; nothing is assumed about affineness of the `X_s`, which is precisely what clause (3)
as the tag states it leaves out. -/
@[stacks 01Q3 "clause (3) implies (1)",
  ega "II 4.5.2" "(a) ⇐ (a')",
  ega "II 5.1.2" "d) ⇒ c')",
  sga "6 II 2.2.3" "(i) ⇒ (ii)",
  sga "6 II 2.2.4" "partial"]
theorem isAmple_of_isBasisNonvanishing [CompactSpace X]
    (h : Stacks.AmpleTheory.IsBasisNonvanishing X L) :
    IsAmple X L :=
  (Stacks.SectionExtension.isAmple_iff_compactSpace_and_isBasisNonvanishing X L).mpr
    ⟨‹CompactSpace X›, h⟩

/-! ### Clause (9) of Stacks Tag 01Q3 -/

section ClauseNine

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-- **Clause (9) of [Stacks, Tag 01Q3]** — the clause labelled 01QC: `X` is quasi-separated, and
every sheaf of ideals of finite type on `X` is a quotient of a direct sum of `k` copies of
`L ^⊗ (-n)` for some `n > 0` and `k ≥ 0`.

A sheaf of ideals is presented as a module `J` together with a monomorphism `J ⟶ 𝒪_X`, which is
what "sheaf of ideals" means; `k` is the cardinality of the finite index type `ι`, a direct sum
over a finite index type being a direct sum of `Nat.card ι` copies.

The clause is read with its ideals **quasi-coherent**, as clause (6) of the source states them
explicitly, and this is forced rather than chosen: a quotient of a direct sum of quasi-coherent
modules is quasi-coherent, so the clause would be false for a sheaf of ideals that is not. It is
also what makes the source's "the implication (8) ⇒ (9) is trivial" true, and it is the generality
in which clause (8) is registered
(`Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_exists_epi_biproduct_of_isAmple`).

The proof is exactly the source's: clause (9) is clause (8) with its quantifier restricted, so
clause (8) applied to `J` is the whole content. -/
@[stacks 01Q3 "clause (9)",
  ega "II 2.7.10" "ideals",
  ega "II 4.5.5" "(a) ⇒ (d'), ideals"]
theorem quasiSeparatedSpace_and_exists_epi_biproduct_ideal_of_isAmple (hL : IsAmple X L) :
    QuasiSeparatedSpace X ∧ ∀ (J : X.Modules) (j : J ⟶ unitModule X), Mono j →
      J.IsQuasicoherent → SheafOfModules.IsFiniteType.{u, u, u} J →
        ∃ (n : ℤ) (ι : Type u) (_ : Finite ι), 0 < n ∧
          ∃ (b : CategoryTheory.Limits.Bicone fun _ : ι => tensorPowModule X L (-n))
            (_ : b.IsBilimit) (p : b.pt ⟶ J), CategoryTheory.Epi p := by
  obtain ⟨hqs, h8⟩ :=
    Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_exists_epi_biproduct_of_isAmple L hL
  exact ⟨hqs, fun J _ _ hJqc hJft => h8 J hJqc hJft⟩

end ClauseNine

end Stacks.AmpleCharacterization

end
