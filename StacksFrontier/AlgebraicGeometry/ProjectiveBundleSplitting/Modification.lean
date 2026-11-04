module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.Datum
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.SymDatum
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.TrivialSection

/-!
# Tag 0AYP from the epimorphy of the tautological map

`Stacks.Divisors.exists_modification_hasInvertibleFiltration` is Tag 0AYP read off
`Stacks.Divisors.BundleSplittingDatum`, the record of what the projective bundle of a module of
rank `m + 2` supplies. This file builds that record on the graded-algebra presentation
`Stacks.SymGraded.schemeProjectiveBundle` of `𝐏(ℰ)` from a single input: that the tautological
map `π^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)` is an epimorphism.

Everything else the record asks for is a construction. The bundle, its projection and the
properness of that projection, the degree-one twist, its invertibility, the tautological map and
its kernel, and the pullback stability of the tautological sequence are assembled in
`Stacks.ProjectiveBundleSplitting.bundleSplittingDatumOfSym`. The two fields that were still
arguments there are supplied here: the rank of the tautological kernel is
`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible`, and the
section over a nonempty open is
`Stacks.ProjectiveBundleSplitting.exists_nonempty_open_section`, Tag 01OE.

## Main results

* `Stacks.ProjectiveBundleSplitting.nonempty_bundleSplittingDatumOfSym_of_epi`: the splitting
  datum of `𝐏(ℰ)` on an irreducible base, from the epimorphy of the tautological map alone.
* `Stacks.ProjectiveBundleSplitting.exists_modification_hasInvertibleFiltration_of_epi`:
  Tag 0AYP from that same one input, taken for every integral scheme.
* `Stacks.ProjectiveBundleSplitting.exists_nonempty_open_section_projectiveBundle` and
  `Stacks.ProjectiveBundleSplitting.nonempty_bundleSplittingDatum_of_tautological_of_rank`: the
  same on the `Stacks.RelativeProj.Situation` presentation of the bundle, where the input is a
  `Stacks.RelativeProj.TautologicalDatum`.

## Implementation notes

**No point of the bundle is needed.** Rank additivity along the tautological sequence is read at
a point, and `Stacks.ProjectiveBundleSplitting.nonempty_bundleSplittingDatumOfSym_of_rank` takes
one as an argument;
`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible` chooses
the point itself, around the trivialising open it works on, so this file consumes that instead.
Were a point of `𝐏(ℰ)` wanted anyway it would be free here: the section of Tag 01OE has a
nonempty open of the base for its source, and its image is a point of the bundle.

**Why the base is integral in the hypothesis about the datum.** The record asks for a *nonempty*
open of the base, so no record exists over an empty scheme; the hypothesis of
`Stacks.Divisors.exists_modification_hasInvertibleFiltration` quantifies over the integral
schemes, which is exactly where the theorem applies it, and matches what its own attribute
already says.

**The rank of the tautological kernel is read off, not assumed.** The kernel of an epimorphism
onto an invertible module, out of a module of rank `m + 2`, is finite locally free of rank
`m + 1`: local freeness is Tag 05P2's flat-plus-finitely-presented criterion in
`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFree_kernel_of_epi_isInvertible`, and the value
of the rank is forced by additivity in
`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible`.

## References

* [Stacks Project, Tag 0AYP](https://stacks.math.columbia.edu/tag/0AYP)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.SymGraded
open Stacks.WeilCohomology (HasInvertibleFiltration)

universe u

namespace Stacks.ProjectiveBundleSplitting

open Stacks.Divisors

/-- The kernel of an epimorphism from a pullback of a rank `m + 2` module to an invertible module
has rank `m + 1`. -/
private theorem isFiniteLocallyFreeOfRank_kernel_pullback_of_epi {X P : Scheme.{u}} (g : P ⟶ X)
    (E : X.Modules) (m : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 2))
    {L : P.Modules} (q : (Scheme.Modules.pullback g).obj E ⟶ L) (hq : Epi q)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 L) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (kernel q) (m + 1) :=
  have := hE
  isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred q hq hL (m + 1)
    (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ E (m + 2))

/-- **The splitting datum of `𝐏(ℰ)` from the epimorphy of the tautological map.** On an
irreducible base the trivialising open and the section of the projection over it are produced by
Tag 01OE, and a point of the open carries along the section to the point of the bundle at which
the rank of the tautological kernel is read. -/
theorem nonempty_bundleSplittingDatumOfSym_of_epi {X : Scheme.{u}} [IrreducibleSpace X]
    (E : X.Modules) [E.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (hqc : IsQuasicoherentPieces E) (m : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 2))
    (hepi : Epi (tautologicalMap E hqc)) :
    Nonempty (BundleSplittingDatum X E (m + 1)) := by
  obtain ⟨U, hU, σ, hσ⟩ := exists_nonempty_open_section E hqc (m + 1) hE
  have hrank := isFiniteLocallyFreeOfRank_kernel_pullback_of_epi _ E m hE
    (tautologicalMap E hqc) hepi (isInvertible_tautologicalTwist E hqc)
  exact nonempty_bundleSplittingDatumOfSym E hqc (m + 1) hepi hrank ⟨U, hU, σ, hσ⟩

/-- **Stacks Project, Tag 0AYP from the epimorphy of the tautological map.** On an integral
scheme a finite locally free module of rank `r` acquires, after pullback along a modification, a
filtration of length `r` with invertible successive quotients.

The single input is taken for every integral scheme and every module of rank `m + 2` on it: that
the tautological map of the projective bundle of such a module is an epimorphism, which is that
the degree-one twist is generated by its degree-one sections. Everything else — the bundle, its
proper projection, the invertible twist, the pullback stability of the tautological sequence,
the finite local freeness of its kernel and the value of that kernel's rank, and the section
over a nonempty open — is built here out of what is in the library. -/
theorem exists_modification_hasInvertibleFiltration_of_epi
    (hepi : ∀ (Y : Scheme.{u}) [IsIntegral Y] (F : Y.Modules) [F.IsQuasicoherent]
      (hqcF : IsQuasicoherentPieces F), Epi (tautologicalMap F hqcF))
    (r : ℕ) (X : Scheme.{u}) [IsIntegral X] (E : X.Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    ∃ (X' : Scheme.{u}) (f : X' ⟶ X), IsModification f ∧
      HasInvertibleFiltration X' ((Scheme.Modules.pullback f).obj E) r := by
  refine exists_modification_hasInvertibleFiltration ?_ r X E hE
  intro Y _ F m hF
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F :=
    hF.isFiniteLocallyFree
  have : F.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree F
  have hqcF : IsQuasicoherentPieces F := isQuasicoherentPieces_of_isFiniteLocallyFree F
  exact nonempty_bundleSplittingDatumOfSym_of_epi F hqcF m hF (hepi Y F hqcF)

/-! ### The same on the `Situation` presentation -/

/-- **A section over a nonempty open, on the `Situation` presentation of the bundle.** The
section of `Stacks.ProjectiveBundleSplitting.exists_nonempty_open_section` lives on
`Stacks.SymGraded.schemeProjectiveBundle`; `AlgebraicGeometry.projectiveBundlePresentationsAgree`
carries it to `Stacks.RelativeProj.projectiveBundle` over the base. -/
theorem exists_nonempty_open_section_projectiveBundle {X : Scheme.{u}} [IrreducibleSpace X]
    (E : X.Modules) [E.IsQuasicoherent] (n : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)) :
    ∃ (U : X.Opens) (_ : Nonempty U)
      (σ : U.toScheme ⟶ Stacks.RelativeProj.projectiveBundle X E),
        σ ≫ Stacks.RelativeProj.projectiveBundleToBase X E = U.ι := by
  have hqc : IsQuasicoherentPieces E := isQuasicoherentPieces_of_isQuasicoherent E
  obtain ⟨U, hU, τ, hτ⟩ := exists_nonempty_open_section E hqc n hE
  obtain ⟨b, hb⟩ : ∃ b : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme ≅
      Stacks.RelativeProj.projectiveBundle X E,
      b.hom ≫ Stacks.RelativeProj.projectiveBundleToBase X E =
        (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase :=
    AlgebraicGeometry.projectiveBundlePresentationsAgree E hqc
  exact ⟨U, hU, τ ≫ b.hom, by rw [Category.assoc, hb]; exact hτ⟩

/-- **The splitting datum on the `Situation` presentation, with the section discharged.** The
tautological datum of the bundle supplies the twist, its invertibility and the surjection onto
it; the section over a nonempty open and the point at which the rank of the kernel is read are
produced as in
`Stacks.ProjectiveBundleSplitting.nonempty_bundleSplittingDatumOfSym_of_epi`. -/
theorem nonempty_bundleSplittingDatum_of_tautological_of_rank {X : Scheme.{u}}
    [IrreducibleSpace X] (E : X.Modules) [E.IsQuasicoherent] (m : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 2))
    (D : Stacks.RelativeProj.TautologicalDatum X E) :
    Nonempty (BundleSplittingDatum X E (m + 1)) := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
    hE.isFiniteLocallyFree
  obtain ⟨U, hU, σ, hσ⟩ := exists_nonempty_open_section_projectiveBundle E (m + 1) hE
  have hrank := isFiniteLocallyFreeOfRank_kernel_pullback_of_epi _ E m hE D.univ D.epi_univ
    D.invertible
  exact nonempty_bundleSplittingDatum_of_tautological E (m + 1) D hrank ⟨U, hU, σ, hσ⟩

end Stacks.ProjectiveBundleSplitting

end
