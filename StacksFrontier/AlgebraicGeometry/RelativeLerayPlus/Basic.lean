module

public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.AlgebraicGeometry.RelativeLeray.CardVocabulary
public import StacksFrontier.AlgebraicGeometry.RelativeLeray.Leray
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToTransport
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo
public import StacksFrontier.Topology.Sheaves.Functors.Module.EnoughInjectives

/-!
# The relative Leray spectral sequence for bounded below complexes

For composable morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z` and a bounded below
complex `K` of `𝒪_X`-modules, there is a cohomological spectral sequence of `𝒪_Z`-modules with
```
E_2^{p,q} = R ᵖ g_*(H^q(R f_* K)),
```
vanishing for `p < 0`, bounded on every antidiagonal from its starting page, which abuts to
`H^{p+q}(R (f ≫ g)_* K)`.

This is the **bounded below complexes** clause of [Stacks, Tag 01F6].  That clause asks for the
spectral sequence *one complex at a time* -- a function of an object of `D⁺(Mod(𝒪_X))`, with a
`Nonempty`-valued second-page identification and the convergence clause
`CategoryTheory.SpectralSequence.AbutsTo` -- and not as a functor.  No naturality is asked of
it, and none is proved here.

The functorial strengthening is a different statement, and is the subject of
`StacksDraft.AlgebraicGeometry.F3.RelativeLeray.Statement`, whose
`RelativeLeraySpectralSequencePlusData` carries a functor
`D⁺(Mod(𝒪_X)) ⥤ E₂CohomologicalSpectralSequence (Mod(𝒪_Z))` together with a
`FunctorialRightHalfPlaneAbutsTo`.  Neither implies the other mechanically and the clause of the
tag is the objectwise one, so the two live side by side; nothing here supersedes that file.

## Main results

* `Stacks.RelativeLerayPlus.exists_spectralSequence_relativeLerayPlus`: **the relative Leray
  spectral sequence of a bounded below complex**, with all four clauses of
  [Stacks, Tag 01F6]'s bounded-below statement.
* `Stacks.RelativeLerayPlus.relativeLeraySpectralSequencePlus`: the same, packaged as the
  four-clause record `RelativeLeraySpectralSequencePlusData`.

## What the construction satisfies

The spectral sequence is not merely produced; each of the four clauses pins it down, and none of
them is satisfied by an arbitrary term of its type.  Recording this explicitly, since a clause
asking only for data would be satisfied by every spectral sequence whatsoever:

* `pageTwoIso` identifies `E_2^{p,q}` with `R ᵖ g_*(H^q(R f_* K))` for `p : ℕ`, in Mathlib's
  `ℕ`-indexed spelling `CategoryTheory.Functor.rightDerived`.  The zero spectral sequence fails
  this whenever some `R ᵖ g_*(H^q(R f_* K))` is nonzero.
* `pageTwo_isZero` asserts the vanishing in the left half plane, which the identification above
  cannot state because it is indexed by `ℕ`.
* `bounded` asserts that each antidiagonal of the starting page has finitely many nonzero terms.
* `abutment` asserts that `E` abuts to `n ↦ H ⁿ(R (f ≫ g)_* K)`: there is a finite decreasing
  filtration of each `H ⁿ` whose graded pieces are the terms of the infinity page.  This is the
  clause that fails for a spectral sequence unrelated to `f` and `g`.

## Implementation notes

Everything is assembled from statements already in the development; no new mathematics appears
here.

* The spectral sequence is `Stacks.RelativeLeray.exists_spectralSequence_relativeLeray`, which
  is [Stacks, Tag 015N] for the pair `(f_*, g_*)`.  Its `(Fil, Z, D, FH)` presentation is
  universally quantified, so it is instantiated at the defining formulas, each equation holding
  by `rfl`.  The abutment is stated about `(f ≫ g)_*` directly and needs no comparison
  isomorphism, because `f_* ⋙ g_* = (f ≫ g)_*` on the nose
  (`Stacks.RelativeLeray.modulePushforward_comp`).
* The convergence clause is `CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite`, whose only
  hypothesis beyond that presentation is degreewise finiteness of the filtration of the
  auxiliary filtered complex -- which [Stacks, Tag 015N] records as a conclusion.  It is then
  moved off that complex and onto `H ⁿ(R (f ≫ g)_* K)` by
  `CategoryTheory.SpectralSequence.AbutsTo.of_nonempty_iso`, which asks for exactly the
  degreewise `Nonempty` isomorphism types [Stacks, Tag 015N] concludes.
* [Stacks, Tag 015N] states its second page in the `ℤ`-indexed spelling
  `CategoryTheory.Functor.rightDerivedPlus`, while the tag asks for the `ℕ`-indexed
  `CategoryTheory.Functor.rightDerived`.  The comparison is
  `Stacks.DerivedIndexing.rightDerivedIso`.  It exists only in non-negative degrees, which is
  why the left-half-plane vanishing is a separate clause; it is
  `Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj`, part (1) of [Stacks, Tag 05TD],
  transported along the second-page identification.
* The category is written `SheafOfModules.{u} (structureSheafRing X)`; the tag writes
  `Modules X` and `pushforward f`.  These are the same category and the same functor *on the
  nose*, by `Stacks.RelativeLeray.modules_eq_sheafOfModules_ringSheaf` and
  `Stacks.RelativeLeray.pushforward_eq_modulePushforward`, both proved by `rfl`, so the choice of
  spelling is not a weakening of the statement.

## References

* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.RelativeLerayPlus

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] Stacks.RelativeLeray.preservesFiniteLimits_modulePushforward

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The relative Leray spectral sequence of a bounded below complex**, [Stacks, Tag 01F6] for
bounded below complexes.  For `f : X ⟶ Y` and `g : Y ⟶ Z` morphisms of ringed spaces and `K` an
object of `D⁺(Mod(𝒪_X))`, there is a cohomological spectral sequence `E` of `𝒪_Z`-modules,
starting at page `0`, such that

* `E_2^{p,q} ≅ R ᵖ g_*(H^q(R f_* K))` for every `p : ℕ` and `q : ℤ`;
* `E_2^{p,q} = 0` for `p < 0`;
* each antidiagonal of the starting page has only finitely many nonzero terms;
* `E` abuts to `n ↦ H ⁿ(R (f ≫ g)_* K)`.

The clauses are the four the tag states for bounded below complexes.  The spectral sequence is
produced for one `K` at a time, as the tag asks; no naturality in `K` is claimed. -/
theorem exists_spectralSequence_relativeLerayPlus
    (K : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X))) :
    ∃ E : CohomologicalSpectralSequence (SheafOfModules.{u} (structureSheafRing Z)) 0,
      (∀ (p : ℕ) (q : ℤ), Nonempty ((E.page 2 zero_le_two).X ((p : ℤ), q) ≅
        ((modulePushforward g).rightDerived p).obj
          ((DerivedCategory.Plus.homologyFunctor
              (SheafOfModules.{u} (structureSheafRing Y)) q).obj
            ((modulePushforward f).rightDerivedFunctorPlus.obj K)))) ∧
      (∀ p q : ℤ, p < 0 → IsZero ((E.page 2 zero_le_two).X (p, q))) ∧
      (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 0).X (p, n - p))}.Finite) ∧
      SpectralSequence.AbutsTo E (fun n =>
        (DerivedCategory.Plus.homologyFunctor (SheafOfModules.{u} (structureSheafRing Z)) n).obj
          ((modulePushforward (f ≫ g)).rightDerivedFunctorPlus.obj K)) := by
  obtain ⟨L, hL, hfin, hrest⟩ := Stacks.RelativeLeray.exists_spectralSequence_relativeLeray f g K
  obtain ⟨E, e, hE₂, hbdd, -, -, -⟩ := hrest _ (fun _ _ => rfl) _ (fun _ _ _ => rfl)
    _ (fun _ _ _ => rfl) _ (fun _ _ => rfl)
  refine ⟨E, fun p q => ⟨(hE₂ (p : ℤ) q).some ≪≫
      ((Stacks.DerivedIndexing.rightDerivedIso (modulePushforward g) p).app _).symm⟩,
    fun p q hp => (Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj
      (modulePushforward g) p hp _).of_iso (hE₂ p q).some, hbdd, ?_⟩
  exact (CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite L _ (fun _ _ => rfl)
    _ (fun _ _ _ => rfl) _ (fun _ _ _ => rfl) E e hfin).of_nonempty_iso hL

/-- **The request of [Stacks, Tag 01F6] for bounded below complexes.**  For each object of
`D⁺(Mod(𝒪_X))` a cohomological spectral sequence of `𝒪_Z`-modules, its second page identified
with `R ᵖ g_*(H^q(R f_* K))`, its vanishing in the left half plane, its boundedness on each
antidiagonal, and its abutment on `n ↦ H ⁿ(R (f ≫ g)_* K)`.

Four of the five fields are propositions about `sequence`, so inhabiting this structure is a
theorem rather than a choice of data: see the "what the construction satisfies" section of this
file's header. -/
structure RelativeLeraySpectralSequencePlusData where
  /-- A spectral sequence for each bounded below complex. -/
  sequence (K : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X))) :
    CohomologicalSpectralSequence (SheafOfModules.{u} (structureSheafRing Z)) 0
  /-- Its objectwise second-page identification `E_2^{p,q} ≅ R ᵖ g_*(H^q(R f_* K))`. -/
  pageTwoIso (K : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X)))
      (p : ℕ) (q : ℤ) :
    Nonempty (((sequence K).page 2 zero_le_two).X ((p : ℤ), q) ≅
      ((modulePushforward g).rightDerived p).obj
        ((DerivedCategory.Plus.homologyFunctor
            (SheafOfModules.{u} (structureSheafRing Y)) q).obj
          ((modulePushforward f).rightDerivedFunctorPlus.obj K)))
  /-- The terms with negative first coordinate vanish. -/
  pageTwo_isZero (K : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X)))
      (p q : ℤ) (hp : p < 0) :
    IsZero (((sequence K).page 2 zero_le_two).X (p, q))
  /-- The spectral sequence is bounded on each total degree from its starting page. -/
  bounded (K : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X))) (n : ℤ) :
    {p : ℤ | ¬ IsZero (((sequence K).page 0).X (p, n - p))}.Finite
  /-- Convergence gives a finite filtration on each cohomology object. -/
  abutment (K : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X))) :
    SpectralSequence.AbutsTo (sequence K) (fun n =>
      (DerivedCategory.Plus.homologyFunctor (SheafOfModules.{u} (structureSheafRing Z)) n).obj
        ((modulePushforward (f ≫ g)).rightDerivedFunctorPlus.obj K))

/-- **Relative Leray spectral sequence for bounded below complexes**, [Stacks, Tag 01F6].  For
each bounded below complex of `𝒪_X`-modules there is a bounded spectral sequence with second
page `R ᵖ g_*(H^q(R f_* K))`, vanishing in the left half plane, abutting to
`H ⁿ(R (f ≫ g)_* K)` by a finite filtration.

This is `exists_spectralSequence_relativeLerayPlus` with the spectral sequence chosen for each
complex; the four propositional clauses are the content, and all four are proved there. -/
@[stacks 01F6 "bounded below complexes"]
noncomputable def relativeLeraySpectralSequencePlus :
    RelativeLeraySpectralSequencePlusData f g where
  sequence K := (exists_spectralSequence_relativeLerayPlus f g K).choose
  pageTwoIso K := (exists_spectralSequence_relativeLerayPlus f g K).choose_spec.1
  pageTwo_isZero K := (exists_spectralSequence_relativeLerayPlus f g K).choose_spec.2.1
  bounded K := (exists_spectralSequence_relativeLerayPlus f g K).choose_spec.2.2.1
  abutment K := (exists_spectralSequence_relativeLerayPlus f g K).choose_spec.2.2.2

end Stacks.RelativeLerayPlus

end
