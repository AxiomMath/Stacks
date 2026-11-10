module

public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessResolution.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.StepAssembly

/-!
# [Stacks, Tag 02O6] over a field from a family of twists, and what that gives Tag 0BEM

[Stacks, Tag 02O6] over a field says that `Hⁿ(X, ℱ)` is a finite-dimensional `k`-vector space for
`X` proper over `k` and `ℱ` coherent.
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_isProper` reduces
it to a single hypothesis: every coherent module is the target of an epimorphism from *one*
coherent module whose cohomology is finite-dimensional in every degree. This file states that
hypothesis in the shape projective space actually supplies it, so that nothing between the two
named absences and the conclusion remains to be assembled, and carries the result through to the
one consumer whose only remaining hypothesis is [Stacks, Tag 02O6].

**What projective space supplies.** The source's proof of clause (3) of [Stacks, Tag 01YS] uses
two inputs about `ℙⁿ`. The first is the "quotient of twists" clause of the same tag: a coherent
module `ℱ` on `ℙⁿ` admits a surjection `𝒪(-d)^{⊕ r} ⟶ ℱ` for some `d` and some `r`. The second is
the Čech computation of [Stacks, Tag 01XT]: `Hⁿ(ℙⁿ, 𝒪(d))` is finite-dimensional for every `d` and
every `n`. Neither is in the library. What *is* in the library, after this file, is the whole of
the step from those two to the conclusion: the resolving module is a power `(𝒪(-d))^{⊞ r}` of a
single twist, powers of a coherent module are coherent, and finite dimensionality of the
cohomology passes to a power — so the two inputs compose with the descending induction by
application.

**A power of one module, not a sum of several.** The source's surjection is from a direct sum of
twists of *varying* degree, and the heterogeneous case is already available as
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_coproduct`. It is not what is used here:
Serre's statement produces a surjection from a power of a *single* twist, and taking the resolving
module to be `AlgebraicGeometry.Scheme.Modules.biprodPow` of one module avoids the `HasBiproduct`
binder the heterogeneous lemma needs. The family `𝒯` below is indexed so that the twist may still
depend on the module being resolved; only the summands of one resolution are required to be equal.

**And it transports along a closed immersion.** A proper scheme over `k` need not be projective,
so the hypothesis cannot be discharged on `X` itself in general; what the source does is embed.
The composites below therefore also state the conclusion for a closed subscheme `Z` of `X`, which
is the form the curve consumers of this tree need, and in particular give the structure sheaf of
`Z` — base case (1) of the dévissage of [Stacks, Tag 01YH] — from a family of twists on `X` alone.

**What Tag 0BEM gets.** The theorem
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_finiteDimensional_cohomology` is
[Stacks, Tag 0BEM] with [Stacks, Tag 02O6] as its one remaining hypothesis. The last two
theorems below discharge that hypothesis from the family of twists, on `X` and on a closed
subscheme of `X`, so that the residue of [Stacks, Tag 0BEM] becomes the two projective inputs and
an embedding rather than Tag 02O6 as a whole.

## Main results

* `AlgebraicGeometry.exists_isCoherent_and_forall_finiteDimensional_and_epi_of_epi_biprodPow`: a
  surjection from a power of a member of the family is a resolving module in the sense of
  `forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_le`.
* `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_biprodPow_of_le`: the
  descending induction run on a family of twists, with the vanishing degree as a hypothesis and
  no condition on `f`.
* `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_biprodPow`:
  **[Stacks, Tag 02O6] over a field for `X` proper, from the two inputs the source computes on
  projective space.**
* `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isClosedImmersion_of_twists`:
  the same for a closed subscheme of `X`, over the composite structure morphism.
* `…_unit_of_isClosedImmersion_of_twists`, the elided prefix being
  `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField`: **base case (1) of the
  dévissage** for that closed subscheme, in the shape
  `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_devissage` consumes as
  `hunit`.
* `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_epi_biprodPow` and
  `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_isClosedImmersion_of_twists`:
  **[Stacks, Tag 0BEM] with its Tag 02O6 hypothesis replaced by the family of twists**, on `X`
  and on a closed subscheme of `X`.

## Implementation notes

**No tag attribute is attached to anything here, and this file proves no tag.** Every statement
below carries the finiteness of the cohomology of the twists and the existence of the surjection
as explicit hypotheses; the first is [Stacks, Tag 01XT] and the second is a clause of
[Stacks, Tag 01YS], and neither is in the library. By the covering-set rule the attribute for
either tag, and for [Stacks, Tag 02O6] and [Stacks, Tag 0BEM], belongs on none of these
declarations. The attribute token is deliberately not spelled out in this comment: a
comment-blind attribute grep reads a spelled token as coverage.

**The family is a hypothesis, not a construction, and deliberately carries no geometry.** `𝒯` is
an arbitrary family of modules on `X` indexed by `ℕ`; nothing below knows that its members are
twists, that `X` is projective space, or which of the two models of projective space is meant.
That is what keeps this file independent of the identification of
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf` on `Proj R[T₀, …, Tₙ]` with the twists
of `AlgebraicGeometry.projectiveSpaceOverRing`, which is not in the library either: whichever
model carries the twists, the hypotheses below are what it has to produce.

**Which coherence predicate.** `SheafOfModules.IsCoherent` here is the root-level class declared
in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentFinitePresentation.lean`, which is the
one `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_le`,
`AlgebraicGeometry.SheafOfModules.isCoherent_biprodPow` and
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_finiteDimensional_cohomology` all use.
`Stacks.SheafOfModules.IsCoherent` is a *different constant* with the same two fields; nothing
below needs the conversion `SheafOfModules.isCoherent_iff`, and the enclosing namespace does not
begin with `Stacks`, so the relative name resolves to the root class.

## References

* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (T : ℕ → X.Modules)

/-! ### A power of a twist is a resolving module -/

/-- **A surjection from a power of a member of the family is a resolving module.** If every member
of `𝒯` is coherent with finite-dimensional cohomology in every degree, then a surjection
`(𝒯 d)^{⊞ r} ⟶ 𝒢` exhibits `𝒢` as a quotient of a coherent module whose cohomology is
finite-dimensional in every degree — which is the hypothesis
`forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_le` takes.

Coherence of the power is `SheafOfModules.isCoherent_biprodPow` and finite dimensionality of its
cohomology is `finiteDimensional_cohomologyOverField_biprodPow`; there is no hypothesis on `f`. -/
theorem exists_isCoherent_and_forall_finiteDimensional_and_epi_of_epi_biprodPow
    (hTcoh : ∀ d : ℕ, SheafOfModules.IsCoherent (T d))
    (hTfin : ∀ d n : ℕ, FiniteDimensional k (cohomologyOverField k f (T d) n))
    (G : X.Modules) (hG : ∃ d r : ℕ, ∃ φ : (T d).biprodPow r ⟶ G, Epi φ) :
    ∃ E : X.Modules, SheafOfModules.IsCoherent E ∧
      (∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f E n)) ∧ ∃ φ : E ⟶ G, Epi φ := by
  obtain ⟨d, r, φ, hφ⟩ := hG
  exact ⟨(T d).biprodPow r, SheafOfModules.isCoherent_biprodPow (T d) (hTcoh d) r,
    fun n => finiteDimensional_cohomologyOverField_biprodPow k f (T d) r n (hTfin d n), φ, hφ⟩

/-! ### The descending induction on a family of twists -/

/-- Every coherent module is a quotient of a coherent module with finite-dimensional cohomology,
given that it is a quotient of a power of a member of the family. -/
private theorem exists_resolving_of_epi_biprodPow
    (hTcoh : ∀ d : ℕ, SheafOfModules.IsCoherent (T d))
    (hTfin : ∀ d n : ℕ, FiniteDimensional k (cohomologyOverField k f (T d) n))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ d r : ℕ, ∃ φ : (T d).biprodPow r ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G → ∃ E : X.Modules, SheafOfModules.IsCoherent E ∧
      (∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f E n)) ∧ ∃ φ : E ⟶ G, Epi φ :=
  fun G hG => exists_isCoherent_and_forall_finiteDimensional_and_epi_of_epi_biprodPow
    k f T hTcoh hTfin G (hgen G hG)

/-- **The descending induction of [Stacks, Tag 02O6] run on a family of twists**, with the
vanishing degree as a hypothesis. Suppose the cohomology of every coherent module is
finite-dimensional in all degrees `≥ N`, every member of `𝒯` is coherent with finite-dimensional
cohomology in every degree, and every coherent module is a quotient of a power of a member of
`𝒯`. Then the cohomology of every coherent module is finite-dimensional in every degree.

There is no hypothesis on `f`: properness enters only through `N`, which is discharged in
`forall_finiteDimensional_cohomologyOverField_of_epi_biprodPow`. -/
theorem forall_finiteDimensional_cohomologyOverField_of_epi_biprodPow_of_le (N : ℕ)
    (hN : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, N ≤ n → FiniteDimensional k (cohomologyOverField k f G n))
    (hTcoh : ∀ d : ℕ, SheafOfModules.IsCoherent (T d))
    (hTfin : ∀ d n : ℕ, FiniteDimensional k (cohomologyOverField k f (T d) n))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ d r : ℕ, ∃ φ : (T d).biprodPow r ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f G n) :=
  forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_le k f N hN
    (exists_resolving_of_epi_biprodPow k f T hTcoh hTfin hgen)

/-- **[Stacks, Tag 02O6] over a field from the two inputs the source computes on projective
space.** For `X` proper over `k`, if there is a family `𝒯` of coherent modules whose cohomology is
finite-dimensional in every degree and such that every coherent module on `X` is a quotient of a
power of a member of `𝒯`, then the cohomology of every coherent module on `X` is
finite-dimensional in every degree.

On `ℙⁿ` the family is the twists `𝒪(-d)`: the first hypothesis is the Čech computation of
[Stacks, Tag 01XT] and the second is the "quotient of twists" clause of [Stacks, Tag 01YS]. The
vanishing degree is supplied by
`exists_forall_finiteDimensional_cohomologyOverField_of_le_of_isProper`, which needs only
properness, and a coherent module is quasi-coherent by [Stacks, Tag 01BW]. -/
theorem forall_finiteDimensional_cohomologyOverField_of_epi_biprodPow [IsProper f]
    (hTcoh : ∀ d : ℕ, SheafOfModules.IsCoherent (T d))
    (hTfin : ∀ d n : ℕ, FiniteDimensional k (cohomologyOverField k f (T d) n))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ d r : ℕ, ∃ φ : (T d).biprodPow r ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f G n) :=
  forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_isProper k f
    (exists_resolving_of_epi_biprodPow k f T hTcoh hTfin hgen)

/-! ### Transport to a closed subscheme -/

variable {Z : Scheme.{u}}

/-- **[Stacks, Tag 02O6] over a field for a closed subscheme of a proper scheme carrying a family
of twists.** A proper scheme over a field need not be projective, so the family cannot in general
be produced on the scheme one cares about; what the source does is embed it. If `i : Z ⟶ X` is a
closed immersion into a locally Noetherian `X` proper over `k`, and `X` carries a family of twists
in the sense above, then the cohomology of every coherent module on `Z` is finite-dimensional in
every degree, over the structure morphism `g` presented as the composite.

`Spec k` is not terminal in the category of schemes, so the factorisation `i ≫ f = g` is a
hypothesis and not automatic. -/
theorem forall_finiteDimensional_cohomologyOverField_of_isClosedImmersion_of_twists
    [IsLocallyNoetherian X] [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (g : Z ⟶ Spec (.of k)) (hg : i ≫ f = g)
    (hTcoh : ∀ d : ℕ, SheafOfModules.IsCoherent (T d))
    (hTfin : ∀ d n : ℕ, FiniteDimensional k (cohomologyOverField k f (T d) n))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ d r : ℕ, ∃ φ : (T d).biprodPow r ⟶ G, Epi φ) :
    ∀ G : Z.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, FiniteDimensional k (cohomologyOverField k g G n) :=
  forall_finiteDimensional_cohomologyOverField_of_isClosedImmersion_of_exists_epi_of_eq k f i g hg
    (exists_resolving_of_epi_biprodPow k f T hTcoh hTfin hgen)

/-- **Base case (1) of the dévissage of [Stacks, Tag 01YH], for a closed subscheme of a proper
scheme carrying a family of twists.** `Hⁿ(Z, 𝒪_Z)` is a finite-dimensional `k`-vector space in
every degree.

This is the hypothesis `hunit` of
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_devissage` verbatim, so it can
be fed to it directly; the theorem one step earlier supplies that dévissage's `hclosed` as well,
and indeed makes the dévissage unnecessary.

Coherence of `𝒪_Z` is **not** a hypothesis: `Z` is locally Noetherian by
`AlgebraicGeometry.isLocallyNoetherian_of_isClosedImmersion`, already in this file's import
closure, and the structure sheaf of a locally Noetherian scheme is coherent by
[Stacks, Tag 01XZ], `Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent`.
That local-Noetherianness theorem is deliberately not an instance — its source is determined
only by the morphism `i` — so it is applied by name. -/
theorem forall_finiteDimensional_cohomologyOverField_unit_of_isClosedImmersion_of_twists
    [IsLocallyNoetherian X] [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (g : Z ⟶ Spec (.of k)) (hg : i ≫ f = g)
    (hTcoh : ∀ d : ℕ, SheafOfModules.IsCoherent (T d))
    (hTfin : ∀ d n : ℕ, FiniteDimensional k (cohomologyOverField k f (T d) n))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ d r : ℕ, ∃ φ : (T d).biprodPow r ⟶ G, Epi φ) :
    ∀ n : ℕ,
      FiniteDimensional k (cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) n) :=
  have : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  forall_finiteDimensional_cohomologyOverField_of_isClosedImmersion_of_twists k f T i g hg
    hTcoh hTfin hgen (SheafOfModules.unit Z.ringCatSheaf) inferInstance

/-! ### [Stacks, Tag 0BEM] with its Tag 02O6 hypothesis discharged -/

variable {r : ℕ}

/-- **[Stacks, Tag 0BEM] from a family of twists.** The Euler characteristics of the twists
`ℱ ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r}` of a coherent sheaf on a scheme proper over a field are the
values of a rational polynomial which is zero or of total degree at most `dim Supp ℱ`, provided
the scheme carries a family of twists in the sense of
`forall_finiteDimensional_cohomologyOverField_of_epi_biprodPow`.

`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_finiteDimensional_cohomology` carries
[Stacks, Tag 02O6] as its one remaining hypothesis; this discharges it. The two families are
independent: `𝓛` is the tuple of invertible modules the tag twists by, and `𝒯` is the family that
resolves coherent modules. -/
theorem exists_eulerPolynomial_twistedSheaf_of_epi_biprodPow [IsProper f]
    (L : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
    (hTcoh : ∀ d : ℕ, SheafOfModules.IsCoherent (T d))
    (hTfin : ∀ d n : ℕ, FiniteDimensional k (cohomologyOverField k f (T d) n))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ d s : ℕ, ∃ φ : (T d).biprodPow s ⟶ G, Epi φ)
    (F : X.Modules) (hF : SheafOfModules.IsCoherent F) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤
        topologicalKrullDim (_root_.SheafOfModules.supp F)) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
        = (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
            (@twistedSheaf_isCoherent X r F L _ hF n) : ℚ) :=
  exists_eulerPolynomial_twistedSheaf_of_finiteDimensional_cohomology k f L
    (forall_finiteDimensional_cohomologyOverField_of_epi_biprodPow k f T hTcoh hTfin hgen) F hF

/-- **[Stacks, Tag 0BEM] for a closed subscheme of a proper scheme carrying a family of twists.**
This is the form a projective scheme over a field meets: the family of twists lives on the ambient
`X`, and the Euler polynomial is produced on `Z` for the invertible modules `ℳ` of `Z`.

Properness of `g` is a hypothesis rather than a consequence: a closed immersion into a proper
scheme is proper, but the factorisation `i ≫ f = g` is itself a hypothesis here, since `Spec k` is
not terminal in the category of schemes. -/
theorem exists_eulerPolynomial_twistedSheaf_of_isClosedImmersion_of_twists
    [IsLocallyNoetherian X] [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (g : Z ⟶ Spec (.of k)) (hg : i ≫ f = g) [IsProper g]
    (M : Fin r → Z.Modules)
    [∀ j, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 (M j)]
    (hTcoh : ∀ d : ℕ, SheafOfModules.IsCoherent (T d))
    (hTfin : ∀ d n : ℕ, FiniteDimensional k (cohomologyOverField k f (T d) n))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ d s : ℕ, ∃ φ : (T d).biprodPow s ⟶ G, Epi φ)
    (F : Z.Modules) (hF : SheafOfModules.IsCoherent F) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤
        topologicalKrullDim (_root_.SheafOfModules.supp F)) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
        = (@eulerCharacteristic k _ Z g _ (twistedSheaf F M n)
            (@twistedSheaf_isCoherent Z r F M _ hF n) : ℚ) :=
  exists_eulerPolynomial_twistedSheaf_of_finiteDimensional_cohomology k g M
    (forall_finiteDimensional_cohomologyOverField_of_isClosedImmersion_of_twists k f T i g hg
      hTcoh hTfin hgen) F hF

end AlgebraicGeometry

end
