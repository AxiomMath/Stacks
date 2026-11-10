module

public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessTwists.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharBiproduct.Basic
public import StacksFrontier.AlgebraicGeometry.FreeStalkBasis.BiprodPowStalk

/-!
# [Stacks, Tag 02O6] over a field from the "quotient of twists" clause as the source states it

`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_biprodPow` reduces
[Stacks, Tag 02O6] over a field to a surjection from a **power of a single** member of a family of
modules, `(𝒯 d)^{⊞ r} ⟶ 𝒢`. Clause (1) of [Stacks, Tag 01YS] does not say that. It says that
there are `r ≥ 0` and `d₁, …, d_r ∈ ℤ` and a surjection

  `𝒪(d₁) ⊕ ⋯ ⊕ 𝒪(d_r) ⟶ ℱ`,

a direct sum of twists of **varying** degree; the single-degree form is the separate
[Stacks, Tag 01QB], which is the item of the ample-characterization proposition
[Stacks, Tag 01Q3] that the source's proof of clause (1) *uses*. This file states the reduction at
the heterogeneous shape, so that the hypothesis the library asks of projective space is clause (1)
itself rather than a strengthening of it, and proves that the power form implies the heterogeneous
form — so nothing that could be fed to the power-form reduction is lost.

**What makes the heterogeneous shape usable.** Finite dimensionality of the cohomology of a finite
coproduct is `AlgebraicGeometry.finiteDimensional_cohomologyOverField_coproduct` and coherence of a
finite biproduct is `AlgebraicGeometry.SheafOfModules.isCoherent_biproduct`; both take
`CategoryTheory.Limits.HasBiproduct` as a binder, which the hypothesis below cannot supply because
its family is existentially quantified, and which is not an instance at the `X.Modules` spelling.
`AlgebraicGeometry.Scheme.Modules.hasFiniteBiproducts` is therefore used as a local instance, and
is public rather than private so that a consumer proving something new about the coproduct can do
the same. Without it six declarations below fail with
`failed to synthesize instance HasBiproduct …`. On the other hand, a consumer that only *states* the
hypothesis does **not** need it, because `∐` asks for
`CategoryTheory.Limits.HasCoproduct`, which instance search supplies on an abelian category.

**The family is indexed by an arbitrary type.** Clause (1) indexes the twists by `ℤ`, while
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_biprodPow` indexes its
family by `ℕ`. Taking the index type to be a variable covers both and keeps one statement where
there would otherwise be two.

## Main results

* `AlgebraicGeometry.Scheme.Modules.biprodPowBiconeIsBilimit` and
  `AlgebraicGeometry.Scheme.Modules.biprodPowIsoCoproduct`: **`𝒢^{⊞ n}` is the biproduct, hence
  the coproduct, of `n` copies of `𝒢`.** The two biproduct identities for the explicit inclusions
  and projections of a power are
  `AlgebraicGeometry.Scheme.Modules.biprodPowIncl_proj` and
  `AlgebraicGeometry.Scheme.Modules.biprodPow_total`; this packages them as a bicone and reads off
  the comparison.
* `AlgebraicGeometry.exists_isCoherent_and_forall_finiteDimensional_and_epi_of_epi_coproduct`: a
  surjection from a finite coproduct of members of the family is a resolving module in the sense of
  `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_le`.
* `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_coproduct_of_le`: the
  descending induction with the vanishing degree as a hypothesis and no condition on `f`.
* `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_coproduct`:
  **[Stacks, Tag 02O6] over a field for `X` proper, from clause (1) of [Stacks, Tag 01YS] at the
  shape the source states it.**
* `…_of_isClosedImmersion_of_coproduct` and `…_unit_of_isClosedImmersion_of_coproduct`, the
  elided prefix being `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField`: the same
  for a closed subscheme of `X`, the second in the shape
  `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_devissage` consumes as
  `hunit`.
* `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_epi_coproduct`: **[Stacks, Tag 0BEM]
  with its Tag 02O6 hypothesis replaced by clause (1).**
* `AlgebraicGeometry.exists_epi_coproduct_of_epi_biprodPow`: **the power form implies the
  heterogeneous form**, so the hypothesis of every theorem above is weaker than the hypothesis of
  the corresponding `…_of_epi_biprodPow` theorem, and the theorems above are correspondingly
  stronger.
* `AlgebraicGeometry.exists_coproduct_family_of_forall_finiteDimensional`: the three hypotheses are
  **jointly satisfiable** on every `X` whose coherent cohomology is already known to be
  finite-dimensional — witnessed by the family of all coherent modules, with one summand. This is
  what rules out the hypothesis set being vacuous; see the implementation notes.

## Implementation notes

**No tag attribute is attached to anything here, and this file proves no tag.** Every statement
carries finiteness of the cohomology of the family and the existence of the surjection as explicit
hypotheses; the first is [Stacks, Tag 01XT] and the second is clause (1) of [Stacks, Tag 01YS],
and neither is in the library. By the covering-set rule the attribute for either of those tags,
and for [Stacks, Tag 02O6] and [Stacks, Tag 0BEM], belongs on none of these declarations. The
attribute token is deliberately not spelled out in this comment: a comment-blind attribute grep
reads a spelled token as coverage.

**Why joint satisfiability is recorded as a theorem.** A hypothesis set can compile, be sorry-free
and still be satisfied by nothing, and no axiom check sees that. Here the three hypotheses
constrain the family and, separately, every coherent module, and the family in the surjection
hypothesis is chosen per module, so no binder is shared between them in a way that could force a
contradiction; `AlgebraicGeometry.exists_coproduct_family_of_forall_finiteDimensional` makes that
concrete by exhibiting a family. It takes the conclusion as its hypothesis, so it does not prove
the set satisfiable on projective space — on projective space the family is the twists and the
finiteness of their cohomology is exactly the missing [Stacks, Tag 01XT]. What it does prove is
that the set is consistent, and that it is satisfied wherever the conclusion is.

**Which coherence predicate.** `SheafOfModules.IsCoherent` here is the root-level class declared
in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentFinitePresentation.lean`, which is the
one `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_le`,
`AlgebraicGeometry.SheafOfModules.isCoherent_biproduct` and
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_finiteDimensional_cohomology` all use.
`Stacks.SheafOfModules.IsCoherent` is a *different constant* with the same two fields; nothing
below needs the conversion `SheafOfModules.isCoherent_iff`, and the enclosing namespace does not
begin with `Stacks`, so the relative name resolves to the root class.

**The family carries no geometry, and in particular no model of projective space.** `𝒯` is an
arbitrary family of modules on an arbitrary `X`. That matters here more than it does for the power
form, because the twists of the two models of projective space in this library are different
constants: the twists of `AlgebraicGeometry.projectiveSpaceOverRing` are pullbacks along
`AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse` of the twists of
`AlgebraicGeometry.Proj` of the *integral* polynomial ring, while
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf` of the polynomial ring over the
coefficient ring itself is where the Čech description of the sections lives, and the two schemes
are identified only over the integers
(`Stacks.ProjectiveCohomology.integralModelIso`). Whichever of them a supply of twists is produced
on, the statements below apply to it; what they require is that the finiteness of the cohomology of
the twists and the surjection be produced on the *same* one, over the same structure morphism.

## References

* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01QB](https://stacks.math.columbia.edu/tag/01QB)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe v u

variable {X : Scheme.{u}}

/-! ### A power is a coproduct -/

attribute [local instance] hasFiniteBiproducts_modules

/-- **The bicone exhibiting `𝒢^{⊞ n}` as the biproduct of `n` copies of `𝒢`**, on the explicit
inclusions and projections of `AlgebraicGeometry.Scheme.Modules.biprodPowIncl` and
`AlgebraicGeometry.Scheme.Modules.biprodPowProj`. Its one field is
`AlgebraicGeometry.Scheme.Modules.biprodPowIncl_proj`; the family being constant, the `eqToHom` of
`CategoryTheory.Limits.Bicone` is an identity. -/
noncomputable def Scheme.Modules.biprodPowBicone (G : X.Modules) (n : ℕ) :
    Bicone (fun _ : Fin n => G) where
  pt := G.biprodPow n
  π := G.biprodPowProj n
  ι := G.biprodPowIncl n
  ι_π j j' := by
    rw [Scheme.Modules.biprodPowIncl_proj]
    by_cases h : j = j'
    · subst h; simp
    · simp [h]

/-- **That bicone is a biproduct**, by the total identity
`AlgebraicGeometry.Scheme.Modules.biprodPow_total`. The docstring of that identity says the
inclusions and projections exhibit `𝒢^{⊞ n}` as the biproduct of `n` copies of `𝒢`; this is that
sentence. -/
noncomputable def Scheme.Modules.biprodPowBiconeIsBilimit (G : X.Modules) (n : ℕ) :
    (G.biprodPowBicone n).IsBilimit :=
  isBilimitOfTotal _ (G.biprodPow_total n)

/-- `𝒢^{⊞ n} ≅ ⨁ⱼ 𝒢`, the comparison with the library's biproduct of the constant family. -/
noncomputable def Scheme.Modules.biprodPowIsoBiproduct (G : X.Modules) (n : ℕ) :
    G.biprodPow n ≅ ⨁ (fun _ : Fin n => G) :=
  biproduct.uniqueUpToIso _ (G.biprodPowBiconeIsBilimit n)

/-- **`𝒢^{⊞ n} ≅ ∐ⱼ 𝒢`**: a power is a finite coproduct of equal summands. This is what makes the
power form of the resolving hypothesis a special case of the heterogeneous form. -/
noncomputable def Scheme.Modules.biprodPowIsoCoproduct (G : X.Modules) (n : ℕ) :
    G.biprodPow n ≅ ∐ (fun _ : Fin n => G) :=
  (G.biprodPowIsoBiproduct n).trans (biproduct.isoCoproduct _)

/-! ### A finite coproduct of members of the family is a resolving module -/

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) {ι : Type v} (T : ι → X.Modules)

/-- **A surjection from a finite coproduct of members of `𝒯` is a resolving module.** If every
member of `𝒯` is coherent with finite-dimensional cohomology in every degree, then a surjection
`∐ⱼ 𝒯(dⱼ) ⟶ 𝒢` exhibits `𝒢` as a quotient of a coherent module whose cohomology is
finite-dimensional in every degree — which is the hypothesis
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_le` takes. The
degrees `dⱼ` need not be equal, which is what clause (1) of [Stacks, Tag 01YS] provides.

Coherence of the coproduct is `AlgebraicGeometry.SheafOfModules.isCoherent_biproduct` transported
along `CategoryTheory.Limits.biproduct.isoCoproduct`, coherent modules being closed under
isomorphism as a weak Serre class ([Stacks, Tag 01BY] (5)); finite dimensionality of its cohomology
is `AlgebraicGeometry.finiteDimensional_cohomologyOverField_coproduct`. There is no hypothesis on
`f`. -/
theorem exists_isCoherent_and_forall_finiteDimensional_and_epi_of_epi_coproduct
    (hTcoh : ∀ a : ι, SheafOfModules.IsCoherent (T a))
    (hTfin : ∀ (a : ι) (n : ℕ), FiniteDimensional k (cohomologyOverField k f (T a) n))
    (G : X.Modules)
    (hG : ∃ (r : ℕ) (d : Fin r → ι), ∃ φ : (∐ fun j => T (d j)) ⟶ G, Epi φ) :
    ∃ E : X.Modules, SheafOfModules.IsCoherent E ∧
      (∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f E n)) ∧ ∃ φ : E ⟶ G, Epi φ := by
  obtain ⟨r, d, φ, hφ⟩ := hG
  refine ⟨∐ fun j => T (d j), ?_, ?_, φ, hφ⟩
  · have hb := SheafOfModules.isCoherent_biproduct (fun j => T (d j)) fun j => hTcoh (d j)
    let P : ObjectProperty X.Modules := fun M => SheafOfModules.IsCoherent M
    let _ : P.IsWeakSerreClass := _root_.SheafOfModules.coherentModules_isWeakSerreClass
    exact P.prop_of_iso (biproduct.isoCoproduct (fun j => T (d j))) hb
  · exact fun n => finiteDimensional_cohomologyOverField_coproduct k f
      (fun j => T (d j)) n fun j => hTfin (d j) n

/-- Every coherent module admits a coherent cover with finite-dimensional cohomology. -/
private theorem exists_resolving_of_epi_coproduct
    (hTcoh : ∀ a : ι, SheafOfModules.IsCoherent (T a))
    (hTfin : ∀ (a : ι) (n : ℕ), FiniteDimensional k (cohomologyOverField k f (T a) n))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ (r : ℕ) (d : Fin r → ι), ∃ φ : (∐ fun j => T (d j)) ⟶ G, Epi φ)
    (G : X.Modules) (hG : SheafOfModules.IsCoherent G) :
    ∃ E : X.Modules, SheafOfModules.IsCoherent E ∧
      (∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f E n)) ∧ ∃ φ : E ⟶ G, Epi φ :=
  exists_isCoherent_and_forall_finiteDimensional_and_epi_of_epi_coproduct
    k f T hTcoh hTfin G (hgen G hG)

/-! ### The descending induction on a family of twists of varying degree -/

/-- **The descending induction of [Stacks, Tag 02O6] run on clause (1) of [Stacks, Tag 01YS]**,
with the vanishing degree as a hypothesis. Suppose the cohomology of every coherent module is
finite-dimensional in all degrees `≥ N`, every member of `𝒯` is coherent with finite-dimensional
cohomology in every degree, and every coherent module is a quotient of a finite coproduct of
members of `𝒯`. Then the cohomology of every coherent module is finite-dimensional in every
degree.

There is no hypothesis on `f`: properness enters only through `N`, which is discharged in
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_coproduct`. -/
theorem forall_finiteDimensional_cohomologyOverField_of_epi_coproduct_of_le (N : ℕ)
    (hN : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, N ≤ n → FiniteDimensional k (cohomologyOverField k f G n))
    (hTcoh : ∀ a : ι, SheafOfModules.IsCoherent (T a))
    (hTfin : ∀ (a : ι) (n : ℕ), FiniteDimensional k (cohomologyOverField k f (T a) n))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ (r : ℕ) (d : Fin r → ι), ∃ φ : (∐ fun j => T (d j)) ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f G n) :=
  forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_le k f N hN
    (exists_resolving_of_epi_coproduct k f T hTcoh hTfin hgen)

/-- **[Stacks, Tag 02O6] over a field from clause (1) of [Stacks, Tag 01YS] at the shape the
source states it.** For `X` proper over `k`, if there is a family `𝒯` of coherent modules whose
cohomology is finite-dimensional in every degree and such that every coherent module on `X` is a
quotient of a finite coproduct of members of `𝒯`, then the cohomology of every coherent module on
`X` is finite-dimensional in every degree.

On `ℙⁿ` the family is the twists and the two hypotheses are the Čech computation of
[Stacks, Tag 01XT] and clause (1) of [Stacks, Tag 01YS]. Unlike
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_biprodPow`, the summands of
one surjection are not required to be equal, so what has to be produced on projective space is
clause (1) and not the stronger single-degree [Stacks, Tag 01QB].

The vanishing degree is supplied by
`AlgebraicGeometry.exists_forall_finiteDimensional_cohomologyOverField_of_le_of_isProper`, which
needs only properness, and a coherent module is quasi-coherent by [Stacks, Tag 01BW]. -/
theorem forall_finiteDimensional_cohomologyOverField_of_epi_coproduct [IsProper f]
    (hTcoh : ∀ a : ι, SheafOfModules.IsCoherent (T a))
    (hTfin : ∀ (a : ι) (n : ℕ), FiniteDimensional k (cohomologyOverField k f (T a) n))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ (r : ℕ) (d : Fin r → ι), ∃ φ : (∐ fun j => T (d j)) ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f G n) :=
  forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_isProper k f
    (exists_resolving_of_epi_coproduct k f T hTcoh hTfin hgen)

/-! ### Transport to a closed subscheme -/

section Closed

variable {Z : Scheme.{u}}

/-- **[Stacks, Tag 02O6] over a field for a closed subscheme of a proper scheme carrying a family
of twists of varying degree.** A proper scheme over a field need not be projective, so the family
cannot in general be produced on the scheme one cares about; what the source does is embed it. If
`i : Z ⟶ X` is a closed immersion into a locally Noetherian `X` proper over `k`, and `X` carries a
family in the sense above, then the cohomology of every coherent module on `Z` is
finite-dimensional in every degree, over the structure morphism `g` presented as the composite.

`Spec k` is not terminal in the category of schemes, so the factorisation `i ≫ f = g` is a
hypothesis and not automatic. -/
theorem forall_finiteDimensional_cohomologyOverField_of_isClosedImmersion_of_coproduct
    [IsLocallyNoetherian X] [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (g : Z ⟶ Spec (.of k)) (hg : i ≫ f = g)
    (hTcoh : ∀ a : ι, SheafOfModules.IsCoherent (T a))
    (hTfin : ∀ (a : ι) (n : ℕ), FiniteDimensional k (cohomologyOverField k f (T a) n))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ (r : ℕ) (d : Fin r → ι), ∃ φ : (∐ fun j => T (d j)) ⟶ G, Epi φ) :
    ∀ G : Z.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, FiniteDimensional k (cohomologyOverField k g G n) :=
  forall_finiteDimensional_cohomologyOverField_of_isClosedImmersion_of_exists_epi_of_eq k f i g hg
    (exists_resolving_of_epi_coproduct k f T hTcoh hTfin hgen)

/-- **Base case (1) of the dévissage of [Stacks, Tag 01YH], for a closed subscheme of a proper
scheme carrying a family of twists of varying degree.** `Hⁿ(Z, 𝒪_Z)` is a finite-dimensional
`k`-vector space in every degree.

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
theorem forall_finiteDimensional_cohomologyOverField_unit_of_isClosedImmersion_of_coproduct
    [IsLocallyNoetherian X] [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (g : Z ⟶ Spec (.of k)) (hg : i ≫ f = g)
    (hTcoh : ∀ a : ι, SheafOfModules.IsCoherent (T a))
    (hTfin : ∀ (a : ι) (n : ℕ), FiniteDimensional k (cohomologyOverField k f (T a) n))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ (r : ℕ) (d : Fin r → ι), ∃ φ : (∐ fun j => T (d j)) ⟶ G, Epi φ) :
    ∀ n : ℕ,
      FiniteDimensional k (cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) n) :=
  have : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  forall_finiteDimensional_cohomologyOverField_of_isClosedImmersion_of_coproduct k f T i g hg
    hTcoh hTfin hgen (SheafOfModules.unit Z.ringCatSheaf) inferInstance

end Closed

/-! ### [Stacks, Tag 0BEM] with its Tag 02O6 hypothesis discharged -/

section Euler

variable {m : ℕ}

/-- **[Stacks, Tag 0BEM] from clause (1) of [Stacks, Tag 01YS].** The Euler characteristics of the
twists `ℱ ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_m^{⊗ n_m}` of a coherent sheaf on a scheme proper over a field are
the values of a rational polynomial which is zero or of total degree at most `dim Supp ℱ`, provided
the scheme carries a family in the sense of
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_coproduct`.

`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_finiteDimensional_cohomology` carries
[Stacks, Tag 02O6] as its one remaining hypothesis; this discharges it. The two families are
independent: `𝓛` is the tuple of invertible modules the tag twists by, and `𝒯` is the family that
resolves coherent modules. -/
theorem exists_eulerPolynomial_twistedSheaf_of_epi_coproduct [IsProper f]
    (L : Fin m → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
    (hTcoh : ∀ a : ι, SheafOfModules.IsCoherent (T a))
    (hTfin : ∀ (a : ι) (n : ℕ), FiniteDimensional k (cohomologyOverField k f (T a) n))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ (r : ℕ) (d : Fin r → ι), ∃ φ : (∐ fun j => T (d j)) ⟶ G, Epi φ)
    (F : X.Modules) (hF : SheafOfModules.IsCoherent F) :
    ∃ P : MvPolynomial (Fin m) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤
        topologicalKrullDim (_root_.SheafOfModules.supp F)) ∧
      ∀ n : Fin m → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
        = (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
            (@twistedSheaf_isCoherent X m F L _ hF n) : ℚ) :=
  exists_eulerPolynomial_twistedSheaf_of_finiteDimensional_cohomology k f L
    (forall_finiteDimensional_cohomologyOverField_of_epi_coproduct k f T hTcoh hTfin hgen) F hF

end Euler

/-! ### The power form is a special case -/

/-- **The power form of the resolving hypothesis implies the heterogeneous form.** A surjection
from `(𝒯 a)^{⊞ r}` is a surjection from `∐ⱼ 𝒯(dⱼ)` with every `dⱼ = a`, by
`AlgebraicGeometry.Scheme.Modules.biprodPowIsoCoproduct`.

So the hypothesis `hgen` of every theorem above is implied by the hypothesis `hgen` of the
corresponding theorem of
`StacksFrontier/AlgebraicGeometry/CohomologyFinitenessTwists/Basic.lean`, and the theorems above
are therefore at least as strong. Nothing that could be fed to the power form is lost by stating
the reduction at the heterogeneous shape. -/
theorem exists_epi_coproduct_of_epi_biprodPow (S : X.Modules) (r : ℕ) (a : ι)
    (h : ∃ φ : (T a).biprodPow r ⟶ S, Epi φ) :
    ∃ (s : ℕ) (d : Fin s → ι), ∃ φ : (∐ fun j => T (d j)) ⟶ S, Epi φ := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨r, fun _ => a, ((T a).biprodPowIsoCoproduct r).inv ≫ φ, epi_comp _ _⟩

/-! ### The hypotheses are jointly satisfiable -/

/-- **The three hypotheses of
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_coproduct` are jointly
satisfiable**, on every `X` whose coherent cohomology over `k` is finite-dimensional in every
degree. The witnessing family is the family of *all* coherent modules, and the surjection onto `𝒢`
is the single-summand coproduct `∐_{j : Fin 1} 𝒢 ⟶ 𝒢`, which is a split epimorphism.

This is a check that no axiom check provides: a hypothesis set can be free of `sorry` and of
nonstandard axioms and yet be satisfied by nothing at all. It does not discharge the hypotheses on
projective space — there
the family is the twists and the finiteness of their cohomology is [Stacks, Tag 01XT], which is
absent. It establishes that the set is consistent, and that it holds wherever the conclusion
does. -/
theorem exists_coproduct_family_of_forall_finiteDimensional
    (h : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f G n)) :
    ∃ (J : Type (u + 1)) (S : J → X.Modules),
      (∀ a : J, SheafOfModules.IsCoherent (S a)) ∧
      (∀ (a : J) (n : ℕ), FiniteDimensional k (cohomologyOverField k f (S a) n)) ∧
      ∀ G : X.Modules, SheafOfModules.IsCoherent G →
        ∃ (r : ℕ) (d : Fin r → J), ∃ φ : (∐ fun j => S (d j)) ⟶ G, Epi φ := by
  refine ⟨{G : X.Modules // SheafOfModules.IsCoherent G}, Subtype.val, fun a => a.2,
    fun a n => h a.1 a.2 n, fun G hG => ⟨1, fun _ => ⟨G, hG⟩,
      Sigma.desc fun _ => 𝟙 G, ?_⟩⟩
  have : IsSplitEpi (Sigma.desc fun _ : Fin 1 => 𝟙 G) :=
    IsSplitEpi.mk' ⟨Sigma.ι (fun _ : Fin 1 => G) 0, by simp⟩
  infer_instance

end AlgebraicGeometry

end
