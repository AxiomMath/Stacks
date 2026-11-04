module

public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.EulerCharDirectSum.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EmptySupport

/-!
# [Stacks, Tag 02O6] over a field from a supply of resolving modules

[Stacks, Tag 02O6] over a field says that `Hⁿ(X, ℱ)` is a finite-dimensional `k`-vector space
for `X` proper over `k` and `ℱ` coherent. `CohomologyFinitenessDevissage` reduces it, through
the dévissage of [Stacks, Tag 01YH], to its two base cases — the structure sheaf and the coherent
modules supported in a proper closed subset. This file gives the *other* reduction, the one the
source itself uses to prove clause (3) of [Stacks, Tag 01YS]: a descending induction on the
degree, run on a supply of modules whose cohomology is already known to be finite-dimensional
and which surject onto every coherent module.

**The induction.** For `X` proper over `k` the cohomology of every quasi-coherent module vanishes
above a single degree `N`
(`exists_forall_finiteDimensional_cohomologyOverField_of_le_of_isProper`), so finite dimensionality
holds for free in degrees `≥ N`. Suppose it holds in all degrees `> n` for all coherent modules,
and let `ℱ` be coherent. Choose a coherent `ℰ` with finite-dimensional cohomology and an
epimorphism `ℰ ⟶ ℱ`; its kernel `𝒦` is coherent ([Stacks, Tag 01BY] (3)), and the long exact
sequence of `0 ⟶ 𝒦 ⟶ ℰ ⟶ ℱ ⟶ 0` places `Hⁿ(X, ℱ)` between `Hⁿ(X, ℰ)` and `Hⁿ⁺¹(X, 𝒦)`, both
finite-dimensional. So `Hⁿ(X, ℱ)` is finite-dimensional, and the induction closes. Nothing else is
used: the propagation step is the unconditional
`finiteDimensional_cohomologyOverField_three_of_shortExact`.

**What this buys.** The dévissage route carries three hypotheses — the dévissage of
[Stacks, Tag 01YH] itself, which is not in the library, and the two base cases. This route
carries *one*, and it is the hypothesis the source discharges on projective space by the Čech
computation of [Stacks, Tag 01XT]: there the resolving modules are the finite direct sums of
twists `𝒪(d)`, and the epimorphism is clause "quotient of twists" of [Stacks, Tag 01YS]. **Both
of those are still absent from the library**, so no `@[stacks]` attribute is attached to anything
here; what is removed is the dévissage, not the projective computation.

**And it transports along a closed immersion.** `Hⁿ(Z, 𝒢) ≅ Hⁿ(X, i_* 𝒢)` for a closed immersion
`i : Z ⟶ X` (`cohomologyOverFieldPushforwardIsoOfIsClosedImmersion`) and `i_* 𝒢` is coherent when
`X` is locally Noetherian ([Stacks, Tag 087T]), so the property for all coherent modules on `X`
gives it for all coherent modules on `Z`. Composed with the induction this says: a scheme
admitting a closed immersion into a proper `X` over `k` for which the resolving modules exist
satisfies [Stacks, Tag 02O6] over `k` — in particular both base cases of the dévissage at once,
the structure sheaf included.

## Main results

* `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_le`: the
  descending induction, with the vanishing degree as a hypothesis and no condition on `f`.
* `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_isProper`:
  **[Stacks, Tag 02O6] over a field from the single hypothesis that every coherent module is a
  quotient of a coherent module with finite-dimensional cohomology.**
* `AlgebraicGeometry.finiteDimensional_cohomologyOverField_biprod`, `…_biprodPow`,
  `…_biproduct` and `…_coproduct`: finite dimensionality of the cohomology is closed under
  binary biproducts, finite powers, and finite biproducts and coproducts of arbitrary families,
  so the hypothesis above need only be supplied for the summands.
* `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isClosedImmersion`: the
  property for all coherent modules transports from `X` to a closed subscheme of `X`.
* `…_of_isClosedImmersion_of_exists_epi` and `…_of_eq`: the two composed, the second for a
  structure morphism of `Z` presented as the composite.
* `…_unit_of_isClosedImmersion_of_exists_epi`: **base case (1) of the dévissage** —
  `Hⁿ(Z, 𝒪_Z)` is finite-dimensional — in the shape
  `forall_finiteDimensional_cohomologyOverField_of_devissage` consumes as `hunit`. The elided
  prefix in these two bullets is `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField`.

## Implementation notes

**The induction is on the gap to the vanishing degree, not on the degree.** A descending
induction is formalised as an ordinary induction on `d` of the statement "for every coherent `ℱ`
and every `n` with `N ≤ n + d`, the space `Hⁿ(X, ℱ)` is finite-dimensional"; the degree `n` is
quantified *inside*, which is what lets the step appeal to the inductive hypothesis at `n + 1`.
Quantifying over coherent modules inside the induction is equally essential, because the step
applies the hypothesis to the kernel `𝒦` and not to `ℱ`.

**The hypothesis asks for one module, not a family.** Supplying it for a direct sum of twists is
then a statement about that single sum, and the four biproduct lemmas below reduce it to the
summands — including the heterogeneous finite coproduct `∐ⱼ 𝒪(dⱼ)` that the source actually
uses. The induction behind that one splits off one summand through
`CategoryTheory.Limits.kernelBiproductπIso`, which identifies the biproduct over the complement
of an index with the kernel of the projection at it; Mathlib states no decomposition of a
`Fin (r + 1)`-indexed biproduct into a binary one, and none is needed.

**`HasFiniteBiproducts X.Modules` is not an instance**, although it is one term —
`HasFiniteBiproducts.of_hasFiniteProducts`, the category being abelian. It is supplied here as a
*local* instance, since a new global instance on `X.Modules` changes instance search for every
consumer of this tree. The public statements nonetheless take `[HasBiproduct ℰ]` as a binder
rather than relying on that local instance: with it alone the statement of
`finiteDimensional_cohomologyOverField_biproduct` fails to elaborate — measurably as a
consequence of elaborating the *proof* of the private induction above it, since replacing that
proof by `sorry` makes the statement elaborate, and re-asserting the local instance immediately
before the statement does not. The binder is also the more general statement.

**The hypothesis is not logically weaker than the conclusion, and that is not the point.** Given
the conclusion one supplies the hypothesis with `ℰ = ℱ` and `φ = 𝟙`, so the two are equivalent as
statements. What makes the reduction worth having is that the hypothesis is *suppliable by a
computation* — on projective space, of the cohomology of the twists — whereas the conclusion is
not. Nothing here is a weakening of anything: no tag is attached.

**Coherence of the kernel is an instance.** `SheafOfModules.kernel_isCoherent` is registered for
the root-level coherence predicate, which is the one
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_devissage` uses. Note that
`Stacks.SheafOfModules.IsCoherent` is a *different constant* with the same two fields; the
conversion is `SheafOfModules.isCoherent_iff` and nothing below needs it.

## References

* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### Finite dimensionality is closed under finite biproducts -/

/-- Modules on a scheme have biproducts of finite families: the category is abelian, hence has
finite products, and in a preadditive category a finite product is a biproduct. A theorem made a
*local* instance rather than a global one, for the reason in the implementation notes. -/
theorem hasFiniteBiproducts_modules : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

attribute [local instance] hasFiniteBiproducts_modules

/-- Finite dimensionality of the cohomology passes to a binary biproduct: `Hᵐ(X, 𝒜 ⊞ ℬ)` is the
product of `Hᵐ(X, 𝒜)` and `Hᵐ(X, ℬ)` as a `k`-vector space, by
`AlgebraicGeometry.nonempty_cohomologyOverField_biprod_linearEquiv`, which holds with no
hypothesis on `f` or on the modules. -/
theorem finiteDimensional_cohomologyOverField_biprod (A B : X.Modules) (n : ℕ)
    (hA : FiniteDimensional k (cohomologyOverField k f A n))
    (hB : FiniteDimensional k (cohomologyOverField k f B n)) :
    FiniteDimensional k (cohomologyOverField k f (A ⊞ B) n) := by
  obtain ⟨e⟩ := nonempty_cohomologyOverField_biprod_linearEquiv k f A B n
  have := hA
  have := hB
  exact Module.Finite.equiv e.symm

/-- Finite dimensionality of the cohomology passes to a finite power `𝒢^{⊞ r}`, whose cohomology
is `Fin r → Hᵐ(X, 𝒢)`. -/
theorem finiteDimensional_cohomologyOverField_biprodPow (G : X.Modules) (r n : ℕ)
    (h : FiniteDimensional k (cohomologyOverField k f G n)) :
    FiniteDimensional k (cohomologyOverField k f (G.biprodPow r) n) := by
  obtain ⟨e⟩ := nonempty_cohomologyOverField_biprodPow_linearEquiv k f G n r
  have := h
  exact Module.Finite.equiv e.symm

/-- The kernel sequence of an epimorphism is short exact. -/
private theorem shortExact_kernelSequence_of_epi {C : Type*} [Category C] [Abelian C] {A B : C}
    (φ : A ⟶ B) [Epi φ] : (ShortComplex.kernelSequence φ).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact φ) inferInstance
    (inferInstanceAs (Epi φ))

/-- The induction behind `finiteDimensional_cohomologyOverField_biproduct`, on the number of
summands. Splitting off one summand `ℰ i` leaves the biproduct over the complement of `i`, which
is the kernel of the projection `biproduct.π ℰ i` by
`CategoryTheory.Limits.kernelBiproductπIso`. -/
private theorem finiteDimensional_cohomologyOverField_biproduct_aux (n : ℕ) :
    ∀ (N : ℕ) {J : Type} [Fintype J] (E : J → X.Modules), Fintype.card J = N →
      (∀ j, FiniteDimensional k (cohomologyOverField k f (E j) n)) →
      FiniteDimensional k (cohomologyOverField k f (⨁ E) n) := by
  classical
  intro N
  induction N with
  | zero =>
    intro J _ E hcard _
    have : IsEmpty J := Fintype.card_eq_zero_iff.mp hcard
    have hz : IsZero (⨁ E) := by
      rw [IsZero.iff_id_eq_zero]
      exact biproduct.hom_ext _ _ fun j => isEmptyElim j
    exact finiteDimensional_of_isZero k (isZero_cohomologyOverField_of_isZero k f hz n)
  | succ N ih =>
    intro J _ E hcard h
    obtain ⟨i⟩ : Nonempty J := Fintype.card_pos_iff.mp (by omega)
    have hcard' : Fintype.card {j // j ≠ i} = N := by
      rw [Fintype.card_subtype_compl (p := fun j => j = i), Fintype.card_subtype_eq, hcard]
      omega
    have : IsSplitEpi (biproduct.π E i) := IsSplitEpi.mk' ⟨biproduct.ι E i, by simp⟩
    have hrest := ih (Subtype.restrict (fun j => j ≠ i) E) hcard' fun j => h j.1
    refine finiteDimensional_cohomologyOverField_of_shortExact k f
      (shortExact_kernelSequence_of_epi (biproduct.π E i)) n ?_ (h i)
    exact Module.Finite.equiv
      (cohomologyOverFieldIso k f (kernelBiproductπIso E i) n).toLinearEquiv.symm

/-- **Finite dimensionality of the cohomology passes to a finite biproduct.** The degree is
fixed: splitting off one summand gives a short exact sequence with the summand and the remaining
biproduct in the outer positions and the whole biproduct in the middle, and the middle position
is the one that needs no degree shift. -/
theorem finiteDimensional_cohomologyOverField_biproduct {J : Type} [Finite J]
    (E : J → X.Modules) [HasBiproduct E] (n : ℕ)
    (h : ∀ j, FiniteDimensional k (cohomologyOverField k f (E j) n)) :
    FiniteDimensional k (cohomologyOverField k f (⨁ E) n) := by
  let _ := Fintype.ofFinite J
  exact finiteDimensional_cohomologyOverField_biproduct_aux k f n _ E rfl h

/-- **Finite dimensionality of the cohomology passes to a finite coproduct**, which in an
additive category is the biproduct. This is the shape in which the "quotient of twists" clause of
[Stacks, Tag 01YS] produces the resolving module: a finite coproduct `∐ⱼ 𝒪(dⱼ)`. -/
theorem finiteDimensional_cohomologyOverField_coproduct {J : Type} [Finite J]
    (E : J → X.Modules) [HasBiproduct E] (n : ℕ)
    (h : ∀ j, FiniteDimensional k (cohomologyOverField k f (E j) n)) :
    FiniteDimensional k (cohomologyOverField k f (∐ E) n) :=
  have := finiteDimensional_cohomologyOverField_biproduct k f E n h
  Module.Finite.equiv
    (cohomologyOverFieldIso k f (biproduct.isoCoproduct E) n).toLinearEquiv

/-! ### The descending induction -/

/-- **[Stacks, Tag 02O6] over a field by descending induction on the degree.** Suppose the
cohomology of every coherent module on `X` is finite-dimensional in all degrees `≥ N`, and that
every coherent module is the target of an epimorphism from a coherent module whose cohomology is
finite-dimensional in *every* degree. Then the cohomology of every coherent module is
finite-dimensional in every degree.

There is no hypothesis on `f`: properness enters only through the vanishing degree `N`, which is
why it is taken as a hypothesis here and discharged in
`forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_isProper`. -/
theorem forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_le (N : ℕ)
    (hN : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, N ≤ n → FiniteDimensional k (cohomologyOverField k f G n))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ E : X.Modules, SheafOfModules.IsCoherent E ∧
        (∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f E n)) ∧
        ∃ φ : E ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f G n) := by
  -- the descending induction, on the gap `d` between the degree and the vanishing bound
  have key : ∀ d : ℕ, ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, N ≤ n + d → FiniteDimensional k (cohomologyOverField k f G n) := by
    intro d
    induction d with
    | zero => exact fun G hG n hn => hN G hG n (by omega)
    | succ d ih =>
      intro G hG n hn
      by_cases hnd : N ≤ n + d
      · exact ih G hG n hnd
      obtain ⟨E, hE, hEfin, φ, hφ⟩ := hgen G hG
      have := hE
      have := hG
      have := hφ
      have hker : SheafOfModules.IsCoherent (kernel φ) :=
        SheafOfModules.kernel_isCoherent φ
      exact finiteDimensional_cohomologyOverField_three_of_shortExact k f
        (shortExact_kernelSequence_of_epi φ) n (hEfin n)
        (ih (kernel φ) hker (n + 1) (by omega))
  exact fun G hG n => key N G hG n (by omega)

/-- **[Stacks, Tag 02O6] over a field from a supply of resolving modules.** For `X` proper over
`k`, if every coherent module on `X` is a quotient of a coherent module whose cohomology is
finite-dimensional in every degree, then the cohomology of every coherent module on `X` is
finite-dimensional in every degree.

The vanishing degree is supplied by
`exists_forall_finiteDimensional_cohomologyOverField_of_le_of_isProper`, and a coherent module is
quasi-coherent by [Stacks, Tag 01BW].

No `@[stacks 02O6]` attribute is attached: the hypothesis is the content of the Čech computation
of [Stacks, Tag 01XT] together with the "quotient of twists" clause of [Stacks, Tag 01YS], and
neither is in the library. -/
theorem forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_isProper [IsProper f]
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ E : X.Modules, SheafOfModules.IsCoherent E ∧
        (∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f E n)) ∧
        ∃ φ : E ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f G n) := by
  obtain ⟨N, hN⟩ := exists_forall_finiteDimensional_cohomologyOverField_of_le_of_isProper k f
  refine forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_le k f N
    (fun G hG n hn => hN G ?_ n hn) hgen
  have := hG
  exact isQuasicoherent_of_isCoherent G

/-! ### Transport to a closed subscheme -/

variable {Z : Scheme.{u}}

/-- **Finite dimensionality of the cohomology of every coherent module transports to a closed
subscheme.** If `i : Z ⟶ X` is a closed immersion into a locally Noetherian `X` and the
cohomology over `k` of every coherent module on `X` is finite-dimensional, then so is that of
every coherent module on `Z`, taken over the composite structure morphism `i ≫ f`.

The direct image `i_* 𝒢` is coherent by [Stacks, Tag 087T] and `Hⁿ(Z, 𝒢) ≅ Hⁿ(X, i_* 𝒢)` as
`k`-vector spaces by `cohomologyOverFieldPushforwardIsoOfIsClosedImmersion`. -/
theorem forall_finiteDimensional_cohomologyOverField_of_isClosedImmersion
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i]
    (h : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f G n)) :
    ∀ G : Z.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, FiniteDimensional k (cohomologyOverField k (i ≫ f) G n) := by
  intro G hG n
  have := hG
  have hpush := h ((Scheme.Modules.pushforward i).obj G)
    (isCoherent_pushforward_of_isClosedImmersion i G) n
  exact Module.Finite.equiv
    (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k i f G n).toLinearEquiv.symm

/-- **[Stacks, Tag 02O6] over a field for a closed subscheme of a proper scheme with a supply of
resolving modules.** The descending induction on `X` composed with the transport along the closed
immersion `i : Z ⟶ X`. -/
theorem forall_finiteDimensional_cohomologyOverField_of_isClosedImmersion_of_exists_epi
    [IsLocallyNoetherian X] [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ E : X.Modules, SheafOfModules.IsCoherent E ∧
        (∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f E n)) ∧
        ∃ φ : E ⟶ G, Epi φ) :
    ∀ G : Z.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, FiniteDimensional k (cohomologyOverField k (i ≫ f) G n) :=
  forall_finiteDimensional_cohomologyOverField_of_isClosedImmersion k f i
    (forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_isProper k f hgen)

/-- The same for a structure morphism `g : Z ⟶ Spec k` presented as the composite of the closed
immersion with the structure morphism of `X`. `Spec k` is not terminal in the category of
schemes, so the factorisation is a hypothesis and not automatic. -/
theorem forall_finiteDimensional_cohomologyOverField_of_isClosedImmersion_of_exists_epi_of_eq
    [IsLocallyNoetherian X] [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (g : Z ⟶ Spec (.of k)) (hg : i ≫ f = g)
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ E : X.Modules, SheafOfModules.IsCoherent E ∧
        (∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f E n)) ∧
        ∃ φ : E ⟶ G, Epi φ) :
    ∀ G : Z.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, FiniteDimensional k (cohomologyOverField k g G n) := by
  subst hg
  exact forall_finiteDimensional_cohomologyOverField_of_isClosedImmersion_of_exists_epi k f i hgen

/-- **Base case (1) of the [Stacks, Tag 01YH] dévissage, for a closed subscheme of a proper
scheme with a supply of resolving modules.** `Hⁿ(Z, 𝒪_Z)` is a finite-dimensional `k`-vector
space in every degree.

This is the hypothesis `hunit` of
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_devissage` verbatim, so it can
be fed to it directly; the same theorem one step earlier supplies that dévissage's `hclosed` as
well, and indeed makes the dévissage unnecessary.

Coherence of `𝒪_Z` is **not** a hypothesis. `Z` is locally Noetherian by
`AlgebraicGeometry.isLocallyNoetherian_of_isClosedImmersion`, which this file already imports,
and the structure sheaf of a locally Noetherian scheme is coherent by [Stacks, Tag 01XZ],
`Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent`, which is registered as
an instance. The local Noetherianness of `Z` is applied by name because its own theorem is
deliberately not an instance: its source is determined only by the morphism `i`, so registering
it would make instance search guess a closed immersion. -/
theorem forall_finiteDimensional_cohomologyOverField_unit_of_isClosedImmersion_of_exists_epi
    [IsLocallyNoetherian X] [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (g : Z ⟶ Spec (.of k)) (hg : i ≫ f = g)
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ E : X.Modules, SheafOfModules.IsCoherent E ∧
        (∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f E n)) ∧
        ∃ φ : E ⟶ G, Epi φ) :
    ∀ n : ℕ,
      FiniteDimensional k (cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) n) :=
  have : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  forall_finiteDimensional_cohomologyOverField_of_isClosedImmersion_of_exists_epi_of_eq k f i g hg
    hgen _ inferInstance

end AlgebraicGeometry

end
