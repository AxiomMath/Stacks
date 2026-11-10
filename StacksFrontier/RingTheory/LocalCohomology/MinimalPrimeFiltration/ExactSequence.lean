module

public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.MinimalPrimeComparison
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.NonminimalPrimesColimit

/-!
# The exact sequence of the minimal-prime filtration of local cohomology

Let `A` be a Noetherian ring, let `T ⊆ Spec(A)` be stable under specialization and let
`T' ⊆ T` be the set of primes of `T` that are not minimal in `T`. For every `A`-module `M` there
is an exact sequence
$$ 0 \to \operatorname*{colim}_{Z, f} H^1_f(H^{i-1}_Z(M)) \to H^i_{T'}(M) \to H^i_T(M) \to
   \bigoplus_{\mathfrak p \in T \setminus T'} H^i_{\mathfrak p A_{\mathfrak p}}(M_{\mathfrak p}) $$
where the colimit is over the closed subsets `Z ⊆ T` and the elements `f ∈ A` with
`V(f) ∩ Z ⊆ T'`. This is Tag 0EF8, whose other assertion — that `T'` is again stable under
specialization — is
`PrimeSpectrum.stableUnderSpecialization_nonminimalPrimes` in
`StacksFrontier/RingTheory/Spectrum/Prime/NonminimalPrimes.lean`.

## Main definitions

* `Stacks.LocalCohomology.localTermSum` — the direct sum on the right of the sequence.
* `Stacks.LocalCohomology.localTermSumMap` — the right-hand map of the sequence.
* `Stacks.LocalCohomology.ExactSequenceData` — the sequence together with all its maps and the
  identifications that pin them down.
* `Stacks.LocalCohomology.exactSequenceData` — that data, constructed from the two families of
  identifications it rests on.

## Main results

* `Stacks.LocalCohomology.nonempty_exactSequenceData` — the sequence exists.
* `Stacks.LocalCohomology.localTermSumMap_eq_zero_iff` — exactness at `Hⁱ_T(M)`.
* `Stacks.LocalCohomology.finite_minimalPrimes_nonzero_localization` — a class in `Hⁱ_T(K)` has
  nonzero localization at only finitely many primes minimal in `T`, which is what makes the
  right-hand map land in the direct sum.

## Implementation notes

All the maps of the sequence are canonical, and `ExactSequenceData` records them together with
the data that identifies them, so that the existence statement cannot be satisfied by an
unrelated sequence.

* The colimit term is the colimit of a diagram over the admissible pairs `(Z, f)` whose value at
  a pair is the iterated group `H¹_f(Hⁱ⁻¹_Z(M))` (field `stage`), embedded by `edge` into
  `Hⁱ_{Z ∩ V(f)}(M)` as the kernel of the widening map to `Hⁱ_Z(M)` (fields `edge_injective`
  and `edge_range`); `edge_naturality` says the transition maps of the diagram are the widening
  maps of the cuts, and `left_stage` says the map out of the colimit is the widening map into
  `Hⁱ_{T'}(M)`.
* The middle map is the widening map `changeOfSupport`.
* The right-hand map is localization at each prime minimal in `T` followed by the identification
  of that localization with local cohomology over `A_𝔭` (fields `comparison` and
  `right_component`).

Only the identifications `stage` and `comparison` are produced by existence statements rather
than named constructions — see
`StacksFrontier/RingTheory/LocalCohomology/MinimalPrimeFiltration/PrincipalCutFirstCohomology.lean`
and `StacksFrontier/RingTheory/LocalCohomology/MinimalPrimeFiltration/MinimalPrimeComparison.lean` —
which is why the whole package is an existence
statement. Everything else is a construction: `exactSequenceData` takes those two families as
arguments and builds the data, so a client that has them in hand gets the actual maps rather
than a chosen witness, and `nonempty_exactSequenceData` is that construction fed by choice.

## References

* [Stacks Project, Tag 0EF8](https://stacks.math.columbia.edu/tag/0EF8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- The primes of `T` that are minimal in `T`: the index set of the direct sum on the right of
the sequence of Tag 0EF8. -/
abbrev MinimalSupportPrimes (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A)) :=
  {p : PrimeSpectrum A // p ∈ T \ PrimeSpectrum.nonminimalPrimes T}

/-- Local cohomology of the localized module at a prime minimal in `T`, regarded as an
`A`-module by restriction of scalars. -/
def localTerm (A : Type u) [CommRing A] [IsNoetherianRing A] (T : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u v} A) (i : ℤ) (p : MinimalSupportPrimes A T) : ModuleCat.{max u v} A :=
  (ModuleCat.restrictScalars (algebraMap A (Localization p.val.asIdeal.primeCompl))).obj
    ((localCohomologyModuleFunctor (Localization p.val.asIdeal.primeCompl) i).obj
      (M.localizedModule p.val.asIdeal.primeCompl))

/-- The direct sum `⨁_{𝔭 ∈ T ∖ T'} Hⁱ_{𝔭A_𝔭}(M_𝔭)` on the right of the sequence of Tag 0EF8. -/
def localTermSum (A : Type u) [CommRing A] [IsNoetherianRing A] (T : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u v} A) (i : ℤ) : ModuleCat.{max u v} A :=
  ModuleCat.of A (⨁ p : MinimalSupportPrimes A T, localTerm.{u, v} A T M i p)

/-- **A local cohomology class has nonzero localization at only finitely many primes minimal in
its support.** This is what makes the right-hand map of Tag 0EF8 land in the direct sum. -/
theorem finite_minimalPrimes_nonzero_localization (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    (x : localCohomologyWithSupportIn.{u, v} A T K i) :
    {p : PrimeSpectrum A | p ∈ T \ PrimeSpectrum.nonminimalPrimes T ∧
      (ModuleCat.localizedModuleMkLinearMap
        (localCohomologyWithSupportIn.{u, v} A T K i) p.asIdeal.primeCompl) x ≠ 0}.Finite := by
  obtain ⟨J, y, rfl⟩ := exists_closedSupport_representative.{u, v} A T hT K i x
  refine (finite_minimalSupportPrimes_in_closedSupport T (OrderDual.ofDual J).1
    (OrderDual.ofDual J).2).subset ?_
  rintro p ⟨hpdiff, hne⟩
  refine ⟨hpdiff, ?_⟩
  by_contra hpI
  refine hne ?_
  rw [localizedModuleMk_natural p.asIdeal.primeCompl
      (changeOfSupport A (OrderDual.ofDual J).2 K i) y,
    localCohomology_localizes_zero_outside_support (ClosedSupportIdeal.support A J) K i p hpI y,
    map_zero]

/-- A family of linear maps out of a fixed module, all but finitely many of whose values vanish
at each element, assembles into a map to the direct sum. -/
def linearMapToDirectSum {R : Type*} [CommRing R] {ι : Type*} {X : Type*}
    [AddCommGroup X] [Module R X] {Y : ι → Type*} [∀ i, AddCommGroup (Y i)]
    [∀ i, Module R (Y i)] (f : ∀ i, X →ₗ[R] Y i) (hf : ∀ x, {i | f i x ≠ 0}.Finite) :
    X →ₗ[R] ⨁ i, Y i where
  toFun x :=
    { toFun i := f i x
      support' := Trunc.mk ⟨(hf x).toFinset.val, fun i ↦ by
        classical
        by_cases hi : f i x = 0
        · exact Or.inr hi
        · exact Or.inl ((Set.Finite.mem_toFinset _).mpr hi)⟩ }
  map_add' x y := DFinsupp.ext fun i ↦ (f i).map_add x y
  map_smul' a x := DFinsupp.ext fun i ↦ (f i).map_smul a x

/-- The identifications, at the primes minimal in `T`, of the localization of `Hⁱ_T(M)` with
local cohomology over the corresponding local ring: the data the right-hand map of the sequence
of Tag 0EF8 is built from. -/
abbrev MinimalPrimeComparison (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (M : ModuleCat.{max u v} A) (i : ℤ) :=
  ∀ p : MinimalSupportPrimes A T,
    (localCohomologyWithSupportIn.{u, v} A T
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i).localizedModule
          p.val.asIdeal.primeCompl ≅
      (localCohomologyModuleFunctor (Localization p.val.asIdeal.primeCompl) i).obj
        (M.localizedModule p.val.asIdeal.primeCompl)

/-- The component at a prime minimal in `T` of the right-hand map of Tag 0EF8: localization at
that prime, read through the given identification. -/
def localTermComponent (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (M : ModuleCat.{max u v} A) (i : ℤ)
    (comparison : MinimalPrimeComparison.{u, v} A T M i) (p : MinimalSupportPrimes A T) :
    localCohomologyWithSupportIn.{u, v} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i →ₗ[A]
      localTerm.{u, v} A T M i p where
  toFun x := (comparison p).hom.hom ((ModuleCat.localizedModuleMkLinearMap
    (localCohomologyWithSupportIn.{u, v} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)
    p.val.asIdeal.primeCompl) x)
  map_add' x y := by
    simp only [map_add]
    rfl
  map_smul' a x := by
    change (comparison p).hom.hom ((ModuleCat.localizedModuleMkLinearMap
          (localCohomologyWithSupportIn.{u, v} A T
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)
          p.val.asIdeal.primeCompl) (a • x)) =
      algebraMap A (Localization p.val.asIdeal.primeCompl) a •
        (comparison p).hom.hom ((ModuleCat.localizedModuleMkLinearMap
          (localCohomologyWithSupportIn.{u, v} A T
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)
          p.val.asIdeal.primeCompl) x)
    rw [map_smul, ← IsScalarTower.algebraMap_smul (Localization p.val.asIdeal.primeCompl) a,
      map_smul]

/-- A component of the right-hand map of Tag 0EF8 vanishes exactly when the localization of the
class at that prime does. -/
private theorem localTermComponent_eq_zero_iff (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (M : ModuleCat.{max u v} A) (i : ℤ)
    (comparison : MinimalPrimeComparison.{u, v} A T M i) (p : MinimalSupportPrimes A T)
    (x : localCohomologyWithSupportIn.{u, v} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) :
    localTermComponent.{u, v} A T M i comparison p x = 0 ↔
      (ModuleCat.localizedModuleMkLinearMap
        (localCohomologyWithSupportIn.{u, v} A T
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)
        p.val.asIdeal.primeCompl) x = 0 :=
  ⟨fun h ↦ (ModuleCat.mono_iff_injective (comparison p).hom).mp inferInstance
      (h.trans (map_zero _).symm),
    fun h ↦ (congrArg (comparison p).hom.hom h).trans (map_zero _)⟩

/-- **The components of the right-hand map of Tag 0EF8 vanish away from a finite set.** At each
class of `Hⁱ_T(M)` all but finitely many of the components are zero, which is what makes the
right-hand map land in the direct sum. -/
theorem finite_localTermComponent_ne_zero (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : ModuleCat.{max u v} A) (i : ℤ) (comparison : MinimalPrimeComparison.{u, v} A T M i)
    (x : localCohomologyWithSupportIn.{u, v} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) :
    {p | localTermComponent.{u, v} A T M i comparison p x ≠ 0}.Finite := by
  refine ((finite_minimalPrimes_nonzero_localization.{u, v} A T hT
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i x).preimage
    Subtype.val_injective.injOn).subset fun p hp ↦
      ⟨p.property, fun hz ↦ hp ((localTermComponent_eq_zero_iff ..).2 hz)⟩

/-- **The right-hand map of the sequence of Tag 0EF8**: the componentwise localization map
`Hⁱ_T(M) ⟶ ⨁_{𝔭 ∈ T ∖ T'} Hⁱ_{𝔭A_𝔭}(M_𝔭)`, built from the identifications of the localizations
of `Hⁱ_T(M)` at the primes minimal in `T` with local cohomology over the corresponding local
rings. -/
def localTermSumMap (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : ModuleCat.{max u v} A) (i : ℤ) (comparison : MinimalPrimeComparison.{u, v} A T M i) :
    localCohomologyWithSupportIn.{u, v} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i ⟶
      localTermSum.{u, v} A T M i :=
  ModuleCat.ofHom (linearMapToDirectSum (localTermComponent.{u, v} A T M i comparison)
    (finite_localTermComponent_ne_zero.{u, v} A T hT M i comparison))

/-- The component of the right-hand map of Tag 0EF8 at a prime minimal in `T` is localization at
that prime, read through the given identification. -/
theorem localTermSumMap_component (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : ModuleCat.{max u v} A) (i : ℤ) (comparison : MinimalPrimeComparison.{u, v} A T M i)
    (p : MinimalSupportPrimes A T)
    (x : localCohomologyWithSupportIn.{u, v} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) :
    DirectSum.component A (MinimalSupportPrimes A T) (fun q ↦ localTerm.{u, v} A T M i q) p
        ((localTermSumMap.{u, v} A T hT M i comparison).hom x) =
      (comparison p).hom.hom ((ModuleCat.localizedModuleMkLinearMap
        (localCohomologyWithSupportIn.{u, v} A T
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)
        p.val.asIdeal.primeCompl) x) :=
  rfl

/-- **Exactness at `Hⁱ_T(M)`.** The kernel of the right-hand map of Tag 0EF8 is the image of the
widening map `Hⁱ_{T'}(M) ⟶ Hⁱ_T(M)`. -/
theorem localTermSumMap_eq_zero_iff (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : ModuleCat.{max u v} A) (i : ℤ) (comparison : MinimalPrimeComparison.{u, v} A T M i)
    (x : localCohomologyWithSupportIn.{u, v} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) :
    (localTermSumMap.{u, v} A T hT M i comparison).hom x = 0 ↔
      ∃ y, (changeOfSupport A (PrimeSpectrum.nonminimalPrimes_subset T)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i).hom y = x := by
  classical
  rw [range_changeOfSupport_eq_localizationKernel.{u, v} A T hT
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i x]
  constructor
  · exact fun hx p hp ↦ (localTermComponent_eq_zero_iff A T M i comparison ⟨p, hp⟩ x).1
      (DFinsupp.ext_iff.1 hx ⟨p, hp⟩)
  · exact fun hx ↦ DFinsupp.ext fun p ↦
      (localTermComponent_eq_zero_iff ..).2 (hx p.val p.property)

/-- **The exact sequence of Tag 0EF8**, with all its maps and the identifications that pin them
down. See the implementation notes of this file for what each field says. -/
structure ExactSequenceData (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (M : ModuleCat.{max u v} A) (i : ℤ) where
  /-- The diagram over the admissible pairs whose colimit is the left-hand term. -/
  diagram : FirstIndex A T ⥤ ModuleCat.{max u v} A
  /-- Its value at a pair `(Z, f)` is the iterated group `H¹_f(Hⁱ⁻¹_Z(M))`. -/
  stage : ∀ j, diagram.obj j ≅ firstStage.{u, v} A T M i j
  /-- Each stage embeds into the local cohomology of the cut `Z ∩ V(f)`. -/
  edge : ∀ j, diagram.obj j ⟶ localCohomologyWithSupportIn.{u, v} A (principalCut j)
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i
  /-- That embedding is injective. -/
  edge_injective : ∀ j, Function.Injective (edge j).hom
  /-- Its image is the kernel of the widening map to the local cohomology of `Z`. -/
  edge_range : ∀ j y, ((changeOfSupport A Set.inter_subset_left
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i).hom y = 0 ↔
    ∃ z, (edge j).hom z = y)
  /-- The transition maps of the diagram are the widening maps of the cuts. -/
  edge_naturality : ∀ {j k : FirstIndex A T} (h : j ≤ k) (z : diagram.obj j),
    (changeOfSupport A h.2
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i).hom
        ((edge j).hom z) =
      (edge k).hom ((diagram.map (homOfLE h)).hom z)
  /-- The left-hand map of the sequence. -/
  left : colimit diagram ⟶ localCohomologyWithSupportIn.{u, v} A
    (PrimeSpectrum.nonminimalPrimes T)
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i
  /-- On the class coming from a pair it is the widening map into `Hⁱ_{T'}(M)`. -/
  left_stage : ∀ j z, left.hom ((colimit.ι diagram j).hom z) =
    (changeOfSupport A j.admissible
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i).hom ((edge j).hom z)
  /-- **The leading zero**: the left-hand map is injective. -/
  left_injective : Function.Injective left.hom
  /-- **Exactness at `Hⁱ_{T'}(M)`**: the kernel of the widening map `Hⁱ_{T'}(M) ⟶ Hⁱ_T(M)` is
  the image of the left-hand map. -/
  exact_left : ∀ x, ((changeOfSupport A (PrimeSpectrum.nonminimalPrimes_subset T)
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i).hom x = 0 ↔
    ∃ z, left.hom z = x)
  /-- The identification of the localization of `Hⁱ_T(M)` at a prime minimal in `T` with local
  cohomology over the corresponding local ring. -/
  comparison : ∀ p : MinimalSupportPrimes A T,
    (localCohomologyWithSupportIn.{u, v} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i).localizedModule
        p.val.asIdeal.primeCompl ≅
      (localCohomologyModuleFunctor (Localization p.val.asIdeal.primeCompl) i).obj
        (M.localizedModule p.val.asIdeal.primeCompl)
  /-- The right-hand map of the sequence. -/
  right : localCohomologyWithSupportIn.{u, v} A T
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i ⟶
      localTermSum.{u, v} A T M i
  /-- Its component at a prime minimal in `T` is localization at that prime, read through the
  identification. -/
  right_component : ∀ p x, DirectSum.component A (MinimalSupportPrimes A T)
      (fun q ↦ localTerm.{u, v} A T M i q) p (right.hom x) =
    (comparison p).hom.hom ((ModuleCat.localizedModuleMkLinearMap
      (localCohomologyWithSupportIn.{u, v} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)
      p.val.asIdeal.primeCompl) x)
  /-- **Exactness at `Hⁱ_T(M)`**: the kernel of the right-hand map is the image of the widening
  map `Hⁱ_{T'}(M) ⟶ Hⁱ_T(M)`. -/
  exact_right : ∀ x, (right.hom x = 0 ↔ ∃ y,
    (changeOfSupport A (PrimeSpectrum.nonminimalPrimes_subset T)
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i).hom y = x)

/-- The identifications, at each admissible pair, of the iterated group `H¹_f(Hⁱ⁻¹_Z(M))` with
the kernel of the widening map of the cut: the data the left-hand term of the sequence of
Tag 0EF8 is built from. -/
abbrev FirstStageComparison (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (M : ModuleCat.{max u v} A) (i : ℤ) :=
  ∀ j : FirstIndex A T, firstStage.{u, v} A T M i j ≅
    (kernel (principalCutToAmbient.{u, v} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)).obj j

/-- **The exact sequence of Tag 0EF8, as data.** Given the identifications of the stages with
the kernels of the widening maps of the cuts and of the localizations of `Hⁱ_T(M)` at the primes
minimal in `T` with local cohomology over the corresponding local rings, every map of the
sequence is a named construction: the colimit is the colimit of `kernel (principalCutToAmbient
…)`, the left-hand map is `principalCutKernelColimitMap`, the middle map is `changeOfSupport`
and the right-hand map is `localTermSumMap`. -/
def exactSequenceData (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : ModuleCat.{max u v} A) (i : ℤ)
    (stages : FirstStageComparison.{u, v} A T M i)
    (comparisons : MinimalPrimeComparison.{u, v} A T M i) :
    ExactSequenceData.{u, v} A T M i where
  diagram := kernel (principalCutToAmbient.{u, v} A T
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)
  stage j := (stages j).symm
  edge j := (kernel.ι (principalCutToAmbient.{u, v} A T
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)).app j
  edge_injective j := (ModuleCat.mono_iff_injective
    ((kernel.ι (principalCutToAmbient.{u, v} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)).app j)).mp inferInstance
  edge_range j y := kernel_app_exact.{u, v} (principalCutToAmbient.{u, v} A T
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) j y
  edge_naturality h z := (congrArg (fun ψ => ModuleCat.Hom.hom ψ z)
    ((kernel.ι (principalCutToAmbient.{u, v} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)).naturality
        (homOfLE h))).symm
  left := principalCutKernelColimitMap.{u, v} A T
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i
  left_stage j z := principalCutKernelColimitMap_ι_apply.{u, v} A T
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i j z
  left_injective := principalCut_kernel_colimit_injective.{u, v} A T hT
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i
  exact_left := principalCut_kernel_colimit_range.{u, v} A T hT
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i
  comparison := comparisons
  right := localTermSumMap.{u, v} A T hT M i comparisons
  right_component := localTermSumMap_component.{u, v} A T hT M i comparisons
  exact_right := localTermSumMap_eq_zero_iff.{u, v} A T hT M i comparisons

/-- **Stacks 0EF8, the exact sequence.** Let `A` be a Noetherian ring, let `T ⊆ Spec(A)` be
stable under specialization and let `T' ⊆ T` be the set of primes of `T` that are not minimal in
`T`. For every `A`-module `M` and every `i` there is an exact sequence
`0 ⟶ colim_{Z,f} H¹_f(Hⁱ⁻¹_Z(M)) ⟶ Hⁱ_{T'}(M) ⟶ Hⁱ_T(M) ⟶ ⨁_{𝔭 ∈ T ∖ T'} Hⁱ_{𝔭A_𝔭}(M_𝔭)`
where the colimit is over the closed subsets `Z ⊆ T` and the `f ∈ A` with `V(f) ∩ Z ⊆ T'`. -/
@[stacks 0EF8 "the exact sequence"]
theorem nonempty_exactSequenceData (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : ModuleCat.{max u v} A) (i : ℤ) :
    Nonempty (ExactSequenceData.{u, v} A T M i) :=
  ⟨exactSequenceData.{u, v} A T hT M i
    (fun j ↦ Classical.choice (nonempty_firstStage_iso_kernel.{u, v} A T M i j))
    (fun p ↦ Classical.choice (nonempty_minimalPrime_localCohomology_iso.{u, v} A T hT p.val
      p.property M i))⟩

end Stacks.LocalCohomology

end
