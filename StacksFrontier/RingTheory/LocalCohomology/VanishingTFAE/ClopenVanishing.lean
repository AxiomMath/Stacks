module

public import StacksFrontier.RingTheory.LocalCohomology.CechModel
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimensionBounds

/-!
# Local cohomology along a clopen zero locus

Let `I` be a finitely generated ideal of a commutative ring `A` and suppose the zero locus
`V(I) ⊆ Spec A` is **closed and open**. Then the local cohomology `H^i_{V(I)}(M)` vanishes for
every module `M` and every `i > 0`, so the cohomological dimension of `I` is at most zero.

The argument is elementary and replaces the sheaf-theoretic one of the source. A clopen subset of
`Spec A` is the zero locus of a single idempotent `e` (Mathlib's
`PrimeSpectrum.isClopen_iff_zeroLocus`), the local-cohomology functor depends
only on the zero locus, and the Čech model of
`StacksFrontier/RingTheory/LocalCohomology/CechModel.lean` computes `RΓ_{V(e)}(M)` by the two-term
complex `M ⟶ M_e`. For an idempotent `e` the localization map `M ⟶ M_e` is *surjective* —
`m / eⁿ = m / 1`, because `e · (m - e · m) = 0` — so that complex has no cohomology in degree one,
and it has no terms at all above degree one.

## Main results

* `Stacks.LocalCohomology.surjective_mkLinearMap_powers_of_isIdempotentElem` — the localization
  map `M ⟶ M_e` at an idempotent is surjective.
* `Stacks.LocalCohomology.nonempty_localCohomology_iso_extendedCechObject_of_zeroLocus_eq` —
  **the Čech model for any family cutting out the same zero locus.** This is
  `Stacks.LocalCohomology.nonempty_localCohomology_iso_extendedCechObject` with the hypothesis
  `span (range f) = I` relaxed to `V(span (range f)) = V(I)`.
* `Stacks.LocalCohomology.isZero_homology_extendedCechComplex_singleton_of_isIdempotentElem` — the
  Čech complex of a single idempotent has no cohomology in positive degrees.
* `Stacks.LocalCohomology.isZero_localCohomologyModule_of_isClopen_zeroLocus` — **the
  implication (3) ⇒ (1) of Stacks 0DX7 at `d = 0`**, in the strong form that covers condition (2)
  as well: a clopen zero locus forces `H^i_{V(I)}(M) = 0` for every module `M` and every `i > 0`.
* `Stacks.LocalCohomology.isLocalCohomologyBound_zero_of_isClopen_zeroLocus` and
  `Stacks.LocalCohomology.cohomologicalDimension_le_zero_of_isClopen_zeroLocus` — the same,
  packaged through the cohomological dimension of Stacks 0DX8.
* `Stacks.LocalCohomology.isClopen_zeroLocus_span_singleton_of_isIdempotentElem` and
  `Stacks.LocalCohomology.isClopen_zeroLocus_ne_empty_ne_univ_prod` — the hypothesis is satisfied,
  and has instances in which `V(I)` is neither empty nor all of `Spec A`, so the bound is not the
  degenerate one.

## Implementation notes

No Stacks tag attribute is placed here. The statement of Stacks 0DX7 is a three-way equivalence;
the `d = 0` branch of one of its implications is not the covering set of that tag, and the
geometric condition of its third clause in positive degrees — vanishing of sheaf cohomology on
`Spec A ∖ V(I)` — is not reached by this file at all. The branch at `d = -1` is
`StacksFrontier/RingTheory/LocalCohomology/VanishingTFAE/ZeroLocusGeometry.lean`, and the
equivalence of the first two clauses is
`StacksFrontier/RingTheory/LocalCohomology/LongExactSequence/AllModules.lean`.

`Stacks.LocalCohomology.cohomologicalDimension_le_zero_of_zeroLocus_eq_univ` of
`StacksFrontier/RingTheory/LocalCohomology/VanishingTFAE/LocalDimensionBound.lean` is the special
case `V(I) = Spec A` of the bound below: that zero locus is clopen, with idempotent `e = 0`.

`HasDerivedCategory.standard` is pinned as a local instance, as in every file of this development.
That is forced rather than chosen: the model is already baked into the types of
`Stacks.LocalCohomology.localCohomologyModule` and
`Stacks.LocalCohomology.extendedCechObject`, so there is no free-model version of the objects
below to state instead. Nothing here mentions a coproduct or a product of a derived category of
sheaves, which is where the standard model would make a statement vacuous; these objects live in
`D(ModuleCat A)`, of which the standard model is a legitimate derived category.

## References

* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
* [Stacks Project, Tag 0DX8](https://stacks.math.columbia.edu/tag/0DX8)
* [Stacks Project, Tag 0953](https://stacks.math.columbia.edu/tag/0953)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe w v u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-! ### The Čech model for a family with the right zero locus -/

/-- **The Čech model of local cohomology for any family cutting out the same zero locus.** For a
finitely generated ideal `I` and a finite family `f` with `V(f₁, …, f_r) = V(I)`, the object
`RΓ_{V(I)}(M[0])` is the extended alternating Čech complex `C^•(f₁, …, f_r; M)`.

This relaxes the hypothesis of
`Stacks.LocalCohomology.nonempty_localCohomology_iso_extendedCechObject`, where the family has to
generate `I` on the nose. Both the torsion property of the Čech object and the universal property
of its augmentation are statements about the full subcategory of `D(A)` cut out by `I`, and that
subcategory depends only on `V(I)` once `I` is finitely generated (Stacks 0953), which is
`Stacks.LocalCohomology.derivedPowerTorsionProperty_iff_of_zeroLocus_eq`. -/
theorem nonempty_localCohomology_iso_extendedCechObject_of_zeroLocus_eq
    (I : Ideal A) (hI : I.FG) {r : ℕ} (f : Fin r → A)
    (hIf : PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus ((Ideal.span (Set.range f) : Ideal A) : Set A))
    (M : ModuleCat.{max u v} A) :
    Nonempty ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
        ((Dualizing.localCohomologyFunctor A I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) ≅
      extendedCechObject f M) := by
  have hJ : (Ideal.span (Set.range f)).FG := Submodule.fg_span (Set.finite_range f)
  refine nonempty_localCohomology_iso_coreflection I hI
    ((derivedPowerTorsionProperty_iff_of_zeroLocus_eq.{v} I _ hI hJ hIf _).mpr
      (derivedPowerTorsionProperty_extendedCechObject f M _ hJ rfl))
    (extendedCechAugmentationHom f M) fun W hW => ?_
  exact bijective_comp_extendedCechAugmentationHom f M _ hJ rfl W
    ((derivedPowerTorsionProperty_iff_of_zeroLocus_eq.{v} I _ hI hJ hIf W).mp hW)

/-- **The local cohomology modules for any family cutting out the same zero locus.** The degree-`i`
local cohomology of `M` with support in `V(I)` is the degree-`i` cohomology of the extended
alternating Čech complex of any finite family whose zero locus is `V(I)`. -/
theorem nonempty_homology_localCohomology_iso_cechHomology_of_zeroLocus_eq
    (I : Ideal A) (hI : I.FG) {r : ℕ} (f : Fin r → A)
    (hIf : PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus ((Ideal.span (Set.range f) : Ideal A) : Set A))
    (M : ModuleCat.{max u v} A) (i : ℤ) :
    Nonempty (localCohomologyModule A I hI M i ≅ (extendedCechComplex f M).homology i) := by
  obtain ⟨e⟩ := nonempty_localCohomology_iso_extendedCechObject_of_zeroLocus_eq.{v} I hI f hIf M
  exact ⟨(DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A) i).app
      (extendedCechComplex f M)⟩

/-! ### Localizing at an idempotent -/

/-- **The localization map `M ⟶ M_e` at an idempotent is surjective.** Every fraction `m / eⁿ`
equals `m / 1`, because `eⁿ · (eⁿ · m) = eⁿ · m`. -/
theorem surjective_mkLinearMap_powers_of_isIdempotentElem {t : A} (ht : IsIdempotentElem t)
    (M : Type w) [AddCommGroup M] [Module A M] :
    Function.Surjective (LocalizedModule.mkLinearMap (Submonoid.powers t) M) := by
  intro z
  induction z using LocalizedModule.induction_on with
  | h m s =>
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 s.2
    refine ⟨m, LocalizedModule.mk_eq.2 ⟨s, ?_⟩⟩
    have hs : (s : A) = t ^ n := hn.symm
    simp only [Submonoid.smul_def, one_smul, smul_smul, hs]
    rw [(ht.pow n).eq]

/-- The Čech differential out of degree zero, for the one-element family `e`, is surjective when
`e` is idempotent: it is the localization map `M ⟶ M_e` placed in the unique summand. -/
theorem surjective_cechD_zero_singleton_of_isIdempotentElem {t : A} (ht : IsIdempotentElem t)
    (M : Type w) [AddCommGroup M] [Module A M] :
    Function.Surjective (Cech.cechD (fun _ : Fin 1 => t) M 0) := by
  set f : Fin 1 → A := fun _ => t with hf
  have hsub : Cech.cechSub f {0} = Submonoid.powers t := by
    change Submonoid.powers (∏ i ∈ ({0} : Finset (Fin 1)), f i) = Submonoid.powers t
    rw [Finset.prod_singleton]
  have hsurj : Function.Surjective (LocalizedModule.mkLinearMap (Cech.cechSub f {0}) M) := by
    rw [hsub]
    exact surjective_mkLinearMap_powers_of_isIdempotentElem ht M
  have h1 : ∀ s : {s : Finset (Fin 1) // s.card = 1}, s = ⟨{0}, rfl⟩ := by
    intro s
    refine Subtype.ext ?_
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 s.2
    rw [ha, Fin.fin_one_eq_zero a]
  have hatt : (∅ : Finset (Fin 1))ᶜ.attach = {⟨0, by simp⟩} := by
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_attach _ _, fun x _ => ?_⟩
    exact Subtype.ext (Fin.fin_one_eq_zero x.1)
  intro y
  have hy : y = DirectSum.lof A _ _ (⟨{0}, rfl⟩ : {s : Finset (Fin 1) // s.card = 1})
      (y ⟨{0}, rfl⟩) := by
    refine DFinsupp.ext fun j => ?_
    obtain rfl := h1 j
    simp [DirectSum.lof_eq_of, DirectSum.of_eq_same]
  obtain ⟨m, hm⟩ := hsurj (y ⟨{0}, rfl⟩)
  refine ⟨DirectSum.lof A _ _ (⟨∅, rfl⟩ : {s : Finset (Fin 1) // s.card = 0})
    (LocalizedModule.mkLinearMap (Cech.cechSub f ∅) M m), ?_⟩
  rw [Cech.cechD_lof, hatt, Finset.sum_singleton, Cech.cechι_mk,
    show Cech.cechSign (∅ : Finset (Fin 1)) 0 = 1 from by simp [Cech.cechSign], one_smul, hy,
    ← hm]
  rfl

/-- The Čech complex of a single idempotent has no cohomology in degree one: it is the two-term
complex `M ⟶ M_e`, whose differential is surjective. -/
theorem isZero_homology_cechComplex_singleton_one_of_isIdempotentElem {t : A}
    (ht : IsIdempotentElem t) (M : ModuleCat.{max u v} A) :
    IsZero ((Cech.cechComplex (fun _ : Fin 1 => t) M).homology 1) := by
  set f : Fin 1 → A := fun _ => t with hf
  have hX₃ : IsZero ((Cech.cechComplex f M).X 2) :=
    ModuleCat.isZero_iff_subsingleton.2 (subsingleton_cechTerm_of_lt f M (by omega))
  have hd : (Cech.cechComplex f M).d 0 1 = ModuleCat.ofHom (Cech.cechD f M 0) :=
    CochainComplex.of_d (fun p => ModuleCat.of A (Cech.cechTerm f (M : Type (max u v)) p))
      (fun p => ModuleCat.ofHom (Cech.cechD f (M : Type (max u v)) p)) 0
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)]
  refine (ShortComplex.exact_iff_epi _ (hX₃.eq_of_tgt _ _)).2 ?_
  change Epi ((Cech.cechComplex f M).d 0 1)
  rw [hd]
  exact (ModuleCat.epi_iff_surjective _).2
    (surjective_cechD_zero_singleton_of_isIdempotentElem ht M)

/-- **The Čech complex of a single idempotent has no cohomology in positive degrees.** In degree
one the differential out of degree zero is surjective, and above degree one the complex has no
terms. -/
theorem isZero_homology_extendedCechComplex_singleton_of_isIdempotentElem {t : A}
    (ht : IsIdempotentElem t) (M : ModuleCat.{max u v} A) (i : ℤ) (hi : 0 < i) :
    IsZero ((extendedCechComplex (fun _ : Fin 1 => t) M).homology i) := by
  set f : Fin 1 → A := fun _ => t with hf
  rcases eq_or_lt_of_le (show (1 : ℤ) ≤ i by omega) with rfl | hi'
  · exact (isZero_homology_cechComplex_singleton_one_of_isIdempotentElem.{v} ht M).of_iso
      ((Cech.cechComplex f M).extendHomologyIso ComplexShape.embeddingUpNat
        (j := 1) (j' := (1 : ℤ)) (by simp))
  · exact ShortComplex.isZero_homology_of_isZero_X₂ _
      (isZero_extendedCechComplex_X f M i (Or.inr (by push_cast; omega)))

/-! ### A clopen zero locus -/

/-- **A clopen zero locus kills all higher local cohomology.** If `V(I) ⊆ Spec A` is closed and
open then `H^i_{V(I)}(M) = 0` for every `A`-module `M` and every `i > 0`.

This is the implication (3) ⇒ (1) of Stacks 0DX7 at `d = 0`, and in fact its conclusion for every
module at once, which is condition (2) of that tag at `d = 0`. A clopen is the zero locus of an
idempotent `e`, so `V(I) = V(e)`; the Čech model of local cohomology for the one-element family
`e` is the two-term complex `M ⟶ M_e`, and `M ⟶ M_e` is surjective because `e` is idempotent. -/
theorem isZero_localCohomologyModule_of_isClopen_zeroLocus
    (I : Ideal A) (hI : I.FG) (h : IsClopen (PrimeSpectrum.zeroLocus (I : Set A)))
    (M : ModuleCat.{max u v} A) (i : ℤ) (hi : 0 < i) :
    IsZero (localCohomologyModule A I hI M i) := by
  obtain ⟨t, ht, hte⟩ := PrimeSpectrum.isClopen_iff_zeroLocus.1 h
  have hIf : PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus
        ((Ideal.span (Set.range (fun _ : Fin 1 => t)) : Ideal A) : Set A) := by
    rw [PrimeSpectrum.zeroLocus_span, Set.range_const, hte]
  obtain ⟨e⟩ := nonempty_homology_localCohomology_iso_cechHomology_of_zeroLocus_eq.{v}
    I hI (fun _ : Fin 1 => t) hIf M i
  exact (isZero_homology_extendedCechComplex_singleton_of_isIdempotentElem.{v}
    ht M i hi).of_iso e

/-- **Zero is a vanishing bound for a clopen zero locus**, in the sense of Stacks 0DX8. -/
theorem isLocalCohomologyBound_zero_of_isClopen_zeroLocus
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (h : IsClopen (PrimeSpectrum.zeroLocus (I : Set A))) :
    IsLocalCohomologyBound A I hI 0 :=
  ⟨by omega, fun i hi =>
    isZero_localCohomologyModule_of_isClopen_zeroLocus.{u} I hI h (ModuleCat.of A A) i hi⟩

/-- **The cohomological dimension of an ideal with clopen zero locus is at most zero.** This
generalizes `Stacks.LocalCohomology.cohomologicalDimension_le_zero_of_zeroLocus_eq_univ`, whose
hypothesis `V(I) = Spec A` makes `V(I)` clopen with idempotent `e = 0`. -/
theorem cohomologicalDimension_le_zero_of_isClopen_zeroLocus
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (h : IsClopen (PrimeSpectrum.zeroLocus (I : Set A))) :
    cohomologicalDimension A I hI ≤ 0 :=
  cohomologicalDimension_le A I hI 0 (isLocalCohomologyBound_zero_of_isClopen_zeroLocus A I hI h)

/-! ### The hypothesis is satisfied, and not only degenerately -/

/-- **Every idempotent gives an ideal satisfying the hypothesis above.** The repository therefore
constructs witnesses to it, and by `PrimeSpectrum.isClopen_iff_zeroLocus` these are all of them. -/
theorem isClopen_zeroLocus_span_singleton_of_isIdempotentElem {t : A} (ht : IsIdempotentElem t) :
    IsClopen (PrimeSpectrum.zeroLocus ((Ideal.span {t} : Ideal A) : Set A)) := by
  rw [PrimeSpectrum.zeroLocus_span]
  exact PrimeSpectrum.isClopen_iff_zeroLocus.2 ⟨t, ht, rfl⟩

/-- An element of a product ring whose first coordinate is a unit is not nilpotent. -/
theorem not_isNilpotent_one_zero (R S : Type u) [CommRing R] [CommRing S] [Nontrivial R] :
    ¬ IsNilpotent ((1, 0) : R × S) := by
  simpa using fun h => not_isNilpotent_one (h.map (RingHom.fst R S))

/-- An element of a product ring whose second coordinate is a unit is not nilpotent. -/
theorem not_isNilpotent_zero_one (R S : Type u) [CommRing R] [CommRing S] [Nontrivial S] :
    ¬ IsNilpotent ((0, 1) : R × S) := by
  simpa using fun h => not_isNilpotent_one (h.map (RingHom.snd R S))

/-- **The hypothesis of
`Stacks.LocalCohomology.isZero_localCohomologyModule_of_isClopen_zeroLocus` has non-degenerate
instances.** In a product of two nontrivial rings the ideal generated by the idempotent `(1, 0)`
has a zero locus which is clopen and is neither empty nor all of the spectrum, so the bound above
is not merely the two cases `V(I) = ∅` and `V(I) = Spec A` — the second of which is
`Stacks.LocalCohomology.cohomologicalDimension_le_zero_of_zeroLocus_eq_univ`. -/
theorem isClopen_zeroLocus_ne_empty_ne_univ_prod (R S : Type u) [CommRing R] [CommRing S]
    [Nontrivial R] [Nontrivial S] :
    (Ideal.span {((1, 0) : R × S)}).FG ∧
      IsClopen (PrimeSpectrum.zeroLocus
          ((Ideal.span {((1, 0) : R × S)} : Ideal (R × S)) : Set (R × S))) ∧
        PrimeSpectrum.zeroLocus
            ((Ideal.span {((1, 0) : R × S)} : Ideal (R × S)) : Set (R × S)) ≠ ∅ ∧
          PrimeSpectrum.zeroLocus
            ((Ideal.span {((1, 0) : R × S)} : Ideal (R × S)) : Set (R × S)) ≠ Set.univ := by
  have hidem : IsIdempotentElem ((1, 0) : R × S) := by
    refine Prod.ext ?_ ?_ <;> simp
  have hsub : (1 : R × S) - (1, 0) = (0, 1) := by
    refine Prod.ext ?_ ?_ <;> simp
  refine ⟨Submodule.fg_span (Set.finite_singleton _), ?_, ?_, ?_⟩
  · exact isClopen_zeroLocus_span_singleton_of_isIdempotentElem hidem
  · rw [PrimeSpectrum.zeroLocus_span,
      PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem _ hidem, hsub]
    intro hempty
    exact not_isNilpotent_zero_one R S ((PrimeSpectrum.basicOpen_eq_bot_iff _).1
      (TopologicalSpace.Opens.coe_eq_empty.1 hempty))
  · rw [PrimeSpectrum.zeroLocus_span]
    intro huniv
    refine not_isNilpotent_one_zero R S ((PrimeSpectrum.basicOpen_eq_bot_iff
      ((1, 0) : R × S)).1 (TopologicalSpace.Opens.coe_eq_empty.1 ?_))
    rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, huniv, Set.compl_univ]

end Stacks.LocalCohomology

end
