module

public import StacksFrontier.Algebra.Homology.InjectiveDimension.Criteria
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.RingTheory.Dualizing.DimensionFunctionSpecialization
public import StacksFrontier.RingTheory.Dualizing.NormalizedZeroDimensional
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldShift
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality
public import StacksFrontier.RingTheory.KrullDimension.Defs

/-!
# Finite dimension of a ring with a dualizing complex

A Noetherian ring `A` admitting a dualizing complex `K` has finite Krull dimension. The dimension
function `δ_K` of `K` drops strictly along every non-trivial specialization, so a chain of primes
of length `n` forces `δ_K` to span at least `n` values; it therefore suffices to bound `δ_K`. The
bound comes from the finite injective amplitude `[a, b]` of `K`: at a minimal prime `p` the
cohomology `H^{-δ_K(p)}(K)_p` is non-zero, and at a maximal ideal `m` the group
`Ext^{-δ_K(m)}(A/m, K)` is non-zero, so both values lie in `[-b, -a]`; every other prime is
sandwiched between a minimal prime and a maximal ideal, along which `δ_K` is antitone.

## Main results

* `Dualizing.ringKrullDim_lt_top_of_isDualizingComplex` — a Noetherian ring admitting a dualizing
  complex has finite Krull dimension.
* `Dualizing.exists_height_le_of_isDualizingComplex` — the same bound in the currency the
  consumers want: a natural number bounding the heights of all the primes.

## Implementation notes

Non-vanishing at a minimal prime `p` uses that `A_p` is zero-dimensional, so the normalized
complex `K_p⟦-δ_K(p)⟧` is an injective hull of the residue field in degree zero
([Stacks, Tag 0A7R]); its cohomology in degree zero is non-zero, and localization of cohomology
commutes with localization of the complex. Non-vanishing at a maximal ideal `m` uses that
`RHom_A(A/m, K)` is a shift of the residue field ([Stacks, Tag 0A7L]); the adjunction between
restriction of scalars and derived Hom ([Stacks, Tag 0A70]) turns that shift into a non-zero Ext
group, and the shift is identified with `δ_K(m)` through [Stacks, Tag 0A7Y].

## References

* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80)
* [Stacks Project, Tag 0A7Z](https://stacks.math.columbia.edu/tag/0A7Z)
* [Stacks Project, Tag 0A7R](https://stacks.math.columbia.edu/tag/0A7R)
* [Stacks Project, Tag 0A7L](https://stacks.math.columbia.edu/tag/0A7L)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0A5T](https://stacks.math.columbia.edu/tag/0A5T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StacksDraft.PseudoCoherence TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-! ### From a bounded dimension function to finite Krull dimension -/

/-- A ring whose prime spectrum carries a dimension function with values in a bounded interval
has finite Krull dimension. -/
private theorem ringKrullDim_lt_top_of_bounded_dimensionFunction
    (A : Type*) [CommRing A]
    (δ : TopologicalSpace.DimensionFunction (PrimeSpectrum A)) (N : ℕ)
    (hδ : ∀ p, -(N : ℤ) ≤ δ p ∧ δ p ≤ N) :
    ringKrullDim A < ⊤ := by
  let β := OrderDual (Set.Icc (-(N : ℤ)) (N : ℤ))
  have : Finite (Set.Icc (-(N : ℤ)) (N : ℤ)) := (Set.finite_Icc _ _).to_subtype
  let : Fintype β := Fintype.ofFinite β
  have : Nonempty β := ⟨⟨0, by simp⟩⟩
  have hfd : FiniteDimensionalOrder β :=
    (not_infiniteDimensionalOrder_iff (α := β)).mp fun hInf => by
      obtain ⟨s, hs⟩ := hInf.exists_relSeries_with_length (Fintype.card β)
      exact (LTSeries.length_lt_card s).ne hs
  let f : PrimeSpectrum A → β := fun p => ⟨δ p, hδ p⟩
  have hf : StrictMono f := by
    intro p q hpq
    change δ q < δ p
    exact δ.strictAnti_specializes ((PrimeSpectrum.le_iff_specializes p q).mp hpq.le) hpq.ne
  change Order.krullDim (PrimeSpectrum A) < ⊤
  exact (Order.krullDim_le_of_strictMono f hf).trans_lt
    (lt_top_iff_ne_top.mpr (Order.krullDim_ne_top_of_finiteDimensionalOrder (α := β)))

/-! ### Injective amplitude bounds the degrees of non-vanishing cohomology -/

/-- A complex with injective amplitude in `[a, b]` is bounded below by `a` and above by `b`. -/
private theorem isGE_isLE_of_hasInjectiveAmplitude {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (a b : ℤ)
    (hK : StacksDraft.InjectiveDimension.HasInjectiveAmplitude K a b) :
    K.IsGE a ∧ K.IsLE b := by
  obtain ⟨I, hGE, hLE, hI, ⟨e⟩⟩ := hK
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso e.symm a,
    DerivedCategory.TStructure.t.isLE_of_iso e.symm b⟩

/-- The degrees in which a bounded complex has non-zero cohomology lie between its bounds. -/
private theorem homology_index_bounds {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (a b i : ℤ)
    (hGE : K.IsGE a) (hLE : K.IsLE b)
    (h : Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K)) :
    a ≤ i ∧ i ≤ b := by
  have key : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K) :=
    fun hz => (not_nontrivial_iff_subsingleton.mpr (ModuleCat.isZero_iff_subsingleton.mp hz)) h
  exact ⟨le_of_not_gt fun hia => key (DerivedCategory.isZero_of_isGE K a i hia),
    le_of_not_gt fun hib => key (DerivedCategory.isZero_of_isLE K b i hib)⟩

/-- A degree in which the cohomology of a bounded complex is non-zero after localization at a
prime lies between the bounds of the complex. -/
private theorem localized_homology_index_bounds {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (a b i : ℤ)
    (hGE : K.IsGE a) (hLE : K.IsLE b) (p : PrimeSpectrum A)
    (h : Nontrivial (LocalizedModule p.asIdeal.primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K))) :
    a ≤ i ∧ i ≤ b := by
  apply homology_index_bounds.{u, v} K a b i hGE hLE
  by_contra hn
  have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K) :=
    not_nontrivial_iff_subsingleton.mp hn
  exact (not_nontrivial_iff_subsingleton.mpr inferInstance) h

/-- A complex isomorphic to a shift of a module in degree zero has cohomology only in the degree
recording the shift. -/
private theorem homology_index_eq_of_iso_single_shift {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (M : ModuleCat.{max v u} A) (n i : ℤ)
    (e : K ≅ ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj M)⟦n⟧)
    (h : Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K)) :
    i = -n := by
  let S := (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj M
  have : S.IsGE 0 := inferInstance
  have : S.IsLE 0 := inferInstance
  have : (S⟦n⟧).IsGE (-n) := DerivedCategory.TStructure.t.isGE_shift S 0 n (-n) (by omega)
  have : (S⟦n⟧).IsLE (-n) := DerivedCategory.TStructure.t.isLE_shift S 0 n (-n) (by omega)
  have : K.IsGE (-n) := DerivedCategory.TStructure.t.isGE_of_iso e.symm (-n)
  have : K.IsLE (-n) := DerivedCategory.TStructure.t.isLE_of_iso e.symm (-n)
  have hi := homology_index_bounds.{u, v} K (-n) (-n) i inferInstance inferInstance h
  omega

/-- A complex isomorphic to a shift of a non-zero module in degree zero has non-zero cohomology
in the degree recording the shift. -/
private theorem nontrivial_homology_of_iso_single_shift {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (M : ModuleCat.{max v u} A) [Nontrivial M]
    (n : ℤ)
    (e : K ≅ ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj M)⟦n⟧) :
    Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) (-n)).obj K) := by
  let H₀ := DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0
  let S := (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj M
  have : Nontrivial (H₀.obj S) :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{max v u} A) 0).app M).toLinearEquiv.toEquiv.nontrivial_congr.mpr inferInstance
  exact (((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) (-n)).mapIso e) ≪≫
    ((H₀.shiftIso n (-n) 0 (by omega)).app S)).toLinearEquiv.toEquiv.nontrivial_congr.mpr this

/-! ### Localization of cohomology -/

/-- **Localizing a complex localizes its cohomology.** -/
def localizedHomologyIso {A : Type u} [CommRing A]
    (p : Ideal A) [p.IsPrime] (K : DerivedCategory (ModuleCat.{max v u} A)) (i : ℤ) :
    (ModuleCat.restrictScalars (algebraMap A (Localization.AtPrime p))).obj
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{max v u} (Localization.AtPrime p)) i).obj
          ((derivedExtensionScalars (algebraMap A (Localization.AtPrime p))).obj K)) ≅
      ModuleCat.of A (LocalizedModule p.primeCompl
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K)) := by
  let T := p.primeCompl
  let R := Localization.AtPrime p
  let M := (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K
  let U := ModuleCat.uliftFunctor.{u, max v u} A
  let eHom := (mapDerivedCategoryCompHomologyFunctorIso U i).app K
  let eLift := (CochainComplex.DerivedTensor.localizedModuleFunctor.{u, max v u} T).mapIso eHom
  let eULift := localizedModuleUliftIso.{u, max v u} (R := A) (S := T) (M := M)
  let eLoc :=
    (CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso.{u, u, max v u}
      T (A := R) i).app (U.mapDerivedCategory.obj K)
  exact eLoc ≪≫ eLift ≪≫ eULift

/-! ### The value of the dimension function at a minimal prime -/

/-- At a minimal prime the normalized localization of a dualizing complex is an injective hull of
the residue field placed in degree zero. -/
private theorem minimalPrime_localizedDualizing_iso_injectiveHull {A : Type u} [CommRing A]
    [IsNoetherianRing A] (K : DerivedCategory (ModuleCat.{max v u} A)) (hK : IsDualizingComplex K)
    (p : PrimeSpectrum A) (hp : IsMinimalPrime p.asIdeal) :
    ∃ E : ModuleCat.{max v u} (Localization.AtPrime p.asIdeal), Nontrivial E ∧
      Nonempty ((derivedExtensionScalars
            (algebraMap A (Localization.AtPrime p.asIdeal))).obj K ≅
        ((DerivedCategory.singleFunctor
          (ModuleCat.{max v u} (Localization.AtPrime p.asIdeal)) 0).obj E)⟦
          dualizingDimension.{u, v} K p⟧) := by
  let R := Localization.AtPrime p.asIdeal
  have : IsLocalRing R := Localization.AtPrime.isLocalRing p.asIdeal
  have : IsNoetherianRing R :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl R inferInstance
  have hnorm := dualizingDimension_spec.{u, v} K hK p
  obtain ⟨E, i, hi, hiHull⟩ := Module.exists_isInjectiveHull R
    ((ModuleCat.uliftFunctor.{v} R).obj (ModuleCat.of R (IsLocalRing.ResidueField R)))
  have : Mono i := hi
  have hheight : p.asIdeal.height = 0 :=
    Ideal.height_eq_zero_iff.2 (show p.asIdeal ∈ minimalPrimes A from hp)
  have hdimR : ringKrullDim R = (0 : WithBot ℕ∞) := by
    simpa [hheight] using IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal R
  obtain ⟨enorm⟩ :=
    nonempty_iso_single_injectiveHull_of_ringKrullDim_eq_zero.{u, v} _ hnorm hdimR E i hiHull
  exact ⟨E, ((ModuleCat.mono_iff_injective i).mp hi).nontrivial,
    ⟨(shiftNegShift _ _).symm ≪≫ (shiftFunctor _ _).mapIso enorm⟩⟩

/-- At a minimal prime the cohomology of a dualizing complex is non-zero after localization in
the degree opposite to the value of the dimension function. -/
private theorem nontrivial_localized_homology_neg_dualizingDimension {A : Type u} [CommRing A]
    [IsNoetherianRing A] (K : DerivedCategory (ModuleCat.{max v u} A)) (hK : IsDualizingComplex K)
    (p : PrimeSpectrum A) (hp : IsMinimalPrime p.asIdeal) :
    Nontrivial (LocalizedModule p.asIdeal.primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A)
        (-dualizingDimension.{u, v} K p)).obj K)) := by
  obtain ⟨E, hE, ⟨eL⟩⟩ := minimalPrime_localizedDualizing_iso_injectiveHull.{u, v} K hK p hp
  exact (localizedHomologyIso.{u, v} p.asIdeal K
    (-dualizingDimension.{u, v} K p)).toLinearEquiv.toEquiv.nontrivial_congr.mp
    (nontrivial_homology_of_iso_single_shift.{u, v} _ E _ eL)

/-! ### The value of the dimension function at a maximal ideal -/

/-- If derived Hom from a quotient ring into a complex is a shift of that ring in degree zero,
then the corresponding Ext group out of the quotient is non-zero. -/
private theorem residueExt_nontrivial_of_derivedHom_shift {A B : Type u} [CommRing A] [CommRing B]
    [Nontrivial B] (f : A →+* B) (K : DerivedCategory (ModuleCat.{max v u} A)) (n : ℤ)
    (hIso : Nonempty ((derivedHom.{u, v} f).obj K ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) 0).obj
        ((ModuleCat.uliftFunctor.{v} B).obj (ModuleCat.of B B)))⟦n⟧)) :
    Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        ((ModuleCat.restrictScalars.{max v u} f).obj
          ((ModuleCat.uliftFunctor.{v} B).obj (ModuleCat.of B B)))) K (-n)) := by
  let C := DerivedCategory (ModuleCat.{max v u} A)
  let S₀ := (DerivedCategory.singleFunctor (ModuleCat.{max v u} B) 0).obj
    ((ModuleCat.uliftFunctor.{v} B).obj (ModuleCat.of B B))
  let X₀ := (ModuleCat.restrictScalars.{max v u} f).obj
    ((ModuleCat.uliftFunctor.{v} B).obj (ModuleCat.of B B))
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj X₀
  let F₀ := ModuleCat.restrictScalars.{max v u} f
  let F := F₀.mapDerivedCategory
  let G := derivedHom.{u, v} f
  obtain ⟨eK⟩ := hIso
  let eSingle := (Functor.mapDerivedCategorySingleFunctor F₀ 0).app
    ((ModuleCat.uliftFunctor.{v} B).obj (ModuleCat.of B B))
  let eShift := (Functor.CommShift.commShiftIso F n).app S₀ ≪≫
    (shiftFunctor C n).mapIso eSingle
  let adj := Classical.choice (restrictScalarsDerived_adj_derivedHom.{u, v} f)
  let eAdj : (F.obj (S₀⟦n⟧) ⟶ K) ≃ (S₀⟦n⟧ ⟶ G.obj K) := adj.homEquiv _ _
  let eTarget : (F.obj (S₀⟦n⟧) ⟶ K) ≃ DerivedCategory.Ext X K (-n) :=
    (eShift.homCongr (Iso.refl K)).trans ((shiftEquiv C n).toAdjunction.homEquiv X K)
  let e : (S₀⟦n⟧ ⟶ G.obj K) ≃ DerivedCategory.Ext X K (-n) := eAdj.symm.trans eTarget
  have hId₀ : (𝟙 S₀ : S₀ ⟶ S₀) ≠ 0 := by
    let M := (ModuleCat.uliftFunctor.{v} B).obj (ModuleCat.of B B)
    let SF := DerivedCategory.singleFunctor (ModuleCat.{max v u} B) 0
    let : SF.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful SF
    have hmod : (𝟙 M : M ⟶ M) ≠ 0 := fun hz => one_ne_zero
      (congrArg (fun g : M ⟶ M => ULift.down (g.hom (ULift.up (1 : B)))) hz : (1 : B) = 0)
    exact fun hz => hmod (SF.map_injective (by simpa [S₀, M, SF] using hz))
  have hId : (𝟙 (S₀⟦n⟧) : S₀⟦n⟧ ⟶ S₀⟦n⟧) ≠ 0 := fun hz =>
    hId₀ ((shiftFunctor _ n).map_injective (by simpa using hz))
  have hHom : Nontrivial (S₀⟦n⟧ ⟶ G.obj K) :=
    nontrivial_of_ne eK.inv 0 fun hz => hId (by rw [← eK.inv_hom_id, hz, zero_comp])
  exact e.nontrivial_congr.mp hHom

/-- At a maximal ideal the shift identifying `RHom_A(A/m, K)` with the residue field is minus the
value of the dimension function. -/
private theorem dualizingDimension_eq_of_derivedHom_residueField_shift {A : Type u} [CommRing A]
    [IsNoetherianRing A] (K : DerivedCategory (ModuleCat.{max v u} A)) (hK : IsDualizingComplex K)
    (m : Ideal A) (hm : m.IsMaximal) (n : ℤ)
    (hIso : Nonempty ((derivedHom.{u, v} (Ideal.Quotient.mk m)).obj K ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} (A ⧸ m)) 0).obj
        ((ModuleCat.uliftFunctor.{v} (A ⧸ m)).obj (ModuleCat.of (A ⧸ m) (A ⧸ m))))⟦n⟧)) :
    dualizingDimension.{u, v} K ⟨m, hm.isPrime⟩ = n := by
  let B := A ⧸ m
  let f : A →+* B := Ideal.Quotient.mk m
  let : Field B := Ideal.Quotient.field m
  let : IsNoetherianRing B := inferInstance
  let p : PrimeSpectrum A := ⟨m, hm.isPrime⟩
  obtain ⟨eK⟩ := hIso
  have hKB : IsDualizingComplex ((derivedHom.{u, v} f).obj K) :=
    isDualizingComplex_derivedHom_of_finite.{u, v} f
      (RingHom.Finite.of_surjective f Ideal.Quotient.mk_surjective) K hK
  let KB := (derivedHom.{u, v} f).obj K
  have hcomap : PrimeSpectrum.comap f (⊥ : PrimeSpectrum B) = p :=
    PrimeSpectrum.ext (Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem)
  have hδquot : dualizingDimension.{u, v} K p
      = dualizingDimension.{u, v} KB (⊥ : PrimeSpectrum B) := by
    rw [← hcomap]
    exact (dualizingDimension_derivedHom_of_surjective.{u, v} f
      Ideal.Quotient.mk_surjective K hK (⊥ : PrimeSpectrum B)).symm
  let d := dualizingDimension.{u, v} KB (⊥ : PrimeSpectrum B)
  let R := Localization.AtPrime (⊥ : Ideal B)
  let LR := (derivedExtensionScalars (algebraMap B R)).obj KB
  have hminB : IsMinimalPrime (⊥ : Ideal B) := by
    change (⊥ : Ideal B) ∈ minimalPrimes B
    rw [IsDomain.minimalPrimes_eq_singleton_bot]
    simp
  obtain ⟨E, -, ⟨eL⟩⟩ :=
    minimalPrime_localizedDualizing_iso_injectiveHull.{u, v} KB hKB (⊥ : PrimeSpectrum B) hminB
  let CB := ModuleCat.{max v u} B
  let kB := (ModuleCat.uliftFunctor.{v} B).obj (ModuleCat.of B B)
  let T := (⊥ : PrimeSpectrum B).asIdeal.primeCompl
  let M := (DerivedCategory.homologyFunctor CB (-n)).obj KB
  have : Nontrivial M := nontrivial_homology_of_iso_single_shift.{u, v} KB kB n eK
  have hmk : Function.Injective (LocalizedModule.mkLinearMap T M) := by
    refine (IsLocalizedModule.injective_iff_isRegular T _).2 fun s x y hxy => ?_
    change (s : B) • x = (s : B) • y at hxy
    exact smul_right_injective M (fun hs0 => s.property (by simp [hs0])) hxy
  have hLRhom : Nontrivial
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) (-n)).obj LR) :=
    (localizedHomologyIso.{u, v} (⊥ : PrimeSpectrum B).asIdeal KB
      (-n)).toLinearEquiv.toEquiv.nontrivial_congr.mpr hmk.nontrivial
  have hdEq : -n = -d := homology_index_eq_of_iso_single_shift.{u, v} LR E d (-n) eL hLRhom
  rw [hδquot]
  omega

/-- The dimension function of a normalized dualizing complex over a Noetherian local ring
vanishes at the closed point. -/
theorem dualizingDimension_maximalIdeal_eq_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K) :
    dualizingDimension.{u, v} K
      ⟨IsLocalRing.maximalIdeal A, (IsLocalRing.maximalIdeal.isMaximal A).isPrime⟩ = 0 := by
  refine dualizingDimension_eq_of_derivedHom_residueField_shift.{u, v} K hK.1
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal.isMaximal A) 0 ?_
  obtain ⟨e⟩ := hK.2
  exact ⟨e ≪≫ ((shiftFunctorZero
    (DerivedCategory (ModuleCat.{max v u} (IsLocalRing.ResidueField A))) ℤ).app _).symm⟩

/-- At a maximal ideal the value of the dimension function of a dualizing complex with injective
amplitude in `[a, b]` lies in `[-b, -a]`. -/
private theorem dualizingDimension_maximal_mem_amplitude {A : Type u} [CommRing A]
    [IsNoetherianRing A] (K : DerivedCategory (ModuleCat.{max v u} A)) (hK : IsDualizingComplex K)
    (a b : ℤ) (hAmp : StacksDraft.InjectiveDimension.HasInjectiveAmplitude K a b)
    (m : Ideal A) (hm : m.IsMaximal) :
    a ≤ -dualizingDimension.{u, v} K ⟨m, hm.isPrime⟩ ∧
      -dualizingDimension.{u, v} K ⟨m, hm.isPrime⟩ ≤ b := by
  let B := A ⧸ m
  let f : A →+* B := Ideal.Quotient.mk m
  let : Field B := Ideal.Quotient.field m
  obtain ⟨n, hIso⟩ := derivedHom_residueField_iso_shift.{u, v} K hK m hm
  have hExt := residueExt_nontrivial_of_derivedHom_shift.{u, v} f K n hIso
  have hExtVan :=
    (StacksDraft.InjectiveDimension.hasInjectiveAmplitude_iff_ext_vanishing_iff_quotient_vanishing
      K a b).1.mp hAmp
  let X := (ModuleCat.restrictScalars.{max v u} f).obj
    ((ModuleCat.uliftFunctor.{v} B).obj (ModuleCat.of B B))
  rw [dualizingDimension_eq_of_derivedHom_residueField_shift.{u, v} K hK m hm n hIso]
  constructor
  · by_contra h
    exact (not_nontrivial_iff_subsingleton.mpr (hExtVan X (-n) (Or.inl (by omega)))) hExt
  · by_contra h
    exact (not_nontrivial_iff_subsingleton.mpr (hExtVan X (-n) (Or.inr (by omega)))) hExt

/-! ### The main result -/

/-- **Stacks Project, Tag 0A80.** A Noetherian ring admitting a dualizing complex has finite
Krull dimension. -/
@[stacks 0A80 "of finite dimension"]
theorem ringKrullDim_lt_top_of_isDualizingComplex {A : Type u} [CommRing A] [IsNoetherianRing A]
    {K : DerivedCategory (ModuleCat.{u} A)} (hK : IsDualizingComplex K) :
    ringKrullDim A < ⊤ := by
  obtain ⟨a, b, hAmp⟩ := hK.finiteInjectiveDimension
  obtain ⟨hGE, hLE⟩ := isGE_isLE_of_hasInjectiveAmplitude.{u, u} K a b hAmp
  set N : ℕ := a.natAbs + b.natAbs with hN
  set δ := dualizingDimensionFunction.{u, u} K hK
  have hδval : ∀ p, δ p = dualizingDimension.{u, u} K p := fun _ => rfl
  have hmin : ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal →
      -(N : ℤ) ≤ δ p ∧ δ p ≤ N := by
    intro p hp
    have hindex := localized_homology_index_bounds.{u, u} K a b
      (-dualizingDimension.{u, u} K p) hGE hLE p
      (nontrivial_localized_homology_neg_dualizingDimension.{u, u} K hK p hp)
    rw [hδval p, hN]
    omega
  have hmax : ∀ (m : Ideal A) (hm : m.IsMaximal),
      -(N : ℤ) ≤ δ ⟨m, hm.isPrime⟩ ∧ δ ⟨m, hm.isPrime⟩ ≤ N := by
    intro m hm
    have hindex := dualizingDimension_maximal_mem_amplitude.{u, u} K hK a b hAmp m hm
    rw [hδval ⟨m, hm.isPrime⟩, hN]
    omega
  have hanti : ∀ x y : PrimeSpectrum A, x ≤ y → δ y ≤ δ x := by
    intro x y hxy
    by_cases hEq : x = y
    · exact hEq ▸ le_rfl
    · exact (δ.strictAnti_specializes ((PrimeSpectrum.le_iff_specializes x y).mp hxy) hEq).le
  have hbound : ∀ p : PrimeSpectrum A, -(N : ℤ) ≤ δ p ∧ δ p ≤ N := by
    intro p
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (J := p.asIdeal) bot_le
    obtain ⟨mm, hmm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
    exact ⟨le_trans (hmax mm hmm).1
        (hanti p ⟨mm, hmm.isPrime⟩ ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hpm)),
      le_trans (hanti ⟨q, hq.isPrime⟩ p ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hqp))
      (hmin ⟨q, hq.isPrime⟩ hq).2⟩
  exact ringKrullDim_lt_top_of_bounded_dimensionFunction A δ N hbound

/-- **The heights of the primes of a ring with a dualizing complex are bounded by a natural
number.** The Krull dimension of such a ring is finite by
`Dualizing.ringKrullDim_lt_top_of_isDualizingComplex`, and no height exceeds it
(`Ideal.height_le_ringKrullDim_of_isPrime`).

The bound is packaged as a natural number because that is the currency of the consumers: the
statements of `Stacks.LocalCohomology.exists_isClosed_subset_depth_lt_subset` and
`Stacks.LocalCohomology.exists_isClosed_subset_depth_lt_two_subset` take a bound `d : ℕ` on the
heights rather than the dualizing complex that produces it, so that they apply to any
finite-dimensional Noetherian ring. -/
theorem exists_height_le_of_isDualizingComplex {A : Type u} [CommRing A] [IsNoetherianRing A]
    {K : DerivedCategory (ModuleCat.{u} A)} (hK : IsDualizingComplex K) :
    ∃ d : ℕ, ∀ q : PrimeSpectrum A, q.asIdeal.height ≤ (d : ℕ∞) := by
  have hdim := ringKrullDim_lt_top_of_isDualizingComplex hK
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ringKrullDim A ≤ (N : ℕ) := by
    by_cases he : ringKrullDim A = ⊥
    · exact ⟨0, he ▸ bot_le⟩
    obtain ⟨e, he'⟩ := WithBot.ne_bot_iff_exists.mp he
    have hetop : e ≠ ⊤ := by
      intro h
      rw [← he', h] at hdim
      exact lt_irrefl _ hdim
    obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp hetop
    exact ⟨M, by rw [← he', ← hM]; rfl⟩
  exact ⟨N, fun q => by
    exact_mod_cast (Ideal.height_le_ringKrullDim_of_isPrime (I := q.asIdeal)).trans hN⟩

end Dualizing

end
