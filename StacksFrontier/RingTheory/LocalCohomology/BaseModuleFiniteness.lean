module

public import StacksFrontier.RingTheory.F6Rank301.AnnihilatingLocalCohomology
public import StacksFrontier.RingTheory.LocalCohomology.FiniteLocallyFreeFiniteness
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessAnnihilatorCriterion

/-!
# Annihilating and finiteness of local cohomology relative to an arbitrary base module

Tags 0BPX and 0BPY are stated over the base module `A`, the ring viewed as a module over itself.
Nothing in their proofs uses that the base is the ring: all that is needed is a base module `N`
together with, for every `g ∈ I`, a factorization `a ∘ b = g ^ k` of a power of `g` on `M`
through a finite direct sum of copies of `N`. These are the two statements with `A` replaced by
such an `N`.

## Main results

* `Stacks.LocalCohomology.exists_pow_smul_localCohomology_eq_bot_of_base` — tag 0BPX over an
  arbitrary base module.
* `Stacks.LocalCohomology.localCohomologyWithSupportIn_finite_of_base` — tag 0BPY over an
  arbitrary base module.

## References

* [Stacks Project, Tag 0BPX](https://stacks.math.columbia.edu/tag/0BPX)
* [Stacks Project, Tag 0BPY](https://stacks.math.columbia.edu/tag/0BPY)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

section Base

variable (A : Type u) [CommRing A]

/-- `J • ⊤ = ⊥` on a module exactly when `J` lies in its annihilator. -/
private lemma smul_top_eq_bot_iff_le_annihilator {A : Type u} [CommRing A] {M : Type u}
    [AddCommGroup M] [Module A M] (J : Ideal A) :
    J • (⊤ : Submodule A M) = ⊥ ↔ J ≤ Module.annihilator A M := by
  rw [← Submodule.annihilator_top, Submodule.le_annihilator_iff]

/-- An element annihilates `H X` iff `H` sends multiplication by it on `X` to zero. -/
private lemma mem_annihilator_iff_map_smul_id_eq_zero {A : Type u} [CommRing A]
    (H : ModuleCat.{u} A ⥤ ModuleCat.{u} A) [H.Additive] [H.Linear A] (X : ModuleCat.{u} A)
    (a : A) : a ∈ Module.annihilator A (H.obj X) ↔ H.map (a • 𝟙 X) = 0 := by
  rw [Functor.map_smul, H.map_id, Module.mem_annihilator]
  refine ⟨fun h ↦ by ext z; exact h z, fun h z ↦ ?_⟩
  simpa only [ModuleCat.hom_smul, ModuleCat.hom_id, ModuleCat.hom_zero, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq, LinearMap.zero_apply] using
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) z

/-- If `J ^ n` annihilates `H^i_T(N)`, it annihilates `H^i_T(N^{⊕d})` for every `d`: the identity
of a finite direct sum is the sum of the idempotents `e j ∘ p j`, and the `A`-linear additive
functor `H^i_T(-)` turns multiplication by `a ∈ J ^ n` on `N^{⊕d}` into a sum of maps factoring
through multiplication by `a` on `H^i_T(N)`, which is zero. -/
private lemma localCohomology_basePi_annihilator (J : Ideal A) (n : ℕ)
    (T : Set (PrimeSpectrum A)) (i : ℤ) (N : ModuleCat.{u} A)
    (hN : J ^ n • (⊤ : Submodule A
      (localCohomologyWithSupportIn.{u, 0} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) i)) = ⊥)
    (d : ℕ) :
    J ^ n ≤ Module.annihilator A
      (localCohomologyWithSupportIn.{u, 0} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (Fin d → (N : Type u)))) i) := by
  -- degree-`i` local cohomology with support in `T`, as a functor on `A`-modules
  let H : ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
    DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
      derivedSectionsWithSupportIn.{u, 0} A T ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
  let F : ModuleCat.{u} A := ModuleCat.of A (Fin d → (N : Type u))
  have hscalar (a : A) (ha : a ∈ J ^ n) : H.map (a • (𝟙 N)) = 0 :=
    (mem_annihilator_iff_map_smul_id_eq_zero H N a).mp
      ((smul_top_eq_bot_iff_le_annihilator (M := H.obj N) _).mp hN ha)
  let e (j : Fin d) : (N : Type u) →ₗ[A] (Fin d → (N : Type u)) :=
    LinearMap.single A (fun _ : Fin d => (N : Type u)) j
  let p (j : Fin d) : (Fin d → (N : Type u)) →ₗ[A] (N : Type u) :=
    LinearMap.proj (R := A) (φ := fun _ : Fin d => (N : Type u)) j
  have hid : (∑ j : Fin d, (e j).comp (p j)) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply, e, p,
      LinearMap.single_apply, LinearMap.proj_apply]
    exact Finset.univ_sum_single x
  have hdecomp : (∑ j : Fin d, ModuleCat.ofHom (p j) ≫ ModuleCat.ofHom (e j)) = 𝟙 F := by
    apply (ModuleCat.homAddEquiv (M := F) (N := F)).injective
    rw [map_sum]
    simpa [ModuleCat.homAddEquiv, ModuleCat.homEquiv, ModuleCat.hom_comp,
      ModuleCat.hom_id, e, p] using hid
  have hzero (a : A) (ha : a ∈ J ^ n) : H.map (a • (𝟙 F)) = 0 := by
    calc
      H.map (a • (𝟙 F)) =
          H.map (a • (∑ j : Fin d, ModuleCat.ofHom (p j) ≫ ModuleCat.ofHom (e j))) := by
        rw [← hdecomp]
      _ = ∑ j : Fin d, H.map (a • (ModuleCat.ofHom (p j) ≫ ModuleCat.ofHom (e j))) := by
        simp only [Functor.map_sum, Finset.smul_sum]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [Functor.map_smul, Functor.map_comp]
        have hmid : a • (H.map (ModuleCat.ofHom (p j)) ≫ H.map (ModuleCat.ofHom (e j))) =
            H.map (ModuleCat.ofHom (p j)) ≫ H.map (a • (𝟙 N)) ≫
              H.map (ModuleCat.ofHom (e j)) := by
          have hlinid : H.map (a • 𝟙 N) = a • 𝟙 (H.obj N) := by
            rw [Functor.map_smul, H.map_id]
          set g := H.map (ModuleCat.ofHom (p j))
          set k := H.map (ModuleCat.ofHom (e j))
          have hg : a • g = g ≫ (a • 𝟙 (H.obj N)) := by
            rw [Linear.comp_smul, Category.comp_id]
          rw [← Linear.smul_comp, hg, Category.assoc, ← hlinid]
        rw [hmid, hscalar a ha]
        simp
  exact fun a ha ↦ (mem_annihilator_iff_map_smul_id_eq_zero H F a).mpr (hzero a ha)

/-- Given a factorization `a ∘ b = g ^ k` of a power of `g` on `M` through `N^{⊕d}`, the element
`g ^ k` lies in the colon ideal `(ann H^i_T(M) : J ^ n)`. Multiply the factorization by `y ∈ J ^ n`
and apply `H^i_T(-)`: the middle map becomes zero because `J ^ n` annihilates `H^i_T(N^{⊕d})`, so
multiplication by `g ^ k * y` is zero on `H^i_T(M)`. -/
private lemma localCohomology_base_annihilator_colon (J : Ideal A) (n : ℕ)
    (T : Set (PrimeSpectrum A)) (i : ℤ) (N : ModuleCat.{u} A)
    (hN : J ^ n • (⊤ : Submodule A
      (localCohomologyWithSupportIn.{u, 0} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) i)) = ⊥)
    (M : ModuleCat.{u} A) (g : A) (k d : ℕ)
    (a : (Fin d → (N : Type u)) →ₗ[A] (M : Type u))
    (b : (M : Type u) →ₗ[A] (Fin d → (N : Type u)))
    (hfactor : a ∘ₗ b = g ^ k • LinearMap.id) :
    g ^ k ∈ Submodule.colon (Module.annihilator A
      (localCohomologyWithSupportIn.{u, 0} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) i))
      (J ^ n : Ideal A) := by
  -- degree-`i` local cohomology with support in `T`, as a functor on `A`-modules
  let H : ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
    DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
      derivedSectionsWithSupportIn.{u, 0} A T ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
  let F : ModuleCat.{u} A := ModuleCat.of A (Fin d → (N : Type u))
  have hfreeAnn := localCohomology_basePi_annihilator A J n T i N hN d
  rw [Submodule.mem_colon]
  intro y hy
  have hkill : H.map (ModuleCat.ofHom
      (y • (LinearMap.id : (Fin d → (N : Type u)) →ₗ[A] (Fin d → (N : Type u))))) = 0 :=
    (mem_annihilator_iff_map_smul_id_eq_zero H F y).mp (hfreeAnn hy)
  have hfactorY : a.comp
      ((y • (LinearMap.id : (Fin d → (N : Type u)) →ₗ[A] (Fin d → (N : Type u)))).comp b) =
      (g ^ k * y) • LinearMap.id := by
    ext x
    show a (y • b x) = (g ^ k * y) • x
    rw [map_smul, ← LinearMap.comp_apply, hfactor]
    simp [smul_smul, mul_comm]
  have hcat : ModuleCat.ofHom b ≫
      ModuleCat.ofHom
        (y • (LinearMap.id : (Fin d → (N : Type u)) →ₗ[A] (Fin d → (N : Type u)))) ≫
      ModuleCat.ofHom a =
      ModuleCat.ofHom ((g ^ k * y) • (LinearMap.id : (M : Type u) →ₗ[A] (M : Type u))) := by
    apply ModuleCat.hom_ext
    simpa [ModuleCat.hom_comp, ← LinearMap.comp_assoc] using hfactorY
  have hmapcat := congrArg H.map hcat
  rw [Functor.map_comp, Functor.map_comp] at hmapcat
  have hzero : H.map (ModuleCat.ofHom
      ((g ^ k * y) • (LinearMap.id : (M : Type u) →ₗ[A] (M : Type u)))) = 0 := by
    rw [← hmapcat]
    simp [hkill]
  exact (mem_annihilator_iff_map_smul_id_eq_zero H M _).mpr hzero

end Base

/-- **Tag 0BPX over an arbitrary base module.** If a power of `J` annihilates the `i`-th local
cohomology of `N` supported on `V(I)`, then a power of `J` annihilates the corresponding local
cohomology of every `A`-module `M` such that, for every `g ∈ I`, some power of `g` on `M` factors
through a finite direct sum of copies of `N`. -/
theorem exists_pow_smul_localCohomology_eq_bot_of_base
    (A : Type u) [CommRing A] (J I : Ideal A) (hJI : J ≤ I) (hI : I.FG) (i : ℕ)
    (N : ModuleCat.{u} A)
    (hN : ∃ n : ℕ, J ^ n • (⊤ : Submodule A
      (localCohomologyWithSupportIn.{u, 0} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) (i : ℤ))) = ⊥)
    (M : ModuleCat.{u} A)
    (hM : ∀ g ∈ I, ∃ (k d : ℕ) (a : (Fin d → (N : Type u)) →ₗ[A] (M : Type u))
        (b : (M : Type u) →ₗ[A] (Fin d → (N : Type u))),
        a ∘ₗ b = g ^ k • LinearMap.id) :
    ∃ m : ℕ, J ^ m • (⊤ : Submodule A
      (localCohomologyWithSupportIn.{u, 0} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (i : ℤ))) = ⊥ := by
  obtain ⟨n, hNeq⟩ := hN
  let T := PrimeSpectrum.zeroLocus (I : Set A)
  let Hmod := localCohomologyWithSupportIn.{u, 0} A T
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (i : ℤ)
  let Ann : Ideal A := Module.annihilator A Hmod
  let K : Ideal A := Submodule.colon Ann (J ^ n : Ideal A)
  have hIrad : I ≤ K.radical := by
    intro g hg
    obtain ⟨k, d, a, b, hfactor⟩ := hM g hg
    exact Ideal.mem_radical_iff.mpr ⟨k,
      localCohomology_base_annihilator_colon A J n T i N hNeq M g k d a b hfactor⟩
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIrad hI
  have hJpow : J ^ m ≤ K := (Ideal.pow_right_mono hJI m).trans hm
  have hprod : J ^ (m + n) ≤ Ann := by
    rw [pow_add]
    apply Ideal.mul_le.mpr
    intro x hx y hy
    have hxy : x • y ∈ Ann := (Submodule.mem_colon.mp (hJpow hx)) y hy
    simpa [smul_eq_mul] using hxy
  refine ⟨m + n, ?_⟩
  exact (smul_top_eq_bot_iff_le_annihilator _).mpr hprod

/-- **Tag 0BPY over an arbitrary base module.** Let `A` be a Noetherian ring, `I ⊆ A` an ideal,
`Z = V(I)` and `n ≥ 0`. If the local cohomology `H^i_Z(N)` of a finite module `N` is finite for
`0 ≤ i ≤ n`, then `H^i_Z(M)` is finite for `0 ≤ i ≤ n`, for every finite `A`-module `M` such that,
for every `g ∈ I`, some power of `g` on `M` factors through a finite direct sum of copies of
`N`. -/
theorem localCohomologyWithSupportIn_finite_of_base
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ)
    (N : ModuleCat.{u} A) [Module.Finite A (N : Type u)]
    (hN : ∀ i : ℕ, i ≤ n → Module.Finite A
      (localCohomologyWithSupportIn.{u, 0} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) (i : ℤ)))
    (M : ModuleCat.{u} A) [Module.Finite A (M : Type u)]
    (hM : ∀ g ∈ I, ∃ (k d : ℕ) (a : (Fin d → (N : Type u)) →ₗ[A] (M : Type u))
        (b : (M : Type u) →ₗ[A] (Fin d → (N : Type u))),
        a ∘ₗ b = g ^ k • LinearMap.id) :
    ∀ i : ℕ, i ≤ n → Module.Finite A
      (localCohomologyWithSupportIn.{u, 0} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (i : ℤ)) := by
  -- finiteness in the natural-number degrees `≤ n` gives it in all integral degrees `≤ n`,
  -- the modules in negative degrees vanishing
  have hNint : ∀ i : ℤ, i ≤ (n : ℤ) → Module.Finite A
      (localCohomologyWithSupportIn.{u, 0} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) i) := by
    intro i hi
    rcases lt_or_ge i 0 with hneg | hpos
    · exact finite_localCohomologyWithSupportIn_of_nonpos.{u, 0} A _ N i hneg.le
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = (k : ℤ) := ⟨i.toNat, (Int.toNat_of_nonneg hpos).symm⟩
      exact hN k (by omega)
  obtain ⟨e, he⟩ :=
    (finite_localCohomologyWithSupportIn_iff_exists_pow_annihilator.{u, 0} A I N n).mp hNint
  have key : ∀ i : ℕ, ∃ m : ℕ, i ≤ n → I ^ m ≤ Module.annihilator A
      (localCohomologyWithSupportIn.{u, 0} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (i : ℤ)) := by
    intro i
    by_cases hi : i ≤ n
    · obtain ⟨m, hm⟩ := exists_pow_smul_localCohomology_eq_bot_of_base A I I le_rfl
        (Ideal.fg_of_isNoetherianRing I) i N
        ⟨e, (smul_top_eq_bot_iff_le_annihilator _).mpr
          (he (i : ℤ) (by exact_mod_cast hi))⟩
        M hM
      exact ⟨m, fun _ ↦ (smul_top_eq_bot_iff_le_annihilator _).mp hm⟩
    · exact ⟨0, fun h ↦ absurd h hi⟩
  choose m hm using key
  intro i hi
  refine (finite_localCohomologyWithSupportIn_iff_exists_pow_annihilator.{u, 0} A I M n).mpr
    ⟨(Finset.range (n + 1)).sup m, ?_⟩ (i : ℤ) (by exact_mod_cast hi)
  intro j hj
  rcases lt_or_ge j 0 with hneg | hpos
  · rw [Module.annihilator_eq_top_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp
      (isZero_localCohomologyWithSupportIn_of_neg.{u, 0} _ M j hneg))]
    exact le_top
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = (k : ℤ) := ⟨j.toNat, (Int.toNat_of_nonneg hpos).symm⟩
    refine (Ideal.pow_le_pow_right ?_).trans (hm k (by omega))
    exact Finset.le_sup (Finset.mem_range.mpr (by omega))

end Stacks.LocalCohomology

end
