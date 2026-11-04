module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Support
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ExtComparison
public import StacksFrontier.RingTheory.Dualizing.ExtCompletionComparison
public import StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds
public import StacksFrontier.RingTheory.Dualizing.ExtSupportBound
public import StacksFrontier.RingTheory.Dualizing.Normalized
public import StacksFrontier.RingTheory.Dualizing.NormalizedZeroDimensional

/-!
# Nonvanishing of a dualizing complex at a minimal prime

Let `A` be a Noetherian local ring with a normalized dualizing complex `K`, and let `p` be a
minimal prime of `A` with `dim(A/p) = e`. This file proves that the localization at `p` of the
cohomology module `H^i(K)` is nonzero exactly in the single degree `i = -e`.

Three facts combine. Above the degree `-e` the support of `H^i(K)` has dimension at most `-i`,
which is too small to contain `p`. Below it, multiplication by a suitable element outside `p`
factors through `A/p^n` for a power `p^n` killed by that element, and `Ext` out of `A/p^n`
vanishes below `-e`. In the degree `-e` itself, nonvanishing comes from the fact that a dualizing
complex has full support: an element of `A` acting as zero on every cohomology module of `K`
acts nilpotently on `K` itself, hence vanishes in the ring of derived endomorphisms of `K`,
which is `A`.

Over a Noetherian ring that need not be local, and for a dualizing complex that need not be
normalized, the same phenomenon takes the weaker form of a bare existence and uniqueness
statement: at a minimal prime `p` exactly one `H^i(K)_p` is nonzero. Here `A_p` has Krull
dimension zero, so the localized complex, which is again dualizing, is a shift of an injective
hull of the residue field of `A_p` placed in degree zero; that object has cohomology in a single
degree, and the shift records which one.

## Main results

* `Dualizing.nontrivial_localized_homology_iff_eq_neg_dimension` is [Stacks, Tag 0A7V]: for `p` a
  minimal prime with `dim(A/p) = e`, the module `H^i(K)_p` is nonzero if and only if `i = -e`.
* `Dualizing.existsUnique_nontrivial_localized_homology` is [Stacks, Tag 0A7X]: over a Noetherian
  ring and for a dualizing complex `K`, exactly one `H^i(K)_p` is nonzero at a minimal prime `p`.

## Implementation notes

Nonvanishing of the localization is stated as `Nontrivial (LocalizedModule p.primeCompl _)`,
which is by definition membership in `Module.support`, so the proof works with
`Module.support` throughout.

Derived endomorphisms of `K` are identified with `A` by composing the Ext--cohomology comparison
`Dualizing.extDerivedHomLinearEquiv` with `Dualizing.dualizingDerivedHomSelfIsoRing`. Only the
`A`-linearity of that identification is used, never the image of the identity morphism: an
element killing the whole module `K ⟶ K⟦0⟧` kills `1 : A`, which is enough.

The localization of `K` at `p` is the derived extension of scalars along `A → A_p`, and the
comparison of that construction with localization of cohomology modules
(`CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso`) is what turns a
statement about `H^i(K_p)` into one about `H^i(K)_p`. It is stated for modules in the universe of
the ring, so the cohomology of `K` is lifted there first and then lifted back.

## References

* [Stacks Project, Tag 0A7V](https://stacks.math.columbia.edu/tag/0A7V)
* [Stacks Project, Tag 0A7X](https://stacks.math.columbia.edu/tag/0A7X)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated Triangulated

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-! ### A free rank-one module corepresents cohomology -/

/-- Morphisms out of the universe-lifted ring are its target, `A`-linearly. -/
private noncomputable def homFromUliftRing {A : Type u} [CommRing A]
    (M : ModuleCat.{max v u} A) :
    (ModuleCat.of A (ULift.{v} A) ⟶ M) ≃ₗ[A] M :=
  (ModuleCat.homLinearEquiv (S := A)).trans
    ((LinearEquiv.arrowCongr (ULift.moduleEquiv (R := A) (M := A)) (LinearEquiv.refl A M)).trans
      (LinearMap.ringLmapEquivSelf A A M))

/-- `Ext^i` out of the universe-lifted ring placed in degree zero is the degree-`i` cohomology
module: the free rank-one module is projective, so it corepresents cohomology. -/
private noncomputable def extFromUliftRing {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (i : ℤ) :
    DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A (ULift.{v} A))) K i ≃ₗ[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K) :=
  (DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of A (ULift.{v} A))
      ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) i).obj K) 0 A).trans
    ((homFromUliftRing _).trans
      ((StacksDraft.DerivedHom.ExtComparison.homologyShiftNatIso.{u, v} A i).app K).toLinearEquiv)

/-! ### Dimension of the support -/

/-- A prime in the support of a module forces the dimension of the support to be at least the
dimension of `A/p`, since the whole closed set `V(p)` lies in the support. -/
private lemma ringKrullDim_quotient_le_supportDim {A : Type u} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N] {p : PrimeSpectrum A}
    (hp : p ∈ Module.support A N) :
    ringKrullDim (A ⧸ p.asIdeal) ≤ Module.supportDim A N := by
  have hsub : Set.Ici p ⊆ Module.support A N := fun _ hq => Module.mem_support_mono hq hp
  rw [ringKrullDim_quotient,
    show PrimeSpectrum.zeroLocus (R := A) (p.asIdeal : Set A) = Set.Ici p from rfl]
  exact Order.krullDim_le_of_strictMono
    (fun q : Set.Ici p => (⟨q.1, hsub q.2⟩ : Module.support A N)) (fun _ _ h => h)

/-- **Stacks 0A7U, read on cohomology.** The support of `H^i(K)` has dimension at most `-i`. -/
private lemma supportDim_homology_le {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K) (i : ℤ) :
    Module.supportDim A ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K) ≤
      if i ≤ 0 then (((Int.toNat (-i) : ℕ) : ℕ∞) : WithBot ℕ∞) else ⊥ := by
  have : Module.Finite A (ULift.{v} A) :=
    Module.Finite.equiv (ULift.moduleEquiv (R := A) (M := A)).symm
  have h := supportDim_ext_le_neg_degree K (ULift.{v} A) hK i
  rwa [Module.supportDim_eq_of_equiv (extFromUliftRing K i)] at h

/-- If `p` is in the support of `H^i(K)` then `i ≤ -e`, where `e = dim(A/p)`. -/
private lemma le_neg_of_mem_support_homology {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K) (p : PrimeSpectrum A) (e : ℕ)
    (hdim : ringKrullDim (A ⧸ p.asIdeal) = (e : WithBot ℕ∞)) (i : ℤ)
    (hp : p ∈ Module.support A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K)) :
    i ≤ -(e : ℤ) := by
  have hle := le_trans (hdim ▸ ringKrullDim_quotient_le_supportDim hp)
    (supportDim_homology_le K hK i)
  split_ifs at hle with hi
  · have hnat : (e : ℕ∞) ≤ ((Int.toNat (-i) : ℕ) : ℕ∞) := by exact_mod_cast hle
    have : e ≤ Int.toNat (-i) := by exact_mod_cast hnat
    omega
  · exact absurd (le_bot_iff.mp hle) (by simp)

/-! ### A power of the prime is killed by an element outside it -/

/-- At a minimal prime `p` of a Noetherian ring, some element outside `p` kills a positive power
of `p`: the localization `A_p` is artinian, so its maximal ideal is nilpotent, and the finitely
many generators of `p^n` each die in `A_p`. -/
private lemma exists_smul_pow_eq_zero {A : Type u} [CommRing A] [IsNoetherianRing A]
    (p : PrimeSpectrum A) (hp : IsMinimalPrime p.asIdeal) :
    ∃ (n : ℕ) (s : A), 0 < n ∧ s ∉ p.asIdeal ∧ ∀ x ∈ p.asIdeal ^ n, s * x = 0 := by
  have hpp : p.asIdeal.IsPrime := p.isPrime
  have hheight : p.asIdeal.height = 0 :=
    Ideal.height_eq_zero_iff.mpr (by simpa [minimalPrimes] using hp)
  have hdim : ringKrullDim (Localization.AtPrime p.asIdeal) = 0 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Localization.AtPrime p.asIdeal),
      hheight]
    rfl
  have hart : IsArtinianRing (Localization.AtPrime p.asIdeal) :=
    isArtinianRing_iff_krullDimLE_zero.mpr (Ring.krullDimLE_iff.mpr (by simp [hdim]))
  obtain ⟨m, hm⟩ :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal (Localization.AtPrime p.asIdeal)).mp hart
  have hm' : ∀ y ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ^ (m + 1),
      y = 0 := by
    intro y hy
    have hy' : y ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ^ m :=
      Ideal.pow_le_pow_right (by omega) hy
    rw [hm] at hy'
    simpa using hy'
  -- every element of `p ^ (m + 1)` dies in `A_p`
  have hzero : ∀ x ∈ p.asIdeal ^ (m + 1),
      ∃ c ∉ p.asIdeal, c * x = 0 := by
    intro x hx
    have hmapmem : algebraMap A (Localization.AtPrime p.asIdeal) x ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ^ (m + 1) := by
      have h1 : algebraMap A (Localization.AtPrime p.asIdeal) x ∈
          Ideal.map (algebraMap A (Localization.AtPrime p.asIdeal)) (p.asIdeal ^ (m + 1)) :=
        Ideal.mem_map_of_mem _ hx
      rwa [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal
        (Localization.AtPrime p.asIdeal)] at h1
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl _ x).mp
      (hm' _ hmapmem)
    exact ⟨c.1, c.2, hc⟩
  -- a common witness for a finite generating set
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian (p.asIdeal ^ (m + 1)) : (p.asIdeal ^ (m + 1)).FG)
  have hmemG : ∀ g : G, (g : A) ∈ p.asIdeal ^ (m + 1) := by
    intro g
    rw [← hG]
    exact Submodule.subset_span g.2
  choose c hc hcz using fun g : G => hzero g.1 (hmemG g)
  refine ⟨m + 1, ∏ g ∈ G.attach, c g, by omega, ?_, ?_⟩
  · exact p.asIdeal.primeCompl.prod_mem (fun g _ => hc g)
  · intro x hx
    have hsub : p.asIdeal ^ (m + 1) ≤
        LinearMap.ker (LinearMap.lsmul A A (∏ g ∈ G.attach, c g)) := by
      rw [← hG, Submodule.span_le]
      intro y hy
      obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem c (Finset.mem_attach G ⟨y, hy⟩)
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.lsmul_apply, smul_eq_mul]
      rw [hd, mul_comm (c ⟨y, hy⟩) d, mul_assoc, hcz ⟨y, hy⟩, mul_zero]
    simpa [LinearMap.mem_ker] using hsub hx

/-! ### Scalar actions -/

/-- Precomposing with `s • 𝟙` is acting by `s`. -/
private lemma smul_id_comp {A : Type u} [CommRing A] {C : Type*} [Category C] [Preadditive C]
    [Linear A C] {X Y : C} (s : A) (f : X ⟶ Y) : (s • 𝟙 X) ≫ f = s • f := by
  simp

/-- An element killing all of a module kills any linearly equivalent module. -/
private lemma smul_eq_zero_of_linearEquiv {A : Type u} [CommRing A] {M N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) (s : A)
    (h : ∀ x : M, s • x = 0) (y : N) : s • y = 0 := by
  rw [← e.apply_symm_apply y, ← map_smul, h, map_zero]

/-- An element acts as zero on the cohomology of an object if that cohomology vanishes. -/
private lemma smul_homology_eq_zero_of_isZero {A : Type u} [CommRing A] (s : A)
    {X : DerivedCategory (ModuleCat.{max v u} A)} {j : ℤ}
    (hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) j).obj X))
    (m : (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) j).obj X) : s • m = 0 := by
  have := ModuleCat.isZero_iff_subsingleton.mp hz
  exact Subsingleton.elim _ _

/-! ### The auxiliary quotient `A / p ^ n` -/

/-- The quotient by a positive power of `p` has support of dimension `dim(A/p)`. -/
private lemma supportDim_ulift_quotient_pow {A : Type u} [CommRing A] (p : PrimeSpectrum A)
    (e n : ℕ) (hn : 0 < n) (hdim : ringKrullDim (A ⧸ p.asIdeal) = (e : WithBot ℕ∞)) :
    Module.supportDim A (ULift.{v} (A ⧸ p.asIdeal ^ n)) = (e : WithBot ℕ∞) := by
  have hq : ringKrullDim (A ⧸ p.asIdeal ^ n) = ringKrullDim (A ⧸ p.asIdeal) := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient,
      PrimeSpectrum.zeroLocus_pow p.asIdeal (by omega)]
  rw [Module.supportDim_eq_of_equiv (ULift.moduleEquiv (R := A) (M := A ⧸ p.asIdeal ^ n)),
    Module.supportDim_quotient_eq_ringKrullDim, hq, hdim]

/-! ### Vanishing below the dimension -/

/-- The quotient map `A → A / I`, universe-lifted. -/
private noncomputable def uliftMkQ {A : Type u} [CommRing A] (I : Ideal A) :
    ModuleCat.of A (ULift.{v} A) ⟶ ModuleCat.of A (ULift.{v} (A ⧸ I)) :=
  ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ I.mkQ ∘ₗ ULift.moduleEquiv.toLinearMap)

/-- Multiplication by an element killing `I`, viewed as a map out of `A / I` and
universe-lifted. -/
private noncomputable def uliftLiftQ {A : Type u} [CommRing A] (I : Ideal A) (s : A)
    (hs : I ≤ LinearMap.ker (LinearMap.lsmul A A s)) :
    ModuleCat.of A (ULift.{v} (A ⧸ I)) ⟶ ModuleCat.of A (ULift.{v} A) :=
  ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ
    I.liftQ (LinearMap.lsmul A A s) hs ∘ₗ ULift.moduleEquiv.toLinearMap)

/-- Multiplication by an element killing `I` factors through `A / I`. -/
private lemma uliftMkQ_comp_uliftLiftQ {A : Type u} [CommRing A] (I : Ideal A) (s : A)
    (hs : I ≤ LinearMap.ker (LinearMap.lsmul A A s)) :
    uliftMkQ I ≫ uliftLiftQ I s hs = s • 𝟙 (ModuleCat.of A (ULift.{v} A)) :=
  ModuleCat.hom_ext <| LinearMap.ext fun y =>
    ULift.ext _ _ (LinearMap.congr_fun (I.liftQ_mkQ _ hs) y.down)

/-- Multiplication by an element `s` killing an ideal `I` factors through `A / I`; applying
`Ext^i(-, K)` therefore makes `s` kill `Ext^i(A[0], K)` whenever `Ext^i((A/I)[0], K)` vanishes. -/
private lemma smul_extFromUliftRing_eq_zero {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (I : Ideal A) (s : A)
    (hs : ∀ x ∈ I, s * x = 0) (i : ℤ)
    (hsub : Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A (ULift.{v} (A ⧸ I)))) K i))
    (x : DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A (ULift.{v} A))) K i) :
    s • x = 0 := by
  have hker : I ≤ LinearMap.ker (LinearMap.lsmul A A s) := by
    intro y hy
    simpa [LinearMap.mem_ker] using hs y hy
  have hS : s • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A (ULift.{v} A))) =
      (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map (uliftMkQ.{u, v} I) ≫
        (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
          (uliftLiftQ.{u, v} I s hker) := by
    rw [← Functor.map_comp, uliftMkQ_comp_uliftLiftQ, Functor.map_smul,
      (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map_id]
  calc s • x = (s • 𝟙 _) ≫ x := (smul_id_comp s x).symm
    _ = (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map (uliftMkQ.{u, v} I) ≫
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
          (uliftLiftQ.{u, v} I s hker) ≫ x) := by
          rw [hS, Category.assoc]
    _ = 0 := by
        rw [Subsingleton.elim ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
          (uliftLiftQ.{u, v} I s hker) ≫ x) 0, Limits.comp_zero]

/-- Below the degree `-e` the prime `p` is outside the support of `H^i(K)`. -/
private lemma notMem_support_homology_of_lt {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K) (p : PrimeSpectrum A)
    (hp : IsMinimalPrime p.asIdeal) (e : ℕ)
    (hdim : ringKrullDim (A ⧸ p.asIdeal) = (e : WithBot ℕ∞)) (i : ℤ) (hi : i < -(e : ℤ)) :
    p ∉ Module.support A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K) := by
  obtain ⟨n, s, hn, hsp, hs⟩ := exists_smul_pow_eq_zero p hp
  have hntop : p.asIdeal ^ n ≠ ⊤ :=
    fun h => p.isPrime.ne_top (top_le_iff.mp (h ▸ Ideal.pow_le_self (by omega)))
  have hNT : Nontrivial (ULift.{v} (A ⧸ p.asIdeal ^ n)) := by
    have := Ideal.Quotient.nontrivial_iff.mpr hntop
    infer_instance
  have hFin : Module.Finite A (ULift.{v} (A ⧸ p.asIdeal ^ n)) :=
    Module.Finite.equiv (ULift.moduleEquiv (R := A) (M := A ⧸ p.asIdeal ^ n)).symm
  have hBdim : Module.supportDim A (ULift.{v} (A ⧸ p.asIdeal ^ n)) = (e : WithBot ℕ∞) :=
    supportDim_ulift_quotient_pow p e n hn hdim
  have hsub : Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A (ULift.{v} (A ⧸ p.asIdeal ^ n)))) K i) := by
    rw [← not_nontrivial_iff_subsingleton]
    intro hnt
    exact absurd (ext_degree_mem_Icc_of_nontrivial K hK e hBdim i hnt).1 (by omega)
  rw [Module.notMem_support_iff']
  intro m
  refine ⟨s, hsp, ?_⟩
  exact smul_eq_zero_of_linearEquiv (extFromUliftRing K i) s
    (smul_extFromUliftRing_eq_zero K (p.asIdeal ^ n) s hs i hsub) m

/-! ### Nilpotence of a scalar acting trivially on cohomology -/

/-- An object concentrated in a single degree on which `s` acts as zero on cohomology has
`s • 𝟙 = 0`. -/
private lemma smul_id_eq_zero_of_single {A : Type u} [CommRing A] (s : A)
    (X : DerivedCategory (ModuleCat.{max v u} A)) (a : ℤ) (hGE : X.IsGE a) (hLE : X.IsLE a)
    (h : ∀ m : (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) a).obj X, s • m = 0) :
    s • 𝟙 X = 0 := by
  let : X.IsGE a := hGE
  let : X.IsLE a := hLE
  obtain ⟨e⟩ := DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor X a
  have hM : s • 𝟙 ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) a).obj X) = 0 :=
    ModuleCat.hom_ext (LinearMap.ext fun m => h m)
  have hS : s • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) a).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) a).obj X)) = 0 := by
    rw [← (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) a).map_id, ← Functor.map_smul,
      hM, Functor.map_zero]
  calc s • 𝟙 X = s • (e.hom ≫ e.inv) := by rw [e.hom_inv_id]
    _ = e.hom ≫ (s • 𝟙 _) ≫ e.inv := by
        rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul]
    _ = 0 := by rw [hS, Limits.zero_comp, Limits.comp_zero]

/-- A scalar acting as zero on every cohomology module of a bounded object acts nilpotently on
the object itself: the exponent is the length of the interval carrying the cohomology. The
induction is along the canonical truncation triangle. -/
private lemma smul_pow_id_eq_zero {A : Type u} [CommRing A] (s : A) :
    ∀ (k : ℕ) (X : DerivedCategory (ModuleCat.{max v u} A)) (a b : ℤ),
      b ≤ a + k → X.IsGE a → X.IsLE b →
      (∀ (i : ℤ) (m : (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj X),
          s • m = 0) →
      s ^ (k + 1) • 𝟙 X = 0 := by
  intro k
  induction k with
  | zero =>
      intro X a b hb hGE hLE hs
      let : X.IsLE b := hLE
      have hLE' : X.IsLE a := DerivedCategory.TStructure.t.isLE_of_le X b a (by omega)
      simpa using smul_id_eq_zero_of_single s X a hGE hLE' (hs a)
  | succ k ih =>
      intro X a b hb hGE hLE hs
      let : X.IsGE a := hGE
      let : X.IsLE b := hLE
      by_cases hba : b ≤ a
      · have hLE' : X.IsLE a := DerivedCategory.TStructure.t.isLE_of_le X b a hba
        rw [pow_succ s (k + 1), ← smul_smul, smul_id_eq_zero_of_single s X a hGE hLE' (hs a),
          smul_zero]
      · rw [not_le] at hba
        let Y₁ := (DerivedCategory.TStructure.t.truncLT b).obj X
        let Y₃ := (DerivedCategory.TStructure.t.truncGE b).obj X
        let ι : Y₁ ⟶ X := (DerivedCategory.TStructure.t.truncLTι b).app X
        let π : X ⟶ Y₃ := (DerivedCategory.TStructure.t.truncGEπ b).app X
        let δ : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧ := (DerivedCategory.TStructure.t.truncGEδLT b).app X
        have hT : Triangle.mk ι π δ ∈ distTriang (DerivedCategory (ModuleCat.{max v u} A)) :=
          DerivedCategory.TStructure.t.triangleLTGE_distinguished b X
        have hepi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) b).map π) := by
          refine (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT b (b + 1)
            rfl).2 ?_
          exact (DerivedCategory.isZero_of_isLE Y₁ (b - 1) (b + 1) (by omega)).eq_of_tgt _ _
        have hY3 : ∀ m : (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) b).obj Y₃,
            s • m = 0 := by
          intro m
          obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective _).mp hepi m
          rw [← map_smul, hs b x, map_zero]
        have hid3 : s • 𝟙 Y₃ = 0 :=
          smul_id_eq_zero_of_single s Y₃ b inferInstance inferInstance hY3
        have hY1 : ∀ (i : ℤ) (m : (DerivedCategory.homologyFunctor
            (ModuleCat.{max v u} A) i).obj Y₁), s • m = 0 := by
          intro i m
          by_cases hi : i ≤ b - 1
          · have hmono : Mono ((DerivedCategory.homologyFunctor
                (ModuleCat.{max v u} A) i).map ι) := by
              refine (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT (i - 1) i
                (by omega)).2 ?_
              exact (DerivedCategory.isZero_of_isGE Y₃ b (i - 1) (by omega)).eq_of_src _ _
            refine (ModuleCat.mono_iff_injective _).mp hmono ?_
            rw [map_smul, hs i _, map_zero]
          · exact smul_homology_eq_zero_of_isZero s
              (DerivedCategory.isZero_of_isLE Y₁ (b - 1) i (by omega)) m
        have hih : s ^ (k + 1) • 𝟙 Y₁ = 0 :=
          ih Y₁ a (b - 1) (by omega) inferInstance inferInstance hY1
        have hsp : (s • 𝟙 X) ≫ π = 0 := by
          have h2 : π ≫ (s • 𝟙 Y₃) = s • π := by rw [Linear.comp_smul, Category.comp_id]
          rw [smul_id_comp, ← h2, hid3, Limits.comp_zero]
        obtain ⟨g, hg₀⟩ := Triangle.coyoneda_exact₂ _ hT (s • 𝟙 X) hsp
        have hg : s • 𝟙 X = (g : X ⟶ Y₁) ≫ ι := hg₀
        have key : s ^ (k + 1 + 1) • 𝟙 X = (s • 𝟙 X) ≫ (s ^ (k + 1) • 𝟙 X) := by
          rw [smul_id_comp, smul_smul, ← pow_succ']
        have hiota : (s ^ (k + 1) : A) • ι = 0 := by
          rw [← smul_id_comp, hih, Limits.zero_comp]
        rw [key, hg, Category.assoc, Linear.comp_smul, Category.comp_id, hiota,
          Limits.comp_zero]

/-! ### Derived endomorphisms of a dualizing complex -/

/-- **The derived endomorphisms of a dualizing complex are the ring.** The degree-zero `Ext`
module of `K` into itself is `A`, universe-lifted: this is the Ext--cohomology comparison
followed by biduality of [Stacks, Tag 0A7C]. -/
private noncomputable def extSelfLinearEquivUliftRing (A : Type u) [CommRing A]
    [IsNoetherianRing A] (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsDualizingComplex K) :
    (K ⟶ (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (0 : ℤ)).obj K)
      ≃ₗ[A] ULift.{v} A :=
  let e₁ : (K ⟶ (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max v u} A))
        (0 : ℤ)).obj K) ≃ₗ[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0).obj
        ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A).hom.obj (Opposite.op K, K))) :=
    extDerivedHomLinearEquiv.{u, v} A K 0 K
  let e₂ : ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0).obj
        ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A).hom.obj (Opposite.op K, K)))
      ≃ₗ[A] ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A (ULift.{v} A)))) :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0).mapIso
      (dualizingDerivedHomSelfIsoRing.{u, v} A hK)).toLinearEquiv
  let e₃ : ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A (ULift.{v} A)))) ≃ₗ[A] ULift.{v} A :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{max v u} A) 0).app (ModuleCat.of A (ULift.{v} A))).toLinearEquiv
  (e₁.trans e₂).trans e₃

/-- **A dualizing complex has full support.** Every prime of `A` lies in the support of some
cohomology module of a dualizing complex: otherwise some element outside the prime would kill
all of them, hence act nilpotently on `K`, hence vanish in `A`. -/
private lemma exists_mem_support_homology {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (hK : IsDualizingComplex K)
    (p : PrimeSpectrum A) :
    ∃ j : ℤ, p ∈ Module.support A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) j).obj K) := by
  by_contra hcon
  rw [not_exists] at hcon
  obtain ⟨a, b, I, hIGE, hILE, hinj, ⟨e⟩⟩ := hK.finiteInjectiveDimension
  have hKGE : K.IsGE a := DerivedCategory.TStructure.t.isGE_of_iso e.symm a
  have hKLE : K.IsLE b := DerivedCategory.TStructure.t.isLE_of_iso e.symm b
  have hwit : ∀ j : ℤ, ∃ t : A, t ∉ p.asIdeal ∧
      ∀ m : (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) j).obj K, t • m = 0 := by
    intro j
    have : Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) j).obj K) :=
      hK.finiteCohomology j
    have hnotle : ¬ (Module.annihilator A
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) j).obj K) ≤ p.asIdeal) :=
      fun h => hcon j (Module.mem_support_iff_of_finite.2 h)
    obtain ⟨t, ht, htp⟩ := SetLike.not_le_iff_exists.mp hnotle
    exact ⟨t, htp, Module.mem_annihilator.mp ht⟩
  choose t htp hts using hwit
  set s := ∏ j ∈ Finset.Icc a b, t j with hsdef
  have hsp : s ∉ p.asIdeal := p.asIdeal.primeCompl.prod_mem (fun j _ => htp j)
  have hskill : ∀ (j : ℤ) (m : (DerivedCategory.homologyFunctor
      (ModuleCat.{max v u} A) j).obj K), s • m = 0 := by
    intro j m
    by_cases hj : j ∈ Finset.Icc a b
    · obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem t hj
      rw [hsdef, hd, mul_comm (t j) d, mul_smul, hts j m, smul_zero]
    · rw [Finset.mem_Icc] at hj
      refine smul_homology_eq_zero_of_isZero s ?_ m
      rcases not_and_or.mp hj with h | h
      · exact DerivedCategory.isZero_of_isGE K a j (by omega)
      · exact DerivedCategory.isZero_of_isLE K b j (by omega)
  have hnil : s ^ ((b - a).toNat + 1) • 𝟙 K = 0 :=
    smul_pow_id_eq_zero s (b - a).toNat K a b (by omega) hKGE hKLE hskill
  -- the scalar kills the degree-zero self-Ext module, which is the ring
  have hkill : ∀ φ : K ⟶ (CategoryTheory.shiftFunctor
      (DerivedCategory (ModuleCat.{max v u} A)) (0 : ℤ)).obj K,
      (s ^ ((b - a).toNat + 1)) • φ = 0 := by
    intro φ
    rw [← smul_id_comp, hnil, Limits.zero_comp]
  have hone := smul_eq_zero_of_linearEquiv (extSelfLinearEquivUliftRing A K hK) _ hkill
    (ULift.up (1 : A))
  have hzero : s ^ ((b - a).toNat + 1) = 0 := by simpa using congrArg ULift.down hone
  exact hsp (p.isPrime.mem_of_pow_mem ((b - a).toNat + 1) (hzero ▸ p.asIdeal.zero_mem))

/-! ### The main result -/

/-- **Stacks Project, Tag 0A7V.** Let `A` be a Noetherian local ring with a normalized dualizing
complex `K`, and let `p` be a minimal prime of `A` with `dim(A/p) = e`. Then the localization at
`p` of the cohomology module `H^i(K)` is nonzero if and only if `i = -e`. -/
@[stacks 0A7V]
theorem nontrivial_localized_homology_iff_eq_neg_dimension
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K)
    (p : PrimeSpectrum A) (hp : IsMinimalPrime p.asIdeal) (e : ℕ)
    (hdim : ringKrullDim (A ⧸ p.asIdeal) = (e : WithBot ℕ∞)) (i : ℤ) :
    Nontrivial (LocalizedModule p.asIdeal.primeCompl
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K)) ↔
      i = -(e : ℤ) := by
  have hout : ∀ j : ℤ, j ≠ -(e : ℤ) → p ∉ Module.support A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) j).obj K) := by
    intro j hj
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · exact notMem_support_homology_of_lt K hK p hp e hdim j hlt
    · exact fun hmem => absurd (le_neg_of_mem_support_homology K hK p e hdim j hmem) (by omega)
  refine ⟨fun hmem => by_contra fun hj => hout i hj hmem, ?_⟩
  rintro rfl
  obtain ⟨j, hj⟩ := exists_mem_support_homology K hK.1 p
  obtain rfl : j = -(e : ℤ) := by_contra fun hje => hout j hje hj
  exact hj

/-! ### The global statement at a minimal prime -/

/-- **Stacks Project, Tag 0A7X.** Let `A` be a Noetherian ring with a dualizing complex `K` and
let `p` be a minimal prime of `A`. Then the localization at `p` of the cohomology module `H^i(K)`
is nonzero for exactly one `i`. -/
@[stacks 0A7X]
theorem existsUnique_nontrivial_localized_homology
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDualizingComplex K)
    (p : Ideal A) [p.IsPrime] (hp : p ∈ minimalPrimes A) :
    ∃! i : ℤ, Nontrivial
      (LocalizedModule p.primeCompl
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K)) := by
  classical
  let B := Localization p.primeCompl
  have : IsLocalRing B := Localization.AtPrime.isLocalRing p
  let Kloc : DerivedCategory (ModuleCat.{max v u} B) :=
    (StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap A B)).obj K
  have hKloc : IsDualizingComplex Kloc := isDualizingComplex_localization p.primeCompl K hK
  have hdim : ringKrullDim B = 0 := by
    simpa [(Ideal.height_eq_zero_iff).2 hp] using
      IsLocalization.AtPrime.ringKrullDim_eq_height p B
  let κ : ModuleCat.{max v u} B :=
    (ModuleCat.uliftFunctor.{v} B).obj (ModuleCat.of B (IsLocalRing.ResidueField B))
  obtain ⟨E, i, hiMono, hiHull⟩ := Module.exists_isInjectiveHull B κ
  have : Mono i := hiMono
  obtain ⟨n, ⟨e⟩⟩ := exists_shift_iso_single_injectiveHull_of_ringKrullDim_eq_zero
    Kloc hKloc hdim E i hiHull
  let H := fun j : ℤ => DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) j
  have hE : Nontrivial E := by
    have hi : Function.Injective i := (ModuleCat.mono_iff_injective i).mp hiMono
    have hneq : (0 : κ) ≠ ULift.up (1 : IsLocalRing.ResidueField B) :=
      fun h => zero_ne_one (congrArg ULift.down h)
    exact nontrivial_of_ne (i 0) (i (ULift.up (1 : IsLocalRing.ResidueField B)))
      fun hmap => hneq (hi hmap)
  have hsingle : ∀ j : ℤ,
      Nontrivial ((H j).obj ((DerivedCategory.singleFunctor
        (ModuleCat.{max v u} B) 0).obj E)) ↔ j = 0 := by
    intro j
    by_cases hj : j = 0
    · subst j
      refine ⟨fun _ => rfl, fun _ => ?_⟩
      exact ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max v u} B) 0).app E).toLinearEquiv.toEquiv.nontrivial_congr.2 hE
    · have hz : IsZero ((H j).obj ((DerivedCategory.singleFunctor
          (ModuleCat.{max v u} B) 0).obj E)) := by
        rcases lt_or_gt_of_ne hj with hlt | hgt
        · exact DerivedCategory.isZero_of_isGE _ 0 j hlt
        · exact DerivedCategory.isZero_of_isLE _ 0 j hgt
      refine ⟨fun h => ?_, fun h => (hj h).elim⟩
      obtain ⟨x, y, hxy⟩ := h
      have : Subsingleton ((H j).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) 0).obj E)) :=
        ModuleCat.isZero_iff_subsingleton.mp hz
      exact absurd (Subsingleton.elim x y) hxy
  have hlocalized (j : ℤ) :
      Nontrivial (LocalizedModule p.primeCompl
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) j).obj K)) ↔
      Nontrivial ((H j).obj Kloc) := by
    let U := ModuleCat.uliftFunctor.{u, v} A
    let Kbig := U.mapDerivedCategory.obj K
    let eHom := (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso U j).app K
    let eLoc :=
      (CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso.{u, u, v}
        p.primeCompl (A := B) j).app Kbig
    let eLift := (CochainComplex.DerivedTensor.localizedModuleFunctor.{u, max v u}
      p.primeCompl).mapIso eHom
    let eULift := localizedModuleUliftIso (R := A) (S := p.primeCompl)
      (M := ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) j).obj K))
    have e : (ModuleCat.restrictScalars (algebraMap A B)).obj ((H j).obj Kloc) ≅
        ModuleCat.of A (LocalizedModule p.primeCompl
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) j).obj K)) := by
      show (ModuleCat.restrictScalars (algebraMap A B)).obj
          ((H j).obj
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
              (algebraMap A B)).functor.obj Kbig)) ≅ _
      exact eLoc ≪≫ eLift ≪≫ eULift
    exact e.toLinearEquiv.toEquiv.nontrivial_congr.symm
  have hdegree (j : ℤ) : Nontrivial ((H j).obj Kloc) ↔ n + j = 0 := by
    let eH : (H j).obj Kloc ≅ (H (n + j)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) 0).obj E) :=
      (H j).mapIso e ≪≫ ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) 0).shiftIso
        n j (n + j) rfl).app ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) 0).obj E)
    exact eH.toLinearEquiv.toEquiv.nontrivial_congr.trans
      (hsingle (n + j))
  refine ⟨-n, (hlocalized (-n)).2 ((hdegree (-n)).2 (by omega)), ?_⟩
  intro j hj
  have hzero : n + j = 0 := (hdegree j).1 ((hlocalized j).mp hj)
  omega

end Dualizing
