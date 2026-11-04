module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Ideal
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.Supported
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteProjective
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
public import StacksCore.Tactic.StacksAttribute

/-!
# Annihilating local cohomology

Let `J ⊆ I` be ideals of a commutative ring `A`, with `I` finitely generated, and let
`Z = V(I)`. If `J ^ n` annihilates `H^i_Z(A)` then, for every finitely presented `A`-module
`M` whose localization `M_f` is a finite locally free `A_f`-module for every `f ∈ I`, some
power of `J` annihilates `H^i_Z(M)`.

The argument is the one of the source. Over a free module of finite rank the hypothesis
transfers at once, because `H^i_Z(-)` is an `A`-linear additive functor and a finite free
module is a finite biproduct of copies of `A`. For a general `M` and an `f ∈ I`, finite local
freeness of `M_f` produces maps `a : A^{⊕d} → M` and `b : M → A^{⊕d}` with `a ∘ b = f^k`;
applying `H^i_Z(-)` shows that `f ^ k` lies in the colon ideal `(ann H^i_Z(M) : J ^ n)`. Thus
`I` is contained in the radical of that colon ideal, and finite generation of `I` turns this
into an inclusion `I ^ m ⊆ (ann H^i_Z(M) : J ^ n)`, whence `J ^ (m + n)` annihilates `H^i_Z(M)`.

## Main results

* `Stacks.LocalCohomology.exists_pow_smul_localCohomology_eq_bot` — **Stacks 0BPX**, the
  transfer of power-torsion from the local cohomology of the ring to that of such a module.

## Implementation notes

The closed subset `V(I)` is `PrimeSpectrum.zeroLocus I`, and local cohomology in degree `i` is
`Stacks.LocalCohomology.localCohomologyWithSupportIn` applied to the module placed in degree
zero. "The ideal `J ^ n` annihilates `N`" is expressed as `J ^ n • (⊤ : Submodule A N) = ⊥`.

The `A`-linearity and triangulatedness of derived sections with support, which the source uses
implicitly, are the instances already available for
`Stacks.LocalCohomology.derivedSectionsWithSupportIn`; only the additive-functor computation on
a finite free module is carried out here. The source assumes both `I` and `J` finitely
generated, but its proof uses finite generation of `I` only, so no hypothesis on `J` is imposed.

## References

* [Stacks Project, Tag 0BPX](https://stacks.math.columbia.edu/tag/0BPX)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A]

/-- Degree-`i` local cohomology with support in `T`, as a functor on `A`-modules: place the
module in degree zero, apply derived sections with support in `T`, take the `i`-th homology. -/
private noncomputable abbrev supportedLocalCohomologyFunctor
    (T : Set (PrimeSpectrum A)) (i : ℤ) : ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
    derivedSectionsWithSupportIn.{u, 0} A T ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) i

/-- A scalar acts as zero on a module object exactly when `a • 𝟙 M = 0`. -/
private lemma smul_id_eq_zero_iff_mem_annihilator {A : Type u} [CommRing A] {M : ModuleCat.{u} A}
    (a : A) : a • 𝟙 M = 0 ↔ a ∈ Module.annihilator A M := by
  refine ⟨fun h => Module.mem_annihilator.mpr fun z => ?_, fun h => ?_⟩
  · simpa only [ModuleCat.hom_smul, ModuleCat.hom_id, ModuleCat.hom_zero, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq, LinearMap.zero_apply] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) z
  · exact ModuleCat.hom_ext (LinearMap.ext fun x => Module.mem_annihilator.mp h x)

/-- If `J ^ n` annihilates `H^i_T(A)`, it annihilates `H^i_T(A^{⊕d})` for every `d`: the
identity of a finite free module is the sum of the idempotents `e j ∘ p j`, and the `A`-linear
additive functor `H^i_T(-)` turns multiplication by `a ∈ J ^ n` on `A^{⊕d}` into a sum of maps
factoring through multiplication by `a` on `H^i_T(A)`, which is zero. -/
private lemma localCohomology_finiteFree_annihilator (J : Ideal A) (n : ℕ)
    (T : Set (PrimeSpectrum A)) (i : ℤ)
    (hA : J ^ n • (⊤ : Submodule A
      (localCohomologyWithSupportIn.{u, 0} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A A)) i)) = ⊥)
    (d : ℕ) :
    J ^ n ≤ Module.annihilator A
      (localCohomologyWithSupportIn.{u, 0} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (Fin d →₀ A))) i) := by
  let H := supportedLocalCohomologyFunctor A T i
  let F : ModuleCat.{u} A := ModuleCat.of A (Fin d →₀ A)
  let X : ModuleCat.{u} A := ModuleCat.of A A
  have hAann : J ^ n ≤ Module.annihilator A (H.obj X) := by
    change J ^ n ≤ Module.annihilator A
      (localCohomologyWithSupportIn.{u, 0} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj X) i)
    rw [← Submodule.annihilator_top]
    exact Submodule.le_annihilator_iff.mpr hA
  have hscalar (a : A) (ha : a ∈ J ^ n) : a • 𝟙 (H.obj X) = 0 :=
    (smul_id_eq_zero_iff_mem_annihilator a).mpr (hAann ha)
  let e (j : Fin d) : A →ₗ[A] (Fin d →₀ A) := Finsupp.lsingle j
  let p (j : Fin d) : (Fin d →₀ A) →ₗ[A] A := Finsupp.lapply j
  have hid : (∑ j : Fin d, (e j).comp (p j)) = LinearMap.id := by
    ext x j
    simp [e, p]
  have hdecomp : (∑ j : Fin d, ModuleCat.ofHom (p j) ≫ ModuleCat.ofHom (e j)) = 𝟙 F := by
    apply (ModuleCat.homAddEquiv (M := F) (N := F)).injective
    rw [map_sum]
    simpa [ModuleCat.homAddEquiv, ModuleCat.homEquiv, ModuleCat.hom_comp,
      ModuleCat.hom_id, e, p] using hid
  have hzero (a : A) (ha : a ∈ J ^ n) : a • (𝟙 (H.obj F)) = 0 := by
    calc
      a • (𝟙 (H.obj F)) = H.map (a • (𝟙 F)) := by
        rw [Functor.map_smul, H.map_id]
      _ = H.map (a • (∑ j : Fin d, ModuleCat.ofHom (p j) ≫ ModuleCat.ofHom (e j))) := by
        rw [← hdecomp]
      _ = ∑ j : Fin d, H.map (a • (ModuleCat.ofHom (p j) ≫ ModuleCat.ofHom (e j))) := by
        simp only [Functor.map_sum, Finset.smul_sum]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [Functor.map_smul, Functor.map_comp, ← Linear.smul_comp,
          show a • H.map (ModuleCat.ofHom (p j)) =
              H.map (ModuleCat.ofHom (p j)) ≫ (a • 𝟙 (H.obj X)) by
            rw [Linear.comp_smul, Category.comp_id],
          hscalar a ha]
        simp
  change J ^ n ≤ Module.annihilator A (H.obj F)
  exact fun a ha => (smul_id_eq_zero_iff_mem_annihilator a).mp (hzero a ha)

/-- A finite locally free module is projective: a covering family witnessing finite local
freeness is exactly condition (7) of `Module.finite_projective_tfae`. -/
private lemma finiteLocallyFree_projective (R : Type u) [CommRing R] (M : Type u)
    [AddCommGroup M] [Module R M] (h : Module.IsFiniteLocallyFree R M) :
    Module.Projective R M := by
  obtain ⟨ι, f, hcover, hfree⟩ := h
  have hp : Module.Finite R M ∧ Module.Projective R M := by
    apply ((Module.finite_projective_tfae R M).out 7 2).mp
    refine ⟨Set.range f, ?_, ?_⟩
    · simpa using hcover
    · rintro _ ⟨i, rfl⟩
      exact hfree i
  exact hp.2

/-- If `M` is finitely presented and `M_f` is a finite locally free `A_f`-module, then a power
of `f` on `M` factors through a finite free module: a splitting of a presentation of `M_f`,
available because `M_f` is projective, is lifted to `A` by clearing denominators. -/
private lemma exists_pow_id_factors_through_finiteFree (M : Type u) [AddCommGroup M]
    [Module A M] (hFP : Module.FinitePresentation A M) (f : A)
    (hM : Module.IsFiniteLocallyFree (Localization.Away f) (LocalizedModule.Away f M)) :
    ∃ (k d : ℕ) (a : (Fin d → A) →ₗ[A] M) (b : M →ₗ[A] (Fin d → A)),
      a.comp b = f ^ k • LinearMap.id := by
  let S := Submonoid.powers f
  let B := Localization.Away f
  obtain ⟨n, r, π, δ, hπ, hδ⟩ := Module.FinitePresentation.exists_fin' A M
  let F := Fin n → A
  let fF : F →ₗ[A] LocalizedModule.Away f F := LocalizedModule.mkLinearMap S F
  let fM : M →ₗ[A] LocalizedModule.Away f M := LocalizedModule.mkLinearMap S M
  let ρ := IsLocalizedModule.map S fF fM π
  have hρ : Function.Surjective ρ := IsLocalizedModule.map_surjective S fF fM π hπ
  let ρB := ρ.extendScalarsOfIsLocalization S B
  have : Module.Projective B (LocalizedModule.Away f M) :=
    finiteLocallyFree_projective B (LocalizedModule.Away f M) hM
  obtain ⟨sB, hsB⟩ := Module.projective_lifting_property ρB LinearMap.id hρ
  let sA := sB.restrictScalars A
  have hsA : ρ.comp sA = LinearMap.id := by
    ext x
    change ρB (sB x) = x
    exact congrArg (fun g : LocalizedModule.Away f M →ₗ[B] LocalizedModule.Away f M => g x) hsB
  obtain ⟨b, t, hb⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    S fF (sA.comp fM)
  change fF.comp b = t.1 • (sA.comp fM) at hb
  have hmap : ρ.comp fF = fM.comp π := IsLocalizedModule.map_comp S fF fM π
  have hlocal : fM.comp (π.comp b) = fM.comp (t.1 • LinearMap.id) := by
    calc
      fM.comp (π.comp b) = ρ.comp (fF.comp b) := by
        rw [← LinearMap.comp_assoc, ← hmap, LinearMap.comp_assoc]
      _ = ρ.comp (t.1 • (sA.comp fM)) := by rw [hb]
      _ = t.1 • ((ρ.comp sA).comp fM) := by
        rw [LinearMap.comp_smul, LinearMap.comp_assoc]
      _ = t.1 • fM := by rw [hsA, LinearMap.id_comp]
      _ = fM.comp (t.1 • LinearMap.id) := by
        simp [LinearMap.comp_smul]
  obtain ⟨t', ht'⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    S fM (π.comp b) (t.1 • LinearMap.id) hlocal
  let a := t'.1 • π
  have hfactor : a.comp b = (t'.1 * t.1) • LinearMap.id := by
    ext x
    have hx := congrArg (fun q : M →ₗ[A] M => q x) ht'
    change (t'.1 • π) (b x) = ((t'.1 * t.1) • LinearMap.id) x
    simpa [Submonoid.smul_def, smul_smul] using hx
  obtain ⟨k, hk⟩ :=
    (Submonoid.mem_powers_iff (t'.1 * t.1) f).mp (S.mul_mem t'.property t.property)
  exact ⟨k, n, a, b, by simpa [hk] using hfactor⟩

/-- For `f ∈ I`, some power of `f` lies in the colon ideal `(ann H^i_T(M) : J ^ n)`. Multiply
the factorization `a ∘ b = f ^ k` of a power of `f` through a finite free module by `y ∈ J ^ n`
and apply `H^i_T(-)`: the middle map becomes zero by the finite free case, so multiplication by
`f ^ k * y` is zero on `H^i_T(M)`. -/
private lemma localCohomology_annihilator_colon (J : Ideal A) (n : ℕ)
    (T : Set (PrimeSpectrum A)) (i : ℤ)
    (hA : J ^ n • (⊤ : Submodule A
      (localCohomologyWithSupportIn.{u, 0} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A A)) i)) = ⊥)
    (M : ModuleCat.{u} A) (hFP : Module.FinitePresentation A M) (f : A)
    (hM : Module.IsFiniteLocallyFree (Localization.Away f) (LocalizedModule.Away f M)) :
    ∃ k : ℕ, f ^ k ∈ Submodule.colon (Module.annihilator A
      (localCohomologyWithSupportIn.{u, 0} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) i))
      (J ^ n : Ideal A) := by
  obtain ⟨k, d, a, b, hfactor⟩ := exists_pow_id_factors_through_finiteFree A M hFP f hM
  let e : (Fin d →₀ A) ≃ₗ[A] (Fin d → A) := Finsupp.linearEquivFunOnFinite A A (Fin d)
  let a' : (Fin d →₀ A) →ₗ[A] M := a.comp e.toLinearMap
  let b' : M →ₗ[A] (Fin d →₀ A) := e.symm.toLinearMap.comp b
  have hfactor' : a'.comp b' = f ^ k • LinearMap.id := by
    ext x
    change a (e (e.symm (b x))) = (f ^ k • LinearMap.id) x
    calc
      a (e (e.symm (b x))) = a (b x) := by simp
      _ = (f ^ k • LinearMap.id) x := by
        simpa [LinearMap.comp_apply] using congrArg (fun q : M →ₗ[A] M => q x) hfactor
  let H := supportedLocalCohomologyFunctor A T i
  let F : ModuleCat.{u} A := ModuleCat.of A (Fin d →₀ A)
  refine ⟨k, ?_⟩
  rw [Submodule.mem_colon]
  intro y hy
  have hkill :
      H.map (ModuleCat.ofHom (y • (LinearMap.id : (Fin d →₀ A) →ₗ[A] (Fin d →₀ A)))) = 0 := by
    rw [show ModuleCat.ofHom (y • (LinearMap.id : (Fin d →₀ A) →ₗ[A] (Fin d →₀ A))) =
        y • (𝟙 F) from rfl, Functor.map_smul, H.map_id]
    exact (smul_id_eq_zero_iff_mem_annihilator y).mpr
      (localCohomology_finiteFree_annihilator A J n T i hA d hy)
  have hfactorY : a'.comp ((y • (LinearMap.id : (Fin d →₀ A) →ₗ[A] (Fin d →₀ A))).comp b') =
      (f ^ k * y) • LinearMap.id := by
    ext x
    change a' (y • b' x) = (f ^ k * y) • x
    calc
      a' (y • b' x) = y • a' (b' x) := by simp
      _ = y • ((a'.comp b') x) := rfl
      _ = y • ((f ^ k • LinearMap.id) x) := by rw [hfactor']
      _ = (f ^ k * y) • x := by simp [smul_smul, mul_comm]
  have hcat : ModuleCat.ofHom b' ≫
      ModuleCat.ofHom (y • (LinearMap.id : (Fin d →₀ A) →ₗ[A] (Fin d →₀ A))) ≫ ModuleCat.ofHom a' =
      ModuleCat.ofHom ((f ^ k * y) • (LinearMap.id : M →ₗ[A] M)) := by
    apply ModuleCat.hom_ext
    simpa [ModuleCat.hom_comp, ← LinearMap.comp_assoc] using hfactorY
  have hmapcat := congrArg H.map hcat
  rw [Functor.map_comp, Functor.map_comp] at hmapcat
  have hzero : H.map (ModuleCat.ofHom ((f ^ k * y) • (LinearMap.id : M →ₗ[A] M))) = 0 := by
    rw [← hmapcat]
    simp [hkill]
  have hsmul : (f ^ k * y) • (𝟙 (H.obj M)) = 0 := by
    have hzero' : H.map ((f ^ k * y) • 𝟙 M) = 0 := hzero
    rwa [Functor.map_smul, H.map_id] at hzero'
  exact (smul_id_eq_zero_iff_mem_annihilator _).mp hsmul

/-- **Stacks 0BPX.** If a power of `J` annihilates the `i`-th local cohomology of `A` supported
on `V(I)`, then a power of `J` annihilates the corresponding local cohomology of every finitely
presented `A`-module which is finite locally free after localization at every element of `I`. -/
@[stacks 0BPX]
theorem exists_pow_smul_localCohomology_eq_bot (J I : Ideal A) (hJI : J ≤ I) (hI : I.FG) (i : ℕ)
    (hA : ∃ n : ℕ,
      J ^ n • (⊤ : Submodule A
        (localCohomologyWithSupportIn.{u, 0} A (PrimeSpectrum.zeroLocus (I : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A A)) (i : ℤ))) = ⊥) :
    ∀ (M : ModuleCat.{u} A), Module.FinitePresentation A M →
      (∀ f ∈ I, Module.IsFiniteLocallyFree (Localization.Away f) (LocalizedModule.Away f M)) →
      ∃ m : ℕ,
        J ^ m • (⊤ : Submodule A
          (localCohomologyWithSupportIn.{u, 0} A (PrimeSpectrum.zeroLocus (I : Set A))
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (i : ℤ))) = ⊥ := by
  intro M hFP hLoc
  obtain ⟨n, hAeq⟩ := hA
  let T := PrimeSpectrum.zeroLocus (I : Set A)
  let Hmod := localCohomologyWithSupportIn.{u, 0} A T
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (i : ℤ)
  let N : Ideal A := Module.annihilator A Hmod
  let K : Ideal A := Submodule.colon N (J ^ n : Ideal A)
  have hIrad : I ≤ K.radical := fun f hf =>
    Ideal.mem_radical_iff.mpr (localCohomology_annihilator_colon A J n T i hAeq M hFP f (hLoc f hf))
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIrad hI
  have hJpow : J ^ m ≤ K := (Ideal.pow_right_mono hJI m).trans hm
  have hprod : J ^ (m + n) ≤ N := by
    rw [pow_add]
    exact Ideal.mul_le.mpr fun x hx y hy => by
      simpa [smul_eq_mul] using Submodule.mem_colon.mp (hJpow hx) y hy
  refine ⟨m + n, ?_⟩
  change J ^ (m + n) • (⊤ : Submodule A Hmod) = ⊥
  apply Submodule.le_annihilator_iff.mp
  rwa [Submodule.annihilator_top]

end Stacks.LocalCohomology
