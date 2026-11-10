module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Homotopy
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Pure.Defs
public import StacksFrontier.Algebra.Module.Pure.Injective
public import StacksFrontier.RingTheory.Flat.UniversallyInjective

/-!
# Pure injective resolutions

A *pure injective resolution* of a module is a cochain complex of pure injective modules,
universally exact and augmented under the module.  This file proves existence, the comparison
map from any universally exact resolution, and uniqueness of the comparison map up to
homotopy.

## References

* [Stacks Project, Tag 0702](https://stacks.math.columbia.edu/tag/0702)
* [Stacks Project, Tag 0704](https://stacks.math.columbia.edu/tag/0704)
-/

@[expose] public section

namespace Module.PureInjectiveResolution

section

universe u v


variable {A : Type u} [CommRing A]

/-- An augmentation `M ⟶ I⁰` of a cochain complex is a *pure injective resolution* if
`0 ⟶ M ⟶ I⁰ ⟶ I¹ ⟶ ⋯` is universally exact and every `Iⁱ` is pure injective. -/
@[stacks 0702 "pure_injective_resolution"] public structure IsPureInjectiveResolution
    {M : Type v} [AddCommGroup M] [Module A M]
    (I : CochainComplex (ModuleCat.{v} A) ℕ) (augmentation : M →ₗ[A] I.X 0) : Prop where
  /-- Exactness at the initial module: the augmentation is injective. -/
  injective_augmentation : Function.Injective augmentation
  /-- The augmentation stays injective after tensoring with every module. -/
  universallyInjective_augmentation : UniversallyInjective augmentation
  /-- The augmented complex is exact at degree zero. -/
  exact_zero : Function.Exact augmentation (I.d 0 1)
  /-- Exactness at degree zero is preserved by tensoring with every module. -/
  baseChange_exact_zero : ∀ (Q : Type v) [AddCommGroup Q] [Module A Q],
    Function.Exact (augmentation.rTensor Q) ((I.d 0 1).hom.rTensor Q)
  /-- The complex is exact between every three consecutive terms. -/
  exact : ∀ i : ℕ, Function.Exact (I.d i (i + 1)) (I.d (i + 1) (i + 2))
  /-- Exactness between consecutive terms is preserved by tensoring with every module. -/
  baseChange_exact : ∀ (Q : Type v) [AddCommGroup Q] [Module A Q] (i : ℕ),
    Function.Exact ((I.d i (i + 1)).hom.rTensor Q) ((I.d (i + 1) (i + 2)).hom.rTensor Q)
  /-- Every term of the resolution is pure injective. -/
  pureInjective : ∀ i : ℕ, Module.PureInjective A (I.X i)

end

section

universe u v


variable {A : Type u} [CommRing A]

/-- A universally exact augmented cochain resolution of a module. -/
public structure IsUniversallyExactResolution
    {M : Type v} [AddCommGroup M] [Module A M]
    (C : CochainComplex (ModuleCat.{v} A) ℕ) (augmentation : M →ₗ[A] C.X 0) : Prop where
  /-- The augmentation is injective. -/
  injective_augmentation : Function.Injective augmentation
  /-- The augmentation stays injective after tensoring with every module. -/
  universallyInjective_augmentation : UniversallyInjective augmentation
  /-- The augmented complex is exact at degree zero. -/
  exact_zero : Function.Exact augmentation (C.d 0 1)
  /-- Exactness at degree zero is preserved by tensoring with every module. -/
  baseChange_exact_zero : ∀ (Q : Type v) [AddCommGroup Q] [Module A Q],
    Function.Exact (augmentation.rTensor Q) ((C.d 0 1).hom.rTensor Q)
  /-- The complex is exact between every three consecutive terms. -/
  exact : ∀ i : ℕ, Function.Exact (C.d i (i + 1)) (C.d (i + 1) (i + 2))
  /-- Exactness between consecutive terms is preserved by tensoring with every module. -/
  baseChange_exact : ∀ (Q : Type v) [AddCommGroup Q] [Module A Q] (i : ℕ),
    Function.Exact ((C.d i (i + 1)).hom.rTensor Q) ((C.d (i + 1) (i + 2)).hom.rTensor Q)

private theorem exists_extend_of_pureInjective
    {K M J : Type v} [AddCommGroup K] [Module A K] [AddCommGroup M] [Module A M]
    [AddCommGroup J] [Module A J] (e : K →ₗ[A] M)
    (he : UniversallyInjective e) (hinj : Function.Injective e)
    (hJ : Module.PureInjective A J) (g : K →ₗ[A] J) :
    ∃ g' : M →ₗ[A] J, g'.comp e = g := by
  let S := LinearMap.range e
  obtain ⟨g', hg'⟩ :=
    (hJ K M (M ⧸ S) e S.mkQ hinj S.mkQ_surjective (by simp [S]) he).2.1 g
  exact ⟨g', hg'⟩

/-- A map out of `X` that kills the kernel of `d : X → Y` extends along `d` to a pure injective
target, provided `d` is the next map after `f` in a universally exact sequence. -/
private theorem exists_extend_of_exact
    {L X Y Z : Type v} [AddCommGroup L] [Module A L] [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] [AddCommGroup Z] [Module A Z]
    (f : L →ₗ[A] X) (d : X →ₗ[A] Y) (g : X →ₗ[A] Z) (hexact : Function.Exact f d)
    (hbase : ∀ (Q : Type v) [AddCommGroup Q] [Module A Q],
      Function.Exact (f.rTensor Q) (d.rTensor Q))
    (hker : d.ker ≤ g.ker) (hZ : Module.PureInjective A Z) :
    ∃ g' : Y →ₗ[A] Z, g'.comp d = g := by
  let lift := d.ker.liftQ g hker
  let φ : d.range →ₗ[A] Z := lift.comp d.quotKerEquivRange.symm.toLinearMap
  have hφ : φ.comp d.rangeRestrict = g := by
    ext x
    change lift (d.quotKerEquivRange.symm ⟨d x, LinearMap.mem_range_self d x⟩) = g x
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    exact congrArg (fun q : X →ₗ[A] Z => q x) (Submodule.liftQ_mkQ d.ker g hker)
  obtain ⟨g', hg'⟩ := exists_extend_of_pureInjective d.range.subtype
    (Module.universallyInjective_range_subtype f d hexact hbase)
    (by intro x y h; exact Subtype.ext h) hZ φ
  refine ⟨g', ?_⟩
  calc
    g'.comp d = (g'.comp d.range.subtype).comp d.rangeRestrict := rfl
    _ = g := by rw [hg', hφ]

/-- If `g` agrees with `δ ∘ h'` on the image of `dp`, and `dp, d` is universally exact,
then `g = δ ∘ h' + h ∘ d` for some `h` into a pure injective target. -/
private theorem exists_eq_comp_add_comp
    {X Y Z V W : Type v} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    [AddCommGroup Z] [Module A Z] [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (dp : X →ₗ[A] Y) (d : Y →ₗ[A] Z) (hexact : Function.Exact dp d)
    (hbase : ∀ (Q : Type v) [AddCommGroup Q] [Module A Q],
      Function.Exact (dp.rTensor Q) (d.rTensor Q))
    (hW : Module.PureInjective A W) (g : Y →ₗ[A] W) (δ : V →ₗ[A] W) (h' : Y →ₗ[A] V)
    (hg : g.comp dp = (δ.comp h').comp dp) :
    ∃ h : Z →ₗ[A] W, g = δ.comp h' + h.comp d := by
  obtain ⟨h, hh⟩ := exists_extend_of_exact dp d (g - δ.comp h') hexact hbase
    (fun x hx => by
      obtain ⟨y, rfl⟩ := (hexact x).mp hx
      exact sub_eq_zero.mpr (congrArg (fun q : X →ₗ[A] W => q y) hg)) hW
  exact ⟨h, by rw [hh]; abel⟩

private structure ComparisonPrefix
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (C I : CochainComplex (ModuleCat.{v} A) ℕ)
    (aC : M →ₗ[A] C.X 0) (aI : N →ₗ[A] I.X 0) (f : M →ₗ[A] N)
    (n : ℕ) where
  map : (i : ℕ) → C.X i →ₗ[A] I.X i
  initial : (map 0).comp aC = aI.comp f
  comm : ∀ i, i < n → (map (i + 1)).comp (C.d i (i + 1)).hom =
    (I.d i (i + 1)).hom.comp (map i)

private theorem next_comparison_map
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {C I : CochainComplex (ModuleCat.{v} A) ℕ}
    {aC : M →ₗ[A] C.X 0} {aI : N →ₗ[A] I.X 0} {f : M →ₗ[A] N}
    {n : ℕ} (p : ComparisonPrefix (A := A) C I aC aI f n)
    (hC : IsUniversallyExactResolution C aC)
    (hI : Module.PureInjectiveResolution.IsPureInjectiveResolution I aI) :
    ∃ g : C.X (n + 1) →ₗ[A] I.X (n + 1),
      g.comp (C.d n (n + 1)).hom = (I.d n (n + 1)).hom.comp (p.map n) := by
  let dC := (C.d n (n + 1)).hom
  let dI := (I.d n (n + 1)).hom
  let g := dI.comp (p.map n)
  have hker : dC.ker ≤ g.ker := by
    intro x hx
    change dI (p.map n x) = 0
    cases n with
    | zero =>
        obtain ⟨m, hm⟩ := (hC.exact_zero x).mp hx
        rw [← hm]
        rw [show (p.map 0) (aC m) = (aI.comp f) m from congrArg (fun q => q m) p.initial]
        exact Function.Exact.apply_apply_eq_zero hI.exact_zero (f m)
    | succ k =>
        obtain ⟨y, hy⟩ := (hC.exact k x).mp hx
        have hp := p.comm k (Nat.lt_succ_self k)
        have hzero := Function.Exact.apply_apply_eq_zero (hI.exact k) (p.map k y)
        rw [← hy]
        rw [show (p.map (k + 1)) ((C.d k (k + 1)).hom y) =
          (I.d k (k + 1)).hom ((p.map k) y) from congrArg (fun q => q y) hp]
        exact hzero
  cases n with
  | zero =>
      exact exists_extend_of_exact aC dC g hC.exact_zero hC.baseChange_exact_zero hker
        (hI.pureInjective 1)
  | succ k =>
      exact exists_extend_of_exact (C.d k (k + 1)).hom dC g (hC.exact k) (hC.baseChange_exact · k)
        hker (hI.pureInjective (k + 2))

private noncomputable def extendComparisonPrefix
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {C I : CochainComplex (ModuleCat.{v} A) ℕ}
    {aC : M →ₗ[A] C.X 0} {aI : N →ₗ[A] I.X 0} {f : M →ₗ[A] N}
    {n : ℕ} (p : ComparisonPrefix (A := A) C I aC aI f n)
    (hC : IsUniversallyExactResolution C aC)
    (hI : Module.PureInjectiveResolution.IsPureInjectiveResolution I aI) :
    ComparisonPrefix (A := A) C I aC aI f (n + 1) := by
  classical
  let g := Classical.choose (next_comparison_map p hC hI)
  have hg := Classical.choose_spec (next_comparison_map p hC hI)
  let newMap : (i : ℕ) → C.X i →ₗ[A] I.X i :=
    fun i => if h : i = n + 1 then h.symm ▸ g else p.map i
  refine ⟨newMap, ?_, ?_⟩
  · have h0 : (0 : ℕ) ≠ n + 1 := by omega
    simpa [newMap, h0] using p.initial
  · intro i hi
    by_cases hlt : i < n
    · have hne : i + 1 ≠ n + 1 := by omega
      have hne' : i ≠ n := by omega
      have hne'' : i ≠ n + 1 := by omega
      simpa [newMap, hne, hne', hne''] using p.comm i hlt
    · have hie : i = n := by omega
      subst i
      have hne : n ≠ n + 1 := by omega
      simpa [newMap, hne] using hg

private noncomputable def initialComparisonPrefix
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {C I : CochainComplex (ModuleCat.{v} A) ℕ}
    (aC : M →ₗ[A] C.X 0) (aI : N →ₗ[A] I.X 0) (f : M →ₗ[A] N)
    (g0 : C.X 0 →ₗ[A] I.X 0) (hg0 : g0.comp aC = aI.comp f) :
    ComparisonPrefix (A := A) C I aC aI f 0 := by
  refine ⟨(fun i => if h : i = 0 then h.symm ▸ g0 else 0), ?_, ?_⟩
  · simpa using hg0
  · intro i hi; omega

/-- A map `M → N` extends to a map from any universally exact resolution of `M`
to any pure injective resolution of `N`. -/
@[stacks 0704 "comparison_map"]
public theorem exists_comparison_map
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N)
    (C I : CochainComplex (ModuleCat.{v} A) ℕ)
    (aC : M →ₗ[A] C.X 0) (aI : N →ₗ[A] I.X 0)
    (hC : IsUniversallyExactResolution C aC)
    (hI : Module.PureInjectiveResolution.IsPureInjectiveResolution I aI) :
    ∃ F : C ⟶ I, (F.f 0).hom.comp aC = aI.comp f := by
  classical
  obtain ⟨g0, hg0⟩ := exists_extend_of_pureInjective aC
    hC.universallyInjective_augmentation hC.injective_augmentation
    (hI.pureInjective 0) (aI.comp f)
  let prefixes : ∀ n, ComparisonPrefix (A := A) C I aC aI f n :=
    Nat.rec (initialComparisonPrefix aC aI f g0 hg0)
      (fun n p => extendComparisonPrefix p hC hI)
  let F : C ⟶ I := HomologicalComplex.Hom.mk
    (fun i => ModuleCat.ofHom (prefixes i |>.map i))
    (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      rcases hij with rfl
      apply ModuleCat.hom_ext
      change (I.d i (i + 1)).hom.comp ((prefixes i).map i) =
        ((prefixes (i + 1)).map (i + 1)).comp (C.d i (i + 1)).hom
      have hmap : ((prefixes (i + 1)).map i) = ((prefixes i).map i) := by
        simp [prefixes, extendComparisonPrefix]
      rw [← hmap]
      exact ((prefixes (i + 1)).comm i (Nat.lt_succ_self i)).symm)
  exact ⟨F, (prefixes 0).initial⟩

end

section

open CategoryTheory

universe u v


variable {A : Type u} [CommRing A]


private theorem homotopy_exists_of_zero_augmentation
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (C I : CochainComplex (ModuleCat.{v} A) ℕ)
    (aC : M →ₗ[A] C.X 0) (hC : Module.PureInjectiveResolution.IsUniversallyExactResolution C aC)
    {aI : N →ₗ[A] I.X 0}
    (hI : Module.PureInjectiveResolution.IsPureInjectiveResolution I aI)
    (e : C ⟶ I) (he : (e.f 0).hom.comp aC = 0) : Nonempty (Homotopy e 0) := by
  classical
  let g : (i : ℕ) → C.X i →ₗ[A] I.X i := fun i => (e.f i).hom
  obtain ⟨h0, hh0⟩ := exists_extend_of_exact aC (C.d 0 1).hom (g 0) hC.exact_zero
    hC.baseChange_exact_zero
    (fun x hx => by
      obtain ⟨m, rfl⟩ := (hC.exact_zero x).mp hx
      exact congrArg (fun q : M →ₗ[A] I.X 0 => q m) he) (hI.pureInjective 0)
  have hh0' : g 0 = h0.comp (C.d 0 1).hom := hh0.symm
  have hchain0 : (g 1).comp (C.d 0 1).hom = (I.d 0 1).hom.comp (g 0) := by
    have hc : (e.f 1).hom.comp (C.d 0 1).hom =
        (I.d 0 1).hom.comp (e.f 0).hom :=
      congrArg (fun q : C.X 0 ⟶ I.X 1 => q.hom) (e.comm 0 1).symm
    change (e.f 1).hom.comp (C.d 0 1).hom =
      (I.d 0 1).hom.comp (e.f 0).hom
    exact hc
  obtain ⟨h1, hh1⟩ := exists_eq_comp_add_comp (C.d 0 1).hom (C.d 1 2).hom (hC.exact 0)
    (hC.baseChange_exact · 0) (hI.pureInjective 1) (g 1) (I.d 0 1).hom h0
    (by rw [hchain0, hh0', LinearMap.comp_assoc])
  have comm_one : e.f 1 =
      (ModuleCat.ofHom h0) ≫ I.d 0 1 + C.d 1 2 ≫ (ModuleCat.ofHom h1) := by
    apply ModuleCat.hom_ext
    change (e.f 1).hom = (I.d 0 1).hom.comp h0 + h1.comp (C.d 1 2).hom
    exact hh1
  refine ⟨Homotopy.mkCoinductive e (ModuleCat.ofHom h0) ?_ (ModuleCat.ofHom h1) comm_one ?_⟩
  · apply ModuleCat.hom_ext
    change (e.f 0).hom = h0.comp (C.d 0 1).hom
    exact hh0'
  · intro n p
    have heq : g (n + 1) = (I.d n (n + 1)).hom.comp p.1.hom +
        p.2.1.hom.comp (C.d (n + 1) (n + 2)).hom := by
      apply LinearMap.ext
      intro y
      have hp : (e.f (n + 1)).hom = (I.d n (n + 1)).hom.comp p.1.hom +
          p.2.1.hom.comp (C.d (n + 1) (n + 2)).hom :=
        congrArg (fun q : C.X (n + 1) ⟶ I.X (n + 1) => q.hom) p.2.2
      exact congrArg (fun q : C.X (n + 1) →ₗ[A] I.X (n + 1) => q y) hp
    have hdd : (I.d (n + 1) (n + 2)).hom.comp (I.d n (n + 1)).hom = 0 := by
      rw [← ModuleCat.hom_comp, I.d_comp_d, ModuleCat.hom_zero]
    have hc : (g (n + 2)).comp (C.d (n + 1) (n + 2)).hom =
        (I.d (n + 1) (n + 2)).hom.comp (g (n + 1)) :=
      congrArg (fun q : C.X (n + 1) ⟶ I.X (n + 2) => q.hom) (e.comm (n + 1) (n + 2)).symm
    let step := exists_eq_comp_add_comp (C.d (n + 1) (n + 2)).hom (C.d (n + 2) (n + 3)).hom
      (hC.exact (n + 1)) (hC.baseChange_exact · (n + 1)) (hI.pureInjective (n + 2))
      (g (n + 2)) (I.d (n + 1) (n + 2)).hom p.2.1.hom
      (by
        rw [hc, heq, LinearMap.comp_add, ← LinearMap.comp_assoc, hdd, LinearMap.zero_comp,
          zero_add, LinearMap.comp_assoc])
    let hn := Classical.choose step
    have hne := Classical.choose_spec step
    refine ⟨ModuleCat.ofHom hn, ?_⟩
    apply ModuleCat.hom_ext
    change (e.f (n + 2)).hom =
      (I.d (n + 1) (n + 2)).hom.comp p.2.1.hom +
        hn.comp (C.d (n + 2) (n + 3)).hom
    exact hne

/-- Comparison maps extending the same map between resolved modules are homotopic. -/
@[stacks 0704 "comparison_homotopy"]
public theorem homotopy_of_same_augmentation
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (C I : CochainComplex (ModuleCat.{v} A) ℕ)
    (augmentationC : M →ₗ[A] C.X 0) (augmentationI : N →ₗ[A] I.X 0)
    (hC : Module.PureInjectiveResolution.IsUniversallyExactResolution C augmentationC)
    (hI : Module.PureInjectiveResolution.IsPureInjectiveResolution I augmentationI)
    (f : M →ₗ[A] N) (α β : C ⟶ I)
    (hα : (α.f 0).hom.comp augmentationC = augmentationI.comp f)
    (hβ : (β.f 0).hom.comp augmentationC = augmentationI.comp f) :
    Nonempty (Homotopy α β) := by
  classical
  let γ : C ⟶ I := α - β
  have hγ : (γ.f 0).hom.comp augmentationC = 0 := by
    ext m
    change (α.f 0).hom (augmentationC m) - (β.f 0).hom (augmentationC m) = 0
    simpa only [sub_eq_zero, LinearMap.comp_apply] using
      (congrArg (fun q : M →ₗ[A] I.X 0 => q m) hα).trans
        (congrArg (fun q : M →ₗ[A] I.X 0 => q m) hβ).symm
  obtain ⟨hγ⟩ := homotopy_exists_of_zero_augmentation C I augmentationC hC hI γ hγ
  exact ⟨(Homotopy.equivSubZero (f := α) (g := β)).symm hγ⟩

end

section

universe u v

open Module


open CategoryTheory
open scoped TensorProduct

variable {A : Type u} [CommRing A]

private structure PureInjectiveExtension (M : ModuleCat.{v} A) where
  I : ModuleCat.{v} A
  N : ModuleCat.{v} A
  f : M ⟶ I
  g : I ⟶ N
  f_injective : Function.Injective f.hom
  g_surjective : Function.Surjective g.hom
  exact : LinearMap.range f.hom = LinearMap.ker g.hom
  f_universallyInjective : UniversallyInjective f.hom
  I_pureInjective : Module.PureInjective A I

private noncomputable def pureInjectiveExtension (M : ModuleCat.{v} A) :
    PureInjectiveExtension (A := A) M := by
  choose I N hIadd hImod hNadd hNmod f g hf hg hex hui hpi using
    exists_pureInjective_universallyExact_extension A M
  letI : AddCommGroup I := hIadd
  letI : Module A I := hImod
  letI : AddCommGroup N := hNadd
  letI : Module A N := hNmod
  exact ⟨ModuleCat.of A I, ModuleCat.of A N, ModuleCat.ofHom f, ModuleCat.ofHom g,
    hf, hg, hex, hui, hpi⟩

private noncomputable def resolutionModules (M : Type v) [AddCommGroup M] [Module A M] :
    ℕ → ModuleCat.{v} A :=
  Nat.rec (ModuleCat.of A M) (fun _ X => (pureInjectiveExtension (A := A) X).N)

private noncomputable def resolutionTerms (M : Type v) [AddCommGroup M] [Module A M]
    (n : ℕ) : ModuleCat.{v} A :=
  (pureInjectiveExtension (A := A) (resolutionModules (A := A) M n)).I

private noncomputable def resolutionEmbedding (M : Type v) [AddCommGroup M] [Module A M]
    (n : ℕ) : resolutionModules (A := A) M n ⟶ resolutionTerms (A := A) M n :=
  (pureInjectiveExtension (A := A) (resolutionModules (A := A) M n)).f

private noncomputable def resolutionQuotient (M : Type v) [AddCommGroup M] [Module A M]
    (n : ℕ) : resolutionTerms (A := A) M n ⟶ resolutionModules (A := A) M (n + 1) :=
  (pureInjectiveExtension (A := A) (resolutionModules (A := A) M n)).g

private noncomputable def resolutionDifferential (M : Type v) [AddCommGroup M] [Module A M]
    (n : ℕ) : resolutionTerms (A := A) M n ⟶ resolutionTerms (A := A) M (n + 1) :=
  resolutionQuotient (A := A) M n ≫ resolutionEmbedding (A := A) M (n + 1)

private lemma exact_comp_surjective_injective
    {R : Type u} [Semiring R]
    {L M N P Q : Type v}
    [AddCommMonoid L] [Module R L] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    [AddCommMonoid Q] [Module R Q]
    (f : L →ₗ[R] M) (g : M →ₗ[R] N) (h : N →ₗ[R] P) (i : P →ₗ[R] Q)
    (hf : Function.Surjective f) (hi : Function.Injective i)
    (hex : Function.Exact g h) :
    Function.Exact (g.comp f) (i.comp h) := by
  intro x
  constructor
  · intro hx
    have hzero : h x = 0 := hi (by simpa [LinearMap.comp_apply] using hx)
    have hmem : x ∈ LinearMap.range g := (hex x).mp hzero
    obtain ⟨y, hy⟩ := hmem
    obtain ⟨z, hz⟩ := hf y
    refine ⟨z, ?_⟩
    change g (f z) = x
    rw [hz]
    exact hy
  · rintro ⟨z, rfl⟩
    have hz : h (g (f z)) = 0 := (hex (g (f z))).mpr ⟨f z, rfl⟩
    simp [LinearMap.comp_apply, hz]

private lemma resolution_embedding_comp_quotient (M : Type v) [AddCommGroup M]
    [Module A M] (n : ℕ) :
    resolutionEmbedding (A := A) M n ≫ resolutionQuotient (A := A) M n = 0 := by
  apply ModuleCat.hom_ext
  ext x
  change (pureInjectiveExtension (A := A) (resolutionModules (A := A) M n)).g.hom
      ((pureInjectiveExtension (A := A) (resolutionModules (A := A) M n)).f.hom x) = 0
  apply LinearMap.mem_ker.mp
  rw [← (pureInjectiveExtension (A := A) (resolutionModules (A := A) M n)).exact]
  exact LinearMap.mem_range_self _ x

/-- Every module admits an augmented, universally exact cochain complex of pure injectives. -/
@[stacks 0704 "existence"]
public theorem exists_pureInjectiveResolution
    (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M] :
    ∃ (I : CochainComplex (ModuleCat.{v} A) ℕ) (augmentation : M →ₗ[A] I.X 0),
      Module.PureInjectiveResolution.IsPureInjectiveResolution I augmentation := by
  classical
  let X : ℕ → ModuleCat.{v} A := resolutionTerms (A := A) M
  let d : ∀ n, X n ⟶ X (n + 1) := resolutionDifferential (A := A) M
  have hd : ∀ n, d n ≫ d (n + 1) = 0 := by
    intro n
    calc
      (resolutionQuotient (A := A) M n ≫ resolutionEmbedding (A := A) M (n + 1)) ≫
        (resolutionQuotient (A := A) M (n + 1) ≫ resolutionEmbedding (A := A) M (n + 1 + 1)) =
        resolutionQuotient (A := A) M n ≫
        (resolutionEmbedding (A := A) M (n + 1) ≫ resolutionQuotient (A := A) M (n + 1)) ≫
        resolutionEmbedding (A := A) M (n + 1 + 1) := by simp only [Category.assoc]
      _ = 0 := by rw [resolution_embedding_comp_quotient (A := A) M (n + 1)]; simp
  let I := CochainComplex.of X d hd
  have hI_d (n : ℕ) :
      (I.d n (n + 1)).hom = (resolutionDifferential (A := A) M n).hom := by
    simp [I, d, CochainComplex.of_d, resolutionDifferential]
  have hI_d_comp (n : ℕ) :
      (I.d n (n + 1)).hom =
        (resolutionEmbedding (A := A) M (n + 1)).hom.comp
          (resolutionQuotient (A := A) M n).hom := by
    rw [hI_d, resolutionDifferential]
    simp [ModuleCat.hom_comp]
  let augmentation : M →ₗ[A] I.X 0 := (resolutionEmbedding (A := A) M 0).hom
  have hExact (n : ℕ) :
      Function.Exact
        ((resolutionEmbedding (A := A) M n).hom)
        ((resolutionQuotient (A := A) M n).hom) := by
    rw [LinearMap.exact_iff]
    exact (pureInjectiveExtension (A := A) (resolutionModules (A := A) M n)).exact.symm
  have hSurj (n : ℕ) : Function.Surjective ((resolutionQuotient (A := A) M n).hom) :=
    (pureInjectiveExtension (A := A) (resolutionModules (A := A) M n)).g_surjective
  have hInj (n : ℕ) : Function.Injective ((resolutionEmbedding (A := A) M n).hom) :=
    (pureInjectiveExtension (A := A) (resolutionModules (A := A) M n)).f_injective
  have hUni (n : ℕ) : UniversallyInjective ((resolutionEmbedding (A := A) M n).hom) :=
    (pureInjectiveExtension (A := A) (resolutionModules (A := A) M n)).f_universallyInjective
  refine ⟨I, augmentation, ?_⟩
  refine {
    injective_augmentation := hInj 0
    universallyInjective_augmentation := hUni 0
    exact_zero := ?_
    baseChange_exact_zero := ?_
    exact := ?_
    baseChange_exact := ?_
    pureInjective := ?_ }
  · apply exact_comp_surjective_injective (LinearMap.id : M →ₗ[A] M)
      ((resolutionEmbedding (A := A) M 0).hom)
      ((resolutionQuotient (A := A) M 0).hom)
      ((resolutionEmbedding (A := A) M 1).hom)
    · intro x
      exact ⟨x, rfl⟩
    · exact hInj 1
    · exact hExact 0
  · intro Q hQadd hQmod
    let := hQadd
    let := hQmod
    have hresult := exact_comp_surjective_injective
      (LinearMap.id :
        ((resolutionModules (A := A) M 0 ⊗[A] Q) →ₗ[A]
          (resolutionModules (A := A) M 0 ⊗[A] Q)))
      (LinearMap.rTensor Q ((resolutionEmbedding (A := A) M 0).hom))
      (LinearMap.rTensor Q ((resolutionQuotient (A := A) M 0).hom))
      (LinearMap.rTensor Q ((resolutionEmbedding (A := A) M 1).hom))
      (by intro x; exact ⟨x, rfl⟩) (hUni 1 Q)
      (rTensor_exact Q (hExact 0) (hSurj 0))
    change Function.Exact
      (LinearMap.rTensor Q ((resolutionEmbedding (A := A) M 0).hom))
      (LinearMap.rTensor Q ((I.d 0 1).hom))
    rw [congrArg (LinearMap.rTensor Q) (hI_d_comp 0)]
    rw [LinearMap.rTensor_comp]
    change Function.Exact
      (LinearMap.rTensor Q ((resolutionEmbedding (A := A) M 0).hom))
      (LinearMap.rTensor Q ((resolutionEmbedding (A := A) M 1).hom) ∘ₗ
        LinearMap.rTensor Q ((resolutionQuotient (A := A) M 0).hom))
    simpa only [LinearMap.comp_id] using hresult
  -- The indices are written `n + 1 + 1` rather than `n + 2` throughout: `hI_d_comp (n + 1)`
  -- rewrites to the former, and closing the goal against a hypothesis stated in the latter
  -- sends `isDefEq` into the `Classical.choose` under `resolutionEmbedding`.
  · intro n
    have hresult := exact_comp_surjective_injective
      ((resolutionQuotient (A := A) M n).hom)
      ((resolutionEmbedding (A := A) M (n + 1)).hom)
      ((resolutionQuotient (A := A) M (n + 1)).hom)
      ((resolutionEmbedding (A := A) M (n + 1 + 1)).hom)
      (hSurj n) (hInj (n + 1 + 1)) (hExact (n + 1))
    change Function.Exact ((I.d n (n + 1)).hom) ((I.d (n + 1) (n + 1 + 1)).hom)
    rw [hI_d_comp n, hI_d_comp (n + 1)]
    exact hresult
  · intro Q hQadd hQmod n
    let := hQadd
    let := hQmod
    have hresult := exact_comp_surjective_injective
      (LinearMap.rTensor Q ((resolutionQuotient (A := A) M n).hom))
      (LinearMap.rTensor Q ((resolutionEmbedding (A := A) M (n + 1)).hom))
      (LinearMap.rTensor Q ((resolutionQuotient (A := A) M (n + 1)).hom))
      (LinearMap.rTensor Q ((resolutionEmbedding (A := A) M (n + 1 + 1)).hom))
      (LinearMap.rTensor_surjective Q (hSurj n)) (hUni (n + 1 + 1) Q)
      (rTensor_exact Q (hExact (n + 1)) (hSurj (n + 1)))
    change Function.Exact
      (LinearMap.rTensor Q ((I.d n (n + 1)).hom))
      (LinearMap.rTensor Q ((I.d (n + 1) (n + 1 + 1)).hom))
    rw [congrArg (LinearMap.rTensor Q) (hI_d_comp n),
      congrArg (LinearMap.rTensor Q) (hI_d_comp (n + 1))]
    rw [LinearMap.rTensor_comp, LinearMap.rTensor_comp]
    exact hresult
  · intro n
    change Module.PureInjective A (resolutionTerms (A := A) M n)
    exact (pureInjectiveExtension (A := A) (resolutionModules (A := A) M n)).I_pureInjective

end

end Module.PureInjectiveResolution

end
