module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Pure.Defs
public import StacksFrontier.Algebra.Module.Pure.InjectiveResolution
public import StacksFrontier.Algebra.Module.Pure.Projective
public import StacksFrontier.Algebra.Module.Pure.ProjectiveResolution

/-!
# Pure extension groups

The *pure Ext* groups of a pair of modules are the cohomology of the Hom complex of a pure
injective resolution of the second argument.  They vanish in positive degrees when that
argument is pure injective, and also when the first argument is pure projective — in
particular when it is of finite presentation.

## References

* [Stacks Project, Tag 0705](https://stacks.math.columbia.edu/tag/0705)
* [Stacks Project, Tag 0706](https://stacks.math.columbia.edu/tag/0706)
-/

@[expose] public section

namespace Module

section

open CategoryTheory

universe u v


variable {A : Type u} [CommRing A]

/-- The cochain complex `Hom_A(M, Iᐧ)` associated to a cochain complex `I`. -/
public noncomputable def homComplex (M : Type v) [AddCommGroup M] [Module A M]
    (I : CochainComplex (ModuleCat.{v} A) ℕ) :
    CochainComplex (ModuleCat.{v} A) ℕ :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of A (M →ₗ[A] I.X n))
    (fun n ↦ ModuleCat.ofHom
      { toFun := fun f ↦ (I.d n (n + 1)).hom.comp f
        map_add' := by intros; ext; simp
        map_smul' := by intros; ext; simp })
    (fun n ↦ by
      apply ModuleCat.hom_ext
      ext f x
      change ((I.d (n + 1) (n + 2)).hom.comp
        ((I.d n (n + 1)).hom.comp f)) x = 0
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      change (I.d n (n + 1) ≫ I.d (n + 1) (n + 2)) (f x) = 0
      rw [I.d_comp_d]
      rfl)

/-- The `i`th pure extension module of `M` by `N`. -/
@[stacks 0705]
public noncomputable def pureExt (M N : Type v) [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (i : ℕ) : ModuleCat.{v} A :=
  let I := Classical.choose (Module.PureInjectiveResolution.exists_pureInjectiveResolution A N)
  (homComplex M I).homology i

end

section

open CategoryTheory

universe u v


variable {A : Type u} [CommRing A]

private lemma pureInjective_splits_universallyInjective
    {K P : Type v} [AddCommGroup K] [Module A K]
    [AddCommGroup P] [Module A P]
    (hK : Module.PureInjective A K)
    (f : K →ₗ[A] P) (hf : Function.Injective f)
    (hfu : UniversallyInjective f) :
    ∃ r : P →ₗ[A] K, r.comp f = LinearMap.id := by
  obtain ⟨r, hr⟩ := (hK K P (P ⧸ LinearMap.range f) f (LinearMap.range f).mkQ hf
    (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _).symm hfu).2.1 LinearMap.id
  exact ⟨r, LinearMap.ext fun x => DFunLike.congr_fun hr x⟩

private lemma pureInjective_of_retract
    {K P : Type v} [AddCommGroup K] [Module A K]
    [AddCommGroup P] [Module A P]
    (hP : Module.PureInjective A P)
    (j : K →ₗ[A] P) (r : P →ₗ[A] K)
    (hr : r.comp j = LinearMap.id) :
    Module.PureInjective A K := by
  intro X Y Z _ _ _ _ _ _ f g hf hg hfg hfu
  have hgf : g.comp f = 0 := LinearMap.range_le_ker_iff.mp hfg.le
  have hPI := hP X Y Z f g hf hg hfg hfu
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    have hab' : LinearMap.lcomp A P g (j.comp a) =
        LinearMap.lcomp A P g (j.comp b) := by
      ext y
      exact congrArg j (DFunLike.congr_fun hab y)
    have heq := hPI.1 hab'
    have heq' := congrArg (LinearMap.compRight A r) heq
    change (r.comp j).comp a = (r.comp j).comp b at heq'
    simpa [hr] using heq'
  · intro x
    obtain ⟨y, hy⟩ := hPI.2.1 (j.comp x)
    refine ⟨r.comp y, ?_⟩
    have hy' := congrArg (LinearMap.compRight A r) hy
    change r.comp (y.comp f) = r.comp (j.comp x) at hy'
    calc
      LinearMap.lcomp A K f (r.comp y) = r.comp (y.comp f) := rfl
      _ = r.comp (j.comp x) := hy'
      _ = x := by rw [← LinearMap.comp_assoc, hr]; simp
  · apply le_antisymm
    · rintro x ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      ext z
      show y (g (f z)) = 0
      simpa using congrArg y (DFunLike.congr_fun hgf z)
    · intro x hx
      have hxP : LinearMap.lcomp A P f (j.comp x) = 0 := by
        ext z
        simpa using congrArg j (DFunLike.congr_fun hx z)
      obtain ⟨y, hy⟩ : j.comp x ∈ LinearMap.range (LinearMap.lcomp A P g) := by
        rw [hPI.2.2, LinearMap.mem_ker]
        exact hxP
      refine ⟨r.comp y, ?_⟩
      have hy' := congrArg (LinearMap.compRight A r) hy
      change r.comp (y.comp g) = r.comp (j.comp x) at hy'
      calc
        LinearMap.lcomp A K g (r.comp y) = r.comp (y.comp g) := rfl
        _ = r.comp (j.comp x) := hy'
        _ = x := by rw [← LinearMap.comp_assoc, hr]; simp

private lemma pureInjective_of_linearEquiv
    {K P : Type v} [AddCommGroup K] [Module A K]
    [AddCommGroup P] [Module A P]
    (e : K ≃ₗ[A] P)
    (hP : Module.PureInjective A P) :
    Module.PureInjective A K :=
  pureInjective_of_retract hP e.toLinearMap e.symm.toLinearMap (by ext; simp)

private noncomputable def kerRet_linearEquiv_range
    {K I J : Type v} [AddCommGroup K] [Module A K]
    [AddCommGroup I] [Module A I] [AddCommGroup J] [Module A J]
    (f : K →ₗ[A] I) (g : I →ₗ[A] J) (r : I →ₗ[A] K)
    (hfg : LinearMap.range f = LinearMap.ker g)
    (hr : r.comp f = LinearMap.id) :
    LinearMap.ker r ≃ₗ[A] LinearMap.range g := by
  have hgf : g.comp f = 0 := LinearMap.range_le_ker_iff.mp hfg.le
  let e0 : LinearMap.ker r →ₗ[A] LinearMap.range g :=
    { toFun := fun x => ⟨g x, ⟨x, rfl⟩⟩
      map_add' := by intro x y; ext; simp
      map_smul' := by intro a x; ext; simp }
  have hinj : Function.Injective e0 := by
    intro x y hxy
    apply Subtype.ext
    obtain ⟨z, hz⟩ : x.1 - y.1 ∈ LinearMap.range f := by
      rw [hfg, LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact congrArg Subtype.val hxy
    have hz' := congrArg r hz
    have hrf : r (f z) = z := by simpa using LinearMap.congr_fun hr z
    have hrxy : r (x.1 - y.1) = 0 := by
      simp [map_sub, LinearMap.mem_ker.mp x.property, LinearMap.mem_ker.mp y.property]
    obtain rfl : z = 0 := by rwa [hrf, hrxy] at hz'
    exact sub_eq_zero.mp (by simpa using hz.symm)
  have hsurj : Function.Surjective e0 := by
    rintro ⟨y, ⟨x, rfl⟩⟩
    let x' : LinearMap.ker r := ⟨x - f (r x), by
      rw [LinearMap.mem_ker]
      have hh := congrArg (fun q : K →ₗ[A] K => q (r x)) hr
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at hh
      simp [map_sub, hh]⟩
    refine ⟨x', ?_⟩
    apply Subtype.ext
    change g (x - f (r x)) = g x
    simp only [map_sub]
    have hh := congrArg (fun q : K →ₗ[A] J => q (r x)) hgf
    simpa using congrArg (fun z : J => g x - z) hh
  exact LinearEquiv.ofBijective e0 ⟨hinj, hsurj⟩

private lemma pureInjective_range_of_splitSequence
    {K I J : Type v} [AddCommGroup K] [Module A K]
    [AddCommGroup I] [Module A I] [AddCommGroup J] [Module A J]
    (hK : Module.PureInjective A K)
    (hI : Module.PureInjective A I)
    (f : K →ₗ[A] I) (g : I →ₗ[A] J)
    (hf : Function.Injective f) (hfu : UniversallyInjective f)
    (hex : Function.Exact f g) :
    Module.PureInjective A (LinearMap.range g) := by
  have hfg : LinearMap.range f = LinearMap.ker g := hex.linearMap_ker_eq.symm
  obtain ⟨r, hr⟩ := pureInjective_splits_universallyInjective hK f hf hfu
  let j : LinearMap.ker r →ₗ[A] I := (LinearMap.ker r).subtype
  let p : I →ₗ[A] LinearMap.ker r :=
    { toFun := fun x => ⟨x - f (r x), by
        rw [LinearMap.mem_ker]
        have hh := congrArg (fun q : K →ₗ[A] K => q (r x)) hr
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at hh
        simp [map_sub, hh]⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        show (x + y) - f (r (x + y)) =
          (x - f (r x)) + (y - f (r y))
        simp only [map_add]
        abel_nf
      map_smul' := by
        intro a x
        apply Subtype.ext
        show a • x - f (r (a • x)) = a • (x - f (r x))
        simp only [map_smul, smul_sub] }
  have hpj : p.comp j = LinearMap.id := by
    ext x
    show x - f (r x) = x
    simp [LinearMap.mem_ker.mp x.property]
  have hker : Module.PureInjective A (LinearMap.ker r) :=
    pureInjective_of_retract hI j p hpj
  exact pureInjective_of_linearEquiv (kerRet_linearEquiv_range f g r hfg hr).symm hker

private lemma rangeSubtype_universallyInjective_of_tensorExact
    {K I J : Type v} [AddCommGroup K] [Module A K]
    [AddCommGroup I] [Module A I] [AddCommGroup J] [Module A J]
    (f : K →ₗ[A] I) (g : I →ₗ[A] J)
    (hexfg : Function.Exact f g)
    (hbase₁ : ∀ (Q : Type v) [AddCommGroup Q] [Module A Q],
      Function.Exact (f.rTensor Q) (g.rTensor Q)) :
    UniversallyInjective (LinearMap.range g).subtype := by
  intro Q _ _
  let q := g.rangeRestrict
  let j := (LinearMap.range g).subtype
  have hq : Function.Surjective q := by
    rw [← LinearMap.range_eq_top]
    exact LinearMap.range_rangeRestrict g
  intro x y hxy
  have hsub : LinearMap.rTensor Q j (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := LinearMap.rTensor_surjective Q hq (x - y)
  have hgz : LinearMap.rTensor Q g z = 0 := by
    rw [show g = j.comp q from rfl, LinearMap.rTensor_comp, LinearMap.comp_apply, hz, hsub]
  obtain ⟨w, hw⟩ := (hbase₁ Q z).mp hgz
  have hqf : q.comp f = 0 := by
    ext x
    show g (f x) = 0
    exact (hexfg (f x)).mpr ⟨x, rfl⟩
  have hqz : LinearMap.rTensor Q q z = 0 := by
    rw [← hw, ← LinearMap.rTensor_comp_apply, hqf, LinearMap.rTensor_zero, LinearMap.zero_apply]
  exact sub_eq_zero.mp (hz.symm.trans hqz)

private lemma range_eq_ker_of_exact
    {K I J : Type v} [AddCommGroup K] [Module A K]
    [AddCommGroup I] [Module A I] [AddCommGroup J] [Module A J]
    (f : K →ₗ[A] I) (g : I →ₗ[A] J) (hex : Function.Exact f g) :
    LinearMap.range f = LinearMap.ker g :=
  hex.linearMap_ker_eq.symm

private lemma pureResolution_rangeSubtype_universallyInjective
    {M : Type v} [AddCommGroup M] [Module A M]
    (I : CochainComplex (ModuleCat.{v} A) ℕ) (augmentation : M →ₗ[A] I.X 0)
    (hI : Module.PureInjectiveResolution.IsPureInjectiveResolution I augmentation)
    (n : ℕ) :
    UniversallyInjective (LinearMap.range (I.d n (n + 1)).hom).subtype := by
  cases n with
  | zero =>
      exact rangeSubtype_universallyInjective_of_tensorExact augmentation (I.d 0 1).hom
        hI.exact_zero hI.baseChange_exact_zero
  | succ n =>
      exact rangeSubtype_universallyInjective_of_tensorExact (I.d n (n + 1)).hom
        (I.d (n + 1) (n + 2)).hom (hI.exact n)
        (fun Q _ _ => hI.baseChange_exact Q n)

private lemma pureResolution_images_pureInjective
    {N : Type v} [AddCommGroup N] [Module A N]
    (I : CochainComplex (ModuleCat.{v} A) ℕ) (augmentation : N →ₗ[A] I.X 0)
    (hI : Module.PureInjectiveResolution.IsPureInjectiveResolution I augmentation)
    (hN : Module.PureInjective A N) :
    ∀ n : ℕ, Module.PureInjective A
      (LinearMap.range (I.d n (n + 1)).hom) := by
  intro n
  induction n with
  | zero =>
      exact pureInjective_range_of_splitSequence hN (hI.pureInjective 0)
        augmentation (I.d 0 1).hom hI.injective_augmentation hI.universallyInjective_augmentation
        hI.exact_zero
  | succ n ih =>
      exact pureInjective_range_of_splitSequence ih (hI.pureInjective (n + 1))
        (LinearMap.range (I.d n (n + 1)).hom).subtype (I.d (n + 1) (n + 2)).hom
        Subtype.val_injective (pureResolution_rangeSubtype_universallyInjective I augmentation hI n)
        fun x => by simpa using hI.exact n x

/-- `Hom_A(M, -)` is exact at `J` when every map `M → range g` lifts through `g`. -/
private lemma compRight_exact_of_lift
    {M I J L : Type v} [AddCommGroup M] [Module A M]
    [AddCommGroup I] [Module A I] [AddCommGroup J] [Module A J] [AddCommGroup L] [Module A L]
    (g : I →ₗ[A] J) (h : J →ₗ[A] L) (hgh : LinearMap.range g = LinearMap.ker h)
    (hlift : ∀ y : M →ₗ[A] LinearMap.range g, ∃ ψ : M →ₗ[A] I, g.rangeRestrict.comp ψ = y) :
    Function.Exact
      (LinearMap.compRight A g : (M →ₗ[A] I) →ₗ[A] (M →ₗ[A] J))
      (LinearMap.compRight A h : (M →ₗ[A] J) →ₗ[A] (M →ₗ[A] L)) := by
  intro x
  constructor
  · intro hx
    obtain ⟨ψ, hψ⟩ := hlift (LinearMap.codRestrict (LinearMap.range g) x (fun m => by
      rw [hgh, LinearMap.mem_ker]
      exact DFunLike.congr_fun hx m))
    refine ⟨ψ, ?_⟩
    ext m
    exact congrArg Subtype.val (DFunLike.congr_fun hψ m)
  · rintro ⟨y, rfl⟩
    show h.comp (g.comp y) = 0
    rw [← LinearMap.comp_assoc, LinearMap.range_le_ker_iff.mp hgh.le]
    simp

/-- In a pure injective resolution, `Iⁿ` receives a universally injective, injective map from a
module `K` with image the kernel of `Iⁿ → Iⁿ⁺¹`, and `K` is pure injective when `N` is. -/
private lemma exists_universallyInjective_ker_inclusion
    {N : Type v} [AddCommGroup N] [Module A N]
    (I : CochainComplex (ModuleCat.{v} A) ℕ) (η : N →ₗ[A] I.X 0)
    (hI : Module.PureInjectiveResolution.IsPureInjectiveResolution I η) (n : ℕ) :
    ∃ (K : Type v) (_ : AddCommGroup K) (_ : Module A K) (f : K →ₗ[A] I.X n),
      Function.Injective f ∧ UniversallyInjective f ∧
        LinearMap.range f = LinearMap.ker (I.d n (n + 1)).hom ∧
        (Module.PureInjective A N → Module.PureInjective A K) := by
  cases n with
  | zero =>
      exact ⟨N, _, _, η, hI.injective_augmentation, hI.universallyInjective_augmentation,
        range_eq_ker_of_exact _ _ hI.exact_zero, id⟩
  | succ n =>
      exact ⟨LinearMap.range (I.d n (n + 1)).hom, _, _,
        (LinearMap.range (I.d n (n + 1)).hom).subtype, Subtype.val_injective,
        pureResolution_rangeSubtype_universallyInjective I η hI n,
        range_eq_ker_of_exact _ _ fun x => by simpa using hI.exact n x,
        fun hN => pureResolution_images_pureInjective I η hI hN n⟩

/-- `Hom_A(M, Iᐧ)` is exact in degree `n + 1` if the maps induced by `Iⁿ → Iⁿ⁺¹ → Iⁿ⁺²` are. -/
private lemma homComplex_exactAt_of_exact
    (M : Type v) [AddCommGroup M] [Module A M] (I : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (hExact : Function.Exact
      (LinearMap.compRight A (I.d n (n + 1)).hom : (M →ₗ[A] I.X n) →ₗ[A] (M →ₗ[A] I.X (n + 1)))
      (LinearMap.compRight A (I.d (n + 1) (n + 2)).hom :
        (M →ₗ[A] I.X (n + 1)) →ₗ[A] (M →ₗ[A] I.X (n + 2)))) :
    (homComplex M I).ExactAt (n + 1) := by
  let C := homComplex M I
  have hMap₁ : (C.d n (n + 1)).hom = LinearMap.compRight A (I.d n (n + 1)).hom := by
    ext φ
    simp only [C, Module.homComplex, CochainComplex.of_d, ModuleCat.hom_ofHom]
    rfl
  have hMap₂ : (C.d (n + 1) (n + 2)).hom = LinearMap.compRight A (I.d (n + 1) (n + 2)).hom := by
    have hMap₂' : (C.d (n + 1) ((n + 1) + 1)).hom =
        LinearMap.compRight A (I.d (n + 1) ((n + 1) + 1)).hom := by
      ext φ
      simp only [C, Module.homComplex, CochainComplex.of_d, ModuleCat.hom_ofHom]
      rfl
    simpa only [show (n + 1) + 1 = n + 2 by omega] using hMap₂'
  apply (C.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).2
  apply ModuleCat.shortComplex_exact
  show Function.Exact (C.d n (n + 1)).hom (C.d (n + 1) (n + 2)).hom
  rw [hMap₁, hMap₂]
  exact hExact

private lemma hom_exact_of_split
    {M K I J L : Type v} [AddCommGroup M] [Module A M]
    [AddCommGroup K] [Module A K] [AddCommGroup I] [Module A I]
    [AddCommGroup J] [Module A J] [AddCommGroup L] [Module A L]
    (f : K →ₗ[A] I) (g : I →ₗ[A] J) (h : J →ₗ[A] L)
    (hfg : LinearMap.range f = LinearMap.ker g)
    (hgh : LinearMap.range g = LinearMap.ker h)
    (r : I →ₗ[A] K) (hr : r.comp f = LinearMap.id) :
    Function.Exact
      (LinearMap.compRight A g : (M →ₗ[A] I) →ₗ[A] (M →ₗ[A] J))
      (LinearMap.compRight A h : (M →ₗ[A] J) →ₗ[A] (M →ₗ[A] L)) := by
  let e := kerRet_linearEquiv_range f g r hfg hr
  refine compRight_exact_of_lift g h hgh fun y => ⟨((LinearMap.ker r).subtype.comp
    e.symm.toLinearMap).comp y, ?_⟩
  ext m
  exact congrArg Subtype.val (e.apply_symm_apply (y m))

/-- Positive-degree pure extensions into a pure injective module vanish. -/
@[stacks 0706 "pure_injective_vanishing"]
public theorem pureExt_isZero_of_pureInjective
    (M N : Type v) [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (hN : Module.PureInjective A N)
    (i : ℕ) (hi : 0 < i) :
    CategoryTheory.Limits.IsZero (Module.pureExt (A := A) M N i) := by
  classical
  let hExists := Module.PureInjectiveResolution.exists_pureInjectiveResolution A N
  let I := Classical.choose hExists
  obtain ⟨augmentation, hI⟩ : ∃ augmentation : N →ₗ[A] I.X 0,
      Module.PureInjectiveResolution.IsPureInjectiveResolution I augmentation :=
    Classical.choose_spec hExists
  show CategoryTheory.Limits.IsZero ((Module.homComplex M I).homology i)
  cases i with
  | zero => omega
  | succ n =>
      refine (homComplex_exactAt_of_exact M I n ?_).isZero_homology
      obtain ⟨K, _, _, f, hf, hfu, hfg, hK⟩ :=
        exists_universallyInjective_ker_inclusion I augmentation hI n
      obtain ⟨r, hr⟩ := pureInjective_splits_universallyInjective (hK hN) f hf hfu
      exact hom_exact_of_split f _ _ hfg (range_eq_ker_of_exact _ _ (hI.exact n)) r hr

end

section

open CategoryTheory

open scoped DirectSum

universe u v

variable {A : Type u} [CommRing A]

/-- A module of finite presentation is pure projective: it is a retract of the direct sum of
the one-element family consisting of itself. -/
public theorem pureProjective_of_finitePresentation
    (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] :
    Module.PureProjective A M :=
  Module.pureProjective_of_directSum_retract A M Unit (fun _ => M) (fun _ => inferInstance)
    (DirectSum.lof A Unit (fun _ => M) ())
    (DirectSum.toModule A Unit M fun _ => LinearMap.id)
    (by ext x; simp)

private lemma hom_exact_of_pureProjective
    {M K I J L : Type (max u v)} [AddCommGroup M] [Module A M]
    [AddCommGroup K] [Module A K] [AddCommGroup I] [Module A I]
    [AddCommGroup J] [Module A J] [AddCommGroup L] [Module A L]
    (hM : Module.PureProjective A M)
    (f : K →ₗ[A] I) (g : I →ₗ[A] J) (h : J →ₗ[A] L)
    (hf : Function.Injective f) (hfu : UniversallyInjective f)
    (hfg : LinearMap.range f = LinearMap.ker g)
    (hgh : LinearMap.range g = LinearMap.ker h) :
    Function.Exact
      (LinearMap.compRight A g : (M →ₗ[A] I) →ₗ[A] (M →ₗ[A] J))
      (LinearMap.compRight A h : (M →ₗ[A] J) →ₗ[A] (M →ₗ[A] L)) := by
  have hker : LinearMap.range f = LinearMap.ker g.rangeRestrict := by
    rw [hfg, LinearMap.ker_rangeRestrict]
  have hlift := (hM K I (LinearMap.range g) f g.rangeRestrict hf
    (LinearMap.surjective_rangeRestrict g) hker hfu).2.1
  refine compRight_exact_of_lift g h hgh fun y => ?_
  obtain ⟨ψ, hψ⟩ := hlift y
  exact ⟨ψ, by simpa [LinearMap.compRight_apply] using hψ⟩

/-- For a pure projective module `M`, the complex `Hom_A(M, Iᐧ)` attached to a pure injective
resolution `I` of `N` is exact in every positive degree.  This is the exactness of the columns
of the double complex `Hom_A(Pᐧ, Iᐧ)`. -/
public theorem homComplex_exactAt_of_pureProjective
    {M N : Type (max u v)} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (hM : Module.PureProjective A M)
    (I : CochainComplex (ModuleCat.{max u v} A) ℕ) (η : N →ₗ[A] I.X 0)
    (hI : Module.PureInjectiveResolution.IsPureInjectiveResolution I η)
    (n : ℕ) :
    (Module.homComplex M I).ExactAt (n + 1) := by
  refine homComplex_exactAt_of_exact M I n ?_
  obtain ⟨K, _, _, f, hf, hfu, hfg, -⟩ := exists_universallyInjective_ker_inclusion I η hI n
  exact hom_exact_of_pureProjective hM f _ _ hf hfu hfg (range_eq_ker_of_exact _ _ (hI.exact n))

/-- Positive-degree pure extensions out of a pure projective module vanish. -/
@[stacks 0706 "pure_projective_vanishing"]
public theorem pureExt_isZero_of_pureProjective
    (M N : Type (max u v)) [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (hM : Module.PureProjective A M)
    (i : ℕ) (hi : 0 < i) :
    CategoryTheory.Limits.IsZero (Module.pureExt (A := A) M N i) := by
  obtain ⟨η, hI⟩ := Classical.choose_spec
    (Module.PureInjectiveResolution.exists_pureInjectiveResolution A N)
  cases i with
  | zero => omega
  | succ n => exact (homComplex_exactAt_of_pureProjective (M := M) hM _ η hI n).isZero_homology

/-- Positive-degree pure extensions out of a module of finite presentation vanish. -/
@[stacks 0706 "finite_presentation_vanishing"]
public theorem pureExt_isZero_of_finitePresentation
    (M N : Type (max u v)) [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.FinitePresentation A M]
    (i : ℕ) (hi : 0 < i) :
    CategoryTheory.Limits.IsZero (Module.pureExt (A := A) M N i) :=
  Module.pureExt_isZero_of_pureProjective M N
    (Module.pureProjective_of_finitePresentation A M) i hi

end

section

open CategoryTheory

universe u v

variable {A : Type u} [CommRing A]

/-- The cochain complex `Hom_A(Pᐧ, N)` associated to a chain complex `P`. -/
public noncomputable def homComplexOfChain (P : ChainComplex (ModuleCat.{v} A) ℕ)
    (N : Type v) [AddCommGroup N] [Module A N] :
    CochainComplex (ModuleCat.{v} A) ℕ :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of A (P.X n →ₗ[A] N))
    (fun n ↦ ModuleCat.ofHom (LinearMap.lcomp A N (P.d (n + 1) n).hom))
    (fun n ↦ by
      apply ModuleCat.hom_ext
      ext f x
      change f ((P.d (n + 1) n).hom ((P.d (n + 2) (n + 1)).hom x)) = 0
      have hz := congrArg (fun k : P.X (n + 2) ⟶ P.X n => k.hom x)
        (P.d_comp_d (n + 2) (n + 1) n)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] at hz
      rw [hz, map_zero])

private lemma hom_exact_of_pureInjective
    {J X Y Z : Type (max u v)} [AddCommGroup J] [Module A J]
    [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    [AddCommGroup Z] [Module A Z]
    (hJ : Module.PureInjective A J)
    (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z)
    (hfg : LinearMap.range f = LinearMap.ker g)
    (hu : UniversallyInjective (LinearMap.range f).subtype)
    (hu' : UniversallyInjective (LinearMap.range g).subtype) :
    Function.Exact
      (LinearMap.lcomp A J g : (Z →ₗ[A] J) →ₗ[A] (Y →ₗ[A] J))
      (LinearMap.lcomp A J f : (Y →ₗ[A] J) →ₗ[A] (X →ₗ[A] J)) := by
  have hgf : g.comp f = 0 := LinearMap.range_le_ker_iff.mp hfg.le
  have hker : LinearMap.range (LinearMap.range f).subtype =
      LinearMap.ker g.rangeRestrict := by
    rw [Submodule.range_subtype, hfg, LinearMap.ker_rangeRestrict]
  have hPI := hJ (LinearMap.range f) Y (LinearMap.range g)
    (LinearMap.range f).subtype g.rangeRestrict Subtype.val_injective
    (LinearMap.surjective_rangeRestrict g) hker hu
  have hExt := (hJ (LinearMap.range g) Z (Z ⧸ LinearMap.range g)
    (LinearMap.range g).subtype (LinearMap.range g).mkQ Subtype.val_injective
    (Submodule.mkQ_surjective _)
    (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) hu').2.1
  have hdecomp : (LinearMap.range g).subtype.comp g.rangeRestrict = g :=
    LinearMap.ext fun _ => rfl
  intro φ
  constructor
  · intro hφ
    have hmem : φ ∈ LinearMap.ker (LinearMap.lcomp A J (LinearMap.range f).subtype) := by
      rw [LinearMap.mem_ker]
      apply LinearMap.ext
      rintro ⟨y, x, rfl⟩
      simpa using DFunLike.congr_fun hφ x
    rw [← hPI.2.2] at hmem
    obtain ⟨ψ, hψ⟩ := hmem
    have hψ' : ψ.comp g.rangeRestrict = φ := hψ
    obtain ⟨χ, hχ⟩ := hExt ψ
    have hχ' : χ.comp (LinearMap.range g).subtype = ψ := hχ
    refine ⟨χ, ?_⟩
    show χ.comp g = φ
    rw [← hψ', ← hχ', LinearMap.comp_assoc, hdecomp]
  · rintro ⟨χ, rfl⟩
    show (χ.comp g).comp f = 0
    rw [LinearMap.comp_assoc, hgf]
    simp

/-- For a pure injective module `J`, the complex `Hom_A(Pᐧ, J)` attached to a pure projective
resolution `P` of `M` is exact in every positive degree.  This is the exactness of the rows of
the double complex `Hom_A(Pᐧ, Iᐧ)`. -/
public theorem homComplexOfChain_exactAt_of_pureInjective
    {M J : Type (max u v)} [AddCommGroup M] [Module A M] [AddCommGroup J] [Module A J]
    (hJ : Module.PureInjective A J)
    (P : ChainComplex (ModuleCat.{max u v} A) ℕ) (ε : P.X 0 →ₗ[A] M)
    (hP : Module.PureProjectiveResolution.IsPureProjectiveResolution P ε)
    (n : ℕ) :
    (Module.homComplexOfChain P J).ExactAt (n + 1) := by
  let C := Module.homComplexOfChain P J
  let f := (P.d (n + 2) (n + 1)).hom
  let g := (P.d (n + 1) n).hom
  have hExact : Function.Exact
      (LinearMap.lcomp A J g : (P.X n →ₗ[A] J) →ₗ[A] (P.X (n + 1) →ₗ[A] J))
      (LinearMap.lcomp A J f : (P.X (n + 1) →ₗ[A] J) →ₗ[A] (P.X (n + 2) →ₗ[A] J)) := by
    refine hom_exact_of_pureInjective hJ f g
      (range_eq_ker_of_exact f g (by simpa [f, g] using hP.exact n)) ?_ ?_
    · exact Module.universallyInjective_range_subtype (P.d (n + 3) (n + 2)).hom f
        (by simpa [f] using hP.exact (n + 1))
        (fun Q _ _ => hP.baseChange_exact Q (n + 1))
    · exact Module.universallyInjective_range_subtype f g
        (by simpa [f, g] using hP.exact n)
        (fun Q _ _ => hP.baseChange_exact Q n)
  have hMap₁ : (C.d n (n + 1)).hom = LinearMap.lcomp A J g := by
    simp only [C, Module.homComplexOfChain, CochainComplex.of_d, ModuleCat.hom_ofHom]
    rfl
  have hMap₂ : (C.d (n + 1) (n + 2)).hom = LinearMap.lcomp A J f := by
    have hMap₂' : (C.d (n + 1) ((n + 1) + 1)).hom =
        LinearMap.lcomp A J (P.d ((n + 1) + 1) (n + 1)).hom := by
      simp only [C, Module.homComplexOfChain, CochainComplex.of_d, ModuleCat.hom_ofHom]
      rfl
    simpa only [show (n + 1) + 1 = n + 2 by omega] using hMap₂'
  apply (C.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).2
  apply ModuleCat.shortComplex_exact
  show Function.Exact (C.d n (n + 1)).hom (C.d (n + 1) (n + 2)).hom
  rw [hMap₁, hMap₂]
  exact hExact

/-- `Hom_A(-, J)` is left exact at the augmentation of a chain resolution: a map `Pᵢ → J`
killing the image of `P₁ → P₀` factors through the augmentation. -/
public theorem homComplexOfChain_augmentation_exact
    {M P₀ P₁ J : Type v} [AddCommGroup M] [Module A M] [AddCommGroup P₀] [Module A P₀]
    [AddCommGroup P₁] [Module A P₁] [AddCommGroup J] [Module A J]
    (d : P₁ →ₗ[A] P₀) (ε : P₀ →ₗ[A] M) (hε : Function.Surjective ε)
    (hex : LinearMap.range d = LinearMap.ker ε) :
    Function.Exact
      (LinearMap.lcomp A J ε : (M →ₗ[A] J) →ₗ[A] (P₀ →ₗ[A] J))
      (LinearMap.lcomp A J d : (P₀ →ₗ[A] J) →ₗ[A] (P₁ →ₗ[A] J)) := by
  intro φ
  constructor
  · intro hφ
    have hle : LinearMap.ker ε ≤ LinearMap.ker φ := by
      rw [← hex]
      rintro _ ⟨x, rfl⟩
      exact LinearMap.mem_ker.mpr (DFunLike.congr_fun hφ x)
    refine ⟨((LinearMap.ker ε).liftQ φ hle).comp
      (ε.quotKerEquivOfSurjective hε).symm.toLinearMap, ?_⟩
    show (((LinearMap.ker ε).liftQ φ hle).comp
      (ε.quotKerEquivOfSurjective hε).symm.toLinearMap).comp ε = φ
    ext x
    have hx : (ε.quotKerEquivOfSurjective hε).symm (ε x) = (LinearMap.ker ε).mkQ x :=
      (ε.quotKerEquivOfSurjective hε).symm_apply_eq.2 rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hx]
    exact DFunLike.congr_fun (Submodule.liftQ_mkQ (LinearMap.ker ε) φ hle) x
  · rintro ⟨χ, rfl⟩
    show (χ.comp ε).comp d = 0
    rw [LinearMap.comp_assoc, LinearMap.range_le_ker_iff.mp hex.le]
    simp

/-- `Hom_A(Q, -)` is left exact at the augmentation of a cochain resolution: a map `Q → I⁰`
killing by `I⁰ → I¹` lands in the image of the augmentation. -/
public theorem homComplex_augmentation_exact
    {Q N I₀ I₁ : Type v} [AddCommGroup Q] [Module A Q] [AddCommGroup N] [Module A N]
    [AddCommGroup I₀] [Module A I₀] [AddCommGroup I₁] [Module A I₁]
    (η : N →ₗ[A] I₀) (d : I₀ →ₗ[A] I₁) (hη : Function.Injective η)
    (hex : LinearMap.range η = LinearMap.ker d) :
    Function.Exact
      (LinearMap.compRight A η : (Q →ₗ[A] N) →ₗ[A] (Q →ₗ[A] I₀))
      (LinearMap.compRight A d : (Q →ₗ[A] I₀) →ₗ[A] (Q →ₗ[A] I₁)) := by
  have hrange : Function.Bijective η.rangeRestrict :=
    ⟨fun x y hxy => hη (congrArg Subtype.val hxy), LinearMap.surjective_rangeRestrict η⟩
  let e : N ≃ₗ[A] LinearMap.range η := LinearEquiv.ofBijective η.rangeRestrict hrange
  refine compRight_exact_of_lift η d hex fun y => ⟨e.symm.toLinearMap.comp y, ?_⟩
  ext q
  exact congrArg Subtype.val (e.apply_symm_apply (y q))

end

end Module

end
