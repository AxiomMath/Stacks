module

public import Mathlib.Algebra.Category.ModuleCat.InjectiveDimension
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.Algebra.Polynomial.Module.TensorProduct
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import StacksFrontier.Algebra.Module.Essential

/-!
# Injective modules: splittings, examples and stability

This file collects the facts about injective modules that feed the construction of injective
hulls and the computation of injective dimension.

The starting point is that an injective module splits off from any module containing it: an
injective linear map out of an injective module exhibits its target as a product. Dually, a map
out of a module is injective as soon as its restriction to an essential submodule is, which is
what makes an injective hull of `M` a maximal essential extension of `M`.

Two families of examples and two stability statements follow. Over a reduced ring the
localization at a minimal prime is an injective module — the localization is then a field, and
Baer's criterion is checked by hand. Over a Noetherian ring an arbitrary direct sum of injective
modules is again injective; the Noetherian hypothesis enters because a linear map out of a
finitely generated ideal has image in a finite partial sum. Finally, extending an injective
module over a Noetherian ring along `A → A[X]` raises injective dimension by at most one: the
coinduced module `Hom_A(A[X], E)` is injective over `A[X]`, and multiplication by `X` fits the
extension into a short exact sequence with the coinduced module in the middle two spots.

## Main results

* `Module.exists_linearEquiv_prod_of_injective` — an injective submodule is a direct summand.
* `Module.mono_of_isEssentialMono_of_comp_mono` — a morphism whose restriction to an essential
  subobject is a monomorphism is a monomorphism.
* `Module.bijective_hom_localizationAtPrime` — maps into a localization at a prime are exactly
  the maps out of the localized module.
* `Module.injective_localizationAtPrime_of_minimal` — the localization of a reduced ring at a
  minimal prime is an injective module.
* `Module.directSum_injective` — over a Noetherian ring a direct sum of injective modules is
  injective.
* `Module.tensorProduct_polynomial_hasInjectiveDimensionLE` — the extension of scalars of an
  injective module along `A → A[X]` has injective dimension at most one.

## References

* [Stacks Project, Tag 08XT](https://stacks.math.columbia.edu/tag/08XT)
* [Stacks Project, Tag 08XV](https://stacks.math.columbia.edu/tag/08XV)
* [Stacks Project, Tag 0A6J](https://stacks.math.columbia.edu/tag/0A6J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Module

section Split

variable {R : Type u} [Ring R]
variable {J I : Type v} [AddCommGroup J] [AddCommGroup I] [Module R J] [Module R I]

/-- An injective submodule splits off: an injective linear map from an injective module identifies
the target with the product of its source and a complementary submodule. -/
lemma exists_linearEquiv_prod_of_injective (f : J →ₗ[R] I) (hf : Function.Injective f)
    [Module.Injective R J] :
    ∃ K : Submodule R I, ∃ e : I ≃ₗ[R] J × K, ∀ x : J, e (f x) = (x, 0) := by
  obtain ⟨g, hg⟩ := Module.Injective.out f hf (LinearMap.id : J →ₗ[R] J)
  let K : Submodule R I := LinearMap.ker g
  have hmem : ∀ x : I, x - f (g x) ∈ K := by
    intro x
    simp only [K, LinearMap.mem_ker]
    rw [map_sub, hg, LinearMap.id_apply, sub_self]
  let q : I →ₗ[R] K := (LinearMap.id - f.comp g).codRestrict K hmem
  let a : I →ₗ[R] J × K := g.prod q
  let b : J × K →ₗ[R] I :=
    f.comp (LinearMap.fst R J K) + K.subtype.comp (LinearMap.snd R J K)
  have hab : b.comp a = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change f (g x) + (x - f (g x)) = x
    abel
  have hba : a.comp b = LinearMap.id := by
    apply LinearMap.ext
    intro z
    rcases z with ⟨x, y⟩
    apply Prod.ext
    · simp [a, b, q, K, hg]
    · apply Subtype.ext
      change f x + (y : I) - f (g (f x + (y : I))) = (y : I)
      simp [map_add, hg, K]
  refine ⟨K, LinearEquiv.ofLinearMap a b hba hab, fun x => ?_⟩
  change (g (f x), q (f x)) = (x, 0)
  apply Prod.ext
  · simp [hg]
  · apply Subtype.ext
    simp [q, hg]

end Split

section EssentialMono

variable {C : Type u} [Category.{v, u} C] [Abelian C]

private lemma pullback_kernel_eq_bot {A B J : C} (i : A ⟶ B) (f : B ⟶ J) [Mono (i ≫ f)] :
    (Subobject.pullback i).obj (kernelSubobject f) = ⊥ := by
  rw [Subobject.pullback_kernelSubobject f i, Subobject.kernelSubobject_eq_bot_of_mono]

private lemma inf_kernel_mk_eq_bot {A B J : C} (i : A ⟶ B) (f : B ⟶ J) [Mono i]
    [Mono (i ≫ f)] : kernelSubobject f ⊓ Subobject.mk i = ⊥ := by
  rw [inf_comm, Subobject.inf_eq_map_pullback]
  let e := Subobject.underlyingIso i
  have heq : e.hom ≫ (i ≫ f) = (Subobject.mk i).arrow ≫ f := by
    rw [← Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]
  have : Mono ((Subobject.mk i).arrow ≫ f) := heq ▸ inferInstance
  rw [pullback_kernel_eq_bot (Subobject.mk i).arrow f]
  exact Subobject.map_bot _

/-- A morphism whose restriction to an essential subobject is a monomorphism
is itself a monomorphism. -/
theorem mono_of_isEssentialMono_of_comp_mono {A B J : C} (i : A ⟶ B) [Mono i] (f : B ⟶ J)
    (hi : IsEssentialMono i) [Mono (i ≫ f)] : Mono f := by
  apply Abelian.mono_of_kernel_ι_eq_zero f
  rw [← kernelSubobject_arrow']
  have hK : kernelSubobject f = ⊥ := by
    by_contra hK
    exact (hi (kernelSubobject f) hK) (inf_kernel_mk_eq_bot i f)
  have hArrow : (kernelSubobject f).arrow = 0 := by
    rw [hK]
    simp
  rw [hArrow, comp_zero]

end EssentialMono

section Localization

/-- For any module, maps into the localization at a prime are exactly the
maps from its localized module, via canonical precomposition. -/
@[stacks 08XT "canonical identification of Hom modules"]
theorem bijective_hom_localizationAtPrime
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (M : Type v) [AddCommGroup M] [Module R M] :
    Function.Bijective
      (fun f : LocalizedModule.AtPrime p M →ₗ[Localization.AtPrime p]
          Localization.AtPrime p =>
        (f.restrictScalars R).comp (LocalizedModule.mkLinearMap p.primeCompl M)) := by
  let S := p.primeCompl
  let i : M →ₗ[R] LocalizedModule S M := LocalizedModule.mkLinearMap S M
  refine ⟨fun f g h => LinearMap.restrictScalars_injective R
    (IsLocalizedModule.linearMap_ext S i (Algebra.linearMap R (Localization S)) h), fun g => ?_⟩
  let F : LocalizedModule S M →ₗ[R] Localization S :=
    LocalizedModule.lift S g (IsLocalizedModule.map_units (Algebra.linearMap R (Localization S)))
  let G : LocalizedModule S M →ₗ[Localization S] Localization S := {
    toFun := F
    map_add' := F.map_add
    map_smul' := by
      intro a x
      obtain ⟨⟨r, s⟩, hs⟩ := IsLocalization.mk'_surjective S a
      rw [← hs]
      induction x using LocalizedModule.induction_on with
      | h m t =>
        simp [F, LocalizedModule.lift_mk]
  }
  exact ⟨G, LocalizedModule.lift_comp S g
    (IsLocalizedModule.map_units (Algebra.linearMap R (Localization S)))⟩

/-- The localization of a reduced ring at a minimal prime is injective as
an `R`-module. -/
@[stacks 08XT "injectivity at a minimal prime"]
theorem injective_localizationAtPrime_of_minimal
    {R : Type u} [CommRing R] [IsReduced R] (p : Ideal R)
    [p.IsPrime] (hp : p ∈ minimalPrimes R) :
    Module.Injective R (Localization.AtPrime p) := by
  let K := Localization.AtPrime p
  let S := p.primeCompl
  let _ : Ring.KrullDimLE 0 K := Ring.KrullDimLE.of_isLocalization p hp K
  let _ : Field K := IsField.toField (Ring.KrullDimLE.isField_of_isReduced (R := K))
  apply Module.Baer.injective
  intro I f
  by_cases hI : ∃ y : I, (y : R) ∉ p
  · obtain ⟨y, hy⟩ := hI
    have hyunit : IsUnit (algebraMap R K (y : R)) :=
      IsLocalization.map_units (Localization.AtPrime p) (⟨(y : R), hy⟩ : p.primeCompl)
    let c : K := (algebraMap R K (y : R))⁻¹ * f y
    refine ⟨LinearMap.toSpanSingleton R K c, ?_⟩
    intro x hxI
    let xI : I := ⟨x, hxI⟩
    have hmul : (algebraMap R K (y : R)) * f xI =
        (algebraMap R K (x : R)) * f y := by
      simpa only [← Algebra.smul_def, ← map_smul] using
        congrArg f (show (y : R) • xI = (x : R) • y from
          Subtype.ext (mul_comm (y : R) x))
    change (x : R) • c = f xI
    rw [Algebra.smul_def]
    dsimp [c]
    symm
    calc
      f xI = (algebraMap R K (y : R))⁻¹ *
          ((algebraMap R K (y : R)) * f xI) := by
            rw [← mul_assoc, inv_mul_cancel₀ hyunit.ne_zero, one_mul]
      _ = (algebraMap R K (y : R))⁻¹ *
          ((algebraMap R K (x : R)) * f y) := by rw [hmul]
      _ = algebraMap R K (x : R) *
          ((algebraMap R K (y : R))⁻¹ * f y) := by ring
  · refine ⟨0, ?_⟩
    intro x hxI
    let xI : I := ⟨x, hxI⟩
    have hxP : x ∈ p := by
      by_contra hx
      exact hI ⟨xI, hx⟩
    have hxzero : algebraMap R K (x : R) = 0 := by
      by_contra hx
      exact (IsLocalization.AtPrime.isUnit_to_map_iff K p x).mp
        (isUnit_iff_ne_zero.mpr hx) hxP
    obtain ⟨s, hsx⟩ := (IsLocalization.map_eq_zero_iff (M := S) (S := K) x).mp hxzero
    have hsunit : IsUnit (algebraMap R K (s : R)) := IsLocalization.map_units K s
    have hsmul : (s : R) • xI = 0 := Subtype.ext hsx
    have hkill : (algebraMap R K (s : R)) * f xI = 0 := by
      simpa [Algebra.smul_def] using congrArg f hsmul
    simpa using (mul_eq_zero.mp hkill).resolve_left hsunit.ne_zero |>.symm

end Localization

section DirectSum

open scoped DirectSum

/-- Over a Noetherian ring, a linear map into a direct sum sends the multiples of `y` lying in its
domain into a fixed finite partial sum. -/
private theorem exists_finset_directSum_apply_eq_zero
    {R : Type*} [CommRing R] [IsNoetherianRing R] {ι : Type*} {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {Y : Type*} [AddCommGroup Y] [Module R Y]
    {A : Submodule R Y} (hA : A →ₗ[R] ⨁ i, M i) (y : Y) :
    ∃ S : Finset ι, ∀ i ∉ S, ∀ (r : R) (hr : r • y ∈ A), hA ⟨r • y, hr⟩ i = 0 := by
  classical
  let J : Ideal R := A.comap (LinearMap.toSpanSingleton R Y y)
  have hJ (r : R) : r ∈ J ↔ r • y ∈ A := by simp [J]
  obtain ⟨t, ht, hspan⟩ := Submodule.fg_def.mp (Ideal.FG.of_isNoetherianRing J)
  have ht' (z : R) (hz : z ∈ t) : z • y ∈ A := (hJ z).mp (hspan ▸ Submodule.subset_span hz)
  refine ⟨ht.toFinset.attach.biUnion fun x =>
    (hA ⟨x.1 • y, ht' x.1 (ht.mem_toFinset.mp x.2)⟩).support, fun i hi r hr => ?_⟩
  let K : Submodule R Y := (LinearMap.ker ((DirectSum.component R ι M i).comp hA)).map A.subtype
  have hle : J ≤ K.comap (LinearMap.toSpanSingleton R Y y) := by
    rw [← hspan, Submodule.span_le]
    intro z hz
    rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.mem_map]
    refine ⟨⟨z • y, ht' z hz⟩, ?_, by simp⟩
    rw [LinearMap.mem_ker]
    apply DFinsupp.notMem_support_iff.mp
    intro hzi
    exact hi (Finset.mem_biUnion.mpr
      ⟨⟨z, ht.mem_toFinset.mpr hz⟩, Finset.mem_attach _ _, hzi⟩)
  obtain ⟨b, hb, hby⟩ := Submodule.mem_map.mp (hle ((hJ r).mpr hr))
  obtain rfl : b = ⟨r • y, hr⟩ := Subtype.ext (by simpa using hby)
  exact hb

/-- Over a Noetherian ring, a linear map into a direct sum of injective modules is given, on the
multiples of `y` lying in its domain, by scaling a single element. -/
private theorem exists_smul_eq_directSum_of_injective
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {ι : Type v} (M : ι → Type (max v w)) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] [∀ i, Module.Injective R (M i)]
    {Y : Type (max v w)} [AddCommGroup Y] [Module R Y] (A : Submodule R Y)
    (hA : A →ₗ[R] ⨁ i, M i) (y : Y) :
    ∃ q : ⨁ i, M i, ∀ (r : R) (hr : r • y ∈ A), hA ⟨r • y, hr⟩ = r • q := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_directSum_apply_eq_zero hA y
  let e : ∀ i : (S : Set ι), Y →ₗ[R] M i.1 := fun i =>
    (Module.Injective.out (R := R) (Q := M i.1) A.subtype Subtype.val_injective
      ((DirectSum.component R ι M i.1).comp hA)).choose
  have he (i : (S : Set ι)) (x : A) : e i x.1 = hA x i.1 :=
    (Module.Injective.out (R := R) (Q := M i.1) A.subtype Subtype.val_injective
      ((DirectSum.component R ι M i.1).comp hA)).choose_spec x
  refine ⟨DirectSum.lmk R ι M S (fun i => e i y), fun r hr => ?_⟩
  apply DirectSum.ext_component R
  intro i
  change hA ⟨r • y, hr⟩ i = r • (DFinsupp.lmk S (fun i => e i y)) i
  by_cases hi : i ∈ S
  · let j : (↑S : Set ι) := ⟨i, hi⟩
    rw [DFinsupp.lmk_apply, DFinsupp.mk_apply, dite_eq_left hi, ← he j ⟨r • y, hr⟩, map_smul]
  · rw [DFinsupp.lmk_apply, DFinsupp.mk_apply, dite_eq_right hi, hS i hi r hr, smul_zero]

private theorem extensionOfMax_adjoin_apply_eq
    {R : Type u} [CommRing R] {Q X Y : Type w} [AddCommGroup Q] [Module R Q]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    {f : X →ₗ[R] Y} [Fact (Function.Injective f)] {g : X →ₗ[R] Q} {y : Y} {q : Q}
    (hq : ∀ (r : R) (hr : r • y ∈ (Baer.extensionOfMax f g).domain),
      (Baer.extensionOfMax f g).toLinearPMap.toFun ⟨r • y, hr⟩ = r • q)
    (x : Baer.supExtensionOfMaxSingleton f g y)
    (a : (Baer.extensionOfMax f g).domain) (r : R) (hxr : (x : Y) = a.1 + r • y) :
    (Baer.extensionOfMax f g).toLinearPMap.toFun (Baer.ExtensionOfMaxAdjoin.fst f x) +
        Baer.ExtensionOfMaxAdjoin.snd f x • q =
      (Baer.extensionOfMax f g).toLinearPMap.toFun a + r • q := by
  have heq : (r - Baer.ExtensionOfMaxAdjoin.snd f x) • y =
      (Baer.ExtensionOfMaxAdjoin.fst f x : Y) - a.1 := by
    rw [sub_smul, sub_eq_sub_iff_add_eq_add, ← hxr.symm.trans (Baer.ExtensionOfMaxAdjoin.eqn f x),
      add_comm]
  have hm : (r - Baer.ExtensionOfMaxAdjoin.snd f x) • y ∈ (Baer.extensionOfMax f g).domain := by
    rw [heq]
    exact Submodule.sub_mem _ (Baer.ExtensionOfMaxAdjoin.fst f x).2 a.2
  have hsub : (⟨(r - Baer.ExtensionOfMaxAdjoin.snd f x) • y, hm⟩ :
      (Baer.extensionOfMax f g).domain) = Baer.ExtensionOfMaxAdjoin.fst f x - a := Subtype.ext heq
  have hdiff : (Baer.extensionOfMax f g).toLinearPMap.toFun (Baer.ExtensionOfMaxAdjoin.fst f x) -
      (Baer.extensionOfMax f g).toLinearPMap.toFun a =
        (r - Baer.ExtensionOfMaxAdjoin.snd f x) • q := by
    rw [← map_sub, ← hsub]
    exact hq _ hm
  rw [sub_eq_iff_eq_add.mp hdiff, sub_smul]
  abel

private theorem exists_extensionOf_le_mem_domain
    {R : Type u} [CommRing R] {Q X Y : Type w} [AddCommGroup Q] [Module R Q]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    {f : X →ₗ[R] Y} [Fact (Function.Injective f)] {g : X →ₗ[R] Q} {y : Y} {q : Q}
    (hq : ∀ (r : R) (hr : r • y ∈ (Baer.extensionOfMax f g).domain),
      (Baer.extensionOfMax f g).toLinearPMap.toFun ⟨r • y, hr⟩ = r • q) :
    ∃ p' : Baer.ExtensionOf f g, Baer.extensionOfMax f g ≤ p' ∧ y ∈ p'.domain := by
  let p := Baer.extensionOfMax f g
  let hA := p.toLinearPMap.toFun
  let extFun : Baer.supExtensionOfMaxSingleton f g y → Q := fun x =>
    hA (Baer.ExtensionOfMaxAdjoin.fst f x) + Baer.ExtensionOfMaxAdjoin.snd f x • q
  have hext (x : Baer.supExtensionOfMaxSingleton f g y) (a : p.domain) (r : R)
      (hxr : (x : Y) = a.1 + r • y) : extFun x = hA a + r • q :=
    extensionOfMax_adjoin_apply_eq hq x a r hxr
  let p' : Baer.ExtensionOf f g := {
    domain := Baer.supExtensionOfMaxSingleton f g y
    le := le_trans p.le le_sup_left
    toFun := {
      toFun := extFun
      map_add' := fun x x' => by
        have hx : (↑(x + x') : Y) =
            ↑(Baer.ExtensionOfMaxAdjoin.fst f x + Baer.ExtensionOfMaxAdjoin.fst f x') +
              (Baer.ExtensionOfMaxAdjoin.snd f x + Baer.ExtensionOfMaxAdjoin.snd f x') • y := by
          change (x : Y) + (x' : Y) = _
          rw [Baer.ExtensionOfMaxAdjoin.eqn f x, Baer.ExtensionOfMaxAdjoin.eqn f x',
            Submodule.coe_add, add_smul]
          abel
        rw [hext (x + x') _ _ hx, map_add, add_smul,
          hext x _ _ (Baer.ExtensionOfMaxAdjoin.eqn f x),
          hext x' _ _ (Baer.ExtensionOfMaxAdjoin.eqn f x')]
        abel
      map_smul' := fun r x => by
        have hx : (↑(r • x) : Y) = ↑(r • Baer.ExtensionOfMaxAdjoin.fst f x) +
            (r * Baer.ExtensionOfMaxAdjoin.snd f x) • y := by
          change r • (x : Y) = _
          rw [Baer.ExtensionOfMaxAdjoin.eqn f x, smul_add, smul_smul, Submodule.coe_smul]
        rw [hext (r • x) _ _ hx, map_smul, smul_add, mul_smul]
        rfl }
    is_extension := fun x => by
      let a : p.domain := ⟨f x, p.le ⟨x, rfl⟩⟩
      change g x = extFun ⟨f x, le_trans p.le le_sup_left ⟨x, rfl⟩⟩
      rw [hext _ a 0 (by simp [a]), zero_smul, add_zero]
      exact p.is_extension x }
  refine ⟨p', ⟨le_sup_left, fun x x' hEq => ?_⟩, ?_⟩
  · symm
    change extFun x' = hA x
    simpa using hext x' x 0 (by simp [hEq])
  · change y ∈ p.domain ⊔ Submodule.span R {y}
    rw [Submodule.mem_sup]
    exact ⟨0, Submodule.zero_mem _, y, Submodule.mem_span_singleton_self _, by simp⟩

/-- An arbitrary direct sum of injective modules over a Noetherian ring is
injective. -/
@[stacks 08XV]
theorem directSum_injective
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {ι : Type v} (M : ι → Type (max v w)) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] [∀ i, Module.Injective R (M i)]
    : Module.Injective R (⨁ i, M i) := by
  refine ⟨?_⟩
  intro X Y _ _ _ _ f hf g
  have : Fact (Function.Injective f) := ⟨hf⟩
  let p : Module.Baer.ExtensionOf f g := Module.Baer.extensionOfMax f g
  have htop : p.domain = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun y => ?_
    obtain ⟨q, hq⟩ := exists_smul_eq_directSum_of_injective R M p.domain p.toLinearPMap.toFun y
    obtain ⟨p', hle, hy⟩ := exists_extensionOf_le_mem_domain (f := f) (g := g) hq
    rw [Module.Baer.extensionOfMax_is_max f g p' hle] at hy
    simpa [p] using hy
  refine ⟨
    { toFun := fun y => p.toLinearPMap ⟨y, htop ▸ Set.mem_univ y⟩
      map_add' := fun x y => by
        rw [← LinearPMap.map_add]
        congr 1
      map_smul' := fun r x => by
        rw [← LinearPMap.map_smul]
        dsimp }, ?_⟩
  intro x
  simpa using (p.is_extension x).symm

end DirectSum

section Polynomial

noncomputable section

/-- Injectivity transfers along a linear equivalence. -/
private theorem injective_of_linearEquiv {A : Type u} [CommRing A] [Small.{w} A]
    {M N : Type w} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) [Module.Injective.{u, w} A N] : Module.Injective.{u, w} A M :=
  Module.Baer.iff_injective.{u, w}.mp
    ((Module.Baer.congr e).mpr (Module.Baer.iff_injective.{u, w}.mpr ‹_›))

private theorem finsupp_nat_injective_of_noetherian
    {A : Type u} [CommRing A] [IsNoetherianRing A] [Small.{w} A]
    (E : Type w) [AddCommGroup E] [Module A E] [Module.Injective.{u, w} A E] :
    Module.Injective.{u, w} A (ℕ →₀ E) := by
  classical
  have : Module.Injective.{u, w} A (Π₀ _ : ℕ, E) := directSum_injective.{u, 0, w} A fun _ : ℕ => E
  exact injective_of_linearEquiv (finsuppLequivDFinsupp A)

private theorem polyModule_injective
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (E : Type w) [AddCommGroup E] [Module A E] [Small.{w} A]
    [Module.Injective.{u, w} A E] :
    Module.Injective.{u, w} A (PolynomialModule A E) := by
  have := finsupp_nat_injective_of_noetherian (A := A) E
  exact injective_of_linearEquiv (PolynomialModule.coeffLinearEquiv A A)

private theorem small_quotient_ext {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
    (H K : Submodule R M) (hHK : H ≤ K)
    [Small.{w} (M ⧸ K)] [Small.{w} (K ⧸ H.comap K.subtype)] :
    Small.{w} (M ⧸ H) := by
  classical
  let sec : M ⧸ K → M := fun q => Classical.choose (K.mkQ_surjective q)
  have hsec (q : M ⧸ K) : K.mkQ (sec q) = q := Classical.choose_spec (K.mkQ_surjective q)
  let res (m : M) : K := ⟨m - sec (K.mkQ m), by
    have hh : K.mkQ (m - sec (K.mkQ m)) = 0 := by rw [map_sub, hsec]; simp
    exact (Submodule.Quotient.mk_eq_zero K).mp hh⟩
  let f : M ⧸ H → (M ⧸ K) × (K ⧸ H.comap K.subtype) := fun x =>
    Quotient.liftOn' x (fun m => (K.mkQ m, (H.comap K.subtype).mkQ (res m))) (by
      intro a b hab
      have hab' : a - b ∈ H := by
        have hh : -a + b ∈ H.toAddSubgroup := by
          change QuotientAddGroup.leftRel H.toAddSubgroup a b at hab
          exact (QuotientAddGroup.leftRel_apply).mp hab
        have hn := H.toAddSubgroup.neg_mem hh
        simpa [sub_eq_add_neg, add_comm] using hn
      apply Prod.ext
      · exact (Submodule.Quotient.eq K).2 (hHK hab')
      · apply (Submodule.Quotient.eq (H.comap K.subtype)).2
        change (res a).val - (res b).val ∈ H
        have hq : K.mkQ a = K.mkQ b := (Submodule.Quotient.eq K).2 (hHK hab')
        have hs : sec (K.mkQ a) = sec (K.mkQ b) := congrArg sec hq
        change (a - sec (K.mkQ a)) - (b - sec (K.mkQ b)) ∈ H
        rw [hs]
        simpa using hab')
  have hf : Function.Injective f := by
    intro x y h
    revert h
    refine Quotient.inductionOn' x ?_
    intro a
    refine Quotient.inductionOn' y ?_
    intro b h
    change (K.mkQ a, (H.comap K.subtype).mkQ (res a)) =
      (K.mkQ b, (H.comap K.subtype).mkQ (res b)) at h
    rcases Prod.mk.inj h with ⟨h1, h2⟩
    apply (Submodule.Quotient.eq H).2
    have hr : ((res a : K) - (res b : K)) ∈ H.comap K.subtype :=
      (Submodule.Quotient.eq (H.comap K.subtype)).1 h2
    change (res a).val - (res b).val ∈ H at hr
    have hs : sec (K.mkQ a) = sec (K.mkQ b) := congrArg sec h1
    have hab : a - b = (res a).val - (res b).val := by
      change a - b = (a - sec (K.mkQ a)) - (b - sec (K.mkQ b))
      rw [hs]
      abel
    rw [hab]
    exact hr
  exact small_of_injective hf

private theorem small_power_layer {A : Type u} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) [Small.{v} (A ⧸ J)] (n : ℕ) :
    let K : Submodule A A := J ^ n
    let H : Submodule A A := J ^ (n+1)
    Small.{v} (K ⧸ H.comap K.subtype) := by
  let K : Submodule A A := J ^ n
  let H : Submodule A A := J ^ (n+1)
  change Small.{v} (K ⧸ H.comap K.subtype)
  have hgen : K.FG := IsNoetherian.noetherian (R := A) (M := A) K
  let _ : Module.Finite A K := Module.Finite.of_fg hgen
  let _ : Module.Finite A (K ⧸ H.comap K.subtype) := Module.Finite.quotient A (H.comap K.subtype)
  let T : Type u := K ⧸ H.comap K.subtype
  have hT : Module.IsTorsionBySet A T (J : Set A) := by
    rw [Module.isTorsionBySet_iff_subset_annihilator]
    intro j hj
    apply (Module.mem_annihilator).2
    intro t
    obtain ⟨x, rfl⟩ := (Submodule.Quotient.mk_surjective (H.comap K.subtype)) t
    change Submodule.Quotient.mk (j • x) = 0
    apply (Submodule.Quotient.mk_eq_zero (H.comap K.subtype)).2
    change j * (x : A) ∈ J ^ (n+1)
    rw [pow_succ']
    exact Ideal.mul_mem_mul hj x.property
  let _ : Module (A ⧸ J) T := hT.module
  have hfinite : Module.Finite (A ⧸ J) T :=
    Module.Finite.of_surjective hT.semilinearMap (fun x => ⟨x, rfl⟩)
  exact Module.Finite.small (A ⧸ J) T

private theorem small_power_quotient {A : Type u} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) [Small.{v} (A ⧸ J)] (n : ℕ) : Small.{v} (A ⧸ J ^ n) := by
  induction n with
  | zero => simpa [pow_zero] using (inferInstance : Small.{v} (A ⧸ (⊤ : Ideal A)))
  | succ n ih =>
    let K : Submodule A A := J ^ n
    let H : Submodule A A := J ^ (n+1)
    have hHK : H ≤ K := Ideal.pow_le_pow_right (Nat.le_succ n)
    have hL : Small.{v} (K ⧸ H.comap K.subtype) := by
      simpa [K, H] using small_power_layer (A := A) J n
    exact small_quotient_ext H K hHK

/-- The quotient of `A` by the annihilator of an `A`-module `E` is `v`-small: it embeds into the
endomorphisms of `E`. -/
public theorem small_quotient_annihilator {A : Type u} [CommRing A]
    (E : Type v) [AddCommGroup E] [Module A E] :
    Small.{v} (A ⧸ Module.annihilator A E) := by
  classical
  exact small_map (RingHom.quotientKerEquivRange (Module.toAddMonoidEnd A E)).toEquiv

/-- By Artin–Rees, a linear map from an ideal `I` into a module `E` vanishes on the elements of `I`
lying in a large enough power of the annihilator of `E`. -/
private theorem exists_map_eq_zero_of_mem_annihilator_pow {A : Type u} [CommRing A]
    [IsNoetherianRing A] {E : Type v} [AddCommGroup E] [Module A E] (I : Ideal A) (g : I →ₗ[A] E) :
    ∃ n : ℕ, ∀ x : I, (x : A) ∈ Module.annihilator A E ^ n → g x = 0 := by
  let J : Ideal A := Module.annihilator A E
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul J (I : Submodule A A)
  let n : ℕ := k + 1
  have hlow : (J ^ n : Submodule A A) ⊓ (I : Submodule A A) ≤ J • (I : Submodule A A) := by
    have htop (L : Ideal A) : (L : Submodule A A) = L • (⊤ : Submodule A A) := by
      ext x
      simp
    rw [htop (J ^ n), hk n (by omega), show n - k = 1 by omega, pow_one]
    exact Submodule.smul_mono (le_refl J) inf_le_right
  have hmap : J • (I : Submodule A A) ≤ (LinearMap.ker g).map I.subtype := by
    rw [Submodule.smul_le]
    intro j hj x hx
    refine Submodule.mem_map.mpr ⟨⟨j * x, I.mul_mem_left j hx⟩, ?_, rfl⟩
    change g (j • (⟨x, hx⟩ : I)) = 0
    rw [g.map_smul]
    exact Module.mem_annihilator.mp (show j ∈ Module.annihilator A E from hj) _
  refine ⟨n, fun x hx => ?_⟩
  obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp (hmap (hlow ⟨by simpa [J, n] using hx, x.property⟩))
  obtain rfl : z = x := Subtype.ext hzx
  exact hz

private theorem injective_ascend_noetherian
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Injective.{u, v} A E] :
    Module.Injective.{u, max u v} A (ULift.{u} E) := by
  let _ : Small.{max u v} A := small_lift.{u, v, u} A
  rw [← Module.Baer.iff_injective]
  intro I g
  classical
  have : Small.{v} (A ⧸ Module.annihilator A E) := small_quotient_annihilator E
  let g₀ : I →ₗ[A] E := (ULift.moduleEquiv : ULift.{u} E ≃ₗ[A] E).toLinearMap.comp g
  obtain ⟨n, hn⟩ := exists_map_eq_zero_of_mem_annihilator_pow I g₀
  let Jn : Ideal A := Module.annihilator A E ^ n
  have : Small.{v} (A ⧸ Jn) := small_power_quotient (Module.annihilator A E) n
  let _ : Module A (A ⧸ Jn) := Module.compHom (A ⧸ Jn) (Ideal.Quotient.mk Jn)
  let qlin : A →ₗ[A] (A ⧸ Jn) := {
    toFun := fun a => Ideal.Quotient.mk Jn a
    map_add' := fun a b => by simp
    map_smul' := fun _ _ => rfl }
  let f : I →ₗ[A] (A ⧸ Jn) := qlin.comp I.subtype
  have hker : f.ker ≤ g₀.ker := fun x hx => hn x (Ideal.Quotient.eq_zero_iff_mem.mp hx)
  let hbar : I ⧸ f.ker →ₗ[A] E := f.ker.liftQ g₀ hker
  let hRange : f.range →ₗ[A] E := hbar.comp f.quotKerEquivRange.symm.toLinearMap
  let eI : Shrink.{v} f.range ≃ₗ[A] f.range := Shrink.linearEquiv A f.range
  let eQ : Shrink.{v} (A ⧸ Jn) ≃ₗ[A] (A ⧸ Jn) := Shrink.linearEquiv A (A ⧸ Jn)
  let inc : Shrink.{v} f.range →ₗ[A] Shrink.{v} (A ⧸ Jn) :=
    eQ.symm.toLinearMap.comp (f.range.subtype.comp eI.toLinearMap)
  have hinc : Function.Injective inc := fun x y h =>
    eI.injective (f.range.subtype_injective (eQ.symm.injective h))
  obtain ⟨ext, hext⟩ := Module.Injective.out (Q := E) inc hinc (hRange.comp eI.toLinearMap)
  let extQ : (A ⧸ Jn) →ₗ[A] E := ext.comp eQ.symm.toLinearMap
  have hextQ (x : I) : extQ (f x) = g₀ x := by
    have hm : f x ∈ f.range := ⟨x, rfl⟩
    have hs := hext (eI.symm ⟨f x, hm⟩)
    simpa [extQ, inc, eI, eQ, hRange, hbar, LinearMap.comp_apply] using hs
  let extA : A →ₗ[A] E := extQ.comp qlin
  refine ⟨(ULift.moduleEquiv.symm.toLinearMap).comp extA, ?_⟩
  intro x hx
  apply ULift.ext
  simpa [extA, extQ, g₀, f, qlin, LinearMap.comp_apply] using hextQ ⟨x, hx⟩

/-- The `A[X]`-module structure on `Hom_A(A[X], N)` coinduced along `A → A[X]`: a polynomial `p`
acts on a linear map by precomposition with multiplication by `p`. -/
private instance coinducedModule' (A : Type u) [CommRing A] (N : Type (max u (max u v)))
    [AddCommGroup N] [Module A N] :
    Module (Polynomial A) (Polynomial A →ₗ[A] N) where
  smul p f := f.comp (LinearMap.mulLeft A p)
  one_smul f := by
    change f.comp (LinearMap.mulLeft A 1) = f
    ext q
    simp [LinearMap.comp_apply]
  mul_smul p q f := by
    apply LinearMap.ext
    intro r
    change f ((p * q) * r) = f (q * (p * r))
    congr 1
    ring
  smul_zero p := by
    change (0 : Polynomial A →ₗ[A] N).comp (LinearMap.mulLeft A p) = 0
    rfl
  smul_add p f g := by
    change (f + g).comp (LinearMap.mulLeft A p) =
      f.comp (LinearMap.mulLeft A p) + g.comp (LinearMap.mulLeft A p)
    ext q
    simp
  add_smul p q f := by
    apply LinearMap.ext
    intro r
    change f ((p + q) * r) = f (p * r) + f (q * r)
    rw [add_mul, map_add]
  zero_smul f := by
    change f.comp (LinearMap.mulLeft A 0) = 0
    ext q
    simp

private theorem coinduced_injective (A : Type u) [CommRing A] (N : Type (max u (max u v)))
    [AddCommGroup N] [Module A N] [Module.Injective.{u, max u (max u v)} A N] :
    Module.Injective.{u, max u (max u v)} (Polynomial A) (Polynomial A →ₗ[A] N) := by
  constructor
  intro X Y _ _ _ _ f hf g
  let _ : Module A X := Module.compHom X (algebraMap A (Polynomial A))
  let _ : Module A Y := Module.compHom Y (algebraMap A (Polynomial A))
  let _ : IsScalarTower A (Polynomial A) X := IsScalarTower.of_algebraMap_smul fun a x => rfl
  let _ : IsScalarTower A (Polynomial A) Y := IsScalarTower.of_algebraMap_smul fun a y => rfl
  let g0 : X →ₗ[A] (N : Type (max u (max u v))) := {
    toFun := fun x => g x 1
    map_add' := fun x y => by simp
    map_smul' := by
      intro a x
      calc
        g (a • x) 1 = g ((algebraMap A (Polynomial A) a) • x) 1 := by
          rw [IsScalarTower.algebraMap_smul]
        _ = ((algebraMap A (Polynomial A) a) • g x) 1 := by rw [map_smul]
        _ = g x ((algebraMap A (Polynomial A) a) * 1) := rfl
        _ = a • g x 1 := by
          rw [← Algebra.smul_def]
          exact (g x).map_smul a (1 : Polynomial A) }
  obtain ⟨h0, hh0⟩ := Module.Injective.out (f.restrictScalars A) hf g0
  let h : Y →ₗ[Polynomial A] (Polynomial A →ₗ[A] N) := {
    toFun := fun y => {
      toFun := fun b => h0 (b • y)
      map_add' := fun b c => by simp [add_smul, h0.map_add]
      map_smul' := fun a b => by simp [h0.map_smul] }
    map_add' := fun y z => by ext b; simp [h0.map_add]
    map_smul' := by
      intro b y
      apply LinearMap.ext
      intro c
      change h0 (c • (b • y)) = h0 ((b * c) • y)
      rw [smul_smul, mul_comm] }
  refine ⟨h, ?_⟩
  intro x
  apply LinearMap.ext
  intro b
  change h0 (b • f x) = g x b
  rw [← f.map_smul]
  change h0 ((f.restrictScalars A) (b • x)) = g x b
  rw [hh0 (b • x)]
  change g (b • x) 1 = g x b
  rw [map_smul]
  change ((g x).comp (LinearMap.mulLeft A b)) 1 = g x b
  simp [LinearMap.comp_apply]

/-- The `A[X]`-linear map `P → Hom_A(A[X], P)` sending `p` to `q ↦ q • p`. -/
private def coevalPoly (A : Type u) [CommRing A] (P : Type (max u v)) [AddCommGroup P]
    [Module A P] [Module (Polynomial A) P] [IsScalarTower A (Polynomial A) P] :
    P →ₗ[Polynomial A] (Polynomial A →ₗ[A] P) where
  toFun p :=
    { toFun := fun q => q • p
      map_add' := fun q r => add_smul q r p
      map_smul' := fun a q => by
        change (a • q) • p = a • (q • p)
        rw [Algebra.smul_def, mul_smul, IsScalarTower.algebraMap_smul] }
  map_add' p q := LinearMap.ext fun r => smul_add r p q
  map_smul' b p := LinearMap.ext fun q => by
    change q • (b • p) = (b * q) • p
    rw [smul_smul, mul_comm]

private lemma coevalPoly_apply (A : Type u) [CommRing A] (P : Type (max u v)) [AddCommGroup P]
    [Module A P] [Module (Polynomial A) P] [IsScalarTower A (Polynomial A) P]
    (p : P) (q : Polynomial A) :
    coevalPoly A P p q = q • p := rfl

/-- Multiplication by `X` on `P`, as an `A`-linear map. -/
private def mulXLin (A : Type u) [CommRing A] (P : Type (max u v)) [AddCommGroup P]
    [Module A P] [Module (Polynomial A) P] [IsScalarTower A (Polynomial A) P] :
    P →ₗ[A] P where
  toFun z := (Polynomial.X : Polynomial A) • z
  map_add' := smul_add _
  map_smul' a z := smul_comm _ a z

/-- The `A[X]`-linear map `f ↦ f ∘ X - X • f` on `Hom_A(A[X], P)`. -/
private def coinducedXSub (A : Type u) [CommRing A] (P : Type (max u v)) [AddCommGroup P]
    [Module A P] [Module (Polynomial A) P] [IsScalarTower A (Polynomial A) P] :
    (Polynomial A →ₗ[A] P) →ₗ[Polynomial A] (Polynomial A →ₗ[A] P) where
  toFun f := f.comp (LinearMap.mulLeft A (Polynomial.X : Polynomial A)) - (mulXLin A P).comp f
  map_add' f g := LinearMap.ext fun q => by
    change f (Polynomial.X * q) + g (Polynomial.X * q) -
        (Polynomial.X : Polynomial A) • (f q + g q) =
      (f (Polynomial.X * q) - (Polynomial.X : Polynomial A) • f q) +
        (g (Polynomial.X * q) - (Polynomial.X : Polynomial A) • g q)
    rw [smul_add]
    abel
  map_smul' b f := LinearMap.ext fun q => by
    change f (b * (Polynomial.X * q)) - (Polynomial.X : Polynomial A) • f (b * q) =
      f (Polynomial.X * (b * q)) - (Polynomial.X : Polynomial A) • f (b * q)
    rw [mul_left_comm]

private lemma coinducedXSub_apply (A : Type u) [CommRing A] (P : Type (max u v)) [AddCommGroup P]
    [Module A P] [Module (Polynomial A) P] [IsScalarTower A (Polynomial A) P]
    (f : Polynomial A →ₗ[A] P) (q : Polynomial A) :
    coinducedXSub A P f q = f (Polynomial.X * q) - (Polynomial.X : Polynomial A) • f q := rfl

private theorem coinducedXSub_comp_coevalPoly
    (A : Type u) [CommRing A] (P : Type (max u v)) [AddCommGroup P]
    [Module A P] [Module (Polynomial A) P] [IsScalarTower A (Polynomial A) P] :
    (coinducedXSub A P).comp (coevalPoly A P) = 0 :=
  LinearMap.ext fun p => LinearMap.ext fun q => by
    change (Polynomial.X * q) • p - (Polynomial.X : Polynomial A) • (q • p) = 0
    rw [smul_smul, sub_self]

private theorem exact_coevalPoly_coinducedXSub
    (A : Type u) [CommRing A] (P : Type (max u v)) [AddCommGroup P]
    [Module A P] [Module (Polynomial A) P] [IsScalarTower A (Polynomial A) P] :
    Function.Exact (coevalPoly A P) (coinducedXSub A P) := by
  intro f
  refine ⟨fun hf => ?_, ?_⟩
  · have hrec (q : Polynomial A) :
        f (Polynomial.X * q) = (Polynomial.X : Polynomial A) • f q := by
      have hh := LinearMap.congr_fun hf q
      change f (Polynomial.X * q) - (Polynomial.X : Polynomial A) • f q = 0 at hh
      exact sub_eq_zero.mp hh
    have hmon (n : ℕ) : f (Polynomial.monomial n (1 : A)) =
        Polynomial.monomial n (1 : A) • f 1 := by
      induction n with
      | zero => simp
      | succ n ih => rw [← Polynomial.X_mul_monomial, hrec, ih, smul_smul]
    exact ⟨f 1, ((Polynomial.basisMonomials A).ext fun n => by
      simpa [coevalPoly_apply] using hmon n).symm⟩
  · rintro ⟨p, rfl⟩
    exact LinearMap.congr_fun (coinducedXSub_comp_coevalPoly A P) p

private theorem coevalPoly_injective
    (A : Type u) [CommRing A] (P : Type (max u v)) [AddCommGroup P]
    [Module A P] [Module (Polynomial A) P] [IsScalarTower A (Polynomial A) P] :
    Function.Injective (coevalPoly A P) := fun p q h => by
  simpa [coevalPoly_apply] using LinearMap.congr_fun h 1

private theorem coinducedXSub_surjective
    (A : Type u) [CommRing A] (P : Type (max u v)) [AddCommGroup P]
    [Module A P] [Module (Polynomial A) P] [IsScalarTower A (Polynomial A) P] :
    Function.Surjective (coinducedXSub A P) := by
  intro g
  let basis := Polynomial.basisMonomials A
  let vals : ℕ → P := Nat.rec 0 fun n y =>
    g (Polynomial.monomial n (1 : A)) + (Polynomial.X : Polynomial A) • y
  obtain ⟨f, hval⟩ : ∃ f : Polynomial A →ₗ[A] P, ∀ n, f (basis n) = vals n :=
    ⟨basis.constr A vals, basis.constr_basis A vals⟩
  refine ⟨f, basis.ext fun n => ?_⟩
  have hstep : vals (n + 1) =
      g (Polynomial.monomial n 1) + (Polynomial.X : Polynomial A) • vals n := rfl
  have hmul : Polynomial.X * basis n = basis (n + 1) := by
    dsimp [basis]
    exact Polynomial.X_mul_monomial n (1 : A)
  have hb : basis n = Polynomial.monomial n (1 : A) := by
    dsimp [basis]
    exact congrFun (Polynomial.coe_basisMonomials A) n
  rw [coinducedXSub_apply, hmul, hval, hval, hstep, add_sub_cancel_right, hb]

private theorem polynomial_module_id_le_one
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Injective.{u, v} A E] :
    HasInjectiveDimensionLE
      (ModuleCat.of (Polynomial A) (PolynomialModule A (ULift.{u} E))) 1 := by
  let _ : Small.{max u v} A := small_lift.{u, v, u} A
  let _ : Module.Injective.{u, max u v} A (ULift.{u} E) := injective_ascend_noetherian E
  let P := PolynomialModule A (ULift.{u} E)
  let _ : Module.Injective.{u, max u v} A P := polyModule_injective (ULift.{u} E)
  let C := Polynomial A →ₗ[A] P
  let _ : Module (Polynomial A) C := coinducedModule' A P
  have hCobj : CategoryTheory.Injective (ModuleCat.of (Polynomial A) C) :=
    (Module.injective_iff_injective_object (Polynomial A) C).mp (coinduced_injective A P)
  let S := ModuleCat.shortComplexOfCompEqZero (coevalPoly A P) (coinducedXSub A P)
    (coinducedXSub_comp_coevalPoly A P)
  have hexactS := ModuleCat.shortComplex_shortExact S (exact_coevalPoly_coinducedXSub A P)
    (coevalPoly_injective A P) (coinducedXSub_surjective A P)
  have : CategoryTheory.Injective S.X₂ := hCobj
  have hX₃ : HasInjectiveDimensionLT S.X₃ 1 := injective_iff_hasInjectiveDimensionLT_one.mp hCobj
  change HasInjectiveDimensionLT (ModuleCat.of (Polynomial A) P) 2
  exact hexactS.hasInjectiveDimensionLT_X₁ 1 hX₃ inferInstance

private def polynomial_lift_equiv
    {A : Type u} [CommRing A]
    (E : Type v) [AddCommGroup E] [Module A E] :
    PolynomialModule A E ≃ₗ[Polynomial A] PolynomialModule A (ULift.{u} E) := by
  let e0 : E ≃ₗ[A] ULift.{u} E := ULift.moduleEquiv.symm
  let f : PolynomialModule A E →ₗ[A] PolynomialModule A (ULift.{u} E) :=
    PolynomialModule.map A e0.toLinearMap
  let g : PolynomialModule A (ULift.{u} E) →ₗ[A] PolynomialModule A E :=
    PolynomialModule.map A e0.symm.toLinearMap
  have hgf : g.comp f = LinearMap.id := by
    apply PolynomialModule.hom_ext
    intro n
    ext e
    simp [f, g]
  have hfg : f.comp g = LinearMap.id := by
    apply PolynomialModule.hom_ext
    intro n
    ext e
    simp [f, g]
  let fB : PolynomialModule A E →ₗ[Polynomial A] PolynomialModule A (ULift.{u} E) := {
    toFun := f
    map_add' := f.map_add
    map_smul' := by
      intro p q
      simpa [f, Polynomial.map_id] using PolynomialModule.map_smul A e0.toLinearMap p q }
  let gB : PolynomialModule A (ULift.{u} E) →ₗ[Polynomial A] PolynomialModule A E := {
    toFun := g
    map_add' := g.map_add
    map_smul' := by
      intro p q
      simpa [g, Polynomial.map_id] using PolynomialModule.map_smul A e0.symm.toLinearMap p q }
  exact {
    toFun := fB
    invFun := gB
    left_inv := by
      intro q
      have h := congrArg (fun k : PolynomialModule A E →ₗ[A] PolynomialModule A E => k q) hgf
      simpa [fB, gB] using h
    right_inv := by
      intro q
      have h := congrArg (fun k : PolynomialModule A (ULift.{u} E) →ₗ[A]
        PolynomialModule A (ULift.{u} E) => k q) hfg
      simpa [fB, gB] using h
    map_add' := fB.map_add
    map_smul' := fB.map_smul }

private theorem tensor_polynomial_id_le_one
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Injective.{u, v} A E] :
    HasInjectiveDimensionLE
      (ModuleCat.of (Polynomial A) (TensorProduct A (Polynomial A) E)) 1 := by
  let _ : Small.{max u v} (Polynomial A) := small_lift.{u, max u v, u} (Polynomial A)
  let e₀ := PolynomialModule.polynomialTensorProductLEquivPolynomialModule A E
  let e₁ := PolynomialModule.polynomialTensorProductLEquivPolynomialModule A (ULift.{u} E)
  let e : TensorProduct A (Polynomial A) E ≃ₗ[Polynomial A]
      TensorProduct A (Polynomial A) (ULift.{u} E) :=
    e₀.trans ((polynomial_lift_equiv E).trans e₁.symm)
  have hLift : HasInjectiveDimensionLE
      (ModuleCat.of (Polynomial A) (TensorProduct A (Polynomial A) (ULift.{u} E))) 1 :=
    (ModuleCat.hasInjectiveDimensionLE_iff_of_linearEquiv e₁ 1).mpr
      (polynomial_module_id_le_one E)
  exact (ModuleCat.hasInjectiveDimensionLE_iff_of_linearEquiv e 1).mpr hLift

/-- **Stacks Project, Tag 0A6J.** Extending an injective module over a Noetherian ring to the
one-variable polynomial ring gives a module of injective dimension at most one. -/
@[stacks 0A6J]
theorem tensorProduct_polynomial_hasInjectiveDimensionLE
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Injective A E] :
    HasInjectiveDimensionLE
      (ModuleCat.of (Polynomial A) (TensorProduct A (Polynomial A) E)) 1 := by
  exact tensor_polynomial_id_le_one (A := A) E

end

end Polynomial

end Module

end
