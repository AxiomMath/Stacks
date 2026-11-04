module

public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.RingTheory.LocalCohomology.ModulesSupportedIn
public import StacksCore.Tactic.StacksAttribute

/-!
# Matlis theory: the supported part of an injective module

Let `A` be a Noetherian ring and `T ⊆ Spec(A)` a subset stable under specialization. By Matlis'
structure theory an injective `A`-module `E` decomposes as a direct sum of injective hulls
`E(κ(p))` of residue fields, one indecomposable summand for each point `p` of the spectrum
occurring in it. The point of this file is that the degree-zero sections with support in `T`,
`Γ_T(E) = H⁰_T(E)`, simply select the summands whose point lies in `T`: for an injective hull of
`κ(p)` the whole module is `p`-power torsion, so `Γ_T` of it is everything when `p ∈ T` and zero
otherwise. The selection is an idempotent `A`-linear projection of `E` with image `Γ_T(E)`, so
`Γ_T(E)` is a direct summand of `E` and therefore again injective.

Consequently every `A`-module supported in `T` embeds into an injective module which is itself
supported in `T`: take an injective hull `E` of the module and pass to `Γ_T(E)`. This is the
covering property that makes the bounded comparison between the derived category of modules
supported in `T` and the derived category of complexes with cohomology supported in `T` work; see
`StacksFrontier.Algebra.Module.Matlis.DerivedPlusComparison`.

## Main results

* `Module.primaryComponent_eq_top_of_isInjectiveHull_residueField` — an injective hull of the
  residue field at a prime `p` is `p`-power torsion.
* `Stacks.LocalCohomology.support_subset_of_isInjectiveHull_residueField` — such a hull is
  supported in any specialization-stable set containing `p`.
* `Stacks.LocalCohomology.sectionsWithSupportIn_eq_top_of_isInjectiveHull_residueField` and
  `Stacks.LocalCohomology.sectionsWithSupportIn_eq_bot_of_isInjectiveHull_residueField` — the
  sections with support in `T` of such a hull are everything or zero according as `p ∈ T`.
* `Stacks.LocalCohomology.injective_sectionsWithSupportIn` — over a Noetherian ring, the sections
  with support in a specialization-stable set of an injective module form an injective module.
* `Stacks.LocalCohomology.exists_injective_supported_envelope` — a module supported in `T` embeds
  into an injective module supported in `T`.

## References

* [Stacks Project, Tag 08YA](https://stacks.math.columbia.edu/tag/08YA)
* [Stacks Project, Tag 0EEZ](https://stacks.math.columbia.edu/tag/0EEZ)
* [Stacks Project, Tag 0EF2](https://stacks.math.columbia.edu/tag/0EF2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u v

namespace Module

variable {R : Type u} [CommRing R]

/-- An essential monomorphism meets the line spanned by any nonzero element of its target: some
multiple of that element is a nonzero element of the image. -/
public lemma exists_smul_mem_range_of_isEssentialMono
    {M N : ModuleCat.{v} R} (i : M ⟶ N) [Mono i]
    (hi : Module.IsEssentialMono i) {x : N} (hx : x ≠ 0) :
    ∃ a : R, a • x ∈ LinearMap.range i.hom ∧ a • x ≠ 0 := by
  let P : Submodule R N := R ∙ x
  have hP : P ≠ ⊥ := Submodule.span_singleton_eq_bot.not.mpr hx
  have hcat := hi ((ModuleCat.subobjectModule N).symm P) (by
    intro hbot
    apply hP
    have hbot' := congrArg (ModuleCat.subobjectModule N) hbot
    rw [(ModuleCat.subobjectModule N).apply_symm_apply,
      (ModuleCat.subobjectModule N).map_bot] at hbot'
    exact hbot')
  have hrange : (ModuleCat.subobjectModule N) (Subobject.mk i) = LinearMap.range i.hom := by
    let e : M ≃ₗ[R] LinearMap.range i.hom :=
      LinearEquiv.ofInjective i.hom ((ModuleCat.mono_iff_injective i).mp inferInstance)
    have hs : (ModuleCat.subobjectModule N).symm (LinearMap.range i.hom) = Subobject.mk i := by
      show Subobject.mk (ModuleCat.ofHom (LinearMap.range i.hom).subtype) = Subobject.mk i
      apply Subobject.mk_eq_mk_of_comm _ _ e.symm.toModuleIso
      ext x
      simp [e]
    rw [← hs, (ModuleCat.subobjectModule N).apply_symm_apply]
  have hmeet : P ⊓ LinearMap.range i.hom ≠ ⊥ := by
    intro hbot
    have hbot' := congrArg (ModuleCat.subobjectModule N).symm hbot
    rw [(ModuleCat.subobjectModule N).symm.map_inf, ← hrange,
      (ModuleCat.subobjectModule N).symm_apply_apply,
      (ModuleCat.subobjectModule N).symm.map_bot] at hbot'
    exact hcat hbot'
  obtain ⟨y, hy⟩ := Submodule.nonzero_mem_of_bot_lt ((bot_lt_iff_ne_bot).2 hmeet)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (Submodule.mem_inf.mp y.2).1
  refine ⟨a, ?_, ?_⟩
  · simpa [ha] using (Submodule.mem_inf.mp y.2).2
  · exact fun hzero => hy (Subtype.ext (by simpa [ha] using hzero))

/-- A monomorphism containing an essential subobject in its image is itself essential. -/
private lemma isEssentialMono_of_subobject_mk_le
    {C : Type*} [Category C] [HasZeroObject C] [HasPullbacks C]
    {K P E : C} (i : K ⟶ E) (j : P ⟶ E) [Mono i] [Mono j]
    (hi : Module.IsEssentialMono i) (hij : Subobject.mk i ≤ Subobject.mk j) :
    Module.IsEssentialMono j := by
  intro q hq hj
  exact hi q hq (bot_unique ((inf_le_inf_left q hij).trans_eq hj))

/-- An essential monomorphism of modules admitting a retraction is surjective. -/
public lemma surjective_of_isEssentialMono_of_comp_eq_id {P E : ModuleCat.{v} R} (j : P ⟶ E)
    [Mono j] (hj : Module.IsEssentialMono j) (r : E ⟶ P) (hr : j ≫ r = 𝟙 _) :
    Function.Surjective j.hom := by
  have hr' : r.hom.comp j.hom = LinearMap.id := by
    simpa using congrArg (fun f : P ⟶ P => f.hom) hr
  have hleft (y : P) : r.hom (j.hom y) = y := by
    simpa using congrArg (fun f : P →ₗ[R] P => f y) hr'
  have hker (x : E) (hx : r.hom x = 0) : x = 0 := by
    by_contra hx0
    obtain ⟨a, ha, hane⟩ := exists_smul_mem_range_of_isEssentialMono j hj hx0
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp ha
    have hy0 : y = 0 := by rw [← hleft y, hy, map_smul, hx, smul_zero]
    exact hane (by rw [← hy, hy0, map_zero])
  intro x
  refine ⟨r.hom x, ?_⟩
  have hzero : r.hom (x - j.hom (r.hom x)) = 0 := by
    simp [LinearMap.map_sub, hleft]
  exact (sub_eq_zero.mp (hker _ hzero)).symm

/-- Elements of the prime `p` kill every element of a module identified with the residue field. -/
private lemma smul_eq_zero_of_linearEquiv_residueField (p : Ideal R) [p.IsPrime]
    {K : Type*} [AddCommGroup K] [Module R K] (e : K ≃ₗ[R] p.ResidueField) {r : R} (hr : r ∈ p)
    (y : K) : r • y = 0 := by
  apply e.injective
  rw [map_smul, Algebra.smul_def, Ideal.algebraMap_residueField_eq_zero.mpr hr, zero_mul,
    map_zero]

/-- **Matlis theory (Stacks 08YA).** An injective hull of the residue field at a prime `p` is
`p`-power torsion: the `p`-primary component is the whole module.

The `p`-primary component is an injective submodule containing the embedded residue field, hence
an essential submodule, hence a direct summand along an injection; the retraction has trivial
kernel, so the inclusion is onto. -/
theorem primaryComponent_eq_top_of_isInjectiveHull_residueField [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (K E : ModuleCat.{v} R)
    (e : K ≃ₗ[R] p.ResidueField) (i : K ⟶ E) [Mono i]
    (hE : Module.IsInjectiveHull i) :
    Ideal.primaryComponent E p = ⊤ := by
  let P : Submodule R E := Ideal.primaryComponent E p
  have hEInj : Module.Injective R E := (Module.injective_iff_injective_object R E).mpr hE.1
  let : Module.Injective R E := hEInj
  have hPInj : Module.Injective R P := Module.injective_primaryComponent E p
  let : CategoryTheory.Injective (ModuleCat.of R P) :=
    (Module.injective_iff_injective_object R (ModuleCat.of R P)).mp hPInj
  have hmem (x : K) : i.hom x ∈ P := by
    rw [show P = Ideal.primaryComponent E p from rfl, Ideal.primaryComponent_mem]
    refine ⟨1, ?_⟩
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    have ha : (a : R) ∈ p := by simpa using a.property
    rw [← i.hom.map_smul, smul_eq_zero_of_linearEquiv_residueField p e ha, map_zero]
  let g : K ⟶ ModuleCat.of R P := ModuleCat.ofHom (i.hom.codRestrict P hmem)
  let j : ModuleCat.of R P ⟶ E := ModuleCat.ofHom P.subtype
  have : Mono j := (ModuleCat.mono_iff_injective j).2 P.subtype_injective
  have hfac : i = g ≫ j := by ext x; rfl
  have hle : Subobject.mk i ≤ Subobject.mk j := Subobject.mk_le_mk_of_comm g hfac
  have hess := isEssentialMono_of_subobject_mk_le i j hE.2 hle
  calc
    Ideal.primaryComponent E p = LinearMap.range P.subtype := P.range_subtype.symm
    _ = ⊤ := LinearMap.range_eq_top.mpr (surjective_of_isEssentialMono_of_comp_eq_id j hess
      (Injective.factorThru (𝟙 _) j) (Injective.comp_factorThru _ _))

/-- The range of an idempotent endomorphism of an injective module is injective, being a direct
summand. -/
private lemma injective_range_of_comp_self_eq {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Injective R M] (p : M →ₗ[R] M) (hp : p.comp p = p) :
    Module.Injective R p.range := by
  let j : p.range →ₗ[R] M := p.range.subtype
  let r : M →ₗ[R] p.range := p.codRestrict p.range (fun x => ⟨x, rfl⟩)
  have hrj : r.comp j = LinearMap.id := by
    ext y
    obtain ⟨x, hx⟩ := y.property
    show p y.val = y.val
    rw [← hx]
    exact LinearMap.congr_fun hp x
  refine ⟨?_⟩
  intro X Y _ _ _ _ f hf g
  obtain ⟨g', hg'⟩ := Module.Injective.out (R := R) (Q := M) f hf (j.comp g)
  exact ⟨r.comp g', fun x => (congrArg r (hg' x)).trans (LinearMap.congr_fun hrj (g x))⟩

end Module

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R]

/-- **Stacks Project, Tag 08YA.** An injective hull of the residue field at a prime `p` is
supported in any specialization-stable subset of the spectrum containing `p`. -/
theorem support_subset_of_isInjectiveHull_residueField [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (K E : ModuleCat.{v} R)
    (e : K ≃ₗ[R] p.ResidueField) (i : K ⟶ E) [Mono i]
    (hE : Module.IsInjectiveHull i) (T : Set (PrimeSpectrum R))
    (hT : StableUnderSpecialization T) (hpT : (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum R) ∈ T) :
    Module.support R E ⊆ T := by
  have hpc := Module.primaryComponent_eq_top_of_isInjectiveHull_residueField p K E e i hE
  intro q hq
  obtain ⟨x, hx⟩ := Module.mem_support_iff_exists_annihilator.mp hq
  rw [Ideal.annihilator_span_singleton_eq_torsionOf] at hx
  have hxm : x ∈ Ideal.primaryComponent E p := by simp [hpc]
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem E p x).mp hxm
  have hpow : p ^ n ≤ Ideal.torsionOf R E x := by
    intro a ha
    show a • x = 0
    simp only [Submodule.mem_torsionBySet_iff] at hn
    exact hn ⟨a, ha⟩
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    have htop : (⊤ : Ideal R) ≤ q.asIdeal := by simpa using hpow.trans hx
    exact q.2.ne_top (top_unique htop)
  have hpq : p ≤ q.asIdeal := (q.2.pow_le_iff hn0).mp (hpow.trans hx)
  exact hT (PrimeSpectrum.le_iff_specializes (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum R) q |>.mp hpq) hpT

/-- **Stacks Project, Tag 08YA.** If `p` lies in a specialization-stable set `T`, then an
injective hull of the residue field at `p` consists entirely of sections with support in `T`. -/
theorem sectionsWithSupportIn_eq_top_of_isInjectiveHull_residueField [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (K E : ModuleCat.{v} R)
    (e : K ≃ₗ[R] p.ResidueField) (i : K ⟶ E) [Mono i]
    (hE : Module.IsInjectiveHull i) (T : Set (PrimeSpectrum R))
    (hT : StableUnderSpecialization T) (hpT : (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum R) ∈ T) :
    sectionsWithSupportIn R T E = ⊤ :=
  (sectionsWithSupportIn_eq_top_iff R T E).2
    (support_subset_of_isInjectiveHull_residueField p K E e i hE T hT hpT)

/-- A nonzero element of a module identified with the residue field at `p` has annihilator `p`. -/
public lemma torsionOf_eq_of_linearEquiv_residueField (p : Ideal R) [p.IsPrime]
    {K : Type*} [AddCommGroup K] [Module R K] (e : K ≃ₗ[R] p.ResidueField) {y : K}
    (hy : y ≠ 0) : Ideal.torsionOf R K y = p := by
  ext r
  rw [Ideal.mem_torsionOf_iff]
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · have her : (algebraMap R p.ResidueField r) * e y = 0 := by
      simpa [Algebra.smul_def] using congrArg e hr
    by_contra hrp
    have hmap : algebraMap R p.ResidueField r ≠ 0 := fun hz =>
      hrp (Ideal.algebraMap_residueField_eq_zero.mp hz)
    have hey : e y ≠ 0 := fun h => hy (e.injective (by simpa using h))
    exact (mul_ne_zero hmap hey) her
  · exact Module.smul_eq_zero_of_linearEquiv_residueField p e hr y

/-- A linear map does not shrink the annihilator ideal of an element: `r • x = 0` gives
`r • f x = 0`. -/
private lemma torsionOf_le_torsionOf_map {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (x : M) :
    Ideal.torsionOf R M x ≤ Ideal.torsionOf R N (f x) := fun a ha => by
  rw [Ideal.mem_torsionOf_iff] at ha ⊢
  rw [← map_smul, ha, map_zero]

/-- An injective linear map preserves the annihilator ideal of an element. -/
private lemma torsionOf_map_eq_of_injective {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {f : M →ₗ[R] N} (hf : Function.Injective f) (x : M) :
    Ideal.torsionOf R N (f x) = Ideal.torsionOf R M x :=
  le_antisymm (fun a ha => hf (by simpa [Ideal.mem_torsionOf_iff] using ha))
    (torsionOf_le_torsionOf_map f x)

/-- **Stacks Project, Tag 08YA.** If `p` does not lie in `T`, then an injective hull of the
residue field at `p` has no nonzero section with support in `T`.

A nonzero such section has a nonzero multiple in the embedded residue field, and the annihilator
of a nonzero element of the residue field is exactly `p`; so `p` would belong to `T`. -/
theorem sectionsWithSupportIn_eq_bot_of_isInjectiveHull_residueField [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (K E : ModuleCat.{v} R)
    (e : K ≃ₗ[R] p.ResidueField) (i : K ⟶ E) [Mono i]
    (hE : Module.IsInjectiveHull i) (T : Set (PrimeSpectrum R))
    (hpT : (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum R) ∉ T) :
    sectionsWithSupportIn R T E = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
  by_contra hx0
  obtain ⟨a, ha, hane⟩ := Module.exists_smul_mem_range_of_isEssentialMono i hE.2 hx0
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp ha
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hane (by rw [← hy, map_zero])
  have hxT := (mem_sectionsWithSupportIn_iff R T E x).mp hx
  have hsmul := torsionOf_le_torsionOf_map (LinearMap.lsmul R E a) x
  have hiy := torsionOf_map_eq_of_injective ((ModuleCat.mono_iff_injective i).mp inferInstance) y
  rw [hy] at hiy
  refine hpT (hxT ?_)
  rw [PrimeSpectrum.mem_zeroLocus]
  exact hsmul.trans (le_of_eq (hiy.trans (torsionOf_eq_of_linearEquiv_residueField p e hy0)))

/-- The image of a module supported in `T` consists of sections with support in `T`. -/
theorem mem_sectionsWithSupportIn_of_support_subset (T : Set (PrimeSpectrum R))
    (M E : ModuleCat.{v} R) (i : M ⟶ E) (hM : Module.support R M ⊆ T) (x : M) :
    i.hom x ∈ sectionsWithSupportIn R T E := by
  have ht := torsionOf_le_torsionOf_map i.hom x
  rw [mem_sectionsWithSupportIn_iff]
  intro q hq
  rw [PrimeSpectrum.mem_zeroLocus] at hq
  refine hM (Module.mem_support_iff_exists_annihilator.mpr ⟨x, ?_⟩)
  rw [Ideal.annihilator_span_singleton_eq_torsionOf]
  exact ht.trans hq

/-- The sections with support in `T` form a module supported in `T`. -/
theorem support_sectionsWithSupportIn_subset (T : Set (PrimeSpectrum R)) (E : ModuleCat.{v} R) :
    Module.support R (sectionsWithSupportIn R T E) ⊆ T := by
  let P := sectionsWithSupportIn R T E
  have ht (x : P) : Ideal.torsionOf R P x = Ideal.torsionOf R E x.val :=
    (torsionOf_map_eq_of_injective (f := P.subtype) P.subtype_injective x).symm
  intro q hq
  obtain ⟨x, hx⟩ := Module.mem_support_iff_exists_annihilator.mp hq
  rw [Ideal.annihilator_span_singleton_eq_torsionOf] at hx
  refine (mem_sectionsWithSupportIn_iff R T E x.val).mp x.property ?_
  rw [PrimeSpectrum.mem_zeroLocus, ← ht]
  exact hx

/-- Sections with support in `T` of a direct sum are computed coordinatewise. -/
theorem mem_sectionsWithSupportIn_directSum_iff {ι : Type v} (T : Set (PrimeSpectrum R))
    (M : ι → Type (max u v)) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (x : ⨁ i, M i) :
    x ∈ sectionsWithSupportIn R T (⨁ i, M i) ↔
      ∀ i, x i ∈ sectionsWithSupportIn R T (M i) := by
  classical
  refine ⟨fun hx i => ?_, fun hx => ?_⟩
  · rw [mem_sectionsWithSupportIn_iff]
    intro q hq
    have hle := torsionOf_le_torsionOf_map (DirectSum.component R ι M i) x
    refine (mem_sectionsWithSupportIn_iff R T (⨁ j, M j) x).mp hx ?_
    rw [PrimeSpectrum.mem_zeroLocus]
    exact le_trans hle hq
  · have hterm (i : ι) : DirectSum.of M i (x i) ∈ sectionsWithSupportIn R T (⨁ j, M j) := by
      let S := sectionsWithSupportIn R T (M i)
      let f : ModuleCat.of R S ⟶ ModuleCat.of R (⨁ j, M j) :=
        ModuleCat.ofHom ((DirectSum.lof R ι M i).comp S.subtype)
      exact mem_sectionsWithSupportIn_of_support_subset T (ModuleCat.of R S)
        (ModuleCat.of R (⨁ j, M j)) f
        (support_sectionsWithSupportIn_subset T (ModuleCat.of R (M i))) ⟨x i, hx i⟩
    rw [← DirectSum.sum_support_of x]
    exact Submodule.sum_mem _ fun i _ => hterm i

/-- An isomorphism of modules restricts to a linear equivalence between the sections with support
in `T`. -/
public def sectionsWithSupportInEquivOfIso (T : Set (PrimeSpectrum R)) {E D : ModuleCat.{v} R}
    (e : E ≅ D) : sectionsWithSupportIn R T E ≃ₗ[R] sectionsWithSupportIn R T D :=
  LinearEquiv.ofLinearMap
    ((e.hom.hom.comp (sectionsWithSupportIn R T E).subtype).codRestrict
      (sectionsWithSupportIn R T D) fun x =>
        mem_sectionsWithSupportIn_of_support_subset T
          (ModuleCat.of R (sectionsWithSupportIn R T E)) D
          (ModuleCat.ofHom (e.hom.hom.comp (sectionsWithSupportIn R T E).subtype))
          (support_sectionsWithSupportIn_subset T E) x)
    ((e.inv.hom.comp (sectionsWithSupportIn R T D).subtype).codRestrict
      (sectionsWithSupportIn R T E) fun x =>
        mem_sectionsWithSupportIn_of_support_subset T
          (ModuleCat.of R (sectionsWithSupportIn R T D)) E
          (ModuleCat.ofHom (e.inv.hom.comp (sectionsWithSupportIn R T D).subtype))
          (support_sectionsWithSupportIn_subset T D) x)
    (LinearMap.ext fun _ => Subtype.ext (by simp))
    (LinearMap.ext fun _ => Subtype.ext (by simp))

/-- If the sections with support in `T` of each summand of an injective direct sum are everything
or zero according to a predicate `P`, then the sections with support in `T` of the direct sum are
injective: they are the range of the idempotent projecting onto the summands satisfying `P`. -/
public lemma injective_sectionsWithSupportIn_directSum {ι : Type v} (T : Set (PrimeSpectrum R))
    (M : ι → Type (max u v)) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [Module.Injective R (⨁ i, M i)] (P : ι → Prop) [DecidablePred P]
    (hM : ∀ i, sectionsWithSupportIn R T (M i) = if P i then ⊤ else ⊥) :
    Module.Injective R (sectionsWithSupportIn R T (⨁ i, M i)) := by
  classical
  let pr : (⨁ i, M i) →ₗ[R] ⨁ i, M i :=
    DirectSum.lmap fun i => if P i then LinearMap.id else 0
  have hpr : pr.comp pr = pr := by
    apply DirectSum.linearMap_ext
    intro i
    ext x
    by_cases hi : P i <;> simp [pr, hi]
  have hfixed (x : ⨁ i, M i) : x ∈ sectionsWithSupportIn R T (⨁ i, M i) ↔ pr x = x := by
    rw [mem_sectionsWithSupportIn_directSum_iff]
    refine ⟨fun hx => ?_, fun hx i => ?_⟩
    · ext i
      by_cases hi : P i
      · simp [pr, hi]
      · have hxi := hx i
        rw [hM i] at hxi
        have hx0 : x i = 0 := by simpa [hi] using hxi
        simp [pr, hi, hx0]
    · rw [hM i]
      by_cases hi : P i
      · simp [hi]
      · have hcoord : (pr x) i = x i := congrArg (fun z : ⨁ j, M j => z i) hx
        have hx0 : x i = 0 := by simpa [pr, hi] using hcoord.symm
        simp [hi, hx0]
  have hRange : pr.range = sectionsWithSupportIn R T (⨁ i, M i) := by
    ext x
    refine ⟨?_, fun hx => ⟨x, (hfixed x).1 hx⟩⟩
    rintro ⟨y, rfl⟩
    exact (hfixed _).2 (by simpa using LinearMap.congr_fun hpr y)
  rw [← hRange]
  exact Module.injective_range_of_comp_self_eq pr hpr

/-- The data exhibiting an indecomposable injective module as an injective hull of a residue
field, as produced by Matlis' structure theorem. -/
private structure ResidueHullWitness (E : ModuleCat.{max u v} R) where
  /-- The associated prime. -/
  p : Ideal R
  /-- Primality of the associated prime. -/
  hp : p.IsPrime
  /-- A model of the residue field in the module universe. -/
  K : ModuleCat.{max u v} R
  /-- Its identification with the residue field. -/
  e : K ≃ₗ[R] p.ResidueField
  /-- The embedding of the residue field. -/
  i : K ⟶ E
  /-- The embedding is a monomorphism. -/
  hi : Mono i
  /-- The embedding exhibits `E` as an injective hull. -/
  hull : letI : Mono i := hi; Module.IsInjectiveHull i

private lemma nonempty_residueHullWitness [IsNoetherianRing R] (E : ModuleCat.{max u v} R)
    [CategoryTheory.Injective E] (hE : Indecomposable E) :
    Nonempty (ResidueHullWitness.{u, v} E) := by
  obtain ⟨p, K, ⟨e⟩, i, hi, hh⟩ :=
    Module.exists_isInjectiveHull_residueField_of_indecomposable R E hE
  exact ⟨⟨p.asIdeal, p.2, K, e, i, hi, hh⟩⟩

/-- **Stacks Project, Tag 08YA.** Over a Noetherian ring, the sections with support in a
specialization-stable subset `T` of the spectrum of an injective module form an injective module.

Decompose the injective module into indecomposable injectives (Matlis), each an injective hull of
a residue field. The sections with support in `T` of a summand are everything or zero according as
the summand's prime lies in `T`, so the sections with support in `T` of the whole are the range of
the idempotent projecting onto the summands with prime in `T`; a direct summand of an injective
module is injective. -/
theorem injective_sectionsWithSupportIn [IsNoetherianRing R] (T : Set (PrimeSpectrum R))
    (hT : StableUnderSpecialization T) (E : ModuleCat.{max u v} R)
    [CategoryTheory.Injective E] :
    Module.Injective R (sectionsWithSupportIn R T E) := by
  classical
  obtain ⟨ι, F, e, hFI, hF⟩ := Module.exists_iso_directSum_of_injective R E
  let data : ∀ i, ResidueHullWitness.{u, v} (F i) := fun i => by
    let : CategoryTheory.Injective (F i) := hFI i
    exact Classical.choice (nonempty_residueHullWitness (F i) (hF i))
  let point (i : ι) : PrimeSpectrum R := ⟨(data i).p, (data i).hp⟩
  let D : ModuleCat.{max u v} R := ModuleCat.of R (⨁ i, (F i : Type _))
  let : CategoryTheory.Injective D :=
    CategoryTheory.Injective.of_iso e (inferInstance : CategoryTheory.Injective E)
  let : Module.Injective R (⨁ i, (F i : Type _)) :=
    (Module.injective_iff_injective_object R D).mpr (inferInstance : CategoryTheory.Injective D)
  have hΓi (i : ι) : sectionsWithSupportIn R T (F i) = if point i ∈ T then ⊤ else ⊥ := by
    let : (data i).p.IsPrime := (data i).hp
    let : Mono (data i).i := (data i).hi
    by_cases hi : point i ∈ T
    · simpa [hi, point] using sectionsWithSupportIn_eq_top_of_isInjectiveHull_residueField
        (data i).p (data i).K (F i) (data i).e (data i).i (data i).hull T hT hi
    · simpa [hi, point] using sectionsWithSupportIn_eq_bot_of_isInjectiveHull_residueField
        (data i).p (data i).K (F i) (data i).e (data i).i (data i).hull T hi
  have hΓD := injective_sectionsWithSupportIn_directSum T (fun i => (F i : Type _))
    (fun i => point i ∈ T) hΓi
  exact (Module.injective_iff_injective_object R _).mpr
    (CategoryTheory.Injective.of_iso (sectionsWithSupportInEquivOfIso T e).toModuleIso.symm
      ((Module.injective_iff_injective_object R _).mp hΓD))

/-- **Stacks Project, Tag 0EF2 (covering step).** Over a Noetherian ring, a module supported in a
specialization-stable subset `T` of the spectrum embeds into an injective module which is itself
supported in `T`: take the sections with support in `T` of an injective hull. -/
theorem exists_injective_supported_envelope [IsNoetherianRing R] (T : Set (PrimeSpectrum R))
    (hT : StableUnderSpecialization T) (X : ModulesSupportedIn.{u, max u v} R T) :
    ∃ J : ModuleCat.{max u v} R, supportModuleProperty.{u, max u v} R T J ∧
      ∃ i : X.1 ⟶ J, Mono i ∧ CategoryTheory.Injective (ModuleCat.of R (↑J)) := by
  classical
  obtain ⟨E, i, hi, hE⟩ := Module.exists_isInjectiveHull R X.1
  let : Mono i := hi
  let : CategoryTheory.Injective E := hE.1
  let J : ModuleCat.{max u v} R := ModuleCat.of R (sectionsWithSupportIn R T E)
  let k : X.1 ⟶ J := ModuleCat.ofHom
    (i.hom.codRestrict _ (fun x =>
      mem_sectionsWithSupportIn_of_support_subset T X.1 E i X.2 x))
  have hk : Mono k := by
    refine (ModuleCat.mono_iff_injective k).2 fun x y hxy => ?_
    exact (ModuleCat.mono_iff_injective i).1 hi (congrArg Subtype.val hxy)
  exact ⟨J, support_sectionsWithSupportIn_subset T E, k, hk,
    (Module.injective_iff_injective_object R (↑J)).mp (injective_sectionsWithSupportIn T hT E)⟩

end Stacks.LocalCohomology
