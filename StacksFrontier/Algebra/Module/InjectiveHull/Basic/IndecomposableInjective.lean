module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Module
public import StacksCore.Algebra.Category.ModuleCat.Localization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Essential
public import StacksFrontier.Algebra.Module.InjectiveHull.Injective
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic.Existence

/-!
# Indecomposable injective modules

Over a Noetherian ring the injective modules admit a classification. An indecomposable injective
module `E` is an injective hull of each of its nonzero submodules; its endomorphism ring is local,
with maximal ideal the endomorphisms having nonzero kernel; the scalars acting non-injectively on
`E` form a prime ideal `p`, and `E` is the injective hull of the residue field `κ(p)`. Conversely
the injective hull of `R ⧸ p` is indecomposable. Power-torsion submodules of an injective module
are again injective.

## Main results

* `Module.Subobject.isInjectiveHull_arrow_of_indecomposable` — an indecomposable injective module
  is an injective hull of each of its nonzero submodules.
* `Module.endomorphismRing_isLocalRing` — the endomorphism ring of an indecomposable injective
  module is local.
* `Module.exists_prime_eq_zeroDivisorsOn` — the zerodivisors on an indecomposable injective module
  form a prime ideal.
* `Module.indecomposable_of_isInjectiveHull_quotient` — the injective hull of `R ⧸ p` is
  indecomposable.
* `Module.exists_isInjectiveHull_residueField_of_indecomposable` — over a Noetherian ring, every
  indecomposable injective module is an injective hull of a residue field.
* `Module.injective_primaryComponent` — ideal-power torsion in an injective module is injective.

## References

* [Stacks Project, Tag 08XW](https://stacks.math.columbia.edu/tag/08XW)
* [Stacks Project, Tag 08Y7](https://stacks.math.columbia.edu/tag/08Y7)
* [Stacks Project, Tag 08Y8](https://stacks.math.columbia.edu/tag/08Y8)
* [Stacks Project, Tag 08Y9](https://stacks.math.columbia.edu/tag/08Y9)
-/

@[expose] public section

open CategoryTheory

namespace Module

universe u v w

/-! ### Indecomposable injective modules

An indecomposable injective module is an injective hull of each of its nonzero submodules, and
consequently any two of its nonzero submodules meet. Submodules are represented by subobjects of
`ModuleCat`; their canonical inclusions are therefore the arrows of those subobjects. -/

/-- A submodule is nonzero exactly when the corresponding subobject is nonzero. -/
private lemma subobjectModule_symm_ne_bot {R : Type u} [Ring R] (E : ModuleCat.{v} R)
    (A : Submodule R E) : (ModuleCat.subobjectModule E).symm A ≠ ⊥ ↔ A ≠ ⊥ :=
  not_congr (map_eq_bot_iff _)

/-- The inclusion of any nonzero submodule of an indecomposable injective module exhibits the
ambient module as its injective hull. -/
@[stacks 08Y7 "injective_hull"]
lemma Subobject.isInjectiveHull_arrow_of_indecomposable
    (R : Type u) [Ring R] (E : ModuleCat.{v} R) [CategoryTheory.Injective E]
    (hE : Indecomposable E) (M : Subobject E) (hM : M ≠ ⊥) :
    IsInjectiveHull M.arrow := by
  have : Module.Injective R E := Module.injective_module_of_injective_object R E
  obtain ⟨A, hAM⟩ : ∃ A : Submodule R E, (ModuleCat.subobjectModule E).symm A = M :=
    ⟨ModuleCat.subobjectModule E M, (ModuleCat.subobjectModule E).symm_apply_apply M⟩
  have hAne : A ≠ ⊥ := (subobjectModule_symm_ne_bot E A).1 (hAM ▸ hM)
  -- A maximal essential extension `C` of `A` inside `E` is injective, hence a direct summand of
  -- `E`; indecomposability forces the complement to vanish, so `C = ⊤` and `A` is essential in
  -- the whole of `E`.
  obtain ⟨C, hAC, hessC, hCinj⟩ := exists_injective_essential_extension A
  have hCne : C ≠ ⊥ := fun h => hAne (le_bot_iff.mp (hAC.trans h.le))
  have : Module.Injective R C := hCinj
  obtain ⟨K, e, he⟩ := exists_linearEquiv_prod_of_injective C.subtype C.subtype_injective
  have hsplit : E ≅ ModuleCat.of R C ⊞ ModuleCat.of R K :=
    e.toModuleIso ≪≫ (ModuleCat.biprodIsoProd (ModuleCat.of R C) (ModuleCat.of R K)).symm
  have hCtop : C = ⊤ := by
    rcases hE.2 (ModuleCat.of R C) (ModuleCat.of R K) hsplit with hC0 | hK0
    · obtain ⟨a, haA, ha0⟩ := (Submodule.ne_bot_iff A).mp hAne
      exact absurd (Subtype.ext_iff.mp
        ((ModuleCat.isZero_iff_subsingleton.mp hC0).elim (⟨a, hAC haA⟩ : C) 0)) ha0
    · have : Subsingleton K := ModuleCat.isZero_iff_subsingleton.mp hK0
      refine le_antisymm le_top fun x _ => ?_
      have hx : x = ((e x).1 : E) := by
        apply e.injective
        rw [show ((e x).1 : E) = C.subtype (e x).1 from rfl, he (e x).1]
        exact Prod.ext rfl (Subsingleton.elim _ _)
      rw [hx]
      exact (e x).1.2
  refine ⟨inferInstance, ?_⟩
  have hessE : IsEssentialMono (ModuleCat.ofHom A.subtype) := by
    refine (isEssentialMono_subtype_iff A).2 fun x hx => ?_
    obtain ⟨r, hr, hr0⟩ := hessC ⟨x, hCtop ▸ Submodule.mem_top⟩ (by simpa using hx)
    exact ⟨r, hr, hr0⟩
  refine (essential_congr_subobject_eq (ModuleCat.ofHom A.subtype) M.arrow ?_).1 hessE
  rw [Subobject.mk_arrow]
  exact hAM

/-- A module in a category which is not a zero object is nontrivial. -/
private theorem nontrivial_of_not_isZero {R : Type u} [Ring R] {M : ModuleCat.{v} R}
    (h : ¬Limits.IsZero M) : Nontrivial M :=
  not_subsingleton_iff_nontrivial.mp fun _ => h (ModuleCat.isZero_of_subsingleton _)

/-- Two nonzero submodules of an indecomposable injective module have nonzero intersection. -/
@[stacks 08Y7 "nonzero_intersection"]
lemma Subobject.inf_ne_bot_of_indecomposable_injective (R : Type u) [Ring R]
    (E : ModuleCat.{v} R) [CategoryTheory.Injective E] (hE : Indecomposable E)
    (A B : Subobject E) (hA : A ≠ ⊥) (hB : B ≠ ⊥) : A ⊓ B ≠ ⊥ := by
  simpa [inf_comm] using (Subobject.isInjectiveHull_arrow_of_indecomposable R E hE A hA).2 B hB

/-- Two nonzero submodules of an indecomposable injective module meet, stated for submodules of
the underlying module rather than for subobjects. -/
private theorem inf_ne_bot_of_nonzero_submodules
    (R : Type u) [Ring R] (E : ModuleCat.{v} R) [CategoryTheory.Injective E]
    (hE : Indecomposable E) (A B : Submodule R E)
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) : A ⊓ B ≠ ⊥ := by
  let e := ModuleCat.subobjectModule E
  have ha : e.symm A ≠ ⊥ := (subobjectModule_symm_ne_bot E A).2 hA
  have hb : e.symm B ≠ ⊥ := (subobjectModule_symm_ne_bot E B).2 hB
  refine fun h => Subobject.inf_ne_bot_of_indecomposable_injective R E hE _ _ ha hb ?_
  rw [← e.symm.map_inf, h, e.symm.map_bot]

/-! ### The endomorphism ring of an indecomposable injective module

The endomorphism ring of an indecomposable injective module is a noncommutative local ring, whose
maximal ideal consists exactly of the endomorphisms having nonzero kernel. Since the ring need not
be commutative, that ideal is exhibited as a left ideal together with `Ideal.IsTwoSided`; the
assertion that every element outside it is a unit records the source's noncommutative meaning of
maximality. -/

/-- An endomorphism of an indecomposable injective module with trivial kernel is invertible. -/
private theorem endo_unit_of_ker_bot
    {R : Type u} {E : Type v} [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E] (hE : Indecomposable (ModuleCat.of R E))
    (f : Module.End R E) (hf : LinearMap.ker f = ⊥) : IsUnit f := by
  have : CategoryTheory.Injective (ModuleCat.of R E) :=
    Module.injective_object_of_injective_module R E
  have hfmono : Mono (ModuleCat.ofHom f) :=
    (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker_eq_bot.mp hf)
  obtain ⟨g, hg⟩ := Injective.factors (𝟙 (ModuleCat.of R E)) (ModuleCat.ofHom f)
  have hgf : g.hom.comp f = LinearMap.id := by
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id] using
      congrArg ModuleCat.Hom.hom hg
  let P : Submodule R E := LinearMap.range f
  let Q : Submodule R E := LinearMap.ker g.hom
  have hP : P ≠ ⊥ := by
    intro h
    have hzero : f = 0 := LinearMap.range_eq_bot.mp h
    have hsub : Subsingleton E := by
      have : (LinearMap.id : Module.End R E) = 0 := by simpa [hzero] using hgf.symm
      constructor; intro x y
      have hx : x = (0 : E) := by simpa using congrArg (fun k : Module.End R E => k x) this
      have hy : y = (0 : E) := by simpa using congrArg (fun k : Module.End R E => k y) this
      exact hx.trans hy.symm
    exact hE.1 (ModuleCat.isZero_of_subsingleton (ModuleCat.of R E))
  have hQ : Q = ⊥ := by
    by_contra hQ
    have hPQ := inf_ne_bot_of_nonzero_submodules R (ModuleCat.of R E) hE P Q hP hQ
    apply hPQ; apply le_antisymm ?_ bot_le
    intro x hx; change x = 0
    rcases hx with ⟨hxP, hxQ⟩
    obtain ⟨y, rfl⟩ := hxP
    have hy : g.hom (f y) = 0 := (LinearMap.mem_ker).mp hxQ
    have hgy := congrArg (fun k : Module.End R E => k y) hgf
    have hgy' : y = g.hom (f y) := by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hgy.symm
    have : y = 0 := hgy'.trans hy
    simp [this]
  have hg_inj : Function.Injective g.hom := LinearMap.ker_eq_bot.mp hQ
  have hfg : f.comp g.hom = LinearMap.id := by
    ext x; apply hg_inj
    have := congrArg (fun k : Module.End R E => k (g.hom x)) hgf
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using this
  apply (Module.End.isUnit_iff f).mpr
  refine ⟨LinearMap.ker_eq_bot.mp hf, ?_⟩
  intro x; refine ⟨g.hom x, ?_⟩
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
    congrArg (fun k : Module.End R E => k x) hfg

/-- An endomorphism of an indecomposable injective module is invertible exactly when its kernel
is trivial. -/
private theorem endo_isUnit_iff_ker_eq_bot
    {R : Type u} {E : Type v} [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E] (hE : Indecomposable (ModuleCat.of R E))
    (f : Module.End R E) : IsUnit f ↔ LinearMap.ker f = ⊥ := by
  constructor
  · intro hf; exact LinearMap.ker_eq_bot.mpr ((Module.End.isUnit_iff f).mp hf).1
  · exact endo_unit_of_ker_bot hE f

/-- If `a * f` is invertible then so is `f`, for endomorphisms of an indecomposable injective
module. -/
private theorem endo_isUnit_of_isUnit_mul
    {R : Type u} {E : Type v} [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E] (hE : Indecomposable (ModuleCat.of R E))
    (a f : Module.End R E) (hu : IsUnit (a * f)) : IsUnit f := by
  rw [endo_isUnit_iff_ker_eq_bot hE] at hu ⊢
  exact eq_bot_mono (LinearMap.ker_le_ker_comp f a) hu

/-- The endomorphism ring of an indecomposable injective module is a (possibly
noncommutative) local ring. -/
@[stacks 08Y7 "endomorphism_ring_local"]
theorem endomorphismRing_isLocalRing
    {R : Type u} {E : Type v} [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : Indecomposable (ModuleCat.of R E)) :
    IsLocalRing (Module.End R E) := by
  have : CategoryTheory.Injective (ModuleCat.of R E) :=
    Module.injective_object_of_injective_module R E
  have : Nontrivial E := nontrivial_of_not_isZero hE.1
  have : Nontrivial (Module.End R E) := inferInstance
  apply IsLocalRing.of_nonunits_add
  intro f g hf hg
  change ¬IsUnit f at hf; change ¬IsUnit g at hg
  show ¬IsUnit (f + g)
  have hfker : LinearMap.ker f ≠ ⊥ := fun h => hf ((endo_isUnit_iff_ker_eq_bot hE f).2 h)
  have hgker : LinearMap.ker g ≠ ⊥ := fun h => hg ((endo_isUnit_iff_ker_eq_bot hE g).2 h)
  have hInf := inf_ne_bot_of_nonzero_submodules R (ModuleCat.of R E) hE _ _ hfker hgker
  intro hu; apply hInf; apply le_antisymm ?_ bot_le
  intro x hx
  have hfg : x ∈ LinearMap.ker (f + g) := by
    have hfx : f x = 0 := LinearMap.mem_ker.mp hx.1
    have hgx : g x = 0 := LinearMap.mem_ker.mp hx.2
    exact LinearMap.mem_ker.mpr (by simp [hfx, hgx])
  exact (endo_isUnit_iff_ker_eq_bot hE (f + g)).1 hu ▸ hfg

/-- The maximal two-sided ideal of the endomorphism ring consists exactly of the
endomorphisms with nonzero kernel, and every endomorphism outside it is invertible. -/
@[stacks 08Y7 "endomorphism_ring_local"]
theorem exists_maximalIdeal_endomorphismRing
    {R : Type u} {E : Type v} [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : Indecomposable (ModuleCat.of R E)) :
    ∃ I : Ideal (Module.End R E), I.IsTwoSided ∧ I.IsMaximal ∧
      (∀ φ : Module.End R E, φ ∈ I ↔ LinearMap.ker φ ≠ ⊥) ∧
      (∀ φ : Module.End R E, φ ∉ I → IsUnit φ) := by
  have : Nontrivial E := nontrivial_of_not_isZero hE.1
  have : Nontrivial (Module.End R E) := inferInstance
  have : IsLocalRing (Module.End R E) := endomorphismRing_isLocalRing hE
  let I : Ideal (Module.End R E) := {
    carrier := {φ | ¬IsUnit φ}
    zero_mem' := not_isUnit_zero
    add_mem' := by
      intro f g hf hg
      exact IsLocalRing.nonunits_add hf hg
    smul_mem' := by
      intro a f hf hu
      exact hf (endo_isUnit_of_isUnit_mul hE a f hu) }
  refine ⟨I, ?_, ?_, ?_, ?_⟩
  · constructor
    intro f a hf
    show ¬IsUnit (f * a)
    intro hu
    have ha : IsUnit a := endo_isUnit_of_isUnit_mul hE f a hu
    obtain ⟨u, rfl⟩ := ha
    have hfu : IsUnit f := by
      have hprod : IsUnit ((f * (u : Module.End R E)) * (↑(u⁻¹) : Module.End R E)) :=
        hu.mul (u⁻¹).isUnit
      simpa only [mul_assoc, Units.mul_inv, mul_one] using hprod
    exact hf hfu
  · apply Ideal.isMaximal_iff.mpr
    constructor
    · exact not_not_intro isUnit_one
    · intro J x hIJ hx hxJ
      have hu : IsUnit x := Classical.not_not.mp hx
      obtain ⟨u, rfl⟩ := hu
      have h := J.smul_mem (↑(u⁻¹) : Module.End R E) hxJ
      simpa only [smul_eq_mul, Units.inv_mul] using h
  · intro φ; change (¬IsUnit φ) ↔ _
    exact not_congr (endo_isUnit_iff_ker_eq_bot hE φ)
  · intro φ hφ; exact Classical.not_not.mp hφ

/-! ### Zerodivisors on an indecomposable injective module

The elements of a commutative ring which kill a nonzero element of an indecomposable injective
module form a prime ideal, and the module is naturally a module over the localization at that
prime. -/

/-- An element `r` kills a nonzero element of `M` precisely when multiplication by `r` on `M` has
nonzero kernel. -/
private lemma mem_zeroDivisors_iff_ker_lsmul_ne_bot {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (r : R) :
    (∃ m : M, m ≠ 0 ∧ r • m = 0) ↔ LinearMap.ker (LinearMap.lsmul R M r) ≠ ⊥ := by
  constructor
  · rintro ⟨m, hm, hrm⟩ h
    exact hm ((Submodule.eq_bot_iff _).mp h m (by simpa using hrm))
  · intro h
    obtain ⟨m, hm, hm0⟩ := (Submodule.ne_bot_iff _).mp h
    exact ⟨m, hm0, by simpa using hm⟩

/-- The set of zerodivisors on an indecomposable injective module is the underlying set of a prime
ideal. -/
@[stacks 08Y7 "zero_divisors_prime"]
theorem exists_prime_eq_zeroDivisorsOn {R : Type u} [CommRing R]
    (E : ModuleCat.{v} R) [CategoryTheory.Injective E] (hE : Indecomposable E) :
    ∃ p : Ideal R, p.IsPrime ∧ (p : Set R) = {r : R | ∃ m : E, m ≠ 0 ∧ r • m = 0} := by
  have : Module.Injective R E := Module.injective_module_of_injective_object R E
  obtain ⟨I, -, hI, hker, hunit⟩ :=
    exists_maximalIdeal_endomorphismRing (R := R) (E := E) hE
  let f : R →+* Module.End R E := Module.toModuleEnd R E
  have : I.IsPrime := ⟨hI.ne_top, by
    intro x y hxy; by_contra h
    exact hI.ne_top (I.eq_top_of_isUnit_mem hxy
      ((hunit x (not_or.mp h).1).mul (hunit y (not_or.mp h).2)))⟩
  refine ⟨I.comap f, Ideal.comap_isPrime f I, ?_⟩
  ext r
  show f r ∈ I ↔ r ∈ {r : R | ∃ m : E, m ≠ 0 ∧ r • m = 0}
  rw [hker]
  exact ((mem_zeroDivisors_iff_ker_lsmul_ne_bot (M := (E : Type v)) r).symm)

/-- An indecomposable injective module is an injective module over the localization at its prime
ideal of zerodivisors. -/
@[stacks 08Y7 "injective_over_localization"]
theorem exists_injective_localizationAtPrime_module
    {R : Type u} [CommRing R] (E : ModuleCat.{v} R) [CategoryTheory.Injective E]
    (hE : Indecomposable E) (p : Ideal R) (hp : p.IsPrime)
    (hpE : (p : Set R) = {r : R | ∃ m : E, m ≠ 0 ∧ r • m = 0}) :
    ∃ moduleStructure : Module (Localization.AtPrime p) E,
      letI := moduleStructure
      (∀ (r : R) (x : E), algebraMap R (Localization.AtPrime p) r • x = r • x) ∧
        CategoryTheory.Injective (ModuleCat.of (Localization.AtPrime p) E) := by
  let S := Localization.AtPrime p
  have : Module.Injective R E := Module.injective_module_of_injective_object R E
  obtain ⟨I, -, -, hker, hunit⟩ := exists_maximalIdeal_endomorphismRing hE
  have hg : ∀ s : p.primeCompl, IsUnit (algebraMap R (Module.End R E) s) := by
    rintro ⟨r, hr⟩
    refine hunit _ ?_
    rw [hker]
    intro hne
    exact hr (hpE ▸ (mem_zeroDivisors_iff_ker_lsmul_ne_bot (M := (E : Type v)) r).mpr hne)
  let : IsLocalizedModule p.primeCompl (LinearMap.id : E →ₗ[R] E) :=
    { map_units := hg
      surj x := ⟨⟨x, 1⟩, by simp⟩
      exists_of_eq h := ⟨1, by simpa using h⟩ }
  let : Module S E := IsLocalizedModule.module p.primeCompl (LinearMap.id : E →ₗ[R] E)
  let : IsScalarTower R S E :=
    IsLocalizedModule.isScalarTower_module p.primeCompl (LinearMap.id : E →ₗ[R] E)
  refine ⟨inferInstance, (fun r x => algebraMap_smul S r x),
    (Module.injective_iff_injective_object S E).mp ?_⟩
  refine ⟨?_⟩; intro X Y _ _ _ _ i hi j
  let : Module R X := Module.compHom X (algebraMap R S)
  let : Module R Y := Module.compHom Y (algebraMap R S)
  let : IsScalarTower R S X := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower R S Y := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨k, hk⟩ := Module.Injective.out (i.restrictScalars R) hi (j.restrictScalars R)
  exact ⟨k.extendScalarsOfIsLocalization p.primeCompl S, hk⟩

/-! ### Injective hulls of prime quotients are indecomposable

The inclusion of the prime quotient into its injective hull is represented by an arbitrary
monomorphism satisfying `Module.IsInjectiveHull`; thus the statement does not depend on a chosen
construction of the hull. -/

/-- In an injective hull, every nonzero element of the hull has a nonzero multiple which is the
image of a nonzero element of the embedded module. -/
private theorem essential_scalar {R : Type u} [Ring R]
    {M E : ModuleCat.{v} R} (i : M ⟶ E) [Mono i] (hi : IsInjectiveHull i) (x : E) (hx : x ≠ 0) :
    ∃ (r : R) (w : M), i w = r • x ∧ w ≠ 0 := by
  obtain ⟨r, ⟨w, hw⟩, hr⟩ := (isEssentialMono_subtype_iff (R := R) (N := E)
    (LinearMap.range i.hom)).1 ((isEssentialMono_iff_range i).1 hi.2) x hx
  exact ⟨r, w, hw, fun h => hr (by simpa [h] using hw.symm)⟩

/-- Two nonzero elements of `R ⧸ p`, for `p` prime, have a common nonzero multiple. -/
private lemma exists_common_nonzero_smul_quotient {R : Type*} [CommRing R] (p : Ideal R)
    [p.IsPrime] (x y : ULift.{v} (R ⧸ p)) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ a b : R, a • x = b • y ∧ a • x ≠ 0 := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x.down
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective y.down
  refine ⟨b, a, ?_, ?_⟩
  · apply ULift.down_injective
    show b • x.down = a • y.down
    rw [← ha, ← hb]
    simp only [Algebra.smul_def]
    simp [mul_comm]
  · intro h
    have h' : b • x.down = 0 := congrArg ULift.down h
    rw [← ha] at h'
    simp only [Algebra.smul_def] at h'
    have ha' : (Ideal.Quotient.mk p) a ≠ 0 := by
      intro hh
      exact hx (ULift.down_injective (by simpa [← ha] using hh))
    have hb' : (Ideal.Quotient.mk p) b ≠ 0 := by
      intro hh
      exact hy (ULift.down_injective (by simpa [← hb] using hh))
    exact (mul_ne_zero hb' ha') (by simpa using h')

/-- The injective hull of the quotient by a prime ideal is indecomposable. -/
@[stacks 08Y8 "indecomposable"]
theorem indecomposable_of_isInjectiveHull_quotient
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {E : ModuleCat.{max v u} R}
    (i : ModuleCat.of R (ULift.{v} (R ⧸ p)) ⟶ E) [Mono i]
    (hi : IsInjectiveHull i) : Indecomposable E := by
  have hnonzero : ¬ Limits.IsZero E := by
    intro hE
    have hq : (ULift.up (1 : R ⧸ p) : ULift.{v} (R ⧸ p)) = 0 := by
      apply (ModuleCat.mono_iff_injective i).mp inferInstance
      exact (ModuleCat.isZero_iff_subsingleton.mp hE).elim _ _
    exact one_ne_zero (congrArg ULift.down hq)
  refine ⟨hnonzero, ?_⟩
  intro Y Z e
  let F : E ≃ₗ[R] Y × Z := (e ≪≫ ModuleCat.biprodIsoProd Y Z).toLinearEquiv
  by_contra h
  obtain ⟨hY, hZ⟩ := not_or.mp h
  have := nontrivial_of_not_isZero hY
  have := nontrivial_of_not_isZero hZ
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  obtain ⟨z, hz⟩ := exists_ne (0 : Z)
  let ey : E := F.symm (y, 0)
  let ez : E := F.symm (0, z)
  have hey : ey ≠ 0 := by
    intro h
    exact hy (by simpa [ey] using congrArg Prod.fst (congrArg F h))
  have hez : ez ≠ 0 := by
    intro h
    exact hz (by simpa [ez] using congrArg Prod.snd (congrArg F h))
  obtain ⟨r, x, hx, hxne⟩ := essential_scalar i hi ey hey
  obtain ⟨s, w, hw, hwne⟩ := essential_scalar i hi ez hez
  obtain ⟨a, b, hab, habne⟩ := exists_common_nonzero_smul_quotient p x w hxne hwne
  have hf : F (i (a • x)) = 0 := by
    apply Prod.ext
    · simp [map_smul, hab, hw, ez]
    · simp [map_smul, hx, ey]
  exact habne ((ModuleCat.mono_iff_injective i).mp inferInstance
    (F.injective (by simpa using hf)))

/-! ### Indecomposable injective modules over Noetherian rings

An indecomposable injective module over a Noetherian ring is an injective hull of the residue
field at a prime ideal. A prime ideal is represented by a point of `PrimeSpectrum R`; since the
residue field's chosen type need not lie in the universe of `E`, it is represented there by a
linearly equivalent module. -/

/-- Over a Noetherian ring, an indecomposable injective module has a nonzero element annihilated
by the whole prime ideal of zerodivisors. -/
private theorem exists_nonzero_annihilated_by_prime
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (E : ModuleCat.{v} R) [CategoryTheory.Injective E] (hE : Indecomposable E)
    (p : Ideal R) (hpE : (p : Set R) = {r : R | ∃ m : E, m ≠ 0 ∧ r • m = 0}) :
    ∃ x : E, x ≠ 0 ∧ ∀ r ∈ p, r • x = 0 := by
  classical
  have : Nontrivial E := nontrivial_of_not_isZero hE.1
  obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.mp (Ideal.fg_of_isNoetherianRing p)
  let s := hSfin.toFinset
  let T (t : Finset R) : Submodule R E :=
    ⨅ r ∈ t, LinearMap.ker (LinearMap.lsmul R E r)
  have hT : ∀ t : Finset R, (∀ r ∈ t, r ∈ p) → T t ≠ ⊥ := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro _
        simp [T]
    | @insert r t hrt ih =>
        intro ht
        have hrp : r ∈ p := ht r (Finset.mem_insert_self ..)
        obtain ⟨y, hy, hry⟩ : ∃ m : E, m ≠ 0 ∧ r • m = 0 := by
          have : r ∈ (p : Set R) := hrp
          rwa [hpE] at this
        have hker : LinearMap.ker (LinearMap.lsmul R E r) ≠ ⊥ :=
          (Submodule.ne_bot_iff _).mpr ⟨y, by simpa using hry, hy⟩
        have ht' : T t ≠ ⊥ := ih (fun a ha => ht a (Finset.mem_insert_of_mem ha))
        simpa only [T, Finset.iInf_insert] using inf_ne_bot_of_nonzero_submodules R E hE
          (LinearMap.ker (LinearMap.lsmul R E r)) (T t) hker ht'
  have hs : ∀ r ∈ s, r ∈ p := by
    intro r hr
    rw [← hS]
    exact Submodule.subset_span (hSfin.mem_toFinset.mp hr)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff (T s)).mp (hT s hs)
  have hkill : ∀ r ∈ Submodule.span R S, r • x = 0 := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem a ha =>
        have hxa : x ∈ LinearMap.ker (LinearMap.lsmul R E a) :=
          (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hx a)
            (hSfin.mem_toFinset.mpr ha)
        simpa using hxa
    | zero => simp
    | add a b ha hb iha ihb => simp [add_smul, iha, ihb]
    | smul a b hb ihb => simp [mul_smul, ihb]
  exact ⟨x, hx0, fun r hr => hkill r (hS.symm ▸ hr)⟩

/-- An indecomposable injective module over a Noetherian ring is an injective hull of the residue
field at some prime ideal. -/
@[stacks 08Y9]
theorem exists_isInjectiveHull_residueField_of_indecomposable
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (E : ModuleCat.{v} R) [CategoryTheory.Injective E] (hE : Indecomposable E) :
    ∃ (p : PrimeSpectrum R) (K : ModuleCat.{v} R),
      Nonempty (K ≃ₗ[R] p.asIdeal.ResidueField) ∧
        ∃ (i : K ⟶ E) (_ : Mono i), IsInjectiveHull i := by
  classical
  obtain ⟨p, hp, hpE⟩ := exists_prime_eq_zeroDivisorsOn E hE
  have : p.IsPrime := hp
  obtain ⟨x, hx, hpx⟩ := exists_nonzero_annihilated_by_prime R E hE p hpE
  obtain ⟨moduleStructure, hcompat, -⟩ :=
    exists_injective_localizationAtPrime_module E hE p hp hpE
  let A := Localization.AtPrime p
  let : Module A E := moduleStructure
  let : IsScalarTower R A E := IsScalarTower.of_algebraMap_smul hcompat
  let fA : A →ₗ[A] E := LinearMap.toSpanSingleton A E x
  have hker_le : (IsLocalRing.maximalIdeal A : Ideal A) ≤ fA.ker := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p)]
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    show fA (algebraMap R A r) = 0
    rw [LinearMap.toSpanSingleton_apply, hcompat]
    exact hpx r hr
  have hker_ne_top : fA.ker ≠ ⊤ := by
    intro h
    have h1 : (1 : A) ∈ fA.ker := by rw [h]; trivial
    exact hx (by simpa [fA, LinearMap.toSpanSingleton_apply] using h1)
  have hker : (IsLocalRing.maximalIdeal A : Ideal A) = fA.ker :=
    (IsLocalRing.maximalIdeal.isMaximal A).eq_of_le hker_ne_top hker_le
  let fK : p.ResidueField →ₗ[A] E := (IsLocalRing.maximalIdeal A).liftQ fA hker_le
  have hfK : Function.Injective fK :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ fA hker)
  let fR : p.ResidueField →ₗ[R] E := fK.restrictScalars R
  have hfR : Function.Injective fR := hfK
  have hrange : fR.range ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr
      ⟨fR 1, LinearMap.mem_range_self fR 1, fun h => one_ne_zero (hfR (by simpa using h))⟩
  let M : Subobject E := (ModuleCat.subobjectModule E).symm fR.range
  have hM : M ≠ ⊥ := (subobjectModule_symm_ne_bot E _).2 hrange
  let i : ModuleCat.of R fR.range ⟶ E := ModuleCat.ofHom fR.range.subtype
  have hMmk : M = Subobject.mk i := rfl
  let eM : (M : ModuleCat.{v} R) ≃ₗ[R] fR.range := by
    rw [hMmk]
    exact (Subobject.underlyingIso i).toLinearEquiv
  let eK : (M : ModuleCat.{v} R) ≃ₗ[R] p.ResidueField :=
    eM.trans (LinearEquiv.ofInjective fR hfR).symm
  exact ⟨⟨p, hp⟩, (M : ModuleCat.{v} R), ⟨eK⟩, M.arrow, inferInstance,
    Subobject.isInjectiveHull_arrow_of_indecomposable R E hE M hM⟩

/-! ### Power-torsion submodules of an injective module

Over a Noetherian ring, the submodule of an injective module consisting of the elements
annihilated by some power of an element, or more generally by some power of an ideal, is again
injective. The union `I[f^∞]` is expressed as the supremum of the submodules annihilated by
`f ^ n`, and the ideal-power torsion submodule `I[J^∞]` is Mathlib's `Ideal.primaryComponent`. -/

section PowerTorsion

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (I : Type v) [AddCommGroup I] [Module R I] [Module.Injective R I]

omit [IsNoetherianRing R] in
/-- Essentiality of a submodule inclusion, read off elementwise on the larger submodule. -/
private lemma exists_smul_mem_of_essential_inclusion {N : ModuleCat.{v} R}
    (M M' : Submodule R N) (hM : M ≤ M')
    [Mono (ModuleCat.ofHom (Submodule.inclusion hM))]
    (h : IsEssentialMono (ModuleCat.ofHom (Submodule.inclusion hM)))
    (x : M') (hx : x ≠ 0) :
    ∃ a : R, a • (x : N) ∈ M ∧ a • x ≠ 0 := by
  let P : Submodule R M' := R ∙ x
  have hP : P ≠ ⊥ := by
    intro hP
    apply hx
    have : x ∈ P := Submodule.subset_span (by simp)
    rw [hP] at this
    simpa using this
  have hcat := h ((ModuleCat.subobjectModule (ModuleCat.of R M')).symm P)
    ((subobjectModule_symm_ne_bot (ModuleCat.of R M') P).2 hP)
  let e : M ≃ₗ[R] M.comap M'.subtype :=
    { toFun := fun y => ⟨⟨y, hM y.2⟩, y.2⟩
      invFun := fun y => ⟨y.1.1, y.2⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl
      left_inv := by intro y; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  have : Mono (ModuleCat.ofHom (M.comap M'.subtype).subtype) :=
    (ModuleCat.mono_iff_injective _).mpr (Submodule.subtype_injective _)
  have himage : (ModuleCat.subobjectModule (ModuleCat.of R M'))
      (Subobject.mk (ModuleCat.ofHom (Submodule.inclusion hM))) = M.comap M'.subtype := by
    have hs : (ModuleCat.subobjectModule (ModuleCat.of R M')).symm (M.comap M'.subtype) =
        Subobject.mk (ModuleCat.ofHom (Submodule.inclusion hM)) := by
      apply Subobject.mk_eq_mk_of_comm _ _ e.symm.toModuleIso
      ext y
      rfl
    rw [← hs]
    exact (ModuleCat.subobjectModule (ModuleCat.of R M')).apply_symm_apply _
  have hmeet : P ⊓ M.comap M'.subtype ≠ ⊥ := by
    intro hbot
    apply hcat
    apply (ModuleCat.subobjectModule (ModuleCat.of R M')).injective
    rw [OrderIso.map_inf, OrderIso.apply_symm_apply, himage, OrderIso.map_bot]
    exact hbot
  obtain ⟨y, hy⟩ := Submodule.nonzero_mem_of_bot_lt ((bot_lt_iff_ne_bot).2 hmeet)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (Submodule.mem_inf.mp y.2).1
  refine ⟨a, ?_, ?_⟩
  · show M'.subtype (a • x) ∈ M
    rw [ha]
    exact (Submodule.mem_inf.mp y.2).2
  · intro hzero
    apply hy
    apply Subtype.ext
    simpa [ha] using congrArg Subtype.val hzero

omit [IsNoetherianRing R] [Module.Injective R I] in
/-- Membership in the `f`-power torsion submodule means being killed by some power of `f`. -/
private lemma mem_iSup_torsionBy_pow_iff (f : R) (x : I) :
    x ∈ (⨆ n : ℕ, Submodule.torsionBy R I (f ^ n) : Submodule R I) ↔
      ∃ n : ℕ, f ^ n • x = 0 := by
  rw [Submodule.mem_iSup_of_directed _ (Monotone.directed_le fun m n h =>
    Submodule.torsionBy_le_torsionBy_of_dvd _ _ (pow_dvd_pow f h))]
  simp

omit [IsNoetherianRing R] [Module.Injective R I] in
/-- Membership in `Ideal.primaryComponent` means being killed by some power of the ideal. -/
private lemma mem_primaryComponent_iff (J : Ideal R) (x : I) :
    x ∈ Ideal.primaryComponent I J ↔
      ∃ n : ℕ, ∀ a : R, a ∈ J ^ n → a • x = 0 := by
  simp [Ideal.primaryComponent_mem, Submodule.mem_torsionBySet_iff]

/-- The submodule of an injective module consisting of the elements annihilated by some power
of `f` is injective. This is part (1) of Stacks Project, Tag 08XW. -/
@[stacks 08XW "part (1)", sga "2 IV 2.2" "principal ideal case"]
lemma injective_iSup_torsionBy_pow (f : R) :
    Module.Injective R (⨆ n : ℕ, Submodule.torsionBy R I (f ^ n) : Submodule R I) := by
  classical
  let E : Submodule R I := ⨆ n : ℕ, Submodule.torsionBy R I (f ^ n)
  rw [show (⨆ n : ℕ, Submodule.torsionBy R I (f ^ n) : Submodule R I) = E from rfl]
  rw [injective_iff_eq_of_essential_extension R I E]
  intro E' hE' hi hessential
  have : Mono (ModuleCat.ofHom (Submodule.inclusion hE')) :=
    (ModuleCat.mono_iff_injective _).mpr (Submodule.inclusion_injective hE')
  apply le_antisymm hE'
  intro x hx
  by_contra hxE
  let J : Ideal R :=
    { carrier := {a | a • (x : I) ∈ E}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simpa [add_smul] using E.add_mem ha hb
      smul_mem' := by
        intro a b hb
        simpa [smul_smul, mul_comm] using E.smul_mem a hb }
  obtain ⟨S, hS⟩ := J.fg_of_isNoetherianRing
  have hgen (a : R) (ha : a ∈ S) : ∃ m : ℕ, f ^ m • (a • (x : I)) = 0 := by
    apply (mem_iSup_torsionBy_pow_iff I f _).mp
    show a ∈ J
    rw [← hS]
    exact Submodule.subset_span (by simpa using ha)
  choose! exponent hexponent using hgen
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ a ∈ S, f ^ n • (a • (x : I)) = 0 := by
    exact ⟨S.sup exponent, fun a ha => Submodule.torsionBy_le_torsionBy_of_dvd _ _
      (pow_dvd_pow f (Finset.le_sup (f := exponent) ha)) (hexponent a ha)⟩
  let x' : E' := ⟨f ^ n • (x : I), E'.smul_mem _ hx⟩
  have hx'E : (x' : I) ∉ E := by
    intro hx'
    obtain ⟨m, hm⟩ := (mem_iSup_torsionBy_pow_iff I f _).mp hx'
    apply hxE
    apply (mem_iSup_torsionBy_pow_iff I f _).mpr
    refine ⟨m + n, ?_⟩
    simpa [x', pow_add, mul_smul] using hm
  have hx'0 : x' ≠ 0 := fun hx'0 => hx'E (by simp [hx'0])
  have hkill (a : R) (ha : a • (x' : E') ∈ E.comap E'.subtype) : a • x' = 0 := by
    have hax'E : a • (x' : I) ∈ E := by simpa [x'] using ha
    have haJ : a ∈ J := by
      show a • (x : I) ∈ E
      obtain ⟨m, hm⟩ := (mem_iSup_torsionBy_pow_iff I f _).mp hax'E
      apply (mem_iSup_torsionBy_pow_iff I f _).mpr
      refine ⟨m + n, ?_⟩
      rw [pow_add, mul_smul]
      convert hm using 1
      simp [x', smul_smul, mul_comm]
    rw [← hS] at haJ
    have ha0 : f ^ n • (a • (x : I)) = 0 := by
      refine Submodule.span_induction (p := fun a _ => f ^ n • (a • (x : I)) = 0)
        (fun b hb => hn b (by simpa using hb)) (by simp) ?_ ?_ haJ
      · intro b c _ _ hb hc
        simpa [add_smul, smul_add] using congrArg₂ (· + ·) hb hc
      · intro r b _ hb
        simpa [smul_eq_mul, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
          congrArg (fun z => r • z) hb
    apply Subtype.ext
    simpa [x', smul_smul, mul_comm] using ha0
  obtain ⟨a, haE, ha0⟩ :=
    exists_smul_mem_of_essential_inclusion (R := R) (N := ModuleCat.of R I)
      (M := E) (M' := E') hE' hessential (x := x') hx'0
  exact ha0 (hkill a haE)

omit [Module.Injective R I] in
/-- The `f`-power torsion of an injective submodule, computed inside the ambient module. -/
private lemma injective_inf_powerTorsion (E : Submodule R I) [Module.Injective R E] (f : R) :
    Module.Injective R
      ↥(E ⊓ (⨆ n : ℕ, Submodule.torsionBy R I (f ^ n) : Submodule R I)) := by
  let T : Submodule R E := ⨆ n : ℕ, Submodule.torsionBy R E (f ^ n)
  let e := E.equivSubtypeMap T
  have hT : Module.Injective R T := injective_iSup_torsionBy_pow E f
  have hmap : T.map E.subtype =
      E ⊓ (⨆ n : ℕ, Submodule.torsionBy R I (f ^ n) : Submodule R I) := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_inf, T]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨n, hn⟩ := (mem_iSup_torsionBy_pow_iff E f _).mp hy
      refine ⟨y.2, (mem_iSup_torsionBy_pow_iff I f _).mpr ⟨n, ?_⟩⟩
      exact congrArg Subtype.val hn
    · rintro ⟨hxE, hx⟩
      obtain ⟨n, hn⟩ := (mem_iSup_torsionBy_pow_iff I f _).mp hx
      refine ⟨⟨x, hxE⟩, (mem_iSup_torsionBy_pow_iff E f _).mpr ⟨n, ?_⟩, rfl⟩
      exact Subtype.ext hn
  rw [← hmap]
  exact injective_of_linearEquiv e hT

/-- The submodule of an injective module consisting of the elements annihilated by some power
of `J` is injective. This is part (2) of Stacks Project, Tag 08XW. -/
@[stacks 08XW "part (2)", sga "2 IV 2.2"]
lemma injective_primaryComponent (J : Ideal R) :
    Module.Injective R (Ideal.primaryComponent I J) := by
  classical
  obtain ⟨S, hS⟩ := J.fg_of_isNoetherianRing
  let G : R → Submodule R I := fun f => ⨆ n : ℕ, Submodule.torsionBy R I (f ^ n)
  have hfin (T : Finset R) : Module.Injective R ↥(⨅ f : R, ⨅ _ : f ∈ T, G f) := by
    induction T using Finset.induction with
    | empty =>
        have he : (⨅ f : R, ⨅ _ : f ∈ (∅ : Finset R), G f) = ⊤ := by
          ext x
          simp
        rw [he]
        exact injective_of_linearEquiv Submodule.topEquiv.symm inferInstance
    | @insert f T hf ih =>
        rw [show (⨅ g : R, ⨅ _ : g ∈ insert f T, G g) =
          (⨅ g : R, ⨅ _ : g ∈ T, G g) ⊓ G f by
            ext x
            simp [and_comm]]
        have : Module.Injective R ↥(⨅ g : R, ⨅ _ : g ∈ T, G g) := ih
        exact injective_inf_powerTorsion I (⨅ g : R, ⨅ _ : g ∈ T, G g) f
  have heq : Ideal.primaryComponent I J = ⨅ f : R, ⨅ _ : f ∈ S, G f := by
    ext x
    rw [mem_primaryComponent_iff I J]
    simp only [Submodule.mem_iInf, G]
    constructor
    · rintro ⟨n, hn⟩ f hf
      apply (mem_iSup_torsionBy_pow_iff I f x).mpr
      have hfJ : f ∈ J := by
        rw [← hS]
        exact Submodule.subset_span (by simpa using hf)
      exact ⟨n, hn _ (Ideal.pow_mem_pow hfJ n)⟩
    · intro h
      let A : Ideal R :=
        { carrier := {a | a • x = 0}
          zero_mem' := by simp
          add_mem' := by
            intro a b ha hb
            show (a + b) • x = 0
            rw [add_smul, ha, hb, add_zero]
          smul_mem' := by
            intro a b hb
            show (a * b) • x = 0
            rw [mul_smul, hb, smul_zero] }
      have hJA : J ≤ A.radical := by
        rw [← hS, Ideal.span_le]
        intro f hf
        obtain ⟨n, hn⟩ := (mem_iSup_torsionBy_pow_iff I f x).mp (h f (by simpa using hf))
        exact ⟨n, hn⟩
      obtain ⟨n, hn⟩ := A.exists_radical_pow_le_of_fg A.radical.fg_of_isNoetherianRing
      exact ⟨n, fun a ha => hn (pow_le_pow_left' hJA n ha)⟩
  rw [heq]
  exact hfin S

end PowerTorsion

end Module
