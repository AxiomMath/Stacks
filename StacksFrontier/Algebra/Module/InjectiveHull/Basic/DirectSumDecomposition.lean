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
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic.IndecomposableInjective

/-!
# Injective modules over Noetherian rings

The action of `R` on an injective hull of `R ⧸ p`, `p` prime, extends to the local ring at `p`,
and the module is then an injective hull of the residue field `κ(p)`. Every injective module over
a Noetherian ring is a direct sum of indecomposable injective modules, each an injective hull of
a residue field.

## Main results

* `Module.exists_isInjectiveHull_residueField_localization` — the injective hull of `R ⧸ p` is an
  injective hull of `κ(p)` over the local ring at `p`.
* `Module.exists_iso_directSum_of_injective` — over a Noetherian ring, every injective module is a
  direct sum of indecomposable injectives.

## References

* [Stacks Project, Tag 08Y8](https://stacks.math.columbia.edu/tag/08Y8)
* [Stacks Project, Tag 08YA](https://stacks.math.columbia.edu/tag/08YA)
-/

@[expose] public section

open CategoryTheory

namespace Module

universe u v w

/-! ### Localizing an injective hull at its prime

Let `p` be a prime ideal of a commutative ring `R`. If `E` is an injective hull of `R ⧸ p`, then
the action of `R` on `E` extends to the local ring at `p`, and `E` is an injective hull of the
residue field at `p` for this extended action. The scalar-tower witness records that the new action
extends the given `R`-action, while the displayed equality says that the new embedding restricts
along `R ⧸ p → p.ResidueField` to the original injective-hull embedding. -/

/-- If every element of `S` acts invertibly on `M`, then `M` is a module over the localization of
`R` at `S`. -/
@[instance_reducible]
private noncomputable def moduleOfInvertibleScalars
    {R : Type u} [CommRing R] (S : Submonoid R)
    (T : Type u) [CommRing T] [Algebra R T] [IsLocalization S T]
    (M : Type u) [AddCommGroup M] [Module R M]
    (h : ModuleCat.invertibleSMul S (ModuleCat.of R M)) : Module T M := by
  letI : IsLocalizedModule S (LinearMap.id : M →ₗ[R] M) :=
    ModuleCat.isLocalizedModule_id_of_invertibleSMul S (ModuleCat.of R M) h
  letI : IsLocalizedModule S (LocalizedModule.mkLinearMap S M) := inferInstance
  letI : Module T (LocalizedModule S M) :=
    @LocalizedModule.moduleOfIsLocalization R _ S M _ _ T _ _ _
  let e : M ≃ₗ[R] LocalizedModule S M :=
    IsLocalizedModule.linearEquiv S (LinearMap.id : M →ₗ[R] M)
      (LocalizedModule.mkLinearMap S M)
  let smulT : SMul T M := ⟨fun a x => e.symm (a • e x)⟩
  letI : SMul T M := smulT
  exact {
    smul := smulT.smul
    one_smul := by
      intro x
      change e.symm ((1 : T) • e x) = x
      rw [one_smul]
      exact e.symm_apply_apply x
    mul_smul := by
      intro a b x
      change e.symm ((a * b) • e x) = e.symm (a • e (e.symm (b • e x)))
      rw [e.apply_symm_apply]
      exact congrArg e.symm (mul_smul a b (e x))
    smul_add := by
      intro a x y
      change e.symm (a • e (x + y)) = e.symm (a • e x) + e.symm (a • e y)
      rw [← e.symm.map_add, map_add]
      exact congrArg e.symm (smul_add a (e x) (e y))
    smul_zero := by
      intro a
      change e.symm (a • e 0) = 0
      rw [map_zero, smul_zero, map_zero]
    add_smul := by
      intro a b x
      change e.symm ((a + b) • e x) = e.symm (a • e x) + e.symm (b • e x)
      rw [← e.symm.map_add]
      exact congrArg e.symm (add_smul a b (e x))
    zero_smul := by
      intro x
      change e.symm (0 • e x) = 0
      rw [zero_smul, map_zero]
  }

/-- The localized action of `Module.moduleOfInvertibleScalars` extends the original one. -/
private theorem moduleOfInvertibleScalars_tower
    {R : Type u} [CommRing R] (S : Submonoid R)
    (T : Type u) [CommRing T] [Algebra R T] [IsLocalization S T]
    (M : Type u) [AddCommGroup M] [Module R M]
    (h : ModuleCat.invertibleSMul S (ModuleCat.of R M)) :
    letI : Module T M := moduleOfInvertibleScalars S T M h
    IsScalarTower R T M := by
  let : Module T M := moduleOfInvertibleScalars S T M h
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  let : IsLocalizedModule S (LinearMap.id : M →ₗ[R] M) :=
    ModuleCat.isLocalizedModule_id_of_invertibleSMul S (ModuleCat.of R M) h
  let : IsLocalizedModule S (LocalizedModule.mkLinearMap S M) := inferInstance
  let : Module T (LocalizedModule S M) :=
    @LocalizedModule.moduleOfIsLocalization R _ S M _ _ T _ _ _
  let e : M ≃ₗ[R] LocalizedModule S M :=
    IsLocalizedModule.linearEquiv S (LinearMap.id : M →ₗ[R] M)
      (LocalizedModule.mkLinearMap S M)
  apply e.injective
  show e (e.symm (algebraMap R T r • e x)) = e (r • x)
  simp only [e.apply_symm_apply, e.map_smul]
  rw [Algebra.algebraMap_eq_smul_one (R := R) (A := T) r]
  simpa only [one_smul] using IsScalarTower.smul_assoc r (1 : T) (e x)

/-- The submodule corresponding to the subobject cut out by a monomorphism is its range. -/
private theorem moduleSubobjectMk
    {R : Type u} [Ring R] {M N : ModuleCat.{u} R}
    (f : M ⟶ N) [Mono f] :
    ModuleCat.subobjectModule N (Subobject.mk f) = LinearMap.range f.hom := by
  show LinearMap.range (Subobject.mk f).arrow.hom = LinearMap.range f.hom
  let e := Subobject.underlyingIso f
  have hcomp : (Subobject.mk f).arrow.hom.comp e.inv.hom = f.hom :=
    congrArg ModuleCat.Hom.hom (Subobject.underlyingIso_arrow f)
  have hsurj : Function.Surjective e.inv.hom := fun x => ⟨e.hom.hom x, by simp⟩
  rw [← hcomp, LinearMap.range_comp, LinearMap.range_eq_top.mpr hsurj]
  simp

/-- A monomorphism of modules is essential iff every nonzero submodule of the target meets its
range nontrivially. -/
private theorem isEssentialMono_iff_inf_range_ne_bot
    {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (i : M ⟶ N) [Mono i] :
    IsEssentialMono i ↔ ∀ P : Submodule R N, P ≠ ⊥ → P ⊓ LinearMap.range i.hom ≠ ⊥ := by
  have key (B : Subobject N) : B = ⊥ ↔ ModuleCat.subobjectModule N B = ⊥ := by
    rw [← (ModuleCat.subobjectModule N).map_bot]
    exact (ModuleCat.subobjectModule N).eq_iff_eq.symm
  constructor
  · intro h P hP
    have := h ((ModuleCat.subobjectModule N).symm P) (by
      rw [Ne, key, OrderIso.apply_symm_apply]
      exact hP)
    rwa [Ne, key, OrderIso.map_inf, OrderIso.apply_symm_apply, moduleSubobjectMk] at this
  · intro h B hB
    have := h (ModuleCat.subobjectModule N B) (by rwa [Ne, ← key])
    rwa [Ne, key, OrderIso.map_inf, moduleSubobjectMk]

/-- A scalar acting invertibly on a field embedded essentially in an injective module acts
invertibly on the module. -/
private theorem scalar_isUnit_of_isInjectiveHull
    {R K E : Type u} [CommRing R] [Field K] [Algebra R K] [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R K ⟶ ModuleCat.of R E) [Mono i]
    (hE : CategoryTheory.Injective (ModuleCat.of R E))
    (hess : IsEssentialMono i)
    (r : R) (hr : algebraMap R K r ≠ 0) :
    IsUnit (algebraMap R (Module.End R E) r) := by
  let φ : K →ₗ[R] K :=
    { toFun := fun x => algebraMap R K r * x
      map_add' := by intro x y; simp [mul_add]
      map_smul' := by intro a x; simp [mul_comm] }
  let ψ : Module.End R E := algebraMap R (Module.End R E) r
  have hφ : Function.Injective φ := fun x y h => mul_left_cancel₀ hr h
  have : Mono (ModuleCat.ofHom φ) := (ModuleCat.mono_iff_injective _).mpr hφ
  have hcomm : i ≫ ModuleCat.ofHom ψ = ModuleCat.ofHom φ ≫ i := by
    ext x
    calc
      ψ (i.hom x) = r • i.hom x := by simp [ψ]
      _ = i.hom (r • x) := (i.hom.map_smul r x).symm
      _ = i.hom (φ x) := by congr 1; simp [φ, Algebra.smul_def]
  have hψmono : Mono (ModuleCat.ofHom ψ) :=
    mono_of_isEssentialMono_of_comp_eq i hess (ModuleCat.ofHom φ) i (ModuleCat.ofHom ψ) hcomm
  have : Mono (ModuleCat.ofHom ψ) := hψmono
  have : CategoryTheory.Injective (ModuleCat.of R E) := hE
  let retract : ModuleCat.of R E ⟶ ModuleCat.of R E :=
    Injective.factorThru (𝟙 _) (ModuleCat.ofHom ψ)
  have hretract : ModuleCat.ofHom ψ ≫ retract = 𝟙 _ :=
    Injective.comp_factorThru (𝟙 _) (ModuleCat.ofHom ψ)
  let kerR := LinearMap.ker retract.hom
  let B : Subobject (ModuleCat.of R E) := (ModuleCat.subobjectModule _).symm kerR
  have hrApply (y : E) : retract.hom (ψ y) = y := by
    have hh := congrArg (fun f : ModuleCat.of R E ⟶ ModuleCat.of R E => f y) hretract
    simpa using hh
  have hdisj : kerR ⊓ LinearMap.range i.hom = ⊥ := by
    apply (Submodule.eq_bot_iff (kerR ⊓ LinearMap.range i.hom)).2
    intro x hx
    rcases Submodule.mem_inf.mp hx with ⟨hxker, hxrange⟩
    obtain ⟨m, rfl⟩ := hxrange
    have hφinv : φ ((algebraMap R K r)⁻¹ * m) = m := by
      show algebraMap R K r * ((algebraMap R K r)⁻¹ * m) = m
      simp [hr]
    have hcompApply (y : K) : ψ (i.hom y) = i.hom (φ y) := by
      have hh := congrArg (fun f : ModuleCat.of R K ⟶ ModuleCat.of R E => f y) hcomm
      simpa using hh
    have hzero : retract.hom (i.hom m) = 0 := hxker
    have hcalc : retract.hom (i.hom m) = i.hom ((algebraMap R K r)⁻¹ * m) := by
      calc
        _ = retract.hom (ψ (i.hom ((algebraMap R K r)⁻¹ * m))) := by
          rw [hcompApply, hφinv]
        _ = i.hom ((algebraMap R K r)⁻¹ * m) := by
          simpa using hrApply (i.hom ((algebraMap R K r)⁻¹ * m))
    have hm : (algebraMap R K r)⁻¹ * m = 0 := by
      apply (ModuleCat.mono_iff_injective i).mp inferInstance
      calc
        i.hom ((algebraMap R K r)⁻¹ * m) = retract.hom (i.hom m) := hcalc.symm
        _ = i.hom 0 := by simpa using hzero
    have hm' : m = 0 := (mul_eq_zero.mp hm).resolve_left (inv_ne_zero hr)
    simp [hm']
  have hker : kerR = ⊥ := by
    by_contra hn
    exact (isEssentialMono_iff_inf_range_ne_bot i |>.mp hess) kerR hn hdisj
  have hretractInjective : Function.Injective retract.hom := LinearMap.ker_eq_bot.mp hker
  have hψsurj : Function.Surjective ψ := by
    intro y
    refine ⟨retract.hom y, ?_⟩
    apply hretractInjective
    simpa using hrApply (retract.hom y)
  exact (Module.End.isUnit_iff ψ).mpr ⟨(ModuleCat.mono_iff_injective _).mp hψmono, hψsurj⟩

/-- An `R`-injective module which is also a module over a localization of `R`, compatibly, is
injective over that localization. -/
private theorem injective_over_localization
    {R T E : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (S : Submonoid R) [IsLocalization S T]
    [AddCommGroup E] [Module R E] [Module T E] [IsScalarTower R T E]
    (hE : CategoryTheory.Injective (ModuleCat.of R E)) :
    CategoryTheory.Injective (ModuleCat.of T E) := by
  constructor
  intro X Y g f hf
  let F := ModuleCat.restrictScalars (algebraMap R T)
  let eE := ModuleCat.restrictScalarsAlgebraMapIso (R := R) (ModuleCat.of T E)
  let fR := F.map f
  let gR := F.map g ≫ eE.hom
  have : Mono fR := Functor.map_mono F f
  obtain ⟨hR, hcomp⟩ := hE.factors gR fR
  let : Module R Y := Module.compHom Y (algebraMap R T)
  let : IsScalarTower R T Y := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower R T (F.obj Y) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let eY := ModuleCat.restrictScalarsAlgebraMapEquiv (R := R) Y
  let eYT := eY.extendScalarsOfIsLocalization S T
  let hExt := hR.hom.extendScalarsOfIsLocalization S T
  let hT : Y →ₗ[T] E := hExt.comp eYT.symm.toLinearMap
  refine ⟨ModuleCat.ofHom hT, ?_⟩
  ext y
  have hcomp' := congrArg (fun q : F.obj X ⟶ ModuleCat.of R E => q y) hcomp
  change hR.hom (f y) = eE.hom (g y) at hcomp'
  have he (x : E) : eE.hom (show F.obj (ModuleCat.of T E) from x) = x := by
    show ModuleCat.restrictScalarsAlgebraMapEquiv (R := R)
      (M := ModuleCat.of T E) (show F.obj (ModuleCat.of T E) from x) = x
    exact ModuleCat.restrictScalarsAlgebraMapEquiv_apply _ _
  show hR.hom (eY.symm (f y)) = g y
  rw [ModuleCat.restrictScalarsAlgebraMapEquiv_symm_apply]
  exact hcomp'.trans (he (g y))

/-- Essentiality of an embedding is preserved when the scalars are enlarged to a localization. -/
private theorem essential_localized
    {R T K E : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (S : Submonoid R) [IsLocalization S T] [Field K] [Algebra R K]
    [Module T K] [IsScalarTower R T K]
    [AddCommGroup E] [Module R E] [Module T E] [IsScalarTower R T E]
    (iR : ModuleCat.of R K ⟶ ModuleCat.of R E) [Mono iR]
    (iT : ModuleCat.of T K ⟶ ModuleCat.of T E) [Mono iT]
    (hmap : ∀ x, iT.hom x = iR.hom x)
    (hess : IsEssentialMono iR) :
    IsEssentialMono iT := by
  rw [isEssentialMono_iff_inf_range_ne_bot] at hess ⊢
  intro NT hNT
  let NR : Submodule R E := NT.restrictScalars R
  have hNRne : NR ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff NT).mp hNT
    apply (Submodule.ne_bot_iff NR).mpr
    exact ⟨x, by simpa [NR] using hx, hx0⟩
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp (hess NR hNRne)
  have hxNT : x ∈ NT := by simpa [NR] using hx.1
  obtain ⟨y, hy⟩ := hx.2
  exact (Submodule.ne_bot_iff _).mpr ⟨x, ⟨hxNT, ⟨y, by rw [hmap]; exact hy⟩⟩, hx0⟩

/-- The injective hull of `R ⧸ p` is naturally an injective hull of the residue field at `p` over
`Rₚ`. -/
@[stacks 08Y8 "localized_hull"]
theorem exists_isInjectiveHull_residueField_localization
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (E : ModuleCat.{u} R) (i : ModuleCat.of R (R ⧸ p) ⟶ E) [Mono i]
    (hi : IsInjectiveHull i) :
    ∃ moduleStructure : Module (Localization.AtPrime p) E,
      letI := moduleStructure
      ∃ tower : IsScalarTower R (Localization.AtPrime p) E,
        letI := tower
        ∃ j : ModuleCat.of (Localization.AtPrime p) p.ResidueField ⟶
            ModuleCat.of (Localization.AtPrime p) E,
          ∃ monoJ : Mono j,
            letI := monoJ
            ModuleCat.ofHom
                ((LinearMap.restrictScalars R j.hom).comp
                  (LinearMap.restrictScalars R
                    (Algebra.linearMap (R ⧸ p) p.ResidueField))) = i ∧
              IsInjectiveHull j := by
  let S : Submonoid R := p.primeCompl
  let T := Localization.AtPrime p
  have hKinv : ModuleCat.invertibleSMul S (ModuleCat.of R p.ResidueField) :=
    ModuleCat.invertibleSMul_of_isScalarTower S T p.ResidueField
  let φ : ModuleCat.of R (R ⧸ p) ⟶ ModuleCat.of R p.ResidueField :=
    ModuleCat.ofHom ((Algebra.linearMap (R ⧸ p) p.ResidueField).restrictScalars R)
  have hφ : Function.Injective φ := p.injective_algebraMap_quotient_residueField
  have : Mono φ := (ModuleCat.mono_iff_injective φ).mpr hφ
  have : CategoryTheory.Injective E := hi.1
  let jR : ModuleCat.of R p.ResidueField ⟶ E := Injective.factorThru i φ
  have hφj : φ ≫ jR = i := Injective.comp_factorThru i φ
  have hjR : Function.Injective jR.hom := by
    intro x y hxy
    have hdiff : jR.hom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (R ⧸ p) (x - y)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hb' : algebraMap (R ⧸ p) p.ResidueField (Ideal.Quotient.mk p r) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hscalar : r • (x - y) = φ.hom a := by
      show r • (x - y) = algebraMap (R ⧸ p) p.ResidueField a
      rw [Algebra.smul_def]
      rw [← hab, div_eq_mul_inv]
      rw [← Ideal.algebraMap_quotient_residueField_mk p r]
      calc
        algebraMap (R ⧸ p) p.ResidueField (Ideal.Quotient.mk p r) *
            (algebraMap (R ⧸ p) p.ResidueField a *
              (algebraMap (R ⧸ p) p.ResidueField (Ideal.Quotient.mk p r))⁻¹) =
            algebraMap (R ⧸ p) p.ResidueField a *
              (algebraMap (R ⧸ p) p.ResidueField (Ideal.Quotient.mk p r) *
                (algebraMap (R ⧸ p) p.ResidueField (Ideal.Quotient.mk p r))⁻¹) := by ring
        _ = algebraMap (R ⧸ p) p.ResidueField a := by rw [mul_inv_cancel₀ hb', mul_one]
    have hzero : jR.hom (φ.hom a) = 0 := by
      calc
        _ = jR.hom (r • (x - y)) := congrArg jR.hom hscalar.symm
        _ = r • jR.hom (x - y) := jR.hom.map_smul r _
        _ = 0 := by rw [hdiff, smul_zero]
    have ha : a = 0 := by
      apply (ModuleCat.mono_iff_injective i).mp inferInstance
      have hh : jR.hom (φ.hom a) = i.hom a := by
        have hh := congrArg (fun f : ModuleCat.of R (R ⧸ p) ⟶ E => f a) hφj
        simpa using hh
      rw [← hh]
      simpa using hzero
    have hxy' : x - y = 0 := by rw [← hab, ha]; simp
    exact sub_eq_zero.mp hxy'
  have : Mono jR := (ModuleCat.mono_iff_injective jR).mpr hjR
  have hHullR : IsInjectiveHull jR := ⟨hi.1, fun B hB h => hi.2 B hB
    (le_bot_iff.1 ((inf_le_inf_left B (Subobject.mk_le_mk_of_comm φ hφj)).trans h.le))⟩
  have hEinv : ModuleCat.invertibleSMul S E := by
    intro s
    have hs : algebraMap R p.ResidueField s.1 ≠ 0 := fun h =>
      s.2 ((Ideal.algebraMap_residueField_eq_zero).mp h)
    exact scalar_isUnit_of_isInjectiveHull (R := R) (K := p.ResidueField)
      (E := (E : Type u)) jR hHullR.1 hHullR.2 s.1 hs
  let mT : Module T E := moduleOfInvertibleScalars S T E hEinv
  refine ⟨mT, ?_⟩
  let : Module T E := mT
  let tower : IsScalarTower R T E := moduleOfInvertibleScalars_tower S T E hEinv
  refine ⟨tower, ?_⟩
  let : IsScalarTower R T E := tower
  let : Module T (ModuleCat.of R p.ResidueField) := inferInstanceAs (Module T p.ResidueField)
  let : IsScalarTower R T (ModuleCat.of R p.ResidueField) :=
    inferInstanceAs (IsScalarTower R T p.ResidueField)
  let : IsLocalizedModule S (LinearMap.id : E →ₗ[R] E) :=
    ModuleCat.isLocalizedModule_id_of_invertibleSMul S E hEinv
  let : IsLocalizedModule S (LinearMap.id : p.ResidueField →ₗ[R] p.ResidueField) :=
    ModuleCat.isLocalizedModule_id_of_invertibleSMul S (ModuleCat.of R p.ResidueField) hKinv
  let jT : ModuleCat.of T p.ResidueField ⟶ ModuleCat.of T E :=
    ModuleCat.ofHom (jR.hom.extendScalarsOfIsLocalization S T)
  have hjT : Function.Injective jT.hom := fun x y hxy => hjR hxy
  have : Mono jT := (ModuleCat.mono_iff_injective jT).mpr hjT
  have hcompat :
      ModuleCat.ofHom
        ((LinearMap.restrictScalars R jT.hom).comp
          (LinearMap.restrictScalars R
            (Algebra.linearMap (R ⧸ p) p.ResidueField))) = i := by
    show φ ≫ jR = i
    exact hφj
  have hInjectiveT : CategoryTheory.Injective (ModuleCat.of T E) :=
    injective_over_localization S hi.1
  have hEssT : IsEssentialMono jT := essential_localized S jR jT (fun _ => rfl) hHullR.2
  exact ⟨jT, inferInstance, hcompat, hInjectiveT, hEssT⟩

/-! ### Injective modules over Noetherian rings

Over a Noetherian ring, every injective module is a direct sum of indecomposable injective
modules, and every indecomposable injective module is an injective hull of the residue field at a
prime ideal. The two conclusions of the proposition are stated separately; in the second, a module
in the universe of the given injective module is identified by a linear equivalence with the
residue field, which permits the ring and its modules to live in independent universes. -/

section DirectSumDecomposition

open scoped DirectSum

/-- A module containing `R ⧸ p` as an essential submodule, `p` prime, is indecomposable. -/
private theorem indecomposable_of_essential_prime_quotient
    (R : Type u) [CommRing R] {p : Ideal R} [p.IsPrime]
    (Q : Type v) [AddCommGroup Q] [Module R Q]
    (f : R ⧸ p →ₗ[R] Q) (hf : Function.Injective f)
    (hess : ∀ x : Q, x ≠ 0 → ∃ r : R, r • x ∈ LinearMap.range f ∧ r • x ≠ 0) :
    Indecomposable (ModuleCat.of R Q) := by
  classical
  have hQ : ¬ Limits.IsZero (ModuleCat.of R Q) := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : R ⧸ p)
    exact hx (by
      apply hf
      have := (ModuleCat.isZero_iff_subsingleton.mp h)
      exact Subsingleton.elim _ _)
  refine ⟨hQ, ?_⟩
  intro Y Z e
  by_contra hYZ
  rcases not_or.mp hYZ with ⟨hY0, hZ0⟩
  let F : Q ≃ₗ[R] Y × Z := (e ≪≫ ModuleCat.biprodIsoProd Y Z).toLinearEquiv
  have hY : Nontrivial Y := not_subsingleton_iff_nontrivial.mp fun h => hY0
    (ModuleCat.isZero_iff_subsingleton.mpr h)
  have hZ : Nontrivial Z := not_subsingleton_iff_nontrivial.mp fun h => hZ0
    (ModuleCat.isZero_iff_subsingleton.mpr h)
  obtain ⟨y, hy⟩ := @exists_ne Y hY (0 : Y)
  obtain ⟨z, hz⟩ := @exists_ne Z hZ (0 : Z)
  let ey : Q := F.symm (y, 0)
  let ez : Q := F.symm (0, z)
  have hey : ey ≠ 0 := by
    intro h
    exact hy (by simpa [ey] using congrArg Prod.fst (congrArg F h))
  have hez : ez ≠ 0 := by
    intro h
    exact hz (by simpa [ez] using congrArg Prod.snd (congrArg F h))
  obtain ⟨r, hramem, hraa⟩ := hess ey hey
  obtain ⟨s, hsbmem, hsbb⟩ := hess ez hez
  obtain ⟨a, hra⟩ := hramem
  obtain ⟨b, hsb⟩ := hsbmem
  have hfa : f a ≠ 0 := by
    intro h
    exact hraa (by rw [← hra, h])
  have hfb : f b ≠ 0 := by
    intro h
    exact hsbb (by rw [← hsb, h])
  obtain ⟨aR, haR⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨bR, hbR⟩ := Ideal.Quotient.mk_surjective b
  have ha0 : a ≠ 0 := fun h => hfa (by simp [h])
  have hb0 : b ≠ 0 := fun h => hfb (by simp [h])
  have hab : bR • f a = aR • f b := by
    calc
      bR • f a = f (bR • a) := (map_smul f _ _).symm
      _ = f (aR • b) := by
        congr 1
        rw [← haR, ← hbR]
        simp [Algebra.smul_def, mul_comm]
      _ = aR • f b := map_smul f _ _
  have hab0 : bR • f a ≠ 0 := by
    intro h
    have hprod : (Ideal.Quotient.mk p bR) * a ≠ (0 : R ⧸ p) :=
      mul_ne_zero (by simpa [hbR] using hb0) ha0
    have harg : bR • a = 0 := hf (by simpa [map_smul] using h)
    exact hprod (by simpa [Algebra.smul_def] using harg)
  have hrightzero : Prod.fst (F (aR • f b)) = 0 := by
    rw [map_smul, hsb]
    simp [ez, F]
  have hleftzero' : Prod.snd (F (bR • f a)) = 0 := by
    rw [map_smul, hra]
    simp [ey, F]
  have hzero : F (bR • f a) = 0 := by
    apply Prod.ext
    · simpa [hab] using hrightzero
    · exact hleftzero'
  exact hab0 (F.injective (by simpa using hzero))

/-- A nonzero injective module over a Noetherian ring contains an indecomposable injective
submodule: the injective hull, inside the module, of an associated prime quotient. -/
private theorem exists_injective_indecomposable_submodule
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (C : Type v) [AddCommGroup C] [Module R C] [Module.Injective R C]
    [Nontrivial C] :
    ∃ E : Submodule R C, Module.Injective R E ∧
      Indecomposable (ModuleCat.of R E) := by
  classical
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty R C
  obtain ⟨hp', f, hf⟩ :=
    (isAssociatedPrime_iff_exists_injective_linearMap (I := p) (M := C)).mp hp
  have : p.IsPrime := hp'
  obtain ⟨E, hE₀E, hessE, hEinj⟩ := exists_injective_essential_extension (LinearMap.range f)
  let fE : R ⧸ p →ₗ[R] E := f.codRestrict E (fun x => hE₀E ⟨x, rfl⟩)
  have hfE : Function.Injective fE := fun x y h => hf (congrArg (fun z : E => (z : C)) h)
  have hessE' : ∀ x : E, x ≠ 0 → ∃ r : R, r • x ∈ LinearMap.range fE ∧ r • x ≠ 0 := by
    intro x hx
    obtain ⟨r, hr, hr0⟩ := hessE x hx
    obtain ⟨a, ha⟩ := hr
    refine ⟨r, ⟨a, Subtype.ext ha⟩, ?_⟩
    intro hz
    exact hr0 (by simpa using congrArg (fun z : E => (z : C)) hz)
  exact ⟨E, hEinj, indecomposable_of_essential_prime_quotient R E fE hfE hessE'⟩

/-- A supremum of independent injective submodules is injective. -/
private theorem injective_iSup_of_independent_submodules
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (ι : Type v) (p : ι → Submodule R M)
    (hind : iSupIndep p) (hinj : ∀ i, Module.Injective R (p i)) :
    Module.Injective R (↑(⨆ i, p i) : Type v) := by
  classical
  let S : Submodule R M := ⨆ i, p i
  let f : (⨁ i, p i) →ₗ[R] M := DFinsupp.lsum ℕ fun i => (p i).subtype
  have hf : Function.Injective f := hind.dfinsupp_lsum_injective
  have e₀ : (⨁ i, p i) ≃ₗ[R] LinearMap.range f := LinearEquiv.ofInjective f hf
  have hRange : LinearMap.range f = S := by
    simpa [f] using (Submodule.iSup_eq_range_dfinsupp_lsum p).symm
  let e : (⨁ i, p i) ≃ₗ[R] S := e₀.trans (LinearEquiv.ofEq (LinearMap.range f) S hRange)
  have (i : ι) : Module.Injective R (p i) := hinj i
  exact injective_of_linearEquiv e (directSum_injective R (fun i => (p i : Type v)))

/-- The kernel of a retraction of an injective module onto a submodule is injective. -/
private theorem injective_ker_of_retraction {R : Type u} [Ring R] {M : Type v} [AddCommGroup M]
    [Module R M] [Module.Injective R M] {S : Submodule R M} (r : M →ₗ[R] S)
    (hr : ∀ x : S, r x = x) : Module.Injective R (LinearMap.ker r) := by
  let C := LinearMap.ker r
  let P : M →ₗ[R] M := LinearMap.id - S.subtype.comp r
  let q : M →ₗ[R] C := P.codRestrict C (by
    intro x
    apply LinearMap.mem_ker.mpr
    show r (P x) = 0
    simp [P, hr])
  have hq (x : C) : q x = x := by
    apply Subtype.ext
    show P (x : M) = x
    have hx : r (x : M) = 0 := LinearMap.mem_ker.mp x.property
    show (x : M) - S.subtype (r (x : M)) = (x : M)
    rw [hx]
    simp
  refine ⟨?_⟩
  intro X Y _ _ _ _ f hf g
  obtain ⟨h, hh⟩ := Module.Injective.out (R := R) (Q := M) f hf (C.subtype.comp g)
  refine ⟨q.comp h, ?_⟩
  intro x
  show q (h (f x)) = g x
  rw [hh x]
  exact hq (g x)

/-- Adding a submodule disjoint from the supremum of an independent set keeps it independent. -/
private theorem sSupIndep_insert_of_disjoint_sSup {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] {s : Set (Submodule R M)} (hs : sSupIndep s) {K : Submodule R M}
    (hK : Disjoint (sSup s) K) : sSupIndep (insert K s) := by
  intro A hA
  rcases Set.mem_insert_iff.mp hA with hAK | hAs
  · rw [hAK]
    refine hK.symm.mono_right (sSup_le fun x hx => le_sSup ?_)
    rcases hx with ⟨hx, hxK⟩
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact False.elim (hxK rfl)
    · exact hx
  · let B : Submodule R M := sSup (s \ {A})
    have hB : B ≤ sSup s := sSup_le fun x hx => le_sSup hx.1
    have hrest : sSup ((insert K s) \ {A}) ≤ B ⊔ K := by
      apply sSup_le
      intro x hx
      rcases hx with ⟨hx, hxA⟩
      rcases Set.mem_insert_iff.mp hx with rfl | hxS
      · exact le_sup_right
      · exact le_sup_of_le_left (le_sSup ⟨hxS, by simpa using hxA⟩)
    have hAB : Disjoint A (B ⊔ K) := by
      apply disjoint_iff.mpr
      apply (A ⊓ (B ⊔ K)).eq_bot_iff.mpr
      intro x hx
      have hxA : x ∈ A := hx.1
      obtain ⟨b, hb, k, hk, hbk⟩ := (Submodule.mem_sup.mp hx.2)
      have hkS : k ∈ sSup s := by
        have hxmb : x - b ∈ sSup s := (sSup s).sub_mem (le_sSup hAs hxA) (hB hb)
        have hkEq : x - b = k := by rw [← hbk]; abel
        rwa [hkEq] at hxmb
      have hk0 : k = 0 := (Submodule.mem_bot R).mp
        (disjoint_iff.mp hK ▸ (⟨hkS, hk⟩ : k ∈ sSup s ⊓ K))
      have hxB : x ∈ B := by
        rw [← hbk, hk0, add_zero]
        exact hb
      have hxinf' : x ∈ A ⊓ sSup (s \ {A}) := ⟨hxA, hxB⟩
      exact (Submodule.mem_bot R).mp ((disjoint_iff.mp (hs hAs)) ▸ hxinf')
    exact hAB.mono_right hrest

/-- A nonzero injective submodule of a module over a Noetherian ring contains a nonzero
injective indecomposable submodule. -/
private theorem exists_injective_indecomposable_le (R : Type u) [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {C : Submodule R M} [Module.Injective R C]
    (hC : C ≠ ⊥) : ∃ K : Submodule R M, K ≤ C ∧ K ≠ ⊥ ∧ Module.Injective R K ∧
      Indecomposable (ModuleCat.of R K) := by
  have hCnontrivial : Nontrivial C := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    apply hC
    apply C.eq_bot_iff.mpr
    intro x hx
    have hx0 : (⟨x, hx⟩ : C) = 0 := hsub.elim _ _
    exact congrArg (fun y : C => (y : M)) hx0
  obtain ⟨H, hHinj, hHind⟩ := exists_injective_indecomposable_submodule R C
  let kMap : H →ₗ[R] M := C.subtype.comp H.subtype
  have hkMap : Function.Injective kMap :=
    C.subtype_injective.comp H.subtype_injective
  let K : Submodule R M := LinearMap.range kMap
  have hKinj : Module.Injective R K :=
    injective_of_linearEquiv (LinearEquiv.ofInjective kMap hkMap) hHinj
  let eK : ModuleCat.of R H ≅ ModuleCat.of R K :=
    (LinearEquiv.ofInjective kMap hkMap).toModuleIso
  have hKind : Indecomposable (ModuleCat.of R K) := by
    refine ⟨?_, fun Y Z e => ?_⟩
    · intro hKzero
      apply hHind.1
      apply ModuleCat.isZero_iff_subsingleton.mpr
      have : Subsingleton K := ModuleCat.isZero_iff_subsingleton.mp hKzero
      exact ⟨fun a b => (eK.toLinearEquiv).injective (Subsingleton.elim _ _)⟩
    · exact hHind.2 Y Z (eK ≪≫ e)
  have hKC : K ≤ C := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact (y : C).property
  have hKne : K ≠ ⊥ := by
    intro hKbot
    apply hHind.1
    apply ModuleCat.isZero_iff_subsingleton.mpr
    refine ⟨fun a b => hkMap ?_⟩
    have ha : kMap a = 0 := (Submodule.mem_bot R).mp
      (hKbot ▸ LinearMap.mem_range_self kMap a)
    have hb : kMap b = 0 := (Submodule.mem_bot R).mp
      (hKbot ▸ LinearMap.mem_range_self kMap b)
    exact ha.trans hb.symm
  exact ⟨K, hKC, hKne, hKinj, hKind⟩

/-- An injective module over a Noetherian ring is isomorphic to a direct sum of indecomposable
injective modules. -/
@[stacks 08YA "direct sum decomposition"]
theorem exists_iso_directSum_of_injective
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : ModuleCat.{v} R) [CategoryTheory.Injective I] :
    ∃ (ι : Type v) (E : ι → ModuleCat.{v} R)
      (_ : I ≅ ModuleCat.of R (⨁ i, E i)),
      (∀ i, CategoryTheory.Injective (E i)) ∧ (∀ i, Indecomposable (E i)) := by
  classical
  let Good : Set (Set (Submodule R I)) := {s |
    sSupIndep s ∧ ∀ E ∈ s,
      Module.Injective R E ∧ Indecomposable (ModuleCat.of R E)}
  have hchain : ∀ c : Set (Set (Submodule R I)), c ⊆ Good →
      IsChain (· ⊆ ·) c → ∃ ub ∈ Good, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hcc
    refine ⟨⋃₀ c, ⟨iSupIndep_sUnion_of_directed hcc.directedOn fun t ht => (hc ht).1, ?_⟩,
      fun s hs => Set.subset_sUnion_of_mem hs⟩
    intro E hE
    obtain ⟨t, ht, hEt⟩ := Set.mem_sUnion.mp hE
    exact (hc ht).2 E hEt
  obtain ⟨s, hsGood, hmax⟩ := zorn_subset Good hchain
  obtain ⟨hsInd, hsFacts⟩ := hsGood
  let S : Submodule R I := sSup s
  let p : s → Submodule R I := fun i => i.1
  have hind : iSupIndep p := by
    rw [sSupIndep_iff] at hsInd
    exact hsInd
  have hSinj : Module.Injective R S := by
    have hinjSup : Module.Injective R (↑(⨆ i : s, p i) : Type v) :=
      injective_iSup_of_independent_submodules R (I : Type v) s p hind
        (fun i => (hsFacts i.1 i.2).1)
    have hS_eq : (⨆ i : s, p i) = S := by
      apply le_antisymm
      · exact iSup_le fun i => le_sSup i.property
      · exact sSup_le fun E hE => le_iSup (fun i : s => p i) ⟨E, hE⟩
    exact injective_of_linearEquiv (LinearEquiv.ofEq (⨆ i : s, p i) S hS_eq) hinjSup
  have hIinj : Module.Injective R I := Module.injective_module_of_injective_object R I
  let j : S →ₗ[R] I := S.subtype
  obtain ⟨r, hr⟩ := Module.Injective.out (R := R) (Q := S)
    j S.subtype_injective LinearMap.id
  let C : Submodule R I := LinearMap.ker r
  have hSC : Disjoint S C := by
    apply disjoint_iff.mpr
    apply (S ⊓ C).eq_bot_iff.mpr
    intro x hx
    have hxS : x ∈ S := hx.1
    have hrx0 : r x = 0 := LinearMap.mem_ker.mp hx.2
    have hxS0 : (⟨x, hxS⟩ : S) = 0 := (hr ⟨x, hxS⟩).symm.trans hrx0
    exact congrArg (fun y : S => (y : I)) hxS0
  have hCinj : Module.Injective R C := injective_ker_of_retraction r hr
  have hStop : S = ⊤ := by
    by_contra hS
    have hCne : C ≠ ⊥ := by
      intro hC
      apply hS
      apply le_antisymm le_top
      intro x _
      let P : I →ₗ[R] I := LinearMap.id - j.comp r
      have hmem : P x ∈ C := by
        apply LinearMap.mem_ker.mpr
        show r (P x) = 0
        simp [P, hr]
      have hz : P x = 0 := by
        rw [hC] at hmem
        simpa using hmem
      have hxEq : x = j (r x) := by
        have hx0 : x - j (r x) = 0 := hz
        exact sub_eq_zero.mp hx0
      rw [hxEq]
      exact (r x).property
    obtain ⟨K, hKC, hKne, hKinj, hKind⟩ := exists_injective_indecomposable_le R hCne
    have hKnot : K ∉ s := by
      intro hKs
      have hKbot : K ≤ ⊥ := (le_inf (le_sSup hKs) hKC).trans hSC.le_bot
      exact hKne (bot_unique hKbot)
    have hTind : sSupIndep (insert K s) :=
      sSupIndep_insert_of_disjoint_sSup hsInd (hSC.mono_right hKC)
    have hTfacts : ∀ A ∈ insert K s,
        Module.Injective R A ∧ Indecomposable (ModuleCat.of R A) := by
      intro A hA
      rcases Set.mem_insert_iff.mp hA with rfl | hAs
      · exact ⟨hKinj, hKind⟩
      · exact hsFacts A hAs
    exact hKnot (hmax ⟨hTind, hTfacts⟩ (Set.subset_insert _ _) (Set.mem_insert _ _))
  let eI : (⨁ i : s, (i.1 : Submodule R I)) ≃ₗ[R] I := hind.linearEquiv (by
    show (⨆ i : s, (i.1 : Submodule R I)) = ⊤
    change sSup s = ⊤ at hStop
    rw [sSup_eq_iSup] at hStop
    simpa only [iSup_subtype] using hStop)
  refine ⟨s, fun i => ModuleCat.of R (i.1 : Submodule R I),
    (LinearEquiv.toModuleIso eI).symm, ?_, ?_⟩
  · intro i
    have : Module.Injective R (i.1 : Submodule R I) := (hsFacts i.1 i.2).1
    exact Module.injective_object_of_injective_module R (i.1 : Submodule R I)
  · intro i
    exact (hsFacts i.1 i.2).2

/-- An indecomposable injective module over a Noetherian ring is an injective hull of the residue
field at a prime ideal. -/
@[stacks 08YA "indecomposable injective modules"]
theorem exists_residueField_injectiveHull
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (E : ModuleCat.{v} R) [CategoryTheory.Injective E] (hE : Indecomposable E) :
    ∃ (p : Ideal R) (hp : p.IsPrime),
      letI := hp
      ∃ (K : ModuleCat.{v} R) (_ : K ≃ₗ[R] p.ResidueField)
        (i : K ⟶ E) (hi : Mono i),
        letI := hi
        IsInjectiveHull i := by
  obtain ⟨p, K, hK, i, hi, h⟩ := exists_isInjectiveHull_residueField_of_indecomposable R E hE
  obtain ⟨e⟩ := hK
  exact ⟨p.asIdeal, p.isPrime, K, e, i, hi, h⟩

end DirectSumDecomposition
end Module
