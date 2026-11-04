module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.RingTheory.Length.Defs

/-!
# Matlis duality over an Artinian local ring

Let `R` be an Artinian local ring with residue field `κ`, and let `E` be an injective hull of `κ`
as an `R`-module.  Taking `R`-linear maps into `E` is an exact, length-preserving duality on
finite `R`-modules: the length of `Hom_R(M, E)` equals the length of `M`, the hull `E` itself is a
finite `R`-module, every finite module is canonically identified with its double `E`-dual, and the
scalar action identifies `R` with `End_R(E)`.  Packaged categorically, `Hom_R(-, E)` is an
anti-equivalence of the category of finitely generated `R`-modules with itself which preserves
finite limits and finite colimits.

Throughout, the maximal ideal and residue field of `R` are Mathlib's `IsLocalRing.maximalIdeal R`
and `IsLocalRing.ResidueField R`, and the injective hull is presented by the chosen essential
monomorphism `i : κ ⟶ E` in `ModuleCat R`.

## Main definitions

* `Dualizing.injectiveHullDualObj` — the `E`-valued dual of a finite module, again finite.
* `Dualizing.injectiveHullDual` — the contravariant `E`-valued dual functor on `FGModuleCat R`.
* `Dualizing.injectiveHullDualEvaluation` — the natural transformation whose components are the
  canonical evaluation maps `m ↦ (f ↦ f m)` into the `E`-valued double dual.

## Main results

* `Dualizing.length_linearMap_eq` — taking linear maps into `E` preserves the length of a finite
  module.
* `Dualizing.finite_of_isInjectiveHull_residueField` — `E` is a finite `R`-module.
* `Dualizing.evaluation_bijective_of_isInjectiveHull` — a finite module is canonically identified
  with its double `E`-dual.
* `Dualizing.algebraMap_end_bijective_of_isInjectiveHull` — the canonical map `R → End_R(E)` is
  bijective.
* `Dualizing.injectiveHullDual_isEquivalence` — `Hom_R(-, E)` is an anti-equivalence of
  `FGModuleCat R` with itself.
* `Dualizing.injectiveHullDual_preservesFiniteLimits` and
  `Dualizing.injectiveHullDual_preservesFiniteColimits` — exactness of the duality.
* `Dualizing.injectiveHullDualEvaluation_isIso` — the canonical double-dual identification.

## References

* [Stacks Project, Tag 08YX](https://stacks.math.columbia.edu/tag/08YX)
* [Stacks Project, Tag 08YY](https://stacks.math.columbia.edu/tag/08YY)
* [Stacks Project, Tag 08YZ](https://stacks.math.columbia.edu/tag/08YZ)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace Dualizing

/-- Under the order isomorphism between subobjects of a module and its submodules, the subobject
of a monomorphism corresponds to the range of that monomorphism. -/
public lemma subobjectModule_mk_eq_range {R : Type u} [Ring R] {M N : ModuleCat.{v} R}
    (i : M ⟶ N) [Mono i] :
    ModuleCat.subobjectModule N (Subobject.mk i) = LinearMap.range i.hom := by
  change LinearMap.range ((Subobject.mk i).arrow.hom) = LinearMap.range i.hom
  have h := congrArg (fun f => LinearMap.range f.hom)
    (Subobject.underlyingIso_hom_comp_eq_mk i)
  rw [← h]
  change (i.hom ∘ₗ (Subobject.underlyingIso i).hom.hom).range = i.hom.range
  exact (Subobject.underlyingIso i).toLinearEquiv.range_comp i.hom

/-- The linear map underlying the chosen monomorphism from the residue field is injective. -/
private lemma hom_injective {R : Type u} [CommRing R] [IsLocalRing R] {E : Type u}
    [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (IsLocalRing.ResidueField R) ⟶ ModuleCat.of R E) [Mono i] :
    Function.Injective i.hom :=
  (ModuleCat.mono_iff_injective i).mp inferInstance

section LengthDuality

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
variable (E : Type u) [AddCommGroup E] [Module R E]
variable (i : ModuleCat.of R (IsLocalRing.ResidueField R) ⟶ ModuleCat.of R E) [Mono i]

omit [IsArtinianRing R] in
private lemma essential_range (hi : Module.IsInjectiveHull i)
    (N : Submodule R E) (hN : N ≠ ⊥) : N ⊓ LinearMap.range i.hom ≠ ⊥ := by
  let e := ModuleCat.subobjectModule (ModuleCat.of R E)
  have hS : e.symm N ≠ ⊥ := fun h => hN (by rw [← e.apply_symm_apply N, h, e.map_bot])
  have h := hi.2 (e.symm N) hS
  intro hz
  apply h
  apply e.injective
  rw [e.map_inf, e.map_bot, e.apply_symm_apply]
  change N ⊓ (ModuleCat.subobjectModule (ModuleCat.of R E)) (Subobject.mk i) = ⊥
  rw [subobjectModule_mk_eq_range i]
  exact hz

omit [IsArtinianRing R] in
private lemma residueField_isSimpleModule :
    IsSimpleModule R (IsLocalRing.ResidueField R) :=
  (isSimpleModule_iff_isCoatom).2
    (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal R))

private noncomputable def residueRangeEquiv :
    IsLocalRing.ResidueField R ≃ₗ[R] LinearMap.range i.hom :=
  LinearEquiv.ofInjective i.hom (hom_injective i)

omit [IsArtinianRing R] in
private lemma range_isSimpleModule : IsSimpleModule R (LinearMap.range i.hom) := by
  have := residueField_isSimpleModule R
  exact IsSimpleModule.congr (residueRangeEquiv R E i).symm

omit [IsLocalRing R] [IsArtinianRing R] in
private lemma range_isSimpleModule_of_ne_zero {M N : Type*}
    [AddCommGroup M] [Module R M] [IsSimpleModule R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hf : f ≠ 0) :
    IsSimpleModule R (LinearMap.range f) := by
  exact IsSimpleModule.congr (LinearEquiv.ofInjective f (LinearMap.injective_of_ne_zero hf)).symm

omit [IsArtinianRing R] in
private lemma range_le_hull (hi : Module.IsInjectiveHull i)
    (f : IsLocalRing.ResidueField R →ₗ[R] E) :
    LinearMap.range f ≤ LinearMap.range i.hom := by
  by_cases hf : f = 0
  · simp [hf]
  have := residueField_isSimpleModule R
  have hfatom : IsAtom (LinearMap.range f) :=
    isSimpleModule_iff_isAtom.mp (range_isSimpleModule_of_ne_zero R f hf)
  have hiatom : IsAtom (LinearMap.range i.hom) :=
    isSimpleModule_iff_isAtom.mp (range_isSimpleModule R E i)
  have hmeet := essential_range R E i hi (LinearMap.range f)
    (fun h => hf (LinearMap.range_eq_bot.mp h))
  exact le_of_eq (((hfatom.le_iff_eq hmeet).mp inf_le_left).symm.trans
    ((hiatom.le_iff_eq hmeet).mp inf_le_right))

private noncomputable def endEvalOne :
    (IsLocalRing.ResidueField R →ₗ[R] IsLocalRing.ResidueField R) →ₗ[R]
      IsLocalRing.ResidueField R where
  toFun f := f 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsArtinianRing R] in
private lemma endEvalOne_bijective : Function.Bijective (endEvalOne R) := by
  constructor
  · intro f g h
    ext x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    have hx : IsLocalRing.residue R r = r • (1 : IsLocalRing.ResidueField R) := by
      simp [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq]
    rw [hx, map_smul, map_smul]
    exact congrArg (fun y : IsLocalRing.ResidueField R => r • y) h
  · intro x
    exact ⟨LinearMap.mulLeft R x, by simp [endEvalOne]⟩

omit [IsArtinianRing R] in
private lemma compRight_hull_bijective (hi : Module.IsInjectiveHull i) :
    Function.Bijective
      (LinearMap.compRight R i.hom :
        (IsLocalRing.ResidueField R →ₗ[R] IsLocalRing.ResidueField R) →ₗ[R]
          (IsLocalRing.ResidueField R →ₗ[R] E)) := by
  constructor
  · intro f g h
    ext x
    exact hom_injective i (congrArg (fun q : IsLocalRing.ResidueField R →ₗ[R] E => q x) h)
  · intro f
    let c : IsLocalRing.ResidueField R →ₗ[R] LinearMap.range i.hom :=
      f.codRestrict (LinearMap.range i.hom)
        (fun x => range_le_hull R E i hi f (LinearMap.mem_range_self f x))
    let g : IsLocalRing.ResidueField R →ₗ[R] IsLocalRing.ResidueField R :=
      (residueRangeEquiv R E i).symm.toLinearMap.comp c
    refine ⟨g, ?_⟩
    ext x
    change i.hom (g x) = f x
    exact congrArg Subtype.val ((residueRangeEquiv R E i).apply_symm_apply (c x))

omit [IsArtinianRing R] in
private lemma length_hom_residueField (hi : Module.IsInjectiveHull i) :
    Module.length R (IsLocalRing.ResidueField R →ₗ[R] E) = 1 := by
  have := residueField_isSimpleModule R
  let e₁ := LinearEquiv.ofBijective
    (LinearMap.compRight R i.hom :
      (IsLocalRing.ResidueField R →ₗ[R] IsLocalRing.ResidueField R) →ₗ[R]
        (IsLocalRing.ResidueField R →ₗ[R] E))
    (compRight_hull_bijective R E i hi)
  let e₂ := LinearEquiv.ofBijective (endEvalOne R) (endEvalOne_bijective R)
  calc
    Module.length R (IsLocalRing.ResidueField R →ₗ[R] E) =
        Module.length R (IsLocalRing.ResidueField R →ₗ[R] IsLocalRing.ResidueField R) :=
      e₁.length_eq.symm
    _ = Module.length R (IsLocalRing.ResidueField R) := e₂.length_eq
    _ = 1 := Module.length_eq_one R (IsLocalRing.ResidueField R)

omit [IsArtinianRing R] in
private lemma simple_equiv_residueField {S : Type v} [AddCommGroup S]
    [Module R S] [IsSimpleModule R S] :
    Nonempty (S ≃ₗ[R] IsLocalRing.ResidueField R) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (inferInstance : IsSimpleModule R S)
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact ⟨e⟩

omit [IsArtinianRing R] in
private lemma length_hom_simple (hi : Module.IsInjectiveHull i)
    (S : Type v) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    Module.length R (S →ₗ[R] E) = Module.length R S := by
  obtain ⟨e⟩ := simple_equiv_residueField (S := S) R
  calc
    Module.length R (S →ₗ[R] E) =
        Module.length R (IsLocalRing.ResidueField R →ₗ[R] E) :=
      (LinearEquiv.arrowCongr e (LinearEquiv.refl R E)).length_eq
    _ = 1 := length_hom_residueField R E i hi
    _ = Module.length R S := (Module.length_eq_one R S).symm

omit [IsArtinianRing R] in
private lemma length_hom_eq_add (hi : Module.IsInjectiveHull i)
    {M : Type v} [AddCommGroup M] [Module R M] (N : Submodule R M) :
    Module.length R (M →ₗ[R] E) =
      Module.length R ((M ⧸ N) →ₗ[R] E) + Module.length R (N →ₗ[R] E) := by
  have : Module.Injective R E := Module.injective_module_of_injective_object R E (inj := hi.1)
  let f : ((M ⧸ N) →ₗ[R] E) →ₗ[R] (M →ₗ[R] E) :=
    LinearMap.lcomp R E N.mkQ
  let g : (M →ₗ[R] E) →ₗ[R] (N →ₗ[R] E) :=
    LinearMap.lcomp R E N.subtype
  have hf : Function.Injective f :=
    LinearMap.lcomp_injective_of_surjective N.mkQ N.mkQ_surjective
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨b, hb⟩ := Module.Injective.extension_property R E N M
      N.subtype N.subtype_injective a
    exact ⟨b, by simpa [g, LinearMap.lcomp_apply'] using hb⟩
  have hfg : Function.Exact f g := by
    apply LinearMap.exact_of_comp_eq_zero_of_ker_le_range
    · ext a x
      simp [f, g, LinearMap.lcomp_apply,
        (Submodule.Quotient.mk_eq_zero N (x := (x : M))).mpr x.property]
    · intro a ha
      have hzero : a.comp N.subtype = 0 := by
        simpa [g, LinearMap.lcomp_apply'] using ha
      have hker : N ≤ LinearMap.ker a := by
        intro x hx
        have hx' := congrArg (fun q : N →ₗ[R] E => q ⟨x, hx⟩) hzero
        simpa using hx'
      refine ⟨N.liftQ a hker, ?_⟩
      ext x
      rfl
  exact Module.length_eq_add_of_exact f g hf hg hfg

omit [IsArtinianRing R] in
private lemma length_hom_eq_of_finiteLength (hi : Module.IsInjectiveHull i)
    {M : Type v} [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Module.length R (M →ₗ[R] E) = Module.length R M := by
  induction hM with
  | @of_subsingleton M _ _ _ =>
      have : Subsingleton (M →ₗ[R] E) := ⟨by
        intro f g
        ext x
        have hx : x = 0 := Subsingleton.elim x 0
        simp [hx]⟩
      simp
  | @of_simple_quotient M _ _ N _ hN ih =>
      have h₁ := length_hom_eq_add R E i hi N
      have h₂ := length_hom_simple R E i hi (M ⧸ N)
      have h₃ := Module.length_eq_add_of_exact N.subtype N.mkQ
        N.subtype_injective N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
      rw [h₁, h₂, ih, add_comm, ← h₃]

/-- **Stacks Project, Tag 08YX.** Taking linear maps into an injective hull of
the residue field preserves the length of a finite module. -/
@[stacks 08YX "length equality"]
public lemma length_linearMap_eq (hi : Module.IsInjectiveHull i)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.length R (M →ₗ[R] E) = Module.length R M :=
  length_hom_eq_of_finiteLength R E i hi
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

/-- **Stacks Project, Tag 08YX.** An injective hull of the residue field of an
Artinian local ring is finite over the ring. -/
@[stacks 08YX "finiteness of the injective hull"]
public lemma finite_of_isInjectiveHull_residueField
    (hi : Module.IsInjectiveHull i) : Module.Finite R E := by
  have h : Module.length R E = Module.length R R := by
    rw [← (LinearMap.ringLmapEquivSelf R R E).length_eq]
    exact length_linearMap_eq R E i hi R
  have hfinite : IsFiniteLength R E := Module.length_ne_top_iff.mp (h ▸ Module.length_ne_top)
  have : IsNoetherian R E := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).1
  infer_instance

end LengthDuality

section Evaluation

private lemma separates_points
    (R : Type u) [CommRing R] [IsLocalRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (IsLocalRing.ResidueField R) ⟶ ModuleCat.of R E)
    [Mono i]
    (hinj : Injective (ModuleCat.of R E))
    (M : Type v) [AddCommGroup M] [Module R M]
    (x : M) (hx : x ≠ 0) :
    ∃ f : M →ₗ[R] E, f x ≠ 0 := by
  let f : R →ₗ[R] M := LinearMap.toSpanSingleton R M x
  let g : R →ₗ[R] IsLocalRing.ResidueField R := Algebra.linearMap R _
  have hproper : LinearMap.ker f ≠ ⊤ := by
    intro h
    have : f 1 = 0 := (LinearMap.mem_ker).mp (h ▸ Submodule.mem_top)
    exact hx (by simpa [f] using this)
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro r hr
    change g r = 0
    change algebraMap R (IsLocalRing.ResidueField R) r = 0
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact (IsLocalRing.residue_eq_zero_iff r).mpr
      (IsLocalRing.le_maximalIdeal hproper hr)
  let q : LinearMap.range f →ₗ[R] IsLocalRing.ResidueField R :=
    (LinearMap.ker f).liftQ g hker ∘ₗ f.quotKerEquivRange.symm.toLinearMap
  let j : LinearMap.range f →ₗ[R] M := (LinearMap.range f).subtype
  have : Module.Injective R E := (Module.injective_iff_injective_object R E).mpr hinj
  obtain ⟨h, hh⟩ := Module.Injective.extension_property R E _ _ j
    (Submodule.subtype_injective _) (i.hom ∘ₗ q)
  refine ⟨h, ?_⟩
  have hf : f 1 = x := by simp [f]
  have hq : q ⟨x, hf ▸ LinearMap.mem_range_self f 1⟩ = 1 := by
    calc
      q ⟨x, hf ▸ LinearMap.mem_range_self f 1⟩ = g 1 := by
        simp only [q, LinearMap.comp_apply]
        change (LinearMap.ker f).liftQ g hker
          (f.quotKerEquivRange.symm ⟨x, hf ▸ LinearMap.mem_range_self f 1⟩) = g 1
        rw [show f.quotKerEquivRange.symm ⟨x, hf ▸ LinearMap.mem_range_self f 1⟩ =
          (LinearMap.ker f).mkQ 1 by simp [← hf]]
        exact Submodule.liftQ_apply (LinearMap.ker f) g 1
      _ = 1 := by simp [g]
  have := LinearMap.congr_fun hh ⟨x, hf ▸ LinearMap.mem_range_self f 1⟩
  have hi : i.hom (1 : IsLocalRing.ResidueField R) ≠ 0 := fun hz =>
    one_ne_zero (hom_injective i (by simpa using hz))
  simp only [LinearMap.comp_apply, hq] at this
  exact fun hz => hi (this ▸ hz)

/-- **Stacks Project, Tag 08YY.** Evaluation into an injective hull of the
residue field identifies every finite module over an Artinian local ring with
its double dual. -/
@[stacks 08YY "the evaluation map"]
public theorem evaluation_bijective_of_isInjectiveHull
    (R : Type u) [CommRing R] [IsArtinianRing R] [IsLocalRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (IsLocalRing.ResidueField R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Bijective
      (LinearMap.flip
        (LinearMap.id : (M →ₗ[R] E) →ₗ[R] (M →ₗ[R] E))) := by
  let e : M →ₗ[R] ((M →ₗ[R] E) →ₗ[R] E) :=
    LinearMap.flip (LinearMap.id : (M →ₗ[R] E) →ₗ[R] (M →ₗ[R] E))
  have he : Function.Injective e := by
    apply LinearMap.ker_eq_bot.mp
    ext x
    constructor
    · intro hx
      by_contra hn
      obtain ⟨f, hf⟩ := separates_points R E i hi.1 M x hn
      have := LinearMap.congr_fun hx f
      exact hf (by simpa [e] using this)
    · intro hx
      simp [show x = 0 by simpa using hx]
  have : Module.Finite R E := finite_of_isInjectiveHull_residueField R E i hi
  have : Module.Finite R (M →ₗ[R] E) := inferInstance
  have : Module.Finite R ((M →ₗ[R] E) →ₗ[R] E) := inferInstance
  have hlen := (length_linearMap_eq R E i hi (M →ₗ[R] E)).trans
    (length_linearMap_eq R E i hi M)
  have hs : Function.Surjective e := by
    rw [← LinearMap.range_eq_top]
    by_contra hn
    have hl := Submodule.length_lt (R := R) hn
    have heq := (LinearEquiv.ofInjective e he).length_eq.symm
    exact (not_lt_of_ge (by rw [heq, ← hlen])) hl
  exact ⟨he, hs⟩

/-- **Stacks Project, Tag 08YY.** The canonical scalar-action map from an
Artinian local ring to the endomorphism ring of an injective hull of its
residue field is bijective. -/
@[stacks 08YY "the endomorphism ring"]
public theorem algebraMap_end_bijective_of_isInjectiveHull
    (R : Type u) [CommRing R] [IsArtinianRing R] [IsLocalRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (IsLocalRing.ResidueField R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i) :
    Function.Bijective (algebraMap R (Module.End R E)) := by
  let e := LinearMap.ringLmapEquivSelf R R E
  have ht := evaluation_bijective_of_isInjectiveHull R E i hi R
  constructor
  · intro a b hab
    apply ht.1
    apply LinearMap.ext
    intro g
    have h := congrArg (fun z : Module.End R E => z (e g)) hab
    have hga : g a = a • e g := by simpa [e] using (g.map_smul a (1 : R))
    have hgb : g b = b • e g := by simpa [e] using (g.map_smul b (1 : R))
    simpa [Module.algebraMap_end_apply, hga, hgb] using h
  · intro f
    let F : (R →ₗ[R] E) →ₗ[R] E := f ∘ₗ e.toLinearMap
    obtain ⟨r, hr⟩ := ht.2 F
    refine ⟨r, ?_⟩
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun hr (e.symm x)
    simpa [F, e, Module.algebraMap_end_apply] using h

end Evaluation

section DualityFunctor

open CategoryTheory.Limits

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
variable (E : Type u) [AddCommGroup E] [Module R E]
variable (i : ModuleCat.of R (IsLocalRing.ResidueField R) ⟶ ModuleCat.of R E)
  [Mono i] (hi : Module.IsInjectiveHull i)

/-- The `E`-valued dual of a finite module, as a finite module. -/
public def injectiveHullDualObj (M : FGModuleCat.{u} R) : FGModuleCat.{u} R := by
  letI : Module.Finite R E :=
    finite_of_isInjectiveHull_residueField R E i hi
  exact FGModuleCat.of R (M →ₗ[R] E)

/-- Taking linear maps into the injective hull, contravariantly, on finite modules. -/
@[stacks 08YZ "the duality functor"]
public def injectiveHullDual : (FGModuleCat.{u} R)ᵒᵖ ⥤ FGModuleCat.{u} R where
  obj M := injectiveHullDualObj R E i hi M.unop
  map := fun {X Y} f => by
    letI : Module.Finite R E :=
      finite_of_isInjectiveHull_residueField R E i hi
    exact FGModuleCat.ofHom {
      toFun := fun g => g.comp f.unop.hom.hom
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  map_id := by intros; apply FGModuleCat.hom_ext; ext; rfl
  map_comp := by intros; apply FGModuleCat.hom_ext; ext; rfl

/-- The natural transformation with components the canonical evaluation maps
`m ↦ (f ↦ f m)` into the `E`-valued double dual. -/
@[stacks 08YZ "canonical evaluation transformation"]
public def injectiveHullDualEvaluation :
    𝟭 (FGModuleCat.{u} R) ⟶
      opOp (FGModuleCat.{u} R) ⋙ (injectiveHullDual R E i hi).op ⋙
        injectiveHullDual R E i hi where
  app M := by
    letI : Module.Finite R E :=
      finite_of_isInjectiveHull_residueField R E i hi
    exact FGModuleCat.ofHom
      (LinearMap.flip (LinearMap.id : (M →ₗ[R] E) →ₗ[R] (M →ₗ[R] E)))
  naturality := by
    intros
    apply FGModuleCat.hom_ext
    ext
    rfl

private theorem injectiveHullDualEvaluation_isIso_private :
    IsIso (injectiveHullDualEvaluation R E i hi) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have : Module.Finite R E :=
    finite_of_isInjectiveHull_residueField R E i hi
  dsimp [injectiveHullDualEvaluation]
  let D : FGModuleCat R :=
    (injectiveHullDual R E i hi).obj (Opposite.op M)
  let ev : (M : Type u) →ₗ[R] (D →ₗ[R] E) :=
    LinearMap.flip (LinearMap.id : (M →ₗ[R] E) →ₗ[R] (M →ₗ[R] E))
  have hev : Function.Bijective ev :=
    evaluation_bijective_of_isInjectiveHull R E i hi (M := (M : Type u))
  let e : (M : Type u) ≃ₗ[R] (D →ₗ[R] E) := LinearEquiv.ofBijective ev hev
  refine ⟨FGModuleCat.ofHom e.symm, ?_, ?_⟩ <;> apply FGModuleCat.hom_ext <;> ext x
  · exact e.left_inv x
  · exact e.right_inv x

/-- **Stacks Project, Tag 08YZ.** Linear duality with values in an injective hull of the residue
field is an anti-equivalence of the category of finite modules with itself. -/
@[stacks 08YZ "anti-equivalence"]
public theorem injectiveHullDual_isEquivalence :
    (injectiveHullDual R E i hi).IsEquivalence := by
  let F := injectiveHullDual R E i hi
  let G : FGModuleCat.{u} R ⥤ (FGModuleCat.{u} R)ᵒᵖ :=
    opOp (FGModuleCat.{u} R) ⋙ F.op
  have : IsIso (injectiveHullDualEvaluation R E i hi) :=
    injectiveHullDualEvaluation_isIso_private R E i hi
  have τ : (G ⋙ F).op ≅ F ⋙ G := by
    cat_disch
  exact Functor.IsEquivalence.mk' G
    ((Functor.opId (FGModuleCat.{u} R)).symm ≪≫
      (NatIso.op (asIso (injectiveHullDualEvaluation R E i hi))).symm ≪≫ τ)
    (asIso (injectiveHullDualEvaluation R E i hi)).symm

/-- **Stacks Project, Tag 08YZ.** The `E`-valued duality preserves finite limits, hence takes
finite colimits of finite modules to finite limits. -/
@[stacks 08YZ "exactness: limits"]
public theorem injectiveHullDual_preservesFiniteLimits :
    PreservesFiniteLimits (injectiveHullDual R E i hi) := by
  have := injectiveHullDual_isEquivalence R E i hi
  infer_instance

/-- **Stacks Project, Tag 08YZ.** The `E`-valued duality preserves finite colimits, hence takes
finite limits of finite modules to finite colimits. -/
@[stacks 08YZ "exactness: colimits"]
public theorem injectiveHullDual_preservesFiniteColimits :
    PreservesFiniteColimits (injectiveHullDual R E i hi) := by
  have := injectiveHullDual_isEquivalence R E i hi
  infer_instance

/-- The canonical evaluation maps give a natural isomorphism from the
identity functor to the square of the `E`-valued duality. -/
@[stacks 08YZ "canonical double-dual identification"]
public theorem injectiveHullDualEvaluation_isIso :
    IsIso (injectiveHullDualEvaluation R E i hi) :=
  injectiveHullDualEvaluation_isIso_private R E i hi

end DualityFunctor

end Dualizing
