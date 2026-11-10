module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Basic.Countable.Small
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Logic.Small.Basic
public import Mathlib.Logic.Small.Set

@[expose] public section

/-!
# `I`-projective modules

Let `R` be a commutative ring, `I ⊆ R` an ideal and `M` an `R`-module. The module `M` is
`I`-projective when for every `a ∈ I` the multiplication-by-`a` endomorphism of `M` factors
through a projective `R`-module.

## Main definitions

* `FactorsThroughProj`: an `R`-linear map factors through a projective `R`-module.
* `FactorsThroughFree`: an `R`-linear map factors through a free `R`-module.
* `FactorsThroughProj.submodule`: the submodule of `M →ₗ[R] N` of maps factoring through a
  projective module ([stacks 0G90] (2)).
* `Module.IsIProjective`: `M` is `I`-projective ([stacks 0G93]).

## Main results

* `factorsThroughProj_iff_free`: factoring through a projective module is the same as factoring
  through a free module ([stacks 0G90] (1)).
* `FactorsThroughProj.comp_comp`: factoring through a projective module is stable under pre- and
  post-composition ([stacks 0G90] (3)).
* `Module.exists_finite_projective_factorization`: a map out of a finite module which factors
  through a projective module already factors through a *finite* projective module
  ([stacks 0G91]).
* `Module.isIProjective_iff_free`: `M` is `I`-projective if and only if multiplication by each
  element of `I` factors through a free module, which is the equivalence of conditions (1) and (2)
  of [stacks 0G92].
* `Module.isIProjective_iff_ext_annihilated`: `M` is `I`-projective if and only if `I` annihilates
  `Ext¹_R(M, N)` for every `R`-module `N`, which is the equivalence of conditions (1) and (3) of
  [stacks 0G92].
* `Module.isIProjective_of_smul_eq_zero`: a module annihilated by `I` is `I`-projective
  ([stacks 0G94]).
* `Module.isIProjective_of_injective_of_exact`: the kernel of a projective presentation of an
  `I`-projective module is `I`-projective ([stacks 0G95]).
* `Module.IsIProjective.dual`: the dual of a finite `I`-projective module is `I`-projective
  ([stacks 0G96]).
-/

universe u v w p

/-- An `R`-linear map `φ : M →ₗ[R] N` *factors through a projective `R`-module* if there are a
projective `R`-module `P` and `R`-linear maps `α : M →ₗ[R] P`, `β : P →ₗ[R] N` with
`φ = β ∘ₗ α`. -/
def FactorsThroughProj {R : Type u} {M : Type v} {N : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) : Prop :=
  ∃ (P : Type (max u v w)) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Projective R P)
    (α : M →ₗ[R] P) (β : P →ₗ[R] N), φ = β ∘ₗ α

/-- An `R`-linear map `φ : M →ₗ[R] N` *factors through a free `R`-module* if there are an index
type `J` and `R`-linear maps `σ : M →ₗ[R] (J →₀ R)`, `τ : (J →₀ R) →ₗ[R] N` with `φ = τ ∘ₗ σ`. -/
def FactorsThroughFree {R : Type u} {M : Type v} {N : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) : Prop :=
  ∃ (J : Type (max u v w)) (σ : M →ₗ[R] (J →₀ R)) (τ : (J →₀ R) →ₗ[R] N), φ = τ ∘ₗ σ

/-- A linear map factors through a projective module if and only if it factors through a free
module. -/
@[stacks 0G90 "(1)"]
theorem factorsThroughProj_iff_free
    {R : Type u} {M : Type v} {N : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) :
    FactorsThroughProj φ ↔ FactorsThroughFree φ := by
  constructor
  · rintro ⟨P, _, _, hP, α, β, hφ⟩
    obtain ⟨s, hs⟩ := Module.projective_def'.mp hP
    have key : ∀ p : P, Finsupp.linearCombination R id (s p) = p := fun p => by
      simpa using LinearMap.congr_fun hs p
    exact ⟨P, s ∘ₗ α, β ∘ₗ Finsupp.linearCombination R id, by ext m; simp [hφ, key]⟩
  · rintro ⟨J, σ, τ, hφ⟩
    exact ⟨(J →₀ R), inferInstance, inferInstance, inferInstance, σ, τ, hφ⟩

/-- A factorization through a projective module living in an arbitrary universe, provided that
module is small enough to be replaced by an equivalent one in `Type (max u v w)`. -/
theorem FactorsThroughProj.mk' {R : Type u} {M : Type v} {N : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {φ : M →ₗ[R] N}
    {P : Type p} [AddCommGroup P] [Module R P] [Module.Projective R P]
    [Small.{max u v w} P] (α : M →ₗ[R] P) (β : P →ₗ[R] N) (h : φ = β ∘ₗ α) :
    FactorsThroughProj φ := by
  let e : Shrink.{max u v w} P ≃ₗ[R] P := Shrink.linearEquiv R P
  exact ⟨Shrink.{max u v w} P, inferInstance, inferInstance, inferInstance,
    (e.symm : P →ₗ[R] _) ∘ₗ α, β ∘ₗ (e : _ →ₗ[R] P), by rw [h]; ext m; simp⟩

/-- A composite `τ ∘ₗ σ` through a free module `J →₀ R` on an index type `J` in an arbitrary
universe factors through a free module on an index type in `Type (max u v w)`. -/
theorem FactorsThroughFree.of_comp_finsupp
    {R : Type u} [CommRing R] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {J : Type*} (σ : M →ₗ[R] (J →₀ R)) (τ : (J →₀ R) →ₗ[R] N) :
    FactorsThroughFree (τ ∘ₗ σ) := by
  classical
  let s : Set J := ⋃ m : M, ((σ m).support : Set J)
  have : Small.{max u v w} s := inferInstance
  let σ' : M →ₗ[R] Finsupp.supported R R s :=
    σ.codRestrict _ fun m => Set.subset_iUnion (fun m : M => ((σ m).support : Set J)) m
  let e : Finsupp.supported R R s ≃ₗ[R] (Shrink.{max u v w} s →₀ R) :=
    Finsupp.supportedEquivFinsupp s ≪≫ₗ Finsupp.domLCongr (equivShrink s)
  refine ⟨Shrink.{max u v w} s, e.toLinearMap ∘ₗ σ',
    τ ∘ₗ (Finsupp.supported R R s).subtype ∘ₗ e.symm.toLinearMap, ?_⟩
  ext m
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rfl

/-- The `R`-linear maps `M →ₗ[R] N` which factor through a projective `R`-module form an
`R`-submodule of `M →ₗ[R] N`. -/
@[stacks 0G90 "(2)"]
def FactorsThroughProj.submodule (R : Type u) [CommRing R] (M : Type v) (N : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    Submodule R (M →ₗ[R] N) where
  carrier := {φ | FactorsThroughProj φ}
  zero_mem' := FactorsThroughProj.mk' (0 : M →ₗ[R] R) (0 : R →ₗ[R] N) (by simp)
  add_mem' := by
    rintro φ χ ⟨P, _, _, _, α, β, hφ⟩ ⟨Q, _, _, _, γ, δ, hχ⟩
    exact ⟨P × Q, inferInstance, inferInstance, inferInstance,
      α.prod γ, β.coprod δ, by ext m; simp [hφ, hχ]⟩
  smul_mem' := by
    rintro r φ ⟨P, _, _, _, α, β, hφ⟩
    exact ⟨P, inferInstance, inferInstance, inferInstance, α, r • β, by ext m; simp [hφ]⟩

/-- A linear map lies in `FactorsThroughProj.submodule R M N` if and only if it factors through a
projective module. -/
@[simp]
theorem FactorsThroughProj.mem_submodule {R : Type u} [CommRing R] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) :
    φ ∈ FactorsThroughProj.submodule R M N ↔ FactorsThroughProj φ := Iff.rfl

/-- Factoring through a projective module is stable under precomposition and postcomposition by
arbitrary linear maps. -/
@[stacks 0G90 "(3)"]
theorem FactorsThroughProj.comp_comp {R : Type u} [CommRing R] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {φ : M →ₗ[R] N}
    (hφ : FactorsThroughProj φ) {M' : Type*} {N' : Type*} [AddCommGroup M'] [Module R M']
    [AddCommGroup N'] [Module R N'] (ψ : M' →ₗ[R] M) (ξ : N →ₗ[R] N') :
    FactorsThroughProj (ξ ∘ₗ φ ∘ₗ ψ) := by
  obtain ⟨J, σ, τ, hφ⟩ := (factorsThroughProj_iff_free φ).mp hφ
  refine (factorsThroughProj_iff_free _).mpr ?_
  simpa only [hφ, LinearMap.comp_assoc] using
    FactorsThroughFree.of_comp_finsupp (σ ∘ₗ ψ) (ξ ∘ₗ τ)

/-- An `R`-module `M` is *`I`-projective*, for an ideal `I` of `R`, if for every `a ∈ I` the
multiplication-by-`a` endomorphism `m ↦ a • m` of `M` factors through a projective
`R`-module. -/
@[stacks 0G93]
def Module.IsIProjective (R : Type u) [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] : Prop :=
  ∀ a ∈ I, FactorsThroughProj ((LinearMap.lsmul R M) a)

/-- `M` is `I`-projective if and only if for every `a ∈ I` the multiplication-by-`a`
endomorphism of `M` factors through a free `R`-module. -/
@[stacks 0G92 "(1)-(2)"]
theorem Module.isIProjective_iff_free (R : Type u) [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] :
    Module.IsIProjective R I M ↔ ∀ a ∈ I, FactorsThroughFree ((LinearMap.lsmul R M) a) :=
  forall₂_congr fun _ _ => factorsThroughProj_iff_free _

section Ext

open CategoryTheory CategoryTheory.Limits

/-- Over a ring `R` with `Small.{v} R`, a projective factorization of a map between modules in
`Type v` can be chosen with its middle module again in `Type v`. -/
theorem FactorsThroughProj.exists_small_factorization
    {R : Type u} [CommRing R] [Small.{v} R]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {f : M →ₗ[R] N} (hf : FactorsThroughProj f) :
    ∃ (P : Type v) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Projective R P)
      (g : M →ₗ[R] P) (h : P →ₗ[R] N), f = h ∘ₗ g := by
  classical
  obtain ⟨J, g, h, rfl⟩ := factorsThroughProj_iff_free f |>.mp hf
  let s : Set J := ⋃ m : M, (g m).support
  let g' : M →ₗ[R] (s →₀ R) := (Finsupp.lsubtypeDomain s).comp g
  let h' : (s →₀ R) →ₗ[R] N := h.comp (Finsupp.lmapDomain R R ((↑) : s → J))
  have hgh : h ∘ₗ g = h' ∘ₗ g' := by
    ext m
    apply congrArg h
    change g m = Finsupp.mapDomain Subtype.val
      (Finsupp.subtypeDomain (fun j ↦ j ∈ s) (g m))
    calc
      g m = (Finsupp.subtypeDomain (fun j ↦ j ∈ s) (g m)).extendDomain :=
        (Finsupp.extendDomain_subtypeDomain _ fun _ hj ↦ Set.mem_iUnion_of_mem m hj).symm
      _ = Finsupp.embDomain (.subtype _) (Finsupp.subtypeDomain (fun j ↦ j ∈ s) (g m)) :=
        Finsupp.extendDomain_eq_embDomain_subtype _
      _ = _ := Finsupp.embDomain_eq_mapDomain _ _
  let e : Shrink.{v} (s →₀ R) ≃ₗ[R] (s →₀ R) := Shrink.linearEquiv R _
  exact ⟨Shrink.{v} (s →₀ R), inferInstance, inferInstance, inferInstance,
    e.symm.toLinearMap ∘ₗ g', h' ∘ₗ e.toLinearMap, by rw [hgh]; ext; simp⟩

/-- `M` is `I`-projective if and only if `I` annihilates `Ext¹_R(M, N)` for every `R`-module `N`.
-/
@[stacks 0G92 "(1)-(3)"]
theorem Module.isIProjective_iff_ext_annihilated (R : Type u) [CommRing R] [Small.{v} R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    Module.IsIProjective R I M ↔
      ∀ (N : Type v) [AddCommGroup N] [Module R N],
        I ≤ Module.annihilator R
          (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R N) 1) := by
  constructor
  · intro h N _ _ a ha
    obtain ⟨P, _, _, _, α, β, hfac⟩ := (h a ha).exists_small_factorization
    rw [Module.mem_annihilator]
    intro e
    rw [← Abelian.Ext.mk₀_id_comp e, ← Abelian.Ext.smul_comp,
      ← Abelian.Ext.mk₀_smul]
    change (Abelian.Ext.mk₀ (ModuleCat.ofHom ((LinearMap.lsmul R M) a))).comp e _ = 0
    rw [hfac, ModuleCat.ofHom_comp, ← Abelian.Ext.mk₀_comp_mk₀]
    have hz : (Abelian.Ext.mk₀ (ModuleCat.ofHom β)).comp e (zero_add 1) = 0 :=
      Abelian.Ext.eq_zero_of_projective _
    rw [Abelian.Ext.comp_assoc_of_second_deg_zero, hz, Abelian.Ext.comp_zero]
  · intro h a ha
    let X : ModuleCat.{v} R := ModuleCat.of R M
    let S := ShortComplex.mk (kernel.ι (Projective.π X)) (Projective.π X)
      (kernel.condition (Projective.π X))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel S.g) }
    have hzero :
        (Abelian.Ext.mk₀ (ModuleCat.ofHom ((LinearMap.lsmul R M) a))).comp
            hS.extClass (zero_add 1) = 0 := by
      change (Abelian.Ext.mk₀ (a • 𝟙 X)).comp hS.extClass (zero_add 1) = 0
      rw [Abelian.Ext.mk₀_smul, Abelian.Ext.smul_comp]
      simpa using Module.mem_annihilator.mp (h S.X₁ ha) hS.extClass
    obtain ⟨x, hx⟩ := Abelian.Ext.covariant_sequence_exact₃
      (X := X) hS (Abelian.Ext.mk₀ (ModuleCat.ofHom ((LinearMap.lsmul R M) a)))
        (zero_add 1) hzero
    let α : X ⟶ S.X₂ := Abelian.Ext.addEquiv₀ x
    have hα : α ≫ S.g = ModuleCat.ofHom ((LinearMap.lsmul R M) a) := by
      apply (Abelian.Ext.mk₀_bijective _ _).1
      dsimp only [α]
      rw [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_addEquiv₀_apply, hx]
    exact FactorsThroughProj.mk' α.hom S.g.hom (by
      simpa using congrArg ModuleCat.Hom.hom hα.symm)

end Ext
@[expose] public section

/-- If `M` is annihilated by the ideal `I`, that is `a • m = 0` for all `a ∈ I` and `m : M`, then
`M` is `I`-projective. -/
@[stacks 0G94]
theorem Module.isIProjective_of_smul_eq_zero {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (h : ∀ a ∈ I, ∀ m : M, a • m = 0) :
    Module.IsIProjective R I M := by
  intro a ha
  refine FactorsThroughProj.mk' (P := PUnit.{1}) 0 0 ?_
  ext m
  simpa using h a ha m

/-- Given a short exact sequence `0 → K →[i] P →[p] M → 0` of `R`-modules with `M` `I`-projective
and `P` projective, the module `K` is `I`-projective. -/
@[stacks 0G95]
theorem Module.isIProjective_of_injective_of_exact {R : Type*} [CommRing R] (I : Ideal R)
    {K P M : Type u} [AddCommGroup K] [Module R K] [AddCommGroup P] [Module R P]
    [Module.Projective R P] [AddCommGroup M] [Module R M] (i : K →ₗ[R] P) (p : P →ₗ[R] M)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hexact : LinearMap.range i = LinearMap.ker p)
    (hM : Module.IsIProjective R I M) :
    Module.IsIProjective R I K := by
  intro a ha
  obtain ⟨Q, _, _, _, σ, τ, hστ⟩ := hM a ha
  obtain ⟨τtilde, hτtilde⟩ := Module.projective_lifting_property p τ hp
  set ψ : P →ₗ[R] P := τtilde ∘ₗ σ ∘ₗ p with hψ
  set θ : P →ₗ[R] P := a • LinearMap.id - ψ with hθ
  have hθrange : ∀ x : P, θ x ∈ LinearMap.range i := by
    intro x
    rw [hexact, LinearMap.mem_ker]
    have h₁ : p (τtilde (σ (p x))) = τ (σ (p x)) := by rw [← LinearMap.comp_apply, hτtilde]
    have h₂ : τ (σ (p x)) = a • p x := by simpa using (LinearMap.congr_fun hστ (p x)).symm
    simp [hθ, hψ, h₁, h₂]
  let θ' : P →ₗ[R] LinearMap.range i := LinearMap.codRestrict (LinearMap.range i) θ hθrange
  let e : K ≃ₗ[R] LinearMap.range i := LinearEquiv.ofInjective i hi
  let τ' : P →ₗ[R] K := (e.symm : LinearMap.range i →ₗ[R] K) ∘ₗ θ'
  refine FactorsThroughProj.mk' i τ' ?_
  ext k
  have hpi : p (i k) = 0 := by rw [← LinearMap.mem_ker, ← hexact]; exact ⟨k, rfl⟩
  have : θ' (i k) = e (a • k) := Subtype.ext <| by simp [θ', e, hθ, hψ, hpi]
  change a • k = e.symm (θ' (i k))
  rw [this, LinearEquiv.symm_apply_apply]

/-- A linear map into `J →₀ R` sends every element of a module spanned by `s` to a
finsupp supported in the union of the supports of the images of `s`. -/
theorem Finsupp.support_linearMap_subset_biUnion {R M J : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [DecidableEq J] (σ : M →ₗ[R] J →₀ R) {s : Finset M}
    (hs : Submodule.span R (s : Set M) = ⊤) (x : M) :
    ((σ x).support : Set J) ⊆ ↑(s.biUnion fun g => (σ g).support) := by
  have hx : x ∈ Submodule.span R (s : Set M) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem g hg =>
      intro j hj
      simp only [Finset.coe_biUnion, Finset.mem_coe, Set.mem_iUnion]
      exact ⟨g, hg, by simpa using hj⟩
  | zero => simp
  | add y z _ _ hy hz =>
      intro j hj
      rw [map_add] at hj
      rcases Finset.mem_union.mp (Finsupp.support_add hj) with h | h
      · exact hy h
      · exact hz h
  | smul r y _ hy =>
      intro j hj
      rw [map_smul] at hj
      exact hy (Finsupp.support_smul hj)

/-- Restricting a finsupp to a subtype containing its support and mapping back along
`Subtype.val` recovers the original finsupp. -/
theorem Finsupp.mapDomain_subtypeDomain_of_support_subset {J M : Type*} [AddCommMonoid M]
    {p : J → Prop} {f : J →₀ M} (hf : ∀ j ∈ f.support, p j) :
    Finsupp.mapDomain Subtype.val (Finsupp.subtypeDomain p f) = f := by
  ext j
  by_cases hj : p j
  · exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨j, hj⟩
  · rw [Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨⟨i, hi⟩, rfl⟩; exact hj hi),
      Finsupp.notMem_support_iff.mp fun h => hj (hf j h)]

/-- A linear map from a finitely generated module to a finsupp module factors through the
finsupp module on a finite subtype of the index type. -/
private theorem exists_finite_factorization_finsupp {R : Type*} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] [Module.Finite R M] {J : Type p} (σ : M →ₗ[R] (J →₀ R)) :
    ∃ (ι : Type p) (_ : Finite ι) (σ₀ : M →ₗ[R] (ι →₀ R)) (incl : (ι →₀ R) →ₗ[R] (J →₀ R)),
      incl ∘ₗ σ₀ = σ := by
  classical
  obtain ⟨s, hs⟩ := (Module.finite_def.mp ‹Module.Finite R M› : (⊤ : Submodule R M).FG)
  set K : Finset J := s.biUnion (fun g => (σ g).support)
  have hsupp := Finsupp.support_linearMap_subset_biUnion σ hs
  refine ⟨K, inferInstance, (Finsupp.lsubtypeDomain (R := R) {j | j ∈ K}) ∘ₗ σ,
    Finsupp.lmapDomain R R Subtype.val, LinearMap.ext fun x => ?_⟩
  exact Finsupp.mapDomain_subtypeDomain_of_support_subset fun _ hj => hsupp x hj

/-- A linear map out of a *finite* module which factors through a projective module already
factors through a *finite* projective module. -/
@[stacks 0G91]
theorem Module.exists_finite_projective_factorization
    {R : Type u} [CommRing R] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) (hφ : FactorsThroughProj φ) :
    ∃ (P : Type (max u v w)) (_ : AddCommGroup P) (_ : Module R P)
      (_ : Module.Finite R P) (_ : Module.Projective R P)
      (α : M →ₗ[R] P) (β : P →ₗ[R] N), φ = β ∘ₗ α := by
  obtain ⟨J, σ, τ, hτσ⟩ := (factorsThroughProj_iff_free φ).mp hφ
  obtain ⟨ι, _, α, incl, hincl⟩ := exists_finite_factorization_finsupp σ
  refine ⟨ι →₀ R, inferInstance, inferInstance,
    Module.Finite.equiv (Finsupp.linearEquivFunOnFinite R R ι).symm, inferInstance,
    α, τ ∘ₗ incl, ?_⟩
  rw [hτσ, ← hincl, LinearMap.comp_assoc]

/-- If `M` is a finite `I`-projective `R`-module, then its dual `M^∨ = Hom_R(M, R)` is
`I`-projective. -/
@[stacks 0G96]
theorem Module.IsIProjective.dual (R : Type u) [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Module.IsIProjective R I M) :
    Module.IsIProjective R I (Module.Dual R M) := by
  classical
  rw [Module.isIProjective_iff_free] at hM ⊢
  intro a ha
  obtain ⟨J, σ, τ, hτσ⟩ := hM a ha
  obtain ⟨ι, _, σ₀, incl, hincl⟩ := exists_finite_factorization_finsupp σ
  set τ₀ : (ι →₀ R) →ₗ[R] M := τ ∘ₗ incl
  have hfact : τ₀ ∘ₗ σ₀ = LinearMap.lsmul R M a := by
    simpa only [τ₀, LinearMap.comp_assoc, hincl] using hτσ.symm
  let e : Module.Dual R (ι →₀ R) ≃ₗ[R] (ι →₀ R) :=
    (Finsupp.basisSingleOne (R := R) (ι := ι)).dualBasis.repr
  let c : (ULift.{u} ι →₀ R) ≃ₗ[R] (ι →₀ R) := Finsupp.domLCongr (Equiv.ulift)
  refine ⟨ULift.{u} ι,
    (c.symm : (ι →₀ R) →ₗ[R] _) ∘ₗ (e : _ →ₗ[R] _) ∘ₗ τ₀.dualMap,
    σ₀.dualMap ∘ₗ (e.symm : (ι →₀ R) →ₗ[R] _) ∘ₗ (c : _ →ₗ[R] _), ?_⟩
  have hdual : σ₀.dualMap ∘ₗ τ₀.dualMap = LinearMap.lsmul R (Module.Dual R M) a := by
    rw [LinearMap.dualMap_comp_dualMap, hfact]
    ext φ x
    simp [LinearMap.lsmul_apply, LinearMap.dualMap_apply]
  refine (LinearMap.ext fun φ => ?_).symm
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [c.apply_symm_apply, e.symm_apply_apply]
  simpa only [LinearMap.coe_comp, Function.comp_apply] using LinearMap.congr_fun hdual φ
