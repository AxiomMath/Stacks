module

public import StacksFrontier.RingTheory.Flat.LocalCriterionEssFP
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Injectivity and flatness of the cokernel from injectivity modulo the maximal ideal

Let `R → S` be a local homomorphism of local rings with `S` essentially of finite presentation
over `R`, let `𝔪` be the maximal ideal of `R` and let `u : M → N` be a map of `S`-modules with `M`
finite over `S` and `N` of finite presentation over `S` and flat over `R`. If
`ū : M/𝔪M → N/𝔪N` is injective, then `N/u(M)` is flat over `R`, and if moreover `Ker u` is a
finite `S`-module, then `u` is injective.

## Main results

* `Module.Flat.flat_quotient_range_of_injective_mapQ_maximalIdeal`: if `ū` is injective, then
  `N/u(M)` is flat over `R`.
* `Module.Flat.injective_of_fg_ker_of_injective_mapQ_maximalIdeal`: if `ū` is injective, `N/u(M)`
  is flat over `R` and `Ker u` is a finite `S`-module, then `u` is injective.
* `Module.Flat.injective_and_flat_quotient_range_of_fg_ker_of_injective_mapQ_maximalIdeal`: for
  `M` and `N` of finite presentation over `S`, if `ū` is injective and `Ker u` is a finite
  `S`-module, then `u` is injective and `N/u(M)` is flat over `R`.
* `CategoryTheory.isLocalHom_map_of_isLocalHom_app`: if the components of a cone from a diagram
  of commutative rings to a ring are local homomorphisms, then so are the transition maps.

## Implementation notes

The fibre `M/𝔪M` is the quotient `M ⧸ 𝔪 • (⊤ : Submodule R M)`, and `ū` is the map
`Submodule.mapQ` of `u.restrictScalars R` between two such quotients, the required inclusion being
`Submodule.smul_top_le_comap_smul_top`. The submodules `𝔪 • (⊤ : Submodule R M)` and
`(𝔪S) • (⊤ : Submodule S M)` have the same elements, so nothing is lost by taking the quotient
over `R` rather than over `S`.

## References

* [Stacks Project, Tag 046Y](https://stacks.math.columbia.edu/tag/046Y)
-/

@[expose] public section

open CategoryTheory IsLocalRing TensorProduct
universe u u₁ u₂ u₃ u₄

namespace Module.Flat

section SMulOfTensor

variable {R : Type*} [CommRing R] (I : Ideal R) {X Y : Type*} [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y]

/-- The action map `I ⊗_R X → X`, `i ⊗ x ↦ i • x`, as the composite of
`LinearMap.rTensor X I.subtype` with `TensorProduct.lid`. -/
private noncomputable def smulOfTensor : I ⊗[R] X →ₗ[R] X :=
  (TensorProduct.lid R X).toLinearMap ∘ₗ LinearMap.rTensor X I.subtype

private lemma smulOfTensor_tmul (i : I) (x : X) : smulOfTensor I (i ⊗ₜ x) = (i : R) • x :=
  rfl

/-- The image of the action map `I ⊗_R X → X` is `I • X`. -/
private lemma range_smulOfTensor : LinearMap.range (smulOfTensor I (X := X)) = I • ⊤ := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul i x => exact smulOfTensor_tmul I i x ▸ Submodule.smul_mem_smul i.2 Submodule.mem_top
    | add a b ha hb => simpa using Submodule.add_mem _ ha hb
  · rw [Submodule.smul_le]
    intro r hr x _
    exact ⟨(⟨r, hr⟩ : I) ⊗ₜ x, rfl⟩

/-- Over a flat module the action map `I ⊗_R X → X` is injective. -/
private lemma injective_smulOfTensor [Module.Flat R X] :
    Function.Injective (smulOfTensor I (X := X)) := by
  rw [smulOfTensor, LinearMap.coe_comp]
  exact
    (TensorProduct.lid R X).injective.comp
      (Module.Flat.iff_rTensor_injective'.mp ‹Module.Flat R X› I)

/-- The action map is natural in the module. -/
private lemma smulOfTensor_lTensor (f : X →ₗ[R] Y) (y : I ⊗[R] X) :
    smulOfTensor I (LinearMap.lTensor (↥I) f y) = f (smulOfTensor I y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i x => simp [smulOfTensor_tmul]
  | add a b ha hb => simp [ha, hb]

/-- The action map lands in `I • X`. -/
private lemma smulOfTensor_mem_smul_top (y : I ⊗[R] X) :
    smulOfTensor I y ∈ I • (⊤ : Submodule R X) := by
  rw [← range_smulOfTensor]
  exact LinearMap.mem_range_self _ _

end SMulOfTensor

/-- Every module over the quotient of a ring by a maximal ideal is flat. -/
private lemma flat_of_isMaximal_quotient {R : Type*} [CommRing R] (I : Ideal R) (hI : I.IsMaximal)
    (X : Type*) [AddCommGroup X] [Module (R ⧸ I) X] : Module.Flat (R ⧸ I) X :=
  have := hI
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  Module.Flat.of_free

section Flatness

variable {R : Type u₁} {S : Type u₂} {M : Type u₃} {N : Type u₄} [CommRing R] [CommRing S]
  [Algebra R S] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [AddCommGroup N]
  [Module R N] [Module S N] [IsScalarTower R S N]

/-- Injectivity of `ū : M/IM → N/IN` says that `u` pulls `IN` back into `IM`. -/
private lemma mem_smul_top_of_map_mem (I : Ideal R) (u : M →ₗ[S] N)
    (hu :
      Function.Injective
        (Submodule.mapQ (I • (⊤ : Submodule R M)) (I • (⊤ : Submodule R N)) (u.restrictScalars R)
          (Submodule.smul_top_le_comap_smul_top I (u.restrictScalars R)))) {m : M}
    (hm : u m ∈ I • (⊤ : Submodule R N)) : m ∈ I • (⊤ : Submodule R M) := by
  rw [← Submodule.Quotient.mk_eq_zero]
  exact hu (by simpa using hm)

/-- Injectivity of `ū : M/IM → N/IN` says that `u` pulls `IN` back into `IM`, hence that
`u(M) ∩ IN = I u(M)`. -/
private lemma inf_range_le_smul_range (I : Ideal R) (u : M →ₗ[S] N)
    (hu :
      Function.Injective
        (Submodule.mapQ (I • (⊤ : Submodule R M)) (I • (⊤ : Submodule R N)) (u.restrictScalars R)
          (Submodule.smul_top_le_comap_smul_top I (u.restrictScalars R)))) :
    (I • (⊤ : Submodule R N)) ⊓ LinearMap.range (u.restrictScalars R) ≤
      I • LinearMap.range (u.restrictScalars R) := by
  rintro x ⟨hx, m, rfl⟩
  rw [LinearMap.range_eq_map, ← Submodule.map_smul'']
  exact Submodule.mem_map_of_mem (mem_smul_top_of_map_mem I u hu hx)

/-- If `N` is flat over `R` and `ū : M/IM → N/IN` is injective, then the action map
`I ⊗_R (N/u(M)) → N/u(M)` is injective. -/
private lemma injective_smulOfTensor_quotient_range [Module.Flat R N] (I : Ideal R) (u : M →ₗ[S] N)
    (hu :
      Function.Injective
        (Submodule.mapQ (I • (⊤ : Submodule R M)) (I • (⊤ : Submodule R N)) (u.restrictScalars R)
          (Submodule.smul_top_le_comap_smul_top I (u.restrictScalars R)))) :
    Function.Injective (smulOfTensor I (X := N ⧸ LinearMap.range u)) := by
  set v := u.restrictScalars R with hv
  set g := ((LinearMap.range u).mkQ).restrictScalars R with hg
  have hgv : g ∘ₗ v = 0 := by
    ext m; simp [hg, hv]
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hgs : Function.Surjective g := by
    rw [hg, LinearMap.coe_restrictScalars]
    exact Submodule.mkQ_surjective _
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective (↥I) hgs x
  have h1 : g (smulOfTensor I y) = 0 := by
    rw [← smulOfTensor_lTensor]
    exact hx
  have h2 : smulOfTensor I y ∈ (I • (⊤ : Submodule R N)) ⊓ LinearMap.range v := by
    refine ⟨?_, ?_⟩
    · exact smulOfTensor_mem_smul_top I y
    · obtain ⟨m, hm⟩ : smulOfTensor I y ∈ LinearMap.range u :=
        (Submodule.Quotient.mk_eq_zero _).mp h1
      exact ⟨m, hm⟩
  have h3 := inf_range_le_smul_range I u hu h2
  rw [LinearMap.range_eq_map, ← Submodule.map_smul'', ← range_smulOfTensor] at h3
  obtain ⟨m, hm, hmv⟩ := h3
  obtain ⟨z, hz⟩ := hm
  have hy : LinearMap.lTensor (↥I) v z = y := by
    apply injective_smulOfTensor I (X := N)
    rw [smulOfTensor_lTensor, hz, hmv]
  rw [← hy, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hgv]
  simp

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Module.Finite S M]
  [Module.FinitePresentation S N]

/-- Let `R → S` be a local homomorphism of local rings with `S` essentially of finite presentation
over `R`, let `𝔪` be the maximal ideal of `R`, and let `u : M → N` be a map of `S`-modules with `M`
finite over `S`, `N` of finite presentation over `S` and `N` flat over `R`. If
`ū : M/𝔪M → N/𝔪N` is injective, then `N/u(M)` is flat over `R`. -/
public theorem flat_quotient_range_of_injective_mapQ_maximalIdeal [Module.Flat R N]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation) (u : M →ₗ[S] N)
    (hu :
      Function.Injective
        (Submodule.mapQ (maximalIdeal R • (⊤ : Submodule R M))
          (maximalIdeal R • (⊤ : Submodule R N)) (u.restrictScalars R)
          (Submodule.smul_top_le_comap_smul_top (maximalIdeal R) (u.restrictScalars R)))) :
    Module.Flat R (N ⧸ LinearMap.range u) := by
  have hQ : Module.FinitePresentation S (N ⧸ LinearMap.range u) := by
    refine
      Module.finitePresentation_of_surjective (LinearMap.range u).mkQ (Submodule.mkQ_surjective _)
        ?_
    rw [Submodule.ker_mkQ, ← Submodule.map_top]
    exact (Module.Finite.fg_top (R := S) (M := M)).map u
  refine
    Module.Flat.of_rTensor_subtype_injective_of_flat_quotient_of_essentiallyOfFinitePresentation S
      _ hS (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top ?_ ?_
  · have h := injective_smulOfTensor_quotient_range (maximalIdeal R) u hu
    rw [smulOfTensor, LinearMap.coe_comp] at h
    exact h.of_comp
  · exact flat_of_isMaximal_quotient (maximalIdeal R) (maximalIdeal.isMaximal R) _

end Flatness

section Injectivity

variable {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- If `M → N → P → 0` is exact with `N` and `P` flat over `R`, and if the kernel of `v : M → N`
is contained in `I • M`, then it is contained in `I • Ker v`. -/
private lemma ker_le_smul_ker (I : Ideal R) {v : M →ₗ[R] N} {f : N →ₗ[R] P} [Module.Flat R N]
    [Module.Flat R P] (hf : Function.Surjective f) (hvf : Function.Exact v f)
    (hIM : LinearMap.ker v ≤ I • (⊤ : Submodule R M)) : LinearMap.ker v ≤ I • LinearMap.ker v := by
  have hex : Function.Exact ((LinearMap.range v).subtype) f := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
    exact LinearMap.exact_iff.mp hvf
  have hι : Function.Injective (LinearMap.lTensor (↥I) (LinearMap.range v).subtype) :=
    LinearMap.lTensor_injective_of_exact_of_flat f hf _ (Submodule.injective_subtype _) hex (↥I)
  intro x hx
  obtain ⟨ξ, hξ⟩ : x ∈ LinearMap.range (smulOfTensor I (X := M)) := by
    rw [range_smulOfTensor]; exact hIM hx
  have hvξ : LinearMap.lTensor (↥I) v ξ = 0 := by
    apply injective_smulOfTensor I (X := N)
    rw [map_zero, smulOfTensor_lTensor, hξ]
    exact LinearMap.mem_ker.mp hx
  have hpξ : LinearMap.lTensor (↥I) v.rangeRestrict ξ = 0 := by
    apply hι
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      LinearMap.subtype_comp_rangeRestrict]
    exact hvξ
  have hkerex : Function.Exact ((LinearMap.ker v).subtype) v.rangeRestrict := by
    rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict]
  obtain ⟨η, hη⟩ := (_root_.lTensor_exact (↥I) hkerex v.surjective_rangeRestrict ξ).mp hpξ
  have hmap :
    x ∈ Submodule.map (LinearMap.ker v).subtype (I • (⊤ : Submodule R ↥(LinearMap.ker v))) := by
    refine ⟨smulOfTensor I η, ?_, ?_⟩
    · exact smulOfTensor_mem_smul_top I η
    · have h : smulOfTensor I ξ = (LinearMap.ker v).subtype (smulOfTensor I η) := by
        rw [← hη, smulOfTensor_lTensor]
      rw [← hξ, h]
  rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at hmap

end Injectivity

section Nakayama

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
  [Module S M] [IsScalarTower R S M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N]

/-- The sequence `M → N → N/u(M) → 0` is exact over `R`. -/
private lemma exact_restrictScalars_mkQ (u : M →ₗ[S] N) :
    Function.Exact (u.restrictScalars R) ((LinearMap.range u).mkQ.restrictScalars R) := by
  rw [LinearMap.exact_iff, LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
  ext x
  simp

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- Locality of `R → S` turns `𝔪_R`-multiples into `𝔪_S`-multiples. -/
private lemma smul_le_restrictScalars_maximalIdeal_smul (K : Submodule S M) :
    maximalIdeal R • (K.restrictScalars R) ≤ Submodule.restrictScalars R (maximalIdeal S • K) := by
  rw [Submodule.smul_le]
  intro r hr y hy
  rw [Submodule.restrictScalars_mem, ← algebraMap_smul S r y]
  refine Submodule.smul_mem_smul ?_ ((Submodule.restrictScalars_mem R K y).mp hy)
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact fun h => (IsLocalRing.mem_maximalIdeal r).mp hr (isUnit_of_map_unit _ r h)

/-- Let `R → S` be a local homomorphism of local rings, let `𝔪` be the maximal ideal of `R`, and
let `u : M → N` be a map of `S`-modules with `N` and `N/u(M)` flat over `R`. If
`ū : M/𝔪M → N/𝔪N` is injective and `Ker u` is a finite `S`-module, then `u` is injective. -/
public theorem injective_of_fg_ker_of_injective_mapQ_maximalIdeal [Module.Flat R N] (u : M →ₗ[S] N)
    (hQ : Module.Flat R (N ⧸ LinearMap.range u))
    (hu :
      Function.Injective
        (Submodule.mapQ (maximalIdeal R • (⊤ : Submodule R M))
          (maximalIdeal R • (⊤ : Submodule R N)) (u.restrictScalars R)
          (Submodule.smul_top_le_comap_smul_top (maximalIdeal R) (u.restrictScalars R))))
    (hfg : (LinearMap.ker u).FG) : Function.Injective u := by
  have := hQ
  have hstep :
    LinearMap.ker (u.restrictScalars R) ≤ maximalIdeal R • LinearMap.ker (u.restrictScalars R) :=
    ker_le_smul_ker (maximalIdeal R) (v := u.restrictScalars R) (f :=
      (LinearMap.range u).mkQ.restrictScalars R) (LinearMap.range u).mkQ_surjective
      (exact_restrictScalars_mkQ u) fun x hx =>
      mem_smul_top_of_map_mem _ u hu ((LinearMap.mem_ker.mp hx).symm ▸ zero_mem _)
  have hK : LinearMap.ker u ≤ maximalIdeal S • LinearMap.ker u := by
    intro x hx
    have h1 := hstep (LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp hx))
    rw [LinearMap.ker_restrictScalars] at h1
    exact
      (Submodule.restrictScalars_mem R _ x).mp
        (smul_le_restrictScalars_maximalIdeal_smul (LinearMap.ker u) h1)
  rw [← LinearMap.ker_eq_bot]
  exact
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal S) (LinearMap.ker u) hfg hK
      (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal S) bot_ne_top).symm)

end Nakayama

/-- Let `R → S` be a local homomorphism of local rings with `S` essentially of finite presentation
over `R`, let `𝔪` be the maximal ideal of `R`, and let `u : M → N` be a map of `S`-modules with
`M`, `N` of finite presentation over `S` and `N` flat over `R`. If the induced map
`ū : M/𝔪M → N/𝔪N` is injective and `Ker u` is finitely generated, then `u` is injective and
`N/u(M)` is flat over `R`. -/
@[ega "IV 11.3.7" "(b) ⇒ (a), special case"]
public theorem injective_and_flat_quotient_range_of_fg_ker_of_injective_mapQ_maximalIdeal
    {R S M N : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.FinitePresentation S M] [Module.FinitePresentation S N] [Module.Flat R N]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation) (u : M →ₗ[S] N)
    (hu :
      Function.Injective
        (Submodule.mapQ (maximalIdeal R • (⊤ : Submodule R M))
          (maximalIdeal R • (⊤ : Submodule R N)) (u.restrictScalars R)
          (Submodule.smul_top_le_comap_smul_top (maximalIdeal R) (u.restrictScalars R))))
    (hfg : (LinearMap.ker u).FG) : Function.Injective u ∧ Module.Flat R (N ⧸ LinearMap.range u) :=
  have hQ := flat_quotient_range_of_injective_mapQ_maximalIdeal hS u hu
  ⟨injective_of_fg_ker_of_injective_mapQ_maximalIdeal u hQ hu hfg, hQ⟩

end Module.Flat

/-- If every component `A i → R` of a cone `ρ` from a diagram `A` of commutative rings is a local
homomorphism, then so is every transition map `A i → A j`. -/
public lemma CategoryTheory.isLocalHom_map_of_isLocalHom_app {Λ : Type u} [Preorder Λ]
    {A : Λ ⥤ CommRingCat.{u}} {R : Type u} [CommRing R]
    (ρ : A ⟶ (Functor.const Λ).obj (CommRingCat.of R)) (hρ : ∀ i, IsLocalHom (ρ.app i).hom)
    ⦃i j : Λ⦄ (h : i ⟶ j) : IsLocalHom (A.map h).hom := by
  have hnat : A.map h ≫ ρ.app j = ρ.app i := by simp
  refine ⟨fun a ha => ?_⟩
  have h2 : (ρ.app j).hom ((A.map h).hom a) = (ρ.app i).hom a := by
    rw [← hnat]; rfl
  exact (hρ i).map_nonunit a (h2 ▸ ha.map (ρ.app j).hom)
