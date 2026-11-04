module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import StacksFrontier.Algebra.Module.Essential

/-!
# Projective covers

A *projective cover* of an object `M` is an essential epimorphism `f : P ⟶ M` whose source `P`
is projective: `P` surjects onto `M`, and no proper subobject of `P` already does. Projective
covers need not exist, but when they do they are unique up to an isomorphism over `M`, so a
projective cover is a canonical "smallest" projective surjecting onto `M`.

The basic existence result is Nakayama's: a finite module `M` over a local ring `R` with maximal
ideal `𝔪` and residue field `k` has a projective cover, namely a free module on a `k`-basis of
`M/𝔪M`. Minimality of that lift is exactly the statement that a submodule of `R^n` surjecting
onto `M` must be everything, which is Nakayama's lemma.

## Main definitions

* `Module.IsProjectiveCover` — `f : P ⟶ M` is an essential epimorphism with `P` projective.

## Main results

* `Module.isProjectiveCover_unique` — two projective covers of an object are isomorphic over it.
* `Module.exists_projectiveCover_of_finite` — a finite module over a local ring has a projective
  cover.

## Implementation notes

The definition is stated in any category with images, so that it specialises to modules over a
ring through `ModuleCat`. In the existence statement both modules are placed in a universe large
enough to contain the ring and the given module, `Shrink` providing an isomorphic copy of the
latter there; the projective source is asserted to exist rather than constructed.

## References

* [Stacks Project, Tag 08XY](https://stacks.math.columbia.edu/tag/08XY)
* [Stacks Project, Tag 08XZ](https://stacks.math.columbia.edu/tag/08XZ)
* [Stacks Project, Tag 08Y0](https://stacks.math.columbia.edu/tag/08Y0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Module

section Defs

variable {C : Type u} [Category.{v} C] [HasImages C]

/-- A morphism is a projective cover if its source is projective and it is an essential
epimorphism. -/
@[stacks 08XY]
abbrev IsProjectiveCover {P M : C} (f : P ⟶ M) : Prop :=
  CategoryTheory.Projective P ∧ IsEssentialEpi f

end Defs

/-- Two projective covers of the same object are isomorphic over that object. -/
@[stacks 08XZ]
lemma isProjectiveCover_unique {C : Type u} [Category.{v} C] [Abelian C] {P P' M : C}
    (f : P ⟶ M) (g : P' ⟶ M) (hf : IsProjectiveCover f) (hg : IsProjectiveCover g) :
    ∃ e : P ≅ P', e.hom ≫ g = f := by
  have : CategoryTheory.Projective P := hf.1
  have : CategoryTheory.Projective P' := hg.1
  have : Epi g := hg.2.1
  let α := Projective.factorThru f g
  have hα : α ≫ g = f := Projective.factorThru_comp f g
  have : Epi α :=
    haveI : Epi (α ≫ g) := hα ▸ hf.2.1
    epi_of_comp_isEssentialEpi α g hg.2
  let β := Projective.factorThru (𝟙 P') α
  have hβα : β ≫ α = 𝟙 P' := Projective.factorThru_comp (𝟙 P') α
  have hβf : β ≫ f = g := by rw [← hα, ← Category.assoc, hβα, Category.id_comp]
  have : Epi β :=
    haveI : Epi (β ≫ f) := hβf ▸ inferInstance
    epi_of_comp_isEssentialEpi β f hf.2
  have : IsIso α := IsIso.of_epi_section' ⟨β, hβα⟩
  exact ⟨asIso α, hα⟩

/-- A surjective linear map such that no proper submodule of its source surjects onto its target
is an essential epimorphism in `ModuleCat`. -/
private lemma isEssentialEpi_ofHom {R : Type u} [Ring R] {P M : Type v} [AddCommGroup P]
    [Module R P] [AddCommGroup M] [Module R M] {f : P →ₗ[R] M} (hf : f.range = ⊤)
    (hmin : ∀ N : Submodule R P, N.map f = ⊤ → N = ⊤) :
    IsEssentialEpi (ModuleCat.ofHom f) := by
  refine ⟨(ModuleCat.epi_iff_range_eq_top _).2 hf, fun X hX => ?_⟩
  refine Subobject.ind
    (fun Y => Y ≠ ⊤ → (Subobject.«exists» (ModuleCat.ofHom f)).obj Y ≠ ⊤) ?_ X hX
  intro A g hg hX htop
  let Y := Subobject.mk g
  let N : Submodule R P := Y.arrow.hom.range
  have hNproper : N ≠ ⊤ := by
    intro hN
    have : Epi Y.arrow := (ModuleCat.epi_iff_range_eq_top Y.arrow).2 (by simpa [N] using hN)
    exact hX ((Subobject.isIso_arrow_iff_eq_top Y).mp (isIso_of_mono_of_epi Y.arrow))
  refine hNproper (hmin N (top_unique fun y _ => ?_))
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective _).mp
    ((epi_arrow_comp_iff_exists_obj_eq_top (ModuleCat.ofHom f) Y).2 htop) y
  refine Submodule.mem_map.mpr ⟨Y.arrow.hom a, LinearMap.mem_range.mpr ⟨a, rfl⟩, ?_⟩
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply] using ha

/-- Nakayama's lemma for a map out of a finite module over a local ring: if `f p ∈ 𝔪 • ⊤` forces
`p ∈ 𝔪 • ⊤`, then every submodule of the source that `f` maps onto the target is everything. -/
private lemma eq_top_of_map_eq_top_of_mem_smul_top {R : Type u} [CommRing R] [IsLocalRing R]
    {P M : Type v} [AddCommGroup P] [Module R P] [Module.Finite R P] [AddCommGroup M]
    [Module R M] {f : P →ₗ[R] M}
    (hf : ∀ p, f p ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) →
      p ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R P))
    {N : Submodule R P} (hN : N.map f = ⊤) : N = ⊤ := by
  refine (IsLocalRing.map_mkQ_eq_top (N := N)).mp (top_unique fun z _ => ?_)
  obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ z
  have hfp : f p ∈ N.map f := by simp [hN]
  obtain ⟨n, hn, hfn⟩ := Submodule.mem_map.mp hfp
  refine Submodule.mem_map.mpr ⟨n, hn, (Submodule.Quotient.eq _).2 ?_⟩
  have hpn : f (p - n) ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := by
    rw [map_sub, hfn, sub_self]
    exact zero_mem _
  simpa using Submodule.neg_mem _ (hf _ hpn)

/-- A finite module over a local ring has a projective cover. -/
@[stacks 08Y0]
lemma exists_projectiveCover_of_finite
    (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (P : ModuleCat.{max u v} R)
      (f : P ⟶ ModuleCat.of R (Shrink.{max u v} M)),
      IsProjectiveCover f := by
  classical
  let M' := Shrink.{max u v} M
  have : IsScalarTower R R M' := ⟨fun r s x => by simp [smul_smul]⟩
  let I := IsLocalRing.maximalIdeal R
  let k := IsLocalRing.ResidueField R
  let Q := M' ⧸ (I • (⊤ : Submodule R M'))
  let _ : Module k Q := by
    show Module (R ⧸ I) Q
    exact Module.instQuotientIdealSubmoduleHSMulTop M' I
  have : IsScalarTower R k Q := inferInstanceAs (IsScalarTower R (R ⧸ I) Q)
  let σ : R →+* k := IsLocalRing.residue R
  let qsl : M' →ₛₗ[σ] Q :=
    { toFun := Submodule.Quotient.mk
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hq : Function.Surjective qsl := Submodule.mkQ_surjective _
  have : Module.Finite k Q := Module.Finite.of_surjective qsl hq
  let b := Module.Free.chooseBasis k Q
  let ι := Module.Free.ChooseBasisIndex k Q
  choose x hx using fun i : ι => hq (b i)
  let f : (ι → R) →ₗ[R] M' := Fintype.linearCombination R x
  have hrepr (p : ι → R) (i : ι) : b.repr (qsl (f p)) i = σ (p i) := by
    have hred : qsl (f p) = ∑ i, σ (p i) • b i := by
      rw [Fintype.linearCombination_apply, map_sum]
      exact Finset.sum_congr rfl fun i _ => (qsl.map_smulₛₗ (p i) (x i)).trans (by rw [hx])
    simp [hred, Finsupp.single_apply, Finset.sum_ite_eq']
  have hf_range : f.range = ⊤ := by
    refine (IsLocalRing.map_mkQ_eq_top (N := f.range)).mp (top_unique fun y _ => ?_)
    choose p hp using fun i => Ideal.Quotient.mk_surjective (I := I) (b.repr y i)
    refine Submodule.mem_map.mpr ⟨f p, LinearMap.mem_range.mpr ⟨p, rfl⟩, ?_⟩
    exact b.repr.injective (Finsupp.ext fun i => (hrepr p i).trans (hp i))
  have hkernel (p : ι → R) (hp : f p ∈ I • (⊤ : Submodule R M')) :
      p ∈ I • (⊤ : Submodule R (ι → R)) := by
    have hp' : qsl (f p) = 0 := (Submodule.Quotient.mk_eq_zero _).2 hp
    have hm (i : ι) : p i ∈ I :=
      (IsLocalRing.residue_eq_zero_iff _).mp ((hrepr p i).symm.trans (by simp [hp']))
    rw [pi_eq_sum_univ p]
    exact sum_mem fun i _ => Submodule.smul_mem_smul (hm i) Submodule.mem_top
  exact ⟨ModuleCat.of R (ι → R), ModuleCat.ofHom f, ModuleCat.projective_of_free (Pi.basisFun R ι),
    isEssentialEpi_ofHom hf_range fun _ => eq_top_of_map_eq_top_of_mem_smul_top hkernel⟩

end Module

end
