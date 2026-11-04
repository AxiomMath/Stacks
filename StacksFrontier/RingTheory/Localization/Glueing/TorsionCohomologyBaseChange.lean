module

public import StacksFrontier.RingTheory.Localization.Glueing.IdealPowerTorsion

/-!
# Base change of a complex with `I`-power torsion cohomology

Let `R → S` be a flat ring map inducing an isomorphism `R / I ≅ S / IS`, and let
`A --d--> B --e--> C` be a complex of `R`-modules (`e ∘ d = 0`) whose cohomology
`ker e / range d` is `I`-power torsion. Then base change along `R → S` does not change that
cohomology: the unit `B → B ⊗[R] S` induces an isomorphism from `ker e / range d` onto the
cohomology of `A ⊗ S → B ⊗ S → C ⊗ S`.

This file records the two halves of that statement elementwise, in the form used for
Mayer–Vietoris chases: a cocycle of `B` whose base change is a coboundary is already a
coboundary, and every cocycle of `B ⊗ S` is the base change of a cocycle of `B` up to a
coboundary.

## Main results

* `FormalGlueing.mem_range_of_tmul_one_mem_range_rTensor`: injectivity on cohomology.
* `FormalGlueing.exists_eq_tmul_one_add_of_rTensor_eq_zero`: surjectivity on cohomology.

## Implementation notes

Both statements reduce, through flatness of `S` and right exactness of the tensor product, to
the bijectivity of the unit `H → H ⊗[R] S` on the `I`-power torsion module `H = ker e / range d`,
which is `IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective`.

## References

* [Stacks Project, Tag 05E9](https://stacks.math.columbia.edu/tag/05E9)
-/

@[expose] public section

open TensorProduct

universe u

namespace FormalGlueing

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)
  {A B C : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] {d : A →ₗ[R] B} {e : B →ₗ[R] C}

/-- The cohomology `ker e / range d` of a complex `A → B → C`. -/
abbrev cohomologyModule (d : A →ₗ[R] B) (e : B →ₗ[R] C) : Type u :=
  LinearMap.ker e ⧸ (LinearMap.range d).comap (LinearMap.ker e).subtype

include I in
/-- The unit of base change is bijective on the cohomology of a complex whose cohomology is
`I`-power torsion. -/
theorem bijective_cohomologyModule_tensorUnit (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (htors : IsIPowerTorsion R (cohomologyModule d e) I) :
    Function.Bijective ((TensorProduct.mk R (cohomologyModule d e) S).flip 1) :=
  (IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective.{u, u, u} R S I hflat).mpr hq _
    htors

/-- The quotient map from the cocycles onto the cohomology. -/
abbrev cohomologyπ (d : A →ₗ[R] B) (e : B →ₗ[R] C) :
    LinearMap.ker e →ₗ[R] cohomologyModule d e :=
  Submodule.mkQ _

/-- The coboundaries, as a submodule of the cocycles, are the image of `A`. -/
theorem exact_codRestrict_cohomologyπ (hde : e ∘ₗ d = 0) :
    Function.Exact (LinearMap.codRestrict (LinearMap.ker e) d fun a ↦ by
        change (e ∘ₗ d) a = 0
        rw [hde, LinearMap.zero_apply]) (cohomologyπ d e) := by
  intro z
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    LinearMap.mem_range, Set.mem_range]
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, Subtype.ext ha⟩, fun ⟨a, ha⟩ ↦ ⟨a, congrArg Subtype.val ha⟩⟩

/-- The quotient map from the cocycles onto the cohomology is surjective. -/
theorem surjective_cohomologyπ : Function.Surjective (cohomologyπ d e) :=
  Submodule.mkQ_surjective _

/-- The corestriction of `d` to the cocycles of a complex. -/
private def coboundaryLift (hde : e ∘ₗ d = 0) : A →ₗ[R] LinearMap.ker e :=
  LinearMap.codRestrict (LinearMap.ker e) d fun a ↦ by
    change (e ∘ₗ d) a = 0
    rw [hde, LinearMap.zero_apply]

/-- After base change along a flat `S`, the corestriction of `d` to the cocycles is still exact
with the quotient map onto the cohomology. -/
private theorem exact_rTensor_coboundaryLift [Module.Flat R S] (hde : e ∘ₗ d = 0) :
    Function.Exact ((coboundaryLift hde).rTensor S) ((cohomologyπ d e).rTensor S) :=
  Module.Flat.rTensor_exact S (exact_codRestrict_cohomologyπ hde)

include I in
/-- **Injectivity on cohomology.** Let `R → S` be flat and an isomorphism modulo `I`, and let
`A → B → C` be a complex whose cohomology is `I`-power torsion. A cocycle `b` of `B` whose base
change `b ⊗ 1` is a coboundary of the base-changed complex is a coboundary. -/
theorem mem_range_of_tmul_one_mem_range_rTensor (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (hde : e ∘ₗ d = 0) (htors : IsIPowerTorsion R (cohomologyModule d e) I)
    {b : B} (hb : e b = 0) (hbS : b ⊗ₜ[R] (1 : S) ∈ LinearMap.range (d.rTensor S)) :
    b ∈ LinearMap.range d := by
  set Z := LinearMap.ker e
  have hexS := exact_rTensor_coboundaryLift (S := S) hde
  have hinj : Function.Injective (Z.subtype.rTensor S) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  obtain ⟨w, hw⟩ := hbS
  -- `⟨b⟩ ⊗ 1` is the image of `w` in `Z ⊗ S`
  have hz : (⟨b, hb⟩ : Z) ⊗ₜ[R] (1 : S) = (coboundaryLift hde).rTensor S w :=
    hinj <| by rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]; exact hw.symm
  have h0 : (cohomologyπ d e).rTensor S ((⟨b, hb⟩ : Z) ⊗ₜ[R] (1 : S)) = 0 := by
    rw [hz]
    exact hexS.apply_apply_eq_zero w
  rw [LinearMap.rTensor_tmul] at h0
  have h1 : cohomologyπ d e ⟨b, hb⟩ = 0 :=
    (bijective_cohomologyModule_tensorUnit I hflat hq htors).1 (by rwa [map_zero])
  obtain ⟨a, ha⟩ := (exact_codRestrict_cohomologyπ hde _).mp h1
  exact ⟨a, congrArg Subtype.val ha⟩

include I in
/-- **Surjectivity on cohomology.** Let `R → S` be flat and an isomorphism modulo `I`, and let
`A → B → C` be a complex whose cohomology is `I`-power torsion. Every cocycle `y` of the
base-changed complex is the base change `b ⊗ 1` of a cocycle `b` of `B` up to a coboundary of
the base-changed complex. -/
theorem exists_eq_tmul_one_add_of_rTensor_eq_zero (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (hde : e ∘ₗ d = 0) (htors : IsIPowerTorsion R (cohomologyModule d e) I)
    {y : B ⊗[R] S} (hy : e.rTensor S y = 0) :
    ∃ b : B, e b = 0 ∧ y - b ⊗ₜ[R] (1 : S) ∈ LinearMap.range (d.rTensor S) := by
  set Z := LinearMap.ker e
  have hexS := exact_rTensor_coboundaryLift (S := S) hde
  have hZ : Function.Exact Z.subtype e := by
    intro x
    simp [Z]
  obtain ⟨u, rfl⟩ := (Module.Flat.rTensor_exact S hZ y).mp hy
  obtain ⟨h, hh⟩ := (bijective_cohomologyModule_tensorUnit I hflat hq htors).2
    ((cohomologyπ d e).rTensor S u)
  obtain ⟨z, rfl⟩ := surjective_cohomologyπ (d := d) (e := e) h
  have hdiff : (cohomologyπ d e).rTensor S (u - z ⊗ₜ[R] (1 : S)) = 0 := by
    rw [map_sub, LinearMap.rTensor_tmul, ← hh]
    simp
  obtain ⟨w, hw⟩ := (hexS _).mp hdiff
  refine ⟨z, z.2, w, ?_⟩
  rw [← show Z.subtype ∘ₗ coboundaryLift hde = d from rfl,
    LinearMap.rTensor_comp, LinearMap.comp_apply, hw, map_sub, LinearMap.rTensor_tmul]
  rfl

end FormalGlueing
