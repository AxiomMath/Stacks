module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChangeGlobal

/-!
# Changing the family in which a grading takes its values

A grading of a commutative ring `A` is a family `𝒜 : ι → σ` of subobjects of `A`, for any `σ`
satisfying `SetLike σ A` and `AddSubgroupClass σ A`. The same decomposition of `A` can therefore
be presented by families valued in different `σ`'s — most often by a family of additive subgroups
and by a family of submodules with the same carriers — and the resulting graded rings, their
homogeneous localizations and their projective spectra are then different terms of different
types.

This file supplies the comparison. Two families with the same carriers grade `A` in the same way,
the identity of `A` is a homomorphism of graded rings between them, and the induced morphism of
projective spectra is an isomorphism.

## Main definitions

* `Stacks.GradedRegrading.gradedRing` is the `GradedRing` structure transported along an equality
  of carriers.
* `Stacks.GradedRegrading.regrade` is the identity of `A`, read as a homomorphism of graded rings
  between two families with the same carriers.
* `Stacks.GradedRegrading.projIso` is the induced isomorphism of projective spectra.

## Main results

* `Stacks.GradedRegrading.irrelevant_le_map_regrade`: the irrelevant-ideal hypothesis that
  `AlgebraicGeometry.Proj.map` asks of `Stacks.GradedRegrading.regrade`.
* `Stacks.GradedRegrading.projIso_hom_comp_toSpecZero`: the comparison isomorphism is a morphism
  over the degree-zero parts.
* `Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id`: the same irrelevant-ideal hypothesis
  for an arbitrary homomorphism of graded rings admitting a section.

## Implementation notes

The transported decomposition is built with `DirectSum.Decomposition.ofAddHom` from the
degreewise identity `𝒜 i →+ ℬ i`, exactly as `Stacks.GradedQuotient.decomposition` is built from
the degreewise quotient map; the two inverse conditions are checked on the generators of the
direct sum by `DirectSum.addHom_ext`.

A `GradedRing` structure is not an instance here, since neither family determines the other: the
transported structure is applied explicitly, or registered with `attribute [local instance]` in a
file that fixes both families.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry DirectSum Graded HomogeneousIdeal

universe u

namespace Stacks.GradedRegrading

/-! ### Transporting a grading -/

section Algebra

variable {ι A σ τ : Type*} [DecidableEq ι] [AddMonoid ι] [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ A] [AddSubgroupClass τ A]

omit [DecidableEq ι] [AddMonoid ι] [CommRing A] [AddSubgroupClass σ A] [AddSubgroupClass τ A] in
/-- Membership in two families of additive subgroups with the same carriers is the same
condition. -/
theorem mem_congr {𝒜 : ι → σ} {ℬ : ι → τ} (h : ∀ i, (𝒜 i : Set A) = ℬ i) {i : ι} {x : A} :
    x ∈ 𝒜 i ↔ x ∈ ℬ i := by
  rw [← SetLike.mem_coe, ← SetLike.mem_coe, h i]

/-- The identity of `A`, read degreewise between two families with the same carriers. -/
def componentHom {𝒜 : ι → σ} {ℬ : ι → τ} (h : ∀ i, (𝒜 i : Set A) = ℬ i) (i : ι) :
    𝒜 i →+ ℬ i where
  toFun x := ⟨x.1, (mem_congr h).mp x.2⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

omit [DecidableEq ι] [AddMonoid ι] in
/-- The degreewise identity `Stacks.GradedRegrading.componentHom` does not change the underlying
element of `A`. -/
@[simp]
theorem coe_componentHom {𝒜 : ι → σ} {ℬ : ι → τ} (h : ∀ i, (𝒜 i : Set A) = ℬ i) (i : ι)
    (x : 𝒜 i) : (componentHom h i x : A) = x := rfl

omit [DecidableEq ι] [AddSubgroupClass σ A] [AddSubgroupClass τ A] in
/-- Two families with the same carriers have the same graded monoid structure. -/
theorem gradedMonoid {𝒜 : ι → σ} {ℬ : ι → τ} [SetLike.GradedMonoid 𝒜]
    (h : ∀ i, (𝒜 i : Set A) = ℬ i) : SetLike.GradedMonoid ℬ where
  one_mem := (mem_congr h).mp SetLike.GradedOne.one_mem
  mul_mem := by
    intro _ _ _ _ hx hy
    exact (mem_congr h).mp
      (SetLike.GradedMul.mul_mem ((mem_congr h).mpr hx) ((mem_congr h).mpr hy))

/-- The decomposition of `A` along a family of additive subgroups, transported to a family with
the same carriers. -/
@[instance_reducible]
def decomposition {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] (h : ∀ i, (𝒜 i : Set A) = ℬ i) :
    DirectSum.Decomposition ℬ :=
  DirectSum.Decomposition.ofAddHom ℬ
    ((DirectSum.map (componentHom h)).comp (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom)
    (AddMonoidHom.ext fun x ↦ by
      have key : (DirectSum.coeAddMonoidHom ℬ).comp (DirectSum.map (componentHom h)) =
          DirectSum.coeAddMonoidHom 𝒜 := DirectSum.addHom_ext fun i y ↦ by simp
      simpa [DirectSum.decomposeAddEquiv] using
        congr($key (DirectSum.decompose 𝒜 x)).trans ((DirectSum.decompose 𝒜).left_inv x))
    (DirectSum.addHom_ext fun i x ↦ by
      have hx : (x : A) ∈ 𝒜 i := (mem_congr h).mpr x.2
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.coeAddMonoidHom_of,
        AddMonoidHom.id_apply, AddEquiv.coe_toAddMonoidHom, DirectSum.decomposeAddEquiv_apply,
        DirectSum.decompose_of_mem 𝒜 hx, DirectSum.map_of]
      rfl)

/-- **A family of additive subgroups with the same carriers as a grading is a grading.** -/
@[instance_reducible]
def gradedRing {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] (h : ∀ i, (𝒜 i : Set A) = ℬ i) :
    GradedRing ℬ :=
  { gradedMonoid h, decomposition h with }

/-- The identity of `A`, read as a homomorphism of graded rings between two families with the
same carriers. -/
def regrade {𝒜 : ι → σ} {ℬ : ι → τ} (h : ∀ i, (𝒜 i : Set A) = ℬ i) : 𝒜 →+*ᵍ ℬ where
  __ := RingHom.id A
  map_mem hx := (mem_congr h).mp hx

omit [DecidableEq ι] [AddMonoid ι] [AddSubgroupClass σ A] [AddSubgroupClass τ A] in
/-- `Stacks.GradedRegrading.regrade` is the identity on elements of `A`. -/
@[simp]
theorem regrade_apply {𝒜 : ι → σ} {ℬ : ι → τ} (h : ∀ i, (𝒜 i : Set A) = ℬ i) (x : A) :
    regrade h x = x := rfl

omit [DecidableEq ι] [AddMonoid ι] [AddSubgroupClass σ A] [AddSubgroupClass τ A] in
/-- Regrading from `𝒜` to `ℬ` and back is the identity homomorphism of graded rings of `𝒜`. -/
theorem regrade_comp_regrade {𝒜 : ι → σ} {ℬ : ι → τ} (h : ∀ i, (𝒜 i : Set A) = ℬ i) :
    (regrade fun i ↦ (h i).symm).comp (regrade h) = GradedRingHom.id 𝒜 :=
  GradedRingHom.ext fun _ ↦ rfl

end Algebra

/-- A homomorphism of graded rings with a section satisfies the irrelevant-ideal hypothesis. -/
private theorem irrelevant_le_map_of_comp {A B σ τ : Type*} [CommRing A] [CommRing B] [SetLike σ A]
    [AddSubmonoidClass σ A] [SetLike τ B] [AddSubmonoidClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
    [GradedRing 𝒜] [GradedRing ℬ] {f : 𝒜 →+*ᵍ ℬ} {g : ℬ →+*ᵍ 𝒜}
    (hfg : f.comp g = GradedRingHom.id ℬ) : ℬ₊ ≤ 𝒜₊.map f := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi x hx
  have hx' : f (g x) = x := congr($hfg x)
  exact hx' ▸ Ideal.mem_map_of_mem _ (mem_irrelevant_of_mem 𝒜 hi (map_mem g hx))

/-! ### The comparison of projective spectra -/

section Proj

variable {A σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ A]
  [AddSubgroupClass τ A] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The irrelevant ideal of `ℬ` is generated by the image of the irrelevant ideal of `𝒜` under
the identity, so `Stacks.GradedRegrading.regrade` induces a morphism of projective spectra. -/
theorem irrelevant_le_map_regrade (h : ∀ i, (𝒜 i : Set A) = ℬ i) :
    ℬ₊ ≤ 𝒜₊.map (regrade h) :=
  irrelevant_le_map_of_comp (regrade_comp_regrade fun i ↦ (h i).symm)

/-- **Two families of additive subgroups with the same carriers have the same projective
spectrum.** -/
def projIso (h : ∀ i, (𝒜 i : Set A) = ℬ i) : Proj ℬ ≅ Proj 𝒜 :=
  @asIso _ _ _ _ _ (Proj.isIso_map (irrelevant_le_map_regrade h)
    (irrelevant_le_map_regrade fun i ↦ (h i).symm) (regrade_comp_regrade h)
    (regrade_comp_regrade fun i ↦ (h i).symm))

/-- The comparison isomorphism of projective spectra is `AlgebraicGeometry.Proj.map` of the
degreewise identity. -/
theorem projIso_hom (h : ∀ i, (𝒜 i : Set A) = ℬ i) :
    (projIso h).hom = Proj.map (regrade h) (irrelevant_le_map_regrade h) := rfl

/-- The comparison isomorphism of projective spectra is a morphism over `Spec` of the degree-zero
parts, which are themselves identified by the degreewise identity. -/
theorem projIso_hom_comp_toSpecZero (h : ∀ i, (𝒜 i : Set A) = ℬ i) :
    (projIso h).hom ≫ Proj.toSpecZero 𝒜 = Proj.toSpecZero ℬ ≫
      Spec.map (CommRingCat.ofHom (regrade h).gradedZeroRingHom) :=
  Proj.map_toSpecZero _ _

end Proj

/-! ### Homomorphisms of graded rings with a section -/

section Section

variable {A B σ τ : Type*} [CommRing A] [CommRing B] [SetLike σ A] [AddSubmonoidClass σ A]
  [SetLike τ B] [AddSubmonoidClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- **A homomorphism of graded rings with a section satisfies the irrelevant-ideal hypothesis of
`AlgebraicGeometry.Proj.map`.** A homogeneous element of positive degree of the target is the
image of its own preimage under the section, which is homogeneous of the same degree and hence
irrelevant. -/
theorem irrelevant_le_map_of_comp_eq_id {f : 𝒜 →+*ᵍ ℬ} {g : ℬ →+*ᵍ 𝒜}
    (hfg : f.comp g = GradedRingHom.id ℬ) : ℬ₊ ≤ 𝒜₊.map f :=
  irrelevant_le_map_of_comp hfg

end Section

end Stacks.GradedRegrading

end
