module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjRegrading
public import StacksFrontier.AlgebraicGeometry.Limits.ProjGradedSurjection01N0
public import StacksFrontier.AlgebraicGeometry.ProjClosedImmersion.Quotient
public import StacksFrontier.RingTheory.GradedAlgebra.NoetherianModel

/-!
# A surjection of graded rings is the quotient by its kernel

Let `f : 𝒜 →+*ᵍ ℬ` be a surjective homomorphism of graded rings. Its kernel is a homogeneous
ideal, and `f` therefore factors as the quotient map `𝒜 ⟶ 𝒜 ⧸ ker f` followed by an
**isomorphism** of graded rings `𝒜 ⧸ ker f ≅ ℬ`. This file builds that isomorphism and records
what it says about the induced morphisms of projective spectra: `AlgebraicGeometry.Proj.map f` is
an isomorphism `Proj ℬ ≅ Proj (𝒜 ⧸ ker f)` followed by the canonical morphism
`Proj (𝒜 ⧸ ker f) ⟶ Proj 𝒜`.

That last statement is a form of "two surjections of graded rings with the same kernel induce
the same morphism of projective spectra": a morphism presented as
`AlgebraicGeometry.Proj.map` of an arbitrary surjection is identified, up to a canonical
isomorphism of its source, with one presented as `Proj.map` of a graded *quotient* map, which is
the shape `Stacks.ClosedSubschemeProjQuotient.ambientHom` has.

## Main definitions

* `Stacks.GradedKerQuotient.homogeneousKer`: the kernel of a homomorphism of graded rings, as a
  `HomogeneousIdeal`.
* `Stacks.GradedKerQuotient.desc`: the induced homomorphism `𝒜 ⧸ ker f →+*ᵍ ℬ`.
* `Stacks.GradedKerQuotient.inv`: its inverse.
* `Stacks.GradedKerQuotient.projIso`: **the induced isomorphism `Proj ℬ ≅ Proj (𝒜 ⧸ ker f)`.**

## Main results

* `Stacks.GradedKerQuotient.desc_comp_quotientMk`: **`f` factors through the quotient by its own
  kernel**, by the isomorphism above.
* `Stacks.GradedKerQuotient.inv_comp_desc` and `…desc_comp_inv`: the two homomorphisms are
  mutually inverse.
* `Stacks.GradedKerQuotient.projMap_eq`: **`Proj.map f` is the isomorphism followed by `Proj.map`
  of the quotient map.**

## Implementation notes

The grading is a family `𝒜 : ℕ → σ` of additive subgroups for an arbitrary `σ`, which is the
shape `AlgebraicGeometry.Proj`, `HomogeneousIdeal` and
`Stacks.HomogeneousIdeal.quotientGrading` are all stated for; in particular the grading of a
relative-Proj chart, `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.grading`, is
of that shape and needs no transport.

The inverse is produced from `RingEquiv.ofBijective` rather than by choosing preimages: the
descent is injective because the kernel of `f` is exactly the ideal divided out, and surjective
because `f` is. Grading-preservation of the inverse is where surjectivity is used a second time,
through `AlgebraicGeometry.Proj.gradedAddHom_surjective_of_surjective`: a homogeneous element
of the target is the image of a homogeneous element of the same degree, whose
class in the quotient is therefore a homogeneous preimage.

Everything is stated for the underlying `RingHom` first and the graded homomorphisms are built on
top of it. `GradedRingHom` coercion is not syntactically the coercion of the underlying
`RingHom`, so a lemma proved about one is not available to `rw` at the other; the
`…_apply` lemmas below are the bridges, and they are `rfl`.

## References

* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousIdeal
open Stacks.HomogeneousIdeal

namespace Stacks.GradedKerQuotient

universe u

variable {σ τ A B : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-! ### The kernel and the descent -/

/-- **The kernel of a homomorphism of graded rings, as a homogeneous ideal.** Homogeneity is
`Stacks.GradedModel.isHomogeneous_ker`. -/
def homogeneousKer (f : 𝒜 →+*ᵍ ℬ) : HomogeneousIdeal 𝒜 :=
  ⟨RingHom.ker (f : A →+* B), Stacks.GradedModel.isHomogeneous_ker 𝒜 ℬ f⟩

/-- An element lies in the kernel exactly when `f` kills it. -/
theorem mem_homogeneousKer_iff (f : 𝒜 →+*ᵍ ℬ) (x : A) :
    x ∈ (homogeneousKer 𝒜 ℬ f).toIdeal ↔ f x = 0 := RingHom.mem_ker

/-- The descent of `f` to the quotient by its kernel, as a ring homomorphism. -/
def descRingHom (f : 𝒜 →+*ᵍ ℬ) : (A ⧸ (homogeneousKer 𝒜 ℬ f).toIdeal) →+* B :=
  Ideal.Quotient.lift _ (f : A →+* B) fun _ ha => ha

/-- The descent sends the class of `a` to `f a`. -/
@[simp]
theorem descRingHom_mk (f : 𝒜 →+*ᵍ ℬ) (a : A) :
    descRingHom 𝒜 ℬ f (Ideal.Quotient.mk (homogeneousKer 𝒜 ℬ f).toIdeal a) = f a :=
  Ideal.Quotient.lift_mk _ _ _

/-- The descent to the quotient by the kernel is injective. -/
theorem injective_descRingHom (f : 𝒜 →+*ᵍ ℬ) : Function.Injective (descRingHom 𝒜 ℬ f) :=
  RingHom.kerLift_injective (f : A →+* B)

/-- The descent of a surjection is surjective. -/
theorem surjective_descRingHom (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    Function.Surjective (descRingHom 𝒜 ℬ f) :=
  Ideal.Quotient.lift_surjective_of_surjective _ _ hf

/-- **The descent of a surjection to the quotient by its kernel is a ring isomorphism.** -/
def descRingEquiv (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    (A ⧸ (homogeneousKer 𝒜 ℬ f).toIdeal) ≃+* B :=
  RingEquiv.ofBijective (descRingHom 𝒜 ℬ f)
    ⟨injective_descRingHom 𝒜 ℬ f, surjective_descRingHom 𝒜 ℬ f hf⟩

/-- The ring isomorphism `descRingEquiv` acts as the descent. -/
theorem descRingEquiv_apply (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    (x : A ⧸ (homogeneousKer 𝒜 ℬ f).toIdeal) :
    descRingEquiv 𝒜 ℬ f hf x = descRingHom 𝒜 ℬ f x := rfl

/-- **The descent of `f` to the quotient by its kernel, as a homomorphism of graded rings.** -/
def desc (f : 𝒜 →+*ᵍ ℬ) : quotientGrading (homogeneousKer 𝒜 ℬ f) →+*ᵍ ℬ where
  __ := descRingHom 𝒜 ℬ f
  map_mem := by
    rintro i x ⟨a, ha, rfl⟩
    exact (descRingHom_mk 𝒜 ℬ f a) ▸ f.map_mem ha

/-- The graded descent acts as the ring-homomorphism descent. -/
theorem desc_apply (f : 𝒜 →+*ᵍ ℬ) (x : A ⧸ (homogeneousKer 𝒜 ℬ f).toIdeal) :
    desc 𝒜 ℬ f x = descRingHom 𝒜 ℬ f x := rfl

/-- The graded descent sends the class of `a` to `f a`. -/
@[simp]
theorem desc_mk (f : 𝒜 →+*ᵍ ℬ) (a : A) :
    desc 𝒜 ℬ f (Ideal.Quotient.mk (homogeneousKer 𝒜 ℬ f).toIdeal a) = f a :=
  descRingHom_mk 𝒜 ℬ f a

/-- **`f` factors through the quotient by its own kernel.** -/
theorem desc_comp_quotientMk (f : 𝒜 →+*ᵍ ℬ) :
    (desc 𝒜 ℬ f).comp (quotientMk (homogeneousKer 𝒜 ℬ f)) = f :=
  GradedRingHom.ext fun a => desc_mk 𝒜 ℬ f a

/-! ### The inverse -/

/-- **The inverse of the descent, as a homomorphism of graded rings.** Surjectivity in each degree
is what makes it grading-preserving: a homogeneous element of the target is the image of a
homogeneous element of the same degree, whose class in the quotient is its preimage. -/
def inv (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    ℬ →+*ᵍ quotientGrading (homogeneousKer 𝒜 ℬ f) where
  __ := (descRingEquiv 𝒜 ℬ f hf).symm.toRingHom
  map_mem := by
    intro i y hy
    obtain ⟨a, ha⟩ :=
      Proj.gradedAddHom_surjective_of_surjective f hf i ⟨y, hy⟩
    have hay : f (a : A) = y := congrArg Subtype.val ha
    have hmk : (descRingEquiv 𝒜 ℬ f hf).symm y =
        Ideal.Quotient.mk (homogeneousKer 𝒜 ℬ f).toIdeal (a : A) := by
      rw [← hay, ← descRingHom_mk 𝒜 ℬ f (a : A),
        ← descRingEquiv_apply 𝒜 ℬ f hf, RingEquiv.symm_apply_apply]
    exact hmk ▸ mk_mem_quotientGrading _ a.2

/-- The graded inverse acts as the inverse of `descRingEquiv`. -/
theorem inv_apply (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) (y : B) :
    inv 𝒜 ℬ f hf y = (descRingEquiv 𝒜 ℬ f hf).symm y := rfl

/-- The inverse undoes the descent. -/
theorem inv_comp_desc (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    (inv 𝒜 ℬ f hf).comp (desc 𝒜 ℬ f) =
      GradedRingHom.id (quotientGrading (homogeneousKer 𝒜 ℬ f)) :=
  GradedRingHom.ext fun x => (descRingEquiv 𝒜 ℬ f hf).symm_apply_apply x

/-- The descent undoes the inverse. -/
theorem desc_comp_inv (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    (desc 𝒜 ℬ f).comp (inv 𝒜 ℬ f hf) = GradedRingHom.id ℬ :=
  GradedRingHom.ext fun y => (descRingEquiv 𝒜 ℬ f hf).apply_symm_apply y

/-! ### The induced morphisms of projective spectra -/

/-- The descent satisfies the irrelevant-ideal hypothesis of `AlgebraicGeometry.Proj.map`: it has
a graded inverse. -/
theorem irrelevant_le_map_desc (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    ℬ₊ ≤ (quotientGrading (homogeneousKer 𝒜 ℬ f))₊.map (desc 𝒜 ℬ f) :=
  Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id (desc_comp_inv 𝒜 ℬ f hf)

/-- The inverse of the descent satisfies the irrelevant-ideal hypothesis of
`AlgebraicGeometry.Proj.map`. -/
theorem irrelevant_le_map_inv (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    (quotientGrading (homogeneousKer 𝒜 ℬ f))₊ ≤ ℬ₊.map (inv 𝒜 ℬ f hf) :=
  Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id (inv_comp_desc 𝒜 ℬ f hf)

/-- **The isomorphism of projective spectra attached to a surjection of graded rings**: `Proj ℬ`
is `Proj` of the quotient of `𝒜` by the kernel of the surjection. -/
def projIso (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    AlgebraicGeometry.Proj ℬ ≅
      AlgebraicGeometry.Proj (quotientGrading (homogeneousKer 𝒜 ℬ f)) :=
  @asIso _ _ _ _ _ (Proj.isIso_map (irrelevant_le_map_desc 𝒜 ℬ f hf)
    (irrelevant_le_map_inv 𝒜 ℬ f hf) (inv_comp_desc 𝒜 ℬ f hf) (desc_comp_inv 𝒜 ℬ f hf))

/-- The forward map of `projIso` is `Proj.map` of the descent. -/
theorem projIso_hom (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    (projIso 𝒜 ℬ f hf).hom = Proj.map (desc 𝒜 ℬ f) (irrelevant_le_map_desc 𝒜 ℬ f hf) := rfl

/-- The quotient map satisfies the irrelevant-ideal hypothesis of `AlgebraicGeometry.Proj.map`:
it is surjective. -/
theorem irrelevant_le_map_quotientMk (f : 𝒜 →+*ᵍ ℬ) :
    (quotientGrading (homogeneousKer 𝒜 ℬ f))₊ ≤ 𝒜₊.map (quotientMk (homogeneousKer 𝒜 ℬ f)) :=
  Proj.irrelevant_le_map_of_surjective _ (surjective_quotientMk _)

/-- **`Proj.map` of a surjection is `Proj.map` of the quotient map by its kernel**, precomposed
with the canonical isomorphism of the source. This is the identification of a morphism of
projective spectra presented by an arbitrary surjection with one presented by a graded quotient
map — the shape `Stacks.ClosedSubschemeProjQuotient.ambientHom` has. -/
theorem projMap_eq (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) (hirr : ℬ₊ ≤ 𝒜₊.map f) :
    Proj.map f hirr = (projIso 𝒜 ℬ f hf).hom ≫
      Proj.map (quotientMk (homogeneousKer 𝒜 ℬ f)) (irrelevant_le_map_quotientMk 𝒜 ℬ f) := by
  rw [projIso_hom, ← Proj.map_comp]
  exact Proj.map_congr (desc_comp_quotientMk 𝒜 ℬ f) _ hirr

end Stacks.GradedKerQuotient

end
