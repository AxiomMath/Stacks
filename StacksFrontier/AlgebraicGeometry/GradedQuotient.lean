module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# The grading of a quotient by a homogeneous ideal

Let `𝒜` be an internal grading of a commutative ring `A` by a family of additive subgroups, and
let `I` be a homogeneous ideal of `A`. The images of the graded pieces `𝒜 d` under the quotient
map `A → A ⧸ I` form an internal grading of `A ⧸ I`.

## Main definitions

* `Stacks.GradedQuotient.grading` is the family of additive subgroups of `A ⧸ I` given by the
  images of the graded pieces of `𝒜`.
* `Stacks.GradedQuotient.decomposition` is the direct sum decomposition of `A ⧸ I` along that
  family.

## Main results

* `Stacks.GradedQuotient.gradedRing` is the resulting `GradedRing` structure.
* `Stacks.GradedQuotient.gradedRingOfCoeEq` is the same statement for any family of additive
  subgroups whose carriers are the degreewise images, which is the form a client needs when its
  grading is spelled with `AddSubgroup.map` rather than with `Stacks.GradedQuotient.grading`.

## Implementation notes

The decomposition is built by lifting the composite `A → ⨁ d, 𝒜 d → ⨁ d, grading 𝒜 I d` through
the quotient; homogeneity of `I` is exactly what makes that composite kill `I`. The lift uses
`QuotientAddGroup.lift`, which applies because `Submodule.Quotient.addCommGroup` is by definition
the additive group structure of the quotient by the underlying additive subgroup.

Mathlib has no grading on a quotient by a homogeneous ideal, so this is new infrastructure
rather than a wrapper.
-/

@[expose] public section

open DirectSum

namespace Stacks.GradedQuotient

variable {ι σ A : Type*} [DecidableEq ι] [AddMonoid ι] [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (I : Ideal A)

/-- The image of the degree `d` piece of `𝒜` in the quotient ring `A ⧸ I`. -/
def grading (d : ι) : AddSubgroup (A ⧸ I) where
  carrier := Ideal.Quotient.mk I '' (𝒜 d)
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, add_mem ha hb, map_add _ _ _⟩
  zero_mem' := ⟨0, zero_mem _, map_zero _⟩
  neg_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨-a, neg_mem ha, map_neg _ _⟩

omit [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜] in
/-- The underlying set of `grading 𝒜 I d` is the image of `𝒜 d` under the quotient map. -/
theorem coe_grading (d : ι) :
    (grading 𝒜 I d : Set (A ⧸ I)) = Ideal.Quotient.mk I '' (𝒜 d) := rfl

omit [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜] in
/-- An element of `A ⧸ I` lies in `grading 𝒜 I d` if and only if it is the class of an element
of `𝒜 d`. -/
theorem mem_grading {d : ι} {x : A ⧸ I} :
    x ∈ grading 𝒜 I d ↔ ∃ a ∈ 𝒜 d, Ideal.Quotient.mk I a = x := Iff.rfl

omit [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜] in
/-- The class of an element of `𝒜 d` lies in `grading 𝒜 I d`. -/
theorem mk_mem_grading {d : ι} {a : A} (ha : a ∈ 𝒜 d) :
    Ideal.Quotient.mk I a ∈ grading 𝒜 I d := ⟨a, ha, rfl⟩

/-- The images of the graded pieces of `𝒜` form a graded monoid in `A ⧸ I`. -/
instance : SetLike.GradedMonoid (grading 𝒜 I) where
  one_mem := ⟨1, SetLike.GradedOne.one_mem, map_one _⟩
  mul_mem := by
    rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, SetLike.GradedMul.mul_mem ha hb, map_mul _ _ _⟩

/-- The quotient map from the degree `d` piece of `𝒜` onto its image in `A ⧸ I`. -/
def componentHom (d : ι) : 𝒜 d →+ grading 𝒜 I d where
  toFun a := ⟨Ideal.Quotient.mk I a.1, mk_mem_grading 𝒜 I a.2⟩
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

omit [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜] in
/-- The image of `a : 𝒜 d` under `componentHom 𝒜 I d` is the class of `a` in `A ⧸ I`. -/
@[simp]
theorem coe_componentHom (d : ι) (a : 𝒜 d) :
    (componentHom 𝒜 I d a : A ⧸ I) = Ideal.Quotient.mk I a.1 := rfl

/-- The composite `A → ⨁ d, 𝒜 d → ⨁ d, grading 𝒜 I d`, which descends to the quotient when `I`
is homogeneous. -/
def preDecompose : A →+ ⨁ d, grading 𝒜 I d :=
  (DirectSum.map (componentHom 𝒜 I)).comp (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

/-- The degree `d` component of `preDecompose 𝒜 I a` is the class of the degree `d` component
of `a`. -/
theorem preDecompose_apply (a : A) (d : ι) :
    preDecompose 𝒜 I a d = componentHom 𝒜 I d (DirectSum.decompose 𝒜 a d) := by
  simp [preDecompose, DirectSum.decomposeAddEquiv]

/-- The sum of the components of `preDecompose 𝒜 I a` is the class of `a` in `A ⧸ I`. -/
theorem coe_preDecompose (a : A) :
    DirectSum.coeAddMonoidHom (grading 𝒜 I) (preDecompose 𝒜 I a) = Ideal.Quotient.mk I a := by
  have key : (DirectSum.coeAddMonoidHom (grading 𝒜 I)).comp (DirectSum.map (componentHom 𝒜 I)) =
      (Ideal.Quotient.mk I).toAddMonoidHom.comp (DirectSum.coeAddMonoidHom 𝒜) :=
    DirectSum.addHom_ext fun d a => by simp
  have hcoe : DirectSum.coeAddMonoidHom 𝒜 (DirectSum.decompose 𝒜 a) = a :=
    (DirectSum.decompose 𝒜).left_inv a
  have h := DFunLike.congr_fun key (DirectSum.decompose 𝒜 a)
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, RingHom.toAddMonoidHom_eq_coe,
    hcoe] at h
  simpa [preDecompose, DirectSum.decomposeAddEquiv] using h

/-- If `I` is homogeneous, then `preDecompose 𝒜 I` vanishes on `I`. -/
theorem preDecompose_eq_zero_of_mem (hI : I.IsHomogeneous 𝒜) {a : A} (ha : a ∈ I) :
    preDecompose 𝒜 I a = 0 := by
  refine DFunLike.ext _ _ fun d => Subtype.coe_injective ?_
  change Ideal.Quotient.mk I (DirectSum.decompose 𝒜 a d : A) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI d ha)

/-- The decomposition map of the quotient, obtained from `Stacks.GradedQuotient.preDecompose`
by descending through `I`. -/
def decomposeHom (hI : I.IsHomogeneous 𝒜) : (A ⧸ I) →+ ⨁ d, grading 𝒜 I d :=
  QuotientAddGroup.lift I.toAddSubgroup (preDecompose 𝒜 I) fun _ ha =>
    preDecompose_eq_zero_of_mem 𝒜 I hI ha

/-- `decomposeHom 𝒜 I hI` sends the class of `a` to `preDecompose 𝒜 I a`. -/
@[simp]
theorem decomposeHom_mk (hI : I.IsHomogeneous 𝒜) (a : A) :
    decomposeHom 𝒜 I hI (Ideal.Quotient.mk I a) = preDecompose 𝒜 I a := rfl

/-- A quotient of a graded commutative ring by a homogeneous ideal decomposes as the direct sum
of the images of the graded pieces. -/
@[instance_reducible]
def decomposition (hI : I.IsHomogeneous 𝒜) : DirectSum.Decomposition (grading 𝒜 I) :=
  DirectSum.Decomposition.ofAddHom (grading 𝒜 I) (decomposeHom 𝒜 I hI)
    (AddMonoidHom.ext fun x => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      simpa using coe_preDecompose 𝒜 I a)
    (DirectSum.addHom_ext fun d x => by
      obtain ⟨a, ha, hax⟩ := x.2
      have hx : x = componentHom 𝒜 I d ⟨a, ha⟩ := Subtype.ext hax.symm
      simp [DirectSum.coeAddMonoidHom_of, preDecompose,
        DirectSum.decompose_of_mem 𝒜 ha, hx])

/-- The quotient of a graded commutative ring by a homogeneous ideal is graded by the images of
the graded pieces. -/
@[instance_reducible]
def gradedRing (hI : I.IsHomogeneous 𝒜) : GradedRing (grading 𝒜 I) :=
  { (inferInstance : SetLike.GradedMonoid (grading 𝒜 I)), decomposition 𝒜 I hI with }

/-- Any family of additive subgroups of `A ⧸ I` whose carriers are the images of the graded
pieces of `𝒜` is a grading of `A ⧸ I`, when `I` is homogeneous. -/
@[instance_reducible]
def gradedRingOfCoeEq (hI : I.IsHomogeneous 𝒜) (ℐ : ι → AddSubgroup (A ⧸ I))
    (hℐ : ∀ d, (ℐ d : Set (A ⧸ I)) = Ideal.Quotient.mk I '' (𝒜 d)) : GradedRing ℐ := by
  have h : ℐ = grading 𝒜 I := funext fun d => SetLike.coe_injective (hℐ d)
  subst h
  exact gradedRing 𝒜 I hI

end Stacks.GradedQuotient

end
