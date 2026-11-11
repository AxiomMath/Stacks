module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso

/-!
# The Picard category of Section 0372

Let `π : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site.
Stacks, Section 0372 defines the category `Picardstack_{X/B}`: an object is a triple `(U, b, L)`
of a scheme `U` of `(Sch/S)_fppf`, a morphism `b : U ⟶ B` over `S` and an invertible sheaf `L` on
the base change `X_U`; a morphism `(f, g) : (U, b, L) ⟶ (U', b', L')` is a morphism of schemes
`f : U ⟶ U'` over `B` together with an isomorphism `g : f^*L' ⟶ L`; the composite of `(f, g)`
with `(f', g')` is `(f' ∘ f, g ∘ f^*(g'))`.  It comes with the functor
`p : Picardstack_{X/B} ⟶ (Sch/S)_fppf`, `(U, b, L) ↦ U`, whose fibre category over `U` is the
disjoint union over `b ∈ Mor_S(U, B)` of the categories of invertible sheaves on `X_U`, so that
the fibre categories are groupoids.

This file records the category, its functor `p` and the groupoid fibres with no hypothesis.  The
objects, the morphisms and the composition are
`AlgebraicGeometry.Space.PicardObject`, `AlgebraicGeometry.Space.PicardHom` and
`AlgebraicGeometry.Space.PicardHom.comp` of
`StacksFrontier/AlgebraicGeometry/Quot/PicardStack.lean`.  The identities and the three category
laws of `StacksFrontier/AlgebraicGeometry/Quot/PicardStackCategory.lean` are stated over a
pseudofunctoriality `AlgebraicGeometry.Space.ModulePushforwardCoherence` of the direct images of
Stacks 03LU, and here that input is `AlgebraicGeometry.Space.modulePushforwardCoherence`, which is
constructed with no hypothesis.

## Main definitions

* `AlgebraicGeometry.Space.picardStackCategory`: **Section 0372**, the category
  `Picardstack_{X/B}`.
* `AlgebraicGeometry.Space.picardStackBasedCategory`: **Section 0372**, the functor
  `p : Picardstack_{X/B} ⟶ (Sch/S)_fppf`.

## Main results

* `AlgebraicGeometry.Space.picardStackBasedCategory_fiber_isGroupoid`: **Section 0372**, the
  fibre categories of `p` are groupoids.
* `AlgebraicGeometry.Space.picardStackBasedCategory_fiber_hom_structure`: a morphism of the
  fibre of `p` over `U` preserves the morphism `b : U ⟶ B`, so that the fibre is the disjoint
  union over the `b` of the categories of invertible modules on `X_U`.

## Implementation notes

The source writes the base change as `U ×_{b, B} X` and this development as `X ×_B U`, the
convention of `AlgebraicGeometry.Space.PicardSituation` of Stacks 0D25; the two differ by the
symmetry of a fibre product.  The full stack condition of Stacks 04WN for `p` is
`AlgebraicGeometry.Space.picardBasedCategory_isStackInGroupoids` of
`StacksFrontier/AlgebraicGeometry/Quot/PicardStackIsStack.lean`, stated for the same functor.

## References

* [Stacks Project, Section 0372](https://stacks.math.columbia.edu/tag/0372)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (s : PicardSituation B S hS)

/-- **Section 0372, the category `Picardstack_{X/B}`.**  The objects are the triples `(U, b, L)`
of `AlgebraicGeometry.Space.PicardObject`, the morphisms `(U, b, L) ⟶ (U', b', L')` are the
pairs `(f, g)` of `AlgebraicGeometry.Space.PicardHom` of a morphism of schemes `f : U ⟶ U'`
over the base and an isomorphism `g : f^*L' ⟶ L`, the composite of `(f, g)` with `(f', g')` is
`(f' ∘ f, g ∘ f^*(g'))` (`AlgebraicGeometry.Space.PicardHom.comp`), and the identity of
`(U, b, L)` is the identity of `U` with the unit law `(𝟙)^*L ≅ L` of the inverse images of
Stacks 03LU.

The comparisons of inverse images are the ones of the pseudofunctoriality
`AlgebraicGeometry.Space.modulePushforwardCoherence` of the direct images, which is constructed
with no hypothesis, so the category takes no input beyond the morphism `π : X ⟶ B` of algebraic
spaces of `s`. -/
@[instance_reducible, stacks 0372 "the category Picardstack_{X/B}: objects (U, b, L), morphisms \
(f, g) with g : f^*L' ≅ L, composition (f' ∘ f, g ∘ f^*(g')), and its identities"]
def picardStackCategory : Category.{u + 1} (PicardObject s) :=
  picardCategory (modulePushforwardCoherence B S hS) s

/-- The morphisms of `AlgebraicGeometry.Space.picardStackCategory` are the pairs `(f, g)` of
`AlgebraicGeometry.Space.PicardHom`. -/
theorem picardStackCategory_hom (A C : PicardObject s) :
    (letI := picardStackCategory s; A ⟶ C) = PicardHom A C :=
  rfl

/-- The identity of `AlgebraicGeometry.Space.picardStackCategory` is
`AlgebraicGeometry.Space.PicardHom.id`: the identity of the test scheme together with the unit
law `(𝟙)^*L ≅ L` of Stacks 03LU. -/
theorem picardStackCategory_id (A : PicardObject s) :
    @CategoryStruct.id (PicardObject s) (picardStackCategory s).toCategoryStruct A =
      PicardHom.id (modulePushforwardCoherence B S hS) A :=
  rfl

/-- Composition in `AlgebraicGeometry.Space.picardStackCategory` is
`AlgebraicGeometry.Space.PicardHom.comp`: the composite of `(f, g)` with `(f', g')` is
`(f' ∘ f, g ∘ f^*(g'))`. -/
theorem picardStackCategory_comp {A C D : PicardObject s} (m : PicardHom A C)
    (n : PicardHom C D) :
    @CategoryStruct.comp (PicardObject s) (picardStackCategory s).toCategoryStruct A C D m n =
      PicardHom.comp m n :=
  rfl

/-- **Section 0372, the functor `p : Picardstack_{X/B} ⟶ (Sch/S)_fppf`**, sending `(U, b, L)` to
`U` and `(f, g)` to `f`, as a category over the big fppf site of `S`. -/
@[stacks 0372 "the functor p : Picardstack_{X/B} ⟶ (Sch/S)_fppf, (U, b, L) ↦ U"]
def picardStackBasedCategory : BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS) :=
  picardBasedCategory (modulePushforwardCoherence B S hS) s

/-- The functor `p` of `AlgebraicGeometry.Space.picardStackBasedCategory` sends `(U, b, L)` to
`U`. -/
theorem picardStackBasedCategory_p_obj (A : PicardObject s) :
    (picardStackBasedCategory s).p.obj A = A.T.left :=
  rfl

/-- The functor `p` of `AlgebraicGeometry.Space.picardStackBasedCategory` sends `(f, g)` to `f`. -/
theorem picardStackBasedCategory_p_map {A C : PicardObject s} (m : PicardHom A C) :
    (picardStackBasedCategory s).p.map (X := A) (Y := C) m = m.base.left :=
  rfl

/-- In the fibre of `p` over a scheme `U`, a morphism `(U, b, L) ⟶ (U, b', L')` has `b = b'`:
the fibre category over `U` is the disjoint union over the morphisms `b : U ⟶ B` of the
categories of invertible modules on `X_U`. -/
theorem picardStackBasedCategory_fiber_hom_structure {U : BigFppfOver B S hS}
    {A C : (picardStackBasedCategory s).p.Fiber U} (φ : A ⟶ C) :
    (schemeSpaceFunctor B S hS).map (eqToHom (A.2.trans C.2.symm)) ≫ (C.1 : PicardObject s).T.hom =
      (A.1 : PicardObject s).T.hom := by
  have hφ : (picardStackBasedCategory s).p.IsHomLift (𝟙 U) φ.1 := φ.2
  have h := IsHomLift.fac' (picardStackBasedCategory s).p (𝟙 U) φ.1
  simp only [Category.id_comp, eqToHom_trans] at h
  rw [← CostructuredArrow.w (show PicardHom A.1 C.1 from φ.1).base]
  exact congrArg (fun k ↦ (schemeSpaceFunctor B S hS).map k ≫ (C.1 : PicardObject s).T.hom) h.symm

/-- **Section 0372, the fibre categories of `Picardstack_{X/B}` are groupoids.**  Every morphism
of the fibre of `p : Picardstack_{X/B} ⟶ (Sch/S)_fppf` over a scheme `U` is an isomorphism. -/
@[stacks 0372 "the fibre categories of Picardstack_{X/B} over (Sch/S)_fppf are groupoids"]
theorem picardStackBasedCategory_fiber_isGroupoid (U : BigFppfOver B S hS) :
    IsGroupoid ((picardStackBasedCategory s).p.Fiber U) :=
  (picardBasedCategory_isFiberedInGroupoids (modulePushforwardCoherence B S hS) s).fiber_isGroupoid
    U

end AlgebraicGeometry.Space

end
