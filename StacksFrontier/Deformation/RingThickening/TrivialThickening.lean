module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Topology.Sheaves.Presheaf
public import StacksFrontier.Topology.Sheaves.RingedSpace.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Trivial first order thickenings

A first order thickening `i : X ⟶ X'` of ringed spaces is *trivial* when `i` admits a
retraction, and a *trivialization* is a choice of such a retraction. Since `i` is a monomorphism
these are exactly the categorical notions `CategoryTheory.IsSplitMono` and
`CategoryTheory.SplitMono` applied to `i`.

This file relates a trivialization to a splitting of the structure-sheaf map, in both
directions.

* A splitting of the map on structure sheaves of a morphism of ringed spaces whose underlying
  map is a homeomorphism transports, along the inverse homeomorphism, to a morphism of ringed
  spaces in the opposite direction which retracts the original one.
* Conversely, a trivialization splits the quotient map of the thickening, and consequently
  identifies its structure sheaf with the trivial square-zero extension of the kernel ideal:
  `A'(U) ≅ A(U) × ker(π_U)` with product `(a, x) * (b, y) = (a * b, a • y + b • x)`,
  compatibly with all restriction maps.

## Main definitions

* `Deformation.RingThickening.quotientKernelMap`: the map on kernel ideals induced by a morphism
  of the indexing category.
* `Deformation.RingThickening.quotientKernelMul`: the infinitesimal term in the product of two
  elements of a split square-zero extension.
* `Deformation.RingThickening.PresheafTrivialSquareZeroEquiv`: a natural, restriction-compatible
  identification of a presheaf of rings with a trivial square-zero extension.
* `Deformation.RingThickening.retractionFromSplitting`: the ringed-space morphism whose
  underlying map is the inverse homeomorphism and whose map on structure sheaves is a given
  splitting.

## Main results

* `Deformation.RingThickening.splittingFromTrivialization`: a trivialization identifies a first
  order thickening with the trivial square-zero extension by its kernel ideal.
* `Deformation.RingThickening.retractionFromSplitting_comp`: the morphism induced by a splitting
  of the structure-sheaf map retracts the original morphism.

## References

* [Stacks Project, Tag 08L9](https://stacks.math.columbia.edu/tag/08L9)
-/

@[expose] public section


open AlgebraicGeometry CategoryTheory

universe u v w

add_to_stacks 08L9 "trivial_thickening_and_trivialization" CategoryTheory.SplitMono
add_to_stacks 08L9 "trivial_thickening_and_trivialization" CategoryTheory.IsSplitMono
add_to_sga "4 I 10.6" CategoryTheory.IsSplitMono

namespace Deformation.RingThickening

section Presheaf

variable {C : Type u} [Category.{v} C]
variable (A' A : C ⥤ CommRingCat.{w}) (quotient : A' ⟶ A)

private lemma retraction_section_app (A A' : C ⥤ CommRingCat.{w})
    (split : A ⟶ A') (π : SplitMono split)
    (U : C) (a : A.obj U) :
    (π.retraction.app U) (split.app U a) = a := by
  change ((split ≫ π.retraction).app U) a = a
  simp [π.id]

/-- The map on kernel ideals induced by a morphism in the indexing category. -/
def quotientKernelMap {U V : C} (f : U ⟶ V) :
    RingHom.ker (quotient.app U).hom → RingHom.ker (quotient.app V).hom := fun x ↦
  ⟨A'.map f x.1, by
    rw [RingHom.mem_ker]
    change (quotient.app V) (A'.map f x.1) = 0
    rw [← CommRingCat.comp_apply, quotient.naturality f, CommRingCat.comp_apply,
      RingHom.mem_ker.mp x.2, map_zero]⟩

/-- The infinitesimal term in the product of two elements of a split square-zero extension. -/
def quotientKernelMul (split : A ⟶ A') {U : C} (a b : A.obj U)
    (x y : RingHom.ker (quotient.app U).hom) : RingHom.ker (quotient.app U).hom :=
  ⟨split.app U a * y.1 + split.app U b * x.1, by
    rw [RingHom.mem_ker]
    simp only [map_add, map_mul]
    rw [RingHom.mem_ker.mp y.2, RingHom.mem_ker.mp x.2, mul_zero, mul_zero, zero_add]⟩

/-- A natural identification of a presheaf of rings with a trivial square-zero extension.

The product on `A(U) × ker(quotient(U))` is
`(a, x) * (b, y) = (a * b, a • y + b • x)`.  The fields below spell out both the ring laws
preserved by the equivalence and its compatibility with restriction maps. -/
structure PresheafTrivialSquareZeroEquiv (split : A ⟶ A') where
  /-- The equivalence on every object of the indexing category. -/
  equiv (U : C) : (A.obj U × RingHom.ker (quotient.app U).hom) ≃ A'.obj U
  /-- The equivalence is the canonical map `(a, x) ↦ section(a) + x`. -/
  apply_eq (U : C) (a : A.obj U) (x : RingHom.ker (quotient.app U).hom) :
    equiv U (a, x) = split.app U a + x.1
  /-- The canonical equivalence preserves zero. -/
  map_zero (U : C) : equiv U (0, 0) = 0
  /-- The canonical equivalence preserves one. -/
  map_one (U : C) : equiv U (1, 0) = 1
  /-- The canonical equivalence preserves addition. -/
  map_add (U : C) (a b : A.obj U) (x y : RingHom.ker (quotient.app U).hom) :
    equiv U (a, x) + equiv U (b, y) = equiv U (a + b, x + y)
  /-- The canonical equivalence preserves the trivial square-zero multiplication. -/
  map_mul (U : C) (a b : A.obj U) (x y : RingHom.ker (quotient.app U).hom) :
    equiv U (a, x) * equiv U (b, y) =
      equiv U (a * b, quotientKernelMul A' A quotient split a b x y)
  /-- The equivalences commute with all restriction maps. -/
  naturality {U V : C} (f : U ⟶ V)
      (z : A.obj U × RingHom.ker (quotient.app U).hom) :
    A'.map f (equiv U z) =
      equiv V (A.map f z.1, quotientKernelMap A' A quotient f z.2)
  /-- The kernel ideal is square-zero on every object. -/
  kernel_sq (U : C) : RingHom.ker (quotient.app U).hom ^ 2 = ⊥

/-- A trivialization identifies a first order thickening with the trivial square-zero extension
by its kernel ideal. -/
@[stacks 08L9 "splitting_from_trivialization", ega "0 18.2.3" "special case"]
noncomputable def splittingFromTrivialization
    (split : A ⟶ A') (π : SplitMono split)
    (h_sq : ∀ U : C, RingHom.ker (π.retraction.app U).hom ^ 2 = ⊥) :
  PresheafTrivialSquareZeroEquiv A' A π.retraction split :=
  { equiv := fun U =>
      { toFun := fun z => split.app U z.1 + z.2.1
        invFun := fun y =>
          (π.retraction.app U y,
            ⟨y - split.app U (π.retraction.app U y), by
              rw [RingHom.mem_ker]; simp [retraction_section_app A A' split π U]⟩)
        left_inv := by
          rintro ⟨a, x⟩
          apply Prod.ext
          · simp [RingHom.mem_ker.mp x.2, retraction_section_app A A' split π U]
          · apply Subtype.ext
            simp [RingHom.mem_ker.mp x.2, retraction_section_app A A' split π U]
        right_inv := by intro y; dsimp; abel }
    apply_eq _ _ _ := rfl
    map_zero := by intro U; simp
    map_one := by intro U; simp
    map_add := by
      intro U a b x y
      change (split.app U a + x.1) + (split.app U b + y.1) =
        split.app U (a + b) + (x.1 + y.1)
      rw [map_add]; abel
    map_mul := by
      intro U a b x y
      have hxy : x.1 * y.1 = 0 := by
        have hmem : x.1 * y.1 ∈ RingHom.ker (π.retraction.app U).hom ^ 2 := by
          simpa only [pow_two] using Ideal.mul_mem_mul x.2 y.2
        simpa [h_sq U] using hmem
      change (split.app U a + x.1) * (split.app U b + y.1) =
        split.app U (a * b) +
          (split.app U a * y.1 + split.app U b * x.1)
      rw [map_mul, mul_add, add_mul, add_mul, hxy]; ring
    naturality := by
      intro U V f z
      change A'.map f (split.app U z.1 + z.2.1) =
        split.app V (A.map f z.1) + A'.map f z.2.1
      rw [map_add, ← CommRingCat.comp_apply, ← split.naturality f,
        CommRingCat.comp_apply]
    kernel_sq := h_sq }

end Presheaf

/-- The section of the structure-sheaf map, transported along the inverse homeomorphism of the
base map, defines a morphism of ringed spaces in the opposite direction. -/
@[stacks 08L9 "trivialization_from_splitting"]
noncomputable abbrev retractionFromSplitting {X X' : RingedSpace.{u, v}}
    (i : X ⟶ X') [IsIso i.hom.base]
    (splitting : SplitEpi i.hom.c) : X' ⟶ X :=
  ⟨⟨(asIso i.hom.base).inv,
    TopCat.Presheaf.toPushforwardOfIso (asIso i.hom.base) splitting.section_⟩⟩

/-- The morphism induced by a splitting of the structure-sheaf map retracts the original
morphism. -/
@[stacks 08L9 "trivialization_from_splitting"]
theorem retractionFromSplitting_comp {X X' : RingedSpace.{u, v}}
    (i : X ⟶ X') [IsIso i.hom.base]
    (splitting : SplitEpi i.hom.c) :
    i ≫ retractionFromSplitting i splitting = 𝟙 X := by
  refine SheafedSpace.ext _ _ ?_ ?_
  · simp
  · apply NatTrans.ext; funext U
    have h (V) : splitting.section_.app V ≫ i.hom.c.app V = 𝟙 _ :=
      congrArg (fun f => f.app V) splitting.id
    rw [NatTrans.comp_app, SheafedSpace.comp_hom_c_app,
      TopCat.Presheaf.toPushforwardOfIso_app, Category.assoc, h]
    simp only [SheafedSpace.id_hom, PresheafedSpace.id_base, Functor.comp_obj, Functor.op_obj,
      SheafedSpace.comp_hom_base, TopCat.Presheaf.pushforward_obj_obj,
      TopologicalSpace.Opens.map_comp_obj, Functor.whiskerRight_app,
      PresheafedSpace.id_c_app, CategoryTheory.Functor.map_id]
    exact (X.presheaf.map_comp _ _).symm.trans
      ((congrArg X.presheaf.map (Subsingleton.elim _ (CategoryStruct.id U))).trans
        (X.presheaf.map_id U))

add_to_stacks 08LA "the splitting determined by a trivialization"
  Deformation.RingThickening.splittingFromTrivialization
add_to_stacks 08LA "the split square-zero extension it lands in"
  Deformation.RingThickening.PresheafTrivialSquareZeroEquiv

end Deformation.RingThickening

end
