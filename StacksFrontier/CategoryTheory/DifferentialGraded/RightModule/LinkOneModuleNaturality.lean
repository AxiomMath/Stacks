module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.CochainComplexFunctor
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.LinkApplyLemmas

/-!
# The first link of Tag 09LK is natural in the module variable

The first link of [Stacks, Tag 09LK],
`DGCategory.RightModule.homShiftEquivGradedCohomology`, is a bijection

`Hom_{K(Mod^dg(C))}(h_X, M⟦n⟧) ≃ H^n(M X)`

for each fixed `M`, and `DGCategory.RightModule.homShiftEquivGradedCohomology_mk` computes it:
the homotopy class of a cocycle goes to the class of its evaluation at the identity of `X`. What
that computation does not say is how the bijection reacts to a morphism `u : M ⟶ N` of
`K(Mod^dg(C))`, which is the form in which the `unit_app_id` clause of
`CochainComplex.derivedHomLiftIdentificationOfNaturality` meets it: there the morphism is the
unit `η` of the reflector of steps 1 and 2, and the cohomology class produced by the comparison
`β` differs from the class of a cocycle of `Hom^•(K, Y)` exactly by the map that `η` induces on
cohomology.

This file supplies that naturality. Both sides of the bijection are functorial in the module
variable — composition with `u⟦n⟧` on the left, the map induced on the explicit cohomology of the
complex `M X` on the right — and the link intertwines them.

## The induced map on the explicit cohomology

`DGCategory.RightModule.gradedCohomology` is cocycles modulo coboundaries, so the map induced by
a closed degree-zero homogeneous morphism is elementary: the morphism carries cocycles to
cocycles because it commutes with the differentials
(`DGCategory.RightModule.app_d_of_closed`), and coboundaries to coboundaries because it does so
in every degree. No homology machinery is involved, and the induced map computes on the class of
a cocycle by construction.

## Main definitions

* `DGCategory.RightModule.gradedCocyclesMapOf` and
  `DGCategory.RightModule.gradedCohomologyMapOf`: the maps induced on the degree-`n` cocycles
  and on the degree-`n` explicit cohomology of `M X` by a closed degree-zero homogeneous
  morphism `M ⟶ N`.
* `DGCategory.RightModule.shiftCocycle`: the shift of such a morphism, as a morphism
  `M⟦n⟧ ⟶ N⟦n⟧`.

## Main results

* `DGCategory.RightModule.homKEquivGradedCohomology_comp`: the differential graded Yoneda lemma
  in degree zero is natural in the module.
* `DGCategory.RightModule.gradedCohomologyShiftEquiv_gradedCohomologyMapOf`: the comparison of
  the cohomology of a shift with the shifted cohomology is natural in the module.
* `DGCategory.RightModule.homShiftEquivGradedCohomology_comp`: **the first link is natural in
  the module variable.** On a morphism `g ≫ u⟦n⟧` the link is the map induced by `u` on the
  explicit cohomology, applied to the link of `g`.
* `DGCategory.RightModule.homShiftEquivEvaluationGradedCohomology_comp`: the same statement for
  the spelling of the link that the chain of [Stacks, Tag 09LK] uses, with the complex written
  as `ev_X M`.

## Implementation notes

The naturality is proved through the two factors of
`DGCategory.RightModule.homShiftEquivGradedCohomology` rather than on its value: the shift factor
`DGCategory.RightModule.gradedCohomologyShiftEquiv` carries a degree equation `i + n = j` which
has to be substituted before its value is an equality of elements of one module, and doing that
once inside the proof of
`DGCategory.RightModule.gradedCohomologyShiftEquiv_gradedCohomologyMapOf` keeps every other step
free of transports.

The Koszul sign `(-1)^(n p)` of `DGCategory.RightModule.shiftMap` is `1` here because the
morphism being shifted has degree `p = 0`; no sign survives, and that is the only place where the
shift of a morphism enters.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK);
  [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC), the identification of a cohomology class
  of a Hom complex with a morphism of the homotopy category.
-/

@[expose] public section

namespace DGCategory

universe v u r

open CategoryTheory

namespace RightModule

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

attribute [local implicit_reducible] DGCategory.K

variable {M N : (rightModuleCategory.{v} C).K}

/-! ### The map induced on the explicit cohomology -/

/-- **The map induced on the degree-`n` cocycles of `M X` by a morphism of modules.** A closed
degree-zero homogeneous morphism commutes with the differentials, by
`DGCategory.RightModule.app_d_of_closed`, so it carries cocycles to cocycles. -/
def gradedCocyclesMapOf (ψ : (rightModuleCategory.{v} C).Cocycle M N) (X : C.Obj) (n : ℤ) :
    gradedCocycles M X n →ₗ[R] gradedCocycles N X n :=
  LinearMap.codRestrict _
    ((ψ.1.1 ⟨X, n, n, add_zero n⟩).comp (gradedCocycles M X n).subtype)
    fun a => by
      rw [mem_gradedCocycles]
      change N.d (rfl : n + 1 = n + 1) (app ψ.1 (add_zero n) (a : M.obj X n)) = 0
      rw [app_d_of_closed ψ.2 (rfl : n + 1 = n + 1) (a : M.obj X n),
        show M.d (rfl : n + 1 = n + 1) (a : M.obj X n) = 0 from mem_gradedCocycles.1 a.2,
        app_zero]

/-- The underlying element of the image of a cocycle under `gradedCocyclesMapOf ψ X n` is the
image of the underlying element under `ψ`. -/
@[simp] theorem gradedCocyclesMapOf_val (ψ : (rightModuleCategory.{v} C).Cocycle M N) (X : C.Obj)
    (n : ℤ) (a : gradedCocycles M X n) :
    (gradedCocyclesMapOf ψ X n a : N.obj X n) = app ψ.1 (add_zero n) (a : M.obj X n) := rfl

/-- The induced map on cocycles commutes with the differential into the cocycles: both sides are
the morphism applied after the differential. -/
theorem gradedCocyclesMapOf_comp_gradedToCocycles (ψ : (rightModuleCategory.{v} C).Cocycle M N)
    (X : C.Obj) {i n : ℤ} (h : i + 1 = n) :
    (gradedCocyclesMapOf ψ X n).comp (gradedToCocycles M X h) =
      (gradedToCocycles N X h).comp (ψ.1.1 ⟨X, i, i, add_zero i⟩) :=
  LinearMap.ext fun a => Subtype.ext (app_d_of_closed ψ.2 h a).symm

/-- The induced map carries the degree-`n` coboundaries of `M X` into those of `N X`. -/
theorem gradedBoundaries_le_comap_gradedCocyclesMapOf
    (ψ : (rightModuleCategory.{v} C).Cocycle M N) (X : C.Obj) (n : ℤ) :
    gradedBoundaries M X n ≤
      (gradedBoundaries N X n).comap (gradedCocyclesMapOf ψ X n) := by
  have h : n - 1 + 1 = n := by omega
  rintro _ ⟨a, rfl⟩
  refine Submodule.mem_comap.2 ?_
  rw [gradedBoundaries_eq_range N X h]
  exact ⟨app ψ.1 (add_zero (n - 1)) a,
    (LinearMap.congr_fun (gradedCocyclesMapOf_comp_gradedToCocycles ψ X h) a).symm⟩

/-- **The map induced on the degree-`n` explicit cohomology of `M X` by a morphism of
modules.** -/
def gradedCohomologyMapOf (ψ : (rightModuleCategory.{v} C).Cocycle M N) (X : C.Obj) (n : ℤ) :
    gradedCohomology M X n →ₗ[R] gradedCohomology N X n :=
  Submodule.mapQ _ _ (gradedCocyclesMapOf ψ X n)
    (gradedBoundaries_le_comap_gradedCocyclesMapOf ψ X n)

/-- The induced map takes the class of a cocycle to the class of its image. -/
@[simp] theorem gradedCohomologyMapOf_mk (ψ : (rightModuleCategory.{v} C).Cocycle M N)
    (X : C.Obj) (n : ℤ) (a : gradedCocycles M X n) :
    gradedCohomologyMapOf ψ X n (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (gradedCocyclesMapOf ψ X n a) :=
  rfl

/-! ### The shift of a morphism of modules -/

/-- **The shift of a closed degree-zero homogeneous morphism**, as a morphism `M⟦n⟧ ⟶ N⟦n⟧` of
`Comp(Mod^dg(C))`: the image of the morphism under the shift functor of differential graded
categories. Its Koszul sign is `(-1)^(n·0) = 1`. -/
def shiftCocycle (ψ : (rightModuleCategory.{v} C).Cocycle M N) (n : ℤ) :
    (rightModuleCategory.{v} C).Cocycle (shift M n) (shift N n) :=
  (rightModuleShiftFunctor.{v} C n).mapCocycle ψ

/-- The underlying morphism of `shiftCocycle ψ n` is the shift `shiftMap ψ.1 n`. -/
@[simp] theorem shiftCocycle_val (ψ : (rightModuleCategory.{v} C).Cocycle M N) (n : ℤ) :
    (shiftCocycle ψ n).1 = shiftMap ψ.1 n := rfl

/-- The shift functor of `K(Mod^dg(C))` carries the homotopy class of a closed degree-zero
morphism to the class of its shift. -/
theorem shiftFunctor_map_mk (ψ : (rightModuleCategory.{v} C).Cocycle M N) (n : ℤ) :
    (shiftFunctor (rightModuleCategory.{v} C).K n).map (Quotient.mk _ ψ : M ⟶ N) =
      Quotient.mk _ (shiftCocycle ψ n) := rfl

/-! ### Naturality of the two factors of the first link -/

/-- **The differential graded Yoneda lemma in degree zero is natural in the module.** For
`u : M ⟶ N` a morphism of `K(Mod^dg(C))` and `g : h_X ⟶ M`, the cohomology class that
`DGCategory.RightModule.homKEquivGradedCohomology` assigns to `g ≫ u` is the image under the map
induced by `u` of the class it assigns to `g`.

Both sides are evaluation at the identity of `X`, and evaluating a composite at the identity is
applying the second factor to the evaluation of the first — all three degrees being zero, so that
no reindexing occurs. -/
theorem homKEquivGradedCohomology_comp (ψ : (rightModuleCategory.{v} C).Cocycle M N) (X : C.Obj)
    (g : yonedaObjK X ⟶ M) :
    homKEquivGradedCohomology N X (g ≫ (Quotient.mk _ ψ : M ⟶ N)) =
      gradedCohomologyMapOf ψ X 0 (homKEquivGradedCohomology M X g) :=
  Quotient.inductionOn g fun f =>
    (homKEquivGradedCohomology_mk N X ((rightModuleCategory.{v} C).compCocycle ψ f)).trans
      ((congrArg Submodule.Quotient.mk
            (Subtype.ext (app_homComp_zero ψ.1 f.1 (by omega) 0 (zero_add 0) (C.id X)) :
              yonedaCocyclesEquiv N X 0 ((rightModuleCategory.{v} C).compCocycle ψ f) =
                gradedCocyclesMapOf ψ X 0 (yonedaCocyclesEquiv M X 0 f))).trans
        (congrArg (gradedCohomologyMapOf ψ X 0)
          (homKEquivGradedCohomology_mk M X f)).symm)

/-- **The comparison of the cohomology of a shift with the shifted cohomology is natural in the
module.** The map on cohomology induced by the shift `u⟦n⟧` of a morphism corresponds, under
`DGCategory.RightModule.gradedCohomologyShiftEquiv`, to the map induced by `u` itself.

The shift of a closed degree-zero homogeneous morphism carries the Koszul sign `(-1)^(n·0) = 1`,
so on underlying elements both sides are the same application of the morphism; the degree
equation is substituted first. -/
theorem gradedCohomologyShiftEquiv_gradedCohomologyMapOf
    (ψ : (rightModuleCategory.{v} C).Cocycle M N) (n : ℤ) (X : C.Obj) {i j : ℤ}
    (h : i + n = j) (c : gradedCohomology (shift M n) X i) :
    gradedCohomologyShiftEquiv N n X h (gradedCohomologyMapOf (shiftCocycle ψ n) X i c) =
      gradedCohomologyMapOf ψ X j (gradedCohomologyShiftEquiv M n X h c) := by
  subst h
  induction c using Submodule.Quotient.induction_on with
  | H a =>
    rw [gradedCohomologyMapOf_mk, gradedCohomologyShiftEquiv_mk, gradedCohomologyShiftEquiv_mk,
      gradedCohomologyMapOf_mk]
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    rw [gradedCocyclesShiftEquiv'_rfl, gradedCocyclesShiftEquiv_val, gradedCocyclesMapOf_val,
      gradedCocyclesMapOf_val, gradedCocyclesShiftEquiv'_rfl, gradedCocyclesShiftEquiv_val,
      shiftCocycle_val, app_shiftMap ψ.1 n (add_zero i) (a : (shift M n).obj X i), mul_zero,
      Int.natAbs_zero, pow_zero, one_smul]

/-! ### The first link, natural in the module variable -/

/-- **The first link of [Stacks, Tag 09LK] is natural in the module variable.** For
`u : M ⟶ N` a morphism of `K(Mod^dg(C))` and `g : h_X ⟶ M⟦n⟧`, the degree-`n` cohomology class
that `DGCategory.RightModule.homShiftEquivGradedCohomology` assigns to `g ≫ u⟦n⟧` is the image
under the map induced by `u` of the class it assigns to `g`.

This is the compatibility that the `unit_app_id` clause of
`CochainComplex.derivedHomLiftIdentificationOfNaturality` consumes on the side of the chain: the
class the chain starts from is the class of a cocycle of `Hom^•(K, Y)` pushed along the unit of
the reflector, and this lemma is what moves the unit from inside the link to the map it induces
on cohomology. -/
theorem homShiftEquivGradedCohomology_comp (ψ : (rightModuleCategory.{v} C).Cocycle M N)
    (X : C.Obj) (n : ℤ) (g : yonedaObjK X ⟶ M⟦n⟧) :
    homShiftEquivGradedCohomology N X n
        (g ≫ (shiftFunctor (rightModuleCategory.{v} C).K n).map (Quotient.mk _ ψ : M ⟶ N)) =
      gradedCohomologyMapOf ψ X n (homShiftEquivGradedCohomology M X n g) :=
  (congrArg (gradedCohomologyShiftEquiv N n X (zero_add n))
      (homKEquivGradedCohomology_comp (shiftCocycle ψ n) X g)).trans
    (gradedCohomologyShiftEquiv_gradedCohomologyMapOf ψ n X (zero_add n)
      (homKEquivGradedCohomology (shift M n) X g))

/-- **The first link in the form the chain uses is natural in the module variable.** The same
statement as `DGCategory.RightModule.homShiftEquivGradedCohomology_comp` read through
`DGCategory.RightModule.gradedCohomology_evaluation`, which is how
`DGCategory.RightModule.chainEquivReflectorEvaluation` spells the source of the chain. -/
theorem homShiftEquivEvaluationGradedCohomology_comp
    (ψ : (rightModuleCategory.{v} C).Cocycle M N) (K : C.Obj)
    (e : (endDGCategory C K).Obj) (n : ℤ) (g : yonedaObjK K ⟶ M⟦n⟧) :
    homShiftEquivEvaluationGradedCohomology N K e n
        (g ≫ (shiftFunctor (rightModuleCategory.{v} C).K n).map (Quotient.mk _ ψ : M ⟶ N)) =
      gradedCohomologyMapOf ψ K n
        (homShiftEquivEvaluationGradedCohomology M K e n g) :=
  homShiftEquivGradedCohomology_comp ψ K n g

end RightModule

end DGCategory

end
