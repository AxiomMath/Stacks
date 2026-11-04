module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeMateInverse

/-!
# The keystone with [stacks 0E1W] uncurried

`Dualizing.tensorBaseChangeMor_eq_iff_natIso_inv` puts the component of [stacks 0E1W] on the side
whose chain-level value inverts nothing, at the price of a `homEquiv` of [stacks 0A63] on the
right-hand side: the equation it states is

`(η_X ≫ (transpose of μ')|_R) ≫ 0E1W⁻¹_{Y, F (X ⊗ᴸ_R Y)} = (transpose of η_{X ⊗ᴸ_R Y})`.

Every chain-level value of the [stacks 0E1W] factor is stated *uncurried*, though.
`Stacks.DerivedHom.BaseChangeIso.uncurry_homComplexChangeOfRingsMap` values the [stacks 0A63]
uncurrying of the chain-level Hom-side map, not the map;
`Stacks.DerivedHom.BaseChangeIso.homEquiv_Q_map_homComplexChangeOfRingsMap` and
`Stacks.DerivedHom.BaseChangeIso.homEquiv_Q_map_comp_eq_of_uncurry_eq` localize that uncurried
form; and the [stacks 068I] side is a morphism out of a tensor product to begin with.  So the
curried shape of the equation is the wrong one on both sides.

This file transposes the whole equation over [stacks 0A63] over `R`.  Since that transposition is
a bijection, nothing is weakened, and two things come out of it:

* the right-hand side loses its `homEquiv` and becomes the **bare unit** of [stacks 0GMT] at
  `X ⊗ᴸ_R Y`, which
  `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq_of_kFlat`
  values outright at a K-flat complex;
* the component of [stacks 0E1W] occurs only through its own [stacks 0A63] transpose

  `ψ_{Y, M} : (RHom_A(F Y, M))|_R ⊗ᴸ_R Y ⟶ M|_R`,

  which is the uncurried direction, and it occurs as a single trailing factor, the rest of the
  left-hand side being one morphism of the tensor bifunctor.

The resulting equation has three factors: the tensor bifunctor applied to the pair
`(η_X ≫ (transpose of μ')|_R, 𝟙_Y)`, then `ψ`.  Both of the first two are determinate at a K-flat
pair — the unit by the reference above and the transpose of the [stacks 068I] candidate by
`Dualizing.tensorBaseChangeMor_comp_eq_q_obj` — so the one remaining unknown is `ψ`.

**What is not done here.**  Neither the keystone nor `Dualizing.TensorComparisonCompatibility` is
proved, `Dualizing.KFlatAlgebraActionEq` stays open and no tag loses its conditional caveat.
What changes is the shape in which the one remaining unknown is read: uncurried, as its
chain-level values are stated.

## Main results

* `Dualizing.eq_derivedTensorBaseChange_iff_tensorTranspose` — a morphism is the lax monoidal
  structure map exactly when the uncurried equation holds, with the **inverse** component of
  [stacks 0E1W] entering through its [stacks 0A63] transpose and the right-hand side the bare
  unit of [stacks 0GMT].
* `Dualizing.tensorBaseChangeMor_eq_iff_tensorTranspose` — the same at the [stacks 068I]
  candidate, i.e. the keystone itself.
* `Dualizing.tensorBaseChangeMor_eq_of_kFlat_tensorTranspose` — the keystone in that shape at
  pairs of localizations of K-flat complexes implies it everywhere, so this is the form in which
  it has to be checked.

## Implementation notes

The transposition is `CategoryTheory.DerivedHomAdjunction.homEquiv_naturality_left`, the
naturality of the Hom equivalence of [stacks 0A63] in its source variable, which turns the
composite `u ≫ ψ'` into `tensor (u, 𝟙) ≫ (transpose of ψ')`; the two `≫` of the left-hand side of
`Dualizing.tensorBaseChangeMor_eq_iff_natIso_inv` are already bracketed that way, so the field
applies to it with no reassociation.

It is applied in term position rather than by `rw`.  The source of a component of [stacks 0E1W] is
spelled as the value of a composite functor and is only definitionally the restriction of an
internal Hom, and the pair-morphism arguments of the tensor bifunctor are elaborated at the
product category's `Quiver.Hom`; keyed matching fires on neither, while definitional unification
crosses both.  This is the obstruction recorded in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeStrong`.

No `@[stacks]` attribute is placed here: the obligation is still open, so nothing in this file
covers a tag.

## What the remaining obligation now is

The three factors of the equation are all valued, and it is worth saying exactly where, because
two earlier notes in this chapter described the residue wrongly.

* `η`, the unit of [stacks 0GMT], at a pair of localizations of K-flat complexes: the object it
  sits at is `X ⊗ᴸ_R Y`, which is *not* a class, so
  `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq_of_kFlat`
  does not apply to it directly.  `…_unit_app_eq_of_model` does, at any object whatever, with the
  presentation supplied by `CochainComplex.DerivedTensor.derivedTensor_comparison` at the K-flat
  second argument.
* `μ'`, the [stacks 068I] candidate, by `Dualizing.tensorBaseChangeMor_comp_eq_q_obj`.
* `ψ`, the [stacks 0A63] transpose of the inverse component of [stacks 0E1W], by
  `Stacks.DerivedHom.BaseChange.
  homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_presentations`, in which no unit or counit
  of either scalar equivalence survives.

What that leaves is **not** a comparison in `D(R)`.  `ψ`'s value is
`E.inverse.map BIG ≫ E.unitIso.inv.app (U.obj M)` for `E` the scalar equivalence of
[stacks 0E1W], and the other factor of the left-hand side is `E.inverse` of a morphism too:
`(derivedHomAdjunctionOverRing R).tensor` *is*
`StacksDraft.DerivedHom.DerivedHomAdjunction.transportTensor` of the fixed-universe tensor, and
`…transportTensor_map` says on morphisms it is `E.inverse` of the fixed-universe tensor's.  So
the whole left-hand side is one `E.inverse.map` of a composite of `D(ULift R)` followed by one
inverse unit, and by `CategoryTheory.Equivalence.inverse_map_comp_unitIso_inv_eq_iff` the
equation is equivalent -- `E.functor` being faithful, so nothing is weakened -- to an equation
of `D(ULift R)`:

`Model.tensor.map (E.functor.map (η_X ≫ (transpose of μ')|_R) ≫ δ_* ≫ ε, 𝟙) ≫ Model.homEquiv (…)`
`  = E.counitIso.inv.app (Model.tensor.obj (E.functor X, E.functor Y)) ≫ E.functor.map η_{X ⊗ Y}`

with `Model.homEquiv` the *fixed-universe* tensor--Hom transpose.  That is the form in which the
comparison has to be made, because `Model.tensor`, `Model.homEquiv` and
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` -- the one chain map the [stacks 068I]
side carries, by `CochainComplex.DerivedTensor.
IsTensorBaseChangeIso.hom_eq_extendScalarsMonoidalIso_hom` -- all live in `D(ULift R)` and
`D(ULift A)`, while the two sides as stated above live in `D(R)`.

The factor that the comparison has still to get past is therefore not a
`CategoryTheory.Functor.mapDerivedCategoryFactors` component but `Model.homEquiv`, the
fixed-universe transpose, applied to a three-factor composite.  Unwinding it means evaluating the
transpose of `DerivedInternalHom` at a composite, which
`StacksDraft.DerivedHom.DerivedInternalHom.Model.homEquiv_map_uncurry` and
`…homEquiv_composition` do only at a class in each variable; the three objects here are
`V.obj (RHom_{ULift A}(…))`, `E.functor.obj Y` and `E.functor.obj (U.obj M)`, and only the second
is presented as one.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars
open CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

include hF in
/-- **A morphism is the lax monoidal structure map of derived base change exactly when the
uncurried equation holds.**

This is `Dualizing.eq_derivedTensorBaseChange_iff_natIso_inv` transposed over the tensor--Hom
adjunction of [stacks 0A63] over `R`.  The right-hand side becomes the bare unit of [stacks 0GMT]
at `X ⊗ᴸ_R Y`, and the component of [stacks 0E1W] occurs only through its own [stacks 0A63]
transpose

`ψ_{Y, M} : (RHom_A(F Y, M))|_R ⊗ᴸ_R Y ⟶ M|_R`,

which is the direction in which every chain-level value of that factor is stated.  The
transposition is a bijection, so this says exactly what the curried form says. -/
theorem eq_derivedTensorBaseChange_iff_tensorTranspose
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (g : (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
        (F.obj X, F.obj Y) ⟶
      F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
        (X, Y))) :
    g = derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ↔
      (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
            (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X ≫
                (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
                  (((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                      max uR uA uM + 1} A).homEquiv (F.obj X) (F.obj Y)
                      (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                        max uR uA uM + 1} R).tensor.obj (X, Y)))).symm g),
              𝟙 Y) :
              ((X, Y) : DerivedCategory (ModuleCat.{max uR uA uM} R) ×
                  DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
                ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
                    ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                      max uR uA uM + 1} A).hom.obj (Opposite.op (F.obj Y),
                        F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                          max uR uA uM + 1} R).tensor.obj (X, Y)))),
                  Y)) ≫
          (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
            ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
              ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                max uR uA uM + 1} A).hom.obj (Opposite.op (F.obj Y),
                  F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                    max uR uA uM + 1} R).tensor.obj (X, Y)))))
            Y
            ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
              (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                max uR uA uM + 1} R).tensor.obj (X, Y))))
            ((Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
                comparison).inv.app
              (Opposite.op Y, F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                max uR uA uM + 1} R).tensor.obj (X, Y)))) =
        (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
          ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensor.obj (X, Y)) := by
  rw [eq_derivedTensorBaseChange_iff_natIso_inv.{uR, uA, uM} f F comparison X Y g]
  exact (Equiv.eq_symm_apply ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
    max uR uA uM + 1} R).homEquiv X Y _).toEquiv).trans
      (Iff.of_eq (congrArg (· = _) ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
        max uR uA uM + 1} R).homEquiv_naturality_left _ _)))

variable (D : TotalDerivedExtensionScalars.{uR, max uR uA uM, uA, max uR uA uM + 1,
  max uR uA uM + 1} f)

include hF in
/-- **The keystone, uncurried.**  The [stacks 068I] morphism `Dualizing.tensorBaseChangeMor` is
the lax monoidal structure map of derived base change exactly when the tensor bifunctor applied to
the pair consisting of the unit of [stacks 0GMT] followed by the restricted transpose of that
morphism and the identity of `Y`, followed by the [stacks 0A63] transpose of the inverse component
of [stacks 0E1W], is the unit of [stacks 0GMT] at `X ⊗ᴸ_R Y`.

This is `Dualizing.eq_derivedTensorBaseChange_iff_tensorTranspose` at the [stacks 068I] candidate,
so it is the same equation as `Dualizing.tensorBaseChangeMor_eq_iff`,
`Dualizing.tensorBaseChangeMor_eq_iff_section_comp` and
`Dualizing.tensorBaseChangeMor_eq_iff_natIso_inv`; what it adds is that no `homEquiv` of
[stacks 0A63] is left on the right-hand side and that the one occurrence of [stacks 0E1W] is
uncurried. -/
theorem tensorBaseChangeMor_eq_iff_tensorTranspose
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y =
        derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ↔
      (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
            (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X ≫
                (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
                  (((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                      max uR uA uM + 1} A).homEquiv (F.obj X) (F.obj Y)
                      (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                        max uR uA uM + 1} R).tensor.obj (X, Y)))).symm
                    (tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y)),
              𝟙 Y) :
              ((X, Y) : DerivedCategory (ModuleCat.{max uR uA uM} R) ×
                  DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
                ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
                    ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                      max uR uA uM + 1} A).hom.obj (Opposite.op (F.obj Y),
                        F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                          max uR uA uM + 1} R).tensor.obj (X, Y)))),
                  Y)) ≫
          (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
            ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
              ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                max uR uA uM + 1} A).hom.obj (Opposite.op (F.obj Y),
                  F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                    max uR uA uM + 1} R).tensor.obj (X, Y)))))
            Y
            ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
              (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                max uR uA uM + 1} R).tensor.obj (X, Y))))
            ((Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
                comparison).inv.app
              (Opposite.op Y, F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                max uR uA uM + 1} R).tensor.obj (X, Y)))) =
        (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
          ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensor.obj (X, Y)) :=
  eq_derivedTensorBaseChange_iff_tensorTranspose.{uR, uA, uM} f F comparison X Y
    (tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y)

include hF in
/-- **The uncurried keystone has to be checked only at pairs of K-flat complexes.**  Granted the
uncurried equation at every pair of localizations of K-flat complexes, the [stacks 068I] morphism
is the lax monoidal structure map at every pair of objects of `D(R)`.

This is `Dualizing.tensorBaseChangeMor_eq_of_kFlat` with its hypothesis read through
`Dualizing.tensorBaseChangeMor_eq_iff_tensorTranspose`; it is the exact shape of the chapter's
remaining obligation, every factor of whose two determinate sides is named by
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq_of_kFlat`
and `Dualizing.tensorBaseChangeMor_comp_eq_q_obj`. -/
theorem tensorBaseChangeMor_eq_of_kFlat_tensorTranspose
    (h : ∀ K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ, K.KFlat → L.KFlat →
      (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
            (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
                  (DerivedCategory.Q.obj K) ≫
                (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
                  (((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                      max uR uA uM + 1} A).homEquiv (F.obj (DerivedCategory.Q.obj K))
                      (F.obj (DerivedCategory.Q.obj L))
                      (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                        max uR uA uM + 1} R).tensor.obj (DerivedCategory.Q.obj K,
                          DerivedCategory.Q.obj L)))).symm
                    (tensorBaseChangeMor.{uR, uA, uM} f F comparison D (DerivedCategory.Q.obj K)
                      (DerivedCategory.Q.obj L))),
              𝟙 (DerivedCategory.Q.obj L)) :
              ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :
                  DerivedCategory (ModuleCat.{max uR uA uM} R) ×
                    DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
                ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
                    ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                      max uR uA uM + 1} A).hom.obj
                      (Opposite.op (F.obj (DerivedCategory.Q.obj L)),
                        F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                          max uR uA uM + 1} R).tensor.obj (DerivedCategory.Q.obj K,
                            DerivedCategory.Q.obj L)))),
                  DerivedCategory.Q.obj L)) ≫
          (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
            ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
              ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                max uR uA uM + 1} A).hom.obj (Opposite.op (F.obj (DerivedCategory.Q.obj L)),
                  F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                    max uR uA uM + 1} R).tensor.obj (DerivedCategory.Q.obj K,
                      DerivedCategory.Q.obj L)))))
            (DerivedCategory.Q.obj L)
            ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
              (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                max uR uA uM + 1} R).tensor.obj (DerivedCategory.Q.obj K,
                  DerivedCategory.Q.obj L))))
            ((Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
                comparison).inv.app
              (Opposite.op (DerivedCategory.Q.obj L),
                F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                  max uR uA uM + 1} R).tensor.obj (DerivedCategory.Q.obj K,
                    DerivedCategory.Q.obj L)))) =
        (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
          ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)))
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y =
      derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y :=
  tensorBaseChangeMor_eq_of_kFlat.{uR, uA, uM} f F comparison D
    (fun K L hK hL =>
      (tensorBaseChangeMor_eq_iff_tensorTranspose.{uR, uA, uM} f F comparison D
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).2 (h K L hK hL)) X Y

end Dualizing

end
