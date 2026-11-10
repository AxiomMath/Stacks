module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonReduction

/-!
# The tensor-comparison obligation as one equation, with no transpose and no [stacks 0E1W]

`Dualizing.TensorComparisonCompatibility` is the equation

`μ_{X, A} ≫ tensorComparisonOfIso X = 𝟙_{X ⊗ᴸ_R R'} ⊗ derivedBaseChangeAlgebraIso`,

and it is the only remaining input of `Dualizing.KFlatAlgebraActionEq`.  Two readings of it have
been recorded in this directory, each paying for the absence of one factor with the presence of
another: `Dualizing.tensorComparisonCompatibility_of_homEquiv` removes the lax monoidal structure
map `μ` and the morphism of [stacks 0E1X] at the cost of two transposes and one component of
[stacks 0E1W], and `Dualizing.tensorComparisonCompatibility_rhs_eq_section` then removes that
component again at the cost of the inverse `Dualizing.derivedTensorBaseChangeSection` of `μ`.

Neither cost has to be paid.  `Dualizing.isIso_derivedTensorBaseChange` proves `μ` invertible
*unconditionally*, with `Dualizing.derivedTensorBaseChangeSection` as its two-sided inverse, and
`Stacks.CategoryTheory.BaseChange.isIso_tensorComparisonOfIso` proves the comparison across the
square invertible because each of its four factors is.  So the obligation may be divided by either
factor, and this file records the two resulting readings:

* by `μ`: the obligation is the identity `tensorComparisonOfIso X = ν_{X, A} ≫ (𝟙 ⊗ θ)`, in which
  no transpose, no unit of [stacks 0GMT], no `homEquiv` of [stacks 0A63], no component of
  [stacks 0E1W] and no morphism of [stacks 0E1X] occurs;
* by the comparison: the obligation is a *determinate value* for `μ`, namely
  `μ_{X, A} = (𝟙 ⊗ θ) ≫ (tensorComparisonOfIso X)⁻¹`.

The second is the sense in which the docstrings of this directory say that what remains of the
keystone "is a determinate value for `μ`, equivalently for `ν`, equivalently for the component of
[stacks 0E1W]"; it is now a theorem rather than a remark.

Combining the first with the K-flat reduction
`Dualizing.tensorComparisonCompatibility_of_kFlat` gives
`Dualizing.tensorComparisonCompatibility_of_section_q_obj`: the obligation at *every* object of
`D(R)` follows from the single transpose-free equation at the classes of K-flat complexes, where
both sides are chain-level data —
`Dualizing.tensorComparisonCompatibility_lhs_app_q_obj` for the left and
`Dualizing.tensorBaseChangeMor_comp_eq_q_obj` for the right.

**What is not done here.**  `Dualizing.TensorComparisonCompatibility` is not proved and no tag
loses its conditional caveat.  What this file changes is that the obligation is now one equation
between two morphisms of `D(R')` rather than a chain of mutually transposed readings.

## Main results

* `Dualizing.tensorComparisonCompatibility_iff_section` — **the obligation with no transpose**:
  it holds at `X` exactly when the comparison across the square is
  `Dualizing.derivedTensorBaseChangeSection` followed by the tensor of the identity with
  `Dualizing.derivedBaseChangeAlgebraIso`.
* `Dualizing.tensorComparisonCompatibility_iff_eq_inv` — **the obligation as a determinate value
  for the lax monoidal structure map**.
* `Dualizing.tensorComparisonCompatibility_of_section_q_obj` — the obligation at every object,
  from the transpose-free equation at the classes of K-flat complexes.

## Implementation notes

`Dualizing.TensorComparisonCompatibility` is a `def` whose body is the equation, so a proof of
the equation is a proof of it and conversely; the idiom `replace h : _ = _ := h` and `show _ = _`
of `StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonReduction` is used to
move between the two, rather than unfolding the definition, which would reprint a
twenty-line term.

The morphism `𝟙 ⊗ derivedBaseChangeAlgebraIso` is written as a raw pair with its type ascribed,
exactly as in the definition of `Dualizing.TensorComparisonCompatibility`, so that `rw` matches
the two occurrences against each other.

No `@[stacks]` attribute is placed here: the obligation is still open, so nothing in this file
covers a tag.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars

namespace Dualizing

universe uR uA uRp v

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Ff : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alphaf : DerivedCategory.Q ⋙ Ff ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Fi : DerivedCategory (ModuleCat.{max v uR uA uRp} R') ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (alphai : DerivedCategory.Q ⋙ Fi ⟶
    (ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

variable [hf : Ff.IsLeftDerivedFunctor alphaf
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))]
  [hR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hi : Fi.IsLeftDerivedFunctor alphai
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]

include hf hA hR hi in
/-- **The tensor-comparison obligation with the lax monoidal structure map divided out.**  The
obligation holds at `X` exactly when the comparison
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` of the two derived tensor products across
the base-change square is `Dualizing.derivedTensorBaseChangeSection` followed by the tensor of the
identity with the base change `Dualizing.derivedBaseChangeAlgebraIso` of the algebra.

`Dualizing.derivedTensorBaseChangeSection` is a two-sided inverse of the lax monoidal structure
map, unconditionally, by
`Dualizing.derivedTensorBaseChangeSection_comp_derivedTensorBaseChange` and
`Dualizing.derivedTensorBaseChange_comp_derivedTensorBaseChangeSection`; so this is the obligation
multiplied by it on one side.  Neither transpose of
`Dualizing.tensorComparisonCompatibility_of_homEquiv` survives, and neither does the component of
[stacks 0E1W] that reading introduces. -/
theorem tensorComparisonCompatibility_iff_section
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
        Ff alphaf Fi alphai X ↔
      Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso
          (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
          (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
          (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
            Fi alphai)
          (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
            comparisonA hA) X =
        derivedTensorBaseChangeSection.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
            comparisonR X (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
          (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
              max v uR uA uRp + 1} R').tensor.map
            ((𝟙 (baseChangeR.obj X),
                (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
                  comparisonA hA).hom) :
              (baseChangeR.obj X,
                  baseChangeR.obj
                    (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
                (baseChangeR.obj X,
                  derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                    (Algebra.TensorProduct.includeRight :
                      R' →ₐ[R] TensorProduct R A R').toRingHom)) := by
  constructor
  · intro h
    replace h : _ = _ := h
    refine Eq.symm (Eq.trans (congrArg (fun z => _ ≫ z) h.symm) ?_)
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫ _)
      (derivedTensorBaseChangeSection_comp_derivedTensorBaseChange.{uR, uRp, max v uA}
        (algebraMap R R') baseChangeR comparisonR X
        (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ?_
    exact Category.id_comp _
  · intro h
    change _ = _
    refine Eq.trans (congrArg (fun z => _ ≫ z) h) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫ _)
      (derivedTensorBaseChange_comp_derivedTensorBaseChangeSection.{uR, uRp, max v uA}
        (algebraMap R R') baseChangeR comparisonR X
        (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ?_
    exact Category.id_comp _

include hf hA hR hi in
/-- **The tensor-comparison obligation is a determinate value for the lax monoidal structure
map.**  The comparison of the two derived tensor products across the base-change square is
invertible — each of its four factors is, by
`Stacks.CategoryTheory.BaseChange.isIso_tensorComparisonOfIso` — so the obligation holds at `X`
exactly when the lax monoidal structure map `μ` of derived base change along `R → R'` at
`(X, A[0])` is the tensor of the identity with `Dualizing.derivedBaseChangeAlgebraIso` followed by
the comparison's inverse.

This is the sense in which what remains of the keystone is a determinate value for `μ`: no
further reduction can split the obligation into a part about `μ` and a part about the comparison,
because either one determines the other. -/
theorem tensorComparisonCompatibility_iff_eq_inv
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
        Ff alphaf Fi alphai X ↔
      derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR X
          (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) =
        (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
              max v uR uA uRp + 1} R').tensor.map
            ((𝟙 (baseChangeR.obj X),
                (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
                  comparisonA hA).hom) :
              (baseChangeR.obj X,
                  baseChangeR.obj
                    (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
                (baseChangeR.obj X,
                  derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                    (Algebra.TensorProduct.includeRight :
                      R' →ₐ[R] TensorProduct R A R').toRingHom)) ≫
          (Stacks.CategoryTheory.BaseChange.tensorComparisonIsoOfIso
            (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
            (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
            (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR
              comparisonR Fi alphai)
            (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
              comparisonA hA) X).inv :=
  (Iso.eq_comp_inv (Stacks.CategoryTheory.BaseChange.tensorComparisonIsoOfIso
    (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
    (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
    (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR
      comparisonR Fi alphai)
    (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
      comparisonA hA) X)).symm

include hf hA hR hi in
/-- **The obligation at every object, from the transpose-free equation at the classes of K-flat
complexes.**  `Dualizing.tensorComparisonCompatibility_iff_section` turns the obligation into one
equation between two morphisms of `D(R')`, and
`Dualizing.tensorComparisonCompatibility_of_kFlat` reduces the objects it has to be read at to the
localizations of K-flat complexes of `R`-modules.

This is the keystone's single remaining hypothesis in the shape in which both of its sides are
chain-level data: the left-hand side by
`Dualizing.tensorComparisonCompatibility_lhs_app_q_obj` together with
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_baseChangeR_q_obj`, the right-hand side
by `Dualizing.tensorBaseChangeMor_comp_eq_q_obj` once the [stacks 068I] candidate is identified
with the lax monoidal structure map. -/
theorem tensorComparisonCompatibility_of_section_q_obj
    (h : ∀ K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
      CochainComplex.KFlat.{uR, max v uA uRp} K →
      Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso
          (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
          (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
          (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
            Fi alphai)
          (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
            comparisonA hA) (DerivedCategory.Q.obj K) =
        derivedTensorBaseChangeSection.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
            comparisonR (DerivedCategory.Q.obj K)
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
          (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
              max v uR uA uRp + 1} R').tensor.map
            ((𝟙 (baseChangeR.obj (DerivedCategory.Q.obj K)),
                (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
                  comparisonA hA).hom) :
              (baseChangeR.obj (DerivedCategory.Q.obj K),
                  baseChangeR.obj
                    (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
                (baseChangeR.obj (DerivedCategory.Q.obj K),
                  derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                    (Algebra.TensorProduct.includeRight :
                      R' →ₐ[R] TensorProduct R A R').toRingHom)))
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai X :=
  tensorComparisonCompatibility_of_kFlat hTor baseChangeR comparisonR baseChangeA comparisonA
    Ff alphaf Fi alphai
    (fun K hK => (tensorComparisonCompatibility_iff_section hTor baseChangeR comparisonR
      baseChangeA comparisonA Ff alphaf Fi alphai (DerivedCategory.Q.obj K)).mpr (h K hK)) X

end Dualizing

end
