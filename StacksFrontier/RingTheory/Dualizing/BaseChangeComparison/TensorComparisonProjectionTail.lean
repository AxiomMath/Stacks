module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeCanonicalValue
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonAlgebraResolution

/-!
# The comparison identity with the projection formula over the base read forwards

`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonBaseChangeMor` divides the
keystone `Dualizing.TensorComparisonCompatibility` into two hypotheses, jointly equivalent to it
and neither redundant:

* the **identification** `μ' = μ` of the [stacks 068I] morphism with the lax monoidal structure
  map of derived base change, at pairs of K-flat complexes; and
* the **comparison identity** `μ'_{X, A} ≫ tensorComparisonOfIso X = 𝟙 ⊗ θ`, in which no component
  of [stacks 0E1W], no morphism of [stacks 0E1X] and no transpose occurs.

`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonAlgebraResolution` carries
the second onto a K-flat resolution of the algebra, and records that every factor of the result
then has a chain-level value.  That is *almost* true, and the exception is the subject of this
file.  The comparison across the square is

`Lg (pf.inv.app X) ≫ Θ.inv.app (Lf X) ≫ Rf' (γ.hom.app X) ≫ pf'.hom.app (Lg X)`,

and the first factor is the projection formula over `R` read in the **inverse** direction, which is
the one direction nothing evaluates: `Dualizing.tensorComparisonOfIso_app_q_obj` substitutes
component formulas for the other three and says of this one that it is "left alone, being the
factor for which no component formula is in play", while
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj` evaluates only `pf.hom`.

This file moves it across the equation.  Since the [stacks 068I] morphism is invertible outright
(`Dualizing.isIso_tensorBaseChangeMor`) and the resolution factor `𝟙 ⊗ b⁻¹` is invertible with
`𝟙 ⊗ b` for inverse, the whole prefix of the comparison identity may be cancelled, and what is
left is an equation between the three-factor tail of the comparison and a right-hand side built
from `pf.hom`, the resolution map, the inverse [stacks 068I] morphism and `θ`.  Every factor of
*that* equation is read in a direction some component formula evaluates.

**What is not done here.** `Dualizing.TensorComparisonCompatibility` is not proved and no tag loses
its conditional caveat.  What changes is that the keystone's second half no longer contains a
factor with no component formula at all.  The obstruction that remains is a different one, and it
is worth naming: the two projection formulas `pf` (at `R → A`, read at `Q K`) and `pf'` (at
`R' → A ⊗_R R'`, read at `baseChangeR (Q K)`, hence by
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_baseChangeR_q_obj` at `Q (R' ⊗_R K)`) are
each evaluated by `Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj`, whose
right-hand side is an eight-factor composite running through *two* universe-lift equivalences, the
uniqueness isomorphism `leftAdjointUniq` of the two derived extensions of scalars across the lift,
`Stacks.DerivedHom.BaseChange.scalarRestrictionIso` and the equal-universe projection formula
`Dualizing.derivedExtendRestrictScalarsTensorIsoEqualUniverse`.  The two stacks sit at different
ring maps and at different complexes, so they do not cancel against each other; reconciling them
is what a proof of the comparison identity now asks for.

## Main results

* `Stacks.CategoryTheory.BaseChange.comp_tensorComparisonOfIso_eq_iff_tail` — **the cancellation**:
  an equation read against the comparison across a square of adjunctions, with the projection
  formula over the base moved to the other side, so that only its `hom` direction occurs.  Stated
  over variable categories, and taking the inverse of the cancelled prefix as an argument with its
  two defining equations rather than through `IsIso`.
* `Dualizing.tensor_map_id_comp_inv` — tensoring the identity with an isomorphism cancels against
  its inverse, which is the invertibility of the resolution factor.
* `Dualizing.tensorBaseChangeMor_comp_tensorComparison_eq_iff_tail` — **the re-reading**: the
  transported comparison identity at `(Q K, P)` holds exactly when the tail equation does.
* `Dualizing.tensorComparisonCompatibility_of_kFlat_tail` — the split with the algebra resolved and
  the projection formula over the base read forwards, which is the form a consumer attempting the
  keystone's second half should take.

## Implementation notes

Two spellings of the comparison's source are definitionally but not syntactically equal at the
base-change square: the partial application of the tensor bifunctor of [stacks 0A63] and
`Dualizing.derivedExtendRestrictScalarsTensorFunctor`, between which
`Dualizing.derivedExtendRestrictScalarsTensorFunctor_map` is the `rfl` that `rw` would have to
cross.  Two consequences shape the statements here.

First, the cancellation takes the inverse of the prefix as an argument with its two equations
instead of as an `IsIso` instance: an `IsIso` hypothesis carries the object spellings in its
*indices*, and instance resolution works only up to reducible transparency, so the goal
`IsIso (baseChangeR.map (tensor.map (𝟙, b⁻¹)))` with the one spelling is not closed by the
instance proved for the other — and the two goals print identically.

Second, the composite `n ≫ r` of the cancelled inverse with the right-hand side is passed as an
argument `s` with its defining equation `n ≫ r = s`, in the manner of
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso_eq_of_values`.  Reassociating it after the
fact does not work: `rw [Category.assoc]` and `simp only [Category.assoc]` both report that the
pattern `(f ≫ g) ≫ h` does not occur, because the outer composite carries one spelling of the
shared object and the inner one carries the other.  Supplying the reassociation as an argument
elaborates it against the expected type at default transparency, where the gap is crossed.

No `@[stacks]` attribute is placed here: the obligation is still open, so nothing in this file
covers a tag.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars

namespace Stacks.CategoryTheory.BaseChange

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Lg' : B ⥤ B'}

/-- **An equation read against the comparison across a square, with the projection formula over
the base moved to the other side.**  The first factor of
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` is `Lg` applied to the *inverse* of the
projection formula `pf`, and it is the only one of the four for which no component formula is
recorded in the direction the comparison reads it.  An equation `m ≫ tensorComparisonOfIso X = r`,
with `m` invertible, is therefore rewritten here as an equation whose left-hand side is the
remaining three factors and whose right-hand side carries `Lg (pf.hom.app X)` — the projection
formula in the direction a component formula evaluates.

The inverse of `m` is taken as an argument `n` with its two defining equations rather than through
`IsIso`, so that no instance has to be synthesized at the composite: at the base-change square the
target of `m` is `Lg (Tens X)`, whose two spellings — the partial application of the tensor
bifunctor of [stacks 0A63] and `Dualizing.derivedExtendRestrictScalarsTensorFunctor` — are
definitionally but not syntactically equal, and instance resolution does not cross that gap even
though the goal it fails on prints identically to the one it would solve.

Nothing is assumed of the square beyond the four isomorphisms and nothing of `m` beyond the two
equations, which are exactly invertibility; the two readings are equivalent, so neither is weaker.
Stated over variable categories for the reason recorded on
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso_eq_of_values`: an instantiation at a
concrete square computes its type from the arguments instead of unifying two spellings of the
comparison's source. -/
theorem comp_tensorComparisonOfIso_eq_iff_tail {Tens : A ⥤ A} {Tens' : A' ⥤ A'}
    (pf : Lf ⋙ Rf ≅ Tens) (pf' : Lf' ⋙ Rf' ≅ Tens')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg) (X : A)
    {W : A'} (m : W ⟶ Lg.obj (Tens.obj X)) (n : Lg.obj (Tens.obj X) ⟶ W)
    (hmn : m ≫ n = 𝟙 W) (hnm : n ≫ m = 𝟙 (Lg.obj (Tens.obj X)))
    (r : W ⟶ Tens'.obj (Lg.obj X)) {s : Lg.obj (Tens.obj X) ⟶ Tens'.obj (Lg.obj X)}
    (hs : n ≫ r = s) :
    m ≫ tensorComparisonOfIso pf pf' γ Θ X = r ↔
      Θ.inv.app (Lf.obj X) ≫ Rf'.map (γ.hom.app X) ≫ pf'.hom.app (Lg.obj X) =
        Lg.map (pf.hom.app X) ≫ s := by
  subst hs
  have hdef : tensorComparisonOfIso pf pf' γ Θ X =
      Lg.map (pf.inv.app X) ≫
        (Θ.inv.app (Lf.obj X) ≫ Rf'.map (γ.hom.app X) ≫ pf'.hom.app (Lg.obj X)) :=
    rfl
  have hc : Lg.map (pf.inv.app X) ≫ Lg.map (pf.hom.app X) = 𝟙 (Lg.obj (Tens.obj X)) := by
    rw [← Lg.map_comp, pf.inv_hom_id_app, Lg.map_id]
  have hc' : Lg.map (pf.hom.app X) ≫ Lg.map (pf.inv.app X) =
      𝟙 (Lg.obj ((Lf ⋙ Rf).obj X)) := by
    rw [← Lg.map_comp, pf.hom_inv_id_app, Lg.map_id]
  rw [hdef]
  constructor
  · rintro rfl
    simp only [reassoc_of% hnm, reassoc_of% hc']
  · intro h
    rw [h]
    simp only [reassoc_of% hc, reassoc_of% hmn]

end Stacks.CategoryTheory.BaseChange

namespace Dualizing

universe uR uA uRp v u₀ v₀

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

section TensorMapIso

/-- **Tensoring the identity with an isomorphism cancels against its inverse.**  The tensor
bifunctor of [stacks 0A63] is functorial on the product category, so the pairs `(𝟙, b.hom)` and
`(𝟙, b.inv)` compose to `(𝟙, 𝟙)`, which it carries to the identity.

The transport of the comparison identity onto a resolution of the algebra composes the identity on
`X` with the resolution map in the second variable, and this is what lets the resulting factor be
moved across the equation.  Recorded as the equation rather than as an `IsIso` instance: the two
spellings of the morphism's target differ syntactically at the base-change square, and an `IsIso`
hypothesis carries those spellings in its indices, where instance resolution cannot cross between
them. -/
theorem tensor_map_id_comp_inv {R : Type u₀} [CommRing R]
    (X : DerivedCategory (ModuleCat.{max u₀ v₀} R))
    {Y Y' : DerivedCategory (ModuleCat.{max u₀ v₀} R)} (b : Y ≅ Y') :
    (derivedHomAdjunctionOverRing.{u₀, v₀, max u₀ v₀ + 1} R).tensor.map
          ((𝟙 X, b.hom) : (X, Y) ⟶ (X, Y')) ≫
        (derivedHomAdjunctionOverRing.{u₀, v₀, max u₀ v₀ + 1} R).tensor.map
          ((𝟙 X, b.inv) : (X, Y') ⟶ (X, Y)) =
      𝟙 ((derivedHomAdjunctionOverRing.{u₀, v₀, max u₀ v₀ + 1} R).tensor.obj (X, Y)) :=
  Eq.trans ((derivedHomAdjunctionOverRing.{u₀, v₀, max u₀ v₀ + 1} R).tensor_map_comp _ _ _ _)
    (Eq.trans (congrArg _ (Prod.ext (Category.comp_id _) b.hom_inv_id))
      ((derivedHomAdjunctionOverRing.{u₀, v₀, max u₀ v₀ + 1} R).tensor_map_id _ _))

/-- Conjugating an inverse pair `u, v` by an isomorphism `m` into `F.obj Y` gives two cancelling
composites. -/
private theorem map_comp_inv_cancel {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W : D} {Y Z : C} (m : W ⟶ F.obj Y) [IsIso m] (u : Y ⟶ Z) (v : Z ⟶ Y)
    (huv : u ≫ v = 𝟙 Y) (hvu : v ≫ u = 𝟙 Z) :
    (m ≫ F.map u) ≫ F.map v ≫ inv m = 𝟙 W ∧ (F.map v ≫ inv m) ≫ m ≫ F.map u = 𝟙 (F.obj Z) := by
  constructor
  · rw [Category.assoc, ← Category.assoc (F.map u), ← F.map_comp, huv, F.map_id, Category.id_comp,
      IsIso.hom_inv_id]
  · rw [Category.assoc, IsIso.inv_hom_id_assoc, ← F.map_comp, hvu, F.map_id]

end TensorMapIso

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
/-- **The transported comparison identity, with the projection formula over the base read
forwards.**  The hypothesis of `Dualizing.tensorComparisonCompatibility_of_kFlat_resolution` —
the keystone's second half, carried onto a resolution `b : A[0] ≅ P` of the algebra — reads the
projection formula over `R` through `pf.inv`, the one factor of
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` for which this directory records no
component formula in that direction: `Dualizing.tensorComparisonOfIso_app_q_obj` leaves it alone,
and `Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj` evaluates only `pf.hom`.

`Stacks.CategoryTheory.BaseChange.comp_tensorComparisonOfIso_eq_iff_tail` moves it across the
equation.  What is left on the left-hand side is the three remaining factors — the inverse
comparison of [stacks 0661] at `Ff X`, the base-change square isomorphism at `X`, and the
projection formula over `R'` at `baseChangeR X` — and the right-hand side carries `baseChangeR`
of `pf.hom`, of the resolution map tensored into `X`, and the inverse of the [stacks 068I]
morphism, which `Dualizing.isIso_tensorBaseChangeMor` provides unconditionally.

Every factor is now read in the direction some component formula evaluates it:
`Dualizing.restrictionBaseChangeIsoGeneral_inv_app_of_iso` and
`Dualizing.restrictionBaseChangeIsoGeneral_inv_app_q_obj` for the first,
`Dualizing.derivedBaseChangeSquareIso_hom_app_q_obj` for the second,
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_baseChangeR_q_obj` for the third,
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj` for `pf.hom`,
`Dualizing.tensorBaseChangeMor_comp_eq_q_obj` together with
`Dualizing.isIso_tensorBaseChangeMor` for the inverse [stacks 068I] morphism, and
`Dualizing.derivedBaseChangeAlgebraIso_hom_eq_single` for the base change of the algebra.

This is an `Iff`, so nothing is weakened: the two readings of the keystone's second half are
interchangeable. -/
theorem tensorBaseChangeMor_comp_tensorComparison_eq_iff_tail
    (D : TotalDerivedExtensionScalars.{uR, max v uR uA uRp, uRp,
      max v uR uA uRp + 1, max v uR uA uRp + 1} (algebraMap R R'))
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    {P : DerivedCategory (ModuleCat.{max v uR uA uRp} R)}
    (b : derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A) ≅ P) :
    (tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR D X P ≫
          baseChangeR.map ((derivedHomAdjunctionOverRing.{uR, max v uR uA uRp,
                max v uR uA uRp + 1} R).tensor.map
              ((𝟙 X, b.inv) :
                (X, P) ⟶ (X, derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
            Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso
              (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp}
                (algebraMap R A) Ff alphaf)
              (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
              (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR
                comparisonR Fi alphai)
              (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
                comparisonA hA) X =
        (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
            max v uR uA uRp + 1} R').tensor.map
          ((𝟙 (baseChangeR.obj X),
              baseChangeR.map b.inv ≫
                (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
                  comparisonA hA).hom) :
            (baseChangeR.obj X, baseChangeR.obj P) ⟶
              (baseChangeR.obj X,
                derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom))) ↔
      (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
              comparisonA hA).inv.app (Ff.obj X) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
            ((derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR
              comparisonR Fi alphai).hom.app X) ≫
            (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).hom.app
              (baseChangeR.obj X) =
        baseChangeR.map
            ((derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp}
              (algebraMap R A) Ff alphaf).hom.app X) ≫
          baseChangeR.map ((derivedHomAdjunctionOverRing.{uR, max v uR uA uRp,
                max v uR uA uRp + 1} R).tensor.map
              ((𝟙 X, b.hom) :
                (X, derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ⟶ (X, P))) ≫
            CategoryTheory.inv (tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R')
                baseChangeR comparisonR D X P) ≫
              (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
                  max v uR uA uRp + 1} R').tensor.map
                ((𝟙 (baseChangeR.obj X),
                    baseChangeR.map b.inv ≫
                      (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
                        comparisonA hA).hom) :
                  (baseChangeR.obj X, baseChangeR.obj P) ⟶
                    (baseChangeR.obj X,
                      derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                        (Algebra.TensorProduct.includeRight :
                          R' →ₐ[R] TensorProduct R A R').toRingHom)) := by
  obtain ⟨hmn, hnm⟩ := map_comp_inv_cancel baseChangeR
    (tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR D X P)
    _ _ (tensor_map_id_comp_inv X b.symm) (tensor_map_id_comp_inv X b)
  have key := Stacks.CategoryTheory.BaseChange.comp_tensorComparisonOfIso_eq_iff_tail
    (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
    (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
    (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
      Fi alphai)
    (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
      comparisonA hA) X
    (tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR D X P ≫
      baseChangeR.map ((derivedHomAdjunctionOverRing.{uR, max v uR uA uRp,
            max v uR uA uRp + 1} R).tensor.map
          ((𝟙 X, b.inv) :
            (X, P) ⟶ (X, derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))))
    (baseChangeR.map ((derivedHomAdjunctionOverRing.{uR, max v uR uA uRp,
          max v uR uA uRp + 1} R).tensor.map
        ((𝟙 X, b.hom) :
          (X, derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ⟶ (X, P))) ≫
      CategoryTheory.inv (tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R')
        baseChangeR comparisonR D X P))
    hmn hnm
    ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
        max v uR uA uRp + 1} R').tensor.map
      ((𝟙 (baseChangeR.obj X),
          baseChangeR.map b.inv ≫
            (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
              comparisonA hA).hom) :
        (baseChangeR.obj X, baseChangeR.obj P) ⟶
          (baseChangeR.obj X,
            derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom)))
    (Category.assoc _ _ _)
  rw [Category.assoc] at key
  exact key

include hf hA hR hi in
/-- **The split with the algebra resolved and the projection formula over the base read
forwards.**  `Dualizing.TensorComparisonCompatibility` holds at every object of `D(R)` as soon as

* the [stacks 068I] morphism is the lax monoidal structure map at every pair of localizations of
  K-flat complexes of `R`-modules, and
* for every K-flat `P`, every isomorphism `b : A[0] ≅ Q P` and every K-flat `K`, the three-factor
  tail of the comparison across the base-change square at `Q K` is `baseChangeR` of the projection
  formula over `R` and of the resolution map tensored into `Q K`, followed by the inverse of the
  [stacks 068I] morphism and the tensoring of the identity with the base change of the algebra.

This is `Dualizing.tensorComparisonCompatibility_of_kFlat_resolution` with its second hypothesis
rewritten by `Dualizing.tensorBaseChangeMor_comp_tensorComparison_eq_iff_tail`.  What it changes is
the direction in which the projection formula over `R` is read: the earlier form reads it through
`pf.inv` at `Q K`, for which no component formula exists, and this one through `pf.hom` at `Q K`,
where `Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj` evaluates it.  Each of the
other five factors was already available in the direction it is read here.

Nothing is weakened: the rewriting is an `Iff`, and the hypothesis quantifies over the same
resolutions. -/
theorem tensorComparisonCompatibility_of_kFlat_tail
    (D : TotalDerivedExtensionScalars.{uR, max v uR uA uRp, uRp,
      max v uR uA uRp + 1, max v uR uA uRp + 1} (algebraMap R R'))
    (hmu : ∀ K L : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
      CochainComplex.KFlat.{uR, max v uA uRp} K → CochainComplex.KFlat.{uR, max v uA uRp} L →
      tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR D
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) =
        derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L))
    (h : ∀ P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
      CochainComplex.KFlat.{uR, max v uA uRp} P →
      ∀ b : derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A) ≅
          DerivedCategory.Q.obj P,
      ∀ K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
      CochainComplex.KFlat.{uR, max v uA uRp} K →
      (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
              comparisonA hA).inv.app (Ff.obj (DerivedCategory.Q.obj K)) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
            ((derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR
              comparisonR Fi alphai).hom.app (DerivedCategory.Q.obj K)) ≫
            (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).hom.app
              (baseChangeR.obj (DerivedCategory.Q.obj K)) =
        baseChangeR.map
            ((derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp}
              (algebraMap R A) Ff alphaf).hom.app (DerivedCategory.Q.obj K)) ≫
          baseChangeR.map ((derivedHomAdjunctionOverRing.{uR, max v uR uA uRp,
                max v uR uA uRp + 1} R).tensor.map
              ((𝟙 (DerivedCategory.Q.obj K), b.hom) :
                (DerivedCategory.Q.obj K,
                    derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ⟶
                  (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P))) ≫
            CategoryTheory.inv (tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R')
                baseChangeR comparisonR D (DerivedCategory.Q.obj K)
                (DerivedCategory.Q.obj P)) ≫
            (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
                max v uR uA uRp + 1} R').tensor.map
              ((𝟙 (baseChangeR.obj (DerivedCategory.Q.obj K)),
                  baseChangeR.map b.inv ≫
                    (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
                      comparisonA hA).hom) :
                (baseChangeR.obj (DerivedCategory.Q.obj K),
                    baseChangeR.obj (DerivedCategory.Q.obj P)) ⟶
                  (baseChangeR.obj (DerivedCategory.Q.obj K),
                    derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                      (Algebra.TensorProduct.includeRight :
                        R' →ₐ[R] TensorProduct R A R').toRingHom)))
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai X :=
  tensorComparisonCompatibility_of_kFlat_resolution hTor baseChangeR comparisonR baseChangeA
    comparisonA Ff alphaf Fi alphai D hmu
    (fun P hP b K hK =>
      (tensorBaseChangeMor_comp_tensorComparison_eq_iff_tail hTor baseChangeR comparisonR
        baseChangeA comparisonA Ff alphaf Fi alphai D (DerivedCategory.Q.obj K) b).mpr
        (h P hP b K hK)) X

end Dualizing

end
