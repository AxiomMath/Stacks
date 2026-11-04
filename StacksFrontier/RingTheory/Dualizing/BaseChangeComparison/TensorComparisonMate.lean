module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonTranspose

/-!
# The comparison across the square, with the base change 2-cell transposed away

`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` is a composite of four factors,

`Lg (pf.inv) ≫ Θ.inv ≫ Rf' (γ.hom) ≫ pf'.hom`,

and two of them — the inverse base-change 2-cell `Θ.inv` and `Rf'` of the comparison `γ` of the
two composites around the square — are the only place the 2-cell `Θ` occurs.  When `Θ.inv` is the
mate of `γ.inv`, which is the hypothesis
`Stacks.CategoryTheory.BaseChange.tensorComparison_comp_action_of_mate` already asks for, those two
factors are *one adjoint transpose* of a morphism written with `γ` alone:

`Θ.inv (Lf X) ≫ Rf' (γ.hom X) = transpose (γ.inv (Rf (Lf X)) ≫ Lg' (counit) ≫ γ.hom X)`.

This is `CategoryTheory.mateEquiv_counit`, whose statement is exactly the transpose of a mate along
the counit of the lower adjunction, read at the object `Lf X`.  Substituting it eliminates `Θ`
from the comparison outright: what is left is `γ`, the counit of the upper adjunction and the two
projection formulas.

In the base-change square of [stacks 0E2A] this removes the comparison of [stacks 0661] from the
left-hand side of `Dualizing.TensorComparisonCompatibility`.  That comparison —
`Dualizing.restrictionBaseChangeIsoGeneral`, the only factor of the obligation that needs the
Tor-independence hypothesis, and the one whose components
`Dualizing.restrictionBaseChangeIsoGeneral_inv_app_of_iso` can only reach through a transport — no
longer occurs; the square isomorphism `Dualizing.derivedBaseChangeSquareIso`, which does have a
component formula at a K-flat complex
(`Dualizing.derivedBaseChangeSquareIso_hom_app_q_obj`), occurs twice instead.  The mate identity
needed is `Dualizing.derivedBaseChangeSquareIso_mate_eq'`, which holds unconditionally.

## Main results

* `Stacks.CategoryTheory.BaseChange.mate_inv_app_comp_map_hom_app` — the two middle factors of the
  comparison are one adjoint transpose of a morphism written with `γ` and a counit.
* `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso_eq_homEquiv` — **the comparison with the
  base change 2-cell eliminated**: three factors, none of them `Θ`.
* `Stacks.CategoryTheory.BaseChange.homEquiv_symm_tensorComparisonOfIso` — the same statement with
  the projection formula over `A'` transposed away as well: the comparison, read as a morphism
  `Lf' (Lg (Tens X)) ⟶ Lg' (Lf X)` through the lower adjunction and `pf'`, is the four-factor
  composite of `Lf' Lg (pf.inv)`, `γ.inv`, `Lg'` of a counit and `γ.hom`.
* `Stacks.CategoryTheory.BaseChange.map_unit_comp_mate_inv_app` — on the image of the unit of the
  upper adjunction the two middle factors are the unit of the lower one: there `γ` cancels against
  itself and *neither* `γ` nor `Θ` survives.
* `Stacks.CategoryTheory.BaseChange.map_map_unit_comp_counit_conjugate` — the transposed form of
  that statement: the counit of `adjf` conjugated by `γ` retracts `Lf' Lg` of the unit of `adjf`.
  No mate identity is needed for this one.
* `Dualizing.tensorComparisonOfIso_eq_homEquiv_square` — the instance at the base-change square of
  [stacks 0E2A], where the mate identity is `Dualizing.derivedBaseChangeSquareIso_mate_eq'`.
* `Dualizing.tensorComparisonCompatibility_of_homEquiv_square` —
  `Dualizing.tensorComparisonCompatibility_of_homEquiv` with the comparison of [stacks 0661]
  removed from the hypothesis, and the projection formula over `R` taken out of the transpose.

## Implementation notes

The abstract statements are proved by adjunction calculus only: `CategoryTheory.mateEquiv_counit`,
`CategoryTheory.Adjunction.homEquiv_naturality_left`,
`CategoryTheory.Adjunction.homEquiv_naturality_right` and the two triangle-free equations
`CategoryTheory.Adjunction.homEquiv_unit`, `CategoryTheory.Adjunction.homEquiv_counit`.  Nothing
about rings, modules or derived categories enters, so the transparency obstructions of
`StacksFrontier.Homology.HomComplex.RHom.BaseChange` do not arise.

No `@[stacks]` attribute is placed here: `Dualizing.TensorComparisonCompatibility` is still open,
so nothing in this file covers a tag.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars

namespace Stacks.CategoryTheory.BaseChange

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Lg' : B ⥤ B'}

/-- **The two middle factors of the comparison are one adjoint transpose.**  Let `Θ.inv` be the
mate of `γ.inv` under the two adjunctions.  Then the composite of `Θ.inv` at `Lf X` with `Rf'`
applied to `γ.hom` at `X` is the transpose, under `adjf'`, of

`γ.inv (Rf (Lf X)) ≫ Lg' (counit of adjf at Lf X) ≫ γ.hom X`.

This is `CategoryTheory.mateEquiv_counit` at the object `Lf X`: that equation says precisely that
the transpose of the mate along the counit of `adjf'` is `γ.inv` followed by `Lg'` of the counit of
`adjf`; composing with `γ.hom` on the right is
`CategoryTheory.Adjunction.homEquiv_naturality_right`. -/
theorem mate_inv_app_comp_map_hom_app (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg)
    (hα : mateEquiv adjf adjf' (TwoSquare.mk Lg Lf Lf' Lg' γ.inv) =
      TwoSquare.mk Rf Lg' Lg Rf' Θ.inv)
    (X : A) :
    Θ.inv.app (Lf.obj X) ≫ Rf'.map (γ.hom.app X) =
      adjf'.homEquiv (Lg.obj (Rf.obj (Lf.obj X))) (Lf'.obj (Lg.obj X))
        (γ.inv.app (Rf.obj (Lf.obj X)) ≫ Lg'.map (adjf.counit.app (Lf.obj X)) ≫
          γ.hom.app X) := by
  have key := mateEquiv_counit adjf adjf' (TwoSquare.mk Lg Lf Lf' Lg' γ.inv) (Lf.obj X)
  rw [hα] at key
  have h0 : (adjf'.homEquiv (Lg.obj (Rf.obj (Lf.obj X))) (Lg'.obj (Lf.obj X))).symm
        (Θ.inv.app (Lf.obj X)) =
      γ.inv.app (Rf.obj (Lf.obj X)) ≫ Lg'.map (adjf.counit.app (Lf.obj X)) := by
    rw [Adjunction.homEquiv_counit]
    exact key
  have h1 : adjf'.homEquiv (Lg.obj (Rf.obj (Lf.obj X))) (Lg'.obj (Lf.obj X))
        (γ.inv.app (Rf.obj (Lf.obj X)) ≫ Lg'.map (adjf.counit.app (Lf.obj X))) =
      Θ.inv.app (Lf.obj X) := by
    rw [← h0, Equiv.apply_symm_apply]
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  exact congrArg (fun z => z ≫ Rf'.map (γ.hom.app X)) h1.symm

/-- **The comparison across the square with the base change 2-cell eliminated.**  When `Θ.inv` is
the mate of `γ.inv`, `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` is the inverse
projection formula over the base, the adjoint transpose of
`γ.inv ≫ Lg' (counit) ≫ γ.hom`, and the projection formula over `A'`.

The 2-cell `Θ` does not occur.  For the base-change square of [stacks 0E2A] that means the
comparison of [stacks 0661] does not occur: the comparison `γ` of the two composites around the
square occurs twice in its place. -/
theorem tensorComparisonOfIso_eq_homEquiv {Tens : A ⥤ A} {Tens' : A' ⥤ A'}
    (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    (pf : Lf ⋙ Rf ≅ Tens) (pf' : Lf' ⋙ Rf' ≅ Tens')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg)
    (hα : mateEquiv adjf adjf' (TwoSquare.mk Lg Lf Lf' Lg' γ.inv) =
      TwoSquare.mk Rf Lg' Lg Rf' Θ.inv)
    (X : A) :
    tensorComparisonOfIso pf pf' γ Θ X =
      Lg.map (pf.inv.app X) ≫
        adjf'.homEquiv (Lg.obj (Rf.obj (Lf.obj X))) (Lf'.obj (Lg.obj X))
            (γ.inv.app (Rf.obj (Lf.obj X)) ≫ Lg'.map (adjf.counit.app (Lf.obj X)) ≫
              γ.hom.app X) ≫
          pf'.hom.app (Lg.obj X) := by
  dsimp only [tensorComparisonOfIso]
  rw [← Category.assoc (Θ.inv.app (Lf.obj X)),
    mate_inv_app_comp_map_hom_app adjf adjf' γ Θ hα X]

/-- **The comparison across the square, transposed through the lower adjunction.**  Reading
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` into `Rf' (Lf' (Lg X))` by the inverse
projection formula over `A'` and transposing under `adjf'` leaves a four-factor composite in which
neither projection formula over `A'` nor the base change 2-cell `Θ` occurs: `Lf' Lg` of the inverse
projection formula over the base, `γ.inv`, `Lg'` of the counit of `adjf`, and `γ.hom`.

So the whole of `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` is determined by `γ`, the
counit of the upper adjunction and the projection formula over the base. -/
theorem homEquiv_symm_tensorComparisonOfIso {Tens : A ⥤ A} {Tens' : A' ⥤ A'}
    (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    (pf : Lf ⋙ Rf ≅ Tens) (pf' : Lf' ⋙ Rf' ≅ Tens')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg)
    (hα : mateEquiv adjf adjf' (TwoSquare.mk Lg Lf Lf' Lg' γ.inv) =
      TwoSquare.mk Rf Lg' Lg Rf' Θ.inv)
    (X : A) :
    (adjf'.homEquiv (Lg.obj (Tens.obj X)) (Lf'.obj (Lg.obj X))).symm
        (tensorComparisonOfIso pf pf' γ Θ X ≫ pf'.inv.app (Lg.obj X)) =
      Lf'.map (Lg.map (pf.inv.app X)) ≫ γ.inv.app (Rf.obj (Lf.obj X)) ≫
        Lg'.map (adjf.counit.app (Lf.obj X)) ≫ γ.hom.app X := by
  have h4 : adjf'.homEquiv (Lg.obj (Rf.obj (Lf.obj X))) (Lf'.obj (Lg.obj X))
          (γ.inv.app (Rf.obj (Lf.obj X)) ≫ Lg'.map (adjf.counit.app (Lf.obj X)) ≫
            γ.hom.app X) ≫
        pf'.hom.app (Lg.obj X) ≫ pf'.inv.app (Lg.obj X) =
      adjf'.homEquiv (Lg.obj (Rf.obj (Lf.obj X))) (Lf'.obj (Lg.obj X))
        (γ.inv.app (Rf.obj (Lf.obj X)) ≫ Lg'.map (adjf.counit.app (Lf.obj X)) ≫
          γ.hom.app X) := by
    rw [pf'.hom_inv_id_app]
    exact Category.comp_id _
  have h3 : tensorComparisonOfIso pf pf' γ Θ X ≫ pf'.inv.app (Lg.obj X) =
      Lg.map (pf.inv.app X) ≫
        adjf'.homEquiv (Lg.obj (Rf.obj (Lf.obj X))) (Lf'.obj (Lg.obj X))
          (γ.inv.app (Rf.obj (Lf.obj X)) ≫ Lg'.map (adjf.counit.app (Lf.obj X)) ≫
            γ.hom.app X) := by
    rw [tensorComparisonOfIso_eq_homEquiv adjf adjf' pf pf' γ Θ hα X, Category.assoc,
      Category.assoc, h4]
  rw [h3, Adjunction.homEquiv_naturality_left_symm]
  exact congrArg (fun z => Lf'.map (Lg.map (pf.inv.app X)) ≫ z)
    ((adjf'.homEquiv (Lg.obj (Rf.obj (Lf.obj X))) (Lf'.obj (Lg.obj X))).symm_apply_apply _)

/-- **The two middle factors of the comparison, precomposed with `Lg` of the unit, are the unit of
the lower adjunction.**  Both `γ` and `Θ` disappear: the unit form of the mates correspondence,
`CategoryTheory.unit_mateEquiv`, turns `Lg (unit) ≫ Θ.inv (Lf X)` into
`unit' (Lg X) ≫ Rf' (γ.inv X)`, and the `γ.inv` it produces cancels against the `γ.hom` that
follows.

So the only part of `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` that depends on the
base-change square at all is its leading factor, the inverse projection formula over the base:
everything after it agrees, on the image of the unit, with the unit over `A'`. -/
theorem map_unit_comp_mate_inv_app (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg)
    (hα : mateEquiv adjf adjf' (TwoSquare.mk Lg Lf Lf' Lg' γ.inv) =
      TwoSquare.mk Rf Lg' Lg Rf' Θ.inv)
    (X : A) :
    Lg.map (adjf.unit.app X) ≫ Θ.inv.app (Lf.obj X) ≫ Rf'.map (γ.hom.app X) =
      adjf'.unit.app (Lg.obj X) := by
  have key := unit_mateEquiv adjf adjf' (TwoSquare.mk Lg Lf Lf' Lg' γ.inv) X
  rw [hα] at key
  have key' : Lg.map (adjf.unit.app X) ≫ Θ.inv.app (Lf.obj X) =
      adjf'.unit.app (Lg.obj X) ≫ Rf'.map (γ.inv.app X) := key
  have hcancel : Rf'.map (γ.inv.app X) ≫ Rf'.map (γ.hom.app X) =
      𝟙 (Rf'.obj ((Lg ⋙ Lf').obj X)) := by
    rw [← Rf'.map_comp, γ.inv_hom_id_app, Rf'.map_id]
  rw [← Category.assoc]
  refine Eq.trans (congrArg (fun z => z ≫ Rf'.map (γ.hom.app X)) key') ?_
  rw [Category.assoc, hcancel]
  exact Category.comp_id _

/-- **The counit conjugated by the square isomorphism retracts `Lf' Lg` of the unit.**  The
morphism that `Stacks.CategoryTheory.BaseChange.homEquiv_symm_tensorComparisonOfIso` leaves after
the leading factor — `γ.inv` at `Rf (Lf X)`, `Lg'` of the counit of `adjf`, and `γ.hom` at `X` — is
a retraction of `Lf' Lg` applied to the unit of `adjf`.

Neither adjunction's mate nor the 2-cell `Θ` enters: this is the naturality of `γ.inv` at the unit
followed by the left triangle identity of `adjf`, and then `γ` cancelling against itself. -/
theorem map_map_unit_comp_counit_conjugate (adjf : Lf ⊣ Rf)
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (X : A) :
    Lf'.map (Lg.map (adjf.unit.app X)) ≫ γ.inv.app (Rf.obj (Lf.obj X)) ≫
        Lg'.map (adjf.counit.app (Lf.obj X)) ≫ γ.hom.app X = 𝟙 (Lf'.obj (Lg.obj X)) := by
  have hnat := γ.inv.naturality (adjf.unit.app X)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hnat
  have hinner : Lg'.map (Lf.map (adjf.unit.app X)) ≫
      Lg'.map (adjf.counit.app (Lf.obj X)) ≫ γ.hom.app X = γ.hom.app X := by
    rw [← Category.assoc, ← Lg'.map_comp]
    refine Eq.trans (congrArg (fun z => Lg'.map z ≫ γ.hom.app X)
      (adjf.left_triangle_components X)) ?_
    refine Eq.trans (congrArg (fun z => z ≫ γ.hom.app X) (Lg'.map_id (Lf.obj X))) ?_
    exact Category.id_comp _
  rw [← Category.assoc, hnat, Category.assoc, hinner]
  exact γ.inv_hom_id_app X

end Stacks.CategoryTheory.BaseChange

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
/-- **The tensor comparison at the base-change square, with the comparison of [stacks 0661]
transposed away.**  This is
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso_eq_homEquiv` at the square of
[stacks 0E2A], where the mate identity it needs is `Dualizing.derivedBaseChangeSquareIso_mate_eq'`
— which holds with no hypothesis beyond the four derived-functor universal properties.

`Dualizing.restrictionBaseChangeIsoGeneral`, the comparison of [stacks 0661], does not occur on the
right-hand side: the square isomorphism `Dualizing.derivedBaseChangeSquareIso` occurs twice, once
inverted, with the counit of derived extension of scalars along `R → A` between them, all three
under the adjoint transpose of [stacks 0GMT] along `R' → A ⊗_R R'`. -/
theorem tensorComparisonOfIso_eq_homEquiv_square
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso
        (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
        (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
        (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
          Fi alphai)
        (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
          comparisonA hA) X =
      baseChangeR.map
          ((derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp}
            (algebraMap R A) Ff alphaf).inv.app X) ≫
        (derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).homEquiv _ _
            ((derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR
                  comparisonR Fi alphai).inv.app
                ((ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategory.obj (Ff.obj X)) ≫
              baseChangeA.map
                  ((derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A)
                    Ff alphaf).counit.app (Ff.obj X)) ≫
                (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR
                  comparisonR Fi alphai).hom.app X) ≫
          (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).hom.app (baseChangeR.obj X) :=
  Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso_eq_homEquiv
    (derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
    (derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
    (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
    (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
    (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
      Fi alphai)
    (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA comparisonA hA)
    (derivedBaseChangeSquareIso_mate_eq' hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai)
    X

include hf hA hR hi in
/-- **The tensor-comparison obligation from its transpose, with the comparison of [stacks 0661]
gone.**  `Dualizing.tensorComparisonCompatibility_of_homEquiv` reduces
`Dualizing.TensorComparisonCompatibility` at `X` to an equation whose left-hand side is the
transpose over [stacks 0GMT] along `R → R'` of
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso`.  Substituting
`Dualizing.tensorComparisonOfIso_eq_homEquiv_square` for that comparison and taking the leading
factor out of the transpose by `CategoryTheory.Adjunction.homEquiv_naturality_left` leaves the
hypothesis displayed here.

Neither `Dualizing.restrictionBaseChangeIsoGeneral` — the comparison of [stacks 0661] — nor the
lax monoidal structure map `μ` nor the derived-Hom base-change morphism of [stacks 0E1X] occurs in
it.  What is left on the left-hand side is: the inverse projection formula over `R`, the transpose
over [stacks 0GMT] along `R → R'` of the transpose over [stacks 0GMT] along `R' → A ⊗_R R'` of the
square isomorphism `Dualizing.derivedBaseChangeSquareIso` conjugating a counit, and the projection
formula over `R'`. -/
theorem tensorComparisonCompatibility_of_homEquiv_square
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (h : (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp}
            (algebraMap R A) Ff alphaf).inv.app X ≫
          (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
              comparisonR).homEquiv _ _
            ((derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).homEquiv _ _
                ((derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR
                      comparisonR Fi alphai).inv.app
                    ((ModuleCat.restrictScalars.{max v uR uA uRp}
                      (algebraMap R A)).mapDerivedCategory.obj (Ff.obj X)) ≫
                  baseChangeA.map
                      ((derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A)
                        Ff alphaf).counit.app (Ff.obj X)) ≫
                    (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR
                      comparisonR Fi alphai).hom.app X) ≫
              (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).hom.app
                (baseChangeR.obj X)) =
        (derivedHomAdjunctionOverRing.{uR, max v uR uA uRp, max v uR uA uRp + 1} R).homEquiv X
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) _
          ((derivedExtensionScalarsAdjunction.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
                comparisonR).homEquiv X _
              (((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
                    max v uR uA uRp + 1} R').homEquiv _ _ _).symm
                ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
                    max v uR uA uRp + 1} R').tensor.map
                  (Prod.mkHom (𝟙 (baseChangeR.obj X))
                    (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
                      comparisonA hA).hom))) ≫
            (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uRp, max v uA}
              (algebraMap R R') baseChangeR comparisonR).inv.app
                (Opposite.op (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)), _))) :
    TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai X := by
  refine tensorComparisonCompatibility_of_homEquiv hTor baseChangeR comparisonR baseChangeA
    comparisonA Ff alphaf Fi alphai X ?_
  rw [tensorComparisonOfIso_eq_homEquiv_square hTor baseChangeR comparisonR baseChangeA
      comparisonA Ff alphaf Fi alphai X,
    Adjunction.homEquiv_naturality_left]
  exact h

end Dualizing

end
