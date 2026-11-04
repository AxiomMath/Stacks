module

public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsModelComp
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.Basic

/-!
# The base-change square of models of derived extension of scalars

Let `R → A` and `R → R'` be two ring homomorphisms and let `A' = A ⊗_R R'` be the pushout.  The
square

```
  R ---→ A
  |      |
  v      v
  R' --→ A ⊗_R R'
```

of ring homomorphisms commutes, both composites being the structure map of `A ⊗_R R'` as an
`R`-algebra.  For *arbitrary* models `Ff`, `baseChangeA`, `baseChangeR`, `Fi` of derived
extension of scalars along the four edges there is a canonical isomorphism

`Ff ⋙ baseChangeA ≅ baseChangeR ⋙ Fi`

of functors `D(R) ⥤ D(A ⊗_R R')`, together with the equation it satisfies against the two
composite comparisons to degreewise extension of scalars along `R → A ⊗_R R'`.

Nothing is assumed about the models beyond being total left derived functors of degreewise
extension of scalars, and Tor independence is not needed.

## Main definitions

* `Dualizing.derivedBaseChangeSquareIso`: the isomorphism.

## Main results

* `Dualizing.derivedBaseChangeSquareIso_hom_app_comp_comparison`: its characterizing equation.
* `Dualizing.derivedBaseChangeSquare_hom_ext`: two morphisms into `Ff ⋙ baseChangeA` agree as
  soon as they agree against that composite comparison at every cochain complex.

## Implementation notes

The four rings occupy four independent universes: `R` in `uR`, `A` in `uA`, `R'` in `uR'` and
`A ⊗_R R'` in `max uA uR'`, with a common module universe `max v uR uA uR'`, the generality of
`StacksDraft.DerivedExtensionScalarsModelComp.modelSquareIso`. The composition isomorphisms of
`StacksDraft.DerivedExtensionScalarsComp` and of
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp` are available only at
equal ring universes and only at the chosen models, so neither applies here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open CochainComplex.DerivedExtensionScalars

namespace Dualizing

universe uR uA uRp v

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] extendScalarsAdditiveOfRingHom
attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Square

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

/-- **The top-and-right edge of the base-change square.**  Extending scalars from `R` to `A` and
then to `A ⊗_R R'` is extending them from `R` to `A ⊗_R R'`. -/
theorem algebraMap_tensorProduct_comp_left :
    (algebraMap A (TensorProduct R A R')).comp (algebraMap R A) =
      algebraMap R (TensorProduct R A R') :=
  (IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm

/-- **The left-and-bottom edge of the base-change square.**  Extending scalars from `R` to `R'`
and then along the inclusion `R' → A ⊗_R R'` is extending them from `R` to `A ⊗_R R'`: the
inclusion is a homomorphism of `R`-algebras. -/
theorem algebraMap_tensorProduct_comp_right :
    (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom.comp (algebraMap R R') =
      algebraMap R (TensorProduct R A R') :=
  (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').comp_algebraMap

variable
  (Ff : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alphaf : DerivedCategory.Q ⋙ Ff ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
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
/-- **The base-change square of models of derived extension of scalars.**  For arbitrary models
of derived extension of scalars along the four edges of

```
  R ---→ A
  |      |
  v      v
  R' --→ A ⊗_R R'
```

the two composites `D(R) ⥤ D(A ⊗_R R')` are canonically isomorphic, both being total left
derived functors of degreewise extension of scalars along `R → A ⊗_R R'`. -/
def derivedBaseChangeSquareIso : Ff ⋙ baseChangeA ≅ baseChangeR ⋙ Fi :=
  @StacksDraft.DerivedExtensionScalarsModelComp.modelSquareIso.{uR, uA, uRp, v,
      max v uR uA uRp + 1, max v uR uA uRp + 1, max v uR uA uRp + 1}
    R A R' (TensorProduct R A R') _ _ _ _ _ _ _ _
    (algebraMap R A) (algebraMap A (TensorProduct R A R')) (algebraMap R R')
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
    (algebraMap R (TensorProduct R A R'))
    algebraMap_tensorProduct_comp_left algebraMap_tensorProduct_comp_right
    Ff alphaf baseChangeA comparisonA baseChangeR comparisonR Fi alphai hf hA hR hi

include hf hA hR hi in
/-- **The characterizing equation of the base-change square isomorphism.**  Composing it with
the composite comparison along `R → R' → A ⊗_R R'` returns the composite comparison along
`R → A → A ⊗_R R'`, at every cochain complex of `R`-modules. -/
theorem derivedBaseChangeSquareIso_hom_app_comp_comparison
    (P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) :
    (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
            Fi alphai).hom.app (DerivedCategory.Q.obj P) ≫
        (StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
          max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
          max v uR uA uRp + 1}
          (algebraMap R R')
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom
          baseChangeR comparisonR Fi alphai
          (algebraMap R (TensorProduct R A R'))
          algebraMap_tensorProduct_comp_right).app P =
      (StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uA,
        max uA uRp, max v uRp, max v uR uA uRp + 1, max v uR uA uRp + 1,
        max v uR uA uRp + 1}
        (algebraMap R A) (algebraMap A (TensorProduct R A R'))
        Ff alphaf baseChangeA comparisonA
        (algebraMap R (TensorProduct R A R'))
        algebraMap_tensorProduct_comp_left).app P :=
  @StacksDraft.DerivedExtensionScalarsModelComp.modelSquareIso_hom_app_comp_comparison.{uR,
      uA, uRp, v, max v uR uA uRp + 1, max v uR uA uRp + 1, max v uR uA uRp + 1}
    R A R' (TensorProduct R A R') _ _ _ _ _ _ _ _
    (algebraMap R A) (algebraMap A (TensorProduct R A R')) (algebraMap R R')
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
    (algebraMap R (TensorProduct R A R'))
    algebraMap_tensorProduct_comp_left algebraMap_tensorProduct_comp_right
    Ff alphaf baseChangeA comparisonA baseChangeR comparisonR Fi alphai hf hA hR hi P

include hf hA in
/-- **Two morphisms into the top-and-right composite agree as soon as they agree against its
comparison.**  Two morphisms into `Ff ⋙ baseChangeA` are equal as soon as their composites with
the composite comparison along `R → A → A ⊗_R R'` agree at every cochain complex. -/
theorem derivedBaseChangeSquare_hom_ext
    (H : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
    (γ₁ γ₂ : H ⟶ Ff ⋙ baseChangeA)
    (hγ : ∀ P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
      γ₁.app (DerivedCategory.Q.obj P) ≫
          (StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uA,
            max uA uRp, max v uRp, max v uR uA uRp + 1, max v uR uA uRp + 1,
            max v uR uA uRp + 1}
            (algebraMap R A) (algebraMap A (TensorProduct R A R'))
            Ff alphaf baseChangeA comparisonA
            (algebraMap R (TensorProduct R A R'))
            algebraMap_tensorProduct_comp_left).app P =
        γ₂.app (DerivedCategory.Q.obj P) ≫
          (StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uA,
            max uA uRp, max v uRp, max v uR uA uRp + 1, max v uR uA uRp + 1,
            max v uR uA uRp + 1}
            (algebraMap R A) (algebraMap A (TensorProduct R A R'))
            Ff alphaf baseChangeA comparisonA
            (algebraMap R (TensorProduct R A R'))
            algebraMap_tensorProduct_comp_left).app P) :
    γ₁ = γ₂ :=
  @StacksDraft.DerivedExtensionScalarsModelComp.comp_hom_ext.{uR, uA, max uA uRp, max v uRp,
      max v uR uA uRp + 1, max v uR uA uRp + 1, max v uR uA uRp + 1}
    R A (TensorProduct R A R') _ _ _ _ _ _
    (algebraMap R A) (algebraMap A (TensorProduct R A R'))
    Ff alphaf baseChangeA comparisonA hf hA
    (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_left H γ₁ γ₂ hγ

end Square

end Dualizing

end
