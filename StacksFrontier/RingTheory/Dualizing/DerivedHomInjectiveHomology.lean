module

public import StacksFrontier.Algebra.Homology.DerivedCategory.InjectiveRepresents
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ExtComparison
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessInternalHomCompare

/-!
# The cohomology of derived Hom into an injective module

Let `A` be a commutative ring, `E` an injective `A`-module and `Y` an arbitrary object of `D(A)`.
This file identifies

`H^n(RHom_A(Y, E[0])) ≅ Hom_A(H^{-n}(Y), E)`

`A`-linearly and naturally in `Y`, for the internal Hom of
`StacksDraft.DerivedHom.derivedHomAdjunction`, the tensor--Hom adjunction whose module universe
is the ring's own.

Three identifications compose, and each is natural in `Y`.

* The two spellings of internal derived Hom agree as bifunctors,
  `Dualizing.modelHomNatIsoDerivedHomAdjunctionOverRing`. This is what makes the next step
  available here: the Ext--cohomology comparison is proved for the other spelling.
* The cohomology of derived Hom is `Ext`,
  `StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso`, which does not require the
  target to be dualizing, so it may be used at `E[0]`.
* An injective object placed in degree `-n` represents `H^{-n}` on the whole derived category,
  `DerivedCategory.homologyToSingleLinearEquiv`.

## Main definitions

* `Dualizing.homologyDerivedHomInjectiveEquiv` — the identification.

## Main results

* `Dualizing.modelHom_map_smul_id_left` — derived Hom for the same-universe adjunction is
  `A`-linear in its source variable, which the comparison of the two spellings carries across
  because it is natural in that variable.
* `Dualizing.homologyDerivedHomInjectiveEquiv_comp` — the identification is natural in `Y`.

## References

* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

variable {A : Type u} [CommRing A]

/-- The fixed identification of `E[0]⟦n⟧` with `E[-n]`. -/
def singleShiftNegIso (E : ModuleCat.{u} A) (n : ℤ) :
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E)⟦n⟧ ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-n)).obj E :=
  ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso n (-n) 0 (by omega)).app E

/-- **Derived Hom is `A`-linear in its source variable, for the same-universe adjunction.**
`ExtComparison.derivedHom_map_smul_id_left` proves this for the
adjunction of [stacks 0A63]; it carries across
`Dualizing.modelHomNatIsoDerivedHomAdjunctionOverRing` precisely because that comparison is
natural in the source variable. One consequence is that `Ext^i_A(M, ω)` is annihilated by every
ideal that annihilates `M`. -/
theorem modelHom_map_smul_id_left (K Ω : DerivedCategory (ModuleCat.{u} A)) (a : A) :
    (DerivedInternalHom.Model.hom A).map
        (((a • 𝟙 K).op, 𝟙 Ω) : ((Opposite.op K, Ω) : _ × _) ⟶ (Opposite.op K, Ω)) =
      a • 𝟙 ((DerivedInternalHom.Model.hom A).obj
        (Opposite.op K, Ω)) := by
  have h := (modelHomNatIsoDerivedHomAdjunctionOverRing A).hom.naturality
    (((a • 𝟙 K).op, 𝟙 Ω) : ((Opposite.op K, Ω) : _ × _) ⟶ (Opposite.op K, Ω))
  rw [ExtComparison.derivedHom_map_smul_id_left] at h
  rw [← cancel_mono ((modelHomNatIsoDerivedHomAdjunctionOverRing A).hom.app (Opposite.op K, Ω)),
    h, Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

/-- `Y ↦ RHom_A(Y, W)` for the same-universe adjunction, in the spelling that
`Dualizing.dualizingDerivedHomFunctor` uses for the other one. -/
def derivedHomIntoFunctor (W : DerivedCategory (ModuleCat.{u} A)) :
    (DerivedCategory (ModuleCat.{u} A))ᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Functor.prod' (Functor.id _) ((Functor.const _).obj W) ⋙ (derivedHomAdjunction (R := A)).hom

/-- **`RHom_A(-, W)` depends on `W` only up to isomorphism**, naturally in the source variable.
`Dualizing.derivedHomIntoFunctor` is the bifunctor `derivedHomAdjunction.hom` with its second
variable fixed at `W`, so an isomorphism `W ≅ W'` is carried by that bifunctor in that
variable, and the naturality square is the commutation
`(f, 𝟙) ≫ (𝟙, e) = (𝟙, e) ≫ (f, 𝟙)` of a product category. -/
def derivedHomIntoFunctorCongr {W W' : DerivedCategory (ModuleCat.{u} A)} (e : W ≅ W') :
    derivedHomIntoFunctor W ≅ derivedHomIntoFunctor W' :=
  NatIso.ofComponents
    (fun X => (derivedHomAdjunction (R := A)).hom.mapIso (Iso.prod (Iso.refl X) e))
    (fun f => by
      change (derivedHomAdjunction (R := A)).hom.map (f, 𝟙 W) ≫
          (derivedHomAdjunction (R := A)).hom.map ((Iso.prod (Iso.refl _) e)).hom =
        (derivedHomAdjunction (R := A)).hom.map ((Iso.prod (Iso.refl _) e)).hom ≫
          (derivedHomAdjunction (R := A)).hom.map (f, 𝟙 W')
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      exact Prod.ext (by simp) (by simp))

/-- **The cohomology of derived Hom into an injective module is corepresented by the module in a
shifted degree**, as an isomorphism of functors on `D(A)ᵒᵖ`: the degree-`n` cohomology of
`RHom_A(-, E[0])`, universe-lifted, is `Hom_{D(A)}(-, E[-n])`.

Three isomorphisms of functors compose: the comparison of the two spellings of internal derived
Hom, `Dualizing.modelHomNatIsoDerivedHomAdjunctionOverRing`; the Ext--cohomology comparison
`StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso` at the target `E[0]`, which
does not need it to be dualizing; and `Dualizing.singleShiftNegIso` in the target variable. -/
def derivedHomInjectiveHomologyNatIso (E : ModuleCat.{u} A) (n : ℤ) :
    derivedHomIntoFunctor ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) n ⋙
          ModuleCat.uliftFunctor.{u + 1, u} A ≅
      (linearYoneda A (DerivedCategory (ModuleCat.{u} A))).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (-n)).obj E) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (Functor.prod' (Functor.id (DerivedCategory (ModuleCat.{u} A))ᵒᵖ)
          ((Functor.const _).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E)))
        (modelHomNatIsoDerivedHomAdjunctionOverRing A))
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n ⋙
        ModuleCat.uliftFunctor.{u + 1, u} A) ≪≫
    (ExtComparison.extCohomologyComparisonIso.{u, u} A
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E) n).symm ≪≫
    (linearYoneda A (DerivedCategory (ModuleCat.{u} A))).mapIso (singleShiftNegIso E n)

/-- **The cohomology of derived Hom into an injective module is the dual of cohomology.** For
`E` an injective `A`-module, `Y` an arbitrary object of `D(A)` and `n : ℤ`,

`H^n(RHom_A(Y, E[0])) ≅ Hom_A(H^{-n}(Y), E)`

`A`-linearly. The first half is `Dualizing.derivedHomInjectiveHomologyNatIso`, the second
`DerivedCategory.homologyToSingleLinearEquiv`. Naturality in `Y` is
`Dualizing.homologyDerivedHomInjectiveEquiv_comp`. -/
def homologyDerivedHomInjectiveEquiv (Y : DerivedCategory (ModuleCat.{u} A))
    (E : ModuleCat.{u} A) [Injective E] (n : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        ((derivedHomAdjunction (R := A)).hom.obj
          (Opposite.op Y, (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E)) :
        Type u) ≃ₗ[A]
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-n)).obj Y : Type u) →ₗ[A]
        (E : Type u)) :=
  (ULift.moduleEquiv (R := A)).symm.trans
    ((((derivedHomInjectiveHomologyNatIso E n).app (Opposite.op Y)).toLinearEquiv).trans
      ((DerivedCategory.homologyToSingleLinearEquiv Y E (-n) A).trans
        ModuleCat.homLinearEquiv))

/-- **The identification is natural in `Y`.** The first half is a morphism of functors, so its
naturality square is `CategoryTheory.NatTrans.naturality`; the second is
`DerivedCategory.homologyToSingleLinearEquiv_comp`. -/
theorem homologyDerivedHomInjectiveEquiv_comp
    {Y Y' : DerivedCategory (ModuleCat.{u} A)} (g : Y' ⟶ Y)
    (E : ModuleCat.{u} A) [Injective E] (n : ℤ)
    (x : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      ((derivedHomIntoFunctor
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E)).obj (Opposite.op Y)) :
        Type u)) :
    homologyDerivedHomInjectiveEquiv Y' E n
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
          ((derivedHomIntoFunctor
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E)).map g.op)).hom x) =
      (homologyDerivedHomInjectiveEquiv Y E n x).comp
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-n)).map g).hom := by
  have happ := congrArg (fun m => ModuleCat.Hom.hom m (ULift.up x))
    ((derivedHomInjectiveHomologyNatIso E n).hom.naturality g.op)
  simp only [Functor.comp_map, ModuleCat.hom_comp, ModuleCat.uliftFunctor, linearYoneda,
    ModuleCat.hom_ofHom] at happ
  have h1 : homologyDerivedHomInjectiveEquiv Y' E n
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
          ((derivedHomIntoFunctor
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E)).map g.op)).hom x) =
      (ModuleCat.homLinearEquiv (R := A) (S := A))
        (DerivedCategory.homologyToSingleLinearEquiv Y' E (-n) A
          (((derivedHomInjectiveHomologyNatIso E n).app (Opposite.op Y')).toLinearEquiv
            (ULift.up (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
              ((derivedHomIntoFunctor
                ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E)).map g.op)).hom
                  x)))) :=
    rfl
  have hkey : ((derivedHomInjectiveHomologyNatIso E n).app (Opposite.op Y')).toLinearEquiv
        (ULift.up (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
          ((derivedHomIntoFunctor
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E)).map g.op)).hom x)) =
      g ≫ ((((derivedHomInjectiveHomologyNatIso E n).app (Opposite.op Y)).toLinearEquiv
        (ULift.up x) : _) : Y ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-n)).obj E) :=
    happ
  have h2 := DerivedCategory.homologyToSingleLinearEquiv_comp Y E (-n) A g
    ((((derivedHomInjectiveHomologyNatIso E n).app (Opposite.op Y)).toLinearEquiv
      (ULift.up x) : _) : Y ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-n)).obj E)
  rw [h1, hkey, h2]
  rfl
end Dualizing

end
