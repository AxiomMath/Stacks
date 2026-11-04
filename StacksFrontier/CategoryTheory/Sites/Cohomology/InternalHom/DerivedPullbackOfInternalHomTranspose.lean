module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedPullbackOfInternalHom
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap

/-!
# The canonical map of Stacks 08JF is a transpose comparison

Let `h : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi. The canonical map
`Lh^* RSheafHom(K, L) ⟶ RSheafHom(Lh^* K, Lh^* L)` of Stacks 08JF,
`AlgebraicGeometry.RingedToposSiteHom.derivedPullbackSheafHomMap`, is built from three inputs:
the tensor–internal-Hom bijections of Stacks 08J8 on the two topoi and the monoidality of `Lh^*`
of Stacks 07A4. The abstract comparison
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison` is built from exactly
those inputs. This file records that the first is an instance of the second, so that statements
proved about the abstract comparison of a functor with internal Homs apply to the canonical
map of Stacks 08JF.

## Main definitions

* `AlgebraicGeometry.RingedToposSiteHom.derivedPullbackTensorIsoInternal`: the comparison of
  Stacks 07A4 read at the derived tensor products the internal Homs of Stacks 08J8 are stated
  over, as an isomorphism of uncurried bifunctors.

## Main results

* `AlgebraicGeometry.RingedToposSiteHom.derivedPullbackTensorIsoInternal_inv_app`: the inverse
  of that comparison at a pair of objects, as the composite it is built from.
* `AlgebraicGeometry.RingedToposSiteHom.derivedPullbackSheafHomPairing_eq_homComparisonDatum`:
  the pairing of Stacks 08JF is the transpose datum of the abstract comparison.
* `AlgebraicGeometry.RingedToposSiteHom.derivedPullbackSheafHomMap_eq_homComparison`: the map
  of Stacks 08JF is `Transpose.homComparison` at `P = Lh^*`, the two derived internal Homs, the
  two bijections of Stacks 08J8 and the comparison above.

## Implementation notes

The abstract comparison takes the two bijections of Stacks 08J8 as plain equivalences, so they
enter through `AddEquiv.toEquiv`. The equalities are proved by rewriting, never by `rfl` across
the whole composite: comparing the application of the additive equivalence with that of its
underlying equivalence by definitional unfolding exhausts the recursion depth at these
arguments, as recorded in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedPullbackOfInternalHom`. The two
private lemmas `toEquiv_apply'` and `toEquiv_symm_apply'` state the identification with the
equivalence abstract, where it is `rfl`, and are rewritten with.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedToposSiteHom

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (h : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy h).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  (hmos : h.u.IsMorphismOfSites Y.J X.J)

/-- **Stacks 07A4 at the derived tensor products of Stacks 08J8.** The comparison
`Lh^*(K ⊗^L L) ≅ Lh^*K ⊗^L Lh^*L` of `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso`,
read on both sides through `AlgebraicGeometry.RingedSite.derivedTensorFunctorIso` at the derived
tensor product `Stacks.SheafOfModules.derivedTensorProductFunctor` that the derived internal Hom
and the bijection of Stacks 08J8 are stated over. -/
def derivedPullbackTensorIsoInternal :
    Functor.uncurry.obj
        (Stacks.SheafOfModules.derivedTensorProductFunctor (RingedTopos.toRingedSite Y)) ⋙
        derivedPullback h ≅
      (derivedPullback h).prod (derivedPullback h) ⋙
        Functor.uncurry.obj
          (Stacks.SheafOfModules.derivedTensorProductFunctor (RingedTopos.toRingedSite X)) :=
  Functor.isoWhiskerRight
      (Functor.uncurry.mapIso (RingedSite.derivedTensorFunctorIso (RingedTopos.toRingedSite Y)))
      (derivedPullback h) ≪≫
    Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso h hmos ≪≫
    Functor.isoWhiskerLeft ((derivedPullback h).prod (derivedPullback h))
      (Functor.uncurry.mapIso
        (RingedSite.derivedTensorFunctorIso (RingedTopos.toRingedSite X))).symm

/-- Applying the underlying equivalence of an additive equivalence is applying it. Stated with
the equivalence abstract, so that rewriting with it never compares the large types the
bijection of Stacks 08J8 is stated between. -/
private theorem toEquiv_apply' {α β : Type*} [Add α] [Add β] (e : α ≃+ β) (x : α) :
    e.toEquiv x = e x := rfl

/-- Applying the inverse of the underlying equivalence of an additive equivalence is applying its
inverse; see `toEquiv_apply'`. -/
private theorem toEquiv_symm_apply' {α β : Type*} [Add α] [Add β] (e : α ≃+ β) (y : β) :
    e.toEquiv.symm y = e.symm y := rfl

/-- The inverse of `derivedPullbackTensorIsoInternal` at a pair of objects. -/
theorem derivedPullbackTensorIsoInternal_inv_app
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (derivedPullbackTensorIsoInternal h hmos).inv.app (A, B) =
      (RingedSite.derivedTensorObjIso (RingedTopos.toRingedSite X)
          ((derivedPullback h).obj A) ((derivedPullback h).obj B)).hom ≫
        ((Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso h hmos).app (A, B)).inv ≫
          (derivedPullback h).map
            (RingedSite.derivedTensorObjIso (RingedTopos.toRingedSite Y) A B).inv := by
  simp only [derivedPullbackTensorIsoInternal, Iso.trans_inv, NatTrans.comp_app, Category.assoc]
  rfl

/-- The pairing of Stacks 08JF is the transpose datum of `Transpose.homComparison`. -/
theorem derivedPullbackSheafHomPairing_eq_homComparisonDatum
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    derivedPullbackSheafHomPairing h hmos K L =
      Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparisonDatum (derivedPullback h)
        (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite Y))
        (Functor.uncurry.obj
          (Stacks.SheafOfModules.derivedTensorProductFunctor (RingedTopos.toRingedSite Y)))
        (Functor.uncurry.obj
          (Stacks.SheafOfModules.derivedTensorProductFunctor (RingedTopos.toRingedSite X)))
        (fun A B C => (RingedSite.derivedCurryHomEquiv (RingedTopos.toRingedSite Y) A B C).toEquiv)
        (derivedPullbackTensorIsoInternal h hmos) K L := by
  rw [derivedPullbackSheafHomPairing,
    Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparisonDatum,
    Stacks.Cohomology.DerivedInternalHomPullback.Transpose.evaluation,
    derivedPullbackTensorIsoInternal_inv_app, RingedSite.derivedSheafHomCounit, toEquiv_apply',
    Category.assoc, Category.assoc, ← Functor.map_comp]

/-- **The map of Stacks 08JF is a transpose comparison.** It is
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison` at the functor `Lh^*`,
the derived internal Homs of the two topoi, the tensor–internal-Hom bijections of Stacks 08J8
on the two topoi, and the comparison of Stacks 07A4 read at the derived tensor products those
bijections are stated over. -/
theorem derivedPullbackSheafHomMap_eq_homComparison
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    derivedPullbackSheafHomMap h hmos K L =
      Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison (derivedPullback h)
        (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite Y))
        (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite X))
        (Functor.uncurry.obj
          (Stacks.SheafOfModules.derivedTensorProductFunctor (RingedTopos.toRingedSite Y)))
        (Functor.uncurry.obj
          (Stacks.SheafOfModules.derivedTensorProductFunctor (RingedTopos.toRingedSite X)))
        (fun A B C => (RingedSite.derivedCurryHomEquiv (RingedTopos.toRingedSite Y) A B C).toEquiv)
        (fun A B C => (RingedSite.derivedCurryHomEquiv (RingedTopos.toRingedSite X) A B C).toEquiv)
        (derivedPullbackTensorIsoInternal h hmos) K L := by
  rw [derivedPullbackSheafHomMap, derivedPullbackSheafHomPairing_eq_homComparisonDatum,
    Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison, toEquiv_symm_apply']

end AlgebraicGeometry.RingedToposSiteHom

end
