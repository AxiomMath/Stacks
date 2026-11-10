module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ConstraintNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorBraidingOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorBraidingNatTrans

/-!
# The two spellings of the commutativity constraint of [Stacks, Tag 0FPT] agree on a ringed site

On the derived category `D(𝒪)` of a ringed site there are two spellings of the commutativity
constraint `A ⊗^L B ≅ B ⊗^L A` of [Stacks, Tag 0FPT]:

* `Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom`, the braiding of the symmetric
  monoidal structure re-seated on the derived tensor bifunctor of [Stacks, Tag 06YU]; this is the
  spelling in which the comparison of [Stacks, Tag 07A4] is known to be braided
  (`Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_braiding`);
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso`, the Koszul symmetry of total
  tensor complexes descended through the K-flat models; this is the spelling of
  `Stacks.EtaleCohomology.etaleDerivedTensorBraidingIso` on `D(X_étale, Λ)`.

This file proves that they agree, for arbitrary objects of `D(𝒪)`. For ringed spaces this is
`Stacks.Cohomology.SupportedComplexes.braidingIsoEqCanonical`; the proof here is the same, with
the descent along the localization of the K-flat complexes of [Stacks, Tag 06YS] done by
`CategoryTheory.Localization.natTrans₂_ext`, through which
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingTrans` is defined.

## Main results

* `Stacks.DerivedTensor.RingedSite.canonicalBraidingHom_eq_braidingIso`.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Prod

universe u

namespace Stacks.DerivedTensor.RingedSite

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf
  Stacks.SheafOfModules.Strict.braidedUnderlyingRingSheaf

variable (X : RingedSite.{u, u, u})
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The two spellings of the commutativity constraint of [Stacks, Tag 0FPT] agree** on the
derived category of a ringed site: the braiding of the re-seated symmetric monoidal structure
is the Koszul symmetry of total tensor complexes descended through the K-flat models, for
arbitrary `A`, `B` in `D(𝒪)`. -/
theorem canonicalBraidingHom_eq_braidingIso (A B : DerivedModules X.O) :
    Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom X.O A B =
      ((canonicalDerivedTensorProduct X.O).braidingIso X A B).hom := by
  rw [DerivedTensorProduct.braidingIso_hom_eq]
  let τ : (canonicalDerivedTensorProduct X.O).tensor ⟶
      (canonicalDerivedTensorProduct X.O).tensor.flip :=
    { app := fun A =>
        { app := fun B => Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom X.O A B
          naturality := fun B B' v => by
            convert Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom_naturality X.O
              (𝟙 A) v using 1
            simp
            rfl }
      naturality := fun A A' u => by
        ext B
        convert Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom_naturality X.O
          u (𝟙 B) using 1
        simp
        rfl }
  have hτ : τ = DerivedTensorProduct.braidingTrans X (canonicalDerivedTensorProduct X.O) := by
    refine Localization.natTrans₂_ext (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQ X.O)
      (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQ X.O)
      (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQuasiIso X.O)
      (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQuasiIso X.O) (fun K L => ?_)
    change Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom X.O
        (DerivedCategory.Q.obj K.obj) (DerivedCategory.Q.obj L.obj) =
      ((DerivedTensorProduct.braidingTrans X (canonicalDerivedTensorProduct X.O)).app
        (DerivedCategory.Q.obj K.obj)).app (DerivedCategory.Q.obj L.obj)
    have hK : Stacks.SheafOfModules.KFlat X.O K.obj := K.property
    have hL : Stacks.SheafOfModules.KFlat X.O L.obj := L.property
    rw [DerivedTensorProduct.braidingTrans_app_app X _ K.obj L.obj hK hL]
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine (Iso.eq_comp_inv _).2 ?_
    exact (Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_braiding X.O K.obj L.obj
      hK hL).trans (congrArg
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalComparisonHom X.O K.obj L.obj hK hL ≫ ·)
        ((Stacks.SheafOfModules.DerivedMonoidal.complexBraidingHom_eq X.O K.obj L.obj).trans
          (congrArg DerivedCategory.Q.map
            (Stacks.SheafOfModules.Tensor.koszulBraiding_eq_tensorComplexFlipIso X.O K.obj L.obj))))
  exact congrArg (fun t => (t.app A).app B) hτ

end Stacks.DerivedTensor.RingedSite

end
