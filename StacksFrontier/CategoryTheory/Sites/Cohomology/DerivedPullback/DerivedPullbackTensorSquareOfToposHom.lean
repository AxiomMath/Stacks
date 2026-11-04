module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorIsoCompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOfToposHom
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaBaseChange

/-!
# The comparisons of Stacks 07A4 around a commutative square of ringed topoi

For a commutative square `g ∘ f' = f ∘ g'` of morphisms of ringed topoi, the isomorphisms
`α_h : Lh^*(K ⊗^L L) ≅ Lh^*K ⊗^L Lh^*L` of Stacks 07A4 along the four sides are compatible
across the identification of `Lg^* ⋙ L(f')^*` and `Lf^* ⋙ L(g')^*` with the derived pullback
along the common composite (Stacks 0D6D). This follows from the composition law
`Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_comp`.

## Main results

* `Stacks.Sheaves.DerivedPullback.OfToposHom.tensorComparisonCompatible_derivedPullbackTensorIso`:
  the four comparisons of Stacks 07A4 around a commutative square of morphisms of ringed topoi
  satisfy `Stacks.AffineProjectionFormula.TensorComparisonCompatible`.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Prod

namespace Stacks.Sheaves.DerivedPullback.OfToposHom

open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

/-! ## The four comparisons around a commutative square -/

section Square

open Stacks.Cohomology.DerivedBaseChangeOfToposHom

variable {X' X Y' Y : RingedTopos.{u, u, u}}
  [X'.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y'.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X'.J (Type u)] [HasSheafify X.J (Type u)]
  [HasSheafify Y'.J (Type u)] [HasSheafify Y.J (Type u)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y'.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y'.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y'.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposHom X Y) (g' : RingedToposHom X' X) (f' : RingedToposHom X' Y')
  (g : RingedToposHom Y' Y) (h : g.comp f' = f.comp g')

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.O).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.O).obj M).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
/-- The identification of the derived pullbacks along two equal morphisms is the transport along
the equality, read through the family of all derived pullbacks. -/
private lemma derivedPullbackCongr_eq {m₁ m₂ : RingedToposHom X' Y} (e : m₁ = m₂) :
    derivedPullbackCongr e =
      eqToIso (congrArg (fun m : RingedToposHom X' Y ↦ derivedPullback m) e) := by
  subst e
  rfl

/-- The compatibility of four comparisons around a square does not see a common change of the
functor both composites are identified with. -/
private lemma tensorComparisonCompatible_trans_iso {S T S' T' : Type*} [Category S] [Category T]
    [Category S'] [Category T'] {Lf : S ⥤ T} {Lf' : S' ⥤ T'} {Lg : S ⥤ S'} {Lg' : T ⥤ T'}
    {Lc Lc' : S ⥤ T'} (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc') (t : Lc' ≅ Lc)
    (A : S × S ⥤ S) (A' : S' × S' ⥤ S') (B : T × T ⥤ T) (B' : T' × T' ⥤ T')
    (αf : A ⋙ Lf ⟶ Lf.prod Lf ⋙ B) (αf' : A' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ B')
    (αg : A ⋙ Lg ⟶ Lg.prod Lg ⋙ A') (αg' : B ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ B') (M N : S)
    (h : Stacks.AffineProjectionFormula.TensorComparisonCompatible (eg ≪≫ t.symm) ef A A' B B'
      αf αf' αg αg' M N) :
    Stacks.AffineProjectionFormula.TensorComparisonCompatible eg (ef ≪≫ t) A A' B B'
      αf αf' αg αg' M N := by
  have hs : Stacks.AffineProjectionFormula.squareCompositeIso eg (ef ≪≫ t) =
      Stacks.AffineProjectionFormula.squareCompositeIso (eg ≪≫ t.symm) ef := by
    simp only [Stacks.AffineProjectionFormula.squareCompositeIso, Iso.trans_symm, Iso.trans_assoc]
  unfold Stacks.AffineProjectionFormula.TensorComparisonCompatible at h ⊢
  rw [hs]
  exact h

/-- **The four isomorphisms of Stacks 07A4 around a commutative square of ringed topoi are
compatible.** For a commutative square `g ∘ f' = f ∘ g'` of morphisms of ringed topoi, the two
iterated derived pullbacks `Lg^* ⋙ L(f')^*` and `Lf^* ⋙ L(g')^*` are identified with the derived
pullback along the common composite by Stacks 0D6D; across that identification, the comparison
of Stacks 07A4 along `g` followed by the one along `f'` is the comparison along `f` followed by
the one along `g'`. -/
theorem tensorComparisonCompatible_derivedPullbackTensorIso
    (M N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    Stacks.AffineProjectionFormula.TensorComparisonCompatible
      (derivedPullbackCompIsoLeft f' g)
      (derivedPullbackCompIsoRight f g' f' g h)
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O))
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y'.O))
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O))
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X'.O))
      (derivedPullbackTensorIso f).hom (derivedPullbackTensorIso f').hom
      (derivedPullbackTensorIso g).hom (derivedPullbackTensorIso g').hom M N := by
  have heg : derivedPullbackCompIsoLeft f' g ≪≫ (derivedPullbackCongr h.symm).symm =
      derivedPullbackCompIso f' g ≪≫
        eqToIso (congrArg (fun m : RingedToposHom X' Y ↦ derivedPullback m) h) := by
    rw [derivedPullbackCongr_eq]
    exact Iso.ext (by simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.inv, eqToIso.hom]; rfl)
  refine tensorComparisonCompatible_trans_iso _ (derivedPullbackCompIso g' f)
    (derivedPullbackCongr h.symm) _ _ _ _ _ _ _ _ M N ?_
  exact Stacks.Cohomology.DerivedProjectionFormula.tensorComparisonCompatible_of_comparisonSquare
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y'.O))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X'.O))
    (derivedPullbackTensorIso g).hom (derivedPullbackTensorIso f').hom
    (derivedPullbackTensorIso f).hom (derivedPullbackTensorIso g').hom
    (Stacks.Cohomology.DerivedRelativeCupProduct.comparisonCompatibleWithSquare_of_composition_laws
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O))
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y'.O))
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O))
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X'.O))
      (derivedPullbackTensorIso g).hom (derivedPullbackTensorIso f').hom
      (derivedPullbackTensorIso f).hom (derivedPullbackTensorIso g').hom
      (fun m : RingedToposHom X' Y ↦ derivedPullback m)
      (fun m ↦ (derivedPullbackTensorIso m).hom) h (derivedPullbackCompIso f' g)
      (derivedPullbackCompIso g' f) _ heg
      (derivedPullbackTensorIso_comp f' g)
      (derivedPullbackTensorIso_comp g' f)) M N

end Square

end Stacks.Sheaves.DerivedPullback.OfToposHom

end
