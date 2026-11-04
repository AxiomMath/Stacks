module

public import StacksFrontier.CategoryTheory.Monoidal.DualConjugatePseudofunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorSheafHomAdjunctionSlot
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.InvertibleDerivedSheafHomCounitOnASite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedBiduality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `D(O)` is closed symmetric monoidal

For a ringed site `(C, O)` the symmetric monoidal structure of [Stacks, Tag 0FPT] on `D(O)`,
whose tensor product is the derived tensor product on the nose, is closed: the adjunctions
`- ⊗^𝐋 B ⊣ R𝓗om(B, -)` of [Stacks, Tag 08J8] give the internal hom `R𝓗om(B, -)` on the nose.
The biduality morphism of the closed structure is the biduality morphism of [Stacks, Tag 0A89].

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedTensorFlipIso`: the braiding, as an isomorphism between
  `B ↦ (- ⊗^𝐋 B)` and `B ↦ (B ⊗^𝐋 -)`.
* `AlgebraicGeometry.RingedSite.derivedTensorMonoidalClosed`: the closed structure.

## Main results

* `AlgebraicGeometry.RingedSite.closedBidualityApp_eq_derivedBiduality`: the biduality of the
  closed structure is `AlgebraicGeometry.RingedSite.derivedBiduality`.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

attribute [local instance] derivedTensorMonoidal derivedTensorSymmetric

/-- The braiding identifies `B ↦ (- ⊗^𝐋 B)` with `B ↦ (B ⊗^𝐋 -)`. -/
def derivedTensorFlipIso : (Stacks.SheafOfModules.derivedTensorProductFunctor X).flip ≅
    curriedTensor
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  NatIso.ofComponents
    (fun B => NatIso.ofComponents (fun A => β_ A B)
      (fun g => BraidedCategory.braiding_naturality_left g B))
    (fun l => by
      ext A
      exact BraidedCategory.braiding_naturality_right A l)

/-- **`D(O)` is monoidal closed**, with internal hom `R𝓗om(B, -)` ([Stacks, Tag 08J8]). -/
@[instance_reducible, sga "5 III 2.2" "more general", sga "6 I 7.4" "more general"]
def derivedTensorMonoidalClosed :
    MonoidalClosed
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) where
  closed B :=
    { rightAdj := (derivedSheafHomBifunctor X).obj (op B)
      adj := (derivedTensorSheafHomAdjunction X B).ofNatIsoLeft ((derivedTensorFlipIso X).app B) }

attribute [local instance] derivedTensorMonoidalClosed

/-- The counit of [Stacks, Tag 08J8] is the derived evaluation morphism. -/
theorem derivedTensorSheafHomAdjunction_counit_app_eq
    (B Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedTensorSheafHomAdjunction X B).counit.app Z = derivedSheafHomCounit X B Z := by
  rw [derivedTensorSheafHomAdjunction_counit_app, derivedSheafHomCounit]

/-- The adjunction `A ⊗ - ⊣ ihom A` of the closed structure is the adjunction
`- ⊗^𝐋 A ⊣ R𝓗om(A, -)` transported along `derivedTensorFlipIso`. -/
theorem ihom_adjunction_derivedTensorMonoidalClosed
    (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ihom.adjunction A =
      (derivedTensorSheafHomAdjunction X A).ofNatIsoLeft ((derivedTensorFlipIso X).app A) :=
  rfl

/-- `uncurry` of the closed structure: `Y ⊗ A ≅ A ⊗ Y` followed by the transpose under
[Stacks, Tag 08J8], that is, `f ⊗ A` followed by evaluation. -/
theorem uncurry_derivedTensorMonoidalClosed
    {A Y Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : Y ⟶ (ihom A).obj Z) :
    MonoidalClosed.uncurry f = (β_ Y A).inv ≫
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f).app A ≫
        derivedSheafHomCounit X A Z := by
  show (((derivedTensorSheafHomAdjunction X A).ofNatIsoLeft
    ((derivedTensorFlipIso X).app A)).homEquiv Y Z).symm f = _
  refine (Adjunction.homEquiv_ofNatIsoLeft_symm_apply _ _ f).trans ?_
  refine whisker_eq _ (((derivedTensorSheafHomAdjunction X A).homEquiv_counit (g := f)).trans ?_)
  exact whisker_eq _ (derivedTensorSheafHomAdjunction_counit_app_eq X A Z)

/-- Applying the derived tensor functor to an identity morphism does not change the counit. -/
private theorem map_id_app_derivedSheafHomCounit
    (A Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
      (𝟙 (((derivedSheafHomBifunctor X).obj (op A)).obj Z))).app A ≫ derivedSheafHomCounit X A Z =
      derivedSheafHomCounit X A Z := by
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- The evaluation of the closed structure is the symmetry followed by the derived evaluation
morphism. -/
@[sga "5 III 2.2" "partial", sga "6 I 7.5" "more general"]
theorem ihom_ev_app_derivedTensorMonoidalClosed
    (A Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (ihom.ev A).app Z = (β_ ((ihom A).obj Z) A).inv ≫ derivedSheafHomCounit X A Z := by
  exact (MonoidalClosed.uncurry_id_eq_ev A Z).symm.trans
    ((uncurry_derivedTensorMonoidalClosed X (𝟙 ((ihom A).obj Z))).trans
      (whisker_eq _ (map_id_app_derivedSheafHomCounit X A Z)))

/-- **The biduality of the closed structure is the biduality morphism of [Stacks, Tag 0A89].** -/
theorem closedBidualityApp_eq_derivedBiduality
    (ω M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    MonoidalClosed.closedBidualityApp ω M = derivedBiduality X ω M := by
  apply MonoidalClosed.uncurry_injective
  have e1 := uncurry_derivedTensorMonoidalClosed X (A := M) (Z := ω) (𝟙 ((ihom M).obj ω))
  have e2 := uncurry_derivedTensorMonoidalClosed X (A := derivedDualInto X ω M) (Z := ω)
    (derivedBiduality X ω M)
  refine (MonoidalClosed.uncurry_closedBidualityApp ω M).trans ?_
  refine (whisker_eq _ (MonoidalClosed.uncurry_id_eq_ev (A := M) (X := ω)).symm).trans ?_
  refine (whisker_eq _ e1).trans ?_
  refine (Iso.hom_inv_id_assoc _ _).trans ((map_id_app_derivedSheafHomCounit X M ω).trans ?_)
  refine Eq.trans ?_ e2.symm
  exact (Iso.inv_hom_id_assoc _ _).symm.trans (whisker_eq _ (derivedBiduality_spec X ω M).symm)

end AlgebraicGeometry.RingedSite

end
