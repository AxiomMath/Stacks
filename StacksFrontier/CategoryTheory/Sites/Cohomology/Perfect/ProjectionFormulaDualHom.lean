module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedUnitorCoherenceUnitPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BraidingNatIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftUnitorNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaStrictlyPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHom

/-!
# Maps out of a perfect object into a derived pullback

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi presented by a morphism of
sites, and let `P` be a perfect object of `D(𝒪_C)` with dual `P^∨`. Suppose that the
projection-formula map of [Stacks, Tag 0B56]

  `Rf_*P^∨ ⊗^L K ⟶ Rf_*(P^∨ ⊗^L Lf^*K)`

is invertible for every `K` (this is [Stacks, Tag 08IN] in the situation of algebraic spaces)
and that `L = Rf_*P^∨` is perfect (this is [Stacks, Tag 0CTM] there). Then, naturally in
`K ∈ D(𝒪_D)`,

  `Hom(P, Lf^*K) = Hom(𝒪_C, P^∨ ⊗^L Lf^*K) = Hom(𝒪_D, Rf_*(P^∨ ⊗^L Lf^*K))`
  `          = Hom(𝒪_D, L ⊗^L K) = Hom(L^∨, K)`.

The first and the last steps are [Stacks, Tag 08JJ] (`M ⊗^L K^∨ = RHom(K, M)` for perfect `K`)
together with the tensor-Hom adjunction [Stacks, Tag 08J8] and the unit constraint; the second
step is the adjunction `Lf^* ⊣ Rf_*` of [Stacks, Tag 07A6] with `Lf^*𝒪_D = 𝒪_C`.

## Main results

* `AlgebraicGeometry.RingedSite.coyonedaDualTensorIso`: `Hom(K, -) ≅ Hom(𝒪, - ⊗^L K^∨)` for a
  perfect `K`, as an isomorphism of functors.
* `Stacks.Cohomology.ProjectionFormulaDualHom.derivedPullbackCoyonedaIso`:
  `Hom(P, Lf^*-) ≅ Hom((Rf_*P^∨)^∨, -)`.

## References

* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor)

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

/-- **Stacks 08JJ as an isomorphism of functors**: for a perfect `K`, tensoring with `K^∨` is
the derived internal Hom out of `K`. The components are `derivedDualTensorSheafHomIso` and the
naturality is `derivedDualTensorSheafHomIso_naturality`. -/
def derivedDualTensorSheafHomNatIso
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    (Stacks.SheafOfModules.derivedTensorProductFunctor X).flip.obj (derivedDual X K) ≅
      (derivedSheafHomBifunctor X).obj (op K) :=
  NatIso.ofComponents (fun M => derivedDualTensorSheafHomIso X K M hK)
    (fun g => derivedDualTensorSheafHomIso_naturality X K hK g)

/-- **Maps out of a perfect object are maps out of the structure sheaf into a tensor product
with the dual**: `Hom(K, M) ≅ Hom(𝒪, M ⊗^L K^∨)`, naturally in `M`. It is Stacks 08JJ
(`derivedDualTensorSheafHomNatIso`), the adjunction of Stacks 08J8 at the structure sheaf, and
the left unit constraint `𝒪 ⊗^L K ≅ K`. -/
def coyonedaDualTensorIso
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    (Stacks.SheafOfModules.derivedTensorProductFunctor X).flip.obj (derivedDual X K) ⋙
        coyoneda.obj (op (derivedStructureSheaf X)) ≅ coyoneda.obj (op K) :=
  Functor.isoWhiskerRight (derivedDualTensorSheafHomNatIso X K hK) _ ≪≫
    ((derivedTensorSheafHomAdjunction X K).compCoyonedaIso.app
      (op (derivedStructureSheaf X))).symm ≪≫
    coyoneda.mapIso (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso X
      (canonicalRingedSiteDerivedTensorProduct X) K).symm.op

/-- For a perfect `K`, the bidual map `K ⟶ K^∨^∨` as an isomorphism. -/
def derivedBidualIso
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) : K ≅ derivedDual X (derivedDual X K) :=
  haveI := isIso_derivedBidual_of_isPerfect X
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) K hK
  asIso (derivedBidual X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) K)

/-- The structure-sheaf-indexed derived tensor product with `E` in the first variable is the
site-indexed derived tensor product with `E` in the second variable: the comparison of the two
canonical bifunctors (`derivedTensorFunctorIso`) followed by the commutativity constraint. -/
def derivedTensorObjFlipIso
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).obj E ≅
      (Stacks.SheafOfModules.derivedTensorProductFunctor X).flip.obj E :=
  ((derivedTensorFunctorIso X).app E).symm ≪≫
    (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso X
      (canonicalRingedSiteDerivedTensorProduct X)).app E

end AlgebraicGeometry.RingedSite

namespace Stacks.Cohomology.ProjectionFormulaDualHom

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ V : Y.C, HasSheafify (Y.J.over V) AddCommGrpCat.{u}]
  [∀ V : Y.C, (Y.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Y.C, (Y.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : Y.C, (Y.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} X.O).obj A).Additive]
  [(sheafTensor.{u, u, u} Y.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-- **The projection formula as an isomorphism of functors, in the site-indexed tensor
product.** If the map of Stacks 0B56 at `E` is invertible at every `K`, then
`K ↦ Rf_*(Lf^*K ⊗^L E)` is `K ↦ Rf_*E ⊗^L K`. -/
def projectionFormulaNatIso
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : ∀ K, IsIso (ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E K)) :
    derivedPullback f ⋙
        (Stacks.SheafOfModules.derivedTensorProductFunctor X.toRingedSite).flip.obj E ⋙
          derivedPushforward f ≅
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O).obj
        ((derivedPushforward f).obj E) :=
  haveI : ∀ K, IsIso
      ((ProjectionFormulaPerfectOnRingedTopoi.projectionFormulaTransformation f hmos E).app K) := hE
  haveI : IsIso (ProjectionFormulaPerfectOnRingedTopoi.projectionFormulaTransformation f hmos E) :=
    NatIso.isIso_of_isIso_app _
  Functor.isoWhiskerLeft (derivedPullback f)
      (Functor.isoWhiskerRight (derivedTensorObjFlipIso X.toRingedSite E).symm _) ≪≫
    (asIso (ProjectionFormulaPerfectOnRingedTopoi.projectionFormulaTransformation f hmos E)).symm

/-- **Maps out of a perfect object into a derived pullback.** Let `P` be perfect on `X`, let the
projection-formula map of Stacks 0B56 at `P^∨` be invertible at every `K`, and let
`L = Rf_*P^∨` be perfect. Then `Hom(P, Lf^*K) ≅ Hom(L^∨, K)`, naturally in `K`. -/
def derivedPullbackCoyonedaIso
    (P : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hP : X.toRingedSite.IsPerfect P)
    (hpf : ∀ K, IsIso (ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos
      (derivedDual X.toRingedSite P) K))
    (hL : Y.toRingedSite.IsPerfect ((derivedPushforward f).obj (derivedDual X.toRingedSite P))) :
    derivedPullback f ⋙ coyoneda.obj (op P) ≅
      coyoneda.obj (op (derivedDual Y.toRingedSite
        ((derivedPushforward f).obj (derivedDual X.toRingedSite P)))) :=
  let L := (derivedPushforward f).obj (derivedDual X.toRingedSite P)
  Functor.isoWhiskerLeft (derivedPullback f) (coyonedaDualTensorIso X.toRingedSite P hP).symm ≪≫
    Functor.isoWhiskerLeft (derivedPullback f)
      (Functor.isoWhiskerLeft _ (coyoneda.mapIso
        (Stacks.Sheaves.DerivedPullback.derivedPullbackUnitIso f hmos).op)) ≪≫
    Functor.isoWhiskerLeft (derivedPullback f) (Functor.isoWhiskerLeft _
      ((DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).compCoyonedaIso.app
        (op (derivedStructureSheaf Y.toRingedSite)))) ≪≫
    Functor.isoWhiskerLeft (derivedPullback f) (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (projectionFormulaNatIso f hmos _ hpf) _ ≪≫
    Functor.isoWhiskerRight (derivedTensorObjFlipIso Y.toRingedSite L) _ ≪≫
    Functor.isoWhiskerRight
      ((Stacks.SheafOfModules.derivedTensorProductFunctor Y.toRingedSite).flip.mapIso
        (derivedBidualIso Y.toRingedSite L hL)) _ ≪≫
    coyonedaDualTensorIso Y.toRingedSite (derivedDual Y.toRingedSite L)
      (isPerfect_derivedDual Y.toRingedSite L hL)

end Stacks.Cohomology.ProjectionFormulaDualHom

end
