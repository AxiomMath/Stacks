module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatKFlatDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AssociatorPinnedOnRingedTopoi

/-!
# The associativity law of the comparison of Tag 07A4 is determined on K-flat models

Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a morphism of ringed topoi. Both routes of the
associativity law of the comparison of [Stacks, Tag 07A4] — split the outer tensor, then the
inner one, then re-bracket downstairs, versus re-bracket upstairs and then split — are natural
transformations

`Lf^*((P ⊗^L_{𝒪'} Q) ⊗^L_{𝒪'} S) ⟶ Lf^*P ⊗^L_𝒪 (Lf^*Q ⊗^L_𝒪 Lf^*S)`

of functors on `D(𝒪')³`, and they agree as soon as they agree at a triple of K-flat complexes
with flat terms, the models of [Stacks, Tag 06YS]. The re-bracketings are the associativity
constraint `Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociatorHom` of
[Stacks, Tag 0FPT].

## Main definitions

* `Stacks.Sheaves.DerivedPullback.canonicalAssociatorNatTrans`: the associativity constraint of
  [Stacks, Tag 0FPT] as a natural transformation on `D(𝒪')³`.
* `Stacks.Sheaves.DerivedPullback.comparisonThenAssociator` and `associatorThenComparison`: the
  two routes, as transformations of functors on `D(𝒪')³`.

## Main results

* `Stacks.Sheaves.DerivedPullback.comparisonThenAssociator_eq_of_kFlat`: the two routes agree as
  soon as they agree at a triple of K-flat complexes with flat terms.
* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_associator_of_kFlat`: the comparison
  of [Stacks, Tag 07A4] carries the associativity constraint of [Stacks, Tag 0FPT] on `D(𝒪')` to
  the one on `D(𝒪)` for arbitrary `P`, `Q`, `S` in `D(𝒪')` as soon as it does so on those models.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.DerivedTensor.RingedSite
open Stacks.SheafOfModules.DerivedMonoidal (canonicalAssociatorHom)
open Stacks.Cohomology.RelativeCupProductOnRingedTopoi
open scoped CategoryTheory.Prod

namespace Stacks.Sheaves.DerivedPullback

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### The three projections and the two bracketings of a triple tensor product -/

section Triple

variable (W : RingedTopos.{u, u, u})
  [HasSheafify W.J AddCommGrpCat.{u}] [W.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O).obj M).Additive]
  [∀ (P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.O)) ℤ),
    HomologicalComplex.HasMapBifunctor P Q
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O) (ComplexShape.up ℤ)]

/-- The first of three derived modules. -/
abbrev tripleFst :
    DerivedModules W.O × DerivedModules W.O × DerivedModules W.O ⥤ DerivedModules W.O :=
  CategoryTheory.Prod.fst _ _

/-- The second of three derived modules. -/
abbrev tripleSnd :
    DerivedModules W.O × DerivedModules W.O × DerivedModules W.O ⥤ DerivedModules W.O :=
  CategoryTheory.Prod.snd _ _ ⋙ CategoryTheory.Prod.fst _ _

/-- The third of three derived modules. -/
abbrev tripleThd :
    DerivedModules W.O × DerivedModules W.O × DerivedModules W.O ⥤ DerivedModules W.O :=
  CategoryTheory.Prod.snd _ _ ⋙ CategoryTheory.Prod.snd _ _

/-- The functor `(P, Q, S) ↦ (P ⊗^L_𝒪 Q) ⊗^L_𝒪 S` on `D(𝒪)³`. -/
abbrev tripleTensorLeft :=
  Functor.prod' (Functor.prod' (tripleFst W) (tripleSnd W) ⋙ uncurriedDerivedTensor W)
      (tripleThd W) ⋙
    uncurriedDerivedTensor W

/-- The functor `(P, Q, S) ↦ P ⊗^L_𝒪 (Q ⊗^L_𝒪 S)` on `D(𝒪)³`. -/
abbrev tripleTensorRight :=
  Functor.prod' (tripleFst W)
      (Functor.prod' (tripleSnd W) (tripleThd W) ⋙ uncurriedDerivedTensor W) ⋙
    uncurriedDerivedTensor W

/-- **The associativity constraint of [Stacks, Tag 0FPT] as a natural transformation** on
`D(𝒪)³`, with components `Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociatorHom`. -/
def canonicalAssociatorNatTrans : tripleTensorLeft W ⟶ tripleTensorRight W where
  app T := canonicalAssociatorHom W.O T.1 T.2.1 T.2.2
  naturality _ _ g := canonicalAssociatorHom_naturality W g.1 g.2.1 g.2.2

end Triple

/-! ### The two routes of the associativity law -/

section Routes

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor P Q
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor P Q
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-- The derived pullback in all three variables. -/
abbrev pullbackTriple :=
  (derivedPullback f).prod ((derivedPullback f).prod (derivedPullback f))

/-- **The first route of the associativity law**, as a transformation
`(P, Q, S) ↦ Lf^*((P ⊗^L Q) ⊗^L S) ⟶ Lf^*P ⊗^L (Lf^*Q ⊗^L Lf^*S)` on `D(𝒪')³`: the comparison
of [Stacks, Tag 07A4] in the outer and then the inner tensor factor, followed by the
associativity constraint of the three derived pullbacks. -/
def comparisonThenAssociator :
    tripleTensorLeft Y ⋙ derivedPullback f ⟶ pullbackTriple f ⋙ tripleTensorRight X :=
  Functor.whiskerLeft
      (Functor.prod' (Functor.prod' (tripleFst Y) (tripleSnd Y) ⋙ uncurriedDerivedTensor Y)
        (tripleThd Y))
      (derivedPullbackTensorIso f hmos).hom ≫
    Functor.whiskerRight
        (NatTrans.prod'
          (Functor.whiskerLeft (Functor.prod' (tripleFst Y) (tripleSnd Y))
            (derivedPullbackTensorIso f hmos).hom)
          (NatTrans.id (tripleThd Y ⋙ derivedPullback f)))
        (uncurriedDerivedTensor X) ≫
      Functor.whiskerLeft (pullbackTriple f) (canonicalAssociatorNatTrans X)

/-- **The second route**: the derived pullback of the associativity constraint, followed by the
comparison of [Stacks, Tag 07A4] in the outer and then the inner tensor factor. -/
def associatorThenComparison :
    tripleTensorLeft Y ⋙ derivedPullback f ⟶ pullbackTriple f ⋙ tripleTensorRight X :=
  Functor.whiskerRight (canonicalAssociatorNatTrans Y) (derivedPullback f) ≫
    Functor.whiskerLeft
        (Functor.prod' (tripleFst Y)
          (Functor.prod' (tripleSnd Y) (tripleThd Y) ⋙ uncurriedDerivedTensor Y))
        (derivedPullbackTensorIso f hmos).hom ≫
      Functor.whiskerRight
        (NatTrans.prod' (NatTrans.id (tripleFst Y ⋙ derivedPullback f))
          (Functor.whiskerLeft (Functor.prod' (tripleSnd Y) (tripleThd Y))
            (derivedPullbackTensorIso f hmos).hom))
        (uncurriedDerivedTensor X)

/-- **The associativity law of the comparison of [Stacks, Tag 07A4] at a triple of derived
modules**, as a proposition: the comparison carries the associativity constraint of
[Stacks, Tag 0FPT] on `D(𝒪')` to the one on `D(𝒪)`. One route splits the outer tensor, then the
inner one, then re-brackets downstairs; the other re-brackets upstairs and then splits. -/
def DerivedPullbackTensorIsoAssociator (P Q S : DerivedModules Y.O) : Prop :=
  (derivedPullbackTensorIso f hmos).hom.app ((uncurriedDerivedTensor Y).obj (P, Q), S) ≫
      (uncurriedDerivedTensor X).map
          ((derivedPullbackTensorIso f hmos).hom.app (P, Q) ×ₘ
            𝟙 ((derivedPullback f).obj S)) ≫
        canonicalAssociatorHom X.O ((derivedPullback f).obj P) ((derivedPullback f).obj Q)
          ((derivedPullback f).obj S) =
    (derivedPullback f).map (canonicalAssociatorHom Y.O P Q S) ≫
      (derivedPullbackTensorIso f hmos).hom.app (P, (uncurriedDerivedTensor Y).obj (Q, S)) ≫
        (uncurriedDerivedTensor X).map
          (𝟙 ((derivedPullback f).obj P) ×ₘ
            (derivedPullbackTensorIso f hmos).hom.app (Q, S))

/-- The components of `Stacks.Sheaves.DerivedPullback.comparisonThenAssociator` are the left-hand
side of the associativity law. -/
theorem comparisonThenAssociator_app (P Q S : DerivedModules Y.O) :
    (comparisonThenAssociator f hmos).app (P, Q, S) =
      (derivedPullbackTensorIso f hmos).hom.app ((uncurriedDerivedTensor Y).obj (P, Q), S) ≫
        (uncurriedDerivedTensor X).map
            ((derivedPullbackTensorIso f hmos).hom.app (P, Q) ×ₘ
              𝟙 ((derivedPullback f).obj S)) ≫
          canonicalAssociatorHom X.O ((derivedPullback f).obj P) ((derivedPullback f).obj Q)
            ((derivedPullback f).obj S) :=
  rfl

/-- The components of `Stacks.Sheaves.DerivedPullback.associatorThenComparison` are the
right-hand side of the associativity law. -/
theorem associatorThenComparison_app (P Q S : DerivedModules Y.O) :
    (associatorThenComparison f hmos).app (P, Q, S) =
      (derivedPullback f).map (canonicalAssociatorHom Y.O P Q S) ≫
        (derivedPullbackTensorIso f hmos).hom.app
            (P, (uncurriedDerivedTensor Y).obj (Q, S)) ≫
          (uncurriedDerivedTensor X).map
            (𝟙 ((derivedPullback f).obj P) ×ₘ
              (derivedPullbackTensorIso f hmos).hom.app (Q, S)) :=
  rfl

/-! ### The descent to arbitrary derived modules -/

/-- **The two routes of the associativity law agree as soon as they agree on K-flat models.**
The transformations `Lf^*((P ⊗^L Q) ⊗^L S) ⟶ Lf^*P ⊗^L (Lf^*Q ⊗^L Lf^*S)` of functors on
`D(𝒪')³` are equal if they agree at every triple of K-flat complexes with flat terms. -/
theorem comparisonThenAssociator_eq_of_kFlat
    (h : ∀ K L M : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ,
      CochainComplex.KFlatBifunctor.KFlat
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K →
      CochainComplex.KFlatBifunctor.KFlat
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L →
      CochainComplex.KFlatBifunctor.KFlat
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) M →
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) →
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) →
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) →
      DerivedPullbackTensorIsoAssociator f hmos (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)) :
    comparisonThenAssociator f hmos = associatorThenComparison f hmos :=
  natTrans_ext_of_flatKFlat₃ Y _ _ fun K L M hK hL hM hfK hfL hfM =>
    (comparisonThenAssociator_app f hmos _ _ _).trans
      ((h K L M hK hL hM hfK hfL hfM).trans (associatorThenComparison_app f hmos _ _ _).symm)

/-- **The comparison of [Stacks, Tag 07A4] carries the associativity constraint of
[Stacks, Tag 0FPT] on `D(𝒪')` to the one on `D(𝒪)` for arbitrary derived modules, as soon as it
does so on K-flat models.** -/
theorem derivedPullbackTensorIso_associator_of_kFlat
    (h : ∀ K L M : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ,
      CochainComplex.KFlatBifunctor.KFlat
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K →
      CochainComplex.KFlatBifunctor.KFlat
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L →
      CochainComplex.KFlatBifunctor.KFlat
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) M →
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) →
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) →
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) →
      DerivedPullbackTensorIsoAssociator f hmos (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M))
    (P Q S : DerivedModules Y.O) :
    DerivedPullbackTensorIsoAssociator f hmos P Q S :=
  (comparisonThenAssociator_app f hmos P Q S).symm.trans
    ((congrArg (fun τ => τ.app (P, Q, S)) (comparisonThenAssociator_eq_of_kFlat f hmos h)).trans
      (associatorThenComparison_app f hmos P Q S))

end Routes

end Stacks.Sheaves.DerivedPullback

end
