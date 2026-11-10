module

public import
 StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorModelOfToposHom

/-!
# The associativity law of the comparison of Tag 07A4, for a morphism of ringed topoi

Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a morphism of ringed topoi in the two-field sense of
[Stacks, Tag 01D3], part (2): a morphism of the underlying *topoi* together with the structure
map, with no functor between the underlying sites.  The comparison of [Stacks, Tag 07A4],

`Lf^*(P ⊗^L_{𝒪'} Q) ≅ Lf^*P ⊗^L_𝒪 Lf^*Q`

(`Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso`), carries the associativity
constraint of the monoidal derived category of [Stacks, Tag 0FPT] on `D(𝒪')` to the one on
`D(𝒪)`, for **arbitrary** `P`, `Q`, `S` in `D(𝒪')`: both routes

`Lf^*((P ⊗^L Q) ⊗^L S) ⟶ Lf^*P ⊗^L (Lf^*Q ⊗^L Lf^*S)`

— split the outer tensor, then the inner one, then re-bracket downstairs; or re-bracket upstairs
and then split — agree.  That is, `Lf^*` is a monoidal functor for the derived tensor product.

## Main results

* `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_associator_app_of_kFlat`:
  the law at a triple of K-flat complexes with flat terms.
* `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_associator_of_kFlat`: the
  law at every triple of objects of `D(𝒪')`, as soon as it holds at those models.
* `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_associator`: the law for
  every morphism of ringed topoi and every triple of objects of `D(𝒪')`.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FPL](https://stacks.math.columbia.edu/tag/0FPL)
* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex)
open Stacks.DerivedTensor.RingedSite
open Stacks.SheafOfModules.DerivedMonoidal (canonicalAssociatorHom)
open Stacks.Cohomology.RelativeCupProductOnRingedTopoi
open scoped CategoryTheory.Prod

namespace Stacks.Sheaves.DerivedPullback.OfToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

section Routes

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : AlgebraicGeometry.RingedToposHom X Y)

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
      (derivedPullbackTensorIso f).hom ≫
    Functor.whiskerRight
        (NatTrans.prod'
          (Functor.whiskerLeft (Functor.prod' (tripleFst Y) (tripleSnd Y))
            (derivedPullbackTensorIso f).hom)
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
        (derivedPullbackTensorIso f).hom ≫
      Functor.whiskerRight
        (NatTrans.prod' (NatTrans.id (tripleFst Y ⋙ derivedPullback f))
          (Functor.whiskerLeft (Functor.prod' (tripleSnd Y) (tripleThd Y))
            (derivedPullbackTensorIso f).hom))
        (uncurriedDerivedTensor X)

/-- **The associativity law of the comparison of [Stacks, Tag 07A4] at a triple of derived
modules**, as a proposition: the comparison carries the associativity constraint of
[Stacks, Tag 0FPT] on `D(𝒪')` to the one on `D(𝒪)`.  One route splits the outer tensor, then the
inner one, then re-brackets downstairs; the other re-brackets upstairs and then splits. -/
def DerivedPullbackTensorIsoAssociator (P Q S : DerivedModules Y.O) : Prop :=
  (derivedPullbackTensorIso f).hom.app ((uncurriedDerivedTensor Y).obj (P, Q), S) ≫
      (uncurriedDerivedTensor X).map
          ((derivedPullbackTensorIso f).hom.app (P, Q) ×ₘ
            𝟙 ((derivedPullback f).obj S)) ≫
        canonicalAssociatorHom X.O ((derivedPullback f).obj P) ((derivedPullback f).obj Q)
          ((derivedPullback f).obj S) =
    (derivedPullback f).map (canonicalAssociatorHom Y.O P Q S) ≫
      (derivedPullbackTensorIso f).hom.app (P, (uncurriedDerivedTensor Y).obj (Q, S)) ≫
        (uncurriedDerivedTensor X).map
          (𝟙 ((derivedPullback f).obj P) ×ₘ
            (derivedPullbackTensorIso f).hom.app (Q, S))

/-- The components of `comparisonThenAssociator` are the left-hand
side of the associativity law. -/
theorem comparisonThenAssociator_app (P Q S : DerivedModules Y.O) :
    (comparisonThenAssociator f).app (P, Q, S) =
      (derivedPullbackTensorIso f).hom.app ((uncurriedDerivedTensor Y).obj (P, Q), S) ≫
        (uncurriedDerivedTensor X).map
            ((derivedPullbackTensorIso f).hom.app (P, Q) ×ₘ
              𝟙 ((derivedPullback f).obj S)) ≫
          canonicalAssociatorHom X.O ((derivedPullback f).obj P) ((derivedPullback f).obj Q)
            ((derivedPullback f).obj S) :=
  rfl

/-- The components of `Stacks.Sheaves.DerivedPullback.OfToposHom.associatorThenComparison` are the
right-hand side of the associativity law. -/
theorem associatorThenComparison_app (P Q S : DerivedModules Y.O) :
    (associatorThenComparison f).app (P, Q, S) =
      (derivedPullback f).map (canonicalAssociatorHom Y.O P Q S) ≫
        (derivedPullbackTensorIso f).hom.app
            (P, (uncurriedDerivedTensor Y).obj (Q, S)) ≫
          (uncurriedDerivedTensor X).map
            (𝟙 ((derivedPullback f).obj P) ×ₘ
              (derivedPullbackTensorIso f).hom.app (Q, S)) :=
  rfl

/-! ### The descent to arbitrary derived modules -/

/-- The two routes of the associativity law, as transformations
`Lf^*((P ⊗^L Q) ⊗^L S) ⟶ Lf^*P ⊗^L (Lf^*Q ⊗^L Lf^*S)` of functors on `D(𝒪')³`, agree as soon as
they agree at every triple of K-flat complexes with flat terms. -/
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
      DerivedPullbackTensorIsoAssociator f (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)) :
    comparisonThenAssociator f = associatorThenComparison f :=
  natTrans_ext_of_flatKFlat₃ Y _ _ fun K L M hK hL hM hfK hfL hfM ↦
    (comparisonThenAssociator_app f _ _ _).trans
      ((h K L M hK hL hM hfK hfL hfM).trans (associatorThenComparison_app f _ _ _).symm)

/-- **The comparison of [Stacks, Tag 07A4] carries the associativity constraint of
[Stacks, Tag 0FPT] on `D(𝒪')` to the one on `D(𝒪)` for arbitrary derived modules, as soon as it
does so on K-flat complexes with flat terms.**  The three objects `P`, `Q`, `S` are arbitrary
objects of `D(𝒪')`. -/
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
      DerivedPullbackTensorIsoAssociator f (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M))
    (P Q S : DerivedModules Y.O) :
    DerivedPullbackTensorIsoAssociator f P Q S :=
  (comparisonThenAssociator_app f P Q S).symm.trans
    ((congrArg (fun τ ↦ τ.app (P, Q, S)) (comparisonThenAssociator_eq_of_kFlat f h)).trans
      (associatorThenComparison_app f P Q S))

end Routes

section AbstractBridges

attribute [local instance] monoidalModules symmetricModules
  monoidalPreadditiveModules monoidalClosedModules hasTensorModules monoidalComplexes

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ ⥤
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  (d : ∀ A B : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ,
    P.obj (totalObj Y A B) ⟶ totalObj X (P.obj A) (P.obj B))

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The left-hand side of an associativity square for a family of maps
`P Tot(A ⊗ B) ⟶ Tot(PA ⊗ PB)`, read at the two pinnings of the total tensor complex**: the one
through `Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair`, at which the constraints of
[Stacks, Tag 0FPT] are stated, and the one through `Stacks.Sheaves.DerivedPullback.totalObj`. -/
theorem totalComplexPair_associator_lhs_eq
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (d ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)) M :
        P.obj ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj
            ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L), M)) ⟶
          (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
              (P.obj ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
                (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)),
                P.obj M)) ≫
        totalComplexMapRight X (d K L :
            P.obj ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)) ⟶
              (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
                (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
                  (P.obj K, P.obj L)) (P.obj M) ≫
          complexAssociatorPair X (P.obj K) (P.obj L) (P.obj M) =
      d (totalObj Y K L) M ≫ totalComplexMapRightTopos X (d K L) (P.obj M) ≫
          complexAssociatorPairTopos X (P.obj K) (P.obj L) (P.obj M) := by
  rw [totalComplexMapRight_eq_topos]
  rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The right-hand side of an associativity square for a family of maps
`P Tot(A ⊗ B) ⟶ Tot(PA ⊗ PB)`, read at the two pinnings of the total tensor complex**; the
companion of `totalComplexPair_associator_lhs_eq`. -/
theorem totalComplexPair_associator_rhs_eq
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    P.map (complexAssociatorPair Y K L M) ≫
        (d K ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M)) :
          P.obj ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj
              (K, (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
                (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M))) ⟶
            (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
                (P.obj K, P.obj ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
                  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj
                    (L, M)))) ≫
          totalComplexMapLeft X (P.obj K) (d L M :
            P.obj ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M)) ⟶
              (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
                (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
                  (P.obj L, P.obj M)) =
      P.map (complexAssociatorPairTopos Y K L M) ≫ d K (totalObj Y L M) ≫
          totalComplexMapLeftTopos X (P.obj K) (d L M) :=
  (congrArg (fun z ↦ P.map (complexAssociatorPair Y K L M) ≫
      d K ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M)) ≫ z)
    (totalComplexMapLeft_eq_topos X (P.obj K) (d L M :
      P.obj ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M)) ⟶
        (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
            (P.obj L, P.obj M)))).trans rfl

end AbstractBridges

section Models

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : AlgebraicGeometry.RingedToposHom X Y)

/-- **The comparison `f^*Tot(K ⊗_{𝒪'} L) ⟶ Tot(f^*K ⊗_𝒪 f^*L)` of [Stacks, Tag 03EL]**, with
its source and target written through
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` rather than through
`HomologicalComplex.mapBifunctor`. -/
def pullbackTensorComplexPair
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackComplex f).obj
        ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)) ⟶
      (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
          ((pullbackComplex f).obj K, (pullbackComplex f).obj L) :=
  (pullbackTensorTotalIso f.toModulesHom K L).hom

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- `pullbackTensorComplexPair` *is* the comparison of total
tensor complexes of [Stacks, Tag 03EL]. -/
theorem pullbackTensorComplexPair_eq
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    pullbackTensorComplexPair f K L = (pullbackTensorComplexIso f K L).hom :=
  rfl

/-- **The model of `Lf^*(QK ⊗^L_{𝒪'} QL)` on a pair of complexes**: the comparison of
[Stacks, Tag 06YY] at the total tensor complex, followed by the comparison
`f^*Tot(K ⊗_{𝒪'} L) ≅ Tot(f^*K ⊗_𝒪 f^*L)` of [Stacks, Tag 03EL], with the total tensor complexes
written through `Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair`. -/
def pullbackTensorModel
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (derivedPullback f).obj
        (DerivedCategory.Q.obj
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L))) ⟶
      DerivedCategory.Q.obj
        ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
            ((pullbackComplex f).obj K, (pullbackComplex f).obj L)) :=
  pullbackComparisonQ f
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)) ≫
    DerivedCategory.Q.map (pullbackTensorComplexPair f K L)

/-- `Stacks.Sheaves.DerivedPullback.OfToposHom.pullbackTensorModel` is the comparison of
[Stacks, Tag 06YY] followed by the comparison of total tensor complexes of
[Stacks, Tag 03EL], with both written at the
`Stacks.SheafOfModules.Tensor.tensorComplex` spelling. -/
theorem pullbackTensorModel_eq
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    pullbackTensorModel f K L =
      pullbackComparisonQ f (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj K).obj L) ≫
        DerivedCategory.Q.map (pullbackTensorComplexIso f K L).hom :=
  rfl

/-- **The model of `Lf^*((QK ⊗^L QL) ⊗^L QM)`**: the model of
`pullbackTensorModel` at the pair `(Tot(K ⊗ L), M)`, followed by
the comparison of [Stacks, Tag 03EL] in the first tensor factor. -/
def pullbackTensorModelTripleLeft
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (derivedPullback f).obj
        (DerivedCategory.Q.obj
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj
            ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L), M))) ⟶
      DerivedCategory.Q.obj
        ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
              ((pullbackComplex f).obj K, (pullbackComplex f).obj L),
            (pullbackComplex f).obj M)) :=
  pullbackTensorModel f
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)) M ≫
    DerivedCategory.Q.map
      (totalComplexMapRight X (pullbackTensorComplexPair f K L)
        ((pullbackComplex f).obj M))

/-- **The model of `Lf^*(QK ⊗^L (QL ⊗^L QM))`**: the model of `pullbackTensorModel` at the pair
`(K, Tot(L ⊗ M))`, followed by the comparison of [Stacks, Tag 03EL] in the second tensor
factor. -/
def pullbackTensorModelTripleRight
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (derivedPullback f).obj
        (DerivedCategory.Q.obj
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj
            (K, (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M)))) ⟶
      DerivedCategory.Q.obj
        ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
          ((pullbackComplex f).obj K,
            (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
                ((pullbackComplex f).obj L, (pullbackComplex f).obj M))) :=
  pullbackTensorModel f K
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M)) ≫
    DerivedCategory.Q.map
      (totalComplexMapLeft X ((pullbackComplex f).obj K)
        (pullbackTensorComplexPair f L M))

/-! ### The two models of the triple tensor product, matched -/

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- **The left-hand side of the coherence of [Stacks, Tag 03EL], read at the
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` spelling.** -/
theorem pullbackTensorComplexPair_associator_lhs
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    pullbackTensorComplexPair f
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)) M ≫
        totalComplexMapRight X (pullbackTensorComplexPair f K L)
            ((pullbackComplex f).obj M) ≫
          complexAssociatorPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
            ((pullbackComplex f).obj M) =
      (pullbackTensorTotalIso f.toModulesHom (totalObj Y K L) M).hom ≫
        totalComplexMapRightTopos X ((pullbackTensorTotalIso f.toModulesHom K L).hom)
            ((pullbackComplex f).obj M) ≫
          complexAssociatorPairTopos X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
            ((pullbackComplex f).obj M) :=
  totalComplexPair_associator_lhs_eq (pullbackComplex f)
    (fun A B ↦ (pullbackTensorTotalIso f.toModulesHom A B).hom) K L M

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- **The right-hand side of the coherence of [Stacks, Tag 03EL], read at the
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` spelling**; the companion of
`Stacks.Sheaves.DerivedPullback.OfToposHom.pullbackTensorComplexPair_associator_lhs`. -/
theorem pullbackTensorComplexPair_associator_rhs
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackComplex f).map (complexAssociatorPair Y K L M) ≫
        pullbackTensorComplexPair f K
            ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M)) ≫
          totalComplexMapLeft X ((pullbackComplex f).obj K)
            (pullbackTensorComplexPair f L M) =
      (pullbackComplex f).map (complexAssociatorPairTopos Y K L M) ≫
        (pullbackTensorTotalIso f.toModulesHom K (totalObj Y L M)).hom ≫
          totalComplexMapLeftTopos X ((pullbackComplex f).obj K)
            ((pullbackTensorTotalIso f.toModulesHom L M).hom) :=
  totalComplexPair_associator_rhs_eq (pullbackComplex f)
    (fun A B ↦ (pullbackTensorTotalIso f.toModulesHom A B).hom) K L M

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- **The comparison of [Stacks, Tag 03EL] on total complexes is compatible with the associator
of total tensor complexes**, with every term written at the
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` spelling. -/
theorem pullbackTensorComplexPair_associator_pair
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    pullbackTensorComplexPair f
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)) M ≫
        totalComplexMapRight X (pullbackTensorComplexPair f K L)
            ((pullbackComplex f).obj M) ≫
          complexAssociatorPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
            ((pullbackComplex f).obj M) =
      (pullbackComplex f).map (complexAssociatorPair Y K L M) ≫
        pullbackTensorComplexPair f K
            ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M)) ≫
          totalComplexMapLeft X ((pullbackComplex f).obj K)
            (pullbackTensorComplexPair f L M) :=
  (pullbackTensorComplexPair_associator_lhs f K L M).trans
    ((pullbackTensorTotalIso_associator_pair f K L M).trans
      (pullbackTensorComplexPair_associator_rhs f K L M).symm)

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- `pullbackTensorComplexPair_associator_pair` in the derived
category, with the three factors of each side carried across `DerivedCategory.Q` separately. -/
theorem pullbackTensorComplexPair_associator_pair_Q
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    DerivedCategory.Q.map (pullbackTensorComplexPair f
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)) M) ≫
        DerivedCategory.Q.map
            (totalComplexMapRight X (pullbackTensorComplexPair f K L)
              ((pullbackComplex f).obj M)) ≫
          DerivedCategory.Q.map
            (complexAssociatorPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
              ((pullbackComplex f).obj M)) =
      DerivedCategory.Q.map ((pullbackComplex f).map (complexAssociatorPair Y K L M)) ≫
        DerivedCategory.Q.map (pullbackTensorComplexPair f K
            ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M))) ≫
          DerivedCategory.Q.map
            (totalComplexMapLeft X ((pullbackComplex f).obj K)
              (pullbackTensorComplexPair f L M)) := by
  have h := congrArg DerivedCategory.Q.map (pullbackTensorComplexPair_associator_pair f K L M)
  rwa [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp] at h

/-- **The model of `Lf^*(QK ⊗^L QL)` carries the associator of complexes to the associator of
complexes**, at the `Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` spelling. -/
theorem pullbackTensorModel_assoc_pair
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    pullbackTensorModelTripleLeft f K L M ≫
        DerivedCategory.Q.map
          (complexAssociatorPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
            ((pullbackComplex f).obj M)) =
      (derivedPullback f).map
          (DerivedCategory.Q.map (complexAssociatorPair Y K L M)) ≫
        pullbackTensorModelTripleRight f K L M := by
  dsimp only [pullbackTensorModelTripleLeft, pullbackTensorModelTripleRight,
    pullbackTensorModel]
  simp only [Category.assoc]
  rw [pullbackTensorComplexPair_associator_pair_Q f K L M,
    reassoc_of% (pullbackComparisonQ_naturality f (complexAssociatorPair Y K L M))]

/-- **The model identification of [Stacks, Tag 07A4] at a pair of K-flat complexes with flat
terms**: the comparison `Lf^*(QK ⊗^L_{𝒪'} QL) ⟶ Lf^*QK ⊗^L_𝒪 Lf^*QL`, followed by the
comparison of [Stacks, Tag 06YY] in each tensor factor and the comparison of
[Stacks, Tag 06YU], is the derived pullback of the comparison of [Stacks, Tag 06YU] followed by
`Stacks.Sheaves.DerivedPullback.OfToposHom.pullbackTensorModel`. -/
theorem derivedPullbackTensorIso_hom_app_comp_comparisonPair
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        (uncurriedDerivedTensor X).map
            (pullbackComparisonQ f K ×ₘ pullbackComparisonQ f L) ≫
          comparisonPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
            (kFlat_pullbackComplex_pinned f K hK hfK)
            (kFlat_pullbackComplex_pinned f L hL hfL) =
      (derivedPullback f).map (comparisonPair Y K L hK hL) ≫ pullbackTensorModel f K L := by
  rw [comparisonPair_eq_toTensor, comparisonPair_eq_toTensor, pullbackTensorModel_eq]
  exact (toTensor_square_of_kFlat f K L
    ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O K).mp hK)
    ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O L).mp hL) hfK hfL).symm

/-! ### The model identifications at the two triples -/

/-- The model identification of [Stacks, Tag 07A4] at the pair `(Tot(K ⊗ L), M)`, read against
the model `Tot(f^*K ⊗ f^*L)` of the first factor, as a proposition. -/
def ModelIdentificationLeft
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    Prop :=
  (derivedPullbackTensorIso f).hom.app
        (DerivedCategory.Q.obj
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)),
          DerivedCategory.Q.obj M) ≫
      (uncurriedDerivedTensor X).map
          (pullbackTensorModel f K L ×ₘ pullbackComparisonQ f M) ≫
        comparisonPair X
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
              ((pullbackComplex f).obj K, (pullbackComplex f).obj L))
          ((pullbackComplex f).obj M)
          (kFlat_totalComplexPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
            (kFlat_pullbackComplex_pinned f K hK hfK)
            (kFlat_pullbackComplex_pinned f L hL hfL))
          (kFlat_pullbackComplex_pinned f M hM hfM) =
    (derivedPullback f).map
        (comparisonPair Y
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)) M
          (kFlat_totalComplexPair Y K L hK hL) hM) ≫
      (pullbackTensorModelTripleLeft f K L M)

/-- **The model identification of [Stacks, Tag 07A4] at the pair `(Tot(K ⊗ L), M)`, re-read
against the model `Tot(f^*K ⊗ f^*L)` of the first factor.** -/
theorem derivedPullbackTensorIso_hom_app_comp_comparisonPair_left
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    ModelIdentificationLeft f K L M hK hL hM hfK hfL hfM :=
  bifunctor_comparison_model_comp_left (uncurriedDerivedTensor Y) (uncurriedDerivedTensor X)
    (derivedPullbackTensorIso f).hom
    (derivedPullbackTensorIso_hom_app_comp_comparisonPair f
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)) M
      (kFlat_totalComplexPair Y K L hK hL) hM
      (isFlat_totalComplexPair_X Y K L hfK hfL) hfM)
    (comparisonPair_naturality_right X (pullbackTensorComplexPair f K L)
      (kFlat_pullbackComplex_pinned f
        ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L))
        (kFlat_totalComplexPair Y K L hK hL) (isFlat_totalComplexPair_X Y K L hfK hfL))
      (kFlat_totalComplexPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
        (kFlat_pullbackComplex_pinned f K hK hfK)
        (kFlat_pullbackComplex_pinned f L hL hfL))
      (kFlat_pullbackComplex_pinned f M hM hfM))

/-- The model identification of [Stacks, Tag 07A4] at the pair `(K, Tot(L ⊗ M))`, read against
the model `Tot(f^*L ⊗ f^*M)` of the second factor, as a proposition. -/
def ModelIdentificationRight
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    Prop :=
  (derivedPullbackTensorIso f).hom.app
        (DerivedCategory.Q.obj K,
          DerivedCategory.Q.obj
            ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M))) ≫
      (uncurriedDerivedTensor X).map
          (pullbackComparisonQ f K ×ₘ pullbackTensorModel f L M) ≫
        comparisonPair X ((pullbackComplex f).obj K)
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
              ((pullbackComplex f).obj L, (pullbackComplex f).obj M))
          (kFlat_pullbackComplex_pinned f K hK hfK)
          (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
            (kFlat_pullbackComplex_pinned f L hL hfL)
            (kFlat_pullbackComplex_pinned f M hM hfM)) =
    (derivedPullback f).map
        (comparisonPair Y K
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M)) hK
          (kFlat_totalComplexPair Y L M hL hM)) ≫
      (pullbackTensorModelTripleRight f K L M)

/-- **The model identification of [Stacks, Tag 07A4] at the pair `(K, Tot(L ⊗ M))`, re-read
against the model `Tot(f^*L ⊗ f^*M)` of the second factor.** -/
theorem derivedPullbackTensorIso_hom_app_comp_comparisonPair_right
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    ModelIdentificationRight f K L M hK hL hM hfK hfL hfM :=
  bifunctor_comparison_model_comp_right (uncurriedDerivedTensor Y) (uncurriedDerivedTensor X)
    (derivedPullbackTensorIso f).hom
    (derivedPullbackTensorIso_hom_app_comp_comparisonPair f K
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M))
      hK (kFlat_totalComplexPair Y L M hL hM) hfK
      (isFlat_totalComplexPair_X Y L M hfL hfM))
    (comparisonPair_naturality_left X (pullbackTensorComplexPair f L M)
      (kFlat_pullbackComplex_pinned f K hK hfK)
      (kFlat_pullbackComplex_pinned f
        ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M))
        (kFlat_totalComplexPair Y L M hL hM) (isFlat_totalComplexPair_X Y L M hfL hfM))
      (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
        (kFlat_pullbackComplex_pinned f L hL hfL)
        (kFlat_pullbackComplex_pinned f M hM hfM)))

/-! ### The corner of the associativity square -/

/-- The pair of comparisons of [Stacks, Tag 06YY] in the last two factors, tensored and followed
by the comparison of [Stacks, Tag 06YU], tensored against the comparison in the first factor and
followed by the comparison of [Stacks, Tag 06YU] again, is an isomorphism on K-flat complexes
with flat terms. -/
theorem isIso_modelCorner
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    IsIso ((uncurriedDerivedTensor X).map
          (pullbackComparisonQ f K ×ₘ
            ((uncurriedDerivedTensor X).map
                (pullbackComparisonQ f L ×ₘ pullbackComparisonQ f M) ≫
              comparisonPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
                (kFlat_pullbackComplex_pinned f L hL hfL)
                (kFlat_pullbackComplex_pinned f M hM hfM))) ≫
        comparisonPair X ((pullbackComplex f).obj K)
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
              ((pullbackComplex f).obj L, (pullbackComplex f).obj M))
          (kFlat_pullbackComplex_pinned f K hK hfK)
          (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
            (kFlat_pullbackComplex_pinned f L hL hfL)
            (kFlat_pullbackComplex_pinned f M hM hfM))) := by
  have hLx := kFlat_pullbackComplex_pinned f L hL hfL
  have hMx := kFlat_pullbackComplex_pinned f M hM hfM
  have := isIso_pullbackComparisonQ f K hK hfK
  have := isIso_pullbackComparisonQ f L hL hfL
  have := isIso_pullbackComparisonQ f M hM hfM
  have := isIso_comparisonPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M) hLx hMx
  have := isIso_comparisonPair X ((pullbackComplex f).obj K)
    ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
        ((pullbackComplex f).obj L, (pullbackComplex f).obj M))
    (kFlat_pullbackComplex_pinned f K hK hfK)
    (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M) hLx hMx)
  have : IsIso (pullbackComparisonQ f L ×ₘ pullbackComparisonQ f M) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have : IsIso (pullbackComparisonQ f K ×ₘ ((uncurriedDerivedTensor X).map
      (pullbackComparisonQ f L ×ₘ pullbackComparisonQ f M) ≫
        comparisonPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M) hLx hMx)) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  infer_instance

/-- The composite shown invertible in `Stacks.Sheaves.DerivedPullback.OfToposHom.isIso_modelCorner`
is a monomorphism. -/
theorem mono_modelCorner
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    Mono ((uncurriedDerivedTensor X).map
          (pullbackComparisonQ f K ×ₘ
            ((uncurriedDerivedTensor X).map
                (pullbackComparisonQ f L ×ₘ pullbackComparisonQ f M) ≫
              comparisonPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
                (kFlat_pullbackComplex_pinned f L hL hfL)
                (kFlat_pullbackComplex_pinned f M hM hfM))) ≫
        comparisonPair X ((pullbackComplex f).obj K)
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
              ((pullbackComplex f).obj L, (pullbackComplex f).obj M))
          (kFlat_pullbackComplex_pinned f K hK hfK)
          (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
            (kFlat_pullbackComplex_pinned f L hL hfL)
            (kFlat_pullbackComplex_pinned f M hM hfM))) := by
  have := isIso_modelCorner f K L M hK hL hM hfK hfL hfM
  infer_instance

/-! ### The five bundles of the associativity square -/

/-- **The two associativity laws of the models and the naturality of the constraint of
[Stacks, Tag 0FPT]**, as a proposition.  The source models are the comparison of
[Stacks, Tag 06YU] on `D(𝒪')` at the spelling
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.comparisonPair`, the target models are the
same on `D(𝒪)`, the two re-bracketings are the associator of total tensor complexes
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.complexAssociatorPair` on each side, and the
constraint is `Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociatorHom` of
[Stacks, Tag 0FPT]. -/
def AssocLaws
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    Prop :=
  AssocModelLaws (derivedPullback f) (uncurriedDerivedTensor Y) (uncurriedDerivedTensor X)
    (canonicalAssociatorHom Y.O (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
      (DerivedCategory.Q.obj M))
    (canonicalAssociatorHom X.O (DerivedCategory.Q.obj ((pullbackComplex f).obj K))
      (DerivedCategory.Q.obj ((pullbackComplex f).obj L))
      (DerivedCategory.Q.obj ((pullbackComplex f).obj M)))
    (canonicalAssociatorHom X.O ((derivedPullback f).obj (DerivedCategory.Q.obj K))
      ((derivedPullback f).obj (DerivedCategory.Q.obj L))
      ((derivedPullback f).obj (DerivedCategory.Q.obj M)))
    (pullbackComparisonQ f K) (pullbackComparisonQ f L) (pullbackComparisonQ f M)
    (comparisonPair Y K L hK hL) (comparisonPair Y L M hL hM)
    (comparisonPair Y
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)) M
      (kFlat_totalComplexPair Y K L hK hL) hM)
    (comparisonPair Y K
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M)) hK
      (kFlat_totalComplexPair Y L M hL hM))
    (DerivedCategory.Q.map (complexAssociatorPair Y K L M))
    (comparisonPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
      (kFlat_pullbackComplex_pinned f K hK hfK)
      (kFlat_pullbackComplex_pinned f L hL hfL))
    (comparisonPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
      (kFlat_pullbackComplex_pinned f L hL hfL)
      (kFlat_pullbackComplex_pinned f M hM hfM))
    (comparisonPair X
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
          ((pullbackComplex f).obj K, (pullbackComplex f).obj L))
      ((pullbackComplex f).obj M)
      (kFlat_totalComplexPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
        (kFlat_pullbackComplex_pinned f K hK hfK)
        (kFlat_pullbackComplex_pinned f L hL hfL))
      (kFlat_pullbackComplex_pinned f M hM hfM))
    (comparisonPair X ((pullbackComplex f).obj K)
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
          ((pullbackComplex f).obj L, (pullbackComplex f).obj M))
      (kFlat_pullbackComplex_pinned f K hK hfK)
      (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
        (kFlat_pullbackComplex_pinned f L hL hfL)
        (kFlat_pullbackComplex_pinned f M hM hfM)))
    (DerivedCategory.Q.map (complexAssociatorPair X ((pullbackComplex f).obj K)
      ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)))

/-- **The two associativity laws of the models and the naturality of the constraint of
[Stacks, Tag 0FPT] hold.** -/
theorem assocModelLaws
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    AssocLaws f K L M hK hL hM hfK hfL hfM :=
  ⟨canonicalComparison_associator_uncurried Y K L M hK hL hM,
    canonicalComparison_associator_uncurried X ((pullbackComplex f).obj K)
      ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
      (kFlat_pullbackComplex_pinned f K hK hfK)
      (kFlat_pullbackComplex_pinned f L hL hfL)
      (kFlat_pullbackComplex_pinned f M hM hfM),
    canonicalAssociatorHom_naturality X (pullbackComparisonQ f K) (pullbackComparisonQ f L)
      (pullbackComparisonQ f M)⟩

/-- The model identifications of [Stacks, Tag 07A4] at the pairs `(K, L)` and `(L, M)`, as a
proposition. -/
def AssocPairs
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    Prop :=
  AssocModelPairs (derivedPullback f) (uncurriedDerivedTensor Y) (uncurriedDerivedTensor X)
    (derivedPullbackTensorIso f).hom
    (pullbackComparisonQ f K) (pullbackComparisonQ f L) (pullbackComparisonQ f M)
    (comparisonPair Y K L hK hL) (comparisonPair Y L M hL hM)
    (comparisonPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
      (kFlat_pullbackComplex_pinned f K hK hfK)
      (kFlat_pullbackComplex_pinned f L hL hfL))
    (comparisonPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
      (kFlat_pullbackComplex_pinned f L hL hfL)
      (kFlat_pullbackComplex_pinned f M hM hfM))
    (pullbackTensorModel f K L) (pullbackTensorModel f L M)

/-- **The model identifications of [Stacks, Tag 07A4] at the pairs `(K, L)` and `(L, M)` hold.** -/
theorem assocModelPairs
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    AssocPairs f K L M hK hL hM hfK hfL hfM :=
  ⟨derivedPullbackTensorIso_hom_app_comp_comparisonPair f K L hK hL hfK hfL,
    derivedPullbackTensorIso_hom_app_comp_comparisonPair f L M hL hM hfL hfM⟩

/-- The model identification of [Stacks, Tag 07A4] at `(Tot(K ⊗ L), M)`, read against the model
`Tot(f^*K ⊗ f^*L)` of the first factor, as a proposition. -/
def AssocTripleLeft
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    Prop :=
  AssocModelTripleLeft (derivedPullback f) (uncurriedDerivedTensor Y) (uncurriedDerivedTensor X)
    (derivedPullbackTensorIso f).hom
    (pullbackComparisonQ f M)
    (comparisonPair Y
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)) M
      (kFlat_totalComplexPair Y K L hK hL) hM)
    (comparisonPair X
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
          ((pullbackComplex f).obj K, (pullbackComplex f).obj L))
      ((pullbackComplex f).obj M)
      (kFlat_totalComplexPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
        (kFlat_pullbackComplex_pinned f K hK hfK)
        (kFlat_pullbackComplex_pinned f L hL hfL))
      (kFlat_pullbackComplex_pinned f M hM hfM))
    (pullbackTensorModel f K L)
    (pullbackTensorModelTripleLeft f K L M)

/-- **The model identification of [Stacks, Tag 07A4] at `(Tot(K ⊗ L), M)`, read against the model
`Tot(f^*K ⊗ f^*L)` of the first factor, holds.** -/
theorem assocModelTripleLeft
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    AssocTripleLeft f K L M hK hL hM hfK hfL hfM :=
  ⟨derivedPullbackTensorIso_hom_app_comp_comparisonPair_left f K L M hK hL hM
    hfK hfL hfM⟩

/-- The model identification of [Stacks, Tag 07A4] at `(K, Tot(L ⊗ M))`, read against the model
`Tot(f^*L ⊗ f^*M)` of the second factor, as a proposition. -/
def AssocTripleRight
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    Prop :=
  AssocModelTripleRight (derivedPullback f) (uncurriedDerivedTensor Y) (uncurriedDerivedTensor X)
    (derivedPullbackTensorIso f).hom
    (pullbackComparisonQ f K)
    (comparisonPair Y K
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M)) hK
      (kFlat_totalComplexPair Y L M hL hM))
    (comparisonPair X ((pullbackComplex f).obj K)
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
          ((pullbackComplex f).obj L, (pullbackComplex f).obj M))
      (kFlat_pullbackComplex_pinned f K hK hfK)
      (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
        (kFlat_pullbackComplex_pinned f L hL hfL)
        (kFlat_pullbackComplex_pinned f M hM hfM)))
    (pullbackTensorModel f L M)
    (pullbackTensorModelTripleRight f K L M)

/-- **The model identification of [Stacks, Tag 07A4] at `(K, Tot(L ⊗ M))`, read against the model
`Tot(f^*L ⊗ f^*M)` of the second factor, holds.** -/
theorem assocModelTripleRight
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    AssocTripleRight f K L M hK hL hM hfK hfL hfM :=
  ⟨derivedPullbackTensorIso_hom_app_comp_comparisonPair_right f K L M hK hL hM
    hfK hfL hfM⟩

/-- The identity linking the two models of the triple tensor product, as a proposition: the two
model comparisons out of `Tot(Tot(K ⊗ L) ⊗ M)` and `Tot(K ⊗ Tot(L ⊗ M))` match the associator of
total tensor complexes upstairs with the one downstairs. -/
def AssocLink
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    Prop :=
  AssocModelLink (derivedPullback f)
    (DerivedCategory.Q.map (complexAssociatorPair Y K L M))
    (DerivedCategory.Q.map (complexAssociatorPair X ((pullbackComplex f).obj K)
      ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)))
    (pullbackTensorModelTripleLeft f K L M)
    (pullbackTensorModelTripleRight f K L M)

/-- **The identity linking the two models of the triple tensor product holds.** -/
theorem assocModelLink
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    AssocLink f K L M :=
  ⟨pullbackTensorModel_assoc_pair f K L M⟩

/-! ### The associativity law at a triple of K-flat complexes with flat terms -/

/-- **The comparison of [Stacks, Tag 07A4] carries the associativity constraint of
[Stacks, Tag 0FPT] on `D(𝒪')` to the one on `D(𝒪)`, at a triple of K-flat complexes with flat
terms.** -/
theorem derivedPullbackTensorIso_associator_app_of_kFlat
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hM : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    DerivedPullbackTensorIsoAssociator f (DerivedCategory.Q.obj K)
      (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M) :=
  have hK' := (Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O K).mpr hK
  have hL' := (Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O L).mpr hL
  have hM' := (Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O M).mpr hM
  bifunctor_comparison_assoc_of_bundles
    (mono_modelCorner f K L M hK' hL' hM' hfK hfL hfM)
    (assocModelLaws f K L M hK' hL' hM' hfK hfL hfM)
    (assocModelPairs f K L M hK' hL' hM' hfK hfL hfM)
    (assocModelTripleLeft f K L M hK' hL' hM' hfK hfL hfM)
    (assocModelTripleRight f K L M hK' hL' hM' hfK hfL hfM)
    (assocModelLink f K L M)

end Models

/-! ### The law for arbitrary derived modules -/

section Law

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : AlgebraicGeometry.RingedToposHom X Y)

/-- **`Lf^*` is a monoidal functor for the derived tensor product, for every morphism of ringed
topoi**: the comparison of [Stacks, Tag 07A4] carries the associativity constraint of
[Stacks, Tag 0FPT] on `D(𝒪')` to the one on `D(𝒪)`, for arbitrary `P`, `Q`, `S` in `D(𝒪')` and
with no boundedness, flatness, finiteness or quasi-coherence hypothesis.  The morphism `f` is a
morphism of the underlying topoi together with the structure map. -/
theorem derivedPullbackTensorIso_associator (P Q S : DerivedModules Y.O) :
    DerivedPullbackTensorIsoAssociator f P Q S :=
  derivedPullbackTensorIso_associator_of_kFlat f
    (fun K L M hK hL hM hfK hfL hfM ↦
      derivedPullbackTensorIso_associator_app_of_kFlat f K L M hK hL hM hfK hfL hfM)
    P Q S

end Law

end Stacks.Sheaves.DerivedPullback.OfToposHom

end
