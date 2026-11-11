module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorAssociatorOnKFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseatConstraints

/-!
# Associativity of the relative cup product on a ringed topos, over the canonical constraints

Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a morphism of ringed topoi. The relative cup product is
associative: for all `K`, `L`, `M` in `D(𝒪)` the square

```
(Rf_*K ⊗' Rf_*L) ⊗' Rf_*M --→ Rf_*(K ⊗ L) ⊗' Rf_*M --→ Rf_*((K ⊗ L) ⊗ M)
          |                                                     |
          | a                                                   | Rf_*a
          ↓                                                     ↓
Rf_*K ⊗' (Rf_*L ⊗' Rf_*M) --→ Rf_*K ⊗' Rf_*(L ⊗ M) --→ Rf_*(K ⊗ (L ⊗ M))
```

commutes in `D(𝒪')`, where the two constraints `a` are the associators of the monoidal
structure `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`, whose tensor product
is the derived tensor bifunctor.

## Main definitions

* `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.derivedAssociator`: the associativity
  constraint of `⊗^L_𝒪` on a ringed topos, read on the uncurried derived tensor bifunctor.
* `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.PullbackTensorComparisonAssociative`: the
  comparison `Lf^*(A ⊗^L_{𝒪'} B) ≅ Lf^*A ⊗^L_𝒪 Lf^*B` is compatible with the associativity
  constraints.

## Main results

* `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.derivedAssociator_naturality`: the
  constraint is natural in the three objects jointly.
* `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.pullbackTensorComparisonAssociative`:
  `Lf^*` is a monoidal functor for `⊗^L`, for arbitrary objects of `D(𝒪')`.
* `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.relativeCupProduct_assoc_canonical`: the
  relative cup product is associative over the canonical constraints, for a morphism presented
  on the underlying sites; [Stacks, Tag 0FPL] for an arbitrary morphism of ringed topoi is
  `Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct_assoc`.

## References

* [Stacks Project, Tag 0FPL](https://stacks.math.columbia.edu/tag/0FPL)
* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FP4](https://stacks.math.columbia.edu/tag/0FP4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.DerivedTensor.RingedSite
open Stacks.SheafOfModules.DerivedMonoidal (canonicalDerivedMonoidal)
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.RelativeCupProductOnRingedTopoi

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### The canonical associativity constraint of the derived tensor product -/

section Constraint

variable (W : RingedTopos.{u, u, u})
  [HasSheafify W.J AddCommGrpCat.{u}] [W.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O).obj M).Additive]
  [∀ (P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.O)) ℤ),
    HomologicalComplex.HasMapBifunctor P Q
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O) (ComplexShape.up ℤ)]

/-- The associativity constraint of the derived tensor product on a ringed topos: the associator
of `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`, read on the uncurried
derived tensor bifunctor. -/
def derivedAssociator (P Q S : DerivedModules W.O) :
    (uncurriedDerivedTensor W).obj ((uncurriedDerivedTensor W).obj (P, Q), S) ≅
      (uncurriedDerivedTensor W).obj (P, (uncurriedDerivedTensor W).obj (Q, S)) :=
  letI := canonicalDerivedMonoidal W.O
  α_ P Q S

/-- The associativity constraint is the associator of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`. -/
theorem derivedAssociator_eq (P Q S : DerivedModules W.O) :
    letI := canonicalDerivedMonoidal W.O
    derivedAssociator W P Q S = α_ P Q S :=
  rfl

/-- The associativity constraint is
`Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociatorHom`. -/
theorem derivedAssociator_hom_eq_canonicalAssociatorHom (P Q S : DerivedModules W.O) :
    (derivedAssociator W P Q S).hom =
      Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociatorHom W.O P Q S :=
  rfl

/-- The associativity constraint is natural in its three variables jointly. -/
theorem derivedAssociator_naturality {P P' Q Q' S S' : DerivedModules W.O}
    (u : P ⟶ P') (v : Q ⟶ Q') (w : S ⟶ S') :
    (derivedAssociator W P Q S).hom ≫
        (uncurriedDerivedTensor W).map (u ×ₘ (uncurriedDerivedTensor W).map (v ×ₘ w)) =
      (uncurriedDerivedTensor W).map ((uncurriedDerivedTensor W).map (u ×ₘ v) ×ₘ w) ≫
        (derivedAssociator W P' Q' S').hom :=
  let := canonicalDerivedMonoidal W.O
  (MonoidalCategory.associator_naturality u v w).symm

end Constraint

/-! ### The associativity law of the comparison of derived pullback with derived tensor -/

section Comparison

variable {X Y : RingedTopos.{u, u, u}}
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

/-- The comparison `Lf^*(A ⊗^L_{𝒪'} B) ≅ Lf^*A ⊗^L_𝒪 Lf^*B` is compatible with the
associativity constraints `derivedAssociator` on either side: the two composites
`Lf^*((P ⊗' Q) ⊗' S) ⟶ Lf^*P ⊗ (Lf^*Q ⊗ Lf^*S)`, splitting the tensor products and then
re-bracketing downstairs, or re-bracketing upstairs and then splitting, agree. -/
def PullbackTensorComparisonAssociative : Prop :=
  ∀ P Q S : DerivedModules Y.O,
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom.app
          ((uncurriedDerivedTensor Y).obj (P, Q), S) ≫
        (uncurriedDerivedTensor X).map
          ((Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom.app (P, Q) ×ₘ
            𝟙 ((derivedPullback f).obj S)) ≫
          (derivedAssociator X ((derivedPullback f).obj P) ((derivedPullback f).obj Q)
            ((derivedPullback f).obj S)).hom =
      (derivedPullback f).map (derivedAssociator Y P Q S).hom ≫
        (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom.app
            (P, (uncurriedDerivedTensor Y).obj (Q, S)) ≫
          (uncurriedDerivedTensor X).map
            (𝟙 ((derivedPullback f).obj P) ×ₘ
              (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom.app (Q, S))

end Comparison

/-! ### Associativity of the relative cup product over the canonical constraints -/

section Assoc

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

/-- `Lf^*` is a monoidal functor for the derived tensor product: the comparison
`Lf^*(A ⊗^L_{𝒪'} B) ≅ Lf^*A ⊗^L_𝒪 Lf^*B` carries the associativity constraint
`derivedAssociator` of `⊗^L_{𝒪'}` to the one of `⊗^L_𝒪`, for arbitrary `P`, `Q`, `S` in
`D(𝒪')`. -/
theorem pullbackTensorComparisonAssociative :
    PullbackTensorComparisonAssociative f hmos :=
  Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_associator_of_kFlat f hmos
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_associator_app_of_kFlat f hmos)

/-- The relative cup product is associative: for all `K`, `L`, `M` in `D(𝒪)` the square

```
(Rf_*K ⊗' Rf_*L) ⊗' Rf_*M --→ Rf_*(K ⊗ L) ⊗' Rf_*M --→ Rf_*((K ⊗ L) ⊗ M)
          |                                                     |
          | a                                                   | Rf_*a
          ↓                                                     ↓
Rf_*K ⊗' (Rf_*L ⊗' Rf_*M) --→ Rf_*K ⊗' Rf_*(L ⊗ M) --→ Rf_*(K ⊗ (L ⊗ M))
```

commutes in `D(𝒪')`. The four unlabelled arrows are relative cup products in one or the other
tensor factor; the two edges `a` are the canonical associativity constraints `derivedAssociator`
of `⊗^L_{𝒪'}` and `⊗^L_𝒪`.

This is the statement for a morphism presented by a continuous functor between the underlying
sites with `Functor.IsMorphismOfSites`; [Stacks, Tag 0FPL] for an arbitrary morphism of ringed
topoi is `Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct_assoc`. -/
theorem relativeCupProduct_assoc_canonical (K L M : DerivedModules X.O) :
    (uncurriedDerivedTensor Y).map
          (relativeCupProduct f hmos K L ×ₘ 𝟙 ((derivedPushforward f).obj M)) ≫
        relativeCupProduct f hmos ((uncurriedDerivedTensor X).obj (K, L)) M ≫
          (derivedPushforward f).map (derivedAssociator X K L M).hom =
      (derivedAssociator Y ((derivedPushforward f).obj K) ((derivedPushforward f).obj L)
            ((derivedPushforward f).obj M)).hom ≫
        (uncurriedDerivedTensor Y).map
            (𝟙 ((derivedPushforward f).obj K) ×ₘ relativeCupProduct f hmos L M) ≫
          relativeCupProduct f hmos K ((uncurriedDerivedTensor X).obj (L, M)) := by
  rw [← Category.assoc,
    relativeCupProduct_assoc f hmos (fun P Q S => (derivedAssociator Y P Q S).hom)
      (derivedAssociator X) (fun u v w => derivedAssociator_naturality X u v w)
      (pullbackTensorComparisonAssociative f hmos) K L M]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
  rw [(derivedPushforward f).map_id, Category.comp_id]

end Assoc

end Stacks.Cohomology.RelativeCupProductOnRingedTopoi

end
