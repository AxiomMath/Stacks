module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorAssociatorOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductAssociativity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductBraidingOfToposHom
import StacksCore.Tactic.StacksAttribute

/-!
# Associativity of the relative cup product, for a morphism of ringed topoi

Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a morphism of ringed topoi in the sense of
[Stacks, Tag 01D3], part (2): a morphism of the underlying *topoi* together with the structure
map, `AlgebraicGeometry.RingedToposHom`, with no functor between the underlying sites.
[Stacks, Tag 0FPL] says that the relative cup product of [Stacks, Tag 0B6C],

`Rf_*K ⊗^L_{𝒪'} Rf_*L ⟶ Rf_*(K ⊗^L_𝒪 L)`

(`Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct`), is associative: for `K`,
`L`, `M` in `D(𝒪)` the two ways of contracting `Rf_*K ⊗ Rf_*L ⊗ Rf_*M` to `Rf_*(K ⊗ L ⊗ M)` agree.

## Main results

* `Stacks.Cohomology.RelativeCupProductOfToposHom.pullbackTensorComparisonAssociative`: the
  comparison of [Stacks, Tag 07A4] carries the canonical associativity constraint
  `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.derivedAssociator` of `⊗^L_{𝒪'}` to that of
  `⊗^L_𝒪`, for every morphism of ringed topoi and all objects of `D(𝒪')`.
* `Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct_assoc`:
  **[Stacks, Tag 0FPL]**, with no hypothesis and no class argument;
  `relativeCupProduct_assoc_of_instances` is the same statement at the variable block of the cup
  product.

## Implementation notes

The site-presented statement
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.relativeCupProduct_assoc_canonical` is for a
morphism presented by a continuous functor between the underlying sites satisfying
`Functor.IsMorphismOfSites`; a morphism of topoi need not have such a presentation on the given
sites, so this is the statement in the generality of the source.  The proof is the abstract one:
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct_assoc` applied to the
derived adjunction of [Stacks, Tag 07A6], the comparison of [Stacks, Tag 07A4], the naturality
of the canonical constraint, and the associativity law of the comparison, which is
`Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_associator`.  The
site-presented `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.relativeCupProduct_assoc`, over
arbitrary constraints with their naturality and that associativity law as hypotheses, is what
`relativeCupProduct_assoc_canonical` specialises.  Neither carries a `stacks` attribute: the
site-presented statements are special cases of the one here, which alone is registered as
[Stacks, Tag 0FPL].

## References

* [Stacks Project, Tag 0FPL](https://stacks.math.columbia.edu/tag/0FPL)
* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.RelativeCupProductOnRingedTopoi
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.RelativeCupProductOfToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

section Instances

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
  (f : RingedToposHom X Y)

/-- **`Lf^*` is a monoidal functor for the derived tensor product, for a morphism of ringed
topoi**: the comparison `Lf^*(A ⊗^L_{𝒪'} B) ≅ Lf^*A ⊗^L_𝒪 Lf^*B` of [Stacks, Tag 07A4] carries
the canonical associativity constraint `derivedAssociator` of `⊗^L_{𝒪'}` to that of `⊗^L_𝒪`, for
all `P`, `Q`, `S` in `D(𝒪')`.  This is
`Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_associator`, read through
`derivedAssociator_hom_eq_canonicalAssociatorHom`. -/
theorem pullbackTensorComparisonAssociative
    (P Q S : DerivedModules Y.O) :
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom.app
          ((uncurriedDerivedTensor Y).obj (P, Q), S) ≫
        (uncurriedDerivedTensor X).map
          ((Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom.app (P, Q) ×ₘ
            𝟙 ((derivedPullback f).obj S)) ≫
          (derivedAssociator X ((derivedPullback f).obj P) ((derivedPullback f).obj Q)
            ((derivedPullback f).obj S)).hom =
      (derivedPullback f).map (derivedAssociator Y P Q S).hom ≫
        (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom.app
            (P, (uncurriedDerivedTensor Y).obj (Q, S)) ≫
          (uncurriedDerivedTensor X).map
            (𝟙 ((derivedPullback f).obj P) ×ₘ
              (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom.app
                (Q, S)) :=
  Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_associator f P Q S

/-- **[Stacks, Tag 0FPL], at the variable block of the cup product.**  This is
`relativeCupProduct_assoc` with the `Prop`-valued class arguments that `relativeCupProduct` is
defined under kept as binders; `relativeCupProduct_assoc` drops them, because instance search
supplies every one of them. -/
theorem relativeCupProduct_assoc_of_instances (K L M : DerivedModules X.O) :
    (uncurriedDerivedTensor Y).map
          (relativeCupProduct f K L ×ₘ 𝟙 ((derivedPushforward f).obj M)) ≫
        relativeCupProduct f ((uncurriedDerivedTensor X).obj (K, L)) M ≫
          (derivedPushforward f).map (derivedAssociator X K L M).hom =
      (derivedAssociator Y ((derivedPushforward f).obj K) ((derivedPushforward f).obj L)
            ((derivedPushforward f).obj M)).hom ≫
        (uncurriedDerivedTensor Y).map
            (𝟙 ((derivedPushforward f).obj K) ×ₘ relativeCupProduct f L M) ≫
          relativeCupProduct f K ((uncurriedDerivedTensor X).obj (L, M)) := by
  simp only [relativeCupProduct_eq_adjunctionCupProduct]
  rw [← Category.assoc,
    adjunctionCupProduct_assoc (derivedAdjunction f) (uncurriedDerivedTensor Y)
      (uncurriedDerivedTensor X)
      (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom
      (fun P Q S => (derivedAssociator Y P Q S).hom) (derivedAssociator X)
      (fun u v w => derivedAssociator_naturality X u v w)
      (pullbackTensorComparisonAssociative f) K L M]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
  rw [(derivedPushforward f).map_id, Category.comp_id]

end Instances

attribute [local instance high] hasMapBifunctor_sheafTensor_ringedTopos

/-- **[Stacks, Tag 0FPL].**  The relative cup product of [Stacks, Tag 0B6C] is associative.  Let
`f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a morphism of ringed topoi: a morphism of the underlying
topoi together with the structure map.  Then for **all** `K`, `L`, `M` in `D(𝒪)` the square

```
(Rf_*K ⊗' Rf_*L) ⊗' Rf_*M --→ Rf_*(K ⊗ L) ⊗' Rf_*M --→ Rf_*((K ⊗ L) ⊗ M)
          |                                                     |
          | a                                                   | Rf_*a
          ↓                                                     ↓
Rf_*K ⊗' (Rf_*L ⊗' Rf_*M) --→ Rf_*K ⊗' Rf_*(L ⊗ M) --→ Rf_*(K ⊗ (L ⊗ M))
```

commutes in `D(𝒪')`.  The four unlabelled arrows are relative cup products in one or the other
tensor factor; the two edges `a` are the associativity constraints `derivedAssociator` of
`⊗^L_{𝒪'}` and `⊗^L_𝒪`, the associators of the monoidal structures of [Stacks, Tag 0FPT] whose
tensor product is the derived tensor product of [Stacks, Tag 06YU] on the nose; they appear
because the source draws its square with `⊗^L` strictly associative.

The statement has no hypothesis and no class argument of its own.  The associativity law of the
comparison of [Stacks, Tag 07A4] that the source's proof uses silently is
`pullbackTensorComparisonAssociative`, proved above. -/
@[stacks 0FPL "the whole tag, for an arbitrary morphism of ringed topoi in the two-field sense \
  of Tag 01D3, part (2) (a morphism of the underlying topoi with its structure map, no functor \
  between the underlying sites and no morphism-of-sites hypothesis), at RingedTopos.{u, u, u}, \
  for all K, L, M in D(𝒪); the edges a are the associativity constraints derivedAssociator of \
  Tag 0FPT and the statement has no hypothesis or class argument; the associativity law of \
  the comparison of Tag 07A4, which the source's proof uses silently, is \
  pullbackTensorComparisonAssociative"]
theorem relativeCupProduct_assoc {X Y : RingedTopos.{u, u, u}} (f : RingedToposHom X Y)
    (K L M : DerivedModules X.O) :
    (uncurriedDerivedTensor Y).map
          (relativeCupProduct f K L ×ₘ 𝟙 ((derivedPushforward f).obj M)) ≫
        relativeCupProduct f ((uncurriedDerivedTensor X).obj (K, L)) M ≫
          (derivedPushforward f).map (derivedAssociator X K L M).hom =
      (derivedAssociator Y ((derivedPushforward f).obj K) ((derivedPushforward f).obj L)
            ((derivedPushforward f).obj M)).hom ≫
        (uncurriedDerivedTensor Y).map
            (𝟙 ((derivedPushforward f).obj K) ×ₘ relativeCupProduct f L M) ≫
          relativeCupProduct f K ((uncurriedDerivedTensor X).obj (L, M)) :=
  @relativeCupProduct_assoc_of_instances X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f K L M

end Stacks.Cohomology.RelativeCupProductOfToposHom

end
