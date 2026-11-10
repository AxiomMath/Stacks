module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorIsoCompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorAssociatorOnKFlat

/-!
# The comparison of Tag 07A4 on K-flat models, for a morphism of ringed topoi

Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a morphism of ringed topoi in the two-field sense of
[Stacks, Tag 01D3], part (2) — a morphism of the underlying *topoi* together with the structure
map, with no functor between the underlying sites — and let `K`, `M` be K-flat complexes of
`𝒪'`-modules with flat terms.  This file records the facts about the comparison

`Lf^*(K ⊗^L_{𝒪'} M) ≅ Lf^*K ⊗^L_𝒪 Lf^*M`

of [Stacks, Tag 07A4]
(`Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso`) that the associativity law
of that comparison is assembled from, beyond those already proved for its braiding and its
composition law in `DerivedPullbackTensorBraidingOfToposHom.lean` and
`DerivedPullbackTensorIsoCompositionOfToposHom.lean` (the comparison `pullbackComparisonQ` of
[Stacks, Tag 06YY] at an arbitrary complex and its naturality, and the square
`toTensor_square_of_kFlat` of [Stacks, Tag 0FPH] on a pair of models, all reused here):

* the comparison of [Stacks, Tag 06YY] is invertible on a K-flat complex with flat terms, and
  [Stacks, Tag 0G7E] holds, at the pinned spelling `Stacks.SheafOfModules.KFlat` of
  K-flatness at which the constraints of [Stacks, Tag 0FPT] are stated;
* the comparison `f^*Tot(K ⊗_{𝒪'} L) ≅ Tot(f^*K ⊗_𝒪 f^*L)` of [Stacks, Tag 03EL] on total complexes
  is compatible with the associator of total tensor complexes, in the forward direction
  (`pullbackTensorTotalIso_associator_pair`).

They are the morphism-of-topoi counterparts of
`Stacks.Sheaves.DerivedPullback.isIso_pullbackComparisonQ`,
`Stacks.Sheaves.DerivedPullback.kFlat_pullbackComplex_pinned` and
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso_associator_pair`, which are stated for
a morphism presented by a morphism of the underlying sites.

## Main results

* `Stacks.Sheaves.DerivedPullback.OfToposHom.isIso_pullbackComparisonQ` and
  `kFlat_pullbackComplex_pinned`.
* `Stacks.Sheaves.DerivedPullback.OfToposHom.oplax_associativity_totalObj`: the associativity
  clause of an oplax monoidal functor between complexes of modules, read at the
  `HomologicalComplex.mapBifunctor` spelling of the total tensor complex.
* `Stacks.Sheaves.DerivedPullback.OfToposHom.pullbackTensorTotalIso_associator_pair`: the
  associativity coherence of the comparison of [Stacks, Tag 03EL] on total complexes.

## Implementation notes

Every statement is the site-presented one with the morphism-of-sites hypothesis removed: the
inputs it consumed there — the computation of `Lf^*` on K-flat complexes with flat terms
(Stacks 06YY), Stacks 0G7E and the comparison of total tensor complexes — are available for a
morphism of topoi unconditionally (`isIso_pullbackComparisonQ_of_kFlat`,
`Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.kFlat_pullbackComplex`,
`Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso`), and the last is stated for the pullback
of Stacks 03D6 part (2) itself, so no transport between two pullbacks intervenes.

*The associativity coherence.*  It is the associativity clause of
`CategoryTheory.Functor.OplaxMonoidal` for the monoidal lift of `f^*` to complexes, whose oplax
tensorator is the comparison of total tensor complexes
(`Stacks.Sheaves.DerivedPullback.delta_pullbackComplexFunctor`).  The clause is stated with `⊗`,
the statement here with `HomologicalComplex.mapBifunctor`, and identifying the two at the
concrete functor `f^*` makes the unifier unfold the pullback of sheaves of modules, which exceeds
the heartbeat budget.  So the identification is made once for an *abstract* oplax monoidal
functor (`oplax_associativity_totalObj`), where there is nothing to unfold, and the concrete
statement is that lemma applied to `f^*`.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex)

namespace Stacks.Sheaves.DerivedPullback.OfToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : AlgebraicGeometry.RingedToposHom X Y)

/-! ### The comparison of Tag 06YY at an arbitrary complex -/

section Comparison

/-- **[Stacks, Tag 0G7E] at the pinned spelling of K-flatness**: the degreewise pullback of a
K-flat complex of `𝒪'`-modules with flat terms along a morphism of ringed topoi is K-flat. -/
theorem kFlat_pullbackComplex_pinned
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    Stacks.SheafOfModules.KFlat X.O
      ((Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.pullbackComplex f).obj K) :=
  Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.kFlat_pullbackComplex f K hK hflat

/-- **The comparison of [Stacks, Tag 06YY] at a K-flat complex with flat terms is
invertible.** -/
theorem isIso_pullbackComparisonQ
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    IsIso (Stacks.Sheaves.DerivedPullback.OfToposHom.pullbackComparisonQ f K) :=
  isIso_pullbackComparisonQ_of_kFlat f K
    ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O K).mp hK) hflat

end Comparison

/-! ### The associativity coherence of Tag 03EL on total complexes -/

section OplaxAssociator

open MonoidalCategory

attribute [local instance] monoidalModules symmetricModules monoidalPreadditiveModules
  monoidalClosedModules hasTensorModules monoidalComplexes

variable {X Y : RingedTopos.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ ⥤
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  [P.OplaxMonoidal]

/-- **The associativity clause of an oplax monoidal functor between complexes of modules, at the
`HomologicalComplex.mapBifunctor` spelling of the total tensor complex.**  Let `P` be an oplax
monoidal functor for the total tensor products, and let `d` be its oplax tensorator rewritten with
source and target at that spelling (`hd`).  Then the square

```
P Tot(Tot(K ⊗ L) ⊗ M) ⟶ Tot(P Tot(K ⊗ L) ⊗ PM) ⟶ Tot(Tot(PK ⊗ PL) ⊗ PM)
         |                                                    |
         | Pα                                                 | α
         v                                                    v
P Tot(K ⊗ Tot(L ⊗ M)) ⟶ Tot(PK ⊗ P Tot(L ⊗ M)) ⟶ Tot(PK ⊗ Tot(PL ⊗ PM))
```

commutes.  The functor is kept abstract, so identifying the two spellings of the total tensor
complex never unfolds it. -/
theorem oplax_associativity_totalObj
    (d : ∀ A B : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ,
      P.obj (totalObj Y A B) ⟶ totalObj X (P.obj A) (P.obj B))
    (hd : ∀ A B, d A B = Functor.OplaxMonoidal.δ P A B)
    (K L M : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    d (totalObj Y K L) M ≫ totalComplexMapRightTopos X (d K L) (P.obj M) ≫
        complexAssociatorPairTopos X (P.obj K) (P.obj L) (P.obj M) =
      P.map (complexAssociatorPairTopos Y K L M) ≫ d K (totalObj Y L M) ≫
        totalComplexMapLeftTopos X (P.obj K) (d L M) := by
  simp only [hd, totalComplexMapRightTopos, totalComplexMapLeftTopos, complexAssociatorPairTopos]
  exact Functor.OplaxMonoidal.oplax_associativity P K L M

end OplaxAssociator

section Associator

attribute [local instance] monoidalModules symmetricModules monoidalPreadditiveModules
  monoidalClosedModules hasTensorModules monoidalComplexes pullbackModulesMonoidalSheafTensor
  pullbackModules_preservesAntidiagonalCoproducts

variable
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

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- **The associativity coherence of the comparison of total tensor complexes for a morphism of
ringed topoi**, in the forward direction and with every term written at the
`HomologicalComplex.mapBifunctor` spelling of the total tensor complex: for cochain complexes
`K, L, M` of `𝒪'`-modules the square

```
f^*Tot(Tot(K ⊗ L) ⊗ M) ⟶ Tot(f^*Tot(K ⊗ L) ⊗ f^*M) ⟶ Tot(Tot(f^*K ⊗ f^*L) ⊗ f^*M)
         |                                                         |
         | f^*α                                                    | α
         v                                                         v
f^*Tot(K ⊗ Tot(L ⊗ M)) ⟶ Tot(f^*K ⊗ f^*Tot(L ⊗ M)) ⟶ Tot(f^*K ⊗ Tot(f^*L ⊗ f^*M))
```

commutes.  The comparison of [Stacks, Tag 03EL] on total complexes is the oplax tensorator of the
monoidal lift of `f^*` to complexes
(`Stacks.Sheaves.DerivedPullback.delta_pullbackComplexFunctor`), so this is
`oplax_associativity_totalObj` at that lift. -/
theorem pullbackTensorTotalIso_associator_pair
    (K L M : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackTensorTotalIso f.toModulesHom (totalObj Y K L) M).hom ≫
        totalComplexMapRightTopos X ((pullbackTensorTotalIso f.toModulesHom K L).hom)
            ((pullbackComplex f).obj M) ≫
          complexAssociatorPairTopos X ((pullbackComplex f).obj K)
            ((pullbackComplex f).obj L) ((pullbackComplex f).obj M) =
      (pullbackComplex f).map (complexAssociatorPairTopos Y K L M) ≫
        (pullbackTensorTotalIso f.toModulesHom K (totalObj Y L M)).hom ≫
          totalComplexMapLeftTopos X ((pullbackComplex f).obj K)
            ((pullbackTensorTotalIso f.toModulesHom L M).hom) :=
  oplax_associativity_totalObj (pullbackComplexFunctor f.toModulesHom)
    (fun A B => (pullbackTensorTotalIso f.toModulesHom A B).hom)
    (fun A B => (delta_pullbackComplexFunctor f.toModulesHom A B).symm) K L M

end Associator

end Stacks.Sheaves.DerivedPullback.OfToposHom

end
