module

public import StacksFrontier.CategoryTheory.BifunctorComparisonAssocModels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorTotalSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorAssociatorDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorComplexAssociatorOnRingedTopoi

/-!
# The associativity law of the comparison of Tag 07A4 at a triple of K-flat complexes

Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a morphism of ringed topoi.  The comparison of
[Stacks, Tag 07A4],

`Lf^*(P ⊗^L_{𝒪'} Q) ≅ Lf^*P ⊗^L_𝒪 Lf^*Q`,

carries the associativity constraint of the monoidal derived category of [Stacks, Tag 0FPT] on
`D(𝒪')` to the one on `D(𝒪)`.  This file proves that law at a triple of K-flat complexes with
flat terms, which by [Stacks, Tag 06YS] is where the law has to be proved: the descent to
arbitrary objects of `D(𝒪')` is
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_associator_of_kFlat`.

On such a triple every object of the associativity square is computed by an ordinary total
tensor complex.  The comparison of [Stacks, Tag 06YU] identifies the derived tensor product with
that total complex, the constraint of [Stacks, Tag 0FPT] is then the associator of
`Comp(Mod(𝒪))`, the comparison of [Stacks, Tag 07A4] against those models is the square of
[Stacks, Tag 0FPH], and the comparison of [Stacks, Tag 06YY] identifies `Lf^*` of a K-flat
complex with flat terms with the image of its degreewise pullback.  The diagram chase that joins
these is carried out for an arbitrary functor and arbitrary bifunctors in
`StacksFrontier.CategoryTheory.BifunctorComparisonConstraints`, and consumed here through the five
bundles of `StacksFrontier.CategoryTheory.BifunctorComparisonAssocModels`; what this file supplies
is the instantiation.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.pullbackTensorComplexPair`: the comparison
  `f^*Tot(K ⊗_{𝒪'} L) ⟶ Tot(f^*K ⊗_𝒪 f^*L)` of [Stacks, Tag 03EL], at the total-complex
  spelling the constraints of [Stacks, Tag 0FPT] are pinned at.
* `Stacks.Sheaves.DerivedPullback.pullbackTensorModel`: **the model of
  `Lf^*(QK ⊗^L_{𝒪'} QL)`** -- the comparison of [Stacks, Tag 06YY] at the total tensor complex
  followed by that comparison of [Stacks, Tag 03EL].
* `Stacks.Sheaves.DerivedPullback.pullbackTensorModelTripleLeft` and
  `pullbackTensorModelTripleRight`: the two models of the triple tensor product, one for each
  bracketing.
* `Stacks.Sheaves.DerivedPullback.ModelIdentificationLeft` and `ModelIdentificationRight`: the
  model identifications of [Stacks, Tag 07A4] at the two triples, as propositions.
* `Stacks.Sheaves.DerivedPullback.AssocLaws`, `AssocPairs`, `AssocTripleLeft`,
  `AssocTripleRight`, `AssocLink`: the five bundles of the chase, each naming the objects and
  maps it relates.

## Main results

* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_hom_app_comp_comparisonPair`: the
  model identification of [Stacks, Tag 07A4] at a pair of K-flat complexes with flat terms,
  which is the square of [Stacks, Tag 0FPH] read against the comparison of [Stacks, Tag 06YU].
* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_hom_app_comp_comparisonPair_left` and
  `..._right`: that identification at the two triples, re-read against the model
  `Tot(f^*K ⊗ f^*L)` of the composite factor.
* `Stacks.Sheaves.DerivedPullback.isIso_modelCorner`, `mono_modelCorner`: the composite the
  chase cancels is invertible.
* `Stacks.Sheaves.DerivedPullback.pullbackTensorModel_assoc_pair` and `assocModelLink`: the
  identity matching the two models of the triple tensor product, which is the associativity
  coherence of [Stacks, Tag 03EL] on total complexes pushed into the derived category.
* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_associator_app_of_kFlat`: **the
  associativity law at a triple of K-flat complexes with flat terms.**

## Implementation notes

*Pinning.*  The total tensor complex of two complexes of `𝒪`-modules has three spellings in
play: `⊗` of the monoidal structure on `Comp(Mod(𝒪))`, which the associator is written at;
`Stacks.SheafOfModules.Tensor.tensorComplex`, which the comparison of [Stacks, Tag 06YU] and the
square of [Stacks, Tag 0FPH] land in; and
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair`, at which the constraints of
[Stacks, Tag 0FPT] are pinned in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AssociatorPinnedOnRingedTopoi`.  They
denote the same complex, but the identifications are conversions the `HomologicalComplex`
instance arguments make expensive, so every statement here is written at the last of the three
and the identification with the others is paid for exactly once, in
`Stacks.Sheaves.DerivedPullback.pullbackTensorComplexPair`,
`Stacks.Sheaves.DerivedPullback.pullbackTensorModel` and
`Stacks.Sheaves.DerivedPullback.isFlat_totalComplexPair_X`, each with a one-line lemma recording
what it is.  K-flatness has two spellings for the same reason -- the predicate
`CochainComplex.KFlatBifunctor.KFlat` that [Stacks, Tag 0G7E] and [Stacks, Tag 06YY] are stated
at, and `Stacks.SheafOfModules.KFlat`, which the comparison of [Stacks, Tag 06YU] is
stated at -- and `Stacks.Sheaves.DerivedPullback.kFlat_pullbackComplex_pinned` pays for that
identification once.

*The two models of the triple tensor product.*  The model identification of [Stacks, Tag 07A4]
at a pair of complexes lands in `Q(f^*Tot(K ⊗ L))`, while the associativity square needs it
against `Q(Tot(f^*K ⊗ f^*L))`.  `CategoryTheory.bifunctor_comparison_model_comp_left` and
`_right` re-read it against the further model, along the naturality of the comparison of
[Stacks, Tag 06YU] in one variable; what is left over is the identity
`Stacks.Sheaves.DerivedPullback.AssocLink`, which is the associativity coherence of the
comparison of [Stacks, Tag 03EL] on total complexes pushed into the derived category along the
comparison of [Stacks, Tag 06YY].  The two models of the triple tensor product are named in
`Stacks.Sheaves.DerivedPullback.pullbackTensorModelTripleLeft` and
`pullbackTensorModelTripleRight`: each is a composite of two arrows, and naming them is what
keeps the declaration that matches them against that identity inside the heartbeat budget.

*The `Prop`-valued `def`s.*  The long equations -- the two re-read model identifications and the
five bundles of the chase -- have their statements in `Prop`-valued `def`s, separate from their
proofs.  That is not a mathematical choice: the heartbeat budget is per declaration, and naming
the eleven objects and sixteen maps of the chase and proving the fields in a single declaration
exceeds it.  Nothing is assumed and nothing is weakened; the application is paid for in
instalments.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0G6Q](https://stacks.math.columbia.edu/tag/0G6Q)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback.KFlatPullback
open Stacks.DerivedTensor.RingedSite
open Stacks.SheafOfModules.DerivedMonoidal (canonicalAssociatorHom)
open Stacks.Cohomology.RelativeCupProductOnRingedTopoi
open scoped CategoryTheory.Prod

namespace Stacks.Sheaves.DerivedPullback

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### The comparison of Tag 06YU as the canonical map to the total tensor complex -/

section OneTopos

variable (W : RingedTopos.{u, u, u})
  [HasSheafify W.J AddCommGrpCat.{u}] [W.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O).obj M).Additive]
  [∀ (P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.O)) ℤ),
    HomologicalComplex.HasMapBifunctor P Q
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O) (ComplexShape.up ℤ)]

/-- **On a pair of K-flat complexes the canonical map of [Stacks, Tag 06YU] from the derived
tensor product to the ordinary total tensor complex is the comparison**, at the pinned spelling
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.comparisonPair`. -/
theorem comparisonPair_eq_toTensor
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat W.O K)
    (hL : Stacks.SheafOfModules.KFlat W.O L) :
    comparisonPair W K L hK hL = (canonicalDerivedTensorProduct W.O).toTensor K L :=
  ((canonicalDerivedTensorProduct W.O).toTensor_eq_comparison K L hK hL).symm

/-- The uncurried derived tensor bifunctor of [Stacks, Tag 06YU] on a pair of morphisms is the
value of the curried one on that pair, in the form
`Stacks.Sheaves.DerivedPullback.bifunctorMap`. -/
theorem uncurriedDerivedTensor_map_eq_bifunctorMap {A A' B B' : DerivedModules W.O} (a : A ⟶ A')
    (b : B ⟶ B') :
    (uncurriedDerivedTensor W).map ((a ×ₘ b) : ((A, B) : _ × _) ⟶ (A', B')) =
      bifunctorMap (canonicalDerivedTensorProduct W.O).tensor a b :=
  rfl

end OneTopos

/-! ### Flat terms of a total tensor complex -/

section OneToposFlat

variable (W : RingedTopos.{u, u, u})
  [HasSheafify W.J AddCommGrpCat.{u}] [W.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O) (ComplexShape.up ℤ)]

/-- **The total tensor complex of two complexes with flat terms has flat terms**, at the pinned
spelling `Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair`: each bidegree
`K^p ⊗_𝒪 L^q` is flat by [Stacks, Tag 0G6Q] and the term in total degree `n` is their direct
sum. -/
theorem isFlat_totalComplexPair_X
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.O)) ℤ)
    (hK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := W.O) (K.X i))
    (hL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := W.O) (L.X i))
    (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := W.O)
      (((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O)).obj (K, L)).X n) :=
  isFlat_tensorComplex_X W.O K L hK hL n

end OneToposFlat

/-! ### The two pinnings of the total tensor complex, identified -/

section Bridges

attribute [local instance] monoidalModules symmetricModules
  monoidalPreadditiveModules monoidalClosedModules hasTensorModules monoidalComplexes

variable (Z : RingedTopos.{u, u, u})
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ)]

omit [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The total tensor complex of a cochain map and an identity in the second variable, read at the
two pinnings of the total tensor complex: the one through
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair`, at which the constraints of
[Stacks, Tag 0FPT] are stated, and the one through
`Stacks.Sheaves.DerivedPullback.totalObj`, at which the comparison of [Stacks, Tag 03EL] on
total complexes is.  The identification is made degreewise: both are the degreewise bifunctor map
of the pair `(a, 𝟙 B)`. -/
theorem totalComplexMapRight_eq_topos
    {A A' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ}
    (a : A ⟶ A')
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    totalComplexMapRight Z a B = totalComplexMapRightTopos Z a B :=
  HomologicalComplex.hom_ext _ _ fun n =>
    (congrArg (fun φ => HomologicalComplex.Hom.f φ n)
        (totalComplexMapRight_eq_mapBifunctorMap Z a B)).trans
      (HomologicalComplex.Monoidal.whiskerRight_f a B n).symm

omit [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The total tensor complex of an identity and a cochain map in the second variable, read at the
two pinnings; the companion of
`Stacks.Sheaves.DerivedPullback.totalComplexMapRight_eq_topos`. -/
theorem totalComplexMapLeft_eq_topos
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    {B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ}
    (b : B ⟶ B') :
    totalComplexMapLeft Z A b = totalComplexMapLeftTopos Z A b :=
  HomologicalComplex.hom_ext _ _ fun n =>
    (congrArg (fun φ => HomologicalComplex.Hom.f φ n)
        (totalComplexMapLeft_eq_mapBifunctorMap Z A b)).trans
      (HomologicalComplex.Monoidal.whiskerLeft_f A b n).symm

omit [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The associator of total tensor complexes, read at the two pinnings.  Both are the associator
of the monoidal structure on `Comp(Mod(𝒪))` whose tensor product is the total tensor complex, so
the two differ only in how that structure is named. -/
theorem complexAssociatorPair_eq_topos
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    complexAssociatorPair Z K L M = complexAssociatorPairTopos Z K L M :=
  rfl

end Bridges

/-! ### The model of the derived pullback of a total tensor complex -/

section Models

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
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

omit [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))] in
include hmos in
/-- **[Stacks, Tag 0G7E] at the pinned spelling of K-flatness**: the degreewise pullback of a
K-flat complex of `𝒪'`-modules with flat terms is a K-flat complex of `𝒪`-modules, with the
conclusion read at `Stacks.SheafOfModules.KFlat`, which is the predicate the comparison of
[Stacks, Tag 06YU] is stated at. -/
theorem kFlat_pullbackComplex_pinned
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    Stacks.SheafOfModules.KFlat X.O ((pullbackComplex f).obj K) :=
  (Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor X.O _).mpr
    (kFlat_pullbackComplex' f hmos K
      ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O K).mp hK) hflat)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
include hmos in
/-- **The comparison of [Stacks, Tag 06YY] at a K-flat complex with flat terms is
invertible.**  It is the `hom` of `Stacks.Sheaves.DerivedPullback.flatPullbackIso`. -/
theorem isIso_pullbackComparisonQ
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    IsIso (pullbackComparisonQ f K) :=
  let hK' := (Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O K).mp hK
  flatPullbackIso_hom_eq_pullbackComparisonQ f hmos K hK' hflat ▸
    (flatPullbackIso f hmos K hK' hflat).isIso_hom

/-- **The comparison `f^*Tot(K ⊗_{𝒪'} L) ⟶ Tot(f^*K ⊗_𝒪 f^*L)` of [Stacks, Tag 03EL]**, with
its source and target written through
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` rather than through
`HomologicalComplex.mapBifunctor`.

The two spellings denote the same complex, but the identification is a conversion the
`HomologicalComplex` instance arguments make expensive; everything below is written at the
former, which is the spelling the constraints of [Stacks, Tag 0FPT] are pinned at, and this
definition pays for the identification **once**. -/
def pullbackTensorComplexPair
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackComplex f).obj
        ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)) ⟶
      (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
          ((pullbackComplex f).obj K, (pullbackComplex f).obj L) :=
  (pullbackToposTensorTotalIso f hmos K L).hom

omit [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))] in
/-- `Stacks.Sheaves.DerivedPullback.pullbackTensorComplexPair` *is* the comparison of total
tensor complexes of [Stacks, Tag 03EL]. -/
theorem pullbackTensorComplexPair_eq
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    pullbackTensorComplexPair f hmos K L = (pullbackTensorComplexIso f hmos K L).hom :=
  rfl

/-- **The model of `Lf^*(QK ⊗^L_{𝒪'} QL)` on a pair of complexes**: the comparison of
[Stacks, Tag 06YY] at the total tensor complex, followed by the comparison
`f^*Tot(K ⊗_{𝒪'} L) ≅ Tot(f^*K ⊗_𝒪 f^*L)` of [Stacks, Tag 03EL].

Every term is written at the
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` spelling of the total tensor complex,
which is the one the constraints of [Stacks, Tag 0FPT] are pinned at. -/
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
    DerivedCategory.Q.map (pullbackTensorComplexPair f hmos K L)

/-- `Stacks.Sheaves.DerivedPullback.pullbackTensorModel` is the comparison of
[Stacks, Tag 06YY] followed by the comparison of total tensor complexes of
[Stacks, Tag 03EL], with both written at the
`Stacks.SheafOfModules.Tensor.tensorComplex` spelling. -/
theorem pullbackTensorModel_eq
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    pullbackTensorModel f hmos K L =
      pullbackComparisonQ f (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj K).obj L) ≫
        DerivedCategory.Q.map (pullbackTensorComplexIso f hmos K L).hom :=
  rfl

/-- **The model of `Lf^*((QK ⊗^L QL) ⊗^L QM)`**: the model of
`Stacks.Sheaves.DerivedPullback.pullbackTensorModel` at the pair `(Tot(K ⊗ L), M)`, followed by
the comparison of [Stacks, Tag 03EL] in the first tensor factor.  This is the arrow of the
associativity square out of the left bracketing of the triple tensor product. -/
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
  pullbackTensorModel f hmos
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)) M ≫
    DerivedCategory.Q.map
      (totalComplexMapRight X (pullbackTensorComplexPair f hmos K L)
        ((pullbackComplex f).obj M))

/-- **The model of `Lf^*(QK ⊗^L (QL ⊗^L QM))`**; the companion of
`Stacks.Sheaves.DerivedPullback.pullbackTensorModelTripleLeft`, the arrow of the associativity
square out of the right bracketing of the triple tensor product. -/
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
  pullbackTensorModel f hmos K
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M)) ≫
    DerivedCategory.Q.map
      (totalComplexMapLeft X ((pullbackComplex f).obj K)
        (pullbackTensorComplexPair f hmos L M))

/-! ### The two models of the triple tensor product, matched -/

omit [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))] in
/-- **The left-hand side of the coherence of [Stacks, Tag 03EL], read at the
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` spelling.**  Splitting the
identification of the two pinnings of the total tensor complex into the two sides of the
coherence separately is what keeps each declaration inside the heartbeat budget. -/
theorem pullbackTensorComplexPair_associator_lhs
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    pullbackTensorComplexPair f hmos
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)) M ≫
        totalComplexMapRight X (pullbackTensorComplexPair f hmos K L)
            ((pullbackComplex f).obj M) ≫
          complexAssociatorPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
            ((pullbackComplex f).obj M) =
      (pullbackToposTensorTotalIso f hmos (totalObj Y K L) M).hom ≫
        totalComplexMapRightTopos X ((pullbackToposTensorTotalIso f hmos K L).hom)
            ((pullbackComplex f).obj M) ≫
          complexAssociatorPairTopos X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
            ((pullbackComplex f).obj M) := by
  rw [totalComplexMapRight_eq_topos]
  rfl

omit [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))] in
/-- **The right-hand side of the coherence of [Stacks, Tag 03EL], read at the
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` spelling**; the companion of
`Stacks.Sheaves.DerivedPullback.pullbackTensorComplexPair_associator_lhs`. -/
theorem pullbackTensorComplexPair_associator_rhs
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackComplex f).map (complexAssociatorPair Y K L M) ≫
        pullbackTensorComplexPair f hmos K
            ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M)) ≫
          totalComplexMapLeft X ((pullbackComplex f).obj K)
            (pullbackTensorComplexPair f hmos L M) =
      (pullbackComplex f).map (complexAssociatorPairTopos Y K L M) ≫
        (pullbackToposTensorTotalIso f hmos K (totalObj Y L M)).hom ≫
          totalComplexMapLeftTopos X ((pullbackComplex f).obj K)
            ((pullbackToposTensorTotalIso f hmos L M).hom) := by
  rw [totalComplexMapLeft_eq_topos]
  rfl

omit [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))] in
/-- **The comparison of [Stacks, Tag 03EL] on total complexes is compatible with the associator
of total tensor complexes**, with every term written at the
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` spelling.  This is
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso_associator_pair` read through
`Stacks.Sheaves.DerivedPullback.pullbackTensorComplexPair_associator_lhs` and
`pullbackTensorComplexPair_associator_rhs`; no total complex is taken apart. -/
theorem pullbackTensorComplexPair_associator_pair
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    pullbackTensorComplexPair f hmos
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)) M ≫
        totalComplexMapRight X (pullbackTensorComplexPair f hmos K L)
            ((pullbackComplex f).obj M) ≫
          complexAssociatorPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
            ((pullbackComplex f).obj M) =
      (pullbackComplex f).map (complexAssociatorPair Y K L M) ≫
        pullbackTensorComplexPair f hmos K
            ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M)) ≫
          totalComplexMapLeft X ((pullbackComplex f).obj K)
            (pullbackTensorComplexPair f hmos L M) :=
  (pullbackTensorComplexPair_associator_lhs f hmos K L M).trans
    ((pullbackToposTensorTotalIso_associator_pair f hmos K L M).trans
      (pullbackTensorComplexPair_associator_rhs f hmos K L M).symm)

omit [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))] in
/-- `Stacks.Sheaves.DerivedPullback.pullbackTensorComplexPair_associator_pair` in the derived
category, with the three factors of each side carried across `DerivedCategory.Q` separately.
Splitting this off keeps the declaration that uses it inside the heartbeat budget. -/
theorem pullbackTensorComplexPair_associator_pair_Q
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    DerivedCategory.Q.map (pullbackTensorComplexPair f hmos
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)) M) ≫
        DerivedCategory.Q.map
            (totalComplexMapRight X (pullbackTensorComplexPair f hmos K L)
              ((pullbackComplex f).obj M)) ≫
          DerivedCategory.Q.map
            (complexAssociatorPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
              ((pullbackComplex f).obj M)) =
      DerivedCategory.Q.map ((pullbackComplex f).map (complexAssociatorPair Y K L M)) ≫
        DerivedCategory.Q.map (pullbackTensorComplexPair f hmos K
            ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M))) ≫
          DerivedCategory.Q.map
            (totalComplexMapLeft X ((pullbackComplex f).obj K)
              (pullbackTensorComplexPair f hmos L M)) :=
  by simpa only [Functor.map_comp] using
    congrArg DerivedCategory.Q.map (pullbackTensorComplexPair_associator_pair f hmos K L M)

/-- **The model of `Lf^*(QK ⊗^L QL)` carries the associator of complexes to the associator of
complexes**, at the `Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` spelling.  The
comparison of [Stacks, Tag 06YY] is natural in the complex, and the comparison of total tensor
complexes of [Stacks, Tag 03EL] is compatible with the associator
(`Stacks.Sheaves.DerivedPullback.pullbackTensorComplexPair_associator_pair`).  This is the
identity linking the two models of the triple tensor product that the diagram chase asks for. -/
theorem pullbackTensorModel_assoc_pair
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    pullbackTensorModelTripleLeft f hmos K L M ≫
        DerivedCategory.Q.map
          (complexAssociatorPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
            ((pullbackComplex f).obj M)) =
      (derivedPullback f).map
          (DerivedCategory.Q.map (complexAssociatorPair Y K L M)) ≫
        pullbackTensorModelTripleRight f hmos K L M := by
  have hnat := pullbackComparisonQ_naturality f (complexAssociatorPair Y K L M)
  dsimp only [pullbackTensorModelTripleLeft, pullbackTensorModelTripleRight,
    pullbackTensorModel]
  simp only [Category.assoc]
  rw [pullbackTensorComplexPair_associator_pair_Q f hmos K L M, reassoc_of% hnat]

/-- **The model identification of [Stacks, Tag 07A4] at a pair of K-flat complexes with flat
terms**: the comparison `Lf^*(QK ⊗^L_{𝒪'} QL) ⟶ Lf^*QK ⊗^L_𝒪 Lf^*QL`, followed by the
comparison of [Stacks, Tag 06YY] in each tensor factor and the comparison of
[Stacks, Tag 06YU], is the derived pullback of the comparison of [Stacks, Tag 06YU] followed by
`Stacks.Sheaves.DerivedPullback.pullbackTensorModel`.

This is the square of [Stacks, Tag 0FPH] with its two canonical maps to the ordinary total
tensor complex read as the comparison of [Stacks, Tag 06YU] at the pinned spelling. -/
theorem derivedPullbackTensorIso_hom_app_comp_comparisonPair
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    (derivedPullbackTensorIso f hmos).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        (uncurriedDerivedTensor X).map
            (pullbackComparisonQ f K ×ₘ pullbackComparisonQ f L) ≫
          comparisonPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
            (kFlat_pullbackComplex_pinned f hmos K hK hfK)
            (kFlat_pullbackComplex_pinned f hmos L hL hfL) =
      (derivedPullback f).map (comparisonPair Y K L hK hL) ≫ pullbackTensorModel f hmos K L := by
  rw [comparisonPair_eq_toTensor, comparisonPair_eq_toTensor, pullbackTensorModel_eq]
  exact (derivedPullback_toTensor_square f hmos K L).symm

/-! ### The model identifications at the two triples -/

/-- The statement of
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_hom_app_comp_comparisonPair_left`, as a
`Prop`-valued `def` so that it and the proof term are elaborated in separate declarations. -/
def ModelIdentificationLeft
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    Prop :=
  (derivedPullbackTensorIso f hmos).hom.app
        (DerivedCategory.Q.obj
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)),
          DerivedCategory.Q.obj M) ≫
      (uncurriedDerivedTensor X).map
          (pullbackTensorModel f hmos K L ×ₘ pullbackComparisonQ f M) ≫
        comparisonPair X
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
              ((pullbackComplex f).obj K, (pullbackComplex f).obj L))
          ((pullbackComplex f).obj M)
          (kFlat_totalComplexPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
            (kFlat_pullbackComplex_pinned f hmos K hK hfK)
            (kFlat_pullbackComplex_pinned f hmos L hL hfL))
          (kFlat_pullbackComplex_pinned f hmos M hM hfM) =
    (derivedPullback f).map
        (comparisonPair Y
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)) M
          (kFlat_totalComplexPair Y K L hK hL) hM) ≫
      (pullbackTensorModelTripleLeft f hmos K L M)

/-- **The model identification of [Stacks, Tag 07A4] at the pair `(Tot(K ⊗ L), M)`, re-read
against the model `Tot(f^*K ⊗ f^*L)` of the first factor.**  The model identification itself
lands in `Q(f^*Tot(K ⊗ L))`, while the associativity square needs it against
`Q(Tot(f^*K ⊗ f^*L))`, and `CategoryTheory.bifunctor_comparison_model_comp_left` re-reads it
there along the naturality of the comparison of [Stacks, Tag 06YU] in its first variable. -/
theorem derivedPullbackTensorIso_hom_app_comp_comparisonPair_left
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    ModelIdentificationLeft f hmos K L M hK hL hM hfK hfL hfM :=
  bifunctor_comparison_model_comp_left (uncurriedDerivedTensor Y) (uncurriedDerivedTensor X)
    (derivedPullbackTensorIso f hmos).hom
    (derivedPullbackTensorIso_hom_app_comp_comparisonPair f hmos
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L)) M
      (kFlat_totalComplexPair Y K L hK hL) hM
      (isFlat_totalComplexPair_X Y K L hfK hfL) hfM)
    (comparisonPair_naturality_right X (pullbackTensorComplexPair f hmos K L)
      (kFlat_pullbackComplex_pinned f hmos
        ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (K, L))
        (kFlat_totalComplexPair Y K L hK hL) (isFlat_totalComplexPair_X Y K L hfK hfL))
      (kFlat_totalComplexPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
        (kFlat_pullbackComplex_pinned f hmos K hK hfK)
        (kFlat_pullbackComplex_pinned f hmos L hL hfL))
      (kFlat_pullbackComplex_pinned f hmos M hM hfM))

/-- The statement of
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_hom_app_comp_comparisonPair_right`, as a
`Prop`-valued `def` for the same reason as
`Stacks.Sheaves.DerivedPullback.ModelIdentificationLeft`. -/
def ModelIdentificationRight
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    Prop :=
  (derivedPullbackTensorIso f hmos).hom.app
        (DerivedCategory.Q.obj K,
          DerivedCategory.Q.obj
            ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M))) ≫
      (uncurriedDerivedTensor X).map
          (pullbackComparisonQ f K ×ₘ pullbackTensorModel f hmos L M) ≫
        comparisonPair X ((pullbackComplex f).obj K)
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
              ((pullbackComplex f).obj L, (pullbackComplex f).obj M))
          (kFlat_pullbackComplex_pinned f hmos K hK hfK)
          (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
            (kFlat_pullbackComplex_pinned f hmos L hL hfL)
            (kFlat_pullbackComplex_pinned f hmos M hM hfM)) =
    (derivedPullback f).map
        (comparisonPair Y K
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M)) hK
          (kFlat_totalComplexPair Y L M hL hM)) ≫
      (pullbackTensorModelTripleRight f hmos K L M)

/-- **The model identification of [Stacks, Tag 07A4] at the pair `(K, Tot(L ⊗ M))`, re-read
against the model `Tot(f^*L ⊗ f^*M)` of the second factor**; the companion of
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_hom_app_comp_comparisonPair_left`. -/
theorem derivedPullbackTensorIso_hom_app_comp_comparisonPair_right
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    ModelIdentificationRight f hmos K L M hK hL hM hfK hfL hfM :=
  bifunctor_comparison_model_comp_right (uncurriedDerivedTensor Y) (uncurriedDerivedTensor X)
    (derivedPullbackTensorIso f hmos).hom
    (derivedPullbackTensorIso_hom_app_comp_comparisonPair f hmos K
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M))
      hK (kFlat_totalComplexPair Y L M hL hM) hfK
      (isFlat_totalComplexPair_X Y L M hfL hfM))
    (comparisonPair_naturality_left X (pullbackTensorComplexPair f hmos L M)
      (kFlat_pullbackComplex_pinned f hmos K hK hfK)
      (kFlat_pullbackComplex_pinned f hmos
        ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M))
        (kFlat_totalComplexPair Y L M hL hM) (isFlat_totalComplexPair_X Y L M hfL hfM))
      (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
        (kFlat_pullbackComplex_pinned f hmos L hL hfL)
        (kFlat_pullbackComplex_pinned f hmos M hM hfM)))

/-! ### The corner the associativity chase cancels -/

/-- **The composite the associativity chase cancels is an isomorphism.**  It is the pair of
comparisons of [Stacks, Tag 06YY] in the last two factors, tensored and followed by the
comparison of [Stacks, Tag 06YU], tensored against the first factor and followed by the
comparison of [Stacks, Tag 06YU] again: each factor is invertible on K-flat complexes with flat
terms, so the composite is. -/
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
                (kFlat_pullbackComplex_pinned f hmos L hL hfL)
                (kFlat_pullbackComplex_pinned f hmos M hM hfM))) ≫
        comparisonPair X ((pullbackComplex f).obj K)
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
              ((pullbackComplex f).obj L, (pullbackComplex f).obj M))
          (kFlat_pullbackComplex_pinned f hmos K hK hfK)
          (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
            (kFlat_pullbackComplex_pinned f hmos L hL hfL)
            (kFlat_pullbackComplex_pinned f hmos M hM hfM))) := by
  have hKx := kFlat_pullbackComplex_pinned f hmos K hK hfK
  have hLx := kFlat_pullbackComplex_pinned f hmos L hL hfL
  have hMx := kFlat_pullbackComplex_pinned f hmos M hM hfM
  have : IsIso (pullbackComparisonQ f L ×ₘ pullbackComparisonQ f M) :=
    (isIso_prod_iff _ _).mpr
      ⟨isIso_pullbackComparisonQ f hmos L hL hfL, isIso_pullbackComparisonQ f hmos M hM hfM⟩
  have := isIso_comparisonPair X _ _ hLx hMx
  have : IsIso (pullbackComparisonQ f K ×ₘ ((uncurriedDerivedTensor X).map
      (pullbackComparisonQ f L ×ₘ pullbackComparisonQ f M) ≫
        comparisonPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M) hLx hMx)) :=
    (isIso_prod_iff _ _).mpr ⟨isIso_pullbackComparisonQ f hmos K hK hfK, inferInstance⟩
  have := isIso_comparisonPair X _ _ hKx (kFlat_totalComplexPair X _ _ hLx hMx)
  infer_instance

/-- The composite the associativity chase cancels is a monomorphism.  It is an isomorphism
(`Stacks.Sheaves.DerivedPullback.isIso_modelCorner`); stating the consequence in its own
declaration is what keeps the instance search off the diagram chase, where the morphism it would
have to be found for is still half unknown. -/
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
                (kFlat_pullbackComplex_pinned f hmos L hL hfL)
                (kFlat_pullbackComplex_pinned f hmos M hM hfM))) ≫
        comparisonPair X ((pullbackComplex f).obj K)
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
              ((pullbackComplex f).obj L, (pullbackComplex f).obj M))
          (kFlat_pullbackComplex_pinned f hmos K hK hfK)
          (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
            (kFlat_pullbackComplex_pinned f hmos L hL hfL)
            (kFlat_pullbackComplex_pinned f hmos M hM hfM))) := by
  have := isIso_modelCorner f hmos K L M hK hL hM hfK hfL hfM
  infer_instance

/-! ### The five bundles of the chase -/

/-- **The objects and maps of the associativity chase, and the two laws its models satisfy**, as
a `Prop`-valued `def` so that naming the eleven objects and sixteen maps and proving the three
fields are elaborated in separate declarations.  The source models are the comparison of
[Stacks, Tag 06YU] on `D(𝒪')` at the pinned spelling
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
      (kFlat_pullbackComplex_pinned f hmos K hK hfK)
      (kFlat_pullbackComplex_pinned f hmos L hL hfL))
    (comparisonPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
      (kFlat_pullbackComplex_pinned f hmos L hL hfL)
      (kFlat_pullbackComplex_pinned f hmos M hM hfM))
    (comparisonPair X
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
          ((pullbackComplex f).obj K, (pullbackComplex f).obj L))
      ((pullbackComplex f).obj M)
      (kFlat_totalComplexPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
        (kFlat_pullbackComplex_pinned f hmos K hK hfK)
        (kFlat_pullbackComplex_pinned f hmos L hL hfL))
      (kFlat_pullbackComplex_pinned f hmos M hM hfM))
    (comparisonPair X ((pullbackComplex f).obj K)
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
          ((pullbackComplex f).obj L, (pullbackComplex f).obj M))
      (kFlat_pullbackComplex_pinned f hmos K hK hfK)
      (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
        (kFlat_pullbackComplex_pinned f hmos L hL hfL)
        (kFlat_pullbackComplex_pinned f hmos M hM hfM)))
    (DerivedCategory.Q.map (complexAssociatorPair X ((pullbackComplex f).obj K)
      ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)))

/-- **The two associativity laws of the models and the naturality of the constraint of
[Stacks, Tag 0FPT].**  Both laws are the associativity clause of [Stacks, Tag 0FPT] in uncurried,
pinned form
(`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.canonicalComparison_associator_uncurried`),
read on `Y` and on `X`; the naturality is
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.canonicalAssociatorHom_naturality` at the
three comparisons of [Stacks, Tag 06YY]. -/
theorem assocModelLaws
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    AssocLaws f hmos K L M hK hL hM hfK hfL hfM :=
  ⟨canonicalComparison_associator_uncurried Y K L M hK hL hM,
    canonicalComparison_associator_uncurried X ((pullbackComplex f).obj K)
      ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
      (kFlat_pullbackComplex_pinned f hmos K hK hfK)
      (kFlat_pullbackComplex_pinned f hmos L hL hfL)
      (kFlat_pullbackComplex_pinned f hmos M hM hfM),
    canonicalAssociatorHom_naturality X (pullbackComparisonQ f K) (pullbackComparisonQ f L)
      (pullbackComparisonQ f M)⟩

/-- The statement of `Stacks.Sheaves.DerivedPullback.assocModelPairs`, as a `Prop`-valued `def`
for the same reason as `Stacks.Sheaves.DerivedPullback.AssocLaws`. -/
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
    (derivedPullbackTensorIso f hmos).hom
    (pullbackComparisonQ f K) (pullbackComparisonQ f L) (pullbackComparisonQ f M)
    (comparisonPair Y K L hK hL) (comparisonPair Y L M hL hM)
    (comparisonPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
      (kFlat_pullbackComplex_pinned f hmos K hK hfK)
      (kFlat_pullbackComplex_pinned f hmos L hL hfL))
    (comparisonPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
      (kFlat_pullbackComplex_pinned f hmos L hL hfL)
      (kFlat_pullbackComplex_pinned f hmos M hM hfM))
    (pullbackTensorModel f hmos K L) (pullbackTensorModel f hmos L M)

/-- **The model identifications of [Stacks, Tag 07A4] at the pairs `(K, L)` and `(L, M)`**, which
are
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_hom_app_comp_comparisonPair` at those
two pairs. -/
theorem assocModelPairs
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    AssocPairs f hmos K L M hK hL hM hfK hfL hfM :=
  ⟨derivedPullbackTensorIso_hom_app_comp_comparisonPair f hmos K L hK hL hfK hfL,
    derivedPullbackTensorIso_hom_app_comp_comparisonPair f hmos L M hL hM hfL hfM⟩

/-- The statement of `Stacks.Sheaves.DerivedPullback.assocModelTripleLeft`, as a `Prop`-valued
`def` for the same reason as `Stacks.Sheaves.DerivedPullback.AssocLaws`. -/
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
    (derivedPullbackTensorIso f hmos).hom
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
        (kFlat_pullbackComplex_pinned f hmos K hK hfK)
        (kFlat_pullbackComplex_pinned f hmos L hL hfL))
      (kFlat_pullbackComplex_pinned f hmos M hM hfM))
    (pullbackTensorModel f hmos K L)
    (pullbackTensorModelTripleLeft f hmos K L M)

/-- **The model identification of [Stacks, Tag 07A4] at `(Tot(K ⊗ L), M)`, read against the model
`Tot(f^*K ⊗ f^*L)` of the first factor**, which is
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_hom_app_comp_comparisonPair_left`. -/
theorem assocModelTripleLeft
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    AssocTripleLeft f hmos K L M hK hL hM hfK hfL hfM :=
  ⟨derivedPullbackTensorIso_hom_app_comp_comparisonPair_left f hmos K L M hK hL hM
    hfK hfL hfM⟩

/-- The statement of `Stacks.Sheaves.DerivedPullback.assocModelTripleRight`, as a `Prop`-valued
`def` for the same reason as `Stacks.Sheaves.DerivedPullback.AssocLaws`. -/
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
    (derivedPullbackTensorIso f hmos).hom
    (pullbackComparisonQ f K)
    (comparisonPair Y K
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).obj (L, M)) hK
      (kFlat_totalComplexPair Y L M hL hM))
    (comparisonPair X ((pullbackComplex f).obj K)
      ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
          ((pullbackComplex f).obj L, (pullbackComplex f).obj M))
      (kFlat_pullbackComplex_pinned f hmos K hK hfK)
      (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
        (kFlat_pullbackComplex_pinned f hmos L hL hfL)
        (kFlat_pullbackComplex_pinned f hmos M hM hfM)))
    (pullbackTensorModel f hmos L M)
    (pullbackTensorModelTripleRight f hmos K L M)

/-- **The model identification of [Stacks, Tag 07A4] at `(K, Tot(L ⊗ M))`, read against the model
`Tot(f^*L ⊗ f^*M)` of the second factor**, which is
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_hom_app_comp_comparisonPair_right`. -/
theorem assocModelTripleRight
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hL : Stacks.SheafOfModules.KFlat Y.O L)
    (hM : Stacks.SheafOfModules.KFlat Y.O M)
    (hfK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hfL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (hfM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)) :
    AssocTripleRight f hmos K L M hK hL hM hfK hfL hfM :=
  ⟨derivedPullbackTensorIso_hom_app_comp_comparisonPair_right f hmos K L M hK hL hM
    hfK hfL hfM⟩

/-- **The identity linking the two models of the triple tensor product.**  The two model
comparisons out of `Tot(Tot(K ⊗ L) ⊗ M)` and `Tot(K ⊗ Tot(L ⊗ M))` land in different objects of
`D(𝒪)`, and this matches the associator of total tensor complexes upstairs with the one
downstairs: it is the associativity coherence of the comparison
`f^*Tot(K ⊗_{𝒪'} L) ≅ Tot(f^*K ⊗_𝒪 f^*L)` of [Stacks, Tag 03EL], pushed into the derived
category along the comparison of [Stacks, Tag 06YY]. -/
def AssocLink
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    Prop :=
  AssocModelLink (derivedPullback f)
    (DerivedCategory.Q.map (complexAssociatorPair Y K L M))
    (DerivedCategory.Q.map (complexAssociatorPair X ((pullbackComplex f).obj K)
      ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)))
    (pullbackTensorModelTripleLeft f hmos K L M)
    (pullbackTensorModelTripleRight f hmos K L M)

/-- **The identity linking the two models of the triple tensor product**, which is
`Stacks.Sheaves.DerivedPullback.pullbackTensorModel_assoc_pair`: the associativity coherence of
the comparison of [Stacks, Tag 03EL] on total complexes, pushed into the derived category along
the comparison of [Stacks, Tag 06YY]. -/
theorem assocModelLink
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    AssocLink f hmos K L M :=
  ⟨pullbackTensorModel_assoc_pair f hmos K L M⟩

/-! ### The associativity law at a triple of K-flat complexes with flat terms -/

/-- **The comparison of [Stacks, Tag 07A4] carries the associativity constraint of
[Stacks, Tag 0FPT] on `D(𝒪')` to the one on `D(𝒪)`, at a triple of K-flat complexes with flat
terms.**

The diagram chase is `CategoryTheory.bifunctor_comparison_assoc_of_bundles`: the models are the
comparison of [Stacks, Tag 06YU] on both sides at the pinned spelling
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.comparisonPair`, the model of the comparison
of [Stacks, Tag 07A4] at a pair is the square of [Stacks, Tag 0FPH], and the compatibility of
the models with the two constraints is the associativity clause of [Stacks, Tag 0FPT].  The
equation proved is spelled out in
`Stacks.Sheaves.DerivedPullback.DerivedPullbackTensorIsoAssociator`.

The identity matching the two models of the triple tensor product, spelled out in
`Stacks.Sheaves.DerivedPullback.AssocLink`, is the associativity coherence of the comparison
`f^*Tot(K ⊗_{𝒪'} L) ≅ Tot(f^*K ⊗_𝒪 f^*L)` of [Stacks, Tag 03EL] on total complexes, pushed into
the derived category. -/
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
    DerivedPullbackTensorIsoAssociator f hmos (DerivedCategory.Q.obj K)
      (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M) :=
  let hK' := (Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O K).mpr hK
  let hL' := (Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O L).mpr hL
  let hM' := (Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O M).mpr hM
  bifunctor_comparison_assoc_of_bundles
    (mono_modelCorner f hmos K L M hK' hL' hM' hfK hfL hfM)
    (assocModelLaws f hmos K L M hK' hL' hM' hfK hfL hfM)
    (assocModelPairs f hmos K L M hK' hL' hM' hfK hfL hfM)
    (assocModelTripleLeft f hmos K L M hK' hL' hM' hfK hfL hfM)
    (assocModelTripleRight f hmos K L M hK' hL' hM' hfK hfL hfM)
    (assocModelLink f hmos K L M)

end Models

end Stacks.Sheaves.DerivedPullback

end
