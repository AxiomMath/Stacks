module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.DualizingHomothetyIso
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentDerivedDualityBounded
public import
  StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentDerivedDualityCoherence
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentDuality
public import StacksFrontier.AlgebraicGeometry.InternalHomEvaluation.DualizingEvaluation
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.Duality
import StacksCore.Tactic.StacksAttribute

/-!
# Canonical biduality is an isomorphism, and the two anti-equivalences of Tag 0A89

Let `X` be a locally Noetherian scheme and `K` a dualizing complex on `X` ([Stacks, Tag 0A87]).
The canonical biduality morphism of [Stacks, Tag 0A89]

`L ⟶ R𝓗om_{𝒪_X}(R𝓗om_{𝒪_X}(L, K), K)`

(`Stacks.Duality.dualizingDerivedSheafHomBiduality`) is an isomorphism at every object `L` of
`D_Coh(𝒪_X)`, and `D = R𝓗om_{𝒪_X}(-, K)` is therefore an anti-equivalence of `D_Coh(𝒪_X)`, and
of `D^b_Coh(𝒪_X)` when `X` is in addition quasi-compact.

## The two factors

The biduality morphism factors, by `Stacks.SheafOfModules.derivedSheafHomBidualMap_eq`, as the
left unitor read backwards, the homothety of `K` whiskered by `L`, and the derived evaluation
morphism of [Stacks, Tag 0A8U] at `(L, K, K)`. Both of the last two are invertible:

* the homothety `𝒪_X[0] ⟶ R𝓗om_{𝒪_X}(K, K)` of a dualizing complex is an isomorphism,
  `Stacks.Duality.isIso_derivedSheafHomothety_of_isDualizingComplex`;
* the evaluation morphism `R𝓗om_{𝒪_X}(K, K) ⊗^𝐋_{𝒪_X} L ⟶ R𝓗om_{𝒪_X}(R𝓗om_{𝒪_X}(L, K), K)` is
  an isomorphism for `L` with coherent cohomology sheaves,
  `Stacks.Duality.isIso_derivedSheafHomEvaluation_of_isDualizingComplex`.

Whiskering by `L` carries an isomorphism to an isomorphism, and the left unitor is one, so the
composite is invertible. The hypothesis on `L` is exactly membership in `D_Coh(𝒪_X)`, which is
where the tag asserts the biduality.

## From biduality to the anti-equivalences

A contravariant functor whose square is naturally isomorphic to the identity is an equivalence,
`Dualizing.isEquivalence_of_opOpNatIso`; that is the only categorical input. On `D_Coh(𝒪_X)` the
functor is `Stacks.Duality.coherentDualizingDerivedSheafHomFunctor`, which lands in the
subcategory by `Stacks.Duality.derivedCategoryB_isCoherent_dualizingDerivedSheafHom`; on
`D^b_Coh(𝒪_X)` it is `Stacks.Duality.boundedCoherentDualizingDerivedSheafHomFunctor`, which
lands there by `Stacks.Duality.derivedCategoryBBounded_isCoherent_dualizingDerivedSheafHom`,
whose two bounds are the two boundedness exchanges of
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/CoherentDerivedDualityBounded.lean` and
therefore ask for `X` quasi-compact. In both cases a morphism of a full subcategory is
invertible as soon as the underlying morphism is, so each component of the restricted biduality
is an isomorphism and the whole natural transformation is one.

This is the scheme-level counterpart of the affine decomposition of [Stacks, Tag 0A7C] in
`StacksFrontier/RingTheory/Dualizing/DerivedHomDuality/Duality.lean`, which this file mirrors
statement for statement.

## Main definitions

* `Stacks.Duality.coherentDualizingDerivedSheafHomBiduality` and
  `Stacks.Duality.coherentDualizingDerivedSheafHomBidualityIso`: canonical biduality on
  `D_Coh(𝒪_X)`, and the natural isomorphism it is.
* `Stacks.Duality.boundedCoherentDualizingDerivedSheafHomFunctor`,
  `Stacks.Duality.boundedCoherentDualizingDerivedSheafHomBiduality` and
  `Stacks.Duality.boundedCoherentDualizingDerivedSheafHomBidualityIso`: the same on
  `D^b_Coh(𝒪_X)`, which is `Stacks.Duality.BoundedCoherentDerivedCategory` of
  `StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/CoherentDuality.lean`.

## Main results

* `Stacks.Duality.isIso_dualizingDerivedSheafHomBiduality_app`: **[Stacks, Tag 0A89], canonical
  biduality** — the morphism `L ⟶ R𝓗om(R𝓗om(L, K), K)` is an isomorphism for every `L` of
  `D_Coh(𝒪_X)`.
* `Stacks.Duality.coherentDualizingDerivedSheafHom_isEquivalence`: **[Stacks, Tag 0A89], the
  anti-equivalence on coherent objects.**
* `Stacks.Duality.boundedCoherentDualizingDerivedSheafHom_isEquivalence`: **[Stacks, Tag 0A89],
  the bounded anti-equivalence**, for `X` quasi-compact.

## References

* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 0A8U](https://stacks.math.columbia.edu/tag/0A8U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

-- Standard model only: `Stacks.SheafOfModules.derivedSheafHomothety`.
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] derivedMonoidalStructure

variable {Y : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} Y)
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor.{u, u, u, u, u} Rc)
      (ComplexShape.up ℤ)]

/-- **The canonical biduality morphism is an isomorphism as soon as its two non-formal factors
are.** By `Stacks.SheafOfModules.derivedSheafHomBidualMap_eq` the morphism is the left unitor
read backwards, the homothety of `K` whiskered by `L`, and the derived evaluation morphism of
[Stacks, Tag 0A8U] at `(L, K, K)`. The left unitor is invertible for formal reasons and
whiskering carries an isomorphism to an isomorphism, so the homothety and the evaluation
morphism are the whole content. -/
theorem isIso_derivedSheafHomBidualMap
    (K L : DerivedCategory (StructureSheafModules Rc))
    (hh : IsIso (derivedSheafHomothety Rc K))
    (he : IsIso (derivedSheafHomEvaluation Rc L K K)) :
    IsIso (derivedSheafHomBidualMap Rc K L) := by
  rw [derivedSheafHomBidualMap_eq]
  have := hh
  have := he
  have : IsIso (derivedSheafHomothety Rc K ▷ L) :=
    (whiskerRightIso (asIso (derivedSheafHomothety Rc K)) L).isIso_hom
  infer_instance

end Stacks.SheafOfModules

namespace Stacks.Duality

open Stacks.SheafOfModules

-- Standard model only: `Stacks.SheafOfModules.derivedSheafHomothety`,
--   `Stacks.SheafOfModules.derivedSheafHom`.
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable {X : Scheme.{u}}

/-! ### Biduality at an object of `D_Coh` -/

/-- **Stacks Project, Tag 0A89.** The canonical biduality morphism

`L ⟶ R𝓗om_{𝒪_X}(R𝓗om_{𝒪_X}(L, K), K)`

is an isomorphism, for `K` a dualizing complex on a locally Noetherian scheme `X` and `L` an
object of `D_Coh(𝒪_X)`.

The morphism is the left unitor read backwards, the homothety of `K` whiskered by `L`, and the
derived evaluation morphism of [Stacks, Tag 0A8U] at `(L, K, K)`
(`Stacks.SheafOfModules.isIso_derivedSheafHomBidualMap`). The homothety of a dualizing complex
is invertible (`Stacks.Duality.isIso_derivedSheafHomothety_of_isDualizingComplex`), and the
evaluation morphism is invertible at a source with coherent cohomology sheaves
(`Stacks.Duality.isIso_derivedSheafHomEvaluation_of_isDualizingComplex`). -/
@[stacks 0A89 "canonical biduality"]
theorem isIso_dualizingDerivedSheafHomBiduality_app [IsLocallyNoetherian X]
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) (L : DerivedCategory X.Modules)
    (hL : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent) :
    IsIso ((dualizingDerivedSheafHomBiduality X K).app L) := by
  -- Apply the component equation in term position: left to the elaborator, identifying the
  -- component of the natural transformation with `derivedSheafHomBidualMap` is a `whnf` through
  -- the whole re-seated monoidal structure, which does not terminate inside the heartbeat limit.
  rw [dualizingDerivedSheafHomBiduality_app]
  exact isIso_derivedSheafHomBidualMap X.sheaf K L
    (isIso_derivedSheafHomothety_of_isDualizingComplex K hK)
    (isIso_derivedSheafHomEvaluation_of_isDualizingComplex hK hL)

/-! ### The anti-equivalence of `D_Coh` -/

/-- **Canonical biduality on `D_Coh(𝒪_X)`**: the natural transformation
`𝟭 ⟶ opOp ⋙ D.op ⋙ D` on `D_Coh(𝒪_X)`, for `D` the functor
`Stacks.Duality.coherentDualizingDerivedSheafHomFunctor`. Its components are those of
`Stacks.Duality.dualizingDerivedSheafHomBiduality` and its naturality is that one's. -/
def coherentDualizingDerivedSheafHomBiduality (X : Scheme.{u}) [IsLocallyNoetherian X]
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) :
    Functor.id (CoherentDerivedCategory X) ⟶
      opOp (CoherentDerivedCategory X) ⋙
        (coherentDualizingDerivedSheafHomFunctor X hK).op ⋙
          coherentDualizingDerivedSheafHomFunctor X hK where
  app L := ⟨(dualizingDerivedSheafHomBiduality X K).app L.obj⟩
  naturality {_L _L'} f := by
    ext
    exact (dualizingDerivedSheafHomBiduality X K).naturality f.hom

/-- **Canonical biduality is a natural isomorphism on `D_Coh(𝒪_X)`.** Each component is
invertible by `Stacks.Duality.isIso_dualizingDerivedSheafHomBiduality_app`, and a morphism of a
full subcategory is invertible as soon as the underlying morphism is. -/
theorem isIso_coherentDualizingDerivedSheafHomBiduality (X : Scheme.{u}) [IsLocallyNoetherian X]
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) :
    IsIso (coherentDualizingDerivedSheafHomBiduality X hK) := by
  have happ : ∀ L, IsIso ((coherentDualizingDerivedSheafHomBiduality X hK).app L) := fun L =>
    @isIso_of_reflects_iso _ _ _ _ _ _ _ (ObjectProperty.ι _)
      (isIso_dualizingDerivedSheafHomBiduality_app hK L.obj L.property) _
  exact NatIso.isIso_of_isIso_app _

/-- The canonical natural isomorphism from the identity functor to double derived duality on
`D_Coh(𝒪_X)`. -/
def coherentDualizingDerivedSheafHomBidualityIso (X : Scheme.{u}) [IsLocallyNoetherian X]
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) :
    Functor.id (CoherentDerivedCategory X) ≅
      opOp (CoherentDerivedCategory X) ⋙
        (coherentDualizingDerivedSheafHomFunctor X hK).op ⋙
          coherentDualizingDerivedSheafHomFunctor X hK :=
  have := isIso_coherentDualizingDerivedSheafHomBiduality X hK
  asIso (coherentDualizingDerivedSheafHomBiduality X hK)

/-- **Stacks Project, Tag 0A89.** `D = R𝓗om_{𝒪_X}(-, K)` is an anti-equivalence of
`D_Coh(𝒪_X)`, for `K` a dualizing complex on a locally Noetherian scheme `X`: canonical
biduality is a natural isomorphism, and a contravariant functor whose square is naturally
isomorphic to the identity is an equivalence. -/
@[stacks 0A89 "the anti-equivalence on coherent objects"]
theorem coherentDualizingDerivedSheafHom_isEquivalence (X : Scheme.{u}) [IsLocallyNoetherian X]
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) :
    (coherentDualizingDerivedSheafHomFunctor X hK).IsEquivalence :=
  Dualizing.isEquivalence_of_opOpNatIso _ (coherentDualizingDerivedSheafHomBidualityIso X hK)

/-! ### The anti-equivalence of `D^b_Coh` -/

/-- **The functor `D` induces on `D^b_Coh(𝒪_X)`**, for `K` a dualizing complex on a quasi-compact
locally Noetherian scheme: `D : D^b_Coh(𝒪_X)ᵒᵖ ⥤ D^b_Coh(𝒪_X)`. It lands in the subcategory by
`Stacks.Duality.derivedCategoryBBounded_isCoherent_dualizingDerivedSheafHom`, whose two bounds
are the boundedness exchanges and therefore need `X` quasi-compact.

This is the scheme-level counterpart of
`Dualizing.boundedCoherentDualizingDerivedHomFunctor`. -/
def boundedCoherentDualizingDerivedSheafHomFunctor (X : Scheme.{u}) [IsLocallyNoetherian X]
    [CompactSpace X] {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) :
    (BoundedCoherentDerivedCategory X)ᵒᵖ ⥤ BoundedCoherentDerivedCategory X where
  obj L := ⟨(dualizingDerivedSheafHomFunctor X K).obj (op L.unop.obj),
    derivedCategoryBBounded_isCoherent_dualizingDerivedSheafHom hK L.unop.obj L.unop.property⟩
  map f := ⟨(dualizingDerivedSheafHomFunctor X K).map ((ObjectProperty.ι _).map f.unop).op⟩
  map_id _ := by
    ext
    dsimp
    exact (dualizingDerivedSheafHomFunctor X K).map_id _
  map_comp f g := by
    ext
    dsimp
    exact (dualizingDerivedSheafHomFunctor X K).map_comp _ _

/-- **Canonical biduality on `D^b_Coh(𝒪_X)`**, the restriction of
`Stacks.Duality.dualizingDerivedSheafHomBiduality` to the bounded coherent objects. -/
def boundedCoherentDualizingDerivedSheafHomBiduality (X : Scheme.{u}) [IsLocallyNoetherian X]
    [CompactSpace X] {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) :
    Functor.id (BoundedCoherentDerivedCategory X) ⟶
      opOp (BoundedCoherentDerivedCategory X) ⋙
        (boundedCoherentDualizingDerivedSheafHomFunctor X hK).op ⋙
          boundedCoherentDualizingDerivedSheafHomFunctor X hK where
  app L := ⟨(dualizingDerivedSheafHomBiduality X K).app L.obj⟩
  naturality {_L _L'} f := by
    ext
    exact (dualizingDerivedSheafHomBiduality X K).naturality f.hom

/-- **Canonical biduality is a natural isomorphism on `D^b_Coh(𝒪_X)`.** -/
theorem isIso_boundedCoherentDualizingDerivedSheafHomBiduality (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) :
    IsIso (boundedCoherentDualizingDerivedSheafHomBiduality X hK) := by
  have happ : ∀ L,
      IsIso ((boundedCoherentDualizingDerivedSheafHomBiduality X hK).app L) := fun L =>
    @isIso_of_reflects_iso _ _ _ _ _ _ _ (ObjectProperty.ι _)
      (isIso_dualizingDerivedSheafHomBiduality_app hK L.obj L.property.2) _
  exact NatIso.isIso_of_isIso_app _

/-- The canonical natural isomorphism from the identity functor to double derived duality on
`D^b_Coh(𝒪_X)`. -/
def boundedCoherentDualizingDerivedSheafHomBidualityIso (X : Scheme.{u}) [IsLocallyNoetherian X]
    [CompactSpace X] {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) :
    Functor.id (BoundedCoherentDerivedCategory X) ≅
      opOp (BoundedCoherentDerivedCategory X) ⋙
        (boundedCoherentDualizingDerivedSheafHomFunctor X hK).op ⋙
          boundedCoherentDualizingDerivedSheafHomFunctor X hK :=
  have := isIso_boundedCoherentDualizingDerivedSheafHomBiduality X hK
  asIso (boundedCoherentDualizingDerivedSheafHomBiduality X hK)

/-- **Stacks Project, Tag 0A89.** `D = R𝓗om_{𝒪_X}(-, K)` is an anti-equivalence of
`D^b_Coh(𝒪_X)`, for `K` a dualizing complex on a quasi-compact locally Noetherian scheme `X`. -/
@[stacks 0A89 "the bounded anti-equivalence"]
theorem boundedCoherentDualizingDerivedSheafHom_isEquivalence (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) :
    (boundedCoherentDualizingDerivedSheafHomFunctor X hK).IsEquivalence :=
  Dualizing.isEquivalence_of_opOpNatIso _
    (boundedCoherentDualizingDerivedSheafHomBidualityIso X hK)

end Stacks.Duality

end
