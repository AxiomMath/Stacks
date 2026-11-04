module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.CoefficientHypotheses
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IdempotentCoefficientLFunction
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.CharSeriesIdempotent
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit

/-!
# Reduction of the trace formula for L-functions to local coefficient rings

Tag 03UZ: for `X` of finite type over a finite field `k`, a finite ring `Λ` of order prime to the
characteristic and a constructible flat `Λ`-module `F` on `X_étale`,
`L(X, F) = det(1 - π_X^* T | RΓ_c(X_k̄, F))⁻¹` in `Λ⟦T⟧`.

A finite commutative ring is a product of local rings, cut out by idempotents. This file reduces
the identity to local coefficient rings. For an idempotent `e` of `Λ` with factors
`Λ₁ = Λ ⧸ (1 - e)` and `Λ₂ = Λ ⧸ (e)`:

* `F` is the direct sum of the restrictions of scalars of `e F = Λ₁ ⊗_Λ F` and of
  `(1 - e) F = Λ₂ ⊗_Λ F` (`IsIdempotentElem.sheafBinaryBicone`), so `RΓ_c(X_k̄, F)` is the direct
  sum of `RΓ_c(X_k̄, e F)|_Λ` and `RΓ_c(X_k̄, (1 - e) F)|_Λ`, compatibly with `π_X^*`
  (`Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyRestrictScalarsIso`);
* the characteristic series over `Λ` of such a direct sum maps to those of the summands
  (`CategoryTheory.FilteredDerived.exists_isPerfect_map_perfectDerivedCharSeries_of_binaryBicone`);
* so does the L-function (`Stacks.EtaleCohomology.map_constructibleFlatLFunction_sheafBaseChange`);
* and a power series over `Λ` is determined by its two images (`IsIdempotentElem.powerSeries_ext`).

So the identity for `e F` and `(1 - e) F` gives the identity for `F`, and by induction on the
cardinality of `Λ` the identity for local coefficient rings gives it for all finite coefficient
rings.

## Main definitions

* `Stacks.EtaleCohomology.LFunctionCharSeriesIdentity`: the identity of Tag 03UZ, for one
  compactification and one presentation of the cardinality of `k`.

## Main results

* `Stacks.EtaleCohomology.lFunctionCharSeriesIdentity_of_isIdempotentElem`: the identity for
  `e F` and `(1 - e) F` implies it for `F`.
* `Stacks.EtaleCohomology.lFunctionCharSeriesIdentity_of_isLocalRing`: the identity for all
  finite local coefficient rings implies it for all finite commutative coefficient rings.

## References

* [Stacks Project, Tag 03UZ](https://stacks.math.columbia.edu/tag/03UZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Frobenius
open scoped TensorProduct ZeroObject

universe u r v

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The identity -/

section Identity

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ] [Finite Λ]
  [HasColimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r} Λ)]
  [HasLimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r} Λ)]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{max (u + 1) r} Λ) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ)]
  {k : Type u} [Field k] [Fintype k] (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **The identity of Tag 03UZ**, for a constructible flat sheaf `F` of `Λ`-modules, one
compactification `j` of `X` over `k` and one presentation `#k = p ^ q`: the complex
`RΓ_c(X_k̄, F)` is perfect and
`L(X, F) = det(1 - π_X^* T | RΓ_c(X_k̄, F))⁻¹` in `Λ⟦T⟧`. -/
public def LFunctionCharSeriesIdentity
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) (j : CompactificationOf (Over.mk f))
    (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q) : Prop :=
  let K := (Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ X.obj) 0).obj
    ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{max (u + 1) r} Λ)).functor.obj F)
  ∃ hperf : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K)),
    constructibleFlatLFunction B X Λ F f hF =
      ↑(CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hperf
        (DerivedCategory.Plus.ι.map
          (canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard K)))⁻¹

end Identity

/-! ### Transporting a direct sum decomposition along a functor -/

section Transport

variable {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] [Preadditive 𝒞] [Preadditive 𝒟]
  (Φ : 𝒞 ⥤ 𝒟) [Φ.Additive] {X Y : 𝒞} (b : BinaryBicone X Y) {X' Y' : 𝒟}
  (eX : Φ.obj X ≅ X') (eY : Φ.obj Y ≅ Y')

/-- The image of a binary bicone under an additive functor, with its summands replaced by
isomorphic objects. -/
public def binaryBiconeMapIsos : BinaryBicone X' Y' where
  pt := Φ.obj b.pt
  fst := Φ.map b.fst ≫ eX.hom
  snd := Φ.map b.snd ≫ eY.hom
  inl := eX.inv ≫ Φ.map b.inl
  inr := eY.inv ≫ Φ.map b.inr
  inl_fst := by simp [← Φ.map_comp_assoc]
  inl_snd := by simp [← Φ.map_comp_assoc]
  inr_fst := by simp [← Φ.map_comp_assoc]
  inr_snd := by simp [← Φ.map_comp_assoc]

/-- If `b` is a direct sum decomposition (`fst ≫ inl + snd ≫ inr = 𝟙`), so is its transport
`binaryBiconeMapIsos Φ b eX eY`. -/
public theorem binaryBiconeMapIsos_total (h : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt) :
    (binaryBiconeMapIsos Φ b eX eY).fst ≫ (binaryBiconeMapIsos Φ b eX eY).inl +
      (binaryBiconeMapIsos Φ b eX eY).snd ≫ (binaryBiconeMapIsos Φ b eX eY).inr =
        𝟙 (Φ.obj b.pt) := by
  simp only [binaryBiconeMapIsos, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Φ.map_comp, ← Φ.map_comp]
  exact (Φ.map_add (f := b.fst ≫ b.inl) (g := b.snd ≫ b.inr)).symm.trans
    ((congrArg Φ.map h).trans (Φ.map_id _))

variable {Φ} (τ : Φ ⟶ Φ)

/-- A natural endomorphism `τ` of `Φ` commutes with the first projection of the transported
bicone, where it acts on `X'` as `φ'`: if `τ.app X ≫ eX.hom = eX.hom ≫ φ'`, then
`τ.app b.pt ≫ fst = fst ≫ φ'`. -/
public theorem binaryBiconeMapIsos_fst_comm {φ' : X' ⟶ X'} (h : τ.app X ≫ eX.hom = eX.hom ≫ φ') :
    τ.app b.pt ≫ (binaryBiconeMapIsos Φ b eX eY).fst =
      (binaryBiconeMapIsos Φ b eX eY).fst ≫ φ' := by
  simp only [binaryBiconeMapIsos, ← τ.naturality_assoc, h, Category.assoc]

/-- A natural endomorphism `τ` of `Φ` commutes with the second projection of the transported
bicone, where it acts on `Y'` as `φ'`: if `τ.app Y ≫ eY.hom = eY.hom ≫ φ'`, then
`τ.app b.pt ≫ snd = snd ≫ φ'`. -/
public theorem binaryBiconeMapIsos_snd_comm {φ' : Y' ⟶ Y'} (h : τ.app Y ≫ eY.hom = eY.hom ≫ φ') :
    τ.app b.pt ≫ (binaryBiconeMapIsos Φ b eX eY).snd =
      (binaryBiconeMapIsos Φ b eX eY).snd ≫ φ' := by
  simp only [binaryBiconeMapIsos, ← τ.naturality_assoc, h, Category.assoc]

end Transport

/-- Placing an object in degree `q` is additive. -/
public instance additive_singlePlusFunctor {C : Type*} [Category* C] [Abelian C] (q : ℤ) :
    (Stacks.DerivedIndexing.singlePlusFunctor C q).Additive where
  map_add {X Y f g} := by
    apply ObjectProperty.hom_ext
    exact (HomologicalComplex.single C (ComplexShape.up ℤ) q).map_add

/-! ### `RΓ_c(X_k̄, -)` is additive -/

section Additive

attribute [local instance] Functor.commShiftRightDerivedFunctorPlus
  Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  Functor.isTriangulated_rightDerivedFunctorPlus

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {Y : Scheme.{u}}
  (f : Y ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar]

/-- **`RΓ_c(X_k̄, -)` is an additive functor**, a composite of additive functors. -/
public instance compactSupportFrobeniusFunctor_additive :
    (compactSupportFrobeniusFunctor.{u, r} Λ f j kbar).Additive := by
  have (Z : Scheme.{u}) : (DerivedCategory.Plus.Q (C := EtaleModules.{u, r} Λ Z)).Additive := by
    dsimp [DerivedCategory.Plus.Q]
    infer_instance
  have : (etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.Additive := by
    dsimp [Functor.mapCochainComplexPlus]
    infer_instance
  have : (etaleModuleInverseImage.{u, r} Λ
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.Additive := by
    dsimp [Functor.mapCochainComplexPlus]
    infer_instance
  dsimp only [compactSupportFrobeniusFunctor, fieldBaseChangeRestrictionFunctor]
  infer_instance

end Additive

/-! ### Two factors -/

section Reduction

/-- Two commuting squares of isomorphisms compose. -/
private theorem comm_trans {C : Type*} [Category* C] {A A' A'' : C} (a : A ≅ A') (b : A' ≅ A'')
    {φ : A ⟶ A} {φ' : A' ⟶ A'} {φ'' : A'' ⟶ A''} (ha : φ ≫ a.hom = a.hom ≫ φ')
    (hb : φ' ≫ b.hom = b.hom ≫ φ'') : φ ≫ (a ≪≫ b).hom = (a ≪≫ b).hom ≫ φ'' := by
  rw [Iso.trans_hom, reassoc_of% ha, hb, Category.assoc]

variable {Λ : Type} [CommRing Λ] {e : Λ} (he : IsIdempotentElem e)
  {k : Type u} [Field k] [Fintype k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- Restriction of scalars commutes with placing a sheaf in degree `0`. -/
public def singlePlusRestrictScalarsIso (G : EtaleModules.{u, 0} (Λ ⧸ Ideal.span {1 - e}) Y) :
    (Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ Y) 0).obj
        ((etaleModuleRestrictScalars (algebraMap Λ (Λ ⧸ Ideal.span {1 - e})) Y).obj G) ≅
      (etaleModuleRestrictScalars
        (algebraMap Λ (Λ ⧸ Ideal.span {1 - e})) Y).mapCochainComplexPlus.obj
        ((Stacks.DerivedIndexing.singlePlusFunctor
          (EtaleModules.{u, 0} (Λ ⧸ Ideal.span {1 - e}) Y) 0).obj G) :=
  ObjectProperty.isoMk _ ((HomologicalComplex.singleMapHomologicalComplex
    (etaleModuleRestrictScalars (algebraMap Λ (Λ ⧸ Ideal.span {1 - e})) Y)
      (ComplexShape.up ℤ) 0).app G).symm

/-- The summand `RΓ_c(X_k̄, (e F)|_Λ)` of `RΓ_c(X_k̄, F)` is `RΓ_c(X_k̄, e F)|_Λ`. -/
public def compactSupportRestrictScalarsSingleIso
    (G : EtaleModules.{u, 0} (Λ ⧸ Ideal.span {1 - e}) Y) :
    DerivedCategory.Plus.ι.obj ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).obj
        ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ Y) 0).obj
          ((etaleModuleRestrictScalars (algebraMap Λ (Λ ⧸ Ideal.span {1 - e})) Y).obj G))) ≅
      (ModuleCat.restrictScalars.{u + 1}
        (algebraMap Λ (Λ ⧸ Ideal.span {1 - e}))).mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj ((compactSupportFrobeniusFunctor.{u, 0} (Λ ⧸ Ideal.span {1 - e})
          f j kbar).obj ((Stacks.DerivedIndexing.singlePlusFunctor
            (EtaleModules.{u, 0} (Λ ⧸ Ideal.span {1 - e}) Y) 0).obj G))) :=
  DerivedCategory.Plus.ι.mapIso
    ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).mapIso
      (singlePlusRestrictScalarsIso (e := e) G) ≪≫
      (compactSupportFrobeniusCohomologyRestrictScalarsIso
        (algebraMap Λ (Λ ⧸ Ideal.span {1 - e})) f j kbar _).symm)

/-- **The comparison of the summands commutes with `π_X^*`.** -/
public theorem compactSupportRestrictScalarsSingleIso_comm
    (G : EtaleModules.{u, 0} (Λ ⧸ Ideal.span {1 - e}) Y) :
    DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q hcard
        ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ Y) 0).obj
          ((etaleModuleRestrictScalars (algebraMap Λ (Λ ⧸ Ideal.span {1 - e})) Y).obj G))) ≫
        (compactSupportRestrictScalarsSingleIso f j kbar G).hom =
      (compactSupportRestrictScalarsSingleIso f j kbar G).hom ≫
        (ModuleCat.restrictScalars.{u + 1}
          (algebraMap Λ (Λ ⧸ Ideal.span {1 - e}))).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0}
            (Λ ⧸ Ideal.span {1 - e}) f j kbar p q hcard
            ((Stacks.DerivedIndexing.singlePlusFunctor
              (EtaleModules.{u, 0} (Λ ⧸ Ideal.span {1 - e}) Y) 0).obj G))) := by
  let ρ := algebraMap Λ (Λ ⧸ Ideal.span {1 - e})
  let sG := singlePlusRestrictScalarsIso (e := e) G
  have ha := ((canonicalCompactSupportFrobeniusNatTrans.{u, 0} Λ f j kbar p q hcard).naturality
    sG.hom).symm
  have hb := restrictScalars_canonicalCompactSupportFrobenius ρ f j kbar p q hcard
    ((Stacks.DerivedIndexing.singlePlusFunctor
      (EtaleModules.{u, 0} (Λ ⧸ Ideal.span {1 - e}) Y) 0).obj G)
  have hb' : canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q hcard
        ((etaleModuleRestrictScalars ρ Y).mapCochainComplexPlus.obj
          ((Stacks.DerivedIndexing.singlePlusFunctor
            (EtaleModules.{u, 0} (Λ ⧸ Ideal.span {1 - e}) Y) 0).obj G)) ≫
        (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ f j kbar _).inv =
      (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ f j kbar _).inv ≫
        (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.map
          (canonicalCompactSupportFrobenius.{u, 0} (Λ ⧸ Ideal.span {1 - e}) f j kbar p q hcard
            ((Stacks.DerivedIndexing.singlePlusFunctor
              (EtaleModules.{u, 0} (Λ ⧸ Ideal.span {1 - e}) Y) 0).obj G)) := by
    rw [Iso.comp_inv_eq, Category.assoc, hb, Iso.inv_hom_id_assoc]
  have h' := congrArg DerivedCategory.Plus.ι.map <|
    comm_trans ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).mapIso sG)
      (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ f j kbar _).symm ha hb'
  simp only [Functor.map_comp] at h'
  exact h'

end Reduction

/-! ### The reduction along one idempotent -/

section Summand

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {Λ : Type} [CommRing Λ] {e : Λ}
  (he : IsIdempotentElem e)
  [HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ)] [HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ)]
  [HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {1 - e}))]
  [HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {1 - e}))]
  {k : Type u} [Field k] [Fintype k] (f : X.obj ⟶ Spec (.of k))
  (kbar : Type u) [Field kbar] [Algebra k kbar]
  (j : CompactificationOf (Over.mk f)) (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The summand of `RΓ_c(X_k̄, F)` cut out by `e`, compared with `RΓ_c(X_k̄, e F)`. -/
public def compactSupportSummandIso
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) :
    DerivedCategory.Plus.ι.obj ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).obj
        ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ X.obj) 0).obj
          ((IsIdempotentElem.sheafRestrictScalars.{u + 1} (e := e) X.obj.smallEtaleTopology).obj
            ((he.sheafBaseChange.{u + 1} X.obj.smallEtaleTopology).obj
              ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).functor.obj F))))) ≅
      (ModuleCat.restrictScalars.{u + 1}
        (algebraMap Λ (Λ ⧸ Ideal.span {1 - e}))).mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj ((compactSupportFrobeniusFunctor.{u, 0}
          (Λ ⧸ Ideal.span {1 - e}) f j kbar).obj
          ((Stacks.DerivedIndexing.singlePlusFunctor
            (EtaleModules.{u, 0} (Λ ⧸ Ideal.span {1 - e}) X.obj) 0).obj
            ((SmallEtale.sheafEquiv B X.obj X.property
              (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {1 - e}))).functor.obj
              ((he.sheafBaseChange.{u + 1} (SmallEtale.topology B X.obj X.property)).obj F))))) :=
  compactSupportRestrictScalarsSingleIso f j kbar _ ≪≫
    (ModuleCat.restrictScalars.{u + 1}
      (algebraMap Λ (Λ ⧸ Ideal.span {1 - e}))).mapDerivedCategory.mapIso
      (DerivedCategory.Plus.ι.mapIso ((compactSupportFrobeniusFunctor.{u, 0}
        (Λ ⧸ Ideal.span {1 - e}) f j kbar).mapIso
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).mapIso
            ((sheafEquivSheafBaseChangeIso B X he).app F))))

omit [HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ)]
  [HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {1 - e}))] in
/-- **The comparison of the summand with `RΓ_c(X_k̄, e F)` commutes with `π_X^*`.** -/
public theorem compactSupportSummandIso_comm
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) :
    DerivedCategory.Plus.ι.map ((canonicalCompactSupportFrobeniusNatTrans.{u, 0} Λ f j kbar p q
        hcard).app ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ X.obj) 0).obj
          ((IsIdempotentElem.sheafRestrictScalars.{u + 1} (e := e) X.obj.smallEtaleTopology).obj
            ((he.sheafBaseChange.{u + 1} X.obj.smallEtaleTopology).obj
              ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).functor.obj F))))) ≫
        (compactSupportSummandIso B X he f kbar j F).hom =
      (compactSupportSummandIso B X he f kbar j F).hom ≫
        (ModuleCat.restrictScalars.{u + 1}
          (algebraMap Λ (Λ ⧸ Ideal.span {1 - e}))).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map ((canonicalCompactSupportFrobeniusNatTrans.{u, 0}
            (Λ ⧸ Ideal.span {1 - e}) f j kbar p q hcard).app
            ((Stacks.DerivedIndexing.singlePlusFunctor
              (EtaleModules.{u, 0} (Λ ⧸ Ideal.span {1 - e}) X.obj) 0).obj
              ((SmallEtale.sheafEquiv B X.obj X.property
                (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {1 - e}))).functor.obj
                ((he.sheafBaseChange.{u + 1} (SmallEtale.topology B X.obj X.property)).obj
                  F))))) := by
  refine comm_trans _ _ (compactSupportRestrictScalarsSingleIso_comm f j kbar p q hcard _) ?_
  have hn := (canonicalCompactSupportFrobeniusNatTrans.{u, 0} (Λ ⧸ Ideal.span {1 - e}) f j kbar p q
    hcard).naturality ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
      ((sheafEquivSheafBaseChangeIso B X he).hom.app F))
  have h := congrArg (fun g => (ModuleCat.restrictScalars.{u + 1}
    (algebraMap Λ (Λ ⧸ Ideal.span {1 - e}))).mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map g)) hn
  simp only [Functor.map_comp] at h
  exact h.symm

end Summand

section TwoFactors

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {Λ : Type} [CommRing Λ] [Finite Λ] {e : Λ}
  (he : IsIdempotentElem e)
  [HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ)] [HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ)]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} Λ) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} Λ)]
  [HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {1 - e}))]
  [HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {1 - e}))]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {1 - e})) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {1 - e}))]
  [HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {1 - (1 - e)}))]
  [HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {1 - (1 - e)}))]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {1 - (1 - e)})) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {1 - (1 - e)}))]
  {k : Type u} [Field k] [Fintype k] (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] (kbar : Type u) [Field kbar] [Algebra k kbar]
  (j : CompactificationOf (Over.mk f)) (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

omit [Finite Λ] in
/-- **The identity of Tag 03UZ for `e F` and `(1 - e) F` implies it for `F`.** Here `e F` is a
sheaf of modules over `Λ ⧸ (1 - e)` and `(1 - e) F` one over `Λ ⧸ (e)`. -/
public theorem lFunctionCharSeriesIdentity_of_isIdempotentElem
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleFlatModuleSheaf B X Λ F)
    (h₁ : LFunctionCharSeriesIdentity B X (Λ ⧸ Ideal.span {1 - e}) f kbar
      ((he.sheafBaseChange.{u + 1} (SmallEtale.topology B X.obj X.property)).obj F)
      (isConstructibleFlatModuleSheaf_sheafBaseChange B X he hF) j p q hcard)
    (h₂ : LFunctionCharSeriesIdentity B X (Λ ⧸ Ideal.span {1 - (1 - e)}) f kbar
      ((he.one_sub.sheafBaseChange.{u + 1} (SmallEtale.topology B X.obj X.property)).obj F)
      (isConstructibleFlatModuleSheaf_sheafBaseChange B X he.one_sub hF) j p q hcard) :
    LFunctionCharSeriesIdentity B X Λ f kbar F hF j p q hcard := by
  obtain ⟨hp₁, hL₁⟩ := h₁
  obtain ⟨hp₂, hL₂⟩ := h₂
  have := he.projective_quotient
  have := he.one_sub.projective_quotient
  let F' := (SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).functor.obj F
  let bS := he.sheafBinaryBicone.{u + 1} X.obj.smallEtaleTopology F'
  let Φ := Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ X.obj) 0 ⋙
    compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙ DerivedCategory.Plus.ι
  let τ : Φ ⟶ Φ := Functor.whiskerLeft _ (Functor.whiskerRight
    (canonicalCompactSupportFrobeniusNatTrans.{u, 0} Λ f j kbar p q hcard) DerivedCategory.Plus.ι)
  let b := binaryBiconeMapIsos Φ bS (compactSupportSummandIso B X he f kbar j F)
    (compactSupportSummandIso B X he.one_sub f kbar j F)
  have htotal := binaryBiconeMapIsos_total Φ bS (compactSupportSummandIso B X he f kbar j F)
    (compactSupportSummandIso B X he.one_sub f kbar j F) (he.sheafBinaryBicone_total _ F')
  have hc₁ : τ.app ((IsIdempotentElem.sheafRestrictScalars.{u + 1} (e := e)
      X.obj.smallEtaleTopology).obj
        ((he.sheafBaseChange.{u + 1} X.obj.smallEtaleTopology).obj F')) ≫
        (compactSupportSummandIso B X he f kbar j F).hom =
      (compactSupportSummandIso B X he f kbar j F).hom ≫ _ :=
    compactSupportSummandIso_comm B X he f kbar j p q hcard F
  have hc₂ : τ.app ((IsIdempotentElem.sheafRestrictScalars.{u + 1} (e := 1 - e)
      X.obj.smallEtaleTopology).obj
        ((he.one_sub.sheafBaseChange.{u + 1} X.obj.smallEtaleTopology).obj F')) ≫
        (compactSupportSummandIso B X he.one_sub f kbar j F).hom =
      (compactSupportSummandIso B X he.one_sub f kbar j F).hom ≫ _ :=
    compactSupportSummandIso_comm B X he.one_sub f kbar j p q hcard F
  have hφ₁ := binaryBiconeMapIsos_fst_comm bS (compactSupportSummandIso B X he f kbar j F)
    (compactSupportSummandIso B X he.one_sub f kbar j F) τ hc₁
  have hφ₂ := binaryBiconeMapIsos_snd_comm bS (compactSupportSummandIso B X he f kbar j F)
    (compactSupportSummandIso B X he.one_sub f kbar j F) τ hc₂
  let φ : b.pt ⟶ b.pt := τ.app F'
  obtain ⟨hK, hm₁, hm₂⟩ :=
    CategoryTheory.FilteredDerived.exists_isPerfect_map_perfectDerivedCharSeries_of_binaryBicone
      Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk_span_one_sub_self e)
      (by rw [Ideal.Quotient.algebraMap_eq, sub_sub_cancel]
          exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self e))
      _ hp₁ _ _ hp₂ _ b htotal φ hφ₁ hφ₂
  have k₁ := congrArg (fun x => (x⁻¹).val) hm₁
  have k₂ := congrArg (fun x => (x⁻¹).val) hm₂
  simp only [← map_inv, Units.coe_map] at k₁ k₂
  refine ⟨hK, he.powerSeries_ext ?_ ?_⟩
  · rw [map_constructibleFlatLFunction_sheafBaseChange B X he f F hF, hL₁]
    exact k₁.symm
  · rw [map_constructibleFlatLFunction_sheafBaseChange B X he.one_sub f F hF, hL₂]
    exact k₂.symm

end TwoFactors

/-! ### Reduction to local coefficient rings -/

section Local

variable (B : BigEtaleSite.{u}) (X : B.Scheme)
  {k : Type u} [Field k] [Fintype k] (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] (kbar : Type u) [Field kbar] [Algebra k kbar]
  (j : CompactificationOf (Over.mk f)) (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- Over the zero ring every object of the derived category is perfect. -/
private theorem isPerfect_of_subsingleton {R : Type u} [CommRing R] [Subsingleton R]
    (K : DerivedCategory (ModuleCat.{v} R)) : StacksDraft.Perfect.IsPerfect K := by
  have hz : ∀ M : ModuleCat.{v} R, IsZero M := fun M =>
    have : Subsingleton M := Module.subsingleton R M
    ModuleCat.isZero_of_subsingleton M
  have hc : ∀ C : CochainComplex (ModuleCat.{v} R) ℤ, IsZero C := fun C =>
    (IsZero.iff_id_eq_zero _).2 (HomologicalComplex.hom_ext _ _ fun n => (hz _).eq_of_src _ _)
  have hK : IsZero K := (DerivedCategory.Q.map_isZero
    (hc (DerivedCategory.Q.objPreimage K))).of_iso (DerivedCategory.Q.objObjPreimageIso K).symm
  let Z : CochainComplex (ModuleCat.{v} R) ℤ := 0
  have (n : ℤ) : Subsingleton (Z.X n) := Module.subsingleton R _
  refine ⟨Z, 0, 0, ?_, ?_, fun n => inferInstance, fun n => inferInstance,
    ⟨hK.iso (DerivedCategory.Q.map_isZero (hc Z))⟩⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun i _ => hz _
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun i _ => hz _

/-- The cardinality of a quotient divides that of the ring. -/
private theorem card_quotient_dvd {R : Type} [CommRing R] [Finite R] (I : Ideal R) :
    Nat.card (R ⧸ I) ∣ Nat.card R :=
  ⟨Nat.card I, by rw [Submodule.card_eq_card_quotient_mul_card I, mul_comm]⟩

/-- A quotient by a nonzero ideal is strictly smaller. -/
private theorem card_quotient_lt {R : Type} [CommRing R] [Finite R] {I : Ideal R} (hI : I ≠ ⊥) :
    Nat.card (R ⧸ I) < Nat.card R := by
  have : Finite (R ⧸ I) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  rw [Submodule.card_eq_card_quotient_mul_card I]
  have h1 : 0 < Nat.card (R ⧸ I) := Nat.card_pos
  have h2 : 1 < Nat.card I := by
    rw [Finite.one_lt_card_iff_nontrivial]
    exact Submodule.nontrivial_iff_ne_bot.2 hI
  nlinarith

/-- **Reduction of Tag 03UZ to local coefficient rings.** If the identity
`L(X, F) = det(1 - π_X^* T | RΓ_c(X_k̄, F))⁻¹` holds for every finite local coefficient ring of
order invertible in `k` and every constructible flat sheaf over it, it holds for every finite
commutative coefficient ring of order invertible in `k`. A finite commutative ring which is not
local splits along an idempotent into two rings of smaller cardinality, and
`Stacks.EtaleCohomology.lFunctionCharSeriesIdentity_of_isIdempotentElem` assembles the identity
from the two factors. -/
public theorem lFunctionCharSeriesIdentity_of_isLocalRing
    (hloc : ∀ (Λ' : Type) [CommRing Λ'] [Finite Λ'] [IsLocalRing Λ']
      [HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ')]
      [HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ')]
      [∀ (S T : B.Scheme) (g : T ⟶ S),
        ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
          (ModuleCat.{u + 1} Λ') (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
      [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
        HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} Λ')],
      ((Nat.card Λ' : ℕ) : k) ≠ 0 →
      ∀ (F' : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ'))
        (hF' : IsConstructibleFlatModuleSheaf B X Λ' F'),
        LFunctionCharSeriesIdentity B X Λ' f kbar F' hF' j p q hcard)
    (Λ : Type) [CommRing Λ] [Finite Λ]
    [HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ)] [HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ)]
    [∀ (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} Λ) (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} Λ)]
    (hΛ : ((Nat.card Λ : ℕ) : k) ≠ 0)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) :
    LFunctionCharSeriesIdentity B X Λ f kbar F hF j p q hcard := by
  induction h : Nat.card Λ using Nat.strong_induction_on generalizing Λ with
  | _ n ih =>
  by_cases hsub : Subsingleton Λ
  · exact ⟨isPerfect_of_subsingleton _, Subsingleton.elim _ _⟩
  have : Nontrivial Λ := not_subsingleton_iff_nontrivial.1 hsub
  by_cases hlocal : IsLocalRing Λ
  · exact hloc Λ hΛ F hF
  have : IsArtinianRing Λ := isArtinian_of_finite
  obtain ⟨e, he, he0, he1⟩ := exists_isIdempotentElem_ne_zero_ne_one Λ hlocal
  have hdvd : ∀ I : Ideal Λ, ((Nat.card (Λ ⧸ I) : ℕ) : k) ≠ 0 := fun I hI => by
    obtain ⟨c, hc⟩ := card_quotient_dvd I
    exact hΛ (by rw [hc, Nat.cast_mul, hI, zero_mul])
  have (e : Λ) : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {1 - e})) :=
    ModuleCat.hasLimitsOfSize.{u, u, u + 1}
  have := fun (e : Λ) (S T : B.Scheme) (g : T ⟶ S) =>
    SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat.{0, 0, u} B
      (Λ ⧸ Ideal.span {1 - e}) S T g
  have := fun (e : Λ) (T : B.Scheme) (V : SmallEtale B T.obj T.property) =>
    SmallEtale.hasWeakSheafify_over_moduleCat.{0, 0, u} B (Λ ⧸ Ideal.span {1 - e}) T V
  have key : ∀ {e : Λ} (he : IsIdempotentElem e), 1 - e ≠ 0 →
      LFunctionCharSeriesIdentity B X (Λ ⧸ Ideal.span {1 - e}) f kbar
        ((he.sheafBaseChange.{u + 1} (SmallEtale.topology B X.obj X.property)).obj F)
        (isConstructibleFlatModuleSheaf_sheafBaseChange B X he hF) j p q hcard := by
    intro e he h1
    have : Finite (Λ ⧸ Ideal.span {1 - e}) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    exact ih _ (h ▸ card_quotient_lt (by rwa [Ne, Ideal.span_singleton_eq_bot]))
      (Λ ⧸ Ideal.span {1 - e}) (hdvd _)
      ((he.sheafBaseChange.{u + 1} (SmallEtale.topology B X.obj X.property)).obj F)
      (isConstructibleFlatModuleSheaf_sheafBaseChange B X he hF) rfl
  have h₁ := key he (sub_ne_zero.2 he1.symm)
  have h₂ := key he.one_sub (by rwa [sub_sub_cancel])
  exact lFunctionCharSeriesIdentity_of_isIdempotentElem B X he f kbar j p q hcard F hF h₁ h₂

end Local

end Stacks.EtaleCohomology

end
