module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFieldExtension

/-!
# `Hⁱ_c` of an ℓ-adic sheaf after a finite extension of the base field

Let `X` be a separated scheme of finite type over a finite field `k` with `q = p ^ f` elements,
compactified by `j : X ⟶ X̄`, let `F` be an ℓ-adic sheaf on `X`, `k'` a finite extension of `k`
and `k̄` an extension of `k'`.  Write `X' = X ×_k k'`, a scheme over `k'` compactified by the base
change of `j`, and `g : X' ⟶ X` for the projection.  Then

`Hⁱ_c(X'_{k̄}, g⁻¹F) ≅ Hⁱ_c(X_{k̄}, F)`

as `ℤ_ℓ`-modules, and after `⊗ ℚ_ℓ`; if `k'` has `q ^ m` elements, the isomorphism carries the
Frobenius `π_{X'}^*` of `X'` over `k'` to `(π_X^*) ^ m`, so the two have the same trace.  This is
the reduction, in the proof of [Stacks, Tag 03V0], of the trace of `(π_X^*) ^ m` to the trace of
the Frobenius of `X ×_k k_m` over `k_m` in Tag 03V2.

The isomorphism is assembled level by level from the identification of the levels of `g⁻¹F`
(`Stacks.EtaleCohomology.padicLevelInverseImageIso`) and the identification of the compactly
supported cohomology (`Stacks.EtaleCohomology.compactSupportFieldExtensionIso`); both are
compatible with the transition maps.

## Main definitions

* `fieldExtensionScheme`: `X ×_k k'` as an object of the big étale site.
* `LAdicSheaf.fieldExtensionCohomologyIso`: `Hⁱ_c(X_{k̄}, F) ≅ Hⁱ_c(X'_{k̄}, g⁻¹F)`.

## Main results

* `LAdicSheaf.trace_rationalGeometricCompactlySupportedFrobenius_fieldExtension`:
  `Tr(π_{X'}^* | Hⁱ_c(X'_{k̄}, g⁻¹F)) = Tr((π_X^*) ^ m | Hⁱ_c(X_{k̄}, F))`.

## References

* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-! ### The base change as an object of the big étale site -/

section Scheme

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  (k' : Type u) [Field k'] [Algebra k k'] [Module.Finite k k']

/-- For a finite extension `k'` of `k`, the morphism `Spec k' ⟶ Spec k` is locally of finite
type. -/
instance : LocallyOfFiniteType (specAlgebraMap k k') :=
  HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)

/-- **`X ×_k k'` as an object of the big étale site**, for a finite extension `k'` of `k`. -/
abbrev fieldExtensionScheme : B.Scheme :=
  ⟨pullback f (specAlgebraMap k k'),
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (pullback.fst f (specAlgebraMap k k'))
      X.property⟩

/-- The projection `X ×_k k' ⟶ X` in the big étale site. -/
abbrev fieldExtensionProj : fieldExtensionScheme B X f k' ⟶ X :=
  ObjectProperty.homMk (pullback.fst f (specAlgebraMap k k'))

end Scheme

/-! ### The levels -/

section Levels

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) (k' : Type u) [Field k'] [Algebra k k']
  [Module.Finite k k'] [IsNoetherian X.1] [IsNoetherian (fieldExtensionScheme B X f k').1]

/-- Two commutative squares paste to a commutative rectangle. -/
private lemma square_paste {D : Type*} [Category* D] {P Q P' Q' R S : D} {a : P ⟶ Q}
    {s₁ : P ⟶ P'} {s₂ : Q ⟶ Q'} {b : P' ⟶ Q'} {x₁ : P' ⟶ R} {x₂ : Q' ⟶ S} {d : R ⟶ S}
    (hn : a ≫ s₂ = s₁ ≫ b) (h : b ≫ x₂ = x₁ ≫ d) : a ≫ s₂ ≫ x₂ = (s₁ ≫ x₁) ≫ d := by
  rw [reassoc_of% hn, h, Category.assoc]

/-- A functor carries a commutative square to a commutative square. -/
private lemma map_comp_eq_of_comp_eq {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {P Q P' Q' : C} {a : P ⟶ Q} {b : Q ⟶ Q'} {c : P ⟶ P'} {d : P' ⟶ Q'} (h : a ≫ b = c ≫ d) :
    G.map a ≫ G.map b = G.map c ≫ G.map d := by
  rw [← G.map_comp, ← G.map_comp, h]

/-- **The level `(g⁻¹F)ₙ` on `X ×_k k'`, as a complex in degree zero, is the inverse image of the
level `Fₙ`.** -/
def padicComplexFieldExtensionIso (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
        (pullback.fst f (specAlgebraMap k k'))).mapCochainComplexPlus.obj
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n)) ≅
      (padicCoefficientComplex B (fieldExtensionScheme B X f k') ℓ).obj
        (LAdicSheaf.padicLevel B (fieldExtensionScheme B X f k') ℓ
          (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) n) :=
  ObjectProperty.isoMk _
    ((HomologicalComplex.singleMapHomologicalComplex (etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
        (pullback.fst f (specAlgebraMap k k'))) (ComplexShape.up ℤ) 0).app _ ≪≫
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
        (padicLevelInverseImageIso B (fieldExtensionProj B X f k') ℓ n (F.level n)))

/-- The identification of the levels is compatible with the transition maps. -/
lemma padicComplexFieldExtensionIso_transition (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
        (pullback.fst f (specAlgebraMap k k'))).mapCochainComplexPlus.map
        ((padicCoefficientComplex B X ℓ).map (LAdicSheaf.padicTransition B X ℓ F n)) ≫
      (padicComplexFieldExtensionIso B X ℓ f k' F n).hom =
    (padicComplexFieldExtensionIso B X ℓ f k' F (n + 1)).hom ≫
      (padicCoefficientComplex B (fieldExtensionScheme B X f k') ℓ).map
        (LAdicSheaf.padicTransition B (fieldExtensionScheme B X f k') ℓ
          (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) n) := by
  have h := padicLevelInverseImageIso_transition B (fieldExtensionProj B X f k') ℓ F n
  have hn := (HomologicalComplex.singleMapHomologicalComplex (etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
    (pullback.fst f (specAlgebraMap k k'))) (ComplexShape.up ℤ) 0).hom.naturality
      ((padicSheafEquiv B ℓ X).map (LAdicSheaf.padicTransition B X ℓ F n))
  dsimp only [Functor.comp_map] at hn
  have h' := ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map_comp _ _).symm.trans
    ((congrArg (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map h).trans
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map_comp _ _))
  ext1
  exact square_paste hn h'

end Levels

/-! ### The cohomology -/

section Cohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
  (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] [Module.Finite k k']
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra k' kbar] [IsScalarTower k k' kbar]
  [IsNoetherian X.1] [IsNoetherian (fieldExtensionScheme B X f k').1]
  (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ)

/-- **`Hⁱ_c(X_{k̄}, Fₙ) ≅ Hⁱ_c(X'_{k̄}, (g⁻¹F)ₙ)`** at a finite level. -/
def geometricCompactSupportFieldExtensionIso (n : ℕ) :
    (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
        (LAdicSheaf.padicLevel B X ℓ F n) ≅
      (geometricCompactSupportPadicCohomology B (fieldExtensionScheme B X f k') ℓ
          (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar
          i).obj
        (LAdicSheaf.padicLevel B (fieldExtensionScheme B X f k') ℓ
          (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) n) :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i).mapIso
    ((compactSupportFieldExtensionIso ℤ_[ℓ] f j k' kbar
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n))).symm ≪≫
      (compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] (pullback.snd f (specAlgebraMap k k'))
        (compactificationFieldBaseChange f j k') kbar).mapIso
        (padicComplexFieldExtensionIso B X ℓ f k' F n))

omit [Fintype k] [Fintype k'] in
/-- The finite-level identification is compatible with the maps of the inverse systems. -/
lemma geometricCompactSupportFieldExtensionIso_transition [Finite k] (n : ℕ) :
    (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).map
        (LAdicSheaf.padicTransition B X ℓ F n) ≫
      (geometricCompactSupportFieldExtensionIso B X ℓ f j k' kbar F i n).hom =
    (geometricCompactSupportFieldExtensionIso B X ℓ f j k' kbar F i (n + 1)).hom ≫
      (geometricCompactSupportPadicCohomology B (fieldExtensionScheme B X f k') ℓ
          (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar
          i).map
        (LAdicSheaf.padicTransition B (fieldExtensionScheme B X f k') ℓ
          (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) n) := by
  have := Fintype.ofFinite k
  have hE := compactSupportFieldExtensionIso_hom_naturality ℤ_[ℓ] f j k' kbar
    ((padicCoefficientComplex B X ℓ).map (LAdicSheaf.padicTransition B X ℓ F n))
  have hE' : (compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar).map
        ((padicCoefficientComplex B X ℓ).map (LAdicSheaf.padicTransition B X ℓ F n)) ≫
      (compactSupportFieldExtensionIso ℤ_[ℓ] f j k' kbar
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n))).inv =
      (compactSupportFieldExtensionIso ℤ_[ℓ] f j k' kbar
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F (n + 1)))).inv ≫
        (compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] (pullback.snd f (specAlgebraMap k k'))
          (compactificationFieldBaseChange f j k') kbar).map
          ((etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
            (pullback.fst f (specAlgebraMap k k'))).mapCochainComplexPlus.map
            ((padicCoefficientComplex B X ℓ).map (LAdicSheaf.padicTransition B X ℓ F n))) := by
    rw [Iso.comp_inv_eq, Category.assoc, hE, Iso.inv_hom_id_assoc]
  have hl := congrArg (compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ]
    (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar).map
    (padicComplexFieldExtensionIso_transition B X ℓ f k' F n)
  rw [Functor.map_comp, Functor.map_comp] at hl
  have h := square_paste hE' hl
  exact map_comp_eq_of_comp_eq (DerivedCategory.Plus.homologyFunctor _ i) h


/-- The finite-level identifications, as an isomorphism of inverse systems
`(n ↦ Hⁱ_c(X_{k̄}, Fₙ)) ≅ (n ↦ Hⁱ_c(X'_{k̄}, (g⁻¹F)ₙ))`. -/
def geometricCompactlySupportedCohomologySystemFieldExtensionIso :
    LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i ≅
      LAdicSheaf.geometricCompactlySupportedCohomologySystem B (fieldExtensionScheme B X f k') ℓ
        (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar
        (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i :=
  NatIso.ofComponents
    (fun n => geometricCompactSupportFieldExtensionIso B X ℓ f j k' kbar F i n.unop)
    (fun φ => (NatTrans.ofOpSequence
      (F := LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i)
      (G := LAdicSheaf.geometricCompactlySupportedCohomologySystem B
        (fieldExtensionScheme B X f k') ℓ
        (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar
        (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i)
      (fun n => (geometricCompactSupportFieldExtensionIso B X ℓ f j k' kbar F i n).hom)
      (fun n => (congrArg
          (· ≫ (geometricCompactSupportFieldExtensionIso B X ℓ f j k' kbar F i n).hom)
          (LAdicSheaf.geometricCompactlySupportedCohomologySystem_map_succ B X ℓ f j kbar F i
            n)).trans
        ((geometricCompactSupportFieldExtensionIso_transition B X ℓ f j k' kbar F i n).trans
          (congrArg
            ((geometricCompactSupportFieldExtensionIso B X ℓ f j k' kbar F i (n + 1)).hom ≫ ·)
            (LAdicSheaf.geometricCompactlySupportedCohomologySystem_map_succ B
              (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
              (compactificationFieldBaseChange f j k') kbar
              (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i n).symm)))).naturality φ)

/-- **`Hⁱ_c(X_{k̄}, F) ≅ Hⁱ_c(X'_{k̄}, g⁻¹F)`** for `X' = X ×_k k'` and the projection
`g : X' ⟶ X`: the limit of the finite-level identifications. -/
def LAdicSheaf.fieldExtensionCohomologyIso :
    LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i ≅
      LAdicSheaf.geometricCompactlySupportedCohomology B (fieldExtensionScheme B X f k') ℓ
        (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar
        (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i :=
  HasLimit.isoOfNatIso
    (geometricCompactlySupportedCohomologySystemFieldExtensionIso B X ℓ f j k' kbar F i)

/-- The limit identification lies over the finite-level ones. -/
lemma LAdicSheaf.fieldExtensionCohomologyIso_hom_π (n : ℕ) :
    (LAdicSheaf.fieldExtensionCohomologyIso B X ℓ f j k' kbar F i).hom ≫
        LAdicSheaf.geometricCompactlySupportedCohomologyπ B (fieldExtensionScheme B X f k') ℓ
          (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar
          (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i n =
      LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f j kbar F i n ≫
        (geometricCompactSupportFieldExtensionIso B X ℓ f j k' kbar F i n).hom :=
  HasLimit.isoOfNatIso_hom_π
    (geometricCompactlySupportedCohomologySystemFieldExtensionIso B X ℓ f j k' kbar F i)
    (Opposite.op n)

/-- **The `ℚ_ℓ`-version**, `Hⁱ_c(X_{k̄}, F ⊗ ℚ_ℓ) ≅ Hⁱ_c(X'_{k̄}, g⁻¹F ⊗ ℚ_ℓ)`. -/
def LAdicSheaf.rationalFieldExtensionCohomologyIso :
    LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i ≅
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B (fieldExtensionScheme B X f k') ℓ
        (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar
        (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i :=
  (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).mapIso
    (LAdicSheaf.fieldExtensionCohomologyIso B X ℓ f j k' kbar F i)

section Frobenius

variable (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP k' p]
  (hcard : Fintype.card k = p ^ q) (m : ℕ) (hcard' : Fintype.card k' = p ^ (q * (m + 1)))

/-- If `e` intertwines `x` with `y`, then `e.inv` intertwines `y` with `x`. -/
private lemma conj_symm {D : Type*} [Category* D] {A₀ B₀ : D} (e : A₀ ≅ B₀) (x : A₀ ⟶ A₀)
    (y : B₀ ⟶ B₀) (h : x ≫ e.hom = e.hom ≫ y) : y ≫ e.inv = e.inv ≫ x := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- A functor carries the powers of an endomorphism to the powers of its image. -/
lemma map_end_pow {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D) {Y : C} (a : Y ⟶ Y)
    (e : ℕ) : G.map ((End.of a) ^ e) = (End.of (G.map a)) ^ e :=
  (G.mapEnd Y).map_pow (End.of a) e

/-- **At a finite level, the identification carries `(π_X^*) ^ (m + 1)` to `π_{X'}^*`.** -/
lemma geometricCompactSupportFieldExtensionIso_comm (n : ℕ) :
    ((End.of ((geometricCompactSupportPadicCohomologyPullback B X ℓ f j kbar i
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard)).app
          (LAdicSheaf.padicLevel B X ℓ F n))) ^ (m + 1)) ≫
      (geometricCompactSupportFieldExtensionIso B X ℓ f j k' kbar F i n).hom =
    (geometricCompactSupportFieldExtensionIso B X ℓ f j k' kbar F i n).hom ≫
      (geometricCompactSupportPadicCohomologyPullback B (fieldExtensionScheme B X f k') ℓ
          (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar i
          (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ]
            (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar p
            (q * (m + 1)) hcard')).app
        (LAdicSheaf.padicLevel B (fieldExtensionScheme B X f k') ℓ
          (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) n) := by
  have hc := compactSupportFieldExtensionIso_comm ℤ_[ℓ] f j k' kbar p q hcard m hcard'
    ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n))
  have hc' := conj_symm _ _ _ hc
  have hN := (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ]
    (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar p
    (q * (m + 1)) hcard').naturality (padicComplexFieldExtensionIso B X ℓ f k' F n).hom
  have h := square_paste hc' hN.symm
  show ((End.of ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i).map
      (canonicalCompactSupportFrobenius.{u, 0} ℤ_[ℓ] f j kbar p q hcard
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n))))) ^ (m + 1)) ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i).map _ = _
  rw [← map_end_pow]
  exact map_comp_eq_of_comp_eq (DerivedCategory.Plus.homologyFunctor _ i) h


/-- The square on the limits from the squares at the finite levels. -/
private lemma limit_square {D : Type*} [Category* D] {L L' M M' : D} {Φ : L ⟶ L'} {πm : L' ⟶ M'}
    {πX : L ⟶ M} {β : M ⟶ M'} {P : L ⟶ L} {Pn : M ⟶ M} {cm : M' ⟶ M'} {Fr : L' ⟶ L'}
    (h₁ : Φ ≫ πm = πX ≫ β) (h₂ : P ≫ πX = πX ≫ Pn) (h₃ : Pn ≫ β = β ≫ cm)
    (h₄ : Fr ≫ πm = πm ≫ cm) : (P ≫ Φ) ≫ πm = (Φ ≫ Fr) ≫ πm := by
  rw [Category.assoc, h₁, reassoc_of% h₂, h₃, Category.assoc, h₄, reassoc_of% h₁]

/-- The `(m + 1)`-st power of `π_X^*` on the limit lies over the `(m + 1)`-st powers at the finite
levels. -/
lemma geometricCompactlySupportedFrobenius_pow_π (e n : ℕ) :
    ((End.of (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i)) ^ e) ≫
        LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f j kbar F i n =
      LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f j kbar F i n ≫
        ((End.of ((geometricCompactSupportPadicCohomologyPullback B X ℓ f j kbar i
          (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard)).app
            (LAdicSheaf.padicLevel B X ℓ F n))) ^ e) := by
  induction e with
  | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
  | succ e ih =>
      rw [pow_succ, pow_succ, End.mul_def, End.mul_def, Category.assoc, ih, ← Category.assoc,
        ← Category.assoc]
      congr 1
      exact LAdicSheaf.geometricCompactlySupportedCohomologyPullback_π B X ℓ f j kbar F i _ n

/-- **On `Hⁱ_c`, the identification carries `(π_X^*) ^ (m + 1)` to `π_{X'}^*`.** -/
theorem LAdicSheaf.fieldExtensionCohomologyIso_comm :
    ((End.of (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i)) ^
        (m + 1)) ≫ (LAdicSheaf.fieldExtensionCohomologyIso B X ℓ f j k' kbar F i).hom =
      (LAdicSheaf.fieldExtensionCohomologyIso B X ℓ f j k' kbar F i).hom ≫
        LAdicSheaf.geometricCompactlySupportedFrobenius B (fieldExtensionScheme B X f k') ℓ
          (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar p
          (q * (m + 1)) hcard' (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i := by
  refine limit.hom_ext fun n => ?_
  show _ ≫ LAdicSheaf.geometricCompactlySupportedCohomologyπ B (fieldExtensionScheme B X f k') ℓ
      (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar
      (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i n.unop = _ ≫
    LAdicSheaf.geometricCompactlySupportedCohomologyπ B (fieldExtensionScheme B X f k') ℓ
      (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar
      (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i n.unop
  exact limit_square (LAdicSheaf.fieldExtensionCohomologyIso_hom_π B X ℓ f j k' kbar F i n.unop)
    (geometricCompactlySupportedFrobenius_pow_π B X ℓ f j kbar F i p q hcard (m + 1) n.unop)
    (geometricCompactSupportFieldExtensionIso_comm B X ℓ f j k' kbar F i p q hcard m hcard' n.unop)
    (LAdicSheaf.geometricCompactlySupportedCohomologyPullback_π B (fieldExtensionScheme B X f k') ℓ
      (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar
      (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i _ n.unop)

/-- **The trace of `π_{X'}^*` on `Hⁱ_c(X'_{k̄}, g⁻¹F ⊗ ℚ_ℓ)` is the trace of `(π_X^*) ^ (m + 1)`
on `Hⁱ_c(X_{k̄}, F ⊗ ℚ_ℓ)`**, for `X' = X ×_k k'` over a field `k'` with `q ^ (m + 1)` elements. -/
theorem LAdicSheaf.trace_rationalGeometricCompactlySupportedFrobenius_fieldExtension :
    LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B (fieldExtensionScheme B X f k') ℓ
          (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar p
          (q * (m + 1)) hcard' (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i).hom =
      LinearMap.trace ℚ_[ℓ] _
        ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
          i).hom ^ (m + 1)) := by
  have h := congrArg (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
    (LAdicSheaf.fieldExtensionCohomologyIso_comm B X ℓ f j k' kbar F i p q hcard m hcard')
  rw [Functor.map_comp, Functor.map_comp, map_end_pow] at h
  have hl := congrArg ModuleCat.Hom.hom h
  simp only [ModuleCat.hom_comp] at hl
  have hp : ((End.of (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q
      hcard F i)) ^ (m + 1)).hom =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i).hom ^
        (m + 1) := by
    have h₀ := map_pow (ModuleCat.endRingEquiv
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i))
      (End.of
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i))
      (m + 1)
    simp only [ModuleCat.endRingEquiv_apply] at h₀
    exact h₀
  rw [← LinearMap.trace_conj' _
    (LAdicSheaf.rationalFieldExtensionCohomologyIso B X ℓ f j k' kbar F i).toLinearEquiv, ← hp]
  congr 1
  refine LinearMap.ext fun v => ?_
  have hv := LinearMap.congr_fun hl
    ((LAdicSheaf.rationalFieldExtensionCohomologyIso B X ℓ f j k' kbar F i).inv.hom v)
  simp only [LinearMap.coe_comp] at hv
  rw [LinearEquiv.conj_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  have hi : (LAdicSheaf.rationalFieldExtensionCohomologyIso B X ℓ f j k' kbar F i).hom.hom
      ((LAdicSheaf.rationalFieldExtensionCohomologyIso B X ℓ f j k' kbar F i).inv.hom v) = v :=
    Iso.inv_hom_id_apply (LAdicSheaf.rationalFieldExtensionCohomologyIso B X ℓ f j k' kbar F i) v
  exact (hv.trans (congrArg (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B
    (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
    (compactificationFieldBaseChange f j k') kbar p (q * (m + 1)) hcard'
    (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i).hom hi)).symm

end Frobenius

end Cohomology

end Stacks.EtaleCohomology

end
