module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TermwiseInvertibility
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.CopowerMooreHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.FreeModuleResolution
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedOfSystem
import StacksCore.Tactic.StacksAttribute

/-!
# Lemma 09D2: `Lπ_!(K) = Lπ_!(K ⊗^L_{A_•} B_•)`

Let `C` be a site, `π : Δ × C ⥤ C` the projection, and `A_• ⟶ B_•` a homomorphism of simplicial
sheaves of commutative rings on `C`. If `Lπ_!A_• ⟶ Lπ_!B_•` is an isomorphism in `D(C)`, then
the canonical map `Lπ_!(K) ⟶ Lπ_!(K ⊗^L_{A_•} B_•)` is an isomorphism for every `K` in
`D(A_•)` (Stacks 09D2).

## Main results

* `Stacks.SimplicialModules.isIso_derivedBaseChangeComparison`: if `Lπ_!A_• ⟶ Lπ_!B_•` is an
  isomorphism, then `Lπ_!(K) ⟶ Lπ_!(K ⊗^L_{A_•} B_•)` is an isomorphism for every `K`.
* `Stacks.SimplicialModules.isIso_derivedLowerShriek_map_single_sheafify`: `Lπ_!` inverts the
  sheafification of a morphism of abelian presheaves on `Δ × C` whose Moore homology is inverted
  by sheafification on `C`.

## Proof

The proof is the source's, with the generators made explicit.

1. **Resolution.** Every complex of `A_•`-modules is quasi-isomorphic to a sequential colimit of
  bounded above complexes whose terms are free simplicial modules `A_•⟨∐ h_{X_i}⟩` on sums of
  representables of `Δ × C` (`exists_freeSumResolution`, the ladder of Stacks 077J). These terms
  are flat, so the colimit is K-flat with flat terms (Stacks 06YQ, 06YR), and there the derived
  base change is computed degreewise (Stacks 06YY): the canonical map is `Lπ_!` of the degreewise
  unit `M ⟶ M ⊗_{A_•} B_•` read on underlying complexes of abelian sheaves
  (`isIso_derivedBaseChangeComparison_app_Q_of_kFlat`).
2. **Colimits and bounded above complexes.** `Lπ_!` is exact and commutes with countable direct
  sums, so it inverts the unit at the colimit once it does at every term of the sequence
  (Stacks 0949), and at a bounded above complex once it does at each of its terms placed in a
  single degree (the stupid filtration); this is
  `StacksFrontier/Algebra/Homology/DerivedCategory/TermwiseInvertibility.lean`.
3. **Generators.** At `A_•⟨S⟩`, `S = ∐ h_{X_i}`, the unit is on underlying abelian sheaves the
  sheafification of the copower by `S` of `A_• ⟶ B_•` (`baseChangeUnit_freeModule_arrowIso`).
  By Stacks 08PJ and the point resolution `[•] ↦ ([•], V)` of the fibres (Stacks 08Q9, 08QD),
  `L_nπ_!` of a sheafified presheaf is the sheafified homology of its Moore complexes
  `V ↦ s(P(⦋•⦌, V))`; for the copower by `h_{(⦋m⦌, U)}` these are `s(P(⦋•⦌, V)) × Δ[m] ×
  Hom(V, U)`, whose homology is, `Δ[m]` being contractible, the copower by `h_U` of the homology
  of `s(P(⦋•⦌, V))`; and sheafification inverts the copower of what it inverts
  (`isIso_sheafify_homology_moore_copowerMap`). The hypothesis says exactly that sheafification
  inverts the Moore homology of `A_• ⟶ B_•` (`isIso_sheafify_homology_moore_unitPresheafMap`).

## References

* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
* [Stacks Project, Tag 08PJ](https://stacks.math.columbia.edu/tag/08PJ)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 0949](https://stacks.math.columbia.edu/tag/0949)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.SimplicialModules

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

section Criterion

/-- A functor inverting `g` inverts every `f` with `Arrow.mk f ≅ Arrow.mk g`. -/
private theorem isIso_map_of_arrow_iso {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] (Ψ : 𝒜 ⥤ ℬ)
    {X Y X' Y' : 𝒜} {f : X ⟶ Y} {g : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk g)
    (h : IsIso (Ψ.map g)) : IsIso (Ψ.map f) :=
  ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (Ψ.mapArrow.mapIso e)).mpr h

/-- **`Lπ_!` inverts the sheafification of a morphism of abelian presheaves on `Δ × C` whose
Moore homology is inverted by sheafification on `C`.** -/
theorem isIso_derivedLowerShriek_map_single_sheafify
    {P P' : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}} (c : P ⟶ P')
    (hc : ∀ n : ℕ, IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map
      (HomologicalComplex.homologyMap ((mooreComplex J).map c) n))) :
    IsIso ((derivedLowerShriek J).map ((DerivedCategory.singleFunctor _ 0).map
      ((presheafToSheaf (simplicialProjectionTopology J) AddCommGrpCat.{u}).map c))) := by
  let s := projectionSituation J
  have e : ∀ n : ℕ, presheafToSheaf s.topology AddCommGrpCat.{u} ⋙
      s.derivedAbelianLowerShriekHomology n ≅
        mooreComplex J ⋙ HomologicalComplex.homologyFunctor _ _ n ⋙
          presheafToSheaf J AddCommGrpCat.{u} := fun n =>
    s.derivedLowerShriekHomologyPresheafNatIso s.abelianLowerShriekAcyclic
      (s.uliftFreeCoverLowerShriekAcyclic_of_generatorsAcyclic
        (Stacks.Sites.FibredCategory.FibredCategorySituation.abelianLowerShriekGeneratorsAcyclic
          s)) n ≪≫
      Functor.isoWhiskerRight (fiberHomologyPresheafIsoPointMoore J n) _
  have hn : ∀ n : ℕ, IsIso ((s.derivedAbelianLowerShriekHomology n).map
      ((presheafToSheaf s.topology AddCommGrpCat.{u}).map c)) :=
    fun n => (NatIso.isIso_map_iff (e n) c).mpr (hc n)
  rw [DerivedCategory.isIso_iff]
  intro k
  rcases le_or_gt k 0 with hk | hk
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨k.natAbs, by omega⟩
    exact hn n
  · have h := s.isLE_derivedAbelianLowerShriek_obj_single s.abelianLowerShriekAcyclic
    have hF := h ((presheafToSheaf s.topology AddCommGrpCat.{u}).obj P)
    have hG := h ((presheafToSheaf s.topology AddCommGrpCat.{u}).obj P')
    exact isIso_of_source_target_iso_zero _
      ((DerivedCategory.isZero_of_isLE _ 0 k hk).isoZero)
      ((DerivedCategory.isZero_of_isLE _ 0 k hk).isoZero)

end Criterion

variable {A B : SimplicialObject (Sheaf J CommRingCat.{u})} (φ : A ⟶ B)

section Hypothesis

variable (hφ : IsIso ((derivedLowerShriek J).map
  ((DerivedCategory.singleFunctor _ 0).map (ringAbelianSheafMap J φ))))
include hφ

/-- The hypothesis of Lemma 09D2, read on the Moore homology of `A_• ⟶ B_•`. -/
theorem isIso_sheafify_homology_moore_unitPresheafMap (n : ℕ) :
    IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map
      (HomologicalComplex.homologyMap ((mooreComplex J).map (unitPresheafMap J φ)) n)) := by
  have h' : IsIso ((DerivedCategory.homologyFunctor _ (-(n : ℤ))).map
      ((derivedLowerShriek J).map ((DerivedCategory.singleFunctor _ 0).map
        (ringAbelianSheafMap J φ)))) := inferInstance
  have h : IsIso (((projectionSituation J).derivedAbelianLowerShriekHomology n).map
      (ringAbelianSheafMap J φ)) := h'
  have h2 := (NatIso.isIso_map_iff (derivedLowerShriekHomologyIsoMoore J n)
    (ringAbelianSheafMap J φ)).mp h
  rwa [Functor.comp_map, Functor.comp_map, Functor.comp_map,
    HomologicalComplex.homologyFunctor_map] at h2

/-- **The generator case**: on a free simplicial module on a sum of representables, `Lπ_!`
inverts the base change unit, read on underlying abelian sheaves. -/
theorem isIso_derivedLowerShriek_map_single_unit_freeModule {ι : Type u}
    (X : ι → SimplexCategory × C) :
    IsIso ((derivedLowerShriek J).map ((DerivedCategory.singleFunctor _ 0).map
      ((toAbelian J A).map ((baseChangeAdjunction J φ).unit.app
        ((freeModule J A).obj (∐ fun i => yoneda.obj (X i))))))) := by
  obtain ⟨e⟩ := baseChangeUnit_freeModule_arrowIso J φ (∐ fun i => yoneda.obj (X i))
  have h := isIso_derivedLowerShriek_map_single_sheafify J _ fun n =>
    isIso_sheafify_homology_moore_copowerMap J (unitPresheafMap J φ) n
      (isIso_sheafify_homology_moore_unitPresheafMap J φ hφ n) X
  exact isIso_map_of_arrow_iso (derivedLowerShriek J)
    ((DerivedCategory.singleFunctor _ 0).mapArrow.mapIso e) h

end Hypothesis

section Assembly

/-- The base change unit `M ⟶ M ⊗_{A_•} B_•` read on underlying abelian sheaves, as a natural
transformation. -/
def unitAbelian :
    toAbelian J A ⟶ baseChange J φ ⋙ restrictScalars J φ ⋙ toAbelian J A where
  app M := (toAbelian J A).map ((baseChangeAdjunction J φ).unit.app M)
  naturality M N f := by
    simp only [Functor.comp_map, ← Functor.map_comp]
    congr 1
    exact (baseChangeAdjunction J φ).unit.naturality f

/-- The component of `unitAbelian` at `M` is the base change unit at `M` read on underlying
abelian sheaves. -/
@[simp]
lemma unitAbelian_app (M : Modules J A) :
    (unitAbelian J φ).app M = (toAbelian J A).map ((baseChangeAdjunction J φ).unit.app M) :=
  rfl

/-- The base change unit on complexes, read on underlying complexes of abelian sheaves. -/
abbrev unitAbelianComplex :
    (toAbelian J A).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      (baseChange J φ ⋙ restrictScalars J φ ⋙ toAbelian J A).mapHomologicalComplex
        (ComplexShape.up ℤ) :=
  NatTrans.mapHomologicalComplex (unitAbelian J φ) (ComplexShape.up ℤ)

/-- The derived category of abelian sheaves on `C` has countable coproducts. -/
instance : HasColimitsOfShape (Discrete ℕ)
    (DerivedCategory (Sheaf J AddCommGrpCat.{u})) :=
  have := CategoryTheory.SimplicialSiteSituation.derivedSheafHasCountableCoproducts J
  inferInstance

/-- Sequential colimits of abelian sheaves on `Δ × C` are exact. -/
instance : HasExactColimitsOfShape ℕ (Sheaf (simplicialProjectionTopology J) AddCommGrpCat.{u}) :=
  Stacks.Cohomology.DerivedLowerShriek.hasExactColimitsOfShape_nat_sheafAb.{u}
    (simplicialProjectionTopology J)

/-- `Lπ_!` commutes with the shift. -/
instance derivedLowerShriek_commShift : (derivedLowerShriek J).CommShift ℤ :=
  (projectionSituation J).derivedAbelianLowerShriekCommShift
    (projectionSituation J).abelianLowerShriekAcyclic

/-- `Lπ_!` is a triangulated functor. -/
instance derivedLowerShriek_isTriangulated : (derivedLowerShriek J).IsTriangulated :=
  (projectionSituation J).derivedAbelianLowerShriek_isTriangulated
    (projectionSituation J).abelianLowerShriekAcyclic

/-- `Lπ_!` commutes with countable direct sums. -/
instance derivedLowerShriek_preservesCoproducts :
    PreservesColimitsOfShape (Discrete ℕ) (derivedLowerShriek J) :=
  have := ((projectionSituation J).derivedAbelianLowerShriekAdjunction
    (projectionSituation J).abelianLowerShriekAcyclic).leftAdjoint_preservesColimits
  inferInstance

variable (hφ : IsIso ((derivedLowerShriek J).map
  ((DerivedCategory.singleFunctor _ 0).map (ringAbelianSheafMap J φ))))
include hφ

/-- `Lπ_!` inverts the base change unit of a bounded above complex of free simplicial modules on
sums of representables. -/
theorem isIso_derivedLowerShriek_map_Q_unitAbelianComplex_of_isStrictlyLE
    (K : CochainComplex (Modules J A) ℤ) (b : ℤ) [K.IsStrictlyLE b]
    (hK : ∀ i, IsFreeSumModule J A (K.X i)) :
    IsIso ((derivedLowerShriek J).map (DerivedCategory.Q.map
      ((unitAbelianComplex J φ).app K))) := by
  have hi : ∀ i, IsIso ((derivedLowerShriek J).map ((DerivedCategory.singleFunctor _ i).map
      (((unitAbelianComplex J φ).app K).f i))) := by
    intro i
    rw [Stacks.DerivedCategory.TermwiseInvertibility.isIso_map_singleFunctor_iff]
    obtain ⟨ι, X, ⟨e⟩⟩ := hK i
    have h := isIso_derivedLowerShriek_map_single_unit_freeModule J φ hφ X
    have e' : Arrow.mk (((unitAbelianComplex J φ).app K).f i) ≅
        Arrow.mk ((unitAbelian J φ).app ((freeModule J A).obj (∐ fun i => yoneda.obj (X i)))) :=
      Arrow.isoMk ((toAbelian J A).mapIso e)
        ((baseChange J φ ⋙ restrictScalars J φ ⋙ toAbelian J A).mapIso e)
        ((unitAbelian J φ).naturality e.hom)
    exact isIso_map_of_arrow_iso (DerivedCategory.singleFunctor _ 0 ⋙ derivedLowerShriek J) e' h
  exact Stacks.DerivedCategory.TermwiseInvertibility.isIso_map_Q_map_of_isStrictlyLE
    (derivedLowerShriek J) ((unitAbelianComplex J φ).app K) (b := b) hi
    (CategoryTheory.SimplicialSiteSituation.sheafHasExactCountableDirectSums
        (simplicialProjectionTopology J))

omit hφ in
/-- The forgetful functor from `A_•`-modules to abelian sheaves preserves sequential colimits. -/
theorem toAbelian_preservesColimitsOfShape_nat (A : SimplicialObject (Sheaf J CommRingCat.{u})) :
    PreservesColimitsOfShape ℕ (toAbelian J A) :=
  have := AlgebraicGeometry.SheafOfModules.toSheaf_preservesColimits.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J A))
  have : PreservesColimitsOfSize.{0, 0} (toAbelian J A) :=
    preservesColimitsOfSize_shrink.{0, u, 0, u} _
  inferInstance

omit hφ in
/-- The functor `M ↦ M ⊗_{A_•} B_•`, read on underlying abelian sheaves, preserves sequential
colimits. -/
theorem baseChangeAbelian_preservesColimitsOfShape_nat :
    PreservesColimitsOfShape ℕ (baseChange J φ ⋙ restrictScalars J φ ⋙ toAbelian J A) :=
  have := toAbelian_preservesColimitsOfShape_nat J B
  have : PreservesColimitsOfShape ℕ (restrictScalars J φ ⋙ toAbelian J A) :=
    preservesColimitsOfShape_of_natIso (restrictScalarsCompToAbelianIso J φ).symm
  have : PreservesColimitsOfShape ℕ (baseChange J φ) :=
    (baseChangeAdjunction J φ).leftAdjoint_preservesColimits.preservesColimitsOfShape
  comp_preservesColimitsOfShape _ _

/-- `Lπ_!` inverts the base change unit of a sequential colimit of bounded above complexes of
free simplicial modules on sums of representables. -/
theorem isIso_derivedLowerShriek_map_Q_unitAbelianComplex_colimit
    (D : ℕ ⥤ CochainComplex (Modules J A) ℤ) (hD : ∀ n : ℕ, ∃ b : ℤ, (D.obj n).IsStrictlyLE b)
    (hfree : ∀ (n : ℕ) (i : ℤ), IsFreeSumModule J A ((D.obj n).X i)) :
    IsIso ((derivedLowerShriek J).map (DerivedCategory.Q.map
      ((unitAbelianComplex J φ).app (colimit D)))) := by
  have := toAbelian_preservesColimitsOfShape_nat J A
  have := baseChangeAbelian_preservesColimitsOfShape_nat J φ
  exact Stacks.DerivedCategory.TermwiseInvertibility.isIso_map_Q_map_app_colimit
    (derivedLowerShriek J)
    (CategoryTheory.SimplicialSiteSituation.sheafHasExactCountableDirectSums
        (simplicialProjectionTopology J))
    (unitAbelianComplex J φ) D fun n => by
      obtain ⟨b, hb⟩ := hD n
      exact isIso_derivedLowerShriek_map_Q_unitAbelianComplex_of_isStrictlyLE J φ hφ _ b
        (hfree n)

omit hφ in
/-- A functor inverting `g` inverts `i ≫ g ≫ j` for isomorphisms `i`, `j`. -/
lemma isIso_map_of_eq_comp {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] (Ψ : 𝒜 ⥤ ℬ)
    {X X' Y' Y : 𝒜} {f : X ⟶ Y} (i : X ⟶ X') (g : X' ⟶ Y') (j : Y' ⟶ Y) [IsIso i] [IsIso j]
    (h : f = i ≫ g ≫ j) (hg : IsIso (Ψ.map g)) : IsIso (Ψ.map f) := by
  rw [h, Functor.map_comp, Functor.map_comp]
  infer_instance

omit hφ in
/-- **The canonical map of Stacks 09D2 at a K-flat complex with flat terms** is `Lπ_!` of the
degreewise base change unit, read on underlying complexes of abelian sheaves. -/
theorem isIso_derivedBaseChangeComparison_app_Q_of_kFlat
    (P : CochainComplex (Modules J A) ℤ)
    (hP : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := ⟨SimplexCategory × C, simplicialProjectionTopology J, commRingSheaf J A⟩)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))
    (h : IsIso ((derivedLowerShriek J).map (DerivedCategory.Q.map
      ((unitAbelianComplex J φ).app P)))) :
    IsIso ((derivedBaseChangeComparison J φ).app (DerivedCategory.Q.obj P)) := by
  let M := (HomotopyCategory.quotient (Modules J A) (ComplexShape.up ℤ)).obj P
  have hcmp : IsIso ((derivedBaseChangeComparisonh J φ).app M) :=
    Stacks.Cohomology.DerivedPullbackOnRingedTopoi.isIso_derivedPullbackComparison_app_kFlat
      (coefficientChangeHom J φ) (Functor.isMorphismOfSites_id _) P hP.1 hP.2
  let u := (CategoryTheory.Adjunction.mapHomologicalComplexAdjunction (baseChangeAdjunction J φ)
    (ComplexShape.up ℤ)).unit.app P
  let U := (derivedBaseChangeAdjunction J φ).unit.app (DerivedCategory.Qh.obj M)
  let fi := (restrictScalars J φ).mapDerivedCategoryFactorsh.inv.app
    (((baseChange J φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)
  let hU₀ := ((baseChangeAdjunction J φ).mapHomotopyCategoryAdjunction
    (ComplexShape.up ℤ)).unit.app M
  let e₁ : Arrow.mk U ≅ Arrow.mk (DerivedCategory.Qh.map hU₀) :=
    Arrow.isoMk (Iso.refl _)
      (asIso ((derivedRestrictScalars J φ).map ((derivedBaseChangeComparisonh J φ).app M)) ≪≫
        (asIso fi).symm) (by
          dsimp
          rw [Category.id_comp, ← Category.assoc,
            derivedBaseChangeAdjunction_unit_fac J φ M, Category.assoc, IsIso.hom_inv_id,
            Category.comp_id])
  let e₂ : Arrow.mk (DerivedCategory.Qh.map hU₀) ≅ Arrow.mk (DerivedCategory.Q.map u) :=
    Arrow.isoOfNatIso (DerivedCategory.quotientCompQhIso _) (Arrow.mk u)
  let e₃ : (toAbelianDerived J A).mapArrow.obj (Arrow.mk (DerivedCategory.Q.map u)) ≅
      Arrow.mk (DerivedCategory.Q.map ((unitAbelianComplex J φ).app P)) :=
    Arrow.isoOfNatIso (toAbelian J A).mapDerivedCategoryFactors (Arrow.mk u)
  have hU : IsIso ((derivedLowerShriek J).map ((toAbelianDerived J A).map U)) :=
    isIso_map_of_arrow_iso (derivedLowerShriek J)
      ((toAbelianDerived J A).mapArrow.mapIso (e₁ ≪≫ e₂) ≪≫ e₃) h
  have hM : IsIso ((derivedBaseChangeComparison J φ).app (DerivedCategory.Qh.obj M)) := by
    rw [derivedBaseChangeComparison_app, derivedBaseChangeUnitAbelian_app, Functor.map_comp]
    exact IsIso.comp_isIso' hU inferInstance
  exact (NatTrans.isIso_app_iff_of_iso _ ((DerivedCategory.quotientCompQhIso _).app P)).mp hM

/-- Let `C` be a site and `A_• ⟶ B_•` a homomorphism of simplicial sheaves of (commutative) rings
on `C`. If `Lπ_!A_• ⟶ Lπ_!B_•` is an isomorphism in `D(C)`, then the canonical map
`Lπ_!(K) ⟶ Lπ_!(K ⊗^L_{A_•} B_•)` is an isomorphism for every `K` in `D(A_•)`. -/
@[stacks 09D2]
theorem isIso_derivedBaseChangeComparison : IsIso (derivedBaseChangeComparison J φ) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  rw [← NatTrans.isIso_app_iff_of_iso _ (DerivedCategory.Q.objObjPreimageIso K)]
  obtain ⟨D, α, hα, hD, hfree⟩ :=
    exists_freeSumResolution J A (DerivedCategory.Q.objPreimage K)
  have : IsIso (DerivedCategory.Q.map α) := by
    rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]
  rw [← NatTrans.isIso_app_iff_of_iso _ (asIso (DerivedCategory.Q.map α))]
  have hflat : ∀ (n : ℕ) (i : ℤ), AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := commRingSheaf J A) ((D.obj n).X i) := fun n i =>
    isFlat_of_isFreeSumModule J A (hfree n i)
  have := Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} (commRingSheaf J A)
  have : ∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (commRingSheaf J A)).obj M).Additive := fun M =>
    Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} (commRingSheaf J A) M
  have := Stacks.SheafOfModules.KFlatResolution.hasTotal_ofSize (commRingSheaf J A)
  exact isIso_derivedBaseChangeComparison_app_Q_of_kFlat J φ (colimit D)
    ⟨Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat_ofSize
      (commRingSheaf J A) D hD hflat,
      Stacks.SheafOfModules.KFlatResolution.isFlat_colimit_X_ofSize (commRingSheaf J A) D hflat⟩
    (isIso_derivedLowerShriek_map_Q_unitAbelianComplex_colimit J φ hφ D hD hfree)

end Assembly


end Stacks.SimplicialModules
