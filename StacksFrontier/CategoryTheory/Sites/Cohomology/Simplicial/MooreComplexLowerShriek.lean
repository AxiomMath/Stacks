module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModuleDerivedLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Derived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Sheafify
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.DerivedLowerShriekFibreHomologyIso
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekFreeModuleBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# `Lπ_!` of a simplicial abelian sheaf is computed by its Moore complex

Let `C` be a site and `π : Δ × C ⥤ C` the projection. The prose of the Stacks project preceding
Lemma 09D2 records that for a simplicial abelian sheaf `F_•` on `C`, read as an abelian sheaf on
`Δ × C`, the object `Lπ_!(F_•)` of `D(C)` is represented by the associated chain complex
`s(F_•)` (Simplicial, Section 0194), by Lemmas 08PJ and 08Q9. This file proves the form of that
statement on homology sheaves, naturally in `F_•`:

`H^{-n}(Lπ_! F_•) ≅ H_n(s(F_•))^#`,

the sheaf associated to the presheaf of homology of the Moore complex.

## Main definitions

* `Stacks.SimplicialModules.projectionCosimplicial`: the cosimplicial objects
  `A_{•,V} = (⦋•⦌, V)` of `Δ × C`, one over each object `V` of `C`; each is a point resolution of
  the fibre `Δ × {V} ≅ Δ` (Stacks 08QD).

## Main results

* `Stacks.SimplicialModules.projectionCosimplicial_pointResolution`: the fibrewise point
  resolution hypothesis.

## References

* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2), the prose preceding it.
* [Stacks Project, Tag 08PJ](https://stacks.math.columbia.edu/tag/08PJ)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QD](https://stacks.math.columbia.edu/tag/08QD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology
open Stacks.Sites.FibredCategory

universe u

namespace Stacks.SimplicialModules

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- The cosimplicial objects `A_{•,V} = (⦋•⦌, V)` of `Δ × C`, functorially in `V`. -/
abbrev projectionCosimplicial : C ⥤ CosimplicialObject (SimplexCategory × C) :=
  Functor.curry.obj (CategoryTheory.Prod.swap C SimplexCategory)

/-- Each `A_{•,V}` lies over `V`. -/
theorem projectionCosimplicial_comp :
    projectionCosimplicial (C := C) ⋙
        (Functor.whiskeringRight SimplexCategory (SimplexCategory × C) C).obj
          (projectionSituation J).p =
      Functor.const SimplexCategory :=
  rfl

/-- The object `(⦋n⦌, V)` of the fibre over `V`. -/
def fiberObj (V : C) (n : SimplexCategory) : (projectionSituation J).p.Fiber V :=
  ⟨(n, V), rfl⟩

/-- In the fibre over `V`, the morphisms `(⦋n⦌, V) ⟶ (⦋m⦌, V)` are the morphisms `⦋n⦌ ⟶ ⦋m⦌`. -/
def fiberHomEquiv (V : C) (n m : SimplexCategory) :
    (fiberObj J V n ⟶ fiberObj J V m) ≃ (n ⟶ m) where
  toFun φ := φ.1.1
  invFun a := ⟨(a, 𝟙 V), (inferInstance : (projectionSituation J).p.IsHomLift
    ((projectionSituation J).p.map ((a, 𝟙 V) : ((n, V) : SimplexCategory × C) ⟶ (m, V)))
      ((a, 𝟙 V) : ((n, V) : SimplexCategory × C) ⟶ (m, V)))⟩
  left_inv φ := by
    apply Subtype.ext
    have h : 𝟙 V = φ.1.2 :=
      @IsHomLift.eq_of_isHomLift _ _ _ _ (projectionSituation J).p
        ((n, V) : SimplexCategory × C) ((m, V) : SimplexCategory × C) (𝟙 V) φ.1 φ.2
    exact Prod.ext rfl h
  right_inv a := rfl

/-- **Each `A_{•,V}` is a point resolution of its fibre**: for every object `W` of the fibre over
`V`, the simplicial set `Mor(A_{•,V}, W)` is the standard simplex `Δ[m]` on the simplicial degree
`m` of `W`, which is contractible (Stacks 08QD). -/
theorem projectionCosimplicial_pointResolution (V : C)
    (W : (projectionSituation J).p.Fiber V) :
    ∃ f : (Functor.Fiber.inducedFunctor
          (Functor.congr_obj (projectionCosimplicial_comp J) V)).op ⋙ yoneda.obj W ⟶
        (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1},
      SimplicialObject.homotopyEquivalences (Type u) f := by
  obtain ⟨⟨m, V'⟩, hW⟩ := W
  change V' = V at hW
  subst hW
  obtain ⟨f₀, hf₀⟩ := Stacks.ChaoticSite.isPointResolution_id_simplexCategory m
  let e : (Functor.Fiber.inducedFunctor
        (Functor.congr_obj (projectionCosimplicial_comp J) V')).op ⋙
          yoneda.obj (fiberObj J V' m) ≅
      ((𝟭 SimplexCategory).op ⋙ yoneda.obj m) ⋙ uliftFunctor.{u} :=
    NatIso.ofComponents (fun n => Equiv.toIso ((fiberHomEquiv J V' n.unop m).trans
      Equiv.ulift.symm)) (fun _ => rfl)
  let e' : (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{1} ⋙ uliftFunctor.{u} ≅
      (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1} :=
    Functor.constComp _ _ _ ≪≫
      (Functor.const _).mapIso (Equiv.toIso (Equiv.ulift.trans Equiv.punitEquivPUnit))
  exact ⟨e.hom ≫ Functor.whiskerRight f₀ uliftFunctor ≫ e'.hom,
    CategoryTheory.SimplicialObject.homotopyEquivalences_iso_comp_iso _ _ _
      (CategoryTheory.SimplicialObject.homotopyEquivalences_whiskering_map uliftFunctor hf₀)⟩

/-! ### The δ-functor of the Moore complex on presheaves -/

section Moore

/-- The homology of the Moore complex `V ↦ G(A_{•,V})` as a homological δ-functor on abelian
presheaves on `Δ × C`: `G ↦ G(A_{•,V})` is exact, being evaluation. -/
def pointMooreDeltaFunctor :
    Stacks.CategoryHomology.HomologicalDeltaFunctor
      ((SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  Stacks.CategoryHomology.HomologicalDeltaFunctor.ofChainComplexFunctor
    ((projectionSituation J).pointMooreComplex (projectionCosimplicial (C := C)))
    (fun {S} hS => by
      refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
      exact hS.map_of_exact ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
        (((projectionSituation J).pointEvaluationShape
          (projectionCosimplicial (C := C))).obj (op ⦋n⦌))))

/-- **The δ-functor of the Moore complex is coeffaceable**: every abelian presheaf on `Δ × C` is
an epimorphic image of a direct sum of free abelian presheaves on representables, whose Moore
complexes have no positive homology (Stacks 08Q9, fibrewise). -/
theorem coeffaceable_pointMooreDeltaFunctor : (pointMooreDeltaFunctor J).Coeffaceable :=
  Stacks.CategoryHomology.HomologicalDeltaFunctor.Coeffaceable.of_exists_epi_isZero _ fun X n => by
    obtain ⟨P, hP, π, hπ⟩ := (projectionSituation J).exists_epi_isFreeSum X
    exact ⟨P, π, hπ, (projectionSituation J).isZero_pointMooreComplex_homology_of_isFreeSum
      (projectionCosimplicial_comp J) (projectionCosimplicial_pointResolution J) P hP n⟩

/-- The δ-functor of the Moore complex on abelian presheaves on `Δ × C` is universal. -/
instance isUniversal_pointMooreDeltaFunctor : (pointMooreDeltaFunctor J).IsUniversal :=
  have := coeffaceable_pointMooreDeltaFunctor J
  Stacks.CategoryHomology.HomologicalDeltaFunctor.isUniversal_of_coeffaceable _

/-- In degree zero the homology of the Moore complex is `V ↦ H_0(G(A_{•,V}))`, the cokernel of
the two faces. -/
def pointMooreHomologyZeroIso :
    (pointMooreDeltaFunctor J).functor 0 ≅
      (projectionSituation J).pointZero (projectionCosimplicial (C := C)) :=
  NatIso.ofComponents (fun G => ChainComplex.isoHomologyι₀ _) (fun {G G'} α => by
    change HomologicalComplex.homologyMap _ 0 ≫ (ChainComplex.isoHomologyι₀ _).hom =
      (ChainComplex.isoHomologyι₀ _).hom ≫ HomologicalComplex.opcyclesMap _ 0
    simp [HomologicalComplex.homologyι_naturality])

/-- **The degree-zero comparison**: degree-zero fibre homology and the degree-zero homology of the
Moore complex are both left adjoint to restriction along the projection, the first as a left Kan
extension (Stacks 08PE), the second by the degree-zero part of Stacks 08Q9 fibrewise. -/
def fiberHomologyZeroIsoPointMoore :
    (fiberHomologyPresheafDeltaFunctor (projectionSituation J)).functor 0 ≅
      (pointMooreDeltaFunctor J).functor 0 :=
  (lanIsoFiberHomologyPresheafFunctorZero (projectionSituation J)).symm ≪≫
    ((projectionSituation J).p.op.lanAdjunction AddCommGrpCat.{u}).leftAdjointUniq
      ((projectionSituation J).pointZeroAdjunction (projectionCosimplicial_comp J)
        (projectionCosimplicial_pointResolution J)) ≪≫
    (pointMooreHomologyZeroIso J).symm

/-- **Fibre homology is the homology of the Moore complex**, as homological δ-functors on abelian
presheaves on `Δ × C`: both are universal and they agree in degree zero (the dual of
Stacks 010U). -/
def fiberHomologyDeltaIsoPointMoore :
    fiberHomologyPresheafDeltaFunctor (projectionSituation J) ≅ pointMooreDeltaFunctor J :=
  have := isUniversal_fiberHomologyPresheafDeltaFunctor (projectionSituation J)
  Stacks.CategoryHomology.HomologicalDeltaFunctor.IsUniversal.isoOfIso
    (fiberHomologyZeroIsoPointMoore J)

/-- **The presheaf of fibre homology of an abelian presheaf `F` on `Δ × C` is the homology of its
Moore complex** `V ↦ s(F(⦋•⦌, V))`, naturally in `F`. -/
def fiberHomologyPresheafIsoPointMoore (n : ℕ) :
    fiberHomologyPresheafFunctor (projectionSituation J) n ≅
      (projectionSituation J).pointMooreComplex (projectionCosimplicial (C := C)) ⋙
        HomologicalComplex.homologyFunctor _ _ n :=
  Stacks.CategoryHomology.HomologicalDeltaFunctor.isoApp (fiberHomologyDeltaIsoPointMoore J) n

end Moore

/-! ### `Lπ_!` on homology sheaves -/

section Sheaf

attribute [local instance] HasDerivedCategory.standard

/-- **`L_nπ_!` is the sheafified homology of the Moore complex** (the prose before Lemma 09D2, on
homology sheaves): for an abelian sheaf `F` on `Δ × C`, naturally in `F`,
`H^{-n}(Lπ_!(F)) ≅ (V ↦ H_n(s(F(⦋•⦌, V))))^#`. This is Stacks 08PJ followed by
`fiberHomologyPresheafIsoPointMoore`. -/
def derivedLowerShriekHomologyIsoMoore (n : ℕ) :
    (projectionSituation J).derivedAbelianLowerShriekHomology n ≅
      sheafToPresheaf (simplicialProjectionTopology J) AddCommGrpCat.{u} ⋙
        (projectionSituation J).pointMooreComplex (projectionCosimplicial (C := C)) ⋙
          HomologicalComplex.homologyFunctor _ _ n ⋙ presheafToSheaf J AddCommGrpCat.{u} :=
  (projectionSituation J).derivedLowerShriekHomologyIsoFiberHomology n ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (fiberHomologyPresheafIsoPointMoore J n) _)

/-- **A morphism of abelian sheaves on `Δ × C` which induces an isomorphism on the sheafified
homology of the Moore complexes in every degree is inverted by `Lπ_!`.** -/
theorem isIso_derivedLowerShriek_map_single_of_isIso_homology
    {F G : Sheaf (simplicialProjectionTopology J) AddCommGrpCat.{u}} (a : F ⟶ G)
    (ha : ∀ n : ℕ, IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map
      (HomologicalComplex.homologyMap
        (((projectionSituation J).pointMooreComplex (projectionCosimplicial (C := C))).map a.hom)
        n))) :
    IsIso ((derivedLowerShriek J).map ((DerivedCategory.singleFunctor _ 0).map a)) := by
  have hn : ∀ n : ℕ, IsIso (((projectionSituation J).derivedAbelianLowerShriekHomology n).map a) :=
    fun n => (NatIso.isIso_map_iff (derivedLowerShriekHomologyIsoMoore J n) a).mpr (ha n)
  rw [DerivedCategory.isIso_iff]
  intro k
  rcases le_or_gt k 0 with hk | hk
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨k.natAbs, by omega⟩
    exact hn n
  · have h := (projectionSituation J).isLE_derivedAbelianLowerShriek_obj_single
      (projectionSituation J).abelianLowerShriekAcyclic
    have hF := h F
    have hG := h G
    exact isIso_of_source_target_iso_zero _
      ((DerivedCategory.isZero_of_isLE _ 0 k hk).isoZero)
      ((DerivedCategory.isZero_of_isLE _ 0 k hk).isoZero)

end Sheaf

end Stacks.SimplicialModules

end
