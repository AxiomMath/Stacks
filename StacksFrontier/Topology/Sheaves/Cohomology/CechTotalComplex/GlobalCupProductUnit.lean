module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductShift
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedGlobalCupProduct.UnitEvaluation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.UnitLeftFactorNaturality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomFilteredColimit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction

/-!
# The unit law for the global cup product

Let `(S, 𝒪_S)` be a ringed space and `A = Γ(S, 𝒪_S)`. The class `1 ∈ H⁰(S, 𝒪_S)` of the global
section `1` is a left unit for the cup product of Cohomology, Section 0FKU, read on the total
tensor complex: for a complex `ℳ^•` of `𝒪_S`-modules and `η ∈ Hʲ(S, ℳ^•)`, the cup product
`1 ∪ η ∈ Hʲ(S, Tot(𝒪_S[0] ⊗ ℳ^•))`, carried to `Hʲ(S, ℳ^•)` by the left unitor
`Tot(𝒪_S[0] ⊗ ℳ^•) ≅ ℳ^•`, is `η`.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_unit_left`: the class of `1` is a
  left unit for the cup product.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

universe u


namespace Stacks.Cohomology.DerivedGlobalCupProduct

open Stacks.Cohomology.GlobalKunneth
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open RingTheory.TorProducts (cycleClass)
open scoped TensorProduct
open Stacks.Cech.SheafTensorPairing (ι_naiveCupProductEval_f pairEval evalComplex
  naiveCupProductEval)
open Stacks.Cech.ModuleCupProduct (CoeffRing)
open Stacks.Cech.CupProduct (tensorModules)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose

open scoped CategoryTheory.Prod Stacks.Topology.SheafTensorAdditiveOnOpens

variable {S : AlgebraicGeometry.RingedSpace.{u, u}}

/-- The collapse `Tot(𝒪_S[0] ⊗ ℳ^•) ≅ ℳ^•` of a complex of modules on a ringed space `S`: the
left unitor `AlgebraicGeometry.RingedSite.structureSheafComplexTensorLeftIso` on the site of
open subsets of `S`. -/
abbrev unitTensorLeftIso
    (M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) :=
  AlgebraicGeometry.RingedSite.structureSheafComplexTensorLeftIso
    (Stacks.SheafOfModules.opensRingedSite S.sheaf) M

/-- The structure sheaf `𝒪_S` placed in degree `0`, as a complex of modules over the structure
sheaf of the site of open subsets of `S`: the unit of the monoidal structure on complexes, and
`unitComplex S 0` up to the spelling of the ring sheaf. -/
abbrev unitComplexR (S : AlgebraicGeometry.RingedSpace.{u, u}) :
    CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ :=
  AlgebraicGeometry.RingedSite.structureSheafComplex (Stacks.SheafOfModules.opensRingedSite S.sheaf)

/-- The global section `1` of `𝒪_S` in degree `0`, as a family of global cocycles parametrized
by the free module of rank one. -/
abbrev unitCycleHom (S : AlgebraicGeometry.RingedSpace.{u, u}) :
    ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S (unitComplexR S)).cycles 0 :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing S) _
    (unitCycle S 0 : (sectionsComplex S (unitComplexR S)).cycles 0))

/-- Moving the degree of a family of global cocycles along an equality of degrees moves the
degree of its class. -/
theorem globalCycleClass_comp_eqToHom {T : ModuleCat.{u} (baseRing S)}
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ} {j k : ℤ} (h : j = k)
    (z : T ⟶ (sectionsComplex S K).cycles j) :
    globalCycleClass z ≫ eqToHom (congrArg (cohomologyModule (DerivedCategory.Q.obj K)) h) =
      globalCycleClass (z ≫ eqToHom (congrArg (fun k => (sectionsComplex S K).cycles k) h)) := by
  subst h
  simp

/-- The naturality of `eqToHom` between the cohomology modules of two degrees. -/
theorem eqToHom_comp_cohomologyModule_map
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
    (f : K ⟶ L) {j k : ℤ} (h : j = k) :
    eqToHom (congrArg (cohomologyModule K) h) ≫
        (DerivedCategory.homologyFunctor _ k).map ((baseSections S).map f) =
      (DerivedCategory.homologyFunctor _ j).map ((baseSections S).map f) ≫
        eqToHom (congrArg (cohomologyModule L) h) := by
  subst h
  simp

/-- Two morphisms out of the free module of rank one agree as soon as they agree at `1`. -/
theorem moduleCat_hom_ext_of_one {R : Type u} [CommRing R] {Y : ModuleCat.{u} R}
    (f g : ModuleCat.of R R ⟶ Y) (h : f.hom 1 = g.hom 1) : f = g :=
  ModuleCat.hom_ext (LinearMap.ext_ring h)

/-- Moving the degree of the cocycles of a complex of modules along an equality of degrees, read
on the underlying cochains. -/
theorem eqToHom_comp_iCycles {R : Type u} [Ring R] (Y : CochainComplex (ModuleCat.{u} R) ℤ)
    {j k : ℤ} (h : j = k) :
    eqToHom (congrArg (fun k => Y.cycles k) h) ≫ Y.iCycles k =
      Y.iCycles j ≫ (Y.XIsoOfEq h).hom := by
  subst h
  simp

/-- Global sections of the identification `Mʲ ≅ Mᵏ` along an equality of degrees are the
identification for the complex of global sections. -/
theorem evaluation_XIsoOfEq_hom_apply
    (M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) {j k : ℤ} (h : j = k)
    (y : (evalComplex S.sheaf ⊤ M).X j) :
    ((evalComplex S.sheaf ⊤ M).XIsoOfEq h).hom.hom y = ((M.XIsoOfEq h).hom.val.app (op ⊤)) y := by
  subst h
  rfl

/-- The left unitor carries the naive cup product of the global cocycle `1` with a family of
global cocycles `w`, computed through a lift `z₀` to the cycles of the tensor complex, back to `w`.
The coefficients are spelled through the ring of sections
`Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤` of the naive cup product. -/
theorem unitCycle_naive_unitor
    (M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (j : ℤ)
    (w : ModuleCat.of (CoeffRing S.sheaf ⊤) (CoeffRing S.sheaf ⊤) ⟶
      (evalComplex S.sheaf ⊤ M).cycles j)
    (z₀ : ((tensorModules (CoeffRing S.sheaf ⊤)).obj
        ((evalComplex S.sheaf ⊤ (unitComplexR S)).cycles 0)).obj
        ((evalComplex S.sheaf ⊤ M).cycles j) ⟶
      (HomologicalComplex.mapBifunctor (evalComplex S.sheaf ⊤ (unitComplexR S))
        (evalComplex S.sheaf ⊤ M) (tensorModules (CoeffRing S.sheaf ⊤))
        (ComplexShape.up ℤ)).cycles (0 + j))
    (hz₀ : z₀ ≫ (HomologicalComplex.mapBifunctor (evalComplex S.sheaf ⊤ (unitComplexR S))
        (evalComplex S.sheaf ⊤ M) (tensorModules (CoeffRing S.sheaf ⊤))
        (ComplexShape.up ℤ)).iCycles (0 + j) =
      Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤
          ((evalComplex S.sheaf ⊤ (unitComplexR S)).iCycles 0)
          ((evalComplex S.sheaf ⊤ M).iCycles j) ≫
        HomologicalComplex.ιMapBifunctor (evalComplex S.sheaf ⊤ (unitComplexR S))
          (evalComplex S.sheaf ⊤ M) (tensorModules (CoeffRing S.sheaf ⊤))
          (ComplexShape.up ℤ) 0 j (0 + j) rfl) :
    (λ_ (ModuleCat.of (CoeffRing S.sheaf ⊤) (CoeffRing S.sheaf ⊤))).inv ≫
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤
          (ModuleCat.ofHom (LinearMap.toSpanSingleton (CoeffRing S.sheaf ⊤)
            ((evalComplex S.sheaf ⊤ (unitComplexR S)).cycles 0) (unitCycle S 0))) w ≫ z₀ ≫
        HomologicalComplex.cyclesMap (naiveCupProductEval S.sheaf ⊤ (unitComplexR S) M) (0 + j) ≫
        HomologicalComplex.cyclesMap
          (((_root_.SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf)
            (op ⊤)).mapHomologicalComplex (ComplexShape.up ℤ)).map (unitTensorLeftIso M).hom)
          (0 + j) =
      w ≫ eqToHom (congrArg (fun k => (evalComplex S.sheaf ⊤ M).cycles k) (zero_add j).symm) := by
  refine (cancel_mono ((evalComplex S.sheaf ⊤ M).iCycles (0 + j))).1 ?_
  refine moduleCat_hom_ext_of_one _ _ ?_
  let P := evalComplex S.sheaf ⊤ (unitComplexR S)
  let Q := evalComplex S.sheaf ⊤ M
  let c₁ : P.cycles 0 := unitCycle S 0
  let s₁ : P.X 0 := unitSection S 0
  let y : Q.X j := (Q.iCycles j).hom (w.hom 1)
  have e1 : ((λ_ (ModuleCat.of (CoeffRing S.sheaf ⊤) (CoeffRing S.sheaf ⊤))).inv ≫
      Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤ (ModuleCat.ofHom
        (LinearMap.toSpanSingleton (CoeffRing S.sheaf ⊤) (P.cycles 0) c₁)) w).hom 1 =
      c₁ ⊗ₜ w.hom 1 :=
    congrArg (· ⊗ₜ[CoeffRing S.sheaf ⊤] w.hom 1) (one_smul (CoeffRing S.sheaf ⊤) c₁)
  have e2 : (P.iCycles 0).hom c₁ = s₁ := iCycles_unitCycle S 0
  have e3 := ConcreteCategory.congr_hom hz₀ (c₁ ⊗ₜ w.hom 1)
  have e4 := ConcreteCategory.congr_hom (ι_naiveCupProductEval_f S.sheaf ⊤ (unitComplexR S) M 0 j
    (0 + j) rfl) (s₁ ⊗ₜ y)
  let O := Stacks.SheafOfModules.opensRingedSite S.sheaf
  have e5 := O.structureSheafComplexTensorLeftIso_hom_f_val_app_tensorComplexSection M j (0 + j)
    rfl ⊤ y
  let iQ := Q.iCycles (0 + j)
  let ιPQ := HomologicalComplex.ιMapBifunctor P Q (tensorModules (CoeffRing S.sheaf ⊤))
    (ComplexShape.up ℤ) 0 j (0 + j) rfl
  let nv := naiveCupProductEval S.sheaf ⊤ (unitComplexR S) M
  let Gl := ((_root_.SheafOfModules.evaluation (ringSheaf.{u, u, u} S.sheaf)
    (op ⊤)).mapHomologicalComplex (ComplexShape.up ℤ)).map (unitTensorLeftIso M).hom
  have f1 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i Gl (0 + j))
    ((HomologicalComplex.cyclesMap nv (0 + j)).hom (z₀.hom (c₁ ⊗ₜ w.hom 1)))
  have f2 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i nv (0 + j))
    (z₀.hom (c₁ ⊗ₜ w.hom 1))
  have L : iQ.hom ((HomologicalComplex.cyclesMap Gl (0 + j)).hom
      ((HomologicalComplex.cyclesMap nv (0 + j)).hom (z₀.hom (c₁ ⊗ₜ w.hom 1)))) =
      ((M.XIsoOfEq (show j = 0 + j by omega)).hom.val.app (op ⊤)) y := by
    refine f1.trans ?_
    refine (congrArg (Gl.f (0 + j)).hom f2).trans ?_
    refine (congrArg (fun x => (Gl.f (0 + j)).hom ((nv.f (0 + j)).hom x)) e3).trans ?_
    refine (congrArg (fun x => (Gl.f (0 + j)).hom ((nv.f (0 + j)).hom (ιPQ.hom (x ⊗ₜ y))))
      e2).trans ?_
    refine (congrArg (Gl.f (0 + j)).hom e4).trans ?_
    exact e5
  have R : ((w ≫ eqToHom (congrArg (fun k => Q.cycles k) (zero_add j).symm)) ≫ iQ) =
      w ≫ Q.iCycles j ≫ (Q.XIsoOfEq (show j = 0 + j by omega)).hom :=
    (Category.assoc _ _ _).trans (congrArg (w ≫ ·) (eqToHom_comp_iCycles Q _))
  refine Eq.trans (b := iQ.hom ((HomologicalComplex.cyclesMap Gl (0 + j)).hom
    ((HomologicalComplex.cyclesMap nv (0 + j)).hom (z₀.hom
      (((λ_ (ModuleCat.of (CoeffRing S.sheaf ⊤) (CoeffRing S.sheaf ⊤))).inv ≫
        Stacks.Cech.SheafTensorPairing.tensorMap S.sheaf ⊤ (ModuleCat.ofHom
          (LinearMap.toSpanSingleton (CoeffRing S.sheaf ⊤) (P.cycles 0) c₁)) w).hom 1))))) rfl ?_
  refine (congrArg (fun x => iQ.hom ((HomologicalComplex.cyclesMap Gl (0 + j)).hom
    ((HomologicalComplex.cyclesMap nv (0 + j)).hom (z₀.hom x)))) e1).trans (L.trans ?_)
  exact (evaluation_XIsoOfEq_hom_apply M _ y).symm.trans (ConcreteCategory.congr_hom R 1).symm

/-- The unit law for the cup product on the class of a family of global cocycles `w`: the cup
product of the class of `1` with the class of `w`, carried back by the collapse
`Tot(𝒪_S[0] ⊗ ℳ^•) ≅ ℳ^•`, is the class of `w`. -/
theorem totalCupPairing_unit_left_of_globalCycleClass
    (M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (j : ℤ)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S M).cycles j) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (globalCycleClass (unitCycleHom S) ⊗ₘ globalCycleClass w) ≫
          totalCupPairing (unitComplexR S) M 0 j ≫
            (DerivedCategory.homologyFunctor _ (0 + j)).map ((baseSections S).map
              (DerivedCategory.Q.map (unitTensorLeftIso M).hom)) =
      globalCycleClass w ≫
        eqToHom (congrArg (cohomologyModule (DerivedCategory.Q.obj M)) (zero_add j).symm) := by
  obtain ⟨z₀, hz₀⟩ := exists_tensorCycles_naive (unitComplexR S) M 0 j
  refine (totalCupPairing_globalCycleClass_naive_assoc (unitComplexR S) M (unitCycleHom S) w z₀
    hz₀ _).trans ?_
  refine (globalCycleClass_mapR _ _).trans ?_
  refine Eq.trans ?_ (globalCycleClass_comp_eqToHom (zero_add j).symm w).symm
  refine congrArg globalCycleClass ?_
  have h := unitCycle_naive_unitor M j w z₀ hz₀
  simp only [Category.assoc] at h ⊢
  exact h

/-- Pasting commutative squares: from `l ≫ h = t ≫ l'`, `L ≫ x ≫ T ≫ t = L ≫ x' ≫ T'` and
`L ≫ x' ≫ T' ≫ l' = Y` follows `(L ≫ x ≫ T ≫ l) ≫ h = Y`. -/
theorem unit_left_paste {C : Type*} [Category* C] {P Q R U V W R' U' : C} (L : P ⟶ Q)
    (x : Q ⟶ R) (T : R ⟶ U) (l : U ⟶ V) (h : V ⟶ W) (t : U ⟶ U') (l' : U' ⟶ W) (x' : Q ⟶ R')
    (T' : R' ⟶ U') {Y : P ⟶ W} (n₁ : l ≫ h = t ≫ l') (n₂ : L ≫ x ≫ T ≫ t = L ≫ x' ≫ T')
    (k : L ≫ x' ≫ T' ≫ l' = Y) : (L ≫ x ≫ T ≫ l) ≫ h = Y := by
  simp only [Category.assoc]
  rw [n₁, ← Category.assoc T, ← Category.assoc x, ← Category.assoc L]
  simp only [Category.assoc] at n₂ ⊢
  rw [reassoc_of% n₂, k]

/-- `Hᵏ(RΓ(S, -))` of a composite of chain maps. -/
theorem homology_map_Q_comp (k : ℤ)
    {K L N : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (f : K ⟶ L) (g : L ⟶ N) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) k).map
        ((baseSections S).map (DerivedCategory.Q.map (f ≫ g))) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) k).map
          ((baseSections S).map (DerivedCategory.Q.map f)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) k).map
          ((baseSections S).map (DerivedCategory.Q.map g)) :=
  (congrArg (fun t => (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) k).map
      ((baseSections S).map t)) (DerivedCategory.Q.map_comp f g)).trans
    ((congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) k).map
      ((baseSections S).map_comp _ _)).trans
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) k).map_comp _ _))

/-- `Hᵏ(RΓ(S, -))` of an identity. -/
theorem homology_map_Q_id (k : ℤ)
    (K : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) k).map
        ((baseSections S).map (DerivedCategory.Q.map (𝟙 K))) = 𝟙 _ :=
  (congrArg (fun f => (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) k).map
      ((baseSections S).map f)) (DerivedCategory.Q.map_id _)).trans
    ((congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) k).map
      ((baseSections S).map_id _)).trans
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) k).map_id _))

/-- The cup product with the class of `1`, carried back by the collapse
`Tot(𝒪_S[0] ⊗ ℳ^•) ≅ ℳ^•`, is natural along chain maps `ℳ^• ⟶ ℳ'^•`. -/
theorem totalCupPairing_unit_left_naturality
    {M M' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ} (s : M ⟶ M')
    (j : ℤ)
    (η : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule (DerivedCategory.Q.obj M) j) :
    ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (globalCycleClass (unitCycleHom S) ⊗ₘ η) ≫ totalCupPairing (unitComplexR S) M 0 j ≫
          (DerivedCategory.homologyFunctor _ (0 + j)).map ((baseSections S).map
            (DerivedCategory.Q.map (unitTensorLeftIso M).hom))) ≫
        (DerivedCategory.homologyFunctor _ (0 + j)).map ((baseSections S).map
          (DerivedCategory.Q.map s)) =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (globalCycleClass (unitCycleHom S) ⊗ₘ (η ≫ (DerivedCategory.homologyFunctor _ j).map
          ((baseSections S).map (DerivedCategory.Q.map s)))) ≫
          totalCupPairing (unitComplexR S) M' 0 j ≫
          (DerivedCategory.homologyFunctor _ (0 + j)).map ((baseSections S).map
            (DerivedCategory.Q.map (unitTensorLeftIso M').hom)) := by
  have n₁ := AlgebraicGeometry.RingedSite.structureSheafComplexTensorLeftIso_hom_naturality
    (Stacks.SheafOfModules.opensRingedSite S.sheaf) s
  have n₁' := (homology_map_Q_comp (0 + j) _ _).symm.trans
    ((congrArg (fun f => (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S))
      (0 + j)).map ((baseSections S).map (DerivedCategory.Q.map f))) n₁.symm).trans
        (homology_map_Q_comp (0 + j) _ _))
  have n₂ := totalCupPairing_naturality' (𝟙 (unitComplexR S)) s 0 j
    (globalCycleClass (unitCycleHom S)) η
  rw [homology_map_Q_id, Category.comp_id] at n₂
  exact unit_left_paste _ _ _ _ _ _ _ _ _ n₁' n₂ rfl

/-- **The class of `1` is a left unit for the cup product.** For a complex `ℳ^•` of `𝒪_S`-modules
and `η ∈ Hʲ(S, ℳ^•)`, the cup product `1 ∪ η ∈ Hʲ(S, Tot(𝒪_S[0] ⊗ ℳ^•))` of the class
`1 ∈ H⁰(S, 𝒪_S)` of the global section `1` with `η`, carried to `Hʲ(S, ℳ^•)` by the collapse
`Tot(𝒪_S[0] ⊗ ℳ^•) ≅ ℳ^•`, is `η`. Classes are families parametrized by the free module of rank
one, and `0 + j` is identified with `j`. -/
theorem totalCupPairing_unit_left
    (M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (j : ℤ)
    (η : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule (DerivedCategory.Q.obj M) j) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (globalCycleClass (unitCycleHom S) ⊗ₘ η) ≫ totalCupPairing (unitComplexR S) M 0 j ≫
          (DerivedCategory.homologyFunctor _ (0 + j)).map ((baseSections S).map
            (DerivedCategory.Q.map (unitTensorLeftIso M).hom)) =
      η ≫ eqToHom (congrArg (cohomologyModule (DerivedCategory.Q.obj M)) (zero_add j).symm) := by
  obtain ⟨I, s, hI, hs⟩ :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective S M
  have hQ : IsIso (DerivedCategory.Q.map s) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hs
  have hR : IsIso ((baseSections S).map (DerivedCategory.Q.map s)) :=
    (Functor.mapIso (baseSections S) (@asIso _ _ _ _ (DerivedCategory.Q.map s) hQ)).isIso_hom
  have hiso : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0 + j)).map
      ((baseSections S).map (DerivedCategory.Q.map s))) :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0 + j)).mapIso
      (@asIso _ _ _ _ ((baseSections S).map (DerivedCategory.Q.map s)) hR)).isIso_hom
  refine (cancel_mono ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (0 + j)).map
    ((baseSections S).map (DerivedCategory.Q.map s)))).1 ?_
  obtain ⟨c, hc⟩ := exists_globalClass_of_isKInjective I hI j
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) j).map
      ((baseSections S).map (DerivedCategory.Q.map s))).hom (η.hom 1))
  have hw : η ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) j).map
      ((baseSections S).map (DerivedCategory.Q.map s)) =
      globalCycleClass (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing S) _ c)) :=
    moduleCat_hom_ext_of_one _ _ (hc.symm.trans (congrArg (globalClass I j)
      (one_smul (baseRing S) c).symm))
  refine (totalCupPairing_unit_left_naturality s j η).trans ?_
  rw [hw]
  refine (totalCupPairing_unit_left_of_globalCycleClass I j _).trans ?_
  rw [← hw, Category.assoc, Category.assoc]
  exact congrArg (η ≫ ·)
    (eqToHom_comp_cohomologyModule_map (DerivedCategory.Q.map s) (zero_add j).symm).symm

end Stacks.Cohomology.DerivedGlobalCupProduct
