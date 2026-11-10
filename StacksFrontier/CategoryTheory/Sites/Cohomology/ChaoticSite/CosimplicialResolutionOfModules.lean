module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.EvaluationToDerivedColimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekOfAResolution
import StacksCore.Tactic.StacksAttribute

/-!
# Homology of a category with linear coefficients, computed by a cosimplicial resolution

Let `C` be a small category carrying the chaotic topology, let `B` be a ring and let `B̲` be the
constant sheaf of rings on `C`, so that a `B̲`-module is a diagram of `B`-modules on `Cᵒᵖ` and the
homology groups `L_nπ_!(ℱ)` are the values of the left derived functors of the colimit over `Cᵒᵖ`
(Tag 08PF). Let `U_•` be a cosimplicial object of `C` such that for every object `W` the
simplicial set `Mor_C(U_•, W)` is homotopy equivalent to the constant simplicial set on a
singleton. Then

`L_nπ_!(ℱ) = H_n(ℱ(U_•))`

as `B`-modules, for every `B̲`-module `ℱ`, naturally in `ℱ`. This is the **module half of
Tag 08Q9**, whose abelian half — the same statement for an abelian presheaf, with the same `U_•` —
is `Stacks.ChaoticSite.leftDerivedColimitNatIso`.

## Main definitions

* `Stacks.ChaoticSite.ModuleValued.moduleCosimplicialMooreComplex`: the functor sending a diagram
  of `B`-modules `ℱ` to the Moore complex of the simplicial `B`-module `ℱ(U_•)`.
* `Stacks.ChaoticSite.ModuleValued.moduleCosimplicialHomologyDeltaFunctor`: its homology, as a
  homological δ-functor in `ℱ`.
* `Stacks.ChaoticSite.ModuleValued.moduleFreeRepresentablePresheaf`: the free diagram of
  `B`-modules on a representable presheaf, `j_{W!}B_W`.
* `Stacks.ChaoticSite.ModuleValued.moduleDirectSumPresheaf`, with its summand inclusions
  `moduleDirectSumPresheafIncl` and its universal morphism `moduleDirectSumPresheafDesc`: the
  sectionwise direct sum of a family of diagrams of `B`-modules.

## Main results

* `Stacks.ChaoticSite.ModuleValued.isZero_moduleCosimplicialHomology_of_abelian`: vanishing of
  the homology of `ℱ(U_•)` is detected on the underlying diagram of abelian groups.
* `Stacks.ChaoticSite.ModuleValued.mooreComplexHomologyIsoOfHomotopyEquiv`: for any functor
  `T : Type u ⥤ AddCommGrpCat` and any simplicial set `X_•` homotopy equivalent to a singleton,
  the Moore complex of `T(X_•)` has the homology of `T(∗)` placed in degree zero.
* `Stacks.ChaoticSite.ModuleValued.isZero_moduleCosimplicialHomology_projective_succ`: the
  homology of `ℱ(U_•)` vanishes in positive degrees on every projective diagram of `B`-modules.
* `Stacks.ChaoticSite.ModuleValued.module_map_op_comp_eq_of_isPointResolution`: any two morphisms
  `U_0 ⟶ W` restrict identically into a `B`-linear map killing the degree-one differential of
  `ℱ(U_•)`.
* `Stacks.ChaoticSite.ModuleValued.moduleColimitι_isColimit` and
  `Stacks.ChaoticSite.ModuleValued.moduleCosimplicialHomologyZeroNatIsoColim`: the colimit
  injection at `U_0` is a cokernel of the degree-one differential of `ℱ(U_•)`, so
  `H_0(ℱ(U_•)) = colim_{Cᵒᵖ}ℱ` naturally in `ℱ`.
* `Stacks.ChaoticSite.ModuleValued.moduleDerivedColimitDeltaFunctor_isUniversal`: the left
  derived functors of `colim` on diagrams of `B`-modules form a universal homological δ-functor.
* `Stacks.ChaoticSite.ModuleValued.moduleLeftDerivedColimitNatIso`: for diagrams of `B`-modules
  `ℱ`, `L_n colim_{Cᵒᵖ}(ℱ) = H_n(ℱ(U_•))` naturally in `ℱ`.
* `Stacks.ChaoticSite.ModuleValued.moduleLeftDerivedPointLowerShriekNatIso`: the sections at the
  point of `L_nπ_!(ℱ)` are `H_n(ℱ(U_•))` for sheaves of `B`-modules `ℱ` on the chaotic site,
  naturally in `ℱ`.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
* [Stacks Project, Tag 08P2](https://stacks.math.columbia.edu/tag/08P2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.CategoryHomology

namespace Stacks.ChaoticSite.ModuleValued

universe u

/-! ### Reflecting vanishing along a faithful additive functor -/

/-- A faithful functor preserving zero morphisms reflects zero objects: an object is zero as soon
as its image is. -/
theorem isZero_of_map_isZero {A D : Type*} [Category* A] [Category* D]
    [Preadditive A] [Preadditive D] (F : A ⥤ D) [F.Faithful] [F.PreservesZeroMorphisms]
    {X : A} (h : IsZero (F.obj X)) : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  apply F.map_injective
  rw [F.map_id, F.map_zero]
  exact h.eq_of_src _ _

variable {C : Type u} [SmallCategory C] {B : Type u} [Ring B]

/-- The forgetful functor from `B`-modules to abelian groups. -/
abbrev forgetModules : ModuleCat.{u} B ⥤ AddCommGrpCat.{u} := forget₂ _ _

variable (U : CosimplicialObject C)

/-- The Moore complex of the evaluation of a diagram of `B`-modules on a cosimplicial object: the
complex `ℱ(U_•)`, functorially in `ℱ`. -/
abbrev moduleCosimplicialMooreComplex :
    (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ChainComplex (ModuleCat.{u} B) ℕ :=
  GeneralValued.cosimplicialMooreComplex (ModuleCat.{u} B) U

/-- The Moore complex of the underlying diagram of abelian groups is the Moore complex of the
diagram of modules, read degreewise in abelian groups. -/
theorem cosimplicialMooreComplex_comp_forgetModules (G : Cᵒᵖ ⥤ ModuleCat.{u} B) :
    (cosimplicialMooreComplex U).obj (G ⋙ forgetModules) =
      ((forgetModules (B := B)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((moduleCosimplicialMooreComplex U).obj G) :=
  (congrArg (fun F ↦ F.obj (U.op ⋙ G))
    (AlgebraicTopology.map_alternatingFaceMapComplex (forgetModules (B := B)))).symm

/-- **Vanishing of the homology of `ℱ(U_•)` is detected on underlying abelian groups.** -/
theorem isZero_moduleCosimplicialHomology_of_abelian (G : Cᵒᵖ ⥤ ModuleCat.{u} B) (n : ℕ)
    (h : IsZero (((cosimplicialMooreComplex U).obj (G ⋙ forgetModules)).homology n)) :
    IsZero (((moduleCosimplicialMooreComplex U).obj G).homology n) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff]
  refine (forgetModules (B := B)).reflects_exact_of_faithful _ ?_
  have h' : (((forgetModules (B := B)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj ((moduleCosimplicialMooreComplex U).obj G)).ExactAt n := by
    rw [← cosimplicialMooreComplex_comp_forgetModules,
      HomologicalComplex.exactAt_iff_isZero_homology]
    exact h
  rw [HomologicalComplex.exactAt_iff] at h'
  exact h'

/-! ### Acyclicity of the free diagram of modules on a representable -/

/-- The Moore complex of the simplicial abelian group obtained by applying a functor
`T : Type u ⥤ AddCommGrpCat` to the constant simplicial set on a singleton is the alternating
constant complex on `T(∗)`. -/
def constMooreComplexIso (T : Type u ⥤ AddCommGrpCat.{u}) :
    (alternatingFaceMapComplex AddCommGrpCat.{u}).obj
        (((SimplicialObject.whiskering (Type u) AddCommGrpCat.{u}).obj T).obj
          ((Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1})) ≅
      ChainComplex.alternatingConst.obj (T.obj PUnit.{u + 1}) :=
  (alternatingFaceMapComplex AddCommGrpCat.{u}).mapIso
      (Functor.constComp SimplexCategoryᵒᵖ PUnit.{u + 1} T) ≪≫
    AlgebraicTopology.alternatingFaceMapComplexConst.app (T.obj PUnit.{u + 1})

/-- **The Moore complex of `T(X_•)` for `X_•` homotopy equivalent to a singleton has the homology
of `T(∗)` placed in degree zero**, for every functor `T : Type u ⥤ AddCommGrpCat`. -/
def mooreComplexHomologyIsoOfHomotopyEquiv (T : Type u ⥤ AddCommGrpCat.{u})
    {X : SimplicialObject (Type u)}
    {f : X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1}}
    (hf : SimplicialObject.homotopyEquivalences (Type u) f) (n : ℕ) :
    ((alternatingFaceMapComplex AddCommGrpCat.{u}).obj (X ⋙ T)).homology n ≅
      (ChainComplex.alternatingConst.obj (T.obj PUnit.{u + 1})).homology n := by
  have hg := SimplicialObject.homotopyEquivalences_whiskering_map T hf
  have hq : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (((SimplicialObject.whiskering (Type u) AddCommGrpCat.{u}).obj T).map f)) :=
    homotopyEquivalences_le_quasiIso AddCommGrpCat.{u} (ComplexShape.down ℕ) _
      (AlgebraicTopology.homotopyEquivalences_alternatingFaceMapComplex_map hg)
  have : IsIso (HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
        (((SimplicialObject.whiskering (Type u) AddCommGrpCat.{u}).obj T).map f)) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).mp (hq.quasiIsoAt n)
  exact asIso (HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
        (((SimplicialObject.whiskering (Type u) AddCommGrpCat.{u}).obj T).map f)) n) ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n).mapIso
      (constMooreComplexIso T)

/-- The free diagram of `B`-modules on a representable presheaf, `j_{W!}B_W`: the free `B`-module
on the set of morphisms into `W`. -/
abbrev moduleFreeRepresentablePresheaf (W : C) : Cᵒᵖ ⥤ ModuleCat.{u} B :=
  yoneda.obj W ⋙ ModuleCat.free B

/-- **The underlying abelian diagram of `j_{W!}B_W` is acyclic for `ℱ ↦ ℱ(U_•)` in positive
degrees**, for `U_•` a point resolution. -/
theorem isZero_cosimplicialHomology_moduleFreeRepresentable_succ (hU : IsPointResolution U)
    (W : C) (n : ℕ) :
    IsZero (((cosimplicialMooreComplex U).obj
      (moduleFreeRepresentablePresheaf (B := B) W ⋙ forgetModules)).homology (n + 1)) := by
  refine IsZero.of_iso ?_ (mooreComplexHomologyIsoOfHomotopyEquiv
    (ModuleCat.free B ⋙ forgetModules) (hU W).choose_spec (n + 1))
  exact (ChainComplex.alternatingConst_exactAt
    ((ModuleCat.free B ⋙ forgetModules).obj PUnit.{u + 1}) (n + 1)
    (Nat.succ_ne_zero n)).isZero_homology

/-! ### The canonical presentation by free diagrams on representables -/

/-- The function out of the generators used by
`Stacks.ChaoticSite.ModuleValued.moduleFreeRepresentableHom`: the generator `h : V ⟶ W` is sent to
the restriction of the section along `h`. -/
def moduleFreeRepresentableFun {P : Cᵒᵖ ⥤ ModuleCat.{u} B} (W : C) (s : P.obj (op W))
    (Y : Cᵒᵖ) : (yoneda.obj W).obj Y → (P.obj Y : Type u) :=
  fun h ↦ P.map h.op s

/-- The morphism out of the free diagram of `B`-modules on a representable determined by a
section over the representing object: the generator `h : V ⟶ W` is sent to the restriction of
the section along `h`. -/
def moduleFreeRepresentableHom {P : Cᵒᵖ ⥤ ModuleCat.{u} B} (W : C) (s : P.obj (op W)) :
    moduleFreeRepresentablePresheaf (B := B) W ⟶ P where
  app Y := ModuleCat.freeDesc (↾moduleFreeRepresentableFun W s Y)
  naturality Y Z f := by
    apply ModuleCat.free_hom_ext
    intro g
    have hL : ((moduleFreeRepresentablePresheaf (B := B) W).map f ≫
        ModuleCat.freeDesc (↾moduleFreeRepresentableFun W s Z)) (ModuleCat.freeMk g) =
        P.map (f.unop ≫ g).op s := by
      rw [ConcreteCategory.comp_apply]
      change ModuleCat.freeDesc (↾moduleFreeRepresentableFun W s Z)
          ((ModuleCat.free B).map ((yoneda.obj W).map f) (ModuleCat.freeMk g)) = _
      rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply]
      rfl
    have hR : (ModuleCat.freeDesc (↾moduleFreeRepresentableFun W s Y) ≫ P.map f)
        (ModuleCat.freeMk g) = P.map f (P.map g.op s) := by
      rw [ConcreteCategory.comp_apply, ModuleCat.freeDesc_apply]
      rfl
    rw [hL, hR, show (f.unop ≫ g).op = g.op ≫ f from rfl, P.map_comp]
    rfl

/-- The value of `Stacks.ChaoticSite.ModuleValued.moduleFreeRepresentableHom` on the generator
`𝟙 W`: it is the given section. -/
lemma moduleFreeRepresentableHom_id {P : Cᵒᵖ ⥤ ModuleCat.{u} B} (W : C) (s : P.obj (op W)) :
    (moduleFreeRepresentableHom W s).app (op W) (ModuleCat.freeMk (𝟙 W)) = s := by
  change ModuleCat.freeDesc (↾moduleFreeRepresentableFun W s (op W)) (ModuleCat.freeMk (𝟙 W)) = s
  rw [ModuleCat.freeDesc_apply]
  change (P.map (𝟙 (op W))) s = s
  rw [P.map_id]
  rfl

section DirectSum

open scoped DirectSum

variable {ι : Type u} [DecidableEq ι] (F : ι → (Cᵒᵖ ⥤ ModuleCat.{u} B))

/-- The sectionwise direct sum of a family of diagrams of `B`-modules, a coproduct of the
family. -/
@[sga "3 I 3.1.1" "partial"]
def moduleDirectSumPresheaf : Cᵒᵖ ⥤ ModuleCat.{u} B where
  obj Y := ModuleCat.of B (⨁ i, ((F i).obj Y : Type u))
  map {Y Z} f := ModuleCat.ofHom (DirectSum.toModule B ι (⨁ i, ((F i).obj Z : Type u))
    fun i ↦ (DirectSum.lof B ι (fun j ↦ ((F j).obj Z : Type u)) i).comp ((F i).map f).hom)
  map_id Y := by
    apply ModuleCat.hom_ext
    refine DirectSum.linearMap_ext B fun i ↦ LinearMap.ext fun x ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      DirectSum.toModule_lof, LinearMap.comp_apply, (F i).map_id]
    rfl
  map_comp {Y Z T} f g := by
    apply ModuleCat.hom_ext
    refine DirectSum.linearMap_ext B fun i ↦ LinearMap.ext fun x ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      DirectSum.toModule_lof, LinearMap.comp_apply, (F i).map_comp]
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      DirectSum.toModule_lof]

/-- The restriction maps of the sectionwise direct sum, as a simplification rule. -/
@[simp]
lemma moduleDirectSumPresheaf_map {Y Z : Cᵒᵖ} (f : Y ⟶ Z) :
    (moduleDirectSumPresheaf F).map f = ModuleCat.ofHom
      (DirectSum.toModule B ι (⨁ i, ((F i).obj Z : Type u))
        fun i ↦ (DirectSum.lof B ι (fun j ↦ ((F j).obj Z : Type u)) i).comp ((F i).map f).hom) :=
  rfl

/-- The inclusion of the `i`th summand into the sectionwise direct sum. -/
def moduleDirectSumPresheafIncl (i : ι) : F i ⟶ moduleDirectSumPresheaf F where
  app Y := ModuleCat.ofHom (DirectSum.lof B ι (fun j ↦ ((F j).obj Y : Type u)) i)
  naturality Y Z f := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun x ↦ ?_
    change DirectSum.lof B ι (fun j ↦ ((F j).obj Z : Type u)) i (((F i).map f) x) =
      DirectSum.toModule B ι (⨁ j, ((F j).obj Z : Type u))
        (fun j ↦ (DirectSum.lof B ι (fun k ↦ ((F k).obj Z : Type u)) j).comp
          ((F j).map f).hom) (DirectSum.lof B ι (fun j ↦ ((F j).obj Y : Type u)) i x)
    rw [DirectSum.toModule_lof]
    rfl

/-- The morphism out of a sectionwise direct sum determined by a family of morphisms out of its
summands. -/
def moduleDirectSumPresheafDesc {G : Cᵒᵖ ⥤ ModuleCat.{u} B} (η : ∀ i, F i ⟶ G) :
    moduleDirectSumPresheaf F ⟶ G where
  app Y := ModuleCat.ofHom (DirectSum.toModule B ι (G.obj Y) fun i ↦ ((η i).app Y).hom)
  naturality Y Z f := by
    apply ModuleCat.hom_ext
    refine DirectSum.linearMap_ext B fun i ↦ LinearMap.ext fun x ↦ ?_
    change DirectSum.toModule B ι (G.obj Z) (fun j ↦ ((η j).app Z).hom)
        (DirectSum.toModule B ι (⨁ j, ((F j).obj Z : Type u))
          (fun j ↦ (DirectSum.lof B ι (fun k ↦ ((F k).obj Z : Type u)) j).comp
            ((F j).map f).hom) (DirectSum.lof B ι (fun j ↦ ((F j).obj Y : Type u)) i x)) =
      G.map f (DirectSum.toModule B ι (G.obj Y) (fun j ↦ ((η j).app Y).hom)
        (DirectSum.lof B ι (fun j ↦ ((F j).obj Y : Type u)) i x))
    rw [DirectSum.toModule_lof, LinearMap.comp_apply, DirectSum.toModule_lof,
      DirectSum.toModule_lof]
    exact congrFun (congrArg (fun k : (F i).obj Y ⟶ G.obj Z ↦ (k.hom : _ → _))
      ((η i).naturality f)) x

/-- The value of `Stacks.ChaoticSite.ModuleValued.moduleDirectSumPresheafDesc` on the `i`th
summand. -/
lemma moduleDirectSumPresheafDesc_app_lof {G : Cᵒᵖ ⥤ ModuleCat.{u} B} (η : ∀ i, F i ⟶ G)
    (i : ι) (Y : Cᵒᵖ) (x : (F i).obj Y) :
    (moduleDirectSumPresheafDesc F η).app Y
        (DirectSum.lof B ι (fun j ↦ ((F j).obj Y : Type u)) i x) = (η i).app Y x := by
  change DirectSum.toModule B ι (G.obj Y) (fun j ↦ ((η j).app Y).hom)
      (DirectSum.lof B ι (fun j ↦ ((F j).obj Y : Type u)) i x) = _
  rw [DirectSum.toModule_lof]

/-- `Stacks.ChaoticSite.ModuleValued.moduleDirectSumPresheafDesc` is an epimorphism as soon as
every section of the target is the image of a section of some summand. -/
theorem epi_moduleDirectSumPresheafDesc {G : Cᵒᵖ ⥤ ModuleCat.{u} B} (η : ∀ i, F i ⟶ G)
    (h : ∀ (Y : Cᵒᵖ) (s : (G.obj Y : Type u)), ∃ (i : ι) (x : ((F i).obj Y : Type u)),
      (η i).app Y x = s) :
    Epi (moduleDirectSumPresheafDesc F η) := by
  have happ : ∀ Y : Cᵒᵖ, Epi ((moduleDirectSumPresheafDesc F η).app Y) := by
    intro Y
    rw [ModuleCat.epi_iff_surjective]
    intro s
    obtain ⟨i, x, hx⟩ := h Y s
    exact ⟨DirectSum.lof B ι (fun j ↦ ((F j).obj Y : Type u)) i x,
      (moduleDirectSumPresheafDesc_app_lof F η i Y x).trans hx⟩
  exact NatTrans.epi_of_epi_app _

end DirectSum

/-! ### Positive-degree vanishing on projective diagrams of modules -/

section Vanishing

open scoped DirectSum

variable {ι : Type u} [DecidableEq ι] (F : ι → (Cᵒᵖ ⥤ ModuleCat.{u} B))

/-- In each degree the Moore complex of the underlying abelian diagram of `(⊕ᵢ ℱᵢ)(U_•)` is the
direct sum of the Moore complexes of the `ℱᵢ(U_•)`. -/
def moduleMooreComplexDirectSumEquiv (p : ℕ) :
    (⨁ i, (((cosimplicialMooreComplex U).obj (F i ⋙ forgetModules)).X p : Type u)) ≃+
      (((cosimplicialMooreComplex U).obj
        (moduleDirectSumPresheaf F ⋙ forgetModules)).X p : Type u) :=
  AddEquiv.refl _

/-- The comparison of `Stacks.ChaoticSite.ModuleValued.moduleMooreComplexDirectSumEquiv` is
compatible with the differentials. -/
lemma moduleMooreComplexDirectSumEquiv_ladder (p q : ℕ) :
    AddMonoidHom.comp (((cosimplicialMooreComplex U).obj
          (moduleDirectSumPresheaf F ⋙ forgetModules)).d p q).hom
        (moduleMooreComplexDirectSumEquiv U F p).toAddMonoidHom =
      AddMonoidHom.comp (moduleMooreComplexDirectSumEquiv U F q).toAddMonoidHom
        (DirectSum.map fun i ↦
          (((cosimplicialMooreComplex U).obj (F i ⋙ forgetModules)).d p q).hom) := by
  refine DirectSum.addHom_ext fun i y ↦ ?_
  have hcomm := ((cosimplicialMooreComplex U).map
    (Functor.whiskerRight (moduleDirectSumPresheafIncl F i) forgetModules)).comm p q
  have h := ConcreteCategory.congr_hom hcomm y
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, DirectSum.map_of]
  exact h

/-- **Vanishing of the homology of `ℱ(U_•)` in a fixed positive degree passes to sectionwise direct
sums of diagrams of modules**, read on the underlying abelian diagrams. -/
theorem isZero_cosimplicialHomology_moduleDirectSum_succ (n : ℕ)
    (h : ∀ i, IsZero (((cosimplicialMooreComplex U).obj
      (F i ⋙ forgetModules)).homology (n + 1))) :
    IsZero (((cosimplicialMooreComplex U).obj
      (moduleDirectSumPresheaf F ⋙ forgetModules)).homology (n + 1)) := by
  have key : ∀ K : ChainComplex AddCommGrpCat.{u} ℕ, IsZero (K.homology (n + 1)) ↔
      Function.Exact (K.d (n + 2) (n + 1)).hom (K.d (n + 1) n).hom := fun K ↦ by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology,
      HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (ChainComplex.prev ℕ (n + 1))
        (ChainComplex.next_nat_succ n),
      ShortComplex.ab_exact_iff_function_exact]
    exact Iff.rfl
  rw [key]
  refine Function.Exact.of_ladder_addEquiv_of_exact
    (moduleMooreComplexDirectSumEquiv U F (n + 2))
    (moduleMooreComplexDirectSumEquiv U F (n + 1))
    (moduleMooreComplexDirectSumEquiv U F n)
    (moduleMooreComplexDirectSumEquiv_ladder U F (n + 2) (n + 1))
    (moduleMooreComplexDirectSumEquiv_ladder U F (n + 1) n) ?_
  exact directSum_exact _ _ fun i ↦ (key _).1 (h i)

end Vanishing

/-- **The homology of `ℱ(U_•)` vanishes in positive degrees on every projective diagram of
`B`-modules**, for `U_•` a point resolution. -/
theorem isZero_moduleCosimplicialHomology_projective_succ (hU : IsPointResolution U) (n : ℕ)
    (P : Cᵒᵖ ⥤ ModuleCat.{u} B) [Projective P] :
    IsZero (((moduleCosimplicialMooreComplex U).obj P).homology (n + 1)) := by
  classical
  refine isZero_moduleCosimplicialHomology_of_abelian U P (n + 1) ?_
  set J : Type u := Σ W : C, ((P.obj (op W) : Type u)) with hJ
  set F : J → (Cᵒᵖ ⥤ ModuleCat.{u} B) :=
    fun j ↦ moduleFreeRepresentablePresheaf (B := B) j.1 with hF
  set q : moduleDirectSumPresheaf F ⟶ P :=
    moduleDirectSumPresheafDesc F (fun j ↦ moduleFreeRepresentableHom j.1 j.2) with hqdef
  have hq : Epi q := epi_moduleDirectSumPresheafDesc F _ fun Y s ↦
    ⟨⟨Y.unop, s⟩, ModuleCat.freeMk (𝟙 Y.unop), moduleFreeRepresentableHom_id Y.unop s⟩
  refine isZero_cosimplicialHomology_of_retract U
    (Functor.whiskerRight (Projective.factorThru (𝟙 P) q) forgetModules)
    (Functor.whiskerRight q forgetModules) ?_ (n + 1) ?_
  · rw [← Functor.whiskerRight_comp, Projective.factorThru_comp,
      Functor.whiskerRight_id']
  · exact isZero_cosimplicialHomology_moduleDirectSum_succ U F n fun j ↦
      isZero_cosimplicialHomology_moduleFreeRepresentable_succ U hU j.1 n

/-! ### The degree-zero identification `H₀(ℱ(U_•)) = colim ℱ` -/

/-- The degree-one differential of the Moore complex of `ℱ(U_•)` is the difference of the two
cofaces `U_0 ⟶ U_1`. -/
lemma moduleCosimplicialMooreComplex_obj_d_one_zero (G : Cᵒᵖ ⥤ ModuleCat.{u} B) :
    ((moduleCosimplicialMooreComplex U).obj G).d 1 0 =
      G.map (U.map (SimplexCategory.δ (0 : Fin 2))).op -
        G.map (U.map (SimplexCategory.δ (1 : Fin 2))).op :=
  GeneralValued.cosimplicialMooreComplex_obj_d_one_zero U G

/-- **Any two morphisms `U_0 ⟶ W` restrict identically into a map killing the degree-one
differential of `ℱ(U_•)`**, for a diagram of `B`-modules `ℱ`. -/
theorem module_map_op_comp_eq_of_isPointResolution (hU : IsPointResolution U)
    (G : Cᵒᵖ ⥤ ModuleCat.{u} B) {T : ModuleCat.{u} B}
    (h : G.obj (op (U.obj (SimplexCategory.mk 0))) ⟶ T)
    (hh : ((moduleCosimplicialMooreComplex U).obj G).d 1 0 ≫ h = 0) {W : C}
    (g g' : U.obj (SimplexCategory.mk 0) ⟶ W) :
    G.map g.op ≫ h = G.map g'.op ≫ h := by
  apply (forgetModules (B := B)).map_injective
  have hd : ((cosimplicialMooreComplex U).obj (G ⋙ forgetModules)).d 1 0 ≫
      (forgetModules (B := B)).map h = 0 := by
    rw [cosimplicialMooreComplex_obj_d_one_zero]
    have hdiff : (G ⋙ forgetModules (B := B)).map (U.map (SimplexCategory.δ (0 : Fin 2))).op -
        (G ⋙ forgetModules (B := B)).map (U.map (SimplexCategory.δ (1 : Fin 2))).op =
        (forgetModules (B := B)).map
          (((moduleCosimplicialMooreComplex U).obj G).d 1 0) := by
      rw [moduleCosimplicialMooreComplex_obj_d_one_zero, Functor.map_sub]
      rfl
    rw [hdiff, ← Functor.map_comp, hh, Functor.map_zero]
  have key := map_op_comp_eq_of_isPointResolution U hU (G ⋙ forgetModules)
    ((forgetModules (B := B)).map h) hd g g'
  rw [Functor.map_comp, Functor.map_comp]
  exact key

/-- **The colimit injection at `U_0` kills the degree-one differential**: the two cofaces become
equal after composing with the injections of the colimit over `Cᵒᵖ`. -/
theorem module_d_one_zero_comp_colimitι (G : Cᵒᵖ ⥤ ModuleCat.{u} B) :
    ((moduleCosimplicialMooreComplex U).obj G).d 1 0 ≫
        colimit.ι G (op (U.obj (SimplexCategory.mk 0))) = 0 :=
  GeneralValued.d_one_zero_comp_colimitι U G

/-- The cocone on `ℱ` attached to a map out of `ℱ(U_0)` killing the degree-one differential: over
`V` it is the restriction along a chosen morphism `U_0 ⟶ V`, which that relation makes
independent of the choice. -/
def moduleColimitιCocone (hU : IsPointResolution U) (G : Cᵒᵖ ⥤ ModuleCat.{u} B)
    {T : ModuleCat.{u} B} (h : G.obj (op (U.obj (SimplexCategory.mk 0))) ⟶ T)
    (hh : ((moduleCosimplicialMooreComplex U).obj G).d 1 0 ≫ h = 0) : Cocone G where
  pt := T
  ι :=
    { app Y := G.map (pointResolutionHom U hU Y.unop).op ≫ h
      naturality Y Y' φ := by
        change G.map φ ≫ G.map (pointResolutionHom U hU Y'.unop).op ≫ h =
          (G.map (pointResolutionHom U hU Y.unop).op ≫ h) ≫ 𝟙 T
        rw [Category.comp_id, ← Category.assoc, ← G.map_comp,
          show φ ≫ (pointResolutionHom U hU Y'.unop).op =
            (pointResolutionHom U hU Y'.unop ≫ φ.unop).op from rfl]
        exact module_map_op_comp_eq_of_isPointResolution U hU G h hh _ _ }

/-- **The colimit injection at `U_0` is a cokernel of the degree-one differential of `ℱ(U_•)`**,
for a diagram of `B`-modules `ℱ`. -/
def moduleColimitι_isColimit (hU : IsPointResolution U) (G : Cᵒᵖ ⥤ ModuleCat.{u} B) :
    IsColimit (CokernelCofork.ofπ (colimit.ι G (op (U.obj (SimplexCategory.mk 0))))
      (module_d_one_zero_comp_colimitι U G)) :=
  Cofork.IsColimit.mk _
    (fun S ↦ colimit.desc G (moduleColimitιCocone U hU G S.π (CokernelCofork.condition S)))
    (fun S ↦ by
      refine (colimit.ι_desc _ _).trans ?_
      refine (module_map_op_comp_eq_of_isPointResolution U hU G S.π
        (CokernelCofork.condition S)
        (pointResolutionHom U hU (U.obj (SimplexCategory.mk 0))) (𝟙 _)).trans ?_
      simp)
    (fun S m hm ↦ by
      have key : ∀ m' : colimit G ⟶ S.pt,
          colimit.ι G (op (U.obj (SimplexCategory.mk 0))) ≫ m' = S.π →
            m' = colimit.desc G
              (moduleColimitιCocone U hU G S.π (CokernelCofork.condition S)) := by
        intro m' hm'
        refine colimit.hom_ext fun Y ↦ ?_
        refine Eq.trans ?_
          (colimit.ι_desc (moduleColimitιCocone U hU G S.π (CokernelCofork.condition S)) Y).symm
        rw [← colimit.w G (pointResolutionHom U hU Y.unop).op, Category.assoc, hm']
        rfl
      exact key m hm)

/-- **`H₀(ℱ(U_•)) = colim_{Cᵒᵖ}ℱ`, at the level of degree-zero opcycles**, for a diagram of
`B`-modules. -/
def moduleCosimplicialOpcyclesZeroIsoColim (hU : IsPointResolution U)
    (G : Cᵒᵖ ⥤ ModuleCat.{u} B) :
    ((moduleCosimplicialMooreComplex U).obj G).opcycles 0 ≅ colimit G :=
  IsColimit.coconePointUniqueUpToIso
    (HomologicalComplex.opcyclesIsCokernel ((moduleCosimplicialMooreComplex U).obj G) 1 0
      (by simp))
    (moduleColimitι_isColimit U hU G)

/-- `Stacks.ChaoticSite.ModuleValued.moduleCosimplicialOpcyclesZeroIsoColim` is compatible with
the colimit injection at `U_0`. -/
lemma pOpcycles_comp_moduleCosimplicialOpcyclesZeroIsoColim (hU : IsPointResolution U)
    (G : Cᵒᵖ ⥤ ModuleCat.{u} B) :
    ((moduleCosimplicialMooreComplex U).obj G).pOpcycles 0 ≫
        (moduleCosimplicialOpcyclesZeroIsoColim U hU G).hom =
      colimit.ι G (op (U.obj (SimplexCategory.mk 0))) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (HomologicalComplex.opcyclesIsCokernel ((moduleCosimplicialMooreComplex U).obj G) 1 0
      (by simp))
    (moduleColimitι_isColimit U hU G) WalkingParallelPair.one

/-- **`H₀(ℱ(U_•)) = colim_{Cᵒᵖ}ℱ`** for a diagram of `B`-modules, the comparison being induced by
the colimit injection at `U_0`. -/
def moduleCosimplicialHomologyZeroIsoColim (hU : IsPointResolution U)
    (G : Cᵒᵖ ⥤ ModuleCat.{u} B) :
    ((moduleCosimplicialMooreComplex U).obj G).homology 0 ≅ colimit G :=
  ChainComplex.isoHomologyι₀ ((moduleCosimplicialMooreComplex U).obj G) ≪≫
    moduleCosimplicialOpcyclesZeroIsoColim U hU G

/-- `Stacks.ChaoticSite.ModuleValued.moduleCosimplicialHomologyZeroIsoColim` is natural in the
diagram of `B`-modules. -/
lemma moduleCosimplicialHomologyZeroIsoColim_naturality (hU : IsPointResolution U)
    {G G' : Cᵒᵖ ⥤ ModuleCat.{u} B} (α : G ⟶ G') :
    HomologicalComplex.homologyMap ((moduleCosimplicialMooreComplex U).map α) 0 ≫
        (moduleCosimplicialHomologyZeroIsoColim U hU G').hom =
      (moduleCosimplicialHomologyZeroIsoColim U hU G).hom ≫
        (colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).map α := by
  have hop : HomologicalComplex.opcyclesMap ((moduleCosimplicialMooreComplex U).map α) 0 ≫
      (moduleCosimplicialOpcyclesZeroIsoColim U hU G').hom =
        (moduleCosimplicialOpcyclesZeroIsoColim U hU G).hom ≫
          (colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).map α := by
    rw [← cancel_epi (((moduleCosimplicialMooreComplex U).obj G).pOpcycles 0),
      HomologicalComplex.p_opcyclesMap_assoc,
      pOpcycles_comp_moduleCosimplicialOpcyclesZeroIsoColim, ← Category.assoc,
      pOpcycles_comp_moduleCosimplicialOpcyclesZeroIsoColim]
    exact (colimit.ι_map α (op (U.obj (SimplexCategory.mk 0)))).symm
  have hhom : HomologicalComplex.homologyMap ((moduleCosimplicialMooreComplex U).map α) 0 ≫
      (ChainComplex.isoHomologyι₀ ((moduleCosimplicialMooreComplex U).obj G')).hom =
        (ChainComplex.isoHomologyι₀ ((moduleCosimplicialMooreComplex U).obj G)).hom ≫
          HomologicalComplex.opcyclesMap ((moduleCosimplicialMooreComplex U).map α) 0 := by
    rw [← cancel_epi
        (ChainComplex.isoHomologyι₀ ((moduleCosimplicialMooreComplex U).obj G)).inv,
      Iso.inv_hom_id_assoc, ChainComplex.isoHomologyι₀_inv_naturality_assoc, Iso.inv_hom_id,
      Category.comp_id]
  rw [moduleCosimplicialHomologyZeroIsoColim, moduleCosimplicialHomologyZeroIsoColim,
    Iso.trans_hom, Iso.trans_hom, ← Category.assoc, hhom]
  simp only [Category.assoc]
  rw [hop]

/-! ### Tag 08Q9 for a diagram of modules -/

/-- **Evaluation on a cosimplicial object followed by the Moore complex is an exact functor of the
diagram of `B`-modules.** -/
theorem moduleCosimplicialMooreComplex_map_shortExact
    {S : ShortComplex (Cᵒᵖ ⥤ ModuleCat.{u} B)} (hS : S.ShortExact) :
    (S.map (moduleCosimplicialMooreComplex U)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    hS.map_of_exact
      ((evaluation Cᵒᵖ (ModuleCat.{u} B)).obj (op (Functor.obj U (SimplexCategory.mk n))))

/-- **The homology of `ℱ(U_•)` as a homological δ-functor** in the diagram of `B`-modules `ℱ`,
with the connecting morphisms of the long exact homology sequence. -/
def moduleCosimplicialHomologyDeltaFunctor :
    HomologicalDeltaFunctor (Cᵒᵖ ⥤ ModuleCat.{u} B) (ModuleCat.{u} B) :=
  HomologicalDeltaFunctor.ofChainComplexFunctor (moduleCosimplicialMooreComplex U)
    fun hS ↦ moduleCosimplicialMooreComplex_map_shortExact U hS

/-- The degree-`n` functor of
`Stacks.ChaoticSite.ModuleValued.moduleCosimplicialHomologyDeltaFunctor` is the homology of
`ℱ(U_•)` in degree `n`. -/
lemma moduleCosimplicialHomologyDeltaFunctor_functor (n : ℕ) :
    (moduleCosimplicialHomologyDeltaFunctor U).functor n =
      moduleCosimplicialMooreComplex U ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ) n :=
  rfl

/-- **`H₀(ℱ(U_•)) = colim_{Cᵒᵖ}ℱ`, naturally in the diagram of `B`-modules `ℱ`**, by the
canonical comparison. -/
def moduleCosimplicialHomologyZeroNatIsoColim (hU : IsPointResolution U) :
    (moduleCosimplicialHomologyDeltaFunctor U).functor 0 ≅
      (colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B) :=
  NatIso.ofComponents (fun G ↦ moduleCosimplicialHomologyZeroIsoColim U hU G)
    fun α ↦ moduleCosimplicialHomologyZeroIsoColim_naturality U hU α

/-- The left derived functors of `colim_{Cᵒᵖ}` on diagrams of `B`-modules, as a homological
δ-functor. -/
abbrev moduleDerivedColimitDeltaFunctor :
    HomologicalDeltaFunctor (Cᵒᵖ ⥤ ModuleCat.{u} B) (ModuleCat.{u} B) :=
  (colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ _).leftDerivedHomologicalDeltaFunctor

/-- **The left derived functors of `colim` on diagrams of `B`-modules form a universal homological
δ-functor.** -/
theorem moduleDerivedColimitDeltaFunctor_isUniversal :
    (moduleDerivedColimitDeltaFunctor.{u} (C := C) (B := B)).IsUniversal :=
  HomologicalDeltaFunctor.isUniversal_of_isZero_projective _
    fun n P _ ↦ Functor.isZero_leftDerived_obj_projective_succ _ n P

/-- Let `U_•` be a cosimplicial object of a small category `C` such that every simplicial set
`Mor_C(U_•, W)` is homotopy equivalent to a singleton, and let `B` be a ring. For every `B̲`-module
`ℱ` on the chaotic site `C` — that is, every diagram of `B`-modules on `Cᵒᵖ` — the homology
`L_nπ_!` of `C` with coefficients `ℱ` is the homology of the Moore complex of `ℱ(U_•)`, naturally
in `ℱ`, as `B`-modules. -/
@[stacks 08Q9 "module half: `Lπ_!(ℱ) = ℱ(U_•)` in `D(B)` functorially in `ℱ` in `Mod(B̲)`, \
  read degreewise as `L_nπ_! = L_n colim` of Tag 08PF and as the Moore complex of the \
  simplicial `B`-module obtained by evaluating `ℱ` on `U_•`"]
def moduleLeftDerivedColimitNatIso (hU : IsPointResolution U) (n : ℕ) :
    (colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived n ≅
      moduleCosimplicialMooreComplex U ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ) n :=
  have _ : (moduleCosimplicialHomologyDeltaFunctor U (B := B)).IsUniversal :=
    HomologicalDeltaFunctor.isUniversal_of_isZero_projective _
      fun m P _ ↦ isZero_moduleCosimplicialHomology_projective_succ U hU m P
  have _ : (moduleDerivedColimitDeltaFunctor (C := C) (B := B)).IsUniversal :=
    moduleDerivedColimitDeltaFunctor_isUniversal
  HomologicalDeltaFunctor.isoApp
    (HomologicalDeltaFunctor.IsUniversal.isoOfIso
      (H := moduleDerivedColimitDeltaFunctor (C := C) (B := B))
      (G := moduleCosimplicialHomologyDeltaFunctor U (B := B))
      ((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerivedZeroIsoSelf ≪≫
        (moduleCosimplicialHomologyZeroNatIsoColim U hU).symm)) n

/-! ### Derived lower shriek along the point morphism, with linear coefficients -/

section PointMorphism

variable (C) (B)

/-- Sheaves of `B`-modules for the chaotic topology have enough projectives. -/
instance moduleTrivialSheafEnoughProjectives :
    EnoughProjectives (Sheaf (GrothendieckTopology.trivial C) (ModuleCat.{u} B)) :=
  Equivalence.enoughProjectives
    (sheafToPresheaf (GrothendieckTopology.trivial C) (ModuleCat.{u} B)).asEquivalence.symm

/-- `π_!` on sheaves of `B`-modules for the chaotic topology on a small category, with the module
sections in the universe of the site. -/
abbrev modulePointLowerShriek :
    Sheaf (GrothendieckTopology.trivial C) (ModuleCat.{u} B) ⥤
      Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) (ModuleCat.{u} B) :=
  (Functor.star C).sheafPullback (ModuleCat.{u} B) (GrothendieckTopology.trivial C)
    (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))

/-- The colimit presentation of lower shriek with linear coefficients is additive. -/
instance moduleColimitLowerShriek_additive :
    (colimitLowerShriek (ModuleCat.{u} B) C).Additive :=
  inferInstanceAs ((sheafToPresheaf (GrothendieckTopology.trivial C) (ModuleCat.{u} B) ⋙
    colim ⋙ Functor.const (Discrete PUnit.{u + 1})ᵒᵖ ⋙
      presheafToSheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
        (ModuleCat.{u} B)).Additive)

/-- `π_!` on sheaves of `B`-modules is additive. -/
instance modulePointLowerShriek_additive : (modulePointLowerShriek C B).Additive :=
  Functor.additive_of_iso (lowerShriekColimitIso (ModuleCat.{u} B) C).symm

/-- **`L_nπ_!(ℱ) = H_n(ℱ(U_•))` for sheaves of `B`-modules on a chaotic site.** Let `U_•` be a
cosimplicial object of a small category `C` such that every simplicial set `Mor_C(U_•, W)` is
homotopy equivalent to a singleton, and let `B` be a ring. Then for every sheaf of `B`-modules `ℱ`
on the chaotic site `C` the sections at the point of `L_nπ_!(ℱ)` are the degree `n` homology of the
Moore complex of the simplicial `B`-module `ℱ(U_•)`, naturally in `ℱ`. -/
def moduleLeftDerivedPointLowerShriekNatIso (U : CosimplicialObject C) (hU : IsPointResolution U)
    (n : ℕ) :
    (modulePointLowerShriek C B).leftDerived n ⋙
        pointSections.{u, u + 1, u} (ModuleCat.{u} B) ≅
      sheafToPresheaf (GrothendieckTopology.trivial C) (ModuleCat.{u} B) ⋙
        moduleCosimplicialMooreComplex U ⋙
          HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ) n :=
  (Functor.leftDerivedCompIso (modulePointLowerShriek C B)
        (pointSections.{u, u + 1, u} (ModuleCat.{u} B)) n).symm ≪≫
    Functor.leftDerivedIsoOfNatIso
      (lowerShriek_pointSections_colimitIso (ModuleCat.{u} B) C) n ≪≫
    Functor.compLeftDerivedIso
      (sheafToPresheaf (GrothendieckTopology.trivial C) (ModuleCat.{u} B)) colim n ≪≫
    Functor.isoWhiskerLeft
      (sheafToPresheaf (GrothendieckTopology.trivial C) (ModuleCat.{u} B))
      (moduleLeftDerivedColimitNatIso U hU n)

end PointMorphism

end Stacks.ChaoticSite.ModuleValued

end
