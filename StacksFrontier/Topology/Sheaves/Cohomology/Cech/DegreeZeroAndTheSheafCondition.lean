module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDegreeZero.Augmentation
import StacksCore.Tactic.StacksAttribute

/-!
# Degree-zero Cech cohomology and the sheaf condition

An abelian presheaf `F` on a topological space is a sheaf exactly when, for every open covering
`V = ⋃ Uᵢ`, the family of restriction maps `F(V) ⟶ ∏ᵢ F(Uᵢ)` induces an isomorphism from `F(V)`
onto the degree-zero cohomology of the Cech complex of the covering. This is Tag 01EG.

The proof identifies the degree-zero part of the Cech complex with
`SheafConditionEqualizerProducts.piOpens` and its degree-one part with `piInters`, and the
differential with the difference of the two restriction maps; under those identifications the
kernel fork of the Cech differential and the equalizer fork of the sheaf condition are the same
fork, so one is a limit exactly when the other is. Being the kernel of the differential is in
turn the same as receiving an isomorphism onto degree-zero homology, which is the form the tag
states.

## Main definitions

* `Stacks.Cohomology.CechDegreeZero.cechDegreeZeroRestriction`: the restriction map from
  sections on the covered open to degree zero of the Cech complex, whose component at
  `i : Fin 1 → ι` is restriction to `U (i 0)`.

## Main results

* `Stacks.Cohomology.CechDegreeZero.isSheaf_iff_existsUnique_cechRestrictionHomologyMap`:
  abelian sheaves are characterized by bijectivity of the canonical map to degree-zero Cech
  cohomology for every open covering.

## Implementation notes

The canonical map is not named; instead it is specified by its composite with the canonical
map from homology into opcycles, which is the family of restriction maps. That records which map
is meant and expresses bijectivity categorically, as `IsIso` in `AddCommGrpCat`, rather than
through the underlying function.

An abelian presheaf is `TopCat.Presheaf AddCommGrpCat X`: the repository has no separate
`AbelianPresheaf` abbreviation, the two clauses of Tag 006K being registered directly against
the Mathlib notions.

## References

* [Stacks Project, Tag 01EG](https://stacks.math.columbia.edu/tag/01EG)
-/

@[expose] public section

universe u

namespace Stacks.Cohomology.CechDegreeZero

open _root_.CategoryTheory Opposite TopologicalSpace

variable {X : TopCat.{u}}

/-- The restriction map from sections on a covered open to degree zero of its
Čech complex. Its component indexed by `i : Fin 1 → ι` is restriction to
the member `U (i 0)` of the cover. -/
public noncomputable def cechDegreeZeroRestriction
    {ι : Type u} (F : TopCat.Presheaf AddCommGrpCat.{u} X) (V : Opens X) (U : ι → Opens X)
    (hU : V = iSup U) :
    F.obj (op V) ⟶ ((CategoryTheory.cechComplexFunctor U).obj F).X 0 :=
  F.map (eqToHom (congrArg op hU)) ≫
    Limits.Pi.lift (fun i ↦ F.map
      ((Limits.Pi.π (fun a : Fin 1 ↦ U (i a)) 0) ≫
        homOfLE (le_iSup U (i 0))).op)

open Stacks.Cohomology.CechZero in
private theorem homologyZeroCriterion
    (K : CochainComplex AddCommGrpCat.{u} ℕ) {A : AddCommGrpCat.{u}}
    (r : A ⟶ K.X 0) (w : r ≫ K.d 0 1 = 0) :
    Nonempty (Limits.IsLimit (Limits.KernelFork.ofι r w)) ↔
      ∃! f : A ⟶ K.homology 0,
        IsIso f ∧ f ≫ K.homologyι 0 = r ≫ K.pOpcycles 0 := by
  constructor
  · rintro ⟨hr⟩
    let e := hr.conePointUniqueUpToIso (homologyZeroKernel K)
    have he : e.hom ≫ (K.isoHomologyπ₀.inv ≫ K.iCycles 0) = r := by
      simpa only [Limits.Fork.app_zero_eq_ι, Limits.KernelFork.ι_ofι] using
        hr.conePointUniqueUpToIso_hom_comp (homologyZeroKernel K)
          Limits.WalkingParallelPair.zero
    have hcomp : e.hom ≫ K.homologyι 0 = r ≫ K.pOpcycles 0 := by
      rw [← homologyZeroKernel_arrow, ← CategoryTheory.Category.assoc, he]
    exact ⟨e.hom, ⟨inferInstance, hcomp⟩,
      fun g hg => (cancel_mono (K.homologyι 0)).mp (hg.2.trans hcomp.symm)⟩
  · rintro ⟨f, ⟨hf, hcomp⟩, _⟩
    have hcomp' : f ≫ (K.isoHomologyπ₀.inv ≫ K.iCycles 0) = r := by
      apply (cancel_mono (K.pOpcycles 0)).mp
      calc
        _ = f ≫ K.homologyι 0 := by
          rw [CategoryTheory.Category.assoc, homologyZeroKernel_arrow]
        _ = _ := hcomp
    exact ⟨Limits.IsKernel.isoKernel (K.d 0 1) r (homologyZeroKernel K)
      (asIso f) hcomp'⟩

private noncomputable def cechZeroIso {ι : Type u} (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) :
    ((CategoryTheory.cechComplexFunctor U).obj F).X 0 ≅
      TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens F U :=
  (Limits.Pi.mapIso (fun i : Fin 1 → ι =>
    F.mapIso ((Limits.productUniqueIso (fun a : Fin 1 => U (i a))).symm.op))) ≪≫
    Limits.Pi.reindex (Equiv.funUnique (Fin 1) ι)
      (fun i => F.obj (op (U i)))

private lemma cechZeroIso_hom_π {ι : Type u} (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) (j : Fin 1 → ι) :
    (cechZeroIso F U).hom ≫ Limits.Pi.π _ (j 0) =
      Limits.Pi.π _ j ≫
        F.map ((Limits.productUniqueIso (fun a : Fin 1 => U (j a))).symm.op).hom := by
  let p : ∀ k : Fin 1 → ι,
      F.obj (op (∏ᶜ fun a : Fin 1 => U (k a))) ≅ F.obj (op (U (k 0))) :=
    fun k => F.mapIso ((Limits.productUniqueIso (fun a : Fin 1 => U (k a))).symm.op)
  exact (Category.assoc (Limits.Pi.mapIso p).hom
      (Limits.Pi.reindex (Equiv.funUnique (Fin 1) ι) (fun i => F.obj (op (U i)))).hom
      (Limits.Pi.π (fun i => F.obj (op (U i))) (j 0))).trans
    ((congrArg (fun t => (Limits.Pi.mapIso p).hom ≫ t)
        (Limits.Pi.reindex_hom_π (Equiv.funUnique (Fin 1) ι)
          (fun i => F.obj (op (U i))) j)).trans
      (Limits.Pi.mapIso_hom_π p j))

private lemma cechPairProduct_eq_inf {ι : Type u} (U : ι → Opens X) (i : Fin 2 → ι) :
    (∏ᶜ fun a : Fin 2 => U (i a)) = U (i 0) ⊓ U (i 1) := by
  apply le_antisymm
  · exact le_inf (leOfHom (Limits.Pi.π _ 0)) (leOfHom (Limits.Pi.π _ 1))
  · refine leOfHom (Limits.Pi.lift (fun a => homOfLE ?_))
    fin_cases a <;> simp

private noncomputable def cechOneIso {ι : Type u} (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) :
    ((CategoryTheory.cechComplexFunctor U).obj F).X 1 ≅
      TopCat.Presheaf.SheafConditionEqualizerProducts.piInters F U :=
  (Limits.Pi.mapIso (fun i : Fin 2 → ι =>
    F.mapIso (eqToIso (congrArg op (cechPairProduct_eq_inf U i))))) ≪≫
    Limits.Pi.reindex (finTwoArrowEquiv ι)
      (fun p => F.obj (op (U p.1 ⊓ U p.2)))

private lemma cechOneIso_hom_π {ι : Type u} (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) (i : Fin 2 → ι) :
    (cechOneIso F U).hom ≫ Limits.Pi.π _ (finTwoArrowEquiv ι i) =
      Limits.Pi.π _ i ≫
        F.map (eqToHom (congrArg op (cechPairProduct_eq_inf U i))) := by
  let p : ∀ k : Fin 2 → ι,
      F.obj (op (∏ᶜ fun a : Fin 2 => U (k a))) ≅ F.obj (op (U (k 0) ⊓ U (k 1))) :=
    fun k => F.mapIso (eqToIso (congrArg op (cechPairProduct_eq_inf U k)))
  exact (Category.assoc (Limits.Pi.mapIso p).hom
      (Limits.Pi.reindex (finTwoArrowEquiv ι)
        (fun q => F.obj (op (U q.1 ⊓ U q.2)))).hom
      (Limits.Pi.π (fun q => F.obj (op (U q.1 ⊓ U q.2))) (finTwoArrowEquiv ι i))).trans
    ((congrArg (fun t => (Limits.Pi.mapIso p).hom ≫ t)
        (Limits.Pi.reindex_hom_π (finTwoArrowEquiv ι)
          (fun q => F.obj (op (U q.1 ⊓ U q.2))) i)).trans
      (Limits.Pi.mapIso_hom_π p i))

/-- The component of the degree-zero Čech augmentation at a tuple: the comparison along the
covering equality, followed by restriction to the intersection. -/
lemma cechDegreeZeroRestriction_π {ι : Type u} (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (V : Opens X) (U : ι → Opens X) (hU : V = iSup U) (j : Fin 1 → ι) :
    cechDegreeZeroRestriction F V U hU ≫ Limits.Pi.π _ j =
      F.map (eqToHom (congrArg op hU)) ≫
        F.map ((Limits.Pi.π (fun a : Fin 1 => U (j a)) 0) ≫
          homOfLE (le_iSup U (j 0))).op := by
  let q : ∀ k : Fin 1 → ι,
      F.obj (op (iSup U)) ⟶ F.obj (op (∏ᶜ fun a : Fin 1 => U (k a))) :=
    fun k => F.map ((Limits.Pi.π (fun a : Fin 1 => U (k a)) 0) ≫ homOfLE (le_iSup U (k 0))).op
  exact (Category.assoc (F.map (eqToHom (congrArg op hU))) (Limits.Pi.lift q)
      (Limits.Pi.π (fun b : Fin 1 → ι => F.obj (op (∏ᶜ fun a : Fin 1 => U (b a)))) j)).trans
    (congrArg (fun t => F.map (eqToHom (congrArg op hU)) ≫ t) (Limits.Pi.lift_comp_π q j))

private lemma cechRestriction_zeroIso {ι : Type u} (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (V : Opens X) (U : ι → Opens X) (hU : V = iSup U) :
    cechDegreeZeroRestriction F V U hU ≫ (cechZeroIso F U).hom =
      F.map (eqToHom (congrArg op hU)) ≫
        TopCat.Presheaf.SheafConditionEqualizerProducts.res F U := by
  apply Limits.Pi.hom_ext
  intro i
  have h0 : (cechZeroIso F U).hom ≫ Limits.Pi.π (fun k => F.obj (op (U k))) i =
      Limits.Pi.π (fun b : Fin 1 → ι => F.obj (op (∏ᶜ fun a : Fin 1 => U (b a))))
          (fun _ : Fin 1 => i) ≫
        F.map ((Limits.productUniqueIso (fun _ : Fin 1 => U i)).symm.op).hom :=
    cechZeroIso_hom_π F U (fun _ : Fin 1 => i)
  have h1 : cechDegreeZeroRestriction F V U hU ≫
        Limits.Pi.π (fun b : Fin 1 → ι => F.obj (op (∏ᶜ fun a : Fin 1 => U (b a))))
          (fun _ : Fin 1 => i) =
      F.map (eqToHom (congrArg op hU)) ≫
        F.map ((Limits.Pi.π (fun _ : Fin 1 => U i) 0) ≫ homOfLE (le_iSup U i)).op :=
    cechDegreeZeroRestriction_π F V U hU (fun _ : Fin 1 => i)
  have h2 : F.map ((Limits.Pi.π (fun _ : Fin 1 => U i) 0) ≫ homOfLE (le_iSup U i)).op ≫
        F.map ((Limits.productUniqueIso (fun _ : Fin 1 => U i)).symm.op).hom =
      F.map (TopologicalSpace.Opens.leSupr U i).op := by
    rw [← F.map_comp]
    congr 1
  calc (cechDegreeZeroRestriction F V U hU ≫ (cechZeroIso F U).hom) ≫
          Limits.Pi.π (fun k => F.obj (op (U k))) i
      = cechDegreeZeroRestriction F V U hU ≫
          ((cechZeroIso F U).hom ≫ Limits.Pi.π (fun k => F.obj (op (U k))) i) :=
        Category.assoc _ _ _
    _ = cechDegreeZeroRestriction F V U hU ≫
          (Limits.Pi.π (fun b : Fin 1 → ι => F.obj (op (∏ᶜ fun a : Fin 1 => U (b a))))
              (fun _ : Fin 1 => i) ≫
            F.map ((Limits.productUniqueIso (fun _ : Fin 1 => U i)).symm.op).hom) :=
        congrArg (fun t => cechDegreeZeroRestriction F V U hU ≫ t) h0
    _ = (cechDegreeZeroRestriction F V U hU ≫
          Limits.Pi.π (fun b : Fin 1 → ι => F.obj (op (∏ᶜ fun a : Fin 1 => U (b a))))
            (fun _ : Fin 1 => i)) ≫
          F.map ((Limits.productUniqueIso (fun _ : Fin 1 => U i)).symm.op).hom :=
        (Category.assoc _ _ _).symm
    _ = (F.map (eqToHom (congrArg op hU)) ≫
          F.map ((Limits.Pi.π (fun _ : Fin 1 => U i) 0) ≫ homOfLE (le_iSup U i)).op) ≫
          F.map ((Limits.productUniqueIso (fun _ : Fin 1 => U i)).symm.op).hom :=
        congrArg (fun t => t ≫
          F.map ((Limits.productUniqueIso (fun _ : Fin 1 => U i)).symm.op).hom) h1
    _ = F.map (eqToHom (congrArg op hU)) ≫
          (F.map ((Limits.Pi.π (fun _ : Fin 1 => U i) 0) ≫ homOfLE (le_iSup U i)).op ≫
            F.map ((Limits.productUniqueIso (fun _ : Fin 1 => U i)).symm.op).hom) :=
        Category.assoc _ _ _
    _ = F.map (eqToHom (congrArg op hU)) ≫
          F.map (TopologicalSpace.Opens.leSupr U i).op :=
        congrArg (fun t => F.map (eqToHom (congrArg op hU)) ≫ t) h2
    _ = F.map (eqToHom (congrArg op hU)) ≫
          (TopCat.Presheaf.SheafConditionEqualizerProducts.res F U ≫
            Limits.Pi.π (fun k => F.obj (op (U k))) i) :=
        (congrArg (fun t => F.map (eqToHom (congrArg op hU)) ≫ t)
          (TopCat.Presheaf.SheafConditionEqualizerProducts.res_π F U i)).symm
    _ = (F.map (eqToHom (congrArg op hU)) ≫
          TopCat.Presheaf.SheafConditionEqualizerProducts.res F U) ≫
          Limits.Pi.π (fun k => F.obj (op (U k))) i :=
        (Category.assoc _ _ _).symm

private lemma cech_d01 {ι : Type u} (F : TopCat.Presheaf AddCommGrpCat.{u} X) (U : ι → Opens X) :
    ((CategoryTheory.cechComplexFunctor U).obj F).d 0 1 =
      ((CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
        (CategoryTheory.Limits.FormalCoproduct.mk _ U).cech).obj F).δ 0 -
      ((CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
        (CategoryTheory.Limits.FormalCoproduct.mk _ U).cech).obj F).δ 1 := by
  show AlgebraicTopology.AlternatingCofaceMapComplex.objD
    ((CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
      (CategoryTheory.Limits.FormalCoproduct.mk _ U).cech).obj F) 0 = _
  simp [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Fin.sum_univ_two]
  abel

private lemma cech_coface_zero_π {ι : Type u} (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) (i : Fin 2 → ι) :
    ((CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
      (CategoryTheory.Limits.FormalCoproduct.mk _ U).cech).obj F).δ 0 ≫
        Limits.Pi.π _ i =
      Limits.Pi.π _ (fun _ : Fin 1 => i 1) ≫
        F.map ((Limits.Pi.lift (fun _ : Fin 1 =>
          Limits.Pi.π (fun a : Fin 2 => U (i a)) 1)).op) := by
  simp only [CategoryTheory.CosimplicialObject.δ,
    CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor,
    CategoryTheory.Limits.FormalCoproduct.evalOp,
    CategoryTheory.Limits.FormalCoproduct.cech,
    CategoryTheory.Limits.FormalCoproduct.mapPower,
    SimplexCategory.δ_zero_eq_const, Nat.reduceAdd, Functor.rightOp_obj, Fin.isValue,
    SimplexCategory.const]
  exact Limits.Pi.lift_comp_π _ i

private lemma cech_coface_one_π {ι : Type u} (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) (i : Fin 2 → ι) :
    ((CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
      (CategoryTheory.Limits.FormalCoproduct.mk _ U).cech).obj F).δ 1 ≫
        Limits.Pi.π _ i =
      Limits.Pi.π _ (fun _ : Fin 1 => i 0) ≫
        F.map ((Limits.Pi.lift (fun _ : Fin 1 =>
          Limits.Pi.π (fun a : Fin 2 => U (i a)) 0)).op) := by
  simp only [CategoryTheory.CosimplicialObject.δ,
    CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor,
    CategoryTheory.Limits.FormalCoproduct.evalOp,
    CategoryTheory.Limits.FormalCoproduct.cech,
    CategoryTheory.Limits.FormalCoproduct.mapPower,
    SimplexCategory.δ_one_eq_const, Nat.reduceAdd, Functor.rightOp_obj, Fin.isValue,
    SimplexCategory.const]
  exact Limits.Pi.lift_comp_π _ i

/-- Transport of a commutative square along a functor, stated on variables so that the two
`CategoryTheory.Functor.map_comp` rewrites never have to be keyed. -/
public lemma map_comp_eq_map_comp {C₁ : Type*} [Category* C₁] {C₂ : Type*} [Category* C₂]
    (T : C₁ ⥤ C₂) {A B A' D : C₁} (a : A ⟶ B) (b : B ⟶ D) (a' : A ⟶ A') (b' : A' ⟶ D)
    (h : a ≫ b = a' ≫ b') : T.map a ≫ T.map b = T.map a' ≫ T.map b' :=
  (T.map_comp a b).symm.trans ((congrArg T.map h).trans (T.map_comp a' b'))

private lemma cechDifferential_component_zero {ι : Type u}
    (F : TopCat.Presheaf AddCommGrpCat.{u} X) (U : ι → Opens X) (i : Fin 2 → ι) :
    ((CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
        (CategoryTheory.Limits.FormalCoproduct.mk _ U).cech).obj F).δ 0 ≫
      (Limits.Pi.π (fun b : Fin 2 → ι => F.obj (op (∏ᶜ fun a : Fin 2 => U (b a)))) i ≫
        F.map (eqToHom (congrArg op (cechPairProduct_eq_inf U i)))) =
    (cechZeroIso F U).hom ≫
      (TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes F U ≫
        Limits.Pi.π (fun q => F.obj (op (U q.1 ⊓ U q.2))) (finTwoArrowEquiv ι i)) := by
  have hres : TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes F U ≫
        Limits.Pi.π (fun q => F.obj (op (U q.1 ⊓ U q.2))) (finTwoArrowEquiv ι i) =
      Limits.Pi.π (fun k => F.obj (op (U k))) (i 1) ≫
        F.map (TopologicalSpace.Opens.infLERight (U (i 0)) (U (i 1))).op :=
    Limits.Pi.lift_comp_π _ (finTwoArrowEquiv ι i)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫
    F.map (eqToHom (congrArg op (cechPairProduct_eq_inf U i))))
    (cech_coface_zero_π F U i)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => Limits.Pi.π
      (fun b : Fin 1 → ι => F.obj (op (∏ᶜ fun a : Fin 1 => U (b a))))
      (fun _ : Fin 1 => i 1) ≫ t)
    (map_comp_eq_map_comp F _ _
      ((Limits.productUniqueIso (fun _ : Fin 1 => U (i 1))).symm.op).hom
      (TopologicalSpace.Opens.infLERight (U (i 0)) (U (i 1))).op
        (Subsingleton.elim _ _))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫
      F.map (TopologicalSpace.Opens.infLERight (U (i 0)) (U (i 1))).op)
    (cechZeroIso_hom_π F U (fun _ : Fin 1 => i 1)).symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun t => (cechZeroIso F U).hom ≫ t) hres.symm

private lemma cechDifferential_component_one {ι : Type u}
    (F : TopCat.Presheaf AddCommGrpCat.{u} X) (U : ι → Opens X) (i : Fin 2 → ι) :
    ((CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
        (CategoryTheory.Limits.FormalCoproduct.mk _ U).cech).obj F).δ 1 ≫
      (Limits.Pi.π (fun b : Fin 2 → ι => F.obj (op (∏ᶜ fun a : Fin 2 => U (b a)))) i ≫
        F.map (eqToHom (congrArg op (cechPairProduct_eq_inf U i)))) =
    (cechZeroIso F U).hom ≫
      (TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes F U ≫
        Limits.Pi.π (fun q => F.obj (op (U q.1 ⊓ U q.2))) (finTwoArrowEquiv ι i)) := by
  have hres : TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes F U ≫
        Limits.Pi.π (fun q => F.obj (op (U q.1 ⊓ U q.2))) (finTwoArrowEquiv ι i) =
      Limits.Pi.π (fun k => F.obj (op (U k))) (i 0) ≫
        F.map (TopologicalSpace.Opens.infLELeft (U (i 0)) (U (i 1))).op :=
    Limits.Pi.lift_comp_π _ (finTwoArrowEquiv ι i)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫
    F.map (eqToHom (congrArg op (cechPairProduct_eq_inf U i))))
    (cech_coface_one_π F U i)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => Limits.Pi.π
      (fun b : Fin 1 → ι => F.obj (op (∏ᶜ fun a : Fin 1 => U (b a))))
      (fun _ : Fin 1 => i 0) ≫ t)
    (map_comp_eq_map_comp F _ _
      ((Limits.productUniqueIso (fun _ : Fin 1 => U (i 0))).symm.op).hom
      (TopologicalSpace.Opens.infLELeft (U (i 0)) (U (i 1))).op
        (Subsingleton.elim _ _))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫
      F.map (TopologicalSpace.Opens.infLELeft (U (i 0)) (U (i 1))).op)
    (cechZeroIso_hom_π F U (fun _ : Fin 1 => i 0)).symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun t => (cechZeroIso F U).hom ≫ t) hres.symm

private lemma cechDifferential_eq {ι : Type u} (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) :
    ((CategoryTheory.cechComplexFunctor U).obj F).d 0 1 ≫ (cechOneIso F U).hom =
      (cechZeroIso F U).hom ≫
        (TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes F U -
          TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes F U) := by
  apply Limits.Pi.hom_ext
  intro p
  obtain ⟨i, rfl⟩ := (finTwoArrowEquiv ι).surjective p
  refine (Category.assoc (((CategoryTheory.cechComplexFunctor U).obj F).d 0 1)
      (cechOneIso F U).hom
      (Limits.Pi.π (fun q => F.obj (op (U q.1 ⊓ U q.2))) (finTwoArrowEquiv ι i))).trans ?_
  refine Eq.trans ?_ (Category.assoc (cechZeroIso F U).hom
      (TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes F U -
        TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes F U)
      (Limits.Pi.π (fun q => F.obj (op (U q.1 ⊓ U q.2))) (finTwoArrowEquiv ι i))).symm
  rw [cechOneIso_hom_π F U i, cech_d01 F U]
  refine (Preadditive.sub_comp _ _ _).trans ?_
  refine Eq.trans ?_ ((congrArg (fun t => (cechZeroIso F U).hom ≫ t)
    (Preadditive.sub_comp _ _ _)).trans (Preadditive.comp_sub _ _ _)).symm
  congr 1
  · exact cechDifferential_component_zero F U i
  · exact cechDifferential_component_one F U i

private theorem isLimit_kernelFork_iff_ofIso
    {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {A B A' B' P P' : C} {d : A ⟶ B} {d' : A' ⟶ B'}
    {r : P ⟶ A} {r' : P' ⟶ A'} (w : r ≫ d = 0) (w' : r' ≫ d' = 0)
    (eA : A ≅ A') (eB : B ≅ B') (eP : P ≅ P')
    (hd : eA.hom ≫ d' = d ≫ eB.hom)
    (hr : eP.hom ≫ r' = r ≫ eA.hom) :
    Nonempty (Limits.IsLimit (Limits.KernelFork.ofι r w)) ↔
      Nonempty (Limits.IsLimit (Limits.KernelFork.ofι r' w')) := by
  refine ⟨(fun ⟨h⟩ => ⟨Limits.IsKernel.ofIso d h _ eA eB eP hd hr⟩), ?_⟩
  rintro ⟨h⟩
  have hd' : eA.inv ≫ d = d' ≫ eB.inv := by
    rw [← cancel_mono eB.hom]
    simp [← hd, Category.assoc]
  have hr' : eP.inv ≫ r = r' ≫ eA.inv := by
    rw [← cancel_mono eA.hom]
    simp [← hr, Category.assoc]
  exact ⟨Limits.IsKernel.ofIso d' h _ eA.symm eB.symm eP.symm hd' hr'⟩

private lemma cechRestriction_d_zero {ι : Type u} (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (V : Opens X) (U : ι → Opens X) (hU : V = iSup U) :
    cechDegreeZeroRestriction F V U hU ≫
      ((CategoryTheory.cechComplexFunctor U).obj F).d 0 1 = 0 := by
  apply (cancel_mono (cechOneIso F U).hom).mp
  rw [Category.assoc, cechDifferential_eq, ← Category.assoc,
    cechRestriction_zeroIso]
  rw [Category.assoc, Preadditive.comp_sub]
  rw [TopCat.Presheaf.SheafConditionEqualizerProducts.w]
  simp

private theorem cechKernel_iff_sheafFork {ι : Type u} (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (V : Opens X) (U : ι → Opens X) (hU : V = iSup U) :
    Nonempty (Limits.IsLimit (Limits.KernelFork.ofι
      (cechDegreeZeroRestriction F V U hU) (cechRestriction_d_zero F V U hU))) ↔
      Nonempty (Limits.IsLimit
        (TopCat.Presheaf.SheafConditionEqualizerProducts.fork F U)) := by
  let K := (CategoryTheory.cechComplexFunctor U).obj F
  let S := TopCat.Presheaf.SheafConditionEqualizerProducts.fork F U
  let eV := F.mapIso (eqToIso (congrArg op hU))
  have hd : (cechZeroIso F U).hom ≫
      (TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes F U -
        TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes F U) =
      K.d 0 1 ≫ (-cechOneIso F U).hom := by
    rw [Preadditive.neg_iso_hom, Preadditive.comp_neg,
      cechDifferential_eq, Preadditive.comp_sub]
    simp only [Preadditive.comp_sub]
    abel
  have hr : eV.hom ≫ S.ι =
      cechDegreeZeroRestriction F V U hU ≫ (cechZeroIso F U).hom :=
    (cechRestriction_zeroIso F V U hU).symm
  have hTransport := isLimit_kernelFork_iff_ofIso
    (cechRestriction_d_zero F V U hU)
    (show S.ι ≫
      (TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes F U -
        TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes F U) = 0 by
      rw [Preadditive.comp_sub, sub_eq_zero, S.condition])
    (cechZeroIso F U) (-cechOneIso F U) eV hd hr
  exact ⟨fun h => ⟨Preadditive.isLimitForkOfKernelFork (hTransport.mp h).some⟩,
    fun h => hTransport.mpr ⟨Preadditive.isLimitKernelForkOfFork h.some⟩⟩


/-- An abelian presheaf is a sheaf if and only if, for every open covering, the
canonical restriction-induced map from sections on the covered open to zeroth
Čech cohomology is an isomorphism. -/
@[stacks 01EG]
public theorem isSheaf_iff_existsUnique_cechRestrictionHomologyMap
    (F : TopCat.Presheaf AddCommGrpCat.{u} X) :
    F.IsSheaf ↔
      ∀ (ι : Type u) (V : Opens X) (U : ι → Opens X) (hU : V = iSup U),
        ∃! f : F.obj (op V) ⟶
            ((CategoryTheory.cechComplexFunctor U).obj F).homology 0,
          IsIso f ∧
            f ≫ ((CategoryTheory.cechComplexFunctor U).obj F).homologyι 0 =
              cechDegreeZeroRestriction F V U hU ≫
                ((CategoryTheory.cechComplexFunctor U).obj F).pOpcycles 0 := by
  constructor
  · intro h ι V U hU
    exact (homologyZeroCriterion ((CategoryTheory.cechComplexFunctor U).obj F)
      (cechDegreeZeroRestriction F V U hU)
      (cechRestriction_d_zero F V U hU)).mp
      ((cechKernel_iff_sheafFork F V U hU).mpr
        (((TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts F).mp h) U))
  · intro h
    exact (TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts F).mpr fun ι U =>
      (cechKernel_iff_sheafFork F (iSup U) U rfl).mp
        ((homologyZeroCriterion ((CategoryTheory.cechComplexFunctor U).obj F)
          (cechDegreeZeroRestriction F (iSup U) U rfl)
          (cechRestriction_d_zero F (iSup U) U rfl)).mpr
          (h ι (iSup U) U rfl))

end Stacks.Cohomology.CechDegreeZero
