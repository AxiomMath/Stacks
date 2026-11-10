module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.RingTheory.Finiteness.Projective
import StacksCore.Tactic.StacksAttribute

/-!
# Modules on a space which are summands of a finite free module

Let `X` be a topological space and `𝒪` a sheaf of rings on `X`. A sheaf of `𝒪`-modules is a
*direct summand of a finite free module* when it is a retract of a finite direct sum
`𝒪 ⊕ ⋯ ⊕ 𝒪` of copies of the structure sheaf. This file shows that global sections identify the
category of such modules with the category of finite projective modules over the ring
`Γ(X, 𝒪) = 𝒪(X)`.

The argument is the one in the source. A finite free module represents `n`-tuples of global
sections: a map out of it is determined by its `n` coordinates, which are maps out of `𝒪`, and
these are global sections. So on finite free modules global sections are fully faithful and
send `𝒪^{⊕ n}` to the free module `𝒪(X)^n`; both properties pass to retracts, which gives
fullness, faithfulness, and finiteness and projectivity of the global sections of a summand of
a finite free module. Essential surjectivity goes the other way: a finite projective
`𝒪(X)`-module is a retract of some `𝒪(X)^n`, hence is cut out by an idempotent of `𝒪(X)^n`;
that idempotent comes from a unique idempotent of `𝒪^{⊕ n}`, which splits because sheaves of
modules are idempotent complete.

## Main definitions

* `Stacks.Modules.IsDirectSummandOfFiniteFree`: being a retract of a finite free module.
* `Stacks.Modules.globalSectionsFunctor`: global sections of a sheaf of `𝒪`-modules, as a
  module over `𝒪(X)`.

## Main results

* `Stacks.Modules.globalSections_equivalence_finiteFreeSummand_finiteProjective`: the
  equivalence of categories induced by global sections, together with a natural isomorphism
  identifying its underlying functor with global sections.

## Implementation notes

Finite free sheaves are represented by `SheafOfModules.free` on the finite type
`ULift (Fin n)`, and the finite biproducts used to compare that with a product of copies of
the structure sheaf come from the finite products of sheaves of modules.

Global sections of a sheaf on `X` are its sections over the top open set, so
`globalSectionsFunctor` is `SheafOfModules.evaluation 𝒪 (op ⊤)`, valued in modules over
`𝒪(⊤)`.

The ringed-site form of the same source result is Stacks Tag 0FPX, proved in
`StacksDraft.Ch21.Sec49.FiniteFreeSummands` as
`AlgebraicGeometry.RingedSite.finiteFreeSummandEquivalenceFiniteProjective`, whose auxiliary
definitions carry the same short names in the namespace
`AlgebraicGeometry.RingedSite`. Neither result specialises to the other: there the base is a
`RingedSite`, whose structure sheaf is `CommRingCat`-valued, and global sections are the
compatible families `Stacks.Cohomology.SiteModules.globalSectionsFunctor`, valued in modules
over the subring `RingCat.sectionsSubring`; here `𝒪` is an arbitrary `RingCat`-valued sheaf on
the open-cover site of a space and global sections are evaluation at `⊤`.

## References

* [Stacks Project, Tag 0FPF](https://stacks.math.columbia.edu/tag/0FPF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Modules

variable {X : TopCat.{u}}
  (𝒪 : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

private local instance : HasFiniteBiproducts (SheafOfModules 𝒪) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private noncomputable def sectionsTopEquiv (M : SheafOfModules 𝒪) :
    M.sections ≃ M.val.obj (op (⊤ : Opens X)) where
  toFun s := s.val (op ⊤)
  invFun x := ⟨fun U =>
    ((M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat).map
      (homOfLE le_top).op) x, by
      intro U V f
      change (((M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat).map
          (homOfLE le_top).op) ≫
          (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat).map f) x =
        ((M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat).map
          (homOfLE le_top).op) x
      rw [← Functor.map_comp]
      congr 1⟩
  left_inv s := by
    apply M.val.sections_ext
    intro U
    change ((M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat).map
        (homOfLE le_top).op) (s.val (op ⊤)) = s.val U
    simpa using (s.property (homOfLE le_top).op)
  right_inv x := by
    let F := M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat
    change (F.map (𝟙 (op ⊤))) x = x
    rw [F.map_id]
    rfl

private def evaluationObjectEquiv (M : SheafOfModules 𝒪) :
    ((SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).obj M) ≃
      M.val.obj (op (⊤ : Opens X)) :=
  Equiv.refl _

private noncomputable def finiteFreeProductIso (n : ℕ) :
    (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).obj
        (SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin n))) ≅
      (ModuleCat.HasLimit.productLimitCone
        (fun _ : ULift.{u} (Fin n) =>
          (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).obj
            (SheafOfModules.unit 𝒪))).cone.pt := by
  let I := ULift.{u} (Fin n)
  let F : I → SheafOfModules 𝒪 := fun _ => SheafOfModules.unit 𝒪
  let E := SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))
  let iso1 : (⨁ F) ≅ (∐ F) := biproduct.isoCoproduct F
  let isoProdS : (⨁ F) ≅ ∏ᶜ F := biproduct.isoProduct F
  let prodCone := ModuleCat.HasLimit.productLimitCone (E.obj ∘ F)
  let moduleProductIso : (∏ᶜ (E.obj ∘ F)) ≅ prodCone.cone.pt :=
    IsLimit.conePointUniqueUpToIso (limit.isLimit (Discrete.functor (E.obj ∘ F))) prodCone.isLimit
  let evProd : E.obj (∏ᶜ F) ≅ ∏ᶜ (E.obj ∘ F) := preservesLimitIso E (Discrete.functor F)
  exact (moduleProductIso.symm ≪≫ evProd.symm ≪≫ E.mapIso isoProdS.symm ≪≫ E.mapIso iso1).symm

private lemma finiteFreeProductIso_inv_proj (n : ℕ) (j : ULift.{u} (Fin n)) :
    (finiteFreeProductIso 𝒪 n).hom ≫
      (ModuleCat.HasLimit.productLimitCone
        (fun _ : ULift.{u} (Fin n) =>
          (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).obj (SheafOfModules.unit 𝒪))).cone.π.app
        (Discrete.mk j) =
      (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).map
        ((biproduct.isoCoproduct
            (fun _ : ULift.{u} (Fin n) => SheafOfModules.unit 𝒪)).inv ≫
          biproduct.π (fun _ : ULift.{u} (Fin n) => SheafOfModules.unit 𝒪) j) := by
  let I := ULift.{u} (Fin n)
  let F : I → SheafOfModules 𝒪 := fun _ => SheafOfModules.unit 𝒪
  let E := SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))
  let iso1 : (⨁ F) ≅ (∐ F) := biproduct.isoCoproduct F
  let isoProdS : (⨁ F) ≅ ∏ᶜ F := biproduct.isoProduct F
  let prodCone := ModuleCat.HasLimit.productLimitCone (E.obj ∘ F)
  let moduleProductIso : (∏ᶜ (E.obj ∘ F)) ≅ prodCone.cone.pt :=
    IsLimit.conePointUniqueUpToIso (limit.isLimit (Discrete.functor (E.obj ∘ F))) prodCone.isLimit
  let evProd : E.obj (∏ᶜ F) ≅ ∏ᶜ (E.obj ∘ F) := preservesLimitIso E (Discrete.functor F)
  have hprod : moduleProductIso.hom ≫ prodCone.cone.π.app (Discrete.mk j) =
      limit.π (Discrete.functor (E.obj ∘ F)) (Discrete.mk j) :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (limit.isLimit (Discrete.functor (E.obj ∘ F))) prodCone.isLimit (Discrete.mk j)
  have hpres : evProd.hom ≫ limit.π (Discrete.functor (E.obj ∘ F)) (Discrete.mk j) =
      E.map (limit.π (Discrete.functor F) (Discrete.mk j)) :=
    preservesLimitIso_hom_π E (Discrete.functor F) (Discrete.mk j)
  have hbp : isoProdS.hom ≫ limit.π (Discrete.functor F) (Discrete.mk j) = biproduct.π F j := by
    simp [isoProdS, biproduct.isoProduct_hom]
  change E.map iso1.inv ≫ E.map isoProdS.hom ≫ evProd.hom ≫ moduleProductIso.hom ≫
      prodCone.cone.π.app (Discrete.mk j) = E.map (iso1.inv ≫ biproduct.π F j)
  rw [hprod, hpres, ← Functor.map_comp, hbp, ← Functor.map_comp]

private lemma finiteFreeProductIso_ι_proj (n : ℕ) (i j : ULift.{u} (Fin n)) :
    (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).map
        (SheafOfModules.ιFree (R := 𝒪) i) ≫ (finiteFreeProductIso 𝒪 n).hom ≫
      (ModuleCat.HasLimit.productLimitCone
        (fun _ : ULift.{u} (Fin n) =>
          (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).obj (SheafOfModules.unit 𝒪))).cone.π.app
        (Discrete.mk j) =
      if _h : i = j then
        (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).map (𝟙 (SheafOfModules.unit 𝒪))
      else (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).map (0 :
        SheafOfModules.unit 𝒪 ⟶ SheafOfModules.unit 𝒪) := by
  classical
  let I := ULift.{u} (Fin n)
  let F : I → SheafOfModules 𝒪 := fun _ => SheafOfModules.unit 𝒪
  let E := SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))
  let iso1 : (⨁ F) ≅ (∐ F) := biproduct.isoCoproduct F
  have hι : SheafOfModules.ιFree (R := 𝒪) i ≫ (biproduct.isoCoproduct F).inv =
      biproduct.ι F i := by
    dsimp [SheafOfModules.ιFree, SheafOfModules.free]
    rw [biproduct.isoCoproduct_inv, Sigma.ι_comp_desc]
  calc
    E.map (SheafOfModules.ιFree (R := 𝒪) i) ≫
        ((finiteFreeProductIso 𝒪 n).hom ≫
          (ModuleCat.HasLimit.productLimitCone (E.obj ∘ F)).cone.π.app (Discrete.mk j)) =
      E.map (SheafOfModules.ιFree (R := 𝒪) i) ≫
        E.map (iso1.inv ≫ biproduct.π F j) := by
          have h := finiteFreeProductIso_inv_proj (𝒪 := 𝒪) n j
          change (finiteFreeProductIso 𝒪 n).hom ≫
              (ModuleCat.HasLimit.productLimitCone (E.obj ∘ F)).cone.π.app (Discrete.mk j) =
            E.map (iso1.inv ≫ biproduct.π F j) at h
          rw [h]
          rfl
    _ = E.map (SheafOfModules.ιFree (R := 𝒪) i ≫
        (biproduct.isoCoproduct F).inv ≫ biproduct.π F j) := by rw [← Functor.map_comp]
    _ = E.map (biproduct.ι F i ≫ biproduct.π F j) :=
      congrArg E.map (congrArg (fun f => f ≫ biproduct.π F j) hι)
    _ = if h : i = j then E.map (𝟙 (SheafOfModules.unit 𝒪)) else E.map (0) := by
      rw [biproduct.ι_π]
      split_ifs with h
      · subst j
        simp [F]
      · simp

private noncomputable def finiteFreeEvalLinearEquiv (n : ℕ) :
    (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).obj
        (SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin n))) ≃ₗ[
      𝒪.obj.obj (op (⊤ : Opens X))] (ULift.{u} (Fin n) → 𝒪.obj.obj (op (⊤ : Opens X))) :=
  (finiteFreeProductIso 𝒪 n).toLinearEquiv

private noncomputable def unitAtTopOne :
    (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).obj
      (SheafOfModules.unit 𝒪) := (1 : 𝒪.obj.obj (op (⊤ : Opens X)))

private lemma finiteFreeEvalLinearEquiv_ι (n : ℕ) (i : ULift.{u} (Fin n)) :
    finiteFreeEvalLinearEquiv 𝒪 n
      ((SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).map
        (SheafOfModules.ιFree (R := 𝒪) i) (unitAtTopOne 𝒪)) =
      (fun j => if i = j then (1 : 𝒪.obj.obj (op (⊤ : Opens X))) else 0) := by
  classical
  funext j
  have h' := congrArg (fun f => f.hom (unitAtTopOne 𝒪))
    (finiteFreeProductIso_ι_proj (𝒪 := 𝒪) n i j)
  have hu : unitAtTopOne 𝒪 = (1 : 𝒪.obj.obj (op (⊤ : Opens X))) := rfl
  have h'' : (finiteFreeProductIso 𝒪 n).hom.hom
      (((SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).map
        (SheafOfModules.ιFree (R := 𝒪) i)) (unitAtTopOne 𝒪)) j =
      if i = j then (1 : 𝒪.obj.obj (op (⊤ : Opens X))) else 0 := by
    let E := SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))
    let p := (ModuleCat.HasLimit.productLimitCone
      (fun _ : ULift.{u} (Fin n) => E.obj (SheafOfModules.unit 𝒪))).cone.π.app
        (Discrete.mk j)
    change (ConcreteCategory.hom p)
      ((ConcreteCategory.hom (finiteFreeProductIso 𝒪 n).hom)
        ((ConcreteCategory.hom (E.map (SheafOfModules.ιFree (R := 𝒪) i)))
          (unitAtTopOne 𝒪))) = _
    change (ConcreteCategory.hom p)
      ((ConcreteCategory.hom (finiteFreeProductIso 𝒪 n).hom)
        ((ConcreteCategory.hom (E.map (SheafOfModules.ιFree (R := 𝒪) i)))
          (unitAtTopOne 𝒪))) =
      (ConcreteCategory.hom (if h : i = j then E.map (𝟙 (SheafOfModules.unit 𝒪))
        else E.map 0)) (unitAtTopOne 𝒪) at h'
    nth_rewrite 2 [hu] at h'
    by_cases hij : i = j
    · subst j
      simp only [Discrete.functor_obj_eq_as, Functor.const_obj_obj, hu, ↓reduceDIte,
        CategoryTheory.Functor.map_id, ModuleCat.hom_id, LinearMap.id_coe] at h'
      simp only [Discrete.functor_obj_eq_as, Functor.const_obj_obj, ↓reduceIte]
      change _ = unitAtTopOne 𝒪 at h'
      change _ = unitAtTopOne 𝒪
      exact h'
    · simp only [Discrete.functor_obj_eq_as, Functor.const_obj_obj, hij, ↓reduceDIte,
        Functor.map_zero, ModuleCat.hom_zero] at h'
      simp only [Discrete.functor_obj_eq_as, Functor.const_obj_obj, hij, ↓reduceIte]
      exact h'
  exact h''

private noncomputable def freeEvalMapPreimage (n m : ℕ)
    (f : (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).obj
        (SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin n))) ⟶
      (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).obj
        (SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin m)))) :
    SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin n)) ⟶
      SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin m)) :=
  (SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin m))).freeHomEquiv.symm
    (fun i => (sectionsTopEquiv 𝒪
      (SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin m)))).symm
      (evaluationObjectEquiv 𝒪 _
        (f ((finiteFreeEvalLinearEquiv 𝒪 n).symm (Pi.single i 1)))))

private lemma eval_unit_hom (M : SheafOfModules 𝒪)
    (f : SheafOfModules.unit 𝒪 ⟶ M) :
    (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).map f (unitAtTopOne 𝒪) =
      sectionsTopEquiv 𝒪 M (M.unitHomEquiv f) :=
  rfl

private lemma sectionsTopEquiv_map (M N : SheafOfModules 𝒪)
    (f : M ⟶ N) (s : M.sections) :
    sectionsTopEquiv 𝒪 N (SheafOfModules.sectionsMap f s) =
      (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).map f
        (sectionsTopEquiv 𝒪 M s) :=
  rfl

private lemma freeEvalMapPreimage_spec (n m : ℕ)
    (f : (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).obj
        (SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin n))) ⟶
      (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).obj
        (SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin m)))) :
    (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).map
        (freeEvalMapPreimage 𝒪 n m f) = f := by
  classical
  let E := SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))
  let I := ULift.{u} (Fin n)
  let J := ULift.{u} (Fin m)
  let B := SheafOfModules.free (R := 𝒪) J
  let en := finiteFreeEvalLinearEquiv 𝒪 n
  let em := finiteFreeEvalLinearEquiv 𝒪 m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let g₁ : (I → 𝒪.obj.obj (op ⊤)) →ₗ[𝒪.obj.obj (op ⊤)]
      (J → 𝒪.obj.obj (op ⊤)) := em.toLinearMap.comp
        ((E.map (freeEvalMapPreimage 𝒪 n m f)).hom.comp en.symm.toLinearMap)
  let g₂ : (I → 𝒪.obj.obj (op ⊤)) →ₗ[𝒪.obj.obj (op ⊤)]
      (J → 𝒪.obj.obj (op ⊤)) := em.toLinearMap.comp (f.hom.comp en.symm.toLinearMap)
  have hg : g₁ = g₂ := by
    apply (Pi.basisFun (𝒪.obj.obj (op ⊤)) I).ext
    intro i
    have hb : en.symm (Pi.single i (1 : 𝒪.obj.obj (op ⊤))) =
        E.map (SheafOfModules.ιFree (R := 𝒪) i) (unitAtTopOne 𝒪) := by
      apply en.injective
      rw [finiteFreeEvalLinearEquiv_ι]
      ext j
      simp [Pi.single_apply, eq_comm]
    have hbase : E.map (freeEvalMapPreimage 𝒪 n m f) (en.symm
        (Pi.single i (1 : 𝒪.obj.obj (op ⊤)))) =
        f (en.symm (Pi.single i (1 : 𝒪.obj.obj (op ⊤)))) := by
      rw [hb]
      change (E.map (SheafOfModules.ιFree (R := 𝒪) i ≫
        freeEvalMapPreimage 𝒪 n m f) (unitAtTopOne 𝒪)) = _
      rw [eval_unit_hom, SheafOfModules.unitHomEquiv_comp_apply]
      have hfree : (SheafOfModules.free (R := 𝒪) I).unitHomEquiv
          (SheafOfModules.ιFree (R := 𝒪) i) = SheafOfModules.freeSection (R := 𝒪) i := rfl
      dsimp [freeEvalMapPreimage]
      rw [hfree, SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection,
        (sectionsTopEquiv 𝒪 B).apply_symm_apply]
      change f (en.symm (Pi.single i (1 : 𝒪.obj.obj (op ⊤)))) =
        f (E.map (SheafOfModules.ιFree (R := 𝒪) i) (unitAtTopOne 𝒪))
      exact congrArg f hb
    simpa [g₁, g₂, Pi.basisFun_apply] using congrArg em hbase
  apply em.injective
  simpa [g₁, g₂] using congrArg (fun q => q (en x)) hg

/-- A sheaf of `𝒪`-modules is a direct summand of a finite free sheaf if it is
a retract of the free sheaf on `n` generators for some `n`. -/
public def IsDirectSummandOfFiniteFree
    (E : SheafOfModules 𝒪) : Prop :=
  ∃ n : ℕ,
    Nonempty (Retract E
      (SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin n))))

private lemma freeEvalMap_injective (n m : ℕ)
    {f g : SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin n)) ⟶
      SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin m))}
    (h : (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).map f =
      (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).map g) : f = g := by
  let A := SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin n))
  let B := SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin m))
  let E := SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))
  have hfun : B.freeHomEquiv f = B.freeHomEquiv g := by
    funext i
    apply (sectionsTopEquiv 𝒪 B).injective
    have hgen : E.map (SheafOfModules.ιFree (R := 𝒪) i) (unitAtTopOne 𝒪) =
        sectionsTopEquiv 𝒪 A (SheafOfModules.freeSection (R := 𝒪) i) := rfl
    change sectionsTopEquiv 𝒪 B (SheafOfModules.sectionsMap f
        (SheafOfModules.freeSection (R := 𝒪) i)) =
      sectionsTopEquiv 𝒪 B (SheafOfModules.sectionsMap g
        (SheafOfModules.freeSection (R := 𝒪) i))
    rw [sectionsTopEquiv_map, sectionsTopEquiv_map, ← hgen]
    exact congrArg (fun k => k (E.map (SheafOfModules.ιFree (R := 𝒪) i) (unitAtTopOne 𝒪))) h
  exact B.freeHomEquiv.injective hfun

private lemma finiteFreeGlobalSections_finiteProjective (n : ℕ) :
    Module.Finite (𝒪.obj.obj (op (⊤ : Opens X)))
      ((SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).obj
        (SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin n)))) ∧
    Module.Projective (𝒪.obj.obj (op (⊤ : Opens X)))
      ((SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).obj
        (SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin n)))) :=
  ⟨Module.Finite.of_surjective (finiteFreeEvalLinearEquiv 𝒪 n).symm.toLinearMap
      (finiteFreeEvalLinearEquiv 𝒪 n).symm.surjective,
    Module.Projective.of_equiv' (finiteFreeEvalLinearEquiv 𝒪 n).symm⟩

private lemma globalSections_finiteProjective_of_retract
    (M : SheafOfModules 𝒪) (hM : IsDirectSummandOfFiniteFree 𝒪 M) :
    Module.Finite (𝒪.obj.obj (op (⊤ : Opens X)))
        ((SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).obj M) ∧
      Module.Projective (𝒪.obj.obj (op (⊤ : Opens X)))
        ((SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).obj M) := by
  obtain ⟨n, ⟨r⟩⟩ := hM
  let E := SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))
  let r' := r.map E
  obtain ⟨_, _⟩ := finiteFreeGlobalSections_finiteProjective (𝒪 := 𝒪) n
  have hri : ∀ x, r'.r.hom (r'.i.hom x) = x := fun x => by
    change (r'.i ≫ r'.r) x = x
    rw [r'.retract]
    rfl
  exact ⟨Module.Finite.of_surjective r'.r.hom fun x => ⟨r'.i.hom x, hri x⟩,
    Module.Projective.of_split r'.i.hom r'.r.hom (LinearMap.ext hri)⟩

private lemma globalSections_map_injective_of_retract
    (M N : SheafOfModules 𝒪)
    (hM : IsDirectSummandOfFiniteFree 𝒪 M)
    (hN : IsDirectSummandOfFiniteFree 𝒪 N)
    {f g : M ⟶ N}
    (h : (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).map f =
      (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).map g) : f = g := by
  obtain ⟨n, ⟨rM⟩⟩ := hM
  obtain ⟨m, ⟨rN⟩⟩ := hN
  let E := SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))
  have hcomp : E.map (rM.r ≫ f ≫ rN.i) = E.map (rM.r ≫ g ≫ rN.i) := by
    simp only [Functor.map_comp]
    rw [h]
  calc
    f = rM.i ≫ (rM.r ≫ f ≫ rN.i) ≫ rN.r := by
      simp [Category.assoc, rN.retract]
    _ = rM.i ≫ (rM.r ≫ g ≫ rN.i) ≫ rN.r := by rw [freeEvalMap_injective (𝒪 := 𝒪) n m hcomp]
    _ = g := by simp [Category.assoc, rN.retract]

private lemma globalSections_map_surjective_of_retract
    (M N : SheafOfModules 𝒪)
    (hM : IsDirectSummandOfFiniteFree 𝒪 M)
    (hN : IsDirectSummandOfFiniteFree 𝒪 N)
    (f : (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).obj M ⟶
      (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).obj N) :
    ∃ g : M ⟶ N,
      (SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))).map g = f := by
  obtain ⟨n, ⟨rM⟩⟩ := hM
  obtain ⟨m, ⟨rN⟩⟩ := hN
  let E := SheafOfModules.evaluation 𝒪 (op (⊤ : Opens X))
  let hfree : E.obj (SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin n))) ⟶
      E.obj (SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin m))) :=
    E.map rM.r ≫ f ≫ E.map rN.i
  let ffree := freeEvalMapPreimage 𝒪 n m hfree
  refine ⟨rM.i ≫ ffree ≫ rN.r, ?_⟩
  simp only [Functor.map_comp]
  change E.map rM.i ≫ E.map ffree ≫ E.map rN.r = f
  rw [freeEvalMapPreimage_spec]
  have hleft : E.map rM.i ≫ E.map rM.r = 𝟙 _ := (rM.map E).retract
  have hright : E.map rN.i ≫ E.map rN.r = 𝟙 _ := (rN.map E).retract
  dsimp [hfree]
  calc
    (E.map rM.i ≫ (E.map rM.r ≫ f ≫ E.map rN.i)) ≫ E.map rN.r =
        (E.map rM.i ≫ E.map rM.r) ≫ (f ≫ E.map rN.i ≫ E.map rN.r) := by
          cat_disch
    _ = f := by rw [hleft, hright, Category.id_comp, Category.comp_id]

/-- If `i₁ ≫ r₁ = 𝟙` and `r₂ ≫ i₂ = r₁ ≫ i₁`, then `i₁ ≫ r₂ ≫ i₂ ≫ r₁ = 𝟙`. -/
private theorem retract_comp_comp_eq_id {C : Type*} [Category C] {U V W : C}
    {i₁ : U ⟶ V} {r₁ : V ⟶ U} {i₂ : W ⟶ V} {r₂ : V ⟶ W}
    (h₁ : i₁ ≫ r₁ = 𝟙 U) (h : r₂ ≫ i₂ = r₁ ≫ i₁) :
    i₁ ≫ r₂ ≫ i₂ ≫ r₁ = 𝟙 U := by
  rw [← Category.assoc r₂, h]
  simp [h₁]

private def finiteULiftPiLinearEquiv (n : ℕ) :
    (ULift.{u} (Fin n) → 𝒪.obj.obj (op (⊤ : Opens X))) ≃ₗ[
      𝒪.obj.obj (op (⊤ : Opens X))]
        (Fin n → 𝒪.obj.obj (op (⊤ : Opens X))) where
  toFun f i := f ⟨i⟩
  invFun f i := f i.down
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The functor taking a sheaf of `𝒪`-modules to its module of global
sections over `Γ(X, 𝒪)`. -/
public noncomputable def globalSectionsFunctor :
    SheafOfModules 𝒪 ⥤ ModuleCat.{u} (𝒪.obj.obj (op (⊤ : Opens X))) :=
  SheafOfModules.evaluation 𝒪 (op ⊤)

/-- **Stacks Project, Tag 0FPF.** Global sections induce an equivalence from
direct summands of finite free `𝒪`-modules to finite projective modules over
the ring of global sections. -/
@[stacks 0FPF]
public theorem globalSections_equivalence_finiteFreeSummand_finiteProjective :
    ∃ (e : ObjectProperty.FullSubcategory (IsDirectSummandOfFiniteFree 𝒪) ≌
        ObjectProperty.FullSubcategory
          (fun M : ModuleCat.{u} (𝒪.obj.obj (op (⊤ : Opens X))) =>
            Module.Finite (𝒪.obj.obj (op (⊤ : Opens X))) M ∧
              Module.Projective (𝒪.obj.obj (op (⊤ : Opens X))) M)),
      Nonempty
        (e.functor ⋙ ObjectProperty.ι _ ≅
          ObjectProperty.ι _ ⋙ globalSectionsFunctor 𝒪) := by
  let R := 𝒪.obj.obj (op (⊤ : Opens X))
  let P : ObjectProperty (SheafOfModules 𝒪) := IsDirectSummandOfFiniteFree 𝒪
  let Q : ObjectProperty (ModuleCat.{u} R) := fun M =>
    Module.Finite R M ∧ Module.Projective R M
  let G := globalSectionsFunctor 𝒪
  let H := P.ι ⋙ G
  have hobj : ∀ A : P.FullSubcategory, Q (G.obj A.obj) := fun A =>
    globalSections_finiteProjective_of_retract 𝒪 A.obj A.property
  let F := Q.lift H hobj
  have : H.Full := by
    refine ⟨?_⟩
    intro A B f
    obtain ⟨g, hg⟩ := globalSections_map_surjective_of_retract 𝒪 A.obj B.obj
      A.property B.property f
    exact ⟨P.homMk g, hg⟩
  have : H.Faithful := by
    refine ⟨?_⟩
    intro A B f g h
    exact P.ι.map_injective (globalSections_map_injective_of_retract 𝒪 A.obj B.obj
      A.property B.property h)
  have : F.EssSurj := by
    refine ⟨?_⟩
    intro T
    let M := T.obj
    have hfinite : Module.Finite R M := T.property.1
    have hprojective : Module.Projective R M := T.property.2
    obtain ⟨n, f, g, -, -, hfg⟩ :=
      Module.Finite.exists_comp_eq_id_of_projective R M
    let A := SheafOfModules.free (R := 𝒪) (ULift.{u} (Fin n))
    let E := G
    let e := finiteFreeEvalLinearEquiv 𝒪 n
    let eI := finiteULiftPiLinearEquiv (𝒪 := 𝒪) n
    let iMap := e.symm.toLinearMap.comp (eI.symm.toLinearMap.comp g)
    let rMap := f.comp (eI.toLinearMap.comp e.toLinearMap)
    have hsplit : rMap.comp iMap = LinearMap.id := by
      ext x
      simpa [iMap, rMap, LinearMap.comp_apply] using
        congrArg (fun k : M →ₗ[R] M => k x) hfg
    let iM : M ⟶ E.obj A := ModuleCat.ofHom iMap
    let rM : E.obj A ⟶ M := ModuleCat.ofHom rMap
    have hsplitCat : iM ≫ rM = 𝟙 M := by
      ext x
      change rMap (iMap x) = x
      exact congrArg (fun k : M →ₗ[R] M => k x) hsplit
    let pM : E.obj A ⟶ E.obj A := rM ≫ iM
    have hpM : pM ≫ pM = pM := by
      change (rM ≫ iM) ≫ (rM ≫ iM) = rM ≫ iM
      calc
        (rM ≫ iM) ≫ (rM ≫ iM) = rM ≫ (iM ≫ rM) ≫ iM := by cat_disch
        _ = rM ≫ 𝟙 M ≫ iM := by rw [hsplitCat]
        _ = rM ≫ iM := by simp
    let pS := freeEvalMapPreimage 𝒪 n n pM
    have hpSmap : E.map pS = pM := freeEvalMapPreimage_spec 𝒪 n n pM
    have hpS : pS ≫ pS = pS := by
      apply freeEvalMap_injective (𝒪 := 𝒪) n n
      calc
        E.map (pS ≫ pS) = E.map pS ≫ E.map pS := by rw [Functor.map_comp]
        _ = pM ≫ pM := by rw [hpSmap]
        _ = pM := hpM
        _ = E.map pS := hpSmap.symm
    obtain ⟨Y, iY, rY, hiY, hpY⟩ :=
      IsIdempotentComplete.idempotents_split A pS hpS
    have hY : P Y := ⟨n, ⟨⟨iY, rY, hiY⟩⟩⟩
    have hsplitMap : E.map rY ≫ E.map iY = pM := by
      rw [← Functor.map_comp, hpY, hpSmap]
    have hsplitMap' := ((⟨iY, rY, hiY⟩ : Retract Y A).map E).retract
    let eYM : E.obj Y ≅ M := {
      hom := E.map iY ≫ rM
      inv := iM ≫ E.map rY
      hom_inv_id := retract_comp_comp_eq_id hsplitMap' hsplitMap.symm
      inv_hom_id := retract_comp_comp_eq_id hsplitCat hsplitMap
    }
    exact ⟨⟨Y, hY⟩, ⟨Q.isoMk eYM⟩⟩
  have : F.IsEquivalence := { }
  exact ⟨F.asEquivalence, ⟨ObjectProperty.liftCompιIso Q H hobj⟩⟩

end Stacks.Modules
