module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Adequate.Defs

/-!
# Pushforward of adequate functors

Restricting a module-valued functor along a ring map takes adequate functors to adequate
functors.

## References

* [Stacks Project, Tag 06VA](https://stacks.math.columbia.edu/tag/06VA)
-/

@[expose] public section

namespace AdequateFunctor

section

open CategoryTheory CategoryTheory.Limits

universe u v c w


private theorem pushforward_preservesKernel
    {C D : Type v} [Category.{c} C] [Category.{c} D]
    {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}
    (G : C ⥤ D) (φ : S ⟶ G.op ⋙ R)
    {X Y : PresheafOfModules.{max u w} R} (g : X ⟶ Y) :
    PreservesLimit (parallelPair g 0) (PresheafOfModules.pushforward.{max u w} φ) :=
  preservesLimit_of_preserves_limit_cone (kernelIsKernel g)
    (PresheafOfModules.evaluationJointlyReflectsLimits _ _ fun Z =>
      isLimitOfPreserves (ModuleCat.restrictScalars (φ.app Z).hom)
        (isLimitOfPreserves (PresheafOfModules.evaluation R (G.op.obj Z)) (kernelIsKernel g)))

variable {A A' : Type u} [CommRing A] [CommRing A'] (f : A →+* A')

/-- Extension of the base ring on commutative algebras. -/
public noncomputable def baseChangeFunctor : CommAlgCat.{u} A ⥤ CommAlgCat.{u} A' :=
  (commAlgCatEquivUnder (CommRingCat.of A)).functor ⋙
    Under.pushout (CommRingCat.ofHom f) ⋙
      (commAlgCatEquivUnder (CommRingCat.of A')).inverse

/-- The canonical map from an algebra to its base change, as a map of ring diagrams. -/
public noncomputable def baseChangeRingHom :
    AdequateFunctor.algebraRingDiagram A ⟶
      (baseChangeFunctor f).op.op ⋙ AdequateFunctor.algebraRingDiagram A' where
  app X := RingCat.ofHom (pushout.inl
    ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj X.unop.unop).hom
    (CommRingCat.ofHom f)).hom
  naturality := by
    intro X Y g
    apply RingCat.hom_ext
    change CommRingCat.Hom.hom
      (g.unop.unop.hom.toUnder.right ≫ pushout.inl _ _) =
      CommRingCat.Hom.hom
        (pushout.inl _ _ ≫
          ((Under.pushout (CommRingCat.ofHom f)).map g.unop.unop.hom.toUnder).right)
    congr 1
    simp only [CommRingCat.mkUnder_hom, Under.pushout, Under.mk_right, Under.homMk_right]
    rw [pushout.inl_desc]

/-- The module-valued functor `B ↦ F'(A' ⊗[A] B)`, with its natural `B`-module action. -/
public noncomputable def pushforward
    (F' : AdequateFunctor.ModuleValuedFunctor.{w, u} A') :
    AdequateFunctor.ModuleValuedFunctor.{w, u} A :=
  (PresheafOfModules.pushforward (baseChangeRingHom f)).obj F'

/-- Adequacy is preserved by extension of the base ring in the argument. -/
@[stacks 06VA]
public lemma isAdequate_pushforward
    (F' : AdequateFunctor.ModuleValuedFunctor.{w, u} A')
    (hF' : AdequateFunctor.IsAdequate.{w, u} (A := A') (𝟭 _) F') :
    AdequateFunctor.IsAdequate.{w, u} (A := A) (𝟭 _) (pushforward f F') := by
  rcases hF' with ⟨M', N', g', ⟨e'⟩⟩
  let M := (ModuleCat.restrictScalars f).obj M'
  let N := (ModuleCat.restrictScalars f).obj N'
  let g := (ModuleCat.restrictScalars f).map g'
  refine ⟨M, N, g, ?_⟩
  let : Algebra A A' := f.toAlgebra
  let E := PresheafOfModules.pushforward (baseChangeRingHom f)
  let d' := (AdequateFunctor.moduleExtensionFunctor A').map g'
  let : PreservesLimit (parallelPair d' 0) E :=
    pushforward_preservesKernel
      (C := (CommAlgCat.{u} A)ᵒᵖ) (D := (CommAlgCat.{u} A')ᵒᵖ)
      (R := AdequateFunctor.algebraRingDiagram A') (S := AdequateFunctor.algebraRingDiagram A)
      ((baseChangeFunctor f).op) (baseChangeRingHom f) d'
  let : Functor.PreservesZeroMorphisms E := ⟨by
    intro X Y
    ext Z z
    rfl⟩
  have hpres := PreservesKernel.iso E d'
  let makeIso (P' : ModuleCat.{max u w} A') :
      E.obj ((AdequateFunctor.moduleExtensionFunctor A').obj P') ≅
        (AdequateFunctor.moduleExtensionFunctor A).obj ((ModuleCat.restrictScalars f).obj P') := by
    let P := (ModuleCat.restrictScalars f).obj P'
    let hpX (X : ((CommAlgCat.{u} A)ᵒᵖ)ᵒᵖ) :
        (E.obj ((AdequateFunctor.moduleExtensionFunctor A').obj P')).obj X ≅
          ((AdequateFunctor.moduleExtensionFunctor A).obj P).obj X := by
      let B := X.unop.unop
      let B' := ((baseChangeFunctor f).op.obj X.unop).unop
      let : Algebra B B' := (((baseChangeRingHom f).app X).hom).toAlgebra
      let : Algebra A B' := ((algebraMap A' B').comp f).toAlgebra
      let : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq' rfl
      let U := (commAlgCatEquivUnder (CommRingCat.of A)).functor.obj B
      have hcomm : U.hom ≫ pushout.inl U.hom (CommRingCat.ofHom f) =
          CommRingCat.ofHom f ≫ pushout.inr U.hom (CommRingCat.ofHom f) := pushout.condition
      have hcomp : algebraMap A B' = (algebraMap B B').comp (algebraMap A B) := by
        ext a
        change (pushout.inr U.hom (CommRingCat.ofHom f)).hom (f a) =
          (pushout.inl U.hom (CommRingCat.ofHom f)).hom (U.hom.hom a)
        exact congrArg (fun k : CommRingCat.Hom _ _ => k.hom a) hcomm.symm
      let : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' hcomp
      let : IsScalarTower A A' (↑P) := IsScalarTower.of_algebraMap_smul fun r x => rfl
      have hbase : Algebra.IsPushout A B A' B' := by
        apply (CommRingCat.isPushout_iff_isPushout (R := A) (R' := B)
          (S := A') (S' := B')).mp
        refine ⟨⟨hcomm⟩, ⟨pushoutIsPushout U.hom (CommRingCat.ofHom f)⟩⟩
      exact (Algebra.IsPushout.cancelBaseChange A B A' B' P).toModuleIso
    have eM : E.obj ((AdequateFunctor.moduleExtensionFunctor A').obj P') ≅
        (AdequateFunctor.moduleExtensionFunctor A).obj P :=
      PresheafOfModules.isoMk hpX (by
        intro X Y t
        let eX := hpX X
        let eY := hpX Y
        let BX := X.unop.unop
        let BY := Y.unop.unop
        let B'X := ((baseChangeFunctor f).op.obj X.unop).unop
        let B'Y := ((baseChangeFunctor f).op.obj Y.unop).unop
        let UX := (commAlgCatEquivUnder (CommRingCat.of A)).functor.obj BX
        let UY := (commAlgCatEquivUnder (CommRingCat.of A)).functor.obj BY
        let : Algebra BX B'X := (((baseChangeRingHom f).app X).hom).toAlgebra
        let : Algebra BY B'Y := (((baseChangeRingHom f).app Y).hom).toAlgebra
        let : Algebra A B'X := ((algebraMap A' B'X).comp f).toAlgebra
        let : Algebra A B'Y := ((algebraMap A' B'Y).comp f).toAlgebra
        let : IsScalarTower A A' B'X := IsScalarTower.of_algebraMap_eq' rfl
        let : IsScalarTower A A' B'Y := IsScalarTower.of_algebraMap_eq' rfl
        have hcommX : UX.hom ≫ pushout.inl UX.hom (CommRingCat.ofHom f) =
            CommRingCat.ofHom f ≫ pushout.inr UX.hom (CommRingCat.ofHom f) := pushout.condition
        have hcommY : UY.hom ≫ pushout.inl UY.hom (CommRingCat.ofHom f) =
            CommRingCat.ofHom f ≫ pushout.inr UY.hom (CommRingCat.ofHom f) := pushout.condition
        have hcompX : algebraMap A B'X = (algebraMap BX B'X).comp (algebraMap A BX) := by
          ext a
          change (pushout.inr UX.hom (CommRingCat.ofHom f)).hom (f a) =
            (pushout.inl UX.hom (CommRingCat.ofHom f)).hom (UX.hom.hom a)
          exact congrArg (fun k : CommRingCat.Hom _ _ => k.hom a) hcommX.symm
        have hcompY : algebraMap A B'Y = (algebraMap BY B'Y).comp (algebraMap A BY) := by
          ext a
          change (pushout.inr UY.hom (CommRingCat.ofHom f)).hom (f a) =
            (pushout.inl UY.hom (CommRingCat.ofHom f)).hom (UY.hom.hom a)
          exact congrArg (fun k : CommRingCat.Hom _ _ => k.hom a) hcommY.symm
        let : IsScalarTower A BX B'X := IsScalarTower.of_algebraMap_eq' hcompX
        let : IsScalarTower A BY B'Y := IsScalarTower.of_algebraMap_eq' hcompY
        let : IsScalarTower A A' (↑P) := IsScalarTower.of_algebraMap_smul fun r x => rfl
        have hbaseX : Algebra.IsPushout A BX A' B'X := by
          apply (CommRingCat.isPushout_iff_isPushout (R := A) (R' := BX)
            (S := A') (S' := B'X)).mp
          refine ⟨⟨hcommX⟩, ⟨pushoutIsPushout UX.hom (CommRingCat.ofHom f)⟩⟩
        have hbaseY : Algebra.IsPushout A BY A' B'Y := by
          apply (CommRingCat.isPushout_iff_isPushout (R := A) (R' := BY)
            (S := A') (S' := B'Y)).mp
          refine ⟨⟨hcommY⟩, ⟨pushoutIsPushout UY.hom (CommRingCat.ofHom f)⟩⟩
        let : Algebra.IsPushout A BX A' B'X := hbaseX
        let : Algebra.IsPushout A BY A' B'Y := hbaseY
        have hring (b : BX) :
            (((baseChangeRingHom f).app Y).hom) (t.unop.unop.hom b) =
              (RingCat.Hom.hom (((baseChangeFunctor f).op.op ⋙
                AdequateFunctor.algebraRingDiagram A').map t))
                (((baseChangeRingHom f).app X).hom b) := by
          have hnat := (baseChangeRingHom f).naturality t
          exact congrArg (fun q : RingCat.Hom _ _ => q.hom b) hnat
        have hinv :
            ((AdequateFunctor.moduleExtensionFunctor A).obj P).map t ≫
                (ModuleCat.restrictScalars
                  (RingCat.Hom.hom ((AdequateFunctor.algebraRingDiagram A).map t))).map eY.inv =
              eX.inv ≫ (E.obj ((AdequateFunctor.moduleExtensionFunctor A').obj P')).map t := by
          apply ModuleCat.hom_ext
          ext z
          induction z using TensorProduct.induction_on with
          | zero => rfl
          | tmul b m =>
            rw [ModuleCat.comp_apply]
            change (Algebra.IsPushout.cancelBaseChange A (↑BY) A' ↑B'Y P).symm
              (t.unop.unop.hom b ⊗ₜ[A] m) = _
            rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
            rw [ModuleCat.comp_apply]
            have hX : eX.inv (b ⊗ₜ[A] m) =
                (algebraMap BX B'X b ⊗ₜ[A'] (m : P') :
                  ↑((E.obj ((AdequateFunctor.moduleExtensionFunctor A').obj P')).obj X)) := by
              change (Algebra.IsPushout.cancelBaseChange A (↑BX) A' ↑B'X P).symm
                (b ⊗ₜ[A] m) = _
              rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
              rfl
            have hXmap := congrArg
              (fun z : ↑((E.obj ((AdequateFunctor.moduleExtensionFunctor A').obj P')).obj X) =>
                ((E.obj ((AdequateFunctor.moduleExtensionFunctor A').obj P')).map t) z) hX
            change (algebraMap BY B'Y (t.unop.unop.hom b) ⊗ₜ[A'] (m : P')) =
              (E.obj ((AdequateFunctor.moduleExtensionFunctor A').obj P')).map t
                (eX.inv (b ⊗ₜ[A] m))
            rw [hXmap]
            rw [PresheafOfModules.pushforward_obj_map_apply
              (φ := baseChangeRingHom f)
              (M := (AdequateFunctor.moduleExtensionFunctor A').obj P')
              (f := t)
              (m := (algebraMap BX B'X b ⊗ₜ[A'] (m : P') :
                ↑((E.obj ((AdequateFunctor.moduleExtensionFunctor A').obj P')).obj X)))]
            change (algebraMap BY B'Y (t.unop.unop.hom b) ⊗ₜ[A'] (m : P')) =
              ((AdequateFunctor.moduleExtensionMap A' P'
                (((baseChangeFunctor f).op.map t.unop).op.unop.unop))
                (algebraMap BX B'X b ⊗ₜ[A'] (m : P')))
            dsimp only [AdequateFunctor.moduleExtensionMap]
            exact congrArg (fun c : ↑B'Y => c ⊗ₜ[A'] (m : P')) (hring b)
          | add x y hx hy =>
            simp only [map_add]
            rw [hx, hy]
        have hh := congrArg (fun q => q ≫
          (ModuleCat.restrictScalars
            (RingCat.Hom.hom ((AdequateFunctor.algebraRingDiagram A).map t))).map eY.hom) hinv
        rw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id] at hh
        rw [((ModuleCat.restrictScalars
          (RingCat.Hom.hom ((AdequateFunctor.algebraRingDiagram A).map t))).map_id
            (((AdequateFunctor.moduleExtensionFunctor A).obj P).obj Y))] at hh
        simp only [Category.comp_id] at hh
        have hh₁ : ((AdequateFunctor.moduleExtensionFunctor A).obj P).map t =
            eX.inv ≫ (E.obj ((AdequateFunctor.moduleExtensionFunctor A').obj P')).map t ≫
              (ModuleCat.restrictScalars
                (RingCat.Hom.hom ((AdequateFunctor.algebraRingDiagram A).map t))).map eY.hom := by
          convert hh using 1
        have hh₂ := congrArg (fun q => eX.hom ≫ q) hh₁
        simpa [Category.assoc, Iso.hom_inv_id] using hh₂.symm)
    exact eM
  let eM := makeIso M'
  let eN := makeIso N'
  have hsq :
      ((AdequateFunctor.moduleExtensionFunctor A).map g) ≫ eN.inv =
        eM.inv ≫ E.map d' := by
    apply PresheafOfModules.hom_ext
    intro X
    let BX := X.unop.unop
    let B'X := ((baseChangeFunctor f).op.obj X.unop).unop
    let UX := (commAlgCatEquivUnder (CommRingCat.of A)).functor.obj BX
    let : Algebra BX B'X := (((baseChangeRingHom f).app X).hom).toAlgebra
    let : Algebra A B'X := ((algebraMap A' B'X).comp f).toAlgebra
    let : IsScalarTower A A' B'X := IsScalarTower.of_algebraMap_eq' rfl
    have hcommX : UX.hom ≫ pushout.inl UX.hom (CommRingCat.ofHom f) =
        CommRingCat.ofHom f ≫ pushout.inr UX.hom (CommRingCat.ofHom f) := pushout.condition
    have hcompX : algebraMap A B'X = (algebraMap BX B'X).comp (algebraMap A BX) := by
      ext a
      change (pushout.inr UX.hom (CommRingCat.ofHom f)).hom (f a) =
        (pushout.inl UX.hom (CommRingCat.ofHom f)).hom (UX.hom.hom a)
      exact congrArg (fun k : CommRingCat.Hom _ _ => k.hom a) hcommX.symm
    let : IsScalarTower A BX B'X := IsScalarTower.of_algebraMap_eq' hcompX
    have hbaseX : Algebra.IsPushout A BX A' B'X := by
      apply (CommRingCat.isPushout_iff_isPushout (R := A) (R' := BX)
        (S := A') (S' := B'X)).mp
      refine ⟨⟨hcommX⟩, ⟨pushoutIsPushout UX.hom (CommRingCat.ofHom f)⟩⟩
    let : Algebra.IsPushout A BX A' B'X := hbaseX
    let : IsScalarTower A A' (↑M) := IsScalarTower.of_algebraMap_smul fun r x => rfl
    have hinvM (b : BX) (m : M) :
        (eM.inv.app X) (b ⊗ₜ[A] m) = algebraMap BX B'X b ⊗ₜ[A'] (m : M') := by
      change (Algebra.IsPushout.cancelBaseChange A BX A' B'X M).symm
        (b ⊗ₜ[A] m) = _
      rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
    let : IsScalarTower A A' (↑N) := IsScalarTower.of_algebraMap_smul fun r x => rfl
    have hinvN (b : BX) (m : N) :
        (eN.inv.app X) (b ⊗ₜ[A] m) = algebraMap BX B'X b ⊗ₜ[A'] (m : N') := by
      change (Algebra.IsPushout.cancelBaseChange A BX A' B'X N).symm
        (b ⊗ₜ[A] m) = _
      rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
    apply ModuleCat.hom_ext
    ext z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul b m =>
      change (eN.inv.app X)
          (((AdequateFunctor.moduleExtensionFunctor A).map g).app X (b ⊗ₜ[A] m)) =
        ((E.map d').app X) (eM.inv.app X (b ⊗ₜ[A] m))
      rw [AdequateFunctor.moduleExtensionFunctor_map_app_tmul]
      rw [hinvN b (g.hom m)]
      rw [hinvM b m]
      -- `m` is bound at the restricted carrier `↑((ModuleCat.restrictScalars f).obj M')`,
      -- which `rw` will not see through at reducible transparency.  Since
      -- `moduleExtensionFunctor_map_app_tmul` holds by `rfl`, state its right-hand side in
      -- the `change` instead of rewriting with it.
      change (algebraMap BX B'X b ⊗ₜ[A'] (g.hom m : N')) =
        (algebraMap BX B'X b ⊗ₜ[A'] (g'.hom (m : M') : N'))
      rfl
    | add x y hx hy =>
      simp only [map_add]
      rw [hx, hy]
  let d := (AdequateFunctor.moduleExtensionFunctor A).map g
  have hsq' : eM.hom ≫ d = E.map d' ≫ eN.hom := by
    simpa [Category.assoc, Iso.hom_inv_id] using congrArg (fun q => eM.hom ≫ q ≫ eN.hom) hsq
  let kernelIso : kernel (E.map d') ≅ kernel d :=
    kernel.mapIso (E.map d') d eM eN hsq'.symm
  let uliftA' :=
    (AdequateFunctor.presheafOfModulesUliftFunctor.{u, w}
      (AdequateFunctor.algebraRingDiagram A')).obj F'
  let uliftA :=
    (AdequateFunctor.presheafOfModulesUliftFunctor.{u, w}
      (AdequateFunctor.algebraRingDiagram A)).obj
      (pushforward f F')
  exact ⟨(show uliftA ≅ E.obj uliftA' from Iso.refl _).trans
    ((E.mapIso e').trans hpres |>.trans kernelIso)⟩

end

end AdequateFunctor

end
