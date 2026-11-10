module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.TensorDualEndomorphism
import StacksCore.Tactic.StacksAttribute

/-!
# Coevaluation for a locally finite free summand

Let `(X, O_X)` be a ringed space and let `F` be a sheaf of `O_X`-modules which is locally a
direct summand of a finite free module. Stacks 0FNV attaches to `F` a *coevaluation*
`O_X ⟶ F ⊗ F^∨`, namely the inverse image of the identity endomorphism under the rank-one
isomorphism `F ⊗ F^∨ ≅ SheafHom(F, F)` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.TensorDualEndomorphism`.

## Main definitions

* `Stacks.SheafOfModules.OnSpace.freeCoordinate` is the `j`-th coordinate functional on a
  finite free module over an open `U`.
* `Stacks.SheafOfModules.OnSpace.splittingBasisSection` and
  `Stacks.SheafOfModules.OnSpace.splittingDualSection` are the dual basis attached to a
  splitting of `F|_U` through a finite free module.
* `Stacks.SheafOfModules.OnSpace.identityEndomorphism` is the global section of
  `SheafHom(F, F)` given by the identity on every restriction.
* `Stacks.SheafOfModules.OnSpace.coevaluation` is the coevaluation morphism.

## Main results

* `Stacks.SheafOfModules.OnSpace.splitting_dualBasis`: a splitting of `F|_U` through a finite
  free module gives a dual basis for `F` over `U`.
* `Stacks.SheafOfModules.OnSpace.coevaluation_comp_tensorDualToEndomorphism`: under the
  rank-one isomorphism the coevaluation is the identity endomorphism.
* `Stacks.SheafOfModules.OnSpace.coevaluation_apply_eq_sum_of_retract`: on an open carrying a
  splitting through a finite free module, the value of the coevaluation at `1` is
  `∑ j, p(e j) ⊗ (e j)^* ∘ i`. Since the left-hand side does not mention the splitting, this
  also says that the displayed sum is independent of it.

## Implementation notes

The coevaluation is the composite of `identityEndomorphism` with the inverse of
`tensorDualToEndomorphism`; no `eqToHom` is needed, because `dualSheaf X F` is *by definition*
`sheafHom X F (SheafOfModules.unit _)`, the target of the rank-one map.

`freeCoordinate` is `Sigma.desc` of the Kronecker family, which is the coordinate functional
`e_j^*`; the local formula is stated at the terminal object `Over.mk (𝟙 U)` of the slice site
over `U`, where a section of the internal hom is evaluated.

## References

* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace TensorProduct

universe u

namespace Stacks.SheafOfModules.OnSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace

attribute [local implicit_reducible] restrFun ORestr PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ ModuleCat.restrictScalars internalHom

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- The `j`-th coordinate functional `e_j^*` on the finite free module `O_U^{⊕n}`. -/
noncomputable def freeCoordinate (U : Opens X.carrier) (n : ℕ) (j : Fin n) :
    SheafOfModules.free (R := (structureSheafRing X).over U) (ULift.{u} (Fin n)) ⟶
      SheafOfModules.unit ((structureSheafRing X).over U) :=
  Sigma.desc (fun k => if k = ULift.up j then 𝟙 _ else 0)

/-- The image of the `j`-th standard basis vector under a map `O_U^{⊕n} ⟶ F|_U`, read as a
section of `F` over `U`. -/
noncomputable def splittingBasisSection
    (F : SheafOfModules.{u} (structureSheafRing X)) (U : Opens X.carrier) (n : ℕ)
    (p : SheafOfModules.free (R := (structureSheafRing X).over U)
      (ULift.{u} (Fin n)) ⟶ F.over U) (j : Fin n) : F.val.obj (op U) :=
  ((SheafOfModules.ιFree (R := (structureSheafRing X).over U) (ULift.up j) ≫ p).val.app
    (op (Over.mk (𝟙 U)))).hom (1 : X.presheaf.obj (op U))

/-- The local functional `e_j^* ∘ i` attached to a map `i : F|_U ⟶ O_U^{⊕n}`. -/
noncomputable def splittingDualSection
    (F : SheafOfModules.{u} (structureSheafRing X)) (U : Opens X.carrier) (n : ℕ)
    (i : F.over U ⟶
      SheafOfModules.free (R := (structureSheafRing X).over U) (ULift.{u} (Fin n)))
    (j : Fin n) : (dualSheaf X F).val.obj (op U) :=
  i.val ≫ (freeCoordinate X U n j).val

/-- **The dual basis attached to a splitting.** If `i ≫ p = 𝟙` exhibits `F|_U` as a retract of
`O_U^{⊕n}`, then every local section of `F` over an object `V` of the slice site over `U` is
the sum of its coordinates times the restricted basis sections. -/
theorem splitting_dualBasis
    (F : SheafOfModules.{u} (structureSheafRing X)) (U : Opens X.carrier) (n : ℕ)
    (i : F.over U ⟶
      SheafOfModules.free (R := (structureSheafRing X).over U) (ULift.{u} (Fin n)))
    (p : SheafOfModules.free (R := (structureSheafRing X).over U)
      (ULift.{u} (Fin n)) ⟶ F.over U) (hip : i ≫ p = 𝟙 _)
    (V : (Over U)ᵒᵖ) (g : F.val.obj (op V.unop.left)) :
    ∑ j : Fin n, dualValue X F (splittingDualSection X F U n i j) V g •
      resSection X F V (splittingBasisSection X F U n p j) = g := by
  classical
  let R := (structureSheafRing X).over U
  let a (j : Fin n) : SheafOfModules.unit R ⟶ F.over U :=
    SheafOfModules.ιFree (ULift.up j) ≫ p
  let b (j : Fin n) : F.over U ⟶ SheafOfModules.unit R := i ≫ freeCoordinate X U n j
  have hq (j : Fin n) (k : ULift.{u} (Fin n)) :
      SheafOfModules.ιFree (R := R) k ≫ freeCoordinate X U n j =
        if k = ULift.up j then 𝟙 _ else 0 := Sigma.ι_comp_desc _ _
  have hsumfree : ∑ j : Fin n,
      freeCoordinate X U n j ≫ SheafOfModules.ιFree (R := R) (ULift.up j) =
      𝟙 (SheafOfModules.free (R := R) (ULift.{u} (Fin n))) := by
    apply Sigma.hom_ext
    intro k
    obtain ⟨k⟩ := k
    change SheafOfModules.ιFree (R := R) (ULift.up k) ≫
        (∑ j : Fin n, freeCoordinate X U n j ≫ SheafOfModules.ιFree (ULift.up j)) =
      SheafOfModules.ιFree (R := R) (ULift.up k) ≫
        𝟙 (SheafOfModules.free (R := R) (ULift.{u} (Fin n)))
    rw [Preadditive.comp_sum, Category.comp_id, Finset.sum_eq_single k]
    · rw [← Category.assoc, hq k (ULift.up k)]
      simp
    · intro j _ hjk
      rw [← Category.assoc, hq j (ULift.up k)]
      simp [Ne.symm hjk]
    · simp
  have hab : ∑ j : Fin n, b j ≫ a j = 𝟙 (F.over U) := by
    dsimp only [a, b]
    simp only [Category.assoc]
    rw [← Preadditive.comp_sum]
    simp_rw [← Category.assoc]
    rw [← Preadditive.sum_comp, hsumfree, Category.id_comp, hip]
  have ha (j : Fin n) :
      resSection X F V (splittingBasisSection X F U n p j) =
      unitMapValue X F (a j) V (1 : X.presheaf.obj (op V.unop.left)) := by
    have h := PresheafOfModules.naturality_apply (a j).val
      (Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 U)).op (1 : X.presheaf.obj (op U))
    change unitMapValue X F (a j) V ((X.presheaf.map V.unop.hom.op).hom 1) =
      resSection X F V (splittingBasisSection X F U n p j) at h
    rw [map_one] at h
    exact h.symm
  have hlin (j : Fin n) (c : X.presheaf.obj (op V.unop.left)) :
      unitMapValue X F (a j) V c = c • unitMapValue X F (a j) V 1 := by
    refine Eq.trans (congrArg (unitMapValue X F (a j) V)
      (mul_one (M := X.presheaf.obj (op V.unop.left)) c).symm) ?_
    exact ((a j).val.app V).hom.map_smul c (1 : X.presheaf.obj (op V.unop.left))
  have hterm (j : Fin n) :
      dualValue X F (splittingDualSection X F U n i j) V g •
        resSection X F V (splittingBasisSection X F U n p j) =
      ((b j ≫ a j).val.app V).hom g :=
    (congrArg (fun z : F.val.obj (op V.unop.left) =>
      dualValue X F (splittingDualSection X F U n i j) V g • z) (ha j)).trans
        (hlin j (dualValue X F (splittingDualSection X F U n i j) V g)).symm
  have hev (s : Finset (Fin n)) :
      ((∑ j ∈ s, b j ≫ a j).val.app V).hom g =
        ∑ j ∈ s, ((b j ≫ a j).val.app V).hom g := by
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      change ((b j ≫ a j).val.app V).hom g +
        ((∑ j ∈ s, b j ≫ a j).val.app V).hom g = _
      rw [ih]
  refine Eq.trans (Finset.sum_congr rfl fun j _ => hterm j) ?_
  refine Eq.trans (hev Finset.univ).symm ?_
  exact congrArg (fun q : F.over U ⟶ F.over U => (q.val.app V).hom g) hab

/-- **The identity endomorphism as a global section of `SheafHom(F, F)`**: the morphism
`O_X ⟶ SheafHom(F, F)` whose value on every open is the identity of the restricted sheaf. -/
noncomputable def identityEndomorphism
    (F : SheafOfModules.{u} (structureSheafRing X)) :
    SheafOfModules.unit (structureSheafRing X) ⟶ sheafHom X F F :=
  (sheafHom X F F).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun U => 𝟙 ((restrFun X.presheaf U.unop).obj F.val))
      (by
        intro U V f
        change homRestr X.presheaf F.val F.val f.unop (𝟙 _) = 𝟙 _
        simp [homRestr]))

/-- The value of `identityEndomorphism` at `1` is the identity. -/
theorem identityEndomorphism_apply_one
    (F : SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ) :
    ((identityEndomorphism X F).val.app U).hom (1 : X.presheaf.obj U) =
      𝟙 ((restrFun X.presheaf U.unop).obj F.val) :=
  congrArg (fun s : (sheafHom X F F).sections => s.val U)
    ((sheafHom X F F).unitHomEquiv.apply_symm_apply _)

/-- **The coevaluation `O_X ⟶ F ⊗ F^∨`** of Stacks 0FNV: the inverse image of the identity
endomorphism under the rank-one isomorphism `F ⊗ F^∨ ≅ SheafHom(F, F)`. -/
@[stacks 0FNV "coevaluation"]
noncomputable def coevaluation
    (F : SheafOfModules.{u} (structureSheafRing X))
    (hF : IsLocallyFiniteFreeSummand X F) :
    SheafOfModules.unit (structureSheafRing X) ⟶
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj
        ((dualSheaf X F))) :=
  identityEndomorphism X F ≫ @inv _ _ _ _ (tensorDualToEndomorphism X F)
    (tensorDualToEndomorphism_isIso X F hF)

/-- Under the rank-one isomorphism, the coevaluation is the identity endomorphism. -/
@[stacks 0FNV "coevaluation"]
theorem coevaluation_comp_tensorDualToEndomorphism
    (F : SheafOfModules.{u} (structureSheafRing X))
    (hF : IsLocallyFiniteFreeSummand X F) :
    coevaluation X F hF ≫ tensorDualToEndomorphism X F = identityEndomorphism X F := by
  have hI := tensorDualToEndomorphism_isIso X F hF
  change (identityEndomorphism X F ≫ @inv _ _ _ _ (tensorDualToEndomorphism X F) hI) ≫
    tensorDualToEndomorphism X F = _
  exact (Category.assoc _ _ _).trans ((congrArg (identityEndomorphism X F ≫ ·)
    (@IsIso.inv_hom_id _ _ _ _ _ hI)).trans (Category.comp_id _))

/-- **Stacks 0FNV.** On an open `U` carrying a splitting `i ≫ p = 𝟙` of `F|_U` through a
finite free module, the value of the coevaluation at `1` is `∑ j, p(e j) ⊗ (e j)^* ∘ i`. The
left-hand side does not mention the splitting, so the displayed sum is independent of it. -/
@[stacks 0FNV "coevaluation"]
theorem coevaluation_apply_eq_sum_of_retract
    (F : SheafOfModules.{u} (structureSheafRing X))
    (hF : IsLocallyFiniteFreeSummand X F) (U : Opens X.carrier) (n : ℕ)
    (i : F.over U ⟶
      SheafOfModules.free (R := (structureSheafRing X).over U) (ULift.{u} (Fin n)))
    (p : SheafOfModules.free (R := (structureSheafRing X).over U)
      (ULift.{u} (Fin n)) ⟶ F.over U) (hip : i ≫ p = 𝟙 _) :
    ((coevaluation X F hF).val.app (op U)).hom (1 : X.presheaf.obj (op U)) =
      ∑ j : Fin n, toTensorSheafSection X F (dualSheaf X F) (op U)
        (splittingBasisSection X F U n p j ⊗ₜ[X.presheaf.obj (op U)]
          splittingDualSection X F U n i j) := by
  classical
  have hval : Mono (tensorDualToEndomorphism X F).val :=
    @IsIso.mono_of_iso _ _ _ _ _ ((SheafOfModules.forget (structureSheafRing X)).mapIso
      (@asIso _ _ _ _ (tensorDualToEndomorphism X F)
        (tensorDualToEndomorphism_isIso X F hF))).isIso_hom
  apply PresheafOfModules.injective_of_mono
    (tensorDualToEndomorphism X F).val (op U)
  have hlhs : ((tensorDualToEndomorphism X F).val.app (op U)).hom
      (((coevaluation X F hF).val.app (op U)).hom (1 : X.presheaf.obj (op U))) =
      ((identityEndomorphism X F).val.app (op U)).hom (1 : X.presheaf.obj (op U)) :=
    congrArg (fun q : SheafOfModules.unit (structureSheafRing X) ⟶ sheafHom X F F =>
      (q.val.app (op U)).hom (1 : X.presheaf.obj (op U)))
      (coevaluation_comp_tensorDualToEndomorphism X F hF)
  refine hlhs.trans ?_
  refine Eq.trans (identityEndomorphism_apply_one X F (op U)) ?_
  refine Eq.trans ?_ (map_sum ((tensorDualToEndomorphism X F).val.app (op U)).hom
    (fun j : Fin n => toTensorSheafSection X F (dualSheaf X F) (op U)
      (splittingBasisSection X F U n p j ⊗ₜ[X.presheaf.obj (op U)]
        splittingDualSection X F U n i j)) Finset.univ).symm
  apply PresheafOfModules.hom_ext
  intro V
  ext g
  refine Eq.trans ?_ (sheafHom_sum_apply X F F U Finset.univ
    (fun j : Fin n => ((tensorDualToEndomorphism X F).val.app (op U)).hom
      (toTensorSheafSection X F (dualSheaf X F) (op U)
        (splittingBasisSection X F U n p j ⊗ₜ[X.presheaf.obj (op U)]
          splittingDualSection X F U n i j))) V g).symm
  refine Eq.trans ?_ (Finset.sum_congr rfl fun j _ =>
    (tensorDualToEndomorphism_tmul_apply X F U (splittingBasisSection X F U n p j)
      (splittingDualSection X F U n i j) V g).symm)
  exact (splitting_dualBasis X F U n i p hip V g).symm

end Stacks.SheafOfModules.OnSpace
