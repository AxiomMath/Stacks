module

public import StacksFrontier.AlgebraicGeometry.Descent.Modules.TensorEqualizer.Comparison

/-!
# The base-changed descent diagram is an equalizer

For a universally injective ring map `R → A` and a module descent datum, the base change to
`A` of the equalizer defining its pushforward is again an equalizer (Tag 08X7). The limit fork
is obtained by dualizing: the split equalizer of the descent diagram becomes a split
coequalizer of character modules, which is spread over the tensor factors and reflected back.
-/

@[expose] public section

universe u v w

noncomputable section

namespace ModuleCat

open CategoryTheory TensorProduct
open scoped ModuleCat.Algebra

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/-- Dualizing an isomorphism and its inverse gives mutually inverse maps. -/
private theorem dual_symm_comp_dual {S : Type*} [CommRing S] {M N : Type*} [AddCommGroup M]
    [AddCommGroup N] [Module S M] [Module S N] (e : M ≃ₗ[S] N) :
    (CharacterModule.dual e.symm.toLinearMap).comp (CharacterModule.dual e.toLinearMap) =
      LinearMap.id := by
  ext χ x
  exact congrArg χ (e.apply_symm_apply x)

/-- Dualizing a commuting square of linear maps gives a commuting square of character modules. -/
private theorem dual_comp_comm {S : Type*} [CommRing S] {M N P Q : Type*} [AddCommGroup M]
    [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q] [Module S M] [Module S N] [Module S P]
    [Module S Q] {f : N →ₗ[S] Q} {e : M →ₗ[S] N} {e' : P →ₗ[S] Q} {f' : M →ₗ[S] P}
    (h : f.comp e = e'.comp f') :
    (CharacterModule.dual e).comp (CharacterModule.dual f) =
      (CharacterModule.dual f').comp (CharacterModule.dual e') := by
  rw [← CharacterModule.dual_comp, ← CharacterModule.dual_comp, h]

/-- A split coequalizer of linear maps transports along isomorphisms conjugating its maps. -/
private theorem nonempty_isSplitCoequalizer_of_conj.{t} {S : Type*} [CommRing S]
    {Y X Z Y' X' Z' : Type t} [AddCommGroup Y] [AddCommGroup X] [AddCommGroup Z]
    [AddCommGroup Y'] [AddCommGroup X'] [AddCommGroup Z'] [Module S Y] [Module S X] [Module S Z]
    [Module S Y'] [Module S X'] [Module S Z'] {α β : Y →ₗ[S] X} {π : X →ₗ[S] Z}
    (hs : IsSplitCoequalizer (ModuleCat.ofHom α) (ModuleCat.ofHom β) (ModuleCat.ofHom π))
    (u : Y' ≃ₗ[S] Y) (v : X' ≃ₗ[S] X) (w : Z' ≃ₗ[S] Z) {f g : Y' →ₗ[S] X'} {p : X' →ₗ[S] Z'}
    (hf : f = (v.symm.toLinearMap.comp α).comp u.toLinearMap)
    (hg : g = (v.symm.toLinearMap.comp β).comp u.toLinearMap)
    (hp : p = (w.symm.toLinearMap.comp π).comp v.toLinearMap) :
    Nonempty (IsSplitCoequalizer (ModuleCat.ofHom f) (ModuleCat.ofHom g) (ModuleCat.ofHom p)) := by
  have hc := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hs.condition)
  have hr := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hs.rightSection_π)
  have hb := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hs.leftSection_bottom)
  have ht := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hs.leftSection_top)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id, LinearMap.comp_apply,
    LinearMap.id_apply] at hc hr hb ht
  subst hf hg hp
  refine ⟨{
    rightSection := ModuleCat.ofHom
      ((v.symm.toLinearMap.comp hs.rightSection.hom).comp w.toLinearMap)
    leftSection := ModuleCat.ofHom
      ((u.symm.toLinearMap.comp hs.leftSection.hom).comp v.toLinearMap)
    condition := ?_
    rightSection_π := ?_
    leftSection_bottom := ?_
    leftSection_top := ?_ }⟩ <;>
  · apply ModuleCat.hom_ext
    ext x
    simp [hc, hr, hb, ht]

/-- The equalizer property of the base-changed descent diagram, in `Nonempty` form: the limit
cone is produced by dualizing, so it is obtained from a choice. -/
public theorem tensorPushforward_isEqualizer_aux
    (h : Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{u}
      (Algebra.linearMap R A))
    (D : DescentData.{u, v, w} R A) :
    Nonempty (CategoryTheory.Limits.IsLimit
      (CategoryTheory.Limits.Fork.ofι
        (ModuleCat.ofHom (tensorPushforwardComparison R A D))
        (tensorPushforwardComparison_condition R A D))) := by
  classical
  let : Module A (↑D.module) := D.module.isModule
  let : Module R (↑D.module) := Module.compHom (↑D.module) (algebraMap R A)
  let F := ModuleCat.restrictScalars (algebraMap R A)
  let POrig : ModuleCat A := ModuleCat.of A (ULift.{v} D.module)
  let QOrig : ModuleCat A := ModuleCat.of A (A ⊗[R] restrictModule R A D.module)
  let YOrig : ModuleCat A := ModuleCat.of A ((A ⊗[R] A) ⊗[R] restrictModule R A D.module)
  let PObj : ModuleCat R := F.obj POrig
  let QObj : ModuleCat R := F.obj QOrig
  let YObj : ModuleCat R := F.obj YOrig
  let P := (PObj : Type _)
  let Q := (QObj : Type _)
  let Y := (YObj : Type _)
  let : AddCommGroup P := PObj.isAddCommGroup
  let : Module R P := PObj.isModule
  let : AddCommGroup Q := QObj.isAddCommGroup
  let : Module R Q := QObj.isModule
  let : AddCommGroup Y := YObj.isAddCommGroup
  let : Module R Y := YObj.isModule
  let : Module A P := POrig.isModule
  let : Module A Q := QOrig.isModule
  let : Module A Y := YOrig.isModule
  let I₀ := invariantSubmodule R A D
  let I := ULift.{v} I₀
  let eC : (D.module : Type w) ≃ₗ[R] restrictModule R A D.module := {
    toFun := fun x => x
    invFun := fun x => x
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    left_inv _ := rfl
    right_inv _ := rfl }
  let eP : P ≃ₗ[R] restrictModule R A D.module := {
    toFun := fun x => eC x.down
    invFun := fun x => ULift.up (eC.symm x)
    map_add' := by intros; rfl
    map_smul' := by intro r x; rfl
    left_inv := by intro x; cases x; rfl
    right_inv _ := rfl }
  let eI : I ≃ₗ[R] I₀ := ULift.moduleEquiv.{u, w, v} (R := R) (M := I₀)
  let i : I →ₗ[R] P := eP.symm.toLinearMap.comp (I₀.subtype.comp eI.toLinearMap)
  let k : P →ₗ[R] Q :=
    (F.map (ModuleCat.ofHom (DescentData.descentComparisonHom R A D))).hom
  let l : P →ₗ[R] Q := {
    toFun := fun m => (1 : A) ⊗ₜ[R] (eP m)
    map_add' x y := by rw [eP.map_add, TensorProduct.tmul_add]; rfl
    map_smul' := by
      intro r x
      rw [eP.map_smul]
      change (1 : A) ⊗ₜ[R] (r • eP x) =
        (algebraMap R A r) • ((1 : A) ⊗ₜ[R] eP x)
      rw [← TensorProduct.smul_tmul]
      simp [Algebra.smul_def, TensorProduct.smul_tmul'] }
  let f : Q →ₗ[R] Y :=
    (F.map (ModuleCat.ofHom (DescentData.transition12AfterUnitHom R A D))).hom
  let g : Q →ₗ[R] Y :=
    (F.map (ModuleCat.ofHom (DescentData.rightUnitBaseChangeHom R A D))).hom
  have hkEval (m : P) : k m = DescentData.descentComparisonHom R A D m := rfl
  have hki : k.comp i = l.comp i := by
    ext m
    dsimp [k, i, l]
    cases m with
    | up m =>
        change DescentData.descentComparisonHom R A D (ULift.up (eC.symm m.1)) =
          (1 : A) ⊗ₜ[R] eC (eC.symm m.1)
        rw [DescentData.descentComparisonHom_apply]
        exact m.2
  have hi : Function.Injective i := by
    intro x y hxy
    apply eI.injective
    apply Subtype.ext
    simpa [i] using congrArg eP hxy
  have hexact : Function.Exact i (l - k) := by
    apply LinearMap.exact_of_comp_of_mem_range
    · refine LinearMap.ext fun m => ?_
      have hm := LinearMap.congr_fun hki m
      simp only [LinearMap.comp_apply] at hm
      simp [hm]
    · intro x hx
      have hx' : k x = l x := (sub_eq_zero.mp (LinearMap.mem_ker.mp hx)).symm
      cases x with
      | up x =>
          have hmem : x ∈ I₀ := by
            change DescentData.descentComparisonHom R A D (ULift.up x) =
              (1 : A) ⊗ₜ[R] eC x at hx'
            rwa [DescentData.descentComparisonHom_apply] at hx'
          refine ⟨ULift.up ⟨eC x, hmem⟩, ?_⟩
          change (ULift.moduleEquiv.{u, w, v} (R := R) (M := D.module)).symm
            (eC.symm (eC x)) = ULift.up x
          rw [eC.symm_apply_apply]
          rfl
  let h0 := Classical.choice (DescentData.isSplitEqualizer_descentComparison R A D)
  let hR := h0.map F
  have hsplitR : IsSplitEqualizer (ModuleCat.ofHom f) (ModuleCat.ofHom g)
      (ModuleCat.ofHom k) := hR
  let q := characterDual_splitCoequalizer_of_splitEqualizer k f g hsplitR
  let hsf := exists_unitBaseChange_characterSectionFamily (R := R) (A := A) h
  let sFam := Classical.choose hsf
  have hsFamUnit := (Classical.choose_spec hsf).1
  have hsFamNat := (Classical.choose_spec hsf).2
  let eQ : (A ⊗[R] restrictModule R A D.module) ≃ₗ[R] Q := {
    toFun := fun x => x
    invFun := fun x => x
    map_add' := by intros; rfl
    map_smul' := by
      intro r x
      let lhs : (A ⊗[R] restrictModule R A D.module) →+ (A ⊗[R] restrictModule R A D.module) := {
        toFun := fun x => r • x
        map_zero' := by simp
        map_add' := fun x y => smul_add r x y }
      let rhs : Q →+ Q := {
        toFun := fun x => (RingHom.id R) r • x
        map_zero' := by simp
        map_add' := fun x y => smul_add _ _ _ }
      change lhs x = rhs x
      induction x using TensorProduct.inductionOn with
      | add x y hx hy =>
          rw [lhs.map_add, hx, hy]
          exact (rhs.map_add x y).symm
      | tmul a m =>
          change (r • a) ⊗ₜ[R] m = (algebraMap R A r * a) ⊗ₜ[R] m
          exact congrArg (fun b : A => b ⊗ₜ[R] m) (Algebra.smul_def r a)
    left_inv _ := rfl
    right_inv _ := rfl }
  let eY : ((A ⊗[R] A) ⊗[R] restrictModule R A D.module) ≃ₗ[R] Y := {
    toFun := fun x => x
    invFun := fun x => x
    map_add' := by intros; rfl
    map_smul' := by
      intro r x
      let lhs : ((A ⊗[R] A) ⊗[R] restrictModule R A D.module) →+
          ((A ⊗[R] A) ⊗[R] restrictModule R A D.module) := {
        toFun := fun x => r • x
        map_zero' := by simp
        map_add' := fun x y => smul_add r x y }
      let rhs : Y →+ Y := {
        toFun := fun x => (RingHom.id R) r • x
        map_zero' := by simp
        map_add' := fun x y => smul_add _ _ _ }
      change lhs x = rhs x
      induction x using TensorProduct.inductionOn with
      | add x y hx hy =>
          rw [lhs.map_add, hx, hy]
          exact (rhs.map_add x y).symm
      | tmul p m =>
          induction p using TensorProduct.inductionOn with
          | add p p' hp hp' =>
              rw [TensorProduct.add_tmul]
              rw [lhs.map_add, hp, hp']
              exact (rhs.map_add _ _).symm
          | tmul a b =>
              change ((r • a) ⊗ₜ[R] b) ⊗ₜ[R] m =
                ((algebraMap R A r * a) ⊗ₜ[R] b) ⊗ₜ[R] m
              exact congrArg (fun c : A => (c ⊗ₜ[R] b) ⊗ₜ[R] m)
                (Algebra.smul_def r a)
    left_inv _ := rfl
    right_inv _ := rfl }
  have heQApply (x : A ⊗[R] restrictModule R A D.module) : eQ x = x := rfl
  have heYApply (x : (A ⊗[R] A) ⊗[R] restrictModule R A D.module) : eY x = x := rfl
  let pA : (A ⊗[R] P) ≃ₗ[R] Q :=
    (TensorProduct.congr (LinearEquiv.refl R A) eP).trans eQ
  let qA : (A ⊗[R] Q) ≃ₗ[R] Y :=
    (TensorProduct.congr (LinearEquiv.refl R A) eQ.symm).trans <|
      (TensorProduct.assoc R A A (restrictModule R A D.module)).symm.trans eY
  let tQ : Q →ₗ[R] Y :=
    qA.toLinearMap.comp (unitBaseChangeMap (R := R) (A := A) Q)
  have hfEval (x : Q) :
      f x = DescentData.transition12AfterUnit R A D x := by
    change ((DescentData.transition12AfterUnitHom R A D).restrictScalars R) x = _
    rw [DescentData.transition12AfterUnitHom_restrictScalars]
  have hgEval (x : Q) :
      g x = DescentData.rightUnitBaseChange R A D x := by
    change ((DescentData.rightUnitBaseChangeHom R A D).restrictScalars R) x = _
    rw [DescentData.rightUnitBaseChangeHom_restrictScalars]
  have hfEvalRaw (x : A ⊗[R] restrictModule R A D.module) :
      f (eQ x) = DescentData.transition12AfterUnit R A D x := by
    simpa only [heQApply] using hfEval (eQ x)
  have hgEvalRaw (x : A ⊗[R] restrictModule R A D.module) :
      g (eQ x) = DescentData.rightUnitBaseChange R A D x := by
    simpa only [heQApply] using hgEval (eQ x)
  have hpATmul (a : A) (m : P) :
      pA.toLinearMap (a ⊗ₜ[R] m) = eQ (a ⊗ₜ[R] eP m) := by
    simp [pA, TensorProduct.congr_tmul]
  have hlFormula (m : P) : l m = eQ ((1 : A) ⊗ₜ[R] eP m) := rfl
  have hkRaw (m : P) : eQ.symm (k m) =
      DescentData.descentComparisonLeft R A D m.down := by
    cases m with
    | up x =>
        rw [hkEval (ULift.up x), DescentData.descentComparisonHom_apply]
        rfl
  have hlRaw (m : P) : eQ.symm (l m) =
      (1 : A) ⊗ₜ[R] eP m := by
    rw [hlFormula m, eQ.symm_apply_apply]
  have hunitP : pA.symm.toLinearMap.comp l =
      unitBaseChangeMap (R := R) (A := A) P := by
    ext x
    apply pA.injective
    simp only [LinearMap.comp_apply]
    change pA (pA.symm (l x)) = pA (unitBaseChangeMap (R := R) (A := A) P x)
    rw [pA.apply_symm_apply]
    rfl
  have hunitQ : qA.symm.toLinearMap.comp tQ =
      unitBaseChangeMap (R := R) (A := A) Q := by
    ext x
    apply qA.injective
    simp [tQ, unitBaseChangeMap]
  have hmapK : f.comp pA.toLinearMap =
      qA.toLinearMap.comp (LinearMap.lTensor A k) := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy, map_add]
    | tmul a x =>
        cases x with
        | up x =>
            simp only [LinearMap.comp_apply]
            let px : P := ULift.up x
            change f (pA.toLinearMap (a ⊗ₜ[R] px)) =
              qA.toLinearMap ((LinearMap.lTensor A k) (a ⊗ₜ[R] px))
            rw [hpATmul, hfEvalRaw, LinearMap.lTensor_tmul, show eP px = eC x from rfl]
            dsimp [qA]
            change eY (DescentData.transition12AfterUnit R A D
                (a ⊗ₜ[R] eC x)) =
              eY ((TensorProduct.assoc R A A (restrictModule R A D.module)).symm
                ((TensorProduct.congr (LinearEquiv.refl R A) eQ.symm)
                  (a ⊗ₜ[R] k px)))
            apply congrArg eY
            rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, hkRaw px]
            simp [DescentData.transition12AfterUnit, transition12,
              DescentData.descentComparisonLeft]
            rfl
  have hmapL : g.comp pA.toLinearMap =
      qA.toLinearMap.comp (LinearMap.lTensor A l) := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy, map_add]
    | tmul a x =>
        cases x with
        | up x =>
            simp only [LinearMap.comp_apply]
            let px : P := ULift.up x
            change g (pA.toLinearMap (a ⊗ₜ[R] px)) =
              qA.toLinearMap ((LinearMap.lTensor A l) (a ⊗ₜ[R] px))
            rw [hpATmul, hgEvalRaw, LinearMap.lTensor_tmul, show eP px = eC x from rfl]
            dsimp [qA]
            change eY (DescentData.rightUnitBaseChange R A D
                (a ⊗ₜ[R] eC x)) =
              eY ((TensorProduct.assoc R A A (restrictModule R A D.module)).symm
                ((TensorProduct.congr (LinearEquiv.refl R A) eQ.symm)
                  (a ⊗ₜ[R] l px)))
            apply congrArg eY
            rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, hlRaw px]
            simp [DescentData.rightUnitBaseChange, TensorProduct.assoc_symm_tmul]
            rfl
  have hmapK' : (LinearMap.lTensor A k).comp pA.symm.toLinearMap =
      qA.symm.toLinearMap.comp f := by
    ext x
    apply qA.injective
    simpa using (LinearMap.congr_fun hmapK (pA.symm x)).symm
  have hmapL' : (LinearMap.lTensor A l).comp pA.symm.toLinearMap =
      qA.symm.toLinearMap.comp g := by
    ext x
    apply qA.injective
    simpa using (LinearMap.congr_fun hmapL (pA.symm x)).symm
  have hpAunit : pA.toLinearMap.comp
      (unitBaseChangeMap (R := R) (A := A) P) = l := by
    ext x
    simpa using (congrArg pA (LinearMap.congr_fun hunitP x)).symm
  have hunitNatK : (LinearMap.lTensor A k).comp
      (unitBaseChangeMap (R := R) (A := A) P) =
      (unitBaseChangeMap (R := R) (A := A) Q).comp k := by
    ext x
    simp [unitBaseChangeMap]
  have hunitNatL : (LinearMap.lTensor A l).comp
      (unitBaseChangeMap (R := R) (A := A) P) =
      (unitBaseChangeMap (R := R) (A := A) Q).comp l := by
    ext x
    simp [unitBaseChangeMap]
  have hretKmap : tQ.comp k = f.comp l := by
    dsimp [tQ]
    rw [LinearMap.comp_assoc, ← hunitNatK, ← LinearMap.comp_assoc, ← hmapK, LinearMap.comp_assoc,
      hpAunit]
  have hretLmap : tQ.comp l = g.comp l := by
    dsimp [tQ]
    rw [LinearMap.comp_assoc, ← hunitNatL, ← LinearMap.comp_assoc, ← hmapL, LinearMap.comp_assoc,
      hpAunit]
  let sP : CharacterModule P →ₗ[R] CharacterModule Q :=
    (CharacterModule.dual pA.symm.toLinearMap).comp (sFam P)
  let sQ : CharacterModule Q →ₗ[R] CharacterModule Y :=
    (CharacterModule.dual qA.symm.toLinearMap).comp (sFam Q)
  let ρP : CharacterModule Q →ₗ[R] CharacterModule P := CharacterModule.dual l
  let ρQ : CharacterModule Y →ₗ[R] CharacterModule Q := CharacterModule.dual tQ
  have hsP : ρP.comp sP = LinearMap.id := by
    dsimp [ρP, sP]
    rw [← LinearMap.comp_assoc, ← CharacterModule.dual_comp l pA.symm.toLinearMap, hunitP]
    exact hsFamUnit P
  have hsQ : ρQ.comp sQ = LinearMap.id := by
    dsimp [ρQ, sQ]
    rw [← LinearMap.comp_assoc, ← CharacterModule.dual_comp tQ qA.symm.toLinearMap, hunitQ]
    exact hsFamUnit Q
  have hNatK : sP.comp (CharacterModule.dual k) =
      (CharacterModule.dual f).comp sQ := by
    dsimp [sP, sQ]
    rw [LinearMap.comp_assoc, hsFamNat, ← LinearMap.comp_assoc, ← CharacterModule.dual_comp,
      hmapK', CharacterModule.dual_comp, LinearMap.comp_assoc]
  have hNatL : sP.comp (CharacterModule.dual l) =
      (CharacterModule.dual g).comp sQ := by
    dsimp [sP, sQ]
    rw [LinearMap.comp_assoc, hsFamNat, ← LinearMap.comp_assoc, ← CharacterModule.dual_comp,
      hmapL', CharacterModule.dual_comp, LinearMap.comp_assoc]
  have hRetK : (CharacterModule.dual k).comp ρQ =
      ρP.comp (CharacterModule.dual f) := by
    dsimp [ρP, ρQ]
    rw [← CharacterModule.dual_comp k tQ, ← CharacterModule.dual_comp l f,
      hretKmap]
  have hRetL : (CharacterModule.dual l).comp ρQ =
      ρP.comp (CharacterModule.dual g) := by
    dsimp [ρP, ρQ]
    rw [← CharacterModule.dual_comp l tQ, ← CharacterModule.dual_comp l g,
      hretLmap]
  have hδi : (CharacterModule.dual i).comp ρP =
      (CharacterModule.dual i).comp (CharacterModule.dual k) := by
    dsimp [ρP]
    rw [← CharacterModule.dual_comp i l, ← CharacterModule.dual_comp i k, hki]
  let hsplitDualI := characterDual_splitCoequalizer_of_splitCoequalizer
    l f g k i k l hi hki hexact q sP sQ ρP ρQ hsP hsQ hNatK hNatL hRetK hRetL hδi
  let qTensor := characterDual_splitCoequalizer_tensor_any (A := A) hsplitDualI
  let pI : (A ⊗[R] I) ≃ₗ[R] (A ⊗[R] I₀) :=
    TensorProduct.congr (LinearEquiv.refl R A) eI
  let dP : CharacterModule Q →ₗ[R] CharacterModule (A ⊗[R] P) :=
    CharacterModule.dual pA.toLinearMap
  let dPInv : CharacterModule (A ⊗[R] P) →ₗ[R] CharacterModule Q :=
    CharacterModule.dual pA.symm.toLinearMap
  let dQ : CharacterModule Y →ₗ[R] CharacterModule (A ⊗[R] Q) :=
    CharacterModule.dual qA.toLinearMap
  let dQInv : CharacterModule (A ⊗[R] Q) →ₗ[R] CharacterModule Y :=
    CharacterModule.dual qA.symm.toLinearMap
  let dI : CharacterModule (A ⊗[R] I₀) →ₗ[R] CharacterModule (A ⊗[R] I) :=
    CharacterModule.dual pI.toLinearMap
  let dIInv : CharacterModule (A ⊗[R] I) →ₗ[R] CharacterModule (A ⊗[R] I₀) :=
    CharacterModule.dual pI.symm.toLinearMap
  let α₀ : CharacterModule (A ⊗[R] Q) →ₗ[R] CharacterModule (A ⊗[R] P) :=
    CharacterModule.dual (LinearMap.lTensor A k)
  let β₀ : CharacterModule (A ⊗[R] Q) →ₗ[R] CharacterModule (A ⊗[R] P) :=
    CharacterModule.dual (LinearMap.lTensor A l)
  let π₀ : CharacterModule (A ⊗[R] P) →ₗ[R] CharacterModule (A ⊗[R] I) :=
    CharacterModule.dual (LinearMap.lTensor A i)
  have hdP : dPInv.comp dP = LinearMap.id := dual_symm_comp_dual pA
  have hdQ : dQInv.comp dQ = LinearMap.id := dual_symm_comp_dual qA
  have hdI : dIInv.comp dI = LinearMap.id := dual_symm_comp_dual pI
  have hdP' : dP.comp dPInv = LinearMap.id := dual_symm_comp_dual pA.symm
  have hdQ' : dQ.comp dQInv = LinearMap.id := dual_symm_comp_dual qA.symm
  have hdI' : dI.comp dIInv = LinearMap.id := dual_symm_comp_dual pI.symm
  have hαK : dP.comp (CharacterModule.dual f) = α₀.comp dQ := dual_comp_comm hmapK
  have hβK : dP.comp (CharacterModule.dual g) = β₀.comp dQ := dual_comp_comm hmapL
  have hα : CharacterModule.dual f = (dPInv.comp α₀).comp dQ := by
    rw [LinearMap.comp_assoc, ← hαK, ← LinearMap.comp_assoc, hdP, LinearMap.id_comp]
  have hβ : CharacterModule.dual g = (dPInv.comp β₀).comp dQ := by
    rw [LinearMap.comp_assoc, ← hβK, ← LinearMap.comp_assoc, hdP, LinearMap.id_comp]
  let cmpR := (tensorPushforwardComparison R A D).restrictScalars R
  let cmpQ := eQ.toLinearMap.comp cmpR
  have hcmpQ : cmpQ = eQ.toLinearMap.comp cmpR := rfl
  have hIncQ : cmpQ =
      pA.toLinearMap.comp ((LinearMap.lTensor A i).comp pI.symm.toLinearMap) := by
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul a m =>
        simp [cmpQ, cmpR, tensorPushforwardComparison, pA, pI, i, eI, eP, eC, eQ]
        rfl
  have hπQ : CharacterModule.dual cmpQ =
      (dIInv.comp π₀).comp dP := by
    rw [hIncQ, CharacterModule.dual_comp
      ((LinearMap.lTensor A i).comp pI.symm.toLinearMap) pA.toLinearMap,
      CharacterModule.dual_comp pI.symm.toLinearMap (LinearMap.lTensor A i)]
  let r : CharacterModule (A ⊗[R] I₀) →ₗ[R] CharacterModule Q :=
    (dPInv.comp qTensor.rightSection.hom).comp dI
  let t : CharacterModule Q →ₗ[R] CharacterModule Y :=
    (dQInv.comp qTensor.leftSection.hom).comp dP
  obtain ⟨hsplitQ⟩ := nonempty_isSplitCoequalizer_of_conj qTensor
    (.ofLinearMap dQ dQInv hdQ' hdQ) (.ofLinearMap dP dPInv hdP' hdP)
    (.ofLinearMap dI dIInv hdI' hdI) hα hβ hπQ
  let dE : CharacterModule Q →ₗ[R]
      CharacterModule (A ⊗[R] restrictModule R A D.module) :=
    CharacterModule.dual eQ.toLinearMap
  let dEInv : CharacterModule (A ⊗[R] restrictModule R A D.module) →ₗ[R]
      CharacterModule Q := CharacterModule.dual eQ.symm.toLinearMap
  let dY : CharacterModule Y →ₗ[R]
      CharacterModule ((A ⊗[R] A) ⊗[R] restrictModule R A D.module) :=
    CharacterModule.dual eY.toLinearMap
  let dYInv : CharacterModule ((A ⊗[R] A) ⊗[R] restrictModule R A D.module) →ₗ[R]
      CharacterModule Y := CharacterModule.dual eY.symm.toLinearMap
  have hdE : dEInv.comp dE = LinearMap.id := dual_symm_comp_dual eQ
  have hdE' : dE.comp dEInv = LinearMap.id := dual_symm_comp_dual eQ.symm
  have hdY : dYInv.comp dY = LinearMap.id := dual_symm_comp_dual eY
  have hdY' : dY.comp dYInv = LinearMap.id := dual_symm_comp_dual eY.symm
  have hfCompat : f.comp eQ.toLinearMap =
      eY.toLinearMap.comp (DescentData.transition12AfterUnit R A D) := by
    exact LinearMap.ext fun x => (hfEvalRaw x).trans (heYApply _).symm
  have hgCompat : g.comp eQ.toLinearMap =
      eY.toLinearMap.comp (DescentData.rightUnitBaseChange R A D) := by
    exact LinearMap.ext fun x => (hgEvalRaw x).trans (heYApply _).symm
  have hαCompat : dE.comp (CharacterModule.dual f) =
      (CharacterModule.dual (DescentData.transition12AfterUnit R A D)).comp dY :=
    dual_comp_comm hfCompat
  have hβCompat : dE.comp (CharacterModule.dual g) =
      (CharacterModule.dual (DescentData.rightUnitBaseChange R A D)).comp dY :=
    dual_comp_comm hgCompat
  have hαRaw : CharacterModule.dual (DescentData.transition12AfterUnit R A D) =
      (dE.comp (CharacterModule.dual f)).comp dYInv := by
    rw [hαCompat, LinearMap.comp_assoc, hdY', LinearMap.comp_id]
  have hβRaw : CharacterModule.dual (DescentData.rightUnitBaseChange R A D) =
      (dE.comp (CharacterModule.dual g)).comp dYInv := by
    rw [hβCompat, LinearMap.comp_assoc, hdY', LinearMap.comp_id]
  have hcmpDual : CharacterModule.dual cmpQ =
      (CharacterModule.dual cmpR).comp dE := by
    rw [hcmpQ, ← CharacterModule.dual_comp cmpR eQ.toLinearMap]
  have hπRaw : CharacterModule.dual cmpR = (CharacterModule.dual cmpQ).comp dEInv := by
    rw [hcmpDual, LinearMap.comp_assoc, hdE', LinearMap.comp_id]
  let rRaw : CharacterModule (A ⊗[R] I₀) →ₗ[R]
      CharacterModule (A ⊗[R] restrictModule R A D.module) :=
    dE.comp hsplitQ.rightSection.hom
  let tRaw : CharacterModule (A ⊗[R] restrictModule R A D.module) →ₗ[R]
      CharacterModule ((A ⊗[R] A) ⊗[R] restrictModule R A D.module) :=
    (dY.comp hsplitQ.leftSection.hom).comp dEInv
  obtain ⟨hsplitRaw⟩ := nonempty_isSplitCoequalizer_of_conj hsplitQ
    (.ofLinearMap dYInv dY hdY hdY') (.ofLinearMap dEInv dE hdE hdE') (.refl R _) hαRaw hβRaw hπRaw
  have hsplitRaw' : IsSplitCoequalizer
      (ModuleCat.ofHom (CharacterModule.dual
        ((DescentData.transition12AfterUnitHom R A D).restrictScalars R)))
      (ModuleCat.ofHom (CharacterModule.dual
        ((DescentData.rightUnitBaseChangeHom R A D).restrictScalars R)))
      (ModuleCat.ofHom (CharacterModule.dual cmpR)) := by
    simpa only [DescentData.transition12AfterUnitHom_restrictScalars,
      DescentData.rightUnitBaseChangeHom_restrictScalars] using hsplitRaw
  exact ⟨isLimitFork_of_characterDual_splitCoequalizer
    (tensorPushforwardComparison R A D)
    (DescentData.transition12AfterUnitHom R A D)
    (DescentData.rightUnitBaseChangeHom R A D)
    (tensorPushforwardComparison_condition R A D) hsplitRaw'⟩

/-- For a universally injective ring map, the displayed diagram of `A`-modules
is an equalizer. The middle and right objects and both parallel arrows use the
canonical identifications from the descent datum. -/
@[stacks 08X7 "equalizer"]
public noncomputable def tensorPushforward_isEqualizer
    (h : Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{u}
      (Algebra.linearMap R A))
    (D : DescentData.{u, v, w} R A) :
    CategoryTheory.Limits.IsLimit
      (CategoryTheory.Limits.Fork.ofι
        (ModuleCat.ofHom (tensorPushforwardComparison R A D))
        (tensorPushforwardComparison_condition R A D)) :=
  Classical.choice (tensorPushforward_isEqualizer_aux R A h D)

end ModuleCat

end
