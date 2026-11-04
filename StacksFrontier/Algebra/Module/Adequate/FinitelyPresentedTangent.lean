module

public import StacksFrontier.Algebra.Module.Adequate.Tangent
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Tangent modules of finitely presented modules

Let `A` be a commutative ring and let `F` be a module-valued functor on commutative
`A`-algebras whose tangent functor is right exact at every algebra, as recorded by
`AdequateFunctor.RightExactTangentFunctor`.  For an `A`-algebra `B` and a finitely
presented `B`-module `N`, the tangent module `TF(B, N)` is canonically isomorphic to
`TF(B, B) ⊗[B] N`, where both tangent modules carry the second `B`-module structure of
`AdequateFunctor.secondModuleStructure`.

## Main definitions

* `AdequateFunctor.tangentMapForElement`: the map `TF(B, B) → TF(B, N)` induced by
  `b ↦ b • n` for an element `n` of `N`.
* `AdequateFunctor.tangentTensorMap`: the resulting `B`-linear comparison map
  `TF(B, B) ⊗[B] N → TF(B, N)`.
* `AdequateFunctor.tangentTensorEquiv`: the comparison map for a finitely presented `N`,
  packaged with its defining formula on pure tensors, as a linear equivalence.

## Main results

* `AdequateFunctor.tangentTensorFreeMap_bijective`: the comparison map is bijective when
  `N` is finite free.
* `AdequateFunctor.tangentTensorEquiv`: the comparison map is an isomorphism for every
  finitely presented `N`.  The equivalence is specified on pure tensors rather than merely
  asserted to exist, which is what records its canonical character.

## References

* [Stacks Project, Tag 06ZB](https://stacks.math.columbia.edu/tag/06ZB)
* [Stacks Project, Tag 06ZD](https://stacks.math.columbia.edu/tag/06ZD)
-/

@[expose] public section

open CategoryTheory

namespace AdequateFunctor

universe u v w

/-- The morphism of algebra-module pairs `(B, M) ⟶ (B, N)` given by the identity of `B` and a
`B`-linear map `f : M →ₗ[B] N`. -/
def pairHom {A : Type u} [CommRing A] {B : Type v} [CommRing B]
    [Algebra A B] {M N : Type v} [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N] (f : M →ₗ[B] N) :
    ({ algebra := B, module := M } : AlgebraModulePair.{v} A) ⟶
      ({ algebra := B, module := N } : AlgebraModulePair.{v} A) :=
  ⟨AlgHom.id A B, f⟩

/-- For an element `n : N`, the map `TF(B, B) → TF(B, N)` obtained by applying the tangent
functor to the `B`-linear map `B → N`, `b ↦ b • n`. -/
noncomputable def tangentMapForElement {A : Type u} [CommRing A]
    (F : PresheafOfModules.{w} (algebraStructurePresheaf.{v} A))
    {B : Type v} [CommRing B] [Algebra A B]
    {N : Type v} [AddCommGroup N] [Module B N] (n : N) :
    (tangentModule A F ({ algebra := B, module := B } : AlgebraModulePair.{v} A)) →
      tangentModule A F ({ algebra := B, module := N } : AlgebraModulePair.{v} A) :=
  (tangentFunctor A F).map (pairHom ((LinearMap.id : B →ₗ[B] B).smulRight n))

/-- The tangent maps of pair morphisms induced by linear maps compose like the linear maps. -/
private lemma tangentFunctor_map_pairHom_comp
    (S : RightExactTangentFunctor.{u, v, w}) {B : Type v} [CommRing B]
    [Algebra S.A B] {L M N : Type v} [AddCommGroup L] [Module B L] [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N] (f : L →ₗ[B] M) (g : M →ₗ[B] N)
    (x : tangentModule S.A S.F ({ algebra := B, module := L } : AlgebraModulePair.{v} S.A)) :
    (tangentFunctor S.A S.F).map (pairHom g) ((tangentFunctor S.A S.F).map (pairHom f) x) =
      (tangentFunctor S.A S.F).map (pairHom (g ∘ₗ f)) x := by
  rw [← (tangentFunctor S.A S.F).map_comp]
  rfl

/-- The tangent functor sends the morphism of pairs given by `f₁.prod f₂ : M → N × N` to the sum
of the tangent maps of `f₁` and `f₂` followed by the two inclusions `N → N × N`. -/
private lemma tangentFunctor_map_pairHom_prod
    (S : RightExactTangentFunctor.{u, v, w}) {B : Type v} [CommRing B]
    [Algebra S.A B] {M N : Type v} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (f₁ f₂ : M →ₗ[B] N) (x : tangentModule S.A S.F
      ({ algebra := B, module := M } : AlgebraModulePair.{v} S.A)) :
    (tangentFunctor S.A S.F).map (pairHom (f₁.prod f₂)) x =
      (tangentFunctor S.A S.F).map (pairHom (LinearMap.inl B N N))
          ((tangentFunctor S.A S.F).map (pairHom f₁) x) +
        (tangentFunctor S.A S.F).map (pairHom (LinearMap.inr B N N))
          ((tangentFunctor S.A S.F).map (pairHom f₂) x) := by
  have h0 (y : tangentModule S.A S.F
      ({ algebra := B, module := M } : AlgebraModulePair.{v} S.A)) :
      (tangentFunctor S.A S.F).map (pairHom (0 : M →ₗ[B] N)) y = 0 := by
    rw [tangentFunctor_map_eq_zero S.A S.F _ rfl]
    rfl
  refine (tangentModule_prod_bijective S B N N).1 (Prod.ext ?_ ?_)
  · change (tangentFunctor S.A S.F).map (pairHom (LinearMap.fst B N N)) _ =
      (tangentFunctor S.A S.F).map (pairHom (LinearMap.fst B N N)) _
    rw [map_add]
    repeat rw [tangentFunctor_map_pairHom_comp]
    simp only [LinearMap.fst_prod, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr,
      LinearMap.zero_comp, LinearMap.id_comp]
    exact (add_zero _).symm.trans (by congr 1; exact (h0 x).symm)
  · change (tangentFunctor S.A S.F).map (pairHom (LinearMap.snd B N N)) _ =
      (tangentFunctor S.A S.F).map (pairHom (LinearMap.snd B N N)) _
    rw [map_add]
    repeat rw [tangentFunctor_map_pairHom_comp]
    simp only [LinearMap.snd_prod, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr,
      LinearMap.zero_comp, LinearMap.id_comp]
    exact (zero_add _).symm.trans (by congr 1; exact (h0 x).symm)

/-- The map `tangentMapForElement` is additive in the element of `N`. -/
lemma tangentMapForElement_add {A : Type u} [CommRing A]
    (S : RightExactTangentFunctor.{u, v, w}) {B : Type v} [CommRing B]
    [Algebra S.A B] {N : Type v} [AddCommGroup N] [Module B N]
    (n₁ n₂ : N) (x : tangentModule S.A S.F
      ({ algebra := B, module := B } : AlgebraModulePair.{v} S.A)) :
    tangentMapForElement S.F (n₁ + n₂) x =
      tangentMapForElement S.F n₁ x + tangentMapForElement S.F n₂ x := by
  have hsum : (LinearMap.id : B →ₗ[B] B).smulRight (n₁ + n₂) =
      (LinearMap.fst B N N + LinearMap.snd B N N) ∘ₗ
        ((LinearMap.id : B →ₗ[B] B).smulRight n₁).prod ((LinearMap.id : B →ₗ[B] B).smulRight n₂) :=
    by ext; simp
  have hinl : (LinearMap.fst B N N + LinearMap.snd B N N) ∘ₗ LinearMap.inl B N N =
      LinearMap.id := by ext; simp
  have hinr : (LinearMap.fst B N N + LinearMap.snd B N N) ∘ₗ LinearMap.inr B N N =
      LinearMap.id := by ext; simp
  change (tangentFunctor S.A S.F).map (pairHom _) x = _
  rw [hsum, ← tangentFunctor_map_pairHom_comp, tangentFunctor_map_pairHom_prod, map_add,
    tangentFunctor_map_pairHom_comp, tangentFunctor_map_pairHom_comp,
    tangentFunctor_map_pairHom_comp, tangentFunctor_map_pairHom_comp, hinl, hinr,
    LinearMap.id_comp, LinearMap.id_comp]
  rfl

/-- The map `tangentMapForElement` sends `b • n` to the composite of the second scalar action
of `b` on `TF(B, B)` with `tangentMapForElement` for `n`. -/
lemma tangentMapForElement_smul
    (S : RightExactTangentFunctor.{u, v, w}) {B : Type v} [CommRing B]
    [Algebra S.A B] {N : Type v} [AddCommGroup N] [Module B N]
    (b : B) (n : N) (x : tangentModule S.A S.F
      ({ algebra := B, module := B } : AlgebraModulePair.{v} S.A)) :
    tangentMapForElement S.F (b • n) x =
      tangentMapForElement S.F n
        (secondScalarAction S.A S.F
          ({ algebra := B, module := B } : AlgebraModulePair.{v} S.A) x b) := by
  have hcomp : (LinearMap.id : B →ₗ[B] B).smulRight (b • n) =
      ((LinearMap.id : B →ₗ[B] B).smulRight n) ∘ₗ LinearMap.lsmul B B b := by
    ext; simp
  change (tangentFunctor S.A S.F).map (pairHom _) x = _
  rw [hcomp, ← tangentFunctor_map_pairHom_comp]
  rfl

/-- The `B`-linear comparison map `TF(B, B) ⊗[B] N → TF(B, N)` sending `x ⊗ₜ n` to
`tangentMapForElement S.F n x`, for given `B`-module structures on the tangent modules
realising the second scalar action. -/
noncomputable def tangentTensorMap
    (S : RightExactTangentFunctor.{u, v, w}) {B : Type v} [CommRing B]
    [Algebra S.A B] {N : Type v} [AddCommGroup N] [Module B N]
    (sX : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := B } : AlgebraModulePair.{v} S.A)) //
      ∀ (b : B) (x : tangentModule S.A S.F
        ({ algebra := B, module := B } : AlgebraModulePair.{v} S.A)),
        m.toDistribMulAction.toSMul.smul b x =
          secondScalarAction S.A S.F _ x b})
    (sY : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)) //
      ∀ (b : B) (x : tangentModule S.A S.F
        ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)),
        m.toDistribMulAction.toSMul.smul b x =
          secondScalarAction S.A S.F _ x b}) :
    letI : Module B (tangentModule S.A S.F
      ({ algebra := B, module := B } : AlgebraModulePair.{v} S.A)) := sX.1
    letI : Module B (tangentModule S.A S.F
      ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)) := sY.1
    TensorProduct B (tangentModule S.A S.F
      ({ algebra := B, module := B } : AlgebraModulePair.{v} S.A)) N →ₗ[B]
      tangentModule S.A S.F ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A) := by
  classical
  let X : AlgebraModulePair.{v} S.A := { algebra := B, module := B }
  let Y : AlgebraModulePair.{v} S.A := { algebra := B, module := N }
  letI : Module B (tangentModule S.A S.F X) := sX.1
  letI : Module B (tangentModule S.A S.F Y) := sY.1
  let bil : tangentModule S.A S.F X →ₗ[B]
      N →ₗ[B] tangentModule S.A S.F Y := {
    toFun := fun x => {
      toFun := fun n => tangentMapForElement S.F n x
      map_add' := fun n₁ n₂ => by
        change tangentMapForElement S.F (n₁ + n₂) x = _
        exact tangentMapForElement_add (A := S.A) (S := S) (B := B) (N := N)
          n₁ n₂ x
      map_smul' := fun b n => by
        rw [tangentMapForElement_smul S b n x]
        let f : X ⟶ Y := pairHom ((LinearMap.id : B →ₗ[B] B).smulRight n)
        change (tangentFunctor S.A S.F).map f
          (secondScalarAction S.A S.F X x b) = _
        rw [secondScalarAction_naturality S f x b]
        have hb : f.base b = b := rfl
        rw [hb, ← sY.2 b _]
        rfl
    }
    map_add' := fun x y => by
      ext n
      exact congrArg Subtype.val <| map_add
        ((tangentFunctor S.A S.F).map
          (pairHom ((LinearMap.id : B →ₗ[B] B).smulRight n))) x y
    map_smul' := fun b x => by
      refine LinearMap.ext fun n => ?_
      have hx : b • x = secondScalarAction S.A S.F X x b :=
        sX.2 b x
      let f : X ⟶ Y := pairHom ((LinearMap.id : B →ₗ[B] B).smulRight n)
      have hb : f.base b = b := rfl
      rw [hx]
      change (tangentFunctor S.A S.F).map f
          (secondScalarAction S.A S.F X x b) = _
      rw [secondScalarAction_naturality S f x b, hb]
      rw [← sY.2 b _]
      rfl
  }
  exact TensorProduct.lift bil

/-- The comparison map `tangentTensorMap` sends `x ⊗ₜ n` to `tangentMapForElement S.F n x`. -/
lemma tangentTensorMap_tmul
    (S : RightExactTangentFunctor.{u, v, w}) {B : Type v} [CommRing B]
    [Algebra S.A B] {N : Type v} [AddCommGroup N] [Module B N]
    (x : tangentModule S.A S.F ({ algebra := B, module := B } : AlgebraModulePair.{v} S.A))
    (n : N) :
    let X : AlgebraModulePair.{v} S.A := { algebra := B, module := B }
    let Y : AlgebraModulePair.{v} S.A := { algebra := B, module := N }
    letI : Module B (tangentModule S.A S.F X) := (secondModuleStructure S X).1
    letI : Module B (tangentModule S.A S.F Y) := (secondModuleStructure S Y).1
    (tangentTensorMap S (B := B) (N := N)
      (secondModuleStructure S ({ algebra := B, module := B } : AlgebraModulePair.{v} S.A))
      (secondModuleStructure S ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)))
      (x ⊗ₜ[B] n) =
      tangentMapForElement S.F n x := by
  rfl

/-- The map `TF(B, M) → TF(B, N)` induced by a `B`-linear map `f : M →ₗ[B] N`, as a `B`-linear
map for given `B`-module structures realising the second scalar action. -/
noncomputable def tangentPairMapLinear
    (S : RightExactTangentFunctor.{u, v, w}) {B : Type v} [CommRing B]
    [Algebra S.A B] {M N : Type v} [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N] (f : M →ₗ[B] N)
    (sM : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := M } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x =
        secondScalarAction S.A S.F _ x b})
    (sN : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x =
        secondScalarAction S.A S.F _ x b}) :
    letI : Module B (tangentModule S.A S.F
      ({ algebra := B, module := M } : AlgebraModulePair.{v} S.A)) := sM.1
    letI : Module B (tangentModule S.A S.F
      ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)) := sN.1
    tangentModule S.A S.F ({ algebra := B, module := M } : AlgebraModulePair.{v} S.A) →ₗ[B]
      tangentModule S.A S.F ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A) := by
  classical
  let X : AlgebraModulePair.{v} S.A := { algebra := B, module := M }
  let Y : AlgebraModulePair.{v} S.A := { algebra := B, module := N }
  letI : Module B (tangentModule S.A S.F X) := sM.1
  letI : Module B (tangentModule S.A S.F Y) := sN.1
  let h : X ⟶ Y := pairHom f
  refine {
    toFun := (tangentFunctor S.A S.F).map h
    map_add' := fun x y => map_add _ x y
    map_smul' := ?_ }
  intro b x
  change ((tangentFunctor S.A S.F).map h)
      (sM.1.toDistribMulAction.toSMul.smul b x) =
    sN.1.toDistribMulAction.toSMul.smul b
      ((tangentFunctor S.A S.F).map h x)
  rw [sM.2 b x]
  change (tangentFunctor S.A S.F).map h
    (secondScalarAction S.A S.F X x b) = _
  rw [secondScalarAction_naturality S h x b]
  have hb : h.base b = b := by
    change (AlgHom.id S.A B) b = b
    rfl
  rw [hb, ← sN.2 b _]

/-- For a surjective `B`-linear map `g : L → N`, the sequence `0 → ker g → L → N → 0` is a
short exact sequence of `B`-modules. -/
private lemma shortExact_moduleCatMk_ker_subtype {B : Type v} [CommRing B] {L N : Type v}
    [AddCommGroup L] [Module B L] [AddCommGroup N] [Module B N] (g : L →ₗ[B] N)
    (hg : Function.Surjective g) :
    (ShortComplex.moduleCatMk (LinearMap.ker g).subtype g (by
      ext x
      exact (LinearMap.mem_ker).mp x.property)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    exact (LinearMap.ker g).subtype_injective
  · rw [ModuleCat.epi_iff_surjective]
    exact hg

/-- If `f : M →ₗ[B] N` is surjective, then so is the induced map
`tangentPairMapLinear S f sM sN : TF(B, M) → TF(B, N)`. -/
lemma tangentPairMapLinear_surjective
    (S : RightExactTangentFunctor.{u, v, w}) {B : Type v} [CommRing B]
    [Algebra S.A B] {M N : Type v} [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N] (f : M →ₗ[B] N)
    (hf : Function.Surjective f)
    (sM : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := M } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x = secondScalarAction S.A S.F _ x b})
    (sN : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x = secondScalarAction S.A S.F _ x b}) :
    Function.Surjective (tangentPairMapLinear S f sM sN) := by
  have hc := shortExact_moduleCatMk_ker_subtype f hf
  have hsurj : Function.Surjective ((tangentFunctorAt S.A S.F B).map (ShortComplex.moduleCatMk
      (LinearMap.ker f).subtype f (by
        ext x
        exact (LinearMap.mem_ker).mp x.property)).g) :=
    (AddCommGrpCat.epi_iff_surjective _).mp (S.rightExact B _ hc).2
  exact hsurj

/-- The comparison maps `tangentTensorMap` are natural in the module: they commute with the
maps induced by a `B`-linear map `f : M →ₗ[B] N` on tangent modules and on tensor products. -/
lemma tangentTensorMap_natural
    (S : RightExactTangentFunctor.{u, v, w}) {B : Type v} [CommRing B]
    [Algebra S.A B] {M N : Type v} [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N] (f : M →ₗ[B] N)
    (sB : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := B } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x = secondScalarAction S.A S.F _ x b})
    (sM : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := M } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x = secondScalarAction S.A S.F _ x b})
    (sN : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x = secondScalarAction S.A S.F _ x b}) :
    letI : Module B (tangentModule S.A S.F
      ({ algebra := B, module := B } : AlgebraModulePair.{v} S.A)) := sB.1
    letI : Module B (tangentModule S.A S.F
      ({ algebra := B, module := M } : AlgebraModulePair.{v} S.A)) := sM.1
    letI : Module B (tangentModule S.A S.F
      ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)) := sN.1
    (tangentPairMapLinear S f sM sN).comp (tangentTensorMap S sB sM) =
      (tangentTensorMap S sB sN).comp (f.lTensor
        (tangentModule S.A S.F ({ algebra := B, module := B } : AlgebraModulePair.{v} S.A))) := by
  let X : AlgebraModulePair.{v} S.A := { algebra := B, module := B }
  let XM : AlgebraModulePair.{v} S.A := { algebra := B, module := M }
  let XN : AlgebraModulePair.{v} S.A := { algebra := B, module := N }
  let : Module B (tangentModule S.A S.F X) := sB.1
  let : Module B (tangentModule S.A S.F XM) := sM.1
  let : Module B (tangentModule S.A S.F XN) := sN.1
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x m =>
      change (tangentFunctor S.A S.F).map (pairHom f) ((tangentFunctor S.A S.F).map (pairHom _) x) =
        (tangentFunctor S.A S.F).map (pairHom _) x
      have hcomp : f ∘ₗ (LinearMap.id : B →ₗ[B] B).smulRight m =
          (LinearMap.id : B →ₗ[B] B).smulRight (f m) := by ext; simp
      rw [tangentFunctor_map_pairHom_comp, hcomp]
  | add z₁ z₂ hz₁ hz₂ =>
      show (tangentPairMapLinear S f sM sN).comp
          (tangentTensorMap S sB sM) (z₁ + z₂) =
        (tangentTensorMap S sB sN).comp
          (f.lTensor (tangentModule S.A S.F
            ({ algebra := B, module := B } : AlgebraModulePair.{v} S.A))) (z₁ + z₂)
      simp only [map_add, LinearMap.comp_apply, hz₁, hz₂]

/-- If `g : L → N` is surjective, then `TF(B, ker g) → TF(B, L) → TF(B, N)` is exact. -/
private lemma tangentPairMapLinear_ker_subtype_exact
    (S : RightExactTangentFunctor.{u, v, w}) {B : Type v} [CommRing B]
    [Algebra S.A B] {L N : Type v} [AddCommGroup L] [Module B L] [AddCommGroup N] [Module B N]
    (g : L →ₗ[B] N) (hg : Function.Surjective g)
    (sL : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := L } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x = secondScalarAction S.A S.F _ x b})
    (sN : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x = secondScalarAction S.A S.F _ x b}) :
    Function.Exact (tangentPairMapLinear S (LinearMap.ker g).subtype
        (secondModuleStructure S
          ({ algebra := B, module := LinearMap.ker g } : AlgebraModulePair.{v} S.A)) sL)
      (tangentPairMapLinear S g sL sN) := by
  have hExact := (ShortComplex.ab_exact_iff_function_exact _).mp
    (S.rightExact B _ (shortExact_moduleCatMk_ker_subtype g hg)).1
  change Function.Exact ((tangentFunctor S.A S.F).map (pairHom (LinearMap.ker g).subtype))
    ((tangentFunctor S.A S.F).map (pairHom g)) at hExact
  exact hExact

/-- If `g ∘ f = 0`, then the composite of the induced maps `TF(B, M) → TF(B, L) → TF(B, N)`
vanishes. -/
private lemma tangentPairMapLinear_apply_apply_eq_zero
    (S : RightExactTangentFunctor.{u, v, w}) {B : Type v} [CommRing B]
    [Algebra S.A B] {M L N : Type v} [AddCommGroup M] [Module B M]
    [AddCommGroup L] [Module B L] [AddCommGroup N] [Module B N]
    (f : M →ₗ[B] L) (g : L →ₗ[B] N) (hgf : g.comp f = 0)
    (sM : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := M } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x = secondScalarAction S.A S.F _ x b})
    (sL : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := L } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x = secondScalarAction S.A S.F _ x b})
    (sN : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x = secondScalarAction S.A S.F _ x b})
    (x : tangentModule S.A S.F ({ algebra := B, module := M } : AlgebraModulePair.{v} S.A)) :
    tangentPairMapLinear S g sL sN (tangentPairMapLinear S f sM sL x) = 0 := by
  change (tangentFunctor S.A S.F).map (pairHom g) ((tangentFunctor S.A S.F).map (pairHom f) x) = 0
  rw [tangentFunctor_map_pairHom_comp, tangentFunctor_map_eq_zero S.A S.F (pairHom (g ∘ₗ f)) hgf]
  rfl

/-- If `M → L → N → 0` is exact, then so is the induced sequence of tangent modules
`TF(B, M) → TF(B, L) → TF(B, N)`. -/
lemma tangentPairMapLinear_exact
    (S : RightExactTangentFunctor.{u, v, w}) {B : Type v} [CommRing B]
    [Algebra S.A B] {M L N : Type v} [AddCommGroup M] [Module B M]
    [AddCommGroup L] [Module B L] [AddCommGroup N] [Module B N]
    (f : M →ₗ[B] L) (g : L →ₗ[B] N)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (sM : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := M } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x = secondScalarAction S.A S.F _ x b})
    (sL : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := L } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x = secondScalarAction S.A S.F _ x b})
    (sN : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x = secondScalarAction S.A S.F _ x b}) :
    Function.Exact (tangentPairMapLinear S f sM sL)
      (tangentPairMapLinear S g sL sN) := by
  let sK := secondModuleStructure S
    ({ algebra := B, module := LinearMap.ker g } : AlgebraModulePair.{v} S.A)
  let i : LinearMap.ker g →ₗ[B] L := (LinearMap.ker g).subtype
  have hkerRange : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.mp hfg
  have hfker (x : M) : f x ∈ LinearMap.ker g := by
    rw [hkerRange]
    exact ⟨x, rfl⟩
  let fk : M →ₗ[B] LinearMap.ker g := f.codRestrict _ hfker
  have hfk : Function.Surjective fk := by
    intro y
    have hy : (y : L) ∈ LinearMap.range f := by
      rw [← hkerRange]
      exact y.property
    rcases hy with ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  have hTfk := tangentPairMapLinear_surjective S fk hfk sM sK
  have hExact := tangentPairMapLinear_ker_subtype_exact S g hg sL sN
  intro y
  constructor
  · intro hy
    obtain ⟨k, hk⟩ := Set.mem_range.mp ((hExact y).mp hy)
    obtain ⟨x, hx⟩ := hTfk k
    have hx' : (tangentFunctor S.A S.F).map (pairHom fk) x = k := hx
    have hk' : (tangentFunctor S.A S.F).map (pairHom i) k = y := hk
    exact ⟨x, (tangentFunctor_map_pairHom_comp S fk i x).symm.trans (by rw [hx', hk'])⟩
  · rintro ⟨x, rfl⟩
    exact tangentPairMapLinear_apply_apply_eq_zero S f g hfg.linearMap_comp_eq_zero sM sL sN x

/-- Given exact sequences `M → N → P → 0` and `M' → N' → P' → 0`, linear equivalences
`M ≃ M'` and `N ≃ N'`, and a linear map `P → P'` making both squares commute, the map
`P → P'` is bijective. -/
lemma bijective_of_exact_diagram
    {R M M' N N' P P' : Type*} [Semiring R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    [AddCommGroup P] [Module R P] [AddCommGroup P'] [Module R P']
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (f' : M' →ₗ[R] N') (g' : N' →ₗ[R] P')
    (eA : M ≃ₗ[R] M') (eB : N ≃ₗ[R] N') (hC : P →ₗ[R] P')
    (hex : Function.Exact f g) (hsurj : Function.Surjective g)
    (hex' : Function.Exact f' g') (hsurj' : Function.Surjective g')
    (hcomm₁ : eB.toLinearMap.comp f = f'.comp eA.toLinearMap)
    (hcomm₂ : hC.comp g = g'.comp eB.toLinearMap) :
    Function.Bijective hC := by
  constructor
  · intro c₁ c₂ hc
    obtain ⟨b₁, rfl⟩ := hsurj c₁
    obtain ⟨b₂, rfl⟩ := hsurj c₂
    have hdiff : hC (g (b₁ - b₂)) = 0 := by
      simp [map_sub, hc]
    have hpoint₂ := congrArg (fun q : N →ₗ[R] P' => q (b₁ - b₂)) hcomm₂
    change hC (g (b₁ - b₂)) = g' (eB (b₁ - b₂)) at hpoint₂
    have hz : g' (eB (b₁ - b₂)) = 0 := hpoint₂.symm.trans hdiff
    obtain ⟨a', ha'⟩ := Set.mem_range.mp ((hex' (eB (b₁ - b₂))).mp hz)
    let a : M := eA.symm a'
    have hpoint₁ := congrArg (fun q : M →ₗ[R] N' => q a) hcomm₁
    change eB (f a) = f' (eA a) at hpoint₁
    have heq : eB (f a) = eB (b₁ - b₂) := by
      calc
        eB (f a) = f' (eA a) := hpoint₁
        _ = f' a' := by rw [eA.apply_symm_apply]
        _ = eB (b₁ - b₂) := ha'
    have hfa : f a = b₁ - b₂ := eB.injective heq
    rw [← sub_eq_zero, ← map_sub, ← hfa]
    exact (hex (f a)).mpr ⟨a, rfl⟩
  · intro c'
    obtain ⟨b', hb'⟩ := hsurj' c'
    obtain ⟨b, rfl⟩ := eB.surjective b'
    refine ⟨g b, ?_⟩
    have hpoint := congrArg (fun q : N →ₗ[R] P' => q b) hcomm₂
    change hC (g b) = g' (eB b) at hpoint
    exact hpoint.trans hb'

/-- The `B`-linear equivalence `TF(B, M) ≃ₗ[B] TF(B, N)` induced by a linear equivalence
`e : M ≃ₗ[B] N`. -/
noncomputable def tangentMapLinearEquiv
    (S : RightExactTangentFunctor.{u, v, w}) {B : Type v} [CommRing B]
    [Algebra S.A B] {M N : Type v} [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N] (e : M ≃ₗ[B] N)
    (sM : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := M } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x = secondScalarAction S.A S.F _ x b})
    (sN : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x = secondScalarAction S.A S.F _ x b}) :
    letI : Module B (tangentModule S.A S.F
      ({ algebra := B, module := M } : AlgebraModulePair.{v} S.A)) := sM.1
    letI : Module B (tangentModule S.A S.F
      ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)) := sN.1
    tangentModule S.A S.F ({ algebra := B, module := M } : AlgebraModulePair.{v} S.A) ≃ₗ[B]
      tangentModule S.A S.F ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A) := by
  let X : AlgebraModulePair.{v} S.A := { algebra := B, module := M }
  let Y : AlgebraModulePair.{v} S.A := { algebra := B, module := N }
  letI : Module B (tangentModule S.A S.F X) := sM.1
  letI : Module B (tangentModule S.A S.F Y) := sN.1
  let f : X ⟶ Y := pairHom e.toLinearMap
  let g : Y ⟶ X := pairHom e.symm.toLinearMap
  have hfg : f ≫ g = 𝟙 X := by
    apply AlgebraModulePair.Hom.ext
    · rfl
    · exact e.left_inv
  have hgf : g ≫ f = 𝟙 Y := by
    apply AlgebraModulePair.Hom.ext
    · rfl
    · exact e.right_inv
  exact LinearEquiv.ofLinearMap
    (tangentPairMapLinear S e.toLinearMap sM sN)
    (tangentPairMapLinear S e.symm.toLinearMap sN sM)
    (by
      refine LinearMap.ext fun x => ?_
      change (tangentFunctor S.A S.F).map f
        ((tangentFunctor S.A S.F).map g x) = x
      rw [← (tangentFunctor S.A S.F).map_comp, hgf]
      exact (tangentFunctor S.A S.F).map_id Y x)
    (by
      refine LinearMap.ext fun x => ?_
      change (tangentFunctor S.A S.F).map g
        ((tangentFunctor S.A S.F).map f x) = x
      rw [← (tangentFunctor S.A S.F).map_comp, hfg]
      exact (tangentFunctor S.A S.F).map_id X x)

/-- The coordinate map to the tangent modules of a finite product. -/
noncomputable def tangentPiCoordMap
    (S : RightExactTangentFunctor.{u, v, w}) {B : Type v} [CommRing B]
    [Algebra S.A B] (n : ℕ)
    (sP : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := (Fin n → B) } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x =
        secondScalarAction S.A S.F _ x b})
    (sB : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := B } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x =
        secondScalarAction S.A S.F _ x b}) :
    letI : Module B (tangentModule S.A S.F
      ({ algebra := B, module := (Fin n → B) } : AlgebraModulePair.{v} S.A)) := sP.1
    letI : Module B (tangentModule S.A S.F
      ({ algebra := B, module := B } : AlgebraModulePair.{v} S.A)) := sB.1
    tangentModule S.A S.F
        ({ algebra := B, module := (Fin n → B) } : AlgebraModulePair.{v} S.A) →ₗ[B]
      (Fin n → tangentModule S.A S.F
        ({ algebra := B, module := B } : AlgebraModulePair.{v} S.A)) := by
  classical
  let X : AlgebraModulePair.{v} S.A := { algebra := B, module := (Fin n → B) }
  let Y : AlgebraModulePair.{v} S.A := { algebra := B, module := B }
  letI : Module B (tangentModule S.A S.F X) := sP.1
  letI : Module B (tangentModule S.A S.F Y) := sB.1
  exact LinearMap.pi fun i => tangentPairMapLinear S (LinearMap.proj i) sP sB

/-- The `B`-linear equivalence `TF(B, M × N) ≃ₗ[B] TF(B, M) × TF(B, N)` induced by the two
projections. -/
noncomputable def tangentProdEquiv
    (S : RightExactTangentFunctor.{u, v, w}) {B : Type v} [CommRing B]
    [Algebra S.A B] {M N : Type v} [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N]
    (sP : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := M × N } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x = secondScalarAction S.A S.F _ x b})
    (sM : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := M } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x = secondScalarAction S.A S.F _ x b})
    (sN : {m : Module B (tangentModule S.A S.F
      ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)) //
      ∀ b x, m.toDistribMulAction.toSMul.smul b x = secondScalarAction S.A S.F _ x b}) :
    letI : Module B (tangentModule S.A S.F
      ({ algebra := B, module := M × N } : AlgebraModulePair.{v} S.A)) := sP.1
    letI : Module B (tangentModule S.A S.F
      ({ algebra := B, module := M } : AlgebraModulePair.{v} S.A)) := sM.1
    letI : Module B (tangentModule S.A S.F
      ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)) := sN.1
    tangentModule S.A S.F
        ({ algebra := B, module := M × N } : AlgebraModulePair.{v} S.A) ≃ₗ[B]
      (tangentModule S.A S.F ({ algebra := B, module := M } : AlgebraModulePair.{v} S.A) ×
        tangentModule S.A S.F ({ algebra := B, module := N } : AlgebraModulePair.{v} S.A)) := by
  let X : AlgebraModulePair.{v} S.A := { algebra := B, module := M × N }
  let XM : AlgebraModulePair.{v} S.A := { algebra := B, module := M }
  let XN : AlgebraModulePair.{v} S.A := { algebra := B, module := N }
  letI : Module B (tangentModule S.A S.F X) := sP.1
  letI : Module B (tangentModule S.A S.F XM) := sM.1
  letI : Module B (tangentModule S.A S.F XN) := sN.1
  let f₁ := tangentPairMapLinear S (LinearMap.fst B M N) sP sM
  let f₂ := tangentPairMapLinear S (LinearMap.snd B M N) sP sN
  let q : tangentModule S.A S.F X →ₗ[B]
      tangentModule S.A S.F XM × tangentModule S.A S.F XN := {
    toFun := fun x => (f₁ x, f₂ x)
    map_add' x y := by simp [f₁, f₂]
    map_smul' b x := by simp [f₁, f₂]
  }
  exact LinearEquiv.ofBijective q
    (tangentModule_prod_bijective S B M N)

/-- The `B`-linear equivalence `TF(B, Fin n → B) ≃ₗ[B] (Fin n → TF(B, B))`, for the second
module structures. -/
noncomputable def tangentPiCoordEquiv
    (S : RightExactTangentFunctor.{u, v, w}) {B : Type v} [CommRing B]
    [Algebra S.A B] (n : ℕ) :
    let X : AlgebraModulePair.{v} S.A := { algebra := B, module := (Fin n → B) }
    let Y : AlgebraModulePair.{v} S.A := { algebra := B, module := B }
    letI : Module B (tangentModule S.A S.F X) := (secondModuleStructure S X).1
    letI : Module B (tangentModule S.A S.F Y) := (secondModuleStructure S Y).1
    tangentModule S.A S.F X ≃ₗ[B] (Fin n → tangentModule S.A S.F Y) := by
  induction n with
  | zero =>
      let X : AlgebraModulePair.{v} S.A := { algebra := B, module := (Fin 0 → B) }
      let Y : AlgebraModulePair.{v} S.A := { algebra := B, module := B }
      let sX := secondModuleStructure S X
      let sY := secondModuleStructure S Y
      letI : Module B (tangentModule S.A S.F X) := sX.1
      letI : Module B (tangentModule S.A S.F Y) := sY.1
      letI : Subsingleton X.module := inferInstance
      letI : Subsingleton (tangentModule S.A S.F X) :=
        tangentModule_subsingleton S.A S.F X
      exact LinearEquiv.ofBijective (tangentPiCoordMap S 0 sX sY)
        ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  | succ n ih =>
      let X : AlgebraModulePair.{v} S.A :=
        { algebra := B, module := (Fin (n + 1) → B) }
      let XP : AlgebraModulePair.{v} S.A :=
        { algebra := B, module := B × (Fin n → B) }
      let Y : AlgebraModulePair.{v} S.A := { algebra := B, module := B }
      let Z : AlgebraModulePair.{v} S.A := { algebra := B, module := (Fin n → B) }
      let sX := secondModuleStructure S X
      let sP := secondModuleStructure S XP
      let sY := secondModuleStructure S Y
      let sZ := secondModuleStructure S Z
      letI : Module B (tangentModule S.A S.F X) := sX.1
      letI : Module B (tangentModule S.A S.F XP) := sP.1
      letI : Module B (tangentModule S.A S.F Y) := sY.1
      letI : Module B (tangentModule S.A S.F Z) := sZ.1
      let eP : (Fin (n + 1) → B) ≃ₗ[B] B × (Fin n → B) :=
        (Fin.consLinearEquiv B (fun _ : Fin (n + 1) => B)).symm
      let eTan := tangentMapLinearEquiv S eP sX sP
      let eProd := tangentProdEquiv S sP sY sZ
      let eTail := ih
      let eMiddle := (LinearEquiv.refl B
        (tangentModule S.A S.F Y)).prodCongr eTail
      let eCons := Fin.consLinearEquiv B
        (fun _ : Fin (n + 1) => tangentModule S.A S.F Y)
      exact (((eTan.trans eProd).trans eMiddle).trans eCons)

/-- The `i`-th coordinate of `tangentPiCoordEquiv S n x` is the image of `x` under the map
induced by the `i`-th projection `(Fin n → B) → B`. -/
lemma tangentPiCoordEquiv_apply
    (S : RightExactTangentFunctor.{u, v, w}) {B : Type v} [CommRing B]
    [Algebra S.A B] (n : ℕ)
    (x : tangentModule S.A S.F
      ({ algebra := B, module := (Fin n → B) } : AlgebraModulePair.{v} S.A))
    (i : Fin n) :
    let X : AlgebraModulePair.{v} S.A := { algebra := B, module := (Fin n → B) }
    let Y : AlgebraModulePair.{v} S.A := { algebra := B, module := B }
    letI : Module B (tangentModule S.A S.F X) := (secondModuleStructure S X).1
    letI : Module B (tangentModule S.A S.F Y) := (secondModuleStructure S Y).1
    (tangentPiCoordEquiv S (B := B) n x) i =
      (tangentFunctor S.A S.F).map
        (pairHom (LinearMap.proj i : (Fin n → B) →ₗ[B] B)) x := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      let ePi : (Fin (n + 1) → B) ≃ₗ[B] B × (Fin n → B) :=
        (Fin.consLinearEquiv B (fun _ : Fin (n + 1) => B)).symm
      cases i using Fin.cases with
      | zero =>
          change (tangentFunctor S.A S.F).map (pairHom (LinearMap.fst B B (Fin n → B)))
            ((tangentFunctor S.A S.F).map (pairHom ePi.toLinearMap) x) = _
          rw [tangentFunctor_map_pairHom_comp]
          rfl
      | succ j =>
          change tangentPiCoordEquiv S (B := B) n ((tangentFunctor S.A S.F).map
            (pairHom (LinearMap.snd B B (Fin n → B)))
            ((tangentFunctor S.A S.F).map (pairHom ePi.toLinearMap) x)) j = _
          rw [ih, tangentFunctor_map_pairHom_comp, tangentFunctor_map_pairHom_comp]
          rfl

/-- The comparison map `TF(B, B) ⊗[B] (Fin n → B) → TF(B, Fin n → B)` is bijective. -/
theorem tangentTensorFreeMap_bijective
    (S : RightExactTangentFunctor.{u, v, w}) {B : Type v} [CommRing B]
    [Algebra S.A B] (n : ℕ) :
    let X : AlgebraModulePair.{v} S.A := { algebra := B, module := B }
    let Y : AlgebraModulePair.{v} S.A := { algebra := B, module := (Fin n → B) }
    letI : Module B (tangentModule S.A S.F X) := (secondModuleStructure S X).1
    letI : Module B (tangentModule S.A S.F Y) := (secondModuleStructure S Y).1
    Function.Bijective (tangentTensorMap S
      (secondModuleStructure S X) (secondModuleStructure S Y)) := by
  classical
  let X : AlgebraModulePair.{v} S.A := { algebra := B, module := B }
  let Y : AlgebraModulePair.{v} S.A := { algebra := B, module := (Fin n → B) }
  let sX := secondModuleStructure S X
  let sY := secondModuleStructure S Y
  let : Module B (tangentModule S.A S.F X) := sX.1
  let : Module B (tangentModule S.A S.F Y) := sY.1
  let α := tangentTensorMap S (B := B) (N := (Fin n → B)) sX sY
  let eC := tangentPiCoordEquiv S (B := B) n
  let pC := tangentPiCoordMap S n sY sX
  let eT := TensorProduct.piScalarRight B B
    (tangentModule S.A S.F X) (Fin n)
  have hcoordmap : pC = eC.toLinearMap := by
    ext z i
    simpa [pC, tangentPiCoordMap, tangentPairMapLinear] using
      (tangentPiCoordEquiv_apply S n z i).symm
  have hpure (x : tangentModule S.A S.F X) (f : Fin n → B) :
      pC (α (x ⊗ₜ[B] f)) = eT (x ⊗ₜ[B] f) := by
    rw [hcoordmap]
    funext i
    rw [tangentTensorMap_tmul]
    show (tangentPiCoordEquiv S (B := B) n
      (tangentMapForElement S.F f x)) i = _
    rw [tangentPiCoordEquiv_apply]
    have hcomp : LinearMap.proj i ∘ₗ (LinearMap.id : B →ₗ[B] B).smulRight f =
        LinearMap.lsmul B B (f i) := by ext; simp [mul_comm]
    change (tangentFunctor S.A S.F).map (pairHom (LinearMap.proj i))
      ((tangentFunctor S.A S.F).map (pairHom ((LinearMap.id : B →ₗ[B] B).smulRight f)) x) =
        f i • x
    rw [tangentFunctor_map_pairHom_comp, hcomp]
    exact (sX.2 (f i) x).symm
  have hcomp : pC.comp α = eT.toLinearMap := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x f => exact hpure x f
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hcomp' : eC.toLinearMap.comp α = eT.toLinearMap := by rwa [← hcoordmap]
  constructor
  · intro z₁ z₂ hz
    apply eT.injective
    calc
      eT z₁ = eC (α z₁) := (LinearMap.congr_fun hcomp' z₁).symm
      _ = eC (α z₂) := congrArg eC hz
      _ = eT z₂ := LinearMap.congr_fun hcomp' z₂
  · intro y
    obtain ⟨z, hz⟩ := eT.surjective (eC y)
    exact ⟨z, eC.injective ((LinearMap.congr_fun hcomp' z).trans hz)⟩

/-- The canonical tensor-product description of the tangent module of a
finitely presented module, using the second action on both tangent modules. -/
@[stacks 06ZB "tensor_finitely_presented", stacks 06ZD]
noncomputable def tangentTensorEquiv
    (S : RightExactTangentFunctor.{u, v, w})
    (B : Type v) [CommRing B] [Algebra S.A B]
    (N : Type v) [AddCommGroup N] [Module B N]
    [Module.FinitePresentation B N] :
    let X : AlgebraModulePair.{v} S.A := { algebra := B, module := B }
    let Y : AlgebraModulePair.{v} S.A := { algebra := B, module := N }
    letI : Module B (tangentModule S.A S.F X) :=
      (secondModuleStructure S X).1
    letI : Module B (tangentModule S.A S.F Y) :=
      (secondModuleStructure S Y).1
    { e : TensorProduct B (tangentModule S.A S.F X) N ≃ₗ[B]
        tangentModule S.A S.F Y //
      ∀ (x : tangentModule S.A S.F X) (n : N),
        e (TensorProduct.tmul B x n) =
          (tangentFunctor S.A S.F).map
            ({ base := AlgHom.id S.A B
               linear := (LinearMap.id : B →ₗ[B] B).smulRight n } : X ⟶ Y) x } := by
  classical
  let X : AlgebraModulePair.{v} S.A := { algebra := B, module := B }
  let Y : AlgebraModulePair.{v} S.A := { algebra := B, module := N }
  let sB := secondModuleStructure S X
  let sN := secondModuleStructure S Y
  letI : Module B (tangentModule S.A S.F X) := sB.1
  letI : Module B (tangentModule S.A S.F Y) := sN.1
  let α := tangentTensorMap S (B := B) (N := N) sB sN
  choose n m f g hf hfg using Module.FinitePresentation.exists_fin' B N
  let Xm : AlgebraModulePair.{v} S.A := { algebra := B, module := (Fin m → B) }
  let Xn : AlgebraModulePair.{v} S.A := { algebra := B, module := (Fin n → B) }
  let sm := secondModuleStructure S Xm
  let sn := secondModuleStructure S Xn
  letI : Module B (tangentModule S.A S.F Xm) := sm.1
  letI : Module B (tangentModule S.A S.F Xn) := sn.1
  let Tb := tangentModule S.A S.F X
  let hfreeM := LinearEquiv.ofBijective (tangentTensorMap S sB sm)
    (tangentTensorFreeMap_bijective S m)
  let hfreeN := LinearEquiv.ofBijective (tangentTensorMap S sB sn)
    (tangentTensorFreeMap_bijective S n)
  have hTensorExact : Function.Exact (LinearMap.lTensor Tb g)
      (LinearMap.lTensor Tb f) := lTensor_exact Tb hfg hf
  have hTensorSurj : Function.Surjective (LinearMap.lTensor Tb f) :=
    LinearMap.lTensor_surjective Tb hf
  have hTangentExact := tangentPairMapLinear_exact S g f hfg hf sm sn sN
  have hTangentSurj := tangentPairMapLinear_surjective S f hf sn sN
  have hcomm₁ : hfreeN.toLinearMap.comp (LinearMap.lTensor Tb g) =
      (tangentPairMapLinear S g sm sn).comp hfreeM.toLinearMap :=
    (tangentTensorMap_natural S g sB sm sn).symm
  have hcomm₂ : α.comp (LinearMap.lTensor Tb f) =
      (tangentPairMapLinear S f sn sN).comp hfreeN.toLinearMap :=
    (tangentTensorMap_natural S f sB sn sN).symm
  have hα : Function.Bijective α :=
    bijective_of_exact_diagram
      (LinearMap.lTensor Tb g) (LinearMap.lTensor Tb f)
      (tangentPairMapLinear S g sm sn) (tangentPairMapLinear S f sn sN)
      hfreeM hfreeN α hTensorExact hTensorSurj hTangentExact hTangentSurj hcomm₁ hcomm₂
  exact ⟨LinearEquiv.ofBijective α hα, fun _ _ => rfl⟩

end AdequateFunctor
