module

public import Mathlib
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.HomComplex.Basic
public import StacksFrontier.Homology.HomComplex.CochainScalarTower

@[expose] public noncomputable section

/-!
# Base change of cochains out of a complex into a bounded complex

Let `f : A →+* B` be a ring map and let `P`, `F` be cochain complexes of `A`-modules. Extending
scalars along `f` termwise sends a degree-`n` cochain `P → F` to a degree-`n` cochain between the
scalar extensions, and the resulting `A`-linear map lifts to a `B`-linear comparison out of
`B ⊗[A] Cochain P F n`. This file collects that comparison together with the two finiteness
facts that make it an isomorphism when `F` is concentrated in a bounded window: a cochain into
such an `F` is determined by its finitely many components landing in the window, and there are
only finitely many triplets of a fixed total degree whose target degree lies in it.

## Main definitions

* `StacksDraft.RelativelyPerfect.homCochainRestrict`: cochains into a complex concentrated in
  `[a, b]` as a finite product of the Hom-modules of the components in that window.
* `StacksDraft.RelativelyPerfect.homCochainExtendScalars`: termwise scalar extension of a
  cochain.
* `StacksDraft.RelativelyPerfect.homCochainBaseChange`: the induced `B`-linear base-change map
  on cochains.
* `StacksDraft.RelativelyPerfect.homComplexBaseChange`: those maps assembled into a morphism of
  Hom complexes.

## Main results

* `StacksDraft.RelativelyPerfect.finite_homCochain_support`: the triplets of total degree `n`
  with target degree in `[a, b]` form a finite type.
* `StacksDraft.RelativelyPerfect.linearMap_isBaseChange_of_finiteFree`: linear maps out of a
  finite free module base-change to linear maps out of the scalar extension.
* `StacksDraft.RelativelyPerfect.homCochainBaseChange_bijective`: out of a finite free complex
  into a complex concentrated in a bounded window, the base-change map on cochains is
  bijective.

## Implementation notes

The `A`-module structure on cochains between complexes of `B`-modules comes from the scoped
`ModuleCat.Algebra` instances together with
`CochainComplex.HomComplex.Cochain.isScalarTower`, which is why the declarations after
`finite_homCochain_support` are stated with those in scope. The ring universes and the module
universe are independent.
-/

open CategoryTheory

open scoped TensorProduct

namespace StacksDraft.RelativelyPerfect

universe u v w

/-- Cochains into a complex concentrated in `[a, b]` are determined by their finitely many
components landing in that window. -/
def homCochainRestrict
    {A : Type u} [CommRing A] (P F : CochainComplex (ModuleCat.{v} A) ℤ)
    (n a b : ℤ) [F.IsStrictlyGE a] [F.IsStrictlyLE b] :
    CochainComplex.HomComplex.Cochain P F n ≃ₗ[A]
      (t : {t : CochainComplex.HomComplex.Triplet n // a ≤ t.q ∧ t.q ≤ b}) →
        (P.X t.val.p ⟶ F.X t.val.q) := by
  classical
  refine
    { toFun := fun z t ↦ z t.val
      invFun := fun z t ↦ if h : a ≤ t.q ∧ t.q ≤ b then z ⟨t, h⟩ else 0
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    funext t
    dsimp
    split_ifs with h
    · rfl
    · by_cases ha : t.q < a
      · exact (F.isZero_of_isStrictlyGE a t.q ha).eq_of_tgt _ _
      · exact (F.isZero_of_isStrictlyLE b t.q (by omega)).eq_of_tgt _ _
  · intro z
    funext t
    exact dite_eq_left t.property

/-- There are only finitely many triplets of a fixed total degree whose target degree lies in a
bounded window. -/
lemma finite_homCochain_support (n a b : ℤ) :
    Finite {t : CochainComplex.HomComplex.Triplet n // a ≤ t.q ∧ t.q ≤ b} := by
  apply Finite.of_injective
    (fun t ↦ (⟨t.val.q, t.property⟩ : Set.Icc a b))
  intro ⟨⟨p, q, hpq⟩, h⟩ ⟨⟨p', q', hpq'⟩, h'⟩ he
  have hq : q = q' := congrArg Subtype.val he
  have hp : p = p' := by omega
  subst p'
  subst q'
  rfl

open scoped ModuleCat.Algebra

attribute [local instance] CochainComplex.HomComplex.Cochain.isScalarTower

/-- Termwise scalar extension of a cochain. -/
def homCochainExtendScalars
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (P F : CochainComplex (ModuleCat.{w} A) ℤ) (n : ℤ) :
    let := f.toAlgebra
    CochainComplex.HomComplex.Cochain P F n →ₗ[A]
      CochainComplex.HomComplex.Cochain
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj P)
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj F) n := by
  let := f.toAlgebra
  refine
    { toFun := fun z ↦ z.map (ModuleCat.extendScalars f)
      map_add' := fun z w ↦ CochainComplex.HomComplex.Cochain.map_add z w _
      map_smul' := fun a z ↦ CochainComplex.HomComplex.Cochain.ext _ _ fun p q hpq ↦
        ModuleCat.hom_ext (LinearMap.baseChange_smul a (z.v p q hpq).hom) }

/-- The base-change map from the scalar extension of the cochains to the cochains between the
scalar extensions. -/
def homCochainBaseChange
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (P F : CochainComplex (ModuleCat.{w} A) ℤ) (n : ℤ) :
    ((ModuleCat.extendScalars.{u, v, w} f).obj
      ((CochainComplex.HomComplexR A P F).X n)) →ₗ[B]
      CochainComplex.HomComplex.Cochain
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj P)
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj F) n := by
  let := f.toAlgebra
  exact LinearMap.liftBaseChange B (homCochainExtendScalars f P F n)

/-- The base-change maps on cochains assemble into a morphism of complexes. -/
def homComplexBaseChange
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (P F : CochainComplex (ModuleCat.{w} A) ℤ) :
    ((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.HomComplexR A P F) ⟶
      CochainComplex.HomComplexR B
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj P)
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj F) where
  f n := by
    let := f.toAlgebra
    exact ModuleCat.ofHom (X := B ⊗[A] CochainComplex.HomComplex.Cochain P F n)
      (homCochainBaseChange f P F n)
  comm' i j hij := by
    let := f.toAlgebra
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    change B ⊗[A] CochainComplex.HomComplex.Cochain P F i at t
    change (CochainComplex.HomComplex.δ_hom B _ _ i j)
        (homCochainBaseChange f P F i t) =
      homCochainBaseChange f P F j
        ((LinearMap.baseChange B (CochainComplex.HomComplex.δ_hom A P F i j)) t)
    dsimp only [homCochainBaseChange]
    induction t using TensorProduct.induction_on with
    -- `t` is only definitionally an element of the tensor product, so the zero and the sum
    -- carry a different `Zero`/`Add` path from the one the maps' domain declares and neither
    -- `rw` nor `simp` can match `map_zero`/`map_add` against them. Both steps are terms.
    | zero =>
      have h₀ : (LinearMap.liftBaseChange B (homCochainExtendScalars f P F i))
          (0 : B ⊗[A] CochainComplex.HomComplex.Cochain P F i) = 0 := map_zero _
      refine (congrArg
        (fun z => (CochainComplex.HomComplex.δ_hom B _ _ i j) z) h₀).trans ?_
      exact (map_zero _).trans (map_zero _).symm
    | add t s ht hs =>
      have hLi : (LinearMap.liftBaseChange B (homCochainExtendScalars f P F i)) (t + s) =
          (LinearMap.liftBaseChange B (homCochainExtendScalars f P F i)) t +
            (LinearMap.liftBaseChange B (homCochainExtendScalars f P F i)) s := map_add _ _ _
      have hbc : (LinearMap.baseChange B
            (CochainComplex.HomComplex.δ_hom A P F i j)) (t + s) =
          (LinearMap.baseChange B (CochainComplex.HomComplex.δ_hom A P F i j)) t +
            (LinearMap.baseChange B
              (CochainComplex.HomComplex.δ_hom A P F i j)) s := map_add _ _ _
      have e₁ : (CochainComplex.HomComplex.δ_hom B _ _ i j)
            ((LinearMap.liftBaseChange B (homCochainExtendScalars f P F i)) (t + s)) =
          (CochainComplex.HomComplex.δ_hom B _ _ i j)
              ((LinearMap.liftBaseChange B (homCochainExtendScalars f P F i)) t) +
            (CochainComplex.HomComplex.δ_hom B _ _ i j)
              ((LinearMap.liftBaseChange B (homCochainExtendScalars f P F i)) s) :=
        (congrArg (fun z => (CochainComplex.HomComplex.δ_hom B _ _ i j) z) hLi).trans
          (map_add _ _ _)
      have e₂ : (LinearMap.liftBaseChange B (homCochainExtendScalars f P F j))
            ((LinearMap.baseChange B
              (CochainComplex.HomComplex.δ_hom A P F i j)) (t + s)) =
          (LinearMap.liftBaseChange B (homCochainExtendScalars f P F j))
              ((LinearMap.baseChange B
                (CochainComplex.HomComplex.δ_hom A P F i j)) t) +
            (LinearMap.liftBaseChange B (homCochainExtendScalars f P F j))
              ((LinearMap.baseChange B
                (CochainComplex.HomComplex.δ_hom A P F i j)) s) :=
        (congrArg (fun z => (LinearMap.liftBaseChange B
          (homCochainExtendScalars f P F j)) z) hbc).trans (map_add _ _ _)
      refine e₁.trans (Eq.trans ?_ e₂.symm)
      exact (congrArg (fun z => z +
          (CochainComplex.HomComplex.δ_hom B _ _ i j)
            ((LinearMap.liftBaseChange B (homCochainExtendScalars f P F i)) s)) ht).trans
        (congrArg (fun z =>
          (LinearMap.liftBaseChange B
            (homCochainExtendScalars f P F j))
            ((LinearMap.baseChange B
              (CochainComplex.HomComplex.δ_hom A P F i j)) t) + z) hs)
    | tmul a z =>
      simp only [LinearMap.baseChange_tmul]
      change (CochainComplex.HomComplex.δ_hom B _ _ i j)
          (a • z.map (ModuleCat.extendScalars f)) =
        a • ((CochainComplex.HomComplex.δ i j z).map (ModuleCat.extendScalars f))
      rw [map_smul]
      exact congrArg (a • ·) (CochainComplex.HomComplex.δ_map i j z _)

/-- Linear maps out of a finite free module base-change to linear maps out of the scalar
extension. -/
lemma linearMap_isBaseChange_of_finiteFree
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M N : Type*) [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    [Module.Finite A M] [Module.Free A M] :
    IsBaseChange B (LinearMap.baseChangeHom A B M N) := by
  have h := (TensorProduct.isBaseChange (R := A) (M := M) B).linearMapLeftRight
    (TensorProduct.isBaseChange (R := A) (M := N) B)
  convert h using 1
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t s ht hs => simp only [map_add, ht, hs]
  | tmul b x =>
    calc
      b ⊗ₜ[A] z x = b • (1 ⊗ₜ[A] z x) := by simp [TensorProduct.smul_tmul']
      _ = b • _ := congrArg (b • ·) (IsBaseChange.linearMapLeftRightHom_comp_apply
          (TensorProduct.isBaseChange (R := A) (M := M) B) (TensorProduct.mk A B N 1) z x).symm
      _ = _ := by rw [← map_smul]; congr 1; simp [TensorProduct.smul_tmul']

/-- For a finite free source and a bounded target, base change of cochains is bijective. -/
lemma homCochainBaseChange_bijective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (P F : CochainComplex (ModuleCat.{w} A) ℤ) (a b n : ℤ)
    [F.IsStrictlyGE a] [F.IsStrictlyLE b]
    [∀ i, Module.Finite A (P.X i)] [∀ i, Module.Free A (P.X i)] :
    Function.Bijective (homCochainBaseChange f P F n) := by
  let := f.toAlgebra
  let I := {t : CochainComplex.HomComplex.Triplet n // a ≤ t.q ∧ t.q ≤ b}
  have : Finite I := finite_homCochain_support n a b
  let Ext := (ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)
  let P' := Ext.obj P
  let F' := Ext.obj F
  let eM := (homCochainRestrict P F n a b).trans
    (LinearEquiv.piCongrRight fun t : I ↦
      (ModuleCat.homLinearEquiv (S := A) (M := P.X t.val.p) (N := F.X t.val.q)))
  let eN := (homCochainRestrict P' F' n a b).trans
    (LinearEquiv.piCongrRight fun t : I ↦
      (ModuleCat.homLinearEquiv (S := B) (M := P'.X t.val.p) (N := F'.X t.val.q)))
  dsimp [P', F', Ext] at eN
  let : IsScalarTower A B ((t : I) →
      B ⊗[A] (P.X t.val.p) →ₗ[B] B ⊗[A] (F.X t.val.q)) :=
    ⟨fun r s z ↦ by funext t; apply LinearMap.ext; intro x; exact smul_assoc r s (z t x)⟩
  let g := LinearMap.pi fun t : I ↦
    (LinearMap.baseChangeHom A B (P.X t.val.p) (F.X t.val.q)).comp (LinearMap.proj t)
  have hg : IsBaseChange B g :=
    IsBaseChange.pi _ (fun t ↦ linearMap_isBaseChange_of_finiteFree _ _)
  let e := (eM.baseChange A B).trans (hg.equiv.trans eN.symm)
  have he : homCochainBaseChange f P F n = e.toLinearMap := by
    apply LinearMap.ext
    intro t
    change B ⊗[A] CochainComplex.HomComplex.Cochain P F n at t
    show (LinearMap.liftBaseChange B (homCochainExtendScalars f P F n)) t = e t
    apply eN.injective
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add t s ht hs => simp only [map_add, ht, hs]
    | tmul c z =>
      simp only [LinearMap.liftBaseChange_tmul, map_smul, e, LinearEquiv.trans_apply,
        LinearEquiv.baseChange_tmul]
      show c • eN ((homCochainExtendScalars f P F n) z) =
        eN (eN.symm (hg.equiv (c ⊗ₜ[A] eM z)))
      refine Eq.trans ?_ (eN.apply_symm_apply (hg.equiv (c ⊗ₜ[A] eM z))).symm
      rfl
  rw [he]
  exact e.bijective

end StacksDraft.RelativelyPerfect
