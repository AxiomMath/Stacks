module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Finiteness.Small
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Examples.Linear.FiniteProjectiveModules

/-!
# Finite projective modules are cofibered in groupoids over the base category

The projection sending a finite projective module over an object of `𝒞_Λ` to that object is
cofibered in groupoids. Pushing an object `(A, M)` forward along `A → B` is extension of
scalars, `(B, M ⊗_A B)`; and given `(A, M) → (B, N)`, `(A, M) → (C, P)` and `B → C` over `A`,
the unique filling morphism `(B, N) → (C, P)` is obtained by identifying `N ⊗_B C` with
`(M ⊗_A B) ⊗_B C = M ⊗_A C` and hence with `P`.

## Main results

* `Deformation.Examples.FiniteProjectiveModule.Family.projection_isCofiberedInGroupoids`: the
  projection of the category of finite projective modules is cofibered in groupoids.

## Implementation notes

The statement is made for an arbitrary `FiniteProjectiveModule.Family`, that is, for any
category structure on the objects satisfying the formulas of that structure, and hence applies
in particular to the chosen family `FiniteProjectiveModule.family`.

Extension of scalars has to be transported back into the module universe, which is independent
of the universe of the base ring. `FiniteProjectiveModule.small_carrier` and
`Deformation.ArtinianLocalAlgCat.small` supply the smallness needed for that
transport, and `Shrink` performs it.

## References

* [Stacks Project, Tag 0D3I](https://stacks.math.columbia.edu/tag/0D3I)
-/

@[expose] public section

open CategoryTheory

namespace Deformation.Examples.FiniteProjectiveModule

universe u w t

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Extension of scalars of a finite projective module stays small in the universe of the
module. -/
private theorem small_baseChange
    (X : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k))
    (B : ArtinianLocalAlgCat.{u, w, w} Λ k) (f : X.base ⟶ B) :
    letI : Algebra X.base B := f.hom.toRingHom.toAlgebra
    Small.{t} (TensorProduct X.base B X.carrier) := by
  let : Algebra X.base B := f.hom.toRingHom.toAlgebra
  by_cases hM : Subsingleton X.carrier
  · let : Subsingleton X.carrier := hM
    infer_instance
  · let : Nontrivial X.carrier := not_subsingleton_iff_nontrivial.mp hM
    let : Small.{t} k := small_residueField_of_nontrivial X
    let : Small.{t} B := ArtinianLocalAlgCat.small B
    let : Module.Free X.base X.carrier := Module.free_of_flat_of_isLocalRing
    let b := Module.Free.chooseBasis X.base X.carrier
    have : Finite (Module.Free.ChooseBasisIndex X.base X.carrier) :=
      Module.Finite.finite_basis b
    let b' := b.baseChange B
    have : Module.Finite B (TensorProduct X.base B X.carrier) := Module.Finite.of_basis b'
    exact Module.Finite.small.{t, w, max t w} B (TensorProduct X.base B X.carrier)

/-- The pushforward of a finite projective module along a morphism of base algebras: extension
of scalars, transported back into the module universe. -/
private noncomputable def baseChangeObj
    (X : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k))
    (B : ArtinianLocalAlgCat.{u, w, w} Λ k) (f : X.base ⟶ B) :
    FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k) := by
  letI : Algebra X.base B := f.hom.toRingHom.toAlgebra
  let N := TensorProduct X.base B X.carrier
  letI : Small.{t} N := small_baseChange X B f
  letI : Module.Free X.base X.carrier := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis X.base X.carrier
  haveI : Finite (Module.Free.ChooseBasisIndex X.base X.carrier) :=
    Module.Finite.finite_basis b
  let b' := b.baseChange B
  letI : Module.Free B N := Module.Free.of_basis b'
  letI : Module.Finite B N := Module.Finite.of_basis b'
  exact { base := B, carrier := Shrink.{t, max t w} N }

/-- The canonical morphism from a finite projective module to its pushforward. -/
private noncomputable def baseChangeHom
    (X : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k))
    (B : ArtinianLocalAlgCat.{u, w, w} Λ k) (f : X.base ⟶ B) :
    FiniteProjectiveModule.Hom.{u, w, w, t} X (baseChangeObj X B f) := by
  letI : Algebra X.base B := f.hom.toRingHom.toAlgebra
  let N := TensorProduct X.base B X.carrier
  letI : Small.{t} N := small_baseChange X B f
  let e : N ≃ₗ[B] Shrink.{t, max t w} N :=
    (Shrink.linearEquiv.{t, w, max t w} B N).symm
  let l : X.carrier →ₛₗ[f.hom.toRingHom] Shrink.{t, max t w} N :=
    { toFun := fun m => e (TensorProduct.tmul X.base (1 : B) m)
      map_add' := by intro m n; rw [TensorProduct.tmul_add, map_add]
      map_smul' := by
        intro a m
        rw [TensorProduct.tmul_smul]
        exact map_smul e (algebraMap X.base B a) _ }
  exact ⟨f, l, ⟨e, by intro m; rfl⟩⟩

/-- Base algebra structures along `b.base = a.base ≫ g` form a scalar tower. -/
private theorem isScalarTower_of_base_eq
    {X Y Z : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)}
    (a : FiniteProjectiveModule.Hom X Y) (b : FiniteProjectiveModule.Hom X Z)
    (g : Y.base ⟶ Z.base) (hbase : b.base = a.base ≫ g) :
    letI : Algebra X.base Y.base := a.base.hom.toRingHom.toAlgebra
    letI : Algebra X.base Z.base := b.base.hom.toRingHom.toAlgebra
    letI : Algebra Y.base Z.base := g.hom.toRingHom.toAlgebra
    IsScalarTower X.base Y.base Z.base := by
  let : Algebra X.base Y.base := a.base.hom.toRingHom.toAlgebra
  let : Algebra X.base Z.base := b.base.hom.toRingHom.toAlgebra
  let : Algebra Y.base Z.base := g.hom.toRingHom.toAlgebra
  have hAlg : b.base.hom = g.hom.comp a.base.hom := by
    simpa using congrArg (fun q : X.base ⟶ Z.base => q.hom) hbase
  exact IsScalarTower.of_algebraMap_eq' (R := X.base) (S := Y.base) (A := Z.base)
    (by ext r; exact congrArg (fun q => q r) hAlg)

/-- Given `a : X ⟶ Y` and `b : X ⟶ Z` and a morphism `g : Y.base ⟶ Z.base` of base algebras
with `b.base = a.base ≫ g`, the module of `Z` is obtained from the module of `Y` by extension
of scalars along `g`. -/
private noncomputable def fillEquiv
    {X Y Z : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)}
    (a : FiniteProjectiveModule.Hom X Y) (b : FiniteProjectiveModule.Hom X Z)
    (g : Y.base ⟶ Z.base) (hbase : b.base = a.base ≫ g) :
    (letI : Algebra Y.base Z.base := g.hom.toRingHom.toAlgebra
     (TensorProduct Y.base Z.base Y.carrier) ≃ₗ[Z.base] Z.carrier) := by
  letI : Algebra X.base Y.base := a.base.hom.toRingHom.toAlgebra
  letI : Algebra X.base Z.base := b.base.hom.toRingHom.toAlgebra
  letI : Algebra Y.base Z.base := g.hom.toRingHom.toAlgebra
  letI : IsScalarTower X.base Y.base Z.base := isScalarTower_of_base_eq a b g hbase
  let eA : TensorProduct X.base Y.base X.carrier ≃ₗ[Y.base] Y.carrier :=
    Classical.choose a.baseChange
  let eB : TensorProduct X.base Z.base X.carrier ≃ₗ[Z.base] Z.carrier :=
    Classical.choose b.baseChange
  let eChange : TensorProduct Y.base Z.base Y.carrier ≃ₗ[Z.base]
      TensorProduct Y.base Z.base (TensorProduct X.base Y.base X.carrier) :=
    LinearEquiv.baseChange Y.base Z.base Y.carrier _ eA.symm
  let eAssoc : TensorProduct X.base (TensorProduct Y.base Z.base Y.base) X.carrier ≃ₗ[Z.base]
      TensorProduct Y.base Z.base (TensorProduct X.base Y.base X.carrier) :=
    TensorProduct.AlgebraTensorModule.assoc X.base Y.base Z.base Z.base Y.base X.carrier
  let eRid : TensorProduct Y.base Z.base Y.base ≃ₗ[Z.base] Z.base :=
    TensorProduct.AlgebraTensorModule.rid Y.base Z.base Z.base
  let eTensor : TensorProduct X.base (TensorProduct Y.base Z.base Y.base) X.carrier ≃ₗ[Z.base]
      TensorProduct X.base Z.base X.carrier :=
    TensorProduct.AlgebraTensorModule.congr eRid (LinearEquiv.refl X.base X.carrier)
  exact eChange.trans eAssoc.symm |>.trans eTensor |>.trans eB

/-- The filling morphism `Y ⟶ Z` determined by `a : X ⟶ Y`, `b : X ⟶ Z` and a morphism of
base algebras `g` with `b.base = a.base ≫ g`. -/
private noncomputable def fillHom
    {X Y Z : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)}
    (a : FiniteProjectiveModule.Hom X Y) (b : FiniteProjectiveModule.Hom X Z)
    (g : Y.base ⟶ Z.base) (hbase : b.base = a.base ≫ g) :
    FiniteProjectiveModule.Hom Y Z := by
  letI : Algebra Y.base Z.base := g.hom.toRingHom.toAlgebra
  let e := fillEquiv a b g hbase
  let tmul : Y.carrier →ₛₗ[g.hom.toRingHom] TensorProduct Y.base Z.base Y.carrier :=
    { toFun := fun m => TensorProduct.tmul Y.base (1 : Z.base) m
      map_add' := by intro m n; exact TensorProduct.tmul_add (1 : Z.base) m n
      map_smul' := by intro c m; rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']; rfl }
  let l : Y.carrier →ₛₗ[g.hom.toRingHom] Z.carrier := e.toLinearMap.comp tmul
  exact ⟨g, l, ⟨e, by intro m; rfl⟩⟩

/-- The filling morphism is compatible with the two given morphisms out of `X`. -/
private theorem fillHom_linear
    {X Y Z : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)}
    (a : FiniteProjectiveModule.Hom X Y) (b : FiniteProjectiveModule.Hom X Z)
    (g : Y.base ⟶ Z.base) (hbase : b.base = a.base ≫ g) (m : X.carrier) :
    (fillHom a b g hbase).linear (a.linear m) = b.linear m := by
  classical
  let : Algebra X.base Y.base := a.base.hom.toRingHom.toAlgebra
  let : Algebra X.base Z.base := b.base.hom.toRingHom.toAlgebra
  let : Algebra Y.base Z.base := g.hom.toRingHom.toAlgebra
  let : IsScalarTower X.base Y.base Z.base := isScalarTower_of_base_eq a b g hbase
  have heA := Classical.choose_spec a.baseChange
  have heB := Classical.choose_spec b.baseChange
  change fillEquiv a b g hbase (TensorProduct.tmul Y.base (1 : Z.base) (a.linear m)) = _
  rw [← heA m]
  simp only [fillEquiv, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    LinearEquiv.symm_apply_apply,
    TensorProduct.AlgebraTensorModule.assoc_symm_tmul,
    TensorProduct.AlgebraTensorModule.congr_tmul, TensorProduct.AlgebraTensorModule.rid_tmul,
    one_smul]
  exact heB m

/-- A semilinear map out of `Y` is determined by its values on the image of `X`, because `Y` is
generated over `Y.base` by that image. -/
private theorem semilinear_eq_of_eq_on_image
    {X Y Z : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)}
    (a : FiniteProjectiveModule.Hom X Y)
    (f₁ f₂ : Y.base ⟶ Z.base) (hf : f₁ = f₂)
    (l₁ : Y.carrier →ₛₗ[f₁.hom.toRingHom] Z.carrier)
    (l₂ : Y.carrier →ₛₗ[f₂.hom.toRingHom] Z.carrier)
    (h : ∀ m : X.carrier, l₁ (a.linear m) = l₂ (a.linear m)) :
    ∀ y : Y.carrier, l₁ y = l₂ y := by
  let : Algebra X.base Y.base := a.base.hom.toRingHom.toAlgebra
  let e : TensorProduct X.base Y.base X.carrier ≃ₗ[Y.base] Y.carrier :=
    Classical.choose a.baseChange
  have he := Classical.choose_spec a.baseChange
  intro y
  have hgen : ∀ q : TensorProduct X.base Y.base X.carrier,
      l₁ (e q) = l₂ (e q) := by
    intro q
    induction q using TensorProduct.induction_on with
    | zero => rw [e.map_zero, l₁.map_zero, l₂.map_zero]
    | add q r hq hr =>
        rw [e.map_add, l₁.map_add, l₂.map_add, hq, hr]
    | tmul c m =>
        have htmul : TensorProduct.tmul X.base c m =
            c • TensorProduct.tmul X.base (1 : Y.base) m := by
          simp [TensorProduct.smul_tmul']
        have heval : e (TensorProduct.tmul X.base c m) = c • a.linear m := by
          rw [htmul, map_smul, he]
        rw [heval, l₁.map_smulₛₗ, l₂.map_smulₛₗ]
        have hmap : f₁.hom.toRingHom c = f₂.hom.toRingHom c :=
          congrArg (fun q => q.hom.toRingHom c) hf
        rw [hmap, h m]
  simpa using hgen (e.symm y)

namespace Family

/-- The projection from finite projective modules to their Artinian local base algebras is
cofibered in groupoids. -/
@[stacks 0D3I]
public theorem projection_isCofiberedInGroupoids
    (𝓕 : FiniteProjectiveModule.Family.{u, w, t} (Λ := Λ) (k := k)) :
    letI := 𝓕.category
    IsCofiberedInGroupoids 𝓕.projection := by
  let := 𝓕.category
  change (𝓕.projection.op).IsFiberedInGroupoids
  constructor
  · intro V U f x hx
    let X := x.unop
    have hX : 𝓕.projection.obj X = U.unop := congrArg Opposite.unop hx
    have hbase : X.base = U.unop := (𝓕.projection_obj X).symm.trans hX
    let g : X.base ⟶ V.unop := eqToHom hbase ≫ f.unop
    let Y := baseChangeObj X V.unop g
    let h := baseChangeHom X V.unop g
    let a : X ⟶ Y := 𝓕.homEquiv X Y |>.symm h
    refine ⟨Opposite.op Y, Opposite.op a, ?_⟩
    have hy : 𝓕.projection.op.obj (Opposite.op Y) = V := by
      change Opposite.op (𝓕.projection.obj Y) = Opposite.op (V.unop)
      exact congrArg Opposite.op (𝓕.projection_obj Y)
    apply IsHomLift.of_fac' (p := 𝓕.projection.op) f (Opposite.op a) hy hx
    apply Quiver.Hom.unop_inj
    change 𝓕.projection.map a = _
    calc
      𝓕.projection.map a = eqToHom (𝓕.projection_obj X) ≫ h.base ≫
            eqToHom (𝓕.projection_obj Y).symm := by
              rw [𝓕.projection_map_eq a]
              simp [a]
      _ = _ := by
        have hleft : eqToHom (𝓕.projection_obj X) ≫ eqToHom hbase =
            (eqToHom hx.symm).unop := by
          rw [eqToHom_trans, eqToHom_unop]
        have hright : eqToHom (𝓕.projection_obj Y).symm =
            (eqToHom hy).unop := by
          rw [eqToHom_unop]
          exact congrArg eqToHom (Subsingleton.elim _ _)
        simp only [h, baseChangeHom]
        dsimp [g]
        calc
          _ = (eqToHom (𝓕.projection_obj X) ≫ eqToHom hbase) ≫ f.unop ≫
                eqToHom (𝓕.projection_obj Y).symm := by rfl
          _ = (eqToHom hx.symm).unop ≫ f.unop ≫ (eqToHom hy).unop := by
                dsimp [Y, baseChangeObj] at hright ⊢
                rw [hleft, hright]
          _ = _ := by rfl
  · intro x y z φ ψ f hf
    let X := x.unop
    let Y := y.unop
    let Z := z.unop
    let a : X ⟶ Y := φ.unop
    let b : X ⟶ Z := ψ.unop
    let g : Y.base ⟶ Z.base :=
      eqToHom (𝓕.projection_obj Y).symm ≫ f.unop ≫
        eqToHom (𝓕.projection_obj Z)
    let ha := 𝓕.homEquiv X Y a
    let hb := 𝓕.homEquiv X Z b
    have hfbase : 𝓕.projection.map b = 𝓕.projection.map a ≫ f.unop :=
      Quiver.Hom.op_inj (by simpa [a, b] using hf.symm)
    have hbase : hb.base = ha.base ≫ g := by
      calc
        hb.base = eqToHom (𝓕.projection_obj X).symm ≫
            𝓕.projection.map b ≫ eqToHom (𝓕.projection_obj Z) := by
              rw [𝓕.projection_map b]
        _ = eqToHom (𝓕.projection_obj X).symm ≫
            (𝓕.projection.map a ≫ f.unop) ≫
              eqToHom (𝓕.projection_obj Z) := by rw [hfbase]
        _ = ha.base ≫ g := by
              rw [𝓕.projection_map_eq a]
              simp [ha, g, Category.assoc]
    let hfill := fillHom ha hb g hbase
    let c : Y ⟶ Z := (𝓕.homEquiv Y Z).symm hfill
    have hcomp : a ≫ c = b := by
      apply (𝓕.homEquiv X Z).injective
      let hc := 𝓕.homEquiv X Z (a ≫ c)
      have hcompBase : hc.base = hb.base := by
        calc
          hc.base = ha.base ≫
              (𝓕.homEquiv Y Z c).base := by rw [𝓕.comp_base]
          _ = ha.base ≫ g := by simp [c, hfill, fillHom]
          _ = hb.base := hbase.symm
      have hcompLinear : ∀ m, hc.linear m = hb.linear m := by
        intro m
        change (𝓕.homEquiv X Z (a ≫ c)).linear m = hb.linear m
        rw [𝓕.comp_linear]
        have hcFill : 𝓕.homEquiv Y Z c = hfill :=
          (𝓕.homEquiv Y Z).apply_symm_apply hfill
        rw [hcFill]
        exact fillHom_linear ha hb g hbase m
      exact FiniteProjectiveModule.Hom.ext_of_base_eq hc hb hcompBase hcompLinear
    have hmapc : 𝓕.projection.map c = f.unop := by
      calc
        𝓕.projection.map c = eqToHom (𝓕.projection_obj Y) ≫
            (𝓕.homEquiv Y Z c).base ≫
              eqToHom (𝓕.projection_obj Z).symm :=
          𝓕.projection_map_eq c
        _ = eqToHom (𝓕.projection_obj Y) ≫ g ≫
              eqToHom (𝓕.projection_obj Z).symm := by
                simp [c, hfill, fillHom]
        _ = f.unop := by simp [g, Category.assoc]
    refine ⟨Opposite.op c, ⟨Quiver.Hom.unop_inj (by simpa using hmapc),
      Quiver.Hom.unop_inj (by simpa [a, b] using hcomp)⟩, fun χ hχ => Quiver.Hom.unop_inj ?_⟩
    let d : Y ⟶ Z := χ.unop
    have hmapd : 𝓕.projection.map d = f.unop :=
      congrArg Quiver.Hom.unop (by simpa [d] using hχ.1 : (𝓕.projection.map d).op = f)
    have hbaseD : (𝓕.homEquiv Y Z d).base = g := by
      rw [← 𝓕.projection_map d, hmapd]
    have hcompD : a ≫ d = b := by simpa [a, b, d] using congrArg Quiver.Hom.unop hχ.2
    let hd := 𝓕.homEquiv Y Z d
    have hgen : ∀ m : X.carrier, hd.linear (ha.linear m) = hb.linear m := by
      intro m
      have heq := congrArg (fun q => q.linear m)
        (congrArg (𝓕.homEquiv X Z) hcompD)
      rw [𝓕.comp_linear] at heq
      simpa [hd, ha, hb] using heq
    have hlinPoint : ∀ m, hd.linear (ha.linear m) = hfill.linear (ha.linear m) := fun m =>
      (hgen m).trans (fillHom_linear ha hb g hbase m).symm
    have hbaseD' : hd.base = g := by simpa [hd] using hbaseD
    have hfun := semilinear_eq_of_eq_on_image ha hd.base g hbaseD'
      hd.linear hfill.linear hlinPoint
    have hbaseEq : hd.base = hfill.base := by
      rw [hbaseD']
      simp [hfill, fillHom]
    have hArrow : d = c := (𝓕.homEquiv Y Z).injective (by
      simpa [hd, c] using FiniteProjectiveModule.Hom.ext_of_base_eq hd hfill hbaseEq hfun)
    simpa [d] using hArrow

end Family

end Deformation.Examples.FiniteProjectiveModule
