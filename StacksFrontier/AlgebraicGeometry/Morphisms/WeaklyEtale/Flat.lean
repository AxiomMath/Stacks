module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.WeaklyEtale.Flat
public import StacksCore.Tactic.StacksAttribute

/-!
# Flatness over the source from a flat diagonal

Let `f : X ⟶ Y` be a morphism of schemes whose diagonal is flat. An `O_X`-module that is flat
over `Y` is flat over `X`.

## Main results

* `AlgebraicGeometry.isFlatOver_self_of_flat_diagonal` gives flatness over the source.

## Implementation notes

The local ring at a point of `X ×_Y X` above the diagonal image of `x` is a localization of
`O_{X,x} ⊗_{O_{Y,f x}} O_{X,x}`, and flatness of the diagonal transfers along that localization
to flatness of the multiplication map. The module is an arbitrary sheaf of modules; no
quasi-coherence is assumed.

## References

* [Stacks Project, Tag 094R](https://stacks.math.columbia.edu/tag/094R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

private lemma stalkCongr_hom_comp {X : TopCat} (F : X.Presheaf CommRingCat)
    {x y z : X} (hxy : x = y) (hyz : y = z) :
    (F.stalkCongr (.of_eq hxy)).hom ≫ (F.stalkCongr (.of_eq hyz)).hom =
      (F.stalkCongr (.of_eq (hxy.trans hyz))).hom := by
  cases hxy
  cases hyz
  simp [TopCat.Presheaf.stalkCongr]

private lemma stalkCongr_inv_hom {X : TopCat} (F : X.Presheaf CommRingCat)
    {x y : X} (h : x = y) :
    (F.stalkCongr (.of_eq h)).inv =
      (F.stalkCongr (.of_eq h.symm)).hom := by
  cases h
  simp [TopCat.Presheaf.stalkCongr]

private lemma stalkCongr_eqToHom_cancel {X : TopCat} (F : X.Presheaf CommRingCat)
    {x y : X} (h : x = y) :
    eqToHom (congrArg F.stalk h) ≫ (F.stalkCongr (.of_eq h.symm)).hom = 𝟙 (F.stalk x) := by
  cases h
  simp

private lemma moduleFlat_stalk_congr {X : Scheme} (F : X.Modules)
    {x y : X} (h : x = y) :
    (by
      let M : PresheafOfModules.{u}
          (X.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) := inferInstance
      exact Module.Flat (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)) ↔
    (by
      let M : PresheafOfModules.{u}
          (X.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
      letI : Module (X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf y) := inferInstance
      exact Module.Flat (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf y)) := by
  cases h
  rfl

/-- If the diagonal of a scheme morphism is flat, every module flat over the
target is flat over the source. -/
@[stacks 094R]
theorem isFlatOver_self_of_flat_diagonal
    {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    [Flat (pullback.diagonal f)]
    (hF : IsFlatOver f.toLRSHom.toShHom F) :
    IsFlatOver ((𝟙 X : X ⟶ X).toLRSHom.toShHom) F := by
  intro x
  let z : (pullback f f).carrier := pullback.diagonal f x
  let R := Y.presheaf.stalk ((pullback.fst f f ≫ f).base z)
  let A := X.presheaf.stalk ((pullback.fst f f) z)
  let B := X.presheaf.stalk ((pullback.snd f f) z)
  let C := (pullback f f).presheaf.stalk z
  let M : PresheafOfModules.{u}
      (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
  let N := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf
    ((pullback.fst f f) z)
  have hpt (g : pullback f f ⟶ X) (hg : pullback.diagonal f ≫ g = 𝟙 X) : g z = x := by
    show (pullback.diagonal f ≫ g) x = x
    rw [hg]
    rfl
  have hx₁ : (pullback.fst f f) z = x := hpt _ (pullback.diagonal_fst f)
  have hx₂ : (pullback.snd f f) z = x := hpt _ (pullback.diagonal_snd f)
  have hx₂₁ : (pullback.snd f f) z = (pullback.fst f f) z :=
    hx₂.trans hx₁.symm
  let h : (pullback.fst f f ≫ f).base z = (pullback.snd f f ≫ f).base z := by
    rw [Scheme.Hom.comp_base, TopCat.comp_app,
      Scheme.Hom.comp_base, TopCat.comp_app]
    exact congrArg (fun p : X => f.base p) (hx₁.trans hx₂.symm)
  let : Algebra R A := (f.stalkMap ((pullback.fst f f) z)).hom.toAlgebra
  let : Algebra R B :=
    ((eqToHom (congrArg Y.presheaf.stalk h) ≫
      f.stalkMap ((pullback.snd f f) z)).hom).toAlgebra
  let : Module A N := inferInstance
  let : Module R N := Module.compHom N (f.stalkMap ((pullback.fst f f) z)).hom
  let : IsScalarTower R A N :=
    IsScalarTower.of_algebraMap_smul (fun r n => rfl)
  have hN : Module.Flat R N := hF ((pullback.fst f f) z)
  obtain ⟨φ, hφleft, hφright, W, hW⟩ :=
    BaseChangeStalk.pullback_stalk_isLocalization f f z
  let : Algebra (A ⊗[R] B) C := φ.toAlgebra
  let : Algebra R (A ⊗[R] B) := Algebra.TensorProduct.leftAlgebra
  let : IsLocalization W C := by simpa [C] using hW
  have hφ : φ.Flat := by
    show Module.Flat (A ⊗[R] B) C
    exact IsLocalization.flat C W
  let eIso := X.presheaf.stalkCongr (.of_eq hx₂₁)
  let e : B ≃ₐ[R] A :=
    { toRingEquiv := eIso.commRingCatIsoToRingEquiv
      commutes' := by
        intro r
        show ((eIso.hom.hom.comp
          ((f.stalkMap ((pullback.snd f f) z)).hom.comp
            (eqToHom (congrArg Y.presheaf.stalk h)).hom)) r) =
          (f.stalkMap ((pullback.fst f f) z)).hom r
        have hnat := Scheme.Hom.stalkMap_congr_point f
          ((pullback.snd f f) z) ((pullback.fst f f) z) hx₂₁
        have hcanc :
            eqToHom (congrArg Y.presheaf.stalk h) ≫
              (Y.presheaf.stalkCongr (.of_eq
                (congrArg (fun p : X => f.base p) hx₂₁))).hom = 𝟙 R :=
          stalkCongr_eqToHom_cancel Y.presheaf h
        have hcat :
            eqToHom (congrArg Y.presheaf.stalk h) ≫
              f.stalkMap ((pullback.snd f f) z) ≫ eIso.hom =
            f.stalkMap ((pullback.fst f f) z) := by
          refine (congrArg
            (fun k => eqToHom (congrArg Y.presheaf.stalk h) ≫ k) hnat).trans ?_
          refine (Category.assoc _ _ _).symm.trans ?_
          refine (congrArg
            (fun k => k ≫ f.stalkMap ((pullback.fst f f) z)) hcanc).trans ?_
          exact Category.id_comp _
        have hring := congrArg CommRingCat.Hom.hom hcat
        exact DFunLike.congr_fun hring r }
  let eX := X.presheaf.stalkCongr (.of_eq hx₁)
  let ψ : C →+* A := ((pullback.diagonal f).stalkMap x ≫ eX.inv).hom
  have hψ : ψ.Flat := by
    show RingHom.Flat (eX.inv.hom.comp ((pullback.diagonal f).stalkMap x).hom)
    exact RingHom.Flat.comp
      (Flat.stalkMap (pullback.diagonal f) x)
      (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso eX.inv))
  have hdiag (g : pullback f f ⟶ X) (hg : pullback.diagonal f ≫ g = 𝟙 X) (hgz : g z = x) :
      g.stalkMap z ≫ (pullback.diagonal f).stalkMap x =
        (X.presheaf.stalkCongr (.of_eq hgz)).hom := by
    rw [← Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_congr_hom _ (𝟙 X) hg x,
      Scheme.Hom.stalkMap_id]
    rfl
  have hleft : ψ.comp ((pullback.fst f f).stalkMap z).hom = RingHom.id A := by
    show CommRingCat.Hom.hom
      (((pullback.fst f f).stalkMap z ≫
        (pullback.diagonal f).stalkMap x) ≫ eX.inv) = RingHom.id A
    rw [hdiag _ (pullback.diagonal_fst f) hx₁]
    change CommRingCat.Hom.hom (eX.hom ≫ eX.inv) = _
    simp [A]
  have hright : ψ.comp ((pullback.snd f f).stalkMap z).hom = e.toRingHom := by
    show CommRingCat.Hom.hom
      (((pullback.snd f f).stalkMap z ≫
        (pullback.diagonal f).stalkMap x) ≫ eX.inv) = eIso.hom.hom
    rw [hdiag _ (pullback.diagonal_snd f) hx₂, stalkCongr_inv_hom X.presheaf hx₁]
    apply congrArg CommRingCat.Hom.hom
    have htrans : hx₂.trans hx₁.symm = hx₂₁ := Subsingleton.elim _ _
    simpa [eIso, htrans] using stalkCongr_hom_comp X.presheaf hx₂ hx₁.symm
  let θ := Algebra.TensorProduct.congr
    (AlgEquiv.refl : A ≃ₐ[R] A) e.symm
  have hφleft_apply (a : A) :
      φ (Algebra.TensorProduct.includeLeftRingHom a) =
        ((pullback.fst f f).stalkMap z).hom a := by
    show (φ.comp Algebra.TensorProduct.includeLeftRingHom) a = _
    exact DFunLike.congr_fun hφleft a
  have hφright_apply (b : B) :
      φ (Algebra.TensorProduct.includeRight.toRingHom b) =
        ((pullback.snd f f).stalkMap z).hom b := by
    show (φ.comp Algebra.TensorProduct.includeRight.toRingHom) b = _
    exact DFunLike.congr_fun hφright b
  have hleft_apply (a : A) :
      ψ (((pullback.fst f f).stalkMap z).hom a) = a := by
    show (ψ.comp ((pullback.fst f f).stalkMap z).hom) a = RingHom.id A a
    exact DFunLike.congr_fun hleft a
  have hright_apply (b : B) :
      ψ (((pullback.snd f f).stalkMap z).hom b) =
        e.toRingEquiv.toRingHom b := by
    show (ψ.comp ((pullback.snd f f).stalkMap z).hom) b =
      e.toRingEquiv.toRingHom b
    exact DFunLike.congr_fun hright b
  have hlmulLeft (a : A) :
      (Algebra.TensorProduct.lmul' R (S := A)).toRingHom
        (Algebra.TensorProduct.includeLeftRingHom a) = a := by
    simp [Algebra.TensorProduct.includeLeftRingHom,
      Algebra.TensorProduct.lmul'_apply_tmul]
  have hlmulRight (a : A) :
      (Algebra.TensorProduct.lmul' R (S := A)).toRingHom
        (Algebra.TensorProduct.includeRight.toRingHom a) = a := by
    simp [Algebra.TensorProduct.includeRight, Algebra.TensorProduct.lmul'_apply_tmul]
  have hmul : (ψ.comp φ).comp θ.toRingHom =
      (Algebra.TensorProduct.lmul' R (S := A)).toRingHom := by
    apply Algebra.TensorProduct.ringHom_ext
    · ext a
      show ψ (φ (θ (Algebra.TensorProduct.includeLeftRingHom a))) =
        (Algebra.TensorProduct.lmul' R (S := A)).toRingHom
          (Algebra.TensorProduct.includeLeftRingHom a)
      rw [show θ (Algebra.TensorProduct.includeLeftRingHom a) =
        Algebra.TensorProduct.includeLeftRingHom a by
          simp [θ, Algebra.TensorProduct.includeLeftRingHom]]
      rw [hφleft_apply]
      exact (hleft_apply a).trans (hlmulLeft a).symm
    · ext a
      show ψ (φ (θ (Algebra.TensorProduct.includeRight.toRingHom a))) =
        (Algebra.TensorProduct.lmul' R (S := A)).toRingHom
          (Algebra.TensorProduct.includeRight.toRingHom a)
      rw [show θ (Algebra.TensorProduct.includeRight.toRingHom a) =
        Algebra.TensorProduct.includeRight.toRingHom (e.symm a) by
          simp [θ, Algebra.TensorProduct.includeRight]]
      rw [hφright_apply, hright_apply]
      exact (show e (e.symm a) = a by simp).trans (hlmulRight a).symm
  have hMulFlat : Algebra.MulFlat R A := by
    show (Algebra.TensorProduct.lmul' R (S := A)).toRingHom.Flat
    rw [← hmul]
    have hθ : θ.toRingEquiv.toRingHom.Flat :=
      RingHom.Flat.of_bijective θ.bijective
    exact RingHom.Flat.comp hθ (RingHom.Flat.comp hφ hψ)
  have hresult := flat_of_flat_of_mul_flat R A hMulFlat N hN
  show IsFlatOverAt ((Scheme.Hom.toLRSHom (𝟙 X)).toShHom) F x
  have hid : (𝟙 X : X ⟶ X).toLRSHom.toShHom = 𝟙 (X.toSheafedSpace) := by rfl
  rw [hid]
  simp only [IsFlatOverAt, SheafedSpace.id_hom, PresheafedSpace.id_base, TopCat.hom_id,
    ContinuousMap.id_apply]
  have hpoint := (moduleFlat_stalk_congr F hx₁).mp hresult
  have hstalk : CommRingCat.Hom.hom
      ((𝟙 (X.toSheafedSpace) : X.toSheafedSpace ⟶ X.toSheafedSpace).hom.stalkMap x) =
        RingHom.id (X.presheaf.stalk x) :=
    congrArg CommRingCat.Hom.hom
      (PresheafedSpace.stalkMap.id X.toSheafedSpace.toPresheafedSpace x)
  rw [hstalk]
  exact hpoint

end AlgebraicGeometry
