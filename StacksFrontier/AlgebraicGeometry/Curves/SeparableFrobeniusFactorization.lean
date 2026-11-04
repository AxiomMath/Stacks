module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.SeparableClosure
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableFrobeniusChainAssembly
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula

/-!
# Separating a morphism of smooth proper curves by an iterated Frobenius

Let `k` be a field of characteristic `p > 0` and let `f : X ⟶ Y` be a nonconstant morphism of
proper smooth curves over `k`.  **Stacks 0CD2** asserts that `f` factors as
`X ⟶ X^(p^n) ⟶ Y`, where `X^(p^n) = X ×_{Spec k, F^n} Spec k` is the `n`-fold Frobenius twist of
`X`, the first morphism is the `n`-fold relative Frobenius of `X`, and the second is a
nonconstant morphism of proper smooth curves inducing a *separable* extension of function
fields.

The proof is the one of the source.  The separable closure `E` of `k(Y)` in `k(X)` is a finitely
generated extension of `k` of transcendence degree one, so by [Stacks, Tag 0BY1] it is the
function field of a proper nonsingular curve `Z` over `k`, and the inclusions
`k(Y) ⊆ E ⊆ k(X)` are induced by morphisms `X ⟶ Z ⟶ Y` composing to `f`.  The extension
`k(X)/E` is purely inseparable, so [Stacks, Tag 0CCZ] identifies `Z` with an iterated Frobenius
twist of `X` and `X ⟶ Z` with the iterated relative Frobenius.

## Main results

* `AlgebraicGeometry.exists_nFoldRelativeFrobenius_comp_isSeparable` — the factorization.

## Implementation notes

The Frobenius twist is the chosen categorical pullback of `X` along the `n`-fold absolute
Frobenius of `Spec k`, so the assertion `X^(p^n) = X ×_{Spec k, F^n} Spec k` of the source is
part of the shape of the statement rather than a separate conclusion, and the first morphism of
the factorization is `AlgebraicGeometry.nFoldRelativeFrobenius`.  Separability of the resulting
extension of function fields is stated for `AlgebraicGeometry.functionFieldMap`, the stalk map
of the second morphism at the generic point read through the identification of the image of that
generic point with the generic point of `Y`; that identification is also recorded as a clause of
the conclusion, and nonconstancy of the second morphism is recorded as the nontriviality of its
range, the reading of "nonconstant" used throughout this development.

## References

* [Stacks Project, Tag 0CD2](https://stacks.math.columbia.edu/tag/0CD2)
* [Stacks Project, Tag 030K](https://stacks.math.columbia.edu/tag/030K)
* [Stacks Project, Tag 0BY1](https://stacks.math.columbia.edu/tag/0BY1)
* [Stacks Project, Tag 0CCZ](https://stacks.math.columbia.edu/tag/0CCZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- **[Stacks, Tag 030K] for a morphism of proper curves, through [Stacks, Tag 0BY1].** A
nonconstant morphism `f : X ⟶ Y` of proper curves over `k` with `X` normal factors as
`X ⟶ Z ⟶ Y` through a proper nonsingular curve `Z` over `k` so that the extension of function
fields of `X ⟶ Z` is purely inseparable and that of `Z ⟶ Y` is separable: take for `Z` a proper
nonsingular model of the separable closure of `k(Y)` in `k(X)`. -/
private theorem exists_curve_separable_purelyInseparable_factorization {k : Type u} [Field k]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY] [IsNormal X] [IsProper pX] [IsProper pY]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (hn : (Set.range f).Nontrivial) :
    ∃ (Z : Scheme.{u}) (pZ : Z ⟶ Spec (.of k)) (_ : IsCurve k pZ) (_ : IsProper pZ)
      (_ : IsRegular Z) (a : X ⟶ Z) (b : Z ⟶ Y),
      a ≫ pZ = pX ∧ b ≫ pY = pZ ∧ a ≫ b = f ∧
        (Set.range a).Nontrivial ∧ (Set.range b).Nontrivial ∧
        (a.residueFieldMap (genericPoint X)).hom.IsPurelyInseparable ∧
        @Algebra.IsSeparable (Y.residueField (b (genericPoint Z)))
          (Z.residueField (genericPoint Z)) _ _
          (b.residueFieldMap (genericPoint Z)).hom.toAlgebra := by
  classical
  let VX : Variety k := { toScheme := X, structureMap := pX }
  let VY : Variety k := { toScheme := Y, structureMap := pY }
  let _ : Algebra k X.functionField := varietyFunctionFieldAlgebra VX
  let _ : Algebra k Y.functionField := varietyFunctionFieldAlgebra VY
  have _ : IsDominant f := isDominant_of_nontrivial_range_of_isCurve pX pY f hn
  let F : Over.mk pX ⟶ Over.mk pY := Over.homMk f hf
  have _ : IsDominant F.left := inferInstanceAs (IsDominant f)
  let φ : Y.functionField →ₐ[k] X.functionField :=
    { (functionFieldMap f) with commutes' := fun a => functionFieldMap_algebraMap VX VY F a }
  let _ : Algebra Y.functionField X.functionField := (functionFieldMap f).toAlgebra
  let _ : IsScalarTower k Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => (functionFieldMap_algebraMap VX VY F a).symm
  have htrY : Algebra.trdeg k Y.functionField = 1 :=
    (isCurve_iff_trdeg_functionField_eq_one VY).mp inferInstance
  let _ : Algebra.EssFiniteType k Y.functionField := varietyFunctionField_essFiniteType VY
  let _ : Module.Finite Y.functionField X.functionField :=
    finiteDimensional_functionField_of_isCurve pX pY f hf
  let _ : Algebra.IsAlgebraic Y.functionField X.functionField :=
    Algebra.IsAlgebraic.of_finite _ _
  -- the separable closure of `k(Y)` in `k(X)`, and its proper nonsingular model
  let E := separableClosure Y.functionField X.functionField
  let _ : Algebra.EssFiniteType k E := Algebra.EssFiniteType.comp k Y.functionField E
  have htrE : Algebra.trdeg k E = 1 := by
    have H := trdeg_add_eq k Y.functionField (A := E)
    rw [htrY, trdeg_eq_zero_iff.mpr inferInstance, add_zero] at H
    exact H.symm
  obtain ⟨M⟩ := nonempty_functionFieldModel (k := k) E htrE
  let VZ : Variety k := M.variety
  have hZcurve : IsCurve k VZ.structureMap := M.isCurve
  have hZproper : IsProper VZ.structureMap := M.isProper
  have hZnormal : IsNormal VZ.toScheme := isNormal_of_isRegular _ M.isRegular
  let _ : Algebra k VZ.toScheme.functionField := varietyFunctionFieldAlgebra VZ
  let ι : E →ₐ[k] X.functionField := E.val.restrictScalars k
  let ψ : Y.functionField →ₐ[k] E := IsScalarTower.toAlgHom k Y.functionField E
  obtain ⟨A, -, -, -, hAdom, hAff⟩ :=
    exists_hom_functionFieldMap_eq VX VZ (ι.comp M.equiv.toAlgHom)
  obtain ⟨B, -, -, -, hBdom, hBff⟩ :=
    exists_hom_functionFieldMap_eq VZ VY (M.equiv.symm.toAlgHom.comp ψ)
  have _ : IsDominant A.left := hAdom
  have _ : IsDominant B.left := hBdom
  -- the composition is `f`
  have hAB : A.left ≫ B.left = f := by
    have _ : IsDominant (A ≫ B).left :=
      ⟨B.left.denseRange.comp A.left.denseRange B.left.continuous⟩
    have hcomp : functionFieldMap (A ≫ B).left = functionFieldMap F.left := by
      show functionFieldMap (A.left ≫ B.left) = functionFieldMap f
      rw [functionFieldMap_comp A.left B.left, hAff, hBff]
      ext x
      show ι (M.equiv (M.equiv.symm (ψ x))) = functionFieldMap f x
      rw [M.equiv.apply_symm_apply]
      rfl
    exact congrArg Over.Hom.left (over_hom_ext_of_functionFieldMap VX VY (A ≫ B) F hcomp)
  -- the first morphism is purely inseparable
  have hApure : (functionFieldMap A.left).IsPurelyInseparable := by
    rw [hAff]
    refine RingHom.isPurelyInseparable_of_ringEquiv (algebraMap E X.functionField)
      (ι.comp M.equiv.toAlgHom).toRingHom M.equiv.symm.toRingEquiv (RingEquiv.refl _) ?_
      (RingHom.isPurelyInseparable_algebraMap_iff.mpr inferInstance)
    ext x
    show ι (M.equiv (M.equiv.symm x)) = algebraMap E X.functionField x
    rw [M.equiv.apply_symm_apply]
    rfl
  -- the second morphism is separable
  have hBsep : @Algebra.IsSeparable Y.functionField VZ.toScheme.functionField _ _
      (functionFieldMap B.left).toAlgebra := by
    let _ : Algebra Y.functionField VZ.toScheme.functionField :=
      (functionFieldMap B.left).toAlgebra
    refine Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl Y.functionField)
      M.equiv.symm.toRingEquiv ?_
    ext x
    show functionFieldMap B.left x = M.equiv.symm (algebraMap Y.functionField E x)
    rw [hBff]
    rfl
  exact ⟨VZ.toScheme, VZ.structureMap, hZcurve, hZproper, M.isRegular, A.left, B.left,
    A.w, B.w, hAB, nontrivial_range_of_isDominant_of_isCurve pX VZ.structureMap A.left A.w,
    nontrivial_range_of_isDominant_of_isCurve VZ.structureMap pY B.left B.w,
    (isPurelyInseparable_functionFieldMap_iff_residueFieldMap A.left).mp hApure,
    (isSeparable_functionField_iff_residueField B.left).mp hBsep⟩

/-- **Stacks Project, Tag 0CD2.** Let `k` be a field of characteristic `p > 0` and let
`f : X ⟶ Y` be a nonconstant morphism of proper smooth curves over `k`.  Then `f` factors as
`X ⟶ X^(p^n) ⟶ Y`, where `X^(p^n)` is the `n`-fold Frobenius twist of `X`, that is, the base
change of `X` along the `n`-fold absolute Frobenius of `Spec k`, the first morphism is the
`n`-fold relative Frobenius of `X`, and the second is a nonconstant morphism of proper smooth
curves over `k` inducing a separable extension of function fields. -/
@[stacks 0CD2]
theorem exists_nFoldRelativeFrobenius_comp_isSeparable {k : Type u} [Field k] (p : ℕ)
    [Fact p.Prime] (hk : IsInCharacteristic (Spec (.of k)) p)
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY] [Smooth pX] [Smooth pY] [IsProper pX] [IsProper pY]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (hnonconstant : (Set.range f).Nontrivial) :
    ∃ n : ℕ,
      let T := nFoldFrobeniusTwist (Spec (.of k)) p hk n (Over.mk pX)
      ∃ (g : T.left ⟶ Y) (hcurve : IsCurve k T.hom) (hdom : IsDominant g),
        letI := hcurve
        letI := hdom
        Smooth T.hom ∧ IsProper T.hom ∧ g ≫ pY = T.hom ∧
          f = (nFoldRelativeFrobenius (Spec (.of k)) p hk n (Over.mk pX)).left ≫ g ∧
          (Set.range g).Nontrivial ∧ g (genericPoint T.left) = genericPoint Y ∧
          @Algebra.IsSeparable Y.functionField T.left.functionField _ _
            (functionFieldMap g).toAlgebra := by
  classical
  have _ : CharP k p := by
    refine (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr ?_
    simpa only [map_natCast, map_zero] using congrArg (Scheme.ΓSpecIso (.of k)).hom hk
  have hXreg : IsRegular X := isRegular_of_smooth_over_field pX
  have _ : IsNormal X := isNormal_of_isRegular X hXreg
  obtain ⟨Z, pZ, hZcurve, hZproper, hZreg, a, b, ha, hb, hab, hna, hnb, hapure, hbsep⟩ :=
    exists_curve_separable_purelyInseparable_factorization pX pY f hf hnonconstant
  obtain ⟨n, ⟨e, he, -⟩, -⟩ := existsUnique_nat_existsUnique_iso_nFoldFrobeniusTwist p hk pX pZ
    hXreg hZreg a ha hna hapure
  refine ⟨n, ?_⟩
  intro T
  have hTsmooth : Smooth T.hom :=
    InseparableFrobeniusIteration.smooth_nFoldFrobeniusTwist (Spec (.of k)) p hk n
      (Over.mk pX) (show Smooth (Over.mk pX).hom from inferInstanceAs (Smooth pX))
  have hTproper : IsProper T.hom := by
    show IsProper (pullback.snd pX (absoluteFrobeniusPow (Spec (.of k)) p hk n))
    infer_instance
  have hTcurve : IsCurve k T.hom :=
    InseparableFrobeniusIteration.isCurve_nFoldFrobeniusTwist p hk n (Over.mk pX)
      (show IsCurve k (Over.mk pX).hom from inferInstanceAs (IsCurve k pX))
      (show Smooth (Over.mk pX).hom from inferInstanceAs (Smooth pX))
  have _ : IsIso e.hom.left := Functor.map_isIso (Over.forget (Spec (.of k))) e.hom
  have hgfactor : (nFoldRelativeFrobenius (Spec (.of k)) p hk n (Over.mk pX)).left ≫
      e.hom.left = a := by
    rw [← Over.comp_left, he]
    rfl
  have _ : IsDominant b := isDominant_of_nontrivial_range_of_isCurve pZ pY b hnb
  have hgdom : IsDominant (e.hom.left ≫ b) :=
    ⟨b.denseRange.comp e.hom.left.denseRange b.continuous⟩
  have hgw : (e.hom.left ≫ b) ≫ pY = T.hom := by
    rw [Category.assoc, hb]
    exact e.hom.w
  refine ⟨e.hom.left ≫ b, hTcurve, hgdom, hTsmooth, hTproper, hgw, ?_,
    nontrivial_range_of_isDominant_of_isCurve T.hom pY (e.hom.left ≫ b) hgw,
    (congrArg b (genericPoint_eq_of_isOpenImmersion e.hom.left)).trans
      (map_genericPoint_of_isDominant b), ?_⟩
  · rw [← hab, ← hgfactor, Category.assoc]
  · let _ : Algebra Y.functionField (Over.mk pZ).left.functionField :=
      (functionFieldMap b).toAlgebra
    have _ : Algebra.IsSeparable Y.functionField (Over.mk pZ).left.functionField :=
      (isSeparable_functionField_iff_residueField b).mpr hbsep
    let _ : Algebra Y.functionField T.left.functionField :=
      (functionFieldMap (e.hom.left ≫ b)).toAlgebra
    have hbij : Function.Bijective (functionFieldMap e.hom.left) :=
      functionFieldMap_bijective_of_residueDegree_eq_one e.hom.left
        (InseparableFrobeniusIteration.residueDegree_of_isIso e.hom.left (genericPoint T.left))
    refine Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl Y.functionField)
      (RingEquiv.ofBijective _ hbij) ?_
    ext x
    show functionFieldMap (e.hom.left ≫ b) x = functionFieldMap e.hom.left
      (functionFieldMap b x)
    rw [functionFieldMap_comp e.hom.left b]
    rfl

end AlgebraicGeometry

end
