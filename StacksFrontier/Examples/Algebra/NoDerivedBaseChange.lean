module

public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.Tor.ChangeOfRings
public import StacksFrontier.Homology.DerivedComplete.PrincipalTorsionTower
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute

/-!
# Failure of derived base change

Derived base change does not factor through the derived category of the ordinary tensor product:
there are two maps out of a commutative ring `R`, to `A` and to `R'`, for which derived tensoring
with `R'` cannot be lifted from `D(R')` to the derived category of the ordinary tensor product
`A ⊗[R] R'`. The failure already occurs on modules, so no exactness of a proposed lift is needed.

The source's example is `R = k[x, y]`, `R' = R/(xy)` and `A = R/(x²)`; the version proved here
takes `A = R/(x)`, for which the obstruction is already visible on the module `A` itself. Over
`B = A ⊗[R] R'` the candidate value of the lift would be an object of `D(B)` whose two nonzero
homology modules are both free of rank one, so it would split as a direct sum of two shifts of `B`;
restricting that splitting to `R'` would make the mapping cone of multiplication by `x` on `R'`
isomorphic to a split sum, which it is not.

## Main results

* `Stacks.Examples.no_derived_base_change`: rings for which no functor from `D(A)` to
  `D(A ⊗[R] R')` has the prescribed value on every module after restriction to `R'`.

## Implementation notes

Because the obstruction is object-level, the statement does not require the proposed functor to be
triangulated. The condition is expressed by objectwise isomorphisms in `D(R')`; no choice or
naturality of these isomorphisms is assumed.

## References

* [Stacks Project, Tag 08J3](https://stacks.math.columbia.edu/tag/08J3)
-/

@[expose] public section

open CategoryTheory TensorProduct
open CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars

universe u


namespace Stacks.Examples

attribute [local instance] HasDerivedCategory.standard

private noncomputable def homologyRestrictScalarsIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (E : DerivedCategory (ModuleCat.{u} S)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((ModuleCat.restrictScalars f).mapDerivedCategory.obj E) ≅
      (ModuleCat.restrictScalars f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj E) := by
  let P := DerivedCategory.Q.objPreimage E
  let e : DerivedCategory.Q.obj P ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let U := ModuleCat.restrictScalars f
  exact (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      ((U.mapDerivedCategory.mapIso e).symm ≪≫ U.mapDerivedCategoryFactors.app P) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app _ ≪≫
    (ShortComplex.mapHomologyIso (P.sc i) U) ≪≫
    U.mapIso ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S) i).app P).symm ≪≫
    U.mapIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).mapIso e)

private theorem isZero_homology_restrictScalars_iff
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (E : DerivedCategory (ModuleCat.{u} S)) (i : ℤ) :
    CategoryTheory.Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((ModuleCat.restrictScalars f).mapDerivedCategory.obj E)) ↔
    CategoryTheory.Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj E) := by
  rw [(homologyRestrictScalarsIso f E i).isZero_iff]
  simp only [ModuleCat.isZero_iff_subsingleton]
  rfl

private theorem isGE_restrictScalars_iff
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (E : DerivedCategory (ModuleCat.{u} S)) (n : ℤ) :
    ((ModuleCat.restrictScalars f).mapDerivedCategory.obj E).IsGE n ↔ E.IsGE n := by
  rw [DerivedCategory.isGE_iff, DerivedCategory.isGE_iff]
  exact forall₂_congr fun i _ => isZero_homology_restrictScalars_iff f E i

private theorem isLE_restrictScalars_iff
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (E : DerivedCategory (ModuleCat.{u} S)) (n : ℤ) :
    ((ModuleCat.restrictScalars f).mapDerivedCategory.obj E).IsLE n ↔ E.IsLE n := by
  rw [DerivedCategory.isLE_iff, DerivedCategory.isLE_iff]
  exact forall₂_congr fun i _ => isZero_homology_restrictScalars_iff f E i

private noncomputable def xTensorQuotientEquiv
    (k : Type u) [CommRing k] :
    (CochainComplex.DerivedChangeOfRings.NodalRing k ⧸
      (Ideal.span {CochainComplex.DerivedChangeOfRings.xVariable k}).map
        (algebraMap (CochainComplex.DerivedChangeOfRings.PolynomialRing k)
          (CochainComplex.DerivedChangeOfRings.NodalRing k))) ≃+*
      (CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k ⊗[
        CochainComplex.DerivedChangeOfRings.PolynomialRing k]
        CochainComplex.DerivedChangeOfRings.NodalRing k) := by
  let I : Ideal (CochainComplex.DerivedChangeOfRings.PolynomialRing k) :=
    Ideal.span {CochainComplex.DerivedChangeOfRings.xVariable k}
  letI : CommRing (CochainComplex.DerivedChangeOfRings.PolynomialRing k) := inferInstance
  letI : CommRing (CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k) :=
    Ideal.Quotient.commRing I
  letI : CommRing (CochainComplex.DerivedChangeOfRings.NodalRing k) :=
    Ideal.Quotient.commRing _
  letI : Algebra (CochainComplex.DerivedChangeOfRings.NodalRing k)
      (CochainComplex.DerivedChangeOfRings.NodalRing k ⊗[
        CochainComplex.DerivedChangeOfRings.PolynomialRing k]
        CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k) :=
    Algebra.TensorProduct.leftAlgebra
  letI : Algebra (CochainComplex.DerivedChangeOfRings.NodalRing k)
      (CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k ⊗[
        CochainComplex.DerivedChangeOfRings.PolynomialRing k]
        CochainComplex.DerivedChangeOfRings.NodalRing k) :=
    Algebra.TensorProduct.rightAlgebra
  letI : Algebra (CochainComplex.DerivedChangeOfRings.NodalRing k)
      (CochainComplex.DerivedChangeOfRings.NodalRing k ⧸
        I.map (algebraMap (CochainComplex.DerivedChangeOfRings.PolynomialRing k)
          (CochainComplex.DerivedChangeOfRings.NodalRing k))) :=
    Ideal.Quotient.algebra _
  let e₁ := Algebra.TensorProduct.quotIdealMapEquivTensorQuot
    (CochainComplex.DerivedChangeOfRings.NodalRing k) I
  let e₂ := AlgEquiv.extendScalarsOfSurjective
    (R := CochainComplex.DerivedChangeOfRings.PolynomialRing k)
    (S := CochainComplex.DerivedChangeOfRings.NodalRing k)
    (A := CochainComplex.DerivedChangeOfRings.NodalRing k ⊗[
      CochainComplex.DerivedChangeOfRings.PolynomialRing k]
      CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k)
    (B := CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k ⊗[
      CochainComplex.DerivedChangeOfRings.PolynomialRing k]
      CochainComplex.DerivedChangeOfRings.NodalRing k)
    (show Function.Surjective
      (algebraMap (CochainComplex.DerivedChangeOfRings.PolynomialRing k)
        (CochainComplex.DerivedChangeOfRings.NodalRing k)) from fun s => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
      exact ⟨r, rfl⟩)
    (Algebra.TensorProduct.comm _ _ _)
  simpa only [I] using (e₁.trans e₂).toRingEquiv

private noncomputable abbrev xConeTriangle (k : Type u) [CommRing k] :=
  DerivedCategory.Q.mapTriangle.obj
    (CochainComplex.mappingCone.triangle
      (CochainComplex.DerivedChangeOfRings.scalarMultiplication
        (CochainComplex.DerivedChangeOfRings.NodalRing k)
        (CochainComplex.DerivedChangeOfRings.xClass k)))

private noncomputable abbrev xConeModule (k : Type u) [CommRing k] :=
  ModuleCat.of (CochainComplex.DerivedChangeOfRings.NodalRing k)
    (CochainComplex.DerivedChangeOfRings.NodalRing k)

private theorem singleHomologyIsZero {S : Type u} [CommRing S]
    (M : ModuleCat.{u} S) (i j : ℤ) (h : i ≠ j) :
    CategoryTheory.Limits.IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} S) i).obj ((DerivedCategory.singleFunctor
        (ModuleCat.{u} S) j).obj M)) := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact DerivedCategory.isZero_of_isGE _ j i hlt
  · exact DerivedCategory.isZero_of_isLE _ j i hgt

private noncomputable def xConeSingleHomology (k : Type u) [CommRing k] :
  (DerivedCategory.homologyFunctor (ModuleCat.{u}
    (CochainComplex.DerivedChangeOfRings.NodalRing k)) (0 : ℤ)).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u}
        (CochainComplex.DerivedChangeOfRings.NodalRing k)) 0).obj (xConeModule k)) ≅
    xConeModule k :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u}
    (CochainComplex.DerivedChangeOfRings.NodalRing k)) 0).app (xConeModule k)

private theorem xCone_homology_mor₁ (k : Type u) [CommRing k] :
    (DerivedCategory.homologyFunctor (ModuleCat.{u}
      (CochainComplex.DerivedChangeOfRings.NodalRing k)) 0).map
        (xConeTriangle k).mor₁ ≫ (xConeSingleHomology k).hom =
      (xConeSingleHomology k).hom ≫
        PrincipalTorsionTower.powerMultiplication
          (CochainComplex.DerivedChangeOfRings.NodalRing k) (xConeModule k)
          (CochainComplex.DerivedChangeOfRings.xClass k) := by
  let S := CochainComplex.DerivedChangeOfRings.NodalRing k
  let a := CochainComplex.DerivedChangeOfRings.xClass k
  let M := xConeModule k
  exact (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} S) 0).hom.naturality
    (PrincipalTorsionTower.powerMultiplication S M a)

private theorem xConeTorsionKernel (k : Type u) [CommRing k] :
    let T := xConeTriangle k
    let δ := DerivedCategory.HomologySequence.δ T (-1) 0 (by omega) ≫
        (xConeSingleHomology k).hom
    ∃ h : δ ≫ PrincipalTorsionTower.powerMultiplication
      (CochainComplex.DerivedChangeOfRings.NodalRing k) (xConeModule k)
      (CochainComplex.DerivedChangeOfRings.xClass k) = 0,
      Nonempty (CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.KernelFork.ofι δ h)) := by
  let S := CochainComplex.DerivedChangeOfRings.NodalRing k
  let M := xConeModule k
  let T := xConeTriangle k
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} S) 0
  let a := CochainComplex.DerivedChangeOfRings.xClass k
  let p := PrincipalTorsionTower.powerMultiplication S M a
  let δ := DerivedCategory.HomologySequence.δ T (-1) 0 (by omega) ≫
    (xConeSingleHomology k).hom
  have hT : T ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished _
  have hδ : δ ≫ p = 0 := by
    calc
      δ ≫ p = DerivedCategory.HomologySequence.δ T (-1) 0 (by omega) ≫
            ((xConeSingleHomology k).hom ≫ p) :=
          Category.assoc (DerivedCategory.HomologySequence.δ T (-1) 0 (by omega))
            (xConeSingleHomology k).hom p
      _ = DerivedCategory.HomologySequence.δ T (-1) 0 (by omega) ≫
            (H.map T.mor₁ ≫ (xConeSingleHomology k).hom) :=
          congrArg (fun z => DerivedCategory.HomologySequence.δ T (-1) 0 (by omega) ≫ z)
            (xCone_homology_mor₁ k).symm
      _ = (DerivedCategory.HomologySequence.δ T (-1) 0 (by omega) ≫ H.map T.mor₁) ≫
            (xConeSingleHomology k).hom :=
          (Category.assoc (DerivedCategory.HomologySequence.δ T (-1) 0 (by omega))
            (H.map T.mor₁) (xConeSingleHomology k).hom).symm
      _ = 0 ≫ (xConeSingleHomology k).hom :=
          congrArg (fun z => z ≫ (xConeSingleHomology k).hom)
            (DerivedCategory.HomologySequence.δ_comp T hT (-1) 0)
      _ = 0 := zero_comp
  let Z := ShortComplex.mk δ p hδ
  have hZ : Z.Exact := by
    apply ShortComplex.exact_of_iso _ (DerivedCategory.HomologySequence.exact₁ T hT (-1) 0)
    exact ShortComplex.isoMk (Iso.refl _) (xConeSingleHomology k) (xConeSingleHomology k)
      (by simp [Z, δ]) (by exact (xCone_homology_mor₁ k).symm)
  have hmono : Mono (DerivedCategory.HomologySequence.δ T (-1) 0) :=
    (DerivedCategory.HomologySequence.exact₃ T hT (-1) 0).mono_g_iff.mpr
      ((singleHomologyIsZero M (-1) 0 (by omega)).eq_of_src _ _)
  have : Mono Z.f := by
    dsimp only [Z, δ]
    exact mono_comp' hmono (IsIso.mono_of_iso (xConeSingleHomology k).hom)
  exact ⟨hδ, ⟨hZ.fIsKernel⟩⟩

private noncomputable def xConeHomologyMinusOneIso (k : Type u) [CommRing k] :
    (DerivedCategory.homologyFunctor (ModuleCat.{u}
      (CochainComplex.DerivedChangeOfRings.NodalRing k)) (-1)).obj
      (DerivedCategory.Q.obj (CochainComplex.DerivedChangeOfRings.xMultiplicationComplex k)) ≅
    CategoryTheory.Limits.kernel (PrincipalTorsionTower.powerMultiplication
      (CochainComplex.DerivedChangeOfRings.NodalRing k) (xConeModule k)
      (CochainComplex.DerivedChangeOfRings.xClass k)) :=
  (xConeTorsionKernel k).choose_spec.some.conePointUniqueUpToIso
    (CategoryTheory.Limits.limit.isLimit _)

private theorem xConeQuotientCokernel (k : Type u) [CommRing k] :
    let T := xConeTriangle k
    let b := (xConeSingleHomology k).inv ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u}
        (CochainComplex.DerivedChangeOfRings.NodalRing k)) 0).map T.mor₂
    ∃ h : PrincipalTorsionTower.powerMultiplication
      (CochainComplex.DerivedChangeOfRings.NodalRing k) (xConeModule k)
      (CochainComplex.DerivedChangeOfRings.xClass k) ≫ b = 0,
      Nonempty (CategoryTheory.Limits.IsColimit
        (CategoryTheory.Limits.CokernelCofork.ofπ b h)) := by
  let S := CochainComplex.DerivedChangeOfRings.NodalRing k
  let M := xConeModule k
  let T := xConeTriangle k
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} S) 0
  let a := CochainComplex.DerivedChangeOfRings.xClass k
  let p := PrincipalTorsionTower.powerMultiplication S M a
  let e₂ : H.obj T.obj₂ ≅ M := by
    dsimp [T, xConeTriangle]
    exact xConeSingleHomology k
  let e₁ : H.obj T.obj₁ ≅ M := xConeSingleHomology k
  let b := e₂.inv ≫ H.map T.mor₂
  have hT : T ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished _
  have hnat : H.map T.mor₁ ≫ e₂.hom = e₁.hom ≫ p := xCone_homology_mor₁ k
  have hm : p ≫ e₂.inv = e₁.inv ≫ H.map T.mor₁ := by
    calc
      p ≫ e₂.inv = e₁.inv ≫ (e₁.hom ≫ p) ≫ e₂.inv := by simp
      _ = e₁.inv ≫ (H.map T.mor₁ ≫ e₂.hom) ≫ e₂.inv := by rw [← hnat]
      _ = e₁.inv ≫ H.map T.mor₁ := by simp
  have hb : p ≫ b = 0 := by
    dsimp only [b]
    rw [← Category.assoc, hm, Category.assoc, ← Functor.map_comp,
      Pretriangulated.comp_distTriang_mor_zero₁₂ T hT, Functor.map_zero]
    simp
  let Z := ShortComplex.mk p b hb
  have hZ : Z.Exact := by
    apply ShortComplex.exact_of_iso _ (DerivedCategory.HomologySequence.exact₂ T hT 0)
    exact ShortComplex.isoMk e₁ e₂ (Iso.refl _)
      (by simpa [Z, p] using hnat.symm)
      (by
        change e₂.hom ≫ (e₂.inv ≫ H.map T.mor₂) = H.map T.mor₂ ≫ 𝟙 _
        simp)
  have hEpi : Epi (H.map T.mor₂) :=
    (DerivedCategory.HomologySequence.exact₃ T hT 0 1).epi_f_iff.mpr
      ((singleHomologyIsZero M 1 0 (by omega)).eq_of_tgt _ _)
  have : Epi Z.g := by
    dsimp only [Z, b]
    infer_instance
  exact ⟨hb, ⟨hZ.gIsCokernel⟩⟩

private noncomputable def xConeHomologyZeroIso (k : Type u) [CommRing k] :
    (DerivedCategory.homologyFunctor (ModuleCat.{u}
      (CochainComplex.DerivedChangeOfRings.NodalRing k)) 0).obj
      (DerivedCategory.Q.obj (CochainComplex.DerivedChangeOfRings.xMultiplicationComplex k)) ≅
    CategoryTheory.Limits.cokernel (PrincipalTorsionTower.powerMultiplication
      (CochainComplex.DerivedChangeOfRings.NodalRing k) (xConeModule k)
      (CochainComplex.DerivedChangeOfRings.xClass k)) :=
  (xConeQuotientCokernel k).choose_spec.some.coconePointUniqueUpToIso
    (CategoryTheory.Limits.colimit.isColimit _)

private theorem range_lsmul_eq_span {S : Type u} [CommRing S] (a : S) :
    LinearMap.range (LinearMap.lsmul S S a) = Ideal.span {a} := by
  ext z
  change (∃ r : S, a * r = z) ↔ z ∈ Ideal.span {a}
  rw [Ideal.mem_span_singleton]
  exact ⟨fun ⟨r, hr⟩ => ⟨r, hr.symm⟩, fun ⟨r, hr⟩ => ⟨r, hr.symm⟩⟩

private noncomputable def xConeCokernelToXAxisModule (k : Type u) [CommRing k] :
    CategoryTheory.Limits.cokernel (PrincipalTorsionTower.powerMultiplication
      (CochainComplex.DerivedChangeOfRings.NodalRing k) (xConeModule k)
      (CochainComplex.DerivedChangeOfRings.xClass k)) ≅
    ModuleCat.of (CochainComplex.DerivedChangeOfRings.NodalRing k)
      (CochainComplex.DerivedChangeOfRings.XAxisModule k) := by
  let S := CochainComplex.DerivedChangeOfRings.NodalRing k
  let a := CochainComplex.DerivedChangeOfRings.xClass k
  let p := PrincipalTorsionTower.powerMultiplication S (xConeModule k) a
  have h : p.hom.range = (CochainComplex.DerivedChangeOfRings.xAxisIdeal k : Submodule S S) := by
    change LinearMap.range (LinearMap.lsmul S S a) = _
    simpa [CochainComplex.DerivedChangeOfRings.xAxisIdeal, a] using
      range_lsmul_eq_span (S := S) a
  exact ModuleCat.cokernelIsoRangeQuotient p ≪≫ (Submodule.quotEquivOfEq _ _ h).toModuleIso

private noncomputable def xConeHomologyZeroToXAxisModule (k : Type u) [CommRing k] :
    (DerivedCategory.homologyFunctor (ModuleCat.{u}
      (CochainComplex.DerivedChangeOfRings.NodalRing k)) 0).obj
      (DerivedCategory.Q.obj (CochainComplex.DerivedChangeOfRings.xMultiplicationComplex k)) ≅
    ModuleCat.of (CochainComplex.DerivedChangeOfRings.NodalRing k)
      (CochainComplex.DerivedChangeOfRings.XAxisModule k) :=
  xConeHomologyZeroIso k ≪≫ xConeCokernelToXAxisModule k

private theorem nodal_x_annihilator (k : Type u) [CommRing k]
    (element : CochainComplex.DerivedChangeOfRings.NodalRing k) :
    CochainComplex.DerivedChangeOfRings.xClass k * element = 0 ↔
      element ∈ Ideal.span {CochainComplex.DerivedChangeOfRings.yClass k} := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective element
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨Ideal.Quotient.mk _ q, ?_⟩
    apply Ideal.Quotient.eq.mpr
    have hp : p = CochainComplex.DerivedChangeOfRings.yVariable k * q := by
      rw [← MvPolynomial.X_mul_cancel_left_iff (i := false)]
      simpa [mul_assoc] using hq
    simp [hp]
  · rintro ⟨q, hq⟩
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective q
    apply Ideal.Quotient.eq.mp at hq
    rw [Ideal.mem_span_singleton] at hq
    obtain ⟨r, hr⟩ := hq
    exact ⟨q + CochainComplex.DerivedChangeOfRings.xVariable k * r, by
      linear_combination CochainComplex.DerivedChangeOfRings.xVariable k * hr⟩

private theorem nodal_y_annihilator (k : Type u) [CommRing k]
    (element : CochainComplex.DerivedChangeOfRings.NodalRing k) :
    CochainComplex.DerivedChangeOfRings.yClass k * element = 0 ↔
      element ∈ Ideal.span {CochainComplex.DerivedChangeOfRings.xClass k} := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective element
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨Ideal.Quotient.mk _ q, ?_⟩
    apply Ideal.Quotient.eq.mpr
    have hp : p = CochainComplex.DerivedChangeOfRings.xVariable k * q := by
      rw [← MvPolynomial.X_mul_cancel_left_iff (i := true), hq]
      ring
    simp [hp]
  · rintro ⟨q, hq⟩
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective q
    apply Ideal.Quotient.eq.mp at hq
    rw [Ideal.mem_span_singleton] at hq
    obtain ⟨r, hr⟩ := hq
    exact ⟨q + CochainComplex.DerivedChangeOfRings.yVariable k * r, by
      linear_combination CochainComplex.DerivedChangeOfRings.yVariable k * hr⟩

private noncomputable def xAxisModuleEquivXKernel (k : Type u) [CommRing k] :
    CochainComplex.DerivedChangeOfRings.XAxisModule k ≃ₗ[
      CochainComplex.DerivedChangeOfRings.NodalRing k]
      (LinearMap.lsmul (CochainComplex.DerivedChangeOfRings.NodalRing k)
        (CochainComplex.DerivedChangeOfRings.NodalRing k)
        (CochainComplex.DerivedChangeOfRings.xClass k)).ker := by
  let S := CochainComplex.DerivedChangeOfRings.NodalRing k
  let x := CochainComplex.DerivedChangeOfRings.xClass k
  let y := CochainComplex.DerivedChangeOfRings.yClass k
  let fx := LinearMap.lsmul S S x
  let fy := LinearMap.lsmul S S y
  have hker : LinearMap.ker fy =
      (CochainComplex.DerivedChangeOfRings.xAxisIdeal k : Submodule S S) := by
    ext z
    change y * z = 0 ↔ z ∈ CochainComplex.DerivedChangeOfRings.xAxisIdeal k
    exact nodal_y_annihilator k z
  have hrange : LinearMap.range fy = LinearMap.ker fx := by
    ext z
    constructor
    · rintro ⟨r, rfl⟩
      change x * (y * r) = 0
      have hxy : x * y = 0 := by
        change CochainComplex.DerivedChangeOfRings.nodalRingMap k
          (CochainComplex.DerivedChangeOfRings.xVariable k *
            CochainComplex.DerivedChangeOfRings.yVariable k) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span (Set.mem_singleton _)
      rw [← mul_assoc, hxy, zero_mul]
    · intro hz
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp ((nodal_x_annihilator k z).mp hz)
      exact ⟨r, hr.symm⟩
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivRange fy) |>.trans
    (LinearEquiv.ofEq _ _ hrange)

private noncomputable def xConeKernelToXAxisModule (k : Type u) [CommRing k] :
    CategoryTheory.Limits.kernel (PrincipalTorsionTower.powerMultiplication
      (CochainComplex.DerivedChangeOfRings.NodalRing k) (xConeModule k)
      (CochainComplex.DerivedChangeOfRings.xClass k)) ≅
    ModuleCat.of (CochainComplex.DerivedChangeOfRings.NodalRing k)
      (CochainComplex.DerivedChangeOfRings.XAxisModule k) := by
  let S := CochainComplex.DerivedChangeOfRings.NodalRing k
  let p := PrincipalTorsionTower.powerMultiplication S (xConeModule k)
    (CochainComplex.DerivedChangeOfRings.xClass k)
  exact (ModuleCat.kernelIsoKer p) ≪≫
    (xAxisModuleEquivXKernel k).toModuleIso.symm

private noncomputable def xConeHomologyMinusOneToXAxisModule (k : Type u) [CommRing k] :
    (DerivedCategory.homologyFunctor (ModuleCat.{u}
      (CochainComplex.DerivedChangeOfRings.NodalRing k)) (-1)).obj
      (DerivedCategory.Q.obj (CochainComplex.DerivedChangeOfRings.xMultiplicationComplex k)) ≅
    ModuleCat.of (CochainComplex.DerivedChangeOfRings.NodalRing k)
      (CochainComplex.DerivedChangeOfRings.XAxisModule k) :=
  xConeHomologyMinusOneIso k ≪≫ xConeKernelToXAxisModule k

@[instance_reducible]
private noncomputable def xAxisModuleNodalAlgebra (k : Type u) [CommRing k] :
    Algebra (CochainComplex.DerivedChangeOfRings.NodalRing k)
      (CochainComplex.DerivedChangeOfRings.XAxisModule k) :=
  Ideal.Quotient.algebra _

attribute [local instance] xAxisModuleNodalAlgebra

@[instance_reducible]
private noncomputable def xTensorNodalAlgebra (k : Type u) [CommRing k] :
    Algebra (CochainComplex.DerivedChangeOfRings.NodalRing k)
      (CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k ⊗[
        CochainComplex.DerivedChangeOfRings.PolynomialRing k]
        CochainComplex.DerivedChangeOfRings.NodalRing k) :=
  Algebra.TensorProduct.rightAlgebra

attribute [local instance] xTensorNodalAlgebra

@[instance_reducible]
private noncomputable def xTensorNodalModule (k : Type u) [CommRing k] :
  Module (CochainComplex.DerivedChangeOfRings.NodalRing k)
      (CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k ⊗[
        CochainComplex.DerivedChangeOfRings.PolynomialRing k]
        CochainComplex.DerivedChangeOfRings.NodalRing k) := by
  let S := CochainComplex.DerivedChangeOfRings.NodalRing k
  let B := CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k ⊗[
    CochainComplex.DerivedChangeOfRings.PolynomialRing k]
    CochainComplex.DerivedChangeOfRings.NodalRing k
  letI : CommSemiring S := inferInstance
  letI : Semiring B := inferInstance
  letI : Algebra S B := xTensorNodalAlgebra k
  exact Algebra.toModule

attribute [local instance] xTensorNodalModule

private noncomputable def xAxisTensorLinearEquiv (k : Type u) [CommRing k] :
    CochainComplex.DerivedChangeOfRings.XAxisModule k ≃ₗ[
      CochainComplex.DerivedChangeOfRings.NodalRing k]
      (CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k ⊗[
        CochainComplex.DerivedChangeOfRings.PolynomialRing k]
        CochainComplex.DerivedChangeOfRings.NodalRing k) := by
  let S := CochainComplex.DerivedChangeOfRings.NodalRing k
  let A := CochainComplex.DerivedChangeOfRings.XAxisModule k
  let B := CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k ⊗[
    CochainComplex.DerivedChangeOfRings.PolynomialRing k]
    CochainComplex.DerivedChangeOfRings.NodalRing k
  let R := CochainComplex.DerivedChangeOfRings.PolynomialRing k
  let I : Ideal R := Ideal.span {CochainComplex.DerivedChangeOfRings.xVariable k}
  letI : CommRing S := inferInstance
  letI : CommRing A := inferInstance
  letI : CommRing B := inferInstance
  have hI : CochainComplex.DerivedChangeOfRings.xAxisIdeal k =
      I.map (algebraMap R S) := by
    change Ideal.span {CochainComplex.DerivedChangeOfRings.xClass k} = _
    rw [Ideal.map_span, Set.image_singleton]
    congr 1
  let e := (Ideal.quotEquivOfEq hI).trans (xTensorQuotientEquiv k)
  have he (s : S) : e (algebraMap S A s) = algebraMap S B s := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    have hq : (Ideal.quotEquivOfEq hI) (algebraMap S A
        (Ideal.Quotient.mk (CochainComplex.DerivedChangeOfRings.nodalRelationIdeal k) r)) =
        Ideal.Quotient.mk (I.map (algebraMap R S)) (algebraMap R S r) := by
      change (Ideal.quotEquivOfEq hI)
          (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ r)) =
        Ideal.Quotient.mk _ (Ideal.Quotient.mk _ r)
      rw [Ideal.quotEquivOfEq_mk]
    change xTensorQuotientEquiv k
      ((Ideal.quotEquivOfEq hI) (algebraMap S A
        (Ideal.Quotient.mk (CochainComplex.DerivedChangeOfRings.nodalRelationIdeal k) r))) = _
    rw [hq]
    rw [← Ideal.Quotient.mk_algebraMap]
    change Algebra.TensorProduct.comm R S
      (CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k)
        (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I
          (Ideal.Quotient.mk (I.map (algebraMap R S)) (algebraMap R S r))) = _
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    rw [Algebra.TensorProduct.comm_tmul]
    rw [Algebra.TensorProduct.right_algebraMap_apply]
    rw [Ideal.Quotient.algebraMap_eq]
  refine
    { toFun := e
      invFun := e.symm
      map_add' := e.map_add
      map_smul' := ?_
      left_inv := e.left_inv
      right_inv := e.right_inv }
  intro s a
  change e (algebraMap S A s * a) = s • e a
  rw [Algebra.smul_def, e.map_mul, he]

private noncomputable def xConeHomologyZeroAsTensorLinearEquiv (k : Type u) [CommRing k] :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u}
      (CochainComplex.DerivedChangeOfRings.NodalRing k)) 0).obj
      (DerivedCategory.Q.obj (CochainComplex.DerivedChangeOfRings.xMultiplicationComplex k))) ≃ₗ[
        CochainComplex.DerivedChangeOfRings.NodalRing k]
      (CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k ⊗[
        CochainComplex.DerivedChangeOfRings.PolynomialRing k]
        CochainComplex.DerivedChangeOfRings.NodalRing k) :=
  (xConeHomologyZeroToXAxisModule k).toLinearEquiv.trans (xAxisTensorLinearEquiv k)

private noncomputable def xConeHomologyMinusOneAsTensorLinearEquiv (k : Type u) [CommRing k] :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u}
      (CochainComplex.DerivedChangeOfRings.NodalRing k)) (-1)).obj
      (DerivedCategory.Q.obj (CochainComplex.DerivedChangeOfRings.xMultiplicationComplex k))) ≃ₗ[
        CochainComplex.DerivedChangeOfRings.NodalRing k]
      (CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k ⊗[
        CochainComplex.DerivedChangeOfRings.PolynomialRing k]
        CochainComplex.DerivedChangeOfRings.NodalRing k) :=
  (xConeHomologyMinusOneToXAxisModule k).toLinearEquiv.trans (xAxisTensorLinearEquiv k)

private theorem derivedObject_splits_of_free_homology
    {S : Type u} [CommRing S] (E : DerivedCategory (ModuleCat.{u} S))
    [E.IsGE (-1 : ℤ)] [E.IsLE (0 : ℤ)]
    (hfree : ∀ i : ℤ, Module.Free S
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj E)) :
    Nonempty (E ≅ ⨁ fun i : Finset.Icc (-1 : ℤ) 0 =>
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) i.1).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i.1).obj E)) := by
  have hproj (i : ℤ) : CategoryTheory.Projective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj E) := by
    let := hfree i
    let := Module.Projective.of_free (R := S)
      (P := (DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj E)
    exact ModuleCat.projective_of_categoryTheory_projective _
  apply DerivedCategory.nonempty_iso_biproduct_singleFunctor_obj_homology_of_forall_ext_eq_zero
    E (-1) 0
  intro i j p hij hp e
  let : CategoryTheory.Projective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj E) := hproj i
  exact e.eq_zero_of_hasProjectiveDimensionLT 1 (by omega)

private theorem quotientRightTensorAlgebraMap_surjective
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) :
    letI : Algebra R (R ⧸ I) := inferInstance
    letI : Algebra S ((R ⧸ I) ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    Function.Surjective (algebraMap S ((R ⧸ I) ⊗[R] S)) := by
  let e := TensorProduct.quotTensorEquivQuotSMul (M := S) I
  intro b
  let J := I • (⊤ : Submodule R S)
  obtain ⟨s, hs⟩ := Submodule.mkQ_surjective J (e b)
  refine ⟨s, ?_⟩
  apply e.injective
  simpa [e, Algebra.TensorProduct.right_algebraMap_apply] using hs

private noncomputable def linearEquiv_lift_surjective
    {R S M N : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module S M] [Module S N]
    [Module R M] [Module R N] (f : R →+* S) (hf : Function.Surjective f)
    (e : M ≃ₗ[R] N)
    (hM : ∀ (r : R) (m : M), r • m = f r • m)
    (hN : ∀ (r : R) (n : N), r • n = f r • n) : M ≃ₗ[S] N := by
  letI : Algebra R S := f.toAlgebra
  haveI : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul
    (fun r m => (hM r m).symm)
  haveI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul
    (fun r n => (hN r n).symm)
  exact LinearEquiv.extendScalarsOfSurjective hf e

private noncomputable def twoTermBiproductToSplit (k : Type u) [CommRing k] :
    let S := CochainComplex.DerivedChangeOfRings.NodalRing k
    let N : ModuleCat.{u} S := ModuleCat.of S
      (CochainComplex.DerivedChangeOfRings.XAxisModule k)
    ((DerivedCategory.singleFunctor (ModuleCat.{u} S) (-1)).obj N) ⊞
        ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj N) ≅
      DerivedCategory.Q.obj (CochainComplex.DerivedChangeOfRings.splitXAxisComplex k) := by
  let S := CochainComplex.DerivedChangeOfRings.NodalRing k
  let N : ModuleCat.{u} S := ModuleCat.of S
    (CochainComplex.DerivedChangeOfRings.XAxisModule k)
  let C := CochainComplex.DerivedChangeOfRings.singleModule S
    (CochainComplex.DerivedChangeOfRings.XAxisModule k)
  let KminusOne := (DerivedCategory.singleFunctor (ModuleCat.{u} S) (-1)).obj N
  let Kzero := (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj N
  letI : PreservesBinaryBiproducts (DerivedCategory.Q (C := ModuleCat.{u} S)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let hshift := (DerivedCategory.Q.commShiftIso (1 : ℤ)).app C ≪≫
    ((DerivedCategory.singleFunctors (ModuleCat.{u} S)).shiftIso 1 (-1) 0 (by decide)).app N
  exact biprod.mapIso hshift.symm (Iso.refl Kzero) ≪≫
    (DerivedCategory.Q.mapBiprod (C⟦(1 : ℤ)⟧) C).symm

private theorem extensionScalars_xAxisModel
    (k : Type u) [CommRing k] [Nontrivial k] :
    Nonempty
      (((derivedExtensionScalarsGeneral
            (CochainComplex.DerivedChangeOfRings.nodalRingMap k)).functor.obj
          (((ModuleCat.restrictScalars (Ideal.Quotient.mk
              (Ideal.span
                {CochainComplex.DerivedChangeOfRings.xVariable k}))).mapDerivedCategory).obj
            ((DerivedCategory.singleFunctor
                (ModuleCat.{u} (CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k)) 0).obj
              (ModuleCat.of (CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k)
                (CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k))))) ≅
        CochainComplex.DerivedChangeOfRings.derivedTensorRestrictedXAxisWithNodalRing k) := by
  let R := CochainComplex.DerivedChangeOfRings.PolynomialRing k
  let A := CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k
  let R' := CochainComplex.DerivedChangeOfRings.NodalRing k
  let f : R →+* A :=
    Ideal.Quotient.mk (Ideal.span {CochainComplex.DerivedChangeOfRings.xVariable k})
  let g : R →+* R' := CochainComplex.DerivedChangeOfRings.nodalRingMap k
  let P := CochainComplex.DerivedChangeOfRings.xAxisResolution k
  let ε := (CochainComplex.DerivedChangeOfRings.derivedTensorModuleStructuresDiffer
    k).xAxisAugmentation
  let F := ModuleCat.restrictScalars f
  let D := derivedExtensionScalarsGeneral g
  let M : ModuleCat.{u} A := ModuleCat.of A A
  have hε : IsIso (DerivedCategory.Q.map ε) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (CochainComplex.DerivedChangeOfRings.derivedTensorModuleStructuresDiffer
        k).xAxisAugmentation_quasiIso
  have hcmp : IsIso (D.comparison.app P) :=
    D.comparison_isIso_of_kFlat P
      (CochainComplex.DerivedChangeOfRings.derivedTensorModuleStructuresDiffer
        k).xAxisResolution_kFlat
  have hsingle := F.mapDerivedCategorySingleFunctor 0
  have hinput : (F.mapDerivedCategory).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≅
      (DerivedCategory.Q.obj P) := by
    refine (hsingle.app M) ≪≫ ?_ ≪≫ (asIso (DerivedCategory.Q.map ε)).symm
    change (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (F.obj M) ≅
      DerivedCategory.Q.obj (CochainComplex.DerivedChangeOfRings.singleModule R A)
    rfl
  change Nonempty (D.functor.obj
      ((F.mapDerivedCategory).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) ≅
      CochainComplex.DerivedChangeOfRings.derivedTensorRestrictedXAxisWithNodalRing k)
  refine ⟨D.functor.mapIso hinput ≪≫ asIso (D.comparison.app P) ≪≫ ?_⟩
  rfl

private noncomputable def rightTensorAlgebraMap (k : Type u) [CommRing k] :
    CochainComplex.DerivedChangeOfRings.NodalRing k →+*
      (CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k ⊗[
        CochainComplex.DerivedChangeOfRings.PolynomialRing k]
        CochainComplex.DerivedChangeOfRings.NodalRing k) :=
  @algebraMap _ _ _ _ (xTensorNodalAlgebra k)

private theorem no_lift_xAxisModel (k : Type u) [CommRing k] [Nontrivial k] :
    let R := CochainComplex.DerivedChangeOfRings.PolynomialRing k
    let S := CochainComplex.DerivedChangeOfRings.NodalRing k
    let A := CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k
    let B := A ⊗[R] S
    let I : Ideal R := Ideal.span {CochainComplex.DerivedChangeOfRings.xVariable k}
    letI : CommRing R := inferInstance
    letI : CommRing A := Ideal.Quotient.commRing I
    letI : CommRing S := Ideal.Quotient.commRing
      (CochainComplex.DerivedChangeOfRings.nodalRelationIdeal k)
    letI : CommRing B := inferInstance
    letI : Algebra R A := (Ideal.Quotient.mk I).toAlgebra
    letI : Algebra R S := (CochainComplex.DerivedChangeOfRings.nodalRingMap k).toAlgebra
    letI : Algebra S B := Algebra.TensorProduct.rightAlgebra
    ∀ (E : DerivedCategory (ModuleCat.{u} B)),
      Nonempty
        (((ModuleCat.restrictScalars.{u} (rightTensorAlgebraMap k)).mapDerivedCategory.obj E) ≅
          DerivedCategory.Q.obj (CochainComplex.DerivedChangeOfRings.xMultiplicationComplex k)) →
        False := by
  dsimp only
  intro E hE
  let R := CochainComplex.DerivedChangeOfRings.PolynomialRing k
  let S := CochainComplex.DerivedChangeOfRings.NodalRing k
  let A := CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k
  let B := A ⊗[R] S
  let I : Ideal R := Ideal.span {CochainComplex.DerivedChangeOfRings.xVariable k}
  let : CommRing R := inferInstance
  let : CommRing A := Ideal.Quotient.commRing I
  let : CommRing S := Ideal.Quotient.commRing
    (CochainComplex.DerivedChangeOfRings.nodalRelationIdeal k)
  let : CommRing B := inferInstance
  let : Algebra R A := (Ideal.Quotient.mk I).toAlgebra
  let : Algebra R S := (CochainComplex.DerivedChangeOfRings.nodalRingMap k).toAlgebra
  let : Algebra S B := Algebra.TensorProduct.rightAlgebra
  let U := ModuleCat.restrictScalars.{u} (rightTensorAlgebraMap k)
  have hsurj : Function.Surjective (rightTensorAlgebraMap k) := by
    change Function.Surjective (algebraMap S (A ⊗[R] S))
    exact quotientRightTensorAlgebraMap_surjective (R := R) (S := S) I
  obtain ⟨eModel⟩ := hE
  let H_B (i : ℤ) := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  let H_S (i : ℤ) := DerivedCategory.homologyFunctor (ModuleCat.{u} S) i
  let N : ModuleCat.{u} S := ModuleCat.of S (CochainComplex.DerivedChangeOfRings.XAxisModule k)
  let eBN : U.obj (ModuleCat.of B B) ≅ N := (xAxisTensorLinearEquiv k).symm.toModuleIso
  let P := CochainComplex.DerivedChangeOfRings.xMultiplicationComplex k
  have key (i : ℤ) (e : (H_S i).obj (DerivedCategory.Q.obj P) ≃ₗ[S] B) :
      Module.Free B ((H_B i).obj E) ∧ Nonempty (U.mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) i).obj ((H_B i).obj E)) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} S) i).obj N) := by
    let : Module S ((H_B i).obj E) :=
      Module.compHom ((H_B i).obj E) (rightTensorAlgebraMap k)
    let eS : U.obj ((H_B i).obj E) ≅ ModuleCat.of S B :=
      (homologyRestrictScalarsIso (rightTensorAlgebraMap k) E i).symm ≪≫
        (H_S i).mapIso eModel ≪≫ e.toModuleIso
    let eB : ((H_B i).obj E) ≃ₗ[B] B :=
      linearEquiv_lift_surjective (rightTensorAlgebraMap k) hsurj eS.toLinearEquiv
        (fun _ _ => rfl) (fun r b => Algebra.smul_def r b)
    exact ⟨Module.Free.of_equiv eB.symm, ⟨U.mapDerivedCategory.mapIso
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) i).mapIso eB.toModuleIso) ≪≫
      (U.mapDerivedCategorySingleFunctor i).app (ModuleCat.of B B) ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) i).mapIso eBN⟩⟩
  have : P.IsStrictlyGE (-1 : ℤ) := by
    dsimp [P, CochainComplex.DerivedChangeOfRings.xMultiplicationComplex]
    exact CochainComplex.isStrictlyGE_mappingCone _ 0 0 (-1) (by omega) (by omega)
  have : P.IsStrictlyLE (0 : ℤ) := by
    dsimp [P, CochainComplex.DerivedChangeOfRings.xMultiplicationComplex]
    exact CochainComplex.isStrictlyLE_mappingCone _ 0 0 0 (by omega) (by omega)
  have hRestGE : (U.mapDerivedCategory.obj E).IsGE (-1 : ℤ) :=
    DerivedCategory.TStructure.t.isGE_of_iso eModel.symm (-1)
  have hRestLE : (U.mapDerivedCategory.obj E).IsLE (0 : ℤ) :=
    DerivedCategory.TStructure.t.isLE_of_iso eModel.symm 0
  have : E.IsGE (-1 : ℤ) := (isGE_restrictScalars_iff (rightTensorAlgebraMap k) E (-1)).1 hRestGE
  have : E.IsLE (0 : ℤ) := (isLE_restrictScalars_iff (rightTensorAlgebraMap k) E 0).1 hRestLE
  have hsplit : Nonempty (E ≅ ⨁ fun i : ↥(Finset.Icc (-1 : ℤ) 0) =>
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) i.1).obj ((H_B i.1).obj E)) := by
    have hfree (i : ℤ) : Module.Free B ((H_B i).obj E) := by
      obtain rfl | rfl | hi : i = -1 ∨ i = 0 ∨ i < -1 ∨ 0 < i := by omega
      · exact (key _ (xConeHomologyMinusOneAsTensorLinearEquiv k)).1
      · exact (key _ (xConeHomologyZeroAsTensorLinearEquiv k)).1
      · have : Subsingleton ((H_B i).obj E) :=
          ModuleCat.isZero_iff_subsingleton.mp <| hi.elim
            (fun h => DerivedCategory.isZero_of_isGE E (-1) i h)
            (fun h => DerivedCategory.isZero_of_isLE E 0 i h)
        exact Module.Free.of_subsingleton B _
    exact derivedObject_splits_of_free_homology E hfree
  obtain ⟨eSplit⟩ := hsplit
  let F := fun i : ↥(Finset.Icc (-1 : ℤ) 0) =>
    (DerivedCategory.singleFunctor (ModuleCat.{u} B) i.1).obj ((H_B i.1).obj E)
  let X := (DerivedCategory.singleFunctor (ModuleCat.{u} B) (-1)).obj ((H_B (-1)).obj E)
  let Y := (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj ((H_B 0).obj E)
  let eIndex : (↥(Finset.Icc (-1 : ℤ) 0)) ≃ CategoryTheory.Limits.WalkingPair :=
    { toFun := fun i => if i.1 = -1 then CategoryTheory.Limits.WalkingPair.left
        else CategoryTheory.Limits.WalkingPair.right
      invFun := fun w => match w with
        | CategoryTheory.Limits.WalkingPair.left => ⟨-1, by norm_num [Finset.mem_Icc]⟩
        | CategoryTheory.Limits.WalkingPair.right => ⟨0, by norm_num [Finset.mem_Icc]⟩
      left_inv := fun i => by
        have hm := Finset.mem_Icc.mp i.2
        apply Subtype.ext
        by_cases h : i.1 = -1
        · simp [h]
        · have h0 : i.1 = 0 := by omega
          simp [h0]
      right_inv := fun w => by cases w <;> rfl }
  let G := CategoryTheory.Limits.pairFunction X Y
  have heq (i : ↥(Finset.Icc (-1 : ℤ) 0)) : G (eIndex i) = F i := by
    have hm := Finset.mem_Icc.mp i.2
    obtain h | h : i.1 = -1 ∨ i.1 = 0 := by omega
    · obtain rfl : i = ⟨-1, by simp⟩ := Subtype.ext h
      simp [eIndex, F, G, X]
    · obtain rfl : i = ⟨0, by simp⟩ := Subtype.ext h
      simp [eIndex, F, G, Y]
  let eIndexSum := biproduct.whiskerEquiv eIndex (fun i => eqToIso (heq i))
  let b := biproduct.bicone G
  let hb : b.toBinaryBicone.IsBilimit :=
    (Bicone.toBinaryBiconeIsBilimit b).symm (biproduct.isBilimit G)
  let ePair : (⨁ F) ≅ X ⊞ Y := eIndexSum ≪≫ biprod.uniqueUpToIso X Y hb
  obtain ⟨eX⟩ := (key _ (xConeHomologyMinusOneAsTensorLinearEquiv k)).2
  obtain ⟨eY⟩ := (key _ (xConeHomologyZeroAsTensorLinearEquiv k)).2
  have hcontra : Nonempty
      (DerivedCategory.Q.obj P ≅
        DerivedCategory.Q.obj (CochainComplex.DerivedChangeOfRings.splitXAxisComplex k)) := by
    let : PreservesBinaryBiproducts (U.mapDerivedCategory) :=
      preservesBinaryBiproducts_of_preservesBiproducts _
    refine ⟨eModel.symm ≪≫ (U.mapDerivedCategory).mapIso eSplit ≪≫
      (U.mapDerivedCategory).mapIso ePair ≪≫
      (U.mapDerivedCategory).mapBiprod X Y ≪≫
      biprod.mapIso eX eY ≪≫ twoTermBiproductToSplit k⟩
  let cmp := CochainComplex.DerivedChangeOfRings.derivedTensorModuleStructuresDiffer k
  rcases hcontra with ⟨hcontra⟩
  exact cmp.not_iso ⟨cmp.tensorRestrictedXAxisWithNodalRingIsoXMultiplication ≪≫
    hcontra ≪≫ cmp.tensorXAxisWithRestrictedNodalRingIsoSplit.symm⟩

/-- In general, derived base change of `A`-modules to `R'` does not factor
through the derived category of the ordinary tensor-product algebra. -/
@[stacks 08J3]
public theorem no_derived_base_change :
    ∃ (R : Type u), ∃ (hR : CommRing R),
      letI : CommRing R := hR
      ∃ (A : Type u), ∃ (hA : CommRing A),
        letI : CommRing A := hA
        ∃ (R' : Type u), ∃ (hR' : CommRing R'),
          letI : CommRing R' := hR'
          ∃ (f : R →+* A) (g : R →+* R'),
            letI : Algebra R A := f.toAlgebra
            letI : Algebra R R' := g.toAlgebra
            letI : Algebra R' (A ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
            ¬ ∃ (T : DerivedCategory (ModuleCat.{u} A) ⥤
                DerivedCategory (ModuleCat.{u} (A ⊗[R] R'))),
              ∀ (M : ModuleCat.{u} A),
                Nonempty
                  (((ModuleCat.restrictScalars
                      (algebraMap R' (A ⊗[R] R'))).mapDerivedCategory.obj
                        (T.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))) ≅
                    ((derivedExtensionScalarsGeneral.{u, u, u} g).functor.obj
                      ((ModuleCat.restrictScalars f).mapDerivedCategory.obj
                        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)))) :=
  by
  classical
  let k : Type u := ULift.{u} ℤ
  refine ⟨CochainComplex.DerivedChangeOfRings.PolynomialRing k, inferInstance,
    CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k, ?_,
    CochainComplex.DerivedChangeOfRings.NodalRing k, ?_, ?_, ?_, ?_⟩
  · exact Ideal.Quotient.commRing _
  · exact Ideal.Quotient.commRing _
  · exact Ideal.Quotient.mk _
  · exact CochainComplex.DerivedChangeOfRings.nodalRingMap k
  · intro hT
    rcases hT with ⟨T, hT⟩
    let A := CochainComplex.DerivedChangeOfRings.PolynomialXAxisModule k
    let S := CochainComplex.DerivedChangeOfRings.NodalRing k
    let B := A ⊗[CochainComplex.DerivedChangeOfRings.PolynomialRing k] S
    let : CommRing A := inferInstance
    let : CommRing S := inferInstance
    let : CommRing B := inferInstance
    let : Algebra (CochainComplex.DerivedChangeOfRings.PolynomialRing k) A :=
      (Ideal.Quotient.mk _).toAlgebra
    let : Algebra (CochainComplex.DerivedChangeOfRings.PolynomialRing k) S :=
      (CochainComplex.DerivedChangeOfRings.nodalRingMap k).toAlgebra
    let : Algebra S B := Algebra.TensorProduct.rightAlgebra
    obtain ⟨e⟩ := hT (ModuleCat.of A A)
    obtain ⟨e'⟩ := extensionScalars_xAxisModel k
    exact no_lift_xAxisModel k _ ⟨e ≪≫ e' ≪≫
      (CochainComplex.DerivedChangeOfRings.derivedTensorModuleStructuresDiffer
        k).tensorRestrictedXAxisWithNodalRingIsoXMultiplication⟩

end Stacks.Examples
