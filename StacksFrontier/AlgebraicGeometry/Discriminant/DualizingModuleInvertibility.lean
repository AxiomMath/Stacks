module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Projective.Invertible
public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.BaseChange
public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.FlatAlgebraBaseChange
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.PairingIndependence
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.QuasiFiniteGorenstein
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleComparison
public import StacksFrontier.AlgebraicGeometry.Discriminant.FlatOverBase
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleData0BVG
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap
public import StacksFrontier.AlgebraicGeometry.Pullback.AffineOpens
public import StacksFrontier.RingTheory.Flat.FlatAtPointCriteria
public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.RingTheory.Flat.SyzygyFreeLocus

/-!
# Invertibility of the relative dualizing module is a fibrewise condition

Let `A → B` be a quasi-finite flat homomorphism of Noetherian rings with relative dualizing
module `ω_{B/A} = Hom_A(B', A) ⊗_{B'} B` computed from a finite-open factorization
`A → B' → B`. This file proves that `ω_{B/A}` is an invertible `B`-module exactly when the
dualizing module `ω_{B ⊗_A κ(p) / κ(p)}` of every fibre is invertible over `B ⊗_A κ(p)`, and the
corresponding statement for a quasi-finite flat morphism `f : Y ⟶ X` of Noetherian schemes: the
relative dualizing module `ω_{Y/X}` is an invertible `𝒪_Y`-module exactly when the relative
dualizing module `ω_{Y_x/x}` of the scheme-theoretic fibre over `x` is invertible for every point
`x` of `X`.

## Main results

* `Stacks.Discriminant.dualizingModule_invertible_iff_fibers`: the relative dualizing module of
  a flat quasi-finite map of Noetherian rings is invertible if and only if the relative dualizing
  module of each of its residue-field fibres is invertible.
* `Stacks.Discriminant.relativeDualizingModuleData_isInvertible_iff_fibers`: the relative
  dualizing module of a quasi-finite flat morphism of Noetherian schemes is invertible if and
  only if the relative dualizing module of each of its fibres is invertible.
* `Stacks.Discriminant.relativeDualizingModule_isInvertible_iff_fibers`: the same for any
  relative dualizing modules of the morphism and of its fibres, given as chart data.
* `Stacks.Discriminant.module_invertible_of_fiberwise_invertible`: a finite module over the
  target which is flat over the base and whose every residue-field fibre is invertible is itself
  invertible.
* `Stacks.Discriminant.algEquivFiberSections`: the fibre ring `κ(p) ⊗_A B` of a chart of `f` is
  the ring of sections of the scheme-theoretic fibre `Y_x` over its affine open
  `f.fiberι x ⁻¹ᵁ V`.

## Implementation notes

Base change of the relative dualizing module along a residue field is an isomorphism because the
algebra is flat, by `Stacks.Discriminant.dualizingModule.baseChangeLinearMap_bijective`, so the
fibre condition is about `(B ⊗_A κ(p)) ⊗_B ω_{B/A}`. Invertibility of such a module is detected by
finite presentation, flatness and rank one at every point: flatness over the target is checked
after localizing at a maximal ideal, where the fibre of the base is a local ring and the local
criterion for flatness upgrades a free fibre to a free module; rank one at a point of the target
is read off from the invertible fibre through it, using that the rank at a stalk is insensitive
to base change. Flatness of the relative dualizing module over the base, which feeds the local
criterion, is `Stacks.Discriminant.dualizingModule_flat`, and its finiteness over the target is
`Stacks.Discriminant.dualizingModule_finite`.

Since the relative dualizing module is computed from a finite-open factorization, the fibre
condition is stated for every finite-open factorization of the fibre; the choice is immaterial by
`Stacks.Discriminant.dualizingModuleEquiv`. The fibre of `A → B` at a prime `p` is written
`κ(p) ⊗_A B`, which is `Ideal.Fiber`.

Invertibility of `ω_{Y/X}` is chartwise, by
`Stacks.Discriminant.isInvertible_iff_exists_chart_dualizingModule_invertible`, so the scheme
statement reduces to the algebraic one over a chart `Spec B = V ⊆ f⁻¹(U)`, `Spec A = U`: the
fibre over a point `x ∈ U` meets that chart in the chart `f⁻¹(V) ∩ Y_x` of the fibre morphism
over the whole of `Spec κ(x)`, and the square of section rings is cocartesian, so
`Γ(Y_x, f⁻¹(V)) = κ(x) ⊗_A B`. A relative dualizing module of a morphism is carried by
`Stacks.Discriminant.RelativeDualizingModuleData`, whose existence and uniqueness are Tag 0BVG;
the statement of record is about the constructed `Stacks.Discriminant.relativeDualizingModuleData`
of the morphism and of each of its fibres.

## References

* [Stacks Project, Tag 0DWK](https://stacks.math.columbia.edu/tag/0DWK)
* [Stacks Project, Tag 0BVF](https://stacks.math.columbia.edu/tag/0BVF)
* [Stacks Project, Tag 0BVG](https://stacks.math.columbia.edu/tag/0BVG)
-/

@[expose] public section

universe u v w z

namespace Stacks.Discriminant

open scoped TensorProduct

/-- A finitely presented module which is free at every point of the spectrum and has rank one
there is invertible. -/
private theorem module_invertible_of_freeLocus_eq_univ_of_rank_one
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M]
    (hfree : Module.freeLocus R M = Set.univ)
    (hrank : Module.rankAtStalk (R := R) M = Function.const (PrimeSpectrum R) 1) :
    Module.Invertible R M := by
  have : Module.Projective R M := (Module.freeLocus_eq_univ_iff (R := R) (M := M)).mp hfree
  exact (Module.finite_projective_rankAtStalk_one_tfae_invertible_exists_tensor_inverse.{
      u, v, max u v}
      R M).1.out 1 2 |>.mp
    (show Module.Finite R M ∧ Module.Projective R M ∧
        Module.rankAtStalk (R := R) M = Function.const (PrimeSpectrum R) 1 from
      ⟨inferInstance, inferInstance, hrank⟩)

/-- A finitely presented flat module of constant rank one is invertible. -/
private theorem module_invertible_of_finitePresentation_flat_of_rank_one
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat R M]
    (hrank : Module.rankAtStalk (R := R) M = Function.const (PrimeSpectrum R) 1) :
    Module.Invertible R M := by
  have : Module.Projective R M := Module.Flat.projective_of_finitePresentation
  exact module_invertible_of_freeLocus_eq_univ_of_rank_one
    ((Module.freeLocus_eq_univ_iff (R := R) (M := M)).mpr inferInstance) hrank

/-- If every residue-field fibre of a finite flat module over the target is invertible, then the
module has rank one at every point of the target. -/
private theorem module_rankAtStalk_eq_one_of_fiberwise_invertible
    {A : Type u} {B : Type v} {M : Type w}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] [Module.Flat B M]
    (hfiber : ∀ (p : PrimeSpectrum A),
      letI : Algebra p.asIdeal.ResidueField (p.asIdeal.Fiber B) :=
        Algebra.TensorProduct.leftAlgebra
      letI : Algebra B (p.asIdeal.Fiber B) := Algebra.TensorProduct.rightAlgebra
      Module.Invertible (p.asIdeal.Fiber B) ((p.asIdeal.Fiber B) ⊗[B] M)) :
    Module.rankAtStalk (R := B) M = Function.const (PrimeSpectrum B) 1 := by
  funext q
  let p : PrimeSpectrum A := q.comap (algebraMap A B)
  let : Algebra p.asIdeal.ResidueField (p.asIdeal.Fiber B) :=
    Algebra.TensorProduct.leftAlgebra
  let : Algebra B (p.asIdeal.Fiber B) := Algebra.TensorProduct.rightAlgebra
  let qf : PrimeSpectrum (p.asIdeal.Fiber B) :=
    PrimeSpectrum.preimageEquivFiber A B p ⟨q, rfl⟩
  have hqf : qf.comap (algebraMap B (p.asIdeal.Fiber B)) = q := by
    change qf.comap Algebra.TensorProduct.includeRight.toRingHom = q
    have h := congrArg Subtype.val
      ((PrimeSpectrum.preimageEquivFiber A B p).left_inv ⟨q, rfl⟩)
    simpa [qf, PrimeSpectrum.preimageEquivFiber] using h
  have hrank :=
    (Module.finite_projective_rankAtStalk_one_tfae_invertible_exists_tensor_inverse.{
      max u v, max (max u v) w, max (max u v) (max (max u v) w)}
      (p.asIdeal.Fiber B) ((p.asIdeal.Fiber B) ⊗[B] M)).1.out 2 1 |>.mp (hfiber p)
  have hbase :
      Module.rankAtStalk (R := p.asIdeal.Fiber B)
          ((p.asIdeal.Fiber B) ⊗[B] M) qf = Module.rankAtStalk (R := B) M q := by
    rw [Module.rankAtStalk_baseChange]
    simp [hqf]
  have hfiberRank :
      Module.rankAtStalk (R := p.asIdeal.Fiber B)
          ((p.asIdeal.Fiber B) ⊗[B] M) qf = 1 := by
    simpa only [Function.const_apply] using congrFun hrank.2.2 qf
  change Module.rankAtStalk (R := B) M q = 1
  exact hbase.symm.trans hfiberRank

/-- Invertibility of a base change is inherited by any further base change along a tower. -/
private theorem invertible_tensor_tower
    {R S T M : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [AddCommGroup M] [Module R M]
    [Module.Invertible S (S ⊗[R] M)] : Module.Invertible T (T ⊗[R] M) :=
  Module.Invertible.congr (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M)

/-- Invertibility is preserved and reflected by a linear equivalence. -/
private theorem invertible_iff_of_linearEquiv {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (e : M ≃ₗ[R] N) :
    Module.Invertible R M ↔ Module.Invertible R N :=
  ⟨fun _ => Module.Invertible.congr e, fun _ => Module.Invertible.congr e.symm⟩

/-- The relative dualizing module of the base change of a flat quasi-finite algebra is invertible
exactly when the base change of the relative dualizing module is. -/
private theorem invertible_dualizingModule_baseChange_iff
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) (K : Type*) [CommRing K] [Algebra A K] :
    letI : Algebra B (K ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    Module.Invertible (K ⊗[A] B) (dualizingModule (FiniteOpenFactorization.baseChange F K)) ↔
      Module.Invertible (K ⊗[A] B) ((K ⊗[A] B) ⊗[B] dualizingModule F) := by
  let : Algebra B (K ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let : Module B (dualizingModule (FiniteOpenFactorization.baseChange F K)) :=
    Module.compHom _ (algebraMap B (K ⊗[A] B))
  let : IsScalarTower B (K ⊗[A] B) (dualizingModule (FiniteOpenFactorization.baseChange F K)) :=
    IsScalarTower.of_compHom B (K ⊗[A] B) _
  exact (invertible_iff_of_linearEquiv (LinearEquiv.ofBijective
    (dualizingModule.baseChangeLinearMap F K)
    (dualizingModule.baseChangeLinearMap_bijective F K))).symm

/-- A finite module over the target which is flat over the base and has invertible residue-field
fibres becomes free after localizing the target at any prime. -/
private theorem free_localized_of_flat_of_fiberwise_invertible
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] [Module.Flat A M]
    (hfiber : ∀ p : PrimeSpectrum A,
      letI : Algebra B (p.asIdeal.Fiber B) := Algebra.TensorProduct.rightAlgebra
      Module.Invertible (p.asIdeal.Fiber B) ((p.asIdeal.Fiber B) ⊗[B] M))
    (q : Ideal B) [q.IsPrime] :
    Module.Free (Localization.AtPrime q) (LocalizedModule.AtPrime q M) := by
  let p := q.under A
  let S := Localization.AtPrime q
  let N := LocalizedModule.AtPrime q M
  let J := p.map (algebraMap A S)
  let T := S ⧸ J
  let : Algebra (Localization.AtPrime p) S := Ideal.algebraLocalizationAtPrimeUnder q
  let : IsScalarTower A (Localization.AtPrime p) S :=
    Ideal.isScalarTower_localizationAtPrimeUnder q
  let : IsLocalHom (algebraMap (Localization.AtPrime p) S) :=
    Ideal.isLocalHom_algebraMap_localizationAtPrimeUnder q
  let : Module (Localization.AtPrime p) N :=
    Module.compHom N (algebraMap (Localization.AtPrime p) S)
  let : IsScalarTower (Localization.AtPrime p) S N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower A (Localization.AtPrime p) N :=
    IsScalarTower.of_algebraMap_smul fun a n => by
      change algebraMap (Localization.AtPrime p) S
        (algebraMap A (Localization.AtPrime p) a) • n = a • n
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_smul]
  have : Module.Flat A N := Module.Flat.of_isLocalizedModule_of_tower q.primeCompl
    (LocalizedModule.mkLinearMap q.primeCompl M)
  have : Module.Flat (Localization.AtPrime p) N :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl N).mpr
      inferInstance
  have hker : p ≤ RingHom.ker (algebraMap A T) := by
    intro a ha
    change algebraMap A T a = 0
    rw [← Ideal.Quotient.mk_algebraMap A J, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  have hunits : p.primeCompl ≤ Submonoid.comap (algebraMap A T) (IsUnit.submonoid T) := by
    intro a ha
    change IsUnit (algebraMap A T a)
    rw [IsScalarTower.algebraMap_apply A S T, IsScalarTower.algebraMap_apply A B S]
    exact (IsLocalization.map_units (M := q.primeCompl) S ⟨algebraMap A B a, ha⟩).map _
  let φ := Ideal.ResidueField.lift p (algebraMap A T) hker hunits
  let : Algebra p.ResidueField T := φ.toAlgebra
  let : IsScalarTower A p.ResidueField T :=
    IsScalarTower.of_algebraMap_eq fun a => (Ideal.ResidueField.lift_algebraMap _ _ _ _ a).symm
  let : Algebra B (p.Fiber B) := Algebra.TensorProduct.rightAlgebra
  let ψ : p.Fiber B →ₐ[A] T := Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom A p.ResidueField T) (IsScalarTower.toAlgHom A B T)
    (fun _ _ => Commute.all _ _)
  let : Algebra (p.Fiber B) T := ψ.toRingHom.toAlgebra
  have : IsScalarTower B (p.Fiber B) T :=
    IsScalarTower.of_algebraMap_eq fun b => by
      change algebraMap B T b = ψ (1 ⊗ₜ[A] b)
      simp [ψ]
  have : Module.Invertible (p.Fiber B) ((p.Fiber B) ⊗[B] M) := hfiber ⟨p, inferInstance⟩
  have : Module.Invertible T (T ⊗[B] M) := invertible_tensor_tower (S := p.Fiber B)
  let e : (T ⊗[S] N) ≃ₗ[T] (T ⊗[B] M) :=
    (LinearEquiv.baseChange S T _ _
        (LocalizedModule.isBaseChange q.primeCompl M).equiv.symm).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange B S T T M)
  have : Module.Invertible T (T ⊗[S] N) := Module.Invertible.congr e.symm
  have : Module.Projective T (T ⊗[S] N) := inferInstance
  have : Module.Flat T (T ⊗[S] N) := Module.Flat.of_projective
  have : IsLocalRing T := (Ideal.localizationFiberPointRingEquiv A q).isLocalRing
  have : Module.Free T (T ⊗[S] N) := Module.free_of_flat_of_isLocalRing
  rcases subsingleton_or_nontrivial N with _ | _
  · exact Module.Free.of_subsingleton _ _
  refine (Module.Flat.free_and_flat_of_free_maximalIdeal
    (R := Localization.AtPrime p) ?_).1
  rw [Ideal.map_maximalIdeal_eq_map_under q]
  exact Module.Free.of_equiv (LinearEquiv.extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective (TensorProduct.quotTensorEquivQuotSMul N J))

/-- A finite module over the target of a map of Noetherian rings which is flat over the base is
invertible as soon as all of its residue-field fibres are invertible. -/
theorem module_invertible_of_fiberwise_invertible
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] [Module.Flat A M]
    (hfiber : ∀ p : PrimeSpectrum A,
      letI : Algebra B (p.asIdeal.Fiber B) := Algebra.TensorProduct.rightAlgebra
      Module.Invertible (p.asIdeal.Fiber B) ((p.asIdeal.Fiber B) ⊗[B] M)) :
    Module.Invertible B M := by
  have : Module.FinitePresentation B M := Module.finitePresentation_of_finite B M
  have : Module.Flat B M := by
    apply Module.flat_of_localized_maximal
    intro q hq
    have := free_localized_of_flat_of_fiberwise_invertible hfiber q
    have : Module.Flat (Localization.AtPrime q) (LocalizedModule.AtPrime q M) :=
      Module.Flat.of_free
    exact Module.Flat.trans B (Localization.AtPrime q) _
  exact module_invertible_of_finitePresentation_flat_of_rank_one
    (module_rankAtStalk_eq_one_of_fiberwise_invertible hfiber)

/-- **Stacks Project, Tag 0DWK**, part (1). For a quasi-finite flat homomorphism of Noetherian
rings, the relative dualizing module is invertible over the target if and only if the relative
dualizing module of the fibre `B ⊗_A κ(p)` over `κ(p)` is invertible for every prime `p` of the
base. -/
@[stacks 0DWK "part (1)"]
theorem dualizingModule_invertible_iff_fibers
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra.FiniteType A B] [Algebra.QuasiFinite A B]
    [Module.Flat A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    Module.Invertible B (dualizingModule F) ↔
      ∀ (p : PrimeSpectrum A),
        letI : Algebra p.asIdeal.ResidueField (p.asIdeal.Fiber B) :=
          Algebra.TensorProduct.leftAlgebra
        ∀ (G : FiniteOpenFactorization.{u, max u v, max u w}
            p.asIdeal.ResidueField (p.asIdeal.Fiber B)),
          Module.Invertible (p.asIdeal.Fiber B) (dualizingModule G) := by
  constructor
  · intro h p
    let : Algebra p.asIdeal.ResidueField (p.asIdeal.Fiber B) :=
      Algebra.TensorProduct.leftAlgebra
    intro G
    let H := FiniteOpenFactorization.baseChange F p.asIdeal.ResidueField
    have : Module.Invertible (p.asIdeal.Fiber B) (dualizingModule H) :=
      (invertible_dualizingModule_baseChange_iff F p.asIdeal.ResidueField).mpr
        (by let : Algebra B (p.asIdeal.Fiber B) := Algebra.TensorProduct.rightAlgebra
            infer_instance)
    exact Module.Invertible.congr (dualizingModuleEquiv H G)
  · intro h
    let M := dualizingModule F
    let : Module A M := Module.compHom M (algebraMap A B)
    have : IsScalarTower A B M := IsScalarTower.of_compHom A B M
    have : Module.Finite B M := dualizingModule_finite F
    have : Module.Flat A M := dualizingModule_flat F
    have hfiber (p : PrimeSpectrum A) :
        let : Algebra B (p.asIdeal.Fiber B) := Algebra.TensorProduct.rightAlgebra
        Module.Invertible (p.asIdeal.Fiber B) ((p.asIdeal.Fiber B) ⊗[B] M) := by
      let : Algebra p.asIdeal.ResidueField (p.asIdeal.Fiber B) :=
        Algebra.TensorProduct.leftAlgebra
      let : Algebra B (p.asIdeal.Fiber B) := Algebra.TensorProduct.rightAlgebra
      exact (invertible_dualizingModule_baseChange_iff F p.asIdeal.ResidueField).mp
        (h p (FiniteOpenFactorization.baseChange F p.asIdeal.ResidueField))
    exact module_invertible_of_fiberwise_invertible hfiber

section Schemes

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped _root_.AlgebraicGeometry

noncomputable section

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-! ### Invertibility along a semilinear equivalence -/

/-- A semilinear equivalence over a ring isomorphism carries an invertible module to an
invertible module. -/
private theorem invertible_of_semilinearEquiv
    {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (σ : R ≃+* S) (e : M ≃ₛₗ[(σ : R →+* S)] N) [Module.Invertible R M] :
    Module.Invertible S N := by
  let : Algebra R S := σ.toRingHom.toAlgebra
  let : Module R N := Module.compHom N σ.toRingHom
  let : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  let e' : M ≃ₗ[R] N :=
    { e.toAddEquiv with map_smul' := fun r m => e.map_smul' r m }
  have : IsLocalization (⊥ : Submonoid R) S :=
    IsLocalization.of_le_isUnit_of_bijective (by
      rintro _ ⟨x, hx, rfl⟩
      have hx : x = 1 := hx
      simp [hx]) σ.bijective
  have : IsLocalizedModule (⊥ : Submonoid R) e'.toLinearMap :=
    { map_units := by intro x; have hx : x.val = 1 := x.property; simp [hx]
      surj := fun y => ⟨(e'.symm y, 1), by simp⟩
      exists_of_eq := fun h => ⟨1, by simpa using e'.injective h⟩ }
  exact Module.Invertible.of_isLocalization (⊥ : Submonoid R) e'.toLinearMap

/-- Invertibility is read off either side of a semilinear equivalence. -/
private theorem invertible_iff_semilinearEquiv
    {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (σ : R ≃+* S) (e : M ≃ₛₗ[(σ : R →+* S)] N) :
    Module.Invertible R M ↔ Module.Invertible S N :=
  ⟨fun _ => invertible_of_semilinearEquiv σ e,
    fun _ => invertible_of_semilinearEquiv σ.symm e.symm⟩

/-- An isomorphism `S ≃ T` of `R`-algebras induces a semilinear isomorphism of the base changes
of an `R`-module along the two. -/
private def tensorSemilinearEquivOfAlgEquiv
    {R S T M : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [AddCommGroup M] [Module R M]
    (e : S ≃ₐ[R] T) :
    (S ⊗[R] M) ≃ₛₗ[(e.toRingEquiv : S →+* T)] (T ⊗[R] M) := by
  let eT := TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M)
  refine { eT.toAddEquiv with map_smul' := ?_ }
  intro s m
  induction m using TensorProduct.inductionOn with
  | tmul t m => simp [eT, TensorProduct.smul_tmul', map_mul]
  | add x y hx hy =>
      change eT (s • (x + y)) = e s • eT (x + y)
      simp only [smul_add, map_add]
      exact congrArg₂ (· + ·) hx hy

/-! ### Moving a finite-open factorization along an isomorphism of the target -/

/-- Composing with a ring isomorphism of the target does not disturb the away localizations. -/
private theorem awayMap_bijective_of_ringEquiv
    {C B B' : Type*} [CommRing C] [CommRing B] [CommRing B']
    (φ : C →+* B) (e : B ≃+* B') (g : C)
    (h : Function.Bijective (Localization.awayMap φ g)) :
    Function.Bijective (Localization.awayMap (e.toRingHom.comp φ) g) := by
  let eL := IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (φ g)) (T := Submonoid.powers (e (φ g)))
    (Localization.Away (φ g))
    (Localization.Away (e (φ g))) e (by simp)
  have h1 : ∀ x : C, Localization.awayMap φ g (algebraMap C (Localization.Away g) x) =
      algebraMap B (Localization.Away (φ g)) (φ x) :=
    fun x => RingHom.congr_fun (awayMap_comp_algebraMap φ g) x
  have h2 : ∀ x : C, Localization.awayMap (e.toRingHom.comp φ) g
      (algebraMap C (Localization.Away g) x) =
      algebraMap B' (Localization.Away ((e.toRingHom.comp φ) g)) (e (φ x)) :=
    fun x => RingHom.congr_fun (awayMap_comp_algebraMap (e.toRingHom.comp φ) g) x
  have he : eL.toRingHom.comp (Localization.awayMap φ g) =
      Localization.awayMap (e.toRingHom.comp φ) g := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    apply RingHom.ext
    intro x
    change eL (Localization.awayMap φ g (algebraMap C (Localization.Away g) x)) =
      Localization.awayMap (e.toRingHom.comp φ) g (algebraMap C (Localization.Away g) x)
    rw [h1, h2]
    simp only [eL, IsLocalization.ringEquivOfRingEquiv_eq]
    rfl
  rw [← he]
  exact eL.bijective.comp h

/-- The finite-open factorization obtained from `F` by transporting its target along an
isomorphism of algebras; the intermediate ring is unchanged. -/
private def factorizationMapTarget
    {A : Type u} {B : Type v} {B' : Type z}
    [CommRing A] [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B']
    (F : FiniteOpenFactorization.{u, v, w} A B) (e : B ≃ₐ[A] B') :
    FiniteOpenFactorization.{u, z, w} A B' := by
  letI : Algebra F.middle B' := (e.toRingHom.comp (algebraMap F.middle B)).toAlgebra
  have ht : IsScalarTower A F.middle B' :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap A B' a = e (algebraMap F.middle B (algebraMap A F.middle a))
      rw [← IsScalarTower.algebraMap_apply, e.commutes]
  have hc : PrimeSpectrum.comap (algebraMap F.middle B') =
      PrimeSpectrum.comap (algebraMap F.middle B) ∘ PrimeSpectrum.comap e.toRingHom :=
    PrimeSpectrum.comap_comp _ _
  have hr : Set.range (PrimeSpectrum.comap (algebraMap F.middle B')) =
      Set.range (PrimeSpectrum.comap (algebraMap F.middle B)) := by
    rw [hc, Set.range_comp,
      (PrimeSpectrum.isHomeomorph_comap_of_bijective e.bijective).surjective.range_eq]
    simp
  exact {
    middle := F.middle
    commRingMiddle := inferInstance
    algebraMiddle := inferInstance
    algebraTarget := inferInstance
    scalarTower := ht
    finite_middle := inferInstance
    isOpenEmbedding_comap := by
      rw [hc]
      exact F.isOpenEmbedding_comap.comp
        (PrimeSpectrum.isHomeomorph_comap_of_bijective e.bijective).isOpenEmbedding
    awayMap_bijective := fun g hg =>
      awayMap_bijective_of_ringEquiv (algebraMap F.middle B) e.toRingEquiv g
        (F.awayMap_bijective g (by rwa [← hr])) }

/-- Transporting the target of a finite-open factorization along an isomorphism of algebras
transports its relative dualizing module semilinearly. -/
private def dualizingModuleMapTargetEquiv
    {A : Type u} {B : Type v} {B' : Type z}
    [CommRing A] [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B']
    (F : FiniteOpenFactorization.{u, v, w} A B) (e : B ≃ₐ[A] B') :
    dualizingModule F ≃ₛₗ[(e.toRingEquiv : B →+* B')]
      dualizingModule (factorizationMapTarget F e) := by
  letI : Algebra F.middle B' := (e.toRingHom.comp (algebraMap F.middle B)).toAlgebra
  letI := algebraDualModule A F.middle
  let eB : B ≃ₐ[F.middle] B' := { e.toRingEquiv with commutes' := fun _ => rfl }
  let eT : Module.Dual A F.middle ⊗[F.middle] B ≃ₗ[F.middle]
      Module.Dual A F.middle ⊗[F.middle] B' :=
    TensorProduct.congr (LinearEquiv.refl F.middle (Module.Dual A F.middle)) eB.toLinearEquiv
  let eD : dualizingModule F ≃+ dualizingModule (factorizationMapTarget F e) := eT.toAddEquiv
  have hmap : ∀ (φ : Module.Dual A F.middle) (x : B),
      eD (dualizingModule.tmul F φ x) =
        dualizingModule.tmul (factorizationMapTarget F e) φ (e x) := fun _ _ => rfl
  refine { eD with map_smul' := ?_ }
  intro b m
  induction m using dualizingModule.induction_on with
  | tmul d x =>
      change eD (b • dualizingModule.tmul F d x) = e b • eD (dualizingModule.tmul F d x)
      rw [dualizingModule.smul_tmul, hmap, hmap]
      exact (congrArg (dualizingModule.tmul (factorizationMapTarget F e) d)
          (map_mul e b x)).trans
        (dualizingModule.smul_tmul (factorizationMapTarget F e) (e b) (e x) d).symm
  | add x y hx hy =>
      have hx' : eD (b • x) = e b • eD x := hx
      have hy' : eD (b • y) = e b • eD y := hy
      change eD (b • (x + y)) = e b • eD (x + y)
      rw [smul_add, map_add, map_add, hx', hy', smul_add]

/-! ### The relative dualizing module of a cocartesian chart -/

/-- **Formation of the relative dualizing module commutes with a cocartesian change of chart.**
If `T` is the pushout of `A → B` along `A → K` and `A → B` is flat and quasi-finite over a
Noetherian base, then the relative dualizing module of `K → T` is invertible exactly when the
base change to `T` of the relative dualizing module of `A → B` is. -/
private theorem dualizingModule_invertible_iff_baseChange_of_isPushout
    {A B K T : Type u} [CommRing A] [CommRing B] [CommRing K] [CommRing T]
    [Algebra A B] [Algebra A K] [Algebra B T] [Algebra K T] [Algebra A T]
    [IsScalarTower A K T] [IsScalarTower A B T] [Algebra.IsPushout A K B T]
    [IsNoetherianRing A] [IsNoetherianRing K] [IsNoetherianRing T] [Module.Flat A B]
    (F : FiniteOpenFactorization.{u, u, u} A B)
    (G : FiniteOpenFactorization.{u, u, u} K T) :
    Module.Invertible T (dualizingModule G) ↔
      Module.Invertible T (T ⊗[B] dualizingModule F) := by
  let : Algebra B (K ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let e := Algebra.IsPushout.equiv A K B T
  let eB : K ⊗[A] B ≃ₐ[B] T :=
    { e.toRingEquiv with
      commutes' := fun b => by
        change e (1 ⊗ₜ[A] b) = _
        simp [e, Algebra.IsPushout.equiv_tmul] }
  let H := FiniteOpenFactorization.baseChange F K
  let J := factorizationMapTarget H e
  rw [invertible_iff_of_linearEquiv (dualizingModuleEquiv G J),
    ← invertible_iff_semilinearEquiv e.toRingEquiv (dualizingModuleMapTargetEquiv H e)]
  exact (invertible_dualizingModule_baseChange_iff F K).trans
    (invertible_iff_semilinearEquiv eB.toRingEquiv (tensorSemilinearEquivOfAlgEquiv eB))

/-! ### The residue field of a point of an affine chart -/

/-- The residue field of a prime of the coordinate ring of an affine chart, compared with the
global sections of the spectrum of the residue field of the corresponding point. -/
def affineResidueFieldIso {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (p : Spec Γ(X, U)) [p.asIdeal.IsPrime] :
    CommRingCat.of p.asIdeal.ResidueField ≅
      Γ(Spec (X.residueField (hU.fromSpec p)), ⊤) :=
  haveI : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  haveI : IsIso (hU.fromSpec.residueFieldMap p) :=
    isIso_residueFieldMap_of_isPreimmersion hU.fromSpec p
  (Scheme.Spec.residueFieldIso Γ(X, U) p).symm ≪≫
    (asIso (hU.fromSpec.residueFieldMap p)).symm ≪≫
      (Scheme.ΓSpecIso (X.residueField (hU.fromSpec p))).symm

/-- The comparison of residue fields of an affine chart is a map of algebras over the
coordinate ring of the chart. -/
theorem affineResidueFieldIso_comp {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (p : Spec Γ(X, U)) [p.asIdeal.IsPrime]
    (hp : (⊤ : (Spec (X.residueField (hU.fromSpec p))).Opens) ≤
      X.fromSpecResidueField (hU.fromSpec p) ⁻¹ᵁ U) :
    CommRingCat.ofHom (algebraMap Γ(X, U) p.asIdeal.ResidueField) ≫
      (affineResidueFieldIso hU p).hom =
      (X.fromSpecResidueField (hU.fromSpec p)).appLE U ⊤ hp := by
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have : IsIso (hU.fromSpec.residueFieldMap p) :=
    isIso_residueFieldMap_of_isPreimmersion hU.fromSpec p
  apply Spec.map_injective
  apply (cancel_mono hU.fromSpec).mp
  rw [IsAffineOpen.SpecMap_appLE_fromSpec _ hU (isAffineOpen_top _) hp]
  dsimp only [affineResidueFieldIso, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  simp only [Spec.map_comp, Category.assoc]
  rw [← Category.assoc (Spec.map (Scheme.Spec.residueFieldIso Γ(X, U) p).inv),
    Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  simp only [← Spec.map_comp_assoc, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  rw [IsAffineOpen.fromSpec_top]
  congr 1
  exact (Scheme.isoSpec_Spec_inv _).symm

/-! ### The scheme version -/

section Fibres

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
  [IsNoetherian X] [IsNoetherian Y]
  [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] [Flat f]

/-- The whole spectrum of a residue field maps into any open containing the point. -/
private theorem top_le_preimage_fromSpecResidueField {X : Scheme.{u}} {U : X.Opens} {x : X}
    (hx : x ∈ U) : (⊤ : (Spec (X.residueField x)).Opens) ≤ X.fromSpecResidueField x ⁻¹ᵁ U := by
  intro q _
  change X.fromSpecResidueField x q ∈ U
  rwa [Scheme.fromSpecResidueField_apply]

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] [LocallyOfFiniteType f]
  [QuasiCompact f] [LocallyQuasiFinite f] [Flat f] in
/-- The chart of the fibre over `x` cut out by an affine chart `V` of the source is affine. -/
theorem isAffineOpen_fiber_preimage
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (x : X) (hx : x ∈ U.1) : IsAffineOpen (f.fiberι x ⁻¹ᵁ V.1) := by
  have hWeq : f.fiberι x ⁻¹ᵁ V.1 = f.fiberι x ⁻¹ᵁ V.1 ⊓
      f.fiberToSpecResidueField x ⁻¹ᵁ (⊤ : (Spec (X.residueField x)).Opens) := by simp
  exact IsAffineOpen.inf_preimage_of_isPullback
    (IsPullback.of_hasPullback f (X.fromSpecResidueField x)) U.2 V.2 hVU
    (isAffineOpen_top _) (top_le_preimage_fromSpecResidueField hx) hWeq

/-- **Every fibre of a morphism with invertible relative dualizing module has invertible
relative dualizing module.** -/
private theorem fiber_isInvertible_of_isInvertible
    (D : RelativeDualizingModuleData f)
    (hD : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property D.sheaf)
    (x : X) (E : RelativeDualizingModuleData (f.fiberToSpecResidueField x)) :
    Stacks.SheafOfModules.IsInvertible (f.fiber x).presheaf
      (structureSheafRing (f.fiber x).toRingedSpace).property E.sheaf := by
  refine (isInvertible_iff_exists_chart_dualizingModule_invertible E).mpr fun z => ?_
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (⊤ : X.Opens) from trivial) (⊤ : X.Opens).isOpen
  have hzU : f.fiberι x z ∈ f ⁻¹ᵁ U := by
    change f (f.fiberι x z) ∈ U
    have hz := (f.fiberHomeo x z).property
    change f (f.fiberι x z) = x at hz
    rwa [hz]
  obtain ⟨-, ⟨V, hV, rfl⟩, hzV, hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    hzU (f ⁻¹ᵁ U).isOpen
  have hUa : IsAffineOpen U := hU
  have hVa : IsAffineOpen V := hV
  let Ua : X.affineOpens := ⟨U, hUa⟩
  let Va : Y.affineOpens := ⟨V, hVa⟩
  let K : (Spec (X.residueField x)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let W : (f.fiber x).affineOpens :=
    ⟨f.fiberι x ⁻¹ᵁ V, isAffineOpen_fiber_preimage f Ua Va hVU x hxU⟩
  have hKU : K.1 ≤ X.fromSpecResidueField x ⁻¹ᵁ U := top_le_preimage_fromSpecResidueField hxU
  have hWK : W.1 ≤ f.fiberToSpecResidueField x ⁻¹ᵁ K.1 := by simp [K]
  have hWV : W.1 ≤ f.fiberι x ⁻¹ᵁ V := le_rfl
  refine ⟨K, W, hWK, hzV, fun G => ?_⟩
  let a := f.appLE U V hVU
  let b := (X.fromSpecResidueField x).appLE U K hKU
  let c := (f.fiberι x).appLE V W hWV
  let d := (f.fiberToSpecResidueField x).appLE K W hWK
  have hWeq : W.1 = f.fiberι x ⁻¹ᵁ V ⊓ f.fiberToSpecResidueField x ⁻¹ᵁ K.1 := by
    simp [W, K]
  have hpush : IsPushout a b c d := isPushout_appLE_of_isPullback
    (IsPullback.of_hasPullback f (X.fromSpecResidueField x)) hU hV hVU
    (isAffineOpen_top _) hKU hWeq
  let : Algebra Γ(X, U) Γ(Y, V) := a.hom.toAlgebra
  let : Algebra Γ(X, U) Γ(Spec (X.residueField x), K.1) := b.hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(f.fiber x, W.1) := c.hom.toAlgebra
  let : Algebra Γ(Spec (X.residueField x), K.1) Γ(f.fiber x, W.1) := d.hom.toAlgebra
  let : Algebra Γ(X, U) Γ(f.fiber x, W.1) := (c.hom.comp a.hom).toAlgebra
  have : IsScalarTower Γ(X, U) Γ(Y, V) Γ(f.fiber x, W.1) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X, U) Γ(Spec (X.residueField x), K.1) Γ(f.fiber x, W.1) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hpush.w)
  have : Algebra.IsPushout Γ(X, U) Γ(Spec (X.residueField x), K.1) Γ(Y, V)
      Γ(f.fiber x, W.1) := CommRingCat.isPushout_iff_isPushout.mp hpush.flip
  have := IsLocallyNoetherian.component_noetherian Ua
  have := IsLocallyNoetherian.component_noetherian Va
  have := IsLocallyNoetherian.component_noetherian K
  have := IsLocallyNoetherian.component_noetherian W
  have : Module.Flat Γ(X, U) Γ(Y, V) := f.flat_appLE hU hV hVU
  obtain ⟨F⟩ := nonempty_relativeDualizingChartFactorization f Ua Va hVU
  have : Module.Invertible Γ(Y, V) (dualizingModule F) :=
    module_invertible_dualizingModule D Ua Va hVU F
  exact (dualizingModule_invertible_iff_baseChange_of_isPushout F G).mpr inferInstance

/-- **The fibre of a chart is a chart of the fibre.** For affine opens `U = Spec A ⊆ X` and
`V = Spec B ⊆ Y` with `f(V) ⊆ U`, and a prime `p` of `A` with corresponding point `x` of `U`,
the fibre ring `κ(p) ⊗_A B` is the ring of sections of the scheme-theoretic fibre `Y_x` over its
affine open `f.fiberι x ⁻¹ᵁ V`. -/
@[ega "IV 2.2.1" "special case"]
noncomputable def algEquivFiberSections (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (p : PrimeSpectrum Γ(X, U.1)) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    letI : Algebra Γ(Y, V.1) (p.asIdeal.Fiber Γ(Y, V.1)) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra Γ(Y, V.1)
        Γ(f.fiber (U.2.fromSpec p), f.fiberι (U.2.fromSpec p) ⁻¹ᵁ V.1) :=
      ((f.fiberι (U.2.fromSpec p)).appLE V.1
        (f.fiberι (U.2.fromSpec p) ⁻¹ᵁ V.1) le_rfl).hom.toAlgebra
    p.asIdeal.Fiber Γ(Y, V.1) ≃ₐ[Γ(Y, V.1)]
      Γ(f.fiber (U.2.fromSpec p), f.fiberι (U.2.fromSpec p) ⁻¹ᵁ V.1) := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  set x := U.2.fromSpec p
  have hxU : x ∈ U.1 := U.2.range_fromSpec.le ⟨p, rfl⟩
  let K : (Spec (X.residueField x)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let W : (f.fiber x).affineOpens :=
    ⟨f.fiberι x ⁻¹ᵁ V.1, isAffineOpen_fiber_preimage f U V hVU x hxU⟩
  have hKU : K.1 ≤ X.fromSpecResidueField x ⁻¹ᵁ U.1 := by
    intro q _
    change X.fromSpecResidueField x q ∈ U.1
    rwa [Scheme.fromSpecResidueField_apply]
  have hWK : W.1 ≤ f.fiberToSpecResidueField x ⁻¹ᵁ K.1 := by simp [K]
  have hWV : W.1 ≤ f.fiberι x ⁻¹ᵁ V.1 := le_rfl
  let a := f.appLE U.1 V.1 hVU
  let b := (X.fromSpecResidueField x).appLE U.1 K.1 hKU
  let c := (f.fiberι x).appLE V.1 W.1 hWV
  let d := (f.fiberToSpecResidueField x).appLE K.1 W.1 hWK
  have hWeq : W.1 = f.fiberι x ⁻¹ᵁ V.1 ⊓ f.fiberToSpecResidueField x ⁻¹ᵁ K.1 := by
    simp [W, K]
  have hpush : IsPushout a b c d := isPushout_appLE_of_isPullback
    (IsPullback.of_hasPullback f (X.fromSpecResidueField x)) U.2 V.2 hVU
    (isAffineOpen_top _) hKU hWeq
  let : Algebra Γ(X, U.1) Γ(Spec (X.residueField x), K.1) := b.hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(f.fiber x, W.1) := c.hom.toAlgebra
  let : Algebra Γ(Spec (X.residueField x), K.1) Γ(f.fiber x, W.1) := d.hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(f.fiber x, W.1) := (c.hom.comp a.hom).toAlgebra
  have : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(f.fiber x, W.1) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X, U.1) Γ(Spec (X.residueField x), K.1) Γ(f.fiber x, W.1) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hpush.w)
  have : Algebra.IsPushout Γ(X, U.1) Γ(Spec (X.residueField x), K.1) Γ(Y, V.1)
      Γ(f.fiber x, W.1) := CommRingCat.isPushout_iff_isPushout.mp hpush.flip
  let eK : p.asIdeal.ResidueField ≃ₐ[Γ(X, U.1)] Γ(Spec (X.residueField x), K.1) :=
    { (affineResidueFieldIso U.2 p).commRingCatIsoToRingEquiv with
      commutes' := fun r => congrArg (fun φ : Γ(X, U.1) ⟶
        Γ(Spec (X.residueField x), K.1) => φ r) (affineResidueFieldIso_comp U.2 p hKU) }
  let eT := (Algebra.TensorProduct.congr eK
    (AlgEquiv.refl (R := Γ(X, U.1)) (A₁ := Γ(Y, V.1)))).trans
    ((Algebra.IsPushout.equiv Γ(X, U.1) Γ(Spec (X.residueField x), K.1)
      Γ(Y, V.1) Γ(f.fiber x, W.1)).restrictScalars Γ(X, U.1))
  let : Algebra Γ(Y, V.1) (p.asIdeal.Fiber Γ(Y, V.1)) := Algebra.TensorProduct.rightAlgebra
  exact
    { eT.toRingEquiv with
      commutes' := fun r => by
        change eT (1 ⊗ₜ[Γ(X, U.1)] r) = _
        simp [eT, Algebra.TensorProduct.congr_apply, Algebra.IsPushout.equiv_tmul]
        rfl }

/-- **A morphism whose fibres all have invertible relative dualizing module has invertible
relative dualizing module.** -/
private theorem isInvertible_of_fiber_isInvertible
    (D : RelativeDualizingModuleData f)
    (E : ∀ x : X, RelativeDualizingModuleData (f.fiberToSpecResidueField x))
    (hE : ∀ x : X, Stacks.SheafOfModules.IsInvertible (f.fiber x).presheaf
      (structureSheafRing (f.fiber x).toRingedSpace).property (E x).sheaf) :
    Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property D.sheaf := by
  refine (isInvertible_iff_exists_chart_dualizingModule_invertible D).mpr fun y => ?_
  obtain ⟨-, ⟨U, hU, rfl⟩, hyU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show f.base y ∈ (⊤ : X.Opens) from trivial) (⊤ : X.Opens).isOpen
  obtain ⟨-, ⟨V, hV, rfl⟩, hyV, hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    hyU (f ⁻¹ᵁ U).isOpen
  have hUa : IsAffineOpen U := hU
  have hVa : IsAffineOpen V := hV
  let Ua : X.affineOpens := ⟨U, hUa⟩
  let Va : Y.affineOpens := ⟨V, hVa⟩
  refine ⟨Ua, Va, hVU, hyV, fun F => ?_⟩
  let : Algebra Γ(X, U) Γ(Y, V) := (f.appLE U V hVU).hom.toAlgebra
  have := IsLocallyNoetherian.component_noetherian Ua
  have := IsLocallyNoetherian.component_noetherian Va
  have : Module.Flat Γ(X, U) Γ(Y, V) := f.flat_appLE hU hV hVU
  have : Algebra.FiniteType Γ(X, U) Γ(Y, V) := f.finiteType_appLE hU hV hVU
  have : Algebra.QuasiFinite Γ(X, U) Γ(Y, V) :=
    LocallyQuasiFinite.quasiFinite_appLE hU hV hVU
  let : Module Γ(X, U) (dualizingModule F) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(Y, V))
  have : IsScalarTower Γ(X, U) Γ(Y, V) (dualizingModule F) :=
    IsScalarTower.of_compHom _ _ _
  have := dualizingModule_finite F
  have := dualizingModule_flat F
  refine module_invertible_of_fiberwise_invertible (A := Γ(X, U)) fun p => ?_
  let x := hUa.fromSpec p
  have hxU : x ∈ U := hUa.range_fromSpec.le ⟨p, rfl⟩
  let K : (Spec (X.residueField x)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let W : (f.fiber x).affineOpens :=
    ⟨f.fiberι x ⁻¹ᵁ V, isAffineOpen_fiber_preimage f Ua Va hVU x hxU⟩
  have hKU : K.1 ≤ X.fromSpecResidueField x ⁻¹ᵁ U := top_le_preimage_fromSpecResidueField hxU
  have hWK : W.1 ≤ f.fiberToSpecResidueField x ⁻¹ᵁ K.1 := by simp [K]
  have hWV : W.1 ≤ f.fiberι x ⁻¹ᵁ V := le_rfl
  let a := f.appLE U V hVU
  let b := (X.fromSpecResidueField x).appLE U K hKU
  let c := (f.fiberι x).appLE V W hWV
  let d := (f.fiberToSpecResidueField x).appLE K W hWK
  have hWeq : W.1 = f.fiberι x ⁻¹ᵁ V ⊓ f.fiberToSpecResidueField x ⁻¹ᵁ K.1 := by
    simp [W, K]
  have hpush : IsPushout a b c d := isPushout_appLE_of_isPullback
    (IsPullback.of_hasPullback f (X.fromSpecResidueField x)) hU hV hVU
    (isAffineOpen_top _) hKU hWeq
  let : Algebra Γ(X, U) Γ(Spec (X.residueField x), K.1) := b.hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(f.fiber x, W.1) := c.hom.toAlgebra
  let : Algebra Γ(Spec (X.residueField x), K.1) Γ(f.fiber x, W.1) := d.hom.toAlgebra
  let : Algebra Γ(X, U) Γ(f.fiber x, W.1) := (c.hom.comp a.hom).toAlgebra
  have : IsScalarTower Γ(X, U) Γ(Y, V) Γ(f.fiber x, W.1) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X, U) Γ(Spec (X.residueField x), K.1) Γ(f.fiber x, W.1) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hpush.w)
  have : Algebra.IsPushout Γ(X, U) Γ(Spec (X.residueField x), K.1) Γ(Y, V)
      Γ(f.fiber x, W.1) := CommRingCat.isPushout_iff_isPushout.mp hpush.flip
  have := IsLocallyNoetherian.component_noetherian K
  have := IsLocallyNoetherian.component_noetherian W
  have := hE x
  obtain ⟨G⟩ := nonempty_relativeDualizingChartFactorization
    (f.fiberToSpecResidueField x) K W hWK
  have : Module.Invertible Γ(f.fiber x, W.1) (dualizingModule G) :=
    module_invertible_dualizingModule (E x) K W hWK G
  have : Module.Invertible Γ(f.fiber x, W.1)
      (Γ(f.fiber x, W.1) ⊗[Γ(Y, V)] dualizingModule F) :=
    (dualizingModule_invertible_iff_baseChange_of_isPushout F G).mp inferInstance
  let : Algebra Γ(Y, V) (p.asIdeal.Fiber Γ(Y, V)) := Algebra.TensorProduct.rightAlgebra
  let eB := algEquivFiberSections f Ua Va hVU p
  exact (invertible_iff_semilinearEquiv eB.toRingEquiv
    (tensorSemilinearEquivOfAlgEquiv (M := dualizingModule F) eB)).mpr inferInstance

/-- For a quasi-finite flat morphism of Noetherian schemes, a relative dualizing module `D` of
`f` is an invertible `𝒪_Y`-module if and only if, for every point `x` of `X`, a relative
dualizing module `E x` of the fibre `Y_x → Spec κ(x)` is invertible. The modules are given as
chart data; for the constructed modules of Tag 0BVG this is
`Stacks.Discriminant.relativeDualizingModuleData_isInvertible_iff_fibers`. -/
theorem relativeDualizingModule_isInvertible_iff_fibers
    (D : RelativeDualizingModuleData f)
    (E : ∀ x : X, RelativeDualizingModuleData (f.fiberToSpecResidueField x)) :
    Stacks.SheafOfModules.IsInvertible Y.presheaf
        (structureSheafRing Y.toRingedSpace).property D.sheaf ↔
      ∀ x : X, Stacks.SheafOfModules.IsInvertible (f.fiber x).presheaf
        (structureSheafRing (f.fiber x).toRingedSpace).property (E x).sheaf :=
  ⟨fun hD x => fiber_isInvertible_of_isInvertible f D hD x (E x),
    isInvertible_of_fiber_isInvertible f D E⟩

/-- **Stacks Project, Tag 0DWK**, part (2). For a quasi-finite flat morphism `f : Y ⟶ X` of
Noetherian schemes, the relative dualizing module `ω_{Y/X}` of Tag 0BVG is an invertible
`𝒪_Y`-module if and only if the relative dualizing module `ω_{Y_x/x}` of the fibre
`Y_x → Spec κ(x)` is invertible for every point `x` of `X`. Both modules are the ones constructed
by `Stacks.Discriminant.relativeDualizingModuleData`. -/
@[stacks 0DWK "part (2)"]
theorem relativeDualizingModuleData_isInvertible_iff_fibers :
    Stacks.SheafOfModules.IsInvertible Y.presheaf
        (structureSheafRing Y.toRingedSpace).property (relativeDualizingModuleData f).sheaf ↔
      ∀ x : X, Stacks.SheafOfModules.IsInvertible (f.fiber x).presheaf
        (structureSheafRing (f.fiber x).toRingedSpace).property
          (relativeDualizingModuleData (f.fiberToSpecResidueField x)).sheaf :=
  relativeDualizingModule_isInvertible_iff_fibers f (relativeDualizingModuleData f)
    fun x => relativeDualizingModuleData (f.fiberToSpecResidueField x)

end Fibres

end

end Schemes

end Stacks.Discriminant

end
