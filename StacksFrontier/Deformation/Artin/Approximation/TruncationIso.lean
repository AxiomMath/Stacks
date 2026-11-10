module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence
public import StacksFrontier.Deformation.Artin.Approximation.QuotientEquiv
public import StacksFrontier.RingTheory.AdicCompletion.PolynomialSurjection
public import StacksFrontier.RingTheory.Algebra.DirectLimit.FinitePresentation
public import StacksFrontier.RingTheory.ArtinRees.AssociatedGraded
public import StacksFrontier.RingTheory.ArtinRees.Constant
public import StacksFrontier.RingTheory.Etale.AssociatedGraded
public import StacksFrontier.RingTheory.Filtration.AssociatedGraded
public import StacksFrontier.RingTheory.GRing.Defs
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.RingTheory.Noetherian.ArtinRees
public import StacksFrontier.RingTheory.Smoothing.ApproximationGRing
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import all StacksFrontier.Deformation.Artin.Approximation.QuotientEquiv

/-!
# Approximation over a complete local ring: truncation isomorphisms

Second part of `StacksFrontier.Deformation.Artin.Approximation`. It contains the geometric
inputs of the proof of Stacks 07XB (finite affine charts of a field spectrum, factorisation
through an affine open, quotients in the chosen big site, morphisms of site objects), the form
of Artin approximation over a G-ring (Stacks 07QZ) the proof consumes, finiteness of residue
fields under truncation isomorphisms, the graded ring maps induced by ring maps, and the
truncation isomorphisms for étale, completion, quotient and localization maps.

## References

* [Stacks Project, Tag 07XB](https://stacks.math.columbia.edu/tag/07XB)
* [Stacks Project, Tag 07QZ](https://stacks.math.columbia.edu/tag/07QZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing AssociatedGraded

namespace Deformation.Artin.Approximation

universe u v w

/-- A locally finite type map from a field spectrum has a finite affine chart on
sections. This is the first geometric bridge in the approximation argument: it
lets the residue field be treated as a finite algebra over a suitable affine
neighborhood of its image. -/
theorem exists_finite_affine_chart_of_field
    {k : Type u} [Field k] {S : Scheme.{u}} (f : Spec (.of k) ⟶ S)
    (hfinite : LocallyOfFiniteType f) (hquasi : QuasiCompact f) :
    ∃ (U : S.affineOpens)
      (hU : (⊤ : (Spec (.of k)).Opens) ≤ f ⁻¹ᵁ U.1),
      ((f.appLE U ⊤ hU) ≫ (Scheme.ΓSpecIso (.of k)).hom).hom.Finite := by
  have hfirst : LocallyOfFiniteType f ∧ QuasiCompact f := ⟨hfinite, hquasi⟩
  exact ((AlgebraicGeometry.finiteType_specField_tfae f).out 1 3).mp hfirst

/-- The finite affine chart can also be used as a finite-type algebra chart. This
form is convenient when adjoining the finitely many coefficients used in the
polynomial presentation of the approximation. -/
private theorem exists_finiteType_affine_chart_of_field
    {k : Type u} [Field k] {S : Scheme.{u}} (f : Spec (.of k) ⟶ S)
    (hfinite : LocallyOfFiniteType f) (hquasi : QuasiCompact f) :
    ∃ (U : S.affineOpens)
      (hU : (⊤ : (Spec (.of k)).Opens) ≤ f ⁻¹ᵁ U.1),
      (((f.appLE U ⊤ hU) ≫ (Scheme.ΓSpecIso (.of k)).hom).hom).FiniteType := by
  obtain ⟨U, hU, hfin⟩ := exists_finite_affine_chart_of_field f hfinite hquasi
  exact ⟨U, hU, hfin.finiteType⟩

/-- A morphism from the spectrum of a local ring whose closed point lands in an open
subscheme factors through that open. This lets the finite affine chart of the residue
field also serve as a chart for the complete local ring. -/
theorem factorsThrough_affineOpen_of_closedPoint
    {R : Type u} [CommRing R] [IsLocalRing R] {S : Scheme.{u}}
    (f : Spec (.of R) ⟶ S) (U : S.affineOpens) (s : S)
    (hs : f (closedPoint R) = s) (hsU : s ∈ U.1) :
    ∃ g : Spec (.of R) ⟶ U.1, g ≫ U.1.ι = f := by
  have hclosed : f (closedPoint R) ∈ U.1 := hs ▸ hsU
  have hrange : Set.range f ⊆ Set.range U.1.ι := by
    rintro _ ⟨x, rfl⟩
    have hx : f x ∈ U.1 :=
      ((IsLocalRing.specializes_closedPoint x).map f.continuous).mem_open U.1.2 hclosed
    exact ⟨⟨f x, hx⟩, rfl⟩
  exact ⟨IsOpenImmersion.lift U.1.ι f hrange, IsOpenImmersion.lift_fac _ _ _⟩

/-- Quotients of affine objects of the chosen big site remain in the site. -/
theorem contains_spec_quotient
    (B : AlgebraicGeometry.BigFppfSite.{u}) {R : Type u} [CommRing R]
    (hR : B.Contains (Spec (.of R))) (I : Ideal R) :
    B.Contains (Spec (.of (R ⧸ I))) := by
  apply Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit hR
  exact (Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := I))).trans
    (le_max_right _ _)

/-- A compatible map of affine schemes induces a morphism of their objects over `S`. -/
def siteObjectHom
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R A : Type u} [CommRing R] [CommRing A]
    (hR : B.Contains (Spec (.of R))) (hA : B.Contains (Spec (.of A)))
    (fR : Spec (.of R) ⟶ S) (fA : Spec (.of A) ⟶ S)
    (g : Spec (.of R) ⟶ Spec (.of A)) (hg : g ≫ fA = fR) :
    siteObject B S hS hR fR ⟶ siteObject B S hS hA fA := by
  refine Over.homMk (ObjectProperty.homMk (X := B.obj hR) (Y := B.obj hA) g) ?_
  apply ObjectProperty.hom_ext
  exact hg

private theorem toScheme_siteObjectHom
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R A : Type u} [CommRing R] [CommRing A]
    (hR : B.Contains (Spec (.of R))) (hA : B.Contains (Spec (.of A)))
    (fR : Spec (.of R) ⟶ S) (fA : Spec (.of A) ⟶ S)
    (g : Spec (.of R) ⟶ Spec (.of A)) (hg : g ≫ fA = fR) :
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (siteObjectHom B S hS hR hA fR fA g hg) = g := rfl

/-- **Stacks 07QZ**, Artin approximation for a finite system of polynomial equations over a
Noetherian local G-ring, in the shape the proof of Stacks 07XB consumes.

Given a solution of the system in the completion of `R` at its maximal ideal, there is an
étale `R`-algebra `R'` with a maximal ideal `m'` over `m_R` inducing an isomorphism on
residue fields, a local `R`-algebra map `R' → R^` and an exact solution in `R'` congruent
to the given one modulo `(m')^N`.

This repackages `Stacks.Smoothing.exists_localEtaleSolution_of_isGRing`, which is 07QZ
proved unconditionally, as a plain existential statement. -/
private theorem exists_etale_solution_approximating
    (R : Type u) [CommRing R] [IsLocalRing R] (hG : IsGRing R)
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) R)
    (a : Fin n → AdicCompletion (maximalIdeal R) R)
    (ha : ∀ j, MvPolynomial.eval₂
      (algebraMap R (AdicCompletion (maximalIdeal R) R)) a (f j) = 0)
    (N : ℕ) :
    letI : IsNoetherianRing R := hG.1
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R')
      (_ : Algebra.Etale R R') (m' : Ideal R'),
      ∃ _ : m'.IsMaximal,
        ∃ h_over : Ideal.comap (algebraMap R R') m' = maximalIdeal R,
        Function.Bijective
          (Ideal.ResidueField.map (maximalIdeal R) m'
            (algebraMap R R') h_over.symm) ∧
        ∃ (ι : R' →ₐ[R] AdicCompletion (maximalIdeal R) R)
          (b : Fin n → R'),
          Ideal.comap ι.toRingHom
              (maximalIdeal (AdicCompletion (maximalIdeal R) R)) = m' ∧
          (∀ j, MvPolynomial.eval₂ (algebraMap R R') b (f j) = 0) ∧
          (∀ i, a i - ι (b i) ∈ Ideal.map ι.toRingHom (m' ^ N)) := by
  let : IsNoetherianRing R := hG.1
  obtain ⟨s, hmax, ι, hιlocal, hclose, -⟩ :=
    Stacks.Smoothing.exists_localEtaleSolution_of_isGRing hG f N a
      (fun j => by rw [MvPolynomial.aeval_def]; exact ha j)
  refine ⟨s.carrier, s.commRing, s.algebra, s.etale, s.prime, hmax, s.comap_prime.symm,
    s.residueField_bijective, ι, s.sol, ?_, s.eval_sol, hclose⟩
  ext x
  rw [Ideal.mem_comap]
  exact (hιlocal x).symm

/-- Artin approximation with arbitrary finite sets of variables and equations,
deduced from the `Fin`-indexed form by reindexing. This shape keeps the four blocks of
variables in the approximation construction separate. -/
theorem exists_etale_solution_approximating_fintype
    (R : Type u) [CommRing R] [IsLocalRing R] (hG : IsGRing R)
    {E : Type v} {V : Type w} [Finite E] [Finite V]
    (f : E → MvPolynomial V R)
    (a : V → AdicCompletion (maximalIdeal R) R)
    (ha : ∀ j, MvPolynomial.eval₂
      (algebraMap R (AdicCompletion (maximalIdeal R) R)) a (f j) = 0)
    (N : ℕ) :
    letI : IsNoetherianRing R := hG.1
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R')
      (_ : Algebra.Etale R R') (m' : Ideal R'),
      ∃ _ : m'.IsMaximal,
        ∃ h_over : Ideal.comap (algebraMap R R') m' = maximalIdeal R,
          Function.Bijective
            (Ideal.ResidueField.map (maximalIdeal R) m'
              (algebraMap R R') h_over.symm) ∧
          ∃ (ι : R' →ₐ[R] AdicCompletion (maximalIdeal R) R)
            (b : V → R'),
            Ideal.comap ι.toRingHom
                (maximalIdeal (AdicCompletion (maximalIdeal R) R)) = m' ∧
            (∀ j, MvPolynomial.eval₂ (algebraMap R R') b (f j) = 0) ∧
            (∀ i, a i - ι (b i) ∈ Ideal.map ι.toRingHom (m' ^ N)) := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let : Fintype V := Fintype.ofFinite V
  let eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let eE : E ≃ Fin (Fintype.card E) := Fintype.equivFin E
  let fFin : Fin (Fintype.card E) →
      MvPolynomial (Fin (Fintype.card V)) R :=
    fun j ↦ MvPolynomial.rename eV (f (eE.symm j))
  let aFin : Fin (Fintype.card V) → AdicCompletion (maximalIdeal R) R :=
    fun i ↦ a (eV.symm i)
  have haFin (j : Fin (Fintype.card E)) :
      MvPolynomial.eval₂
        (algebraMap R (AdicCompletion (maximalIdeal R) R)) aFin (fFin j) = 0 := by
    simpa [fFin, aFin, MvPolynomial.eval₂_rename, Function.comp_def]
      using ha (eE.symm j)
  let : IsNoetherianRing R := hG.1
  obtain ⟨R', ringR', algR', etaleR', m', hm', hover, hbij,
    ι, bFin, hlocal, hzero, hclose⟩ :=
      exists_etale_solution_approximating R hG fFin aFin haFin N
  let : CommRing R' := ringR'
  let : Algebra R R' := algR'
  let : Algebra.Etale R R' := etaleR'
  refine ⟨R', ringR', algR', etaleR', m', hm', hover, hbij,
    ι, (fun v ↦ bFin (eV v)), hlocal, ?_, ?_⟩
  · intro j
    simpa [fFin, MvPolynomial.eval₂_rename, Function.comp_def]
      using hzero (eE j)
  · intro i
    simpa [aFin] using hclose (eV i)

/-- A maximal ideal contracts to a maximal ideal when its residue field is
finite over the ground ring. -/
theorem isMaximal_comap_of_finite_residueField
    {Λ A T : Type*} [CommRing Λ] [CommRing A] [CommRing T]
    [Algebra Λ A] [Algebra A T] [Algebra Λ T] [IsScalarTower Λ A T]
    (m : Ideal T) [m.IsMaximal]
    [Module.Finite Λ m.ResidueField] :
    (Ideal.comap (algebraMap A T) m).IsMaximal := by
  let f : A →+* m.ResidueField :=
    (algebraMap T m.ResidueField).comp (algebraMap A T)
  let : Algebra A m.ResidueField := f.toAlgebra
  let : Module A m.ResidueField := Algebra.toModule
  have : IsScalarTower Λ A m.ResidueField := IsScalarTower.of_algebraMap_eq (by
    intro x
    change (algebraMap T m.ResidueField) ((algebraMap Λ T) x) =
      (algebraMap T m.ResidueField) ((algebraMap A T) ((algebraMap Λ A) x))
    rw [IsScalarTower.algebraMap_apply Λ A T])
  let : Module.Finite A m.ResidueField :=
    Module.Finite.right Λ A m.ResidueField
  let : Algebra.IsIntegral A m.ResidueField :=
    Algebra.IsIntegral.of_finite A m.ResidueField
  convert Algebra.ker_algebraMap_isMaximal_of_isIntegral A m.ResidueField using 1
  ext x
  change (algebraMap A T) x ∈ m ↔
    (algebraMap T m.ResidueField) ((algebraMap A T) x) = 0
  exact Ideal.algebraMap_residueField_eq_zero.symm

/-- Finite residue fields pass through an algebra isomorphism of positive-order
infinitesimal neighborhoods. -/
private theorem finite_residue_quotient_of_trunc_equiv
    {Λ : Type u} {R : Type v} {A : Type w} [CommRing Λ] [CommRing R] [CommRing A]
    [Algebra Λ R] [Algebra Λ A] [IsLocalRing R]
    (mA : Ideal A) [mA.IsMaximal]
    [Module.Finite Λ (R ⧸ maximalIdeal R)]
    (N : ℕ) (hN : 1 ≤ N)
    (e : (R ⧸ maximalIdeal R ^ N) ≃ₐ[Λ] (A ⧸ mA ^ N)) :
    Module.Finite Λ (A ⧸ mA) := by
  have hpowA : mA ^ N ≤ mA :=
    Ideal.pow_le_self (by omega : N ≠ 0)
  let π : (A ⧸ mA ^ N) →+* (A ⧸ mA) :=
    Ideal.Quotient.factor hpowA
  let ψ : R →+* (A ⧸ mA) :=
    π.comp (e.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk _))
  have hψsurj : Function.Surjective ψ :=
    (Ideal.Quotient.factor_surjective hpowA).comp
      (e.surjective.comp Ideal.Quotient.mk_surjective)
  let : Field (A ⧸ mA) := Ideal.Quotient.field mA
  have hker : RingHom.ker ψ = maximalIdeal R :=
    IsLocalRing.ker_eq_maximalIdeal ψ hψsurj
  have hkill : ∀ r ∈ maximalIdeal R, ψ r = 0 := fun r hr ↦
    RingHom.mem_ker.mp (by rwa [hker])
  let q : (R ⧸ maximalIdeal R) →+* (A ⧸ mA) :=
    Ideal.Quotient.lift (maximalIdeal R) ψ hkill
  have hqsurj : Function.Surjective q :=
    Ideal.Quotient.lift_surjective_of_surjective (maximalIdeal R) hkill hψsurj
  let qAlg : (R ⧸ maximalIdeal R) →ₐ[Λ] (A ⧸ mA) :=
    { toRingHom := q
      commutes' := by
        intro l
        change q (Ideal.Quotient.mk (maximalIdeal R) (algebraMap Λ R l)) =
          Ideal.Quotient.mk mA (algebraMap Λ A l)
        rw [Ideal.Quotient.lift_mk]
        change π (e (Ideal.Quotient.mk (maximalIdeal R ^ N) (algebraMap Λ R l))) =
          Ideal.Quotient.mk mA (algebraMap Λ A l)
        rw [show Ideal.Quotient.mk (maximalIdeal R ^ N) (algebraMap Λ R l) =
            algebraMap Λ (R ⧸ maximalIdeal R ^ N) l from rfl, e.commutes]
        change π (Ideal.Quotient.mk (mA ^ N) (algebraMap Λ A l)) = _
        exact Ideal.Quotient.factor_mk hpowA _ }
  exact Module.Finite.of_surjective qAlg.toLinearMap hqsurj

theorem finite_residueField_of_trunc_equiv
    {Λ : Type u} {R : Type v} {A : Type w} [CommRing Λ] [CommRing R] [CommRing A]
    [Algebra Λ R] [Algebra Λ A] [IsLocalRing R]
    (mA : Ideal A) [mA.IsMaximal]
    [Module.Finite Λ (R ⧸ maximalIdeal R)]
    (N : ℕ) (hN : 1 ≤ N)
    (e : (R ⧸ maximalIdeal R ^ N) ≃ₐ[Λ] (A ⧸ mA ^ N)) :
    Module.Finite Λ mA.ResidueField := by
  let : Module.Finite Λ (A ⧸ mA) :=
    finite_residue_quotient_of_trunc_equiv mA N hN e
  have : Module.Finite (A ⧸ mA) mA.ResidueField :=
    .of_surjective (Algebra.linearMap _ _)
      mA.bijective_algebraMap_quotient_residueField.surjective
  exact Module.Finite.trans (A ⧸ mA) mA.ResidueField

/-- Finiteness of a quotient module is independent of whether its scalar
action is supplied through the quotient or through its compatible algebra map. -/
theorem finite_quotient_of_compatible_algebraMap
    {Λ : Type u} {R : Type v} [CommRing Λ] [CommRing R] [IsLocalRing R]
    (φ : Λ →+* R) (ψ : Λ →+* (R ⧸ maximalIdeal R))
    (hφψ : (Ideal.Quotient.mk (maximalIdeal R)).comp φ = ψ)
    (hfin : letI : Algebra Λ (R ⧸ maximalIdeal R) := ψ.toAlgebra
      Module.Finite Λ (R ⧸ maximalIdeal R)) :
    letI : Algebra Λ R := φ.toAlgebra
    Module.Finite Λ (R ⧸ maximalIdeal R) := by
  let : Algebra Λ (R ⧸ maximalIdeal R) := ψ.toAlgebra
  let : Module.Finite Λ (R ⧸ maximalIdeal R) := hfin
  let : Algebra Λ R := φ.toAlgebra
  subst ψ
  let P : Module Λ (R ⧸ maximalIdeal R) :=
    @Algebra.toModule Λ (R ⧸ maximalIdeal R) _ _
      ((Ideal.Quotient.mk (maximalIdeal R)).comp φ).toAlgebra
  let Q : Module Λ (R ⧸ maximalIdeal R) :=
    Submodule.Quotient.module' (maximalIdeal R)
  have hPQ : P = Q := by
    apply Module.ext' P Q
    intro l x
    induction x using Quotient.inductionOn with
    | _ r => rfl
  have : Module.Finite Λ (R ⧸ maximalIdeal R) := by
    have hPF : @Module.Finite Λ (R ⧸ maximalIdeal R) _ _ P := hfin
    exact hPQ ▸ hPF
  exact inferInstance

/-- A finite type subalgebra can be enlarged to contain the image of a
finite type algebra while remaining finite type. -/
theorem exists_finiteType_intermediate_range
    {Λ : Type u} {C : Type v} {T : Type w}
    [CommRing Λ] [CommRing C] [CommRing T]
    [Algebra Λ C] [Algebra Λ T] [Algebra.FiniteType Λ C]
    (S : Subalgebra Λ T) [Algebra.FiniteType Λ S]
    (f : C →ₐ[Λ] T) :
    ∃ S' : Subalgebra Λ T,
      S ≤ S' ∧ Algebra.FiniteType Λ S' ∧
      ∃ f' : C →ₐ[Λ] S', (S'.val).comp f' = f := by
  let S' : Subalgebra Λ T := S ⊔ f.range
  have hS : S.FG := (Subalgebra.fg_iff_finiteType S).mpr inferInstance
  have hRange : f.range.FG := by
    rw [← Algebra.map_top]
    exact Subalgebra.FG.map f Algebra.FiniteType.out
  have hS' : S'.FG := Subalgebra.FG.sup hS hRange
  let : Algebra.FiniteType Λ S' := (Subalgebra.fg_iff_finiteType S').mp hS'
  let f' : C →ₐ[Λ] S' :=
    (Subalgebra.inclusion le_sup_right).comp f.rangeRestrict
  refine ⟨S', le_sup_left, inferInstance, f', ?_⟩
  ext c
  rfl


private def gradedPieceMap {A : Type u} {D : Type v} [CommRing A] [CommRing D]
    (f : A →+* D) (I : Ideal A) (J : Ideal D) (h : I ≤ J.comap f) (n : ℕ) :
    piece (M := A) I n →+ piece (M := D) J n := by
  let g : power (M := A) I n →+ power (M := D) J n :=
    { toFun := fun a => ⟨f a, by
        rw [ring_power_eq]
        change (a : A) ∈ Ideal.comap f (J ^ n)
        exact ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow f n))
          (by simpa using a.property)⟩
      map_zero' := Subtype.ext f.map_zero
      map_add' := fun a b => Subtype.ext (f.map_add a b) }
  exact QuotientAddGroup.map _ _ g (fun a ha => by
    change f a ∈ power (M := D) J (n+1)
    rw [ring_power_eq]
    change (a : A) ∈ Ideal.comap f (J ^ (n+1))
    apply ((Ideal.pow_right_mono h (n+1)).trans (Ideal.le_comap_pow f (n+1)))
    change (a : A) ∈ power (M := A) I (n+1) at ha
    simpa only [ring_power_eq] using ha)

private theorem gradedPieceMap_mk {A : Type u} {D : Type v} [CommRing A] [CommRing D]
    (f : A →+* D) (I : Ideal A) (J : Ideal D) (h : I ≤ J.comap f) (n : ℕ)
    (a : power (M := A) I n) :
    gradedPieceMap f I J h n (mk I n a) =
      mk J n ⟨f a, by
        rw [ring_power_eq]
        change (a : A) ∈ Ideal.comap f (J ^ n)
        exact ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow f n))
          (by simpa using a.property)⟩ := rfl

private def gradedRingMap {A : Type u} {D : Type v} [CommRing A] [CommRing D]
    (f : A →+* D) (I : Ideal A) (J : Ideal D) (h : I ≤ J.comap f) :
    gradedRing I →+* gradedRing J := by
  classical
  let g : gradedRing I →+ gradedRing J := DirectSum.map (gradedPieceMap f I J h)
  refine { g with map_one' := ?_, map_mul' := ?_ }
  · change g (DirectSum.of _ 0 (mk I 0 ⟨1, mem_power_zero _ _⟩)) =
      DirectSum.of _ 0 (mk J 0 ⟨1, mem_power_zero _ _⟩)
    simp only [g, DirectSum.map_of, gradedPieceMap_mk, map_one]
  · intro x y
    change g (x * y) = g x * g y
    induction x using DirectSum.induction_on with
    | zero => simp
    | add x x' hx hx' => simpa only [add_mul, map_add] using congrArg₂ (· + ·) hx hx'
    | of i a =>
      induction y using DirectSum.induction_on with
      | zero => simp
      | add y y' hy hy' => simpa only [mul_add, map_add] using congrArg₂ (· + ·) hy hy'
      | of j b =>
        induction a using Quotient.inductionOn with
        | _ a =>
          induction b using Quotient.inductionOn with
          | _ b =>
            change g (DirectSum.of _ i (mk I i a) * DirectSum.of _ j (mk I j b)) = _
            simp only [of_mul_of, homogeneousSMul_mk, g, DirectSum.map_of,
              gradedPieceMap_mk]
            change DirectSum.of _ (i+j) (mk J (i+j) ⟨f ((a : A) * b), _⟩) =
              DirectSum.of _ (i+j) (mk J (i+j) ⟨f a * f b, _⟩)
            simp only [map_mul]

private theorem gradedRingMap_of {A : Type u} {D : Type v} [CommRing A] [CommRing D]
    (f : A →+* D) (I : Ideal A) (J : Ideal D) (h : I ≤ J.comap f)
    (n : ℕ) (a : piece (M := A) I n) :
    gradedRingMap f I J h (DirectSum.of _ n a) =
      DirectSum.of _ n (gradedPieceMap f I J h n a) := by
  classical
  exact DirectSum.map_of _ _ _

private theorem gradedPieceMap_bijective {A : Type u} {D : Type v}
    [CommRing A] [CommRing D] (f : A →+* D) (I : Ideal A) (J : Ideal D)
    (h : I ≤ J.comap f)
    (hb : ∀ n, Function.Bijective (Ideal.quotientMap (J ^ n) f
      ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow f n)))) (n : ℕ) :
    Function.Bijective (gradedPieceMap f I J h n) := by
  have hreflect (k : ℕ) (a : A) (ha : f a ∈ J ^ k) : a ∈ I ^ k := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (hb k).1
    simpa only [map_zero, Ideal.quotientMap_mk] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
  refine ⟨fun a b hab ↦ ?_, fun b ↦ ?_⟩
  · induction a using Quotient.inductionOn with
    | _ a =>
      induction b using Quotient.inductionOn with
      | _ b =>
        change mk J n _ = mk J n _ at hab
        rw [mk, mk, Submodule.Quotient.eq] at hab
        apply (Submodule.Quotient.eq _).2
        change (a : A) - b ∈ power (M := A) I (n+1)
        rw [ring_power_eq]
        apply hreflect
        change f (a : A) - f (b : A) ∈ power (M := D) J (n+1) at hab
        simpa only [map_sub, ring_power_eq] using hab
  · induction b using Quotient.inductionOn with
    | _ b =>
      obtain ⟨a, ha⟩ := (hb (n+1)).2 (Ideal.Quotient.mk _ (b : D))
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      have hd : f a - b ∈ J ^ (n+1) := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 ha
      have haI : a ∈ I ^ n := by
        apply hreflect
        have hbJ : (b : D) ∈ J ^ n := by simpa using b.property
        have hdJ : f a - b ∈ J ^ n := (Ideal.pow_le_pow_right (Nat.le_succ n)) hd
        simpa using (J ^ n).add_mem hdJ hbJ
      refine ⟨mk I n ⟨a, by simpa using haI⟩, ?_⟩
      rw [gradedPieceMap_mk]
      apply (Submodule.Quotient.eq _).2
      change f a - (b : D) ∈ power (M := D) J (n+1)
      simpa only [ring_power_eq] using hd

private def gradedRingEquiv {A : Type u} {D : Type v}
    [CommRing A] [CommRing D] (f : A →+* D) (I : Ideal A) (J : Ideal D)
    (h : I ≤ J.comap f)
    (hb : ∀ n, Function.Bijective (Ideal.quotientMap (J ^ n) f
      ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow f n)))) :
    gradedRing I ≃+* gradedRing J := by
  classical
  let e (n : ℕ) := AddEquiv.ofBijective (gradedPieceMap f I J h n)
    (gradedPieceMap_bijective f I J h hb n)
  exact RingEquiv.ofBijective (gradedRingMap f I J h)
    (DirectSum.congrAddEquiv e).bijective

private theorem gradedRingEquiv_of {A : Type u} {D : Type v}
    [CommRing A] [CommRing D] (f : A →+* D) (I : Ideal A) (J : Ideal D)
    (h : I ≤ J.comap f)
    (hb : ∀ n, Function.Bijective (Ideal.quotientMap (J ^ n) f
      ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow f n)))) (n : ℕ)
    (a : piece (M := A) I n) :
    gradedRingEquiv f I J h hb (DirectSum.of _ n a) =
      DirectSum.of _ n (gradedPieceMap f I J h n a) := gradedRingMap_of f I J h n a

private theorem gradedRingEquiv_zero {A : Type u} {D : Type v}
    [CommRing A] [CommRing D] (f : A →+* D) (I : Ideal A) (J : Ideal D)
    (h : I ≤ J.comap f)
    (hb : ∀ n, Function.Bijective (Ideal.quotientMap (J ^ n) f
      ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow f n)))) (a : A) :
    gradedRingEquiv f I J h hb
        (DirectSum.of _ 0 (mk I 0 (⟨a, mem_power_zero _ _⟩ : power (M := A) I 0))) =
      DirectSum.of _ 0 (mk J 0 (⟨f a, mem_power_zero _ _⟩ : power (M := D) J 0)) := by
  rw [gradedRingEquiv_of, gradedPieceMap_mk]

private theorem gradedRingEquiv_symm_grade {A : Type u} {D : Type v}
    [CommRing A] [CommRing D] (f : A →+* D) (I : Ideal A) (J : Ideal D)
    (h : I ≤ J.comap f)
    (hb : ∀ n, Function.Bijective (Ideal.quotientMap (J ^ n) f
      ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow f n)))) (n : ℕ)
    (b : piece (M := D) J n) :
    ∃ a : piece (M := A) I n,
      (gradedRingEquiv f I J h hb).symm (DirectSum.of _ n b) = DirectSum.of _ n a := by
  obtain ⟨a, rfl⟩ := (gradedPieceMap_bijective f I J h hb n).2 b
  refine ⟨a, ?_⟩
  rw [← gradedRingEquiv_of f I J h hb, RingEquiv.symm_apply_apply]

private theorem ringEquiv_trunc_bijective {A : Type u} {D : Type v}
    [CommRing A] [CommRing D] (e : A ≃+* D) (I : Ideal A) (J : Ideal D)
    (h : Ideal.map e.toRingHom I = J) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap (I := I ^ n) (J ^ n) e.toRingHom
      (by rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, h])) := by
  have hp : J ^ n = Ideal.map e.toRingHom (I ^ n) := by rw [Ideal.map_pow, h]
  exact (Ideal.quotientEquiv (I ^ n) (J ^ n) e hp).bijective

private theorem ringGradedEquivOfDenomEq_of {A : Type u} [CommRing A]
    (I J K : Ideal A)
    (hden : ∀ n,
      (power (M := A) I (n + 1) ⊔ (J : Submodule A A)).comap (power I n).subtype =
      (power (M := A) I (n + 1) ⊔ (K : Submodule A A)).comap (power I n).subtype)
    (n : ℕ) (a : piece (M := A ⧸ J) (Ideal.map (Ideal.Quotient.mk J) I) n) :
    ringGradedEquivOfDenomEq I J K hden (DirectSum.of _ n a) =
      DirectSum.of _ n (ringPieceEquiv I J K n (hden n) a) := by
  classical
  exact DirectSum.map_of _ _ _

private theorem ringGradedEquivOfDenomEq_rep {A : Type u} [CommRing A]
    (I J K : Ideal A)
    (hden : ∀ n,
      (power (M := A) I (n + 1) ⊔ (J : Submodule A A)).comap (power I n).subtype =
      (power (M := A) I (n + 1) ⊔ (K : Submodule A A)).comap (power I n).subtype)
    (n : ℕ) (a : power (M := A) I n) :
    ringGradedEquivOfDenomEq I J K hden (DirectSum.of _ n (ringPieceRep I J n a)) =
      DirectSum.of _ n (ringPieceRep I K n a) := by
  rw [ringGradedEquivOfDenomEq_of]
  exact congrArg (DirectSum.of _ n) (ringPieceEquiv_mk I J K n (hden n) a)

private theorem degreeZero_eq_of_sub_mem {A : Type u} [CommRing A]
    (I : Ideal A) (a b : A) (h : a - b ∈ I) :
    DirectSum.of _ 0 (mk I 0 (⟨a, mem_power_zero _ _⟩ : power (M := A) I 0)) =
      DirectSum.of _ 0 (mk I 0 (⟨b, mem_power_zero _ _⟩ : power (M := A) I 0)) := by
  congr 1
  apply (Submodule.Quotient.eq _).2
  change a - b ∈ power (M := A) I (0+1)
  simpa using h

private def quotientPowEquiv {A : Type u} [CommRing A] (K I : Ideal A) (n : ℕ) :
    (A ⧸ (K ⊔ I ^ n)) ≃+*
      ((A ⧸ K) ⧸ (Ideal.map (Ideal.Quotient.mk K) I) ^ n) :=
  ((Ideal.quotEquivOfEq (sup_comm K (I ^ n))).trans
    (quotientSupEquiv (I ^ n) K)).trans
    (Ideal.quotEquivOfEq (Ideal.map_pow _ _ _))

private theorem quotientPowEquiv_mk {A : Type u} [CommRing A] (K I : Ideal A)
    (n : ℕ) (a : A) :
    quotientPowEquiv K I n (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk K a) := by
  simp only [quotientPowEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    quotientSupEquiv_mk]

/-- An isomorphism of quotients compatible with a ring map `f` induces an isomorphism of the
further quotients by `K` and `map f K`, compatible with `f`. -/
private theorem exists_quotient_sup_equiv {A : Type u} {D : Type v} [CommRing A] [CommRing D]
    (f : A →+* D) (I K : Ideal A) (J : Ideal D) (e : (A ⧸ I) ≃+* (D ⧸ J))
    (he : ∀ a, e (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (f a)) :
    ∃ E : (A ⧸ (K ⊔ I)) ≃+* (D ⧸ (Ideal.map f K ⊔ J)),
      ∀ a, E (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (f a) := by
  have hmap : Ideal.map e.toRingHom (Ideal.map (Ideal.Quotient.mk I) K) =
      Ideal.map (Ideal.Quotient.mk J) (Ideal.map f K) := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    ext a
    exact he a
  refine ⟨((quotientSupEquiv K I).trans (Ideal.quotientEquiv _ _ e hmap.symm)).trans
    (quotientSupEquiv (Ideal.map f K) J).symm, fun a => ?_⟩
  apply (quotientSupEquiv (Ideal.map f K) J).injective
  simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply, quotientSupEquiv_mk]
  change Ideal.Quotient.mk _ (e (Ideal.Quotient.mk _ a)) = _
  rw [he]

private theorem quotient_trunc_bijective {A : Type u} {D : Type v}
    [CommRing A] [CommRing D] (f : A →+* D) (I K : Ideal A) (J L : Ideal D)
    (h : I ≤ J.comap f) (hL : Ideal.map f K = L) (n : ℕ)
    (hb : Function.Bijective (Ideal.quotientMap (J ^ n) f
      ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow f n))))
    (g : (A ⧸ K) →+* (D ⧸ L))
    (hg : g.comp (Ideal.Quotient.mk K) = (Ideal.Quotient.mk L).comp f)
    (hIJ : Ideal.map (Ideal.Quotient.mk K) I ≤
      Ideal.comap g (Ideal.map (Ideal.Quotient.mk L) J)) :
    Function.Bijective (Ideal.quotientMap ((Ideal.map (Ideal.Quotient.mk L) J) ^ n) g
      ((Ideal.pow_right_mono hIJ n).trans (Ideal.le_comap_pow g n))) := by
  let e := RingEquiv.ofBijective (Ideal.quotientMap (J ^ n) f
    ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow f n))) hb
  have he (a : A) : e (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (f a) := rfl
  subst hL
  obtain ⟨eMid, heMid⟩ := exists_quotient_sup_equiv f (I ^ n) K (J ^ n) e he
  let eFinal := ((quotientPowEquiv K I n).symm.trans eMid).trans
    (quotientPowEquiv (Ideal.map f K) J n)
  have heFinal (a : A) : eFinal (Ideal.Quotient.mk _ (Ideal.Quotient.mk K a)) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.map f K) (f a)) := by
    calc
      _ = eFinal (quotientPowEquiv K I n (Ideal.Quotient.mk _ a)) :=
        congrArg eFinal (quotientPowEquiv_mk K I n a).symm
      _ = quotientPowEquiv (Ideal.map f K) J n (eMid (Ideal.Quotient.mk _ a)) := by
        change quotientPowEquiv (Ideal.map f K) J n (eMid ((quotientPowEquiv K I n).symm
          (quotientPowEquiv K I n (Ideal.Quotient.mk _ a)))) = _
        rw [RingEquiv.symm_apply_apply]
      _ = _ := by rw [heMid, quotientPowEquiv_mk]
  have hFinal : Ideal.quotientMap ((Ideal.map (Ideal.Quotient.mk (Ideal.map f K)) J) ^ n) g
      ((Ideal.pow_right_mono hIJ n).trans (Ideal.le_comap_pow g n)) = eFinal.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    apply Ideal.Quotient.ringHom_ext
    ext a
    change Ideal.Quotient.mk _ (g (Ideal.Quotient.mk K a)) = eFinal
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk K a))
    rw [heFinal]
    exact congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun hg a)
  rw [hFinal]
  exact eFinal.bijective

theorem etale_completion_trunc_bijective
    {T D : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [CommRing D]
    [Algebra T D] [Algebra.Etale T D] (mD : Ideal D) [mD.IsMaximal]
    (hcomp : Ideal.comap (algebraMap T D) mD = IsLocalRing.maximalIdeal T)
    (hres : Function.Bijective (Ideal.ResidueField.map
      (IsLocalRing.maximalIdeal T) mD (algebraMap T D) hcomp.symm))
    (f : D →ₐ[T] AdicCompletion (IsLocalRing.maximalIdeal T) T)
    (hf : Ideal.comap f.toRingHom
      (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal T) T)) = mD)
    (n : ℕ) :
    Function.Bijective (Ideal.quotientMap (I := mD ^ n)
      (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal T) T) ^ n)
      f.toRingHom (by rw [← hf]; exact Ideal.le_comap_pow f.toRingHom n)) := by
  cases n with
  | zero =>
    have : Subsingleton (D ⧸ mD ^ 0) := by
      simp only [pow_zero, Ideal.one_eq_top]
      infer_instance
    have : Subsingleton (AdicCompletion (IsLocalRing.maximalIdeal T) T ⧸
        IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal T) T) ^ 0) := by
      simp only [pow_zero, Ideal.one_eq_top]
      infer_instance
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  | succ n =>
    let eT := etaleTruncEquiv mD hcomp hres (n+1) (by omega)
    let eP := completionTruncEquiv T (n+1)
    let g := Ideal.quotientMap (I := mD ^ (n+1))
      (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal T) T) ^ (n+1))
      f.toRingHom (by rw [← hf]; exact Ideal.le_comap_pow f.toRingHom (n+1))
    have heq : g.comp eT.toRingHom = eP.symm.toRingHom := by
      apply Ideal.Quotient.ringHom_ext
      ext t
      apply eP.injective
      change eP (g (eT (Ideal.Quotient.mk _ t))) = eP (eP.symm (Ideal.Quotient.mk _ t))
      rw [eP.apply_symm_apply, etaleTruncEquiv_mk]
      change eP (Ideal.Quotient.mk _ (f (algebraMap T D t))) = _
      rw [f.commutes]
      exact completionTruncEquiv_mk T (n+1) t
    have hg : g = (eT.symm.trans eP.symm).toRingHom := by
      apply RingHom.ext
      intro z
      obtain ⟨y, rfl⟩ := eT.surjective z
      simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
        using RingHom.congr_fun heq y
    change Function.Bijective g
    rw [hg]
    exact (eT.symm.trans eP.symm).bijective

theorem localization_intermediate {Λ : Type u} {D : Type v}
    [CommRing Λ] [CommRing D] [Algebra Λ D]
    (S T : Subalgebra Λ D) (hST : S ≤ T) (M : Submonoid S)
    [IsLocalization M D] :
    IsLocalization (M.map (Subalgebra.inclusion hST).toRingHom) D where
  map_units := by
    rintro ⟨_, a, ha, rfl⟩
    exact IsLocalization.map_units D (⟨a, ha⟩ : M)
  surj := by
    intro z
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj M z
    refine ⟨⟨Subalgebra.inclusion hST a,
      ⟨Subalgebra.inclusion hST b, ⟨b, b.property, rfl⟩⟩⟩, hab⟩
  exists_of_eq := by
    intro x y hxy
    refine ⟨1, ?_⟩
    simpa using (Subtype.ext hxy : x = y)

theorem localization_trunc_bijective {A : Type u} {D : Type v}
    [CommRing A] [CommRing D] [Algebra A D] (M : Submonoid A) [IsLocalization M D]
    (J : Ideal D) [J.IsMaximal] (I : Ideal A) [I.IsMaximal]
    (hI : Ideal.comap (algebraMap A D) J = I) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap (I := I ^ n) (J ^ n) (algebraMap A D)
      (by rw [← hI]; exact Ideal.le_comap_pow (algebraMap A D) n)) := by
  have hmap : Ideal.map (algebraMap A D) I = J := by
    rw [← hI]
    exact IsLocalization.map_under M D J
  have hunits : Algebra.algebraMapSubmonoid (A ⧸ I ^ n) M ≤
      IsUnit.submonoid (A ⧸ I ^ n) := by
    rintro _ ⟨a, ha, rfl⟩
    apply Ideal.Quotient.isUnit_mk_pow_of_notMem I
    intro hmem
    have hj : algebraMap A D a ∈ J := by
      change a ∈ Ideal.comap (algebraMap A D) J
      rwa [hI]
    exact (Ideal.IsMaximal.ne_top (inferInstance : J.IsMaximal))
      (J.eq_top_of_isUnit_mem hj (IsLocalization.map_units D ⟨a, ha⟩))
  let e := IsLocalization.atUnits (A ⧸ I ^ n)
    (Algebra.algebraMapSubmonoid (A ⧸ I ^ n) M)
    (S := D ⧸ Ideal.map (algebraMap A D) (I ^ n)) hunits
  have hp : Ideal.map (algebraMap A D) (I ^ n) = J ^ n := by
    rw [Ideal.map_pow, hmap]
  let e' := e.toRingEquiv.trans (Ideal.quotEquivOfEq hp)
  have he : Ideal.quotientMap (I := I ^ n) (J ^ n) (algebraMap A D)
      (by rw [← hI]; exact Ideal.le_comap_pow (algebraMap A D) n) = e'.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    ext a
    rfl
  rw [he]
  exact e'.bijective

private theorem exists_truncation_equiv_of_congruent_relations
    {P : Type u} {R : Type v} {D : Type w} [CommRing P] [CommRing R] [CommRing D]
    (f : P →+* R) (hf : Function.Surjective f)
    (g : D →+* P) (I : Ideal P) (J : Ideal R) (m : Ideal D) (K : Ideal D)
    (n : ℕ) (hIJ : Ideal.map f I = J)
    (e : (D ⧸ m ^ n) ≃+* (P ⧸ I ^ n))
    (he : ∀ d, e (Ideal.Quotient.mk _ d) = Ideal.Quotient.mk _ (g d))
    (hrel : RingHom.ker f ⊔ I ^ n = Ideal.map g K ⊔ I ^ n) :
    ∃ e' : (R ⧸ J ^ n) ≃+* ((D ⧸ K) ⧸ (Ideal.map (Ideal.Quotient.mk K) m) ^ n),
      ∀ p d, p - g d ∈ I ^ n →
        e' (Ideal.Quotient.mk _ (f p)) = Ideal.Quotient.mk _ (Ideal.Quotient.mk K d) := by
  let F := (Ideal.Quotient.mk (J ^ n)).comp f
  have hF : Function.Surjective F := Ideal.Quotient.mk_surjective.comp hf
  have hker : RingHom.ker F = RingHom.ker f ⊔ I ^ n := by
    change Ideal.comap f (RingHom.ker (Ideal.Quotient.mk (J ^ n))) = _
    rw [Ideal.mk_ker, ← hIJ, ← Ideal.map_pow, Ideal.comap_map_of_surjective f hf]
    exact sup_comm _ _
  let eR : (P ⧸ (RingHom.ker f ⊔ I ^ n)) ≃+* (R ⧸ J ^ n) :=
    (Ideal.quotEquivOfEq hker.symm).trans (F.quotientKerEquivOfSurjective hF)
  have heR (p : P) : eR (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (f p) := by
    simp only [eR, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
    rfl
  obtain ⟨eD, heD⟩ := exists_quotient_sup_equiv g (m ^ n) K (I ^ n) e he
  let e' := ((eR.symm.trans (Ideal.quotEquivOfEq hrel)).trans eD.symm).trans
    (quotientPowEquiv K m n)
  refine ⟨e', ?_⟩
  intro p d hpd
  rw [← heR]
  change quotientPowEquiv K m n (eD.symm ((Ideal.quotEquivOfEq hrel)
    (eR.symm (eR (Ideal.Quotient.mk _ p))))) = _
  rw [eR.symm_apply_apply, Ideal.quotEquivOfEq_mk]
  have heq : Ideal.Quotient.mk (Ideal.map g K ⊔ I ^ n) p =
      Ideal.Quotient.mk (Ideal.map g K ⊔ I ^ n) (g d) :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 (Ideal.mem_sup_right hpd)
  rw [heq, ← heD, eD.symm_apply_apply, quotientPowEquiv_mk]

/-- The `N`th truncation isomorphism produced by an approximating set of generators.

`φP` presents `R` as the quotient of the complete ring `P` by the ideal generated by `bP`,
and `bB` is a family in `B'` whose image in `P` agrees with `bP` to order `N`. Then `R` and
`B' ⧸ (bB)` have isomorphic `N`th infinitesimal neighbourhoods, and the isomorphism
matches any two elements that are themselves congruent to order `N`.

Isolating this step keeps the main theorem affordable: the étale truncation equivalence and
the comparison of the two relation ideals are elaborated once, here. -/
theorem exists_truncation_equiv_of_approximating_generators
    {P R B' : Type u} [CommRing P] [IsLocalRing P] [CommRing R] [IsLocalRing R]
    [CommRing B'] (φP : P →+* R) (hφPsurj : Function.Surjective φP)
    (ιB : B' →+* P) (mB : Ideal B')
    (hι : mB ≤ Ideal.comap ιB (maximalIdeal P))
    (hιTrunc : ∀ n, Function.Bijective (Ideal.quotientMap (maximalIdeal P ^ n) ιB
      ((Ideal.pow_right_mono hι n).trans (Ideal.le_comap_pow ιB n))))
    {rP : ℕ} (bP : Fin rP → P) (bB : Fin rP → B')
    (hbP : Ideal.span (Set.range bP) = (RingHom.ker φP : Submodule P P))
    (N : ℕ) (hclose : ∀ j, bP j - ιB (bB j) ∈ maximalIdeal P ^ N) :
    ∃ e : (R ⧸ maximalIdeal R ^ N) ≃+*
        ((B' ⧸ Ideal.span (Set.range bB)) ⧸
          Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range bB))) mB ^ N),
      ∀ (p : P) (b : B'), p - ιB b ∈ maximalIdeal P ^ N →
        e (Ideal.Quotient.mk (maximalIdeal R ^ N) (φP p)) =
          Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span (Set.range bB)) b) := by
  have hιPowN : mB ^ N ≤ Ideal.comap ιB (maximalIdeal P ^ N) :=
    (Ideal.pow_right_mono hι N).trans (Ideal.le_comap_pow ιB N)
  let eBtruncP : (B' ⧸ mB ^ N) ≃+* (P ⧸ maximalIdeal P ^ N) :=
    RingEquiv.ofBijective (Ideal.quotientMap _ ιB hιPowN) (hιTrunc N)
  have hrelN : RingHom.ker φP ⊔ maximalIdeal P ^ N =
      Ideal.map ιB (Ideal.span (Set.range bB)) ⊔ maximalIdeal P ^ N := by
    calc
      _ = Ideal.span (Set.range bP) ⊔ maximalIdeal P ^ N :=
        congrArg (fun K : Submodule P P ↦ K ⊔ (maximalIdeal P ^ N : Ideal P)) hbP.symm
      _ = Ideal.span (Set.range fun j ↦ ιB (bB j)) ⊔ maximalIdeal P ^ N :=
        span_range_sup_eq_of_sub_mem _ bP _ hclose
      _ = _ := by rw [Ideal.map_span, ← Set.range_comp']
  exact exists_truncation_equiv_of_congruent_relations φP hφPsurj ιB (maximalIdeal P)
    (maximalIdeal R) mB (Ideal.span (Set.range bB)) N
    (IsLocalRing.map_maximalIdeal_of_surjective φP hφPsurj) eBtruncP (fun _ ↦ rfl) hrelN

end Deformation.Artin.Approximation
