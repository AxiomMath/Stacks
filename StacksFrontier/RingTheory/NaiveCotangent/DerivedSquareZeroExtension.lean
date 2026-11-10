module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.IntoField
public import StacksFrontier.Deformation.Artin.Obstruction
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveCotangentPresentation
public import StacksFrontier.Homology.DoubleExtend
public import StacksFrontier.Homology.TensorComplex.SingleTensor
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.TwoTermComplex.Ext
public import StacksFrontier.RingTheory.NaiveCotangent.Defs
public import StacksFrontier.RingTheory.NaiveCotangent.ExtensionQuasiIso

/-!
# A square-zero extension detecting a morphism into the naive cotangent complex

Let `Λ → A → k` be finite type ring maps of Noetherian rings, where `k = κ(𝔭)` is the residue
field of a prime `𝔭` of `A`.  Let `ξ : E ⟶ NL_{A/Λ}` be a morphism in `D⁻(A)` whose effect on
`H⁻¹` after derived base change to `k` fails to be surjective.  Then `A` admits a square-zero
thickening `A' → A` by `k` which does not change the differentials modulo `𝔭` and which kills
`ξ`: the composite `E ⟶ NL_{A/Λ} ⟶ NL_{A/A'}` vanishes.

The construction is dual to the failure of surjectivity.  A linear functional on
`H⁻¹(NL_{A/Λ} ⊗ᴸ k)` annihilating the image of `ξ` is, by the duality between `Ext` into a
field and the linear dual of derived base change, a nonzero class `α ∈ Ext¹(NL_{A/Λ}, k)` with
`ξ ≫ α = 0`.  Representing `α` by an actual map out of the conormal module of the canonical
presentation `P = Λ[A] ↠ A` and forming the pushout of the square-zero extension `P ↠ A` along
it produces `A'`.  That `A' → A` does not change `Ω ⊗ k` is the statement that `α ≠ 0` forces
`NL_{A/A'} ⊗ k` to have vanishing differential, which by right exactness identifies
`Ω_{A'/Λ} ⊗ k` with `Ω_{A/Λ} ⊗ k`.

## Main results

* `Deformation.Artin.exists_squareZeroExtension_killing_cotangent_morphism` constructs the
  required square-zero thickening.
* `Deformation.Artin.differentialsBaseChangeMap_surjective` — the base-change map of
  differentials of a tower `Λ → A' → A → k` is surjective as soon as `A' → A` is.
* `Deformation.Artin.differentialsBaseChangeMap_bijective_of_ker_le_ker_sq` — **the quotient
  transfer of differentials**: it is bijective as soon as, in addition, the kernel of `A' → A`
  is contained in the square of the kernel of `A' → k`.  This is the form in which "does not
  change differentials modulo `𝔭`" is verified at a surjection whose kernel is that small, and
  it is stated for arbitrary commutative rings.

## Implementation notes

The naive cotangent complex is used here in the cohomological, derived-category form
`Deformation.Artin.derivedNaiveCotangentComplex`, which places the two-term complex of the
canonical presentation in degrees `-1` and `0`; the morphism attached to a tower of base rings
is `Deformation.Artin.naiveCotangentBaseMap`.  The source writes equalities after tensoring
differentials with the residue field; here that is expressed by bijectivity of the canonical
base-change map `Deformation.Artin.differentialsBaseChangeMap`.  A derived tensor product is
supplied as data through `Deformation.Artin.DerivedTensorProduct`, so that no choice of
resolution enters the statement; that structure is pinned down by a total-left-derived
universal property, so the hypothesis does not depend on which instance is supplied.

The source invokes the identification `NL_{A/A'} ≅ I[1]` in `D(A)` for a square-zero extension
`A' ↠ A` with kernel `I`.  It is produced here at the level of the two-term complexes placed in
cohomological degrees `-1` and `0`: the tautological extension `A' ↠ A` has subsingleton
cotangent space, so its naive cotangent complex is already isomorphic, as a complex, to the
single complex `I[1]`, and the comparison with the canonical presentation is a homotopy
equivalence because morphisms of extensions exist in both directions.

## References

* [Stacks Project, Tag 07YL](https://stacks.math.columbia.edu/tag/07YL)
* [Stacks Project, Tag 07YK](https://stacks.math.columbia.edu/tag/07YK)
* [Stacks Project, Tag 07BP](https://stacks.math.columbia.edu/tag/07BP)
-/

@[expose] public section

open CategoryTheory
open ComplexShape (upIntRelNegOneZero)
open scoped TensorProduct

universe u

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard

-- The naive cotangent complex of an extension is matched below against the two-term complex
-- it defines, so its projections must unfold during unification and instance search.
attribute [local implicit_reducible] NaiveCotangent.nlOfExtension

/-- Surjectivity of the structure map of an algebra, phrased for `Algebra.ofId`. -/
private lemma surjective_ofId {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (h : Function.Surjective (algebraMap R A)) : Function.Surjective (Algebra.ofId R A) := h

/-- The tautological extension of `A` over `R` attached to a surjection `R → A`: its ring is
`R` itself and its kernel is the kernel of `R → A`. -/
private noncomputable abbrev tautologicalExtension {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (h : Function.Surjective (algebraMap R A)) : Algebra.Extension.{u} R A :=
  Algebra.Extension.ofSurjective (Algebra.ofId R A) (surjective_ofId h)

/-! ### Linear algebra of a failure of surjectivity -/

private lemma exists_nonzero_linearFunctional_annihilating_range
    {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (f : V →ₗ[k] W)
    (hf : ¬ Function.Surjective f) :
    ∃ ψ : W →ₗ[k] k, ψ ≠ 0 ∧ ψ.comp f = 0 := by
  have hrange : LinearMap.range f < ⊤ := by
    refine lt_top_iff_ne_top.mpr ?_
    intro htop
    apply hf
    intro w
    have hw : w ∈ LinearMap.range f := by rw [htop]; exact Submodule.mem_top
    rcases LinearMap.mem_range.mp hw with ⟨v, hv⟩
    exact ⟨v, hv⟩
  obtain ⟨ψ, hψ, hψrange⟩ :=
    (LinearMap.range f).exists_dual_map_eq_bot_of_lt_top hrange (by infer_instance)
  refine ⟨ψ, hψ, ?_⟩
  ext v
  have hfv : f v ∈ LinearMap.range f := LinearMap.mem_range.mpr ⟨v, rfl⟩
  have hzero : ψ (f v) ∈ (⊥ : Submodule k k) := by
    rw [← hψrange]
    exact ⟨f v, hfv, rfl⟩
  exact (Submodule.mem_bot k).mp hzero

private lemma field_linearMap_injective_of_ne_zero
    {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
    (f : k →ₗ[k] W) (hf : f ≠ 0) : Function.Injective f := by
  have hf1 : f 1 ≠ 0 := by
    intro h
    apply hf
    apply LinearMap.ext
    intro x
    have hx := f.map_smul x (1 : k)
    simp [h] at hx
    simp [hx]
  intro x y hxy
  have h : (x - y) • f 1 = 0 := by
    rw [← f.map_smul]
    simp [map_sub, hxy]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_right hf1)

private lemma lTensor_bijective_of_exact_of_zero
    {R M N P Q : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hf : LinearMap.lTensor Q f = 0) :
    Function.Bijective (LinearMap.lTensor Q g) := by
  have hfg' := lTensor_exact Q hfg hg
  exact ⟨(LinearMap.injective_iff_eq_zero_of_exact hfg').2 hf,
    LinearMap.lTensor_surjective Q hg⟩

private lemma baseChange_eq_zero_of_no_retraction
    {A k I W : Type*} [CommRing A] [Field k] [Algebra A k] [Algebra.IsEpi A k]
    [AddCommGroup I] [Module A I] [AddCommGroup W] [Module A W]
    (eI : I ≃ₗ[A] k) (d : I →ₗ[A] W)
    (h : ¬ ∃ β : W →ₗ[A] k, β.comp d = eI.toLinearMap) :
    d.baseChange k = 0 := by
  classical
  by_contra hd
  let e : k ⊗[A] I ≃ₗ[k] k :=
    (LinearEquiv.baseChange A k I k eI).trans (TensorProduct.lid' A k k)
  let g := (d.baseChange k).comp e.symm.toLinearMap
  have hg : g ≠ 0 := by
    intro hg
    apply hd
    apply LinearMap.ext
    intro z
    have hh := LinearMap.congr_fun hg (e z)
    simpa [g] using hh
  obtain ⟨β, hβ⟩ := g.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (field_linearMap_injective_of_ne_zero g hg))
  apply h
  refine ⟨(LinearMap.liftBaseChangeEquiv k).symm β, ?_⟩
  ext x
  have hh := LinearMap.congr_fun hβ (e (1 ⊗ₜ[A] x))
  simpa [g, e, LinearMap.liftBaseChangeEquiv_symm_apply,
    LinearEquiv.baseChange_tmul] using hh

private lemma residueField_isEpi {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime] :
    Algebra.IsEpi A p.ResidueField := by
  apply (Algebra.isEpi_iff_forall_one_tmul_eq A p.ResidueField).mpr
  intro z
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A ⧸ p) z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hb' : algebraMap A p.ResidueField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (A ⧸ p) p.ResidueField)).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp hb)
  change 1 ⊗ₜ[A] (algebraMap A p.ResidueField a / algebraMap A p.ResidueField b) =
    (algebraMap A p.ResidueField a / algebraMap A p.ResidueField b) ⊗ₜ[A] 1
  calc
    _ = (algebraMap A p.ResidueField a) ⊗ₜ[A] (1 / algebraMap A p.ResidueField b) := by
      rw [Algebra.algebraMap_eq_smul_one a, TensorProduct.smul_tmul]
      congr 1
      simp [Algebra.smul_def, div_eq_mul_inv]
    _ = (b • (algebraMap A p.ResidueField a / algebraMap A p.ResidueField b)) ⊗ₜ[A]
        (1 / algebraMap A p.ResidueField b) := by
      rw [Algebra.smul_def, mul_div_cancel₀ _ hb']
    _ = _ := by
      rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_div_cancel₀ _ hb']

/-! ### The square-zero pushout of a presentation along a conormal functional -/

private lemma linearEquiv_transportModule_compat
    {B A M N : Type*} [CommRing B] [CommRing A] [Algebra B A]
    [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower B A N]
    (e : M ≃ₗ[B] N) :
    letI := e.toAddEquiv.module A
    ∀ (b : B) (x : M), (algebraMap B A b) • x = b • x := by
  let := e.toAddEquiv.module A
  intro b x
  apply e.injective
  change e (e.symm ((algebraMap B A b) • e x)) = e (b • x)
  simp only [e.apply_symm_apply, e.map_smul, IsScalarTower.algebraMap_smul]

section SquareZeroPushout

open TrivSqZeroExt

private def conormalGraphIdeal
    {B M : Type u} [CommRing B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    (J : Ideal B) (φ : J →ₗ[B] M) (hJ : ∀ (j : J) (m : M), (j : B) • m = 0) :
    Ideal (TrivSqZeroExt B M) where
  carrier := {x | ∃ j : J, inl (j : B) + inr (-φ j) = x}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨j, rfl⟩ ⟨j', rfl⟩
    refine ⟨j + j', ?_⟩
    ext <;> simp [add_comm]
  smul_mem' := by
    rintro c x ⟨j, rfl⟩
    refine ⟨c.fst • j, ?_⟩
    ext <;> simp [smul_eq_mul, mul_add, hJ]

private lemma ker_smul_eq_zero
    {B A M : Type u} [CommRing B] [CommRing A] [Algebra B A]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower B A M]
    (j : RingHom.ker (algebraMap B A)) (m : M) : (j : B) • m = 0 := by
  rw [← IsScalarTower.algebraMap_smul A, j.property, zero_smul]

@[ega "0 18.2.8" "partial"]
private def conormalPushoutMap
    {B A M : Type u} [CommRing B] [CommRing A] [Algebra B A]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower B A M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    (φ : RingHom.ker (algebraMap B A) →ₗ[B] M) :
    (TrivSqZeroExt B M ⧸ conormalGraphIdeal (RingHom.ker (algebraMap B A)) φ
      (ker_smul_eq_zero (A := A))) →+* A :=
  Ideal.Quotient.lift _
    ((algebraMap B A).comp (TrivSqZeroExt.fstHom B B M).toRingHom) (by
      rintro x ⟨j, rfl⟩
      change (algebraMap B A) ((j : B) + 0) = 0
      rw [add_zero]
      exact j.property)

private noncomputable def conormalPushoutInclusion
    {B A M : Type u} [CommRing B] [CommRing A] [Algebra B A]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower B A M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    (φ : RingHom.ker (algebraMap B A) →ₗ[B] M) :
    M →ₗ[B] RingHom.ker (conormalPushoutMap φ) := by
  let J := conormalGraphIdeal (RingHom.ker (algebraMap B A)) φ (ker_smul_eq_zero (A := A))
  refine {
    toFun := fun m => ⟨Ideal.Quotient.mk J (inr m), ?_⟩
    map_add' := by intros; apply Subtype.ext; simp
    map_smul' := by
      intro b m
      apply Subtype.ext
      change Ideal.Quotient.mk J (inr (b • m)) = b • Ideal.Quotient.mk J (inr m)
      rw [inr_smul]
      exact map_smul (Ideal.Quotient.mkₐ B J) b (inr m) }
  change (algebraMap B A) 0 = 0
  exact map_zero _

private lemma conormalPushoutInclusion_injective
    {B A M : Type u} [CommRing B] [CommRing A] [Algebra B A]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower B A M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    (φ : RingHom.ker (algebraMap B A) →ₗ[B] M) :
    Function.Injective (conormalPushoutInclusion φ) := by
  have hz : ∀ m, conormalPushoutInclusion φ m = 0 → m = 0 := by
    intro m hm
    have hm' := congrArg Subtype.val hm
    change Ideal.Quotient.mk _ (inr m) = 0 at hm'
    obtain ⟨j, hj⟩ := Ideal.Quotient.eq_zero_iff_mem.mp hm'
    have hj0 : j = 0 := by
      apply Subtype.ext
      simpa using congrArg TrivSqZeroExt.fst hj
    subst j
    simpa using (congrArg TrivSqZeroExt.snd hj).symm
  intro m n h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, h, sub_self]

private lemma conormalPushoutInclusion_surjective
    {B A M : Type u} [CommRing B] [CommRing A] [Algebra B A]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower B A M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    (φ : RingHom.ker (algebraMap B A) →ₗ[B] M) :
    Function.Surjective (conormalPushoutInclusion φ) := by
  rintro ⟨x, hx⟩
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hz : (algebraMap B A) z.fst = 0 := hx
  let j : RingHom.ker (algebraMap B A) := ⟨z.fst, hz⟩
  refine ⟨φ j + z.snd, Subtype.ext ?_⟩
  change Ideal.Quotient.mk _ (inr (φ j + z.snd)) = Ideal.Quotient.mk _ z
  apply Ideal.Quotient.eq.mpr
  refine ⟨-j, ?_⟩
  ext <;> simp [j]

@[ega "0 18.2.8" "partial"]
private lemma conormalPushoutMap_surjective
    {B A M : Type u} [CommRing B] [CommRing A] [Algebra B A]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower B A M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    (φ : RingHom.ker (algebraMap B A) →ₗ[B] M)
    (h : Function.Surjective (algebraMap B A)) :
    Function.Surjective (conormalPushoutMap φ) := by
  intro a
  obtain ⟨b, rfl⟩ := h a
  exact ⟨Ideal.Quotient.mk _ (inl b), rfl⟩

@[ega "0 18.2.8" "partial"]
private lemma conormalPushoutMap_square_zero
    {B A M : Type u} [CommRing B] [CommRing A] [Algebra B A]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower B A M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    (φ : RingHom.ker (algebraMap B A) →ₗ[B] M) :
    RingHom.ker (conormalPushoutMap φ) ^ 2 = ⊥ := by
  apply le_antisymm _ bot_le
  rw [pow_two, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨m, hm⟩ := conormalPushoutInclusion_surjective φ ⟨x, hx⟩
  obtain ⟨n, hn⟩ := conormalPushoutInclusion_surjective φ ⟨y, hy⟩
  change x * y = 0
  calc
    x * y = Ideal.Quotient.mk _ (inr m) * Ideal.Quotient.mk _ (inr n) :=
      congrArg₂ (· * ·) (congrArg Subtype.val hm).symm (congrArg Subtype.val hn).symm
    _ = 0 := by rw [← map_mul, inr_mul_inr, map_zero]

private noncomputable def conormalPushoutKernelEquiv
    {B A M : Type u} [CommRing B] [CommRing A] [Algebra B A]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower B A M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    (φ : RingHom.ker (algebraMap B A) →ₗ[B] M) :
    RingHom.ker (conormalPushoutMap φ) ≃ₗ[B] M :=
  (LinearEquiv.ofBijective (conormalPushoutInclusion φ)
    ⟨conormalPushoutInclusion_injective φ, conormalPushoutInclusion_surjective φ⟩).symm

private lemma conormalPushoutKernelEquiv_inclusion
    {B A M : Type u} [CommRing B] [CommRing A] [Algebra B A]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower B A M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    (φ : RingHom.ker (algebraMap B A) →ₗ[B] M) (m : M) :
    conormalPushoutKernelEquiv φ (conormalPushoutInclusion φ m) = m :=
  (LinearEquiv.ofBijective (conormalPushoutInclusion φ)
    ⟨conormalPushoutInclusion_injective φ,
      conormalPushoutInclusion_surjective φ⟩).symm_apply_apply m

private lemma conormalPushoutKernel_compat
    {B A M : Type u} [CommRing B] [CommRing A] [Algebra B A]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower B A M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    (φ : RingHom.ker (algebraMap B A) →ₗ[B] M) :
    letI := (conormalPushoutKernelEquiv φ).toAddEquiv.module A
    ∀ c (x : RingHom.ker (conormalPushoutMap φ)),
      (conormalPushoutMap φ c) • x = c • x := by
  let e := conormalPushoutKernelEquiv φ
  let := e.toAddEquiv.module A
  intro c x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective c
  change (algebraMap B A z.fst) • x = _
  rw [linearEquiv_transportModule_compat e z.fst x]
  obtain ⟨m, rfl⟩ := conormalPushoutInclusion_surjective φ x
  apply Subtype.ext
  let J := conormalGraphIdeal (RingHom.ker (algebraMap B A)) φ (ker_smul_eq_zero (A := A))
  change z.fst • Ideal.Quotient.mk J (inr m) =
    Ideal.Quotient.mk J z * Ideal.Quotient.mk J (inr m)
  calc
    z.fst • Ideal.Quotient.mk J (inr m) = Ideal.Quotient.mk J (z.fst • inr m) :=
      (map_smul (Ideal.Quotient.mkₐ B J) z.fst (inr m)).symm
    _ = Ideal.Quotient.mk J (z * inr m) := by
      congr 1
      ext <;> simp
    _ = _ := map_mul _ _ _

private lemma conormalPushoutInclusion_relation
    {B A M : Type u} [CommRing B] [CommRing A] [Algebra B A]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower B A M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    (φ : RingHom.ker (algebraMap B A) →ₗ[B] M)
    (j : RingHom.ker (algebraMap B A)) :
    (conormalPushoutInclusion φ (φ j) :
      TrivSqZeroExt B M ⧸ conormalGraphIdeal _ φ (ker_smul_eq_zero (A := A))) =
      algebraMap B _ j := by
  change Ideal.Quotient.mk _ (TrivSqZeroExt.inr (φ j)) =
    Ideal.Quotient.mk _ (TrivSqZeroExt.inl (j : B))
  apply Ideal.Quotient.eq.mpr
  refine ⟨-j, ?_⟩
  ext <;> simp

end SquareZeroPushout

/-! ### Comparison of the derived tensor product with derived extension of scalars -/

section DerivedBaseChange

open CategoryTheory.MonoidalCategory CategoryTheory.Functor

private noncomputable def extensionUnderlyingIso
    {A k : Type u} [CommRing A] [CommRing k] [Algebra A k] :
    tensorLeft (ModuleCat.of A k) ≅
      ModuleCat.extendScalars.{u, u, u} (algebraMap A k) ⋙
        ModuleCat.restrictScalars.{u, u, u} (algebraMap A k) :=
  NatIso.ofComponents (fun M => by
    let N := (ModuleCat.restrictScalars.{u, u, u} (algebraMap A k)).obj (ModuleCat.of k k)
    let eN : k ≃ₗ[A] N := {
      toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => Algebra.smul_def r x }
    let e := TensorProduct.congr eN (LinearEquiv.refl A M)
    refine {
      hom := ModuleCat.ofHom (X := (tensorLeft (ModuleCat.of A k)).obj M)
        (Y := (ModuleCat.restrictScalars (algebraMap A k)).obj
          ((ModuleCat.extendScalars (algebraMap A k)).obj M)) {
        toFun := e
        map_add' := e.map_add
        map_smul' := e.map_smul }
      inv := ModuleCat.ofHom (Y := (tensorLeft (ModuleCat.of A k)).obj M)
        (X := (ModuleCat.restrictScalars (algebraMap A k)).obj
          ((ModuleCat.extendScalars (algebraMap A k)).obj M)) {
        toFun := e.symm
        map_add' := e.symm.map_add
        map_smul' := e.symm.map_smul }
      hom_inv_id := by ext x; exact e.symm_apply_apply x
      inv_hom_id := by ext x; exact e.apply_symm_apply x }) (by
      intro M N f
      ext : 1
      apply TensorProduct.ext'
      intro a m
      rfl)

private noncomputable def singleTensorNatIso
    {A : Type u} [CommRing A] (N : ModuleCat.{u} A) :
    TleftCochain ((CochainComplex.singleFunctor _ 0).obj N) ≅
      (tensorLeft N).mapHomologicalComplex (.up ℤ) :=
  (NatIso.ofComponents (fun K => (TotalTensorComplex.SingleTensor.singleTensorIso N K).symm)
    (fun f => (TotalTensorComplex.SingleTensor.singleTensorIso_naturality N f).symm)).symm

private noncomputable def tensorExtensionComplexIso
    {A k : Type u} [CommRing A] [CommRing k] [Algebra A k] :
    complexTensorRight A ((CochainComplex.singleFunctor _ 0).obj (ModuleCat.of A k)) ≅
      CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral.{u, u, u}
        (algebraMap A k) ⋙
          (ModuleCat.restrictScalars.{u, u, u} (algebraMap A k)).mapDerivedCategory := by
  let e := (singleTensorNatIso (ModuleCat.of A k)) ≪≫
    NatIso.mapHomologicalComplex (extensionUnderlyingIso (A := A) (k := k)) (.up ℤ)
  exact isoWhiskerRight e DerivedCategory.Q ≪≫
    isoWhiskerLeft
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap A k)).mapHomologicalComplex (.up ℤ))
      (ModuleCat.restrictScalars.{u, u, u} (algebraMap A k)).mapDerivedCategoryFactors.symm ≪≫
    (Functor.associator _ _ _).symm

private noncomputable def derivedTensorExtensionIso
    {A k : Type u} [CommRing A] [CommRing k] [Algebra A k]
    (T : DerivedTensorProduct A) :
    T.tensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A k)) ≅
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A k)).functor ⋙
      (ModuleCat.restrictScalars.{u, u, u} (algebraMap A k)).mapDerivedCategory := by
  let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A k)
  let B := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A k)
  let U := (ModuleCat.restrictScalars.{u, u, u} (algebraMap A k)).mapDerivedCategory
  let cmp : DerivedCategory.Q ⋙ B.functor ⟶
      CochainComplex.extendScalarsLarge (algebraMap A k) ⋙ DerivedCategory.Q := B.comparison
  let β := (Functor.associator DerivedCategory.Q B.functor U).inv ≫ whiskerRight cmp U
  let : B.functor.IsLeftDerivedFunctor cmp
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)) := B.isLeftDerived
  let : (B.functor ⋙ U).IsLeftDerivedFunctor β
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)) :=
    CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_extension_postcomp
      (algebraMap A k) B.functor cmp U
  let : (T.tensor.obj (DerivedCategory.Q.obj K)).IsLeftDerivedFunctor
      (T.comparison_right K) (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)) :=
    T.isLeftDerived_right K
  exact (T.braiding.app _).symm ≪≫
    Functor.leftDerivedNatIso (T.tensor.obj (DerivedCategory.Q.obj K)) (B.functor ⋙ U)
      (T.comparison_right K) β (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ))
      tensorExtensionComplexIso

private noncomputable def mapDerivedCategoryHomologyIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F] (n : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n ≅
      DerivedCategory.homologyFunctor C n ⋙ F := by
  let e : F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor D (.up ℤ) n ≅
      HomologicalComplex.homologyFunctor C (.up ℤ) n ⋙ F :=
    NatIso.ofComponents (fun K => (K.sc n).mapHomologyIso F) (fun f =>
      ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor C (.up ℤ) n).map f) F)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
    (DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n))
    (DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor C n ⋙ F)) _ _
    (isoWhiskerRight F.mapDerivedCategoryFactors (DerivedCategory.homologyFunctor D n) ≪≫
      isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.homologyFunctorFactors D n) ≪≫ e ≪≫
      isoWhiskerRight (DerivedCategory.homologyFunctorFactors C n).symm F)

/-- The comparison of derived fibres, followed by the homology comparison for restriction. -/
private noncomputable def derivedTensorHomologyIso
    {A k : Type u} [CommRing A] [CommRing k] [Algebra A k]
    (T : DerivedTensorProduct A) (n : ℤ) :
    T.tensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A k)) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) n ≅
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A k)).functor ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) n ⋙
        ModuleCat.restrictScalars.{u, u, u} (algebraMap A k) :=
  isoWhiskerRight (derivedTensorExtensionIso (k := k) T)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n) ≪≫
    isoWhiskerLeft _ (mapDerivedCategoryHomologyIso _ n)

/-- A morphism property respecting isos holds on both sides of the derived fibre comparison. -/
private lemma derivedTensor_map_iff_extension
    {A k : Type u} [CommRing A] [CommRing k] [Algebra A k]
    (T : DerivedTensorProduct A)
    {E F : DerivedCategory (ModuleCat.{u} A)} (ξ : E ⟶ F) (n : ℤ)
    (P : MorphismProperty (ModuleCat.{u} A)) [P.RespectsIso] :
    P ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        ((T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A k))).map ξ)) ↔
    P ((ModuleCat.restrictScalars.{u, u, u} (algebraMap A k)).map
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).map
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A k)).functor.map ξ))) :=
  P.arrow_iso_iff (f := Arrow.mk _) (g := Arrow.mk _)
    (Arrow.isoMk ((derivedTensorHomologyIso T n).app E)
      ((derivedTensorHomologyIso T n).app F) ((derivedTensorHomologyIso T n).hom.naturality ξ).symm)

private lemma derivedTensor_surjective_iff_extension
    {A k : Type u} [CommRing A] [CommRing k] [Algebra A k]
    (T : DerivedTensorProduct A)
    {E F : DerivedCategory (ModuleCat.{u} A)} (ξ : E ⟶ F) (n : ℤ) :
    Function.Surjective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        ((T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A k))).map ξ)) ↔
    Function.Surjective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).map
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A k)).functor.map ξ)) := by
  rw [← ModuleCat.epi_iff_surjective]
  exact (derivedTensor_map_iff_extension (k := k) T ξ n (.epimorphisms _)).trans
    (ModuleCat.epi_iff_surjective _)

private lemma derivedTensor_injective_iff_extension
    {A k : Type u} [CommRing A] [CommRing k] [Algebra A k]
    (T : DerivedTensorProduct A)
    {E F : DerivedCategory (ModuleCat.{u} A)} (ξ : E ⟶ F) (n : ℤ) :
    Function.Injective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        ((T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A k))).map ξ)) ↔
    Function.Injective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).map
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A k)).functor.map ξ)) := by
  rw [← ModuleCat.mono_iff_injective]
  exact (derivedTensor_map_iff_extension (k := k) T ξ n (.monomorphisms _)).trans
    (ModuleCat.mono_iff_injective _)

/-- The derived fibre `E ⊗ᴸ_A k` computed through a chosen derived tensor product
`Deformation.Artin.DerivedTensorProduct` and the derived fibre computed as the total derived
extension of scalars along `A ⟶ k` have the same cohomology, naturally in `E`: a morphism `ξ`
induces a surjection on `H^n` of one exactly when it does on `H^n` of the other.

This is the comparison of the two presentations of the derived fibre used in the Artin
obstruction-theory chapter. Stacks 07YL and Stacks 07YM state their cohomological hypotheses
through a `DerivedTensorProduct` supplied as data, whereas the duality of Stacks 07YK is
available for the total derived extension of scalars; this identifies the two, so that a
hypothesis in either shape may be used with the other's consequences. Its proof is
`Deformation.Artin.derivedTensorExtensionIso`: both functors are total left derived functors
of the same comparison of complexes, hence naturally isomorphic, and the homology of the
restriction of scalars is the restriction of scalars of the homology. -/
public alias surjective_derivedTensorFibre_iff_surjective_derivedExtensionScalars :=
  derivedTensor_surjective_iff_extension

/-- The injective counterpart of
`Deformation.Artin.surjective_derivedTensorFibre_iff_surjective_derivedExtensionScalars`: the
derived fibre computed through a chosen derived tensor product and the derived fibre computed
as the total derived extension of scalars along `A ⟶ k` agree on injectivity of the map
induced on `H^n` by a morphism `ξ`. Condition (2) of Stacks 07YM in degree `0` is an
injectivity, so this is the form in which that half of the condition passes between the two
presentations. -/
public alias injective_derivedTensorFibre_iff_injective_derivedExtensionScalars :=
  derivedTensor_injective_iff_extension

private lemma exists_nonzero_ext_annihilating
    {A k : Type u} [CommRing A] [Field k] [Algebra A k]
    (E F : DerivedCategory.Minus (ModuleCat.{u} A)) (ξ : E.1 ⟶ F.1)
    (hξ : ¬ Function.Surjective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (-1)).map
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A k)).functor.map ξ))) :
    ∃ α : DerivedCategory.Ext F.1
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          ((ModuleCat.restrictScalars (algebraMap A k)).obj
            (ModuleCat.of k (ULift.{u} k)))) 1,
      α ≠ 0 ∧ ξ ≫ α = 0 := by
  let B := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A k)
  let g := (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (-1)).map (B.functor.map ξ)
  obtain ⟨ψ, hψ, hψg⟩ := exists_nonzero_linearFunctional_annihilating_range g.hom hξ
  let φ := ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp ψ)
  let e := DerivedCategory.extIntoFieldEquivDualBaseChangeHomology.{u, u, u} (algebraMap A k) F 1
  refine ⟨e.symm φ, ?_, ?_⟩
  · intro h
    apply hψ
    have hz : φ = 0 := by simpa using congrArg e h
    ext x
    exact congrArg ULift.down (LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hz) x)
  · apply (DerivedCategory.extIntoFieldEquivDualBaseChangeHomology.{u, u, u}
      (algebraMap A k) E 1).injective
    rw [DerivedCategory.extIntoFieldEquivDualBaseChangeHomology_naturality, map_zero]
    change g ≫ (e (e.symm φ)) = 0
    rw [e.apply_symm_apply]
    exact ModuleCat.hom_ext (LinearMap.ext fun x => congrArg ULift.up (LinearMap.congr_fun hψg x))

/-! ### Two-term complexes in cohomological degrees `-1` and `0` -/

private lemma derivedDouble_isLE
    {A : Type u} [CommRing A] {M N : ModuleCat.{u} A} (d : M ⟶ N) :
    (DerivedCategory.Q.obj (HomologicalComplex.double d upIntRelNegOneZero)).IsLE 0 := by
  let K : CochainComplex (ModuleCat.{u} A) ℤ := HomologicalComplex.double d upIntRelNegOneZero
  have : K.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact HomologicalComplex.isZero_double_X d upIntRelNegOneZero i (by omega) (by omega)
  infer_instance

private lemma Q_map_surjective_from_double_to_single
    {A : Type u} [CommRing A] {M N P : ModuleCat.{u} A} (d : M ⟶ N)
    [Projective N] :
    Function.Surjective (fun f : HomologicalComplex.double d upIntRelNegOneZero ⟶
        (CochainComplex.singleFunctor _ (-1)).obj P => DerivedCategory.Q.map f) := by
  let K : CochainComplex (ModuleCat.{u} A) ℤ := HomologicalComplex.double d upIntRelNegOneZero
  let L := (CochainComplex.singleFunctor (ModuleCat.{u} A) (-1)).obj P
  have hK : ∀ i, 0 < i → Limits.IsZero (K.X i) := fun i hi =>
    HomologicalComplex.isZero_double_X d upIntRelNegOneZero i (by omega) (by omega)
  have hK₀ : Projective (K.X 0) :=
    Projective.of_iso
      (HomologicalComplex.doubleXIso₁ d upIntRelNegOneZero (by omega)).symm inferInstance
  have hL : ∀ i ≤ (-2 : ℤ), Limits.IsZero (L.X i) := fun i hi =>
    HomologicalComplex.isZero_single_obj_X (.up ℤ) (-1) P i (by omega)
  intro α
  obtain ⟨f, hf⟩ := (TwoTermComplexExt.toHomD_bijective K L hK hK₀ hL).surjective α
  exact ⟨Quot.out f, (TwoTermComplexExt.toHomD_quotient_map (Quot.out f)).symm.trans
    ((congrArg TwoTermComplexExt.toHomD (HomotopyCategory.quotient_map_out f)).trans hf)⟩

/-- The morphism from the two-term complex of `d : M ⟶ N`, placed in cohomological degrees
`-1` and `0`, to the single complex `P[1]`, induced by a map `φ : M ⟶ P` out of the
degree `-1` term. -/
private noncomputable def doubleToSingle
    {A : Type u} [CommRing A] {M N P : ModuleCat.{u} A} (d : M ⟶ N) (φ : M ⟶ P) :
    HomologicalComplex.double d upIntRelNegOneZero ⟶ (CochainComplex.singleFunctor _ (-1)).obj P :=
  HomologicalComplex.mkHomToSingle
    ((HomologicalComplex.doubleXIso₀ d upIntRelNegOneZero).hom ≫ φ)
    (by
      intro i hi
      rw [HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by
        change i + 1 = -1 at hi
        omega)]
      simp)

private lemma Q_doubleToSingle_surjective
    {A : Type u} [CommRing A] {M N P : ModuleCat.{u} A} (d : M ⟶ N)
    [Projective N] :
    Function.Surjective (fun φ : M ⟶ P => DerivedCategory.Q.map (doubleToSingle d φ)) := by
  intro α
  obtain ⟨f, hf⟩ := Q_map_surjective_from_double_to_single d α
  let φ := (HomologicalComplex.doubleXIso₀ d upIntRelNegOneZero).inv ≫
    f.f (-1) ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) (-1) P).hom
  refine ⟨φ, ?_⟩
  have he : doubleToSingle d φ = f := by
    apply HomologicalComplex.Hom.ext
    funext i
    by_cases hi : i = -1
    · subst i
      simp [doubleToSingle, HomologicalComplex.mkHomToSingle_f, φ]
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) (-1) P i hi).eq_of_tgt _ _
  exact (congrArg DerivedCategory.Q.map he).trans hf

private lemma Q_doubleToSingle_comp_eq_zero
    {A : Type u} [CommRing A] {M N P : ModuleCat.{u} A}
    (d : M ⟶ N) (β : N ⟶ P) :
    DerivedCategory.Q.map (doubleToSingle d (d ≫ β)) = 0 := by
  classical
  let K := HomologicalComplex.double d upIntRelNegOneZero
  let L := (CochainComplex.singleFunctor (ModuleCat.{u} A) (-1)).obj P
  let h0 : K.X 0 ⟶ L.X (-1) :=
    (HomologicalComplex.doubleXIso₁ d upIntRelNegOneZero (by omega)).hom ≫ β ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) (-1) P).inv
  let hom : ∀ i j, K.X i ⟶ L.X j := fun i j =>
    if hi : i = 0 then if hj : j = -1 then
      eqToHom (by rw [hi]) ≫ h0 ≫ eqToHom (by rw [hj]) else 0 else 0
  have h : Homotopy (doubleToSingle d (d ≫ β)) 0 := by
    refine ⟨hom, ?_, ?_⟩
    · intro i j hij
      dsimp [hom]
      split_ifs with hi hj
      · subst i j
        exact (hij rfl).elim
      all_goals rfl
    · intro i
      rw [dNext_eq hom (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
        prevD_eq hom (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]
      by_cases hi : i = -1
      · subst i
        simp [doubleToSingle, hom, h0, K, HomologicalComplex.double_d, Category.assoc]
      · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) (-1) P i hi).eq_of_tgt _ _
  exact (DerivedCategory.Q_map_eq_of_homotopy (h := h)).trans (Functor.map_zero _ _ _)

end DerivedBaseChange

/-! ### The naive cotangent complex of a square-zero extension -/

section RelativeComparison

private noncomputable def nlBaseChainMap
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    {P : Algebra.Extension.{u} R A} {Q : Algebra.Extension.{u} S A}
    (f : P.Hom Q) :
    NaiveCotangent.ChainMap (NaiveCotangent.nlOfExtension P)
      (NaiveCotangent.nlOfExtension Q) where
  f₁ := Algebra.Extension.Cotangent.map f
  f₀ := Algebra.Extension.CotangentSpace.map f
  comm := by
    ext x
    exact (Algebra.Extension.CotangentSpace.map_cotangentComplex f x).symm

private lemma nlBaseChainMap_homotopic
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    {P : Algebra.Extension.{u} R A} {Q : Algebra.Extension.{u} S A}
    (f g : P.Hom Q) : NaiveCotangent.Homotopic (nlBaseChainMap f) (nlBaseChainMap g) :=
  ⟨Algebra.Extension.Hom.sub f g,
    Algebra.Extension.Cotangent.map_sub_map f g,
    Algebra.Extension.CotangentSpace.map_sub_map f g⟩

private lemma nlBaseChainMap_id
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (P : Algebra.Extension.{u} R A) :
    nlBaseChainMap (Algebra.Extension.Hom.id P) =
      NaiveCotangent.ChainMap.id (NaiveCotangent.nlOfExtension P) :=
  NaiveCotangent.ChainMap.ext Algebra.Extension.Cotangent.map_id
    Algebra.Extension.CotangentSpace.map_id

private lemma nlBaseChainMap_comp
    {R S T A : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra R A] [Algebra S A] [Algebra T A]
    [IsScalarTower R S A] [IsScalarTower S T A] [IsScalarTower R T A]
    {P : Algebra.Extension.{u} R A} {Q : Algebra.Extension.{u} S A}
    {V : Algebra.Extension.{u} T A} (f : P.Hom Q) (g : Q.Hom V) :
    nlBaseChainMap (g.comp f) = (nlBaseChainMap g).comp (nlBaseChainMap f) :=
  NaiveCotangent.ChainMap.ext (Algebra.Extension.Cotangent.map_comp _ f g)
    (Algebra.Extension.CotangentSpace.map_comp f g)

/-- The tautological extension attached to a surjection `S → A` has subsingleton cotangent
space: its ring is `S` and `Ω[S⁄S] = 0`. -/
private lemma subsingleton_cotangentSpace_tautological
    {S A : Type u} [CommRing S] [CommRing A] [Algebra S A]
    (h : Function.Surjective (algebraMap S A)) :
    Subsingleton (tautologicalExtension h).CotangentSpace := by
  have hΩ : Subsingleton (Ω[(tautologicalExtension h).Ring⁄S]) :=
    KaehlerDifferential.subsingleton_of_surjective S S Function.surjective_id
  unfold Algebra.Extension.CotangentSpace
  infer_instance

/-- The canonical presentation of `A` over `S` receives a morphism of extensions from the
tautological extension of a surjection `S → A`, namely the structure map of the polynomial
ring. -/
private noncomputable def homTautologicalToSelf
    {S A : Type u} [CommRing S] [CommRing A] [Algebra S A]
    (h : Function.Surjective (algebraMap S A)) :
    (tautologicalExtension h).Hom (Algebra.Generators.self S A).toExtension :=
  Algebra.Extension.Hom.ofAlgHom
    (Algebra.ofId S (Algebra.Generators.self S A).toExtension.Ring) (by ext)

/-- For a surjection `S → A`, the comparison from the naive cotangent complex of the canonical
presentation of `A` over `S` to that of the tautological extension is a homotopy
equivalence. -/
private lemma nlBaseChainMap_defaultHom_isHomotopyEquiv
    {S A : Type u} [CommRing S] [CommRing A] [Algebra S A]
    (h : Function.Surjective (algebraMap S A)) :
    NaiveCotangent.IsHomotopyEquiv
      (nlBaseChainMap (R := S) (Algebra.Extension.defaultHom S A (tautologicalExtension h))) := by
  refine ⟨nlBaseChainMap (homTautologicalToSelf h), ?_, ?_⟩
  · rw [← nlBaseChainMap_comp, ← nlBaseChainMap_id (Algebra.Generators.self S A).toExtension]
    exact nlBaseChainMap_homotopic _ _
  · rw [← nlBaseChainMap_comp, ← nlBaseChainMap_id (tautologicalExtension h)]
    exact nlBaseChainMap_homotopic _ _

/-- A morphism out of a two-term complex whose degree-`0` term vanishes, into the corresponding
single complex, is an isomorphism as soon as it is one in degree `-1`. -/
private lemma isIso_doubleToSingle
    {A : Type u} [CommRing A] {M N P : ModuleCat.{u} A}
    [Subsingleton N] (d : M ⟶ N) (e : M ≅ P) : IsIso (doubleToSingle d e.hom) := by
  have h : ∀ i, IsIso ((doubleToSingle d e.hom).f i) := by
    intro i
    by_cases hi : i = -1
    · subst i
      simp only [doubleToSingle, HomologicalComplex.mkHomToSingle_f]
      infer_instance
    · apply Limits.IsZero.isIso
      · by_cases hi0 : i = 0
        · subst i
          exact (ModuleCat.isZero_of_subsingleton N).of_iso
            (HomologicalComplex.doubleXIso₁ d upIntRelNegOneZero (by omega))
        · exact HomologicalComplex.isZero_double_X d upIntRelNegOneZero i hi hi0
      · exact HomologicalComplex.isZero_single_obj_X (.up ℤ) (-1) P i hi
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **Stacks Project, Tag 07BP, conormal form.** For a surjection `R → A` whose kernel `I` has
square zero, the cotangent module of the tautological extension `R → A` is `I` itself. -/
private noncomputable def squareZeroCotangentEquiv
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (h : Function.Surjective (algebraMap R A))
    (hI : RingHom.ker (algebraMap R A) ^ 2 = ⊥)
    [Module A (RingHom.ker (algebraMap R A))]
    [IsScalarTower R A (RingHom.ker (algebraMap R A))] :
    (tautologicalExtension h).Cotangent ≃ₗ[A] RingHom.ker (algebraMap R A) := by
  let P := tautologicalExtension h
  let : Module A P.ker := inferInstanceAs (Module A (RingHom.ker (algebraMap R A)))
  let : IsScalarTower R A P.ker :=
    inferInstanceAs (IsScalarTower R A (RingHom.ker (algebraMap R A)))
  let e : P.ker ≃ₗ[R] P.Cotangent := LinearEquiv.ofBijective
    (Algebra.Extension.Cotangent.mk (P := P)) ⟨?_, Algebra.Extension.Cotangent.mk_surjective⟩
  · exact (LinearEquiv.extendScalarsOfSurjective h e).symm
  · intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hz := (Algebra.Extension.Cotangent.mk_eq_mk_iff_sub_mem x y).mp hxy
    have hI' : P.ker ^ 2 = ⊥ := hI
    rwa [hI', Submodule.mem_bot] at hz

/-- `squareZeroCotangentEquiv` sends the conormal class of an element of the kernel to the
element itself. -/
private lemma squareZeroCotangentEquiv_mk
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (h : Function.Surjective (algebraMap R A))
    (hI : RingHom.ker (algebraMap R A) ^ 2 = ⊥)
    [Module A (RingHom.ker (algebraMap R A))]
    [IsScalarTower R A (RingHom.ker (algebraMap R A))]
    (x : RingHom.ker (algebraMap R A)) :
    squareZeroCotangentEquiv h hI (Algebra.Extension.Cotangent.mk x) = x := by
  unfold squareZeroCotangentEquiv
  apply LinearEquiv.symm_apply_apply

private lemma baseChange_toKaehler_bijective_of_nonzero
    {R A k : Type u} [CommRing R] [CommRing A] [Field k]
    [Algebra R A] [Algebra A k] [Algebra.IsEpi A k]
    (P W : Algebra.Extension.{u} R A) (f : P.Hom W)
    (N : ModuleCat.{u} A) (eW : W.Cotangent ≃ₗ[A] N) (eN : N ≃ₗ[A] k)
    (h : DerivedCategory.Q.map (doubleToSingle (ModuleCat.ofHom P.cotangentComplex)
      (ModuleCat.ofHom (eW.toLinearMap.comp (Algebra.Extension.Cotangent.map f)))) ≠ 0) :
    Function.Bijective (W.toKaehler.baseChange k) := by
  have hd : W.cotangentComplex.baseChange k = 0 := by
    apply baseChange_eq_zero_of_no_retraction (eW.trans eN)
    rintro ⟨β, hβ⟩
    let γ := eN.symm.toLinearMap.comp β
    have hf : eW.toLinearMap.comp (Algebra.Extension.Cotangent.map f) =
        (γ.comp (Algebra.Extension.CotangentSpace.map f)).comp P.cotangentComplex := by
      apply LinearMap.ext
      intro x
      apply eN.injective
      have hx := LinearMap.congr_fun hβ (Algebra.Extension.Cotangent.map f x)
      dsimp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply] at hx ⊢
      dsimp only [γ, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [eN.apply_symm_apply, Algebra.Extension.CotangentSpace.map_cotangentComplex]
      exact hx.symm
    rw [hf] at h
    exact h <| Q_doubleToSingle_comp_eq_zero (ModuleCat.ofHom P.cotangentComplex)
      (ModuleCat.ofHom (γ.comp (Algebra.Extension.CotangentSpace.map f)))
  exact lTensor_bijective_of_exact_of_zero W.cotangentComplex W.toKaehler
    W.exact_cotangentComplex_toKaehler W.toKaehler_surjective
    (LinearMap.ext (fun x => LinearMap.congr_fun hd x))

end RelativeComparison

private lemma naiveCotangentBaseMap_comp_squareZero
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    (h : Function.Surjective (algebraMap S A))
    (hI : RingHom.ker (algebraMap S A) ^ 2 = ⊥)
    [Module A (RingHom.ker (algebraMap S A))]
    [IsScalarTower S A (RingHom.ker (algebraMap S A))]
    (N : ModuleCat.{u} A) (eI : RingHom.ker (algebraMap S A) ≃ₗ[A] N)
    (f : (Algebra.Generators.self R A).toExtension.Hom (tautologicalExtension h)) :
    ∃ e : derivedNaiveCotangentComplex S A ≅
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ (-1)).obj N),
      naiveCotangentBaseMap R S A ≫ e.hom =
        DerivedCategory.Q.map (doubleToSingle
          (ModuleCat.ofHom (Algebra.Generators.self R A).toExtension.cotangentComplex)
          (ModuleCat.ofHom ((eI.trans (LinearEquiv.refl A N)).toLinearMap.comp
            ((squareZeroCotangentEquiv h hI).toLinearMap.comp
              (Algebra.Extension.Cotangent.map f))))) := by
  let P := (Algebra.Generators.self R A).toExtension
  let Q := (Algebra.Generators.self S A).toExtension
  let V := tautologicalExtension h
  let c : Q.Hom V := Algebra.Extension.defaultHom S A V
  let g : P.Hom Q := ((Algebra.Generators.self R A).defaultHom
    (Algebra.Generators.self S A)).toExtensionHom
  let eV := (squareZeroCotangentEquiv h hI).trans eI
  have hc : IsIso (DerivedCategory.Q.map (twoTermHom (nlBaseChainMap c))) :=
    isIso_Q_map_twoTermHom (nlBaseChainMap_defaultHom_isHomotopyEquiv h)
  have hV : Subsingleton V.CotangentSpace := subsingleton_cotangentSpace_tautological h
  let b := doubleToSingle (ModuleCat.ofHom V.cotangentComplex) eV.toModuleIso.hom
  have hb : IsIso b := isIso_doubleToSingle _ eV.toModuleIso
  let e := (@asIso _ _ _ _ (DerivedCategory.Q.map (twoTermHom (nlBaseChainMap c))) hc) ≪≫
    DerivedCategory.Q.mapIso (@asIso _ _ _ _ b hb)
  refine ⟨e, ?_⟩
  have key : DerivedCategory.Q.map (twoTermHom (nlBaseChainMap g)) ≫
      (DerivedCategory.Q.map (twoTermHom (nlBaseChainMap c)) ≫ DerivedCategory.Q.map b) =
      DerivedCategory.Q.map (doubleToSingle (ModuleCat.ofHom P.cotangentComplex)
        (ModuleCat.ofHom ((eI.trans (LinearEquiv.refl A N)).toLinearMap.comp
          ((squareZeroCotangentEquiv h hI).toLinearMap.comp
            (Algebra.Extension.Cotangent.map f))))) := by
    rw [← Category.assoc, ← Functor.map_comp, ← twoTermHom_comp,
      ← nlBaseChainMap_comp, Q_map_twoTermHom_eq_of_homotopic
        (nlBaseChainMap_homotopic (c.comp g) f),
      ← DerivedCategory.Q.map_comp (twoTermHom (nlBaseChainMap f)) b]
    congr 1
    apply HomologicalComplex.from_double_hom_ext
    · rw [HomologicalComplex.comp_f, twoTermHom_f_neg_one]
      simp [doubleToSingle, b, eV, nlBaseChainMap, Category.assoc]
      rfl
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) (-1) N 0 (by omega)).eq_of_tgt _ _
  exact key

/-! ### Transfer of differentials along a quotient -/

/-- For a tower `Λ → A' → A → k` with `A' → A` surjective, the base-change map of
differentials `k ⊗_{A'} Ω_{A'/Λ} ⟶ k ⊗_A Ω_{A/Λ}` is surjective.

This is `KaehlerDifferential.mapBaseChange_surjective` after base change to `k`; no hypothesis
on the kernel of `A' → A` is needed. -/
public theorem differentialsBaseChangeMap_surjective
    (R A' A k : Type u) [CommRing R] [CommRing A'] [CommRing A] [CommRing k]
    [Algebra R A'] [Algebra R A] [Algebra A' A] [Algebra A k] [Algebra A' k]
    [Algebra R k] [IsScalarTower R A' A] [IsScalarTower R A k]
    [IsScalarTower R A' k] [IsScalarTower A' A k]
    (h : Function.Surjective (algebraMap A' A)) :
    Function.Surjective (differentialsBaseChangeMap R A' A k) := by
  unfold differentialsBaseChangeMap
  exact (LinearMap.baseChange_surjective k
    (KaehlerDifferential.mapBaseChange_surjective R A' A h)).comp
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A' A k k
      (KaehlerDifferential R A')).symm.surjective

/-- An element of the square of the kernel of `B → k` has vanishing differential in
`k ⊗_B Ω_{B/Λ}`: by the Leibniz rule `d (m * n) = m · d n + n · d m`, and each coefficient
`m`, `n` already acts as `0` on `k`. -/
public theorem tmul_D_eq_zero_of_mem_ker_sq
    (Λ : Type u) {B k : Type u} [CommRing Λ] [CommRing B] [CommRing k]
    [Algebra Λ B] [Algebra B k] [Algebra Λ k] (c : k) {x : B}
    (hx : x ∈ RingHom.ker (algebraMap B k) ^ 2) :
    c ⊗ₜ[B] KaehlerDifferential.D Λ B x = (0 : k ⊗[B] KaehlerDifferential Λ B) := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun m hm n hn => ?_) (fun y z hy hz => ?_)
  · have hmc : m • c = 0 := by
      rw [Algebra.smul_def, RingHom.mem_ker.mp hm, zero_mul]
    have hnc : n • c = 0 := by
      rw [Algebra.smul_def, RingHom.mem_ker.mp hn, zero_mul]
    rw [Derivation.leibniz, TensorProduct.tmul_add, ← TensorProduct.smul_tmul,
      ← TensorProduct.smul_tmul, hmc, hnc, TensorProduct.zero_tmul,
      TensorProduct.zero_tmul, add_zero]
  · rw [map_add, TensorProduct.tmul_add, hy, hz, add_zero]

/-- **The quotient transfer of differentials, injectivity.** For a tower `Λ → B → A → k` in
which `B → A` is surjective with kernel contained in the square of the kernel of `B → k`, the
base-change map of differentials `k ⊗_B Ω_{B/Λ} ⟶ k ⊗_A Ω_{A/Λ}` is injective.

The kernel of `A ⊗_B Ω_{B/Λ} ⟶ Ω_{A/Λ}` is the image of the conormal module of `B → A`
(`KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`), so it consists of the
elements `1 ⊗ d x` with `x` in the kernel of `B → A`. Base change to `k` is right exact, so it
takes that exact sequence to an exact one, and the hypothesis on the kernel makes the image of
the conormal module die by `Deformation.Artin.tmul_D_eq_zero_of_mem_ker_sq`. -/
@[ega "0 20.5.12" "(ii)"]
public theorem differentialsBaseChangeMap_injective_of_ker_le_ker_sq
    (Λ B A k : Type u) [CommRing Λ] [CommRing B] [CommRing A] [CommRing k]
    [Algebra Λ B] [Algebra Λ A] [Algebra Λ k] [Algebra B A] [Algebra B k] [Algebra A k]
    [IsScalarTower Λ B A] [IsScalarTower Λ B k] [IsScalarTower Λ A k] [IsScalarTower B A k]
    (h : Function.Surjective (algebraMap B A))
    (hI : RingHom.ker (algebraMap B A) ≤ RingHom.ker (algebraMap B k) ^ 2) :
    Function.Injective (differentialsBaseChangeMap Λ B A k) := by
  set g := KaehlerDifferential.mapBaseChange Λ B A with hg
  have hzero : ∀ u : k ⊗[A] (LinearMap.ker g),
      LinearMap.lTensor (R := A) k (LinearMap.ker g).subtype u = 0 := by
    intro u
    induction u using TensorProduct.inductionOn with
    | add v w hv hw => rw [map_add, hv, hw, add_zero]
    | tmul c z =>
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply]
      obtain ⟨y, hy⟩ := (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange Λ B A h
        (z : A ⊗[B] KaehlerDifferential Λ B)).mp (LinearMap.mem_ker.mp z.2)
      obtain ⟨w, hw⟩ := (RingHom.ker (algebraMap B A)).toCotangent_surjective y
      have hz : (z : A ⊗[B] KaehlerDifferential Λ B) =
          (1 : A) ⊗ₜ[B] KaehlerDifferential.D Λ B (w : B) := by
        rw [← hy, ← hw, KaehlerDifferential.kerCotangentToTensor_toCotangent]
      rw [hz]
      have hcancel : (TensorProduct.AlgebraTensorModule.cancelBaseChange B A k k
          (KaehlerDifferential Λ B)) (c ⊗ₜ[A] ((1 : A) ⊗ₜ[B]
            KaehlerDifferential.D Λ B (w : B))) = 0 := by
        rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
        exact tmul_D_eq_zero_of_mem_ker_sq Λ c (hI w.2)
      exact (TensorProduct.AlgebraTensorModule.cancelBaseChange B A k k
        (KaehlerDifferential Λ B)).map_eq_zero_iff.mp hcancel
  have hzero' : LinearMap.lTensor (R := A) k (LinearMap.ker g).subtype = 0 :=
    LinearMap.ext fun u => (hzero u).trans (LinearMap.zero_apply u).symm
  have hinj : Function.Injective (LinearMap.lTensor (R := A) k g) :=
    LinearMap.ker_eq_bot.mp (by
      rw [(lTensor_exact k (LinearMap.exact_subtype_ker_map g)
        (hg ▸ KaehlerDifferential.mapBaseChange_surjective Λ B A h)).linearMap_ker_eq,
        hzero', LinearMap.range_zero])
  have hbc : Function.Injective (g.baseChange k) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact hinj
  exact hbc.comp (TensorProduct.AlgebraTensorModule.cancelBaseChange B A k k
    (KaehlerDifferential Λ B)).symm.injective

/-- **The quotient transfer of differentials.** For a tower `Λ → B → A → k` in which `B → A`
is surjective with kernel contained in the square of the kernel of `B → k`, the base-change
map of differentials `k ⊗_B Ω_{B/Λ} ⟶ k ⊗_A Ω_{A/Λ}` is bijective: passing to such a quotient
of `B` does not change the differentials over `k`.

Surjectivity is `Deformation.Artin.differentialsBaseChangeMap_surjective` and needs only the
surjectivity of `B → A`; the hypothesis on the kernel enters only through
`Deformation.Artin.differentialsBaseChangeMap_injective_of_ker_le_ker_sq`. -/
public theorem differentialsBaseChangeMap_bijective_of_ker_le_ker_sq
    (Λ B A k : Type u) [CommRing Λ] [CommRing B] [CommRing A] [CommRing k]
    [Algebra Λ B] [Algebra Λ A] [Algebra Λ k] [Algebra B A] [Algebra B k] [Algebra A k]
    [IsScalarTower Λ B A] [IsScalarTower Λ B k] [IsScalarTower Λ A k] [IsScalarTower B A k]
    (h : Function.Surjective (algebraMap B A))
    (hI : RingHom.ker (algebraMap B A) ≤ RingHom.ker (algebraMap B k) ^ 2) :
    Function.Bijective (differentialsBaseChangeMap Λ B A k) :=
  ⟨differentialsBaseChangeMap_injective_of_ker_le_ker_sq Λ B A k h hI,
    differentialsBaseChangeMap_surjective Λ B A k h⟩

/-- **Stacks Project, Tag 07YL.** Let `Λ → A → k = κ(𝔭)` be finite type maps of Noetherian
rings and let `ξ : E ⟶ NL_{A/Λ}` be a morphism in `D⁻(A)` such that `H⁻¹(ξ ⊗ᴸ k)` is not
surjective.  Then there is a surjection of `Λ`-algebras `A' → A` whose kernel `I` has square
zero and is isomorphic to `k` as an `A`-module, which does not change differentials modulo
`𝔭`, and for which the composite of `ξ` with `NL_{A/Λ} ⟶ NL_{A/A'}` vanishes. -/
@[stacks 07YL]
public theorem exists_squareZeroExtension_killing_cotangent_morphism
    (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]
    [IsNoetherianRing Λ] [IsNoetherianRing A] [Algebra.FiniteType Λ A]
    (p : Ideal A) [p.IsPrime] [Algebra.FiniteType A p.ResidueField]
    (T : DerivedTensorProduct A)
    (E : DerivedCategory (ModuleCat.{u} A))
    (hE : (DerivedCategory.TStructure.t
      (C := ModuleCat.{u} A)).minus E)
    (ξ : E ⟶ derivedNaiveCotangentComplex Λ A)
    (hξ : ¬ Function.Surjective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).map
        ((T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A p.ResidueField))).map ξ))) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra Λ A') (_ : Algebra A' A)
      (_ : IsScalarTower Λ A' A),
      Function.Surjective (algebraMap A' A) ∧
      let I := RingHom.ker (algebraMap A' A)
      I ^ 2 = ⊥ ∧
      ∃ (_ : Module A I),
        (∀ (a' : A') (x : I), (algebraMap A' A a') • x = a' • x) ∧
        Nonempty (I ≃ₗ[A] p.ResidueField) ∧
        Function.Bijective (differentialsBaseChangeMap Λ A' A p.ResidueField) ∧
        ξ ≫ naiveCotangentBaseMap Λ A' A = 0 := by
  classical
  let G := Algebra.Generators.self Λ A
  let P := G.toExtension
  have hP : Function.Surjective (algebraMap P.Ring A) := P.algebraMap_surjective
  have hξk := (derivedTensor_surjective_iff_extension (k := p.ResidueField)
    T ξ (-1)).not.mp hξ
  have hNL : (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus
      (derivedNaiveCotangentComplex Λ A) :=
    ⟨0, derivedDouble_isLE (ModuleCat.ofHom P.cotangentComplex)⟩
  obtain ⟨α, hα, hξα⟩ := exists_nonzero_ext_annihilating
    (k := p.ResidueField) ⟨E, hE⟩ ⟨derivedNaiveCotangentComplex Λ A, hNL⟩ ξ hξk
  let N := (ModuleCat.restrictScalars (algebraMap A p.ResidueField)).obj
    (ModuleCat.of p.ResidueField (ULift.{u} p.ResidueField))
  let e := ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso
    1 (-1) 0 (by omega)).app N
  let : Projective (ModuleCat.of A P.CotangentSpace) := inferInstance
  obtain ⟨φ, hφ⟩ := Q_doubleToSingle_surjective (ModuleCat.ofHom P.cotangentComplex)
    (α ≫ e.hom)
  let : Module P.Ring N := Module.compHom N (algebraMap P.Ring A)
  let : IsScalarTower P.Ring A N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : Module P.Ringᵐᵒᵖ N := Module.compHom N
    (RingHom.fromOpposite (RingHom.id P.Ring) (fun _ _ => Commute.all _ _))
  let : IsCentralScalar P.Ring N := ⟨fun _ _ => rfl⟩
  let ψ : RingHom.ker (algebraMap P.Ring A) →ₗ[P.Ring] N :=
    (φ.hom.restrictScalars P.Ring).comp
      (P.cotangentEquivCotangentKer.symm.toLinearMap.comp P.ker.toCotangent)
  let J := conormalGraphIdeal (RingHom.ker (algebraMap P.Ring A)) ψ
    (ker_smul_eq_zero (A := A))
  let A' := TrivSqZeroExt P.Ring N ⧸ J
  let : Algebra A' A := (conormalPushoutMap ψ).toAlgebra
  let : Algebra Λ A' := ((algebraMap P.Ring A').comp (algebraMap Λ P.Ring)).toAlgebra
  let : IsScalarTower Λ A' A := IsScalarTower.of_algebraMap_eq (fun l => by
    change (algebraMap Λ A) l = (algebraMap P.Ring A) ((algebraMap Λ P.Ring) l)
    exact IsScalarTower.algebraMap_apply Λ P.Ring A l)
  refine ⟨A', inferInstance, inferInstance, inferInstance, inferInstance,
    conormalPushoutMap_surjective ψ hP, conormalPushoutMap_square_zero ψ, ?_⟩
  let eI := conormalPushoutKernelEquiv ψ
  let := eI.toAddEquiv.module A
  let eA : RingHom.ker (conormalPushoutMap ψ) ≃ₗ[A] N := {
    __ := eI.toAddEquiv
    map_smul' := fun a x => by
      change eI (eI.symm (a • eI x)) = a • eI x
      exact eI.apply_symm_apply _ }
  let eN : N ≃ₗ[A] p.ResidueField := {
    toFun := ULift.down
    invFun := ULift.up
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun a x => by
      change (algebraMap A p.ResidueField a) * x.down = a • x.down
      exact (Algebra.smul_def a x.down).symm }
  refine ⟨inferInstance, conormalPushoutKernel_compat ψ, ⟨eA.trans eN⟩, ?_⟩
  have hq : Function.Surjective (algebraMap A' A) := conormalPushoutMap_surjective ψ hP
  have hI : RingHom.ker (algebraMap A' A) ^ 2 = ⊥ := conormalPushoutMap_square_zero ψ
  let : IsScalarTower A' A (RingHom.ker (algebraMap A' A)) :=
    IsScalarTower.of_algebraMap_smul (conormalPushoutKernel_compat ψ)
  let V := tautologicalExtension hq
  let f : P.Hom V := {
    toRingHom := algebraMap P.Ring A'
    toRingHom_algebraMap := fun _ => rfl
    algebraMap_toRingHom := fun _ => rfl }
  obtain ⟨τ, hτ⟩ := naiveCotangentBaseMap_comp_squareZero hq hI N eA f
  have heφ : (eA.trans (LinearEquiv.refl A N)).toLinearMap.comp
      ((squareZeroCotangentEquiv hq hI).toLinearMap.comp
        (Algebra.Extension.Cotangent.map f)) = φ.hom := by
    ext x
    obtain ⟨j, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
    have hmk : Algebra.Extension.Cotangent.map f (Algebra.Extension.Cotangent.mk j) =
        Algebra.Extension.Cotangent.mk (conormalPushoutInclusion ψ (ψ j)) := by
      rw [Algebra.Extension.Cotangent.map_mk]
      exact congrArg (fun y => Algebra.Extension.Cotangent.mk y)
        (Subtype.ext (conormalPushoutInclusion_relation ψ j).symm)
    refine Eq.trans (congrArg (fun z => eA ((squareZeroCotangentEquiv hq hI) z)) hmk) ?_
    refine Eq.trans (congrArg (fun z => eA z)
      (squareZeroCotangentEquiv_mk hq hI (conormalPushoutInclusion ψ (ψ j)))) ?_
    exact conormalPushoutKernelEquiv_inclusion ψ (ψ j)
  rw [heφ] at hτ
  have hφ' : DerivedCategory.Q.map (doubleToSingle
      (ModuleCat.ofHom P.cotangentComplex) (ModuleCat.ofHom φ.hom)) = α ≫ e.hom := hφ
  have hvanish : ξ ≫ naiveCotangentBaseMap Λ A' A = 0 := by
    apply (cancel_mono τ.hom).mp
    rw [Category.assoc, hτ, hφ', Limits.zero_comp, ← Category.assoc, hξα, Limits.zero_comp]
  refine ⟨?_, hvanish⟩
  let : Algebra.IsEpi A p.ResidueField := residueField_isEpi p
  let W := Algebra.Extension.ofSurjective (IsScalarTower.toAlgHom Λ A' A) hq
  let fw : P.Hom W := {
    toRingHom := algebraMap P.Ring A'
    toRingHom_algebraMap := fun _ => rfl
    algebraMap_toRingHom := fun _ => rfl }
  let eW : W.Cotangent ≃ₗ[A] N := (squareZeroCotangentEquiv hq hI).trans eA
  have heW : eW.toLinearMap.comp (Algebra.Extension.Cotangent.map fw) = φ.hom := heφ
  have hn : DerivedCategory.Q.map (doubleToSingle (ModuleCat.ofHom P.cotangentComplex)
      (ModuleCat.ofHom (eW.toLinearMap.comp (Algebra.Extension.Cotangent.map fw)))) ≠ 0 := by
    rw [heW]
    intro hz
    have he : α ≫ e.hom = 0 := hφ'.symm.trans hz
    exact hα ((cancel_mono e.hom).mp (by simpa using he))
  exact (baseChange_toKaehler_bijective_of_nonzero P W fw N eW eN hn).comp
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A' A p.ResidueField p.ResidueField
      (KaehlerDifferential Λ A')).symm.bijective

end Deformation.Artin
