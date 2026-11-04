module

public import StacksFrontier.RingTheory.Koszul.Variables.ContractingHomotopy

/-!
# The Koszul resolution of the variables and its tensor contraction

Let `A` be a commutative ring and `E` a linearly ordered type.  This file shows that the Koszul
complex of the variables of `P = A[E]` is a projective resolution of `A` over `P`, proves the
augmented contraction identity in exterior degree zero, and transports the chosen contraction to
the Koszul complex tensored with a power `I ^ n` of the ideal of variables.

## Main definitions

* `MvPolynomial.variableKoszulResolution`: The Koszul complex as a projective resolution of `A`.
* `MvPolynomial.variableKoszulTensorEmbed`: The embedding `K_j ⊗ I ^ n → K_j`.
* `MvPolynomial.koszulTensorContract`: The contraction `K_j ⊗ I ^ (n + 1) → K_(j+1) ⊗ I ^ n`.

## Main results

* `MvPolynomial.variableKoszulChosenContract_homotopy_zero_augmented`: The augmented contraction
  identity in exterior degree zero.
* `MvPolynomial.koszulTensorContract_homotopy`: The homotopy identity on `K_• ⊗ I ^ n`.

## References

* [Stacks Project, Tag 08RE](https://stacks.math.columbia.edu/tag/08RE)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace MvPolynomial

/-- Each term of the Koszul complex of the variables is a projective `A[E]`-module. -/
lemma variableKoszul_term_projective
    (A : Type u) [CommRing A] (E : Type v) (j : ℕ) :
    CategoryTheory.Projective ((Koszul.complex (variableKoszulDual A E)).X j) := by
  show CategoryTheory.Projective
    (ModuleCat.of (MvPolynomial E A) (⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)))
  infer_instance

/-- The Koszul complex of the variables is exact in positive degree: the range of `d (q + 1)`
is the kernel of `d q`. -/
lemma variableKoszul_exact_positive
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (q : ℕ) :
    LinearMap.range (Koszul.d (variableKoszulDual A E) (q + 1)) =
      LinearMap.ker (Koszul.d (variableKoszulDual A E) q) := by
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr (Koszul.d_comp_d _ q)
  · intro x hx
    have hdx : Koszul.d (variableKoszulDual A E) q x = 0 := hx
    have h := variableKoszulChosenContract_homotopy A E q x
    rw [hdx, map_zero, add_zero] at h
    exact ⟨variableKoszulChosenContract A E (q + 1) x, h⟩

/-- The Koszul complex of the variables is exact in every positive degree. -/
lemma variableKoszul_complex_exact_positive
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (q : ℕ) :
    (Koszul.complex (variableKoszulDual A E)).ExactAt (q + 1) := by
  apply (HomologicalComplex.exactAt_iff'
    (Koszul.complex (variableKoszulDual A E)) (i := q + 2) (j := q + 1) (k := q)
    (by simp) (by simp)).2
  apply ShortComplex.Exact.moduleCat_of_range_eq_ker
  simp only [Koszul.complex_d]
  show LinearMap.range (Koszul.d (variableKoszulDual A E) (q + 1)) =
    LinearMap.ker (Koszul.d (variableKoszulDual A E) q)
  exact variableKoszul_exact_positive A E q

/-- The ideal of variables is contained in the kernel of evaluation at `0`. -/
lemma variableIdeal_le_augmentation_ker
    (A : Type u) [CommRing A] (E : Type v) :
    (Ideal.span (Set.range MvPolynomial.X) : Ideal (MvPolynomial E A)) ≤
      RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id A) (0 : E → A)) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨e, rfl⟩
  simp

/-- The kernel of evaluation at `0` is the ideal of variables. -/
lemma augmentation_ker_eq_variableIdeal
    (A : Type u) [CommRing A] (E : Type v) :
    RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id A) (0 : E → A)) =
      (Ideal.span (Set.range MvPolynomial.X) : Ideal (MvPolynomial E A)) := by
  apply le_antisymm
  · intro p hp
    show p ∈ MvPolynomial.idealOfVars E A
    rw [← pow_one (MvPolynomial.idealOfVars E A)]
    apply (MvPolynomial.mem_pow_idealOfVars_iff' 1 p).mpr
    intro x hx
    have hx0 : x = 0 := by
      apply (Finsupp.degree_eq_zero_iff x).mp
      omega
    subst x
    simpa [MvPolynomial.eval₂Hom_zero_apply, MvPolynomial.constantCoeff_eq] using hp
  · exact variableIdeal_le_augmentation_ker A E

/-- The augmentation of the Koszul complex of the variables onto `A`, an `A[E]`-module by
evaluation at `0`: the chain map to `A` in degree zero given by `⋀⁰ ≃ A[E] → A`. -/
noncomputable def variableKoszulAugmentationULift
    (A : Type u) [CommRing A] (E : Type v) :
    let P := MvPolynomial E A
    letI : Algebra P A :=
      (MvPolynomial.eval₂Hom (RingHom.id A) (0 : E → A)).toAlgebra
    Koszul.complex (variableKoszulDual A E) ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} P)).obj
        (ModuleCat.of P (ULift.{v} A)) := by
  let P := MvPolynomial E A
  let f := MvPolynomial.eval₂Hom (RingHom.id A) (0 : E → A)
  letI : Algebra P A := f.toAlgebra
  let g : (⋀[P]^0 (E →₀ P)) →ₗ[P] ULift.{v} A :=
    ULift.moduleEquiv.symm.toLinearMap.comp
      ((Algebra.linearMap P A).comp
        (exteriorPower.zeroEquiv P (E →₀ P)).toLinearMap)
  refine (ChainComplex.toSingle₀Equiv _ _).symm ⟨ModuleCat.ofHom g, ?_⟩
  apply ModuleCat.hom_ext
  ext x
  change (⋀[P]^1 (E →₀ P)) at x
  change f (exteriorPower.zeroEquiv P (E →₀ P)
    (Koszul.d (variableKoszulDual A E) 0 x)) = 0
  apply RingHom.mem_ker.mp
  rw [augmentation_ker_eq_variableIdeal A E]
  have h : exteriorPower.zeroEquiv P (E →₀ P)
      (Koszul.d (variableKoszulDual A E) 0 x) ∈
      Submodule.map
        (exteriorPower.zeroEquiv P (E →₀ P)).toLinearMap
        (LinearMap.range (Koszul.d (variableKoszulDual A E) 0)) := ⟨_, ⟨x, rfl⟩, rfl⟩
  rwa [variableKoszul_range_d_zero] at h

/-- The augmentation `⋀⁰ → A` is surjective. -/
lemma variableKoszulAugmentation_surjective
    (A : Type u) [CommRing A] (E : Type v) :
    let P := MvPolynomial E A
    letI : Algebra P A :=
      (MvPolynomial.eval₂Hom (RingHom.id A) (0 : E → A)).toAlgebra
    Function.Surjective
      (ULift.moduleEquiv.symm.toLinearMap.comp
        ((Algebra.linearMap P A).comp
          (exteriorPower.zeroEquiv P (E →₀ P)).toLinearMap)) := by
  dsimp only
  intro a
  refine ⟨(exteriorPower.zeroEquiv (MvPolynomial E A)
    (E →₀ MvPolynomial E A)).symm (MvPolynomial.C a.down), ?_⟩
  cases a
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Algebra.linearMap_apply,
    ULift.moduleEquiv_symm_apply]
  apply ULift.ext
  show MvPolynomial.eval₂Hom (RingHom.id A) (0 : E → A)
    (MvPolynomial.C _) = _
  simp

/-- The image of the first Koszul differential is the kernel of the augmentation `⋀⁰ → A`. -/
lemma variableKoszulAugmentation_exactAt_zero
    (A : Type u) [CommRing A] (E : Type v) :
    let P := MvPolynomial E A
    letI : Algebra P A :=
      (MvPolynomial.eval₂Hom (RingHom.id A) (0 : E → A)).toAlgebra
    LinearMap.range (Koszul.d (variableKoszulDual A E) 0) =
      LinearMap.ker
        ((ULift.moduleEquiv.symm.toLinearMap : A →ₗ[P] ULift.{v} A).comp
          ((Algebra.linearMap P A).comp
            (exteriorPower.zeroEquiv P (E →₀ P)).toLinearMap)) := by
  let P := MvPolynomial E A
  let f := MvPolynomial.eval₂Hom (RingHom.id A) (0 : E → A)
  let _ : Algebra P A := f.toAlgebra
  let z := exteriorPower.zeroEquiv P (E →₀ P)
  let g : (⋀[P]^0 (E →₀ P)) →ₗ[P] ULift.{v} A :=
    ULift.moduleEquiv.symm.toLinearMap.comp
      ((Algebra.linearMap P A).comp z.toLinearMap)
  have hker : Submodule.map z.toLinearMap (LinearMap.ker g) = RingHom.ker f := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ULift.up (f (z x)) = 0 at hx
      exact RingHom.mem_ker.mpr (congrArg ULift.down hx)
    · intro hp
      refine ⟨z.symm p, ?_, by simp⟩
      show g (z.symm p) = 0
      simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, Algebra.linearMap_apply,
        ULift.moduleEquiv_symm_apply]
      apply ULift.ext
      show f p = 0
      rw [RingHom.mem_ker.mp hp]
  apply Submodule.map_injective_of_injective z.injective
  show Submodule.map z.toLinearMap
      (LinearMap.range (Koszul.d (variableKoszulDual A E) 0)) =
    Submodule.map z.toLinearMap (LinearMap.ker g)
  rw [variableKoszul_range_d_zero, hker,
    augmentation_ker_eq_variableIdeal]

/-- The Koszul complex of the variables, as a projective resolution of `A` over `A[E]`, where
`A` is an `A[E]`-module by evaluation at `0`. -/
noncomputable def variableKoszulResolution
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] :
    let P := MvPolynomial E A
    letI : Algebra P A :=
      (MvPolynomial.eval₂Hom (RingHom.id A) (0 : E → A)).toAlgebra
    ProjectiveResolution (ModuleCat.of P (ULift.{v} A)) := by
  let P := MvPolynomial E A
  letI : Algebra P A :=
    (MvPolynomial.eval₂Hom (RingHom.id A) (0 : E → A)).toAlgebra
  let π := variableKoszulAugmentationULift A E
  refine {
    complex := Koszul.complex (variableKoszulDual A E)
    projective := ?_
    π := π
    quasiIso := ?_ }
  · intro j
    exact variableKoszul_term_projective A E j
  · refine ⟨fun j ↦ ?_⟩
    cases j with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      constructor
      · apply ShortComplex.Exact.moduleCat_of_range_eq_ker
        change LinearMap.range (Koszul.d (variableKoszulDual A E) 0) =
          LinearMap.ker
            ((ULift.moduleEquiv.symm.toLinearMap : A →ₗ[P] ULift.{v} A).comp
              ((Algebra.linearMap P A).comp
                (exteriorPower.zeroEquiv P (E →₀ P)).toLinearMap))
        exact variableKoszulAugmentation_exactAt_zero A E
      · change Epi (ModuleCat.ofHom
          ((ULift.moduleEquiv.symm.toLinearMap : A →ₗ[P] ULift.{v} A).comp
            ((Algebra.linearMap P A).comp
              (exteriorPower.zeroEquiv P (E →₀ P)).toLinearMap)))
        rw [ModuleCat.epi_iff_surjective]
        exact variableKoszulAugmentation_surjective A E
    | succ q =>
      rw [quasiIsoAt_iff_exactAt'
        (hL := ChainComplex.exactAt_succ_single_obj ..)]
      exact variableKoszul_complex_exact_positive A E q

/-- The `A[E]`-linear map `⋀^j ⊗ I ^ n → ⋀^j`, `x ⊗ r ↦ r • x`, where `I` is the ideal of
variables. -/
noncomputable def variableKoszulTensorEmbed
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (j n : ℕ) :
    let P := MvPolynomial E A
    let I : Ideal P := Ideal.span (Set.range MvPolynomial.X)
    ((⋀[P]^j (E →₀ P)) ⊗[P] (I ^ n : Ideal P)) →ₗ[P]
      (⋀[P]^j (E →₀ P)) := by
  let P := MvPolynomial E A
  let I : Ideal P := Ideal.span (Set.range MvPolynomial.X)
  exact (TensorProduct.rid P (⋀[P]^j (E →₀ P))).toLinearMap.comp
    (TensorProduct.map LinearMap.id (I ^ n : Ideal P).subtype)

/-- `variableKoszulTensorEmbed` sends `x ⊗ r` to `r • x`. -/
lemma variableKoszulTensorEmbed_tmul
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (j n : ℕ)
    (x : ⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A))
    (r : (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n :
      Ideal (MvPolynomial E A))) :
    variableKoszulTensorEmbed A E j n (x ⊗ₜ[MvPolynomial E A] r) = (r : MvPolynomial E A) • x := by
  simp [variableKoszulTensorEmbed]

/-- The coordinates of the image of `z` in the basis of `⋀^j` are the coordinates of `z` under
`⋀^j ⊗ I ^ n ≃ (_ →₀ I ^ n)`, regarded as polynomials. -/
lemma variableKoszulTensorEmbed_repr
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (j n : ℕ)
    (z : (⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) ⊗[MvPolynomial E A]
      (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n :
        Ideal (MvPolynomial E A))) :
    let b := (Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower j
    b.repr (variableKoszulTensorEmbed A E j n z) =
      Finsupp.mapRange.linearMap
        (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n :
          Ideal (MvPolynomial E A)).subtype
        (TensorProduct.equivFinsuppOfBasisLeft b z) := by
  classical
  let b := (Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower j
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x r =>
    ext s
    simp [variableKoszulTensorEmbed_tmul, mul_comm]
  | add x y hx hy => simp [map_add, hx, hy]

/-- `variableKoszulTensorEmbed` is injective. -/
lemma variableKoszulTensorEmbed_injective
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (j n : ℕ) :
    Function.Injective (variableKoszulTensorEmbed A E j n) := by
  let b := (Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower j
  intro x y h
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  apply Finsupp.ext
  intro s
  apply Subtype.val_injective
  have hh := congrArg (fun z => b.repr z s) h
  rwa [variableKoszulTensorEmbed_repr, variableKoszulTensorEmbed_repr] at hh

/-- The range of `variableKoszulTensorEmbed` is `I ^ n • ⋀^j`. -/
lemma variableKoszulTensorEmbed_range
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (j n : ℕ) :
    LinearMap.range (variableKoszulTensorEmbed A E j n) =
      (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n) •
        (⊤ : Submodule (MvPolynomial E A)
          (⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A))) := by
  let I : Ideal (MvPolynomial E A) := Ideal.span (Set.range MvPolynomial.X)
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x r =>
      rw [variableKoszulTensorEmbed_tmul]
      exact Submodule.smul_mem_smul r.property (by simp)
    | add x y hx hy =>
      simpa only [map_add] using (I ^ n • (⊤ : Submodule _ _)).add_mem hx hy
  · intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y hy
      refine ⟨y ⊗ₜ[MvPolynomial E A] (⟨r, hr⟩ : (I ^ n : Ideal _)), ?_⟩
      exact variableKoszulTensorEmbed_tmul A E j n y ⟨r, hr⟩
    · intro x y hx hy
      exact (LinearMap.range _).add_mem hx hy

/-- `variableKoszulTensorEmbed` commutes with the Koszul differential. -/
lemma variableKoszulTensorEmbed_d
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (j n : ℕ)
    (z : (⋀[MvPolynomial E A]^(j + 1) (E →₀ MvPolynomial E A)) ⊗[MvPolynomial E A]
      (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n :
        Ideal (MvPolynomial E A))) :
    variableKoszulTensorEmbed A E j n
        ((Koszul.d (variableKoszulDual A E) j).rTensor _ z) =
      Koszul.d (variableKoszulDual A E) j
        (variableKoszulTensorEmbed A E (j + 1) n z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x r =>
    simp [variableKoszulTensorEmbed_tmul, LinearMap.rTensor_tmul]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- `variableKoszulTensorEmbed` is compatible with the inclusion `I ^ (n + 1) ≤ I ^ n`. -/
lemma variableKoszulTensorEmbed_inclusion
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (j n : ℕ)
    (z : (⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) ⊗[MvPolynomial E A]
      (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ (n + 1) :
        Ideal (MvPolynomial E A))) :
    let I : Ideal (MvPolynomial E A) := Ideal.span (Set.range MvPolynomial.X)
    variableKoszulTensorEmbed A E j n
        (TensorProduct.map LinearMap.id
          (Submodule.inclusion
            (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n)) z) =
      variableKoszulTensorEmbed A E j (n + 1) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x r => simp [variableKoszulTensorEmbed_tmul]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- A morphism `φ : S ⟶ T` of short complexes of modules induces zero on homology if and only if
`φ.τ₂` maps every cycle of `S` into the range of `T.f`. -/
lemma shortComplex_homologyMap_eq_zero_iff_cycles
    {R : Type w} [CommRing R] {S T : ShortComplex (ModuleCat.{w} R)} (φ : S ⟶ T) :
    ShortComplex.homologyMap φ = 0 ↔
      ∀ x : S.X₂, S.g x = 0 → φ.τ₂ x ∈ LinearMap.range T.f.hom := by
  have heq := ShortComplex.π_homologyMap_ι φ
  constructor
  · intro h x hx
    have hzero : S.iCycles ≫ φ.τ₂ ≫ T.pOpcycles = 0 := by
      rw [← heq, h]
      simp
    let y := S.moduleCatCyclesIso.inv ⟨x, hx⟩
    have hy : S.iCycles y = x :=
      ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_iCycles ⟨x, hx⟩
    apply (T.moduleCat_pOpcycles_eq_zero_iff _).1
    simpa [ConcreteCategory.comp_apply, hy] using ConcreteCategory.congr_hom hzero y
  · intro h
    apply (cancel_epi S.homologyπ).1
    apply (cancel_mono T.homologyι).1
    rw [Category.assoc, heq]
    apply ModuleCat.hom_ext
    ext y
    simpa [ConcreteCategory.comp_apply] using
      (T.moduleCat_pOpcycles_eq_zero_iff _).2
        (h (S.iCycles y) (ConcreteCategory.congr_hom S.iCycles_g y))

/-- A morphism `φ : K ⟶ L` of chain complexes of modules induces zero on homology in degree `j`
if and only if `φ.f j` maps every cycle of `K` in degree `j` into the range of `L.d i j`. -/
lemma chain_homologyMap_eq_zero_iff_cycles
    {R : Type w} [CommRing R] {K L : ChainComplex (ModuleCat.{w} R) ℕ}
    (φ : K ⟶ L) (i j k : ℕ) (hi : (ComplexShape.down ℕ).prev j = i)
    (hk : (ComplexShape.down ℕ).next j = k) :
    HomologicalComplex.homologyMap φ j = 0 ↔
      ∀ x : K.X j, K.d j k x = 0 → φ.f j x ∈ LinearMap.range (L.d i j).hom := by
  let e := HomologicalComplex.natIsoSc' (ModuleCat.{w} R) (ComplexShape.down ℕ) i j k hi hk
  let φ' := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{w} R)
    (ComplexShape.down ℕ) i j k).map φ
  have hnat := congrArg (fun v ↦ ShortComplex.homologyMap v) (e.hom.naturality φ)
  simp only [ShortComplex.homologyMap_comp] at hnat
  change HomologicalComplex.homologyMap φ j ≫ (L.homologyIsoSc' i j k hi hk).hom =
    (K.homologyIsoSc' i j k hi hk).hom ≫ ShortComplex.homologyMap φ' at hnat
  have heq : HomologicalComplex.homologyMap φ j = 0 ↔ ShortComplex.homologyMap φ' = 0 := by
    constructor
    · intro h
      apply (cancel_epi (K.homologyIsoSc' i j k hi hk).hom).1
      simpa [h] using hnat.symm
    · intro h
      apply (cancel_mono (L.homologyIsoSc' i j k hi hk).hom).1
      simpa [h, φ', e] using hnat
  exact heq.trans (shortComplex_homologyMap_eq_zero_iff_cycles φ')

/-- Contraction of a wedge against a functional, in exterior degree zero. -/
lemma koszul_d_zero_wedge {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (φ : Module.Dual R M) (e : M) (y : ⋀[R]^0 M) :
    Koszul.d φ 0 (koszulWedge e 0 y) = φ e • y := by
  apply Subtype.ext
  have hy : (y : ExteriorAlgebra R M) =
      algebraMap R (ExteriorAlgebra R M) (exteriorPower.zeroEquiv R M y) := by
    conv_lhs => rw [← (exteriorPower.zeroEquiv R M).symm_apply_apply y]
    exact Koszul.coe_zeroEquiv_symm _
  show CliffordAlgebra.contractLeft φ
      (ExteriorAlgebra.ι R e * (y : ExteriorAlgebra R M)) =
    φ e • (y : ExteriorAlgebra R M)
  rw [CliffordAlgebra.contractLeft_ι_mul, hy,
    CliffordAlgebra.contractLeft_algebraMap, mul_zero, sub_zero]

/-- In exterior degree zero the multidegree is the monomial exponent. -/
lemma variableKoszulMultidegree_zero {E : Type v}
    (p : (E →₀ ℕ) × {s : Finset E // s.card = 0}) :
    variableKoszulMultidegree 0 p = p.1 := by
  classical
  have h : p.2.1 = (∅ : Finset E) := Finset.card_eq_zero.mp p.2.2
  simp [variableKoszulMultidegree, h]

/-- The basis element of `A[E]` indexed by `m` is the monomial `X ^ m`. -/
private lemma basisMonomials_apply_eq_monomial (A : Type u) [CommRing A] (E : Type v)
    (m : E →₀ ℕ) : (MvPolynomial.basisMonomials E A) m = MvPolynomial.monomial m (1 : A) :=
  congrFun (MvPolynomial.coe_basisMonomials E A) m

/-- The degree-zero contraction identity at a term of positive monomial degree. -/
lemma variableKoszulContractAt_homotopy_termBasis_zero
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (e : E)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = 0}) (he : p.1 e ≠ 0) :
    Koszul.d (variableKoszulDual A E) 0
        (variableKoszulContractAt A E e 0 (variableKoszulTermBasis A E 0 p)) =
      variableKoszulTermBasis A E 0 p := by
  have hX : (MvPolynomial.X e : MvPolynomial E A) =
      MvPolynomial.monomial (Finsupp.single e 1) 1 := rfl
  rw [variableKoszulContractAt_termBasis_nonzero A E e 0 p he, map_smul,
    koszul_d_zero_wedge, variableKoszulDual_single, smul_smul,
    variableKoszulTermBasis_apply, basisMonomials_apply_eq_monomial, hX,
    MvPolynomial.monomial_mul_monomial, one_mul,
    variableExponent_sub_single_add p.1 e he]

/-- The identification `⋀⁰ (E →₀ A[E]) ≃ A[E]`, as a linear map. -/
abbrev variableKoszulAug (A : Type u) [CommRing A] (E : Type v) :
    (⋀[MvPolynomial E A]^0 (E →₀ MvPolynomial E A)) →ₗ[MvPolynomial E A] MvPolynomial E A :=
  (exteriorPower.zeroEquiv (MvPolynomial E A) (E →₀ MvPolynomial E A)).toLinearMap

/-- The `A`-linear map `A → ⋀⁰ (E →₀ A[E])` sending `a` to the constant `C a`. -/
abbrev variableKoszulUnit (A : Type u) [CommRing A] (E : Type v) :
    A →ₗ[A] (⋀[MvPolynomial E A]^0 (E →₀ MvPolynomial E A)) :=
  ((exteriorPower.zeroEquiv (MvPolynomial E A)
      (E →₀ MvPolynomial E A)).symm.toLinearMap.restrictScalars A).comp
    (Algebra.linearMap A (MvPolynomial E A))

/-- `variableKoszulAug` sends the basis element of `⋀⁰` to `1`. -/
lemma variableKoszulAug_exteriorBasis (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (s : {t : Finset E // t.card = 0}) :
    variableKoszulAug A E
      ((Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower 0 s) = 1 := by
  rw [variableExteriorBasis_apply]
  refine Koszul.zeroEquiv_eq_of_coe ?_
  show ExteriorAlgebra.ιMulti (MvPolynomial E A) 0
      (fun k ↦ Finsupp.single (s.1.orderEmbOfFin s.2 k) 1) = algebraMap _ _ 1
  simp [ExteriorAlgebra.ιMulti]

/-- `variableKoszulAug` sends the basis element of `⋀⁰` indexed by `(m, ∅)` to `X^m`. -/
lemma variableKoszulAug_termBasis (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (p : (E →₀ ℕ) × {s : Finset E // s.card = 0}) :
    variableKoszulAug A E (variableKoszulTermBasis A E 0 p) =
      MvPolynomial.monomial p.1 (1 : A) := by
  rw [variableKoszulTermBasis_apply, basisMonomials_apply_eq_monomial, map_smul,
    variableKoszulAug_exteriorBasis,
    smul_eq_mul, mul_one]

/-- `variableKoszulAug` sends `variableKoszulUnit A E a` to `C a`. -/
lemma variableKoszulAug_unit (A : Type u) [CommRing A] (E : Type v) (a : A) :
    variableKoszulAug A E (variableKoszulUnit A E a) = MvPolynomial.C a := by
  show (exteriorPower.zeroEquiv (MvPolynomial E A) (E →₀ MvPolynomial E A))
    ((exteriorPower.zeroEquiv (MvPolynomial E A) (E →₀ MvPolynomial E A)).symm
      (algebraMap A (MvPolynomial E A) a)) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The augmentation kills the image of the degree-zero Koszul differential. -/
lemma variableKoszulAug_d_zero (A : Type u) [CommRing A] (E : Type v)
    (x : ⋀[MvPolynomial E A]^1 (E →₀ MvPolynomial E A)) :
    MvPolynomial.eval₂Hom (RingHom.id A) (0 : E → A)
      (variableKoszulAug A E (Koszul.d (variableKoszulDual A E) 0 x)) = 0 := by
  apply RingHom.mem_ker.mp
  rw [augmentation_ker_eq_variableIdeal A E]
  have h : variableKoszulAug A E (Koszul.d (variableKoszulDual A E) 0 x) ∈
      Submodule.map (exteriorPower.zeroEquiv (MvPolynomial E A)
          (E →₀ MvPolynomial E A)).toLinearMap
        (LinearMap.range (Koszul.d (variableKoszulDual A E) 0)) := ⟨_, ⟨x, rfl⟩, rfl⟩
  rwa [variableKoszul_range_d_zero] at h

/-- Evaluation at zero kills every nonconstant monomial. -/
private lemma variableEval_zero_monomial_eq_zero (A : Type u) [CommRing A] {E : Type v}
    {m : E →₀ ℕ} (hm : m ≠ 0) :
    MvPolynomial.eval₂Hom (RingHom.id A) (0 : E → A) (MvPolynomial.monomial m (1 : A)) = 0 := by
  obtain ⟨e, he⟩ : ∃ e, m e ≠ 0 := by
    by_contra h
    exact hm (Finsupp.ext fun e => by simpa using not_exists.mp h e)
  rw [MvPolynomial.eval₂Hom_monomial]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr he) ?_)
  simp [zero_pow he]

/-- The augmented degree-zero contraction identity on a basis element of `⋀⁰`. -/
private lemma variableKoszulChosenContract_homotopy_zero_augmented_termBasis
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (p : (E →₀ ℕ) × {s : Finset E // s.card = 0}) :
    Koszul.d (variableKoszulDual A E) 0
        (variableKoszulChosenContract A E 0 (variableKoszulTermBasis A E 0 p)) +
      variableKoszulUnit A E (MvPolynomial.eval₂Hom (RingHom.id A) (0 : E → A)
        (variableKoszulAug A E (variableKoszulTermBasis A E 0 p))) =
      variableKoszulTermBasis A E 0 p := by
  classical
  have hmd : variableKoszulMultidegree 0 p = p.1 := variableKoszulMultidegree_zero p
  rw [variableKoszulAug_termBasis]
  by_cases hp : p.1 = 0
  · have hc : variableKoszulChosenContract A E 0 (variableKoszulTermBasis A E 0 p) = 0 := by
      rw [variableKoszulChosenContract_termBasis, dite_eq_left (hmd.trans hp)]
    rw [hc, map_zero, zero_add]
    refine (exteriorPower.zeroEquiv (MvPolynomial E A) (E →₀ MvPolynomial E A)).injective ?_
    show variableKoszulAug A E _ = variableKoszulAug A E _
    rw [variableKoszulAug_unit, variableKoszulAug_termBasis, hp]
    simp
  · have hα : variableKoszulMultidegree 0 p ≠ 0 := by rwa [hmd]
    rw [variableEval_zero_monomial_eq_zero A hp, map_zero, add_zero,
      variableKoszulChosenContract_termBasis_eq_at A E 0 p hα]
    refine variableKoszulContractAt_homotopy_termBasis_zero A E _ p fun hc => ?_
    have hmem := Finset.min'_mem (variableKoszulMultidegree 0 p).support
      (Finset.nonempty_iff_ne_empty.mpr (mt Finsupp.support_eq_empty.mp hα))
    exact Finsupp.mem_support_iff.mp hmem ((DFunLike.congr_fun hmd _).trans hc)

/-- **The augmented degree-zero contraction identity.**  In exterior degree zero the chosen
contraction splits the Koszul differential modulo the image of the unit. -/
lemma variableKoszulChosenContract_homotopy_zero_augmented
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (x : ⋀[MvPolynomial E A]^0 (E →₀ MvPolynomial E A)) :
    Koszul.d (variableKoszulDual A E) 0 (variableKoszulChosenContract A E 0 x) +
        variableKoszulUnit A E
          (MvPolynomial.eval₂Hom (RingHom.id A) (0 : E → A) (variableKoszulAug A E x)) = x := by
  classical
  let ev : MvPolynomial E A →ₗ[A] A :=
    { toFun := MvPolynomial.eval₂Hom (RingHom.id A) (0 : E → A)
      map_add' := map_add _
      map_smul' := fun a p => by
        show MvPolynomial.eval₂Hom (RingHom.id A) (0 : E → A) (a • p) = a • _
        rw [MvPolynomial.smul_eq_C_mul, map_mul]
        simp [smul_eq_mul] }
  have hlin : ((((Koszul.d (variableKoszulDual A E) 0).restrictScalars A).comp
        (variableKoszulChosenContract A E 0)) +
      ((variableKoszulUnit A E).comp
        (ev.comp ((variableKoszulAug A E).restrictScalars A)))) = LinearMap.id :=
    (variableKoszulTermBasis A E 0).ext
      (variableKoszulChosenContract_homotopy_zero_augmented_termBasis A E)
  exact LinearMap.congr_fun hlin x

/-- The augmentation vanishes on the positive part of the filtration. -/
lemma variableKoszulAug_eq_zero_of_mem_filtration
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (x : ⋀[MvPolynomial E A]^0 (E →₀ MvPolynomial E A))
    (hx : x ∈ variableKoszulFiltration A E 0 1) :
    MvPolynomial.eval₂Hom (RingHom.id A) (0 : E → A) (variableKoszulAug A E x) = 0 := by
  classical
  have hx' : x ∈ Submodule.span A (Set.range
      (fun p : {p : (E →₀ ℕ) × {s : Finset E // s.card = 0} // 1 ≤ p.1.degree} ↦
        variableKoszulTermBasis A E 0 p.1)) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, rfl⟩ := hy
    have hp : p.1.1 ≠ 0 := fun h ↦ by simpa [h] using p.2
    rw [variableKoszulAug_termBasis]
    exact variableEval_zero_monomial_eq_zero A hp
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | smul r a _ ha =>
    rw [(variableKoszulAug A E).map_smul_of_tower r, MvPolynomial.smul_eq_C_mul, map_mul, ha,
      mul_zero]

/-- The chosen contraction splits the Koszul differential in exterior degree zero on the part
of positive monomial degree: the case of the augmented identity in which the augmentation
vanishes. -/
lemma variableKoszulChosenContract_homotopy_zero
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (x : ⋀[MvPolynomial E A]^0 (E →₀ MvPolynomial E A))
    (hx : x ∈ variableKoszulFiltration A E 0 1) :
    Koszul.d (variableKoszulDual A E) 0
      (variableKoszulChosenContract A E 0 x) = x := by
  have h := variableKoszulChosenContract_homotopy_zero_augmented A E x
  rwa [variableKoszulAug_eq_zero_of_mem_filtration A E x hx, map_zero, add_zero] at h

/-! ### The contracting homotopy on the Koszul complex tensored with a power of the ideal -/

section Contract

variable (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]

/-- The degree-`j` term of the Koszul complex of the variables, tensored with the `n`-th power
of the ideal of variables. -/
abbrev koszulTensorIdealPow (j n : ℕ) : Type max u v :=
  (⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) ⊗[MvPolynomial E A]
    ((Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n :
      Ideal (MvPolynomial E A)))

/-- The filtration by monomial degree is antitone. -/
lemma variableKoszulFiltration_antitone (j : ℕ) {m n : ℕ} (h : m ≤ n) :
    variableKoszulFiltration A E j n ≤ variableKoszulFiltration A E j m := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨p, rfl⟩
  exact Submodule.subset_span ⟨⟨p.1, h.trans p.2⟩, rfl⟩

/-- The image of the embedding of `K_j ⊗ I ^ n` into `K_j` is the `n`-th filtration step. -/
lemma mem_range_variableKoszulTensorEmbed_iff (j n : ℕ)
    (y : ⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) :
    y ∈ LinearMap.range (variableKoszulTensorEmbed A E j n) ↔
      y ∈ variableKoszulFiltration A E j n := by
  rw [variableKoszulTensorEmbed_range, variableKoszulFiltration_eq_idealPower_smul]
  exact Iff.rfl

/-- The embedding of `K_j ⊗ I ^ n` lands in the `n`-th filtration step. -/
private lemma variableKoszulTensorEmbed_mem_filtration (j n : ℕ)
    (z : koszulTensorIdealPow A E j n) :
    variableKoszulTensorEmbed A E j n z ∈ variableKoszulFiltration A E j n :=
  (mem_range_variableKoszulTensorEmbed_iff A E j n _).1 ⟨z, rfl⟩

/-- The chosen contraction carries the image of `K_j ⊗ I ^ (n + 1)` into the image of
`K_(j+1) ⊗ I ^ n`. -/
lemma variableKoszulChosenContract_mem_range (j n : ℕ) (z : koszulTensorIdealPow A E j (n + 1)) :
    variableKoszulChosenContract A E j (variableKoszulTensorEmbed A E j (n + 1) z) ∈
      LinearMap.range (variableKoszulTensorEmbed A E (j + 1) n) := by
  rw [mem_range_variableKoszulTensorEmbed_iff]
  exact variableKoszulChosenContract_maps_filtration A E j n _
    (variableKoszulTensorEmbed_mem_filtration A E j (n + 1) z)

/-- `K_j ⊗ I ^ n` is isomorphic to its image in `K_j`. -/
noncomputable def koszulTensorEmbedEquiv (j n : ℕ) :
    koszulTensorIdealPow A E j n ≃ₗ[MvPolynomial E A]
      LinearMap.range (variableKoszulTensorEmbed A E j n) :=
  LinearEquiv.ofInjective _ (variableKoszulTensorEmbed_injective A E j n)

/-- `variableKoszulTensorEmbed` sends the preimage of `y` under `koszulTensorEmbedEquiv` to
`y`. -/
lemma variableKoszulTensorEmbed_symm_apply (j n : ℕ)
    (y : LinearMap.range (variableKoszulTensorEmbed A E j n)) :
    variableKoszulTensorEmbed A E j n ((koszulTensorEmbedEquiv A E j n).symm y) = (y : _) :=
  congrArg Subtype.val ((koszulTensorEmbedEquiv A E j n).apply_symm_apply y)

/-- **The contracting homotopy.** The `A`-linear map `K_j ⊗ I ^ (n + 1) → K_(j+1) ⊗ I ^ n`
induced by the chosen contraction of the Koszul complex. -/
noncomputable def koszulTensorContract (j n : ℕ) :
    koszulTensorIdealPow A E j (n + 1) →ₗ[A] koszulTensorIdealPow A E (j + 1) n :=
  ((koszulTensorEmbedEquiv A E (j + 1) n).symm.toLinearMap.restrictScalars A).comp
    (LinearMap.codRestrict
      (Submodule.restrictScalars A (LinearMap.range (variableKoszulTensorEmbed A E (j + 1) n)))
      ((variableKoszulChosenContract A E j).comp
        ((variableKoszulTensorEmbed A E j (n + 1)).restrictScalars A))
      (variableKoszulChosenContract_mem_range A E j n))

/-- Under `variableKoszulTensorEmbed`, `koszulTensorContract` is the chosen contraction. -/
@[simp]
lemma variableKoszulTensorEmbed_koszulTensorContract (j n : ℕ)
    (z : koszulTensorIdealPow A E j (n + 1)) :
    variableKoszulTensorEmbed A E (j + 1) n (koszulTensorContract A E j n z) =
      variableKoszulChosenContract A E j (variableKoszulTensorEmbed A E j (n + 1) z) :=
  variableKoszulTensorEmbed_symm_apply A E (j + 1) n _

/-- The homotopy identity in positive degree. -/
lemma koszulTensorContract_homotopy (q n : ℕ) (z : koszulTensorIdealPow A E (q + 1) (n + 1)) :
    (Koszul.d (variableKoszulDual A E) (q + 1)).rTensor _
        (koszulTensorContract A E (q + 1) n z) +
      koszulTensorContract A E q n ((Koszul.d (variableKoszulDual A E) q).rTensor _ z) =
      TensorProduct.map LinearMap.id
        (Submodule.inclusion (Ideal.pow_le_pow_right (Nat.le_succ n) :
          Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ (n + 1) ≤
            Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n)) z := by
  apply variableKoszulTensorEmbed_injective A E (q + 1) n
  rw [map_add, variableKoszulTensorEmbed_d, variableKoszulTensorEmbed_koszulTensorContract,
    variableKoszulTensorEmbed_koszulTensorContract, variableKoszulTensorEmbed_d,
    variableKoszulTensorEmbed_inclusion]
  exact variableKoszulChosenContract_homotopy A E q
    (variableKoszulTensorEmbed A E (q + 1) (n + 1) z)

/-- The homotopy identity in degree zero. -/
lemma koszulTensorContract_homotopy_zero (n : ℕ) (z : koszulTensorIdealPow A E 0 (n + 1)) :
    (Koszul.d (variableKoszulDual A E) 0).rTensor _ (koszulTensorContract A E 0 n z) =
      TensorProduct.map LinearMap.id
        (Submodule.inclusion (Ideal.pow_le_pow_right (Nat.le_succ n) :
          Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ (n + 1) ≤
            Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n)) z := by
  apply variableKoszulTensorEmbed_injective A E 0 n
  rw [variableKoszulTensorEmbed_d, variableKoszulTensorEmbed_koszulTensorContract,
    variableKoszulTensorEmbed_inclusion]
  refine variableKoszulChosenContract_homotopy_zero A E _ ?_
  exact variableKoszulFiltration_antitone A E 0 (Nat.one_le_iff_ne_zero.2 (Nat.succ_ne_zero n))
    (variableKoszulTensorEmbed_mem_filtration A E 0 (n + 1) z)

/-- The homotopy identity in positive degree, as an identity of maps. -/
lemma koszulTensorContract_homotopy_map (q n : ℕ) :
    (((Koszul.d (variableKoszulDual A E) (q + 1)).rTensor
          (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n :
            Ideal (MvPolynomial E A))).restrictScalars A).comp
        (koszulTensorContract A E (q + 1) n) +
      (koszulTensorContract A E q n).comp
        (((Koszul.d (variableKoszulDual A E) q).rTensor
          (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ (n + 1) :
            Ideal (MvPolynomial E A))).restrictScalars A) =
      (TensorProduct.map LinearMap.id
        (Submodule.inclusion (Ideal.pow_le_pow_right (Nat.le_succ n) :
          Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ (n + 1) ≤
            Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n))
          ).restrictScalars A :=
  LinearMap.ext fun z => koszulTensorContract_homotopy A E q n z

/-- The homotopy identity in degree zero, as an identity of maps. -/
lemma koszulTensorContract_homotopy_zero_map (n : ℕ) :
    (((Koszul.d (variableKoszulDual A E) 0).rTensor
          (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n :
            Ideal (MvPolynomial E A))).restrictScalars A).comp
        (koszulTensorContract A E 0 n) =
      (TensorProduct.map LinearMap.id
        (Submodule.inclusion (Ideal.pow_le_pow_right (Nat.le_succ n) :
          Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ (n + 1) ≤
            Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n))
          ).restrictScalars A :=
  LinearMap.ext fun z => koszulTensorContract_homotopy_zero A E n z

end Contract
end MvPolynomial

end
