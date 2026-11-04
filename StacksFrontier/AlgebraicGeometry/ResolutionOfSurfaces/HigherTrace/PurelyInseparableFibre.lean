module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.KummerPolynomial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples

/-!
# Fibres of a finite dominant morphism whose function field extension has its `p`-th powers below

Let `f : Y ⟶ X` be a finite dominant morphism of integral schemes with `X` normal, and suppose
that every element of the function field `L` of `Y` has its `p`-th power in the function field
`K` of `X`.  Then every fibre of `f` is a single point.

Over an affine open `U ⊆ X` the ring `A = Γ(X, U)` is a normal domain with fraction field `K`,
and `B = Γ(Y, f⁻¹U)` is a domain, finite over `A`, with fraction field `L`.  For `b ∈ B` the
element `b ^ p` of `B` lies in `K` by hypothesis, and it is integral over `A` because `b` is, so
normality of `A` puts it in `A`.  Thus `B` is generated over `A` by elements whose `p`-th power
lies in `A` — and whose `p`-fold sum vanishes, the characteristic being `p` — so
`Spec(B) → Spec(A)` is a homeomorphism by [Stacks, Tag 0BRA].  Injectivity of that map is the
uniqueness half of the fibre statement; the existence half is surjectivity of a finite dominant
morphism, which holds because such a morphism is closed with dense image.

## Main results

* `PrimeSpectrum.injective_comap_of_forall_pow_mem_range`: the ring-level injectivity, from
  [Stacks, Tag 0BRA].
* `AlgebraicGeometry.pow_mem_range_appLE_of_forall_pow_mem_range`: the sections over an affine
  open of `Y` have their `p`-th powers in the sections over the affine open of `X` below.
* `AlgebraicGeometry.exists_preimage_singleton_of_forall_pow_mem_range`: every fibre is a single
  point.
* `pow_mem_range_of_algEquiv_adjoinRoot`: a presentation `L ≅ K[T]⧸(Tᵖ - a)` in characteristic
  `p` puts every `p`-th power of `L` in `K`, which is the hypothesis above in the form
  [Stacks, Tag 0AX6] supplies it.
* `AlgebraicGeometry.exists_preimage_singleton_of_algEquiv_adjoinRoot`: the two combined — the
  fibre statement for the morphism of [Stacks, Tag 0AX6] itself.

## References

* [Stacks Project, Tag 0AX6](https://stacks.math.columbia.edu/tag/0AX6)
* [Stacks Project, Tag 0BRA](https://stacks.math.columbia.edu/tag/0BRA)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

namespace PrimeSpectrum

/-- **A ring map all of whose `p`-th powers lie in the base is injective on spectra**, provided
`p` vanishes in the target and the kernel is contained in the nilradical.  Every element `b`
satisfies `b ^ p ^ 1 ∈ A` and `p ^ 1 • b = 0 ∈ A`, which is the generating condition of
[Stacks, Tag 0BRA] with `n = 1`; that lemma then makes `Spec(B) → Spec(A)` a homeomorphism. -/
theorem injective_comap_of_forall_pow_mem_range {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] {p : ℕ} (hp : p.Prime)
    (hchar : (p : B) = 0) (hker : RingHom.ker (algebraMap A B) ≤ nilradical A)
    (hpow : ∀ b : B, b ^ p ∈ (algebraMap A B).range) :
    Function.Injective (comap (algebraMap A B)) := by
  have hgen : Algebra.adjoin A {x : B | ∃ n > 0, x ^ p ^ n ∈ (algebraMap A B).range ∧
      p ^ n • x ∈ (algebraMap A B).range} = ⊤ := by
    refine eq_top_iff.mpr fun b _ => Algebra.subset_adjoin ⟨1, Nat.one_pos, ?_, ?_⟩
    · simpa using hpow b
    · rw [RingHom.mem_range]
      exact ⟨0, by simp [pow_one, nsmul_eq_mul, hchar]⟩
  exact (isHomeomorph_comap_and_isPurelyInseparable_and_baseChange_of_adjoin_pow_eq_top.{u, v, 0, 0}
    p hp hker hgen).1.injective

end PrimeSpectrum

/-- A nontrivial ring in which a prime `p` vanishes has characteristic `p`: the characteristic
divides `p` and is not `1`. -/
theorem charP_of_natCast_eq_zero {L : Type u} [CommRing L] [Nontrivial L] {p : ℕ}
    (hp : p.Prime) (h : (p : L) = 0) : CharP L p := by
  obtain ⟨c, hc⟩ := CharP.exists L
  have := hc
  rcases hp.eq_one_or_self_of_dvd c ((CharP.cast_eq_zero_iff L c p).mp h) with h1 | h1
  · exact absurd h1 (CharP.char_ne_one L c)
  · exact h1 ▸ hc

/-- A prime that vanishes in the base of an algebra vanishes in the algebra. -/
theorem natCast_eq_zero_of_charP {Λ L : Type u} [CommRing Λ] [CommRing L] [Algebra Λ L]
    (p : ℕ) [CharP Λ p] : (p : L) = 0 := by
  rw [← map_natCast (algebraMap Λ L) p, CharP.cast_eq_zero, map_zero]

/-- **A `p`-th root presentation of a field extension in characteristic `p` puts every `p`-th
power in the base.**  The elements of `L` whose `p`-th power comes from `K` form a `K`-subalgebra
— Frobenius is a ring map in characteristic `p` — and that subalgebra contains the adjoined
root, whose `p`-th power is `a`; the root generates `L` over `K` by
`AdjoinRoot.adjoinRoot_eq_top`. -/
theorem pow_mem_range_of_algEquiv_adjoinRoot {K L : Type u} [Field K] [Field L] [Algebra K L]
    {p : ℕ} (hp : p.Prime) [CharP L p] (a : K)
    (e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C a) ≃ₐ[K] L) (l : L) :
    l ^ p ∈ (algebraMap K L).range := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨w, rfl⟩ := e.surjective l
  have hw : w ∈ Algebra.adjoin K
      ({AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C a)} :
        Set (AdjoinRoot (Polynomial.X ^ p - Polynomial.C a))) := by
    rw [AdjoinRoot.adjoinRoot_eq_top]
    exact Algebra.mem_top
  induction hw using Algebra.adjoin_induction with
  | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      refine RingHom.mem_range.mpr ⟨a, ?_⟩
      have hroot : AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C a) ^ p =
          algebraMap K (AdjoinRoot (Polynomial.X ^ p - Polynomial.C a)) a := by
        rw [AdjoinRoot.algebraMap_eq]
        exact root_X_pow_sub_C_pow p a
      rw [← map_pow, hroot, AlgEquiv.commutes]
  | algebraMap r =>
      exact RingHom.mem_range.mpr ⟨r ^ p, by rw [AlgEquiv.commutes, map_pow]⟩
  | add x y _ _ ihx ihy =>
      rw [map_add, add_pow_char]
      exact add_mem ihx ihy
  | mul x y _ _ ihx ihy =>
      rw [map_mul, mul_pow]
      exact mul_mem ihx ihy

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The two spellings of the function field extension of a dominant morphism of integral
schemes agree: `AlgebraicGeometry.functionFieldMap` indexes the comparison of stalks of the
target by an `Inseparable`, `AlgebraicGeometry.Scheme.Hom.functionFieldMap` by the underlying
`Specializes`. -/
theorem functionFieldMap_eq_hom (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    functionFieldMap f = (Scheme.Hom.functionFieldMap f).hom :=
  rfl

/-- **The sections of `Y` over the preimage of an affine open of a normal `X` have their `p`-th
powers in the sections of `X`.**  The section `b` is integral over `A = Γ(X, U)` because `f` is
finite, so `b ^ p` is too; it lies in the function field `K` of `X` by hypothesis, and `A` is
integrally closed in `K` by [Stacks, Tag 033L], so `b ^ p` comes from `A`. -/
theorem pow_mem_range_appLE_of_forall_pow_mem_range (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsNormal X] [IsFinite f] [IsDominant f] {p : ℕ}
    (hpow : ∀ l : ↑Y.functionField, l ^ p ∈ (functionFieldMap f).range)
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
    (b : Γ(Y, f ⁻¹ᵁ U)) :
    b ^ p ∈ (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom.range := by
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  let : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  have halg : algebraMap Γ(X, U) Γ(Y, f ⁻¹ᵁ U) = (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom := rfl
  let : Algebra X.functionField Y.functionField :=
    (Scheme.Hom.functionFieldMap f).hom.toAlgebra
  let : Algebra Γ(X, U) Y.functionField :=
    ((Scheme.Hom.functionFieldMap f).hom.comp (X.germToFunctionField U).hom).toAlgebra
  have : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X, U) Γ(Y, f ⁻¹ᵁ U) Y.functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have h : X.germToFunctionField U ≫ Scheme.Hom.functionFieldMap f =
        f.appLE U (f ⁻¹ᵁ U) le_rfl ≫ Y.germToFunctionField (f ⁻¹ᵁ U) :=
      f.germ_functionFieldMap le_rfl _ _
    exact congrArg CommRingCat.Hom.hom h
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  have : IsFractionRing Γ(Y, f ⁻¹ᵁ U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y (f ⁻¹ᵁ U) hV
  have : IsIntegrallyClosed Γ(X, U) :=
    (isNormal_iff_forall_affineOpen_normal X).mp ‹IsNormal X› ⟨U, hU⟩ ‹Nonempty U›
  have hfin : (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom.Finite := by
    rw [Scheme.Hom.appLE_eq_app]
    exact IsFinite.finite_app f U hU
  have : Module.Finite Γ(X, U) Γ(Y, f ⁻¹ᵁ U) :=
    RingHom.finite_algebraMap.mp (by rw [halg]; exact hfin)
  have : FaithfulSMul X.functionField Y.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (Scheme.Hom.functionFieldMap f).hom.injective
  have hpow' : ∀ l : Y.functionField,
      l ^ p ∈ (algebraMap X.functionField Y.functionField).range := fun l => by
    rw [show algebraMap X.functionField Y.functionField =
      (Scheme.Hom.functionFieldMap f).hom from rfl, ← functionFieldMap_eq_hom f]
    exact hpow l
  obtain ⟨k, hk⟩ := RingHom.mem_range.mp
    (hpow' (algebraMap Γ(Y, f ⁻¹ᵁ U) Y.functionField b))
  have hbint : _root_.IsIntegral Γ(X, U)
      (algebraMap Γ(Y, f ⁻¹ᵁ U) Y.functionField b) :=
    (Algebra.IsIntegral.isIntegral (R := Γ(X, U)) b).algebraMap
  have hkint : _root_.IsIntegral Γ(X, U) k := by
    refine (isIntegral_algebraMap_iff (R := Γ(X, U)) (A := X.functionField)
      (B := Y.functionField) (x := k)).mp ?_
    have hrw : algebraMap X.functionField Y.functionField k =
        algebraMap Γ(Y, f ⁻¹ᵁ U) Y.functionField b ^ p := hk
    rw [hrw]
    exact hbint.pow p
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hkint
  refine RingHom.mem_range.mpr ⟨a, ?_⟩
  rw [← halg]
  refine IsFractionRing.injective Γ(Y, f ⁻¹ᵁ U) Y.functionField ?_
  calc algebraMap Γ(Y, f ⁻¹ᵁ U) Y.functionField (algebraMap Γ(X, U) Γ(Y, f ⁻¹ᵁ U) a)
      = algebraMap Γ(X, U) Y.functionField a :=
        (IsScalarTower.algebraMap_apply Γ(X, U) Γ(Y, f ⁻¹ᵁ U) Y.functionField a).symm
    _ = algebraMap X.functionField Y.functionField
          (algebraMap Γ(X, U) X.functionField a) :=
        IsScalarTower.algebraMap_apply Γ(X, U) X.functionField Y.functionField a
    _ = algebraMap X.functionField Y.functionField k := by rw [ha]
    _ = algebraMap Γ(Y, f ⁻¹ᵁ U) Y.functionField b ^ p := hk
    _ = algebraMap Γ(Y, f ⁻¹ᵁ U) Y.functionField (b ^ p) := (map_pow _ _ _).symm

/-- **The fibres of a finite dominant morphism onto a normal integral scheme are single
points**, when `p` vanishes in the function field `L` of the source and every `p`-th power in
`L` lies in the function field of the target.  Over an affine open of `X` the map on spectra is
injective by `PrimeSpectrum.injective_comap_of_forall_pow_mem_range`, whose generating
hypothesis is `AlgebraicGeometry.pow_mem_range_appLE_of_forall_pow_mem_range`; a finite dominant
morphism is surjective, so the fibre is nonempty. -/
theorem exists_preimage_singleton_of_forall_pow_mem_range (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsNormal X] [IsFinite f] [IsDominant f] {p : ℕ}
    (hp : p.Prime) (hchar : (p : ↑Y.functionField) = 0)
    (hpow : ∀ l : ↑Y.functionField, l ^ p ∈ (functionFieldMap f).range) (x : X) :
    ∃ y : Y, f ⁻¹' {x} = {y} := by
  obtain ⟨y, hy⟩ := f.surjective x
  refine ⟨y, Set.eq_singleton_iff_unique_mem.mpr ⟨hy, fun z hz => ?_⟩⟩
  have hzx : f.base z = x := hz
  obtain ⟨U, hU, hxU, -⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (Opens.mem_top x)
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have hmem : ∀ w, f.base w = x → w ∈ f ⁻¹ᵁ U := fun w hw => show f.base w ∈ U from hw ▸ hxU
  have hyV := hmem y hy
  have hzV := hmem z hzx
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨y, hyV⟩⟩
  let : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  have halg : algebraMap Γ(X, U) Γ(Y, f ⁻¹ᵁ U) = (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom := rfl
  have : IsFractionRing Γ(Y, f ⁻¹ᵁ U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y (f ⁻¹ᵁ U) hV
  have hcharB : ((p : ℕ) : Γ(Y, f ⁻¹ᵁ U)) = 0 :=
    IsFractionRing.injective Γ(Y, f ⁻¹ᵁ U) Y.functionField
      (by rw [map_natCast, map_zero]; exact hchar)
  have htfae := ((tfae_isDominant_of_isIntegral f).out 1 4).mp ‹IsDominant f›
  have hinjAB : Function.Injective (algebraMap Γ(X, U) Γ(Y, f ⁻¹ᵁ U)) :=
    htfae ⟨f ⁻¹ᵁ U, hV⟩ ⟨U, hU⟩ inferInstance inferInstance le_rfl
  have hker : RingHom.ker (algebraMap Γ(X, U) Γ(Y, f ⁻¹ᵁ U)) ≤ nilradical Γ(X, U) := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinjAB]
    exact bot_le
  have hspec := PrimeSpectrum.injective_comap_of_forall_pow_mem_range hp hcharB hker
    (pow_mem_range_appLE_of_forall_pow_mem_range f hpow U hU)
  have hcomap : ∀ (w : Y) (hw : w ∈ f ⁻¹ᵁ U),
      PrimeSpectrum.comap (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom (hV.primeIdealOf ⟨w, hw⟩) =
        hU.primeIdealOf ⟨f.base w, hw⟩ := fun w hw =>
    IsAffineOpen.comap_primeIdealOf_appLE U hU (f ⁻¹ᵁ U) hV le_rfl hw
  have hpt : hV.primeIdealOf ⟨z, hzV⟩ = hV.primeIdealOf ⟨y, hyV⟩ := by
    refine hspec ?_
    show PrimeSpectrum.comap (algebraMap Γ(X, U) Γ(Y, f ⁻¹ᵁ U)) _ =
      PrimeSpectrum.comap (algebraMap Γ(X, U) Γ(Y, f ⁻¹ᵁ U)) _
    rw [halg, hcomap z hzV, hcomap y hyV]
    exact congrArg hU.primeIdealOf (Subtype.ext (hzx.trans hy.symm))
  have := congrArg hV.fromSpec hpt
  rwa [hV.fromSpec_primeIdealOf ⟨z, hzV⟩, hV.fromSpec_primeIdealOf ⟨y, hyV⟩] at this

/-- **The fibres of the morphism of [Stacks, Tag 0AX6] are single points.**  The source presents
the extension of function fields as `L ≅ K[T]⧸(Tᵖ - a)` in characteristic `p`, which by
`pow_mem_range_of_algEquiv_adjoinRoot` puts every `p`-th power of `L` in `K`; that is the
hypothesis of `AlgebraicGeometry.exists_preimage_singleton_of_forall_pow_mem_range`. -/
theorem exists_preimage_singleton_of_algEquiv_adjoinRoot (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsNormal X] [IsFinite f] [IsDominant f] {p : ℕ}
    (hp : p.Prime) (hchar : (p : ↑X.functionField) = 0) :
    letI : Algebra ↑X.functionField ↑Y.functionField := (functionFieldMap f).toAlgebra
    ∀ (a : ↑X.functionField)
      (_e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C a) ≃ₐ[↑X.functionField]
        ↑Y.functionField) (x : X), ∃ y : Y, f ⁻¹' {x} = {y} := by
  let : Algebra ↑X.functionField ↑Y.functionField := (functionFieldMap f).toAlgebra
  intro a e x
  have : CharP ↑X.functionField p := charP_of_natCast_eq_zero hp hchar
  have : CharP ↑Y.functionField p :=
    charP_of_natCast_eq_zero hp (natCast_eq_zero_of_charP (Λ := ↑X.functionField) p)
  refine exists_preimage_singleton_of_forall_pow_mem_range f hp
    (CharP.cast_eq_zero _ p) (fun l => ?_) x
  exact pow_mem_range_of_algEquiv_adjoinRoot hp a e l

/-- `AlgebraicGeometry.exists_preimage_singleton_of_algEquiv_adjoinRoot` in the form
`AlgebraicGeometry.pushforwardStalkEquivOfPreimageSingleton` consumes: the fibre of `f` through
a point `y` of `Y` is `{y}`. -/
theorem preimage_singleton_eq_of_algEquiv_adjoinRoot (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsNormal X] [IsFinite f] [IsDominant f] {p : ℕ}
    (hp : p.Prime) (hchar : (p : ↑X.functionField) = 0) :
    letI : Algebra ↑X.functionField ↑Y.functionField := (functionFieldMap f).toAlgebra
    ∀ (a : ↑X.functionField)
      (_e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C a) ≃ₐ[↑X.functionField]
        ↑Y.functionField) (y : Y), f ⁻¹' {f.base y} = {y} := by
  let : Algebra ↑X.functionField ↑Y.functionField := (functionFieldMap f).toAlgebra
  intro a e y
  obtain ⟨y', hy'⟩ :=
    exists_preimage_singleton_of_algEquiv_adjoinRoot f hp hchar a e (f.base y)
  have hyy : y = y' := by
    have hmem : y ∈ f ⁻¹' {f.base y} := rfl
    rw [hy'] at hmem
    exact hmem
  rw [hy', hyy]

end AlgebraicGeometry

end
