module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import StacksFrontier.RingTheory.Dualizing.DerivedTorsion

/-!
# The Ext² comparison for derived torsion is not surjective

Let `A` be a commutative ring, `f ∈ A`, and `I = (f)`. The `I`-power-torsion modules form a
Serre subcategory of `Mod(A)`, and the inclusion induces comparison maps on `Extⁿ` between
torsion modules. Those maps are bijective for `n = 0, 1` — parts (1) and (2) of Stacks 0A6P,
proved in `StacksFrontier.RingTheory.Dualizing.DerivedTorsion` — and this file shows that in
degree `2` the comparison is not surjective in general, which is part (3) of Stacks 0A6P. Part
(4), that the comparison functor of Stacks 0A6N is not an equivalence, follows.

## The counterexample

The only property of the ring that is used is the one the source's ring
`ℤ[f, x, xₙ]/(fx, fⁿxₙ - x)` was built to have: a nonzero element `x` annihilated by `f` and
divisible by every power of `f`. Such an `x` annihilates *every* `I`-power-torsion module, since
an element of such a module is killed by some `fⁿ` and `x ∈ fⁿA`.

Take `M = A/fA` and `N = A[f]`, and consider the two short exact sequences

`S_q : 0 → (f) → A → A/fA → 0`,   `S_t : 0 → A[f] → A → (f) → 0`

whose Yoneda product is the class `ξ ∈ Ext²_A(M, N)` of the four-term exact sequence
`0 → A[f] → A → A → A/fA → 0`. The argument that `ξ` is not in the image is this. Let
`N ↪ E` be an injective embedding in `Mod(A)` and let `J = Γ_I(E)` be its torsion part; then `J`
is injective *in the torsion category*, because `Γ_I` is right adjoint to the exact inclusion,
and the embedding corestricts to a monomorphism `ι_J : N → J` of torsion modules. Any class
`α ∈ Ext²` of the torsion category composed with `ι_J` therefore vanishes, so the same holds for
the image of `α` in `Ext²_A(M, J)`. But `ξ` composed with `ι_J` is *not* zero: if it were, then
`A` being free, two applications of the long exact sequence of `Ext` in the first variable —
first along `S_q` to cancel `Ext¹_A(A, J) = 0`, then along `S_t` — would extend `ι_J` to an
`A`-linear map `φ : A → J`, and then `ι_J(x) = φ(x) = x · φ(1) = 0` because `J` is torsion,
contradicting `x ≠ 0` and `ι_J` monomorphic.

This replaces the source's argument, which compares four-term exact sequences and is the step
its proof marks "some details omitted": only `Ext¹` and the long exact sequence are used here.

## Main results

* `Dualizing.TorsionExt.not_surjective_mapExt_two_of_infinitelyDivisible` — the criterion: for
  any commutative ring with a nonzero `f`-torsion element divisible by every power of `f`, the
  `Ext²` comparison for `I = (f)` is not surjective.
* `Dualizing.TorsionExt.witness_x_ne_zero`, `Dualizing.TorsionExt.witness_mul_eq_zero`,
  `Dualizing.TorsionExt.witness_dvd` — the explicit witness `ℤ ⋉ (ℚ/ℤ)` has such an element.
* `Dualizing.exists_not_surjective_mapExt_two_powerTorsionModule` — **Stacks 0A6P (3)**.
* `Dualizing.exists_not_isEquivalence_powerTorsionComparison` — **Stacks 0A6P (4)**.
* `Dualizing.bijective_hom_and_ext_one_and_exists_not_surjective_ext_two_and_not_isEquivalence`
  — **the whole of Stacks 0A6P**: the conjunction of its four parts, the first two universally
  quantified and the last two existential, as in the source. Each part is also stated and tagged
  on its own, parts (1) and (2) in
  `StacksFrontier.RingTheory.Dualizing.DerivedTorsion` and parts (3) and (4) here.

## Implementation notes

The witness is the trivial square-zero extension `ℤ ⋉ (ℚ/ℤ)` rather than the source's
presentation by generators and relations: the three properties required of `(f, x)` are then
immediate, whereas for the quotient of a polynomial ring in infinitely many variables even
`x ≠ 0` is a monomial computation. Part (3) is an existential statement, so any witness proves
it.

## References

* [Stacks Project, Tag 0A6P](https://stacks.math.columbia.edu/tag/0A6P)
* [Stacks Project, Tag 0A6N](https://stacks.math.columbia.edu/tag/0A6N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe u v

namespace Dualizing.TorsionExt

section Criterion

variable {A : Type u} [CommRing A] (f : A)

/-- A principal ideal is finitely generated. -/
theorem fg_span_singleton : (Ideal.span {f}).FG :=
  ⟨{f}, by simp⟩

/-- An element divisible by every power of `f` annihilates every `(f)`-power-torsion module. -/
theorem smul_eq_zero_of_isIPowerTorsion {x : A} (hdvd : ∀ n : ℕ, ∃ y : A, x = f ^ n * y)
    {T : Type*} [AddCommGroup T] [Module A T] (hT : IsIPowerTorsion A T (Ideal.span {f}))
    (t : T) : x • t = 0 := by
  obtain ⟨n, -, hkill⟩ := hT t
  obtain ⟨y, hy⟩ := hdvd n
  have h0 : f ^ n • t = 0 :=
    hkill _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self f) n)
  rw [hy, mul_comm, mul_smul, h0, smul_zero]

/-- The quotient map `A ⟶ A/(f)`. -/
def quotMap : A →ₗ[A] (A ⧸ Ideal.span {f}) := (Ideal.span {f}).mkQ

/-- The quotient map `A ⟶ A/(f)` is surjective. -/
theorem quotMap_surjective : Function.Surjective (quotMap f) :=
  fun m ↦ ⟨Quotient.out m, Quotient.out_eq _⟩

/-- `S_q : 0 → (f) → A → A/(f) → 0`, the presentation of `A/(f)` by the free module `A`. -/
abbrev seqQuot : ShortComplex (ModuleCat.{u} A) := (quotMap f).shortComplexKer

/-- The sequence `0 → (f) → A → A/(f) → 0` is short exact. -/
theorem seqQuot_shortExact : (seqQuot f).ShortExact :=
  LinearMap.shortExact_shortComplexKer (quotMap_surjective f)

/-- Multiplication by `f`, as a surjection of `A` onto the kernel of `A ⟶ A/(f)`. -/
def mulByF : A →ₗ[A] (LinearMap.ker (quotMap f)) where
  toFun a := ⟨f * a, by
    change (quotMap f) (f * a) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self f))⟩
  map_add' a b := by apply Subtype.ext; change f * (a + b) = f * a + f * b; ring
  map_smul' c a := by apply Subtype.ext; change f * (c * a) = c * (f * a); ring

/-- Multiplication by `f` maps `A` onto the ideal `(f)`. -/
theorem mulByF_surjective : Function.Surjective (mulByF f) := by
  intro y
  have hy : (y : A) ∈ Ideal.span {f} :=
    (Submodule.Quotient.mk_eq_zero _).mp (show (quotMap f) (y : A) = 0 from y.2)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hy
  exact ⟨b, Subtype.ext hb.symm⟩

/-- `S_t : 0 → A[f] → A → (f) → 0`, multiplication by `f` out of the free module `A`. -/
abbrev seqTors : ShortComplex (ModuleCat.{u} A) := (mulByF f).shortComplexKer

/-- The sequence `0 → A[f] → A → (f) → 0` is short exact. -/
theorem seqTors_shortExact : (seqTors f).ShortExact :=
  LinearMap.shortExact_shortComplexKer (mulByF_surjective f)

/-- The quotient `A/(f)` is `(f)`-power-torsion. -/
theorem isIPowerTorsion_quot :
    IsIPowerTorsion A (A ⧸ Ideal.span {f}) (Ideal.span {f}) := by
  intro m
  refine ⟨1, Nat.one_pos, fun a ha ↦ ?_⟩
  rw [pow_one] at ha
  obtain ⟨b, rfl⟩ : ∃ b, Submodule.Quotient.mk b = m := ⟨Quotient.out m, Quotient.out_eq _⟩
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Ideal.mul_mem_right b _ ha)

/-- The `f`-torsion submodule `A[f]` is `(f)`-power-torsion. -/
theorem isIPowerTorsion_ker :
    IsIPowerTorsion A (LinearMap.ker (mulByF f)) (Ideal.span {f}) := by
  intro m
  refine ⟨1, Nat.one_pos, fun a ha ↦ ?_⟩
  rw [pow_one, Ideal.mem_span_singleton] at ha
  obtain ⟨c, rfl⟩ := ha
  have hm : f * (m : A) = 0 := congrArg Subtype.val m.2
  apply Subtype.ext
  show (f * c) * (m : A) = 0
  rw [mul_comm f c, mul_assoc, hm, mul_zero]

/-- `M = A/(f)`, as an object of the category of `(f)`-power-torsion modules. -/
def quotObj : PowerTorsionModule.{u, u} A (Ideal.span {f}) (fg_span_singleton f) :=
  ⟨(seqQuot f).X₃, isIPowerTorsion_quot f⟩

/-- `N = A[f]`, as an object of the category of `(f)`-power-torsion modules. -/
def torsObj : PowerTorsionModule.{u, u} A (Ideal.span {f}) (fg_span_singleton f) :=
  ⟨(seqTors f).X₁, isIPowerTorsion_ker f⟩

attribute [local instance] HasDerivedCategory.standard CategoryTheory.HasExt.standard

/-- The class in `Ext²_A(A/fA, A[f])` of the four-term exact sequence
`0 → A[f] → A → A → A/fA → 0`, as the Yoneda product of the classes of
`Dualizing.TorsionExt.seqQuot` and `Dualizing.TorsionExt.seqTors`. -/
def extTwoClass :
    Ext ((powerTorsionModuleProperty A (Ideal.span {f}) (fg_span_singleton f)).ι.obj (quotObj f))
      ((powerTorsionModuleProperty A (Ideal.span {f}) (fg_span_singleton f)).ι.obj (torsObj f))
      2 :=
  ((seqQuot_shortExact f).extClass).comp ((seqTors_shortExact f).extClass)
    (show 1 + 1 = 2 by norm_num)

/-- **Stacks 0A6P (3), the criterion.** Let `A` be a commutative ring and `f, x ∈ A` with
`f * x = 0`, with `x ≠ 0`, and with `x` divisible by every power of `f`. Then the comparison map
on `Ext²` from the category of `(f)`-power-torsion modules to `Mod(A)` is not surjective, for
`M = A/fA` and `N = A[f]`.

The class not in the image is `Dualizing.TorsionExt.extTwoClass`, the Yoneda product of the two
presentations of `M` and `A[f]` by the free module `A`. -/
theorem not_surjective_mapExt_two_of_infinitelyDivisible
    {x : A} (hfx : f * x = 0) (hx : x ≠ 0) (hdvd : ∀ n : ℕ, ∃ y : A, x = f ^ n * y) :
    ¬ Function.Surjective
      ((powerTorsionModuleProperty A (Ideal.span {f}) (fg_span_singleton f)).ι.mapExtAddHom
        (quotObj f) (torsObj f) 2) := by
  let _ : EnoughInjectives (ModuleCat.{u} A) := ModuleCat.enoughInjectives A
  have _ : Module.Projective A A := inferInstance
  have h12 : (1 : ℕ) + 1 = 2 := by norm_num
  intro hsurj
  let P := powerTorsionModuleProperty A (Ideal.span {f}) (fg_span_singleton f)
  let N : PowerTorsionModule.{u, u} A (Ideal.span {f}) (fg_span_singleton f) := torsObj f
  let M : PowerTorsionModule.{u, u} A (Ideal.span {f}) (fg_span_singleton f) := quotObj f
  -- an injective embedding of `N` in `Mod(A)`, and its torsion part
  let E : ModuleCat.{u} A := Injective.under (P.ι.obj N)
  let adj : P.ι ⊣ powerTorsionFunctor.{u, u} A (Ideal.span {f}) :=
    powerTorsionAdjunction.{u, u} A (Ideal.span {f})
  let J : PowerTorsionModule.{u, u} A (Ideal.span {f}) (fg_span_singleton f) :=
    (powerTorsionFunctor.{u, u} A (Ideal.span {f})).obj E
  have hJinj : Injective J := adj.map_injective E inferInstance
  let iotaJ : N ⟶ J := (adj.homEquiv N E) (Injective.ι (P.ι.obj N))
  have hgfac : P.ι.map iotaJ ≫ adj.counit.app E = Injective.ι (P.ι.obj N) :=
    (adj.homEquiv N E).symm_apply_apply _
  have hgmono : Mono (P.ι.map iotaJ) := by
    have : Mono (P.ι.map iotaJ ≫ adj.counit.app E) := by rw [hgfac]; infer_instance
    exact mono_of_mono (P.ι.map iotaJ) (adj.counit.app E)
  -- the image of any torsion `Ext²` class dies after composing with `ι_J`
  have key : ∀ β : Ext M N 2,
      (P.ι.mapExtAddHom M N 2 β).comp (Ext.mk₀ (P.ι.map iotaJ)) (add_zero 2) = 0 := by
    intro β
    rw [Functor.mapExtAddHom_apply, ← Ext.mapExactFunctor_mk₀, ← Ext.mapExactFunctor_comp,
      Ext.eq_zero_of_injective (β.comp (Ext.mk₀ iotaJ) (add_zero 2)),
      Ext.mapExactFunctor_zero]
  obtain ⟨α, hα⟩ := hsurj (extTwoClass f)
  have h2 : (extTwoClass f).comp (Ext.mk₀ (P.ι.map iotaJ)) (add_zero 2) = 0 := by
    rw [← hα]; exact key α
  -- but it does not: unwind the Yoneda product
  have hassoc := Ext.comp_assoc_of_third_deg_zero ((seqQuot_shortExact f).extClass)
    ((seqTors_shortExact f).extClass) (Ext.mk₀ (P.ι.map iotaJ)) h12
  have h3 := hassoc.symm.trans h2
  have hprojQ : Projective (seqQuot f).X₂ := inferInstance
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ (seqQuot_shortExact f) (P.ι.obj J)
    (((seqTors_shortExact f).extClass).comp (Ext.mk₀ (P.ι.map iotaJ)) (add_zero 1)) h12 h3
  have hy0 : ((seqTors_shortExact f).extClass).comp
      (Ext.mk₀ (P.ι.map iotaJ)) (add_zero 1) = 0 := by
    rw [← hy, Ext.eq_zero_of_projective y, Ext.comp_zero]
  obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₁ (seqTors_shortExact f) (P.ι.obj J)
    (Ext.mk₀ (P.ι.map iotaJ)) (add_zero 1) hy0
  rw [← Ext.mk₀_homEquiv₀_apply z, Ext.mk₀_comp_mk₀] at hz
  have hfφ : (seqTors f).f ≫ Ext.homEquiv₀ z = P.ι.map iotaJ :=
    Ext.homEquiv₀.symm.injective hz
  -- the contradiction: `x` annihilates the torsion module `J`
  have hxmem : (mulByF f) x = 0 := Subtype.ext hfx
  let xN : (P.ι.obj N : ModuleCat.{u} A) := ⟨x, hxmem⟩
  have hval : (P.ι.map iotaJ).hom xN = (Ext.homEquiv₀ z).hom x :=
    (congrArg (fun (h : (seqTors f).X₁ ⟶ P.ι.obj J) ↦ h.hom xN) hfφ).symm
  have h0 : (Ext.homEquiv₀ z).hom x = 0 := by
    have hxx : (Ext.homEquiv₀ z).hom x = x • (Ext.homEquiv₀ z).hom 1 := by
      rw [← map_smul]; simp
    rw [hxx]
    exact smul_eq_zero_of_isIPowerTorsion f hdvd J.property _
  have hzero : (P.ι.map iotaJ).hom xN = 0 := by rw [hval, h0]
  have hxzero : xN = 0 := by
    have hinj := (ModuleCat.mono_iff_injective (P.ι.map iotaJ)).mp hgmono
    apply hinj
    rw [hzero, map_zero]
  exact hx
    (congrArg (fun m : (P.ι.obj N : ModuleCat.{u} A) ↦ ((seqTors f).f).hom m) hxzero)

end Criterion

section Witness

/-- `ℚ/ℤ`, as a `ℤ`-module: a nonzero torsion module in which every element is divisible by
every integer. -/
abbrev RatModInt : Type := ℚ ⧸ Submodule.span ℤ {(1 : ℚ)}

/-- The ring homomorphism `ℤᵐᵒᵖ → ℤ` given by `MulOpposite.unop`, using commutativity of `ℤ`. -/
def opUnopInt : ℤᵐᵒᵖ →+* ℤ where
  toFun := MulOpposite.unop
  map_one' := rfl
  map_mul' _ _ := mul_comm _ _
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The right `ℤ`-module structure on `ℚ/ℤ`, equal to the left one. -/
instance : Module ℤᵐᵒᵖ RatModInt := Module.compHom RatModInt opUnopInt

/-- The left and right actions of `ℤ` on `ℚ/ℤ` agree. -/
instance : IsCentralScalar ℤ RatModInt := ⟨fun _ _ ↦ rfl⟩

/-- The witness ring `ℤ ⋉ (ℚ/ℤ)`: the trivial square-zero extension of `ℤ` by `ℚ/ℤ`. It plays
the role of the source's `ℤ[f, x, xₙ]/(fx, fⁿxₙ - x)`. -/
abbrev WitnessRing : Type := TrivSqZeroExt ℤ RatModInt

/-- The element `f = 2` of the witness ring. -/
def witnessF : WitnessRing := TrivSqZeroExt.inl 2

/-- The element `x = (1/2 mod ℤ)` of the witness ring: it is nonzero, killed by `f = 2`, and
divisible by every power of `2`. -/
def witnessX : WitnessRing :=
  TrivSqZeroExt.inr (Submodule.Quotient.mk ((1 : ℚ) / 2))

/-- Multiplying `inr (q mod ℤ)` by `inl k` in the witness ring multiplies `q` by `k`. -/
private theorem inl_mul_inr_mk (k : ℤ) (q : ℚ) :
    (TrivSqZeroExt.inl k : WitnessRing) * TrivSqZeroExt.inr (Submodule.Quotient.mk q : RatModInt) =
      TrivSqZeroExt.inr (Submodule.Quotient.mk (k • q)) := by
  rw [TrivSqZeroExt.inl_mul_inr]; rfl

/-- In the witness ring, `f * x = 0`. -/
theorem witness_mul_eq_zero : witnessF * witnessX = 0 := by
  rw [witnessF, witnessX, inl_mul_inr_mk, show ((2 : ℤ) • ((1 : ℚ) / 2)) = (1 : ℚ) by norm_num,
    (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self _)]
  exact TrivSqZeroExt.inr_zero ℤ

/-- In the witness ring, `x ≠ 0`. -/
theorem witness_x_ne_zero : witnessX ≠ 0 := by
  intro h
  have h2 : (Submodule.Quotient.mk ((1 : ℚ) / 2) : RatModInt) = 0 :=
    TrivSqZeroExt.inr_injective (R := ℤ) (M := RatModInt)
      (h.trans (TrivSqZeroExt.inr_zero ℤ).symm)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp ((Submodule.Quotient.mk_eq_zero _).mp h2)
  rw [zsmul_eq_mul, mul_one] at ha
  have h3 : (2 : ℚ) * (a : ℚ) = 1 := by rw [ha]; norm_num
  have h4 : (2 * a : ℤ) = 1 := by exact_mod_cast h3
  omega

/-- In the witness ring, `x` is divisible by `f ^ n` for every `n`. -/
theorem witness_dvd (n : ℕ) :
    ∃ y : WitnessRing, witnessX = witnessF ^ n * y := by
  refine ⟨TrivSqZeroExt.inr (Submodule.Quotient.mk ((1 : ℚ) / 2 ^ (n + 1))), ?_⟩
  have hpow : (witnessF : WitnessRing) ^ n = TrivSqZeroExt.inl (2 ^ n) := by
    simp [witnessF]
  have hq : ((2 : ℤ) ^ n) • ((1 : ℚ) / 2 ^ (n + 1)) = (1 : ℚ) / 2 := by
    rw [zsmul_eq_mul]
    push_cast
    rw [pow_succ]
    field_simp
  rw [hpow, inl_mul_inr_mk, witnessX, hq]

end Witness

end Dualizing.TorsionExt

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard CategoryTheory.HasExt.standard

/-- **Stacks 0A6P (3).** The comparison map
`Ext²_{D(I^∞-torsion)}(M, N) ⟶ Ext²_{D(A)}(M, N)` between `I`-power-torsion modules is not
surjective in general: there is a commutative ring `A`, a finitely generated (indeed principal)
ideal `I`, and `I`-power-torsion modules `M` and `N` for which the inclusion of the torsion
category does not hit every class of `Ext²_A(M, N)`.

Parts (1) and (2) of the source, that the comparison is bijective on `Hom` and on `Ext¹`, are
`Dualizing.bijective_derivedInclusion_map_singleFunctor` and
`Dualizing.bijective_mapExt_one_powerTorsionModule`. -/
@[stacks 0A6P "part (3)"]
theorem exists_not_surjective_mapExt_two_powerTorsionModule :
    ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (hI : I.FG)
      (M N : PowerTorsionModule.{0, 0} A I hI),
      ¬ Function.Surjective
        ((powerTorsionModuleProperty A I hI).ι.mapExtAddHom M N 2) :=
  ⟨TorsionExt.WitnessRing, inferInstance, Ideal.span {TorsionExt.witnessF},
    TorsionExt.fg_span_singleton _, TorsionExt.quotObj _, TorsionExt.torsObj _,
    TorsionExt.not_surjective_mapExt_two_of_infinitelyDivisible _
      TorsionExt.witness_mul_eq_zero TorsionExt.witness_x_ne_zero TorsionExt.witness_dvd⟩

/-- **Stacks 0A6P (4).** The comparison functor of Stacks 0A6N,
`D(I^∞-torsion) ⟶ D_{I^∞-torsion}(A)`, is not an equivalence in general.

This is part (3) together with
`Dualizing.not_isEquivalence_powerTorsionComparison_of_not_surjective_mapExt`: an equivalence
would be bijective on `Extⁿ` in every degree. -/
@[stacks 0A6P "part (4)"]
theorem exists_not_isEquivalence_powerTorsionComparison :
    ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (hI : I.FG),
      ¬ (powerTorsionComparison.{0, 0} A I hI).IsEquivalence := by
  obtain ⟨A, hA, I, hI, M, N, hns⟩ := exists_not_surjective_mapExt_two_powerTorsionModule
  exact ⟨A, hA, I, hI,
    not_isEquivalence_powerTorsionComparison_of_not_surjective_mapExt A I hI M N 2 hns⟩

/-- **Stacks 0A6P, all four parts.** For every ring `A`, every finitely generated ideal
`I ⊆ A` and all `I`-power-torsion `A`-modules `M` and `N`:

1. `Hom_{D(A)}(M, N) = Hom_{D(I^∞-torsion)}(M, N)`;
2. `Ext¹_{D(A)}(M, N) = Ext¹_{D(I^∞-torsion)}(M, N)`;
3. `Ext²_{D(I^∞-torsion)}(M, N) ⟶ Ext²_{D(A)}(M, N)` is not surjective in general;
4. the comparison functor `D(I^∞-torsion) ⟶ D_{I^∞-torsion}(A)` of Stacks 0A6N is not an
   equivalence in general.

Parts (1) and (2) are universally quantified and parts (3) and (4) are existential, exactly as
in the source. The four conjuncts are
`Dualizing.bijective_derivedInclusion_map_singleFunctor`,
`Dualizing.bijective_mapExt_one_powerTorsionModule`,
`Dualizing.exists_not_surjective_mapExt_two_powerTorsionModule` and
`Dualizing.exists_not_isEquivalence_powerTorsionComparison`, each of which carries the tag for
its own clause. -/
@[stacks 0A6P "all four parts conjoined"]
theorem bijective_hom_and_ext_one_and_exists_not_surjective_ext_two_and_not_isEquivalence :
    (∀ (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
        (M N : PowerTorsionModule.{u, v} A I hI),
        Function.Bijective fun f :
            (DerivedCategory.singleFunctor (PowerTorsionModule.{u, v} A I hI) 0).obj M ⟶
              (DerivedCategory.singleFunctor (PowerTorsionModule.{u, v} A I hI) 0).obj N ↦
          (powerTorsionModuleProperty A I hI).ι.mapDerivedCategory.map f) ∧
      (∀ (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
        (M N : PowerTorsionModule.{u, v} A I hI),
        Function.Bijective ((powerTorsionModuleProperty A I hI).ι.mapExtAddHom M N 1)) ∧
      (∃ (A : Type) (_ : CommRing A) (I : Ideal A) (hI : I.FG)
        (M N : PowerTorsionModule.{0, 0} A I hI),
        ¬ Function.Surjective
          ((powerTorsionModuleProperty A I hI).ι.mapExtAddHom M N 2)) ∧
      (∃ (A : Type) (_ : CommRing A) (I : Ideal A) (hI : I.FG),
        ¬ (powerTorsionComparison.{0, 0} A I hI).IsEquivalence) :=
  ⟨fun A _ I hI M N ↦ bijective_derivedInclusion_map_singleFunctor.{u, v} A I hI M N,
    fun A _ I hI M N ↦ bijective_mapExt_one_powerTorsionModule.{u, v} A I hI M N,
    exists_not_surjective_mapExt_two_powerTorsionModule,
    exists_not_isEquivalence_powerTorsionComparison⟩

end Dualizing

end
