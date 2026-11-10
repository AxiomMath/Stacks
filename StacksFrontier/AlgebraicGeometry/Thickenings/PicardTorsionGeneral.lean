module

public import StacksFrontier.AlgebraicGeometry.Picard.FirstCohomologyNaturality
public import StacksFrontier.AlgebraicGeometry.Picard.PurelyInseparablePullback
public import StacksFrontier.AlgebraicGeometry.Thickenings.PicardSequence
public import StacksFrontier.RingTheory.Nilpotent.Lifting

/-!
# Torsion in the Picard group of an arbitrary thickening

Let `i : X ⟶ X'` be a thickening of schemes and let `n` be an integer invertible in `𝒪_X`.
Restriction of invertible modules along `i` is then a bijection from the `n`-torsion of
`Pic(X')` onto the `n`-torsion of `Pic(X)` if and only if every invertible global function on
`X` is an `n`-th power times the restriction of an invertible global function on `X'`.

The mechanism is the short exact sequence of sheaves of abelian groups
`0 ⟶ 𝒦 ⟶ 𝒪_{X'}^* ⟶ i_* 𝒪_X^* ⟶ 0` on `X'`, where `𝒦` is the kernel of restriction of units;
over an affine open `U` of `X'` the group `𝒦(U)` is the group of units of `Γ(X', U)`
congruent to `1` modulo the ideal of `X`, which is a locally nilpotent ideal because the
thickening is surjective.  Raising to the `n`th power is therefore bijective on `𝒦(U)` by
[Stacks, Tag 0CAP], so multiplication by `n` is an automorphism of `𝒦` and hence of
`H^k(X', 𝒦)` in every degree.  The long exact cohomology sequence then gives the bijection on
torsion, the first Leray edge map `H¹(X', i_* 𝒪_X^*) ⟶ H¹(X, 𝒪_X^*)` being invertible because
`i` is a closed immersion, and the identification of first cohomology of the sheaf of units
with the Picard group being natural in the scheme.

## Main results

* `Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_of_globalUnitsPowerLift`:
  [Stacks, Tag 0C6S] in its corrected form (an erratum; see the implementation notes), assuming
  `Stacks.Thickenings.GlobalUnitsPowerLift`.  This is what carries the tag here.
* `Stacks.Thickenings.surjOn_schemePullbackClass_zsmulTorsion_of_isThickening`: the
  surjectivity half, with no hypothesis beyond the original statement's.
* `Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_iff`: the bijection of
  [Stacks, Tag 0C6S] for an arbitrary thickening, as an equivalence with the condition
  `Stacks.Thickenings.GlobalUnitsPowerLift` on invertible global functions.  The tag as
  originally printed asserts the bijection with no such condition; see the implementation
  notes.
* `Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_of_isThickening`: its sufficiency
  half under the stronger hypothesis that global units lift along the thickening.
* `Stacks.Thickenings.unitsKernelShortComplex_shortExact`: the short exact sequence of sheaves
  of [Stacks, Tag 0C6R] for an arbitrary thickening, with `(1 + ℐ)^*` presented as the kernel
  of restriction of units.
* `Stacks.Thickenings.bijOn_cohomologyUnitsRestriction_zsmulTorsion_iff`: the same equivalence,
  in the spelling of first cohomology of the sheaves of units.
* `Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_iff_cohomology`: that the two
  spellings are the same statement.

## Implementation notes

**[Stacks, Tag 0C6S] is false as originally printed, and `Stacks.Thickenings.GlobalUnitsPowerLift`
is the correction: it is proved here to be exactly equivalent to the tag's conclusion, and a
thickening violating it is exhibited in
`StacksFrontier/Examples/Scheme/TwistedDoubledLineUnits.lean`.
The tag is registered on the corrected statement, which assumes the
condition.**  The original statement asserts the bijection with
no hypothesis beyond invertibility of `n`,
but the exact sequence of [Stacks, Tag 0C6R] that its proof invokes,
`H⁰(X', 𝒪_{X'}^*) ⟶ H⁰(X, 𝒪_X^*) --δ--> H¹(X', 𝒦) ⟶ Pic(X') ⟶ Pic(X) ⟶ H²(X', 𝒦)`,
continues to the left, so the kernel of `Pic(X') ⟶ Pic(X)` is not `H¹(X', 𝒦)` but its quotient
by the image of `δ`.  Multiplication by `n` is bijective on `H¹(X', 𝒦)`, which is what the
source's argument supplies, and that does give surjectivity — proved here with no extra
hypothesis.  It does not give injectivity: a quotient of a group on which `n` acts bijectively
by a subgroup that is not `n`-divisible does have `n`-torsion, `ℤ[1/2]/ℤ` with `n = 2` being the
pattern.  What injectivity needs is that the image of `δ` be saturated for multiplication by
`n`, and since `n` is bijective on `H¹(X', 𝒦)` and the sequence is exact at `H⁰(X, 𝒪_X^*)`,
that saturation is equivalent to: every invertible global function on `X` is an `n`-th power
times the restriction of an invertible global function on `X'`.  That is
`Stacks.Thickenings.GlobalUnitsPowerLift`, and the equivalence is both directions of
`Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_iff`, so the hypothesis is not merely
sufficient but necessary: the bijection of the tag fails for any thickening with an invertible
global function on `X` that is not such a product.  The condition holds whenever the invertible
global functions on `X` are `n`-divisible — for instance on a connected proper scheme over an
algebraically closed field with `n` invertible — and whenever every invertible global function
on `X` lifts to `X'`, which is the form in which the source's argument is complete and is the
hypothesis `hunits` of
`Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_of_isThickening`.

Such a thickening exists, so the equivalence above refutes the tag rather than merely leaving it
unproved.  Over `ℚ`, let `X` be the affine line over `ℚ[t, t⁻¹]` with its origin doubled — two
copies of `Spec ℚ[t,t⁻¹][x]` glued along the basic open of `x` by the identity — so that
`Γ(X, 𝒪_X) = ℚ[t,t⁻¹][x]` and `t` is an invertible global function, and let `X ⊂ X'` be the
first-order thickening with ideal `𝒪_X` obtained by gluing two copies of
`Spec ℚ[t,t⁻¹][x][ε]`, `ε² = 0`, along the twist `b ↦ b + ε x⁻¹ (t ∂/∂t) b`.  Two is invertible
in `𝒪_X`.  A global function on `X'` restricts to a `p` with `x ∣ (t ∂/∂t) p` applied
coefficientwise, and `t = a² p` has no such solution — this is
`StacksFrontier/Examples/Scheme/TwistedDoubledLineUnits.lean` — so `GlobalUnitsPowerLift` fails for
`n = 2` and `Pic(X')[2] ⟶ Pic(X)[2]` is not injective: the class of the invertible function
`1 + ½ x⁻¹ε` on the glueing locus is a nonzero `2`-torsion class of `Pic(X')` restricting to `0`,
its square `1 + x⁻¹ε` being the comparison of the two lifts of `t` and hence a coboundary.  That
thickening is assembled as a thickening of schemes in
`StacksFrontier/Examples/Scheme/TwistedDoubledLineThickening.lean`, where the equivalence proved
here turns it into
`Stacks.Examples.TwistedDoubledLine.not_forall_bijOn_schemePullbackClass_zsmulTorsion`, the
negation of the tag as printed.
That refutation is what the erratum rests on, and the counterexample is kept for it.  The tag is
registered on the corrected statement,
`Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_of_globalUnitsPowerLift`; the
surjectivity half remains available separately, needing no such hypothesis.

Cohomology is Mathlib's `CategoryTheory.Sheaf.H`, the `Ext`-groups out of the constant sheaf of
integers, so the long exact sequence of a short exact sequence of sheaves is available with no
transport; the Picard group is reached through the degree-one comparison with right-derived
global sections, in which the identification of [Stacks, Tag 09NU] and its naturality are
stated.

## References

* [Stacks Project, Tag 0C6S](https://stacks.math.columbia.edu/tag/0C6S)
* [Stacks Project, Tag 0C6R](https://stacks.math.columbia.edu/tag/0C6R)
* [Stacks Project, Tag 0CAP](https://stacks.math.columbia.edu/tag/0CAP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Thickenings

open Stacks.Cohomology.Generators (unitsSheaf)
open Stacks.Cohomology.LerayLowDegree (abelianSections abelianPushforward abelianCohomology
  abelianEdgeMap abelianEdgeMap_injective abelianSecondEdgeMap abelianExact)
open Stacks.Picard.FirstCohomology (h1UnitsRightDerived h1UnitsAddEquivPicard
  h1UnitsAddEquivPicard_naturality)
open Stacks.GlueSquishUnits (unitsPushforwardMap unitsPushforwardMap_app)
open Stacks.Picard (zsmulTorsion ofScheme schemePullbackClass schemePullbackClassHom)

attribute [local implicit_reducible] TopCat.Sheaf

attribute [local instance] hasExtAbelianSheaf

/-! ### Transporting torsion statements along isomorphisms -/

section AbstractTorsion

variable {A B A' B' : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup A']
  [AddCommGroup B']

/-- An additive equivalence preserves `n`-torsion. -/
private theorem zsmul_equiv_eq_zero_iff {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (n : ℤ) (x : A) : n • e x = 0 ↔ n • x = 0 := by
  rw [← map_zsmul, map_eq_zero_iff e e.injective]

/-- Transport a bijection on `n`-torsion along isomorphisms of the source and the target. -/
private theorem bijOn_zsmulTorsion_conjugate (f : A → B) (g : A' → B') (eA : A ≃+ A')
    (eB : B ≃+ B') (h : ∀ x, g (eA x) = eB (f x)) (n : ℤ)
    (hf : Set.BijOn f (zsmulTorsion A n) (zsmulTorsion B n)) :
    Set.BijOn g (zsmulTorsion A' n) (zsmulTorsion B' n) := by
  have heA := zsmul_equiv_eq_zero_iff eA n
  have heB := zsmul_equiv_eq_zero_iff eB n
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨x, rfl⟩ := eA.surjective x
    change n • g (eA x) = 0
    rw [h, heB]
    exact hf.1 ((heA x).mp hx)
  · intro x hx y hy hxy
    obtain ⟨x, rfl⟩ := eA.surjective x
    obtain ⟨y, rfl⟩ := eA.surjective y
    exact congrArg eA (hf.2.1 ((heA x).mp hx) ((heA y).mp hy)
      (eB.injective (by simpa only [← h] using hxy)))
  · intro y hy
    obtain ⟨y, rfl⟩ := eB.surjective y
    obtain ⟨x, hx, hxy⟩ := hf.2.2 ((heB y).mp hy)
    exact ⟨eA x, (heA x).mpr hx, by rw [h, hxy]⟩

/-- Bijectivity on `n`-torsion is invariant under conjugation by isomorphisms of the source and
the target. -/
private theorem bijOn_zsmulTorsion_conjugate_iff (f : A → B) (g : A' → B') (eA : A ≃+ A')
    (eB : B ≃+ B') (h : ∀ x, g (eA x) = eB (f x)) (n : ℤ) :
    Set.BijOn f (zsmulTorsion A n) (zsmulTorsion B n) ↔
      Set.BijOn g (zsmulTorsion A' n) (zsmulTorsion B' n) := by
  refine ⟨bijOn_zsmulTorsion_conjugate f g eA eB h n, fun hg => ?_⟩
  refine bijOn_zsmulTorsion_conjugate g f eA.symm eB.symm (fun x => ?_) n hg
  apply eB.injective
  rw [AddEquiv.apply_symm_apply, ← h, AddEquiv.apply_symm_apply]

/-- Transport a surjection on `n`-torsion along isomorphisms of the source and the target. -/
private theorem surjOn_zsmulTorsion_conjugate (f : A → B) (g : A' → B') (eA : A ≃+ A')
    (eB : B ≃+ B') (h : ∀ x, g (eA x) = eB (f x)) (n : ℤ)
    (hf : Set.SurjOn f (zsmulTorsion A n) (zsmulTorsion B n)) :
    Set.SurjOn g (zsmulTorsion A' n) (zsmulTorsion B' n) := by
  have heA := zsmul_equiv_eq_zero_iff eA n
  have heB := zsmul_equiv_eq_zero_iff eB n
  intro y hy
  obtain ⟨y, rfl⟩ := eB.surjective y
  obtain ⟨x, hx, hxy⟩ := hf ((heB y).mp hy)
  exact ⟨eA x, (heA x).mpr hx, by rw [h, hxy]⟩

/-- The converse of `Stacks.Thickenings.injOn_zsmul_of_exact`: along an exact `E → A → B → C`,
injectivity of the last map on the `n`-torsion of `B` forces the image of `E` in `A` to be
saturated for multiplication by `n`.  Indeed if `n • a` comes from `E` then `f a` is `n`-torsion
and dies in `C`, so `f a = 0`, so `a` comes from `E`. -/
private theorem saturated_of_injOn_zsmul_of_exact {E A B C : Type*} [AddCommGroup E]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (e : E →+ A) (f : A →+ B) (g : B →+ C)
    (hef : Function.Exact e f) (hfg : Function.Exact f g) (n : ℤ)
    (hinj : Set.InjOn g (zsmulTorsion B n)) (a : A) (ha : n • a ∈ Set.range e) :
    a ∈ Set.range e := by
  have hfa : n • f a = 0 := by
    rw [← map_zsmul]
    exact (hef (n • a)).mpr ha
  refine (hef a).mp (hinj hfa (show n • (0 : B) = 0 from smul_zero n) ?_)
  rw [map_zero]
  exact (hfg (f a)).mpr ⟨a, rfl⟩

end AbstractTorsion

/-! ### Units congruent to one modulo a locally nilpotent ideal -/

section Ring

variable {R S : Type*} [CommRing R] [CommRing S]

/-- For a locally nilpotent ideal `I`, the subtype `1 + I` of the ring is the subtype of units
congruent to `1` modulo `I`: an element of `1 + I` differs from `1` by a nilpotent and is
therefore invertible. -/
private def oneAddIdealEquivNearOneUnits (I : Ideal R) (hI : ∀ x ∈ I, IsNilpotent x) :
    Stacks.NilpotentIdeal.PowerMap.OneAddIdeal I ≃ {u : Rˣ // (u : R) - 1 ∈ I} := by
  classical
  have hy (y : Stacks.NilpotentIdeal.PowerMap.OneAddIdeal I) : IsUnit y.1 := by
    have h : y.1 = 1 + (y.1 - 1) := by ring
    rw [h]
    exact (hI _ y.2).isUnit_one_add
  refine
    { toFun := fun y => ⟨(hy y).unit, by simpa [IsUnit.unit_spec (hy y)] using y.2⟩
      invFun := fun u => ⟨u.1, u.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro y
    exact Subtype.ext (IsUnit.unit_spec (hy y))
  · intro u
    apply Subtype.ext
    apply Units.ext
    rfl

/-- The `n`th power map on the units congruent to `1` modulo an ideal. -/
private def nearOneUnitsPow (I : Ideal R) (n : ℕ) (u : {u : Rˣ // (u : R) - 1 ∈ I}) :
    {u : Rˣ // (u : R) - 1 ∈ I} :=
  ⟨u.1 ^ n, by
    simpa only [Units.val_pow_eq_pow_val] using
      (Stacks.NilpotentIdeal.PowerMap.pow_sub_one_mem I u.2 n)⟩

/-- **Stacks Project, Tag 0CAP (1)** for the units congruent to `1`: for a locally nilpotent
ideal `I` and `n ≥ 1` invertible in `R ⧸ I`, raising to the `n`th power is a bijection of the
group of units congruent to `1` modulo `I`. -/
private theorem nearOneUnitsPow_bijective (I : Ideal R) (hI : ∀ x ∈ I, IsNilpotent x) {n : ℕ}
    (hn : 1 ≤ n) (hnu : IsUnit ((n : R ⧸ I))) :
    Function.Bijective (nearOneUnitsPow I n) := by
  let e := oneAddIdealEquivNearOneUnits I hI
  have hc (u : {u : Rˣ // (u : R) - 1 ∈ I}) :
      nearOneUnitsPow I n u = e (Stacks.NilpotentIdeal.PowerMap.powMap I n (e.symm u)) := by
    apply Subtype.ext
    apply Units.ext
    dsimp [e, oneAddIdealEquivNearOneUnits, nearOneUnitsPow,
      Stacks.NilpotentIdeal.PowerMap.powMap]
  rw [funext hc]
  exact e.bijective.comp
    ((Stacks.NilpotentIdeal.PowerMap.powMap_bijective I hI hn hnu).comp e.symm.bijective)

/-- A surjective ring homomorphism with locally nilpotent kernel is surjective on units: a
preimage of a unit has a two-sided inverse up to a nilpotent, hence is a unit. -/
private theorem surjective_unitsMap_of_nil_ker (f : R →+* S) (hf : Function.Surjective f)
    (hker : ∀ x ∈ RingHom.ker f, IsNilpotent x) :
    Function.Surjective (Units.map f.toMonoidHom) := by
  intro u
  obtain ⟨x, hx⟩ := hf u.val
  obtain ⟨y, hy⟩ := hf u.inv
  have hnil : IsNilpotent (x * y - 1) := hker _ (by
    change f (x * y - 1) = 0
    simp [hx, hy])
  have hxunit : IsUnit x := isUnit_of_mul_isUnit_left (by
    simpa using hnil.isUnit_add_one : IsUnit (x * y))
  exact ⟨hxunit.unit, Units.ext ((congrArg f hxunit.unit_spec).trans hx)⟩

/-- The units congruent to `1` modulo the kernel of a ring homomorphism are the kernel of the
induced map on units, written additively. -/
private def nearOneUnitsEquivKernel (f : R →+* S) :
    {u : Rˣ // (u : R) - 1 ∈ RingHom.ker f} ≃
      (Units.map f.toMonoidHom).toAdditive.ker where
  toFun u := ⟨Additive.ofMul u.val, by
    change Additive.ofMul (Units.map f.toMonoidHom u.val) = 0
    apply congrArg Additive.ofMul
    apply Units.ext
    have h := u.property
    change f ((u.val : R) - 1) = 0 at h
    change f (u.val : R) = 1
    simpa only [map_sub, map_one, sub_eq_zero] using h⟩
  invFun u := ⟨Additive.toMul u.val, by
    change f (((Additive.toMul u.val : Rˣ) : R) - 1) = 0
    have h := congrArg (fun x : Additive Sˣ => ((Additive.toMul x : Sˣ) : S)) u.property
    change f ((Additive.toMul u.val : Rˣ) : R) = 1 at h
    simp [h]⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Multiplication by a natural number `n ≥ 1` invertible in the target is bijective on the
kernel of the map on units induced by a surjective ring homomorphism with locally nilpotent
kernel: written multiplicatively, that is the `n`th power map on the units congruent to `1`. -/
private theorem bijective_nsmul_unitsMap_ker (f : R →+* S) (hf : Function.Surjective f)
    (hker : ∀ x ∈ RingHom.ker f, IsNilpotent x) (n : ℕ) (hn : 1 ≤ n) (hnu : IsUnit (n : S)) :
    Function.Bijective (fun x : (Units.map f.toMonoidHom).toAdditive.ker => n • x) := by
  let e := nearOneUnitsEquivKernel f
  have hquot : IsUnit (n : R ⧸ RingHom.ker f) := by
    simpa using hnu.map (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom
  have hpow := nearOneUnitsPow_bijective (RingHom.ker f) hker hn hquot
  have he (x) : e (nearOneUnitsPow (RingHom.ker f) n x) = n • e x := rfl
  constructor
  · intro x y hxy
    apply e.symm.injective
    apply hpow.1
    apply e.injective
    simpa only [he, e.apply_symm_apply] using hxy
  · intro y
    obtain ⟨x, hx⟩ := hpow.2 (e.symm y)
    refine ⟨e x, ?_⟩
    change n • e x = y
    rw [← he, hx, e.apply_symm_apply]

/-- Multiplication by an integer invertible in the target is bijective on the kernel of the map
on units induced by a surjective ring homomorphism with locally nilpotent kernel. -/
private theorem bijective_zsmul_unitsMap_ker (f : R →+* S) (hf : Function.Surjective f)
    (hker : ∀ x ∈ RingHom.ker f, IsNilpotent x) (n : ℤ) (hnu : IsUnit ((n : ℤ) : S)) :
    Function.Bijective (fun x : (Units.map f.toMonoidHom).toAdditive.ker => n • x) := by
  rcases n with n | n
  · cases n with
    | zero =>
      have h01 : (0 : S) = 1 := isUnit_zero_iff.mp (by simpa using hnu)
      obtain ⟨k, hk⟩ := hker 1 (by simpa [RingHom.mem_ker] using h01.symm)
      have : Subsingleton R := subsingleton_of_zero_eq_one (by simpa using hk.symm)
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
    | succ n =>
      simpa only [Int.ofNat_eq_natCast, natCast_zsmul] using
        bijective_nsmul_unitsMap_ker f hf hker (n + 1) (Nat.succ_pos n) (by simpa using hnu)
  · have hn : IsUnit ((n + 1 : ℕ) : S) := by
      simpa using hnu.neg
    have hb := bijective_nsmul_unitsMap_ker f hf hker (n + 1) (Nat.succ_pos n) hn
    have hneg := (Equiv.neg ((Units.map f.toMonoidHom).toAdditive.ker)).bijective.comp hb
    simpa only [Function.comp_def, Equiv.neg_apply, negSucc_zsmul] using hneg

end Ring

/-! ### The kernel of restriction of units along a thickening -/

section Sheaves

variable {X X' : Scheme.{u}}

/-- Along a thickening, a function on an affine open of the ambient scheme that restricts to
zero is nilpotent: the kernel ideal sheaf has full support, hence is contained in the
nilradical. -/
private theorem isNilpotent_of_mem_ker_app_of_isThickening (i : X ⟶ X') (hi : IsThickening i)
    (U : X'.Opens) (hU : IsAffineOpen U) (s : Γ(X', U)) (hs : (i.app U).hom s = 0) :
    IsNilpotent s := by
  let : IsClosedImmersion i := hi.1
  have hsupport : i.ker.support = ⊤ := by
    apply TopologicalSpace.Closeds.ext
    rw [Scheme.Hom.support_ker, Set.range_eq_univ.mpr hi.2, closure_univ]
    rfl
  have hker : i.ker ≤ X'.nilradical := by
    calc
      i.ker ≤ i.ker.radical := Scheme.IdealSheafData.le_radical _
      _ = X'.nilradical := by
        rw [← Scheme.IdealSheafData.vanishingIdeal_support, hsupport,
          Scheme.IdealSheafData.vanishingIdeal_top]
  have hs' : s ∈ i.ker.ideal ⟨U, hU⟩ := by
    simpa only [Scheme.Hom.ker_apply, RingHom.mem_ker] using hs
  exact (show s ∈ Ideal.radical (⊥ : Ideal Γ(X', U)) from hker ⟨U, hU⟩ hs')

/-- Restriction of units along a thickening is an epimorphism of sheaves of abelian groups:
over an affine open the map of rings is surjective with locally nilpotent kernel, so a unit
lifts. -/
theorem unitsRestrictionSheafHom_epi_of_isThickening (i : X ⟶ X') (hi : IsThickening i) :
    Epi (unitsRestrictionSheafHom i) := by
  let : IsClosedImmersion i := hi.1
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  obtain ⟨s, hs⟩ := surjective_unitsMap_of_nil_ker (i.app V).hom (i.app_surjective V hV)
    (isNilpotent_of_mem_ker_app_of_isThickening i hi V hV)
    (Additive.toMul ((pushforwardUnitsSheaf i).obj.map (homOfLE hVU).op t))
  exact ⟨V, hVU, ⟨Additive.ofMul s, congrArg Additive.ofMul hs⟩, hxV⟩

/-- For an integer `n` invertible in `𝒪_X`, multiplication by `n` is an automorphism of the
kernel of restriction of units along a thickening: over an affine open the kernel is the group
of units congruent to `1` modulo a locally nilpotent ideal, on which the `n`th power map is
bijective by [Stacks, Tag 0CAP]. -/
theorem isIso_zsmul_kernel_unitsRestrictionSheafHom (i : X ⟶ X') (hi : IsThickening i) (n : ℤ)
    (hn : IsUnit ((n : ℤ) : Γ(X, ⊤))) :
    IsIso (n • 𝟙 (kernel (unitsRestrictionSheafHom i))) := by
  let : IsClosedImmersion i := hi.1
  apply TopCat.Sheaf.isIso_iff_isIso_basis
    (B := fun U : X'.affineOpens => U.val)
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using X'.isBasis_affineOpens)
  intro U
  let E := (sheafToPresheaf (Opens.grothendieckTopology X') AddCommGrpCat.{u}) ⋙
    (evaluation (Opens X')ᵒᵖ AddCommGrpCat.{u}).obj (op U.val)
  let e := (PreservesKernel.iso E (unitsRestrictionSheafHom i) ≪≫
    AddCommGrpCat.kernelIsoKer (E.map (unitsRestrictionSheafHom i))).addCommGroupIsoToAddEquiv
  have hnU : IsUnit ((n : ℤ) : Γ(X, i ⁻¹ᵁ U.val)) := by
    simpa using hn.map (X.presheaf.map (homOfLE (show i ⁻¹ᵁ U.val ≤ ⊤ from le_top)).op).hom
  have hb := bijective_zsmul_unitsMap_ker (i.app U.val).hom
    (i.app_surjective U.val U.property)
    (isNilpotent_of_mem_ker_app_of_isThickening i hi U.val U.property) n hnU
  change Function.Bijective
    (fun x : (E.map (unitsRestrictionSheafHom i)).hom.ker => n • x) at hb
  have hb' : Function.Bijective
      (fun x : E.obj (kernel (unitsRestrictionSheafHom i)) => n • x) := by
    constructor
    · intro x y hxy
      apply e.injective
      apply hb.1
      simpa only [map_zsmul] using congrArg e hxy
    · intro y
      obtain ⟨x, hx⟩ := hb.2 (e y)
      refine ⟨e.symm x, e.injective ?_⟩
      simpa only [map_zsmul, e.apply_symm_apply] using hx
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hb'

/-- The short exact sequence of sheaves of abelian groups attached to an arbitrary thickening:
`0 ⟶ 𝒦 ⟶ 𝒪_{X'}^* ⟶ i_* 𝒪_X^* ⟶ 0`, with `𝒦` the kernel of restriction of units. -/
def unitsKernelShortComplex (i : X ⟶ X') :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X') :=
  ShortComplex.mk (kernel.ι (unitsRestrictionSheafHom i)) (unitsRestrictionSheafHom i)
    (kernel.condition _)

/-- **Stacks Project, Tag 0C6R** for an arbitrary thickening: the sequence of sheaves
`0 ⟶ 𝒦 ⟶ 𝒪_{X'}^* ⟶ i_* 𝒪_X^* ⟶ 0` is short exact, where `𝒦` is the kernel of restriction of
units, i.e. the sheaf of units congruent to `1` modulo the ideal of `X`. -/
@[stacks 0C6R "the short exact sequence of sheaves, for an arbitrary thickening, with the \
sheaf of units congruent to one presented as a kernel"]
theorem unitsKernelShortComplex_shortExact (i : X ⟶ X') (hi : IsThickening i) :
    (unitsKernelShortComplex i).ShortExact := by
  let g := unitsRestrictionSheafHom i
  let S := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hmono : Mono S.f := inferInstanceAs (Mono (kernel.ι g))
  have hepi : Epi S.g := unitsRestrictionSheafHom_epi_of_isThickening i hi
  change S.ShortExact
  exact { exact := S.exact_of_f_is_kernel (kernelIsKernel _) }

end Sheaves

/-! ### Torsion in the first cohomology of the sheaves of units -/

section Cohomology

variable {X X' : Scheme.{u}}

/-- Multiplication by an integer is bijective on the cohomology of a sheaf of abelian groups in
every degree as soon as it is an automorphism of the sheaf. -/
private theorem bijective_zsmul_cohomology_of_isIso {Y : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} Y) (n : ℤ) (k : ℕ) (hiso : IsIso (n • 𝟙 F)) :
    Function.Bijective fun y : CategoryTheory.Sheaf.H.{u} F k => n • y := by
  have heq : (fun y : CategoryTheory.Sheaf.H.{u} F k => n • y) =
      cohomologyEquivOfIso (@asIso _ _ _ _ (n • 𝟙 F) hiso) k := by
    funext y
    exact (cohomology_map_zsmul_id_apply _ k n y).symm
  rw [heq]
  exact (cohomologyEquivOfIso (@asIso _ _ _ _ (n • 𝟙 F) hiso) k).bijective

/-- The connecting map `H⁰(X, 𝒪_X^*) → H¹(X', 𝒦)` of the sequence of an arbitrary
thickening. -/
def unitsKernelBoundary (i : X ⟶ X') (hi : IsThickening i) :
    CategoryTheory.Sheaf.H.{u} (pushforwardUnitsSheaf i) 0 →+
      CategoryTheory.Sheaf.H.{u} (kernel (unitsRestrictionSheafHom i)) 1 :=
  cohomologyBoundary (unitsKernelShortComplex_shortExact i hi) 0

/-- Every invertible global function on `X` is an `n`-th power times the restriction of an
invertible global function on `X'`.  For `n` invertible in `𝒪_X` this is exactly the condition
under which restriction is a bijection on `n`-torsion of the Picard groups; see
`Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_iff`. -/
def GlobalUnitsPowerLift (i : X ⟶ X') (n : ℤ) : Prop :=
  ∀ u, ∃ v, ∃ w, u = v ^ n * Units.map (CommRingCat.Hom.hom (i.app ⊤)).toMonoidHom w

/-- If every invertible global function on `X` lifts to `X'`, then every one of them is an `n`-th
power times such a lift: take the `n`-th power to be `1`. -/
theorem globalUnitsPowerLift_of_surjective (i : X ⟶ X') (n : ℤ)
    (hunits : Function.Surjective (Units.map (CommRingCat.Hom.hom (i.app ⊤)).toMonoidHom)) :
    GlobalUnitsPowerLift i n := by
  intro u
  obtain ⟨w, hw⟩ := hunits u
  exact ⟨1, w, by rw [one_zpow, one_mul, hw]⟩

/-- If every invertible global function on `X` is an `n`-th power — as on a connected proper
scheme over an algebraically closed field, for `n` invertible there — then every one of them is
an `n`-th power times a restriction: take the restricted factor to be `1`. -/
theorem globalUnitsPowerLift_of_isPow (i : X ⟶ X') (n : ℤ)
    (hdiv : ∀ u : Γ(X, i ⁻¹ᵁ (⊤ : X'.Opens))ˣ, ∃ v, u = v ^ n) :
    GlobalUnitsPowerLift i n := by
  intro u
  obtain ⟨v, hv⟩ := hdiv u
  exact ⟨v, 1, by rw [map_one, mul_one, hv]⟩

/-- The class of an invertible global function on `X` in degree-zero cohomology of the
pushed-forward sheaf of units. -/
private abbrev unitsClass (i : X ⟶ X') (hT : IsTerminal (⊤ : Opens X'))
    (u : Γ(X, i ⁻¹ᵁ (⊤ : X'.Opens))ˣ) :
    CategoryTheory.Sheaf.H.{u} (pushforwardUnitsSheaf i) 0 :=
  (CategoryTheory.Sheaf.H.equiv₀ (pushforwardUnitsSheaf i) hT).symm (Additive.ofMul u)

/-- The class of an invertible global function on `X'` in degree-zero cohomology of its sheaf of
units. -/
private abbrev ambientUnitsClass (X' : Scheme.{u}) (hT : IsTerminal (⊤ : Opens X'))
    (u : Γ(X', (⊤ : X'.Opens))ˣ) :
    CategoryTheory.Sheaf.H.{u} (unitsSheaf X'.toLocallyRingedSpace.toRingedSpace) 0 :=
  (CategoryTheory.Sheaf.H.equiv₀
    (unitsSheaf X'.toLocallyRingedSpace.toRingedSpace) hT).symm (Additive.ofMul u)

/-- Every degree-zero class of the pushed-forward sheaf of units is the class of an invertible
global function on `X`. -/
private theorem exists_unitsClass (i : X ⟶ X') (hT : IsTerminal (⊤ : Opens X'))
    (y : CategoryTheory.Sheaf.H.{u} (pushforwardUnitsSheaf i) 0) :
    ∃ u : Γ(X, i ⁻¹ᵁ (⊤ : X'.Opens))ˣ, unitsClass i hT u = y :=
  ⟨Additive.toMul (CategoryTheory.Sheaf.H.equiv₀ (pushforwardUnitsSheaf i) hT y),
    (CategoryTheory.Sheaf.H.equiv₀ (pushforwardUnitsSheaf i) hT).symm_apply_apply y⟩

/-- Every degree-zero class of the sheaf of units of `X'` is the class of an invertible global
function on `X'`. -/
private theorem exists_ambientUnitsClass (X' : Scheme.{u}) (hT : IsTerminal (⊤ : Opens X'))
    (y : CategoryTheory.Sheaf.H.{u} (unitsSheaf X'.toLocallyRingedSpace.toRingedSpace) 0) :
    ∃ u : Γ(X', (⊤ : X'.Opens))ˣ, ambientUnitsClass X' hT u = y :=
  ⟨Additive.toMul (CategoryTheory.Sheaf.H.equiv₀
      (unitsSheaf X'.toLocallyRingedSpace.toRingedSpace) hT y),
    (CategoryTheory.Sheaf.H.equiv₀
      (unitsSheaf X'.toLocallyRingedSpace.toRingedSpace) hT).symm_apply_apply y⟩

/-- Taking classes turns multiplication of invertible global functions into addition. -/
private theorem unitsClass_mul (i : X ⟶ X') (hT : IsTerminal (⊤ : Opens X'))
    (a b : Γ(X, i ⁻¹ᵁ (⊤ : X'.Opens))ˣ) :
    unitsClass i hT (a * b) = unitsClass i hT a + unitsClass i hT b :=
  map_add (CategoryTheory.Sheaf.H.equiv₀ (pushforwardUnitsSheaf i) hT).symm _ _

/-- Taking classes turns the `n`-th power into multiplication by `n`. -/
private theorem unitsClass_zpow (i : X ⟶ X') (hT : IsTerminal (⊤ : Opens X'))
    (a : Γ(X, i ⁻¹ᵁ (⊤ : X'.Opens))ˣ) (n : ℤ) :
    unitsClass i hT (a ^ n) = n • unitsClass i hT a :=
  map_zsmul (CategoryTheory.Sheaf.H.equiv₀ (pushforwardUnitsSheaf i) hT).symm n _

/-- Restriction of units on degree-zero cohomology is restriction of invertible global
functions. -/
private theorem unitsToSubCohomology_zero_ambientUnitsClass (i : X ⟶ X')
    (hT : IsTerminal (⊤ : Opens X')) (a : Γ(X', (⊤ : X'.Opens))ˣ) :
    unitsToSubCohomology i 0 (ambientUnitsClass X' hT a) =
      unitsClass i hT (Units.map (CommRingCat.Hom.hom (i.app ⊤)).toMonoidHom a) := by
  have hnat := CategoryTheory.Sheaf.H.equiv₀_symm_naturality (hT := hT)
    (f := unitsRestrictionSheafHom i) (Additive.ofMul a)
  rwa [unitsRestrictionSheafHom_app] at hnat

/-- Taking classes is injective. -/
private theorem unitsClass_injective (i : X ⟶ X') (hT : IsTerminal (⊤ : Opens X'))
    {a b : Γ(X, i ⁻¹ᵁ (⊤ : X'.Opens))ˣ} (h : unitsClass i hT a = unitsClass i hT b) : a = b :=
  congrArg Additive.toMul
    ((CategoryTheory.Sheaf.H.equiv₀ (pushforwardUnitsSheaf i) hT).symm.injective h)

/-- `Stacks.Thickenings.GlobalUnitsPowerLift` read in degree-zero cohomology: every class in
`H⁰(X, 𝒪_X^*)` is `n` times a class plus one restricted from `H⁰(X', 𝒪_{X'}^*)`. -/
private theorem zsmul_add_range_of_globalUnitsPowerLift (i : X ⟶ X')
    {n : ℤ} (hpow : GlobalUnitsPowerLift i n)
    (y : CategoryTheory.Sheaf.H.{u} (pushforwardUnitsSheaf i) 0) :
    ∃ z, ∃ w, y = n • z + unitsToSubCohomology i 0 w := by
  have hT : IsTerminal (⊤ : Opens X') := isTerminalTop
  obtain ⟨u, hu⟩ := exists_unitsClass i hT y
  obtain ⟨v, w₀, huvw⟩ := hpow u
  refine ⟨unitsClass i hT v, ambientUnitsClass X' hT w₀, ?_⟩
  calc y = unitsClass i hT u := hu.symm
    _ = unitsClass i hT (v ^ n * Units.map (CommRingCat.Hom.hom (i.app ⊤)).toMonoidHom w₀) :=
        congrArg (unitsClass i hT) huvw
    _ = unitsClass i hT (v ^ n) +
          unitsClass i hT (Units.map (CommRingCat.Hom.hom (i.app ⊤)).toMonoidHom w₀) :=
        unitsClass_mul i hT _ _
    _ = n • unitsClass i hT v + unitsToSubCohomology i 0 (ambientUnitsClass X' hT w₀) :=
        congrArg₂ (· + ·) (unitsClass_zpow i hT v n)
          (unitsToSubCohomology_zero_ambientUnitsClass i hT w₀).symm

/-- The converse reading: the degree-zero statement in cohomology is
`Stacks.Thickenings.GlobalUnitsPowerLift`. -/
private theorem globalUnitsPowerLift_of_zsmul_add_range (i : X ⟶ X') {n : ℤ}
    (h : ∀ y : CategoryTheory.Sheaf.H.{u} (pushforwardUnitsSheaf i) 0,
      ∃ z, ∃ w, y = n • z + unitsToSubCohomology i 0 w) :
    GlobalUnitsPowerLift i n := by
  have hT : IsTerminal (⊤ : Opens X') := isTerminalTop
  intro u
  obtain ⟨z, w, hzw⟩ := h (unitsClass i hT u)
  obtain ⟨v, hv⟩ := exists_unitsClass i hT z
  obtain ⟨w₀, hw₀⟩ := exists_ambientUnitsClass X' hT w
  refine ⟨v, w₀, unitsClass_injective i hT ?_⟩
  calc unitsClass i hT u = n • z + unitsToSubCohomology i 0 w := hzw
    _ = n • unitsClass i hT v +
          unitsToSubCohomology i 0 (ambientUnitsClass X' hT w₀) :=
        congrArg₂ (· + ·) (congrArg (fun t => n • t) hv.symm)
          (congrArg (unitsToSubCohomology i 0) hw₀.symm)
    _ = unitsClass i hT (v ^ n) +
          unitsClass i hT (Units.map (CommRingCat.Hom.hom (i.app ⊤)).toMonoidHom w₀) :=
        congrArg₂ (· + ·) (unitsClass_zpow i hT v n).symm
          (unitsToSubCohomology_zero_ambientUnitsClass i hT w₀)
    _ = unitsClass i hT (v ^ n * Units.map (CommRingCat.Hom.hom (i.app ⊤)).toMonoidHom w₀) :=
        (unitsClass_mul i hT _ _).symm

/-- The saturation that injectivity needs follows from
`Stacks.Thickenings.GlobalUnitsPowerLift`: the part of a class of `H⁰(X, 𝒪_X^*)` restricted from
`X'` is killed by the connecting map, so the connecting map sends such a class to `n` times
something, and `n` is injective on `H¹(X', 𝒦)`. -/
theorem saturated_range_unitsKernelBoundary (i : X ⟶ X') (hi : IsThickening i) {n : ℤ}
    (hn : IsUnit ((n : ℤ) : Γ(X, ⊤))) (hpow : GlobalUnitsPowerLift i n)
    (a : CategoryTheory.Sheaf.H.{u} (kernel (unitsRestrictionSheafHom i)) 1)
    (ha : n • a ∈ Set.range (unitsKernelBoundary i hi)) :
    a ∈ Set.range (unitsKernelBoundary i hi) := by
  obtain ⟨y, hy⟩ := ha
  obtain ⟨z, w, hzw⟩ := zsmul_add_range_of_globalUnitsPowerLift i hpow y
  have hw : unitsKernelBoundary i hi (unitsToSubCohomology i 0 w) = 0 :=
    (cohomology_exact_quotient (unitsKernelShortComplex_shortExact i hi) 0 _).mpr ⟨w, rfl⟩
  have hiso := isIso_zsmul_kernel_unitsRestrictionSheafHom i hi n hn
  refine ⟨z, ((bijective_zsmul_cohomology_of_isIso _ n 1 hiso).1 ?_).symm⟩
  change n • a = n • unitsKernelBoundary i hi z
  rw [← hy, hzw, map_add, hw, add_zero, map_zsmul]

/-- Conversely, saturation of the image of `H⁰(X, 𝒪_X^*)` in `H¹(X', 𝒦)` forces
`Stacks.Thickenings.GlobalUnitsPowerLift`: the connecting map of an invertible global function on
`X` is `n` times a class, saturation makes that class a connecting image, and exactness at
`H⁰(X, 𝒪_X^*)` then exhibits the correcting unit on `X'`. -/
theorem globalUnitsPowerLift_of_saturated_range_unitsKernelBoundary (i : X ⟶ X')
    (hi : IsThickening i) {n : ℤ} (hn : IsUnit ((n : ℤ) : Γ(X, ⊤)))
    (hsat : ∀ a : CategoryTheory.Sheaf.H.{u} (kernel (unitsRestrictionSheafHom i)) 1,
      n • a ∈ Set.range (unitsKernelBoundary i hi) →
        a ∈ Set.range (unitsKernelBoundary i hi)) :
    GlobalUnitsPowerLift i n := by
  have hiso := isIso_zsmul_kernel_unitsRestrictionSheafHom i hi n hn
  refine globalUnitsPowerLift_of_zsmul_add_range i fun y => ?_
  obtain ⟨a, ha⟩ := (bijective_zsmul_cohomology_of_isIso _ n 1 hiso).2
    (unitsKernelBoundary i hi y)
  have ha' : n • a = unitsKernelBoundary i hi y := ha
  obtain ⟨z, hz⟩ := hsat a ⟨y, ha'.symm⟩
  have h1 : unitsKernelBoundary i hi y = n • unitsKernelBoundary i hi z := by
    rw [hz]
    exact ha'.symm
  have hδ : unitsKernelBoundary i hi (y - n • z) = 0 := by
    rw [map_sub, map_zsmul, h1, sub_self]
  obtain ⟨w, hw⟩ := (cohomology_exact_quotient
    (unitsKernelShortComplex_shortExact i hi) 0 (y - n • z)).mp hδ
  have hw' : unitsToSubCohomology i 0 w = y - n • z := hw
  exact ⟨z, w, by rw [hw']; abel⟩

/-- The surjectivity half of [Stacks, Tag 0C6S] in the cohomological spelling, with no
hypothesis beyond the source's: restriction of units carries the `n`-torsion of
`H¹(X', 𝒪_{X'}^*)` onto the `n`-torsion of `H¹(X', i_* 𝒪_X^*)`. -/
theorem surjOn_cohomologyUnitsRestriction_zsmulTorsion (i : X ⟶ X') (hi : IsThickening i)
    {n : ℤ} (hn : IsUnit ((n : ℤ) : Γ(X, ⊤))) :
    Set.SurjOn (unitsToSubCohomology i 1)
      (zsmulTorsion (CategoryTheory.Sheaf.H.{u}
        (unitsSheaf X'.toLocallyRingedSpace.toRingedSpace) 1) n)
      (zsmulTorsion (CategoryTheory.Sheaf.H.{u} (pushforwardUnitsSheaf i) 1) n) := by
  have hS := unitsKernelShortComplex_shortExact i hi
  have hiso := isIso_zsmul_kernel_unitsRestrictionSheafHom i hi n hn
  exact surjOn_zsmul_of_exact
    (CategoryTheory.Sheaf.H.map.{u} (kernel.ι (unitsRestrictionSheafHom i)) 1)
    (unitsToSubCohomology i 1) (cohomologyBoundary hS 1)
    (cohomology_exact_middle hS 1) (cohomology_exact_quotient hS 1) n
    (bijective_zsmul_cohomology_of_isIso _ n 1 hiso).2
    (bijective_zsmul_cohomology_of_isIso _ n 2 hiso).1

/-- [Stacks, Tag 0C6S] in the cohomological spelling, with the hypothesis the source's argument
needs and with its necessity: for `n` invertible in `𝒪_X`, restriction of units is a bijection
from the `n`-torsion of `H¹(X', 𝒪_{X'}^*)` onto the `n`-torsion of `H¹(X', i_* 𝒪_X^*)` if and
only if every invertible global function on `X` is an `n`-th power times the restriction of an
invertible global function on `X'`. -/
theorem bijOn_cohomologyUnitsRestriction_zsmulTorsion_iff (i : X ⟶ X') (hi : IsThickening i)
    {n : ℤ} (hn : IsUnit ((n : ℤ) : Γ(X, ⊤))) :
    Set.BijOn (unitsToSubCohomology i 1)
      (zsmulTorsion (CategoryTheory.Sheaf.H.{u}
        (unitsSheaf X'.toLocallyRingedSpace.toRingedSpace) 1) n)
      (zsmulTorsion (CategoryTheory.Sheaf.H.{u} (pushforwardUnitsSheaf i) 1) n) ↔
      GlobalUnitsPowerLift i n := by
  have hS := unitsKernelShortComplex_shortExact i hi
  have hiso := isIso_zsmul_kernel_unitsRestrictionSheafHom i hi n hn
  refine ⟨fun hb => globalUnitsPowerLift_of_saturated_range_unitsKernelBoundary i hi hn
    fun a ha => ?_, fun hpow => ?_⟩
  · exact saturated_of_injOn_zsmul_of_exact (unitsKernelBoundary i hi)
      (CategoryTheory.Sheaf.H.map.{u} (kernel.ι (unitsRestrictionSheafHom i)) 1)
      (unitsToSubCohomology i 1) (cohomology_exact_sub hS 0) (cohomology_exact_middle hS 1)
      n hb.injOn a ha
  · exact bijOn_zsmul_of_exact (unitsKernelBoundary i hi)
      (CategoryTheory.Sheaf.H.map.{u} (kernel.ι (unitsRestrictionSheafHom i)) 1)
      (unitsToSubCohomology i 1) (cohomologyBoundary hS 1)
      (cohomology_exact_sub hS 0) (cohomology_exact_middle hS 1)
      (cohomology_exact_quotient hS 1) n
      (bijective_zsmul_cohomology_of_isIso _ n 1 hiso).2
      (bijective_zsmul_cohomology_of_isIso _ n 2 hiso).1
      (saturated_range_unitsKernelBoundary i hi hn hpow)

/-- [Stacks, Tag 0C6S] in the cohomological spelling: for `n` invertible in `𝒪_X` and a
thickening along which global units lift, restriction of units is a bijection from the
`n`-torsion of `H¹(X', 𝒪_{X'}^*)` onto the `n`-torsion of `H¹(X', i_* 𝒪_X^*)`. -/
theorem bijOn_cohomologyUnitsRestriction_zsmulTorsion (i : X ⟶ X') (hi : IsThickening i)
    {n : ℤ} (hn : IsUnit ((n : ℤ) : Γ(X, ⊤)))
    (hunits : Function.Surjective (Units.map (CommRingCat.Hom.hom (i.app ⊤)).toMonoidHom)) :
    Set.BijOn (unitsToSubCohomology i 1)
      (zsmulTorsion (CategoryTheory.Sheaf.H.{u}
        (unitsSheaf X'.toLocallyRingedSpace.toRingedSpace) 1) n)
      (zsmulTorsion (CategoryTheory.Sheaf.H.{u} (pushforwardUnitsSheaf i) 1) n) :=
  (bijOn_cohomologyUnitsRestriction_zsmulTorsion_iff i hi hn).mpr
    (globalUnitsPowerLift_of_surjective i n hunits)

end Cohomology

/-! ### From `Ext`-cohomology to the Picard group -/

section Picard

variable {X X' : Scheme.{u}}

/-- First cohomology computed as the first right-derived functor of global sections agrees,
naturally in the sheaf, with first cohomology computed as `Ext` from the constant sheaf of
integers. -/
private def cohomologyFunctorExtIso (Y : TopCat.{u}) :
    abelianCohomology.{u, u} Y ⊤ 1 ≅
      CategoryTheory.Sheaf.functorH.{u, u, u, u} (Opens.grothendieckTopology Y) 1 :=
  ModuleSheafCohomology.rightDerivedIso (sectionsCoyonedaIso Y).symm 1 ≪≫
    ModuleSheafCohomology.rightDerivedCoyonedaSuccIso
      ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) 0

/-- The first Leray edge map `H¹(Y, f_* F) ⟶ H¹(Z, F)` of a closed embedding is bijective: it
is injective by [Stacks, Tag 01F2], and surjective because the first higher direct image
`R¹ f_* F` vanishes, the direct image along a closed embedding being exact. -/
theorem bijective_abelianEdgeMap_of_isClosedEmbedding {Z Y : TopCat.{u}} (f : Z ⟶ Y)
    (hf : Topology.IsClosedEmbedding f)
    (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) :
    Function.Bijective ((abelianEdgeMap.{u, u} f 1).app F) := by
  have hP := Stacks.ClosedImmersion.hasCohomologyPushforwardIso_of_isClosedEmbedding.{u, u, u} f hf
  let : PreservesFiniteLimits (abelianPushforward.{u, u} f) := hP.preservesFiniteLimits
  let : PreservesFiniteColimits (abelianPushforward.{u, u} f) := hP.preservesFiniteColimits
  have hz : IsZero (((abelianPushforward.{u, u} f).rightDerived 1).obj F) := by
    let I := injectiveResolution F
    let K := ((abelianPushforward.{u, u} f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    have hex : K.ExactAt 1 := by
      apply (HomologicalComplex.exactAt_iff' K 0 1 2 (by simp) (by simp)).mpr
      exact (I.exact_succ 0).map (abelianPushforward.{u, u} f)
    exact hex.isZero_homology.of_iso (I.isoRightDerivedObj (abelianPushforward.{u, u} f) 1)
  have hz' := (abelianSections.{u, u} Y ⊤).map_isZero hz
  refine ⟨abelianEdgeMap_injective.{u, u} f F, fun y => ?_⟩
  have hzero : (abelianSecondEdgeMap.{u, u} f 1).app F y = 0 :=
    (AddCommGrpCat.subsingleton_of_isZero hz').elim _ _
  exact ((ShortComplex.ab_exact_iff_function_exact _).mp (abelianExact.{u, u} f F) y).mp hzero

/-- Restriction of units and the map on units of the sheaf-of-units sequence are the same map
of sheaves of abelian groups: both are `Units.map (i.app U)` on sections. -/
private theorem unitsPushforwardMap_eq_unitsRestrictionSheafHom (i : X ⟶ X') :
    unitsPushforwardMap i = unitsRestrictionSheafHom i := by
  apply Sheaf.hom_ext
  ext U s
  exact (unitsPushforwardMap_app i U.unop (Additive.toMul s)).trans
    (unitsRestrictionSheafHom_app i U.unop (Additive.toMul s)).symm

/-- The first Leray edge map of the closed embedding underlying a thickening, for the sheaf of
units of `X`, as an additive equivalence. -/
private def unitsEdgeEquiv (i : X ⟶ X') (hi : IsThickening i) :
    ↑((abelianPushforward.{u, u} i.base ⋙ abelianCohomology.{u, u} X' ⊤ 1).obj
      (unitsSheaf X.toLocallyRingedSpace.toRingedSpace)) ≃+
    ↑((abelianCohomology.{u, u} X ⊤ 1).obj (unitsSheaf X.toLocallyRingedSpace.toRingedSpace)) :=
  AddEquiv.ofBijective
    ((abelianEdgeMap.{u, u} i.base 1).app (unitsSheaf X.toLocallyRingedSpace.toRingedSpace)).hom
    (bijective_abelianEdgeMap_of_isClosedEmbedding i.base hi.1.isClosedEmbedding _)

/-- Restriction of Picard classes is conjugate, under the identification of [Stacks, Tag 09NU]
and the Leray edge map, to restriction of units on right-derived first cohomology. -/
private theorem schemePullbackClass_h1UnitsAddEquivPicard (i : X ⟶ X') (hi : IsThickening i)
    (c : h1UnitsRightDerived X') :
    schemePullbackClass i ((h1UnitsAddEquivPicard X') c) =
      ((unitsEdgeEquiv i hi).trans (h1UnitsAddEquivPicard X))
        ((abelianCohomology.{u, u} X' ⊤ 1).map (unitsRestrictionSheafHom i) c) := by
  have h := h1UnitsAddEquivPicard_naturality i c
  rw [← unitsPushforwardMap_eq_unitsRestrictionSheafHom]
  exact h.symm

/-- Restriction of units on `Ext`-cohomology is conjugate to restriction of units on
right-derived cohomology under the comparison of the two spellings. -/
private theorem cohomologyFunctorExtIso_symm_naturality (i : X ⟶ X')
    (x : CategoryTheory.Sheaf.H.{u} (unitsSheaf X'.toLocallyRingedSpace.toRingedSpace) 1) :
    (abelianCohomology.{u, u} X' ⊤ 1).map (unitsRestrictionSheafHom i)
      ((((cohomologyFunctorExtIso X').app
        (unitsSheaf X'.toLocallyRingedSpace.toRingedSpace)).symm).addCommGroupIsoToAddEquiv x) =
      (((cohomologyFunctorExtIso X').app (pushforwardUnitsSheaf i)).symm
        ).addCommGroupIsoToAddEquiv (unitsToSubCohomology i 1 x) :=
  (ConcreteCategory.congr_hom
    ((cohomologyFunctorExtIso X').inv.naturality (unitsRestrictionSheafHom i)) x).symm

/-- The bijection on `n`-torsion of the Picard groups and the bijection on the `n`-torsion of
the first cohomology of the sheaves of units are the same statement: they are conjugate under
the comparison of `Ext`-cohomology with right-derived global sections, the Leray edge map of the
closed embedding, and the identification of [Stacks, Tag 09NU]. -/
theorem bijOn_schemePullbackClass_zsmulTorsion_iff_cohomology (i : X ⟶ X')
    (hi : IsThickening i) (n : ℤ) :
    Set.BijOn (schemePullbackClass i) (zsmulTorsion (ofScheme X') n)
        (zsmulTorsion (ofScheme X) n) ↔
      Set.BijOn (unitsToSubCohomology i 1)
        (zsmulTorsion (CategoryTheory.Sheaf.H.{u}
          (unitsSheaf X'.toLocallyRingedSpace.toRingedSpace) 1) n)
        (zsmulTorsion (CategoryTheory.Sheaf.H.{u} (pushforwardUnitsSheaf i) 1) n) := by
  exact ((bijOn_zsmulTorsion_conjugate_iff _ _ _ _
    (schemePullbackClass_h1UnitsAddEquivPicard i hi) n).symm.trans
    (bijOn_zsmulTorsion_conjugate_iff _ _ _ _ (cohomologyFunctorExtIso_symm_naturality i) n).symm)

/-- The correction to [Stacks, Tag 0C6S]: the bijection the tag asserts, as an equivalence with
the hypothesis the source's argument needs, which is therefore also necessary.  For a thickening
`i : X ⟶ X'` and an integer `n` invertible in `𝒪_X`, restriction of invertible modules is a
bijection `Pic(X')[n] → Pic(X)[n]` if and only if every invertible global function on `X` is an
`n`-th power times the restriction of an invertible global function on `X'`.  See the
implementation notes: the tag as originally stated carries no such hypothesis, that condition is
exactly what the exact sequence of [Stacks, Tag 0C6R] makes equivalent to it, and a thickening
violating the condition exists.  The corrected
statement of the tag assumes `Stacks.Thickenings.GlobalUnitsPowerLift`, and it is registered on
`Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_of_globalUnitsPowerLift` below. -/
theorem bijOn_schemePullbackClass_zsmulTorsion_iff (i : X ⟶ X') (hi : IsThickening i) {n : ℤ}
    (hn : IsUnit ((n : ℤ) : Γ(X, ⊤))) :
    Set.BijOn (schemePullbackClass i) (zsmulTorsion (ofScheme X') n)
        (zsmulTorsion (ofScheme X) n) ↔ GlobalUnitsPowerLift i n :=
  (bijOn_schemePullbackClass_zsmulTorsion_iff_cohomology i hi n).trans
    (bijOn_cohomologyUnitsRestriction_zsmulTorsion_iff i hi hn)

/-- **Stacks Project, Tag 0C6S**, with the correction discussed in the implementation notes.
For a thickening `i : X ⟶ X'`, an integer `n` invertible in `𝒪_X` and the hypothesis that every
invertible global function on `X` is the restriction of an invertible global function on `X'`,
restriction of invertible modules is a bijection `Pic(X')[n] → Pic(X)[n]`. -/
theorem bijOn_schemePullbackClass_zsmulTorsion_of_isThickening (i : X ⟶ X')
    (hi : IsThickening i) {n : ℤ} (hn : IsUnit ((n : ℤ) : Γ(X, ⊤)))
    (hunits : Function.Surjective (Units.map (CommRingCat.Hom.hom (i.app ⊤)).toMonoidHom)) :
    Set.BijOn (schemePullbackClass i) (zsmulTorsion (ofScheme X') n)
      (zsmulTorsion (ofScheme X) n) :=
  (bijOn_schemePullbackClass_zsmulTorsion_iff i hi hn).mpr
    (globalUnitsPowerLift_of_surjective i n hunits)

/-- **Stacks Project, Tag 0C6S** in its corrected form (an erratum to the printed statement).
For a thickening `i : X ⟶ X'` and an integer `n` invertible in `𝒪_X`, assuming every invertible
global function on `X` is an `n`-th power times the restriction of an invertible global function
on `X'`, restriction of invertible modules is a bijection `Pic(X')[n] → Pic(X)[n]`.

The original statement omitted that assumption and is refuted by
`Stacks.Examples.TwistedDoubledLine.not_forall_bijOn_schemePullbackClass_zsmulTorsion`; the
assumption is not merely sufficient but necessary, by
`Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_iff`. -/
@[stacks 0C6S]
theorem bijOn_schemePullbackClass_zsmulTorsion_of_globalUnitsPowerLift (i : X ⟶ X')
    (hi : IsThickening i) {n : ℤ} (hn : IsUnit ((n : ℤ) : Γ(X, ⊤)))
    (hpow : GlobalUnitsPowerLift i n) :
    Set.BijOn (schemePullbackClass i) (zsmulTorsion (ofScheme X') n)
      (zsmulTorsion (ofScheme X) n) :=
  (bijOn_schemePullbackClass_zsmulTorsion_iff i hi hn).mpr hpow

/-- **Stacks Project, Tag 0C6S**, the half of it that is true as stated: the surjectivity of
restriction on `n`-torsion, for an arbitrary thickening and with no hypothesis beyond the
source's, so that every `n`-torsion class on `X` is the restriction of an `n`-torsion class on
`X'`.

This is the surjectivity half alone, and it needs no hypothesis beyond the source's.  Injectivity
is equivalent to `Stacks.Thickenings.GlobalUnitsPowerLift` by
`Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_iff`, and the corrected statement of
the tag, which assumes it, is
`Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_of_globalUnitsPowerLift`. -/
theorem surjOn_schemePullbackClass_zsmulTorsion_of_isThickening (i : X ⟶ X')
    (hi : IsThickening i) {n : ℤ} (hn : IsUnit ((n : ℤ) : Γ(X, ⊤))) :
    Set.SurjOn (schemePullbackClass i) (zsmulTorsion (ofScheme X') n)
      (zsmulTorsion (ofScheme X) n) := by
  exact surjOn_zsmulTorsion_conjugate _ _ _ _ (schemePullbackClass_h1UnitsAddEquivPicard i hi) n
    (surjOn_zsmulTorsion_conjugate _ _ _ _ (cohomologyFunctorExtIso_symm_naturality i) n
      (surjOn_cohomologyUnitsRestriction_zsmulTorsion i hi hn))

end Picard

end Stacks.Thickenings

end
