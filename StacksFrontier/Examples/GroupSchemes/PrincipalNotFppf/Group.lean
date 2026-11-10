module

public import Mathlib.Algebra.Category.CommAlgCat.Monoidal
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import StacksFrontier.Examples.GroupSchemes.PrincipalNotFppf.Ring

/-!
# The diagonalizable group and its coaction on the radical tower

The group scheme of the counterexample is the product `∏ᵢ μ_{i+2}` of the groups of
`(i + 2)`-nd roots of unity over `ℚ`, that is the spectrum of the group algebra of
`CharGroup = ⨁ᵢ ℤ/(i+2)`.  It acts on the radical tower algebra
`A = ℚ[x₀, x₁, …]/(xᵢ ^ (i + 2) - 2)` by scaling `xᵢ` by the `i`-th coordinate, which on
coordinate rings is the coaction `xᵢ ↦ tᵢ ⊗ xᵢ`.

This file builds that coaction and proves that the induced shear map
`A ⊗ A → ℚ[CharGroup] ⊗ A`, `a ⊗ 1 ↦ coaction a`, `1 ⊗ a ↦ 1 ⊗ a`, is an isomorphism of
`ℚ`-algebras, with inverse sending `tᵢ ↦ xᵢ ⊗ xᵢ⁻¹`.  Algebraically this is the statement that
the action is simply transitive.

## Main definitions

* `Stacks.Examples.RadicalTower.CharGroup` is `⨁ᵢ ℤ/(i+2)`, written multiplicatively, with
  generators `Stacks.Examples.RadicalTower.gen`.
* `Stacks.Examples.RadicalTower.Coord` is its group algebra over `ℚ`, a Hopf algebra.
* `Stacks.Examples.RadicalTower.coaction` is the coaction `xᵢ ↦ tᵢ ⊗ xᵢ`.
* `Stacks.Examples.RadicalTower.shear` is the shear map and
  `Stacks.Examples.RadicalTower.shearEquiv` the resulting algebra isomorphism.

## Main results

* `Stacks.Examples.RadicalTower.monoidHom_ext` and
  `Stacks.Examples.RadicalTower.coord_algHom_ext`: the generators generate.
* `Stacks.Examples.RadicalTower.unshear_comp_shear` and
  `Stacks.Examples.RadicalTower.shear_comp_unshear`: the shear map is invertible.

## Implementation notes

Using a single radicand with growing exponents rather than infinitely many square roots makes
the group `⨁ᵢ ℤ/(i+2)` instead of `⨁ᵢ ℤ/2`; the group algebra of any such group is a Hopf
algebra, so the group scheme structure comes for free from Mathlib.

The inverse of the shear map is built from the character of `CharGroup` with values in the units
of `A ⊗ A` sending the `i`-th generator to `xᵢ ⊗ xᵢ⁻¹`; this is a well-defined character because
that unit has order dividing `i + 2`, its `(i + 2)`-nd power being `2 ⊗ 2⁻¹ = 1`.

## References

* [Stacks Project, Tag 077B](https://stacks.math.columbia.edu/tag/077B)
-/

@[expose] public section

open TensorProduct

namespace Stacks.Examples.RadicalTower

/-- The character group `⨁ᵢ ℤ/(i+2)` of the group scheme of the counterexample. -/
abbrev Exponents := DirectSum ℕ fun i : ℕ => ZMod (i + 2)

/-- The character group, written multiplicatively. -/
abbrev CharGroup := Multiplicative Exponents

/-- The `i`-th generator of the character group, of order `i + 2`. -/
def gen (i : ℕ) : CharGroup :=
  Multiplicative.ofAdd (DirectSum.of (fun j : ℕ => ZMod (j + 2)) i 1)

/-- The `i`-th generator of the character group has order dividing `i + 2`. -/
@[simp] theorem gen_pow (i : ℕ) : gen i ^ (i + 2) = 1 := by
  have hz : (i + 2) • (1 : ZMod (i + 2)) = 0 := by
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_self]
  have h : (i + 2) • DirectSum.of (fun j : ℕ => ZMod (j + 2)) i 1 = 0 := by
    rw [← map_nsmul, hz, map_zero]
  rw [gen, ← ofAdd_nsmul, h]
  simp

/-- Two monoid homomorphisms out of the character group agree as soon as they agree on each
generator. -/
theorem monoidHom_ext {B : Type*} [Monoid B] {f g : CharGroup →* B}
    (h : ∀ i, f (gen i) = g (gen i)) : f = g := by
  suffices H : ∀ a : Exponents, f (Multiplicative.ofAdd a) = g (Multiplicative.ofAdd a) from
    MonoidHom.ext fun x => H (Multiplicative.toAdd x)
  intro a
  induction a using DirectSum.induction_on with
  | zero => simp
  | of i y =>
      have hy : DirectSum.of (fun j : ℕ => ZMod (j + 2)) i y =
          y.val • DirectSum.of (fun j : ℕ => ZMod (j + 2)) i 1 := by
        rw [← map_nsmul]
        congr 1
        simp [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id]
      rw [hy, ofAdd_nsmul]
      rw [show Multiplicative.ofAdd (DirectSum.of (fun j : ℕ => ZMod (j + 2)) i 1) = gen i from rfl,
        map_pow, map_pow, h i]
  | add x y hx hy => rw [ofAdd_add, map_mul, map_mul, hx, hy]

/-- The coordinate ring of the group scheme: the group algebra of the character group. -/
abbrev Coord := MonoidAlgebra ℚ CharGroup

/-- Two `ℚ`-algebra maps out of the group algebra agree as soon as they agree on the group-like
elements attached to the generators. -/
theorem coord_algHom_ext {B : Type*} [CommRing B] [Algebra ℚ B] {f g : Coord →ₐ[ℚ] B}
    (h : ∀ i, f (MonoidAlgebra.single (gen i) 1) = g (MonoidAlgebra.single (gen i) 1)) :
    f = g := by
  refine (MonoidAlgebra.lift ℚ B CharGroup).symm.injective (monoidHom_ext fun i => ?_)
  simpa using h i

/-- A pure tensor is the product of its two factors, each tensored with `1`. -/
private theorem tmul_eq_tmul_one_mul_one_tmul {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (a : A) (b : B) :
    a ⊗ₜ[ℚ] b = (a ⊗ₜ[ℚ] (1 : B)) * ((1 : A) ⊗ₜ[ℚ] b) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Two `ℚ`-algebra maps out of a tensor product agree as soon as they agree on each factor. -/
theorem tmul_algHom_ext {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra ℚ A] [Algebra ℚ B] [Algebra ℚ C] {f g : A ⊗[ℚ] B →ₐ[ℚ] C}
    (h₁ : ∀ a : A, f (a ⊗ₜ 1) = g (a ⊗ₜ 1))
    (h₂ : ∀ b : B, f ((1 : A) ⊗ₜ b) = g ((1 : A) ⊗ₜ b)) : f = g := by
  refine Algebra.TensorProduct.ext' fun a b => ?_
  rw [tmul_eq_tmul_one_mul_one_tmul, map_mul, map_mul, h₁, h₂]

section Coaction

/-- The coaction on the polynomial algebra, sending `Xᵢ` to `tᵢ ⊗ xᵢ`. -/
noncomputable def coactionAux : MvPolynomial ℕ ℚ →ₐ[ℚ] Coord ⊗[ℚ] Alg :=
  MvPolynomial.aeval (R := ℚ) (S₁ := Coord ⊗[ℚ] Alg)
    fun i => (MonoidAlgebra.single (gen i) (1 : ℚ) ⊗ₜ[ℚ] root i : Coord ⊗[ℚ] Alg)

/-- The coaction on the polynomial algebra sends `Xᵢ` to `tᵢ ⊗ xᵢ`. -/
@[simp] theorem coactionAux_X (i : ℕ) :
    coactionAux (MvPolynomial.X i) =
      MonoidAlgebra.single (gen i) (1 : ℚ) ⊗ₜ[ℚ] root i := by
  simp [coactionAux]

/-- The element `1 ⊗ 2` of a tensor product is the scalar `2`. -/
private theorem one_tmul_two_aux {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] : (1 : A) ⊗ₜ[ℚ] (2 : B) = (2 : A ⊗[ℚ] B) := by
  simpa using map_ofNat (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] A ⊗[ℚ] B) 2

/-- The element `1 ⊗ 2` of the tensor product is the scalar `2`. -/
theorem one_tmul_two : (1 : Coord) ⊗ₜ[ℚ] (2 : Alg) = (2 : Coord ⊗[ℚ] Alg) :=
  one_tmul_two_aux

/-- The coaction sends each radical relation to zero, because the `i`-th generator of the
character group has order dividing `i + 2`. -/
theorem coactionAux_relation (i : ℕ) : coactionAux (relation i) = 0 := by
  have h : coactionAux.toRingHom (relation i) =
      (MonoidAlgebra.single (gen i) (1 : ℚ) ⊗ₜ[ℚ] root i) ^ (i + 2) - 2 := by
    rw [relation, map_sub, map_pow, map_ofNat]
    exact congrArg (fun x => x ^ (i + 2) - 2) (coactionAux_X i)
  refine h.trans ?_
  rw [Algebra.TensorProduct.tmul_pow, MonoidAlgebra.single_pow, gen_pow, root_pow, one_pow,
    ← MonoidAlgebra.one_def, one_tmul_two, sub_self]

/-- The coaction kills the ideal of radical relations. -/
theorem coactionAux_eq_zero_of_mem (a : MvPolynomial ℕ ℚ) (ha : a ∈ relationsIdeal) :
    coactionAux a = 0 := by
  have hle : relationsIdeal ≤
      RingHom.ker coactionAux.toRingHom := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact coactionAux_relation i
  exact hle ha

/-- The coaction of the group scheme on the radical tower algebra, sending the `i`-th generator
`xᵢ` to `tᵢ ⊗ xᵢ`. -/
noncomputable def coaction : Alg →ₐ[ℚ] Coord ⊗[ℚ] Alg :=
  Ideal.Quotient.liftₐ relationsIdeal coactionAux coactionAux_eq_zero_of_mem

/-- The coaction sends the `i`-th generator `xᵢ` to `tᵢ ⊗ xᵢ`. -/
@[simp] theorem coaction_root (i : ℕ) :
    coaction (root i) = MonoidAlgebra.single (gen i) (1 : ℚ) ⊗ₜ root i := by
  rw [coaction, root]
  simp only [Ideal.Quotient.liftₐ_apply]
  exact coactionAux_X i

end Coaction

section Characters

/-- The units of `A ⊗ A` form a commutative group. -/
noncomputable local instance tensorUnitsCommGroup : CommGroup ((Alg ⊗[ℚ] Alg)ˣ) :=
  Units.instCommGroupUnits (α := Alg ⊗[ℚ] Alg)

/-- Inclusion of the radical tower into the left factor of `A ⊗ A`, on units. -/
noncomputable def leftUnitHom : Algˣ →* (Alg ⊗[ℚ] Alg)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeftRingHom :
    Alg →+* Alg ⊗[ℚ] Alg).toMonoidHom

/-- Inclusion of the radical tower into the right factor of `A ⊗ A`, on units. -/
noncomputable def rightUnitHom : Algˣ →* (Alg ⊗[ℚ] Alg)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight :
    Alg →ₐ[ℚ] Alg ⊗[ℚ] Alg).toRingHom.toMonoidHom

/-- The left inclusion sends a unit `u` to `u ⊗ 1`. -/
@[simp] theorem leftUnitHom_val (u : Algˣ) :
    (leftUnitHom u : Alg ⊗[ℚ] Alg) = (u : Alg) ⊗ₜ 1 := by
  simp [leftUnitHom]

/-- The right inclusion sends a unit `u` to `1 ⊗ u`. -/
@[simp] theorem rightUnitHom_val (u : Algˣ) :
    (rightUnitHom u : Alg ⊗[ℚ] Alg) = 1 ⊗ₜ (u : Alg) := by
  simp [rightUnitHom]

/-- The two inclusions agree on the unit `2`, because `2` is a scalar. -/
theorem leftUnitHom_twoUnit : leftUnitHom twoUnit = rightUnitHom twoUnit := by
  refine Units.ext ?_
  rw [leftUnitHom_val, rightUnitHom_val, twoUnit_val]
  have h1 : (2 : Alg) ⊗ₜ[ℚ] (1 : Alg) = (2 : Alg ⊗[ℚ] Alg) := by
    simpa using map_ofNat
      (Algebra.TensorProduct.includeLeftRingHom : Alg →+* Alg ⊗[ℚ] Alg) 2
  rw [h1, one_tmul_two_aux]

/-- The character value `xᵢ ⊗ xᵢ⁻¹` attached to the `i`-th generator. -/
noncomputable def shearUnit (i : ℕ) : (Alg ⊗[ℚ] Alg)ˣ :=
  leftUnitHom (rootUnit i) / rightUnitHom (rootUnit i)

/-- Multiplying the character value by `1 ⊗ xᵢ` gives `xᵢ ⊗ 1`, as units. -/
theorem shearUnit_mul_rightUnitHom (i : ℕ) :
    shearUnit i * rightUnitHom (rootUnit i) = leftUnitHom (rootUnit i) := by
  rw [shearUnit, div_mul_cancel]

/-- Multiplying the character value by `1 ⊗ xᵢ` gives `xᵢ ⊗ 1`. -/
theorem shearUnit_mul (i : ℕ) :
    (shearUnit i : Alg ⊗[ℚ] Alg) * (1 ⊗ₜ root i) = root i ⊗ₜ 1 := by
  calc (shearUnit i : Alg ⊗[ℚ] Alg) * (1 ⊗ₜ root i)
      = ((shearUnit i * rightUnitHom (rootUnit i) : (Alg ⊗[ℚ] Alg)ˣ) : Alg ⊗[ℚ] Alg) := by
        rw [Units.val_mul, rightUnitHom_val, rootUnit_val]
    _ = root i ⊗ₜ 1 := by rw [shearUnit_mul_rightUnitHom, leftUnitHom_val, rootUnit_val]

/-- The character value has order dividing `i + 2`: its `(i + 2)`-nd power is `2 ⊗ 2⁻¹ = 1`. -/
theorem shearUnit_pow (i : ℕ) : shearUnit i ^ (i + 2) = 1 := by
  have hl : leftUnitHom (rootUnit i) ^ (i + 2) = leftUnitHom twoUnit := by
    rw [← map_pow, rootUnit_pow]
  have hr : rightUnitHom (rootUnit i) ^ (i + 2) = rightUnitHom twoUnit := by
    rw [← map_pow, rootUnit_pow]
  rw [shearUnit, div_pow, hl, hr, leftUnitHom_twoUnit, div_self']

/-- The `i`-th component of the character: the homomorphism out of `ℤ/(i+2)` sending `1` to the
character value `xᵢ ⊗ xᵢ⁻¹`. -/
noncomputable def charComponent (i : ℕ) : ZMod (i + 2) →+ Additive ((Alg ⊗[ℚ] Alg)ˣ) :=
  ZMod.lift (i + 2) ⟨zmultiplesHom (Additive ((Alg ⊗[ℚ] Alg)ˣ)) (Additive.ofMul (shearUnit i)),
    by
      change Additive.ofMul (shearUnit i ^ ((i + 2 : ℕ) : ℤ)) = 0
      rw [zpow_natCast, shearUnit_pow]
      rfl⟩

/-- The `i`-th component of the character sends `1` to the character value. -/
theorem charComponent_one (i : ℕ) :
    charComponent i 1 = Additive.ofMul (shearUnit i) := by
  rw [charComponent, show (1 : ZMod (i + 2)) = ((1 : ℤ) : ZMod (i + 2)) from by norm_num,
    ZMod.lift_coe]
  exact one_zsmul _

/-- The character of the exponent group with values in the units of `A ⊗ A`. -/
noncomputable def charAddHom : Exponents →+ Additive ((Alg ⊗[ℚ] Alg)ˣ) :=
  DirectSum.toAddMonoid charComponent

/-- The character sends the `i`-th generator of the exponent group to the character value. -/
theorem charAddHom_of (i : ℕ) :
    charAddHom (DirectSum.of (fun j : ℕ => ZMod (j + 2)) i 1) =
      Additive.ofMul (shearUnit i) := by
  rw [charAddHom, DirectSum.toAddMonoid_of]
  exact charComponent_one i

/-- The character of the character group with values in `A ⊗ A`. -/
noncomputable def charMonoidHom : CharGroup →* Alg ⊗[ℚ] Alg where
  toFun g := ((Additive.toMul (charAddHom (Multiplicative.toAdd g)) : (Alg ⊗[ℚ] Alg)ˣ) :
    Alg ⊗[ℚ] Alg)
  map_one' := by
    change ((Additive.toMul (charAddHom 0) : (Alg ⊗[ℚ] Alg)ˣ) : Alg ⊗[ℚ] Alg) = 1
    rw [map_zero]
    rfl
  map_mul' a b := by
    change ((Additive.toMul (charAddHom (Multiplicative.toAdd a + Multiplicative.toAdd b)) :
      (Alg ⊗[ℚ] Alg)ˣ) : Alg ⊗[ℚ] Alg) = _
    rw [map_add]
    rfl

/-- The character sends the `i`-th generator to `xᵢ ⊗ xᵢ⁻¹`. -/
@[simp] theorem charMonoidHom_gen (i : ℕ) :
    charMonoidHom (gen i) = (shearUnit i : Alg ⊗[ℚ] Alg) := by
  change ((Additive.toMul (charAddHom (DirectSum.of (fun j : ℕ => ZMod (j + 2)) i 1)) :
    (Alg ⊗[ℚ] Alg)ˣ) : Alg ⊗[ℚ] Alg) = _
  rw [charAddHom_of]
  rfl

/-- The algebra map out of the group algebra given by the character `tᵢ ↦ xᵢ ⊗ xᵢ⁻¹`. -/
noncomputable def charHom : Coord →ₐ[ℚ] Alg ⊗[ℚ] Alg :=
  MonoidAlgebra.lift ℚ (Alg ⊗[ℚ] Alg) CharGroup charMonoidHom

/-- The algebra map `charHom` sends `tᵢ` to `xᵢ ⊗ xᵢ⁻¹`. -/
@[simp] theorem charHom_single (i : ℕ) :
    charHom (MonoidAlgebra.single (gen i) (1 : ℚ)) = (shearUnit i : Alg ⊗[ℚ] Alg) := by
  rw [charHom, MonoidAlgebra.lift_single, charMonoidHom_gen, one_smul]

end Characters

section Shear

/-- The left inclusion `a ↦ a ⊗ 1` of the radical tower into `A ⊗ A`. -/
noncomputable def inclLeft : Alg →ₐ[ℚ] Alg ⊗[ℚ] Alg := Algebra.TensorProduct.includeLeft

/-- The left inclusion `t ↦ t ⊗ 1` of the group algebra into `ℚ[CharGroup] ⊗ A`. -/
noncomputable def inclLeftCoord : Coord →ₐ[ℚ] Coord ⊗[ℚ] Alg :=
  Algebra.TensorProduct.includeLeft

/-- The left inclusion sends `a` to `a ⊗ 1`. -/
@[simp] theorem inclLeft_apply (a : Alg) : inclLeft a = a ⊗ₜ 1 := rfl

/-- The left inclusion of the group algebra sends `c` to `c ⊗ 1`. -/
@[simp] theorem inclLeftCoord_apply (c : Coord) : inclLeftCoord c = c ⊗ₜ 1 := rfl

/-- The shear map of the action: `a ⊗ 1 ↦ coaction a` and `1 ⊗ a ↦ 1 ⊗ a`. -/
noncomputable def shear : Alg ⊗[ℚ] Alg →ₐ[ℚ] Coord ⊗[ℚ] Alg :=
  Algebra.TensorProduct.lift coaction Algebra.TensorProduct.includeRight
    fun x y => Commute.all (coaction x) (Algebra.TensorProduct.includeRight y)

/-- The inverse shear map: `t ⊗ 1 ↦ charHom t` and `1 ⊗ a ↦ 1 ⊗ a`. -/
noncomputable def unshear : Coord ⊗[ℚ] Alg →ₐ[ℚ] Alg ⊗[ℚ] Alg :=
  Algebra.TensorProduct.lift charHom Algebra.TensorProduct.includeRight
    fun x y => Commute.all (charHom x) (Algebra.TensorProduct.includeRight y)

/-- The shear map sends `a ⊗ 1` to `coaction a`. -/
@[simp] theorem shear_tmul_one (a : Alg) : shear (a ⊗ₜ 1) = coaction a :=
  (Algebra.TensorProduct.lift_tmul _ _ _ a 1).trans (mul_one (coaction a))

/-- The shear map sends `1 ⊗ a` to `1 ⊗ a`. -/
@[simp] theorem shear_one_tmul (a : Alg) : shear ((1 : Alg) ⊗ₜ a) = 1 ⊗ₜ a :=
  (Algebra.TensorProduct.lift_tmul _ _ _ 1 a).trans
    ((congrArg (fun z => z * Algebra.TensorProduct.includeRight a)
      coaction.map_one).trans (one_mul (Algebra.TensorProduct.includeRight a)))

/-- The inverse shear map sends `c ⊗ 1` to `charHom c`. -/
@[simp] theorem unshear_tmul_one (c : Coord) : unshear (c ⊗ₜ 1) = charHom c :=
  (Algebra.TensorProduct.lift_tmul _ _ _ c 1).trans (mul_one (charHom c))

/-- The inverse shear map sends `1 ⊗ a` to `1 ⊗ a`. -/
@[simp] theorem unshear_one_tmul (a : Alg) : unshear ((1 : Coord) ⊗ₜ a) = 1 ⊗ₜ a :=
  (Algebra.TensorProduct.lift_tmul _ _ _ 1 a).trans
    ((congrArg (fun z => z * Algebra.TensorProduct.includeRight a)
      charHom.map_one).trans (one_mul (Algebra.TensorProduct.includeRight a)))

/-- The inverse shear map undoes the shear map on the left factor. -/
theorem unshear_shear_tmul_one (a : Alg) :
    unshear (shear (a ⊗ₜ[ℚ] (1 : Alg))) = a ⊗ₜ[ℚ] (1 : Alg) := by
  have key : (unshear.comp shear).comp inclLeft = inclLeft := by
    refine algHom_ext (B := Alg ⊗[ℚ] Alg) fun i => ?_
    change unshear (shear (root i ⊗ₜ[ℚ] (1 : Alg))) = root i ⊗ₜ[ℚ] (1 : Alg)
    rw [shear_tmul_one, coaction_root, tmul_eq_tmul_one_mul_one_tmul, map_mul, unshear_tmul_one,
      unshear_one_tmul, charHom_single, shearUnit_mul]
  exact AlgHom.congr_fun key a

/-- The shear map undoes the inverse shear map on the left factor. -/
theorem shear_unshear_tmul_one (c : Coord) :
    shear (unshear (c ⊗ₜ[ℚ] (1 : Alg))) = c ⊗ₜ[ℚ] (1 : Alg) := by
  have key : (shear.comp unshear).comp inclLeftCoord = inclLeftCoord := by
    refine coord_algHom_ext (B := Coord ⊗[ℚ] Alg) fun i => ?_
    change shear (unshear (MonoidAlgebra.single (gen i) (1 : ℚ) ⊗ₜ[ℚ] (1 : Alg))) =
      MonoidAlgebra.single (gen i) (1 : ℚ) ⊗ₜ[ℚ] (1 : Alg)
    rw [unshear_tmul_one, charHom_single]
    have hu : IsUnit ((1 : Coord) ⊗ₜ[ℚ] root i) := by
      simpa using (isUnit_root i).map
        (Algebra.TensorProduct.includeRight : Alg →ₐ[ℚ] Coord ⊗[ℚ] Alg)
    refine hu.mul_left_cancel ?_
    rw [show ((1 : Coord) ⊗ₜ[ℚ] root i) = shear ((1 : Alg) ⊗ₜ[ℚ] root i) from
        (shear_one_tmul _).symm, ← map_mul, mul_comm ((1 : Alg) ⊗ₜ[ℚ] root i), shearUnit_mul,
      shear_tmul_one, coaction_root, shear_one_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one]
  exact AlgHom.congr_fun key c

/-- The inverse shear map is a left inverse of the shear map. -/
theorem unshear_comp_shear : unshear.comp shear = AlgHom.id ℚ (Alg ⊗[ℚ] Alg) := by
  refine tmul_algHom_ext (A := Alg) (B := Alg) (C := Alg ⊗[ℚ] Alg) ?_ ?_
  · intro a
    exact unshear_shear_tmul_one a
  · intro b
    change unshear (shear ((1 : Alg) ⊗ₜ[ℚ] b)) = (1 : Alg) ⊗ₜ[ℚ] b
    rw [shear_one_tmul, unshear_one_tmul]

/-- The inverse shear map is a right inverse of the shear map. -/
theorem shear_comp_unshear : shear.comp unshear = AlgHom.id ℚ (Coord ⊗[ℚ] Alg) := by
  refine tmul_algHom_ext (A := Coord) (B := Alg) (C := Coord ⊗[ℚ] Alg) ?_ ?_
  · intro c
    exact shear_unshear_tmul_one c
  · intro b
    change shear (unshear ((1 : Coord) ⊗ₜ[ℚ] b)) = (1 : Coord) ⊗ₜ[ℚ] b
    rw [unshear_one_tmul, shear_one_tmul]

/-- The shear map is an isomorphism of `ℚ`-algebras: the action of the group scheme on the
radical tower is simply transitive. -/
noncomputable def shearEquiv : (Alg ⊗[ℚ] Alg) ≃ₐ[ℚ] (Coord ⊗[ℚ] Alg) :=
  AlgEquiv.ofAlgHom shear unshear shear_comp_unshear unshear_comp_shear

end Shear

end Stacks.Examples.RadicalTower

end
