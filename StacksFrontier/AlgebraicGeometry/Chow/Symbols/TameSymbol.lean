module

public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Multiplicativity

/-!
# The tame symbol of a one-dimensional local domain

For a one-dimensional Noetherian local domain, the symbol on pairs of nonzero elements extends
multiplicatively to pairs of units of its fraction field.

## Main definitions

* `AlgebraicGeometry.RegularElements` is the monoid of nonzerodivisors.
* `AlgebraicGeometry.regularSymbol` is the symbol of the ring on a pair of nonzerodivisors.
* `AlgebraicGeometry.TameSymbol` packages a two-variable symbol on the fraction field, its
  multiplicativity, and agreement with the original module symbol.
* `AlgebraicGeometry.tameSymbol` is the resulting extension.

## Main results

* `AlgebraicGeometry.fractionGroupEquiv` identifies the Grothendieck group of the
  nonzerodivisors with the units of the fraction field.
* `AlgebraicGeometry.regularSymbol_mul_left`, `AlgebraicGeometry.regularSymbol_mul_right` and
  `AlgebraicGeometry.regularSymbol_swap` are the multiplicativity properties of the symbol on
  nonzerodivisors.

## Implementation notes

The fraction field is an arbitrary field realization `K` of the fraction ring of `A`.
Multiplicativity in both variables and agreement on nonzero elements of `A` determine the
extension uniquely. The structure makes these properties available to downstream statements
without unfolding the construction.

## References

* [Stacks Project, Tag 02Q1](https://stacks.math.columbia.edu/tag/02Q1)
-/

@[expose] public section

noncomputable section

namespace AlgebraicGeometry

universe u v

/-- The monoid of nonzerodivisors of a commutative ring. -/
abbrev RegularElements (A : Type u) [CommRing A] := nonZeroDivisors A

/-- Multiplication on the nonzerodivisors of a domain is cancellative. -/
instance regularElements_isCancelMul {A : Type u} [CommRing A] [IsDomain A] :
    IsCancelMul (RegularElements A) where
  mul_left_cancel a _ _ h := Subtype.ext <|
    mul_left_cancel₀ (mem_nonZeroDivisors_iff_ne_zero.mp a.property) (congrArg Subtype.val h)
  mul_right_cancel a _ _ h := Subtype.ext <|
    mul_right_cancel₀ (mem_nonZeroDivisors_iff_ne_zero.mp a.property) (congrArg Subtype.val h)

/-- A nonzerodivisor of a domain becomes a unit of its fraction field. -/
noncomputable def fractionUnitMap {A : Type u} [CommRing A] [IsDomain A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K] :
    RegularElements A →* Kˣ :=
  IsUnit.liftRight ((algebraMap A K).toMonoidHom.domRestrict (RegularElements A))
    (fun a ↦ IsLocalization.map_units K a)

/-- The induced map from the Grothendieck group of the nonzerodivisors to the units of the
fraction field. -/
noncomputable def fractionGroupMap {A : Type u} [CommRing A] [IsDomain A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K] :
    Algebra.GrothendieckGroup (RegularElements A) →* Kˣ :=
  Algebra.GrothendieckGroup.lift fractionUnitMap

/-- `fractionUnitMap` is the structure map of the fraction field. -/
theorem fractionUnitMap_val {A : Type u} [CommRing A] [IsDomain A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    (a : RegularElements A) :
    (fractionUnitMap (K := K) a : K) = algebraMap A K a :=
  IsUnit.coe_liftRight _ _ _

/-- `fractionGroupMap` takes a formal fraction to the corresponding quotient of units. -/
theorem fractionGroupMap_mk {A : Type u} [CommRing A] [IsDomain A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    (a b : RegularElements A) :
    fractionGroupMap (K := K) (Localization.mk a ⟨b, Submonoid.mem_top b⟩) =
      fractionUnitMap (K := K) a / fractionUnitMap (K := K) b := by
  rw [Localization.mk_eq_monoidOf_mk'_apply]
  change (Localization.monoidOf ⊤).lift (g := fractionUnitMap (K := K))
    (fun _ ↦ Group.isUnit _) ((Localization.monoidOf ⊤).mk' a
      ⟨b, Submonoid.mem_top b⟩) = _
  rw [Submonoid.LocalizationMap.lift_mk', div_eq_mul_inv]
  congr 1
  rw [Units.val_inv_eq_inv_val]
  exact congrArg Inv.inv (IsUnit.coe_liftRight _ _ _)

/-- `fractionGroupMap` is injective. -/
theorem fractionGroupMap_injective {A : Type u} [CommRing A] [IsDomain A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K] :
    Function.Injective (fractionGroupMap (A := A) (K := K)) := by
  intro x y h
  induction x, y using Localization.induction_on₂ with
  | H p q =>
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    apply (Localization.mk_eq_mk_iff').2
    apply Subtype.ext
    apply IsFractionRing.injective A K
    have h' := congrArg (fun z : Kˣ ↦ (z : K)) h
    rw [fractionGroupMap_mk, fractionGroupMap_mk] at h'
    simp only [Units.val_div_eq_div_val, fractionUnitMap_val] at h'
    have hne (x : RegularElements A) : algebraMap A K (x : A) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.property
    simpa only [Submonoid.coe_mul, map_mul, mul_comm] using (div_eq_div_iff (hne b) (hne d)).mp h'

/-- `fractionGroupMap` is surjective. -/
theorem fractionGroupMap_surjective {A : Type u} [CommRing A] [IsDomain A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K] :
    Function.Surjective (fractionGroupMap (A := A) (K := K)) := by
  intro z
  obtain ⟨a, b, hb, heq⟩ := IsFractionRing.div_surjective A (z : K)
  have ha : a ≠ 0 := by
    rintro rfl
    simp at heq
    exact z.ne_zero heq.symm
  let a' : RegularElements A := ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩
  let b' : RegularElements A := ⟨b, hb⟩
  refine ⟨Localization.mk a' ⟨b', Submonoid.mem_top b'⟩, ?_⟩
  apply Units.ext
  rw [fractionGroupMap_mk]
  simpa only [Units.val_div_eq_div_val, fractionUnitMap_val] using heq

/-- The Grothendieck group of the nonzerodivisors of a domain is the group of units of its
fraction field. -/
noncomputable def fractionGroupEquiv {A : Type u} [CommRing A] [IsDomain A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K] :
    Algebra.GrothendieckGroup (RegularElements A) ≃* Kˣ :=
  MulEquiv.ofBijective (fractionGroupMap (A := A) (K := K))
    ⟨fractionGroupMap_injective, fractionGroupMap_surjective⟩

/-- A nonzerodivisor of a domain acts regularly on the ring. -/
private theorem isSMulRegular_of_mem_regular {A : Type u} [CommRing A] (a : RegularElements A) :
    IsSMulRegular A (a : A) :=
  (isRegular_iff_mem_nonZeroDivisors.mpr a.property).isSMulRegular

/-- A one-dimensional Noetherian local ring has support dimension one as a module over itself. -/
private theorem supportDim_self_of_ringKrullDim_eq_one {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hdim : ringKrullDim A = 1) :
    Module.supportDim A A = 1 :=
  (Module.supportDim_self_eq_ringKrullDim A).trans hdim

/-- The symbol of a one-dimensional Noetherian local domain on a pair of nonzerodivisors. -/
noncomputable def regularSymbol {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] (hdim : ringKrullDim A = 1)
    (a b : RegularElements A) : (IsLocalRing.ResidueField A)ˣ :=
  moduleSymbol (M := A) a b
    (isRegular_iff_mem_nonZeroDivisors.mpr a.property).isSMulRegular
    (isRegular_iff_mem_nonZeroDivisors.mpr b.property).isSMulRegular
    ((Module.supportDim_self_eq_ringKrullDim A).trans hdim)

/-- The symbol on nonzerodivisors is multiplicative in its second argument. -/
theorem regularSymbol_mul_right {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] (hdim : ringKrullDim A = 1)
    (a b c : RegularElements A) :
    regularSymbol hdim a (b * c) =
      regularSymbol hdim a b * regularSymbol hdim a c :=
  moduleSymbol_mul_right (A := A) (M := A) a b c
    (isSMulRegular_of_mem_regular a)
    (isSMulRegular_of_mem_regular b)
    (isSMulRegular_of_mem_regular c)
    (supportDim_self_of_ringKrullDim_eq_one hdim)

/-- Swapping the arguments of the symbol on nonzerodivisors inverts it. -/
theorem regularSymbol_swap {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] (hdim : ringKrullDim A = 1)
    (a b : RegularElements A) :
    regularSymbol hdim a b * regularSymbol hdim b a = 1 :=
  moduleSymbol_mul_swap (A := A) (M := A) a b
    (isSMulRegular_of_mem_regular a)
    (isSMulRegular_of_mem_regular b)
    (supportDim_self_of_ringKrullDim_eq_one hdim)

/-- Swapping the arguments of the symbol on nonzerodivisors inverts it. -/
private theorem regularSymbol_eq_inv_swap {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] (hdim : ringKrullDim A = 1)
    (a b : RegularElements A) : regularSymbol hdim a b = (regularSymbol hdim b a)⁻¹ :=
  mul_eq_one_iff_eq_inv.mp (regularSymbol_swap hdim a b)

/-- The symbol on nonzerodivisors is multiplicative in its first argument. -/
theorem regularSymbol_mul_left {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] (hdim : ringKrullDim A = 1)
    (a b c : RegularElements A) :
    regularSymbol hdim (a * b) c =
      regularSymbol hdim a c * regularSymbol hdim b c := by
  rw [regularSymbol_eq_inv_swap hdim (a * b) c, regularSymbol_mul_right, mul_inv_rev,
    ← regularSymbol_eq_inv_swap hdim a c, ← regularSymbol_eq_inv_swap hdim b c]
  ac_rfl

/-- The symbol on nonzerodivisors is trivial on `1`. -/
theorem regularSymbol_one_right {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] (hdim : ringKrullDim A = 1)
    (a : RegularElements A) : regularSymbol hdim a 1 = 1 := by
  have h := regularSymbol_mul_right hdim a 1 1
  simp only [mul_one] at h
  apply mul_left_cancel (a := regularSymbol hdim a 1)
  simpa only [mul_one] using h.symm

/-- The symbol on nonzerodivisors as a bilinear monoid homomorphism. -/
noncomputable def regularSymbolHom {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] (hdim : ringKrullDim A = 1) :
    RegularElements A →* (RegularElements A →* (IsLocalRing.ResidueField A)ˣ) where
  toFun a := {
    toFun := regularSymbol hdim a
    map_one' := regularSymbol_one_right hdim a
    map_mul' := regularSymbol_mul_right hdim a }
  map_one' := by
    ext b
    have h : regularSymbol hdim 1 b = 1 :=
      (mul_eq_one_iff_eq_inv.mp (regularSymbol_swap hdim 1 b)).trans
        (by simp only [regularSymbol_one_right, inv_one])
    exact congrArg Units.val h
  map_mul' a b := by
    ext c
    exact congrArg Units.val (regularSymbol_mul_left hdim a b c)

/-- The symbol extended to the Grothendieck group of the nonzerodivisors. -/
noncomputable def groupSymbol {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] (hdim : ringKrullDim A = 1)
    (x y : Algebra.GrothendieckGroup (RegularElements A)) :
    (IsLocalRing.ResidueField A)ˣ :=
  Algebra.GrothendieckGroup.lift
    ((Algebra.GrothendieckGroup.lift (regularSymbolHom hdim)) x) y

/-- The extended symbol is multiplicative in its first argument. -/
theorem groupSymbol_mul_left {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] (hdim : ringKrullDim A = 1)
    (x x' y : Algebra.GrothendieckGroup (RegularElements A)) :
    groupSymbol hdim (x * x') y = groupSymbol hdim x y * groupSymbol hdim x' y := by
  simp only [groupSymbol, map_mul, Algebra.GrothendieckGroup.lift_apply,
    MonoidHom.mul_apply, div_eq_mul_inv, mul_inv_rev]
  ac_rfl

/-- The extended symbol is multiplicative in its second argument. -/
theorem groupSymbol_mul_right {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] (hdim : ringKrullDim A = 1)
    (x y y' : Algebra.GrothendieckGroup (RegularElements A)) :
    groupSymbol hdim x (y * y') = groupSymbol hdim x y * groupSymbol hdim x y' :=
  map_mul (Algebra.GrothendieckGroup.lift
    ((Algebra.GrothendieckGroup.lift (regularSymbolHom hdim)) x)) y y'

/-- The extended symbol agrees with the symbol on nonzerodivisors. -/
theorem groupSymbol_of {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] (hdim : ringKrullDim A = 1)
    (a b : RegularElements A) :
    groupSymbol hdim (Algebra.GrothendieckGroup.of a)
      (Algebra.GrothendieckGroup.of b) = regularSymbol hdim a b := by
  simp [groupSymbol, Algebra.GrothendieckGroup.lift,
    Algebra.GrothendieckGroup.of, regularSymbolHom]

/-- `fractionGroupEquiv` sends the unit of a nonzerodivisor back to its class. -/
theorem fractionGroupEquiv_symm_map_units {A : Type u} [CommRing A]
    [IsDomain A] {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    (a : RegularElements A) :
    (fractionGroupEquiv (A := A) (K := K)).symm
      (IsLocalization.map_units K a).unit = Algebra.GrothendieckGroup.of a := by
  apply (fractionGroupEquiv (A := A) (K := K)).injective
  rw [MulEquiv.apply_symm_apply]
  change (IsLocalization.map_units K a).unit =
    fractionGroupMap (K := K) (Localization.mk a (1 : (⊤ : Submonoid (RegularElements A))))
  rw [fractionGroupMap_mk]
  change (IsLocalization.map_units K a).unit =
    fractionUnitMap (K := K) a / fractionUnitMap (K := K) 1
  rw [map_one, div_one]
  exact Units.ext (fractionUnitMap_val (K := K) a).symm

/-- A multiplicative extension of the symbol from nonzero elements of a one-dimensional local
domain to units of its fraction field. -/
structure TameSymbol {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] {K : Type v} [Field K]
    [Algebra A K] [IsFractionRing A K] (hdim : ringKrullDim A = 1) where
  /-- The symbol of two units of the fraction field, a unit of the residue field. -/
  toFun : Kˣ → Kˣ → (IsLocalRing.ResidueField A)ˣ
  /-- The symbol is multiplicative in its first argument. -/
  map_mul_left (x x' y : Kˣ) :
    toFun (x * x') y = toFun x y * toFun x' y
  /-- The symbol is multiplicative in its second argument. -/
  map_mul_right (x y y' : Kˣ) :
    toFun x (y * y') = toFun x y * toFun x y'
  /-- On nonzerodivisors of `A` the symbol is `moduleSymbol` of `A` as a module over itself. -/
  eq_moduleSymbol (a b : A) (ha : IsRegular a) (hb : IsRegular b) :
    toFun
      (IsLocalization.map_units K
        ⟨a, isRegular_iff_mem_nonZeroDivisors.mp ha⟩).unit
      (IsLocalization.map_units K
        ⟨b, isRegular_iff_mem_nonZeroDivisors.mp hb⟩).unit =
      moduleSymbol (M := A) a b ha.isSMulRegular hb.isSMulRegular
        ((Module.supportDim_self_eq_ringKrullDim A).trans hdim)

/-- A bundled tame symbol acts as a two-variable map. -/
instance {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] {K : Type v} [Field K]
    [Algebra A K] [IsFractionRing A K] {hdim : ringKrullDim A = 1} :
    CoeFun (TameSymbol (K := K) hdim)
      (fun _ ↦ Kˣ → Kˣ → (IsLocalRing.ResidueField A)ˣ) :=
  ⟨TameSymbol.toFun⟩

/-- **Stacks Project, Tag 02Q1.** The tame symbol of a one-dimensional Noetherian local
domain, extended to its fraction field. -/
@[stacks 02Q1]
noncomputable def tameSymbol {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] {K : Type v} [Field K]
    [Algebra A K] [IsFractionRing A K] (hdim : ringKrullDim A = 1) :
    TameSymbol (K := K) hdim := by
  let e := fractionGroupEquiv (A := A) (K := K)
  refine {
    toFun := fun x y ↦ groupSymbol hdim (e.symm x) (e.symm y)
    map_mul_left := fun x x' y ↦ by rw [map_mul, groupSymbol_mul_left]
    map_mul_right := fun x y y' ↦ by rw [map_mul, groupSymbol_mul_right]
    eq_moduleSymbol := ?_ }
  intro a b ha hb
  let a' : RegularElements A := ⟨a, isRegular_iff_mem_nonZeroDivisors.mp ha⟩
  let b' : RegularElements A := ⟨b, isRegular_iff_mem_nonZeroDivisors.mp hb⟩
  change groupSymbol hdim (e.symm (IsLocalization.map_units K a').unit)
    (e.symm (IsLocalization.map_units K b').unit) = _
  rw [fractionGroupEquiv_symm_map_units a', fractionGroupEquiv_symm_map_units b',
    groupSymbol_of]
  rfl

end AlgebraicGeometry
