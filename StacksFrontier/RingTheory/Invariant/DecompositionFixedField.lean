module

public import StacksFrontier.RingTheory.Henselian.Canonicity
public import StacksFrontier.RingTheory.Henselian.IntegralDomain
public import StacksFrontier.RingTheory.Henselian.Henselization.AlgebraicInCompletion
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties
public import StacksFrontier.RingTheory.Invariant.InertiaFixedField
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fixed field of a decomposition group is the henselized fraction field

Let `(A, 𝔪, κ)` be a normal local domain with fraction field `K`, let `L / K` be a Galois
extension with `L` separably closed, let `B` be the integral closure of `A` in `L` and let `q` be
a prime of `B` lying over `𝔪`. Write `D = {σ ∈ Gal(L/K) | σ q = q}` for the decomposition group
at `q`. This file identifies the fixed field `L^D` with the fraction field `K^h` of a
henselization `A^h` of `A`, which is the step `K^h = (K^sep)^D` in the proof of Stacks 0BSW.

The argument is Hensel uniqueness, not invariant theory: the ring `B_q` of
`IsIntegralClosure.localizedSubring` is strictly henselian, so there is exactly one local
`A`-algebra map `A^h → B_q` (Stacks 04GS), and the two directions are

* an automorphism in `D` restricts to an `A`-algebra automorphism of `B_q`, so composing it with
  that map gives another local `A`-algebra map, hence the same one: `D` fixes the image of `A^h`;
* conversely an automorphism fixing the image of `A^h` pointwise is an automorphism of `L` over
  `A^h`, so it carries units of `B_q` to units; since membership in `q` is exactly non-unitness
  in `B_q`, it stabilizes `q`.

So the subgroup of `Gal(L/K)` fixing the image of `K^h` is exactly `D`, and the Galois
correspondence turns that into `L^D = K^h`. The argument never uses `(B_q)^D = A^h`: unlike the
inertia group, the invariants of `B_q` under `D` are not directly available as a henselization.

## Main results

* `IsIntegralClosure.henselizationToLocalizedSubring` — the canonical local `A`-algebra map
  `A^h → B_q`, and `IsIntegralClosure.henselizationToField` its composite with `B_q ⊆ L`.
* `IsIntegralClosure.mem_stabilizer_iff_apply_henselizationToField` — an automorphism lies in `D`
  exactly when it fixes the image of `A^h` pointwise.
* `IsIntegralClosure.exists_algHom_fieldRange_eq_fixedField_stabilizer` — **`K^h = L^D`**: the
  fraction field `K^h` of `A^h` embeds in `L` over `K`, compatibly with `A^h → B_q`, with image
  the fixed field of `D` and with `D` as the fixing subgroup of that image.

## Implementation notes

`B_q` is `IsIntegralClosure.localizedSubring q`, a subring of `L`, and is given its `A`-algebra
structure through the integral closure; that structure map is local because `q` lies over `𝔪`.
The restriction of an automorphism stabilizing `q` is
`IsIntegralClosure.localizedSubringEquivOfStabilizes`.

The preservation of units under an automorphism over a henselian local ring
(`IsIntegralClosure.isUnit_iff_isUnit_of_algEquiv`) is proved by passing to the integral closure
of the henselian base inside `L`, which is again a henselian local ring (Stacks 04GH) and carries
the automorphism; the comparison map to `B_q` is local because its source is integral over the
base.

The fraction field `K^h` is taken as data, with its `K`-algebra structure, rather than
constructed: the embedding `K^h → L` is the extension of `A^h → B_q ⊆ L`, which is injective
because `A^h` is a domain (Stacks 06DI) algebraic over `A` (Stacks 0A1W).

## References

* [Stacks Project, Tag 0BSW](https://stacks.math.columbia.edu/tag/0BSW)
* [Stacks Project, Tag 04GS](https://stacks.math.columbia.edu/tag/04GS)
* [Stacks Project, Tag 06DI](https://stacks.math.columbia.edu/tag/06DI)
* [Stacks Project, Tag 0A1W](https://stacks.math.columbia.edu/tag/0A1W)

## Tags

decomposition group, fixed field, henselization, fraction field, Galois action
-/

@[expose] public noncomputable section

universe u

open IsLocalRing

namespace IsIntegralClosure

section Base

variable {A L : Type u} [CommRing A] [Field L] [Algebra A L]
  (q : Ideal (integralClosure A L)) [q.IsPrime]

/-! ### `B_q` as an `A`-algebra -/

/-- The structure map `A → B_q`, through the integral closure. -/
instance algebraLocalizedSubringBase : Algebra A (localizedSubring q) :=
  ((algebraMap (integralClosure A L) (localizedSubring q)).comp
    (algebraMap A (integralClosure A L))).toAlgebra

/-- The structure map `A → B_q` factors through the integral closure. -/
theorem algebraMap_localizedSubringBase (a : A) :
    algebraMap A (localizedSubring q) a =
      algebraMap (integralClosure A L) (localizedSubring q)
        (algebraMap A (integralClosure A L) a) := rfl

/-- The structure map `A → B_q` is the structure map `A → L`, read inside `L`. -/
theorem coe_algebraMap_localizedSubringBase (a : A) :
    ((algebraMap A (localizedSubring q) a : localizedSubring q) : L) = algebraMap A L a := by
  rw [algebraMap_localizedSubringBase, coe_algebraMap_localizedSubring]
  exact (IsScalarTower.algebraMap_apply A (integralClosure A L) L a).symm

/-- `A → B_q → L` is `A → L`. -/
instance isScalarTower_localizedSubringBase : IsScalarTower A (localizedSubring q) L :=
  .of_algebraMap_eq fun a => (coe_algebraMap_localizedSubringBase q a).symm

/-- **The structure map `A → B_q` is a local ring map**, because `q` lies over the maximal ideal
of `A`. -/
instance isLocalHom_algebraMap_localizedSubring [IsLocalRing A]
    [q.LiesOver (maximalIdeal A)] :
    IsLocalHom (algebraMap A (localizedSubring q)) := by
  refine ⟨fun a hu => ?_⟩
  by_contra hna
  have haM : a ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal a).mpr hna
  rw [Ideal.LiesOver.over (P := q) (p := maximalIdeal A)] at haM
  have hmem : (algebraMap A (localizedSubring q) a) ∈ maximalIdeal (localizedSubring q) := by
    rw [algebraMap_localizedSubringBase]
    exact algebraMap_mem_maximalIdeal_localizedSubring q haM
  exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem) hu

end Base

/-- **A henselization of a normal local domain is a normal domain**, by Stacks Tag 06DI applied
to a strict henselization of `A`, which exists by Stacks Tag 04GP. -/
@[ega "IV 7.5.3" "(vi), special case"]
theorem isDomain_and_isIntegrallyClosed_henselization (A Ah : Type u) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [IsLocalRing A] [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsLocalRing.IsHenselization A (ResidueField A) Ah] :
    IsDomain Ah ∧ IsIntegrallyClosed Ah := by
  obtain ⟨Rsh, _, _, _, hsh⟩ := IsLocalRing.exists_isHenselization_separableClosure A
  let := hsh
  refine ((isNormalDomain_tfae_henselization_strictHenselization A Ah Rsh
    (SeparableClosure (ResidueField A))).out 1 2).mp ?_
  exact ⟨‹IsDomain A›, ‹IsIntegrallyClosed A›⟩

section Decomposition

open scoped Pointwise

variable (A K L : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsFractionRing A K] [IsGalois K L]

attribute [local instance] galAction galSMulCommClass

/-! ### Units and automorphisms over a henselian base -/

section Generic

variable {R T E : Type*} [CommRing R] [HenselianLocalRing R] [CommRing T] [IsLocalRing T]
  [IsDomain T] [IsIntegrallyClosed T] [Field E] [Algebra R T]
  [IsLocalHom (algebraMap R T)] [Algebra T E] [IsFractionRing T E] [Algebra R E]
  [IsScalarTower R T E]

omit [IsDomain T] [IsIntegrallyClosed T] in
/-- An `R`-algebra map from a local ring integral over the henselian local ring `R` to a local
`R`-algebra with `R → T` local is itself local: the contraction of the maximal ideal of `T` is a
prime of `C` contracting to the maximal ideal of `R`, hence maximal because `C` is integral
over `R`. -/
private theorem isLocalHom_of_isIntegral_source
    {C : Type*} [CommRing C] [IsLocalRing C] [Algebra R C] [Algebra.IsIntegral R C]
    (f : C →ₐ[R] T) : IsLocalHom f := by
  let P := (maximalIdeal T).comap f.toRingHom
  have hP : P.IsPrime := Ideal.comap_isPrime _ _
  have hc : P.comap (algebraMap R C) = maximalIdeal R := by
    rw [Ideal.comap_comap,
      show f.toRingHom.comp (algebraMap R C) = algebraMap R T from RingHom.ext f.commutes]
    exact maximalIdeal_comap (algebraMap R T)
  have hm : P.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) P
      (by rw [Ideal.under_def, hc]; infer_instance)
  exact ⟨(((local_hom_TFAE f.toRingHom).out 5 1).mp (eq_maximalIdeal hm) :
    IsLocalHom f.toRingHom).map_nonunit⟩

omit [HenselianLocalRing R] [IsLocalRing T] [IsDomain T] [IsLocalHom (algebraMap R T)] in
/-- The integral closure of `R` in the fraction field `E` of a normal domain `T` maps into `T`,
compatibly with the inclusions into `E`. -/
private theorem exists_algHom_integralClosure_of_isIntegrallyClosed :
    ∃ f : integralClosure R E →ₐ[R] T, ∀ x, algebraMap T E (f x) = (x : E) := by
  let j := IsScalarTower.toAlgHom R T E
  let e := AlgEquiv.ofInjective j (IsFractionRing.injective T E)
  let k : integralClosure R E →ₐ[R] j.range :=
    (integralClosure R E).val.codRestrict j.range fun x =>
      IsIntegrallyClosed.algebraMap_eq_of_integral (x.property.tower_top (A := T))
  exact ⟨e.symm.toAlgHom.comp k, fun x => congrArg Subtype.val (e.apply_symm_apply (k x))⟩

omit [IsDomain T] in
/-- **An automorphism over a henselian local ring preserves units.** If `σ` is an automorphism of
`E` over the henselian local ring `R` and carries `b : T` to `c : T`, with `b` integral over `R`,
then `b` is a unit exactly when `c` is: both are read off from the integral closure of `R` in
`E`, a henselian local ring on which `σ` acts. -/
private theorem isUnit_iff_isUnit_of_algEquiv (σ : E ≃ₐ[R] E) (b c : T)
    (hb : IsIntegral R (algebraMap T E b)) (hσ : σ (algebraMap T E b) = algebraMap T E c) :
    IsUnit b ↔ IsUnit c := by
  obtain ⟨hC, -, -⟩ := RingHom.exists_henselianLocalRing_of_isIntegral_of_isDomain
    (algebraMap R (integralClosure R E)) (Algebra.IsIntegral.isIntegral (R := R))
  let : HenselianLocalRing (integralClosure R E) := hC
  obtain ⟨f, hf⟩ := exists_algHom_integralClosure_of_isIntegrallyClosed (R := R) (T := T) (E := E)
  let : IsLocalHom f := isLocalHom_of_isIntegral_source f
  let e : integralClosure R E ≃ₐ[R] integralClosure R E := σ.mapIntegralClosure
  let x : integralClosure R E := ⟨algebraMap T E b, hb⟩
  have hfb : f x = b := IsFractionRing.injective T E (hf x)
  have hfc : f (e x) = c := IsFractionRing.injective T E ((hf (e x)).trans hσ)
  rw [← hfb, ← hfc, isUnit_map_iff f, isUnit_map_iff f, isUnit_map_iff e]

/-- **An `R`-algebra map from a domain algebraic over `R` into a field is injective**, provided
the structure map of the field is. If `x ≠ 0` is killed, divide the largest power of `X` out of
an annihilating polynomial: the remaining factor annihilates `x` too and has a nonzero constant
term, which the map sends to zero. -/
private theorem injective_of_isAlgebraic {R S E : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] [Field E] [Algebra R S] [Algebra R E] [Algebra.IsAlgebraic R S] (f : S →ₐ[R] E)
    (hinj : Function.Injective (algebraMap R E)) : Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  obtain ⟨p, hp, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) x
  set n := p.rootMultiplicity 0 with hn
  set g := p /ₘ (Polynomial.X - Polynomial.C (0 : R)) ^ n with hg
  have hpg : (Polynomial.X - Polynomial.C (0 : R)) ^ n * g = p :=
    Polynomial.pow_mul_divByMonic_rootMultiplicity_eq p 0
  have hg0 : g.coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero 0 hp
  have hmul : x ^ n * Polynomial.aeval x g = 0 := by
    rw [← hpx, ← hpg, map_mul, map_pow]
    simp
  have hgx : Polynomial.aeval x g = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero n hx0)
  have hfg := congrArg f hgx
  rw [← Polynomial.aeval_algHom_apply, hx, map_zero, Polynomial.aeval_def,
    Polynomial.eval₂_at_zero] at hfg
  exact hg0 (hinj (by simpa using hfg))

/-- Membership in the fixing subgroup of the range of an embedding of a fraction field is tested
on the base ring. -/
private theorem mem_fixingSubgroup_fieldRange_iff {F S E E' : Type*} [Field F] [CommRing S]
    [Field E] [Field E'] [Algebra F E] [Algebra F E'] [Algebra S E] [IsFractionRing S E]
    (j : E →ₐ[F] E') (σ : Gal(E'/F)) :
    σ ∈ j.fieldRange.fixingSubgroup ↔
      ∀ a : S, σ (j (algebraMap S E a)) = j (algebraMap S E a) := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  refine ⟨fun h a => h _ (AlgHom.mem_fieldRange.mpr ⟨_, rfl⟩), fun h x hx => ?_⟩
  obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
  have he : σ.toRingHom.comp j.toRingHom = j.toRingHom := IsFractionRing.ringHom_ext (A := S) h
  exact RingHom.congr_fun he y

end Generic

/-! ### An automorphism stabilizing `q` restricts to `B_q` -/

/-- An automorphism of `L` over `K` stabilizing `q` restricts to an `A`-algebra automorphism of
`B_q`, by `IsIntegralClosure.smul_mem_localizedSubring`. -/
def localizedSubringEquivOfStabilizes (q : Ideal (integralClosure A L)) [q.IsPrime]
    {σ : Gal(L/K)} (hσ : σ • q = q) : localizedSubring q ≃ₐ[A] localizedSubring q where
  toFun x := ⟨σ (x : L), smul_mem_localizedSubring A K L q hσ x.2⟩
  invFun x := ⟨σ⁻¹ (x : L), smul_mem_localizedSubring A K L q
    (by conv_lhs => rw [← hσ]
        exact inv_smul_smul σ q) x.2⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply (x : L))
  right_inv x := Subtype.ext (σ.apply_symm_apply (x : L))
  map_mul' _ _ := Subtype.ext (map_mul σ _ _)
  map_add' _ _ := Subtype.ext (map_add σ _ _)
  commutes' a := Subtype.ext (by
    change σ ((algebraMap A (localizedSubring q) a : localizedSubring q) : L) = _
    rw [coe_algebraMap_localizedSubringBase q a, IsScalarTower.algebraMap_apply A K L a]
    exact σ.commutes _)

include K in
/-- The restriction of `σ` to `B_q` is `σ`, read inside `L`. -/
theorem coe_localizedSubringEquivOfStabilizes (q : Ideal (integralClosure A L)) [q.IsPrime]
    {σ : Gal(L/K)} (hσ : σ • q = q) (x : localizedSubring q) :
    ((localizedSubringEquivOfStabilizes A K L q hσ x : localizedSubring q) : L) = σ (x : L) :=
  rfl

/-! ### The canonical map from the henselization -/

section Henselization

variable [IsLocalRing A] [IsSepClosed L]
  (q : Ideal (integralClosure A L)) [q.IsPrime] [q.LiesOver (maximalIdeal A)]
  (Ah : Type u) [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
  [IsLocalRing.IsHenselization A (ResidueField A) Ah]

omit [IsIntegrallyClosed A] in
include K in
/-- **There is exactly one local `A`-algebra map `A^h → B_q`**, by the universal property of the
henselization (Stacks 04GS): `B_q` is henselian local and `A → B_q` is local. -/
theorem existsUnique_isLocalHom_algHom_localizedSubring :
    ∃! φ : Ah →ₐ[A] localizedSubring q, IsLocalHom φ := by
  let := (henselianLocalRing_and_isSepClosed_localizedSubring A K L q).1
  let : IsLocalHom (algebraMap A Ah) :=
    IsLocalRing.IsHenselization.isLocalHom (R := A) (L := ResidueField A) (Rh := Ah)
  have hres : Function.Surjective (ResidueField.map (algebraMap A Ah)) := by
    obtain ⟨e, he⟩ := IsLocalRing.IsHenselization.exists_residueFieldEquiv
      (R := A) (L := ResidueField A) (Rh := Ah)
    have hm : ResidueField.map (algebraMap A Ah) = (e : ResidueField A →+* ResidueField Ah) := by
      ext x
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
      rw [ResidueField.map_residue]
      simpa using (he a).symm
    rw [hm]
    exact e.surjective
  exact HenselianLocalRing.existsUnique_isLocalHom_of_ind_etale
    (IsLocalRing.IsHenselization.ind_etale (R := A) (L := ResidueField A) (Rh := Ah)) hres

/-- **The canonical local `A`-algebra map `A^h → B_q`**, the unique one given by
`IsIntegralClosure.existsUnique_isLocalHom_algHom_localizedSubring`. -/
def henselizationToLocalizedSubring : Ah →ₐ[A] localizedSubring q :=
  (existsUnique_isLocalHom_algHom_localizedSubring A K L q Ah).choose

omit [IsIntegrallyClosed A] in
/-- The canonical map `A^h → B_q` is a local ring map. -/
theorem isLocalHom_henselizationToLocalizedSubring :
    IsLocalHom (henselizationToLocalizedSubring A K L q Ah) :=
  (existsUnique_isLocalHom_algHom_localizedSubring A K L q Ah).choose_spec.1

omit [IsIntegrallyClosed A] in
/-- Every local `A`-algebra map `A^h → B_q` is the canonical one. -/
theorem eq_henselizationToLocalizedSubring (φ : Ah →ₐ[A] localizedSubring q)
    (hφ : IsLocalHom φ) : φ = henselizationToLocalizedSubring A K L q Ah :=
  (existsUnique_isLocalHom_algHom_localizedSubring A K L q Ah).choose_spec.2 φ hφ

/-- **The embedding `A^h → K^sep`** attached to the choice of `𝔪^sep`: the canonical local map
`A^h → B_q` read inside `L`. -/
def henselizationToField : Ah →ₐ[A] L :=
  (IsScalarTower.toAlgHom A (localizedSubring q) L).comp
    (henselizationToLocalizedSubring A K L q Ah)

omit [IsIntegrallyClosed A] in
/-- The embedding `A^h → L` is the canonical map `A^h → B_q`, read inside `L`. -/
theorem henselizationToField_apply (x : Ah) :
    henselizationToField A K L q Ah x =
      ((henselizationToLocalizedSubring A K L q Ah x : localizedSubring q) : L) := rfl

/-- **The decomposition group fixes `K^h` pointwise.** An automorphism stabilizing `q` restricts
to an `A`-algebra automorphism of `B_q`, and composing the canonical map `A^h → B_q` with it
gives another local `A`-algebra map, hence the same one. -/
theorem apply_henselizationToField_of_stabilizes {σ : Gal(L/K)} (hσ : σ • q = q) (x : Ah) :
    σ (henselizationToField A K L q Ah x) = henselizationToField A K L q Ah x := by
  set e := localizedSubringEquivOfStabilizes A K L q hσ with he
  set φ := henselizationToLocalizedSubring A K L q Ah with hφ
  have hloc : IsLocalHom (e.toAlgHom.comp φ) := by
    refine ⟨fun a ha => ?_⟩
    refine (isLocalHom_henselizationToLocalizedSubring A K L q Ah).map_nonunit a ?_
    have h := ha.map e.symm
    rwa [show e.symm ((e.toAlgHom.comp φ) a) = φ a from e.symm_apply_apply (φ a)] at h
  have hcomp : e.toAlgHom.comp φ = φ :=
    (eq_henselizationToLocalizedSubring A K L q Ah _ hloc).trans hφ.symm
  have hx := AlgHom.congr_fun hcomp x
  exact congrArg (fun z : localizedSubring q => (z : L)) hx

omit [IsIntegrallyClosed A] in
/-- **An automorphism of `K^sep` over `K` fixing `K^h` pointwise stabilizes `𝔪^sep`.** It is then
an automorphism over `A^h`, so it preserves units of `B_q` by
`IsIntegralClosure.isUnit_iff_isUnit_of_algEquiv`, and membership in `q` is non-unitness. -/
theorem stabilizes_of_apply_henselizationToField {σ : Gal(L/K)}
    (hσ : ∀ x : Ah, σ (henselizationToField A K L q Ah x) = henselizationToField A K L q Ah x) :
    σ • q = q := by
  let : Algebra Ah (localizedSubring q) :=
    (henselizationToLocalizedSubring A K L q Ah).toRingHom.toAlgebra
  let : Algebra Ah L := (henselizationToField A K L q Ah).toRingHom.toAlgebra
  let : IsScalarTower Ah (localizedSubring q) L := .of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A Ah L :=
    .of_algebraMap_eq fun a => ((henselizationToField A K L q Ah).commutes a).symm
  let : IsLocalHom (algebraMap Ah (localizedSubring q)) :=
    ⟨(isLocalHom_henselizationToLocalizedSubring A K L q Ah).map_nonunit⟩
  let : HenselianLocalRing Ah :=
    IsLocalRing.IsHenselization.henselian (R := A) (L := ResidueField A) (Rh := Ah)
  let := isIntegrallyClosed_localizedSubring A K L q
  let := isFractionRing_localizedSubring A K L q
  let σ' : L ≃ₐ[Ah] L := { σ.toRingEquiv with commutes' := hσ }
  have hmem : ∀ b : integralClosure A L, σ • b ∈ q ↔ b ∈ q := by
    intro b
    have hcoe : ∀ c : integralClosure A L,
        algebraMap (localizedSubring q) L
            (algebraMap (integralClosure A L) (localizedSubring q) c) = (c : L) := fun c => by
      rw [algebraMap_localizedSubring_field, coe_algebraMap_localizedSubring]
    have hb : IsIntegral Ah (algebraMap (localizedSubring q) L
        (algebraMap (integralClosure A L) (localizedSubring q) b)) := by
      rw [hcoe b]
      exact b.2.tower_top (A := Ah)
    have hσ' : σ' (algebraMap (localizedSubring q) L
          (algebraMap (integralClosure A L) (localizedSubring q) b)) =
        algebraMap (localizedSubring q) L
          (algebraMap (integralClosure A L) (localizedSubring q) (σ • b)) := by
      rw [hcoe b, hcoe (σ • b)]
      show σ (b : L) = ((σ • b : integralClosure A L) : L)
      exact (coe_smul A K L σ b).symm
    have hunit := isUnit_iff_isUnit_of_algEquiv (R := Ah) (T := localizedSubring q) (E := L) σ'
      (algebraMap (integralClosure A L) (localizedSubring q) b)
      (algebraMap (integralClosure A L) (localizedSubring q) (σ • b)) hb hσ'
    have hiff : ∀ c : integralClosure A L,
        c ∈ q ↔ ¬ IsUnit (algebraMap (integralClosure A L) (localizedSubring q) c) := by
      intro c
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (localizedSubring q) q c,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [hiff (σ • b), hiff b, not_iff_not, hunit]
  ext b
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  simpa only [smul_inv_smul] using (hmem (σ⁻¹ • b)).symm

include K in
/-- **Stacks Project, Tag 0BSW: `K^h = (K^sep)^D`, in the form of the fixing subgroup.** An
automorphism of `K^sep` over `K` lies in the decomposition group `D` at `𝔪^sep` exactly when it
fixes the image of the henselization `A^h` pointwise, that is exactly when it fixes `K^h`. -/
theorem mem_stabilizer_iff_apply_henselizationToField (σ : Gal(L/K)) :
    σ ∈ MulAction.stabilizer Gal(L/K) q ↔
      ∀ x : Ah, σ (henselizationToField A K L q Ah x) = henselizationToField A K L q Ah x :=
  ⟨fun hσ => apply_henselizationToField_of_stabilizes A K L q Ah
      (MulAction.mem_stabilizer_iff.mp hσ),
    fun h => MulAction.mem_stabilizer_iff.mpr
      (stabilizes_of_apply_henselizationToField A K L q Ah h)⟩

include K in
/-- **The embedding `K^h → K^sep` is injective on `A^h`.** The henselization is a domain
algebraic over `A` (Stacks Tag 0A1W) and `A → K^sep` is injective. -/
theorem injective_henselizationToField :
    Function.Injective (henselizationToField A K L q Ah) := by
  let := (isDomain_and_isIntegrallyClosed_henselization A Ah).1
  let : Algebra.IsAlgebraic A Ah := ⟨IsLocalRing.isAlgebraic_of_isHenselization A Ah⟩
  refine injective_of_isAlgebraic _ ?_
  rw [IsScalarTower.algebraMap_eq A K L]
  exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)

/-- **Stacks Project, Tag 0BSW: `K^h = (K^sep)^D`.** Let `(A, 𝔪, κ)` be a normal local domain
with fraction field `K`, let `K^sep` be a separable closure of `K`, let `𝔪^sep = q` be a prime of
the integral closure `A^sep` of `A` in `K^sep` lying over `𝔪`, let `A^h` be a henselization of
`A` and let `K^h` be its fraction field. Then `K^h` embeds in `K^sep` over `K`, compatibly with
the canonical local map `A^h → (A^sep)_{𝔪^sep}`, in such a way that the subgroup of
`Gal(K^sep/K)` fixing its image is exactly the decomposition group
`D = {σ | σ 𝔪^sep = 𝔪^sep}`; equivalently the image of `K^h` is the fixed field `(K^sep)^D`.

Together with Stacks Tag 0BNE — under which the image of `π₁(Spec K^h)` in `π₁(Spec K)` is the
subgroup of `Gal(K^sep/K)` fixing `K^h` — this is the identification `π₁(U^h) = D` of the top
row of the diagram of Tag 0BSV. -/
@[stacks 0BSW "the identification K^h = (K^sep)^D of the middle of the top row of the diagram: \
the fixed field of the decomposition group D is the fraction field of a henselization of A, \
embedded in K^sep compatibly with the canonical local map to (A^sep)_{𝔪^sep}"]
theorem exists_algHom_fieldRange_eq_fixedField_stabilizer
    (Kh : Type u) [Field Kh] [Algebra Ah Kh] [IsFractionRing Ah Kh]
    [Algebra A Kh] [IsScalarTower A Ah Kh] [Algebra K Kh] [IsScalarTower A K Kh] :
    ∃ j : Kh →ₐ[K] L,
      (∀ x : Ah, j (algebraMap Ah Kh x) = henselizationToField A K L q Ah x) ∧
      j.fieldRange.fixingSubgroup = MulAction.stabilizer Gal(L/K) q ∧
      j.fieldRange = IntermediateField.fixedField (MulAction.stabilizer Gal(L/K) q) := by
  let := (isDomain_and_isIntegrallyClosed_henselization A Ah).1
  have hinj := injective_henselizationToField A K L q Ah
  set j0 : Kh →ₐ[A] L := IsFractionRing.liftAlgHom (R := A) hinj with hj0
  have hj0a : ∀ x : Ah, j0 (algebraMap Ah Kh x) = henselizationToField A K L q Ah x := fun x =>
    IsFractionRing.lift_algebraMap hinj x
  have hcomm : ∀ c : K, j0 (algebraMap K Kh c) = algebraMap K L c := by
    have h : ∀ a : A, (j0.toRingHom.comp (algebraMap K Kh)) (algebraMap A K a) =
        (algebraMap K L : K →+* L) (algebraMap A K a) := by
      intro a
      show j0 (algebraMap K Kh (algebraMap A K a)) = algebraMap K L (algebraMap A K a)
      rw [← IsScalarTower.algebraMap_apply A K Kh a, ← IsScalarTower.algebraMap_apply A K L a]
      exact j0.commutes a
    have hK : j0.toRingHom.comp (algebraMap K Kh) = (algebraMap K L : K →+* L) :=
      IsFractionRing.ringHom_ext (A := A) h
    exact fun c => RingHom.congr_fun hK c
  set j : Kh →ₐ[K] L := { j0.toRingHom with commutes' := hcomm } with hj
  have hja : ∀ x : Ah, j (algebraMap Ah Kh x) = henselizationToField A K L q Ah x := hj0a
  have hfix : j.fieldRange.fixingSubgroup = MulAction.stabilizer Gal(L/K) q := by
    ext σ
    rw [mem_fixingSubgroup_fieldRange_iff (S := Ah) j σ,
      mem_stabilizer_iff_apply_henselizationToField A K L q Ah σ]
    simp only [hja]
  exact ⟨j, hja, hfix, by rw [← hfix, InfiniteGalois.fixedField_fixingSubgroup]⟩

end Henselization

end Decomposition

end IsIntegralClosure

end
