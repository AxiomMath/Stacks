module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ModelPicardNumericalType
public import StacksFrontier.AlgebraicGeometry.Curves.Models.TrivialTensorPower
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.PicardGroup.Defs
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The torsion exact sequence of the Picard groups of a regular model

Let `X ⟶ Spec(R)` be a regular proper model of a smooth projective curve `C` over the fraction
field of a discrete valuation ring, write the special fibre as `X_k = Σ mᵢ Cᵢ`, put
`d = gcd(m₁, …, mₙ)`, and let `T` be the numerical type associated to `X`. For an integer
`h ≥ 1` prime to `d`, [Stacks, Tag 0CAD] asserts the existence of an exact sequence

`0 ⟶ Pic(X)[h] ⟶ Pic(C)[h] ⟶ Pic(T)[h]`.

The two maps are constructed: the first is the restriction to `h`-torsion of the restriction of
Picard classes to the generic fibre, the second the restriction to `h`-torsion of the canonical
map `Pic(C) ⟶ Pic(T)` of [Stacks, Tag 0CAC]. The theorem is that the first is injective and that
the kernel of the second is the image of the first, the latter in Mathlib's `Function.Exact`
vocabulary.

The `h`-torsion of an abelian group `A` is `Submodule.torsionBy ℤ A h`, the kernel of
multiplication by `h` viewed as a `ℤ`-submodule; `Stacks.Picard.mem_torsionBy_iff_mem_zsmulTorsion`
identifies its carrier with the set `Stacks.Picard.zsmulTorsion A h` used elsewhere in the
development.

## Main definitions

* `Stacks.Picard.zsmulTorsionRestrict` — the restriction `A[h] →ₗ[ℤ] B[h]` of a homomorphism of
  abelian groups to `h`-torsion.
* `Stacks.Models.RegularProperModelSituation.picardTorsionRestriction` — the first map
  `Pic(X)[h] ⟶ Pic(C)[h]`.
* `Stacks.Models.RegularProperModelSituation.picardTorsionToNumericalType` — the second map
  `Pic(C)[h] ⟶ Pic(T)[h]`.

## Main results

* `Stacks.Models.eq_zero_of_zsmul_eq_zero_of_coprime` — an element killed by two coprime
  integers is zero.
* `Stacks.Models.injective_zsmulTorsionRestrict` and `Stacks.Models.exact_zsmulTorsionRestrict`
  — the two clauses for abstract abelian groups, from the kernel description of Tag 0CAC and the
  `d`-torsion statement of Tag 0CAB.
* `Stacks.Models.RegularProperModelSituation.injective_picardTorsionRestriction` — exactness at
  `Pic(X)[h]`.
* `Stacks.Models.RegularProperModelSituation.picardTorsionSequence_exact` — [Stacks, Tag 0CAD].

## The proof

*Injectivity.* Let `ξ ∈ Pic(X)[h]` restrict to `0` on `C`. Its degree on every component is
`0`, because `ℤ` is torsion-free; so [Stacks, Tag 0CAB] gives `d ξ = 0`. As `h ξ = 0` and `h` is
prime to `d`, `ξ = 0`. (The source takes `h`-torsion in the sequence of [Stacks, Tag 0C63]; the
`d`-torsion statement of Tag 0CAB packages the same computation.)

*Exactness at the middle.* A class `ξ = ρ(x)` with `h x = 0` has degree `0` on every component,
so it is in the kernel of the map of Tag 0CAC. Conversely let `ξ ∈ Pic(C)[h]` die in
`Pic(T)[h]`. By Tag 0CAC there is `x` of degree `0` on every component with `ρ(x) = ξ`. Then
`h x` is trivial on `C` and of degree `0`, so Tag 0CAB gives `d h x = 0`. Pick `d'` and `c` with
`d' d + c h = 1`; then `y = (d' d) x` satisfies `h y = 0` and `ρ(y) = (1 - c h) ξ = ξ`. This is
the source's `ℒ^{⊗dd'}`.

## References

* [Stacks Project, Tag 0CAD](https://stacks.math.columbia.edu/tag/0CAD)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C63](https://stacks.math.columbia.edu/tag/0C63)
* [Stacks Project, Tag 0CAB](https://stacks.math.columbia.edu/tag/0CAB)
* [Stacks Project, Tag 0CAC](https://stacks.math.columbia.edu/tag/0CAC)
* [Stacks Project, Tag 0CA5](https://stacks.math.columbia.edu/tag/0CA5)
* [Stacks Project, Tag 0C7H](https://stacks.math.columbia.edu/tag/0C7H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Divisors
open Stacks.Picard (ofScheme zsmulTorsion)

universe u

namespace Stacks.Picard

/-! ### Restricting a homomorphism to `h`-torsion -/

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- The `n`-torsion submodule `A[n] = Submodule.torsionBy ℤ A n` has for carrier the set
`Stacks.Picard.zsmulTorsion A n` of elements killed by `n`. -/
theorem mem_torsionBy_iff_mem_zsmulTorsion (n : ℤ) (x : A) :
    x ∈ Submodule.torsionBy ℤ A n ↔ x ∈ zsmulTorsion A n :=
  Submodule.mem_torsionBy_iff n x

/-- **The restriction `A[n] ⟶ B[n]` of a homomorphism of abelian groups to `n`-torsion.** A
homomorphism carries `n`-torsion to `n`-torsion, so it restricts; the restriction is `ℤ`-linear
because every homomorphism of abelian groups is. -/
def zsmulTorsionRestrict (f : A →+ B) (n : ℤ) :
    Submodule.torsionBy ℤ A n →ₗ[ℤ] Submodule.torsionBy ℤ B n :=
  LinearMap.restrict f.toIntLinearMap fun x hx => by
    rw [Submodule.mem_torsionBy_iff] at hx ⊢
    change n • f x = 0
    rw [← map_zsmul, hx, map_zero]

/-- The restriction `zsmulTorsionRestrict f n` sends an `n`-torsion element `x` to `f x`. -/
@[simp]
theorem zsmulTorsionRestrict_coe (f : A →+ B) (n : ℤ) (x : Submodule.torsionBy ℤ A n) :
    ((zsmulTorsionRestrict f n x : B)) = f (x : A) := rfl

end Stacks.Picard

namespace Stacks.Models

/-! ### The group-theoretic core of the two exactness clauses -/

/-- **An `h`-torsion class has degree zero on every component.** More precisely: a homomorphism
from an abelian group to `ℤ^{⊕n}`, which is torsion-free, kills `h`-torsion for `h ≠ 0`. This is
the step of [Stacks, Tag 0CAD] that the source makes by passing from `ℒ` to `ℒ^{⊗h}`. -/
theorem map_eq_zero_of_zsmul_eq_zero {PX ι : Type*} [AddCommGroup PX] {h : ℕ}
    (deg : PX →+ (ι → ℤ)) (hh : h ≠ 0) {x : PX}
    (hx : (h : ℤ) • x = 0) : deg x = 0 := by
  have hdx : (h : ℤ) • deg x = 0 := by rw [← map_zsmul, hx, map_zero]
  exact (smul_eq_zero.mp hdx).resolve_left (Int.natCast_ne_zero.mpr hh)

/-- **An element killed by two coprime integers is zero.** If `h • x = 0` and `d • x = 0` with
`gcd(h, d) = 1`, then a Bézout relation `1 = a h + b d` gives `x = a (h • x) + b (d • x) = 0`. -/
theorem eq_zero_of_zsmul_eq_zero_of_coprime {A : Type*} [AddCommGroup A] {h d : ℕ}
    (hcop : Nat.Coprime h d) {x : A} (hh : (h : ℤ) • x = 0) (hd : (d : ℤ) • x = 0) :
    x = 0 := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  rw [← one_smul ℤ x, ← hab, add_smul, mul_smul, mul_smul, hh, hd, smul_zero, smul_zero,
    add_zero]

/-- The restriction of `f` to `n`-torsion kills `x` exactly when `f` kills `x`. -/
private theorem zsmulTorsionRestrict_eq_zero_iff {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (n : ℤ) (x : Submodule.torsionBy ℤ A n) :
    Stacks.Picard.zsmulTorsionRestrict f n x = 0 ↔ f x = 0 :=
  Subtype.ext_iff

section Abstract

variable {PX PC PT : Type*} [AddCommGroup PX] [AddCommGroup PC] [AddCommGroup PT]
  {ι : Type*} [Fintype ι] (m : ι → ℕ) {h : ℕ}

/-- **The group-theoretic core of exactness at `Pic(X)[h]` in [Stacks, Tag 0CAD].** Let
`ρ : PX ⟶ PC` and `deg : PX ⟶ ℤ^{⊕n}` be homomorphisms of abelian groups such that an element
killed by `ρ` and by `deg` is killed by `d = gcd(mᵢ)` (this is [Stacks, Tag 0CAB]). If `h ≠ 0` is
prime to `d`, then an `h`-torsion element of `PX` killed by `ρ` is zero: it has degree `0`
because `ℤ^{⊕n}` is torsion-free, so it is killed by both `h` and `d`. -/
theorem eq_zero_of_zsmul_eq_zero_of_map_eq_zero (ρ : PX →+ PC) (deg : PX →+ (ι → ℤ))
    (htriv : ∀ x : PX, ρ x = 0 → deg x = 0 → ((Finset.univ.gcd m : ℕ) : ℤ) • x = 0)
    (hh : h ≠ 0) (hcop : Nat.Coprime h (Finset.univ.gcd m))
    {x : PX} (hx : (h : ℤ) • x = 0) (hρ : ρ x = 0) : x = 0 :=
  eq_zero_of_zsmul_eq_zero_of_coprime hcop hx
    (htriv x hρ (map_eq_zero_of_zsmul_eq_zero deg hh hx))

/-- **The group-theoretic core of exactness at `Pic(C)[h]` in [Stacks, Tag 0CAD].** Let
`ρ : PX ⟶ PC` and `p : PC ⟶ PT` be homomorphisms of abelian groups, `deg : PX ⟶ ℤ^{⊕n}` a
further homomorphism, and suppose

* `hker`: the kernel of `p` is the image under `ρ` of the elements killed by `deg` — this is
  [Stacks, Tag 0CAC];
* `htriv`: an element killed by `ρ` and by `deg` is killed by `d = gcd(mᵢ)` — this is
  [Stacks, Tag 0CAB].

If `h ≠ 0` is prime to `d` then an `h`-torsion element of `PC` dies under `p` exactly when it is
`ρ` of an `h`-torsion element of `PX`. -/
theorem map_eq_zero_iff_of_zsmul_eq_zero (ρ : PX →+ PC) (p : PC →+ PT) (deg : PX →+ (ι → ℤ))
    (hker : ∀ ξ : PC, p ξ = 0 ↔ ∃ x : PX, deg x = 0 ∧ ρ x = ξ)
    (htriv : ∀ x : PX, ρ x = 0 → deg x = 0 → ((Finset.univ.gcd m : ℕ) : ℤ) • x = 0)
    (hh : h ≠ 0) (hcop : Nat.Coprime h (Finset.univ.gcd m))
    {ξ : PC} (hξ : (h : ℤ) • ξ = 0) :
    p ξ = 0 ↔ ∃ x : PX, (h : ℤ) • x = 0 ∧ ρ x = ξ := by
  refine ⟨fun hp => ?_, fun ⟨x, hx, hρ⟩ =>
    (hker ξ).2 ⟨x, map_eq_zero_of_zsmul_eq_zero deg hh hx, hρ⟩⟩
  obtain ⟨x, hdeg, hρ⟩ := (hker ξ).1 hp
  have hdh : ((Finset.univ.gcd m : ℕ) : ℤ) • ((h : ℤ) • x) = 0 :=
    htriv _ (by rw [map_zsmul, hρ, hξ]) (by rw [map_zsmul, hdeg, smul_zero])
  obtain ⟨d', c, hbez⟩ := Nat.isCoprime_iff_coprime.mpr hcop.symm
  refine ⟨(d' * ((Finset.univ.gcd m : ℕ) : ℤ)) • x, ?_, ?_⟩
  · rw [smul_smul, show (h : ℤ) * (d' * ((Finset.univ.gcd m : ℕ) : ℤ)) =
        d' * (((Finset.univ.gcd m : ℕ) : ℤ) * (h : ℤ)) by ring, ← smul_smul, ← smul_smul, hdh,
      smul_zero]
  · rw [map_zsmul, hρ, eq_sub_of_add_eq hbez, sub_smul, one_smul, mul_smul, hξ, smul_zero,
      sub_zero]

/-! #### The two clauses for abstract Picard carriers -/

/-- **Exactness at `PX[h]` for abstract carriers**: injectivity of `PX[h] ⟶ PC[h]` under the
hypotheses of `Stacks.Models.eq_zero_of_zsmul_eq_zero_of_map_eq_zero`. -/
theorem injective_zsmulTorsionRestrict (ρ : PX →+ PC) (deg : PX →+ (ι → ℤ))
    (htriv : ∀ x : PX, ρ x = 0 → deg x = 0 → ((Finset.univ.gcd m : ℕ) : ℤ) • x = 0)
    (hh : h ≠ 0) (hcop : Nat.Coprime h (Finset.univ.gcd m)) :
    Function.Injective (Stacks.Picard.zsmulTorsionRestrict ρ (h : ℤ)) := by
  exact (injective_iff_map_eq_zero _).2 fun x hx => Subtype.ext
    (eq_zero_of_zsmul_eq_zero_of_map_eq_zero m ρ deg htriv hh hcop
      ((Submodule.mem_torsionBy_iff _ _).mp x.2) ((zsmulTorsionRestrict_eq_zero_iff _ _ _).1 hx))

/-- **Exactness at `PC[h]` for abstract carriers**: the kernel of `PC[h] ⟶ PT[h]` is the image
of `PX[h] ⟶ PC[h]`, under the hypotheses of
`Stacks.Models.map_eq_zero_iff_of_zsmul_eq_zero`. -/
theorem exact_zsmulTorsionRestrict (ρ : PX →+ PC) (p : PC →+ PT) (deg : PX →+ (ι → ℤ))
    (hker : ∀ ξ : PC, p ξ = 0 ↔ ∃ x : PX, deg x = 0 ∧ ρ x = ξ)
    (htriv : ∀ x : PX, ρ x = 0 → deg x = 0 → ((Finset.univ.gcd m : ℕ) : ℤ) • x = 0)
    (hh : h ≠ 0) (hcop : Nat.Coprime h (Finset.univ.gcd m)) :
    Function.Exact (Stacks.Picard.zsmulTorsionRestrict ρ (h : ℤ))
      (Stacks.Picard.zsmulTorsionRestrict p (h : ℤ)) := by
  intro ξ
  have hmain := map_eq_zero_iff_of_zsmul_eq_zero m ρ p deg hker htriv hh hcop
    ((Submodule.mem_torsionBy_iff _ _).mp ξ.2)
  constructor
  · intro hp
    obtain ⟨x, hx, hρ⟩ := hmain.1 ((zsmulTorsionRestrict_eq_zero_iff _ _ _).1 hp)
    exact ⟨⟨x, (Submodule.mem_torsionBy_iff _ _).mpr hx⟩, Subtype.ext hρ⟩
  · rintro ⟨x, hx⟩
    exact (zsmulTorsionRestrict_eq_zero_iff _ _ _).2
      (hmain.2 ⟨(x : PX), (Submodule.mem_torsionBy_iff _ _).mp x.2, congrArg Subtype.val hx⟩)

end Abstract

/-! ### The torsion sequence of a regular proper model -/

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **The first map `Pic(X)[h] ⟶ Pic(C)[h]` of the torsion sequence of [Stacks, Tag 0CAD]**: the
restriction to `h`-torsion of the restriction of Picard classes to the generic fibre, which is
the third map of the sequence of [Stacks, Tag 0C63]. -/
def picardTorsionRestriction (h : ℤ) :
    Submodule.torsionBy ℤ (ofScheme S.X) h →ₗ[ℤ] Submodule.torsionBy ℤ (ofScheme S.C) h :=
  Stacks.Picard.zsmulTorsionRestrict (genericFiberPicardRestriction S) h

/-- The map `picardTorsionRestriction` sends an `h`-torsion class to its restriction to the
generic fibre. -/
@[simp]
theorem picardTorsionRestriction_coe (h : ℤ) (x : Submodule.torsionBy ℤ (ofScheme S.X) h) :
    ((S.picardTorsionRestriction h x : ofScheme S.C)) =
      genericFiberPicardRestriction S (x : ofScheme S.X) := rfl

/-- The degrees `(deg(ℒ|_{C₁}), …, deg(ℒ|_{Cₙ}))` of a Picard class on the components of the
special fibre, as one homomorphism `Pic(X) ⟶ ℤ^{⊕n}`. -/
private abbrev componentDegreeVector :
    ofScheme S.X →+ (irreducibleComponents S.specialFiber → ℤ) :=
  AddMonoidHom.pi fun Z => S.specialFiberComponentDegreeHom Z

/-- **[Stacks, Tag 0CAB] in the form the torsion sequence consumes**: a class `x ∈ Pic(X)` which
restricts to `0` in `Pic(C)` and has degree `0` on every component is killed by
`d = gcd(m₁, …, mₙ)`. This is
`Stacks.Models.nonempty_tensorPower_gcd_iso_unit_of_componentDegree_eq_zero` read on Picard
classes: exactness of [Stacks, Tag 0C63] at `Pic(X)` writes `x = Σ aᵢ[𝒪_X(Cᵢ)]`, and the degrees
make `(aᵢ)` a rational multiple of `(mᵢ)`. -/
private theorem gcd_zsmul_eq_zero_of_componentDegreeVector (x : ofScheme S.X)
    (hρ : genericFiberPicardRestriction S x = 0) (hdeg : S.componentDegreeVector x = 0) :
    ((Finset.univ.gcd S.specialFiberMultiplicity : ℕ) : ℤ) • x = 0 := by
  classical
  obtain ⟨a, ha⟩ := (exact_componentPicardHom_genericFiberPicardRestriction S x).1 hρ
  set L := Stacks.Picard.picardRepresentative S.X.toRingedSpace x
  have hLx : Stacks.SheafOfModules.picardClass S.X.presheaf
      (Stacks.RingedSpace.structureIsSheaf S.X.toRingedSpace) L.obj L.property = x :=
    Stacks.Picard.classOf_picardRepresentative S.X.toRingedSpace x
  obtain ⟨q, hq⟩ := exists_eq_mul_specialFiberMultiplicity_of_componentDegree_eq_zero S L.obj
    L.property a (hLx.trans ha.symm) fun Z => by
      rw [← S.specialFiberComponentDegreeHom_picardClass Z L.obj L.property, hLx]
      exact congrFun hdeg Z
  rw [← ha]
  exact gcd_zsmul_componentPicardHom_eq_zero S S.specialFiberComponentIdeal
    S.specialFiberMultiplicity S.specialFiberIdeal_eq_prod a q hq

/-- **Exactness of the torsion sequence of [Stacks, Tag 0CAD] at `Pic(X)[h]`**: for `h ≥ 1`
prime to `d = gcd(m₁, …, mₙ)`, restriction to the generic fibre is injective on `h`-torsion. -/
theorem injective_picardTorsionRestriction {h : ℕ} (hh : 1 ≤ h)
    (hcop : Nat.Coprime h (Finset.univ.gcd S.specialFiberMultiplicity)) :
    Function.Injective (S.picardTorsionRestriction (h : ℤ)) :=
  injective_zsmulTorsionRestrict S.specialFiberMultiplicity (genericFiberPicardRestriction S)
    S.componentDegreeVector S.gcd_zsmul_eq_zero_of_componentDegreeVector
    (Nat.one_le_iff_ne_zero.mp hh) hcop

variable [DecidableEq (irreducibleComponents S.specialFiber)]

/-- **The second map `Pic(C)[h] ⟶ Pic(T)[h]` of the torsion sequence of [Stacks, Tag 0CAD]**,
for `T` the numerical type associated to `X` (through the enumeration `e` of the components):
the restriction to `h`-torsion of the canonical map `Pic(C) ⟶ Pic(T)` of [Stacks, Tag 0CAC]. -/
def picardTorsionToNumericalType (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (h : ℤ) :
    Submodule.torsionBy ℤ (ofScheme S.C) h →ₗ[ℤ]
      Submodule.torsionBy ℤ
        (AlgebraicGeometry.NumericalType.picardGroup (S.associatedNumericalType n e)) h :=
  Stacks.Picard.zsmulTorsionRestrict (S.picardNumericalTypeHom n e) h

/-- The map `picardTorsionToNumericalType` sends an `h`-torsion class `ξ` to its image under
`picardNumericalTypeHom`. -/
@[simp]
theorem picardTorsionToNumericalType_coe (n : ℕ)
    (e : Fin n ≃ irreducibleComponents S.specialFiber) (h : ℤ)
    (ξ : Submodule.torsionBy ℤ (ofScheme S.C) h) :
    ((S.picardTorsionToNumericalType n e h ξ :
        AlgebraicGeometry.NumericalType.picardGroup (S.associatedNumericalType n e))) =
      S.picardNumericalTypeHom n e (ξ : ofScheme S.C) := rfl

/-- **Exactness of the torsion sequence of [Stacks, Tag 0CAD] at `Pic(C)[h]`**: for `h ≥ 1`
prime to `d = gcd(m₁, …, mₙ)`, the kernel of `Pic(C)[h] ⟶ Pic(T)[h]` is the image of
`Pic(X)[h] ⟶ Pic(C)[h]`. -/
theorem exact_picardTorsionRestriction (n : ℕ)
    (e : Fin n ≃ irreducibleComponents S.specialFiber) {h : ℕ} (hh : 1 ≤ h)
    (hcop : Nat.Coprime h (Finset.univ.gcd S.specialFiberMultiplicity)) :
    Function.Exact (S.picardTorsionRestriction (h : ℤ))
      (S.picardTorsionToNumericalType n e (h : ℤ)) :=
  exact_zsmulTorsionRestrict S.specialFiberMultiplicity (genericFiberPicardRestriction S)
    (S.picardNumericalTypeHom n e) S.componentDegreeVector
    (fun ξ => (S.picardNumericalTypeHom_eq_zero_iff' n e ξ).trans <| by
      simp only [funext_iff, Pi.zero_apply]
      rfl)
    S.gcd_zsmul_eq_zero_of_componentDegreeVector (Nat.one_le_iff_ne_zero.mp hh) hcop

/-- **Stacks Project, Tag 0CAD.** In the situation of [Stacks, Tag 0C61] let
`d = gcd(m₁, …, mₙ)` for the multiplicities `mᵢ` of the irreducible components of the special
fibre, let `T` be the numerical type associated to `X` (through an enumeration `e` of the
components), and let `h ≥ 1` be prime to `d`. Then

`0 ⟶ Pic(X)[h] ⟶ Pic(C)[h] ⟶ Pic(T)[h]`

is exact, where the first map is restriction to the generic fibre and the second is the
canonical map of [Stacks, Tag 0CAC]: the first map is injective and the kernel of the second is
the image of the first. -/
@[stacks 0CAD "the exact sequence 0 -> Pic(X)[h] -> Pic(C)[h] -> Pic(T)[h] for h prime to \
d = gcd(m_i), with T the numerical type associated to X"]
theorem picardTorsionSequence_exact (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    {h : ℕ} (hh : 1 ≤ h) (hcop : Nat.Coprime h (Finset.univ.gcd S.specialFiberMultiplicity)) :
    Function.Injective (S.picardTorsionRestriction (h : ℤ)) ∧
      Function.Exact (S.picardTorsionRestriction (h : ℤ))
        (S.picardTorsionToNumericalType n e (h : ℤ)) :=
  ⟨S.injective_picardTorsionRestriction hh hcop, S.exact_picardTorsionRestriction n e hh hcop⟩

end RegularProperModelSituation

end Stacks.Models

end
