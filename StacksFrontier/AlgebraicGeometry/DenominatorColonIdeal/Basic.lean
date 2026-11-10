module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Stalks
public import StacksFrontier.AlgebraicGeometry.DenominatorIdealInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.DenominatorLocalRatio.Basic

/-!
# The denominator ideal of a meromorphic section is a colon ideal on an affine open

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `s` a meromorphic section of `L`.  The
*denominator ideal* of `s` is the subsheaf of `𝒪_X` whose sections over `V` are the `f` with
`f s` a section of `L`; `Stacks.DenominatorIdeal.denominatorIdeal` realises it as a fibre
product and `Stacks.DenominatorIdeal.denominatorIdeal_sections` is that description.

This file identifies the denominator ideal *over an affine open on which the data are
trivialized*.  On an affine open `V` over which `L` is free of rank one on a generator `e` and
over which `s` is the ratio `a / b` of two sections of `𝒪_X` with `b` a nonzerodivisor, a
section `g` of `𝒪_X` over `V` is a denominator of `s` exactly when `g a ∈ b Γ(X, V)` — that is,
the denominator ideal over `V` is the colon ideal `(b Γ(X, V) : a)`.
`Stacks.DenominatorLocalRatio.exists_affineOpen_denominator` supplies such a `V` around every
point.

## Main results

* `Stacks.DenominatorColonIdeal.isUnit_toK₀_app`: a nonzerodivisor on an affine open becomes a
  unit in the sheaf of total quotient rings.
* `Stacks.DenominatorColonIdeal.injective_smul_kAsOModule`: consequently it acts injectively on
  the sections of the sheaf of meromorphic sections there.
* `Stacks.DenominatorColonIdeal.injective_toK_app`: the canonical map `L ⟶ K_X(L)` is injective
  on sections over every open set, for an invertible `L`.
* `Stacks.DenominatorColonIdeal.exists_denominator_iff_mul_eq`: **the affine-local
  presentation**, stated for a rank-one generator, and
  `exists_denominator_iff_mul_eq_of_trivialization` the same for a trivialization.
* `Stacks.DenominatorColonIdeal.range_denominatorIdealι_app_eq`: the same as an equality of the
  image of the ideal inclusion on sections with the colon ideal, written out as a set.
* `Stacks.DenominatorColonIdeal.exists_affineOpen_colon_presentation`: around every point of
  every open set there is an affine open carrying that presentation.

## Implementation notes

Both directions of the presentation need the nonzerodivisor `b` to be *cancellable* on the
sections of `K_X(L)` over `V`, and that is where affineness enters: on an affine open the
denominator submonoid of the total quotient presheaf is the whole of `nonZeroDivisors Γ(X, V)`
by `AlgebraicGeometry.submonoidPresheafOfStalk_obj_eq_nonZeroDivisors`, so `b` is a unit already
in the sections of that presheaf — by
`AlgebraicGeometry.isLocalization_totalQuotientPresheaf_obj_of_isAffineOpen`, which carries no
Noetherian hypothesis — and the sheafification map carries that unit forward.

Three spellings of one ring are in play and instance search distinguishes them.  The module
structures on the sections of a sheaf of `𝒪_X`-modules are stated at
`Stacks.DenominatorLocalRatio.oScalar`, the `RingCat` spelling, so all scalars here are typed at
that; the sections of `K_X(L)` are a module over `Stacks.DenominatorLocalRatio.kScalar` and the
action of `𝒪_X` on them is *definitionally* the action of the image in `K_X`; and
`Stacks.SheafDescent.Trivialization` states its isomorphism over
`Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.presheaf`, for which neither
`SMul` nor `HMul` against an `oScalar` is synthesizable.  `Stacks.DenominatorColonIdeal.oTriv`
retypes that isomorphism into the `oScalar` spelling — the two `Module` instances are
definitionally equal — after which `map_smul` and `smul_eq_mul` apply normally.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.DenominatorIdeal Stacks.DenominatorIdealResidue Stacks.DenominatorLocalRatio

universe u

namespace Stacks.DenominatorColonIdeal

/-- Multiplication by a unit is injective on any module. -/
lemma injective_smul_of_isUnit {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {c : R}
    (hc : IsUnit c) : Function.Injective fun x : M => c • x :=
  fun _ _ h => hc.smul_left_cancel.1 h

variable (X : Scheme.{u})

/-- Multiplication on the sections of the structure sheaf is commutative, in the `RingCat`
spelling at which the module structures on sheaves of `𝒪_X`-modules are stated. -/
lemma oScalar_mul_comm (V : Opens X) (x y : oScalar X V) : x * y = y * x :=
  mul_comm (G := (Γ(X, V) : Type u)) x y

/-- **A nonzerodivisor on an affine open becomes a unit in the sheaf of total quotient
rings.** -/
lemma isUnit_toK₀_app {U : Opens X} (hU : IsAffineOpen U) {b : Γ(X, U)}
    (hb : b ∈ nonZeroDivisors Γ(X, U)) :
    IsUnit (((toK₀ X).app (op U)).hom b) := by
  let : Algebra Γ(X, U) ((X.presheaf.totalQuotientPresheaf).obj (op U)) :=
    (X.presheaf.toTotalQuotientPresheaf.app (op U)).hom.toAlgebra
  have hloc : IsLocalization (nonZeroDivisors Γ(X, U))
      ((X.presheaf.totalQuotientPresheaf).obj (op U)) :=
    AlgebraicGeometry.isLocalization_totalQuotientPresheaf_obj_of_isAffineOpen X U hU
  have h1 : IsUnit (algebraMap Γ(X, U) ((X.presheaf.totalQuotientPresheaf).obj (op U)) b) :=
    IsLocalization.map_units _ (⟨b, hb⟩ : nonZeroDivisors Γ(X, U))
  rw [RingHom.algebraMap_toAlgebra] at h1
  exact h1.map ((toSheafify (Opens.grothendieckTopology X)
    X.presheaf.totalQuotientPresheaf).app (op U)).hom

variable (L : SheafOfModules.{u} (O X))

/-- **The canonical map from an invertible sheaf to its sheaf of meromorphic sections is
injective on the sections over every open set.** -/
lemma injective_toK_app
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L)
    (U : (Opens X)ᵒᵖ) : Function.Injective ((toK X L).val.app U) := by
  have hq : Mono (toK X L) := Stacks.DenominatorIdealInvertible.mono_toK X L hL
  have happ : Mono (((SheafOfModules.forget (O X) ⋙
      PresheafOfModules.toPresheaf (O X).obj).map (toK X L)).app U) := inferInstance
  exact fun _ _ hab => (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp happ hab

/-- **A nonzerodivisor on an affine open acts injectively on the sections of the sheaf of
meromorphic sections there.** -/
lemma injective_smul_kAsOModule {U : Opens X} (hU : IsAffineOpen U) (b : oScalar X U)
    (hb : b ∈ nonZeroDivisors Γ(X, U)) :
    Function.Injective fun y : ((kAsOModule X L).val.obj (op U) : Type u) => b • y := by
  obtain ⟨c, hc⟩ : ∃ c : kScalar X U, ((toK₀ X).app (op U)).hom b = c := ⟨_, rfl⟩
  have hcu : IsUnit c := by rw [← hc]; exact isUnit_toK₀_app X hU hb
  have hbridge : ∀ y : ((kAsOModule X L).val.obj (op U) : Type u),
      b • y = @HSMul.hSMul (kScalar X U) ((K X L).val.obj (op U) : Type u) _ _ c y := fun y => by
    rw [← hc]; rfl
  intro y z h
  have h' : @HSMul.hSMul (kScalar X U) ((K X L).val.obj (op U) : Type u) _ _ c y =
      @HSMul.hSMul (kScalar X U) ((K X L).val.obj (op U) : Type u) _ _ c z := by
    rwa [← hbridge y, ← hbridge z]
  exact injective_smul_of_isUnit (M := ((K X L).val.obj (op U) : Type u)) hcu h'

/-! ### A trivialization, retyped

`Stacks.SheafDescent.Trivialization` states its isomorphism over the
`Stacks.SheafOfModules.TensorSheafification` spelling of the ring of sections, against which no
scalar action can be written by hand; here it is retyped into the spelling instance search
uses. -/

/-- The isomorphism of a trivialization over the open set itself, read in the `RingCat` spelling
at which the module structures on the sections of a sheaf of `𝒪_X`-modules are stated. -/
def oTriv {V : Opens X} (θ : Stacks.SheafDescent.Trivialization X.presheaf L.val V) :
    (L.val.obj (op V) : Type u) ≃ₗ[oScalar X V] oScalar X V :=
  θ.θ V (𝟙 V)

/-- The generator of the sections of `L` over an open set determined by a trivialization. -/
def oTrivBasis {V : Opens X} (θ : Stacks.SheafDescent.Trivialization X.presheaf L.val V) :
    (L.val.obj (op V) : Type u) :=
  (oTriv X L θ).symm 1

/-- Every section of `L` over a trivializing open set is a multiple of the generator. -/
lemma exists_smul_oTrivBasis {V : Opens X}
    (θ : Stacks.SheafDescent.Trivialization X.presheaf L.val V)
    (y : (L.val.obj (op V) : Type u)) : ∃ u : oScalar X V, y = u • oTrivBasis X L θ := by
  refine ⟨oTriv X L θ y, (oTriv X L θ).injective ?_⟩
  simp only [oTrivBasis, map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

/-- The generator of a trivialization is a basis: distinct multiples of it are distinct. -/
lemma injective_smul_oTrivBasis {V : Opens X}
    (θ : Stacks.SheafDescent.Trivialization X.presheaf L.val V) :
    Function.Injective fun u : oScalar X V => u • oTrivBasis X L θ := by
  intro p q hpq
  simpa only [oTrivBasis, map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one] using
    congrArg (oTriv X L θ) hpq

variable (s : MeromorphicSection.{u, u} X.sheaf L)

/-- The canonical map to the sheaf of meromorphic sections is linear on sections. -/
lemma toK_app_smul (V : Opens X) (c : oScalar X V) (y : (L.val.obj (op V) : Type u)) :
    (toK X L).val.app (op V) (c • y) = c • (toK X L).val.app (op V) y :=
  map_smul _ c y

/-- Multiplication by a section of the structure sheaf on the meromorphic section is symmetric in
the two factors: `g · (b · s) = b · (g · s)`. -/
lemma smul_sectionMap_app_comm (V : Opens X) (g b : oScalar X V) :
    g • (sectionMap X L s).val.app (op V) b = b • (sectionMap X L s).val.app (op V) g := by
  have h1 : (sectionMap X L s).val.app (op V) (g • b) =
      g • (sectionMap X L s).val.app (op V) b := map_smul _ g b
  have h2 : (sectionMap X L s).val.app (op V) (b • g) =
      b • (sectionMap X L s).val.app (op V) g := map_smul _ b g
  rw [← h1, ← h2]
  congr 1
  change g * b = b * g
  exact oScalar_mul_comm X V g b

/-! ### The affine-local presentation -/

/-- **The affine-local presentation of the denominator ideal.**  On an affine open `V` over which
the invertible sheaf `L` is free of rank one on a generator `e`, and over which the meromorphic
section `s` is the ratio `a / b` of two sections of the structure sheaf with `b` a
nonzerodivisor, a section `g` of `𝒪_X` over `V` is a denominator of `s` exactly when `g a` is a
multiple of `b`.  In other words, the denominator ideal over `V` is the colon ideal
`(b Γ(X, V) : a)`. -/
theorem exists_denominator_iff_mul_eq
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L)
    {V : Opens X} (hV : IsAffineOpen V) {e : (L.val.obj (op V) : Type u)}
    (hsurj : ∀ y : (L.val.obj (op V) : Type u), ∃ u : oScalar X V, y = u • e)
    (hinj : Function.Injective fun u : oScalar X V => u • e)
    {b : oScalar X V} (hb : b ∈ nonZeroDivisors Γ(X, V)) {a : oScalar X V}
    (hbt : (toK X L).val.app (op V) (a • e) = (sectionMap X L s).val.app (op V) b)
    (g : oScalar X V) :
    (∃ d : (denominatorIdeal X L s).val.obj (op V),
        (denominatorIdealι X L s).val.app (op V) d = g) ↔
      ∃ u : oScalar X V, g * a = b * u := by
  have hbinj := injective_smul_kAsOModule X L hV b hb
  have key : b • (sectionMap X L s).val.app (op V) g =
      (toK X L).val.app (op V) (g • a • e) :=
    calc b • (sectionMap X L s).val.app (op V) g
        = g • (sectionMap X L s).val.app (op V) b := smul_sectionMap_app_comm X L s V b g
      _ = g • (toK X L).val.app (op V) (a • e) := by rw [hbt]
      _ = (toK X L).val.app (op V) (g • a • e) := (toK_app_smul X L V g (a • e)).symm
  rw [denominatorIdeal_sections X L s V g]
  constructor
  · rintro ⟨t', ht'⟩
    obtain ⟨u, rfl⟩ := hsurj t'
    have hkey : b • u • e = g • a • e :=
      injective_toK_app X L hL (op V) (by rw [← key, toK_app_smul, ht'])
    rw [smul_smul, smul_smul] at hkey
    exact ⟨u, (hinj hkey).symm⟩
  · rintro ⟨u, hu⟩
    refine ⟨u • e, ?_⟩
    have hkey : b • u • e = g • a • e := by rw [smul_smul, smul_smul, hu]
    refine hbinj ?_
    change @HSMul.hSMul (oScalar X V) _ _ _ b
        ((sectionMap X L s).val.app (op V) g) =
      @HSMul.hSMul (oScalar X V) _ _ _ b ((toK X L).val.app (op V) (u • e))
    rw [key, ← hkey, toK_app_smul]

/-- **The affine-local presentation, with the rank-one hypothesis supplied by a
trivialization.** -/
theorem exists_denominator_iff_mul_eq_of_trivialization
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L)
    {V : Opens X} (hV : IsAffineOpen V)
    (θ : Stacks.SheafDescent.Trivialization X.presheaf L.val V)
    {b : oScalar X V} (hb : b ∈ nonZeroDivisors Γ(X, V)) {a : oScalar X V}
    (hbt : (toK X L).val.app (op V) (a • oTrivBasis X L θ) =
      (sectionMap X L s).val.app (op V) b)
    (g : oScalar X V) :
    (∃ d : (denominatorIdeal X L s).val.obj (op V),
        (denominatorIdealι X L s).val.app (op V) d = g) ↔
      ∃ u : oScalar X V, g * a = b * u :=
  exists_denominator_iff_mul_eq X L s hL hV (exists_smul_oTrivBasis X L θ)
    (injective_smul_oTrivBasis X L θ) hb hbt g

/-- **The affine-local presentation as an equality of the sections of the denominator ideal with
the colon ideal `(b Γ(X, V) : a)`**, the latter written out as a set. -/
theorem range_denominatorIdealι_app_eq
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L)
    {V : Opens X} (hV : IsAffineOpen V)
    (θ : Stacks.SheafDescent.Trivialization X.presheaf L.val V)
    {b : oScalar X V} (hb : b ∈ nonZeroDivisors Γ(X, V)) {a : oScalar X V}
    (hbt : (toK X L).val.app (op V) (a • oTrivBasis X L θ) =
      (sectionMap X L s).val.app (op V) b) :
    Set.range (ConcreteCategory.hom ((denominatorIdealι X L s).val.app (op V))) =
      {g : oScalar X V | ∃ u : oScalar X V, g * a = b * u} :=
  Set.ext fun g =>
    exists_denominator_iff_mul_eq_of_trivialization X L s hL hV θ hb hbt g

/-- **Around every point of every open set there is an affine open carrying the colon-ideal
presentation of the denominator ideal.** -/
theorem exists_affineOpen_colon_presentation
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L)
    (W : Opens X) (x : X) (hx : x ∈ W) :
    ∃ V : Opens X, V ≤ W ∧ x ∈ V ∧ IsAffineOpen V ∧
      ∃ b : oScalar X V, b ∈ nonZeroDivisors Γ(X, V) ∧ ∃ a : oScalar X V,
        Set.range (ConcreteCategory.hom ((denominatorIdealι X L s).val.app (op V))) =
          {g : oScalar X V | ∃ u : oScalar X V, g * a = b * u} := by
  obtain ⟨V, hVW, hxV, hVaff, ⟨θ⟩, b, hb, t, hbt⟩ :=
    Stacks.DenominatorLocalRatio.exists_affineOpen_denominator X L s hL W x hx
  obtain ⟨a, hat⟩ := exists_smul_oTrivBasis X L θ t
  rw [hat] at hbt
  exact ⟨V, hVW, hxV, hVaff, b, hb, a,
    range_denominatorIdealι_app_eq X L s hL hVaff θ hb hbt⟩

end Stacks.DenominatorColonIdeal

end
