module

public import StacksFrontier.AlgebraicGeometry.DenominatorIdealQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.DenominatorLocalRatio.MulCokernel
public import StacksFrontier.AlgebraicGeometry.Modules.InvertibleStalkFree

/-!
# Multiplication by a meromorphic section on its denominator ideal, on sections

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `s` a meromorphic section of `L`. The
denominator ideal `I ⊆ 𝒪_X` of `s` carries two projections: the inclusion
`Stacks.DenominatorIdeal.denominatorIdealι` in the structure sheaf, and multiplication by the
section, `Stacks.DenominatorIdeal.denominatorIdealMul : I ⟶ L`. For the first,
`Stacks.DenominatorColonIdeal.range_denominatorIdealι_app_eq` writes its image on sections over
a trivialized affine open as the colon ideal `{g | g a ∈ b 𝒪}`; this file gives the same
presentation for the second.

Over an affine open `V` on which `L` is trivialized by a basis element `e` and on which `s` is
the ratio `a / b` of two sections of `𝒪_X` with `b` a nonzerodivisor, a section `t` of `L` over
`V` is in the image of multiplication by `s` exactly when `t = y e` for a `y` with
`y b ∈ a 𝒪_X(V)`. So the image of the second projection on sections is

  `{y e | y b ∈ a Γ(X, V)}`,

the *fractional* colon ideal `(a) : (b)` times the basis element, where the first projection gives
the colon ideal `(b) : (a)`.

## Main definitions

* `Stacks.DenominatorMul.trivBasis` — the basis element of a trivialization, at the declared type
  `Γ(L, V)` carrying the scalar action of `Γ(X, V)`.

## Main results

* `Stacks.DenominatorMul.eq_oTriv_smul_oTrivBasis` — every section is its own coordinate times
  the basis element.
* `Stacks.DenominatorMul.exists_denominatorIdealMul_app_eq_smul_iff` — **the affine-local
  presentation**: `y e` is a value of multiplication by `s` exactly when `y b` is a multiple of
  `a`.
* `Stacks.DenominatorMul.range_denominatorIdealMul_app_eq` — the same as an equality of the image
  of the second projection on sections with the image of that set of scalars under `y ↦ y e`.
* `Stacks.DenominatorMul.range_denominatorIdealMul_app_basicOpen` — that presentation restricted
  to a basic open of `V`.
* `Stacks.DenominatorMul.isStalkBasis_germ_trivBasis` — the germ of the basis element of a
  trivialization is a stalk basis in the sense of `Stacks.Divisors.IsStalkBasis`.
* `Stacks.DenominatorMul.exists_affineOpen_denominator_presentations` — around every point of a
  scheme with `L` invertible there is an affine open carrying a ratio `a / b` with `b` a
  nonzerodivisor and a basis element whose germ is a stalk basis, for which **both**
  presentations hold on every basic open.
* `Stacks.DenominatorMul.exists_affineOpen_denominator_presentations_of_isRegular` — the same with
  the numerator a nonzerodivisor as well, for a regular meromorphic section.

## Implementation notes

Three spellings of one ring of scalars are in play and instance search crosses none of them. The
sections of `L` over `V` are a module over `Stacks.DenominatorLocalRatio.oScalar`, the `RingCat`
spelling, at which the trivialization and the ratio equation are stated; the *multiplications*
`y * b` in the colon ideal need a `CommRing`, which is synthesizable only at `Γ(X, V)`; and
`Γ(L, V)` is the spelling at which Mathlib registers the action of `Γ(X, V)` on the sections of
an `𝒪_X`-module. So the two-sided criterion is stated entirely at `oScalar`, and the range
statements at `Γ(X, V)` and `Γ(L, V)`, where the colon ideal can be written;
`Stacks.DenominatorMul.trivBasis` is the ascription of the basis element that makes the second
spelling available.

The names `denominatorIdeal`, `denominatorIdealι` and `denominatorIdealMul` are ambiguous between
`Stacks.DenominatorIdeal` and `AlgebraicGeometry`, so the latter are hidden when opening
`AlgebraicGeometry`.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry hiding denominatorIdeal denominatorIdealι denominatorIdealMul
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.DenominatorIdeal Stacks.DenominatorColonIdeal Stacks.DenominatorLocalRatio
open Stacks.DenominatorIdealQcoh (oTrivBasis_comp toK_app_restrict)

universe u

namespace Stacks.DenominatorMul

variable (X : Scheme.{u}) (L : X.Modules)
  (s : AlgebraicGeometry.MeromorphicSection.{u, u} X.sheaf L)

/-- The basis element `Stacks.DenominatorColonIdeal.oTrivBasis` of a trivialization, at the
declared type `Γ(L, V)`. -/
abbrev trivBasis {V : Opens X} (θ : Stacks.SheafDescent.Trivialization X.presheaf L.val V) :
    Γ(L, V) :=
  oTrivBasis X L θ

/-- **Every section of `L` over a trivializing open set is its own coordinate times the basis
element.** -/
lemma eq_oTriv_smul_oTrivBasis {V : Opens X}
    (θ : Stacks.SheafDescent.Trivialization X.presheaf L.val V)
    (y : (L.val.obj (op V) : Type u)) : y = oTriv X L θ y • oTrivBasis X L θ := by
  refine (oTriv X L θ).injective ?_
  simp only [oTrivBasis, map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

/-- The basis element of a restricted trivialization is the restriction of the basis element,
read at the `Γ(L, V)` spelling. -/
lemma map_trivBasis {V W : Opens X} (h : W ≤ V)
    (θ : Stacks.SheafDescent.Trivialization X.presheaf L.val V) :
    L.presheaf.map (homOfLE h).op (trivBasis X L θ) = trivBasis X L (θ.comp (homOfLE h)) :=
  (oTrivBasis_comp X L θ (homOfLE h)).symm

/-- **The affine-local presentation of multiplication by the section.** On an affine open `V`
over which the invertible sheaf `L` is trivialized with basis element `e`, and over which the
meromorphic section `s` is the ratio `a / b` of two sections of the structure sheaf with `b` a
nonzerodivisor, the multiple `y e` of the basis element is a value of multiplication by `s` on the
denominator ideal exactly when `y b` is a multiple of `a`. -/
theorem exists_denominatorIdealMul_app_eq_smul_iff
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L)
    {V : Opens X} (hV : IsAffineOpen V)
    (θ : Stacks.SheafDescent.Trivialization X.presheaf L.val V)
    {b : oScalar X V} (hb : b ∈ nonZeroDivisors Γ(X, V)) {a : oScalar X V}
    (hbt : (toK X L).val.app (op V) (a • oTrivBasis X L θ) =
      (sectionMap X L s).val.app (op V) b)
    (y : oScalar X V) :
    (∃ d : (denominatorIdeal X L s).val.obj (op V),
        (denominatorIdealMul X L s).val.app (op V) d = y • oTrivBasis X L θ) ↔
      ∃ u : oScalar X V, y * b = a * u := by
  have hc : ∀ g : oScalar X V, b • (sectionMap X L s).val.app (op V) g =
      (toK X L).val.app (op V) (g • a • oTrivBasis X L θ) := fun g =>
    (smul_sectionMap_app_comm X L s V b g).trans <| by
      rw [hbt.symm, toK_app_smul X L V g (a • oTrivBasis X L θ)]
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨g, hg⟩ : ∃ g : oScalar X V,
        (denominatorIdealι X L s).val.app (op V) d = g := ⟨_, rfl⟩
    have hsk : (sectionMap X L s).val.app (op V) g =
        (toK X L).val.app (op V) (y • oTrivBasis X L θ) := by
      rw [← hd, ← hg]; exact app_condition X L s V d
    have hkey : b • y • oTrivBasis X L θ = g • a • oTrivBasis X L θ := by
      refine injective_toK_app X L hL (op V) ?_
      rw [toK_app_smul X L V b, ← hsk, hc]
    rw [smul_smul, smul_smul] at hkey
    have hby := injective_smul_oTrivBasis X L θ hkey
    exact ⟨g, (oScalar_mul_comm X V y b).trans (hby.trans (oScalar_mul_comm X V g a))⟩
  · rintro ⟨u, hu⟩
    have hgu : b * y = u * a :=
      (oScalar_mul_comm X V b y).trans (hu.trans (oScalar_mul_comm X V a u))
    have hsk : (sectionMap X L s).val.app (op V) u =
        (toK X L).val.app (op V) (y • oTrivBasis X L θ) := by
      refine injective_smul_kAsOModule X L hV b hb ?_
      change @HSMul.hSMul (oScalar X V) _ _ _ b ((sectionMap X L s).val.app (op V) u) =
        @HSMul.hSMul (oScalar X V) _ _ _ b
          ((toK X L).val.app (op V) (y • oTrivBasis X L θ))
      rw [hc, ← toK_app_smul X L V b, smul_smul, smul_smul, hgu]
    obtain ⟨d, hd⟩ :=
      (denominatorIdeal_sections X L s V u).mpr ⟨y • oTrivBasis X L θ, hsk⟩
    refine ⟨d, injective_toK_app X L hL (op V) ?_⟩
    rwa [← app_condition X L s V d, hd]

/-- **The image of multiplication by the section on sections over a trivialized affine open is the
fractional colon ideal `(a) : (b)` times the basis element.** -/
theorem range_denominatorIdealMul_app_eq
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L)
    {V : Opens X} (hV : IsAffineOpen V)
    (θ : Stacks.SheafDescent.Trivialization X.presheaf L.val V)
    {b : Γ(X, V)} (hb : b ∈ nonZeroDivisors Γ(X, V)) {a : Γ(X, V)}
    (hbt : (toK X L).val.app (op V) (a • trivBasis X L θ) =
      (sectionMap X L s).val.app (op V) b) :
    Set.range (ConcreteCategory.hom ((denominatorIdealMul X L s).val.app (op V))) =
      (fun y : Γ(X, V) => y • trivBasis X L θ) ''
        {y : Γ(X, V) | ∃ u : Γ(X, V), y * b = a * u} := by
  ext t
  constructor
  · rintro ⟨d, rfl⟩
    obtain ⟨y, hy⟩ :=
      exists_smul_oTrivBasis X L θ ((denominatorIdealMul X L s).val.app (op V) d)
    exact ⟨y, (exists_denominatorIdealMul_app_eq_smul_iff X L s hL hV θ hb hbt y).mp ⟨d, hy⟩,
      hy.symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact (exists_denominatorIdealMul_app_eq_smul_iff X L s hL hV θ hb hbt y).mpr hy

/-- **The presentation of multiplication by the section restricts to a basic open.** The image
of multiplication by `s` on sections over `X.basicOpen f` is the fractional colon ideal of the
restricted numerator and denominator times the restricted basis element. -/
theorem range_denominatorIdealMul_app_basicOpen
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L)
    {V : Opens X} (hV : IsAffineOpen V)
    (θ : Stacks.SheafDescent.Trivialization X.presheaf L.val V)
    {b : Γ(X, V)} (hb : b ∈ nonZeroDivisors Γ(X, V)) {a : Γ(X, V)}
    (hbt : (toK X L).val.app (op V) (a • trivBasis X L θ) =
      (sectionMap X L s).val.app (op V) b) (f : Γ(X, V)) :
    Set.range (ConcreteCategory.hom
        ((denominatorIdealMul X L s).val.app (op (X.basicOpen f)))) =
      (fun y : Γ(X, X.basicOpen f) =>
          y • L.presheaf.map (homOfLE (X.basicOpen_le f)).op (trivBasis X L θ)) ''
        {y : Γ(X, X.basicOpen f) | ∃ u : Γ(X, X.basicOpen f),
          y * algebraMap Γ(X, V) Γ(X, X.basicOpen f) b =
            algebraMap Γ(X, V) Γ(X, X.basicOpen f) a * u} := by
  let := hV.isLocalization_basicOpen f
  have hb' : (O X).obj.map (homOfLE (X.basicOpen_le f)).op b ∈
      nonZeroDivisors Γ(X, X.basicOpen f) :=
    IsLocalization.nonZeroDivisors_le_comap (M := Submonoid.powers f)
      (S := Γ(X, X.basicOpen f)) hb
  have h := range_denominatorIdealMul_app_eq X L s hL (hV.basicOpen f)
    (θ.comp (homOfLE (X.basicOpen_le f))) hb'
    (toK_app_restrict X L s (homOfLE (X.basicOpen_le f)) θ hbt)
  rwa [← map_trivBasis X L (X.basicOpen_le f) θ] at h

/-- **The germ of the basis element of a trivialization is a stalk basis.** -/
theorem isStalkBasis_germ_trivBasis {V : Opens X}
    (θ : Stacks.SheafDescent.Trivialization X.presheaf L.val V) (x : X) (hx : x ∈ V) :
    Stacks.Divisors.IsStalkBasis L x (L.presheaf.germ V x hx (trivBasis X L θ)) := by
  refine Stacks.Divisors.isStalkBasis_germ_of_bijective_smul (trivBasis X L θ) ?_ x hx
  intro W hW
  rw [map_trivBasis X L hW θ]
  exact ⟨injective_smul_oTrivBasis X L (θ.comp (homOfLE hW)),
    fun z => (exists_smul_oTrivBasis X L (θ.comp (homOfLE hW)) z).imp fun _ h => h.symm⟩

/-- **Around every point of a scheme there is an affine open carrying both affine-local
presentations of the denominator ideal of [Stacks, Tag 02P0], on every basic open of it, together
with a basis element whose germ is a stalk basis.** The two presentations are those of the two
projections of the denominator ideal: the colon ideal `(b) : (a)` for the inclusion in the
structure sheaf, and the fractional colon ideal `(a) : (b)` times the basis element for
multiplication by the section, both for one and the same ratio `a / b` whose denominator `b` is
a nonzerodivisor. -/
theorem exists_affineOpen_denominator_presentations
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L) (x : X) :
    ∃ (V : Opens X) (hxV : x ∈ V), IsAffineOpen V ∧
      ∃ (a b : Γ(X, V)) (e : Γ(L, V)),
        b ∈ nonZeroDivisors Γ(X, V) ∧
        Stacks.Divisors.IsStalkBasis L x (L.presheaf.germ V x hxV e) ∧
        (∀ f : Γ(X, V),
          Set.range (ConcreteCategory.hom
              ((denominatorIdealι X L s).val.app (op (X.basicOpen f)))) =
            {g : Γ(X, X.basicOpen f) | ∃ v : Γ(X, X.basicOpen f),
              g * algebraMap Γ(X, V) Γ(X, X.basicOpen f) a =
                algebraMap Γ(X, V) Γ(X, X.basicOpen f) b * v}) ∧
        ∀ f : Γ(X, V),
          Set.range (ConcreteCategory.hom
              ((denominatorIdealMul X L s).val.app (op (X.basicOpen f)))) =
            (fun y : Γ(X, X.basicOpen f) =>
                y • L.presheaf.map (homOfLE (X.basicOpen_le f)).op e) ''
              {y : Γ(X, X.basicOpen f) | ∃ u : Γ(X, X.basicOpen f),
                y * algebraMap Γ(X, V) Γ(X, X.basicOpen f) b =
                  algebraMap Γ(X, V) Γ(X, X.basicOpen f) a * u} := by
  obtain ⟨V, -, hxV, hVaff, ⟨θ⟩, b, hb, t, hbt⟩ :=
    Stacks.DenominatorLocalRatio.exists_affineOpen_denominator X L s hL ⊤ x (Opens.mem_top x)
  obtain ⟨a, hat⟩ := exists_smul_oTrivBasis X L θ t
  rw [hat] at hbt
  exact ⟨V, hxV, hVaff, a, b, trivBasis X L θ, hb,
    isStalkBasis_germ_trivBasis X L θ x hxV,
    fun f => Stacks.DenominatorIdealQcoh.range_denominatorIdealι_app_basicOpen
      X L s hL hVaff θ hb hbt f,
    fun f => range_denominatorIdealMul_app_basicOpen X L s hL hVaff θ hb hbt f⟩

/-- **Around every point of a scheme there is an affine open carrying both affine-local
presentations of the denominator ideal of [Stacks, Tag 02P0] for a ratio whose numerator *and*
denominator are nonzerodivisors**, for a regular meromorphic section `s`. -/
theorem exists_affineOpen_denominator_presentations_of_isRegular
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) (x : X) :
    ∃ (V : Opens X) (hxV : x ∈ V), IsAffineOpen V ∧
      ∃ (a b : Γ(X, V)) (e : Γ(L, V)),
        a ∈ nonZeroDivisors Γ(X, V) ∧ b ∈ nonZeroDivisors Γ(X, V) ∧
        Stacks.Divisors.IsStalkBasis L x (L.presheaf.germ V x hxV e) ∧
        (∀ f : Γ(X, V),
          Set.range (ConcreteCategory.hom
              ((denominatorIdealι X L s).val.app (op (X.basicOpen f)))) =
            {g : Γ(X, X.basicOpen f) | ∃ v : Γ(X, X.basicOpen f),
              g * algebraMap Γ(X, V) Γ(X, X.basicOpen f) a =
                algebraMap Γ(X, V) Γ(X, X.basicOpen f) b * v}) ∧
        ∀ f : Γ(X, V),
          Set.range (ConcreteCategory.hom
              ((denominatorIdealMul X L s).val.app (op (X.basicOpen f)))) =
            (fun y : Γ(X, X.basicOpen f) =>
                y • L.presheaf.map (homOfLE (X.basicOpen_le f)).op e) ''
              {y : Γ(X, X.basicOpen f) | ∃ u : Γ(X, X.basicOpen f),
                y * algebraMap Γ(X, V) Γ(X, X.basicOpen f) b =
                  algebraMap Γ(X, V) Γ(X, X.basicOpen f) a * u} := by
  obtain ⟨V, -, hxV, hVaff, ⟨θ⟩, b, hb, t, hbt⟩ :=
    Stacks.DenominatorLocalRatio.exists_affineOpen_denominator X L s hL ⊤ x (Opens.mem_top x)
  obtain ⟨a, ha0⟩ : ∃ a : Γ(X, V), oTriv X L θ t = a := ⟨_, rfl⟩
  have ha : a ∈ nonZeroDivisors Γ(X, V) :=
    Stacks.DenominatorCokernel.mem_nonZeroDivisors_of_trivialization X L s hs
      (oTriv X L θ) b hb t hbt a ha0
  have hta : t = a • trivBasis X L θ := ha0 ▸ eq_oTriv_smul_oTrivBasis X L θ t
  have hbt' : (toK X L).val.app (op V) (a • trivBasis X L θ) =
      (sectionMap X L s).val.app (op V) b :=
    (congrArg (fun y : (L.val.obj (op V) : Type u) => (toK X L).val.app (op V) y) hta).symm.trans
      hbt
  exact ⟨V, hxV, hVaff, a, b, trivBasis X L θ, ha, hb,
    isStalkBasis_germ_trivBasis X L θ x hxV,
    fun f => Stacks.DenominatorIdealQcoh.range_denominatorIdealι_app_basicOpen
      X L s hL hVaff θ hb hbt' f,
    fun f => range_denominatorIdealMul_app_basicOpen X L s hL hVaff θ hb hbt' f⟩

end Stacks.DenominatorMul

end
