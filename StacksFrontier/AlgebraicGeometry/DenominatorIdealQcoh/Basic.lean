module

public import StacksFrontier.AlgebraicGeometry.DenominatorColonIdeal.Basic
public import StacksFrontier.AlgebraicGeometry.DenominatorIdealQcoh.ColonLocalization
public import StacksFrontier.AlgebraicGeometry.DenominatorIdealQcoh.Cover
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The denominator ideal of a meromorphic section is quasi-coherent

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `s` a meromorphic section of `L`.  The
denominator ideal of `s` is `Stacks.DenominatorIdeal.denominatorIdeal`, the subsheaf of `𝒪_X`
whose sections over `V` are the `f` with `f s` a section of `L`.  This file proves that it is
quasi-coherent, which is the assertion of Stacks Tag 02P0 that its proof actually establishes by
a computation: around every point there is an affine open on which the denominator ideal is a
colon ideal `(b Γ(X, V) : a)`, and the colon ideal commutes with localization.

Two inputs make that into quasi-coherence.
`Stacks.DenominatorColonIdeal.range_denominatorIdealι_app_eq` is the colon-ideal presentation on
a trivialized affine open, and `Stacks.ColonLocalization.isLocalizedModule_of_range_eq_colon` is
the purely algebraic statement that two such presentations, on an affine open and on one of its
basic opens, exhibit the smaller sections as a localization of the bigger ones.

## Main results

* `Stacks.DenominatorIdealQcoh.isLocalizedModule_restrictₗ_of_range_eq_colon`: a submodule of the
  structure sheaf presented by colon ideals on an affine open and on one of its basic opens is
  localized there.
* `Stacks.DenominatorIdealQcoh.range_denominatorIdealι_app_basicOpen`: the colon-ideal
  presentation of the denominator ideal restricts to a basic open.
* `Stacks.DenominatorIdealQcoh.isQuasicoherent_of_colon_presentations`: a submodule of the
  structure sheaf which is a colon ideal on an affine neighbourhood of every point, and on every
  basic open of that neighbourhood, is quasi-coherent.
* `Stacks.DenominatorIdealQcoh.denominatorIdeal_isQuasicoherent`: **the denominator ideal of a
  meromorphic section of an invertible sheaf is quasi-coherent.**  No Noetherian hypothesis.

## Implementation notes

The sections of the denominator ideal carry three relevant module structures over three spellings
of `Γ(X, V)` and instance search crosses none of them, so each statement is written at one spelling
and the conversions are made by named lemmas.  `inclₗ` and `inclBasicOpenₗ` retype the inclusion in
the structure sheaf as `Γ(X, V)`-linear maps, the form in which the algebraic criterion is stated;
the colon-ideal presentations are stated at the `Stacks.DenominatorLocalRatio.oScalar` spelling, at
which `•` is synthesizable but `CommRing` is not.  In particular the ratio equation and its
restriction are stated with `(O X).obj.map h.op` rather than `algebraMap`, because the scalar in
`a • e` must be typed at `oScalar` for `HSMul` to be found at all, while the colon ideals
themselves contain only multiplications and so can be written at `Γ(X, V)`.

`isQuasicoherent_of_colon_presentations` is stated for a variable `N : X.Modules` rather than for
the denominator ideal directly.  `AlgebraicGeometry.Scheme.Modules` is a `def`, so instance
search will not unfold `SheafOfModules (O X)` to it, and the `Module Γ(X, V) Γ(N, V)` instance is
therefore unavailable when `N` is spelled as a concrete `SheafOfModules (O X)`; with `N` a
variable it is found, and the resulting lemma still applies to the denominator ideal because
elaboration of an explicit argument runs at default transparency.

The restriction of a trivialization is `Stacks.SheafDescent.Trivialization.comp`, and its basis
element is the restriction of the original one — `oTrivBasis_comp` — because both are the
preimage of `1` under the same linear equivalence; this uses that `𝟙 V ≫ h = h` holds by proof
irrelevance in the poset category of opens.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.DenominatorIdeal Stacks.DenominatorColonIdeal Stacks.DenominatorLocalRatio
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.DenominatorIdealQcoh

variable (X : Scheme.{u})

/-! ### Submodules of the structure sheaf -/

/-- The sections over `V` of a module equipped with a map to the structure sheaf, mapped to the
sections of the structure sheaf, as a `Γ(X, V)`-linear map. -/
def inclₗ (N : X.Modules) (ι : N ⟶ SheafOfModules.unit X.ringCatSheaf) (V : Opens X) :
    Γ(N, V) →ₗ[Γ(X, V)] Γ(X, V) where
  toFun d := ι.val.app (op V) d
  map_add' x y := map_add _ x y
  map_smul' r x := (ι.val.app (op V)).hom.map_smul r x

/-- `inclₗ` evaluates to the inclusion of sections in the structure sheaf. -/
@[simp] lemma inclₗ_apply (N : X.Modules) (ι : N ⟶ SheafOfModules.unit X.ringCatSheaf)
    (V : Opens X) (d : Γ(N, V)) : inclₗ X N ι V d = ι.val.app (op V) d := rfl

/-- The same map over a basic open set, read as a linear map over the sections of the structure
sheaf on the ambient open set. -/
def inclBasicOpenₗ (N : X.Modules) (ι : N ⟶ SheafOfModules.unit X.ringCatSheaf) {V : Opens X}
    (f : Γ(X, V)) :
    letI := moduleOfLE N (X.basicOpen_le f)
    Γ(N, X.basicOpen f) →ₗ[Γ(X, V)] Γ(X, X.basicOpen f) :=
  letI := moduleOfLE N (X.basicOpen_le f)
  { toFun d := ι.val.app (op (X.basicOpen f)) d
    map_add' x y := map_add _ x y
    map_smul' _r x := (ι.val.app (op (X.basicOpen f))).hom.map_smul _ x }

/-- Restriction of sections commutes with the inclusion in the structure sheaf. -/
lemma inclBasicOpenₗ_restrictₗ (N : X.Modules) (ι : N ⟶ SheafOfModules.unit X.ringCatSheaf)
    {V : Opens X} (f : Γ(X, V)) (x : Γ(N, V)) :
    inclBasicOpenₗ X N ι f (restrictₗ N (X.basicOpen_le f) x) =
      algebraMap Γ(X, V) Γ(X, X.basicOpen f) (inclₗ X N ι V x) :=
  PresheafOfModules.naturality_apply ι.val (homOfLE (X.basicOpen_le f)).op x

/-- `inclBasicOpenₗ` evaluates to the inclusion of sections in the structure sheaf. -/
lemma inclBasicOpenₗ_apply (N : X.Modules) (ι : N ⟶ SheafOfModules.unit X.ringCatSheaf)
    {V : Opens X} (f : Γ(X, V)) (d : Γ(N, X.basicOpen f)) :
    inclBasicOpenₗ X N ι f d = ι.val.app (op (X.basicOpen f)) d := rfl

/-- **A submodule of the structure sheaf presented by a colon ideal on an affine open and on one
of its basic opens is localized there.**  If the sections of `N` over an affine open `V` are the
colon ideal `(b Γ(X, V) : a)` and its sections over `X.basicOpen f` are the colon ideal of the
restricted data, then the sections over `X.basicOpen f` are the localization of the sections over
`V` away from `f`.

This is `Stacks.ColonLocalization.isLocalizedModule_of_range_eq_colon` with the localization of
`Γ(X, V)` supplied by `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`. -/
theorem isLocalizedModule_restrictₗ_of_range_eq_colon (N : X.Modules)
    (ι : N ⟶ SheafOfModules.unit X.ringCatSheaf) {V : Opens X} (hV : IsAffineOpen V)
    (f : Γ(X, V)) (hinj : Function.Injective (inclₗ X N ι V))
    (hinj' : Function.Injective (inclBasicOpenₗ X N ι f)) (a b : Γ(X, V))
    (hrange : Set.range (inclₗ X N ι V) = {g : Γ(X, V) | ∃ v : Γ(X, V), g * a = b * v})
    (hrange' : Set.range (inclBasicOpenₗ X N ι f) =
      {g : Γ(X, X.basicOpen f) | ∃ v : Γ(X, X.basicOpen f),
        g * algebraMap Γ(X, V) Γ(X, X.basicOpen f) a =
          algebraMap Γ(X, V) Γ(X, X.basicOpen f) b * v}) :
    letI := moduleOfLE N (X.basicOpen_le f)
    IsLocalizedModule.Away f (restrictₗ N (X.basicOpen_le f)) := by
  let := moduleOfLE N (X.basicOpen_le f)
  let := hV.isLocalization_basicOpen f
  exact Stacks.ColonLocalization.isLocalizedModule_of_range_eq_colon _
    (restrictₗ N (X.basicOpen_le f)) (inclₗ X N ι V) (inclBasicOpenₗ X N ι f) hinj hinj'
    (inclBasicOpenₗ_restrictₗ X N ι f) hrange hrange'

/-! ### The denominator ideal -/

variable (L : SheafOfModules.{u} (O X)) (s : MeromorphicSection.{u, u} X.sheaf L)

/-- The inclusion of the denominator ideal in the structure sheaf is injective on the sections
over every open set: it is a monomorphism of sheaves of modules by
`Stacks.DenominatorIdealInvertible.denominatorIdeal_inclusion_mono`, and the evaluation functors
preserve monomorphisms. -/
lemma injective_denominatorIdealι_app
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L)
    (U : (Opens X)ᵒᵖ) : Function.Injective ((denominatorIdealι X L s).val.app U) := by
  have hq : Mono (denominatorIdealι X L s) :=
    Stacks.DenominatorIdealInvertible.denominatorIdeal_inclusion_mono X L s hL
  have happ : Mono (((SheafOfModules.forget (O X) ⋙
      PresheafOfModules.toPresheaf (O X).obj).map (denominatorIdealι X L s)).app U) :=
    inferInstance
  exact fun _ _ hab => (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp happ hab

/-- The restriction of a trivialization trivializes on the restriction of its basis element. -/
lemma oTrivBasis_comp {V V' : Opens X}
    (θ : Stacks.SheafDescent.Trivialization X.presheaf L.val V) (h : V' ⟶ V) :
    oTrivBasis X L (θ.comp h) = L.val.map h.op (oTrivBasis X L θ) := by
  refine (oTriv X L (θ.comp h)).injective ?_
  have h1 : oTriv X L (θ.comp h) (oTrivBasis X L (θ.comp h)) = 1 :=
    (oTriv X L (θ.comp h)).apply_symm_apply 1
  have h2 : oTriv X L (θ.comp h) (L.val.map h.op (oTrivBasis X L θ)) = 1 := θ.θ_basisAt h
  rw [h1, h2]

/-- Restriction along an inclusion of open sets, on sections of the structure sheaf, is the
structure map of the algebra of sections over the smaller set. -/
lemma oMap_eq_algebraMap {V : Opens X} (f : Γ(X, V)) (a : Γ(X, V)) :
    (O X).obj.map (homOfLE (X.basicOpen_le f)).op a =
      algebraMap Γ(X, V) Γ(X, X.basicOpen f) a := rfl

/-- The ratio equation restricts: if the meromorphic section `s` is `a / b` over `V` relative to
the basis element of a trivialization, it is the ratio of the restrictions of `a` and `b`
relative to the basis element of the restricted trivialization. -/
lemma toK_app_restrict {V V' : Opens X} (h : V' ⟶ V)
    (θ : Stacks.SheafDescent.Trivialization X.presheaf L.val V) {a b : oScalar X V}
    (hbt : (toK X L).val.app (op V) (a • oTrivBasis X L θ) =
      (sectionMap X L s).val.app (op V) b) :
    (toK X L).val.app (op V') ((O X).obj.map h.op a • oTrivBasis X L (θ.comp h)) =
      (sectionMap X L s).val.app (op V') ((O X).obj.map h.op b) := by
  have e1 : (toK X L).val.app (op V') (L.val.map h.op (a • oTrivBasis X L θ)) =
      (kAsOModule X L).val.map h.op ((toK X L).val.app (op V) (a • oTrivBasis X L θ)) :=
    PresheafOfModules.naturality_apply (toK X L).val h.op _
  have e2 : (sectionMap X L s).val.app (op V')
        ((SheafOfModules.unit (O X)).val.map h.op b) =
      (kAsOModule X L).val.map h.op ((sectionMap X L s).val.app (op V) b) :=
    PresheafOfModules.naturality_apply (sectionMap X L s).val h.op _
  have e3 : L.val.map h.op (a • oTrivBasis X L θ) =
      (O X).obj.map h.op a • oTrivBasis X L (θ.comp h) := by
    rw [oTrivBasis_comp X L θ h]
    exact L.val.map_smul h.op a (oTrivBasis X L θ)
  rw [← e3, e1, hbt, ← e2]
  rfl

/-- **The colon-ideal presentation of the denominator ideal restricts to a basic open.**  On
`X.basicOpen f` the data are again trivialized — the trivialization restricts, the restriction of
a nonzerodivisor is a nonzerodivisor because `Γ(X, X.basicOpen f)` is a localization of
`Γ(X, V)`, and the ratio equation restricts by naturality — so the denominator ideal there is the
colon ideal of the restricted numerator and denominator. -/
theorem range_denominatorIdealι_app_basicOpen
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L)
    {V : Opens X} (hV : IsAffineOpen V)
    (θ : Stacks.SheafDescent.Trivialization X.presheaf L.val V)
    {b : oScalar X V} (hb : b ∈ nonZeroDivisors Γ(X, V)) {a : oScalar X V}
    (hbt : (toK X L).val.app (op V) (a • oTrivBasis X L θ) =
      (sectionMap X L s).val.app (op V) b) (f : Γ(X, V)) :
    Set.range (ConcreteCategory.hom
        ((denominatorIdealι X L s).val.app (op (X.basicOpen f)))) =
      {g : Γ(X, X.basicOpen f) | ∃ v : Γ(X, X.basicOpen f),
        g * algebraMap Γ(X, V) Γ(X, X.basicOpen f) a =
          algebraMap Γ(X, V) Γ(X, X.basicOpen f) b * v} := by
  let := hV.isLocalization_basicOpen f
  have hb' : (O X).obj.map (homOfLE (X.basicOpen_le f)).op b ∈
      nonZeroDivisors Γ(X, X.basicOpen f) :=
    IsLocalization.nonZeroDivisors_le_comap (M := Submonoid.powers f)
      (S := Γ(X, X.basicOpen f)) hb
  exact range_denominatorIdealι_app_eq X L s hL (hV.basicOpen f)
    (θ.comp (homOfLE (X.basicOpen_le f))) hb'
    (toK_app_restrict X L s (homOfLE (X.basicOpen_le f)) θ hbt)

/-- **Around every point there is an affine open on which the denominator ideal is a colon
ideal, and so is its restriction to every basic open of it.**  The affine open, its
trivialization and the ratio come from
`Stacks.DenominatorLocalRatio.exists_affineOpen_denominator`, which uses no Noetherian
hypothesis. -/
theorem exists_affineOpen_colon_presentations
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L) (x : X) :
    ∃ (V : Opens X) (_ : x ∈ V) (_ : IsAffineOpen V) (a b : Γ(X, V)),
      Set.range (ConcreteCategory.hom ((denominatorIdealι X L s).val.app (op V))) =
          {g : Γ(X, V) | ∃ v : Γ(X, V), g * a = b * v} ∧
        ∀ f : Γ(X, V),
          Set.range (ConcreteCategory.hom
              ((denominatorIdealι X L s).val.app (op (X.basicOpen f)))) =
            {g : Γ(X, X.basicOpen f) | ∃ v : Γ(X, X.basicOpen f),
              g * algebraMap Γ(X, V) Γ(X, X.basicOpen f) a =
                algebraMap Γ(X, V) Γ(X, X.basicOpen f) b * v} := by
  obtain ⟨V, -, hxV, hVaff, ⟨θ⟩, b, hb, t, hbt⟩ :=
    Stacks.DenominatorLocalRatio.exists_affineOpen_denominator X L s hL ⊤ x (Opens.mem_top x)
  obtain ⟨a, hat⟩ := exists_smul_oTrivBasis X L θ t
  rw [hat] at hbt
  exact ⟨V, hxV, hVaff, a, b, range_denominatorIdealι_app_eq X L s hL hVaff θ hb hbt,
    fun f => range_denominatorIdealι_app_basicOpen X L s hL hVaff θ hb hbt f⟩

/-- **A submodule of the structure sheaf which is a colon ideal on an affine neighbourhood of
every point, and on every basic open of that neighbourhood, is quasi-coherent.**  The colon ideal
commutes with localization, so the first condition gives the localization statement on every
basic open of the neighbourhood, and quasi-coherence is detected on the members of a cover. -/
theorem isQuasicoherent_of_colon_presentations (N : X.Modules)
    (ι : N ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hinj : ∀ W : Opens X, Function.Injective (ConcreteCategory.hom (ι.val.app (op W))))
    (hpres : ∀ x : X, ∃ (V : Opens X) (_ : x ∈ V) (_ : IsAffineOpen V) (a b : Γ(X, V)),
      Set.range (ConcreteCategory.hom (ι.val.app (op V))) =
          {g : Γ(X, V) | ∃ v : Γ(X, V), g * a = b * v} ∧
        ∀ f : Γ(X, V), Set.range (ConcreteCategory.hom (ι.val.app (op (X.basicOpen f)))) =
          {g : Γ(X, X.basicOpen f) | ∃ v : Γ(X, X.basicOpen f),
            g * algebraMap Γ(X, V) Γ(X, X.basicOpen f) a =
              algebraMap Γ(X, V) Γ(X, X.basicOpen f) b * v}) :
    N.IsQuasicoherent := by
  choose V hxV hVaff a b hr hr' using hpres
  refine isQuasicoherent_of_isLocalizedModule_cover N V ?_ hVaff fun x f => ?_
  · exact IsOpenCover.mk (eq_top_iff.mpr fun y _ => Opens.mem_iSup.mpr ⟨y, hxV y⟩)
  · exact isLocalizedModule_restrictₗ_of_range_eq_colon X N ι (hVaff x) f
      (fun _ _ h => hinj (V x) h) (fun _ _ h => hinj (X.basicOpen f) h) (a x) (b x)
      (hr x) (hr' x f)

/-- **The denominator ideal of a meromorphic section of an invertible sheaf is quasi-coherent.**

Around every point there is an affine open `V` on which the denominator ideal is the colon ideal
`(b Γ(X, V) : a)` for a nonzerodivisor `b` and a numerator `a`, and the colon ideal commutes with
localization, so the sections over each basic open of `V` are the localization of the sections
over `V`.  Those affine opens cover `X`, and quasi-coherence is detected by that condition on the
members of a cover. -/
@[stacks 02P0 "quasi-coherence", ega "IV 20.2.14" "special case"]
theorem denominatorIdeal_isQuasicoherent
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L) :
    (denominatorIdeal X L s).IsQuasicoherent :=
  isQuasicoherent_of_colon_presentations X (denominatorIdeal X L s) (denominatorIdealι X L s)
    (fun W => injective_denominatorIdealι_app X L s hL (op W))
    (exists_affineOpen_colon_presentations X L s hL)

end Stacks.DenominatorIdealQcoh

end
