module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiSeparated.LocalizedRestriction
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Sections
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of quasi-coherent modules vanishing on a principal open

Let `X` be a scheme, let `W` be a quasi-compact open of `X` and let `g` be a function on `W`.
A morphism `α : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules with `ℱ` of finite type whose
restriction to the principal open `X_g` vanishes is annihilated by a single power of `g`: there
is one exponent `e` with `g ^ e • α = 0` over every open contained in `W`.

This is the statement that makes the comparison map of
[Stacks, Tag 0B5M](https://stacks.math.columbia.edu/tag/0B5M) injective in the case of a
*trivial* invertible module, which is the case the Stacks proof of
[Stacks, Tag 01XQ](https://stacks.math.columbia.edu/tag/01XQ) treats first and then glues: for
a general invertible `ℒ` one chooses a finite affine cover over which `ℒ` is trivial and
`s|_{U_j}` becomes a function `f_j` with `X_s ∩ U_j = D(f_j)`.

## Main results

* `AlgebraicGeometry.exists_pow_smul_app_eq_zero_of_isCompact`: the uniform exponent over a
  quasi-compact open.
* `AlgebraicGeometry.exists_pow_smul_app_eq_zero_of_compactSpace`: the same statement on a
  quasi-compact scheme.

## Implementation notes

Neither part of Tag 01XQ itself is proved here, so no `@[stacks 01XQ]` attribute is attached.
Tag 01XQ is about the map `0B5M`
`(⨁_{n} Hom(ℱ, 𝒢 ⊗ ℒ^{⊗ n}))_{(s)} ⟶ Hom_{𝒪_{X_s}}(ℱ|_{X_s}, 𝒢|_{X_s})`, which is already
constructed as `Stacks.SheafOfModules.homLocalizationMap`; what is missing is its injectivity
for `ℱ` of finite type and its bijectivity for `ℱ` of finite presentation, both of which also
require transporting the statement below across the tensor powers of `ℒ`.

The three steps are the ones in the source. Over an affine open `U` the sections `Γ(ℱ, U)`
form a finite `Γ(X, U)`-module (`AlgebraicGeometry.moduleFinite_sections_on_affine`, Tag 01PB)
and `Γ(𝒢, X.basicOpen g|_U)` is their localization (Tag 01P7), so
`Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule` — the algebra statement whose proof
the source omits — produces an exponent there. Quasi-compactness of `W` makes finitely many
affine opens suffice, and the supremum of their exponents is the uniform one. Passing from an
affine open to its basic opens uses that the sections of `ℱ` over a basic open are a
localization again and that the defining function becomes a unit there; the basic opens of the
members of the cover form a cover of every open, so the sheaf condition on `𝒢` finishes.

## References

* [Stacks Project, Tag 01XQ](https://stacks.math.columbia.edu/tag/01XQ)
* [Stacks Project, Tag 0B5M](https://stacks.math.columbia.edu/tag/0B5M)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 0583](https://stacks.math.columbia.edu/tag/0583)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.QcohLimits
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.AlgebraicGeometry.QcqsLocalizedRestriction

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- On an affine open, a morphism of quasi-coherent modules whose source is of finite type and
which vanishes on the principal open of `g` is annihilated by a power of `g`. -/
private theorem exists_pow_smul_app_eq_zero_of_isAffineOpen (F G : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] [G.IsQuasicoherent] (α : F ⟶ G) {W : X.Opens}
    (g : Γ(X, W)) (hα : ∀ V ≤ X.basicOpen g, ∀ x : Γ(F, V), α.app V x = 0) {U : X.Opens}
    (hU : IsAffineOpen U) (hUW : U ≤ W) :
    ∃ e : ℕ, ∀ x : Γ(F, U), X.presheaf.map (homOfLE hUW).op g ^ e • α.app U x = 0 := by
  set gU : Γ(X, U) := X.presheaf.map (homOfLE hUW).op g with hgU
  have hle : X.basicOpen gU ≤ U := X.basicOpen_le gU
  let _i := moduleOfLE G hle
  have hloc : IsLocalizedModule.Away gU (restrictₗ G hle) :=
    isLocalizedModule_restrictₗ G hU gU rfl hle
  have hFin : Module.Finite Γ(X, U) Γ(F, U) := moduleFinite_sections_on_affine F U hU
  have hbo : X.basicOpen gU ≤ X.basicOpen g := by
    rw [hgU, X.basicOpen_res g (homOfLE hUW).op]
    exact inf_le_right
  have hcomp : (restrictₗ G hle).comp (appₗ α U)
      = (restrictₗ G hle).comp (0 : Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U)) := by
    ext x
    change G.presheaf.map (homOfLE hle).op (α.app U x) = _
    rw [← app_naturality α hle x, hα (X.basicOpen gU) hbo _]
    simp
  obtain ⟨s, hs⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    (Submonoid.powers gU) (restrictₗ G hle) (appₗ α U) 0 hcomp
  obtain ⟨n, hn⟩ := s.2
  refine ⟨n, fun x => ?_⟩
  rw [show gU ^ n = (s : Γ(X, U)) from hn]
  simpa [LinearMap.smul_apply, Submonoid.smul_def, appₗ] using LinearMap.congr_fun hs x

/-- An exponent annihilating a morphism of quasi-coherent modules over an affine open
annihilates it over each basic open of that affine open. -/
private theorem pow_smul_app_basicOpen_eq_zero (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (α : F ⟶ G) {U : X.Opens} (hU : IsAffineOpen U) (c a : Γ(X, U)) (e : ℕ)
    (he : ∀ x : Γ(F, U), c ^ e • α.app U x = 0) (y : Γ(F, X.basicOpen a)) :
    X.presheaf.map (homOfLE (X.basicOpen_le a)).op c ^ e • α.app (X.basicOpen a) y = 0 := by
  let _iF := moduleOfLE F (X.basicOpen_le a)
  have hlocF : IsLocalizedModule.Away a (restrictₗ F (X.basicOpen_le a)) :=
    isLocalizedModule_restrictₗ F hU a rfl (X.basicOpen_le a)
  obtain ⟨n, z, hz⟩ := IsLocalizedModule.Away.surj (restrictₗ F (X.basicOpen_le a)) a y
  have hunit : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) :=
    X.toRingedSpace.isUnit_res_basicOpen a
  refine ((hunit.pow n).smul_eq_zero).mp ?_
  have hstep : X.presheaf.map (homOfLE (X.basicOpen_le a)).op a ^ n • α.app (X.basicOpen a) y
      = α.app (X.basicOpen a) (F.presheaf.map (homOfLE (X.basicOpen_le a)).op z) := by
    rw [← map_pow, ← α.app_smul]
    exact congrArg (α.app (X.basicOpen a)) hz
  rw [smul_comm, hstep, app_naturality α (X.basicOpen_le a) z, ← map_pow, ← G.map_smul, he z,
    map_zero]

/-- **The trivially twisted case of [Stacks, Tag 01XQ] part (1).** Let `g` be a function on a
quasi-compact open `W` of a scheme `X`. If a morphism `α : ℱ ⟶ 𝒢` of quasi-coherent
`𝒪_X`-modules with `ℱ` of finite type vanishes on the principal open of `g`, then a single
power of `g` annihilates `α` over every open contained in `W`. -/
theorem exists_pow_smul_app_eq_zero_of_isCompact (F G : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] [G.IsQuasicoherent] (α : F ⟶ G) {W : X.Opens} (hW : IsCompact (W : Set X))
    (g : Γ(X, W)) (hα : ∀ V ≤ X.basicOpen g, ∀ x : Γ(F, V), α.app V x = 0) :
    ∃ e : ℕ, ∀ (V : X.Opens) (hV : V ≤ W) (x : Γ(F, V)),
      X.presheaf.map (homOfLE hV).op g ^ e • α.app V x = 0 := by
  classical
  choose ee hee using fun U : {U : X.affineOpens // U.1 ≤ W} =>
    exists_pow_smul_app_eq_zero_of_isAffineOpen F G α g hα U.1.2 U.2
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover
    (fun U : {U : X.affineOpens // U.1 ≤ W} => (U.1.1 : Set X))
    (fun U => U.1.1.isOpen) (fun x hx => by
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
      exact Set.mem_iUnion.2 ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩)
  refine ⟨t.sup ee, fun V hV x => ?_⟩
  have hbump : ∀ U ∈ t, ∀ y : Γ(F, (U : {U : X.affineOpens // U.1 ≤ W}).1.1),
      X.presheaf.map (homOfLE U.2).op g ^ t.sup ee • α.app U.1.1 y = 0 := by
    intro U hU y
    rw [← Nat.sub_add_cancel (Finset.le_sup (f := ee) hU), pow_add, mul_smul, hee U y, smul_zero]
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨G.presheaf, G.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun p : {p : (Σ U : {U : X.affineOpens // U.1 ≤ W}, Γ(X, U.1.1)) //
        p.1 ∈ t ∧ X.basicOpen p.2 ≤ V} => X.basicOpen p.1.2)
    V (fun p => homOfLE p.2.2) ?_ _ 0 ?_
  · intro z hzV
    obtain ⟨U, hUt, hzU⟩ := Set.mem_iUnion₂.1 (ht (hV hzV))
    obtain ⟨a, haV, hza⟩ := U.1.2.exists_basicOpen_le (⟨z, hzV⟩ : V) hzU
    exact Opens.mem_iSup.2 ⟨⟨⟨U, a⟩, hUt, haV⟩, hza⟩
  · intro p
    obtain ⟨⟨U, a⟩, hUt, haV⟩ := p
    have hbU : X.basicOpen a ≤ U.1.1 := X.basicOpen_le a
    have hg2 : X.presheaf.map (homOfLE haV).op (X.presheaf.map (homOfLE hV).op g)
        = X.presheaf.map (homOfLE (hbU.trans U.2)).op g := resRing_res hV haV _ g
    rw [map_zero, G.map_smul, map_pow, hg2, ← app_naturality α haV x,
      ← resRing_res U.2 hbU (hbU.trans U.2) g]
    exact pow_smul_app_basicOpen_eq_zero F G α U.1.2
      (X.presheaf.map (homOfLE U.2).op g) a (t.sup ee) (hbump U hUt) _

/-- **The trivially twisted case of [Stacks, Tag 01XQ] part (1) on a quasi-compact scheme.** A
morphism of quasi-coherent modules with source of finite type which vanishes on the principal
open of a global function is annihilated by a power of that function. -/
theorem exists_pow_smul_app_eq_zero_of_compactSpace [CompactSpace X] (F G : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] [G.IsQuasicoherent] (α : F ⟶ G) (g : Γ(X, ⊤))
    (hα : ∀ V ≤ X.basicOpen g, ∀ x : Γ(F, V), α.app V x = 0) :
    ∃ e : ℕ, ∀ (V : X.Opens) (x : Γ(F, V)),
      X.presheaf.map (homOfLE (le_top (a := V))).op g ^ e • α.app V x = 0 := by
  obtain ⟨e, he⟩ := exists_pow_smul_app_eq_zero_of_isCompact F G α
    (W := ⊤) (by simpa using isCompact_univ) g hα
  exact ⟨e, fun V => he V le_top⟩

end AlgebraicGeometry

end
