module

public import Mathlib.RingTheory.LocalProperties.Submodule
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.IdealPowerSections
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange

/-!
# Sections of an ideal-power multiple over an affine open

Let `X` be a scheme, `I` a quasi-coherent sheaf of ideals given by its affine-local ideal data
and `M` a quasi-coherent `𝒪_X`-module. The subsheaf `I ^ n • M` of
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple` is defined as the *least* subsheaf of
`M` whose sections over every affine open `U` contain `I(U) ^ n · Γ(M, U)`, so only the
inclusion `⊇` of

`Γ(I ^ n • M, U) = I(U) ^ n · Γ(M, U)`

is true by construction. This file proves the equality for quasi-coherent `M`.

The point is that the affine-local family `U ↦ I(U) ^ n · Γ(M, U)` is itself already a subsheaf:
membership in it is a local condition because the sections of a quasi-coherent module over a
basic open of an affine open are a localization of its sections over that affine open, and
localization commutes with the product of an ideal and a submodule. Testing the least upper
bound against that subsheaf gives the missing inclusion.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPower.idealPowSmulSections` — the submodule
  `I(U) ^ n · Γ(M, U)` of the sections over an affine open.
* `Stacks.AlgebraicGeometry.IdealPower.locallyIdealPowSmul` — the subsheaf of `M` of sections
  which lie in `idealPowSmulSections` on every affine open of their domain.

## Main results

* `Stacks.AlgebraicGeometry.IdealPower.span_image_idealPowSmulSections` — the family
  `idealPowSmulSections` localizes: the span of the image of `I(U) ^ n · Γ(M, U)` in the
  sections over a basic open `D(f) ⊆ U` is `I(D(f)) ^ n · Γ(M, D(f))`.
* `Stacks.AlgebraicGeometry.IdealPower.mem_idealPowSmulSections_of_basicOpen_cover` — the
  local-to-global step: a section lying in the family on each member of a family of basic opens
  covering an affine open lies in it over that affine open.
* `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_obj_affine_of_isQuasicoherent` — the
  equality `Γ(I ^ n • M, U) = I(U) ^ n · Γ(M, U)` on affine opens.

## Implementation notes

The ideal powers of an `AlgebraicGeometry.Scheme.IdealSheafData` are again ideal data, so the
localization property of `I(U) ^ n` is `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`
applied to `I ^ n` rather than a separate computation with `Ideal.map_pow`.

The two module structures on the sections of a quasi-coherent module over a basic open — the
native one over `Γ(X, D(f))` and the one obtained by restricting scalars along the restriction
map of the structure sheaf — are both in play; the latter is
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.moduleOfLE` and is what the localization
statements are phrased in, which is why each proof opens with the corresponding `let`s.

For the specialization to the structure sheaf see
`Stacks.LocalCohomology.idealPowerMultiple_obj_affine`, which predates this file and is proved
differently, by exhibiting the kernel of the map to the structure sheaf of the closed subscheme
as an upper bound.

**What these two results are for, and what still blocks Tag 01YB.** The source replaces `F` by
`F' = I ^ m • F` for a large `m` and needs two things of that replacement: that `F'` has no
`I`-power torsion, which rests on the equality of sections proved here together with Artin–Rees,
and that `F'|_U = F|_U`, which is
`idealPowerMultiple_obj_eq_top_of_disjoint_support'`. Both are now available, and the sections
half of 01YB follows for a *coherent* `F` on a Noetherian scheme:
`Stacks.LocalCohomology.canonicalMapToSections_bijective_of_isCoherent` in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.SectionsOverOpenCoherent`. What 01YB still asks
for beyond that lies outside this file:

* the sections half of 01YB has since been reduced from a quasi-coherent `F` to that coherent
  case, by the covering statement of Tag 01PG
  (`AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_section`), and now holds in the
  clause's own generality:
  `Stacks.LocalCohomology.canonicalMapToSections_bijective_of_isQuasicoherent` in
  `StacksFrontier.AlgebraicGeometry.LocalCohomology.SectionsOverOpenQuasicoherent`;
* what still blocks the tag is the morphism half. Its sheaf-hom input is now available for
  coherent arguments on a locally Noetherian scheme
  (`Stacks.AlgebraicGeometry.InternalHomScheme.isQuasicoherent_internalHomSheaf`); what remains
  is the canonical map `colim_n Hom(I ^ n • G, F) ⟶ Hom_{𝒪_U}(G|_U, F|_U)` for a general source
  `G`, which no declaration in this library provides.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB) uses this computation
  through the Artin–Rees lemma.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AlgebraicGeometry.IdealPower

variable {X : Scheme.{u}}

/-- The submodule `I(U) ^ n · Γ(M, U)` of the sections of `M` over an affine open `U`. -/
public noncomputable def idealPowSmulSections (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    (U : X.affineOpens) : Submodule Γ(X, U.1) Γ(M, U.1) :=
  I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1))

/-- The restriction map of `M` carries `I(V) ^ n · Γ(M, V)` into `I(U) ^ n · Γ(M, U)` for affine
opens `U ≤ V`: the restriction of a scalar in `I(V) ^ n` lies in `I(U) ^ n`. -/
public lemma idealPowSmulSections_map_le (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    {U V : X.affineOpens} (h : U.1 ≤ V.1) {s : Γ(M, V.1)}
    (hs : s ∈ idealPowSmulSections I n M V) :
    M.presheaf.map (homOfLE h).op s ∈ idealPowSmulSections I n M U := by
  have hideal : I.ideal V ^ n ≤
      (I.ideal U ^ n).comap (X.presheaf.map (homOfLE h).op).hom :=
    (I ^ n).ideal_le_comap_ideal h
  refine Submodule.smul_induction_on hs (fun a ha x _ ↦ ?_) (fun x y hx hy ↦ ?_)
  · rw [Scheme.Modules.map_smul]
    exact Submodule.smul_mem_smul (hideal ha) Submodule.mem_top
  · rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- The family `idealPowSmulSections` localizes: over a basic open `D(f)` of an affine open `U`
the span of the image of `I(U) ^ n · Γ(M, U)` is `I(D(f)) ^ n · Γ(M, D(f))`.

This is the compatibility that makes membership in the family a local condition. -/
public lemma span_image_idealPowSmulSections (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    [M.IsQuasicoherent] (U : X.affineOpens) (f : Γ(X, U.1)) :
    Submodule.span Γ(X, X.basicOpen f)
        (M.presheaf.map (homOfLE (X.basicOpen_le f)).op ''
          (idealPowSmulSections I n M U : Set Γ(M, U.1))) =
      idealPowSmulSections I n M (X.affineBasicOpen f) := by
  let _ : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  let _ := moduleOfLE M (X.basicOpen_le f)
  let _ := isScalarTowerOfLE M (X.basicOpen_le f)
  let _ : Module Γ(X, U.1) Γ(M, U.1) := (M.val.obj (.op U.1)).isModule
  have _ : IsLocalizedModule (Submonoid.powers f) (restrictₗ M (X.basicOpen_le f)) :=
    isLocalizedModule_restrictₗ M U.2 f rfl (X.basicOpen_le f)
  have hmap : Ideal.map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f)) (I.ideal U ^ n) =
      I.ideal (X.affineBasicOpen f) ^ n := by
    have := (I ^ n).map_ideal_basicOpen U f
    simpa [RingHom.algebraMap_toAlgebra, algebraOfLE] using this
  have e1 : (idealPowSmulSections I n M U).localized' Γ(X, X.basicOpen f)
        (Submonoid.powers f) (restrictₗ M (X.basicOpen_le f)) =
      (I.ideal U ^ n).localized' Γ(X, X.basicOpen f) (Submonoid.powers f)
          (Algebra.linearMap _ _) •
        (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)).localized' Γ(X, X.basicOpen f)
          (Submonoid.powers f) (restrictₗ M (X.basicOpen_le f)) :=
    Submodule.localized'_smul _ _ _ _ _
  have e2 : (I.ideal U ^ n).localized' Γ(X, X.basicOpen f) (Submonoid.powers f)
      (Algebra.linearMap Γ(X, U.1) Γ(X, X.basicOpen f)) =
      I.ideal (X.affineBasicOpen f) ^ n :=
    (Ideal.localized'_eq_map _ _ _).trans hmap
  refine (Submodule.localized'_eq_span Γ(X, X.basicOpen f) (Submonoid.powers f)
    (restrictₗ M (X.basicOpen_le f)) (idealPowSmulSections I n M U)).symm.trans ?_
  rw [e1, e2, Submodule.localized'_top]
  rfl

/-- The local-to-global step: if the basic opens `D(f)` for `f` in a set spanning `Γ(X, U)`
all contain the restriction of `s` inside `I(D(f)) ^ n · Γ(M, D(f))`, then `s` itself lies in
`I(U) ^ n · Γ(M, U)`. -/
public lemma mem_idealPowSmulSections_of_span_eq_top (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) [M.IsQuasicoherent] (U : X.affineOpens) (t : Set Γ(X, U.1))
    (ht : Ideal.span t = ⊤) (s : Γ(M, U.1))
    (hs : ∀ f : t, M.presheaf.map (homOfLE (X.basicOpen_le f.1)).op s ∈
      idealPowSmulSections I n M (X.affineBasicOpen f.1)) :
    s ∈ idealPowSmulSections I n M U := by
  let _ (r : t) : Module Γ(X, X.basicOpen r.1) Γ(M, X.basicOpen r.1) :=
    (M.val.obj (.op (X.basicOpen r.1))).isModule
  let _ (r : t) := moduleOfLE M (X.basicOpen_le r.1)
  let _ (r : t) := isScalarTowerOfLE M (X.basicOpen_le r.1)
  let _ (r : t) : IsLocalization.Away r.1 Γ(X, X.basicOpen r.1) :=
    U.2.isLocalization_basicOpen r.1
  have _ (r : t) : IsLocalizedModule (Submonoid.powers r.1)
      (restrictₗ M (X.basicOpen_le r.1)) :=
    isLocalizedModule_restrictₗ M U.2 r.1 rfl (X.basicOpen_le r.1)
  refine Submodule.mem_of_isLocalized_span t ht (fun r ↦ Γ(M, X.basicOpen r.1))
    (fun r ↦ restrictₗ M (X.basicOpen_le r.1)) (fun r ↦ ?_)
  have : (restrictₗ M (X.basicOpen_le r.1)) s ∈
      (idealPowSmulSections I n M U).localized' Γ(X, X.basicOpen r.1) (Submonoid.powers r.1)
        (restrictₗ M (X.basicOpen_le r.1)) := by
    rw [Submodule.localized'_eq_span]
    exact (span_image_idealPowSmulSections I n M U r.1).ge (hs r)
  exact this

/-! ### The affine-local family as a subsheaf -/

/-- The sections of `M` over an open `V` which lie in `I(W) ^ n · Γ(M, W)` on every affine open
`W ≤ V`, as a submodule of the underlying presheaf of modules. -/
public noncomputable def locallyIdealPowSmulPresheaf (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) : M.val.Submodule where
  obj V :=
    { carrier := {s | ∀ (W : X.affineOpens) (h : W.1 ≤ V.unop),
        M.val.map (homOfLE h).op s ∈ idealPowSmulSections I n M W}
      zero_mem' := fun W h ↦ by
        rw [map_zero]
        exact Submodule.zero_mem _
      add_mem' := fun {a b} ha hb W h ↦ by
        rw [map_add]
        exact Submodule.add_mem _ (ha W h) (hb W h)
      smul_mem' := fun c a ha W h ↦ by
        rw [PresheafOfModules.map_smul]
        exact Submodule.smul_mem _ _ (ha W h) }
  map {V V'} g := fun s hs W h ↦ by
    have h1 : W.1 ≤ V.unop := h.trans (leOfHom g.unop)
    have key : M.val.map (homOfLE h).op (M.val.map g s) =
        M.val.map (homOfLE h1).op s := by
      rw [← PresheafOfModules.map_comp_apply]
      exact PresheafOfModules.congr_map_apply M.val (Subsingleton.elim _ _) s
    simp only [PresheafOfModules.restrictₛₗ_apply]
    rw [key]
    exact hs W h1

/-- Membership in `locallyIdealPowSmulPresheaf` is a local condition, so it defines a subsheaf
of `M`.

Over an affine open the condition is tested on a family of basic opens covering it, and
`mem_idealPowSmulSections_of_span_eq_top` closes the gap because those basic opens span the
unit ideal. -/
public noncomputable def locallyIdealPowSmul (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    [M.IsQuasicoherent] : M.Submodule where
  toSubmodule := locallyIdealPowSmulPresheaf I n M
  isSheaf {V} s hs := by
    intro W hW
    set u : Γ(M, W.1) := M.val.map (homOfLE hW).op s with hu
    set t : Set Γ(X, W.1) :=
      {f | M.val.map (homOfLE (X.basicOpen_le f)).op u ∈
        idealPowSmulSections I n M (X.affineBasicOpen f)} with hT
    have hspan : Ideal.span t = ⊤ := by
      rw [← W.2.iSup_basicOpen_eq_self_iff]
      refine le_antisymm (iSup_le fun f ↦ X.basicOpen_le f.1) fun x hx ↦ ?_
      obtain ⟨V', g, hg, hxV'⟩ := hs x (hW hx)
      obtain ⟨f, hfle, hxf⟩ :=
        W.2.exists_basicOpen_le (V := W.1 ⊓ V') ⟨x, ⟨hx, hxV'⟩⟩ hx
      have hft : f ∈ t := by
        have hmem := hg (X.affineBasicOpen f) (hfle.trans inf_le_right)
        have hcomp : M.val.map (homOfLE (hfle.trans inf_le_right : X.basicOpen f ≤ V')).op
            (M.val.map g.op s) = M.val.map (homOfLE (X.basicOpen_le f)).op u := by
          rw [hu, ← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
          exact PresheafOfModules.congr_map_apply M.val (Subsingleton.elim _ _) s
        have hmem' : M.val.map
            (homOfLE (hfle.trans inf_le_right : X.basicOpen f ≤ V')).op (M.val.map g.op s) ∈
              idealPowSmulSections I n M (X.affineBasicOpen f) := hmem
        rw [hcomp] at hmem'
        exact hmem'
      exact IsConcreteLE.le_iff.mp (le_iSup (fun f : t ↦ X.basicOpen f.1) ⟨f, hft⟩) hxf
    exact mem_idealPowSmulSections_of_span_eq_top I n M W t hspan u fun f ↦ f.2

/-- The affine-local lower bound defining `I ^ n • M` holds for `locallyIdealPowSmul`: a
section in `I(U) ^ n · Γ(M, U)` restricts into `I(W) ^ n · Γ(M, W)` on every affine `W ≤ U`. -/
public lemma le_locallyIdealPowSmul (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    [M.IsQuasicoherent] (U : X.affineOpens) :
    idealPowSmulSections I n M U ≤
      (locallyIdealPowSmul I n M).toSubmodule.obj (op U.1) :=
  fun _ hs _W h ↦ idealPowSmulSections_map_le I n M h hs

/-- **The sections of `I ^ n • M` over an affine open.** For a quasi-coherent module `M` on a
scheme and a quasi-coherent sheaf of ideals `I`, the sections of the subsheaf `I ^ n • M` over
an affine open `U` are exactly `I(U) ^ n · Γ(M, U)`.

The inclusion `⊇` is the defining affine-local lower bound of `idealPowerMultiple`; the
inclusion `⊆` holds because the affine-local family `I(U) ^ n · Γ(M, U)` is itself a subsheaf
of `M`, namely `locallyIdealPowSmul`, so the least such subsheaf is contained in it. -/
public alias idealPowerMultiple_obj_affine_of_isQuasicoherent :=
  Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_obj_affineOpen

/-! ### The ideal-power multiple away from the vanishing locus -/

/-- On an affine open disjoint from the support of `I` the ideal of `I` is the unit ideal: its
vanishing locus in that chart is empty. -/
public lemma ideal_eq_top_of_affine_disjoint_support (I : X.IdealSheafData) (U : X.affineOpens)
    (hU : ∀ x ∈ U.1, x ∉ I.support) : I.ideal U = ⊤ := by
  have hdisj : X.zeroLocus (U := U.1) (I.ideal U) ∩ (U.1 : Set X) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hxZ, hxU⟩
    exact hU x hxU ((I.mem_support_iff_of_mem hxU).2 hxZ)
  have hz : PrimeSpectrum.zeroLocus (I.ideal U : Set Γ(X, U.1)) = ∅ := by
    by_contra hne
    obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have himage : U.2.fromSpec '' PrimeSpectrum.zeroLocus (I.ideal U : Set Γ(X, U.1)) = ∅ := by
      rw [U.2.fromSpec_image_zeroLocus]
      exact hdisj
    exact absurd (show U.2.fromSpec p ∈
      U.2.fromSpec '' PrimeSpectrum.zeroLocus (I.ideal U : Set Γ(X, U.1)) from ⟨p, hp, rfl⟩)
      (by simp [himage])
  simpa only [SetLike.coe_sort_coe] using PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp hz

/-- **`I ^ n • M` agrees with `M` away from `V(I)`.** Over an open disjoint from the support of
`I` the subsheaf `I ^ n • M` has all of the sections of `M`.

The affine opens contained in the given open cover it, on each of them `I` is the unit ideal, so
the defining affine-local lower bound already gives every section there, and membership in a
subsheaf is a local condition. No quasi-coherence of `M` is needed.

The disjointness is asked of the open itself.  The unprimed
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_obj_eq_top_of_disjoint_support` of
`StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.IdealPowerSections` is the same assertion
with the open presented as a subobject of an ambient open disjoint from the support, which is
the shape its own consumers apply it in. -/
public theorem idealPowerMultiple_obj_eq_top_of_disjoint_support' (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) (V : X.Opens) (hV : ∀ x ∈ V, x ∉ I.support) :
    (idealPowerMultiple I n M).toSubmodule.obj (op V) = ⊤ := by
  refine eq_top_iff.2 fun s _ ↦ (idealPowerMultiple I n M).isSheaf s fun x hx ↦ ?_
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  refine ⟨W, homOfLE hWV, ?_, hxW⟩
  have htop : I.ideal ⟨W, hW⟩ = ⊤ :=
    ideal_eq_top_of_affine_disjoint_support I ⟨W, hW⟩ fun y hy ↦ hV y (hWV hy)
  refine le_idealPowerMultiple_obj I n M ⟨W, hW⟩ ?_
  rw [htop, Ideal.top_pow, Submodule.top_smul]
  exact Submodule.mem_top

end Stacks.AlgebraicGeometry.IdealPower

end
