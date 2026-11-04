module

public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# The kernel ideal sheaf of a morphism read on global sections

Let `f : X ⟶ Y` be a quasi-compact morphism of schemes. Its kernel ideal sheaf
`AlgebraicGeometry.Scheme.Hom.ker` is indexed by the *affine* opens of `Y`, where it is the
kernel of the map on sections; the kernel of the map `Γ(Y, ⊤) ⟶ Γ(X, ⊤)` on global sections is
a different object, and over a non-affine `Y` it need not be the value of any ideal sheaf.

This file relates the two in the direction needed to recognise a thickening: if a power of the
kernel ideal sheaf vanishes, the same power of the global-sections kernel vanishes.

## Main results

* `AlgebraicGeometry.Scheme.ker_appTop_pow_eq_bot`: if `f.ker ^ n = ⊥` then
  `RingHom.ker f.appTop.hom ^ n = ⊥`.

Quasi-compactness is an explicit hypothesis rather than an instance: the morphism this is
applied to is a base change produced by a representability witness, and instance search does
not see through the projections of such a witness to the closed immersion it carries.

## Implementation notes

`AlgebraicGeometry.Scheme.ker_pow_eq_bot_iff_of_isAffine` is the two-sided statement when `Y`
is affine, where `Γ(Y, ⊤)` is the ring of an affine open and the ideal sheaf is determined by
its value there. The implication proved here needs no affineness of `Y`, and only one
direction is available without it: a global section of the kernel ideal sheaf is exactly a
global section whose restriction to every affine open lies in the kernel there, which is
weaker than lying in the kernel on global sections only when `Y` is not covered by one affine.

The proof restricts to a single affine open. Restriction carries `RingHom.ker f.appTop` into
`RingHom.ker (f.app U)` by naturality of `f` on sections, so it carries the `n`th power of the
first ideal into the `n`th power of the second, which is `(f.ker ^ n).ideal U = ⊥`. A global
section all of whose restrictions to affine opens vanish is zero, the affine opens being a
basis of the topology and `Γ` a sheaf.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme

/-- Restriction to an affine open carries the kernel of a morphism on global sections into its
kernel over that open: the two are related by naturality of the map on sections. -/
private theorem mem_ker_app_of_mem_ker_appTop {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.affineOpens) {s : Γ(Y, ⊤)} (hs : s ∈ RingHom.ker f.appTop.hom) :
    (Y.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom s ∈
      RingHom.ker (f.app U.1).hom := by
  have h1 := f.naturality (U' := (⊤ : Y.Opens)) (U := U.1) (homOfLE le_top).op
  have h2 := congrArg (fun φ => (CommRingCat.Hom.hom φ) s) h1
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  rw [RingHom.mem_ker] at hs ⊢
  rw [h2, show (CommRingCat.Hom.hom (Scheme.Hom.app f ⊤)) s = 0 from hs, map_zero]

/-- **A vanishing power of the kernel ideal sheaf vanishes on global sections.** If the `n`th
power of the kernel ideal sheaf of a quasi-compact morphism of schemes is zero, then the `n`th
power of the kernel of the induced map `Γ(Y, ⊤) ⟶ Γ(X, ⊤)` is zero.

No affineness of the target is needed: the `n`th power of the global-sections kernel restricts
into the `n`th power of the kernel ideal over each affine open, which vanishes, and a global
section vanishing on a basis of opens is zero. -/
theorem ker_appTop_pow_eq_bot {X Y : Scheme.{u}} (f : X ⟶ Y) (hqc : QuasiCompact f) {n : ℕ}
    (hf : f.ker ^ n = ⊥) : RingHom.ker f.appTop.hom ^ n = ⊥ := by
  have := hqc
  have key : ∀ U : Y.affineOpens, ∀ s ∈ RingHom.ker f.appTop.hom ^ n,
      (Y.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom s = 0 := by
    intro U s hs
    have hbot : RingHom.ker (f.app U.1).hom ^ n = ⊥ := by
      have hpow : (f.ker ^ n).ideal U = (f.ker.ideal U) ^ n :=
        congrFun (Scheme.IdealSheafData.ideal_pow f.ker n) U
      rw [← Scheme.Hom.ker_apply f U, ← hpow, hf]
      rfl
    have hmap : Ideal.map (Y.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom
        (RingHom.ker f.appTop.hom) ≤ RingHom.ker (f.app U.1).hom :=
      Ideal.map_le_iff_le_comap.mpr fun x hx => mem_ker_app_of_mem_ker_appTop f U hx
    have hle : Ideal.map (Y.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom
        (RingHom.ker f.appTop.hom ^ n) ≤ ⊥ := by
      rw [Ideal.map_pow, ← hbot]
      exact Ideal.pow_right_mono hmap n
    exact hle (Ideal.mem_map_of_mem _ hs)
  refine le_antisymm (fun s hs => ?_) bot_le
  show s = 0
  refine Y.IsSheaf.section_ext (U := op (⊤ : Y.Opens)) ?_
  intro x _
  obtain ⟨V, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨U, le_top, hxU, by rw [map_zero]; exact key ⟨U, hU⟩ s hs⟩

end AlgebraicGeometry.Scheme

end
