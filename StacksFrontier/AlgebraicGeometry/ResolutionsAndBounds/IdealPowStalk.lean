module

public import StacksFrontier.AlgebraicGeometry.Scheme.AffineOpenNeighborhood
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk

/-!
# The stalk of a subsheaf of the structure sheaf, and the stalk of `Iⁿ`

Let `X` be a scheme and `N ⊆ 𝒪_X` a subsheaf of the structure sheaf, viewed as a submodule of
`𝒪_X` over itself. Its sections over any open are an ideal of the sections of `𝒪_X` there, and
the germs at a point `x` of all those sections form an ideal `germIdeal N x` of the local ring
`𝒪_{X,x}`: the set of germs is closed under addition because two sections can be restricted to
the intersection of their domains, and under multiplication by an arbitrary element of the local
ring because that element is itself the germ of a section.

For the subsheaf `Iⁿ ⊆ 𝒪_X` cut out by a power of a quasi-coherent sheaf of ideals, that ideal
of germs is the stalk of the ideal sheaf `Iⁿ` in the sense of
`AlgebraicGeometry.IdealSheafData.stalk`. So an element of the local ring lies in `(Iⁿ)_x`
exactly when it is the germ of a section of `Iⁿ` on some neighbourhood of `x`, which is the
form in which a membership statement about the stalk of `Iⁿ` can be fed a section and can
produce one.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPowerColimit.germIdeal`: the ideal of germs at a point of the
  sections of a subsheaf of the structure sheaf.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.germIdeal_idealPowerMultiple`: the ideal of germs
  of the sections of `Iⁿ ⊆ 𝒪_X` is the stalk of the ideal sheaf `Iⁿ`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.mem_stalk_pow_iff`: membership in the stalk of
  `Iⁿ` is being the germ of a section of `Iⁿ`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.germ_mem_stalk_pow` and
  `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_section_idealPow_germ_eq`: the two halves
  of that equivalence, stated with sections of the sheaf of modules `Iⁿ` rather than with
  sections of `𝒪_X` subject to a membership condition.

## Implementation notes

The ideal of germs is defined over an arbitrary subsheaf of the structure sheaf rather than over
`Iⁿ` alone: its three closure properties use nothing about `Iⁿ`, only that the sections form a
submodule on each open and are stable under restriction.

Both inclusions in `germIdeal_idealPowerMultiple` go through a single affine open containing the
point, via `AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ` and
`Stacks.AlgebraicGeometry.IdealPowerColimit.obj_idealPow_affineOpen_eq_ideal_pow`; the
containment of the germ ideal in the stalk needs the given open to be shrunk to an affine one,
which is where stability of the sections of `Iⁿ` under restriction is used.

This stays with the germ maps of the structure sheaf, which take values in the `CommRingCat`
stalk `X.presheaf.stalk x` where `AlgebraicGeometry.IdealSheafData.stalk` lives. The stalk of
`Iⁿ` *as a sheaf of modules* is instead the colimit `TopCat.Presheaf.stalk (idealPow I n).val`
taken in `AddCommGrpCat`, a module over the `RingCat` stalk of `X.ringCatSheaf`, and the two
local rings are a comparison isomorphism apart; stating the result in germs avoids that
comparison without weakening it, since a germ determines and is determined by a section on a
neighbourhood.

## References

* [Stacks Project, Tag 0FZ0](https://stacks.math.columbia.edu/tag/0FZ0)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPower

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-- **The germs of the sections of a subsheaf of the structure sheaf**, as an ideal of the local
ring at a point. An element of `𝒪_{X,x}` belongs to it exactly when it is the germ of a section
of `N` on some open neighbourhood of `x`. -/
noncomputable def germIdeal (N : (structureModule X).Submodule) (x : X) :
    Ideal (X.presheaf.stalk x) where
  carrier := {a | ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(X, U)),
    s ∈ N.toSubmodule.obj (op U) ∧ (X.presheaf.germ U x hx).hom s = a}
  zero_mem' := ⟨⊤, trivial, 0, Submodule.zero_mem _, map_zero _⟩
  add_mem' := by
    rintro a b ⟨U, hxU, s, hs, rfl⟩ ⟨V, hxV, t, ht, rfl⟩
    refine ⟨U ⊓ V, ⟨hxU, hxV⟩, X.presheaf.map (homOfLE inf_le_left).op s +
      X.presheaf.map (homOfLE inf_le_right).op t,
      Submodule.add_mem _ (N.toSubmodule.map_mem _ hs) (N.toSubmodule.map_mem _ ht), ?_⟩
    rw [map_add]
    exact congrArg₂ (· + ·)
      (X.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ V ≤ U)) x ⟨hxU, hxV⟩ s)
      (X.presheaf.germ_res_apply (homOfLE (inf_le_right : U ⊓ V ≤ V)) x ⟨hxU, hxV⟩ t)
  smul_mem' := by
    rintro c a ⟨U, hxU, s, hs, rfl⟩
    obtain ⟨V, hVU, hxV, d, hd⟩ := X.presheaf.exists_le_germ_eq c hxU
    refine ⟨V, hxV, d * X.presheaf.map (homOfLE hVU).op s,
      Submodule.smul_mem _ d (N.toSubmodule.map_mem _ hs), ?_⟩
    rw [map_mul, hd, X.presheaf.germ_res_apply (homOfLE hVU) x hxV s]
    rfl

/-- The germ of a section of a subsheaf of the structure sheaf lies in the ideal of germs. -/
theorem germ_mem_germIdeal (N : (structureModule X).Submodule) (x : X) (U : X.Opens)
    (hx : x ∈ U) (s : Γ(X, U)) (hs : s ∈ N.toSubmodule.obj (op U)) :
    (X.presheaf.germ U x hx).hom s ∈ germIdeal N x :=
  ⟨U, hx, s, hs, rfl⟩

/-- Every element of the ideal of germs of a subsheaf of the structure sheaf is the germ of a
section of that subsheaf. -/
theorem exists_section_germ_eq {N : (structureModule X).Submodule} {x : X}
    {a : X.presheaf.stalk x} (ha : a ∈ germIdeal N x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(X, U)),
      s ∈ N.toSubmodule.obj (op U) ∧ (X.presheaf.germ U x hx).hom s = a := ha

/-- **The germs of the sections of `Iⁿ ⊆ 𝒪_X` are the stalk of the ideal sheaf `Iⁿ`.** -/
theorem germIdeal_idealPowerMultiple (I : X.IdealSheafData) (n : ℕ) (x : X) :
    germIdeal (idealPowerMultiple I n (structureModule X)) x =
      AlgebraicGeometry.IdealSheafData.stalk (I ^ n) x := by
  refine le_antisymm ?_ ?_
  · rintro a ⟨U, hxU, s, hs, rfl⟩
    obtain ⟨V, hxV, hVU⟩ := exists_affineOpen_mem_le x U hxU
    have hres : X.presheaf.map (homOfLE hVU).op s ∈ ((I ^ n).ideal V : Ideal Γ(X, V.1)) := by
      rw [← obj_idealPow_affineOpen_eq_ideal_pow I n V]
      exact (idealPowerMultiple I n (structureModule X)).toSubmodule.map_mem _ hs
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ x V hxV,
      ← X.presheaf.germ_res_apply (homOfLE hVU) x hxV s]
    exact Ideal.mem_map_of_mem _ hres
  · obtain ⟨V, hxV⟩ := exists_affineOpen_mem_le x ⊤ trivial |>.imp fun _ h ↦ h.1
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ x V hxV, Ideal.map_le_iff_le_comap]
    intro b hb
    refine germ_mem_germIdeal _ x V.1 hxV b ?_
    rw [obj_idealPow_affineOpen_eq_ideal_pow I n V]
    exact hb

/-- **Membership in the stalk of `Iⁿ` is being the germ of a section of `Iⁿ`.** -/
theorem mem_stalk_pow_iff (I : X.IdealSheafData) (n : ℕ) (x : X) (a : X.presheaf.stalk x) :
    a ∈ AlgebraicGeometry.IdealSheafData.stalk (I ^ n) x ↔
      ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(X, U)),
        s ∈ (idealPowerMultiple I n (structureModule X)).toSubmodule.obj (op U) ∧
          (X.presheaf.germ U x hx).hom s = a := by
  rw [← germIdeal_idealPowerMultiple I n x]
  exact Iff.rfl

/-- **The germ of a section of the sheaf of modules `Iⁿ` lies in the stalk of the ideal sheaf
`Iⁿ`.** -/
theorem germ_mem_stalk_pow (I : X.IdealSheafData) (n : ℕ) (U : X.Opens) (x : X) (hx : x ∈ U)
    (s : Γ(idealPow I n, U)) :
    (X.presheaf.germ U x hx).hom (s.1 : Γ(X, U)) ∈
      AlgebraicGeometry.IdealSheafData.stalk (I ^ n) x :=
  (mem_stalk_pow_iff I n x _).2 ⟨U, hx, s.1, s.2, rfl⟩

/-- **Every element of the stalk of the ideal sheaf `Iⁿ` is the germ of a section of the sheaf
of modules `Iⁿ`.** -/
theorem exists_section_idealPow_germ_eq (I : X.IdealSheafData) (n : ℕ) (x : X)
    {a : X.presheaf.stalk x} (ha : a ∈ AlgebraicGeometry.IdealSheafData.stalk (I ^ n) x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(idealPow I n, U)),
      (X.presheaf.germ U x hx).hom (s.1 : Γ(X, U)) = a := by
  obtain ⟨U, hx, s, hs, hgerm⟩ := (mem_stalk_pow_iff I n x a).1 ha
  exact ⟨U, hx, ⟨s, hs⟩, hgerm⟩

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
