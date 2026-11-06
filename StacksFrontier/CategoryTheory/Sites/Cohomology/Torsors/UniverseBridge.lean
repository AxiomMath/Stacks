module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.CategoryOfTorsors

/-!
# Carrying a torsor across universes and along an identification of the acting group

A pseudo-torsor of Stacks 03AH records two universes independently: the universe `w` of the
sections of the sheaf of groups that acts, and the universe `t` of the sections of the sheaf it
acts on. Two renderings of the same torsor can therefore differ in both, and a comparison
between them needs to move a pseudo-torsor in each of the two directions separately.

This file provides the two moves.

* `PseudoTorsor.uliftSections` lifts the sections of the underlying sheaf along
  `CategoryTheory.uliftFunctor`, leaving the acting sheaf of groups alone. The sheaf condition
  survives because `CategoryTheory.Presieve.isSheaf_comp_uliftFunctor_iff` is a biconditional,
  and simple transitivity survives because `Equiv.ulift` is a bijection.
* `PseudoTorsor.transport` replaces the acting sheaf of groups by another one whose sections are
  identified with its own, leaving the underlying sheaf alone. The identification is
  `SheafOfGroups.SectionEquiv`: a bijection on sections over every object which is multiplicative
  and compatible with the restriction maps. Its source and target universes are independent, so
  this is where a change in the universe of the *group* is absorbed.

Composing the two is `PseudoTorsor.bridge`, and `SheafOfGroups.Torsors.bridge` is the same move
on an object of the category `𝒢-Torsors` of Stacks 04UJ.

## Main definitions

* `SheafOfGroups.SectionEquiv`: a multiplicative, restriction-compatible bijection between the
  sections of two sheaves of groups on the same site, whose section universes may differ.
* `PseudoTorsor.transport`: a pseudo-torsor read as one under an identified sheaf of groups.
* `PseudoTorsor.uliftSections`: a pseudo-torsor with its sections lifted to a larger universe.
* `PseudoTorsor.bridge` and `SheafOfGroups.Torsors.bridge`: the two moves at once.

## Main results

* `PseudoTorsor.transport_isTorsor` and `PseudoTorsor.uliftSections_isTorsor`: both moves
  preserve local nonemptiness, so they carry torsors to torsors.

## Implementation notes

`SheafOfGroups.SectionEquiv` is not a morphism of sheaves of groups, since its two sides have
sections in different universes and a natural transformation between presheaves of different
value universes does not typecheck; it is the bijection on sections together with the two
equations a morphism of sheaves of groups would satisfy. Multiplicativity is required and
`SheafOfGroups.SectionEquiv.map_one` is derived from it, as it is for a monoid homomorphism
between groups.

`PseudoTorsor.transport` takes the identification *into* the group that already acts, so that
the new action is the old one read on translated sections and no inverse is applied; the
inverse direction is `SheafOfGroups.SectionEquiv.symm`.

Local nonemptiness depends on the underlying sheaf alone, so `PseudoTorsor.transport` preserves
it by definition.

## References

* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
* [Stacks Project, Tag 04UJ](https://stacks.math.columbia.edu/tag/04UJ)
-/

@[expose] public section

open CategoryTheory Opposite

universe t₂ t₁ w₂ w₁ v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-! ### Identifying the sections of two sheaves of groups -/

/-- An identification of two sheaves of groups on one site: a bijection between their sections
over every object which is multiplicative and compatible with the restriction maps.

The section universes of the two sides are independent, so this is *not* an isomorphism of
presheaves — such a morphism does not typecheck across universes — but exactly the data a
sectionwise isomorphism of sheaves of groups carries. -/
structure SheafOfGroups.SectionEquiv (𝒢 : SheafOfGroups.{w₁} (C := C) J)
    (ℋ : SheafOfGroups.{w₂} (C := C) J) where
  /-- The bijection on sections over an object. -/
  equiv : ∀ V : Cᵒᵖ, 𝒢.presheaf.obj V ≃ ℋ.presheaf.obj V
  /-- The bijection is multiplicative. -/
  map_mul : ∀ (V : Cᵒᵖ) (g h : 𝒢.presheaf.obj V), equiv V (g * h) = equiv V g * equiv V h
  /-- The bijection is compatible with the restriction maps. -/
  naturality : ∀ {V W : Cᵒᵖ} (f : V ⟶ W) (g : 𝒢.presheaf.obj V),
    equiv W (𝒢.presheaf.map f g) = ℋ.presheaf.map f (equiv V g)

namespace SheafOfGroups.SectionEquiv

variable {𝒢 : SheafOfGroups.{w₁} (C := C) J} {ℋ : SheafOfGroups.{w₂} (C := C) J}

/-- An identification of sheaves of groups carries the identity section to the identity
section: a multiplicative map between groups is a monoid homomorphism. -/
theorem map_one (e : SectionEquiv 𝒢 ℋ) (V : Cᵒᵖ) : e.equiv V 1 = 1 := by
  have h : e.equiv V 1 * e.equiv V 1 = e.equiv V 1 * 1 := by
    rw [mul_one, ← e.map_mul, one_mul]
  exact mul_left_cancel h

/-- The identification read in the other direction. -/
def symm (e : SectionEquiv 𝒢 ℋ) : SectionEquiv ℋ 𝒢 where
  equiv V := (e.equiv V).symm
  map_mul V g h := by
    apply (e.equiv V).injective
    rw [Equiv.apply_symm_apply, e.map_mul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  naturality {V W} f g := by
    apply (e.equiv W).injective
    rw [Equiv.apply_symm_apply, e.naturality, Equiv.apply_symm_apply]

end SheafOfGroups.SectionEquiv

/-! ### Reading a pseudo-torsor under an identified sheaf of groups -/

namespace PseudoTorsor

variable {𝒢 : SheafOfGroups.{w₁} (C := C) J} {ℋ : SheafOfGroups.{w₂} (C := C) J}

/-- A pseudo-torsor under `𝒢`, read as a pseudo-torsor under a sheaf of groups `ℋ` whose
sections are identified with those of `𝒢`: a section of `ℋ` acts as the section of `𝒢` it is
identified with. The underlying sheaf, and hence the universe of its sections, is unchanged. -/
def transport (F : PseudoTorsor.{t₁} 𝒢) (e : SheafOfGroups.SectionEquiv ℋ 𝒢) :
    PseudoTorsor.{t₁} ℋ where
  presheaf := F.presheaf
  isSheaf := F.isSheaf
  act V g s := F.act V (e.equiv V g) s
  one_act V s := by rw [e.map_one, F.one_act]
  mul_act V g h s := by rw [e.map_mul, F.mul_act]
  naturality {V W} f g s := by rw [F.naturality, e.naturality]
  simplyTransitive V hne s t := by
    obtain ⟨g, hg, hu⟩ := F.simplyTransitive V hne s t
    refine ⟨(e.equiv V).symm g, ?_, ?_⟩
    · change F.act V (e.equiv V ((e.equiv V).symm g)) s = t
      rw [Equiv.apply_symm_apply]
      exact hg
    · intro y hy
      exact (Equiv.eq_symm_apply _).2 (hu _ hy)

/-- The underlying presheaf of a transported pseudo-torsor is that of the original. -/
@[simp]
theorem transport_presheaf (F : PseudoTorsor.{t₁} 𝒢) (e : SheafOfGroups.SectionEquiv ℋ 𝒢) :
    (F.transport e).presheaf = F.presheaf :=
  rfl

/-- A section of `ℋ` acts on a transported pseudo-torsor as the section of `𝒢` identified with
it. -/
@[simp]
theorem transport_act (F : PseudoTorsor.{t₁} 𝒢) (e : SheafOfGroups.SectionEquiv ℋ 𝒢)
    (V : Cᵒᵖ) (g : ℋ.presheaf.obj V) (s : F.presheaf.obj V) :
    (F.transport e).act V g s = F.act V (e.equiv V g) s :=
  rfl

/-- Reading a torsor under an identified sheaf of groups gives a torsor: local nonemptiness is
a condition on the underlying sheaf, which is unchanged. -/
theorem transport_isTorsor (F : PseudoTorsor.{t₁} 𝒢) (e : SheafOfGroups.SectionEquiv ℋ 𝒢)
    (hF : F.IsTorsor) : (F.transport e).IsTorsor :=
  hF

/-! ### Lifting the sections of a pseudo-torsor to a larger universe -/

/-- A pseudo-torsor with the sections of its underlying sheaf lifted to a larger universe, the
acting sheaf of groups being unchanged. -/
def uliftSections (F : PseudoTorsor.{t₁} 𝒢) : PseudoTorsor.{max t₁ t₂} 𝒢 where
  presheaf := F.presheaf ⋙ uliftFunctor.{t₂}
  isSheaf := (isSheaf_iff_isSheaf_of_type J _).2
    (Presieve.isSheaf_comp_uliftFunctor J ((isSheaf_iff_isSheaf_of_type J _).1 F.isSheaf))
  act V g s := ULift.up (F.act V g s.down)
  one_act V s := by
    refine ULift.ext ?_
    exact F.one_act V s.down
  mul_act V g h s := by
    refine ULift.ext ?_
    exact F.mul_act V g h s.down
  naturality {V W} f g s := by
    refine ULift.ext ?_
    exact F.naturality f g s.down
  simplyTransitive V hne s t := by
    obtain ⟨g, hg, hu⟩ := F.simplyTransitive V ⟨s.down⟩ s.down t.down
    refine ⟨g, ULift.ext hg, ?_⟩
    intro y hy
    exact hu y (congrArg ULift.down hy)

/-- The underlying presheaf of `F.uliftSections` is that of `F` composed with
`CategoryTheory.uliftFunctor`. -/
@[simp]
theorem uliftSections_presheaf (F : PseudoTorsor.{t₁} 𝒢) :
    (F.uliftSections.{t₂}).presheaf = F.presheaf ⋙ uliftFunctor.{t₂} :=
  rfl

/-- The action on lifted sections is the action on the underlying sections, lifted again. -/
@[simp]
theorem uliftSections_act (F : PseudoTorsor.{t₁} 𝒢) (V : Cᵒᵖ) (g : 𝒢.presheaf.obj V)
    (s : (F.presheaf ⋙ uliftFunctor.{t₂}).obj V) :
    (F.uliftSections.{t₂}).act V g s = ULift.up (F.act V g s.down) :=
  rfl

/-- Lifting the sections of a torsor gives a torsor: a lifted section set is nonempty exactly
when the section set is. -/
theorem uliftSections_isTorsor (F : PseudoTorsor.{t₁} 𝒢) (hF : F.IsTorsor) :
    (F.uliftSections.{t₂}).IsTorsor := by
  intro U
  obtain ⟨S, hS, hne⟩ := hF U
  refine ⟨S, hS, ?_⟩
  intro V f hf
  exact (hne hf).elim fun s => ⟨ULift.up s⟩

/-! ### The two moves at once -/

/-- **The universe bridge for pseudo-torsors.** A pseudo-torsor under `𝒢` with sections in
`Type t₁`, read as a pseudo-torsor under an identified sheaf of groups `ℋ` with sections in the
larger universe `Type (max t₁ t₂)`. Both universes of the rendering are changed: that of the
group by the identification, that of the sections by the lift. -/
def bridge (F : PseudoTorsor.{t₁} 𝒢) (e : SheafOfGroups.SectionEquiv ℋ 𝒢) :
    PseudoTorsor.{max t₁ t₂} ℋ :=
  (F.uliftSections.{t₂}).transport e

/-- The underlying presheaf of `F.bridge e` is that of `F` composed with
`CategoryTheory.uliftFunctor`. -/
@[simp]
theorem bridge_presheaf (F : PseudoTorsor.{t₁} 𝒢) (e : SheafOfGroups.SectionEquiv ℋ 𝒢) :
    (F.bridge.{t₂} e).presheaf = F.presheaf ⋙ uliftFunctor.{t₂} :=
  rfl

/-- A section of `ℋ` acts on a lifted section of `F.bridge e` as the identified section of `𝒢`
acts on the underlying section, lifted again. -/
@[simp]
theorem bridge_act (F : PseudoTorsor.{t₁} 𝒢) (e : SheafOfGroups.SectionEquiv ℋ 𝒢)
    (V : Cᵒᵖ) (g : ℋ.presheaf.obj V) (s : (F.presheaf ⋙ uliftFunctor.{t₂}).obj V) :
    (F.bridge.{t₂} e).act V g s = ULift.up (F.act V (e.equiv V g) s.down) :=
  rfl

/-- The universe bridge carries a torsor to a torsor. -/
theorem bridge_isTorsor (F : PseudoTorsor.{t₁} 𝒢) (e : SheafOfGroups.SectionEquiv ℋ 𝒢)
    (hF : F.IsTorsor) : (F.bridge.{t₂} e).IsTorsor :=
  transport_isTorsor _ e (uliftSections_isTorsor F hF)

end PseudoTorsor

/-! ### The bridge on an object of `𝒢-Torsors` -/

namespace SheafOfGroups.Torsors

/-- **The universe bridge for an object of `𝒢-Torsors`.** An object of the category of torsors
of Stacks 04UJ under a sheaf of groups `𝒢`, read as an object of the category of torsors under
an identified sheaf of groups `ℋ`, with the sections of its torsor lifted to a larger
universe. -/
def bridge {𝒢 : SheafOfGroups.{w₁} (C := C) J} {ℋ : SheafOfGroups.{w₂} (C := C) J}
    (T : Torsors.{t₁} 𝒢) (e : ∀ V : C, SheafOfGroups.SectionEquiv (ℋ.over V) (𝒢.over V)) :
    Torsors.{max t₁ t₂} ℋ where
  base := T.base
  torsor := T.torsor.bridge.{t₂} (e T.base)
  isTorsor := PseudoTorsor.bridge_isTorsor _ _ T.isTorsor

/-- The bridge of an object of `𝒢-Torsors` lives over the same object of the site. -/
@[simp]
theorem bridge_base {𝒢 : SheafOfGroups.{w₁} (C := C) J} {ℋ : SheafOfGroups.{w₂} (C := C) J}
    (T : Torsors.{t₁} 𝒢) (e : ∀ V : C, SheafOfGroups.SectionEquiv (ℋ.over V) (𝒢.over V)) :
    (T.bridge.{t₂} e).base = T.base :=
  rfl

end SheafOfGroups.Torsors

end
