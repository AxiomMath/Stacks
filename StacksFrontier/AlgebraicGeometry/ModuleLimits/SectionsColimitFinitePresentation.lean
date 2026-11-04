module

public import StacksFrontier.AlgebraicGeometry.AmpleLimit.Unconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 01Z0 for a module of finite presentation on the base stage

Stacks 01Z0 reads: in the situation of Stacks 086P — a directed inverse system of quasi-compact
and quasi-separated schemes `Sᵢ` with affine transition morphisms, with limit `S = lim Sᵢ` and a
chosen base index `0` — for `ℱ₀` a **quasi-coherent** module on `S₀`, writing `ℱᵢ = f_{i0}⁺ℱ₀`
for `i ≥ 0` and `ℱ = f_0⁺ℱ₀`, one has `Γ(S, ℱ) = colim_{i ≥ 0} Γ(Sᵢ, ℱᵢ)`.

**This file proves that for `ℱ₀` of finite presentation.**  The colimit assertion is stated in the
elementwise form `Stacks.IsStagesColimit` of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/SectionsColimitDescent.lean`, which for a directed
index set is exactly the assertion that `Γ(S, ℱ)` is the filtered colimit of the `Γ(Sᵢ, ℱᵢ)`: the
maps to `Γ(S, ℱ)` are compatible with the transition maps, every global section at the limit comes
from a stage, and two global sections at one stage with the same image at the limit already agree
at a later stage.

## Main definitions

* `AlgebraicGeometry.stagePullbackSectionTransition` is the transition map
  `Γ(Sᵢ, ℱᵢ) → Γ(Sⱼ, ℱⱼ)` for `0 ≤ i ≤ j`: pull the section back along `Sⱼ ⟶ Sᵢ` and read the
  iterated pullback as the pullback along the composite, through
  `Stacks.AlgebraicGeometry.ModuleLimits.canHom`.
* `AlgebraicGeometry.stagePullbackSectionProjection` is the map `Γ(Sᵢ, ℱᵢ) → Γ(S, ℱ)`, defined the
  same way from a chosen cone on the inverse system.

## Main results

* `AlgebraicGeometry.map_homOfLE_op_comp`: the transition morphisms of a directed inverse system
  compose, the index category of a preorder being thin.
* `AlgebraicGeometry.isStagesColimit_stagePullbackSection_of_isFinitePresentation`:
  **Stacks 01Z0 for a module of finite presentation on the base stage.**  This is the declaration
  carrying `@[stacks 01Z0 ...]`, keyed to that restriction.

## Implementation notes

The three clauses come from `StacksFrontier/AlgebraicGeometry/AmpleLimit/Unconditional.lean`: the
cocone law is `Stacks.AlgebraicGeometry.ModuleLimits.sectionsMap_canHom_modulePullbackSection_comp`
and the surjectivity and injectivity halves are
`Stacks.AlgebraicGeometry.ModuleLimits.exists_canonical_section_eq_of_isLimit` and
`...ModuleLimits.exists_canonical_section_eq_of_canonical_section_eq_of_isLimit`.  Both halves read
a global section of a module as a morphism out of the structure sheaf and then quote
[Stacks Project, Tag 01ZR], (2) and (3) respectively; since Tag 01ZR is a statement about finitely
presented modules, that is exactly where the restriction on the coefficients comes from.  The
restriction is removed, by interchanging this colimit with the presentation of a quasi-coherent
module as a filtered colimit of finitely presented ones, in
`StacksFrontier/AlgebraicGeometry/ModuleLimits/SectionsColimitQuasiCoherent.lean`, whose
`AlgebraicGeometry.isStagesColimit_stagePullbackSection_of_isQuasicoherent` is the whole of
Stacks 01Z0.

Those halves are stated for a cofiltered index *category*, so they are applied here to `αᵒᵖ` for
`α` the directed index preorder, with the base index `op 0`.  Two bookkeeping lemmas do the
translation and nothing else: the halves produce a morphism `e` of `αᵒᵖ` where the statement below
names the one attached to an inequality, and since the hom-sets of a preorder category are
subsingletons the two are *equal*, so the translation is a `subst` on a variable rather than a
transport of a section along an isomorphism.  That is why
`exists_stagePullbackSectionProjection_eq_aux` takes the surjectivity clause already packaged as
an existential, with the morphism as a free variable: a section whose type mentions `e` cannot be
generalised over `e` while it sits in the context.

## References

* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 086P](https://stacks.math.columbia.edu/tag/086P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-! ### Stacks 01Z0 for a module of finite presentation on the base stage -/

open Stacks.AlgebraicGeometry.ModuleLimits
open Stacks.SheafOfModules (modulePullbackSection)

variable {α : Type u} [Preorder α] [IsDirected α (· ≤ ·)] [Nonempty α] (E : αᵒᵖ ⥤ Scheme.{u})

omit [IsDirected α fun x1 x2 ↦ x1 ≤ x2] [Nonempty α] in
/-- **The transition morphisms of a directed inverse system of schemes compose.** The transition
morphism `Sⱼ ⟶ Sᵢ` attached to `i ≤ j` followed by the transition morphism `Sᵢ ⟶ S₀` attached to
`0 ≤ i` is the transition morphism `Sⱼ ⟶ S₀` attached to `0 ≤ j`: the index category of a
preorder is thin, so the two morphisms of `αᵒᵖ` being compared are equal. -/
theorem map_homOfLE_op_comp {a₀ a b : α} (ha : a₀ ≤ a) (hb : a₀ ≤ b) (hab : a ≤ b) :
    E.map (homOfLE hab).op ≫ E.map (homOfLE ha).op = E.map (homOfLE hb).op := by
  rw [← E.map_comp]
  exact congrArg E.map (Subsingleton.elim _ _)

/-- **The transition map `Γ(Sᵢ, ℱᵢ) ⟶ Γ(Sⱼ, ℱⱼ)` of Stacks 01Z0.** For `ℱ₀` a module on the base
stage `S₀` of a directed inverse system of schemes, `ℱᵢ = f_{i0}⁺ℱ₀` and `0 ≤ i ≤ j`, this pulls a
global section of `ℱᵢ` back along `Sⱼ ⟶ Sᵢ` and reads the resulting iterated pullback as the
pullback along the composite, through
`Stacks.AlgebraicGeometry.ModuleLimits.canHom`. -/
def stagePullbackSectionTransition {a₀ a b : α} (ha : a₀ ≤ a) (hb : a₀ ≤ b) (hab : a ≤ b)
    (F₀ : (E.obj (op a₀)).Modules) :
    ((Scheme.Modules.pullback (E.map (homOfLE ha).op)).obj F₀).sections →
      ((Scheme.Modules.pullback (E.map (homOfLE hb).op)).obj F₀).sections :=
  fun x => SheafOfModules.sectionsMap
    (canHom (E.map (homOfLE hab).op) (E.map (homOfLE ha).op) (E.map (homOfLE hb).op)
      (map_homOfLE_op_comp E ha hb hab) F₀)
    (modulePullbackSection (E.map (homOfLE hab).op).toLRSHom _ x)

/-- **The map `Γ(Sᵢ, ℱᵢ) ⟶ Γ(S, ℱ)` of Stacks 01Z0.** For a chosen cone `c` on the inverse system
this pulls a global section of `ℱᵢ = f_{i0}⁺ℱ₀` back along the projection `S ⟶ Sᵢ` and reads the
resulting iterated pullback as the pullback along the projection `S ⟶ S₀`. -/
def stagePullbackSectionProjection {a₀ a : α} (ha : a₀ ≤ a) (F₀ : (E.obj (op a₀)).Modules)
    (c : Cone E) :
    ((Scheme.Modules.pullback (E.map (homOfLE ha).op)).obj F₀).sections →
      ((Scheme.Modules.pullback (c.π.app (op a₀))).obj F₀).sections :=
  fun x => SheafOfModules.sectionsMap
    (canHom (c.π.app (op a)) (E.map (homOfLE ha).op) (c.π.app (op a₀)) (c.w (homOfLE ha).op) F₀)
    (modulePullbackSection (c.π.app (op a)).toLRSHom _ x)

omit [IsDirected α fun x1 x2 ↦ x1 ≤ x2] [Nonempty α] in
/-- The surjectivity clause, with the transition morphism of the inverse system replaced by the
one attached to the inequality it realises.  The replacement is an equality of morphisms of
`αᵒᵖ`, so it is performed by `subst` on a variable rather than by transporting a section. -/
private theorem exists_stagePullbackSectionProjection_eq_aux {a₀ k : α} (hk : a₀ ≤ k)
    (c : Cone E) (F₀ : (E.obj (op a₀)).Modules) (e : op k ⟶ op a₀)
    (t : ((Scheme.Modules.pullback (c.π.app (op a₀))).obj F₀).sections)
    (h : ∃ x : ((Scheme.Modules.pullback (E.map e)).obj F₀).sections,
      SheafOfModules.sectionsMap
          (canHom (c.π.app (op k)) (E.map e) (c.π.app (op a₀)) (c.w e) F₀)
          (modulePullbackSection (c.π.app (op k)).toLRSHom _ x) = t) :
    ∃ x, stagePullbackSectionProjection E hk F₀ c x = t := by
  obtain rfl : e = (homOfLE hk).op := Subsingleton.elim _ _
  exact h

omit [IsDirected α fun x1 x2 ↦ x1 ≤ x2] [Nonempty α] in
/-- The injectivity clause, with the transition morphism of the inverse system replaced by the
one attached to the inequality it realises, and with the composite chosen to be the transition
morphism to the base stage. -/
private theorem stagePullbackSectionTransition_eq_aux {a₀ a b : α} (ha : a₀ ≤ a) (hb : a₀ ≤ b)
    (hab : a ≤ b) (F₀ : (E.obj (op a₀)).Modules) (g : op b ⟶ op a)
    (x y : ((Scheme.Modules.pullback (E.map (homOfLE ha).op)).obj F₀).sections)
    (h : ∀ (f : op b ⟶ op a₀) (w : E.map g ≫ E.map (homOfLE ha).op = E.map f),
      SheafOfModules.sectionsMap (canHom (E.map g) (E.map (homOfLE ha).op) (E.map f) w F₀)
            (modulePullbackSection (E.map g).toLRSHom _ x)
          = SheafOfModules.sectionsMap (canHom (E.map g) (E.map (homOfLE ha).op) (E.map f) w F₀)
            (modulePullbackSection (E.map g).toLRSHom _ y)) :
    stagePullbackSectionTransition E ha hb hab F₀ x
      = stagePullbackSectionTransition E ha hb hab F₀ y := by
  obtain rfl : g = (homOfLE hab).op := Subsingleton.elim _ _
  exact h (homOfLE hb).op (map_homOfLE_op_comp E ha hb hab)

/-- **[Stacks Project, Tag 01Z0] for a module of finite presentation on the base stage.** Let
`E` be a directed inverse system of quasi-compact and quasi-separated schemes with affine
transition morphisms, let `c` be a limit cone on it, let `0` be a chosen index and let `ℱ₀` be a
module of **finite presentation** on `S₀ = E.obj (op 0)`.  Setting `ℱᵢ = f_{i0}⁺ℱ₀` for `i ≥ 0`
and `ℱ = f_0⁺ℱ₀`, the group `Γ(S, ℱ)` is the filtered colimit of the `Γ(Sᵢ, ℱᵢ)`, in the
elementwise form `Stacks.IsStagesColimit`: the maps to `Γ(S, ℱ)` are compatible with the
transition maps, every global section at the limit comes from a stage, and two global sections at
one stage with the same image at the limit already agree at a later stage.

The three clauses are, in order,
`Stacks.AlgebraicGeometry.ModuleLimits.sectionsMap_canHom_modulePullbackSection_comp`,
`Stacks.AlgebraicGeometry.ModuleLimits.exists_canonical_section_eq_of_isLimit` and
`...ModuleLimits.exists_canonical_section_eq_of_canonical_section_eq_of_isLimit`
— the cocone law for the canonical identification of an iterated pullback with the pullback along
the composite, and the surjectivity and injectivity halves, both of which read a global section
of a module as a morphism out of the structure sheaf and then apply [Stacks Project, Tag 01ZR],
(2) and (3) respectively.  That is why the coefficients are restricted to a module of finite
presentation: Tag 01ZR is a statement about finitely presented modules.

The tag is keyed because this is only part of Stacks 01Z0: the coefficient module is of finite
presentation and not merely quasi-coherent.  The whole tag is
`AlgebraicGeometry.isStagesColimit_stagePullbackSection_of_isQuasicoherent` in
`StacksFrontier/AlgebraicGeometry/ModuleLimits/SectionsColimitQuasiCoherent.lean`, which is this
statement interchanged with [Stacks Project, Tag 01PJ].  The index set lies in the universe of
the schemes, which is not a restriction that may be dropped —
`Stacks.LimitSectionsIdentification.not_card_01Z0` refutes the statement over an index set one
universe up. -/
@[stacks 01Z0 "for a module of finite presentation on the base stage, with the index set in the \
universe of the schemes", ega "IV 8.5.2" "(i), special case", ega "IV 8.5.4" "special case"]
theorem isStagesColimit_stagePullbackSection_of_isFinitePresentation
    [∀ {i j : αᵒᵖ} (f : i ⟶ j), IsAffineHom (E.map f)]
    [∀ i : αᵒᵖ, CompactSpace (E.obj i)] [∀ i : αᵒᵖ, QuasiSeparatedSpace (E.obj i)]
    (c : Cone E) (hc : IsLimit c) (a₀ : α) (F₀ : (E.obj (op a₀)).Modules)
    (hF₀ : F₀.IsFinitePresentation) :
    Stacks.IsStagesColimit
      (fun (a b : {a : α // a₀ ≤ a}) (h : a ≤ b) =>
        stagePullbackSectionTransition E a.2 b.2 (Subtype.coe_le_coe.mpr h) F₀)
      (fun a : {a : α // a₀ ≤ a} => stagePullbackSectionProjection E a.2 F₀ c) where
  ι_trans a b h x :=
    sectionsMap_canHom_modulePullbackSection_comp (c.π.app (op b.1))
      (E.map (homOfLE (Subtype.coe_le_coe.mpr h)).op) (E.map (homOfLE a.2).op)
      (c.π.app (op a.1)) (c.w (homOfLE (Subtype.coe_le_coe.mpr h)).op)
      (E.map (homOfLE b.2).op) (map_homOfLE_op_comp E a.2 b.2 (Subtype.coe_le_coe.mpr h))
      (c.π.app (op a₀)) (c.w (homOfLE a.2).op) (c.w (homOfLE b.2).op) F₀ x
  exists_stage t := by
    obtain ⟨k, e, t', ht⟩ := exists_canonical_section_eq_of_isLimit E c hc (op a₀) F₀ hF₀ t
    obtain ⟨k⟩ := k
    exact ⟨⟨k, leOfHom e.unop⟩,
      exists_stagePullbackSectionProjection_eq_aux E (leOfHom e.unop) c F₀ e t ⟨t', ht⟩⟩
  exists_trans_eq a x y hxy := by
    obtain ⟨l, g, hg⟩ := exists_canonical_section_eq_of_canonical_section_eq_of_isLimit E c hc
      (op a₀) F₀ hF₀ (op a.1) (homOfLE a.2).op x y hxy
    obtain ⟨l⟩ := l
    exact ⟨⟨l, a.2.trans (leOfHom g.unop)⟩, Subtype.coe_le_coe.mp (leOfHom g.unop),
      stagePullbackSectionTransition_eq_aux E a.2 (a.2.trans (leOfHom g.unop))
        (leOfHom g.unop) F₀ g x y hg⟩

end AlgebraicGeometry

end
