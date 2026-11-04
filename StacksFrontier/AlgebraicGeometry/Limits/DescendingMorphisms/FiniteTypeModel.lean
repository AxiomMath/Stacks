module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.NoetherianSystem
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit

/-!
# Finite type models over a limit of Noetherian schemes

Let `S = lim S_i` be the limit of a directed inverse system of Noetherian schemes with affine
transition morphisms, and let `X ⟶ S` be quasi-separated and of finite type. The Stacks project
attaches to this situation a diagram

```
X ⟶ W
↓    ↓
S ⟶ S_i
```

in which `W ⟶ S_i` is of finite type and the induced morphism `X ⟶ S ×_{S_i} W` is a closed
immersion. This file introduces that diagram as a bundled structure and provides the basic
geometric facts about the limit situation which the consumers of the diagram need.

## Main definitions

* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram` is the diagram above, bundling the
  stage `i`, the model `W ⟶ S_i`, the morphism `X ⟶ W`, the commutativity of the square, the
  finite-type properties of the model and the closed-immersion property of the induced morphism.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.induced` is the induced morphism
  `X ⟶ S ×_{S_i} W`.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.isAffineHom_π`: every projection `S ⟶ S_i` of the
  limit is affine.
* `AlgebraicGeometry.LimitNoetherianSituation.compactSpace_limitScheme` and
  `AlgebraicGeometry.LimitNoetherianSituation.quasiSeparatedSpace_limitScheme`: the limit scheme
  is quasi-compact and quasi-separated.
* `AlgebraicGeometry.LimitNoetherianSituation.compactSpace_of_quasiCompact_toLimitScheme` and
  `AlgebraicGeometry.LimitNoetherianSituation.quasiSeparatedSpace_of_quasiSeparated_toLimitScheme`:
  a scheme quasi-compact, respectively quasi-separated, over the limit is itself so.
* `AlgebraicGeometry.LimitNoetherianSituation.nonempty_goodDiagram_of_isClosedImmersion`: a closed
  immersion of `X` into the base change of a finite-type model, compatible with `f`, is the same
  data as a good diagram.

## Implementation notes

The transition morphism `S_{i'} ⟶ S_i` for `i ≤ i'` is the image of a morphism of `Iᵒᵖ` under
`AlgebraicGeometry.LimitNoetherianSituation.system`, so the stage attached to a good diagram
enters the types through `Opposite.op`. The fibre product `S ×_{S_i} W` is Mathlib's chosen
pullback and the induced morphism is `CategoryTheory.Limits.pullback.lift` applied to the
commuting square. Finite type is expressed, as in Tag 01T1, by `LocallyOfFiniteType` together
with `QuasiCompact`.

The index type of the system lives at a universe independent of the universe of the schemes. The
geometric facts about the limit are therefore taken from
`StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit`, the restatement of
Mathlib's `Mathlib.AlgebraicGeometry.AffineTransitionLimit` at an independent index universe,
rather than from Mathlib directly. The only smallness hypothesis they need is
`CategoryTheory.EssentiallySmall` of the index type relative to the scheme universe: local
smallness is automatic because a preorder is a thin category, and initial smallness follows from
essential smallness. No identification of the two universes and no `Small` instance on the index
type is required.

The structure `GoodDiagram` itself needs no hypothesis on the index type at all.

## References

* [Stacks Project, Tag 0CNM](https://stacks.math.columbia.edu/tag/0CNM)
* [Stacks Project, Tag 0CNN](https://stacks.math.columbia.edu/tag/0CNN)
* [Stacks Project, Tag 0CNP](https://stacks.math.columbia.edu/tag/0CNP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

namespace LimitNoetherianSituation

section Situation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : LimitNoetherianSituation.{v, u} I)

/-- The transition morphisms of a limit-Noetherian situation are affine. -/
instance isAffineHom_system_map {i j : Iᵒᵖ} (g : i ⟶ j) : IsAffineHom (D.system.map g) :=
  D.transition_affine g

/-- Every scheme of a limit-Noetherian situation is Noetherian. -/
instance isNoetherian_system_obj (i : Iᵒᵖ) : IsNoetherian (D.system.obj i) :=
  D.noetherian i.unop

/-- Every projection `S ⟶ S_i` out of the limit of a limit-Noetherian situation is affine. -/
theorem isAffineHom_π [EssentiallySmall.{u} I] (i : Iᵒᵖ) :
    IsAffineHom (D.limitCone.π.app i) := by
  have : InitiallySmall.{u} Iᵒᵖ := initiallySmall_of_essentiallySmall Iᵒᵖ
  exact isAffineHom_π_app_of_initiallySmall D.system D.limitCone D.isLimit i

/-- The limit of a limit-Noetherian situation is quasi-compact. -/
theorem compactSpace_limitScheme [EssentiallySmall.{u} I] : CompactSpace D.limitScheme := by
  have : InitiallySmall.{u} Iᵒᵖ := initiallySmall_of_essentiallySmall Iᵒᵖ
  exact Scheme.compactSpace_of_isLimit_of_initiallySmall D.system D.limitCone D.isLimit

/-- The limit of a limit-Noetherian situation is quasi-separated. -/
theorem quasiSeparatedSpace_limitScheme [EssentiallySmall.{u} I] :
    QuasiSeparatedSpace D.limitScheme := by
  obtain ⟨i⟩ : Nonempty Iᵒᵖ := inferInstance
  have hπ : IsAffineHom (D.limitCone.π.app i) := D.isAffineHom_π i
  have : QuasiSeparated (D.limitCone.π.app i ≫ terminal.from (D.system.obj i)) :=
    inferInstance
  refine (quasiSeparatedSpace_iff_quasiSeparated D.limitScheme).2 ?_
  simpa using this

/-- A scheme quasi-compact over the limit of a limit-Noetherian situation is quasi-compact. -/
theorem compactSpace_of_quasiCompact_toLimitScheme [EssentiallySmall.{u} I] {X : Scheme.{u}}
    (f : X ⟶ D.limitScheme) [QuasiCompact f] : CompactSpace X :=
  have := D.compactSpace_limitScheme
  QuasiCompact.compactSpace_of_compactSpace f

/-- A scheme quasi-separated over the limit of a limit-Noetherian situation is
quasi-separated. -/
theorem quasiSeparatedSpace_of_quasiSeparated_toLimitScheme [EssentiallySmall.{u} I]
    {X : Scheme.{u}} (f : X ⟶ D.limitScheme) [QuasiSeparated f] : QuasiSeparatedSpace X :=
  have := D.quasiSeparatedSpace_limitScheme
  AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated f

end Situation

/-- **Stacks Project, Tag 0CNP.** A diagram `X ⟶ W ⟶ S_i` over `S ⟶ S_i` in which `W ⟶ S_i`
is of finite type and the induced map `X ⟶ S ×_{S_i} W` is a closed immersion. Stacks 0CNN
asserts that such a diagram exists for every quasi-separated `X ⟶ S` of finite type. -/
structure GoodDiagram {I : Type v} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : LimitNoetherianSituation.{v, u} I)
    {X : Scheme.{u}} (f : X ⟶ D.limitScheme) where
  /-- The stage `i` over which the model is defined. -/
  index : I
  /-- The finite-type model over `S_i`. -/
  W : Scheme.{u}
  /-- The structure morphism `W ⟶ S_i`. -/
  modelMap : W ⟶ D.system.obj (op index)
  /-- The horizontal morphism `X ⟶ W`. -/
  toModel : X ⟶ W
  /-- The square with vertical maps `f` and `modelMap` commutes. -/
  commutes : f ≫ D.limitCone.π.app (op index) = toModel ≫ modelMap
  /-- The model is locally of finite type over `S_i`. -/
  locallyOfFiniteType : LocallyOfFiniteType modelMap
  /-- The model morphism is quasi-compact, so it is of finite type. -/
  quasiCompact : QuasiCompact modelMap
  /-- The induced morphism from `X` to the base change of the model is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion (pullback.lift f toModel commutes)

namespace GoodDiagram

/-- The morphism `X ⟶ S ×_{S_i} W` induced by a good diagram. -/
noncomputable abbrev induced {I : Type v} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] {D : LimitNoetherianSituation.{v, u} I}
    {X : Scheme.{u}} {f : X ⟶ D.limitScheme} (G : GoodDiagram D f) :
    X ⟶ pullback (D.limitCone.π.app (op G.index)) G.modelMap :=
  pullback.lift f G.toModel G.commutes

end GoodDiagram

section Construction

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : LimitNoetherianSituation.{v, u} I) {X : Scheme.{u}} {f : X ⟶ D.limitScheme}

/-- A closed immersion of `X` into the base change of a finite-type model over a stage of the
system, compatible with `f`, yields a good diagram. -/
theorem nonempty_goodDiagram_of_isClosedImmersion (j : I) {W : Scheme.{u}}
    (w : W ⟶ D.system.obj (op j)) (hw₁ : LocallyOfFiniteType w) (hw₂ : QuasiCompact w)
    (g : X ⟶ pullback (D.limitCone.π.app (op j)) w) (hg : IsClosedImmersion g)
    (hgf : g ≫ pullback.fst (D.limitCone.π.app (op j)) w = f) :
    Nonempty (GoodDiagram D f) := by
  have hcomm : f ≫ D.limitCone.π.app (op j) =
      (g ≫ pullback.snd (D.limitCone.π.app (op j)) w) ≫ w := by
    rw [← hgf, Category.assoc, Category.assoc, pullback.condition]
  have hlift : pullback.lift f (g ≫ pullback.snd (D.limitCone.π.app (op j)) w) hcomm = g := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hgf]
    · rw [pullback.lift_snd]
  refine ⟨⟨j, W, w, g ≫ pullback.snd _ _, hcomm, hw₁, hw₂, ?_⟩⟩
  rw [hlift]
  exact hg

/-- The reduction of Stacks Tag 0CNN to its two inputs: Tag 01ZG, which embeds `X` as a closed
subscheme of a scheme of finite presentation over the limit, and part (1) of Tag 01ZM, which
descends that scheme to a finite stage of the system.

This is the argument of the Stacks proof of Tag 0CNN; the two inputs are hypotheses because
neither is available yet. It is **not** a proof of Tag 0CNN and carries no tag. -/
theorem nonempty_goodDiagram_of_exists_model
    (h01ZG : ∃ (X' : Scheme.{u}) (p : X' ⟶ D.limitScheme) (ι : X ⟶ X'),
      FinitePresentation p ∧ IsClosedImmersion ι ∧ ι ≫ p = f)
    (h01ZM : ∀ (X' : Scheme.{u}) (p : X' ⟶ D.limitScheme), FinitePresentation p →
      ∃ (j : I) (W : Scheme.{u}) (w : W ⟶ D.system.obj (op j)) (_ : FinitePresentation w)
        (e : X' ≅ pullback (D.limitCone.π.app (op j)) w),
        e.hom ≫ pullback.fst (D.limitCone.π.app (op j)) w = p) :
    Nonempty (GoodDiagram D f) := by
  obtain ⟨X', p, ι, hp, hι, hιp⟩ := h01ZG
  obtain ⟨j, W, w, hw, e, he⟩ := h01ZM X' p hp
  have hw₁ : LocallyOfFiniteType w :=
    have := hw.locallyOfFinitePresentation
    inferInstance
  refine nonempty_goodDiagram_of_isClosedImmersion D j w hw₁ hw.quasiCompact (ι ≫ e.hom) ?_ ?_
  · have : IsClosedImmersion ι := hι
    have : IsIso e.hom := inferInstance
    infer_instance
  · rw [Category.assoc, he, hιp]

end Construction

end LimitNoetherianSituation

end AlgebraicGeometry
