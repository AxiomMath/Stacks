module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestrictionFlatCommute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SyntomicFibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The flat-pullback class of a flat morphism in the completed bivariant group

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
flat morphism of schemes locally of finite type over `S`. The flat-pullback class of
**Stacks 0B78** is attached to a flat morphism of a *fixed* relative dimension `r` and lies in
`A^{-r}(X ⟶ Y)`. When the relative dimension of `f` is only constant on each connected component
`X_a` of `X`, say equal to `r_a` there, the flat pullback `f^*` is an element of the completed
bivariant group `A^*(X ⟶ Y)^∧ = ∏_a A^*(X_a ⟶ Y_{a'})` of Stacks 0FE0: its component on `X_a`
is the class of Stacks 0B78 of the restriction `X_a ⟶ Y_{a'}` of `f`, in degree `-r_a`.

This is the case of a flat local complete intersection morphism (Stacks 069F): such a morphism
is syntomic (Stacks 069K), so its restriction to a connected component of the source is a flat
morphism locally of finite presentation with Cohen–Macaulay fibres (Stacks 045R) and connected
source, which has pure relative dimension (Stacks 02NM). The class `f^*` is then defined with no
further hypothesis; for a smooth morphism it is `Stacks.Chow.completedFlatPullbackOfSmooth`.

## Main definitions

* `Stacks.Chow.flatComponentRelativeDimension` — the relative dimension `r_a` of `f` on the
  connected component `X_a`, for a morphism whose relative dimension is constant on each
  connected component.
* `Stacks.Chow.completedFlatPullback` — **Stacks 0B78** on completions: `f^* ∈ A^*(X ⟶ Y)^∧`.
* `Stacks.Chow.completedFlatPullbackOfFlatLCI` — `f^* ∈ A^*(X ⟶ Y)^∧` for a flat local complete
  intersection morphism `f`.

## Main results

* `Stacks.Chow.completedFlatPullback_apply` — on `X_a` the class `f^*` is the class of
  Stacks 0B78 of the restriction of `f`, placed in degree `-r_a`.
* `Stacks.Chow.completedFlatPullbackOfSmooth_eq_completedFlatPullback` — for a smooth morphism
  this is the class `Stacks.Chow.completedFlatPullbackOfSmooth`.
* `Stacks.Chow.exists_relativeDimension_resConnectedComponent_of_isLocalCompleteIntersection` —
  a flat local complete intersection morphism has pure relative dimension on every connected
  component of its source.

## Implementation notes

The relative dimension is supplied as the assertion that one exists on each connected component,
and `Stacks.Chow.flatComponentRelativeDimension` chooses it. A connected component is nonempty,
so the relative dimension on it is unique
(`AlgebraicGeometry.RelativeDimension.eq_of_nonempty`) and the choice is no choice at all: the
class does not depend on how the existence was proved
(`Stacks.Chow.completedFlatPullback_congr`). Every input of Stacks 0B78 is discharged at the
Gysin system of the first Chern class rule of invertible modules, as for
`Stacks.Chow.completedFlatPullbackOfSmooth`.

## References

* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 069F](https://stacks.math.columbia.edu/tag/069F)
* [Stacks Project, Tag 069K](https://stacks.math.columbia.edu/tag/069K)
* [Stacks Project, Tag 045R](https://stacks.math.columbia.edu/tag/045R)
* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The relative dimension on a connected component -/

section Dimension

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
  [LocallyOfFiniteType f]

/-- The relative dimension `r_a` of a morphism `f : X ⟶ Y` on a connected component `X_a` of its
source, for a morphism whose restriction to every connected component has pure relative
dimension. A connected component being nonempty, it is the unique such dimension. -/
def flatComponentRelativeDimension
    (hrel : ∀ a : _root_.ConnectedComponents X,
      ∃ r : ℕ, AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) r)
    (a : _root_.ConnectedComponents X) : ℕ :=
  (hrel a).choose

/-- The restriction of `f` to the connected component `X_a` has pure relative dimension
`Stacks.Chow.flatComponentRelativeDimension`. -/
theorem relativeDimension_flatComponentRelativeDimension
    (hrel : ∀ a : _root_.ConnectedComponents X,
      ∃ r : ℕ, AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) r)
    (a : _root_.ConnectedComponents X) :
    AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a)
      (flatComponentRelativeDimension f hrel a) :=
  (hrel a).choose_spec

/-- The relative dimension on a connected component is the relative dimension of the
restriction there, whichever way it is given. -/
theorem flatComponentRelativeDimension_eq
    (hrel : ∀ a : _root_.ConnectedComponents X,
      ∃ r : ℕ, AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) r)
    (a : _root_.ConnectedComponents X) {r : ℕ}
    (hr : AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) r) :
    flatComponentRelativeDimension f hrel a = r :=
  (relativeDimension_flatComponentRelativeDimension f hrel a).eq_of_nonempty hr

/-- For a smooth morphism the relative dimension on a connected component is
`Stacks.Chow.smoothComponentRelativeDimension`. -/
theorem flatComponentRelativeDimension_eq_smoothComponentRelativeDimension [Smooth f]
    (hrel : ∀ a : _root_.ConnectedComponents X,
      ∃ r : ℕ, AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) r)
    (a : _root_.ConnectedComponents X) :
    flatComponentRelativeDimension f hrel a = smoothComponentRelativeDimension f a :=
  flatComponentRelativeDimension_eq f hrel a
    (relativeDimension_smoothComponentRelativeDimension f a)

end Dimension

/-! ### Flat local complete intersection morphisms -/

section LCI

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)

/-- **Flat local complete intersection morphisms have locally constant relative dimension.** The
restriction of a flat local complete intersection morphism (Stacks 069F) to a connected component
of its source has pure relative dimension. The morphism is syntomic (Stacks 069K), hence so is its
restriction to the component (Stacks 01UD); a syntomic morphism is flat, locally of finite
presentation (Stacks 01UK) and has Cohen–Macaulay fibres (Stacks 045R), and a morphism of this
kind with connected source has pure relative dimension (Stacks 02NM). -/
@[sga "4½ Th_finitude 2.2" "more general"]
theorem exists_relativeDimension_resConnectedComponent_of_isLocalCompleteIntersection [Flat f]
    [LocallyOfFiniteType f] (hlci : IsLocalCompleteIntersectionMorphism f)
    (a : _root_.ConnectedComponents X) :
    ∃ r : ℕ, AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) r := by
  have hsyn : Syntomic (f.resConnectedComponent a) :=
    syntomic_resLE (syntomic_of_flat_of_isLocalCompleteIntersectionMorphism ‹Flat f› hlci) _ _ _
  have : Flat (f.resConnectedComponent a) := flat hsyn
  have : LocallyOfFinitePresentation (f.resConnectedComponent a) :=
    locallyOfFinitePresentation hsyn
  exact exists_relativeDimension_of_preconnectedSpace _ (isCohenMacaulay_fiber_of_syntomic hsyn)

end LCI

/-! ### The class on completions -/

section Class

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX)

/-- **`f^* ∈ A^*(X ⟶ Y)^∧` for a flat morphism `f`** (Stacks 0B78 on completions). For a flat
morphism whose restriction to every connected component `X_a` of `X` has pure relative dimension
`r_a`, the flat-pullback class in the completed bivariant group of Stacks 0FE0: on `X_a` it is the
class of Stacks 0B78 of the restriction `X_a ⟶ Y_{a'}` of `f`, placed in degree `-r_a`. Every input
of Stacks 0B78 is discharged. -/
def completedFlatPullback [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (hrel : ∀ a : _root_.ConnectedComponents X,
      ∃ r : ℕ, AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) r) :
    completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf :=
  fun a ↦ DirectSum.of _ (-(flatComponentRelativeDimension f hrel a : ℤ))
    (flatPullbackBivariantClassOfInvertible C ((X.connectedComponentOpens a).ι ≫ sX)
        ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap a)).ι ≫ sY)
        (f.resConnectedComponent a) (f.resConnectedComponent_comp_ι_comp hf a)
        (flatComponentRelativeDimension f hrel a)
        (relativeDimension_flatComponentRelativeDimension f hrel a))

variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- On a connected component `X_a` of `X`, the completed class `f^*` is the class of
Stacks 0B78 of the restriction of `f`, placed in degree `-r_a`. -/
theorem completedFlatPullback_apply
    (hrel : ∀ a : _root_.ConnectedComponents X,
      ∃ r : ℕ, AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) r)
    (a : _root_.ConnectedComponents X) :
    completedFlatPullback C sX sY f hf hrel a =
      DirectSum.of _ (-(flatComponentRelativeDimension f hrel a : ℤ))
        (flatPullbackBivariantClassOfInvertible C ((X.connectedComponentOpens a).ι ≫ sX)
            ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap a)).ι ≫ sY)
            (f.resConnectedComponent a) (f.resConnectedComponent_comp_ι_comp hf a)
            (flatComponentRelativeDimension f hrel a)
            (relativeDimension_flatComponentRelativeDimension f hrel a)) :=
  rfl

/-- On a connected component `X_a` on which `f` has relative dimension `r`, the completed class
`f^*` is the class of Stacks 0B78 of the restriction of `f` of relative dimension `r`, placed in
degree `-r`. -/
theorem completedFlatPullback_apply_of_relativeDimension
    (hrel : ∀ a : _root_.ConnectedComponents X,
      ∃ r : ℕ, AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) r)
    (a : _root_.ConnectedComponents X) (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) r) :
    completedFlatPullback C sX sY f hf hrel a =
      DirectSum.of _ (-(r : ℤ))
        (flatPullbackBivariantClassOfInvertible C ((X.connectedComponentOpens a).ι ≫ sX)
            ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap a)).ι ≫ sY)
            (f.resConnectedComponent a) (f.resConnectedComponent_comp_ι_comp hf a) r hr) := by
  have key : ∀ (s : ℕ) (hs : AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) s),
      s = r → DirectSum.of _ (-(s : ℤ))
        (flatPullbackBivariantClassOfInvertible C ((X.connectedComponentOpens a).ι ≫ sX)
            ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap a)).ι ≫ sY)
            (f.resConnectedComponent a) (f.resConnectedComponent_comp_ι_comp hf a) s hs) =
      DirectSum.of _ (-(r : ℤ))
        (flatPullbackBivariantClassOfInvertible C ((X.connectedComponentOpens a).ι ≫ sX)
            ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap a)).ι ≫ sY)
            (f.resConnectedComponent a) (f.resConnectedComponent_comp_ι_comp hf a) r hr) := by
    rintro s hs rfl
    rfl
  exact key _ _ (flatComponentRelativeDimension_eq f hrel a hr)

/-- The completed class `f^*` does not depend on how the existence of the relative dimensions is
proved. -/
theorem completedFlatPullback_congr
    (hrel hrel' : ∀ a : _root_.ConnectedComponents X,
      ∃ r : ℕ, AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) r) :
    completedFlatPullback C sX sY f hf hrel = completedFlatPullback C sX sY f hf hrel' :=
  rfl

/-- **The smooth case.** For a smooth morphism, the completed flat-pullback class is
`Stacks.Chow.completedFlatPullbackOfSmooth`. -/
theorem completedFlatPullbackOfSmooth_eq_completedFlatPullback [Smooth f]
    (hrel : ∀ a : _root_.ConnectedComponents X,
      ∃ r : ℕ, AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) r) :
    completedFlatPullbackOfSmooth C sX sY f hf = completedFlatPullback C sX sY f hf hrel := by
  funext a
  rw [completedFlatPullback_apply_of_relativeDimension C sX sY f hf hrel a _
    (relativeDimension_smoothComponentRelativeDimension f a)]
  rfl

/-- **`f^* ∈ A^*(X ⟶ Y)^∧` for a flat local complete intersection morphism `f`.** The class
`Stacks.Chow.completedFlatPullback` of a flat local complete intersection morphism (Stacks 069F),
whose relative dimension is constant on every connected component of its source by
`Stacks.Chow.exists_relativeDimension_resConnectedComponent_of_isLocalCompleteIntersection`. -/
def completedFlatPullbackOfFlatLCI (hlci : IsLocalCompleteIntersectionMorphism f) :
    completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf :=
  completedFlatPullback C sX sY f hf
    (exists_relativeDimension_resConnectedComponent_of_isLocalCompleteIntersection f hlci)

/-- On a connected component `X_a` on which the flat local complete intersection morphism `f`
has relative dimension `r`, the class `f^*` is the class of Stacks 0B78 of the restriction of
`f`, placed in degree `-r`. -/
theorem completedFlatPullbackOfFlatLCI_apply (hlci : IsLocalCompleteIntersectionMorphism f)
    (a : _root_.ConnectedComponents X) (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) r) :
    completedFlatPullbackOfFlatLCI C sX sY f hf hlci a =
      DirectSum.of _ (-(r : ℤ))
        (flatPullbackBivariantClassOfInvertible C ((X.connectedComponentOpens a).ι ≫ sX)
            ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap a)).ι ≫ sY)
            (f.resConnectedComponent a) (f.resConnectedComponent_comp_ι_comp hf a) r hr) :=
  completedFlatPullback_apply_of_relativeDimension C sX sY f hf _ a r hr

end Class

end Stacks.Chow

end
