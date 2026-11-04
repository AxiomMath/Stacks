module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.SetTheory.Cardinal.ENat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-!
# The number of connected components of a geometric fibre

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. A field-valued point
`p` of `Y` cuts out the fibre `X_p`, the fibre product of `f` with the morphism `h_{Spec κ} ⟶ Y`
represented by `p`, and the number of connected components of the point space of that fibre is
a cardinal, read as an element of `ℕ∞` by sending every infinite cardinal to `∞`. Restricting
attention to *geometric* representatives — those whose field is algebraically closed — this
number depends only on the point of `|Y|` represented, and the resulting function
`|Y| → ℕ∞` is the one of **Stacks 0E1B**.

## Main definitions

* `AlgebraicGeometry.Space.geometricFiberComponentCount` is the number of connected components
  of the fibre over one field-valued point of the target.
* `AlgebraicGeometry.Space.numberGeometricConnectedComponents` is the resulting function on
  the points of the target.

## Main results

* `AlgebraicGeometry.Space.exists_geometricRepresentative`: every point of a presheaf on the
  big fppf site of `S` is the class of a geometric point, so the infimum defining the function
  is taken over a nonempty set.
* `AlgebraicGeometry.Space.cardinalMk_connectedComponents_eq_of_iso`: isomorphic presheaves
  have equinumerous sets of connected components of points.
* `AlgebraicGeometry.Space.geometricFiberComponentCount_pullback_snd_eq`: the count is
  compatible with base change, on representatives.

## Implementation notes

The count takes values in `ℕ∞` through `Cardinal.toENat`, which sends every infinite cardinal
to `⊤`; this is the source's value set `{0, 1, 2, …, ∞}`.

`AlgebraicGeometry.Space.numberGeometricConnectedComponents` is defined as the infimum of the
counts over all geometric representatives of the given point. That all of those counts agree
is the content of the source lemma, and it needs the invariance of the number of connected
components of an algebraic space under an extension of separably closed base fields
(Stacks 0A12); the two statements depending on it are not in this file.

Neither the definition of the count nor the existence of a geometric representative uses the
algebraic-space axioms: the point topology of Stacks 03BX,
`AlgebraicGeometry.Space.pointTopology`, is available for an arbitrary presheaf, so no
algebraicity hypothesis is carried. Clients with algebraic spaces in hand simply do not have
to supply one.

## References

* [Stacks Project, Tag 0E1B](https://stacks.math.columbia.edu/tag/0E1B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Homeomorph

/-- A homeomorphism induces a homeomorphism of the spaces of connected components: it is a
quotient map, hence coinducing, and its fibres are singletons. -/
noncomputable def connectedComponentsCongr {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : ConnectedComponents X ≃ₜ ConnectedComponents Y :=
  e.isQuotientMap.isCoinducing.connectedComponentsHomeomorph fun y ↦ by
    have hfib : e ⁻¹' {y} = {e.symm y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h ↦ by rw [← h, e.symm_apply_apply], fun h ↦ by rw [h, e.apply_symm_apply]⟩
    rw [hfib]
    exact isConnected_singleton

end Homeomorph

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Isomorphic presheaves on the big fppf site of `S` have equinumerous sets of connected
components of points, their point spaces being homeomorphic. -/
theorem cardinalMk_connectedComponents_eq_of_iso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
    Cardinal.mk (ConnectedComponents (points B S hS F)) =
      Cardinal.mk (ConnectedComponents (points B S hS G)) :=
  Cardinal.mk_congr (pointsHomeomorphOfIso B S hS e).connectedComponentsCongr.toEquiv

/-- The number of connected components of the fibre of a morphism of presheaves over a
field-valued point of the target, with every infinite cardinality sent to `∞`.

The fibre is the pullback of the morphism along the morphism represented by the field-valued
point, and its point space carries the topology of Stacks 03BX. -/
noncomputable def geometricFiberComponentCount
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (p : FieldValuedPoint B S hS G) : ℕ∞ :=
  Cardinal.toENat
    (Cardinal.mk (ConnectedComponents (points B S hS (pullback f (yonedaEquiv.symm p.value)))))

/-- **Stacks 0E1B.** The number of geometric connected components of the fibres of a morphism
of algebraic spaces: the function on the points of the target whose value at `y` is the number
of connected components of the fibre over any geometric point representing `y`.

By `AlgebraicGeometry.Space.exists_geometricRepresentative` the set whose infimum is taken is
nonempty, and the source lemma is that all of its elements agree. -/
@[stacks 0E1B "function", ega "III 4.3.4", ega "IV 4.5.2" "partial"]
noncomputable def numberGeometricConnectedComponents
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) : points B S hS G → ℕ∞ :=
  fun y ↦ sInf {n : ℕ∞ | ∃ p : GeometricPoint B S hS G,
    p.image = y ∧ geometricFiberComponentCount B S hS f p.val = n}

/-- Taking the fibre over a field-valued point commutes with base change: the fibre of the
projection from a fibre product over a field-valued point of the second factor is the fibre of
the original morphism over the image of that point. -/
theorem geometricFiberComponentCount_pullback_snd_eq
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (g : H ⟶ G)
    (p : FieldValuedPoint B S hS H) :
    geometricFiberComponentCount B S hS (pullback.snd f g) p =
      geometricFiberComponentCount B S hS f (FieldValuedPoint.map B S hS H g p) := by
  set q := FieldValuedPoint.map B S hS H g p with hq
  have hβ : yonedaEquiv.symm p.value ≫ g = yonedaEquiv.symm q.value := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp]
    show g.app (op p.siteObject) (yonedaEquiv (yonedaEquiv.symm p.value)) =
      yonedaEquiv (yonedaEquiv.symm q.value)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  have hIso : pullback (pullback.snd f g) (yonedaEquiv.symm p.value) ≅
      pullback f (yonedaEquiv.symm q.value) := by
    rw [← hβ]
    exact pullbackLeftPullbackSndIso f g (yonedaEquiv.symm p.value)
  exact congrArg Cardinal.toENat (cardinalMk_connectedComponents_eq_of_iso B S hS hIso)

end AlgebraicGeometry.Space

end
