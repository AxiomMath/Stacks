module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverFieldDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreQuasiFinite

/-!
# Two more of the equivalences of Stacks 0ACK

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, let `p` be a field-valued point of `Y` with field of definition `k`, let `y` be the point
of `|Y|` it represents, and let `X_k = X ×_Y Spec(k)` be the field fibre. Stacks 0ACK compares
eight conditions on this data; `StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreConditions.lean`
states them, and that file together with
`StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreQuasiFinite.lean` proves the implications which
need no input beyond the point topology and Lemma 0ACA in its library form.

This file adds two statements of the tag. The first is the arrow the source draws from decency
of `f`: condition (4) implies condition (5). The second packages the two proved implications
between conditions (7) and (8) as the equivalence the tag asserts.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.discreteTopology_points_fieldFibre_of_finite_of_isDecent` is
  Stacks 0ACK, condition (4) implies condition (5) for a decent morphism.
* `AlgebraicGeometry.Space.dimension_fieldFibre_eq_zero_iff_isQuasiFiniteAt` is Stacks 0ACK,
  conditions (7) and (8) are equivalent.
* `AlgebraicGeometry.Space.bijective_pointsMap_of_isIso` and
  `AlgebraicGeometry.Space.discreteTopology_points_of_isIso` transport the point set and its
  topology along an isomorphism of presheaves.

## Implementation notes

The decent arrow is Lemma 0ACA, condition (1) implies condition (2), applied to the field fibre
over `Spec(k)`: that is
`AlgebraicGeometry.Space.discreteTopology_points_of_finite_of_isDecentSpace`, whose hypotheses
are an algebraic space locally of finite type over a one-point base, decent, with finite point
set. Three of the four are immediate for the field fibre — `Spec(k)` has one point, the
structure morphism is a base change of `f` by Tag 03XH, and condition (4) *is* the finiteness.
The fourth is where decency of `f` is used, and it is why the proof runs on the **flipped**
pullback. Stacks 03KZ asks every base change `T ×_Y X` along a morphism out of a representable
presheaf to be a decent algebraic space, and for `T = Spec(k)` that is
`CategoryTheory.Limits.pullback (fieldMorphism B S hS Y p) f`, whereas the field fibre is
`CategoryTheory.Limits.pullback f (fieldMorphism B S hS Y p)`. The two are interchanged by
`CategoryTheory.Limits.pullbackSymmetry`, and the hypothesis and the conclusion are carried
across it by `AlgebraicGeometry.Space.bijective_pointsMap_of_isIso` and
`AlgebraicGeometry.Space.discreteTopology_points_of_isIso`; both rest on functoriality of the
point set (Tag 03BU) and, for the topology, on continuity of the induced map, which is clause
(2) of Tag 03BX.

Conditions (7) and (8) are stated as the source states them, with the algebraic-space structure
of the field fibre supplied by `AlgebraicGeometry.Space.isAlgebraicSpace_pullback` inside the
statement rather than hypothesised, so that condition (7) reads as the plain equation
`dim(X_k) = 0`. The nonemptiness hypothesis is used only in the direction (8) implies (7): the
dimension of Tag 04N6 is a supremum in `WithBot ℕ∞`, so the empty space has dimension `⊥` and
not `0`, and a nonempty set-theoretic fibre is what gives the field fibre a point, by Tag 03H4.

**What is not proved.** The equivalence of conditions (5) and (6), that of conditions (6) and
(7), and the two statements conditioned on `Y` being decent — conditions (2) and (3) equivalent,
and conditions (2) and (5) equivalent — all turn on the one arrow of Lemma 0ACA that is missing,
from the topological conditions (2), (3), (5), (6) back to the dimension condition (7). Without
it discreteness of `|X_k|` cannot be compared across two field-valued representatives of the
same point of `|Y|`, since the only representative-free condition in the chain is condition (8).
The remaining statement, "condition (1) implies condition (4) for decent spaces", needs more
than that arrow: it needs the fibres of `|X_k| → F` to be finite, which is the residue-field
description of the points of a field fibre. Stacks 0AC8 is proved in full
(`StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreInducing.lean`) and is *not* what any of them
lacks.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03KZ](https://stacks.math.columbia.edu/tag/03KZ)
* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
* [Stacks Project, Tag 04N6](https://stacks.math.columbia.edu/tag/04N6)
* [Stacks Project, Tag 0ACA](https://stacks.math.columbia.edu/tag/0ACA)
* [Stacks Project, Tag 0ACK](https://stacks.math.columbia.edu/tag/0ACK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Transport of the point set along an isomorphism -/

section Transfer

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An isomorphism of presheaves on the big fppf site of `S` is bijective on the points of
Tag 03BU: the point set is functorial, so the inverse morphism induces a two-sided inverse. -/
theorem bijective_pointsMap_of_isIso (α : F ⟶ G) [IsIso α] :
    Function.Bijective (pointsMap B S hS F α) := by
  have h1 : pointsMap B S hS G (inv α) ∘ pointsMap B S hS F α = id := by
    rw [← pointsMap_comp, IsIso.hom_inv_id, pointsMap_id]
  have h2 : pointsMap B S hS F α ∘ pointsMap B S hS G (inv α) = id := by
    rw [← pointsMap_comp, IsIso.inv_hom_id, pointsMap_id]
  exact Function.bijective_iff_has_inverse.mpr ⟨_, congrFun h1, congrFun h2⟩

/-- Discreteness of the point space of Tag 03BX transports along an isomorphism of presheaves:
the inverse morphism is injective on points and continuous, so the preimage of a singleton is
the singleton of its image. -/
theorem discreteTopology_points_of_isIso (α : F ⟶ G) [IsIso α]
    (h : DiscreteTopology (points B S hS F)) : DiscreteTopology (points B S hS G) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro y
  have hinj := (bijective_pointsMap_of_isIso B S hS (inv α)).1
  have hpre : pointsMap B S hS G (inv α) ⁻¹' {pointsMap B S hS G (inv α) y} = {y} := by
    ext z
    exact ⟨fun hz ↦ hinj hz, fun hz ↦ by rw [hz]; rfl⟩
  rw [← hpre]
  have := h
  exact (isOpen_discrete _).preimage (continuous_pointsMap B S hS (inv α))

end Transfer

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Condition (4) implies condition (5) for a decent morphism -/

/-- **Stacks 0ACK, condition (4) implies condition (5) for a decent morphism.** If `f` is a
decent morphism locally of finite type and the point set of the field fibre `X_k` is finite,
then that point set is discrete.

The field fibre is an algebraic space locally of finite type over the one-point scheme `Spec(k)`
and, `f` being decent, a decent one; so Lemma 0ACA, condition (1) implies condition (2), applies
to it. Decency is available for the flipped pullback `Spec(k) ×_Y X`, which is the shape
Stacks 03KZ quantifies over, and the hypothesis and conclusion are carried across the symmetry
isomorphism. -/
@[stacks 0ACK "condition (4) implies condition (5) for a decent morphism"]
theorem discreteTopology_points_fieldFibre_of_finite_of_isDecent
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y) (hft : IsLocallyOfFiniteType B S hS f)
    (hdecent : IsDecent B S hS f)
    (hfinite : (Set.univ : Set (points B S hS (fieldFibre B S hS f p))).Finite) :
    DiscreteTopology (points B S hS (fieldFibre B S hS f p)) := by
  have hZ : IsAlgebraicSpace B S hS (yoneda.obj p.siteObject) :=
    isAlgebraicSpace_yoneda B S hS p.siteObject
  have hflip : IsAlgebraicSpace B S hS (pullback (fieldMorphism B S hS Y p) f) :=
    isAlgebraicSpace_pullback B S hS (fieldMorphism B S hS Y p) f hZ hX hY
  have hk : Subsingleton ((BigFppfOver.toScheme B S hS).obj p.siteObject) :=
    subsingleton_toScheme_siteObject B S hS Y p
  have hgft : IsLocallyOfFiniteType B S hS (pullback.fst (fieldMorphism B S hS Y p) f) :=
    IsLocallyOfFiniteType.of_isPullback B S hS
      (IsPullback.of_hasPullback (fieldMorphism B S hS Y p) f) hX hY hft
  have hfin : Finite (points B S hS (pullback (fieldMorphism B S hS Y p) f)) := by
    have : Finite (points B S hS (fieldFibre B S hS f p)) := Set.finite_univ_iff.mp hfinite
    exact Finite.of_injective _
      (bijective_pointsMap_of_isIso B S hS
        (pullbackSymmetry (fieldMorphism B S hS Y p) f).hom).1
  exact discreteTopology_points_of_isIso B S hS
    (pullbackSymmetry (fieldMorphism B S hS Y p) f).hom
    (discreteTopology_points_of_finite_of_isDecentSpace B S hS hflip hk
      (pullback.fst (fieldMorphism B S hS Y p) f) hgft (hdecent p.siteObject _) hfin)

/-! ### Conditions (7) and (8) are equivalent -/

/-- **Stacks 0ACK, conditions (7) and (8).** For a morphism `f` locally of finite type and a
field-valued point `p` of its target with nonempty set-theoretic fibre, the field fibre `X_k`
has dimension zero as an algebraic space exactly when `f` is quasi-finite at every point of
`|X|` above the point represented by `p`.

Both implications are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreQuasiFinite.lean`; the nonemptiness hypothesis
is needed only to turn `dim(X_k) ≤ 0` into `dim(X_k) = 0`, and it reaches the field fibre
through Tag 03H4. -/
@[stacks 0ACK "conditions (7) and (8)"]
theorem dimension_fieldFibre_eq_zero_iff_isQuasiFiniteAt
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y) (hft : IsLocallyOfFiniteType B S hS f)
    (hne : (setFibre B S hS f p).Nonempty) :
    dimension B S hS (fieldFibre B S hS f p)
        (isAlgebraicSpace_pullback B S hS f (fieldMorphism B S hS Y p) hX
          (isAlgebraicSpace_yoneda B S hS p.siteObject) hY) = 0 ↔
      ∀ x : points B S hS X, x ∈ setFibre B S hS f p → IsQuasiFiniteAt B S hS f x :=
  ⟨fun h ↦ isQuasiFiniteAboveFieldValuedPoint_of_isZeroDimensionalFieldFibre B S hS hX hY hft
      p _ h,
    fun h ↦ isZeroDimensionalFieldFibre_of_isQuasiFiniteAboveFieldValuedPoint B S hS hX hY hft
      p _ h ((nonempty_points_fieldFibre_iff B S hS f p).mpr hne)⟩

end AlgebraicGeometry.Space

end
