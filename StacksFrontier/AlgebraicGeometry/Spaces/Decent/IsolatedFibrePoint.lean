module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ZeroDimensionalPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocus

/-!
# Isolated points of a field-valued fibre

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, let `p` be a field-valued point of `Y` with field of definition `k`, presenting a point
`y` of `|Y|` by a morphism `Spec k ⟶ Y`, and let `X_k = X ×_Y Spec k` be the field fibre. For
a point `x̃` of `|X_k|`, with image `x` in `|X|`, Stacks 0ACB compares eight conditions. Four
of them concern the field fibre and `f` itself:

* (5) `x̃` is isolated in `|X_k|`;
* (6) `x̃` is closed in `|X_k|` and admits no nontrivial generalization there;
* (7) `X_k` has dimension zero at `x̃`;
* (8) `f` is quasi-finite at `x`.

This file proves that these four are equivalent, as the three successive equivalences
(5) ⇔ (6), (6) ⇔ (7) and (7) ⇔ (8).

## Main results

* `AlgebraicGeometry.Space.isIsolatedPoint_fieldFibre_iff_isClosedNoGeneralization`:
  conditions (5) and (6).
* `AlgebraicGeometry.Space.isClosedNoGeneralization_fieldFibre_iff_dimensionAtPoint_eq_zero`:
  conditions (6) and (7).
* `AlgebraicGeometry.Space.dimensionAtPoint_fieldFibre_eq_zero_iff_isQuasiFiniteAt`:
  conditions (7) and (8).

## Implementation notes

The field fibre is a presheaf over `S`, not over `Spec k`, and its structure morphism
`X_k ⟶ Spec k` is the morphism to the presheaf represented by the object
`AlgebraicGeometry.Space.FieldValuedPoint.siteObject` of the site, whose underlying scheme is
`Spec k`. The equivalences (5) ⇔ (6) and (6) ⇔ (7) are therefore the criteria of Stacks 0AC9
applied to that structure morphism, in the form in which
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.ZeroDimensionalPoint` proves them for an
arbitrary base scheme: nothing has to be transported across a change of base scheme, and the
hypothesis those criteria need — a morphism from the scheme underlying the base object to the
spectrum of a field which is locally of finite type — is here the identity of `Spec k`.

The conditions are stated at a point `x̃` of `|X_k|` throughout, the point `x` of `|X|` of the
source statement being its image under `|X_k| → |X|`. That image is automatically in the
set-theoretic fibre `f^{-1}({y})`, by
`AlgebraicGeometry.Space.range_pointsMap_fst_fieldFibre`, so no compatibility hypothesis is
needed.

The remaining four conditions of the source — the local dimension of `|X_k|` at `x̃`, and the
three conditions on `x` inside the set-theoretic fibre `f^{-1}({y})` — are not compared here.
Comparing the local dimension of `|X_k|` with the dimension of `X_k` is Stacks 0A4J for the
decent space `X_k`, and comparing the conditions inside `f^{-1}({y})` with those on `|X_k|`
needs the comparison map `|X_k| → f^{-1}({y})` to be a homeomorphism for a quasi-compact
monomorphic representative, which is the topological half of Stacks 0AC8; neither is available
in this repository yet. Once they are, the resulting equivalences belong beside these three.

## References

* [Stacks Project, Tag 0ACB](https://stacks.math.columbia.edu/tag/0ACB)
* [Stacks Project, Tag 0AC9](https://stacks.math.columbia.edu/tag/0AC9)
* [Stacks Project, Tag 0ABM](https://stacks.math.columbia.edu/tag/0ABM)
* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
* [Stacks Project, Tag 06LS](https://stacks.math.columbia.edu/tag/06LS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The field fibre as a space over the spectrum of a field -/

/-- The field fibre of a morphism of algebraic spaces along a field-valued point of the target
is an algebraic space. -/
theorem isAlgebraicSpace_fieldFibre (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) :
    IsAlgebraicSpace B S hS (fieldFibre B S hS f p) :=
  isAlgebraicSpace_pullback B S hS f (yonedaEquiv.symm p.value) hX
    (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS Y)) hY

/-! ### The equivalences -/

/-- A point of the field fibre is closed with no nontrivial generalization exactly when it is
isolated. -/
private theorem isClosedNoGeneralization_iff_isIsolatedPoint_fieldFibre
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (z : points B S hS (fieldFibre B S hS f p)) :
    (IsClosed ({z} : Set (points B S hS (fieldFibre B S hS f p))) ∧
        ∀ z' : points B S hS (fieldFibre B S hS f p), z' ⤳ z → z' = z) ↔
      IsIsolatedPoint z :=
  isClosedNoGeneralization_iff_isIsolatedPoint_of_isLocallyOfFiniteType
    (k := p.carrier) (𝟙 _) (isAlgebraicSpace_fieldFibre hX hY f p)
    (pullback.snd f (yonedaEquiv.symm p.value))
    (isLocallyOfFiniteType_snd_fieldFibre B S hS hX hY hf p) z

/-- **Stacks 0ACB, conditions (5) and (6).** A point of the field fibre of a morphism of
algebraic spaces locally of finite type is isolated exactly when it is closed in the field
fibre and admits no nontrivial generalization there.

The field fibre is locally of finite type over the spectrum of a field, so this is the
comparison of conditions (2) and (3) of Stacks 0AC9. -/
@[stacks 0ACB "conditions (5) and (6)"]
theorem isIsolatedPoint_fieldFibre_iff_isClosedNoGeneralization
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (z : points B S hS (fieldFibre B S hS f p)) :
    IsIsolatedPoint z ↔
      (IsClosed ({z} : Set (points B S hS (fieldFibre B S hS f p))) ∧
        ∀ z' : points B S hS (fieldFibre B S hS f p), z' ⤳ z → z' = z) :=
  (isClosedNoGeneralization_iff_isIsolatedPoint_fieldFibre hX hY f hf p z).symm

/-- **Stacks 0ACB, conditions (6) and (7).** A point of the field fibre of a morphism of
algebraic spaces locally of finite type is closed there with no nontrivial generalization
exactly when the field fibre has dimension zero at that point.

The field fibre is locally of finite type over the spectrum of a field, so this is the
comparison of conditions (2), (3) and (4) of Stacks 0AC9. -/
@[stacks 0ACB "conditions (6) and (7)"]
theorem isClosedNoGeneralization_fieldFibre_iff_dimensionAtPoint_eq_zero
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (z : points B S hS (fieldFibre B S hS f p)) :
    (IsClosed ({z} : Set (points B S hS (fieldFibre B S hS f p))) ∧
        ∀ z' : points B S hS (fieldFibre B S hS f p), z' ⤳ z → z' = z) ↔
      dimensionAtPoint B S hS (fieldFibre B S hS f p)
        (isAlgebraicSpace_fieldFibre hX hY f p) z = 0 :=
  (isClosedNoGeneralization_iff_isIsolatedPoint_fieldFibre hX hY f hf p z).trans
    (isIsolatedPoint_iff_dimensionAtPoint_eq_zero_of_isLocallyOfFiniteType
      (k := p.carrier) (𝟙 _) (isAlgebraicSpace_fieldFibre hX hY f p)
      (pullback.snd f (yonedaEquiv.symm p.value))
      (isLocallyOfFiniteType_snd_fieldFibre B S hS hX hY hf p) z)

/-- **Stacks 0ACB, conditions (7) and (8).** The field fibre of a morphism of algebraic spaces
locally of finite type has dimension zero at a point exactly when the morphism is quasi-finite
at the image of that point.

The implication to quasi-finiteness is Stacks 06LS. Conversely, the locus of quasi-finiteness
of the structure morphism of the field fibre is the inverse image of the locus of
quasi-finiteness of the morphism (Stacks 0ABM, part (2)), so the structure morphism of the
field fibre is quasi-finite at the point; the spectrum of a field has one point, so the field
fibre has dimension zero there. -/
@[stacks 0ACB "conditions (7) and (8)"]
theorem dimensionAtPoint_fieldFibre_eq_zero_iff_isQuasiFiniteAt
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (z : points B S hS (fieldFibre B S hS f p)) :
    dimensionAtPoint B S hS (fieldFibre B S hS f p)
        (isAlgebraicSpace_fieldFibre hX hY f p) z = 0 ↔
      IsQuasiFiniteAt B S hS f
        (pointsMap B S hS (fieldFibre B S hS f p)
          (pullback.fst f (yonedaEquiv.symm p.value)) z) := by
  have hsub : Subsingleton
      ((BigFppfOver.toScheme B S hS).obj (p.siteObject B S hS Y)) :=
    inferInstanceAs (Subsingleton (Spec (.of p.carrier)))
  refine ⟨isQuasiFiniteAt_of_dimensionAtPoint_fiber_eq_zero B S hS hX hY f hf p z,
    fun hq ↦ ?_⟩
  let X' : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Y' : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let T' : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj (p.siteObject B S hS Y),
      isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS Y)⟩
  let f' : X' ⟶ Y' := ObjectProperty.homMk f
  let g' : T' ⟶ Y' := ObjectProperty.homMk (yonedaEquiv.symm p.value)
  have hlocus := setOf_isQuasiFiniteAt_eq_preimage_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f' g') hf
  have hz : IsQuasiFiniteAt B S hS (pullback.snd f (yonedaEquiv.symm p.value)) z :=
    (Set.ext_iff.mp hlocus z).mpr hq
  exact dimensionAtPoint_eq_zero_of_isQuasiFiniteAt_of_subsingleton
    (T := p.siteObject B S hS Y) (isAlgebraicSpace_fieldFibre hX hY f p)
    (pullback.snd f (yonedaEquiv.symm p.value)) z hz

end AlgebraicGeometry.Space

end
