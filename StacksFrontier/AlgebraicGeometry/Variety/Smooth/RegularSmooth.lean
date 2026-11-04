module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Descent.SmoothAlgebra
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A regular scheme over a perfect field is smooth

Over a perfect field the two conditions "smooth over `k`" and "regular" agree for a scheme
locally of finite type over `k`. One direction is `isRegular_of_smooth_over_field` (Stacks tag
056S); this file supplies the converse, which is the global form of the equality of the smooth
and the regular locus (Stacks tag 0B8X), and derives from it that a fibre product of two such
schemes over `k` is again regular.

## Main results

* `AlgebraicGeometry.smooth_of_isRegular_over_perfectField`: a regular scheme locally of finite
  type over a perfect field is smooth over that field.
* `AlgebraicGeometry.smooth_iff_isRegular_over_perfectField`: over a perfect field, a scheme
  locally of finite type is regular exactly when it is smooth.
* `AlgebraicGeometry.smooth_pullback_of_isRegular`: a fibre product over a perfect field of two
  regular schemes locally of finite type is smooth over the field. In particular `X ×_k X` is
  smooth over `k` when `X` is regular, which together with smoothness of `X` is the input that a
  regularity statement about the diagonal of a nonsingular variety consumes.
* `AlgebraicGeometry.isRegular_pullback_of_isRegular`: the same fibre product is regular.

## Implementation notes

The argument is affine-local on the source and goes through the ring-level statement
`Stacks.RingTheory.SmoothDescent.smooth_of_isRegularRing`: on an affine open `U` witnessing
regularity, `Γ(X, U)` is a regular ring of finite type — hence, the base being a field and so
Noetherian, of finite presentation — over `Γ(Spec k, ⊤)`, which is a perfect field because
`Scheme.ΓSpecIso` identifies it with `k`. Since `Spec k` is affine,
`HasRingHomProperty.of_iSup_eq_top` turns a family of affine opens covering `X` together with
smoothness of each `f.appLE ⊤ U le_top` into `Smooth f`; the witnessing opens supplied by
`IsRegular` are indexed by the points of `X` and cover it by construction.

The fibre product statement is stated for two morphisms rather than for a self-product, which
costs nothing: `pullback.fst f g` is the base change of `g`, so smoothness of the projection and
hence of the structure morphism `pullback.fst f g ≫ f` is instance resolution, and Stacks 056S
converts it back to regularity. Note that no algebraic closedness and no reducedness hypothesis
is needed in either direction; perfection of the ground field is used only for the direction
proved here, and is necessary, a regular algebra of finite type over a nonperfect field not
being smooth in general.

## References

* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
* [Stacks Project, Tag 00TV](https://stacks.math.columbia.edu/tag/00TV)
* [Stacks Project, Tag 0B8X](https://stacks.math.columbia.edu/tag/0B8X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.RingTheory.SmoothDescent

universe u

namespace AlgebraicGeometry

/-- A regular scheme locally of finite type over a perfect field is smooth over that field.

This is the converse of `AlgebraicGeometry.isRegular_of_smooth_over_field` (Stacks tag 056S), and
the global form of the equality of the smooth and the regular locus of Stacks tag 0B8X. -/
@[ega "0 19.0.2" "IV",
  ega "IV 17.15.2" "Over a perfect field",
  ega "IV 17.15.5" "special case",
  sga "1 II 5.4" "more general",
  sga "6 XIV 4.2" "Clause"]
theorem smooth_of_isRegular_over_perfectField {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (hX : IsRegular X) :
    Smooth f := by
  choose U hU hreg using hX
  refine HasRingHomProperty.of_iSup_eq_top (Q := RingHom.Smooth) U ?_ fun x ↦ ?_
  · exact eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hU x⟩
  · let _ : Field Γ(Spec (.of k), ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.isField (Field.toIsField k)).toField
    have : PerfectField Γ(Spec (.of k), ⊤) :=
      PerfectField.of_ringEquiv (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm
    let _ : Algebra Γ(Spec (.of k), ⊤) Γ(X, (U x).1) :=
      (f.appLE ⊤ (U x).1 le_top).hom.toAlgebra
    have : Algebra.FiniteType Γ(Spec (.of k), ⊤) Γ(X, (U x).1) :=
      f.finiteType_appLE (isAffineOpen_top _) (U x).2 le_top
    have : Algebra.FinitePresentation Γ(Spec (.of k), ⊤) Γ(X, (U x).1) :=
      Algebra.FinitePresentation.of_finiteType.mp ‹_›
    have : IsRegularRing Γ(X, (U x).1) := hreg x
    exact smooth_of_isRegularRing Γ(Spec (.of k), ⊤) Γ(X, (U x).1)

/-- Over a perfect field, a scheme locally of finite type is regular exactly when its structure
morphism is smooth. -/
@[ega "0 19.0.2",
  ega "IV 17.15.2",
  ega "IV 17.15.5" "special case",
  sga "1 II 5.4" "more general",
  sga "6 XIV 4.2" "Clause"]
theorem smooth_iff_isRegular_over_perfectField {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    Smooth f ↔ IsRegular X :=
  ⟨fun _ ↦ isRegular_of_smooth_over_field f, smooth_of_isRegular_over_perfectField f⟩

/-- A fibre product over a perfect field of two regular schemes locally of finite type over that
field is smooth over the field. Taking `g = f` this says that `X ×_k X` is smooth over `k`
whenever `X` is regular, which together with smoothness of `X` itself is what a regularity
statement about the diagonal (Stacks tag 067U) consumes. -/
@[ega "0 19.0.2" "IV", sga "1 II 5.4" "more general"]
theorem smooth_pullback_of_isRegular {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (hX : IsRegular X) (hY : IsRegular Y) :
    Smooth (pullback.fst f g ≫ f) := by
  have : Smooth f := smooth_of_isRegular_over_perfectField f hX
  have : Smooth g := smooth_of_isRegular_over_perfectField g hY
  infer_instance

/-- A fibre product over a perfect field of two regular schemes locally of finite type over that
field is regular. Taking `g = f` this says that `X ×_k X` is regular whenever `X` is. -/
theorem isRegular_pullback_of_isRegular {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (hX : IsRegular X) (hY : IsRegular Y) :
    IsRegular (pullback f g) :=
  have : Smooth (pullback.fst f g ≫ f) := smooth_pullback_of_isRegular f g hX hY
  isRegular_of_smooth_over_field (pullback.fst f g ≫ f)

end AlgebraicGeometry

end
