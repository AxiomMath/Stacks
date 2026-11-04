module

public import StacksFrontier.AlgebraicGeometry.AmpleFamilyRelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePullback.QuasiAffineUnitIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite

/-!
# Ample families along an affine or quasi-affine morphism

Let `f : X ⟶ Y` be an affine or quasi-affine morphism of schemes. **Stacks 0GTQ** says that if
`Y` has an ample family of invertible modules, then so does `X`.

## Main results

* `Stacks.AmpleFamilyRelativeAmple.exists_isAmpleFamily_of_isQuasiAffineHom`: the quasi-affine
  case.
* `Stacks.AmpleFamilyRelativeAmple.exists_isAmpleFamily_of_isAffineHom_or_isQuasiAffineHom`:
  **Stacks 0GTQ**.

## Implementation notes

The morphism being quasi-affine is exactly the structure sheaf `𝒪_X` being ample relative to
`f`, which is Stacks 0891; the lemma is then the case `L = 𝒪_X` of Stacks 0GTP, which produces an
ample family on `X` out of one on `Y` and an `f`-ample invertible module. The form of Stacks 0891
used is `Stacks.AmplePullback.isRelativelyAmple_of_isQuasiAffineHom_of_iso_unitModule`, whose
right-hand side is the class `AlgebraicGeometry.IsQuasiAffineHom`.

An affine morphism is quasi-affine, by `AlgebraicGeometry.isQuasiAffineHom_of_isAffineHom`, so the
disjunction in the source collapses to its second alternative; it is kept in the statement because
that is the hypothesis the source offers its consumers.

## References

* [Stacks Project, Tag 0GTQ](https://stacks.math.columbia.edu/tag/0GTQ)
* [Stacks Project, Tag 0GTP](https://stacks.math.columbia.edu/tag/0GTP)
* [Stacks Project, Tag 0891](https://stacks.math.columbia.edu/tag/0891)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Ample (unitModule isInvertibleModule_unit)

universe u v

namespace Stacks.AmpleFamilyRelativeAmple

/-- The source of a quasi-affine morphism of schemes inherits an ample family of invertible
modules from its target: the structure sheaf is ample relative to a quasi-affine morphism, so
Stacks 0GTP applies to it. -/
theorem exists_isAmpleFamily_of_isQuasiAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsQuasiAffineHom f] {I : Type v} (N : I → Y.Modules) (hN : Y.IsAmpleFamily N) :
    ∃ (J : Type v) (M : J → X.Modules), X.IsAmpleFamily M :=
  exists_isAmpleFamily f N hN ⟨unitModule X, isInvertibleModule_unit X,
    Stacks.AmplePullback.isRelativelyAmple_of_isQuasiAffineHom_of_iso_unitModule f
      (unitModule X) (Iso.refl _)⟩

/-- **Stacks 0GTQ.** Let `f : X ⟶ Y` be an affine or quasi-affine morphism of schemes. If `Y` has
an ample family of invertible modules, then so does `X`. -/
@[stacks 0GTQ]
theorem exists_isAmpleFamily_of_isAffineHom_or_isQuasiAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsAffineHom f ∨ IsQuasiAffineHom f) {I : Type v} (N : I → Y.Modules)
    (hN : Y.IsAmpleFamily N) :
    ∃ (J : Type v) (M : J → X.Modules), X.IsAmpleFamily M :=
  have : IsQuasiAffineHom f :=
    hf.elim (fun h ↦ @isQuasiAffineHom_of_isAffineHom X Y f h) id
  exists_isAmpleFamily_of_isQuasiAffineHom f N hN

end Stacks.AmpleFamilyRelativeAmple

end
