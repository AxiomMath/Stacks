module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.RingTheory.Dualizing.DerivedHomAnyModel

@[expose] public noncomputable section

/-!
# Derived Hom along a ring homomorphism is an exact functor, at arbitrary chosen models

`Dualizing.AnyModel.restrictScalarsDerived_adj_derivedHom` ([stacks 0A70], at arbitrary chosen
models of the two derived categories) exhibits `RHom_A(B, -) : D(A) ⥤ D(B)` as the right adjoint of
the functor induced by restriction of scalars. The right adjoint of an exact functor of
triangulated categories is exact, so `RHom_A(B, -)` is exact as well — but neither the
compatibility with the shift nor the exactness is available by synthesis, for two reasons that are
both bookkeeping:

* the adjunction is only known to *exist* (`Nonempty`), so the `CommShift` structure it induces on
  `RHom_A(B, -)` through `CategoryTheory.Adjunction.rightAdjointCommShift` cannot be an instance;
* `CategoryTheory.Functor.mapDerivedCategory.IsTriangulated` needs
  `PreservesFiniteLimits`/`PreservesFiniteColimits` of `ModuleCat.restrictScalars f`, which are
  `local instance`s in `StacksFrontier/RingTheory/Dualizing/DerivedHomAnyModel.lean` and so are
  invisible to a consumer.

This file records the conclusion once, so that a consumer gets both facts from a single `obtain`.
That shape is deliberate: where two chosen models of one derived category are in scope,
destructuring with `obtain` avoids the instance searches that a dot-projection would run.

## Main results

* `StacksDraft.CompactDevissage.exists_commShift_isTriangulated_derivedHom` — `RHom_A(B, -)`
  carries a compatibility with the shift for which it is an exact functor of triangulated
  categories, between arbitrary chosen models of `D(A)` and `D(B)`.

## References

* [The Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Functor

namespace StacksDraft.CompactDevissage

universe u v u' w w'

/-- **Derived coextension of scalars is exact.** For a homomorphism of commutative rings
`f : A →+* B` and arbitrary chosen models of `D(A)` and `D(B)`, the functor
`RHom_A(B, -) : D(A) ⥤ D(B)` of `Dualizing.AnyModel.derivedHom` carries a compatibility with the
shift by `ℤ` for which it is an exact functor of triangulated categories.

Both halves come from `Dualizing.AnyModel.restrictScalarsDerived_adj_derivedHom`, which is
[stacks 0A70] at arbitrary models: restriction of scalars is exact, hence so is the functor it
induces on derived categories, and the right adjoint of an exact functor is exact. The two facts
are bundled because the second only makes sense for the shift structure produced by the first, and
that structure depends on the chosen adjunction. -/
theorem exists_commShift_isTriangulated_derivedHom {A : Type u} {B : Type u'}
    [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{max v u u'} A)]
    [HasDerivedCategory.{w'} (ModuleCat.{max v u u'} B)] (f : A →+* B) :
    ∃ h : (Dualizing.AnyModel.derivedHom.{u, v, u', w, w'} f).CommShift ℤ,
      letI := h; (Dualizing.AnyModel.derivedHom.{u, v, u', w, w'} f).IsTriangulated := by
  have : Limits.PreservesFiniteLimits (ModuleCat.restrictScalars.{max v u u'} f) :=
    ⟨fun _ _ _ => ⟨inferInstance⟩⟩
  have : Limits.PreservesFiniteColimits (ModuleCat.restrictScalars.{max v u u'} f) :=
    ⟨fun _ _ _ => ⟨inferInstance⟩⟩
  obtain ⟨adj⟩ := Dualizing.AnyModel.restrictScalarsDerived_adj_derivedHom.{u, v, u', w, w'} f
  let hcs : (Dualizing.AnyModel.derivedHom.{u, v, u', w, w'} f).CommShift ℤ :=
    adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  exact ⟨hcs, adj.isTriangulated_rightAdjoint⟩

end StacksDraft.CompactDevissage

end
