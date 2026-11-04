module

public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced

/-!
# A finite reduced scheme over a perfect field is étale

Let `k` be a perfect field and `X` a reduced scheme finite over `Spec k`. Then `X → Spec k` is
étale. A reduced scheme over a perfect field is geometrically reduced ([Stacks, Tag 020I]), a
finite morphism is proper, and the global functions of a geometrically reduced proper scheme over
a field form a finite étale algebra ([Stacks, Tag 0BUG]); since `X` is affine, that is étaleness
of `X → Spec k`.

This is the step of the proof of [Stacks, Tag 03UG] (Step 3) which removes a finite closed set of
points from a curve over a finite field: the reduced induced structure on it is finite étale over
`k`.

## Main results

* `Stacks.AlgebraicGeometry.ProperSectionsGeom.etale_of_isFinite_of_isReduced`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.AlgebraicGeometry.ProperSectionsGeom

/-- **A finite reduced scheme over a perfect field is étale over it.** -/
theorem etale_of_isFinite_of_isReduced {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsFinite f] [IsReduced X] : Etale f := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  obtain ⟨h, -⟩ := etale_globalSections_of_geometricallyReduced k f
  have : IsAffine X := isAffine_of_isAffineHom f
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
  have e : f.appTop.hom =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.comp (Scheme.ΓSpecIso (.of k)).hom.hom := by
    rw [← CommRingCat.hom_comp, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [e]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _))
    ((RingHom.etale_algebraMap).2 h)

end Stacks.AlgebraicGeometry.ProperSectionsGeom
