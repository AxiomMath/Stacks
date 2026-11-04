module

public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# The morphism of triangles induced by a morphism of shift-compatible functors

For a natural transformation `τ : F ⟶ G` compatible with the shift, between functors that commute
with the shift, `StacksDraft.CompactDevissage.mapTriangleHom τ T` is the morphism of triangles
`F.mapTriangle.obj T ⟶ G.mapTriangle.obj T` whose three components are given by `τ`. Unlike
`CategoryTheory.Functor.mapTriangleIso`, it does not require `τ` to be an isomorphism.

## Main definitions

* `StacksDraft.CompactDevissage.mapTriangleHom`: the morphism of triangles induced by `τ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace StacksDraft.CompactDevissage

universe v v' u u'

section Shift

variable {D : Type u} [Category.{v} D] [HasShift D ℤ]
  {D' : Type u'} [Category.{v'} D'] [HasShift D' ℤ]
  {F G : D ⥤ D'} [F.CommShift ℤ] [G.CommShift ℤ]
  (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]

/-- The morphism of triangles `F.mapTriangle.obj T ⟶ G.mapTriangle.obj T` induced by a morphism
`τ : F ⟶ G` of functors compatible with the shift; all three components are `τ` itself. -/
def mapTriangleHom (T : Triangle D) : F.mapTriangle.obj T ⟶ G.mapTriangle.obj T where
  hom₁ := τ.app _
  hom₂ := τ.app _
  hom₃ := τ.app _
  comm₁ := τ.naturality _
  comm₂ := τ.naturality _
  comm₃ :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => F.map T.mor₃ ≫ z)
          (NatTrans.shift_app_comm τ (1 : ℤ) T.obj₁)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁)
              (τ.naturality T.mor₃)).trans (Category.assoc _ _ _))))

end Shift

end StacksDraft.CompactDevissage
