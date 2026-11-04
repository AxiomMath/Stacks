module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionKeyPush
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionPull
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionSourceIdealSpan

/-!
# The obstruction of Stacks 0E3V vanishes exactly when the morphism lifts

For first-order deformations `X'` of `X` and `Y'` of `Y` over `k[M]`, the class `Push(Y')`
(`Deformation.Examples.schemeMorphismObstructionPush`) equals the class `Pull(X')`
(`Deformation.Examples.schemeMorphismObstructionPull`) exactly when `f : X → Y` lifts to a morphism
`X' ⟶ Y'` over `Spec k[M]`. This is the key step of the last paragraph of the proof of
[Stacks Project, Tag 0E3V]: the obstruction `Push(Y') − Pull(X')` vanishes exactly on the pairs
along which `f` deforms.

## Main results

* `Deformation.Examples.schemeMorphismObstructionPush_eq_pull_iff`.
* `Deformation.Examples.schemeMorphismObstruction_key`: the same at the rank-one module.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Sites.Conormal (kernelIdeal)

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX) (M : FGModuleCat.{u} k)

/-- **`Push(Y') = Pull(X')` exactly when `f` lifts to `X' ⟶ Y'` over `Spec k[M]`.** -/
theorem schemeMorphismObstructionPush_eq_pull_iff
    (xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
    (yε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)) :
    schemeMorphismObstructionPush f pY M yε = schemeMorphismObstructionPull f pX pY hf M xε ↔
      Nonempty (globalLiftsOverBase f xε.1 yε.1 (eqToHom (yε.2.trans xε.2.symm))) :=
  schemeMorphismObstructionPush_eq_iff hf xε yε (sourceIdealGenerator_span f pY yε) _
    (schemeMorphismPullExtension_idealBijective f pX pY hf M xε)
    (schemeMorphismPullExtension_idealIncl f pX pY hf M xε) _
    (schemeMorphismPullBaseMap_comp_reduction f pX pY hf M xε)

/-- **The key equivalence of the last paragraph of the proof of Stacks 0E3V**, at the rank-one
coordinate module `k`: for first-order deformations `X'` of `X` and `Y'` of `Y` over the dual
numbers, `Push(Y') = Pull(X')` exactly when `f` lifts to a morphism `X' ⟶ Y'` over the dual
numbers. -/
theorem schemeMorphismObstruction_key :
    ∀ (xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj (FGModuleCat.of k (ULift.{u} k))))
      (yε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj (FGModuleCat.of k (ULift.{u} k)))),
      schemeMorphismObstructionPush f pY _ yε = schemeMorphismObstructionPull f pX pY hf _ xε ↔
        Nonempty (globalLiftsOverBase f xε.1 yε.1 (eqToHom (yε.2.trans xε.2.symm))) :=
  fun xε yε => schemeMorphismObstructionPush_eq_pull_iff f pX pY hf _ xε yε

end Deformation.Examples

end
