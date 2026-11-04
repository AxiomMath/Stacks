module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceAsImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite

/-!
# The graded piece of the wedge filtration, reached from its numerator

`SheafOfModules.cokernelOfLEIsoExteriorGraded` identifies `F^k⋀ⁿH/F^{k+1}⋀ⁿH` with the graded
piece `gr^k⋀ⁿH` of `SheafOfModules.exteriorGraded`. **This file says which identification it
is**: the one carrying the quotient projection out of `F^k⋀ⁿH` to the projection of `⋀ⁿH` onto
`⋀ⁿH/F^{k+1}⋀ⁿH`.

That is the compatibility a differential has to be carried along. The graded piece of a filtered
complex is reached from the step by an epimorphism (`CategoryTheory.FilteredObject.grMapπ`), so
its differential is determined by what the projection does, and every step of an identification
of graded pieces has to be known on the projection before a square involving a differential can
be checked.

## Main results

* `SheafOfModules.π_cokernelOfLEIsoExteriorGraded_hom_comp_arrow`: the identification carries the
  quotient projection to the projection onto `⋀ⁿH/F^{k+1}⋀ⁿH`.

## Implementation notes

The statement is one line and it has a module to itself, because it cannot be proved in the
module that defines `SheafOfModules.cokernelOfLEIsoExteriorGraded`. There the definition's body
is in scope and the *kernel's* check of the proof against the type exhausts the default budget;
across the module boundary the identical proof is checked in seconds. The elaborator reports
nothing either way, so the only signal is a build. The docstring of the result records which
shapes of the proof were tried.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace SheafOfModules

open MonoidalCategory

attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite

/-! The wedge-product morphisms below go out of objects `Stacks.SheafOfModules.Tensor.sheafTensor`
builds, indexed by `Stacks.SheafOfModules.Tensor.ringSheaf`, while the abelian structure their
images are taken in is indexed by `CategoryTheory.Sheaf.toRingCat`. The two are the same bundled
sheaf of rings, but `ringSheaf` is an opaque `def`, so `HasImage` is not found for such a
morphism. Making `ringSheaf` reducible for implicit-argument unification identifies the two
spellings. -/
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↑X) CommRingCat.{u}}
  {F H : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↑X) Osharp)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↑X) F)
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↑X) H)

/-- **The identification of `F^k⋀ⁿH/F^{k+1}⋀ⁿH` with `gr^k⋀ⁿH` carries the quotient projection
to the projection onto `⋀ⁿH/F^{k+1}⋀ⁿH`**, `n = k + 1 + m`: read inside that ambient quotient,
the projection of `F^k⋀ⁿH` onto the quotient by the next step, followed by the identification
with the graded piece, is the inclusion of `F^k⋀ⁿH` into `⋀ⁿH` followed by the projection.

This is the compatibility a consumer of `SheafOfModules.cokernelOfLEIsoExteriorGraded` needs:
`Limits.cokernel.π` of the inclusion of one step in the next is what the graded piece of a
*filtered complex* presents degreewise, so a statement about the numerator crosses to the
sheaf-level graded piece along this square. The inclusion of `gr^k⋀ⁿH` into `⋀ⁿH/F^{k+1}⋀ⁿH` is a
monomorphism, so the square determines the morphism onto the graded piece itself.

Two things about this statement are forced rather than chosen, and both are about the *kernel*.

It cannot be proved in the module that defines
`SheafOfModules.cokernelOfLEIsoExteriorGraded`. There the definition's body is in scope, and the
kernel's check of this proof against this type — which needs that body — exhausts the default
budget, in every shape of the proof tried: the generic compatibility applied as a term, the same
with `@[reassoc]` dropped, and the identification opened with `rw` first. Across the module
boundary the same proof is checked in seconds. The elaborator never sees the difference, and
neither does `#count_heartbeats`, which runs at `maxHeartbeats 0`: the term-mode proof takes
36,220 heartbeats there and still fails the kernel check.

And `rw` is only affordable because
`Stacks.GradedPieceImage.cokernelEpiCompIsoImageInQuotient` names the three-fold composite that
`SheafOfModules.cokernelOfLEIsoExteriorGraded` is as one constant; against the composite written
out, the same `rw` costs 193,705 heartbeats in the elaborator alone. -/
theorem π_cokernelOfLEIsoExteriorGraded_hom_comp_arrow (iF : F ⟶ H) (k m : ℕ) :
    cokernel.π (Subobject.ofLE _ _ (imageSubobject_prodWedgeHom_succ_le AF A iF k m)) ≫
        (cokernelOfLEIsoExteriorGraded AF A iF k m).hom ≫
          (imageSubobject (exteriorGradedHom AF A iF k m)).arrow =
      (imageSubobject (prodWedgeHom AF A A iF (𝟙 H) k (1 + m) ≫
          eqToHom (congrArg A.exterior.piece
            (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm))).arrow ≫
        cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m) := by
  rw [cokernelOfLEIsoExteriorGraded]
  exact Stacks.GradedPieceImage.π_cokernelEpiCompIsoImageInQuotient_hom_comp_arrow _ _ _ _ _ _ _

end SheafOfModules

end
