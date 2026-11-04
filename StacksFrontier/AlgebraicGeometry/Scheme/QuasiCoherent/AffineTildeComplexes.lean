module

public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 01I9 on complexes, and the factorisation through the homotopy category

Let `f : R ⟶ S` be a homomorphism of commutative rings. Degreewise, the pullback along `Spec f`
of a complex of associated sheaves is the complex of sheaves associated to the extension of
scalars,

  `f^*(M̃^•) ≅ (S ⊗_R M^•)~`,

which is [Stacks, Tag 01I9] — already available on single modules as
`AlgebraicGeometry.pullbackTildeIso` — applied degreewise. This file also carries one generic
fact about additive functors and homotopy categories, `mapHomologicalComplexCompFactors`.

## Why these declarations live here and not with the comparison square they serve

Both are inputs to the affine comparison square of [Stacks, Tag 08DW] part (2),
`Lf^*(M̃^•) ≅ (S ⊗ᴸ_R M^•)~`, which the library proves twice: at the locally small model of the
derived category in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/AffinePullbackComparison.lean`, and at
`CategoryTheory.HasDerivedCategory.standard` in
`StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentStandardModel.lean`. Those two files
*cannot* import one another: the first carries
`StacksFrontier.Homology.DerivedCategory.LocallySmall`, whose `HasDerivedCategory` declarations are
global instances, and the second fixes the standard model by a file-level
`attribute [local instance]`, which a global instance would beat. Since
`CategoryTheory.HasDerivedCategory` carries the localized category as *data*, almost every
declaration of that comparison genuinely differs between the two files — the two `DerivedCategory`
types are not equal, and at the locally small model the morphisms land in `Type u` where the
standard model puts them in `Type (u + 1)`.

The declarations below are the exception: neither mentions a derived category at all, so each is
one declaration serving both developments rather than two. This module is therefore imported by
both, and its own imports are confined to ones both files already had, so that
`StacksFrontier.Homology.DerivedCategory.LocallySmall` stays out of its closure and the standard-model
file can import it.

## Main definitions

* `Stacks.DerivedPullback.mapHomologicalComplexCompFactors` — if a functor out of complexes
  factors through the homotopy category, then so does its precomposition with a degreewise
  additive functor.
* `AlgebraicGeometry.tildePullbackComplexIso` — **[Stacks, Tag 01I9] on complexes.**

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace Stacks.DerivedPullback

/-! ### A functor on complexes that factors through the homotopy category -/

/-- If a functor `H` out of the category of complexes of `B` factors through the homotopy
category, then so does `G^• ⋙ H` for any additive `G : A ⥤ B`, by the degreewise functor on
homotopy categories. -/
def mapHomologicalComplexCompFactors
    {A : Type u₁} [Category.{v₁} A] [Preadditive A]
    {B : Type u₂} [Category.{v₂} B] [Preadditive B]
    {D : Type u₃} [Category.{v₃} D]
    (G : A ⥤ B) [G.Additive]
    (H : CochainComplex B ℤ ⥤ D) (Hh : HomotopyCategory B (ComplexShape.up ℤ) ⥤ D)
    (e : HomotopyCategory.quotient B (ComplexShape.up ℤ) ⋙ Hh ≅ H) :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Hh) ≅
      G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ H :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) Hh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (G.mapHomologicalComplex (ComplexShape.up ℤ)) e

end Stacks.DerivedPullback

namespace AlgebraicGeometry

/-! ### Stacks 01I9 on complexes -/

variable (R S : CommRingCat.{u}) (f : R ⟶ S)

/-- Extension of scalars is additive, being a left adjoint. -/
local instance extendScalarsSpec_additive :
    (ModuleCat.extendScalars.{u, u, u} f.hom).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom).left_adjoint_additive

/-- **Stacks 01I9 on complexes.** Degreewise, the pullback along `Spec f` of a complex of
associated sheaves is the complex of sheaves associated to the extension of scalars. -/
@[ega "III 6.4.4"]
def tildePullbackComplexIso :
    (tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (Scheme.Modules.pullback (Spec.map f)).mapHomologicalComplex
          (ComplexShape.up ℤ) ≅
      (ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (tilde.functor S).mapHomologicalComplex (ComplexShape.up ℤ) :=
  (Functor.mapHomologicalComplexCompIso
      (Iso.refl (tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map f)))
      (ComplexShape.up ℤ)) ≪≫
    NatIso.mapHomologicalComplex (pullbackTildeIso R S f) (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ModuleCat.extendScalars.{u, u, u} f.hom ⋙ tilde.functor S))
      (ComplexShape.up ℤ)).symm

end AlgebraicGeometry

end
