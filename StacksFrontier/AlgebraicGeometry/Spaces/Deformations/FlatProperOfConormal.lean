module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.ThickeningProperties
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.EtaleLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UnramifiedLocalAtSource
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.Properties
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Etale
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Flat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Smooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Syntomic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.CartesianFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SeparatedAndClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.FirstOrderThickeningFlatConormal
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# A morphism of first-order thickenings with flat, proper special fibre

Let
```
X --⊆--→ X'
|f       |g
↓        ↓
Y --⊆--→ Y'
```
be a morphism of first-order thickenings of algebraic spaces over a scheme `S` whose canonical
map `f^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of conormal modules of [Stacks Project, Tag 04CP] is an
isomorphism.  If `f` is flat, proper and of finite presentation, then so is `g`, and the square
is cartesian.

This is the last paragraph of the proof of [Stacks Project, Tag 0D3X]: once the first-order
thickening `X₁ ⊂ X` over `Spec(R₁) ⊂ Spec(lim Rₙ)` has been built, "`X → Spec(lim Rₙ)` is flat
by the already used More on Morphisms of Spaces, Lemma 06BH.  By More on Morphisms of Spaces,
Lemma 0CG6 we see that `X → Spec(lim Rₙ)` is proper and of finite presentation."  Flatness and
the cartesian square are (2) ⟹ (1) of [Stacks Project, Tag 06BH]; the cartesian square makes the
situation a cartesian finite-order deformation in the sense of
`AlgebraicGeometry.Space.CartesianFiniteOrderDeformation`, over the thickening `Y ⊂ Y'` itself,
and properness and local finite presentation then pass from `f` to `g` by
[Stacks Project, Tag 0CG6], parts 0CGS and 0CGK.  Quasi-compactness and quasi-separatedness,
the two remaining conditions of finite presentation, follow from properness.

## Main results

* `AlgebraicGeometry.Space.cartesianFiniteOrderDeformationOfFirstOrder`: the cartesian
  finite-order deformation attached to a cartesian morphism of first-order thickenings with flat
  ambient morphism.
* `AlgebraicGeometry.Space.isFlat_isProper_isFinitePresentation_of_isIso_conormalMapOfImmersions`:
  the conclusion above.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
* [Stacks Project, Tag 0CG6](https://stacks.math.columbia.edu/tag/0CG6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' Y' : AlgebraicSpaces B S hS} (X : ClosedSubspaces B S hS X'.1)
    (Y : ClosedSubspaces B S hS Y'.1) (g : X' ⟶ Y')
    (f : (⟨X.1.toFunctor, X.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))

/-- **The cartesian finite-order deformation of a cartesian morphism of first-order
thickenings.**  A morphism `(f, g) : (X ⊆ X') → (Y ⊆ Y')` of first-order thickenings whose square
is cartesian and whose ambient morphism `g` is flat is a cartesian finite-order deformation over
the thickening `Y ⊆ Y'` itself, the structure morphisms of the targets being identities. -/
def cartesianFiniteOrderDeformationOfFirstOrder
    (hX : IsFirstOrderThickening B S hS X' X.1) (hY : IsFirstOrderThickening B S hS Y' Y.1)
    (hg : IsFlat B S hS g.hom)
    (hcart : IsPullback (subspaceInclusion B S hS X' X) f g (subspaceInclusion B S hS Y' Y)) :
    CartesianFiniteOrderDeformation B S hS where
  X' := X'
  Y' := Y'
  B' := Y'
  X := X.1
  Y := Y.1
  B := Y.1
  base_finiteOrder := hY.isFiniteOrderThickening
  source_thickening := hX.isThickening
  target_thickening := hY.isThickening
  f := f.hom
  f' := g.hom
  g := 𝟙 _
  g' := 𝟙 _
  comm_f := (congrArg (fun m => m.hom) hcart.w).symm
  comm_g := by simp
  isPullback_X := by
    rw [Category.comp_id, Category.comp_id]
    exact AlgebraicSpaces.isPullback_hom B S hS hcart
  isPullback_Y := IsPullback.of_vert_isIso ⟨by simp⟩
  flat_X' := by simpa only [Category.comp_id] using hg

/-- **The last step of the proof of Stacks 0D3X.**  Let `(f, g) : (X ⊆ X') → (Y ⊆ Y')` be a
morphism of first-order thickenings of algebraic spaces whose canonical map
`f^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of conormal modules is an isomorphism.  If `f` is flat, proper and of
finite presentation, then `g` is flat, proper and of finite presentation, and `X = Y ×_{Y'} X'`.

Flatness and the cartesian square are (2) ⟹ (1) of Stacks 06BH; properness and local finite
presentation are carried from `f` to `g` by Stacks 0CG6, parts 0CGS and 0CGK, at the cartesian
finite-order deformation `AlgebraicGeometry.Space.cartesianFiniteOrderDeformationOfFirstOrder`;
quasi-compactness and quasi-separatedness of `g` follow from its properness. -/
theorem isFlat_isProper_isFinitePresentation_of_isIso_conormalMapOfImmersions
    (hsq : subspaceInclusion B S hS X' X ≫ g = f ≫ subspaceInclusion B S hS Y' Y)
    (hX : IsFirstOrderThickening B S hS X' X.1) (hY : IsFirstOrderThickening B S hS Y' Y.1)
    (hflat : IsFlat B S hS f.hom) (hproper : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (h : IsIso (conormalMapOfImmersions B S hS (subspaceInclusion B S hS X' X)
        (subspaceInclusion B S hS Y' Y) f g (isImmersion_subspaceInclusion B S hS X' X)
        (isImmersion_subspaceInclusion B S hS Y' Y) hsq)) :
    IsFlat B S hS g.hom ∧ IsProper B S hS g.hom ∧ IsFinitePresentation B S hS g.hom ∧
      IsPullback (subspaceInclusion B S hS X' X) f g (subspaceInclusion B S hS Y' Y) := by
  obtain ⟨hg, hcart⟩ :=
    isFlat_and_isPullback_of_isIso_conormalMapOfImmersions B S hS X Y g f hsq hX hY hflat h
  let D := cartesianFiniteOrderDeformationOfFirstOrder B S hS X Y g f hX hY hg hcart
  have hgproper : IsProper B S hS g.hom := D.isProper_iff.1 hproper
  exact ⟨hg, hgproper, ⟨D.isLocallyOfFinitePresentation_iff.1 hfp.1, hgproper.2.1.2,
    isQuasiSeparated_of_isSeparated B S hS hgproper.1⟩, hcart⟩

end AlgebraicGeometry.Space

end
