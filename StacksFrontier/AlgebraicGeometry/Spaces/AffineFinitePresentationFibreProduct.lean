module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal

/-!
# Fibre products of algebraic spaces affine and of finite presentation over a base

Let `Y` be an algebraic space over `S`.  The algebraic spaces over `Y` whose structure
morphism is affine and of finite presentation are closed under fibre products over `Y`: if
`P`, `Q` and `Z` are such spaces and `c : P ⟶ Q`, `σ : Z ⟶ Q` are morphisms over `Y`, then
`P ×_Q Z` is again affine and of finite presentation over `Y`.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_of_comp`: a morphism whose composite with a
  quasi-separated morphism locally of finite type is of finite presentation is itself of finite
  presentation.
* `AlgebraicGeometry.Space.isFinitePresentation_id`: an identity of an algebraic space is of
  finite presentation.
* `AlgebraicGeometry.Space.isAffineHom_comp_of_isPullback` and
  `AlgebraicGeometry.Space.isFinitePresentation_comp_of_isPullback`: the fibre product over
  `Q` of two spaces affine (resp. of finite presentation) over `Y` is affine (resp. of finite
  presentation) over `Y`, when `Q ⟶ Y` is affine (resp. of finite presentation).

## References

* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
* [Stacks Project, Tag 05WT](https://stacks.math.columbia.edu/tag/05WT)
* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
* [Stacks Project, Tag 0DPW](https://stacks.math.columbia.edu/tag/0DPW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If `f ≫ g` is of finite presentation and `g` is locally of finite type and quasi-separated,
then `f` is of finite presentation. -/
theorem isFinitePresentation_of_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H) (f : F ⟶ G) (g : G ⟶ H)
    (hfg : IsFinitePresentation B S hS (f ≫ g)) (hg : IsLocallyOfFiniteType B S hS g)
    (hgqs : IsQuasiSeparated B S hS g) :
    IsFinitePresentation B S hS f :=
  ⟨isLocallyOfFinitePresentation_of_comp B S hS hF hG hH f g hfg.1 hg,
    isQuasiCompact_of_comp_of_isQuasiSeparated B S hS f g hF hH hfg.2.1 hgqs,
    isQuasiSeparated_of_comp B S hS f g hfg.2.2⟩

/-- An identity morphism of an algebraic space over `S` is of finite presentation. -/
theorem isFinitePresentation_id {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) : IsFinitePresentation B S hS (𝟙 X) :=
  ⟨isLocallyOfFinitePresentation_id B S hS hX, isQuasiCompact_of_isIso B S hS (𝟙 X),
    isQuasiSeparated_of_isSeparated B S hS (isSeparated_of_isIso B S hS (𝟙 X))⟩

variable {B S hS}
variable {W P Q Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : W ⟶ P} {b : W ⟶ Z} {c : P ⟶ Q} {σ : Z ⟶ Q}
    {pP : P ⟶ Y} {pQ : Q ⟶ Y} {pZ : Z ⟶ Y}

/-- A fibre product over `Q` of spaces affine over `Y` is affine over `Y`, when `Q ⟶ Y` is
affine. -/
theorem isAffineHom_comp_of_isPullback (hQ : IsAlgebraicSpace B S hS Q)
    (hY : IsAlgebraicSpace B S hS Y) (sq : IsPullback a b c σ) (hc : c ≫ pQ = pP)
    (hP : IsAffineHom B S hS pP) (hQY : IsAffineHom B S hS pQ) (hZ : IsAffineHom B S hS pZ) :
    IsAffineHom B S hS (b ≫ pZ) := by
  have hcaff : IsAffineHom B S hS c :=
    isAffineHom_of_isAffineHom_comp_of_isSeparated B S hS c pQ (hc ▸ hP)
      (isSeparated_of_isAffineHom B S hS pQ hQ hY hQY)
  exact isAffineHom_comp B S hS _ _ (IsAffineHom.of_isPullback sq hcaff) hZ

/-- A fibre product over `Q` of spaces of finite presentation over `Y` is of finite
presentation over `Y`, when `Q ⟶ Y` is of finite presentation. -/
theorem isFinitePresentation_comp_of_isPullback (hW : IsAlgebraicSpace B S hS W)
    (hPa : IsAlgebraicSpace B S hS P) (hQ : IsAlgebraicSpace B S hS Q)
    (hZa : IsAlgebraicSpace B S hS Z) (hY : IsAlgebraicSpace B S hS Y)
    (sq : IsPullback a b c σ) (hc : c ≫ pQ = pP)
    (hP : IsFinitePresentation B S hS pP) (hQY : IsFinitePresentation B S hS pQ)
    (hZ : IsFinitePresentation B S hS pZ) :
    IsFinitePresentation B S hS (b ≫ pZ) := by
  have hcfp : IsFinitePresentation B S hS c :=
    isFinitePresentation_of_comp B S hS hPa hQ hY c pQ (hc ▸ hP)
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hQY.1) hQY.2.2
  exact isFinitePresentation_comp B S hS hW hZa hY _ _
    (IsFinitePresentation.of_isPullback B S hS hW hPa hZa hQ sq hcfp) hZ

end AlgebraicGeometry.Space

end
