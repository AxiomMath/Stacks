module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpacesEtaleIdentification
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineOfAffineReduction
import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReductionSite
import StacksFrontier.AlgebraicGeometry.FormalSpace.LiftAlongAffineBase
import StacksFrontier.AlgebraicGeometry.FormalSpace.SpacesEtaleIdentificationSupplement
import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction
import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeOnReductionsChartMaps
import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionExistence

/-!
# The affine étale site of a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B` and `X` a formal algebraic space over `S`
with reduction `X_red`. By Stacks 0DEA, part (3), `X_{affine, étale}` is the affine étale site
of `X_red`. **Stacks 0DEH** identifies it with the category `C` whose objects are the morphisms
`φ : U ⟶ X` of formal algebraic spaces with `U` an affine formal algebraic space and `φ`
representable by algebraic spaces and étale
(`AlgebraicGeometry.FormalSpace.AffineEtaleFormalCharts`), the equivalence being `U ↦ U_red`, as
the proof of Stacks 0DEJ uses it.

## Main definitions

* `AlgebraicGeometry.FormalSpace.affineEtaleChartsToSpacesEtale`: the functor
  `(U ⟶ X) ↦ (U_red ⟶ X_red)` from `C` to `X_{spaces, étale}`, the comparison functor of
  Stacks 0DEG restricted to `C`.
* `AlgebraicGeometry.FormalSpace.Reduction.affineEtaleToSpacesEtale`: the fully faithful
  inclusion of `X_{affine, étale}` into `X_{spaces, étale}` (Stacks 03G1).
* `AlgebraicGeometry.FormalSpace.affineEtaleReductionFunctor`: the functor `U ↦ U_red` from `C`
  to `X_{affine, étale}`, and `AlgebraicGeometry.FormalSpace.affineEtaleReductionFunctorCompIso`
  its compatibility with the two functors above.
* `AlgebraicGeometry.FormalSpace.affineEtaleReductionEquivalence`: **Stacks 0DEH**.

## Main results

* `AlgebraicGeometry.FormalSpace.affineEtaleChartsToSpacesEtale_obj_mem_essImage`: the reduction
  of an affine formal algebraic space is affine (the easy half of Stacks 0DE8), so the functor
  `U ↦ U_red` lands in `X_{affine, étale}`.
* `AlgebraicGeometry.FormalSpace.exists_affineEtaleChartsToSpacesEtale_obj_iso`: every object of
  `X_{affine, étale}` is the reduction of an object of `C` — Stacks 0DEG produces a formal
  algebraic space representable étale over `X` with the given reduction, and it is affine by
  Stacks 0DE8.
* `AlgebraicGeometry.FormalSpace.affineEtaleReductionFunctor_isEquivalence`: **Stacks 0DEH**.

## Implementation notes

The proof is the source's: combine Stacks 0DEG and Stacks 0DE8. The functor `U ↦ U_red` is the
comparison functor of Stacks 0DEG on `C`, lifted along the fully faithful inclusion of
`X_{affine, étale}` into `X_{spaces, étale}` by `CategoryTheory.Functor.essImage.liftFunctor`;
so on objects it is a chosen affine étale chart isomorphic to `U_red ⟶ X_red`, and the
isomorphism is recorded by `AlgebraicGeometry.FormalSpace.affineEtaleReductionFunctorCompIso`.
As in Stacks 0DEA, the reduction of `X` is a given datum
(`AlgebraicGeometry.FormalSpace.Reduction`), which Stacks 0AIN supplies.

## References

* [Stacks Project, Tag 0DEH](https://stacks.math.columbia.edu/tag/0DEH)
* [Stacks Project, Tag 0DEG](https://stacks.math.columbia.edu/tag/0DEG)
* [Stacks Project, Tag 0DE8](https://stacks.math.columbia.edu/tag/0DE8)
* [Stacks Project, Tag 0DEA](https://stacks.math.columbia.edu/tag/0DEA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The objects of the category of Stacks 0DEH are among those of the category of Stacks 0DEG:
an affine formal algebraic space is a formal algebraic space. -/
theorem isAffineEtaleFormalChart_le_isRepresentableEtaleFormalSpaceOver (X : FppfSheaf B S hS) :
    IsAffineEtaleFormalChart B S hS X ≤ IsRepresentableEtaleFormalSpaceOver X :=
  fun _ hU ↦ ⟨isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hU.1, hU.2⟩

/-- The functor `(U ⟶ X) ↦ (U_red ⟶ X_red)` from the category of Stacks 0DEH to
`X_{spaces, étale}`: the comparison functor of Stacks 0DEG restricted to the affine formal
algebraic spaces representable étale over `X`. -/
def affineEtaleChartsToSpacesEtale {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    (R : Reduction B S hS X) : AffineEtaleFormalCharts B S hS X ⥤ R.SpacesEtale :=
  ObjectProperty.ιOfLE (isAffineEtaleFormalChart_le_isRepresentableEtaleFormalSpaceOver X) ⋙
    spacesEtaleComparison hX R

/-- The inclusion of `X_{affine, étale}` into `X_{spaces, étale}`: an affine étale scheme chart
of the reduction is an algebraic space étale over it (Stacks 03G1). -/
def Reduction.affineEtaleToSpacesEtale {X : FppfSheaf B S hS} (R : Reduction B S hS X) :
    R.AffineEtale ⥤ R.SpacesEtale :=
  Space.AffineEtale.inclusion B S hS R.space.obj ⋙ Space.comparisonFunctor B S hS R.space

/-- The inclusion of `X_{affine, étale}` into `X_{spaces, étale}` is full. -/
instance Reduction.full_affineEtaleToSpacesEtale {X : FppfSheaf B S hS}
    (R : Reduction B S hS X) : R.affineEtaleToSpacesEtale.Full := by
  have := Space.comparisonFunctor_full B S hS R.space
  dsimp only [Reduction.affineEtaleToSpacesEtale]
  infer_instance

/-- The inclusion of `X_{affine, étale}` into `X_{spaces, étale}` is faithful. -/
instance Reduction.faithful_affineEtaleToSpacesEtale {X : FppfSheaf B S hS}
    (R : Reduction B S hS X) : R.affineEtaleToSpacesEtale.Faithful := by
  have := Space.comparisonFunctor_faithful B S hS R.space
  dsimp only [Reduction.affineEtaleToSpacesEtale]
  infer_instance

/-- The object of the category of Stacks 0DEG underlying an object of the category of
Stacks 0DEH. -/
abbrev AffineEtaleFormalCharts.toRepresentableEtale {X : FppfSheaf B S hS}
    (U : AffineEtaleFormalCharts B S hS X) : RepresentableEtaleFormalSpacesOver X :=
  (ObjectProperty.ιOfLE (isAffineEtaleFormalChart_le_isRepresentableEtaleFormalSpaceOver X)).obj U

/-- **The reduction of an object of the category of Stacks 0DEH is affine.** For
`φ : U ⟶ X` with `U` an affine formal algebraic space and `φ` representable by algebraic spaces
and étale, the object `U_red ⟶ X_red` of `X_{spaces, étale}` comes from an affine étale scheme
chart of `X_red`, i.e. from an object of `X_{affine, étale}`. -/
theorem affineEtaleChartsToSpacesEtale_obj_mem_essImage {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X)
    (U : AffineEtaleFormalCharts B S hS X) :
    R.affineEtaleToSpacesEtale.essImage ((affineEtaleChartsToSpacesEtale hX R).obj U) := by
  let RU := objReduction hX R U.toRepresentableEtale
  obtain ⟨T, hTaff, ⟨e'⟩⟩ := exists_isAffine_uliftYoneda_iso_of_isAffineFormalAlgebraicSpace
    B S hS RU.isReduction U.property.1
  let e : schemeSpace T ≅ RU.space := (ObjectProperty.fullyFaithfulι _).preimageIso
    ((liftFullyFaithful B S hS).preimageIso e')
  let f : schemeSpace T ⟶ R.space := e.hom ≫ RU.map R U.obj.hom
  have hetale : Space.IsEtale B S hS (RU.map R U.obj.hom).hom :=
    ((affineEtaleChartsToSpacesEtale hX R).obj U).property
  let : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have he : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf e.hom.hom := by
    have : IsIso e.hom.hom := Functor.map_isIso (ObjectProperty.ι _) e.hom
    refine ⟨Functor.relativelyRepresentable.of_isIso yoneda e.hom.hom,
      fun A C g fst snd hpb ↦ ?_⟩
    have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
    have : IsIso snd := Functor.FullyFaithful.isIso_of_isIso_map Yoneda.fullyFaithful snd
    show Etale ((BigFppfOver.toScheme B S hS).map snd)
    infer_instance
  let V : R.AffineEtale := ⟨⟨CostructuredArrow.mk f.hom, hetale T e.hom.hom he⟩, hTaff⟩
  exact ⟨V, ⟨ObjectProperty.isoMk _ (Over.isoMk e rfl)⟩⟩

/-- **The functor `U ↦ U_red` of Stacks 0DEH**, from the category of the morphisms
`φ : U ⟶ X` with `U` an affine formal algebraic space and `φ` representable by algebraic
spaces and étale to `X_{affine, étale} = X_{red, affine, étale}`. It sends `φ` to the affine
étale scheme chart of `X_red` given by the reduction `U_red ⟶ X_red` (which is the fibre
product `U ×_X X_red`, Stacks 0GB7): it is the comparison functor of Stacks 0DEG, which lands in
the affine part of `X_{spaces, étale}` on these objects
(`AlgebraicGeometry.FormalSpace.affineEtaleChartsToSpacesEtale_obj_mem_essImage`), lifted
along the fully faithful inclusion of `X_{affine, étale}` into `X_{spaces, étale}`. Its
composite with that inclusion is the functor `(U ⟶ X) ↦ (U_red ⟶ X_red)`, by
`AlgebraicGeometry.FormalSpace.affineEtaleReductionFunctorCompIso`. -/
def affineEtaleReductionFunctor {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    (R : Reduction B S hS X) : AffineEtaleFormalCharts B S hS X ⥤ R.AffineEtale :=
  Functor.essImage.liftFunctor (affineEtaleChartsToSpacesEtale hX R) R.affineEtaleToSpacesEtale
    (affineEtaleChartsToSpacesEtale_obj_mem_essImage hX R)

/-- The functor `U ↦ U_red` of Stacks 0DEH, followed by the inclusion of `X_{affine, étale}`
into `X_{spaces, étale}`, is the functor `(U ⟶ X) ↦ (U_red ⟶ X_red)` of Stacks 0DEG on the
objects of Stacks 0DEH. -/
def affineEtaleReductionFunctorCompIso {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X) :
    affineEtaleReductionFunctor hX R ⋙ R.affineEtaleToSpacesEtale ≅
      affineEtaleChartsToSpacesEtale hX R :=
  Functor.essImage.liftFunctorCompIso _ _ _

/-! ### Stacks 0DEH -/

/-- The functor `(U ⟶ X) ↦ (U_red ⟶ X_red)` from the category of Stacks 0DEH to
`X_{spaces, étale}` is full: it is the restriction of the comparison functor of Stacks 0DEG
to a full subcategory. -/
theorem full_affineEtaleChartsToSpacesEtale {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X) :
    (affineEtaleChartsToSpacesEtale hX R).Full := by
  have := full_spacesEtaleComparison hX R
  dsimp only [affineEtaleChartsToSpacesEtale]
  infer_instance

/-- The functor `(U ⟶ X) ↦ (U_red ⟶ X_red)` from the category of Stacks 0DEH to
`X_{spaces, étale}` is faithful. -/
theorem faithful_affineEtaleChartsToSpacesEtale {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X) :
    (affineEtaleChartsToSpacesEtale hX R).Faithful := by
  have := faithful_spacesEtaleComparison hX R
  dsimp only [affineEtaleChartsToSpacesEtale]
  infer_instance

/-- **Every object of `X_{affine, étale}` is the reduction of an affine formal algebraic space
representable étale over `X`.** The quasi-inverse of Stacks 0DEG produces, for an affine étale
scheme chart `V ⟶ X_red`, a formal algebraic space `U` representable étale over `X` whose
reduction is `V`; since `V` is affine, `U` is an affine formal algebraic space by Stacks 0DE8. -/
theorem exists_affineEtaleChartsToSpacesEtale_obj_iso {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X) (V : R.AffineEtale) :
    ∃ U : AffineEtaleFormalCharts B S hS X,
      Nonempty ((affineEtaleChartsToSpacesEtale hX R).obj U ≅
        R.affineEtaleToSpacesEtale.obj V) := by
  have := essSurj_spacesEtaleComparison hX R
  obtain ⟨U₀, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := spacesEtaleComparison hX R)
    (R.affineEtaleToSpacesEtale.obj V)
  let RU := objReduction hX R U₀
  let e₁ : RU.space ≅ schemeSpace ((Space.SmallEtale.toOver B S hS R.space.obj).obj V.obj) :=
    (Over.forget _).mapIso ((ObjectProperty.ι _).mapIso e)
  let e₂ : uliftYoneda.{u + 1}.obj ((Space.SmallEtale.toOver B S hS R.space.obj).obj V.obj) ≅
      (liftSheaf B S hS RU.space).obj :=
    Functor.isoWhiskerRight ((ObjectProperty.ι _).mapIso e₁.symm) uliftFunctor.{u + 1}
  have haff : IsAffineFormalAlgebraicSpace B S hS U₀.obj.left :=
    (isAffineFormalAlgebraicSpace_iff_isAffine_reduction B S hS U₀.property.1
      RU.isReduction).mpr ⟨_, V.property, ⟨e₂⟩⟩
  exact ⟨⟨U₀.obj, haff, U₀.property.2⟩, ⟨e⟩⟩

/-- **Stacks 0DEH.** Let `X` be a formal algebraic space over `S`. The functor `U ↦ U_red` is an
equivalence from the category of the morphisms `φ : U ⟶ X` of formal algebraic spaces with
`U` an affine formal algebraic space and `φ` representable by algebraic spaces and étale to
`X_{affine, étale}`. -/
theorem affineEtaleReductionFunctor_isEquivalence {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X) :
    (affineEtaleReductionFunctor hX R).IsEquivalence := by
  have := full_affineEtaleChartsToSpacesEtale hX R
  have := faithful_affineEtaleChartsToSpacesEtale hX R
  have : (affineEtaleReductionFunctor hX R).Faithful :=
    Functor.Faithful.of_comp_iso (affineEtaleReductionFunctorCompIso hX R)
  have : (affineEtaleReductionFunctor hX R).Full :=
    Functor.Full.of_comp_faithful_iso (affineEtaleReductionFunctorCompIso hX R)
  have : (affineEtaleReductionFunctor hX R).EssSurj := ⟨fun V ↦ by
    obtain ⟨U, ⟨e⟩⟩ := exists_affineEtaleChartsToSpacesEtale_obj_iso hX R V
    exact ⟨U, ⟨R.affineEtaleToSpacesEtale.preimageIso
      ((affineEtaleReductionFunctorCompIso hX R).app U ≪≫ e)⟩⟩⟩
  exact { }

/-- **Stacks 0DEH.** Let `S` be a scheme and `X` a formal algebraic space over `S`. Then
`X_{affine, étale}` is equivalent to the category whose objects are the morphisms `φ : U ⟶ X`
of formal algebraic spaces with `U` an affine formal algebraic space and `φ` representable by
algebraic spaces and étale; the equivalence is the functor `U ↦ U_red`,
`AlgebraicGeometry.FormalSpace.affineEtaleReductionFunctor`. -/
@[stacks 0DEH]
def affineEtaleReductionEquivalence {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X) :
    AffineEtaleFormalCharts B S hS X ≌ R.AffineEtale :=
  have := affineEtaleReductionFunctor_isEquivalence hX R
  (affineEtaleReductionFunctor hX R).asEquivalence

end AlgebraicGeometry.FormalSpace

end
