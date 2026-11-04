module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaceThickenings
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeNoetherianRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableSetTheoreticCondition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransferRefined

/-!
# Sources of representable and of finite type morphisms: Stacks 0AJI, 0AQ8

The statements of `StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableSource` (Stacks 0AJI)
and `StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeNoetherian` (Stacks 0AQ8) at the
source's hypotheses. Those modules take Stacks 0AIU, Stacks 0ANL, Stacks 0AKP and the
set-theoretic condition of Stacks 0AIS as hypotheses; here each is proved:

* Stacks 0AIU in its corrected form is
  `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_isRepresentableThickeningULift`;
  it is applied only to sheaves satisfying the set-theoretic condition, which is the only
  correction it needs;
* the set-theoretic condition of a sheaf representable by algebraic spaces over a formal
  algebraic space is the following lemma of the namespace `AlgebraicGeometry.FormalSpace`:
`satisfiesSetTheoreticCondition_of_isRepresentableByAlgebraicSpacesULift_of_isFormalAlgebraicSpace`
* Stacks 0AQ7 is
  `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_source_of_isLocallyOfFiniteType'`.

## Main results

* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_isRepresentableByAlgebraicSpacesULift`:
  **Stacks 0AJI**.
* `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_of_isPullback_of_isLocallyOfFiniteType`:
  **Stacks 0AQ8**, for a cartesian square over an arbitrary fppf sheaf `Y`: neither `X` nor `Y`
  needs to be a formal algebraic space.

## References

* [Stacks Project, Tag 0AJI](https://stacks.math.columbia.edu/tag/0AJI)
* [Stacks Project, Tag 0AQ7](https://stacks.math.columbia.edu/tag/0AQ7)
* [Stacks Project, Tag 0AQ8](https://stacks.math.columbia.edu/tag/0AQ8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AJI.** If `Y` is a formal algebraic space over `S` and `f : X ⟶ Y` is a morphism
of fppf sheaves representable by algebraic spaces, then `X` is a formal algebraic space over
`S`.

This is `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_representable_over_formal`
with its hypotheses proved: the set-theoretic condition of `X` and of the base changed atlas
members by
`satisfiesSetTheoreticCondition_of_isRepresentableByAlgebraicSpacesULift_of_isFormalAlgebraicSpace`
and Stacks 0AIU by its corrected form
`isFormalAlgebraicSpace_of_colimit_isRepresentableThickeningULift`. -/
@[stacks 0AJI]
theorem isFormalAlgebraicSpace_of_isRepresentableByAlgebraicSpacesULift
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom) :
    IsFormalAlgebraicSpace B S hS X :=
  isFormalAlgebraicSpace_of_representable_over_formal B S hS f hY hf
    (satisfiesSetTheoreticCondition_of_isRepresentableByAlgebraicSpacesULift_of_isFormalAlgebraicSpace
      B S hS f hf hY)
    (fun _ v hV _ =>
      satisfiesSetTheoreticCondition_of_isRepresentableByAlgebraicSpacesULift_of_isFormalAlgebraicSpace
        B S hS (pullback.fst v f)
        (Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _
          ((IsPullback.of_hasPullback v f).map
            (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))).flip hf)
        (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hV))
    (isFormalAlgebraicSpace_of_colimit_isRepresentableThickeningULift B S hS)

/-- **Stacks 0AQ8.** Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of fppf sheaves over `S`.
If `Z` is a locally Noetherian formal algebraic space and `f` is locally of finite type, then
`Z ×_Y X` is locally Noetherian.

The projection `p : Z ×_Y X ⟶ Z` is a base change of `f`, so it is locally of finite type by
Stacks 0AQ5; being representable by algebraic spaces it makes `Z ×_Y X` a formal algebraic space
by Stacks 0AJI, and Stacks 0AQ7 applies to `p`. The fibre product is presented as an arbitrary
cartesian square, so the statement covers either order of its two legs; `X` and `Y` need not be
formal algebraic spaces. -/
@[stacks 0AQ8]
theorem isLocallyNoetherian_of_isPullback_of_isLocallyOfFiniteType
    {W X Y Z : FppfSheaf B S hS} {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f)
    (hZ : IsLocallyNoetherian B S hS Z)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyNoetherian B S hS W := by
  obtain ⟨hprep, hpprop⟩ := IsLocallyOfFiniteType.of_isPullback B S hS sq hf
  exact isLocallyNoetherian_source_of_isLocallyOfFiniteType' B S hS p
    (isFormalAlgebraicSpace_of_isRepresentableByAlgebraicSpacesULift B S hS p hZ.1 hprep) hZ
    ⟨hprep, hpprop⟩

end AlgebraicGeometry.FormalSpace

end
