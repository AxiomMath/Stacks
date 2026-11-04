module

public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationTheorem
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiDMRelativePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFlatCoverDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedFlatPresentation

/-!
# The easy directions of Stacks 06N3 and Stacks 06MF

`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationTheorem` states both tags in the
shape the source gives them, as an equivalence carrying each implication as an explicit
hypothesis, because the substantial direction of each rests on a structure theorem this library
does not have. The *easy* direction of each is available, and is proved here: a
Deligne-Mumford algebraic stack is DM, and a stack with a quasi-DM presentation is
absolutely quasi-DM.

Neither carries a `@[stacks ...]` attribute. Each is one implication of an equivalence whose
other implication is unproved, so registering a clause key on it would claim the tag on the
strength of its easy half; the registrations stay where they are, on the equivalences.

## Main results

* `AlgebraicGeometry.Stack.isAbsolutelyDMOfExistsEtalePresentation` -- the easy direction of
  **Stacks 06N3**.
* `AlgebraicGeometry.Stack.isAbsolutelyQuasiDMOfHasQuasiDMPresentation` -- the easy direction of
  **Stacks 06MF**.

## References

* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The easy direction of Stacks 06N3.** A Deligne–Mumford algebraic stack is DM. -/
theorem isAbsolutelyDMOfExistsEtalePresentation :
    IsAbsolutelyDMOfExistsEtalePresentation.{u, w} B S hS hZ := by
  intro 𝒳 h𝒳
  obtain ⟨W, pres, hEt, hSurjObj⟩ :=
    exists_etalePresentation_of_isDeligneMumfordStack.{u, w} B S hS (𝒜 := 𝒳.val) h𝒳
  set f : schemeStack.{u, w} B S hS W ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom pres
  have hSm : IsRelativelySmooth B S hS f.hom :=
    isRelativelySmooth_of_isRelativelyEtale B S hS pres hEt
  have hDiag := fun P => hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS P f.hom
    (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W)
    (PresheafOfCategories.sliceElementsEquivalenceOver W) hSm
  have hFlat : AlgebraicStacks.IsFlat B S hS f :=
    (AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS f).2
      (hDiag _ (Space.isFlat_id B S hS (isAlgebraicSpace_yoneda B S hS W)))
  have hLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f :=
    hasPropertyOnEverySmoothDiagram_of_hasPropertyOnSomeSmoothDiagram B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) f.hom
      (hDiag _ (Space.isLocallyOfFinitePresentation_id B S hS (isAlgebraicSpace_yoneda B S hS W)))
  have hSurj : IsSurjective B S hS f :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u + 1} B S hS f hEt.1).2
      ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS
        f.hom hEt.1).1 hSurjObj)
  exact AlgebraicStacks.isAbsolutelyDM_of_isUnramified_flatCover.{u, w} B S hS hZ f
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W) hSurj hFlat hLfp
    (hasRelativeProperty_unramified_of_isRelativelyEtale B S hS hEt _)

/-- **The easy direction of Stacks 06MF.** An algebraic stack with a surjective, flat, locally
finitely presented, locally quasi-finite presentation by a scheme is quasi-DM. -/
theorem isAbsolutelyQuasiDMOfHasQuasiDMPresentation :
    IsAbsolutelyQuasiDMOfHasQuasiDMPresentation.{u, w} B S hS hZ := by
  rintro 𝒳 ⟨W, f, hSurj, hFlat, hLfp, hQf⟩
  exact AlgebraicStacks.isAbsolutelyQuasiDM_of_isLocallyQuasiFinite_flatCover.{u, w} B S hS hZ f
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W) hSurj hFlat hLfp hQf

end AlgebraicGeometry.Stack

end
