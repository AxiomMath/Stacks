module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareGeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianExtensionByZeroCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietoris
import StacksCore.Tactic.StacksAttribute

/-!
# The lifts of a geometric point along the four morphisms of an elementary distinguished square

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` and let `P = U ×_X V` be its intersection.  A geometric point `x̄` of `X` either lies
in the open subspace `U` or it does not, and the two cases have opposite lift counts along the
four morphisms of the square:

* `x̄ ∈ U`: it has exactly one lift to `U`, because an open immersion is a monomorphism of
  presheaves;
* `x̄ ∉ U`: it has no lift to `U`, hence none to `P` either, and exactly one lift to `V`,
  because the étale morphism of the square restricts to an isomorphism over the reduced closed
  complement of `U`.

These are the counts that make the Mayer–Vietoris stalk sequence of Stacks 08GV degenerate at
every geometric point: by Equation 08GU the stalk of an extension by zero is the direct sum of
the stalks of the restriction over the lifts, so a unique lift makes the counit of the
extension-by-zero adjunction invertible on stalks and no lift makes the extension by zero have
vanishing stalk.

## Main definitions

* `AlgebraicGeometry.Space.edsInterLiftToOpen` sends a lift of a geometric point to the
  intersection to its lift to the open subspace.

## Main results

* `AlgebraicGeometry.Space.unique_geometricPointLift_edsOpenHom_of_mem`: a geometric point lying
  in the open subspace has exactly one lift to it.
* `AlgebraicGeometry.Space.isEmpty_geometricPointLift_edsOpenHom_of_notMem` and
  `AlgebraicGeometry.Space.isEmpty_geometricPointLift_edsInterHom_of_notMem`: a geometric point
  not lying in the open subspace has no lift to it and none to the intersection.
* `AlgebraicGeometry.Space.unique_geometricPointLift_edsEtaleHom_of_notMem`: such a point has
  exactly one lift along the étale morphism of the square.
* `AlgebraicGeometry.Space.isZero_sheafFiber_edsOpen_shriek_of_notMem` and
  `AlgebraicGeometry.Space.isZero_sheafFiber_edsInter_shriek_of_notMem`: at a geometric point
  outside the open subspace the extensions by zero from the open subspace and from the
  intersection have vanishing stalk.
* `AlgebraicGeometry.Space.isIso_sheafFiber_edsEtale_counit_of_notMem` and
  `AlgebraicGeometry.Space.isIso_sheafFiber_edsOpen_counit_of_mem`: the counit of the
  extension-by-zero adjunction along the étale morphism is invertible on the stalk at a point
  outside the open subspace, and the counit along the open immersion is invertible on the stalk
  at a point of the open subspace.

## Implementation notes

Nothing geometric happens here.  The three counts over the open subspace and over the étale
morphism are
`AlgebraicGeometry.Space.subsingleton_geometricPointLift_of_mono`,
`AlgebraicGeometry.Space.nonempty_geometricPointLift_ι_iff_mem_range_pointsMap` and
`AlgebraicGeometry.Space.existsUnique_geometricPointLift_of_notMem_range_pointsMap`, read for
the morphisms of the square; the fourth is the observation that the morphism from the
intersection to the ambient space factors through the open subspace by definition, so a lift to
the intersection produces a lift to the open subspace.

The four stalk statements are then immediate from the counit formula of Equation 08GU,
`AlgebraicGeometry.Space.EtaleShriekStalk.isIso_sheafFiber_counit_of_unique` and
`AlgebraicGeometry.Space.EtaleShriekStalk.isZero_sheafFiber_restriction_shriek_of_isEmpty`, fed
with those counts.  They are three of the four degeneracies that make the Mayer–Vietoris short
complex of Stacks 08GV split at every geometric point; the fourth, the invertibility at a point
of the open subspace of the comparison out of the intersection towards the étale algebraic
space, is
`AlgebraicGeometry.Space.isIso_edsModuleStalk_edsShriekEtaleComparison_of_mem` of
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisComparisonStalk`.

## References

* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 08GU](https://stacks.math.columbia.edu/tag/08GU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  (x : GeometricPoint B S hS W.1)

/-- **A lift of a geometric point to the intersection of an elementary distinguished square
lifts it to the open subspace**, the morphism from the intersection being the composite through
the open subspace by definition. -/
def edsInterLiftToOpen
    (t : GeometricPointLift B S hS (edsInterHom B S hS hsq).hom x) :
    GeometricPointLift B S hS (edsOpenHom B S hS hsq).hom x :=
  ⟨(edsFst B S hS hsq).hom.app (op (x.val.siteObject B S hS W.1)) t.1, t.2⟩

/-- **A geometric point of the ambient space of an elementary distinguished square which lies in
the open subspace has exactly one lift to it.** -/
@[instance_reducible]
def unique_geometricPointLift_edsOpenHom_of_mem
    (hx : x.image ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    Unique (GeometricPointLift B S hS (edsOpenHom B S hS hsq).hom x) := by
  have hne := (nonempty_geometricPointLift_ι_iff_mem_range_pointsMap B S hS W.2 Uo
    hsq.isOpenSubspace x).2 hx
  haveI hss : Subsingleton (GeometricPointLift B S hS (edsOpenHom B S hS hsq).hom x) :=
    subsingleton_geometricPointLift_of_mono B S hS Uo.ι inferInstance x
  exact uniqueOfSubsingleton hne.some

/-- **A geometric point of the ambient space of an elementary distinguished square which does
not lie in the open subspace has no lift to it.** -/
theorem isEmpty_geometricPointLift_edsOpenHom_of_notMem
    (hx : x.image ∉ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    IsEmpty (GeometricPointLift B S hS (edsOpenHom B S hS hsq).hom x) :=
  not_nonempty_iff.1 fun h => hx ((nonempty_geometricPointLift_ι_iff_mem_range_pointsMap
    B S hS W.2 Uo hsq.isOpenSubspace x).1 h)

/-- **A geometric point of the ambient space of an elementary distinguished square which does
not lie in the open subspace has no lift to the intersection either.** -/
theorem isEmpty_geometricPointLift_edsInterHom_of_notMem
    (hx : x.image ∉ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    IsEmpty (GeometricPointLift B S hS (edsInterHom B S hS hsq).hom x) :=
  have h := isEmpty_geometricPointLift_edsOpenHom_of_notMem B S hS hsq x hx
  ⟨fun t => h.elim (edsInterLiftToOpen B S hS hsq x t)⟩

/-- **A geometric point of the ambient space of an elementary distinguished square which does
not lie in the open subspace has exactly one lift along the étale morphism of the square**, that
morphism restricting to an isomorphism over the reduced closed complement. -/
@[instance_reducible]
def unique_geometricPointLift_edsEtaleHom_of_notMem
    (hx : x.image ∉ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    Unique (GeometricPointLift B S hS (edsEtaleHom B S hS hsq).hom x) := by
  have hne := nonempty_geometricPointLift_of_notMem_range_pointsMap B S hS W.2 Uo fV hsq x hx
  haveI hss : Subsingleton (GeometricPointLift B S hS (edsEtaleHom B S hS hsq).hom x) :=
    subsingleton_geometricPointLift_of_notMem_range_pointsMap B S hS W.2 Uo fV hsq x hx
  exact uniqueOfSubsingleton hne.some

/-! ### The three stalk degeneracies of the Mayer–Vietoris sequence -/

section Stalks

variable (G : Sheaf (SmallEtale.topology B S hS W.1) AddCommGrpCat.{u})

/-- **At a geometric point outside the open subspace the extension by zero from the open
subspace has vanishing stalk**, there being no lift of the point to the open subspace. -/
theorem isZero_sheafFiber_edsOpen_shriek_of_notMem
    (hx : x.image ∉ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    IsZero ((etaleSitePoint B S hS W.1 x W.2).sheafFiber.obj
      ((abelianEtaleExtensionByZero B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq)).obj
        ((abelianEtaleRestriction B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq)).obj G))) :=
  have := isEmpty_geometricPointLift_edsOpenHom_of_notMem B S hS hsq x hx
  EtaleShriekStalk.isZero_sheafFiber_restriction_shriek_of_isEmpty B S hS
    (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq) x G

/-- **At a geometric point outside the open subspace the extension by zero from the
intersection has vanishing stalk**, there being no lift of the point to the intersection. -/
theorem isZero_sheafFiber_edsInter_shriek_of_notMem
    (hx : x.image ∉ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    IsZero ((etaleSitePoint B S hS W.1 x W.2).sheafFiber.obj
      ((abelianEtaleExtensionByZero B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).obj
        ((abelianEtaleRestriction B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).obj G))) :=
  have := isEmpty_geometricPointLift_edsInterHom_of_notMem B S hS hsq x hx
  EtaleShriekStalk.isZero_sheafFiber_restriction_shriek_of_isEmpty B S hS
    (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq) x G

/-- **At a geometric point outside the open subspace the counit of the extension by zero along
the étale morphism of the square is invertible on stalks**, the point having exactly one lift
along that morphism. -/
theorem isIso_sheafFiber_edsEtale_counit_of_notMem
    (hx : x.image ∉ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    IsIso ((etaleSitePoint B S hS W.1 x W.2).sheafFiber.map
      ((abelianEtaleExtensionByZeroAdjunction B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).counit.app G)) :=
  have := unique_geometricPointLift_edsEtaleHom_of_notMem B S hS hsq x hx
  EtaleShriekStalk.isIso_sheafFiber_counit_of_unique B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq) x G

/-- **At a geometric point of the open subspace the counit of the extension by zero from the
open subspace is invertible on stalks**, the point having exactly one lift to it. -/
theorem isIso_sheafFiber_edsOpen_counit_of_mem
    (hx : x.image ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    IsIso ((etaleSitePoint B S hS W.1 x W.2).sheafFiber.map
      ((abelianEtaleExtensionByZeroAdjunction B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).counit.app G)) :=
  have := unique_geometricPointLift_edsOpenHom_of_mem B S hS hsq x hx
  EtaleShriekStalk.isIso_sheafFiber_counit_of_unique B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq) x G

end Stalks

end AlgebraicGeometry.Space

end
