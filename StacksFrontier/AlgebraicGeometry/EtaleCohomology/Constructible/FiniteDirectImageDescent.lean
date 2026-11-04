module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PropertyAPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite

/-!
# Constructibility descends along a finite direct image

Let `f : X ⟶ Y` be a finite morphism of schemes with `X` Noetherian, and let `F` be an abelian
sheaf on the small étale site of `X`. If the direct image `f_* F` is constructible, then so is
`F`.

The argument: the counit `f^{-1} f_* F ⟶ F` is surjective, because `f` is integral and so has
property (A) (`AlgebraicGeometry.hasPropertyA_of_isIntegralHom` and
`Stacks.EtaleCohomology.smallEtalePushforwardAb_properties_of_hasPropertyA`); the inverse image
`f^{-1} f_* F` is constructible by Stacks 095G
(`AlgebraicGeometry.isConstructibleFiniteSheaf_pullback`); and on a Noetherian scheme a quotient
of a constructible abelian sheaf is constructible, by Stacks 09BH (2)
(`AlgebraicGeometry.isConstructibleAbelianSheaf_of_epi`).

## Main definitions

* `Stacks.EtaleCohomology.IsConstructibleEtaleSheaf` is constructibility (Stacks 03RW) of an
  abelian sheaf on Mathlib's small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology`,
  read on the small étale site `X_étale` of Stacks 021B cut out of a big étale site `B`
  containing `X`. The two sites have the same sheaves
  (`AlgebraicGeometry.SmallEtale.sheafEquiv`), and the predicate is constructibility of the sheaf
  corresponding to `F` under that equivalence.

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleSheaf_of_smallEtaleDirectImageAb` — for a finite
  morphism with Noetherian source, constructibility of `f_* F` gives constructibility of `F`.

## Implementation notes

The constructibility predicate of this library, `AlgebraicGeometry.IsConstructibleAbelianSheaf`,
lives on the size-bounded small étale site of Stacks 021B, while étale cohomology
(`CategoryTheory.Sheaf.H`) and direct image are computed on Mathlib's small étale site. The
proof therefore runs on Mathlib's site for the counit, crosses to the bounded site through
`AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso`, which identifies the two inverse
images, and applies Stacks 095G and Stacks 09BH (2) there.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 0A5D](https://stacks.math.columbia.edu/tag/0A5D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u})

/-- **Constructibility of an abelian sheaf on Mathlib's small étale site.** An abelian sheaf `F`
on `AlgebraicGeometry.Scheme.smallEtaleTopology X` is constructible, relative to a big étale site
`B` containing `X`, when the sheaf it corresponds to on the small étale site `X_étale` of
Stacks 021B is constructible in the sense of Stacks 03RW. -/
public abbrev IsConstructibleEtaleSheaf {X : Scheme.{u}} (hX : B.Contains X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  IsConstructibleAbelianSheaf B (B.obj X hX)
    ((SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse.obj F)

/-- **Constructibility descends along a finite direct image.** For a finite morphism `f : X ⟶ Y`
with `X` Noetherian and an abelian sheaf `F` on the small étale site of `X`, if `f_* F` is
constructible then so is `F`: it is a quotient of the constructible sheaf `f^{-1} f_* F`. -/
public theorem isConstructibleEtaleSheaf_of_smallEtaleDirectImageAb {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [IsNoetherian X] (hX : B.Contains X) (hY : B.Contains Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleEtaleSheaf B hY ((smallEtaleDirectImageAb f).obj F)) :
    IsConstructibleEtaleSheaf B hX F := by
  let fB : B.obj X hX ⟶ B.obj Y hY := ObjectProperty.homMk f
  let EX := SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}
  let EY := SmallEtale.sheafEquiv B Y hY AddCommGrpCat.{u + 1}
  let LB := B.smallInverseImage fB AddCommGrpCat.{u + 1}
  -- the counit of the inverse-image/direct-image adjunction on Mathlib's site is surjective
  have hc : Epi ((smallEtaleAdjunctionAb f).counit.app F) :=
    (smallEtalePushforwardAb_properties_of_hasPropertyA f (hasPropertyA_of_isIntegralHom f)).2.2.1 F
  -- the inverse images of the two presentations agree
  let e : EY.functor ⋙ (Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPullback
        AddCommGrpCat.{u + 1} Y.smallEtaleTopology X.smallEtaleTopology ≅ LB ⋙ EX.functor :=
    SmallEtale.sheafEquivPullbackBaseChangeIso B fB AddCommGrpCat.{u + 1}
      (smallEtaleAdjunctionAb f)
      (B.smallPullbackAdjunction fB AddCommGrpCat.{u + 1})
  let G := EY.inverse.obj ((smallEtaleDirectImageAb f).obj F)
  -- `F` is a quotient of `EX.functor (LB G)`
  let p : EX.functor.obj (LB.obj G) ⟶ F :=
    (e.app G).inv ≫
      ((Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPullback AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology X.smallEtaleTopology).map (EY.counitIso.hom.app _) ≫
      (smallEtaleAdjunctionAb f).counit.app F
  have hp : Epi p := epi_comp' inferInstance (epi_comp' inferInstance hc)
  exact isConstructibleAbelianSheaf_of_epi B (B.obj X hX)
    (smallEtaleUnderlyingSetCommutes B (B.obj X hX))
    (representableIsConstructibleSetSheaf B (B.obj X hX))
    (hasFiniteRepresentableCover B (B.obj X hX))
    (EX.unitIso.hom.app (LB.obj G) ≫ EX.inverse.map p)
    (isConstructibleFiniteSheaf_pullback B fB G hF)

end Stacks.EtaleCohomology

end
