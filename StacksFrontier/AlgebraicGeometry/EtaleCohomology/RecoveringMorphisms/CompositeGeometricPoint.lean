module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.SitePoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.GeometricStalkReflectsUnits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.ToposPointPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Stalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.StalkReflectsUnits
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.ToposHomUnitsSquare
public import StacksFrontier.CategoryTheory.Sites.Point.FiberIsoTransport
public import StacksFrontier.CategoryTheory.Sites.Point.OfToposPoint
public import StacksFrontier.CategoryTheory.Sites.Point.ToposPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The composite of a morphism of small étale topoi with a geometric point is a geometric point

Let `X` and `Y` be schemes of a big étale site and let `g` be a morphism of topoi from the small
étale topos of `X` to that of `Y` — in the application, the topos part of a morphism of the small
étale *ringed* topoi, which is the datum of [Stacks Project, Tag 04I6].  Let `x̄` be a geometric
point of `X`, giving the point `p = x̄` of the small étale site of `X`
(`AlgebraicGeometry.geometricPointSitePoint`) and hence, by Stacks 00YA (1), a point of its topos.

This file supplies the step the iso-ness half of Stacks 04I6 turns on: **the composite point
`q = g ∘ p` of the small étale topos of `Y` is the geometric stalk functor of a geometric point
`ȳ` of `Y`**.  That is the source's appeal to Lemma 59.29.12 when it writes "`q = g ∘ p`
corresponds to a geometric point `ȳ`", and it is what makes the stalk of `g⁻¹h_V` at `x̄` a set of
lifts of a geometric point of `Y`, so that the solution-set computation of
[Stacks Project, Tag 04GX] can be run on it.

## Why this is not simply Stacks 04HU (2) as formalized

`AlgebraicGeometry.exists_geometricPoint_inverseImage_iso` already says that every point of the
small étale topos has a geometric stalk functor as its inverse image.  It is stated at the
coefficient universe `Type (u + 1)`, because the reconstruction of a point of a site from a point
of a topos (Stacks 00YA (2)) is formalized asking `Small.{w}` of the site, and the small étale site —
objects in `Type (u + 1)`, morphisms in `Type u` — is `Small.{w}` only for `w = u + 1`.

The comparison of Stacks 04I6 lives one universe down: the representable sheaves
`(SmallEtale.topology B Y.obj Y.property).yoneda.obj V` take values in `Type u`, because the
hom-sets of the site do, and that is also the universe of the structure sheaf and of the
iso-detection criterion `AlgebraicGeometry.isIso_iff_forall_bijective_geometricSheafFiber`.  So
the statement needed here is the one at `Type u`, and it is the form of the reconstruction whose
side condition is `EssentiallySmall.{w}` rather than `Small.{w}` —
`CategoryTheory.PointOfTopos.sitePointOfEssentiallySmall` and
`CategoryTheory.PointOfTopos.sheafFiberIsoInverseImageOfEssentiallySmall` — which the small étale
site does satisfy (`AlgebraicGeometry.SmallEtale.essentiallySmall`).  What makes that form
available is `CategoryTheory.CategoryOfElements.initiallySmall_elements_of_essentiallySmall`.

## Main results

* `AlgebraicGeometry.exists_geometricPoint_inverseImage_comp_sheafFiber_iso` — **the step**: the
  composite of `g⁻¹` with the geometric stalk functor at `x̄` is the geometric stalk functor at
  some geometric point `ȳ` of `Y`.
* `AlgebraicGeometry.exists_geometricPoint_sheafFiber_inverseImage_yoneda_equiv` — the same read
  on a representable: the geometric fibre at `x̄` of `g⁻¹h_V` is the set of lifts of `ȳ` to the
  chart `V`, naturally in `V`.
* `AlgebraicGeometry.isLocalHom_geometricSheafFiber_fSharpInverseImage` — the second input the
  stalk computation needs, and the only place the *locally* ringed hypothesis is used: the fibre
  at `x̄` of the structure map `g⁻¹𝒪_Y ⟶ 𝒪_X` is a **local** homomorphism.  This is the
  hypothesis of [Stacks Project, Tag 04GX].

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04HU](https://stacks.math.columbia.edu/tag/04HU)
* [Stacks Project, Tag 00YA](https://stacks.math.columbia.edu/tag/00YA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (hY : B.Contains Y)
  (g : MorphismOfTopoi (Sheaf (SmallEtale.topology B X hX) (Type u))
    (Sheaf (SmallEtale.topology B Y hY) (Type u)))
  (x : GeometricPoint X)

/-- **The composite of a morphism of small étale topoi with a geometric point is a geometric
point.**  For `g` a morphism of topoi from the small étale topos of `X` to that of `Y` and `x̄` a
geometric point of `X`, there is a geometric point `ȳ` of `Y` whose geometric stalk functor is
`g⁻¹` followed by the geometric stalk functor at `x̄`.

This is the source's "`q = g ∘ p` corresponds to a geometric point `ȳ`" in the proof of
[Stacks Project, Tag 04I6], at the coefficient universe `Type u` in which the representable
sheaves of the site live.

The proof is Stacks 00YA (2) followed by Stacks 04HU (1): the composite point of the topos is
reconstructed as a point of the *site* of `Y` (`PointOfTopos.sitePointOfEssentiallySmall`, whose
stalk functor is the inverse image by
`PointOfTopos.sheafFiberIsoInverseImageOfEssentiallySmall`), and a point of the small étale
site of `Y` has the fibre functor of a geometric point
(`AlgebraicGeometry.exists_geometricPoint_fiber_iso`), along which the stalk functor transports
by `Stacks.SitePointFiberIso.sheafFiberIsoOfFiberIso`. -/
alias exists_geometricPoint_inverseImage_comp_sheafFiber_iso :=
  AlgebraicGeometry.exists_geometricPoint_inverseImage_comp_sheafFiberIso

/-- **The geometric fibre of `g⁻¹h_V` is a set of lifts of a geometric point of `Y`.**  For `g` a
morphism of topoi from the small étale topos of `X` to that of `Y` and `x̄` a geometric point of
`X`, there is a geometric point `ȳ` of `Y` such that the fibre at `x̄` of `g⁻¹` of the sheaf
represented by an étale chart `V` of `Y` is the set of lifts of `ȳ` to `V`, naturally in `V`.

This is `AlgebraicGeometry.exists_geometricPoint_inverseImage_comp_sheafFiber_iso` composed with
the identification of the stalk of a representable sheaf with the fibre functor,
`AlgebraicGeometry.smallEtaleYonedaCompEtaleStalkFunctorIso`.  It is the form in which the
iso-ness half of [Stacks Project, Tag 04I6] uses the step: the source's stalk computation compares
the lifts of `ȳ` to `V` with the lifts of `x̄` to `X ×_Y V`. -/
theorem exists_geometricPoint_sheafFiber_inverseImage_yoneda_equiv :
    ∃ y : GeometricPoint Y,
      Nonempty ((SmallEtale.topology B Y hY).yoneda ⋙ g.inverseImage ⋙
          (geometricPointSitePoint B X hX x).sheafFiber (A := Type u) ≅
        geometricPointFiber B Y hY y) := by
  obtain ⟨y, ⟨i⟩⟩ := exists_geometricPoint_inverseImage_comp_sheafFiber_iso B hX hY g x
  exact ⟨y, ⟨Functor.isoWhiskerLeft (SmallEtale.topology B Y hY).yoneda i ≪≫
    smallEtaleYonedaCompEtaleStalkFunctorIso B Y hY y⟩⟩

/-! ### The locality of the structure map at a geometric point -/

/-- **The fibre at a geometric point of the structure map of a locally ringed morphism of small
étale ringed topoi is a local homomorphism.**

This is the second input to the stalk computation of step (3) of the proof of
[Stacks Project, Tag 04I6], and the only place in that proof where the hypothesis that `(g, g^♯)`
is a morphism of *locally* ringed topoi is used: it is the source's "because the morphism is
locally ringed, `(g^♯)_p` is a local homomorphism of strictly henselian local rings".  The
strict henselianness of the two rings is `AlgebraicGeometry.etaleLocalRing_strictHenselian`
(Stacks 04GH) read through `AlgebraicGeometry.etaleStalkCmp_bijective`; the locality is this
statement, and together they are the hypotheses of [Stacks Project, Tag 04GX].

Both halves are available: direction (1) ⇒ (3) of Stacks 04H9 for a morphism of ringed topoi is
`AlgebraicGeometry.RingedToposHom.reflectsUnitsObj_of_isLocallyRinged`, applied to the geometric
stalk functor, which is left exact because it is the inverse image of a point of the site; and the
passage from reflection of units to locality of the stalk map is
`AlgebraicGeometry.RingedTopos.isLocalHom_sheafFiber_of_reflectsUnitsObj`. -/
@[sga "4 IV 13.9" "c), special case"]
theorem isLocalHom_geometricSheafFiber_fSharpInverseImage {X Y : B.Scheme}
    (g : RingedToposHom
      (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (hg : g.IsLocallyRinged) (x : GeometricPoint X.obj) :
    IsLocalHom (((geometricPointSitePoint B X.obj X.property x).sheafFiber
      (A := CommRingCat.{u})).map g.fSharpInverseImage).hom :=
  RingedTopos.isLocalHom_sheafFiber_of_reflectsUnitsObj _ _
    (g.reflectsUnitsObj_of_isLocallyRinged hg
      ((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u)))

end AlgebraicGeometry

end
