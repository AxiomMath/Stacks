module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationComponentLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.InverseImageFiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.LocalizedGeneralCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianStalkBaseChange
public import StacksFrontier.CategoryTheory.Sites.ConstantSheaf.PointFiber
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverTerminal

/-!
# A locally constant sheaf becomes constant on the strict henselization

Let `X` be a scheme, `x` a geometric point of it and `p : Spec 𝒪^{sh}_{X,x} ⟶ X` the structure
morphism of the strict henselization there. If `G` is a locally constant abelian sheaf on the
small étale site of `X`, then its inverse image `p⁻¹G` is the *constant* sheaf with value the
stalk `G_x`. This is the fact the proof of [Stacks, Tag 0GJR] uses without a separate citation,
and it is what this file proves, in the two forms the dévissage of that tag consumes: for sheaves,
and for the degree-zero complexes they define in the unbounded derived category.

## The argument

Local constancy of `G` passes to `p⁻¹G` by Tag 093R,
`Stacks.ConstantSheaf.isLocallyConstant_sheafPullback`. So it suffices to see that over
`Spec 𝒪^{sh}_{X,x}` a locally constant abelian sheaf is already constant, and that is a statement
about one covering: a locally constant sheaf becomes constant on a covering of the final object of
the site, and over a strictly henselian local base *every* covering sieve of the final object
contains the identity.

That last point is the only input from the geometry, and it is read off a fact already available:
the final object of the small étale site of `Spec 𝒪^{sh}_{X,x}`, with the canonical geometric
point as its lift, is an *initial* étale neighbourhood of that point
(`Stacks.EtaleCohomology.isInitialPointSmallEtaleClosedPointElement`, the strictly henselian
lifting property). Indeed a covering sieve `R` of an object `T` of any site has, at any element
`ξ` of the fibre of a point of the site over `T`, a member `g : Y ⟶ T` of `R` through which `ξ`
comes (`CategoryTheory.GrothendieckTopology.Point.jointly_surjective`); initiality produces a
morphism of neighbourhoods `T ⟶ Y`; and when `T` is terminal its composite with `g` can only be
the identity, which therefore lies in `R`.

Granted constancy, the value is identified by taking the stalk at the canonical geometric point:
the stalk of a constant sheaf is its value
(`CategoryTheory.GrothendieckTopology.Point.constantFiberIso`), the stalk of `p⁻¹G` there is the
stalk of `G` at `x` by Tag 03Q1 (`Stacks.EtaleCohomology.smallEtaleStalkPullbackAbIso`), and the
canonical geometric point of the strict henselization lies over `x`
(`AlgebraicGeometry.geometricPointToStrictHenselization_comp`).

## Main results

* `Stacks.ConstantSheaf.arrows_id_of_isInitial_point` — a covering sieve of a terminal object
  contains the identity, as soon as the site has a point one of whose fibre elements over that
  object is initial in the category of elements.
* `Stacks.ConstantSheaf.isConstant_of_isLocallyConstant_of_isInitial` — under the same hypothesis,
  a locally constant sheaf is constant.
* `AlgebraicGeometry.isConstant_smallEtalePullbackAb_strictHenselization` — the inverse image of a
  locally constant abelian étale sheaf on the strict henselization is constant.
* `AlgebraicGeometry.nonempty_strictHenselizationPullbackConstantAbIso` and
  `AlgebraicGeometry.strictHenselizationPullbackConstantAbIso` — that inverse image is the
  constant sheaf with value the stalk of `G` at `x`.
* `AlgebraicGeometry.strictHenselizationDerivedPullbackConstantComplexIso` — the same statement on
  derived inverse images of degree-zero complexes, which is the form Tag 0GJR consumes.

## Implementation notes

The transfer from the localized site over the terminal object back to the site itself is
`CategoryTheory.GrothendieckTopology.sheafOverTerminalEquivalence`: restriction to the slice over
a terminal object is an equivalence of sheaf categories whose functor is
`CategoryTheory.GrothendieckTopology.overPullback` on the nose, so
`Stacks.ConstantSheaf.isConstant_of_pushforward` applies to its inverse and carries constancy
across.

## References

* [Stacks Project, Tag 0GJR](https://stacks.math.columbia.edu/tag/0GJR)
* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w' w v u

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **A covering sieve of a terminal object contains the identity**, provided the site has a
point `Φ` and an element `ξ` of its fibre over that object which is initial in the category of
elements of `Φ.fiber`.

A covering sieve is jointly surjective on fibres, so `ξ` is the image of an element `y` of the
fibre over some `Y` along a member `g : Y ⟶ T` of the sieve; initiality gives a morphism
`T ⟶ Y` of elements, and its composite with `g` is the identity because `T` is terminal. -/
theorem arrows_id_of_isInitial_point {Φ : J.Point.{w}} {T : C} (hT : IsTerminal T)
    (ξ : Φ.fiber.obj T)
    (hinit : IsInitial (show Φ.fiber.Elements from Φ.fiber.elementsMk T ξ))
    {R : Sieve T} (hR : R ∈ J T) : R.arrows (𝟙 T) := by
  obtain ⟨Y, g, hg, y, -⟩ := Φ.jointly_surjective R hR ξ
  have h := R.downward_closed hg (hinit.to (show Φ.fiber.Elements from Φ.fiber.elementsMk Y y)).hom
  rwa [hT.hom_ext (_ ≫ g) (𝟙 T)] at h

/-- **A locally constant sheaf is constant** on a site with a terminal object `T` which carries an
initial element of the fibre of a point of the site.

The sheaf becomes constant on a covering of `T`; that covering contains the identity of `T` by
`Stacks.ConstantSheaf.arrows_id_of_isInitial_point`, so the sheaf is already constant after
restriction to the slice over `T`; and restriction to the slice over a terminal object is an
equivalence of sheaf categories. -/
theorem isConstant_of_isLocallyConstant_of_isInitial [HasPullbacks C] (A : Type w')
    [Category.{t} A] [HasWeakSheafify J A] [∀ U : C, HasWeakSheafify (J.over U) A]
    {Φ : J.Point.{w}} {T : C} (hT : IsTerminal T) (ξ : Φ.fiber.obj T)
    (hinit : IsInitial (show Φ.fiber.Elements from Φ.fiber.elementsMk T ξ))
    (H : Sheaf J A) (hH : IsLocallyConstant J H) : Sheaf.IsConstant J H := by
  obtain ⟨I, Y, g, hg, hc⟩ := hH.exists_cover T
  obtain ⟨i, h, -⟩ :=
    (Sieve.mem_ofArrows_iff Y g (𝟙 T)).mp (arrows_id_of_isInitial_point hT ξ hinit hg)
  have := hc i
  have : Sheaf.IsConstant (J.over T) ((J.overPullback A T).obj H) :=
    Localization.isConstant_over_of_isConstant_over J A h H
  let e := J.sheafOverTerminalEquivalence A hT
  have := isConstant_of_pushforward (J.over T) J A (Over.forget T) e.symm.toAdjunction
    (Iso.refl _) Over.mkIdTerminal hT (Iso.refl T) ((J.overPullback A T).obj H)
  obtain ⟨E, ⟨ce⟩⟩ :=
    Sheaf.mem_essImage_of_isConstant J (e.symm.functor.obj ((J.overPullback A T).obj H))
  have hu : H ≅ e.symm.functor.obj ((J.overPullback A T).obj H) := e.unitIso.app H
  exact Sheaf.isConstant_of_iso J (hu ≪≫ ce.symm)

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

open Stacks.EtaleCohomology AlgebraicGeometry.Scheme

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) (x : GeometricPoint X)

/-- **A locally constant abelian étale sheaf has constant inverse image on the strict
henselization.** The inverse image is locally constant by Tag 093R, and over the spectrum of the
strictly henselian local ring `𝒪^{sh}_{X,x}` a locally constant sheaf is constant, because the
canonical geometric point there has the final object of the small étale site as an initial étale
neighbourhood. -/
@[stacks 04HX "a locally constant abelian étale sheaf becomes constant on the strict \
henselization, because every étale covering of a strictly henselian local scheme splits"]
theorem isConstant_smallEtalePullbackAb_strictHenselization
    (G : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    (hG : Stacks.ConstantSheaf.IsLocallyConstant (smallEtaleTopology X) G) :
    Sheaf.IsConstant (smallEtaleTopology (strictHenselization B X hX x))
      ((smallEtalePullbackAb (strictHenselizationToBase B X hX x)).obj G) := by
  have := hG
  exact Stacks.ConstantSheaf.isConstant_of_isLocallyConstant_of_isInitial Ab.{u + 1}
    (Φ := Scheme.pointSmallEtale (geometricPointToStrictHenselization B X hX x))
    (isTerminalEtaleMkId _)
    (Stacks.EtaleCohomology.pointSmallEtaleClosedPointElement
      (geometricPointToStrictHenselization B X hX x))
    (Stacks.EtaleCohomology.isInitialPointSmallEtaleClosedPointElement
      (geometricPointToStrictHenselization B X hX x)
      (geometricPointToStrictHenselization_base_default B X hX x)) _
    (Stacks.ConstantSheaf.isLocallyConstant_sheafPullback (smallEtaleTopology X)
      (smallEtaleTopology (strictHenselization B X hX x)) Ab.{u + 1}
      (Stacks.EtaleCohomology.smallEtaleBaseChange (strictHenselizationToBase B X hX x))
      (Stacks.EtaleCohomology.coverPreserving_smallEtaleBaseChange _) G)

/-- **The inverse image of a locally constant abelian étale sheaf on the strict henselization is
the constant sheaf with value the stalk at `x`.**

The inverse image is constant by
`AlgebraicGeometry.isConstant_smallEtalePullbackAb_strictHenselization`; the value is read off by
taking the stalk at the canonical geometric point `σ` of the strict henselization, where the
stalk of a constant sheaf is its value and the stalk of the inverse image is the stalk of `G` at
`σ ≫ p = x`. -/
theorem nonempty_strictHenselizationPullbackConstantAbIso
    (G : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    (hG : Stacks.ConstantSheaf.IsLocallyConstant (smallEtaleTopology X) G) :
    Nonempty ((smallEtalePullbackAb (strictHenselizationToBase B X hX x)).obj G ≅
      (smallEtalePullbackAb (strictHenselizationToBase B X hX x)).obj
        ((constantSheaf (smallEtaleTopology X) Ab.{u + 1}).obj
          ((smallEtaleStalkAb x.hom).obj G))) := by
  have := isConstant_smallEtalePullbackAb_strictHenselization B hX x G hG
  obtain ⟨E, ⟨c⟩⟩ := Sheaf.mem_essImage_of_isConstant
    (smallEtaleTopology (strictHenselization B X hX x))
    ((smallEtalePullbackAb (strictHenselizationToBase B X hX x)).obj G)
  have hval : E ≅ (smallEtaleStalkAb x.hom).obj G :=
    (GrothendieckTopology.Point.constantFiberIso
        (smallEtaleTopology (strictHenselization B X hX x)) Ab.{u + 1}
        (Scheme.pointSmallEtale (geometricPointToStrictHenselization B X hX x)) E).symm ≪≫
      (smallEtaleStalkAb (geometricPointToStrictHenselization B X hX x)).mapIso c ≪≫
      (Stacks.EtaleCohomology.smallEtaleStalkPullbackAbIso
        (strictHenselizationToBase B X hX x)
        (geometricPointToStrictHenselization B X hX x)).app G ≪≫
      eqToIso (congrArg (fun y : x.source ⟶ X => (smallEtaleStalkAb y).obj G)
        (geometricPointToStrictHenselization_comp B X hX x))
  exact ⟨c.symm ≪≫
    (constantSheaf (smallEtaleTopology (strictHenselization B X hX x)) Ab.{u + 1}).mapIso hval ≪≫
    ((Stacks.ConstantSheaf.sheafPullbackConstantSheafIso
      (Stacks.EtaleCohomology.smallEtaleBaseChange (strictHenselizationToBase B X hX x))
      Ab.{u + 1} (smallEtaleTopology X)
      (smallEtaleTopology (strictHenselization B X hX x)) (isTerminalEtaleMkId X)
      (isTerminalEtaleMkId _)
      (((isTerminalEtaleMkId X).isTerminalObj _ _).uniqueUpToIso
        (isTerminalEtaleMkId _))).app ((smallEtaleStalkAb x.hom).obj G)).symm⟩

/-- The isomorphism of
`AlgebraicGeometry.nonempty_strictHenselizationPullbackConstantAbIso`, chosen. -/
def strictHenselizationPullbackConstantAbIso
    (G : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    (hG : Stacks.ConstantSheaf.IsLocallyConstant (smallEtaleTopology X) G) :
    (smallEtalePullbackAb (strictHenselizationToBase B X hX x)).obj G ≅
      (smallEtalePullbackAb (strictHenselizationToBase B X hX x)).obj
        ((constantSheaf (smallEtaleTopology X) Ab.{u + 1}).obj
          ((smallEtaleStalkAb x.hom).obj G)) :=
  (nonempty_strictHenselizationPullbackConstantAbIso B hX x G hG).some

attribute [local instance] HasDerivedCategory.standard

/-- **Tag 0GJR's strict-henselization input.** The derived inverse image on the strict
henselization of the degree-zero complex of a locally constant abelian étale sheaf `G` is the
derived inverse image of the constant complex with value the stalk `G_x`.

This is `AlgebraicGeometry.strictHenselizationPullbackConstantAbIso` read in the unbounded derived
category: inverse image is exact, so it carries a sheaf placed in degree zero to its inverse image
placed in degree zero, by `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`. -/
def strictHenselizationDerivedPullbackConstantComplexIso
    (G : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    (hG : Stacks.ConstantSheaf.IsLocallyConstant (smallEtaleTopology X) G) :
    (smallEtaleDerivedPullbackAb (strictHenselizationToBase B X hX x)).obj
        ((DerivedCategory.singleFunctor (Sheaf (smallEtaleTopology X) Ab.{u + 1}) 0).obj G) ≅
      (smallEtaleDerivedPullbackAb (strictHenselizationToBase B X hX x)).obj
        (smallEtaleConstantComplexAb X ((smallEtaleStalkAb x.hom).obj G)) :=
  (Functor.mapDerivedCategorySingleFunctor
      (smallEtalePullbackAb (strictHenselizationToBase B X hX x)) 0).app G ≪≫
    (DerivedCategory.singleFunctor
        (Sheaf (smallEtaleTopology (strictHenselization B X hX x)) Ab.{u + 1}) 0).mapIso
      (strictHenselizationPullbackConstantAbIso B hX x G hG) ≪≫
    ((Functor.mapDerivedCategorySingleFunctor
        (smallEtalePullbackAb (strictHenselizationToBase B X hX x)) 0).app
      ((constantSheaf (smallEtaleTopology X) Ab.{u + 1}).obj
        ((smallEtaleStalkAb x.hom).obj G))).symm

end AlgebraicGeometry

end
