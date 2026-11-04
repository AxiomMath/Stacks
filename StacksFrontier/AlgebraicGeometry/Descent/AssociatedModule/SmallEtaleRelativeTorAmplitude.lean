module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullOnFree
public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRelativeRingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSiteHomGeneral
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleToposRingedHom
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.FlatPullbackExact
public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableRingedAugmentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkPullbackAtAPointPair
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Stalks
public import StacksFrontier.AlgebraicGeometry.RelativeTorAmplitudeAffine
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeTorAmplitude
public import StacksFrontier.Homology.ExtendScalars.AlongARingIsomorphism
public import Mathlib.Topology.Sheaves.Points
import StacksCore.Tactic.StacksAttribute

/-!
# Relative Tor amplitude across the Zariski-to-étale comparison

Let `f : X ⟶ Y` be a morphism of schemes and let
`ε = id_{small, étale, Zar} : X_étale ⟶ X_Zar` be the comparison of Stacks 08H7, read with
coefficients in `f⁻¹𝒪_Y` as the morphism of ringed topoi
`(X_étale, ε⁻¹f⁻¹𝒪_Y) ⟶ (X_Zar, f⁻¹𝒪_Y)`.  Its pullback of sheaves of modules is `ε^*`, and an
object `E` of `D(f⁻¹𝒪_Y)` has Tor amplitude in `[a, b]` if and only if `ε^*E` has Tor amplitude
in `[a, b]` as an object of `D(ε⁻¹f⁻¹𝒪_Y)`.  The same holds for finite Tor dimension.

## Main definitions

* `AlgebraicGeometry.SmallEtale.relativeRingSheafMap`: the structure map of the comparison on
  sheaves of not necessarily commutative rings, `f⁻¹𝒪_Y ⟶ ε_*(ε⁻¹f⁻¹𝒪_Y)`.
* `AlgebraicGeometry.SmallEtale.relativeAssociatedModule`: `ε^*` with coefficients in `f⁻¹𝒪_Y`,
  `Mod(f⁻¹𝒪_Y) ⥤ Mod(ε⁻¹f⁻¹𝒪_Y)`, with
  `AlgebraicGeometry.SmallEtale.relativeAssociatedModuleAdjunction` exhibiting it as the left
  adjoint of the pushforward along the comparison.
* `AlgebraicGeometry.SmallEtale.toZariskiRelativeRingedSiteHom`: the comparison as a morphism of
  ringed sites, which carries the morphism of topoi underlying `ε`.
* `AlgebraicGeometry.SmallEtale.relativeStalkFunctorIso`: the stalk of `ε^*M` at the geometric
  point of `X` at `x` is the stalk `M_x`, with its scalars extended along a bijective map of stalk
  rings.
* `AlgebraicGeometry.SmallEtale.relativeDerivedAssociatedModule`: the induced functor
  `D(f⁻¹𝒪_Y) ⥤ D(ε⁻¹f⁻¹𝒪_Y)`.

## Main results

* `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_relativeAssociatedModule`: `ε^*` with
  coefficients in `f⁻¹𝒪_Y` is exact, the exactness assertion of Stacks 08H8 in relative form.
* `hasTorAmplitudeCanonical_derivedModuleFiber_relativeDerivedAssociatedModule_iff`, in the
  namespace `AlgebraicGeometry.SmallEtale`: the derived stalk of `ε^*E` at the geometric point
  at `x` has Tor amplitude in `[a, b]` exactly when `E_x` does.
* `AlgebraicGeometry.SmallEtale.hasTorAmplitude_relativeDerivedAssociatedModule_iff`:
  **Stacks 0DK7, part (1)**, both directions.
* `AlgebraicGeometry.SmallEtale.hasFiniteTorDimension_relativeDerivedAssociatedModule_iff`: the
  same for finite Tor dimension.  This is *not* part (2) of Stacks 0DK7, which is about
  *locally* finite Tor dimension and is
  `AlgebraicGeometry.SmallEtale.locallyHasFiniteTorDimension_relativeDerivedAssociatedModule`.

## Implementation notes

*An arbitrary object of `D(f⁻¹𝒪_Y)`.*  The source states both parts for an object `E` of
`D(𝒪_X)` read in `D(f⁻¹𝒪_Y)` through restriction of scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X`.  The
statements here quantify over an arbitrary object of `D(f⁻¹𝒪_Y)`, so they apply in particular
to `(AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction f).obj E`, which is that reading.

*The structure sheaf on the étale side.*  Stacks 0DK7 reads `ε^*E` as an object of
`D(f_{small}^{-1}𝒪_{Y_étale})`, where `f_{small} : X_étale ⟶ Y_étale` is base change on small
étale sites.  The structure sheaf used here is `ε⁻¹f⁻¹𝒪_Y`, the
`AlgebraicGeometry.SmallEtale.relativeStructureSheaf` over which the comparison of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleRelativeRingedToposHom.lean`
is defined.  The two are *not* isomorphic — at a geometric point over `x ∈ X` their stalks are
`𝒪_{Y, f(x)}` and its strict henselization — as the implementation notes of that module record,
and this is the respect in which the statements below differ from the source.  The statements
with `f_{small}^{-1}𝒪_{Y_étale}` itself are, in the namespace `AlgebraicGeometry.Space`,
`hasTorAmplitude_derivedScalarRestriction_iff_representedZariskiDerivedPullback` and its
companion for part (2), which pass through the stalks too and then through Stacks 0DJF
and 0DK0 along the strict henselization.

*Nothing is carried as a hypothesis.*  An earlier form of this module took four inputs as
hypotheses — exactness of `ε^*`, preservation of flat modules by `ε^*`, reflection of zero
objects by `ε^*` and a comparison of the two derived tensor products along `ε^*` — because it ran
the argument of Stacks 08H5 through
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_mapDerivedCategory_iff`.  The first
is now an instance: the comparison is a morphism of ringed sites
(`toZariskiRelativeRingedSiteHom`), so it carries a morphism of topoi, and its structure map in
inverse-image form is an isomorphism (`toZariskiRelativeRingedSiteHom_fSharpInverseImage`), hence
flat, so Stacks 04JC applies.  The other three are not needed at all: both sides are read at the
stalks by Stacks 0DJJ, at the points of `X` on the Zariski side and at the geometric points of
`X` on the étale side, two conservative families indexed by the points of `X`, and at the point
`x` the two derived stalks agree by Stacks 05V5
(`hasTorAmplitudeCanonical_derivedModuleFiber_relativeDerivedAssociatedModule_iff`).  This is
the argument of the source's proof of part (1) without the strict henselization, which the
coefficients `ε⁻¹f⁻¹𝒪_Y` do not see.

*Spelling of the sheaf of rings.*  The Tor-amplitude vocabulary reads the sheaf of rings of a
ringed site through `Stacks.SheafOfModules.Tensor.ringSheaf`, while
`AlgebraicGeometry.RingedTopos.ringSheaf` builds it with `CategoryTheory.sheafCompose` and
an instance argument.  The two are definitionally equal, but not at instance transparency,
so a statement mixing them makes every instance for the modules of one side fail to fire
for the other.  `relativeRingSheafMap` is the structure map of the comparison retyped once
and for all at the first spelling, and everything below stays there.

*Instances.*  The three auxiliary instances recorded below are restatements: continuity of the
inclusion of the small Zariski site at the spelling of the two ringed sites, and the two
adjointness instances that `SheafOfModules.pullback` consumes.  Instance search does not find
them from the fields of the comparison, the small Zariski site of `X` being presented by the
opens of its space, one universe below the objects of the small étale site.  The two derived
categories have independent hom universes, as everywhere in this development.

## References

* [Stacks Project, Tag 0DK7](https://stacks.math.columbia.edu/tag/0DK7)
* [Stacks Project, Tag 08H5](https://stacks.math.columbia.edu/tag/08H5)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u d e

attribute [local instance] AlgebraicGeometry.smallEtale_hasSheafify
  AlgebraicGeometry.smallEtale_wEqualsLocallyBijective

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) {Y : Scheme.{u}}
  (f : X ⟶ Y)

/-! ### `ε^*` with coefficients in `f⁻¹𝒪_Y` -/

/-- The inclusion of the small Zariski site of `X` into its small étale site is continuous for
the topologies of the two ringed sites `(X_Zar, f⁻¹𝒪_Y)` and `(X_étale, ε⁻¹f⁻¹𝒪_Y)`. -/
instance isContinuous_opensToSmallEtale_inverseImage :
    (opensToSmallEtale B X hX).IsContinuous (Scheme.Hom.inverseImageRingedSite f).J
      (relativeRingedTopos B X hX f).toRingedSite.J :=
  isContinuous_opensToSmallEtale B X hX

/-- **The structure map of the comparison `(X_étale, ε⁻¹f⁻¹𝒪_Y) ⟶ (X_Zar, f⁻¹𝒪_Y)`**, on
sheaves of not necessarily commutative rings: the unit `f⁻¹𝒪_Y ⟶ ε_*(ε⁻¹f⁻¹𝒪_Y)` of the
inverse-image/direct-image adjunction, with commutativity forgotten.

This is the `fSharpRing` of `AlgebraicGeometry.SmallEtale.toZariskiRelativeRingedToposHom`, with
source and target spelled through `Stacks.SheafOfModules.Tensor.ringSheaf`, which is the
spelling the sheaves of modules of a ringed site are indexed by. -/
def relativeRingSheafMap :
    Stacks.SheafOfModules.Tensor.ringSheaf (Scheme.Hom.inverseImageRingedSite f).O ⟶
      ((opensToSmallEtale B X hX).sheafPushforwardContinuous RingCat.{u}
          (Scheme.Hom.inverseImageRingedSite f).J
          (relativeRingedTopos B X hX f).toRingedSite.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (relativeRingedTopos B X hX f).toRingedSite.O) :=
  (toZariskiRelativeRingedToposHom B X hX f).fSharpRing

/-- The pushforward of presheaves of modules along the comparison has a left adjoint: the small
Zariski site of `X` is small, and the morphisms of the small étale site live in the universe of
its objects. -/
instance presheafPushforward_isRightAdjoint_relative :
    (PresheafOfModules.pushforward.{u} (relativeRingSheafMap B X hX f).hom).IsRightAdjoint :=
  Stacks.ModulePullback.isRightAdjoint_pushforward _

/-- The pushforward of sheaves of modules along the comparison has a left adjoint. -/
instance sheafPushforward_isRightAdjoint_relative :
    (SheafOfModules.pushforward.{u} (relativeRingSheafMap B X hX f)).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u}
    (relativeRingSheafMap B X hX f)).isRightAdjoint

/-- **`ε^*` with coefficients in `f⁻¹𝒪_Y`**, `Mod(f⁻¹𝒪_Y) ⥤ Mod(ε⁻¹f⁻¹𝒪_Y)`: the pullback of
sheaves of modules along the comparison of ringed topoi
`(X_étale, ε⁻¹f⁻¹𝒪_Y) ⟶ (X_Zar, f⁻¹𝒪_Y)`. -/
abbrev relativeAssociatedModule :
    RingedSite.Modules.{u, u, u} (Scheme.Hom.inverseImageRingedSite f) ⥤
      RingedSite.Modules.{u + 1, u, u} (relativeRingedTopos B X hX f).toRingedSite :=
  SheafOfModules.pullback.{u} (relativeRingSheafMap B X hX f)

/-- `ε^*` is left adjoint to the pushforward of sheaves of modules along the comparison. -/
def relativeAssociatedModuleAdjunction :
    relativeAssociatedModule B X hX f ⊣
      SheafOfModules.pushforward.{u} (relativeRingSheafMap B X hX f) :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} (relativeRingSheafMap B X hX f)

/-- `ε^*` is additive, being the pullback of sheaves of modules along a morphism of ringed
sites. -/
instance additive_relativeAssociatedModule : (relativeAssociatedModule B X hX f).Additive :=
  inferInstance

/-- `ε^*` is right exact, being a left adjoint. -/
instance preservesFiniteColimits_relativeAssociatedModule :
    PreservesFiniteColimits (relativeAssociatedModule B X hX f) := by
  have := (relativeAssociatedModuleAdjunction B X hX f).leftAdjoint_preservesColimits
  infer_instance

/-! ### `ε` with coefficients in `f⁻¹𝒪_Y` as a morphism of ringed sites, and exactness of `ε^*` -/

/-- **`ε` with coefficients in `f⁻¹𝒪_Y`, as a morphism of ringed sites at independent
universes**: the inclusion of the small Zariski site of `X` into its small étale site, which is
a morphism of sites (`AlgebraicGeometry.SmallEtale.opensToSmallEtale_isMorphismOfSites`), with
structure map the unit `f⁻¹𝒪_Y ⟶ ε_*(ε⁻¹f⁻¹𝒪_Y)`.  It carries the morphism of topoi underlying
`ε`, which `AlgebraicGeometry.SmallEtale.toZariskiRelativeRingedToposHom` does not. -/
def toZariskiRelativeRingedSiteHom :
    RingedSite.HomGeneral (relativeRingedTopos B X hX f).toRingedSite
      (Scheme.Hom.inverseImageRingedSite f) where
  u := opensToSmallEtale B X hX
  isMorphismOfSites := opensToSmallEtale_isMorphismOfSites B X hX
  fsharp := (inverseImageCommRingAdjunction B X hX).unit.app
    (Scheme.Hom.inverseImageCommRingSheaf f)

/-- **The inverse-image form of the structure map of `ε` with coefficients in `f⁻¹𝒪_Y` is an
isomorphism**: it is the comparison `AlgebraicGeometry.SmallEtale.invCommRingIso` of the two
models of `ε⁻¹` on sheaves of commutative rings, at `f⁻¹𝒪_Y`.  Both the topos inverse image and
the sheaf pullback are left adjoints of the pushforward along the inclusion of the small Zariski
site, and the structure map is the transpose of the unit of the second adjunction. -/
theorem toZariskiRelativeRingedSiteHom_fSharpInverseImage :
    (toZariskiRelativeRingedSiteHom B X hX f).toRingedToposHom.fSharpInverseImage =
      (invCommRingIso B X hX).hom.app (Scheme.Hom.inverseImageCommRingSheaf f) := by
  have h := homEquiv_symm_comp_leftAdjointUniq
    ((Stacks.Sheaves.ToposPushforward.commRingImageAdjunction.{u, u, u, u + 1, u, u}
      (toposHom B X hX)).ofNatIsoRight (pushCommRingIso B X hX))
    (inverseImageCommRingAdjunction B X hX) (Scheme.Hom.inverseImageCommRingSheaf f)
    (relativeStructureSheaf B X hX f) (toZariskiRelativeRingedToposHom B X hX f).fSharp
  have h2 := homEquiv_symm_ofNatIsoRight
    (Stacks.Sheaves.ToposPushforward.commRingImageAdjunction.{u, u, u, u + 1, u, u}
      (toposHom B X hX))
    (pushCommRingIso B X hX) (Scheme.Hom.inverseImageCommRingSheaf f)
    (relativeStructureSheaf B X hX f) (toZariskiRelativeRingedToposHom B X hX f).fSharp
  rw [homEquiv_symm_toZariskiRelativeRingedToposHom_fSharp, Category.comp_id] at h
  exact h2.symm.trans h

/-- The inverse-image form of the structure map of `ε` with coefficients in `f⁻¹𝒪_Y` is an
isomorphism. -/
theorem isIso_toZariskiRelativeRingedSiteHom_fSharpInverseImage :
    IsIso (toZariskiRelativeRingedSiteHom B X hX f).toRingedToposHom.fSharpInverseImage := by
  rw [toZariskiRelativeRingedSiteHom_fSharpInverseImage]
  exact inferInstanceAs
    (IsIso ((invCommRingIso B X hX).app (Scheme.Hom.inverseImageCommRingSheaf f)).hom)

/-- **`ε^*` with coefficients in `f⁻¹𝒪_Y` is the pullback along the morphism of ringed topoi
attached to `ε`.**  This is
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral` at
`toZariskiRelativeRingedSiteHom`, the site-presented pullback being `relativeAssociatedModule`
on the nose. -/
def pullbackModulesRelativeIso :
    Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u, u, u, u + 1, u, u}
        (toZariskiRelativeRingedSiteHom B X hX f).toRingedToposHom.toRingedToposModulesHom ≅
      relativeAssociatedModule B X hX f :=
  (toZariskiRelativeRingedSiteHom B X hX f).pullbackModulesToposIsoGeneral

/-- **`ε^*` with coefficients in `f⁻¹𝒪_Y` is exact**: the second assertion of Stacks 08H8 in its
relative form.  The structure map of `ε` with these coefficients is an isomorphism in
inverse-image form (`toZariskiRelativeRingedSiteHom_fSharpInverseImage`), hence flat, so Stacks
04JC applies to the morphism of ringed topoi attached to `ε`. -/
instance preservesFiniteLimits_relativeAssociatedModule :
    PreservesFiniteLimits (relativeAssociatedModule B X hX f) := by
  have hpf := ((exactFunctor_iff _).mp
    (Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap
      (toZariskiRelativeRingedSiteHom B X hX f).toRingedToposHom
      (AlgebraicGeometry.SheafOfModules.isFlatMapULift_of_isIso _
        (isIso_toZariskiRelativeRingedSiteHom_fSharpInverseImage B X hX f)))).1
  exact preservesFiniteLimits_of_natIso (pullbackModulesRelativeIso B X hX f)

/-! ### The stalks of `ε^*` at the geometric points -/

/-- The geometric point of `X` at a point `x`, as a point of the small étale site of `X`. -/
abbrev relativeEtalePoint (x : X) : (topology B X hX).Point.{u} :=
  geometricPointSitePoint B X hX (.ofPoint X x)

/-- A lift into an open `V` of the geometric point of `X` at `x` exists only if `x ∈ V`. -/
theorem mem_of_relativeEtalePoint_fiber {x : X} {V : X.Opens}
    (p : (relativeEtalePoint B X hX x).fiber.obj ((opensToSmallEtale B X hX).obj V)) :
    x ∈ V := by
  let q : (GeometricPoint.ofPoint X x).source ⟶ (V : Scheme.{u}) := p.1
  have hp : q ≫ V.ι = (GeometricPoint.ofPoint X x).hom := p.2
  have h1 : V.ι (q default) = x := by
    rw [← Scheme.Hom.comp_apply, hp]
    exact GeometricPoint.ofPoint_liesOver X x
  rw [← h1]
  exact (Scheme.Opens.range_ι V).subset (Set.mem_range_self _)

/-- Lifts of the geometric point of `X` at `x` into an open of `X` are unique, the open immersion
being a monomorphism. -/
theorem relativeEtalePoint_fiber_ext {x : X} {V : X.Opens}
    (p q : (relativeEtalePoint B X hX x).fiber.obj ((opensToSmallEtale B X hX).obj V)) :
    p = q := by
  apply Subtype.ext
  let p' : (GeometricPoint.ofPoint X x).source ⟶ (V : Scheme.{u}) := p.1
  let q' : (GeometricPoint.ofPoint X x).source ⟶ (V : Scheme.{u}) := q.1
  have hp : p' ≫ V.ι = (GeometricPoint.ofPoint X x).hom := p.2
  have hq : q' ≫ V.ι = (GeometricPoint.ofPoint X x).hom := q.2
  exact (cancel_mono V.ι).1 (hp.trans hq.symm)

/-- The lift of the geometric point of `X` at `x` into an open containing `x`. -/
noncomputable def relativeEtalePointFiberOfMem {x : X} {V : X.Opens} (hx : x ∈ V) :
    (relativeEtalePoint B X hX x).fiber.obj ((opensToSmallEtale B X hX).obj V) :=
  let l : (GeometricPoint.ofPoint X x).source ⟶ (V : Scheme.{u}) :=
    IsOpenImmersion.lift V.ι (GeometricPoint.ofPoint X x).hom (by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι, Subsingleton.elim t default]
      exact (GeometricPoint.ofPoint_liesOver X x).symm ▸ hx)
  ⟨l, (IsOpenImmersion.lift_fac V.ι (GeometricPoint.ofPoint X x).hom _ :
    l ≫ V.ι = (GeometricPoint.ofPoint X x).hom)⟩

/-- **The geometric point of `X` at `x`, restricted to the small Zariski site, is the point `x`.**
The lifts of the geometric point into an open `V` are the proofs that `x ∈ V`: one exists exactly
then, and it is unique, the open immersion of `V` being a monomorphism. -/
def relativeEtalePointFiberIso (x : X) :
    opensToSmallEtale B X hX ⋙ (relativeEtalePoint B X hX x).fiber ≅
      (Opens.pointGrothendieckTopology x).fiber :=
  NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun p => ⟨⟨mem_of_relativeEtalePoint_fiber B X hX p⟩⟩
      invFun := fun h => relativeEtalePointFiberOfMem B X hX h.down.down
      left_inv := fun p => relativeEtalePoint_fiber_ext B X hX _ _
      right_inv := fun _ => Subsingleton.elim _ _ })
    (fun _ => by ext; exact Subsingleton.elim _ _)

/-- **The matched pair of points of `ε`.**  The stalk at `x` of a sheaf of sets on the small
Zariski site of `X` is the stalk of its inverse image along `ε` at the geometric point of `X`
at `x`. -/
def relativeSheafFiberIso (x : X) :
    (Opens.pointGrothendieckTopology x).sheafFiber (A := Type u) ≅
      (toZariskiRelativeRingedSiteHom B X hX f).toposHom.inverseImage ⋙
        (relativeEtalePoint B X hX x).sheafFiber (A := Type u) :=
  (sheafFiberIsoOfAdjOfFiberIso (Opens.pointGrothendieckTopology x)
    (relativeEtalePoint B X hX x) (opensToSmallEtale B X hX)
    (relativeEtalePointFiberIso B X hX x)
    (toZariskiRelativeRingedSiteHom B X hX f).toposHom.adj).symm

/-- The homomorphism `(f⁻¹𝒪_Y)_x ⟶ (ε⁻¹f⁻¹𝒪_Y)_{x̄}` of stalk rings along which the stalk of `ε^*`
at the geometric point `x̄` of `X` at `x` extends scalars. -/
abbrev relativeStalkRingMap (x : X) :=
  Stacks.Sheaves.StalkPullback.stalkRingMap
    (toZariskiRelativeRingedSiteHom B X hX f).toRingedToposHom.toRingedToposModulesHom
    (relativeEtalePoint B X hX x) (Opens.pointGrothendieckTopology x)
    (relativeSheafFiberIso B X hX f x)

/-- **Stacks 05V5 for `ε` with coefficients in `f⁻¹𝒪_Y`.**  The stalk of `ε^*M` at the geometric
point of `X` at `x` is the extension of scalars of the stalk `M_x` along the homomorphism
`relativeStalkRingMap` of stalk rings, naturally in the `f⁻¹𝒪_Y`-module `M`. -/
def relativeStalkFunctorIso (x : X) :
    relativeAssociatedModule B X hX f ⋙
        Stacks.sheafModuleFiberOfCommRing (relativeEtalePoint B X hX x)
          (relativeRingedTopos B X hX f).toRingedSite.O ≅
      Stacks.sheafModuleFiberOfCommRing (Opens.pointGrothendieckTopology x)
          (Scheme.Hom.inverseImageRingedSite f).O ⋙
        ModuleCat.extendScalars (relativeStalkRingMap B X hX f x) :=
  Functor.isoWhiskerRight (pullbackModulesRelativeIso B X hX f).symm _ ≪≫
    Stacks.Sheaves.StalkPullback.stalkFunctorIso
      (toZariskiRelativeRingedSiteHom B X hX f).toRingedToposHom.toRingedToposModulesHom
      (relativeEtalePoint B X hX x) (Opens.pointGrothendieckTopology x)
      (relativeSheafFiberIso B X hX f x)

/-- **The homomorphism of stalk rings of `ε` with coefficients in `f⁻¹𝒪_Y` is bijective**: it is
an isomorphism of stalk rings followed by the stalk of the inverse-image form of the structure
map, which is an isomorphism (`toZariskiRelativeRingedSiteHom_fSharpInverseImage`). -/
theorem bijective_relativeStalkRingMap (x : X) :
    Function.Bijective (relativeStalkRingMap B X hX f x) := by
  have hθ : IsIso (Stacks.Sheaves.RingedToposModules.fSharpCommRing
      (toZariskiRelativeRingedSiteHom B X hX f).toRingedToposHom.toRingedToposModulesHom) := by
    have h := isIso_toZariskiRelativeRingedSiteHom_fSharpInverseImage B X hX f
    have hZ : ∀ Z, IsIso ((Stacks.Sheaves.RingedToposModules.fSharpCommRing
        (toZariskiRelativeRingedSiteHom B X hX f).toRingedToposHom.toRingedToposModulesHom).app
          Z) := fun Z => by
      have hb : Function.Bijective (((sheafToPresheaf _ _).map
          (toZariskiRelativeRingedSiteHom B X hX f).toRingedToposHom.fSharpInverseImage).app Z) :=
        ConcreteCategory.bijective_of_isIso _
      exact (ConcreteCategory.isIso_iff_bijective _).2 hb
    exact NatIso.isIso_of_isIso_app _
  exact (ConcreteCategory.bijective_of_isIso
    (((relativeEtalePoint B X hX x).presheafFiber (A := CommRingCat.{u})).map _)).comp
    (RingEquiv.bijective _)

/-! ### `ε^*` on derived categories, and Tor amplitude across it -/

section Derived

variable [PreservesFiniteLimits (relativeAssociatedModule B X hX f)]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} (Scheme.Hom.inverseImageRingedSite f))]
  [HasDerivedCategory.{e}
    (RingedSite.Modules.{u + 1, u, u} (relativeRingedTopos B X hX f).toRingedSite)]

/-- **`ε^*` on derived categories**, `D(f⁻¹𝒪_Y) ⥤ D(ε⁻¹f⁻¹𝒪_Y)`.

Over exactness of `ε^*` this is the induced functor on the unbounded derived categories, with no
resolution; `CategoryTheory.Limits.PreservesFiniteColimits` is data rather than a proposition,
so a consumer should transport along an isomorphism rather than rebuild it.  Exactness is the
instance `preservesFiniteLimits_relativeAssociatedModule`. -/
def relativeDerivedAssociatedModule :
    RingedSite.DerivedModules.{u, u, u, d} (Scheme.Hom.inverseImageRingedSite f) ⥤
      RingedSite.DerivedModules.{u + 1, u, u, e} (relativeRingedTopos B X hX f).toRingedSite :=
  (relativeAssociatedModule B X hX f).mapDerivedCategory

end Derived

section DerivedStalks

open StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard

variable
  [hd : HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} (Scheme.Hom.inverseImageRingedSite f))]
  [he : HasDerivedCategory.{e}
    (RingedSite.Modules.{u + 1, u, u} (relativeRingedTopos B X hX f).toRingedSite)]

/-- Canonical Tor amplitude depends only on the isomorphism class of an object of `D(R)`. -/
private theorem hasTorAmplitudeCanonical_iff_of_iso {R : Type u} [CommRing R]
    {E F : letI := HasDerivedCategory.standard (ModuleCat.{u} R); DerivedCategory (ModuleCat.{u} R)}
    (e : letI := HasDerivedCategory.standard (ModuleCat.{u} R); E ≅ F) (a b : ℤ) :
    HasTorAmplitudeCanonical R E a b ↔ HasTorAmplitudeCanonical R F a b :=
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  ⟨AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e a b,
    AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e.symm a b⟩

/-- **The derived stalk of `ε^*E` at a geometric point is the derived stalk of `E`.**  The derived
stalk of `ε^*E` at the geometric point of `X` at `x` has Tor amplitude in `[a, b]` over
`(ε⁻¹f⁻¹𝒪_Y)_{x̄}` exactly when the derived stalk `E_x` has Tor amplitude in `[a, b]` over
`(f⁻¹𝒪_Y)_x`: by Stacks 05V5 (`relativeStalkFunctorIso`) the first is the second with its scalars
extended along the bijective `relativeStalkRingMap`. -/
theorem hasTorAmplitudeCanonical_derivedModuleFiber_relativeDerivedAssociatedModule_iff
    (x : X) (E : RingedSite.DerivedModules.{u, u, u, d} (Scheme.Hom.inverseImageRingedSite f))
    (a b : ℤ) :
    letI : HasDerivedCategory.{d} (SheafOfModules.{u}
        (Stacks.commRingSheafToRingSheaf.{u, u, u} (Scheme.Hom.inverseImageRingedSite f).O)) := hd
    letI : HasDerivedCategory.{e} (SheafOfModules.{u}
        (Stacks.commRingSheafToRingSheaf.{u, u + 1, u}
          (relativeRingedTopos B X hX f).toRingedSite.O)) := he
    HasTorAmplitudeCanonical
        (((relativeEtalePoint B X hX x).presheafFiber (A := CommRingCat.{u})).obj
          (relativeRingedTopos B X hX f).toRingedSite.O.obj)
        ((Stacks.derivedModuleFiber (relativeEtalePoint B X hX x)
          (relativeRingedTopos B X hX f).toRingedSite.O).obj
          ((relativeDerivedAssociatedModule B X hX f).obj E)) a b ↔
      HasTorAmplitudeCanonical
        (((Opens.pointGrothendieckTopology x).presheafFiber (A := CommRingCat.{u})).obj
          (Scheme.Hom.inverseImageRingedSite f).O.obj)
        ((Stacks.derivedModuleFiber (Opens.pointGrothendieckTopology x)
          (Scheme.Hom.inverseImageRingedSite f).O).obj E) a b := by
  let : HasDerivedCategory.{d} (SheafOfModules.{u}
      (Stacks.commRingSheafToRingSheaf.{u, u, u} (Scheme.Hom.inverseImageRingedSite f).O)) := hd
  let : HasDerivedCategory.{e} (SheafOfModules.{u}
      (Stacks.commRingSheafToRingSheaf.{u, u + 1, u}
        (relativeRingedTopos B X hX f).toRingedSite.O)) := he
  let K := DerivedCategory.Q.objPreimage E
  let eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let ψ := RingEquiv.ofBijective (relativeStalkRingMap B X hX f x)
    (bijective_relativeStalkRingMap B X hX f x)
  let Fx := Stacks.sheafModuleFiberOfCommRing (Opens.pointGrothendieckTopology x)
    (Scheme.Hom.inverseImageRingedSite f).O
  let Fe := Stacks.sheafModuleFiberOfCommRing (relativeEtalePoint B X hX x)
    (relativeRingedTopos B X hX f).toRingedSite.O
  let N : relativeAssociatedModule B X hX f ⋙ Fe ≅
      Fx ⋙ ModuleCat.restrictScalars ψ.symm.toRingHom :=
    relativeStalkFunctorIso B X hX f x ≪≫
      Functor.isoWhiskerLeft Fx (ModuleCat.extendScalarsIsoRestrictScalarsSymm ψ)
  let C := (Fx.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let eC : (Fe.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((relativeAssociatedModule B X hX f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      ((ModuleCat.restrictScalars ψ.symm.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C :=
    HomologicalComplex.Hom.isoOfComponents (fun i => N.app (K.X i))
      (fun i j _ => (N.hom.naturality (K.d i j)).symm)
  let e₁ : (Stacks.derivedModuleFiber (relativeEtalePoint B X hX x)
        (relativeRingedTopos B X hX f).toRingedSite.O).obj
        ((relativeDerivedAssociatedModule B X hX f).obj E) ≅
      DerivedCategory.Q.obj (((ModuleCat.restrictScalars ψ.symm.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C) :=
    (Stacks.derivedModuleFiber (relativeEtalePoint B X hX x)
        (relativeRingedTopos B X hX f).toRingedSite.O).mapIso
        ((relativeDerivedAssociatedModule B X hX f).mapIso eK.symm ≪≫
          (relativeAssociatedModule B X hX f).mapDerivedCategoryFactors.app K) ≪≫
      Fe.mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso eC
  let e₂ : (Stacks.derivedModuleFiber (Opens.pointGrothendieckTopology x)
        (Scheme.Hom.inverseImageRingedSite f).O).obj E ≅ DerivedCategory.Q.obj C :=
    (Stacks.derivedModuleFiber (Opens.pointGrothendieckTopology x)
        (Scheme.Hom.inverseImageRingedSite f).O).mapIso eK.symm ≪≫
      Fx.mapDerivedCategoryFactors.app K
  exact (hasTorAmplitudeCanonical_iff_of_iso e₁ a b).trans
    ((AffineRelativeTorAmplitude.hasTorAmplitudeCanonical_restrictScalars_ringEquiv_iff
      ψ.symm C a b).trans (hasTorAmplitudeCanonical_iff_of_iso e₂ a b).symm)

end DerivedStalks

section TorAmplitude

variable
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} (Scheme.Hom.inverseImageRingedSite f))]
  [HasDerivedCategory.{e}
    (RingedSite.Modules.{u + 1, u, u} (relativeRingedTopos B X hX f).toRingedSite)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    (Scheme.Hom.inverseImageRingedSite f).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    (Scheme.Hom.inverseImageRingedSite f).O).obj M).Additive]
  [∀ (K L : CochainComplex
      (RingedSite.Modules.{u, u, u} (Scheme.Hom.inverseImageRingedSite f)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (Scheme.Hom.inverseImageRingedSite f).O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (relativeRingedTopos B X hX f).toRingedSite.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (relativeRingedTopos B X hX f).toRingedSite.O).obj M).Additive]
  [∀ (K L : CochainComplex
      (RingedSite.Modules.{u + 1, u, u} (relativeRingedTopos B X hX f).toRingedSite) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (relativeRingedTopos B X hX f).toRingedSite.O)
      (ComplexShape.up ℤ)]

variable
  (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d}
    (Scheme.Hom.inverseImageRingedSite f))
  (T' : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
    (relativeRingedTopos B X hX f).toRingedSite)

/-- **Stacks 0DK7, part (1).**  Let `f : X ⟶ Y` be a morphism of schemes and let `E` be an
object of `D(f⁻¹𝒪_Y)`.  Then `E` has Tor amplitude in `[a, b]` if and only if `ε^*E` has Tor
amplitude in `[a, b]` as an object of `D(ε⁻¹f⁻¹𝒪_Y)`.

Both sides are read at the stalks by Stacks 0DJJ: on the small Zariski site of `X` at the points
of `X`, a conservative family, and on the small étale site at the geometric points of `X` at the
points of `X`, a conservative family too
(`AlgebraicGeometry.isConservativeFamilyOfPoints_geometricSitePoints`).  At the point `x` the
two stalks agree, by Stacks 05V5 for `ε`
(`hasTorAmplitudeCanonical_derivedModuleFiber_relativeDerivedAssociatedModule_iff`). -/
@[stacks 0DK7 "part (1), with `ε⁻¹f⁻¹𝒪_Y` for `f_small⁻¹𝒪_{Y_étale}`; see the implementation \
notes.  The form with `f_small⁻¹𝒪_{Y_étale}` itself is, in `AlgebraicGeometry.Space`, \
`hasTorAmplitude_derivedScalarRestriction_iff_representedZariskiDerivedPullback`"]
theorem hasTorAmplitude_relativeDerivedAssociatedModule_iff
    (E : RingedSite.DerivedModules.{u, u, u, d} (Scheme.Hom.inverseImageRingedSite f))
    (a b : ℤ) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude T E a b ↔
      Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude T'
        ((relativeDerivedAssociatedModule B X hX f).obj E) a b := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine
      Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_forall_derivedModuleFiber_family
      T' _ a b (fun x : X => relativeEtalePoint B X hX x)
      (isConservativeFamilyOfPoints_geometricSitePoints B X hX) fun x => ?_
    exact (hasTorAmplitudeCanonical_derivedModuleFiber_relativeDerivedAssociatedModule_iff
      B X hX f x E a b).2
      (Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeCanonical_derivedModuleFiber
        T E a b h _)
  · refine
      Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_forall_derivedModuleFiber_family
      T E a b (fun x : X => Opens.pointGrothendieckTopology x)
      (Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology X) fun x => ?_
    exact (hasTorAmplitudeCanonical_derivedModuleFiber_relativeDerivedAssociatedModule_iff
      B X hX f x E a b).1
      (Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeCanonical_derivedModuleFiber
        T' _ a b h _)

/-- **Finite Tor dimension across the comparison.**  An object `E` of `D(f⁻¹𝒪_Y)` has finite
Tor dimension if and only if `ε^*E` has finite Tor dimension as an object of `D(ε⁻¹f⁻¹𝒪_Y)`.

This is `hasTorAmplitude_relativeDerivedAssociatedModule_iff` quantified over the interval.  It
is not part (2) of Stacks 0DK7, which is about *locally* finite Tor dimension, and no tag is
placed here. -/
theorem hasFiniteTorDimension_relativeDerivedAssociatedModule_iff
    (E : RingedSite.DerivedModules.{u, u, u, d} (Scheme.Hom.inverseImageRingedSite f)) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension T E ↔
      Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension T'
        ((relativeDerivedAssociatedModule B X hX f).obj E) :=
  exists₂_congr fun a b => hasTorAmplitude_relativeDerivedAssociatedModule_iff B X hX f T T' E a b

end TorAmplitude

end AlgebraicGeometry.SmallEtale

end
