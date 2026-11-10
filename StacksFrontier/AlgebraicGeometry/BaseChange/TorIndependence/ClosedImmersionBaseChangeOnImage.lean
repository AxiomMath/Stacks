module

public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeFour.ClosedImmersionBaseChangeOffImage
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.LocalRingPushout
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkSpellingFunctorBridge

/-!
# Derived base change along a closed immersion, on the closed subscheme

Consider a cartesian diagram of schemes

```
Z' --i'--> X'
|g          |f
Z --i-----> X
```

with `i` a closed immersion, and suppose `Z` and `X'` are Tor independent over `X`.  Stacks 0E23
asserts that the canonical derived base change map `Lf^*(Ri_* K) ⟶ Ri'_*(Lg^* K)` of Stacks 08HY
is an isomorphism of functors `D(𝒪_Z) ⟶ D(𝒪_{X'})`.

Invertibility in the derived category is detected on derived stalks, and
`StacksFrontier/AlgebraicGeometry/Perfect/BaseChangeFour/ClosedImmersionBaseChangeOffImage.lean`
settles the points of `X'` outside `Z'`, where both sides vanish.  This file contributes the two
remaining pieces that do not need a diagram chase:

* the reduction of Stacks 0E23 to the points *on* `Z'`, both at a single complex and as an
  isomorphism of functors;
* the ring-level invertibility that Tor independence supplies there, namely Stacks 0661 read at
  the four local rings of the square at a point of `Z'`.

Where Stacks 0E23 itself is proved is recorded in the implementation notes below.

## Main definitions

* `Stacks.Cohomology.ClosedImmersionBaseChange.modulesStalkFunctorCongr` and
  `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkFunctorCongr`: the stalk functor and
  the derived stalk functor transported along an equality of points, which is what relates the
  two presentations `i (g w)` and `f (i' w)` of one point of `X`.
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIsoOfOnImage`: Stacks 0E23
  as an isomorphism of functors, from the on-image clause.

## Main results

* `Stacks.Cohomology.ClosedImmersionBaseChange.comp_toShHom_of_isPullback`: the commutativity of
  the square, in the ringed-space spelling the derived base change map is stated in.
* `Stacks.Cohomology.ClosedImmersionBaseChange.isIso_derivedBaseChangeMap_of_onImage`: **the
  reduction to the closed subscheme.**  If the derived base change map has invertible derived
  stalk at every point of the form `i' w`, it is an isomorphism.
* `Stacks.Cohomology.ClosedImmersionBaseChange.isIso_derivedBaseChangeSquare_of_onImage`: the
  same for the morphism of functors, hence at every complex simultaneously.
* `Stacks.Cohomology.ClosedImmersionBaseChange.stalkMap_ringHom_square`: the square of germ maps
  of local rings at a point of `Z'`, as ring homomorphisms.
* `Stacks.Cohomology.ClosedImmersionBaseChange.torIndependent_stalkMap_of_torIndependent`: Tor
  independence of `Z` and `X'` over `X` read at the local rings of a point of `Z'`, with the
  algebra structures the germ maps themselves induce.
* `Stacks.Cohomology.ClosedImmersionBaseChange.isIso_derivedBaseChangeComparison_stalk`:
  **Stacks 0661 at the local rings of the square.**  The canonical comparison from derived base
  change over `𝒪_{X, i (g w)}` to derived base change over `𝒪_{Z, g w}` is invertible, for every
  choice of models of the two total derived extension-of-scalars functors.

## Implementation notes

*Why the reduction is stated with the on-image clause as a hypothesis.*  The two halves of the
stalkwise criterion are of completely different difficulty: off `Z'` both sides of the comparison
are zero objects, while on `Z'` the comparison has to be identified with the ring-level one.
Separating them lets the easy half be used, and makes the hard half a single named goal.

*Which spelling of the derived stalk appears where.*  The stalkwise criterion
`Stacks.Cohomology.StalkwiseIso.isIso_iff_forall_derivedStalk_isIso` is stated over the
`RingCat`-valued stalk of the sheaf of rings, while everything about Tor independence is stated
over the local ring `𝒪_{X',x'}`.  `AlgebraicGeometry.isIso_derivedStalkFunctor_map_iff` crosses
between them.  It has to be used through `Iff.mp` rather than `rw`: `X'.ringCatSheaf` and
`structureSheafRing X'.toSheafedSpace` are definitionally equal and not
syntactically equal, so a syntactic rewrite does not fire where unification at default
transparency succeeds.

*The two presentations of the point of `X`.*  The square commutes only up to a propositional
equality, so the point `f (i' w)` of `X` and the point `i (g w)` are equal without being the same
term, and the two local rings `𝒪_{X, f (i' w)}` and `𝒪_{X, i (g w)}` are two objects.  Everything
below is written at `i (g w)`, which is the presentation
`Stacks.Cohomology.StalkPushout.isPushout_stalkMap_toAlgebra_of_isPullback` and
`AlgebraicGeometry.BaseChangeTorAmplitude.ringTorIndependent_of_schemeTorIndependent_stalks` use;
the germ map of `f` then carries a `TopCat.Presheaf.stalkCongr`.  `derivedStalkFunctorCongr` is
the comparison needed in the other direction, for `AlgebraicGeometry.derivedPullbackStalkIso`,
which is stated at `f (i' w)`.

*Why `isIso_derivedBaseChangeComparison_stalk` takes the derived functors as parameters.*  Stacks
0661 is stated for an arbitrary pair of models of the two total left derived functors, and so is
this.  That is not generality for its own sake: the geometric chain presents derived extension of
scalars at the stalks through `AlgebraicGeometry.derivedPullbackStalkIso`, whose model is
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`, and a consumer discharges
the two `Functor.IsLeftDerivedFunctor` hypotheses from that structure's own field.  Taking them as
hypotheses also keeps the two instances out of instance search, which does not find a structure
field.

*The two algebra transports.*  The Tor independence of the stalks is available with the germ map
of `f` written `eqToHom ... ≫ f.stalkMap (i' w)` and the pushout of the stalks with it written
`(stalkCongr ...).hom ≫ f.stalkMap (i' w)`; the two spellings give two `Algebra` instances and
hence two statements.  `stalkCongr_hom_eq_eqToHom` identifies them, and
`torIndependent_stalkMap_of_torIndependent` moves the Tor statement to the pushout's spelling, so
that one set of instances serves Stacks 0661.

*Where Stacks 0E23 is proved.*  Nothing in this file carries the tag.  The on-image clause
consumed by `isIso_derivedBaseChangeSquare_of_onImage` is
`Stacks.Cohomology.ClosedImmersionBaseChange.isIso_derivedStalk_derivedBaseChangeMap_onImage`, and
Stacks 0E23 itself is `Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareAsIso`,
both in `ClosedImmersionBaseChangeTorIndependent.lean`.

## References

* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars
open RingTheory.TorIndependence

noncomputable section

namespace Stacks.Cohomology.ClosedImmersionBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

/-- `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` carries the left-derived
universal property in a structure field, and a structure field is not found by instance search;
this re-seats it where the hypotheses of Stacks 0661 can pick it up. -/
local instance isLeftDerivedFunctor_totalDerivedExtensionScalars {R A : Type u}
    [CommRing R] [CommRing A] (φ : R →+* A) :
    (totalDerivedExtensionScalars.{u, u, u} φ).functor.IsLeftDerivedFunctor
      (totalDerivedExtensionScalars.{u, u, u} φ).comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  (totalDerivedExtensionScalars.{u, u, u} φ).isLeftDerived

/-! ### Transport of the stalk functor along an equality of points -/

section Congr

variable {Y : Scheme.{u}}

/-- Restriction of scalars along the comparison of the stalk rings at two equal points preserves
finite limits.  Mathlib's instance is for commutative rings and the germ comparison is a morphism
of `CommRingCat`. -/
local instance preservesFiniteLimits_restrictScalars_stalkCongr {a b : Y} (h : a = b) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u, u, u}
      (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom) :=
  inferInstance

/-- Restriction of scalars along the comparison of the stalk rings at two equal points preserves
finite colimits. -/
local instance preservesFiniteColimits_restrictScalars_stalkCongr {a b : Y} (h : a = b) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u, u, u}
      (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom) :=
  inferInstance

/-- **The germ comparison at two equal points is the transport.** -/
theorem stalkCongr_hom_eq_eqToHom {a b : Y} (h : a = b) :
    (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom
      = eqToHom (congrArg (fun z => Y.presheaf.stalk z) h) := by
  subst h; simp [TopCat.Presheaf.stalkCongr]

/-- **The stalk functor at two equal points.**  For `h : a = b` the stalk at `b`, with scalars
restricted along the comparison `𝒪_{Y,a} ≅ 𝒪_{Y,b}`, is the stalk at `a`.

The two points are equal, so the statement is proved by substituting one for the other; what is
left is that the comparison becomes the identity and that restriction of scalars along the
identity is the identity functor. -/
def modulesStalkFunctorCongr {a b : Y} (h : a = b) :
    Stacks.ModuleSkyscraper.modulesStalkFunctor Y b ⋙
        ModuleCat.restrictScalars.{u, u, u}
          (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom ≅
      Stacks.ModuleSkyscraper.modulesStalkFunctor Y a := by
  subst h
  exact Functor.isoWhiskerLeft _
      (eqToIso (congrArg (fun φ => ModuleCat.restrictScalars.{u, u, u} φ)
        (congrArg CommRingCat.Hom.hom (stalkCongr_hom_eq_eqToHom (rfl : a = a))))) ≪≫
    Functor.isoWhiskerLeft _ (ModuleCat.restrictScalarsId'.{u, u} _ rfl) ≪≫
    Functor.rightUnitor _

open Stacks.Cohomology.PerfectComplexTriangles in
/-- **The derived stalk functor at two equal points.**  `modulesStalkFunctorCongr` on unbounded
derived categories: every functor in it is exact, so the underived comparison is carried along
`Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso`, with
`Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso` splitting the composite.

This is the comparison Stacks 0E23 needs between `AlgebraicGeometry.derivedPullbackStalkIso`,
which is stated at the point `f (i' w)`, and the computation of the derived stalk of `Ri_*`,
which is stated at the point `i (g w)`. -/
def derivedStalkFunctorCongr {a b : Y} (h : a = b) :
    AlgebraicGeometry.derivedStalkFunctor b ⋙
        (ModuleCat.restrictScalars.{u, u, u}
          (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom).mapDerivedCategory ≅
      AlgebraicGeometry.derivedStalkFunctor a :=
  (mapDerivedCategoryCompIso (Stacks.ModuleSkyscraper.modulesStalkFunctor Y b)
      (ModuleCat.restrictScalars.{u, u, u}
        (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom)).symm ≪≫
    mapDerivedCategoryIsoOfNatIso _ _ (modulesStalkFunctorCongr h)

/-- **The germ comparison of a point with itself is the identity homomorphism.**  The identity
case of `stalkCongr_hom_eq_eqToHom`, read as an equation of ring homomorphisms: this is the
hypothesis `ModuleCat.restrictScalarsId'` and
`StacksDraft.DerivedRingIso.restrictScalarsIdDerivedIso` ask for. -/
theorem stalkCongr_self_hom_hom {a : Y} (h : a = a) :
    (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom
      = RingHom.id (ToType (Y.presheaf.stalk a)) := by
  simp

/-- **`modulesStalkFunctorCongr` at a self-equality of points, unfolded.**  Its definition
substitutes one point for the other, so at an equality of a point with itself the substitution
reduces and the definition is visible: the transport of restriction of scalars along
`stalkCongr_hom_eq_eqToHom`, then the collapse of restriction of scalars along the identity.

Stated here, where that reduction is reflexivity, so that no consumer unfolds the definition. -/
theorem modulesStalkFunctorCongr_unfold {a : Y} (h : a = a) :
    modulesStalkFunctorCongr h =
      Functor.isoWhiskerLeft (Stacks.ModuleSkyscraper.modulesStalkFunctor Y a)
          (eqToIso (congrArg (fun φ => ModuleCat.restrictScalars.{u, u, u} φ)
            (congrArg CommRingCat.Hom.hom (stalkCongr_hom_eq_eqToHom (rfl : a = a))))) ≪≫
        Functor.isoWhiskerLeft _ (ModuleCat.restrictScalarsId'.{u, u} _ rfl) ≪≫
          Functor.rightUnitor _ := rfl

end Congr

/-! ### The reduction of Stacks 0E23 to the closed subscheme -/

section Square

variable {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X}

/-- **The square commutes as a square of ringed spaces.**  This is the commutativity hypothesis
in the spelling `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap` asks for, with the
scheme-theoretic square of Stacks 0E23 matched to the square of Stacks 08HY by `g' := g`,
`f' := i'`, `f := i` and `g := f`. -/
theorem comp_toShHom_of_isPullback (sq : IsPullback i' g f i) :
    g.toLRSHom.toShHom ≫ i.toLRSHom.toShHom =
      i'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom := by
  simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
    congrArg (fun h : Z' ⟶ X => h.toLRSHom.toShHom) sq.w.symm

/-- **Stacks 0E23 reduces to the points of the closed subscheme.**  In a cartesian square of
schemes with `i` a closed immersion, the derived base change map `Lf^*(Ri_* K) ⟶ Ri'_*(Lg^* K)` is
an isomorphism as soon as its derived stalk is invertible at every point of the form `i' w`.

Invertibility is tested on derived stalks by
`Stacks.Cohomology.StalkwiseIso.isIso_iff_forall_derivedStalk_isIso`, and at a point outside the
image of `i'` the derived stalk is invertible unconditionally by
`isIso_derivedStalk_derivedBaseChangeMap`, both sides being zero objects there.  No Tor
independence is used: it is needed only for the hypothesis. -/
theorem isIso_derivedBaseChangeMap_of_onImage (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (hon : ∀ w : Z', IsIso ((AlgebraicGeometry.derivedStalkFunctor (i' w)).map
      (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g.toLRSHom.toShHom
        i'.toLRSHom.toShHom i.toLRSHom.toShHom f.toLRSHom.toShHom
        (comp_toShHom_of_isPullback sq) K))) :
    IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g.toLRSHom.toShHom
      i'.toLRSHom.toShHom i.toLRSHom.toShHom f.toLRSHom.toShHom
      (comp_toShHom_of_isPullback sq) K) := by
  refine (Stacks.Cohomology.StalkwiseIso.isIso_iff_forall_derivedStalk_isIso
    (structureSheafRing X'.toRingedSpace) _).2 fun x' => ?_
  refine (AlgebraicGeometry.isIso_derivedStalkFunctor_map_iff _ _).1 ?_
  by_cases hx' : x' ∈ Set.range (⇑i')
  · obtain ⟨w, rfl⟩ := hx'
    exact hon w
  · exact isIso_derivedStalk_derivedBaseChangeMap sq K x' hx'

/-- **Stacks 0E23 at the level of functors, reduced to the closed subscheme.**  The canonical
morphism of functors `Ri_* ⋙ Lf^* ⟶ Lg^* ⋙ Ri'_*` of Stacks 08HY is an isomorphism as soon as
its derived stalk is invertible at every point of the form `i' w` and at every complex.

This is `isIso_derivedBaseChangeMap_of_onImage` at every object, together with
`CategoryTheory.NatIso.isIso_of_isIso_app`. -/
theorem isIso_derivedBaseChangeSquare_of_onImage (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i]
    (hon : ∀ (w : Z')
        (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))),
      IsIso ((AlgebraicGeometry.derivedStalkFunctor (i' w)).map
        (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g.toLRSHom.toShHom
          i'.toLRSHom.toShHom i.toLRSHom.toShHom f.toLRSHom.toShHom
          (comp_toShHom_of_isPullback sq) K))) :
    IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare g.toLRSHom.toShHom
      i'.toLRSHom.toShHom i.toLRSHom.toShHom f.toLRSHom.toShHom
      (comp_toShHom_of_isPullback sq)) := by
  have : ∀ K, IsIso ((Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare
      g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom f.toLRSHom.toShHom
      (comp_toShHom_of_isPullback sq)).app K) :=
    fun K => isIso_derivedBaseChangeMap_of_onImage sq K fun w => hon w K
  exact NatIso.isIso_of_isIso_app _

/-- **Stacks 0E23 as an isomorphism of functors, reduced to the closed subscheme.**  From the
on-image clause, `Ri'_* ∘ Lg^*` and `Lf^* ∘ Ri_*` are isomorphic as functors
`D(𝒪_Z) ⟶ D(𝒪_{X'})`, by the canonical morphism of Stacks 08HY. -/
def derivedBaseChangeSquareIsoOfOnImage (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i]
    (hon : ∀ (w : Z')
        (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))),
      IsIso ((AlgebraicGeometry.derivedStalkFunctor (i' w)).map
        (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g.toLRSHom.toShHom
          i'.toLRSHom.toShHom i.toLRSHom.toShHom f.toLRSHom.toShHom
          (comp_toShHom_of_isPullback sq) K))) :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i.toLRSHom.toShHom ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          f.toLRSHom.toShHom ≅
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          i'.toLRSHom.toShHom :=
  haveI := isIso_derivedBaseChangeSquare_of_onImage sq hon
  asIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare g.toLRSHom.toShHom
    i'.toLRSHom.toShHom i.toLRSHom.toShHom f.toLRSHom.toShHom
    (comp_toShHom_of_isPullback sq))

/-! ### Stacks 0661 at the local rings of the square -/

/-- **The square of germ maps of local rings.**  At a point `w` of `Z'` the four germ maps of the
square form a commutative square of rings, the two presentations `i (g w)` and `f (i' w)` of the
image point being compared by `TopCat.Presheaf.stalkCongr`.

This is `Stacks.Cohomology.StalkPushout.stalkMap_comm_of_isPullback`, reassociated and read as an
equation of ring homomorphisms, which is the form Stacks 0661 asks for. -/
theorem stalkMap_ringHom_square (sq : IsPullback i' g f i) (w : Z')
    (hpt : i (g w) = f (i' w)) :
    (g.stalkMap w).hom.comp (i.stalkMap (g w)).hom =
      (i'.stalkMap w).hom.comp
        ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫ f.stalkMap (i' w)).hom := by
  have h := Stacks.Cohomology.StalkPushout.stalkMap_comm_of_isPullback sq w hpt
  rw [← Category.assoc] at h
  exact congrArg CommRingCat.Hom.hom h

/-- **Tor independence at the local rings of a point of `Z'`.**  If `Z` and `X'` are Tor
independent over `X`, then `𝒪_{Z, g w}` and `𝒪_{X', i' w}` are Tor independent over
`𝒪_{X, i (g w)}`, for the algebra structures the germ maps of `i` and of `f` induce.

This is
`AlgebraicGeometry.BaseChangeTorAmplitude.ringTorIndependent_of_schemeTorIndependent_stalks` with
the germ map of `f` rewritten from the `eqToHom` presentation of the transport to the
`TopCat.Presheaf.stalkCongr` presentation, which is the one
`Stacks.Cohomology.StalkPushout.isPushout_stalkMap_toAlgebra_of_isPullback` uses; the two are the
same morphism by `stalkCongr_hom_eq_eqToHom`, and so the two algebra structures are the same
instance. -/
theorem torIndependent_stalkMap_of_torIndependent
    (htor : AlgebraicGeometry.TorIndependent i f) (w : Z') (hpt : i (g w) = f (i' w)) :
    @TorIndependent (ToType (X.presheaf.stalk (i (g w)))) (ToType (Z.presheaf.stalk (g w)))
      (ToType (X'.presheaf.stalk (i' w))) _ _ _ (i.stalkMap (g w)).hom.toAlgebra
      ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫
        f.stalkMap (i' w)).hom.toAlgebra := by
  rw [stalkCongr_hom_eq_eqToHom hpt]
  exact AlgebraicGeometry.BaseChangeTorAmplitude.ringTorIndependent_of_schemeTorIndependent_stalks
    htor (g w) (i' w) hpt

/-- **Stacks 0661 at the local rings of a cartesian square with `i` a closed immersion.**  Let `w`
be a point of `Z'`.  If `Z` and `X'` are Tor independent over `X`, then the canonical comparison

`K ⊗ᴸ_{𝒪_{X, i (g w)}} 𝒪_{X', i' w} ⟶ K ⊗ᴸ_{𝒪_{Z, g w}} 𝒪_{Z', w}`

of Stacks 065Z is an isomorphism of functors on the unbounded derived category of
`𝒪_{Z, g w}`-modules, for every choice of models of the two total derived extension-of-scalars
functors.

The two hypotheses of Stacks 0661 are supplied geometrically:
`Stacks.Cohomology.StalkPushout.isPushout_stalkMap_toAlgebra_of_isPullback` says the four local
rings form a pushout square — this is where the closed immersion and cartesianness are used — and
`torIndependent_stalkMap_of_torIndependent` transports the Tor independence of the schemes to the
local rings.  The two scalar towers are the commutativity of the square of germ maps.

This is the ring-level input of Stacks 0E23 on the image of `i'`.  It is not Stacks 0E23: what it
does not say is that the derived stalk of the derived base change map of Stacks 08HY *is* this
comparison. -/
theorem isIso_derivedBaseChangeComparison_stalk (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f)
    (w : Z') (hpt : i (g w) = f (i' w))
    (L_g : DerivedCategory (ModuleCat.{u} (ToType (X.presheaf.stalk (i (g w))))) ⥤
      DerivedCategory (ModuleCat.{u} (ToType (X'.presheaf.stalk (i' w)))))
    (L_h : DerivedCategory (ModuleCat.{u} (ToType (Z.presheaf.stalk (g w)))) ⥤
      DerivedCategory (ModuleCat.{u} (ToType (Z'.presheaf.stalk w))))
    (alpha_g : DerivedCategory.Q ⋙ L_g ⟶
      (ModuleCat.extendScalars.{u, u, u}
        ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫
          f.stalkMap (i' w)).hom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (alpha_h : DerivedCategory.Q ⋙ L_h ⟶
      (ModuleCat.extendScalars.{u, u, u}
        (g.stalkMap w).hom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [L_g.IsLeftDerivedFunctor alpha_g
      (HomologicalComplex.quasiIso (ModuleCat.{u} (ToType (X.presheaf.stalk (i (g w)))))
        (ComplexShape.up ℤ))]
    [L_h.IsLeftDerivedFunctor alpha_h
      (HomologicalComplex.quasiIso (ModuleCat.{u} (ToType (Z.presheaf.stalk (g w))))
        (ComplexShape.up ℤ))] :
    IsIso (derivedBaseChangeComparison.{u, u, u, u, u} (i.stalkMap (g w)).hom
      ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫ f.stalkMap (i' w)).hom
      (g.stalkMap w).hom (i'.stalkMap w).hom (stalkMap_ringHom_square sq w hpt)
      L_g L_h alpha_g alpha_h).2.1 := by
  let algRA : Algebra (ToType (X.presheaf.stalk (i (g w)))) (ToType (Z.presheaf.stalk (g w))) :=
    (i.stalkMap (g w)).hom.toAlgebra
  let algRR' : Algebra (ToType (X.presheaf.stalk (i (g w))))
      (ToType (X'.presheaf.stalk (i' w))) :=
    ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫ f.stalkMap (i' w)).hom.toAlgebra
  let algRA' : Algebra (ToType (X.presheaf.stalk (i (g w)))) (ToType (Z'.presheaf.stalk w)) :=
    ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫ f.stalkMap (i' w) ≫
      i'.stalkMap w).hom.toAlgebra
  let algAA' : Algebra (ToType (Z.presheaf.stalk (g w))) (ToType (Z'.presheaf.stalk w)) :=
    (g.stalkMap w).hom.toAlgebra
  let algR'A' : Algebra (ToType (X'.presheaf.stalk (i' w))) (ToType (Z'.presheaf.stalk w)) :=
    (i'.stalkMap w).hom.toAlgebra
  have towerA : IsScalarTower (ToType (X.presheaf.stalk (i (g w))))
      (ToType (Z.presheaf.stalk (g w))) (ToType (Z'.presheaf.stalk w)) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        RingHom.algebraMap_toAlgebra]
      exact (stalkMap_ringHom_square sq w hpt).symm)
  have towerR' : IsScalarTower (ToType (X.presheaf.stalk (i (g w))))
      (ToType (X'.presheaf.stalk (i' w))) (ToType (Z'.presheaf.stalk w)) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Category.assoc])
  have hpush : Algebra.IsPushout (ToType (X.presheaf.stalk (i (g w))))
      (ToType (Z.presheaf.stalk (g w))) (ToType (X'.presheaf.stalk (i' w)))
      (ToType (Z'.presheaf.stalk w)) :=
    Stacks.Cohomology.StalkPushout.isPushout_stalkMap_toAlgebra_of_isPullback sq w hpt
  exact derivedBaseChangeComparison_isIso_of_torIndependent.{u, u, u, u, u}
    (torIndependent_stalkMap_of_torIndependent htor w hpt) L_g L_h alpha_g alpha_h

end Square

end Stacks.Cohomology.ClosedImmersionBaseChange

end

end
