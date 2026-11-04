module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentIso

/-!
# Restriction to an open subspace on derived categories of `𝒪`-modules

Restriction of `𝒪_X`-modules to an open subspace `U` of a ringed space `X`,
`AlgebraicGeometry.RingedSpace.restrictModules`, is an exact functor: it is additive, it
preserves finite limits and it preserves finite colimits. It therefore induces a triangulated
functor `D(𝒪_X) ⥤ D(𝒪_{X|U})`, and this file gives that functor a name,
`AlgebraicGeometry.RingedSpace.derivedRestrictModules`, together with the properties its
consumers need: it commutes with the shift, it is triangulated, it carries distinguished
triangles to distinguished triangles, and it is computed termwise on an object in the image of
the localization functor `DerivedCategory.Q`.

The reason for the name is the same as for
`AlgebraicGeometry.RingedSpace.derivedPushforwardOXMod`: statements in the derived category of
an open subspace are expensive to elaborate and the development must not end up with several
spellings of this one functor. Here the three exactness facts are global instances with no
hypotheses, so there is exactly one functor to speak of, and
`derivedRestrictModules` is its canonical name; consumers should use it rather than writing
`(restrictModules X U).mapDerivedCategory`.

## Main definitions

* `AlgebraicGeometry.RingedSpace.derivedRestrictModules` is `(·)|_U : D(𝒪_X) ⥤ D(𝒪_{X|U})`.
* `AlgebraicGeometry.RingedSpace.derivedRestrictModulesFactors` says it is computed by applying
  `restrictModules` in each degree.
* `AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso` is that identification at a
  single complex, written with `AlgebraicGeometry.RingedSpace.restrictComplex`.

## Main results

* `AlgebraicGeometry.RingedSpace.exactFunctor_restrictModules`: restriction to an open subspace
  is exact, as a single named fact.
* `AlgebraicGeometry.RingedSpace.isRightDerivedFunctor_derivedRestrictModules`: the induced
  functor is a right derived functor of restriction, so writing it `R(·)|_U` is justified.
* `AlgebraicGeometry.RingedSpace.map_distinguished_derivedRestrictModules`: it carries
  distinguished triangles to distinguished triangles.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_derivedRestrict` is Stacks
  08CC part (1) phrased through `derivedRestrictModules`: an object of `D(𝒪_X)` which has a
  strictly perfect approximation in degrees above `m` on a neighbourhood of every point, *the
  approximation being a morphism into the derived restriction of the object itself*, is
  `m`-pseudo-coherent.

## Implementation notes

Exactness is not reproved here. Additivity is
`AlgebraicGeometry.RingedSpace.restrictModules_additive` and the two halves of exactness are
`AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteLimits` and
`AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteColimits`, all three already
available: restriction is restriction to the slice `Over U` of the site of opens followed by
Mathlib's equivalence `TopologicalSpace.Opens.sheafOfModulesEquivOver`, the slice restriction
preserves finite limits and has a left adjoint, and an equivalence preserves everything. What
this file adds is the derived functor and its interface.

`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_derivedRestrict` is the shape in
which an argument living in the derived category consumes Stacks 08CC part (1): the existing form
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_derived_approximation` asks for
approximations of `DerivedCategory.Q.obj (restrictComplex K U)` for an explicitly chosen complex
representative `K` of the object, whereas an argument by induction on a distinguished triangle
produces approximations of `(derivedRestrictModules X U).obj E` and has no representative in
hand. The representative is supplied here by essential surjectivity of `DerivedCategory.Q` and
the approximation is transported along `derivedRestrictModulesObjQIso`.

Every binder is written at the `StrictlyPerfect.OXMod` spelling of the category of
`𝒪`-modules, so that all instance synthesis happens in this file; see the implementation notes
of `StacksFrontier/AlgebraicGeometry/PseudoCoherent/PushforwardOXMod.lean` for why that matters.

The derived category of `X` and the derived categories of its open subspaces are hypotheses
with independent universes, as everywhere in this development.

## References

* [Stacks Project, Lemma 20.46.9 (Tag 08CC)](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Definition 20.46.4 (Tag 08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace StrictlyPerfect

universe d d' u

namespace AlgebraicGeometry.RingedSpace

/-! ### Exactness as a single named fact -/

/-- **Restriction of `𝒪`-modules to an open subspace is exact.** Both halves are already
instances — `AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteLimits` and
`AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteColimits` — and this bundles them,
so that a consumer can cite exactness of restriction by one name. Together with
`AlgebraicGeometry.RingedSpace.restrictModules_additive` it is what makes
`AlgebraicGeometry.RingedSpace.derivedRestrictModules` exist. -/
public theorem exactFunctor_restrictModules (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    exactFunctor (OXMod.{u, u} X) (OXMod.{u, u} (X.restrict U.isOpenEmbedding))
      (restrictModules X U) :=
  ⟨restrictModules_preservesFiniteLimits X U, restrictModules_preservesFiniteColimits X U⟩

/-! ### The derived restriction functor -/

section Functor

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)
  [HasDerivedCategory.{d} (OXMod.{u, u} X)]
  [HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]

/-- **Restriction to an open subspace on derived categories**, `(·)|_U : D(𝒪_X) ⥤ D(𝒪_{X|U})`.

Restriction of `𝒪_X`-modules to `U` is exact
(`AlgebraicGeometry.RingedSpace.exactFunctor_restrictModules`), so it induces a functor on
unbounded derived categories with no resolution at all.

This is the canonical name for that functor. The three exactness facts it is built from are
global instances with no hypotheses, so there is no freedom in the construction and no reason
for a consumer to rebuild `CategoryTheory.Functor.mapDerivedCategory` with its own `haveI`;
doing so would produce a term that is not *provably* equal to this one, because
`CategoryTheory.Limits.PreservesFiniteColimits` is data rather than a proposition. -/
public def derivedRestrictModules :
    DerivedCategory (OXMod.{u, u} X) ⥤
      DerivedCategory (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) :=
  (restrictModules X U).mapDerivedCategory

/-- `(·)|_U` commutes with the shift on derived categories. -/
public instance commShift_derivedRestrictModules : (derivedRestrictModules X U).CommShift ℤ :=
  inferInstanceAs ((restrictModules X U).mapDerivedCategory.CommShift ℤ)

/-- `(·)|_U` is a triangulated functor. -/
public instance isTriangulated_derivedRestrictModules :
    (derivedRestrictModules X U).IsTriangulated :=
  -- The module universe of `restrictModules` is not determined by its explicit arguments, and
  -- the argument of `inferInstanceAs` is elaborated on its own, so it is written out here.
  inferInstanceAs ((restrictModules.{u, u} X U).mapDerivedCategory.IsTriangulated)

/-- `(·)|_U` on derived categories is a right derived functor of restriction passed to homotopy
categories, with unit `CategoryTheory.Functor.mapDerivedCategoryFactorsh.inv`. This is what
justifies calling it `R(·)|_U`; since restriction is exact, no resolution intervenes. -/
public theorem isRightDerivedFunctor_derivedRestrictModules :
    (derivedRestrictModules X U).IsRightDerivedFunctor
      (restrictModules X U).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (OXMod.{u, u} X) (ComplexShape.up ℤ)) :=
  Stacks.ClosedImmersion.isRightDerivedFunctor_mapDerivedCategory (restrictModules X U)

/-- `(·)|_U` carries a distinguished triangle of `D(𝒪_X)` to a distinguished triangle of
`D(𝒪_{X|U})`.

This is what an induction over a distinguished triangle needs in order to localize: a
distinguished triangle on `X` restricts to a distinguished triangle on `U`, to which the local
criteria of Stacks 08CC and 08CD apply. -/
public theorem map_distinguished_derivedRestrictModules
    (T : Triangle (DerivedCategory (OXMod.{u, u} X)))
    (hT : T ∈ distTriang (DerivedCategory (OXMod.{u, u} X))) :
    (derivedRestrictModules X U).mapTriangle.obj T ∈
      distTriang (DerivedCategory (OXMod.{u, u} (X.restrict U.isOpenEmbedding))) :=
  (derivedRestrictModules X U).map_distinguished T hT

/-- The derived restriction of a complex of `𝒪_X`-modules is the restricted complex: on an
object in the image of the localization functor `DerivedCategory.Q`, `(·)|_U` is computed
degreewise by `AlgebraicGeometry.RingedSpace.restrictModules`.

This is `CategoryTheory.Functor.mapDerivedCategoryFactors`, and it is what connects the derived
statement of pseudo-coherence to the complex-level one. -/
public def derivedRestrictModulesFactors :
    DerivedCategory.Q ⋙ derivedRestrictModules X U ≅
      (restrictModules X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (restrictModules X U).mapDerivedCategoryFactors

/-- `AlgebraicGeometry.RingedSpace.derivedRestrictModulesFactors` at a single complex, with the
restricted complex written as `AlgebraicGeometry.RingedSpace.restrictComplex`.

That spelling is the one `AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplexFrom` and
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_derived_approximation` use, and it
is not syntactically the one `derivedRestrictModulesFactors` produces, so the identification is
given its own name. -/
public def derivedRestrictModulesObjQIso (K : CochainComplex (OXMod.{u, u} X) ℤ) :
    (derivedRestrictModules X U).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (restrictComplex K U) :=
  (derivedRestrictModulesFactors X U).app K

end Functor

/-! ### Stacks 08CC part (1) through the derived restriction functor -/

variable {X : RingedSpace.{u, u}}

/-- **Stacks 08CC part (1), phrased through the derived restriction functor.** Let `E` be an
object of the derived category of `𝒪_X`-modules and suppose that every point of `X` has an open
neighbourhood `U` on which some strictly perfect complex `𝒫` maps to `E|_U` by a morphism of
`D(𝒪_{X|U})` which is an isomorphism on cohomology above `m` and an epimorphism in degree `m`.
Then `E` is `m`-pseudo-coherent.

This is `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_derived_approximation` with
the complex representative of `E` supplied by essential surjectivity of `DerivedCategory.Q`:
the given approximation of `(derivedRestrictModules X U).obj E` is transported to one of
`DerivedCategory.Q.obj (restrictComplex K U)` along
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso` and the comparison isomorphism
`DerivedCategory.Q.obj K ≅ E`. Composing with isomorphisms changes neither the isomorphisms nor
the epimorphism on cohomology.

It is the form an argument internal to the derived category can use: such an argument restricts
*objects* and has no complex representative to name. -/
public theorem isPseudoCoherentFrom_of_local_derivedRestrict
    [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    [∀ U : Opens X.carrier,
      HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]
    (E : DerivedCategory (OXMod.{u, u} X)) (m : ℤ)
    (h : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P ∧
        ∃ α : DerivedCategory.Q.obj P ⟶ (derivedRestrictModules X U).obj E,
          (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map α)) ∧
          Epi ((DerivedCategory.homologyFunctor _ m).map α)) :
    IsPseudoCoherentFrom E m := by
  refine isPseudoCoherentFrom_of_local_derived_approximation E m (DerivedCategory.Q.objPreimage E)
    (Functor.objObjPreimageIso DerivedCategory.Q E) fun x => ?_
  obtain ⟨U, hx, P, hP, α, hα, hα₀⟩ := h x
  refine ⟨U, hx, P, hP, α ≫ (derivedRestrictModules X U).map
      (Functor.objObjPreimageIso DerivedCategory.Q E).inv ≫
    (derivedRestrictModulesObjQIso X U (DerivedCategory.Q.objPreimage E)).hom,
    fun j hj => ?_, ?_⟩
  · have := hα j hj
    rw [CategoryTheory.Functor.map_comp]
    infer_instance
  · have := hα₀
    rw [CategoryTheory.Functor.map_comp]
    exact epi_comp _ _

end AlgebraicGeometry.RingedSpace

end
