module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.OpenImmersionPullback
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.ShortComplexOfDirectImages

/-!
# The derived pullback along an open immersion is restriction

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces whose pullback `f^*` of sheaves of
modules is exact — an open immersion, for instance, which is flat.  Then nothing is derived:
the left derived pullback `Lf^*` of Tag 079W, built from K-flat resolutions, is the functor
`f^*` induces degreewise on unbounded derived categories.

Specialized to the canonical inclusion `j_U : (U, 𝒪_X|_U) ⟶ (X, 𝒪_X)` of an open subspace,
this identifies `Lj_U^*` with `D(j_U^*)`, the derived restriction to `U` in which the
Mayer--Vietoris Ext sequence of Stacks 08BW is stated.

## Main results

* `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory`: for a morphism
  of ringed spaces with exact pullback, `Lf^* ≅ D(f^*)`.
* `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso`: the same for an
  arbitrary open immersion of ringed spaces, with no hypothesis left over.
* `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackModuleRestrictionIso`: `Lj_U^*` is
  ordinary restriction to the open subspace `U`.
* `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso`: the same in the
  spelling `Stacks.ExtensionByZero.derivedRestriction (structureSheafRing X) U` of the
  Mayer--Vietoris material.
* `Stacks.Cohomology.DerivedOpenImmersion.modulePullbackJStarIso`: the underived comparison
  that both rest on, in that same spelling.

## Implementation notes

The mathematical content is entirely in the two inputs: exactness of `f^*`, and the underived
comparison of pullback along `j_U` with restriction.  The passage to derived categories is
`Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso` — for an exact functor the comparison
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` is invertible, so the degreewise functor is
itself a left derived functor, and left derived functors are unique up to a unique isomorphism.
No new adjunction is needed, and the isomorphism is one of functors, hence natural in the
complex.

Everything is stated at `HasDerivedCategory.standard`, which is the model the consumers of the
derived pullback use (`AlgebraicGeometry.Perfect.RelativeDescentDerivedHom` and
`Stacks.DerivedPullback.Composition`); the composition and associativity coherences of Tag 0D5S
are baked at that model and take no universe binder, so they cannot be read at another one.

Two spellings of the structure sheaf of an open subspace meet here:
`structureSheafRing (X.restrict U.isOpenEmbedding)`, which the pullback functor and hence Tag
079W use, and `ExtensionByZeroModules.resRing U (structureSheafRing X)`, which restriction uses.
They are definitionally equal, both semireducible, and so a goal mixing
them is not type-correct at `instances` transparency: the two routes to the `Preadditive`
instance of the category of modules on `U` differ, and the `Functor.Additive` instance found
for one is not the one declared against the other.  Both crossings are therefore paid in a
term-mode `exact`, where the conversion check runs at default transparency — once in
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackModuleRestrictionIso`, whose three
exactness arguments are written out rather than synthesized, and once in
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso`, whose type
ascription forces the `resRing` spelling on the target.  This is the pattern of
`Stacks.Cohomology.RestrictionTensor.restrictMapComplexIso`.  Downstream only honest
isomorphisms are composed.

Naturality in the complex is automatic: every statement is an isomorphism of functors.
Naturality in the open subspace IS recorded, in the module
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestrictionNaturality`:
`derivedPullbackIsoMapDerivedCategory_comp` (line 402), `derivedPullbackOpenImmersionIso_comp`
(line 466) and `derivedPullbackOpenImmersionIso_ofRestrict_comp` (line 491).  The composition
coherence of Tag 0D5S it rests on is
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical` of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/CompositionUnconditional.lean` (line
171), with the tag itself registered at line 151 of that file.

## References

* [Stacks Project, Lemma 20.28.6 (Tag 079W)](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Lemma 20.28.2 (Tag 06YJ)](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Section 17.6 (Tag 00AB)](https://stacks.math.columbia.edu/tag/00AB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction ExtensionByZeroModules
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.HigherDirectImage

namespace Stacks.Cohomology.DerivedOpenImmersion

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### Exact pullback is its own left derived functor -/

/-- **The left derived pullback along a morphism of ringed spaces with exact pullback is the
degreewise pullback.**  `Lf^* ≅ D(f^*)` on unbounded derived categories of sheaves of modules.

The two exactness hypotheses are what makes `f^*` induce a functor on derived categories at
all; an open immersion satisfies them, by
`Stacks.Cohomology.openImmersionModulePullback_preservesHomology`. -/
def derivedPullbackIsoMapDerivedCategory {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    [PreservesFiniteLimits (modulePullback f)] [PreservesFiniteColimits (modulePullback f)] :
    derivedPullback f ≅ (modulePullback f).mapDerivedCategory :=
  Stacks.Homology.leftDerivedIsoMapDerivedCategory (modulePullback f)
    (derivedPullback f) (derivedPullbackComparison f)

/-! ### Pullback along an open immersion -/

section OpenImmersion

variable {X Y : RingedSpace.{u, u}} (i : X ⟶ Y) [SheafedSpace.IsOpenImmersion i]

/-- Pullback along an open immersion of ringed spaces preserves homology, being the concrete
restriction to the image up to an equivalence.  This is
`Stacks.Cohomology.openImmersionModulePullback_preservesHomology`, seated as an
instance so that the functor it induces on derived categories can be written down. -/
instance modulePullbackOpenImmersion_preservesHomology :
    (modulePullback i).PreservesHomology :=
  Stacks.Cohomology.openImmersionModulePullback_preservesHomology i

/-- Pullback along an open immersion of ringed spaces is right exact. -/
instance modulePullbackOpenImmersion_preservesFiniteColimits :
    PreservesFiniteColimits (modulePullback i) :=
  (modulePullback i).preservesFiniteColimits_of_preservesHomology

/-- **The left derived pullback along an open immersion of ringed spaces is the degreewise
pullback.**  An open immersion is flat, so `i^*` is exact (Stacks 01E5 transported to the
abstract pullback) and no derivation happens. -/
def derivedPullbackOpenImmersionIso :
    derivedPullback i ≅ (modulePullback i).mapDerivedCategory :=
  derivedPullbackIsoMapDerivedCategory i

end OpenImmersion

/-! ### Restriction to an open subspace -/

section Open

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)

/-- **Pullback along the canonical inclusion of an open subspace is restriction of modules.**
Both are left adjoints of pushforward along the inclusion.  This is
`Stacks.Cohomology.RelativeMayerVietoris.modulePullbackOpenInclusionIso` in the
extension-by-zero spelling `ExtensionByZeroModules.jStar` of restriction. -/
def modulePullbackJStarIso :
    modulePullback (X.ofRestrict U.isOpenEmbedding) ≅ jStar U (structureSheafRing X) :=
  (Stacks.Cohomology.RelativeMayerVietoris.modulePullbackOpenInclusionIso X U).symm

-- Restriction `j^*` to an open subspace is exact: it is a right adjoint of extension by zero
-- and a left adjoint of pushforward.  Both facts are proved once, at a variable sheaf of rings,
-- as `ExtensionByZeroModules.preservesFinite{Limits,Colimits}_jStar`; they are switched on here
-- rather than restated, so this file declares no instance of its own.  (The same two facts are
-- also available as the global instances `ExtensionByZeroModules.jStar_preservesFinite{Limits,
-- Colimits}`, at a different `PreservesLimitsOfSize` universe; naming the lemmas here pins the
-- size this file's elaboration needs.)
attribute [local instance] preservesFiniteLimits_jStar preservesFiniteColimits_jStar

/-- **The left derived pullback along the inclusion of an open subspace is ordinary
restriction.**  `Lj_U^* ≅ D((-)|_U)`, naturally in the complex.

Restriction is exact, so it is its own left derived functor, and it is pullback along `j_U`
by `Stacks.Cohomology.RelativeMayerVietoris.modulePullbackOpenInclusionIso`. -/
def derivedPullbackModuleRestrictionIso :
    derivedPullback (X.ofRestrict U.isOpenEmbedding) ≅
      (moduleRestriction X U).mapDerivedCategory := by
  have hadd : (moduleRestriction X U).Additive := inferInstance
  have hlim : PreservesFiniteLimits (moduleRestriction X U) := inferInstance
  have hcolim : PreservesFiniteColimits (moduleRestriction X U) := inferInstance
  exact @Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso _ _ _ _ _ _ _ _
    (modulePullback (X.ofRestrict U.isOpenEmbedding)) (moduleRestriction X U)
    inferInstance hadd hlim hcolim
    (derivedPullback (X.ofRestrict U.isOpenEmbedding))
    (derivedPullbackComparison (X.ofRestrict U.isOpenEmbedding)) inferInstance
    (Stacks.Cohomology.RelativeMayerVietoris.modulePullbackOpenInclusionIso X U).symm

/-- **The left derived pullback along the inclusion of an open subspace is derived
restriction.**  `Lj_U^* ≅ D(j_U^*)`, naturally in the complex: the right-hand side is
`Stacks.ExtensionByZero.derivedRestriction (structureSheafRing X) U`, the functor the
Mayer--Vietoris Ext sequence of Stacks 08BW is stated in.

This is `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackModuleRestrictionIso` with the
`ExtensionByZeroModules.resRing` spelling of the structure sheaf of `U` forced on the target
by the type ascription, which is where the two spellings are crossed. -/
def derivedPullbackOpenRestrictionIso :
    (derivedPullback (X.ofRestrict U.isOpenEmbedding) :
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
        DerivedCategory (SheafOfModules.{u} (resRing U (structureSheafRing X)))) ≅
      (jStar U (structureSheafRing X)).mapDerivedCategory := by
  exact derivedPullbackModuleRestrictionIso X U

end Open

end Stacks.Cohomology.DerivedOpenImmersion

end

