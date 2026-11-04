module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCechQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleModuleInjectives
public import StacksFrontier.Homology.CompositeCollapse

/-!
# The higher direct images along `ε_a` computed by an acyclic resolution

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site and let
`ε_a : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` be the morphism of small étale ringed sites of
[Stacks, Tag 070R] (2).  Let `𝓜` be an `𝒪_{X_étale}`-module and let

`0 ⟶ 𝓜 ⟶ K ⁰ ⟶ K ¹ ⟶ ⋯`

be a resolution of `𝓜` — given as a quasi-isomorphism `ε : 𝓜[0] ⟶ K` onto a cochain complex of
`𝒪_{X_étale}`-modules — each of whose terms is *acyclic* for the direct image, meaning that
`R ᵠ (ε_a)_*(K ʲ) = 0` for every `q > 0`.  Then Leray's acyclicity lemma computes the higher
direct images of `𝓜` as the cohomology of the complex `(ε_a)_* K` of `𝒪_{Y_étale}`-modules:

`R ⁿ (ε_a)_*(𝓜) ≅ H ⁿ ((ε_a)_* K)`.

That is `AlgebraicGeometry.SmallEtale.rightDerivedPushforwardIsoHomologyOfAcyclic` below.  Fed
to the weak Serre closure of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleCechQuasicoherence.lean` it
gives quasi-coherence on the site, and the cartesian condition, of every higher direct image of
`𝓜`, in every degree, as soon as the modules `(ε_a)_*(K ʲ)` are quasi-coherent on the site.

## Why this is here

It is the homological half of the Čech route to the étale part of [Stacks, Tag 071N] above
degree zero, the route recorded in the module documentation of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleQcqsPushforward.lean`, and it
is what replaces the relative Leray spectral sequence of [Stacks, Tag 0734] that the source's
induction uses — unavailable here, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/HigherPushforwardQuasicoherent.lean`: that tag is formalized
for a ringed topos whose three universes agree, whereas the small étale site has its objects one
universe above its modules.  Leray's acyclicity lemma needs no spectral sequence, and
`Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic` carries it at exactly the generality used
here.

**What is still owed is the resolution itself.**  Nothing below constructs one: the complex `K`,
the quasi-isomorphism `ε`, the acyclicity of the terms and their quasi-coherence downstairs are
all hypotheses.  In the intended application `K` is the Čech complex of a finite cover of `X` by
objects `U ⟶ X` of `X_étale` for which `U ⟶ Y` is affine, the terms `(ε_a)_*(K ʲ)` are then
direct images along affine morphisms, and quasi-coherence of those is unconditional by
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pushforward`.

## Main results

* `AlgebraicGeometry.SmallEtale.rightDerivedPushforwardIsoHomologyOfAcyclic`: **the higher
  direct image along `ε_a` is the cohomology of the direct image of an acyclic resolution.**
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_rightDerived_pushforward_of_acyclic`:
  the higher direct images are quasi-coherent on the site when the direct images of the terms
  are.
* `AlgebraicGeometry.SmallEtale.isCartesianOnAffines_rightDerived_pushforward_of_acyclic`: the
  same conclusion in the cartesian form, which is what the degree-zero argument of
  `SmallEtaleQcqsPushforward.lean` consumes.
* `AlgebraicGeometry.SmallEtale.acyclic_pushforward_iff`: the acyclicity hypothesis spelled as
  the vanishing of the higher direct images of a single module, which is the shape a geometric
  vanishing statement is produced in.

## Implementation notes

No new homological algebra appears here.  The three hypotheses
`CategoryTheory.Functor.Additive`, `CategoryTheory.Limits.PreservesFiniteLimits` and
`CategoryTheory.EnoughInjectives` that `Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic`
asks of the functor and its source are all found by instance search: additivity from
`CategoryTheory.SheafOfModules.pushforward_additive`, left exactness because a direct image of
sheaves of modules along a continuous functor is restriction of sections and limits of sheaves
of modules are computed sectionwise, and enough injectives from
`AlgebraicGeometry.SmallEtale.enoughInjectives_smallEtaleModules`.

The priority raise on `CategoryTheory.SheafOfModules.instAbelian` is the one documented in
`AlgebraicGeometry.SmallEtale.enoughInjectives_smallEtaleModules`: with the
module-universe-`max u v r w` instances in the import closure, instance search for `Abelian` on
the modules at module universe `u` commits to them and then fails on the universe constraint.
It is `local`, so no global instance is declared.

**No `@[stacks 071N]` attribute is placed.**  This is one input to that tag's proof above
degree zero and not the tag; the resolution it consumes is not constructed here.

## References

* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- The direct image along `ε_a` of a cochain complex of `𝒪_{X_étale}`-modules, as a cochain
complex of `𝒪_{Y_étale}`-modules: the complex whose cohomology computes the higher direct
images of an object the complex resolves. -/
public abbrev pushforwardCochainComplex
    (K : CochainComplex (SheafOfModules.{u} (structureSheaf B X.obj X.property)) ℕ) :
    CochainComplex (SheafOfModules.{u} (structureSheaf B Y.obj Y.property)) ℕ :=
  ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K

/-- **Acyclicity for the direct image along `ε_a` is the vanishing of the higher direct
images.**  The `(ε_a)_*`-acyclic objects of `Stacks.RightDerivedComp.acyclic` are by definition
those whose higher direct images vanish; this restates the predicate in the shape a geometric
vanishing statement is produced in. -/
public theorem acyclic_pushforward_iff
    (𝓜 : SheafOfModules.{u} (structureSheaf B X.obj X.property)) :
    Stacks.RightDerivedComp.acyclic
        (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)) 𝓜 ↔
      ∀ q, 0 < q → IsZero (((SheafOfModules.pushforward.{u}
        (smallEtaleStructureMapRing B a)).rightDerived q).obj 𝓜) :=
  Iff.rfl

/-- **The higher direct image along `ε_a` is the cohomology of the direct image of an acyclic
resolution.**

Let `ε : 𝓜[0] ⟶ K` be a quasi-isomorphism onto a cochain complex of `𝒪_{X_étale}`-modules — a
resolution `0 ⟶ 𝓜 ⟶ K ⁰ ⟶ K ¹ ⟶ ⋯` — every term of which is acyclic for the direct image along
`ε_a`, meaning `R ᵠ (ε_a)_*(K ʲ) = 0` for `q > 0`.  Then

`R ⁿ (ε_a)_*(𝓜) ≅ H ⁿ ((ε_a)_* K)`

for every `n`.  No term of `K` is required to be injective.  This is Leray's acyclicity lemma
[Stacks, Tag 015E] at `ε_a`, by way of
`Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic`; the three homological hypotheses that
statement takes — additivity and left exactness of the direct image, and enough injectives on
`X_étale` — all hold unconditionally. -/
public def rightDerivedPushforwardIsoHomologyOfAcyclic
    {𝓜 : SheafOfModules.{u} (structureSheaf B X.obj X.property)}
    {K : CochainComplex (SheafOfModules.{u} (structureSheaf B X.obj X.property)) ℕ}
    (ε : (CochainComplex.single₀ (SheafOfModules.{u}
      (structureSheaf B X.obj X.property))).obj 𝓜 ⟶ K) [QuasiIso ε]
    (hK : ∀ q, Stacks.RightDerivedComp.acyclic
      (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)) (K.X q))
    (n : ℕ) :
    ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓜 ≅
      (pushforwardCochainComplex B a K).homology n :=
  Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic _ ε hK n

/-- **The higher direct images along `ε_a` of a module with an acyclic resolution whose direct
images are quasi-coherent on the site are quasi-coherent on the site, in every degree.**

This is `AlgebraicGeometry.SmallEtale.rightDerivedPushforwardIsoHomologyOfAcyclic` read through
the weak Serre closure `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_iso_homology`:
the higher direct image is the cohomology of a complex of quasi-coherent `𝒪`-modules on
`Y_étale`, and such cohomology is quasi-coherent on the site. -/
public theorem isQuasicoherentOnSite_rightDerived_pushforward_of_acyclic
    {𝓜 : SheafOfModules.{u} (structureSheaf B X.obj X.property)}
    {K : CochainComplex (SheafOfModules.{u} (structureSheaf B X.obj X.property)) ℕ}
    (ε : (CochainComplex.single₀ (SheafOfModules.{u}
      (structureSheaf B X.obj X.property))).obj 𝓜 ⟶ K) [QuasiIso ε]
    (hK : ∀ q, Stacks.RightDerivedComp.acyclic
      (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)) (K.X q))
    (hqc : ∀ q, ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
      (K.X q)).IsQuasicoherentOnSite)
    (n : ℕ) :
    (((SheafOfModules.pushforward.{u}
      (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓜).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_iso_homology B Y.obj Y.property (pushforwardCochainComplex B a K)
    hqc n (rightDerivedPushforwardIsoHomologyOfAcyclic B a ε hK n)

/-- **The higher direct images along `ε_a` of a module with an acyclic resolution whose direct
images are quasi-coherent on the site are cartesian on the affine objects, in every degree.**
The cartesian form of
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_rightDerived_pushforward_of_acyclic`, which
is the shape the degree-zero argument of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleQcqsPushforward.lean`
consumes. -/
public theorem isCartesianOnAffines_rightDerived_pushforward_of_acyclic
    {𝓜 : SheafOfModules.{u} (structureSheaf B X.obj X.property)}
    {K : CochainComplex (SheafOfModules.{u} (structureSheaf B X.obj X.property)) ℕ}
    (ε : (CochainComplex.single₀ (SheafOfModules.{u}
      (structureSheaf B X.obj X.property))).obj 𝓜 ⟶ K) [QuasiIso ε]
    (hK : ∀ q, Stacks.RightDerivedComp.acyclic
      (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)) (K.X q))
    (hqc : ∀ q, ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
      (K.X q)).IsQuasicoherentOnSite)
    (n : ℕ) :
    IsCartesianOnAffines B Y.obj Y.property
      (((SheafOfModules.pushforward.{u}
        (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓜) :=
  isCartesianOnAffines_of_iso_homology B Y.obj Y.property (pushforwardCochainComplex B a K)
    hqc n (rightDerivedPushforwardIsoHomologyOfAcyclic B a ε hK n)

end AlgebraicGeometry.SmallEtale

end
