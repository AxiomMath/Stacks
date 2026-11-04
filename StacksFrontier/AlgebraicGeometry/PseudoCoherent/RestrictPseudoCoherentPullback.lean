module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction

/-!
# Pseudo-coherence and the derived pullback along the inclusion of an open subspace

Restriction of `𝒪_X`-modules to an open subspace of a ringed space appears in this development
under two names: `AlgebraicGeometry.RingedSpace.restrictModules`, the pushforward along the
functor `U.isOpenEmbedding.functor` on opens, in which pseudo-coherence is phrased, and
`Stacks.Cohomology.HigherDirectImage.moduleRestriction`, in which the derived pullback of
Tag 079W is phrased. This file identifies the two functors they induce on derived categories and
transports `m`-pseudo-coherence and pseudo-coherence across that identification, so that the two
preservation statements become available in the `derivedPullback` spelling.

## Main definitions

* `AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoDerivedPullback`: the identification
  `(·)|_W ≅ Lj_W^*` of derived restriction to an open subspace with the derived pullback along
  its inclusion.
* `AlgebraicGeometry.Scheme.Modules.derivedRestrictModulesIsoDerivedPullback`: the same for an
  open subscheme, in the spelling `derivedPullback W.ι.toLRSHom.toShHom`.

## Main results

* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedPullback` and
  `AlgebraicGeometry.RingedSpace.isPseudoCoherent_derivedPullback`: the derived pullback along
  the inclusion of an open subspace preserves `m`-pseudo-coherence and pseudo-coherence.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_derivedPullback` and
  `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_derivedPullback`: the same for an open
  subscheme `W` of a scheme, at the open immersion `W.ι`.

## Implementation notes

Both halves of the crossing are definitional identifications, not merely equivalences.
`Stacks.StrictlyPerfect.structureSheafOfRings X` and
`structureSheafRing X` are two constructions of the structure sheaf of `X`
with commutativity forgotten, and they are equal by definition, as are the two spellings of the
structure sheaf of an open subspace; `AlgebraicGeometry.RingedSpace.restrictModules X W` and
`Stacks.Cohomology.HigherDirectImage.moduleRestriction X W` are then one and the same
`CategoryTheory.SheafOfModules.pushforward` along `W.isOpenEmbedding.functor` with identity
change of rings, and the functors they induce on derived categories agree on the nose as well.
The identification is therefore `Stacks.Cohomology.DerivedOpenImmersion`'s comparison of the
derived pullback with `moduleRestriction`, read at the other spelling; nothing is transported
along an equivalence of categories.

Because the two spellings are definitionally but not reducibly equal, the crossings are paid
where a conversion check runs at default transparency: in the statement of the identification,
whose left-hand side fixes the `structureSheafOfRings` spelling, and in the term-mode
applications of `AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom.of_iso`. Instance synthesis
does not cross between the spellings, so each pseudo-coherence statement is proved in the
`restrictModules` spelling first and crossed once, at the end.

The unbounded predicate asks for a *single* complex that is `m`-pseudo-coherent for every `m`,
so it is not the conjunction over `m` of the bounded one; the complex produced by
`AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_restrictComplex` is independent of
`m`, which is what makes the unbounded statement available.

Everything is stated at `CategoryTheory.HasDerivedCategory.standard`, the model in which the
derived pullback and its coherences are built.

## References

* [Stacks Project, Definition 36.60.1 (Tag 08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Lemma 20.28.6 (Tag 079W)](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Lemma 36.60.9 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [Stacks Project, Lemma 35.9.1 (Tag 0DI7)](https://stacks.math.columbia.edu/tag/0DI7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open scoped AlgebraicGeometry

universe d u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-! ### The two vocabularies of derived restriction to an open subspace -/

/-- **Derived restriction to an open subspace is the derived pullback along its inclusion.**
`(·)|_W ≅ Lj_W^*` as functors `D(𝒪_X) ⥤ D(𝒪_{X|W})`, for `W` an open of a ringed space `X`. -/
public def derivedRestrictModulesIsoDerivedPullback (X : RingedSpace.{u, u})
    (W : Opens X.carrier) :
    derivedRestrictModules X W ≅ derivedPullback (X.ofRestrict W.isOpenEmbedding) :=
  (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackModuleRestrictionIso X W).symm

/-! ### Pseudo-coherence under the derived pullback along an open inclusion -/

/-- **The derived pullback of an `m`-pseudo-coherent object along the inclusion of an open
subspace is `m`-pseudo-coherent.** -/
public theorem isPseudoCoherentFrom_derivedPullback (X : RingedSpace.{u, u})
    (W : Opens X.carrier) (E : DerivedCategory (OXMod.{u, u} X)) (m : ℤ)
    (hE : IsPseudoCoherentFrom (X := X) E m) :
    IsPseudoCoherentFrom (X := X.restrict W.isOpenEmbedding)
      ((derivedPullback (X.ofRestrict W.isOpenEmbedding)).obj E) m :=
  IsPseudoCoherentFrom.of_iso (X := X.restrict W.isOpenEmbedding)
    (isPseudoCoherentFrom_derivedRestrictModules E m hE W)
    ((derivedRestrictModulesIsoDerivedPullback X W).app E)

/-- **The derived pullback of a pseudo-coherent object along the inclusion of an open subspace is
pseudo-coherent.** The restriction of a complex representing the object is `m`-pseudo-coherent
for every `m` at once, which is what the unbounded predicate asks for. -/
public theorem isPseudoCoherent_derivedPullback (X : RingedSpace.{u, u}) (W : Opens X.carrier)
    (E : DerivedCategory (OXMod.{u, u} X)) (hE : IsPseudoCoherent (X := X) E) :
    IsPseudoCoherent (X := X.restrict W.isOpenEmbedding)
      ((derivedPullback (X.ofRestrict W.isOpenEmbedding)).obj E) := by
  have h : IsPseudoCoherent (X := X.restrict W.isOpenEmbedding)
      ((derivedRestrictModules X W).obj E) := by
    obtain ⟨K, hK, ⟨e⟩⟩ := hE
    exact ⟨restrictComplex K W,
      fun m => isPseudoCoherentComplexFrom_restrictComplex K m (hK m) W,
      ⟨(derivedRestrictModulesObjQIso X W K).symm ≪≫ (derivedRestrictModules X W).mapIso e⟩⟩
  exact IsPseudoCoherent.of_iso (X := X.restrict W.isOpenEmbedding) h
    ((derivedRestrictModulesIsoDerivedPullback X W).app E)

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme.Modules

/-! ### The same at an open subscheme -/

/-- **Derived restriction to an open subscheme is the derived pullback along `W.ι`.**
`(·)|_W ≅ L(W.ι)^*` as functors `D(𝒪_X) ⥤ D(𝒪_W)`, for `W` an open of a scheme `X`. -/
public def derivedRestrictModulesIsoDerivedPullback (X : Scheme.{u}) (W : X.Opens) :
    RingedSpace.derivedRestrictModules X.toRingedSpace W ≅
      derivedPullback W.ι.toLRSHom.toShHom :=
  RingedSpace.derivedRestrictModulesIsoDerivedPullback X.toRingedSpace W

/-- **The derived pullback of an `m`-pseudo-coherent object along the inclusion of an open
subscheme is `m`-pseudo-coherent.** -/
public theorem isPseudoCoherentFrom_derivedPullback (X : Scheme.{u}) (W : X.Opens)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (m : ℤ)
    (hE : RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E m) :
    RingedSpace.IsPseudoCoherentFrom (X := W.toScheme.toRingedSpace)
      ((derivedPullback W.ι.toLRSHom.toShHom).obj E) m :=
  RingedSpace.isPseudoCoherentFrom_derivedPullback X.toRingedSpace W E m hE

/-- **The derived pullback of a pseudo-coherent object along the inclusion of an open subscheme
is pseudo-coherent.** -/
public theorem isPseudoCoherent_derivedPullback (X : Scheme.{u}) (W : X.Opens)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) :
    RingedSpace.IsPseudoCoherent (X := W.toScheme.toRingedSpace)
      ((derivedPullback W.ι.toLRSHom.toShHom).obj E) :=
  RingedSpace.isPseudoCoherent_derivedPullback X.toRingedSpace W E hE

end AlgebraicGeometry.Scheme.Modules

end
