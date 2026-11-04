module

public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocus.Reduction
public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocus.Chart

/-!
# Representability of the descent locus of a vector bundle

Let `f : X ⟶ S` be a flat, proper morphism of finite presentation such that `𝒪_T ⟶ p_*𝒪_{X_T}`
is an isomorphism for every base change `p : X_T ⟶ T`, and let `E` be a finite locally free
`𝒪_X`-module. [Stacks, Tag 0BDP] says that there is an immersion of finite presentation
`Z ⟶ S` through which a morphism `g : T ⟶ S` factors exactly when the pullback of `E` to `X_T`
is the pullback of a finite locally free `𝒪_T`-module. This is
`AlgebraicGeometry.hasDescentLocus_of_flat_of_isProper`, stated with the representability
predicate `AlgebraicGeometry.HasDescentLocus` of
`StacksFrontier/AlgebraicGeometry/Morphisms/DescentLocus0BDP.lean`.

## Proof

Over each affine open of `S` the problem is a base change of a Noetherian one
(`AlgebraicGeometry.DescentLocus.nonempty_noetherianStage`); at each prime of the Noetherian base a
minimal finite free model of the degree zero cohomology cuts out a closed stratum on which the
cohomology is free with a universal basis, and inside it the locus where that basis trivialises the
bundle is open (`AlgebraicGeometry.DescentLocus.hasChart`). The local loci are glued over the open
set of points whose fibre cohomology does not exceed the rank of the bundle
(`AlgebraicGeometry.DescentLocus.hasDescentLocus_of_hasChart`).

## References

* [Stacks Project, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- **Stacks Tag 0BDP.** Let `f : X ⟶ S` be a flat, proper morphism of finite presentation and
`E` a finite locally free `𝒪_X`-module. Assume that `𝒪_T ⟶ p_*𝒪_{X_T}` is an isomorphism for
every `g : T ⟶ S`, where `p : X_T = X ×_S T ⟶ T`. Then there is an immersion of finite
presentation `j : Z ⟶ S` such that `g : T ⟶ S` factors through `Z` if and only if there is a
finite locally free `𝒪_T`-module `N` with `p^*N ≅ q^*E`, `q : X_T ⟶ X` the projection. -/
@[stacks 0BDP]
theorem hasDescentLocus_of_flat_of_isProper {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [IsProper f]
    (hfp : FinitePresentation f)
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd f g).toLRSHom.toShHom))
    (E : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    HasDescentLocus f E := by
  have := hfp.locallyOfFinitePresentation
  let E' : X.Modules := E
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E' := hE
  exact DescentLocus.hasDescentLocus_of_hasChart f hO E'
    fun hV St p ↦ DescentLocus.hasChart f hO E' hV St p

end AlgebraicGeometry
