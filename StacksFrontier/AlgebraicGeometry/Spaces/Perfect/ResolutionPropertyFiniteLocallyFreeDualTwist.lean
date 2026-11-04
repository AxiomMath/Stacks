module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffinePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyFiniteLocallyFree

/-!
# Stacks 0GUV with only the dual twist assumed

Let `f : X ⟶ Y` be a surjective finite locally free morphism of algebraic spaces over a
scheme `S`.  If `X` has the resolution property, so does `Y`: a finite type quasi-coherent
`𝒪_Y`-module `𝒢` pulls back to a finite type quasi-coherent module on `X`, the resolution
property of `X` gives an epimorphism `p : ℰ ⟶ f^*𝒢` from a finite locally free module, and
`f_*p` is again an epimorphism with finite locally free source, to which the projection formula
and the dual twist by `(f_*𝒪_X)^∨` apply.

## Main results

* `AlgebraicGeometry.Space.hasResolutionProperty_of_isSurjective_isFiniteLocallyFree_of_dualTwist`
  is **Stacks 0GUV** assuming only `AlgebraicGeometry.Space.DirectImageDualDescent`.  It carries
  the `@[stacks 0GUV]` registration.

## Implementation notes

Every step of the source's proof other than its last two is discharged here.

* The finite local freeness of `f_*ℰ` is
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_modulePushforward_of_isFiniteLocallyFree`,
  whose hypothesis is the statement's own finite local freeness of `f`.
* The finite type half of Stacks 03DO for `f^*` is unconditional,
  `AlgebraicGeometry.Space.isFiniteTypeOnSite_modulePullback`.
* The quasi-coherent half, Stacks 03DO(6), is unconditional too: it is **Stacks 03GA**,
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`,
  proved for an arbitrary morphism of algebraic spaces and an arbitrary quasi-coherent module.
  It is available by the chart-diagram route rather than through the reduction of Stacks 03DO
  to Section 03DG.
* The exactness of `f_*` is only ever needed on the single map `p`, whose source and target are
  quasi-coherent — the source because a finite locally free module is of finite presentation,
  the target by the previous item — so
  `AlgebraicGeometry.Space.epi_modulePushforward_map_of_isAffineHom` for the affine morphism `f`
  supplies it.

**What remains assumed, and what it is not.**  `AlgebraicGeometry.Space.DirectImageDualDescent`
is the last two steps of the source's proof: the identification `f_*f^*𝒢 = 𝒢 ⊗_{𝒪_Y} f_*𝒪_X`
and the twist by the dual of `f_*𝒪_X`.  Its first half is **not** the obstruction and is
available: the tensor product of `𝒪_Y`-modules on the small étale ringed site is
`AlgebraicGeometry.Space.modulesMonoidalCategory`, and the projection formula at the structure
sheaf of an affine morphism is
`AlgebraicGeometry.Space.modulePushforwardPullbackIsoSheafTensor`.  The dual of a module is
available as an object as well, `AlgebraicGeometry.Space.smallEtaleInternalHomSmall` into
`𝒪_Y`, the internal Hom of Stacks 03EM brought down to the module universe of the schemes by
the essential smallness of the small étale site.

The obstruction is the *duality* and nothing else.  What the source's last step needs beyond
the two constructions is the **coevaluation** `𝒪_Y ⟶ f_*𝒪_X ⊗ (f_*𝒪_X)^∨`, the trace element
of a finite locally free module; it is what makes `(f_*𝒪_X)^∨` a left dual and so supplies the
adjunction `(f_*𝒪_X)^∨ ⊗ - ⊣ f_*𝒪_X ⊗ -` along which the epimorphism
`f_*ℰ ⟶ 𝒢 ⊗ f_*𝒪_X` is transposed.  The evaluation alone is free from the closed structure and
does not suffice: without the coevaluation the transposed map cannot be formed at all, and the
evaluation `(f_*𝒪_X)^∨ ⊗ f_*𝒪_X ⟶ 𝒪_Y` is not an epimorphism for a module of rank zero.

That the dual of a finite locally free module is a left dual is Stacks 0FNY, and in this
development it is proved only at module universe `max u v`
(`Stacks.SheafOfModules.nonempty_hasRightDual_of_isFiniteLocallyFree`, whose dual object is
`Stacks.SheafOfModules.dualSheaf`), whereas the modules of an algebraic space live at the
universe `u` of the schemes while the objects of its small étale site live at `u + 1`.  The same
universe gap is recorded for the dual criterion of Stacks 0D2X in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/FiniteLocallyFreeModuleDescent.lean`.

Every other ingredient of the scheme-level counterpart
`AlgebraicGeometry.hasResolutionProperty_of_surjective_isFiniteLocallyFree` does have an
algebraic-space form here, and this is where the surjectivity of `f` would be spent:

* `f_*𝒪_X ⊗ -` is faithful on quasi-coherent modules, by the projection formula above together
  with `AlgebraicGeometry.Space.modulePushforward_map_eq_zero_iff_of_isAffineHom` for the affine
  `f` and `AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_map_injective_of_isFlat`
  for the flat and surjective `f` — flatness being
  `AlgebraicGeometry.Space.isFinite_and_isFlat_of_isFiniteLocallyFree` of the hypothesis on `f`,
  and the one-member jointly surjective family being
  `AlgebraicGeometry.Space.isJointlySurjective_const_iff` of its surjectivity.
* Quasi-coherent modules are closed under cokernels,
  `AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`, so a functor injective
  on morphisms between them reflects epimorphisms.
* A tensor product of finite locally free modules is finite locally free, Stacks 03L6(2),
  `Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFiniteLocallyFreeOnSite`, whose
  module universe is free of the site's.

For schemes the left-dual property is available and the lemma is unconditional: that is
Stacks 0GTC, which this development carries.

## References

* [Stacks Project, Tag 0GUV](https://stacks.math.columbia.edu/tag/0GUV)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 0GTC](https://stacks.math.columbia.edu/tag/0GTC)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- For `f : X ⟶ Y` a surjective finite locally free morphism of algebraic spaces over a scheme
`S`, if `X` has the resolution property then so does `Y`, given one further input: `hdual`, the
projection formula together with the dual twist by `(f_*𝒪_X)^∨`.

This is the conditional form of Stacks 0GUV.  The tag itself is **not** registered here, because
`hdual` is now a theorem: `AlgebraicGeometry.Space.directImageDualDescent` proves
`AlgebraicGeometry.Space.DirectImageDualDescent` outright for every morphism of algebraic spaces,
so the unconditional statement — hypotheses exactly the tag's — is
`AlgebraicGeometry.Space.hasResolutionProperty_of_isSurjective_isFiniteLocallyFree_unconditional`
in `StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ResolutionPropertyFiniteLocallyFreeTrace.lean`,
and that is where `@[stacks 0GUV]` sits.  This statement is kept because it isolates which step
of the source's proof uses which input.

The implementation notes below say that the obstruction inside `hdual` is the coevaluation
`𝒪_Y ⟶ f_*𝒪_X ⊗ (f_*𝒪_X)^∨` of Stacks 0FNY, at a module universe the small étale ringed site of
an algebraic space does not reach.  **That was wrong**, and it is why `hdual` looked unreachable
for so long: the transposed map is built from the *evaluation*, the projection formula and the
monoidal constraints alone, and no duality is needed to form it — a duality would only let one
recognise it as a transpose.  `directImageDualDescent` uses no coevaluation and no
`HasRightDual (f_*𝒪_X)`. -/
theorem hasResolutionProperty_of_isSurjective_isFiniteLocallyFree_of_dualTwist (f : X ⟶ Y)
    (hsurj : IsSurjective B S hS f.hom) (hflf : IsFiniteLocallyFree B S hS f)
    (hdual : DirectImageDualDescent B S hS f)
    (hX : HasResolutionProperty.{u, u} B S hS X.1 X.2) :
    HasResolutionProperty.{u, u} B S hS Y.1 Y.2 := by
  refine (hasResolutionProperty_iff B S hS Y.1 Y.2).mpr fun G hGft => ?_
  have hpullQcoh := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f
    G.obj G.property
  have := isFiniteTypeOnSite_modulePullback B S hS f G.obj hGft
  obtain ⟨E, hE, p, hp⟩ := (hasResolutionProperty_iff B S hS X.1 X.2).mp hX
    (⟨(modulePullback B S hS f).obj G.obj, hpullQcoh⟩ :
      QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
  have := hp
  have := SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite hE
  exact hdual hsurj hflf G.obj G.property hGft ((modulePushforward B S hS f).obj E)
    (isFiniteLocallyFreeOnSite_modulePushforward_of_isFiniteLocallyFree B S hS f hflf E hE)
    ((modulePushforward B S hS f).map p)
    (epi_modulePushforward_map_of_isAffineHom f hflf.1 inferInstance hpullQcoh p)

end AlgebraicGeometry.Space

end
