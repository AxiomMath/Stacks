module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTraceDualizingModule
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClosureEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraPullbackQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Modules.RestrictScalarsSheafification
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems

/-!
# The dual of `π_*𝒪_Y` as a `π_*𝒪_Y`-module

Let `π : Y ⟶ X` be a morphism of algebraic spaces and `𝒜 = π_*𝒪_Y`, a sheaf of rings on the
small étale site of `X`.  An `𝒜`-module read as an `𝒪_X`-module is restriction of scalars along
the structure map `π♯ : 𝒪_X ⟶ 𝒜` of Stacks 03G8.  This file constructs the *right* adjoint of
that restriction of scalars — coextension of scalars along `π♯` — and with it the `𝒜`-module

`𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)`,  `(a · φ)(b) = φ(a b)`,

which is the module structure that the quasi-inverse of the affine direct image equivalence of
[Stacks, Tag 08AI] consumes, and hence the input the relative dualizing module `ω_{Y/X}` of
[Stacks, Tag 0GUZ] is produced from.

## Main definitions

* `AlgebraicGeometry.Space.directImageAlgebraCoextendScalars` — coextension of scalars along
  `π♯`, the right adjoint of `AlgebraicGeometry.Space.directImageAlgebraRestrictScalars`.
* `AlgebraicGeometry.Space.dualizingAlgebraModule` — its value at `𝒪_X`, the dual
  `𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` carrying its `π_*𝒪_Y`-module structure.

## Main results

* `AlgebraicGeometry.Space.isLeftAdjoint_restrictScalars_structureSharp` — restriction of
  scalars along `π♯` has a right adjoint.
* `AlgebraicGeometry.Space.directImageAlgebraRestrictCoextendAdjunction` — the adjunction
  `Res ⊣ Coext`, i.e. `Hom_{𝒜}(𝒢, Coext 𝓝) ≅ Hom_{𝒪_X}(Res 𝒢, 𝓝)`.
* `AlgebraicGeometry.Space.homEquiv_dualizingAlgebraModule` — the universal property at `𝒪_X`:
  a map of `𝒜`-modules into the dual is a map of `𝒪_X`-modules into `𝒪_X`.  This is what pins
  `dualizingAlgebraModule` down; it is the characterisation by which
  `Stacks.SheafOfModules.CoextendScalars.coextendScalarsIsoHomSheaf` identifies the two
  small-universe models of the same object.

## Implementation notes

Coextension of scalars for sheaves of modules is in the library already, as Stacks 0932
(`Stacks.SheafOfModules.CoextendScalars.coextendScalars`) and Stacks 0A6F
(`RingedSpaceModuleAdjunction.homSheaf`), with the two identified by
`Stacks.SheafOfModules.CoextendScalars.coextendScalarsIsoHomSheaf`.  Neither is available here.
Both are stated for a site whose objects, whose morphisms and whose rings share one universe,
`{C : Type u} [Category.{u} C] {O O' : Sheaf J RingCat.{u}}`, and they are built sectionwise from
the slice-wise internal-hom presheaf `Stacks.PresheafOfModules.CoextendScalars.coextObj`.  The
small étale ringed site of an algebraic space is `AlgebraicGeometry.RingedSite.{u + 1, u, u}`:
its objects lie in `Type (u + 1)` while its morphisms and its structure rings lie in `Type u`,
so the sectionwise construction cannot be instantiated at it.

The right adjoint is therefore obtained abstractly instead of sectionwise, by the special
adjoint functor theorem (`CategoryTheory.isLeftAdjoint_of_preservesColimits_of_isSeparating`)
at the module universe `u`.  Its hypotheses are all already available at these universes:
restriction of scalars preserves colimits by
`AlgebraicGeometry.SheafOfModules.restrictScalars_preservesColimits`, which is universe-general
and gives preservation at `{u + 1, u}`, brought down to `{u, u}` by
`CategoryTheory.Limits.preservesColimitsOfSize_of_univLE`; and cocompleteness, local
smallness, well-copoweredness and the small separating family all come from
`SheafOfModules.isGrothendieckAbelian_of_essentiallySmall`, the small étale site being
essentially small at `u`.  `AlgebraicGeometry.Space.isLeftAdjoint_ι_quasicoherentSheaves` is
the precedent for this argument on the same site.

Two global instances, `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` and its Grothendieck
counterpart, hold only at a module universe which is a `max` of the site universes; at the
pinned module universe `u` they leave a stuck universe constraint and must be removed, exactly
as in `AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentExact`.

## What is not proved

The identification of the underlying `𝒪_X`-module of `dualizingAlgebraModule` with the already
constructed `AlgebraicGeometry.Space.dualizingPushforward`, i.e. with
`AlgebraicGeometry.Space.smallEtaleInternalHomSmall B S hS X.1 X.2 (π_*𝒪_Y) 𝒪_X`.  The argument
is available in outline and needs two further inputs.  Composing
`AlgebraicGeometry.Space.directImageAlgebraExtendRestrictAdjunction` with
`directImageAlgebraRestrictCoextendAdjunction` gives `E ⋙ Res ⊣ Coext ⋙ Res`, and the
`𝒪_X`-modules carry the tensor-hom adjunction
`AlgebraicGeometry.RingedSite.sheafTensorRightInternalHomSmallAdjunction`, which *is* stated at
`RingedSite.{u + 1, u, u}` and whose right adjoint
`AlgebraicGeometry.RingedSite.internalHomSheafSmallFunctor` has `dualizingPushforward` as its
value at `𝒪_X`.  `CategoryTheory.Adjunction.rightAdjointUniq` then identifies `Coext ⋙ Res`
with it, given a natural isomorphism `E ⋙ Res ≅ - ⊗_{𝒪_X} π_*𝒪_Y`.  What is missing is

* the naturality of `AlgebraicGeometry.Space.restrictScalarsExtendScalarsIsoTensorModule`,
  which is stated objectwise only; and
* that restriction of scalars along `π♯` carries the free rank-one `π_*𝒪_Y`-module to
  `AlgebraicGeometry.Space.pushforwardStructureModule`, equivalently that the direct image of
  modules carries `𝒪_Y` to that free module.  This is *not* definitional — `rfl` exhausts the
  heartbeat budget on it — so it needs a proof.

Both the quasi-coherence of `dualizingAlgebraModule`, which would follow from
`AlgebraicGeometry.Space.isQuasicoherentOnSite_dualizingPushforward` through
`AlgebraicGeometry.Space.isQuasicoherentOnSite_restrictScalars_structureSharp_iff`, and the
construction of `ω_{Y/X}` on `Y` as the value of the quasi-inverse
`AlgebraicGeometry.Space.directImageAlgebraPullback` at this module, wait on that
identification: the quasi-inverse accepts `dualizingAlgebraModule` as it stands, but the
defining property `π_*ω_{Y/X} ≅ 𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` of [Stacks, Tag 0GUZ] is a statement
about `dualizingPushforward`.

## References

* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ)
* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
* [Stacks Project, Tag 0932](https://stacks.math.columbia.edu/tag/0932)
* [Stacks Project, Tag 0A6F](https://stacks.math.columbia.edu/tag/0A6F)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/- The global instances `Abelian (SheafOfModules.{max u v r w} O)` and its Grothendieck
counterpart leave a stuck universe constraint against modules in the pinned universe `u`. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : AlgebraicSpaces B S hS}

/-- **Restriction of scalars along the structure map `π♯ : 𝒪_X ⟶ π_*𝒪_Y` of Stacks 03G8 has a
right adjoint.**

The sectionwise coextension of scalars of Stacks 0932 is unavailable at the universes of the
small étale site of an algebraic space, so the right adjoint is produced by the special adjoint
functor theorem: restriction of scalars preserves colimits, and its source — the
`π_*𝒪_Y`-modules with sections in the universe of the schemes — is a Grothendieck abelian
category, the small étale site being essentially small at that universe. -/
instance isLeftAdjoint_restrictScalars_structureSharp (π : Y ⟶ X) :
    (directImageAlgebraRestrictScalars B S hS π).IsLeftAdjoint := by
  have hes : EssentiallySmall.{u} (SmallEtale B S hS X.1) := inferInstance
  have hG := SheafOfModules.isGrothendieckAbelian_of_essentiallySmall
    (structureRingSheafDirectImage B S hS π)
  have := hG.locallySmall
  have hGX := SheafOfModules.isGrothendieckAbelian_of_essentiallySmall
    (structureRingSheaf B S hS X)
  have := hGX.locallySmall
  have := locallySmall_modules_smallEtale B S hS X.1 X.2
  have hbig : PreservesColimitsOfSize.{u + 1, u}
      (directImageAlgebraRestrictScalars B S hS π) :=
    AlgebraicGeometry.SheafOfModules.restrictScalars_preservesColimits.{u, u, u, u + 1}
      (structureSharp B S hS π)
  have hPres : PreservesColimitsOfSize.{u, u}
      (directImageAlgebraRestrictScalars B S hS π) :=
    preservesColimitsOfSize_of_univLE.{u + 1, u, u, u} _
  exact isLeftAdjoint_of_preservesColimits_of_isSeparating.{u} (isSeparator_separator _) _

/-- **Coextension of scalars along the structure map `π♯ : 𝒪_X ⟶ π_*𝒪_Y`**: the functor
`𝓝 ↦ 𝓗om_{𝒪_X}(π_*𝒪_Y, 𝓝)` from `𝒪_X`-modules to `π_*𝒪_Y`-modules, with the `π_*𝒪_Y`-action
`(a · φ)(b) = φ(a b)`.

This is the right adjoint of restriction of scalars along `π♯`, which is how Stacks 0932 and
Stacks 0A6F characterise the internal Hom over the target ring sheaf; it is obtained here
abstractly rather than sectionwise, for the universe reason recorded in the module
documentation. -/
def directImageAlgebraCoextendScalars (π : Y ⟶ X) :
    Modules.{u, u} B S hS X.1 X.2 ⥤
      SheafOfModules.{u} (structureRingSheafDirectImage B S hS π) :=
  (directImageAlgebraRestrictScalars B S hS π).rightAdjoint

/-- **Stacks 0932 at the structure map `π♯ : 𝒪_X ⟶ π_*𝒪_Y`**: restriction of scalars along `π♯`
is left adjoint to coextension of scalars along it, so a morphism of `π_*𝒪_Y`-modules
`𝒢 ⟶ 𝓗om_{𝒪_X}(π_*𝒪_Y, 𝓝)` is the same datum as a morphism of `𝒪_X`-modules `𝒢 ⟶ 𝓝`. -/
def directImageAlgebraRestrictCoextendAdjunction (π : Y ⟶ X) :
    directImageAlgebraRestrictScalars B S hS π ⊣
      directImageAlgebraCoextendScalars B S hS π :=
  Adjunction.ofIsLeftAdjoint (directImageAlgebraRestrictScalars B S hS π)

/-- **The dual `𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` of `π_*𝒪_Y`, carrying its `π_*𝒪_Y`-module structure
`(a · φ)(b) = φ(a b)`.**

This is the coextension of scalars of the structure sheaf `𝒪_X` along `π♯`.  It is the module
the quasi-inverse of the affine direct image equivalence of [Stacks, Tag 08AI] is applied to in
order to produce the relative dualizing module `ω_{Y/X}` of [Stacks, Tag 0GUZ]: that
quasi-inverse, `AlgebraicGeometry.Space.directImageAlgebraPullback`, consumes exactly a
`π_*𝒪_Y`-module, and the characterising isomorphism
`π_*ω_{Y/X} ≅ 𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` of the tag is an isomorphism of `π_*𝒪_Y`-modules. -/
def dualizingAlgebraModule (π : Y ⟶ X) :
    SheafOfModules.{u} (structureRingSheafDirectImage B S hS π) :=
  (directImageAlgebraCoextendScalars B S hS π).obj
    (SheafOfModules.unit (structureRingSheaf B S hS X))

/-- **The universal property of the dual.**  A morphism of `π_*𝒪_Y`-modules from `𝒢` into
`𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` is the same datum as a morphism of `𝒪_X`-modules from `𝒢`, read
through `π♯`, into `𝒪_X`.

This pins `AlgebraicGeometry.Space.dualizingAlgebraModule` down: it is the characterisation by
which `Stacks.SheafOfModules.CoextendScalars.coextendScalarsIsoHomSheaf` identifies Stacks
0932's and Stacks 0A6F's models of this object with each other in the universes where both are
available. -/
def homEquiv_dualizingAlgebraModule (π : Y ⟶ X)
    (G : SheafOfModules.{u} (structureRingSheafDirectImage B S hS π)) :
    (G ⟶ dualizingAlgebraModule B S hS π) ≃
      ((directImageAlgebraRestrictScalars B S hS π).obj G ⟶
        SheafOfModules.unit (structureRingSheaf B S hS X)) :=
  ((directImageAlgebraRestrictCoextendAdjunction B S hS π).homEquiv G
    (SheafOfModules.unit (structureRingSheaf B S hS X))).symm

end AlgebraicGeometry.Space

end
