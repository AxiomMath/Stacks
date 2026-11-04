module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageOverPushforwardRing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# The left adjoint of the direct image of modules over `f_*𝒪_Y`

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, and let `𝒜 = f_*𝒪_Y` be the direct image of the structure sheaf of `Y`, a sheaf of
rings on the small étale site of `X`.  `AlgebraicGeometry.Space.moduleDirectImage` is the direct
image of `𝒪_Y`-modules taken over `𝒜`, which is Stacks 03D1 for the small étale sites.  This
file constructs its **left adjoint**

`𝒢 ↦ 𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒢`

and the adjunction, for an arbitrary morphism of algebraic spaces.

This is the functor the quasi-inverse of Stacks 08AI is built from: at the level of schemes the
quasi-inverse of Stacks 01SB is `𝒢 ↦ f^*𝒢 ⊗_{f^*𝒜} 𝒪_X`, which is the same formula.

## Main definitions

* `AlgebraicGeometry.Space.directImageAlgebraRingCounit` — the ring-level counit
  `f⁻¹(f_*𝒪_Y) ⟶ 𝒪_Y` on the small étale sites.
* `AlgebraicGeometry.Space.directImageAlgebraPullback` — the functor
  `𝒢 ↦ 𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒢` from `𝒜`-modules to `𝒪_Y`-modules.

## Main results

* `AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction` — Stacks 03D4 for the small
  étale sites of algebraic spaces: `𝒢 ↦ 𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒢` is left adjoint to
  `AlgebraicGeometry.Space.moduleDirectImage`.

## Implementation notes

Both are instances of the topos-level constructions, at the morphism of small étale ringed topoi
of Stacks 03G8 in the shape the modules development consumes,
`AlgebraicGeometry.Space.smallEtaleRingedToposModulesHom`.  Nothing about algebraic spaces enters
beyond two identifications, and both hold on the nose: the direct image of sheaves of sets of
that morphism of topoi is `AlgebraicGeometry.Space.smallEtaleDirectImage`
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_pushforward_eq`), so its direct-image sheaf of
rings is `AlgebraicGeometry.Space.structureRingSheafDirectImage` and its direct image of modules
is `AlgebraicGeometry.Space.moduleDirectImage`.

The inverse image `f⁻¹` of a sheaf of rings other than a structure sheaf is taken along the
morphism of small étale topoi at the universe of the structure rings of Stacks 03G2, part (3),
`AlgebraicGeometry.Space.smallToposMorphismTypeU`.

The form of Stacks 03D4 in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposModuleAdjointPullPush.lean` asks the source
site to be small, which the small étale site is not — its objects lie one universe above its
morphisms.  `Stacks.Sheaves.RingedToposModules.tensorInverseImageAdjPushforwardModuleFunctor` is
the same adjunction over an arbitrary site, and it is what is instantiated below.

The relative tensor product over `f⁻¹𝒜` needs no construction of its own: it is extension of
scalars along the ring-level counit, which
`Stacks.NoncommChangeOfRings.Sheaf.extendScalars` provides over an arbitrary site and for
sheaves of not necessarily commutative rings.

## References

* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
* [Stacks Project, Tag 03D4](https://stacks.math.columbia.edu/tag/03D4)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : AlgebraicSpaces B S hS}

/-- **The ring-level counit `f⁻¹(f_*𝒪_Y) ⟶ 𝒪_Y`** of a morphism `f : Y ⟶ X` of algebraic
spaces, on the small étale sites: the adjunct of the identity of `f_*𝒪_Y` under `f⁻¹ ⊣ f_*`,
as a morphism of sheaves of rings.

This is `Stacks.Sheaves.ToposPushforward.ringCounit` at the morphism of small étale ringed topoi
of Stacks 03G8.  It is the map along which the quasi-inverse of Stacks 08AI extends scalars. -/
noncomputable abbrev directImageAlgebraRingCounit (f : Y ⟶ X) :=
  ringCounit (smallEtaleRingedToposModulesHom B S hS f).toToposHom (structureRingSheaf B S hS Y)

/-- **The left adjoint of the direct image of modules over `𝒜 = f_*𝒪_Y`**: the functor
`𝒢 ↦ 𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒢` from `𝒜`-modules on the small étale site of `X` to `𝒪_Y`-modules on
the small étale site of `Y`.

It is the inverse image of modules of Stacks 03D2 along the morphism of small étale topoi,
followed by extension of scalars along
`AlgebraicGeometry.Space.directImageAlgebraRingCounit`. -/
noncomputable def directImageAlgebraPullback (f : Y ⟶ X) :
    SheafOfModules.{u} (structureRingSheafDirectImage B S hS f) ⥤
      Modules.{u, u} B S hS Y.1 Y.2 :=
  inverseImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
      (structureRingSheafDirectImage B S hS f) ⋙
    Stacks.NoncommChangeOfRings.Sheaf.extendScalars.{u}
      (directImageAlgebraRingCounit B S hS f)

/-- **Stacks 03D4 for the small étale sites of algebraic spaces**: for a morphism `f : Y ⟶ X` of
algebraic spaces and `𝒜 = f_*𝒪_Y`, the functor `𝒢 ↦ 𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒢` is left adjoint to the
direct image `ℱ ↦ f_*ℱ` of `𝒪_Y`-modules over `𝒜`.  It supplies the bijection

`Hom_{𝒪_Y}(𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒢, ℱ) = Hom_𝒜(𝒢, f_*ℱ)`,

naturally in both variables.

No hypothesis is placed on `f`.  The right adjoint is
`AlgebraicGeometry.Space.moduleDirectImage` itself, which is the direct image of Stacks 03D1 for
the small étale sites; so this is the adjoint pair whose unit and counit the equivalence of
Stacks 08AI is about. -/
noncomputable def directImageAlgebraPullbackAdjunction (f : Y ⟶ X) :
    directImageAlgebraPullback B S hS f ⊣ moduleDirectImage B S hS f :=
  tensorInverseImageAdjPushforwardModuleFunctor
    (smallEtaleRingedToposModulesHom B S hS f).toToposHom (structureRingSheaf B S hS Y)

end AlgebraicGeometry.Space

end
