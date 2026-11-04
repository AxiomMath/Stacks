module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationHomSectionsTop
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationThickenedBaseAction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationThickenedBaseGlobalLift
public import StacksFrontier.CategoryTheory.Linear.AdjunctionHomLinearEquiv
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationConormal
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSequenceTerms
public import StacksFrontier.Deformation.Examples.Geometric.SpecialFibreFirstOrder

/-!
# The group acting on the lifts of a morphism of schemes is the derivation term of Tag 0E3V

Let `f : X ⟶ Y` be a morphism of schemes over a field `k`, and let `i : X ⟶ X'` be the
special-fibre immersion of a deformation of `X`. The group that
[Stacks Project, Tag 0CK2] makes act simply transitively on the lifts of `f` over a thickened
base is, over the whole space, the sections of `SheafHom_{𝒪_X}(f^*Ω_{Y/k}, 𝒞_{X/X'})`. When the
deformation is first order the conormal sheaf `𝒞_{X/X'}` is the structure sheaf of `X`
(`Deformation.Examples.deformationConormalIsoUnit`), and then the acting group is

`Hom_{𝒪_X}(f^*Ω_{Y/k}, 𝒪_X) = Hom_{𝒪_Y}(Ω_{Y/k}, f_*𝒪_X) = Der_k(𝒪_Y, f_*𝒪_X)`,

the third term of the exact sequence of [Stacks Project, Tag 0E3V]. This file proves that chain
of identifications **as `k`-vector spaces**: the `k`-action on the acting group comes from `X`
being a scheme over `k` through `f ≫ pY`, the `k`-action on the derivations comes from `Y` being
a scheme over `k` through `pY`, and the adjunction `f^* ⊣ f_*` matches them.

## Main definitions

* `Deformation.Examples.schemeMorphismModuleHomLinearEquiv`: the adjunction
  `Hom_{𝒪_X}(f^*M, N) ≃ Hom_{𝒪_Y}(M, f_*N)` as an isomorphism of `k`-vector spaces, for the two
  `k`-linear structures the two structure morphisms induce.
* `Deformation.Examples.schemeMorphismLiftHomLinearEquiv`: the payoff at the cotangent sheaf,
  `Hom_{𝒪_X}(f^*Ω_{Y/k}, 𝒞) ≃ₗ[k] Der_k(𝒪_Y, f_*𝒪_X)` for any identification of the coefficient
  sheaf `𝒞` with `𝒪_X`.
* `Deformation.Examples.deformationHomSectionsTopAddEquiv`: the sections over the whole space of
  the sheaf of [Stacks Project, Tag 04FJ] are the global homomorphisms
  `f^*Ω_{Y/k} ⟶ 𝒞_{X/X'}`.
* `Deformation.Examples.deformationHomSectionsTopModule`: the resulting `k`-vector space
  structure on that group of sections.
* `Deformation.Examples.deformationHomSectionsTopLinearEquiv`: **the derivations–lift-group
  bridge.** The group acting on the lifts of `f` over the whole space is the third term
  `Der_k(𝒪_Y, f_*𝒪_X)` of the sequence of [Stacks Project, Tag 0E3V], `k`-linearly.
* `Deformation.Examples.deformationHomSectionsTopDerivationsAddEquiv`: that bridge as an
  isomorphism of additive groups, which is what an action by the acting group consumes.

## Main results

* `Deformation.Examples.schemeMorphismPushforward_linear`: the pushforward along a morphism of
  schemes over `k` is `k`-linear. This is what carries the `k`-action across the adjunction.
* `Deformation.Examples.deformationHomSectionsTopLinearEquiv_apply`: the bridge is the adjunction
  bijection, read through the identification of the coefficient sheaf — it is not an arbitrary
  reparametrisation of the acting group.
* `Deformation.Examples.exists_simplyTransitive_addAction_schemeMorphismLifts`:
  **[Stacks Project, Tag 0CK2] instantiated at a pair of deformations.** For deformations `X'` of
  `X` and `Y'` of `Y` over one object of `𝒞_Λ` along which `f` lifts, the third term
  `Der_k(𝒪_Y, f_*𝒪_X)` acts simply transitively on the morphisms `X' ⟶ Y'` over the base that
  restrict to `f`.

## Implementation notes

The two `k`-linear structures are `AlgebraicGeometry.modulesLinear k (Over.mk (f ≫ pY))` on
`𝒪_X`-modules and `AlgebraicGeometry.modulesLinear k (Over.mk pY)` on `𝒪_Y`-modules; neither is
an instance, because the action depends on the structure morphism and not on the type, so both
are supplied by `letI` exactly as in
`StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismSequenceTerms.lean`. They are ascribed
at the *unwrapped* type `SheafOfModules (structureSheafRing _)` rather than at
`Scheme.Modules _`: the two are equal by `rfl`, but `AlgebraicGeometry.Scheme.Modules` is a
`def` and instance search crosses it in neither direction, so an instance registered at the
wrapper is invisible where the sheaf-theoretic constructions state their arrows.

That the `k`-action crosses the adjunction is
`CategoryTheory.Adjunction.homLinearEquiv` applied to
`AlgebraicGeometry.RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction`: the
bijection is `φ ↦ η ≫ f_*φ`, so it suffices that `f_*` be `k`-linear, which is
`AlgebraicGeometry.over_pushforward_linear` — the pushforward of a scalar multiple is the
multiple of the pushforward because the scalar is pulled back from the base in both spellings.
Linearity of `f^*` is not used.

The module `a^*Ω_{Y/Z}` of Tag 0CK2's acting sheaf is
`Stacks.Smooth.pullbackCotangentSheaf`, which is by definition the module pullback of the
ringed-space `Stacks.Sheaves.RingedSpaceDifferentials.moduleOfDifferentials` — the very sheaf
out of which the derivations of
`Deformation.Examples.schemeMorphismDerivationsLinearEquiv` are maps. So no comparison of two
spellings of the cotangent sheaf occurs, and Mathlib's `relativeDifferentials` is not involved.

Over the whole space the preimage `i ⁻¹ᵁ ⊤` is `⊤` by `rfl`, so
`Stacks.Thickenings.deformationHomSections i a pY ⊤` is the sections over `⊤` of the sheaf of
homomorphisms with no transport, and
`Stacks.Thickenings.moduleHomSectionsTopEquiv` identifies those with the global homomorphisms.
There is no `k`-action on a section of a sheaf of homomorphisms defined termwise, so the `k`-
vector space structure on the acting group is *transported* along that identification, as the
one on the derivations is transported in the file cited above; the content of the bridge is
that the two transported structures agree with the two structures the base field induces on the
two groups of global homomorphisms.

The instantiation at a pair of deformations takes the deformation data as the two cartesian
squares over a *common* object `A` of `𝒞_Λ`, which is the shape
`Deformation.Examples.SchemeDeformationCategory` records and the shape
[Stacks Project, Tag 0E3V] uses — `X'` and `Y'` are both deformations over `k[ε]` there. Two
deformations given as objects of that structure have their own `base` fields, and matching them
would mean transporting a sheaf of modules along an equality of base objects, which the library
avoids; taking the base as a parameter and the two squares as hypotheses avoids it. The conormal
datum of Tag 0CK2 is not a hypothesis: it is produced from the given lift by
`Stacks.Thickenings.isBaseCompatibleConormalMap_of_globalLift`, and it is the only one compatible
with the base.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Sheaves.RingedSpaceDifferentials (SDerivation moduleOfDifferentials)
open Stacks.Thickenings (deformationHomSections immersionConormalSheaf moduleHomSections
  moduleHomSectionsTopEquiv)

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))

/-! ### The pulled-back cotangent sheaf -/

/-- `f^*Ω_{Y/k}`, the module out of which the sheaf of [Stacks Project, Tag 04FJ] takes
homomorphisms, written as a module pullback of a ringed-space module of differentials — the
spelling in which the adjunction `f^* ⊣ f_*` is stated. -/
abbrev schemeMorphismPullbackCotangent :
    SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
  (modulePullback f.toLRSHom.toShHom).obj (moduleOfDifferentials pY.toLRSHom.toShHom)

/-- The pulled-back cotangent sheaf is the `a^*Ω_{Y/Z}` of [Stacks Project, Tag 0CK2]: the
cotangent sheaf of a morphism of schemes is by definition the ringed-space module of
differentials, and the module pullback of schemes is the ringed-space one. -/
theorem schemeMorphismPullbackCotangent_eq :
    schemeMorphismPullbackCotangent f pY = Stacks.Smooth.pullbackCotangentSheaf pY f := rfl

/-! ### The `k`-action crosses the adjunction -/

/-- **The pushforward along a morphism of schemes over `k` is `k`-linear.** The scalar action on
`𝒪_X`-modules is multiplication by the image of the scalar under the structure morphism of `X`,
and likewise on `𝒪_Y`-modules; the structure morphism of `X` factors through that of `Y`, so the
two agree on the sections of a pushforward and `f_*(r • φ) = r • f_*φ`. -/
theorem schemeMorphismPushforward_linear :
    letI : Linear k (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
      AlgebraicGeometry.modulesLinear k (Over.mk (f ≫ pY))
    letI : Linear k (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) :=
      AlgebraicGeometry.modulesLinear k (Over.mk pY)
    Functor.Linear k (modulePushforward f.toLRSHom.toShHom) :=
  AlgebraicGeometry.over_pushforward_linear k
    (X := Over.mk (f ≫ pY)) (Y := Over.mk pY) (Over.homMk f rfl)

/-- **The adjunction `f^* ⊣ f_*` as an isomorphism of `k`-vector spaces.** For a morphism
`f : X ⟶ Y` of schemes over `k`, an `𝒪_Y`-module `M` and an `𝒪_X`-module `N`, the canonical
bijection `Hom_{𝒪_X}(f^*M, N) ≃ Hom_{𝒪_Y}(M, f_*N)` of [Stacks Project, Tag 0096] is `k`-linear
for the `k`-vector space structures the two structure morphisms induce on the two groups of
homomorphisms: it sends `φ` to `η_M ≫ f_*φ`, and `f_*` is `k`-linear by
`Deformation.Examples.schemeMorphismPushforward_linear`. -/
def schemeMorphismModuleHomLinearEquiv
    (M : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    letI lX : Linear k (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
      AlgebraicGeometry.modulesLinear k (Over.mk (f ≫ pY))
    letI lY : Linear k (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) :=
      AlgebraicGeometry.modulesLinear k (Over.mk pY)
    letI : Module k ((modulePullback f.toLRSHom.toShHom).obj M ⟶ N) := lX.homModule _ _
    letI : Module k (M ⟶ (modulePushforward f.toLRSHom.toShHom).obj N) := lY.homModule _ _
    ((modulePullback f.toLRSHom.toShHom).obj M ⟶ N) ≃ₗ[k]
      (M ⟶ (modulePushforward f.toLRSHom.toShHom).obj N) :=
  letI : Linear k (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
    AlgebraicGeometry.modulesLinear k (Over.mk (f ≫ pY))
  letI : Linear k (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) :=
    AlgebraicGeometry.modulesLinear k (Over.mk pY)
  letI := schemeMorphismPushforward_linear f pY
  Adjunction.homLinearEquiv k (modulePullbackPushforwardAdjunction f.toLRSHom.toShHom) M N

/-- `Deformation.Examples.schemeMorphismModuleHomLinearEquiv` is the bijection of the adjunction
of [Stacks Project, Tag 0096], so it is not an arbitrary reparametrisation. -/
theorem schemeMorphismModuleHomLinearEquiv_apply
    (M : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (φ : (modulePullback f.toLRSHom.toShHom).obj M ⟶ N) :
    schemeMorphismModuleHomLinearEquiv f pY M N φ = homEquiv f.toLRSHom.toShHom N M φ := rfl

/-! ### The acting group of the lifts is the derivation term -/

/-- **The group of global homomorphisms `f^*Ω_{Y/k} ⟶ 𝒞` is the derivations
`Der_k(𝒪_Y, f_*N)`, `k`-linearly**, for any identification `ε` of the coefficient sheaf `𝒞`
with an `𝒪_X`-module `N`.

At `N = 𝒪_X` this is the third term `Der_k(𝒪_Y, f_*𝒪_X)` of the sequence of
[Stacks Project, Tag 0E3V]. No rank-one hypothesis enters: the coefficient sheaf is arbitrary, so
the statement covers a deformation over a square-zero base of any finite rank, where the conormal
sheaf of the special fibre is free of that rank rather than of rank one.

This is the composite of three `k`-linear identifications: postcomposition with `ε`, which is
`k`-linear because composition is `k`-bilinear; the adjunction
`Deformation.Examples.schemeMorphismModuleHomLinearEquiv` at the cotangent sheaf of `Y`; and the
corepresentability of relative derivations,
`Deformation.Examples.schemeMorphismDerivationsLinearEquiv`. -/
def schemeMorphismLiftHomLinearEquiv
    {C N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)} (ε : C ≅ N) :
    letI lX : Linear k (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
      AlgebraicGeometry.modulesLinear k (Over.mk (f ≫ pY))
    letI : Module k (schemeMorphismPullbackCotangent f pY ⟶ C) := lX.homModule _ _
    letI := schemeMorphismDerivationsModule f pY N
    (schemeMorphismPullbackCotangent f pY ⟶ C) ≃ₗ[k]
      SDerivation pY.toLRSHom.toShHom
        ((modulePushforward f.toLRSHom.toShHom).obj N) :=
  letI : Linear k (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
    AlgebraicGeometry.modulesLinear k (Over.mk (f ≫ pY))
  letI : Linear k (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) :=
    AlgebraicGeometry.modulesLinear k (Over.mk pY)
  (Linear.homCongr k (Iso.refl (schemeMorphismPullbackCotangent f pY)) ε).trans
    ((schemeMorphismModuleHomLinearEquiv f pY (moduleOfDifferentials pY.toLRSHom.toShHom)
        N).trans
      (schemeMorphismDerivationsLinearEquiv f pY N).symm)

/-! ### The sections over the whole space -/

section Sections

variable {X' : Scheme.{u}} (i : X ⟶ X') [IsImmersion i]

/-- **The sections over the whole space of the sheaf of [Stacks Project, Tag 04FJ] are the
global homomorphisms `f^*Ω_{Y/k} ⟶ 𝒞_{X/X'}`.** The group that acts on the lifts of `f` over an
open `V` of `X'` is the sections of `SheafHom_{𝒪_X}(f^*Ω_{Y/k}, 𝒞_{X/X'})` over `i ⁻¹ᵁ V`; at
`V = ⊤` that preimage is `⊤`, and the sections over `⊤` of a sheaf of homomorphisms are the
global homomorphisms by `Stacks.Thickenings.moduleHomSectionsTopEquiv`. -/
def deformationHomSectionsTopAddEquiv :
    deformationHomSections i f pY ⊤ ≃+
      (schemeMorphismPullbackCotangent f pY ⟶ immersionConormalSheaf i) :=
  moduleHomSectionsTopEquiv (schemeMorphismPullbackCotangent f pY) (immersionConormalSheaf i)

/-- **The `k`-vector space structure on the group acting on the lifts of `f`.** A section of a
sheaf of homomorphisms carries no scalar action defined termwise, so the structure is
transported from the global homomorphisms along
`Deformation.Examples.deformationHomSectionsTopAddEquiv`, where it is the action induced by the
structure morphism of `X` over `k`. -/
@[instance_reducible]
def deformationHomSectionsTopModule : Module k (deformationHomSections i f pY ⊤) :=
  letI lX : Linear k (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
    AlgebraicGeometry.modulesLinear k (Over.mk (f ≫ pY))
  letI : Module k (schemeMorphismPullbackCotangent f pY ⟶ immersionConormalSheaf i) :=
    lX.homModule _ _
  (deformationHomSectionsTopAddEquiv f pY i).module k

/-- **The derivations–lift-group bridge of [Stacks Project, Tag 0E3V].** Let `f : X ⟶ Y` be a
morphism of schemes over `k` and let `i : X ⟶ X'` be an immersion whose conormal sheaf is
identified by `ε` with an `𝒪_X`-module `N` — for the special fibre of a first-order deformation
`N` is the structure sheaf of `X` and `ε` is
`Deformation.Examples.deformationConormalIsoUnit`. Then the group that
[Stacks Project, Tag 0CK2] makes act simply transitively on the lifts of `f` over the whole
space **is** `Der_k(𝒪_Y, f_*N)`, as a `k`-vector space:

`Hom_{𝒪_X}(f^*Ω_{Y/k}, 𝒞_{X/X'}) = Hom_{𝒪_X}(f^*Ω_{Y/k}, N) = Hom_{𝒪_Y}(Ω_{Y/k}, f_*N)
= Der_k(𝒪_Y, f_*N)`.

At `N = 𝒪_X` the right-hand side is the third term `Der_k(𝒪_Y, f_*𝒪_X)` of the source's exact
sequence, which is the case the source states. The coefficient sheaf is left arbitrary because
the trivialisation of the conormal sheaf is a rank-one phenomenon while nothing in the chain
above is: over a square-zero base whose maximal ideal has rank `n` the conormal sheaf of the
special fibre is free of rank `n`, and the chain then reads the acting group as
`Der_k(𝒪_Y, f_*(𝒪_X^n))`.

The `k`-action on the left is the one `X` carries as a scheme over `k` through `f ≫ pY`, the
`k`-action on the right is the one `Y` carries through `pY`, and that the adjunction matches them
is `Deformation.Examples.schemeMorphismPushforward_linear`. -/
def deformationHomSectionsTopLinearEquiv
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (ε : immersionConormalSheaf i ≅ N) :
    letI := deformationHomSectionsTopModule f pY i
    letI := schemeMorphismDerivationsModule f pY N
    deformationHomSections i f pY ⊤ ≃ₗ[k]
      SDerivation pY.toLRSHom.toShHom ((modulePushforward f.toLRSHom.toShHom).obj N) :=
  letI lX : Linear k (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
    AlgebraicGeometry.modulesLinear k (Over.mk (f ≫ pY))
  letI : Module k (schemeMorphismPullbackCotangent f pY ⟶ immersionConormalSheaf i) :=
    lX.homModule _ _
  ((deformationHomSectionsTopAddEquiv f pY i).linearEquiv k).trans
    (schemeMorphismLiftHomLinearEquiv f pY ε)

/-- **The bridge is the adjunction bijection**, read through the identification of the conormal
sheaf: it carries a section `θ` of `SheafHom_{𝒪_X}(f^*Ω_{Y/k}, 𝒞_{X/X'})` over the whole space
to the derivation that the corepresentability identification
`Deformation.Examples.schemeMorphismDerivationsAddEquiv` attaches to the transpose, under the
adjunction `f^* ⊣ f_*`, of the global homomorphism of `θ` composed with `ε`. So the bridge is
pinned to the identifications it is built from, and is not an arbitrary reparametrisation of the
acting group. -/
theorem deformationHomSectionsTopLinearEquiv_apply
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (ε : immersionConormalSheaf i ≅ N)
    (θ : deformationHomSections i f pY ⊤) :
    letI := deformationHomSectionsTopModule f pY i
    letI := schemeMorphismDerivationsModule f pY N
    deformationHomSectionsTopLinearEquiv f pY i ε θ =
      schemeMorphismDerivationsAddEquiv f pY N
        (homEquiv f.toLRSHom.toShHom N
          (moduleOfDifferentials pY.toLRSHom.toShHom)
          (deformationHomSectionsTopAddEquiv f pY i θ ≫ ε.hom)) := rfl

/-- The bridge of `Deformation.Examples.deformationHomSectionsTopLinearEquiv` as an isomorphism
of additive groups, which is all that an action by the acting group needs. -/
def deformationHomSectionsTopDerivationsAddEquiv
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (ε : immersionConormalSheaf i ≅ N) :
    deformationHomSections i f pY ⊤ ≃+
      SDerivation pY.toLRSHom.toShHom ((modulePushforward f.toLRSHom.toShHom).obj N) :=
  letI := deformationHomSectionsTopModule f pY i
  letI := schemeMorphismDerivationsModule f pY N
  (deformationHomSectionsTopLinearEquiv f pY i ε).toAddEquiv

end Sections

/-! ### The action on the lifts between two deformations -/

section Lifts

attribute [local instance] residueSpecMap_isClosedImmersion

/-- **Stacks 0E3V: the third term of the source's sequence acts simply transitively on the lifts
of `f` between two deformations.** Let `f : X ⟶ Y` be a morphism of schemes over `k`, let `X'`
and `Y'` be deformations of `X` and of `Y` over one object `A` of `𝒞_Λ` — that is, schemes over
`baseSpec A` whose fibres over the closed point are identified with `X` and with `Y` by the two
cartesian squares `hX` and `hY` — let `i : X ⟶ X'` be a first order thickening, and suppose `f`
lifts to a morphism `F : X' ⟶ Y'` over `baseSpec A`. Then the third term
`Der_k(𝒪_Y, f_*𝒪_X)` of the source's exact sequence **acts simply transitively** on the
morphisms `X' ⟶ Y'` over `baseSpec A` that restrict to `f` along `i`.

This is [Stacks Project, Tag 0CK2] at `Z = Spec k` and `Z' = baseSpec A`, where its cartesian
square is the identification of the special fibre of the deformation of `Y`, its conormal datum
is discharged by `F`, and its acting group is carried onto the derivations by
`Deformation.Examples.deformationHomSectionsTopDerivationsAddEquiv` — which is `k`-linear, so the
action is by the sequence's term and not merely by an abstract group of the same size.

The first-order hypothesis is read on the base object, where it is a condition on `A` alone:
`hA` says the maximal ideal of `A` has square zero, which makes `i` a first-order thickening by
`Deformation.Examples.ker_sq_eq_bot_of_isPullback`. It carries **no rank hypothesis** on that
maximal ideal, and neither does the identification `ε`, which reads the conormal sheaf of `i` as
an arbitrary `𝒪_X`-module `N`: the acting group is then `Der_k(𝒪_Y, f_*N)`. At `N = 𝒪_X` it is
the third term `Der_k(𝒪_Y, f_*𝒪_X)` of the source's sequence, and that is the case
[Stacks Project, Tag 0E3V] uses — there both hypotheses are discharged when `A` is the dual
numbers, by `Deformation.Examples.maximalIdeal_artinianDualNumbers_sq_eq_bot` and
`Deformation.Examples.deformationConormalIsoUnit`. Over a square-zero base whose maximal ideal
has rank `n` the conormal sheaf is instead free of rank `n`, and the statement applies with that
`N`: nothing about the simply transitive action of [Stacks Project, Tag 0CK2] or about the
adjunction `f^* ⊣ f_*` sees the rank. -/
theorem exists_simplyTransitive_addAction_schemeMorphismLifts
    {A : ArtinianLocalAlgCat.{u, u, u} Λ k} {X' Y' : Scheme.{u}}
    (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (hf : f ≫ pY = pX)
    {i : X ⟶ X'} {j : Y ⟶ Y'} [IsClosedImmersion i] [IsImmersion j]
    {pX' : X' ⟶ baseSpec A} {pY' : Y' ⟶ baseSpec A}
    (hX : IsPullback i pX pX' (residueSpecMap A))
    (hY : IsPullback j pY pY' (residueSpecMap A))
    (hA : IsLocalRing.maximalIdeal (A : Type u) ^ 2 = ⊥)
    {F : X' ⟶ Y'} (hF₁ : F ≫ pY' = pX') (hF₂ : i ≫ F = f ≫ j)
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (ε : immersionConormalSheaf i ≅ N) :
    ∃ act : SDerivation pY.toLRSHom.toShHom
          ((modulePushforward f.toLRSHom.toShHom).obj N) →
        Stacks.Thickenings.liftsOverBase i j pX' pY' f ⊤ →
        Stacks.Thickenings.liftsOverBase i j pX' pY' f ⊤,
      (∀ c : Stacks.Thickenings.liftsOverBase i j pX' pY' f ⊤, act 0 c = c) ∧
        (∀ (θ η : SDerivation pY.toLRSHom.toShHom
              ((modulePushforward f.toLRSHom.toShHom).obj N))
            (c : Stacks.Thickenings.liftsOverBase i j pX' pY' f ⊤),
          act (θ + η) c = act θ (act η c)) ∧
          ∀ c₀ c₁ : Stacks.Thickenings.liftsOverBase i j pX' pY' f ⊤,
            ∃! θ : SDerivation pY.toLRSHom.toShHom
                ((modulePushforward f.toLRSHom.toShHom).obj N), act θ c₀ = c₁ := by
  have ci : i ≫ pX' = (f ≫ pY) ≫ residueSpecMap A := by rw [hf]; exact hX.w
  obtain ⟨act, hzero, hadd, htrans⟩ :=
    Stacks.Thickenings.exists_simplyTransitive_addAction_liftsOverBaseOfGlobalLift
      (ker_sq_eq_bot_of_isPullback pX' hX hA) hY ci hF₁ hF₂
  have e := deformationHomSectionsTopDerivationsAddEquiv f pY i ε
  refine ⟨fun θ => act (e.symm θ), fun c => ?_, fun θ η c => ?_, fun c₀ c₁ => ?_⟩
  · exact (congrArg (fun z => act z c) (map_zero e.symm)).trans (hzero c)
  · exact (congrArg (fun z => act z c) (map_add e.symm θ η)).trans (hadd _ _ c)
  · obtain ⟨φ, hφ, huniq⟩ := htrans c₀ c₁
    refine ⟨e φ, (congrArg (fun z => act z c₀) (e.symm_apply_apply φ)).trans hφ, fun ψ hψ => ?_⟩
    exact (e.apply_symm_apply ψ).symm.trans (congrArg e (huniq (e.symm ψ) hψ))

end Lifts


end Deformation.Examples

end
