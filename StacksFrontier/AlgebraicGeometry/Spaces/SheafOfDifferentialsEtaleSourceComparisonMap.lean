module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDifferentialsTriangle
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleSourceLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMapEtale
import StacksCore.Tactic.StacksAttribute

/-!
# The étale-source localization of Stacks 04CU is the comparison map of Stacks 04CX

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `a : U ⟶ X` be
étale.  Stacks 04CU identifies the restriction of `Ω_{X/Y}` to the small étale site of `U` with
the sheaf of differentials of the composite,

`a^*Ω_{X/Y} ≅ Ω_{U/Y}`,

and `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleSourceLocalizationIso` is that
isomorphism.  Separately, Stacks 04CX attaches to the commutative square with top edge `a`,
right edge `f`, left edge `a ≫ f` and bottom edge the identity of `Y` a canonical comparison map
`c_a : a^*Ω_{X/Y} ⟶ Ω_{U/Y}` between the *same* two modules, namely
`AlgebraicGeometry.Space.pullbackDifferentialsMap`.

This file proves that the two are the **same morphism**, and hence that `c_a` is invertible for
an étale `a`.  Nothing in this development connected them before: the identification of 04CU was
built from the corepresentation
`AlgebraicGeometry.Space.derivationEtalePullbackEquiv` of the `Y`-derivations of `𝒪_U` by
`a^*Ω_{X/Y}`, while `c_a` is pinned by `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap`, and
an isomorphism of objects transports no property of a map between them.  Several places in the
tree consequently carry the invertibility of `c_a` as a hypothesis — see the *What this
discharges* section below.

## Main results

* `AlgebraicGeometry.Space.pullbackDifferentialsMap_eq_etaleSourceLocalizationHom`: therefore it
  *is* the comparison map, by the uniqueness clause
  `AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap` of Stacks 04CX.
* `AlgebraicGeometry.Space.isIso_pullbackDifferentialsMap_of_isEtale`: **for an étale `a` the
  comparison map `c_a : a^*Ω_{X/Y} ⟶ Ω_{U/Y}` of Stacks 04CX is an isomorphism.**

## The proof

The forward map of the étale-source localization has the characterizing property of the
comparison map of Stacks 04CX: that is
`AlgebraicGeometry.Space.isSheafOfDifferentialsMap_etaleSourceLocalizationHom` of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsMapEtale.lean`.  The uniqueness clause
`AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap` of Stacks 04CX then identifies the two
maps.

## What this discharges

The invertibility of `c_a` along an étale morphism is carried as an explicit hypothesis in at
least these places, each of which can now drop it:

* `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceSplitting.lean:394` and `:435`, as
  `[IsIso (pullbackDifferentialsMap B S hS φ b)]`, which that file's docstring calls "the
  étale-localization clause of Stacks 04CU … a different tag";
* `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceFormallySmoothSplitting.lean:231`, in
  the same shape;
* `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsDescent.lean:170` and `:203`, as
  `[IsIso cs]` and `[IsIso ct]` for the comparison maps of the two étale projections of a
  descent datum.

## References

* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), the étale localization
  of the sheaf of differentials.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square and its characterization.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the morphism of small
  étale ringed topoi of a morphism of algebraic spaces and the two forms of its structure map.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), inverse and direct
  image of modules and their adjunction.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y U : AlgebraicSpaces B S hS}

/-! ### Stacks 04CU for the comparison map of Stacks 04CX -/

/-- **The comparison map of Stacks 04CX along an étale morphism is the étale-source
localization of Stacks 04CU.**  The two morphisms `a^*Ω_{X/Y} ⟶ Ω_{U/Y}` both have the
characterizing property of Stacks 04CX, and at most one morphism does, by
`AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap`. -/
@[stacks 04CU "the étale-source localization is the comparison map of Stacks 04CX"]
theorem pullbackDifferentialsMap_eq_etaleSourceLocalizationHom (a : U ⟶ X)
    (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) :
    pullbackDifferentialsMap B S hS a f = etaleSourceLocalizationHom B S hS a ha f :=
  eq_of_isSheafOfDifferentialsMap B S hS a f (a ≫ f)
    (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS a f (a ≫ f) (𝟙 Y)
      (by simp))
    (isSheafOfDifferentialsMap_etaleSourceLocalizationHom B S hS a ha f)

/-- **Stacks 04CU, the étale-source localization as an invertibility.**  For an étale
`a : U ⟶ X` and any `f : X ⟶ Y`, the comparison map
`c_a : a^*Ω_{X/Y} ⟶ Ω_{U/Y}` of Stacks 04CX — the first map
`AlgebraicGeometry.Space.pullbackDifferentialsMap` of the transitivity sequence of Stacks 05Z8
at the square over the identity of `Y` — is an isomorphism.

It is the forward map of
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleSourceLocalizationIso`. -/
@[stacks 04CU "the comparison map `a^*Ω_{X/Y} ⟶ Ω_{U/Y}` along an étale `a` is invertible"]
theorem isIso_pullbackDifferentialsMap_of_isEtale (a : U ⟶ X) (ha : IsEtale B S hS a.hom)
    (f : X ⟶ Y) : IsIso (pullbackDifferentialsMap B S hS a f) := by
  rw [pullbackDifferentialsMap_eq_etaleSourceLocalizationHom B S hS a ha f]
  exact ⟨etaleSourceLocalizationInv B S hS a ha f,
    (sheafOfDifferentialsEtaleSourceLocalizationIso B S hS a ha f).hom_inv_id,
    (sheafOfDifferentialsEtaleSourceLocalizationIso B S hS a ha f).inv_hom_id⟩

end AlgebraicGeometry.Space

end
