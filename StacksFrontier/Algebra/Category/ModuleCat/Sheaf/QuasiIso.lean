module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.QuasiIsomorphismLocality

/-!
# Quasi-isomorphy of a complex of sheaves of modules is the same question in abelian sheaves

Let `R` be a sheaf of rings on a site `(C, J)`. **A morphism of complexes of `R`-modules is a
quasi-isomorphism exactly when the underlying morphism of complexes of abelian sheaves is**: the
forgetful functor `SheafOfModules.toSheaf R` is exact, hence preserves homology, and it reflects
isomorphisms.

This is the sheaf analogue of
`PresheafOfModules.quasiIso_of_forall_quasiIso_evaluation` of
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.QuasiIso`, which runs the same argument for
presheaves through `PresheafOfModules.toPresheaf`.

## Main results

* `Stacks.SheafOfModules.preservesHomology_toSheaf`: the forgetful functor to abelian sheaves
  preserves homology.
* `Stacks.SheafOfModules.quasiIso_toSheaf_map_iff`: **the abelian reading of a morphism of
  complexes of sheaves of modules is a quasi-isomorphism if and only if the module reading is.**
* `Stacks.SheafOfModules.quasiIso_of_quasiIso_toSheaf_map`: the direction that is not formal, the
  functor reflecting isomorphisms.
* `Stacks.SheafOfModules.quasiIso_toSheaf_map_of_coversTop`: **quasi-isomorphy in abelian sheaves
  is local on the site, for a morphism coming from sheaves of modules.**

## What this is for

A statement about a complex of sheaves of modules whose consumer is a morphism of complexes of
*abelian* sheaves — the relative de Rham complex is the case at hand, its differential being
linear only over the base
(`AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMap` is a morphism of abelian sheaves for
that reason) — may be proved in whichever of the two categories is convenient, and read in the
other by `quasiIso_toSheaf_map_iff`. In particular the locality of quasi-isomorphy,
`Stacks.SheafOfModules.quasiIso_of_coversTop`, which is stated for complexes of modules, is
available for the abelian reading of such a morphism.

**What it does not supply.** The hypothesis of `quasiIso_toSheaf_map_iff` is that the morphism of
abelian-sheaf complexes *is* the image of a morphism of complexes of `R`-modules. A morphism of
abelian-sheaf complexes with no `R`-module refinement — the direct image of a complex of modules
along a morphism of spaces, for instance, which is a module sheaf only over a different sheaf of
rings — is not covered, and neither is any locality statement for one.

## Implementation notes

Exactness of `SheafOfModules.toSheaf R` is `PreservesFiniteLimits`, a Mathlib instance of
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Limits.lean`, together with
`Stacks.SheafOfModules.toSheaf_preservesFiniteColimits`, which is a `theorem` and not an
instance, so `preservesHomology_toSheaf` is a `theorem` too and is introduced by its consumers
with `letI`, exactly as `Stacks.SheafOfModules.preservesHomology_overFunctor` is.

`ReflectsIsomorphisms` needs nothing: it is the Mathlib instance of
`Mathlib/Algebra/Category/ModuleCat/Presheaf/Sheafification.lean`. This is what distinguishes the
situation from the stalk criterion
`AlgebraicGeometry.SheafOfModules.quasiIso_iff_forall_stalk_quasiIso`, which had to be proved by
hand because a single stalk functor does not reflect isomorphisms.

## References

* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- **The forgetful functor from sheaves of `R`-modules to abelian sheaves preserves homology.**
It preserves finite limits, which is a Mathlib instance, and finite colimits, which is
`Stacks.SheafOfModules.toSheaf_preservesFiniteColimits`; an additive functor between abelian
categories preserving both is exact, and an exact functor preserves homology. -/
theorem preservesHomology_toSheaf :
    (_root_.SheafOfModules.toSheaf.{w} R).PreservesHomology :=
  let := toSheaf_preservesFiniteColimits.{w} R
  Functor.preservesHomologyOfExact _

variable {R}

/-- **A morphism of complexes of sheaves of `R`-modules is a quasi-isomorphism if and only if its
abelian reading is.** The forgetful functor to abelian sheaves preserves homology and reflects
isomorphisms, so quasi-isomorphy is the same question on either side.

This is what makes a statement about complexes of abelian sheaves and the corresponding statement
about complexes of sheaves of modules interchangeable, for a morphism that has a module
refinement. -/
theorem quasiIso_toSheaf_map_iff {ι : Type*} {cs : ComplexShape ι}
    {K L : HomologicalComplex (_root_.SheafOfModules.{w} R) cs} (φ : K ⟶ L) :
    QuasiIso (((_root_.SheafOfModules.toSheaf.{w} R).mapHomologicalComplex cs).map φ) ↔
      QuasiIso φ :=
  let := preservesHomology_toSheaf.{w} R
  HomologicalComplex.quasiIso_map_iff_of_preservesHomology φ
    (_root_.SheafOfModules.toSheaf.{w} R)

/-- **A morphism of complexes of sheaves of modules whose abelian reading is a quasi-isomorphism
is one.** This is the direction of `Stacks.SheafOfModules.quasiIso_toSheaf_map_iff` that is not
formal: it is the forgetful functor reflecting isomorphisms. The converse direction is
`HomologicalComplex.quasiIso_map_of_preservesHomology`. -/
theorem quasiIso_of_quasiIso_toSheaf_map {ι : Type*} {cs : ComplexShape ι}
    {K L : HomologicalComplex (_root_.SheafOfModules.{w} R) cs} (φ : K ⟶ L)
    (hφ : QuasiIso (((_root_.SheafOfModules.toSheaf.{w} R).mapHomologicalComplex cs).map φ)) :
    QuasiIso φ :=
  (quasiIso_toSheaf_map_iff φ).1 hφ

/-- **Quasi-isomorphy in abelian sheaves is local on the site, for a morphism coming from sheaves
of modules.** Let `V : ι → C` be a family of objects covering the final object. The abelian
reading of a morphism of cochain complexes of `R`-modules whose degreewise restriction to the
slice over each `V i` is a quasi-isomorphism is a quasi-isomorphism.

This is `Stacks.SheafOfModules.quasiIso_of_coversTop` read through
`Stacks.SheafOfModules.quasiIso_toSheaf_map_iff`. The hypothesis is still a condition on the
morphism of complexes of *modules*: what is transported is the conclusion. -/
theorem quasiIso_toSheaf_map_of_coversTop [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {K L : CochainComplex (_root_.SheafOfModules.{w} R) ℤ} {ι : Type*} {V : ι → C}
    (hV : J.CoversTop V) (φ : K ⟶ L)
    (hφ : ∀ i, QuasiIso (((_root_.SheafOfModules.overFunctor.{w} R (V i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ)) :
    QuasiIso (((_root_.SheafOfModules.toSheaf.{w} R).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ) :=
  let := preservesHomology_toSheaf.{w} R
  have := quasiIso_of_coversTop hV φ hφ
  inferInstance

end Stacks.SheafOfModules

end
