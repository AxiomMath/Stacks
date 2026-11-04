module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePullbackComparison
public import StacksFrontier.Homology.KFlat.Flat

/-!
# Flat base change for a complex of modules on an affine scheme

Let `f : R ⟶ S` be a homomorphism of commutative rings and let `P^•` be a **K-flat** complex of
`R`-modules — for instance a bounded-above complex of projective, or merely flat, modules. Then
derived pullback along `Spec f` of the degreewise sheafification of `P^•` is computed by the
degreewise sheafification of the degreewise extension of scalars,

  `L(Spec f)^*(P̃^•) ≅ (S ⊗_R P^•)~`,

with no derived tensor product left on the right-hand side.

This is the K-flat case of the affine comparison square of [Stacks, Tag 08DW] part (2). That
square, `AlgebraicGeometry.affinePullbackComparison`, carries derived extension of scalars
`- ⊗ᴸ_R S` on its right-hand side; a K-flat complex is exactly one on which the comparison from
derived to degreewise extension of scalars is invertible, so on such a complex the square
degenerates to the statement above. The two inputs are therefore Tag 08DW part (2) and the
field `comparison_isIso_of_kFlat` of
`CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars`.

## Main results

* `CochainComplex.KFlat.kFlat_of_projective` — a bounded-above complex of projective modules is
  K-flat; the projective case of [Stacks, Tag 064K].
* `AlgebraicGeometry.derivedPullbackTildeExtendScalarsIso` — **the flat base change
  isomorphism** for a K-flat complex, together with
  `AlgebraicGeometry.derivedPullbackTildeExtendScalarsIso_hom` reading off its underlying
  morphism.
* `AlgebraicGeometry.derivedPullbackTildeExtendScalarsIso_naturality` — the isomorphism is
  natural in the complex, along maps between K-flat complexes.
* `AlgebraicGeometry.derivedPullbackTildeExtendScalarsIsoOfProjective` — the same for a
  bounded-above complex of projective modules, with K-flatness discharged.
* `AlgebraicGeometry.derivedPullbackTildeExtendScalarsIsoTwoTerm` — the two-term case, for a
  complex of projective modules concentrated in degrees `-1` and `0`.

## Implementation notes

*The model of the derived categories.* As in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/AffinePullbackComparison.lean`, everything
here is at the preferred locally small model: `ModuleCat.hasDerivedCategory` on the source and
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` on the target, both global instances
collected in `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`. No declaration here
mentions `CategoryTheory.HasDerivedCategory.standard`; the pin is inherited from
`Stacks.Duality.derivedPullback` and from `affinePullbackComparison`, not chosen.

*Two spellings of the right-hand side, and why the proofs are split.* The target of the derived
extension-of-scalars comparison is
`CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral f`, which is *by
definition* degreewise extension of scalars followed by `DerivedCategory.Q`. The statements
below are written at the unfolded spelling, so that a consumer reads a localised complex of
`S`-modules and never has to know that functor. The passage between the two spellings is a
definitional unfolding of a semireducible `def`, so it is available to the term elaborator but
not to `rw`, `dsimp` or instance synthesis, all of which work at reducible transparency. Hence
the shape of this file: the `IsIso` instance is supplied explicitly rather than synthesised, and
the naturality square is *proved* at the `extensionOfScalarsComplexGeneral` spelling, in
`derivedPullbackTildeExtendScalarsNaturalityAux`, where every tactic step is on type-correct
terms, and only then *stated* at the unfolded spelling. Attempting the tactic proof directly at
the unfolded spelling fails on exactly this point, with `rw` unable to see through the goal.

*The additivity of extension of scalars* is not declared here. `ModuleCat.extendScalars` is a
left adjoint and instance search already finds
`CategoryTheory.Functor.Additive` for it, so no file-local instance is needed.

*Why `IsStrictlyGE` appears in the two-term statement.* K-flatness of a bounded-above complex of
flat modules needs no lower bound, so `derivedPullbackTildeExtendScalarsIsoTwoTerm` could drop
that hypothesis. It is kept because the two-term shape is the one its consumers have — a
presentation `P^{-1} ⟶ P^0` of a module — and a statement in that shape is applied without first
discharging a bound.

## References

* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars

universe u

namespace CochainComplex.KFlat

/-- **A bounded-above complex of projective modules is K-flat.** Projective modules are flat, so
this is the projective case of [Stacks, Tag 064K], `CochainComplex.KFlat.kFlat_of_flat`. -/
theorem kFlat_of_projective {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) [P.IsStrictlyLE n]
    [∀ i : ℤ, Module.Projective R (P.X i)] :
    CochainComplex.KFlat.{u, u} P :=
  have : ∀ i : ℤ, Module.Flat R (P.X i) := fun _ => Module.Flat.of_projective
  CochainComplex.KFlat.kFlat_of_flat.{u, u} P n

end CochainComplex.KFlat

namespace AlgebraicGeometry

variable {R S : CommRingCat.{u}} (f : R ⟶ S)


/-- **Flat base change for a complex: Stacks 08DW part (2) on a K-flat complex.** For a
homomorphism `f : R ⟶ S` of commutative rings and a K-flat complex `P^•` of `R`-modules, derived
pullback along `Spec f` of the degreewise sheafification of `P^•` is the degreewise
sheafification of the degreewise extension of scalars:

  `L(Spec f)^*(P̃^•) ≅ (S ⊗_R P^•)~`.

It is the affine comparison square `AlgebraicGeometry.affinePullbackComparison` followed by the
comparison from derived to degreewise extension of scalars, which is invertible precisely
because `P^•` is K-flat. -/
def derivedPullbackTildeExtendScalarsIso (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) :
    (Stacks.Duality.derivedPullback (Spec.map f)).obj
        ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≅
      (tilde.functor S).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (((ModuleCat.extendScalars f.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) :=
  (affinePullbackComparison R S f).app (DerivedCategory.Q.obj P) ≪≫
    (tilde.functor S).mapDerivedCategory.mapIso
      (@asIso _ _ _ _ ((totalDerivedExtensionScalars.{u, u, u} f.hom).comparison.app P)
        ((totalDerivedExtensionScalars.{u, u, u} f.hom).comparison_isIso_of_kFlat P hP))

/-- The morphism underlying flat base change: the affine comparison square of Stacks 08DW part
(2) at the localisation of `P^•`, followed by the sheafification of the derived-to-degreewise
extension-of-scalars comparison. The type of
`AlgebraicGeometry.derivedPullbackTildeExtendScalarsIso` does not determine it, so this equation
is part of the statement and not a convenience. -/
theorem derivedPullbackTildeExtendScalarsIso_hom (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) :
    (derivedPullbackTildeExtendScalarsIso f P hP).hom =
      (affinePullbackComparison R S f).hom.app (DerivedCategory.Q.obj P) ≫
        (tilde.functor S).mapDerivedCategory.map
          ((totalDerivedExtensionScalars.{u, u, u} f.hom).comparison.app P) :=
  rfl

/-- The naturality square of flat base change, at the
`CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral` spelling of the
right-hand side: both factors are components of natural transformations, so the square is the
naturality of the affine comparison square followed by that of the derived-to-degreewise
comparison. Stated here rather than only in the unfolded form of
`derivedPullbackTildeExtendScalarsIso_naturality` because the tactic proof needs its terms to be
type-correct at reducible transparency; see the implementation notes. -/
private theorem derivedPullbackTildeExtendScalarsNaturalityAux
    (P P' : CochainComplex (ModuleCat.{u} R) ℤ) (g : P ⟶ P') :
    ((tilde.functor R).mapDerivedCategory ⋙
            Stacks.Duality.derivedPullback (Spec.map f)).map (DerivedCategory.Q.map g) ≫
        ((affinePullbackComparison R S f).hom.app (DerivedCategory.Q.obj P') ≫
          (tilde.functor S).mapDerivedCategory.map
            ((totalDerivedExtensionScalars.{u, u, u} f.hom).comparison.app P')) =
      ((affinePullbackComparison R S f).hom.app (DerivedCategory.Q.obj P) ≫
          (tilde.functor S).mapDerivedCategory.map
            ((totalDerivedExtensionScalars.{u, u, u} f.hom).comparison.app P)) ≫
        (tilde.functor S).mapDerivedCategory.map
          ((extensionOfScalarsComplexGeneral.{u, u, u} f.hom).map g) := by
  rw [← Category.assoc, (affinePullbackComparison R S f).hom.naturality, Category.assoc,
    Category.assoc, Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact congrArg (tilde.functor S).mapDerivedCategory.map
    ((totalDerivedExtensionScalars.{u, u, u} f.hom).comparison.naturality g)

/-- **Flat base change for a complex is natural in the complex.** Both factors of
`AlgebraicGeometry.derivedPullbackTildeExtendScalarsIso` are components of natural
transformations — the affine comparison square of Stacks 08DW part (2) and the comparison from
derived to degreewise extension of scalars — so the isomorphism commutes with any map of K-flat
complexes of `R`-modules. -/
theorem derivedPullbackTildeExtendScalarsIso_naturality
    (P P' : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) (hP' : CochainComplex.KFlat.{u, u} P')
    (g : P ⟶ P') :
    (Stacks.Duality.derivedPullback (Spec.map f)).map
          ((tilde.functor R).mapDerivedCategory.map (DerivedCategory.Q.map g)) ≫
        (derivedPullbackTildeExtendScalarsIso f P' hP').hom =
      (derivedPullbackTildeExtendScalarsIso f P hP).hom ≫
        (tilde.functor S).mapDerivedCategory.map (DerivedCategory.Q.map
          (((ModuleCat.extendScalars f.hom).mapHomologicalComplex (ComplexShape.up ℤ)).map g)) :=
  derivedPullbackTildeExtendScalarsNaturalityAux f P P' g

/-- **Flat base change for a bounded-above complex of projective modules.** K-flatness is
discharged by `CochainComplex.KFlat.kFlat_of_projective`. -/
def derivedPullbackTildeExtendScalarsIsoOfProjective (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℤ) [P.IsStrictlyLE n] [∀ i : ℤ, Module.Projective R (P.X i)] :
    (Stacks.Duality.derivedPullback (Spec.map f)).obj
        ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≅
      (tilde.functor S).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (((ModuleCat.extendScalars f.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) :=
  derivedPullbackTildeExtendScalarsIso f P (CochainComplex.KFlat.kFlat_of_projective P n)

/-- **Flat base change for a two-term complex of projective modules.** A presentation
`P^{-1} ⟶ P^0` by projective `R`-modules is K-flat, so the derived pullback along `Spec f` of its
degreewise sheafification is the degreewise sheafification of `S ⊗_R P^{-1} ⟶ S ⊗_R P^0`. -/
def derivedPullbackTildeExtendScalarsIsoTwoTerm (P : CochainComplex (ModuleCat.{u} R) ℤ)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0] [∀ i : ℤ, Module.Projective R (P.X i)] :
    (Stacks.Duality.derivedPullback (Spec.map f)).obj
        ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≅
      (tilde.functor S).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (((ModuleCat.extendScalars f.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) :=
  derivedPullbackTildeExtendScalarsIsoOfProjective f P 0

end AlgebraicGeometry

end
