module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison square of a morphism of affine schemes

[Stacks, Tag 08DW] part (2) reads: *if `X` and `Y` are affine and `f : Y ⟶ X` is given by the
ring map `A ⟶ B`, then the square*

  `D(A) ⟶ D_QCoh(𝒪_X)`, `D(B) ⟶ D_QCoh(𝒪_Y)`, `- ⊗ᴸ_A B` on the left and `Lf^*` on the right,

*commutes.* `AlgebraicGeometry.affinePullbackComparison` of
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/AffinePullbackComparison.lean` is that square
for `X = Spec A` and `Y = Spec B` on the nose. This file carries it to a morphism of **arbitrary
affine schemes**, which is the hypothesis the source actually makes: for an affine `X` the
horizontal functor `D(Γ(X, ⊤)) ⥤ D(𝒪_X)` is derived sheafification followed by restriction along
the canonical isomorphism `X ≅ Spec Γ(X, ⊤)`, and that is
`AlgebraicGeometry.affineSchemeDerivedTilde`.

Nothing is assumed of `f` beyond affineness of its source and target. In particular this is *not*
`AlgebraicGeometry.Scheme.Modules.affineModelPullbackDerivedIso` of
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/DualizingComplexSyntomicDescent.lean`,
which is the conjugate of the *degreewise* Tag 01I9 and so is restricted to a flat morphism; here
the left-hand functor is genuinely derived.

## Main definitions

* `AlgebraicGeometry.affineSchemeDerivedTilde` — for an affine scheme `X`, the horizontal functor
  `D(Γ(X, ⊤)) ⥤ D(𝒪_X)` of the square.
* `AlgebraicGeometry.affineSchemePullbackComparison` — **[Stacks, Tag 08DW] part (2) for a
  morphism of arbitrary affine schemes.**

## Implementation notes

The transport is the composition formula `Stacks.Duality.derivedPullbackCompIso` applied twice,
around the naturality square `g ≫ X.isoSpec.hom = Y.isoSpec.hom ≫ Spec.map g.appTop` of
`AlgebraicGeometry.Scheme.isoSpec_hom_naturality`. Both applications are needed: the two
isomorphisms `X ≅ Spec Γ(X, ⊤)` and `Y ≅ Spec Γ(Y, ⊤)` enter the two horizontal arrows, and `Lf^*`
does not commute with either on the nose.

The model of the three derived categories is the locally small one, as it is for
`AlgebraicGeometry.affinePullbackComparison` and for `Stacks.Duality.derivedPullback`; see the
implementation notes of those files.

## References

* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The horizontal functor `D(Γ(X, ⊤)) ⥤ D(𝒪_X)` of the affine comparison square**, for an
affine scheme `X`: derived sheafification on `Spec Γ(X, ⊤)` followed by derived pullback along the
canonical isomorphism `X ≅ Spec Γ(X, ⊤)`.

For `X = Spec R` this is `(tilde.functor R).mapDerivedCategory` up to the canonical isomorphism,
which is the functor `AlgebraicGeometry.affinePullbackComparison` is stated with. -/
abbrev affineSchemeDerivedTilde (X : Scheme.{u}) [IsAffine X] :
    DerivedCategory (ModuleCat.{u} Γ(X, ⊤)) ⥤ DerivedCategory X.Modules :=
  (tilde.functor Γ(X, ⊤)).mapDerivedCategory ⋙ Stacks.Duality.derivedPullback X.isoSpec.hom

/-- **[Stacks, Tag 08DW] part (2) for a morphism of arbitrary affine schemes.** Let `g : Y ⟶ X` be
a morphism of affine schemes, given by the ring map `g.appTop : Γ(X, ⊤) ⟶ Γ(Y, ⊤)`. Then the
square

  `D(Γ(X, ⊤)) ⟶ D(𝒪_X)`, `D(Γ(Y, ⊤)) ⟶ D(𝒪_Y)`, `- ⊗ᴸ Γ(Y, ⊤)` on the left and `Lg^*` on the
  right,

commutes: `Lg^*` of the complex of sheaves associated to an object of `D(Γ(X, ⊤))` is the complex
of sheaves associated to its derived extension of scalars.

This is `AlgebraicGeometry.affinePullbackComparison` conjugated by the two canonical isomorphisms
`X ≅ Spec Γ(X, ⊤)` and `Y ≅ Spec Γ(Y, ⊤)`, the composition formula
`Stacks.Duality.derivedPullbackCompIso` crossing the resulting two triangles. -/
@[stacks 08DW "part (2) for a morphism of arbitrary affine schemes"]
def affineSchemePullbackComparison {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : Y ⟶ X) :
    affineSchemeDerivedTilde X ⋙ Stacks.Duality.derivedPullback g ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (CommRingCat.Hom.hom g.appTop)).functor ⋙
        affineSchemeDerivedTilde Y :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Stacks.Duality.derivedPullbackCompIso g X.isoSpec.hom) ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (congrArg
      (fun q : Y ⟶ Spec Γ(X, ⊤) => Stacks.Duality.derivedPullback q)
      (Scheme.isoSpec_hom_naturality g).symm)) ≪≫
    Functor.isoWhiskerLeft _
      (Stacks.Duality.derivedPullbackCompIso Y.isoSpec.hom (Spec.map g.appTop)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (affinePullbackComparison Γ(X, ⊤) Γ(Y, ⊤) g.appTop) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry

end
