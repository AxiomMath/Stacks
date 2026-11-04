module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineEtaleHomologySheafification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.AdjointExistenceUnbounded

/-!
# The cohomology sheaves of derived upper shriek on the affine étale site

Let `f : X ⟶ Y` be a separated finite type morphism of quasi-compact and quasi-separated
schemes, let `Λ` be a torsion ring and let `K` be an object of the unbounded derived category
`D(Y_étale, Λ)`.  [Stacks, Tag 0GLK] states that the cohomology sheaf `H^n(Rf^! K)`, restricted to
`X_{affine, étale}`, is the sheaf associated to the presheaf
```
U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K[n]).
```

## The object `R(U ⟶ Y)_! Λ`

As in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriekAffineEtale`,
`R(U ⟶ Y)_! Λ` is `Rf_!((j_U)_! Λ)`, functorially in `U`: by [Stacks, Tags 0F7J, 0GKM] this is
the source's object, and the transition maps induced by the morphisms of the site are the maps
`Rf_!(Tr_j)` of the discussion preceding the lemma.

## Main results

* `Stacks.EtaleCohomology.affineEtaleHomPresheafUnboundedAdjIso`: the adjunction step of the
  source's proof, as an isomorphism of presheaves, which is the verification the source omits.
* `Stacks.EtaleCohomology.derivedUpperShriekHomologyAffineEtaleOfAdjunction`: the statement for
  any right adjoint of `Rf_!`.

## References

* [Stacks Project, Tag 0GLK](https://stacks.math.columbia.edu/tag/0GLK)
* [Stacks Project, Tag 0G2C](https://stacks.math.columbia.edu/tag/0G2C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Injectives.KInjectiveResolution

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

/-- **The object `R(U ⟶ Y)_! Λ` of Stacks Tag 0GLK on the unbounded derived category**,
functorially in the object `U` of the small affine étale site of `X`: the derived lower shriek of
`f` applied to `(j_U)_! Λ`. -/
abbrev affineEtaleConstantLowerShriekUnbounded {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ] :
    X.AffineEtale ⥤ DerivedCategory (EtaleModules.{u, r} Λ Y) :=
  affineEtaleConstantUnbounded.{u, r} Λ X ⋙ derivedLowerShriekUnbounded.{u, r} f j Λ

/-- The presheaf `U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K[n])` of Stacks Tag 0GLK on the small affine étale site
of `X`, for `K` in the unbounded derived category `D(Y_étale, Λ)`. -/
abbrev affineEtaleLowerShriekHomPresheafUnbounded {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ]
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y)) (n : ℤ) :
    X.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) r + 1} :=
  (affineEtaleConstantLowerShriekUnbounded.{u, r} f j Λ).op ⋙
    preadditiveYoneda.obj (K⟦n⟧) ⋙ AddCommGrpCat.uliftFunctor.{max (u + 1) r + 1}

/-- The unbounded derived lower shriek is additive, being a composite of triangulated functors. -/
theorem derivedLowerShriekUnbounded_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ] :
    (derivedLowerShriekUnbounded.{u, r} f j Λ).Additive := by
  let := commShiftOfIsRightDerivedFunctor (etaleModuleExtensionByZero.{u, r} Λ j.immersion) _
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j.immersion)
  have := isTriangulated_of_isRightDerivedFunctor
    (etaleModuleExtensionByZero.{u, r} Λ j.immersion) _
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j.immersion)
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, r} Λ j.toBase
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, r} Λ j.toBase
  exact inferInstanceAs ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion ⋙
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase).Additive)

/-- **The verification the source omits, on the unbounded derived category.**  For a right
adjoint `G` of `Rf_!`, the presheaves `U ↦ Hom_X((j_U)_! Λ, G(K)[n])` and
`U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K[n])` agree as presheaves:
```
Hom_X((j_U)_! Λ, G(K)[n]) = Hom_X((j_U)_! Λ, G(K[n])) = Hom_Y(Rf_!((j_U)_! Λ), K[n]),
```
naturally in `U`, because the hom-equivalence of an adjunction is natural in both variables. -/
def affineEtaleHomPresheafUnboundedAdjIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ]
    {G : DerivedCategory (EtaleModules.{u, r} Λ Y) ⥤ DerivedCategory (EtaleModules.{u, r} Λ X)}
    (adj : derivedLowerShriekUnbounded.{u, r} f j Λ ⊣ G)
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y)) (n : ℤ) :
    affineEtaleHomPresheafUnbounded.{u, r} Λ X (G.obj K) n ≅
      affineEtaleLowerShriekHomPresheafUnbounded.{u, r} f j Λ K n :=
  letI := derivedLowerShriekUnboundedCommShift.{u, r} Λ j
  haveI := derivedLowerShriekUnbounded_additive.{u, r} f j Λ
  letI := adj.rightAdjointCommShift ℤ
  Functor.isoWhiskerLeft (affineEtaleConstantUnbounded.{u, r} Λ X).op
    (Functor.isoWhiskerRight
      (preadditiveYoneda.mapIso ((G.commShiftIso n).app K).symm)
      AddCommGrpCat.uliftFunctor.{max (u + 1) r + 1}) ≪≫
  Functor.isoWhiskerLeft (affineEtaleConstantUnbounded.{u, r} Λ X).op
    (adj.compPreadditiveYonedaIso.app (K⟦n⟧))

/-- **Stacks Tag 0GLK for any right adjoint of `Rf_!`.**  Let `G` be a right adjoint of the
derived lower shriek `Rf_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` on unbounded derived categories, and
let `K` be an object of `D(Y_étale, Λ)`.  Then the cohomology sheaf `H^n(G K)`, restricted to the
small affine étale site of `X`, is the sheaf associated to `U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K[n])`.

The source's argument: `affineEtaleHomPresheafUnboundedAdjIso` is the adjunction step together
with the naturality in `U` the source omits, and
`affineEtaleHomPresheafSheafificationIso` identifies the sheafification of
`U ↦ Hom_X((j_U)_! Λ, M[n]) = H^n(U, M)` with `H^n(M)`. -/
def derivedUpperShriekHomologyAffineEtaleOfAdjunction {X Y : Scheme.{u}} {f : X ⟶ Y}
    (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ]
    {G : DerivedCategory (EtaleModules.{u, r} Λ Y) ⥤ DerivedCategory (EtaleModules.{u, r} Λ X)}
    (adj : derivedLowerShriekUnbounded.{u, r} f j Λ ⊣ G)
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y)) (n : ℤ) :
    (presheafToSheaf (AffineEtale.topology X) AddCommGrpCat.{max (u + 1) r + 1}).obj
        (affineEtaleLowerShriekHomPresheafUnbounded.{u, r} f j Λ K n) ≅
      (affineEtaleAbelianRestriction.{u, r} Λ X).obj
        ((DerivedCategory.homologyFunctor _ n).obj (G.obj K)) :=
  (presheafToSheaf (AffineEtale.topology X) AddCommGrpCat.{max (u + 1) r + 1}).mapIso
      (affineEtaleHomPresheafUnboundedAdjIso.{u, r} j Λ adj K n).symm ≪≫
    affineEtaleHomPresheafSheafificationIso (G.obj K) n

end Stacks.EtaleCohomology
