module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSmallEtaleAffineVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SmallEtaleModuleUliftPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.GlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheaf
public import StacksFrontier.CategoryTheory.Sites.PullbackSheafComposeNatIso

/-!
# Inverse image and global sections of the sheaf `ℱ_ρ`

Let `X` be a connected scheme with a geometric point, `Λ` a finite ring, and `ρ ↦ ℱ_ρ` the
functor `AlgebraicGeometry.representationSheaf` from finite `Λ`-modules with a continuous action
of `π₁(X, x)` to sheaves of `Λ`-modules on `X_étale`. This file computes the two operations the
Trace Formula chapter applies to `ℱ_ρ` in Section 03VJ:

* inverse image along a morphism `g : Y ⟶ X` of connected schemes is restriction of the action
  along `π₁(Y, y) ⟶ π₁(X, g(y))` (Tag 0DV6): `g⁻¹ℱ_ρ ≅ ℱ_{ρ ∘ g_*}`, naturally in `ρ`;
* global sections are the invariants: `Γ(X, ℱ_ρ) ≅ M^{π₁(X, x)}`, naturally in `ρ`.

Together they give `H⁰(Y, g⁻¹ℱ_ρ) ≅ M^{π₁(Y, y)}`, the invariants of `M` under the image of
`π₁(Y, y)`. For `Y = X_{k̄}` this is the first identification of Tag 03VL.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sheafEquivSheafComposeIso` — the equivalence between the sheaves
  of the two presentations of the small étale site commutes with a change of coefficients.
* `AlgebraicGeometry.representationSheafIsoEtaleSite` — `ℱ_ρ` read through Tag 0DV5 (3) on
  Mathlib's small étale site.
* `AlgebraicGeometry.representationSheafPullbackIso` — `g⁻¹ℱ_ρ ≅ ℱ_{ρ ∘ g_*}`.
* `AlgebraicGeometry.representationSheafGlobalSectionsIso` — `Γ(X, ℱ_ρ) ≅ M^{π₁(X, x)}`.
* `AlgebraicGeometry.representationSheafPullbackGlobalSectionsIso` — `Γ(Y, g⁻¹ℱ_ρ) ≅ M^{π₁(Y, y)}`.

## Implementation notes

All isomorphisms are isomorphisms of functors of `ρ`; that is what "functorially in the
representation `ρ`" of Tag 03VL asks for. The coefficients of `ℱ_ρ` are the universe lift of the
coefficients of Tag 0DV5, so the invariants appear lifted by `ModuleCat.uliftFunctor`.

## References

* [Stacks Project, Tag 03VL](https://stacks.math.columbia.edu/tag/03VL)
* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
* [Stacks Project, Tag 0DV6](https://stacks.math.columbia.edu/tag/0DV6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.GroupCohomology

universe u r

namespace AlgebraicGeometry

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type*} [Category* A] {A' : Type*} [Category* A'] (U : A ⥤ A')
  [HasLimitsOfSize.{u, u} A] [HasLimitsOfSize.{u, u} A']
  [(topology B S hS).HasSheafCompose U] [S.smallEtaleTopology.HasSheafCompose U]

/-- **The sheaves of the two presentations of the small étale site, compared through a change of
coefficients.** Restriction along the dense subsite inclusion commutes with postcomposition on
the nose; conjugating that square by the two equivalences `AlgebraicGeometry.SmallEtale.sheafEquiv`
gives the square for their functors. -/
def sheafEquivSheafComposeIso :
    (sheafEquiv B S hS A).functor ⋙ sheafCompose S.smallEtaleTopology U ≅
      sheafCompose (topology B S hS) U ⋙ (sheafEquiv B S hS A').functor :=
  Equivalence.conjugateSquare (sheafEquiv B S hS A).symm (sheafEquiv B S hS A').symm
    (Iso.refl _)

end SmallEtale

section EtaleSite

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1) (Λ : Type r) [Ring Λ] [Finite Λ]

/-- **`ℱ_ρ` through Tag 0DV5 (3) on Mathlib's small étale site.** The sheaf
`AlgebraicGeometry.representationSheaf` is built on the site of Stacks 021B and then moved to
Mathlib's site with lifted coefficients; it is equally the sheaf attached to `ρ` by the dictionary
on Mathlib's site, `AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite`,
with lifted coefficients. -/
def representationSheafIsoEtaleSite :
    representationSheaf B X x Λ ≅
      (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x Λ).inverse ⋙
        ObjectProperty.ι _ ⋙
        sheafCompose X.1.smallEtaleTopology (ModuleCat.uliftFunctor.{r, u + 1} Λ) :=
  letI := Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize.{u, u, r, u + 1} Λ
  letI := Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize.{u, u, r, max (u + 1) r} Λ
  Functor.isoWhiskerLeft ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse ⋙
      ObjectProperty.ι _)
    (SmallEtale.sheafEquivSheafComposeIso B X.1 X.2 (ModuleCat.uliftFunctor.{r, u + 1} Λ)).symm

/-- **Global sections of `ℱ_ρ` are the invariants of `ρ`.** For a connected scheme `X` with a
geometric point `x` and a finite ring `Λ`, `Γ(X, ℱ_ρ) ≅ M^{π₁(X, x)}` as `Λ`-modules, naturally in
the finite `Λ`-module `M` with its continuous action `ρ` (the invariants lifted to the coefficient
universe of `ℱ_ρ`). -/
def representationSheafGlobalSectionsIso :
    representationSheaf B X x Λ ⋙ Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, r} Λ X.1 ≅
      finiteTypeContinuousModuleInvariants Λ (EtaleFundamentalGroup X.1 x) ⋙
        ModuleCat.uliftFunctor.{r, u + 1} Λ :=
  letI := Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize.{u, u, r, max (u + 1) r} Λ
  Functor.isoWhiskerLeft (representationSheaf B X x Λ)
      (Sheaf.ΓNatIsoSheafSections X.1.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
        (SmallEtale.isTerminal_toEtaleSite_final B X.1 X.2)) ≪≫
    Functor.isoWhiskerLeft ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse ⋙
        ObjectProperty.ι _ ⋙
        sheafCompose (SmallEtale.topology B X.1 X.2) (ModuleCat.uliftFunctor.{r, u + 1} Λ))
      (Functor.isoWhiskerRight
        (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{max (u + 1) r} Λ)).unitIso
        ((sheafSections (SmallEtale.topology B X.1 X.2) (ModuleCat.{max (u + 1) r} Λ)).obj
          (op (SmallEtale.final B X.1 X.2)))).symm ≪≫
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse
        (finiteTypeLocallyConstantModuleSheafSectionsIsoInvariants B X x Λ).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).counitIso
          _ ≪≫ Functor.leftUnitor _)
      (ModuleCat.uliftFunctor.{r, u + 1} Λ) : _)

end EtaleSite

section Pullback

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (g : Y ⟶ X) [ConnectedSpace X.1]
  [ConnectedSpace Y.1] (Λ : Type r) [Ring Λ] [Finite Λ] (y : GeometricPoint Y.1)

/-- Inverse image along a morphism of schemes commutes with raising the module universe, as an
isomorphism of functors on the sheaves of `Λ`-modules of Mathlib's small étale site. -/
def etaleModuleInverseImageUliftIso :
    sheafCompose X.1.smallEtaleTopology (ModuleCat.uliftFunctor.{r, u + 1} Λ) ⋙
        Stacks.EtaleCohomology.etaleModuleInverseImage.{u, r} Λ g.hom ≅
      (Stacks.EtaleCohomology.smallEtaleBaseChange g.hom).sheafPullback (ModuleCat.{u + 1} Λ)
          X.1.smallEtaleTopology Y.1.smallEtaleTopology ⋙
        sheafCompose Y.1.smallEtaleTopology (ModuleCat.uliftFunctor.{r, u + 1} Λ) :=
  letI : ∀ Z : (Y.1.Etale)ᵒᵖ, PreservesColimitsOfShape
      (CostructuredArrow (Stacks.EtaleCohomology.smallEtaleBaseChange g.hom).op Z)
      (ModuleCat.uliftFunctor.{r, u + 1} Λ) :=
    preservesColimitsOfShape_costructuredArrow_moduleUliftFunctor.{r} g.hom Λ
  (Stacks.EtaleCohomology.smallEtaleBaseChange g.hom).sheafPullbackSheafComposeNatIso
    (ModuleCat.{u + 1} Λ) X.1.smallEtaleTopology Y.1.smallEtaleTopology
    (ModuleCat.uliftFunctor.{r, u + 1} Λ)

/-- **Inverse image of `ℱ_ρ` is `ℱ` of the restricted representation** (Tag 0DV6). For a
morphism `g : Y ⟶ X` of connected schemes and a geometric point `y` of `Y`, the inverse image
`g⁻¹ℱ_ρ` is, naturally in `ρ`, the sheaf attached to `ρ` restricted along the induced
homomorphism `π₁(Y, y) ⟶ π₁(X, g(y))`. -/
def representationSheafPullbackIso :
    representationSheaf B X (y.map g.hom) Λ ⋙
        Stacks.EtaleCohomology.etaleModuleInverseImage.{u, r} Λ g.hom ≅
      finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap g.hom y) ⋙
        representationSheaf B Y y Λ :=
  Functor.isoWhiskerRight (representationSheafIsoEtaleSite B X (y.map g.hom) Λ) _ ≪≫
    Functor.isoWhiskerLeft ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X
        (y.map g.hom) Λ).inverse ⋙ ObjectProperty.ι _)
      (etaleModuleInverseImageUliftIso B g Λ ≪≫
        Functor.isoWhiskerRight (etaleSiteSheafPullbackModuleIsoSheafPullback B g Λ).symm _) ≪≫
    Functor.isoWhiskerRight (Equivalence.conjugateSquare
        (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map g.hom) Λ)
        (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ)
        (Classical.choice
          (nonempty_finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite_pullbackIso
            B g Λ y)))
      (ObjectProperty.ι _ ⋙
        sheafCompose Y.1.smallEtaleTopology (ModuleCat.uliftFunctor.{r, u + 1} Λ)) ≪≫
    Functor.isoWhiskerLeft (finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap g.hom y))
      (representationSheafIsoEtaleSite B Y y Λ).symm

/-- **`H⁰(Y, g⁻¹ℱ_ρ) = M^{π₁(Y, y)}`.** For a morphism `g : Y ⟶ X` of connected schemes and a
geometric point `y` of `Y`, the global sections of the inverse image of `ℱ_ρ` are, naturally in
`ρ` and as `Λ`-modules, the invariants of `M` under `π₁(Y, y)` acting through
`π₁(Y, y) ⟶ π₁(X, g(y))`. -/
def representationSheafPullbackGlobalSectionsIso :
    representationSheaf B X (y.map g.hom) Λ ⋙
        Stacks.EtaleCohomology.etaleModuleInverseImage.{u, r} Λ g.hom ⋙
        Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, r} Λ Y.1 ≅
      finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap g.hom y) ⋙
        finiteTypeContinuousModuleInvariants Λ (EtaleFundamentalGroup Y.1 y) ⋙
        ModuleCat.uliftFunctor.{r, u + 1} Λ :=
  Functor.isoWhiskerRight (representationSheafPullbackIso B g Λ y) _ ≪≫
    Functor.isoWhiskerLeft (finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap g.hom y))
      (representationSheafGlobalSectionsIso B Y y Λ)

end Pullback

section Geometric

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (Λ : Type r) [Ring Λ]
  [Finite Λ] {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) (K : Type u) [Field K]
  [Algebra k K] (hK : B.Contains (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
  [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)]
  (y : GeometricPoint (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))

/-- The base change `X_K = X ×_k K`, as an object of a big étale site containing it. -/
abbrev fieldBaseChangeObj : B.Scheme := ⟨Stacks.Frobenius.fieldBaseChange (Over.mk f) K, hK⟩

/-- The projection `X_K ⟶ X`, as a morphism of a big étale site containing `X_K`. -/
abbrev fieldBaseChangeObjProj : fieldBaseChangeObj B X f K hK ⟶ X :=
  ObjectProperty.homMk (Stacks.Frobenius.fieldBaseChangeProj (Over.mk f) K)

/-- **`H⁰(X_K, ℱ_ρ) = M^{π₁(X_K, y)}`, functorially in `ρ`.** For a connected scheme `X` over a
field `k`, an extension `K` of `k` with `X_K = X ×_k K` connected, a geometric point `y` of
`X_K` and a finite ring `Λ`, the global sections of the restriction to `X_K` of the sheaf `ℱ_ρ`
attached to a finite `Λ`-module `M` with continuous action `ρ` of `π₁(X, y)` are the invariants
of `M` under the geometric fundamental group `π₁(X_K, y)`, acting through
`π₁(X_K, y) ⟶ π₁(X, y)`. This holds as an isomorphism of functors of `(M, ρ)`.

For `K = k^{sep}` and `X` a geometrically connected smooth curve this is the first identification
of Tag 03VL. The big étale site `B` presenting `ℱ_ρ` is required to contain `X_K`, because the
dictionary of Tag 0DV5 on `X_K` and its compatibility Tag 0DV6 with the projection are read
inside one big étale site. -/
def geometricGlobalSectionsIsoInvariants :
    geometricRepresentationSheaf B X (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ f K ⋙
        Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, r} Λ
          (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) ≅
      finiteTypeContinuousModuleRes Λ
          (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f K hK).hom y) ⋙
        finiteTypeContinuousModuleInvariants Λ
          (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y) ⋙
        ModuleCat.uliftFunctor.{r, u + 1} Λ :=
  representationSheafPullbackGlobalSectionsIso B (fieldBaseChangeObjProj B X f K hK) Λ y

end Geometric

end AlgebraicGeometry
