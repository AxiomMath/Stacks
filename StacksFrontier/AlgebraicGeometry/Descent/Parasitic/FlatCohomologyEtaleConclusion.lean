module

public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologyEtaleClauseTwo
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologyGeneralBase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleAssociatedSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelianSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomology
public import StacksCore.Tactic.StacksAttribute

/-!
# The conclusion of [Stacks, Tag 0756] at `τ = étale`

Let `B` be a big fppf site, `S` a scheme below its cutoff and `𝒢` a sheaf of `𝒪`-modules on
`(Sch/S)_fppf` satisfying the two hypotheses of [Stacks, Tag 0756] at `τ = étale`:

1. `𝒢|_{S_étale}` is quasi-coherent on the small étale site of `S`, and
2. for every object of `(Sch/S)_fppf` flat and locally of finite presentation over `S`, with
   structure morphism `g : X ⟶ S`, the canonical map `ε_g^*(𝒢|_{S_étale}) ⟶ 𝒢|_{X_étale}` of
   `AlgebraicGeometry.BigFppfOver.etaleClause2Map` is an isomorphism; this is the adjoint
   transpose of the restriction map `𝒢|_{S_étale} ⟶ ε_{g,*}(𝒢|_{X_étale})` by
   `AlgebraicGeometry.BigFppfOver.etaleClause2Map_eq_homEquiv_symm`.

This file proves the conclusion of the tag at `τ = étale`: for **every** object `U` of
`(Sch/S)_fppf` flat and locally of finite presentation over `S`, with scheme `X`, and every `p`,

```
H^p(U, 𝒢)  ≅  H^p(U, 𝒢|_{U_étale}).
```

## The route

The `τ = Zariski` half of the tag,
`AlgebraicGeometry.BigFppfOver.flatSmallSiteCohomologyAddEquiv`, is proved, and
`StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologyEtaleClauseOne` and
`…FlatCohomologyEtaleClauseTwo` feed it the two étale hypotheses: clause (1) at `τ = étale`
gives clause (1) at `τ = Zariski` by
`AlgebraicGeometry.BigFppfOver.isQuasicoherent_restrictModule_of_isQuasicoherentOnSite` and
clause (2) at `τ = étale` gives clause (2) at `τ = Zariski` by
`AlgebraicGeometry.BigFppfOver.isIso_zariskiClause2Map_of_isIso_etaleClause2Map`.  That yields

```
H^p(U, 𝒢)  ≅  H^p(X, 𝒢|_{X_Zar}).
```

What remains is to replace the right-hand side by the étale one.  Three steps:

* [Stacks, Tag 03DW] clause (2), the small étale link,
  `AlgebraicGeometry.smallEtaleQuasiCoherentSiteCohomologyAddEquiv`, identifies
  `H^p(X, 𝒢|_{X_Zar})` with the cohomology of the associated sheaf on **Mathlib's** small étale
  site of `X`.
* That site and the size-bounded small étale site of [Stacks, Tag 021B] — the one
  `AlgebraicGeometry.BigFppfOver.smallEtaleToBasePushforward` lands on — have the same abelian
  sheaves, by `AlgebraicGeometry.SmallEtale.sheafEquiv`, and
  `AlgebraicGeometry.BigFppfOver.boundedSmallEtaleCohomologyAddEquiv` promotes that to an
  identification of cohomology.  The engine is
  `Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence`, whose `Ext` universe
  is the universe of the objects of the sites, so the comparison is read at the `Ext` universe of
  the modules by `Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv` on both sides.
* On the bounded site the associated sheaf **is** the one of [Stacks, Tag 03DS] read there:
  `AlgebraicGeometry.BigFppfOver.boundedSmallEtaleAssociatedSheaf_eq` is an equality of abelian
  sheaves, both being the pullback-sections presheaf restricted along the canonical functor to
  the schemes over `X`.  And that sheaf is `𝒢|_{X_étale}` itself: clause (1) at `τ = étale`
  passes from `S` to `X` by
  `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_objSmallEtaleRestrict`, so the counit
  `(𝒢|_{X_étale}|_{X_Zar})^a ⟶ 𝒢|_{X_étale}` is invertible by
  `AlgebraicGeometry.SmallEtale.isIso_counit`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.boundedSmallEtaleCohomologyAddEquiv`: **the cohomology of an
  abelian sheaf on Mathlib's small étale site of `X` agrees with the cohomology of its
  restriction to the size-bounded small étale site of [Stacks, Tag 021B].**
* `AlgebraicGeometry.BigFppfOver.objSmallEtaleRestrictAssociatedSheafIso`: on the bounded site
  the associated sheaf of `𝒢|_{X_Zar}` is `𝒢|_{X_étale}`, under the two clauses.
* `AlgebraicGeometry.BigFppfOver.flatSmallEtaleSiteCohomologyAddEquiv`: **the conclusion of
  [Stacks, Tag 0756] at `τ = étale`.**

## Implementation notes

`AlgebraicGeometry.BigFppfOver.boundedSmallEtaleAssociatedSheaf_eq` is `rfl`: the two sheaves
have the same underlying presheaf because
`AlgebraicGeometry.SmallEtale.toEtaleSite` followed by the forgetful functor of Mathlib's small
étale site *is* `AlgebraicGeometry.SmallEtale.toOver`, and restriction of sheaves along a
continuous functor is restriction of presheaves.

## References

* [Stacks Project, Tag 0756](https://stacks.math.columbia.edu/tag/0756)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfOver

attribute [local instance]
  Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite

variable (B : BigFppfSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-! ### The two presentations of the small étale site have the same cohomology -/

/-- The embedding of the size-bounded small étale site of `X` in Mathlib's is continuous,
restated for the big étale site carried by a big fppf site so that instance search sees the size
hypothesis in the form `B.Contains X`. -/
public instance isContinuous_toEtaleSiteOfBigFppf :
    (SmallEtale.toEtaleSite B.toBigEtaleSite X hX).IsContinuous
      (SmallEtale.topology B.toBigEtaleSite X hX) (Scheme.smallEtaleTopology X) :=
  SmallEtale.isContinuous_toEtaleSite B.toBigEtaleSite X hX

/-- The same embedding is cocontinuous, restated in the same spelling. -/
public instance isCocontinuous_toEtaleSiteOfBigFppf :
    (SmallEtale.toEtaleSite B.toBigEtaleSite X hX).IsCocontinuous
      (SmallEtale.topology B.toBigEtaleSite X hX) (Scheme.smallEtaleTopology X) :=
  SmallEtale.isCocontinuous_toEtaleSite B.toBigEtaleSite X hX

/-- The `Ext`-groups of abelian sheaves on the size-bounded small étale site of `X`, with
coefficients at the morphism universe `u` of the site, also live in the universe `u + 1` of the
objects of the site, which is the universe of the morphisms of the sheaf category.  This is the
`Ext` universe `Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence` works at;
`Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite` supplies the other one. -/
public instance hasExt_succ_sheaf_boundedSmallEtale :
    HasExt.{u + 1} (Sheaf (SmallEtale.topology B.toBigEtaleSite X hX) AddCommGrpCat.{u}) :=
  HasExt.standard _

/-- The comma categories of the embedding of the bounded small étale site in Mathlib's have
limits of abelian groups at the universe of the morphisms of the sites: the bounded site is
essentially small there, by [Stacks, Tag 021B]. -/
public instance hasLimitsOfShape_structuredArrow_toEtaleSite_addCommGrp
    (Y : (X.Etale)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow Y (SmallEtale.toEtaleSite B.toBigEtaleSite X hX).op)
      AddCommGrpCat.{u} :=
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- Restriction of abelian sheaves along the embedding of the bounded small étale site of `X` in
Mathlib's is an equivalence: the embedding exhibits a dense subsite, by
`AlgebraicGeometry.SmallEtale.sheafEquiv`. -/
public instance isEquivalence_sheafPushforward_toEtaleSite :
    ((SmallEtale.toEtaleSite B.toBigEtaleSite X hX).sheafPushforwardContinuous AddCommGrpCat.{u}
      (SmallEtale.topology B.toBigEtaleSite X hX) (Scheme.smallEtaleTopology X)).IsEquivalence :=
  (SmallEtale.sheafEquiv B.toBigEtaleSite X hX AddCommGrpCat.{u}).isEquivalence_inverse

attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt in
/-- **The cohomology of the two presentations of the small étale site of `X` agrees.**  For every
abelian sheaf `F` on Mathlib's small étale site of `X` and every `p`,

```
H^p(X_étale, F)  ≅  H^p(X_étale^{bounded}, F|_{X_étale^{bounded}}),
```

the right-hand side being the cohomology of the size-bounded small étale site of
[Stacks, Tag 021B] cut out of the big étale site carried by `B`.

The embedding of the bounded site in Mathlib's is a dense subsite, so restriction of abelian
sheaves is an equivalence and
`Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence` applies; its `Ext`
universe is the universe `u + 1` of the objects of the two sites, and
`Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv` reads the comparison at the universe
`u` of the morphisms, which is where the cohomology of sheaves of modules is taken. -/
public def boundedSmallEtaleCohomologyAddEquiv
    (F : Sheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u}) (p : ℕ) :
    Sheaf.H.{u} F p ≃+
      Sheaf.H.{u} (((SmallEtale.toEtaleSite B.toBigEtaleSite X hX).sheafPushforwardContinuous
        AddCommGrpCat.{u} (SmallEtale.topology B.toBigEtaleSite X hX)
        (Scheme.smallEtaleTopology X)).obj F) p :=
  (Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv.{u, u + 1}).trans
    ((((Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence.{u, u, u + 1}
            (SmallEtale.topology B.toBigEtaleSite X hX) (Scheme.smallEtaleTopology X)
            (SmallEtale.toEtaleSite B.toBigEtaleSite X hX) p).app
          F).symm.addCommGroupIsoToAddEquiv).trans
      Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv.{u + 1, u})

/-! ### The associated sheaf on the bounded small étale site -/

/-- **The associated sheaf of [Stacks, Tag 03DS] on the bounded small étale site is the
restriction of the one on Mathlib's.**  Both are the pullback-sections presheaf
`(f : T → X) ↦ Γ(T, f^*𝓕)` restricted along the canonical functor to the schemes over `X`, and
the embedding of the bounded site in Mathlib's followed by that functor *is* the canonical
functor of the bounded site. -/
public theorem boundedSmallEtaleAssociatedSheaf_eq (F : X.Modules) [F.IsQuasicoherent] :
    ((SmallEtale.toEtaleSite B.toBigEtaleSite X hX).sheafPushforwardContinuous AddCommGrpCat.{u}
        (SmallEtale.topology B.toBigEtaleSite X hX) (Scheme.smallEtaleTopology X)).obj
        (_root_.AlgebraicGeometry.smallEtaleAssociatedSheaf X F) =
      (SheafOfModules.toSheaf (SmallEtale.structureSheaf B.toBigEtaleSite X hX)).obj
        (smallEtaleAssociatedSheaf B X hX F) :=
  rfl

end AlgebraicGeometry.BigFppfOver

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (G : SheafOfModules.{u} (structureSheaf B S hS))

/-- **`(𝒢|_{X_Zar})^a` is `𝒢|_{X_étale}`**, for `X` the scheme of an object `T` of the big fppf
site, under clause (1) of [Stacks, Tag 0756] at `τ = étale` and clause (2) at `T`.

Clause (1) passes from `S` to `X` by
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_objSmallEtaleRestrict`, so the counit of the
associated-module adjunction of the small étale site of `X` is invertible at `𝒢|_{X_étale}` by
`AlgebraicGeometry.SmallEtale.isIso_counit`; and the restriction of `𝒢|_{X_étale}` to `X_Zar` is
`𝒢|_{X_Zar}` by `AlgebraicGeometry.BigFppfOver.smallEtaleToBasePushforwardCompIso`. -/
public def objSmallEtaleRestrictAssociatedSheafIso (T : BigFppfOver B S hS)
    (h : ((smallEtaleToBasePushforward B S hS .fppf).obj G).IsQuasicoherentOnSite)
    (h2 : IsIso (etaleClause2Map B S hS T G)) :
    (SmallEtale.associatedModule B.toBigEtaleSite (objScheme B S hS T)
          (contains_objScheme B S hS T)).obj (objZariskiRestrict B S hS T G) ≅
      objSmallEtaleRestrict B S hS T G :=
  let hqc := isQuasicoherentOnSite_objSmallEtaleRestrict B S hS T G h h2
  let : IsIso ((SmallEtale.associatedModuleAdjunction B.toBigEtaleSite (objScheme B S hS T)
      (contains_objScheme B S hS T)).counit.app (objSmallEtaleRestrict B S hS T G)) :=
    SmallEtale.isIso_counit B.toBigEtaleSite (objScheme B S hS T)
      (contains_objScheme B S hS T) _ hqc
      (SmallEtale.isQuasicoherent_restrictModule B.toBigEtaleSite (objScheme B S hS T)
        (contains_objScheme B S hS T) _ hqc)
  (SmallEtale.associatedModule B.toBigEtaleSite (objScheme B S hS T)
        (contains_objScheme B S hS T)).mapIso
      ((smallEtaleToBasePushforwardCompIso B (objScheme B S hS T)
        (contains_objScheme B S hS T) .fppf).app ((objRestrict B S hS T).obj G)).symm ≪≫
    asIso ((SmallEtale.associatedModuleAdjunction B.toBigEtaleSite (objScheme B S hS T)
      (contains_objScheme B S hS T)).counit.app (objSmallEtaleRestrict B S hS T G))

/-! ### The conclusion -/

section Conclusion

attribute [local instance] Stacks.Topology.hasExt_sheafOpens
  Stacks.Topology.enoughInjectives_sheafOpens
  Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite

variable (U : BigFppfOver B S hS)
  (h : ((smallEtaleToBasePushforward B S hS .fppf).obj G).IsQuasicoherentOnSite)
  (hcl2 : ∀ Z : BigFppfOver B S hS, Flat ((Over.post B.inclusion).obj Z).hom →
    LocallyOfFinitePresentation ((Over.post B.inclusion).obj Z).hom →
    IsIso (etaleClause2Map B S hS Z G))
  (hU₁ : Flat ((Over.post B.inclusion).obj U).hom)
  (hU₂ : LocallyOfFinitePresentation ((Over.post B.inclusion).obj U).hom)

attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt in
/-- **The conclusion of [Stacks, Tag 0756] at `τ = étale`.**  Let `B` be a big fppf site, `S` a
scheme below its cutoff and `𝒢` a sheaf of `𝒪`-modules on `(Sch/S)_fppf` such that

1. `𝒢|_{S_étale}` is quasi-coherent on the small étale site of `S`, and
2. for every object of `(Sch/S)_fppf` flat and locally of finite presentation over `S`, with
   structure morphism `g : X ⟶ S`, the canonical map `ε_g^*(𝒢|_{S_étale}) ⟶ 𝒢|_{X_étale}` of
   `AlgebraicGeometry.BigFppfOver.etaleClause2Map` is an isomorphism; this is the adjoint
   transpose of the restriction map `𝒢|_{S_étale} ⟶ ε_{g,*}(𝒢|_{X_étale})` by
   `AlgebraicGeometry.BigFppfOver.etaleClause2Map_eq_homEquiv_symm`.

Then for **every** object `U` of `(Sch/S)_fppf` flat and locally of finite presentation over `S`,
with scheme `X`, and every `p`,

```
H^p(U, 𝒢)  ≅  H^p(U, 𝒢|_{U_étale}).
```

The left-hand side is global cohomology of `𝒢|_{(Sch/X)_fppf}` on the big fppf site of `X`,
which is the reading of cohomology over an object that
`AlgebraicGeometry.BigFppfOver.flatSmallSiteCohomologyAddEquiv` fixes at `τ = Zariski`; the
right-hand side is the cohomology of the size-bounded small étale site of `X` of
[Stacks, Tag 021B] with values in the restriction of `𝒢` along
`a_X : ((Sch/X)_fppf, 𝒪) ⟶ (X_étale, 𝒪)`.

The attribute records the topology: this is the tag at `τ = étale`.  See
`AlgebraicGeometry.BigFppfOver.flatSmallSiteCohomologyAddEquiv` for the tag at
`τ = Zariski`. -/
@[stacks 0756 "étale topology"]
public def flatSmallEtaleSiteCohomologyAddEquiv (p : ℕ) :
    Sheaf.H.{u} ((SheafOfModules.toSheaf (structureSheaf B (objScheme B S hS U)
        (contains_objScheme B S hS U))).obj ((objRestrict B S hS U).obj G)) p ≃+
      Sheaf.H.{u} ((SheafOfModules.toSheaf (SmallEtale.structureSheaf B.toBigEtaleSite
        (objScheme B S hS U) (contains_objScheme B S hS U))).obj
          (objSmallEtaleRestrict B S hS U G)) p :=
  let hqc := isQuasicoherent_restrictModule_of_isQuasicoherentOnSite B S hS G h
  let hcl2Z : ∀ Z : BigFppfOver B S hS, Flat ((Over.post B.inclusion).obj Z).hom →
      LocallyOfFinitePresentation ((Over.post B.inclusion).obj Z).hom →
      IsIso (zariskiClause2Map B S hS Z G) :=
    fun Z hZ₁ hZ₂ => isIso_zariskiClause2Map_of_isIso_etaleClause2Map B S hS Z G h
      (hcl2 Z hZ₁ hZ₂)
  let : SheafOfModules.IsQuasicoherent
      (R := (objScheme B S hS U).ringCatSheaf) (objZariskiRestrict B S hS U G) :=
    isQuasicoherent_objZariskiRestrict B S hS U G hqc (hcl2Z U hU₁ hU₂)
  (flatSmallSiteCohomologyAddEquiv B S hS G U hqc hcl2Z hU₁ hU₂ p).trans
    ((smallEtaleQuasiCoherentSiteCohomologyAddEquiv (objScheme B S hS U)
          (objZariskiRestrict B S hS U G) p).trans
      ((boundedSmallEtaleCohomologyAddEquiv B (objScheme B S hS U)
            (contains_objScheme B S hS U)
            (_root_.AlgebraicGeometry.smallEtaleAssociatedSheaf (objScheme B S hS U)
              (objZariskiRestrict B S hS U G)) p).trans
        ((Sheaf.functorH.{u} (SmallEtale.topology B.toBigEtaleSite (objScheme B S hS U)
              (contains_objScheme B S hS U)) p).mapIso
            (eqToIso (boundedSmallEtaleAssociatedSheaf_eq B (objScheme B S hS U)
                (contains_objScheme B S hS U) (objZariskiRestrict B S hS U G)) ≪≫
              (SheafOfModules.toSheaf (SmallEtale.structureSheaf B.toBigEtaleSite
                  (objScheme B S hS U) (contains_objScheme B S hS U))).mapIso
                ((smallEtaleAssociatedModuleIsoSheaf B (objScheme B S hS U)
                    (contains_objScheme B S hS U)
                    (objZariskiRestrict B S hS U G)).symm ≪≫
                  objSmallEtaleRestrictAssociatedSheafIso B S hS G U h
                    (hcl2 U hU₁ hU₂)))).addCommGroupIsoToAddEquiv))

end Conclusion

end AlgebraicGeometry.BigFppfOver

end
