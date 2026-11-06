module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.SheafCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalizationPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectCohomologyLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EnoughPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleProjection
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteSheafCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.ModuleCohomologyAbelianComparison

/-!
# Étale cohomology over an object and the small étale site (Stacks 075F)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `x` an object of `𝒳` lying over
a scheme `U`. The second assertion of **Stacks 075F** is that, for `F` an abelian sheaf or a sheaf
of `O_𝒳`-modules on `𝒳_{étale}`,

`H^n_{étale}(x, F) = H^n(U_{étale}, F|_{U_{étale}})`,

where `U_{étale}` is the small étale site of `U` and `F|_{U_{étale}}` the restriction of
Stacks 06W1. As in the source this follows from the first assertion,
`H^n_{étale}(x, F) = H^n((Sch/U)_{étale}, x^{-1}F)`
(`AlgebraicGeometry.Stack.cohomologyOverObjectIso`,
`AlgebraicGeometry.Stack.moduleCohomologyOverObjectIso`), together with the comparison of big and
small étale cohomology of Stacks 03YX.

## Main definitions

* `AlgebraicGeometry.Stack.smallEtaleInclusionOver`: the small étale site of a scheme `T`
  included into the schemes over `T` of the big fppf site `B`, through the big étale site
  carried by `B` (Stacks 03FF).
* `AlgebraicGeometry.Stack.objectSmallEtaleRestriction`: the restriction `F|_{U_{étale}}` of
  Stacks 06W1, as a functor on abelian sheaves.
* `AlgebraicGeometry.Stack.objectSmallEtaleRing`: the structure sheaf of rings of `U_{étale}`.
* `AlgebraicGeometry.Stack.objectSmallEtaleModuleRestriction`: the restriction `F|_{U_{étale}}`
  of a sheaf of `O_𝒳`-modules, a module over `objectSmallEtaleRing`.

## Main results

* `AlgebraicGeometry.Stack.bigSmallEtaleCohomologyIso`: Stacks 03YX, étale case, with the
  coefficients in any universe containing the schemes.
* `AlgebraicGeometry.Stack.objectInverseImageSmallEtaleSheafIso`: the restriction of `x^{-1}F`
  to `U_{étale}` is the restriction `F|_{U_{étale}}` of Stacks 06W1.
* `AlgebraicGeometry.Stack.objectSmallEtaleModuleRestrictionToSheafIso`: the underlying abelian
  sheaf of the restriction of a sheaf of modules is the restriction of its underlying abelian
  sheaf.
* `AlgebraicGeometry.Stack.etaleCohomologyOverObjectIso`: **Stacks 075F**, the étale comparison
  for abelian sheaves.
* `AlgebraicGeometry.Stack.etaleModuleCohomologyOverObjectIso`: **Stacks 075F**, the étale
  comparison for sheaves of `O_𝒳`-modules.
* `AlgebraicGeometry.Stack.cohomologyOverObjectComparison`: **Stacks 075F** in full, for each of
  the five topologies of the source: the comparison with the big site of `U`, for abelian sheaves
  and for sheaves of `O_𝒳`-modules, and, for the étale topology, the comparison with the small
  étale site of `U`, for both kinds of sheaves.

## Implementation notes

The big étale site carried by `B` is `AlgebraicGeometry.BigFppfSite.toBigEtaleSite`; it has the
same underlying category of schemes as `B`, and its topology is the big étale topology
`B.etaleTopology` of the common category (`AlgebraicGeometry.BigFppfSite.toBigEtaleSite_topology`),
so the big étale site of `U` is the slice of `B.etaleTopology` at `U`, which is the site of the
first assertion of the source at `τ = étale`. Stacks 03YX is then
`Stacks.Cohomology.BiggerSite.sheafCohomologyIso` (Stacks 03YU) at the inclusion of the small
étale site, with the coefficients in the universe `max v w (u + 1)` of the first assertion; the
version `AlgebraicGeometry.bigSmallEtaleSheafCohomologyIso` of the library has its coefficients in
the universe `u + 1` of the schemes and does not apply.

For sheaves of modules, cohomology is computed in the category of sheaves of modules. Restriction
to the small étale site does not preserve injective sheaves of modules (Stacks 0758), so the
comparison passes through abelian sheaves: on the big and on the small étale site of `U`, both of
which have a final object, the cohomology of a sheaf of modules is that of its underlying abelian
sheaf (Stacks 03FD,
`Stacks.Cohomology.ModuleAbelianComparison.moduleFunctorHIsoOfIsTerminal`), and between the
underlying abelian sheaves Stacks 03YX applies.

## References

* [Stacks Project, Tag 075F](https://stacks.math.columbia.edu/tag/075F)
* [Stacks Project, Tag 03YX](https://stacks.math.columbia.edu/tag/03YX)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 06W1](https://stacks.math.columbia.edu/tag/06W1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace Stacks.Cohomology.SiteEquivalence

universe w v₁ u₁ v₂ u₂

section AbelianSheaves

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsDenseSubsite J K] [G.IsEquivalence]
  [∀ Y : Dᵒᵖ, HasLimitsOfShape (StructuredArrow Y G.op) AddCommGrpCat.{max u₁ u₂}]
  [HasSheafify J AddCommGrpCat.{max u₁ u₂}] [HasSheafify K AddCommGrpCat.{max u₁ u₂}]

/-- **The inverse image along an equivalence of sites is precomposition with the inverse.** When
the functor `G` exhibiting `(C, J)` as a dense subsite of `(D, K)` is an equivalence of
categories, the underlying presheaf of the inverse image `g^{-1}F` of an abelian sheaf `F` is
`F ∘ G⁻¹`, naturally in `F`. Both are inverse to restriction along `G`: the isomorphism is the
counit `G⁻¹ ⋙ G ≅ 𝟭` followed by the unit of the equivalence of sheaf categories. -/
def inverseImageCompSheafToPresheafIso :
    inverseImage J K G ⋙ sheafToPresheaf K AddCommGrpCat.{max u₁ u₂} ≅
      sheafToPresheaf J AddCommGrpCat.{max u₁ u₂} ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{max u₁ u₂}).obj G.inv.op :=
  Functor.isoWhiskerLeft (inverseImage J K G ⋙ sheafToPresheaf K AddCommGrpCat.{max u₁ u₂})
      ((Functor.whiskeringLeft _ _ AddCommGrpCat.{max u₁ u₂}).mapIso
        (NatIso.op G.asEquivalence.counitIso)) ≪≫
    Functor.isoWhiskerRight
      (Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{max u₁ u₂}).unitIso.symm
      (sheafToPresheaf J AddCommGrpCat.{max u₁ u₂} ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{max u₁ u₂}).obj G.inv.op)

end AbelianSheaves

section Modules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsDenseSubsite J K] (R : Sheaf K RingCat.{w})
  [(G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsEquivalence]

/-- **The equivalence of module categories of a dense subsite is compatible with forgetting to
abelian sheaves.** The inverse of restriction of sheaves of `R`-modules, followed by forgetting
the module structure, is forgetting followed by the inverse of restriction of abelian sheaves,
because restriction itself commutes with forgetting on the nose
(`Stacks.DenseSubsiteModules.moduleRestriction_comp_toSheaf`). -/
def moduleRestrictionEquivalenceInverseCompToSheafIso :
    (Stacks.DenseSubsiteModules.moduleRestrictionEquivalence J K G R).inverse ⋙
        SheafOfModules.toSheaf R ≅
      SheafOfModules.toSheaf (Stacks.DenseSubsiteModules.ringRestriction J K G R) ⋙
        (Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{w}).functor :=
  let E := Stacks.DenseSubsiteModules.moduleRestrictionEquivalence J K G R
  let P := G.sheafPushforwardContinuous AddCommGrpCat.{w} J K
  let T := SheafOfModules.toSheaf (Stacks.DenseSubsiteModules.ringRestriction J K G R)
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (E.inverse ⋙ SheafOfModules.toSheaf R) P.asEquivalence.unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _) P.inv ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft E.inverse
      (eqToIso (Stacks.DenseSubsiteModules.moduleRestriction_comp_toSheaf J K G R).symm)) P.inv ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _).symm P.inv ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight E.counitIso T) P.inv ≪≫
    Functor.isoWhiskerRight (Functor.leftUnitor T) P.inv

end Modules

end Stacks.Cohomology.SiteEquivalence

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u})

/-! ### The small étale site of `U` -/

section Etale

variable (T : Scheme.{u}) (hT : B.toBigEtaleSite.Contains T)

/-- The inclusion `T_{étale} ⥤ (Sch/T)` of the small étale site of `T` into the schemes over `T`
of the big fppf site `B`. The big étale site carried by `B` (Stacks 03FF) has the same
underlying category of schemes as `B`, so this is the inclusion
`AlgebraicGeometry.SmallEtale.inclusion` of the small étale site into the big étale site of `T`,
read in the category of schemes of `B`. -/
def smallEtaleInclusionOver :
    SmallEtale B.toBigEtaleSite T hT ⥤ Over (B.obj (X := T) hT) :=
  SmallEtale.inclusion B.toBigEtaleSite T hT

/-- The big étale topology over `T` of the big étale site carried by `B` (Stacks 03FF) is the
localization at `T` of the big étale topology `B.etaleTopology` on the common category of
schemes. -/
theorem bigEtaleOver_topology_toBigEtaleSite :
    BigEtaleOver.topology B.toBigEtaleSite T hT = B.etaleTopology.over (B.obj (X := T) hT) :=
  (bigEtaleOver_topology_eq B.toBigEtaleSite T hT).trans
    (congrArg (fun t => t.over (B.toBigEtaleSite.obj T hT)) B.toBigEtaleSite_topology)

/-- The inclusion of the small étale site of `T` into the big étale site of `T` is continuous. -/
theorem smallEtaleInclusionOver_isContinuous :
    (smallEtaleInclusionOver B T hT).IsContinuous
      (SmallEtale.topology B.toBigEtaleSite T hT) (B.etaleTopology.over (B.obj (X := T) hT)) :=
  bigEtaleOver_topology_toBigEtaleSite B T hT ▸
    (smallEtaleInclusion_isMorphismOfSites B.toBigEtaleSite T hT).toIsContinuous

/-- The inclusion of the small étale site of `T` into the big étale site of `T` is
cocontinuous. -/
theorem smallEtaleInclusionOver_isCocontinuous :
    (smallEtaleInclusionOver B T hT).IsCocontinuous
      (SmallEtale.topology B.toBigEtaleSite T hT) (B.etaleTopology.over (B.obj (X := T) hT)) :=
  bigEtaleOver_topology_toBigEtaleSite B T hT ▸
    smallEtaleInclusion_isCocontinuous B.toBigEtaleSite T hT

/-- **Restriction from the big to the small étale site of `T`**, `F ↦ F|_{T_{étale}}`, for
abelian sheaves with values in an arbitrary universe containing the schemes. -/
noncomputable abbrev smallEtaleSheafRestriction :
    haveI := smallEtaleInclusionOver_isContinuous B T hT
    Sheaf (B.etaleTopology.over (B.obj (X := T) hT)) AddCommGrpCat.{max v (u + 1)} ⥤
      Sheaf (SmallEtale.topology B.toBigEtaleSite T hT) AddCommGrpCat.{max v (u + 1)} :=
  haveI := smallEtaleInclusionOver_isContinuous B T hT
  (smallEtaleInclusionOver B T hT).sheafPushforwardContinuous
    AddCommGrpCat.{max v (u + 1)} (SmallEtale.topology B.toBigEtaleSite T hT)
    (B.etaleTopology.over (B.obj (X := T) hT))

/-- **Stacks 03YX, étale case, with coefficients in any universe containing the schemes.** For
an abelian sheaf `F` on the big étale site of `T`, the cohomology of `F` over `T` is the
cohomology of its restriction `F|_{T_{étale}}` to the small étale site, naturally in `F`.

This is `Stacks.Cohomology.BiggerSite.sheafCohomologyIso` (Stacks 03YU) at the inclusion of the
small étale site: it is continuous and cocontinuous, it carries the final object `T/T` to the
final object, the small étale site has fibre products and equalizers which the inclusion
preserves — so restriction has an exact left adjoint and preserves injective abelian sheaves
(Stacks 0758) — and restriction is right exact. Unlike
`AlgebraicGeometry.bigSmallEtaleSheafCohomologyIso` the coefficients are not tied to the
universe `u + 1` of the schemes. -/
def bigSmallEtaleCohomologyIso (n : ℕ) :
    haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, v}
      (J := B.etaleTopology.over (B.obj (X := T) hT))
    haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, v}
      (J := SmallEtale.topology B.toBigEtaleSite T hT)
    haveI := Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, v}
      (J := B.etaleTopology.over (B.obj (X := T) hT))
    haveI := Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, v}
      (J := SmallEtale.topology B.toBigEtaleSite T hT)
    smallEtaleSheafRestriction.{u, v} B T hT ⋙
        Sheaf.functorH (SmallEtale.topology B.toBigEtaleSite T hT) n ≅
      Sheaf.functorH (B.etaleTopology.over (B.obj (X := T) hT)) n :=
  haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, v}
    (J := B.etaleTopology.over (B.obj (X := T) hT))
  haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, v}
    (J := SmallEtale.topology B.toBigEtaleSite T hT)
  haveI := Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, v}
    (J := B.etaleTopology.over (B.obj (X := T) hT))
  haveI := Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, v}
    (J := SmallEtale.topology B.toBigEtaleSite T hT)
  haveI := Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{u + 1, u, v}
    (J := B.etaleTopology.over (B.obj (X := T) hT))
  haveI := Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{u + 1, u, v}
    (J := SmallEtale.topology B.toBigEtaleSite T hT)
  haveI := smallEtaleInclusionOver_isContinuous B T hT
  haveI := smallEtaleInclusionOver_isCocontinuous B T hT
  haveI : PreservesLimitsOfShape WalkingCospan (smallEtaleInclusionOver B T hT) :=
    (inferInstance : PreservesLimitsOfShape WalkingCospan
      (SmallEtale.inclusion B.toBigEtaleSite T hT))
  haveI : PreservesLimitsOfShape (Discrete PEmpty.{1}) (smallEtaleInclusionOver B T hT) :=
    (preservesLimitsOfShape_pempty_of_preservesTerminal _ : PreservesLimitsOfShape
      (Discrete PEmpty.{1}) (SmallEtale.inclusion B.toBigEtaleSite T hT))
  haveI : PreservesLimitsOfShape (Discrete WalkingPair) (smallEtaleInclusionOver B T hT) :=
    preservesBinaryProducts_of_preservesTerminal_and_pullbacks _
  haveI : PreservesLimitsOfShape WalkingParallelPair (smallEtaleInclusionOver B T hT) :=
    preservesEqualizers_of_preservesPullbacks_and_binaryProducts _
  haveI := Stacks.Cohomology.BiggerSite.preservesFiniteColimits_sheafPushforwardContinuous
    (SmallEtale.topology B.toBigEtaleSite T hT) (B.etaleTopology.over (B.obj (X := T) hT))
    (smallEtaleInclusionOver B T hT) AddCommGrpCat.{max v (u + 1)}
  haveI := Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous
    (SmallEtale.topology B.toBigEtaleSite T hT) (B.etaleTopology.over (B.obj (X := T) hT))
    (smallEtaleInclusionOver B T hT)
  Stacks.Cohomology.BiggerSite.sheafCohomologyIso
    (SmallEtale.topology B.toBigEtaleSite T hT) (B.etaleTopology.over (B.obj (X := T) hT))
    (smallEtaleInclusionOver B T hT) (SmallEtale.finalIsTerminal B.toBigEtaleSite T hT)
    (Over.mkIdTerminal (X := B.obj (X := T) hT)) rfl n

end Etale

/-! ### Étale cohomology over an object -/

section Object

variable (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (x : 𝒳)

/-- The scheme an object of `𝒳` lies over is contained in the big étale site carried by `B`. -/
theorem toBigEtaleSite_contains_left : B.toBigEtaleSite.Contains (p.obj x).left.1 :=
  (p.obj x).left.2

/-- The inverse image `x^{-1}F` of an étale sheaf on `𝒳`, restricted to the small étale site of
`U`, has the underlying presheaf of Stacks 06W1: the restriction `F|_{U_{étale}}`
(`AlgebraicGeometry.Stack.restrictToSmallEtale`), naturally in `F`. -/
def objectInverseImageSmallEtaleIso :
    haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, u + 1}
      (J := (associatedTopology B S hS p B.etaleTopology).over x)
    haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, max v w}
      (J := B.etaleTopology.over (p.obj x).left)
    haveI := isDenseSubsite_overPost B S hS p hp B.etaleTopology x
    haveI := isEquivalence_overPost B S hS p hp x
    objectInverseImage B S hS p B.etaleTopology x ⋙
        smallEtaleSheafRestriction.{u, max v w} B (p.obj x).left.1
          (toBigEtaleSite_contains_left B S hS p x) ⋙
          sheafToPresheaf _ AddCommGrpCat.{max v w (u + 1)} ≅
      sheafToPresheaf (associatedTopology B S hS p B.etaleTopology)
          AddCommGrpCat.{max v w (u + 1)} ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{max v w (u + 1)}).obj
          ((smallEtaleInclusion B B.toBigEtaleSite rfl (p.obj x).left.1
            (toBigEtaleSite_contains_left B S hS p x)).op ⋙
            (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.op ⋙ (Over.forget x).op) :=
  haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, u + 1}
    (J := (associatedTopology B S hS p B.etaleTopology).over x)
  haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, max v w}
    (J := B.etaleTopology.over (p.obj x).left)
  haveI := isDenseSubsite_overPost B S hS p hp B.etaleTopology x
  haveI := isEquivalence_overPost B S hS p hp x
  Functor.isoWhiskerLeft
    ((associatedTopology B S hS p B.etaleTopology).overPullback
      AddCommGrpCat.{max v w (u + 1)} x)
    (Functor.isoWhiskerRight
      (Stacks.Cohomology.SiteEquivalence.inverseImageCompSheafToPresheafIso
        ((associatedTopology B S hS p B.etaleTopology).over x) (B.etaleTopology.over (p.obj x).left)
        (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))))
      ((Functor.whiskeringLeft _ _ AddCommGrpCat.{max v w (u + 1)}).obj
        (smallEtaleInclusionOver B (p.obj x).left.1 (toBigEtaleSite_contains_left B S hS p x)).op))

/-- **The restriction `F|_{U_{étale}}` of Stacks 06W1, as a functor on abelian sheaves.** An
abelian sheaf `F` on `𝒳_{étale}` is sent to the abelian sheaf on the small étale site of the scheme
`U` underlying `x` whose presheaf is `AlgebraicGeometry.Stack.restrictToSmallEtale` — `F`
restricted to the slice at `x` and transported to the schemes étale over `U`. It is a sheaf because
it is isomorphic to the restriction of `x^{-1}F`
(`AlgebraicGeometry.Stack.objectInverseImageSmallEtaleIso`). -/
def objectSmallEtaleRestriction :
    Sheaf (associatedTopology B S hS p B.etaleTopology) AddCommGrpCat.{max v w (u + 1)} ⥤
      Sheaf (SmallEtale.topology B.toBigEtaleSite (p.obj x).left.1
        (toBigEtaleSite_contains_left B S hS p x)) AddCommGrpCat.{max v w (u + 1)} :=
  haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, u + 1}
    (J := (associatedTopology B S hS p B.etaleTopology).over x)
  haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, max v w}
    (J := B.etaleTopology.over (p.obj x).left)
  haveI := isDenseSubsite_overPost B S hS p hp B.etaleTopology x
  haveI := isEquivalence_overPost B S hS p hp x
  { obj F := ⟨restrictToSmallEtale B B.toBigEtaleSite rfl S hS p hp x F.obj,
      (Presheaf.isSheaf_of_iso_iff ((objectInverseImageSmallEtaleIso B S hS p hp x).app F)).1
        ((objectInverseImage B S hS p B.etaleTopology x ⋙
          smallEtaleSheafRestriction.{u, max v w} B (p.obj x).left.1
            (toBigEtaleSite_contains_left B S hS p x)).obj F).property⟩
    map f := ObjectProperty.homMk (Functor.whiskerLeft ((smallEtaleInclusion B B.toBigEtaleSite rfl (p.obj x).left.1
      (toBigEtaleSite_contains_left B S hS p x)).op ⋙
        (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.op ⋙ (Over.forget x).op) f.hom) }

/-- The restriction of `x^{-1}F` to the small étale site of `U` is the restriction
`F|_{U_{étale}}` of Stacks 06W1, naturally in the abelian sheaf `F`. -/
def objectInverseImageSmallEtaleSheafIso :
    haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, u + 1}
      (J := (associatedTopology B S hS p B.etaleTopology).over x)
    haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, max v w}
      (J := B.etaleTopology.over (p.obj x).left)
    haveI := isDenseSubsite_overPost B S hS p hp B.etaleTopology x
    objectInverseImage B S hS p B.etaleTopology x ⋙
        smallEtaleSheafRestriction.{u, max v w} B (p.obj x).left.1
          (toBigEtaleSite_contains_left B S hS p x) ≅
      objectSmallEtaleRestriction B S hS p hp x :=
  haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, u + 1}
    (J := (associatedTopology B S hS p B.etaleTopology).over x)
  haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, max v w}
    (J := B.etaleTopology.over (p.obj x).left)
  haveI := isDenseSubsite_overPost B S hS p hp B.etaleTopology x
  NatIso.ofComponents
    (fun F => (fullyFaithfulSheafToPresheaf _ _).preimageIso
      ((objectInverseImageSmallEtaleIso B S hS p hp x).app F))
    (fun {F G} f => by
      apply (sheafToPresheaf _ _).map_injective
      simp only [Functor.map_comp]
      exact (objectInverseImageSmallEtaleIso B S hS p hp x).hom.naturality f)

/-- **Stacks 075F, the étale comparison, for abelian sheaves.** Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be
a category fibred in groupoids and `x` an object of `𝒳` lying over a scheme `U`. For every
degree `n`

`H^n_{étale}(x, F) = H^n(U_{étale}, F|_{U_{étale}})`,

naturally in the abelian sheaf `F` on `𝒳_{étale}`, where cohomology over `x` is the global
cohomology of the localized site `𝒳_{étale}/x` applied to the restriction of `F`, `U_{étale}` is
the small étale site of `U` for the big étale site carried by `B` (Stacks 03FF), and
`F|_{U_{étale}}` is the restriction of Stacks 06W1
(`AlgebraicGeometry.Stack.objectSmallEtaleRestriction`).

As in the source, this is the first comparison `AlgebraicGeometry.Stack.cohomologyOverObjectIso`
at the étale topology, `H^n_{étale}(x, F) = H^n((Sch/U)_{étale}, x^{-1}F)`, followed by the
comparison of big and small étale cohomology `AlgebraicGeometry.Stack.bigSmallEtaleCohomologyIso`
(Stacks 03YX), the restriction of `x^{-1}F` to `U_{étale}` being `F|_{U_{étale}}`
(`AlgebraicGeometry.Stack.objectInverseImageSmallEtaleSheafIso`). -/
@[sga "4 IV 4.10.6" "6°, special case", sga "4 VII 4.1" "more general"]
def etaleCohomologyOverObjectIso (n : ℕ) :
    haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, u + 1}
      (J := (associatedTopology B S hS p B.etaleTopology).over x)
    haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, max v w}
      (J := SmallEtale.topology B.toBigEtaleSite (p.obj x).left.1
        (toBigEtaleSite_contains_left B S hS p x))
    haveI := Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{max v w, w, u + 1}
      (J := (associatedTopology B S hS p B.etaleTopology).over x)
    haveI := Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, max v w}
      (J := SmallEtale.topology B.toBigEtaleSite (p.obj x).left.1
        (toBigEtaleSite_contains_left B S hS p x))
    (associatedTopology B S hS p B.etaleTopology).overPullback
        AddCommGrpCat.{max v w (u + 1)} x ⋙
        Sheaf.functorH ((associatedTopology B S hS p B.etaleTopology).over x) n ≅
      objectSmallEtaleRestriction B S hS p hp x ⋙
        Sheaf.functorH (SmallEtale.topology B.toBigEtaleSite (p.obj x).left.1
          (toBigEtaleSite_contains_left B S hS p x)) n :=
  haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, max v w}
    (J := B.etaleTopology.over (p.obj x).left)
  haveI := isDenseSubsite_overPost B S hS p hp B.etaleTopology x
  cohomologyOverObjectIso B S hS p hp B.etaleTopology x n ≪≫
    Functor.isoWhiskerLeft _
      (bigSmallEtaleCohomologyIso.{u, max v w} B (p.obj x).left.1
        (toBigEtaleSite_contains_left B S hS p x) n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (objectInverseImageSmallEtaleSheafIso B S hS p hp x) _

/-! ### Sheaves of modules on the étale site -/

/-- The structure sheaf of rings of the small étale site of the scheme `U` underlying `x`: the
restriction to `U_{étale}` of the structure sheaf of the big étale site of `U`, so that its ring
of sections over `V → U` étale is `Γ(V, O_V)` (lifted to the universe of the modules). -/
abbrev objectSmallEtaleRing :
    Sheaf (SmallEtale.topology B.toBigEtaleSite (p.obj x).left.1
      (toBigEtaleSite_contains_left B S hS p x)) RingCat.{max u v w (u + 1)} :=
  haveI := smallEtaleInclusionOver_isContinuous B (p.obj x).left.1
    (toBigEtaleSite_contains_left B S hS p x)
  ((smallEtaleInclusionOver B (p.obj x).left.1
      (toBigEtaleSite_contains_left B S hS p x)).sheafPushforwardContinuous
    RingCat.{max u v w (u + 1)} _ _).obj
    (baseRingStructureSheafLift.{u, v, w} B B.etaleTopology (etaleTopology_le_topology B)
      (p.obj x).left.1 (p.obj x).left.2)

/-- **The restriction `F|_{U_{étale}}` of a sheaf of `O_𝒳`-modules on `𝒳_{étale}`**: the inverse
image `x^{-1}F` (`AlgebraicGeometry.Stack.objectModuleInverseImage`), a module over the
structure sheaf of the big étale site of `U`, restricted to the small étale site of `U`, where
it is a module over `AlgebraicGeometry.Stack.objectSmallEtaleRing`. Its underlying abelian
sheaf is the restriction of the underlying abelian sheaf of `x^{-1}F`. -/
noncomputable abbrev objectSmallEtaleModuleRestriction :
    SheafOfModules.{max u v w (u + 1)}
        (ringStructureSheaf.{u, v, w, u + 1} B S hS p hp B.etaleTopology
          (etaleTopology_le_topology B)) ⥤
      SheafOfModules.{max u v w (u + 1)} (objectSmallEtaleRing B S hS p x) :=
  haveI := smallEtaleInclusionOver_isContinuous B (p.obj x).left.1
    (toBigEtaleSite_contains_left B S hS p x)
  objectModuleInverseImage B S hS p hp B.etaleTopology x (etaleTopology_le_topology B) ⋙
    SheafOfModules.pushforward.{max u v w (u + 1)}
      (F := smallEtaleInclusionOver B (p.obj x).left.1 (toBigEtaleSite_contains_left B S hS p x))
      (𝟙 (objectSmallEtaleRing B S hS p x))

/-- **The underlying abelian sheaf of `F|_{U_{étale}}`** is the restriction of Stacks 06W1 of the
underlying abelian sheaf of `F`, naturally in the sheaf `F` of `O_𝒳`-modules on `𝒳_{étale}`. -/
def objectSmallEtaleModuleRestrictionToSheafIso :
    objectSmallEtaleModuleRestriction B S hS p hp x ⋙
        SheafOfModules.toSheaf (objectSmallEtaleRing B S hS p x) ≅
      SheafOfModules.toSheaf (ringStructureSheaf.{u, v, w, u + 1} B S hS p hp B.etaleTopology
          (etaleTopology_le_topology B)) ⋙
        objectSmallEtaleRestriction B S hS p hp x :=
  haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, u + 1}
    (J := (associatedTopology B S hS p B.etaleTopology).over x)
  haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, max v w}
    (J := B.etaleTopology.over (p.obj x).left)
  haveI := isDenseSubsite_overPost B S hS p hp B.etaleTopology x
  haveI := smallEtaleInclusionOver_isContinuous B (p.obj x).left.1
    (toBigEtaleSite_contains_left B S hS p x)
  let κ := Stacks.Cohomology.SiteEquivalence.moduleRestrictionEquivalenceInverseCompToSheafIso
    ((associatedTopology B S hS p B.etaleTopology).over x) (B.etaleTopology.over (p.obj x).left)
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS)))
    (baseRingStructureSheafLift.{u, v, w} B B.etaleTopology (etaleTopology_le_topology B)
      (p.obj x).left.1 (p.obj x).left.2)
  let R := smallEtaleSheafRestriction.{u, max v w} B (p.obj x).left.1
    (toBigEtaleSite_contains_left B S hS p x)
  let O := ringStructureSheaf.{u, v, w, u + 1} B S hS p hp B.etaleTopology
    (etaleTopology_le_topology B)
  let M := objectModuleInverseImage B S hS p hp B.etaleTopology x (etaleTopology_le_topology B)
  let Pm := SheafOfModules.pushforward.{max u v w (u + 1)}
    (F := smallEtaleInclusionOver B (p.obj x).left.1 (toBigEtaleSite_contains_left B S hS p x))
    (𝟙 (objectSmallEtaleRing B S hS p x))
  let T := SheafOfModules.toSheaf (objectSmallEtaleRing B S hS p x)
  let T' := SheafOfModules.toSheaf (baseRingStructureSheafLift.{u, v, w} B B.etaleTopology
    (etaleTopology_le_topology B) (p.obj x).left.1 (p.obj x).left.2)
  let T'' := SheafOfModules.toSheaf (O.over x)
  let Ov := SheafOfModules.overFunctor O x
  let Pi := (Functor.IsDenseSubsite.sheafEquiv
    ((associatedTopology B S hS p B.etaleTopology).over x) (B.etaleTopology.over (p.obj x).left)
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))) AddCommGrpCat.{max v w (u + 1)}).functor
  let Ei := (Stacks.DenseSubsiteModules.moduleRestrictionEquivalence
    ((associatedTopology B S hS p B.etaleTopology).over x) (B.etaleTopology.over (p.obj x).left)
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS)))
    (baseRingStructureSheafLift.{u, v, w} B B.etaleTopology (etaleTopology_le_topology B)
      (p.obj x).left.1 (p.obj x).left.2)).inverse
  have h₁ : Pm ⋙ T = T' ⋙ R := rfl
  have h₂ : Ov ⋙ T'' = SheafOfModules.toSheaf O ⋙
      (associatedTopology B S hS p B.etaleTopology).overPullback
        AddCommGrpCat.{max v w (u + 1)} x := rfl
  let α₁ : (M ⋙ Pm) ⋙ T ≅ M ⋙ T' ⋙ R :=
    Functor.associator M Pm T ≪≫ Functor.isoWhiskerLeft M (eqToIso h₁)
  let α₂ : M ⋙ T' ⋙ R ≅ (Ov ⋙ Ei ⋙ T') ⋙ R :=
    (Functor.associator M T' R).symm ≪≫
      Functor.isoWhiskerRight (Functor.associator Ov Ei T') R
  let α₃ : (Ov ⋙ Ei ⋙ T') ⋙ R ≅ ((Ov ⋙ T'') ⋙ Pi) ⋙ R :=
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft Ov κ ≪≫
      (Functor.associator Ov T'' Pi).symm) R
  let α₄ : ((Ov ⋙ T'') ⋙ Pi) ⋙ R ≅ SheafOfModules.toSheaf O ⋙
      (((associatedTopology B S hS p B.etaleTopology).overPullback
        AddCommGrpCat.{max v w (u + 1)} x ⋙ Pi) ⋙ R) :=
    Functor.isoWhiskerRight (Functor.isoWhiskerRight (eqToIso h₂) Pi) R ≪≫
      Functor.isoWhiskerRight (Functor.associator _ _ _) R ≪≫ Functor.associator _ _ _
  α₁ ≪≫ α₂ ≪≫ α₃ ≪≫ α₄ ≪≫ Functor.isoWhiskerLeft (SheafOfModules.toSheaf O)
    (objectInverseImageSmallEtaleSheafIso B S hS p hp x)

/-- **Stacks 075F, the étale comparison, for sheaves of `O_𝒳`-modules.** Let
`p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `x` an object of `𝒳` lying over a
scheme `U`. For every degree `n`

`H^n_{étale}(x, F) = H^n(U_{étale}, F|_{U_{étale}})`,

naturally in the sheaf `F` of `O_𝒳`-modules on `𝒳_{étale}`, where both sides are cohomology of
sheaves of modules, `Ext^n` out of the structure sheaf: on the left that of the restriction of
`F` to the slice `𝒳_{étale}/x`, on the right that of the restriction `F|_{U_{étale}}`
(`AlgebraicGeometry.Stack.objectSmallEtaleModuleRestriction`), a module over the structure sheaf
of the small étale site of `U`.

The proof is the source's: the first comparison for modules
(`AlgebraicGeometry.Stack.moduleCohomologyOverObjectIso`) brings the left side to the big étale
site of `U`; there, and on the small étale site, the cohomology of a sheaf of modules is that of
its underlying abelian sheaf (Stacks 03FD,
`Stacks.Cohomology.ModuleAbelianComparison.moduleFunctorHIsoOfIsTerminal`); and between the
underlying abelian sheaves the comparison of big and small étale cohomology
(`AlgebraicGeometry.Stack.bigSmallEtaleCohomologyIso`, Stacks 03YX) applies. -/
def etaleModuleCohomologyOverObjectIso (n : ℕ) :
    SheafOfModules.overFunctor (ringStructureSheaf.{u, v, w, u + 1} B S hS p hp B.etaleTopology
          (etaleTopology_le_topology B)) x ⋙
        Stacks.Cohomology.BiggerSiteModules.moduleFunctorH.{u + 1, w, max v w}
          ((associatedTopology B S hS p B.etaleTopology).over x)
          ((ringStructureSheaf.{u, v, w, u + 1} B S hS p hp B.etaleTopology
            (etaleTopology_le_topology B)).over x) n ≅
      objectSmallEtaleModuleRestriction B S hS p hp x ⋙
        Stacks.Cohomology.BiggerSiteModules.moduleFunctorH.{max v w, u, u + 1}
          (SmallEtale.topology B.toBigEtaleSite (p.obj x).left.1
            (toBigEtaleSite_contains_left B S hS p x))
          (objectSmallEtaleRing B S hS p x) n :=
  haveI := smallEtaleInclusionOver_isContinuous B (p.obj x).left.1
    (toBigEtaleSite_contains_left B S hS p x)
  moduleCohomologyOverObjectIso B S hS p hp B.etaleTopology x (etaleTopology_le_topology B) n ≪≫
    Functor.isoWhiskerLeft
      (objectModuleInverseImage B S hS p hp B.etaleTopology x (etaleTopology_le_topology B))
      (Stacks.Cohomology.ModuleAbelianComparison.moduleFunctorHIsoOfIsTerminal.{max v w, u, u + 1}
          (B.etaleTopology.over (p.obj x).left)
          (baseRingStructureSheafLift.{u, v, w} B B.etaleTopology (etaleTopology_le_topology B)
            (p.obj x).left.1 (p.obj x).left.2) Over.mkIdTerminal n ≪≫
        Functor.isoWhiskerLeft _
          (bigSmallEtaleCohomologyIso.{u, max v w} B (p.obj x).left.1
            (toBigEtaleSite_contains_left B S hS p x) n).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerLeft
          (SheafOfModules.pushforward.{max u v w (u + 1)}
            (F := smallEtaleInclusionOver B (p.obj x).left.1
              (toBigEtaleSite_contains_left B S hS p x))
            (𝟙 (objectSmallEtaleRing B S hS p x)))
          (Stacks.Cohomology.ModuleAbelianComparison.moduleFunctorHIsoOfIsTerminal.{max v w, u,
            u + 1} _ (objectSmallEtaleRing B S hS p x)
            (SmallEtale.finalIsTerminal B.toBigEtaleSite (p.obj x).left.1
              (toBigEtaleSite_contains_left B S hS p x)) n).symm) ≪≫
    (Functor.associator _ _ _).symm

/-! ### Stacks 075F -/

/-- **Stacks 075F.** Let `S` be a scheme, `p : 𝒳 ⥤ (Sch/S)_{fppf}` a category fibred in groupoids,
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`, and `x` an object of `𝒳` lying over the scheme
`U`. For every degree `n`:

* for `F` an abelian sheaf on `𝒳_τ`, `H^n_τ(x, F) = H^n((Sch/U)_τ, x^{-1}F)`;
* for `F` a sheaf of `O_𝒳`-modules on `𝒳_τ`, `H^n_τ(x, F) = H^n((Sch/U)_τ, x^{-1}F)`;
* if `τ = étale`, then also `H^n_{étale}(x, F) = H^n(U_{étale}, F|_{U_{étale}})`, for `F` an
  abelian sheaf and for `F` a sheaf of `O_𝒳`-modules on `𝒳_{étale}`.

Each identification is a natural isomorphism of functors of `F`; they are
`AlgebraicGeometry.Stack.cohomologyOverObjectIso`,
`AlgebraicGeometry.Stack.moduleCohomologyOverObjectIso`,
`AlgebraicGeometry.Stack.etaleCohomologyOverObjectIso` and
`AlgebraicGeometry.Stack.etaleModuleCohomologyOverObjectIso`, the first two of which are stated
there for any topology on the underlying category of schemes (coarser than the fppf topology, for
modules).

The five topologies are `B.baseTopology τ` for `τ : AlgebraicGeometry.SiteKind`. Cohomology over
`x` is the cohomology of the localized site `𝒳_τ/x` of the restriction of `F` (Stacks 03F3); the
cohomology of a sheaf of modules is computed in the category of sheaves of modules, as `Ext` out
of the structure sheaf; `(Sch/U)_τ` is the big `τ`-site of `U`, identified with `𝒳_τ/x` by the
localization equivalence of Stacks 06W0, compatibly with the structure sheaves by Stacks 06W9;
`x^{-1}F` is `AlgebraicGeometry.Stack.objectInverseImage`, resp.
`AlgebraicGeometry.Stack.objectModuleInverseImage`; `U_{étale}` is the small étale site of `U`
for the big étale site carried by `B` (Stacks 03FF); and `F|_{U_{étale}}` is the restriction of
Stacks 06W1, `AlgebraicGeometry.Stack.objectSmallEtaleRestriction`, resp.
`AlgebraicGeometry.Stack.objectSmallEtaleModuleRestriction`. Abelian sheaves and sheaves of
modules have their sections in the universe `max v w (u + 1)` containing both sites, as explained
in the module docstring of
`StacksFrontier/AlgebraicGeometry/Stacks/ObjectCohomologyLocalization.lean`. -/
@[stacks 075F, sga "4 VII 4.1" "more general"]
def cohomologyOverObjectComparison (τ : SiteKind) (n : ℕ) :
    (
      haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, u + 1}
        (J := (associatedTopology B S hS p (B.baseTopology τ)).over x)
      haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, max v w}
        (J := (B.baseTopology τ).over (p.obj x).left)
      haveI := Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{max v w, w, u + 1}
        (J := (associatedTopology B S hS p (B.baseTopology τ)).over x)
      haveI := Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, max v w}
        (J := (B.baseTopology τ).over (p.obj x).left)
      haveI := isDenseSubsite_overPost B S hS p hp (B.baseTopology τ) x
      (associatedTopology B S hS p (B.baseTopology τ)).overPullback
          AddCommGrpCat.{max v w (u + 1)} x ⋙
          Sheaf.functorH ((associatedTopology B S hS p (B.baseTopology τ)).over x) n ≅
        objectInverseImage B S hS p (B.baseTopology τ) x ⋙
          Sheaf.functorH ((B.baseTopology τ).over (p.obj x).left) n) ×
    (
      SheafOfModules.overFunctor (ringStructureSheaf.{u, v, w, u + 1} B S hS p hp
          (B.baseTopology τ) (B.baseTopology_le_topology τ)) x ⋙
          Stacks.Cohomology.BiggerSiteModules.moduleFunctorH.{u + 1, w, max v w}
            ((associatedTopology B S hS p (B.baseTopology τ)).over x)
            ((ringStructureSheaf.{u, v, w, u + 1} B S hS p hp (B.baseTopology τ)
              (B.baseTopology_le_topology τ)).over x) n ≅
        objectModuleInverseImage B S hS p hp (B.baseTopology τ) x
            (B.baseTopology_le_topology τ) ⋙
          Stacks.Cohomology.BiggerSiteModules.moduleFunctorH.{max v w, u, u + 1}
            ((B.baseTopology τ).over (p.obj x).left)
            (baseRingStructureSheafLift.{u, v, w} B (B.baseTopology τ)
              (B.baseTopology_le_topology τ) (p.obj x).left.1 (p.obj x).left.2) n) ×
    (τ = .etale →
      (
        haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, u + 1}
          (J := (associatedTopology B S hS p B.etaleTopology).over x)
        haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, max v w}
          (J := SmallEtale.topology B.toBigEtaleSite (p.obj x).left.1
            (toBigEtaleSite_contains_left B S hS p x))
        haveI := Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{max v w, w, u + 1}
          (J := (associatedTopology B S hS p B.etaleTopology).over x)
        haveI := Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, max v w}
          (J := SmallEtale.topology B.toBigEtaleSite (p.obj x).left.1
            (toBigEtaleSite_contains_left B S hS p x))
        (associatedTopology B S hS p B.etaleTopology).overPullback
            AddCommGrpCat.{max v w (u + 1)} x ⋙
            Sheaf.functorH ((associatedTopology B S hS p B.etaleTopology).over x) n ≅
          objectSmallEtaleRestriction B S hS p hp x ⋙
            Sheaf.functorH (SmallEtale.topology B.toBigEtaleSite (p.obj x).left.1
              (toBigEtaleSite_contains_left B S hS p x)) n) ×
      (
        SheafOfModules.overFunctor (ringStructureSheaf.{u, v, w, u + 1} B S hS p hp
            B.etaleTopology (etaleTopology_le_topology B)) x ⋙
            Stacks.Cohomology.BiggerSiteModules.moduleFunctorH.{u + 1, w, max v w}
              ((associatedTopology B S hS p B.etaleTopology).over x)
              ((ringStructureSheaf.{u, v, w, u + 1} B S hS p hp B.etaleTopology
                (etaleTopology_le_topology B)).over x) n ≅
          objectSmallEtaleModuleRestriction B S hS p hp x ⋙
            Stacks.Cohomology.BiggerSiteModules.moduleFunctorH.{max v w, u, u + 1}
              (SmallEtale.topology B.toBigEtaleSite (p.obj x).left.1
                (toBigEtaleSite_contains_left B S hS p x))
              (objectSmallEtaleRing B S hS p x) n)) :=
  ⟨cohomologyOverObjectIso B S hS p hp (B.baseTopology τ) x n,
    moduleCohomologyOverObjectIso B S hS p hp (B.baseTopology τ) x
      (B.baseTopology_le_topology τ) n,
    fun _ => ⟨etaleCohomologyOverObjectIso B S hS p hp x n,
      etaleModuleCohomologyOverObjectIso B S hS p hp x n⟩⟩

end Object

end AlgebraicGeometry.Stack

end
