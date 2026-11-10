module

public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalizationStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.BiggerSiteModuleCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# Cohomology over an object of the site of a category fibred in groupoids

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, `τ` a topology on the underlying
category of schemes, and `x` an object of `𝒳` lying over a scheme `U`. For an abelian sheaf `F`
on the associated site `𝒳_τ` of Stacks 06TP, and, when `τ` is coarser than the fppf topology,
for a sheaf `F` of modules over the structure sheaf `O_𝒳` (Stacks 06TV),

`H^n(x, F) = H^n((Sch/U)_τ, x^{-1}F)`,

naturally in `F`: cohomology over the object `x` — the cohomology of the localized site `𝒳_τ/x`
of the restriction of `F` — is the cohomology of the big `τ`-site of `U` of the inverse image
`x^{-1}F`. The two sites are identified by the canonical equivalence of Stacks 06W0, under which
the two structure sheaves correspond (Stacks 06W9), and the inverse image is the transport of
the restriction `F|_x` along it. This is the first assertion of **Stacks 075F**; the second, the
comparison with the small étale site, is in
`StacksFrontier/AlgebraicGeometry/Stacks/ObjectCohomologyLocalizationEtale.lean`.

## Main definitions

* `Stacks.Cohomology.SiteEquivalence.inverseImage`: the inverse image of abelian sheaves along an
  equivalence of sites, that is, the inverse of restriction.
* `AlgebraicGeometry.Stack.objectInverseImage`: the functor `x^{-1}` on abelian sheaves, the
  restriction to `𝒳_τ/x` followed by the transport along the equivalence with `(Sch/U)_τ`.
* `AlgebraicGeometry.Stack.baseRingStructureSheafLift`: the structure sheaf of rings of the big
  `τ`-site of a scheme, with its rings lifted to the universe of the modules.
* `AlgebraicGeometry.Stack.objectModuleInverseImage`: the functor `x^{-1}` on sheaves of
  `O_𝒳`-modules.

## Main results

* `Stacks.Cohomology.SiteEquivalence.cohomologyIso`: an equivalence of sites does not change the
  global cohomology of an abelian sheaf.
* `Stacks.Cohomology.SiteEquivalence.moduleCohomologyIso`: the same for sheaves of modules over a
  sheaf of rings and its restriction, cohomology being `Ext` out of the ring.
* `AlgebraicGeometry.Stack.isDenseSubsite_overPost`: the canonical localization functor of
  Stacks 06W0 exhibits `𝒳_τ/x` as a dense subsite of `(Sch/U)_τ`.
* `AlgebraicGeometry.Stack.ringRestriction_baseRingStructureSheafLift`: Stacks 06W9 for the
  lifted structure sheaves.
* `AlgebraicGeometry.Stack.cohomologyOverObjectIso`: **Stacks 075F**, the comparison for abelian
  sheaves.
* `AlgebraicGeometry.Stack.moduleCohomologyOverObjectIso`: **Stacks 075F**, the comparison for
  sheaves of `O_𝒳`-modules.

## Implementation notes

Global cohomology is Mathlib's `Ext`-based `CategoryTheory.Sheaf.H`, so the comparison is an
instance of `Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso`: `Ext` out of the image
of a left adjoint is computed on the other side of the adjunction. Here the adjunction is that of
the equivalence of sheaf categories attached to a dense subsite
(`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`), and the identification of the two constant
sheaves is Mathlib's `CategoryTheory.equivCommuteConstant`. Nothing has to be proved exact or
injective-preserving: an equivalence is both. The cohomology of a sheaf of modules is computed in
the category of sheaves of modules, as `Ext` out of the structure sheaf
(`Stacks.Cohomology.BiggerSiteModules.moduleFunctorH`), and the same argument applies to the
equivalence of module categories of a dense subsite.

As in `StacksFrontier/AlgebraicGeometry/Stacks/AssociatedSiteLocalization.lean` the topology is an
arbitrary `τ : GrothendieckTopology B.Schemes` (for modules, one coarser than the fppf topology,
which is what makes the structure sheaf a sheaf) rather than one of the five named topologies of
the source. The five topologies `τ ∈ {Zariski, étale, smooth, syntomic, fppf}` of the source are
the topologies `B.baseTopology τ`, `τ : AlgebraicGeometry.SiteKind`, each coarser than the fppf
topology by `AlgebraicGeometry.BigFppfSite.baseTopology_le_topology`, so one statement covers the
source's five cases.

The coefficient universe is the join `max v w (u + 1)` of the object universes of the two sites,
for `𝒳 : Type v` with morphisms in `Type w` over a big fppf site of schemes in `Type u`. That is
where both sheaf categories admit sheafification, have enough injective objects and have
`Ext`-groups in their own morphism universe, and it is the only choice making those two morphism
universes equal, which is what
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso` requires. The sheafification and
`Ext` statements of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/CohomologyOfModules.lean` are therefore
applied with that universe pinned, as local instances rather than global ones: as global
instances their heads match both sites, which leaves the coefficient universe an unsolvable
constraint. For sheaves of modules the structure sheaves are lifted to the same universe
(`AlgebraicGeometry.Stack.ringStructureSheaf` on `𝒳`,
`AlgebraicGeometry.Stack.baseRingStructureSheafLift` on the schemes over `U`), by one and the
same `ULift`, so that Stacks 06W9 holds for them on the nose.

## References

* [Stacks Project, Tag 075F](https://stacks.math.columbia.edu/tag/075F)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 06W9](https://stacks.math.columbia.edu/tag/06W9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace Stacks.Cohomology.SiteEquivalence

universe v₁ u₁ v₂ u₂

/-! ### Abelian sheaves -/

section AbelianSheaves

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsDenseSubsite J K]
  [∀ Y : Dᵒᵖ, HasLimitsOfShape (StructuredArrow Y G.op) AddCommGrpCat.{max u₁ u₂}]
  [HasSheafify J AddCommGrpCat.{max u₁ u₂}] [HasSheafify K AddCommGrpCat.{max u₁ u₂}]

/-- **The inverse image of abelian sheaves along an equivalence of sites.** For `G` exhibiting
`(C, J)` as a dense subsite of `(D, K)`, restriction of abelian sheaves along `G` is an
equivalence of categories; this is its inverse, the functor `g^{-1}` of the induced morphism of
topoi `Sh(D, K) → Sh(C, J)`. -/
abbrev inverseImage :
    Sheaf J AddCommGrpCat.{max u₁ u₂} ⥤ Sheaf K AddCommGrpCat.{max u₁ u₂} :=
  (Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{max u₁ u₂}).functor

variable [HasExt.{max u₁ u₂} (Sheaf J AddCommGrpCat.{max u₁ u₂})]
  [HasExt.{max u₁ u₂} (Sheaf K AddCommGrpCat.{max u₁ u₂})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u₁ u₂})]
  [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{max u₁ u₂})]

/-- **An equivalence of sites does not change global cohomology.** If `G` exhibits `(C, J)` as a
dense subsite of `(D, K)` and carries a terminal object of `C` to a terminal object of `D`, then
the global cohomology of an abelian sheaf `F` on `(C, J)` is the global cohomology of its inverse
image on `(D, K)`, naturally in `F`.

Global cohomology is `Ext` out of the constant sheaf `ℤ`, and the two constant sheaves correspond
under the equivalence (`CategoryTheory.equivCommuteConstant`), so this is
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso` for the adjunction of the
equivalence. -/
def cohomologyIso {T : C} (hT : IsTerminal T) (hT' : IsTerminal (G.obj T)) (n : ℕ) :
    Sheaf.functorH J n ≅ inverseImage J K G ⋙ Sheaf.functorH K n :=
  letI E := Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{max u₁ u₂}
  haveI : E.symm.functor.Additive := Functor.additive_of_preserves_binary_products _
  haveI : E.functor.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms E.symm.toAdjunction
  ExtComparison.extFunctorObjIsoCompOfIso E.symm.toAdjunction
    (E.inverse.mapIso ((equivCommuteConstant J AddCommGrpCat.{max u₁ u₂} K G hT hT').app
        (AddCommGrpCat.of (ULift.{max u₁ u₂} ℤ))).symm ≪≫ (E.unitIso.app _).symm) n

end AbelianSheaves

/-! ### Sheaves of modules

For sheaves of modules the coefficient universe has to contain the morphisms of the two sites as
well as their objects: `SheafOfModules` ties the universe of the sections of the ring to that of
the sections of the modules, and the category of sheaves of modules is Grothendieck abelian only
in a universe containing the whole site. Cohomology is `Ext` out of the ring viewed as a module
over itself (`Stacks.Cohomology.BiggerSiteModules.moduleFunctorH`), and no terminal object is
involved: restriction of modules carries the unit object to the unit object on the nose. -/

section Modules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsDenseSubsite J K]
  [∀ Y : Dᵒᵖ,
    HasLimitsOfShape (StructuredArrow Y G.op) AddCommGrpCat.{max u₁ v₁ u₂ v₂}]
  (R : Sheaf K RingCat.{max u₁ v₁ u₂ v₂})

/-- **An equivalence of sites does not change the cohomology of sheaves of modules.** Let `G`
exhibit `(C, J)` as a dense subsite of `(D, K)` and let `R` be a sheaf of rings on `(D, K)`.
Restriction of sheaves of modules along `G` is then an equivalence onto the sheaves of modules
over the restricted ring (`Stacks.DenseSubsiteModules.moduleRestrictionEquivalence`), and for
every degree `n` the cohomology of a sheaf of modules over the restricted ring is the cohomology
of its inverse image, naturally in the module.

As for abelian sheaves this is
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso` for the adjunction of the
equivalence; the identification of the two unit objects, which replaces the comparison of the
constant sheaves, is the identity. -/
def moduleCohomologyIso (n : ℕ) :
    Stacks.Cohomology.BiggerSiteModules.moduleFunctorH.{max u₂ v₂, v₁, u₁} J
        (Stacks.DenseSubsiteModules.ringRestriction J K G R) n ≅
      (Stacks.DenseSubsiteModules.moduleRestrictionEquivalence J K G R).inverse ⋙
        Stacks.Cohomology.BiggerSiteModules.moduleFunctorH.{max u₁ v₁, v₂, u₂} K R n :=
  letI E := Stacks.DenseSubsiteModules.moduleRestrictionEquivalence J K G R
  haveI : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  haveI : E.inverse.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms E.toAdjunction
  haveI e : E.functor.obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit (Stacks.DenseSubsiteModules.ringRestriction J K G R) := Iso.refl _
  ExtComparison.extFunctorObjIsoCompOfIso E.toAdjunction e n

end Modules

end Stacks.Cohomology.SiteEquivalence

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (x : 𝒳)

include hp in
/-- **The canonical localization functor of Stacks 06W0 exhibits a dense subsite.** The functor
`Over.post` from the slice of `𝒳` at `x` to the schemes over the scheme `x` lies over is an
equivalence of categories identifying the localized associated topology with the localized base
topology, so `𝒳_τ/x` is a dense subsite of `(Sch/U)_τ` along it. -/
theorem isDenseSubsite_overPost :
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).IsDenseSubsite
      ((associatedTopology B S hS p τ).over x) (τ.over (p.obj x).left) := by
  have := isEquivalence_overPost B S hS p hp x
  rw [← inducedTopology_overPost B S hS p hp τ x]
  infer_instance

include hp in
/-- The canonical localization functor of Stacks 06W0 carries the terminal object `id : x → x` of
the slice of `𝒳` at `x` to a terminal object of the schemes over the scheme `x` lies over, being
an equivalence of categories. -/
def isTerminal_overPost_mkId :
    IsTerminal ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).obj (Over.mk (𝟙 x))) :=
  haveI := isEquivalence_overPost B S hS p hp x
  Over.mkIdTerminal.isTerminalObj
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))) (Over.mk (𝟙 x))

/-- **The inverse image `x^{-1}` of abelian sheaves at an object.** An abelian sheaf `F` on the
associated site `𝒳_τ` is restricted to the localized site `𝒳_τ/x` and then transported along the
equivalence of Stacks 06W0 with the big `τ`-site of the scheme `U` that `x` lies over. This is
the inverse image of the morphism of topoi `x : Sh((Sch/U)_τ) → Sh(𝒳_τ)`. -/
abbrev objectInverseImage
    [HasSheafify ((associatedTopology B S hS p τ).over x) AddCommGrpCat.{max v w (u + 1)}]
    [HasSheafify (τ.over (p.obj x).left) AddCommGrpCat.{max v w (u + 1)}]
    [∀ Y : (Over (p.obj x).left)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow Y
        (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).op) AddCommGrpCat.{max v w (u + 1)}]
    [(Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).IsDenseSubsite
      ((associatedTopology B S hS p τ).over x) (τ.over (p.obj x).left)] :
    Sheaf (associatedTopology B S hS p τ) AddCommGrpCat.{max v w (u + 1)} ⥤
      Sheaf (τ.over (p.obj x).left) AddCommGrpCat.{max v w (u + 1)} :=
  (associatedTopology B S hS p τ).overPullback AddCommGrpCat.{max v w (u + 1)} x ⋙
    Stacks.Cohomology.SiteEquivalence.inverseImage ((associatedTopology B S hS p τ).over x)
      (τ.over (p.obj x).left) (Over.post (X := x) (p ⋙ Over.forget (B.obj hS)))

/-- **Stacks 075F, for abelian sheaves.** Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in
groupoids, `τ` a topology on the underlying category of schemes and `x` an object of `𝒳` lying
over a scheme `U`. Then for every degree `n`

`H^n_τ(x, F) = H^n((Sch/U)_τ, x^{-1}F)`,

naturally in the abelian sheaf `F` on `𝒳_τ`, where cohomology over `x` is the global cohomology
of the localized site `𝒳_τ/x` applied to the restriction of `F`.

The two sites are identified by the canonical equivalence of Stacks 06W0, under which the
restriction of `F` to `𝒳_τ/x` becomes `x^{-1}F`; cohomology is then unchanged by
`Stacks.Cohomology.SiteEquivalence.cohomologyIso`. The source's five topologies are the
`B.baseTopology τ`, `τ : AlgebraicGeometry.SiteKind`, `τ` being arbitrary here. -/
def cohomologyOverObjectIso (n : ℕ) :
    haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, u + 1}
      (J := (associatedTopology B S hS p τ).over x)
    haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, max v w}
      (J := τ.over (p.obj x).left)
    haveI := Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{max v w, w, u + 1}
      (J := (associatedTopology B S hS p τ).over x)
    haveI := Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, max v w}
      (J := τ.over (p.obj x).left)
    haveI := isDenseSubsite_overPost B S hS p hp τ x
    (associatedTopology B S hS p τ).overPullback AddCommGrpCat.{max v w (u + 1)} x ⋙
        Sheaf.functorH ((associatedTopology B S hS p τ).over x) n ≅
      objectInverseImage B S hS p τ x ⋙ Sheaf.functorH (τ.over (p.obj x).left) n :=
  haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, u + 1}
    (J := (associatedTopology B S hS p τ).over x)
  haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, max v w}
    (J := τ.over (p.obj x).left)
  haveI := Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{max v w, w, u + 1}
    (J := (associatedTopology B S hS p τ).over x)
  haveI := Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, max v w}
    (J := τ.over (p.obj x).left)
  haveI := isDenseSubsite_overPost B S hS p hp τ x
  haveI := Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{max v w, w, u + 1}
    (J := (associatedTopology B S hS p τ).over x)
  haveI := Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{u + 1, u, max v w}
    (J := τ.over (p.obj x).left)
  Functor.isoWhiskerLeft _
    (Stacks.Cohomology.SiteEquivalence.cohomologyIso ((associatedTopology B S hS p τ).over x)
      (τ.over (p.obj x).left) (Over.post (X := x) (p ⋙ Over.forget (B.obj hS)))
      Over.mkIdTerminal (isTerminal_overPost_mkId B S hS p hp x) n)

/-! ### Sheaves of modules over the structure sheaf -/

section Modules

variable (hτ : τ ≤ B.topology)

set_option linter.checkUnivs false in
/-- **The structure sheaf of rings of the big `τ`-site of a scheme**, with its rings lifted to the
universe `max v w (u + 1)`. Its ring of sections over `V → T` is `Γ(V, O_V)`, transported through
`ULift`; the lift is the one `AlgebraicGeometry.Stack.ringStructureSheaf` applies to the structure
sheaf of `𝒳`, so that, by Stacks 06W9, restricting this sheaf along the localization equivalence
of Stacks 06W0 gives the restriction of the structure sheaf of `𝒳` to the slice at `x` on the
nose (`AlgebraicGeometry.Stack.ringRestriction_baseRingStructureSheafLift`). -/
noncomputable def baseRingStructureSheafLift (T : Scheme.{u}) (hT : B.Contains T) :
    Sheaf (τ.over (B.obj hT)) RingCat.{max u v w (u + 1)} := by
  let F : RingCat.{u} ⥤ RingCat.{max u v w (u + 1)} :=
    { obj R := RingCat.of (ULift.{max v w (u + 1)} R)
      map f := RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (f.hom.comp ULift.ringEquiv.toRingHom)) }
  let O := baseRingStructureSheaf B T hT τ hτ
  refine ⟨O.obj ⋙ F, ?_⟩
  let : PreservesLimitsOfSize.{u, u + 1} (forget RingCat.{u}) :=
    preservesLimits_of_natIso ringForgetIsoCoyoneda
  let : PreservesLimitsOfSize.{u, u + 1} (forget RingCat.{max u v w (u + 1)}) :=
    preservesLimits_of_natIso ringForgetIsoCoyoneda
  let : ReflectsLimitsOfSize.{u, u + 1} (forget RingCat.{max u v w (u + 1)}) :=
    reflectsLimits_of_reflectsIsomorphisms
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget RingCat.{max u v w (u + 1)})
  change Presheaf.IsSheaf _ ((O.obj ⋙ forget RingCat.{u}) ⋙ uliftFunctor.{max v w (u + 1)})
  exact Presheaf.isSheaf_comp_of_isSheaf _ _ _ (Presheaf.isSheaf_comp_of_isSheaf _ _ _ O.property)

include hp in
/-- **Stacks 06W9 for the lifted structure sheaves.** Restricting the lifted structure sheaf of
the big `τ`-site of `U` along the localization equivalence of Stacks 06W0 is the restriction of
the lifted structure sheaf of `𝒳` to the slice at `x`, on the nose. -/
theorem ringRestriction_baseRingStructureSheafLift :
    haveI := isDenseSubsite_overPost B S hS p hp τ x
    Stacks.DenseSubsiteModules.ringRestriction ((associatedTopology B S hS p τ).over x)
        (τ.over (p.obj x).left) (Over.post (X := x) (p ⋙ Over.forget (B.obj hS)))
        (baseRingStructureSheafLift.{u, v, w} B τ hτ (p.obj x).left.1 (p.obj x).left.2) =
      (ringStructureSheaf.{u, v, w, u + 1} B S hS p hp τ hτ).over x :=
  rfl

/-- **The inverse image `x^{-1}` of sheaves of `O_𝒳`-modules at an object.** A sheaf of modules
over the structure sheaf of `𝒳_τ` is restricted to the slice `𝒳_τ/x`, where it is a module over
the restricted structure sheaf, and then transported along the equivalence of Stacks 06W0 to a
sheaf of modules over the structure sheaf of the big `τ`-site of `U`; by Stacks 06W9 the two
structure sheaves correspond under that equivalence
(`AlgebraicGeometry.Stack.ringRestriction_baseRingStructureSheafLift`), so the transport is the
inverse of the equivalence of module categories of
`Stacks.DenseSubsiteModules.moduleRestrictionEquivalence`. -/
noncomputable abbrev objectModuleInverseImage :
    haveI := isDenseSubsite_overPost B S hS p hp τ x
    SheafOfModules.{max u v w (u + 1)} (ringStructureSheaf.{u, v, w, u + 1} B S hS p hp τ hτ) ⥤
      SheafOfModules.{max u v w (u + 1)}
        (baseRingStructureSheafLift.{u, v, w} B τ hτ (p.obj x).left.1 (p.obj x).left.2) :=
  haveI := isDenseSubsite_overPost B S hS p hp τ x
  SheafOfModules.overFunctor (ringStructureSheaf.{u, v, w, u + 1} B S hS p hp τ hτ) x ⋙
    (Stacks.DenseSubsiteModules.moduleRestrictionEquivalence
      ((associatedTopology B S hS p τ).over x) (τ.over (p.obj x).left)
      (Over.post (X := x) (p ⋙ Over.forget (B.obj hS)))
      (baseRingStructureSheafLift.{u, v, w} B τ hτ (p.obj x).left.1 (p.obj x).left.2)).inverse

/-- **Stacks 075F, for sheaves of `O_𝒳`-modules.** Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category
fibred in groupoids, `τ` a topology on the underlying category of schemes coarser than the fppf
topology, and `x` an object of `𝒳` lying over a scheme `U`. Then for every degree `n`

`H^n_τ(x, F) = H^n((Sch/U)_τ, x^{-1}F)`,

naturally in the sheaf `F` of `O_𝒳`-modules on `𝒳_τ`. Here the cohomology of a sheaf of modules
is the cohomology computed in the category of sheaves of modules, `Ext^n` out of the structure
sheaf (`Stacks.Cohomology.BiggerSiteModules.moduleFunctorH`); cohomology over `x` is that of the
restriction of `F` to the slice `𝒳_τ/x`, a module over the restricted structure sheaf; and
`x^{-1}F` is `AlgebraicGeometry.Stack.objectModuleInverseImage`, a module over the structure
sheaf of the big `τ`-site of `U`.

The equivalence of ringed sites of Stacks 06W0 and 06W9 makes the two module categories
equivalent, compatibly with the two structure sheaves, and cohomology is unchanged by
`Stacks.Cohomology.SiteEquivalence.moduleCohomologyIso`. The five topologies of the source are
the `B.baseTopology τ` for `τ : AlgebraicGeometry.SiteKind`, each coarser than the fppf topology
(`AlgebraicGeometry.BigFppfSite.baseTopology_le_topology`). -/
def moduleCohomologyOverObjectIso (n : ℕ) :
    SheafOfModules.overFunctor (ringStructureSheaf.{u, v, w, u + 1} B S hS p hp τ hτ) x ⋙
        Stacks.Cohomology.BiggerSiteModules.moduleFunctorH.{u + 1, w, max v w}
          ((associatedTopology B S hS p τ).over x)
          ((ringStructureSheaf.{u, v, w, u + 1} B S hS p hp τ hτ).over x) n ≅
      objectModuleInverseImage B S hS p hp τ x hτ ⋙
        Stacks.Cohomology.BiggerSiteModules.moduleFunctorH.{max v w, u, u + 1}
          (τ.over (p.obj x).left)
          (baseRingStructureSheafLift.{u, v, w} B τ hτ (p.obj x).left.1 (p.obj x).left.2) n :=
  haveI := isDenseSubsite_overPost B S hS p hp τ x
  Functor.isoWhiskerLeft _
    (Stacks.Cohomology.SiteEquivalence.moduleCohomologyIso ((associatedTopology B S hS p τ).over x)
      (τ.over (p.obj x).left) (Over.post (X := x) (p ⋙ Over.forget (B.obj hS)))
      (baseRingStructureSheafLift.{u, v, w} B τ hτ (p.obj x).left.1 (p.obj x).left.2) n)

end Modules

end AlgebraicGeometry.Stack

end
