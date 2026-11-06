module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.SheafCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Exactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MayerVietoris
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DenseSubsite
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.UniversalHomeomorphismLocal.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteObjectCohomology
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.NoetherianSpaces

/-!
# Transport of the vanishing of the cohomology of a constant sheaf between étale sites

Let `G : C ⥤ D` exhibit `(C, J)` as a dense subsite of `(D, K)` and carry a terminal object of
`C` to a terminal object of `D`. Restriction of abelian sheaves along `G` is then an equivalence
of sheaf categories carrying the constant sheaf on `M` to the constant sheaf on `M`, so the two
sites have the same cohomology of the constant sheaf on `M` in every degree — and in particular
one of those groups vanishes exactly when the other does.

This is applied to the three comparisons relating the small étale sites a scheme carries: the
size-bounded site of Stacks 021B cut out of a chosen big étale site, Mathlib's choice-free
`AlgebraicGeometry.Scheme.Etale`, and the one-universe model of the latter on which
`CategoryTheory.Sheaf.H'` is available; and to the comparison of the small étale sites of two
isomorphic schemes.

Cohomology is Mathlib's `Ext`-based `CategoryTheory.Sheaf.H`, whose `Ext` universe is independent
of the site; the statements therefore allow a different `Ext` universe on each side, which is
what makes them usable when one of the two sheaf categories has `Ext`-groups only in its own
morphism universe while the other is handed an arbitrary one.

## Main results

* `Stacks.Cohomology.DenseSubsiteConstant.subsingleton_H_constantSheaf_of_isDenseSubsite` and
  its primed variant: the transport of the vanishing between a dense subsite and the larger
  site, in both directions.
* `Stacks.EtaleCohomology.ConstantTransport.subsingleton_H_boundedSmallEtale_of_smallEtale` and
  `Stacks.EtaleCohomology.ConstantTransport.subsingleton_H_smallEtale_of_boundedSmallEtale`:
  the transport between the size-bounded small étale site of Stacks 021B and Mathlib's.
* `Stacks.EtaleCohomology.ConstantTransport.subsingleton_H_mayerVietoris_of_smallEtale` and
  `Stacks.EtaleCohomology.ConstantTransport.subsingleton_H_smallEtale_of_mayerVietoris`: the
  transport between Mathlib's small étale site and its one-universe model.
* `Stacks.EtaleCohomology.ConstantTransport.subsingleton_H_smallEtale_of_iso`: the transport
  along an isomorphism of schemes.
* `Stacks.EtaleCohomology.ConstantTransport.subsingleton_H'_opensToSite`: the cohomology of a
  constant sheaf *over* an open subscheme, read as an object of the small étale site, is the
  global cohomology of the constant sheaf on the small étale site of that open subscheme.
* `Stacks.Cohomology.DenseSubsiteConstant.constantSheafPushforwardContinuousIso`: restriction
  of sheaves along a continuous and cocontinuous functor carries the constant sheaf to the
  constant sheaf.

## Implementation notes

The equivalence of sheaf categories is
`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv` and the identification of the two constant
sheaves is Mathlib's `CategoryTheory.equivCommuteConstant` together with its primed variant.
Vanishing is transported by
`Stacks.CohomologyVanishing.subsingleton_ext_of_equivalence`, which crosses the two `Ext`
universes, and the two objects of the `Ext`-group are moved to their intended spellings by
`Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source` and
`Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target`.

The dense subsite inclusions used are: the embedding of the size-bounded site in Mathlib's
(`AlgebraicGeometry.SmallEtale.isDenseSubsite_toEtaleSite`); the functor `AsSmall.down` out of
the one-universe model, which is a dense subsite inclusion because that model carries the
induced topology; and base change along an isomorphism, which is a universal homeomorphism, so
`Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism` (Stacks 03SI) applies.

`Ext`-groups of abelian sheaves on Mathlib's small étale site, in the successor of the scheme
universe, are registered as an instance here: the transports name those groups in their
statements, so the instance has to be available before the statements are elaborated.

Cohomology over an open subscheme is compared with the global cohomology of that subscheme by
`Stacks.Cohomology.BiggerSite.cohomologyPresheafFunctorIso` — Stacks 03YU, statement 2 — at the
functor induced on the one-universe models by composition with the open immersion
(`AlgebraicGeometry.Scheme.Etale.smallEtaleCompose`). That statement needs the two sites to have
their objects and their morphisms in one universe, which is exactly what the one-universe models
provide and what Mathlib's `AlgebraicGeometry.Scheme.Etale` does not. Composition with an étale
morphism preserves fibre products and equalizers because it leaves the underlying scheme of an
object untouched, so the forgetful functor to schemes both reflects and preserves those limits.

## References

* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe w w' v₁ u₁ v₂ u₂ v₃ u₃ u₄ vA uA a u

namespace Stacks.Cohomology.DenseSubsiteConstant

/-- **The cohomology of a constant abelian sheaf does not change on a dense subsite.** If
`G : C ⥤ D` exhibits `(C, J)` as a dense subsite of `(D, K)` and carries the terminal object
`TC` of `C` to a terminal object of `D`, then the vanishing of the cohomology of the constant
sheaf with value `M` on `(D, K)` in degree `q` gives its vanishing on `(C, J)`.

The `Ext` universes on the two sides are unrelated. -/
public theorem subsingleton_H_constantSheaf_of_isDenseSubsite
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
    [G.IsDenseSubsite J K]
    [∀ Y : Dᵒᵖ, HasLimitsOfShape (StructuredArrow Y G.op) AddCommGrpCat.{a}]
    [HasSheafify J AddCommGrpCat.{a}] [HasSheafify K AddCommGrpCat.{a}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{a})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{a})]
    {TC : C} (hTC : IsTerminal TC) (hTD : IsTerminal (G.obj TC))
    (M : AddCommGrpCat.{a}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{w'} ((constantSheaf K AddCommGrpCat.{a}).obj M) q)) :
    Subsingleton (Sheaf.H.{w} ((constantSheaf J AddCommGrpCat.{a}).obj M) q) := by
  let E := Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}
  have : HasBinaryProducts (Sheaf K AddCommGrpCat.{a}) := by
    haveI := Abelian.hasFiniteBiproducts (C := Sheaf K AddCommGrpCat.{a})
    haveI := hasBinaryBiproducts_of_finite_biproducts (Sheaf K AddCommGrpCat.{a})
    exact hasBinaryProducts_of_hasBinaryBiproducts
  have : PreservesLimitsOfShape (Discrete WalkingPair) E.symm.functor :=
    have := E.toAdjunction.rightAdjoint_preservesLimits.{0, 0}; inferInstance
  have : E.symm.functor.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isRightAdjoint _
  have : E.symm.functor.Additive := Functor.additive_of_preserves_binary_products _
  have h₀ : Subsingleton (Abelian.Ext.{w'}
      ((constantSheaf K AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift.{a} ℤ)))
      (E.symm.inverse.obj ((constantSheaf J AddCommGrpCat.{a}).obj M)) q) :=
    Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target
      ((equivCommuteConstant J AddCommGrpCat.{a} K G hTC hTD).app M).symm q h
  exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source
    ((equivCommuteConstant' J AddCommGrpCat.{a} K G hTC hTD).app
      (AddCommGrpCat.of (ULift.{a} ℤ))).symm q
    (Stacks.CohomologyVanishing.subsingleton_ext_of_equivalence E.symm
      ((constantSheaf K AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift.{a} ℤ)))
      ((constantSheaf J AddCommGrpCat.{a}).obj M) q h₀)

/-- **The cohomology of a constant abelian sheaf does not change on a dense subsite**, read from
the subsite to the larger site: the vanishing of the cohomology of the constant sheaf with value
`M` on the dense subsite `(C, J)` in degree `q` gives its vanishing on `(D, K)`.

The `Ext` universes on the two sides are unrelated. -/
public theorem subsingleton_H_constantSheaf_of_isDenseSubsite'
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
    [G.IsDenseSubsite J K]
    [∀ Y : Dᵒᵖ, HasLimitsOfShape (StructuredArrow Y G.op) AddCommGrpCat.{a}]
    [HasSheafify J AddCommGrpCat.{a}] [HasSheafify K AddCommGrpCat.{a}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{a})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{a})]
    {TC : C} (hTC : IsTerminal TC) (hTD : IsTerminal (G.obj TC))
    (M : AddCommGrpCat.{a}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{w} ((constantSheaf J AddCommGrpCat.{a}).obj M) q)) :
    Subsingleton (Sheaf.H.{w'} ((constantSheaf K AddCommGrpCat.{a}).obj M) q) := by
  let E := Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}
  have : HasBinaryProducts (Sheaf J AddCommGrpCat.{a}) := by
    haveI := Abelian.hasFiniteBiproducts (C := Sheaf J AddCommGrpCat.{a})
    haveI := hasBinaryBiproducts_of_finite_biproducts (Sheaf J AddCommGrpCat.{a})
    exact hasBinaryProducts_of_hasBinaryBiproducts
  have : PreservesLimitsOfShape (Discrete WalkingPair) E.functor :=
    have := E.symm.toAdjunction.rightAdjoint_preservesLimits.{0, 0}; inferInstance
  have : E.functor.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isRightAdjoint _
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  have h₀ : Subsingleton (Abelian.Ext.{w}
      ((constantSheaf J AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift.{a} ℤ)))
      (E.inverse.obj ((constantSheaf K AddCommGrpCat.{a}).obj M)) q) :=
    Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target
      ((equivCommuteConstant' J AddCommGrpCat.{a} K G hTC hTD).app M) q h
  exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source
    ((equivCommuteConstant J AddCommGrpCat.{a} K G hTC hTD).app
      (AddCommGrpCat.of (ULift.{a} ℤ))) q
    (Stacks.CohomologyVanishing.subsingleton_ext_of_equivalence E
      ((constantSheaf J AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift.{a} ℤ)))
      ((constantSheaf K AddCommGrpCat.{a}).obj M) q h₀)

/-- **Restriction of sheaves along a continuous and cocontinuous functor carries the constant
sheaf to the constant sheaf.** Restriction is precomposition with `G.op`, which carries the
constant presheaf with value `X` to the constant presheaf with value `X`, and it commutes with
sheafification because `G` is cocontinuous. -/
public def constantSheafPushforwardContinuousIso
    {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₃} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
    (A : Type uA) [Category.{vA} A] [HasWeakSheafify J A] [HasWeakSheafify K A]
    [G.IsContinuous J K] [G.IsCocontinuous J K]
    [∀ P : Cᵒᵖ ⥤ A, G.op.HasPointwiseRightKanExtension P] :
    constantSheaf K A ⋙ G.sheafPushforwardContinuous A J K ≅ constantSheaf J A :=
  Functor.isoWhiskerLeft (Functor.const Dᵒᵖ)
      (G.pushforwardContinuousSheafificationCompatibility A J K).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.constCompWhiskeringLeftIso Cᵒᵖ G.op :
        Functor.const Dᵒᵖ ⋙ (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op ≅ Functor.const Cᵒᵖ)
      (presheafToSheaf J A)

end Stacks.Cohomology.DenseSubsiteConstant

namespace Stacks.EtaleCohomology.ConstantTransport

open Stacks.Cohomology.DenseSubsiteConstant

/-- Abelian sheaves on Mathlib's small étale site of a scheme, with coefficients in the
successor of the scheme universe, have `Ext`-groups in that same universe: the sheaf category is
Grothendieck abelian because the site is essentially small there. -/
public instance hasExt_sheaf_smallEtaleTopology (Y : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  have : IsGrothendieckAbelian.{u + 1}
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale.{u, u} Y
  IsGrothendieckAbelian.hasExt _

/-! ### The size-bounded small étale site and Mathlib's -/

section Bounded

variable (B : BigEtaleSite.{u}) (Y : Scheme.{u}) (hY : B.Contains Y)

/-- The image of the final object `Y / Y` of the size-bounded small étale site under the
embedding in Mathlib's small étale site is terminal there: both are the identity of `Y`. -/
public def isTerminal_toEtaleSite_obj_final :
    IsTerminal ((SmallEtale.toEtaleSite B Y hY).obj (SmallEtale.final B Y hY)) :=
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  MorphismProperty.Over.mkIdTerminal _ _

/-- The structured-arrow categories over the embedding of the size-bounded small étale site in
Mathlib's have limits of their own size, the embedding being a functor between essentially small
categories. -/
private theorem hasLimitsOfShape_structuredArrow_toEtaleSite :
    ∀ T : (Y.Etale)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow T (SmallEtale.toEtaleSite B Y hY).op) AddCommGrpCat.{u + 1} :=
  fun _ => hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- The structured-arrow categories over the opposite of the embedding of the size-bounded small
étale site in Mathlib's have limits of their own size. This is the statement of
`hasLimitsOfShape_structuredArrow_toEtaleSite` as a declaration downstream modules may use. -/
public alias hasLimitsOfShape_structuredArrow_toEtaleSite_op :=
  hasLimitsOfShape_structuredArrow_toEtaleSite

/-- **The vanishing of the cohomology of a finite constant sheaf passes from Mathlib's small
étale site to the size-bounded one.** The site of Stacks 021B cut out of a big étale site `B` is
a dense subsite of Mathlib's, and its final object is carried to the final object. -/
public theorem subsingleton_H_boundedSmallEtale_of_smallEtale
    [HasExt.{w} (Sheaf (SmallEtale.topology B Y hY) AddCommGrpCat.{u + 1})]
    (M : AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1}
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q)) :
    Subsingleton (Sheaf.H.{w}
      ((constantSheaf (SmallEtale.topology B Y hY) AddCommGrpCat.{u + 1}).obj M) q) :=
  have := hasLimitsOfShape_structuredArrow_toEtaleSite B Y hY
  subsingleton_H_constantSheaf_of_isDenseSubsite _ _ (SmallEtale.toEtaleSite B Y hY)
    (SmallEtale.finalIsTerminal B Y hY) (isTerminal_toEtaleSite_obj_final B Y hY) M q h

/-- **The vanishing of the cohomology of a constant sheaf passes from the size-bounded small
étale site to Mathlib's**, the two sites having the same abelian sheaves. -/
public theorem subsingleton_H_smallEtale_of_boundedSmallEtale
    [HasExt.{w} (Sheaf (SmallEtale.topology B Y hY) AddCommGrpCat.{u + 1})]
    (M : AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{w}
      ((constantSheaf (SmallEtale.topology B Y hY) AddCommGrpCat.{u + 1}).obj M) q)) :
    Subsingleton (Sheaf.H.{u + 1}
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q) :=
  have := hasLimitsOfShape_structuredArrow_toEtaleSite B Y hY
  subsingleton_H_constantSheaf_of_isDenseSubsite' _ _ (SmallEtale.toEtaleSite B Y hY)
    (SmallEtale.finalIsTerminal B Y hY) (isTerminal_toEtaleSite_obj_final B Y hY) M q h

end Bounded

/-! ### Mathlib's small étale site and its one-universe model -/

section MayerVietoris

variable (Y : Scheme.{u})

/-- The functor out of the one-universe model of the small étale site carries its final object
to the identity of `Y`, which is the final object of Mathlib's site. -/
private def isTerminal_asSmallDown_self :
    IsTerminal ((AsSmall.down : MayerVietoris.Site Y ⥤ Y.Etale).obj (MayerVietoris.self Y)) :=
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  MorphismProperty.Over.mkIdTerminal _ _

/-- **The vanishing of the cohomology of a constant sheaf passes from Mathlib's small étale site
to its one-universe model.** The model carries the topology induced along `AsSmall.down`, which
makes that functor a dense subsite inclusion. -/
public theorem subsingleton_H_mayerVietoris_of_smallEtale
    (M : AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1}
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q)) :
    Subsingleton (Sheaf.H.{u + 1}
      ((constantSheaf (MayerVietoris.topology Y) AddCommGrpCat.{u + 1}).obj M) q) :=
  subsingleton_H_constantSheaf_of_isDenseSubsite _ _
    (AsSmall.down : MayerVietoris.Site Y ⥤ Y.Etale) (MayerVietoris.selfIsTerminal Y)
    (isTerminal_asSmallDown_self Y) M q h

/-- **The vanishing of the cohomology of a constant sheaf passes from the one-universe model of
the small étale site to Mathlib's.** -/
public theorem subsingleton_H_smallEtale_of_mayerVietoris
    (M : AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1}
      ((constantSheaf (MayerVietoris.topology Y) AddCommGrpCat.{u + 1}).obj M) q)) :
    Subsingleton (Sheaf.H.{u + 1}
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q) :=
  subsingleton_H_constantSheaf_of_isDenseSubsite' _ _
    (AsSmall.down : MayerVietoris.Site Y ⥤ Y.Etale) (MayerVietoris.selfIsTerminal Y)
    (isTerminal_asSmallDown_self Y) M q h

end MayerVietoris

/-! ### An isomorphism of schemes -/

/-- **The vanishing of the cohomology of a constant sheaf is invariant under an isomorphism of
schemes.** An isomorphism is a universal homeomorphism, so base change along it exhibits the
small étale site of the target as a dense subsite of that of the source (Stacks 03SI), and it
carries the final object to the final object. -/
public theorem subsingleton_H_smallEtale_of_iso {Y Y' : Scheme.{u}} (e : Y ≅ Y')
    (M : AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1}
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q)) :
    Subsingleton (Sheaf.H.{u + 1}
      ((constantSheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q) :=
  have := AlgebraicGeometry.universalHomeomorphism_of_isIso e.hom
  have := isDenseSubsite_of_universalHomeomorphism e.hom
  have hT' : IsTerminal (Scheme.Etale.mk (𝟙 Y')) :=
    have : IsIso (Scheme.Etale.mk (𝟙 Y')).hom := inferInstanceAs (IsIso (𝟙 Y'))
    isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 Y'))
  have : ∀ T : (Y.Etale)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow T (smallEtaleBaseChange e.hom).op) AddCommGrpCat.{u + 1} :=
    fun _ => inferInstance
  subsingleton_H_constantSheaf_of_isDenseSubsite _ _ (smallEtaleBaseChange e.hom)
    hT' (isTerminalSmallEtaleBaseChangeObj e.hom hT') M q h

/-- **An isomorphism of schemes restricts to an isomorphism between an open subscheme of the
target and its inverse image.** Both are open subschemes of the two schemes with the same image
in the target, the inverse image being mapped onto the open subscheme because the isomorphism is
surjective on points. -/
public def preimageOpensIsoOfIsIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (V : Y.Opens) :
    (f ⁻¹ᵁ V).toScheme ≅ V.toScheme := by
  refine IsOpenImmersion.isoOfRangeEq ((f ⁻¹ᵁ V).ι ≫ f) V.ι ?_
  have hs : Function.Surjective (TopCat.Hom.hom f.base) :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso f))).surjective
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
    Scheme.Opens.range_ι, Set.range_comp]
  exact Set.image_preimage_eq_of_subset (by simp [hs.range_eq])

/-! ### Cohomology over an open subscheme -/

section Opens

open AlgebraicGeometry.Scheme.Etale

/-- The functor `AsSmall.up` into the one-universe model of the small étale site of a scheme is
a dense subsite inclusion: the model carries the topology induced along `AsSmall.down`, and
`AsSmall.up` is the functor of the corresponding equivalence of sites. -/
public instance asSmallUp_isDenseSubsite (S : Scheme.{u}) :
    (AsSmall.up : S.Etale ⥤ MayerVietoris.Site S).IsDenseSubsite
      S.smallEtaleTopology (MayerVietoris.topology S) :=
  inferInstanceAs ((MayerVietoris.siteEquiv S).functor.IsDenseSubsite S.smallEtaleTopology
    ((MayerVietoris.siteEquiv S).inverse.inducedTopology S.smallEtaleTopology))

/-- **Composition with an étale morphism preserves fibre products of étale schemes.** It leaves
the underlying scheme of an object and the underlying morphism of a morphism untouched, so the
forgetful functor to schemes both reflects and preserves the fibre products in question. -/
public instance smallEtaleCompose_preservesLimitsOfShape_walkingCospan {U X : Scheme.{u}}
    (j : U ⟶ X) [Etale j] :
    PreservesLimitsOfShape WalkingCospan (smallEtaleCompose j) :=
  have : PreservesLimitsOfShape WalkingCospan
      (smallEtaleCompose j ⋙ (Scheme.Etale.forget X ⋙ Over.forget X)) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan
      (Scheme.Etale.forget U ⋙ Over.forget U))
  preservesLimitsOfShape_of_reflects_of_preserves _ (Scheme.Etale.forget X ⋙ Over.forget X)

/-- **Composition with an étale morphism preserves equalizers of étale schemes**, for the same
reason as fibre products. -/
public instance smallEtaleCompose_preservesLimitsOfShape_walkingParallelPair {U X : Scheme.{u}}
    (j : U ⟶ X) [Etale j] :
    PreservesLimitsOfShape WalkingParallelPair (smallEtaleCompose j) :=
  have : PreservesLimitsOfShape WalkingParallelPair
      (smallEtaleCompose j ⋙ (Scheme.Etale.forget X ⋙ Over.forget X)) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingParallelPair
      (Scheme.Etale.forget U ⋙ Over.forget U))
  preservesLimitsOfShape_of_reflects_of_preserves _ (Scheme.Etale.forget X ⋙ Over.forget X)

variable (S : Scheme.{u}) (U : S.Opens)

/-- Composition with the inclusion of an open subscheme, read on the one-universe models of the
two small étale sites. -/
public abbrev opensInclusion : MayerVietoris.Site U.toScheme ⥤ MayerVietoris.Site S :=
  AsSmall.down ⋙ smallEtaleCompose U.ι ⋙ AsSmall.up

/-- Composition with the inclusion of an open subscheme is continuous for the étale topologies
of the one-universe models of the two small étale sites. -/
public instance opensInclusion_isContinuous :
    (opensInclusion S U).IsContinuous (MayerVietoris.topology U.toScheme)
      (MayerVietoris.topology S) :=
  have : (smallEtaleCompose U.ι ⋙ (AsSmall.up : S.Etale ⥤ MayerVietoris.Site S)).IsContinuous
      U.toScheme.smallEtaleTopology (MayerVietoris.topology S) :=
    Functor.isContinuous_comp _ _ _ S.smallEtaleTopology _
  Functor.isContinuous_comp _ _ _ U.toScheme.smallEtaleTopology _

/-- Composition with the inclusion of an open subscheme is cocontinuous for the étale topologies
of the one-universe models of the two small étale sites. -/
public instance opensInclusion_isCocontinuous :
    (opensInclusion S U).IsCocontinuous (MayerVietoris.topology U.toScheme)
      (MayerVietoris.topology S) :=
  have : (smallEtaleCompose U.ι ⋙ (AsSmall.up : S.Etale ⥤ MayerVietoris.Site S)).IsCocontinuous
      U.toScheme.smallEtaleTopology (MayerVietoris.topology S) :=
    isCocontinuous_comp _ _ _ S.smallEtaleTopology
  isCocontinuous_comp _ _ _ U.toScheme.smallEtaleTopology

/-- The final object of the small étale site of an open subscheme `U`, carried into the small
étale site of `S`, is `U` read as an object there: both have underlying scheme `U` and
structure morphism the inclusion. -/
public def opensInclusionSelfIso :
    (opensInclusion S U).obj (MayerVietoris.self U.toScheme) ≅
      (MayerVietoris.opensToSite S).obj U :=
  (AsSmall.up : S.Etale ⥤ MayerVietoris.Site S).mapIso
    (MorphismProperty.Over.isoMk (Iso.refl _) rfl)

/-- **The cohomology of a constant abelian sheaf over an open subscheme is the global cohomology
of the constant sheaf on that open subscheme.** More precisely, the vanishing of the global
cohomology of the constant sheaf with value `M` on the small étale site of `U` in degree `q`
gives the vanishing of the degree-`q` cohomology over `U`, read as an object of the small étale
site of `S`, of the constant sheaf with value `M` there.

Composition with the open immersion is a continuous and cocontinuous functor of the two
one-universe models which preserves fibre products and equalizers, so Stacks 03YU, statement 2,
identifies the cohomology over an object with the cohomology over its image; restriction carries
the constant sheaf to the constant sheaf, and the final object of the site of `U` is carried to
`U`. -/
public theorem subsingleton_H'_opensToSite (M : AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1}
      ((constantSheaf (MayerVietoris.topology U.toScheme) AddCommGrpCat.{u + 1}).obj M) q)) :
    Subsingleton (Sheaf.H'.{u + 1}
      ((constantSheaf (MayerVietoris.topology S) AddCommGrpCat.{u + 1}).obj M) q
      ((MayerVietoris.opensToSite S).obj U)) := by
  have : ∀ P : (MayerVietoris.Site U.toScheme)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (opensInclusion S U).op.HasPointwiseRightKanExtension P :=
    fun P => Stacks.Cohomology.BiggerSite.hasPointwiseRightKanExtension_op _ P
  have h1 : Subsingleton (Sheaf.H'.{u + 1}
      ((constantSheaf (MayerVietoris.topology U.toScheme) AddCommGrpCat.{u + 1}).obj M) q
      (MayerVietoris.self U.toScheme)) :=
    (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'
      (MayerVietoris.topology U.toScheme) _ q _ (MayerVietoris.selfIsTerminal U.toScheme)).1 h
  have e1 : (constantSheaf (MayerVietoris.topology U.toScheme) AddCommGrpCat.{u + 1}).obj M ≅
      ((opensInclusion S U).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (MayerVietoris.topology U.toScheme) (MayerVietoris.topology S)).obj
          ((constantSheaf (MayerVietoris.topology S) AddCommGrpCat.{u + 1}).obj M) :=
    ((Stacks.Cohomology.DenseSubsiteConstant.constantSheafPushforwardContinuousIso
      (MayerVietoris.topology U.toScheme) (MayerVietoris.topology S) (opensInclusion S U)
      AddCommGrpCat.{u + 1}).app M).symm
  have iso : Sheaf.H'.{u + 1}
      ((constantSheaf (MayerVietoris.topology U.toScheme) AddCommGrpCat.{u + 1}).obj M) q
        (MayerVietoris.self U.toScheme) ≅
      Sheaf.H'.{u + 1} ((constantSheaf (MayerVietoris.topology S) AddCommGrpCat.{u + 1}).obj M) q
        ((MayerVietoris.opensToSite S).obj U) :=
    ((Sheaf.cohomologyPresheafFunctor (MayerVietoris.topology U.toScheme) q).mapIso e1).app
        (op (MayerVietoris.self U.toScheme)) ≪≫
      (Stacks.Cohomology.BiggerSite.cohomologyPresheafFunctorIso
        (MayerVietoris.topology U.toScheme) (MayerVietoris.topology S) (opensInclusion S U)
        (MayerVietoris.self U.toScheme) q).app _ ≪≫
      (((constantSheaf (MayerVietoris.topology S) AddCommGrpCat.{u + 1}).obj M).cohomologyPresheaf
        q).mapIso (opensInclusionSelfIso S U).op.symm
  exact iso.symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton

end Opens

end Stacks.EtaleCohomology.ConstantTransport

end
