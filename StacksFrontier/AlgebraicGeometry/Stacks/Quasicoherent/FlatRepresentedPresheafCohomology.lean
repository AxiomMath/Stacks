module

public import StacksFrontier.AlgebraicGeometry.Stacks.ParasiticLisseEtaleVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticFlatSubsiteCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackTerminalSubsite
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor

/-!
# Cohomology over a presheaf represented by a flat 1-morphism

Let `𝒳` be an algebraic stack, `τ` the étale or the fppf topology, and `Z : 𝒯 ⟶ 𝒳` a flat
1-morphism of algebraic stacks whose underlying functor is faithful. The presheaf of sets on `𝒳`
represented by `Z` is the presheaf of components `Ψ(Z)` of
`Stacks.Sites.CoverDescent.componentPresheaf`, and `ℤ_{Ψ(Z)}` is the free abelian sheaf on it;
`Ext^n(ℤ_{Ψ(Z)}, A)` is the cohomology of `A` over `Ψ(Z)`, which is the cohomology of `Z⁻¹A` on
`𝒯`. This file proves that it vanishes in every degree as soon as `A` vanishes at the flat objects
of `𝒳`.

For the final presheaf this is `AlgebraicGeometry.Stack.isZero_functorH_of_subsingleton_flatObject`
again, and the proof is the same: the presheaves represented by flat 1-morphisms with faithful
underlying functor form a class closed under representable covers by flat objects
(`AlgebraicGeometry.Stack.isClosedUnderRepresentableCovers_flatRepresented`) — the cover of
`Ψ(Z)` is the distinguished object of a smooth surjective atlas `(Sch/D) ⟶ 𝒯`, which is a flat
object of `𝒳` because `Z` is flat, and the fibre powers are represented by the iterated 2-fibre
products `D ×_𝒯 ⋯ ×_𝒯 D`, flat over `𝒳` through their projections — so restriction to the flat
objects does not change cohomology over `Ψ(Z)` (the descent of
`StacksFrontier/CategoryTheory/Sites/Cohomology/CoverDescent/Cohomology.lean`), and the restriction
of `A` is zero.

## Main definitions

* `AlgebraicGeometry.Stack.FlatRepresented`: the class of presheaves on `𝒳` represented by a flat
  1-morphism of algebraic stacks with faithful underlying functor.

## Main results

* `AlgebraicGeometry.Stack.isClosedUnderRepresentableCovers_flatRepresented`: the class is closed
  under representable covers by flat objects.
* `AlgebraicGeometry.Stack.ext_freeAbelianSheaf_eq_zero_of_flatRepresented`: the cohomology over a
  member of the class of an abelian sheaf vanishing at the flat objects vanishes.

## References

* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 0775](https://stacks.math.columbia.edu/tag/0775)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open Stacks.Sites.CoverDescent

namespace AlgebraicGeometry.Stack

universe u w

attribute [-instance]
  Stacks.Cohomology.DerivedLowerShriek.preservesFiniteColimits_abelianRestriction
  Stacks.Cohomology.DerivedLowerShriek.preservesColimits_abelianRestriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The presheaves on `𝒳` represented by a flat 1-morphism with faithful underlying functor**:
`Ψ(Z)` for an algebraic stack `𝒯` and a flat 1-morphism `Z : 𝒯 ⟶ 𝒳` whose functor of underlying
categories is faithful. -/
def FlatRepresented (𝒳 : AlgebraicStacks.{u, w} B S hS) (G : 𝒳.val.val.objᵒᵖ ⥤ Type (u + 1)) :
    Prop :=
  ∃ (𝒯 : AlgebraicStacks.{u, w} B S hS) (Z : 𝒯 ⟶ 𝒳),
    (CatFiberedInGroupoids.homFunctor Z.hom).Faithful ∧ AlgebraicStacks.IsFlat B S hS Z ∧
      G = componentPresheaf (CatFiberedInGroupoids.homFunctor Z.hom)

variable (𝒳 : AlgebraicStacks.{u, w} B S hS) {τ : SiteKind}

/-- **The presheaves represented by flat 1-morphisms are closed under representable covers by
flat objects**, for the étale and the fppf topology. The presheaf `Ψ(Z)` represented by a flat
`Z : 𝒯 ⟶ 𝒳` with faithful underlying functor is covered by the image `y` of the distinguished
object of a smooth surjective atlas `e : (Sch/D) ⟶ 𝒯`, which is a flat object of `𝒳` because
`e ≫ Z` is flat; the fibre powers of the cover are represented by the iterated 2-fibre products
`D ×_𝒯 ⋯ ×_𝒯 D`, whose projections to `𝒯` are smooth, so whose projections to `𝒳` are flat, and
whose underlying functors are faithful. This is
`AlgebraicGeometry.Stack.isClosedUnderRepresentableCovers_smoothOverAtlas` with the class of the
presheaves represented over a presentation replaced by that of the flat ones. -/
theorem isClosedUnderRepresentableCovers_flatRepresented (hτ : τ = .etale ∨ τ = .fppf) :
    haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
      𝒳.val.val.p (flatObject B S hS 𝒳.val) τ 𝒳.val.isFiberedInGroupoids
      (isClosedUnderSitePullback_flatObject 𝒳 hτ)
    IsClosedUnderRepresentableCovers.{u + 1}
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
      ((FlatFppf.objectProperty B S hS 𝒳).ι.inheritedTopology
        (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ))
      (FlatFppf.objectProperty B S hS 𝒳).ι (FlatRepresented 𝒳) := by
  have hcl := isClosedUnderSitePullback_flatObject 𝒳 hτ
  have := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p (flatObject B S hS 𝒳.val) τ 𝒳.val.isFiberedInGroupoids hcl
  have := isCocontinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p (flatObject B S hS 𝒳.val) τ 𝒳.val.isFiberedInGroupoids hcl
  have hgen := @generatesCovering_of_isClosedUnderSitePullback B S hS 𝒳 τ
    (flatObject B S hS 𝒳.val) hcl
  intro F hF
  obtain ⟨𝒯, Z, hfaith, hflat, rfl⟩ := hF
  have hz : CatFiberedInGroupoids.homFunctor Z.hom ⋙ 𝒳.val.val.p = 𝒯.val.val.p := Z.hom.hom.w
  obtain ⟨D, e, hesm, hesurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒯
  have : (schemeStack.{u, w} B S hS D).val.val.p.Faithful :=
    inferInstanceAs (Over.forget D).Faithful
  have hy : flatObject B S hS 𝒳.val ((CatFiberedInGroupoids.homFunctor e.hom ⋙
      CatFiberedInGroupoids.homFunctor Z.hom).obj (Over.mk (𝟙 D))) :=
    FlatFppf.flatObject_map B S hS (e ≫ Z)
      (AlgebraicStacks.isFlat_comp B S hS e Z (AlgebraicStacks.isFlat_of_isSmooth B S hS e hesm)
        hflat) ⟨Over.mk (𝟙 D), flatObject_schemeStack_id.{u, w} B S hS D⟩
  let E₀ := componentPresheafIsoOfIsTerminal
    (CatFiberedInGroupoids.homFunctor e.hom ⋙ CatFiberedInGroupoids.homFunctor Z.hom)
    (Over.mkIdTerminal (X := D))
  have := isLocallySurjective_componentPresheafMap_atlas τ hgen
    (CatFiberedInGroupoids.homFunctor Z.hom) hz e hesm hesurj
  let t := E₀.inv ≫ componentPresheafMap (CatFiberedInGroupoids.homFunctor Z.hom)
    (CatFiberedInGroupoids.homFunctor e.hom) ≫ (Iso.refl _).hom
  have ht : Presheaf.IsLocallySurjective
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) t := inferInstance
  refine ⟨⟨_, hy⟩, t, ht, Presheaf.isLocallySurjective_whisker
    ((FlatFppf.objectProperty B S hS 𝒳).ι.inheritedTopology
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ))
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) (FlatFppf.objectProperty B S hS 𝒳).ι t,
    fun r => ?_⟩
  obtain ⟨E, -⟩ := exists_tuplePresheaf_iso_cechTower
    (CatFiberedInGroupoids.homFunctor Z.hom) hz e (r + 1)
  refine ⟨_, ⟨(cechTower B S hS e (r + 1)).1, (cechTower B S hS e (r + 1)).2 ≫ Z, ?_, ?_, rfl⟩,
    ⟨tuplePresheafCompIso E₀.symm _ (Iso.refl _) (r + 1) ≪≫ E⟩⟩
  · have := faithful_cechTower e (r + 1)
    exact Functor.Faithful.of_comp_eq ((cechTower B S hS e (r + 1)).2 ≫ Z).hom.hom.w
  · exact AlgebraicStacks.isFlat_comp B S hS _ Z
      (AlgebraicStacks.isFlat_of_isSmooth B S hS _ (isSmooth_cechTower e hesm (r + 1))) hflat

/-- **The cohomology over a presheaf represented by a flat 1-morphism of an abelian sheaf
vanishing at the flat objects vanishes**, in every degree, for `τ` the étale or the fppf
topology: `Ext^n(ℤ_G, A) = 0`.

Restriction to the flat objects identifies `Ext^n(ℤ_G, A)` with `Ext^n(ℤ_{G'}, A')` for the
restrictions `G'` and `A'` (`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIsoOfAcyclic`):
the comparison `g_! ℤ_{G'} ⟶ ℤ_G` is invertible and restriction carries injective abelian
sheaves to sheaves without higher cohomology over `G'`, both because `G` lies in a class closed
under representable covers by flat objects
(`AlgebraicGeometry.Stack.isClosedUnderRepresentableCovers_flatRepresented`). The restriction
`A'` of `A` is zero. -/
theorem ext_freeAbelianSheaf_eq_zero_of_flatRepresented (hτ : τ = .etale ∨ τ = .fppf)
    {G : 𝒳.val.val.objᵒᵖ ⥤ Type (u + 1)} (hG : FlatRepresented 𝒳 G)
    (A : Sheaf (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ)) AddCommGrpCat.{u + 1})
    (hA : ∀ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x → Subsingleton (A.obj.obj (op x)))
    (n : ℕ)
    (e : Ext.{u + 1} ((Presheaf.freeAbelianSheaf.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ))).obj G) A n) :
    e = 0 := by
  have hcl := isClosedUnderSitePullback_flatObject 𝒳 hτ
  have := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p (flatObject B S hS 𝒳.val) τ 𝒳.val.isFiberedInGroupoids hcl
  have := isCocontinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p (flatObject B S hS 𝒳.val) τ 𝒳.val.isFiberedInGroupoids hcl
  have := isRightAdjoint_subsiteRestriction_of_isClosedUnderSitePullback hcl
  have := preservesCoveringPullbacks_of_isClosedUnderSitePullback hcl
  have h𝔎 := isClosedUnderRepresentableCovers_flatRepresented 𝒳 hτ
  have hiso := isIso_freeComparison.{u + 1, u, u + 1, u + 1}
    (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ))
    (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) (FlatFppf.objectProperty B S hS 𝒳))
    (FlatFppf.objectProperty B S hS 𝒳).ι G
    (fun F hF => restrictHom_bijective_of_mem.{u + 1, u, u + 1, u + 1} _ h𝔎 hG F hF)
  have : PreservesFiniteColimits ((FlatFppf.objectProperty B S hS 𝒳).ι.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1}
      (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) (FlatFppf.objectProperty B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ))) :=
    have : PreservesColimitsOfSize.{0, 0}
        ((FlatFppf.objectProperty B S hS 𝒳).ι.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) (FlatFppf.objectProperty B S hS 𝒳))
        (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ))) :=
      ((FlatFppf.objectProperty B S hS 𝒳).ι.sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
        (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ)
          (FlatFppf.objectProperty B S hS 𝒳))
        (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ))).leftAdjoint_preservesColimits
    inferInstance
  let iso := Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIsoOfAcyclic
    ((FlatFppf.objectProperty B S hS 𝒳).ι.sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) (FlatFppf.objectProperty B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ)))
    (asIso (freeComparison.{u + 1, u, u + 1, u + 1}
      (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ))
      (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) (FlatFppf.objectProperty B S hS 𝒳))
      (FlatFppf.objectProperty B S hS 𝒳).ι G))
    (fun I _ m a => ext_restriction_eq_zero_of_mem.{u + 1, u + 1, u, u + 1} h𝔎
      (fun I _ d m c => subsiteObjectCohomology_eq_zero B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids (B.baseTopology τ) (FlatFppf.objectProperty B S hS 𝒳) I d m c)
      hG I m a) n
  have hz : IsZero ((subsiteRestriction B S hS 𝒳.val.val.p (B.baseTopology τ)
      (FlatFppf.objectProperty B S hS 𝒳)).obj A) := by
    have hz' : IsZero ((subsiteRestriction B S hS 𝒳.val.val.p (B.baseTopology τ)
        (FlatFppf.objectProperty B S hS 𝒳)).obj A).obj :=
      Functor.isZero _ fun x => @AddCommGrpCat.isZero_of_subsingleton _ (hA _ x.unop.property)
    exact (IsZero.iff_id_eq_zero _).2 (Sheaf.hom_ext (hz'.eq_of_src _ _))
  exact (AddCommGrpCat.subsingleton_of_isZero ((iso.app A).isZero_iff.2
    (Functor.map_isZero (extFunctorObj ((Presheaf.freeAbelianSheaf
      (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ)
        (FlatFppf.objectProperty B S hS 𝒳))).obj
          ((FlatFppf.objectProperty B S hS 𝒳).ι.op ⋙ G)) n) hz))).elim e 0

end AlgebraicGeometry.Stack

end
