module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatOverStackCechCovers
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCohomologyAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteGlobalCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor

/-!
# `Ext` out of the presheaf of a flat 1-morphism, on the flat-fppf site

Let `𝒳` be an algebraic stack over `S`, let `g : Sh(𝒳_flat,fppf) ⟶ Sh(𝒳_fppf)` be the morphism of
topoi of the flat-fppf site (**Stacks 0787**), and let `Ψ` be the presheaf of sets on `𝒳`
represented by a flat 1-morphism `z : 𝒯 ⟶ 𝒳` of algebraic stacks with faithful underlying
functor. This file proves

`Ext^n_{𝒳_fppf}(ℤ_Ψ, J) ≅ Ext^n_{𝒳_flat,fppf}(ℤ_{g^{-1}Ψ}, g^{-1}J)`

naturally in the abelian sheaf `J`, at coefficient universe `u + 1`. In particular `Ext^n(ℤ_Ψ, J)`
vanishes in every degree as soon as `g^{-1}J = 0`.

For `Ψ` the final presheaf this is the comparison of global cohomology of **Stacks 0GR0**; for `Ψ`
the presheaf represented by the projection `(Sch/V) ×_𝒴 𝒳 ⟶ 𝒳` of a flat object `y` of an algebraic
stack `𝒴` over the scheme `V`, it is the comparison of the cohomology of that 2-fibre product,
which is what the proof of **Stacks 0775** (2) needs.

## The proof

The two inputs of the universality of `Ext`
(`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIsoOfAcyclic`) are the two conclusions of
the descent of `StacksFrontier/CategoryTheory/Sites/Cohomology/CoverDescent/Cohomology.lean` for the
class `AlgebraicGeometry.Stack.FlatOverStack`, closed under representable covers by flat objects
by `AlgebraicGeometry.Stack.isClosedUnderRepresentableCovers_flatOverStack`: the comparison
`g_!(ℤ_{g^{-1}Ψ}) ≅ ℤ_Ψ` (`Stacks.Sites.CoverDescent.isIso_freeComparison`), and the acyclicity
of `g^{-1}I` against `ℤ_{g^{-1}Ψ}` for injective `I`
(`Stacks.Sites.CoverDescent.ext_restriction_eq_zero_of_mem`), the latter over the acyclicity of
restricted injectives over every flat object, **Stacks 0D6X**
(`AlgebraicGeometry.Stack.subsiteObjectCohomology_eq_zero`).

## Main results

* `AlgebraicGeometry.Stack.extFreeAbelianSheafFlatOverStackIso`: the comparison.
* `AlgebraicGeometry.Stack.ext_freeAbelianSheaf_eq_zero_of_isZero_subsiteRestriction`: the
  vanishing.

## References

* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 0GR0](https://stacks.math.columbia.edu/tag/0GR0)
* [Stacks Project, Tag 0775](https://stacks.math.columbia.edu/tag/0775)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open Stacks.Sites.CoverDescent

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **`Ext` out of the presheaf of a flat 1-morphism is computed on the flat-fppf site.** For a
member `Ψ` of `AlgebraicGeometry.Stack.FlatOverStack`,

`Ext^n(ℤ_Ψ, J) ≅ Ext^n(ℤ_{g^{-1}Ψ}, g^{-1}J)`

naturally in the abelian sheaf `J` on `𝒳_fppf`, where `g^{-1}` is restriction to the flat
objects. -/
def extFreeAbelianSheafFlatOverStackIso {Ψ : 𝒳.val.val.objᵒᵖ ⥤ Type (u + 1)}
    (hΨ : FlatOverStack 𝒳 Ψ) (n : ℕ) :
    haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
      𝒳.val.val.p (FlatFppf.objectProperty B S hS 𝒳) .fppf 𝒳.val.isFiberedInGroupoids
      (isClosedUnderSitePullback_flatObject 𝒳 (τ := .fppf) (Or.inr rfl))
    extFunctorObj.{u + 1} ((Presheaf.freeAbelianSheaf.{u + 1}
        (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology .fppf))).obj Ψ) n ≅
      subsiteRestriction B S hS 𝒳.val.val.p (B.baseTopology .fppf)
          (FlatFppf.objectProperty B S hS 𝒳) ⋙
        extFunctorObj.{u + 1} ((Presheaf.freeAbelianSheaf.{u + 1}
          (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology .fppf)
            (FlatFppf.objectProperty B S hS 𝒳))).obj
              ((FlatFppf.objectProperty B S hS 𝒳).ι.op ⋙ Ψ)) n :=
  let P := FlatFppf.objectProperty B S hS 𝒳
  let hcl := isClosedUnderSitePullback_flatObject 𝒳 (τ := .fppf) (Or.inr rfl)
  haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p P .fppf 𝒳.val.isFiberedInGroupoids hcl
  haveI := isCocontinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p P .fppf 𝒳.val.isFiberedInGroupoids hcl
  haveI := isRightAdjoint_subsiteRestriction_of_isClosedUnderSitePullback hcl
  haveI := preservesCoveringPullbacks_of_isClosedUnderSitePullback hcl
  haveI : PreservesFiniteColimits (subsiteRestriction B S hS 𝒳.val.val.p
      (B.baseTopology .fppf) P) :=
    @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _ _
      ((P.ι.sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
        (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology .fppf) P)
        (associatedTopology B S hS 𝒳.val.val.p
          (B.baseTopology .fppf))).leftAdjoint_preservesColimits.{0, 0})
  have h𝔎 := isClosedUnderRepresentableCovers_flatOverStack 𝒳
  have := isIso_freeComparison.{u + 1, u, u + 1, u + 1}
    (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology .fppf))
    (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology .fppf) P) P.ι Ψ
    (fun F hF => restrictHom_bijective_of_mem.{u + 1, u, u + 1, u + 1} _ h𝔎 hΨ F hF)
  Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIsoOfAcyclic
    (P.ι.sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology .fppf) P)
      (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology .fppf)))
    (asIso (freeComparison.{u + 1, u, u + 1, u + 1}
      (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology .fppf))
      (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology .fppf) P) P.ι Ψ))
    (fun I _ m c => ext_restriction_eq_zero_of_mem.{u + 1, u + 1, u, u + 1} h𝔎
      (fun I _ d m c => subsiteObjectCohomology_eq_zero B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids (B.baseTopology .fppf) P I d m c) hΨ I m c) n

/-- **`Ext` out of the presheaf of a flat 1-morphism vanishes on a sheaf whose restriction to the
flat objects vanishes.** -/
theorem ext_freeAbelianSheaf_eq_zero_of_isZero_subsiteRestriction
    {Ψ : 𝒳.val.val.objᵒᵖ ⥤ Type (u + 1)} (hΨ : FlatOverStack 𝒳 Ψ)
    (J : Sheaf (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology .fppf))
      AddCommGrpCat.{u + 1})
    (hJ : ∀ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x → IsZero (J.obj.obj (op x)))
    (n : ℕ) (e : Ext.{u + 1} ((Presheaf.freeAbelianSheaf.{u + 1}
        (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology .fppf))).obj Ψ) J n) :
    e = 0 := by
  have := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p (FlatFppf.objectProperty B S hS 𝒳) .fppf 𝒳.val.isFiberedInGroupoids
    (isClosedUnderSitePullback_flatObject 𝒳 (τ := .fppf) (Or.inr rfl))
  have hJ' : IsZero ((subsiteRestriction B S hS 𝒳.val.val.p (B.baseTopology .fppf)
      (FlatFppf.objectProperty B S hS 𝒳)).obj J) := by
    rw [IsZero.iff_id_eq_zero]
    refine Sheaf.hom_ext (NatTrans.ext (funext fun x => ?_))
    exact (hJ x.unop.obj x.unop.property).eq_of_src _ _
  have h := ((extFreeAbelianSheafFlatOverStackIso 𝒳 hΨ n).app J).addCommGroupIsoToAddEquiv
  have hz : ∀ a : Ext.{u + 1} ((Presheaf.freeAbelianSheaf.{u + 1}
      (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology .fppf)
        (FlatFppf.objectProperty B S hS 𝒳))).obj
          ((FlatFppf.objectProperty B S hS 𝒳).ι.op ⋙ Ψ))
      ((subsiteRestriction B S hS 𝒳.val.val.p (B.baseTopology .fppf)
        (FlatFppf.objectProperty B S hS 𝒳)).obj J) n, a = 0 :=
    fun a => by
      have h1 : 𝟙 ((subsiteRestriction B S hS 𝒳.val.val.p (B.baseTopology .fppf)
          (FlatFppf.objectProperty B S hS 𝒳)).obj J) = 0 := hJ'.eq_of_src _ _
      rw [← Ext.comp_mk₀_id a, h1, Ext.mk₀_zero, Ext.comp_zero]
  exact h.injective ((hz _).trans (map_zero h).symm)

end AlgebraicGeometry.Stack

end
