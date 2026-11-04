module

public import StacksFrontier.AlgebraicGeometry.Stacks.ParasiticLisseEtaleVanishing

/-!
# Parasitic modules are those vanishing on a smooth chart (Stacks 0779, part (1))

Let `𝒳` be an algebraic stack, let `a : U ⟶ 𝒳` be a smooth surjective atlas by a scheme and let
`x = a(𝟙_U)` be the object of `𝒳` it names.  The proof of **Stacks 0779** part (1) observes that
an `𝒪_𝒳`-module `𝓕` with the flat base change property is parasitic (**Stacks 0773**) if and only
if its restriction `𝓕|_{U_étale}` to the small étale site of `U` vanishes.

The flat base change property enters through one consequence only, which is all this file asks
of `𝓕`: the vanishing of a restriction moves down an arrow lying over a flat morphism of schemes
(`AlgebraicGeometry.Stack.MovesVanishingDownFlatArrows`).  For the presheaf-level comparison map
of **Stacks 0761** this is
`AlgebraicGeometry.Stack.LisseEtale.isZero_restrictModuleToSmallEtale_of_flat_arrow`, and it
holds equally for a sheafified comparison map, the inverse image of a zero module being zero.

* If `𝓕` is parasitic, its restriction to `U_étale` evaluates it at objects lying over schemes
  étale over `U`, hence flat over `𝒳`, so it vanishes.
* Conversely a flat object `z` is covered, in the étale topology, by a single arrow out of an
  object `t` mapping to `x` over a flat morphism of schemes
  (`AlgebraicGeometry.Stack.exists_covering_flat_arrow_atlas_of_flatObject`, which is the
  source's `W = V ×_𝒳 U`); the vanishing moves from `x` to `t`, so the sections at `t` vanish,
  and so do those at `z` because `𝓕` is an étale sheaf.

## Main definitions

* `AlgebraicGeometry.Stack.MovesVanishingDownFlatArrows`

## Main results

* `AlgebraicGeometry.Stack.isZero_restrictModuleToSmallEtale_of_isParasitic`
* `AlgebraicGeometry.Stack.isParasitic_of_isZero_restrictModuleToSmallEtale_atlas`
* `AlgebraicGeometry.Stack.isParasitic_iff_isZero_restrictModuleToSmallEtale_atlas`

## References

* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 07AR](https://stacks.math.columbia.edu/tag/07AR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- A presheaf of `𝒪_𝒳`-modules *moves vanishing down flat arrows* when, for every arrow
`φ : x ⟶ y` of `𝒳` lying over a flat morphism of schemes, the vanishing of its restriction to
the small étale site below `y` implies the vanishing of its restriction below `x`.  This is the
consequence of the flat base change property (**Stacks 0762**) that **Stacks 0779** part (1)
uses. -/
def MovesVanishingDownFlatArrows {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)).obj) : Prop :=
  ∀ ⦃x y : 𝒳.val.val.obj⦄ (φ : x ⟶ y), Flat (B.inclusion.map (𝒳.val.val.p.map φ).left) →
    IsZero (restrictModuleToSmallEtale B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids y
      (etaleTopology B) (etaleTopology_le_topology B) F) →
    IsZero (restrictModuleToSmallEtale B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x
      (etaleTopology B) (etaleTopology_le_topology B) F)

/-- The flat base change property of **Stacks 0762**, in its presheaf form, moves vanishing down
flat arrows. -/
theorem movesVanishingDownFlatArrows_of_hasFlatBaseChangeProperty
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hfbc : HasFlatBaseChangeProperty B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B) F) :
    MovesVanishingDownFlatArrows B E h S hS F :=
  fun _ _ φ hφ hy =>
    LisseEtale.isZero_restrictModuleToSmallEtale_of_flat_arrow B E h S hS F hfbc φ hφ hy

/-- **A parasitic module restricts to zero below a flat object.**  The restriction evaluates the
module at the objects of `𝒳` named by the small étale site of the scheme below `x`, which are
flat objects by `AlgebraicGeometry.Stack.flatObject_smallEtaleToStack_obj`. -/
theorem isZero_restrictModuleToSmallEtale_of_isParasitic {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : IsParasitic.{u, w, u} B S hS 𝒳 .etale F) (x : 𝒳.val.val.obj)
    (hx : flatObject B S hS 𝒳.val x) :
    IsZero (restrictModuleToSmallEtale B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x
      (etaleTopology B) (etaleTopology_le_topology B) F) := by
  rw [PresheafOfModules.isZero_iff_forall_isZero_obj]
  intro V
  exact @ModuleCat.isZero_of_subsingleton _ _ _
    (hF ((smallEtaleToStack B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x).obj V.unop)
      (flatObject_smallEtaleToStack_obj B E h S hS x hx V.unop))

/-- **A module vanishing on a smooth chart is parasitic** (**Stacks 0779** part (1), the
substantial direction of `𝓕|_{U_étale} = 0 ⟺ 𝓕` parasitic), for an étale sheaf of modules
which moves vanishing down flat arrows. -/
theorem isParasitic_of_isZero_restrictModuleToSmallEtale_atlas
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {U : BigFppfOver B S hS}
    (a : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hasm : AlgebraicStacks.IsSmooth B S hS a)
    (hasurj : IsSurjective B S hS a)
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hsheaf : Presheaf.IsSheaf
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) F.presheaf)
    (hF : MovesVanishingDownFlatArrows B E h S hS F)
    (hU : IsZero (restrictModuleToSmallEtale B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      ((CatFiberedInGroupoids.homFunctor a.hom).obj (Over.mk (𝟙 U)))
      (etaleTopology B) (etaleTopology_le_topology B) F)) :
    IsParasitic.{u, w, u} B S hS 𝒳 .etale F := by
  intro z hz
  obtain ⟨t, α, ψ, hψ, hα⟩ :=
    exists_covering_flat_arrow_atlas_of_flatObject B S hS 𝒳 a hasm hasurj hz
  exact subsingleton_of_isZero_of_covering_arrow B S hS F hsheaf α
    (LisseEtale.subsingleton_of_isZero_restrictModuleToSmallEtale B E h S hS F t
      (hF ψ hψ hU)) hα

/-- **Stacks 0779, part (1), the chart criterion.**  For a smooth surjective atlas
`a : U ⟶ 𝒳`, an étale sheaf of `𝒪_𝒳`-modules which moves vanishing down flat arrows — for
instance one with the flat base change property — is parasitic if and only if its restriction
to the small étale site of `U` vanishes. -/
theorem isParasitic_iff_isZero_restrictModuleToSmallEtale_atlas
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {U : BigFppfOver B S hS}
    (a : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hasm : AlgebraicStacks.IsSmooth B S hS a)
    (hasurj : IsSurjective B S hS a)
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hsheaf : Presheaf.IsSheaf
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) F.presheaf)
    (hF : MovesVanishingDownFlatArrows B E h S hS F) :
    IsParasitic.{u, w, u} B S hS 𝒳 .etale F ↔
      IsZero (restrictModuleToSmallEtale B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        ((CatFiberedInGroupoids.homFunctor a.hom).obj (Over.mk (𝟙 U)))
        (etaleTopology B) (etaleTopology_le_topology B) F) :=
  ⟨fun hpar => isZero_restrictModuleToSmallEtale_of_isParasitic B E h S hS F hpar _
      (flatObject_of_smoothObject.{u, w} B S hS 𝒳 (smoothObject_atlas_obj.{u, w} B S hS a hasm)),
    isParasitic_of_isZero_restrictModuleToSmallEtale_atlas B E h S hS a hasm hasurj F hsheaf hF⟩

end AlgebraicGeometry.Stack

end
