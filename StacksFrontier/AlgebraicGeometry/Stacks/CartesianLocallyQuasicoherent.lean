module

public import StacksFrontier.AlgebraicGeometry.Stacks.CartesianKernelFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineCharts
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesianQcoh
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigFppfQuasicoherentCriterion

/-!
# Local quasi-coherence from the cartesian condition, and kernels of quasi-coherent modules

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids. A module on `𝒳` is *locally
quasi-coherent* (**Stacks 06WJ**) when it is an étale sheaf whose restriction `x^*F|_{U_ét}` to
the small étale site of the scheme `U` below each object `x` is quasi-coherent. By the cartesian
criterion on small étale sites (Descent, Proposition 03DX (2),
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_isCartesianOnAffines`) the second clause
holds as soon as the base change comparisons `𝒪(y) ⊗_{𝒪(x)} F(x) ⟶ F(y)` are bijective along the
arrows `y ⟶ x` of `𝒳` lying over étale morphisms of affine schemes, these being the images of
the morphisms between affine objects of the small étale sites
(`AlgebraicGeometry.Stack.bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff`).

A quasi-coherent module on the fppf site of `𝒳` is cartesian between affine objects, and the
kernel of a map of two such modules is cartesian along every arrow lying over a flat morphism
of affine schemes (`AlgebraicGeometry.Stack.bijective_fibredSectionsBaseChange_kernel`), in
particular along every étale one. So the kernel, computed in the fppf modules, is locally
quasi-coherent, although it need not be quasi-coherent.

## Main results

* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_bijective_restrictionBaseChange`: an étale
  sheaf of modules cartesian along the arrows over étale morphisms of affine schemes is locally
  quasi-coherent.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_kernel_of_isCartesianBetweenAffines`: the
  kernel of a map of fppf modules cartesian between affine objects is locally quasi-coherent.

## References

* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GR9](https://stacks.math.columbia.edu/tag/0GR9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **The cartesian criterion for local quasi-coherence.** An étale sheaf of modules on `𝒳` whose
base change comparisons `𝒪(y) ⊗_{𝒪(x)} G(x) ⟶ G(y)` are bijective along every arrow `y ⟶ x`
lying over an étale morphism of affine schemes is locally quasi-coherent (Stacks 06WJ): its
restriction to the small étale site below each object is cartesian between affine objects,
hence quasi-coherent by Descent, Proposition 03DX (2). -/
theorem isLocallyQuasicoherent_of_bijective_restrictionBaseChange
    (G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (hG : ∀ ⦃x y : 𝒳⦄ (g : y ⟶ x), Etale ((BigFppfOver.toScheme B S hS).map (p.map g)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y)) →
      Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        G.val g.op)) :
    IsLocallyQuasicoherent B E h S hS p hp G.val :=
  ⟨G.isSheaf, fun x => ⟨restrictModuleToSmallEtale_isSheaf B E h S hS p hp x G.val G.isSheaf,
    SmallEtale.isQuasicoherentOnSite_of_isCartesianOnAffines E _ _ _ fun {T T'} g hT hT' =>
      (bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff B E h S hS p hp G.val x
        g).2 (hG _ (etale_etaleIndex_map B E h S hS p hp x g)
          (isAffine_etaleIndex_obj B E h S hS p hp x T' hT')
          (isAffine_etaleIndex_obj B E h S hS p hp x T hT))⟩⟩

/-- **The kernel of a map of fppf modules cartesian between affine objects is locally
quasi-coherent.** Let `φ : F ⟶ G` be a map of sheaves of modules on the fppf site of `𝒳`, both
cartesian between affine objects (for instance quasi-coherent, by
`AlgebraicGeometry.Stack.isCartesianBetweenAffines_of_isQuasicoherentOnSite`). The kernel of `φ`
computed in the fppf modules is an étale sheaf, and it is cartesian along every arrow lying over
an étale, hence flat, morphism of affine schemes, by
`AlgebraicGeometry.Stack.bijective_fibredSectionsBaseChange_kernel`; so it is locally
quasi-coherent by the cartesian criterion. -/
theorem isLocallyQuasicoherent_kernel_of_isCartesianBetweenAffines
    {F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl)}
    (hF : IsCartesianBetweenAffines hp F) (hG : IsCartesianBetweenAffines hp G) (φ : F ⟶ G) :
    IsLocallyQuasicoherent B E h S hS p hp (kernel φ).val := by
  let K : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)) :=
    ⟨(kernel φ).val, (kernel φ).isSheaf.of_le (associatedTopology_etale_le_fppf B S hS p)⟩
  refine isLocallyQuasicoherent_of_bijective_restrictionBaseChange B E h S hS p hp K
    fun x y g het hx hy => ?_
  have hflat : let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) g
      Module.Flat (fibredSectionRing B S hS p x) (fibredSectionRing B S hS p y) :=
    Scheme.Hom.flat_appTop _
  have hK := bijective_fibredSectionsBaseChange_kernel hp φ g (hF g hx hy) (hG g hx hy) hflat
  rwa [show (fibredSectionsBaseChange hp (kernel φ) g : _ → _) = _ from
    funext (fibredSectionsBaseChange_eq_restrictionBaseChange hp (kernel φ) g)] at hK

end AlgebraicGeometry.Stack

end
