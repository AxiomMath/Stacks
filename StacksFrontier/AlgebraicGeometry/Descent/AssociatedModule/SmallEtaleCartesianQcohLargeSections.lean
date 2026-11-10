module

public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentLargeSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations

/-!
# Cartesian between affines implies quasi-coherent on a small étale site, at large module universes

`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_isCartesianOnAffines` says that a sheaf of
modules on the small étale site of a scheme whose base-change comparisons
`𝒪(T') ⊗_{𝒪(T)} 𝓕(T) ⟶ 𝓕(T')` are bijective between affine objects is quasi-coherent (the
direction "cartesian ⟹ quasi-coherent" of Descent, Proposition 03DX (2)); its proof goes through
the small Zariski site and is pinned to module sections in the universe `u` of the schemes. This
file proves the same at the module universe `max (u + 1) m`, with nothing assumed.

The route is the one of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentLargeSections`:
the
small étale site of a scheme `T` is the small étale site of the algebraic space it represents
(`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`, the structure sheaves agreeing by
`rfl`), quasi-coherence is invariant under that equivalence at every module universe
(`Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_transport_iff`), and on the side of the
algebraic space the chart criterion holds at every module universe
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts_anyUniverse`), its
base-change comparison being `Stacks.PresheafOfModules.restrictionBaseChange` along the image of
the chart morphism
(`AlgebraicGeometry.Space.bijective_sectionsBaseChange_iff_isIso_restrictionBaseChange`). An
arbitrary big étale site with the cutoff of the big fppf site is then reduced to the canonical one,
the two topologies being equal.

## Main results

* `isQuasicoherentOnSite_represented_of_bijective_restrictionBaseChange`: the criterion on the
  small étale site of the scheme underlying an object of the big fppf site.
* `isQuasicoherentOnSite_of_bijective_restrictionBaseChange_freeModuleUniverse`: the criterion on
  the small étale site of a scheme in any big étale site with the cutoff of a big fppf site, at
  module universe `max (u + 1) m`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
-/

@[expose] public section

open CategoryTheory

universe m u

namespace AlgebraicGeometry.SmallEtale

/-- **Cartesian between affines implies quasi-coherent, on the small étale site of a represented
scheme, at module universe `max (u + 1) m`.** For an object `U` of the big fppf site over `S`, a
sheaf of modules on the small étale site of the scheme underlying `U` whose base-change
comparisons are bijective along every morphism between affine objects is quasi-coherent. -/
theorem isQuasicoherentOnSite_represented_of_bijective_restrictionBaseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
    (G : SheafOfModules.{max (u + 1) m} (Space.representedSchemeStructureSheaf B S hS U))
    (hG : ∀ {T T' : SmallEtale (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
        U.left.property} (g : T ⟶ T'),
      AlgebraicGeometry.IsAffine ((toScheme _ _ _).obj T) →
        AlgebraicGeometry.IsAffine ((toScheme _ _ _).obj T') →
        Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u,
          max (u + 1) m} (R := commStructurePresheaf _ _ _) G.val g.op)) :
    G.IsQuasicoherentOnSite := by
  let e := Space.representedSmallEtaleEquivalence B S hS U
  rw [← Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_transport_iff.{u + 1, u, u, u, m}
    (J' := Space.SmallEtale.topology B S hS (yoneda.obj U))
    e (Space.representedSchemeStructureSheaf B S hS U) G]
  have hF := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U
  refine Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts_anyUniverse
    (F := yoneda.obj U) (hF := hF) _ fun U' V' hU hV f => ?_
  refine (Space.bijective_sectionsBaseChange_iff_isIso_restrictionBaseChange.{u, max (u + 1) m}
    B S hS _ hF _ f).2 ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact hG (e.functor.map f) hV hU

/-- The criterion only depends on the topology through a propositional equality: if it holds for
the sheaves of modules over `Rc` for the topology `J₂`, it holds for an equal topology `J₁`. -/
theorem isQuasicoherentOnSite_of_bijective_restrictionBaseChange_of_topology_eq
    {C : Type (u + 1)} [Category.{u} C] {J₁ J₂ : GrothendieckTopology C} (hJ : J₁ = J₂)
    (Rc : Cᵒᵖ ⥤ CommRingCat.{u}) (aff : C → Prop)
    (hs₁ : Presheaf.IsSheaf J₁ (Rc ⋙ forget₂ CommRingCat RingCat))
    (hs₂ : Presheaf.IsSheaf J₂ (Rc ⋙ forget₂ CommRingCat RingCat))
    (h : ∀ G : SheafOfModules.{max (u + 1) m}
        (⟨Rc ⋙ forget₂ CommRingCat RingCat, hs₂⟩ : Sheaf J₂ RingCat.{u}),
      (∀ {V V' : C} (g : V ⟶ V'), aff V → aff V' →
        Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u,
          max (u + 1) m} (R := Rc) G.val g.op)) → G.IsQuasicoherentOnSite)
    (G : SheafOfModules.{max (u + 1) m}
        (⟨Rc ⋙ forget₂ CommRingCat RingCat, hs₁⟩ : Sheaf J₁ RingCat.{u}))
    (hG : ∀ {V V' : C} (g : V ⟶ V'), aff V → aff V' →
        Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u,
          max (u + 1) m} (R := Rc) G.val g.op)) :
    G.IsQuasicoherentOnSite := by
  subst hJ
  exact h G hG

/-- The topology on the small étale site is generated by the pulled-back étale precoverage. -/
private theorem topology_eq_comap_toGrothendieck (E : BigEtaleSite.{u}) (T : Scheme.{u})
    (hT : E.Contains T) : topology E T hT =
    (((Scheme.etalePrecoverage.comap E.inclusion).comap
      (Over.forget (E.obj T hT))).comap (inclusion E T hT)).toGrothendieck := by
  rw [topology, smallEtale_precoverage_eq_comap E ⟨T, hT⟩,
    bigEtaleOver_precoverage_eq_comap E T hT, bigEtalePrecoverage_eq_comap E]

/-- **Descent, Proposition 03DX (2), "cartesian ⟹ quasi-coherent", at module universe
`max (u + 1) m`.** A sheaf of modules on the small étale site of a scheme `T`, in a big étale site
`E` with the cutoff of the big fppf site `B`, whose base-change comparisons
`𝒪(V') ⊗_{𝒪(V)} 𝓕(V) ⟶ 𝓕(V')` are bijective along every morphism `V' ⟶ V` between affine objects is
quasi-coherent. -/
theorem isQuasicoherentOnSite_of_bijective_restrictionBaseChange_freeModuleUniverse
    (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff) (T : Scheme.{u})
    (hT : E.Contains T)
    (G : SheafOfModules.{max (u + 1) m} (structureSheaf E T hT))
    (hG : ∀ {V V' : SmallEtale E T hT} (g : V ⟶ V'),
      AlgebraicGeometry.IsAffine ((toScheme E T hT).obj V) →
        AlgebraicGeometry.IsAffine ((toScheme E T hT).obj V') →
          Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u,
            max (u + 1) m} (R := commStructurePresheaf E T hT) G.val g.op)) :
    G.IsQuasicoherentOnSite := by
  have hT' : B.Contains T := lt_of_lt_of_eq hT h
  have hE := topology_eq_comap_toGrothendieck E T hT
  have hE' := topology_eq_comap_toGrothendieck (associatedBigEtaleSite B) T hT'
  cases E
  dsimp only at h
  subst h
  exact isQuasicoherentOnSite_of_bijective_restrictionBaseChange_of_topology_eq
    (hE.trans hE'.symm) (commStructurePresheaf _ T hT)
    (fun V => AlgebraicGeometry.IsAffine ((toScheme _ T hT).obj V))
    (structureSheaf _ T hT).property
    (Space.representedSchemeStructureSheaf B T hT' (Over.mk (𝟙 (B.obj hT')))).property
    (isQuasicoherentOnSite_represented_of_bijective_restrictionBaseChange.{m} B T hT'
      (Over.mk (𝟙 (B.obj hT')))) G hG

end AlgebraicGeometry.SmallEtale
