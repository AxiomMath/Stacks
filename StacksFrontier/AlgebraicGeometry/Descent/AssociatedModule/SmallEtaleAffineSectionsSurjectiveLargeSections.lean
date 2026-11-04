module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentLargeSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleExtensionQuasicoherent

/-!
# Sections over affine objects of a short exact sequence with quasi-coherent kernel

Let `T` be a scheme in a big étale site `E` and `0 ⟶ 𝓕₁ ⟶ 𝓕₂ ⟶ 𝓕₃ ⟶ 0` a short exact sequence of
modules on the small étale site `T_ét` whose first term is quasi-coherent. Then for every object
`W` of `T_ét` with affine underlying scheme, `𝓕₂(W) ⟶ 𝓕₃(W)` is surjective: the first étale
cohomology of a quasi-coherent module vanishes on affine objects. This file proves it with the
sections of the modules in the universe `max (u + 1) m`, in which the stacks chapters read
their direct images.

The statement is transported from the small étale site of the algebraic space represented by `T`,
where it is `AlgebraicGeometry.Space.surjective_g_val_app_of_shortExact_of_isQuasicoherentOnSite`,
along the equivalence of ringed sites `AlgebraicGeometry.Space.representedSmallEtaleEquivalence`,
in the same way as the closure properties of quasi-coherence.

## Main results

* `AlgebraicGeometry.SmallEtale.surjective_val_app_of_shortExact_freeModuleUniverse`: the
  surjectivity, for an arbitrary big étale site with the cutoff of a big fppf site.

## References

* [Stacks Project, Tag 03OJ](https://stacks.math.columbia.edu/tag/03OJ)
* [Stacks Project, Tag 03F8](https://stacks.math.columbia.edu/tag/03F8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe m u

namespace AlgebraicGeometry.SmallEtale

/-- Surjectivity on the sections over the objects of a class, of the right-hand map of a short
exact sequence of modules whose left term is quasi-coherent, at the module universe
`max (u + 1) m`. -/
abbrev SurjectiveOnSectionsFreeModuleUniverse {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) (aff : C → Prop) : Prop :=
  ∀ T : ShortComplex (SheafOfModules.{max (u + 1) m} R), T.ShortExact →
    T.X₁.IsQuasicoherentOnSite → ∀ W : C, aff W → Function.Surjective (T.g.val.app (op W))

/-- The surjectivity only depends on the underlying presheaf of rings and on the topology, which
may be given by two propositionally equal terms. -/
theorem surjectiveOnSectionsFreeModuleUniverse_of_eq {C : Type (u + 1)} [Category.{u} C]
    {J₁ J₂ : GrothendieckTopology C} (hJ : J₁ = J₂) (R₁ : Sheaf J₁ RingCat.{u})
    (R₂ : Sheaf J₂ RingCat.{u}) (hR : R₁.obj = R₂.obj) (aff : C → Prop)
    (h : SurjectiveOnSectionsFreeModuleUniverse.{m} R₂ aff) :
    SurjectiveOnSectionsFreeModuleUniverse.{m} R₁ aff := by
  subst hJ
  obtain rfl : R₁ = R₂ := by
    cases R₁
    cases R₂
    cases hR
    rfl
  exact h

/-- Surjectivity of a morphism of presheaves of modules on the sections over an object transfers
along an isomorphism of objects. -/
theorem surjective_app_of_iso {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {X Y : PresheafOfModules.{m} R} (g : X ⟶ Y) {W W' : C} (c : W' ≅ W)
    (hs : Function.Surjective (g.app (op W'))) : Function.Surjective (g.app (op W)) := by
  intro y
  obtain ⟨z, hz⟩ := hs (Y.map c.hom.op y)
  refine ⟨X.map c.inv.op z, ?_⟩
  rw [PresheafOfModules.naturality_apply g c.inv.op z, hz, ← PresheafOfModules.map_comp_apply,
    ← op_comp, c.inv_hom_id, op_id, PresheafOfModules.map_id_apply]

/-- **The surjectivity on the small étale site of a represented scheme.** -/
theorem surjectiveOnSectionsFreeModuleUniverse_represented (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS) :
    SurjectiveOnSectionsFreeModuleUniverse.{m} (Space.representedSchemeStructureSheaf B S hS U)
      (fun W => AlgebraicGeometry.IsAffine ((toScheme _ _ _).obj W)) := by
  intro T hT h₁ W hW
  let e := Space.representedSmallEtaleEquivalence B S hS U
  let Φ : SheafOfModules.{max (u + 1) m} (Space.representedSchemeStructureSheaf B S hS U) ≌
      SheafOfModules.{max (u + 1) m} (Space.representedStructureRingSheaf B S hS U) :=
    Stacks.SheafOfModules.reindexEquivalence e (Space.representedSchemeStructureSheaf B S hS U)
  have : Φ.functor.IsLeftAdjoint := Φ.toAdjunction.isLeftAdjoint
  have : Φ.functor.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  let T' := T.map Φ.functor
  have h₁' : T'.X₁.IsQuasicoherentOnSite :=
    (Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_transport_iff.{u + 1, u, u, u, m}
      e (Space.representedSchemeStructureSheaf B S hS U) T.X₁).2 h₁
  let c := e.counitIso.app W
  have hW' : AlgebraicGeometry.IsAffine ((Space.SmallEtale.toOver B S hS (yoneda.obj U) ⋙
      BigFppfOver.toScheme B S hS).obj (e.inverse.obj W)) :=
    have hc : IsIso ((toScheme _ _ _).map c.hom) := Functor.map_isIso _ _
    @IsAffine.of_isIso _ _ ((toScheme _ _ _).map c.hom) hc hW
  exact surjective_app_of_iso T.g.val c
    (Space.surjective_g_val_app_of_shortExact_of_isQuasicoherentOnSite.{m, u} B S hS
      (yoneda.obj U) (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) T'
      (hT.map_of_exact Φ.functor) h₁' (e.inverse.obj W) hW')

/-- **Sections over affine objects of a short exact sequence with quasi-coherent kernel, at the
module universe `max (u + 1) m`.** For a short exact sequence `0 ⟶ 𝓕₁ ⟶ 𝓕₂ ⟶ 𝓕₃ ⟶ 0` of modules on
the small étale site of a scheme with `𝓕₁` quasi-coherent, `𝓕₂(W) ⟶ 𝓕₃(W)` is surjective for every
object `W` with affine underlying scheme. -/
theorem surjective_val_app_of_shortExact_freeModuleUniverse (B : BigFppfSite.{u})
    (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff) (T : Scheme.{u}) (hT : E.Contains T)
    (Tc : ShortComplex (SheafOfModules.{max (u + 1) m} (structureSheaf E T hT)))
    (hTc : Tc.ShortExact) (h₁ : Tc.X₁.IsQuasicoherentOnSite) (W : SmallEtale E T hT)
    (hW : AlgebraicGeometry.IsAffine ((toScheme E T hT).obj W)) :
    Function.Surjective (Tc.g.val.app (op W)) := by
  have hT' : B.Contains T := lt_of_lt_of_eq hT h
  have key := surjectiveOnSectionsFreeModuleUniverse_represented.{m} B T hT'
    (Over.mk (𝟙 (B.obj hT')))
  have hE : topology E T hT = (((Scheme.etalePrecoverage.comap E.inclusion).comap
      (Over.forget (E.obj T hT))).comap (inclusion E T hT)).toGrothendieck := by
    rw [topology, smallEtale_precoverage_eq_comap E ⟨T, hT⟩,
      bigEtaleOver_precoverage_eq_comap E T hT, bigEtalePrecoverage_eq_comap E]
  have hE' : topology (associatedBigEtaleSite B) T hT' =
      (((Scheme.etalePrecoverage.comap (associatedBigEtaleSite B).inclusion).comap
        (Over.forget ((associatedBigEtaleSite B).obj T hT'))).comap
          (inclusion (associatedBigEtaleSite B) T hT')).toGrothendieck := by
    rw [topology, smallEtale_precoverage_eq_comap (associatedBigEtaleSite B) ⟨T, hT'⟩,
      bigEtaleOver_precoverage_eq_comap (associatedBigEtaleSite B) T hT',
      bigEtalePrecoverage_eq_comap (associatedBigEtaleSite B)]
  cases E
  dsimp only at h
  subst h
  exact surjectiveOnSectionsFreeModuleUniverse_of_eq (hE.trans hE'.symm) (structureSheaf _ T hT)
    (Space.representedSchemeStructureSheaf B T hT' (Over.mk (𝟙 (B.obj hT')))) rfl _ key
    Tc hTc h₁ W hW

end AlgebraicGeometry.SmallEtale

end
