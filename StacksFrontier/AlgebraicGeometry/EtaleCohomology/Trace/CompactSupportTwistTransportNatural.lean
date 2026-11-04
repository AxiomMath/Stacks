module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTwistTransport

/-!
# Transporting the canonical Frobenius along an identification, naturally

The isomorphism `Hⁱ_c(X_k̄, K) ≅ Hⁱ_c(X_k̄, K')` induced by an identification
`γ : (j_! K)|_Y ≅ (j_! K')|_Y` over `Y = X̄_k̄`
(`Stacks.EtaleCohomology.exists_addEquiv_compactSupportSheafCohomology_of_twist`) is composition
with `γ` on `Ext^i(Λ_Y, (j_! -)|_Y)`. So it also carries `a_*` to `a'_*` whenever `γ` intertwines
`(j_! a)|_Y` and `(j_! a')|_Y`, because `a_*` is composition with `(j_! a)|_Y`
(`Stacks.EtaleCohomology.compactSupportFrobeniusSingleIsoExt_hom_naturality`). This naturality
makes the computation of `H²_c` on a curve compatible with the endomorphisms of the coefficients,
which the `E`-linear form of [Tag 03VN](https://stacks.math.columbia.edu/tag/03VN) needs.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main results

* `Stacks.EtaleCohomology.exists_addEquiv_compactSupportSheafCohomology_of_twist_natural`:
  the isomorphism induced by `γ` intertwines the canonical Frobenius twisted by `b`, and carries
  `a_*` to `a'_*` for endomorphisms `a`, `a'` intertwined by `γ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  etaleModuleInverseImageSheafPullbackMonoidal etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- For a scheme `S`, the class of morphisms of presheaves of `Λ`-modules on the small étale site
of `S` that become isomorphisms after sheafification is compatible with the monoidal structure. -/
local instance (S : Scheme.{u}) : (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

/-- **Transport of the canonical Frobenius along an identification over `k̄`, naturally**: the
isomorphism `Hⁱ_c(X_k̄, K) ≅ Hⁱ_c(X_k̄, K')` induced by `γ` (as in
`Stacks.EtaleCohomology.exists_addEquiv_compactSupportSheafCohomology_of_twist`) carries `π_K^*` to
`b_* ∘ π_{K'}^*` and, for endomorphisms `a` of `K` and `a'` of `K'` which `γ` intertwines over `Y`,
carries `a_*` to `a'_*`. -/
theorem exists_addEquiv_compactSupportSheafCohomology_of_twist_natural
    {K K' : EtaleModules.{u, 0} Λ X}
    (γ : (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K) ≅
      (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K'))
    (b : K' ⟶ K')
    (hγ : (frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk j.toBase) kbar p q hcard).app
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K) ≫
        (etaleModuleDirectImage.{u, 0} Λ
          (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)).map γ.hom =
      γ.hom ≫ (frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk j.toBase) kbar p q hcard).app
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K') ≫
        (etaleModuleDirectImage.{u, 0} Λ
          (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)).map
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map b)))
    (i : ℕ) :
    ∃ e : (compactSupportSheafCohomology Λ f j kbar i).obj K ≃+
        (compactSupportSheafCohomology Λ f j kbar i).obj K',
      (∀ x, e (((compactSupportSheafFrobenius Λ f j kbar p q hcard i).app K).hom x) =
        ((compactSupportSheafCohomology Λ f j kbar i).map b).hom
          (((compactSupportSheafFrobenius Λ f j kbar p q hcard i).app K').hom (e x))) ∧
      ∀ (a : K ⟶ K) (a' : K' ⟶ K'),
        (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map a) ≫ γ.hom =
          γ.hom ≫ (etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map a') →
        ∀ x, e (((compactSupportSheafCohomology Λ f j kbar i).map a).hom x) =
          ((compactSupportSheafCohomology Λ f j kbar i).map a').hom (e x) := by
  have : EnoughInjectives (EtaleModules.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar)) :=
    etaleModules_enoughInjectives Λ _
  let I := etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)
  let E := etaleModuleExtensionByZero.{u, 0} Λ j.immersion
  let π := geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard
  let τ := frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk j.toBase) kbar p q hcard
  let Ψ : ∀ L : EtaleModules.{u, 0} Λ X, (compactSupportSheafCohomology Λ f j kbar i).obj L ≃+
      Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology) (I.obj (E.obj L)) i :=
    fun L => (compactSupportFrobeniusSingleIsoExt Λ f j kbar L i).addCommGroupIsoToAddEquiv
  let G := SmallEtale.extPostcompIsoAddEquiv.{u + 1}
    (X := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
      (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology) γ i
  have hπ : ∀ (L : EtaleModules.{u, 0} Λ X) y,
      Ψ L (((compactSupportSheafFrobenius Λ f j kbar p q hcard i).app L).hom y) =
      Stacks.ExtCup.adjunctionExtMap (etaleModuleInverseImage.{u, 0} Λ π)
        (etaleModuleDirectImage.{u, 0} Λ π) (etaleModuleInverseImageAdj.{u, 0} Λ π)
        (I.obj (E.obj L)) ((Ψ L y).comp (Ext.mk₀ (τ.app (E.obj L))) (add_zero i)) := fun L y => by
    have h := compactSupportFrobeniusSingleIsoExt_canonical_apply Λ f j kbar p q hcard L i (Ψ L y)
    rwa [show ((compactSupportFrobeniusSingleIsoExt Λ f j kbar L i).inv).hom (Ψ L y) = y from
      (Ψ L).symm_apply_apply y] at h
  have hG : ∀ w, G w = w.comp (Ext.mk₀ γ.hom) (add_zero i) := fun _ => rfl
  have hmap : ∀ (L : EtaleModules.{u, 0} Λ X) (a : L ⟶ L) z,
      Ψ L (((compactSupportSheafCohomology Λ f j kbar i).map a).hom z) =
      (Ψ L z).comp (Ext.mk₀ (I.map (E.map a))) (add_zero i) := fun L a z =>
    congrArg (fun φ => φ.hom z) (compactSupportFrobeniusSingleIsoExt_hom_naturality Λ f kbar j a i)
  refine ⟨((Ψ K).trans G).trans (Ψ K').symm, ?_, fun a a' haa x => (Ψ K').injective ?_⟩
  swap
  · simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
    rw [hmap K' a', AddEquiv.apply_symm_apply, hG, hG, hmap K a, Ext.comp_assoc_of_third_deg_zero,
      Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, haa]
  intro x
  apply (Ψ K').injective
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [hmap K' b, hπ K', AddEquiv.apply_symm_apply, hG, hG, hπ K]
  refine (Stacks.ExtCup.adjunctionExtMap_comp_mk₀ (etaleModuleInverseImage.{u, 0} Λ π)
    (etaleModuleDirectImage.{u, 0} Λ π) (etaleModuleInverseImageAdj.{u, 0} Λ π) γ.hom
    _).symm.trans (Eq.trans ?_ (Stacks.ExtCup.adjunctionExtMap_comp_mk₀
      (etaleModuleInverseImage.{u, 0} Λ π) (etaleModuleDirectImage.{u, 0} Λ π)
      (etaleModuleInverseImageAdj.{u, 0} Λ π) (I.map (E.map b)) _))
  refine congrArg (Stacks.ExtCup.adjunctionExtMap (etaleModuleInverseImage.{u, 0} Λ π)
      (etaleModuleDirectImage.{u, 0} Λ π) (etaleModuleInverseImageAdj.{u, 0} Λ π)
      (I.obj (E.obj K'))) ?_
  refine (Ext.comp_assoc_of_third_deg_zero _ _ _ _).trans ?_
  refine (congrArg (fun z => (Ψ K x).comp z (add_zero i)) (Ext.mk₀_comp_mk₀ _ _)).trans ?_
  refine (congrArg (fun g => (Ψ K x).comp (Ext.mk₀ g) (add_zero i)) hγ).trans ?_
  refine Eq.symm ((Ext.comp_assoc_of_third_deg_zero _ _ _ _).trans ?_)
  refine (congrArg (fun z => ((Ψ K x).comp (Ext.mk₀ γ.hom) (add_zero i)).comp z (add_zero i))
    (Ext.mk₀_comp_mk₀ _ _)).trans ?_
  refine (Ext.comp_assoc_of_third_deg_zero _ _ _ _).trans ?_
  exact congrArg (fun z => (Ψ K x).comp z (add_zero i)) (Ext.mk₀_comp_mk₀ _ _)

end Stacks.EtaleCohomology

end
