module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportExtNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTowerExcision
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.MultiplicativeFirstCohomology

/-!
# Transporting the canonical Frobenius along an identification of the restrictions

Let `k` be a finite field, `X` a `k`-scheme with a compactification `j : X ⟶ X̄`, `k̄` an
extension of `k`, `Y = X̄_k̄`, `π̄ : Y ⟶ Y` the base change of the geometric Frobenius of `X̄`, and
for a sheaf `K` of `Λ`-modules on `X_étale` let `τ_K : (j_! K)|_Y ⟶ π̄_* (j_! K)|_Y` be the base
change of the Frobenius descent isomorphism. Let `K, K'` be two sheaves on `X`,
`γ : (j_! K)|_Y ≅ (j_! K')|_Y` an isomorphism over `Y` (not necessarily defined over `k`) and
`b : K' ⟶ K'` an endomorphism such that `γ` carries `τ_K` to `τ_{K'}` followed by
`π̄_*(j_! b)|_Y`:

`τ_K ≫ π̄_* γ = γ ≫ τ_{K'} ≫ π̄_* (j_! b)|_Y`.

Then `γ` induces an isomorphism `Hⁱ_c(X_k̄, K) ≅ Hⁱ_c(X_k̄, K')` carrying the canonical Frobenius
`π_K^*` to `b_* ∘ π_{K'}^*`.

## Main results

* `Stacks.EtaleCohomology.exists_addEquiv_compactSupportSheafCohomology_of_twist`: an isomorphism
  `γ` as above induces an isomorphism `Hⁱ_c(X_k̄, K) ≅ Hⁱ_c(X_k̄, K')` carrying `π_K^*` to
  `b_* ∘ π_{K'}^*`.
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

/-- The morphisms of étale presheaves of `Λ`-modules on `S` which become isomorphisms after
sheafification form a monoidal class. -/
local instance (S : Scheme.{u}) : (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

/-- **Transport of the canonical Frobenius along an identification over `k̄`.** If
`γ : (j_! K)|_{X̄_k̄} ≅ (j_! K')|_{X̄_k̄}` carries the Frobenius twist of `K` to that of `K'`
followed by `b : K' ⟶ K'`, then `Hⁱ_c(X_k̄, K) ≅ Hⁱ_c(X_k̄, K')` carries `π_K^*` to
`b_* ∘ π_{K'}^*`. -/
theorem exists_addEquiv_compactSupportSheafCohomology_of_twist {K K' : EtaleModules.{u, 0} Λ X}
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
      ∀ x, e (((compactSupportSheafFrobenius Λ f j kbar p q hcard i).app K).hom x) =
        ((compactSupportSheafCohomology Λ f j kbar i).map b).hom
          (((compactSupportSheafFrobenius Λ f j kbar p q hcard i).app K').hom (e x)) := by
  have : EnoughInjectives (EtaleModules.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar)) :=
    etaleModules_enoughInjectives Λ _
  let I := etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)
  let E := etaleModuleExtensionByZero.{u, 0} Λ j.immersion
  let π := geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard
  let τ := frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk j.toBase) kbar p q hcard
  let Ψ (M : EtaleModules.{u, 0} Λ X) : (compactSupportSheafCohomology Λ f j kbar i).obj M ≃+
      Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology) (I.obj (E.obj M)) i :=
    (compactSupportFrobeniusSingleIsoExt Λ f j kbar M i).addCommGroupIsoToAddEquiv
  let G := SmallEtale.extPostcompIsoAddEquiv.{u + 1}
    (X := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
      (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology) γ i
  have hπ : ∀ M y, Ψ M (((compactSupportSheafFrobenius Λ f j kbar p q hcard i).app M).hom y) =
      Stacks.ExtCup.adjunctionExtMap (etaleModuleInverseImage.{u, 0} Λ π)
        (etaleModuleDirectImage.{u, 0} Λ π) (etaleModuleInverseImageAdj.{u, 0} Λ π)
        (I.obj (E.obj M)) ((Ψ M y).comp (Ext.mk₀ (τ.app (E.obj M))) (add_zero i)) :=
    fun M y => by
    have h := compactSupportFrobeniusSingleIsoExt_canonical_apply Λ f j kbar p q hcard M i (Ψ M y)
    rwa [show ((compactSupportFrobeniusSingleIsoExt Λ f j kbar M i).inv).hom (Ψ M y) = y from
      (Ψ M).symm_apply_apply y] at h
  have hb : ∀ z, Ψ K' (((compactSupportSheafCohomology Λ f j kbar i).map b).hom z) =
      (Ψ K' z).comp (Ext.mk₀ (I.map (E.map b))) (add_zero i) := fun z =>
    congrArg (fun φ => φ.hom z) (compactSupportFrobeniusSingleIsoExt_hom_naturality Λ f kbar j b i)
  refine ⟨((Ψ K).trans G).trans (Ψ K').symm, fun x => (Ψ K').injective ?_⟩
  have hG : ∀ w, G w = w.comp (Ext.mk₀ γ.hom) (add_zero i) := fun _ => rfl
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [hb, hπ K', AddEquiv.apply_symm_apply, hG, hG, hπ K]
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
