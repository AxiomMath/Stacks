module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleModuleExtTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusUniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImageMonoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleFlatTensorExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImageMonoidalUnit

/-!
# The canonical geometric Frobenius on `Hⁱ_c(X_k̄, K) = Ext^i(Λ, (j_! K)|_{X̄_k̄})`

Let `k` be a finite field, `X` a `k`-scheme with a compactification `j : X ⟶ X̄`, `k̄` an extension
of `k`, `Y = X̄_k̄`, `π̄ : Y ⟶ Y` the base change of the geometric Frobenius of `X̄` (a universal
homeomorphism), `K` a sheaf of `Λ`-modules on `X_étale` and `N = (j_! K)|_Y`. Under
`Hⁱ_c(X_k̄, K) ≅ Ext^i(Λ_Y, N)` (`Stacks.EtaleCohomology.compactSupportFrobeniusSingleIsoExt`) the
canonical endomorphism `π_X^*` of `Stacks.EtaleCohomology.canonicalCompactSupportFrobeniusGroup`
is `b ↦ θ(b ∘ τ)`, where `τ : N ⟶ π̄_* N` is the base change of the Frobenius descent isomorphism
of [Stacks, Tag 03SR] and `θ = Stacks.ExtCup.adjunctionExtMap` is
`Ext^i(Λ_Y, π̄_* N) ⟶ Ext^i(Λ_Y, N)`, `b ↦ ε_N ∘ π̄⁻¹(b)`
(`compactSupportFrobeniusSingleIsoExt_conj_canonical`); by
`Stacks.ExtCup.twistAction_homEquiv_symm` this is the twisted action
`Stacks.ExtCup.twistAction π̄⁻¹ σ` with `σ : π̄⁻¹ N ⟶ N` adjoint to `τ`, which commutes with cup
products (`Stacks.ExtCup.twistAction_cup`).

The identification is proved under one hypothesis `hσ`, the compatibility, in degree zero, of the
identification `Γ(Y, π̄_* -) ≅ Γ(Y, -)` underlying the canonical Frobenius with the lax unit
`Λ_Y ⟶ π̄⁻¹ Λ_Y` of the monoidal inverse image, read through the corepresentation of global
sections by `Λ_Y`. It is item (1) of the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), with `hσ` the remaining input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

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

/-- **Item (1) of the purity half of Tag 03VH, given `hσ`.** Under
`Hⁱ_c(X_k̄, K) ≅ Ext^i(Λ_Y, N)`, the canonical geometric Frobenius is `b ↦ θ(b ∘ τ)`. -/
theorem compactSupportFrobeniusSingleIsoExt_conj_canonical
    [(((fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology).W
      (A := ModuleCat.{u + 1} Λ)).IsMonoidal]
    (hσ : Functor.whiskerRight (Functor.twistEdgeIso
          (etaleModuleDirectImage.{u, 0} Λ
            (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
          (etaleModuleDirectImage.{u, 0} Λ
            (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
          (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
          (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar))
          (frobeniusDirectImageComp Λ f j kbar p q hcard)
          (etaleModuleGlobalSectionsDirectImageIso
            (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) Λ)).hom
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≫
        (Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation Λ
          (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology).hom =
      (ModuleSheafCohomology.compCorepresentation
          (etaleModuleDirectImage.{u, 0} Λ
            (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
          (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar) ⋙
            forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
          (𝟙_ (EtaleModules.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar)))
          (Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation Λ
            (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology)
          ((etaleModuleInverseImage.{u, 0} Λ
            (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)).obj (𝟙_ _))
          (Stacks.ExtCup.adjCorepresentation _ _
            (etaleModuleInverseImageAdj.{u, 0} Λ
              (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)))).hom ≫
        preadditiveCoyoneda.map (Functor.LaxMonoidal.ε (etaleModuleInverseImage.{u, 0} Λ
          (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))).op)
    (K : EtaleModules.{u, 0} Λ X) (i : ℕ)
    (b : Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
      (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology)
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K)) i) :
    ((compactSupportFrobeniusSingleIsoExt Λ f j kbar K i).hom).hom
        (((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
          (canonicalCompactSupportFrobeniusGroup.{u, 0} Λ f j kbar p q hcard
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj K) i)).hom
          (((compactSupportFrobeniusSingleIsoExt Λ f j kbar K i).inv).hom b)) =
      Stacks.ExtCup.adjunctionExtMap
        (etaleModuleInverseImage.{u, 0} Λ
          (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} Λ
          (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
        (etaleModuleInverseImageAdj.{u, 0} Λ
          (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K))
        (b.comp (Ext.mk₀ ((frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk j.toBase) kbar p q hcard).app
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K))) (add_zero i)) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let e := compactSupportFrobeniusSingleIso Λ f j kbar K (i : ℤ)
  have ha := compactSupportFrobeniusSingleIso_conj_canonicalCompactSupportFrobeniusGroup
    Λ f j kbar p q hcard K (i : ℤ)
  have hb := etaleModuleRightDerivedPlusIsoExt_conj_edge Λ (fieldBaseChange (Over.mk j.toBase) kbar)
    (etaleModuleInverseImage.{u, 0} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
    (etaleModuleDirectImage.{u, 0} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
    (etaleModuleInverseImageAdj.{u, 0} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)) _ hσ
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K))
    ((frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk j.toBase) kbar p q hcard).app
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K)) i b
  have h1 : ∀ y, (U.map e.hom).hom ((U.map (canonicalCompactSupportFrobeniusGroup.{u, 0} Λ f j kbar
      p q hcard ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj K) i)).hom
        ((U.map e.inv).hom y)) =
      (U.map (e.inv ≫ canonicalCompactSupportFrobeniusGroup.{u, 0} Λ f j kbar
        p q hcard ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj K) i ≫ e.hom)).hom y := by
    intro y
    simp only [Functor.map_comp]
    rfl
  have hE : ∀ x, ((compactSupportFrobeniusSingleIsoExt Λ f j kbar K i).hom).hom x =
      ((etaleModuleRightDerivedPlusIsoExt Λ _ _ i).hom).hom ((U.map e.hom).hom x) := fun _ => rfl
  have hE' : ∀ y, ((compactSupportFrobeniusSingleIsoExt Λ f j kbar K i).inv).hom y =
      (U.map e.inv).hom (((etaleModuleRightDerivedPlusIsoExt Λ _ _ i).inv).hom y) := fun _ => rfl
  refine (hE _).trans ?_
  refine Eq.trans (congrArg (fun x => ((etaleModuleRightDerivedPlusIsoExt Λ _ _ i).hom).hom
    ((U.map e.hom).hom ((U.map (canonicalCompactSupportFrobeniusGroup.{u, 0} Λ f j kbar p q hcard
      ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj K) i)).hom x))) (hE' b)) ?_
  refine Eq.trans (congrArg (fun x => ((etaleModuleRightDerivedPlusIsoExt Λ _ _ i).hom).hom x)
    (h1 _)) ?_
  refine Eq.trans (congrArg (fun g => ((etaleModuleRightDerivedPlusIsoExt Λ _ _ i).hom).hom
    ((U.map g).hom (((etaleModuleRightDerivedPlusIsoExt Λ _ _ i).inv).hom b))) ha) ?_
  exact hb

/-- **Item (1) of the purity half of Tag 03VH.** Under `Hⁱ_c(X_k̄, K) ≅ Ext^i(Λ_Y, N)`, with
`Y = X̄_k̄` and `N = (j_! K)|_Y`, the canonical geometric Frobenius is `b ↦ θ(b ∘ τ)`, where
`τ : N ⟶ π̄_* N` is the base change of the Frobenius descent isomorphism and
`θ = Stacks.ExtCup.adjunctionExtMap` for `π̄⁻¹ ⊣ π̄_*`. The degree-zero compatibility `hσ` of
`compactSupportFrobeniusSingleIsoExt_conj_canonical` is
`Stacks.EtaleCohomology.twistEdgeIso_whiskerRight_comp_corepresentation`. -/
theorem compactSupportFrobeniusSingleIsoExt_canonical_apply
    [(((fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology).W
      (A := ModuleCat.{u + 1} Λ)).IsMonoidal]
    (K : EtaleModules.{u, 0} Λ X) (i : ℕ)
    (b : Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
      (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology)
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K)) i) :
    ((compactSupportFrobeniusSingleIsoExt Λ f j kbar K i).hom).hom
        (((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
          (canonicalCompactSupportFrobeniusGroup.{u, 0} Λ f j kbar p q hcard
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj K) i)).hom
          (((compactSupportFrobeniusSingleIsoExt Λ f j kbar K i).inv).hom b)) =
      Stacks.ExtCup.adjunctionExtMap
        (etaleModuleInverseImage.{u, 0} Λ
          (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} Λ
          (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
        (etaleModuleInverseImageAdj.{u, 0} Λ
          (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K))
        (b.comp (Ext.mk₀ ((frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk j.toBase) kbar p q hcard).app
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K))) (add_zero i)) :=
  compactSupportFrobeniusSingleIsoExt_conj_canonical Λ f j kbar p q hcard
    (twistEdgeIso_whiskerRight_comp_corepresentation Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard).symm) K i b

end Stacks.EtaleCohomology

end
