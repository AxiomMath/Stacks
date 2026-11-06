module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LocallyConstantSectionsConnected
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Formula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ExtensionByZeroToDirectImageMono
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Refinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.CompactSupportGeometricVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A locally constant sheaf on a connected non-closed open has no compactly supported sections

Let `j : X ⟶ Y` be an open immersion whose image is not closed, with `X` connected, and `G` a
locally constant sheaf of `Λ`-modules on `X_étale`. Then `Γ(Y, j_! G) = 0`. Consequently, over
a separably closed field, the compactly supported cohomology `H⁰_c(X, G)` of such a sheaf on a
connected separated scheme of finite type whose compactification does not have closed image
vanishes.

## Main results

* `Stacks.EtaleCohomology.extensionByZero_section_eq_zero_of_isLocallyConstantWith`:
  `Γ(Y, j_! G) = 0` for `j` with connected source and non-closed image.
* `Stacks.EtaleCohomology.isZero_homology_zero_derivedLowerShriek_of_isLocallyConstantWith`:
  over a separably closed field, `H⁰(Rf_!(G[0])) = 0`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` is formed in the standard model
`HasDerivedCategory.standard` of the derived category, and so is the last statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ]

attribute [local instance] hasSheafify_over_etaleModules_locallyConstantSections

attribute [local instance] moduleCat_hasLimitsOfSize in
/-- **`Γ(Y, j_! G) = 0`** for an open immersion `j : X ⟶ Y` with connected source and non-closed
image and a locally constant sheaf `G` of `Λ`-modules on `X_étale`. -/
@[sga "4½ Sommes_trig 1.18" "Clause b)"]
theorem extensionByZero_section_eq_zero_of_isLocallyConstantWith
    (Q : ModuleCat.{u + 1} Λ → Prop) {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    [ConnectedSpace X] (hj : ¬ IsClosed (Set.range j)) (G : EtaleModules.{u, 0} Λ X)
    (hG : Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q G)
    (s : ((etaleModuleExtensionByZero.{u, 0} Λ j).obj G).obj.obj
      (op (Scheme.Etale.mk (𝟙 Y)))) : s = 0 := by
  obtain ⟨z, hzc, hzr⟩ : ∃ z, z ∈ closure (Set.range j) ∧ z ∉ Set.range j :=
    Set.not_subset.1 fun h => hj (closure_subset_iff_isClosed.1 h)
  let T : Y.Etale := Scheme.Etale.mk (𝟙 Y)
  let P := (Scheme.Etale.smallEtaleCompose j).op.lan.obj G.obj
  have : Y.smallEtaleTopology.WEqualsLocallyBijective (ModuleCat.{u + 1} Λ) :=
    Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat.{u, u + 1, u + 1, 0} _ Λ
  have hls : Presheaf.IsLocallySurjective.{u, u + 1, u + 1, u + 2, u + 1, u + 1}
      Y.smallEtaleTopology (CategoryTheory.toSheafify Y.smallEtaleTopology P) :=
    (Y.smallEtaleTopology.W_toSheafify P).isLocallySurjective
  have hmem := Presheaf.imageSieve_mem Y.smallEtaleTopology
    (CategoryTheory.toSheafify Y.smallEtaleTopology P) (U := op T) s
  let zbar : Spec (.of (AlgebraicClosure (Y.residueField z))) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField z)
      (AlgebraicClosure (Y.residueField z)))) ≫ Y.fromSpecResidueField z
  let x₀ : (Scheme.pointSmallEtale zbar).fiber.obj T :=
    Over.homMk zbar (by change zbar ≫ 𝟙 Y = zbar; rw [Category.comp_id])
  obtain ⟨W, g, ⟨p, hp⟩, yW, -⟩ := (Scheme.pointSmallEtale zbar).jointly_surjective _ hmem x₀
  let pt : Spec (.of (AlgebraicClosure (Y.residueField z))) := default
  let y : W.left := yW.left pt
  have hWz : W.hom y = z := by
    show (yW.left ≫ W.hom) pt = z
    rw [show yW.left ≫ W.hom = zbar from Over.w yW]
    exact Scheme.fromSpecResidueField_apply z _
  have hP : IsZero (P.obj (op W)) := by
    have : IsEmpty (W ⟶ Scheme.Etale.smallEtaleSource j) := ⟨fun φ => hzr ⟨φ.left y, by
      rw [← hWz, ← MorphismProperty.Over.w φ]
      rfl⟩⟩
    refine IsZero.of_iso ?_ (extensionByZeroPresheafSectionIso j G.obj W).symm
    rw [IsZero.iff_id_eq_zero]
    exact Sigma.hom_ext _ _ fun b => isEmptyElim b
  have hsW : (((etaleModuleExtensionByZero.{u, 0} Λ j).obj G).obj.map g.op).hom s = 0 := by
    rw [show p = 0 from (ModuleCat.subsingleton_of_isZero hP).elim p 0, map_zero] at hp
    exact hp.symm
  let ε := (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ j).app G
  let B := smallEtaleBaseChange j
  have ht : (G.obj.map (B.map g).op).hom ((ε.hom.app (op T)).hom s) = 0 := by
    have hn := ConcreteCategory.congr_hom (ε.hom.naturality g.op) s
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hn
    have h0 : (ε.hom.app (op W)).hom
        ((((etaleModuleExtensionByZero.{u, 0} Λ j).obj G).obj.map g.op).hom s) = 0 := by
      rw [hsW, map_zero]
    exact hn.symm.trans h0
  have : ConnectedSpace (B.obj T).left := by
    let e := Scheme.homeoOfIso (asIso (pullback.snd (𝟙 Y) j))
    exact e.symm.surjective.connectedSpace e.symm.continuous
  have : Nonempty (B.obj W).left := by
    have : Etale W.hom := W.prop
    have : UniversallyOpen W.hom := UniversallyOpen.of_flat W.hom
    obtain ⟨x, hx⟩ : ((Set.range W.hom) ∩ Set.range j).Nonempty :=
      mem_closure_iff.1 hzc _ W.hom.isOpenMap.isOpen_range ⟨y, hWz⟩
    obtain ⟨⟨w, rfl⟩, x', hx'⟩ := hx
    obtain ⟨q, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := W.hom) (g := j) w x'
      hx'.symm
    exact ⟨q⟩
  have ht0 := eq_zero_of_map_eq_zero_of_isLocallyConstantWith Λ Q G hG (B.map g) _ ht
  have : Mono ε := mono_etaleModuleExtensionByZeroToDirectImage_app Λ j G
  have hinj : Function.Injective (ε.hom.app (op T)).hom := by
    rw [← ModuleCat.mono_iff_injective]
    have : Mono ε.hom := (sheafToPresheaf _ _).map_mono ε
    exact (NatTrans.mono_iff_mono_app ε.hom).1 inferInstance (op T)
  exact hinj (ht0.trans (map_zero _).symm)

section DegreeZero

attribute [local instance] HasDerivedCategory.standard

/-- **`H⁰(Rf_!(G[0])) = 0` over a separably closed field** for a locally constant sheaf `G` of
`Λ`-modules on a connected separated `Ω`-scheme of finite type whose compactification `j` does
not have closed image. -/
theorem isZero_homology_zero_derivedLowerShriek_of_isLocallyConstantWith
    (Q : ModuleCat.{u + 1} Λ → Prop) (Ω : Type u) [Field Ω] [IsSepClosed Ω] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of Ω)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (j : CompactificationOf (Over.mk f)) [ConnectedSpace X]
    (hj : ¬ IsClosed (Set.range j.immersion)) (G : EtaleModules.{u, 0} Λ X)
    (hG : Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q G) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) := by
  have : HasLimitsOfSize.{0, u} (ModuleCat.{u + 1} Λ) := ModuleCat.hasLimitsOfSize.{0, u, u + 1}
  have : HasSheafify (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    hasSheafifyEtale.{u, 0} (Spec (.of Ω)) Λ
  have := isEquivalence_globalSections_of_isSepClosed Ω (ModuleCat.{u + 1} Λ)
  let Γ := etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))
  let K := (derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G)
  obtain ⟨e⟩ := nonempty_compactlySupportedCohomologyGroup_zero_iso Ω f j Λ G
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  have : ConnectedSpace (Over.mk f).left := ‹ConnectedSpace X›
  have hT : IsTerminal (Scheme.Etale.mk (𝟙 j.space)) := MorphismProperty.Over.mkIdTerminal _ _
  have h0 : IsZero ((etaleModuleGlobalSections.{u, 0} Λ j.space).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj G)) := by
    refine IsZero.of_iso ?_ ((Sheaf.ΓNatIsoSheafSections _ _ hT).app _)
    refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun a b => ?_⟩
    rw [extensionByZero_section_eq_zero_of_isLocallyConstantWith Λ Q j.immersion hj G hG a,
      extensionByZero_section_eq_zero_of_isLocallyConstantWith Λ Q j.immersion hj G hG b]
  have h1 : IsZero (Γ.obj ((DerivedCategory.Plus.homologyFunctor _ 0).obj K)) :=
    (h0.of_iso e).of_iso
      ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso Γ 0).app K).symm
  rw [IsZero.iff_id_eq_zero]
  exact Γ.map_injective (by rw [Γ.map_id, Functor.map_zero]; exact h1.eq_of_src _ _)

end DegreeZero

end Stacks.EtaleCohomology

end
