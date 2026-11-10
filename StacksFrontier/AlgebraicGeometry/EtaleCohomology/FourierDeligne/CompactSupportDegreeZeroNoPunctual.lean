module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.CompactSupportDegreeZeroLisse

/-!
# Compactly supported sections of a sheaf without punctual sections

Let `j : X ⟶ Y` be an open immersion with non-closed image and `G` a sheaf of `Λ`-modules on
`X_étale` such that a section over (an étale `X`-scheme isomorphic to) `X` vanishing on a nonempty
étale `X`-scheme vanishes. Then `Γ(Y, j_! G) = 0`, by the argument of
`Stacks.EtaleCohomology.extensionByZero_section_eq_zero_of_isLocallyConstantWith`: a global
section of `j_! G` vanishes near a boundary point of the image of `j`, so its image in `Γ(X, G)`
vanishes on a nonempty étale `X`-scheme.

The vanishing property holds for `G` without sections supported off a connected dense open
`i : V ⟶ X` on which it is locally constant (the unit `G ⟶ i_* i⁻¹ G` is a monomorphism): the
image of the section in `Γ(V, i⁻¹ G)` vanishes on a nonempty étale `V`-scheme, so it vanishes, and
then so does the section.

Over a separably closed field this gives `H⁰(Rf_!(G[0])) = 0` for such `G`, the step of the
single-level argument for the irreducibility of the Fourier transform in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) which handles sheaves `Q ⊆ j_* Q_V`.

## Main results

* `Stacks.EtaleCohomology.eq_zero_of_map_eq_zero_of_mono_unit`.
* `Stacks.EtaleCohomology.extensionByZero_section_eq_zero_of_forall_map_eq_zero`.
* `Stacks.EtaleCohomology.isZero_homology_zero_derivedLowerShriek_of_forall_map_eq_zero`.
* `Stacks.EtaleCohomology.isZero_homology_zero_derivedLowerShriek_of_mono_unit`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard`, and so do the last two statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ]

attribute [local instance] hasSheafify_over_etaleModules_locallyConstantSections

/-- The base change of an étale `X`-scheme `W` along an open immersion `j` is nonempty as soon as
a point of `W` maps into the closure of the image of `j`. -/
private theorem nonempty_baseChange_left {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (W : X.Etale) (y : W.left) (hy : W.hom y ∈ closure (Set.range j)) :
    Nonempty ((smallEtaleBaseChange j).obj W).left := by
  have : Etale W.hom := W.prop
  have : UniversallyOpen W.hom := UniversallyOpen.of_flat W.hom
  obtain ⟨_, ⟨w, rfl⟩, x', hx'⟩ : (Set.range W.hom ∩ Set.range j).Nonempty :=
    mem_closure_iff.1 hy _ W.hom.isOpenMap.isOpen_range ⟨y, rfl⟩
  obtain ⟨q, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := W.hom) (g := j) w x' hx'.symm
  exact ⟨q⟩

/-- A section `t` killed by a restriction vanishes if its image under a monomorphism `η` into a
direct image `j_* H` vanishes as soon as it is killed by the corresponding restriction of `H`. -/
private theorem eq_zero_of_mono_of_forall_map_eq_zero {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (F : EtaleModules.{u, 0} Λ X) (H : EtaleModules.{u, 0} Λ U)
    (η : F ⟶ (etaleModuleDirectImage.{u, 0} Λ j).obj H) [Mono η] {V W : X.Etale} (g : W ⟶ V)
    (t : F.obj.obj (op V)) (ht : (F.obj.map g.op).hom t = 0)
    (hz : ∀ s : H.obj.obj (op ((smallEtaleBaseChange j).obj V)),
      (H.obj.map ((smallEtaleBaseChange j).map g).op).hom s = 0 → s = 0) : t = 0 := by
  have hinj : Function.Injective (η.hom.app (op V)).hom := by
    rw [← ModuleCat.mono_iff_injective]
    have : Mono η.hom := (sheafToPresheaf _ _).map_mono η
    exact (NatTrans.mono_iff_mono_app η.hom).1 inferInstance (op V)
  have hn := ConcreteCategory.congr_hom (η.hom.naturality g.op) t
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hn
  have h0 : (η.hom.app (op W)).hom ((F.obj.map g.op).hom t) = 0 := by rw [ht, map_zero]
  exact hinj ((hz _ (hn.symm.trans h0)).trans (map_zero _).symm)

/-- **A section without support off a connected dense open where the sheaf is locally constant
vanishes as soon as it vanishes on a nonempty étale scheme.** Let `i : V₀ ⟶ X` be an open
immersion with connected source and dense image, `G` a sheaf of `Λ`-modules on `X_étale` with
`i⁻¹ G` locally constant and `G ⟶ i_* i⁻¹ G` a monomorphism. For an étale `X`-scheme `V` with
invertible structure morphism and `g : W ⟶ V` with `W` nonempty, a section `t` of `G` over `V`
with `t|_W = 0` is `0`. -/
theorem eq_zero_of_map_eq_zero_of_mono_unit (Q : ModuleCat.{u + 1} Λ → Prop)
    {X V₀ : Scheme.{u}} (i : V₀ ⟶ X) [IsOpenImmersion i] [ConnectedSpace V₀]
    (hd : Dense (Set.range i)) (G : EtaleModules.{u, 0} Λ X)
    (hG : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V₀.smallEtaleTopology Q
      ((etaleModuleInverseImage.{u, 0} Λ i).obj G))
    (hη : Mono ((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app G))
    {V W : X.Etale} [IsIso V.hom] [Nonempty W.left] (g : W ⟶ V) (t : G.obj.obj (op V))
    (ht : (G.obj.map g.op).hom t = 0) : t = 0 := by
  let M := (etaleModuleInverseImage.{u, 0} Λ i).obj G
  let B := smallEtaleBaseChange i
  have : ConnectedSpace (B.obj V).left := by
    let e := Scheme.homeoOfIso (asIso (pullback.snd V.hom i))
    exact e.symm.surjective.connectedSpace e.symm.continuous
  have : Nonempty (B.obj W).left :=
    nonempty_baseChange_left i W (Classical.arbitrary _) (by rw [hd.closure_eq]; trivial)
  exact eq_zero_of_mono_of_forall_map_eq_zero Λ i G M
    ((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app G) g t ht
    (eq_zero_of_map_eq_zero_of_isLocallyConstantWith Λ Q M hG (B.map g))

attribute [local instance] moduleCat_hasLimitsOfSize in
/-- **`Γ(Y, j_! G) = 0`** for an open immersion `j : X ⟶ Y` with non-closed image and a sheaf `G`
of `Λ`-modules on `X_étale` whose sections over (an étale `X`-scheme isomorphic to) `X` vanish as
soon as they vanish on a nonempty étale `X`-scheme. -/
theorem extensionByZero_section_eq_zero_of_forall_map_eq_zero {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (hj : ¬ IsClosed (Set.range j)) (G : EtaleModules.{u, 0} Λ X)
    (hZ : ∀ {V W : X.Etale} [IsIso V.hom] [Nonempty W.left] (g : W ⟶ V)
      (t : G.obj.obj (op V)), (G.obj.map g.op).hom t = 0 → t = 0)
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
  let zbar : Spec (.of (AlgebraicClosure (Y.residueField z))) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField z)
      (AlgebraicClosure (Y.residueField z)))) ≫ Y.fromSpecResidueField z
  let x₀ : (Scheme.pointSmallEtale zbar).fiber.obj T :=
    Over.homMk zbar (by change zbar ≫ 𝟙 Y = zbar; rw [Category.comp_id])
  obtain ⟨W, g, ⟨p, hp⟩, yW, -⟩ := (Scheme.pointSmallEtale zbar).jointly_surjective _
    (Presheaf.imageSieve_mem Y.smallEtaleTopology
      (CategoryTheory.toSheafify Y.smallEtaleTopology P) (U := op T) s) x₀
  let pt : Spec (.of (AlgebraicClosure (Y.residueField z))) := default
  let y : W.left := yW.left pt
  have hWz : W.hom y = z := by
    have hw : yW.left ≫ W.hom = zbar := Over.w yW
    change (yW.left ≫ W.hom) pt = z
    rw [hw]
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
  have : IsIso (B.obj T).hom := inferInstanceAs (IsIso (pullback.snd (𝟙 Y) j))
  have : Nonempty (B.obj W).left :=
    nonempty_baseChange_left j W y (hWz ▸ hzc)
  have : Mono ε := mono_etaleModuleExtensionByZeroToDirectImage_app Λ j G
  exact eq_zero_of_mono_of_forall_map_eq_zero Λ j _ G ε g s hsW (hZ (B.map g))

section DegreeZero

attribute [local instance] HasDerivedCategory.standard

/-- **`H⁰(Rf_!(G[0])) = 0` over a separably closed field** for a sheaf `G` of `Λ`-modules on a
separated `Ω`-scheme of finite type whose compactification `j` does not have closed image, when a
section of `G` over (an étale scheme isomorphic to) the source vanishing on a nonempty étale
scheme vanishes: `H⁰_c = Γ(X̄, j_! G)` (Tag 0GK1), which vanishes
(`Stacks.EtaleCohomology.extensionByZero_section_eq_zero_of_forall_map_eq_zero`). -/
theorem isZero_homology_zero_derivedLowerShriek_of_forall_map_eq_zero
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of Ω)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (j : CompactificationOf (Over.mk f))
    (hj : ¬ IsClosed (Set.range j.immersion)) (G : EtaleModules.{u, 0} Λ X)
    (hZ : ∀ {V W : X.Etale} [IsIso V.hom] [Nonempty W.left] (g : W ⟶ V)
      (t : G.obj.obj (op V)), (G.obj.map g.op).hom t = 0 → t = 0) :
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
  have hT : IsTerminal (Scheme.Etale.mk (𝟙 j.space)) := MorphismProperty.Over.mkIdTerminal _ _
  have h0 : IsZero ((etaleModuleGlobalSections.{u, 0} Λ j.space).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj G)) := by
    refine IsZero.of_iso ?_ ((Sheaf.ΓNatIsoSheafSections _ _ hT).app _)
    refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun a b => ?_⟩
    rw [extensionByZero_section_eq_zero_of_forall_map_eq_zero Λ j.immersion hj G hZ a,
      extensionByZero_section_eq_zero_of_forall_map_eq_zero Λ j.immersion hj G hZ b]
  have h1 : IsZero (Γ.obj ((DerivedCategory.Plus.homologyFunctor _ 0).obj K)) :=
    (h0.of_iso e).of_iso
      ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso Γ 0).app K).symm
  rw [IsZero.iff_id_eq_zero]
  exact Γ.map_injective (h1.eq_of_src _ _)

/-- **`H⁰(Rf_!(G[0])) = 0` over a separably closed field for `G` without sections supported off a
connected dense open `i : V₀ ⟶ X` on which it is locally constant**, `f` separated of finite type
with a compactification whose image is not closed. -/
theorem isZero_homology_zero_derivedLowerShriek_of_mono_unit
    (Q : ModuleCat.{u + 1} Λ → Prop) (Ω : Type u) [Field Ω] [IsSepClosed Ω] {X V₀ : Scheme.{u}}
    (f : X ⟶ Spec (.of Ω)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (j : CompactificationOf (Over.mk f)) (hj : ¬ IsClosed (Set.range j.immersion))
    (i : V₀ ⟶ X) [IsOpenImmersion i] [ConnectedSpace V₀] (hd : Dense (Set.range i))
    (G : EtaleModules.{u, 0} Λ X)
    (hG : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V₀.smallEtaleTopology Q
      ((etaleModuleInverseImage.{u, 0} Λ i).obj G))
    (hη : Mono ((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app G)) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) :=
  isZero_homology_zero_derivedLowerShriek_of_forall_map_eq_zero Λ Ω f j hj G
    fun g t ht => eq_zero_of_map_eq_zero_of_mono_unit Λ Q i hd G hG hη g t ht

end DegreeZero

end Stacks.EtaleCohomology

end
