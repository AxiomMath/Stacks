module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FibreProduct.AffinePushout

/-!
# Fibre products of divided power schemes: open subschemes and affine charts

This file holds the divided power structure induced on an open subscheme of a divided power
scheme, the comparison of a divided power scheme with the spectrum of its global sections, the
divided power fibre product of affine divided power schemes as a closed subscheme of the
ordinary fibre product, and the charts of the general fibre product: triples of compatible
affine opens of the base and the two factors, with the divided power fibre product over each.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Opposite
open scoped AlgebraicGeometry

universe u v w

namespace Crystalline.DividedPowerScheme

attribute [local implicit_reducible] specDividedPowerScheme toSpecDividedPowerScheme
  specDividedPowerSchemeUnit specDividedPowerHomEquiv

attribute [local implicit_reducible] affineDividedPowerPushoutComparison

attribute [local implicit_reducible] dividedPowersOfSeparatingFamily

attribute [local implicit_reducible] idealTypeSheaf

attribute [local implicit_reducible] kernelSubmodule

attribute [local implicit_reducible] kernelSubmoduleIsLimit

attribute [local implicit_reducible] kernelSubmoduleIso

private theorem kernelSubmoduleIso_hom_ι {X : Scheme.{u}}
    {M N : SheafOfModules.{u} X.ringCatSheaf} (f : M ⟶ N) :
    (kernelSubmoduleIso f).hom ≫ kernel.ι f = (kernelSubmodule f).ι :=
  (kernelSubmoduleIsLimit f).conePointUniqueUpToIso_hom_comp
    (limit.isLimit _) WalkingParallelPair.zero

private theorem submodule_eq_of_iso {X : Scheme.{u}}
    {M : SheafOfModules.{u} X.ringCatSheaf} (I J : M.Submodule)
    (e : I.toSheafOfModules ≅ J.toSheafOfModules) (he : e.hom ≫ J.ι = I.ι) :
    I = J := by
  have hi : e.inv ≫ I.ι = J.ι := by rw [← he, e.inv_hom_id_assoc]
  apply SheafOfModules.Submodule.ext
  apply PresheafOfModules.Submodule.ext
  intro U
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have h := congrArg (fun k => k.val.app U ⟨x, hx⟩) he
    change (e.hom.val.app U ⟨x, hx⟩).val = x at h
    exact h ▸ (e.hom.val.app U ⟨x, hx⟩).property
  · have h := congrArg (fun k => k.val.app U ⟨x, hx⟩) hi
    change (e.inv.val.app U ⟨x, hx⟩).val = x at h
    exact h ▸ (e.inv.val.app U ⟨x, hx⟩).property

/-- Quasi-coherent ideal data for a divided-power scheme. -/
noncomputable def dividedPowerIdealData (X : DividedPowerScheme.{u}) :
    X.scheme.IdealSheafData :=
  Stacks.Divisors.idealSheafDataOfSubmodule X.ideal

attribute [local implicit_reducible] dividedPowerIdealData

private theorem dividedPowerIdealData_ideal (X : DividedPowerScheme.{u})
    (U : X.scheme.affineOpens) :
    (dividedPowerIdealData X).ideal U =
      Crystalline.sectionIdeal X.scheme.sheaf X.ideal (op U.1) :=
  rfl

/-- On an affine open of the source, the induced ideal is the image of the ideal on the
image open under the chart identification. -/
theorem sectionIdeal_map_appIso_comap
    (X : DividedPowerScheme.{u}) {Y : Scheme.{u}} (f : Y ⟶ X.scheme)
    [IsOpenImmersion f] (V : Y.affineOpens) :
    (Crystalline.sectionIdeal X.scheme.sheaf X.ideal (op (f ''ᵁ V.1))).map
        (f.appIso V.1).hom.hom =
      Crystalline.sectionIdeal Y.sheaf
        (idealSheafAsSubmodule ((dividedPowerIdealData X).comap f)) (op V.1) := by
  have hV : V.1 ≤ f ⁻¹ᵁ (f ''ᵁ V.1) := fun x hx => ⟨x, hx, rfl⟩
  have hU : IsAffineOpen (f ''ᵁ V.1) := V.2.image_of_isOpenImmersion f
  have he : (f.appIso V.1).hom = f.appLE (f ''ᵁ V.1) V.1 hV := Scheme.Hom.appIso_hom' f V.1
  rw [he, ← dividedPowerIdealData_ideal X ⟨f ''ᵁ V.1, hU⟩]
  exact idealSheafAsSubmodule_comap_open _ f ⟨f ''ᵁ V.1, hU⟩ V hV

/-- Sections on an open of the source, identified with sections on its image, commute
with restriction. -/
private theorem appIso_hom_comp_map {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (a b : Y.Opens) (hab : b ≤ a) (himg : f ''ᵁ b ≤ f ''ᵁ a) :
    (f.appIso a).hom ≫ Y.presheaf.map (homOfLE hab).op =
      X.presheaf.map (homOfLE himg).op ≫ (f.appIso b).hom := by
  rw [map_comp_appIso_hom f b (f ''ᵁ a) himg (fun x hx => ⟨x, hab hx, rfl⟩),
    Scheme.Hom.appIso_hom', Scheme.Hom.appLE_map]

/-- The divided powers induced on an affine open of an open subscheme: the divided powers
on the image open, transported along the identification of sections. -/
noncomputable def openBasisDividedPowers
    (X : DividedPowerScheme.{u}) {Y : Scheme.{u}} (f : Y ⟶ X.scheme)
    [IsOpenImmersion f] (V : Y.affineOpens) :
    DividedPowers (Crystalline.sectionIdeal Y.sheaf
      (idealSheafAsSubmodule ((dividedPowerIdealData X).comap f)) (op V.1)) :=
  DividedPowers.ofRingEquiv (e := (f.appIso V.1).commRingCatIsoToRingEquiv)
    (sectionIdeal_map_appIso_comap X f V)
    (X.dividedPowers.dividedPowers (op (f ''ᵁ V.1)))

private theorem openBasisDividedPowers_dpow
    (X : DividedPowerScheme.{u}) {Y : Scheme.{u}} (f : Y ⟶ X.scheme)
    [IsOpenImmersion f] (V : Y.affineOpens) (n : ℕ) (x : Γ(Y, V.1)) :
    (openBasisDividedPowers X f V).dpow n x =
      (f.appIso V.1).hom.hom
        ((X.dividedPowers.dividedPowers (op (f ''ᵁ V.1))).dpow n
          ((f.appIso V.1).commRingCatIsoToRingEquiv.symm x)) :=
  DividedPowers.ofRingEquiv_dpow _ _

private theorem openBasisDividedPowers_isDPMorphism
    (X : DividedPowerScheme.{u}) {Y : Scheme.{u}} (f : Y ⟶ X.scheme)
    [IsOpenImmersion f] (V : Y.affineOpens) :
    DividedPowers.IsDPMorphism (X.dividedPowers.dividedPowers (op (f ''ᵁ V.1)))
      (openBasisDividedPowers X f V) (f.appIso V.1).hom.hom := by
  refine ⟨(sectionIdeal_map_appIso_comap X f V).le, ?_⟩
  intro n x hx
  refine (openBasisDividedPowers_dpow X f V n _).trans ?_
  exact congrArg (f.appIso V.1).hom.hom
    (congrArg (fun z => (X.dividedPowers.dividedPowers (op (f ''ᵁ V.1))).dpow n z)
      ((f.appIso V.1).commRingCatIsoToRingEquiv.symm_apply_apply x))

theorem openBasisDividedPowers_naturality
    (X : DividedPowerScheme.{u}) {Y : Scheme.{u}} (f : Y ⟶ X.scheme)
    [IsOpenImmersion f] (a b : Y.affineOpens) (g : b.1 ⟶ a.1) :
    DividedPowers.IsDPMorphism (openBasisDividedPowers X f a)
      (openBasisDividedPowers X f b) (Y.presheaf.map g.op).hom := by
  have hab : b.1 ≤ a.1 := leOfHom g
  have himg : f ''ᵁ b.1 ≤ f ''ᵁ a.1 := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hab hz, rfl⟩
  have hsq : ∀ z, (Y.presheaf.map g.op).hom ((f.appIso a.1).hom.hom z) =
      (f.appIso b.1).hom.hom ((X.scheme.presheaf.map (homOfLE himg).op).hom z) := by
    intro z
    have hz := ConcreteCategory.congr_hom (appIso_hom_comp_map f a.1 b.1 hab himg) z
    simpa [show homOfLE hab = g from Subsingleton.elim _ _] using hz
  have hX := X.dividedPowers.naturality (homOfLE himg).op
  refine ⟨Ideal.map_le_iff_le_comap.mpr
    (fun z hz => (idealSheafAsSubmodule ((dividedPowerIdealData X).comap f)).map_mem g.op hz),
    ?_⟩
  intro n x hx
  have hx' : x ∈ (Crystalline.sectionIdeal X.scheme.sheaf X.ideal (op (f ''ᵁ a.1))).map
      (f.appIso a.1).hom.hom := by
    rw [sectionIdeal_map_appIso_comap X f a]
    exact hx
  obtain ⟨y, hyI, rfl⟩ :=
    (Ideal.mem_map_of_equiv (f.appIso a.1).commRingCatIsoToRingEquiv _).mp hx'
  have hyb : (X.scheme.presheaf.map (homOfLE himg).op).hom y ∈
      Crystalline.sectionIdeal X.scheme.sheaf X.ideal (op (f ''ᵁ b.1)) :=
    hX.1 (Ideal.mem_map_of_mem _ hyI)
  refine (congrArg ((openBasisDividedPowers X f b).dpow n) (hsq y)).trans ?_
  refine ((openBasisDividedPowers_isDPMorphism X f b).map_dpow hyb).symm.trans ?_
  refine (congrArg (f.appIso b.1).hom.hom (hX.map_dpow hyI).symm).trans ?_
  refine (hsq _).symm.trans ?_
  exact congrArg (Y.presheaf.map g.op).hom
    ((openBasisDividedPowers_isDPMorphism X f a).map_dpow hyI)

/-- The divided power structure induced on an open subscheme. -/
noncomputable def openDividedPowerStructure
    (X : DividedPowerScheme.{u}) {Y : Scheme.{u}} (f : Y ⟶ X.scheme)
    [IsOpenImmersion f] :
    Crystalline.DividedPowerStructure.{u, u, u} Y.sheaf
      (idealSheafAsSubmodule ((dividedPowerIdealData X).comap f)) :=
  dividedPowerStructureOfBasis Y _ (fun V : Y.affineOpens => V.1)
    (by simpa using Y.isBasis_affineOpens) (openBasisDividedPowers X f)
    (openBasisDividedPowers_naturality X f)

private theorem openDividedPowerStructure_isDPMorphism
    (X : DividedPowerScheme.{u}) {Y : Scheme.{u}} (f : Y ⟶ X.scheme)
    [IsOpenImmersion f] (U : X.scheme.affineOpens) (V : Y.affineOpens)
    (h : V.1 ≤ f ⁻¹ᵁ U.1) :
    DividedPowers.IsDPMorphism (X.dividedPowers.dividedPowers (op U.1))
      ((openDividedPowerStructure X f).dividedPowers (op V.1))
      (f.appLE U.1 V.1 h).hom := by
  have himg : f ''ᵁ V.1 ≤ U.1 := by
    rintro _ ⟨z, hz, rfl⟩
    exact h hz
  have he : (openDividedPowerStructure X f).dividedPowers (op V.1) =
      openBasisDividedPowers X f V :=
    dividedPowerStructureOfBasis_dividedPowers Y _ (fun V : Y.affineOpens => V.1)
      (by simpa using Y.isBasis_affineOpens) (openBasisDividedPowers X f)
      (openBasisDividedPowers_naturality X f) V
  rw [he]
  have hcomp : (f.appIso V.1).hom.hom.comp
      (X.scheme.presheaf.map (homOfLE himg).op).hom = (f.appLE U.1 V.1 h).hom := by
    rw [← CommRingCat.hom_comp,
      map_comp_appIso_hom f V.1 U.1 himg h]
  rw [← hcomp]
  exact DividedPowers.IsDPMorphism.comp _ (openBasisDividedPowers_isDPMorphism X f V)
    (X.dividedPowers.naturality (homOfLE himg).op)

/-- An open subscheme with its induced quasi-coherent ideal and divided powers. -/
noncomputable def openDividedPowerScheme
    (X : DividedPowerScheme.{u}) {Y : Scheme.{u}} (f : Y ⟶ X.scheme)
    [IsOpenImmersion f] : DividedPowerScheme.{u} where
  scheme := Y
  ideal := idealSheafAsSubmodule ((dividedPowerIdealData X).comap f)
  isQuasicoherent := idealSheafAsSubmodule_isQuasicoherent _
  dividedPowers := openDividedPowerStructure X f

attribute [local implicit_reducible] openDividedPowerScheme

/-- The inclusion of an open divided-power subscheme. -/
noncomputable def openDividedPowerInclusion
    (X : DividedPowerScheme.{u}) {Y : Scheme.{u}} (f : Y ⟶ X.scheme)
    [IsOpenImmersion f] : openDividedPowerScheme X f ⟶ X where
  hom := f
  compatible U := by
    apply isDPMorphism_app_of_affine (openDividedPowerScheme X f) X f ?_ U
    intro V W h
    exact openDividedPowerStructure_isDPMorphism X f V W h

attribute [local implicit_reducible] openDividedPowerInclusion

private theorem openDividedPowerScheme_ideal
    (X : DividedPowerScheme.{u}) {Y : Scheme.{u}} (f : Y ⟶ X.scheme)
    [IsOpenImmersion f] (U : X.scheme.affineOpens) (V : Y.affineOpens)
    (h : V.1 ≤ f ⁻¹ᵁ U.1) :
    (Crystalline.sectionIdeal X.scheme.sheaf X.ideal (op U.1)).map
        (f.appLE U.1 V.1 h).hom =
      Crystalline.sectionIdeal Y.sheaf (openDividedPowerScheme X f).ideal (op V.1) := by
  rw [← dividedPowerIdealData_ideal X U]
  exact idealSheafAsSubmodule_comap_open _ f U V h

theorem openDividedPowerInclusion_isInducedOpen
    (X : DividedPowerScheme.{u}) {Y : Scheme.{u}} (f : Y ⟶ X.scheme)
    [IsOpenImmersion f] : IsInducedOpen (openDividedPowerInclusion X f) :=
  ⟨inferInstanceAs (IsOpenImmersion f), openDividedPowerScheme_ideal X f⟩

attribute [local implicit_reducible] inducedOpenLift

theorem inducedOpenLift_comp
    {X Y Z : DividedPowerScheme.{u}} (f : X ⟶ Y) (hf : IsInducedOpen f)
    (g : Z ⟶ Y) (k : Z.scheme ⟶ X.scheme) (hk : k ≫ f.hom = g.hom) :
    inducedOpenLift f hf g k hk ≫ f = g :=
  DividedPowerScheme.Hom.ext hk

/-- An induced open morphism whose underlying map is an isomorphism is an isomorphism. -/
private theorem isIso_of_inducedOpen
    {X Y : DividedPowerScheme.{u}} (f : X ⟶ Y) (hf : IsInducedOpen f)
    [IsIso f.hom] : IsIso f :=
  ⟨inducedOpenLift f hf (𝟙 Y) (inv f.hom) (IsIso.inv_hom_id f.hom),
    DividedPowerScheme.Hom.ext (IsIso.hom_inv_id f.hom), inducedOpenLift_comp f hf (𝟙 Y) _ _⟩

attribute [local implicit_reducible] globalSectionsDPMorphism

/-- A map from a divided-power spectrum is recovered by its global sections map. -/
private theorem toSpecDividedPowerScheme_globalSections
    {X : DividedPowerScheme.{u}} {A : DividedPowerRing.{u}}
    (f : X ⟶ specDividedPowerScheme A) :
    toSpecDividedPowerScheme X A
      (specDividedPowerSchemeUnit A ≫ globalSectionsDPMorphism f) = f := by
  apply toSpecDividedPowerScheme_hom_ext
  exact toSpecDividedPowerScheme_appTop X A _

private theorem specDividedPowerHomEquiv_comp
    {X : DividedPowerScheme.{u}} {A B : DividedPowerRing.{u}}
    (f : X ⟶ specDividedPowerScheme B) (g : A ⟶ B) :
    specDividedPowerHomEquiv X A (f ≫ specDividedPowerMap g) =
      g ≫ specDividedPowerHomEquiv X B f := by
  show specDividedPowerSchemeUnit A ≫ globalSectionsDPMorphism
    (f ≫ specDividedPowerMap g) = _
  have hcomp : globalSectionsDPMorphism (f ≫ specDividedPowerMap g) =
      globalSectionsDPMorphism (specDividedPowerMap g) ≫ globalSectionsDPMorphism f :=
    (globalSectionsDPMorphism_comp f (specDividedPowerMap g)).symm
  rw [hcomp, ← Category.assoc]
  have h := (specDividedPowerHomEquiv (specDividedPowerScheme B) A).apply_symm_apply
    (g ≫ specDividedPowerSchemeUnit B)
  have hg : (specDividedPowerHomEquiv _ A).symm (g ≫ specDividedPowerSchemeUnit B) =
      specDividedPowerMap g := by
    apply DividedPowerScheme.Hom.ext
    rw [specDividedPowerMap_hom]
    apply ext_to_Spec
    exact (congrArg (fun φ => CommRingCat.ofHom φ.toRingHom) h).trans
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g.toRingHom))
  rw [hg] at h
  change specDividedPowerSchemeUnit A ≫ globalSectionsDPMorphism
    (specDividedPowerMap g) = g ≫ specDividedPowerSchemeUnit B at h
  rw [h, Category.assoc]
  rfl

/-- A pushout of divided-power rings represents the pullback of their spectra. -/
private theorem specDividedPower_isPullback
    {A B C D : DividedPowerRing.{u}}
    (f : A ⟶ B) (g : A ⟶ C) (i : B ⟶ D) (j : C ⟶ D)
    (h : IsPushout f g i j) :
    IsPullback (specDividedPowerMap i) (specDividedPowerMap j)
      (specDividedPowerMap f) (specDividedPowerMap g) := by
  have hw : specDividedPowerMap i ≫ specDividedPowerMap f =
      specDividedPowerMap j ≫ specDividedPowerMap g := by
    rw [← specDividedPowerMap_comp, ← specDividedPowerMap_comp, h.w]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw (fun s =>
    (specDividedPowerHomEquiv s.pt D).symm
      (h.desc (specDividedPowerHomEquiv s.pt B s.fst)
        (specDividedPowerHomEquiv s.pt C s.snd) (by
          have hs := congrArg (specDividedPowerHomEquiv s.pt A) s.condition
          simpa only [specDividedPowerHomEquiv_comp] using hs))) ?_ ?_ ?_⟩⟩
  · intro s
    apply (specDividedPowerHomEquiv s.pt B).injective
    rw [specDividedPowerHomEquiv_comp, Equiv.apply_symm_apply, h.inl_desc]
  · intro s
    apply (specDividedPowerHomEquiv s.pt C).injective
    rw [specDividedPowerHomEquiv_comp, Equiv.apply_symm_apply, h.inr_desc]
  · intro s m hm₁ hm₂
    apply (specDividedPowerHomEquiv s.pt D).injective
    rw [Equiv.apply_symm_apply]
    apply h.hom_ext
    · rw [h.inl_desc, ← specDividedPowerHomEquiv_comp, hm₁]
    · rw [h.inr_desc, ← specDividedPowerHomEquiv_comp, hm₂]

/-- The affine divided-power pullback is a closed subscheme of the ordinary pullback. -/
private theorem specDividedPower_pullbackComparison_isClosedImmersion
    {A B C D : DividedPowerRing.{u}}
    (f : A ⟶ B) (g : A ⟶ C) (i : B ⟶ D) (j : C ⟶ D)
    (h : IsPushout f g i j) :
    IsClosedImmersion (pullback.lift (f := (specDividedPowerMap f).hom)
      (g := (specDividedPowerMap g).hom) (specDividedPowerMap i).hom
      (specDividedPowerMap j).hom
      (congrArg DividedPowerScheme.Hom.hom (specDividedPower_isPullback f g i j h).w)) := by
  let u := Spec.map (CommRingCat.ofHom f.toRingHom)
  let v := Spec.map (CommRingCat.ofHom g.toRingHom)
  have hu : u ≫ 𝟙 _ = 𝟙 _ ≫ (specDividedPowerMap f).hom := by
    rw [Category.comp_id, Category.id_comp]
    exact (specDividedPowerMap_hom f).symm
  have hv : v ≫ 𝟙 _ = 𝟙 _ ≫ (specDividedPowerMap g).hom := by
    rw [Category.comp_id, Category.id_comp]
    exact (specDividedPowerMap_hom g).symm
  let k := pullback.map u v (specDividedPowerMap f).hom (specDividedPowerMap g).hom
    (𝟙 _) (𝟙 _) (𝟙 _) hu hv
  have : IsIso k := by
    dsimp only [k]
    infer_instance
  let l := affineDividedPowerPushoutComparison f g i j h
  have hl : IsClosedImmersion l := affineDividedPowerPushoutComparison_isClosedImmersion f g i j h
  have he : pullback.lift (f := (specDividedPowerMap f).hom)
      (g := (specDividedPowerMap g).hom) (specDividedPowerMap i).hom
      (specDividedPowerMap j).hom
      (congrArg DividedPowerScheme.Hom.hom (specDividedPower_isPullback f g i j h).w) =
      l ≫ k := by
    apply pullback.hom_ext
    · simp only [Category.assoc, k, pullback.map, pullback.lift_fst, Category.comp_id, l]
      exact (specDividedPowerMap_hom i).trans
        (affineDividedPowerPushoutComparison_fst f g i j h).symm
    · simp only [Category.assoc, k, pullback.map, pullback.lift_snd, Category.comp_id, l]
      exact (specDividedPowerMap_hom j).trans
        (affineDividedPowerPushoutComparison_snd f g i j h).symm
  rw [he]
  infer_instance

/-- The canonical map from a divided-power scheme to the spectrum of its sections. -/
private noncomputable def dividedPowerToSpec (X : DividedPowerScheme.{u}) :
    X ⟶ specDividedPowerScheme (X.dividedPowers.toDividedPowerRing (op ⊤)) :=
  toSpecDividedPowerScheme X _ (𝟙 _)

attribute [local implicit_reducible] dividedPowerToSpec

private theorem dividedPowerToSpec_hom (X : DividedPowerScheme.{u}) :
    (dividedPowerToSpec X).hom = X.scheme.toSpecΓ := by
  apply ext_to_Spec
  have h := toSpecDividedPowerScheme_appTop X
    (X.dividedPowers.toDividedPowerRing (op ⊤)) (𝟙 _)
  show (Scheme.ΓSpecIso Γ(X.scheme, ⊤)).inv ≫ (dividedPowerToSpec X).hom.appTop =
    (Scheme.ΓSpecIso Γ(X.scheme, ⊤)).inv ≫ X.scheme.toSpecΓ.appTop
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
  exact congrArg CommRingCat.ofHom h

private instance isIso_dividedPowerToSpec_hom (X : DividedPowerScheme.{u})
    [IsAffine X.scheme] : IsIso (dividedPowerToSpec X).hom := by
  rw [dividedPowerToSpec_hom]
  exact inferInstanceAs (IsIso X.scheme.isoSpec.hom)

/-- On an affine scheme, the canonical map to the spectrum preserves the whole ideal. -/
private theorem dividedPowerToSpec_isInducedOpen (X : DividedPowerScheme.{u})
    [IsAffine X.scheme] : IsInducedOpen (dividedPowerToSpec X) := by
  refine ⟨inferInstance, ?_⟩
  intro U V h
  let A := X.dividedPowers.toDividedPowerRing (op ⊤)
  have he := toSpecDividedPowerScheme_appTop X A (𝟙 _)
  change (dividedPowerToSpec X).hom.appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom = RingHom.id _ at he
  have key : (A.ideal.map (specSectionHom A U.1)).map
        ((dividedPowerToSpec X).hom.appLE U.1 V.1 h).hom =
      Crystalline.sectionIdeal X.scheme.sheaf X.ideal (op V.1) := by
    rw [Ideal.map_map, appLE_comp_specSectionHom, he]
    refine Eq.trans ?_ (sectionIdeal_map_of_isQuasicoherent X.scheme X.ideal
      ⟨⊤, isAffineOpen_top _⟩ V le_top)
    exact congrArg (fun φ => Ideal.map φ A.ideal) (RingHom.comp_id _)
  show (Crystalline.sectionIdeal (Spec (CommRingCat.of A)).sheaf
      (specDividedPowerIdeal A) (op U.1)).map _ = _
  rw [← specDividedPowerIdeal_affine A U]
  exact key

private theorem dividedPowerToSpec_isIso (X : DividedPowerScheme.{u})
    [IsAffine X.scheme] : IsIso (dividedPowerToSpec X) := by
  exact isIso_of_inducedOpen _ (dividedPowerToSpec_isInducedOpen X)

private theorem dividedPowerToSpec_naturality {X Y : DividedPowerScheme.{u}}
    (f : X ⟶ Y) :
    f ≫ dividedPowerToSpec Y =
      dividedPowerToSpec X ≫ specDividedPowerMap (globalSectionsDPMorphism f) := by
  apply DividedPowerScheme.Hom.ext
  simp only [DividedPowerScheme.Hom.comp_hom, dividedPowerToSpec_hom,
    specDividedPowerMap_hom]
  exact Scheme.toSpecΓ_naturality f.hom

attribute [local implicit_reducible] dividedPowerSchemeForget

/-- The naturality square of `dividedPowerToSpec`, on underlying schemes, in terms of the
inverse isomorphisms. -/
private theorem specDividedPowerMap_globalSections_hom_comp_inv
    {X Y : DividedPowerScheme.{u}} [IsIso (dividedPowerToSpec X)]
    [IsIso (dividedPowerToSpec Y)] (f : X ⟶ Y) :
    (specDividedPowerMap (globalSectionsDPMorphism f)).hom ≫
        (dividedPowerSchemeForget.mapIso (asIso (dividedPowerToSpec Y))).inv =
      (dividedPowerSchemeForget.mapIso (asIso (dividedPowerToSpec X))).inv ≫ f.hom := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (congrArg DividedPowerScheme.Hom.hom (dividedPowerToSpec_naturality f)).symm

/-- The ordinary scheme comparison associated to a divided-power pullback cone. -/
def coneSchemeComparison {X Y S : DividedPowerScheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} (c : PullbackCone f g) :
    c.pt.scheme ⟶ pullback f.hom g.hom :=
  pullback.lift c.fst.hom c.snd.hom
    (congrArg DividedPowerScheme.Hom.hom c.condition)

attribute [local implicit_reducible] coneSchemeComparison

/-- A divided-power pullback together with its closed embedding in the scheme pullback. -/
structure DividedPowerPullbackData {X Y S : DividedPowerScheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) where
  cone : PullbackCone f g
  isLimit : IsLimit cone
  isClosedImmersion : IsClosedImmersion (coneSchemeComparison cone)

section

attribute [local implicit_reducible] PullbackCone.mk

/-- Fibre products of affine divided-power schemes are given by ring pushouts. -/
theorem nonempty_affineDividedPowerPullbackData
    {X Y S : DividedPowerScheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsAffine X.scheme] [IsAffine Y.scheme] [IsAffine S.scheme] :
    Nonempty (DividedPowerPullbackData f g) := by
  have := dividedPowerToSpec_isIso X
  have := dividedPowerToSpec_isIso Y
  have := dividedPowerToSpec_isIso S
  let a := globalSectionsDPMorphism f
  let b := globalSectionsDPMorphism g
  let D := pushout a b
  let i : X.dividedPowers.toDividedPowerRing (op ⊤) ⟶ D := pushout.inl a b
  let j : Y.dividedPowers.toDividedPowerRing (op ⊤) ⟶ D := pushout.inr a b
  have h := specDividedPower_isPullback a b i j (IsPushout.of_hasPushout a b)
  let p := specDividedPowerMap i ≫ inv (dividedPowerToSpec X)
  let q := specDividedPowerMap j ≫ inv (dividedPowerToSpec Y)
  have h' : IsPullback p q f g := by
    apply h.of_iso' (Iso.refl _) (asIso (dividedPowerToSpec X))
      (asIso (dividedPowerToSpec Y)) (asIso (dividedPowerToSpec S))
    · simp [p]
    · simp [q]
    · exact (dividedPowerToSpec_naturality f).symm
    · exact (dividedPowerToSpec_naturality g).symm
  let c := PullbackCone.mk p q h'.w
  refine ⟨⟨c, h'.isLimit, ?_⟩⟩
  let eX := dividedPowerSchemeForget.mapIso (asIso (dividedPowerToSpec X))
  let eY := dividedPowerSchemeForget.mapIso (asIso (dividedPowerToSpec Y))
  let eS := dividedPowerSchemeForget.mapIso (asIso (dividedPowerToSpec S))
  let k := pullback.map (specDividedPowerMap a).hom (specDividedPowerMap b).hom
    f.hom g.hom eX.inv eY.inv eS.inv
    (specDividedPowerMap_globalSections_hom_comp_inv f)
    (specDividedPowerMap_globalSections_hom_comp_inv g)
  have : IsIso k := by
    dsimp only [k]
    infer_instance
  let l := coneSchemeComparison (PullbackCone.mk _ _ h.w)
  have hl : IsClosedImmersion l :=
    specDividedPower_pullbackComparison_isClosedImmersion a b i j (IsPushout.of_hasPushout a b)
  have he : coneSchemeComparison c = l ≫ k := by
    apply pullback.hom_ext
    · simp only [coneSchemeComparison, pullback.lift_fst, Category.assoc,
        k, pullback.map, pullback.lift_fst_assoc, l, c, p,
        PullbackCone.mk_fst, DividedPowerScheme.Hom.comp_hom]
      rfl
    · simp only [coneSchemeComparison, pullback.lift_snd, Category.assoc,
        k, pullback.map, pullback.lift_snd_assoc, l, c, q,
        PullbackCone.mk_snd, DividedPowerScheme.Hom.comp_hom]
      rfl
  rw [he]
  infer_instance

end

/-- Pulling back an induced open divided-power subscheme is the ordinary open pullback. -/
private theorem exists_inducedOpenPullback
    {X Y S : DividedPowerScheme.{u}} (f : X ⟶ S) (hf : IsInducedOpen f)
    (g : Y ⟶ S) :
    ∃ d : DividedPowerPullbackData f g,
      IsInducedOpen d.cone.snd ∧ IsIso (coneSchemeComparison d.cone) := by
  have := hf.isOpenImmersion
  let Z := openDividedPowerScheme Y (pullback.snd f.hom g.hom)
  let q : Z ⟶ Y := openDividedPowerInclusion Y (pullback.snd f.hom g.hom)
  have hq : IsInducedOpen q := openDividedPowerInclusion_isInducedOpen Y _
  let p : Z ⟶ X := inducedOpenLift f hf (q ≫ g) (pullback.fst f.hom g.hom)
    pullback.condition
  have hw : p ≫ f = q ≫ g := inducedOpenLift_comp f hf (q ≫ g) _ _
  let c := PullbackCone.mk p q hw
  have hc : IsLimit c := by
    apply PullbackCone.IsLimit.mk hw (fun s => inducedOpenLift q hq s.snd
      (pullback.lift s.fst.hom s.snd.hom
        (congrArg DividedPowerScheme.Hom.hom s.condition)) (pullback.lift_snd _ _ _))
    · exact fun s => DividedPowerScheme.Hom.ext (pullback.lift_fst _ _ _)
    · exact fun s => inducedOpenLift_comp q hq s.snd _ _
    · intro s m hmp hmq
      apply DividedPowerScheme.Hom.ext
      apply pullback.hom_ext
      · exact (congrArg DividedPowerScheme.Hom.hom hmp).trans (pullback.lift_fst _ _ _).symm
      · exact (congrArg DividedPowerScheme.Hom.hom hmq).trans (pullback.lift_snd _ _ _).symm
  have he : coneSchemeComparison c = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans (Category.id_comp _).symm
    · exact (pullback.lift_snd _ _ _).trans (Category.id_comp _).symm
  have hi : IsIso (coneSchemeComparison c) := by
    rw [he]
    exact IsIso.id _
  exact ⟨⟨c, hc, inferInstance⟩, hq, hi⟩

attribute [local implicit_reducible] zeroDividedPowerScheme

attribute [local implicit_reducible] zeroDividedPowerScheme_map

attribute [local implicit_reducible] zeroClosedFiberPresentation

attribute [local implicit_reducible] zeroDividedPowerScheme_map_factorSpec

attribute [local implicit_reducible] zeroDividedPowerScheme_map_factor

attribute [local implicit_reducible] closedFiberFunctor

attribute [local implicit_reducible] DividedPowerOpenPresentation.closedFiberGluing

attribute [local implicit_reducible] DividedPowerOpenPresentation.ideal

private theorem dividedPowersOfRingEquiv_isDPMorphism
    {R A : Type*} [CommRing R] [CommRing A] (I : Ideal R) (J : Ideal A)
    (e : R ≃+* A) (h : I.map e = J) (γ : DividedPowers J) :
    DividedPowers.IsDPMorphism (dividedPowersOfRingEquiv I J e h γ) γ e := by
  refine ⟨h.le, ?_⟩
  intro n x hx
  exact (e.apply_symm_apply _).symm

attribute [local implicit_reducible] DividedPowerOpenPresentation.basisDividedPowers

private theorem appLE_comp_restrict_appIso
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i] (f : Y ⟶ Z)
    (U : Z.Opens) (V : Y.Opens) (W : X.Opens) (hV : V ≤ f ⁻¹ᵁ U)
    (hW : i ''ᵁ W ≤ V) :
    f.appLE U V hV ≫ Y.presheaf.map (homOfLE hW).op ≫ (i.appIso W).hom =
      (i ≫ f).appLE U W (fun x hx => hV (hW ⟨x, hx, rfl⟩)) := by
  rw [← Category.assoc, Scheme.Hom.appLE_map, Scheme.Hom.appIso_hom',
    Scheme.Hom.appLE_comp_appLE]

attribute [local implicit_reducible] DividedPowerOpenPresentation.gluedMap

attribute [local implicit_reducible] DividedPowerOpenPresentation.cocone

attribute [local implicit_reducible] DividedPowerOpenPresentation.isColimit

/-- Compatible affine opens for a pair of divided-power morphisms. -/
structure DividedPowerPullbackChart
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S) where
  base : S.scheme.affineOpens
  left : T.scheme.affineOpens
  right : T'.scheme.affineOpens
  left_le : left.1 ≤ f.hom ⁻¹ᵁ base.1
  right_le : right.1 ≤ g.hom ⁻¹ᵁ base.1

instance {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S) :
    PartialOrder (DividedPowerPullbackChart f g) where
  le a b := a.base ≤ b.base ∧ a.left ≤ b.left ∧ a.right ≤ b.right
  le_refl _ := ⟨le_rfl, le_rfl, le_rfl⟩
  le_trans _ _ _ h k := ⟨h.1.trans k.1, h.2.1.trans k.2.1, h.2.2.trans k.2.2⟩
  le_antisymm a b h k := by
    cases a
    cases b
    congr
    · exact le_antisymm h.1 k.1
    · exact le_antisymm h.2.1 k.2.1
    · exact le_antisymm h.2.2 k.2.2

abbrev DividedPowerPullbackChart.open
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) : (pullback f.hom g.hom).Opens :=
  (pullback.fst f.hom g.hom) ⁻¹ᵁ a.left.1 ⊓
    (pullback.snd f.hom g.hom) ⁻¹ᵁ a.right.1

private theorem DividedPowerPullbackChart.open_mono
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S} :
    Monotone (DividedPowerPullbackChart.open (f := f) (g := g)) := by
  intro a b h
  exact inf_le_inf ((TopologicalSpace.Opens.map (pullback.fst f.hom g.hom).base).monotone h.2.1)
    ((TopologicalSpace.Opens.map (pullback.snd f.hom g.hom).base).monotone h.2.2)

/-- The chart open is monotone, in applied form. -/
theorem DividedPowerPullbackChart.open_le_open
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    {a b : DividedPowerPullbackChart f g} (h : a ≤ b) :
    DividedPowerPullbackChart.open a ≤ DividedPowerPullbackChart.open b :=
  DividedPowerPullbackChart.open_mono h

theorem DividedPowerPullbackChart.isPullback
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) :
    IsPullback
      ((pullback.fst f.hom g.hom).resLE a.left.1 a.open inf_le_left)
      ((pullback.snd f.hom g.hom).resLE a.right.1 a.open inf_le_right)
      (f.hom.resLE a.base.1 a.left.1 a.left_le)
      (g.hom.resLE a.base.1 a.right.1 a.right_le) :=
  Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f.hom g.hom)
    a.right_le a.left_le rfl

-- Checking that the restricted morphism is compatible with the divided powers unfolds the
-- chosen divided power structures on both open subschemes, which is expensive.
/-- The open divided-power restriction of a morphism. -/
noncomputable def restrictDividedPowerHom
    {T S : DividedPowerScheme.{u}} (f : T ⟶ S) (U : S.scheme.Opens)
    (V : T.scheme.Opens) (h : V ≤ f.hom ⁻¹ᵁ U) :
    openDividedPowerScheme T V.ι ⟶ openDividedPowerScheme S U.ι := by
  refine inducedOpenLift (X := openDividedPowerScheme S U.ι) (Y := S)
    (Z := openDividedPowerScheme T V.ι) (openDividedPowerInclusion S U.ι)
    (openDividedPowerInclusion_isInducedOpen S U.ι)
    (openDividedPowerInclusion T V.ι ≫ f) (f.hom.resLE U V h) ?_
  change f.hom.resLE U V h ≫ U.ι = V.ι ≫ f.hom
  exact Scheme.Hom.resLE_comp_ι f.hom h

attribute [local implicit_reducible] restrictDividedPowerHom

theorem restrictDividedPowerHom_comp
    {T S : DividedPowerScheme.{u}} (f : T ⟶ S) (U : S.scheme.Opens)
    (V : T.scheme.Opens) (h : V ≤ f.hom ⁻¹ᵁ U) :
    restrictDividedPowerHom f U V h ≫ openDividedPowerInclusion S U.ι =
      openDividedPowerInclusion T V.ι ≫ f :=
  inducedOpenLift_comp _ _ _ _ _

noncomputable def DividedPowerPullbackChart.data
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) :
    DividedPowerPullbackData
      (restrictDividedPowerHom f a.base.1 a.left.1 a.left_le)
      (restrictDividedPowerHom g a.base.1 a.right.1 a.right_le) := by
  have : IsAffine (openDividedPowerScheme T a.left.1.ι).scheme := a.left.2
  have : IsAffine (openDividedPowerScheme T' a.right.1.ι).scheme := a.right.2
  have : IsAffine (openDividedPowerScheme S a.base.1.ι).scheme := a.base.2
  exact (nonempty_affineDividedPowerPullbackData _ _).some

attribute [local implicit_reducible] DividedPowerPullbackChart.data

noncomputable abbrev DividedPowerPullbackChart.obj
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) := a.data.cone.pt

noncomputable def DividedPowerPullbackChart.fst
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) : a.obj ⟶ T :=
  a.data.cone.fst ≫ openDividedPowerInclusion T a.left.1.ι

attribute [local implicit_reducible] DividedPowerPullbackChart.fst

noncomputable def DividedPowerPullbackChart.snd
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) : a.obj ⟶ T' :=
  a.data.cone.snd ≫ openDividedPowerInclusion T' a.right.1.ι

attribute [local implicit_reducible] DividedPowerPullbackChart.snd

theorem DividedPowerPullbackChart.condition
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) : a.fst ≫ f = a.snd ≫ g := by
  dsimp only [DividedPowerPullbackChart.fst, DividedPowerPullbackChart.snd]
  rw [Category.assoc, Category.assoc, ← restrictDividedPowerHom_comp,
    ← restrictDividedPowerHom_comp, ← Category.assoc, ← Category.assoc,
    a.data.cone.condition]
  exact a.left_le

theorem dividedPower_mono_of_hom {X Y : DividedPowerScheme.{u}} (f : X ⟶ Y)
    [Mono f.hom] : Mono f :=
  ⟨fun _ _ he => DividedPowerScheme.Hom.ext
    ((cancel_mono f.hom).mp (congrArg DividedPowerScheme.Hom.hom he))⟩

theorem DividedPowerPullbackChart.isPullbackDP
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) :
    IsPullback a.data.cone.fst a.data.cone.snd
      (restrictDividedPowerHom f a.base.1 a.left.1 a.left_le)
      (restrictDividedPowerHom g a.base.1 a.right.1 a.right_le) :=
  IsPullback.of_isLimit a.data.isLimit

theorem DividedPowerPullbackChart.hom_ext
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) {Z : DividedPowerScheme.{u}} (p q : Z ⟶ a.obj)
    (h₁ : p ≫ a.fst = q ≫ a.fst) (h₂ : p ≫ a.snd = q ≫ a.snd) : p = q := by
  apply a.isPullbackDP.hom_ext
  · apply DividedPowerScheme.Hom.ext
    apply (cancel_mono a.left.1.ι).mp
    exact congrArg DividedPowerScheme.Hom.hom h₁
  · apply DividedPowerScheme.Hom.ext
    apply (cancel_mono a.right.1.ι).mp
    exact congrArg DividedPowerScheme.Hom.hom h₂

end Crystalline.DividedPowerScheme

end
