module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineSystemModuleColimit
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence

/-!
# The three clauses of Stacks 01ZR on the small étale sites

Let `c` be a limit cone on a cofiltered diagram `X` of quasi-compact and quasi-separated schemes of
a big étale site, with affine transition morphisms.  The three clauses of Stacks 01ZR hold for the
modules on the *small étale* sites of the `X i` and of `c.pt`, with the pullbacks along the
morphisms of small étale ringed sites of Stacks 070R (2): this file reads them off the Zariski
clauses through the associated-module functor `𝓕 ↦ 𝓕^a` of Stacks 03DU (4), which is an
equivalence `QCoh(𝒪_S) ≌ QCoh(S_étale, 𝒪)` (Stacks 03DX (2)) carrying finite presentation to
finite presentation (Stacks 05VG) and commuting with the pullbacks (Stacks 03LC) coherently.

## Main definitions

* `AlgebraicGeometry.SmallEtale.smallEtalePullbackSystem`: the pullback system of modules on the
  small étale sites of `X` and of `c.pt`.
* `AlgebraicGeometry.SmallEtale.associatedModuleTransferUp`: the comparison from the Zariski
  pullback system, given by `𝓕 ↦ 𝓕^a`.

## Main results

* `AlgebraicGeometry.SmallEtale.smallEtalePullbackSystem_faithfulness`, `_fullness` and
  `_essSurj`: the three clauses.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {I : Type u} [Category.{u} I] [IsCofiltered I]
  (X : I ⥤ B.Scheme) (c : Cone X)

/-- **The pullback system of modules on the small étale sites** of the stages of `X` and of the
vertex of `c`: the inverse images are the pullbacks along the morphisms of small étale ringed sites
of Stacks 070R (2), the comparison is `AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso`
followed by the transport along the commutation of the cone, and the property of objects is
finite presentation. -/
abbrev smallEtalePullbackSystem : Stacks.ModuleColimit.PullbackSystem.{u, u, u + 1, u + 1} I where
  C j := SheafOfModules.{u} (structureSheaf B (X.obj j).obj (X.obj j).property)
  L := SheafOfModules.{u} (structureSheaf B c.pt.obj c.pt.property)
  pb e := SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B (X.map e))
  pbL j := SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B (X := c.pt) (c.π.app j))
  comp {j _} e := (smallEtalePullbackCompIso B (X := c.pt) (c.π.app j) (X.map e) ≪≫
    eqToIso (congrArg (fun a => SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a))
      (c.w e))).symm
  P _ M := M.IsFinitePresentation
  PL M := M.IsFinitePresentation

/-- **The Zariski pullback system of the underlying schemes**, spelled through
`AlgebraicGeometry.SmallEtale.schemeHom`, which is the spelling of the base-change identifications
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`.  It is
`Stacks.AlgebraicGeometry.ModuleLimits.zariskiPullbackSystem` of `X ⋙ B.inclusion` and the image of
`c`, up to that spelling. -/
abbrev zariskiSystem : Stacks.ModuleColimit.PullbackSystem.{u, u, u, u + 1} I where
  C j := (X.obj j).obj.Modules
  L := c.pt.obj.Modules
  pb e := Scheme.Modules.pullback (schemeHom B (X.map e))
  pbL j := Scheme.Modules.pullback (schemeHom B (X := c.pt) (c.π.app j))
  comp {j k} e := (Scheme.Modules.pullbackComp (schemeHom B (X := c.pt) (c.π.app j))
      (schemeHom B (X.map e)) ≪≫
    Scheme.Modules.pullbackCongr (show schemeHom B (X := c.pt) (c.π.app j) ≫
      schemeHom B (X.map e) = schemeHom B (X := c.pt) (c.π.app k) from
        congrArg B.inclusion.map (c.w e))).symm
  P _ M := M.IsFinitePresentation
  PL M := M.IsFinitePresentation

/-- The coherence of the identifications `(r^*𝓕)^a ≅ ε_r^*(𝓕^a)` with the comparisons, at an
arbitrary factorization `a ≫ b = p`. -/
theorem associatedModuleObjBaseChangeIso_coherence {W Y Z : B.Scheme} (a : W ⟶ Y)
    (b : Y ⟶ Z) (p : W ⟶ Z) (h : a ≫ b = p) (𝓖 : Z.obj.Modules) :
    (associatedModule B W.obj W.property).map
        (((Scheme.Modules.pullbackComp (schemeHom B a) (schemeHom B b) ≪≫
          Scheme.Modules.pullbackCongr (show schemeHom B a ≫ schemeHom B b = schemeHom B p from
            congrArg B.inclusion.map h)).symm).hom.app 𝓖) =
      (associatedModuleBaseChangeIso B p).hom.app 𝓖 ≫
        ((smallEtalePullbackCompIso B a b ≪≫
          eqToIso (congrArg (fun a => SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a))
            h)).symm).hom.app ((associatedModule B Z.obj Z.property).obj 𝓖) ≫
        (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).map
          ((associatedModuleBaseChangeIso B b).inv.app 𝓖) ≫
        (associatedModuleBaseChangeIso B a).inv.app
          ((Scheme.Modules.pullback (schemeHom B b)).obj 𝓖) := by
  subst h
  have e₁ : Scheme.Modules.pullbackCongr (show schemeHom B a ≫ schemeHom B b =
      schemeHom B (a ≫ b) from congrArg B.inclusion.map rfl) = Iso.refl _ := eqToIso_refl _
  have hc := associatedModuleObjBaseChangeIso_comp B a b 𝓖
  simp only [associatedModuleObjBaseChangeIso, Iso.app_hom] at hc
  rw [e₁]
  simp only [Iso.symm_hom, eqToIso_refl, Iso.trans_refl]
  rw [← cancel_epi ((associatedModule B W.obj W.property).map
    ((Scheme.Modules.pullbackComp (schemeHom B a) (schemeHom B b)).hom.app 𝓖)),
    ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, reassoc_of% hc.symm]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
  rfl

/-- Faithfulness of `𝓕 ↦ 𝓕^a` on quasi-coherent modules. -/
theorem associatedModule_map_injective_of_isQuasicoherent (S : Scheme.{u}) (hS : B.Contains S)
    {M N : S.Modules} (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) (f g : M ⟶ N)
    (h : (associatedModule B S hS).map f = (associatedModule B S hS).map g) : f = g := by
  have := (associatedModuleQcoh B S hS).map_injective
    (X := ⟨M, hM⟩) (Y := ⟨N, hN⟩) (a₁ := ObjectProperty.homMk f) (a₂ := ObjectProperty.homMk g)
    (by exact h)
  exact congrArg (fun φ => φ.hom) this

/-- Fullness of `𝓕 ↦ 𝓕^a` on quasi-coherent modules. -/
theorem associatedModule_map_surjective_of_isQuasicoherent (S : Scheme.{u}) (hS : B.Contains S)
    {M N : S.Modules} (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent)
    (f : (associatedModule B S hS).obj M ⟶ (associatedModule B S hS).obj N) :
    ∃ g : M ⟶ N, (associatedModule B S hS).map g = f :=
  ⟨((associatedModuleQcoh B S hS).preimage (X := ⟨M, hM⟩) (Y := ⟨N, hN⟩) (by exact f)).hom, by
    have h := (associatedModuleQcoh B S hS).map_preimage (X := ⟨M, hM⟩) (Y := ⟨N, hN⟩)
      (by exact f)
    exact h⟩

/-- Essential surjectivity of `𝓕 ↦ 𝓕^a` onto the modules of finite presentation, with preimages
of finite presentation. -/
theorem exists_isFinitePresentation_associatedModule_iso (S : Scheme.{u})
    (hS : B.Contains S) (G : SheafOfModules.{u} (structureSheaf B S hS))
    (hG : G.IsFinitePresentation) :
    ∃ M : S.Modules, M.IsFinitePresentation ∧
      Nonempty ((associatedModule B S hS).obj M ≅ G) := by
  have hq : G.IsQuasicoherentOnSite := SheafOfModules.isQuasicoherentOnSite_of_isQuasicoherent G
  obtain ⟨M, ⟨e⟩⟩ := quasicoherentIsEssImageAssociatedModule B S hS G hq
  refine ⟨M.obj, ?_, ⟨e⟩⟩
  refine (isFinitePresentation_associatedModule_iff B S hS M.obj M.property).2 ?_
  exact Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso e.symm hG

omit [IsCofiltered I] in
/-- The pasting coherence of the identifications `(r^*𝓕)^a ≅ ε_r^*(𝓕^a)` with the comparisons of
the two pullback systems. -/
theorem associatedModuleTransferUp_coherence {j k : I} (e : j ⟶ k) (M : (zariskiSystem B X c).C k) :
    (associatedModule B c.pt.obj c.pt.property).map (((zariskiSystem B X c).comp e).hom.app M) =
      (associatedModuleBaseChangeIso B (X := c.pt) (c.π.app k)).hom.app M ≫
        ((smallEtalePullbackSystem B X c).comp e).hom.app
          ((associatedModule B (X.obj k).obj (X.obj k).property).obj M) ≫
        ((smallEtalePullbackSystem B X c).pbL j).map
          ((associatedModuleBaseChangeIso B (X.map e)).inv.app M) ≫
        (associatedModuleBaseChangeIso B (X := c.pt) (c.π.app j)).inv.app
          (((zariskiSystem B X c).pb e).obj M) :=
  associatedModuleObjBaseChangeIso_coherence B (W := c.pt) (c.π.app j) (X.map e) (c.π.app k)
    (c.w e) M

/-- **The comparison of Zariski modules with small étale modules by `𝓕 ↦ 𝓕^a`**, as a comparison
of pullback systems. -/
def associatedModuleTransferUp :
    Stacks.ModuleColimit.PullbackSystem.TransferUp (zariskiSystem B X c)
      (smallEtalePullbackSystem B X c) where
  F j := associatedModule B (X.obj j).obj (X.obj j).property
  FL := associatedModule B c.pt.obj c.pt.property
  β e := associatedModuleBaseChangeIso B (X.map e)
  βL j := associatedModuleBaseChangeIso B (X := c.pt) (c.π.app j)
  coherence := by
    intro j k e M
    exact associatedModuleTransferUp_coherence B X c e M
  Q _ M := M.IsQuasicoherent
  QL M := M.IsQuasicoherent
  Q_of_P _ M hM := by
    have : M.IsFinitePresentation := hM
    exact Stacks.Modules.isQuasicoherent_of_isFinitePresentation M
  Q_pb e M hM := by
    have : M.IsQuasicoherent := hM
    change ((Scheme.Modules.pullback _).obj M).IsQuasicoherent
    infer_instance
  QL_pbL j M hM := by
    have : M.IsQuasicoherent := hM
    change ((Scheme.Modules.pullback _).obj M).IsQuasicoherent
    infer_instance
  faithful j _ _ hM hN f g h := associatedModule_map_injective_of_isQuasicoherent B _ _ hM hN f g h
  full j _ _ hM hN f := associatedModule_map_surjective_of_isQuasicoherent B _ _ hM hN f
  faithfulL hM hN f g h := associatedModule_map_injective_of_isQuasicoherent B _ _ hM hN f g h
  fullL hM hN f := associatedModule_map_surjective_of_isQuasicoherent B _ _ hM hN f
  P_map j M hM := isFinitePresentation_associatedModule_of_isFinitePresentation B _ _ M hM
  essSurjP j G hG := exists_isFinitePresentation_associatedModule_iso B _ _ G hG
  essSurjL G hG := exists_isFinitePresentation_associatedModule_iso B _ _ G hG

variable [∀ {i j : I} (f : i ⟶ j), IsAffineHom ((X ⋙ B.inclusion).map f)]
  [∀ i, CompactSpace ((X ⋙ B.inclusion).obj i)] [∀ i, QuasiSeparatedSpace ((X ⋙ B.inclusion).obj i)]

omit [∀ i, QuasiSeparatedSpace ((X ⋙ B.inclusion).obj i)] in
/-- **Stacks 01ZR (3)** for the Zariski system of the underlying schemes. -/
theorem zariskiSystem_faithfulness (hc : IsLimit (B.inclusion.mapCone c)) :
    (zariskiSystem B X c).Faithfulness := by
  intro k M N hM hN φ ψ h
  have : M.IsFinitePresentation := hM
  have : N.IsFinitePresentation := hN
  exact Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isLimit (X ⋙ B.inclusion)
    (B.inclusion.mapCone c) hc k M N φ ψ h

/-- **Stacks 01ZR (2)** for the Zariski system of the underlying schemes. -/
theorem zariskiSystem_fullness (hc : IsLimit (B.inclusion.mapCone c)) :
    (zariskiSystem B X c).Fullness := by
  intro k M N hM hN φ
  have : M.IsFinitePresentation := hM
  have : N.IsFinitePresentation := hN
  obtain ⟨j, e, φj, h⟩ := Stacks.AlgebraicGeometry.ModuleLimits.exists_map_of_pullback_of_isLimit
    (X ⋙ B.inclusion) (B.inclusion.mapCone c) hc k M N φ
  refine ⟨j, e, φj, ?_⟩
  have h₂ : (Scheme.Modules.pullback (schemeHom B (X := c.pt) (c.π.app j))).map φj ≫
      ((zariskiSystem B X c).comp e).inv.app N = ((zariskiSystem B X c).comp e).inv.app M ≫ φ := by
    simp only [Iso.symm_inv, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
    exact h
  rw [← reassoc_of% h₂]
  simp

/-- **Stacks 01ZR (1)** for the Zariski system of the underlying schemes. -/
theorem zariskiSystem_essSurj (hc : IsLimit (B.inclusion.mapCone c)) :
    (zariskiSystem B X c).EssSurj := by
  intro M hM
  have : M.IsFinitePresentation := hM
  obtain ⟨i, Mi, hMi, ⟨e⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs
      (X ⋙ B.inclusion) (B.inclusion.mapCone c) hc M
  exact ⟨i, Mi, hMi, ⟨e.symm⟩⟩

omit [∀ i, QuasiSeparatedSpace ((X ⋙ B.inclusion).obj i)] in
/-- **Stacks 01ZR (3) on the small étale sites.** -/
theorem smallEtalePullbackSystem_faithfulness (hc : IsLimit (B.inclusion.mapCone c)) :
    (smallEtalePullbackSystem B X c).Faithfulness :=
  (associatedModuleTransferUp B X c).faithfulness (zariskiSystem_faithfulness B X c hc)

/-- **Stacks 01ZR (2) on the small étale sites.** -/
theorem smallEtalePullbackSystem_fullness (hc : IsLimit (B.inclusion.mapCone c)) :
    (smallEtalePullbackSystem B X c).Fullness :=
  (associatedModuleTransferUp B X c).fullness (zariskiSystem_fullness B X c hc)

/-- **Stacks 01ZR (1) on the small étale sites.** -/
theorem smallEtalePullbackSystem_essSurj (hc : IsLimit (B.inclusion.mapCone c)) :
    (smallEtalePullbackSystem B X c).EssSurj :=
  (associatedModuleTransferUp B X c).essSurj (zariskiSystem_essSurj B X c hc)

omit [∀ i, QuasiSeparatedSpace ((X ⋙ B.inclusion).obj i)] in
/-- **Stacks 01ZR (3) on the small étale sites**, written out. -/
theorem smallEtale_faithfulness (hc : IsLimit (B.inclusion.mapCone c)) (k : I)
    (M N : SheafOfModules.{u} (structureSheaf B (X.obj k).obj (X.obj k).property))
    (hM : M.IsFinitePresentation) (hN : N.IsFinitePresentation) (φ ψ : M ⟶ N)
    (h : (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B (X := c.pt)
        (c.π.app k))).map φ =
      (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B (X := c.pt) (c.π.app k))).map ψ) :
    ∃ (j : I) (e : j ⟶ k),
      (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B (X.map e))).map φ =
        (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B (X.map e))).map ψ :=
  smallEtalePullbackSystem_faithfulness B X c hc k M N hM hN φ ψ h

/-- **Stacks 01ZR (1) on the small étale sites**, written out. -/
theorem smallEtale_essSurj (hc : IsLimit (B.inclusion.mapCone c))
    (M : SheafOfModules.{u} (structureSheaf B c.pt.obj c.pt.property))
    (hM : M.IsFinitePresentation) :
    ∃ (k : I) (Mk : SheafOfModules.{u} (structureSheaf B (X.obj k).obj (X.obj k).property)),
      Mk.IsFinitePresentation ∧
        Nonempty ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B (X := c.pt)
          (c.π.app k))).obj Mk ≅ M) :=
  smallEtalePullbackSystem_essSurj B X c hc M hM

end AlgebraicGeometry.SmallEtale

end
