module

public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsMorphismFibreReading
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeTwistTensorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveSpaceSiteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreQuasiFiniteRepresentableNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableAmpleFibreNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOverTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleResidueFieldOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyRelativeAmple
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.AmpleRestrict
public import StacksFrontier.AlgebraicGeometry.Spaces.AmpleSchemeFibreTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspacePushforwardCech
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCoverTwistVanishing
public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.FibreImmersion

/-!
# Stacks 0D3A: ampleness near a fibre which is a scheme, from Stacks 0D39

Let `Y` be a Noetherian scheme of the site, `f : X ⟶ h_Y` a proper morphism from an algebraic
space, `ℒ` an invertible `𝒪_X`-module and `y ∈ Y` a point whose fibre `X_y` is a scheme on which
`ℒ` is ample.  This file assembles the proof of Stacks 0D3A from the conclusion of Stacks 0D39
(`AlgebraicGeometry.Space.AmpleSchemeFibreTwistStatement`): there is an open neighbourhood `V` of
`y` such that the pullback of `ℒ` is ample on every base change of `f` along `openSub Y V ⟶ Y`.

The proof follows the source.  Sections `s_{y,0}, …, s_{y,r}` of `ℒ_y^{⊗ d}` giving an immersion
`X_y ⟶ ℙʳ_{κ(y)}` (Stacks 01VT) lift by Stacks 0D39 to sections of `ℒ^{⊗ d}` over `X_V`; on the
open subspace where they generate they define `φ : U ⟶ ℙʳ_V` (Stacks 01ND,
`AlgebraicGeometry.Space.sectionsMorphismToProjectiveSpace`), which restricts on the fibre to the
immersion.  Hence `φ` is quasi-finite along the fibre, so near the fibre `X` is a scheme
(`AlgebraicGeometry.Space.exists_mem_isRepresentable_of_isLocallyQuasiFinite_fibre`; the source
reaches this through finiteness, Stacks 0A4W), and the scheme case Stacks 0D2N applies
(`AlgebraicGeometry.Space.exists_mem_isRelativelyAmple_of_isRepresentable`).

## Main results

* `AlgebraicGeometry.Space.exists_fibreSections_lift`: the fibre sections and their lifts.
* `AlgebraicGeometry.Space.exists_mem_isRepresentable_of_fibreSections`: `X` is a scheme near the
  fibre.
* `AlgebraicGeometry.Space.exists_mem_isRelativelyAmpleOver_of_isRepresentable_openSub`: Stacks
  0D2N on that neighbourhood, read over the base.
* `AlgebraicGeometry.Space.exists_mem_isRelativelyAmple_openSub_of_fibreSquare`: Stacks 0D3A from
  the conclusion of Stacks 0D39, the fibre given as a scheme by a cartesian square.
* `AlgebraicGeometry.Space.exists_mem_isRelativelyAmple_openSub_of_isRelativelyAmple_residueField`:
  the same with the hypothesis read through Stacks 0D31 on every base change to `Spec κ(y)`, the
  form consumed by the proof of Stacks 0D3D.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The value at a terminal chart of the global section with a prescribed value there. -/
theorem spaceModuleSections_sectionsEvalAddEquiv_symm_val {Z : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS Z.1 Z.2) {V : SmallEtale B S hS Z.1} (hV : IsTerminal V)
    (z : M.val.obj (op V)) :
    (((sectionsEvalAddEquiv M hV).symm z : spaceModuleSections Z M)).1 (op V) = z :=
  (sectionsEvalAddEquiv_apply M hV _).symm.trans (AddEquiv.apply_symm_apply _ _)

/-- **A residue-field point through an open immersion.**  If `g : K ⟶ A` followed by an open
immersion `i : A ⟶ B` is `K ≅ Spec κ(b) ⟶ B`, then `g` is `K ≅ Spec κ(a) ⟶ A` for every `a` over
`b`: the open immersion identifies the residue fields. -/
theorem exists_iso_comp_fromSpecResidueField_of_isOpenImmersion {A B K : Scheme.{u}} (i : A ⟶ B)
    [_root_.AlgebraicGeometry.IsOpenImmersion i] (a : A) (b : B) (hab : i a = b)
        (e : K ≅ Spec (B.residueField b))
    (g : K ⟶ A) (hg : g ≫ i = e.hom ≫ B.fromSpecResidueField b) :
    ∃ e' : K ≅ Spec (A.residueField a), e'.hom ≫ A.fromSpecResidueField a = g := by
  let ψ : A.residueField a ⟶ B.residueField b :=
    inv (i.residueFieldMap a) ≫ (B.residueFieldCongr hab).hom
  refine ⟨e ≪≫ asIso (Spec.map ψ), ?_⟩
  rw [← cancel_mono i, Iso.trans_hom, asIso_hom, Category.assoc, Category.assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc (Spec.map ψ),
    ← Spec.map_comp, hg]
  congr 1
  have : i.residueFieldMap a ≫ ψ = (B.residueFieldCongr hab).hom := by
    simp [ψ]
  rw [this, Scheme.residueFieldCongr_fromSpecResidueField]

/-- **Lifting finitely many fibre sections at once**, from the monotone lifting clause of Stacks
0D39 for one section: over the intersection of the neighbourhoods attached to each section, all
of them lift. -/
theorem exists_open_restrictSectionAlong_eq_of_forall {Y : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (f : X ⟶ representedAlgebraicSpace B S hS Y)
    (y : (BigFppfOver.toScheme B S hS).obj Y) (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1)
    (G : Modules.{u, u} B S hS X.1 X.2)
    (hconc : ∀ t : spaceModuleSections (representedAlgebraicSpace B S hS U)
        ((modulePullback B S hS (ObjectProperty.homMk p :
          representedAlgebraicSpace B S hS U ⟶ X)).obj G),
      ∃ V : ((BigFppfOver.toScheme B S hS).obj Y).Opens, y ∈ V ∧
        ∀ W : ((BigFppfOver.toScheme B S hS).obj Y).Opens, W ≤ V → y ∈ W →
        ∀ ⦃XW : AlgebraicSpaces B S hS⦄ (pW : XW ⟶ X)
          (fW : XW ⟶ representedAlgebraicSpace B S hS (openSiteObject B S hS Y W)),
          IsPullback pW fW f
            (ObjectProperty.homMk (yoneda.map (openSiteObjectHom B S hS Y W))) →
          ∀ (jW : yoneda.obj U ⟶ XW.1) (h : jW ≫ pW.hom = p),
            ∃ s : spaceModuleSections XW ((modulePullback B S hS pW).obj G),
              restrictSectionAlong pW U jW p h G s = t)
    {r : ℕ} (t' : Fin (r + 1) → spaceModuleSections (representedAlgebraicSpace B S hS U)
        ((modulePullback B S hS (ObjectProperty.homMk p :
          representedAlgebraicSpace B S hS U ⟶ X)).obj G))
    (z : Fin (r + 1) → ((modulePullback B S hS (ObjectProperty.homMk p :
          representedAlgebraicSpace B S hS U ⟶ X)).obj G).val.obj (op (idEtaleChart B S hS U)))
    (ht' : ∀ i, (t' i).1 (op (idEtaleChart B S hS U)) = z i) :
    ∃ V₀ : ((BigFppfOver.toScheme B S hS).obj Y).Opens, y ∈ V₀ ∧
      ∀ W : ((BigFppfOver.toScheme B S hS).obj Y).Opens, W ≤ V₀ → y ∈ W →
      ∀ ⦃XW : AlgebraicSpaces B S hS⦄ (pW : XW ⟶ X)
        (fW : XW ⟶ representedAlgebraicSpace B S hS (openSiteObject B S hS Y W)),
        IsPullback pW fW f
          (ObjectProperty.homMk (yoneda.map (openSiteObjectHom B S hS Y W))) →
        ∀ (jW : yoneda.obj U ⟶ XW.1) (h : jW ≫ pW.hom = p),
          ∃ s : Fin (r + 1) → spaceModuleSections XW ((modulePullback B S hS pW).obj G),
            ∀ i, (restrictSectionAlong pW U jW p h G (s i)).1 (op (idEtaleChart B S hS U)) =
              z i := by
  choose V hyV hV using fun i ↦ hconc (t' i)
  let V₀ : ((BigFppfOver.toScheme B S hS).obj Y).Opens :=
    ⟨⋂ i, ((V i : ((BigFppfOver.toScheme B S hS).obj Y).Opens) :
      Set ((BigFppfOver.toScheme B S hS).obj Y)), isOpen_iInter_of_finite fun i ↦ (V i).isOpen⟩
  refine ⟨V₀, Set.mem_iInter.2 hyV, fun W hW hyW XW pW fW hsqW jW h ↦ ?_⟩
  choose s hs using fun i ↦ hV i W (hW.trans (show V₀ ≤ V i from Set.iInter_subset _ i)) hyW pW
    fW hsqW jW h
  exact ⟨s, fun i ↦ by rw [hs i]; exact ht' i⟩

/-- **The fibre sections of Stacks 0D3A and their lifts.**  There are `d` and sections
`t_0, …, t_r` of `ℒ_y^{⊗ (d+1)}` generating it and defining an immersion `X_y ⟶ ℙʳ_{κ(y)}`, and an
open neighbourhood `V₀` of `y` such that over every smaller open neighbourhood `W` the `t_i`, read
as sections of `p^*(𝒪_X ⊗ ℒ^{⊗ (d+1)})` through an identification `E`, lift to `X_W`. -/
theorem exists_fibreSections_lift (h0D39 : AmpleSchemeFibreTwistStatement B S hS)
    {Y : BigFppfOver B S hS}
    [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ representedAlgebraicSpace B S hS Y)
    (hf : IsProper B S hS f.hom) (L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L]
    (y : (BigFppfOver.toScheme B S hS).obj Y) (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1)
    (q : U ⟶ residuePointObject Y y)
    (hsq : IsPullback p (yoneda.map q) f.hom (yoneda.map (residuePointHom Y y)))
    (hamp : ∃ hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U p), @Stacks.Ample.IsAmple _ _ hL) :
    ∃ (_ : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS L U p)) (d r : ℕ)
      (E : restrictToChartSchemeModules B S hS (representedAlgebraicSpace B S hS U).1
        (representedAlgebraicSpace B S hS U).2
        ((modulePullback B S hS (ObjectProperty.homMk p :
          representedAlgebraicSpace B S hS U ⟶ X)).obj
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O) ⊗ tensorPow B S hS L (d + 1)))
          (idEtaleChart B S hS U) ≅
        Stacks.Ample.tensorPowModule ((BigFppfOver.toScheme B S hS).obj U)
          (baseChangeModule B S hS L U p) ((d + 1 : ℕ) : ℤ))
      (t : Fin (r + 1) → Γ(Stacks.Ample.tensorPowModule ((BigFppfOver.toScheme B S hS).obj U)
          (baseChangeModule B S hS L U p) ((d + 1 : ℕ) : ℤ), ⊤))
      (ht : Stacks.ProjectiveFromSections.GeneratesStalks t),
      _root_.AlgebraicGeometry.IsImmersion (Stacks.ProjectiveFromSections.toProjectiveSpaceOver t ht
        ((BigFppfOver.toScheme B S hS).map q)) ∧
      ∃ V₀ : ((BigFppfOver.toScheme B S hS).obj Y).Opens, y ∈ V₀ ∧
        ∀ W : ((BigFppfOver.toScheme B S hS).obj Y).Opens, W ≤ V₀ → y ∈ W →
        ∀ ⦃XW : AlgebraicSpaces B S hS⦄ (pW : XW ⟶ X)
          (fW : XW ⟶ representedAlgebraicSpace B S hS (openSiteObject B S hS Y W)),
          IsPullback pW fW f
            (ObjectProperty.homMk (yoneda.map (openSiteObjectHom B S hS Y W))) →
          ∀ (jW : yoneda.obj U ⟶ XW.1) (h : jW ≫ pW.hom = p),
            ∃ s : Fin (r + 1) → spaceModuleSections XW
                ((modulePullback B S hS pW).obj
                    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O) ⊗ tensorPow B S hS L (d + 1))),
              ∀ i, (restrictSectionAlong pW U jW p h
                  (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O) ⊗ tensorPow B S hS L (d + 1)) (s i)).1
                  (op (idEtaleChart B S hS U)) =
                restrictToChartSchemeTopSectionsAddEquiv B S hS
                  (representedAlgebraicSpace B S hS U)
                  ((modulePullback B S hS (ObjectProperty.homMk p :
                    representedAlgebraicSpace B S hS U ⟶ X)).obj
                        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O) ⊗ tensorPow B S hS L (d + 1)))
                  (idEtaleChart B S hS U) (Scheme.Modules.Hom.app E.inv ⊤ (t i)) := by
  obtain ⟨hN, hampN⟩ := hamp
  -- the fibre `U ⟶ Spec κ(y)` is proper
  have hpq : IsProper B S hS (yoneda.map q) :=
    isProper_of_isPullback B S hS (isAlgebraicSpace_yoneda B S hS U) X.2
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS Y) hsq hf
  have : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map q) :=
    isProper_toScheme_map_of_isProper B S hS q hpq
  -- Stacks 01VT on the fibre
  open Stacks.AmpleFibreNeighbourhood in
  obtain ⟨d₀, -, himm⟩ :=
    exists_generatesStalks_isImmersion_toProjectiveSpaceOver_of_isAmple
      ((BigFppfOver.toScheme B S hS).map q) (baseChangeModule B S hS L U p) hampN
  -- Stacks 0D39 for the structure sheaf
  have : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2 (isAlgebraicSpace_yoneda B S hS Y)
      f.hom hf.2.1.1 (hasEtaleLocalProperty_of_representable B S hS _ _ Y (Iso.refl _)
        inferInstance)⟩
  obtain ⟨d₁, hd₁⟩ := h0D39 Y X f hf L
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))
    inferInstance y U p q hsq ⟨hN, hampN⟩
  obtain ⟨r, t, ht, himm'⟩ := himm (max d₀ d₁ + 1) (by omega)
  obtain ⟨E⟩ := nonempty_restrictToChartScheme_unit_tensor_tensorPow_iso L U p (max d₀ d₁)
  have hconc := (hd₁ (max d₀ d₁ + 1) (by omega)).2
  obtain ⟨t', ht'⟩ : ∃ t' : Fin (r + 1) → spaceModuleSections (representedAlgebraicSpace B S hS U)
      ((modulePullback B S hS (ObjectProperty.homMk p :
        representedAlgebraicSpace B S hS U ⟶ X)).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O) ⊗ tensorPow B S hS L (max d₀ d₁ + 1))),
      ∀ i, (t' i).1 (op (idEtaleChart B S hS U)) =
        restrictToChartSchemeTopSectionsAddEquiv B S hS (representedAlgebraicSpace B S hS U)
          ((modulePullback B S hS (ObjectProperty.homMk p :
            representedAlgebraicSpace B S hS U ⟶ X)).obj
                (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O) ⊗ tensorPow B S hS L (max d₀ d₁ + 1)))
          (idEtaleChart B S hS U) (Scheme.Modules.Hom.app E.inv ⊤ (t i)) :=
    ⟨fun i ↦ (sectionsEvalAddEquiv _ (isTerminalIdEtaleChart B S hS U)).symm
      (restrictToChartSchemeTopSectionsAddEquiv B S hS (representedAlgebraicSpace B S hS U) _
        (idEtaleChart B S hS U) (Scheme.Modules.Hom.app E.inv ⊤ (t i))),
      fun i ↦ spaceModuleSections_sectionsEvalAddEquiv_symm_val _ (isTerminalIdEtaleChart B S hS U)
        _⟩
  refine ⟨hN, max d₀ d₁, r, E, t, ht, himm', ?_⟩
  exact exists_open_restrictSectionAlong_eq_of_forall f y U p
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O) ⊗ tensorPow B S hS L (max d₀ d₁ + 1)) hconc t'
    (fun i ↦ restrictToChartSchemeTopSectionsAddEquiv B S hS (representedAlgebraicSpace B S hS U)
      _ (idEtaleChart B S hS U) (Scheme.Modules.Hom.app E.inv ⊤ (t i))) ht'

/-- **`X` is a scheme near the fibre** (the step of the proof of Stacks 0D3A after the
construction of `φ`).  Over `V₀` the lifted sections define `φ : U ⟶ ℙʳ_{V₀}` on the open subspace
`U` where they generate; `U` contains the fibre, and there `φ` is the immersion
`φ_{(ℒ_y^{⊗ (d+1)}, t)} : X_y ⟶ ℙʳ_{κ(y)}`, which is locally quasi-finite.  By
`AlgebraicGeometry.Space.exists_mem_isRepresentable_of_isLocallyQuasiFinite_fibre` the base change
of `X_{V₀}` to an open neighbourhood of the image of the fibre is representable. -/
theorem exists_mem_isRepresentable_of_fibreSections {Y : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (f : X ⟶ representedAlgebraicSpace B S hS Y)
    (hf : IsProper B S hS f.hom) (L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L]
    (y : (BigFppfOver.toScheme B S hS).obj Y) (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1)
    (q : U ⟶ residuePointObject Y y)
    (hsq : IsPullback p (yoneda.map q) f.hom (yoneda.map (residuePointHom Y y)))
    [Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U p)] {d r : ℕ}
    (E : restrictToChartSchemeModules B S hS (representedAlgebraicSpace B S hS U).1
      (representedAlgebraicSpace B S hS U).2
      ((modulePullback B S hS (ObjectProperty.homMk p :
        representedAlgebraicSpace B S hS U ⟶ X)).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O) ⊗ tensorPow B S hS L (d + 1)))
        (idEtaleChart B S hS U) ≅
      Stacks.Ample.tensorPowModule ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS L U p) ((d + 1 : ℕ) : ℤ))
    (t : Fin (r + 1) → Γ(Stacks.Ample.tensorPowModule ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS L U p) ((d + 1 : ℕ) : ℤ), ⊤))
    (ht : Stacks.ProjectiveFromSections.GeneratesStalks t)
    (himm : _root_.AlgebraicGeometry.IsImmersion
      (Stacks.ProjectiveFromSections.toProjectiveSpaceOver t ht
        ((BigFppfOver.toScheme B S hS).map q)))
    {T₀ : BigFppfOver B S hS} (ι₀ : T₀ ⟶ Y) [Mono ι₀]
    {XV : AlgebraicSpaces B S hS} (pV : XV ⟶ X) (fV : XV ⟶ representedAlgebraicSpace B S hS T₀)
    (hV : IsPullback pV fV f (ObjectProperty.homMk (yoneda.map ι₀)))
    (κ₀ : residuePointObject Y y ⟶ T₀) (hκ₀ : κ₀ ≫ ι₀ = residuePointHom Y y)
    (x₀ : XV.1.obj (op U)) (h : yonedaEquiv.symm x₀ ≫ pV.hom = p)
    (hfx : yonedaEquiv.symm x₀ ≫ fV.hom = yoneda.map (q ≫ κ₀))
    (s : Fin (r + 1) → spaceModuleSections XV
        ((modulePullback B S hS pV).obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O) ⊗ tensorPow B S hS L (d + 1))))
    (hs : ∀ i, (restrictSectionAlong pV U (yonedaEquiv.symm x₀) p h
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O) ⊗ tensorPow B S hS L (d + 1)) (s i)).1
        (op (idEtaleChart B S hS U)) =
      restrictToChartSchemeTopSectionsAddEquiv B S hS (representedAlgebraicSpace B S hS U)
        ((modulePullback B S hS (ObjectProperty.homMk p :
          representedAlgebraicSpace B S hS U ⟶ X)).obj
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O) ⊗ tensorPow B S hS L
          (d + 1))) (idEtaleChart B S hS U)
        (Scheme.Modules.Hom.app E.inv ⊤ (t i)))
    (k : (BigFppfOver.toScheme B S hS).obj (residuePointObject Y y)) :
    ∃ V : ((BigFppfOver.toScheme B S hS).obj T₀).Opens,
      (BigFppfOver.toScheme B S hS).map κ₀ k ∈ V ∧
      ∀ ⦃X₁ : AlgebraicSpaces B S hS⦄ (p₁ : X₁ ⟶ XV)
        (f₁ : X₁ ⟶ representedAlgebraicSpace B S hS (openSub T₀ V)),
        IsPullback p₁ f₁ fV (ObjectProperty.homMk (yoneda.map (openSubHom T₀ V))) →
        X₁.1.IsRepresentable := by
  have hV' := AlgebraicSpaces.isPullback_hom B S hS hV
  have hfV : IsProper B S hS fV.hom := isProper_of_isPullback B S hS XV.2 X.2
    (isAlgebraicSpace_yoneda B S hS T₀) (isAlgebraicSpace_yoneda B S hS Y) hV' hf
  -- the module, its invertibility, and the generation locus
  have hinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS XV.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS XV.1 XV.2).O)).property
        ((modulePullback B S hS pV).obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O) ⊗ tensorPow B S hS L (d + 1))) :=
    have := isInvertible_unit_tensor_tensorPow L (d + 1)
    isInvertible_modulePullback_stacks pV _
  obtain ⟨hx, hcl⟩ := exists_mem_sectionsGenerationLocus_pointClassifyingMap_eq pV U p _ hinv s x₀
    h E t ht hs
  -- `φ` on the generation locus
  have hO := isOpenSubspace_sectionsGenerationSubfunctor B S hS _ s hinv
    (isQuasicoherentOnSite_of_isInvertible' B S hS _ hinv)
  have hφ : sectionsMorphismToProjectiveSpace B S hS _ hinv s fV.hom ≫
      yoneda.map (projectiveSpaceOverSiteObjectProj B S hS T₀ r) =
      (sectionsGenerationLocus B S hS _ hinv s).ι ≫ fV.hom := by
    ext T x
    exact projectiveSpaceOverSiteHom_comp_proj B S hS r _ _
  -- the fibre point, through the generation locus
  obtain ⟨p', hp', hp''⟩ : ∃ p' : yoneda.obj U ⟶
      (sectionsGenerationLocus B S hS _ hinv s).toFunctor,
      p' ≫ (sectionsGenerationLocus B S hS _ hinv s).ι = yonedaEquiv.symm x₀ ∧
        yonedaEquiv p' = ⟨x₀, hx⟩ :=
    ⟨yonedaEquiv.symm ⟨x₀, hx⟩,
      (yonedaEquiv_symm_naturality_right U (sectionsGenerationLocus B S hS _ hinv s).ι
        ⟨x₀, hx⟩).trans rfl, Equiv.apply_symm_apply _ _⟩
  have hsq' : IsPullback (p' ≫ (sectionsGenerationLocus B S hS _ hinv s).ι) (yoneda.map q)
      fV.hom (yoneda.map κ₀) := by
    rw [hp']
    refine IsPullback.of_right ?_ (by rw [hfx, Functor.map_comp]) hV'
    change IsPullback (yonedaEquiv.symm x₀ ≫ pV.hom) (yoneda.map q) f.hom
      (yoneda.map κ₀ ≫ yoneda.map ι₀)
    rw [h, ← Functor.map_comp, hκ₀]
    exact hsq
  -- `φ` on the fibre is the immersion
  have hψι : yoneda.map (projectiveSpaceOverSiteHom B S hS r q
      (Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse t ht) ≫
        projectiveSpaceOverSiteBaseChange B S hS κ₀ r) =
      p' ≫ sectionsMorphismToProjectiveSpace B S hS _ hinv s fV.hom := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_yoneda_map, yonedaEquiv_comp, hp'']
    refine (projectiveSpaceOverSiteHom_comp_baseChange B S hS κ₀ r q _).trans ?_
    refine (?_ : _ = projectiveSpaceOverSiteHom B S hS r (fV.hom.app (op U) x₀)
      (pointClassifyingMap B S hS _ hinv s U ⟨x₀, hx⟩)).trans
      (sectionsMorphismToProjectiveSpace_app B S hS _ hinv s fV.hom U ⟨x₀, hx⟩).symm
    rw [hcl]
    congr 1
    have := congrArg yonedaEquiv hfx
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map] at this
    exact this.symm
  have hψ : IsLocallyQuasiFinite B S hS (yoneda.map (projectiveSpaceOverSiteHom B S hS r q
      (Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse t ht))) := by
    rw [isLocallyQuasiFinite_yoneda_map_iff]
    change ((@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@_root_.AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
        (Stacks.ProjectiveFromSections.toProjectiveSpaceOver t ht
          ((BigFppfOver.toScheme B S hS).map q))
    exact ⟨inferInstance, inferInstance⟩
  exact exists_mem_isRepresentable_of_isLocallyQuasiFinite_fibre B S hS fV hfV hO
    (projectiveSpaceOverSiteObjectProj B S hS T₀ r) _ hφ κ₀
    (projectiveSpaceOverSiteObjectProj B S hS _ r) (projectiveSpaceOverSiteBaseChange B S hS κ₀ r)
    (isPullback_projectiveSpaceOverSiteBaseChange B S hS κ₀ r) p' q hsq' _ hψι
    (projectiveSpaceOverSiteHom_comp_proj B S hS r _ _) hψ _ ⟨k, rfl⟩

attribute [local instance] pointTopology in
/-- **Ampleness over an open of an open, read over the ambient scheme.**  If the pullback of `ℒ`
to the base change `X_{V₀}` of `f` along `openSub Y V₀ ⟶ Y` is ample over the open subspace cut
out by an open `V'` of `V₀` containing `t`, then `ℒ` is ample over the open subspace cut out by an
open of `Y` containing the image of `t`. -/
theorem exists_mem_isRelativelyAmpleOver_of_openSub {Y : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} {f : X ⟶ schemeSpace Y}
    (L : Modules.{u, u} B S hS X.1 X.2) {V₀ : ((BigFppfOver.toScheme B S hS).obj Y).Opens}
    {XV : AlgebraicSpaces B S hS} {pV : XV ⟶ X} {fV : XV ⟶ schemeSpace (openSub Y V₀)}
    (hV : IsPullback pV fV f (schemeSpaceMap (openSubHom Y V₀)))
    (V' : ((BigFppfOver.toScheme B S hS).obj (openSub Y V₀)).Opens)
    (t : (BigFppfOver.toScheme B S hS).obj (openSub Y V₀)) (ht : t ∈ V')
    (h : IsRelativelyAmpleOver fV ((modulePullback B S hS pV).obj L)
      (Subfunctor.range (yoneda.map (openSubHom (openSub Y V₀) V')))) :
    ∃ V : ((BigFppfOver.toScheme B S hS).obj Y).Opens,
      (BigFppfOver.toScheme B S hS).map (openSubHom Y V₀) t ∈ V ∧
      IsRelativelyAmpleOver f L (Subfunctor.range (yoneda.map (openSubHom Y V))) := by
  have _ : Mono (yoneda.map (openSubHom Y V₀)) :=
    mono_of_presheaf_isOpenImmersion (isOpenImmersion_yoneda_map_openSubHom Y V₀)
  have _ : Mono (yoneda.map (openSubHom (openSub Y V₀) V')) :=
    mono_of_presheaf_isOpenImmersion (isOpenImmersion_yoneda_map_openSubHom (openSub Y V₀) V')
  have _ : Mono (schemeSpaceMap (openSubHom Y V₀) :
      schemeSpace (openSub Y V₀) ⟶ schemeSpace Y).hom :=
    inferInstanceAs (Mono (yoneda.map (openSubHom Y V₀)))
  have h₂ := isRelativelyAmpleOver_range_of_isPullback hV L h
  -- the open subspace and the point
  have hW₁ : IsOpenSubspace B S hS (Subfunctor.range (yoneda.map (openSubHom (openSub Y V₀) V'))) :=
    isOpenSubspace_subfunctorRange B S hS (isAlgebraicSpace_yoneda B S hS _)
      (isOpenImmersion_yoneda_map_openSubHom (openSub Y V₀) V')
  have hW : IsOpenSubspace B S hS (Subfunctor.range
      ((Subfunctor.range (yoneda.map (openSubHom (openSub Y V₀) V'))).ι ≫
        yoneda.map (openSubHom Y V₀))) :=
    isOpenSubspace_subfunctorRange B S hS hW₁.1
      (isOpenImmersion_comp B S hS _ _ hW₁.2 (isOpenImmersion_yoneda_map_openSubHom Y V₀))
  have hpt : (schemePointsHomeomorph B S hS Y).symm
      ((BigFppfOver.toScheme B S hS).map (openSubHom Y V₀) t) ∈ Set.range (pointsMap B S hS _
        (Subfunctor.range ((Subfunctor.range (yoneda.map (openSubHom (openSub Y V₀) V'))).ι ≫
          yoneda.map (openSubHom Y V₀))).ι) := by
    refine ⟨pointsMap B S hS _ (Subfunctor.toRange _)
      (pointsMap B S hS _ (Subfunctor.toRange _)
        ((schemePointsHomeomorph B S hS (openSub (openSub Y V₀) V')).symm ⟨t, ht⟩)), ?_⟩
    rw [← pointsMap_comp_apply, Subfunctor.toRange_ι, pointsMap_comp_apply,
      ← pointsMap_comp_apply B S hS (Subfunctor.toRange _), Subfunctor.toRange_ι]
    refine (congrArg (pointsMap B S hS _ (yoneda.map (openSubHom Y V₀)))
      (schemePointsHomeomorph_symm_naturality B S hS (openSubHom (openSub Y V₀) V') _)).trans ?_
    refine (schemePointsHomeomorph_symm_naturality B S hS (openSubHom Y V₀) _).trans ?_
    congr 2
    rw [toScheme_map_openSubHom]
    rfl
  obtain ⟨V, hyV, hle⟩ := exists_mem_range_openSubHom_le hW _ hpt
  refine ⟨V, hyV, h₂.mono ?_⟩
  exact hle

/-- Ampleness of `ℒ` over `U` through `j' ≫ p` is ampleness of `p^*ℒ` over `U` through `j'`. -/
private theorem exists_isAmple_baseChangeModule_iff {X X' : AlgebraicSpaces B S hS} (p : X' ⟶ X)
    (L : Modules.{u, u} B S hS X.1 X.2) (U : BigFppfOver B S hS) (j' : yoneda.obj U ⟶ X'.1)
    (j : yoneda.obj U ⟶ X.1) (h : j' ≫ p.hom = j) :
    (∃ hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U j), @Stacks.Ample.IsAmple _ _ hL) ↔
    ∃ hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS ((modulePullback B S hS p).obj L) U j'),
      @Stacks.Ample.IsAmple _ _ hL := by
  subst h
  have e := baseChangeModuleCompIso B S hS p L U j'
  constructor
  · rintro ⟨hN, hA⟩
    have : Stacks.Ample.IsInvertibleModule _
        (baseChangeModule B S hS ((modulePullback B S hS p).obj L) U j') :=
      Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e
    exact ⟨inferInstance, (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mp hA⟩
  · rintro ⟨hN, hA⟩
    have : Stacks.Ample.IsInvertibleModule _ (baseChangeModule B S hS L U (j' ≫ p.hom)) :=
      Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e.symm
    exact ⟨inferInstance, (Stacks.RelativeVeryAmple.isAmple_congr _ _ e.symm).mp hA⟩

/-- **Stacks 0D2N on the representable neighbourhood, read over the base.**  Let
`fV : X_V ⟶ h_{T₀}` be proper over a Noetherian `T₀`, `ℒ_V` invertible, `κ₀ : K ⟶ T₀` with `K`
the spectrum of the residue field at `κ₀ k`, and `j` a base change of `fV` along `κ₀` on which
`ℒ_V` is ample.  If the base change of `X_V` to an open `V_Q ∋ κ₀ k` is representable, then `ℒ_V`
is ample over the open subspace cut out by an open of `T₀` containing `κ₀ k`. -/
theorem exists_mem_isRelativelyAmpleOver_of_isRepresentable_openSub {T₀ : BigFppfOver B S hS}
    [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj T₀)]
    {XV : AlgebraicSpaces B S hS} (fV : XV ⟶ schemeSpace T₀)
    (hfV : IsProper B S hS fV.hom) (LV : Modules.{u, u} B S hS XV.1 XV.2)
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS XV.1 XV.2).obj
      (structureRingPresheaf_isSheaf B S hS XV.1 XV.2) LV]
    {K U : BigFppfOver B S hS} (κ₀ : K ⟶ T₀) (j : yoneda.obj U ⟶ XV.1) (q : U ⟶ K)
    (hsq : IsPullback j (yoneda.map q) fV.hom (yoneda.map κ₀))
    (k : (BigFppfOver.toScheme B S hS).obj K)
    (eK : (BigFppfOver.toScheme B S hS).obj K ≅
      Spec (((BigFppfOver.toScheme B S hS).obj T₀).residueField
        ((BigFppfOver.toScheme B S hS).map κ₀ k)))
    (heK : eK.hom ≫ ((BigFppfOver.toScheme B S hS).obj T₀).fromSpecResidueField
        ((BigFppfOver.toScheme B S hS).map κ₀ k) = (BigFppfOver.toScheme B S hS).map κ₀)
    (hamp : ∃ hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS LV U j), @Stacks.Ample.IsAmple _ _ hL)
    (VQ : ((BigFppfOver.toScheme B S hS).obj T₀).Opens)
    (hk : (BigFppfOver.toScheme B S hS).map κ₀ k ∈ VQ)
    (hrep : ∀ ⦃X₁ : AlgebraicSpaces B S hS⦄ (p₁ : X₁ ⟶ XV)
        (f₁ : X₁ ⟶ schemeSpace (openSub T₀ VQ)),
        IsPullback p₁ f₁ fV (schemeSpaceMap (openSubHom T₀ VQ)) →
        X₁.1.IsRepresentable) :
    ∃ V : ((BigFppfOver.toScheme B S hS).obj T₀).Opens,
      (BigFppfOver.toScheme B S hS).map κ₀ k ∈ V ∧
      IsRelativelyAmpleOver fV LV (Subfunctor.range (yoneda.map (openSubHom T₀ V))) := by
  let ι₁ : schemeSpace (openSub T₀ VQ) ⟶
      schemeSpace T₀ :=
    schemeSpaceMap (openSubHom T₀ VQ)
  have hsq₁ := AlgebraicSpaces.isPullback_fiberProduct B S hS fV ι₁
  let X₁ := AlgebraicSpaces.fiberProduct B S hS fV ι₁
  let p₁ : X₁ ⟶ XV := ObjectProperty.homMk (pullback.fst fV.hom ι₁.hom)
  let f₁ : X₁ ⟶ schemeSpace (openSub T₀ VQ) :=
    ObjectProperty.homMk (pullback.snd fV.hom ι₁.hom)
  have : X₁.1.IsRepresentable := hrep p₁ f₁ hsq₁
  -- every point of `K` maps to `κ₀ k`, so `κ₀` factors through `V_Q`
  have hall : ∀ x, (BigFppfOver.toScheme B S hS).map κ₀ x ∈ VQ := by
    intro x
    have : eK.hom x = eK.hom k := Subsingleton.elim _ _
    rwa [← heK, Scheme.Hom.comp_apply, this, ← Scheme.Hom.comp_apply, heK]
  let κ₁ : K ⟶ openSub T₀ VQ := openSubLift T₀ VQ κ₀ hall
  have hκ₁ : κ₁ ≫ openSubHom T₀ VQ = κ₀ := openSubLift_comp_openSubHom T₀ VQ κ₀ hall
  have hι₁ : yoneda.map κ₁ ≫ ι₁.hom = yoneda.map κ₀ :=
    (yoneda.map_comp κ₁ (openSubHom T₀ VQ)).symm.trans (congrArg (fun g => yoneda.map g) hκ₁)
  let j₁ : yoneda.obj U ⟶ X₁.1 := pullback.lift j (yoneda.map (q ≫ κ₁))
    (hsq.w.trans ((congrArg (yoneda.map q ≫ ·) hι₁.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ ι₁.hom) (yoneda.map_comp q κ₁).symm))))
  have hj₁ : j₁ ≫ p₁.hom = j := pullback.lift_fst _ _ _
  have hsq₁' : IsPullback j₁ (yoneda.map q) f₁.hom (yoneda.map κ₁) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback fV.hom ι₁.hom)
    change IsPullback (j₁ ≫ p₁.hom) (yoneda.map q) fV.hom (yoneda.map κ₁ ≫ ι₁.hom)
    rwa [hj₁, hι₁]
  -- the hypotheses of Stacks 0D2N for `f₁`
  have : _root_.AlgebraicGeometry.IsNoetherian
      ((BigFppfOver.toScheme B S hS).obj (openSub T₀ VQ)) :=
    Stacks.AmpleRestrict.isNoetherian_opens_toScheme VQ
  have hf₁ : IsProper B S hS f₁.hom :=
    isProper_of_isPullback B S hS X₁.2 XV.2 (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS T₀) (IsPullback.of_hasPullback fV.hom ι₁.hom) hfV
  have hL₁ : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X₁.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₁.1 X₁.2).O)).property
        ((modulePullback B S hS p₁).obj LV) :=
    isInvertible_modulePullback_stacks p₁ LV
  have hamp₁ : ∃ hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS ((modulePullback B S hS p₁).obj LV) U j₁),
      @Stacks.Ample.IsAmple _ _ hL := by
    exact (exists_isAmple_baseChangeModule_iff p₁ LV U j₁ j hj₁).1 hamp
  -- the residue field at the image point in `V_Q`
  have : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (openSubHom T₀ VQ)) := by
    rw [toScheme_map_openSubHom]
    exact Scheme.Opens.instIsOpenImmersionι VQ
  have hab : (BigFppfOver.toScheme B S hS).map (openSubHom T₀ VQ)
      ((BigFppfOver.toScheme B S hS).map κ₁ k) = (BigFppfOver.toScheme B S hS).map κ₀ k := by
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hκ₁]
  obtain ⟨eK₁, heK₁⟩ := exists_iso_comp_fromSpecResidueField_of_isOpenImmersion
    ((BigFppfOver.toScheme B S hS).map (openSubHom T₀ VQ)) _ _ hab eK
    ((BigFppfOver.toScheme B S hS).map κ₁) (by rw [← Functor.map_comp, hκ₁, heK])
  obtain ⟨V', hV'k, hV'⟩ := exists_mem_isRelativelyAmple_of_isRepresentable f₁ hf₁
    ((modulePullback B S hS p₁).obj LV) hL₁ κ₁ j₁ q hsq₁' _ eK₁ heK₁ hamp₁
  have hover := isRelativelyAmpleOver_range_openSubHom f₁ ((modulePullback B S hS p₁).obj LV) V'
    hV'
  obtain ⟨V, hV, hamp'⟩ := exists_mem_isRelativelyAmpleOver_of_openSub LV hsq₁ V' _ hV'k hover
  exact ⟨V, hab ▸ hV, hamp'⟩

/-- `AlgebraicGeometry.Space.openSub` and `AlgebraicGeometry.Space.openSiteObject` are the same
open subscheme, with structure morphisms equal up to the spelling of the inclusion. -/
def openSubIsoOpenSiteObject (Y : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj Y).Opens) :
    openSub Y W ≅ openSiteObject B S hS Y W :=
  Over.isoMk (Iso.refl _ : (openSub Y W).left ≅ (openSiteObject B S hS Y W).left) (by
    refine (Category.id_comp _).trans ?_
    apply B.inclusion.map_injective
    simp only [openSiteObject, openSub, Over.mk_hom, Functor.map_comp, Functor.map_preimage]
    rfl)

/-- `AlgebraicGeometry.Space.openSubIsoOpenSiteObject` is compatible with the two inclusions. -/
theorem openSubIsoOpenSiteObject_hom_comp (Y : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj Y).Opens) :
    (openSubIsoOpenSiteObject Y W).hom ≫ openSiteObjectHom B S hS Y W = openSubHom Y W := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, map_openSiteObjectHom, toScheme_map_openSubHom]
  exact Category.id_comp W.ι

/-- A base change of `f` along `openSub Y W ⟶ Y` is one along `openSiteObject Y W ⟶ Y`. -/
theorem isPullback_openSiteObjectHom_of_openSubHom {Y : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} {f : X ⟶ schemeSpace Y}
    {W : ((BigFppfOver.toScheme B S hS).obj Y).Opens} {XW : AlgebraicSpaces B S hS}
    {pW : XW ⟶ X} {fW : XW ⟶ schemeSpace (openSub Y W)}
    (hW : IsPullback pW fW f (schemeSpaceMap (openSubHom Y W))) :
    IsPullback pW (fW ≫ (ObjectProperty.homMk (yoneda.map (openSubIsoOpenSiteObject Y W).hom) :
        schemeSpace (openSub Y W) ⟶
          schemeSpace (openSiteObject B S hS Y W))) f
      (schemeSpaceMap (openSiteObjectHom B S hS Y W) :
        schemeSpace (openSiteObject B S hS Y W) ⟶
          schemeSpace Y) := by
  have hW' := AlgebraicSpaces.isPullback_hom B S hS hW
  have h : IsPullback pW.hom (fW.hom ≫ yoneda.map (openSubIsoOpenSiteObject Y W).hom) f.hom
      (yoneda.map (openSiteObjectHom B S hS Y W)) :=
    IsPullback.of_iso hW' (Iso.refl _) (Iso.refl _) (yoneda.mapIso (openSubIsoOpenSiteObject Y W))
      (Iso.refl _) (by simp) (by simp) (by simp) (by
        rw [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom]
        exact (schemeSpaceMap_hom _).trans ((congrArg (fun g => yoneda.map g)
          (openSubIsoOpenSiteObject_hom_comp Y W)).symm.trans (yoneda.map_comp _ _)))
  exact IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ h.w) h

/-- **Stacks 0D3A, from Stacks 0D39, on a chosen fibre square.**  Let `Y` be a Noetherian scheme of
the site, `f : X ⟶ h_Y` proper, `ℒ` invertible, and `y ∈ Y` such that the base change
`U ⟶ Spec κ(y)` of `f` (a scheme, given by the cartesian square `hsq`) carries an ample pullback of
`ℒ`.  Granting the conclusion of Stacks 0D39, there is an open `V ∋ y` of `Y` such that the
pullback of `ℒ` is ample on every base change of `f` along `V ⟶ Y`. -/
theorem exists_mem_isRelativelyAmple_openSub_of_fibreSquare
    (h0D39 : AmpleSchemeFibreTwistStatement B S hS) {Y : BigFppfOver B S hS}
    [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ representedAlgebraicSpace B S hS Y)
    (hf : IsProper B S hS f.hom) (L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L]
    (y : (BigFppfOver.toScheme B S hS).obj Y) (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1)
    (q : U ⟶ residuePointObject Y y)
    (hsq : IsPullback p (yoneda.map q) f.hom (yoneda.map (residuePointHom Y y)))
    (hamp : ∃ hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U p), @Stacks.Ample.IsAmple _ _ hL) :
    ∃ V : ((BigFppfOver.toScheme B S hS).obj Y).Opens, y ∈ V ∧
      ∀ ⦃X₁ : AlgebraicSpaces B S hS⦄ (p₁ : X₁ ⟶ X)
        (f₁ : X₁ ⟶ representedAlgebraicSpace B S hS (openSub Y V)),
        IsPullback p₁ f₁ f (ObjectProperty.homMk (yoneda.map (openSubHom Y V))) →
        IsRelativelyAmple B S hS f₁ ((modulePullback B S hS p₁).obj L) := by
  obtain ⟨hN, d, r, E, t, ht, himm, V₀, hyV₀, hlift⟩ :=
    exists_fibreSections_lift h0D39 f hf L y U p q hsq hamp
  -- the base change to `V₀`
  let ι₀ : representedAlgebraicSpace B S hS (openSub Y V₀) ⟶
      representedAlgebraicSpace B S hS Y :=
    ObjectProperty.homMk (yoneda.map (openSubHom Y V₀))
  have hV := AlgebraicSpaces.isPullback_fiberProduct B S hS f ι₀
  let XV := AlgebraicSpaces.fiberProduct B S hS f ι₀
  let pV : XV ⟶ X := ObjectProperty.homMk (pullback.fst f.hom ι₀.hom)
  let fV : XV ⟶ representedAlgebraicSpace B S hS (openSub Y V₀) :=
    ObjectProperty.homMk (pullback.snd f.hom ι₀.hom)
  have _ : Mono (openSubHom Y V₀) := mono_openSubHom_of_opens Y V₀
  -- `Spec κ(y) ⟶ Y` factors through `V₀`
  have hpt : ∀ x : (BigFppfOver.toScheme B S hS).obj (residuePointObject Y y),
      (BigFppfOver.toScheme B S hS).map (residuePointHom Y y) x = y := fun x ↦
    (((BigFppfOver.toScheme B S hS).obj Y).range_fromSpecResidueField y).subset ⟨x, rfl⟩
  have hall : ∀ x, (BigFppfOver.toScheme B S hS).map (residuePointHom Y y) x ∈ V₀ :=
    fun x ↦ (hpt x).symm ▸ hyV₀
  let κ₀ : residuePointObject Y y ⟶ openSub Y V₀ := openSubLift Y V₀ (residuePointHom Y y) hall
  have hκ₀ : κ₀ ≫ openSubHom Y V₀ = residuePointHom Y y :=
    openSubLift_comp_openSubHom Y V₀ (residuePointHom Y y) hall
  -- the fibre inside `X_{V₀}`
  let j₀ : yoneda.obj U ⟶ XV.1 := pullback.lift p (yoneda.map (q ≫ κ₀)) (by
    change p ≫ f.hom = yoneda.map (q ≫ κ₀) ≫ yoneda.map (openSubHom Y V₀)
    rw [← Functor.map_comp, Category.assoc, hκ₀, hsq.w, Functor.map_comp])
  have h : yonedaEquiv.symm (yonedaEquiv j₀) ≫ pV.hom = p :=
    (yonedaEquiv.symm_apply_apply j₀).symm ▸ pullback.lift_fst _ _ _
  have hfx : yonedaEquiv.symm (yonedaEquiv j₀) ≫ fV.hom = yoneda.map (q ≫ κ₀) :=
    (yonedaEquiv.symm_apply_apply j₀).symm ▸ pullback.lift_snd _ _ _
  have hsq₀ : IsPullback (yonedaEquiv.symm (yonedaEquiv j₀)) (yoneda.map q) fV.hom
      (yoneda.map κ₀) := by
    refine IsPullback.of_right ?_ hfx (AlgebraicSpaces.isPullback_hom B S hS hV)
    change IsPullback (yonedaEquiv.symm (yonedaEquiv j₀) ≫ pV.hom) (yoneda.map q) f.hom
      (yoneda.map κ₀ ≫ yoneda.map (openSubHom Y V₀))
    rw [h, ← Functor.map_comp, hκ₀]
    exact hsq
  obtain ⟨s, hs⟩ := hlift V₀ le_rfl hyV₀ pV _ (isPullback_openSiteObjectHom_of_openSubHom hV)
    (yonedaEquiv.symm (yonedaEquiv j₀)) h
  -- the point of the fibre and its residue field in `V₀`
  obtain ⟨k, -⟩ : ∃ k : (BigFppfOver.toScheme B S hS).obj (residuePointObject Y y), True :=
    ⟨IsLocalRing.closedPoint (((BigFppfOver.toScheme B S hS).obj Y).residueField y), trivial⟩
  have := hN
  obtain ⟨VQ, hkVQ, hrep⟩ := exists_mem_isRepresentable_of_fibreSections f hf L y U p q hsq E t
    ht himm (openSubHom Y V₀) pV fV hV κ₀ hκ₀ (yonedaEquiv j₀) h hfx s hs k
  have : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (openSubHom Y V₀)) := by
    rw [toScheme_map_openSubHom]
    exact Scheme.Opens.instIsOpenImmersionι V₀
  have hab : (BigFppfOver.toScheme B S hS).map (openSubHom Y V₀)
      ((BigFppfOver.toScheme B S hS).map κ₀ k) = y := by
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hκ₀]
    exact hpt k
  obtain ⟨eK, heK⟩ := exists_iso_comp_fromSpecResidueField_of_isOpenImmersion
    ((BigFppfOver.toScheme B S hS).map (openSubHom Y V₀)) _ _ hab
    (Iso.refl ((BigFppfOver.toScheme B S hS).obj (residuePointObject Y y)))
    ((BigFppfOver.toScheme B S hS).map κ₀) (by
      rw [← Functor.map_comp, hκ₀]
      exact (Category.id_comp _).symm)
  -- the hypotheses on `X_{V₀}`
  have : _root_.AlgebraicGeometry.IsNoetherian
      ((BigFppfOver.toScheme B S hS).obj (openSub Y V₀)) :=
    Stacks.AmpleRestrict.isNoetherian_opens_toScheme V₀
  have hfV : IsProper B S hS fV.hom :=
    isProper_of_isPullback B S hS XV.2 X.2 (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS Y) (IsPullback.of_hasPullback f.hom ι₀.hom) hf
  have := isInvertible_modulePullback_stacks pV L
  have hamp₀ : ∃ hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS ((modulePullback B S hS pV).obj L) U
        (yonedaEquiv.symm (yonedaEquiv j₀))), @Stacks.Ample.IsAmple _ _ hL := by
    exact (exists_isAmple_baseChangeModule_iff pV L U _ p h).1 hamp
  -- Stacks 0D2N near the fibre, then back to `Y`
  obtain ⟨V₁, hV₁, hover₁⟩ := exists_mem_isRelativelyAmpleOver_of_isRepresentable_openSub fV hfV
    ((modulePullback B S hS pV).obj L) κ₀ _ q hsq₀ k eK heK hamp₀ VQ hkVQ hrep
  obtain ⟨V, hyV, hover⟩ := exists_mem_isRelativelyAmpleOver_of_openSub L hV V₁ _ hV₁ hover₁
  exact ⟨V, hab ▸ hyV, fun X₁ p₁ f₁ hsq₁ ↦ hover.isRelativelyAmple_openSub V p₁ f₁ hsq₁⟩

/-- **Stacks 0D3A, from Stacks 0D39, with the hypothesis on the residue field read through Stacks
0D31.**  If the pullback of `ℒ` is ample on every base change of `f` along `Spec κ(y) ⟶ Y`, then
the fibre is a scheme on which `ℒ` is ample (Stacks 0D32, 01VK), and the previous theorem
applies. -/
theorem exists_mem_isRelativelyAmple_openSub_of_isRelativelyAmple_residueField
    (h0D39 : AmpleSchemeFibreTwistStatement B S hS) {Y : BigFppfOver B S hS}
    [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ representedAlgebraicSpace B S hS Y)
    (hf : IsProper B S hS f.hom) (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property
        L)
    (y : (BigFppfOver.toScheme B S hS).obj Y)
    (hy : ∀ ⦃X₀ : AlgebraicSpaces B S hS⦄ (p₀ : X₀ ⟶ X)
      (f₀ : X₀ ⟶ representedAlgebraicSpace B S hS
        (residueFieldObject B S hS Y y (B.residueField_spec_contains Y.left.property y))),
      IsPullback p₀ f₀ f (ObjectProperty.homMk (yoneda.map
        (residueFieldMap B S hS Y y (B.residueField_spec_contains Y.left.property y)))) →
      IsRelativelyAmple B S hS f₀ ((modulePullback B S hS p₀).obj L)) :
    ∃ V : ((BigFppfOver.toScheme B S hS).obj Y).Opens, y ∈ V ∧
      ∀ ⦃X₁ : AlgebraicSpaces B S hS⦄ (p₁ : X₁ ⟶ X)
        (f₁ : X₁ ⟶ representedAlgebraicSpace B S hS (openSub Y V)),
        IsPullback p₁ f₁ f (ObjectProperty.homMk (yoneda.map (openSubHom Y V))) →
        IsRelativelyAmple B S hS f₁ ((modulePullback B S hS p₁).obj L) := by
  have : Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L := hL
  let ι : representedAlgebraicSpace B S hS (residuePointObject Y y) ⟶
      representedAlgebraicSpace B S hS Y :=
    ObjectProperty.homMk (yoneda.map (residuePointHom Y y))
  have hsq₀ := AlgebraicSpaces.isPullback_fiberProduct B S hS f ι
  have hamp₀ := hy _ _ hsq₀
  -- the fibre is a scheme
  obtain ⟨U, q, j, hj⟩ := hamp₀.1 (𝟙 (yoneda.obj (residuePointObject Y y)))
  have hsqU : IsPullback (j ≫ pullback.fst f.hom ι.hom) (yoneda.map q) f.hom
      (yoneda.map (residuePointHom Y y)) := by
    convert hj.paste_horiz (IsPullback.of_hasPullback f.hom ι.hom) using 1
    exact (Category.id_comp _).symm
  -- on which `ℒ` is ample
  obtain ⟨hN, hA⟩ := isAmple_baseChangeModule_of_isRelativelyAmple hamp₀ _ U
    (inferInstanceAs (IsAffine (Spec (((BigFppfOver.toScheme B S hS).obj Y).residueField y))))
    (𝟙 _) j q hj
  exact exists_mem_isRelativelyAmple_openSub_of_fibreSquare h0D39 f hf L y U _ q hsqU
    ((exists_isAmple_baseChangeModule_iff
      (ObjectProperty.homMk (pullback.fst f.hom ι.hom) :
        AlgebraicSpaces.fiberProduct B S hS f ι ⟶ X) L U j _ rfl).2 ⟨hN, hA⟩)

end AlgebraicGeometry.Space

end
