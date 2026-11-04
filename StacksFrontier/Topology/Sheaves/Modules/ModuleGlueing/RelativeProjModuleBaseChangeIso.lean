module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleBaseChangeGlued
public import StacksFrontier.AlgebraicGeometry.ModuleChartLocality.Chart
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ModulePieceBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.PullbackSituation

/-!
# The base-change comparison of `ℳ̃` is an isomorphism

Let `g : S' ⟶ S`, let `s` and `s'` be relative `Proj` situations over `S` and `S'`, let `Φ`
identify the graded algebra of `s'` with the pullback of that of `s`, let `Ψ` identify `ℳ'` with
the pullback of `ℳ` degreewise, and let `r = relativeProjBaseChange g Φ hΦ`.
`Stacks.RelativeProj.Situation.moduleSheafBaseChangeHom` is the comparison `r^* ℳ̃ ⟶ ℳ̃'` glued
from the chart comparisons. This file proves that it is an **isomorphism** as soon as the
identifications `Ψ` are.

Invertibility is local on `Proj_{S'}(𝒜')`, which is covered by the charts of the base-change
cover; on the chart over a pair `W' ⊆ g⁻¹W` of affine opens the comparison is, up to the
identifications of the two sides with chart sheaves, the comparison
`Stacks.ProjModuleComparison.moduleMap` of the sheaves of Tag 01M6 across `Proj.map` of the base
change `𝒜(W) ⟶ 𝒜'(W')` of graded section rings. That is invertible by
`Stacks.AlgebraicGeometry.ModuleChartLocality.isIso_moduleMap_of_isIso_extension`, whose chart
hypothesis is `Stacks.AlgebraicGeometry.ModuleChartLocality.isIso_moduleDegreeZeroExtension`: both
the graded section ring and the graded module of sections base-change degreewise over the
degree-zero rings, by `Stacks.RelativeProj.Situation.isBaseChange_pieceMap_gradedBaseChange` and
`Stacks.RelativeProj.Situation.isBaseChange_modulePieceMap_sectionModuleBaseChange`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_restrictFunctor_map`: invertibility of a
  morphism of sheaves of modules is detected by its restrictions along a jointly surjective family
  of open immersions.
* `Stacks.RelativeProj.Situation.isIso_moduleChartBaseChangeHom`: the chart comparisons are
  isomorphisms.
* `Stacks.RelativeProj.Situation.isIso_moduleSheafBaseChangeHom`: **the base-change comparison
  `r^* ℳ̃ ⟶ ℳ̃'` is an isomorphism.**
* `Stacks.RelativeProj.Situation.moduleSheafPullbackIso` and
  `Stacks.RelativeProj.Situation.moduleSheafFibreProductIso`: **property (8) of Tag 01O7** for
  `𝒜' = g^* 𝒜` and `ℳ' = g^* ℳ`, read on `Proj_{S'}(𝒜')` and on `S' ×_S Proj_S(𝒜)`.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules Stacks.ProjModuleComparison

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **Invertibility of a morphism of sheaves of modules is local for a jointly surjective family
of open immersions.** -/
public theorem isIso_of_isIso_restrictFunctor_map {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) {I : Type*} {Y : I → Scheme.{u}} (j : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hcov : ∀ x : X, ∃ (i : I) (y : Y i), j i y = x)
    (h : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (j i)).map φ)) : IsIso φ := by
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk φ fun x ↦ ?_
  obtain ⟨i, y, rfl⟩ := hcov x
  have : IsIso ((Scheme.Modules.restrictFunctor (j i)).map φ) := h i
  have h3 : IsIso ((Scheme.Modules.restrictFunctor (j i) ⋙ Scheme.Modules.toPresheaf _ ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} y).map φ) :=
    Functor.map_isIso (Scheme.Modules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y) _
  have h2 : IsIso ((Scheme.Modules.restrictStalkNatIso (j i) y).hom.app M ≫
      (Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} (j i y)).map φ) := by
    rw [← (Scheme.Modules.restrictStalkNatIso (j i) y).hom.naturality φ]
    infer_instance
  have h2' : IsIso ((Scheme.Modules.restrictStalkNatIso (j i) y).hom.app M ≫
      (TopCat.Presheaf.stalkFunctor Ab.{u} (j i y)).map φ.mapPresheaf) := h2
  exact (isIso_comp_left_iff ((Scheme.Modules.restrictStalkNatIso (j i) y).hom.app M) _).mp h2'

end AlgebraicGeometry.Scheme.Modules

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition

namespace Stacks.RelativeProj.Situation

open Stacks.AlgebraicGeometry.ModuleHomGlue Stacks.AlgebraicGeometry.ModuleChartLocality

variable {s s' : Situation.{u}} (g : s'.base ⟶ s.base)
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback g s.algebra) s'.algebra)
  (hΦ : ∀ m : ℕ, IsIso (Φ.app (m : ℤ)))
  {ℳ : SheafOfModules.LeftGradedModule.{u, u, u} s.algebra}
  {ℳ' : SheafOfModules.LeftGradedModule.{u, u, u} s'.algebra}
  (Ψ : ∀ n : ℤ, (Scheme.Modules.pullback g).obj (ℳ.piece n) ⟶ ℳ'.piece n)
  (hΨ : ∀ (i : ℕ) (n : ℤ) (W : s.base.Opens) (W' : s'.base.Opens) (h : W' ≤ g ⁻¹ᵁ W)
    (a : s.sectionPieces W i) (x : sectionModulePieces ℳ W n),
    pieceSectionModuleHom g Ψ ((i : ℤ) + n) W W' h (ℳ.smul (i : ℤ) n (op W) a x)
      = ℳ'.smul (i : ℤ) n (op W') (pieceSectionHom g Φ i W W' h a)
          (pieceSectionModuleHom g Ψ n W W' h x))

variable [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] [∀ n : ℤ, (ℳ'.piece n).IsQuasicoherent]

omit [∀ n : ℤ, (ℳ'.piece n).IsQuasicoherent] in
include hΨ in
/-- **The chart comparisons of the base change of `ℳ̃` are isomorphisms**, once the degreewise
identification `Ψ` of `ℳ'` with the pullback of `ℳ` is. -/
public theorem isIso_moduleChartBaseChangeHom (hΨiso : ∀ n : ℤ, IsIso (Ψ n))
    (W : s.base.affineOpens) (W' : s'.base.affineOpens) (h : W'.1 ≤ g ⁻¹ᵁ W.1) :
    IsIso (moduleChartBaseChangeHom g Φ hΦ Ψ hΨ W W' h) := by
  let aCD : Algebra ↥(s.sectionRingGrading W.1 0) ↥(s'.sectionRingGrading W'.1 0) :=
    ((gradedBaseChange g Φ W.1 W'.1 h).gradedZeroRingHom).toAlgebra
  have halgCD : ∀ a : ↥(s.sectionRingGrading W.1 0),
      algebraMap ↥(s.sectionRingGrading W.1 0) ↥(s'.sectionRingGrading W'.1 0) a
        = (gradedBaseChange g Φ W.1 W'.1 h).gradedZeroRingHom a := fun _ => rfl
  have halgAB : ∀ r : ↥(s.sectionRingGrading W.1 0),
      ((algebraMap ↥(s.sectionRingGrading W.1 0) ↥(s'.sectionRingGrading W'.1 0) r :
          s'.sectionRing W'.1))
        = gradedBaseChange g Φ W.1 W'.1 h (r : s.sectionRing W.1) := fun _ => rfl
  exact isIso_moduleMap_of_isIso_extension (gradedBaseChange g Φ W.1 W'.1 h)
    (irrelevant_le_gradedBaseChange g Φ W W' h hΦ)
    (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W.1 W'.1 h)
    (sectionModuleBaseChange_mem_grading g Ψ W.1 W'.1 h)
    fun _ _ _ hb => isIso_moduleDegreeZeroExtension (gradedBaseChange g Φ W.1 W'.1 h)
      (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W.1 W'.1 h)
      (sectionModuleBaseChange_mem_grading g Ψ W.1 W'.1 h) halgAB hb
      (fun i => isBaseChange_modulePieceMap_sectionModuleBaseChange g Φ Ψ hΨ hΨiso i W.2 W'.2 h
        hΦ halgCD halgAB)
      (fun n => isBaseChange_pieceMap_gradedBaseChange g Φ n W.2 W'.2 h hΦ halgCD halgAB)

include hΨ in
/-- **The base-change comparison `r^* ℳ̃ ⟶ ℳ̃'` is an isomorphism**, once the degreewise
identification `Ψ` of `ℳ'` with the pullback of `ℳ` is. Invertibility is local, and on each chart
of the base-change cover the comparison is the chart comparison
`Stacks.RelativeProj.Situation.moduleChartBaseChangeHom` between identifications. -/
public theorem isIso_moduleSheafBaseChangeHom (hΨiso : ∀ n : ℤ, IsIso (Ψ n)) :
    IsIso (moduleSheafBaseChangeHom g Φ hΦ Ψ hΨ) := by
  refine Scheme.Modules.isIso_of_isIso_restrictFunctor_map _
    (fun p : (baseChangeCover g).I₀ => relativeProjChart s' p.1.1)
    (fun x => ⟨(baseChangeCover g).idx x, (baseChangeCover g).covers x⟩) fun p => ?_
  rw [restrictFunctor_map_moduleSheafBaseChangeHom]
  have := isIso_moduleChartBaseChangeHom g Φ hΦ Ψ hΨ hΨiso p.1.2 p.1.1 p.2
  unfold moduleSheafBaseChangeRestrictHom moduleSheafBaseChangeChartHom
  infer_instance

/-! ### Property (8): the pullback situation -/

section Pullback

variable (s : Situation.{u}) {S' : Scheme.{u}} (g : S' ⟶ s.base)
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u} s.algebra) [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]

/-- The base-change morphism `Proj_{S'}(g^* 𝒜) ⟶ Proj_S(𝒜)` of the relative projective spectra,
for the pullback `g^* 𝒜` of the graded algebra. -/
public abbrev pullbackRelativeProjMap : relativeProj (s.pullback g) ⟶ relativeProj s :=
  relativeProjBaseChange (s' := s.pullback g) g (pullbackUnitalHom s g)
    (isIso_pullbackUnitalHom_app s g)

/-- **Stacks Project, Tag 01O7, property (8).** **The formation of `ℳ̃` commutes with base
change.** For a morphism of schemes `g : S' ⟶ S`, put `𝒜' = g^* 𝒜` and `ℳ' = g^* ℳ`, and let
`r : Proj_{S'}(𝒜') ⟶ Proj_S(𝒜)` be the induced morphism of relative projective spectra. Then the
canonical comparison `r^* ℳ̃ ⟶ ℳ̃'` is an isomorphism.

The comparison is `Stacks.RelativeProj.Situation.moduleSheafBaseChangeHom`, the unique morphism
restricting on the chart of `Proj_{S'}(𝒜')` over each pair `W' ⊆ g⁻¹W` of affine opens to the
comparison of the sheaves of Tag 01M6 across the base change of the graded section rings
(`Stacks.RelativeProj.Situation.restrictFunctor_map_moduleSheafBaseChangeHom`); it is invertible by
`Stacks.RelativeProj.Situation.isIso_moduleSheafBaseChangeHom`. -/
@[stacks 01O7 "property (8): the canonical isomorphism r^* ℳ̃ ≅ (g^* ℳ)~ on the relative
projective spectrum of g^* 𝒜, for any morphism of schemes g : S' ⟶ S"]
public noncomputable def moduleSheafPullbackIso :
    (Scheme.Modules.pullback (pullbackRelativeProjMap s g)).obj (moduleSheaf ℳ) ≅
      moduleSheaf (s := s.pullback g) (Stacks.Conormal.leftGradedPullback g ℳ) :=
  haveI := isIso_moduleSheafBaseChangeHom (s' := s.pullback g) g (pullbackUnitalHom s g)
    (isIso_pullbackUnitalHom_app s g) (pullbackModuleIdHom g ℳ) (pullbackModuleIdHom_compat g ℳ)
    fun _ => inferInstanceAs (IsIso (𝟙 _))
  asIso (moduleSheafBaseChangeHom (s' := s.pullback g) g (pullbackUnitalHom s g)
    (isIso_pullbackUnitalHom_app s g) (pullbackModuleIdHom g ℳ) (pullbackModuleIdHom_compat g ℳ))

/-- The isomorphism of property (8) is the canonical comparison. -/
public theorem moduleSheafPullbackIso_hom :
    (moduleSheafPullbackIso s g ℳ).hom =
      moduleSheafBaseChangeHom (s' := s.pullback g) g (pullbackUnitalHom s g)
        (isIso_pullbackUnitalHom_app s g) (pullbackModuleIdHom g ℳ)
        (pullbackModuleIdHom_compat g ℳ) := rfl

/-- The canonical identification `Proj_{S'}(g^* 𝒜) ≅ S' ×_S Proj_S(𝒜)` of
`Stacks.RelativeProj.Situation.relativeProjBaseChangeIso`, for the pullback situation. -/
public abbrev pullbackRelativeProjIso :
    relativeProj (s.pullback g) ≅ Limits.pullback (relativeProjToBase s) g :=
  relativeProjBaseChangeIso (s' := s.pullback g) g (pullbackUnitalHom s g)
    (isIso_pullbackUnitalHom_app s g)

/-- The identification followed by the projection to `Proj_S(𝒜)` is the base-change morphism. -/
public theorem pullbackRelativeProjIso_hom_fst :
    (pullbackRelativeProjIso s g).hom ≫ Limits.pullback.fst (relativeProjToBase s) g =
      pullbackRelativeProjMap s g :=
  relativeProjBaseChangeIso_hom_fst (s' := s.pullback g) g (pullbackUnitalHom s g)
    (isIso_pullbackUnitalHom_app s g)

/-- The projection `S' ×_S Proj_S(𝒜) ⟶ Proj_S(𝒜)` is the inverse identification followed by the
base-change morphism. -/
public theorem pullback_fst_eq :
    Limits.pullback.fst (relativeProjToBase s) g =
      (pullbackRelativeProjIso s g).inv ≫ pullbackRelativeProjMap s g := by
  rw [← pullbackRelativeProjIso_hom_fst, Iso.inv_hom_id_assoc]

/-- **Stacks Project, Tag 01O7, property (8), on the fibre product.** For a morphism of schemes
`g : S' ⟶ S`, the pullback of `ℳ̃` along the projection `S' ×_S Proj_S(𝒜) ⟶ Proj_S(𝒜)` is
canonically isomorphic to the sheaf `(g^* ℳ)~`, transported to the fibre product along the
canonical identification `e : Proj_{S'}(g^* 𝒜) ≅ S' ×_S Proj_S(𝒜)` of
`Stacks.RelativeProj.Situation.relativeProjBaseChangeIso`.

It is `Stacks.RelativeProj.Situation.moduleSheafPullbackIso` read through `e`: the projection is
`e⁻¹` followed by the base-change morphism `r`, so its inverse image is `e⁻¹`'s of `r^* ℳ̃`. -/
@[stacks 01O7 "property (8) on the fibre product: the canonical isomorphism between the pullback
of ℳ̃ along S' ×_S Proj_S(𝒜) ⟶ Proj_S(𝒜) and (g^* ℳ)~ carried to S' ×_S Proj_S(𝒜)"]
public noncomputable def moduleSheafFibreProductIso :
    (Scheme.Modules.pullback (Limits.pullback.fst (relativeProjToBase s) g)).obj (moduleSheaf ℳ) ≅
      (Scheme.Modules.pullback (pullbackRelativeProjIso s g).inv).obj
        (moduleSheaf (s := s.pullback g) (Stacks.Conormal.leftGradedPullback g ℳ)) :=
  (Scheme.Modules.pullbackCongr (pullback_fst_eq s g)).app _ ≪≫
    ((Scheme.Modules.pullbackComp (pullbackRelativeProjIso s g).inv
      (pullbackRelativeProjMap s g)).app _).symm ≪≫
    (Scheme.Modules.pullback (pullbackRelativeProjIso s g).inv).mapIso
      (moduleSheafPullbackIso s g ℳ)

end Pullback

end Stacks.RelativeProj.Situation

end
