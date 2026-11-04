module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentIdealMeet
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.CoequalizerGlueingTowerKernel

/-!
# `𝒜_n` injects into `f_* 𝒪_{X'} × 𝒪_{Z_n}`

In the situation of Stacks 0AGH let `π : Y_n = X' ⨿ Z_n ⟶ X_n` be a coequalizer of the kernel
pair of `Y_n ⟶ X` and `𝒜_n = (X_n ⟶ X)_* 𝒪`. The source's description of `𝒜_n` as an equalizer
inside `f_* 𝒪_{X'} × 𝒪_X/𝓘ⁿ` rests on its construction of `X_n`; through the universal property
alone what is available, and what the last paragraph of the proof of Stacks 0AGK uses, is that
the two restriction maps `𝒜_n ⟶ f_* 𝒪_{X'}` and `𝒜_n ⟶ 𝒪_{Z_n}` are jointly injective.

## The argument

On `X_n` let `𝒦₁, 𝒦₂` be the kernels of `𝒪_{X_n} ⟶ (X' ⟶ X_n)_* 𝒪` and `𝒪_{X_n} ⟶ (Z_n ⟶ X_n)_* 𝒪`.
Both are quasi-coherent (the two morphisms are proper over `X_n`, by Stacks 04NX, the morphism
`X_n ⟶ X` being separated), so `𝒦₁ ∩ 𝒦₂` cuts out a closed subspace `W ⊆ X_n` (Stacks 03MB). Both
summands of `Y_n` factor through `W`, hence so does `π`; but `π` is scheme-theoretically dominant
(`AlgebraicGeometry.Space.KernelPairCoequalizer.schemeTheoreticImageSubfunctor_π_eq_top`), so its
kernel ideal vanishes (Stacks 082Z) and with it `𝒦₁ ∩ 𝒦₂`. Since `X_n ⟶ X` is representable, the
sections of `𝒜_n` over an étale chart `V` of `X` are the regular functions on the chart
`X_n ×_X V` of `X_n` (Stacks 03G8), compatibly with the two restriction maps.

## Main results

Names are relative to the namespace `AlgebraicGeometry.Space`.

* `CoequalizerGlueSituation.ClosedSubspaceSystem.kernelIdealSheaf_inl_inf_inr_eq_bot`:
  `𝒦₁ ∩ 𝒦₂ = 0`.
* `CoequalizerGlueSituation.ClosedSubspaceSystem.eq_zero_of_restrictions_eq_zero`: a section of
  `𝒜_n` killed by both restriction maps is zero.

## References

* [Stacks Project, Tag 0AGK](https://stacks.math.columbia.edu/tag/0AGK)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Chart values of direct-image maps along a representable morphism -/

/-- A section killed by a composite `f ≫ g ≫ k` whose last two factors are isomorphisms is
killed by `f`. -/
theorem app_eq_zero_of_comp_comp_app_eq_zero {Y : AlgebraicSpaces B S hS}
    {A C D E : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}} (f : A ⟶ C) (g : C ⟶ D)
    (k : D ⟶ E) (V : (SmallEtale B S hS Y.1)ᵒᵖ) (x : A.obj.obj V)
    (h : (f ≫ g ≫ k).hom.app V x = 0) (hg : IsIso g) (hk : IsIso k) : f.hom.app V x = 0 := by
  have h' : k.hom.app V (g.hom.app V (f.hom.app V x)) = 0 := h
  refine (ConcreteCategory.bijective_of_isIso (g.hom.app V)).1 ?_
  refine ((ConcreteCategory.bijective_of_isIso (k.hom.app V)).1 ?_).trans (map_zero _).symm
  exact h'.trans (map_zero _).symm

/-- A section killed by `f ≫ eqToHom e` is killed by `f`. -/
theorem app_eq_zero_of_comp_eqToHom_app_eq_zero {Y : AlgebraicSpaces B S hS}
    {A C D : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}} (f : A ⟶ C) (e : C = D)
    (V : (SmallEtale B S hS Y.1)ᵒᵖ) (x : A.obj.obj V)
    (h : (f ≫ eqToHom e).hom.app V x = 0) : f.hom.app V x = 0 := by
  subst e
  simpa using h

/-- **The chart value of `h♯ : Z_* 𝒪 ⟶ Y_* 𝒪` along a representable `Z ⟶ X`.** If the map induced
on direct images by `h : Y ⟶ Z` over `X` kills a section `b` of `Z_* 𝒪` over a chart `V`, then the
structure map of `h` kills the regular function on the chart `Z ×_X V` of `Z` corresponding to
`b` (Stacks 03G8). -/
theorem structureSharpCommRing_app_eq_zero_of_pushforwardRingMap_app_eq_zero
    {X : AlgebraicSpaces B S hS} {Y Z : Over X} (h : Y ⟶ Z)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1)
    (b : (pushforwardAlgebra B S hS Z).right.obj.obj (op V))
    (hb : (pushforwardRingMap B S hS h).hom.app (op V) b = 0) :
    letI := (smallBaseChange_isMorphismOfSites B S hS Z.hom hZ).toIsContinuous
    (((smallBaseChange B S hS Z.hom hZ).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.left.1)).map
          (smallEtaleRingedToposHom B S hS h.left).fSharp).hom.app (op V)
      (((smallEtaleRingedToposHom_representableRing B S hS Z.hom hZ).hom.app
        (smallEtaleRingedTopos B S hS Z.left).O).hom.app (op V) b) = 0 := by
  let := (smallBaseChange_isMorphismOfSites B S hS Z.hom hZ).toIsContinuous
  rw [pushforwardRingMap_eq, pushforwardAlgMap] at hb
  have h1 := app_eq_zero_of_comp_comp_app_eq_zero _ _ _ (op V) b
    (app_eq_zero_of_comp_eqToHom_app_eq_zero _ _ (op V) b hb) inferInstance
    (((smallEtaleRingedToposHom_compRingIso B S hS h.left Z.hom).app
      (smallEtaleRingedTopos B S hS Y.left).O).isIso_hom)
  have hnat := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op V))
    ((smallEtaleRingedToposHom_representableRing B S hS Z.hom hZ).hom.naturality
      (smallEtaleRingedToposHom B S hS h.left).fSharp)) b
  have e2 := congrArg (fun y => ((smallEtaleRingedToposHom_representableRing B S hS Z.hom
    hZ).hom.app _).hom.app (op V) y) h1
  rw [map_zero] at e2
  exact hnat.symm.trans e2

namespace CoequalizerGlueSituation

namespace ClosedSubspaceSystem

variable {T : CoequalizerGlueSituation.{u}} (N : T.ClosedSubspaceSystem)
  (D : ∀ n, KernelPairCoequalizer T.B T.S T.hS (N.glueMapAt n))
  (hAGG : ProperKernelPairCoequalizers T.B T.S T.hS)

include hAGG in
/-- A morphism to `X_n` from an algebraic space proper over `X`, compatible with the morphisms
to `X`, is quasi-compact: `X_n ⟶ X` is separated, being finite (Stacks 04NX). -/
theorem isQuasiCompact_of_comp_toTarget (n : ℕ) {A : AlgebraicSpaces T.B T.S T.hS}
    (q : A ⟶ (D n).space) (hq : IsProper T.B T.S T.hS (q ≫ (D n).toTarget).hom) :
    IsQuasiCompact T.B T.S T.hS q.hom :=
  (isProper_of_comp_of_isSeparated T.B T.S T.hS A.property (D n).space.property T.hX q.hom
    (D n).toTarget.hom hq (isSeparated_of_isFinite T.B T.S T.hS _ (D n).space.property T.hX
      (hAGG.isFinite_toTarget _ T.locallyNoetherian (N.isProper_glueMapAt n) (D n)))).2.1.2

/-- The defining ideal of a closed subspace which is everything is zero. -/
theorem _root_.AlgebraicGeometry.Space.definingIdealSheaf_obj_eq_bot_of_eq_top
    {Y : AlgebraicSpaces B S hS} (W : ClosedSubspaces B S hS Y.1) (hW : W.1 = ⊤)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ) : (definingIdealSheaf B S hS Y W).obj U = ⊥ := by
  let ι : (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS) ⟶ Y := ObjectProperty.homMk W.1.ι
  have : IsIso ((ObjectProperty.ι _).map ι) := (Subfunctor.eq_top_iff_isIso _).1 hW
  have : IsIso ι := isIso_of_reflects_iso ι (ObjectProperty.ι _)
  exact kernelIdealSheaf_obj_eq_bot_of_isIso ι U

include hAGG in
/-- **The two summands of `Y_n` detect sections of `𝒪_{X_n}`**: the kernels of
`𝒪_{X_n} ⟶ (X' ⟶ X_n)_* 𝒪` and `𝒪_{X_n} ⟶ (Z_n ⟶ X_n)_* 𝒪` meet in zero. -/
theorem kernelIdealSheaf_inl_inf_inr_eq_bot (n : ℕ) :
    kernelIdealSheaf T.B T.S T.hS (coprod.inl ≫ (D n).π) ⊓
      kernelIdealSheaf T.B T.S T.hS (coprod.inr ≫ (D n).π) = ⊥ := by
  have hq1 := N.isQuasiCompact_of_comp_toTarget D hAGG n (coprod.inl ≫ (D n).π) (by
    rw [Category.assoc, (D n).fac, glueMapAt, coprod.inl_desc]
    exact T.hf)
  have hq2 := N.isQuasiCompact_of_comp_toTarget D hAGG n (coprod.inr ≫ (D n).π) (by
    rw [Category.assoc, (D n).fac, glueMapAt, coprod.inr_desc]
    exact isProper_of_isClosedImmersion T.B T.S T.hS (N.space n).property T.hX _
      (N.isClosedImmersion_toTarget n))
  obtain ⟨W, hW⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite T.B T.S T.hS
    (D n).space _ (isQuasicoherentOnSite_idealInf T.B T.S T.hS (D n).space _ _
      (isQuasicoherentOnSite_kernelIdealSheaf T.B T.S T.hS _ hq1)
      (isQuasicoherentOnSite_kernelIdealSheaf T.B T.S T.hS _ hq2))
  obtain ⟨g1, hg1⟩ := (exists_comp_eq_iff_definingIdealSheaf_le_kernelIdealSheaf T.B T.S T.hS
    (X := (D n).space) W (coprod.inl ≫ (D n).π)).2 (hW ▸ inf_le_left)
  obtain ⟨g2, hg2⟩ := (exists_comp_eq_iff_definingIdealSheaf_le_kernelIdealSheaf T.B T.S T.hS
    (X := (D n).space) W (coprod.inr ≫ (D n).π)).2 (hW ▸ inf_le_right)
  have hπ : coprod.desc g1 g2 ≫ ObjectProperty.homMk W.1.ι = (D n).π := by
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_desc_assoc, hg1]
    · rw [coprod.inr_desc_assoc, hg2]
  have hle : definingIdealSheaf T.B T.S T.hS (D n).space W ≤
      kernelIdealSheaf T.B T.S T.hS (D n).π :=
    (exists_comp_eq_iff_definingIdealSheaf_le_kernelIdealSheaf T.B T.S T.hS (X := (D n).space)
      W (D n).π).1 ⟨_, hπ⟩
  have hker := kernelIdealSheaf_le_definingIdealSheaf_schemeTheoreticImage T.B T.S T.hS (D n).π
    (hAGG.isProper_π _ T.locallyNoetherian (N.isProper_glueMapAt n) (D n)).2.1.2
  rw [← hW]
  refine le_bot_iff.1 fun U r hr => ?_
  rw [SheafOfModules.Submodule.bot_obj]
  have := hker U (hle U hr)
  rwa [definingIdealSheaf_obj_eq_bot_of_eq_top _ (D n).schemeTheoreticImageSubfunctor_π_eq_top]
    at this

include hAGG in
/-- **`𝒜_n ⟶ f_* 𝒪_{X'} × 𝒪_{Z_n}` is injective**: a section of `𝒜_n` over an étale chart of `X`
killed by both restriction maps is zero. -/
theorem eq_zero_of_restrictions_eq_zero (n : ℕ) (V : SmallEtale T.B T.S T.hS T.X)
    (b : (pushforwardAlgebra T.B T.S T.hS (N.stageOver D n)).right.obj.obj (op V))
    (h1 : (pushforwardRingMap T.B T.S T.hS (N.modificationToStage D n)).hom.app (op V) b = 0)
    (h2 : (pushforwardRingMap T.B T.S T.hS (N.memberToStage D n)).hom.app (op V) b = 0) :
    b = 0 := by
  have hrep : yoneda.relativelyRepresentable (N.stageOver D n).hom.hom :=
    relativelyRepresentable_of_isAffineHom T.B T.S T.hS _ (IsFinite.isAffineHom
      (hAGG.isFinite_toTarget _ T.locallyNoetherian (N.isProper_glueMapAt n) (D n)))
  let := (smallBaseChange_isMorphismOfSites T.B T.S T.hS (N.stageOver D n).hom hrep).toIsContinuous
  let α := (smallEtaleRingedToposHom_representableRing T.B T.S T.hS (N.stageOver D n).hom
    hrep).hom.app (smallEtaleRingedTopos T.B T.S T.hS (D n).space).O
  have c1 := structureSharpCommRing_app_eq_zero_of_pushforwardRingMap_app_eq_zero
    (N.modificationToStage D n) hrep V b h1
  have c2 := structureSharpCommRing_app_eq_zero_of_pushforwardRingMap_app_eq_zero
    (N.memberToStage D n) hrep V b h2
  let V' := (smallBaseChange T.B T.S T.hS (N.stageOver D n).hom hrep).obj V
  let x : (SheafOfModules.unit (structureRingSheaf T.B T.S T.hS (D n).space)).val.obj (op V') :=
    α.hom.app (op V) b
  have hmem : x ∈ (kernelIdealSheaf T.B T.S T.hS (coprod.inl ≫ (D n).π) ⊓
      kernelIdealSheaf T.B T.S T.hS (coprod.inr ≫ (D n).π)).obj (op V') :=
    ⟨(structureSharp_app_eq_structureSharpCommRing_app _ _ _).trans c1,
      (structureSharp_app_eq_structureSharpCommRing_app _ _ _).trans c2⟩
  rw [N.kernelIdealSheaf_inl_inf_inr_eq_bot D hAGG n, SheafOfModules.Submodule.bot_obj,
    Submodule.mem_bot] at hmem
  exact (ConcreteCategory.bijective_of_isIso (α.hom.app (op V))).1
    (hmem.trans (map_zero _).symm)

end ClosedSubspaceSystem

end CoequalizerGlueSituation

end AlgebraicGeometry.Space

end
