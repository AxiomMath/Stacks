module

public import Mathlib.FieldTheory.KrullTopology
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.QuasiCompactOpen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.EtaleNeighbourhoodLimitSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapTwistUnitSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldBaseChangeGlobalSectionsGaloisAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.Basic

/-!
# `Γ(Y_K, F|_{Y_K})` as a discrete Galois module

Let `k` be a field, `K/k` a separable algebraic extension, `Y` a quasi-compact and
quasi-separated scheme over `k` and `G` a sheaf of `Λ`-modules on `Y_étale`. A `k`-automorphism
`σ` of `K` acts on `Γ(Y_K, G|_{Y_K})` through `id_Y × Spec σ`
(`Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsGaloisAction`, the degree-zero case of the
action on `RΓ(Y_K, -)` used for Remark 03UI (2)). This file proves that this is a continuous
action of `Aut_k(K)` with its Krull topology on the discrete module, and packages
`F ↦ Γ(Y_K, F|_{Y_K})` as a functor to discrete `Λ[Aut_k(K)]`-modules.

The input is Stacks 09YQ in degree zero: `Y_K` is the limit of the base changes `Y_E` to the
finite subextensions `E ⊆ K`, which are étale over `Y`, so every global section of `G|_{Y_K}` is
the pull back of a section of `G` over some `Y_E`
(`Stacks.EtaleCohomology.exists_fieldStageSection_eq`). The action of `σ` on such a section is
restriction along the projection `Y_K ⟶ Y_E` precomposed with `id_Y × Spec σ`
(`Stacks.EtaleCohomology.ΓRes_selfMapTwistAction_of_moduleUnitSection`), which gives at once the
group laws and that the section is fixed by the open subgroup `Gal(K/E)`.

## Main definitions

* `Stacks.EtaleCohomology.fieldStageSystem`, `Stacks.EtaleCohomology.fieldStageCone`,
  `Stacks.EtaleCohomology.fieldStageConeIsLimit` — `Y_K` as the limit of the étale `Y`-schemes
  `Y_E`.
* `Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsRepresentation` — the representation of
  `Aut_k(K)` on `Γ(Y_K, G|_{Y_K})`.
* `Stacks.EtaleCohomology.GaloisModules` — discrete `Λ[Aut_k(K)]`-modules.
* `Stacks.EtaleCohomology.galoisGlobalSections` — the functor `Γ^Gal : F ↦ Γ(Y_K, F|_{Y_K})`.

## Main results

* `Stacks.EtaleCohomology.exists_fieldStageSection_eq` — global sections come from finite stages.
* `Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsGaloisAction_one`,
  `Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsGaloisAction_mul` — the group laws.
* `Stacks.EtaleCohomology.isOpen_stabilizer_fieldBaseChangeGlobalSectionsGaloisAction` —
  continuity.
* `Stacks.EtaleCohomology.galoisGlobalSections_comp_underlying` — forgetting the action gives
  `Γ(Y_K, -|_{Y_K})` on the nose.

## Implementation notes

The action is the base's `fieldBaseChangeGlobalSectionsGaloisAction`, built from the self-map twist
of `id_Y × Spec σ`, so that the derived version is comparable with
`Stacks.EtaleCohomology.galoisCompactSupportAction`. The existence-only comparison
`AlgebraicGeometry.representationSheafPullbackIso` is not used.

The hypotheses are those under which the action is continuous: for `Y` an infinite disjoint union
of copies of `Spec k` the stabilizers need not be open (see the implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/GaloisModuleHigherDirectImageStalk.lean`), and
for `K/k` inseparable the stages `Y_E` need not be étale over `Y`.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI)
* [Stacks Project, Tag 04JP](https://stacks.math.columbia.edu/tag/04JP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Frobenius

universe u v

namespace Stacks.EtaleCohomology

/-! ### The finite stages `Y_E` of `Y_K` -/

section Stages

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k))) (K : Type u)
  [Field K] [Algebra k K]

/-- The finite subextension `k` itself is the least finite subextension. -/
@[instance_reducible]
def fextOrderBot : OrderBot (FExt k K) where
  bot := ⟨⊥, inferInstance⟩
  bot_le E := (bot_le : (⊥ : IntermediateField k K) ≤ E.1)

attribute [local instance] fextOrderBot

/-- A finite subextension of a separable extension is étale over the base field. -/
theorem etale_spectrumMap_fext [Algebra.IsSeparable k K] (E : FExt k K) :
    Etale (spectrumMap k E.1) := by
  have : FiniteDimensional k E.1 := E.2
  have : Module.FinitePresentation k E.1 := Module.finitePresentation_of_finite k E.1
  have : Algebra.FinitePresentation k E.1 := Algebra.FinitePresentation.of_finitePresentation k E.1
  let h : Algebra.Etale k E.1 :=
    { formallyEtale := (Algebra.FormallyEtale.iff_isSeparable k E.1).mpr inferInstance
      finitePresentation := inferInstance }
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr h)


/-- The transition morphism `Y_{E'} ⟶ Y_E` for finite subextensions `E ⊆ E'`. -/
def fieldStageMap {i j : (FExt k K)ᵒᵖ} (g : i ⟶ j) :
    pullback (spectrumMap k i.unop.1) Y.hom ⟶ pullback (spectrumMap k j.unop.1) Y.hom :=
  pullback.lift (pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom
      (IntermediateField.inclusion (leOfHom g.unop)).toRingHom)) (pullback.snd _ _) (by
    rw [Category.assoc, ← Spec.map_comp, ← pullback.condition]
    rfl)

/-- The transition morphism `Y_{E'} ⟶ Y_E` composed with the first projection is the first
projection followed by `Spec E' ⟶ Spec E`. -/
@[reassoc (attr := simp)]
theorem fieldStageMap_fst {i j : (FExt k K)ᵒᵖ} (g : i ⟶ j) :
    fieldStageMap Y K g ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom
      (IntermediateField.inclusion (leOfHom g.unop)).toRingHom) :=
  pullback.lift_fst _ _ _

/-- The transition morphism `Y_{E'} ⟶ Y_E` commutes with the projections to `Y`. -/
@[reassoc (attr := simp)]
theorem fieldStageMap_snd {i j : (FExt k K)ᵒᵖ} (g : i ⟶ j) :
    fieldStageMap Y K g ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The transition morphism for the identity of `E` is the identity of `Y_E`. -/
theorem fieldStageMap_id (i : (FExt k K)ᵒᵖ) : fieldStageMap Y K (𝟙 i) = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · rw [fieldStageMap_fst, Category.id_comp]
    have h : CommRingCat.ofHom (IntermediateField.inclusion (leOfHom (𝟙 i).unop)).toRingHom =
        𝟙 (CommRingCat.of i.unop.1) := by
      ext x
      rfl
    rw [h, Spec.map_id, Category.comp_id]
  · rw [fieldStageMap_snd, Category.id_comp]

/-- The transition morphisms are compatible with composition of inclusions
`E ⊆ E' ⊆ E''`. -/
theorem fieldStageMap_comp {i j l : (FExt k K)ᵒᵖ} (f : i ⟶ j) (g : j ⟶ l) :
    fieldStageMap Y K (f ≫ g) = fieldStageMap Y K f ≫ fieldStageMap Y K g := by
  refine pullback.hom_ext ?_ ?_
  · rw [fieldStageMap_fst, Category.assoc, fieldStageMap_fst, fieldStageMap_fst_assoc,
      ← Spec.map_comp]
    rfl
  · rw [fieldStageMap_snd, Category.assoc, fieldStageMap_snd, fieldStageMap_snd]

/-- `Spec K ⟶ Spec E ⟶ Spec k` is `Spec K ⟶ Spec k`. -/
theorem spectrumMap_fext_comp (E : FExt k K) :
    Spec.map (CommRingCat.ofHom (algebraMap E.1 K)) ≫ spectrumMap k E.1 = spectrumMap k K := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- The projection `Y_K ⟶ Y_E` to a finite stage. -/
def fieldStageProj (i : (FExt k K)ᵒᵖ) :
    fieldBaseChange Y K ⟶ pullback (spectrumMap k i.unop.1) Y.hom :=
  pullback.lift (pullback.snd Y.hom (spectrumMap k K) ≫
      Spec.map (CommRingCat.ofHom (algebraMap i.unop.1 K)))
    (pullback.fst Y.hom (spectrumMap k K)) (by
      rw [Category.assoc, spectrumMap_fext_comp]
      exact pullback.condition.symm)

/-- The projection `Y_K ⟶ Y_E` composed with the first projection is the projection to
`Spec K` followed by `Spec K ⟶ Spec E`. -/
@[reassoc (attr := simp)]
theorem fieldStageProj_fst (i : (FExt k K)ᵒᵖ) :
    fieldStageProj Y K i ≫ pullback.fst _ _ = pullback.snd Y.hom (spectrumMap k K) ≫
      Spec.map (CommRingCat.ofHom (algebraMap i.unop.1 K)) :=
  pullback.lift_fst _ _ _

/-- The projection `Y_K ⟶ Y_E` commutes with the projections to `Y`. -/
@[reassoc (attr := simp)]
theorem fieldStageProj_snd (i : (FExt k K)ᵒᵖ) :
    fieldStageProj Y K i ≫ pullback.snd _ _ = pullback.fst Y.hom (spectrumMap k K) :=
  pullback.lift_snd _ _ _

variable [Algebra.IsSeparable k K]

attribute [local instance] etale_spectrumMap_fext

/-- **The finite stages of `Y_K`**: the base changes `Y_E = Spec E ×_k Y` to the finite
subextensions `E ⊆ K`, as étale `Y`-schemes. -/
def fieldStageSystem : (FExt k K)ᵒᵖ ⥤ Y.left.Etale where
  obj i := Scheme.Etale.mk (pullback.snd (spectrumMap k i.unop.1) Y.hom)
  map g := MorphismProperty.Over.homMk (fieldStageMap Y K g) (fieldStageMap_snd Y K g) trivial
  map_id i := MorphismProperty.Over.Hom.ext (fieldStageMap_id Y K i)
  map_comp f g := MorphismProperty.Over.Hom.ext (fieldStageMap_comp Y K f g)

/-- **`Y_K` as a cone over its finite stages.** -/
def fieldStageCone :
    Cone (fieldStageSystem Y K ⋙ Scheme.Etale.forget Y.left ⋙ Over.forget Y.left) where
  pt := fieldBaseChange Y K
  π :=
    { app := fieldStageProj Y K
      naturality := fun i j g => by
        refine (Category.id_comp _).trans (pullback.hom_ext ?_ ?_)
        · change _ = fieldStageProj Y K i ≫ fieldStageMap Y K g ≫ pullback.fst _ _
          rw [fieldStageMap_fst, fieldStageProj_fst_assoc, fieldStageProj_fst, ← Spec.map_comp]
          rfl
        · change _ = fieldStageProj Y K i ≫ fieldStageMap Y K g ≫ pullback.snd _ _
          rw [fieldStageMap_snd, fieldStageProj_snd, fieldStageProj_snd] }

/-- The diagram of finite stages is the diagram `fextPullbackDiagram` of base changes. -/
def fextPullbackDiagramIso :
    fextPullbackDiagram (K := K) Y.left Y.hom ≅
      fieldStageSystem Y K ⋙ Scheme.Etale.forget Y.left ⋙ Over.forget Y.left :=
  NatIso.ofComponents (fun i => Iso.refl _) (fun {i j} g => by
    refine (Category.comp_id _).trans ((pullback.hom_ext ?_ ?_).trans (Category.id_comp _).symm)
    · change ((Over.pullback Y.hom).map ((fextOverDiagram (K := K)).map g)).left ≫ _ =
        fieldStageMap Y K g ≫ pullback.fst _ _
      rw [fieldStageMap_fst]
      simp only [Over.pullback_map_left]
      exact pullback.lift_fst _ _ _
    · change ((Over.pullback Y.hom).map ((fextOverDiagram (K := K)).map g)).left ≫ _ =
        fieldStageMap Y K g ≫ pullback.snd _ _
      rw [fieldStageMap_snd]
      simp only [Over.pullback_map_left]
      exact pullback.lift_snd _ _ _)

/-- **`Y_K` is the limit of its finite stages.** -/
def fieldStageConeIsLimit : IsLimit (fieldStageCone Y K) :=
  IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv (fextPullbackDiagramIso Y K) _).symm
      (fextPullbackConeIsLimit (K := K) Y.left Y.hom))
    (Cone.ext (pullbackSymmetry Y.hom (spectrumMap k K)).symm (fun i => by
      refine pullback.hom_ext ?_ ?_
      · change (((Over.pullback Y.hom).map ((fextOverCone (K := K)).π.app i)).left ≫ 𝟙 _) ≫ _ =
          ((pullbackSymmetry Y.hom (spectrumMap k K)).inv ≫ fieldStageProj Y K i) ≫ _
        rw [Category.assoc, fieldStageProj_fst, pullbackSymmetry_inv_comp_snd_assoc,
          Category.comp_id]
        simp only [Over.pullback_map_left]
        exact pullback.lift_fst _ _ _
      · change (((Over.pullback Y.hom).map ((fextOverCone (K := K)).π.app i)).left ≫ 𝟙 _) ≫ _ =
          ((pullbackSymmetry Y.hom (spectrumMap k K)).inv ≫ fieldStageProj Y K i) ≫ _
        rw [Category.assoc, fieldStageProj_snd, pullbackSymmetry_inv_comp_fst, Category.comp_id]
        simp only [Over.pullback_map_left]
        exact pullback.lift_snd _ _ _))

/-- The projection of `Y_K` to a finite stage lies over `Y`. -/
theorem fieldStageCone_π_comp_hom (i : (FExt k K)ᵒᵖ) :
    (fieldStageCone Y K).π.app i ≫ ((fieldStageSystem Y K).obj i).hom =
      fieldBaseChangeProj Y K :=
  fieldStageProj_snd Y K i

omit [Algebra.IsSeparable k K] in
/-- The projection of `Y_K` to the stage `Y_E` is invariant under `id_Y × Spec σ` for every `σ`
fixing `E` pointwise. -/
theorem galoisBaseChange_comp_fieldStageProj (i : (FExt k K)ᵒᵖ) (σ : K ≃ₐ[k] K)
    (hσ : σ ∈ i.unop.1.fixingSubgroup) :
    galoisBaseChange Y K σ ≫ fieldStageProj Y K i = fieldStageProj Y K i := by
  have hfix : Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap i.unop.1 K)) =
        Spec.map (CommRingCat.ofHom (algebraMap i.unop.1 K)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact (IntermediateField.mem_fixingSubgroup_iff _ σ).1 hσ x.1 x.2
  apply pullback.hom_ext
  · rw [Category.assoc, fieldStageProj_fst, galoisBaseChange_comp_snd_assoc, hfix]
  · rw [Category.assoc, fieldStageProj_snd, galoisBaseChange_comp_fst]

/-- The transition morphisms of the finite stages are those of `fextPullbackDiagram`. -/
theorem fextPullbackDiagram_map_eq {i j : (FExt k K)ᵒᵖ} (g : i ⟶ j) :
    (fextPullbackDiagram (K := K) Y.left Y.hom).map g = fieldStageMap Y K g :=
  (Category.comp_id _).symm.trans (((fextPullbackDiagramIso Y K).hom.naturality g).trans
    (Category.id_comp _))

/-- The transition morphisms of the finite stages are affine. -/
instance isAffineHom_fieldStageMap {i j : (FExt k K)ᵒᵖ} (g : i ⟶ j) :
    IsAffineHom (fieldStageMap Y K g) := by
  have h := fextPullbackTransition_isAffineHom (K := K) Y.left Y.hom g
  rwa [fextPullbackDiagram_map_eq] at h

omit [Algebra.IsSeparable k K] in
/-- The finite subextensions are directed. -/
theorem fextIsDirected : IsDirected (FExt k K) (· ≤ ·) where
  directed a b := by
    have := a.2
    have := b.2
    exact ⟨⟨a.1 ⊔ b.1, IntermediateField.finiteDimensional_sup a.1 b.1⟩,
      (le_sup_left : a.1 ≤ a.1 ⊔ b.1), (le_sup_right : b.1 ≤ a.1 ⊔ b.1)⟩

attribute [local instance] fextIsDirected

/-- The stages of a quasi-compact `k`-scheme are quasi-compact. -/
theorem compactSpace_fieldStage [QuasiCompact Y.hom] (E : FExt k K) :
    CompactSpace ((fieldStageSystem Y K).obj (op E)).left := by
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsAffineHom (spectrumMap k E.1) := isAffineHom_of_isAffine _
  exact (inferInstance : CompactSpace (pullback (spectrumMap k E.1) Y.hom : Scheme.{u}))

/-- The stages of a quasi-separated `k`-scheme are quasi-separated. -/
theorem quasiSeparatedSpace_fieldStage [QuasiSeparated Y.hom] (E : FExt k K) :
    QuasiSeparatedSpace ((fieldStageSystem Y K).obj (op E)).left := by
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have : IsAffineHom (spectrumMap k E.1) := isAffineHom_of_isAffine _
  have h : QuasiSeparated (pullback.fst (spectrumMap k E.1) Y.hom) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated)
      (IsPullback.of_hasPullback (spectrumMap k E.1) Y.hom).flip ‹QuasiSeparated Y.hom›
  exact @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.fst (spectrumMap k E.1) Y.hom)
    inferInstance h

/-- Equal morphisms of types agree on every element. -/
theorem type_hom_congr {X Y : Type v} {f g : X ⟶ Y} (h : f = g) (x : X) : f x = g x := by
  rw [h]

/-- The section of `G|_{Y_K}` over `Y_K` pulled back from a section of `G` over the stage
`Y_E`: the pulled back section `u(a)` over `Y_E ×_Y Y_K`, restricted along the projection
`Y_K ⟶ Y_E`. -/
abbrev fieldStageSection (G : EtaleModules.{u, 0} Λ Y.left) (i : FExt k K)
    (a : G.obj.obj (op ((fieldStageSystem Y K).obj (op i)))) :
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).obj.obj
      (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) :=
  ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).obj.map
    (smallEtaleBaseChangeLift (fieldBaseChangeProj Y K) ((fieldStageSystem Y K).obj (op i))
      (fieldStageProj Y K (op i)) (fieldStageCone_π_comp_hom Y K (op i))).op
    (moduleUnitSection Λ (fieldBaseChangeProj Y K) G a)

/-- **Every global section of `G|_{Y_K}` comes from a finite stage** (Stacks 09YQ in degree
zero): for `Y` quasi-compact and quasi-separated over `k` and `K/k` separable algebraic, every
global section of the inverse image of `G` to `Y_K` is, over the final object, the section
pulled back from a section of `G` over some `Y_E`, `E ⊆ K` a finite subextension. -/
theorem exists_fieldStageSection_eq [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    (G : EtaleModules.{u, 0} Λ Y.left)
    (z : (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G)) :
    ∃ (i : FExt k K) (a : G.obj.obj (op ((fieldStageSystem Y K).obj (op i)))),
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).ΓRes
          (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) z =
        fieldStageSection Λ Y K G i a := by
  have : CompactSpace ((fieldStageSystem Y K).obj (op ⊥)).left :=
    compactSpace_fieldStage Y K (⊥ : FExt k K)
  have : QuasiSeparatedSpace ((fieldStageSystem Y K).obj (op ⊥)).left :=
    quasiSeparatedSpace_fieldStage Y K (⊥ : FExt k K)
  have : ∀ {i j : (FExt k K)ᵒᵖ} (a : i ⟶ j), IsAffineHom ((fieldStageSystem Y K).map a).left :=
    fun a => isAffineHom_fieldStageMap Y K a
  let p := fieldBaseChangeProj Y K
  let H := (etaleModuleInverseImage.{u, 0} Λ p).obj G
  let Gs := (etaleModuleUnderlyingSets Λ Y.left).obj G
  let eF := etaleModuleInverseImageForgetIso Λ p G
  let eU := Adjunction.leftAdjointUniq (smallEtaleInverseImageAdjunction.{u, 0} p)
    (etaleTypeInverseImageAdj p)
  let T0 := op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))
  let s₀ : ((etaleModuleUnderlyingSets Λ _).obj H).obj.obj T0 := H.ΓRes T0 z
  let s₂ := (eU.inv.app Gs).hom.app T0 (eF.inv.hom.app T0 s₀)
  obtain ⟨i, x, hx⟩ := (EtaleLimitSections.limitSections_colimit (fieldStageSystem Y K)
    (fieldStageCone Y K) (fieldStageConeIsLimit Y K) (fieldStageCone_π_comp_hom Y K) Gs).1 s₂
  refine ⟨i, x, ?_⟩
  let W := (fieldStageSystem Y K).obj (op i)
  let t := smallEtaleBaseChangeLift p W (fieldStageProj Y K (op i))
    (fieldStageCone_π_comp_hom Y K (op i))
  have h1 : s₀ = eF.hom.hom.app T0 ((eU.hom.app Gs).hom.app T0 s₂) := by
    have a1 := type_hom_congr (congrArg
      (fun φ : (etaleTypeInverseImage p).obj Gs ⟶ (etaleTypeInverseImage p).obj Gs =>
        φ.hom.app T0) (eU.inv_hom_id_app Gs)) (eF.inv.hom.app T0 s₀)
    have a2 := type_hom_congr (congrArg
      (fun φ : (etaleModuleUnderlyingSets Λ _).obj H ⟶ (etaleModuleUnderlyingSets Λ _).obj H =>
        φ.hom.app T0) eF.inv_hom_id) s₀
    exact a2.symm.trans (congrArg (eF.hom.hom.app T0) a1.symm)
  have h2 := type_hom_congr ((eU.hom.app Gs).hom.naturality t.op)
    (((smallEtaleInverseImageAdjunction.{u, 0} p).unit.app Gs).hom.app (op W) x)
  have h3 := type_hom_congr (congrArg (fun φ : Gs ⟶ ((smallEtaleBaseChange
      p).sheafPushforwardContinuous
      (Type (u + 1)) Y.left.smallEtaleTopology (fieldBaseChange Y K).smallEtaleTopology).obj
        ((etaleTypeInverseImage p).obj Gs) => φ.hom.app (op W))
    (Adjunction.unit_leftAdjointUniq_hom_app (smallEtaleInverseImageAdjunction.{u, 0} p)
      (etaleTypeInverseImageAdj p) Gs)) x
  have h4 := type_hom_congr (eF.hom.hom.naturality t.op)
    (((etaleTypeInverseImageAdj p).unit.app Gs).hom.app (op W) x)
  have h5 := etaleModuleInverseImageForgetIso_hom_typeUnitSection Λ p G (V := W) x
  let T := (etaleTypeInverseImage p).obj Gs
  let Hs := (etaleModuleUnderlyingSets Λ _).obj H
  exact h1.trans ((congrArg (eF.hom.hom.app T0) ((congrArg ((eU.hom.app Gs).hom.app T0)
    hx.symm).trans (h2.trans (congrArg (T.obj.map t.op) h3)))).trans
      (h4.trans (congrArg (Hs.obj.map t.op) h5)))

end Stages

/-! ### The Galois action on `Γ(Y_K, G|_{Y_K})` -/

section Action

open scoped Stacks.DiscreteModuleTopology

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k))) (K : Type u)
  [Field K] [Algebra k K]

/-- Restriction to the final object of the small étale site is injective on global sections. -/
theorem ΓRes_etaleMkId_injective {T : Scheme.{u}} (H : EtaleModules.{u, 0} Λ T) :
    Function.Injective ⇑(H.ΓRes (op (Scheme.Etale.mk (𝟙 T)))) := by
  rw [← Sheaf.ΓNatIsoSheafSections_hom_app_general (isTerminalEtaleMkId T) H]
  exact (ConcreteCategory.bijective_of_isIso _).1

/-- Two lifts into a base change along the same morphism agree. -/
theorem smallEtaleBaseChangeLift_congr {Z T : Scheme.{u}} (p : T ⟶ Z) (W : Z.Etale)
    {r r' : T ⟶ W.left} (h : r = r') (hr : r ≫ W.hom = p) (hr' : r' ≫ W.hom = p) :
    smallEtaleBaseChangeLift p W r hr = smallEtaleBaseChangeLift p W r' hr' := by
  subst h
  rfl

/-- The precomposite of a morphism over `Y` with `id_Y × Spec σ` still lies over `Y`. -/
theorem galoisBaseChange_comp_lies_over (σ : K ≃ₐ[k] K) {W : Y.left.Etale}
    {r : fieldBaseChange Y K ⟶ W.left} (hr : r ≫ W.hom = fieldBaseChangeProj Y K) :
    (galoisBaseChange Y K σ ≫ r) ≫ W.hom = fieldBaseChangeProj Y K := by
  rw [Category.assoc, hr]
  exact galoisBaseChange_comp_fst Y K σ

/-- **The Galois action on a pulled back section.** If a global section `z` of `G|_{Y_K}` is, over
the final object, the restriction of the pulled back section `u(a)`, `a ∈ G(W)`, along the
morphism `Y_K ⟶ W ×_Y Y_K` given by `r : Y_K ⟶ W`, then `σ · z` is the restriction of `u(a)`
along the morphism given by `r ∘ (id_Y × Spec σ)`. -/
theorem ΓRes_fieldBaseChangeGlobalSectionsGaloisAction (σ : K ≃ₐ[k] K)
    (G : EtaleModules.{u, 0} Λ Y.left) {W : Y.left.Etale} (a : G.obj.obj (op W))
    {r : fieldBaseChange Y K ⟶ W.left} (hr : r ≫ W.hom = fieldBaseChangeProj Y K)
    (z : (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G))
    (hz : ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) z =
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).obj.map
        (smallEtaleBaseChangeLift (fieldBaseChangeProj Y K) W r hr).op
        (moduleUnitSection Λ (fieldBaseChangeProj Y K) G a)) :
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K))))
        ((fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} Λ Y K σ G) z) =
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).obj.map
        (smallEtaleBaseChangeLift (fieldBaseChangeProj Y K) W (galoisBaseChange Y K σ ≫ r)
          (galoisBaseChange_comp_lies_over Y K σ hr)).op
        (moduleUnitSection Λ (fieldBaseChangeProj Y K) G a) :=
  ΓRes_selfMapTwistAction_of_moduleUnitSection Λ (fieldBaseChangeProj Y K)
    (galoisBaseChange Y K σ) (galoisBaseChange_comp_fst Y K σ) G a z _ _ hz
    ((pullback.lift_fst _ _ _).trans (congrArg (galoisBaseChange Y K σ ≫ ·)
      (pullback.lift_fst _ _ _).symm))

/-- Restricting the pulled back section `u(a)` along equal lifts gives equal sections. -/
private theorem map_smallEtaleBaseChangeLift_congr (G : EtaleModules.{u, 0} Λ Y.left)
    {W : Y.left.Etale} (a : G.obj.obj (op W)) {r r' : fieldBaseChange Y K ⟶ W.left} (h : r = r')
    (hr : r ≫ W.hom = fieldBaseChangeProj Y K) (hr' : r' ≫ W.hom = fieldBaseChangeProj Y K) :
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).obj.map
        (smallEtaleBaseChangeLift (fieldBaseChangeProj Y K) W r hr).op
        (moduleUnitSection Λ (fieldBaseChangeProj Y K) G a) =
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).obj.map
        (smallEtaleBaseChangeLift (fieldBaseChangeProj Y K) W r' hr').op
        (moduleUnitSection Λ (fieldBaseChangeProj Y K) G a) := by
  subst h
  rfl

variable [Algebra.IsSeparable k K] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]

/-- **The identity of `K` acts trivially on `Γ(Y_K, G|_{Y_K})`.** -/
theorem fieldBaseChangeGlobalSectionsGaloisAction_one (G : EtaleModules.{u, 0} Λ Y.left) :
    fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} Λ Y K 1 G = 𝟙 _ := by
  ext z
  apply ΓRes_etaleMkId_injective
  obtain ⟨i, x, hz⟩ := exists_fieldStageSection_eq Λ Y K G z
  rw [ΓRes_fieldBaseChangeGlobalSectionsGaloisAction Λ Y K 1 G x _ z hz, ModuleCat.id_apply, hz]
  exact map_smallEtaleBaseChangeLift_congr Λ Y K G x
    (by rw [galoisBaseChange_one]; exact Category.id_comp _) _ _

/-- **`σ ↦ (σ acting on Γ(Y_K, G|_{Y_K}))` is a left action**: `στ` acts as `τ` followed by `σ`. -/
theorem fieldBaseChangeGlobalSectionsGaloisAction_mul (σ τ : K ≃ₐ[k] K)
    (G : EtaleModules.{u, 0} Λ Y.left) :
    fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} Λ Y K (σ * τ) G =
      fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} Λ Y K τ G ≫
        fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} Λ Y K σ G := by
  ext z
  apply ΓRes_etaleMkId_injective
  obtain ⟨i, x, hz⟩ := exists_fieldStageSection_eq Λ Y K G z
  rw [ΓRes_fieldBaseChangeGlobalSectionsGaloisAction Λ Y K (σ * τ) G x _ z hz, ModuleCat.comp_apply,
    ΓRes_fieldBaseChangeGlobalSectionsGaloisAction Λ Y K σ G x _ _
      (ΓRes_fieldBaseChangeGlobalSectionsGaloisAction Λ Y K τ G x _ z hz)]
  exact map_smallEtaleBaseChangeLift_congr Λ Y K G x
    (by rw [galoisBaseChange_mul]; exact Category.assoc _ _ _) _ _

/-- **Every section of `Γ(Y_K, G|_{Y_K})` has an open stabilizer**: a section coming from the
finite stage `Y_E` is fixed by the open subgroup `Gal(K/E)`. -/
theorem isOpen_stabilizer_fieldBaseChangeGlobalSectionsGaloisAction
    (G : EtaleModules.{u, 0} Λ Y.left)
    (z : (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G)) :
    IsOpen {σ : K ≃ₐ[k] K | fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} Λ Y K σ G z = z} := by
  obtain ⟨i, x, hz⟩ := exists_fieldStageSection_eq Λ Y K G z
  have : FiniteDimensional k i.1 := i.2
  let a := fun σ => fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} Λ Y K σ G
  let S : Subgroup (K ≃ₐ[k] K) :=
    { carrier := {σ | a σ z = z}
      mul_mem' := fun {σ τ} hσ hτ => by
        show a (σ * τ) z = z
        rw [show a (σ * τ) = a τ ≫ a σ from
          fieldBaseChangeGlobalSectionsGaloisAction_mul Λ Y K σ τ G, ModuleCat.comp_apply]
        exact (congrArg (a σ) hτ).trans hσ
      one_mem' := by
        show a 1 z = z
        rw [show a 1 = 𝟙 _ from fieldBaseChangeGlobalSectionsGaloisAction_one Λ Y K G]
        rfl
      inv_mem' := fun {σ} hσ => by
        show a σ⁻¹ z = z
        have h := congrArg (a σ⁻¹) hσ
        rw [← ModuleCat.comp_apply, show a σ ≫ a σ⁻¹ = a (σ⁻¹ * σ) from
          (fieldBaseChangeGlobalSectionsGaloisAction_mul Λ Y K σ⁻¹ σ G).symm, inv_mul_cancel,
          show a 1 = 𝟙 _ from fieldBaseChangeGlobalSectionsGaloisAction_one Λ Y K G] at h
        exact h.symm }
  refine Subgroup.isOpen_mono (H₁ := i.1.fixingSubgroup) (H₂ := S) (fun σ hσ => ?_)
    (IntermediateField.fixingSubgroup_isOpen i.1)
  show fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} Λ Y K σ G z = z
  apply ΓRes_etaleMkId_injective
  rw [ΓRes_fieldBaseChangeGlobalSectionsGaloisAction Λ Y K σ G x _ z hz, hz]
  exact map_smallEtaleBaseChangeLift_congr Λ Y K G x
    (galoisBaseChange_comp_fieldStageProj Y K (op i) σ hσ) _ _

/-- **`Γ(Y_K, G|_{Y_K})` with its Galois action, as a representation** of `Aut_k(K)`. -/
def fieldBaseChangeGlobalSectionsRepresentation (G : EtaleModules.{u, 0} Λ Y.left) :
    Representation Λ (K ≃ₐ[k] K) ((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G)) where
  toFun σ := (fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} Λ Y K σ G).hom
  map_one' := by
    rw [fieldBaseChangeGlobalSectionsGaloisAction_one Λ Y K G]
    rfl
  map_mul' σ τ := by
    rw [fieldBaseChangeGlobalSectionsGaloisAction_mul Λ Y K σ τ G]
    rfl

end Action

/-! ### The functor `F ↦ Γ(Y_K, F|_{Y_K})` into discrete Galois modules -/

section Functor

open scoped Stacks.DiscreteModuleTopology

/-- **The category of discrete `Λ[Aut_k(K)]`-modules**: `Λ`-modules with an action of
`Aut_k(K)` which is continuous for the Krull topology and the discrete topology on the module.
For `K` a separable closure of a finite field `k`, `Aut_k(K) ≅ Ẑ`, and this is the heart of the
bounded below derived category in which the Trace Formula chapter places `RΓ(X_k̄, -)` and
`RΓ_c(X_k̄, -)` "as objects of `D(Λ[[Ẑ]])`" (see the module docstring). -/
abbrev GaloisModules (Λ : Type) [Ring Λ] (k : Type u) [Field k] (K : Type u) [Field K]
    [Algebra k K] :=
  Stacks.Injectives.ContinuousModule.{0, u, u + 1} Λ (K ≃ₐ[k] K)

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] (K : Type u) [Field K] [Algebra k K]
  [Algebra.IsSeparable k K]

/-- **`F ↦ Γ(Y_K, F|_{Y_K})` with its Galois action**, as a functor from sheaves of `Λ`-modules on
`Y_étale` to discrete `Λ[Aut_k(K)]`-modules. The action of `σ` is
`Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsGaloisAction`, induced by
`id_Y × Spec σ`; it is continuous because every global section comes from a finite stage
`Y_E` (Stacks 09YQ in degree zero), `Y` being quasi-compact and quasi-separated. -/
def galoisGlobalSections : EtaleModules.{u, 0} Λ Y.left ⥤ GaloisModules Λ k K where
  obj G := Stacks.GroupCohomology.ofRepresentation
    (fieldBaseChangeGlobalSectionsRepresentation Λ Y K G)
    ((Stacks.GroupCohomology.isContinuous_actionOfRepresentation_iff _).2
      (isOpen_stabilizer_fieldBaseChangeGlobalSectionsGaloisAction Λ Y K G))
  map v := ObjectProperty.homMk (ObjectProperty.homMk
    { hom := (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y K)).map
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).map v)
      comm := fun σ => fieldBaseChangeGlobalSectionsGaloisAction_naturality Λ Y K σ v })
  map_id G := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    exact ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K) ⋙
      etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y K)).map_id G)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    exact ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K) ⋙
      etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y K)).map_comp f g)

/-- **Forgetting the Galois action recovers `Γ(Y_K, -|_{Y_K})`**, on the nose. -/
theorem galoisGlobalSections_comp_underlying :
    galoisGlobalSections Λ Y K ⋙ Stacks.Injectives.continuousModuleUnderlying Λ (K ≃ₐ[k] K) =
      etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K) ⋙
        etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y K) :=
  rfl

/-- The action of `σ` on `Γ^Gal(F)` is
    `Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsGaloisAction`. -/
theorem galoisGlobalSections_ρ (G : EtaleModules.{u, 0} Λ Y.left) (σ : K ≃ₐ[k] K) :
    (((galoisGlobalSections Λ Y K).obj G).obj.obj.ρ σ).asHom =
      fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} Λ Y K σ G :=
  rfl

/-- The underlying `Λ`-module functor of discrete Galois modules is additive. -/
instance additive_injectivesContinuousModuleUnderlying :
    (Stacks.Injectives.continuousModuleUnderlying Λ (K ≃ₐ[k] K)).Additive where
  map_add := by
    intros
    apply ModuleCat.hom_ext
    rfl

/-- `Γ^Gal` is additive, its underlying functor `Γ(Y_K, -|_{Y_K})` being additive. -/
instance galoisGlobalSections_additive : (galoisGlobalSections Λ Y K).Additive := by
  have : (galoisGlobalSections Λ Y K ⋙
      Stacks.Injectives.continuousModuleUnderlying Λ (K ≃ₐ[k] K)).Additive := by
    rw [galoisGlobalSections_comp_underlying]
    infer_instance
  have : (Stacks.Injectives.continuousModuleUnderlying Λ (K ≃ₐ[k] K)).Faithful :=
    ⟨fun h => ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ (Action.hom_ext _ _ h))⟩
  exact Functor.additive_of_comp_faithful _
    (Stacks.Injectives.continuousModuleUnderlying Λ (K ≃ₐ[k] K))

end Functor

end Stacks.EtaleCohomology

end
