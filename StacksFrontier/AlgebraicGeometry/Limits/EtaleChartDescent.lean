module

public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.EmptyFibreAtStage
public import StacksFrontier.AlgebraicGeometry.Limits.LimitPreservingFunctorOfPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending étale charts of the limit of a cofiltered system of schemes

Let `X = lim Xᵢ` be the limit of a cofiltered inverse system of quasi-compact and
quasi-separated schemes with affine transition morphisms. A quasi-compact and quasi-separated
scheme étale over `X` is the base change of a scheme étale over some `Xᵢ`
([Stacks, Tag 01ZM] part (1) and [Stacks, Tag 07RP]); a finite jointly surjective family of such
charts descends to a jointly surjective family at some stage ([Stacks, Tag 05F3]); and a morphism
from the limit of a system of charts to a scheme locally of finite presentation over a fixed base
factors through a stage, two such factorizations agreeing at a later stage ([Stacks, Tag 01ZC]).

These are the three descent steps of the passage from the strict henselization to an étale
neighbourhood in the proof of [Stacks, Tag 03Q9] for global sections.

## Main results

* `AlgebraicGeometry.exists_isPullback_etale_of_etale` — an étale chart of the limit is the base
  change of an étale chart of a stage.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
* [Stacks Project, Tag 05F3](https://stacks.math.columbia.edu/tag/05F3)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism whose composite with an isomorphism is étale is étale. -/
private lemma etale_of_comp_isIso {A B C : Scheme.{u}} (a : A ⟶ B) (g : B ⟶ C) [IsIso g]
    (h : Etale (a ≫ g)) : Etale a := by
  rw [show a = (a ≫ g) ≫ inv g by simp]
  infer_instance

/-- The composite of an étale morphism with an isomorphism is étale. -/
private lemma etale_isIso_comp {A B C : Scheme.{u}} (g : A ⟶ B) (a : B ⟶ C) [IsIso g]
    (h : Etale a) : Etale (g ≫ a) :=
  inferInstance

/-- The composite of an étale morphism followed by an isomorphism is étale. -/
private lemma etale_comp_isIso {A B C : Scheme.{u}} (a : A ⟶ B) (g : B ⟶ C) [IsIso g]
    (h : Etale a) : Etale (a ≫ g) :=
  inferInstance

/-- The source of a quasi-compact and quasi-separated morphism to a quasi-compact and
quasi-separated space is quasi-compact and quasi-separated. -/
private lemma compactSpace_and_quasiSeparatedSpace_of_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    CompactSpace X ∧ QuasiSeparatedSpace X :=
  ⟨QuasiCompact.compactSpace_of_compactSpace f,
    (quasiSeparated_iff_quasiSeparatedSpace f).mp inferInstance⟩

section Objects

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D) (hc : IsLimit c)

include hc in
/-- The limit of a cofiltered system of quasi-compact and quasi-separated schemes with affine
transition morphisms is quasi-compact and quasi-separated, its projections being affine. -/
theorem compactSpace_and_quasiSeparatedSpace_pt :
    CompactSpace c.pt ∧ QuasiSeparatedSpace c.pt := by
  have : InitiallySmall.{u} I := initiallySmall_of_essentiallySmall I
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  have : IsAffineHom (c.π.app i₀) := isAffineHom_π_app_of_initiallySmall D c hc i₀
  exact ⟨QuasiCompact.compactSpace_of_compactSpace (c.π.app i₀),
    quasiSeparatedSpace_of_quasiSeparated (c.π.app i₀)⟩

include hc in
/-- **An étale chart of the limit comes from a stage.** A quasi-compact and quasi-separated
scheme `U` étale over the limit `X` of a cofiltered system of quasi-compact and quasi-separated
schemes with affine transition morphisms is the base change of a quasi-compact and
quasi-separated scheme étale over some stage: this is [Stacks, Tag 01ZM] part (1) followed by
[Stacks, Tag 07RP]. -/
theorem exists_isPullback_etale_of_etale {U : Scheme.{u}} (u : U ⟶ c.pt) [Etale u]
    [CompactSpace U] [QuasiSeparatedSpace U] :
    ∃ (i : I) (U' : Scheme.{u}) (u' : U' ⟶ D.obj i) (θ : U ⟶ U'),
      Etale u' ∧ CompactSpace U' ∧ QuasiSeparatedSpace U' ∧ IsPullback θ u u' (c.π.app i) := by
  obtain ⟨hcpt, hqs⟩ := compactSpace_and_quasiSeparatedSpace_pt D c hc
  have : QuasiCompact u := quasiCompact_of_compactSpace u
  have : QuasiSeparated u := QuasiSeparated.of_quasiSeparatedSpace u
  have hfp : FinitePresentation (Over.mk u).hom :=
    ⟨inferInstanceAs (LocallyOfFinitePresentation u), inferInstanceAs (QuasiCompact u),
      inferInstanceAs (QuasiSeparated u)⟩
  obtain ⟨i, Xi, hXi, ⟨e⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation D c hc (Over.mk u) hfp
  obtain ⟨_, _, _⟩ := hXi
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_hom Xi.hom
  let Y₀ : Over (D.obj i) := Over.mk (𝟙 (D.obj i))
  let f₀ : Xi ⟶ Y₀ := Over.homMk Xi.hom (Category.comp_id _)
  have : CompactSpace Y₀.left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace Y₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  have : LocallyOfFinitePresentation f₀.left := inferInstanceAs
    (LocallyOfFinitePresentation Xi.hom)
  -- the base change of `f₀` to the limit is `u`, up to the isomorphism `e`
  have hlim : Etale ((Over.pullback (c.π.app i)).map f₀).left := by
    have hw : ((Over.pullback (c.π.app i)).map f₀).left ≫ pullback.snd (𝟙 (D.obj i))
        (c.π.app i) = e.inv.left ≫ u :=
      (overPullback_map_left_snd (c.π.app i) f₀).trans (Over.w e.inv).symm
    have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
    exact etale_of_comp_isIso _ (pullback.snd (𝟙 (D.obj i)) (c.π.app i))
      (hw ▸ etale_isIso_comp _ _ inferInstance)
  obtain ⟨j, hj⟩ := exists_etale_pullback_of_isLimit D c hc i Xi Y₀ f₀
  have hu' : Etale (pullback.snd Xi.hom (D.map j.hom)) := by
    rw [← overPullback_map_left_snd (D.map j.hom) f₀]
    exact @etale_comp_isIso _ _ _ _ _
      (inferInstanceAs (IsIso (pullback.snd (𝟙 (D.obj i)) (D.map j.hom)))) hj
  let θ₀ : pullback Xi.hom (c.π.app i) ⟶ pullback Xi.hom (D.map j.hom) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ c.π.app j.left)
      (by rw [Category.assoc, c.w j.hom, pullback.condition])
  have hpb : IsPullback θ₀ (pullback.snd Xi.hom (c.π.app i))
      (pullback.snd Xi.hom (D.map j.hom)) (c.π.app j.left) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback Xi.hom (D.map j.hom))
    rw [pullback.lift_fst, c.w j.hom]
    exact IsPullback.of_hasPullback Xi.hom (c.π.app i)
  refine ⟨j.left, pullback Xi.hom (D.map j.hom), pullback.snd _ _, e.hom.left ≫ θ₀, hu',
    (compactSpace_and_quasiSeparatedSpace_of_hom (pullback.snd Xi.hom (D.map j.hom))).1,
    (compactSpace_and_quasiSeparatedSpace_of_hom (pullback.snd Xi.hom (D.map j.hom))).2, ?_⟩
  let e' : U ≅ pullback Xi.hom (c.π.app i) := (Over.forget _).mapIso e
  refine IsPullback.of_iso hpb e'.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    (by simp) (by simp)
  · simp [e']
  · simpa [e'] using (Over.w e.inv).symm

/-- The comparison `U ×_{Xᵢ₀} X ⟶ U ×_{Xᵢ₀} Xⱼ` for a scheme `U` over the stage `Xᵢ₀`. -/
noncomputable abbrev stageBaseChangeComparison {i₀ j : I} (e : j ⟶ i₀) {U : Scheme.{u}}
    (u : U ⟶ D.obj i₀) :
    pullback (c.π.app i₀) u ⟶ pullback (D.map e) u :=
  pullback.lift (pullback.fst _ _ ≫ c.π.app j) (pullback.snd _ _)
    (by rw [Category.assoc, c.w e, pullback.condition])

omit [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
include hc in
/-- **A morphism out of the limit of a system of charts factors through a stage.** Let
`u : U ⟶ Xᵢ₀` be quasi-compact and quasi-separated over a stage, and let `W ⟶ S` be locally of
finite presentation over a scheme `S` receiving `Xᵢ₀`. A morphism `U ×_{Xᵢ₀} X ⟶ W` over `S` is
the composite of the comparison `U ×_{Xᵢ₀} X ⟶ U ×_{Xᵢ₀} Xⱼ` with a morphism `U ×_{Xᵢ₀} Xⱼ ⟶ W`
over `S`, for some `j ⟶ i₀`. This is [Stacks, Tag 01ZC] for the system `U ×_{Xᵢ₀} Xⱼ`. -/
@[ega "IV 8.13.1" "surjectivity", sga "3 VIB 3.8" "partial"]
theorem exists_stage_hom_of_hom (i₀ : I) {U : Scheme.{u}} (u : U ⟶ D.obj i₀) [CompactSpace U]
    [QuasiSeparatedSpace U] {S W : Scheme.{u}} (σ : D.obj i₀ ⟶ S) (w : W ⟶ S)
    [LocallyOfFinitePresentation w] (φ : pullback (c.π.app i₀) u ⟶ W)
    (hφ : φ ≫ w = pullback.snd _ u ≫ u ≫ σ) :
    ∃ (j : I) (e : j ⟶ i₀) (ψ : pullback (D.map e) u ⟶ W),
      ψ ≫ w = pullback.snd _ u ≫ u ≫ σ ∧ stageBaseChangeComparison D c e u ≫ ψ = φ := by
  let H : Over (D.obj i₀) ⥤ Over S := Over.pullback u ⋙ Over.map (u ≫ σ)
  let G : Over i₀ ⥤ Over S := Over.post D ⋙ H
  let cG : Cone G := H.mapCone ((Over.conePost D i₀).obj c)
  have : IsConnected (Over i₀) := IsCofiltered.isConnected _
  have h₂ : IsLimit ((Over.forget U).mapCone
      ((Over.pullback u).mapCone ((Over.conePost D i₀).obj c))) :=
    isLimitOfPreserves (Over.forget U)
      (isLimitOfPreserves (Over.pullback u) (Over.isLimitConePost i₀ hc))
  have hG : IsLimit cG := isLimitOfReflects (Over.forget S) h₂
  have hpres := (Scheme.locallyOfFinitePresentation_iff_isLimitPreservingOnAffineTransitions
    w).mp inferInstance (Over i₀) G
    (fun a b g => by
      change IsAffineHom ((Over.pullback u).map ((Over.post D).map g)).left
      exact MorphismProperty.of_isPullback (overPullback_isPullback u ((Over.post D).obj a)
        ((Over.post D).obj b) ((Over.post D).map g))
        (show IsAffineHom (D.map g.left) from inferInstance))
    (fun a => (compactSpace_and_quasiSeparatedSpace_of_hom
      (pullback.snd (D.map a.hom) u)).1)
    (fun a => (compactSpace_and_quasiSeparatedSpace_of_hom
      (pullback.snd (D.map a.hom) u)).2)
  obtain ⟨hcol⟩ := hpres.preserves hG.op
  let φ' : cG.pt ⟶ Over.mk w := Over.homMk φ hφ
  obtain ⟨k, ψ', hψ'⟩ := Types.jointly_surjective_of_isColimit hcol φ'
  exact ⟨k.unop.left, k.unop.hom, ψ'.left, Over.w ψ', congrArg CommaMorphism.left hψ'⟩

omit [IsCofiltered I] [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- **A chart of the limit modelled over a stage is modelled over every later stage.** If
`V = U' ×_{Xᵢ} X`, then `V = (U' ×_{Xᵢ} Xⱼ) ×_{Xⱼ} X` for every `j ⟶ i`. -/
theorem isPullback_stage_of_isPullback {i j : I} (e : j ⟶ i) {V U' : Scheme.{u}}
    {v : V ⟶ c.pt} {u' : U' ⟶ D.obj i} {θ : V ⟶ U'} (h : IsPullback θ v u' (c.π.app i)) :
    IsPullback (pullback.lift θ (v ≫ c.π.app j) (by rw [h.w, Category.assoc, c.w e]))
      v (pullback.snd u' (D.map e)) (c.π.app j) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback u' (D.map e))
  rw [pullback.lift_fst, c.w e]
  exact h

omit [∀ i, QuasiSeparatedSpace (D.obj i)] in
include hc in
/-- **A finite family of étale charts covering the limit covers a later stage.** Let
`uₘ : U'ₘ ⟶ Xᵢ` be finitely many étale morphisms whose base changes to the limit `X` are jointly
surjective. Then their base changes to some later stage `Xⱼ` are jointly surjective. The union of
their images is open in `Xᵢ` and contains the image of `X`; its closed complement therefore misses
the image of some `Xⱼ` ([Stacks, Tag 05F3]). -/
theorem exists_stage_jointlySurjective {M : Type*} (i : I) (U' : M → Scheme.{u})
    (u' : ∀ m, U' m ⟶ D.obj i) (hu' : ∀ m, IsOpenMap (u' m).base)
    (hcov : ∀ z : c.pt, ∃ m, ∃ y : (pullback (u' m) (c.π.app i) : Scheme.{u}),
      (pullback.snd (u' m) (c.π.app i)).base y = z) :
    ∃ (j : I) (e : j ⟶ i), ∀ x : D.obj j, ∃ m,
      ∃ y : (pullback (u' m) (D.map e) : Scheme.{u}),
        (pullback.snd (u' m) (D.map e)).base y = x := by
  have : InitiallySmall.{u} I := initiallySmall_of_essentiallySmall I
  let E : Set (D.obj i) := ⋃ m, Set.range (u' m).base
  have hEopen : IsOpen E := isOpen_iUnion fun m => (hu' m).isOpen_range
  let Cl : TopologicalSpace.Closeds (D.obj i) := ⟨Eᶜ, hEopen.isClosed_compl⟩
  let Ii := Scheme.IdealSheafData.vanishingIdeal Cl
  have hrange : Set.range Ii.subschemeι.base = Eᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : CompactSpace Ii.subscheme := QuasiCompact.compactSpace_of_compactSpace Ii.subschemeι
  have hlim : ∀ z : c.pt, (c.π.app i).base z ∈ E := fun z => by
    obtain ⟨m, y, rfl⟩ := hcov z
    refine Set.mem_iUnion.mpr ⟨m, (pullback.fst (u' m) (c.π.app i)).base y, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have hT : IsEmpty (pullback (c.π.app i) Ii.subschemeι : Scheme.{u}) := by
    rw [Scheme.isEmpty_pullback_iff, hrange]
    exact Set.disjoint_compl_right_iff_subset.mpr (Set.range_subset_iff.mpr hlim)
  obtain ⟨j, e, he⟩ := exists_isEmpty_pullback_map_of_isEmpty_pullback_π_app D c hc i
    Ii.subschemeι hT
  rw [Scheme.isEmpty_pullback_iff, hrange] at he
  refine ⟨j, e, fun x => ?_⟩
  have hx : (D.map e).base x ∈ E := by
    by_contra hx
    exact Set.disjoint_left.mp he ⟨x, rfl⟩ hx
  obtain ⟨m, w, hw⟩ := Set.mem_iUnion.mp hx
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback w x hw
  exact ⟨m, z, hz⟩

end Objects

end AlgebraicGeometry
