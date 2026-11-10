module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizerSituation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionModificationEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
import all StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismsFromProperModification

/-!
# Comparing compatibility witnesses of Artin's contraction functor

In the situation of Stacks 0GH8, recorded by `AlgebraicGeometry.Artin.ContractionSituation`,
the compatibility condition of a triple `(Z, u', x̂)` over `V` asks for a witness `V' ⟶ V`, `x̂'`,
`x'` (`AlgebraicGeometry.Artin.ContractionSituation.CompatibilityWitness`). This file records two
facts about witnesses used in Stacks 0GHD.

* `AlgebraicGeometry.Artin.ContractionSituation.CompatibilityWitness.pullback`: the witness of a
  transported triple constructed in the proof of Stacks 0GHA, `V'₂ = V₂ ×_{V₁} V'₁`, as data.
* `AlgebraicGeometry.Artin.ContractionSituation.CompatibilityWitness.exists_hom`: over a locally
  Noetherian `V`, any two witnesses of the same triple are related by a morphism over `V`
  compatible with the two morphisms `x'`. This is the uniqueness half of the main theorem on
  dilatations (Stacks 0GDU) together with the uniqueness statement of Stacks 0GI1.

As an application, for the data `d` of Stacks 0GHD and a morphism `φ : A ⟶ V` from a locally
Noetherian `A` along which the two triples restrict to the same element of `F(A)`, the witness
`A ×_V V'₁` maps to `E'` over `V`
(`AlgebraicGeometry.Artin.ContractionEqualizer.exists_toE'_of_mapTriple_eq`).

## References

* [Stacks Project, Tag 0GDU](https://stacks.math.columbia.edu/tag/0GDU)
* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
* [Stacks Project, Tag 0GHD](https://stacks.math.columbia.edu/tag/0GHD)
* [Stacks Project, Tag 0GI1](https://stacks.math.columbia.edu/tag/0GI1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Two morphisms into an algebraic space whose sheafified universe lifts agree after the
inclusion of a completion agree already on the completion subfunctor. -/
theorem completionSubfunctor_ι_whiskerRight_eq {X W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (T : Set (points B S hS X)) (a b : X ⟶ W)
    (h : completionSheafInclusion B S hS X T ≫ sheafifiedULiftMap B S hS a =
      completionSheafInclusion B S hS X T ≫ sheafifiedULiftMap B S hS b) :
    (completionSubfunctor B S hS X T).ι ≫ Functor.whiskerRight a uliftFunctor.{u + 1} =
      (completionSubfunctor B S hS X T).ι ≫ Functor.whiskerRight b uliftFunctor.{u + 1} := by
  let J := BigFppfOver.topology B S hS
  have hs := FormalSpace.isSheaf_comp_uliftFunctor B S hS hW
  have : IsIso (J.toSheafify (W ⋙ uliftFunctor.{u + 1})) := J.isIso_toSheafify hs
  have hA : J.toSheafify (completionSubfunctor B S hS X T).toFunctor ≫
      (completionSheafInclusion B S hS X T).hom =
      (completionSubfunctor B S hS X T).ι ≫ J.toSheafify (X ⋙ uliftFunctor.{u + 1}) :=
    (J.toSheafify_naturality _).symm
  have hB : ∀ k : X ⟶ W, J.toSheafify (X ⋙ uliftFunctor.{u + 1}) ≫
      (sheafifiedULiftMap B S hS k).hom =
      Functor.whiskerRight k uliftFunctor.{u + 1} ≫ J.toSheafify (W ⋙ uliftFunctor.{u + 1}) :=
    fun k => (J.toSheafify_naturality _).symm
  have key : ∀ k : X ⟶ W, ((completionSubfunctor B S hS X T).ι ≫
      Functor.whiskerRight k uliftFunctor.{u + 1}) ≫ J.toSheafify (W ⋙ uliftFunctor.{u + 1}) =
      J.toSheafify (completionSubfunctor B S hS X T).toFunctor ≫
        ((completionSheafInclusion B S hS X T).hom ≫ (sheafifiedULiftMap B S hS k).hom) := by
    intro k
    exact (Category.assoc _ _ _).trans ((congrArg ((completionSubfunctor B S hS X T).ι ≫ ·)
      (hB k).symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (sheafifiedULiftMap B S hS k).hom) hA.symm).trans
          (Category.assoc _ _ _))))
  have : Mono (J.toSheafify (W ⋙ uliftFunctor.{u + 1})) := IsIso.mono_of_iso _
  rw [← cancel_mono (J.toSheafify (W ⋙ uliftFunctor.{u + 1})), key, key]
  exact congrArg (J.toSheafify (completionSubfunctor B S hS X T).toFunctor ≫ ·)
    (congrArg (fun f => f.hom) h)

end Space

namespace Artin

attribute [local instance] Space.pointTopology

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site needs a larger budget
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ContractionWitnessComparison
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ContractionWitnessComparison
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {c : ContractionSituation B S hS}

/-- **The witness of a transported triple**, the construction of the proof of Stacks 0GHA as
data: for a witness `V'₁ ⟶ V₁`, `x̂'₁`, `x'₁` of the compatibility of a triple over `V₁` and a
morphism `φ : V₂ ⟶ V₁`, the fibre product `V'₂ = V₂ ×_{V₁} V'₁`, the composition of `x̂'₁` with
`V'_{2,/Z₂} ⟶ V'_{1,/Z₁}` and the composition of `x'₁` with `V'₂ ⟶ V'₁` witness the
compatibility of the transported triple. -/
def CompatibilityWitness.pullback {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁) (t : Triple c V₁)
    (w : CompatibilityWitness c V₁ t.Z t.u t.xhat) :
    CompatibilityWitness c V₂ (mapTriple c φ t).Z (mapTriple c φ t).u (mapTriple c φ t).xhat :=
  have hpb : IsPullback (Limits.pullback.fst (yoneda.map φ) w.p)
      (Limits.pullback.snd (yoneda.map φ) w.p) (yoneda.map φ) w.p := IsPullback.of_hasPullback _ _
  have halg : IsAlgebraicSpace B S hS (Limits.pullback (yoneda.map φ) w.p) :=
    isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS V₂)
      w.isAlgebraicSpace_V' (isAlgebraicSpace_yoneda B S hS V₁)
  have hb : Space.pointsMap B S hS (Limits.pullback (yoneda.map φ) w.p)
        (Limits.pullback.fst (yoneda.map φ) w.p) ⁻¹' (mapTriple c φ t).Z ⊆
      Space.pointsMap B S hS (Limits.pullback (yoneda.map φ) w.p)
        (Limits.pullback.snd (yoneda.map φ) w.p) ⁻¹'
          (Space.pointsMap B S hS w.V' w.p ⁻¹' t.Z) := by
    intro z hz
    have hcomm := congrFun (congrArg
      (Space.pointsMap B S hS (Limits.pullback (yoneda.map φ) w.p)) hpb.w) z
    rw [Space.pointsMap_comp, Space.pointsMap_comp, Function.comp_apply,
      Function.comp_apply] at hcomm
    have hz' : Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ)
        (Space.pointsMap B S hS (Limits.pullback (yoneda.map φ) w.p)
          (Limits.pullback.fst (yoneda.map φ) w.p) z) ∈ t.Z := hz
    rw [hcomm] at hz'
    exact hz'
  have hproper : Space.IsProper B S hS (Limits.pullback.fst (yoneda.map φ) w.p) := by
    have hsq : IsPullback
        (ObjectProperty.homMk (Limits.pullback.fst (yoneda.map φ) w.p) :
          (⟨Limits.pullback (yoneda.map φ) w.p, halg⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨yoneda.obj V₂, isAlgebraicSpace_yoneda B S hS V₂⟩)
        (ObjectProperty.homMk (Limits.pullback.snd (yoneda.map φ) w.p) :
          (⟨Limits.pullback (yoneda.map φ) w.p, halg⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨w.V', w.isAlgebraicSpace_V'⟩)
        (ObjectProperty.homMk (yoneda.map φ) :
          (⟨yoneda.obj V₂, isAlgebraicSpace_yoneda B S hS V₂⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨yoneda.obj V₁, isAlgebraicSpace_yoneda B S hS V₁⟩)
        (ObjectProperty.homMk w.p :
          (⟨w.V', w.isAlgebraicSpace_V'⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨yoneda.obj V₁, isAlgebraicSpace_yoneda B S hS V₁⟩) :=
      IsPullback.of_map_of_faithful
        (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
          IsAlgebraicSpace B S hS F)) hpb
    exact (Space.isProper_isStableUnderBaseChange B S hS).of_isPullback hsq.flip
      w.isProper_p
  have hr : Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ) (mapTriple c φ t).Zᶜ t.Zᶜ
      (fun _ hz => hz) ≫ (Space.openSubspaceOfPoints B S hS (yoneda.obj V₁) t.Zᶜ).ι =
    (Space.openSubspaceOfPoints B S hS (yoneda.obj V₂) (mapTriple c φ t).Zᶜ).ι ≫ yoneda.map φ :=
    Space.openSubspaceOfPointsRestrict_comp_ι B S hS _ _ _ _
  have hj : (Space.openSubspaceOfPoints B S hS (yoneda.obj V₁) t.Zᶜ).ι = w.j ≫ w.p := by
    have hw := w.isPullback_j.w
    rwa [Category.id_comp] at hw
  have hlift : (Space.openSubspaceOfPoints B S hS (yoneda.obj V₂) (mapTriple c φ t).Zᶜ).ι ≫
      yoneda.map φ = (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ)
        (mapTriple c φ t).Zᶜ t.Zᶜ (fun _ hz => hz) ≫ w.j) ≫ w.p := by
    rw [Category.assoc, ← hj, hr]
  { V' := Limits.pullback (yoneda.map φ) w.p
    isAlgebraicSpace_V' := halg
    p := Limits.pullback.fst (yoneda.map φ) w.p
    isProper_p := hproper
    j := hpb.lift _ _ hlift
    isPullback_j := by
      refine (IsPullback.of_right ?_ ?_ hpb.flip).flip
      · have hid : IsPullback
            (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ) (mapTriple c φ t).Zᶜ t.Zᶜ
              (fun _ hz => hz)) (𝟙 _) (𝟙 _)
            (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ) (mapTriple c φ t).Zᶜ t.Zᶜ
              (fun _ hz => hz)) :=
          IsPullback.of_id_snd
        have hcomposite := hid.paste_horiz w.isPullback_j.flip
        rw [hr] at hcomposite
        have hsnd : hpb.lift _ _ hlift ≫ Limits.pullback.snd (yoneda.map φ) w.p =
            Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ) (mapTriple c φ t).Zᶜ t.Zᶜ
              (fun _ hz => hz) ≫ w.j :=
          hpb.lift_snd _ _ hlift
        rwa [← hsnd] at hcomposite
      · rw [hpb.lift_fst, Category.id_comp]
    xhat' := Space.completionSheafRestrict B S hS
      (Limits.pullback.snd (yoneda.map φ) w.p) _ _ hb ≫ w.xhat'
    isPullback_xhat' :=
      (Space.isPullback_completionSheafRestrict B S hS (Limits.pullback.fst (yoneda.map φ) w.p)
        (Limits.pullback.snd (yoneda.map φ) w.p) (yoneda.map φ) w.p hpb t.Z _
        (mapTriple c φ t).Z _ rfl rfl rfl (fun _ hz => hz) hb (fun _ hz => hz)
        (fun _ hz => hz)).paste_vert w.isPullback_xhat'
    x' := Limits.pullback.snd (yoneda.map φ) w.p ≫ w.x'
    restrict_x' := by
      rw [← Category.assoc, hpb.lift_snd, Category.assoc, w.restrict_x']
      exact (Category.assoc _ _ _).symm
    completion_x' := by
      rw [Space.sheafifiedULiftMap_comp, ← Category.assoc,
        ← Space.completionSheafRestrict_comp_inclusion B S hS
          (Limits.pullback.snd (yoneda.map φ) w.p) _ _ hb,
        Category.assoc, w.completion_x', ← Category.assoc] }

/-- The structure morphism `p` of the pulled-back witness is the first projection of the pullback
of `p` along `φ`. -/
@[simp]
theorem CompatibilityWitness.pullback_p {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁)
    (t : Triple c V₁) (w : CompatibilityWitness c V₁ t.Z t.u t.xhat) :
    (w.pullback φ t).p = Limits.pullback.fst (yoneda.map φ) w.p := rfl

/-- The morphism `x'` of the pulled-back witness is the second projection of the pullback of `p`
along `φ`, followed by `x'`. -/
@[simp]
theorem CompatibilityWitness.pullback_witnessMap {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁)
    (t : Triple c V₁) (w : CompatibilityWitness c V₁ t.Z t.u t.xhat) :
    (w.pullback φ t).x' = Limits.pullback.snd (yoneda.map φ) w.p ≫ w.x' := rfl

/-- If `j` is the pullback of `p` along `ι` (with the identity as the other leg), then any `k`
with `k ≫ p = a ≫ ι` factors as `a ≫ j`. -/
private theorem eq_comp_of_isPullback_id_left {C : Type*} [Category C] {U V' V A : C}
    {j : U ⟶ V'} {ι : U ⟶ V} {p : V' ⟶ V} (h : IsPullback (𝟙 U) j ι p) {a : A ⟶ U}
    {k : A ⟶ V'} (hk : k ≫ p = a ≫ ι) : k = a ≫ j := by
  have h1 := h.lift_fst a k hk.symm
  have h2 := h.lift_snd a k hk.symm
  rw [Category.comp_id] at h1
  rw [h1] at h2
  exact h2.symm

/-- **Two witnesses of the same triple are comparable.** Over a locally Noetherian `V`, for two
witnesses `V'₁ ⟶ V`, `x̂'₁`, `x'₁` and `V'₂ ⟶ V`, `x̂'₂`, `x'₂` of the compatibility of the same
triple `(Z, u', x̂)` there is a morphism `ψ : V'₁ ⟶ V'₂` over `V` with `x'₂ ∘ ψ = x'₁`.

Both `V'ᵢ ⟶ V` are proper, isomorphisms over `V ∖ Z`, with completion the pullback of `g` along
`x̂`, so the uniqueness half of Stacks 0GDU gives `ψ` compatible with the identifications of the
completions. Then `x'₂ ∘ ψ` and `x'₁` agree over `V'₁ ∖ p⁻¹ Z`, where both restrict `u'`, and on
the completion along `p⁻¹ Z`, where both are `x̂'₁`; by the uniqueness statement of Stacks 0GI1
they are equal. -/
theorem CompatibilityWitness.exists_hom {V : BigFppfOver B S hS}
    (hV : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V))
    {Z : Set (Space.points B S hS (yoneda.obj V))} (hZ : IsClosed Z)
    {u : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor}
    {xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W}
    (ω ω' : CompatibilityWitness c V Z u xhat) :
    ∃ ψ : ω.V' ⟶ ω'.V', ψ ≫ ω'.p = ω.p ∧ ψ ≫ ω'.x' = ω.x' := by
  have hVsp := isAlgebraicSpace_yoneda B S hS V
  have hVN := Space.isLocallyNoetherian_yoneda B S hS V hV
  -- the completions of both witnesses are identified with the pullback of `g` along `x̂`
  let e : ∀ w : CompatibilityWitness c V Z u xhat,
      (Space.completionOverFunctor B S hS Z).obj (Over.mk w.p) ≅
        Over.mk (Limits.pullback.fst xhat c.g) := fun w =>
    Over.isoMk w.isPullback_xhat'.isoPullback (by
      change _ ≫ Limits.pullback.fst xhat c.g = Space.completionSheafMap B S hS w.p Z
      rw [IsPullback.isoPullback_hom_fst]
      exact Space.completionSheafRestrict_self B S hS w.p Z _)
  have hU : ∀ w : CompatibilityWitness c V Z u xhat,
      IsIso (Limits.pullback.snd w.p (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι) := by
    intro w
    have h := w.isPullback_j.flip.isoPullback_hom_snd
    rw [← Iso.eq_inv_comp, Category.comp_id] at h
    rw [h]
    infer_instance
  obtain ⟨ψ, ⟨hψ, -⟩, -⟩ := FormalSpace.existsUnique_completionOverFunctor_map_comp_eq_of_isProper
    hVsp hVN Z hZ (Limits.pullback.fst xhat c.g) ω.isAlgebraicSpace_V' ω'.isAlgebraicSpace_V'
    ω.isProper_p ω'.isProper_p (hU ω) (hU ω') (e ω) (e ω')
  have hp : ψ.left ≫ ω'.p = ω.p := Over.w ψ
  refine ⟨ψ.left, hp, ?_⟩
  -- the completion of `ψ` is compatible with the two morphisms `x̂'`
  have hxhat : Space.completionOverMap B S hS Z ψ ≫ ω'.xhat' = ω.xhat' := by
    have h1 := congrArg CommaMorphism.left hψ
    have h2 := congrArg (· ≫ Limits.pullback.snd xhat c.g) h1
    simp only [Over.comp_left, Category.assoc] at h2
    exact (congrArg (Space.completionOverMap B S hS Z ψ ≫ ·)
      ω'.isPullback_xhat'.isoPullback_hom_snd.symm).trans
        (h2.trans ω.isPullback_xhat'.isoPullback_hom_snd)
  -- `ψ` restricts to the identifications of `V ∖ Z`
  have hjψ : ω.j ≫ ψ.left = ω'.j := by
    exact (eq_comp_of_isPullback_id_left ω'.isPullback_j (a := 𝟙 _)
      (by rw [Category.assoc, hp, ← ω.isPullback_j.w])).trans (Category.id_comp _)
  have hN := Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B S hS
    ω.isAlgebraicSpace_V' hVsp ω.p ω.isProper_p.2.1.1
    (FormalSpace.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyNoetherian hVsp hVN)
  refine Space.eq_of_eq_on_compl_of_eq_on_completion B S hS ω.isAlgebraicSpace_V'
    c.isAlgebraicSpace_X' hN (hZ.preimage (Space.continuous_pointsMap B S hS ω.p)) _ _ ?_ ?_
  · -- over the complement of `p⁻¹ Z` both morphisms restrict `u'`
    let r := Space.openSubspaceOfPointsRestrict B S hS ω.p
      (Space.pointsMap B S hS ω.V' ω.p ⁻¹' Z)ᶜ Zᶜ (fun _ hz => hz)
    have hr : r ≫ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι =
        (Space.openSubspaceOfPoints B S hS ω.V' (Space.pointsMap B S hS ω.V' ω.p ⁻¹' Z)ᶜ).ι ≫
          ω.p :=
      Space.openSubspaceOfPointsRestrict_comp_ι B S hS _ _ _ _
    have hrj : r ≫ ω.j =
        (Space.openSubspaceOfPoints B S hS ω.V' (Space.pointsMap B S hS ω.V' ω.p ⁻¹' Z)ᶜ).ι := by
      exact (eq_comp_of_isPullback_id_left ω.isPullback_j hr.symm).symm
    simp only [← hrj, Category.assoc]
    rw [reassoc_of% hjψ, ω'.restrict_x', ω.restrict_x']
  · -- on the completion along `p⁻¹ Z` both morphisms are `x̂'`
    refine Space.completionSubfunctor_ι_whiskerRight_eq B S hS c.isAlgebraicSpace_X' _ _ _ ?_
    have h1 : Space.completionSheafInclusion B S hS ω.V'
          (Space.pointsMap B S hS ω.V' ω.p ⁻¹' Z) ≫ Space.sheafifiedULiftMap B S hS ψ.left =
        Space.completionOverMap B S hS Z ψ ≫ Space.completionSheafInclusion B S hS ω'.V'
          (Space.pointsMap B S hS ω'.V' ω'.p ⁻¹' Z) :=
      (Space.completionOverMap_comp_inclusion B S hS Z ψ).symm
    rw [Space.sheafifiedULiftMap_comp, ← Category.assoc, h1, Category.assoc, ω'.completion_x',
      ← Category.assoc, hxhat, ω.completion_x']

/-- `AlgebraicGeometry.Artin.ContractionSituation.CompatibilityWitness.exists_hom` for witnesses
of two triples which are equal. -/
theorem CompatibilityWitness.exists_hom_of_eq {V : BigFppfOver B S hS}
    (hV : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)) {τ τ' : Triple c V}
    (h : τ = τ') (ω : CompatibilityWitness c V τ.Z τ.u τ.xhat)
    (ω' : CompatibilityWitness c V τ'.Z τ'.u τ'.xhat) :
    ∃ ψ : ω.V' ⟶ ω'.V', ψ ≫ ω'.p = ω.p ∧ ψ ≫ ω'.x' = ω.x' := by
  subst h
  exact CompatibilityWitness.exists_hom hV τ.isClosed_Z ω ω'

end ContractionSituation

namespace ContractionEqualizer

open ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {c : ContractionSituation B S hS} {V : BigFppfOver B S hS} (d : ContractionEqualizer c V)

/-- **The restricted witness maps to `E'`.** For the data of Stacks 0GHD and a morphism
`φ : A ⟶ V` from a locally Noetherian `A` along which the two triples restrict to the same
element of `F(A)`, the witness `A ×_V V'₁` of the restricted triple maps to `E'` over `V`, by a
morphism whose composite with `E' ⟶ V'₁` is the second projection.

Comparing the restricted witnesses `A ×_V V'₁` and `A ×_V V'₂` of the common restriction
(`AlgebraicGeometry.Artin.ContractionSituation.CompatibilityWitness.exists_hom_of_eq`) gives a
morphism `A ×_V V'₁ ⟶ V'₂` over `V` carrying `x'₂` to the restriction of `x'₁`, hence a
morphism to `V' = V'₁ ×_V V'₂` equalizing the two morphisms to `X'`. -/
theorem exists_toE'_of_mapTriple_eq {A : BigFppfOver B S hS}
    (hA : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj A)) (φ : A ⟶ V)
    (h : mapTriple c φ d.t₁ = mapTriple c φ d.t₂) :
    ∃ x : (d.w₁.pullback φ d.t₁).V' ⟶ d.eqz,
      x ≫ d.toBase = Limits.pullback.fst (yoneda.map φ) d.w₁.p ≫ yoneda.map φ ∧
        x ≫ d.toFst = Limits.pullback.snd (yoneda.map φ) d.w₁.p := by
  obtain ⟨ψ, hψp, hψx⟩ := CompatibilityWitness.exists_hom_of_eq hA h
    (d.w₁.pullback φ d.t₁) (d.w₂.pullback φ d.t₂)
  let ψ' : Limits.pullback (yoneda.map φ) d.w₁.p ⟶ Limits.pullback (yoneda.map φ) d.w₂.p := ψ
  have hψp' : ψ' ≫ Limits.pullback.fst (yoneda.map φ) d.w₂.p =
      Limits.pullback.fst (yoneda.map φ) d.w₁.p := hψp
  have hψx' : ψ' ≫ Limits.pullback.snd (yoneda.map φ) d.w₂.p ≫ d.w₂.x' =
      Limits.pullback.snd (yoneda.map φ) d.w₁.p ≫ d.w₁.x' := hψx
  have hcond : Limits.pullback.snd (yoneda.map φ) d.w₁.p ≫ d.w₁.p =
      (ψ' ≫ Limits.pullback.snd (yoneda.map φ) d.w₂.p) ≫ d.w₂.p :=
    calc Limits.pullback.snd (yoneda.map φ) d.w₁.p ≫ d.w₁.p
        = Limits.pullback.fst (yoneda.map φ) d.w₁.p ≫ yoneda.map φ :=
          Limits.pullback.condition.symm
      _ = (ψ' ≫ Limits.pullback.fst (yoneda.map φ) d.w₂.p) ≫ yoneda.map φ := by rw [hψp']
      _ = ψ' ≫ Limits.pullback.snd (yoneda.map φ) d.w₂.p ≫ d.w₂.p := by
          rw [Category.assoc, Limits.pullback.condition]
      _ = (ψ' ≫ Limits.pullback.snd (yoneda.map φ) d.w₂.p) ≫ d.w₂.p :=
          (Category.assoc _ _ _).symm
  let m : Limits.pullback (yoneda.map φ) d.w₁.p ⟶ d.fibProd := Limits.pullback.lift _ _ hcond
  have hm : m ≫ d.x₁ = m ≫ d.x₂ := by
    simp only [m, x₁, x₂, Limits.pullback.lift_fst_assoc, Limits.pullback.lift_snd_assoc,
      Category.assoc, hψx']
  refine ⟨(equalizer.lift m hm : Limits.pullback (yoneda.map φ) d.w₁.p ⟶ d.eqz), ?_, ?_⟩
  · change equalizer.lift m hm ≫ d.toBase = _
    rw [toBase, equalizer.lift_ι_assoc, Limits.pullback.lift_fst_assoc,
      ← Limits.pullback.condition]
  · change equalizer.lift m hm ≫ d.toFst = _
    rw [toFst, equalizer.lift_ι_assoc, Limits.pullback.lift_fst]

end ContractionEqualizer

end Artin

end AlgebraicGeometry

end
