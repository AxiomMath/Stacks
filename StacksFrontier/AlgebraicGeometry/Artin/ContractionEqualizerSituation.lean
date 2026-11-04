module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizerSmallerBase
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionLimitPreserving
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlgebraicSpaceAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalModificationBaseChangeAdic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocallyNoetherianSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ModificationOutputQuasiCompact
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTargetRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOfAffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
import StacksCore.Tactic.StacksAttribute

/-!
# The equalizer triple of Stacks 0GHD is a situation over `V`

In the situation of Stacks 0GH8, let `V` be a locally Noetherian scheme over `S` and let `d` be
the data of Stacks 0GHD over `V`: two elements `(Zᵢ, u'ᵢ, x̂ᵢ)` of `F(V)` with chosen
compatibility witnesses. This file proves assertion (4) of the remark: the triple `E'`,
`(E' ⟶ V)⁻¹ Z` and `E'_{/Z} ⟶ E_W` is a situation as in Stacks 0GH8 with base scheme `V`.

The inputs, all proved here:

* `E_W` is a locally Noetherian formal algebraic space (the sentence of the remark before the
  list): `E_W ⟶ V_{/Z}` is a base change of the diagonal of `W`, hence representable and locally
  of finite type (Stacks 0AIP), and `V_{/Z}` is locally Noetherian (Stacks 0AQ1), so Stacks 0AQ8
  applies.
* `E_W ⟶ W` is adic: `E_W` is the base change of the diagonal of `V` along
  `V_{/Z₁} ×_W V_{/Z₂} ⟶ V × V`, because `V_{/Z}` is the intersection of `V_{/Z₁}` and `V_{/Z₂}`
  inside `V`, and `V_{/Z₁} ×_W V_{/Z₂} ⟶ W` is adic as `x̂₁` and `x̂₂` are.
* `E'_{/Z} ⟶ E_W` is a formal modification: by assertion (3) it is the base change of the formal
  modification `g : X'_{/T'} ⟶ W` along the adic morphism `E_W ⟶ W`, so this is Stacks 0GDN.
* The reduction of `E_W` viewed over `V` is locally of finite type over `V`
  (`AlgebraicGeometry.Artin.ContractionEqualizer.isLocallyOfFiniteTypeULift_of_isReduction`).

## Main definitions

* `AlgebraicGeometry.Artin.ContractionEqualizer.situation`: **Stacks 0GHD (4)**, the situation of
  Stacks 0GH8 over `V`.

## Main results

* `AlgebraicGeometry.Artin.ContractionEqualizer.isLocallyNoetherian_EW`: `E_W` is a locally
  Noetherian formal algebraic space.
* `AlgebraicGeometry.Artin.ContractionEqualizer.isAdicMorphism_EW`: `E_W ⟶ W` is adic.
* `AlgebraicGeometry.Artin.ContractionEqualizer.isFormalModification_completedToEW`:
  `E'_{/Z} ⟶ E_W` is a formal modification.

## References

* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AQ1](https://stacks.math.columbia.edu/tag/0AQ1)
* [Stacks Project, Tag 0AQ8](https://stacks.math.columbia.edu/tag/0AQ8)
* [Stacks Project, Tag 0GDN](https://stacks.math.columbia.edu/tag/0GDN)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHD](https://stacks.math.columbia.edu/tag/0GHD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The presheaf represented by a locally Noetherian scheme of the big fppf site is a locally
Noetherian algebraic space: every scheme étale over it is locally Noetherian. -/
theorem isLocallyNoetherian_yoneda (V : BigFppfOver B S hS)
    (hV : _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)) :
    IsLocallyNoetherian B S hS (yoneda.obj V) := fun W q hq ↦
  (exists_atlas_iff_forall_etale B S hS _
    (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V)
    (isAlgebraicSpace_yoneda B S hS V)).mp
    ((exists_atlas_iff_of_representable B S hS _
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V) _ (Iso.refl _)).2 hV)
    W q ((isEtale_iff_presheaf_of_yoneda B S hS q).1 hq)

attribute [local instance] pointTopology

/-- **The completion along an intersection is the intersection of the completions.** The
subfunctor of sections with point-set image in `T₁ ∩ T₂` is the fibre product of the subfunctors
of sections with point-set image in `T₁` and in `T₂`, over the universe lift of `X`. -/
theorem isPullback_completionSubfunctor_inter (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T₁ T₂ : Set (points B S hS X))
    {r₁ : (completionSubfunctor B S hS X (T₁ ∩ T₂)).toFunctor ⟶
      (completionSubfunctor B S hS X T₁).toFunctor}
    {r₂ : (completionSubfunctor B S hS X (T₁ ∩ T₂)).toFunctor ⟶
      (completionSubfunctor B S hS X T₂).toFunctor}
    (h₁ : r₁ ≫ (completionSubfunctor B S hS X T₁).ι = (completionSubfunctor B S hS X (T₁ ∩ T₂)).ι)
    (h₂ : r₂ ≫ (completionSubfunctor B S hS X T₂).ι = (completionSubfunctor B S hS X (T₁ ∩ T₂)).ι) :
    IsPullback r₁ r₂ (completionSubfunctor B S hS X T₁).ι (completionSubfunctor B S hS X T₂).ι := by
  let ι₁ := (completionSubfunctor B S hS X T₁).ι
  let ι₂ := (completionSubfunctor B S hS X T₂).ι
  let ι := (completionSubfunctor B S hS X (T₁ ∩ T₂)).ι
  have hlift : ∀ s : PullbackCone ι₁ ι₂,
      Subfunctor.range (s.fst ≫ ι₁) ≤ completionSubfunctor B S hS X (T₁ ∩ T₂) := by
    rintro s U _ ⟨x, rfl⟩
    have hx₂ : (s.fst ≫ ι₁).app U x = (s.snd ≫ ι₂).app U x := by
      rw [s.condition]
    exact fun p => ⟨(s.fst.app U x).2 p, hx₂ ▸ (s.snd.app U x).2 p⟩
  let l := fun s : PullbackCone ι₁ ι₂ =>
    Subfunctor.lift (G := completionSubfunctor B S hS X (T₁ ∩ T₂)) (s.fst ≫ ι₁) (hlift s)
  have hl : ∀ s : PullbackCone ι₁ ι₂, l s ≫ ι = s.fst ≫ ι₁ := fun s => rfl
  refine ⟨⟨h₁.trans h₂.symm⟩, ⟨PullbackCone.IsLimit.mk _ l (fun s => ?_) (fun s => ?_)
    (fun s m hm₁ _ => ?_)⟩⟩
  · exact (cancel_mono ι₁).mp ((Category.assoc _ _ _).trans
      ((congrArg (l s ≫ ·) h₁).trans (hl s)))
  · exact (cancel_mono ι₂).mp ((Category.assoc _ _ _).trans
      ((congrArg (l s ≫ ·) h₂).trans ((hl s).trans s.condition)))
  · exact (cancel_mono ι).mp (((congrArg (m ≫ ·) h₁).symm.trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ι₁) hm₁))).trans (hl s).symm)

end Space

namespace FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of fppf sheaves which is representable by objects of the site, with represented
base changes locally of finite type, is locally of finite type in the sense of Stacks 0AM4. -/
theorem isLocallyOfFiniteType_of_relative {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.inverseImage (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} f.hom) :
    IsLocallyOfFiniteType B S hS f := by
  refine ⟨isRepresentableByAlgebraicSpacesULift_of_relativelyRepresentable B S hS hf.rep,
    fun U ξ => ?_⟩
  have hsq := (hf.rep.isPullback ξ).flip
  have hfst : pullback.fst ξ f.hom =
      hsq.isoPullback.inv ≫ uliftYoneda.{u + 1}.map (hf.rep.snd ξ) := by
    rw [Iso.eq_inv_comp, IsPullback.isoPullback_hom_fst]
  show Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS (pullback.fst ξ f.hom)
  rw [hfst]
  exact Space.holdsOnEveryEtaleChartULift_precomp B S hS _ _ _
    (Space.isLocallyOfFiniteTypeULift_uliftYoneda_map B S hS _ (hf.property_snd ξ))

end FormalSpace

namespace Artin.ContractionEqualizer

open FormalSpace

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {c : ContractionSituation B S hS} {V : BigFppfOver B S hS}
    (d : ContractionEqualizer c V)

/-- `V`, as a representable fppf sheaf of `Type (u + 1)`. -/
abbrev ambient : FppfSheaf B S hS := (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V

/-- The morphism `V_{/T} ⟶ V` from a completion of `V` into `V`. -/
def toAmbient (T : Set (Space.points B S hS (yoneda.obj V))) :
    Space.completionSheaf B S hS (yoneda.obj V) T ⟶ ambient (V := V) :=
  ObjectProperty.homMk (Space.completionSheafToAmbient B S hS (yoneda.obj V)
    (isSheaf_comp_uliftFunctor B S hS (isAlgebraicSpace_yoneda B S hS V)) T)

/-- The morphism `V_{/T} ⟶ V` from a completion of `V` into `V` is a monomorphism. -/
instance mono_toAmbient (T : Set (Space.points B S hS (yoneda.obj V))) :
    Mono (toAmbient (V := V) T) :=
  (sheafToPresheaf _ _).mono_of_mono_map (Space.mono_completionSheafToAmbient B S hS
    (yoneda.obj V) (isSheaf_comp_uliftFunctor B S hS (isAlgebraicSpace_yoneda B S hS V)) T)

/-- The restriction `V_{/T'} ⟶ V_{/T}` along `T' ⊆ T` is compatible with the morphisms into
`V`. -/
theorem completionSheafRestrict_comp_toAmbient (T' T : Set (Space.points B S hS (yoneda.obj V)))
    (h : T' ⊆ Space.pointsMap B S hS _ (𝟙 (yoneda.obj V)) ⁻¹' T) :
    Space.completionSheafRestrict B S hS (𝟙 _) T' T h ≫ toAmbient T = toAmbient T' := by
  let J := BigFppfOver.topology B S hS
  have hs := isSheaf_comp_uliftFunctor B S hS (isAlgebraicSpace_yoneda B S hS V)
  apply ObjectProperty.hom_ext
  refine J.sheafify_hom_ext _ _ hs ?_
  have hA : J.toSheafify (Space.completionSubfunctor B S hS (yoneda.obj V) T').toFunctor ≫
      (Space.completionSheafRestrict B S hS (𝟙 _) T' T h).hom =
      Space.completionSubfunctorRestrict B S hS (𝟙 _) T' T h ≫ J.toSheafify _ :=
    (J.toSheafify_naturality _).symm
  have hB : Space.completionSubfunctorRestrict B S hS (𝟙 _) T' T h ≫
      (Space.completionSubfunctor B S hS (yoneda.obj V) T).ι =
      (Space.completionSubfunctor B S hS (yoneda.obj V) T').ι := rfl
  have hC := Space.toSheafify_comp_completionSheafToAmbient B S hS (yoneda.obj V) hs T
  have hC' := Space.toSheafify_comp_completionSheafToAmbient B S hS (yoneda.obj V) hs T'
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hA).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) hC).trans <| hB.trans hC'.symm

/-- `Z ⊆ Z₁`, as points of `V` pulled back along the identity. -/
theorem Z_subset_preimage₁ :
    d.Z ⊆ Space.pointsMap B S hS _ (𝟙 (yoneda.obj V)) ⁻¹' d.t₁.Z := by
  simpa only [Space.pointsMap_id, Set.preimage_id] using d.Z_subset_t₁

/-- `Z ⊆ Z₂`, as points of `V` pulled back along the identity. -/
theorem Z_subset_preimage₂ :
    d.Z ⊆ Space.pointsMap B S hS _ (𝟙 (yoneda.obj V)) ⁻¹' d.t₂.Z := by
  simpa only [Space.pointsMap_id, Set.preimage_id] using d.Z_subset_t₂

/-- The restriction `V_{/Z} ⟶ V_{/Z₁}`. -/
abbrev restrict₁ : Space.completionSheaf B S hS (yoneda.obj V) d.Z ⟶
    Space.completionSheaf B S hS (yoneda.obj V) d.t₁.Z :=
  Space.completionSheafRestrict B S hS (𝟙 _) d.Z d.t₁.Z d.Z_subset_preimage₁

/-- The restriction `V_{/Z} ⟶ V_{/Z₂}`. -/
abbrev restrict₂ : Space.completionSheaf B S hS (yoneda.obj V) d.Z ⟶
    Space.completionSheaf B S hS (yoneda.obj V) d.t₂.Z :=
  Space.completionSheafRestrict B S hS (𝟙 _) d.Z d.t₂.Z d.Z_subset_preimage₂

/-- `x̂₁ : V_{/Z} ⟶ W` is the restriction `V_{/Z} ⟶ V_{/Z₁}` followed by `x̂ : V_{/Z₁} ⟶ W`. -/
theorem xhat₁_eq : d.xhat₁ = d.restrict₁ ≫ d.t₁.xhat := rfl

/-- `x̂₂ : V_{/Z} ⟶ W` is the restriction `V_{/Z} ⟶ V_{/Z₂}` followed by `x̂ : V_{/Z₂} ⟶ W`. -/
theorem xhat₂_eq : d.xhat₂ = d.restrict₂ ≫ d.t₂.xhat := rfl

/-- **`V_{/Z}` is the intersection of `V_{/Z₁}` and `V_{/Z₂}` inside `V`**, as `Z = Z₁ ∩ Z₂`. -/
theorem isPullback_restrict_toAmbient :
    IsPullback d.restrict₁ d.restrict₂ (toAmbient d.t₁.Z) (toAmbient d.t₂.Z) := by
  have hs := (isAlgebraicSpace_yoneda B S hS V).isSheaf
  let e := fun T => Space.completionSheafIsoSubfunctor B S hS hs T
  have hamb : ∀ T, (e T).inv ≫ (toAmbient (V := V) T).hom =
      (Space.completionSubfunctor B S hS (yoneda.obj V) T).ι := fun T =>
    Space.toSheafify_comp_completionSheafToAmbient B S hS (yoneda.obj V) _ T
  have hr : ∀ (T : Set (Space.points B S hS (yoneda.obj V))) (res : Space.completionSheaf B S hS
      (yoneda.obj V) d.Z ⟶ Space.completionSheaf B S hS (yoneda.obj V) T),
      res ≫ toAmbient T = toAmbient d.Z →
      ((e d.Z).inv ≫ res.hom ≫ (e T).hom) ≫
        (Space.completionSubfunctor B S hS (yoneda.obj V) T).ι =
      (Space.completionSubfunctor B S hS (yoneda.obj V) (d.t₁.Z ∩ d.t₂.Z)).ι := by
    intro T res hres
    have h1 : (e T).hom ≫ (Space.completionSubfunctor B S hS (yoneda.obj V) T).ι =
        (toAmbient (V := V) T).hom :=
      (congrArg ((e T).hom ≫ ·) (hamb T).symm).trans (Iso.hom_inv_id_assoc _ _)
    have h2 : res.hom ≫ (toAmbient (V := V) T).hom = (toAmbient (V := V) d.Z).hom :=
      congrArg (fun φ => φ.hom) hres
    exact (Category.assoc _ _ _).trans <| (congrArg ((e d.Z).inv ≫ ·)
      ((Category.assoc _ _ _).trans ((congrArg (res.hom ≫ ·) h1).trans h2))).trans (hamb d.Z)
  have hsub := Space.isPullback_completionSubfunctor_inter B S hS (yoneda.obj V) d.t₁.Z d.t₂.Z
    (hr d.t₁.Z d.restrict₁ (completionSheafRestrict_comp_toAmbient _ _ _))
    (hr d.t₂.Z d.restrict₂ (completionSheafRestrict_comp_toAmbient _ _ _))
  have hcomm : ∀ (T : Set (Space.points B S hS (yoneda.obj V))) (res : Space.completionSheaf B S hS
      (yoneda.obj V) d.Z ⟶ Space.completionSheaf B S hS (yoneda.obj V) T),
      ((e d.Z).inv ≫ res.hom ≫ (e T).hom) ≫ (e T).symm.hom = (e d.Z).symm.hom ≫ res.hom :=
    fun T res => (Category.assoc _ _ _).trans <| congrArg ((e d.Z).inv ≫ ·) <|
      (Category.assoc _ _ _).trans <| (congrArg (res.hom ≫ ·) (e T).hom_inv_id).trans
        (Category.comp_id _)
  have hpre : IsPullback d.restrict₁.hom d.restrict₂.hom (toAmbient (V := V) d.t₁.Z).hom
      (toAmbient (V := V) d.t₂.Z).hom :=
    hsub.of_iso (e d.Z).symm (e d.t₁.Z).symm (e d.t₂.Z).symm (Iso.refl _)
      (hcomm _ _) (hcomm _ _) ((Category.comp_id _).trans (hamb d.t₁.Z).symm)
      ((Category.comp_id _).trans (hamb d.t₂.Z).symm)
  exact IsPullback.of_map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (ObjectProperty.hom_ext _ hpre.w) hpre

/-- The fibre product `V_{/Z₁} ×_W V_{/Z₂}` of the two given morphisms `x̂ᵢ : V_{/Zᵢ} ⟶ W`. -/
abbrev xhatPullback : FppfSheaf B S hS := pullback d.t₁.xhat d.t₂.xhat

/-- The morphism `E_W ⟶ V_{/Z₁} ×_W V_{/Z₂}`. -/
def EWToXhatPullback : d.EW ⟶ d.xhatPullback :=
  pullback.lift (equalizer.ι d.xhat₁ d.xhat₂ ≫ d.restrict₁)
    (equalizer.ι d.xhat₁ d.xhat₂ ≫ d.restrict₂)
    ((Category.assoc _ _ _).trans ((equalizer.condition d.xhat₁ d.xhat₂).trans
      (Category.assoc _ _ _).symm))

/-- The first component of `E_W ⟶ V_{/Z₁} ×_W V_{/Z₂}` is the restriction `E_W ⟶ V_{/Z₁}`. -/
@[reassoc (attr := simp)]
theorem EWToXhatPullback_fst :
    d.EWToXhatPullback ≫ pullback.fst _ _ = equalizer.ι d.xhat₁ d.xhat₂ ≫ d.restrict₁ :=
  pullback.lift_fst _ _ _

/-- The second component of `E_W ⟶ V_{/Z₁} ×_W V_{/Z₂}` is the restriction `E_W ⟶ V_{/Z₂}`. -/
@[reassoc (attr := simp)]
theorem EWToXhatPullback_snd :
    d.EWToXhatPullback ≫ pullback.snd _ _ = equalizer.ι d.xhat₁ d.xhat₂ ≫ d.restrict₂ :=
  pullback.lift_snd _ _ _

/-- **`E_W` is a base change of the diagonal of `V`**, along
`V_{/Z₁} ×_W V_{/Z₂} ⟶ V × V`: a pair of sections of `V_{/Z₁}` and `V_{/Z₂}` with the same image
in `W` and the same image in `V` is a section of `V_{/Z₁} ∩ V_{/Z₂} = V_{/Z}` on which `x̂₁` and
`x̂₂` agree. -/
theorem isPullback_EWToXhatPullback :
    IsPullback d.EWToXhatPullback (equalizer.ι d.xhat₁ d.xhat₂ ≫ toAmbient d.Z)
      (prod.lift (pullback.fst _ _ ≫ toAmbient d.t₁.Z) (pullback.snd _ _ ≫ toAmbient d.t₂.Z))
      (diag (ambient (V := V))) := by
  have hP := d.isPullback_restrict_toAmbient
  have hra₁ : d.restrict₁ ≫ toAmbient d.t₁.Z = toAmbient d.Z :=
    completionSheafRestrict_comp_toAmbient _ _ _
  have hra₂ : d.restrict₂ ≫ toAmbient d.t₂.Z = toAmbient d.Z :=
    completionSheafRestrict_comp_toAmbient _ _ _
  have hcond : ∀ s : PullbackCone
      (prod.lift (pullback.fst d.t₁.xhat d.t₂.xhat ≫ toAmbient d.t₁.Z)
        (pullback.snd d.t₁.xhat d.t₂.xhat ≫ toAmbient d.t₂.Z)) (diag (ambient (V := V))),
      (s.fst ≫ pullback.fst _ _) ≫ toAmbient d.t₁.Z = s.snd ∧
        (s.fst ≫ pullback.snd _ _) ≫ toAmbient d.t₂.Z = s.snd := fun s =>
    ⟨by simpa using congrArg (· ≫ prod.fst) s.condition,
      by simpa using congrArg (· ≫ prod.snd) s.condition⟩
  let l := fun s : PullbackCone
      (prod.lift (pullback.fst d.t₁.xhat d.t₂.xhat ≫ toAmbient d.t₁.Z)
        (pullback.snd d.t₁.xhat d.t₂.xhat ≫ toAmbient d.t₂.Z)) (diag (ambient (V := V))) =>
    hP.lift (s.fst ≫ pullback.fst _ _) (s.fst ≫ pullback.snd _ _)
      ((hcond s).1.trans (hcond s).2.symm)
  have hl : ∀ s, l s ≫ d.xhat₁ = l s ≫ d.xhat₂ := fun s => by
    rw [xhat₁_eq, xhat₂_eq, hP.lift_fst_assoc, hP.lift_snd_assoc, Category.assoc,
      Category.assoc, pullback.condition]
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => equalizer.lift (l s) (hl s))
    (fun s => ?_) (fun s => ?_) (fun s m hm₁ _ => ?_)⟩⟩
  · apply prod.hom_ext <;> simp [hra₁, hra₂]
  · apply pullback.hom_ext <;> simp [l]
  · simp only [equalizer.lift_ι_assoc]
    rw [← hra₁, hP.lift_fst_assoc]
    exact (hcond s).1
  · apply equalizer.hom_ext
    apply hP.hom_ext <;> simp [l, ← hm₁]

/-- **`E_W ⟶ W` is adic**, that is representable by algebraic spaces: it factors as
`E_W ⟶ V_{/Z₁} ×_W V_{/Z₂} ⟶ V_{/Z₁} ⟶ W`, the first a base change of the diagonal of `V`
(Stacks 0AIP), the second a base change of the adic morphism `x̂₂` and the third the adic morphism
`x̂₁`. -/
theorem isAdicMorphism_EW :
    IsAdicMorphism B S hS (equalizer.ι d.xhat₁ d.xhat₂ ≫ d.xhat₁) := by
  let J := BigFppfOver.topology B S hS
  let L := MorphismProperty.inverseImage (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have hd := relative_locallyOfFiniteType_diag_of_isFormalAlgebraicSpace B S hS
    (isFormalAlgebraicSpace_uliftYoneda B S hS V)
  have h1 : L.relative (Sheaf.sheafifiedYoneda J) d.EWToXhatPullback :=
    (MorphismProperty.relative_isStableUnderBaseChange L).of_isPullback
      d.isPullback_EWToXhatPullback.flip hd
  have h2 : L.relative uliftYoneda.{u + 1} d.EWToXhatPullback.hom :=
    relative_of_natIso (sheafifiedYonedaPresheafIso B S hS) L _
      ((Space.relative_comp_map_iff (Sheaf.sheafifiedYoneda J) (sheafToPresheaf J (Type (u + 1)))
        L _).mpr h1)
  have hφ := isRepresentableByAlgebraicSpacesULift_of_relativelyRepresentable B S hS h2.rep
  have hfst : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (pullback.fst d.t₁.xhat d.t₂.xhat).hom :=
    Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _
      ((IsPullback.of_hasPullback d.t₁.xhat d.t₂.xhat).flip.map (sheafToPresheaf J _))
      d.t₂.adic_xhat
  have heq : equalizer.ι d.xhat₁ d.xhat₂ ≫ d.xhat₁ =
      d.EWToXhatPullback ≫ pullback.fst _ _ ≫ d.t₁.xhat := by
    rw [EWToXhatPullback_fst_assoc]
    exact congrArg (equalizer.ι d.xhat₁ d.xhat₂ ≫ ·) d.xhat₁_eq
  show Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
    (equalizer.ι d.xhat₁ d.xhat₂ ≫ d.xhat₁).hom
  rw [heq]
  exact Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _ hφ
    (Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _ hfst d.t₁.adic_xhat)

/-- **`E_W` is a locally Noetherian formal algebraic space**, half of the sentence of Stacks 0GHD
"`E_W` is a locally Noetherian formal algebraic space separated over `V`": `E_W ⟶ V_{/Z}` is
locally of finite type (a base change of the diagonal of `W`, Stacks 0AIP) and `V_{/Z}` is locally
Noetherian (Stacks 0AQ1), so this is Stacks 0AQ8. -/
@[stacks 0GHD "the sentence `E_W is a locally Noetherian formal algebraic space separated over \
V', the locally Noetherian half in full, for V a locally Noetherian scheme over S; the \
separatedness half is AlgebraicGeometry.Artin.ContractionEqualizer.isSeparatedMorphism_EW"]
theorem isLocallyNoetherian_EW (hVN : IsLocallyNoetherian V.left.obj) :
    FormalSpace.IsLocallyNoetherian B S hS d.EW :=
  isLocallyNoetherian_of_isPullback_of_isLocallyOfFiniteType B S hS
    (IsPullback.id_vert (equalizer.ι d.xhat₁ d.xhat₂))
    (isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian
      (isAlgebraicSpace_yoneda B S hS V) (Space.isLocallyNoetherian_yoneda B S hS V hVN) d.Z
      d.isClosed_Z)
    (isLocallyOfFiniteType_of_relative B S hS _ d.relative_locallyOfFiniteType_ι_EW)

/-- **`E'_{/Z} ⟶ E_W` is a formal modification**, the closing sentence of Stacks 0GHD (3): by
assertion (3) it is the base change of the formal modification `g : X'_{/T'} ⟶ W` along the
adic morphism `E_W ⟶ W` from the locally Noetherian `E_W`, so this is Stacks 0GDN. -/
@[stacks 0GHD "assertion (3), the closing sentence in full: E'_{/Z} → E_W is a formal \
modification, as the base change of g along E_W → W, for V a locally Noetherian scheme over S"]
theorem isFormalModification_completedToEW (hVN : IsLocallyNoetherian V.left.obj) :
    IsFormalModification B S hS d.completedToEW := by
  have hpb := d.isPullback_completedToSituation_completedToEW.2
  have hFM := isFormalModification_pullback_snd_of_isAdicMorphism B S hS c.g
    (equalizer.ι d.xhat₁ d.xhat₂ ≫ d.xhat₁) (d.isLocallyNoetherian_EW hVN) d.isAdicMorphism_EW
    c.isFormalModification_g
  let e := hpb.isoPullback
  have he : d.completedToEW = e.hom ≫ pullback.snd _ _ := (hpb.isoPullback_hom_snd).symm
  rw [he]
  exact isFormalModification_isIso_comp e.hom _
    (isLocallyNoetherian_of_iso B S hS e.symm hFM.isLocallyNoetherian_source)
    hFM.isLocallyNoetherian_target hFM.isProper
    (isRigEtale_comp_of_isRepresentableEtale e.hom
      (isRepresentableEtale_of_isIso B S hS e.hom) _ hFM.isRigEtale)
    hFM.isRigSurjective hFM.isRigSurjective_diagonal

/-- **Stacks 0GHD, assertion (4).** For `V` a locally Noetherian scheme over `S`, the algebraic
space `E'` with its morphism to `V`, the closed subset `(E' ⟶ V)⁻¹ Z ⊆ |E'|` and the morphism
`E'_{/Z} ⟶ E_W` form a situation as in Stacks 0GH8 with base scheme `V`: through the change of
base of Stacks 04SG they become an algebraic space `E'_V` locally of finite type over `V`
(`ContractionSituation.X'`), the closed subset `T'` of `|E'_V|` corresponding to
`(E' ⟶ V)⁻¹ Z` (`ContractionSituation.T'`), the locally Noetherian formal algebraic space `W_V`
attached to `E_W ⟶ V` (`ContractionSituation.W`) and the formal modification attached to
`E'_{/Z} ⟶ E_W` (`ContractionSituation.g`); the reduction of `W_V` is locally of finite type over
`V`. The components are recorded by `situation_space`, `situation_closedSubset`, `situation_W` and
`smallerBaseSheafFunctor_map_situation_g`. -/
@[stacks 0GHD "assertion (4), in full: E', (E' → V)⁻¹Z and E'_{/Z} → E_W form a situation as \
in Situation 0GH8 with base scheme the locally Noetherian scheme V, the objects over S lying \
over V being moved to the big fppf site of V by Stacks 04SG. The inputs are proved: E_W is a \
locally Noetherian formal algebraic space (isLocallyNoetherian_EW, by 0AIP and 0AQ8), \
E'_{/Z} → E_W is a formal modification (isFormalModification_completedToEW, by assertion (3) \
and 0GDN along the adic morphism E_W → W), and the reduction of E_W over V is locally of \
finite type over V (isLocallyOfFiniteTypeULift_of_isReduction)"]
def situation (hVN : IsLocallyNoetherian V.left.obj) :
    ContractionSituation B V.left.obj V.left.property :=
  d.relocalizedSituation hVN (d.isFormalModification_completedToEW hVN)

/-- The algebraic space of the situation of assertion (4) is `E'`, viewed over `V`. -/
theorem situation_space (hVN : IsLocallyNoetherian V.left.obj) :
    (d.situation hVN).X' = Space.smallerBaseInverse B V.left.obj S V.left.property hS V.hom
      d.E'OverV := rfl

/-- The closed subset of the situation of assertion (4) is `(E' ⟶ V)⁻¹ Z`, viewed over `V`. -/
theorem situation_closedSubset (hVN : IsLocallyNoetherian V.left.obj) :
    (d.situation hVN).T' = Space.smallerBaseInverseSet B V.left.obj S V.left.property hS V.hom
      d.E'OverV d.centerEqz := rfl

/-- The formal algebraic space of the situation of assertion (4) is `E_W`, viewed over `V`. -/
theorem situation_W (hVN : IsLocallyNoetherian V.left.obj) :
    (d.situation hVN).W = smallerBaseSheafOf B V.left.obj S V.left.property hS V.hom d.EW
      d.EWToTarget := rfl

/-- The formal modification of the situation of assertion (4) is `E'_{/Z} ⟶ E_W`, viewed over
`V`. -/
theorem smallerBaseSheafFunctor_map_situation_g (hVN : IsLocallyNoetherian V.left.obj) :
    (smallerBaseSheafFunctor B V.left.obj S V.left.property hS V.hom).map (d.situation hVN).g =
      (ContractionSituation.smallerBaseCompletionIso B V.left.obj S V.left.property hS V.hom
          d.E'OverV d.isAlgebraicSpace_eqz d.centerEqz).hom ≫ d.completedToEW ≫
        (smallerBaseSheafOfIso B V.left.obj S V.left.property hS V.hom d.EW d.EWToTarget).inv :=
  ContractionSituation.smallerBaseSheafFunctor_map_ofSmallerBase_g B V.left.obj S V.left.property
    hS V.hom hVN d.E'OverV d.isAlgebraicSpace_eqz d.isLocallyOfFiniteType_toBase d.centerEqz
    d.isClosed_centerEqz d.EW d.EWToTarget d.completedToEW d.completedToEW_comp_EWToTarget
    (d.isFormalModification_completedToEW hVN) d.isLocallyOfFiniteTypeULift_of_isReduction

end Artin.ContractionEqualizer

end AlgebraicGeometry

end
