module

public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapPicardDegree
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapBirational
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.NormalizedRepresentable
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveGeometry
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.Representability
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Abel map `γ_g` is birational

Let `X` be a geometrically irreducible smooth projective curve of genus `g` over `k` with a
rational point, `H` a scheme representing its degree-`g` Hilbert functor and `Pic^g` the degree-`g`
component of its Picard scheme. The normalized subfunctor `F ⊂ Pic_{X/k}` (fibres with
`dim H⁰ = 1` and `H¹ = 0`) is represented both by an open `W ⊂ H` ([Stacks, Tag 0B9X]) and by an
open `U ⊂ Pic^g` (it is an open subfunctor of the degree-`g` component, [Stacks, Tag 0B9V]). The
restriction of `γ_g` to `W` is the comparison `W ≅ U`, so `γ_g` is an open immersion on `W`, hence
birational, `H` and `Pic^g` being irreducible ([Stacks, Tag 0BA0], clause (6)).

## Main results

* `Stacks.AbelMap.isIso_lift_of_representableBy`: the abstract comparison of two representing
  objects of one subfunctor.
* `Stacks.AbelMap.isOpenImmersion_normalizedOpen_ι_comp_curveAbelMap`.
* `Stacks.AbelMap.isBirational_curveAbelMap`.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.AbelMap

/-- The image of a point of an open subscheme under the inclusion lies in the open. -/
private theorem opens_ι_apply_mem {X : Scheme.{u}} (U : X.Opens) (t : U) : U.ι t ∈ U := by
  have h : U.ι t ∈ Set.range U.ι := Set.mem_range_self _
  rwa [Scheme.Opens.range_ι] at h

section Abstract

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (Q F : Subfunctor G)
  {Pd W : BigFppfOver B S hS} (RQ : Q.toFunctor.RepresentableBy Pd)
  (RF : F.toFunctor.RepresentableBy W) (U : Pd.left.obj.Opens)
  (hU : ∀ {T : BigFppfOver B S hS} (m : T ⟶ Pd),
    (RQ.homEquiv m).1 ∈ F.obj (op T) ↔
      ∀ t, (BigFppfOver.toScheme B S hS).map m t ∈ U)
  (j : W ⟶ Pd) (hj : (RQ.homEquiv j).1 = (RF.homEquiv (𝟙 W)).1)

include hU hj in
/-- **Two representing objects of one subfunctor are identified.** If `Q` is represented by `Pd`,
`F` is represented by `W`, the points of `Pd` classifying points in `F` are those landing in an
open `U ⊆ Pd`, and `j : W ⟶ Pd` classifies the universal point of `F`, then `j` is an isomorphism
`W ≅ U` followed by the inclusion of `U`. -/
theorem exists_isIso_comp_openSubHom :
    ∃ a : W ⟶ BigFppfOver.openSubObj B S hS Pd U,
      IsIso a ∧ a ≫ BigFppfOver.openSubHom B S hS Pd U = j := by
  have hjU : Set.range ⇑((BigFppfOver.toScheme B S hS).map j) ⊆ (U : Set Pd.left.obj) := by
    rintro _ ⟨t, rfl⟩
    exact (hU j).1 (hj ▸ (RF.homEquiv (𝟙 W)).2) t
  let ιU := BigFppfOver.openSubHom B S hS Pd U
  let a := AlgebraicGeometry.Space.openSubObjLift B S hS Pd U j hjU
  have ha : a ≫ ιU = j := AlgebraicGeometry.Space.openSubObjLift_comp_openSubHom B S hS Pd U j hjU
  have hιU : (RQ.homEquiv ιU).1 ∈ F.obj (op (BigFppfOver.openSubObj B S hS Pd U)) := by
    refine (hU ιU).2 fun t => ?_
    rw [AlgebraicGeometry.Space.openSubHom_toScheme]
    exact opens_ι_apply_mem U t
  let b : BigFppfOver.openSubObj B S hS Pd U ⟶ W := RF.homEquiv.symm ⟨_, hιU⟩
  have hb : (RF.homEquiv b).1 = (RQ.homEquiv ιU).1 :=
    congrArg Subtype.val (RF.homEquiv.apply_symm_apply ⟨_, hιU⟩)
  have hmono : Mono ιU := AlgebraicGeometry.Space.mono_openSubHom B S hS Pd U
  have h1 : b ≫ a = 𝟙 _ := by
    rw [← cancel_mono ιU, Category.assoc, ha, Category.id_comp]
    apply RQ.homEquiv.injective
    apply Subtype.ext
    rw [RQ.homEquiv_comp, ← hb]
    change G.map b.op (RQ.homEquiv j).1 = _
    rw [hj, ← Category.comp_id b, RF.homEquiv_comp]
    rfl
  have h2 : a ≫ b = 𝟙 _ := by
    apply RF.homEquiv.injective
    apply Subtype.ext
    rw [RF.homEquiv_comp]
    change G.map a.op (RF.homEquiv b).1 = _
    rw [hb, ← hj, ← ha]
    rw [RQ.homEquiv_comp]
    rfl
  exact ⟨a, ⟨b, h2, h1⟩, ha⟩

end Abstract

/-- The form of `Stacks.AbelMap.exists_isIso_comp_openSubHom` for a represented presheaf rather
than a represented subfunctor. -/
theorem exists_isIso_comp_openSubHom' {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (F : Subfunctor G)
    {P W : BigFppfOver B S hS} (RG : G.RepresentableBy P)
    (RF : F.toFunctor.RepresentableBy W) (U : P.left.obj.Opens)
    (hU : ∀ {T : BigFppfOver B S hS} (m : T ⟶ P),
      RG.homEquiv m ∈ F.obj (op T) ↔ ∀ t, (BigFppfOver.toScheme B S hS).map m t ∈ U)
    (j : W ⟶ P) (hj : RG.homEquiv j = (RF.homEquiv (𝟙 W)).1) :
    ∃ a : W ⟶ BigFppfOver.openSubObj B S hS P U,
      IsIso a ∧ a ≫ BigFppfOver.openSubHom B S hS P U = j := by
  let RQ : (⊤ : Subfunctor G).toFunctor.RepresentableBy P :=
    { homEquiv := RG.homEquiv.trans
        { toFun := fun z => ⟨z, trivial⟩, invFun := fun z => z.1,
          left_inv := fun _ => rfl, right_inv := fun _ => rfl }
      homEquiv_comp := fun g a => Subtype.ext (RG.homEquiv_comp g a) }
  exact exists_isIso_comp_openSubHom ⊤ F RQ RF U hU j hj

section Curve

open Stacks.PicardFunctor Stacks.PicardCurve

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  [(picardFunctor B hX hk f).IsRepresentable]
  (H : BigFppfOver B (Spec (.of k)) hk)
  (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map f))
    (Over.mk (B.inclusion.map H.hom)) (genus (B.inclusion.map f)))

/-- **`γ_g` is an open immersion on the open `W ⊂ Hilb^g_{X/k}` of [Stacks, Tag 0B9X].** -/
theorem isOpenImmersion_normalizedOpen_ι_comp_curveAbelMap :
    IsOpenImmersion ((normalizedOpen B hX hk f σ hσ H hH).ι ≫
      B.inclusion.map (curveAbelMap B hX hk f σ hσ H hH).left) := by
  have := isSeparated_of_isCurve B hX hk f
  have := isNoetherian_of_isCurve B hX hk f
  let d : ℤ := (genus (B.inclusion.map f) : ℕ)
  let Q := degreeSubfunctor B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) d
  let RQ := degreeComponentRepresentableBy B hX hk f σ hσ d
  let F := curveNormalized B hX hk f σ hσ
  let RF := normalizedRepresentableBy B hX hk f σ hσ H hH
  let Pd := picardSchemeDegreeComponent B hX hk f σ hσ d
  let ξ := (RQ.homEquiv (𝟙 Pd)).1
  let U := normalizedLocus B hX hk f σ hσ (isIso_c_of_isCurve B hX hk f σ hσ)
    (topologicalKrullDim_le_one_of_isCurve B hX hk f) Pd ξ
  let j := BigFppfOver.openSubHom B _ hk H (normalizedOpen B hX hk f σ hσ H hH) ≫
    curveAbelMap B hX hk f σ hσ H hH
  have hU : ∀ {T : BigFppfOver B (Spec (.of k)) hk} (m : T ⟶ Pd),
      (RQ.homEquiv m).1 ∈ F.obj (op T) ↔
        ∀ t, (BigFppfOver.toScheme B (Spec (.of k)) hk).map m t ∈ U := by
    intro T m
    have e : (RQ.homEquiv m).1 = (picardFunctor B hX hk f).map m.op ξ := by
      rw [← Category.comp_id m, RQ.homEquiv_comp]
      rfl
    rw [e]
    exact map_mem_normalizedSubfunctor_iff B hX hk f σ hσ (isIso_c_of_isCurve B hX hk f σ hσ)
      (topologicalKrullDim_le_one_of_isCurve B hX hk f) m ξ
  have hj : (RQ.homEquiv j).1 = (RF.homEquiv (𝟙 _)).1 := by
    have h := homEquiv_comp_abelMap B hX hk f
      (isDegreeComponent_degreeSubfunctor B hX hk f σ hσ d) H hH RQ
      (BigFppfOver.openSubHom B _ hk H (normalizedOpen B hX hk f σ hσ H hH))
    refine (congrArg Subtype.val h).trans ?_
    change familyClass B hX hk f _ _ = (picardFunctor B hX hk f).map
      (𝟙 _ ≫ BigFppfOver.openSubHom B _ hk H _).op (universalClass B hX hk f H hH)
    rw [Category.id_comp]
    exact familyClass_family B hX hk f H hH _
  obtain ⟨a, ha, haj⟩ := exists_isIso_comp_openSubHom Q F RQ RF U hU j hj
  have e : (normalizedOpen B hX hk f σ hσ H hH).ι ≫
      B.inclusion.map (curveAbelMap B hX hk f σ hσ H hH).left =
        (BigFppfOver.toScheme B _ hk).map a ≫ U.ι := by
    have h := congrArg (BigFppfOver.toScheme B _ hk).map haj
    rw [Functor.map_comp, Functor.map_comp, AlgebraicGeometry.Space.openSubHom_toScheme,
      AlgebraicGeometry.Space.openSubHom_toScheme] at h
    exact h.symm
  rw [e]
  infer_instance

/-- **`γ_g` is birational, granted a normalized point.** If the open `W ⊂ Hilb^g_{X/k}` of
[Stacks, Tag 0B9X] is nonempty, then `γ_g : Hilb^g_{X/k} ⟶ Pic^g_{X/k}` is birational: it is an
open immersion on `W`, `Hilb^g_{X/k}` is a variety, and `Pic^g_{X/k}` is irreducible as the image
of `γ_g` ([Stacks, Tag 0BA0], clause (5)). -/
theorem isBirational_curveAbelMap_of_nonempty
    (hW : ((normalizedOpen B hX hk f σ hσ H hH : Set H.left.obj)).Nonempty) :
    IsBirational (B.inclusion.map (curveAbelMap B hX hk f σ hσ H hH).left) := by
  have hgeo := (Stacks.Hilbert.Curve.hilbertScheme_geometry (B.inclusion.map f)
    (genus (B.inclusion.map f))).2 _ hH
  have : IsVariety k (Over.mk (B.inclusion.map H.hom)).hom := hgeo.2.2.1
  have : IsIntegral (B.inclusion.obj H.left) := this.toIsIntegral
  have : IrreducibleSpace (B.inclusion.obj
      (picardSchemeDegreeComponent B hX hk f σ hσ (genus (B.inclusion.map f) : ℕ)).left) :=
    Function.Surjective.irreducibleSpace
      (B.inclusion.map (curveAbelMap B hX hk f σ hσ H hH).left).continuous
      (surjective_curveAbelMap B hX hk f σ hσ H hH le_rfl).surj
  obtain ⟨w, hw⟩ := hW
  have : Nonempty (normalizedOpen B hX hk f σ hσ H hH) := ⟨⟨w, hw⟩⟩
  have := isOpenImmersion_normalizedOpen_ι_comp_curveAbelMap B hX hk f σ hσ H hH
  exact AlgebraicGeometry.isBirational_of_isOpenImmersion_ι_comp _
    (normalizedOpen B hX hk f σ hσ H hH)

omit [(picardFunctor B hX hk f).IsRepresentable] in
include σ hσ in
/-- **The open `W ⊂ Hilb^g_{X/k}` of [Stacks, Tag 0B9X] is nonempty**, given the conclusion of
[Stacks, Tag 0B9Y]: some translate of the trivial class over `Spec k` is normalized, and the point
of `Hilb^g_{X/k}` it classifies lies in `W`. -/
theorem nonempty_normalizedOpen (htw : TwistToNormalized B hX hk f) :
    ((normalizedOpen B hX hk f σ hσ H hH : Set H.left.obj)).Nonempty := by
  let T := baseObj B hk
  obtain ⟨t⟩ : Nonempty ((BigFppfOver.toScheme B _ hk).obj T) :=
    inferInstanceAs (Nonempty (Spec (.of k)))
  obtain ⟨g, hg⟩ := exists_translate_mem_curveNormalizedLocus B hX hk f σ hσ htw T 0 t
  have hsub : Subsingleton ((BigFppfOver.toScheme B _ hk).obj T) :=
    inferInstanceAs (Subsingleton (Spec (.of k)))
  have hmem : (translate B hX hk f g).hom.app (op T) 0 ∈
      (curveNormalized B hX hk f σ hσ).obj (op T) := fun t' => by
    rwa [Subsingleton.elim t' t]
  let m := (normalizedRepresentableBy B hX hk f σ hσ H hH).homEquiv.symm ⟨_, hmem⟩
  refine ⟨(normalizedOpen B hX hk f σ hσ H hH).ι ((BigFppfOver.toScheme B _ hk).map m t), ?_⟩
  exact opens_ι_apply_mem _ _

include σ hσ in
/-- **`γ_g` is birational** ([Stacks, Tag 0BA0], clause (6)), given the conclusion of
[Stacks, Tag 0B9Y]. -/
theorem isBirational_curveAbelMap_of_twistToNormalized (htw : TwistToNormalized B hX hk f) :
    IsBirational (B.inclusion.map (curveAbelMap B hX hk f σ hσ H hH).left) :=
  isBirational_curveAbelMap_of_nonempty B hX hk f σ hσ H hH
    (nonempty_normalizedOpen B hX hk f σ hσ H hH htw)

end Curve

section LocallyFiniteType

open Stacks.PicardFunctor Stacks.PicardCurve

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  [(picardFunctor B hX hk f).IsRepresentable]

include σ hσ in
/-- **The Picard scheme is covered by copies of the open `W ⊂ Hilb^g_{X/k}` of
[Stacks, Tag 0B9X]**: the translates, by `k`-points, of the open of normalized classes. -/
theorem exists_cover_iso_normalizedOpen (htw : TwistToNormalized B hX hk f)
    (H : BigFppfOver B (Spec (.of k)) hk)
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map f))
      (Over.mk (B.inclusion.map H.hom)) (genus (B.inclusion.map f))) :
    ∃ U : (picardFunctor B hX hk f).obj (op (baseObj B hk)) →
        (picardSchemeOver B hX hk f).left.obj.Opens, iSup U = ⊤ ∧
      ∀ g, ∃ e : ((normalizedOpen B hX hk f σ hσ H hH : Scheme.{u})) ≅ (U g : Scheme.{u}),
        e.hom ≫ (U g).ι ≫ B.inclusion.map (picardSchemeOver B hX hk f).hom =
          (normalizedOpen B hX hk f σ hσ H hH).ι ≫ B.inclusion.map H.hom := by
  have := isSeparated_of_isCurve B hX hk f
  have := isNoetherian_of_isCurve B hX hk f
  let hOiso := isIso_c_of_isCurve B hX hk f σ hσ
  let hdim := topologicalKrullDim_le_one_of_isCurve B hX hk f
  let P := picardSchemeOver B hX hk f
  let RG := (picardFunctor B hX hk f).representableBy
  let ξ := universalPoint B hX hk f
  let Ug : (picardFunctor B hX hk f).obj (op (baseObj B hk)) → P.left.obj.Opens := fun g =>
    normalizedLocus B hX hk f σ hσ hOiso hdim P ((translate B hX hk f g).hom.app (op P) ξ)
  refine ⟨Ug, eq_top_iff.2 fun p _ => ?_, fun g => ?_⟩
  · obtain ⟨g, hg⟩ := exists_translate_mem_curveNormalizedLocus B hX hk f σ hσ htw P ξ p
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨g, hg⟩
  let RF := Subfunctor.preimageIsoRepresentableBy _ (translate B hX hk f g)
    (normalizedRepresentableBy B hX hk f σ hσ H hH)
  have hU : ∀ {T : BigFppfOver B (Spec (.of k)) hk} (m : T ⟶ P),
      RG.homEquiv m ∈ (translateSubfunctor B hX hk f σ hσ hOiso g).obj (op T) ↔
        ∀ t, (BigFppfOver.toScheme B (Spec (.of k)) hk).map m t ∈ Ug g := by
    intro T m
    rw [show RG.homEquiv m = (picardFunctor B hX hk f).map m.op ξ from
      picardHomEquiv_eq_map B hX hk f m]
    exact map_mem_translateSubfunctor_iff B hX hk f σ hσ hOiso hdim g m ξ
  obtain ⟨a, ha, -⟩ := exists_isIso_comp_openSubHom' _ RG RF (Ug g) hU
    (RG.homEquiv.symm (RF.homEquiv (𝟙 _)).1) (RG.homEquiv.apply_symm_apply _)
  exact ⟨asIso ((BigFppfOver.toScheme B _ hk).map a),
    congrArg (fun z => B.inclusion.map z) (Over.w a)⟩

include σ hσ in
/-- **The Picard scheme of the curve is locally of finite type over `k`**. -/
@[sga "6 XIII 3.2" "(i)"]
theorem locallyOfFiniteType_picardScheme (htw : TwistToNormalized B hX hk f) :
    LocallyOfFiniteType (B.inclusion.map (picardSchemeOver B hX hk f).hom) := by
  obtain ⟨H, ⟨hH⟩⟩ := exists_hilbertScheme B hX hk f
  have hHsm : Smooth (Over.mk (B.inclusion.map H.hom)).hom :=
    ((Stacks.Hilbert.Curve.hilbertScheme_geometry (B.inclusion.map f) _).2 _ hH).1
  have : LocallyOfFiniteType (B.inclusion.map H.hom) := by
    have : Smooth (B.inclusion.map H.hom) := hHsm
    infer_instance
  have _ : IsZariskiLocalAtSource (@LocallyOfFiniteType) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
  obtain ⟨U, hU, he⟩ := exists_cover_iso_normalizedOpen B hX hk f σ hσ htw H hH
  refine IsZariskiLocalAtSource.of_iSup_eq_top U hU fun g => ?_
  obtain ⟨e, he⟩ := he g
  rw [e.eq_inv_comp.2 he]
  infer_instance

include σ hσ in
/-- **The Picard scheme of the curve is smooth of relative dimension `g` over `k`**: it is covered
by copies of an open of `Hilb^g_{X/k}`, which is smooth of relative dimension `g`. -/
theorem smoothOfRelativeDimension_picardScheme (htw : TwistToNormalized B hX hk f) :
    SmoothOfRelativeDimension (genus (B.inclusion.map f))
      (B.inclusion.map (picardSchemeOver B hX hk f).hom) := by
  obtain ⟨H, ⟨hH⟩⟩ := exists_hilbertScheme B hX hk f
  have : SmoothOfRelativeDimension (genus (B.inclusion.map f)) (B.inclusion.map H.hom) :=
    Stacks.Hilbert.Curve.smoothOfRelativeDimension_of_represents (B.inclusion.map f) _ _ hH
  have _ : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (genus (B.inclusion.map f))) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @SmoothOfRelativeDimension (genus (B.inclusion.map f)))
  obtain ⟨U, hU, he⟩ := exists_cover_iso_normalizedOpen B hX hk f σ hσ htw H hH
  refine IsZariskiLocalAtSource.of_iSup_eq_top U hU fun g => ?_
  obtain ⟨e, he⟩ := he g
  rw [e.eq_inv_comp.2 he]
  have h1 := smoothOfRelativeDimension_comp (n := 0) (m := genus (B.inclusion.map f))
    (normalizedOpen B hX hk f σ hσ H hH).ι (B.inclusion.map H.hom)
  have h2 := smoothOfRelativeDimension_comp (n := 0) (m := 0 + genus (B.inclusion.map f)) e.inv
    ((normalizedOpen B hX hk f σ hσ H hH).ι ≫ B.inclusion.map H.hom)
  simpa using h2

include σ hσ in
/-- **`Pic^d_{X/k}` is locally of finite type over `k`.** -/
theorem locallyOfFiniteType_picardDegreeComponent (htw : TwistToNormalized B hX hk f) (d : ℤ) :
    LocallyOfFiniteType (B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ d).hom) := by
  have := locallyOfFiniteType_picardScheme B hX hk f σ hσ htw
  change LocallyOfFiniteType (B.inclusion.map
    (degreeLocusHom B hX hk f σ hσ d ≫ (picardSchemeOver B hX hk f).hom))
  rw [Functor.map_comp, inclusion_map_degreeLocusHom]
  infer_instance

end LocallyFiniteType

end Stacks.AbelMap

end
