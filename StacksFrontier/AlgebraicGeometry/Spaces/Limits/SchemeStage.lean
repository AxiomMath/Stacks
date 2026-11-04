module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableFilteredApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStageDescentChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NonemptyLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
import all StacksFrontier.AlgebraicGeometry.Spaces.OverFields.PurelyTranscendentalDescent

/-!
# A limit which is a scheme has a stage which is a scheme

In the situation of Stacks 084R — a directed inverse system of quasi-compact and
quasi-separated algebraic spaces over `S` with affine transition morphisms — if the limit is
a scheme then some stage is a scheme (Stacks 07SR).

## Main results

* `AlgebraicGeometry.Space.DescentSituation.exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq`:
  Stacks 0827 read on the chosen limit cone of a descent situation, the bridge between the
  form `AlgebraicGeometry.Space.exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq` of that
  tag (stated on `limit D`) and the descent situations Stacks 07SQ is stated on.
* `AlgebraicGeometry.Space.DescentSituation.exists_base_le_isRepresentable_system_obj`:
  Stacks 07SR for an index set below the cofinality of the site's size cutoff. It is not
  registered under the tag, the source's statement having no bound on the index.

## Implementation notes

The proof is the source's. Cover the limit `X` by affine opens `W`. By Stacks 0827 each `W` is
the inverse image of a quasi-compact open subspace `V` of a stage `X_i`, and by Stacks 07SQ,
applied to the system of inverse images of `V` in the later stages, some inverse image `V_j` is
affine. So every point of `X` maps, at some stage `j`, into the largest open subspace of `X_j`
which is a scheme, `AlgebraicGeometry.Space.schematicLocus` (Stacks 03JH). These loci increase
along the system, because the inverse image of a scheme along an affine morphism is a scheme.

The source then says "this means `X_i` is a scheme"; what is used there is that the inverse
images `W_{j,i}` cover `X_i` for `i` large. Here that step is made explicit: the reduced closed
complements `Z_i` of the schematic loci (Stacks 03IQ) form an inverse system with affine
transition morphisms (Stacks 03JJ), and if none of them were empty its limit would have a point
by Stacks 086W; that point gives a point of `X` lying outside every schematic locus, which is
impossible. So some schematic locus is everything, and that stage is a scheme.

*The size hypothesis.* The index set is assumed smaller than the cofinality of the site's size
cutoff. This is the standing form of the tags of this section in this development (Stacks 0827,
086V, 086W and 0CUJ carry it), and Stacks 07SQ, which the proof uses, is false without a bound
of this kind: `Stacks.Refute07SQ.not_statement07SQ` exhibits a descent situation over an index as
large as the cutoff whose limit is affine and none of whose stages is affine. For a directed set
the bound gives `AlgebraicGeometry.Space.ChartsBounded`, the hypothesis of
`AlgebraicGeometry.Space.hasAffineStageDescent_of_chartsBounded`, by
`AlgebraicGeometry.Space.chartsBounded_of_lt_cof_ord`.

## References

* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 0827](https://stacks.math.columbia.edu/tag/0827)
* [Stacks Project, Tag 086W](https://stacks.math.columbia.edu/tag/086W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace Stacks.SchemeStage

/-- The size hypotheses of Stacks 07SF for the opposite of a directed set below the
cofinality of the site's size cutoff. -/
private theorem size_op {B : BigFppfSite.{u}} {I : Type u} [Preorder I]
    (hI : #I < B.cutoff.ord.cof) :
    #(Iᵒᵖ) < B.cutoff.ord.cof ∧ ∀ a b : Iᵒᵖ, #(a ⟶ b) < B.cutoff.ord.cof := by
  refine ⟨?_, fun a b => ?_⟩
  · rw [← Cardinal.mk_congr (Opposite.equivToOpposite (α := I))]; exact hI
  · have h1 : #(a ⟶ b) ≤ 1 := by rw [Cardinal.le_one_iff_subsingleton]; infer_instance
    exact h1.trans_lt (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof)

end Stacks.SchemeStage

namespace AlgebraicGeometry.Space.DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})}

/-- **Stacks 0827, on a descent situation.** In the situation of Stacks 084R, with the index set
smaller than the cofinality of the site's size cutoff, every quasi-compact open subspace of the
limit is the inverse image of a quasi-compact open subspace of some stage under the projection
of the chosen limit cone.

This is `AlgebraicGeometry.Space.exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq`, which
is stated on the limit `limit D` chosen by the category, transported to the chosen limit cone
`D.limitCone` along the comparison isomorphism. -/
theorem exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I) (hI : #I < B.cutoff.ord.cof)
    (U : Subfunctor D.limitCone.pt) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor) :
    ∃ (i : I) (V : Subfunctor (D.system.obj (Opposite.op i))), IsOpenSubspace B S hS V ∧
      IsQuasiCompactSpace B S hS V.toFunctor ∧
        V.preimage (D.limitCone.π.app (Opposite.op i)) = U := by
  have : Nonempty I := ⟨D.base⟩
  obtain ⟨hSizeOp, hHomSizeOp⟩ := Stacks.SchemeStage.size_op (B := B) hI
  have hAffineOp : ∀ {a b : Iᵒᵖ} (g : a ⟶ b), IsAffineHom B S hS (D.system.map g) :=
    fun g => D.transition_affine g
  let e := D.isLimit.conePointUniqueUpToIso (limit.isLimit D.system)
  have he (a) : e.hom ≫ limit.π D.system a = D.limitCone.π.app a :=
    D.isLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit D.system) a
  have hlim : IsAlgebraicSpace B S hS (limit D.system) :=
    isAlgebraicSpace_of_iso B S hS e D.limitAlgebraicSpace
  let U' := U.preimage e.inv
  have hU' : IsOpenSubspace B S hS U' :=
    isOpenSubspace_preimage B S hS e.inv U D.limitAlgebraicSpace hlim hU
  have hpb := Subfunctor.isPullback_fromPreimage U e.inv
  have : IsIso (U.fromPreimage e.inv) := hpb.isIso_fst_of_isIso
  have hU'qc : IsQuasiCompactSpace B S hS U'.toFunctor :=
    isQuasiCompactSpace_of_iso B S hS (asIso (U.fromPreimage e.inv)).symm hUqc
  obtain ⟨a, V, hV, hVqc, hVpre⟩ :=
    Space.exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq B S hS D.system hSizeOp
      hHomSizeOp (fun a => D.algebraicSpace a.unop) hAffineOp U' hU' hU'qc
  refine ⟨a.unop, V, hV, hVqc, ?_⟩
  rw [← he, Subfunctor.preimage_comp, hVpre, ← Subfunctor.preimage_comp, e.hom_inv_id,
    Subfunctor.preimage_id]

end AlgebraicGeometry.Space.DescentSituation

namespace Stacks.SchemeStage

attribute [local instance] AlgebraicGeometry.Space.pointTopology

private noncomputable def affineOpenObject
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicGeometry.BigFppfOver B S hS)
    (U : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj X).Opens) :
    AlgebraicGeometry.BigFppfOver B S hS := by
  let Vsite : B.Schemes :=
    ⟨U.toScheme, (Scheme.size_coe_opens_le _ U).trans_lt X.left.2⟩
  let i : Vsite ⟶ X.left := ObjectProperty.homMk (Scheme.Opens.ι U)
  exact Over.mk (i ≫ X.hom)

private noncomputable def affineOpenInclusion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicGeometry.BigFppfOver B S hS)
    (U : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj X).Opens) :
    affineOpenObject B S hS X U ⟶ X := by
  let Vsite : B.Schemes :=
    ⟨U.toScheme, (Scheme.size_coe_opens_le _ U).trans_lt X.left.2⟩
  let i : Vsite ⟶ X.left := ObjectProperty.homMk (Scheme.Opens.ι U)
  exact Over.homMk i (by simp [affineOpenObject, Vsite, i])

private theorem affineOpenInclusion_mono
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicGeometry.BigFppfOver B S hS)
    (U : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj X).Opens) :
  Mono (affineOpenInclusion B S hS X U) := by
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hm : Mono (G.map (affineOpenInclusion B S hS X U)) := by
    show Mono (Scheme.Opens.ι U)
    let : Mono (Scheme.Opens.ι U) := inferInstance
    infer_instance
  exact G.mono_of_mono_map hm

attribute [local instance]
  AlgebraicGeometry.Space.ReasonableApproximation.schemeCutoff_isClosedUnderIsomorphisms
  Space.ReasonableApproximation.schemeCutoff_isClosedUnderLimitsOfShape_walkingCospan
  AlgebraicGeometry.Space.ReasonableApproximation.schemeCutoff_hasPullbacks

private local instance preservesPullbacks_bigFppfOverToScheme
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    PreservesLimitsOfShape WalkingCospan (AlgebraicGeometry.BigFppfOver.toScheme B S hS) := by
  apply comp_preservesLimitsOfShape

private theorem isOpenImmersion_yonedaMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.BigFppfOver B S hS} (f : X ⟶ Y)
    (hf : IsOpenImmersion f.left.hom) :
    AlgebraicGeometry.Space.IsOpenImmersion B S hS (yoneda.map f) := by
  let P := MorphismProperty.inverseImage
    (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.IsStableUnderBaseChange := ⟨fun h hq =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsOpenImmersion.{u})
      (h.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)) hq⟩
  exact MorphismProperty.relative_map (P := P) hf

private theorem isOpenSubspace_range_of_open
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : A ⟶ F) [Mono p] (hA : AlgebraicGeometry.IsAlgebraicSpace B S hS A)
    (hp : AlgebraicGeometry.Space.IsOpenImmersion B S hS p) :
    AlgebraicGeometry.Space.IsOpenSubspace B S hS (Subfunctor.range p) := by
  let e := asIso (Subfunctor.toRange p)
  refine ⟨AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS e.symm hA, ?_⟩
  let Q := MorphismProperty.presheaf
    (MorphismProperty.inverseImage (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))
  have hp' : Q (e.hom ≫ (Subfunctor.range p).ι) := (Subfunctor.toRange_ι p).symm ▸ hp
  let : Q.RespectsIso := inferInstance
  simpa only [← Category.assoc, e.inv_hom_id, Category.id_comp] using
    MorphismProperty.RespectsIso.precomp Q e.inv (e.hom ≫ (Subfunctor.range p).ι) hp'

private theorem isRepresentable_of_isAffineHom
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (hf : AlgebraicGeometry.Space.IsAffineHom B S hS f) [G.IsRepresentable] :
    F.IsRepresentable := by
  have hr₀ : yoneda.relativelyRepresentable f ∧
      (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f :=
    ((AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace B S hS f hF hG).out 2 1).mp hf
  have hr := hr₀.1
  have hp := hr.isPullback G.reprW.hom
  have : IsIso (hr.fst G.reprW.hom) := hp.isIso_fst_of_isIso
  exact Functor.IsRepresentable.mk' (asIso (hr.fst G.reprW.hom))

private theorem preimage_schematicLocus_le
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (hf : AlgebraicGeometry.Space.IsAffineHom B S hS f) :
    (AlgebraicGeometry.Space.schematicLocus B S hS G).preimage f ≤
      AlgebraicGeometry.Space.schematicLocus B S hS F := by
  let U := AlgebraicGeometry.Space.schematicLocus B S hS G
  have hU :=
    (Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hG).1
  have hV := AlgebraicGeometry.Space.isOpenSubspace_preimage B S hS f U hG hF hU
  have : U.toFunctor.IsRepresentable :=
    (Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hG).2
  exact AlgebraicGeometry.Space.le_schematicLocus B S hS F (U.preimage f) hV
    (isRepresentable_of_isAffineHom B S hS (U.fromPreimage f) hV.1 hU.1
      (AlgebraicGeometry.Space.isAffineHom_of_isPullback
        (Subfunctor.isPullback_fromPreimage U f).flip hf))

private noncomputable def affineOpenSubspace
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    [F.IsRepresentable] (e : yoneda.obj F.reprX ≅ F)
    (U : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      F.reprX).affineOpens) : Subfunctor F :=
  Subfunctor.range (yoneda.map (affineOpenInclusion B S hS F.reprX U) ≫ e.hom)

private noncomputable def affineOpenSubspaceIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    [F.IsRepresentable]
    (U : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj F.reprX).affineOpens) :
    yoneda.obj (affineOpenObject B S hS F.reprX U) ≅
      (affineOpenSubspace B S hS F.reprW U).toFunctor := by
  let j := affineOpenInclusion B S hS F.reprX U
  let p := yoneda.map j ≫ F.reprW.hom
  letI : Mono j := affineOpenInclusion_mono B S hS F.reprX U
  letI : Mono (yoneda.map j) := inferInstance
  letI : Mono p := inferInstance
  change yoneda.obj (affineOpenObject B S hS F.reprX U) ≅ (Subfunctor.range p).toFunctor
  exact asIso (Subfunctor.toRange p)

private theorem affineOpenSubspace_isOpen
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    [hX : F.IsRepresentable]
    (U : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj F.reprX).affineOpens) :
    AlgebraicGeometry.Space.IsOpenSubspace B S hS
      (affineOpenSubspace B S hS F.reprW U) := by
  let A := yoneda.obj (affineOpenObject B S hS F.reprX U)
  let j := affineOpenInclusion B S hS F.reprX U
  let p : A ⟶ F := yoneda.map j ≫ F.reprW.hom
  let : Mono j := affineOpenInclusion_mono B S hS F.reprX U
  let : Mono (yoneda.map j) := inferInstance
  let : Mono p := inferInstance
  have hA : AlgebraicGeometry.IsAlgebraicSpace B S hS A :=
    AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (affineOpenObject B S hS F.reprX U)
  have hj : AlgebraicGeometry.Space.IsOpenImmersion B S hS (yoneda.map j) := by
    apply isOpenImmersion_yonedaMap
    exact Scheme.Opens.instIsOpenImmersionι U.1
  have hp : AlgebraicGeometry.Space.IsOpenImmersion B S hS p := by
    let Q := MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS))
    let : Q.RespectsIso := inferInstance
    exact MorphismProperty.RespectsIso.postcomp Q F.reprW.hom (yoneda.map j) hj
  simpa [affineOpenSubspace, A, j, p, Subfunctor.range] using
    isOpenSubspace_range_of_open B S hS p hA hp

private theorem affineOpenSubspace_isQuasiCompact
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    [F.IsRepresentable]
    (U : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj F.reprX).affineOpens) :
    AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS
      (affineOpenSubspace B S hS F.reprW U).toFunctor := by
  let T := affineOpenObject B S hS F.reprX U
  let A := yoneda.obj T
  let e := affineOpenSubspaceIso B S hS U
  let : IsIso e.hom := e.isIso_hom
  refine ⟨T, e.hom, ?_, ?_, ?_⟩
  · let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T) := by
      dsimp [T, affineOpenObject]
      infer_instance
    infer_instance
  · refine ⟨Functor.relativelyRepresentable.of_isIso yoneda e.hom, ?_⟩
    intro V W g fst snd h
    let : IsIso (yoneda.map snd) := h.isIso_snd_of_isIso e.isIso_hom
    let : IsIso snd := isIso_of_fully_faithful yoneda snd
    let : IsIso ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map snd) :=
      Functor.map_isIso _ snd
    show Surjective ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map snd)
    infer_instance
  · let Q := (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf
    let : Q.RespectsIso := inferInstance
    intro V φ hφ
    exact MorphismProperty.RespectsIso.postcomp Q e.hom φ hφ

private theorem pointsMap_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : F ⟶ G) (β : G ⟶ H) (x : AlgebraicGeometry.Space.points B S hS F) :
    AlgebraicGeometry.Space.pointsMap B S hS G β (AlgebraicGeometry.Space.pointsMap B S hS F α x) =
      AlgebraicGeometry.Space.pointsMap B S hS F (α ≫ β) x := by
  induction x using Quot.inductionOn with
  | h p => simp only [AlgebraicGeometry.Space.pointsMap_class]; rfl

private theorem exists_affineOpenSubspace_point
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) [F.IsRepresentable]
    (x : AlgebraicGeometry.Space.points B S hS F) :
    ∃ U : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj F.reprX).affineOpens,
      x ∈ Set.range (AlgebraicGeometry.Space.pointsMap B S hS
        (affineOpenSubspace B S hS F.reprW U).toFunctor
        (affineOpenSubspace B S hS F.reprW U).ι) := by
  obtain ⟨y, hy⟩ := AlgebraicGeometry.Space.pointsMap_surjective_of_isIso B S hS F.reprW.hom x
  revert hy
  refine Quot.inductionOn y ?_
  intro p hp
  let X := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj F.reprX
  let z := AlgebraicGeometry.Space.schemePoint B S hS F.reprX p
  have hz : z ∈ (⨆ U : X.affineOpens, (U : X.Opens)) := by
    rw [iSup_affineOpens_eq_top]
    trivial
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  let j := affineOpenInclusion B S hS F.reprX U
  let A := affineOpenObject B S hS F.reprX U
  let q := yoneda.map j ≫ F.reprW.hom
  have : IsOpenImmersion ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j) := by
    show IsOpenImmersion U.val.ι
    infer_instance
  have hzj : z ∈ Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j) := by
    show z ∈ Set.range U.val.ι
    rw [Scheme.Opens.range_ι]
    exact hU
  obtain ⟨r, hr⟩ := AlgebraicGeometry.PurelyTranscendentalDescent.fieldPoint_factors_through_open
    B S hS j p hzj
  refine ⟨U, AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj A) (Subfunctor.toRange q)
    (r.class B S hS (yoneda.obj A)), ?_⟩
  show AlgebraicGeometry.Space.pointsMap B S hS (Subfunctor.range q).toFunctor
    (Subfunctor.range q).ι _ = x
  dsimp only [affineOpenSubspace]
  rw [pointsMap_comp, Subfunctor.toRange_ι]
  show AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj A)
    (yoneda.map j ≫ F.reprW.hom) _ = x
  rw [← pointsMap_comp, hr]
  exact hp

private theorem affineOpenSubspace_isAffine
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    [F.IsRepresentable]
    (U : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj F.reprX).affineOpens) :
    AlgebraicGeometry.Space.IsAffineSpace B S hS
      (affineOpenSubspace B S hS F.reprW U).toFunctor := by
  refine ⟨affineOpenObject B S hS F.reprX U, ?_, ?_⟩
  · show IsAffine U.1.toScheme; infer_instance
  · exact ⟨(affineOpenSubspaceIso B S hS U).symm⟩

/-- **Stacks 07SQ along an open subspace of a stage.** If the inverse image in the limit of a
quasi-compact open subspace `U` of a stage `X_i` is affine, then its inverse image in some later
stage is a scheme: the inverse images of `U` in the stages beyond `i` form a descent situation
whose limit is the inverse image of `U` in the limit, and Stacks 07SQ applies to it. -/
private theorem exists_isRepresentable_preimage
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {hZ : B.Contains (⊤_ Scheme.{u})}
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : AlgebraicGeometry.Space.DescentSituation B S hS hZ I) (hI : #I < B.cutoff.ord.cof)
    (i : I) (U : Subfunctor (D.system.obj (Opposite.op i)))
    (hU : AlgebraicGeometry.Space.IsOpenSubspace B S hS U)
    (hUqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS U.toFunctor)
    (hlim : AlgebraicGeometry.Space.IsAffineSpace B S hS
      (U.preimage (D.limitCone.π.app (Opposite.op i))).toFunctor) :
    ∃ (j : I) (hij : i ≤ j),
      (U.preimage (D.system.map (homOfLE hij).op)).toFunctor.IsRepresentable := by
  have : Nonempty (LimitTail I i) := ⟨⟨i, le_rfl⟩⟩
  have : IsDirected (LimitTail I i) (· ≤ ·) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨k, hxk, hyk⟩ := IsDirected.directed (r := (· ≤ ·)) x.1 y.1
    exact ⟨⟨k, x.2.trans hxk⟩, hxk, hyk⟩
  let G : (LimitTail I i)ᵒᵖ ⥤ Iᵒᵖ :=
    (limitTailOverEquiv i).functor ⋙ Over.forget (Opposite.op i)
  have : G.Initial := by dsimp only [G]; infer_instance
  let ct : Cone (G ⋙ D.system) := D.limitCone.whisker G
  have hct : IsLimit ct :=
    (Functor.Initial.isLimitWhiskerEquiv G D.limitCone).symm D.isLimit
  let τ : (G ⋙ D.system) ⟶
      (Functor.const ((LimitTail I i)ᵒᵖ)).obj (D.system.obj (Opposite.op i)) :=
    { app := fun j => D.system.map (homOfLE j.unop.2).op
      naturality := fun j k φ =>
        ((D.system.map_comp (G.map φ) ((homOfLE k.unop.2).op)).symm.trans
            (congrArg (fun x : G.obj j ⟶ Opposite.op i => D.system.map x)
              (Subsingleton.elim _ _))).trans
          (Category.comp_id _).symm }
  have hσ : ∀ j, ct.π.app j ≫ τ.app j = D.limitCone.π.app (Opposite.op i) := fun j =>
    D.limitCone.w (homOfLE j.unop.2).op
  have hVp : ∀ j : (LimitTail I i)ᵒᵖ,
      AlgebraicGeometry.Space.IsOpenSubspace B S hS (U.preimage (τ.app j)) :=
    fun j => AlgebraicGeometry.Space.isOpenSubspace_preimage B S hS (τ.app j) U (D.algebraicSpace i)
      (D.algebraicSpace j.unop.1) hU
  have hqc : ∀ j : LimitTail I i, AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS
      ((Subfunctor.preimageDiagram τ U).obj (Opposite.op j)) := fun j =>
    AlgebraicGeometry.PurelyTranscendentalDescent.isQuasiCompact_of_isAffineHom B S hS
      (U.fromPreimage (τ.app (Opposite.op j)))
      (hVp (Opposite.op j)).1 hU.1
      (AlgebraicGeometry.Space.isAffineHom_of_isPullback
        (Subfunctor.isPullback_fromPreimage U (τ.app (Opposite.op j))).flip
        (D.transition_affine _)) hUqc
  let d : AlgebraicGeometry.Space.DescentSituation B S hS hZ (LimitTail I i) :=
    { system := Subfunctor.preimageDiagram τ U
      algebraicSpace := fun j => (hVp (Opposite.op j)).1
      transition_affine := fun φ => AlgebraicGeometry.Space.isAffineHom_of_isPullback
        (Subfunctor.isPullback_preimageDiagram_map τ U φ).flip (D.transition_affine _)
      quasiCompact := hqc
      quasiSeparated := fun j =>
        AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
        (hVp (Opposite.op j)).1 (D.quasiSeparated j.1)
        (AlgebraicGeometry.Space.isQuasiSeparated_of_mono B S hS
          (U.preimage (τ.app (Opposite.op j))).ι inferInstance)
      limitCone := Subfunctor.preimageCone τ U hσ
      isLimit := Subfunctor.isLimitPreimageCone τ U hσ hct
      limitAlgebraicSpace :=
        (AlgebraicGeometry.Space.isOpenSubspace_preimage B S hS _ U (D.algebraicSpace i)
          D.limitAlgebraicSpace hU).1
      base := ⟨i, le_rfl⟩ }
  have hItail : #(LimitTail I i) < B.cutoff.ord.cof :=
    (Cardinal.mk_subtype_le _).trans_lt hI
  obtain ⟨hSizeOp, hHomSizeOp⟩ := size_op (B := B) hItail
  have hb : AlgebraicGeometry.Space.ChartsBounded B S hS d.system :=
    AlgebraicGeometry.Space.chartsBounded_of_lt_cof_ord B S hS d.system hSizeOp hHomSizeOp
  obtain ⟨j, -, T, -, ⟨e⟩⟩ :=
    AlgebraicGeometry.Space.hasAffineStageDescent_of_chartsBounded B S hS hZ d hb hlim
  exact ⟨j.1, j.2, Functor.IsRepresentable.mk' e.symm⟩

private theorem exists_point_not_mem_openSubspace
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (U : Subfunctor F) (hU : AlgebraicGeometry.Space.IsOpenSubspace B S hS U) (hne : U ≠ ⊤) :
    ∃ x : AlgebraicGeometry.Space.points B S hS F,
      x ∉ Set.range (AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor U.ι) := by
  by_contra h
  push Not at h
  obtain ⟨g, hg⟩ := (AlgebraicGeometry.Space.factorsThrough_openSubspace_iff_points
    B S hS hF hF U hU (𝟙 F)).mpr (fun x _ => h x)
  apply hne
  apply top_unique
  intro T x _
  have hx : (g.app T x).val = x := congrArg (fun k => k.app T x) hg
  rw [← hx]
  exact (g.app T x).property

private theorem exists_schematicOpen_preimage_affineOpen
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : AlgebraicGeometry.Space.DescentSituation B S hS hZ I) (hI : #I < B.cutoff.ord.cof)
    [D.limitCone.pt.IsRepresentable]
    (U : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      D.limitCone.pt.reprX).affineOpens) :
    ∃ (j : I) (V : Subfunctor (D.system.obj (Opposite.op j))),
      AlgebraicGeometry.Space.IsOpenSubspace B S hS V ∧ V.toFunctor.IsRepresentable ∧
      V.preimage (D.limitCone.π.app (Opposite.op j)) =
        affineOpenSubspace B S hS D.limitCone.pt.reprW U := by
  obtain ⟨i, V, hV, hVqc, hpre⟩ :=
    D.exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq hI
      (affineOpenSubspace B S hS D.limitCone.pt.reprW U)
      (affineOpenSubspace_isOpen B S hS U)
      (affineOpenSubspace_isQuasiCompact B S hS U)
  have hlim : AlgebraicGeometry.Space.IsAffineSpace B S hS
      (V.preimage (D.limitCone.π.app (Opposite.op i))).toFunctor := by
    rw [hpre]
    exact affineOpenSubspace_isAffine B S hS U
  obtain ⟨j, hij, hj⟩ := exists_isRepresentable_preimage D hI i V hV hVqc hlim
  refine ⟨j, V.preimage (D.system.map (homOfLE hij).op),
    AlgebraicGeometry.Space.isOpenSubspace_preimage B S hS _ V (D.algebraicSpace i)
      (D.algebraicSpace j) hV, hj, ?_⟩
  rw [← Subfunctor.preimage_comp, D.limitCone.w, hpre]

private theorem isAffineHom_of_comp_mono
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (g : G ⟶ H) [Mono g]
    (hfg : AlgebraicGeometry.Space.IsAffineHom B S hS (f ≫ g)) :
    AlgebraicGeometry.Space.IsAffineHom B S hS f := by
  apply AlgebraicGeometry.Space.isAffineHom_of_isPullback (f := f ≫ g) (g := g) (p := 𝟙 F)
  · apply IsPullback.mk'
    · simp
    · intro T a b hab _
      simpa using hab
    · intro T a b hab
      exact ⟨a, by simp, (cancel_mono g).mp (by simpa using hab)⟩
  · exact hfg

private theorem pointsMap_mem_preimage
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (U : Subfunctor G) (hU : AlgebraicGeometry.Space.IsOpenSubspace B S hS U)
    (x : AlgebraicGeometry.Space.points B S hS F)
    (hx : AlgebraicGeometry.Space.pointsMap B S hS F f x ∈
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor U.ι)) :
    x ∈ Set.range (AlgebraicGeometry.Space.pointsMap B S hS (U.preimage f).toFunctor
      (U.preimage f).ι) := by
  obtain ⟨y, hy⟩ := hx
  let V := U.preimage f
  have hV := AlgebraicGeometry.Space.isOpenSubspace_preimage B S hS f U hG hF hU
  let X : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨F, hF⟩
  let Y : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨G, hG⟩
  let A : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨U.toFunctor, hU.1⟩
  let P : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨V.toFunctor, hV.1⟩
  have hp : IsPullback
      (ObjectProperty.homMk V.ι : P ⟶ X)
      (ObjectProperty.homMk (U.fromPreimage f) : P ⟶ A)
      (ObjectProperty.homMk f : X ⟶ Y)
      (ObjectProperty.homMk U.ι : A ⟶ Y) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) (Subfunctor.isPullback_fromPreimage U f).flip
  obtain ⟨z, hz, _⟩ := AlgebraicGeometry.Space.exists_point_of_isPullback B S hS hp x y hy.symm
  exact ⟨z, hz⟩

private theorem exists_top_of_covering_limit
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : AlgebraicGeometry.Space.DescentSituation B S hS hZ I)
    (K : ∀ i : I, Subfunctor (D.system.obj (Opposite.op i)))
    (hK : ∀ i, AlgebraicGeometry.Space.IsOpenSubspace B S hS (K i))
    (hmon : ∀ i j (hij : i ≤ j),
      (K i).preimage (D.system.map (homOfLE hij).op) ≤ K j)
    (hI : #I < B.cutoff.ord.cof)
    (hpoint : ∀ x : AlgebraicGeometry.Space.points B S hS D.limitCone.pt,
      ∃ i, AlgebraicGeometry.Space.pointsMap B S hS D.limitCone.pt
        (D.limitCone.π.app (Opposite.op i)) x ∈
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS (K i).toFunctor (K i).ι)) :
    ∃ i, K i = ⊤ := by
  classical
  have : Nonempty I := ⟨D.base⟩
  let bad (i : I) :=
    (Set.range (AlgebraicGeometry.Space.pointsMap B S hS (K i).toFunctor (K i).ι))ᶜ
  have hbad (i : I) : @IsClosed _
      (AlgebraicGeometry.Space.pointTopology B S hS _) (bad i) :=
    (AlgebraicGeometry.Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS (K i).ι
      (hK i).2).isClosed_compl
  let Z (i : I) := AlgebraicGeometry.Space.reducedClosedSubspace B S hS _ (D.algebraicSpace i)
    (bad i) (hbad i)
  have hZclosed (i : I) : AlgebraicGeometry.Space.IsClosedSubspace B S hS (Z i) :=
    AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace B S hS _ _ _ _
  have hZrange (i : I) : Set.range
      (AlgebraicGeometry.Space.pointsMap B S hS (Z i).toFunctor (Z i).ι) = bad i :=
    AlgebraicGeometry.Space.range_pointsMap_ι_reducedClosedSubspace B S hS _ _ _ _
  have hZred (i : I) :=
    AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS _
      (D.algebraicSpace i) (bad i) (hbad i)
  have hlift {i j : Iᵒᵖ} (f : i ⟶ j) :
      ∃ g : (Z i.unop).toFunctor ⟶ (Z j.unop).toFunctor,
        g ≫ (Z j.unop).ι = (Z i.unop).ι ≫ D.system.map f := by
    apply (AlgebraicGeometry.Space.exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS
      (D.algebraicSpace j.unop) (hZclosed i.unop).1
      (Z j.unop) (hZclosed j.unop) (hZred i.unop) _).mpr
    rintro _ ⟨x, rfl⟩
    rw [hZrange]
    intro hx
    have hxi : AlgebraicGeometry.Space.pointsMap B S hS (Z i.unop).toFunctor (Z i.unop).ι x ∈
        bad i.unop := by
      rw [← hZrange]
      exact ⟨x, rfl⟩
    have hx' : AlgebraicGeometry.Space.pointsMap B S hS _ (D.system.map f)
        (AlgebraicGeometry.Space.pointsMap B S hS _ (Z i.unop).ι x) ∈
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS (K j.unop).toFunctor (K j.unop).ι) := by
      rw [pointsMap_comp]
      exact hx
    obtain ⟨y, hy⟩ := pointsMap_mem_preimage B S hS
      (D.algebraicSpace i.unop) (D.algebraicSpace j.unop)
      (D.system.map f) (K j.unop) (hK j.unop) _ hx'
    have hm : (K j.unop).preimage (D.system.map f) ≤ K i.unop := by
      have hf : (homOfLE (leOfHom f.unop)).op = f := Subsingleton.elim _ _
      simpa only [hf] using hmon j.unop i.unop (leOfHom f.unop)
    apply hxi
    refine ⟨AlgebraicGeometry.Space.pointsMap B S hS _ (Subfunctor.homOfLe hm) y, ?_⟩
    rw [pointsMap_comp, Subfunctor.homOfLe_ι]
    exact hy
  let g {i j : Iᵒᵖ} (f : i ⟶ j) := (hlift f).choose
  have hg {i j : Iᵒᵖ} (f : i ⟶ j) :
      g f ≫ (Z j.unop).ι = (Z i.unop).ι ≫ D.system.map f := (hlift f).choose_spec
  let E : Iᵒᵖ ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
    { obj i := (Z i.unop).toFunctor
      map f := g f
      map_id i := by
        apply (cancel_mono (Z i.unop).ι).mp
        simp only [hg, D.system.map_id, Category.comp_id, Category.id_comp]
      map_comp f f' := by
        apply (cancel_mono (Z _).ι).mp
        simp only [Category.assoc, hg, D.system.map_comp]
        simp only [← Category.assoc, hg] }
  let η : E ⟶ D.system :=
    { app i := (Z i.unop).ι
      naturality i j f := hg f }
  have hE (i : Iᵒᵖ) : AlgebraicGeometry.IsAlgebraicSpace B S hS (E.obj i) :=
    (hZclosed i.unop).1
  have hιaff (i : I) :=
    AlgebraicGeometry.Space.isAffineHom_of_isClosedImmersion B S hS (Z i).ι (hZclosed i).2
  have hEaff {i j : Iᵒᵖ} (f : i ⟶ j) :
      AlgebraicGeometry.Space.IsAffineHom B S hS (E.map f) := by
    apply isAffineHom_of_comp_mono B S hS (E.map f) (Z j.unop).ι
    show AlgebraicGeometry.Space.IsAffineHom B S hS (g f ≫ (Z j.unop).ι)
    rw [hg]
    exact AlgebraicGeometry.Space.isAffineHom_comp B S hS _ _ (hιaff i.unop) (D.transition_affine f)
  have hEqc (i : Iᵒᵖ) : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (E.obj i) :=
    AlgebraicGeometry.Space.isQuasiCompactSpace_of_isClosedImmersion B S hS
      (D.quasiCompact i.unop) (Z i.unop).ι (hZclosed i.unop).2
  refine (em (∃ i, K i = ⊤)).resolve_right fun hne => ?_
  push Not at hne
  have hEne (i : Iᵒᵖ) : Nonempty (AlgebraicGeometry.Space.points B S hS (E.obj i)) := by
    obtain ⟨x, hx⟩ := exists_point_not_mem_openSubspace B S hS
      (D.algebraicSpace i.unop) (K i.unop) (hK i.unop) (hne i.unop)
    have hx' : x ∈ Set.range
        (AlgebraicGeometry.Space.pointsMap B S hS (Z i.unop).toFunctor (Z i.unop).ι) := by
      rw [hZrange]
      exact hx
    obtain ⟨z, _⟩ := hx'
    exact ⟨z⟩
  obtain ⟨hSizeOp, hHomSizeOp⟩ := size_op (B := B) hI
  obtain ⟨y⟩ := AlgebraicGeometry.Space.nonempty_points_limit B S hS E hSizeOp hHomSizeOp hE
    hEaff hEqc hEne
  let a : limit E ⟶ D.limitCone.pt := D.isLimit.lift ((Cone.postcompose η).obj (limit.cone E))
  let x := AlgebraicGeometry.Space.pointsMap B S hS (limit E) a y
  obtain ⟨i, hi⟩ := hpoint x
  refine (show AlgebraicGeometry.Space.pointsMap B S hS D.limitCone.pt
      (D.limitCone.π.app (Opposite.op i)) x ∈ bad i from ?_) hi
  rw [← hZrange]
  refine ⟨AlgebraicGeometry.Space.pointsMap B S hS (limit E) (limit.π E (Opposite.op i)) y, ?_⟩
  have ha : a ≫ D.limitCone.π.app (Opposite.op i) = limit.π E (Opposite.op i) ≫ (Z i).ι :=
    D.isLimit.fac _ _
  dsimp only [x]
  rw [pointsMap_comp, pointsMap_comp, ha]

/-- If the limit of an affine inverse system of quasi-compact and quasi-separated
algebraic spaces is a scheme, then one of its stages is a scheme. -/
private theorem exists_isRepresentable_stage
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)]
    (D : AlgebraicGeometry.Space.DescentSituation B S hS hZ I) (hI : #I < B.cutoff.ord.cof)
    (hX : D.limitCone.pt.IsRepresentable) :
    ∃ i : I, (D.system.obj (Opposite.op i)).IsRepresentable := by
  classical
  let : D.limitCone.pt.IsRepresentable := hX
  let K (i : I) := AlgebraicGeometry.Space.schematicLocus B S hS (D.system.obj (Opposite.op i))
  suffices h : ∃ i : I, K i = ⊤ by
    obtain ⟨i, hi⟩ := h
    have : (K i).toFunctor.IsRepresentable :=
      (Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS
        (D.algebraicSpace i)).2
    have : IsIso (K i).ι := (Subfunctor.eq_top_iff_isIso (K i)).mp hi
    exact ⟨i, isRepresentable_of_natIso (K i).toFunctor (asIso (K i).ι)⟩
  have hmon (i j : I) (hij : i ≤ j) :
      (K i).preimage (D.system.map (homOfLE hij).op) ≤ K j :=
    preimage_schematicLocus_le B S hS _ (D.algebraicSpace j) (D.algebraicSpace i)
      (D.transition_affine _)
  have hdesc (U : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      D.limitCone.pt.reprX).affineOpens) :
      ∃ i : I, affineOpenSubspace B S hS D.limitCone.pt.reprW U ≤
        (K i).preimage (D.limitCone.π.app (Opposite.op i)) := by
    obtain ⟨i, V, hVo, hVr, hpre⟩ := exists_schematicOpen_preimage_affineOpen B S hS hZ D hI U
    refine ⟨i, ?_⟩
    rw [← hpre]
    intro T x hx
    exact AlgebraicGeometry.Space.le_schematicLocus B S hS _ V hVo hVr T hx
  have hpoint (x : AlgebraicGeometry.Space.points B S hS D.limitCone.pt) :
      ∃ i : I, AlgebraicGeometry.Space.pointsMap B S hS D.limitCone.pt
        (D.limitCone.π.app (Opposite.op i)) x ∈
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS (K i).toFunctor (K i).ι) := by
    obtain ⟨U, q, hq⟩ := exists_affineOpenSubspace_point B S hS D.limitCone.pt x
    obtain ⟨i, hUi⟩ := hdesc U
    refine ⟨i, AlgebraicGeometry.Space.pointsMap B S hS
      (affineOpenSubspace B S hS D.limitCone.pt.reprW U).toFunctor
      (Subfunctor.homOfLe hUi ≫ (K i).fromPreimage
        (D.limitCone.π.app (Opposite.op i))) q, ?_⟩
    rw [pointsMap_comp, Category.assoc, Subfunctor.fromPreimage_ι,
      ← Category.assoc, Subfunctor.homOfLe_ι, ← pointsMap_comp, hq]
    rfl
  exact exists_top_of_covering_limit B S hS hZ D K
    (fun i => (Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS
      (D.algebraicSpace i)).1)
    hmon hI hpoint

end Stacks.SchemeStage

namespace AlgebraicGeometry.Space.DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})}

/-- **Stacks 07SR, for an index below the cofinality of the cutoff.** In the situation of
Stacks 084R — a directed inverse system of quasi-compact and quasi-separated algebraic spaces
over `S` with affine transition morphisms, indexed by a set smaller than the cofinality of the
site's size cutoff — if the limit `X` is a scheme then some stage `X_i` is a scheme, and `i` may
be taken beyond the distinguished index.

The size bound is the standing form of Situation 084R in this development; see the
implementation notes of this module. The source states 07SR with no bound on the index, so this
theorem is not registered under the tag. -/
theorem exists_base_le_isRepresentable_system_obj {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) (hI : #I < B.cutoff.ord.cof)
    (hX : D.limitCone.pt.IsRepresentable) :
    ∃ i, D.base ≤ i ∧ (D.system.obj (Opposite.op i)).IsRepresentable := by
  obtain ⟨i, hi⟩ := Stacks.SchemeStage.exists_isRepresentable_stage B S hS hZ I D hI hX
  obtain ⟨j, hbj, hij⟩ := exists_ge_ge D.base i
  refine ⟨j, hbj, ?_⟩
  exact Stacks.SchemeStage.isRepresentable_of_isAffineHom B S hS
    (D.system.map (homOfLE hij).op) (D.algebraicSpace j) (D.algebraicSpace i)
    (D.transition_affine _)

end AlgebraicGeometry.Space.DescentSituation

end
