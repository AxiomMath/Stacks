module

public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.PullbackMono
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatIsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactSchemeTheoreticDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenSchemeLocus

/-!
# Stacks 0CPF: cartesian squares of finite type spaces descend to the stages

Let `B = lim_i B_i` be the limit of a directed inverse system of Noetherian algebraic spaces with
affine transition morphisms, an `AlgebraicGeometry.Space.NoetherianLimitSystem` (Situation 0CP6),
and let `X₁ = X₂ ×_{X₄} X₃` be a cartesian square of algebraic spaces over `B`, quasi-separated
over `B`. Choosing diagrams as in Stacks 0CP8 for the four spaces gives limit descriptions
`X_j = lim_i X^j_i` by their systems of scheme-theoretic images (Stacks 0CP9), and the four
morphisms of the square descend to morphisms of these inverse systems (Stacks 0CPA). Stacks 0CPF
asserts that at every late stage the descended square commutes, that the comparison morphism
`X¹_i ⟶ X²_i ×_{X⁴_i} X³_i` is a closed immersion, and that it is an isomorphism when `a` is flat
and of finite presentation.

## Main definitions

* `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.app`: the component of a morphism of
  image systems at a stage, together with `restrict`, `id` and `comp`.
* `AlgebraicGeometry.Space.GoodDiagram.cartesianDiagram`: the diagram of Stacks 0CP8 for `X₁`
  whose model is the fibre product `X²_k ×_{X⁴_k} X³_k` of the stages.

## Main results

* `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.exists_systemMorphism_inv`: two diagrams
  for the same space give eventually isomorphic limit descriptions (the example of Stacks 0CPB).
* `AlgebraicGeometry.Space.GoodDiagram.exists_isClosedImmersion_cartesianDiagram`: for the
  cartesian diagram the comparison morphisms are closed immersions at every stage.
* `AlgebraicGeometry.Space.GoodDiagram.isIso_lift_of_isFlat`: at a stage where `a_i` is flat and
  `X₃ = X₄ ×_{X⁴_i} X³_i`, a closed comparison morphism is an isomorphism.
* `AlgebraicGeometry.Space.GoodDiagram.exists_isClosedImmersion_lift_and_isIso`: **Stacks 0CPF**.

## Implementation notes

As in the source, the closed immersion is obtained for the cartesian diagram, whose stages sit
inside `X²_i ×_{X⁴_i} X³_i` by construction, and transported to the given diagram of `X₁` along
the eventual isomorphism of limit descriptions of Stacks 0CPB. That `X₁` is a closed subspace of
`B ×_{B_k} (X²_k ×_{X⁴_k} X³_k)` is seen by exhibiting the inclusion as a composite of two base
changes of the closed immersions `X_j ⟶ B ×_{B_k} X^j_k`, using that `X₄ ⟶ B ×_{B_k} X⁴_k` is a
monomorphism.

For the isomorphism the source uses Stacks 0CPC for all four morphisms and Stacks 0852. Here
Stacks 0CPC is used for `a` alone: once `X₃ = X₄ ×_{X⁴_i} X³_i` with `a_i` flat, `X₁` is the base
change of `X₂ ⟶ X²_i` along the flat morphism `X²_i ×_{X⁴_i} X³_i ⟶ X²_i`, so by Stacks 089E its
scheme-theoretic image is everything, and it is contained in the closed subspace `X¹_i`. Only `a`
therefore needs to be flat and of finite presentation; the source assumes this of `a` and `b`.
Quasi-separatedness is used for `X₁`, `X₃` and `X₄`, and algebraicity of `X₂` for Stacks 089E.

The size hypothesis `small` on the index set is the one of the library's form of Stacks 0CP9.

## References

* [Stacks Project, Tag 0CPF](https://stacks.math.columbia.edu/tag/0CPF)
* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CP8](https://stacks.math.columbia.edu/tag/0CP8)
* [Stacks Project, Tag 0CP9](https://stacks.math.columbia.edu/tag/0CP9)
* [Stacks Project, Tag 0CPA](https://stacks.math.columbia.edu/tag/0CPA)
* [Stacks Project, Tag 0CPB](https://stacks.math.columbia.edu/tag/0CPB)
* [Stacks Project, Tag 0CPC](https://stacks.math.columbia.edu/tag/0CPC)
* [Stacks Project, Tag 089E](https://stacks.math.columbia.edu/tag/089E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space


/-- A morphism whose composite with a monomorphism is a closed immersion is a closed immersion:
it is the base change of the composite along the monomorphism. -/
theorem isClosedImmersion_of_comp_mono (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Mono g] (hfg : IsClosedImmersion B S hS (f ≫ g)) : IsClosedImmersion B S hS f :=
  (isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback
    (IsPullback.of_horiz_isIso_mono (fst := 𝟙 X) (snd := f) (f := f ≫ g) (g := g)
      ⟨Category.id_comp _⟩) hfg

namespace GoodDiagram

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] {D : NoetherianLimitSystem B S hS hZ I}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX : X ⟶ D.limitCone.pt}
    {pY : Y ⟶ D.limitCone.pt} {pZ : Z ⟶ D.limitCone.pt}

/-- The member `X_i` of the image system of a good diagram at a stage `i` above its index. -/
noncomputable abbrev stageAt (G : GoodDiagram B S hS hZ D pX) (i : I) (h : G.index ≤ i) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (imageSystem G).obj (Over.mk (homOfLE h).op)

/-- The transition morphism `X_{i'} ⟶ X_i` of the image system for `i ≤ i'`. -/
noncomputable abbrev stageTransition (G : GoodDiagram B S hS hZ D pX) {i i' : I}
    (h : G.index ≤ i) (h' : i ≤ i') :
    stageAt G i' (h.trans h') ⟶ stageAt G i h :=
  (imageSystem G).map (Over.homMk (homOfLE h').op (Subsingleton.elim _ _))

/-- The projection `X ⟶ X_i` of the canonical cone. -/
noncomputable abbrev stageπ (G : GoodDiagram B S hS hZ D pX) (i : I) (h : G.index ≤ i) :
    X ⟶ stageAt G i h :=
  (imageCone G).π.app (Over.mk (homOfLE h).op)

/-- The transition morphism `X_{i'} ⟶ X_i` lies over the transition morphism `B_{i'} ⟶ B_i`. -/
@[reassoc]
lemma stageTransition_ι_fst (G : GoodDiagram B S hS hZ D pX) {i i' : I} (h : G.index ≤ i)
    (h' : i ≤ i') :
    stageTransition G h h' ≫ (stageImage G (Over.mk (homOfLE h).op)).ι ≫ pullback.fst _ _ =
      (stageImage G (Over.mk (homOfLE (h.trans h')).op)).ι ≫ pullback.fst _ _ ≫
        D.system.map (homOfLE h').op := by
  rw [imageSystem_map_ι_assoc, stageTargetMap_fst]
  rfl

/-- The transition morphism `X_{i'} ⟶ X_i` is compatible with the projections to the model. -/
@[reassoc]
lemma stageTransition_ι_snd (G : GoodDiagram B S hS hZ D pX) {i i' : I} (h : G.index ≤ i)
    (h' : i ≤ i') :
    stageTransition G h h' ≫ (stageImage G (Over.mk (homOfLE h).op)).ι ≫ pullback.snd _ _ =
      (stageImage G (Over.mk (homOfLE (h.trans h')).op)).ι ≫ pullback.snd _ _ := by
  rw [imageSystem_map_ι_assoc, stageTargetMap_snd]

/-- Two morphisms into a member `X_{i'}` of the image system agree as soon as they agree over the
stage `B_{i'}` and after the transition morphism to an earlier member `X_i`. -/
lemma stage_hom_ext (G : GoodDiagram B S hS hZ D pX) {i i' : I} (h : G.index ≤ i)
    (h' : i ≤ i') {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {u v : T ⟶ stageAt G i' (h.trans h')}
    (e₁ : u ≫ (stageImage G (Over.mk (homOfLE (h.trans h')).op)).ι ≫ pullback.fst _ _ =
      v ≫ (stageImage G (Over.mk (homOfLE (h.trans h')).op)).ι ≫ pullback.fst _ _)
    (e₂ : u ≫ stageTransition G h h' = v ≫ stageTransition G h h') : u = v := by
  refine (cancel_mono (stageImage G (Over.mk (homOfLE (h.trans h')).op)).ι).1
    (pullback.hom_ext (by simpa only [Category.assoc] using e₁) ?_)
  rw [Category.assoc, Category.assoc, ← stageTransition_ι_snd G h h', reassoc_of% e₂,
    stageTransition_ι_snd]

namespace SystemMorphism

variable {GX : GoodDiagram B S hS hZ D pX} {GY : GoodDiagram B S hS hZ D pY}
    {GZ : GoodDiagram B S hS hZ D pZ} {f : X ⟶ Y} {g : Y ⟶ Z} {i₀ : I}
    {hiX : GX.index ≤ i₀} {hiY : GY.index ≤ i₀} {hiZ : GZ.index ≤ i₀}

/-- The component `f_i : X_i ⟶ Y_i` of a morphism of image systems at a stage `i ≥ i₀`. -/
noncomputable def app (F : SystemMorphism GX GY f i₀ hiX hiY) (i : I) (h : i₀ ≤ i) :
    stageAt GX i (hiX.trans h) ⟶ stageAt GY i (hiY.trans h) :=
  F.maps.app (Over.mk (homOfLE h).op)

/-- The component `f_i` lies over the stage `B_i`. -/
@[reassoc]
lemma app_over_base (F : SystemMorphism GX GY f i₀ hiX hiY) (i : I) (h : i₀ ≤ i) :
    F.app i h ≫ (stageImage GY (Over.mk (homOfLE (hiY.trans h)).op)).ι ≫ pullback.fst _ _ =
      (stageImage GX (Over.mk (homOfLE (hiX.trans h)).op)).ι ≫ pullback.fst _ _ :=
  F.over_base _

/-- The components of a morphism of image systems are compatible with the projections from
the limits. -/
lemma stageπ_app (F : SystemMorphism GX GY f i₀ hiX hiY) (i : I) (h : i₀ ≤ i) :
    stageπ GX i (hiX.trans h) ≫ F.app i h = f ≫ stageπ GY i (hiY.trans h) :=
  F.induces (Over.mk (homOfLE h).op)

/-- The components of a morphism of image systems commute with the transition morphisms. -/
@[reassoc]
lemma stageTransition_app (F : SystemMorphism GX GY f i₀ hiX hiY) {i i' : I} (h : i₀ ≤ i)
    (h' : i ≤ i') :
    stageTransition GX (hiX.trans h) h' ≫ F.app i h =
      F.app i' (h.trans h') ≫ stageTransition GY (hiY.trans h) h' :=
  F.maps.naturality (Over.homMk (homOfLE h').op (Subsingleton.elim _ _) :
    (Over.mk (homOfLE (h.trans h')).op : Over (op i₀)) ⟶ Over.mk (homOfLE h).op)


/-- The restriction of a morphism of image systems to the tail above a later stage. -/
noncomputable def restrict (F : SystemMorphism GX GY f i₀ hiX hiY) {i₁ : I} (h : i₀ ≤ i₁) :
    SystemMorphism GX GY f i₁ (hiX.trans h) (hiY.trans h) where
  maps :=
    { app j := F.maps.app ((Over.map (homOfLE h).op).obj j)
      naturality _ _ v := F.maps.naturality ((Over.map (homOfLE h).op).map v) }
  over_base j := F.over_base ((Over.map (homOfLE h).op).obj j)
  induces j := F.induces ((Over.map (homOfLE h).op).obj j)

/-- The components of a restriction are the components of the original morphism. -/
@[simp]
lemma restrict_app (F : SystemMorphism GX GY f i₀ hiX hiY) {i₁ : I} (h : i₀ ≤ i₁) (i : I)
    (h' : i₁ ≤ i) : (F.restrict h).app i h' = F.app i (h.trans h') := rfl

/-- The identity morphism of the image system of a good diagram, on the tail above `i₀`. -/
noncomputable def id (G : GoodDiagram B S hS hZ D pX) (i₀ : I) (h : G.index ≤ i₀) :
    SystemMorphism G G (𝟙 X) i₀ h h where
  maps := 𝟙 _
  over_base _ := Category.id_comp _
  induces _ := (Category.comp_id _).trans (Category.id_comp _).symm

/-- The components of the identity morphism of an image system are identities. -/
@[simp]
lemma id_app (G : GoodDiagram B S hS hZ D pX) (i₀ : I) (h : G.index ≤ i₀) (i : I)
    (h' : i₀ ≤ i) : (id G i₀ h).app i h' = 𝟙 _ := rfl

/-- The composite of two morphisms of image systems on a common tail. -/
noncomputable def comp (F : SystemMorphism GX GY f i₀ hiX hiY)
    (G : SystemMorphism GY GZ g i₀ hiY hiZ) {fg : X ⟶ Z} (hfg : f ≫ g = fg) :
    SystemMorphism GX GZ fg i₀ hiX hiZ where
  maps := F.maps ≫ G.maps
  over_base j := by
    rw [NatTrans.comp_app, Category.assoc, G.over_base j, F.over_base j]
  induces j := by
    rw [NatTrans.comp_app, ← Category.assoc, F.induces j, Category.assoc, G.induces j,
      ← Category.assoc, hfg]

/-- The components of a composite are the composites of the components. -/
@[simp]
lemma comp_app (F : SystemMorphism GX GY f i₀ hiX hiY)
    (G : SystemMorphism GY GZ g i₀ hiY hiZ) {fg : X ⟶ Z} (hfg : f ≫ g = fg) (i : I)
    (h : i₀ ≤ i) : (F.comp G hfg).app i h = F.app i h ≫ G.app i h := rfl

/-- **Stacks 0CPA, eventual uniqueness, stagewise.** Two morphisms of image systems inducing the
same morphism, defined on tails above possibly different stages, have the same component at
every sufficiently late stage. -/
theorem exists_forall_app_eq (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsQuasiSeparated B S hS pX) (hSize : Cardinal.mk I < B.cutoff.ord.cof)
    {i₁ : I} {hiX' : GX.index ≤ i₁} {hiY' : GY.index ≤ i₁}
    (F : SystemMorphism GX GY f i₀ hiX hiY) (F' : SystemMorphism GX GY f i₁ hiX' hiY') :
    ∃ (i₃ : I) (h₀ : i₀ ≤ i₃) (h₁ : i₁ ≤ i₃), ∀ (i : I) (h : i₃ ≤ i),
      F.app i (h₀.trans h) = F'.app i (h₁.trans h) := by
  obtain ⟨m, hm₀, hm₁⟩ := exists_ge_ge i₀ i₁
  obtain ⟨i₃, hm, hi₃⟩ := eventually_eq_systemMorphism hX hXqs hSize (F.restrict hm₀)
    (F'.restrict hm₁)
  exact ⟨i₃, hm₀.trans hm, hm₁.trans hm, fun i h =>
    hi₃ (Over.mk (homOfLE (hm.trans h)).op) h⟩

/-- **The limit descriptions attached to two good diagrams of the same space are eventually
isomorphic** (the example of Stacks 0CPB). On a common tail there are morphisms of image systems
in both directions inducing the identity of `X`, and at every sufficiently late stage their
components are mutually inverse. -/
theorem exists_systemMorphism_inv (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsQuasiSeparated B S hS pX) (hSize : Cardinal.mk I < B.cutoff.ord.cof)
    (G G' : GoodDiagram B S hS hZ D pX) :
    ∃ (i₀ : I) (h : G.index ≤ i₀) (h' : G'.index ≤ i₀)
      (E : SystemMorphism G G' (𝟙 X) i₀ h h') (E' : SystemMorphism G' G (𝟙 X) i₀ h' h)
      (i₁ : I) (h₁ : i₀ ≤ i₁), ∀ (i : I) (hi : i₁ ≤ i),
        E.app i (h₁.trans hi) ≫ E'.app i (h₁.trans hi) = 𝟙 _ ∧
          E'.app i (h₁.trans hi) ≫ E.app i (h₁.trans hi) = 𝟙 _ := by
  obtain ⟨a, ha, ha', ⟨E₀⟩⟩ := exists_systemMorphism hX hXqs hSize (𝟙 X)
    (Category.id_comp pX) G G'
  obtain ⟨b, hb', hb, ⟨E₀'⟩⟩ := exists_systemMorphism hX hXqs hSize (𝟙 X)
    (Category.id_comp pX) G' G
  obtain ⟨m, ham, hbm⟩ := exists_ge_ge a b
  let E := E₀.restrict ham
  let E' := E₀'.restrict hbm
  obtain ⟨c, hc, _, hc'⟩ := exists_forall_app_eq hX hXqs hSize
    (E.comp E' (Category.id_comp _)) (id G m (ha.trans ham))
  obtain ⟨d, _, _, hd'⟩ := exists_forall_app_eq hX hXqs hSize
    (E'.comp E (Category.id_comp _)) (id G' m (hb'.trans hbm))
  obtain ⟨i₁, hci, hdi⟩ := exists_ge_ge c d
  refine ⟨m, ha.trans ham, hb'.trans hbm, E, E', i₁, hc.trans hci, fun i hi => ⟨?_, ?_⟩⟩
  · exact hc' i (hci.trans hi)
  · exact hd' i (hdi.trans hi)

end SystemMorphism

/-! ### `X` inside the base change of a member of its image system -/

/-- The base change `B ×_{B_i} X_i` of the member `X_i` of the image system to the limit. -/
noncomputable abbrev stageBaseChange (G : GoodDiagram B S hS hZ D pX) (i : I)
    (h : G.index ≤ i) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (D.limitCone.π.app (op i))
    ((stageImage G (Over.mk (homOfLE h).op)).ι ≫ pullback.fst _ _)

/-- The projection `X ⟶ X_i` lies over the projection `B ⟶ B_i`. -/
@[reassoc]
lemma stageπ_ι_fst (G : GoodDiagram B S hS hZ D pX) (i : I) (h : G.index ≤ i) :
    stageπ G i h ≫ (stageImage G (Over.mk (homOfLE h).op)).ι ≫ pullback.fst _ _ =
      pX ≫ D.limitCone.π.app (op i) := by
  rw [imageCone_π_ι_assoc, stageMap_fst]
  rfl

/-- The projection `X ⟶ X_i` followed by the projection to the model is `X ⟶ W`. -/
@[reassoc]
lemma stageπ_ι_snd (G : GoodDiagram B S hS hZ D pX) (i : I) (h : G.index ≤ i) :
    stageπ G i h ≫ (stageImage G (Over.mk (homOfLE h).op)).ι ≫ pullback.snd _ _ =
      G.toModel := by
  rw [imageCone_π_ι_assoc, stageMap_snd]

/-- A morphism `r : X_{i₀} ⟶ Y_{i₀}` between members of two image systems at one stage, over
`B_{i₀}` and compatible with `f` in the limit, extends to a morphism of image systems on the
tail above `i₀` whose components followed by the transition morphisms to the stage `i₀` are the
transition morphisms followed by `r`. -/
theorem exists_systemMorphism_of_stage_hom (GX : GoodDiagram B S hS hZ D pX)
    (GY : GoodDiagram B S hS hZ D pY) (f : X ⟶ Y) (hf : f ≫ pY = pX) {i₀ : I}
    (hiX : GX.index ≤ i₀) (hiY : GY.index ≤ i₀) (r : stageAt GX i₀ hiX ⟶ stageAt GY i₀ hiY)
    (r_base : r ≫ (stageImage GY (Over.mk (homOfLE hiY).op)).ι ≫ pullback.fst _ _ =
      (stageImage GX (Over.mk (homOfLE hiX).op)).ι ≫ pullback.fst _ _)
    (r_lim : stageπ GX i₀ hiX ≫ r = f ≫ stageπ GY i₀ hiY) :
    ∃ F : SystemMorphism GX GY f i₀ hiX hiY, ∀ (i : I) (h : i₀ ≤ i),
      F.app i h ≫ stageTransition GY hiY h = stageTransition GX hiX h ≫ r := by
  obtain ⟨F, hF⟩ := exists_systemMorphism_of_stage_map GX GY f hf hiX hiY
    (r ≫ (stageImage GY (Over.mk (homOfLE hiY).op)).ι ≫ pullback.snd _ _)
    (by
      rw [Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% r_base]
      rfl)
    (by rw [reassoc_of% r_lim, stageπ_ι_snd])
  refine ⟨F, fun i h => (cancel_mono (stageImage GY (Over.mk (homOfLE hiY).op)).ι).1
    (pullback.hom_ext ?_ ?_)⟩
  · simp only [Category.assoc]
    rw [stageTransition_ι_fst, SystemMorphism.app_over_base_assoc, r_base,
      stageTransition_ι_fst]
  · simp only [Category.assoc]
    rw [stageTransition_ι_snd]
    exact hF (Over.mk (homOfLE h).op)

/-- The morphism `X ⟶ B ×_{B_i} X_i`. -/
noncomputable def toStageBaseChange (G : GoodDiagram B S hS hZ D pX) (i : I)
    (h : G.index ≤ i) : X ⟶ stageBaseChange G i h :=
  pullback.lift pX (stageπ G i h) (stageπ_ι_fst G i h).symm

/-- The first component of `X ⟶ B ×_{B_i} X_i` is the structure morphism. -/
@[reassoc (attr := simp)]
lemma toStageBaseChange_fst (G : GoodDiagram B S hS hZ D pX) (i : I) (h : G.index ≤ i) :
    toStageBaseChange G i h ≫ pullback.fst _ _ = pX := pullback.lift_fst _ _ _

/-- The second component of `X ⟶ B ×_{B_i} X_i` is the projection to `X_i`. -/
@[reassoc (attr := simp)]
lemma toStageBaseChange_snd (G : GoodDiagram B S hS hZ D pX) (i : I) (h : G.index ≤ i) :
    toStageBaseChange G i h ≫ pullback.snd _ _ = stageπ G i h := pullback.lift_snd _ _ _

/-- The comparison `B ×_{B_i} X_i ⟶ B ×_{B_{i₀}} W`, a monomorphism. -/
noncomputable def stageBaseChangeToModel (G : GoodDiagram B S hS hZ D pX) (i : I)
    (h : G.index ≤ i) :
    stageBaseChange G i h ⟶ pullback (D.limitCone.π.app (op G.index)) G.modelMap :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ (stageImage G (Over.mk (homOfLE h).op)).ι ≫ pullback.snd _ _) (by
      have hw := D.limitCone.w (homOfLE h).op
      have hc := pullback.condition (f := D.limitCone.π.app (op i))
        (g := (stageImage G (Over.mk (homOfLE h).op)).ι ≫ pullback.fst _ _)
      have hc' := pullback.condition (f := D.system.map (Over.mk (homOfLE h).op).hom)
        (g := G.modelMap)
      simp only [Category.assoc] at hc ⊢
      rw [← hc', ← reassoc_of% hc]
      exact congrArg (pullback.fst _ _ ≫ ·) hw.symm)

/-- The comparison `B ×_{B_i} X_i ⟶ B ×_{B_{i₀}} W` lies over `B`. -/
@[reassoc (attr := simp)]
lemma stageBaseChangeToModel_fst (G : GoodDiagram B S hS hZ D pX) (i : I) (h : G.index ≤ i) :
    stageBaseChangeToModel G i h ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

/-- The comparison `B ×_{B_i} X_i ⟶ B ×_{B_{i₀}} W` followed by the projection to `W`. -/
@[reassoc (attr := simp)]
lemma stageBaseChangeToModel_snd (G : GoodDiagram B S hS hZ D pX) (i : I) (h : G.index ≤ i) :
    stageBaseChangeToModel G i h ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (stageImage G (Over.mk (homOfLE h).op)).ι ≫ pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The comparison `B ×_{B_i} X_i ⟶ B ×_{B_{i₀}} W` is a monomorphism, since
`X_i ⟶ B_i ×_{B_{i₀}} W` is one. -/
instance (G : GoodDiagram B S hS hZ D pX) (i : I) (h : G.index ≤ i) :
    Mono (stageBaseChangeToModel G i h) where
  right_cancellation u v huv := by
    have h₁ : u ≫ pullback.fst _ _ = v ≫ pullback.fst _ _ := by
      simpa using congrArg (· ≫ pullback.fst _ _) huv
    have h₂ := congrArg (· ≫ pullback.snd _ _) huv
    simp only [Category.assoc, stageBaseChangeToModel_snd] at h₂
    refine pullback.hom_ext h₁ ?_
    refine (cancel_mono (stageImage G (Over.mk (homOfLE h).op)).ι).1 ?_
    refine pullback.hom_ext ?_ (by simpa only [Category.assoc] using h₂)
    simp only [Category.assoc, ← pullback.condition, reassoc_of% h₁]

/-- The morphism `X ⟶ B ×_{B_i} X_i` followed by the comparison is the closed immersion of the
good diagram. -/
lemma toStageBaseChange_comp (G : GoodDiagram B S hS hZ D pX) (i : I) (h : G.index ≤ i) :
    toStageBaseChange G i h ≫ stageBaseChangeToModel G i h = G.induced := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, stageBaseChangeToModel_fst, toStageBaseChange_fst, pullback.lift_fst]
  · rw [Category.assoc, stageBaseChangeToModel_snd, toStageBaseChange_snd_assoc, stageπ_ι_snd,
      pullback.lift_snd]

/-- **`X` is a closed subspace of `B ×_{B_i} X_i`.** -/
theorem isClosedImmersion_toStageBaseChange (G : GoodDiagram B S hS hZ D pX) (i : I)
    (h : G.index ≤ i) : IsClosedImmersion B S hS (toStageBaseChange G i h) :=
  isClosedImmersion_of_comp_mono B S hS _ (stageBaseChangeToModel G i h)
    (by rw [toStageBaseChange_comp]; exact G.isClosedImmersion)

namespace SystemMorphism

variable {GX : GoodDiagram B S hS hZ D pX} {GY : GoodDiagram B S hS hZ D pY} {f : X ⟶ Y}
    {i₀ : I} {hiX : GX.index ≤ i₀} {hiY : GY.index ≤ i₀}

/-- The base change `B ×_{B_i} X_i ⟶ B ×_{B_i} Y_i` of a component of a morphism of image
systems. -/
noncomputable def baseChangeMap (F : SystemMorphism GX GY f i₀ hiX hiY) (i : I)
    (h : i₀ ≤ i) :
    stageBaseChange GX i (hiX.trans h) ⟶ stageBaseChange GY i (hiY.trans h) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ F.app i h) (by
    rw [Category.assoc, F.app_over_base, pullback.condition])

/-- The base change of a component lies over `B`. -/
@[reassoc (attr := simp)]
lemma baseChangeMap_fst (F : SystemMorphism GX GY f i₀ hiX hiY) (i : I) (h : i₀ ≤ i) :
    F.baseChangeMap i h ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

/-- The base change of a component is compatible with the component. -/
@[reassoc (attr := simp)]
lemma baseChangeMap_snd (F : SystemMorphism GX GY f i₀ hiX hiY) (i : I) (h : i₀ ≤ i) :
    F.baseChangeMap i h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ F.app i h :=
  pullback.lift_snd _ _ _

/-- A morphism into `B ×_{B_i} X_i` followed by the base change of a component. -/
lemma lift_baseChangeMap (F : SystemMorphism GX GY f i₀ hiX hiY) (i : I) (h : i₀ ≤ i)
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (u : T ⟶ D.limitCone.pt)
    (v : T ⟶ stageAt GX i (hiX.trans h))
    (w : u ≫ D.limitCone.π.app (op i) =
      v ≫ (stageImage GX (Over.mk (homOfLE (hiX.trans h)).op)).ι ≫ pullback.fst _ _) :
    pullback.lift u v w ≫ F.baseChangeMap i h =
      pullback.lift u (v ≫ F.app i h) (by rw [w, Category.assoc, F.app_over_base]) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, baseChangeMap_fst, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, baseChangeMap_snd, pullback.lift_snd_assoc, pullback.lift_snd]

/-- The base changes of the components are compatible with `f` in the limit. -/
@[reassoc]
lemma toStageBaseChange_baseChangeMap (F : SystemMorphism GX GY f i₀ hiX hiY) (hf : f ≫ pY = pX)
    (i : I) (h : i₀ ≤ i) :
    toStageBaseChange GX i (hiX.trans h) ≫ F.baseChangeMap i h =
      f ≫ toStageBaseChange GY i (hiY.trans h) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, baseChangeMap_fst, toStageBaseChange_fst, Category.assoc,
      toStageBaseChange_fst, hf]
  · rw [Category.assoc, baseChangeMap_snd, toStageBaseChange_snd_assoc, Category.assoc,
      toStageBaseChange_snd, stageπ_app]

end SystemMorphism

/-! ### The cartesian square inside the base changes of the stages -/

section Cartesian

variable {X₁ X₂ X₃ X₄ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX₁ : X₁ ⟶ D.limitCone.pt}
    {pX₂ : X₂ ⟶ D.limitCone.pt} {pX₃ : X₃ ⟶ D.limitCone.pt} {pX₄ : X₄ ⟶ D.limitCone.pt}
    {G₂ : GoodDiagram B S hS hZ D pX₂} {G₃ : GoodDiagram B S hS hZ D pX₃}
    {G₄ : GoodDiagram B S hS hZ D pX₄} {p : X₁ ⟶ X₃} {q : X₁ ⟶ X₂} {a : X₃ ⟶ X₄}
    {b : X₂ ⟶ X₄} {i₅ i₆ : I} {h₃₅ : G₃.index ≤ i₅} {h₄₅ : G₄.index ≤ i₅}
    {h₂₆ : G₂.index ≤ i₆} {h₄₆ : G₄.index ≤ i₆}

/-- For a cartesian square `X₁ = X₂ ×_{X₄} X₃` over `B`, the morphism from `X₁` to the fibre
product of the base changes `B ×_{B_k} X^j_k` is a closed immersion: each `X^j` is a closed
subspace of `B ×_{B_k} X^j_k`, and `X^4` maps monomorphically to `B ×_{B_k} X^4_k`. -/
theorem isClosedImmersion_lift_toStageBaseChange (hcart : IsPullback p q a b)
    (ha : a ≫ pX₄ = pX₃) (hb : b ≫ pX₄ = pX₂)
    (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅) (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆) (k : I)
    (h₅ : i₅ ≤ k) (h₆ : i₆ ≤ k) :
    IsClosedImmersion B S hS
      (pullback.lift (q ≫ toStageBaseChange G₂ k (h₂₆.trans h₆))
        (p ≫ toStageBaseChange G₃ k (h₃₅.trans h₅)) (by
          rw [Category.assoc, Category.assoc, Fb.toStageBaseChange_baseChangeMap hb,
            Fa.toStageBaseChange_baseChangeMap ha, ← Category.assoc, ← Category.assoc,
            hcart.w]) :
        X₁ ⟶ pullback (Fb.baseChangeMap k h₆) (Fa.baseChangeMap k h₅)) := by
  set c₂ := toStageBaseChange G₂ k (h₂₆.trans h₆)
  set c₃ := toStageBaseChange G₃ k (h₃₅.trans h₅)
  set c₄ := toStageBaseChange G₄ k (h₄₅.trans h₅)
  set r₂ := Fb.baseChangeMap k h₆
  set r₃ := Fa.baseChangeMap k h₅
  have hc₄ : Mono c₄ :=
    mono_of_isClosedImmersion B S hS _ (isClosedImmersion_toStageBaseChange G₄ k _)
  have e₂ : c₂ ≫ r₂ = b ≫ c₄ := Fb.toStageBaseChange_baseChangeMap hb k h₆
  have e₃ : c₃ ≫ r₃ = a ≫ c₄ := Fa.toStageBaseChange_baseChangeMap ha k h₅
  -- `X₁ ⟶ Y₂ ×_{Y₄} X₃` is the base change of `c₂`.
  let α : X₁ ⟶ pullback r₂ (a ≫ c₄) :=
    pullback.lift (q ≫ c₂) p (by rw [Category.assoc, e₂, ← Category.assoc, ← hcart.w,
      Category.assoc])
  have hα : IsClosedImmersion B S hS α := by
    have s : IsPullback (α ≫ pullback.snd _ _) q (a ≫ c₄) (c₂ ≫ r₂) := by
      rw [pullback.lift_snd, e₂]
      exact hcart.comp_mono c₄
    have sq := IsPullback.of_right s (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback r₂ (a ≫ c₄)).flip
    exact (isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback sq.flip
      (isClosedImmersion_toStageBaseChange G₂ k _)
  -- `Y₂ ×_{Y₄} X₃ ⟶ Y₂ ×_{Y₄} Y₃` is the base change of `c₃`.
  let β : pullback r₂ (a ≫ c₄) ⟶ pullback r₂ r₃ :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ c₃) (by
      rw [Category.assoc, e₃, pullback.condition])
  have hβ : IsClosedImmersion B S hS β := by
    have s : IsPullback (pullback.snd r₂ (a ≫ c₄)) (β ≫ pullback.fst _ _) (c₃ ≫ r₃) r₂ := by
      rw [pullback.lift_fst, e₃]
      exact (IsPullback.of_hasPullback r₂ (a ≫ c₄)).flip
    have sq := IsPullback.of_bot s (pullback.lift_snd _ _ _).symm
      (IsPullback.of_hasPullback r₂ r₃).flip
    exact (isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback sq
      (isClosedImmersion_toStageBaseChange G₃ k _)
  have hαβ : α ≫ β = pullback.lift (q ≫ c₂) (p ≫ c₃) (by
      rw [Category.assoc, Category.assoc, e₂, e₃, ← Category.assoc, ← Category.assoc,
        hcart.w]) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
        pullback.lift_snd]
  rw [← hαβ]
  exact isClosedImmersion_comp B S hS _ _ hα hβ

/-- The finite type model `X^2_k ×_{X^4_k} X^3_k ⟶ B_k` of the cartesian diagram. -/
theorem isFiniteType_cartesianModelMap (alg₄ : IsAlgebraicSpace B S hS X₄)
    (qs₄ : IsQuasiSeparated B S hS pX₄) (small : Cardinal.mk I < B.cutoff.ord.cof)
    (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅) (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆) (k : I)
    (h₅ : i₅ ≤ k) (h₆ : i₆ ≤ k) :
    IsFiniteType B S hS (pullback.fst (Fb.app k h₆) (Fa.app k h₅) ≫
      (stageImage G₂ (Over.mk (homOfLE (h₂₆.trans h₆)).op)).ι ≫ pullback.fst _ _) := by
  have alg₂ := imageSystem_isAlgebraicSpace G₂ (Over.mk (homOfLE (h₂₆.trans h₆)).op)
  have alg₃ := imageSystem_isAlgebraicSpace G₃ (Over.mk (homOfLE (h₃₅.trans h₅)).op)
  have alg₄k := imageSystem_isAlgebraicSpace G₄ (Over.mk (homOfLE (h₄₅.trans h₅)).op)
  have algB := D.system_isAlgebraicSpace k
  have algT := isAlgebraicSpace_pullback B S hS (Fb.app k h₆) (Fa.app k h₅) alg₂ alg₃ alg₄k
  have lft (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pY' : Y' ⟶ D.limitCone.pt)
      (G' : GoodDiagram B S hS hZ D pY') (i : I) (h : G'.index ≤ i) :
      IsLocallyOfFiniteType B S hS
        ((stageImage G' (Over.mk (homOfLE h).op)).ι ≫ pullback.fst _ _) :=
    isLocallyOfFiniteType_comp B S hS (imageSystem_isAlgebraicSpace G' _)
      (isAlgebraicSpace_stageTarget G' _) (D.system_isAlgebraicSpace i) _ _
      (isLocallyOfFiniteType_of_isClosedImmersion B S hS _
        (isClosedSubspace_stageImage G' _).2)
      (isLocallyOfFiniteType_stageTarget_fst G' _)
  have lftA : IsLocallyOfFiniteType B S hS (Fa.app k h₅) := by
    refine isLocallyOfFiniteType_of_comp B S hS alg₃ alg₄k algB _
      ((stageImage G₄ (Over.mk (homOfLE (h₄₅.trans h₅)).op)).ι ≫ pullback.fst _ _) ?_
    rw [Fa.app_over_base]
    exact lft _ _ G₃ k _
  constructor
  · exact isLocallyOfFiniteType_comp B S hS algT alg₂ algB _ _
      (isLocallyOfFiniteType_pullback_fst' B S hS alg₃ alg₄k alg₂ _ _ lftA) (lft _ _ G₂ k _)
  · have qcT : IsQuasiCompactSpace B S hS (pullback (Fb.app k h₆) (Fa.app k h₅)) :=
      isQuasiCompactSpace_pullback B S hS hZ _ _ alg₂ alg₄k
        (imageSystem_isQuasiCompactSpace G₂ _) (imageSystem_isQuasiCompactSpace G₃ _)
        (imageSystem_isAbsolutelyQuasiSeparated_of_isQuasiSeparated G₄ small alg₄ qs₄ _)
    exact isQuasiCompact_of_isQuasiCompactSpace B S hS hZ algB (D.noetherian k).2.1 qcT _

/-- The two projections of `X²_k ×_{X⁴_k} X³_k` lie over the same morphism to `B_k`. -/
@[reassoc]
lemma cartesian_fst_ι_fst (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅)
    (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆) (k : I) (h₅ : i₅ ≤ k) (h₆ : i₆ ≤ k) :
    pullback.fst (Fb.app k h₆) (Fa.app k h₅) ≫
        (stageImage G₂ (Over.mk (homOfLE (h₂₆.trans h₆)).op)).ι ≫ pullback.fst _ _ =
      pullback.snd (Fb.app k h₆) (Fa.app k h₅) ≫
        (stageImage G₃ (Over.mk (homOfLE (h₃₅.trans h₅)).op)).ι ≫ pullback.fst _ _ := by
  rw [← Fa.app_over_base k h₅, ← Fb.app_over_base k h₆, pullback.condition_assoc]

/-- The model of the cartesian good diagram, `X²_k ×_{X⁴_k} X³_k`. -/
noncomputable abbrev cartesianModel (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅)
    (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆) (k : I) (h₅ : i₅ ≤ k) (h₆ : i₆ ≤ k) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (Fb.app k h₆) (Fa.app k h₅)

/-- The structure morphism `X²_k ×_{X⁴_k} X³_k ⟶ B_k`. -/
noncomputable abbrev cartesianModelMap (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅)
    (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆) (k : I) (h₅ : i₅ ≤ k) (h₆ : i₆ ≤ k) :
    cartesianModel Fa Fb k h₅ h₆ ⟶ D.system.obj (op k) :=
  pullback.fst (Fb.app k h₆) (Fa.app k h₅) ≫
    (stageImage G₂ (Over.mk (homOfLE (h₂₆.trans h₆)).op)).ι ≫ pullback.fst _ _

/-- The comparison of `B ×_{B_k} (X²_k ×_{X⁴_k} X³_k)` with the fibre product of the base
changes `B ×_{B_k} X^j_k`. -/
noncomputable def cartesianComparison (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅)
    (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆) (k : I) (h₅ : i₅ ≤ k) (h₆ : i₆ ≤ k) :
    pullback (D.limitCone.π.app (op k)) (cartesianModelMap Fa Fb k h₅ h₆) ⟶
      pullback (Fb.baseChangeMap k h₆) (Fa.baseChangeMap k h₅) :=
  pullback.lift
    (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst _ _) (by
      rw [pullback.condition, Category.assoc]))
    (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (by
      rw [Category.assoc, ← cartesian_fst_ι_fst]
      exact pullback.condition))
    (by
      rw [SystemMorphism.lift_baseChangeMap, SystemMorphism.lift_baseChangeMap]
      congr 1
      rw [Category.assoc, Category.assoc, pullback.condition])

/-- A component of the comparison of base changes. -/
@[reassoc (attr := simp)]
lemma cartesianComparison_fst_fst (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅)
    (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆) (k : I) (h₅ : i₅ ≤ k) (h₆ : i₆ ≤ k) :
    cartesianComparison Fa Fb k h₅ h₆ ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  rw [cartesianComparison, pullback.lift_fst_assoc, pullback.lift_fst]

/-- A component of the comparison of base changes. -/
@[reassoc (attr := simp)]
lemma cartesianComparison_fst_snd (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅)
    (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆) (k : I) (h₅ : i₅ ≤ k) (h₆ : i₆ ≤ k) :
    cartesianComparison Fa Fb k h₅ h₆ ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.fst _ _ := by
  rw [cartesianComparison, pullback.lift_fst_assoc, pullback.lift_snd]

/-- A component of the comparison of base changes. -/
@[reassoc (attr := simp)]
lemma cartesianComparison_snd_fst (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅)
    (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆) (k : I) (h₅ : i₅ ≤ k) (h₆ : i₆ ≤ k) :
    cartesianComparison Fa Fb k h₅ h₆ ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  rw [cartesianComparison, pullback.lift_snd_assoc, pullback.lift_fst]

/-- A component of the comparison of base changes. -/
@[reassoc (attr := simp)]
lemma cartesianComparison_snd_snd (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅)
    (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆) (k : I) (h₅ : i₅ ≤ k) (h₆ : i₆ ≤ k) :
    cartesianComparison Fa Fb k h₅ h₆ ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  rw [cartesianComparison, pullback.lift_snd_assoc, pullback.lift_snd]

/-- The comparison of base changes is a monomorphism. -/
instance (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅) (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆)
    (k : I) (h₅ : i₅ ≤ k) (h₆ : i₆ ≤ k) : Mono (cartesianComparison Fa Fb k h₅ h₆) where
  right_cancellation u v huv := by
    have e₁ := congrArg (· ≫ pullback.fst _ _ ≫ pullback.fst _ _) huv
    have e₂ := congrArg (· ≫ pullback.fst _ _ ≫ pullback.snd _ _) huv
    have e₃ := congrArg (· ≫ pullback.snd _ _ ≫ pullback.snd _ _) huv
    simp only [Category.assoc, cartesianComparison_fst_fst, cartesianComparison_fst_snd,
      cartesianComparison_snd_snd] at e₁ e₂ e₃
    exact pullback.hom_ext e₁ (pullback.hom_ext (by simpa only [Category.assoc] using e₂)
      (by simpa only [Category.assoc] using e₃))

/-- **The good diagram of a cartesian square with model the fibre product of the stages.** For a
cartesian square `X₁ = X₂ ×_{X₄} X₃` over `B` and a stage `k` at which the morphisms `a_k` and
`b_k` of image systems are defined, the diagram `X₁ ⟶ X²_k ×_{X⁴_k} X³_k ⟶ B_k`. -/
noncomputable abbrev cartesianDiagram (alg₄ : IsAlgebraicSpace B S hS X₄)
    (qs₄ : IsQuasiSeparated B S hS pX₄) (small : Cardinal.mk I < B.cutoff.ord.cof)
    (hcart : IsPullback p q a b) (ha : a ≫ pX₄ = pX₃) (hb : b ≫ pX₄ = pX₂)
    (hq : q ≫ pX₂ = pX₁)
    (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅) (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆) (k : I)
    (h₅ : i₅ ≤ k) (h₆ : i₆ ≤ k) : GoodDiagram B S hS hZ D pX₁ where
  index := k
  model := cartesianModel Fa Fb k h₅ h₆
  model_isAlgebraicSpace := isAlgebraicSpace_pullback B S hS _ _
    (imageSystem_isAlgebraicSpace G₂ _) (imageSystem_isAlgebraicSpace G₃ _)
    (imageSystem_isAlgebraicSpace G₄ _)
  modelMap := cartesianModelMap Fa Fb k h₅ h₆
  toModel := pullback.lift (q ≫ stageπ G₂ k (h₂₆.trans h₆)) (p ≫ stageπ G₃ k (h₃₅.trans h₅))
    (by rw [Category.assoc, Category.assoc, Fb.stageπ_app, Fa.stageπ_app, ← Category.assoc,
      ← Category.assoc, hcart.w])
  commutes := by
    rw [pullback.lift_fst_assoc, Category.assoc, stageπ_ι_fst, ← Category.assoc, hq]
  isFiniteType := isFiniteType_cartesianModelMap alg₄ qs₄ small Fa Fb k h₅ h₆
  isClosedImmersion := by
    have hp : p ≫ pX₃ = pX₁ := by rw [← ha, ← Category.assoc, hcart.w, Category.assoc, hb, hq]
    refine isClosedImmersion_of_comp_mono B S hS _ (cartesianComparison Fa Fb k h₅ h₆) ?_
    convert isClosedImmersion_lift_toStageBaseChange hcart ha hb Fa Fb k h₅ h₆ using 1
    refine pullback.hom_ext (pullback.hom_ext ?_ ?_) (pullback.hom_ext ?_ ?_)
    · simp only [Category.assoc, cartesianComparison_fst_fst, pullback.lift_fst,
        toStageBaseChange_fst, hq]
    · simp only [Category.assoc, cartesianComparison_fst_snd, pullback.lift_snd_assoc,
        pullback.lift_fst, toStageBaseChange_snd]
    · simp only [Category.assoc, cartesianComparison_snd_fst, pullback.lift_fst,
        pullback.lift_snd_assoc, toStageBaseChange_fst, hp]
    · simp only [Category.assoc, cartesianComparison_snd_snd, pullback.lift_snd_assoc,
        pullback.lift_snd, toStageBaseChange_snd]

/-- **The cartesian square of the image systems of the cartesian good diagram.** The two
projections of `X²_k ×_{X⁴_k} X³_k` induce morphisms `q'` and `p'` from the image system of the
cartesian good diagram to those of `G₂` and `G₃`, inducing `q` and `p`; at every stage
`i ≥ k` they satisfy `b_i ∘ q'_i = a_i ∘ p'_i`, and `(q'_i, p'_i)` is a closed immersion into
`X²_i ×_{X⁴_i} X³_i`. -/
theorem exists_isClosedImmersion_cartesianDiagram (alg₄ : IsAlgebraicSpace B S hS X₄)
    (qs₄ : IsQuasiSeparated B S hS pX₄) (small : Cardinal.mk I < B.cutoff.ord.cof)
    (hcart : IsPullback p q a b) (ha : a ≫ pX₄ = pX₃) (hb : b ≫ pX₄ = pX₂)
    (hq : q ≫ pX₂ = pX₁)
    (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅) (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆) (k : I)
    (h₅ : i₅ ≤ k) (h₆ : i₆ ≤ k) :
    ∃ (Q : SystemMorphism (cartesianDiagram alg₄ qs₄ small hcart ha hb hq Fa Fb k h₅ h₆) G₂ q k
        le_rfl (h₂₆.trans h₆))
      (P : SystemMorphism (cartesianDiagram alg₄ qs₄ small hcart ha hb hq Fa Fb k h₅ h₆) G₃ p k
        le_rfl (h₃₅.trans h₅))
      (comm : ∀ (i : I) (h : k ≤ i),
        Q.app i h ≫ Fb.app i (h₆.trans h) = P.app i h ≫ Fa.app i (h₅.trans h)),
      ∀ (i : I) (h : k ≤ i), IsClosedImmersion B S hS (pullback.lift _ _ (comm i h)) := by
  have hp : p ≫ pX₃ = pX₁ := by rw [← ha, ← Category.assoc, hcart.w, Category.assoc, hb, hq]
  set G := cartesianDiagram alg₄ qs₄ small hcart ha hb hq Fa Fb k h₅ h₆ with hG
  -- the inclusion of the base stage of `G` into `X²_k ×_{X⁴_k} X³_k`
  let ι₀ : stageAt G k le_rfl ⟶ cartesianModel Fa Fb k h₅ h₆ :=
    (stageImage G (Over.mk (homOfLE (le_refl k)).op)).ι ≫ pullback.snd _ _
  have ι₀_base : ι₀ ≫ cartesianModelMap Fa Fb k h₅ h₆ =
      (stageImage G (Over.mk (homOfLE (le_refl k)).op)).ι ≫ pullback.fst _ _ := by
    have hc := pullback.condition
      (f := D.system.map (Over.mk (homOfLE (le_refl k)).op).hom) (g := G.modelMap)
    have hid : D.system.map (Over.mk (homOfLE (le_refl k)).op).hom = 𝟙 _ :=
      (congrArg D.system.map (Subsingleton.elim _ (𝟙 (op k)))).trans (D.system.map_id _)
    exact (Category.assoc _ _ _).trans
      ((congrArg ((stageImage G (Over.mk (homOfLE (le_refl k)).op)).ι ≫ ·) hc.symm).trans
        ((congrArg (fun t => (stageImage G (Over.mk (homOfLE (le_refl k)).op)).ι ≫
          pullback.fst _ _ ≫ t) hid).trans (congrArg _ (Category.comp_id _))))
  have ι₀_lim : stageπ G k le_rfl ≫ ι₀ = G.toModel := stageπ_ι_snd G k le_rfl
  obtain ⟨Q, hQ⟩ := exists_systemMorphism_of_stage_hom (i₀ := k) G G₂ q hq le_rfl
    (h₂₆.trans h₆) (ι₀ ≫ pullback.fst _ _)
    (by rwa [Category.assoc])
    (by rw [reassoc_of% ι₀_lim]; exact pullback.lift_fst _ _ _)
  obtain ⟨P, hP⟩ := exists_systemMorphism_of_stage_hom (i₀ := k) G G₃ p hp le_rfl
    (h₃₅.trans h₅) (ι₀ ≫ pullback.snd _ _)
    (by rwa [Category.assoc, ← cartesian_fst_ι_fst])
    (by rw [reassoc_of% ι₀_lim]; exact pullback.lift_snd _ _ _)
  have comm : ∀ (i : I) (h : k ≤ i),
      Q.app i h ≫ Fb.app i (h₆.trans h) = P.app i h ≫ Fa.app i (h₅.trans h) := by
    intro i h
    refine stage_hom_ext G₄ (h₄₅.trans h₅) h ?_ ?_
    · rw [Category.assoc, Category.assoc, SystemMorphism.app_over_base,
        SystemMorphism.app_over_base, SystemMorphism.app_over_base,
        SystemMorphism.app_over_base]
    · rw [Category.assoc, Category.assoc, ← Fb.stageTransition_app h₆ h,
        ← Fa.stageTransition_app h₅ h, reassoc_of% hQ i h, reassoc_of% hP i h,
        Category.assoc, Category.assoc, pullback.condition]
  refine ⟨Q, P, comm, fun i h => ?_⟩
  -- the comparison of `X²_i ×_{X⁴_i} X³_i` with the base change of the model
  let κ : pullback (Fb.app i (h₆.trans h)) (Fa.app i (h₅.trans h)) ⟶
      pullback (D.system.map (Over.mk (homOfLE (le_refl k |>.trans h)).op).hom) G.modelMap :=
    pullback.lift
      (pullback.fst _ _ ≫ (stageImage G₂ (Over.mk (homOfLE ((h₂₆.trans h₆).trans h)).op)).ι ≫
        pullback.fst _ _)
      (pullback.lift (pullback.fst _ _ ≫ stageTransition G₂ (h₂₆.trans h₆) h)
        (pullback.snd _ _ ≫ stageTransition G₃ (h₃₅.trans h₅) h) (by
          rw [Category.assoc, Category.assoc, SystemMorphism.stageTransition_app,
            SystemMorphism.stageTransition_app, pullback.condition_assoc]))
      (by
        show _ = _ ≫ cartesianModelMap Fa Fb k h₅ h₆
        simp only [Category.assoc, pullback.lift_fst_assoc]
        rw [stageTransition_ι_fst]
        rfl)
  have hκ : Mono κ := ⟨fun u v huv => by
    have e₁ := congrArg (· ≫ pullback.fst _ _) huv
    have e₂ := congrArg (· ≫ pullback.snd _ _ ≫ pullback.fst _ _) huv
    have e₃ := congrArg (· ≫ pullback.snd _ _ ≫ pullback.snd _ _) huv
    simp only [κ, Category.assoc, pullback.lift_fst, pullback.lift_snd_assoc,
      pullback.lift_snd] at e₁ e₂ e₃
    refine pullback.hom_ext (stage_hom_ext G₂ (h₂₆.trans h₆) h ?_ ?_)
      (stage_hom_ext G₃ (h₃₅.trans h₅) h ?_ ?_)
    · simpa only [Category.assoc] using e₁
    · simpa only [Category.assoc] using e₂
    · simp only [Category.assoc]
      rw [← cartesian_fst_ι_fst]
      simpa only [Category.assoc] using e₁
    · simpa only [Category.assoc] using e₃⟩
  refine isClosedImmersion_of_comp_mono B S hS _ κ ?_
  convert (isClosedSubspace_stageImage G (Over.mk (homOfLE (le_refl k |>.trans h)).op)).2
    using 1
  refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_)
  · simp only [κ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    exact SystemMorphism.app_over_base Q i h
  · simp only [κ, Category.assoc, pullback.lift_snd, pullback.lift_fst, pullback.lift_fst_assoc]
    rw [hQ i h]
    exact stageTransition_ι_snd_assoc _ _ _ _
  · simp only [κ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    rw [hP i h]
    exact stageTransition_ι_snd_assoc _ _ _ _

end Cartesian

/-! ### Stacks 0CPF -/

section Main

variable {X₁ X₂ X₃ X₄ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX₁ : X₁ ⟶ D.limitCone.pt}
    {pX₂ : X₂ ⟶ D.limitCone.pt} {pX₃ : X₃ ⟶ D.limitCone.pt} {pX₄ : X₄ ⟶ D.limitCone.pt}
    {G₁ : GoodDiagram B S hS hZ D pX₁} {G₂ : GoodDiagram B S hS hZ D pX₂}
    {G₃ : GoodDiagram B S hS hZ D pX₃} {G₄ : GoodDiagram B S hS hZ D pX₄} {p : X₁ ⟶ X₃}
    {q : X₁ ⟶ X₂} {a : X₃ ⟶ X₄} {b : X₂ ⟶ X₄} {i₅ i₆ i₇ i₈ : I}
    {h₃₅ : G₃.index ≤ i₅} {h₄₅ : G₄.index ≤ i₅} {h₂₆ : G₂.index ≤ i₆} {h₄₆ : G₄.index ≤ i₆}
    {h₁₇ : G₁.index ≤ i₇} {h₃₇ : G₃.index ≤ i₇} {h₁₈ : G₁.index ≤ i₈} {h₂₈ : G₂.index ≤ i₈}

/-- **Stacks 0CPF, the closed immersion.** In Situation 0CP6, let `X₁ = X₂ ×_{X₄} X₃` be a
cartesian square of algebraic spaces over `B`, with `X₁` and `X₄` quasi-separated over `B`, let
`G₁, …, G₄` be diagrams as in Stacks 0CP8 for the four spaces, and let `a_i`, `b_i`, `p_i`, `q_i`
be morphisms of the image systems inducing `a`, `b`, `p`, `q`, as in Stacks 0CPA. Then at every
sufficiently late stage `a_i ∘ p_i = b_i ∘ q_i`, and `(q_i, p_i) : X¹_i ⟶ X²_i ×_{X⁴_i} X³_i` is a
closed immersion. -/
theorem exists_isClosedImmersion_lift (alg₁ : IsAlgebraicSpace B S hS X₁)
    (alg₄ : IsAlgebraicSpace B S hS X₄) (qs₁ : IsQuasiSeparated B S hS pX₁)
    (qs₄ : IsQuasiSeparated B S hS pX₄) (small : Cardinal.mk I < B.cutoff.ord.cof)
    (cart : IsPullback p q a b) (overA : a ≫ pX₄ = pX₃) (overB : b ≫ pX₄ = pX₂)
    (overQ : q ≫ pX₂ = pX₁)
    (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅) (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆)
    (Fp : SystemMorphism G₁ G₃ p i₇ h₁₇ h₃₇) (Fq : SystemMorphism G₁ G₂ q i₈ h₁₈ h₂₈) :
    ∃ (i₉ : I) (h₅ : i₅ ≤ i₉) (h₆ : i₆ ≤ i₉) (h₇ : i₇ ≤ i₉) (h₈ : i₈ ≤ i₉)
      (comm : ∀ (i : I) (hi : i₉ ≤ i),
        Fq.app i (h₈.trans hi) ≫ Fb.app i (h₆.trans hi) =
          Fp.app i (h₇.trans hi) ≫ Fa.app i (h₅.trans hi)),
      ∀ (i : I) (hi : i₉ ≤ i), IsClosedImmersion B S hS (pullback.lift _ _ (comm i hi)) := by
  obtain ⟨k, h₅k, h₆k⟩ := exists_ge_ge i₅ i₆
  set G := cartesianDiagram alg₄ qs₄ small cart overA overB overQ Fa Fb k h₅k h₆k
  obtain ⟨Q, P, comm', closed'⟩ := exists_isClosedImmersion_cartesianDiagram alg₄ qs₄ small
    cart overA overB overQ Fa Fb k h₅k h₆k
  obtain ⟨m, hmG, hmG', E, E', n, hmn, inv⟩ :=
    SystemMorphism.exists_systemMorphism_inv alg₁ qs₁ small G₁ G
  -- `E'` followed by `q_i` and `p_i` is eventually `Q` and `P`
  obtain ⟨m₁, hm₁, hm₁', hQ⟩ := SystemMorphism.exists_forall_app_eq alg₁ qs₁ small
    ((E'.restrict (exists_ge_ge m i₈).choose_spec.1).comp
      (Fq.restrict (exists_ge_ge m i₈).choose_spec.2) (Category.id_comp q)) Q
  obtain ⟨m₂, hm₂, hm₂', hP⟩ := SystemMorphism.exists_forall_app_eq alg₁ qs₁ small
    ((E'.restrict (exists_ge_ge m i₇).choose_spec.1).comp
      (Fp.restrict (exists_ge_ge m i₇).choose_spec.2) (Category.id_comp p)) P
  -- `a_i ∘ p_i = b_i ∘ q_i` eventually
  classical
  obtain ⟨c, hc⟩ := Finset.exists_le ({i₅, i₆, i₇, i₈} : Finset I)
  obtain ⟨m₃, _, _, hcomm⟩ := SystemMorphism.exists_forall_app_eq alg₁ qs₁ small
    ((Fq.restrict (hc i₈ (by simp))).comp (Fb.restrict (hc i₆ (by simp))) cart.w.symm)
    ((Fp.restrict (hc i₇ (by simp))).comp (Fa.restrict (hc i₅ (by simp))) rfl)
  obtain ⟨i₉, hi₉⟩ := Finset.exists_le ({i₅, i₆, i₇, i₈, k, n, m₁, m₂, m₃} : Finset I)
  have comm : ∀ (i : I) (hi : i₉ ≤ i),
      Fq.app i ((hi₉ i₈ (by simp)).trans hi) ≫ Fb.app i ((hi₉ i₆ (by simp)).trans hi) =
        Fp.app i ((hi₉ i₇ (by simp)).trans hi) ≫ Fa.app i ((hi₉ i₅ (by simp)).trans hi) :=
    fun i hi => hcomm i ((hi₉ m₃ (by simp)).trans hi)
  refine ⟨i₉, hi₉ i₅ (by simp), hi₉ i₆ (by simp), hi₉ i₇ (by simp), hi₉ i₈ (by simp), comm,
    fun i hi => ?_⟩
  have hk : k ≤ i := (hi₉ k (by simp)).trans hi
  have hn : n ≤ i := (hi₉ n (by simp)).trans hi
  have hQi : E'.app i (hmn.trans hn) ≫ Fq.app i ((hi₉ i₈ (by simp)).trans hi) = Q.app i hk :=
    hQ i ((hi₉ m₁ (by simp)).trans hi)
  have hPi : E'.app i (hmn.trans hn) ≫ Fp.app i ((hi₉ i₇ (by simp)).trans hi) = P.app i hk :=
    hP i ((hi₉ m₂ (by simp)).trans hi)
  obtain ⟨inv₁, inv₂⟩ := inv i hn
  have hiso : IsIso (E.app i (hmn.trans hn)) := ⟨⟨_, inv₁, inv₂⟩⟩
  have key : pullback.lift _ _ (comm i hi) =
      E.app i (hmn.trans hn) ≫ pullback.lift (Q.app i hk) (P.app i hk) (comm' i hk) := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← hQi, ← Category.assoc,
        inv₁, Category.id_comp]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← hPi, ← Category.assoc,
        inv₁, Category.id_comp]
  rw [key]
  exact isClosedImmersion_comp B S hS _ _ (isClosedImmersion_of_isIso B S hS _) (closed' i hk)

/-- **The isomorphism at a stage where `X³` is the base change of `X³_i`.** If at a stage `i` the
component `a_i` is flat, the square `X³ = X⁴ ×_{X⁴_i} X³_i` is cartesian, and the morphism
`(q_i, p_i) : X¹_i ⟶ X²_i ×_{X⁴_i} X³_i` is a closed immersion, then that morphism is an
isomorphism: `X¹ = X² ×_{X²_i} (X²_i ×_{X⁴_i} X³_i)` is the base change of `X² ⟶ X²_i`, whose
scheme-theoretic image is all of `X²_i`, along a flat morphism, so its scheme-theoretic image is
all of `X²_i ×_{X⁴_i} X³_i` (Stacks 089E), and it lies in the closed subspace `X¹_i`. -/
theorem isIso_lift_of_isFlat (alg₂ : IsAlgebraicSpace B S hS X₂)
    (small : Cardinal.mk I < B.cutoff.ord.cof) (cart : IsPullback p q a b)
    (_overB : b ≫ pX₄ = pX₂)
    (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅) (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆)
    (Fp : SystemMorphism G₁ G₃ p i₇ h₁₇ h₃₇) (Fq : SystemMorphism G₁ G₂ q i₈ h₁₈ h₂₈)
    (i : I) (h₅ : i₅ ≤ i) (h₆ : i₆ ≤ i) (h₇ : i₇ ≤ i) (h₈ : i₈ ≤ i)
    (comm : Fq.app i h₈ ≫ Fb.app i h₆ = Fp.app i h₇ ≫ Fa.app i h₅)
    (flat : IsFlat B S hS (Fa.app i h₅))
    (base : IsPullback (stageπ G₃ i (h₃₅.trans h₅)) a (Fa.app i h₅)
      (stageπ G₄ i (h₄₅.trans h₅)))
    (closed : IsClosedImmersion B S hS (pullback.lift _ _ comm)) :
    IsIso (pullback.lift _ _ comm) := by
  set φ := pullback.lift _ _ comm
  have alg₂i := imageSystem_isAlgebraicSpace G₂ (Over.mk (homOfLE (h₂₆.trans h₆)).op)
  have alg₃i := imageSystem_isAlgebraicSpace G₃ (Over.mk (homOfLE (h₃₅.trans h₅)).op)
  have alg₄i := imageSystem_isAlgebraicSpace G₄ (Over.mk (homOfLE (h₄₅.trans h₅)).op)
  have algT := isAlgebraicSpace_pullback B S hS (Fb.app i h₆) (Fa.app i h₅) alg₂i alg₃i alg₄i
  -- the composite `X¹ ⟶ X²_i ×_{X⁴_i} X³_i`
  let χ : X₁ ⟶ pullback (Fb.app i h₆) (Fa.app i h₅) := stageπ G₁ i (h₁₈.trans h₈) ≫ φ
  have χ_fst : χ ≫ pullback.fst _ _ = q ≫ stageπ G₂ i (h₂₆.trans h₆) := by
    rw [Category.assoc, pullback.lift_fst, Fq.stageπ_app]
  have χ_snd : χ ≫ pullback.snd _ _ = p ≫ stageπ G₃ i (h₃₅.trans h₅) := by
    rw [Category.assoc, pullback.lift_snd, Fp.stageπ_app]
  -- `X¹` is the base change of `X² ⟶ X²_i` along `X²_i ×_{X⁴_i} X³_i ⟶ X²_i`
  have sq : IsPullback χ q (pullback.fst _ _) (stageπ G₂ i (h₂₆.trans h₆)) := by
    have s := cart.paste_horiz base
    rw [← χ_snd, ← Fb.stageπ_app i h₆] at s
    exact IsPullback.of_right s χ_fst (IsPullback.of_hasPullback (Fb.app i h₆) (Fa.app i h₅)).flip
  have flatFst : IsFlat B S hS (pullback.fst (Fb.app i h₆) (Fa.app i h₅)) :=
    isFlat_of_isPullback_of_isAlgebraicSpace B S hS
      (IsPullback.of_hasPullback (Fb.app i h₆) (Fa.app i h₅)) alg₃i alg₄i flat
  have qcπ : IsQuasiCompact B S hS (stageπ G₂ i (h₂₆.trans h₆)) :=
    isQuasiCompact_of_comp_mono B S hS _ _
      (by rw [toSchemeTheoreticImage_ι]; exact isQuasiCompact_stageMap G₂ small _)
  have himage : schemeTheoreticImageSubfunctor B S hS χ = ⊤ := by
    have he : sq.flip.isoPullback.hom ≫ pullback.snd _ _ = χ := sq.flip.isoPullback_hom_snd
    have : Epi sq.flip.isoPullback.hom := IsIso.epi_of_iso _
    rw [← he, schemeTheoreticImageSubfunctor_comp_of_epi B S hS sq.flip.isoPullback.hom,
      schemeTheoreticImageSubfunctor_pullback_snd_of_isFlat_of_isQuasiCompact' B S hS _ _
        algT alg₂i alg₂ flatFst qcπ]
    have htop : schemeTheoreticImageSubfunctor B S hS (stageπ G₂ i (h₂₆.trans h₆)) = ⊤ :=
      schemeTheoreticImageSubfunctor_toSchemeTheoreticImage_eq_top B S hS _
        (isAlgebraicSpace_stageTarget G₂ _)
    rw [htop]
    rfl
  have hmono : Mono φ := mono_of_isClosedImmersion B S hS _ closed
  have hrange : Subfunctor.range φ = ⊤ := by
    refine top_le_iff.1 (himage ▸ schemeTheoreticImageSubfunctor_le B S hS χ
      (isClosedSubspace_range_of_isClosedImmersion B S hS φ
        (imageSystem_isAlgebraicSpace G₁ _) closed) ?_)
    exact Subfunctor.range_comp_le _ _
  have hepi : Epi φ := (Subfunctor.epi_iff_range_eq_top φ).2 hrange
  exact isIso_of_mono_of_epi φ

/-- **Stacks 0CPF.** In Situation 0CP6, let
```
X₁ --p--> X₃
|q        |a
X₂ --b--> X₄
```
be a cartesian diagram of algebraic spaces over `B`, quasi-separated over `B`. For each
`j = 1, 2, 3, 4` let `G_j` be a diagram `X_j ⟶ W_j ⟶ B_{i_j}` as in Stacks 0CP8, with limit
description `X_j = lim_{i ≥ i_j} X^j_i` (Stacks 0CP9), and let `(a_i)_{i ≥ i₅}`, `(b_i)_{i ≥ i₆}`,
`(p_i)_{i ≥ i₇}`, `(q_i)_{i ≥ i₈}` be morphisms of these inverse systems inducing `a`, `b`, `p`,
`q`, as in Stacks 0CPA. Then there is an `i₉ ≥ i₅, i₆, i₇, i₈` such that for `i ≥ i₉` we have
`a_i ∘ p_i = b_i ∘ q_i` and `(q_i, p_i) : X¹_i ⟶ X²_i ×_{b_i, X⁴_i, a_i} X³_i` is a closed
immersion. If `a` is flat and of finite presentation (the source asks this of `a` and of `b`),
there is an `i₁₀ ≥ i₉` such that for `i ≥ i₁₀` this morphism is an isomorphism. -/
@[stacks 0CPF]
theorem exists_isClosedImmersion_lift_and_isIso (alg₁ : IsAlgebraicSpace B S hS X₁)
    (alg₂ : IsAlgebraicSpace B S hS X₂) (alg₃ : IsAlgebraicSpace B S hS X₃)
    (alg₄ : IsAlgebraicSpace B S hS X₄) (qs₁ : IsQuasiSeparated B S hS pX₁)
    (qs₃ : IsQuasiSeparated B S hS pX₃) (qs₄ : IsQuasiSeparated B S hS pX₄)
    (small : Cardinal.mk I < B.cutoff.ord.cof)
    (cart : IsPullback p q a b) (overA : a ≫ pX₄ = pX₃) (overB : b ≫ pX₄ = pX₂)
    (overQ : q ≫ pX₂ = pX₁)
    (Fa : SystemMorphism G₃ G₄ a i₅ h₃₅ h₄₅) (Fb : SystemMorphism G₂ G₄ b i₆ h₂₆ h₄₆)
    (Fp : SystemMorphism G₁ G₃ p i₇ h₁₇ h₃₇) (Fq : SystemMorphism G₁ G₂ q i₈ h₁₈ h₂₈) :
    ∃ (i₉ : I) (le₅ : i₅ ≤ i₉) (le₆ : i₆ ≤ i₉) (le₇ : i₇ ≤ i₉) (le₈ : i₈ ≤ i₉)
      (comm : ∀ (i : I) (le : i₉ ≤ i),
        Fp.app i (le₇.trans le) ≫ Fa.app i (le₅.trans le) =
          Fq.app i (le₈.trans le) ≫ Fb.app i (le₆.trans le)),
      (∀ (i : I) (le : i₉ ≤ i),
        IsClosedImmersion B S hS (pullback.lift _ _ (comm i le).symm)) ∧
      (IsFlat B S hS a → IsFinitePresentation B S hS a →
        ∃ i₁₀ : I, ∃ le₁₀ : i₉ ≤ i₁₀, ∀ (i : I) (le : i₁₀ ≤ i),
          IsIso (pullback.lift _ _ (comm i (le₁₀.trans le)).symm)) := by
  obtain ⟨i₉, le₅, le₆, le₇, le₈, comm, closed⟩ := exists_isClosedImmersion_lift alg₁ alg₄ qs₁ qs₄
    small cart overA overB overQ Fa Fb Fp Fq
  refine ⟨i₉, le₅, le₆, le₇, le₈, fun i hi => (comm i hi).symm, closed, fun flat fp => ?_⟩
  obtain ⟨i₃, -, hi₃⟩ := SystemMorphism.exists_isFlat_isPullback alg₃ alg₄ qs₃ qs₄ small Fa flat fp
  obtain ⟨i₁₀, h₉, h₃⟩ := exists_ge_ge i₉ i₃
  refine ⟨i₁₀, h₉, fun i hi => ?_⟩
  obtain ⟨flatᵢ, baseᵢ, -⟩ := hi₃ (Over.mk (homOfLE (le₅.trans (h₉.trans hi))).op) (h₃.trans hi)
  exact isIso_lift_of_isFlat alg₂ small cart overB Fa Fb Fp Fq i _ _ _ _
    (comm i (h₉.trans hi)) flatᵢ baseᵢ (closed i (h₉.trans hi))

end Main

end GoodDiagram

end AlgebraicGeometry.Space
