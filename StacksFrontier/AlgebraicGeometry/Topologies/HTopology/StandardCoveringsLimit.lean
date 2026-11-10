module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.ModuleSupport
public import StacksFrontier.AlgebraicGeometry.EssSurj.IsoDescentCompat
public import StacksFrontier.AlgebraicGeometry.LimitFPObjectDescent.Retract
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.BaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.ProperFinitePresentationRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.StandardCoverings

/-!
# Standard h coverings of a limit of affine schemes

Let an affine scheme `T` be the limit of a cofiltered inverse system of affine schemes `Tᵢ`.
Then the category of standard h coverings of `T` is the colimit over the system of the
categories of standard h coverings of the `Tᵢ`: every standard h covering of `T` is the base
change of one at a stage, every morphism between the base changes of two coverings of a stage
comes from a morphism at a later stage, and two morphisms at a stage which become equal at the
limit are already equal at a later stage.

## Main definitions

* `AlgebraicGeometry.pullback₂CompIso`: the canonical identification of the iterated base
  change of a family of morphisms, first along one morphism and then along another, with its
  direct base change along the composite.

## Main results

* `AlgebraicGeometry.exists_isStandardHCovering_model_of_isLimit`: **Stacks 0EV2 part (1)**, a
  standard h covering of the limit is the base change of a standard h covering at a stage.
* `AlgebraicGeometry.exists_hom_isStandardHCovering_model_of_isLimit`: **Stacks 0EV2 part
  (2)**, a morphism between the base changes to the limit of two standard h coverings of a
  stage is the base change of a morphism between their base changes to a later stage.
* `AlgebraicGeometry.eventually_eq_hom_isStandardHCovering_of_isLimit`: **Stacks 0EV2 part
  (3)**, two morphisms of standard h coverings of a stage whose base changes to the limit agree
  already agree after base change to a later stage.

## Implementation notes

A directed inverse system is represented, as elsewhere in this development, by a functor out of
an essentially small cofiltered category; smallness is relative to the scheme universe because
the source's directed set lies in the same ambient universe as the schemes. Families of
morphisms with a fixed target are `CategoryTheory.PreZeroHypercover`, their base change is
`CategoryTheory.PreZeroHypercover.pullback₂`, morphisms of families are
`CategoryTheory.PreZeroHypercover.Hom`, and the base change of a morphism of families is
`CategoryTheory.PreZeroHypercover.Hom.pullback₂`. The three parts are therefore stated for
`AlgebraicGeometry.IsStandardHCovering` of the members of a `PreZeroHypercover`, which is the
form in which the source states Definition 0EUY. In parts (2) and (3) "base change to the
limit" of a morphism at a stage means its base change followed by the canonical identification
`AlgebraicGeometry.pullback₂CompIso` of the iterated base change with the direct one.

Part (1) is reduced to an index category in the scheme universe through
`CategoryTheory.equivSmallModel`, because the descent statements it uses for individual schemes
are stated there. The covering of the limit is first refined, by Stacks 0ETU, by a finite
affine open covering of a single proper surjection of finite presentation; both the members of
the covering and that proper surjection descend to a stage, the former by Stacks 01ZM part (1)
together with Stacks 01Z6 for affineness and the latter by Stacks 081F and Stacks 07RR for
properness and surjectivity, and the refinement morphisms descend by Stacks 01ZM part (2).
Parts (2) and (3) are Stacks 01ZM parts (2) and (3) applied index by index, with
`CategoryTheory.IsCofiltered.wideCospan` providing a lower bound for the finitely many stages
so obtained.

The diagram of base changes of a scheme over one stage to the later stages is a functor out of
the over category of that stage, so that "later stage" is a morphism to it; its reductions are
recorded as separate `rfl` lemmas rather than unfolded by `dsimp`, because the composite
functor defining it blocks instance synthesis on the unreduced form.

## References

* [Stacks Project, Tag 0EV2](https://stacks.math.columbia.edu/tag/0EV2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w w'

namespace AlgebraicGeometry

/-! ### Base change of a family of morphisms along a composite -/

section Comparison

variable {S S' T : Scheme.{u}}

/-- The canonical identification of the iterated base change of a family of morphisms with
fixed target, first along `p : S ⟶ T` and then along `q : S' ⟶ S`, with its direct base change
along the composite `r = q ≫ p`. -/
public noncomputable def pullback₂CompIso (p : S ⟶ T) (q : S' ⟶ S) (r : S' ⟶ T)
    (h : q ≫ p = r) (E : PreZeroHypercover.{v} T) :
    (E.pullback₂ p).pullback₂ q ≅ E.pullback₂ r :=
  PreZeroHypercover.isoMk (Equiv.refl E.I₀)
    (fun k ↦ (Over.forget S').mapIso (overPullbackCompIso p q r h (Over.mk (E.f k))))
    (fun k ↦ (overPullbackCompIso p q r h (Over.mk (E.f k))).hom.w)

/-- The identification of iterated with direct base change is compatible with the first
pullback projections, which pins it down. -/
public lemma pullback₂CompIso_hom_fst (p : S ⟶ T) (q : S' ⟶ S) (r : S' ⟶ T) (h : q ≫ p = r)
    (E : PreZeroHypercover.{v} T) (k : E.I₀) :
    (pullback₂CompIso p q r h E).hom.h₀ k ≫ pullback.fst (E.f k) r =
      pullback.fst (pullback.snd (E.f k) p) q ≫ pullback.fst (E.f k) p :=
  overPullbackCompIso_fst p q r h (Over.mk (E.f k))

/-- The identification of iterated with direct base change commutes with the projections to the
new target. -/
public lemma pullback₂CompIso_hom_snd (p : S ⟶ T) (q : S' ⟶ S) (r : S' ⟶ T) (h : q ≫ p = r)
    (E : PreZeroHypercover.{v} T) (k : E.I₀) :
    (pullback₂CompIso p q r h E).hom.h₀ k ≫ pullback.snd (E.f k) r =
      pullback.snd (pullback.snd (E.f k) p) q :=
  (overPullbackCompIso p q r h (Over.mk (E.f k))).hom.w

end Comparison

/-- Two morphisms of families of morphisms agree as soon as their index maps agree and their
components agree up to the resulting transport. This is
`CategoryTheory.PreZeroHypercover.Hom.ext'` with the transport expressed by `HEq` rather than
by `CategoryTheory.eqToHom`, which is what a component-by-component computation produces. -/
private lemma hom_eq_of_s₀_eq_of_heq {C : Type*} [Category C] {S : C}
    {E : PreZeroHypercover.{v} S} {F : PreZeroHypercover.{w} S} {a b : E.Hom F}
    (hs : a.s₀ = b.s₀) (hh : ∀ k, HEq (a.h₀ k) (b.h₀ k)) : a = b := by
  obtain ⟨as, ah, aw⟩ := a
  obtain ⟨bs, bh, bw⟩ := b
  have hs' : as = bs := hs
  subst hs'
  have hh' : ah = bh := funext fun k ↦ eq_of_heq (hh k)
  subst hh'
  rfl

/-! ### Bookkeeping for base change of morphism properties -/

/-- The first projection of a fibre product is a base change of the second morphism, so it
inherits any property stable under base change. -/
private lemma property_pullback_fst (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (hg : P g) :
    P (pullback.fst f g) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g).flip hg

private lemma finitePresentation_over_comp {R S T : Scheme.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (hf : FinitePresentation f) (hg : FinitePresentation g) : FinitePresentation (f ≫ g) := by
  have := hf.1
  have := hf.2.1
  have := hf.2.2
  have := hg.1
  have := hg.2.1
  have := hg.2.2
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-! ### The diagram of base changes of a scheme over a stage -/

section Diagram

variable {I : Type v} [Category.{w} I] (D : I ⥤ Scheme.{u})

/-- The diagram of base changes of a scheme over one stage to the later stages. -/
private noncomputable def baseChangeStageDiagram (i : I) (X : Over (D.obj i)) :
    Over i ⥤ Scheme.{u} :=
  Over.post D ⋙ Over.pullback X.hom ⋙ Over.forget X.left

private lemma baseChangeStageDiagram_obj (i : I) (X : Over (D.obj i)) (j : Over i) :
    (baseChangeStageDiagram D i X).obj j = pullback (D.map j.hom) X.hom := rfl

private lemma baseChangeStageDiagram_map_fst (i : I) (X : Over (D.obj i)) {j k : Over i}
    (e : j ⟶ k) :
    (baseChangeStageDiagram D i X).map e ≫ pullback.fst (D.map k.hom) X.hom =
      pullback.fst (D.map j.hom) X.hom ≫ D.map e.left :=
  overPullback_map_left_fst X.hom ((Over.post D).map e)

private lemma baseChangeStageDiagram_map_snd (i : I) (X : Over (D.obj i)) {j k : Over i}
    (e : j ⟶ k) :
    (baseChangeStageDiagram D i X).map e ≫ pullback.snd (D.map k.hom) X.hom =
      pullback.snd (D.map j.hom) X.hom :=
  overPullback_map_left_snd X.hom ((Over.post D).map e)

private lemma isAffineHom_baseChangeStageDiagram_map
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)] (i : I) (X : Over (D.obj i))
    {j k : Over i} (e : j ⟶ k) : IsAffineHom ((baseChangeStageDiagram D i X).map e) := by
  have hw : D.map e.left ≫ D.map k.hom = D.map j.hom := by rw [← D.map_comp, Over.w e]
  have outer : IsPullback
      ((baseChangeStageDiagram D i X).map e ≫ pullback.snd (D.map k.hom) X.hom)
      (pullback.fst (D.map j.hom) X.hom) X.hom (D.map e.left ≫ D.map k.hom) := by
    rw [baseChangeStageDiagram_map_snd, hw]
    exact (IsPullback.of_hasPullback (D.map j.hom) X.hom).flip
  exact MorphismProperty.of_isPullback (P := @IsAffineHom)
    (outer.of_right (baseChangeStageDiagram_map_fst D i X e)
      (IsPullback.of_hasPullback (D.map k.hom) X.hom).flip).flip inferInstance

/-- The cone on `AlgebraicGeometry.baseChangeStageDiagram` whose point is the base change to
the limit. -/
private noncomputable def baseChangeStageCone (c : Cone D) (i : I) (X : Over (D.obj i)) :
    Cone (baseChangeStageDiagram D i X) :=
  (Over.pullback X.hom ⋙ Over.forget X.left).mapCone ((Over.conePost D i).obj c)

private lemma baseChangeStageCone_pt (c : Cone D) (i : I) (X : Over (D.obj i)) :
    (baseChangeStageCone D c i X).pt = pullback (c.π.app i) X.hom := rfl

private lemma baseChangeStageCone_π_fst (c : Cone D) (i : I) (X : Over (D.obj i))
    (k : Over i) :
    (baseChangeStageCone D c i X).π.app k ≫ pullback.fst (D.map k.hom) X.hom =
      pullback.fst (c.π.app i) X.hom ≫ c.π.app k.left :=
  overPullback_map_left_fst X.hom (((Over.conePost D i).obj c).π.app k)

private lemma baseChangeStageCone_π_snd (c : Cone D) (i : I) (X : Over (D.obj i))
    (k : Over i) :
    (baseChangeStageCone D c i X).π.app k ≫ pullback.snd (D.map k.hom) X.hom =
      pullback.snd (c.π.app i) X.hom :=
  overPullback_map_left_snd X.hom (((Over.conePost D i).obj c).π.app k)

private noncomputable def isLimitBaseChangeStageCone [IsCofiltered I] (c : Cone D)
    (hc : IsLimit c) (i : I) (X : Over (D.obj i)) :
    IsLimit (baseChangeStageCone D c i X) :=
  isLimitOfPreserves _ (Over.isLimitConePost i hc)

private lemma isPullback_baseChangeStageCone (c : Cone D) (i : I) (X : Over (D.obj i))
    (k : Over i) :
    IsPullback ((baseChangeStageCone D c i X).π.app k)
      (pullback.fst (c.π.app i) X.hom) (pullback.fst (D.map k.hom) X.hom)
      (c.π.app k.left) := by
  have outer : IsPullback
      ((baseChangeStageCone D c i X).π.app k ≫ pullback.snd (D.map k.hom) X.hom)
      (pullback.fst (c.π.app i) X.hom) X.hom (c.π.app k.left ≫ D.map k.hom) := by
    rw [baseChangeStageCone_π_snd, c.w]
    exact (IsPullback.of_hasPullback (c.π.app i) X.hom).flip
  exact outer.of_right (baseChangeStageCone_π_fst D c i X k)
    (IsPullback.of_hasPullback (D.map k.hom) X.hom).flip

/-- Quasi-compactness of the base change of a scheme over a stage, to any later stage. -/
private lemma compactSpace_baseChangeStageDiagram_obj [∀ i, CompactSpace (D.obj i)] (i : I)
    (X : Over (D.obj i)) [QuasiCompact X.hom] (j : Over i) :
    CompactSpace ((baseChangeStageDiagram D i X).obj j) := by
  rw [baseChangeStageDiagram_obj]
  have : QuasiCompact (pullback.fst (D.map j.hom) X.hom) :=
    property_pullback_fst _ _ _ ‹QuasiCompact X.hom›
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst (D.map j.hom) X.hom)

private lemma quasiSeparatedSpace_baseChangeStageDiagram_obj
    [∀ i, QuasiSeparatedSpace (D.obj i)] (i : I) (X : Over (D.obj i)) [QuasiSeparated X.hom]
    (j : Over i) : QuasiSeparatedSpace ((baseChangeStageDiagram D i X).obj j) := by
  rw [baseChangeStageDiagram_obj]
  have : QuasiSeparated (pullback.fst (D.map j.hom) X.hom) :=
    property_pullback_fst _ _ _ ‹QuasiSeparated X.hom›
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.map j.hom) X.hom)

end Diagram

/-! ### The canonical projections between base changes -/

section Projections

variable {I : Type v} [Category.{w} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- The canonical morphism from the base change to the limit of a scheme over a stage to its
base change to an intermediate stage. -/
private noncomputable def limitStageProjection (i : I) (X : Over (D.obj i)) {j : I}
    (e : j ⟶ i) :
    ((Over.pullback (c.π.app i)).obj X).left ⟶ ((Over.pullback (D.map e)).obj X).left :=
  pullback.lift (pullback.fst X.hom (c.π.app i))
    (pullback.snd X.hom (c.π.app i) ≫ c.π.app j)
    (by simp [Category.assoc, c.w, pullback.condition])

private lemma limitStageProjection_eq (i : I) (X : Over (D.obj i)) {j : I} (e : j ⟶ i) :
    limitStageProjection D c i X e =
      (overPullbackCompIso (D.map e) (c.π.app j) (c.π.app i) (c.w e) X).inv.left ≫
        pullback.fst ((Over.pullback (D.map e)).obj X).hom (c.π.app j) := by
  apply pullback.hom_ext
  · simpa only [limitStageProjection, pullback.lift_fst, Category.assoc] using
      (overPullbackCompIso_inv_fst (D.map e) (c.π.app j) (c.π.app i) (c.w e) X).symm
  · simp only [limitStageProjection, pullback.lift_snd, Category.assoc]
    simpa [Over.pullback, Category.assoc, pullback.condition] using
      (congrArg (fun h ↦ h ≫ c.π.app j)
        (overPullbackCompIso (D.map e) (c.π.app j) (c.π.app i) (c.w e) X).inv.w).symm

/-- The canonical morphism between the base changes of a scheme over a stage to two later
stages, one factoring through the other. -/
private noncomputable def stageProjection (i : I) (X : Over (D.obj i)) {j k : I} (e : j ⟶ i)
    (b : k ⟶ j) (d : k ⟶ i) (hd : b ≫ e = d) :
    ((Over.pullback (D.map d)).obj X).left ⟶ ((Over.pullback (D.map e)).obj X).left :=
  pullback.lift (pullback.fst X.hom (D.map d)) (pullback.snd X.hom (D.map d) ≫ D.map b)
    (by simp [Category.assoc, ← D.map_comp, hd, pullback.condition])

private lemma stageProjection_structure (i : I) (X : Over (D.obj i)) {j k : I} (e : j ⟶ i)
    (b : k ⟶ j) (d : k ⟶ i) (hd : b ≫ e = d) :
    stageProjection D i X e b d hd ≫
        (pullback.snd X.hom (D.map e) ≫ D.map e) =
      pullback.snd X.hom (D.map d) ≫ D.map d := by
  rw [← Category.assoc, stageProjection, pullback.lift_snd, Category.assoc, ← D.map_comp, hd]

private lemma limitStageProjection_stageProjection (i : I) (X : Over (D.obj i)) {j k : I}
    (e : j ⟶ i) (b : k ⟶ j) (d : k ⟶ i) (hd : b ≫ e = d) :
    limitStageProjection D c i X d ≫ stageProjection D i X e b d hd =
      limitStageProjection D c i X e := by
  apply pullback.hom_ext
  · simp only [limitStageProjection, stageProjection, Category.assoc, pullback.lift_fst]
  · simp only [limitStageProjection, stageProjection, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, c.w]

end Projections

/-! ### Descending affine schemes of finite presentation -/

section AffineModels

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ i, IsAffine (D.obj i)] (c : Cone D)

/-- An affine scheme of finite presentation over the limit of a cofiltered system of affine
schemes is the base change of an affine scheme of finite presentation over a stage. -/
private lemma exists_isAffine_finitePresentation_model (hc : IsLimit c) (X : Over c.pt)
    [IsAffine X.left] (hX : FinitePresentation X.hom) :
    ∃ (i : I) (Y : Over (D.obj i)), IsAffine Y.left ∧ FinitePresentation Y.hom ∧
      Nonempty ((Over.pullback (c.π.app i)).obj Y ≅ X) := by
  have : ∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e) := fun _ ↦ inferInstance
  have : ∀ i, CompactSpace (D.obj i) := fun _ ↦ inferInstance
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := fun _ ↦ inferInstance
  obtain ⟨i, Y, hY, ⟨α⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation D c hc X hX
  have hαinv : IsIso α.inv.left := by
    change IsIso ((Over.forget c.pt).map α.inv)
    infer_instance
  have : LocallyOfFinitePresentation Y.hom := hY.1
  have : QuasiCompact Y.hom := hY.2.1
  have : QuasiSeparated Y.hom := hY.2.2
  have : ∀ j, CompactSpace ((baseChangeStageDiagram D i Y).obj j) :=
    compactSpace_baseChangeStageDiagram_obj D i Y
  have : ∀ j, QuasiSeparatedSpace ((baseChangeStageDiagram D i Y).obj j) :=
    quasiSeparatedSpace_baseChangeStageDiagram_obj D i Y
  have : ∀ {j k : Over i} (e : j ⟶ k), IsAffineHom ((baseChangeStageDiagram D i Y).map e) :=
    fun e ↦ isAffineHom_baseChangeStageDiagram_map D i Y e
  have : IsAffine (baseChangeStageCone D c i Y).pt := by
    rw [baseChangeStageCone_pt]
    exact IsAffine.of_isIso ((pullbackSymmetry (c.π.app i) Y.hom).hom ≫ α.inv.left)
  obtain ⟨j, hj⟩ := Scheme.exists_isAffine_of_isLimit (baseChangeStageDiagram D i Y)
    (baseChangeStageCone D c i Y) (isLimitBaseChangeStageCone D c hc i Y)
  rw [baseChangeStageDiagram_obj] at hj
  have : IsAffine ((Over.pullback (D.map j.hom)).obj Y).left :=
    IsAffine.of_isIso (pullbackSymmetry Y.hom (D.map j.hom)).hom
  exact ⟨j.left, (Over.pullback (D.map j.hom)).obj Y, inferInstance,
    LimitFPObjectDescent.finitePresentation_overPullback _ Y hY,
    ⟨overPullbackCompIso _ _ _ (c.w j.hom) Y ≪≫ α.symm⟩⟩

/-- Finitely many affine schemes of finite presentation over the limit descend to one common
stage. -/
private lemma exists_isAffine_finitePresentation_models (hc : IsLimit c) {K : Type*} [Finite K]
    (X : K → Over c.pt) [∀ k, IsAffine (X k).left]
    (hX : ∀ k, FinitePresentation (X k).hom) :
    ∃ (i : I) (Y : K → Over (D.obj i)), (∀ k, IsAffine (Y k).left) ∧
      (∀ k, FinitePresentation (Y k).hom) ∧
      Nonempty (∀ k, (Over.pullback (c.π.app i)).obj (Y k) ≅ X k) := by
  classical
  choose levels models haff hfp iso using fun k ↦
    exists_isAffine_finitePresentation_model D c hc (X k) (hX k)
  cases nonempty_fintype K
  obtain ⟨i, arrows⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image levels)
  let maps (k : K) : i ⟶ levels k := (arrows (by simp)).some
  refine ⟨i, fun k ↦ (Over.pullback (D.map (maps k))).obj (models k), fun k ↦ ?_,
    fun k ↦ LimitFPObjectDescent.finitePresentation_overPullback _ _ (hfp k), ?_⟩
  · have : IsAffine (models k).left := haff k
    change IsAffine (pullback (models k).hom (D.map (maps k)))
    exact isAffine_of_isAffineHom (pullback.fst _ _)
  · exact ⟨fun k ↦ overPullbackCompIso _ _ _ (c.w (maps k)) (models k) ≪≫ (iso k).some⟩

end AffineModels

/-! ### Descending proper surjections of finite presentation -/

section ProperSurjectiveModels

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ i, IsAffine (D.obj i)] (c : Cone D)

/-- The structure morphism of a scheme over a stage whose base change to the limit is proper is
proper after base change to some later stage. -/
private lemma exists_isProper_stage (hc : IsLimit c) (i : I) (Y : Over (D.obj i))
    (hY : FinitePresentation Y.hom)
    [IsProper ((Over.pullback (c.π.app i)).obj Y).hom] :
    ∃ (j : I) (e : j ⟶ i), IsProper ((Over.pullback (D.map e)).obj Y).hom := by
  have : LocallyOfFinitePresentation Y.hom := hY.1
  have : QuasiCompact Y.hom := hY.2.1
  have : QuasiSeparated Y.hom := hY.2.2
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have : ∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e) := fun _ ↦ inferInstance
  let Z : Over (D.obj i) := Over.mk (𝟙 _)
  have : CompactSpace Z.left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace Z.left := inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  let f : Y ⟶ Z := Over.homMk Y.hom
  have : LocallyOfFiniteType f.left := inferInstanceAs (LocallyOfFiniteType Y.hom)
  have : IsProper ((Over.pullback (c.π.app i)).map f).left :=
    (overPullback_map_terminal_iff @IsProper _ Y).mpr ‹_›
  obtain ⟨j, e, he⟩ := exists_isProper_baseChange_of_isLimit D c i hc Y Z f
  exact ⟨j, e, (overPullback_map_terminal_iff @IsProper _ Y).mp he⟩

/-- The structure morphism of a scheme over a stage whose base change to the limit is
surjective is surjective after base change to some later stage. -/
private lemma exists_surjective_stage (hc : IsLimit c) (i : I) (Y : Over (D.obj i))
    (hY : FinitePresentation Y.hom)
    [Surjective ((Over.pullback (c.π.app i)).obj Y).hom] :
    ∃ (j : I) (e : j ⟶ i), Surjective ((Over.pullback (D.map e)).obj Y).hom := by
  have : LocallyOfFinitePresentation Y.hom := hY.1
  have : QuasiCompact Y.hom := hY.2.1
  have : QuasiSeparated Y.hom := hY.2.2
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have : ∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e) := fun _ ↦ inferInstance
  let Z : Over (D.obj i) := Over.mk (𝟙 _)
  have : CompactSpace Z.left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace Z.left := inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  let f : Y ⟶ Z := Over.homMk Y.hom
  have : LocallyOfFinitePresentation f.left :=
    inferInstanceAs (LocallyOfFinitePresentation Y.hom)
  have : Surjective ((Over.pullback (c.π.app i)).map f).left :=
    (overPullback_map_terminal_iff @Surjective _ Y).mpr ‹_›
  obtain ⟨j, e, he⟩ :=
    exists_surjective_baseChange_of_surjective_limitBaseChange D c hc i Y Z f
  exact ⟨j, e, (overPullback_map_terminal_iff @Surjective _ Y).mp he⟩

/-- A proper surjection of finite presentation onto the limit is the base change of a proper
surjection of finite presentation onto a stage. -/
private lemma exists_isProper_surjective_finitePresentation_model (hc : IsLimit c)
    (X : Over c.pt) (hX : FinitePresentation X.hom) [IsProper X.hom] [Surjective X.hom] :
    ∃ (i : I) (Y : Over (D.obj i)), FinitePresentation Y.hom ∧ IsProper Y.hom ∧
      Surjective Y.hom ∧ Nonempty ((Over.pullback (c.π.app i)).obj Y ≅ X) := by
  have : ∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e) := fun _ ↦ inferInstance
  have : ∀ i, CompactSpace (D.obj i) := fun _ ↦ inferInstance
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := fun _ ↦ inferInstance
  obtain ⟨i, Y, hY, ⟨α⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation D c hc X hX
  have hαinv : IsIso α.inv.left := by
    change IsIso ((Over.forget c.pt).map α.inv)
    infer_instance
  have : IsProper ((Over.pullback (c.π.app i)).obj Y).hom := by
    rw [← α.inv.w]
    infer_instance
  have : Surjective ((Over.pullback (c.π.app i)).obj Y).hom := by
    rw [← α.inv.w]
    infer_instance
  obtain ⟨j, e, hp⟩ := exists_isProper_stage D c hc i Y hY
  have : IsProper ((Over.pullback (D.map e)).obj Y).hom := hp
  let β : (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj Y) ≅ X :=
    overPullbackCompIso _ _ _ (c.w e) Y ≪≫ α.symm
  have hβ : IsIso β.hom.left := by
    change IsIso ((Over.forget c.pt).map β.hom)
    infer_instance
  have : Surjective ((Over.pullback (c.π.app j)).obj
      ((Over.pullback (D.map e)).obj Y)).hom := by
    rw [← β.hom.w]
    infer_instance
  obtain ⟨k, b, hs⟩ := exists_surjective_stage D c hc j ((Over.pullback (D.map e)).obj Y)
    (LimitFPObjectDescent.finitePresentation_overPullback _ Y hY)
  have : IsProper ((Over.pullback (D.map b)).obj
      ((Over.pullback (D.map e)).obj Y)).hom := by
    change IsProper (pullback.snd ((Over.pullback (D.map e)).obj Y).hom (D.map b))
    infer_instance
  exact ⟨k, (Over.pullback (D.map b)).obj ((Over.pullback (D.map e)).obj Y),
    LimitFPObjectDescent.finitePresentation_overPullback _ _
      (LimitFPObjectDescent.finitePresentation_overPullback _ Y hY),
    inferInstance, hs,
    ⟨overPullbackCompIso _ _ _ (c.w b) ((Over.pullback (D.map e)).obj Y) ≪≫ β⟩⟩

end ProperSurjectiveModels

/-! ### Descending morphisms between schemes of finite presentation -/

section MorphismModels

variable {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (D : I ⥤ Scheme.{u}) (c : Cone D)
  [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]

/-- Stacks 01ZM part (2), with the two comparison isomorphisms identified as the canonical
ones. -/
private lemma exists_morphism_model_canonical (hc : IsLimit c) (i : I) (X Y : Over (D.obj i))
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom)
    (f : (Over.pullback (c.π.app i)).obj X ⟶ (Over.pullback (c.π.app i)).obj Y) :
    ∃ (j : I) (e : j ⟶ i)
      (g : (Over.pullback (D.map e)).obj X ⟶ (Over.pullback (D.map e)).obj Y),
      (overPullbackCompIso (D.map e) (c.π.app j) (c.π.app i) (c.w e) X).hom ≫ f =
        (Over.pullback (c.π.app j)).map g ≫
          (overPullbackCompIso (D.map e) (c.π.app j) (c.π.app i) (c.w e) Y).hom := by
  obtain ⟨j, e, g, α, β, hα, hβ, hfg⟩ :=
    exists_morphism_after_baseChange D c hc i X Y hX hY f
  rw [iso_eq_overPullbackCompIso _ _ _ (c.w e) X α hα,
    iso_eq_overPullbackCompIso _ _ _ (c.w e) Y β hβ] at hfg
  exact ⟨j, e, g, hfg⟩

/-- Stacks 01ZM part (2), recorded as a morphism to the target itself compatible with the
canonical projection from the base change to the limit. -/
private lemma exists_morphism_projection_model (hc : IsLimit c) (i : I)
    (X Y : Over (D.obj i)) (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom)
    (f : (Over.pullback (c.π.app i)).obj X ⟶ (Over.pullback (c.π.app i)).obj Y) :
    ∃ (j : I) (e : j ⟶ i) (h : ((Over.pullback (D.map e)).obj X).left ⟶ Y.left),
      h ≫ Y.hom = ((Over.pullback (D.map e)).obj X).hom ≫ D.map e ∧
        limitStageProjection D c i X e ≫ h = f.left ≫ pullback.fst Y.hom (c.π.app i) := by
  obtain ⟨j, e, g, hg⟩ := exists_morphism_model_canonical D c hc i X Y hX hY f
  refine ⟨j, e, g.left ≫ pullback.fst Y.hom (D.map e), ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun h ↦ h ≫ D.map e) g.w
  · have hf : f = (overPullbackCompIso (D.map e) (c.π.app j) (c.π.app i) (c.w e) X).inv ≫
        (Over.pullback (c.π.app j)).map g ≫
          (overPullbackCompIso (D.map e) (c.π.app j) (c.π.app i) (c.w e) Y).hom := by
      rw [← hg, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rw [limitStageProjection_eq, hf]
    simp only [Over.comp_left, Category.assoc, overPullbackCompIso_fst,
      overPullback_map_left_fst_assoc]

/-- Finitely many morphisms between base changes to the limit descend to one common stage. -/
private lemma exists_finite_morphism_projection_model (hc : IsLimit c) (i : I) {K : Type*}
    [Finite K] (X Y : K → Over (D.obj i)) (hX : ∀ k, FinitePresentation (X k).hom)
    (hY : ∀ k, FinitePresentation (Y k).hom)
    (f : ∀ k, (Over.pullback (c.π.app i)).obj (X k) ⟶
      (Over.pullback (c.π.app i)).obj (Y k)) :
    ∃ (j : I) (e : j ⟶ i)
      (h : ∀ k, ((Over.pullback (D.map e)).obj (X k)).left ⟶ (Y k).left),
      (∀ k, h k ≫ (Y k).hom = ((Over.pullback (D.map e)).obj (X k)).hom ≫ D.map e) ∧
        ∀ k, limitStageProjection D c i (X k) e ≫ h k =
          (f k).left ≫ pullback.fst (Y k).hom (c.π.app i) := by
  classical
  choose lev arr maps hmaps hlim using fun k ↦
    exists_morphism_projection_model D c hc i (X k) (Y k) (hX k) (hY k) (f k)
  obtain ⟨j, e, b, hb⟩ := IsCofiltered.wideCospan arr
  refine ⟨j, e, fun k ↦ stageProjection D i (X k) (arr k) (b k) e (hb k) ≫ maps k, ?_, ?_⟩
  · intro k
    rw [Category.assoc, hmaps k]
    exact stageProjection_structure D i (X k) (arr k) (b k) e (hb k)
  · intro k
    rw [← Category.assoc, limitStageProjection_stageProjection, hlim]

end MorphismModels

/-! ### Part (1): descending a standard h covering -/

section Part1

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ i, IsAffine (D.obj i)] (c : Cone D)

/-- The data exhibiting an h covering of the limit as refined by the affine opens of a proper
surjection of finite presentation descends to a standard ph covering of a stage. -/
private lemma exists_standardPHCovering_model (hc : IsLimit c) {K : Type*} [Finite K]
    (Y : Over c.pt) (hY : FinitePresentation Y.hom) [IsProper Y.hom] [Surjective Y.hom]
    (V : K → Scheme.{u}) [∀ k, IsAffine (V k)] (j : ∀ k, V k ⟶ Y.left)
    [∀ k, IsOpenImmersion (j k)] (hcover : (⋃ k, Set.range (j k)) = Set.univ) :
    ∃ (i : I) (X : K → Scheme.{u}) (f : ∀ k, X k ⟶ D.obj i), StandardPHCovering f ∧
      (∀ k, FinitePresentation (f k)) ∧
      Nonempty (∀ k : K, (Over.pullback (c.π.app i)).obj (Over.mk (f k)) ≅
        Over.mk (j k ≫ Y.hom)) := by
  classical
  obtain ⟨i, Z, hZ, hp, hs, ⟨α⟩⟩ :=
    exists_isProper_surjective_finitePresentation_model D c hc Y hY
  have : LocallyOfFinitePresentation Z.hom := hZ.1
  have : QuasiCompact Z.hom := hZ.2.1
  have : QuasiSeparated Z.hom := hZ.2.2
  have : IsProper Z.hom := hp
  have : Surjective Z.hom := hs
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  have : ∀ {k l : I} (e : k ⟶ l), IsAffineHom (D.map e) := fun _ ↦ inferInstance
  have : ∀ k, CompactSpace ((baseChangeStageDiagram D i Z).obj k) :=
    compactSpace_baseChangeStageDiagram_obj D i Z
  have : ∀ k, QuasiSeparatedSpace ((baseChangeStageDiagram D i Z).obj k) :=
    quasiSeparatedSpace_baseChangeStageDiagram_obj D i Z
  have : ∀ {k l : Over i} (e : k ⟶ l), IsAffineHom ((baseChangeStageDiagram D i Z).map e) :=
    fun e ↦ isAffineHom_baseChangeStageDiagram_map D i Z e
  let γ : (baseChangeStageCone D c i Z).pt ≅ Y.left :=
    pullbackSymmetry (c.π.app i) Z.hom ≪≫ (Over.forget c.pt).mapIso α
  let maps (k : K) : V k ⟶ (baseChangeStageCone D c i Z).pt := j k ≫ γ.inv
  have hopen : ∀ k, IsOpenImmersion (maps k) := fun k ↦ by dsimp [maps]; infer_instance
  have hcov : TopologicalSpace.IsOpenCover (fun k ↦ (maps k).opensRange) := by
    apply TopologicalSpace.Opens.ext
    simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
    apply Set.eq_univ_of_forall
    intro x
    have hx : γ.hom x ∈ ⋃ k, Set.range (j k) := by rw [hcover]; trivial
    obtain ⟨k, y, hy⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨k, y, ?_⟩
    simp only [maps, Scheme.Hom.comp_apply, hy]
    simp
  obtain ⟨k, U, hU, hUa⟩ := Scheme.exists_isOpenCover_and_isAffine_of_finite
    (baseChangeStageDiagram D i Z) (baseChangeStageCone D c i Z)
    (isLimitBaseChangeStageCone D c hc i Z) (fun k ↦ (maps k).opensRange) hcov
    (fun k ↦ isAffineOpen_opensRange (maps k))
  let q : (baseChangeStageDiagram D i Z).obj k ⟶ D.obj k.left :=
    pullback.fst (D.map k.hom) Z.hom
  let W : PreZeroHypercover (D.obj k.left) :=
    { I₀ := K, X := fun t ↦ U t, f := fun t ↦ (U t).ι ≫ q }
  have hqp : IsProper q := property_pullback_fst _ _ _ ‹IsProper Z.hom›
  have hqs : Surjective q := property_pullback_fst _ _ _ ‹Surjective Z.hom›
  have hq : FinitePresentation q := finitePresentation_pullback_fst _ _ hZ
  have haffU : ∀ t, IsAffine (W.X t) := fun t ↦ (hUa t).1
  have hfp (t : K) : FinitePresentation (W.f t) :=
    finitePresentation_over_comp (U t).ι q
      ((finitePresentation_iff_quasiCompact_of_isOpenImmersion _).mpr
        (by have : IsAffine (U t).toScheme := (hUa t).1; infer_instance)) hq
  refine ⟨k.left, W.X, W.f, ?_, hfp, ?_⟩
  · refine StandardPHCovering.of_presentation W.f (fun t ↦ haffU t) q (fun t ↦ (U t).ι)
      hqp hqs (fun t ↦ inferInstance) ?_ (fun _ ↦ rfl)
    change (⋃ t : K, Set.range (U t).ι) = Set.univ
    convert hU.iSup_set_eq_univ using 1
    congr 1
    funext t
    exact Scheme.Opens.range_ι (U t)
  · refine ⟨fun t ↦ ?_⟩
    let B : (baseChangeStageCone D c i Z).pt.Opens :=
      (baseChangeStageCone D c i Z).π.app k ⁻¹ᵁ U t
    have hrange : Set.range B.ι = Set.range (maps t) := by
      rw [Scheme.Opens.range_ι]
      exact congrArg SetLike.coe (hUa t).2.symm
    let ε : (B : Scheme) ≅ V t := IsOpenImmersion.isoOfRangeEq B.ι (maps t) hrange
    have square := (isPullback_morphismRestrict
      ((baseChangeStageCone D c i Z).π.app k) (U t)).paste_vert
      (isPullback_baseChangeStageCone D c i Z k)
    let δ : pullback (W.f t) (c.π.app k.left) ≅ V t := square.isoPullback.symm ≪≫ ε
    refine Over.isoMk δ ?_
    change δ.hom ≫ j t ≫ Y.hom = pullback.snd (W.f t) (c.π.app k.left)
    have hγ : γ.hom ≫ Y.hom = pullback.fst (c.π.app i) Z.hom := by
      change ((pullbackSymmetry (c.π.app i) Z.hom).hom ≫ α.hom.left) ≫ Y.hom = _
      rw [Category.assoc, α.hom.w]
      exact pullbackSymmetry_hom_comp_snd _ _
    have hε : ε.hom ≫ j t ≫ Y.hom = B.ι ≫ pullback.fst (c.π.app i) Z.hom := by
      calc
        ε.hom ≫ j t ≫ Y.hom = (ε.hom ≫ j t ≫ γ.inv) ≫ γ.hom ≫ Y.hom := by
          simp only [Category.assoc, Iso.inv_hom_id_assoc]
        _ = B.ι ≫ γ.hom ≫ Y.hom := by
          rw [IsOpenImmersion.isoOfRangeEq_hom_fac B.ι (maps t) hrange]
        _ = B.ι ≫ pullback.fst (c.π.app i) Z.hom := by rw [hγ]
    dsimp [δ]
    rw [Category.assoc, hε]
    exact square.isoPullback_inv_snd

/-- Part (1) for an index category in the scheme universe. -/
private lemma exists_isStandardHCovering_model_of_isLimit_small (hc : IsLimit c)
    (E : PreZeroHypercover.{v} c.pt)
    (hE : letI : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
      IsStandardHCovering E.f) :
    ∃ (i : I) (F : PreZeroHypercover.{v} (D.obj i)), IsStandardHCovering F.f ∧
      Nonempty (F.pullback₂ (c.π.app i) ≅ E) := by
  classical
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have hfinE : Finite E.I₀ := hE.1
  have haffE : ∀ k, IsAffine (E.X k) := hE.2.1
  have : ∀ k, IsAffine (Over.mk (E.f k)).left := fun k ↦ inferInstanceAs (IsAffine (E.X k))
  obtain ⟨J, Y, p, V, j, hJ, hp, hs, hfp, ha, ho, hcover, href⟩ :=
    exists_finitePresentation_proper_refinement_of_isHCovering E.X E.f hE.isHCovering
  have : Finite J := hJ
  have : IsProper (Over.mk p).hom := hp
  have : Surjective (Over.mk p).hom := hs
  have haffV : ∀ k, IsAffine (V k) := ha
  have hopen : ∀ k, IsOpenImmersion (j k) := ho
  obtain ⟨i, X, haX, hfpX, ⟨α⟩⟩ := exists_isAffine_finitePresentation_models D c hc
    (fun k ↦ Over.mk (E.f k)) (fun k ↦ hE.2.2.1 k)
  obtain ⟨l, Z, z, hz, hfpZ, ⟨β⟩⟩ := exists_standardPHCovering_model D c hc
    (Over.mk p) hfp V j hcover
  let k := IsCofiltered.min i l
  let ei : k ⟶ i := IsCofiltered.minToLeft i l
  let el : k ⟶ l := IsCofiltered.minToRight i l
  let F : PreZeroHypercover.{v} (D.obj k) :=
    { I₀ := E.I₀
      X t := ((Over.pullback (D.map ei)).obj (X t)).left
      f t := ((Over.pullback (D.map ei)).obj (X t)).hom }
  let W : PreZeroHypercover.{u} (D.obj l) := { I₀ := J, X := Z, f := z }
  let Wk := W.pullback₂ (D.map el)
  have hWk : StandardPHCovering Wk.f := hz.pullback (D.map el)
  let αk (t : E.I₀) :
      (Over.pullback (c.π.app k)).obj (Over.mk (F.f t)) ≅ Over.mk (E.f t) :=
    overPullbackCompIso _ _ _ (c.w ei) (X t) ≪≫ α t
  let βk (t : J) :
      (Over.pullback (c.π.app k)).obj (Over.mk (Wk.f t)) ≅ Over.mk (j t ≫ p) :=
    overPullbackCompIso _ _ _ (c.w el) (Over.mk (z t)) ≪≫ β t
  choose index refineMaps hrefineMaps using href
  let A (t : J) : Over (D.obj k) := Over.mk (Wk.f t)
  let B (t : J) : Over (D.obj k) := Over.mk (F.f (index t))
  let φ (t : J) : (Over.pullback (c.π.app k)).obj (A t) ⟶
      (Over.pullback (c.π.app k)).obj (B t) :=
    (βk t).hom ≫ (show Over.mk (j t ≫ p) ⟶ Over.mk (E.f (index t)) from
      Over.homMk (refineMaps t) (hrefineMaps t)) ≫ (αk (index t)).inv
  have : ∀ {a b : I} (e : a ⟶ b), IsAffineHom (D.map e) := fun _ ↦ inferInstance
  have : ∀ a, CompactSpace (D.obj a) := fun _ ↦ inferInstance
  have : ∀ a, QuasiSeparatedSpace (D.obj a) := fun _ ↦ inferInstance
  obtain ⟨s, e, morphisms, hmor, -⟩ := exists_finite_morphism_projection_model D c hc k A B
    (fun t ↦ LimitFPObjectDescent.finitePresentation_overPullback (D.map el)
      (Over.mk (z t)) (hfpZ t))
    (fun t ↦ LimitFPObjectDescent.finitePresentation_overPullback _ _ (hfpX (index t))) φ
  let Fs := F.pullback₂ (D.map e)
  let Ws := Wk.pullback₂ (D.map e)
  have hWs : StandardPHCovering Ws.f := hWk.pullback (D.map e)
  let refinement : Ws.Hom Fs :=
    { s₀ := index
      h₀ t := pullback.lift (morphisms t) (pullback.snd (Wk.f t) (D.map e)) (hmor t)
      w₀ t := pullback.lift_snd _ _ _ }
  have hFs : IsStandardHCovering Fs.f := by
    refine ⟨inferInstanceAs (Finite E.I₀), ?_, ?_, Ws, hWs, ⟨refinement⟩⟩
    · intro t
      have : IsAffine (X t).left := haX t
      have : IsAffine (F.X t) := by
        change IsAffine (pullback (X t).hom (D.map ei))
        exact isAffine_of_isAffineHom (pullback.fst (X t).hom (D.map ei))
      change IsAffine (pullback (F.f t) (D.map e))
      exact isAffine_of_isAffineHom (pullback.fst (F.f t) (D.map e))
    · intro t
      exact LimitFPObjectDescent.finitePresentation_overPullback _ _
        (LimitFPObjectDescent.finitePresentation_overPullback _ _ (hfpX t))
  exact ⟨s, Fs, hFs, ⟨pullback₂CompIso _ _ _ (c.w e) F ≪≫
    PreZeroHypercover.isoMk (Equiv.refl E.I₀)
      (fun t ↦ (Over.forget c.pt).mapIso (αk t)) (fun t ↦ (αk t).hom.w)⟩⟩

end Part1

/-! ### The three parts of Stacks 0EV2 -/

/-- **Stacks 0EV2, part (1).** Let an affine scheme be written as the limit of a cofiltered
inverse system of affine schemes. Then every standard h covering of the limit is isomorphic to
the base change of a standard h covering of one of the stages, with the same index type. -/
@[stacks 0EV2 "part (1)"]
public theorem exists_isStandardHCovering_model_of_isLimit {I : Type v} [Category.{w} I]
    [IsCofiltered I] [EssentiallySmall.{u} I] (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (E : PreZeroHypercover.{v} c.pt)
    (hE : letI : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
      IsStandardHCovering E.f) :
    ∃ (i : I) (F : PreZeroHypercover.{v} (D.obj i)), IsStandardHCovering F.f ∧
      Nonempty (F.pullback₂ (c.π.app i) ≅ E) := by
  let equivalence := equivSmallModel.{u} I
  have : IsCofiltered (SmallModel.{u} I) := IsCofiltered.of_equivalence equivalence
  have : ∀ i, IsAffine ((equivalence.inverse ⋙ D).obj i) := fun i ↦
    inferInstanceAs (IsAffine (D.obj (equivalence.inverse.obj i)))
  obtain ⟨i, F, hF, hiso⟩ := exists_isStandardHCovering_model_of_isLimit_small
    (equivalence.inverse ⋙ D) (c.whisker equivalence.inverse)
    (hc.whiskerEquivalence equivalence.symm) E hE
  exact ⟨equivalence.inverse.obj i, F, hF, hiso⟩

/-- **Stacks 0EV2, part (2).** Let an affine scheme be written as the limit of a cofiltered
inverse system of affine schemes, and let two standard h coverings of a stage be given. Every
morphism between their base changes to the limit is the base change of a morphism between their
base changes to some later stage, compared through the canonical identifications
`AlgebraicGeometry.pullback₂CompIso` of the iterated base changes with the direct ones. -/
@[stacks 0EV2 "part (2)"]
public theorem exists_hom_isStandardHCovering_model_of_isLimit {I : Type v} [Category.{w} I]
    [IsCofiltered I] [EssentiallySmall.{u} I] (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I) (E F : PreZeroHypercover.{v} (D.obj i))
    (hE : IsStandardHCovering E.f) (hF : IsStandardHCovering F.f)
    (f : (E.pullback₂ (c.π.app i)).Hom (F.pullback₂ (c.π.app i))) :
    ∃ (j : I) (e : j ⟶ i) (g : (E.pullback₂ (D.map e)).Hom (F.pullback₂ (D.map e))),
      (pullback₂CompIso (D.map e) (c.π.app j) (c.π.app i) (c.w e) E).hom ≫ f =
        g.pullback₂ (c.π.app j) ≫
          (pullback₂CompIso (D.map e) (c.π.app j) (c.π.app i) (c.w e) F).hom := by
  classical
  have hfinE : Finite E.I₀ := hE.1
  have : ∀ k, CompactSpace (D.obj k) := fun k ↦ inferInstance
  have : ∀ k, QuasiSeparatedSpace (D.obj k) := fun k ↦ inferInstance
  have : ∀ {k l : I} (e : k ⟶ l), IsAffineHom (D.map e) := fun _ ↦ inferInstance
  let X (k : E.I₀) : Over (D.obj i) := Over.mk (E.f k)
  let Y (k : E.I₀) : Over (D.obj i) := Over.mk (F.f (f.s₀ k))
  let φ (k : E.I₀) : (Over.pullback (c.π.app i)).obj (X k) ⟶
      (Over.pullback (c.π.app i)).obj (Y k) := Over.homMk (f.h₀ k) (f.w₀ k)
  obtain ⟨j, e, maps, hmaps, hlim⟩ := exists_finite_morphism_projection_model D c hc i X Y
    (fun k ↦ hE.2.2.1 k) (fun k ↦ hF.2.2.1 (f.s₀ k)) φ
  let gOver (k : E.I₀) : (Over.pullback (D.map e)).obj (X k) ⟶
      (Over.pullback (D.map e)).obj (Y k) :=
    Over.homMk (pullback.lift (maps k) (pullback.snd (E.f k) (D.map e)) (hmaps k))
      (pullback.lift_snd _ _ _)
  let g : (E.pullback₂ (D.map e)).Hom (F.pullback₂ (D.map e)) :=
    { s₀ := f.s₀
      h₀ k := (gOver k).left
      w₀ k := (gOver k).w }
  refine ⟨j, e, g, ?_⟩
  have hOver : ∀ k : E.I₀,
      (overPullbackCompIso (D.map e) (c.π.app j) (c.π.app i) (c.w e) (X k)).hom ≫ φ k =
        (Over.pullback (c.π.app j)).map (gOver k) ≫
          (overPullbackCompIso (D.map e) (c.π.app j) (c.π.app i) (c.w e) (Y k)).hom := by
    intro k
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have hcancel :
          (overPullbackCompIso (D.map e) (c.π.app j) (c.π.app i) (c.w e) (X k)).hom.left ≫
            (overPullbackCompIso (D.map e) (c.π.app j) (c.π.app i) (c.w e) (X k)).inv.left =
          𝟙 ((Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj (X k))).left := by
        rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
      have hgfst : (gOver k).left ≫ pullback.fst (Y k).hom (D.map e) = maps k :=
        pullback.lift_fst _ _ _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc,
        overPullbackCompIso_fst, ← hlim k, limitStageProjection_eq,
        overPullback_map_left_fst_assoc, hgfst, Category.assoc,
        ← Category.assoc
          (overPullbackCompIso (D.map e) (c.π.app j) (c.π.app i) (c.w e) (X k)).hom.left,
        hcancel, Category.id_comp]
    · exact (Over.w _).trans (Over.w _).symm
  exact hom_eq_of_s₀_eq_of_heq rfl fun k ↦ heq_of_eq (congrArg Over.Hom.left (hOver k))

/-- **Stacks 0EV2, part (3).** Let an affine scheme be written as the limit of a cofiltered
inverse system of affine schemes. Two morphisms of standard h coverings of a stage whose base
changes to the limit are equal are already equal after base change to some later stage. -/
@[stacks 0EV2 "part (3)"]
public theorem eventually_eq_hom_isStandardHCovering_of_isLimit {I : Type v} [Category.{w} I]
    [IsCofiltered I] [EssentiallySmall.{u} I] (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I) (E F : PreZeroHypercover.{v} (D.obj i))
    (hE : IsStandardHCovering E.f) (hF : IsStandardHCovering F.f) (f g : E.Hom F)
    (hfg : f.pullback₂ (c.π.app i) = g.pullback₂ (c.π.app i)) :
    ∃ (j : I) (e : j ⟶ i), f.pullback₂ (D.map e) = g.pullback₂ (D.map e) := by
  classical
  have : ∀ k, CompactSpace (D.obj k) := fun k ↦ inferInstance
  have : ∀ k, QuasiSeparatedSpace (D.obj k) := fun k ↦ inferInstance
  have : ∀ {k l : I} (e : k ⟶ l), IsAffineHom (D.map e) := fun _ ↦ inferInstance
  obtain ⟨gs, gh, gw⟩ := g
  have hs : f.s₀ = gs := congrArg (fun h ↦ h.s₀) hfg
  cases hs
  obtain ⟨hs', hcompfg⟩ := PreZeroHypercover.Hom.ext'_iff.mp hfg
  let X (k : E.I₀) : Over (D.obj i) := Over.mk (E.f k)
  let Y (k : E.I₀) : Over (D.obj i) := Over.mk (F.f (f.s₀ k))
  let φ (k : E.I₀) : X k ⟶ Y k := Over.homMk (f.h₀ k) (f.w₀ k)
  let ψ (k : E.I₀) : X k ⟶ Y k := Over.homMk (gh k) (gw k)
  have hstage (k : E.I₀) : ∃ (j : I) (e : j ⟶ i),
      (Over.pullback (D.map e)).map (φ k) = (Over.pullback (D.map e)).map (ψ k) := by
    have hlimit : (Over.pullback (c.π.app i)).map (φ k) =
        (Over.pullback (c.π.app i)).map (ψ k) := by
      apply Over.OverMorphism.ext
      have hidxE : (E.pullback₂ (c.π.app i)).I₀ = E.I₀ :=
        PreZeroHypercover.pullback₂_I₀ (c.π.app i) E
      have hidxF : (F.pullback₂ (c.π.app i)).I₀ = F.I₀ :=
        PreZeroHypercover.pullback₂_I₀ (c.π.app i) F
      cases hidxE
      cases hidxF
      have hX := PreZeroHypercover.pullback₂_X (c.π.app i) E k
      have hY := PreZeroHypercover.pullback₂_X (c.π.app i) F (f.s₀ k)
      have hh₀ : HEq ((f.pullback₂ (c.π.app i)).h₀ k)
          (((⟨f.s₀, gh, gw⟩ : E.Hom F).pullback₂ (c.π.app i)).h₀ k) :=
        Quiver.heq_of_homOfEq_ext rfl
          (congrArg (fun t ↦ (F.pullback₂ (c.π.app i)).X t) (congrFun hs' k)) (hcompfg k)
      have hover : HEq (Over.Hom.left ((Over.pullback (c.π.app i)).map (φ k)))
          (Over.Hom.left ((Over.pullback (c.π.app i)).map (ψ k))) := by
        apply Quiver.heq_of_homOfEq_ext hX.symm hY.symm
        cases hX
        cases hY
        simpa [PreZeroHypercover.Hom.pullback₂, PreZeroHypercover.Hom.pullback₂Map, φ, ψ, X,
          Y, Over.pullback, Quiver.homOfEq] using eq_of_heq hh₀
      exact eq_of_heq hover
    exact eventually_eq_of_baseChange_eq D c hc i (X k) (Y k) (hE.2.2.1 k)
      (hF.2.2.1 (f.s₀ k)) (φ k) (ψ k) hlimit
  have hfinE : Finite E.I₀ := hE.1
  choose lev arr harr using hstage
  obtain ⟨j, e, b, hb⟩ := IsCofiltered.wideCospan arr
  refine ⟨j, e, ?_⟩
  have hidxE : (E.pullback₂ (D.map e)).I₀ = E.I₀ :=
    PreZeroHypercover.pullback₂_I₀ (D.map e) E
  have hidxF : (F.pullback₂ (D.map e)).I₀ = F.I₀ :=
    PreZeroHypercover.pullback₂_I₀ (D.map e) F
  cases hidxE
  cases hidxF
  refine hom_eq_of_s₀_eq_of_heq (a := f.pullback₂ (D.map e))
    (b := (⟨f.s₀, gh, gw⟩ : E.Hom F).pullback₂ (D.map e)) rfl ?_
  intro k
  have hcomp : (Over.pullback (D.map e)).map (φ k) = (Over.pullback (D.map e)).map (ψ k) := by
    have hde : D.map (b k) ≫ D.map (arr k) = D.map e := by rw [← D.map_comp, hb k]
    apply (cancel_epi (overPullbackCompIso (D.map (arr k)) (D.map (b k)) (D.map e)
      hde (X k)).hom).mp
    rw [overPullbackCompIso_naturality (D.map (arr k)) (D.map (b k)) (D.map e) hde (φ k),
      overPullbackCompIso_naturality (D.map (arr k)) (D.map (b k)) (D.map e) hde (ψ k),
      congrArg (Over.pullback (D.map (b k))).map (harr k)]
  have hh := congrArg Over.Hom.left hcomp
  have hX := PreZeroHypercover.pullback₂_X (D.map e) E k
  have hY := PreZeroHypercover.pullback₂_X (D.map e) F (f.s₀ k)
  apply Quiver.heq_of_homOfEq_ext hX hY
  cases hX
  cases hY
  simpa [PreZeroHypercover.Hom.pullback₂, PreZeroHypercover.Hom.pullback₂Map, φ, ψ, X, Y,
    Over.pullback, Quiver.homOfEq] using hh

end AlgebraicGeometry
