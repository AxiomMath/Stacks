module

public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import Mathlib.CategoryTheory.EquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.FiniteTypeClosedInFinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.ProperLimitStage.SeparatedModel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Models of a relation of finite presentation over a stage of a limit

Let `S = lim Sᵢ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition morphisms, and let `s, t : R ⟶ W` be two morphisms between schemes of finite
presentation over `S`. Then `W`, `R`, `s` and `t` are the base changes of schemes `Wᵢ`, `Rᵢ` of
finite presentation over some stage `Sᵢ` and of morphisms `sᵢ, tᵢ : Rᵢ ⟶ Wᵢ`, and every one of
the following properties of the relation over `S` already holds over a stage: `s` and `t` are
étale, `(s, t) : R ⟶ W ×_S W` is a monomorphism or a closed immersion, `W` is affine or flat over
the base, and the relation is reflexive, symmetric and transitive.

## Main definitions

* `AlgebraicGeometry.RelationModel`: a model of `(W, R, s, t)` over a stage, together with the
  identification of its base change to the limit with `(W, R, s, t)`.
* `AlgebraicGeometry.RelationModel.restrict`: the model over a later stage obtained by base change.
* `AlgebraicGeometry.IsGroupoidRelation`: reflexivity, symmetry and transitivity witnesses for a
  pair of morphisms.

## Main results

* `AlgebraicGeometry.RelationModel.exists_model`: a model exists.
* `AlgebraicGeometry.RelationModel.exists_restrict_etale_s₀`,
  `AlgebraicGeometry.RelationModel.exists_restrict_etale_t₀`,
  `AlgebraicGeometry.RelationModel.exists_restrict_mono_prodLift`,
  `AlgebraicGeometry.RelationModel.exists_restrict_isClosedImmersion_prodLift`,
  `AlgebraicGeometry.RelationModel.exists_restrict_isAffineHom_W₀` and
  `AlgebraicGeometry.RelationModel.exists_restrict_flat_W₀`: each of these properties of the
  relation over the limit holds for the model over a later stage.
* `AlgebraicGeometry.RelationModel.exists_isGroupoidRelation`: a reflexive, symmetric and
  transitive relation has a model with the same property.
* `AlgebraicGeometry.RelationModel.exists_etaleEquivalenceRelation`: a model with all of these
  properties at once.

## Implementation notes

The base change of a model to the limit is identified with the given relation by isomorphisms
`eW`, `eR` intertwining the morphisms. Restricting a model to a later stage composes these with
the canonical comparison `AlgebraicGeometry.overPullbackCompIso` between iterated and direct base
change.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZN](https://stacks.math.columbia.edu/tag/01ZN)
* [Stacks Project, Tag 01ZP](https://stacks.math.columbia.edu/tag/01ZP)
* [Stacks Project, Tag 04AI](https://stacks.math.columbia.edu/tag/04AI)
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
* [Stacks Project, Tag 07RQ](https://stacks.math.columbia.edu/tag/07RQ)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Groupoid witnesses -/

section Groupoid

variable {C : Type*} [Category* C] [HasPullbacks C]

/-- Reflexivity, symmetry and transitivity witnesses for a pair of morphisms `s, t : R ⟶ W`,
where `t` is the target and `s` the source map, and composition is defined on
`R ×_{t, W, s} R`. -/
def IsGroupoidRelation {R W : C} (s t : R ⟶ W) : Prop :=
  ∃ (refl : W ⟶ R) (symm : R ⟶ R) (comp : pullback t s ⟶ R),
    refl ≫ s = 𝟙 W ∧ refl ≫ t = 𝟙 W ∧ symm ≫ s = t ∧ symm ≫ t = s ∧
      comp ≫ s = pullback.fst t s ≫ s ∧ comp ≫ t = pullback.snd t s ≫ t

/-- Groupoid witnesses transport along isomorphisms of the two objects intertwining the two
pairs of morphisms. -/
theorem IsGroupoidRelation.of_iso {R W R' W' : C} {s t : R ⟶ W} {s' t' : R' ⟶ W'}
    (eR : R' ≅ R) (eW : W' ≅ W) (hs : s' ≫ eW.hom = eR.hom ≫ s)
    (ht : t' ≫ eW.hom = eR.hom ≫ t) (h : IsGroupoidRelation s t) :
    IsGroupoidRelation s' t' := by
  obtain ⟨refl, symm, comp, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  have hs' : s' = eR.hom ≫ s ≫ eW.inv := by rw [← reassoc_of% hs, Iso.hom_inv_id, Category.comp_id]
  have ht' : t' = eR.hom ≫ t ≫ eW.inv := by rw [← reassoc_of% ht, Iso.hom_inv_id, Category.comp_id]
  let φ : pullback t' s' ⟶ pullback t s :=
    pullback.map _ _ _ _ eR.hom eR.hom eW.hom (by rw [ht]) (by rw [hs])
  refine ⟨eW.hom ≫ refl ≫ eR.inv, eR.hom ≫ symm ≫ eR.inv, φ ≫ comp ≫ eR.inv, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp [hs', reassoc_of% h₁]
  · simp [ht', reassoc_of% h₂]
  · simp [hs', ht', reassoc_of% h₃]
  · simp [hs', ht', reassoc_of% h₄]
  · have hs'' : eR.inv ≫ s' = s ≫ eW.inv := by rw [hs']; simp
    simp only [φ, Category.assoc, hs'', reassoc_of% h₅, pullback.map, pullback.lift_fst_assoc]
    rw [← hs']
  · have ht'' : eR.inv ≫ t' = t ≫ eW.inv := by rw [ht']; simp
    simp only [φ, Category.assoc, ht'', reassoc_of% h₆, pullback.map, pullback.lift_snd_assoc]
    rw [← ht']

/-- Witnesses whose defining equations hold after applying a functor preserving the fibre product
`R ×_{t, W, s} R` give groupoid witnesses for the images of `s` and `t`. -/
theorem IsGroupoidRelation.of_map_eq {D : Type*} [Category* D] [HasPullbacks D] (G : C ⥤ D)
    {R W : C} {s t : R ⟶ W} [PreservesLimit (cospan t s) G] (refl : W ⟶ R) (symm : R ⟶ R)
    (comp : pullback t s ⟶ R) (h₁ : G.map (refl ≫ s) = G.map (𝟙 W))
    (h₂ : G.map (refl ≫ t) = G.map (𝟙 W)) (h₃ : G.map (symm ≫ s) = G.map t)
    (h₄ : G.map (symm ≫ t) = G.map s) (h₅ : G.map (comp ≫ s) = G.map (pullback.fst t s ≫ s))
    (h₆ : G.map (comp ≫ t) = G.map (pullback.snd t s ≫ t)) :
    IsGroupoidRelation (G.map s) (G.map t) := by
  refine ⟨G.map refl, G.map symm, (PreservesPullback.iso G t s).inv ≫ G.map comp, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [← G.map_comp, h₁, G.map_id]
  · rw [← G.map_comp, h₂, G.map_id]
  · rw [← G.map_comp, h₃]
  · rw [← G.map_comp, h₄]
  · rw [Category.assoc, ← G.map_comp, h₅, G.map_comp, PreservesPullback.iso_inv_fst_assoc]
  · rw [Category.assoc, ← G.map_comp, h₆, G.map_comp, PreservesPullback.iso_inv_snd_assoc]

/-- A functor preserving the fibre product `R ×_{t, W, s} R` carries groupoid witnesses to
groupoid witnesses. -/
theorem IsGroupoidRelation.map {D : Type*} [Category* D] [HasPullbacks D] (G : C ⥤ D)
    {R W : C} {s t : R ⟶ W} [PreservesLimit (cospan t s) G] (h : IsGroupoidRelation s t) :
    IsGroupoidRelation (G.map s) (G.map t) := by
  obtain ⟨refl, symm, comp, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact IsGroupoidRelation.of_map_eq G refl symm comp (by rw [h₁]) (by rw [h₂]) (by rw [h₃])
    (by rw [h₄]) (by rw [h₅]) (by rw [h₆])

/-- An equivalence relation in the internal sense has groupoid witnesses. -/
theorem IsGroupoidRelation.of_isEquivalenceRelation {R W : C} {s t : R ⟶ W}
    (h : IsEquivalenceRelation s t) : IsGroupoidRelation s t := by
  obtain ⟨e⟩ := h.nonempty_equivalenceRelation
  refine ⟨e.r, e.s, e.isLimit.lift (pullback.cone t s) ≫ e.t, e.reflexivity₁, e.reflexivity₂,
    e.symmetry₁, e.symmetry₂, ?_, ?_⟩
  · rw [Category.assoc, e.transitivity₁, ← Category.assoc,
      e.isLimit.fac (pullback.cone t s) WalkingCospan.left]
    rfl
  · rw [Category.assoc, e.transitivity₂, ← Category.assoc,
      e.isLimit.fac (pullback.cone t s) WalkingCospan.right]
    rfl

/-- A fully faithful functor preserving the fibre product `R ×_{t, W, s} R` reflects groupoid
witnesses. -/
theorem IsGroupoidRelation.of_map {D : Type*} [Category* D] [HasPullbacks D] {G : C ⥤ D}
    (hG : G.FullyFaithful) {R W : C} {s t : R ⟶ W} [PreservesLimit (cospan t s) G]
    (h : IsGroupoidRelation (G.map s) (G.map t)) : IsGroupoidRelation s t := by
  obtain ⟨refl, symm, comp, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  refine ⟨hG.preimage refl, hG.preimage symm,
    hG.preimage ((PreservesPullback.iso G t s).hom ≫ comp), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    apply hG.map_injective
  · rw [G.map_comp, hG.map_preimage, h₁, G.map_id]
  · rw [G.map_comp, hG.map_preimage, h₂, G.map_id]
  · rw [G.map_comp, hG.map_preimage, h₃]
  · rw [G.map_comp, hG.map_preimage, h₄]
  · rw [G.map_comp, G.map_comp, hG.map_preimage, Category.assoc, h₅,
      PreservesPullback.iso_hom_fst_assoc]
  · rw [G.map_comp, G.map_comp, hG.map_preimage, Category.assoc, h₆,
      PreservesPullback.iso_hom_snd_assoc]

end Groupoid

/-! ### Base change of morphisms of schemes over a base -/

section BaseChange

variable {S T : Scheme.{u}}

/-- A morphism between two schemes of finite presentation over `S` is locally of finite
presentation. -/
@[sga "3 VIB 10.8" "special case", sga "3 X 3.5" "special case"]
theorem locallyOfFinitePresentation_left_of_finitePresentation {X Y : Over S} (f : X ⟶ Y)
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom) :
    LocallyOfFinitePresentation f.left := by
  have : LocallyOfFinitePresentation X.hom := hX.1
  have : LocallyOfFinitePresentation Y.hom := hY.1
  have : LocallyOfFinitePresentation (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  exact locallyOfFinitePresentation_of_comp f.left Y.hom

/-- The binary product of two schemes of finite presentation over `S` is of finite
presentation over `S`. -/
theorem finitePresentation_prod_hom {X Y : Over S} (hX : FinitePresentation X.hom)
    (hY : FinitePresentation Y.hom) : FinitePresentation (X ⨯ Y).hom := by
  have h : (Over.prodLeftIsoPullback X Y).hom ≫ pullback.snd X.hom Y.hom ≫ Y.hom =
      (X ⨯ Y).hom := by
    rw [Over.prodLeftIsoPullback_hom_snd_assoc, Over.w]
  rw [← h]
  have h₁ : FinitePresentation (pullback.snd X.hom Y.hom) :=
    FinitePresentation.of_isPullback (IsPullback.of_hasPullback X.hom Y.hom) hX
  have h₂ := FinitePresentation.comp h₁ hY
  have := h₂.1; have := h₂.2.1; have := h₂.2.2
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Two morphisms over a base whose base changes along `p` agree have equal base changes along
every `q ≫ p`. -/
lemma overPullback_map_eq_comp {T T' T'' : Scheme.{u}} (p : T' ⟶ T) (q : T'' ⟶ T')
    {X Y : Over T} {f g : X ⟶ Y} (h : (Over.pullback p).map f = (Over.pullback p).map g) :
    (Over.pullback (q ≫ p)).map f = (Over.pullback (q ≫ p)).map g := by
  rw [← cancel_mono ((Over.pullbackComp q p).hom.app Y), (Over.pullbackComp q p).hom.naturality,
    (Over.pullbackComp q p).hom.naturality, Functor.comp_map, Functor.comp_map, h]

/-- The fibre product of two schemes of finite presentation over a third, all of finite
presentation over a base, is of finite presentation over the base. -/
lemma finitePresentation_pullback_hom {T : Scheme.{u}} {X Y Z : Over T} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom)
    (hZ : FinitePresentation Z.hom) : FinitePresentation (pullback f g).hom := by
  have : QuasiSeparated Z.hom := hZ.2.2
  have : LocallyOfFinitePresentation Z.hom := hZ.1
  have hg : FinitePresentation g.left :=
    finitePresentation_of_comp g.left Z.hom (by rw [Over.w g]; exact hY)
  have hpb : IsPullback (pullback.fst f g).left (pullback.snd f g).left f.left g.left :=
    (IsPullback.of_hasPullback f g).map (Over.forget T)
  have hfst : FinitePresentation (pullback.fst f g).left :=
    FinitePresentation.of_isPullback hpb.flip hg
  rw [← Over.w (pullback.fst f g)]
  exact FinitePresentation.comp hfst hX

/-- A property of morphisms of schemes invariant under isomorphism holds for a morphism over a
base exactly when it holds for a morphism isomorphic to it in the arrow category. -/
lemma prop_left_iff_of_comm (P : MorphismProperty Scheme.{u}) [P.RespectsIso] {T : Scheme.{u}}
    {X Y X' Y' : Over T} (f : X ⟶ Y) (f' : X' ⟶ Y') (eX : X ≅ X') (eY : Y ≅ Y')
    (h : f ≫ eY.hom = eX.hom ≫ f') : P f.left ↔ P f'.left :=
  MorphismProperty.arrow_mk_iso_iff P (Arrow.isoMk ((Over.forget T).mapIso eX)
    ((Over.forget T).mapIso eY) (by
      simpa only [Functor.mapIso_hom, Over.forget_map, Arrow.mk_hom, Over.comp_left] using
        (congrArg CommaMorphism.left h).symm))

/-- A property of morphisms of schemes invariant under isomorphism holds for the pairing of the
images of two morphisms under a functor preserving binary products exactly when it holds for the
image of their pairing. -/
lemma prop_prodLift_map_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {C : Type*} [Category* C] [HasBinaryProducts C] {T' : Scheme.{u}} (G : C ⥤ Over T')
    [PreservesLimitsOfShape (Discrete WalkingPair) G] {X Y : C} (f g : X ⟶ Y) :
    P (prod.lift (G.map f) (G.map g)).left ↔ P (G.map (prod.lift f g)).left := by
  have h : prod.lift (G.map f) (G.map g) = G.map (prod.lift f g) ≫ prodComparison G Y Y := by
    ext <;> simp [← G.map_comp]
  rw [h, Over.comp_left]
  have : IsIso (prodComparison G Y Y).left := (Over.forget _).map_isIso _
  exact MorphismProperty.cancel_right_of_respectsIso P _ _

/-- A property stable under base change holds for the base change of the structure morphism of `X`
as a morphism to the terminal object, if it holds for the structure morphism of an object
isomorphic to the base change of `X`. -/
private lemma prop_map_homMk_of_iso (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {T T' : Scheme.{u}} (p : T' ⟶ T) {X : Over T} {X' : Over T'}
    (e : X' ≅ (Over.pullback p).obj X) (h : P X'.hom) :
    P ((Over.pullback p).map (Over.homMk X.hom (Category.comp_id _) : X ⟶ Over.mk (𝟙 T))).left :=
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  (overPullback_map_terminal_iff P p X).2 (prop_of_overIso P e h)

/-- A property stable under base change holds for the base change of `X` if it holds for the base
change of its structure morphism as a morphism to the terminal object. -/
private lemma prop_of_map_homMk (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {T T' : Scheme.{u}} (p : T' ⟶ T) {X : Over T}
    (h : P ((Over.pullback p).map
      (Over.homMk X.hom (Category.comp_id _) : X ⟶ Over.mk (𝟙 T))).left) :
    P ((Over.pullback p).obj X).hom :=
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  (overPullback_map_terminal_iff P p X).1 h

end BaseChange

/-! ### Models of a relation over a stage -/

variable {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]

variable (c) in
/-- A model of a relation `s, t : R ⟶ W` over the limit at a stage of the system: schemes of
finite presentation over the stage, two morphisms between them, and the identification of the
base change of this data to the limit with `(W, R, s, t)`. -/
structure RelationModel {W R : Over c.pt} (s t : R ⟶ W) where
  /-- The stage the model is defined over. -/
  stage : I
  /-- The model of `W`. -/
  W₀ : Over (D.obj stage)
  /-- The model of `R`. -/
  R₀ : Over (D.obj stage)
  /-- The model of `s`. -/
  s₀ : R₀ ⟶ W₀
  /-- The model of `t`. -/
  t₀ : R₀ ⟶ W₀
  /-- The model of `W` is of finite presentation over the stage. -/
  finitePresentation_W₀ : FinitePresentation W₀.hom
  /-- The model of `R` is of finite presentation over the stage. -/
  finitePresentation_R₀ : FinitePresentation R₀.hom
  /-- The base change of the model of `W` is `W`. -/
  eW : (Over.pullback (c.π.app stage)).obj W₀ ≅ W
  /-- The base change of the model of `R` is `R`. -/
  eR : (Over.pullback (c.π.app stage)).obj R₀ ≅ R
  /-- The base change of the model of `s` is `s`. -/
  hs : (Over.pullback (c.π.app stage)).map s₀ ≫ eW.hom = eR.hom ≫ s
  /-- The base change of the model of `t` is `t`. -/
  ht : (Over.pullback (c.π.app stage)).map t₀ ≫ eW.hom = eR.hom ≫ t

namespace RelationModel

variable {W R : Over c.pt} {s t : R ⟶ W} (M : RelationModel c s t)

/-- The model over a later stage obtained by base change along a transition morphism. -/
abbrev restrict {k : I} (a : k ⟶ M.stage) : RelationModel c s t where
  stage := k
  W₀ := (Over.pullback (D.map a)).obj M.W₀
  R₀ := (Over.pullback (D.map a)).obj M.R₀
  s₀ := (Over.pullback (D.map a)).map M.s₀
  t₀ := (Over.pullback (D.map a)).map M.t₀
  finitePresentation_W₀ := finitePresentation_overPullbackObj _ _ M.finitePresentation_W₀
  finitePresentation_R₀ := finitePresentation_overPullbackObj _ _ M.finitePresentation_R₀
  eW := overPullbackCompIso (D.map a) (c.π.app k) (c.π.app M.stage) (c.w a) M.W₀ ≪≫ M.eW
  eR := overPullbackCompIso (D.map a) (c.π.app k) (c.π.app M.stage) (c.w a) M.R₀ ≪≫ M.eR
  hs := by
    rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc,
      ← overPullbackCompIso_naturality, Category.assoc, M.hs, Category.assoc]
  ht := by
    rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc,
      ← overPullbackCompIso_naturality, Category.assoc, M.ht, Category.assoc]

omit [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- The base change of the model of `s` is `s`, conjugated by the identifications. -/
lemma map_s₀ : (Over.pullback (c.π.app M.stage)).map M.s₀ = M.eR.hom ≫ s ≫ M.eW.inv := by
  rw [← reassoc_of% M.hs, Iso.hom_inv_id, Category.comp_id]

omit [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- The base change of the model of `t` is `t`, conjugated by the identifications. -/
lemma map_t₀ : (Over.pullback (c.π.app M.stage)).map M.t₀ = M.eR.hom ≫ t ≫ M.eW.inv := by
  rw [← reassoc_of% M.ht, Iso.hom_inv_id, Category.comp_id]

/-- The model of `W` is quasi-compact. -/
instance compactSpace_W₀ : CompactSpace M.W₀.left :=
  have : QuasiCompact M.W₀.hom := M.finitePresentation_W₀.2.1
  QuasiCompact.compactSpace_of_compactSpace M.W₀.hom

/-- The model of `R` is quasi-compact. -/
instance compactSpace_R₀ : CompactSpace M.R₀.left :=
  have : QuasiCompact M.R₀.hom := M.finitePresentation_R₀.2.1
  QuasiCompact.compactSpace_of_compactSpace M.R₀.hom

/-- The model of `W` is quasi-separated. -/
instance quasiSeparatedSpace_W₀ : QuasiSeparatedSpace M.W₀.left :=
  have : QuasiSeparated M.W₀.hom := M.finitePresentation_W₀.2.2
  quasiSeparatedSpace_of_quasiSeparated M.W₀.hom

/-- The model of `R` is quasi-separated. -/
instance quasiSeparatedSpace_R₀ : QuasiSeparatedSpace M.R₀.left :=
  have : QuasiSeparated M.R₀.hom := M.finitePresentation_R₀.2.2
  quasiSeparatedSpace_of_quasiSeparated M.R₀.hom

/-- The model of `s` is locally of finite presentation. -/
instance locallyOfFinitePresentation_s₀ : LocallyOfFinitePresentation M.s₀.left :=
  locallyOfFinitePresentation_left_of_finitePresentation _ M.finitePresentation_R₀
    M.finitePresentation_W₀

/-- The model of `t` is locally of finite presentation. -/
instance locallyOfFinitePresentation_t₀ : LocallyOfFinitePresentation M.t₀.left :=
  locallyOfFinitePresentation_left_of_finitePresentation _ M.finitePresentation_R₀
    M.finitePresentation_W₀

/-! ### Existence of a model -/

omit [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- The comparison isomorphism of a base change along a transition morphism, read through an
identification of the base change of a stage object with a given scheme over the limit. -/
lemma overPullbackCompIso_trans_hom {k j : I} (a : k ⟶ j) {X : Over (D.obj j)} {X' : Over c.pt}
    (e : (Over.pullback (c.π.app j)).obj X ≅ X') :
    (overPullbackCompIso (D.map a) (c.π.app k) (c.π.app j) (c.w a) X ≪≫ e).hom =
      (overPullbackCompIso (D.map a) (c.π.app k) (c.π.app j) (c.w a) X).hom ≫ e.hom := rfl

/-- A morphism between two schemes over the limit, each identified with the base change of a
scheme of finite presentation over a stage, descends to a later stage, compatibly with the
identifications. -/
theorem exists_hom_model (hc : IsLimit c) {j : I} (X Y : Over (D.obj j))
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom) {X' Y' : Over c.pt}
    (eX : (Over.pullback (c.π.app j)).obj X ≅ X') (eY : (Over.pullback (c.π.app j)).obj Y ≅ Y')
    (f : X' ⟶ Y') :
    ∃ (k : I) (a : k ⟶ j) (g : (Over.pullback (D.map a)).obj X ⟶ (Over.pullback (D.map a)).obj Y),
      (Over.pullback (c.π.app k)).map g ≫
          (overPullbackCompIso (D.map a) (c.π.app k) (c.π.app j) (c.w a) Y ≪≫ eY).hom =
        (overPullbackCompIso (D.map a) (c.π.app k) (c.π.app j) (c.w a) X ≪≫ eX).hom ≫ f := by
  obtain ⟨k, a, g, α, β, hα, hβ, hg⟩ :=
    exists_morphism_after_baseChange D c hc j X Y hX hY (eX.hom ≫ f ≫ eY.inv)
  rw [iso_eq_overPullbackCompIso _ _ _ (c.w a) X α hα,
    iso_eq_overPullbackCompIso _ _ _ (c.w a) Y β hβ] at hg
  refine ⟨k, a, g, ?_⟩
  rw [Iso.trans_hom, Iso.trans_hom, ← reassoc_of% hg]
  simp

/-- A relation of finite presentation over the limit has a model over a stage. -/
theorem exists_model (hc : IsLimit c) (hW : FinitePresentation W.hom)
    (hR : FinitePresentation R.hom) : Nonempty (RelationModel c s t) := by
  obtain ⟨i₁, W₁, hW₁, ⟨eW₁⟩⟩ :=
    LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall D c hc W hW
  obtain ⟨i₂, R₁, hR₁, ⟨eR₁⟩⟩ :=
    LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall D c hc R hR
  let k := IsCofiltered.min i₁ i₂
  let a₁ := IsCofiltered.minToLeft i₁ i₂
  let a₂ := IsCofiltered.minToRight i₁ i₂
  let W₂ := (Over.pullback (D.map a₁)).obj W₁
  let R₂ := (Over.pullback (D.map a₂)).obj R₁
  have hW₂ : FinitePresentation W₂.hom := finitePresentation_overPullbackObj _ _ hW₁
  have hR₂ : FinitePresentation R₂.hom := finitePresentation_overPullbackObj _ _ hR₁
  let eW₂ : (Over.pullback (c.π.app k)).obj W₂ ≅ W :=
    overPullbackCompIso (D.map a₁) (c.π.app k) (c.π.app i₁) (c.w a₁) W₁ ≪≫ eW₁.symm
  let eR₂ : (Over.pullback (c.π.app k)).obj R₂ ≅ R :=
    overPullbackCompIso (D.map a₂) (c.π.app k) (c.π.app i₂) (c.w a₂) R₁ ≪≫ eR₁.symm
  obtain ⟨k₁, b₁, s₁, hs₁⟩ := exists_hom_model hc R₂ W₂ hR₂ hW₂ eR₂ eW₂ s
  let W₃ := (Over.pullback (D.map b₁)).obj W₂
  let R₃ := (Over.pullback (D.map b₁)).obj R₂
  have hW₃ : FinitePresentation W₃.hom := finitePresentation_overPullbackObj _ _ hW₂
  have hR₃ : FinitePresentation R₃.hom := finitePresentation_overPullbackObj _ _ hR₂
  let eW₃ := overPullbackCompIso (D.map b₁) (c.π.app k₁) (c.π.app k) (c.w b₁) W₂ ≪≫ eW₂
  let eR₃ := overPullbackCompIso (D.map b₁) (c.π.app k₁) (c.π.app k) (c.w b₁) R₂ ≪≫ eR₂
  obtain ⟨k₂, b₂, t₂, ht₂⟩ := exists_hom_model hc R₃ W₃ hR₃ hW₃ eR₃ eW₃ t
  let M₁ : RelationModel c s t :=
    { stage := k₂
      W₀ := (Over.pullback (D.map b₂)).obj W₃
      R₀ := (Over.pullback (D.map b₂)).obj R₃
      s₀ := (Over.pullback (D.map b₂)).map s₁
      t₀ := t₂
      finitePresentation_W₀ := finitePresentation_overPullbackObj _ _ hW₃
      finitePresentation_R₀ := finitePresentation_overPullbackObj _ _ hR₃
      eW := overPullbackCompIso (D.map b₂) (c.π.app k₂) (c.π.app k₁) (c.w b₂) W₃ ≪≫ eW₃
      eR := overPullbackCompIso (D.map b₂) (c.π.app k₂) (c.π.app k₁) (c.w b₂) R₃ ≪≫ eR₃
      hs := by
        simp only [eW₃, eR₃, Iso.trans_hom, Category.assoc] at hs₁ ⊢
        rw [← reassoc_of% (overPullbackCompIso_naturality (D.map b₂) (c.π.app k₂)
          (c.π.app k₁) (c.w b₂) s₁), hs₁]
      ht := ht₂ }
  exact ⟨M₁⟩

/-! ### Étaleness -/

omit [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- Étaleness of the model of `s` persists under restriction. -/
lemma etale_restrict_s₀ {k : I} (a : k ⟶ M.stage) (h : Etale M.s₀.left) :
    Etale (M.restrict a).s₀.left :=
  MorphismProperty.overPullbackMap (P := @Etale) _ _ h

omit [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- Étaleness of the model of `t` persists under restriction. -/
lemma etale_restrict_t₀ {k : I} (a : k ⟶ M.stage) (h : Etale M.t₀.left) :
    Etale (M.restrict a).t₀.left :=
  MorphismProperty.overPullbackMap (P := @Etale) _ _ h

/-- If `g` is étale and the base change of `f` is `g` up to the identifications, then `f` is étale
over a later stage. -/
private theorem exists_restrict_etale (hc : IsLimit c) (f : M.R₀ ⟶ M.W₀) (g : R ⟶ W)
    [Etale g.left] [LocallyOfFinitePresentation f.left]
    (h : (Over.pullback (c.π.app M.stage)).map f = M.eR.hom ≫ g ≫ M.eW.inv) :
    ∃ (k : I) (a : k ⟶ M.stage), Etale ((Over.pullback (D.map a)).map f).left := by
  have : Etale ((Over.pullback (c.π.app M.stage)).map f).left := by
    have : IsIso M.eR.hom.left := (Over.forget _).map_isIso M.eR.hom
    have : IsIso M.eW.inv.left := (Over.forget _).map_isIso M.eW.inv
    rw [h, Over.comp_left, Over.comp_left]
    infer_instance
  obtain ⟨i, hi⟩ := exists_etale_pullback_of_isLimit D c hc M.stage M.R₀ M.W₀ f
  exact ⟨i.left, i.hom, hi⟩

/-- If `s` is étale, the model of `s` is étale over a later stage. -/
theorem exists_restrict_etale_s₀ (hc : IsLimit c) [Etale s.left] :
    ∃ (k : I) (a : k ⟶ M.stage), Etale (M.restrict a).s₀.left :=
  exists_restrict_etale M hc M.s₀ s M.map_s₀

/-- If `t` is étale, the model of `t` is étale over a later stage. -/
theorem exists_restrict_etale_t₀ (hc : IsLimit c) [Etale t.left] :
    ∃ (k : I) (a : k ⟶ M.stage), Etale (M.restrict a).t₀.left :=
  exists_restrict_etale M hc M.t₀ t M.map_t₀

/-! ### Restriction of identifications, and eventual equality -/

omit [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- A morphism of stage objects compatible with identifications of their base changes stays
compatible after restriction to a later stage. -/
lemma isModel_restrict {j k : I} (a : k ⟶ j) {X Y : Over (D.obj j)} {X' Y' : Over c.pt}
    (eX : (Over.pullback (c.π.app j)).obj X ≅ X') (eY : (Over.pullback (c.π.app j)).obj Y ≅ Y')
    {g : X ⟶ Y} {f : X' ⟶ Y'} (h : (Over.pullback (c.π.app j)).map g ≫ eY.hom = eX.hom ≫ f) :
    (Over.pullback (c.π.app k)).map ((Over.pullback (D.map a)).map g) ≫
        (overPullbackCompIso (D.map a) (c.π.app k) (c.π.app j) (c.w a) Y ≪≫ eY).hom =
      (overPullbackCompIso (D.map a) (c.π.app k) (c.π.app j) (c.w a) X ≪≫ eX).hom ≫ f := by
  rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc, ← overPullbackCompIso_naturality,
    Category.assoc, h, Category.assoc]

variable (I) in
/-- A property of the morphisms into an object `j` of a cofiltered category holds *eventually*
when it holds for every morphism factoring through one fixed morphism into `j`. -/
def EventuallyBelow (j : I) (P : ∀ ⦃k : I⦄, (k ⟶ j) → Prop) : Prop :=
  ∃ (k : I) (a : k ⟶ j), ∀ ⦃k' : I⦄ (b : k' ⟶ k), P (b ≫ a)

omit [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- Two eventual properties hold eventually together. -/
lemma EventuallyBelow.and {j : I} {P Q : ∀ ⦃k : I⦄, (k ⟶ j) → Prop}
    (hP : EventuallyBelow I j P) (hQ : EventuallyBelow I j Q) :
    EventuallyBelow I j fun _ a => P a ∧ Q a := by
  obtain ⟨k₁, a₁, h₁⟩ := hP
  obtain ⟨k₂, a₂, h₂⟩ := hQ
  obtain ⟨k, b₁, b₂, hb⟩ := IsCofiltered.cospan a₁ a₂
  refine ⟨k, b₁ ≫ a₁, fun k' b => ⟨?_, ?_⟩⟩
  · simpa only [Category.assoc] using h₁ (b ≫ b₁)
  · rw [hb]
    simpa only [Category.assoc] using h₂ (b ≫ b₂)

omit [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- Two morphisms of schemes of finite presentation over a stage which agree after base change
to the limit agree after base change along every sufficiently late transition morphism. -/
lemma eventuallyBelow_map_eq [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (hc : IsLimit c) {j : I} {X Y : Over (D.obj j)} (hX : FinitePresentation X.hom)
    (hY : FinitePresentation Y.hom) {f g : X ⟶ Y}
    (h : (Over.pullback (c.π.app j)).map f = (Over.pullback (c.π.app j)).map g) :
    EventuallyBelow I j fun _ a =>
      (Over.pullback (D.map a)).map f = (Over.pullback (D.map a)).map g := by
  obtain ⟨k, a, ha⟩ := eventually_eq_of_baseChange_eq D c hc j X Y hX hY f g h
  refine ⟨k, a, fun k' b => ?_⟩
  dsimp only
  rw [D.map_comp]
  exact overPullback_map_eq_comp _ _ ha

/-! ### Transferring properties of morphisms along identifications -/

omit [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- The base change of the pairing `(s₀, t₀)` of the model is the pairing `(s, t)`, up to the
identifications. -/
lemma map_prodLift_comm :
    (Over.pullback (c.π.app M.stage)).map (prod.lift M.s₀ M.t₀) ≫
        (PreservesLimitPair.iso (Over.pullback (c.π.app M.stage)) M.W₀ M.W₀ ≪≫
          prod.mapIso M.eW M.eW).hom =
      M.eR.hom ≫ prod.lift s t := by
  ext
  · simp [← Functor.map_comp_assoc, M.hs]
  · simp [← Functor.map_comp_assoc, M.ht]

omit [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- A property of morphisms of schemes invariant under isomorphism holds for the base change of
the pairing `(s₀, t₀)` to the limit exactly when it holds for `(s, t)`. -/
lemma prop_map_prodLift_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso] :
    P ((Over.pullback (c.π.app M.stage)).map (prod.lift M.s₀ M.t₀)).left ↔
      P (prod.lift s t).left :=
  prop_left_iff_of_comm P _ _ M.eR _ M.map_prodLift_comm

omit [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- A property of morphisms of schemes stable under base change, holding for the pairing
`(s₀, t₀)` of a model, holds for the pairing of every restriction of the model. -/
lemma prop_prodLift_restrict (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (h : P (prod.lift M.s₀ M.t₀).left) {k : I} (a : k ⟶ M.stage) :
    P (prod.lift (M.restrict a).s₀ (M.restrict a).t₀).left := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (prop_prodLift_map_iff P (Over.pullback (D.map a)) M.s₀ M.t₀).2
    (MorphismProperty.overPullbackMap _ _ h)

/-! ### Monomorphisms and closed immersions -/

/-- The pairing `(s₀, t₀)` of the model is locally of finite type. -/
instance locallyOfFiniteType_prodLift :
    LocallyOfFiniteType (prod.lift M.s₀ M.t₀).left := by
  have := locallyOfFinitePresentation_left_of_finitePresentation (prod.lift M.s₀ M.t₀)
    M.finitePresentation_R₀ (finitePresentation_prod_hom M.finitePresentation_W₀
      M.finitePresentation_W₀)
  infer_instance

/-- The product of the model of `W` with itself is quasi-compact. -/
instance compactSpace_prod : CompactSpace (M.W₀ ⨯ M.W₀).left :=
  have : QuasiCompact (M.W₀ ⨯ M.W₀).hom :=
    (finitePresentation_prod_hom M.finitePresentation_W₀ M.finitePresentation_W₀).2.1
  QuasiCompact.compactSpace_of_compactSpace (M.W₀ ⨯ M.W₀).hom

/-- The product of the model of `W` with itself is quasi-separated. -/
instance quasiSeparatedSpace_prod : QuasiSeparatedSpace (M.W₀ ⨯ M.W₀).left :=
  have : QuasiSeparated (M.W₀ ⨯ M.W₀).hom :=
    (finitePresentation_prod_hom M.finitePresentation_W₀ M.finitePresentation_W₀).2.2
  quasiSeparatedSpace_of_quasiSeparated (M.W₀ ⨯ M.W₀).hom

/-- If `(s, t) : R ⟶ W ×_S W` is a monomorphism, so is the model of it over a later stage. -/
theorem exists_restrict_mono_prodLift (hc : IsLimit c) [Mono (prod.lift s t).left] :
    ∃ (k : I) (a : k ⟶ M.stage), Mono (prod.lift (M.restrict a).s₀ (M.restrict a).t₀).left := by
  have : MorphismProperty.RespectsIso (MorphismProperty.monomorphisms Scheme.{u}) :=
    inferInstance
  have : Mono ((Over.pullback (c.π.app M.stage)).map (prod.lift M.s₀ M.t₀)).left :=
    (M.prop_map_prodLift_iff (MorphismProperty.monomorphisms Scheme.{u})).2
      (inferInstanceAs (Mono (prod.lift s t).left))
  obtain ⟨k, a, ha⟩ := exists_mono_baseChange_of_mono_limitBaseChange D c hc M.stage M.R₀
    (M.W₀ ⨯ M.W₀) (prod.lift M.s₀ M.t₀)
  exact ⟨k, a, (prop_prodLift_map_iff (MorphismProperty.monomorphisms Scheme.{u})
    (Over.pullback (D.map a)) M.s₀ M.t₀).2 ha⟩

/-- If `(s, t) : R ⟶ W ×_S W` is a closed immersion, so is the model of it over a later stage. -/
theorem exists_restrict_isClosedImmersion_prodLift (hc : IsLimit c)
    [IsClosedImmersion (prod.lift s t).left] :
    ∃ (k : I) (a : k ⟶ M.stage),
      IsClosedImmersion (prod.lift (M.restrict a).s₀ (M.restrict a).t₀).left := by
  have : IsClosedImmersion
      ((Over.pullback (c.π.app M.stage)).map (prod.lift M.s₀ M.t₀)).left :=
    (M.prop_map_prodLift_iff @IsClosedImmersion).2 inferInstance
  obtain ⟨k, a, ha⟩ := exists_isClosedImmersion_baseChange_of_isLimit D c hc M.stage M.R₀
    (M.W₀ ⨯ M.W₀) (prod.lift M.s₀ M.t₀)
  exact ⟨k, a, (prop_prodLift_map_iff @IsClosedImmersion (Over.pullback (D.map a)) M.s₀ M.t₀).2
    ha⟩

/-! ### Properties of the model of `W` -/

omit [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- A property of morphisms of schemes stable under base change, holding for the structure
morphism of the model of `W`, holds for every restriction of the model. -/
lemma prop_W₀_restrict (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (h : P M.W₀.hom) {k : I} (a : k ⟶ M.stage) : P (M.restrict a).W₀.hom :=
  P.of_isPullback (IsPullback.of_hasPullback M.W₀.hom (D.map a)) h

/-- The structure morphism of the model of `W`, as a morphism to the terminal object over the
stage. -/
private abbrev toTerminal_W₀ : M.W₀ ⟶ Over.mk (𝟙 (D.obj M.stage)) :=
  Over.homMk M.W₀.hom (Category.comp_id _)

/-- The terminal object over a quasi-compact stage is quasi-compact. -/
private instance compactSpace_mk_id (X : Scheme.{u}) [CompactSpace X] :
    CompactSpace (Over.mk (𝟙 X)).left := ‹CompactSpace X›

/-- The terminal object over a quasi-separated stage is quasi-separated. -/
private instance quasiSeparatedSpace_mk_id (X : Scheme.{u}) [QuasiSeparatedSpace X] :
    QuasiSeparatedSpace (Over.mk (𝟙 X)).left := ‹QuasiSeparatedSpace X›

/-- If `W` is affine over the limit, the model of `W` is affine over a later stage. -/
theorem exists_restrict_isAffineHom_W₀ (hc : IsLimit c) [IsAffineHom W.hom] :
    ∃ (k : I) (a : k ⟶ M.stage), IsAffineHom (M.restrict a).W₀.hom := by
  have := prop_map_homMk_of_iso @IsAffineHom (c.π.app M.stage) M.eW.symm
    (inferInstanceAs (IsAffineHom W.hom))
  obtain ⟨k, a, ha⟩ := exists_isAffineHom_of_isLimit D c hc M.stage M.W₀ _ M.toTerminal_W₀
  exact ⟨k, a, prop_of_map_homMk @IsAffineHom _ ha⟩

/-- If `W` is flat over the limit, the model of `W` is flat over a later stage. -/
theorem exists_restrict_flat_W₀ (hc : IsLimit c) [Flat W.hom] :
    ∃ (k : I) (a : k ⟶ M.stage), Flat (M.restrict a).W₀.hom := by
  have := prop_map_homMk_of_iso @Flat (c.π.app M.stage) M.eW.symm (inferInstanceAs (Flat W.hom))
  have : LocallyOfFinitePresentation M.toTerminal_W₀.left := M.finitePresentation_W₀.1
  obtain ⟨k, a, ha⟩ := exists_flat_baseChange_of_limitBaseChange D c M.stage M.W₀ _
    M.toTerminal_W₀ hc
  exact ⟨k, a, prop_of_map_homMk @Flat _ ha⟩

/-! ### Groupoid witnesses -/

omit [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- Groupoid witnesses for the model persist under restriction. -/
lemma isGroupoidRelation_restrict (h : IsGroupoidRelation M.s₀ M.t₀) {k : I}
    (a : k ⟶ M.stage) : IsGroupoidRelation (M.restrict a).s₀ (M.restrict a).t₀ :=
  h.map (Over.pullback (D.map a))

include M in
/-- If the relation over the limit is reflexive, symmetric and transitive, then so is a model of
it over a later stage. -/
theorem exists_isGroupoidRelation (hc : IsLimit c) (h : IsGroupoidRelation s t) :
    ∃ M' : RelationModel c s t, IsGroupoidRelation M'.s₀ M'.t₀ := by
  obtain ⟨refl, symm, comp, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  obtain ⟨k₁, a₁, r₁, hr₁⟩ := exists_hom_model hc M.W₀ M.R₀ M.finitePresentation_W₀
    M.finitePresentation_R₀ M.eW M.eR refl
  let M₁ := M.restrict a₁
  replace hr₁ : (Over.pullback (c.π.app M₁.stage)).map r₁ ≫ M₁.eR.hom = M₁.eW.hom ≫ refl :=
    hr₁
  obtain ⟨k₂, a₂, σ₂, hσ₂⟩ := exists_hom_model hc M₁.R₀ M₁.R₀ M₁.finitePresentation_R₀
    M₁.finitePresentation_R₀ M₁.eR M₁.eR symm
  let M₂ := M₁.restrict a₂
  replace hσ₂ : (Over.pullback (c.π.app M₂.stage)).map σ₂ ≫ M₂.eR.hom = M₂.eR.hom ≫ symm :=
    hσ₂
  let r₂ := (Over.pullback (D.map a₂)).map r₁
  have hr₂ : (Over.pullback (c.π.app M₂.stage)).map r₂ ≫ M₂.eR.hom = M₂.eW.hom ≫ refl :=
    isModel_restrict a₂ M₁.eW M₁.eR hr₁
  let P := pullback M₂.t₀ M₂.s₀
  have hP : FinitePresentation P.hom :=
    finitePresentation_pullback_hom _ _ M₂.finitePresentation_R₀ M₂.finitePresentation_R₀
      M₂.finitePresentation_W₀
  let F := Over.pullback (c.π.app M₂.stage)
  have hPF : IsPullback (F.map (pullback.fst M₂.t₀ M₂.s₀) ≫ M₂.eR.hom)
      (F.map (pullback.snd M₂.t₀ M₂.s₀) ≫ M₂.eR.hom) t s := by
    exact ((IsPullback.of_hasPullback M₂.t₀ M₂.s₀).map F).of_iso (Iso.refl _) M₂.eR M₂.eR
      M₂.eW (by simp) (by simp) M₂.ht M₂.hs
  let eP : F.obj P ≅ pullback t s := hPF.isoPullback
  have heP₁ : eP.hom ≫ pullback.fst t s = F.map (pullback.fst M₂.t₀ M₂.s₀) ≫ M₂.eR.hom :=
    hPF.isoPullback_hom_fst
  have heP₂ : eP.hom ≫ pullback.snd t s = F.map (pullback.snd M₂.t₀ M₂.s₀) ≫ M₂.eR.hom :=
    hPF.isoPullback_hom_snd
  obtain ⟨k₃, a₃, g₃, hg₃⟩ := exists_hom_model hc P M₂.R₀ hP M₂.finitePresentation_R₀ eP
    M₂.eR comp
  let G₃ := Over.pullback (D.map a₃)
  let F₃ := Over.pullback (c.π.app k₃)
  let Φ₃ := overPullbackCompIso (D.map a₃) (c.π.app k₃) (c.π.app M₂.stage) (c.w a₃)
  let eW₃ := Φ₃ M₂.W₀ ≪≫ M₂.eW
  let eR₃ := Φ₃ M₂.R₀ ≪≫ M₂.eR
  let eP₃ := Φ₃ P ≪≫ eP
  let s₃ := G₃.map M₂.s₀
  let t₃ := G₃.map M₂.t₀
  have hs₃ : F₃.map s₃ ≫ eW₃.hom = eR₃.hom ≫ s := isModel_restrict a₃ M₂.eR M₂.eW M₂.hs
  have ht₃ : F₃.map t₃ ≫ eW₃.hom = eR₃.hom ≫ t := isModel_restrict a₃ M₂.eR M₂.eW M₂.ht
  let r₃ := G₃.map r₂
  have hr₃ : F₃.map r₃ ≫ eR₃.hom = eW₃.hom ≫ refl := isModel_restrict a₃ M₂.eW M₂.eR hr₂
  let σ₃ := G₃.map σ₂
  have hσ₃ : F₃.map σ₃ ≫ eR₃.hom = eR₃.hom ≫ symm := isModel_restrict a₃ M₂.eR M₂.eR hσ₂
  replace hg₃ : F₃.map g₃ ≫ eR₃.hom = eP₃.hom ≫ comp := hg₃
  let comp₃ : pullback t₃ s₃ ⟶ G₃.obj M₂.R₀ := (PreservesPullback.iso G₃ M₂.t₀ M₂.s₀).inv ≫ g₃
  have key : ∀ (p : P ⟶ M₂.R₀) (p' : pullback t₃ s₃ ⟶ G₃.obj M₂.R₀) (q : pullback t s ⟶ R),
      (PreservesPullback.iso G₃ M₂.t₀ M₂.s₀).inv ≫ G₃.map p = p' →
      eP.hom ≫ q = F.map p ≫ M₂.eR.hom →
      F₃.map p' ≫ eR₃.hom = F₃.map (PreservesPullback.iso G₃ M₂.t₀ M₂.s₀).inv ≫ eP₃.hom ≫ q := by
    intro p p' q hp hq
    calc F₃.map p' ≫ eR₃.hom
        = F₃.map (PreservesPullback.iso G₃ M₂.t₀ M₂.s₀).inv ≫
            F₃.map (G₃.map p) ≫ (Φ₃ M₂.R₀).hom ≫ M₂.eR.hom := by
          rw [← hp, F₃.map_comp_assoc]
          rfl
      _ = F₃.map (PreservesPullback.iso G₃ M₂.t₀ M₂.s₀).inv ≫ (Φ₃ P).hom ≫
            F.map p ≫ M₂.eR.hom := by
          rw [reassoc_of% (overPullbackCompIso_naturality (D.map a₃) (c.π.app k₃)
            (c.π.app M₂.stage) (c.w a₃) p)]
      _ = F₃.map (PreservesPullback.iso G₃ M₂.t₀ M₂.s₀).inv ≫ eP₃.hom ≫ q := by
          rw [← hq]
          rfl
  have hfst : F₃.map (pullback.fst t₃ s₃) ≫ eR₃.hom =
      F₃.map (PreservesPullback.iso G₃ M₂.t₀ M₂.s₀).inv ≫ eP₃.hom ≫ pullback.fst t s :=
    key _ _ _ (PreservesPullback.iso_inv_fst G₃ M₂.t₀ M₂.s₀) heP₁
  have hsnd : F₃.map (pullback.snd t₃ s₃) ≫ eR₃.hom =
      F₃.map (PreservesPullback.iso G₃ M₂.t₀ M₂.s₀).inv ≫ eP₃.hom ≫ pullback.snd t s :=
    key _ _ _ (PreservesPullback.iso_inv_snd G₃ M₂.t₀ M₂.s₀) heP₂
  have hcomp₃ : F₃.map comp₃ ≫ eR₃.hom =
      F₃.map (PreservesPullback.iso G₃ M₂.t₀ M₂.s₀).inv ≫ eP₃.hom ≫ comp := by
    rw [F₃.map_comp, Category.assoc, hg₃]
  have hW₃ : FinitePresentation (G₃.obj M₂.W₀).hom :=
    finitePresentation_overPullbackObj _ _ M₂.finitePresentation_W₀
  have hR₃ : FinitePresentation (G₃.obj M₂.R₀).hom :=
    finitePresentation_overPullbackObj _ _ M₂.finitePresentation_R₀
  have hQ : FinitePresentation (pullback t₃ s₃).hom :=
    finitePresentation_pullback_hom _ _ hR₃ hR₃ hW₃
  have e₁ : F₃.map (r₃ ≫ s₃) = F₃.map (𝟙 _) := by
    refine (cancel_mono eW₃.hom).1 ?_
    rw [F₃.map_comp, Category.assoc, hs₃, reassoc_of% hr₃, h₁, F₃.map_id]
    simp
  have e₂ : F₃.map (r₃ ≫ t₃) = F₃.map (𝟙 _) := by
    refine (cancel_mono eW₃.hom).1 ?_
    rw [F₃.map_comp, Category.assoc, ht₃, reassoc_of% hr₃, h₂, F₃.map_id]
    simp
  have e₃ : F₃.map (σ₃ ≫ s₃) = F₃.map t₃ := by
    refine (cancel_mono eW₃.hom).1 ?_
    rw [F₃.map_comp, Category.assoc, hs₃, reassoc_of% hσ₃, h₃, ht₃]
  have e₄ : F₃.map (σ₃ ≫ t₃) = F₃.map s₃ := by
    refine (cancel_mono eW₃.hom).1 ?_
    rw [F₃.map_comp, Category.assoc, ht₃, reassoc_of% hσ₃, h₄, hs₃]
  have e₅ : F₃.map (comp₃ ≫ s₃) = F₃.map (pullback.fst t₃ s₃ ≫ s₃) := by
    refine (cancel_mono eW₃.hom).1 ?_
    simp only [comp₃, F₃.map_comp, Category.assoc, hs₃, reassoc_of% hg₃, reassoc_of% hfst, h₅]
  have e₆ : F₃.map (comp₃ ≫ t₃) = F₃.map (pullback.snd t₃ s₃ ≫ t₃) := by
    refine (cancel_mono eW₃.hom).1 ?_
    simp only [comp₃, F₃.map_comp, Category.assoc, ht₃, reassoc_of% hg₃, reassoc_of% hsnd, h₆]
  obtain ⟨k, a, ha⟩ := (((((eventuallyBelow_map_eq hc hW₃ hW₃ e₁).and
    (eventuallyBelow_map_eq hc hW₃ hW₃ e₂)).and (eventuallyBelow_map_eq hc hR₃ hW₃ e₃)).and
    (eventuallyBelow_map_eq hc hR₃ hW₃ e₄)).and (eventuallyBelow_map_eq hc hQ hW₃ e₅)).and
    (eventuallyBelow_map_eq hc hQ hW₃ e₆)
  obtain ⟨⟨⟨⟨⟨f₁, f₂⟩, f₃⟩, f₄⟩, f₅⟩, f₆⟩ := ha (𝟙 k)
  rw [Category.id_comp] at f₁ f₂ f₃ f₄ f₅ f₆
  exact ⟨(M₂.restrict a₃).restrict a,
    IsGroupoidRelation.of_map_eq (Over.pullback (D.map a)) r₃ σ₃ comp₃ f₁ f₂ f₃ f₄ f₅ f₆⟩

/-! ### All properties at once -/

omit [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- If, under a hypothesis `P`, some restriction of a model satisfies `Q`, then some restriction
satisfies `P → Q`. -/
lemma exists_restrict_imp {P : Prop} {Q : RelationModel c s t → Prop}
    (h : P → ∃ (k : I) (a : k ⟶ M.stage), Q (M.restrict a)) :
    ∃ (k : I) (a : k ⟶ M.stage), P → Q (M.restrict a) := by
  by_cases hP : P
  · obtain ⟨k, a, ha⟩ := h hP
    exact ⟨k, a, fun _ => ha⟩
  · exact ⟨M.stage, 𝟙 _, fun h' => absurd h' hP⟩

end RelationModel

/-- Let `s, t : R ⟶ W` be morphisms of schemes of finite presentation over the limit of a
cofiltered system of quasi-compact quasi-separated schemes with affine transition morphisms.
Assume `s` and `t` are étale, `(s, t) : R ⟶ W ×_S W` is a monomorphism, `W` is affine over the
limit and the relation is reflexive, symmetric and transitive. Then the relation has a model over
a stage with the same properties; it can moreover be chosen with `(s, t)` a closed immersion if
that holds over the limit, and with `W` flat over the stage if `W` is flat over the limit. -/
theorem RelationModel.exists_etaleEquivalenceRelation (hc : IsLimit c) {W R : Over c.pt}
    (s t : R ⟶ W) (hW : FinitePresentation W.hom) (hR : FinitePresentation R.hom)
    [Etale s.left] [Etale t.left] [Mono (prod.lift s t).left] [IsAffineHom W.hom]
    (hgrp : IsGroupoidRelation s t) :
    ∃ M : RelationModel c s t, Etale M.s₀.left ∧ Etale M.t₀.left ∧
      Mono (prod.lift M.s₀ M.t₀).left ∧ IsAffineHom M.W₀.hom ∧ IsGroupoidRelation M.s₀ M.t₀ ∧
      (IsClosedImmersion (prod.lift s t).left → IsClosedImmersion (prod.lift M.s₀ M.t₀).left) ∧
      (Flat W.hom → Flat M.W₀.hom) := by
  obtain ⟨M₀⟩ := RelationModel.exists_model (s := s) (t := t) hc hW hR
  obtain ⟨M₁, g₁⟩ := M₀.exists_isGroupoidRelation hc hgrp
  obtain ⟨k₂, a₂, e₂⟩ := M₁.exists_restrict_etale_s₀ hc
  let M₂ := M₁.restrict a₂
  have g₂ := M₁.isGroupoidRelation_restrict g₁ a₂
  obtain ⟨k₃, a₃, e₃⟩ := M₂.exists_restrict_etale_t₀ hc
  let M₃ := M₂.restrict a₃
  have g₃ := M₂.isGroupoidRelation_restrict g₂ a₃
  have e₂' := M₂.etale_restrict_s₀ a₃ e₂
  obtain ⟨k₄, a₄, m₄⟩ := M₃.exists_restrict_mono_prodLift hc
  let M₄ := M₃.restrict a₄
  have g₄ := M₃.isGroupoidRelation_restrict g₃ a₄
  have e₂'' := M₃.etale_restrict_s₀ a₄ e₂'
  have e₃' := M₃.etale_restrict_t₀ a₄ e₃
  obtain ⟨k₅, a₅, f₅⟩ := M₄.exists_restrict_isAffineHom_W₀ hc
  let M₅ := M₄.restrict a₅
  have g₅ := M₄.isGroupoidRelation_restrict g₄ a₅
  have e₂₅ := M₄.etale_restrict_s₀ a₅ e₂''
  have e₃₅ := M₄.etale_restrict_t₀ a₅ e₃'
  have m₅ := M₄.prop_prodLift_restrict (MorphismProperty.monomorphisms Scheme.{u}) m₄ a₅
  obtain ⟨k₆, a₆, c₆⟩ := M₅.exists_restrict_imp
    (P := IsClosedImmersion (prod.lift s t).left)
    (Q := fun M' => IsClosedImmersion (prod.lift M'.s₀ M'.t₀).left)
    (fun _ => M₅.exists_restrict_isClosedImmersion_prodLift hc)
  let M₆ := M₅.restrict a₆
  obtain ⟨k₇, a₇, f₇⟩ := M₆.exists_restrict_imp (P := Flat W.hom)
    (Q := fun M' => Flat M'.W₀.hom) (fun _ => M₆.exists_restrict_flat_W₀ hc)
  refine ⟨M₆.restrict a₇, M₆.etale_restrict_s₀ a₇ (M₅.etale_restrict_s₀ a₆ e₂₅),
    M₆.etale_restrict_t₀ a₇ (M₅.etale_restrict_t₀ a₆ e₃₅),
    M₆.prop_prodLift_restrict (MorphismProperty.monomorphisms Scheme.{u})
      (M₅.prop_prodLift_restrict (MorphismProperty.monomorphisms Scheme.{u}) m₅ a₆) a₇,
    M₆.prop_W₀_restrict @IsAffineHom (M₅.prop_W₀_restrict @IsAffineHom f₅ a₆) a₇,
    M₆.isGroupoidRelation_restrict (M₅.isGroupoidRelation_restrict g₅ a₆) a₇,
    fun h => M₆.prop_prodLift_restrict @IsClosedImmersion (c₆ h) a₇, f₇⟩

end AlgebraicGeometry
