module

public import StacksFrontier.AlgebraicGeometry.LimitApprox.DescendOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.GluedEtaleRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The system of glued étale equivalence relations of the proof of Stacks 07SU

In the proof of absolute Noetherian approximation (Stacks 07SU) one is given an inverse system
of algebraic spaces `U_j`, schemes `V_j` with open subschemes `W_j ⊆ V_j`, and étale morphisms
`W_j ⟶ U_j`, all compatible with the transition maps. For each `j` one forms the kernel pair
`P_j = W_j ×_{U_j} W_j` (a scheme, since the diagonal of `U_j` is representable) and glues

```
W_j  --δ_j-->  P_j
 |              |
ι_j            b_j
 v              v
V_j  --a_j-->  R_j
```

along the diagonal `δ_j`. The two projections of `P_j` extend by the identity of `V_j` to étale
morphisms `s_j, t_j : R_j ⟶ V_j`, and `(t_j, s_j)` is an étale equivalence relation on `V_j`.
The source asserts moreover that the squares formed by `R_j ⟶ R_{j'}`, `s_j`, `s_{j'}` and
`V_j ⟶ V_{j'}` are cartesian (Stacks 07SV), and that `R_j` is quasi-compact.

This file performs this construction functorially in `j`, inside the big fppf site of `S`, in the
form consumed by `AlgebraicGeometry.Space.relationQuotientSystem`.

## Main definitions

* `AlgebraicGeometry.Space.GluedRelationSystemData`: the input of the construction.
* `AlgebraicGeometry.Space.GluedRelationSystemData.P`: the kernel pairs `P_j = W_j ×_{U_j} W_j`,
  with
  projections `p₁`, `p₂` and diagonal `δ`.
* `AlgebraicGeometry.Space.GluedRelationSystemData.R`: the glued schemes `R_j = V_j ⊔_{W_j} P_j`,
  with
  charts `a`, `b` and source and target maps `s`, `t`.

## Main results

* `AlgebraicGeometry.Space.GluedRelationSystemData.isPullback_p`: `P_j` is the kernel pair of
  `W_j ⟶ U_j`; its projections are étale (`etale_p₁`, `etale_p₂`), its diagonal is an open
  immersion (`isOpenImmersion_δ`), and `(p₂, p₁)` is an equivalence relation
  (`isEquivalenceRelation_p`, Stacks 0262 part (1)).
* `AlgebraicGeometry.Space.GluedRelationSystemData.isPushout`: `R_j` is the pushout of `ι_j` and
  `δ_j`.
* `AlgebraicGeometry.Space.GluedRelationSystemData.isEtaleEquivalenceRelation`: `(t_j, s_j)` is an
  étale equivalence relation on `V_j` over `S`.
* `AlgebraicGeometry.Space.GluedRelationSystemData.isPullback_R_map`: the source squares are
  cartesian (Stacks 07SV), and `isPullback_a`: so are the chart squares.
* `AlgebraicGeometry.Space.GluedRelationSystemData.compactSpace_R`,
  `AlgebraicGeometry.Space.GluedRelationSystemData.quasiCompact_s`,
  `AlgebraicGeometry.Space.GluedRelationSystemData.locallyOfFiniteType_R`: finiteness of the `R_j`.
* `AlgebraicGeometry.Space.isEquivalenceRelation_overLeft`,
  `AlgebraicGeometry.Space.isEquivalenceRelation_of_overLeft`: an equivalence relation in a
  slice category `Over S` is the same as one in the base whose maps lie over `S`.

## Implementation notes

The kernel pairs are lifted through the Yoneda embedding with
`CategoryTheory.Functor.essImage.liftFunctor` applied to the pullback `h_W ×_U h_W` in the
functor category. The glued schemes are built componentwise as Mathlib's pushouts of open
immersions of schemes, and placed in the site by the size bound of Stacks 000Q for a scheme
covered by two opens of the site. The étale equivalence relation is
`AlgebraicGeometry.etale_and_isEquivalenceRelation_of_isPushout`, and the cartesian squares are
`AlgebraicGeometry.isPullback_gluedRelationSource_of_isPullback`, reflected from schemes to the
site by the faithful functor `BigFppfOver.toScheme`, which reflects fibre products.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07SV](https://stacks.math.columbia.edu/tag/07SV)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

/-! ### Equivalence relations in a slice category and in the base -/

section OverTransport

variable {C : Type*} [Category* C] {S : C}

/-- A jointly monic pair of morphisms of a slice category `Over S` stays jointly monic in the
base category. -/
theorem jointlyMono₂_overLeft {R X Y : Over S} (p₁ : R ⟶ X) (p₂ : R ⟶ Y) [JointlyMono₂ p₁ p₂] :
    JointlyMono₂ p₁.left p₂.left := by
  refine ⟨fun Z a b h₁ h₂ => ?_⟩
  have hb : b ≫ R.hom = a ≫ R.hom := by
    rw [← Over.w p₁, ← Category.assoc, ← Category.assoc, h₁]
  exact congrArg CommaMorphism.left (JointlyMono₂.right_cancellation (p₁ := p₁) (p₂ := p₂)
    (Over.homMk a rfl : Over.mk (a ≫ R.hom) ⟶ R) (Over.homMk b hb) (by ext; simpa using h₁)
    (by ext; simpa using h₂))

/-- An equivalence relation in a slice category `Over S` is an equivalence relation in the base
category. -/
theorem isEquivalenceRelation_overLeft {R X : Over S} (p₁ p₂ : R ⟶ X)
    [IsEquivalenceRelation p₁ p₂] :
    IsEquivalenceRelation p₁.left p₂.left := by
  obtain ⟨e⟩ := ‹IsEquivalenceRelation p₁ p₂›.nonempty_equivalenceRelation
  have : JointlyMono₂ p₁ p₂ := e.toJointlyMono₂
  have : JointlyMono₂ ((Over.forget S).map p₁) ((Over.forget S).map p₂) :=
    jointlyMono₂_overLeft p₁ p₂
  exact EquivalenceRelation.isEquivalenceRelation
    { __ := e.toReflexiveRelation.map (Over.forget S)
      __ := e.toSymmetricRelation.map (Over.forget S)
      __ := e.toTransitiveRelation.map (Over.forget S) }

/-- A pair of morphisms of a slice category `Over S` whose underlying pair is an equivalence
relation in the base category is an equivalence relation in `Over S`. -/
@[sga "3 IV 3.1.3" "special case"]
theorem isEquivalenceRelation_of_overLeft [HasPullbacks C] {R X : Over S} (p₁ p₂ : R ⟶ X)
    [IsEquivalenceRelation p₁.left p₂.left] : IsEquivalenceRelation p₁ p₂ := by
  obtain ⟨e⟩ := ‹IsEquivalenceRelation p₁.left p₂.left›.nonempty_equivalenceRelation
  have hR : ∀ {Z : C} (x : Z ⟶ R.left), x ≫ R.hom = x ≫ p₁.left ≫ X.hom := fun x => by
    rw [Over.w p₁]
  let L : (pullback p₂ p₁).left ⟶ e.c.pt :=
    PullbackCone.IsLimit.lift e.isLimit (pullback.fst p₂ p₁).left (pullback.snd p₂ p₁).left
      (by simpa using congrArg CommaMorphism.left (pullback.condition (f := p₂) (g := p₁)))
  have hL : L ≫ e.c.fst = (pullback.fst p₂ p₁).left := PullbackCone.IsLimit.lift_fst _ _ _ _
  have hL' : L ≫ e.c.snd = (pullback.snd p₂ p₁).left := PullbackCone.IsLimit.lift_snd _ _ _ _
  exact EquivalenceRelation.isEquivalenceRelation
    { right_cancellation := fun Z a b h₁ h₂ => Over.OverMorphism.ext
        (e.right_cancellation _ _ (by simpa using congrArg CommaMorphism.left h₁)
          (by simpa using congrArg CommaMorphism.left h₂))
      r := Over.homMk e.r (by rw [hR, e.reflexivity₁_assoc])
      reflexivity₁ := by ext; simp
      reflexivity₂ := by ext; simp
      s := Over.homMk e.s (by rw [hR, e.symmetry₁_assoc, Over.w p₂])
      symmetry₁ := by ext; simpa using e.symmetry₁
      symmetry₂ := by ext; simpa using e.symmetry₂
      c := pullback.cone p₂ p₁
      isLimit := pullback.isLimit p₂ p₁
      t := Over.homMk (L ≫ e.t) (by
        rw [hR, Category.assoc, e.transitivity₁_assoc, ← Category.assoc, hL, Over.w p₁,
          Over.w (pullback.fst p₂ p₁)]
        rfl)
      transitivity₁ := by
        ext
        simp only [Over.comp_left, Over.homMk_left, Category.assoc, e.transitivity₁]
        rw [← Category.assoc, hL]
        rfl
      transitivity₂ := by
        ext
        simp only [Over.comp_left, Over.homMk_left, Category.assoc, e.transitivity₂]
        rw [← Category.assoc, hL']
        rfl }

end OverTransport

/-! ### The input data -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The input of the construction of the relations `R_i ⇉ V_i` in the proof of Stacks 07SU: a
diagram `D` of algebraic spaces (the stages `U_i`), diagrams `V` and `W` of objects of the big
fppf site of `S` with an objectwise open immersion `ι : W ⟶ V`, and a natural transformation
`g : h_W ⟶ D` with étale components. -/
structure GluedRelationSystemData (J : Type*) [Category* J] where
  /-- The stages `U_j`, algebraic spaces over `S`. -/
  D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- Every stage `U_j` is an algebraic space. -/
  isAlgebraicSpace : ∀ j, IsAlgebraicSpace B S hS (D.obj j)
  /-- The schemes `V_j`. -/
  V : J ⥤ BigFppfOver B S hS
  /-- The open subschemes `W_j ⊆ V_j`. -/
  W : J ⥤ BigFppfOver B S hS
  /-- The inclusions `W_j ⟶ V_j`. -/
  ι : W ⟶ V
  /-- The inclusions `W_j ⟶ V_j` are open immersions. -/
  isOpenImmersion_ι :
    ∀ j, _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (ι.app j))
  /-- The étale maps `W_j ⟶ U_j`. -/
  g : W ⋙ yoneda ⟶ D
  /-- The maps `W_j ⟶ U_j` are étale. -/
  isEtale_g : ∀ j, IsEtale B S hS (g.app j)

namespace GluedRelationSystemData

variable {B S hS} {J : Type*} [Category* J] (G : GluedRelationSystemData B S hS J)

/-! ### The kernel pairs `W_j ×_{U_j} W_j` -/

/-- The map `W_j ⟶ U_j` is étale in the relatively representable sense. -/
theorem presheaf_etale_g (j : J) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (G.g.app j) := by
  have hid : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (𝟙 (G.W.obj j))) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@Etale.{u} : MorphismProperty Scheme.{u}) (𝟙 (G.W.obj j))).2
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  have h := G.isEtale_g j (G.W.obj j) (yoneda.map (𝟙 (G.W.obj j))) hid
  rwa [CategoryTheory.Functor.map_id, Category.id_comp] at h

/-- The fibre product `W_j ×_{U_j} W_j` in presheaves is a pullback of `g_j` along itself. -/
theorem isPullback_pullback_app (j : J) :
    IsPullback ((pullback.fst G.g G.g).app j) ((pullback.snd G.g G.g).app j) (G.g.app j)
      (G.g.app j) :=
  (IsPullback.of_hasPullback G.g G.g).map ((evaluation J _).obj j)

/-- The fibre product `W_j ×_{U_j} W_j` is representable, the diagonal of the algebraic space
`U_j` being representable. -/
theorem pullback_obj_mem_essImage (j : J) : yoneda.essImage ((pullback G.g G.g).obj j) := by
  obtain ⟨b, snd, fst, h⟩ := (G.isAlgebraicSpace j).diagonal_representable.of_diag (G.g.app j)
    (G.g.app j)
  exact ⟨b, ⟨h.isoIsPullback _ _ (G.isPullback_pullback_app j)⟩⟩

/-- The system of kernel pairs `P_j = W_j ×_{U_j} W_j`, as objects of the big fppf site. -/
noncomputable def P : J ⥤ BigFppfOver B S hS :=
  Functor.essImage.liftFunctor (pullback G.g G.g) yoneda G.pullback_obj_mem_essImage

/-- The system `P` represents the fibre products `W_j ×_{U_j} W_j`. -/
noncomputable def pIso : G.P ⋙ yoneda ≅ pullback G.g G.g :=
  Functor.essImage.liftFunctorCompIso _ _ _

/-- The first projections `P_j ⟶ W_j`. -/
noncomputable def p₁ : G.P ⟶ G.W :=
  (Yoneda.fullyFaithful.whiskeringRight J).preimage (G.pIso.hom ≫ pullback.fst G.g G.g)

/-- The second projections `P_j ⟶ W_j`. -/
noncomputable def p₂ : G.P ⟶ G.W :=
  (Yoneda.fullyFaithful.whiskeringRight J).preimage (G.pIso.hom ≫ pullback.snd G.g G.g)

/-- The diagonals `W_j ⟶ P_j`. -/
noncomputable def δ : G.W ⟶ G.P :=
  (Yoneda.fullyFaithful.whiskeringRight J).preimage
    (pullback.lift (𝟙 _) (𝟙 _) rfl ≫ G.pIso.inv)

/-- The first projection, read in presheaves. -/
lemma yoneda_map_p₁_app (j : J) :
    yoneda.map (G.p₁.app j) = G.pIso.hom.app j ≫ (pullback.fst G.g G.g).app j := by
  simp [p₁]

/-- The second projection, read in presheaves. -/
lemma yoneda_map_p₂_app (j : J) :
    yoneda.map (G.p₂.app j) = G.pIso.hom.app j ≫ (pullback.snd G.g G.g).app j := by
  simp [p₂]

/-- The diagonal, read in presheaves. -/
lemma yoneda_map_δ_app (j : J) :
    yoneda.map (G.δ.app j) =
      (pullback.lift (𝟙 _) (𝟙 _) rfl : G.W ⋙ yoneda ⟶ pullback G.g G.g).app j ≫
        G.pIso.inv.app j := by
  simp [δ]

/-- The diagonal is a section of the first projection. -/
@[reassoc (attr := simp)]
lemma δ_p₁ : G.δ ≫ G.p₁ = 𝟙 G.W := by
  apply (Yoneda.fullyFaithful.whiskeringRight J).map_injective
  simp only [CategoryTheory.Functor.map_comp, δ, p₁, Functor.FullyFaithful.map_preimage,
    Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_fst, CategoryTheory.Functor.map_id]

/-- The diagonal is a section of the second projection. -/
@[reassoc (attr := simp)]
lemma δ_p₂ : G.δ ≫ G.p₂ = 𝟙 G.W := by
  apply (Yoneda.fullyFaithful.whiskeringRight J).map_injective
  simp only [CategoryTheory.Functor.map_comp, δ, p₂, Functor.FullyFaithful.map_preimage,
    Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_snd, CategoryTheory.Functor.map_id]

/-- **`P_j` is the kernel pair of `g_j`.** -/
theorem isPullback_p (j : J) :
    IsPullback (yoneda.map (G.p₁.app j)) (yoneda.map (G.p₂.app j)) (G.g.app j) (G.g.app j) :=
  (G.isPullback_pullback_app j).of_iso (G.pIso.app j).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (by simp [yoneda_map_p₁_app]) (by simp [yoneda_map_p₂_app]) (by simp) (by simp)

/-- The first projection `P_j ⟶ W_j` is étale. -/
instance etale_p₁ (j : J) : Etale ((BigFppfOver.toScheme B S hS).map (G.p₁.app j)) :=
  (G.presheaf_etale_g j).property (G.g.app j) _ _ (G.isPullback_p j).flip

/-- The second projection `P_j ⟶ W_j` is étale. -/
instance etale_p₂ (j : J) : Etale ((BigFppfOver.toScheme B S hS).map (G.p₂.app j)) :=
  (G.presheaf_etale_g j).property (G.g.app j) _ _ (G.isPullback_p j)

/-- A retraction of the diagonal is a retraction of it on underlying schemes. -/
private lemma toScheme_map_δ_comp_map (q : G.P ⟶ G.W) (hq : G.δ ≫ q = 𝟙 G.W) (j : J) :
    (BigFppfOver.toScheme B S hS).map (G.δ.app j) ≫
      (BigFppfOver.toScheme B S hS).map (q.app j) = 𝟙 _ := by
  rw [← CategoryTheory.Functor.map_comp, ← NatTrans.comp_app, hq]
  simp

/-- The diagonal is a section of the first projection, on underlying schemes. -/
@[reassoc (attr := simp)]
lemma toScheme_map_δ_p₁ (j : J) :
    (BigFppfOver.toScheme B S hS).map (G.δ.app j) ≫
      (BigFppfOver.toScheme B S hS).map (G.p₁.app j) = 𝟙 _ :=
  G.toScheme_map_δ_comp_map _ G.δ_p₁ j

/-- The diagonal is a section of the second projection, on underlying schemes. -/
@[reassoc (attr := simp)]
lemma toScheme_map_δ_p₂ (j : J) :
    (BigFppfOver.toScheme B S hS).map (G.δ.app j) ≫
      (BigFppfOver.toScheme B S hS).map (G.p₂.app j) = 𝟙 _ :=
  G.toScheme_map_δ_comp_map _ G.δ_p₂ j

/-- The diagonal `W_j ⟶ P_j` is an open immersion, being a section of an étale morphism. -/
instance isOpenImmersion_δ (j : J) :
    _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (G.δ.app j)) :=
  isOpenImmersion_of_section_of_etale _ _ (G.toScheme_map_δ_p₁ j)

/-- **Stacks 0262, part (1), for the kernel pair `P_j`.** The pair of projections
`(p₂, p₁) : P_j ⟶ W_j` is an equivalence relation in the category of schemes. -/
instance isEquivalenceRelation_p (j : J) :
    IsEquivalenceRelation ((BigFppfOver.toScheme B S hS).map (G.p₂.app j))
      ((BigFppfOver.toScheme B S hS).map (G.p₁.app j)) :=
  have := isEquivalenceRelation_of_isPullback B S hS (G.g.app j) (G.p₂.app j) (G.p₁.app j)
    (G.isPullback_p j).flip
  isEquivalenceRelation_overLeft ((Over.post B.inclusion).map (G.p₂.app j))
    ((Over.post B.inclusion).map (G.p₁.app j))

/-- The structure morphisms to `S` are compatible with the morphisms of the big fppf site. -/
lemma toScheme_map_comp_inclusion_map_hom {X Y : BigFppfOver B S hS} (f : X ⟶ Y) :
    (BigFppfOver.toScheme B S hS).map f ≫ B.inclusion.map Y.hom = B.inclusion.map X.hom := by
  show B.inclusion.map f.left ≫ B.inclusion.map Y.hom = B.inclusion.map X.hom
  rw [← CategoryTheory.Functor.map_comp, Over.w]

attribute [instance] isOpenImmersion_ι

/-! ### The glued schemes `R_j = V_j ⊔_{W_j} P_j` -/

/-- The open immersion of schemes `W_j ⟶ V_j`. -/
noncomputable abbrev ιs (j : J) := (BigFppfOver.toScheme B S hS).map (G.ι.app j)

/-- The open immersion of schemes `W_j ⟶ P_j`. -/
noncomputable abbrev δs (j : J) := (BigFppfOver.toScheme B S hS).map (G.δ.app j)

/-- Naturality of the open immersions `W_j ⟶ V_j`, on underlying schemes. -/
lemma toScheme_map_ι_naturality {j j' : J} (e : j ⟶ j') :
    (BigFppfOver.toScheme B S hS).map (G.W.map e) ≫ G.ιs j' =
      G.ιs j ≫ (BigFppfOver.toScheme B S hS).map (G.V.map e) := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, G.ι.naturality]

/-- Naturality of the diagonals `W_j ⟶ P_j`, on underlying schemes. -/
lemma toScheme_map_δ_naturality {j j' : J} (e : j ⟶ j') :
    (BigFppfOver.toScheme B S hS).map (G.W.map e) ≫ G.δs j' =
      G.δs j ≫ (BigFppfOver.toScheme B S hS).map (G.P.map e) := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, G.δ.naturality]

/-- The glueing `R_j` of `V_j` and `P_j` along `W_j` belongs to the big fppf site: it is
covered by two open subschemes isomorphic to the objects `V_j` and `P_j` of the site. -/
theorem contains_pushout (j : J) : B.Contains (pushout (G.ιs j) (G.δs j)) := by
  set f := G.ιs j
  set d := G.δs j
  have h := IsPushout.of_hasPushout f d
  have := isOpenImmersion_inl_of_isPushout h
  have := isOpenImmersion_inr_of_isPushout h
  let U : ULift.{u} Bool → (pushout f d).Opens := fun i =>
    bif i.down then (pushout.inl f d).opensRange else (pushout.inr f d).opensRange
  have hcov : ⨆ i, U i = ⊤ := by
    refine top_unique fun x _ => ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    rcases exists_eq_of_isPushout_of_isOpenImmersion h x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact ⟨⟨true⟩, y, rfl⟩
    · exact ⟨⟨false⟩, y, rfl⟩
  refine (Scheme.size_le_of_iSup_eq_top U hcov).trans_lt (max_lt ?_ ?_)
  · exact (Cardinal.lt_aleph0_of_finite _).trans B.aleph0_lt_cutoff
  · refine (ciSup_le' fun i => ?_).trans_lt (max_lt (G.V.obj j).left.2 (G.P.obj j).left.2)
    rcases i with ⟨_ | _⟩
    · show Scheme.size ((pushout.inr f d).opensRange : Scheme.{u}) ≤ _
      rw [← Scheme.size_congr (pushout.inr f d).isoOpensRange]
      exact le_max_right _ _
    · show Scheme.size ((pushout.inl f d).opensRange : Scheme.{u}) ≤ _
      rw [← Scheme.size_congr (pushout.inl f d).isoOpensRange]
      exact le_max_left _ _

/-- The structure morphism `R_j ⟶ S` of the glueing. -/
noncomputable def structureMap (j : J) : pushout (G.ιs j) (G.δs j) ⟶ S :=
  pushout.desc (B.inclusion.map (G.V.obj j).hom) (B.inclusion.map (G.P.obj j).hom)
    (by rw [toScheme_map_comp_inclusion_map_hom, toScheme_map_comp_inclusion_map_hom])

/-- The structure morphism of `R_j` restricted to the chart `V_j`. -/
lemma inl_structureMap (j : J) :
    pushout.inl (G.ιs j) (G.δs j) ≫ G.structureMap j = B.inclusion.map (G.V.obj j).hom :=
  pushout.inl_desc _ _ _

/-- The structure morphism of `R_j` restricted to the chart `P_j`. -/
lemma inr_structureMap (j : J) :
    pushout.inr (G.ιs j) (G.δs j) ≫ G.structureMap j = B.inclusion.map (G.P.obj j).hom :=
  pushout.inr_desc _ _ _

/-- The object `R_j` of the big fppf site of `S`: the glueing of `V_j` and
`P_j = W_j ×_{U_j} W_j` along the open immersions `ι_j : W_j ⟶ V_j` and `δ_j : W_j ⟶ P_j`. -/
noncomputable def RObj (j : J) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (G.contains_pushout j) (G.structureMap j)

/-- The transition morphism of schemes `R_j ⟶ R_{j'}`, induced on the two charts. -/
noncomputable def RMapScheme {j j' : J} (e : j ⟶ j') :
    pushout (G.ιs j) (G.δs j) ⟶ pushout (G.ιs j') (G.δs j') :=
  pushout.desc ((BigFppfOver.toScheme B S hS).map (G.V.map e) ≫ pushout.inl (G.ιs j') (G.δs j'))
    ((BigFppfOver.toScheme B S hS).map (G.P.map e) ≫ pushout.inr (G.ιs j') (G.δs j'))
    (by
      rw [← Category.assoc, ← Category.assoc, ← G.toScheme_map_ι_naturality e,
        ← G.toScheme_map_δ_naturality e, Category.assoc, Category.assoc, pushout.condition])

/-- The transition morphism of `R` on the chart `V`. -/
lemma inl_RMapScheme {j j' : J} (e : j ⟶ j') :
    pushout.inl (G.ιs j) (G.δs j) ≫ G.RMapScheme e =
      (BigFppfOver.toScheme B S hS).map (G.V.map e) ≫ pushout.inl (G.ιs j') (G.δs j') :=
  pushout.inl_desc _ _ _

/-- The transition morphism of `R` on the chart `P`. -/
lemma inr_RMapScheme {j j' : J} (e : j ⟶ j') :
    pushout.inr (G.ιs j) (G.δs j) ≫ G.RMapScheme e =
      (BigFppfOver.toScheme B S hS).map (G.P.map e) ≫ pushout.inr (G.ιs j') (G.δs j') :=
  pushout.inr_desc _ _ _

/-- The transition morphism of `R` on the chart `V`, followed by a morphism. -/
lemma inl_RMapScheme_assoc {j j' : J} (e : j ⟶ j') {Z : Scheme.{u}}
    (h : pushout (G.ιs j') (G.δs j') ⟶ Z) :
    pushout.inl (G.ιs j) (G.δs j) ≫ G.RMapScheme e ≫ h =
      (BigFppfOver.toScheme B S hS).map (G.V.map e) ≫ pushout.inl (G.ιs j') (G.δs j') ≫ h := by
  rw [← Category.assoc, inl_RMapScheme, Category.assoc]

/-- The transition morphism of `R` on the chart `P`, followed by a morphism. -/
lemma inr_RMapScheme_assoc {j j' : J} (e : j ⟶ j') {Z : Scheme.{u}}
    (h : pushout (G.ιs j') (G.δs j') ⟶ Z) :
    pushout.inr (G.ιs j) (G.δs j) ≫ G.RMapScheme e ≫ h =
      (BigFppfOver.toScheme B S hS).map (G.P.map e) ≫ pushout.inr (G.ιs j') (G.δs j') ≫ h := by
  rw [← Category.assoc, inr_RMapScheme, Category.assoc]

/-- The transition morphisms of `R` preserve identities. -/
lemma RMapScheme_id (j : J) : G.RMapScheme (𝟙 j) = 𝟙 _ := by
  apply pushout.hom_ext <;>
    simp only [inl_RMapScheme, inr_RMapScheme, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id]

/-- The transition morphisms of `R` preserve composition. -/
lemma RMapScheme_comp {j j' j'' : J} (e : j ⟶ j') (e' : j' ⟶ j'') :
    G.RMapScheme (e ≫ e') = G.RMapScheme e ≫ G.RMapScheme e' := by
  apply pushout.hom_ext
  · rw [inl_RMapScheme, inl_RMapScheme_assoc, inl_RMapScheme, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  · rw [inr_RMapScheme, inr_RMapScheme_assoc, inr_RMapScheme, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]

/-- The transition morphisms of `R` are morphisms over `S`. -/
lemma RMapScheme_structureMap {j j' : J} (e : j ⟶ j') :
    G.RMapScheme e ≫ G.structureMap j' = G.structureMap j := by
  apply pushout.hom_ext
  · rw [inl_RMapScheme_assoc, inl_structureMap, inl_structureMap,
      toScheme_map_comp_inclusion_map_hom]
  · rw [inr_RMapScheme_assoc, inr_structureMap, inr_structureMap,
      toScheme_map_comp_inclusion_map_hom]

/-- The transition morphism `R_j ⟶ R_{j'}`, induced on the two charts. -/
noncomputable def RMap {j j' : J} (e : j ⟶ j') : G.RObj j ⟶ G.RObj j' :=
  BigFppfOver.homMk B S hS (G.contains_pushout j') (G.structureMap j') (G.RMapScheme e)
    (G.RMapScheme_structureMap e)

/-- The system of glued schemes `R_j = V_j ⊔_{W_j} (W_j ×_{U_j} W_j)` of the proof of
Stacks 07SU. -/
noncomputable def R : J ⥤ BigFppfOver B S hS where
  obj := G.RObj
  map := G.RMap
  map_id j := (BigFppfOver.toScheme B S hS).map_injective
    ((G.RMapScheme_id j).trans ((BigFppfOver.toScheme B S hS).map_id (G.RObj j)).symm)
  map_comp e e' := (BigFppfOver.toScheme B S hS).map_injective
    ((G.RMapScheme_comp e e').trans
      ((BigFppfOver.toScheme B S hS).map_comp (G.RMap e) (G.RMap e')).symm)

/-- The underlying scheme of `R_j` is the pushout `V_j ⊔_{W_j} P_j`. -/
lemma toScheme_obj_R (j : J) :
    (BigFppfOver.toScheme B S hS).obj (G.R.obj j) =
      pushout ((BigFppfOver.toScheme B S hS).map (G.ι.app j))
        ((BigFppfOver.toScheme B S hS).map (G.δ.app j)) :=
  rfl

/-- The underlying morphism of schemes of a transition morphism of `R`. -/
lemma toScheme_map_R_map {j j' : J} (e : j ⟶ j') :
    (BigFppfOver.toScheme B S hS).map (G.R.map e) = G.RMapScheme e :=
  rfl

/-- The chart `V ⟶ R`. -/
noncomputable def a : G.V ⟶ G.R where
  app j := BigFppfOver.homMk B S hS (G.contains_pushout j) (G.structureMap j)
    (pushout.inl (G.ιs j) (G.δs j)) (G.inl_structureMap j)
  naturality _ _ e := (BigFppfOver.toScheme B S hS).map_injective
    (G.inl_RMapScheme e).symm

/-- The chart `P ⟶ R`. -/
noncomputable def b : G.P ⟶ G.R where
  app j := BigFppfOver.homMk B S hS (G.contains_pushout j) (G.structureMap j)
    (pushout.inr (G.ιs j) (G.δs j)) (G.inr_structureMap j)
  naturality _ _ e := (BigFppfOver.toScheme B S hS).map_injective
    (G.inr_RMapScheme e).symm

/-- The chart `a_j : V_j ⟶ R_j` is the first coprojection of the pushout. -/
lemma toScheme_map_a_app (j : J) :
    (BigFppfOver.toScheme B S hS).map (G.a.app j) = pushout.inl (G.ιs j) (G.δs j) :=
  rfl

/-- The chart `b_j : P_j ⟶ R_j` is the second coprojection of the pushout. -/
lemma toScheme_map_b_app (j : J) :
    (BigFppfOver.toScheme B S hS).map (G.b.app j) = pushout.inr (G.ιs j) (G.δs j) :=
  rfl

/-- **The glueing square.** `R_j` is the pushout of `ι_j : W_j ⟶ V_j` and `δ_j : W_j ⟶ P_j`,
with the charts `a_j : V_j ⟶ R_j` and `b_j : P_j ⟶ R_j`. -/
theorem isPushout (j : J) :
    IsPushout ((BigFppfOver.toScheme B S hS).map (G.ι.app j))
      ((BigFppfOver.toScheme B S hS).map (G.δ.app j))
      ((BigFppfOver.toScheme B S hS).map (G.a.app j))
      ((BigFppfOver.toScheme B S hS).map (G.b.app j)) :=
  IsPushout.of_hasPushout _ _

/-- A retraction `q` of the diagonal glues with the identity of `V`. -/
lemma retraction_w (q : G.P ⟶ G.W) (hq : G.δ ≫ q = 𝟙 G.W) (j : J) :
    G.ιs j ≫ 𝟙 _ = G.δs j ≫ (BigFppfOver.toScheme B S hS).map (q.app j) ≫ G.ιs j := by
  rw [Category.comp_id, ← Category.assoc, G.toScheme_map_δ_comp_map q hq, Category.id_comp]

/-- The morphism of schemes `R_j ⟶ V_j` which is the identity on the chart `V_j` and
`q_j ≫ ι_j` on the chart `P_j`, for a retraction `q` of the diagonal. -/
noncomputable def projScheme (q : G.P ⟶ G.W) (hq : G.δ ≫ q = 𝟙 G.W) (j : J) :
    pushout (G.ιs j) (G.δs j) ⟶ (BigFppfOver.toScheme B S hS).obj (G.V.obj j) :=
  pushout.desc (𝟙 _) ((BigFppfOver.toScheme B S hS).map (q.app j) ≫ G.ιs j)
    (G.retraction_w q hq j)

/-- The morphism `projScheme` is the identity on the chart `V_j`. -/
lemma inl_projScheme (q : G.P ⟶ G.W) (hq : G.δ ≫ q = 𝟙 G.W) (j : J) :
    pushout.inl (G.ιs j) (G.δs j) ≫ G.projScheme q hq j = 𝟙 _ :=
  pushout.inl_desc _ _ _

/-- The morphism `projScheme` is `q_j ≫ ι_j` on the chart `P_j`. -/
lemma inr_projScheme (q : G.P ⟶ G.W) (hq : G.δ ≫ q = 𝟙 G.W) (j : J) :
    pushout.inr (G.ιs j) (G.δs j) ≫ G.projScheme q hq j =
      (BigFppfOver.toScheme B S hS).map (q.app j) ≫ G.ιs j :=
  pushout.inr_desc _ _ _

/-- The morphism `projScheme` is a morphism over `S`. -/
lemma projScheme_structureMap (q : G.P ⟶ G.W) (hq : G.δ ≫ q = 𝟙 G.W) (j : J) :
    G.projScheme q hq j ≫ B.inclusion.map (G.V.obj j).hom = G.structureMap j := by
  apply pushout.hom_ext
  · rw [← Category.assoc, inl_projScheme, Category.id_comp, inl_structureMap]
  · rw [← Category.assoc, inr_projScheme, inr_structureMap, Category.assoc,
      toScheme_map_comp_inclusion_map_hom, toScheme_map_comp_inclusion_map_hom]

/-- The morphisms `projScheme` are compatible with the transition morphisms. -/
lemma RMapScheme_projScheme (q : G.P ⟶ G.W) (hq : G.δ ≫ q = 𝟙 G.W) {j j' : J} (e : j ⟶ j') :
    G.RMapScheme e ≫ G.projScheme q hq j' =
      G.projScheme q hq j ≫ (BigFppfOver.toScheme B S hS).map (G.V.map e) := by
  apply pushout.hom_ext
  · rw [inl_RMapScheme_assoc, inl_projScheme, ← Category.assoc, inl_projScheme,
      Category.comp_id, Category.id_comp]
  · rw [inr_RMapScheme_assoc, inr_projScheme, ← Category.assoc (pushout.inr _ _), inr_projScheme,
      Category.assoc, ← G.toScheme_map_ι_naturality e]
    simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp, q.naturality]

/-- The morphism `R ⟶ V` which is the identity on the chart `V` and `q ≫ ι` on the chart `P`,
for a retraction `q` of the diagonal. -/
noncomputable def proj (q : G.P ⟶ G.W) (hq : G.δ ≫ q = 𝟙 G.W) : G.R ⟶ G.V where
  app j := Over.homMk (ObjectProperty.homMk (G.projScheme q hq j))
    (ObjectProperty.hom_ext _ (G.projScheme_structureMap q hq j))
  naturality _ _ e := (BigFppfOver.toScheme B S hS).map_injective
    (G.RMapScheme_projScheme q hq e)

/-- The underlying morphism of schemes of a component of `proj`. -/
lemma toScheme_map_proj_app (q : G.P ⟶ G.W) (hq : G.δ ≫ q = 𝟙 G.W) (j : J) :
    (BigFppfOver.toScheme B S hS).map ((G.proj q hq).app j) = G.projScheme q hq j :=
  rfl

/-- The morphism `proj q` is the identity on the chart `V`. -/
@[reassoc (attr := simp)]
lemma a_proj (q : G.P ⟶ G.W) (hq : G.δ ≫ q = 𝟙 G.W) : G.a ≫ G.proj q hq = 𝟙 G.V :=
  NatTrans.ext (funext fun j => (BigFppfOver.toScheme B S hS).map_injective
    ((G.inl_projScheme q hq j).trans ((BigFppfOver.toScheme B S hS).map_id _).symm))

/-- The morphism `proj q` is `q ≫ ι` on the chart `P`. -/
@[reassoc (attr := simp)]
lemma b_proj (q : G.P ⟶ G.W) (hq : G.δ ≫ q = 𝟙 G.W) : G.b ≫ G.proj q hq = q ≫ G.ι :=
  NatTrans.ext (funext fun j => (BigFppfOver.toScheme B S hS).map_injective
    ((G.inr_projScheme q hq j).trans ((BigFppfOver.toScheme B S hS).map_comp _ _).symm))

/-- The source map `s : R ⟶ V`: the identity on the chart `V` and `p₁ ≫ ι` on the chart `P`. -/
noncomputable def s : G.R ⟶ G.V := G.proj G.p₁ G.δ_p₁

/-- The target map `t : R ⟶ V`: the identity on the chart `V` and `p₂ ≫ ι` on the chart `P`. -/
noncomputable def t : G.R ⟶ G.V := G.proj G.p₂ G.δ_p₂

/-- The source map is the identity on the chart `V`. -/
@[reassoc (attr := simp)]
lemma a_s : G.a ≫ G.s = 𝟙 G.V := G.a_proj _ _

/-- The target map is the identity on the chart `V`. -/
@[reassoc (attr := simp)]
lemma a_t : G.a ≫ G.t = 𝟙 G.V := G.a_proj _ _

/-- The source map is the first projection on the chart `P`. -/
@[reassoc (attr := simp)]
lemma b_s : G.b ≫ G.s = G.p₁ ≫ G.ι := G.b_proj _ _

/-- The target map is the second projection on the chart `P`. -/
@[reassoc (attr := simp)]
lemma b_t : G.b ≫ G.t = G.p₂ ≫ G.ι := G.b_proj _ _

/-! ### The glued relation is an étale equivalence relation -/

/-- **The glued étale equivalence relation of the proof of Stacks 07SU.** The source and
target maps `s_j, t_j : R_j ⟶ V_j` are étale, and `(t_j, s_j)` is an equivalence relation on
`V_j` in the category of schemes. -/
theorem etale_and_isEquivalenceRelation (j : J) :
    Etale ((BigFppfOver.toScheme B S hS).map (G.s.app j)) ∧
      Etale ((BigFppfOver.toScheme B S hS).map (G.t.app j)) ∧
      IsEquivalenceRelation ((BigFppfOver.toScheme B S hS).map (G.t.app j))
        ((BigFppfOver.toScheme B S hS).map (G.s.app j)) :=
  etale_and_isEquivalenceRelation_of_isPushout (G.toScheme_map_δ_p₁ j) (G.toScheme_map_δ_p₂ j)
    (G.isPushout j) (G.inl_projScheme G.p₁ G.δ_p₁ j) (G.inr_projScheme G.p₁ G.δ_p₁ j)
    (G.inl_projScheme G.p₂ G.δ_p₂ j) (G.inr_projScheme G.p₂ G.δ_p₂ j)

/-- **The glued étale equivalence relation of the proof of Stacks 07SU**, as a pre-relation over
`S`: the pair `(t_j, s_j)` is an étale equivalence relation on `V_j` over `S`. -/
instance isEtaleEquivalenceRelation (j : J) :
    IsEtaleEquivalenceRelation (relation B S hS (G.s.app j) (G.t.app j)) := by
  obtain ⟨hs, ht, he⟩ := G.etale_and_isEquivalenceRelation j
  have : IsEquivalenceRelation ((Over.post B.inclusion).map (G.t.app j)).left
      ((Over.post B.inclusion).map (G.s.app j)).left := he
  exact
    { isEquivalenceRelation := by
        simpa only [relation, PreRelation.target, PreRelation.source, prod.lift_fst,
          prod.lift_snd] using isEquivalenceRelation_of_overLeft
            ((Over.post B.inclusion).map (G.t.app j)) ((Over.post B.inclusion).map (G.s.app j))
      etale_source := by
        simp only [relation, PreRelation.source, prod.lift_snd]
        exact hs
      etale_target := by
        simp only [relation, PreRelation.target, prod.lift_fst]
        exact ht }

/-! ### The transition squares are cartesian (Stacks 07SV) -/

/-- The kernel pairs are compatible with the transition maps: when the naturality squares of
`g` are cartesian, the square formed by `P_j ⟶ P_{j'}`, the first projections and
`W_j ⟶ W_{j'}` is cartesian. This is the computation
`(W_{j'} ×_{U_{j'}} W_{j'}) ×_{W_{j'}} W_j = W_j ×_{U_j} W_j` of the proof of Stacks 07SU. -/
theorem isPullback_P_map
    (hgcart : ∀ {j j' : J} (e : j ⟶ j'),
      IsPullback (yoneda.map (G.W.map e)) (G.g.app j) (G.g.app j') (G.D.map e))
    {j j' : J} (e : j ⟶ j') :
    IsPullback (G.P.map e) (G.p₁.app j) (G.p₁.app j') (G.W.map e) := by
  refine IsPullback.of_map_of_faithful (F := yoneda) ?_
  have outer := (G.isPullback_p j).flip.paste_horiz (hgcart e)
  have e₁ : ∀ q : G.P ⟶ G.W, yoneda.map (G.P.map e) ≫ yoneda.map (q.app j') =
      yoneda.map (q.app j) ≫ yoneda.map (G.W.map e) := fun q => by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, q.naturality]
  have e₂ : yoneda.map (G.W.map e) ≫ G.g.app j' = G.g.app j ≫ G.D.map e := G.g.naturality e
  rw [← e₁ G.p₂, ← e₂] at outer
  exact outer.of_right (e₁ G.p₁) (G.isPullback_p j').flip

/-- **Stacks 07SV.** When the open subschemes `W_j ⊆ V_j` and the étale maps `W_j ⟶ U_j` are
compatible with the transition maps (cartesian naturality squares), the square

```
R_j  ⟶ R_{j'}
 ↓s_j    ↓s_{j'}
V_j  ⟶ V_{j'}
```

is cartesian in the big fppf site. -/
theorem isPullback_R_map
    (hιcart : ∀ {j j' : J} (e : j ⟶ j'),
      IsPullback (G.W.map e) (G.ι.app j) (G.ι.app j') (G.V.map e))
    (hgcart : ∀ {j j' : J} (e : j ⟶ j'),
      IsPullback (yoneda.map (G.W.map e)) (G.g.app j) (G.g.app j') (G.D.map e))
    {j j' : J} (e : j ⟶ j') :
    IsPullback (G.R.map e) (G.s.app j) (G.s.app j') (G.V.map e) :=
  IsPullback.of_map_of_faithful (F := BigFppfOver.toScheme B S hS)
    (isPullback_gluedRelationSource_of_isPullback ((hιcart e).map _)
      ((G.isPullback_P_map hgcart e).map _) (G.toScheme_map_δ_p₁ j)
      (G.toScheme_map_δ_naturality e).symm (G.isPushout j) (G.isPushout j')
      (G.inl_projScheme G.p₁ G.δ_p₁ j) (G.inr_projScheme G.p₁ G.δ_p₁ j)
      (G.inl_projScheme G.p₁ G.δ_p₁ j') (G.inr_projScheme G.p₁ G.δ_p₁ j') (G.inl_RMapScheme e)
      (G.inr_RMapScheme e))

/-- The chart `V_j ⟶ R_j` is the inverse image of the chart `V_{j'} ⟶ R_{j'}`: when the
squares of `isPullback_R_map` are cartesian, so are the squares formed by `V_j ⟶ V_{j'}`, the
charts `a` and `R_j ⟶ R_{j'}`. -/
theorem isPullback_a
    (hcart : ∀ {j j' : J} (e : j ⟶ j'), IsPullback (G.R.map e) (G.s.app j) (G.s.app j') (G.V.map e))
    {j j' : J} (e : j ⟶ j') :
    IsPullback (G.V.map e) (G.a.app j) (G.a.app j') (G.R.map e) := by
  have has : ∀ k, G.a.app k ≫ G.s.app k = 𝟙 _ := fun k => by
    rw [← NatTrans.comp_app, a_s, NatTrans.id_app]
  have H : IsPullback (G.V.map e) (G.a.app j ≫ G.s.app j) (G.a.app j' ≫ G.s.app j')
      (G.V.map e) := by
    rw [has, has]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  exact H.of_bot (G.a.naturality e) (hcart e)

/-! ### Finiteness properties of the glued schemes -/

/-- **`P_j` is quasi-compact**: it is a fibre product of two quasi-compact schemes over the
quasi-separated algebraic space `U_j`. -/
theorem compactSpace_P (hZ : B.Contains (⊤_ Scheme.{u}))
    (hDqs : ∀ j, IsAbsolutelyQuasiSeparated B S hS hZ (G.D.obj j))
    (hWc : ∀ j, CompactSpace ((BigFppfOver.toScheme B S hS).obj (G.W.obj j))) (j : J) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj (G.P.obj j)) :=
  compactSpace_of_isAbsolutelyQuasiSeparated B S hS hZ (hDqs j) (G.isPullback_p j) (hWc j)
    (hWc j)

/-- **`R_j` is quasi-compact**, being covered by the quasi-compact opens `V_j` and `P_j`. -/
theorem compactSpace_R (hZ : B.Contains (⊤_ Scheme.{u}))
    (hDqs : ∀ j, IsAbsolutelyQuasiSeparated B S hS hZ (G.D.obj j))
    (hVc : ∀ j, CompactSpace ((BigFppfOver.toScheme B S hS).obj (G.V.obj j)))
    (hWc : ∀ j, CompactSpace ((BigFppfOver.toScheme B S hS).obj (G.W.obj j))) (j : J) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj (G.R.obj j)) :=
  have := hVc j
  have := G.compactSpace_P hZ hDqs hWc j
  compactSpace_of_isPushout (G.isPushout j)

/-- `W_j` is locally of finite type over `Spec ℤ`, being open in `V_j`. -/
theorem locallyOfFiniteType_W
    (hVft : ∀ j,
      LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B S hS).obj (G.V.obj j))))
    (j : J) :
    LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B S hS).obj (G.W.obj j))) := by
  have := hVft j
  rw [← terminal.comp_from (G.ιs j)]
  infer_instance

/-- `P_j` is locally of finite type over `Spec ℤ`, being étale over `W_j`. -/
theorem locallyOfFiniteType_P
    (hVft : ∀ j,
      LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B S hS).obj (G.V.obj j))))
    (j : J) :
    LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B S hS).obj (G.P.obj j))) := by
  have := G.locallyOfFiniteType_W hVft j
  rw [← terminal.comp_from ((BigFppfOver.toScheme B S hS).map (G.p₁.app j))]
  infer_instance

/-- `R_j` is locally of finite type over `Spec ℤ`, being covered by `V_j` and `P_j`. -/
theorem locallyOfFiniteType_R
    (hVft : ∀ j,
      LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B S hS).obj (G.V.obj j))))
    (j : J) :
    LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B S hS).obj (G.R.obj j))) := by
  have : IsZariskiLocalAtSource @LocallyOfFiniteType :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
      (Q := RingHom.FiniteType)
  have := hVft j
  have := G.locallyOfFiniteType_P hVft j
  exact IsZariskiLocalAtSource.of_isPushout (G.isPushout j)
    (by rw [terminal.comp_from]; infer_instance) (by rw [terminal.comp_from]; infer_instance)

/-- The source map `s_j : R_j ⟶ V_j` is quasi-compact: `R_j` is quasi-compact and `V_j`, being
locally of finite type over `Spec ℤ`, is quasi-separated. -/
theorem quasiCompact_s (hZ : B.Contains (⊤_ Scheme.{u}))
    (hDqs : ∀ j, IsAbsolutelyQuasiSeparated B S hS hZ (G.D.obj j))
    (hVc : ∀ j, CompactSpace ((BigFppfOver.toScheme B S hS).obj (G.V.obj j)))
    (hWc : ∀ j, CompactSpace ((BigFppfOver.toScheme B S hS).obj (G.W.obj j)))
    (hVft : ∀ j,
      LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B S hS).obj (G.V.obj j))))
    (j : J) :
    QuasiCompact ((BigFppfOver.toScheme B S hS).map (G.s.app j)) :=
  have := hVft j
  have := quasiSeparatedSpace_of_locallyOfFiniteType_terminal
    ((BigFppfOver.toScheme B S hS).obj (G.V.obj j))
  have := G.compactSpace_R hZ hDqs hVc hWc j
  inferInstance

end GluedRelationSystemData

end AlgebraicGeometry.Space
