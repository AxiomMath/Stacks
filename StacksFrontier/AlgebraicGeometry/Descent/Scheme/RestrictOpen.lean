module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.SingleMorphism

/-!
# Restricting a descent datum to an invariant open

Let `f : X ⟶ S` be a morphism of schemes and let `(V, φ)` be a descent datum relative to
`X/S`, so that `φ : V ×_S X ≅ X ×_S V` is an isomorphism of schemes over `X ×_S X`. An open
`W ⊆ V` is *invariant* when `φ` carries `W ×_S X` onto `X ×_S W`. For such a `W` the gluing
isomorphism restricts, and `W` with the restricted isomorphism is again a descent datum
relative to `X/S`.

## Main definitions

* `AlgebraicGeometry.DescentDatum.IsTransitionInvariant` is invariance of an open of `V`
  under the gluing isomorphism: the image of `W ×_S X` under `φ` *equals* `X ×_S W`.
* `AlgebraicGeometry.DescentDatum.restrictOpen` is the descent datum carried by an invariant
  open: its scheme over `X` is `W` with the structure morphism inherited from `V`, and its
  gluing isomorphism is the restriction of `φ`.
* `AlgebraicGeometry.DescentDatum.restrictOpenObj`, `restrictOpenι` and `restrictOpenιMap`
  are `W` as a scheme over `X`, the open immersion `W ⟶ V` of `X`-schemes, and that open
  immersion base changed to a morphism of `S`-schemes.
* `AlgebraicGeometry.DescentDatum.restrictOpenGluing` and `restrictOpenGluingInv` are the
  restricted gluing map and its inverse as morphisms of `S`-schemes, and
  `AlgebraicGeometry.DescentDatum.restrictOpenTransition` is the resulting isomorphism over
  `X ×_S X`.

## Main results

* `AlgebraicGeometry.DescentDatum.restrictOpen_over`: the scheme over `X` underlying the
  restricted datum is `W` with the inherited structure morphism.
* `AlgebraicGeometry.DescentDatum.restrictOpen_transition_hom_left`: the restricted gluing
  isomorphism commutes with `φ` along the two open immersions `W ×_S X ⟶ V ×_S X` and
  `X ×_S W ⟶ X ×_S V`.
* `AlgebraicGeometry.DescentDatum.eq_restrictOpen_transition_hom_left`: a morphism
  `W ×_S X ⟶ X ×_S W` commuting with `φ` along the two open immersions is the restricted
  gluing isomorphism.
* `AlgebraicGeometry.DescentDatum.restrictOpen_cocycle`: the cocycle condition for the
  restricted gluing map.

## References

* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f) (W : D.over.left.Opens)

/-! ### The open subscheme as a scheme over `X` -/

/-- An open `W` of the scheme `V` underlying a descent datum, as a scheme over `X`: the open
subscheme `W` with the structure morphism inherited from `V`. -/
abbrev restrictOpenObj : Over X := Over.mk (W.ι ≫ D.over.hom)

/-- The open immersion `W ⟶ V`, as a morphism of schemes over `X`. -/
abbrev restrictOpenι : D.restrictOpenObj W ⟶ D.over := Over.homMk W.ι

/-- The open immersion `W ⟶ V` base changed along `f`, that is, viewed as a morphism of
schemes over `S`. -/
abbrev restrictOpenιMap :
    (Over.map f).obj (D.restrictOpenObj W) ⟶ (Over.map f).obj D.over :=
  (Over.map f).map (D.restrictOpenι W)

/-- The morphism of schemes underlying `AlgebraicGeometry.DescentDatum.restrictOpenιMap` is
the open immersion `W ⟶ V`. -/
lemma restrictOpenιMap_left : (D.restrictOpenιMap W).left = W.ι := rfl

/-- The open immersion `W ⟶ V` is a monomorphism of `S`-schemes. -/
instance : Mono (D.restrictOpenιMap W) :=
  Over.mono_of_mono_left _ (hk := inferInstanceAs (Mono W.ι))

/-- The structure morphism of `W` over `X` factors the one of `V` through `W ⟶ V`. -/
@[reassoc (attr := simp)]
lemma restrictOpenιMap_comp_structureMap :
    D.restrictOpenιMap W ≫ structureMap f D.over = structureMap f (D.restrictOpenObj W) := by
  ext
  rfl

/-! ### Invariance of an open under the gluing isomorphism -/

/-- An open `W` of the scheme `V` underlying a descent datum is *invariant* when the gluing
isomorphism `φ : V ×_S X ≅ X ×_S V` carries `W ×_S X` onto `X ×_S W`. -/
def IsTransitionInvariant : Prop :=
  D.transitionPullbackIso.hom ''ᵁ (pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ W) =
    pullback.snd f (D.over.hom ≫ f) ⁻¹ᵁ W

/-- Invariance of an open, as the equality of opens it is defined to be. -/
lemma isTransitionInvariant_def (hW : D.IsTransitionInvariant W) :
    D.transitionPullbackIso.hom ''ᵁ (pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ W) =
      pullback.snd f (D.over.hom ≫ f) ⁻¹ᵁ W := hW

/-- Invariance, read forwards: `φ` carries a point of `W ×_S X` to a point of `X ×_S W`. -/
lemma mem_of_isTransitionInvariant (hW : D.IsTransitionInvariant W)
    (z : ↥(pullback (D.over.hom ≫ f) f)) (hz : pullback.fst (D.over.hom ≫ f) f z ∈ W) :
    pullback.snd f (D.over.hom ≫ f) (D.transitionPullbackIso.hom z) ∈ W := by
  have h : D.transitionPullbackIso.hom z ∈
      D.transitionPullbackIso.hom ''ᵁ (pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ W) := ⟨z, hz, rfl⟩
  rwa [D.isTransitionInvariant_def W hW] at h

/-- Invariance, read backwards: `φ⁻¹` carries a point of `X ×_S W` to a point of
`W ×_S X`. -/
lemma mem_of_isTransitionInvariant' (hW : D.IsTransitionInvariant W)
    (z : ↥(pullback f (D.over.hom ≫ f))) (hz : pullback.snd f (D.over.hom ≫ f) z ∈ W) :
    pullback.fst (D.over.hom ≫ f) f (D.transitionPullbackIso.inv z) ∈ W := by
  have h : z ∈ pullback.snd f (D.over.hom ≫ f) ⁻¹ᵁ W := hz
  rw [← D.isTransitionInvariant_def W hW] at h
  obtain ⟨y, hy, rfl⟩ := h
  have e : D.transitionPullbackIso.inv (D.transitionPullbackIso.hom y) = y :=
    (Scheme.homeoOfIso D.transitionPullbackIso).symm_apply_apply y
  have h' : pullback.fst (D.over.hom ≫ f) f
      (D.transitionPullbackIso.inv (D.transitionPullbackIso.hom y)) ∈ W := by
    rwa [e]
  exact h'

/-! ### The two components of the restricted gluing map, before restriction -/

/-- The composite `W ×_S X ⟶ V ×_S X ⟶ X ×_S V ⟶ V`, that is, the `V`-component of `φ`
restricted to `W ×_S X`. -/
abbrev restrictOpenSndAux :
    (Over.map f).obj (D.restrictOpenObj W) ⨯ Over.mk f ⟶ (Over.map f).obj D.over :=
  prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f)) ≫ D.transition.hom.left ≫ prod.snd

/-- The composite `X ×_S W ⟶ X ×_S V ⟶ V ×_S X ⟶ V`, that is, the `V`-component of `φ⁻¹`
restricted to `X ×_S W`. -/
abbrev restrictOpenFstAux :
    Over.mk f ⨯ (Over.map f).obj (D.restrictOpenObj W) ⟶ (Over.map f).obj D.over :=
  prod.map (𝟙 (Over.mk f)) (D.restrictOpenιMap W) ≫ D.transition.inv.left ≫ prod.fst

/-! ### Transporting between the `Over S`-products and the fibre products -/

/-- The first projection of `V ×_S X`, computed on the literal fibre product. -/
lemma prodLeftIso_hom_pullbackFst :
    (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).hom ≫
        pullback.fst (D.over.hom ≫ f) f =
      (prod.fst : (Over.map f).obj D.over ⨯ Over.mk f ⟶ (Over.map f).obj D.over).left :=
  Over.prodLeftIsoPullback_hom_fst _ _

/-- The second projection of `X ×_S V`, computed on the literal fibre product. -/
lemma prodLeftIso_hom_pullbackSnd :
    (Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj D.over)).hom ≫
        pullback.snd f (D.over.hom ≫ f) =
      (prod.snd : Over.mk f ⨯ (Over.map f).obj D.over ⟶ (Over.map f).obj D.over).left :=
  Over.prodLeftIsoPullback_hom_snd _ _

/-- The comparison `W ×_S X ⟶ V ×_S X`, followed by the projection to `V`, lands in `W`. -/
lemma prodMapιMap_left_comp_pullbackFst :
    (prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f))).left ≫
        (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).hom ≫
          pullback.fst (D.over.hom ≫ f) f =
      (prod.fst : (Over.map f).obj (D.restrictOpenObj W) ⨯ Over.mk f ⟶
        (Over.map f).obj (D.restrictOpenObj W)).left ≫ W.ι := by
  rw [D.prodLeftIso_hom_pullbackFst, ← Over.comp_left, prod.map_fst, Over.comp_left]
  rfl

/-- The comparison `X ×_S W ⟶ X ×_S V`, followed by the projection to `V`, lands in `W`. -/
lemma prodMapιMap_left_comp_pullbackSnd :
    (prod.map (𝟙 (Over.mk f)) (D.restrictOpenιMap W)).left ≫
        (Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj D.over)).hom ≫
          pullback.snd f (D.over.hom ≫ f) =
      (prod.snd : Over.mk f ⨯ (Over.map f).obj (D.restrictOpenObj W) ⟶
        (Over.map f).obj (D.restrictOpenObj W)).left ≫ W.ι := by
  rw [D.prodLeftIso_hom_pullbackSnd, ← Over.comp_left, prod.map_snd, Over.comp_left]
  rfl

/-- `AlgebraicGeometry.DescentDatum.restrictOpenSndAux` computed on the literal fibre
products: it is the gluing isomorphism followed by the projection to `V`. -/
lemma restrictOpenSndAux_left :
    (D.restrictOpenSndAux W).left =
      (prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f))).left ≫
        (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).hom ≫
          D.transitionPullbackIso.hom ≫ pullback.snd f (D.over.hom ≫ f) := by
  have hΦ : D.transitionPullbackIso.hom =
      (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).inv ≫
        D.transition.hom.left.left ≫
          (Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj D.over)).hom := rfl
  rw [hΦ]
  simp only [restrictOpenSndAux, Over.comp_left, Category.assoc, Iso.hom_inv_id_assoc,
    D.prodLeftIso_hom_pullbackSnd]

/-- `AlgebraicGeometry.DescentDatum.restrictOpenFstAux` computed on the literal fibre
products: it is the inverse of the gluing isomorphism followed by the projection to `V`. -/
lemma restrictOpenFstAux_left :
    (D.restrictOpenFstAux W).left =
      (prod.map (𝟙 (Over.mk f)) (D.restrictOpenιMap W)).left ≫
        (Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj D.over)).hom ≫
          D.transitionPullbackIso.inv ≫ pullback.fst (D.over.hom ≫ f) f := by
  have hΦ : D.transitionPullbackIso.inv =
      (Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj D.over)).inv ≫
        D.transition.inv.left.left ≫
          (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).hom := by
    simp [transitionPullbackIso, DescentData.gluingPullbackIso]
  rw [hΦ]
  simp only [restrictOpenFstAux, Over.comp_left, Category.assoc, Iso.hom_inv_id_assoc,
    D.prodLeftIso_hom_pullbackFst]

/-- If `u ≫ v` factors through the open immersion `U ⟶ V`, then `v` carries the image of `u`
into `U`. -/
private lemma apply_mem_of_comp_eq_ι {V Y Z : Scheme.{u}} (U : V.Opens) (u : Y ⟶ Z) (v : Z ⟶ V)
    (p : Y ⟶ U.toScheme) (h : u ≫ v = p ≫ U.ι) (y : Y) : v (u y) ∈ U := by
  have h1 : U.ι (p y) ∈ Set.range U.ι := Set.mem_range_self _
  rw [Scheme.Opens.range_ι, ← Scheme.Hom.comp_apply, ← h] at h1
  simpa only [Scheme.Hom.comp_apply, SetLike.mem_coe] using h1

/-- A point of `W ×_S X`, viewed in `V ×_S X`, has its `V`-coordinate in `W`. -/
lemma pullbackFst_prodLeftIso_mem
    (y : ((Over.map f).obj (D.restrictOpenObj W) ⨯ Over.mk f).left) :
    pullback.fst (D.over.hom ≫ f) f
        ((Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).hom
          ((prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f))).left y)) ∈ W :=
  apply_mem_of_comp_eq_ι W _ _ _ (D.prodMapιMap_left_comp_pullbackFst W) y

/-- A point of `X ×_S W`, viewed in `X ×_S V`, has its `V`-coordinate in `W`. -/
lemma pullbackSnd_prodLeftIso_mem
    (y : (Over.mk f ⨯ (Over.map f).obj (D.restrictOpenObj W)).left) :
    pullback.snd f (D.over.hom ≫ f)
        ((Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj D.over)).hom
          ((prod.map (𝟙 (Over.mk f)) (D.restrictOpenιMap W)).left y)) ∈ W :=
  apply_mem_of_comp_eq_ι W _ _ _ (D.prodMapιMap_left_comp_pullbackSnd W) y

/-- For an invariant open `W`, the `V`-component of `φ` restricted to `W ×_S X` has image
inside `W`. -/
lemma range_restrictOpenSndAux_le (hW : D.IsTransitionInvariant W) :
    Set.range (D.restrictOpenSndAux W).left ⊆ Set.range W.ι := by
  rw [Set.range_subset_iff, Scheme.Opens.range_ι]
  intro x
  have hsnd := D.mem_of_isTransitionInvariant W hW _ (D.pullbackFst_prodLeftIso_mem W x)
  rw [D.restrictOpenSndAux_left W]
  simpa only [Scheme.Hom.comp_apply, SetLike.mem_coe] using hsnd

/-- For an invariant open `W`, the `V`-component of `φ⁻¹` restricted to `X ×_S W` has image
inside `W`. -/
lemma range_restrictOpenFstAux_le (hW : D.IsTransitionInvariant W) :
    Set.range (D.restrictOpenFstAux W).left ⊆ Set.range W.ι := by
  rw [Set.range_subset_iff, Scheme.Opens.range_ι]
  intro x
  have hfst := D.mem_of_isTransitionInvariant' W hW _ (D.pullbackSnd_prodLeftIso_mem W x)
  rw [D.restrictOpenFstAux_left W]
  simpa only [Scheme.Hom.comp_apply, SetLike.mem_coe] using hfst

/-! ### The restricted gluing map -/

/-- The factorization of `AlgebraicGeometry.DescentDatum.restrictOpenSndAux` through the open
immersion `W ⟶ V`, on underlying schemes. -/
def restrictOpenSndLeft (hW : D.IsTransitionInvariant W) :
    ((Over.map f).obj (D.restrictOpenObj W) ⨯ Over.mk f).left ⟶ W.toScheme :=
  IsOpenImmersion.lift W.ι (D.restrictOpenSndAux W).left (D.range_restrictOpenSndAux_le W hW)

/-- `AlgebraicGeometry.DescentDatum.restrictOpenSndLeft` does factor
`AlgebraicGeometry.DescentDatum.restrictOpenSndAux`. -/
@[reassoc (attr := simp)]
lemma restrictOpenSndLeft_comp_ι (hW : D.IsTransitionInvariant W) :
    D.restrictOpenSndLeft W hW ≫ W.ι = (D.restrictOpenSndAux W).left :=
  IsOpenImmersion.lift_fac _ _ _

/-- The factorization of `AlgebraicGeometry.DescentDatum.restrictOpenFstAux` through the open
immersion `W ⟶ V`, on underlying schemes. -/
def restrictOpenFstLeft (hW : D.IsTransitionInvariant W) :
    (Over.mk f ⨯ (Over.map f).obj (D.restrictOpenObj W)).left ⟶ W.toScheme :=
  IsOpenImmersion.lift W.ι (D.restrictOpenFstAux W).left (D.range_restrictOpenFstAux_le W hW)

/-- `AlgebraicGeometry.DescentDatum.restrictOpenFstLeft` does factor
`AlgebraicGeometry.DescentDatum.restrictOpenFstAux`. -/
@[reassoc (attr := simp)]
lemma restrictOpenFstLeft_comp_ι (hW : D.IsTransitionInvariant W) :
    D.restrictOpenFstLeft W hW ≫ W.ι = (D.restrictOpenFstAux W).left :=
  IsOpenImmersion.lift_fac _ _ _

/-- The `W`-component of the restricted gluing map: the map `W ×_S X ⟶ W` given by `φ`. -/
def restrictOpenSnd (hW : D.IsTransitionInvariant W) :
    (Over.map f).obj (D.restrictOpenObj W) ⨯ Over.mk f ⟶
      (Over.map f).obj (D.restrictOpenObj W) :=
  Over.homMk (D.restrictOpenSndLeft W hW) <| by
    simpa using Over.w (D.restrictOpenSndAux W)

/-- The `W`-component of the inverse of the restricted gluing map: the map `X ×_S W ⟶ W`
given by `φ⁻¹`. -/
def restrictOpenFst (hW : D.IsTransitionInvariant W) :
    Over.mk f ⨯ (Over.map f).obj (D.restrictOpenObj W) ⟶
      (Over.map f).obj (D.restrictOpenObj W) :=
  Over.homMk (D.restrictOpenFstLeft W hW) <| by
    simpa using Over.w (D.restrictOpenFstAux W)

/-- `AlgebraicGeometry.DescentDatum.restrictOpenSnd` is a factorization of
`AlgebraicGeometry.DescentDatum.restrictOpenSndAux` through `W ⟶ V`. -/
@[reassoc (attr := simp)]
lemma restrictOpenSnd_comp_ιMap (hW : D.IsTransitionInvariant W) :
    D.restrictOpenSnd W hW ≫ D.restrictOpenιMap W = D.restrictOpenSndAux W :=
  Over.OverMorphism.ext (D.restrictOpenSndLeft_comp_ι W hW)

/-- `AlgebraicGeometry.DescentDatum.restrictOpenFst` is a factorization of
`AlgebraicGeometry.DescentDatum.restrictOpenFstAux` through `W ⟶ V`. -/
@[reassoc (attr := simp)]
lemma restrictOpenFst_comp_ιMap (hW : D.IsTransitionInvariant W) :
    D.restrictOpenFst W hW ≫ D.restrictOpenιMap W = D.restrictOpenFstAux W :=
  Over.OverMorphism.ext (D.restrictOpenFstLeft_comp_ι W hW)

/-- The restricted gluing map `W ×_S X ⟶ X ×_S W`, as a morphism of `S`-schemes. -/
def restrictOpenGluing (hW : D.IsTransitionInvariant W) :
    (Over.map f).obj (D.restrictOpenObj W) ⨯ Over.mk f ⟶
      Over.mk f ⨯ (Over.map f).obj (D.restrictOpenObj W) :=
  prod.lift (prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f)) ≫ D.transition.hom.left ≫ prod.fst)
    (D.restrictOpenSnd W hW)

/-- The inverse of the restricted gluing map, `X ×_S W ⟶ W ×_S X`. -/
def restrictOpenGluingInv (hW : D.IsTransitionInvariant W) :
    Over.mk f ⨯ (Over.map f).obj (D.restrictOpenObj W) ⟶
      (Over.map f).obj (D.restrictOpenObj W) ⨯ Over.mk f :=
  prod.lift (D.restrictOpenFst W hW)
    (prod.map (𝟙 (Over.mk f)) (D.restrictOpenιMap W) ≫ D.transition.inv.left ≫ prod.snd)

/-- The restricted gluing map commutes with `φ` along the two open immersions
`W ×_S X ⟶ V ×_S X` and `X ×_S W ⟶ X ×_S V`. -/
lemma restrictOpenGluing_comp (hW : D.IsTransitionInvariant W) :
    D.restrictOpenGluing W hW ≫ prod.map (𝟙 (Over.mk f)) (D.restrictOpenιMap W) =
      prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f)) ≫ D.transition.hom.left := by
  apply prod.hom_ext <;> simp [restrictOpenGluing]

/-- The inverse of the restricted gluing map commutes with `φ⁻¹` along the two open
immersions. -/
lemma restrictOpenGluingInv_comp (hW : D.IsTransitionInvariant W) :
    D.restrictOpenGluingInv W hW ≫ prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f)) =
      prod.map (𝟙 (Over.mk f)) (D.restrictOpenιMap W) ≫ D.transition.inv.left := by
  apply prod.hom_ext <;> simp [restrictOpenGluingInv]

/-! ### The restricted gluing map is an isomorphism over `X ×_S X` -/

/-- `φ⁻¹` preserves the first component of the base `X ×_S X`. -/
@[reassoc]
lemma transition_inv_fst_structureMap :
    D.transition.inv.left ≫ prod.fst ≫ structureMap f D.over = prod.fst := by
  simpa using congrArg (fun g ↦ g ≫ prod.fst) (Over.w D.transition.inv)

/-- `φ⁻¹` preserves the second component of the base `X ×_S X`. -/
@[reassoc]
lemma transition_inv_snd :
    D.transition.inv.left ≫ prod.snd = prod.snd ≫ structureMap f D.over := by
  simpa using congrArg (fun g ↦ g ≫ prod.snd) (Over.w D.transition.inv)

/-- The `W`-component of the restricted gluing map lies over the second factor of
`X ×_S X`. -/
@[reassoc (attr := simp)]
lemma restrictOpenSnd_comp_structureMap (hW : D.IsTransitionInvariant W) :
    D.restrictOpenSnd W hW ≫ structureMap f (D.restrictOpenObj W) = prod.snd := by
  rw [← D.restrictOpenιMap_comp_structureMap W, ← Category.assoc,
    D.restrictOpenSnd_comp_ιMap W hW]
  simp

/-- The `W`-component of the inverse of the restricted gluing map lies over the first factor
of `X ×_S X`. -/
@[reassoc (attr := simp)]
lemma restrictOpenFst_comp_structureMap (hW : D.IsTransitionInvariant W) :
    D.restrictOpenFst W hW ≫ structureMap f (D.restrictOpenObj W) = prod.fst := by
  rw [← D.restrictOpenιMap_comp_structureMap W, ← Category.assoc,
    D.restrictOpenFst_comp_ιMap W hW]
  simp [D.transition_inv_fst_structureMap]

/-- The restricted gluing map is a morphism over `X ×_S X`. -/
lemma restrictOpenGluing_over (hW : D.IsTransitionInvariant W) :
    D.restrictOpenGluing W hW ≫
        prod.map (𝟙 (Over.mk f)) (structureMap f (D.restrictOpenObj W)) =
      prod.map (structureMap f (D.restrictOpenObj W)) (𝟙 (Over.mk f)) := by
  apply prod.hom_ext <;> simp [restrictOpenGluing]

/-- The inverse of the restricted gluing map is a morphism over `X ×_S X`. -/
lemma restrictOpenGluingInv_over (hW : D.IsTransitionInvariant W) :
    D.restrictOpenGluingInv W hW ≫
        prod.map (structureMap f (D.restrictOpenObj W)) (𝟙 (Over.mk f)) =
      prod.map (𝟙 (Over.mk f)) (structureMap f (D.restrictOpenObj W)) := by
  apply prod.hom_ext <;> simp [restrictOpenGluingInv, D.transition_inv_snd]

/-- The restricted gluing map followed by its inverse is the identity of `W ×_S X`. -/
lemma restrictOpenGluing_hom_inv (hW : D.IsTransitionInvariant W) :
    D.restrictOpenGluing W hW ≫ D.restrictOpenGluingInv W hW =
      𝟙 ((Over.map f).obj (D.restrictOpenObj W) ⨯ Over.mk f) := by
  rw [← cancel_mono (prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f))), Category.assoc,
    D.restrictOpenGluingInv_comp W hW, ← Category.assoc, D.restrictOpenGluing_comp W hW,
    Category.assoc, ← Over.comp_left, Iso.hom_inv_id]
  simp

/-- The inverse followed by the restricted gluing map is the identity of `X ×_S W`. -/
lemma restrictOpenGluingInv_hom (hW : D.IsTransitionInvariant W) :
    D.restrictOpenGluingInv W hW ≫ D.restrictOpenGluing W hW =
      𝟙 (Over.mk f ⨯ (Over.map f).obj (D.restrictOpenObj W)) := by
  rw [← cancel_mono (prod.map (𝟙 (Over.mk f)) (D.restrictOpenιMap W)), Category.assoc,
    D.restrictOpenGluing_comp W hW, ← Category.assoc, D.restrictOpenGluingInv_comp W hW,
    Category.assoc, ← Over.comp_left, Iso.inv_hom_id]
  simp

/-- The restricted gluing isomorphism `W ×_S X ≅ X ×_S W`, as an isomorphism over
`X ×_S X`. -/
def restrictOpenTransition (hW : D.IsTransitionInvariant W) :
    Over.mk (prod.map (structureMap f (D.restrictOpenObj W)) (𝟙 (Over.mk f))) ≅
      Over.mk (prod.map (𝟙 (Over.mk f)) (structureMap f (D.restrictOpenObj W))) where
  hom := Over.homMk (D.restrictOpenGluing W hW) (D.restrictOpenGluing_over W hW)
  inv := Over.homMk (D.restrictOpenGluingInv W hW) (D.restrictOpenGluingInv_over W hW)
  hom_inv_id := Over.OverMorphism.ext (D.restrictOpenGluing_hom_inv W hW)
  inv_hom_id := Over.OverMorphism.ext (D.restrictOpenGluingInv_hom W hW)

/-- The cocycle condition for the restricted gluing map. -/
lemma restrictOpen_cocycle (hW : D.IsTransitionInvariant W) :
    prod.map (D.restrictOpenGluing W hW) (𝟙 (Over.mk f)) ≫
        prodMapLastTwo (D.restrictOpenGluing W hW) =
      prodMapFirstThird (D.restrictOpenGluing W hW) := by
  have hE : prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f)) ≫ D.transition.hom.left =
      D.restrictOpenGluing W hW ≫ prod.map (𝟙 (Over.mk f)) (D.restrictOpenιMap W) :=
    (D.restrictOpenGluing_comp W hW).symm
  have hnat1 := prodMapLastTwo_naturality (𝟙 (Over.mk f)) (D.restrictOpenιMap W)
    (𝟙 (Over.mk f)) (𝟙 (Over.mk f)) (D.restrictOpenιMap W)
    (D.restrictOpenGluing W hW) D.transition.hom.left hE
  have hnat2 := prodMapFirstThird_naturality (D.restrictOpenιMap W) (𝟙 (Over.mk f))
    (𝟙 (Over.mk f)) (𝟙 (Over.mk f)) (D.restrictOpenιMap W)
    (D.restrictOpenGluing W hW) D.transition.hom.left hE
  rw [← cancel_mono (prod.map (prod.map (𝟙 (Over.mk f)) (𝟙 (Over.mk f)))
    (D.restrictOpenιMap W)), Category.assoc, ← hnat1, ← hnat2, ← Category.assoc,
    prod.map_map, Category.comp_id, ← hE, prod.map_comp_id, Category.assoc,
    D.cocycle_triangle]

/-! ### The restricted descent datum -/

/-- The restriction of a descent datum to an invariant open: for a descent datum `(V, φ)`
relative to `f : X ⟶ S` and an open `W ⊆ V` invariant under `φ`, the descent datum
`(W, φ|_{W ×_S X})` whose scheme over `X` is `W` with the structure morphism inherited from `V`
and whose gluing isomorphism is the restriction of `φ`. -/
def restrictOpen (hW : D.IsTransitionInvariant W) : DescentDatum f :=
  mk' (D.restrictOpenObj W) (D.restrictOpenTransition W hW) (D.restrictOpen_cocycle W hW)

/-- The scheme over `X` underlying the restricted descent datum is `W`, with the structure
morphism inherited from `V`. -/
@[simp]
lemma restrictOpen_over (hW : D.IsTransitionInvariant W) :
    (D.restrictOpen W hW).over = Over.mk (W.ι ≫ D.over.hom) := rfl

/-- The gluing isomorphism of the restricted descent datum is the restricted gluing
isomorphism. -/
@[simp]
lemma restrictOpen_transition (hW : D.IsTransitionInvariant W) :
    (D.restrictOpen W hW).transition = D.restrictOpenTransition W hW := rfl

/-- The gluing isomorphism of the restricted descent datum commutes with `φ` along the two
open immersions `W ×_S X ⟶ V ×_S X` and `X ×_S W ⟶ X ×_S V`. -/
lemma restrictOpen_transition_hom_left (hW : D.IsTransitionInvariant W) :
    (D.restrictOpen W hW).transition.hom.left ≫
        prod.map (𝟙 (Over.mk f)) (D.restrictOpenιMap W) =
      prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f)) ≫ D.transition.hom.left :=
  D.restrictOpenGluing_comp W hW

/-- Any morphism `W ×_S X ⟶ X ×_S W` commuting with `φ` along the two open immersions is the
gluing isomorphism of the restricted descent datum. -/
lemma eq_restrictOpen_transition_hom_left (hW : D.IsTransitionInvariant W)
    (ψ : (Over.map f).obj (D.restrictOpenObj W) ⨯ Over.mk f ⟶
      Over.mk f ⨯ (Over.map f).obj (D.restrictOpenObj W))
    (h : ψ ≫ prod.map (𝟙 (Over.mk f)) (D.restrictOpenιMap W) =
      prod.map (D.restrictOpenιMap W) (𝟙 (Over.mk f)) ≫ D.transition.hom.left) :
    ψ = (D.restrictOpen W hW).transition.hom.left :=
  (cancel_mono (prod.map (𝟙 (Over.mk f)) (D.restrictOpenιMap W))).mp
    (h.trans (D.restrictOpen_transition_hom_left W hW).symm)

end DescentDatum

end AlgebraicGeometry

end
