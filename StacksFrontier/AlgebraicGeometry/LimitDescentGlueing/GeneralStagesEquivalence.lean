module

public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GeneralStages
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GeneralStagesFullyFaithful
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatStages
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finitely presented schemes over a limit of schemes

For a scheme `T` let `C_T` be the full subcategory of schemes `W` over `T` such that `W` is
quasi-compact and quasi-separated and such that the structure morphism `W ⟶ T` is locally of
finite presentation. Let `S = lim Sᵢ` be a directed inverse limit of schemes with affine
transition morphisms, with no finiteness hypothesis on the stages `Sᵢ`. The base change functors
induce an equivalence of categories `colim C_{Sᵢ} ⥤ C_S`.

The colimit is taken in `CategoryTheory.Cat`, of a strict model of the diagram `i ↦ C_{Sᵢ}`: an
object of its `j`-th stage is an object of `C_{S_k}` for some `k ≤ j` together with `k`, and its
morphisms are the morphisms of the base changes to `S_j`.

## Main definitions

* `AlgebraicGeometry.LimitDescent.CatQcqsLfp`: the category `C_T`.
* `AlgebraicGeometry.LimitDescent.Stage` and `AlgebraicGeometry.LimitDescent.stageDiagram`: the
  strict model of the diagram `i ↦ C_{Sᵢ}`, as a functor into `CategoryTheory.Cat`.
* `AlgebraicGeometry.LimitDescent.toLimit` and
  `AlgebraicGeometry.LimitDescent.baseChangeComparison`: the base change functors to the limit
  and the functor `colim C_{Sᵢ} ⥤ C_S` they induce.

## Main results

* `AlgebraicGeometry.LimitDescent.isEquivalence_baseChangeComparison`: the functor
  `colim C_{Sᵢ} ⥤ C_S` is an equivalence of categories, for a finally `u`-small index category.
* `AlgebraicGeometry.LimitDescent.isEquivalence_baseChangeComparison_of_directedSet`: the same
  for a directed set in the universe of the schemes, with no smallness hypothesis.
* `AlgebraicGeometry.LimitDescent.Stage.toCatQcqsLfp`: an equivalence `Stage D j ⥤ C_{S_j}`.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.LimitDescent

attribute [local simp] CategoryTheory.Limits.pullback.lift_fst
  CategoryTheory.Limits.pullback.lift_snd CategoryTheory.Limits.pullback.lift_fst_assoc
  CategoryTheory.Limits.pullback.lift_snd_assoc

/-! ### Iterated base change -/

section Iterated

variable {C : Type*} [Category C] [HasPullbacks C] {T T' T'' : C}

variable (f : T' ⟶ T) (g : T'' ⟶ T') (h : T'' ⟶ T) (hgf : g ≫ f = h) (X : Over T)

/-- The underlying morphism `(X ×_T T') ×_{T'} T'' ⟶ X ×_T T''` of
`AlgebraicGeometry.LimitDescent.iterPullbackIso`. -/
noncomputable def iterPullbackHom :
    Limits.pullback (Limits.pullback.snd X.hom f) g ⟶ Limits.pullback X.hom h :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, hgf])

/-- The first component of `AlgebraicGeometry.LimitDescent.iterPullbackHom` is the composite of the
two first projections. -/
@[reassoc (attr := simp)]
lemma iterPullbackHom_fst :
    iterPullbackHom f g h hgf X ≫ pullback.fst X.hom h =
      pullback.fst (pullback.snd X.hom f) g ≫ pullback.fst X.hom f :=
  pullback.lift_fst _ _ _

/-- The second component of `AlgebraicGeometry.LimitDescent.iterPullbackHom` is the second
projection. -/
@[reassoc (attr := simp)]
lemma iterPullbackHom_snd :
    iterPullbackHom f g h hgf X ≫ pullback.snd X.hom h =
      pullback.snd (pullback.snd X.hom f) g :=
  pullback.lift_snd _ _ _

/-- The underlying morphism `X ×_T T'' ⟶ (X ×_T T') ×_{T'} T''` of the inverse of
`AlgebraicGeometry.LimitDescent.iterPullbackIso`. -/
noncomputable def iterPullbackInv :
    Limits.pullback X.hom h ⟶ Limits.pullback (Limits.pullback.snd X.hom f) g :=
  pullback.lift
    (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g) (by
      rw [pullback.condition, Category.assoc, hgf]))
    (pullback.snd _ _) (pullback.lift_snd _ _ _)

/-- The component of `AlgebraicGeometry.LimitDescent.iterPullbackInv` towards `X` is the first
projection of `X ×_T T''`. -/
@[reassoc (attr := simp)]
lemma iterPullbackInv_fst_fst :
    iterPullbackInv f g h hgf X ≫ pullback.fst (pullback.snd X.hom f) g ≫
        pullback.fst X.hom f =
      pullback.fst X.hom h := by
  rw [← Category.assoc, iterPullbackInv, pullback.lift_fst, pullback.lift_fst]

/-- The component of `AlgebraicGeometry.LimitDescent.iterPullbackInv` towards `T'` is the second
projection of `X ×_T T''` followed by `g`. -/
@[reassoc (attr := simp)]
lemma iterPullbackInv_fst_snd :
    iterPullbackInv f g h hgf X ≫ pullback.fst (pullback.snd X.hom f) g ≫
        pullback.snd X.hom f =
      pullback.snd X.hom h ≫ g := by
  rw [← Category.assoc, iterPullbackInv, pullback.lift_fst, pullback.lift_snd]

/-- The component of `AlgebraicGeometry.LimitDescent.iterPullbackInv` towards `T''` is the second
projection of `X ×_T T''`. -/
@[reassoc (attr := simp)]
lemma iterPullbackInv_snd :
    iterPullbackInv f g h hgf X ≫ pullback.snd (pullback.snd X.hom f) g =
      pullback.snd X.hom h :=
  pullback.lift_snd _ _ _

/-- `AlgebraicGeometry.LimitDescent.iterPullbackInv` is a right inverse of
`AlgebraicGeometry.LimitDescent.iterPullbackHom`. -/
@[simp]
lemma iterPullbackHom_iterPullbackInv :
    iterPullbackHom f g h hgf X ≫ iterPullbackInv f g h hgf X = 𝟙 _ := by
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_
  · simp
  · simp [pullback.condition]
  · simp

/-- `AlgebraicGeometry.LimitDescent.iterPullbackInv` is a left inverse of
`AlgebraicGeometry.LimitDescent.iterPullbackHom`. -/
@[simp]
lemma iterPullbackInv_iterPullbackHom :
    iterPullbackInv f g h hgf X ≫ iterPullbackHom f g h hgf X = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- The canonical identification `(X ×_T T') ×_{T'} T'' ≅ X ×_T T''` of an iterated base change
with a base change, for `g ≫ f = h`, as an isomorphism of objects over `T''`. -/
noncomputable def iterPullbackIso :
    (Over.pullback g).obj ((Over.pullback f).obj X) ≅ (Over.pullback h).obj X where
  hom := Over.homMk (iterPullbackHom f g h hgf X) (by simp)
  inv := Over.homMk (iterPullbackInv f g h hgf X) (by simp)
  hom_inv_id := Over.OverMorphism.ext (by simp)
  inv_hom_id := Over.OverMorphism.ext (by simp)

/-- The underlying morphism of `(iterPullbackIso f g h hgf X).hom` is
`iterPullbackHom f g h hgf X`. -/
@[simp]
lemma iterPullbackIso_hom_left :
    (iterPullbackIso f g h hgf X).hom.left = iterPullbackHom f g h hgf X := rfl

/-- The underlying morphism of `(iterPullbackIso f g h hgf X).inv` is
`iterPullbackInv f g h hgf X`. -/
@[simp]
lemma iterPullbackIso_inv_left :
    (iterPullbackIso f g h hgf X).inv.left = iterPullbackInv f g h hgf X := rfl

/-- The identification of an iterated base change with a base change is the only morphism of
objects over `T''` which is the canonical one over `X`. -/
lemma eq_iterPullbackIso_hom
    (φ : (Over.pullback g).obj ((Over.pullback f).obj X) ⟶ (Over.pullback h).obj X)
    (hφ : φ.left ≫ pullback.fst X.hom h =
      pullback.fst ((Over.pullback f).obj X).hom g ≫ pullback.fst X.hom f) :
    φ = (iterPullbackIso f g h hgf X).hom := by
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
  · simpa using hφ
  · simpa using Over.w φ

/-- The component of `AlgebraicGeometry.LimitDescent.iterPullbackInv` towards `X ×_T T'` is the
morphism with components the first projection and the second projection followed by `g`. -/
@[reassoc (attr := simp)]
lemma iterPullbackInv_fst :
    iterPullbackInv f g h hgf X ≫ pullback.fst (pullback.snd X.hom f) g =
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g)
        (by rw [pullback.condition, Category.assoc, hgf]) :=
  pullback.lift_fst _ _ _

end Iterated

/-! ### Transition morphisms of base changes -/

section Proj

variable {C : Type*} [Category C] [HasPullbacks C] {T₁ T₂ T₃ Ta Tb : C}

/-- The canonical morphism `X ×_{Ta} T₂ ⟶ X ×_{Ta} T₁` over a morphism `g : T₂ ⟶ T₁` of the
bases, for `g ≫ m = n`. -/
noncomputable def bcProj (m : T₁ ⟶ Ta) (g : T₂ ⟶ T₁) (n : T₂ ⟶ Ta) (hgm : g ≫ m = n)
    (X : Over Ta) : Limits.pullback X.hom n ⟶ Limits.pullback X.hom m :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g)
    (by rw [pullback.condition, Category.assoc, hgm])

/-- The component of `AlgebraicGeometry.LimitDescent.bcProj` towards `X` is the first
projection. -/
@[reassoc (attr := simp)]
lemma bcProj_fst (m : T₁ ⟶ Ta) (g : T₂ ⟶ T₁) (n : T₂ ⟶ Ta) (hgm : g ≫ m = n) (X : Over Ta) :
    bcProj m g n hgm X ≫ pullback.fst X.hom m = pullback.fst X.hom n :=
  pullback.lift_fst _ _ _

/-- The component of `AlgebraicGeometry.LimitDescent.bcProj` towards `T₁` is the second projection
followed by `g`. -/
@[reassoc (attr := simp)]
lemma bcProj_snd (m : T₁ ⟶ Ta) (g : T₂ ⟶ T₁) (n : T₂ ⟶ Ta) (hgm : g ≫ m = n) (X : Over Ta) :
    bcProj m g n hgm X ≫ pullback.snd X.hom m = pullback.snd X.hom n ≫ g :=
  pullback.lift_snd _ _ _

/-- Base change along the identity does not move the base change. -/
lemma bcProj_id (m : T₁ ⟶ Ta) (g : T₁ ⟶ T₁) (hg : g = 𝟙 T₁) (hgm : g ≫ m = m) (X : Over Ta) :
    bcProj m g m hgm X = 𝟙 _ := by
  subst hg
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- The transition morphisms of the base changes compose. -/
lemma bcProj_comp (m : T₁ ⟶ Ta) (g : T₂ ⟶ T₁) (g' : T₃ ⟶ T₂) (G : T₃ ⟶ T₁) (hG : g' ≫ g = G)
    (n : T₂ ⟶ Ta) (hn : g ≫ m = n) (N : T₃ ⟶ Ta) (hN : G ≫ m = N) (hnN : g' ≫ n = N)
    (X : Over Ta) :
    bcProj m G N hN X = bcProj n g' N hnN X ≫ bcProj m g n hn X := by
  refine pullback.hom_ext ?_ ?_
  · simp
  · rw [bcProj_snd, Category.assoc, bcProj_snd, bcProj_snd_assoc, hG]

/-- A morphism into a base change is determined by its component towards the scheme that is
being base changed: the other component is the structure morphism of the source. -/
lemma hom_ext_fst {m' : T₁ ⟶ Tb} {Z : Over T₁} {B : Over Tb}
    {φ ψ : Z ⟶ (Over.pullback m').obj B}
    (h : φ.left ≫ pullback.fst B.hom m' = ψ.left ≫ pullback.fst B.hom m') : φ = ψ := by
  have h₁ := Over.w φ
  have h₂ := Over.w ψ
  simp only [Over.pullback_obj_hom] at h₁ h₂
  exact Over.OverMorphism.ext (pullback.hom_ext h (h₁.trans h₂.symm))

/-- The conjugate of a morphism of base changes to `T₁` by the canonical identifications of
`AlgebraicGeometry.LimitDescent.iterPullbackIso`: the base change along `g : T₂ ⟶ T₁` of a
morphism of base changes to `T₁`, read as a morphism of base changes to `T₂`. -/
noncomputable def conjIter (m : T₁ ⟶ Ta) (m' : T₁ ⟶ Tb) (g : T₂ ⟶ T₁) (n : T₂ ⟶ Ta)
    (n' : T₂ ⟶ Tb) (hm : g ≫ m = n) (hm' : g ≫ m' = n') {A : Over Ta} {B : Over Tb}
    (φ : (Over.pullback m).obj A ⟶ (Over.pullback m').obj B) :
    (Over.pullback n).obj A ⟶ (Over.pullback n').obj B :=
  (iterPullbackIso m g n hm A).inv ≫ (Over.pullback g).map φ ≫
    (iterPullbackIso m' g n' hm' B).hom

/-- The component towards `B` of the conjugate `AlgebraicGeometry.LimitDescent.conjIter` of `φ` is
`AlgebraicGeometry.LimitDescent.bcProj` followed by the component of `φ` towards `B`. -/
@[reassoc (attr := simp)]
lemma conjIter_left_fst (m : T₁ ⟶ Ta) (m' : T₁ ⟶ Tb) (g : T₂ ⟶ T₁) (n : T₂ ⟶ Ta)
    (n' : T₂ ⟶ Tb) (hm : g ≫ m = n) (hm' : g ≫ m' = n') {A : Over Ta} {B : Over Tb}
    (φ : (Over.pullback m).obj A ⟶ (Over.pullback m').obj B) :
    (conjIter m m' g n n' hm hm' φ).left ≫ pullback.fst B.hom n' =
      bcProj m g n hm A ≫ φ.left ≫ pullback.fst B.hom m' := by
  rw [conjIter]
  simp only [Over.comp_left, iterPullbackIso_inv_left, iterPullbackIso_hom_left,
    Category.assoc, iterPullbackHom_fst, Over.pullback_map_left, Over.pullback_obj_hom,
    pullback.lift_fst_assoc, iterPullbackInv_fst_assoc]
  rfl

/-- The conjugate of an identity morphism is an identity morphism. -/
lemma conjIter_id (m : T₁ ⟶ Ta) (g : T₂ ⟶ T₁) (n : T₂ ⟶ Ta) (hm : g ≫ m = n) (A : Over Ta) :
    conjIter m m g n n hm hm (𝟙 ((Over.pullback m).obj A)) = 𝟙 _ := by
  simp [conjIter]

/-- Conjugation by the canonical identifications commutes with composition. -/
lemma conjIter_comp (m : T₁ ⟶ Ta) (m' : T₁ ⟶ Tb) {Tc : C} (m'' : T₁ ⟶ Tc) (g : T₂ ⟶ T₁)
    (n : T₂ ⟶ Ta) (n' : T₂ ⟶ Tb) (n'' : T₂ ⟶ Tc) (hm : g ≫ m = n) (hm' : g ≫ m' = n')
    (hm'' : g ≫ m'' = n'') {A : Over Ta} {B : Over Tb} {E : Over Tc}
    (φ : (Over.pullback m).obj A ⟶ (Over.pullback m').obj B)
    (ψ : (Over.pullback m').obj B ⟶ (Over.pullback m'').obj E) :
    conjIter m m'' g n n'' hm hm'' (φ ≫ ψ) =
      conjIter m m' g n n' hm hm' φ ≫ conjIter m' m'' g n' n'' hm' hm'' ψ := by
  simp [conjIter]

/-- The naturality square of the canonical identification of an iterated base change with a base
change: base changing a morphism along `g` and then identifying is identifying and then
conjugating. -/
lemma pullback_map_comp_iterPullbackIso (m : T₁ ⟶ Ta) (m' : T₁ ⟶ Tb) (g : T₂ ⟶ T₁) (n : T₂ ⟶ Ta)
    (n' : T₂ ⟶ Tb) (hm : g ≫ m = n) (hm' : g ≫ m' = n') {A : Over Ta} {B : Over Tb}
    (φ : (Over.pullback m).obj A ⟶ (Over.pullback m').obj B) :
    (Over.pullback g).map φ ≫ (iterPullbackIso m' g n' hm' B).hom =
      (iterPullbackIso m g n hm A).hom ≫ conjIter m m' g n n' hm hm' φ := by
  rw [conjIter, Iso.hom_inv_id_assoc]

/-- Conjugating by the canonical identifications leaves a morphism unchanged when the base change
is along the identity. -/
lemma conjIter_of_id (m : T₁ ⟶ Ta) (m' : T₁ ⟶ Tb) (g : T₁ ⟶ T₁) (hg : g = 𝟙 T₁)
    (hm : g ≫ m = m) (hm' : g ≫ m' = m') {A : Over Ta} {B : Over Tb}
    (φ : (Over.pullback m).obj A ⟶ (Over.pullback m').obj B) :
    conjIter m m' g m m' hm hm' φ = φ := by
  refine hom_ext_fst ?_
  rw [conjIter_left_fst, bcProj_id m g hg hm A, Category.id_comp]

/-- Conjugating twice is conjugating once, along the composite. -/
lemma conjIter_conjIter (m : T₁ ⟶ Ta) (m' : T₁ ⟶ Tb) (g : T₂ ⟶ T₁) (g' : T₃ ⟶ T₂) (G : T₃ ⟶ T₁)
    (hG : g' ≫ g = G) (n : T₂ ⟶ Ta) (n' : T₂ ⟶ Tb) (hm : g ≫ m = n) (hm' : g ≫ m' = n')
    (N : T₃ ⟶ Ta) (N' : T₃ ⟶ Tb) (hN : G ≫ m = N) (hN' : G ≫ m' = N')
    (hn : g' ≫ n = N) (hn' : g' ≫ n' = N') {A : Over Ta} {B : Over Tb}
    (φ : (Over.pullback m).obj A ⟶ (Over.pullback m').obj B) :
    conjIter n n' g' N N' hn hn' (conjIter m m' g n n' hm hm' φ) =
      conjIter m m' G N N' hN hN' φ := by
  refine hom_ext_fst ?_
  rw [conjIter_left_fst, conjIter_left_fst, conjIter_left_fst,
    bcProj_comp m g g' G hG n hm N hN hn A, Category.assoc]

/-- A morphism of iterated base changes, read as a morphism of the base changes along the
composite. -/
noncomputable def reIter (m : T₁ ⟶ Ta) (m' : T₁ ⟶ Tb) (g : T₂ ⟶ T₁) (n : T₂ ⟶ Ta)
    (n' : T₂ ⟶ Tb) (hm : g ≫ m = n) (hm' : g ≫ m' = n') {A : Over Ta} {B : Over Tb}
    (ψ : (Over.pullback g).obj ((Over.pullback m).obj A) ⟶
      (Over.pullback g).obj ((Over.pullback m').obj B)) :
    (Over.pullback n).obj A ⟶ (Over.pullback n').obj B :=
  (iterPullbackIso m g n hm A).inv ≫ ψ ≫ (iterPullbackIso m' g n' hm' B).hom

/-- The conjugate of `φ` is the morphism of base changes along the composite which is read off from
the base change of `φ` along `g`. -/
lemma conjIter_eq_reIter (m : T₁ ⟶ Ta) (m' : T₁ ⟶ Tb) (g : T₂ ⟶ T₁) (n : T₂ ⟶ Ta)
    (n' : T₂ ⟶ Tb) (hm : g ≫ m = n) (hm' : g ≫ m' = n') {A : Over Ta} {B : Over Tb}
    (φ : (Over.pullback m).obj A ⟶ (Over.pullback m').obj B) :
    conjIter m m' g n n' hm hm' φ =
      reIter m m' g n n' hm hm' ((Over.pullback g).map φ) := rfl

/-- The coherence of the canonical identifications: identifying a triply iterated base change
with the base change along the composite does not depend on the order in which the two
identifications are made. -/
lemma iterPullbackIso_pentagon (m : T₁ ⟶ Ta) (t : T₂ ⟶ T₁) (n : T₂ ⟶ Ta) (hn : t ≫ m = n)
    (p : T₃ ⟶ T₂) (q : T₃ ⟶ T₁) (hq : p ≫ t = q) (r : T₃ ⟶ Ta) (hr : p ≫ n = r)
    (hqm : q ≫ m = r) (A : Over Ta) :
    (Over.pullback p).map (iterPullbackIso m t n hn A).hom ≫
        (iterPullbackIso n p r hr A).hom =
      (iterPullbackIso t p q hq ((Over.pullback m).obj A)).hom ≫
        (iterPullbackIso m q r hqm A).hom := by
  refine hom_ext_fst ?_
  simp [iterPullbackHom]

/-- A morphism of the base changes to a later stage whose own base change to a yet later stage is
identified with a given morphism there is, after the canonical identifications, that morphism. -/
lemma reIter_conj_eq (m : T₁ ⟶ Ta) (m' : T₁ ⟶ Tb) (t : T₂ ⟶ T₁) (n : T₂ ⟶ Ta) (n' : T₂ ⟶ Tb)
    (hn : t ≫ m = n) (hn' : t ≫ m' = n') (p : T₃ ⟶ T₂) (q : T₃ ⟶ T₁) (hq : p ≫ t = q)
    (r : T₃ ⟶ Ta) (r' : T₃ ⟶ Tb) (hr : p ≫ n = r) (hr' : p ≫ n' = r')
    (hqm : q ≫ m = r) (hqm' : q ≫ m' = r') {A : Over Ta} {B : Over Tb}
    (ψ : (Over.pullback t).obj ((Over.pullback m).obj A) ⟶
      (Over.pullback t).obj ((Over.pullback m').obj B))
    (φ : (Over.pullback q).obj ((Over.pullback m).obj A) ⟶
      (Over.pullback q).obj ((Over.pullback m').obj B))
    (h : (iterPullbackIso t p q hq ((Over.pullback m).obj A)).hom ≫ φ =
      (Over.pullback p).map ψ ≫ (iterPullbackIso t p q hq ((Over.pullback m').obj B)).hom) :
    conjIter n n' p r r' hr hr' (reIter m m' t n n' hn hn' ψ) =
      reIter m m' q r r' hqm hqm' φ := by
  have hA := iterPullbackIso_pentagon m t n hn p q hq r hr hqm A
  have hB := iterPullbackIso_pentagon m' t n' hn' p q hq r' hr' hqm' B
  rw [conjIter_eq_reIter, reIter, reIter, reIter, Functor.map_comp, Functor.map_comp,
    Iso.eq_inv_comp]
  have hR : (iterPullbackIso m q r hqm A).hom =
      (iterPullbackIso t p q hq ((Over.pullback m).obj A)).inv ≫
        (Over.pullback p).map (iterPullbackIso m t n hn A).hom ≫
          (iterPullbackIso n p r hr A).hom := by
    rw [hA, Iso.inv_hom_id_assoc]
  rw [hR]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp, hB, ← Category.assoc ((Over.pullback p).map ψ), ← h,
    Category.assoc, Iso.inv_hom_id_assoc]

omit [HasPullbacks C] in
/-- Conjugating a morphism by two isomorphisms and back. -/
lemma conj_inv_hom {X Y X' Y' : C} (α : X ≅ X') (β : Y ≅ Y') (u : X' ⟶ Y') :
    α.inv ≫ (α.hom ≫ u ≫ β.inv) ≫ β.hom = u := by
  simp

/-- The conjugation by the canonical identifications is injective: two morphisms of base changes
with the same conjugate have the same base change. -/
lemma pullback_map_eq_of_conjIter_eq (m : T₁ ⟶ Ta) (m' : T₁ ⟶ Tb) (g : T₂ ⟶ T₁) (n : T₂ ⟶ Ta)
    (n' : T₂ ⟶ Tb) (hm : g ≫ m = n) (hm' : g ≫ m' = n') {A : Over Ta} {B : Over Tb}
    (φ ψ : (Over.pullback m).obj A ⟶ (Over.pullback m').obj B)
    (h : conjIter m m' g n n' hm hm' φ = conjIter m m' g n n' hm hm' ψ) :
    (Over.pullback g).map φ = (Over.pullback g).map ψ := by
  have h' : (iterPullbackIso m g n hm A).inv ≫ (Over.pullback g).map φ ≫
      (iterPullbackIso m' g n' hm' B).hom =
      (iterPullbackIso m g n hm A).inv ≫ (Over.pullback g).map ψ ≫
      (iterPullbackIso m' g n' hm' B).hom := h
  exact (cancel_mono _).mp ((cancel_epi _).mp h')

end Proj

/-! ### The categories `C_T` -/

/-- The property of an object of `Over T` which cuts out the category `C_T`: the
scheme is quasi-compact and quasi-separated and its structure morphism is locally of finite
presentation. -/
def IsQcqsLfp (T : Scheme.{u}) : ObjectProperty (Over T) := fun X =>
  CompactSpace X.left ∧ QuasiSeparatedSpace X.left ∧ LocallyOfFinitePresentation X.hom

/-- The category `C_T`: the full subcategory of schemes `W` over `T` such that
`W` is quasi-compact and quasi-separated and such that `W ⟶ T` is locally of finite
presentation. -/
abbrev CatQcqsLfp (T : Scheme.{u}) := (IsQcqsLfp T).FullSubcategory

/-- The category `C_T` is stable under base change along an *affine* morphism:
quasi-compactness and quasi-separatedness of the scheme are inherited because the projection to
it is affine, and `LocallyOfFinitePresentation` is stable under base change.

It is not stable under arbitrary base change: the base change of `𝟙 T` along a morphism with
non-quasi-compact source has non-quasi-compact source. -/
lemma isQcqsLfp_pullback {T T' : Scheme.{u}} (f : T' ⟶ T) [IsAffineHom f] {X : Over T}
    (hX : IsQcqsLfp T X) : IsQcqsLfp T' ((Over.pullback f).obj X) := by
  obtain ⟨h₁, h₂, h₃⟩ := hX
  have := h₁
  have := h₂
  have hpb : IsPullback (pullback.fst X.hom f) (pullback.snd X.hom f) X.hom f :=
    IsPullback.of_hasPullback X.hom f
  have : IsAffineHom (pullback.fst X.hom f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip inferInstance
  exact ⟨QuasiCompact.compactSpace_of_compactSpace (pullback.fst X.hom f),
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst X.hom f),
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb h₃⟩

/-- The base change functor `C_T ⥤ C_{T'}` along an *affine* morphism `f : T' ⟶ T`. -/
noncomputable def pullbackCatQcqsLfp {T T' : Scheme.{u}} (f : T' ⟶ T) [IsAffineHom f] :
    CatQcqsLfp T ⥤ CatQcqsLfp T' :=
  ObjectProperty.lift _ ((IsQcqsLfp T).ι ⋙ Over.pullback f) fun X =>
    isQcqsLfp_pullback f X.property

/-- The object underlying the base change of `X` along `f` is `(Over.pullback f).obj X.obj`. -/
@[simp]
lemma pullbackCatQcqsLfp_obj_obj {T T' : Scheme.{u}} (f : T' ⟶ T) [IsAffineHom f]
    (X : CatQcqsLfp T) :
    ((pullbackCatQcqsLfp f).obj X).obj = (Over.pullback f).obj X.obj := rfl

/-- The morphism underlying the base change of `φ` along `f` is `(Over.pullback f).map φ.hom`. -/
@[simp]
lemma pullbackCatQcqsLfp_map_hom {T T' : Scheme.{u}} (f : T' ⟶ T) [IsAffineHom f]
    {X Y : CatQcqsLfp T} (φ : X ⟶ Y) :
    ((pullbackCatQcqsLfp f).map φ).hom = (Over.pullback f).map φ.hom := rfl

/-! ### The strict model of the diagram of stage categories -/

section Stages

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)]

/-- The transition morphism `S_j ⟶ S_k` of the inverse system, for `k ≤ j`. -/
abbrev stageMap {k j : I} (hkj : k ≤ j) : D.obj (op j) ⟶ D.obj (op k) := D.map (homOfLE hkj).op

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] in
/-- The transition morphisms of the inverse system compose: `S_l ⟶ S_k` is `S_l ⟶ S_j ⟶ S_k`. -/
lemma stageMap_comp {k j l : I} (hkj : k ≤ j) (hjl : j ≤ l) :
    stageMap D (hkj.trans hjl) = stageMap D hjl ≫ stageMap D hkj := by
  rw [← D.map_comp]
  rfl

/-- An object of the `j`-th category of the strict model of the diagram `i ↦ C_{Sᵢ}`: an object
of `C_{S_k}` for some stage `k ≤ j`, which represents its base change to `S_j`. -/
structure Stage (j : I) where
  /-- the stage over which the object lives -/
  src : I
  /-- the stage `src` lies below `j` -/
  le : src ≤ j
  /-- the object over `S_src` -/
  obj : Over (D.obj (op src))
  /-- the object is quasi-compact and quasi-separated and locally of finite presentation -/
  property : IsQcqsLfp (D.obj (op src)) obj

/-- The object of `C_{S_j}` that a stage object represents: its base change to `S_j`. -/
noncomputable def Stage.bc {j : I} (o : Stage D j) : Over (D.obj (op j)) :=
  (Over.pullback (stageMap D o.le)).obj o.obj

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The base change to `S_j` of a stage object lies in `C_{S_j}`. -/
lemma Stage.bc_property {j : I} (o : Stage D j) : IsQcqsLfp (D.obj (op j)) o.bc :=
  isQcqsLfp_pullback _ o.property

/-- The morphisms of the `j`-th stage category are the morphisms of the base changes to `S_j`. -/
noncomputable instance (j : I) : Category.{max v (u + 1)} (Stage D j) where
  Hom o o' := ULift.{max v (u + 1)} (o.bc ⟶ o'.bc)
  id o := ULift.up (𝟙 o.bc)
  comp f g := ULift.up (f.down ≫ g.down)
  id_comp _ := by simp
  comp_id _ := by simp
  assoc _ _ _ := by simp

/-- A morphism of the base changes to `S_j` as a morphism of the `j`-th stage category. -/
def Stage.homMk {j : I} {o o' : Stage D j} (f : o.bc ⟶ o'.bc) : o ⟶ o' := ULift.up f

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] in
/-- Two morphisms of a stage category are equal when their underlying morphisms of base changes
are. -/
@[ext]
lemma Stage.hom_ext {j : I} {o o' : Stage D j} {f g : o ⟶ o'} (h : f.down = g.down) : f = g :=
  ULift.ext h

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] in
/-- The underlying morphism of `AlgebraicGeometry.LimitDescent.Stage.homMk f` is `f`. -/
@[simp]
lemma Stage.homMk_down {j : I} {o o' : Stage D j} (f : o.bc ⟶ o'.bc) :
    (Stage.homMk D f).down = f := rfl

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] in
/-- The underlying morphism of the identity of a stage object is the identity of its base
change. -/
@[simp]
lemma Stage.id_down {j : I} (o : Stage D j) : (𝟙 o : o ⟶ o).down = 𝟙 o.bc := rfl

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] in
/-- The underlying morphism of a composite in a stage category is the composite of the underlying
morphisms. -/
@[simp]
lemma Stage.comp_down {j : I} {o o' o'' : Stage D j} (f : o ⟶ o') (g : o' ⟶ o'') :
    (f ≫ g).down = f.down ≫ g.down := rfl

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] in
/-- The transition morphism `S_j ⟶ S_j` is the identity. -/
lemma stageMap_refl (j : I) : stageMap D (le_refl j) = 𝟙 (D.obj (op j)) := D.map_id _

/-- Base change along the identity, as an isomorphism of objects over the base. -/
noncomputable def pullbackIdIso {T : Scheme.{u}} (g : T ⟶ T) (hg : g = 𝟙 T) (Z : Over T) :
    (Over.pullback g).obj Z ≅ Z where
  hom := Over.homMk (pullback.fst Z.hom g) (by simp [pullback.condition, hg])
  inv := Over.homMk (pullback.lift (𝟙 Z.left) Z.hom (by simp [hg])) (by simp)
  hom_inv_id := Over.OverMorphism.ext (by
    refine pullback.hom_ext ?_ ?_ <;> simp [pullback.condition, hg])
  inv_hom_id := Over.OverMorphism.ext (by simp)

/-- The functor from the `j`-th stage category of the strict model to `C_{S_j}`: an object of
the model is sent to the object of `C_{S_j}` it represents, namely its base change to `S_j`, and
a morphism to its underlying morphism of base changes. -/
noncomputable def Stage.toCatQcqsLfp (j : I) : Stage D j ⥤ CatQcqsLfp (D.obj (op j)) where
  obj o := ⟨o.bc, o.bc_property⟩
  map f := ObjectProperty.homMk f.down
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor `AlgebraicGeometry.LimitDescent.Stage.toCatQcqsLfp` is full. -/
instance (j : I) : (Stage.toCatQcqsLfp D j).Full where
  map_surjective f := ⟨Stage.homMk D f.hom, rfl⟩

/-- The functor `AlgebraicGeometry.LimitDescent.Stage.toCatQcqsLfp` is faithful. -/
instance (j : I) : (Stage.toCatQcqsLfp D j).Faithful where
  map_injective h := Stage.hom_ext D (congrArg (fun u => u.hom) h)

/-- The functor `AlgebraicGeometry.LimitDescent.Stage.toCatQcqsLfp` is essentially surjective. -/
instance (j : I) : (Stage.toCatQcqsLfp D j).EssSurj where
  mem_essImage X :=
    ⟨⟨j, le_refl j, X.obj, X.property⟩,
      ⟨ObjectProperty.isoMk _ (pullbackIdIso (stageMap D (le_refl j)) (stageMap_refl D j) X.obj)⟩⟩

/-- The functor `AlgebraicGeometry.LimitDescent.Stage.toCatQcqsLfp` is an equivalence of
categories. -/
instance (j : I) : (Stage.toCatQcqsLfp D j).IsEquivalence where

/-- The transition functor of the strict model: it leaves the object untouched and only moves its
stage up, the morphisms being transported by the canonical identifications. -/
noncomputable def Stage.up {j j' : I} (hjj' : j ≤ j') : Stage D j ⥤ Stage D j' where
  obj o := ⟨o.src, o.le.trans hjj', o.obj, o.property⟩
  map {o o'} f := Stage.homMk D (conjIter (stageMap D o.le) (stageMap D o'.le)
    (stageMap D hjj') (stageMap D (o.le.trans hjj')) (stageMap D (o'.le.trans hjj'))
    (stageMap_comp D o.le hjj').symm (stageMap_comp D o'.le hjj').symm f.down)
  map_id _ := Stage.hom_ext D (conjIter_id _ _ _ _ _)
  map_comp _ _ := Stage.hom_ext D (conjIter_comp _ _ _ _ _ _ _ _ _ _ _ _)

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] in
/-- The transition functor `AlgebraicGeometry.LimitDescent.Stage.up` keeps the object and its stage
and replaces `src ≤ j` by `src ≤ j'`. -/
@[simp]
lemma Stage.up_obj {j j' : I} (hjj' : j ≤ j') (o : Stage D j) :
    (Stage.up D hjj').obj o = ⟨o.src, o.le.trans hjj', o.obj, o.property⟩ := rfl

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] in
/-- The underlying morphism of the image of `f` under `AlgebraicGeometry.LimitDescent.Stage.up` is
the conjugate of the underlying morphism of `f`. -/
@[simp]
lemma Stage.up_map_down {j j' : I} (hjj' : j ≤ j') {o o' : Stage D j} (f : o ⟶ o') :
    ((Stage.up D hjj').map f).down = conjIter (stageMap D o.le) (stageMap D o'.le)
      (stageMap D hjj') (stageMap D (o.le.trans hjj')) (stageMap D (o'.le.trans hjj'))
      (stageMap_comp D o.le hjj').symm (stageMap_comp D o'.le hjj').symm f.down := rfl

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] in
/-- The transition functor along `j ≤ j` is the identity on objects. -/
lemma Stage.up_obj_refl {j : I} (o : Stage D j) : (Stage.up D (le_refl j)).obj o = o := rfl

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] in
/-- The transition functors compose on objects. -/
lemma Stage.up_obj_trans {j j' j'' : I} (hjj' : j ≤ j') (hj'j'' : j' ≤ j'') (o : Stage D j) :
    (Stage.up D (hjj'.trans hj'j'')).obj o =
      (Stage.up D hjj' ⋙ Stage.up D hj'j'').obj o := rfl

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] in
/-- The transition functor along `j ≤ j` is the identity functor. -/
lemma Stage.up_refl (j : I) : Stage.up D (le_refl j) = 𝟭 (Stage D j) := by
  refine CategoryTheory.Functor.ext (fun o => Stage.up_obj_refl D o) fun o o' f => ?_
  change (Stage.up D (le_refl j)).map f = 𝟙 _ ≫ f ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  exact Stage.hom_ext D (conjIter_of_id _ _ _ (stageMap_refl D j) _ _ _)

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] in
/-- The transition functor along `j ≤ j''` is the composite of the transition functors along
`j ≤ j'` and `j' ≤ j''`. -/
lemma Stage.up_trans {j j' j'' : I} (hjj' : j ≤ j') (hj'j'' : j' ≤ j'') :
    Stage.up D (hjj'.trans hj'j'') = Stage.up D hjj' ⋙ Stage.up D hj'j'' := by
  refine CategoryTheory.Functor.ext (fun o => Stage.up_obj_trans D hjj' hj'j'' o) fun o o' f => ?_
  change (Stage.up D (hjj'.trans hj'j'')).map f =
    𝟙 _ ≫ (Stage.up D hjj' ⋙ Stage.up D hj'j'').map f ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  refine Stage.hom_ext D ?_
  rw [Stage.up_map_down, Functor.comp_map, Stage.up_map_down, Stage.up_map_down]
  exact (conjIter_conjIter _ _ _ _ _ (stageMap_comp D hjj' hj'j'').symm _ _ _ _ _ _ _ _ _ _
    f.down).symm

/-- The transition functors of the strict model are the base change functors: under the
identification `AlgebraicGeometry.LimitDescent.Stage.toCatQcqsLfp` of the `j`-th stage of the
strict model with `C_{S_j}`, the transition functor `AlgebraicGeometry.LimitDescent.Stage.up` is
base change along the transition morphism `S_{j'} ⟶ S_j`, the identification being the canonical
one of an iterated base change with a base change. -/
noncomputable def Stage.upPullbackIso {j j' : I} (hjj' : j ≤ j') :
    Stage.toCatQcqsLfp D j ⋙ pullbackCatQcqsLfp (stageMap D hjj') ≅
      Stage.up D hjj' ⋙ Stage.toCatQcqsLfp D j' :=
  NatIso.ofComponents
    (fun o => ObjectProperty.isoMk _ (iterPullbackIso (stageMap D o.le) (stageMap D hjj')
      (stageMap D (o.le.trans hjj')) (stageMap_comp D o.le hjj').symm o.obj))
    fun {o o'} f => ObjectProperty.hom_ext _
      (pullback_map_comp_iterPullbackIso (stageMap D o.le) (stageMap D o'.le)
        (stageMap D hjj') (stageMap D (o.le.trans hjj')) (stageMap D (o'.le.trans hjj'))
        (stageMap_comp D o.le hjj').symm (stageMap_comp D o'.le hjj').symm f.down)

/-- The strict model of the diagram `i ↦ C_{Sᵢ}` of stage categories, as a functor into
`CategoryTheory.Cat`. -/
noncomputable def stageDiagram : I ⥤ Cat.{max v (u + 1), max v (u + 1)} where
  obj j := Cat.of (Stage D j)
  map h := (Stage.up D (leOfHom h)).toCatHom
  map_id j := Cat.ext (Stage.up_refl D j)
  map_comp h h' := Cat.ext (Stage.up_trans D (leOfHom h) (leOfHom h'))

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] in
/-- The `j`-th category of `AlgebraicGeometry.LimitDescent.stageDiagram` is `Stage D j`. -/
@[simp]
lemma stageDiagram_obj (j : I) : (stageDiagram D).obj j = Cat.of (Stage D j) := rfl

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] in
/-- The transition functors of `AlgebraicGeometry.LimitDescent.stageDiagram` are
`AlgebraicGeometry.LimitDescent.Stage.up`. -/
@[simp]
lemma stageDiagram_map_toFunctor {j j' : I} (h : j ⟶ j') :
    ((stageDiagram D).map h).toFunctor = Stage.up D (leOfHom h) := rfl

end Stages

/-- The colimit insertions of two categories of a diagram in `Cat` agree on an object and its image
under a transition functor. -/
private lemma colimit_ι_obj_map {J : Type*} [Category J] (F : J ⥤ Cat) [HasColimit F]
    {j j' : J} (h : j ⟶ j') (G : F.obj j ⥤ F.obj j') (hG : (F.map h).toFunctor = G)
    (o : F.obj j) :
    (colimit.ι F j').toFunctor.obj (G.obj o) = (colimit.ι F j).toFunctor.obj o := by
  subst hG
  exact Functor.congr_obj (congrArg Cat.Hom.toFunctor (colimit.w F h)) o

/-- The colimit insertions of two categories of a diagram in `Cat` agree on a morphism and its image
under a transition functor, up to the identifications of `colimit_ι_obj_map`. -/
private lemma colimit_ι_map_map {J : Type*} [Category J] (F : J ⥤ Cat) [HasColimit F]
    {j j' : J} (h : j ⟶ j') (G : F.obj j ⥤ F.obj j') (hG : (F.map h).toFunctor = G)
    {o o' : F.obj j} (p : o ⟶ o') :
    (colimit.ι F j').toFunctor.map (G.map p) =
      eqToHom (colimit_ι_obj_map F h G hG o) ≫ (colimit.ι F j).toFunctor.map p ≫
        eqToHom (colimit_ι_obj_map F h G hG o').symm := by
  subst hG
  exact Functor.congr_hom (congrArg Cat.Hom.toFunctor (colimit.w F h)) p

/-! ### The comparison functor `colim C_{Sᵢ} ⥤ C_S` -/

section Comparison

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [FinallySmall.{u} I]
  (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)]
  (c : Cone D) (hc : IsLimit c)

include hc in
/-- The legs of a limit cone of an inverse system with affine transition morphisms, indexed by a
finally `u`-small directed category, are affine. -/
lemma isAffineHom_π (i : I) : IsAffineHom (c.π.app (op i)) :=
  isAffineHom_π_app_of_initiallySmall D c hc (op i)

include hc in
/-- The category `C_T` is stable under base change along a leg of the limit cone. -/
lemma isQcqsLfp_pullback_π (i : I) {X : Over (D.obj (op i))}
    (hX : IsQcqsLfp (D.obj (op i)) X) :
    IsQcqsLfp c.pt ((Over.pullback (c.π.app (op i))).obj X) :=
  have := isAffineHom_π D c hc i
  isQcqsLfp_pullback _ hX

/-- The base change to the limit, as a functor from the `j`-th stage category of the strict
model: an object living over the stage `S_k` is based changed along the leg `S ⟶ S_k`. -/
noncomputable def toLimit (j : I) : Stage D j ⥤ CatQcqsLfp c.pt where
  obj o := ⟨(Over.pullback (c.π.app (op o.src))).obj o.obj,
    isQcqsLfp_pullback_π D c hc o.src o.property⟩
  map {o o'} f := ObjectProperty.homMk (conjIter (stageMap D o.le) (stageMap D o'.le)
    (c.π.app (op j)) (c.π.app (op o.src)) (c.π.app (op o'.src))
    (c.w (homOfLE o.le).op) (c.w (homOfLE o'.le).op) f.down)
  map_id _ := ObjectProperty.hom_ext _ (conjIter_id _ _ _ _ _)
  map_comp _ _ := ObjectProperty.hom_ext _ (conjIter_comp _ _ _ _ _ _ _ _ _ _ _ _)

/-- The image of a stage object under `AlgebraicGeometry.LimitDescent.toLimit` is its base change
along the leg `S ⟶ S_src` of the limit cone. -/
@[simp]
lemma toLimit_obj_obj (j : I) (o : Stage D j) :
    ((toLimit D c hc j).obj o).obj = (Over.pullback (c.π.app (op o.src))).obj o.obj := rfl

/-- The underlying morphism of the image of `f` under `AlgebraicGeometry.LimitDescent.toLimit` is
the conjugate of the underlying morphism of `f` along the leg `S ⟶ S_j`. -/
@[simp]
lemma toLimit_map_hom (j : I) {o o' : Stage D j} (f : o ⟶ o') :
    ((toLimit D c hc j).map f).hom = conjIter (stageMap D o.le) (stageMap D o'.le)
      (c.π.app (op j)) (c.π.app (op o.src)) (c.π.app (op o'.src))
      (c.w (homOfLE o.le).op) (c.w (homOfLE o'.le).op) f.down := rfl

/-- Base changing to a later stage and then to the limit agrees on objects with base changing to
the limit. -/
lemma toLimit_up_obj {j j' : I} (hjj' : j ≤ j') (o : Stage D j) :
    (Stage.up D hjj' ⋙ toLimit D c hc j').obj o = (toLimit D c hc j).obj o := rfl

/-- The base change functors to the limit form a cocone: base changing to a later stage and then
to the limit is base changing to the limit. -/
lemma toLimit_up {j j' : I} (hjj' : j ≤ j') :
    Stage.up D hjj' ⋙ toLimit D c hc j' = toLimit D c hc j := by
  refine CategoryTheory.Functor.ext (fun o => toLimit_up_obj D c hc hjj' o) fun o o' f => ?_
  change (Stage.up D hjj' ⋙ toLimit D c hc j').map f = 𝟙 _ ≫ (toLimit D c hc j).map f ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  refine ObjectProperty.hom_ext _ ?_
  rw [Functor.comp_map, toLimit_map_hom, toLimit_map_hom, Stage.up_map_down]
  exact conjIter_conjIter _ _ _ _ _ (c.w (homOfLE hjj').op) _ _ _ _ _ _ _ _ _ _ f.down

/-- The diagram `AlgebraicGeometry.LimitDescent.stageDiagram` has a colimit. -/
instance : HasColimit (stageDiagram D) := by
  let : HasColimitsOfSize.{v, v} Cat.{max v (u + 1), max v (u + 1)} :=
    hasColimitsOfSizeOfUnivLE.{max v (u + 1), max v (u + 1), v, v} Cat
  infer_instance

/-- The diagram of nerves of the stage categories has a colimit. -/
instance : HasColimit (stageDiagram D ⋙
    CategoryTheory.nerveFunctor.{max v (u + 1), max v (u + 1)}) := by
  have : HasColimitsOfSize.{v, v} SSet.{max v (u + 1)} :=
    hasColimitsOfSizeOfUnivLE.{max v (u + 1), max v (u + 1), v, v} _
  infer_instance

/-- The cocone of base change functors to the limit. -/
noncomputable def limitCocone : Cocone (stageDiagram D) where
  pt := Cat.of (AsSmall.{max v (u + 1)} (CatQcqsLfp c.pt))
  ι :=
    { app := fun j => (toLimit D c hc j ⋙ AsSmall.up).toCatHom
      naturality := fun j j' h => Cat.ext (by
        change Stage.up D (leOfHom h) ⋙ toLimit D c hc j' ⋙ AsSmall.up =
          (toLimit D c hc j ⋙ AsSmall.up) ⋙ 𝟭 _
        rw [Functor.comp_id, ← Functor.assoc, toLimit_up D c hc (leOfHom h)]) }

/-- The canonical functor `colim C_{Sᵢ} ⥤ C_S`: the colimit descent of the base change functors
to the limit. -/
noncomputable def baseChangeComparison :
    (colimit (stageDiagram D) : Cat.{max v (u + 1), max v (u + 1)}) ⥤ CatQcqsLfp c.pt :=
  (colimit.desc (stageDiagram D) (limitCocone D c hc)).toFunctor ⋙ AsSmall.down

/-- On each stage the canonical functor `colim C_{Sᵢ} ⥤ C_S` is the base change to the limit. -/
lemma baseChangeComparison_ι (j : I) :
    (colimit.ι (stageDiagram D) j).toFunctor ⋙ baseChangeComparison D c hc =
      toLimit D c hc j := by
  have h : (colimit.ι (stageDiagram D) j).toFunctor ⋙
      (colimit.desc (stageDiagram D) (limitCocone D c hc)).toFunctor =
      toLimit D c hc j ⋙ AsSmall.up :=
    congrArg Cat.Hom.toFunctor (colimit.ι_desc (limitCocone D c hc) j)
  have h' : (colimit.ι (stageDiagram D) j).toFunctor ⋙ baseChangeComparison D c hc =
      ((colimit.ι (stageDiagram D) j).toFunctor ⋙
        (colimit.desc (stageDiagram D) (limitCocone D c hc)).toFunctor) ⋙ AsSmall.down := rfl
  rw [h', h]
  rfl

/-! ### The comparison functor is an equivalence -/

/-- A morphism conjugated by a chain of identifications of its source and of its target which
starts and ends at the same object is itself. -/
lemma eqToHom_conj_six {E : Type*} [Category E] {P₁ P₂ P₃ Q₁ Q₂ Q₃ : E} (a : P₁ = P₂)
    (p : P₂ = P₃) (b : P₃ = P₁) (e : Q₁ = Q₂) (q : Q₂ = Q₃) (g : Q₃ = Q₁) (u : P₁ ⟶ Q₁) :
    eqToHom a ≫ ((eqToHom p ≫ ((eqToHom b ≫ (u ≫ eqToHom e)) ≫ eqToHom q)) ≫ eqToHom g) = u := by
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Category.comp_id]

include hc in
/-- The canonical functor `colim C_{Sᵢ} ⥤ C_S` is essentially surjective. -/
lemma essSurj_baseChangeComparison : (baseChangeComparison D c hc).EssSurj := by
  refine ⟨fun Z => ?_⟩
  obtain ⟨i, Xᵢ, h₁, h₂, h₃, ⟨e⟩⟩ := exists_model_of_locallyOfFinitePresentation D c hc Z.obj
    Z.property.1 Z.property.2.1 Z.property.2.2
  refine ⟨(colimit.ι (stageDiagram D) i).toFunctor.obj ⟨i, le_refl i, Xᵢ, ⟨h₁, h₂, h₃⟩⟩, ⟨?_⟩⟩
  refine eqToIso (Functor.congr_obj (baseChangeComparison_ι D c hc i)
    (⟨i, le_refl i, Xᵢ, ⟨h₁, h₂, h₃⟩⟩ : Stage D i)) ≪≫ ?_
  exact ObjectProperty.isoMk _ e.symm

include hc in
/-- A morphism between the images in `C_S` of two objects of the `j`-th
stage category is, after passing to a later stage, the image of a morphism of that stage
category. -/
lemma exists_stage_hom_of_hom (j : I) (a b : Stage D j)
    (f : (toLimit D c hc j).obj a ⟶ (toLimit D c hc j).obj b) :
    ∃ (j₂ : I) (hjj₂ : j ≤ j₂) (G : (Stage.up D hjj₂).obj a ⟶ (Stage.up D hjj₂).obj b),
      (toLimit D c hc j₂).map G = f := by
  have hwa : c.π.app (op j) ≫ stageMap D a.le = c.π.app (op a.src) := c.w (homOfLE a.le).op
  have hwb : c.π.app (op j) ≫ stageMap D b.le = c.π.app (op b.src) := c.w (homOfLE b.le).op
  obtain ⟨j₂, hjj₂, g, α, β, hα, hβ, heq⟩ :=
    exists_morphism_after_baseChange_of_finallySmall D c hc j a.bc b.bc
      a.bc_property.1 a.bc_property.2.1 b.bc_property.1 b.bc_property.2.1
      a.bc_property.2.2 b.bc_property.2.2
      ((iterPullbackIso (stageMap D a.le) (c.π.app (op j)) (c.π.app (op a.src)) hwa a.obj).hom ≫
        f.hom ≫
        (iterPullbackIso (stageMap D b.le) (c.π.app (op j)) (c.π.app (op b.src)) hwb b.obj).inv)
  rw [eq_iterPullbackIso_hom (stageMap D hjj₂) (c.π.app (op j₂)) (c.π.app (op j))
      (c.w (homOfLE hjj₂).op) a.bc α.hom hα,
    eq_iterPullbackIso_hom (stageMap D hjj₂) (c.π.app (op j₂)) (c.π.app (op j))
      (c.w (homOfLE hjj₂).op) b.bc β.hom hβ] at heq
  refine ⟨j₂, hjj₂, Stage.homMk D (reIter (stageMap D a.le) (stageMap D b.le)
    (stageMap D hjj₂) (stageMap D (a.le.trans hjj₂)) (stageMap D (b.le.trans hjj₂))
    (stageMap_comp D a.le hjj₂).symm (stageMap_comp D b.le hjj₂).symm (A := a.obj) (B := b.obj)
    g), ObjectProperty.hom_ext _ ?_⟩
  refine (reIter_conj_eq (stageMap D a.le) (stageMap D b.le) (stageMap D hjj₂)
    (stageMap D (a.le.trans hjj₂)) (stageMap D (b.le.trans hjj₂))
    (stageMap_comp D a.le hjj₂).symm (stageMap_comp D b.le hjj₂).symm (c.π.app (op j₂))
    (c.π.app (op j)) (c.w (homOfLE hjj₂).op) (c.π.app (op a.src)) (c.π.app (op b.src))
    (c.w (homOfLE (a.le.trans hjj₂)).op) (c.w (homOfLE (b.le.trans hjj₂)).op) hwa hwb g _
    heq).trans ?_
  exact conj_inv_hom _ _ _

include hc in
/-- The canonical functor `colim C_{Sᵢ} ⥤ C_S` is full. -/
lemma full_baseChangeComparison : (baseChangeComparison D c hc).Full := by
  refine ⟨fun {x y} f => ?_⟩
  obtain ⟨j, a₀, b₀, hxa, hyb⟩ := Cat.exists_common_stage_obj_of_colimit (stageDiagram D) x y
  obtain ⟨a, rfl⟩ : ∃ a : Stage D j, a = a₀ := ⟨a₀, rfl⟩
  obtain ⟨b, rfl⟩ : ∃ b : Stage D j, b = b₀ := ⟨b₀, rfl⟩
  subst hxa hyb
  have ea : (baseChangeComparison D c hc).obj
      ((colimit.ι (stageDiagram D) j).toFunctor.obj a) = (toLimit D c hc j).obj a :=
    Functor.congr_obj (baseChangeComparison_ι D c hc j) a
  have eb : (baseChangeComparison D c hc).obj
      ((colimit.ι (stageDiagram D) j).toFunctor.obj b) = (toLimit D c hc j).obj b :=
    Functor.congr_obj (baseChangeComparison_ι D c hc j) b
  obtain ⟨j₂, hjj₂, G, hG⟩ := exists_stage_hom_of_hom D c hc j a b
    (eqToHom ea.symm ≫ f ≫ eqToHom eb)
  have hw : ∀ o : Stage D j, (colimit.ι (stageDiagram D) j₂).toFunctor.obj
      ((Stage.up D hjj₂).obj o) = (colimit.ι (stageDiagram D) j).toFunctor.obj o := fun o =>
    colimit_ι_obj_map (stageDiagram D) (homOfLE hjj₂) (Stage.up D hjj₂) rfl o
  refine ⟨eqToHom (hw a).symm ≫ (colimit.ι (stageDiagram D) j₂).toFunctor.map G ≫
    eqToHom (hw b), ?_⟩
  have hKG : (baseChangeComparison D c hc).map
      ((colimit.ι (stageDiagram D) j₂).toFunctor.map G) =
      eqToHom (Functor.congr_obj (baseChangeComparison_ι D c hc j₂)
          ((Stage.up D hjj₂).obj a)) ≫
        (toLimit D c hc j₂).map G ≫
        eqToHom (Functor.congr_obj (baseChangeComparison_ι D c hc j₂)
          ((Stage.up D hjj₂).obj b)).symm :=
    Functor.congr_hom (baseChangeComparison_ι D c hc j₂) G
  have h₁ : (baseChangeComparison D c hc).map (eqToHom (hw a).symm ≫
        (colimit.ι (stageDiagram D) j₂).toFunctor.map G ≫ eqToHom (hw b)) =
      eqToHom (congrArg (baseChangeComparison D c hc).obj (hw a).symm) ≫
        (baseChangeComparison D c hc).map
          ((colimit.ι (stageDiagram D) j₂).toFunctor.map G) ≫
        eqToHom (congrArg (baseChangeComparison D c hc).obj (hw b)) := by
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  rw [h₁, hKG, hG]
  exact eqToHom_conj_six _ _ _ _ _ _ f

include hc in
/-- Two morphisms of one stage category with the same base change to the limit have the same base
change to that stage. -/
lemma pullback_map_eq_of_toLimit_map_eq (j : I) {o o' : Stage D j} (p q : o ⟶ o')
    (h : (toLimit D c hc j).map p = (toLimit D c hc j).map q) :
    (Over.pullback (c.π.app (op j))).map p.down =
      (Over.pullback (c.π.app (op j))).map q.down :=
  pullback_map_eq_of_conjIter_eq (stageMap D o.le) (stageMap D o'.le) (c.π.app (op j))
    (c.π.app (op o.src)) (c.π.app (op o'.src)) (c.w (homOfLE o.le).op)
    (c.w (homOfLE o'.le).op) p.down q.down (congrArg (fun u => u.hom) h)

omit [Nonempty I] [IsDirected I (· ≤ ·)] [FinallySmall.{u} I]
  [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] in
/-- Two morphisms of one stage category whose base changes to a later stage agree have the same
image under the transition functor to that stage. -/
lemma up_map_eq_of_pullback_map_eq {j j₂ : I} (hjj₂ : j ≤ j₂) {o o' : Stage D j} (p q : o ⟶ o')
    (h : (Over.pullback (stageMap D hjj₂)).map p.down =
      (Over.pullback (stageMap D hjj₂)).map q.down) :
    (Stage.up D hjj₂).map p = (Stage.up D hjj₂).map q :=
  Stage.hom_ext D (congrArg (fun ψ => reIter (stageMap D o.le) (stageMap D o'.le)
    (stageMap D hjj₂) (stageMap D (o.le.trans hjj₂)) (stageMap D (o'.le.trans hjj₂))
    (stageMap_comp D o.le hjj₂).symm (stageMap_comp D o'.le hjj₂).symm
    (A := o.obj) (B := o'.obj) ψ) h)

omit [FinallySmall.{u} I] [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] in
/-- Two morphisms of one stage category which agree after a transition agree in the colimit. -/
lemma colimit_ι_map_eq_of_up_map_eq {j j₂ : I} (hjj₂ : j ≤ j₂) {o o' : Stage D j} (p q : o ⟶ o')
    (h : (Stage.up D hjj₂).map p = (Stage.up D hjj₂).map q) :
    (colimit.ι (stageDiagram D) j).toFunctor.map p =
      (colimit.ι (stageDiagram D) j).toFunctor.map q := by
  have hp := colimit_ι_map_map (stageDiagram D) (homOfLE hjj₂) (Stage.up D hjj₂) rfl p
  rw [h, colimit_ι_map_map (stageDiagram D) (homOfLE hjj₂) (Stage.up D hjj₂) rfl q] at hp
  exact ((cancel_mono _).mp ((cancel_epi _).mp hp)).symm

include hc in
/-- The canonical functor `colim C_{Sᵢ} ⥤ C_S` is faithful. -/
lemma faithful_baseChangeComparison : (baseChangeComparison D c hc).Faithful := by
  refine ⟨fun {x y f g} hfg => ?_⟩
  obtain ⟨j, a₀, b₀, f₀, g₀, hxa, hyb, hf', hg'⟩ :=
    Cat.exists_stage_hom_pair_of_colimit (stageDiagram D) f g
  obtain ⟨a, rfl⟩ : ∃ a : Stage D j, a = a₀ := ⟨a₀, rfl⟩
  obtain ⟨b, rfl⟩ : ∃ b : Stage D j, b = b₀ := ⟨b₀, rfl⟩
  obtain ⟨f', rfl⟩ : ∃ p : a ⟶ b, p = f₀ := ⟨f₀, rfl⟩
  obtain ⟨g', rfl⟩ : ∃ p : a ⟶ b, p = g₀ := ⟨g₀, rfl⟩
  have hcomp : ((colimit.ι (stageDiagram D) j).toFunctor ⋙
        baseChangeComparison D c hc).map f' =
      ((colimit.ι (stageDiagram D) j).toFunctor ⋙ baseChangeComparison D c hc).map g' := by
    change (baseChangeComparison D c hc).map ((colimit.ι (stageDiagram D) j).toFunctor.map f') =
      (baseChangeComparison D c hc).map ((colimit.ι (stageDiagram D) j).toFunctor.map g')
    rw [hf', hg', Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp, hfg]
  rw [baseChangeComparison_ι D c hc j] at hcomp
  obtain ⟨j₂, hjj₂, hres⟩ := eventually_eq_of_baseChange_eq_of_finallySmall D c hc j a.bc b.bc
    a.bc_property.1 a.bc_property.2.1 b.bc_property.1 b.bc_property.2.1
    a.bc_property.2.2 b.bc_property.2.2 f'.down g'.down
    (pullback_map_eq_of_toLimit_map_eq D c hc j f' g' hcomp)
  have hι := colimit_ι_map_eq_of_up_map_eq D hjj₂ f' g'
    (up_map_eq_of_pullback_map_eq D hjj₂ f' g' hres)
  rw [hf', hg'] at hι
  exact (cancel_mono (eqToHom hyb.symm)).mp ((cancel_epi (eqToHom hxa)).mp hι)

/-- For a scheme `T` let `C_T` be the full subcategory of schemes `W` over `T` such that `W` is
quasi-compact and quasi-separated and such that the structure morphism `W ⟶ T` is locally of
finite presentation. Let `S = lim Sᵢ` be a directed inverse limit of schemes with affine
transition morphisms, indexed by a finally `u`-small `I`, with no finiteness hypothesis on the
stages `Sᵢ`. Then the base change functors induce an equivalence of categories
`colim C_{Sᵢ} ⥤ C_S`.

The colimit is the colimit in `CategoryTheory.Cat` of the strict model
`AlgebraicGeometry.LimitDescent.stageDiagram` of the diagram `i ↦ C_{Sᵢ}`, and the functor is
`AlgebraicGeometry.LimitDescent.baseChangeComparison`, the colimit descent of the base change
functors `C_{Sᵢ} ⥤ C_S`. -/
@[stacks 0EY1,
  ega "IV 8.1.1" "more general",
  ega "IV 8.8.3" "more general",
  sga "3 VIB 10.0" "more general",
  sga "4 VII 5.2" "more general",
  sga "4 VII 5.3" "more general"]
public theorem isEquivalence_baseChangeComparison :
    (baseChangeComparison D c hc).IsEquivalence := by
  have := essSurj_baseChangeComparison D c hc
  have := full_baseChangeComparison D c hc
  have := faithful_baseChangeComparison D c hc
  exact { }

end Comparison

section DirectedSet

attribute [local instance] finallySmall_of_essentiallySmall

/-- Let `S = lim Sᵢ` be the limit of an inverse system of schemes indexed by a directed set `I`
in the universe of the schemes, with affine transition morphisms. Then the base change functors
induce an equivalence of categories `colim C_{Sᵢ} ⥤ C_S`, where `C_T` is the category of
quasi-compact, quasi-separated schemes locally of finite presentation over `T`. -/
@[stacks 0EY1,
  ega "IV 8.8.3" "more general",
  sga "3 VIB 10.0" "more general",
  sga "4 VII 5.3" "more general"]
public theorem isEquivalence_baseChangeComparison_of_directedSet
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) :
    (baseChangeComparison D c hc).IsEquivalence :=
  isEquivalence_baseChangeComparison D c hc

end DirectedSet

end AlgebraicGeometry.LimitDescent

end
