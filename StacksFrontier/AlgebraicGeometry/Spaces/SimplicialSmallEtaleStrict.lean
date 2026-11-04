module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleMorphism

/-!
# Strict components of the spaces-étale site of a simplicial algebraic space

Let `X` be a simplicial algebraic space. The degree-`n` component of `X_{spaces,étale}` is the
spaces-étale site of `X_n`, and a simplex map `φ : [m] ⟶ [n]` acts on components by base change
along `X(φ) : X_n ⟶ X_m`, which is functorial in `φ` only up to the canonical isomorphisms of
iterated fibre products. The components are replaced here by equivalent categories on which
base change acts strictly on objects, so that they form a strict cosimplicial diagram.

An object of the strict degree-`n` component is a triple `(k, V/X_k, ψ : [k] ⟶ [n])`, standing
for the base change of `V` along `X(ψ) : X_n ⟶ X_k`; morphisms are the morphisms of these base
changes in `(X_n)_{spaces,étale}`. Realization is fully faithful by construction and essentially
surjective, `V/X_n` being realized by `(n, V, 𝟙)`, so it is an equivalence with
`(X_n)_{spaces,étale}`.

## Main definitions

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.StrictObj`: the triples `(k, V, ψ)`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.StrictComponent`: the strict degree-`n`
  component, with `strictRealize`, the realization in `(X_n)_{spaces,étale}`, an equivalence.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictTransition`: the transition functor
  `u_φ`, realizing to base change along `X(φ)` (`strictTransitionRealizeIso`).
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictCosimplicial`: the cosimplicial
  diagram of strict components; `strictTransition_id` and `strictTransition_comp` say that the
  transition functors compose on the nose.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : SimplicialObject (AlgebraicSpaces B S hS))

/-- An object of the strict degree-`n` component of `X_{spaces,étale}`: a simplicial degree `k`,
an algebraic space `V` étale over `X_k` and a simplex map `ψ : [k] ⟶ [n]`. It stands for the
base change of `V` along `X(ψ) : X_n ⟶ X_k`. -/
structure StrictObj (n : SimplexCategory) where
  /-- The simplicial degree `k` of the algebraic space étale over `X_k`. -/
  degree : SimplexCategory
  /-- The algebraic space `V` étale over `X_k`. -/
  obj : SpacesEtale B S hS (X.obj (op degree))
  /-- The simplex map `ψ : [k] ⟶ [n]` along whose image `V` is base changed, as a monotone map
  of vertices, so that composing with identities and associativity hold on the nose. -/
  map : Fin (degree.len + 1) →o Fin (n.len + 1)

variable {X}

/-- The simplex map `ψ : [k] ⟶ [n]` of a triple `(k, V, ψ)`. -/
abbrev StrictObj.simplex {n : SimplexCategory} (x : StrictObj X n) : x.degree ⟶ n :=
  SimplexCategory.Hom.mk x.map

/-- The realization of `(k, V, ψ)` in `(X_n)_{spaces,étale}`: the base change of `V` along
`X(ψ)`. -/
abbrev StrictObj.realize {n : SimplexCategory} (x : StrictObj X n) :
    SpacesEtale B S hS (X.obj (op n)) :=
  (spacesBaseChange B S hS (X.map x.simplex.op)).functor.obj x.obj

variable (X) in
/-- **The strict degree-`n` component of `X_{spaces,étale}`**: the triples `(k, V, ψ)`, with the
morphisms of their realizations. -/
abbrev StrictComponent (n : SimplexCategory) : Type (u + 1) :=
  InducedCategory (SpacesEtale B S hS (X.obj (op n))) (StrictObj.realize (X := X) (n := n))

variable (X) in
/-- The realization functor of the strict degree-`n` component. -/
abbrev strictRealize (n : SimplexCategory) :
    StrictComponent X n ⥤ SpacesEtale B S hS (X.obj (op n)) :=
  inducedFunctor _

/-- An object `V/X_n` of `(X_n)_{spaces,étale}`, as the triple `(n, V, 𝟙)`. -/
def StrictObj.ofSpacesEtale {n : SimplexCategory} (V : SpacesEtale B S hS (X.obj (op n))) :
    StrictComponent X n :=
  ⟨n, V, OrderHom.id⟩

/-- The first projection of the base change along `X(𝟙) = 𝟙` is an isomorphism. -/
theorem StrictObj.isIso_pullback_fst_map_id {n : SimplexCategory}
    (V : SpacesEtale B S hS (X.obj (op n))) :
    IsIso (pullback.fst V.1.hom (X.map (𝟙 n).op)) := by
  have : IsIso (X.map (𝟙 n).op) := by rw [op_id, X.map_id]; infer_instance
  exact (IsPullback.of_hasPullback V.1.hom (X.map (𝟙 n).op)).isIso_fst_of_isIso

/-- The realization of `(n, V, 𝟙)` is `V`: base change along `X(𝟙) = 𝟙` is the identity, by its
first projection. -/
def StrictObj.realizeOfSpacesEtaleIso {n : SimplexCategory}
    (V : SpacesEtale B S hS (X.obj (op n))) :
    (StrictObj.ofSpacesEtale V).realize ≅ V :=
  (IsEtaleOver B S hS (X.obj (op n))).isoMk (Over.isoMk
    (@asIso _ _ _ _ (pullback.fst V.1.hom (X.map (𝟙 n).op))
      (StrictObj.isIso_pullback_fst_map_id V)) (by
      change pullback.fst _ _ ≫ V.1.hom = pullback.snd _ _
      rw [pullback.condition, op_id, X.map_id, Category.comp_id]))

/-- The realization functor of the strict degree-`n` component is essentially surjective. -/
instance strictRealize_essSurj (n : SimplexCategory) : (strictRealize X n).EssSurj where
  mem_essImage V := ⟨StrictObj.ofSpacesEtale V, ⟨StrictObj.realizeOfSpacesEtaleIso V⟩⟩

/-- The realization functor of the strict degree-`n` component is an equivalence. -/
instance strictRealize_isEquivalence (n : SimplexCategory) : (strictRealize X n).IsEquivalence
  where

/-! ### Base change acts strictly on objects -/

/-- The action of `φ : [m] ⟶ [n]` on triples: `(k, V, ψ) ↦ (k, V, ψ ≫ φ)`. -/
def StrictObj.transition {m n : SimplexCategory} (φ : m ⟶ n) (x : StrictObj X m) :
    StrictObj X n :=
  ⟨x.degree, x.obj, φ.toOrderHom.comp x.map⟩

/-- The degree of `(k, V, ψ ≫ φ)` is `k`. -/
@[simp] theorem StrictObj.transition_degree {m n : SimplexCategory} (φ : m ⟶ n)
    (x : StrictObj X m) : (x.transition φ).degree = x.degree := rfl

/-- The algebraic space of `(k, V, ψ ≫ φ)` is `V`. -/
@[simp] theorem StrictObj.transition_obj {m n : SimplexCategory} (φ : m ⟶ n)
    (x : StrictObj X m) : (x.transition φ).obj = x.obj := rfl

/-- The simplex map of `(k, V, ψ ≫ φ)` is `ψ ≫ φ`. -/
@[simp] theorem StrictObj.transition_simplex {m n : SimplexCategory} (φ : m ⟶ n)
    (x : StrictObj X m) : (x.transition φ).simplex = x.simplex ≫ φ := rfl

/-- The comparison `V ×_{X_k} X_n ⟶ (V ×_{X_k} X_m) ×_{X_m} X_n` of iterated base changes along
`X(ψ ≫ φ)` and along `X(ψ)` then `X(φ)`. -/
def StrictObj.realizeCompHom {k m n : SimplexCategory} (V : SpacesEtale B S hS (X.obj (op k)))
    (ψ : k ⟶ m) (φ : m ⟶ n) :
    pullback V.1.hom (X.map (ψ ≫ φ).op) ⟶
      pullback (pullback.snd V.1.hom (X.map ψ.op)) (X.map φ.op) :=
  pullback.lift (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ X.map φ.op) (by
      rw [pullback.condition, op_comp, X.map_comp, Category.assoc]))
    (pullback.snd _ _) (pullback.lift_snd _ _ _)

/-- The comparison `StrictObj.realizeCompHom` followed by the first projection is the map
`V ×_{X_k} X_n ⟶ V ×_{X_k} X_m` induced by the first projection and `X(φ)`. -/
theorem StrictObj.realizeCompHom_fst {k m n : SimplexCategory}
    (V : SpacesEtale B S hS (X.obj (op k))) (ψ : k ⟶ m) (φ : m ⟶ n) :
    StrictObj.realizeCompHom V ψ φ ≫ pullback.fst (pullback.snd V.1.hom (X.map ψ.op)) (X.map φ.op) =
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ X.map φ.op) (by
        rw [pullback.condition, op_comp, X.map_comp, Category.assoc]) :=
  pullback.lift_fst _ _ _

/-- Compatibility of `StrictObj.realizeCompHom` with composition `φ ≫ φ'`, after the first
projections. -/
theorem StrictObj.realizeCompHom_comp_fst {k l m n : SimplexCategory}
    (V : SpacesEtale B S hS (X.obj (op k))) (ψ : k ⟶ l) (φ : l ⟶ m) (φ' : m ⟶ n) :
    StrictObj.realizeCompHom V ψ (φ ≫ φ') ≫
        pullback.fst (pullback.snd V.1.hom (X.map ψ.op)) (X.map (φ ≫ φ').op) =
      StrictObj.realizeCompHom V (ψ ≫ φ) φ' ≫
        pullback.fst (pullback.snd V.1.hom (X.map (ψ ≫ φ).op)) (X.map φ'.op) ≫
          StrictObj.realizeCompHom V ψ φ ≫
            pullback.fst (pullback.snd V.1.hom (X.map ψ.op)) (X.map φ.op) := by
  have e : X.map (φ ≫ φ').op = X.map φ'.op ≫ X.map φ.op := by rw [op_comp, X.map_comp]
  rw [StrictObj.realizeCompHom_fst, StrictObj.realizeCompHom_fst,
    reassoc_of% (StrictObj.realizeCompHom_fst V (ψ ≫ φ) φ')]
  refine pullback.hom_ext ?_ ?_
  · exact (pullback.lift_fst _ _ _).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans (pullback.lift_fst _ _ _))).symm
  · exact (pullback.lift_snd _ _ _).trans ((congrArg (pullback.snd _ _ ≫ ·) e).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X.map φ.op)
          (pullback.lift_snd _ _ _)).trans (Category.assoc _ _ _))))).symm)

/-- The comparison `V ×_{X_k} X_n ⟶ (V ×_{X_k} X_m) ×_{X_m} X_n` underlying
`StrictObj.transitionRealizeIso`. -/
abbrev StrictObj.transitionRealizeHom {m n : SimplexCategory} (φ : m ⟶ n) (x : StrictObj X m) :
    pullback x.obj.1.hom (X.map (x.simplex ≫ φ).op) ⟶
      pullback (pullback.snd x.obj.1.hom (X.map x.simplex.op)) (X.map φ.op) :=
  StrictObj.realizeCompHom x.obj x.simplex φ

/-- The inverse comparison `(V ×_{X_k} X_m) ×_{X_m} X_n ⟶ V ×_{X_k} X_n`. -/
def StrictObj.transitionRealizeInv {m n : SimplexCategory} (φ : m ⟶ n) (x : StrictObj X m) :
    pullback (pullback.snd x.obj.1.hom (X.map x.simplex.op)) (X.map φ.op) ⟶
      pullback x.obj.1.hom (X.map (x.simplex ≫ φ).op) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, op_comp, X.map_comp])

/-- `StrictObj.transitionRealizeInv` is a left inverse of `StrictObj.transitionRealizeHom`. -/
theorem StrictObj.transitionRealizeHom_inv {m n : SimplexCategory} (φ : m ⟶ n)
    (x : StrictObj X m) :
    StrictObj.transitionRealizeHom φ x ≫ StrictObj.transitionRealizeInv φ x = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, StrictObj.transitionRealizeInv, pullback.lift_fst,
      StrictObj.transitionRealizeHom, StrictObj.realizeCompHom, ← Category.assoc,
      pullback.lift_fst, pullback.lift_fst, Category.id_comp]
  · rw [Category.assoc, StrictObj.transitionRealizeInv, pullback.lift_snd,
      StrictObj.transitionRealizeHom, StrictObj.realizeCompHom, pullback.lift_snd, Category.id_comp]

/-- `StrictObj.transitionRealizeInv` is a right inverse of `StrictObj.transitionRealizeHom`. -/
theorem StrictObj.transitionRealizeInv_hom {m n : SimplexCategory} (φ : m ⟶ n)
    (x : StrictObj X m) :
    StrictObj.transitionRealizeInv φ x ≫ StrictObj.transitionRealizeHom φ x = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, StrictObj.transitionRealizeHom, StrictObj.realizeCompHom,
        pullback.lift_fst_assoc, pullback.lift_fst, StrictObj.transitionRealizeInv,
        pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, Category.assoc, StrictObj.transitionRealizeHom, StrictObj.realizeCompHom,
        pullback.lift_fst_assoc, pullback.lift_snd, ← Category.assoc,
        StrictObj.transitionRealizeInv, pullback.lift_snd, Category.id_comp]
      exact pullback.condition.symm
  · rw [Category.assoc, StrictObj.transitionRealizeHom, StrictObj.realizeCompHom, pullback.lift_snd,
      StrictObj.transitionRealizeInv, pullback.lift_snd, Category.id_comp]

/-- **The realization of `(k, V, ψ ≫ φ)` is the base change along `X(φ)` of the realization of
`(k, V, ψ)`**, by the pasting of fibre products. -/
def StrictObj.transitionRealizeIso {m n : SimplexCategory} (φ : m ⟶ n) (x : StrictObj X m) :
    (x.transition φ).realize ≅ (spacesBaseChange B S hS (X.map φ.op)).functor.obj x.realize :=
  (IsEtaleOver B S hS (X.obj (op n))).isoMk (Over.isoMk
    ⟨StrictObj.transitionRealizeHom φ x, StrictObj.transitionRealizeInv φ x,
      StrictObj.transitionRealizeHom_inv φ x, StrictObj.transitionRealizeInv_hom φ x⟩
    (pullback.lift_snd _ _ _))

variable (X) in
/-- **The transition functor `u_φ` of the strict components** for `φ : [m] ⟶ [n]`: on objects
`(k, V, ψ) ↦ (k, V, ψ ≫ φ)`, on morphisms the base change along `X(φ)` read through
`StrictObj.transitionRealizeIso`. -/
def strictTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    StrictComponent X m ⥤ StrictComponent X n where
  obj x := x.transition φ
  map {x y} g := InducedCategory.homMk ((StrictObj.transitionRealizeIso φ x).hom ≫
    (spacesBaseChange B S hS (X.map φ.op)).functor.map g.hom ≫
      (StrictObj.transitionRealizeIso φ y).inv)
  map_id x := InducedCategory.hom_ext (by
    simp only [InducedCategory.homMk_hom, InducedCategory.id_hom, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.hom_inv_id])
  map_comp {x y z} f g := InducedCategory.hom_ext (by
    simp only [InducedCategory.homMk_hom, InducedCategory.comp_hom, CategoryTheory.Functor.map_comp,
      Category.assoc, Iso.inv_hom_id_assoc])

variable (X) in
/-- The transition functor `u_φ` realizes to base change along `X(φ)`. -/
def strictTransitionRealizeIso {m n : SimplexCategory} (φ : m ⟶ n) :
    strictTransition X φ ⋙ strictRealize X n ≅
      strictRealize X m ⋙ (spacesBaseChange B S hS (X.map φ.op)).functor :=
  NatIso.ofComponents (fun x ↦ StrictObj.transitionRealizeIso φ x) (fun {x y} g ↦ by
    simp only [Functor.comp_map, strictTransition, inducedFunctor_map,
      InducedCategory.homMk_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-! ### Strictness of the transition functors -/

/-- `StrictObj.transitionRealizeHom` followed by the first projection is the map induced by the
first projection and `X(φ)`. -/
theorem StrictObj.transitionRealizeHom_fst {m n : SimplexCategory} (φ : m ⟶ n)
    (x : StrictObj X m) :
    StrictObj.transitionRealizeHom φ x ≫ pullback.fst _ _ =
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ X.map φ.op) (by
        rw [pullback.condition, op_comp, X.map_comp, Category.assoc]) :=
  pullback.lift_fst _ _ _

/-- `StrictObj.transitionRealizeHom` commutes with the second projections. -/
theorem StrictObj.transitionRealizeHom_snd {m n : SimplexCategory} (φ : m ⟶ n)
    (x : StrictObj X m) :
    StrictObj.transitionRealizeHom φ x ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- `StrictObj.transitionRealizeInv` followed by the first projection is the composite of the
first projections. -/
theorem StrictObj.transitionRealizeInv_fst {m n : SimplexCategory} (φ : m ⟶ n)
    (x : StrictObj X m) :
    StrictObj.transitionRealizeInv φ x ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- `StrictObj.transitionRealizeInv` commutes with the second projections. -/
theorem StrictObj.transitionRealizeInv_snd {m n : SimplexCategory} (φ : m ⟶ n)
    (x : StrictObj X m) :
    StrictObj.transitionRealizeInv φ x ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The base change of a morphism `k` of `(X_m)_{spaces,étale}` along `f`, followed by the
first projection, is the first projection followed by `k`. -/
theorem spacesBaseChange_map_fst {Y Z : AlgebraicSpaces B S hS} (f : Y ⟶ Z)
    {V W : SpacesEtale B S hS Z} (k : V ⟶ W) :
    ((spacesBaseChange B S hS f).functor.map k).hom.left ≫ pullback.fst W.1.hom f =
      pullback.fst V.1.hom f ≫ k.hom.left :=
  pullback.lift_fst _ _ _

/-- The base change of a morphism of `(X_m)_{spaces,étale}` along `f` commutes with the second
projections. -/
theorem spacesBaseChange_map_snd {Y Z : AlgebraicSpaces B S hS} (f : Y ⟶ Z)
    {V W : SpacesEtale B S hS Z} (k : V ⟶ W) :
    ((spacesBaseChange B S hS f).functor.map k).hom.left ≫ pullback.snd W.1.hom f =
      pullback.snd V.1.hom f :=
  Over.w ((spacesBaseChange B S hS f).functor.map k).hom

/-- The underlying morphism of a map of strict components, followed by the second projection
of the target realization, is the second projection of the source realization. -/
theorem StrictObj.hom_snd {n : SimplexCategory} {x y : StrictComponent X n} (g : x ⟶ y) :
    g.hom.hom.left ≫ pullback.snd y.obj.1.hom (X.map y.simplex.op) =
      pullback.snd x.obj.1.hom (X.map x.simplex.op) :=
  Over.w g.hom.hom

/-- Two maps of strict components agree when they agree after the first projection of the
target realization. -/
theorem StrictObj.hom_ext {n : SimplexCategory} {x y : StrictComponent X n} {g g' : x ⟶ y}
    (h : g.hom.hom.left ≫ pullback.fst y.obj.1.hom (X.map y.simplex.op) =
      g'.hom.hom.left ≫ pullback.fst y.obj.1.hom (X.map y.simplex.op)) : g = g' :=
  InducedCategory.hom_ext (ObjectProperty.hom_ext _ (Over.OverMorphism.ext
    (pullback.hom_ext h ((StrictObj.hom_snd g).trans (StrictObj.hom_snd g').symm))))

/-- The image of a morphism `g` under `u_φ`, followed by the first projection, is
`StrictObj.transitionRealizeHom` followed by the first projection, then `g` and the first
projection. -/
theorem strictTransition_map_hom_left_fst {m n : SimplexCategory} (φ : m ⟶ n)
    {x y : StrictComponent X m} (g : x ⟶ y) :
    ((strictTransition X φ).map g).hom.hom.left ≫ pullback.fst _ _ =
      StrictObj.transitionRealizeHom φ x ≫ pullback.fst _ _ ≫ g.hom.hom.left ≫
        pullback.fst _ _ := by
  show (StrictObj.transitionRealizeHom φ x ≫
      ((spacesBaseChange B S hS (X.map φ.op)).functor.map g.hom).hom.left ≫
        StrictObj.transitionRealizeInv φ y) ≫ pullback.fst _ _ = _
  exact (Category.assoc _ _ _).trans (congrArg (StrictObj.transitionRealizeHom φ x ≫ ·)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (StrictObj.transitionRealizeInv_fst φ y)).trans
      ((Category.assoc _ _ _).symm.trans ((spacesBaseChange_map_fst (X.map φ.op) g.hom =≫
        pullback.fst y.obj.1.hom (X.map y.simplex.op)).trans (Category.assoc _ _ _))))))

/-- For `φ = 𝟙`, `StrictObj.transitionRealizeHom` followed by the first projection is the
identity. -/
theorem StrictObj.transitionRealizeHom_id_fst {n : SimplexCategory} (x : StrictObj X n) :
    StrictObj.transitionRealizeHom (𝟙 n) x ≫
        pullback.fst (pullback.snd x.obj.1.hom (X.map x.simplex.op)) (X.map (𝟙 n).op) =
      𝟙 (pullback x.obj.1.hom (X.map x.simplex.op)) := by
  refine (StrictObj.transitionRealizeHom_fst (𝟙 n) x).trans (pullback.hom_ext ?_ ?_)
  · exact (pullback.lift_fst _ _ _).trans (Category.id_comp _).symm
  · refine (pullback.lift_snd _ _ _).trans ((congrArg (pullback.snd _ _ ≫ ·)
      (by rw [op_id, X.map_id] : X.map (𝟙 n).op = 𝟙 _)).trans ?_)
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The transition functor of the identity is the identity on morphisms. -/
theorem strictTransition_map_id {n : SimplexCategory} {x y : StrictComponent X n} (g : x ⟶ y) :
    (strictTransition X (𝟙 n)).map g = g :=
  StrictObj.hom_ext (x := x) (y := y) ((strictTransition_map_hom_left_fst (𝟙 n) g).trans
    (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ g.hom.hom.left ≫
      pullback.fst y.obj.1.hom (X.map y.simplex.op))
        (StrictObj.transitionRealizeHom_id_fst x))).trans (Category.id_comp _)))

/-- On morphisms, `u_{φ ≫ φ'}` is `u_φ` followed by `u_{φ'}`. -/
theorem strictTransition_map_comp {l m n : SimplexCategory} (φ : l ⟶ m) (φ' : m ⟶ n)
    {x y : StrictComponent X l} (g : x ⟶ y) :
    (strictTransition X (φ ≫ φ')).map g =
      (strictTransition X φ').map ((strictTransition X φ).map g) :=
  StrictObj.hom_ext (x := (x.transition φ).transition φ') (y := (y.transition φ).transition φ')
    ((strictTransition_map_hom_left_fst (φ ≫ φ') g).trans
      (((reassoc_of% (StrictObj.realizeCompHom_comp_fst x.obj x.simplex φ φ')) _).trans
        ((congrArg (StrictObj.transitionRealizeHom φ' (x.transition φ) ≫
          pullback.fst (pullback.snd x.obj.1.hom (X.map (x.simplex ≫ φ).op)) (X.map φ'.op) ≫ ·)
            (strictTransition_map_hom_left_fst φ g).symm).trans
          (strictTransition_map_hom_left_fst φ' ((strictTransition X φ).map g)).symm)))

variable (X) in
/-- **The transition functor of the identity is the identity**, on the nose. -/
theorem strictTransition_id (n : SimplexCategory) :
    strictTransition X (𝟙 n) = 𝟭 (StrictComponent X n) :=
  Functor.hext (fun _ ↦ rfl) (fun _ _ g ↦ heq_of_eq (strictTransition_map_id g))

variable (X) in
/-- **The transition functors compose strictly**: `u_{φ ≫ φ'} = u_φ ⋙ u_{φ'}`. -/
theorem strictTransition_comp {l m n : SimplexCategory} (φ : l ⟶ m) (φ' : m ⟶ n) :
    strictTransition X (φ ≫ φ') = strictTransition X φ ⋙ strictTransition X φ' :=
  Functor.hext (fun _ ↦ rfl) (fun _ _ g ↦ heq_of_eq (strictTransition_map_comp φ φ' g))

variable (X) in
/-- **The strict cosimplicial diagram of components** `[n] ↦ (X_n)_{spaces,étale}`, with
transition functors `u_φ` composing on the nose. -/
def strictCosimplicial : SimplexCategory ⥤ Cat.{u + 1, u + 1} where
  obj n := Cat.of (StrictComponent X n)
  map φ := (strictTransition X φ).toCatHom
  map_id n := congrArg Functor.toCatHom (strictTransition_id X n)
  map_comp φ φ' := congrArg Functor.toCatHom (strictTransition_comp X φ φ')

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
