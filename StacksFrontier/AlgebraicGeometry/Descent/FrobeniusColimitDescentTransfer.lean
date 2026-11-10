module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitComparison
public import StacksFrontier.CategoryTheory.Sites.Descent.StrongTransDescentData
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# Descent passes to colimits along an endomorphism

Let `V` and `P` be pseudofunctors from `LocallyDiscrete Cᵒᵖ` to `Cat`, let `Φ : V ⟶ V` be a strong
transformation and let `σ n : V ⟶ P` be strong transformations, one for every `n : ℕ`, together
with natural isomorphisms `μ n U : Φ_U ⋙ (σ (n + 1))_U ≅ (σ n)_U` compatible with the naturality
isomorphisms of the three transformations.  At every object `U` this is a pseudo-cocone
`CategoryTheory.EndoColim.Pseudococone` on the sequential diagram `V(U) →Φ V(U) →Φ ⋯` with summit
`P(U)`.

Suppose that at the objects relevant to a morphism `f : X ⟶ S` — `S`, `X`, `X ×_S X` and
`X ×_S X ×_S X` — that pseudo-cocone presents `P(U)` as the colimit of the diagram in the sense of
Stacks Tag 0EXA.  Then **if `V` has effective descent along `{f}`, so has `P`**.

## Main definitions

* `CategoryTheory.EndoColim.Pseudococone.IsColimitPresentation`: a pseudo-cocone presents its
  summit as the colimit of the sequential diagram.
* `CategoryTheory.Pseudofunctor.StrongTrans.pullIsoIter`: the naturality isomorphism of the
  iterate `Φ^k`, `Φ^k (h^* M) ≅ h^* (Φ^k M)`.
* `CategoryTheory.Pseudofunctor.SinglePreDatum`: an object over `X` with a morphism between its
  two pullbacks to `X ×_S X`, not subject to any condition.
* `CategoryTheory.Pseudofunctor.StageColimitData`: the transformations `Φ`, `σ n` and the
  isomorphisms `μ n`.

## Main results

* `CategoryTheory.Pseudofunctor.StageColimitData.essSurj_toDescentData`: if `V` is a stack for
  `{f}`, every descent datum of `P` relative to `{f}` is effective.
* `CategoryTheory.Pseudofunctor.StageColimitData.isStackFor_singleton`: if `V` is a stack for
  `{f}`, so is `P`.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
-/

@[expose] public noncomputable section

universe v' u' v u

namespace CategoryTheory

open Opposite Limits

namespace EndoColim.Pseudococone

variable {A : Type u} [Category.{v} A] {Φ : A ⥤ A} {B : Type u'} [Category.{v'} B]

/-- **A pseudo-cocone presents its summit as the colimit of the sequential diagram** of Stacks
Tag 0EXA: every object of the summit is a stage image, every morphism between two stage images at
one stage is induced by a morphism at some twist, and two morphisms which a stage functor
identifies are identified by some iterate of the endofunctor. -/
structure IsColimitPresentation (P : Pseudococone Φ B) : Prop where
  exists_iso : ∀ M : B, ∃ (n : ℕ) (E : A), Nonempty ((P.stage n).obj E ≅ M)
  exists_mapAt : ∀ (n : ℕ) (E G : A) (m : (P.stage n).obj E ⟶ (P.stage n).obj G),
    ∃ (k : ℕ) (a : (Φ.endoIter k).obj E ⟶ (Φ.endoIter k).obj G), P.mapAt n n k k rfl a = m
  exists_map_eq : ∀ (n : ℕ) (E G : A) (a a' : E ⟶ G), (P.stage n).map a = (P.stage n).map a' →
    ∃ j, (Φ.endoIter j).map a = (Φ.endoIter j).map a'

/-- At equal source and target stages, `P.mapAt n n k k rfl a` is the stage-`(n + k)` image of `a`
conjugated by the isomorphisms `P.iterObjIso n k`. -/
lemma mapAt_self (P : Pseudococone Φ B) (n k : ℕ) {E G : A}
    (a : (Φ.endoIter k).obj E ⟶ (Φ.endoIter k).obj G) :
    P.mapAt n n k k rfl a =
      (P.iterObjIso n k E).inv ≫ (P.stage (n + k)).map a ≫ (P.iterObjIso n k G).hom := by
  simp only [mapAt, stageHom_refl, NatTrans.id_app, Category.id_comp]

/-- The morphism a morphism at twist `k` induces, presented at a larger twist. -/
lemma mapAt_le (P : Pseudococone Φ B) (n : ℕ) {E G : A} (k : ℕ)
    (a : (Φ.endoIter k).obj E ⟶ (Φ.endoIter k).obj G) (k' : ℕ) (hk : k ≤ k') :
    ∃ a' : (Φ.endoIter k').obj E ⟶ (Φ.endoIter k').obj G,
      P.mapAt n n k' k' rfl a' = P.mapAt n n k k rfl a := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact ⟨endoRaise a j, P.mapAt_raise n n k k rfl a j rfl⟩

/-- Casting morphisms between iterates along equalities of the exponents is injective. -/
lemma endoHomCast_injective {E G : A} {m n m' n' : ℕ} (hm : m = m') (hn : n = n')
    {f f' : (Φ.endoIter m).obj E ⟶ (Φ.endoIter n).obj G}
    (h : endoHomCast hm hn f = endoHomCast hm hn f') : f = f' := by
  subst hm hn
  exact h

/-- **A pseudo-cocone whose induced functor out of the colimit category is fully faithful, and
whose summit consists of stage images, presents the summit as the colimit.** -/
theorem isColimitPresentation_of_desc (P : Pseudococone Φ B)
    (hess : ∀ M : B, ∃ (n : ℕ) (E : A), Nonempty ((P.stage n).obj E ≅ M))
    [P.desc.Full] [P.desc.Faithful] : P.IsColimitPresentation where
  exists_iso := hess
  exists_mapAt n E G m := by
    obtain ⟨u, hu⟩ := P.desc.map_surjective (X := (⟨E, n⟩ : EndoColim Φ)) (Y := ⟨G, n⟩) m
    obtain ⟨k, a, rfl⟩ := Hom.exists_of u
    exact ⟨n + k, a, hu⟩
  exists_map_eq n E G a a' h := by
    have h' : P.desc.map ((stageFunctor Φ n).map a) = P.desc.map ((stageFunctor Φ n).map a') := by
      rw [desc_map, desc_map, homMap_stageFunctor_map, homMap_stageFunctor_map, h]
    have h'' := P.desc.map_injective h'
    change Hom.of (A := (⟨E, n⟩ : EndoColim Φ)) (B := ⟨G, n⟩) 0 ((Φ.endoIter (n + 0)).map a) =
      Hom.of 0 ((Φ.endoIter (n + 0)).map a') at h''
    rw [Hom.of_eq_of_iff] at h''
    obtain ⟨j, i, hji, e⟩ := h''
    simp only [zero_add] at hji
    subst hji
    have e' := endoHomCast_injective _ _ e
    dsimp only at e'
    rw [endoRaise_endoIter_map, endoRaise_endoIter_map] at e'
    exact ⟨n + 0 + j, endoHomCast_injective _ _ e'⟩

end EndoColim.Pseudococone

/-- Two morphisms identified by an iterate are identified by every larger iterate. -/
lemma Functor.endoIter_map_eq_of_le {A : Type u} [Category.{v} A] (Φ : A ⥤ A) {E G : A}
    {a a' : E ⟶ G} {j : ℕ} (h : (Φ.endoIter j).map a = (Φ.endoIter j).map a') :
    ∀ j', j ≤ j' → (Φ.endoIter j').map a = (Φ.endoIter j').map a' := by
  intro j' hj
  induction j', hj using Nat.le_induction with
  | base => exact h
  | succ j' _ ih => exact congrArg Φ.map ih

namespace Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
  {V P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

namespace StrongTrans

variable (Φ : StrongTrans V V)

/-- The `k`-th iterate of the component of an endo-transformation at `U`. -/
abbrev iterFunctor (U : C) (k : ℕ) : V.obj (.mk (op U)) ⥤ V.obj (.mk (op U)) :=
  (Φ.app (.mk (op U))).toFunctor.endoIter k

/-- **The naturality isomorphism of the `k`-th iterate of an endo-transformation**,
`Φ^k (h^* M) ≅ h^* (Φ^k M)`. -/
def pullIsoIter {X Y : C} (h : Y ⟶ X) (M : V.obj (.mk (op X))) :
    ∀ k : ℕ, (Φ.iterFunctor Y k).obj ((V.map h.op.toLoc).toFunctor.obj M) ≅
      (V.map h.op.toLoc).toFunctor.obj ((Φ.iterFunctor X k).obj M)
  | 0 => Iso.refl _
  | k + 1 => (Φ.app (.mk (op Y))).toFunctor.mapIso (pullIsoIter h M k) ≪≫
      Φ.pullIso h ((Φ.iterFunctor X k).obj M)

/-- The naturality isomorphism of the zeroth iterate is the identity. -/
lemma pullIsoIter_zero {X Y : C} (h : Y ⟶ X) (M : V.obj (.mk (op X))) :
    Φ.pullIsoIter h M 0 = Iso.refl _ := rfl

/-- The naturality isomorphism of the `(k + 1)`-st iterate is `Φ` applied to that of the `k`-th
iterate, followed by the naturality isomorphism of `Φ`. -/
lemma pullIsoIter_succ_hom {X Y : C} (h : Y ⟶ X) (M : V.obj (.mk (op X))) (k : ℕ) :
    (Φ.pullIsoIter h M (k + 1)).hom =
      (Φ.app (.mk (op Y))).toFunctor.map (Φ.pullIsoIter h M k).hom ≫
        (Φ.pullIso h ((Φ.iterFunctor X k).obj M)).hom := rfl

/-- The inverse of the naturality isomorphism of the `(k + 1)`-st iterate is the inverse
naturality isomorphism of `Φ`, followed by `Φ` applied to the inverse for the `k`-th iterate. -/
lemma pullIsoIter_succ_inv {X Y : C} (h : Y ⟶ X) (M : V.obj (.mk (op X))) (k : ℕ) :
    (Φ.pullIsoIter h M (k + 1)).inv =
      (Φ.pullIso h ((Φ.iterFunctor X k).obj M)).inv ≫
        (Φ.app (.mk (op Y))).toFunctor.map (Φ.pullIsoIter h M k).inv := rfl

/-- **The naturality isomorphism of an iterate is natural.** -/
@[reassoc]
lemma pullIsoIter_naturality {X Y : C} (h : Y ⟶ X) {M N : V.obj (.mk (op X))} (ψ : M ⟶ N) :
    ∀ k : ℕ, (Φ.iterFunctor Y k).map ((V.map h.op.toLoc).toFunctor.map ψ) ≫
        (Φ.pullIsoIter h N k).hom =
      (Φ.pullIsoIter h M k).hom ≫ (V.map h.op.toLoc).toFunctor.map ((Φ.iterFunctor X k).map ψ)
  | 0 => by simp [pullIsoIter]
  | k + 1 => by
      have e1 := congrArg (fun t ↦ (Φ.app (.mk (op Y))).toFunctor.map t ≫
        (Φ.pullIso h ((Φ.iterFunctor X k).obj N)).hom) (pullIsoIter_naturality h ψ k)
      have e2 := Φ.pullIso_naturality h ((Φ.iterFunctor X k).map ψ)
      simp only [Functor.map_comp, Category.assoc] at e1
      rw [e2] at e1
      exact e1.trans (Category.assoc _ _ _).symm

end StrongTrans

/-! ### Pre-descent data relative to one morphism -/

section PreDatum

variable {X S : C} {f : X ⟶ S} (sq : ChosenPullback f f)

/-- The chosen pullbacks of the one-element family `{f}`. -/
abbrev sqF : ∀ _ _ : PUnit.{1}, ChosenPullback ((fun _ : PUnit.{1} ↦ f) PUnit.unit)
    ((fun _ : PUnit.{1} ↦ f) PUnit.unit) := fun _ _ ↦ sq

/-- The chosen threefold pullbacks of the one-element family `{f}`. -/
abbrev sq₃F (sq₃ : ChosenPullback₃ sq sq sq) :
    ∀ i j k : PUnit.{1}, ChosenPullback₃ (sqF sq i j) (sqF sq j k) (sqF sq i k) :=
  fun _ _ _ ↦ sq₃

variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

/-- **A pre-descent datum relative to `{f}`**: an object over `X` and a morphism between its two
pullbacks to `X ×_S X`, with no condition imposed. -/
structure SinglePreDatum where
  /-- the object over `X` -/
  obj : F.obj (.mk (op X))
  /-- the morphism over `X ×_S X` -/
  hom : (F.map sq.p₁.op.toLoc).toFunctor.obj obj ⟶ (F.map sq.p₂.op.toLoc).toFunctor.obj obj

variable {sq F}

namespace SinglePreDatum

variable (D : SinglePreDatum sq F)

/-- The morphism of a pre-descent datum, as a family over the one-element family. -/
abbrev homF : ∀ i j : PUnit.{1},
    (F.map (sqF sq i j).p₁.op.toLoc).toFunctor.obj ((fun _ : PUnit.{1} ↦ D.obj) i) ⟶
      (F.map (sqF sq i j).p₂.op.toLoc).toFunctor.obj ((fun _ : PUnit.{1} ↦ D.obj) j) :=
  fun _ _ ↦ D.hom

/-- The pullback of the morphism of a pre-descent datum along a pair of morphisms into `X`. -/
abbrev pull {Y : C} (q : Y ⟶ S) (f₁ f₂ : Y ⟶ X) (hf₁ : f₁ ≫ f = q) (hf₂ : f₂ ≫ f = q) :
    (F.map f₁.op.toLoc).toFunctor.obj D.obj ⟶ (F.map f₂.op.toLoc).toFunctor.obj D.obj :=
  DescentData'.pullHom' (sq := sqF sq) (f := fun _ : PUnit.{1} ↦ f) D.homF q
    (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁ f₂ hf₁ hf₂

/-- **The two conditions of a descent datum**: the pullback along the diagonal is the identity,
and the cocycle condition holds over `X ×_S X ×_S X`. -/
structure IsDatum (sq₃ : ChosenPullback₃ sq sq sq) : Prop where
  self : D.pull f (𝟙 X) (𝟙 X) (Category.id_comp f) (Category.id_comp f) = 𝟙 _
  comp : D.pull sq₃.p sq₃.p₁ sq₃.p₂ sq₃.w₁ sq₃.w₂ ≫ D.pull sq₃.p sq₃.p₂ sq₃.p₃ sq₃.w₂ sq₃.w₃ =
    D.pull sq₃.p sq₃.p₁ sq₃.p₃ sq₃.w₁ sq₃.w₃

/-- The pullback `D.pull q f₁ f₂ hf₁ hf₂` is `pullHom D.hom` along the morphism `Y ⟶ X ×_S X`
induced by `f₁` and `f₂`. -/
lemma pull_eq_pullHom {Y : C} (q : Y ⟶ S) (f₁ f₂ : Y ⟶ X) (hf₁ : f₁ ≫ f = q)
    (hf₂ : f₂ ≫ f = q) :
    D.pull q f₁ f₂ hf₁ hf₂ = pullHom D.hom (sq.isPullback.lift f₁ f₂ (by rw [hf₁, hf₂])) f₁ f₂
      (sq.isPullback.lift_fst _ _ _) (sq.isPullback.lift_snd _ _ _) := rfl

/-- The transport of a pre-descent datum along a strong transformation. -/
@[reducible, simps]
def map {G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}} (τ : StrongTrans F G) :
    SinglePreDatum sq G where
  obj := (τ.app (.mk (op X))).toFunctor.obj D.obj
  hom := τ.mapPullHom D.hom

/-- The pullbacks of the transport of a pre-descent datum along `τ` are the transports
`τ.mapPullHom` of its pullbacks. -/
lemma map_pull {G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}} (τ : StrongTrans F G)
    {Y : C} (q : Y ⟶ S) (f₁ f₂ : Y ⟶ X) (hf₁ : f₁ ≫ f = q) (hf₂ : f₂ ≫ f = q) :
    (D.map τ).pull q f₁ f₂ hf₁ hf₂ = τ.mapPullHom (D.pull q f₁ f₂ hf₁ hf₂) :=
  τ.pullHom_mapPullHom D.hom _ _ _ _ _

/-- **An isomorphism of pre-descent data**: an isomorphism of the objects over `X` compatible
with the morphisms over `X ×_S X`. -/
structure Iso (D₁ D₂ : SinglePreDatum sq F) where
  /-- the isomorphism of the objects -/
  e : D₁.obj ≅ D₂.obj
  comm : (F.map sq.p₁.op.toLoc).toFunctor.map e.hom ≫ D₂.hom =
    D₁.hom ≫ (F.map sq.p₂.op.toLoc).toFunctor.map e.hom

variable {D}

/-- For an isomorphism `e : D₁.Iso D₂` of pre-descent data, the morphism of `D₂` is that of `D₁`
conjugated by the two pullbacks of `e.e`. -/
lemma Iso.hom_eq {D₁ D₂ : SinglePreDatum sq F} (e : D₁.Iso D₂) :
    D₂.hom = (F.map sq.p₁.op.toLoc).toFunctor.map e.e.inv ≫ D₁.hom ≫
      (F.map sq.p₂.op.toLoc).toFunctor.map e.e.hom := by
  rw [← e.comm, ← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]

/-- For an isomorphism `e : D₁.Iso D₂` of pre-descent data, every pullback of the morphism of
`D₂` is the corresponding pullback for `D₁` conjugated by the pullbacks of `e.e`. -/
lemma Iso.pull {D₁ D₂ : SinglePreDatum sq F} (e : D₁.Iso D₂) {Y : C} (q : Y ⟶ S)
    (f₁ f₂ : Y ⟶ X) (hf₁ : f₁ ≫ f = q) (hf₂ : f₂ ≫ f = q) :
    D₂.pull q f₁ f₂ hf₁ hf₂ = (F.map f₁.op.toLoc).toFunctor.map e.e.inv ≫
      D₁.pull q f₁ f₂ hf₁ hf₂ ≫ (F.map f₂.op.toLoc).toFunctor.map e.e.hom := by
  rw [pull_eq_pullHom, pull_eq_pullHom, e.hom_eq, pullHom_map_comp_map]

/-- The inverse of an isomorphism of pre-descent data. -/
def Iso.symm {D₁ D₂ : SinglePreDatum sq F} (e : D₁.Iso D₂) : D₂.Iso D₁ where
  e := e.e.symm
  comm := by
    rw [e.hom_eq]
    simp only [Iso.symm_hom, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      Functor.map_id, Category.comp_id]

/-- The composite of two isomorphisms of pre-descent data. -/
def Iso.trans {D₁ D₂ D₃ : SinglePreDatum sq F} (e : D₁.Iso D₂) (e' : D₂.Iso D₃) : D₁.Iso D₃ where
  e := e.e ≪≫ e'.e
  comm := by
    simp only [Iso.trans_hom, Functor.map_comp, Category.assoc, e'.comm]
    rw [reassoc_of% e.comm]

/-- An isomorphism of pre-descent data, transported along a strong transformation. -/
def Iso.map {D₁ D₂ : SinglePreDatum sq F} (e : D₁.Iso D₂)
    {G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}} (τ : StrongTrans F G) :
    (D₁.map τ).Iso (D₂.map τ) where
  e := (τ.app (.mk (op X))).toFunctor.mapIso e.e
  comm := by
    dsimp only [Functor.mapIso_hom]
    rw [← τ.mapPullHom_map, ← τ.mapPullHom_map, τ.mapPullHom_comp, τ.mapPullHom_comp, e.comm]

/-- A pre-descent datum isomorphic to one satisfying the two conditions of a descent datum
satisfies them as well. -/
lemma Iso.isDatum {sq₃ : ChosenPullback₃ sq sq sq} {D₁ D₂ : SinglePreDatum sq F}
    (e : D₁.Iso D₂) (h : D₁.IsDatum sq₃) : D₂.IsDatum sq₃ where
  self := by
    rw [e.pull, h.self, Category.id_comp, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]
  comp := by
    rw [e.pull, e.pull, e.pull, ← h.comp]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc (F.map sq₃.p₂.op.toLoc).toFunctor e.e.hom e.e.inv,
      Iso.hom_inv_id, Functor.map_id, Category.id_comp]

variable (D)

/-- The transport along a strong transformation of a pre-descent datum satisfying the two
conditions of a descent datum satisfies them as well. -/
lemma IsDatum.map {sq₃ : ChosenPullback₃ sq sq sq} (h : D.IsDatum sq₃)
    {G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}} (τ : StrongTrans F G) :
    (D.map τ).IsDatum sq₃ where
  self := by rw [map_pull, h.self, τ.mapPullHom_id]
  comp := by rw [map_pull, map_pull, map_pull, τ.mapPullHom_comp, h.comp]

/-- A pre-descent datum satisfying the two conditions, as a descent datum relative to chosen
pullbacks. -/
@[simps]
def toDescentData' {sq₃ : ChosenPullback₃ sq sq sq} (h : D.IsDatum sq₃) :
    F.DescentData' (sqF sq) (sq₃F sq sq₃) where
  obj _ := D.obj
  hom := D.homF
  pullHom'_hom_self _ := h.self
  pullHom'_hom_comp _ _ _ := h.comp

/-- The pre-descent datum underlying a descent datum relative to chosen pullbacks. -/
@[simps]
def ofDescentData' {sq₃ : ChosenPullback₃ sq sq sq}
    (E : F.DescentData' (sqF sq) (sq₃F sq sq₃)) : SinglePreDatum sq F where
  obj := E.obj PUnit.unit
  hom := E.hom PUnit.unit PUnit.unit

/-- The pre-descent datum underlying a descent datum relative to chosen pullbacks satisfies the
two conditions of a descent datum. -/
lemma isDatum_ofDescentData' {sq₃ : ChosenPullback₃ sq sq sq}
    (E : F.DescentData' (sqF sq) (sq₃F sq sq₃)) : (ofDescentData' E).IsDatum sq₃ where
  self := E.pullHom'_hom_self PUnit.unit
  comp := E.pullHom'_hom_comp PUnit.unit PUnit.unit PUnit.unit

/-- An isomorphism of pre-descent data satisfying the two conditions is an isomorphism of
descent data. -/
def Iso.toIso' {sq₃ : ChosenPullback₃ sq sq sq} {D₁ D₂ : SinglePreDatum sq F}
    (e : D₁.Iso D₂) (h₁ : D₁.IsDatum sq₃) (h₂ : D₂.IsDatum sq₃) :
    D₁.toDescentData' h₁ ≅ D₂.toDescentData' h₂ :=
  DescentData'.isoMk (fun _ ↦ e.e) (fun _ _ ↦ e.comm)

/-- The transport of a pre-descent datum along an isomorphism onto its object. -/
@[reducible, simps]
def ofIso (D : SinglePreDatum sq F) {M : F.obj (.mk (op X))} (e : M ≅ D.obj) :
    SinglePreDatum sq F where
  obj := M
  hom := (F.map sq.p₁.op.toLoc).toFunctor.map e.hom ≫ D.hom ≫
    (F.map sq.p₂.op.toLoc).toFunctor.map e.inv

/-- The transport of a pre-descent datum along an isomorphism onto its object is isomorphic to
it. -/
def isoOfIso (D : SinglePreDatum sq F) {M : F.obj (.mk (op X))} (e : M ≅ D.obj) :
    (D.ofIso e).Iso D where
  e := e
  comm := by simp [← Functor.map_comp]

/-- **The canonical pre-descent datum of an object over `S`**: its pullback to `X`, with the
canonical comparison of its two pullbacks to `X ×_S X`. -/
@[reducible]
def can (_sq₃ : ChosenPullback₃ sq sq sq) (M : F.obj (.mk (op S))) : SinglePreDatum sq F where
  obj := (F.map f.op.toLoc).toFunctor.obj M
  hom := (F.mapCompIsoApp f sq.p₁ sq.p sq.hp₁ M).inv ≫ (F.mapCompIsoApp f sq.p₂ sq.p sq.hp₂ M).hom

/-- The morphism of `can sq₃ M` is the composite `p₁^* f^* M ≅ p^* M ≅ p₂^* f^* M` of the
canonical comparison isomorphisms, for `p : X ×_S X ⟶ S`. -/
lemma can_hom (sq₃ : ChosenPullback₃ sq sq sq) (M : F.obj (.mk (op S))) :
    (can sq₃ M).hom = (F.mapCompIsoApp f sq.p₁ sq.p sq.hp₁ M).inv ≫
      (F.mapCompIsoApp f sq.p₂ sq.p sq.hp₂ M).hom := rfl

/-- The canonical pre-descent datum of an object over `S` satisfies the two conditions of a
descent datum. -/
lemma isDatum_can (sq₃ : ChosenPullback₃ sq sq sq) (M : F.obj (.mk (op S))) :
    (can sq₃ M).IsDatum sq₃ :=
  isDatum_ofDescentData' ((DescentData'.fromDescentDataFunctor F (sqF sq) (sq₃F sq sq₃)).obj
    ((F.toDescentData (fun _ : PUnit.{1} ↦ f)).obj M))

/-- The canonical pre-descent datum, transported along a strong transformation. -/
def canMapIso (sq₃ : ChosenPullback₃ sq sq sq)
    {G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}} (τ : StrongTrans F G)
    (M : F.obj (.mk (op S))) :
    ((can sq₃ M).map τ).Iso (can sq₃ ((τ.app (.mk (op S))).toFunctor.obj M)) where
  e := τ.pullIso f M
  comm :=
    (τ.descentDataObjOfObjIso_comm (fun _ : PUnit.{1} ↦ f) M sq.p (i₁ := PUnit.unit)
      (i₂ := PUnit.unit) sq.p₁ sq.p₂ sq.hp₁ sq.hp₂)

/-- An isomorphism of descent data relative to chosen pullbacks, as an isomorphism of the
underlying pre-descent data. -/
def isoOfIso' {sq₃ : ChosenPullback₃ sq sq sq} {E₁ E₂ : F.DescentData' (sqF sq) (sq₃F sq sq₃)}
    (φ : E₁ ≅ E₂) : (ofDescentData' E₁).Iso (ofDescentData' E₂) where
  e := { hom := φ.hom.hom PUnit.unit, inv := φ.inv.hom PUnit.unit,
         hom_inv_id := congrArg (fun ψ ↦ DescentData'.Hom.hom ψ PUnit.unit) φ.hom_inv_id,
         inv_hom_id := congrArg (fun ψ ↦ DescentData'.Hom.hom ψ PUnit.unit) φ.inv_hom_id }
  comm := φ.hom.comm PUnit.unit PUnit.unit

/-- **A morphism of pre-descent data**: a morphism of the objects over `X` compatible with the
morphisms over `X ×_S X`. -/
def IsMor (D₁ D₂ : SinglePreDatum sq F) (φ : D₁.obj ⟶ D₂.obj) : Prop :=
  (F.map sq.p₁.op.toLoc).toFunctor.map φ ≫ D₂.hom = D₁.hom ≫ (F.map sq.p₂.op.toLoc).toFunctor.map φ

/-- A morphism of pre-descent data, conjugated by isomorphisms `i₁ : D₁.Iso D₁'` and
`i₂ : D₂.Iso D₂'`, is a morphism from `D₁'` to `D₂'`. -/
lemma IsMor.of_iso {D₁ D₂ D₁' D₂' : SinglePreDatum sq F} (i₁ : D₁.Iso D₁') (i₂ : D₂.Iso D₂')
    {φ : D₁.obj ⟶ D₂.obj} (h : IsMor D₁ D₂ φ) : IsMor D₁' D₂' (i₁.e.inv ≫ φ ≫ i₂.e.hom) := by
  unfold IsMor at h ⊢
  rw [i₁.hom_eq, i₂.hom_eq]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc _ i₂.e.hom i₂.e.inv, Iso.hom_inv_id, Functor.map_id,
    Category.id_comp, reassoc_of% h]
  simp

/-- If the image of `b` under the component of `τ` at `X` is a morphism of the transported
pre-descent data, then the two sides of the compatibility condition for `b` agree after applying
the component of `τ` at `X ×_S X`. -/
lemma IsMor.map_eq {G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}} (τ : StrongTrans F G)
    {D₁ D₂ : SinglePreDatum sq F} (b : D₁.obj ⟶ D₂.obj)
    (h : IsMor (D₁.map τ) (D₂.map τ) ((τ.app (.mk (op X))).toFunctor.map b)) :
    (τ.app (.mk (op sq.pullback))).toFunctor.map
        ((F.map sq.p₁.op.toLoc).toFunctor.map b ≫ D₂.hom) =
      (τ.app (.mk (op sq.pullback))).toFunctor.map
        (D₁.hom ≫ (F.map sq.p₂.op.toLoc).toFunctor.map b) := by
  unfold IsMor at h
  dsimp only [map] at h
  rw [← τ.mapPullHom_map, ← τ.mapPullHom_map, τ.mapPullHom_comp, τ.mapPullHom_comp] at h
  dsimp only [StrongTrans.mapPullHom] at h
  rwa [cancel_epi, cancel_mono] at h

/-- The component over `X` of a morphism between the descent data of two objects over `S` is a
morphism of their canonical pre-descent data. -/
lemma isMor_can (sq₃ : ChosenPullback₃ sq sq sq) {M M' : F.obj (.mk (op S))}
    (ξ : (F.toDescentData (fun _ : PUnit.{1} ↦ f)).obj M ⟶
      (F.toDescentData (fun _ : PUnit.{1} ↦ f)).obj M') :
    IsMor (can sq₃ M) (can sq₃ M') (ξ.hom PUnit.unit) :=
  ((DescentData'.fromDescentDataFunctor F (sqF sq) (sq₃F sq sq₃)).map ξ).comm PUnit.unit PUnit.unit

/-- A morphism of the canonical pre-descent data is a morphism of descent data. -/
def descentDataHomOfIsMor (sq₃ : ChosenPullback₃ sq sq sq) {M M' : F.obj (.mk (op S))}
    (φ : (can sq₃ M).obj ⟶ (can sq₃ M').obj) (h : IsMor (can sq₃ M) (can sq₃ M') φ) :
    (F.toDescentData (fun _ : PUnit.{1} ↦ f)).obj M ⟶
      (F.toDescentData (fun _ : PUnit.{1} ↦ f)).obj M' :=
  ((DescentData'.descentDataEquivalence F (sqF sq) (sq₃F sq sq₃)).counitIso.app _).inv ≫
    (DescentData'.toDescentDataFunctor F (sqF sq) (sq₃F sq sq₃)).map
      (X := (DescentData'.fromDescentDataFunctor F (sqF sq) (sq₃F sq sq₃)).obj
          ((F.toDescentData (fun _ : PUnit.{1} ↦ f)).obj M))
      (Y := (DescentData'.fromDescentDataFunctor F (sqF sq) (sq₃F sq sq₃)).obj
          ((F.toDescentData (fun _ : PUnit.{1} ↦ f)).obj M'))
      { hom := fun ⟨⟩ ↦ φ, comm := fun ⟨⟩ ⟨⟩ ↦ h } ≫
    ((DescentData'.descentDataEquivalence F (sqF sq) (sq₃F sq sq₃)).counitIso.app _).hom

/-- The component over `X` of `descentDataHomOfIsMor sq₃ φ h` is `φ`. -/
@[simp]
lemma descentDataHomOfIsMor_hom (sq₃ : ChosenPullback₃ sq sq sq) {M M' : F.obj (.mk (op S))}
    (φ : (can sq₃ M).obj ⟶ (can sq₃ M').obj) (h : IsMor (can sq₃ M) (can sq₃ M') φ) :
    (descentDataHomOfIsMor sq₃ φ h).hom PUnit.unit = φ := by
  change 𝟙 _ ≫ φ ≫ 𝟙 _ = φ
  simp

end SinglePreDatum

end PreDatum

/-! ### Iterated transport of pre-descent data -/

namespace SinglePreDatum

variable {X S : C} {f : X ⟶ S} {sq : ChosenPullback f f}

/-- The transport of a pre-descent datum along the `j`-th iterate of an endo-transformation. -/
@[reducible, simps]
def iterMap (D : SinglePreDatum sq V) (Φ : StrongTrans V V) (j : ℕ) : SinglePreDatum sq V where
  obj := (Φ.iterFunctor X j).obj D.obj
  hom := (Φ.pullIsoIter sq.p₁ D.obj j).inv ≫ (Φ.iterFunctor sq.pullback j).map D.hom ≫
    (Φ.pullIsoIter sq.p₂ D.obj j).hom

/-- The morphism of the `(j + 1)`-st iterated transport is that of the transport along `Φ` of the
`j`-th iterated transport. -/
lemma iterMap_succ_hom (D : SinglePreDatum sq V) (Φ : StrongTrans V V) (j : ℕ) :
    (D.iterMap Φ (j + 1)).hom = ((D.iterMap Φ j).map Φ).hom := by
  dsimp only [iterMap, map]
  rw [StrongTrans.pullIsoIter_succ_hom, StrongTrans.pullIsoIter_succ_inv,
    StrongTrans.mapPullHom]
  simp only [Functor.map_comp, Category.assoc]
  exact Category.assoc _ _ _

/-- **The pullbacks of an iterated transport** are the iterates of the pullbacks, conjugated by
the naturality isomorphisms of the iterate. -/
lemma iterMap_pull (D : SinglePreDatum sq V) (Φ : StrongTrans V V) {Y : C} (q : Y ⟶ S)
    (f₁ f₂ : Y ⟶ X) (hf₁ : f₁ ≫ f = q) (hf₂ : f₂ ≫ f = q) :
    ∀ j : ℕ, (D.iterMap Φ j).pull q f₁ f₂ hf₁ hf₂ =
      (Φ.pullIsoIter f₁ D.obj j).inv ≫ (Φ.iterFunctor Y j).map (D.pull q f₁ f₂ hf₁ hf₂) ≫
        (Φ.pullIsoIter f₂ D.obj j).hom
  | 0 => by
      rw [pull_eq_pullHom, pull_eq_pullHom]
      simp [StrongTrans.pullIsoIter_zero]
  | j + 1 => by
      have e : (D.iterMap Φ (j + 1)).pull q f₁ f₂ hf₁ hf₂ =
          ((D.iterMap Φ j).map Φ).pull q f₁ f₂ hf₁ hf₂ := by
        rw [pull_eq_pullHom, pull_eq_pullHom, iterMap_succ_hom]
        rfl
      rw [e, map_pull, iterMap_pull D Φ q f₁ f₂ hf₁ hf₂ j, StrongTrans.mapPullHom,
        StrongTrans.pullIsoIter_succ_hom, StrongTrans.pullIsoIter_succ_inv]
      simp only [Functor.map_comp, Category.assoc]
      exact (Category.assoc _ _ _).symm

/-- If the `j`-th iterate of `Φ` identifies the two sides of each of the two conditions of a
descent datum for `D`, then the `j`-th iterated transport of `D` satisfies these conditions. -/
lemma isDatum_iterMap {sq₃ : ChosenPullback₃ sq sq sq} (D : SinglePreDatum sq V)
    (Φ : StrongTrans V V) (j : ℕ)
    (hself : (Φ.iterFunctor X j).map (D.pull f (𝟙 X) (𝟙 X) (Category.id_comp f)
      (Category.id_comp f)) = (Φ.iterFunctor X j).map (𝟙 _))
    (hcomp : (Φ.iterFunctor sq₃.pullback j).map
        (D.pull sq₃.p sq₃.p₁ sq₃.p₂ sq₃.w₁ sq₃.w₂ ≫ D.pull sq₃.p sq₃.p₂ sq₃.p₃ sq₃.w₂ sq₃.w₃) =
      (Φ.iterFunctor sq₃.pullback j).map (D.pull sq₃.p sq₃.p₁ sq₃.p₃ sq₃.w₁ sq₃.w₃)) :
    (D.iterMap Φ j).IsDatum sq₃ where
  self := by
    rw [iterMap_pull, hself, Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  comp := by
    rw [iterMap_pull, iterMap_pull, iterMap_pull, ← hcomp]
    simp

/-- If the `j`-th iterate of `Φ` identifies the two sides of the compatibility condition for `b`,
then the `j`-th iterate of `b` is a morphism of the `j`-th iterated transports. -/
lemma IsMor.iterMap (Φ : StrongTrans V V) {D₁ D₂ : SinglePreDatum sq V} (b : D₁.obj ⟶ D₂.obj)
    (j : ℕ)
    (h : (Φ.iterFunctor sq.pullback j).map ((V.map sq.p₁.op.toLoc).toFunctor.map b ≫ D₂.hom) =
      (Φ.iterFunctor sq.pullback j).map (D₁.hom ≫ (V.map sq.p₂.op.toLoc).toFunctor.map b)) :
    IsMor (D₁.iterMap Φ j) (D₂.iterMap Φ j) ((Φ.iterFunctor X j).map b) := by
  unfold IsMor
  dsimp only [SinglePreDatum.iterMap]
  have n₁ := Φ.pullIsoIter_naturality sq.p₁ b j
  have n₂ := Φ.pullIsoIter_naturality sq.p₂ b j
  have n₁' : (V.map sq.p₁.op.toLoc).toFunctor.map ((Φ.iterFunctor X j).map b) ≫
      (Φ.pullIsoIter sq.p₁ D₂.obj j).inv = (Φ.pullIsoIter sq.p₁ D₁.obj j).inv ≫
        (Φ.iterFunctor sq.pullback j).map ((V.map sq.p₁.op.toLoc).toFunctor.map b) := by
    rw [Iso.comp_inv_eq, Category.assoc, n₁, Iso.inv_hom_id_assoc]
  rw [reassoc_of% n₁', ← Functor.map_comp_assoc, h, Functor.map_comp_assoc, n₂]
  simp

/-- Equal pre-descent data are isomorphic. -/
def Iso.ofEq {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}} {D₁ D₂ : SinglePreDatum sq F}
    (h : D₁ = D₂) : D₁.Iso D₂ where
  e := eqToIso (congrArg SinglePreDatum.obj h)
  comm := by subst h; simp

/-- The `(j + 1)`-st iterated transport of a pre-descent datum is the transport along `Φ` of the
`j`-th one. -/
lemma iterMap_succ (D : SinglePreDatum sq V) (Φ : StrongTrans V V) (j : ℕ) :
    D.iterMap Φ (j + 1) = (D.iterMap Φ j).map Φ :=
  congrArg (SinglePreDatum.mk ((D.iterMap Φ (j + 1)).obj)) (iterMap_succ_hom D Φ j)

/-- An isomorphism of pre-descent data, transported along an iterate. -/
def Iso.iterMap (Φ : StrongTrans V V) {D₁ D₂ : SinglePreDatum sq V} (i : D₁.Iso D₂) (j : ℕ) :
    (D₁.iterMap Φ j).Iso (D₂.iterMap Φ j) where
  e := (Φ.iterFunctor X j).mapIso i.e
  comm := IsMor.iterMap Φ i.e.hom j (congrArg _ i.comm)

/-- The iterated transport of the canonical pre-descent datum of an object is the canonical
pre-descent datum of its iterate. -/
def canIterIso (sq₃ : ChosenPullback₃ sq sq sq) (Φ : StrongTrans V V) (M : V.obj (.mk (op S))) :
    ∀ j : ℕ, ((can sq₃ M).iterMap Φ j).Iso (can sq₃ ((Φ.iterFunctor S j).obj M))
  | 0 => { e := Φ.pullIsoIter f M 0, comm := by
            simp [StrongTrans.pullIsoIter, iterMap] }
  | j + 1 =>
      ((Iso.ofEq (iterMap_succ (can sq₃ M) Φ j)).trans
        ((canIterIso sq₃ Φ M j).map Φ)).trans
        (canMapIso sq₃ Φ ((Φ.iterFunctor S j).obj M))

/-- The isomorphism of objects underlying `canIterIso sq₃ Φ M j` is the naturality isomorphism
`Φ.pullIsoIter f M j` of the iterate. -/
lemma canIterIso_e (sq₃ : ChosenPullback₃ sq sq sq) (Φ : StrongTrans V V)
    (M : V.obj (.mk (op S))) : ∀ j : ℕ, (canIterIso sq₃ Φ M j).e = Φ.pullIsoIter f M j
  | 0 => rfl
  | j + 1 => by
      ext
      change ((Iso.ofEq (iterMap_succ (can sq₃ M) Φ j)).e.hom ≫
        (Φ.app (.mk (op X))).toFunctor.map (canIterIso sq₃ Φ M j).e.hom) ≫
          (Φ.pullIso f ((Φ.iterFunctor S j).obj M)).hom = _
      rw [canIterIso_e sq₃ Φ M j, StrongTrans.pullIsoIter_succ_hom]
      exact congrArg (· ≫ _) (Category.id_comp _)

/-- The conditions of a descent datum, read through a strong transformation. -/
lemma IsDatum.map_eq {sq₃ : ChosenPullback₃ sq sq sq} (D : SinglePreDatum sq V)
    (τ : StrongTrans V P) (h : (D.map τ).IsDatum sq₃) :
    (τ.app (.mk (op X))).toFunctor.map (D.pull f (𝟙 X) (𝟙 X) (Category.id_comp f)
        (Category.id_comp f)) = (τ.app (.mk (op X))).toFunctor.map (𝟙 _) ∧
      (τ.app (.mk (op sq₃.pullback))).toFunctor.map
          (D.pull sq₃.p sq₃.p₁ sq₃.p₂ sq₃.w₁ sq₃.w₂ ≫ D.pull sq₃.p sq₃.p₂ sq₃.p₃ sq₃.w₂ sq₃.w₃) =
        (τ.app (.mk (op sq₃.pullback))).toFunctor.map
          (D.pull sq₃.p sq₃.p₁ sq₃.p₃ sq₃.w₁ sq₃.w₃) := by
  have h1 := h.self
  have h2 := h.comp
  rw [map_pull] at h1
  rw [map_pull, map_pull, map_pull, τ.mapPullHom_comp] at h2
  rw [← τ.mapPullHom_id] at h1
  dsimp only [StrongTrans.mapPullHom] at h1 h2
  rw [cancel_epi, cancel_mono] at h1 h2
  exact ⟨h1, h2⟩

end SinglePreDatum

/-! ### The stage data -/

variable (V P) in
/-- **The data of a pseudo-cocone of strong transformations**: an endo-transformation `Φ` of `V`,
strong transformations `σ n : V ⟶ P`, and natural isomorphisms `Φ_U ⋙ (σ (n + 1))_U ≅ (σ n)_U`
compatible with the naturality isomorphisms. -/
structure StageColimitData where
  /-- the endo-transformation -/
  Φ : StrongTrans V V
  /-- the stage transformations -/
  σ : ℕ → StrongTrans V P
  /-- the comparison of consecutive stages -/
  μ : ∀ (n : ℕ) (U : C), (Φ.app (.mk (op U))).toFunctor ⋙ ((σ (n + 1)).app (.mk (op U))).toFunctor ≅
    ((σ n).app (.mk (op U))).toFunctor
  /-- the comparison is a modification -/
  pullIso_μ : ∀ (n : ℕ) {X Y : C} (h : Y ⟶ X) (M : V.obj (.mk (op X))),
    ((σ (n + 1)).app (.mk (op Y))).toFunctor.map (Φ.pullIso h M).hom ≫
        ((σ (n + 1)).pullIso h ((Φ.app (.mk (op X))).toFunctor.obj M)).hom ≫
        (P.map h.op.toLoc).toFunctor.map ((μ n X).hom.app M) =
      (μ n Y).hom.app ((V.map h.op.toLoc).toFunctor.obj M) ≫ ((σ n).pullIso h M).hom

namespace StageColimitData

variable (𝔇 : StageColimitData V P)

/-- The pseudo-cocone at an object. -/
abbrev pc (U : C) :
    EndoColim.Pseudococone (𝔇.Φ.app (.mk (op U))).toFunctor (P.obj (.mk (op U))) where
  stage n := ((𝔇.σ n).app (.mk (op U))).toFunctor
  compat n := 𝔇.μ n U

/-- The compatibility `pullIso_μ` of the comparison isomorphisms with the naturality isomorphisms,
iterated: the same compatibility for the isomorphisms `iterObjIso n k` and `pullIsoIter`. -/
lemma iterObjIso_pullIso (n : ℕ) {X Y : C} (h : Y ⟶ X) (M : V.obj (.mk (op X))) :
    ∀ k : ℕ, ((𝔇.σ (n + k)).app (.mk (op Y))).toFunctor.map (𝔇.Φ.pullIsoIter h M k).hom ≫
        ((𝔇.σ (n + k)).pullIso h ((𝔇.Φ.iterFunctor X k).obj M)).hom ≫
        (P.map h.op.toLoc).toFunctor.map ((𝔇.pc X).iterObjIso n k M).hom =
      ((𝔇.pc Y).iterObjIso n k ((V.map h.op.toLoc).toFunctor.obj M)).hom ≫
        ((𝔇.σ n).pullIso h M).hom
  | 0 => by
      simp [StrongTrans.pullIsoIter, EndoColim.Pseudococone.iterObjIso]
  | k + 1 => by
      have ih := iterObjIso_pullIso n h M k
      have hmod := 𝔇.pullIso_μ (n + k) h ((𝔇.Φ.iterFunctor X k).obj M)
      have hnat := (𝔇.μ (n + k) Y).hom.naturality (𝔇.Φ.pullIsoIter h M k).hom
      rw [Functor.comp_map] at hnat
      change ((𝔇.σ (n + k + 1)).app (.mk (op Y))).toFunctor.map
            ((𝔇.Φ.app (.mk (op Y))).toFunctor.map (𝔇.Φ.pullIsoIter h M k).hom ≫
              (𝔇.Φ.pullIso h ((𝔇.Φ.iterFunctor X k).obj M)).hom) ≫
          ((𝔇.σ (n + k + 1)).pullIso h
            ((𝔇.Φ.app (.mk (op X))).toFunctor.obj ((𝔇.Φ.iterFunctor X k).obj M))).hom ≫
          (P.map h.op.toLoc).toFunctor.map
            ((𝔇.μ (n + k) X).hom.app ((𝔇.Φ.iterFunctor X k).obj M) ≫
              ((𝔇.pc X).iterObjIso n k M).hom) =
        ((𝔇.μ (n + k) Y).hom.app ((𝔇.Φ.iterFunctor Y k).obj ((V.map h.op.toLoc).toFunctor.obj M)) ≫
          ((𝔇.pc Y).iterObjIso n k ((V.map h.op.toLoc).toFunctor.obj M)).hom) ≫
          ((𝔇.σ n).pullIso h M).hom
      rw [Functor.map_comp, Functor.map_comp]
      simp only [Category.assoc]
      rw [reassoc_of% hmod, reassoc_of% hnat, ih]

variable {X S : C} {f : X ⟶ S} {sq : ChosenPullback f f}

/-- **Raising a pre-descent datum along the endo-transformation does not change its stage
image**, up to the comparison of the stages. -/
def iterMapIso (E : SinglePreDatum sq V) (n j : ℕ) :
    ((E.iterMap 𝔇.Φ j).map (𝔇.σ (n + j))).Iso (E.map (𝔇.σ n)) where
  e := (𝔇.pc X).iterObjIso n j E.obj
  comm := by
    have h₁ := 𝔇.iterObjIso_pullIso n sq.p₁ E.obj j
    have h₂ := 𝔇.iterObjIso_pullIso n sq.p₂ E.obj j
    have hn := (𝔇.pc sq.pullback).iterObjIso_hom_naturality n j E.hom
    dsimp only [SinglePreDatum.map, SinglePreDatum.iterMap, StrongTrans.mapPullHom] at h₁ h₂ hn ⊢
    simp only [Functor.map_comp, Category.assoc]
    rw [h₂, reassoc_of% hn]
    rw [← cancel_epi ((𝔇.σ (n + j)).pullIso sq.p₁ ((𝔇.Φ.iterFunctor X j).obj E.obj)).hom,
      Iso.hom_inv_id_assoc, ← cancel_epi (((𝔇.σ (n + j)).app (.mk (op sq.pullback))).toFunctor.map
        (𝔇.Φ.pullIsoIter sq.p₁ E.obj j).hom), ← Functor.map_comp_assoc, Iso.hom_inv_id,
      Functor.map_id, Category.id_comp, reassoc_of% h₁, Iso.hom_inv_id_assoc]

/-- **A morphism between stage images over `X ×_S X`, induced at a twist, gives a pre-descent
datum of `V` whose stage image is the given one.** -/
def mapAtIso (n k : ℕ) (A : V.obj (.mk (op X)))
    (m : (P.map sq.p₁.op.toLoc).toFunctor.obj (((𝔇.σ n).app (.mk (op X))).toFunctor.obj A) ⟶
      (P.map sq.p₂.op.toLoc).toFunctor.obj (((𝔇.σ n).app (.mk (op X))).toFunctor.obj A))
    (a : (𝔇.Φ.iterFunctor sq.pullback k).obj ((V.map sq.p₁.op.toLoc).toFunctor.obj A) ⟶
      (𝔇.Φ.iterFunctor sq.pullback k).obj ((V.map sq.p₂.op.toLoc).toFunctor.obj A))
    (ha : (𝔇.pc sq.pullback).mapAt n n k k rfl a =
      ((𝔇.σ n).pullIso sq.p₁ A).hom ≫ m ≫ ((𝔇.σ n).pullIso sq.p₂ A).inv) :
    (SinglePreDatum.map (sq := sq) ⟨(𝔇.Φ.iterFunctor X k).obj A,
        (𝔇.Φ.pullIsoIter sq.p₁ A k).inv ≫ a ≫ (𝔇.Φ.pullIsoIter sq.p₂ A k).hom⟩
      (𝔇.σ (n + k))).Iso ⟨((𝔇.σ n).app (.mk (op X))).toFunctor.obj A, m⟩ where
  e := (𝔇.pc X).iterObjIso n k A
  comm := by
    have h₁ := 𝔇.iterObjIso_pullIso n sq.p₁ A k
    have h₂ := 𝔇.iterObjIso_pullIso n sq.p₂ A k
    rw [EndoColim.Pseudococone.mapAt_self] at ha
    have ha' : ((𝔇.σ (n + k)).app (.mk (op sq.pullback))).toFunctor.map a ≫
        ((𝔇.pc sq.pullback).iterObjIso n k ((V.map sq.p₂.op.toLoc).toFunctor.obj A)).hom =
        ((𝔇.pc sq.pullback).iterObjIso n k ((V.map sq.p₁.op.toLoc).toFunctor.obj A)).hom ≫
          ((𝔇.σ n).pullIso sq.p₁ A).hom ≫ m ≫ ((𝔇.σ n).pullIso sq.p₂ A).inv := by
      rwa [← Iso.inv_comp_eq]
    dsimp only [SinglePreDatum.map, StrongTrans.mapPullHom]
    simp only [Functor.map_comp, Category.assoc]
    rw [h₂, reassoc_of% ha', Iso.inv_hom_id, Category.comp_id, ← reassoc_of% h₁]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Functor.map_id,
      Category.id_comp]

/-- **Essential surjectivity at the level of pre-descent data**: every descent datum of `P`
relative to `{f}` is isomorphic to the stage image of a descent datum of `V`. -/
theorem exists_iso_map (sq₃ : ChosenPullback₃ sq sq sq)
    (hX : (𝔇.pc X).IsColimitPresentation) (hX₂ : (𝔇.pc sq.pullback).IsColimitPresentation)
    (hX₃ : (𝔇.pc sq₃.pullback).IsColimitPresentation)
    (D : SinglePreDatum sq P) (hD : D.IsDatum sq₃) :
    ∃ (N : ℕ) (E : SinglePreDatum sq V), E.IsDatum sq₃ ∧ Nonempty ((E.map (𝔇.σ N)).Iso D) := by
  obtain ⟨n, A, ⟨e⟩⟩ := hX.exists_iso D.obj
  let D₁ := D.ofIso e
  have hD₁ : D₁.IsDatum sq₃ := (D.isoOfIso e).symm.isDatum hD
  obtain ⟨k, a, ha⟩ := hX₂.exists_mapAt n _ _
    (((𝔇.σ n).pullIso sq.p₁ A).hom ≫ D₁.hom ≫ ((𝔇.σ n).pullIso sq.p₂ A).inv)
  let E₀ : SinglePreDatum sq V := ⟨(𝔇.Φ.iterFunctor X k).obj A,
    (𝔇.Φ.pullIsoIter sq.p₁ A k).inv ≫ a ≫ (𝔇.Φ.pullIsoIter sq.p₂ A k).hom⟩
  let i₁ : (E₀.map (𝔇.σ (n + k))).Iso D₁ := 𝔇.mapAtIso n k A D₁.hom a ha
  obtain ⟨hself, hcomp⟩ := SinglePreDatum.IsDatum.map_eq E₀ (𝔇.σ (n + k)) (i₁.symm.isDatum hD₁)
  obtain ⟨j₁, hj₁⟩ := hX.exists_map_eq (n + k) _ _ _ _ hself
  obtain ⟨j₂, hj₂⟩ := hX₃.exists_map_eq (n + k) _ _ _ _ hcomp
  have hE : (E₀.iterMap 𝔇.Φ (j₁ + j₂)).IsDatum sq₃ :=
    E₀.isDatum_iterMap 𝔇.Φ (j₁ + j₂)
      (Functor.endoIter_map_eq_of_le _ hj₁ _ (Nat.le_add_right _ _))
      (Functor.endoIter_map_eq_of_le _ hj₂ _ (Nat.le_add_left _ _))
  exact ⟨n + k + (j₁ + j₂), E₀.iterMap 𝔇.Φ (j₁ + j₂), hE,
    ⟨((𝔇.iterMapIso E₀ (n + k) (j₁ + j₂)).trans i₁).trans (D.isoOfIso e)⟩⟩

/-- The descent-data functor of a one-element family is an equivalence as soon as the
pseudofunctor is a stack for the presieve it generates. -/
lemma isEquivalence_toDescentData_of_isStackFor
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    (h : F.IsStackFor (Presieve.singleton f)) :
    (F.toDescentData (fun _ : PUnit.{1} ↦ f)).IsEquivalence := by
  rwa [← Pseudofunctor.isStackFor_ofArrows_iff, Presieve.ofArrows_pUnit]

/-- An isomorphism of the canonical pre-descent data of two objects with the pre-descent datum of
a descent datum is an isomorphism of descent data. -/
def toDescentDataIsoOfIso {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    (sq₃ : ChosenPullback₃ sq sq sq) (H : F.obj (.mk (op S)))
    (D : F.DescentData (fun _ : PUnit.{1} ↦ f))
    (ch : (SinglePreDatum.can sq₃ H).Iso (SinglePreDatum.ofDescentData'
      ((DescentData'.fromDescentDataFunctor F (sqF sq) (sq₃F sq sq₃)).obj D))) :
    (F.toDescentData (fun _ : PUnit.{1} ↦ f)).obj H ≅ D :=
  ((DescentData'.descentDataEquivalence F (sqF sq) (sq₃F sq sq₃)).counitIso.app _).symm ≪≫
    (DescentData'.toDescentDataFunctor F (sqF sq) (sq₃F sq sq₃)).mapIso
      (DescentData'.isoMk
        (D₁ := (DescentData'.fromDescentDataFunctor F (sqF sq) (sq₃F sq sq₃)).obj
          ((F.toDescentData (fun _ : PUnit.{1} ↦ f)).obj H))
        (D₂ := (DescentData'.fromDescentDataFunctor F (sqF sq) (sq₃F sq sq₃)).obj D)
        (fun ⟨⟩ ↦ ch.e) (fun ⟨⟩ ⟨⟩ ↦ ch.comm)) ≪≫
    (DescentData'.descentDataEquivalence F (sqF sq) (sq₃F sq sq₃)).counitIso.app D

/-- **Effectivity of descent along `{f}` passes from `V` to `P`.** -/
theorem essSurj_toDescentData (sq₃ : ChosenPullback₃ sq sq sq)
    (hX : (𝔇.pc X).IsColimitPresentation) (hX₂ : (𝔇.pc sq.pullback).IsColimitPresentation)
    (hX₃ : (𝔇.pc sq₃.pullback).IsColimitPresentation)
    (hV : V.IsStackFor (Presieve.singleton f)) :
    (P.toDescentData (fun _ : PUnit.{1} ↦ f)).EssSurj := by
  have hVeq := isEquivalence_toDescentData_of_isStackFor hV
  refine ⟨fun D ↦ ?_⟩
  let E' := (DescentData'.fromDescentDataFunctor P (sqF sq) (sq₃F sq sq₃)).obj D
  obtain ⟨N, E, hE, ⟨i⟩⟩ := 𝔇.exists_iso_map sq₃ hX hX₂ hX₃
    (SinglePreDatum.ofDescentData' E') (SinglePreDatum.isDatum_ofDescentData' E')
  let Ev := (DescentData'.toDescentDataFunctor V (sqF sq) (sq₃F sq sq₃)).obj (E.toDescentData' hE)
  let G := (V.toDescentData (fun _ : PUnit.{1} ↦ f)).objPreimage Ev
  let φ : (DescentData'.fromDescentDataFunctor V (sqF sq) (sq₃F sq sq₃)).obj
      ((V.toDescentData (fun _ : PUnit.{1} ↦ f)).obj G) ≅ E.toDescentData' hE :=
    (DescentData'.fromDescentDataFunctor V (sqF sq) (sq₃F sq sq₃)).mapIso
      ((V.toDescentData (fun _ : PUnit.{1} ↦ f)).objObjPreimageIso Ev) ≪≫
      ((DescentData'.descentDataEquivalence V (sqF sq) (sq₃F sq sq₃)).unitIso.app _).symm
  let jV : (SinglePreDatum.can sq₃ G).Iso E := SinglePreDatum.isoOfIso' φ
  let H := ((𝔇.σ N).app (.mk (op S))).toFunctor.obj G
  let ch : (SinglePreDatum.can sq₃ H).Iso (SinglePreDatum.ofDescentData' E') :=
    (SinglePreDatum.canMapIso sq₃ (𝔇.σ N) G).symm.trans ((jV.map (𝔇.σ N)).trans i)
  exact ⟨H, ⟨toDescentDataIsoOfIso sq₃ H D ch⟩⟩

/-- Two objects of the summit are stage images at one common stage. -/
lemma exists_common_stage {U : C} (hU : (𝔇.pc U).IsColimitPresentation)
    (M M' : P.obj (.mk (op U))) :
    ∃ (n : ℕ) (A A' : V.obj (.mk (op U))),
      Nonempty (((𝔇.σ n).app (.mk (op U))).toFunctor.obj A ≅ M) ∧
      Nonempty (((𝔇.σ n).app (.mk (op U))).toFunctor.obj A' ≅ M') := by
  obtain ⟨n, A, ⟨e⟩⟩ := hU.exists_iso M
  obtain ⟨n', A', ⟨e'⟩⟩ := hU.exists_iso M'
  have up : ∀ {m : ℕ} {A : V.obj (.mk (op U))} {M : P.obj (.mk (op U))}
      (_ : ((𝔇.σ m).app (.mk (op U))).toFunctor.obj A ≅ M) (N : ℕ), m ≤ N →
      ∃ A' : V.obj (.mk (op U)), Nonempty (((𝔇.σ N).app (.mk (op U))).toFunctor.obj A' ≅ M) := by
    intro m A M e N hmN
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmN
    exact ⟨(𝔇.Φ.iterFunctor U j).obj A, ⟨(𝔇.pc U).iterObjIso m j A ≪≫ e⟩⟩
  obtain ⟨A₁, h₁⟩ := up e _ (le_max_left n n')
  obtain ⟨A₂, h₂⟩ := up e' _ (le_max_right n n')
  exact ⟨_, A₁, A₂, h₁, h₂⟩

/-- **Descent of morphisms along `{f}`, the separatedness half, passes from `V` to `P`.** -/
theorem map_injective_of_isColimitPresentation
    (hS : (𝔇.pc S).IsColimitPresentation) (hX : (𝔇.pc X).IsColimitPresentation)
    (hV : ∀ {A A' : V.obj (.mk (op S))} (a a' : A ⟶ A'),
      (V.map f.op.toLoc).toFunctor.map a = (V.map f.op.toLoc).toFunctor.map a' → a = a')
    {M M' : P.obj (.mk (op S))} (m m' : M ⟶ M')
    (h : (P.map f.op.toLoc).toFunctor.map m = (P.map f.op.toLoc).toFunctor.map m') : m = m' := by
  obtain ⟨n, A, A', ⟨e⟩, ⟨e'⟩⟩ := 𝔇.exists_common_stage hS M M'
  suffices key : ∀ u u' : ((𝔇.σ n).app (.mk (op S))).toFunctor.obj A ⟶
      ((𝔇.σ n).app (.mk (op S))).toFunctor.obj A',
      (P.map f.op.toLoc).toFunctor.map u = (P.map f.op.toLoc).toFunctor.map u' → u = u' by
    simpa using key (e.hom ≫ m ≫ e'.inv) (e.hom ≫ m' ≫ e'.inv) (by simp [h])
  intro u u' hu
  obtain ⟨k₁, a₁, ha₁⟩ := hS.exists_mapAt n A A' u
  obtain ⟨k₂, a₂, ha₂⟩ := hS.exists_mapAt n A A' u'
  obtain ⟨k, hk₁, hk₂⟩ : ∃ k, k₁ ≤ k ∧ k₂ ≤ k := ⟨max k₁ k₂, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨b₁, hb₁⟩ := (𝔇.pc S).mapAt_le n k₁ a₁ k hk₁
  obtain ⟨b₂, hb₂⟩ := (𝔇.pc S).mapAt_le n k₂ a₂ k hk₂
  rw [← ha₁, ← hb₁, ← ha₂, ← hb₂, EndoColim.Pseudococone.mapAt_self,
    EndoColim.Pseudococone.mapAt_self] at hu ⊢
  simp only [Functor.map_comp, cancel_epi, cancel_mono] at hu
  have h₁ := ((𝔇.σ (n + k)).pullIso_naturality f b₁)
  have h₂ := ((𝔇.σ (n + k)).pullIso_naturality f b₂)
  have hσ : ((𝔇.σ (n + k)).app (.mk (op X))).toFunctor.map ((V.map f.op.toLoc).toFunctor.map b₁) =
      ((𝔇.σ (n + k)).app (.mk (op X))).toFunctor.map ((V.map f.op.toLoc).toFunctor.map b₂) := by
    rw [← cancel_mono ((𝔇.σ (n + k)).pullIso f _).hom, h₁, h₂]
    exact congrArg _ hu
  obtain ⟨j, hj⟩ := hX.exists_map_eq (n + k) _ _ _ _ hσ
  have hj' := congrArg (fun t ↦ t ≫ (𝔇.Φ.pullIsoIter f _ j).hom) hj
  rw [𝔇.Φ.pullIsoIter_naturality, 𝔇.Φ.pullIsoIter_naturality, cancel_epi] at hj'
  have hb := hV _ _ hj'
  have n₁ := (𝔇.pc S).iterObjIso_hom_naturality (n + k) j b₁
  have n₂ := (𝔇.pc S).iterObjIso_hom_naturality (n + k) j b₂
  have : ((𝔇.σ (n + k)).app (.mk (op S))).toFunctor.map b₁ =
      ((𝔇.σ (n + k)).app (.mk (op S))).toFunctor.map b₂ := by
    rw [← cancel_epi ((𝔇.pc S).iterObjIso (n + k) j _).hom]
    change _ ≫ (EndoColim.Pseudococone.stage _ (n + k)).map b₁ = _ ≫
      (EndoColim.Pseudococone.stage _ (n + k)).map b₂
    rw [← n₁, ← n₂, hb]
  rw [this]

/-- **A morphism induced at a twist, pulled back along `f`**, in terms of the pullback of the
morphism it is induced by. -/
lemma map_mapAt_pullback (N K : ℕ) {Z Z' : V.obj (.mk (op S))}
    (x : ((𝔇.σ (N + K)).app (.mk (op S))).toFunctor.obj ((𝔇.Φ.iterFunctor S K).obj Z) ⟶
      ((𝔇.σ (N + K)).app (.mk (op S))).toFunctor.obj ((𝔇.Φ.iterFunctor S K).obj Z')) :
    (P.map f.op.toLoc).toFunctor.map
        (((𝔇.pc S).iterObjIso N K Z).inv ≫ x ≫ ((𝔇.pc S).iterObjIso N K Z').hom) =
      ((𝔇.σ N).pullIso f Z).inv ≫ ((𝔇.pc X).iterObjIso N K _).inv ≫
        ((𝔇.σ (N + K)).app (.mk (op X))).toFunctor.map (𝔇.Φ.pullIsoIter f Z K).hom ≫
        ((𝔇.σ (N + K)).pullIso f _).hom ≫ (P.map f.op.toLoc).toFunctor.map x ≫
        ((𝔇.σ (N + K)).pullIso f _).inv ≫
        ((𝔇.σ (N + K)).app (.mk (op X))).toFunctor.map (𝔇.Φ.pullIsoIter f Z' K).inv ≫
        ((𝔇.pc X).iterObjIso N K _).hom ≫ ((𝔇.σ N).pullIso f Z').hom := by
  have h := 𝔇.iterObjIso_pullIso N f Z K
  have h' := 𝔇.iterObjIso_pullIso N f Z' K
  have hi : (P.map f.op.toLoc).toFunctor.map ((𝔇.pc S).iterObjIso N K Z).inv =
      ((𝔇.σ N).pullIso f Z).inv ≫ ((𝔇.pc X).iterObjIso N K _).inv ≫
        ((𝔇.σ (N + K)).app (.mk (op X))).toFunctor.map (𝔇.Φ.pullIsoIter f Z K).hom ≫
        ((𝔇.σ (N + K)).pullIso f _).hom := by
    rw [← cancel_mono ((P.map f.op.toLoc).toFunctor.map ((𝔇.pc S).iterObjIso N K Z).hom),
      ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]
    simp only [Category.assoc]
    rw [h]
    simp
  have hh : (P.map f.op.toLoc).toFunctor.map ((𝔇.pc S).iterObjIso N K Z').hom =
      ((𝔇.σ (N + K)).pullIso f _).inv ≫
        ((𝔇.σ (N + K)).app (.mk (op X))).toFunctor.map (𝔇.Φ.pullIsoIter f Z' K).inv ≫
        ((𝔇.pc X).iterObjIso N K _).hom ≫ ((𝔇.σ N).pullIso f Z').hom := by
    rw [← h']
    simp
  rw [Functor.map_comp, Functor.map_comp, hi, hh]
  simp only [Category.assoc]

/-- **Descent of morphisms along `{f}`, the gluing half, passes from `V` to `P`.** -/
theorem exists_map_eq_of_isMor (sq₃ : ChosenPullback₃ sq sq sq)
    (hS : (𝔇.pc S).IsColimitPresentation) (hX : (𝔇.pc X).IsColimitPresentation)
    (hX₂ : (𝔇.pc sq.pullback).IsColimitPresentation)
    (hV : ∀ {A A' : V.obj (.mk (op S))} (c : (V.map f.op.toLoc).toFunctor.obj A ⟶
        (V.map f.op.toLoc).toFunctor.obj A'),
      SinglePreDatum.IsMor (SinglePreDatum.can sq₃ A) (SinglePreDatum.can sq₃ A') c →
        ∃ w : A ⟶ A', (V.map f.op.toLoc).toFunctor.map w = c)
    {M M' : P.obj (.mk (op S))} (φ : (P.map f.op.toLoc).toFunctor.obj M ⟶
      (P.map f.op.toLoc).toFunctor.obj M')
    (hφ : SinglePreDatum.IsMor (SinglePreDatum.can sq₃ M) (SinglePreDatum.can sq₃ M') φ) :
    ∃ m : M ⟶ M', (P.map f.op.toLoc).toFunctor.map m = φ := by
  obtain ⟨n, A, A', ⟨e⟩, ⟨e'⟩⟩ := 𝔇.exists_common_stage hS M M'
  let iso : ∀ {N N' : P.obj (.mk (op S))}, (N ≅ N') →
      (SinglePreDatum.can sq₃ N).Iso (SinglePreDatum.can sq₃ N') := fun i ↦
    SinglePreDatum.isoOfIso' ((DescentData'.fromDescentDataFunctor P (sqF sq) (sq₃F sq sq₃)).mapIso
      ((P.toDescentData (fun _ : PUnit.{1} ↦ f)).mapIso i))
  let iA := iso e.symm
  let iA' := iso e'.symm
  let jA := (SinglePreDatum.canMapIso sq₃ (𝔇.σ n) A).symm
  let jA' := (SinglePreDatum.canMapIso sq₃ (𝔇.σ n) A').symm
  let ψ := jA.e.inv ≫ (iA.e.inv ≫ φ ≫ iA'.e.hom) ≫ jA'.e.hom
  have hψ : SinglePreDatum.IsMor ((SinglePreDatum.can sq₃ A).map (𝔇.σ n))
      ((SinglePreDatum.can sq₃ A').map (𝔇.σ n)) ψ :=
    SinglePreDatum.IsMor.of_iso jA jA' (SinglePreDatum.IsMor.of_iso iA iA' hφ)
  obtain ⟨k, b, hb⟩ := hX.exists_mapAt n _ _ ψ
  let E₁ := (SinglePreDatum.can sq₃ A).iterMap 𝔇.Φ k
  let E₂ := (SinglePreDatum.can sq₃ A').iterMap 𝔇.Φ k
  have hb' : SinglePreDatum.IsMor (E₁.map (𝔇.σ (n + k))) (E₂.map (𝔇.σ (n + k)))
      (((𝔇.σ (n + k)).app (.mk (op X))).toFunctor.map b) := by
    have := SinglePreDatum.IsMor.of_iso (𝔇.iterMapIso (SinglePreDatum.can sq₃ A) n k).symm
      (𝔇.iterMapIso (SinglePreDatum.can sq₃ A') n k).symm hψ
    rw [← hb, EndoColim.Pseudococone.mapAt_self] at this
    simpa [SinglePreDatum.Iso.symm, iterMapIso] using this
  obtain ⟨j, hj⟩ := hX₂.exists_map_eq (n + k) _ _ _ _
    (SinglePreDatum.IsMor.map_eq (D₁ := E₁) (D₂ := E₂) (𝔇.σ (n + k)) b hb')
  have hbj := SinglePreDatum.IsMor.iterMap (D₁ := E₁) (D₂ := E₂) 𝔇.Φ b j hj
  let I := fun B : V.obj (.mk (op S)) ↦
    ((SinglePreDatum.canIterIso sq₃ 𝔇.Φ B k).iterMap 𝔇.Φ j).trans
      (SinglePreDatum.canIterIso sq₃ 𝔇.Φ ((𝔇.Φ.iterFunctor S k).obj B) j)
  have hI : ∀ B, (I B).e = (𝔇.Φ.iterFunctor X j).mapIso (𝔇.Φ.pullIsoIter f B k) ≪≫
      𝔇.Φ.pullIsoIter f ((𝔇.Φ.iterFunctor S k).obj B) j := fun B ↦ by
    ext
    change (𝔇.Φ.iterFunctor X j).map (SinglePreDatum.canIterIso sq₃ 𝔇.Φ B k).e.hom ≫
      (SinglePreDatum.canIterIso sq₃ 𝔇.Φ ((𝔇.Φ.iterFunctor S k).obj B) j).e.hom = _
    rw [SinglePreDatum.canIterIso_e, SinglePreDatum.canIterIso_e]
    rfl
  obtain ⟨w, hw⟩ := hV _ (SinglePreDatum.IsMor.of_iso (I A) (I A') hbj)
  let P₁ := 𝔇.Φ.pullIsoIter f A k
  let P₁' := 𝔇.Φ.pullIsoIter f A' k
  rw [hI A, hI A'] at hw
  let x : ((𝔇.σ (n + k)).app (.mk (op S))).toFunctor.obj ((𝔇.Φ.iterFunctor S k).obj A) ⟶
      ((𝔇.σ (n + k)).app (.mk (op S))).toFunctor.obj ((𝔇.Φ.iterFunctor S k).obj A') :=
    ((𝔇.pc S).iterObjIso (n + k) j _).inv ≫
      ((𝔇.σ (n + k + j)).app (.mk (op S))).toFunctor.map w ≫ ((𝔇.pc S).iterObjIso (n + k) j _).hom
  have hx : (P.map f.op.toLoc).toFunctor.map x =
      ((𝔇.σ (n + k)).pullIso f _).inv ≫ ((𝔇.σ (n + k)).app (.mk (op X))).toFunctor.map
        (P₁.inv ≫ b ≫ P₁'.hom) ≫ ((𝔇.σ (n + k)).pullIso f _).hom := by
    rw [𝔇.map_mapAt_pullback (n + k) j]
    have hn := (𝔇.σ (n + k + j)).pullIso_naturality f w
    have hit := (𝔇.pc X).iterObjIso_hom_naturality (n + k) j (P₁.inv ≫ b ≫ P₁'.hom)
    rw [← Iso.eq_comp_inv] at hn
    simp only [Category.assoc] at hn
    rw [← Iso.inv_comp_eq] at hit
    simp only
    rw [← reassoc_of% hn, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hw, ← hit]
    simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
      Category.assoc, Functor.map_comp]
    simp only [Iso.hom_inv_id_map_assoc]
    rfl
  have key : (P.map f.op.toLoc).toFunctor.map
      (((𝔇.pc S).iterObjIso n k A).inv ≫ x ≫ ((𝔇.pc S).iterObjIso n k A').hom) =
      ((𝔇.σ n).pullIso f A).inv ≫ ψ ≫ ((𝔇.σ n).pullIso f A').hom := by
    rw [𝔇.map_mapAt_pullback n k x]
    have hx' : ((𝔇.σ (n + k)).pullIso f _).hom ≫ (P.map f.op.toLoc).toFunctor.map x ≫
        ((𝔇.σ (n + k)).pullIso f _).inv = ((𝔇.σ (n + k)).app (.mk (op X))).toFunctor.map
          (P₁.inv ≫ b ≫ P₁'.hom) := by
      rw [hx]
      simp
    simp only
    rw [reassoc_of% hx', ← hb, EndoColim.Pseudococone.mapAt_self]
    simp [P₁, P₁']
  refine ⟨e.inv ≫ (((𝔇.pc S).iterObjIso n k A).inv ≫ x ≫ ((𝔇.pc S).iterObjIso n k A').hom) ≫
    e'.hom, ?_⟩
  rw [Functor.map_comp, Functor.map_comp, key]
  simp [ψ, jA, jA', iA, iA', SinglePreDatum.canMapIso, SinglePreDatum.Iso.symm,
    SinglePreDatum.isoOfIso', iso]

/-- **Effective descent along `{f}` passes from `V` to the stage colimit `P`**, as soon as the
pseudo-cocones at `S`, `X`, `X ×_S X` and `X ×_S X ×_S X` present `P` as the colimit of the
sequential diagram of `V` along the endo-transformation. -/
theorem isStackFor_singleton (sq₃ : ChosenPullback₃ sq sq sq)
    (hS : (𝔇.pc S).IsColimitPresentation) (hX : (𝔇.pc X).IsColimitPresentation)
    (hX₂ : (𝔇.pc sq.pullback).IsColimitPresentation)
    (hX₃ : (𝔇.pc sq₃.pullback).IsColimitPresentation)
    (hV : V.IsStackFor (Presieve.singleton f)) : P.IsStackFor (Presieve.singleton f) := by
  have hVeq := isEquivalence_toDescentData_of_isStackFor hV
  have hVf : ∀ {A A' : V.obj (.mk (op S))} (a a' : A ⟶ A'),
      (V.map f.op.toLoc).toFunctor.map a = (V.map f.op.toLoc).toFunctor.map a' → a = a' :=
    fun a a' h ↦ (V.toDescentData (fun _ : PUnit.{1} ↦ f)).map_injective
      (Pseudofunctor.DescentData.hom_ext fun _ ↦ h)
  have hVfull : ∀ {A A' : V.obj (.mk (op S))} (c : (V.map f.op.toLoc).toFunctor.obj A ⟶
        (V.map f.op.toLoc).toFunctor.obj A'),
      SinglePreDatum.IsMor (SinglePreDatum.can sq₃ A) (SinglePreDatum.can sq₃ A') c →
        ∃ w : A ⟶ A', (V.map f.op.toLoc).toFunctor.map w = c := by
    intro A A' c h
    refine ⟨(V.toDescentData (fun _ : PUnit.{1} ↦ f)).preimage
      (SinglePreDatum.descentDataHomOfIsMor sq₃ c h), ?_⟩
    exact (congrArg (fun ξ ↦ Pseudofunctor.DescentData.Hom.hom ξ PUnit.unit)
      ((V.toDescentData (fun _ : PUnit.{1} ↦ f)).map_preimage
        (SinglePreDatum.descentDataHomOfIsMor sq₃ c h))).trans
      (SinglePreDatum.descentDataHomOfIsMor_hom sq₃ c h)
  rw [← Presieve.ofArrows_pUnit.{0}, Pseudofunctor.isStackFor_ofArrows_iff]
  have hfaith : (P.toDescentData (fun _ : PUnit.{1} ↦ f)).Faithful := ⟨fun {M M'} m m' h ↦
    𝔇.map_injective_of_isColimitPresentation hS hX hVf m m'
      (congrArg (fun ξ ↦ Pseudofunctor.DescentData.Hom.hom ξ PUnit.unit) h)⟩
  have hfull : (P.toDescentData (fun _ : PUnit.{1} ↦ f)).Full := ⟨fun {M M'} ξ ↦ by
    obtain ⟨m, hm⟩ := 𝔇.exists_map_eq_of_isMor sq₃ hS hX hX₂ hVfull (ξ.hom PUnit.unit)
      (SinglePreDatum.isMor_can sq₃ ξ)
    exact ⟨m, Pseudofunctor.DescentData.hom_ext fun ⟨⟩ ↦ hm⟩⟩
  have hess := 𝔇.essSurj_toDescentData sq₃ hX hX₂ hX₃ hV
  exact { faithful := hfaith, full := hfull, essSurj := hess }

end StageColimitData

end Pseudofunctor

end CategoryTheory

end
