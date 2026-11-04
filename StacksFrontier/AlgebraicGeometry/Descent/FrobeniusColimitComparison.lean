module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitCategory

/-!
# A functor out of the colimit category along an endofunctor

Let `F : C ⥤ C` be an endofunctor and let `colim_F C` be the colimit category of Stacks Tag
0EXA built in `StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitCategory`. A functor
`colim_F C ⥤ D` out of it can be assembled from a functor `S_n : C ⥤ D` for every stage
together with natural isomorphisms `F ⋙ S_{n + 1} ≅ S_n` — a *pseudo-cocone*, which is less
than a cocone in the 1-category `Cat` asks for, where those comparisons would have to be
equalities of functors. This file builds that functor, and specialises it to the comparison
functor of Stacks Tag 0EXB out of `colim_F Vect(X)`. That the assignment is a bijection between
pseudo-cocones and functors out of `colim_F C` is not proved; what is used downstream is only
that the data produces a functor, and that the functor restricts to `S_n` at each stage.

## Main definitions

* `CategoryTheory.EndoColim.Pseudococone`: the data `(S_n)_{n ≥ 0}` together with the
  isomorphisms `F ⋙ S_{n + 1} ≅ S_n`.
* `CategoryTheory.EndoColim.Pseudococone.iterObjIso`: the comparison `S_{n + k}(F^k X) ≅ S_n X`,
  obtained by iterating the pseudo-cocone's own comparison.
* `CategoryTheory.EndoColim.Pseudococone.mapAt`: the morphism `S_n E ⟶ S_m G` of `D` which a
  morphism `F^a E ⟶ F^b G` of `C` induces, for exponents with `n + a = m + b`.
* `CategoryTheory.EndoColim.Pseudococone.desc`: **the functor `colim_F C ⥤ D` determined by a
  pseudo-cocone.**
* `AlgebraicGeometry.frobeniusColimitVectComparison`: **the comparison functor of Stacks Tag
  0EXB**, from `colim_F Vect(X)` to the finite locally free modules over `colim_F 𝒪_X`.

## Main results

* `CategoryTheory.EndoColim.Pseudococone.mapAt_cast` and
  `CategoryTheory.EndoColim.Pseudococone.mapAt_raise`: the induced morphism does not change when
  the presenting morphism of `C` is transported along equalities of its exponents, nor when it is
  raised by applying `F` to it. The second of these is what makes the functor well defined on the
  Hom-sets of `colim_F C`, which are colimits along raising.
* `CategoryTheory.EndoColim.Pseudococone.mapAt_comp` and
  `CategoryTheory.EndoColim.Pseudococone.mapAt_id`: two composable morphisms of `C` induce the
  composite of what they induce, and an identity induces an identity.
* `CategoryTheory.EndoColim.Pseudococone.stageFunctor_comp_desc`: **the functor restricts to
  `S_n` on the stage-`n` copy of `C`**, as an equality of functors.
* `CategoryTheory.EndoColim.Pseudococone.isEquivalence_desc`: **the functor is an equivalence as
  soon as it is bijective on the Hom-sets of `colim_F C` and every object of `D` is isomorphic
  to one in the image of a stage functor.** Every object of `colim_F C` lies in the image of a
  stage functor, so no condition beyond those two is needed.

## Implementation notes

A morphism of `colim_F C` from `(E, n)` to `(G, m)` presented at level `k` is a morphism
`F^{m + k}E ⟶ F^{n + k}G` of `C`, and the two exponents satisfy `n + (m + k) = m + (n + k)` —
they are the two ways of writing one and the same absolute level. The induced morphism is
therefore defined for a pair of exponents `a`, `b` constrained only by `n + a = m + b`, and the
comparison `CategoryTheory.EndoColim.Pseudococone.stageHom` of the stage functors at those two
equal indices is inserted once. Every lemma is proved by substituting that equation, after which
the comparison becomes an identity by proof irrelevance and the content is the naturality of the
isomorphisms `F ⋙ S_{n + 1} ≅ S_n`.

The iterated comparison is taken object by object rather than as an isomorphism of functors.
Both forms are definitionally the same, but the functor form presents the objects it connects as
`(F^k ⋙ S_{n + k}).obj X`, which no rewrite can see through — `Functor.comp` is semireducible —
so a composite built from it is well typed only up to unfolding and neither `simp` nor `rw` can
reassociate it. For the same reason the comparison of the pseudo-cocone is repackaged as
`CategoryTheory.EndoColim.Pseudococone.compatIter`, whose declared type names the objects
`S_{n + (k + 1)}(F^{k + 1}X)` and `S_{n + k}(F^k X)` rather than the composites and shifted
indices that `Iso.app` produces, and `CategoryTheory.endoRaise` is used in place of `F.map`,
its declared type naming `F^{a + 1}E` rather than `F(F^a E)`. With every type in the shape
`S_j.obj (F^i.obj X)` the rewrites go through.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe v u v₂ u₂

namespace CategoryTheory.EndoColim

variable {C : Type u} [Category.{v} C] {F : C ⥤ C} {D : Type u₂} [Category.{v₂} D]

/-- A *pseudo-cocone* on the sequential diagram `C →F C →F ⋯` with summit `D`: a functor
`C ⥤ D` at every stage, and a natural isomorphism identifying the stage-`n + 1` functor
precomposed with `F` with the stage-`n` functor. This is the data a functor out of the colimit
category `colim_F C` of Stacks Tag 0EXA needs; a cocone in `Cat` would ask for those
comparisons to be equalities of functors. -/
structure Pseudococone (F : C ⥤ C) (D : Type u₂) [Category.{v₂} D] where
  /-- the functor `C ⥤ D` at the stage `n` -/
  stage : ℕ → (C ⥤ D)
  /-- the comparison of the stage-`n + 1` functor, precomposed with `F`, with the stage-`n` one -/
  compat : ∀ n : ℕ, F ⋙ stage (n + 1) ≅ stage n

namespace Pseudococone

variable (P : Pseudococone F D)

/-! ### The stage functors at equal indices -/

/-- The comparison of two stage functors whose indices are equal. -/
def stageHom {N N' : ℕ} (h : N = N') : P.stage N ⟶ P.stage N' :=
  eqToHom (congrArg P.stage h)

/-- The comparison of a stage functor with itself is the identity. -/
@[simp]
lemma stageHom_refl {N : ℕ} (h : N = N) : P.stageHom h = 𝟙 (P.stage N) := by
  simp [stageHom]

/-- Comparisons of stage functors at equal indices compose to the comparison along the composite
equality. -/
lemma stageHom_comp {N N' N'' : ℕ} (h : N = N') (h' : N' = N'') :
    P.stageHom h ≫ P.stageHom h' = P.stageHom (h.trans h') := by
  subst h; subst h'; simp

/-- `CategoryTheory.EndoColim.Pseudococone.stageHom_comp`, evaluated at an object. -/
lemma stageHom_app_comp {N N' N'' : ℕ} (h : N = N') (h' : N' = N'') (X : C) :
    (P.stageHom h).app X ≫ (P.stageHom h').app X = (P.stageHom (h.trans h')).app X := by
  rw [← P.stageHom_comp h h']; rfl

/-- The comparison of stage functors at equal indices is natural in the object. -/
lemma stageHom_app_naturality {N N' : ℕ} (h : N = N') {X Y : C} (f : X ⟶ Y) :
    (P.stage N).map f ≫ (P.stageHom h).app Y = (P.stageHom h).app X ≫ (P.stage N').map f :=
  (P.stageHom h).naturality f

/-- `CategoryTheory.EndoColim.Pseudococone.stageHom_app_naturality` with a trailing morphism,
read from right to left. -/
lemma stageHom_app_naturality_assoc {N N' : ℕ} (h : N = N') {X Y : C} (f : X ⟶ Y) {W : D}
    (q : (P.stage N').obj Y ⟶ W) :
    (P.stageHom h).app X ≫ (P.stage N').map f ≫ q =
      (P.stage N).map f ≫ (P.stageHom h).app Y ≫ q := by
  rw [← Category.assoc, ← P.stageHom_app_naturality h f, Category.assoc]

/-- `CategoryTheory.EndoColim.Pseudococone.stageHom_app_comp` with a trailing morphism. -/
lemma stageHom_app_comp_assoc {N N' N'' : ℕ} (h : N = N') (h' : N' = N'') (X : C) {W : D}
    (q : (P.stage N'').obj X ⟶ W) :
    (P.stageHom h).app X ≫ (P.stageHom h').app X ≫ q =
      (P.stageHom (h.trans h')).app X ≫ q := by
  rw [← Category.assoc, P.stageHom_app_comp h h']

/-! ### The stage functors along iterates of `F` -/

/-- The comparison carried by the pseudo-cocone, read between the two objects it connects when
the object is an iterate `F^k X`. Only the type is spelled differently; see the implementation
notes for why that matters. -/
def compatIter (n k : ℕ) (X : C) :
    (P.stage (n + (k + 1))).obj ((F.endoIter (k + 1)).obj X) ≅
      (P.stage (n + k)).obj ((F.endoIter k).obj X) :=
  (P.compat (n + k)).app ((F.endoIter k).obj X)

/-- The comparison `CategoryTheory.EndoColim.Pseudococone.compatIter` is natural in the object. -/
lemma compatIter_hom_naturality (n k : ℕ) {X Y : C} (f : X ⟶ Y) :
    (P.stage (n + (k + 1))).map ((F.endoIter (k + 1)).map f) ≫ (P.compatIter n k Y).hom =
      (P.compatIter n k X).hom ≫ (P.stage (n + k)).map ((F.endoIter k).map f) :=
  (P.compat (n + k)).hom.naturality ((F.endoIter k).map f)

/-- **The stage functors are compatible with arbitrarily many applications of `F`**:
`S_{n + k}(F^k X) ≅ S_n X`. For `k = 1` this is the comparison carried by the pseudo-cocone, and
the general case is that comparison iterated. -/
def iterObjIso (n : ℕ) : ∀ (k : ℕ) (X : C),
    (P.stage (n + k)).obj ((F.endoIter k).obj X) ≅ (P.stage n).obj X
  | 0, _ => Iso.refl _
  | k + 1, X => P.compatIter n k X ≪≫ iterObjIso n k X

/-- The comparison along `k + 1` applications of `F` is the pseudo-cocone's comparison followed by
the comparison along `k` applications. -/
lemma iterObjIso_succ_hom (n k : ℕ) (X : C) :
    (P.iterObjIso n (k + 1) X).hom = (P.compatIter n k X).hom ≫ (P.iterObjIso n k X).hom :=
  rfl

/-- The inverse of the comparison along `k + 1` applications of `F`, unfolded one step. -/
lemma iterObjIso_succ_inv (n k : ℕ) (X : C) :
    (P.iterObjIso n (k + 1) X).inv = (P.iterObjIso n k X).inv ≫ (P.compatIter n k X).inv :=
  rfl

/-- **The comparison along `k` applications of `F` is natural in the object.** -/
lemma iterObjIso_hom_naturality (n k : ℕ) {X Y : C} (f : X ⟶ Y) :
    (P.stage (n + k)).map ((F.endoIter k).map f) ≫ (P.iterObjIso n k Y).hom =
      (P.iterObjIso n k X).hom ≫ (P.stage n).map f := by
  induction k with
  | zero => exact (Category.comp_id _).trans (Category.id_comp _).symm
  | succ k ih =>
      simp only [iterObjIso_succ_hom, Category.assoc]
      rw [reassoc_of% (P.compatIter_hom_naturality n k f), ih]

/-! ### The morphism of `D` induced by a presented morphism of `C` -/

/-- **The morphism `S_n E ⟶ S_m G` induced by a morphism `F^a E ⟶ F^b G` of `C`**, for exponents
with `n + a = m + b`. It is the stage-`n + a` functor applied to the morphism, conjugated by the
comparisons of the stage functors along iterates of `F`. -/
def mapAt (n m a b : ℕ) (h : n + a = m + b) {E G : C}
    (f : (F.endoIter a).obj E ⟶ (F.endoIter b).obj G) :
    (P.stage n).obj E ⟶ (P.stage m).obj G :=
  (P.iterObjIso n a E).inv ≫ (P.stage (n + a)).map f ≫
    (P.stageHom h).app ((F.endoIter b).obj G) ≫ (P.iterObjIso m b G).hom

/-- **Transporting the presenting morphism along equalities of its exponents does not change
the morphism it induces.** -/
lemma mapAt_cast (n m a b a' b' : ℕ) (h : n + a = m + b) (h' : n + a' = m + b')
    (eA : a = a') (eB : b = b') {E G : C}
    (f : (F.endoIter a).obj E ⟶ (F.endoIter b).obj G) :
    P.mapAt n m a' b' h' (endoHomCast eA eB f) = P.mapAt n m a b h f := by
  subst eA; subst eB; rfl

/-- The content of the raising invariance: at one absolute level the comparison of the stage
functors at equal indices absorbs one application of `F`, by naturality of the pseudo-cocone's
comparison isomorphism. -/
lemma compat_inv_app_comp (J K : ℕ) (hJK : J = K) (h' : J + 1 = K + 1) {Y Z : C} (f : Y ⟶ Z) :
    (P.compat J).inv.app Y ≫ (P.stage (J + 1)).map (F.map f) ≫
          (P.stageHom h').app (F.obj Z) ≫ (P.compat K).hom.app Z =
      (P.stage J).map f ≫ (P.stageHom hJK).app Z := by
  subst hJK
  have hnat : (F ⋙ P.stage (J + 1)).map f ≫ (P.compat J).hom.app Z =
      (P.compat J).hom.app Y ≫ (P.stage J).map f := (P.compat J).hom.naturality f
  have key : (P.compat J).inv.app Y ≫ (F ⋙ P.stage (J + 1)).map f ≫
      (P.compat J).hom.app Z = (P.stage J).map f := by
    rw [hnat, Iso.inv_hom_id_app_assoc]
  simpa using key

/-- `CategoryTheory.EndoColim.Pseudococone.compat_inv_app_comp` with its exponents and its
objects spelled as they occur in a presentation raised by one. -/
lemma compatIter_middle (n m a b : ℕ) (h : n + a = m + b) (h' : n + (a + 1) = m + (b + 1))
    {E G : C} (f : (F.endoIter a).obj E ⟶ (F.endoIter b).obj G) :
    (P.compatIter n a E).inv ≫ (P.stage (n + (a + 1))).map (endoRaise f 1) ≫
          (P.stageHom h').app ((F.endoIter (b + 1)).obj G) ≫ (P.compatIter m b G).hom =
      (P.stage (n + a)).map f ≫ (P.stageHom h).app ((F.endoIter b).obj G) :=
  P.compat_inv_app_comp (n + a) (m + b) h (by omega) f

/-- **Raising the presenting morphism by one, by applying `F` to it, does not change the
morphism it induces.** -/
lemma mapAt_succ (n m a b : ℕ) (h : n + a = m + b) (h' : n + (a + 1) = m + (b + 1)) {E G : C}
    (f : (F.endoIter a).obj E ⟶ (F.endoIter b).obj G) :
    P.mapAt n m (a + 1) (b + 1) h' (endoRaise f 1) = P.mapAt n m a b h f := by
  simp only [mapAt, iterObjIso_succ_inv, iterObjIso_succ_hom, Category.assoc]
  rw [reassoc_of% (P.compatIter_middle n m a b h h' f)]

/-- **Raising the presenting morphism does not change the morphism it induces.** -/
lemma mapAt_raise (n m a b : ℕ) (h : n + a = m + b) {E G : C}
    (f : (F.endoIter a).obj E ⟶ (F.endoIter b).obj G) :
    ∀ (j : ℕ) (hj : n + (a + j) = m + (b + j)),
      P.mapAt n m (a + j) (b + j) hj (endoRaise f j) = P.mapAt n m a b h f
  | 0, _ => rfl
  | j + 1, hj =>
      Eq.trans (P.mapAt_succ n m (a + j) (b + j) (by omega) hj (endoRaise f j))
        (mapAt_raise n m a b h f j (by omega))

/-- **A presenting morphism raised and then transported induces the same morphism.** This is the
form in which the raising invariance is used: the morphisms of `colim_F C` which `compHom`
produces are transports of raises. -/
lemma mapAt_endoHomCast_endoRaise (n m a b : ℕ) (h : n + a = m + b) {E G : C}
    (f : (F.endoIter a).obj E ⟶ (F.endoIter b).obj G) (j a' b' : ℕ) (h' : n + a' = m + b')
    (ea : a + j = a') (eb : b + j = b') :
    P.mapAt n m a' b' h' (endoHomCast ea eb (endoRaise f j)) = P.mapAt n m a b h f := by
  rw [P.mapAt_cast n m (a + j) (b + j) a' b' (by omega) h' ea eb,
    P.mapAt_raise n m a b h f j (by omega)]

/-- **An identity induces an identity.** -/
lemma mapAt_id (n a : ℕ) (h : n + a = n + a) {E : C} :
    P.mapAt n n a a h (𝟙 ((F.endoIter a).obj E)) = 𝟙 ((P.stage n).obj E) := by
  simp [mapAt]

/-- **Two composable morphisms of `C` induce the composite of what they induce.** -/
lemma mapAt_comp (n m t a b c : ℕ) (h₁ : n + a = m + b) (h₂ : m + b = t + c) {E G H : C}
    (f : (F.endoIter a).obj E ⟶ (F.endoIter b).obj G)
    (g : (F.endoIter b).obj G ⟶ (F.endoIter c).obj H) :
    P.mapAt n t a c (h₁.trans h₂) (f ≫ g) =
      P.mapAt n m a b h₁ f ≫ P.mapAt m t b c h₂ g := by
  simp only [mapAt, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [P.stageHom_app_naturality_assoc h₁ g, P.stageHom_app_comp_assoc h₁ h₂]

/-- The morphism of `D` which an iterate of a morphism of `C` induces is the stage functor
applied to that morphism. -/
lemma mapAt_endoIter_map (n a : ℕ) (h : n + a = n + a) {E G : C} (f : E ⟶ G) :
    P.mapAt n n a a h ((F.endoIter a).map f) = (P.stage n).map f := by
  simp only [mapAt, stageHom_refl, NatTrans.id_app, Category.id_comp]
  rw [P.iterObjIso_hom_naturality n a f, Iso.inv_hom_id_assoc]

/-! ### The functor out of the colimit category -/

/-- The morphism of `D` induced by a presentation of a morphism of `colim_F C`. -/
def mapRep {A B : EndoColim F} (x : HomRep A B) :
    (P.stage A.stage).obj A.obj ⟶ (P.stage B.stage).obj B.obj :=
  P.mapAt A.stage B.stage (B.stage + x.level) (A.stage + x.level) (by omega) x.hom

/-- **Two presentations of one morphism of `colim_F C` induce the same morphism of `D`.** -/
lemma mapRep_rel {A B : EndoColim F} {x y : HomRep A B} (h : HomRep.Rel x y) :
    P.mapRep x = P.mapRep y := by
  subst h
  exact (P.mapAt_endoHomCast_endoRaise A.stage B.stage (B.stage + x.level)
    (A.stage + x.level) (by omega) x.hom 1 (B.stage + (x.level + 1))
    (A.stage + (x.level + 1)) (by omega) (by omega) (by omega)).symm

/-- The morphism of `D` induced by a morphism of `colim_F C`. -/
def homMap {A B : EndoColim F} (u : A ⟶ B) :
    (P.stage A.stage).obj A.obj ⟶ (P.stage B.stage).obj B.obj :=
  Quot.lift P.mapRep (fun _ _ h ↦ P.mapRep_rel h) u

/-- On a morphism given by a presentation, `homMap` is the morphism that presentation induces. -/
@[simp]
lemma homMap_of {A B : EndoColim F} (k : ℕ)
    (f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj) :
    P.homMap (Hom.of k f) = P.mapRep (⟨k, f⟩ : HomRep A B) :=
  rfl

/-- **The functor `colim_F C ⥤ D` determined by a pseudo-cocone.** On objects it is
`(E, n) ↦ S_n E`, and a morphism presented at level `k` is sent to the stage-`n + m + k`
functor applied to it, conjugated by the comparisons of the stage functors along iterates of
`F`. -/
def desc : EndoColim F ⥤ D where
  obj A := (P.stage A.stage).obj A.obj
  map u := P.homMap u
  map_id A := P.mapAt_id A.stage (A.stage + 0) (by omega)
  map_comp {A B W} u v := by
    induction u using Quot.ind with
    | _ x =>
      induction v using Quot.ind with
      | _ y =>
        change P.mapRep (⟨B.stage + x.level + y.level, compHom x.level x.hom y.level y.hom⟩ :
          HomRep A W) = P.mapRep x ≫ P.mapRep y
        rw [mapRep, compHom,
          P.mapAt_comp A.stage B.stage W.stage
            (W.stage + (B.stage + x.level + y.level))
            (A.stage + W.stage + x.level + y.level)
            (A.stage + (B.stage + x.level + y.level)) (by omega) (by omega)]
        refine congrArg₂ (· ≫ ·) ?_ ?_
        · exact P.mapAt_endoHomCast_endoRaise A.stage B.stage (B.stage + x.level)
            (A.stage + x.level) (by omega) x.hom (W.stage + y.level) _ _ (by omega)
            (by omega) (by omega)
        · exact P.mapAt_endoHomCast_endoRaise B.stage W.stage (W.stage + y.level)
            (B.stage + y.level) (by omega) y.hom (A.stage + x.level) _ _ (by omega)
            (by omega) (by omega)

/-- The functor determined by a pseudo-cocone sends `(E, n)` to `S_n E`. -/
@[simp]
lemma desc_obj (A : EndoColim F) : P.desc.obj A = (P.stage A.stage).obj A.obj := rfl

/-- The functor determined by a pseudo-cocone acts on morphisms by `homMap`. -/
@[simp]
lemma desc_map {A B : EndoColim F} (u : A ⟶ B) : P.desc.map u = P.homMap u := rfl

/-! ### When the functor out of the colimit category is an equivalence -/

/-- **The functor determined by a pseudo-cocone is faithful** as soon as it is injective on the
Hom-sets of `colim_F C`. -/
lemma faithful_desc
    (h : ∀ (A B : EndoColim F) (u v : A ⟶ B), P.homMap u = P.homMap v → u = v) :
    P.desc.Faithful where
  map_injective {A B _ _} huv := h A B _ _ huv

/-- **The functor determined by a pseudo-cocone is full** as soon as it is surjective on the
Hom-sets of `colim_F C`. -/
lemma full_desc
    (h : ∀ (A B : EndoColim F)
      (w : (P.stage A.stage).obj A.obj ⟶ (P.stage B.stage).obj B.obj),
        ∃ u : A ⟶ B, P.homMap u = w) :
    P.desc.Full where
  map_surjective {A B} w := h A B w

/-- **The functor determined by a pseudo-cocone is essentially surjective** as soon as every
object of `D` is isomorphic to one in the image of a stage functor. Every object of `colim_F C`
is in the image of a stage functor, so this is the whole of the condition. -/
lemma essSurj_desc (h : ∀ Y : D, ∃ (n : ℕ) (E : C), Nonempty ((P.stage n).obj E ≅ Y)) :
    P.desc.EssSurj where
  mem_essImage Y := by
    obtain ⟨n, E, ⟨e⟩⟩ := h Y
    exact ⟨⟨E, n⟩, ⟨e⟩⟩

/-- **The functor `colim_F C ⥤ D` determined by a pseudo-cocone is an equivalence** as soon as
it is bijective on the Hom-sets of `colim_F C` and every object of `D` is isomorphic to one in
the image of a stage functor. -/
lemma isEquivalence_desc
    (hhom : ∀ (A B : EndoColim F) (u v : A ⟶ B), P.homMap u = P.homMap v → u = v)
    (hfull : ∀ (A B : EndoColim F)
      (w : (P.stage A.stage).obj A.obj ⟶ (P.stage B.stage).obj B.obj),
        ∃ u : A ⟶ B, P.homMap u = w)
    (hsurj : ∀ Y : D, ∃ (n : ℕ) (E : C), Nonempty ((P.stage n).obj E ≅ Y)) :
    P.desc.IsEquivalence :=
  ⟨P.faithful_desc hhom, P.full_desc hfull, P.essSurj_desc hsurj⟩

/-- **On the stage-`n` copy of `C` the functor determined by a pseudo-cocone acts as the
stage-`n` functor.** -/
lemma homMap_stageFunctor_map (n : ℕ) {E G : C} (f : E ⟶ G) :
    P.homMap ((stageFunctor F n).map f) = (P.stage n).map f :=
  P.mapAt_endoIter_map n (n + 0) (by omega) f

/-- **The functor determined by a pseudo-cocone restricts to the stage-`n` functor on the
stage-`n` copy of `C`.** -/
lemma stageFunctor_comp_desc (n : ℕ) : stageFunctor F n ⋙ P.desc = P.stage n :=
  Functor.hext (fun _ ↦ rfl) fun _ _ f ↦ heq_of_eq (P.homMap_stageFunctor_map n f)

end Pseudococone

end CategoryTheory.EndoColim

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- The pseudo-cocone of Stacks Tag 0EXB: extension of scalars along the stage-`n` coprojection
`𝒪_X ⟶ colim_F 𝒪_X`, together with the identification of pulling back along the absolute
Frobenius and extending scalars at the stage `n + 1` with extending scalars at the stage `n`. -/
noncomputable def frobeniusColimitVectPseudococone :
    CategoryTheory.EndoColim.Pseudococone (frobeniusPullback X p hX)
      (frobeniusColimitVectorBundles X p hX) where
  stage := frobeniusStageFunctor X p hX
  compat := frobeniusStageFunctorIso X p hX

/-- **The comparison functor of Stacks Tag 0EXB.** It takes the object `(ℰ, n)` of
`colim_F Vect(X)` to `ℰ ⊗_{𝒪_X} colim_F 𝒪_X`, the scalars being extended along the stage-`n`
coprojection, and a morphism presented at a level to the extension of scalars of that
morphism, conjugated by the comparisons of the stage functors along iterated Frobenius
pullback. -/
noncomputable def frobeniusColimitVectComparison :
    frobeniusColimitVectModel X p hX ⥤ frobeniusColimitVectorBundles X p hX :=
  (frobeniusColimitVectPseudococone X p hX).desc

/-- **The comparison functor of Stacks Tag 0EXB restricts to extension of scalars along the
stage-`n` coprojection on the stage-`n` copy of `Vect(X)`.** -/
lemma frobeniusColimitVectModelStage_comp_comparison (n : ℕ) :
    frobeniusColimitVectModelStage X p hX n ⋙ frobeniusColimitVectComparison X p hX =
      frobeniusStageFunctor X p hX n :=
  (frobeniusColimitVectPseudococone X p hX).stageFunctor_comp_desc n

end AlgebraicGeometry

end
