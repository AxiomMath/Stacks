module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageShift
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Absolute
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Twist

/-!
# Pulling back along a morphism of schemes on `colim_F Vect`

Let `F : C ⥤ C` and `F' : D ⥤ D` be endofunctors and let `G : C ⥤ D` be a functor together with
a natural isomorphism `e : F ⋙ G ≅ G ⋙ F'`. Then `G` induces a functor between the colimit
categories `colim_F C ⥤ colim_{F'} D` of Stacks Tag 0EXA: it sends `(E, n)` to `(G E, n)`, and a
morphism presented at a level by a morphism `F^a E ⟶ F^b E'` of `C` to the image of that morphism
under `G`, conjugated by the iterates `G (F^a E) ≅ F'^a (G E)` of `e`.

For a morphism of schemes `f : X ⟶ Y` in characteristic `p` the absolute Frobenius commutes with
`f` (Stacks Tag 0CC7), so pullback of finite locally free modules commutes with Frobenius
pullback up to a canonical isomorphism, and this produces the functor

`colim_F Vect(Y) ⥤ colim_F Vect(X)`

of Stacks Tag 0EXH.

## Main definitions

* `CategoryTheory.endoIterCommIso`: the iterate `G (F^a E) ≅ F'^a (G E)` of `e`.
* `CategoryTheory.endoConj`: a morphism between images under `G` of iterates, conjugated by those
  isomorphisms into a morphism between iterates of images.
* `CategoryTheory.EndoColim.mapOfComm`: **the functor `colim_F C ⥤ colim_{F'} D` induced by `G`
  and `e`.**
* `AlgebraicGeometry.Scheme.Vect.pullback`: pullback of finite locally free modules.
* `AlgebraicGeometry.frobeniusVectPullbackIso`: pullback commutes with Frobenius pullback.
* `AlgebraicGeometry.frobeniusColimitVectModelPullback`: **the functor
  `colim_F Vect(Y) ⥤ colim_F Vect(X)` induced by a morphism `f : X ⟶ Y`.**

## Main results

* `CategoryTheory.endoConj_comp`, `CategoryTheory.endoConj_map_endoRaise` and
  `CategoryTheory.endoConj_map_endoHomCast`: conjugation is compatible with composition, with
  raising and with transport of exponents. These are the three facts the functor needs.
* `CategoryTheory.EndoColim.mapOfComm_map_of`: the functor acts on a morphism presented at a level
  by conjugating its image under `G` at that same level.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe v₁ u₁ v₂ u₂ u

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ C} {F' : D ⥤ D} (G : C ⥤ D) (e : F ⋙ G ≅ G ⋙ F')

/-- The iterate of a commutation isomorphism `e : F ⋙ G ≅ G ⋙ F'`: the isomorphism
`G (F^a E) ≅ F'^a (G E)`. -/
def endoIterCommIso : ∀ (a : ℕ) (E : C),
    G.obj ((F.endoIter a).obj E) ≅ (F'.endoIter a).obj (G.obj E)
  | 0, _ => Iso.refl _
  | a + 1, E => e.app ((F.endoIter a).obj E) ≪≫ F'.mapIso (endoIterCommIso a E)

/-- The iterated commutation isomorphism at level `0` is the identity. -/
@[simp]
lemma endoIterCommIso_zero (E : C) : endoIterCommIso G e 0 E = Iso.refl _ := rfl

/-- The iterated commutation isomorphism at level `a + 1` is `e` composed with the image under
`F'` of the one at level `a`. -/
lemma endoIterCommIso_succ (a : ℕ) (E : C) :
    endoIterCommIso G e (a + 1) E =
      e.app ((F.endoIter a).obj E) ≪≫ F'.mapIso (endoIterCommIso G e a E) := rfl

/-- A morphism between images under `G` of iterates of `F`, conjugated by the iterated
commutation isomorphisms into a morphism between iterates of `F'`. -/
def endoConj {E E' : C} {a b : ℕ}
    (φ : G.obj ((F.endoIter a).obj E) ⟶ G.obj ((F.endoIter b).obj E')) :
    (F'.endoIter a).obj (G.obj E) ⟶ (F'.endoIter b).obj (G.obj E') :=
  (endoIterCommIso G e a E).inv ≫ φ ≫ (endoIterCommIso G e b E').hom

variable {G e}

/-- Conjugation is injective. -/
lemma endoConj_injective {E E' : C} {a b : ℕ} :
    Function.Injective (endoConj G e (E := E) (E' := E') (a := a) (b := b)) :=
  (Iso.homCongr (endoIterCommIso G e a E) (endoIterCommIso G e b E')).injective

/-- Every morphism between iterates of `F'` is a conjugate. -/
lemma endoConj_surjective {E E' : C} {a b : ℕ} :
    Function.Surjective (endoConj G e (E := E) (E' := E') (a := a) (b := b)) :=
  (Iso.homCongr (endoIterCommIso G e a E) (endoIterCommIso G e b E')).surjective

/-- **Conjugation is compatible with composition.** -/
lemma endoConj_comp {E E' E'' : C} {a b c : ℕ}
    (φ : G.obj ((F.endoIter a).obj E) ⟶ G.obj ((F.endoIter b).obj E'))
    (ψ : G.obj ((F.endoIter b).obj E') ⟶ G.obj ((F.endoIter c).obj E'')) :
    endoConj G e (φ ≫ ψ) = endoConj G e φ ≫ endoConj G e ψ := by
  simp [endoConj]

/-- **Conjugation takes an identity to an identity.** -/
@[simp]
lemma endoConj_id {E : C} {a : ℕ} :
    endoConj G e (𝟙 (G.obj ((F.endoIter a).obj E))) = 𝟙 _ := by
  simp [endoConj]

/-- One step of `CategoryTheory.endoConj_map_endoRaise`: conjugating the image of `F.map φ` is
applying `F'` to the conjugate of the image of `φ`. -/
lemma endoConj_map_map {E E' : C} {a b : ℕ}
    (φ : (F.endoIter a).obj E ⟶ (F.endoIter b).obj E') :
    endoConj G e (a := a + 1) (b := b + 1) (G.map (F.map φ)) =
      F'.map (endoConj G e (G.map φ)) := by
  have h : G.map (F.map φ) ≫ e.hom.app ((F.endoIter b).obj E') =
      e.hom.app ((F.endoIter a).obj E) ≫ F'.map (G.map φ) := e.hom.naturality φ
  show (F'.map (endoIterCommIso G e a E).inv ≫ e.inv.app ((F.endoIter a).obj E)) ≫
      G.map (F.map φ) ≫ e.hom.app ((F.endoIter b).obj E') ≫
        F'.map (endoIterCommIso G e b E').hom = _
  rw [Category.assoc, reassoc_of% h, Iso.inv_hom_id_app_assoc]
  simp only [endoConj, Functor.map_comp]

/-- **Conjugation is compatible with raising.** -/
lemma endoConj_map_endoRaise {E E' : C} {a b : ℕ}
    (φ : (F.endoIter a).obj E ⟶ (F.endoIter b).obj E') (j : ℕ) :
    endoConj G e (G.map (endoRaise φ j)) = endoRaise (endoConj G e (G.map φ)) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [endoRaise_succ, endoRaise_succ, ← ih]
    exact endoConj_map_map (endoRaise φ j)

/-- **Conjugation is compatible with transport of exponents.** -/
lemma endoConj_map_endoHomCast {E E' : C} {a b a' b' : ℕ} (ha : a = a') (hb : b = b')
    (φ : (F.endoIter a).obj E ⟶ (F.endoIter b).obj E') :
    endoConj G e (G.map (endoHomCast ha hb φ)) = endoHomCast ha hb (endoConj G e (G.map φ)) := by
  subst ha; subst hb; rfl

namespace EndoColim

variable (G e)

/-- The image of a presentation of a morphism of `colim_F C`: the image under `G` of the
presenting morphism, conjugated, at the same level. -/
def HomRep.mapOfComm {A B : EndoColim F} (x : HomRep A B) :
    HomRep (F := F') ⟨G.obj A.obj, A.stage⟩ ⟨G.obj B.obj, B.stage⟩ :=
  ⟨x.level, endoConj G e (G.map x.hom)⟩

variable {G e}

/-- `HomRep.mapOfComm` sends related presentations to related presentations. -/
lemma HomRep.mapOfComm_rel {A B : EndoColim F} {x y : HomRep A B} (h : HomRep.Rel x y) :
    HomRep.Rel (x.mapOfComm G e) (y.mapOfComm G e) := by
  subst h
  unfold HomRep.Rel HomRep.mapOfComm
  dsimp only
  rw [endoConj_map_endoHomCast, endoConj_map_endoRaise]

/-- Conjugating the image under `G` of a composite presentation `compHom k f l g` gives the
composite presentation of the conjugated images of `f` and `g`. -/
lemma HomRep.mapOfComm_compHom {A B W : EndoColim F} (k : ℕ)
    (f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj) (l : ℕ)
    (g : (F.endoIter (W.stage + l)).obj B.obj ⟶ (F.endoIter (B.stage + l)).obj W.obj) :
    endoConj G e (G.map (compHom k f l g)) =
      compHom (A := ⟨G.obj A.obj, A.stage⟩) (B := ⟨G.obj B.obj, B.stage⟩)
        (D := ⟨G.obj W.obj, W.stage⟩) k (endoConj G e (G.map f)) l
        (endoConj G e (G.map g)) := by
  simp only [compHom, Functor.map_comp, endoConj_comp, endoConj_map_endoHomCast,
    endoConj_map_endoRaise]

variable (G e)

/-- **The functor `colim_F C ⥤ colim_{F'} D` induced by a functor `G : C ⥤ D` commuting with the
endofunctors up to `e : F ⋙ G ≅ G ⋙ F'`.** On objects it is `(E, n) ↦ (G E, n)`; a morphism
presented at a level is sent to the conjugate of its image under `G`, at the same level. -/
def mapOfComm : EndoColim F ⥤ EndoColim F' where
  obj A := ⟨G.obj A.obj, A.stage⟩
  map {A B} u := Quot.lift (fun x : HomRep A B ↦
      Hom.of (A := (⟨G.obj A.obj, A.stage⟩ : EndoColim F')) (B := ⟨G.obj B.obj, B.stage⟩)
        x.level (endoConj G e (G.map x.hom)))
    (fun _ _ h ↦ Quot.sound (HomRep.mapOfComm_rel h)) u
  map_id A :=
    congrArg (Hom.of (A := (⟨G.obj A.obj, A.stage⟩ : EndoColim F'))
      (B := ⟨G.obj A.obj, A.stage⟩) 0)
      ((congrArg (endoConj G e) (G.map_id _)).trans endoConj_id)
  map_comp {A B W} u v := by
    induction u using Quot.ind with
    | _ x =>
      induction v using Quot.ind with
      | _ y =>
        exact congrArg (Hom.of (A := (⟨G.obj A.obj, A.stage⟩ : EndoColim F'))
          (B := ⟨G.obj W.obj, W.stage⟩) (B.stage + x.level + y.level))
          (HomRep.mapOfComm_compHom x.level x.hom y.level y.hom)

/-- The induced functor sends `(E, n)` to `(G E, n)`. -/
@[simp]
lemma mapOfComm_obj (A : EndoColim F) : (mapOfComm G e).obj A = ⟨G.obj A.obj, A.stage⟩ := rfl

/-- **The induced functor acts on a morphism presented at level `k` by conjugating its image under
`G`, at the same level.** -/
lemma mapOfComm_map_of {A B : EndoColim F} (k : ℕ)
    (f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj) :
    (mapOfComm G e).map (Hom.of k f : A ⟶ B) =
      (Hom.of (A := ⟨G.obj A.obj, A.stage⟩) (B := ⟨G.obj B.obj, B.stage⟩) k
        (endoConj G e (G.map f))) := rfl

end EndoColim

end CategoryTheory

namespace AlgebraicGeometry

/-- Pullback of finite locally free modules along a morphism of schemes. -/
noncomputable def Scheme.Vect.pullback {X Y : Scheme.{u}} (f : X ⟶ Y) : Y.Vect ⥤ X.Vect :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Scheme.Modules.pullback f)
    (fun M ↦ SheafOfModules.IsFiniteLocallyFree.pullback_scheme f M.1 M.2)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ) [Fact p.Prime]
  (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)

/-- The isomorphism `f^* F_Y^* ≅ F_X^* f^*` of functors on all modules, from the naturality of
the absolute Frobenius (Stacks Tag 0CC7). -/
noncomputable def frobeniusModulesPullbackIso :
    Scheme.Modules.pullback (absoluteFrobenius Y p hY) ⋙ Scheme.Modules.pullback f ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback (absoluteFrobenius X p hX) :=
  Scheme.Modules.pullbackComp f (absoluteFrobenius Y p hY) ≪≫
    Scheme.Modules.pullbackCongr (absoluteFrobenius_naturality f p hX hY).symm ≪≫
      (Scheme.Modules.pullbackComp (absoluteFrobenius X p hX) f).symm

/-- **Pullback of finite locally free modules commutes with Frobenius pullback**: the
isomorphism `f^* F_Y^* ≅ F_X^* f^*` of functors `Vect(Y) ⥤ Vect(X)`. -/
noncomputable def frobeniusVectPullbackIso :
    frobeniusPullback Y p hY ⋙ Scheme.Vect.pullback f ≅
      Scheme.Vect.pullback f ⋙ frobeniusPullback X p hX :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ ((frobeniusModulesPullbackIso f p hX hY).app M.1))
    (fun g ↦ (ObjectProperty.ι _).map_injective
      ((frobeniusModulesPullbackIso f p hX hY).hom.naturality g.hom))

/-- **The functor `colim_F Vect(Y) ⥤ colim_F Vect(X)` of Stacks Tag 0EXH** induced by a morphism
`f : X ⟶ Y` of schemes in characteristic `p`. It sends `(ℰ, n)` to `(f^*ℰ, n)`, and a morphism
`F^{a,*}ℰ ⟶ F^{b,*}𝒢` presenting a morphism of `colim_F Vect(Y)` to its pullback, read as a
morphism `F^{a,*}f^*ℰ ⟶ F^{b,*}f^*𝒢` through the commutation of `f^*` with Frobenius pullback. -/
noncomputable def frobeniusColimitVectModelPullback :
    frobeniusColimitVectModel Y p hY ⥤ frobeniusColimitVectModel X p hX :=
  EndoColim.mapOfComm (Scheme.Vect.pullback f) (frobeniusVectPullbackIso f p hX hY)

end AlgebraicGeometry

end
