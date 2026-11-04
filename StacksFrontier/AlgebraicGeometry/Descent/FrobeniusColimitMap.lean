module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitHomReduction
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageShift

/-!
# Functoriality of the colimit category along an endofunctor

Let `F : C ⥤ C` and `F' : C' ⥤ C'` be endofunctors and let `Φ : C ⥤ C'` be a functor which
commutes with them up to a natural isomorphism `α : F ⋙ Φ ≅ Φ ⋙ F'`. This file builds the
induced functor

`colim_F C ⥤ colim_{F'} C'`

between the colimit categories of Stacks Tag 0EXA, and computes it on a morphism presented at a
level.

## Main definitions

* `CategoryTheory.EndoColim.stageShiftNatIso`: the isomorphism `(F E, n + 1) ≅ (E, n)` of Stacks
  Tag 0EXA, as a natural isomorphism `F ⋙ (stage n + 1) ≅ (stage n)` of functors `C ⥤ colim_F C`.
* `CategoryTheory.EndoColim.squareIter`: the comparison `F'^k (Φ E) ≅ Φ (F^k E)` obtained by
  iterating `α`.
* `CategoryTheory.EndoColim.transportHom`: the morphism between iterates of `F'` which a
  morphism between iterates of `F` induces, namely its image under `Φ` conjugated by
  `squareIter`.
* `CategoryTheory.EndoColim.mapPseudococone` and `CategoryTheory.EndoColim.map`: **the functor
  `colim_F C ⥤ colim_{F'} C'` induced by `Φ`.**

## Main results

* `CategoryTheory.EndoColim.shiftStepHom_naturality`: naturality of the stage shift.
* `CategoryTheory.EndoColim.objShiftIso_conj`: conjugating by the iterated stage shift turns the
  stage functor applied to a morphism of `C` between iterates into the morphism of `colim_F C`
  presented at that level.
* `CategoryTheory.EndoColim.endoRaise_transportHom`: raising the morphism of `C` raises the
  morphism of `C'` it induces.
* `CategoryTheory.EndoColim.mapPseudococone_iterObjIso`: the comparison of the stage functors
  along iterates which the pseudo-cocone of `Φ` carries is `squareIter` followed by the iterated
  stage shift.
* `CategoryTheory.EndoColim.stageFunctor_comp_map`: the induced functor restricts to `Φ` on the
  stage-`n` copy of `C`, as an equality of functors.
* `CategoryTheory.EndoColim.map_map_of`: **the induced functor sends a morphism presented at
  level `k` by `f` to the morphism presented at level `k` by `Φ f`, conjugated by
  `squareIter`.**

## Implementation notes

Every morphism of `colim_F C` here is written as `CategoryTheory.EndoColim.Hom.of` applied to a
morphism of `C`, between objects written out as pairs `(E, n)`, and never as the stage functor
applied to a morphism: `CategoryTheory.EndoColim.stageFunctor` is semireducible, so a composite
in which its action on objects occurs is well typed only up to unfolding it, and then neither
`simp` nor `rw` can reassociate the composite or rewrite inside it — the difficulty the
implementation notes of `StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitComparison`
describe. `CategoryTheory.EndoColim.stageHomOf` and `CategoryTheory.EndoColim.squareApp` are the
two repackagings this needs; the equalities `CategoryTheory.EndoColim.stageFunctor_map` and
`CategoryTheory.EndoColim.stageFunctor_obj` move between the two spellings and hold by `rfl`.

The computations with the iterated stage shift all go the same way. The shift and its inverse
are presented at level `0` by a transport of objects
(`CategoryTheory.EndoColim.objShiftIso_hom_eq` and
`CategoryTheory.EndoColim.objShiftIso_inv_eq`), so a composite with them is a single
`CategoryTheory.EndoColim.Hom.of` whose presenting morphism is read off by unfolding
`CategoryTheory.EndoColim.compHom`; `CategoryTheory.EndoColim.Hom.of_eq_of` then reduces the
identity to one between morphisms of `C`, and the two comparison lemmas
`CategoryTheory.EndoColim.endoHomCast_endoIter_map_map_comp_eq` and
`CategoryTheory.EndoColim.eqToHom_comp_endoIter_map_comp_eqToHom_eq` discharge it: both hold for
whatever exponents the two sides pass through, the side conditions being linear arithmetic.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u u₂

namespace CategoryTheory.EndoColim

variable {C : Type u} [Category.{v} C] {C' : Type u₂} [Category.{v} C']

/-! ### The stage functor, on objects and on morphisms -/

/-- The stage-`n` functor places an object of `C` at the stage `n`. -/
@[simp]
lemma stageFunctor_obj (F : C ⥤ C) (n : ℕ) (E : C) :
    (stageFunctor F n).obj E = ⟨E, n⟩ := rfl

/-- The morphism of `colim_F C` which the stage-`n` functor assigns to a morphism of `C`, with
the objects of `colim_F C` written out as pairs. Only the type is spelled differently; the
functor `CategoryTheory.EndoColim.stageFunctor` is semireducible, so a composite in which its
action on objects occurs is well typed only up to unfolding and no rewrite can see through
it. -/
def stageHomOf (F : C ⥤ C) (n : ℕ) {E G : C} (g : E ⟶ G) :
    (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, n⟩ :=
  Hom.of 0 ((F.endoIter (n + 0)).map g)

/-- The stage-`n` functor presents a morphism of `C` at level `0` by its `n`-th iterate. -/
lemma stageFunctor_map (F : C ⥤ C) (n : ℕ) {E G : C} (g : E ⟶ G) :
    (stageFunctor F n).map g = stageHomOf F n g := rfl

/-- The stage-`n` functor is functorial, in the spelled-out form. -/
lemma stageHomOf_comp (F : C ⥤ C) (n : ℕ) {E G H : C} (g : E ⟶ G) (h : G ⟶ H) :
    stageHomOf F n (g ≫ h) = stageHomOf F n g ≫ stageHomOf F n h :=
  Hom.of_endoIter_map_comp n g h

/-! ### Comparisons between iterates of a morphism of `C` -/

/-- The equality `F^a (F E) = F^b E` for exponents with `a + 1 = b`. -/
lemma endoIter_obj_obj_of_eq (F : C ⥤ C) {a b : ℕ} (h : a + 1 = b) (E : C) :
    (F.endoIter a).obj (F.obj E) = (F.endoIter b).obj E := by
  subst h; exact F.endoIter_obj_obj a E

/-- **The comparison of `F^a (F E)` with `F^{a + 1}E` is natural in `E`**, with every exponent
transported: the two composites agree as soon as the exponents of the two iterates differ
by one. -/
lemma endoHomCast_endoIter_map_map_comp_eq (F : C ⥤ C) {E G : C} (g : E ⟶ G)
    {j i m m' t t' : ℕ} (hij : j + 1 = i) (a₁ : j = m) (a₂ : j = t) (b₁ : i = t') (b₂ : i = m')
    (p : (F.endoIter t).obj (F.obj G) = (F.endoIter m').obj G)
    (p' : (F.endoIter m).obj (F.obj E) = (F.endoIter t').obj E) :
    endoHomCast a₁ a₂ ((F.endoIter j).map (F.map g)) ≫ eqToHom p =
      eqToHom p' ≫ endoHomCast b₁ b₂ ((F.endoIter i).map g) := by
  subst hij; subst a₁; subst a₂; subst b₁; subst b₂
  exact F.endoIter_map_comp_eqToHom j g

/-! ### Naturality of the stage shift -/

/-- **The stage shift is natural**, with the objects of `colim_F C` written out. The
isomorphism `(F E, n + 1) ≅ (E, n)` of Stacks Tag 0EXA is natural in `E`. -/
lemma shiftStepHom_naturality' (F : C ⥤ C) (n : ℕ) {E G : C} (g : E ⟶ G) :
    stageHomOf F (n + 1) (F.map g) ≫ shiftStepHom F n G =
      shiftStepHom F n E ≫ stageHomOf F n g := by
  show Hom.of (n + 1 + 0 + 0) _ = Hom.of (n + 0 + 0) _
  refine Hom.of_eq_of _ _ 0 1 (by omega) ?_
  simp only [compHom, endoRaise_zero, endoRaise_comp, endoRaise_endoHomCast,
    endoRaise_eqToHom, endoRaise_endoIter_map, endoHomCast_comp_rfl, endoHomCast_endoHomCast,
    endoHomCast_eqToHom]
  exact endoHomCast_endoIter_map_map_comp_eq F g (by omega) (by omega) (by omega) (by omega)
    (by omega) _ _

/-- **The stage shift is natural.** The isomorphism `(F E, n + 1) ≅ (E, n)` of Stacks Tag 0EXA
is natural in `E`. -/
lemma shiftStepHom_naturality (F : C ⥤ C) (n : ℕ) {E G : C} (g : E ⟶ G) :
    (stageFunctor F (n + 1)).map (F.map g) ≫ shiftStepHom F n G =
      shiftStepHom F n E ≫ (stageFunctor F n).map g :=
  shiftStepHom_naturality' F n g

/-- **The stage shift of Stacks Tag 0EXA as a natural isomorphism of functors `C ⥤ colim_F C`:**
the stage-`n + 1` functor precomposed with `F` is the stage-`n` functor. -/
def stageShiftNatIso (F : C ⥤ C) (n : ℕ) : F ⋙ stageFunctor F (n + 1) ≅ stageFunctor F n :=
  NatIso.ofComponents (fun E ↦ shiftStepIso F n E) fun g ↦ shiftStepHom_naturality F n g

/-- The component of the stage shift at `E` is the stage-shift morphism
`(F E, n + 1) ⟶ (E, n)`. -/
@[simp]
lemma stageShiftNatIso_hom_app (F : C ⥤ C) (n : ℕ) (E : C) :
    (stageShiftNatIso F n).hom.app E = shiftStepHom F n E := rfl

/-- The inverse component of the stage shift at `E` is the morphism `(E, n) ⟶ (F E, n + 1)`
inverse to the stage shift. -/
@[simp]
lemma stageShiftNatIso_inv_app (F : C ⥤ C) (n : ℕ) (E : C) :
    (stageShiftNatIso F n).inv.app E = shiftStepInv F n E := rfl

/-! ### Iterates of an endofunctor absorb iterates of it -/

/-- **The iterates of an endofunctor absorb one another**: `F^N (F^a E) = F^{a + N}E`. -/
lemma endoIter_obj_endoIter_obj (F : C ⥤ C) (a : ℕ) (E : C) :
    ∀ N : ℕ, (F.endoIter N).obj ((F.endoIter a).obj E) = (F.endoIter (a + N)).obj E
  | 0 => rfl
  | N + 1 => congrArg F.obj (endoIter_obj_endoIter_obj F a E N)

/-- The equality `F^N (F^a E) = F^b E` for exponents with `a + N = b`. -/
lemma endoIter_obj_endoIter_obj_of_eq (F : C ⥤ C) {N a b : ℕ} (h : a + N = b) (E : C) :
    (F.endoIter N).obj ((F.endoIter a).obj E) = (F.endoIter b).obj E := by
  subst h; exact endoIter_obj_endoIter_obj F a E N

/-- **Raising a morphism between iterates is applying an iterate of `F` to it**, up to the
comparisons of the iterates. -/
lemma endoRaise_eq_eqToHom_endoIter_map (F : C ⥤ C) {m n : ℕ} {E G : C}
    (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G) :
    ∀ (N : ℕ)
      (p : (F.endoIter (m + N)).obj E = (F.endoIter N).obj ((F.endoIter m).obj E))
      (q : (F.endoIter N).obj ((F.endoIter n).obj G) = (F.endoIter (n + N)).obj G),
      endoRaise f N = eqToHom p ≫ (F.endoIter N).map f ≫ eqToHom q
  | 0, p, q => by
      rw [endoRaise_zero]
      exact ((Category.id_comp _).trans (Category.comp_id _)).symm
  | N + 1, p, q => by
      have ih := endoRaise_eq_eqToHom_endoIter_map F f N
        (endoIter_obj_endoIter_obj_of_eq F (by omega) E).symm
        (endoIter_obj_endoIter_obj_of_eq F (by omega) G)
      show F.map (endoRaise f N) = _
      rw [ih, F.map_comp, F.map_comp, eqToHom_map, eqToHom_map]
      rfl

/-- **An iterate of `F` applied to a morphism between iterates, transported, is a raise of that
morphism**, whatever exponents the two sides pass through, as soon as the iterate and the raise
amount agree. This is the comparison which the computations with the iterated stage shift
reduce to. -/
lemma eqToHom_comp_endoIter_map_comp_eqToHom_eq (F : C ⥤ C) {a : ℕ} {E G : C}
    (h : (F.endoIter a).obj E ⟶ (F.endoIter a).obj G) {N j q s q' s' : ℕ}
    (hj : N = j) (c₁ : N = q') (c₂ : N = s') (d₁ : a + j = q) (d₂ : a + j = s)
    (p : (F.endoIter q).obj E = (F.endoIter q').obj ((F.endoIter a).obj E))
    (r : (F.endoIter s').obj ((F.endoIter a).obj G) = (F.endoIter s).obj G) :
    eqToHom p ≫ endoHomCast c₁ c₂ ((F.endoIter N).map h) ≫ eqToHom r =
      endoHomCast d₁ d₂ (endoRaise h j) := by
  subst hj; subst c₁; subst c₂; subst d₁; subst d₂
  exact (endoRaise_eq_eqToHom_endoIter_map F h N p r).symm

/-! ### The iterated stage shift, presented at level zero -/

/-- The one-step stage shift, on the nose. -/
lemma shiftStepIso_hom (F : C ⥤ C) (n : ℕ) (E : C) :
    (shiftStepIso F n E).hom = shiftStepHom F n E := rfl

/-- The inverse of the one-step stage shift, on the nose. -/
lemma shiftStepIso_inv (F : C ⥤ C) (n : ℕ) (E : C) :
    (shiftStepIso F n E).inv = shiftStepInv F n E := rfl

/-- The iterated stage shift is the one-step shift followed by the iterated shift. -/
lemma objShiftIso_succ (F : C ⥤ C) (n k : ℕ) (E : C) :
    objShiftIso F n (k + 1) E =
      shiftStepIso F (n + k) ((F.endoIter k).obj E) ≪≫ objShiftIso F n k E := rfl

/-- Composing two morphisms presented at level `0` by comparisons of objects of `C` gives the
morphism presented at level `0` by the comparison between the outer ones. -/
private lemma of_eqToHom_comp_of_eqToHom {F : C ⥤ C} {A B D : EndoColim F}
    (a : (F.endoIter (B.stage + 0)).obj A.obj = (F.endoIter (A.stage + 0)).obj B.obj)
    (b : (F.endoIter (D.stage + 0)).obj B.obj = (F.endoIter (B.stage + 0)).obj D.obj)
    (c : (F.endoIter (D.stage + 0)).obj A.obj = (F.endoIter (A.stage + 0)).obj D.obj) :
    Hom.comp (Hom.of 0 (eqToHom a)) (Hom.of 0 (eqToHom b)) = Hom.of 0 (eqToHom c) := by
  change Hom.of (B.stage + 0 + 0) _ = _
  refine Hom.of_eq_of _ _ 0 (B.stage + 0 + 0) (by omega) ?_
  simp only [compHom, endoRaise_zero, endoRaise_eqToHom, endoHomCast_eqToHom, eqToHom_trans]

/-- **The iterated stage shift `(F^k E, n + k) ≅ (E, n)` is presented at level `0`** by the
comparison of `F^{n}(F^k E) with `F^{n + k}E`. -/
lemma objShiftIso_hom_eq (F : C ⥤ C) (n : ℕ) : ∀ (k : ℕ) (E : C)
    (q : (F.endoIter (n + 0)).obj ((F.endoIter k).obj E) = (F.endoIter (n + k + 0)).obj E),
    (objShiftIso F n k E).hom = Hom.of 0 (eqToHom q)
  | 0, _, _ => rfl
  | k + 1, E, _ => by
      have hq : (F.endoIter (n + 0)).obj (F.obj ((F.endoIter k).obj E)) =
          (F.endoIter (n + k + 1 + 0)).obj E :=
        endoIter_obj_endoIter_obj_of_eq F (show k + 1 + (n + 0) = n + k + 1 + 0 by omega) E
      rw [objShiftIso_succ, Iso.trans_hom, shiftStepIso_hom,
        objShiftIso_hom_eq F n k E (endoIter_obj_endoIter_obj_of_eq F (by omega) E)]
      exact of_eqToHom_comp_of_eqToHom _ _ hq

/-- **The inverse of the iterated stage shift is presented at level `0`** by the comparison of
`F^{n + k}E` with `F^{n}(F^k E)`. -/
lemma objShiftIso_inv_eq (F : C ⥤ C) (n : ℕ) : ∀ (k : ℕ) (E : C)
    (q : (F.endoIter (n + k + 0)).obj E = (F.endoIter (n + 0)).obj ((F.endoIter k).obj E)),
    (objShiftIso F n k E).inv = Hom.of 0 (eqToHom q)
  | 0, _, _ => rfl
  | k + 1, E, _ => by
      have hq : (F.endoIter (n + k + 1 + 0)).obj E =
          (F.endoIter (n + 0)).obj (F.obj ((F.endoIter k).obj E)) :=
        (endoIter_obj_endoIter_obj_of_eq F (show k + 1 + (n + 0) = n + k + 1 + 0 by omega) E).symm
      rw [objShiftIso_succ, Iso.trans_inv, shiftStepIso_inv,
        objShiftIso_inv_eq F n k E (endoIter_obj_endoIter_obj_of_eq F (by omega) E).symm]
      exact of_eqToHom_comp_of_eqToHom _ _ hq

/-- **Conjugating by the iterated stage shift turns the stage functor applied to a morphism of
`C` between iterates into the morphism of `colim_F C` presented at that level.** -/
lemma objShiftIso_conj (F : C ⥤ C) (n k : ℕ) {E G : C}
    (h : (F.endoIter (n + k)).obj E ⟶ (F.endoIter (n + k)).obj G) :
    (objShiftIso F n (n + k) E).inv ≫ stageHomOf F (n + (n + k)) h ≫
        (objShiftIso F n (n + k) G).hom =
      (Hom.of k h : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, n⟩) := by
  have hp : (F.endoIter (n + (n + k) + 0)).obj E =
      (F.endoIter (n + 0)).obj ((F.endoIter (n + k)).obj E) :=
    (endoIter_obj_endoIter_obj_of_eq F (show n + k + (n + 0) = n + (n + k) + 0 by omega) E).symm
  have hq : (F.endoIter (n + 0)).obj ((F.endoIter (n + k)).obj G) =
      (F.endoIter (n + (n + k) + 0)).obj G :=
    endoIter_obj_endoIter_obj_of_eq F (show n + k + (n + 0) = n + (n + k) + 0 by omega) G
  rw [objShiftIso_inv_eq F n (n + k) E hp, objShiftIso_hom_eq F n (n + k) G hq, stageHomOf]
  show Hom.of (n + (n + k) + 0 + (n + (n + k) + 0 + 0)) _ = _
  refine Hom.of_eq_of _ _ 0 (4 * n + k) (by omega) ?_
  simp only [compHom, endoRaise_zero, endoRaise_comp, endoRaise_endoHomCast,
    endoRaise_eqToHom, endoRaise_endoIter_map, endoHomCast_comp_rfl, endoHomCast_endoHomCast,
    endoHomCast_eqToHom]
  exact eqToHom_comp_endoIter_map_comp_eqToHom_eq F h (by omega) (by omega) (by omega)
    (by omega) (by omega) _ _

/-! ### The iterated comparison of a functor commuting with the endofunctors -/

section Square

variable (F : C ⥤ C) (F' : C' ⥤ C') (Φ : C ⥤ C') (α : F ⋙ Φ ≅ Φ ⋙ F')

/-- The comparison `F'^k (Φ E) ≅ Φ (F^k E)` obtained by iterating `α`. -/
def squareIter : ∀ (k : ℕ) (E : C),
    (F'.endoIter k).obj (Φ.obj E) ≅ Φ.obj ((F.endoIter k).obj E)
  | 0, _ => Iso.refl _
  | k + 1, E => F'.mapIso (squareIter k E) ≪≫ (α.app ((F.endoIter k).obj E)).symm

/-- The `0`-th iterated comparison is the identity of `Φ E`. -/
@[simp]
lemma squareIter_zero (E : C) : squareIter F F' Φ α 0 E = Iso.refl _ := rfl

/-- The `(k + 1)`-st iterated comparison applies `F'` to the `k`-th one and then the inverse
of `α` at `F^k E`. -/
lemma squareIter_succ_hom (k : ℕ) (E : C) :
    (squareIter F F' Φ α (k + 1) E).hom =
      F'.map (squareIter F F' Φ α k E).hom ≫ α.inv.app ((F.endoIter k).obj E) := rfl

/-- The inverse of the `(k + 1)`-st iterated comparison is `α` at `F^k E` followed by `F'`
applied to the inverse of the `k`-th one. -/
lemma squareIter_succ_inv (k : ℕ) (E : C) :
    (squareIter F F' Φ α (k + 1) E).inv =
      α.hom.app ((F.endoIter k).obj E) ≫ F'.map (squareIter F F' Φ α k E).inv := rfl

/-- **The iterated comparison is natural in the object.** -/
lemma squareIter_hom_naturality : ∀ (k : ℕ) {E G : C} (g : E ⟶ G),
    (F'.endoIter k).map (Φ.map g) ≫ (squareIter F F' Φ α k G).hom =
      (squareIter F F' Φ α k E).hom ≫ Φ.map ((F.endoIter k).map g)
  | 0, _, _, _ => (Category.comp_id _).trans (Category.id_comp _).symm
  | k + 1, E, G, g => by
      have ih := squareIter_hom_naturality k g
      have hnat := α.inv.naturality ((F.endoIter k).map g)
      simp only [Functor.comp_map] at hnat
      show F'.map ((F'.endoIter k).map (Φ.map g)) ≫
          (F'.map (squareIter F F' Φ α k G).hom ≫ α.inv.app ((F.endoIter k).obj G)) =
        (F'.map (squareIter F F' Φ α k E).hom ≫ α.inv.app ((F.endoIter k).obj E)) ≫
          Φ.map (F.map ((F.endoIter k).map g))
      rw [← Category.assoc, ← F'.map_comp, ih, F'.map_comp, Category.assoc, Category.assoc,
        hnat]

/-- The morphism of `C'` which a morphism of `C` between iterates of `F` induces: the image of
the morphism under `Φ`, conjugated by the iterated comparison. -/
def transportHom (a : ℕ) {E G : C}
    (f : (F.endoIter a).obj E ⟶ (F.endoIter a).obj G) :
    (F'.endoIter a).obj (Φ.obj E) ⟶ (F'.endoIter a).obj (Φ.obj G) :=
  (squareIter F F' Φ α a E).hom ≫ Φ.map f ≫ (squareIter F F' Φ α a G).inv

/-- **Applying `F'` to the induced morphism is the morphism induced by one application of
`F`.** -/
lemma map_transportHom (a : ℕ) {E G : C}
    (f : (F.endoIter a).obj E ⟶ (F.endoIter a).obj G) :
    F'.map (transportHom F F' Φ α a f) = transportHom F F' Φ α (a + 1) (endoRaise f 1) := by
  have hnat := α.inv.naturality f
  simp only [Functor.comp_map] at hnat
  have key : α.inv.app ((F.endoIter a).obj E) ≫ Φ.map (F.map f) ≫
      α.hom.app ((F.endoIter a).obj G) = F'.map (Φ.map f) := by
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  show F'.map ((squareIter F F' Φ α a E).hom ≫ Φ.map f ≫ (squareIter F F' Φ α a G).inv) =
    (F'.map (squareIter F F' Φ α a E).hom ≫ α.inv.app ((F.endoIter a).obj E)) ≫
      Φ.map (F.map f) ≫
        α.hom.app ((F.endoIter a).obj G) ≫ F'.map (squareIter F F' Φ α a G).inv
  rw [F'.map_comp, F'.map_comp, Category.assoc, reassoc_of% key]

/-- **Raising the morphism of `C` raises the morphism of `C'` it induces.** -/
lemma endoRaise_transportHom (a : ℕ) {E G : C}
    (f : (F.endoIter a).obj E ⟶ (F.endoIter a).obj G) :
    ∀ j : ℕ, endoRaise (transportHom F F' Φ α a f) j =
      transportHom F F' Φ α (a + j) (endoRaise f j)
  | 0 => rfl
  | j + 1 => by
      show F'.map (endoRaise (transportHom F F' Φ α a f) j) =
        transportHom F F' Φ α (a + j + 1) (endoRaise (endoRaise f j) 1)
      rw [endoRaise_transportHom a f j]
      exact map_transportHom F F' Φ α (a + j) (endoRaise f j)

end Square

/-! ### The induced functor between the colimit categories -/

section Map

variable (F : C ⥤ C) (F' : C' ⥤ C') (Φ : C ⥤ C') (α : F ⋙ Φ ≅ Φ ⋙ F')

/-- The pseudo-cocone with summit `colim_{F'} C'` determined by `Φ`: at the stage `n` the
functor `Φ` followed by the stage-`n` functor of `colim_{F'} C'`, the comparison being `α`
followed by the stage shift of `colim_{F'} C'`. -/
def mapPseudococone : Pseudococone F (EndoColim F') where
  stage n := Φ ⋙ stageFunctor F' n
  compat n :=
    (Functor.associator F Φ (stageFunctor F' (n + 1))).symm ≪≫
      Functor.isoWhiskerRight α (stageFunctor F' (n + 1)) ≪≫
        Functor.associator Φ F' (stageFunctor F' (n + 1)) ≪≫
          Functor.isoWhiskerLeft Φ (stageShiftNatIso F' n)

/-- **The functor `colim_F C ⥤ colim_{F'} C'` induced by a functor `Φ : C ⥤ C'` which commutes
with the two endofunctors up to the natural isomorphism `α`.** It takes the object `(E, n)` to
`(Φ E, n)`. -/
def map : EndoColim F ⥤ EndoColim F' :=
  (mapPseudococone F F' Φ α).desc

/-- The induced functor takes the object `(E, n)` of `colim_F C` to `(Φ E, n)`. -/
@[simp]
lemma map_obj (E : C) (n : ℕ) :
    (map F F' Φ α).obj ⟨E, n⟩ = ⟨Φ.obj E, n⟩ := rfl

/-- **The induced functor restricts to `Φ` on the stage-`n` copy of `C`**, as an equality of
functors: placing an object at the stage `n` and then transporting is transporting and then
placing at the stage `n`. -/
lemma stageFunctor_comp_map (n : ℕ) :
    stageFunctor F n ⋙ map F F' Φ α = Φ ⋙ stageFunctor F' n :=
  (mapPseudococone F F' Φ α).stageFunctor_comp_desc n

/-- The comparison `α` at an object, with the two objects it connects written out. -/
def squareApp (Y : C) : Φ.obj (F.obj Y) ⟶ F'.obj (Φ.obj Y) := α.hom.app Y

/-- The comparison which the pseudo-cocone of
`CategoryTheory.EndoColim.mapPseudococone` carries, at an iterate of `F`: the image under `α`
of the object, followed by one stage shift of `colim_{F'} C'`. -/
lemma mapPseudococone_compatIter_hom (n k : ℕ) (E : C) :
    ((mapPseudococone F F' Φ α).compatIter n k E).hom =
      stageHomOf F' (n + k + 1) (squareApp F F' Φ α ((F.endoIter k).obj E)) ≫
        shiftStepHom F' (n + k) (Φ.obj ((F.endoIter k).obj E)) := by
  simp only [Pseudococone.compatIter, mapPseudococone, Iso.app_hom, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, stageShiftNatIso_hom_app, Functor.comp_obj, stageFunctor_obj,
    Category.id_comp]
  rfl

end Map

/-! ### The iterated comparison carried by the induced pseudo-cocone -/

section MapIso

variable (F : C ⥤ C) (F' : C' ⥤ C') (Φ : C ⥤ C') (α : F ⋙ Φ ≅ Φ ⋙ F')

/-- **The comparison of the stage functors along iterates which the pseudo-cocone of
`CategoryTheory.EndoColim.mapPseudococone` carries** is the iterated comparison `squareIter`
followed by the iterated stage shift of `colim_{F'} C'`. -/
lemma mapPseudococone_iterObjIso_hom (n : ℕ) : ∀ (k : ℕ) (E : C),
    ((mapPseudococone F F' Φ α).iterObjIso n k E).hom =
      stageHomOf F' (n + k) (squareIter F F' Φ α k E).inv ≫
        (objShiftIso F' n k (Φ.obj E)).hom
  | 0, E => by
      show 𝟙 _ = stageHomOf F' (n + 0) (𝟙 _) ≫ 𝟙 _
      rw [Category.comp_id, stageHomOf, Functor.map_id]
      exact (Hom.of_id _ 0).symm
  | k + 1, E => by
      rw [Pseudococone.iterObjIso_succ_hom, mapPseudococone_compatIter_hom,
        mapPseudococone_iterObjIso_hom n k E]
      show (stageHomOf F' (n + k + 1) (squareApp F F' Φ α ((F.endoIter k).obj E)) ≫
            shiftStepHom F' (n + k) (Φ.obj ((F.endoIter k).obj E))) ≫
          stageHomOf F' (n + k) (squareIter F F' Φ α k E).inv ≫
            (objShiftIso F' n k (Φ.obj E)).hom =
        stageHomOf F' (n + k + 1)
            (squareApp F F' Φ α ((F.endoIter k).obj E) ≫
              F'.map (squareIter F F' Φ α k E).inv) ≫
          shiftStepHom F' (n + k) ((F'.endoIter k).obj (Φ.obj E)) ≫
            (objShiftIso F' n k (Φ.obj E)).hom
      rw [stageHomOf_comp]
      simp only [Category.assoc]
      rw [reassoc_of% (shiftStepHom_naturality' F' (n + k) (squareIter F F' Φ α k E).inv)]

/-- The isomorphism form of
`CategoryTheory.EndoColim.mapPseudococone_iterObjIso_hom`. -/
lemma mapPseudococone_iterObjIso (n k : ℕ) (E : C) :
    (mapPseudococone F F' Φ α).iterObjIso n k E =
      (stageFunctor F' (n + k)).mapIso (squareIter F F' Φ α k E).symm ≪≫
        objShiftIso F' n k (Φ.obj E) :=
  Iso.ext (mapPseudococone_iterObjIso_hom F F' Φ α n k E)

/-- The inverse of the comparison which the pseudo-cocone of
`CategoryTheory.EndoColim.mapPseudococone` carries. -/
lemma mapPseudococone_iterObjIso_inv (n k : ℕ) (E : C) :
    ((mapPseudococone F F' Φ α).iterObjIso n k E).inv =
      (objShiftIso F' n k (Φ.obj E)).inv ≫
        stageHomOf F' (n + k) (squareIter F F' Φ α k E).hom :=
  congrArg Iso.inv (mapPseudococone_iterObjIso F F' Φ α n k E)

/-- **The induced functor sends the morphism presented at level `k` by `f` to the morphism
presented at level `k` by `Φ f`, conjugated by the iterated comparison.** -/
lemma map_map_of (n k : ℕ) {E G : C}
    (f : (F.endoIter (n + k)).obj E ⟶ (F.endoIter (n + k)).obj G) :
    (map F F' Φ α).map (Hom.of k f : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, n⟩) =
      (Hom.of k (transportHom F F' Φ α (n + k) f) :
        (⟨Φ.obj E, n⟩ : EndoColim F') ⟶ ⟨Φ.obj G, n⟩) := by
  have h1 : (map F F' Φ α).map (Hom.of k f : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, n⟩) =
      ((objShiftIso F' n (n + k) (Φ.obj E)).inv ≫
          stageHomOf F' (n + (n + k)) (squareIter F F' Φ α (n + k) E).hom) ≫
        stageHomOf F' (n + (n + k)) (Φ.map f) ≫
          (stageHomOf F' (n + (n + k)) (squareIter F F' Φ α (n + k) G).inv ≫
            (objShiftIso F' n (n + k) (Φ.obj G)).hom) := by
    rw [← mapPseudococone_iterObjIso_inv, ← mapPseudococone_iterObjIso_hom]
    exact Pseudococone.homMap_of_equalStage (mapPseudococone F F' Φ α) n k f
  have h2 : ((objShiftIso F' n (n + k) (Φ.obj E)).inv ≫
          stageHomOf F' (n + (n + k)) (squareIter F F' Φ α (n + k) E).hom) ≫
        stageHomOf F' (n + (n + k)) (Φ.map f) ≫
          (stageHomOf F' (n + (n + k)) (squareIter F F' Φ α (n + k) G).inv ≫
            (objShiftIso F' n (n + k) (Φ.obj G)).hom) =
      (objShiftIso F' n (n + k) (Φ.obj E)).inv ≫
        stageHomOf F' (n + (n + k)) (transportHom F F' Φ α (n + k) f) ≫
          (objShiftIso F' n (n + k) (Φ.obj G)).hom := by
    rw [transportHom, stageHomOf_comp, stageHomOf_comp]
    simp only [Category.assoc]
  rw [h1, h2]
  exact objShiftIso_conj F' n k (transportHom F F' Φ α (n + k) f)

end MapIso

end CategoryTheory.EndoColim

end
