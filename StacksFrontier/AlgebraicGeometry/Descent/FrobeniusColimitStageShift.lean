module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitComparison
public import StacksFrontier.CategoryTheory.Sites.Stackification.ExtensionFullyFaithful

/-!
# Shifting the stage of an object of the colimit category along an endofunctor

Let `F : C ⥤ C` be an endofunctor and let `colim_F C` be the colimit category of Stacks Tag
0EXA, whose objects are the pairs `(E, n)`. Stacks Tag 0EXA records that `(E, n)` and
`(F E, n + 1)` are isomorphic in `colim_F C`; iterating, `(E, n) ≅ (F^k E, n + k)`. This file
constructs those isomorphisms and proves that a functor out of `colim_F C` is fully faithful as
soon as it is bijective on the Hom-sets between objects presented at one and the same stage.

## Main definitions

* `CategoryTheory.EndoColim.shiftStepHom` and `CategoryTheory.EndoColim.shiftStepInv`: the two
  mutually inverse morphisms between `(F E, n + 1)` and `(E, n)`, each presented at level `0` by
  the comparison of `F^{n}(F E)` with `F^{n + 1}E`.
* `CategoryTheory.EndoColim.shiftStepIso`: the isomorphism `(F E, n + 1) ≅ (E, n)`.
* `CategoryTheory.EndoColim.objShiftIso`: **the isomorphism `(F^k E, n + k) ≅ (E, n)`**, the
  one-step isomorphism iterated.
* `CategoryTheory.EndoColim.stageCastIso`: the isomorphism `(E, a) ≅ (E, b)` for equal stages.

## Main results

* `CategoryTheory.Functor.endoIter_obj_obj`: the iterates of an endofunctor absorb one
  application of it, `F^a (F E) = F^{a + 1} E`.
* `CategoryTheory.EndoColim.bijective_desc_map`: **bijectivity of a functor out of `colim_F C`
  on the Hom-sets between objects at one common stage implies bijectivity on all of them.**
* `CategoryTheory.EndoColim.Pseudococone.faithful_desc_of_bijective_equalStage` and
  `CategoryTheory.EndoColim.Pseudococone.full_desc_of_bijective_equalStage`: **the functor
  determined by a pseudo-cocone is faithful, respectively full, as soon as it is bijective on
  the Hom-sets between objects at one common stage.**

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u u₂

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {F : C ⥤ C}

/-! ### Iterates of an endofunctor absorb one application of it -/

/-- **The iterates of an endofunctor absorb one application of it**: `F^a (F E) = F^{a + 1}E`. -/
lemma Functor.endoIter_obj_obj (F : C ⥤ C) (a : ℕ) (E : C) :
    (F.endoIter a).obj (F.obj E) = (F.endoIter (a + 1)).obj E := by
  induction a with
  | zero => rfl
  | succ a ih => exact congrArg F.obj ih

/-- **The comparison of `F^a (F E)` with `F^{a + 1}E` is natural in `E`.** -/
lemma Functor.endoIter_map_comp_eqToHom (F : C ⥤ C) (a : ℕ) {E G : C} (f : E ⟶ G) :
    (F.endoIter a).map (F.map f) ≫ eqToHom (F.endoIter_obj_obj a G) =
      eqToHom (F.endoIter_obj_obj a E) ≫ (F.endoIter (a + 1)).map f := by
  induction a with
  | zero => exact (Category.comp_id _).trans (Category.id_comp _).symm
  | succ a ih =>
      have h := congrArg (fun t ↦ F.map t) ih
      simp only [Functor.map_comp, eqToHom_map] at h
      exact h

/-! ### Raising and transporting a transport of objects -/

/-- An equality between iterates of `F` evaluated at two objects, raised by adding to both
exponents. -/
lemma endoIter_obj_eq_raise {E G : C} {m n : ℕ}
    (q : (F.endoIter m).obj E = (F.endoIter n).obj G) :
    ∀ i : ℕ, (F.endoIter (m + i)).obj E = (F.endoIter (n + i)).obj G
  | 0 => q
  | i + 1 => congrArg F.obj (endoIter_obj_eq_raise q i)

/-- **Raising a transport of objects gives a transport of objects.** -/
lemma endoRaise_eqToHom {E G : C} {m n : ℕ}
    (q : (F.endoIter m).obj E = (F.endoIter n).obj G) :
    ∀ i : ℕ, endoRaise (eqToHom q) i = eqToHom (endoIter_obj_eq_raise q i)
  | 0 => rfl
  | i + 1 => by
      rw [endoRaise_succ, endoRaise_eqToHom q i]
      exact eqToHom_map F _

/-- **Transporting the exponents of a transport of objects gives a transport of objects.** -/
lemma endoHomCast_eqToHom {E G : C} {m n m' n' : ℕ} (hm : m = m') (hn : n = n')
    (q : (F.endoIter m).obj E = (F.endoIter n).obj G) :
    endoHomCast hm hn (eqToHom q) =
      eqToHom (show (F.endoIter m').obj E = (F.endoIter n').obj G by
        subst hm; subst hn; exact q) := by
  subst hm; subst hn; rfl

namespace EndoColim

/-! ### The identity morphism presented at an arbitrary level -/

/-- **The identity of `(E, n)` presented at any level.** -/
lemma Hom.of_id (A : EndoColim F) (k : ℕ) :
    Hom.of k (𝟙 ((F.endoIter (A.stage + k)).obj A.obj)) = 𝟙 A := by
  show Hom.of k _ = Hom.of 0 _
  refine Hom.of_eq_of _ _ 0 k (by omega) ?_
  rw [endoRaise_zero, endoRaise_id]
  exact (endoHomCast_id _).trans (endoHomCast_id _).symm

/-! ### The one-step shift of the stage -/

/-- The morphism `(F E, n + 1) ⟶ (E, n)` of `colim_F C`, presented at level `0` by the
comparison of `F^{n}(F E)` with `F^{n + 1}E`. -/
def shiftStepHom (F : C ⥤ C) (n : ℕ) (E : C) :
    (⟨F.obj E, n + 1⟩ : EndoColim F) ⟶ ⟨E, n⟩ :=
  Hom.of 0 (eqToHom (F.endoIter_obj_obj (n + 0) E))

/-- The morphism `(E, n) ⟶ (F E, n + 1)` of `colim_F C`, presented at level `0` by the
comparison of `F^{n + 1}E` with `F^{n}(F E)`. -/
def shiftStepInv (F : C ⥤ C) (n : ℕ) (E : C) :
    (⟨E, n⟩ : EndoColim F) ⟶ ⟨F.obj E, n + 1⟩ :=
  Hom.of 0 (eqToHom (F.endoIter_obj_obj (n + 0) E).symm)

/-- The two morphisms between `(F E, n + 1)` and `(E, n)` compose to the identity of
`(F E, n + 1)`. -/
lemma shiftStepHom_comp_shiftStepInv (F : C ⥤ C) (n : ℕ) (E : C) :
    shiftStepHom F n E ≫ shiftStepInv F n E = 𝟙 _ := by
  show Hom.of (n + 0 + 0) _ = _
  rw [← Hom.of_id (⟨F.obj E, n + 1⟩ : EndoColim F) (n + 0 + 0)]
  refine congrArg (Hom.of (n + 0 + 0)) ?_
  simp only [compHom, endoRaise_eqToHom, endoHomCast_eqToHom, eqToHom_trans]
  rfl

/-- The two morphisms between `(F E, n + 1)` and `(E, n)` compose to the identity of
`(E, n)`. -/
lemma shiftStepInv_comp_shiftStepHom (F : C ⥤ C) (n : ℕ) (E : C) :
    shiftStepInv F n E ≫ shiftStepHom F n E = 𝟙 _ := by
  show Hom.of (n + 1 + 0 + 0) _ = _
  rw [← Hom.of_id (⟨E, n⟩ : EndoColim F) (n + 1 + 0 + 0)]
  refine congrArg (Hom.of (n + 1 + 0 + 0)) ?_
  simp only [compHom, endoRaise_eqToHom, endoHomCast_eqToHom, eqToHom_trans]
  rfl

/-- **The object `(F E, n + 1)` of `colim_F C` is isomorphic to `(E, n)`.** This is the
isomorphism of Stacks Tag 0EXA which makes `F` invertible on the colimit category. -/
def shiftStepIso (F : C ⥤ C) (n : ℕ) (E : C) :
    (⟨F.obj E, n + 1⟩ : EndoColim F) ≅ ⟨E, n⟩ where
  hom := shiftStepHom F n E
  inv := shiftStepInv F n E
  hom_inv_id := shiftStepHom_comp_shiftStepInv F n E
  inv_hom_id := shiftStepInv_comp_shiftStepHom F n E

/-- **The object `(F^k E, n + k)` of `colim_F C` is isomorphic to `(E, n)`**, by the one-step
isomorphism iterated. -/
def objShiftIso (F : C ⥤ C) (n : ℕ) : ∀ (k : ℕ) (E : C),
    (⟨(F.endoIter k).obj E, n + k⟩ : EndoColim F) ≅ ⟨E, n⟩
  | 0, E => Iso.refl (⟨E, n⟩ : EndoColim F)
  | k + 1, E => shiftStepIso F (n + k) ((F.endoIter k).obj E) ≪≫ objShiftIso F n k E

/-- Two objects of `colim_F C` with the same underlying object and equal stages are
isomorphic. -/
def stageCastIso (F : C ⥤ C) (E : C) {a b : ℕ} (h : a = b) :
    (⟨E, a⟩ : EndoColim F) ≅ ⟨E, b⟩ :=
  eqToIso (congrArg (fun k ↦ (⟨E, k⟩ : EndoColim F)) h)

/-! ### Fully faithfulness from the Hom-sets at a common stage -/

variable {D : Type u₂} [Category.{v} D]

/-- **A functor out of `colim_F C` which is bijective on the Hom-sets between objects presented
at one and the same stage is bijective on all of them.** -/
theorem bijective_desc_map (K : EndoColim F ⥤ D)
    (h : ∀ (n : ℕ) (E G : C),
      Function.Bijective (fun u : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, n⟩ ↦ K.map u))
    (A B : EndoColim F) : Function.Bijective (fun u : A ⟶ B ↦ K.map u) := by
  obtain ⟨E, n⟩ := A
  obtain ⟨G, m⟩ := B
  exact Functor.bijective_map_of_isos K (objShiftIso F n m E)
    (stageCastIso F ((F.endoIter n).obj G) (Nat.add_comm n m) ≪≫ objShiftIso F m n G)
    (h (n + m) ((F.endoIter m).obj E) ((F.endoIter n).obj G))

namespace Pseudococone

variable (P : Pseudococone F D)

/-- **The functor determined by a pseudo-cocone is faithful** as soon as it is bijective on the
Hom-sets between objects presented at one and the same stage. -/
theorem faithful_desc_of_bijective_equalStage
    (h : ∀ (n : ℕ) (E G : C),
      Function.Bijective (fun u : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, n⟩ ↦ P.desc.map u)) :
    P.desc.Faithful where
  map_injective {A B} := (bijective_desc_map P.desc h A B).1

/-- **The functor determined by a pseudo-cocone is full** as soon as it is bijective on the
Hom-sets between objects presented at one and the same stage. -/
theorem full_desc_of_bijective_equalStage
    (h : ∀ (n : ℕ) (E G : C),
      Function.Bijective (fun u : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, n⟩ ↦ P.desc.map u)) :
    P.desc.Full where
  map_surjective {A B} := (bijective_desc_map P.desc h A B).2

end Pseudococone

end EndoColim

end CategoryTheory

end
