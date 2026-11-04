module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageShift

/-!
# The Hom-sets of the comparison functor of Stacks Tag 0EXB

Let `p` be a prime, let `X` be a scheme in characteristic `p` and write `F` for pullback along
the absolute Frobenius and `S_n` for extension of scalars along the stage-`n` coprojection
`𝒪_X ⟶ colim_F 𝒪_X`. The comparison functor of Stacks Tag 0EXB,
`AlgebraicGeometry.frobeniusColimitVectComparison`, takes the object `(ℰ, n)` of
`colim_F Vect(X)` to `S_n ℰ`. On a morphism from `(ℰ, n)` to `(𝒢, n)` presented at level `k` —
that is, on a morphism `F^{n + k, *}ℰ ⟶ F^{n + k, *}𝒢` of `Vect(X)` — it acts by
`AlgebraicGeometry.frobeniusStageHomMap`, which this file records.

Together with the reduction to a single stage of
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageShift` this reduces the full
faithfulness half of Tag 0EXB to one statement about the Hom-sets of `Vect(X)`: **the canonical
map**

`colim_k Hom_X(F^{n + k, *}ℰ, F^{n + k, *}𝒢) → Hom_{colim_F 𝒪_X}(S_n ℰ, S_n 𝒢)`

**given by `AlgebraicGeometry.frobeniusStageHomMap` is bijective.** Injectivity is phrased as it
must be for a colimit of Hom-sets: two presentations with the same image agree after being
raised, which is `CategoryTheory.EndoColim.HomRep.Agree`.

## Main results

* `AlgebraicGeometry.frobeniusColimitVectPseudococone_iterObjIso`: the comparison of the stage
  functors along iterated Frobenius pullback which the pseudo-cocone of Tag 0EXB carries is
  `AlgebraicGeometry.frobeniusStageFunctorIterIso`.
* `AlgebraicGeometry.frobeniusColimitVectComparison_map_of`: **the comparison functor acts on a
  morphism presented at level `k` by `AlgebraicGeometry.frobeniusStageHomMap`.**
* `AlgebraicGeometry.bijective_frobeniusColimitVectComparison_map`: **bijectivity of the
  comparison on each Hom-set of `colim_F Vect(X)`**, from bijectivity of the map out of
  `colim_k Hom_X(F^{n + k, *}ℰ, F^{n + k, *}𝒢)`.
* `AlgebraicGeometry.faithful_frobeniusColimitVectComparison_of_stageHomMap` and
  `AlgebraicGeometry.full_frobeniusColimitVectComparison_of_stageHomMap`: **the comparison
  functor of Tag 0EXB is faithful, respectively full, as soon as that map is bijective.**

## Implementation notes

The two hypotheses are exactly injectivity and surjectivity of the map out of the sequential
colimit of Hom-sets, and nothing else: no finiteness, no affineness and no hypothesis on `X`
beyond the ones Tag 0EXB carries appears in them. They are stated for a Hom-set whose two
objects are presented at the same stage `n`, which is all that is needed — the general case is
reduced to it by
`CategoryTheory.EndoColim.Pseudococone.faithful_desc_of_bijective_equalStage`.

`AlgebraicGeometry.frobeniusStageHomMap` is indexed by the absolute exponent `n + k` rather than
by the level `k`, because that is the exponent of the morphism of `Vect(X)` which presents the
morphism of `colim_F Vect(X)`; a morphism from `(ℰ, n)` to `(𝒢, n)` at level `k` is a morphism
between the `(n + k)`-fold Frobenius pullbacks.

What remains unproved is the bijectivity itself, which is where the quasi-compactness and
quasi-separatedness of `X` and the finite local freeness of `ℰ` enter. See the implementation
notes of `StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundles` for the input it
still needs.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe v u

namespace CategoryTheory.EndoColim

variable {C : Type u} [Category.{v} C] {F : C ⥤ C}

/-- **Two presentations whose raises by a common amount agree, agree.** -/
lemma HomRep.agree_of_endoRaise_eq {A B : EndoColim F} {k : ℕ}
    {f g : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj}
    (j : ℕ) (h : endoRaise f j = endoRaise g j) :
    HomRep.Agree (⟨k, f⟩ : HomRep A B) ⟨k, g⟩ := by
  refine ⟨j, j, rfl, ?_⟩
  rw [h]

variable {D : Type*} [Category D]

/-- **The morphism of `D` induced by a presentation of a morphism between two objects of
`colim_F C` placed at the same stage.** The comparison of the stage functors at equal indices,
which `CategoryTheory.EndoColim.Pseudococone.mapAt` inserts in general, is an identity here. -/
lemma Pseudococone.homMap_of_equalStage (P : Pseudococone F D) (n k : ℕ) {E G : C}
    (f : (F.endoIter (n + k)).obj E ⟶ (F.endoIter (n + k)).obj G) :
    P.homMap (Hom.of k f : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, n⟩) =
      (P.iterObjIso n (n + k) E).inv ≫ (P.stage (n + (n + k))).map f ≫
        (P.iterObjIso n (n + k) G).hom := by
  show (P.iterObjIso n (n + k) E).inv ≫ (P.stage (n + (n + k))).map f ≫
      (P.stageHom (rfl : n + (n + k) = n + (n + k))).app ((F.endoIter (n + k)).obj G) ≫
        (P.iterObjIso n (n + k) G).hom = _
  rw [Pseudococone.stageHom_refl]
  simp

end CategoryTheory.EndoColim

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-! ### The comparison on a Hom-set, at a fixed level -/

/-- **The comparison of the stage functors along iterated Frobenius pullback carried by the
pseudo-cocone of Tag 0EXB is `AlgebraicGeometry.frobeniusStageFunctorIterIso`.** -/
lemma frobeniusColimitVectPseudococone_iterObjIso_hom (n k : ℕ) (E : X.Vect) :
    ((frobeniusColimitVectPseudococone X p hX).iterObjIso n k E).hom =
      (frobeniusStageFunctorIterIso X p hX n k).hom.app E := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [EndoColim.Pseudococone.iterObjIso_succ_hom, ih, frobeniusStageFunctorIterIso_succ]
      simp only [EndoColim.Pseudococone.compatIter, frobeniusColimitVectPseudococone,
        Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
        Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
      exact (Category.id_comp _).symm

/-- The pseudo-cocone of Tag 0EXB carries `AlgebraicGeometry.frobeniusStageFunctorIterIso`, as
an equality of isomorphisms. -/
lemma frobeniusColimitVectPseudococone_iterObjIso (n k : ℕ) (E : X.Vect) :
    (frobeniusColimitVectPseudococone X p hX).iterObjIso n k E =
      (frobeniusStageFunctorIterIso X p hX n k).app E :=
  Iso.ext (frobeniusColimitVectPseudococone_iterObjIso_hom X p hX n k E)

/-- The inverse half of
`AlgebraicGeometry.frobeniusColimitVectPseudococone_iterObjIso_hom`. -/
lemma frobeniusColimitVectPseudococone_iterObjIso_inv (n k : ℕ) (E : X.Vect) :
    ((frobeniusColimitVectPseudococone X p hX).iterObjIso n k E).inv =
      (frobeniusStageFunctorIterIso X p hX n k).inv.app E :=
  congrArg Iso.inv (frobeniusColimitVectPseudococone_iterObjIso X p hX n k E)

/-- **The comparison functor of Tag 0EXB acts on a morphism of `colim_F Vect(X)` between two
objects presented at the same stage `n`, itself presented at level `k`, by
`AlgebraicGeometry.frobeniusStageHomMap`.** -/
lemma frobeniusColimitVectComparison_map_of (n k : ℕ) {E G : X.Vect}
    (f : (frobeniusPullbackIter X p hX (n + k)).obj E ⟶
      (frobeniusPullbackIter X p hX (n + k)).obj G) :
    (frobeniusColimitVectComparison X p hX).map
        (EndoColim.Hom.of k f : (⟨E, n⟩ : frobeniusColimitVectModel X p hX) ⟶ ⟨G, n⟩) =
      frobeniusStageHomMap X p hX n (n + k) f := by
  have key := EndoColim.Pseudococone.homMap_of_equalStage
    (frobeniusColimitVectPseudococone X p hX) n k f
  rw [frobeniusColimitVectPseudococone_iterObjIso_inv,
    frobeniusColimitVectPseudococone_iterObjIso_hom] at key
  exact key

/-! ### Fully faithfulness from bijectivity on the colimit of Hom-sets -/

/-- **The comparison functor of Tag 0EXB is bijective on every Hom-set of `colim_F Vect(X)`
between objects presented at the same stage**, as soon as the map out of the sequential colimit
`colim_k Hom_X(F^{n + k, *}ℰ, F^{n + k, *}𝒢)` given by
`AlgebraicGeometry.frobeniusStageHomMap` is injective and surjective. -/
theorem bijective_frobeniusColimitVectComparison_map_equalStage
    (hinj : ∀ (n k l : ℕ) (E G : X.Vect)
      (f : (frobeniusPullbackIter X p hX (n + k)).obj E ⟶
        (frobeniusPullbackIter X p hX (n + k)).obj G)
      (g : (frobeniusPullbackIter X p hX (n + l)).obj E ⟶
        (frobeniusPullbackIter X p hX (n + l)).obj G),
      frobeniusStageHomMap X p hX n (n + k) f = frobeniusStageHomMap X p hX n (n + l) g →
      EndoColim.HomRep.Agree
        (⟨k, f⟩ : EndoColim.HomRep (⟨E, n⟩ : frobeniusColimitVectModel X p hX) ⟨G, n⟩) ⟨l, g⟩)
    (hsurj : ∀ (n : ℕ) (E G : X.Vect)
      (w : (frobeniusStageFunctor X p hX n).obj E ⟶ (frobeniusStageFunctor X p hX n).obj G),
      ∃ (k : ℕ) (f : (frobeniusPullbackIter X p hX (n + k)).obj E ⟶
        (frobeniusPullbackIter X p hX (n + k)).obj G),
        frobeniusStageHomMap X p hX n (n + k) f = w)
    (n : ℕ) (E G : X.Vect) :
    Function.Bijective (fun u : (⟨E, n⟩ : frobeniusColimitVectModel X p hX) ⟶ ⟨G, n⟩ ↦
      (frobeniusColimitVectComparison X p hX).map u) := by
  refine ⟨fun u v huv => ?_, fun w => ?_⟩
  · obtain ⟨k, f, rfl⟩ := EndoColim.Hom.exists_of u
    obtain ⟨l, g, rfl⟩ := EndoColim.Hom.exists_of v
    exact (EndoColim.Hom.of_eq_of_iff f g).2 (hinj n k l E G f g
      ((frobeniusColimitVectComparison_map_of X p hX n k f).symm.trans
        (huv.trans (frobeniusColimitVectComparison_map_of X p hX n l g))))
  · obtain ⟨k, f, hf⟩ := hsurj n E G w
    exact ⟨EndoColim.Hom.of k f, (frobeniusColimitVectComparison_map_of X p hX n k f).trans hf⟩

/-- **The comparison functor of Stacks Tag 0EXB is faithful** as soon as the map out of the
sequential colimit `colim_k Hom_X(F^{n + k, *}ℰ, F^{n + k, *}𝒢)` given by
`AlgebraicGeometry.frobeniusStageHomMap` is injective and surjective. -/
theorem faithful_frobeniusColimitVectComparison_of_stageHomMap
    (hinj : ∀ (n k l : ℕ) (E G : X.Vect)
      (f : (frobeniusPullbackIter X p hX (n + k)).obj E ⟶
        (frobeniusPullbackIter X p hX (n + k)).obj G)
      (g : (frobeniusPullbackIter X p hX (n + l)).obj E ⟶
        (frobeniusPullbackIter X p hX (n + l)).obj G),
      frobeniusStageHomMap X p hX n (n + k) f = frobeniusStageHomMap X p hX n (n + l) g →
      EndoColim.HomRep.Agree
        (⟨k, f⟩ : EndoColim.HomRep (⟨E, n⟩ : frobeniusColimitVectModel X p hX) ⟨G, n⟩) ⟨l, g⟩)
    (hsurj : ∀ (n : ℕ) (E G : X.Vect)
      (w : (frobeniusStageFunctor X p hX n).obj E ⟶ (frobeniusStageFunctor X p hX n).obj G),
      ∃ (k : ℕ) (f : (frobeniusPullbackIter X p hX (n + k)).obj E ⟶
        (frobeniusPullbackIter X p hX (n + k)).obj G),
        frobeniusStageHomMap X p hX n (n + k) f = w) :
    (frobeniusColimitVectComparison X p hX).Faithful :=
  (frobeniusColimitVectPseudococone X p hX).faithful_desc_of_bijective_equalStage
    (bijective_frobeniusColimitVectComparison_map_equalStage X p hX hinj hsurj)

/-- **The comparison functor of Stacks Tag 0EXB is full** as soon as the map out of the
sequential colimit `colim_k Hom_X(F^{n + k, *}ℰ, F^{n + k, *}𝒢)` given by
`AlgebraicGeometry.frobeniusStageHomMap` is injective and surjective. -/
theorem full_frobeniusColimitVectComparison_of_stageHomMap
    (hinj : ∀ (n k l : ℕ) (E G : X.Vect)
      (f : (frobeniusPullbackIter X p hX (n + k)).obj E ⟶
        (frobeniusPullbackIter X p hX (n + k)).obj G)
      (g : (frobeniusPullbackIter X p hX (n + l)).obj E ⟶
        (frobeniusPullbackIter X p hX (n + l)).obj G),
      frobeniusStageHomMap X p hX n (n + k) f = frobeniusStageHomMap X p hX n (n + l) g →
      EndoColim.HomRep.Agree
        (⟨k, f⟩ : EndoColim.HomRep (⟨E, n⟩ : frobeniusColimitVectModel X p hX) ⟨G, n⟩) ⟨l, g⟩)
    (hsurj : ∀ (n : ℕ) (E G : X.Vect)
      (w : (frobeniusStageFunctor X p hX n).obj E ⟶ (frobeniusStageFunctor X p hX n).obj G),
      ∃ (k : ℕ) (f : (frobeniusPullbackIter X p hX (n + k)).obj E ⟶
        (frobeniusPullbackIter X p hX (n + k)).obj G),
        frobeniusStageHomMap X p hX n (n + k) f = w) :
    (frobeniusColimitVectComparison X p hX).Full :=
  (frobeniusColimitVectPseudococone X p hX).full_desc_of_bijective_equalStage
    (bijective_frobeniusColimitVectComparison_map_equalStage X p hX hinj hsurj)

end AlgebraicGeometry

end
