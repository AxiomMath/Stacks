module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitHomColimit
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStrictColimit

/-!
# The category `colim_F Vect(S)` of Stacks Tag 0EXA, down to earth

Let `p` be a prime and let `S` be a scheme in characteristic `p`, with absolute Frobenius
`F : S ⟶ S`. Stacks Tag 0EXA defines

`colim_F Vect(S) = colim (Vect(S) →F* Vect(S) →F* Vect(S) →F* ⋯)`

and describes it in down-to-earth terms: an object is a pair `(ℰ, n)` with `ℰ` a finite locally
free `𝒪_S`-module and `n ≥ 0`, the morphisms are

`Hom((ℰ, n), (𝒢, m)) = colim_N Hom_S(F^{N - n, *}ℰ, F^{N - m, *}𝒢)`,

and consequently `(ℰ, n) ≅ (F^*ℰ, n + 1)`. The colimit itself is
`AlgebraicGeometry.frobeniusColimitVect`, the colimit in `Cat`; the category on which Tags 0EXB,
0EXC, 0EXD and 0EXE are built is the explicit one, `AlgebraicGeometry.frobeniusColimitVectModel`.
This file proves that the down-to-earth description is correct: it identifies the two categories
and states each clause of the description as a theorem.

## Main results

* `AlgebraicGeometry.frobeniusColimitVectModelEquivalence`: **the explicit category
  `frobeniusColimitVectModel` is equivalent to the colimit `frobeniusColimitVect` in `Cat`**, by
  the functor which sends `(ℰ, n)` to the image of `ℰ` under the stage-`n` coprojection
  (`AlgebraicGeometry.frobeniusColimitVectModelEquivalence_functor_obj`).
* `AlgebraicGeometry.exists_frobeniusColimitVect_obj_eq`: every object of `frobeniusColimitVect`
  is the image of a finite locally free module `ℰ` under a coprojection, that is a pair `(ℰ, n)`.
* `AlgebraicGeometry.frobeniusColimitVectModelHomIsColimit` and
  `AlgebraicGeometry.frobeniusColimitVectHomEquiv`: **the Hom-sets are the colimits
  `colim_N Hom_S(F^{N - n, *}ℰ, F^{N - m, *}𝒢)`**, in the explicit category and in the colimit
  in `Cat`.
* `AlgebraicGeometry.frobeniusColimitVectModelShiftIso`: **`(ℰ, n) ≅ (F^*ℰ, n + 1)`**, naturally
  in `ℰ` (`AlgebraicGeometry.frobeniusColimitVectModelShiftNatIso`).

## Implementation notes

`CategoryTheory.EndoColim.catStage` at the stage `n` is `AsSmall.up` followed by the colimit
coprojection `colimit.ι (frobeniusVectDiagram X p hX) n` (by definition), so it is the
coprojection read on `Vect(S)` itself rather than on its small copy.

No quasi-compactness or quasi-separatedness of `S` is needed for any of this: Tag 0EXA fixes
these hypotheses for the whole section, but they enter only in Tag 0EXB, so they are omitted
here, which generalises the statements.

The colimit `N ≥ n, m` is indexed by `k : ℕ`, standing for `N = max(n, m) + k`
(`CategoryTheory.EndoColim.homDiagram`); its value at `k` is
`Hom_S(F^{N - n, *}ℰ, F^{N - m, *}𝒢)` on the nose (`AlgebraicGeometry.frobeniusHomDiagram_obj`),
and its transition maps apply `F^*` (`AlgebraicGeometry.frobeniusHomDiagram_map_succ`).

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-! ### The explicit category and the colimit in `Cat` -/

/-- **Stacks Tag 0EXA: the explicit category is the colimit.** The category
`frobeniusColimitVectModel`, whose objects are the pairs `(ℰ, n)` and whose Hom-sets are the
colimits `colim_N Hom_S(F^{N - n, *}ℰ, F^{N - m, *}𝒢)`, is equivalent to the colimit
`colim_F Vect(S)` of `Vect(S) →F* Vect(S) →F* ⋯` in `Cat`. -/
@[stacks 0EXA "colim_F Vect(S) is the category of pairs (E, n) described in the tag"]
noncomputable def frobeniusColimitVectModelEquivalence :
    frobeniusColimitVectModel X p hX ≌ frobeniusColimitVect X p hX :=
  EndoColim.catColimitEquivalence.{u + 1} (frobeniusPullback X p hX)

/-- The equivalence of Stacks Tag 0EXA sends the pair `(ℰ, n)` to the image of `ℰ` under the
stage-`n` coprojection of the colimit in `Cat`. -/
lemma frobeniusColimitVectModelEquivalence_functor_obj (E : X.Vect) (n : ℕ) :
    (frobeniusColimitVectModelEquivalence X p hX).functor.obj ⟨E, n⟩ =
      (EndoColim.catStage.{u + 1} (frobeniusPullback X p hX) n).obj E :=
  rfl

/-- The equivalence of Stacks Tag 0EXA restricts, on the stage-`n` copy of `Vect(S)`, to the
stage-`n` coprojection of the colimit in `Cat`, as an equality of functors. -/
lemma frobeniusColimitVectModelStage_comp_equivalence_functor (n : ℕ) :
    frobeniusColimitVectModelStage X p hX n ⋙
        (frobeniusColimitVectModelEquivalence X p hX).functor =
      EndoColim.catStage.{u + 1} (frobeniusPullback X p hX) n :=
  EndoColim.stageFunctor_comp_toCatColimit.{u + 1} (frobeniusPullback X p hX) n

/-- **Stacks Tag 0EXA: the objects of `colim_F Vect(S)` are the pairs `(ℰ, n)`.** Every object of
the colimit in `Cat` is the image of a finite locally free `𝒪_S`-module `ℰ` under the stage-`n`
coprojection, for some `n`. -/
@[stacks 0EXA "an object of colim_F Vect(S) is a pair (E, n)"]
theorem exists_frobeniusColimitVect_obj_eq (Y : frobeniusColimitVect X p hX) :
    ∃ (n : ℕ) (E : X.Vect),
      (EndoColim.catStage.{u + 1} (frobeniusPullback X p hX) n).obj E = Y :=
  EndoColim.exists_catStage_obj_eq.{u + 1} (frobeniusPullback X p hX) Y

/-! ### The Hom-sets -/

/-- The value of the diagram of Hom-sets at `k` is `Hom_S(F^{N - n, *}ℰ, F^{N - m, *}𝒢)` for
`N = max(n, m) + k`. -/
lemma frobeniusHomDiagram_obj (E G : X.Vect) (n m k : ℕ) :
    (EndoColim.homDiagram (⟨E, n⟩ : frobeniusColimitVectModel X p hX) ⟨G, m⟩).obj k =
      ((frobeniusPullbackIter X p hX (max n m + k - n)).obj E ⟶
        (frobeniusPullbackIter X p hX (max n m + k - m)).obj G) :=
  rfl

/-- The transition maps of the diagram of Hom-sets apply `F^*`. -/
lemma frobeniusHomDiagram_map_succ (E G : X.Vect) (n m k : ℕ)
    (f : (frobeniusPullbackIter X p hX (max n m + k - n)).obj E ⟶
      (frobeniusPullbackIter X p hX (max n m + k - m)).obj G) :
    (EndoColim.homDiagram (⟨E, n⟩ : frobeniusColimitVectModel X p hX) ⟨G, m⟩).map
        (homOfLE (Nat.le_add_right k 1)) f =
      endoHomCast (m := max n m + k - n + 1) (n := max n m + k - m + 1)
        (m' := max n m + (k + 1) - n) (n' := max n m + (k + 1) - m) (by omega) (by omega)
        ((frobeniusPullback X p hX).map f) :=
  endoHomCast_endoRaise_eq f (j' := 1) (by omega) (by dsimp only; omega)
    (by dsimp only; omega) _ _

/-- **Stacks Tag 0EXA: the Hom-sets of `colim_F Vect(S)`.** In the explicit category,
`Hom((ℰ, n), (𝒢, m))` is the colimit `colim_N Hom_S(F^{N - n, *}ℰ, F^{N - m, *}𝒢)` over the
`N ≥ n, m` along `F^*`, the colimit maps taking a morphism of `Vect(S)` to the morphism it
presents. -/
@[stacks 0EXA "Hom((E, n), (G, m)) = colim_N Hom_S(F^{N - n, *}E, F^{N - m, *}G)"]
noncomputable def frobeniusColimitVectModelHomIsColimit (E G : X.Vect) (n m : ℕ) :
    IsColimit (EndoColim.homCocone (⟨E, n⟩ : frobeniusColimitVectModel X p hX) ⟨G, m⟩) :=
  EndoColim.homCoconeIsColimit _ _

/-- **Stacks Tag 0EXA: the Hom-sets of `colim_F Vect(S)`, in the colimit in `Cat`.** The
morphisms between the images of `ℰ` and `𝒢` under the stage-`n` and stage-`m` coprojections are
in bijection with `colim_N Hom_S(F^{N - n, *}ℰ, F^{N - m, *}𝒢)`. -/
@[stacks 0EXA "Hom((E, n), (G, m)) = colim_N Hom_S(F^{N - n, *}E, F^{N - m, *}G), for the \
colimit in Cat"]
noncomputable def frobeniusColimitVectHomEquiv (E G : X.Vect) (n m : ℕ) :
    ((EndoColim.catStage.{u + 1} (frobeniusPullback X p hX) n).obj E ⟶
        (EndoColim.catStage.{u + 1} (frobeniusPullback X p hX) m).obj G) ≃
      colimit (EndoColim.homDiagram (⟨E, n⟩ : frobeniusColimitVectModel X p hX) ⟨G, m⟩) :=
  ((frobeniusColimitVectModelEquivalence X p hX).fullyFaithfulFunctor.homEquiv
      (X := ⟨E, n⟩) (Y := ⟨G, m⟩)).symm.trans
    (EndoColim.homEquivColimit _ _)

/-- The bijection of Stacks Tag 0EXA takes the image under the equivalence of the morphism
presented by `f` at the level `N = max(n, m) + k` to the image of `f` in the colimit. -/
lemma frobeniusColimitVectHomEquiv_map (E G : X.Vect) (n m k : ℕ)
    (f : (EndoColim.homDiagram (⟨E, n⟩ : frobeniusColimitVectModel X p hX) ⟨G, m⟩).obj k) :
    frobeniusColimitVectHomEquiv X p hX E G n m
        ((frobeniusColimitVectModelEquivalence X p hX).functor.map
          (EndoColim.homAtOf _ _ k f)) =
      colimit.ι (EndoColim.homDiagram (⟨E, n⟩ : frobeniusColimitVectModel X p hX) ⟨G, m⟩) k f := by
  have h : ((frobeniusColimitVectModelEquivalence X p hX).fullyFaithfulFunctor.homEquiv
      (X := ⟨E, n⟩) (Y := ⟨G, m⟩)).symm
        ((frobeniusColimitVectModelEquivalence X p hX).functor.map
          (EndoColim.homAtOf _ _ k f)) = EndoColim.homAtOf _ _ k f :=
    (frobeniusColimitVectModelEquivalence X p hX).fullyFaithfulFunctor.preimage_map _
  exact (congrArg (EndoColim.homEquivColimit _ _) h).trans
    (EndoColim.homEquivColimit_homAtOf _ _ k f)

/-! ### The shift -/

/-- **Stacks Tag 0EXA: `(ℰ, n) ≅ (F^*ℰ, n + 1)`** in `colim_F Vect(S)`. -/
@[stacks 0EXA "the object (E, n) is isomorphic to the object (F^* E, n + 1)"]
noncomputable def frobeniusColimitVectModelShiftIso (E : X.Vect) (n : ℕ) :
    (⟨E, n⟩ : frobeniusColimitVectModel X p hX) ≅ ⟨(frobeniusPullback X p hX).obj E, n + 1⟩ :=
  (EndoColim.shiftStepIso _ n E).symm

/-- The isomorphism `(ℰ, n) ≅ (F^*ℰ, n + 1)` of Stacks Tag 0EXA is natural in `ℰ`. -/
noncomputable def frobeniusColimitVectModelShiftNatIso (n : ℕ) :
    frobeniusColimitVectModelStage X p hX n ≅
      frobeniusPullback X p hX ⋙ frobeniusColimitVectModelStage X p hX (n + 1) :=
  (EndoColim.stageShiftNatIso _ n).symm

/-- The components of the natural isomorphism `frobeniusColimitVectModelShiftNatIso` are the
isomorphisms `(ℰ, n) ≅ (F^*ℰ, n + 1)` of `frobeniusColimitVectModelShiftIso`. -/
lemma frobeniusColimitVectModelShiftNatIso_hom_app (n : ℕ) (E : X.Vect) :
    (frobeniusColimitVectModelShiftNatIso X p hX n).hom.app E =
      (frobeniusColimitVectModelShiftIso X p hX E n).hom :=
  rfl

end AlgebraicGeometry

end
