module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitPullbackFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.DecompositionBaseChange

/-!
# Essential surjectivity of `colim_F Vect(T') ⥤ colim_F Vect(T)` via a factorization of Frobenius

Let `p` be a prime and `i : T ⟶ T'` a morphism of schemes in characteristic `p`. If some power
`F_T^n` of the absolute Frobenius of `T` factors as `i ≫ g` for a morphism `g : T' ⟶ T`, then
every object of `colim_F Vect(T)` comes from `colim_F Vect(T')`: the object `(ℰ, m)` is the image
of `(g^*ℰ, m + n)`, since `i^*g^*ℰ ≅ F^{n,*}ℰ` and `(F^{n,*}ℰ, m + n) ≅ (ℰ, m)` in the colimit
category.

This is the mechanism behind the invariance of `colim_F Vect` under thickenings and universal
homeomorphisms used in the proof of the essential-image half of Stacks Tag 0EXH.

## Main results

* `AlgebraicGeometry.frobeniusColimitVectModelPullback_essSurj_of_comp_eq_frobPow`.
* `AlgebraicGeometry.frobeniusColimitVectModelPullback_essSurj_subschemeι`: the case of a closed
  subscheme whose ideal is killed by a power of the Frobenius.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable {T T' : Scheme.{u}} (i : T ⟶ T') (g : T' ⟶ T) (p : ℕ) [Fact p.Prime]
  (hT : IsInCharacteristic T p) (hT' : IsInCharacteristic T' p)

/-- `i^*g^*ℰ ≅ F^{n,*}ℰ` for `i ≫ g = F_T^n`, in `Vect(T)`. -/
def vectPullbackPullbackIsoEndoIter (n : ℕ) (h : i ≫ g = frobPow p hT (𝟙 T) n) (E : T.Vect) :
    (Scheme.Vect.pullback i).obj ((Scheme.Vect.pullback g).obj E) ≅
      ((frobeniusPullback T p hT).endoIter n).obj E :=
  ObjectProperty.isoMk _ ((Scheme.Modules.pullbackComp i g).app E.obj ≪≫
    (Scheme.Modules.pullbackCongr h).app E.obj ≪≫
      (frobIso p hT hT (𝟙 T) (vectIsoY E) n).symm)

/-- **If a power of the absolute Frobenius of `T` factors through `i : T ⟶ T'`, then
`colim_F Vect(T') ⥤ colim_F Vect(T)` is essentially surjective.** -/
theorem frobeniusColimitVectModelPullback_essSurj_of_comp_eq_frobPow (n : ℕ)
    (h : i ≫ g = frobPow p hT (𝟙 T) n) :
    (frobeniusColimitVectModelPullback i p hT hT').EssSurj where
  mem_essImage A :=
    ⟨⟨(Scheme.Vect.pullback g).obj A.obj, A.stage + n⟩,
      ⟨(frobeniusColimitVectModelStage T p hT (A.stage + n)).mapIso
          (vectPullbackPullbackIsoEndoIter i g p hT n h A.obj) ≪≫
        EndoColim.objShiftIso (frobeniusPullback T p hT) A.stage n A.obj⟩⟩

/-- Iterated Frobenius twists of a morphism followed by a further morphism. -/
lemma frobPow_comp {S Y Y' : Scheme.{u}} {hY : IsInCharacteristic Y p}
    {hY' : IsInCharacteristic Y' p} (H : S ⟶ Y) (k : Y ⟶ Y') :
    ∀ n, frobPow p hY H n ≫ k = frobPow p hY' (H ≫ k) n
  | 0 => rfl
  | n + 1 => by
    change (frobOf p hY (frobPow p hY H n) ≫ frobPow p hY H n) ≫ k =
      frobOf p hY' (frobPow p hY' (H ≫ k) n) ≫ frobPow p hY' (H ≫ k) n
    rw [Category.assoc, frobPow_comp H k n]

/-- **Pullback to a closed subscheme whose ideal is killed by a Frobenius power is essentially
surjective on `colim_F Vect`.** -/
theorem frobeniusColimitVectModelPullback_essSurj_subschemeι (I : T'.IdealSheafData) (n : ℕ)
    (hI : I ≤ (frobPow p hT' (𝟙 T') n).ker) (hS : IsInCharacteristic I.subscheme p) :
    (frobeniusColimitVectModelPullback I.subschemeι p hS hT').EssSurj := by
  refine frobeniusColimitVectModelPullback_essSurj_of_comp_eq_frobPow I.subschemeι
    (Scheme.IdealSheafData.subschemeLift _ hI) p hS hT' n ?_
  rw [← cancel_mono I.subschemeι, Category.assoc,
    Scheme.IdealSheafData.subschemeLift_subschemeι, comp_frobPow I.subschemeι
      (Category.comp_id _) n, frobPow_comp p (hY := hS) (hY' := hT') (𝟙 _) I.subschemeι n,
    Category.id_comp]

end AlgebraicGeometry

end
