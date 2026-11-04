module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitIsoLevel
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitPullback
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction

/-!
# The fibre condition and the conclusion of the essential-image half of Stacks Tag 0EXH

Let `p` be a prime and `f : X ⟶ Y` a morphism of schemes in characteristic `p`. The
essential-image half of [Stacks, Tag 0EXH] asks of a finite locally free `𝒪_X`-module `ℰ` that
for every `y ∈ Y` some Frobenius power pullback `F^{n_y,*}ℰ` be free on the reduced fibre
`X_{y,red}`, and concludes that some Frobenius power pullback `F^{n,*}ℰ` is the pullback of a
finite locally free `𝒪_Y`-module. This file names the two conditions and shows that the second
one is exactly membership of `(ℰ, m)` in the essential image of
`colim_F Vect(Y) ⥤ colim_F Vect(X)`.

## Main definitions

* `AlgebraicGeometry.Scheme.Vect.IsFreeOnReducedFibresAfterFrobenius`: the hypothesis.
* `AlgebraicGeometry.Scheme.Vect.DescendsAfterFrobenius`: the conclusion.

## Main results

* `AlgebraicGeometry.mem_essImage_frobeniusColimitVectModelPullback_iff`: `(ℰ, m)` lies in the
  essential image of `colim_F Vect(Y) ⥤ colim_F Vect(X)` if and only if some `F^{n,*}ℰ` is
  isomorphic to the pullback of a finite locally free `𝒪_Y`-module.

## References

* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ) [Fact p.Prime]
  (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)

/-- The hypothesis of the essential-image half of Stacks Tag 0EXH on a finite locally free
`𝒪_X`-module `ℰ`: for every point `y` of `Y` there are integers `n_y, r_y ≥ 0` such that the
pullback of `F^{n_y,*}ℰ` to the reduced fibre `X_{y,red}` is isomorphic to `𝒪^{⊕r_y}`. -/
def Scheme.Vect.IsFreeOnReducedFibresAfterFrobenius (E : X.Vect) : Prop :=
  ∀ y : Y, ∃ n r : ℕ, Nonempty
    ((Scheme.Modules.pullback ((f.fiber y).reductionι ≫ f.fiberι y)).obj
        ((frobeniusPullbackIter X p hX n).obj E).obj ≅
      SheafOfModules.free (ULift.{u} (Fin r)))

/-- The conclusion of the essential-image half of Stacks Tag 0EXH for a finite locally free
`𝒪_X`-module `ℰ`: for some `n ≥ 0` the Frobenius power pullback `F^{n,*}ℰ` is isomorphic to the
pullback along `f` of a finite locally free `𝒪_Y`-module. -/
def Scheme.Vect.DescendsAfterFrobenius (E : X.Vect) : Prop :=
  ∃ (n : ℕ) (G : Y.Vect),
    Nonempty ((frobeniusPullbackIter X p hX n).obj E ≅ (Scheme.Vect.pullback f).obj G)

/-- **`(ℰ, m)` is in the essential image of `colim_F Vect(Y) ⥤ colim_F Vect(X)` exactly when
some Frobenius power pullback of `ℰ` is the pullback of a finite locally free `𝒪_Y`-module.** -/
theorem mem_essImage_frobeniusColimitVectModelPullback_iff (A : frobeniusColimitVectModel X p hX) :
    (frobeniusColimitVectModelPullback f p hX hY).essImage A ↔
      Scheme.Vect.DescendsAfterFrobenius f p hX A.obj := by
  constructor
  · rintro ⟨B, ⟨e⟩⟩
    obtain ⟨k, u, -⟩ := EndoColim.exists_iso_hom_eq e.symm
    exact ⟨B.stage + k, (frobeniusPullbackIter Y p hY (A.stage + k)).obj B.obj,
      ⟨u ≪≫ (endoIterCommIso (Scheme.Vect.pullback f)
        (frobeniusVectPullbackIso f p hX hY) (A.stage + k) B.obj).symm⟩⟩
  · rintro ⟨n, G, ⟨e⟩⟩
    exact ⟨⟨G, A.stage + n⟩,
      ⟨(frobeniusColimitVectModelStage X p hX (A.stage + n)).mapIso e.symm ≪≫
        EndoColim.objShiftIso (frobeniusPullback X p hX) A.stage n A.obj⟩⟩

end AlgebraicGeometry

end
