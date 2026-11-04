module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitMap
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusVectPullback

/-!
# Vector bundles on the one-generator almost blowup square after Frobenius colimits

Let `p` be a prime, let `A` be a ring in characteristic `p`, let `f ∈ A` and let `J ⊆ A` be a
finitely generated ideal annihilated by a power of `f`. The almost blowup square of
More on Flatness, Example 0EVG is

```
E = Spec (A / (fA + J))  ⟶  Spec (A / J) = X'
         ↓                        ↓
  Z = Spec (A / fA)       ⟶    Spec A = X
```

Restriction of vector bundles along the four morphisms induces, after taking the colimit along
the absolute Frobenius, four transition functors between the categories `colim_F Vect` of
Stacks Tag 0EXA, and this file builds them and the comparison functor

`colim_F Vect(X) ⟶ colim_F Vect(Z) ×_{colim_F Vect(E)} colim_F Vect(X')`

into Mathlib's `CategoryTheory.Limits.CategoricalPullback`, whose objects are a vector bundle on
the centre, a vector bundle on the modification, and an isomorphism of their restrictions to the
exceptional corner.

## Main definitions

* `AlgebraicGeometry.OneGeneratorSquare.colimVectPullback`: restriction of vector bundles along a
  morphism of schemes in characteristic `p`, read on the colimit categories `colim_F Vect` of
  Stacks Tag 0EXA. It is `CategoryTheory.EndoColim.map` applied to
  `AlgebraicGeometry.Scheme.Vect.pullback`, the comparison with the two Frobenius pullbacks being
  `AlgebraicGeometry.frobeniusVectPullbackIso`.
* `AlgebraicGeometry.OneGeneratorSquare.frobeniusColimitVectModelStage_comp_colimVectPullback`:
  restriction on `colim_F Vect(-)` is ordinary restriction at every stage.
* `AlgebraicGeometry.OneGeneratorSquare.toCentre`,
  `AlgebraicGeometry.OneGeneratorSquare.toModification`,
  `AlgebraicGeometry.OneGeneratorSquare.centreToExceptional` and
  `AlgebraicGeometry.OneGeneratorSquare.modificationToExceptional`: **the four transition
  functors of the square**, on the colimit categories.

## Implementation notes

The model of `colim_F Vect(X)` used here is `AlgebraicGeometry.frobeniusColimitVectModel`, the
down-to-earth category of Stacks Tag 0EXA whose objects are the pairs `(ℰ, n)` and whose Hom-sets
are the colimits `colim_N Hom_X(F^{N - n, *}ℰ, F^{N - m, *}𝒢)`. This is the model for which
Stacks Tag 0EXB is proved in this repository
(`AlgebraicGeometry.frobeniusColimitVectEquivalence`), and it is the model a functor can be built
out of: a cocone in `Cat` on the diagram of Tag 0EXA would ask for equalities of functors,
whereas restriction of vector bundles commutes with the absolute Frobenius only up to the
isomorphism `AlgebraicGeometry.frobeniusVectPullbackIso`.

## References

* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u

namespace AlgebraicGeometry.OneGeneratorSquare

/-- **Restriction of vector bundles on the colimit categories along the absolute Frobenius.**
For a morphism `g : X ⟶ Y` of schemes in characteristic `p`, restriction of finite locally free
modules along `g` commutes with the two absolute Frobenius pullbacks up to
`AlgebraicGeometry.frobeniusVectPullbackIso`, and therefore induces a functor
`colim_F Vect(Y) ⥤ colim_F Vect(X)` between the colimit categories of Stacks Tag 0EXA. -/
def colimVectPullback {X Y : Scheme.{u}} (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (g : X ⟶ Y) :
    frobeniusColimitVectModel Y p hY ⥤ frobeniusColimitVectModel X p hX :=
  EndoColim.map (frobeniusPullback Y p hY) (frobeniusPullback X p hX)
    (Scheme.Vect.pullback g) (frobeniusVectPullbackIso g p hX hY)

/-- Restriction on the colimit categories places the restriction of a vector bundle at the same
stage. -/
@[simp]
lemma colimVectPullback_obj {X Y : Scheme.{u}} (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (g : X ⟶ Y) (E : Y.Vect)
    (n : ℕ) :
    (colimVectPullback p hX hY g).obj ⟨E, n⟩ = ⟨(Scheme.Vect.pullback g).obj E, n⟩ :=
  rfl

/-- **Restriction on `colim_F Vect(-)` is ordinary restriction at every stage**, as an equality
of functors. -/
lemma frobeniusColimitVectModelStage_comp_colimVectPullback {X Y : Scheme.{u}} (p : ℕ)
    [Fact p.Prime] (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (g : X ⟶ Y)
    (n : ℕ) :
    frobeniusColimitVectModelStage Y p hY n ⋙ colimVectPullback p hX hY g =
      Scheme.Vect.pullback g ⋙ frobeniusColimitVectModelStage X p hX n :=
  EndoColim.stageFunctor_comp_map _ _ _ _ n

variable (A : Type u) [CommRing A] (f : A) (J : Ideal A) (p : ℕ) [Fact p.Prime]
  (hp : (p : A) = 0)

/-- `colim_F Vect(X)` for the base `X = Spec A` of the square of Example 0EVG. -/
abbrev colimVectBase : Type (u + 1) :=
  frobeniusColimitVectModel (Spec (.of A)) p (charBase A p hp)

/-- `colim_F Vect(X')` for the modification `X' = Spec (A ⧸ J)` of the square of
Example 0EVG. -/
abbrev colimVectModification : Type (u + 1) :=
  frobeniusColimitVectModel (Spec (.of (A ⧸ J))) p (charMod A J p hp)

/-- `colim_F Vect(Z)` for the centre `Z = Spec (A ⧸ fA)` of the square of Example 0EVG. -/
abbrev colimVectCentre : Type (u + 1) :=
  frobeniusColimitVectModel (Spec (.of (A ⧸ Ideal.span {f}))) p (charCtr A f p hp)

/-- `colim_F Vect(E)` for the exceptional corner `E = Spec (A ⧸ (J + fA))` of the square of
Example 0EVG. -/
abbrev colimVectExceptional : Type (u + 1) :=
  frobeniusColimitVectModel (Spec (.of (A ⧸ (J ⊔ Ideal.span {f})))) p (charExc A f J p hp)

/-- **Restriction to the centre**, `colim_F Vect(X) ⥤ colim_F Vect(Z)`. -/
def toCentre : colimVectBase A p hp ⥤ colimVectCentre A f p hp :=
  colimVectPullback p (charCtr A f p hp) (charBase A p hp) (Spec.map (toCtr A f))

/-- **Restriction to the modification**, `colim_F Vect(X) ⥤ colim_F Vect(X')`. -/
def toModification : colimVectBase A p hp ⥤ colimVectModification A J p hp :=
  colimVectPullback p (charMod A J p hp) (charBase A p hp) (Spec.map (toMod A J))

/-- **Restriction from the centre to the exceptional corner**,
`colim_F Vect(Z) ⥤ colim_F Vect(E)`. -/
def centreToExceptional : colimVectCentre A f p hp ⥤ colimVectExceptional A f J p hp :=
  colimVectPullback p (charExc A f J p hp) (charCtr A f p hp) (Spec.map (ctrToExc A f J))

/-- **Restriction from the modification to the exceptional corner**,
`colim_F Vect(X') ⥤ colim_F Vect(E)`. -/
def modificationToExceptional :
    colimVectModification A J p hp ⥤ colimVectExceptional A f J p hp :=
  colimVectPullback p (charExc A f J p hp) (charMod A J p hp) (Spec.map (modToExc A f J))

end AlgebraicGeometry.OneGeneratorSquare

end
