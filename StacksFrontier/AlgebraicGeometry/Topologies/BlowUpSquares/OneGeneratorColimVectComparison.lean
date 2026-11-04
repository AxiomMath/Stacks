module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitMapComp
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusVectPullbackComp
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVectFaithful

/-!
# The comparison functor of Stacks Tag 0EXC for the one-generator square

Let `p` be a prime, let `A` be a ring in characteristic `p`, let `f ∈ A` and let `J ⊆ A` be an
ideal annihilated by `f ^ n`, so that the spectra of

```
A ⧸ (J + fA) <--- A ⧸ J
      ^             ^
      |             |
   A ⧸ fA   <---    A
```

form the almost blowup square of More on Flatness, Example 0EVG. The four restriction functors
between the categories `colim_F Vect` of Stacks Tag 0EXA are built in
`StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVect`. This file
assembles them into **the comparison functor of Stacks Tag 0EXC**

`colim_F Vect(X) ⟶ colim_F Vect(Z) ×_{colim_F Vect(E)} colim_F Vect(X')`

into Mathlib's `CategoryTheory.Limits.CategoricalPullback`, and proves that it is faithful.

## Main definitions

* `AlgebraicGeometry.OneGeneratorSquare.colimVectPullbackComp`: **restriction on the colimit
  categories respects composition** — restricting along `h` and then along `g` is isomorphic to
  restricting along `g ≫ h`.
* `AlgebraicGeometry.squareColimVectIso`: **the two composite transition functors around the
  square of Example 0EVG agree.**
* `AlgebraicGeometry.colimVectCatCommSqOver`: that square read as a
  `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver`.
* `AlgebraicGeometry.colimVectComparison`: **the comparison functor of Stacks Tag 0EXC** for the
  one-generator almost blowup square.

## Main results

* `AlgebraicGeometry.frobeniusVectPullbackIso_compComm`: the Frobenius comparison for a
  composite of restrictions is the comparison `CategoryTheory.EndoColim.compComm` of the
  composite of the two induced functors. This is exactly the compatibility hypothesis of
  `CategoryTheory.EndoColim.mapCongrIso`, and it is what makes
  `AlgebraicGeometry.OneGeneratorSquare.colimVectPullbackComp` exist.
* `AlgebraicGeometry.colimVectComparison_faithful`: **the comparison functor of Stacks Tag 0EXC
  is faithful** for the square of Example 0EVG.

## Implementation notes

The isomorphism `AlgebraicGeometry.squareColimVectIso` is assembled from the three structural
pieces of `StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitMapComp`. On each of the two
legs of the square, `CategoryTheory.EndoColim.map_comp_map` merges the two induced functors into
the one induced by the composite of the two restrictions, and
`CategoryTheory.EndoColim.mapCongrIso` then replaces that composite by the restriction along the
composite morphism of schemes — its compatibility hypothesis being
`AlgebraicGeometry.frobeniusVectPullbackIso_comp`. Both legs therefore land on
`AlgebraicGeometry.OneGeneratorSquare.colimVectPullback` of a single morphism of schemes, and the
two morphisms are equal by `AlgebraicGeometry.OneGeneratorSquare.specMap_square`; the remaining
comparison is an `CategoryTheory.eqToIso`. The merge step uses
`CategoryTheory.EndoColim.mapCompMapIso` rather than `CategoryTheory.eqToIso` of
`CategoryTheory.EndoColim.map_comp_map`, because the former is the identity on every object and
so the components of
`AlgebraicGeometry.OneGeneratorSquare.colimVectPullbackComp` are computed outright.

## References

* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-! ### Restriction on the colimit categories respects composition -/

section Comp

variable (p : ℕ) [Fact p.Prime] {X Y Z : Scheme.{u}} (hX : IsInCharacteristic X p)
  (hY : IsInCharacteristic Y p) (hZ : IsInCharacteristic Z p) (g : X ⟶ Y) (h : Y ⟶ Z)

/-- **The Frobenius comparison for a composite of restrictions is the comparison for the
composite of the two induced functors.** This is
`AlgebraicGeometry.frobeniusVectPullbackIso_comp` with the right-hand side recognised as
`CategoryTheory.EndoColim.compComm`, which is the shape in which
`CategoryTheory.EndoColim.mapCongrIso` consumes it. -/
theorem frobeniusVectPullbackIso_compComm :
    Functor.isoWhiskerLeft (frobeniusPullback Z p hZ) (Scheme.Vect.pullbackComp g h) ≪≫
        frobeniusVectPullbackIso (g ≫ h) p hX hZ =
      EndoColim.compComm (frobeniusPullback Z p hZ) (frobeniusPullback Y p hY)
            (frobeniusPullback X p hX) (Scheme.Vect.pullback h) (Scheme.Vect.pullback g)
            (frobeniusVectPullbackIso h p hY hZ) (frobeniusVectPullbackIso g p hX hY) ≪≫
        Functor.isoWhiskerRight (Scheme.Vect.pullbackComp g h) (frobeniusPullback X p hX) := by
  rw [frobeniusVectPullbackIso_comp p hX hY hZ g h]
  exact Iso.ext (NatTrans.ext (funext fun M ↦ by simp))

/-- **Restriction of vector bundles on the colimit categories respects composition.**
Restricting along `h : Y ⟶ Z` and then along `g : X ⟶ Y` is isomorphic to restricting along
`g ≫ h`, as functors `colim_F Vect(Z) ⥤ colim_F Vect(X)`. -/
noncomputable def OneGeneratorSquare.colimVectPullbackComp :
    OneGeneratorSquare.colimVectPullback p hY hZ h ⋙
        OneGeneratorSquare.colimVectPullback p hX hY g ≅
      OneGeneratorSquare.colimVectPullback p hX hZ (g ≫ h) :=
  EndoColim.mapCompMapIso (frobeniusPullback Z p hZ) (frobeniusPullback Y p hY)
      (frobeniusPullback X p hX) (Scheme.Vect.pullback h) (Scheme.Vect.pullback g)
      (frobeniusVectPullbackIso h p hY hZ) (frobeniusVectPullbackIso g p hX hY) ≪≫
    EndoColim.mapCongrIso (frobeniusPullback Z p hZ) (frobeniusPullback X p hX)
      (Scheme.Vect.pullback h ⋙ Scheme.Vect.pullback g) (Scheme.Vect.pullback (g ≫ h))
      (EndoColim.compComm (frobeniusPullback Z p hZ) (frobeniusPullback Y p hY)
        (frobeniusPullback X p hX) (Scheme.Vect.pullback h) (Scheme.Vect.pullback g)
        (frobeniusVectPullbackIso h p hY hZ) (frobeniusVectPullbackIso g p hX hY))
      (frobeniusVectPullbackIso (g ≫ h) p hX hZ) (Scheme.Vect.pullbackComp g h)
      (frobeniusVectPullbackIso_compComm p hX hY hZ g h)

/-- The comparison of `AlgebraicGeometry.OneGeneratorSquare.colimVectPullbackComp` at the object
`(ℰ, n)` is the stage-`n` functor applied to the comparison of the two restrictions of `ℰ`. -/
@[simp]
lemma OneGeneratorSquare.colimVectPullbackComp_hom_app (E : Z.Vect) (n : ℕ) :
    (OneGeneratorSquare.colimVectPullbackComp p hX hY hZ g h).hom.app ⟨E, n⟩ =
      EndoColim.stageHomOf (frobeniusPullback X p hX) n
        ((Scheme.Vect.pullbackComp g h).hom.app E) :=
  Category.id_comp _

end Comp

/-! ### The square of transition functors -/

/-- **The two composite transition functors around the square of Example 0EVG agree.** -/
noncomputable def squareColimVectIso (A : Type u) [CommRing A] (f : A) (J : Ideal A)
    (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) :
    OneGeneratorSquare.toCentre A f p hp ⋙ OneGeneratorSquare.centreToExceptional A f J p hp ≅
      OneGeneratorSquare.toModification A J p hp ⋙
        OneGeneratorSquare.modificationToExceptional A f J p hp :=
  OneGeneratorSquare.colimVectPullbackComp p (OneGeneratorSquare.charExc A f J p hp)
      (OneGeneratorSquare.charCtr A f p hp) (OneGeneratorSquare.charBase A p hp)
      (Spec.map (OneGeneratorSquare.ctrToExc A f J))
      (Spec.map (OneGeneratorSquare.toCtr A f)) ≪≫
    eqToIso (congrArg
        (OneGeneratorSquare.colimVectPullback p (OneGeneratorSquare.charExc A f J p hp)
          (OneGeneratorSquare.charBase A p hp))
        (OneGeneratorSquare.specMap_square A f J).symm) ≪≫
      (OneGeneratorSquare.colimVectPullbackComp p (OneGeneratorSquare.charExc A f J p hp)
        (OneGeneratorSquare.charMod A J p hp) (OneGeneratorSquare.charBase A p hp)
        (Spec.map (OneGeneratorSquare.modToExc A f J))
        (Spec.map (OneGeneratorSquare.toMod A J))).symm

/-! ### The comparison functor -/

/-- The square of transition functors of Example 0EVG as a categorical commutative square. -/
noncomputable def colimVectCatCommSqOver (A : Type u) [CommRing A] (f : A) (J : Ideal A)
    (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) :
    CategoricalPullback.CatCommSqOver
      (OneGeneratorSquare.centreToExceptional A f J p hp)
      (OneGeneratorSquare.modificationToExceptional A f J p hp)
      (OneGeneratorSquare.colimVectBase A p hp) where
  fst := OneGeneratorSquare.toCentre A f p hp
  snd := OneGeneratorSquare.toModification A J p hp
  iso := squareColimVectIso A f J p hp

/-- **The comparison functor of Stacks Tag 0EXC** for the one-generator almost blowup square:
`colim_F Vect(X) ⟶ colim_F Vect(Z) ×_{colim_F Vect(E)} colim_F Vect(X')`. -/
noncomputable def colimVectComparison (A : Type u) [CommRing A] (f : A) (J : Ideal A)
    (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) :
    OneGeneratorSquare.colimVectBase A p hp ⥤
      CategoricalPullback
        (OneGeneratorSquare.centreToExceptional A f J p hp)
        (OneGeneratorSquare.modificationToExceptional A f J p hp) :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj
    (colimVectCatCommSqOver A f J p hp)

section Comparison

variable (A : Type u) [CommRing A] (f : A) (J : Ideal A) (p : ℕ) [Fact p.Prime]
  (hp : (p : A) = 0)

/-- The comparison functor of Stacks Tag 0EXC, followed by the first projection, is restriction
to the centre. -/
@[simp]
lemma colimVectComparison_comp_π₁ :
    colimVectComparison A f J p hp ⋙
        CategoricalPullback.π₁ (OneGeneratorSquare.centreToExceptional A f J p hp)
          (OneGeneratorSquare.modificationToExceptional A f J p hp) =
      OneGeneratorSquare.toCentre A f p hp :=
  rfl

/-- The comparison functor of Stacks Tag 0EXC, followed by the second projection, is restriction
to the modification. -/
@[simp]
lemma colimVectComparison_comp_π₂ :
    colimVectComparison A f J p hp ⋙
        CategoricalPullback.π₂ (OneGeneratorSquare.centreToExceptional A f J p hp)
          (OneGeneratorSquare.modificationToExceptional A f J p hp) =
      OneGeneratorSquare.toModification A J p hp :=
  rfl

/-- The first component of the comparison functor on a morphism is its restriction to the
centre. -/
@[simp]
lemma colimVectComparison_map_fst {V W : OneGeneratorSquare.colimVectBase A p hp} (u : V ⟶ W) :
    ((colimVectComparison A f J p hp).map u).fst =
      (OneGeneratorSquare.toCentre A f p hp).map u :=
  rfl

/-- The second component of the comparison functor on a morphism is its restriction to the
modification. -/
@[simp]
lemma colimVectComparison_map_snd {V W : OneGeneratorSquare.colimVectBase A p hp} (u : V ⟶ W) :
    ((colimVectComparison A f J p hp).map u).snd =
      (OneGeneratorSquare.toModification A J p hp).map u :=
  rfl

end Comparison

/-! ### Faithfulness -/

/-- **The comparison functor of Stacks Tag 0EXC is faithful** for the square of Example 0EVG.
A morphism of `colim_F Vect(Spec A)` is determined by the pair of its restrictions to the centre
and to the modification, which is
`AlgebraicGeometry.injective_toCentre_toModification_map`, and those restrictions are the two
components of the image of the morphism under the comparison functor. -/
theorem colimVectComparison_faithful (A : Type u) [CommRing A] (f : A) (J : Ideal A) (n : ℕ)
    (hann : ∀ x ∈ J, f ^ n * x = 0) (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) :
    (colimVectComparison A f J p hp).Faithful where
  map_injective {V W} {u v} huv := by
    refine injective_toCentre_toModification_map A f J n hann p hp V W ?_
    simp only [Prod.mk.injEq]
    exact ⟨congrArg (·.fst) huv, congrArg (·.snd) huv⟩

end AlgebraicGeometry

end
