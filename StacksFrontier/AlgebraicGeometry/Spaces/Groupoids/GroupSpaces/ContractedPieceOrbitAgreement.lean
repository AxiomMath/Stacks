module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteOverAlgClosedFieldConstant
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.CoordinateProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.GeneralLinearTwoPowerContraction
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# The translates of the contracted piece agree on its two rational points

This file closes the step of [Stacks, Tag 0AEM] which spends the finiteness produced by
[Stacks, Tag 0AEJ].

The contraction step
`AlgebraicGeometry.Space.exists_isOpenSubspace_forall_isFinite_comp_eq_orbitMap` gives an open
neighbourhood `U` of the identity in `(GL₂)^m` such that for every `K`-point `M` of `U` the
orbit map

```
C ↪ (ℙ¹_K)^m --M·--> (ℙ¹_K)^m --f--> Z
```

factors through an algebraic space `F` *finite over `Spec K`*. If `K` is algebraically closed
and the point space of `C` is irreducible, then a morphism `C ⟶ F` takes the same value at
every `K`-rational point of `C`
(`AlgebraicGeometry.Space.comp_eq_comp_of_isFinite_toBase`). Hence `f(M · x) = f(M · y)` for
the two distinct `K`-rational points `x ≠ y` of the contracted piece that
`AlgebraicGeometry.Space.exists_reducedClosedSubspace_pair_ne_of_infinite_fibre` supplies, and
for every `K`-point `M` of `U`. That is the source's "`f` is constant on `g(C)` for
`g ∈ G(k)` lying in a Zariski open `U ⊂ G`", read at the two rational points on which the
induction of 0AEM then compares coordinates.

Nothing here uses reducedness of the piece: the factorisation is compared only at rational
points, which is exactly the form 0AEM consumes — the source passes to the algebraic closure
"only so we may argue using rational points".

## Main results

* `AlgebraicGeometry.Space.exists_isOpenSubspace_forall_comp_matrixAut_comp_eq`: for a closed
  subspace `C` of `(ℙ¹_K)^m` with preirreducible point space which `f` carries to a point,
  there is an open neighbourhood of the identity of `(GL₂)^m` over whose `K`-points the
  translated morphism takes the same value at any two `K`-rational points of `C`.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_forall_comp_matrixAut_comp_eq_of_factors`: the
  same with the two rational points given as rational points of `(ℙ¹_K)^m` factoring through
  `C`, so that the conclusion reads `f(M · x) = f(M · y)`.
* `AlgebraicGeometry.Space.preirreducibleSpace_points_reducedClosedSubspace`: the point space
  of the reduced closed subspace on a preirreducible closed set of points is preirreducible.
* `Space.exists_isOpenSubspace_forall_comp_matrixAut_comp_eq_reducedClosedSubspace`:
  the same at the reduced closed subspace on an irreducible closed set, which is the shape in
  which the contracted piece of 0AEM is produced.

## References

* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 0ABJ](https://stacks.math.columbia.edu/tag/0ABJ)
* [Stacks Project, Tag 0AEJ](https://stacks.math.columbia.edu/tag/0AEJ)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (K : Type u) [Field K] [IsAlgClosed K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (CommRingCat.of K))) (m : ℕ)

/-! ### Preirreducibility of the point space of a reduced closed subspace -/

/-- **The point space of the reduced closed subspace on a preirreducible closed set of points
is preirreducible.** The subspace is a closed subspace of Stacks 03IQ, so its map on points is
a topological embedding by [Stacks, Tag 0ABJ] with image the given set. -/
theorem preirreducibleSpace_points_reducedClosedSubspace (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (T : Set (points B S hS X)) (hT : IsClosed T) (hirr : IsPreirreducible T) :
    PreirreducibleSpace
      (points B S hS (reducedClosedSubspace B S hS X hX T hT).toFunctor) := by
  refine preirreducibleSpace_points_of_isPreirreducible_range_pointsMap B S hS hX
    (reducedClosedSubspace B S hS X hX T hT).ι
    (isImmersion_of_isClosedImmersion B S hS
      (isClosedSubspace_reducedClosedSubspace B S hS X hX T hT).2) ?_
  rw [range_pointsMap_ι_reducedClosedSubspace B S hS X hX T hT]
  exact hirr

/-! ### The agreement of the translates on two rational points -/

variable {Z : (BigFppfOver B (Spec (CommRingCat.of K)) hK)ᵒᵖ ⥤ Type u}
  (z : Z ⟶ baseFunctor K B hK)
  (f : projectiveLinePower K B hK (Fin m) ⟶ Z)

/-- **The translates of a contracted piece agree on its rational points.**

Let `K` be an algebraically closed field, let `Z` be an algebraic space over `Spec K` separated
and locally of finite type over `Spec K`, let `f : (ℙ¹_K)^m ⟶ Z`, and let `C` be a closed
subspace of `(ℙ¹_K)^m` whose point space is preirreducible and which `f` carries to a single
point `ζ`. Then there is an open subspace `U ⊆ (GL₂)^m` containing the `K`-point given by the
`m`-tuple of identity matrices such that for every `K`-point `M` of `(GL₂)^m` factoring
through `U` and any two `K`-rational points `l₁, l₂` of `C`,

```
f(M · l₁) = f(M · l₂).
```

This is the conclusion the induction of [Stacks, Tag 0AEM] runs on. The open subspace is the
one [Stacks, Tag 0AEJ] produces; over its `K`-points the orbit map factors through an
algebraic space finite over `Spec K`, and such a factorisation is constant on the rational
points of a space with irreducible point space when the field is algebraically closed. -/
theorem exists_isOpenSubspace_forall_comp_matrixAut_comp_eq
    (C : Subfunctor (projectiveLinePower K B hK (Fin m))) (ζ : baseFunctor K B hK ⟶ Z)
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of K)) hK Z)
    (hz_sep : IsSeparated B (Spec (CommRingCat.of K)) hK z)
    (hz_lft : IsLocallyOfFiniteType B (Spec (CommRingCat.of K)) hK z)
    (hC : IsClosedSubspace B (Spec (CommRingCat.of K)) hK C)
    (hconst : C.ι ≫ f = toBaseFunctor K B hK C.toFunctor ≫ ζ)
    (hCirr : PreirreducibleSpace (points B (Spec (CommRingCat.of K)) hK C.toFunctor)) :
    ∃ U : Subfunctor (generalLinearTwoPowerFunctor K B hK m),
      IsOpenSubspace B (Spec (CommRingCat.of K)) hK U ∧
      (generalLinearTwoPowerFieldValuedPoint K B hK m 1).class B (Spec (CommRingCat.of K)) hK
          (generalLinearTwoPowerFunctor K B hK m) ∈
        Set.range (pointsMap B (Spec (CommRingCat.of K)) hK U.toFunctor U.ι) ∧
      ∀ (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) K)
          (s : baseFunctor K B hK ⟶ U.toFunctor),
        s ≫ U.ι = yoneda.map (generalLinearTwoPowerSitePoint K B hK m M) →
        ∀ l₁ l₂ : baseFunctor K B hK ⟶ C.toFunctor,
          (l₁ ≫ C.ι) ≫ (projectiveLinePowerFunctorMatrixAut K B hK m M).hom ≫ f =
            (l₂ ≫ C.ι) ≫ (projectiveLinePowerFunctorMatrixAut K B hK m M).hom ≫ f := by
  obtain ⟨U, hU, hb, horbit⟩ :=
    exists_isOpenSubspace_forall_isFinite_comp_eq_orbitMap K B hK m z f C ζ hZ hz_sep hz_lft
      hC hconst
  refine ⟨U, hU, hb, fun M s hs l₁ l₂ ↦ ?_⟩
  obtain ⟨F, q, i, t, hfin, hfac⟩ := horbit M s hs
  have key : ∀ l : baseFunctor K B hK ⟶ C.toFunctor,
      (l ≫ C.ι) ≫ (projectiveLinePowerFunctorMatrixAut K B hK m M).hom ≫ f = (l ≫ t) ≫ i :=
    fun l ↦ by rw [Category.assoc, hfac, Category.assoc]
  rw [key, key, comp_eq_comp_of_isFinite_toBase B K hK q hfin t hCirr l₁ l₂]

/-- **`f(g · x) = f(g · y)` for the two rational points of the contracted piece.**

Same hypotheses as
`AlgebraicGeometry.Space.exists_isOpenSubspace_forall_comp_matrixAut_comp_eq`, with the two
rational points given as `K`-rational points `x` and `y` of `(ℙ¹_K)^m` which *factor through*
the contracted piece — the shape in which
`AlgebraicGeometry.Space.exists_reducedClosedSubspace_pair_ne_of_infinite_fibre` produces
them. The conclusion is then literally the step of [Stacks, Tag 0AEM]: for every `K`-point `M`
of the open neighbourhood `U` of the identity,

```
f(M · x) = f(M · y).
```

The two points are not required to be distinct; the induction of 0AEM applies this to a pair
it has already arranged to be distinct. -/
theorem exists_isOpenSubspace_forall_comp_matrixAut_comp_eq_of_factors
    (C : Subfunctor (projectiveLinePower K B hK (Fin m))) (ζ : baseFunctor K B hK ⟶ Z)
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of K)) hK Z)
    (hz_sep : IsSeparated B (Spec (CommRingCat.of K)) hK z)
    (hz_lft : IsLocallyOfFiniteType B (Spec (CommRingCat.of K)) hK z)
    (hC : IsClosedSubspace B (Spec (CommRingCat.of K)) hK C)
    (hconst : C.ι ≫ f = toBaseFunctor K B hK C.toFunctor ≫ ζ)
    (hCirr : PreirreducibleSpace (points B (Spec (CommRingCat.of K)) hK C.toFunctor))
    (x y : baseFunctor K B hK ⟶ projectiveLinePower K B hK (Fin m))
    (hx : ∃ l, l ≫ C.ι = x) (hy : ∃ l, l ≫ C.ι = y) :
    ∃ U : Subfunctor (generalLinearTwoPowerFunctor K B hK m),
      IsOpenSubspace B (Spec (CommRingCat.of K)) hK U ∧
      (generalLinearTwoPowerFieldValuedPoint K B hK m 1).class B (Spec (CommRingCat.of K)) hK
          (generalLinearTwoPowerFunctor K B hK m) ∈
        Set.range (pointsMap B (Spec (CommRingCat.of K)) hK U.toFunctor U.ι) ∧
      ∀ (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) K)
          (s : baseFunctor K B hK ⟶ U.toFunctor),
        s ≫ U.ι = yoneda.map (generalLinearTwoPowerSitePoint K B hK m M) →
        x ≫ (projectiveLinePowerFunctorMatrixAut K B hK m M).hom ≫ f =
          y ≫ (projectiveLinePowerFunctorMatrixAut K B hK m M).hom ≫ f := by
  obtain ⟨lx, rfl⟩ := hx
  obtain ⟨ly, rfl⟩ := hy
  obtain ⟨U, hU, hb, hagree⟩ :=
    exists_isOpenSubspace_forall_comp_matrixAut_comp_eq K B hK m z f C ζ hZ hz_sep hz_lft hC
      hconst hCirr
  exact ⟨U, hU, hb, fun M s hs ↦ hagree M s hs lx ly⟩

/-- **The translates of the contracted piece of [Stacks, Tag 0AEM] agree on its two rational
points.**

This is `AlgebraicGeometry.Space.exists_isOpenSubspace_forall_comp_matrixAut_comp_eq_of_factors`
at the reduced closed subspace on an irreducible closed set of points of `(ℙ¹_K)^m`, which is
the shape in which
`Space.exists_reducedClosedSubspace_pair_ne_of_infinite_fibre_projectiveLinePower`
produces the contracted piece together with two distinct `K`-rational points of it: that
statement supplies the closed set, its irreducibility, and the two factorisations through the
subspace, and `AlgebraicGeometry.Space.rationalPointOfClosedPoint_ne` their distinctness. -/
theorem exists_isOpenSubspace_forall_comp_matrixAut_comp_eq_reducedClosedSubspace
    (T : Set (points B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK (Fin m))))
    (hT : IsClosed T) (hTirr : IsPreirreducible T) (ζ : baseFunctor K B hK ⟶ Z)
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of K)) hK Z)
    (hz_sep : IsSeparated B (Spec (CommRingCat.of K)) hK z)
    (hz_lft : IsLocallyOfFiniteType B (Spec (CommRingCat.of K)) hK z)
    (hconst : (reducedClosedSubspace B (Spec (CommRingCat.of K)) hK
          (projectiveLinePower K B hK (Fin m))
          (isAlgebraicSpace_projectiveLinePowerFin K B hK m) T hT).ι ≫ f =
      toBaseFunctor K B hK (reducedClosedSubspace B (Spec (CommRingCat.of K)) hK
          (projectiveLinePower K B hK (Fin m))
          (isAlgebraicSpace_projectiveLinePowerFin K B hK m) T hT).toFunctor ≫ ζ)
    (x y : baseFunctor K B hK ⟶ projectiveLinePower K B hK (Fin m))
    (hx : ∃ l, l ≫ (reducedClosedSubspace B (Spec (CommRingCat.of K)) hK
      (projectiveLinePower K B hK (Fin m))
      (isAlgebraicSpace_projectiveLinePowerFin K B hK m) T hT).ι = x)
    (hy : ∃ l, l ≫ (reducedClosedSubspace B (Spec (CommRingCat.of K)) hK
      (projectiveLinePower K B hK (Fin m))
      (isAlgebraicSpace_projectiveLinePowerFin K B hK m) T hT).ι = y) :
    ∃ U : Subfunctor (generalLinearTwoPowerFunctor K B hK m),
      IsOpenSubspace B (Spec (CommRingCat.of K)) hK U ∧
      (generalLinearTwoPowerFieldValuedPoint K B hK m 1).class B (Spec (CommRingCat.of K)) hK
          (generalLinearTwoPowerFunctor K B hK m) ∈
        Set.range (pointsMap B (Spec (CommRingCat.of K)) hK U.toFunctor U.ι) ∧
      ∀ (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) K)
          (s : baseFunctor K B hK ⟶ U.toFunctor),
        s ≫ U.ι = yoneda.map (generalLinearTwoPowerSitePoint K B hK m M) →
        x ≫ (projectiveLinePowerFunctorMatrixAut K B hK m M).hom ≫ f =
          y ≫ (projectiveLinePowerFunctorMatrixAut K B hK m M).hom ≫ f :=
  exists_isOpenSubspace_forall_comp_matrixAut_comp_eq_of_factors K B hK m z f _ ζ hZ hz_sep
    hz_lft
    (isClosedSubspace_reducedClosedSubspace B (Spec (CommRingCat.of K)) hK
      (projectiveLinePower K B hK (Fin m))
      (isAlgebraicSpace_projectiveLinePowerFin K B hK m) T hT) hconst
    (preirreducibleSpace_points_reducedClosedSubspace B (Spec (CommRingCat.of K)) hK
      (projectiveLinePower K B hK (Fin m))
      (isAlgebraicSpace_projectiveLinePowerFin K B hK m) T hT hTirr) x y hx hy

end AlgebraicGeometry.Space

end
