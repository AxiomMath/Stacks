module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChartFibreComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementObj
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.Criterion

/-!
# The projections of the complement of the diagonals are pairwise distinct

The valuative criterion step in the proof of Stacks 089J starts from a point of the dense open
`V` with values in the fraction field `K` of a valuation ring, and reads it as **`d` distinct
`K`-points of the étale chart `W`** lying over one `K`-point of the algebraic space. Agreement
over the algebraic space is
`AlgebraicGeometry.Space.SpacesEtale.yoneda_map_diagonalComplementProj_comp_chart_eq`; what is
missing, and what this file supplies, is *distinctness*.

Distinctness is exactly what removing the diagonals buys, and the reason is that the diagonal
`U ⟶ U ×_X U` is the universal solution to "the two projections agree": a morphism into
`U ×_X U` whose two components coincide factors through it. So if two components of a morphism
into the self-product coincided, the morphism would land in the corresponding diagonal, and
every point of the complement of the diagonals avoids that locus.

Note that distinctness is asserted for the *morphisms*, not for the images in the point set of
`W`: two distinct `K`-points of `W` over the same `K`-point of `X` may well have the same image
in `|W|` — they do already for `W = Spec L`, `X = Spec k` with `L/k` quadratic Galois, whose
self-product has a point off the diagonal lying over the unique point of `|W|` twice. It is the
morphisms that the valuative criterion lifts, so it is the morphisms that have to be
distinguished.

Because the lifts counted are morphisms, the fibre-degree bound of [Stacks, Tag 03JL] bounds
them, and distinctness turns into *emptiness*: the complement of the diagonals in the `n`-fold
self-product of a chart with universally bounded fibres has no points at all once `n` exceeds
the bound. The bound on the cardinality of the topological fibres of `|W| → |X|` would not do,
and for the quadratic Galois extension above it does not.

## Main definitions

* `AlgebraicGeometry.Space.fieldSpecPoint`: the canonical point of the presheaf represented by
  the spectrum of a field in the site, which is what makes the distinctness statement applicable
  to the generic point of a valuative square.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.comp_diagonalComplementπ_ne`: **two distinct projections
  of the complement of the diagonals never agree** after composition with any morphism from a
  presheaf which has at least one point.
* `AlgebraicGeometry.Space.SpacesEtale.comp_yoneda_map_diagonalComplementProj_ne`: the same for
  the projections `V ⟶ W` of
  `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementProj`, which is the form the valuative
  criterion of Stacks 089J consumes.
* `AlgebraicGeometry.Space.SpacesEtale.exists_forall_isEmpty_points_diagonalComplement`:
  **the complement of the diagonals in a high enough self-product of a chart with universally
  bounded fibres has no points at all.** A point of it provides `n` pairwise distinct lifts of
  one field-valued point of `X` to the chart, and the fibre-degree bound of Stacks 03JL bounds
  the number of those lifts, so no such point exists once `n` exceeds the bound.

## What is and is not proved

Nothing here carries a Stacks attribute. Tag 0726 sits on
`AlgebraicGeometry.Space.SpacesEtale.diagonalComplement`, Tag 03BU on
`AlgebraicGeometry.Space.points` and Tag 03JL on
`AlgebraicGeometry.Space.HasUniversallyBoundedFibers`; what is added is the consequence of the
three.

The hypothesis that the source presheaf have a point cannot be dropped: a morphism out of the
empty scheme has all its components equal. For the generic point of a valuative square the
source is the spectrum of a field and the point is
`AlgebraicGeometry.Space.fieldSpecPoint`.

Nothing is claimed about the images in the point set of the chart; as explained above, that
statement is false.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The canonical point of the presheaf represented by the spectrum of a field in the site.**
It is the class of the field-valued point whose section is the identity. -/
def fieldSpecPoint {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
    (b : Spec (.of K) ⟶ S) :
    points B S hS (yoneda.obj (siteObject B S hS hK b)) :=
  FieldValuedPoint.class B S hS _
    { carrier := K, contained := hK, toBase := b, value := 𝟙 (siteObject B S hS hK b) }

namespace SpacesEtale

variable (X : AlgebraicSpaces B S hS)

/-- **Two distinct projections of the complement of the diagonals never agree.** Let `U` be an
object of the spaces-étale site of `X` with separated structure morphism, let `g` be a morphism
of presheaves into the complement of the diagonals of the `n`-fold self-product of `U` over `X`,
and suppose the source of `g` has at least one point. Then for `i ≠ j` the composites of `g`
with the `i`-th and the `j`-th projection to `U` are different.

If they agreed, then `g` followed by the pair of projections onto the `(i, j)`-factors of
`U ×_X U` would equal that common composite followed by the diagonal, because a morphism into a
fibre product is determined by its two components; so every point of the source would be sent
into the locus where the `i`-th and `j`-th factors collide, and no point of the complement of
the diagonals lies there. -/
theorem comp_diagonalComplementπ_ne (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.obj.hom.hom)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : F ⟶ (underlying B S hS X (diagonalComplement B S hS X U n hsep)).obj)
    (t : points B S hS F) {i j : Fin n} (hij : i ≠ j) :
    g ≫ ((toSpaces B S hS X).map (diagonalComplementπ B S hS X U n hsep i)).hom ≠
      g ≫ ((toSpaces B S hS X).map (diagonalComplementπ B S hS X U n hsep j)).hom := by
  intro heq
  have sq : IsPullback
      ((toSpaces B S hS X).map
        (pullback.fst (toFinal B S hS U) (toFinal B S hS U))).hom
      ((toSpaces B S hS X).map
        (pullback.snd (toFinal B S hS U) (toFinal B S hS U))).hom
      U.obj.hom.hom U.obj.hom.hom :=
    AlgebraicSpaces.isPullback_hom B S hS (isPullback_toSpaces_prodTwo B S hS X U)
  have hπ : ∀ k : Fin n, ((toSpaces B S hS X).map
        (diagonalComplementπ B S hS X U n hsep k)).hom =
      ((toSpaces B S hS X).map (diagonalComplementι B S hS X U n hsep)).hom ≫
        ((toSpaces B S hS X).map (Pi.π (fun _ : Fin n ↦ U) k)).hom :=
    fun k ↦ hom_toSpaces_map_comp B S hS X _ _
  have h1 : ((toSpaces B S hS X).map (projPair B S hS X U n i j)).hom ≫
      ((toSpaces B S hS X).map
        (pullback.fst (toFinal B S hS U) (toFinal B S hS U))).hom =
      ((toSpaces B S hS X).map (Pi.π (fun _ : Fin n ↦ U) i)).hom := by
    rw [← hom_toSpaces_map_comp, projPair_comp_fst]
  have h1' : ((toSpaces B S hS X).map (projPair B S hS X U n i j)).hom ≫
      ((toSpaces B S hS X).map
        (pullback.snd (toFinal B S hS U) (toFinal B S hS U))).hom =
      ((toSpaces B S hS X).map (Pi.π (fun _ : Fin n ↦ U) j)).hom := by
    rw [← hom_toSpaces_map_comp, projPair_comp_snd]
  have h2 : ((toSpaces B S hS X).map (diagTwo B S hS X U)).hom ≫
      ((toSpaces B S hS X).map
        (pullback.fst (toFinal B S hS U) (toFinal B S hS U))).hom = 𝟙 _ := by
    rw [← hom_toSpaces_map_comp, diagTwo_comp_fst, CategoryTheory.Functor.map_id]
    rfl
  have h2' : ((toSpaces B S hS X).map (diagTwo B S hS X U)).hom ≫
      ((toSpaces B S hS X).map
        (pullback.snd (toFinal B S hS U) (toFinal B S hS U))).hom = 𝟙 _ := by
    rw [← hom_toSpaces_map_comp, diagTwo_comp_snd, CategoryTheory.Functor.map_id]
    rfl
  -- the morphism into the self-product, and the pair of its `i`-th and `j`-th components
  have hpair : (g ≫ ((toSpaces B S hS X).map
        (diagonalComplementι B S hS X U n hsep)).hom) ≫
        ((toSpaces B S hS X).map (projPair B S hS X U n i j)).hom =
      (g ≫ ((toSpaces B S hS X).map (diagonalComplementπ B S hS X U n hsep i)).hom) ≫
        ((toSpaces B S hS X).map (diagTwo B S hS X U)).hom := by
    refine sq.hom_ext ?_ ?_
    · simp only [Category.assoc, h1, h2, Category.comp_id, ← hπ i]
    · simp only [Category.assoc, h1', h2', Category.comp_id, ← hπ j]
      exact heq.symm
  -- hence every point of the source lands in the collision locus
  have hcol : pointsMap B S hS F (g ≫ ((toSpaces B S hS X).map
      (diagonalComplementι B S hS X U n hsep)).hom) t ∈
      collisionPoints B S hS X U n i j := by
    rw [collisionPoints, Set.mem_preimage, ← pointsMap_comp_apply, hpair, pointsMap_comp_apply]
    exact ⟨_, rfl⟩
  -- but no point of the complement of the diagonals does
  rw [pointsMap_comp_apply] at hcol
  exact (mem_diagonalComplementPoints_iff B S hS X U n _).1
    (mem_diagonalComplementPoints_pointsMap_diagonalComplementι B S hS X U n hsep
      (pointsMap B S hS F g t)) i j hij hcol

/-- **The `n` projections `V ⟶ W` of the complement of the diagonals are pairwise distinct**
after composition with any morphism from a presheaf with at least one point. This is the form
the valuative criterion in the proof of Stacks 089J consumes: with `F` the presheaf represented
by the spectrum of the fraction field of the valuation ring and `g` the generic point, it says
that the `n` induced `K`-points of the chart are pairwise distinct. -/
theorem comp_yoneda_map_diagonalComplementProj_ne (W : BigFppfOver B S hS)
    (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c) (hsep : IsSeparated B S hS c) (n : ℕ)
    (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅ (underlying B S hS X
      (diagonalComplement B S hS X (chartObj B S hS X W c hc) n hsep)).obj)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ yoneda.obj V)
    (t : points B S hS F) {i j : Fin n} (hij : i ≠ j) :
    g ≫ yoneda.map (diagonalComplementProj B S hS X W c hc hsep n V e i) ≠
      g ≫ yoneda.map (diagonalComplementProj B S hS X W c hc hsep n V e j) := by
  have key := comp_diagonalComplementπ_ne B S hS X (chartObj B S hS X W c hc) n hsep
    (g ≫ e.hom) t hij
  rw [yoneda_map_diagonalComplementProj B S hS X W c hc hsep n V e i,
    yoneda_map_diagonalComplementProj B S hS X W c hc hsep n V e j]
  intro heq
  refine key ?_
  rw [Category.assoc, Category.assoc]
  exact heq

/-- **The complement of the diagonals in a high enough self-product of a chart with universally
bounded fibres has no points.**

A point of the complement of the diagonals in the `n`-fold self-product of a chart
`c : W ⟶ X` is represented by a field-valued point, whose `n` projections to the chart are `n`
pairwise distinct morphisms `T ⟶ W` lying over one and the same field-valued point of `X`; the
fibre-degree bound of [Stacks, Tag 03JL] bounds the number of such morphisms. So the complement
of the diagonals is empty as soon as `n` exceeds that bound.

This is the emptiness that the proof of [Stacks, Tag 072B] draws from the fibre bound of its
chart. It is the *degree* bound of [Stacks, Tag 03JL] that gives it and not a bound on the
cardinality of the topological fibres of `|W| → |X|`: for `X = Spec k` and `W = Spec k'` with
`k'/k` separable quadratic, `|W| → |X|` is a bijection while `W ×_X W` has a point off the
diagonal. -/
theorem isEmpty_points_diagonalComplement_of_forall_le (W : BigFppfOver B S hS)
    (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c) (hsep : IsSeparated B S hS c) (d : ℕ)
    (hd : ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
      (ξ : yoneda.obj T ⟶ X.obj) (n : ℕ) (w : Fin n → (T ⟶ W)),
        (∀ k, yoneda.map (w k) ≫ c = ξ) → Function.Injective w → n ≤ d)
    (n : ℕ) (hn : d < n) :
    IsEmpty (points B S hS (underlying B S hS X
      (diagonalComplement B S hS X (chartObj B S hS X W c hc) n hsep)).1) := by
  refine ⟨fun x ↦ ?_⟩
  -- a field-valued representative of the point
  obtain ⟨z, -⟩ := Quot.exists_rep x
  -- its `n` projections to the chart, read as morphisms of the site through the Yoneda embedding
  obtain ⟨w, hwmap⟩ : ∃ w : Fin n → (z.siteObject B S hS _ ⟶ W), ∀ i : Fin n,
      yoneda.map (w i) = (fieldMorphism B S hS _ z ≫ ((toSpaces B S hS X).map
          (diagonalComplementπ B S hS X (chartObj B S hS X W c hc) n hsep i)).hom :
        yoneda.obj (z.siteObject B S hS _) ⟶ yoneda.obj W) :=
    ⟨fun i ↦ yoneda.preimage ((fieldMorphism B S hS _ z ≫ ((toSpaces B S hS X).map
        (diagonalComplementπ B S hS X (chartObj B S hS X W c hc) n hsep i)).hom :
      yoneda.obj (z.siteObject B S hS _) ⟶ yoneda.obj W)),
      fun i ↦ yoneda.map_preimage _⟩
  -- they are pairwise distinct, because the diagonals have been removed
  have hwinj : Function.Injective w := by
    intro a b hab
    by_contra hne
    refine comp_diagonalComplementπ_ne B S hS X (chartObj B S hS X W c hc) n hsep
      (fieldMorphism B S hS _ z) ((z.tautologicalPoint B S hS _).class B S hS _) hne ?_
    have h : yoneda.map (w a) = yoneda.map (w b) := by rw [hab]
    rw [hwmap a, hwmap b] at h
    exact h
  -- and they all lie over one field-valued point of `X`
  have hwover : ∀ i : Fin n, yoneda.map (w i) ≫ c =
      fieldMorphism B S hS _ z ≫
        (diagonalComplement B S hS X (chartObj B S hS X W c hc) n hsep).obj.hom.hom := by
    intro i
    rw [hwmap i]
    exact (Category.assoc _ _ _).trans (congrArg (fun k ↦ fieldMorphism B S hS _ z ≫ k)
      (hom_toSpaces_map_diagonalComplementπ_comp B S hS X
        (chartObj B S hS X W c hc) n hsep i))
  have hle := hd z.carrier z.field (z.siteObject B S hS _) (Iso.refl _)
    (fieldMorphism B S hS _ z ≫
      (diagonalComplement B S hS X (chartObj B S hS X W c hc) n hsep).obj.hom.hom)
    n w hwover hwinj
  omega


/-- **The complement of the diagonals in a high enough self-product of a chart with universally
bounded fibres has no points.**  This is
`AlgebraicGeometry.Space.SpacesEtale.isEmpty_points_diagonalComplement_of_forall_le` at the bound
of [Stacks, Tag 03JL]. -/
theorem exists_forall_isEmpty_points_diagonalComplement (W : BigFppfOver B S hS)
    (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c) (hsep : IsSeparated B S hS c)
    (hbound : HasUniversallyBoundedFibers B S hS W c) :
    ∃ d : ℕ, ∀ n : ℕ, d < n →
      IsEmpty (points B S hS (underlying B S hS X
        (diagonalComplement B S hS X (chartObj B S hS X W c hc) n hsep)).1) := by
  obtain ⟨d, hd⟩ := exists_forall_le_of_hasUniversallyBoundedFibers B S hS W c hbound
  exact ⟨d, isEmpty_points_diagonalComplement_of_forall_le B S hS X W c hc hsep d hd⟩

end SpacesEtale

end AlgebraicGeometry.Space

end
