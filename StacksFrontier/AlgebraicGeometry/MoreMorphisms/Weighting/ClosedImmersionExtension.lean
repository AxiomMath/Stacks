module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FibreSumTerm
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Weighting
public import StacksCore.Tactic.StacksAttribute

/-!
# Extending a weighting of a closed subscheme by zero

Let `j : Z ⟶ X` be a closed immersion and `f : X ⟶ Y` a morphism of schemes. A weighting of the
composite `j ≫ f` extends by zero to a weighting of `f`: any integer-valued function on `X`
which vanishes off the closed subscheme and restricts to the given weighting on it is a
weighting of `f`.

## Main results

* `AlgebraicGeometry.IsWeighting.extendByZero_of_isClosedImmersion` — the statement just made.
* `AlgebraicGeometry.separableDegreeWeightedFiberTerm_comp_of_isIso_residueFieldMap` — the term
  of a weighted fibre sum is unchanged by precomposing the morphism and its weight with a
  morphism that induces an isomorphism on the residue field at the point in question. This is
  the closed-immersion analogue of
  `AlgebraicGeometry.separableDegreeWeightedFiberTerm_comp_isPreimmersion`, stated under the
  weakest hypothesis that makes the proof go through.

## Implementation notes

Given chart data `h : U ⟶ X`, `π : U ⟶ V`, `g : V ⟶ Y` for `f`, the chart is pulled back along
`j` to `U ×_X Z`, with projections `i := pullback.fst h j` to `U` and
`h_Z := pullback.snd h j` to `Z`, and `π_Z := i ≫ π`. Then `i` is a closed immersion, being a
base change of `j`, so `π_Z` is finite; and the morphism `U ×_X Z ⟶ Z ×_Y V` induced by the
pulled-back chart is an open immersion. That last point is the only piece of pullback
bookkeeping: writing `P := X ×_Y V` and `Q := Z ×_Y V` and letting `j_Q : Q ⟶ P` be the morphism
induced by `j`, two applications of `CategoryTheory.IsPullback.of_bot` identify `Q` with
`Z ×_X P` and then exhibit `U ×_X Z ⟶ Q` as a base change of the open immersion `U ⟶ P` along
`j_Q`. Open immersions are stable under base change, which finishes it.

The two weighted fibre sums are then compared term by term. The term of `π` at a point `u` of
`U` vanishes unless `w (h u) ≠ 0`, hence unless `h u` lies in the range of `j`, which by
`AlgebraicGeometry.Scheme.Pullback.range_fst` is exactly the range of `i`; and `i` is injective,
so the unconditional `finsum` over `U` collapses to the one over `U ×_X Z`. At a point `i z` the
two terms agree because a closed immersion is a preimmersion, so it induces an isomorphism on
residue fields, which leaves the separable degree over the residue field of the image in `V`
unchanged: the two residue-field extensions have the same base and isomorphic top fields, the
isomorphism being compatible with the structure maps by functoriality of
`AlgebraicGeometry.Scheme.Hom.residueFieldMap`.

## References

* [Stacks Project, Tag 0F3A](https://stacks.math.columbia.edu/tag/0F3A)
* [Stacks Project, Tag 0GK8](https://stacks.math.columbia.edu/tag/0GK8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section ResidueField

/-- Precomposing with a morphism which induces an isomorphism on the residue field at a point
does not change the separable degree of the residue-field extension there: the two extensions
have the same base field and isomorphic top fields, compatibly with the structure maps. -/
private lemma finSepDegree_residueFieldMap_comp_of_isIso
    {Z U V : Scheme.{u}} (i : Z ⟶ U) (π : U ⟶ V) (z : Z)
    (hres : IsIso (i.residueFieldMap z)) :
    letI := ((i ≫ π).residueFieldMap z).hom.toAlgebra
    letI := (π.residueFieldMap (i z)).hom.toAlgebra
    Field.finSepDegree (V.residueField ((i ≫ π) z)) (Z.residueField z) =
      Field.finSepDegree (V.residueField (π (i z))) (U.residueField (i z)) := by
  let : Algebra (V.residueField ((i ≫ π) z)) (Z.residueField z) :=
    ((i ≫ π).residueFieldMap z).hom.toAlgebra
  -- The same instance under the other spelling `π (i z)` of the point `(i ≫ π) z`: the two
  -- agree definitionally, but not at the reducible transparency instance search uses.
  let : Algebra (V.residueField (π (i z))) (Z.residueField z) :=
    ((i ≫ π).residueFieldMap z).hom.toAlgebra
  let : Algebra (V.residueField (π (i z))) (U.residueField (i z)) :=
    (π.residueFieldMap (i z)).hom.toAlgebra
  let e : U.residueField (i z) ≃+* Z.residueField z :=
    RingEquiv.ofBijective (i.residueFieldMap z).hom
      ((ConcreteCategory.isIso_iff_bijective (i.residueFieldMap z)).mp hres)
  have hcompat : ∀ a : V.residueField (π (i z)),
      e (algebraMap (V.residueField (π (i z))) (U.residueField (i z)) a) =
        algebraMap (V.residueField (π (i z))) (Z.residueField z) a := by
    intro a
    change (i.residueFieldMap z).hom ((π.residueFieldMap (i z)).hom a) =
      ((i ≫ π).residueFieldMap z).hom a
    rw [Scheme.residueFieldMap_comp]
    rfl
  exact (Field.finSepDegree_eq_of_equiv (V.residueField (π (i z)))
    (U.residueField (i z)) (Z.residueField z) (AlgEquiv.ofRingEquiv hcompat)).symm

/-- The term of a weighted fibre sum is unchanged by restricting the source along a morphism
which induces an isomorphism on the residue field at the point in question. This is the
counterpart, for immersions, of
`AlgebraicGeometry.separableDegreeWeightedFiberTerm_comp_isPreimmersion`. -/
lemma separableDegreeWeightedFiberTerm_comp_of_isIso_residueFieldMap
    {Z U V : Scheme.{u}} (i : Z ⟶ U) (π : U ⟶ V) (w : U → ℤ) (v : V) (z : Z)
    (hres : IsIso (i.residueFieldMap z)) :
    separableDegreeWeightedFiberTerm (i ≫ π) (w ∘ i) v z =
      separableDegreeWeightedFiberTerm π w v (i z) := by
  by_cases hv : π (i z) = v
  · subst hv
    have hp := Scheme.Hom.comp_apply i π z
    cases hp
    simp only [separableDegreeWeightedFiberTerm, Function.comp_apply, Scheme.Hom.comp_apply,
      reduceIte]
    rw [finSepDegree_residueFieldMap_comp_of_isIso i π z hres]
  · rw [separableDegreeWeightedFiberTerm_of_notMem_fiber π w hv,
      separableDegreeWeightedFiberTerm_of_notMem_fiber (i ≫ π) (w ∘ i)
        (by simpa only [Scheme.Hom.comp_apply] using hv)]

end ResidueField

section ClosedChart

/-- The chart data defining a weighting pulls back along a closed immersion `j : Z ⟶ X`: the
morphism `U ×_X Z ⟶ Z ×_Y V` induced by the pulled-back chart is again an open immersion,
because it is the base change along `Z ×_Y V ⟶ X ×_Y V` of the open immersion
`U ⟶ X ×_Y V`. -/
private lemma isOpenImmersion_lift_pullback_fst
    {Z X Y U V : Scheme.{u}} (j : Z ⟶ X) {f : X ⟶ Y}
    (h : U ⟶ X) (π : U ⟶ V) (g : V ⟶ Y) (comm : h ≫ f = π ≫ g)
    (hU : IsOpenImmersion (pullback.lift h π comm))
    (commZ : pullback.snd h j ≫ (j ≫ f) = (pullback.fst h j ≫ π) ≫ g) :
    IsOpenImmersion (pullback.lift (pullback.snd h j) (pullback.fst h j ≫ π) commZ) := by
  let jQ : (pullback (j ≫ f) g : Scheme) ⟶ (pullback f g : Scheme) :=
    pullback.map (j ≫ f) g f g j (𝟙 V) (𝟙 Y) (by simp) (by simp)
  have hjQ₁ : jQ ≫ pullback.fst f g = pullback.fst (j ≫ f) g ≫ j := by
    simp only [jQ, pullback.map, pullback.lift_fst]
  have hjQ₂ : jQ ≫ pullback.snd f g = pullback.snd (j ≫ f) g := by
    simp only [jQ, pullback.map, pullback.lift_snd, Category.comp_id]
  have hA : IsPullback (pullback.fst (j ≫ f) g) jQ j (pullback.fst f g) := by
    refine IsPullback.of_bot ?_ hjQ₁.symm (IsPullback.of_hasPullback f g)
    rw [hjQ₂]
    exact IsPullback.of_hasPullback (j ≫ f) g
  have hm₁ : pullback.lift (pullback.snd h j) (pullback.fst h j ≫ π) commZ ≫
      pullback.fst (j ≫ f) g = pullback.snd h j := pullback.lift_fst _ _ _
  have hm₂ : pullback.lift (pullback.snd h j) (pullback.fst h j ≫ π) commZ ≫ jQ =
      pullback.fst h j ≫ pullback.lift h π comm := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hjQ₁, pullback.lift_fst]
      rw [← Category.assoc, hm₁]
      exact pullback.condition.symm
    · simp only [Category.assoc, hjQ₂, pullback.lift_snd]
  have hTop : IsPullback (pullback.fst h j)
      (pullback.lift (pullback.snd h j) (pullback.fst h j ≫ π) commZ)
      (pullback.lift h π comm) jQ := by
    refine IsPullback.of_bot ?_ hm₂.symm hA.flip
    rw [hm₁, pullback.lift_fst]
    exact IsPullback.of_hasPullback h j
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) hTop hU

/-- The weighted fibre sum of a chart of `f` for a weight supported on a closed subscheme equals
the weighted fibre sum of the pulled-back chart of `j ≫ f` for the restricted weight. -/
private lemma separableDegreeWeightedFiberSum_eq_of_extendByZero
    {Z X U V : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j]
    (h : U ⟶ X) (π : U ⟶ V) (w : X → ℤ) (wZ : Z → ℤ)
    (hw : ∀ x : X, x ∉ Set.range j → w x = 0)
    (hwj : ∀ z : Z, w (j z) = wZ z) :
    separableDegreeWeightedFiberSum π (w ∘ h) =
      separableDegreeWeightedFiberSum (pullback.fst h j ≫ π) (wZ ∘ pullback.snd h j) := by
  classical
  have hweight : wZ ∘ pullback.snd h j = (w ∘ h) ∘ pullback.fst h j := by
    funext x
    change wZ (pullback.snd h j x) = w (h (pullback.fst h j x))
    have hx : h (pullback.fst h j x) = j (pullback.snd h j x) := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun q : (pullback h j : Scheme) ⟶ X => q x)
          (pullback.condition : pullback.fst h j ≫ h = pullback.snd h j ≫ j)
    rw [hx, hwj]
  funext v
  have hvan : ∀ u : U, u ∉ Set.range (pullback.fst h j) →
      separableDegreeWeightedFiberTerm π (w ∘ h) v u = 0 := by
    intro u hu
    rw [Scheme.Pullback.range_fst] at hu
    have hzero : w (h u) = 0 := hw (h u) (by simpa using hu)
    by_cases huv : π u = v
    · rw [separableDegreeWeightedFiberTerm_of_mem_fiber π (w ∘ h) huv]
      simp [hzero]
    · exact separableDegreeWeightedFiberTerm_of_notMem_fiber π (w ∘ h) huv
  have hind : Set.indicator (Set.range (pullback.fst h j))
      (separableDegreeWeightedFiberTerm π (w ∘ h) v) =
      separableDegreeWeightedFiberTerm π (w ∘ h) v :=
    Set.indicator_eq_self.2 fun u hu ↦ by_contra fun h' ↦ hu (hvan u h')
  rw [hweight, separableDegreeWeightedFiberSum_eq_finsum_term,
    separableDegreeWeightedFiberSum_eq_finsum_term]
  calc (∑ᶠ u : U, separableDegreeWeightedFiberTerm π (w ∘ h) v u)
      = ∑ᶠ u ∈ Set.range (pullback.fst h j),
          separableDegreeWeightedFiberTerm π (w ∘ h) v u := by
        rw [finsum_mem_def, hind]
    _ = ∑ᶠ x : (pullback h j : Scheme),
          separableDegreeWeightedFiberTerm π (w ∘ h) v (pullback.fst h j x) :=
        finsum_mem_range (pullback.fst h j).isEmbedding.injective
    _ = ∑ᶠ x : (pullback h j : Scheme),
          separableDegreeWeightedFiberTerm (pullback.fst h j ≫ π)
            ((w ∘ h) ∘ pullback.fst h j) v x := finsum_congr fun x ↦
        (separableDegreeWeightedFiberTerm_comp_isPreimmersion (pullback.fst h j) π (w ∘ h) v x).symm

/-- A weighting of a closed subscheme, extended by zero, is a weighting of the ambient
morphism: if `j : Z ⟶ X` is a closed immersion, `wZ` is a weighting of `j ≫ f`, and `w` is an
integer-valued function on `X` vanishing off the range of `j` and restricting to `wZ` along `j`,
then `w` is a weighting of `f`. -/
theorem IsWeighting.extendByZero_of_isClosedImmersion {Z X Y : Scheme.{u}}
    (j : Z ⟶ X) [IsClosedImmersion j] {f : X ⟶ Y} {wZ : Z → ℤ}
    (hwZ : IsWeighting (j ≫ f) wZ) (w : X → ℤ)
    (hw : ∀ x : X, x ∉ Set.range j → w x = 0)
    (hwj : ∀ z : Z, w (j z) = wZ z) :
    IsWeighting f w := by
  intro U V h π g comm hg hU hπ
  have commZ : pullback.snd h j ≫ (j ≫ f) = (pullback.fst h j ≫ π) ≫ g := by
    rw [Category.assoc, ← comm, pullback.condition_assoc]
  rw [separableDegreeWeightedFiberSum_eq_of_extendByZero j h π w wZ hw hwj]
  exact hwZ (pullback.snd h j) (pullback.fst h j ≫ π) g commZ hg
    (isOpenImmersion_lift_pullback_fst j h π g comm hU commZ) inferInstance

end ClosedChart

end AlgebraicGeometry
