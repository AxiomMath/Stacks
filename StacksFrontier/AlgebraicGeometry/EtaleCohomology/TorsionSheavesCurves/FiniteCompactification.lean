module

public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationOverField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.RelativeNormal
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# A finite compactification of a finite cover of an open subscheme

Let `Y` be a scheme of finite type over a field `k`, `j : O ⟶ Y` a quasi-compact open immersion and
`f : T ⟶ O` a finite morphism with `T` reduced. The relative normalization `π : Yb ⟶ Y` of `Y` in
`T` is finite (Tag 0BXS), `T` is an open dense subscheme of `Yb` (Zariski's main theorem, in
Mathlib's form `Scheme.Hom.toNormalization`), and the square

```
T --j'--> Yb
|         |
f         π
v         v
O --j---> Y
```

is cartesian: the image of `T` is open and closed in `π⁻¹(O)` (closed because `f` is finite and
`π⁻¹(O) ⟶ O` separated) and dense in it. If `T` is normal so is `Yb`.

## Main results

* `AlgebraicGeometry.exists_isPullback_isFinite_relativeNormalization`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The finite compactification of a finite cover of an open subscheme.** Let `Y` be locally of
finite type over a field `k`, `j : O ⟶ Y` a quasi-compact open immersion and `f : T ⟶ O` a finite
morphism with `T` reduced. Then there are a finite `π : Yb ⟶ Y` and a dominant open immersion
`j' : T ⟶ Yb` with `T = O ×_Y Yb`, and `Yb` is normal if `T` is. -/
theorem exists_isPullback_isFinite_relativeNormalization (k : Type u) [Field k]
    {Y O T : Scheme.{u}} (pY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType pY]
    (j : O ⟶ Y) [IsOpenImmersion j] [QuasiCompact j] (f : T ⟶ O) [IsFinite f] [IsReduced T] :
    ∃ (Yb : Scheme.{u}) (π : Yb ⟶ Y) (j' : T ⟶ Yb), IsFinite π ∧ IsOpenImmersion j' ∧
      IsPullback j' f π j ∧ IsDominant j' ∧ (IsNormal T → IsNormal Yb) := by
  set g := f ≫ j
  have : LocallyOfFiniteType (g ≫ pY) := inferInstance
  have hfin : IsFinite g.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType_over_field k pY (g ≫ pY) g rfl
  have : IsOpenImmersion g.toNormalization := inferInstance
  refine ⟨g.normalization, g.fromNormalization, g.toNormalization, hfin, inferInstance, ?_,
    inferInstance, fun hT => ?_⟩
  · have hw : g.toNormalization ≫ g.fromNormalization = f ≫ j :=
      g.toNormalization_fromNormalization
    refine (IsOpenImmersion.isPullback f g.toNormalization j g.fromNormalization hw ?_).flip
    set π := g.fromNormalization
    set j' := g.toNormalization
    set P := π ⁻¹ᵁ j.opensRange
    have hsub : j'.opensRange ≤ P := by
      rintro _ ⟨t, rfl⟩
      show π.base (j'.base t) ∈ Set.range j.base
      rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    let l : T ⟶ P := IsOpenImmersion.lift P.ι j' (by rw [P.range_ι]; exact hsub)
    have hl : l ≫ P.ι = j' := IsOpenImmersion.lift_fac _ _ _
    let m : (P : Scheme.{u}) ⟶ O := (π ∣_ j.opensRange) ≫ j.isoOpensRange.inv
    have hm : l ≫ m = f := by
      rw [← cancel_mono j]
      simp only [m, Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
      rw [morphismRestrict_ι, ← Category.assoc, hl, hw]
    have : IsSeparated m := inferInstance
    have : UniversallyClosed (l ≫ m) := by rw [hm]; infer_instance
    have : UniversallyClosed l := UniversallyClosed.of_comp_of_isSeparated l m
    have hcl : IsClosed (Set.range l.base) := l.isClosedMap.isClosed_range
    have hden : Dense (Set.range l.base) := by
      have hd : DenseRange j'.base := j'.denseRange
      refine Dense.mono ?_ (hd.preimage P.ι.isOpenEmbedding.isOpenMap)
      rintro ⟨y, hy⟩ ⟨t, ht⟩
      refine ⟨t, P.ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hl]
      exact ht
    have huniv : Set.range l.base = Set.univ := by
      rw [← hcl.closure_eq]; exact hden.closure_eq
    apply le_antisymm _ hsub
    intro y hy
    obtain ⟨t, ht⟩ : (⟨y, hy⟩ : P) ∈ Set.range l.base := huniv ▸ Set.mem_univ _
    refine ⟨t, ?_⟩
    rw [← hl, Scheme.Hom.comp_apply, ht]
    rfl
  · have := hT
    have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (g ≫ pY)
    refine isNormal_normalization g (fun V hV => ?_)
    have : CompactSpace V := isCompact_iff_compactSpace.mp hV
    have : IsNoetherian V := AlgebraicGeometry.IsNoetherian.mk
    exact finite_irreducibleComponents_of_isNoetherian

end AlgebraicGeometry

end
