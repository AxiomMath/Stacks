module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplex

/-!
# Restricting the diagonal open of a relative dualizing complex along an open immersion

Let `f : X ⟶ S` be a morphism of schemes, `W ⊆ X ×_S X` an open through which the relative
diagonal factors as a closed immersion `Δ : X ⟶ W`, and `j : U ⟶ X` an open immersion (for
instance the inclusion of an open of `X`). Write `f_U = j ≫ f : U ⟶ S`. The open immersion
`U ×_S U ⟶ X ×_S X` pulls `W` back to an open `W_U ⊆ U ×_S U`, and the relative diagonal of
`f_U` factors through `W_U` as a closed immersion `Δ_U : U ⟶ W_U`: the square

```
U ---Δ_U---> W_U
|             |
X ----Δ----> W
```

is cartesian, so `Δ_U` is a base change of `Δ`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.restrict`: the diagonal open `W_U` of `f_U`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.restrictInclusion`: the open immersion `W_U ⟶ W`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isPullback_restrictDiag`: the square above is
  cartesian.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.restrictInclusion_proj`: the first projection of
  `W_U` is that of `W` restricted.

## References

* [Stacks Project, Definition 48.28.1 (Tag 0E2T)](https://stacks.math.columbia.edu/tag/0E2T)
* [Stacks Project, Lemma 48.28.6 (Tag 0E2X)](https://stacks.math.columbia.edu/tag/0E2X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f) {Y : Scheme.{u}} (j : Y ⟶ X)
  [IsOpenImmersion j]

/-- The open immersion `U ×_S U ⟶ X ×_S X` induced by `j`. -/
abbrev pullbackOpensMap : pullback (j ≫ f) (j ≫ f) ⟶ pullback f f :=
  pullback.map (j ≫ f) (j ≫ f) f f j j (𝟙 S) (by simp) (by simp)

omit [IsOpenImmersion j] in
/-- The map `U ×_S U ⟶ X ×_S X` followed by the first projection is the first projection
followed by `j`. -/
@[reassoc (attr := simp)]
theorem pullbackOpensMap_fst :
    pullbackOpensMap j ≫ pullback.fst f f = pullback.fst (j ≫ f) (j ≫ f) ≫ j :=
  pullback.lift_fst _ _ _

omit [IsOpenImmersion j] in
/-- The map `U ×_S U ⟶ X ×_S X` followed by the second projection is the second projection
followed by `j`. -/
@[reassoc (attr := simp)]
theorem pullbackOpensMap_snd :
    pullbackOpensMap j ≫ pullback.snd f f = pullback.snd (j ≫ f) (j ≫ f) ≫ j :=
  pullback.lift_snd _ _ _

omit [IsOpenImmersion j] in
/-- The relative diagonal of `f_U` followed by `U ×_S U ⟶ X ×_S X` is the inclusion of `U`
followed by the relative diagonal of `f`. -/
theorem diagonal_comp_pullbackOpensMap :
    pullback.diagonal (j ≫ f) ≫ pullbackOpensMap j = j ≫ pullback.diagonal f := by
  ext <;> simp

/-- The square formed by the two relative diagonals and the inclusions of `U` is cartesian:
`U` is the preimage of `U ×_S U` under the relative diagonal of `f`. -/
theorem isPullback_diagonal_pullbackOpensMap :
    IsPullback (pullback.diagonal (j ≫ f)) j (pullbackOpensMap j) (pullback.diagonal f) := by
  have h := (pullback_map_diagonal_isPullback j j f).flip
  refine IsPullback.of_iso h (asIso (pullback.diagonal j)).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  all_goals simp only [Iso.symm_hom, asIso_inv, Iso.refl_hom, Category.comp_id,
    Category.id_comp]
  · rw [IsIso.eq_inv_comp]
    ext
    · rw [Category.assoc, pullback.lift_fst]
      simp
    · rw [Category.assoc, pullback.lift_snd]
      simp
  · rw [IsIso.eq_inv_comp]
    simp

/-- The open `W_U` of `U ×_S U`: the preimage of `W` under `U ×_S U ⟶ X ×_S X`. -/
abbrev restrictW : Scheme.{u} :=
  pullback D.ι (pullbackOpensMap j)

/-- The open immersion `W_U ⟶ W`. -/
abbrev restrictInclusion : D.restrictW j ⟶ D.W :=
  pullback.fst D.ι (pullbackOpensMap j)

/-- The factorization `Δ_U : U ⟶ W_U` of the relative diagonal of `f_U`. -/
def restrictDiag : Y ⟶ D.restrictW j :=
  pullback.lift (j ≫ D.diag) (pullback.diagonal (j ≫ f))
    (by rw [Category.assoc, D.fac, diagonal_comp_pullbackOpensMap])

omit [IsOpenImmersion j] in
/-- `Δ_U` followed by the inclusion `W_U ⟶ W` is `j` followed by `Δ`. -/
@[reassoc (attr := simp)]
theorem restrictDiag_restrictInclusion :
    D.restrictDiag j ≫ D.restrictInclusion j = j ≫ D.diag :=
  pullback.lift_fst _ _ _

omit [IsOpenImmersion j] in
/-- `Δ_U` followed by the inclusion `W_U ⟶ U ×_S U` is the relative diagonal of `f_U`. -/
@[reassoc (attr := simp)]
theorem restrictDiag_snd :
    D.restrictDiag j ≫ pullback.snd D.ι (pullbackOpensMap j) = pullback.diagonal (j ≫ f) :=
  pullback.lift_snd _ _ _

/-- **The square `Δ_U, U ⊆ X, W_U ⊆ W, Δ` is cartesian**, so `Δ_U` is the base change of `Δ`
along `W_U ⊆ W`. -/
theorem isPullback_restrictDiag :
    IsPullback (D.restrictDiag j) j (D.restrictInclusion j) D.diag := by
  have hc : IsPullback (D.restrictDiag j ≫ pullback.snd D.ι (pullbackOpensMap j)) j
      (pullbackOpensMap j) (D.diag ≫ D.ι) := by
    rw [restrictDiag_snd, D.fac]
    exact isPullback_diagonal_pullbackOpensMap j
  exact IsPullback.of_right hc (restrictDiag_restrictInclusion D j)
    (IsPullback.of_hasPullback D.ι (pullbackOpensMap j)).flip

/-- The inclusion `W_U ⟶ W` is an open immersion. -/
instance isOpenImmersion_restrictInclusion : IsOpenImmersion (D.restrictInclusion j) := by
  have := D.isOpenImmersion
  dsimp only [restrictInclusion]
  infer_instance

/-- The factorization `Δ_U : U ⟶ W_U` is a closed immersion. -/
instance isClosedImmersion_restrictDiag : IsClosedImmersion (D.restrictDiag j) := by
  have := D.isClosedImmersion
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (D.isPullback_restrictDiag j).flip ‹_›

/-- **The diagonal open of `f_U = j ≫ f`**: the preimage `W_U` of `W`
in `U ×_S U`, through which the relative diagonal of `f_U` factors as the closed immersion
`Δ_U`, a base change of `Δ`. -/
abbrev restrict : DiagonalOpen (j ≫ f) where
  W := D.restrictW j
  ι := pullback.snd _ _
  isOpenImmersion := by
    have := D.isOpenImmersion
    infer_instance
  diag := D.restrictDiag j
  isClosedImmersion := inferInstance
  fac := restrictDiag_snd D j

/-- The open of `D.restrict j` is `W_U`. -/
@[simp] theorem restrict_W : (D.restrict j).W = D.restrictW j := rfl

/-- The diagonal factorization of `D.restrict j` is `Δ_U`. -/
@[simp] theorem restrict_diag : (D.restrict j).diag = D.restrictDiag j := rfl

/-- The first projection of `W_U` is the first projection of `W` restricted to `W_U`, landing
in `U`. -/
@[reassoc]
theorem restrictInclusion_proj :
    D.restrictInclusion j ≫ D.proj = (D.restrict j).proj ≫ j := by
  simp only [proj, restrictInclusion, restrict, Category.assoc]
  rw [pullback.condition_assoc, pullbackOpensMap_fst]

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
