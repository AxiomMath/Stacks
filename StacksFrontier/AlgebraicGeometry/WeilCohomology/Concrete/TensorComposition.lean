module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorClopen
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RationalPointSummands
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorAssociativity

/-!
# The tensor product of correspondences is compatible with composition

For smooth projective schemes `X, X', Y, Y', Z, Z'` over a field `k` and correspondences
`a ∈ Corrʳ(X, Y)`, `a' ∈ Corr^{r'}(X', Y')`, `b ∈ Corrˢ(Y, Z)`, `b' ∈ Corr^{s'}(Y', Z')`,

  `(b ⊗ b') ∘ (a ⊗ a') = (b ∘ a) ⊗ (b' ∘ a')`,

which is the bifunctoriality of the tensor product used in Stacks 0FG7. In constant dimension this
is `Stacks.WeilCohomology.composition_tensorBlock`; this file assembles the case of mixed
dimension from it. The block of `a ⊗ a'` indexed by `X_d × X'_{d'}` and `Y_e × Y'_{e'}` lives on
the open and closed subscheme `(X_d × X'_{d'}) × (Y_e × Y'_{e'})` of
`(X × X')_{d+d'} × (Y × Y')_{e+e'}`; composition commutes with pushing forward along these open and
closed immersions, and vanishes when the middle pieces `Y_e × Y'_{e'}` and `Y_{e₁} × Y'_{e₁'}` are
different, hence disjoint (`Stacks.WeilCohomology.composition_prodHomPushforward` and
`Stacks.WeilCohomology.composition_prodHomPushforward_of_disjoint`).

## Main results

* `Stacks.WeilCohomology.comp_tensor`: `(b ⊗ b') ∘ (a ⊗ a') = (b ∘ a) ⊗ (b' ∘ a')`, up to the
  identification of degrees `(r + r') + (s + s') = (r + s) + (r' + s')`, for the canonical diagonal
  classes.

## References

* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k]

/-! ### Composition of blocks pushed into parts -/

section Blocks

variable {X Y Z A B B' C : Scheme.{u}}
  {sX : X ⟶ (fieldChowSituation k).S} {sY : Y ⟶ (fieldChowSituation k).S}
  {sZ : Z ⟶ (fieldChowSituation k).S} {sA : A ⟶ (fieldChowSituation k).S}
  {sB : B ⟶ (fieldChowSituation k).S} {sB' : B' ⟶ (fieldChowSituation k).S}
  {sC : C ⟶ (fieldChowSituation k).S}
  [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY] [IsProper sY] [Smooth sZ]
  [IsSeparated sZ] [Smooth sA] [IsSeparated sA] [Smooth sB] [IsSeparated sB] [IsProper sB]
  [Smooth sB'] [IsSeparated sB'] [Smooth sC] [IsSeparated sC]
  {D M M' F : ℕ}
  (iA : A ⟶ (dimPart sX D).toScheme) [IsOpenImmersion iA] [IsProper iA]
  (iB : B ⟶ (dimPart sY M).toScheme) [IsOpenImmersion iB] [IsProper iB]
  (iB' : B' ⟶ (dimPart sY M').toScheme) [IsOpenImmersion iB'] [IsProper iB']
  (iC : C ⟶ (dimPart sZ F).toScheme) [IsOpenImmersion iC] [IsProper iC]
  (hiA : iA ≫ partBase sX D = sA) (hiB : iB ≫ partBase sY M = sB)
  (hiB' : iB' ≫ partBase sY M' = sB') (hiC : iC ≫ partBase sZ F = sC)

/-- Composition of two blocks pushed forward from open and closed pieces of the parts, through
the same piece `B` of `Y_M`: the pushforward of the composite. -/
theorem comp_lof_prodHomPushforward (hA : RelativeDimension sA D) (hB : RelativeDimension sB M)
    (hC : RelativeDimension sC F) (r s : ℤ)
    (x : Correspondence (fieldChowSituation k) sA sB M r)
    (y : Correspondence (fieldChowSituation k) sB sC F s) :
    comp k sX sY sZ (canonicalDiagonalClassFamily k) r s
        (DirectSum.lof ℚ ℕ _ D (DirectSum.lof ℚ ℕ _ M
          (prodHomPushforward (partBase sX D) (partBase sY M) sA sB iA iB hiA hiB M r x)))
        (DirectSum.lof ℚ ℕ _ M (DirectSum.lof ℚ ℕ _ F
          (prodHomPushforward (partBase sY M) (partBase sZ F) sB sC iB iC hiB hiC F s y))) =
      (DirectSum.lof ℚ ℕ _ D (DirectSum.lof ℚ ℕ _ F
        (prodHomPushforward (partBase sX D) (partBase sZ F) sA sC iA iC hiA hiC F (r + s)
          (composition k sA sB sC (canonicalDiagonalClassFamily k) hA hB hC r s x y))) :
        Corr k sX sZ (r + s)) := by
  rw [comp_lof_lof_lof_lof, composition_prodHomPushforward_canonical iA iB iC hiA hiB hiC hA hB hC]

omit [IsProper sB] [IsSeparated sC] [IsOpenImmersion iC] in
/-- Composition of two blocks pushed forward from open and closed pieces `B ⊆ Y_M` and
`B' ⊆ Y_{M'}` with disjoint images in `Y` vanishes. -/
theorem comp_lof_prodHomPushforward_of_disjoint
    (hdisj : ∀ (p : B) (q : B'), (iB ≫ (dimPart sY M).ι) p ≠ (iB' ≫ (dimPart sY M').ι) q)
    (hA : RelativeDimension sA D) (hB : RelativeDimension sB M) (r s : ℤ)
    (x : Correspondence (fieldChowSituation k) sA sB M r)
    (y : Correspondence (fieldChowSituation k) sB' sC F s) :
    comp k sX sY sZ (canonicalDiagonalClassFamily k) r s
        (DirectSum.lof ℚ ℕ _ D (DirectSum.lof ℚ ℕ _ M
          (prodHomPushforward (partBase sX D) (partBase sY M) sA sB iA iB hiA hiB M r x)))
        (DirectSum.lof ℚ ℕ _ M' (DirectSum.lof ℚ ℕ _ F
          (prodHomPushforward (partBase sY M') (partBase sZ F) sB' sC iB' iC hiB' hiC F s y))) =
      0 := by
  by_cases hM : M = M'
  · subst hM
    rw [comp_lof_lof_lof_lof, composition_prodHomPushforward_of_disjoint_canonical iA iB iC hiA hiB
      hiC iB' hiB' ?_ hA hB (relativeDimension_partBase sX D) (relativeDimension_partBase sY M)
      (relativeDimension_partBase sZ F), map_zero, map_zero]
    rw [Set.disjoint_left]
    rintro _ ⟨p, rfl⟩ ⟨q, hq⟩
    exact hdisj p q (by simp only [Scheme.Hom.comp_apply]; rw [hq])
  · exact comp_lof_lof_lof_of_ne k sX sY sZ _ r s D M M' hM _ _

/-- The composite of two tensor blocks pushed into parts, through the same piece: the pushforward
of the tensor product of the composites. -/
theorem comp_lof_prodHomPushforward_tensorBlock {A A' B₁ B₁' C₁ C₁' : Scheme.{u}}
    {sA : A ⟶ (fieldChowSituation k).S} {sA' : A' ⟶ (fieldChowSituation k).S}
    {sB₁ : B₁ ⟶ (fieldChowSituation k).S} {sB₁' : B₁' ⟶ (fieldChowSituation k).S}
    {sC₁ : C₁ ⟶ (fieldChowSituation k).S} {sC₁' : C₁' ⟶ (fieldChowSituation k).S}
    [Smooth sA] [IsSeparated sA] [Smooth sA'] [IsSeparated sA'] [Smooth sB₁] [IsSeparated sB₁]
    [IsProper sB₁] [Smooth sB₁'] [IsSeparated sB₁'] [IsProper sB₁'] [Smooth sC₁]
    [IsSeparated sC₁] [Smooth sC₁'] [IsSeparated sC₁']
    {d d' e e' f f' : ℕ} (hA : RelativeDimension sA d) (hA' : RelativeDimension sA' d')
    (hB : RelativeDimension sB₁ e) (hB' : RelativeDimension sB₁' e')
    (hC : RelativeDimension sC₁ f) (hC' : RelativeDimension sC₁' f')
    (hP : RelativeDimension (prodBase sA sA') (d + d'))
    (hQ : RelativeDimension (prodBase sB₁ sB₁') (e + e'))
    (hR : RelativeDimension (prodBase sC₁ sC₁') (f + f'))
    (iA : Limits.pullback sA sA' ⟶ (dimPart sX (d + d')).toScheme) [IsOpenImmersion iA]
    [IsProper iA]
    (iB : Limits.pullback sB₁ sB₁' ⟶ (dimPart sY (e + e')).toScheme) [IsOpenImmersion iB]
    [IsProper iB]
    (iC : Limits.pullback sC₁ sC₁' ⟶ (dimPart sZ (f + f')).toScheme) [IsOpenImmersion iC]
    [IsProper iC]
    (hiA : iA ≫ partBase sX (d + d') = prodBase sA sA')
    (hiB : iB ≫ partBase sY (e + e') = prodBase sB₁ sB₁')
    (hiC : iC ≫ partBase sZ (f + f') = prodBase sC₁ sC₁') (r r' s s' : ℤ)
    (x : Correspondence (fieldChowSituation k) sA sB₁ e r)
    (x' : Correspondence (fieldChowSituation k) sA' sB₁' e' r')
    (y : Correspondence (fieldChowSituation k) sB₁ sC₁ f s)
    (y' : Correspondence (fieldChowSituation k) sB₁' sC₁' f' s') :
    comp k sX sY sZ (canonicalDiagonalClassFamily k) (r + r') (s + s')
        (DirectSum.lof ℚ ℕ _ (d + d') (DirectSum.lof ℚ ℕ _ (e + e')
          (prodHomPushforward (partBase sX (d + d')) (partBase sY (e + e')) _ _ iA iB hiA hiB
            ((e + e' : ℕ) : ℤ) (r + r')
            (tensorBlock k sA sA' sB₁ sB₁' (canonicalDiagonalClassFamily k) hA hA' hB hB' r r' x
              x'))))
        (DirectSum.lof ℚ ℕ _ (e + e') (DirectSum.lof ℚ ℕ _ (f + f')
          (prodHomPushforward (partBase sY (e + e')) (partBase sZ (f + f')) _ _ iB iC hiB hiC
            ((f + f' : ℕ) : ℤ) (s + s')
            (tensorBlock k sB₁ sB₁' sC₁ sC₁' (canonicalDiagonalClassFamily k) hB hB' hC hC' s s' y
              y')))) =
      (DirectSum.lof ℚ ℕ _ (d + d') (DirectSum.lof ℚ ℕ _ (f + f')
        (prodHomPushforward (partBase sX (d + d')) (partBase sZ (f + f')) _ _ iA iC hiA hiC
          ((f + f' : ℕ) : ℤ) (r + r' + (s + s'))
          (correspondenceCongr k (prodBase sA sA') (prodBase sC₁ sC₁') (by ring)
            (tensorBlock k sA sA' sC₁ sC₁' (canonicalDiagonalClassFamily k) hA hA' hC hC' (r + s)
              (r' + s') (composition k sA sB₁ sC₁ (canonicalDiagonalClassFamily k) hA hB hC r s x y)
              (composition k sA' sB₁' sC₁' (canonicalDiagonalClassFamily k) hA' hB' hC' r' s' x'
                y'))))) :
        Corr k sX sZ (r + r' + (s + s'))) := by
  rw [comp_lof_prodHomPushforward k iA iB iC hiA hiB hiC hP hQ hR,
    composition_tensorBlock_canonical k sA sA' sB₁ sB₁' sC₁ sC₁' hA hA' hB hB' hC hC' hP hQ hR]

end Blocks

/-! ### Bifunctoriality in mixed dimension -/

section Mixed

variable {X X' Y Y' Z Z' : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sX' : X' ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) (sY' : Y' ⟶ (fieldChowSituation k).S)
  (sZ : Z ⟶ (fieldChowSituation k).S) (sZ' : Z' ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] [Smooth sX'] [IsSeparated sX'] [Smooth sY] [IsSeparated sY]
  [Smooth sY'] [IsSeparated sY'] [Smooth sZ] [IsSeparated sZ] [Smooth sZ'] [IsSeparated sZ']
  [IsProper sX] [IsProper sX'] [IsProper sY] [IsProper sY'] [IsProper sZ] [IsProper sZ']

/-- The block inclusion of the tensor product is the pushforward along the product of the two
inclusions of products of parts. -/
theorem tensorBlockInclusion_eq_prodHomPushforward (d d' e e' : ℕ) (r : ℤ) :
    tensorBlockInclusion k sX sX' sY sY' d d' e e' r =
      prodHomPushforward (partBase (prodBase sX sX') (d + d')) (partBase (prodBase sY sY') (e + e'))
        (prodBase (partBase sX d) (partBase sX' d')) (prodBase (partBase sY e) (partBase sY' e'))
        (partProdHom k sX sX' d d') (partProdHom k sY sY' e e')
        (partProdHom_comp_partBase k sX sX' d d') (partProdHom_comp_partBase k sY sY' e e')
        ((e + e' : ℕ) : ℤ) r :=
  rfl

/-- Pushforward along open and closed immersions commutes with the identification of degrees. -/
theorem prodHomPushforward_correspondenceCongr {P Q P₀ Q₀ : Scheme.{u}}
    (sP : P ⟶ (fieldChowSituation k).S) (sQ : Q ⟶ (fieldChowSituation k).S)
    (sP₀ : P₀ ⟶ (fieldChowSituation k).S) (sQ₀ : Q₀ ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType sP] [LocallyOfFiniteType sQ] [LocallyOfFiniteType sP₀]
    [LocallyOfFiniteType sQ₀] (φP : P₀ ⟶ P) (φQ : Q₀ ⟶ Q) (hφP : φP ≫ sP = sP₀)
    (hφQ : φQ ≫ sQ = sQ₀) [IsProper (prodHom sP sQ sP₀ sQ₀ φP φQ hφP hφQ)] (e : ℤ) {r r' : ℤ}
    (h : r = r') (c : Correspondence (fieldChowSituation k) sP₀ sQ₀ e r) :
    prodHomPushforward sP sQ sP₀ sQ₀ φP φQ hφP hφQ e r' (correspondenceCongr k sP₀ sQ₀ h c) =
      correspondenceCongr k sP sQ h (prodHomPushforward sP sQ sP₀ sQ₀ φP φQ hφP hφQ e r c) := by
  subst h
  rw [correspondenceCongr_self, correspondenceCongr_self]

/-- Points of two pieces `W_e` and `W_{e₁}` with the same image in `W` have `e = e₁`. -/
private theorem dimPart_index_eq {W : Scheme.{u}} (t : W ⟶ (fieldChowSituation k).S) [Smooth t]
    {e e₁ : ℕ} (u : dimPart t e) (v : dimPart t e₁) (h : (dimPart t e).ι u = (dimPart t e₁).ι v) :
    e = e₁ :=
  (isClopenDecomposition_dimPart t).eq_of_mem (x := (dimPart t e).ι u) u.2 (by rw [h]; exact v.2)

omit [IsSeparated sY] [IsSeparated sY'] [IsProper sY] [IsProper sY'] in
/-- The product of two different pairs of parts are disjoint in the product. -/
theorem partProdHom_ne {e e' e₁ e₁' : ℕ} (h : ¬(e = e₁ ∧ e' = e₁'))
    (p : (Limits.pullback (partBase sY e) (partBase sY' e') : Scheme.{u}))
    (q : (Limits.pullback (partBase sY e₁) (partBase sY' e₁') : Scheme.{u})) :
    (partProdHom k sY sY' e e' ≫ (dimPart (prodBase sY sY') (e + e')).ι) p ≠
      (partProdHom k sY sY' e₁ e₁' ≫ (dimPart (prodBase sY sY') (e₁ + e₁')).ι) q := by
  intro hpq
  rw [partProdHom_ι, partProdHom_ι] at hpq
  refine h ⟨?_, ?_⟩
  · have := congrArg (Limits.pullback.fst sY sY').base hpq
    simp only [← Scheme.Hom.comp_apply, partProdMap_fst] at this
    simp only [Scheme.Hom.comp_apply] at this
    exact dimPart_index_eq k sY _ _ this
  · have := congrArg (Limits.pullback.snd sY sY').base hpq
    simp only [← Scheme.Hom.comp_apply, partProdMap_snd] at this
    simp only [Scheme.Hom.comp_apply] at this
    exact dimPart_index_eq k sY' _ _ this

/-- The tensor product on blocks, with the block inclusion written as a pushforward. -/
theorem tensor_lof_lof_eq_prodHomPushforward {P P' Q Q' : Scheme.{u}}
    (sP : P ⟶ (fieldChowSituation k).S) (sP' : P' ⟶ (fieldChowSituation k).S)
    (sQ : Q ⟶ (fieldChowSituation k).S) (sQ' : Q' ⟶ (fieldChowSituation k).S)
    [Smooth sP] [IsSeparated sP] [Smooth sP'] [IsSeparated sP'] [Smooth sQ] [IsSeparated sQ]
    [Smooth sQ'] [IsSeparated sQ'] [IsProper sP] [IsProper sP'] [IsProper sQ] [IsProper sQ']
    (r r' : ℤ) (d e d' e' : ℕ)
    (c : Correspondence (fieldChowSituation k) (partBase sP d) (partBase sQ e) e r)
    (c' : Correspondence (fieldChowSituation k) (partBase sP' d') (partBase sQ' e') e' r') :
    tensor k sP sP' sQ sQ' (canonicalDiagonalClassFamily k) r r'
        (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e c))
        (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' c')) =
      (DirectSum.lof ℚ ℕ _ (d + d') (DirectSum.lof ℚ ℕ _ (e + e')
        (prodHomPushforward (partBase (prodBase sP sP') (d + d'))
          (partBase (prodBase sQ sQ') (e + e')) _ _ (partProdHom k sP sP' d d')
          (partProdHom k sQ sQ' e e') (partProdHom_comp_partBase k sP sP' d d')
          (partProdHom_comp_partBase k sQ sQ' e e') ((e + e' : ℕ) : ℤ) (r + r')
          (tensorBlock k (partBase sP d) (partBase sP' d') (partBase sQ e) (partBase sQ' e')
              (canonicalDiagonalClassFamily k)
          (relativeDimension_partBase sP d) (relativeDimension_partBase sP' d')
          (relativeDimension_partBase sQ e) (relativeDimension_partBase sQ' e') r r' c c'))) :
        Corr k (prodBase sP sP') (prodBase sQ sQ') (r + r')) :=
  tensor_lof_lof k sP sP' sQ sQ' _ r r' d e d' e' c c'

/-- The left side of bifunctoriality on blocks with matching middle indices. -/
theorem comp_tensor_lof_same_left (r r' s s' : ℤ) (d e d' e' f f' : ℕ)
    (x : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    (x' : Correspondence (fieldChowSituation k) (partBase sX' d') (partBase sY' e') e' r')
    (y : Correspondence (fieldChowSituation k) (partBase sY e) (partBase sZ f) f s)
    (y' : Correspondence (fieldChowSituation k) (partBase sY' e') (partBase sZ' f') f' s') :
    comp k (prodBase sX sX') (prodBase sY sY') (prodBase sZ sZ') (canonicalDiagonalClassFamily k)
        (r + r') (s + s')
        (tensor k sX sX' sY sY' (canonicalDiagonalClassFamily k) r r'
          (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
          (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' x')))
        (tensor k sY sY' sZ sZ' (canonicalDiagonalClassFamily k) s s'
          (DirectSum.lof ℚ ℕ _ e (DirectSum.lof ℚ ℕ _ f y))
          (DirectSum.lof ℚ ℕ _ e' (DirectSum.lof ℚ ℕ _ f' y'))) =
      (DirectSum.lof ℚ ℕ _ (d + d') (DirectSum.lof ℚ ℕ _ (f + f')
        (prodHomPushforward (partBase (prodBase sX sX') (d + d'))
          (partBase (prodBase sZ sZ') (f + f')) _ _ (partProdHom k sX sX' d d')
          (partProdHom k sZ sZ' f f') (partProdHom_comp_partBase k sX sX' d d')
          (partProdHom_comp_partBase k sZ sZ' f f') ((f + f' : ℕ) : ℤ) (r + r' + (s + s'))
          (correspondenceCongr k (prodBase (partBase sX d) (partBase sX' d'))
            (prodBase (partBase sZ f) (partBase sZ' f')) (by ring)
            (tensorBlock k (partBase sX d) (partBase sX' d') (partBase sZ f) (partBase sZ' f')
                (canonicalDiagonalClassFamily k)
          (relativeDimension_partBase sX d) (relativeDimension_partBase sX' d')
          (relativeDimension_partBase sZ f) (relativeDimension_partBase sZ' f') (r + s) (r' + s')
              (composition k (partBase sX d) (partBase sY e) (partBase sZ f)
                  (canonicalDiagonalClassFamily k)
              (relativeDimension_partBase sX d) (relativeDimension_partBase sY e)
              (relativeDimension_partBase sZ f) r s x y) (composition k (partBase sX' d')
                  (partBase sY' e') (partBase sZ' f') (canonicalDiagonalClassFamily k)
              (relativeDimension_partBase sX' d') (relativeDimension_partBase sY' e')
              (relativeDimension_partBase sZ' f') r' s' x' y'))))) :
        Corr k (prodBase sX sX') (prodBase sZ sZ') (r + r' + (s + s'))) := by
  have g := comp_lof_prodHomPushforward_tensorBlock k (relativeDimension_partBase sX d)
    (relativeDimension_partBase sX' d') (relativeDimension_partBase sY e)
    (relativeDimension_partBase sY' e') (relativeDimension_partBase sZ f)
    (relativeDimension_partBase sZ' f')
    (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sX d)
      (relativeDimension_partBase sX' d'))
    (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sY e)
      (relativeDimension_partBase sY' e'))
    (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sZ f)
      (relativeDimension_partBase sZ' f')) (partProdHom k sX sX' d d') (partProdHom k sY sY' e e')
    (partProdHom k sZ sZ' f f') (partProdHom_comp_partBase k sX sX' d d')
    (partProdHom_comp_partBase k sY sY' e e') (partProdHom_comp_partBase k sZ sZ' f f') r r' s s'
    x x' y y'
  simp only [tensor_lof_lof_eq_prodHomPushforward]
  convert g using 4

omit [IsSeparated sY] [IsSeparated sY'] in
/-- The right side of bifunctoriality on blocks with matching middle indices. -/
theorem comp_tensor_lof_same_right (r r' s s' : ℤ) (d e d' e' f f' : ℕ)
    (x : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    (x' : Correspondence (fieldChowSituation k) (partBase sX' d') (partBase sY' e') e' r')
    (y : Correspondence (fieldChowSituation k) (partBase sY e) (partBase sZ f) f s)
    (y' : Correspondence (fieldChowSituation k) (partBase sY' e') (partBase sZ' f') f' s') :
    corrCongr k (prodBase sX sX') (prodBase sZ sZ') (by ring)
        (tensor k sX sX' sZ sZ' (canonicalDiagonalClassFamily k) (r + s) (r' + s')
          (comp k sX sY sZ (canonicalDiagonalClassFamily k) r s
            (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
            (DirectSum.lof ℚ ℕ _ e (DirectSum.lof ℚ ℕ _ f y)))
          (comp k sX' sY' sZ' (canonicalDiagonalClassFamily k) r' s'
            (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' x'))
            (DirectSum.lof ℚ ℕ _ e' (DirectSum.lof ℚ ℕ _ f' y')))) =
      (DirectSum.lof ℚ ℕ _ (d + d') (DirectSum.lof ℚ ℕ _ (f + f')
        (prodHomPushforward (partBase (prodBase sX sX') (d + d'))
          (partBase (prodBase sZ sZ') (f + f')) _ _ (partProdHom k sX sX' d d')
          (partProdHom k sZ sZ' f f') (partProdHom_comp_partBase k sX sX' d d')
          (partProdHom_comp_partBase k sZ sZ' f f') ((f + f' : ℕ) : ℤ) (r + r' + (s + s'))
          (correspondenceCongr k (prodBase (partBase sX d) (partBase sX' d'))
            (prodBase (partBase sZ f) (partBase sZ' f')) (by ring)
            (tensorBlock k (partBase sX d) (partBase sX' d') (partBase sZ f) (partBase sZ' f')
                (canonicalDiagonalClassFamily k)
          (relativeDimension_partBase sX d) (relativeDimension_partBase sX' d')
          (relativeDimension_partBase sZ f) (relativeDimension_partBase sZ' f') (r + s) (r' + s')
              (composition k (partBase sX d) (partBase sY e) (partBase sZ f)
                  (canonicalDiagonalClassFamily k)
              (relativeDimension_partBase sX d) (relativeDimension_partBase sY e)
              (relativeDimension_partBase sZ f) r s x y) (composition k (partBase sX' d')
                  (partBase sY' e') (partBase sZ' f') (canonicalDiagonalClassFamily k)
              (relativeDimension_partBase sX' d') (relativeDimension_partBase sY' e')
              (relativeDimension_partBase sZ' f') r' s' x' y'))))) :
        Corr k (prodBase sX sX') (prodBase sZ sZ') (r + r' + (s + s'))) := by
  simp only [comp_lof_lof_lof_lof k sX sY sZ _ r s d e f x y,
    comp_lof_lof_lof_lof k sX' sY' sZ' _ r' s' d' e' f' x' y', tensor_lof_lof_eq_prodHomPushforward,
    corrCongr_lof_lof, prodHomPushforward_correspondenceCongr]

/-- Bifunctoriality on blocks with matching middle indices. -/
theorem comp_tensor_lof_same (r r' s s' : ℤ) (d e d' e' f f' : ℕ)
    (x : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    (x' : Correspondence (fieldChowSituation k) (partBase sX' d') (partBase sY' e') e' r')
    (y : Correspondence (fieldChowSituation k) (partBase sY e) (partBase sZ f) f s)
    (y' : Correspondence (fieldChowSituation k) (partBase sY' e') (partBase sZ' f') f' s') :
    comp k (prodBase sX sX') (prodBase sY sY') (prodBase sZ sZ') (canonicalDiagonalClassFamily k)
        (r + r') (s + s')
        (tensor k sX sX' sY sY' (canonicalDiagonalClassFamily k) r r'
          (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
          (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' x')))
        (tensor k sY sY' sZ sZ' (canonicalDiagonalClassFamily k) s s'
          (DirectSum.lof ℚ ℕ _ e (DirectSum.lof ℚ ℕ _ f y))
          (DirectSum.lof ℚ ℕ _ e' (DirectSum.lof ℚ ℕ _ f' y'))) =
      corrCongr k (prodBase sX sX') (prodBase sZ sZ') (by ring)
        (tensor k sX sX' sZ sZ' (canonicalDiagonalClassFamily k) (r + s) (r' + s')
          (comp k sX sY sZ (canonicalDiagonalClassFamily k) r s
            (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
            (DirectSum.lof ℚ ℕ _ e (DirectSum.lof ℚ ℕ _ f y)))
          (comp k sX' sY' sZ' (canonicalDiagonalClassFamily k) r' s'
            (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' x'))
            (DirectSum.lof ℚ ℕ _ e' (DirectSum.lof ℚ ℕ _ f' y')))) :=
  (comp_tensor_lof_same_left k sX sX' sY sY' sZ sZ' r r' s s' d e d' e' f f' x x' y y').trans
    (comp_tensor_lof_same_right k sX sX' sY sY' sZ sZ' r r' s s' d e d' e' f f' x x' y y').symm

/-- The left side of bifunctoriality vanishes on blocks with different middle indices. -/
theorem comp_tensor_lof_ne_left (r r' s s' : ℤ) (d e d' e' e₁ f e₁' f' : ℕ)
    (he : ¬(e = e₁ ∧ e' = e₁'))
    (x : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    (x' : Correspondence (fieldChowSituation k) (partBase sX' d') (partBase sY' e') e' r')
    (y : Correspondence (fieldChowSituation k) (partBase sY e₁) (partBase sZ f) f s)
    (y' : Correspondence (fieldChowSituation k) (partBase sY' e₁') (partBase sZ' f') f' s') :
    comp k (prodBase sX sX') (prodBase sY sY') (prodBase sZ sZ') (canonicalDiagonalClassFamily k)
        (r + r') (s + s')
        (tensor k sX sX' sY sY' (canonicalDiagonalClassFamily k) r r'
          (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
          (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' x')))
        (tensor k sY sY' sZ sZ' (canonicalDiagonalClassFamily k) s s'
          (DirectSum.lof ℚ ℕ _ e₁ (DirectSum.lof ℚ ℕ _ f y))
          (DirectSum.lof ℚ ℕ _ e₁' (DirectSum.lof ℚ ℕ _ f' y'))) = 0 := by
  have g := comp_lof_prodHomPushforward_of_disjoint k (partProdHom k sX sX' d d')
    (partProdHom k sY sY' e e') (partProdHom k sY sY' e₁ e₁') (partProdHom k sZ sZ' f f')
    (partProdHom_comp_partBase k sX sX' d d') (partProdHom_comp_partBase k sY sY' e e')
    (partProdHom_comp_partBase k sY sY' e₁ e₁') (partProdHom_comp_partBase k sZ sZ' f f')
    (partProdHom_ne k sY sY' he)
    (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sX d)
      (relativeDimension_partBase sX' d'))
    (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sY e)
      (relativeDimension_partBase sY' e')) (r + r') (s + s')
      (tensorBlock k (partBase sX d) (partBase sX' d') (partBase sY e) (partBase sY' e')
        (canonicalDiagonalClassFamily k) (relativeDimension_partBase sX d)
        (relativeDimension_partBase sX' d') (relativeDimension_partBase sY e)
        (relativeDimension_partBase sY' e') r r' x x')
      (tensorBlock k (partBase sY e₁) (partBase sY' e₁') (partBase sZ f) (partBase sZ' f')
        (canonicalDiagonalClassFamily k) (relativeDimension_partBase sY e₁)
        (relativeDimension_partBase sY' e₁') (relativeDimension_partBase sZ f)
        (relativeDimension_partBase sZ' f') s s' y y')
  simp only [tensor_lof_lof_eq_prodHomPushforward]
  convert g using 4

omit [IsSeparated sY] [IsSeparated sY'] in
/-- The right side of bifunctoriality vanishes on blocks with different middle indices. -/
theorem comp_tensor_lof_ne_right (r r' s s' : ℤ) (d e d' e' e₁ f e₁' f' : ℕ)
    (he : ¬(e = e₁ ∧ e' = e₁'))
    (x : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    (x' : Correspondence (fieldChowSituation k) (partBase sX' d') (partBase sY' e') e' r')
    (y : Correspondence (fieldChowSituation k) (partBase sY e₁) (partBase sZ f) f s)
    (y' : Correspondence (fieldChowSituation k) (partBase sY' e₁') (partBase sZ' f') f' s') :
    corrCongr k (prodBase sX sX') (prodBase sZ sZ')
        (show r + s + (r' + s') = r + r' + (s + s') by ring)
        (tensor k sX sX' sZ sZ' (canonicalDiagonalClassFamily k) (r + s) (r' + s')
          (comp k sX sY sZ (canonicalDiagonalClassFamily k) r s
            (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
            (DirectSum.lof ℚ ℕ _ e₁ (DirectSum.lof ℚ ℕ _ f y)))
          (comp k sX' sY' sZ' (canonicalDiagonalClassFamily k) r' s'
            (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' x'))
            (DirectSum.lof ℚ ℕ _ e₁' (DirectSum.lof ℚ ℕ _ f' y')))) = 0 := by
  rcases not_and_or.1 he with h | h
  · simp only [comp_lof_lof_lof_of_ne k sX sY sZ _ r s d e e₁ h, LinearMap.map_zero,
      LinearMap.zero_apply, LinearEquiv.map_zero]
  · simp only [comp_lof_lof_lof_of_ne k sX' sY' sZ' _ r' s' d' e' e₁' h, LinearMap.map_zero,
      LinearEquiv.map_zero]

/-- Bifunctoriality on blocks. -/
theorem comp_tensor_lof (r r' s s' : ℤ) (d e d' e' e₁ f e₁' f' : ℕ)
    (x : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    (x' : Correspondence (fieldChowSituation k) (partBase sX' d') (partBase sY' e') e' r')
    (y : Correspondence (fieldChowSituation k) (partBase sY e₁) (partBase sZ f) f s)
    (y' : Correspondence (fieldChowSituation k) (partBase sY' e₁') (partBase sZ' f') f' s') :
    comp k (prodBase sX sX') (prodBase sY sY') (prodBase sZ sZ') (canonicalDiagonalClassFamily k)
        (r + r') (s + s')
        (tensor k sX sX' sY sY' (canonicalDiagonalClassFamily k) r r'
          (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
          (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' x')))
        (tensor k sY sY' sZ sZ' (canonicalDiagonalClassFamily k) s s'
          (DirectSum.lof ℚ ℕ _ e₁ (DirectSum.lof ℚ ℕ _ f y))
          (DirectSum.lof ℚ ℕ _ e₁' (DirectSum.lof ℚ ℕ _ f' y'))) =
      corrCongr k (prodBase sX sX') (prodBase sZ sZ') (by ring)
        (tensor k sX sX' sZ sZ' (canonicalDiagonalClassFamily k) (r + s) (r' + s')
          (comp k sX sY sZ (canonicalDiagonalClassFamily k) r s
            (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
            (DirectSum.lof ℚ ℕ _ e₁ (DirectSum.lof ℚ ℕ _ f y)))
          (comp k sX' sY' sZ' (canonicalDiagonalClassFamily k) r' s'
            (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' x'))
            (DirectSum.lof ℚ ℕ _ e₁' (DirectSum.lof ℚ ℕ _ f' y')))) := by
  by_cases he : e = e₁ ∧ e' = e₁'
  · obtain ⟨rfl, rfl⟩ := he
    exact comp_tensor_lof_same k sX sX' sY sY' sZ sZ' r r' s s' d e d' e' f f' x x' y y'
  · exact (comp_tensor_lof_ne_left k sX sX' sY sY' sZ sZ' r r' s s' d e d' e' e₁ f e₁' f' he x x'
      y y').trans
      (comp_tensor_lof_ne_right k sX sX' sY sY' sZ sZ' r r' s s' d e d' e' e₁ f e₁' f' he x x' y
        y').symm

/-- Bifunctoriality with three of the four correspondences pure blocks. -/
theorem comp_tensor_lof₃ (r r' s s' : ℤ) (d e : ℕ) (x : Correspondence (fieldChowSituation k)
    (partBase sX d) (partBase sY e) e r) (d' e' : ℕ) (x' : Correspondence (fieldChowSituation k)
        (partBase sX' d') (partBase sY' e') e' r') (e₁ f : ℕ) (y : Correspondence
            (fieldChowSituation k) (partBase sY e₁) (partBase sZ f) f s) (b' : Corr k sY' sZ' s') :
    comp k (prodBase sX sX') (prodBase sY sY') (prodBase sZ sZ') (canonicalDiagonalClassFamily k)
        (r + r') (s + s') (tensor k sX sX' sY sY' (canonicalDiagonalClassFamily k) r r'
            (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x)) (DirectSum.lof ℚ ℕ _ d'
                (DirectSum.lof ℚ ℕ _ e' x')))
        (tensor k sY sY' sZ sZ' (canonicalDiagonalClassFamily k) s s' (DirectSum.lof ℚ ℕ _ e₁
            (DirectSum.lof ℚ ℕ _ f y)) b') =
      corrCongr k (prodBase sX sX') (prodBase sZ sZ') (by ring)
        (tensor k sX sX' sZ sZ' (canonicalDiagonalClassFamily k) (r + s) (r' + s')
          (comp k sX sY sZ (canonicalDiagonalClassFamily k) r s (DirectSum.lof ℚ ℕ _ d
              (DirectSum.lof ℚ ℕ _ e x)) (DirectSum.lof ℚ ℕ _ e₁ (DirectSum.lof ℚ ℕ _ f y)))
          (comp k sX' sY' sZ' (canonicalDiagonalClassFamily k) r' s' (DirectSum.lof ℚ ℕ _ d'
              (DirectSum.lof ℚ ℕ _ e' x')) b')) := by
  induction b' using Corr.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero]
  | add a₁ a₂ h₁ h₂ =>
    simp only [LinearMap.map_add, LinearEquiv.map_add, h₁, h₂]
  | lof e₁' f' y' =>
    exact comp_tensor_lof k sX sX' sY sY' sZ sZ' r r' s s' d e d' e' e₁ f e₁' f' x x' y y'

/-- Bifunctoriality with two of the four correspondences pure blocks. -/
theorem comp_tensor_lof₂ (r r' s s' : ℤ) (d e : ℕ) (x : Correspondence (fieldChowSituation k)
    (partBase sX d) (partBase sY e) e r) (d' e' : ℕ) (x' : Correspondence (fieldChowSituation k)
        (partBase sX' d') (partBase sY' e') e' r') (b : Corr k sY sZ s) (b' : Corr k sY' sZ' s') :
    comp k (prodBase sX sX') (prodBase sY sY') (prodBase sZ sZ') (canonicalDiagonalClassFamily k)
        (r + r') (s + s') (tensor k sX sX' sY sY' (canonicalDiagonalClassFamily k) r r'
            (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x)) (DirectSum.lof ℚ ℕ _ d'
                (DirectSum.lof ℚ ℕ _ e' x')))
        (tensor k sY sY' sZ sZ' (canonicalDiagonalClassFamily k) s s' b b') =
      corrCongr k (prodBase sX sX') (prodBase sZ sZ') (by ring)
        (tensor k sX sX' sZ sZ' (canonicalDiagonalClassFamily k) (r + s) (r' + s')
          (comp k sX sY sZ (canonicalDiagonalClassFamily k) r s (DirectSum.lof ℚ ℕ _ d
              (DirectSum.lof ℚ ℕ _ e x)) b)
          (comp k sX' sY' sZ' (canonicalDiagonalClassFamily k) r' s' (DirectSum.lof ℚ ℕ _ d'
              (DirectSum.lof ℚ ℕ _ e' x')) b')) := by
  induction b using Corr.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearMap.zero_apply, LinearEquiv.map_zero]
  | add a₁ a₂ h₁ h₂ =>
    simp only [LinearMap.map_add, LinearMap.add_apply, LinearEquiv.map_add, h₁, h₂]
  | lof e₁ f y =>
    exact comp_tensor_lof₃ k sX sX' sY sY' sZ sZ' r r' s s' d e x d' e' x' e₁ f y b'

/-- Bifunctoriality with one of the four correspondences a pure block. -/
theorem comp_tensor_lof₁ (r r' s s' : ℤ) (d e : ℕ) (x : Correspondence (fieldChowSituation k)
    (partBase sX d) (partBase sY e) e r) (a' : Corr k sX' sY' r') (b : Corr k sY sZ s) (b' : Corr
        k sY' sZ' s') :
    comp k (prodBase sX sX') (prodBase sY sY') (prodBase sZ sZ') (canonicalDiagonalClassFamily k)
        (r + r') (s + s') (tensor k sX sX' sY sY' (canonicalDiagonalClassFamily k) r r'
            (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x)) a')
        (tensor k sY sY' sZ sZ' (canonicalDiagonalClassFamily k) s s' b b') =
      corrCongr k (prodBase sX sX') (prodBase sZ sZ') (by ring)
        (tensor k sX sX' sZ sZ' (canonicalDiagonalClassFamily k) (r + s) (r' + s')
          (comp k sX sY sZ (canonicalDiagonalClassFamily k) r s (DirectSum.lof ℚ ℕ _ d
              (DirectSum.lof ℚ ℕ _ e x)) b)
          (comp k sX' sY' sZ' (canonicalDiagonalClassFamily k) r' s' a' b')) := by
  induction a' using Corr.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearMap.zero_apply, LinearEquiv.map_zero]
  | add a₁ a₂ h₁ h₂ =>
    simp only [LinearMap.map_add, LinearMap.add_apply, LinearEquiv.map_add, h₁, h₂]
  | lof d' e' x' =>
    exact comp_tensor_lof₂ k sX sX' sY sY' sZ sZ' r r' s s' d e x d' e' x' b b'

/-- **The tensor product of correspondences is compatible with composition** (Stacks 0FG7):
for smooth projective `X, X', Y, Y', Z, Z'` over `k` and correspondences `a ∈ Corrʳ(X, Y)`,
`a' ∈ Corr^{r'}(X', Y')`, `b ∈ Corrˢ(Y, Z)`, `b' ∈ Corr^{s'}(Y', Z')`,

  `(b ⊗ b') ∘ (a ⊗ a') = (b ∘ a) ⊗ (b' ∘ a')`,

compared through the identification of degrees `(r + s) + (r' + s') = (r + r') + (s + s')`, for the
canonical diagonal classes. -/
theorem comp_tensor (r r' s s' : ℤ) (a : Corr k sX sY r) (a' : Corr k sX' sY' r') (b : Corr k sY
    sZ s) (b' : Corr k sY' sZ' s') :
    comp k (prodBase sX sX') (prodBase sY sY') (prodBase sZ sZ') (canonicalDiagonalClassFamily k)
        (r + r') (s + s') (tensor k sX sX' sY sY' (canonicalDiagonalClassFamily k) r r' a a')
        (tensor k sY sY' sZ sZ' (canonicalDiagonalClassFamily k) s s' b b') =
      corrCongr k (prodBase sX sX') (prodBase sZ sZ') (by ring)
        (tensor k sX sX' sZ sZ' (canonicalDiagonalClassFamily k) (r + s) (r' + s')
          (comp k sX sY sZ (canonicalDiagonalClassFamily k) r s a b)
          (comp k sX' sY' sZ' (canonicalDiagonalClassFamily k) r' s' a' b')) := by
  induction a using Corr.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearMap.zero_apply, LinearEquiv.map_zero]
  | add a₁ a₂ h₁ h₂ =>
    simp only [LinearMap.map_add, LinearMap.add_apply, LinearEquiv.map_add, h₁, h₂]
  | lof d e x =>
    exact comp_tensor_lof₁ k sX sX' sY sY' sZ sZ' r r' s s' d e x a' b b'

end Mixed

end Stacks.WeilCohomology

end
