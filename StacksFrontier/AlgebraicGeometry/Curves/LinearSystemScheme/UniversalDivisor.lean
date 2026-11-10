module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.AbelFibre
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.CoordinateDivisor
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.IdealGlue
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.ProjectiveCoordinates
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertPointAddition
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealGeometricStalk

/-!
# The universal divisor over `Proj k[T₀, …, Tₙ]`

Let `X` be a smooth projective curve over an algebraically closed field `k`, `L` an invertible
`𝒪_X`-module and `w₀, …, wₙ` a basis of `Γ(X, L)`. On `X ×_k Q`, `Q = Proj k[T₀, …, Tₙ]`, there is
a closed subscheme `𝒟` cut out over the chart `X ×_k D₊(Tⱼ)` by `Σᵢ (Tᵢ / Tⱼ) · wᵢ`; the charts
agree on overlaps because the coordinate sections of two charts differ by the unit `Tⱼ / Tₗ`. Its
pullback along `X ×_k T ⟶ X ×_k Q` for a morphism `[c₀ : … : cₙ] : T ⟶ Q` is the zero scheme of
`Σᵢ cᵢ · wᵢ`.

## Main definitions

* `Stacks.LinearSystemScheme.chartMap`: the open immersion `X ×_k D₊(Tⱼ) ⟶ X ×_k Q`.
* `Stacks.LinearSystemScheme.universalDivisor`: `𝒟`.

## Main results

* `Stacks.LinearSystemScheme.comap_chartMap_universalDivisor`: `𝒟` restricted to the chart
  `X ×_k D₊(Tⱼ)` is the divisor of the coordinate section `Σᵢ (Tᵢ / Tⱼ) · wᵢ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite HomogeneousLocalization
open AlgebraicGeometry.Proj Stacks.AlgebraicGeometry.SectionsBaseChange Stacks.Hilbert

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.LinearSystemScheme

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] {n : ℕ}
  (w : letI := baseModule f L ⊤; Module.Basis (Fin (n + 1)) Γ(Spec (.of k), ⊤) Γ(L, ⊤))

/-- `Proj k[T₀, …, Tₙ]` as a `k`-scheme. -/
abbrev projOver : Over (Spec (.of k)) := Over.mk (projToSpec k n)

/-- The standard chart `Spec A_{(Tⱼ)}` of `Proj k[T₀, …, Tₙ]`, as a `k`-scheme. -/
abbrev chartOver (j : Fin (n + 1)) : Over (Spec (.of k)) :=
  Over.mk (awayι (coordGrading k n) (MvPolynomial.X j) (X_mem_coordGrading j) one_pos ≫
    projToSpec k n)

/-- The standard chart as a morphism of `k`-schemes. -/
abbrev chartHom (j : Fin (n + 1)) : chartOver k (n := n) j ⟶ projOver k (n := n) :=
  Over.homMk (awayι (coordGrading k n) (MvPolynomial.X j) (X_mem_coordGrading j) one_pos)

/-- The open immersion `X ×_k D₊(Tⱼ) ⟶ X ×_k Q`. -/
abbrev chartMap (j : Fin (n + 1)) :
    ((Over.pullback (chartOver k j).hom).obj (curveOver f)).left ⟶
      ((Over.pullback (projOver k (n := n)).hom).obj (curveOver f)).left :=
  familyBaseChangeMap (curveOver f) (chartHom k j)

/-- The square with sides `chartMap k f j`, the two second projections, and the chart inclusion
`D₊(Tⱼ) ⟶ Q` is a pullback. -/
theorem isPullback_chartMap (j : Fin (n + 1)) :
    IsPullback (chartMap k f (n := n) j) (pullback.snd f (chartOver k j).hom)
      (pullback.snd f (projOver k (n := n)).hom)
      (awayι (coordGrading k n) (MvPolynomial.X j) (X_mem_coordGrading j) one_pos) := by
  refine IsPullback.of_right ?_ (familyBaseChangeMap_comp_snd _ _) (IsPullback.of_hasPullback _ _)
  rw [familyBaseChangeMap_comp_fst]
  exact IsPullback.of_hasPullback _ _

/-- The map `X ×_k D₊(Tⱼ) ⟶ X ×_k Q` is an open immersion. -/
instance (j : Fin (n + 1)) : IsOpenImmersion (chartMap k f (n := n) j) :=
  MorphismProperty.of_isPullback (isPullback_chartMap k f j).flip inferInstance

/-- The inclusion of the standard chart `D₊(Tⱼ) ⟶ Proj k[T₀, …, Tₙ]` is quasi-compact. -/
instance (j : Fin (n + 1)) :
    QuasiCompact (awayι (coordGrading k n) (MvPolynomial.X j) (X_mem_coordGrading j) one_pos) :=
  inferInstance

/-- The map `X ×_k D₊(Tⱼ) ⟶ X ×_k Q` is quasi-compact. -/
instance (j : Fin (n + 1)) : QuasiCompact (chartMap k f (n := n) j) :=
  MorphismProperty.of_isPullback (isPullback_chartMap k f j).flip inferInstance

/-- The coordinates `Tᵢ / Tⱼ` on the chart `D₊(Tⱼ)`, as global functions. -/
def chartFun (j : Fin (n + 1)) : Fin (n + 1) → Γ((chartOver k (n := n) j).left, ⊤) :=
  fun i => (Scheme.ΓSpecIso _).inv (chartElem k n j i)

/-- On the chart `D₊(Tⱼ)` the coordinate `Tⱼ / Tⱼ` is `1`. -/
theorem chartFun_self (j : Fin (n + 1)) : chartFun k (n := n) j j = 1 := by
  simp [chartFun, chartElem_self]

/-- The coordinates `Tᵢ / Tⱼ` generate the unit ideal of the global functions on `D₊(Tⱼ)`. -/
theorem span_range_chartFun (j : Fin (n + 1)) :
    Ideal.span (Set.range (chartFun k (n := n) j)) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨j, rfl⟩)
    (by rw [chartFun_self]; exact isUnit_one)

/-- **The standard chart is `[T₀/Tⱼ : … : Tₙ/Tⱼ]`.** -/
theorem awayι_eq_coordMor (j : Fin (n + 1)) :
    awayι (coordGrading k n) (MvPolynomial.X j) (X_mem_coordGrading j) one_pos =
      coordMor (chartOver k j).hom (chartFun k j) (span_range_chartFun k j) := by
  have hg := awayι_preimage_basicOpen_self (𝒜 := coordGrading k n) one_pos
    (X_mem_coordGrading (k := k) j)
  rw [eq_coordMor_chartCoords (chartOver k j).hom _ rfl j hg]
  congr 1
  funext i
  simp only [chartCoords, awayToSection_comp_awayι_appLE one_pos (X_mem_coordGrading j)]
  rfl

/-- If two structure morphisms `h h' : T ⟶ Spec k` are equal, then
`coordMor h c hc = coordMor h' c hc`. -/
theorem coordMor_congr_struct {T : Scheme.{u}} {h h' : T ⟶ Spec (.of k)} (e : h = h')
    (c : Fin (n + 1) → Γ(T, ⊤)) (hc : Ideal.span (Set.range c) = ⊤) :
    coordMor h c hc = coordMor h' c hc := by
  subst e; rfl

/-- The divisor of the coordinate section `Σᵢ (Tᵢ / Tⱼ) · wᵢ` on `X ×_k D₊(Tⱼ)`. -/
def pieceDivisor (j : Fin (n + 1)) :
    ((Over.pullback (chartOver k (n := n) j).hom).obj (curveOver f)).left.IdealSheafData :=
  coordDivisor k f L w (chartOver k j).hom (chartFun k j)

/-- **The chart divisors agree on overlaps.** -/
theorem pieceDivisor_compat (i l : Fin (n + 1)) :
    (pieceDivisor k f L w i).comap (pullback.fst (chartMap k f i) (chartMap k f l)) =
      (pieceDivisor k f L w l).comap (pullback.snd (chartMap k f i) (chartMap k f l)) := by
  set W := pullback (chartMap k f (n := n) i) (chartMap k f l)
  set a : W ⟶ (chartOver k (n := n) i).left :=
    pullback.fst (chartMap k f i) (chartMap k f l) ≫ pullback.snd f (chartOver k i).hom
  set b : W ⟶ (chartOver k (n := n) l).left :=
    pullback.snd (chartMap k f i) (chartMap k f l) ≫ pullback.snd f (chartOver k l).hom
  set Pl : W ⟶ X := pullback.snd (chartMap k f i) (chartMap k f l) ≫
    pullback.fst f (chartOver k l).hom
  have hP : pullback.fst (chartMap k f i) (chartMap k f l) ≫ pullback.fst f (chartOver k i).hom =
      Pl := by
    have e1 : chartMap k f i ≫ pullback.fst f (projOver k (n := n)).hom =
        pullback.fst f (chartOver k i).hom := familyBaseChangeMap_comp_fst _ _
    have e2 : chartMap k f l ≫ pullback.fst f (projOver k (n := n)).hom =
        pullback.fst f (chartOver k l).hom := familyBaseChangeMap_comp_fst _ _
    simp only [Pl]
    rw [← e1, ← e2, ← Category.assoc, ← Category.assoc, pullback.condition]
  have hab : a ≫ awayι (coordGrading k n) (MvPolynomial.X i) (X_mem_coordGrading i) one_pos =
      b ≫ awayι (coordGrading k n) (MvPolynomial.X l) (X_mem_coordGrading l) one_pos := by
    have e1 : chartMap k f i ≫ pullback.snd f (projOver k (n := n)).hom =
        pullback.snd f (chartOver k i).hom ≫
          awayι (coordGrading k n) (MvPolynomial.X i) (X_mem_coordGrading i) one_pos :=
      familyBaseChangeMap_comp_snd _ _
    have e2 : chartMap k f l ≫ pullback.snd f (projOver k (n := n)).hom =
        pullback.snd f (chartOver k l).hom ≫
          awayι (coordGrading k n) (MvPolynomial.X l) (X_mem_coordGrading l) one_pos :=
      familyBaseChangeMap_comp_snd _ _
    simp only [a, b, Category.assoc]
    rw [← e1, ← e2, ← Category.assoc, ← Category.assoc, pullback.condition]
  set hW : W ⟶ Spec (.of k) := a ≫ (chartOver k i).hom
  have hW' : b ≫ (chartOver k l).hom = hW := by
    simp only [hW, Over.mk_hom, ← Category.assoc, hab]
  set A : Fin (n + 1) → Γ(W, ⊤) := fun m => a.appTop (chartFun k i m)
  set B : Fin (n + 1) → Γ(W, ⊤) := fun m => b.appTop (chartFun k l m)
  have hA := span_range_comp_eq_top a _ (span_range_chartFun k i)
  have hB := span_range_comp_eq_top b _ (span_range_chartFun k l)
  have eA : coordMor hW A hA = a ≫ awayι _ _ (X_mem_coordGrading i) one_pos := by
    rw [awayι_eq_coordMor k i, comp_coordMor]
  have eB : coordMor hW B hB = b ≫ awayι _ _ (X_mem_coordGrading l) one_pos := by
    rw [awayι_eq_coordMor k l, comp_coordMor]
    exact coordMor_congr_struct k hW'.symm _ _
  have hBl : B l = 1 := by simp [B, chartFun_self]
  have hAl : IsUnit (A l) := by
    refine Scheme.isUnit_of_basicOpen_eq_top _ ?_
    rw [← coordMor_preimage_basicOpen hW A hA l, eA, hab, Scheme.Hom.comp_preimage,
      awayι_preimage_basicOpen_self one_pos (X_mem_coordGrading l)]
    rfl
  have hprop := eq_inv_mul_of_coordMor_eq hW A B hA hB (eA.trans (hab.trans eB.symm)) l hBl
    hAl.unit rfl
  refine (comap_zeroScheme_coordSection L w _ _ _ _).trans
    (Eq.trans ?_ (comap_zeroScheme_coordSection L w _ _ _ _).symm)
  rw [show pullback.fst (chartMap k f i) (chartMap k f l) ≫ pullback.snd f (chartOver k i).hom =
    𝟙 W ≫ a from (Category.id_comp _).symm, coordSection_comp]
  rw [show pullback.snd (chartMap k f i) (chartMap k f l) ≫ pullback.snd f (chartOver k l).hom =
    𝟙 W ≫ b from (Category.id_comp _).symm, coordSection_comp]
  change zeroScheme W _ (coordSection _ (𝟙 W) L w A) = zeroScheme W _ (coordSection Pl (𝟙 W) L w B)
  rw [hprop, show (fun m => (↑hAl.unit⁻¹ : Γ(W, ⊤)) * A m) = (↑hAl.unit⁻¹ : Γ(W, ⊤)) • A from rfl,
    coordSection_smul, zeroScheme_unit_smul _ _ (by simp)]
  revert hP
  generalize pullback.fst (chartMap k f i) (chartMap k f l) ≫ pullback.fst f (chartOver k i).hom = P
  rintro rfl
  rfl

/-- **The universal divisor `𝒟 ⊆ X ×_k Q`**, glued from the chart divisors. -/
def universalDivisor :
    ((Over.pullback (projOver k (n := n)).hom).obj (curveOver f)).left.IdealSheafData :=
  ⨅ j, (pieceDivisor k f L w j).map (chartMap k f j)

/-- **`𝒟` restricted to the chart `X ×_k D₊(Tⱼ)` is the divisor of `Σᵢ (Tᵢ / Tⱼ) · wᵢ`.** -/
theorem comap_chartMap_universalDivisor (j : Fin (n + 1)) :
    (universalDivisor k f L w).comap (chartMap k f j) = pieceDivisor k f L w j :=
  comap_iInf_map_eq (fun i => chartMap k f i) (pieceDivisor k f L w)
    (pieceDivisor_compat k f L w) j

end Stacks.LinearSystemScheme

end
