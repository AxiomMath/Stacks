module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorBifunctor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionDecompositionBasePoint
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalFlat
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Coproduct

/-!
# Composition and tensor product along open and closed immersions

Let `iA : A ⟶ P`, `iB : B ⟶ Q`, `iC : C ⟶ R` be open immersions which are proper (that is, open and
closed immersions) of smooth separated schemes over a field `k`, with `A` and `P`, `B` and `Q`,
`C` and `R` of the same constant dimensions. Correspondences on the pieces push forward along
`iA × iB : A × B ⟶ P × Q`, and this file proves that the pushforward is compatible with
composition and with the tensor product of correspondences:

* `(iB × iC)_* y ∘ (iA × iB)_* x = (iA × iC)_*(y ∘ x)`;
* `(iB' × iC)_* y ∘ (iA × iB)_* x = 0` when `iB` and `iB'` have disjoint images;
* `(iA × iB)_* x ⊗ (iA' × iB')_* x' = ((iA × iA') × (iB × iB'))_*(x ⊗ x')`.

These are the naturality statements with which the composition and tensor product of
correspondences between schemes of varying dimension are assembled from their constant-dimension
blocks, the parts `X_d` of a smooth projective scheme being open and closed.

The proofs use Stacks 02RG (flat pullback commutes with proper pushforward in a cartesian square)
and the projection formula of Stacks 0FFC for the open and closed immersions, which are flat and
proper of relative dimension `0`; the tensor product case is
`Stacks.WeilCohomology.properChowPushforward_selfIntersectionProduct_heq`.

## Main definitions

* `Stacks.WeilCohomology.prodHomPushforward`: pushforward `Corrʳ(X', Y') ⟶ Corrʳ(X, Y)` of
  rational correspondences along a proper `φX × φY`.

## Main results

* `Stacks.WeilCohomology.compositionInt_properChowPushforward_prodHom`,
  `Stacks.WeilCohomology.compositionInt_properChowPushforward_prodHom_of_disjoint`,
  `Stacks.WeilCohomology.tensorInt_properChowPushforward_prodHom`: the three identities on
  integral Chow groups, for a family of diagonal classes satisfying the projection formula.
* `Stacks.WeilCohomology.composition_prodHomPushforward`,
  `Stacks.WeilCohomology.composition_prodHomPushforward_of_disjoint`,
  `Stacks.WeilCohomology.tensorBlock_prodHomPushforward`: the same for rational
  correspondences, and their `_canonical` forms for the canonical diagonal classes.

## References

* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 0FFC](https://stacks.math.columbia.edu/tag/0FFC)
* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

section Clopen

variable {k : Type u} [Field k] {Δ : DiagonalClassFamily k}

local notation "pf[" sA ", " sB ", " v ", " hv ", " n "]" =>
  properChowPushforward (fieldChowSituation k) sA sB v hv n
    (properPushforwardDescends _ _ _ _ _ _)

section Instances

variable {S X Y X' Y' : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) (sX' : X' ⟶ S) (sY' : Y' ⟶ S)
  (φX : X' ⟶ X) (φY : Y' ⟶ Y) (hφX : φX ≫ sX = sX') (hφY : φY ≫ sY = sY')

/-- A product `φX × φY` of open immersions is an open immersion. -/
instance [IsOpenImmersion φX] [IsOpenImmersion φY] :
    IsOpenImmersion (prodHom sX sY sX' sY' φX φY hφX hφY) :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance hφX.symm
    hφY.symm

/-- A product `φX × φY` of proper morphisms is proper. -/
instance [IsProper φX] [IsProper φY] : IsProper (prodHom sX sY sX' sY' φX φY hφX hφY) :=
  MorphismProperty.pullbackMap (P := @IsProper) inferInstance inferInstance hφX.symm hφY.symm

/-- `φX × 1 : X' × Z ⟶ X × Z` is the base change of `φX` along `pr₁ : X × Z ⟶ X`. -/
theorem isPullback_prodHom_id_left {Z : Scheme.{u}} (sZ : Z ⟶ S) :
    IsPullback (prodHom sX sZ sX' sZ φX (𝟙 Z) hφX (Category.id_comp _))
      (Limits.pullback.fst sX' sZ) (Limits.pullback.fst sX sZ) φX := by
  refine IsPullback.of_right (h₁₂ := Limits.pullback.snd sX sZ) (h₂₂ := sX) (v₁₃ := sZ) ?_
    (by simp) (IsPullback.of_hasPullback sX sZ).flip
  have h₁ : prodHom sX sZ sX' sZ φX (𝟙 Z) hφX (Category.id_comp _) ≫ Limits.pullback.snd sX sZ =
      Limits.pullback.snd sX' sZ := by simp
  rw [h₁, hφX]
  exact (IsPullback.of_hasPullback sX' sZ).flip

/-- `1 × φY : X × Y' ⟶ X × Y` is the base change of `φY` along `pr₂ : X × Y ⟶ Y`. -/
theorem isPullback_prodHom_id_right {Z : Scheme.{u}} (sZ : Z ⟶ S) :
    IsPullback (Limits.pullback.snd sZ sY') (prodHom sZ sY sZ sY' (𝟙 Z) φY (Category.id_comp _) hφY)
      φY (Limits.pullback.snd sZ sY) := by
  refine (IsPullback.of_right (h₁₂ := Limits.pullback.fst sZ sY) (h₂₂ := sY) (v₁₃ := sZ) ?_
    (by simp) (IsPullback.of_hasPullback sZ sY)).flip
  have h₁ : prodHom sZ sY sZ sY' (𝟙 Z) φY (Category.id_comp _) hφY ≫ Limits.pullback.fst sZ sY =
      Limits.pullback.fst sZ sY' := by simp
  rw [h₁, hφY]
  exact IsPullback.of_hasPullback sZ sY'

/-- A product of open immersions has relative dimension `0`. -/
theorem relativeDimension_prodHom [IsOpenImmersion φX] [IsOpenImmersion φY] :
    RelativeDimension (prodHom sX sY sX' sY' φX φY hφX hφY) 0 :=
  (locallyQuasiFinite_iff_relativeDimension_zero _).mp inferInstance

end Instances

section Rational

variable {X Y X' Y' : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) (sX' : X' ⟶ (fieldChowSituation k).S)
  (sY' : Y' ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX] [LocallyOfFiniteType sX']
  [LocallyOfFiniteType sY] [LocallyOfFiniteType sY']
  (φX : X' ⟶ X) (φY : Y' ⟶ Y) (hφX : φX ≫ sX = sX') (hφY : φY ≫ sY = sY')
  [IsProper (prodHom sX sY sX' sY' φX φY hφX hφY)]

/-- Pushforward of rational correspondences along `φX × φY : X' × Y' ⟶ X × Y`, for `φX × φY`
proper: `Corrʳ(X', Y') ⟶ Corrʳ(X, Y)`, with the target dimension `e` kept. -/
def prodHomPushforward (e r : ℤ) :
    Correspondence (fieldChowSituation k) sX' sY' e r →ₗ[ℚ]
      Correspondence (fieldChowSituation k) sX sY e r :=
  (properChowPushforward (fieldChowSituation k) _ _ (prodHom sX sY sX' sY' φX φY hφX hφY)
    (prodHom_comp_prodBase sX sY sX' sY' φX φY hφX hφY) _
    (properPushforwardDescends _ _ _ _ _ _)).toIntLinearMap.baseChange ℚ

/-- `prodHomPushforward` sends `q ⊗ c` to `q ⊗ (φX × φY)_* c`. -/
@[simp]
theorem prodHomPushforward_tmul (e r : ℤ) (q : ℚ)
    (c : chowGroup (fieldChowSituation k) (prodBase sX' sY') (e - r)) :
    prodHomPushforward sX sY sX' sY' φX φY hφX hφY e r (q ⊗ₜ[ℤ] c) =
      q ⊗ₜ[ℤ] properChowPushforward (fieldChowSituation k) _ _
        (prodHom sX sY sX' sY' φX φY hφX hφY) (prodHom_comp_prodBase sX sY sX' sY' φX φY hφX hφY)
        _ (properPushforwardDescends _ _ _ _ _ _) c :=
  rfl

end Rational

local notation "pb[" sA ", " sB ", " v ", " hv ", " r ", " hr ", " n "]" =>
  flatPullbackChow (fieldChowSituation k) sA sB v hv r hr n
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)

/-- **Pulling back a pushforward along an open and closed immersion**: for `g : X ⟶ Y` an open
immersion which is proper, `g^* g_* c = c`. The square `(𝟙, 𝟙, g, g)` is cartesian, `g` being a
monomorphism, so this is Stacks 02RG. -/
theorem flatPullbackChow_properChowPushforward_self_heq {X Y : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sY] (g : X ⟶ Y)
    [IsOpenImmersion g] [IsProper g] (hg : g ≫ sY = sX) (hg0 : RelativeDimension g 0) (n : ℤ)
    (c : chowGroup (fieldChowSituation k) sX n) :
    pb[sX, sY, g, hg, 0, hg0, n] (pf[sX, sY, g, hg, n] c) ≍ c := by
  have hsq : IsPullback (𝟙 X) (𝟙 X) g g := IsKernelPair.id_of_mono g
  rw [flatPullbackChow_properChowPushforward_of_isProper (fieldChowSituation k) sX sY sX sX g g
    (𝟙 X) (𝟙 X) hsq hg hg (Category.id_comp _) 0 hg0 n c, properChowPushforward_id]
  exact (heq_of_eq (flatPullbackChow_id (fieldChowSituation k) sX n c)).trans
    (chowGroupCast_heq _ _ _ _)

variable {A B C P Q R : Scheme.{u}}
  {sA : A ⟶ (fieldChowSituation k).S} {sB : B ⟶ (fieldChowSituation k).S}
  {sC : C ⟶ (fieldChowSituation k).S} {sP : P ⟶ (fieldChowSituation k).S}
  {sQ : Q ⟶ (fieldChowSituation k).S} {sR : R ⟶ (fieldChowSituation k).S}
  [Smooth sA] [IsSeparated sA] [Smooth sB] [IsSeparated sB] [Smooth sC] [IsSeparated sC]
  [Smooth sP] [IsSeparated sP] [Smooth sQ] [IsSeparated sQ] [Smooth sR] [IsSeparated sR]
  (iA : A ⟶ P) (iB : B ⟶ Q) (iC : C ⟶ R)
  [IsOpenImmersion iA] [IsProper iA] [IsOpenImmersion iB] [IsProper iB]
  [IsOpenImmersion iC] [IsProper iC]
  (hiA : iA ≫ sP = sA) (hiB : iB ≫ sQ = sB) (hiC : iC ≫ sR = sC)

local notation "μ" =>
  selfIntersectionProduct (fieldChowSituation k)
      (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
    (fieldGysinSystem k)

/-- Proper pushforward of heterogeneously equal classes along `u`, up to an equality of degrees. -/
private theorem properChowPushforward_heq_congr_self {X Y : Scheme.{u}}
    {sX : X ⟶ (fieldChowSituation k).S} [LocallyOfFiniteType sX]
    {sY : Y ⟶ (fieldChowSituation k).S} [LocallyOfFiniteType sY] {u : X ⟶ Y} [IsProper u]
    (hu : u ≫ sY = sX) {n n' : ℤ} (hn : n = n') {α : chowGroup (fieldChowSituation k) sX n}
    {α' : chowGroup (fieldChowSituation k) sX n'} (h : α ≍ α') :
    pf[sX, sY, u, hu, n] α ≍ pf[sX, sY, u, hu, n'] α' :=
  properChowPushforward_heq_congr _ sX sY u hu hn _ _ α α' h

omit [IsSeparated sC] [IsOpenImmersion iC] in
/-- The first half of the computation of `(φ_* y) ∘ (ψ_* x)` for open and closed immersions: with
`g = iA × iB × 1 : A × B × R ⟶ P × Q × R`, Stacks 02RG for `pr₁₂` and the projection formula for
`g` move the pushforward of `x` out of the intersection product. -/
private theorem compositionInt_prodHom_heq_aux [IsProper sQ] (hproj : Δ.ProjectionFormula)
    {B' : Scheme.{u}} {sB' : B' ⟶ (fieldChowSituation k).S} [Smooth sB'] [IsSeparated sB']
    (iB' : B' ⟶ Q) [IsOpenImmersion iB'] [IsProper iB'] (hiB' : iB' ≫ sQ = sB') {d e f : ℕ}
    (hA : RelativeDimension sA d) (hB : RelativeDimension sB e)
    (hP : RelativeDimension sP d) (hQ : RelativeDimension sQ e) (hR : RelativeDimension sR f)
    (r s : ℤ) (x : chowGroup (fieldChowSituation k) (prodBase sA sB) ((e : ℤ) - r))
    (y : chowGroup (fieldChowSituation k) (prodBase sB' sC) ((f : ℤ) - s)) :
    compositionInt k sP sQ sR Δ hP hQ hR r s
        (pf[prodBase sA sB, prodBase sP sQ, prodHom sP sQ sA sB iA iB hiA hiB,
          prodHom_comp_prodBase sP sQ sA sB iA iB hiA hiB, (e : ℤ) - r] x)
        (pf[prodBase sB' sC, prodBase sQ sR, prodHom sQ sR sB' sC iB' iC hiB' hiC,
          prodHom_comp_prodBase sQ sR sB' sC iB' iC hiB' hiC, (f : ℤ) - s] y) ≍
      pf[tripleBase sP sQ sR, prodBase sP sR, pr₁₃ sP sQ sR, pr₁₃_comp_prodBase sP sQ sR,
          ((e : ℤ) - r + f) + ((f : ℤ) - s + ((0 : ℕ) : ℤ) + d) - ((f + (e + d) : ℕ) : ℤ)]
      (pf[tripleBase sA sB sR, tripleBase sP sQ sR,
          prodHom (prodBase sP sQ) sR (prodBase sA sB) sR (prodHom sP sQ sA sB iA iB hiA hiB)
            (𝟙 R) (prodHom_comp_prodBase sP sQ sA sB iA iB hiA hiB) (Category.id_comp sR),
          prodHom_comp_prodBase _ _ _ _ _ _ _ _,
          ((e : ℤ) - r + f) + ((f : ℤ) - s + ((0 : ℕ) : ℤ) + d) - ((f + (e + d) : ℕ) : ℤ)]
        (μ (tripleBase sA sB sR) (f + (e + d))
          (Δ _ _ (relativeDimension_tripleBase k sA sB sR hA hB hR))
          ((e : ℤ) - r + f) ((f : ℤ) - s + ((0 : ℕ) : ℤ) + d)
          (pb[tripleBase sA sB sR, prodBase sA sB, pr₁₂ sA sB sR, pr₁₂_comp_prodBase sA sB sR, f,
            relativeDimension_pr₁₂ k sA sB sR hR, (e : ℤ) - r] x)
          (pb[tripleBase sA sB sR, prodBase sB sR, pr₂₃ sA sB sR, pr₂₃_comp_prodBase sA sB sR, d,
            relativeDimension_pr₂₃ k sA sB sR hA, (f : ℤ) - s + ((0 : ℕ) : ℤ)]
            (pb[prodBase sB sR, prodBase sQ sR, prodHom sQ sR sB sR iB (𝟙 R) hiB
                (Category.id_comp sR), prodHom_comp_prodBase _ _ _ _ _ _ _ _, 0,
                relativeDimension_prodHom _ _ _ _ _ _ _ _, (f : ℤ) - s]
              (pf[prodBase sB' sC, prodBase sQ sR, prodHom sQ sR sB' sC iB' iC hiB' hiC,
                prodHom_comp_prodBase sQ sR sB' sC iB' iC hiB' hiC, (f : ℤ) - s] y))))) := by
  have hT := relativeDimension_tripleBase k sP sQ sR hP hQ hR
  have hM := relativeDimension_tripleBase k sA sB sR hA hB hR
  have hg0 := relativeDimension_prodHom (prodBase sP sQ) sR (prodBase sA sB) sR
    (prodHom sP sQ sA sB iA iB hiA hiB) (𝟙 R) (prodHom_comp_prodBase sP sQ sA sB iA iB hiA hiB)
    (Category.id_comp sR)
  have hBR0 := relativeDimension_prodHom sQ sR sB sR iB (𝟙 R) hiB (Category.id_comp sR)
  have hsqA : IsPullback (pr₁₂ sA sB sR)
      (prodHom (prodBase sP sQ) sR (prodBase sA sB) sR (prodHom sP sQ sA sB iA iB hiA hiB)
        (𝟙 R) (prodHom_comp_prodBase sP sQ sA sB iA iB hiA hiB) (Category.id_comp sR))
      (prodHom sP sQ sA sB iA iB hiA hiB) (pr₁₂ sP sQ sR) :=
    (isPullback_prodHom_id_left (prodBase sP sQ) (prodBase sA sB) _
      (prodHom_comp_prodBase sP sQ sA sB iA iB hiA hiB) sR).flip
  have hAeq := flatPullbackChow_properChowPushforward_of_isProper (fieldChowSituation k)
    (prodBase sA sB) (prodBase sP sQ) (tripleBase sA sB sR) (tripleBase sP sQ sR)
    (prodHom sP sQ sA sB iA iB hiA hiB) (pr₁₂ sP sQ sR) (pr₁₂ sA sB sR) _ hsqA
    (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (pr₁₂_comp_prodBase _ _ _) (pr₁₂_comp_prodBase _ _ _)
    f (relativeDimension_pr₁₂ k sP sQ sR hR) ((e : ℤ) - r) x
  have hc : prodHom (prodBase sP sQ) sR (prodBase sA sB) sR (prodHom sP sQ sA sB iA iB hiA hiB)
        (𝟙 R) (prodHom_comp_prodBase sP sQ sA sB iA iB hiA hiB) (Category.id_comp sR) ≫
        pr₂₃ sP sQ sR =
      pr₂₃ sA sB sR ≫ prodHom sQ sR sB sR iB (𝟙 R) hiB (Category.id_comp sR) := by
    apply Limits.pullback.hom_ext <;> simp
  refine (compositionInt_heq k Δ sP sQ sR hP hQ hR r s _ _).trans ?_
  refine properChowPushforward_heq_congr_self (pr₁₃_comp_prodBase _ _ _) (by push_cast; ring) ?_
  refine (selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl rfl rfl (heq_of_eq hAeq)
    HEq.rfl).trans ?_
  refine (hproj.heq_right (tripleBase sP sQ sR) (tripleBase sA sB sR) _
    (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (by omega) hg0 hT hM _ _ _ _).trans ?_
  refine properChowPushforward_heq_congr_self (prodHom_comp_prodBase _ _ _ _ _ _ _ _)
    (by push_cast; ring) ?_
  refine selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl rfl (by push_cast; ring) HEq.rfl ?_
  exact flatPullbackChow_heq_of_comp_eq _ _ _ _ _ (pr₂₃ sP sQ sR) (pr₂₃ sA sB sR) _
    (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (pr₂₃_comp_prodBase _ _ _) (pr₂₃_comp_prodBase _ _ _)
    (prodHom_comp_prodBase _ _ _ _ _ _ _ _) hg0
    (relativeDimension_pr₂₃ k sP sQ sR hP) (relativeDimension_pr₂₃ k sA sB sR hA) hBR0 hc
    (by omega) _ _

/-- **Composition along open and closed immersions**, on integral Chow groups, for schemes of
constant dimension: `(iB × iC)_* y ∘ (iA × iB)_* x = (iA × iC)_*(y ∘ x)`. -/
theorem compositionInt_properChowPushforward_prodHom [IsProper sB] [IsProper sQ]
    (hproj : Δ.ProjectionFormula) {d e f : ℕ}
    (hA : RelativeDimension sA d) (hB : RelativeDimension sB e) (hC : RelativeDimension sC f)
    (hP : RelativeDimension sP d) (hQ : RelativeDimension sQ e) (hR : RelativeDimension sR f)
    (r s : ℤ) (x : chowGroup (fieldChowSituation k) (prodBase sA sB) ((e : ℤ) - r))
    (y : chowGroup (fieldChowSituation k) (prodBase sB sC) ((f : ℤ) - s)) :
    compositionInt k sP sQ sR Δ hP hQ hR r s
        (pf[prodBase sA sB, prodBase sP sQ, prodHom sP sQ sA sB iA iB hiA hiB,
          prodHom_comp_prodBase sP sQ sA sB iA iB hiA hiB, (e : ℤ) - r] x)
        (pf[prodBase sB sC, prodBase sQ sR, prodHom sQ sR sB sC iB iC hiB hiC,
          prodHom_comp_prodBase sQ sR sB sC iB iC hiB hiC, (f : ℤ) - s] y) =
      pf[prodBase sA sC, prodBase sP sR, prodHom sP sR sA sC iA iC hiA hiC,
          prodHom_comp_prodBase sP sR sA sC iA iC hiA hiC, (f : ℤ) - (r + s)]
        (compositionInt k sA sB sC Δ hA hB hC r s x y) := by
  have hBR0 := relativeDimension_prodHom sQ sR sB sR iB (𝟙 R) hiB (Category.id_comp sR)
  have hM := relativeDimension_tripleBase k sA sB sR hA hB hR
  have hN := relativeDimension_tripleBase k sA sB sC hA hB hC
  -- `j₂ = 1 × 1 × iC : A × B × C ⟶ A × B × R`
  have hj₂0 := relativeDimension_prodHom (prodBase sA sB) sR (prodBase sA sB) sC (𝟙 _) iC
    (Category.id_comp _) hiC
  have hsqC : IsPullback (pr₂₃ sA sB sC)
      (prodHom (prodBase sA sB) sR (prodBase sA sB) sC (𝟙 _) iC (Category.id_comp _) hiC)
      (prodHom sB sR sB sC (𝟙 B) iC (Category.id_comp _) hiC) (pr₂₃ sA sB sR) := by
    refine IsPullback.of_bot (v₂₁ := pr₁₂ sA sB sR) (v₂₂ := Limits.pullback.fst sB sR)
      (h₃₁ := Limits.pullback.snd sA sB) ?_ (by apply Limits.pullback.hom_ext <;> simp)
      (isPullback_pr₁₂_pr₂₃ sA sB sR).flip
    have e₁ : prodHom (prodBase sA sB) sR (prodBase sA sB) sC (𝟙 _) iC (Category.id_comp _) hiC ≫
        pr₁₂ sA sB sR = pr₁₂ sA sB sC := by simp
    have e₂ : prodHom sB sR sB sC (𝟙 B) iC (Category.id_comp _) hiC ≫
        Limits.pullback.fst sB sR = Limits.pullback.fst sB sC := by simp
    rw [e₁, e₂]
    exact (isPullback_pr₁₂_pr₂₃ sA sB sC).flip
  -- `(iB × iC)_* y = (iB × 1)_* (1 × iC)_* y`, and `(iB × 1)^* (iB × 1)_* = 1`
  have hy : pb[prodBase sB sR, prodBase sQ sR, prodHom sQ sR sB sR iB (𝟙 R) hiB
        (Category.id_comp sR), prodHom_comp_prodBase _ _ _ _ _ _ _ _, 0, hBR0, (f : ℤ) - s]
        (pf[prodBase sB sC, prodBase sQ sR, prodHom sQ sR sB sC iB iC hiB hiC,
          prodHom_comp_prodBase sQ sR sB sC iB iC hiB hiC, (f : ℤ) - s] y) ≍
      pf[prodBase sB sC, prodBase sB sR, prodHom sB sR sB sC (𝟙 B) iC (Category.id_comp _) hiC,
        prodHom_comp_prodBase _ _ _ _ _ _ _ _, (f : ℤ) - s] y := by
    rw [properChowPushforward_comp_apply (fieldChowSituation k) (prodBase sB sC) (prodBase sB sR)
      (prodBase sQ sR) (prodHom sB sR sB sC (𝟙 B) iC (Category.id_comp _) hiC)
      (prodHom sQ sR sB sR iB (𝟙 R) hiB (Category.id_comp sR))
      (prodHom sQ sR sB sC iB iC hiB hiC) (by apply Limits.pullback.hom_ext <;> simp)
      (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)
      (prodHom_comp_prodBase _ _ _ _ _ _ _ _) _ (properPushforwardDescends _ _ _ _ _ _)
      (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _) y]
    exact flatPullbackChow_properChowPushforward_self_heq _ _ _ _ hBR0 _ _
  -- Stacks 02RG for `pr₂₃` and `j₂`
  have hCeq := flatPullbackChow_properChowPushforward_of_isProper (fieldChowSituation k)
    (prodBase sB sC) (prodBase sB sR) (tripleBase sA sB sC) (tripleBase sA sB sR)
    (prodHom sB sR sB sC (𝟙 B) iC (Category.id_comp _) hiC) (pr₂₃ sA sB sR) (pr₂₃ sA sB sC) _ hsqC
    (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (pr₂₃_comp_prodBase _ _ _) (pr₂₃_comp_prodBase _ _ _)
    d (relativeDimension_pr₂₃ k sA sB sR hA) ((f : ℤ) - s) y
  -- the composite of the pushforwards
  have hcomp : (prodHom (prodBase sA sB) sR (prodBase sA sB) sC (𝟙 _) iC (Category.id_comp _) hiC ≫
        prodHom (prodBase sP sQ) sR (prodBase sA sB) sR (prodHom sP sQ sA sB iA iB hiA hiB)
          (𝟙 R) (prodHom_comp_prodBase sP sQ sA sB iA iB hiA hiB) (Category.id_comp sR)) ≫
        pr₁₃ sP sQ sR = pr₁₃ sA sB sC ≫ prodHom sP sR sA sC iA iC hiA hiC := by
    apply Limits.pullback.hom_ext <;> simp
  refine eq_of_heq ((compositionInt_prodHom_heq_aux iA iB iC hiA hiB hiC hproj iB hiB hA hB hP hQ
    hR r s x y).trans ?_)
  refine HEq.trans ?_ (properChowPushforward_heq_congr_self (prodHom_comp_prodBase _ _ _ _ _ _ _ _)
    (by push_cast; ring) (compositionInt_heq k Δ sA sB sC hA hB hC r s x y)).symm
  have hj₂ := prodHom_comp_prodBase (prodBase sA sB) sR (prodBase sA sB) sC (𝟙 _) iC
    (Category.id_comp _) hiC
  have hg := prodHom_comp_prodBase (prodBase sP sQ) sR (prodBase sA sB) sR
    (prodHom sP sQ sA sB iA iB hiA hiB) (𝟙 R) (prodHom_comp_prodBase sP sQ sA sB iA iB hiA hiB)
    (Category.id_comp sR)
  -- the intersection product on `A × B × R` is the pushforward of the one on `A × B × C`
  have hZ := ((selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl rfl (by push_cast; ring) HEq.rfl
      ((flatPullbackChow_heq_congr _ _ _ (pr₂₃ sA sB sR) (pr₂₃ sA sB sR) (pr₂₃_comp_prodBase _ _ _)
        (pr₂₃_comp_prodBase _ _ _) rfl rfl (relativeDimension_pr₂₃ k sA sB sR hA)
        (relativeDimension_pr₂₃ k sA sB sR hA) (by push_cast; ring)
        (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
        (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) _ _ hy).trans
        (heq_of_eq hCeq))).trans
    (hproj.heq_left (tripleBase sA sB sR) (tripleBase sA sB sC) _ hj₂ (by omega) hj₂0 hM hN _ _ _
      _)).trans
    (properChowPushforward_heq_congr_self hj₂
      (show _ = ((e : ℤ) - r + f) + ((f : ℤ) - s + d) - ((f + (e + d) : ℕ) : ℤ) by push_cast; ring)
      (selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl (by push_cast; ring) rfl
        ((flatPullbackChow_comp _ (tripleBase sA sB sC) (tripleBase sA sB sR) (prodBase sA sB) _
          (pr₁₂ sA sB sR) hj₂ (pr₁₂_comp_prodBase _ _ _) 0 f hj₂0
          (relativeDimension_pr₁₂ k sA sB sR hR) ((e : ℤ) - r)
          (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
          (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
          (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) x).trans
          (flatPullbackChow_heq_congr _ _ _ _ (pr₁₂ sA sB sC) _ (pr₁₂_comp_prodBase _ _ _)
            (by simp) (by omega) _ (relativeDimension_pr₁₂ k sA sB sC hC) rfl
            (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
            (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) x x HEq.rfl))
        HEq.rfl))
  refine (properChowPushforward_heq_congr_self (pr₁₃_comp_prodBase _ _ _) (by push_cast; ring)
    (properChowPushforward_heq_congr_self hg (by push_cast; ring) hZ)).trans ?_
  refine heq_of_eq ?_
  rw [← properChowPushforward_comp_apply (fieldChowSituation k) (tripleBase sA sB sC)
    (tripleBase sA sB sR) (tripleBase sP sQ sR) _ _ _ rfl hj₂ hg (by rw [Category.assoc, hg, hj₂])
    _ (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
    (properPushforwardDescends _ _ _ _ _ _)]
  exact properChowPushforward_comp_eq (fieldChowSituation k) (tripleBase sA sB sC)
    (tripleBase sP sQ sR) (prodBase sA sC) (prodBase sP sR) _ (pr₁₃ sP sQ sR) (pr₁₃ sA sB sC)
    (prodHom sP sR sA sC iA iC hiA hiC) hcomp _ (pr₁₃_comp_prodBase _ _ _)
    (pr₁₃_comp_prodBase _ _ _)
    (prodHom_comp_prodBase _ _ _ _ _ _ _ _) _ (properPushforwardDescends _ _ _ _ _ _)
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
    (properPushforwardDescends _ _ _ _ _ _) _

omit [IsSeparated sC] [IsOpenImmersion iC] in
/-- **Composition through disjoint open and closed pieces vanishes**, on integral Chow groups:
`(iB' × iC)_* y ∘ (iA × iB)_* x = 0` when the images of `iB` and `iB'` are disjoint, the fibre
product of `B × R` and `B' × C` over `Q × R` being empty. -/
theorem compositionInt_properChowPushforward_prodHom_of_disjoint [IsProper sQ]
    (hproj : Δ.ProjectionFormula) {B' : Scheme.{u}}
    {sB' : B' ⟶ (fieldChowSituation k).S} [Smooth sB'] [IsSeparated sB'] (iB' : B' ⟶ Q)
    [IsOpenImmersion iB'] [IsProper iB'] (hiB' : iB' ≫ sQ = sB')
    (hdisj : Disjoint (Set.range iB.base) (Set.range iB'.base)) {d e f : ℕ}
    (hA : RelativeDimension sA d) (hB : RelativeDimension sB e)
    (hP : RelativeDimension sP d) (hQ : RelativeDimension sQ e) (hR : RelativeDimension sR f)
    (r s : ℤ) (x : chowGroup (fieldChowSituation k) (prodBase sA sB) ((e : ℤ) - r))
    (y : chowGroup (fieldChowSituation k) (prodBase sB' sC) ((f : ℤ) - s)) :
    compositionInt k sP sQ sR Δ hP hQ hR r s
        (pf[prodBase sA sB, prodBase sP sQ, prodHom sP sQ sA sB iA iB hiA hiB,
          prodHom_comp_prodBase sP sQ sA sB iA iB hiA hiB, (e : ℤ) - r] x)
        (pf[prodBase sB' sC, prodBase sQ sR, prodHom sQ sR sB' sC iB' iC hiB' hiC,
          prodHom_comp_prodBase sQ sR sB' sC iB' iC hiB' hiC, (f : ℤ) - s] y) = 0 := by
  have hBR0 := relativeDimension_prodHom sQ sR sB sR iB (𝟙 R) hiB (Category.id_comp sR)
  -- the fibre product of `B × R` and `B' × C` over `Q × R` is empty
  have hsq := IsPullback.of_hasPullback (prodHom sQ sR sB' sC iB' iC hiB' hiC)
    (prodHom sQ sR sB sR iB (𝟙 R) hiB (Category.id_comp sR))
  have : IsEmpty (Limits.pullback (prodHom sQ sR sB' sC iB' iC hiB' hiC)
      (prodHom sQ sR sB sR iB (𝟙 R) hiB (Category.id_comp sR)) : Scheme.{u}) := ⟨fun z ↦ by
    have e : (Limits.pullback.fst (prodHom sQ sR sB' sC iB' iC hiB' hiC)
          (prodHom sQ sR sB sR iB (𝟙 R) hiB (Category.id_comp sR)) ≫
          Limits.pullback.fst sB' sC) ≫ iB' =
        (Limits.pullback.snd (prodHom sQ sR sB' sC iB' iC hiB' hiC)
          (prodHom sQ sR sB sR iB (𝟙 R) hiB (Category.id_comp sR)) ≫
          Limits.pullback.fst sB sR) ≫ iB := by
      have := Limits.pullback.condition (f := prodHom sQ sR sB' sC iB' iC hiB' hiC)
        (g := prodHom sQ sR sB sR iB (𝟙 R) hiB (Category.id_comp sR)) =≫
        Limits.pullback.fst sQ sR
      simpa using this
    have h := congrArg (fun φ ↦ φ.base z) e
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    exact Set.disjoint_left.1 hdisj ⟨_, h.symm⟩ ⟨_, rfl⟩⟩
  have hzero : pb[prodBase sB sR, prodBase sQ sR, prodHom sQ sR sB sR iB (𝟙 R) hiB
      (Category.id_comp sR), prodHom_comp_prodBase _ _ _ _ _ _ _ _, 0, hBR0, (f : ℤ) - s]
      (pf[prodBase sB' sC, prodBase sQ sR, prodHom sQ sR sB' sC iB' iC hiB' hiC,
        prodHom_comp_prodBase sQ sR sB' sC iB' iC hiB' hiC, (f : ℤ) - s] y) = 0 := by
    rw [flatPullbackChow_properChowPushforward_of_isProper (fieldChowSituation k) (prodBase sB' sC)
      (prodBase sQ sR) _ (prodBase sB sR) _ _ _ _ hsq (prodHom_comp_prodBase _ _ _ _ _ _ _ _)
      (prodHom_comp_prodBase _ _ _ _ _ _ _ _) rfl 0 hBR0 _ y]
    have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k)
      (Limits.pullback.fst (prodHom sQ sR sB' sC iB' iC hiB' hiC)
        (prodHom sQ sR sB sR iB (𝟙 R) hiB (Category.id_comp sR)) ≫ prodBase sB' sC)
      ((f : ℤ) - s + ((0 : ℕ) : ℤ))
    rw [Subsingleton.elim (flatPullbackChow _ _ _ _ _ _ _ _ _ y) 0, map_zero]
  have h := compositionInt_prodHom_heq_aux iA iB iC hiA hiB hiC hproj iB' hiB' hA hB hP hQ hR r s
    x y
  rw [hzero] at h
  simp only [map_zero] at h
  exact eq_of_heq (h.trans (Stacks.Chow.chowGroup_zero_heq _ _ (by push_cast; ring)))

variable {A' B' P' Q' : Scheme.{u}}
  {sA' : A' ⟶ (fieldChowSituation k).S} {sB' : B' ⟶ (fieldChowSituation k).S}
  {sP' : P' ⟶ (fieldChowSituation k).S} {sQ' : Q' ⟶ (fieldChowSituation k).S}
  [Smooth sA'] [IsSeparated sA'] [Smooth sB'] [IsSeparated sB'] [Smooth sP'] [IsSeparated sP']
  [Smooth sQ'] [IsSeparated sQ'] (iA' : A' ⟶ P') (iB' : B' ⟶ Q')
  [IsOpenImmersion iA'] [IsProper iA'] [IsOpenImmersion iB'] [IsProper iB']
  (hiA' : iA' ≫ sP' = sA') (hiB' : iB' ≫ sQ' = sB')

/-- **Tensor product along open and closed immersions**, on integral Chow groups, for schemes of
constant dimension: `(iA × iB)_* x ⊗ (iA' × iB')_* x' = ((iA × iA') × (iB × iB'))_*(x ⊗ x')`. -/
theorem tensorInt_properChowPushforward_prodHom
    (hproj : Δ.ProjectionFormula) {d d' e e' : ℕ}
    (hA : RelativeDimension sA d) (hA' : RelativeDimension sA' d')
    (hB : RelativeDimension sB e) (hB' : RelativeDimension sB' e')
    (hP : RelativeDimension sP d) (hP' : RelativeDimension sP' d')
    (hQ : RelativeDimension sQ e) (hQ' : RelativeDimension sQ' e') (r r' : ℤ)
    (x : chowGroup (fieldChowSituation k) (prodBase sA sB) ((e : ℤ) - r))
    (x' : chowGroup (fieldChowSituation k) (prodBase sA' sB') ((e' : ℤ) - r')) :
    tensorInt k sP sP' sQ sQ' Δ hP hP' hQ hQ' r r'
        (pf[prodBase sA sB, prodBase sP sQ, prodHom sP sQ sA sB iA iB hiA hiB,
          prodHom_comp_prodBase sP sQ sA sB iA iB hiA hiB, (e : ℤ) - r] x)
        (pf[prodBase sA' sB', prodBase sP' sQ', prodHom sP' sQ' sA' sB' iA' iB' hiA' hiB',
          prodHom_comp_prodBase sP' sQ' sA' sB' iA' iB' hiA' hiB', (e' : ℤ) - r'] x') =
      pf[tensorBase sA sA' sB sB', tensorBase sP sP' sQ sQ',
          prodHom (prodBase sP sP') (prodBase sQ sQ') (prodBase sA sA') (prodBase sB sB')
            (prodHom sP sP' sA sA' iA iA' hiA hiA') (prodHom sQ sQ' sB sB' iB iB' hiB hiB')
            (prodHom_comp_prodBase sP sP' sA sA' iA iA' hiA hiA')
            (prodHom_comp_prodBase sQ sQ' sB sB' iB iB' hiB hiB'),
          prodHom_comp_prodBase _ _ _ _ _ _ _ _, ((e + e' : ℕ) : ℤ) - (r + r')]
        (tensorInt k sA sA' sB sB' Δ hA hA' hB hB' r r' x x') := by
  -- the two sides, unfolded to `pr₁₃^* · pr₂₄^*`
  refine eq_of_heq ((tensorInt_heq k sP sP' sQ sQ' hP hP' hQ hQ' r r' _ _).trans ?_)
  refine HEq.trans ?_ (properChowPushforward_heq_congr_self _ (by push_cast; ring)
    (tensorInt_heq k sA sA' sB sB' hA hA' hB hB' r r' x x')).symm
  exact (properChowPushforward_selfIntersectionProduct_heq hproj (tensorBase sP sP' sQ sQ')
    (prodBase sP sQ) (prodBase sP' sQ') (tensorBase sA sA' sB sB') (prodBase sA sB)
    (prodBase sA' sB') (tensorPr₁₃ sP sP' sQ sQ') (tensorPr₂₄ sP sP' sQ sQ')
    (tensorPr₁₃ sA sA' sB sB') (tensorPr₂₄ sA sA' sB sB')
    (isPullback_tensorPr₁₃_tensorPr₂₄ sP sP' sQ sQ')
    (isPullback_tensorPr₁₃_tensorPr₂₄ sA sA' sB sB')
    _ (prodHom sP sQ sA sB iA iB hiA hiB) (prodHom sP' sQ' sA' sB' iA' iB' hiA' hiB')
    (tensorPr₁₃_comp_prodBase _ _ _ _) (tensorPr₂₄_comp_prodBase _ _ _ _)
    (tensorPr₁₃_comp_prodBase _ _ _ _) (tensorPr₂₄_comp_prodBase _ _ _ _)
    (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)
    (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (by apply Limits.pullback.hom_ext <;> simp)
    (by apply Limits.pullback.hom_ext <;> simp)
    (relativeDimension_tensorPr₁₃ k sP sP' sQ sQ' hP' hQ')
    (relativeDimension_tensorPr₂₄ k sP sP' sQ sQ' hP hQ)
    (relativeDimension_tensorPr₁₃ k sA sA' sB sB' hA' hB')
    (relativeDimension_tensorPr₂₄ k sA sA' sB sB' hA hB)
    (relativeDimension_prodHom _ _ _ _ _ _ _ _) (relativeDimension_prodHom _ _ _ _ _ _ _ _)
    (relativeDimension_prodBase k sP sQ hP hQ) (relativeDimension_prodBase k sA' sB' hA' hB')
    (relativeDimension_tensorBase k sP sP' sQ sQ' hP hP' hQ hQ')
    (relativeDimension_tensorBase k sA sA' sB sB' hA hA' hB hB') (by omega) (by omega)
    (by omega) (by omega) _ _ x x').symm

/-! ### Rational correspondences -/

/-- **Composition along open and closed immersions**, for rational correspondences:
`(iB × iC)_* y ∘ (iA × iB)_* x = (iA × iC)_*(y ∘ x)`. -/
theorem composition_prodHomPushforward [IsProper sB] [IsProper sQ]
    (hproj : Δ.ProjectionFormula) {d e f : ℕ}
    (hA : RelativeDimension sA d) (hB : RelativeDimension sB e) (hC : RelativeDimension sC f)
    (hP : RelativeDimension sP d) (hQ : RelativeDimension sQ e) (hR : RelativeDimension sR f)
    (r s : ℤ) (x : Correspondence (fieldChowSituation k) sA sB e r)
    (y : Correspondence (fieldChowSituation k) sB sC f s) :
    composition k sP sQ sR Δ hP hQ hR r s (prodHomPushforward sP sQ sA sB iA iB hiA hiB e r x)
        (prodHomPushforward sQ sR sB sC iB iC hiB hiC f s y) =
      prodHomPushforward sP sR sA sC iA iC hiA hiC f (r + s)
        (composition k sA sB sC Δ hA hB hC r s x y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul q a =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a' b' ha hb => simp only [map_add, ha, hb]
    | tmul q' c =>
      rw [prodHomPushforward_tmul, prodHomPushforward_tmul, composition_tmul, composition_tmul,
        prodHomPushforward_tmul,
        compositionInt_properChowPushforward_prodHom iA iB iC hiA hiB hiC hproj hA hB hC hP hQ hR]

omit [IsSeparated sC] [IsOpenImmersion iC] in
/-- **Composition through disjoint open and closed pieces vanishes**, for rational
correspondences. -/
theorem composition_prodHomPushforward_of_disjoint [IsProper sQ]
    (hproj : Δ.ProjectionFormula) {B' : Scheme.{u}}
    {sB' : B' ⟶ (fieldChowSituation k).S} [Smooth sB'] [IsSeparated sB'] (iB' : B' ⟶ Q)
    [IsOpenImmersion iB'] [IsProper iB'] (hiB' : iB' ≫ sQ = sB')
    (hdisj : Disjoint (Set.range iB.base) (Set.range iB'.base)) {d e f : ℕ}
    (hA : RelativeDimension sA d) (hB : RelativeDimension sB e)
    (hP : RelativeDimension sP d) (hQ : RelativeDimension sQ e) (hR : RelativeDimension sR f)
    (r s : ℤ) (x : Correspondence (fieldChowSituation k) sA sB e r)
    (y : Correspondence (fieldChowSituation k) sB' sC f s) :
    composition k sP sQ sR Δ hP hQ hR r s (prodHomPushforward sP sQ sA sB iA iB hiA hiB e r x)
        (prodHomPushforward sQ sR sB' sC iB' iC hiB' hiC f s y) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, add_zero]
  | tmul q a =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a' b' ha hb => simp only [map_add, ha, hb, add_zero]
    | tmul q' c =>
      rw [prodHomPushforward_tmul, prodHomPushforward_tmul, composition_tmul,
        compositionInt_properChowPushforward_prodHom_of_disjoint iA iB iC hiA hiB hiC hproj iB'
          hiB' hdisj hA hB hP hQ hR, TensorProduct.tmul_zero]

/-- **Tensor product along open and closed immersions**, for rational correspondences:
`(iA × iB)_* x ⊗ (iA' × iB')_* x' = ((iA × iA') × (iB × iB'))_*(x ⊗ x')`. -/
theorem tensorBlock_prodHomPushforward (hproj : Δ.ProjectionFormula) {d d' e e' : ℕ}
    (hA : RelativeDimension sA d) (hA' : RelativeDimension sA' d')
    (hB : RelativeDimension sB e) (hB' : RelativeDimension sB' e')
    (hP : RelativeDimension sP d) (hP' : RelativeDimension sP' d')
    (hQ : RelativeDimension sQ e) (hQ' : RelativeDimension sQ' e') (r r' : ℤ)
    (x : Correspondence (fieldChowSituation k) sA sB e r)
    (x' : Correspondence (fieldChowSituation k) sA' sB' e' r') :
    tensorBlock k sP sP' sQ sQ' Δ hP hP' hQ hQ' r r'
        (prodHomPushforward sP sQ sA sB iA iB hiA hiB e r x)
        (prodHomPushforward sP' sQ' sA' sB' iA' iB' hiA' hiB' e' r' x') =
      prodHomPushforward (prodBase sP sP') (prodBase sQ sQ') (prodBase sA sA') (prodBase sB sB')
        (prodHom sP sP' sA sA' iA iA' hiA hiA') (prodHom sQ sQ' sB sB' iB iB' hiB hiB')
        (prodHom_comp_prodBase sP sP' sA sA' iA iA' hiA hiA')
        (prodHom_comp_prodBase sQ sQ' sB sB' iB iB' hiB hiB') ((e + e' : ℕ) : ℤ) (r + r')
        (tensorBlock k sA sA' sB sB' Δ hA hA' hB hB' r r' x x') := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul q a =>
    induction x' using TensorProduct.induction_on with
    | zero => simp
    | add a' b' ha hb => simp only [map_add, ha, hb]
    | tmul q' c =>
      rw [prodHomPushforward_tmul, prodHomPushforward_tmul, tensorBlock_tmul, tensorBlock_tmul,
        prodHomPushforward_tmul,
        tensorInt_properChowPushforward_prodHom iA iB hiA hiB iA' iB' hiA' hiB' hproj hA hA' hB hB'
          hP hP' hQ hQ']

/-! ### The canonical diagonal classes -/

/-- `Stacks.WeilCohomology.composition_prodHomPushforward` for the canonical diagonal
classes. -/
theorem composition_prodHomPushforward_canonical [IsProper sB] [IsProper sQ] {d e f : ℕ}
    (hA : RelativeDimension sA d) (hB : RelativeDimension sB e) (hC : RelativeDimension sC f)
    (hP : RelativeDimension sP d) (hQ : RelativeDimension sQ e) (hR : RelativeDimension sR f)
    (r s : ℤ) (x : Correspondence (fieldChowSituation k) sA sB e r)
    (y : Correspondence (fieldChowSituation k) sB sC f s) :
    composition k sP sQ sR (canonicalDiagonalClassFamily k) hP hQ hR r s
        (prodHomPushforward sP sQ sA sB iA iB hiA hiB e r x)
        (prodHomPushforward sQ sR sB sC iB iC hiB hiC f s y) =
      prodHomPushforward sP sR sA sC iA iC hiA hiC f (r + s)
        (composition k sA sB sC (canonicalDiagonalClassFamily k) hA hB hC r s x y) :=
  composition_prodHomPushforward iA iB iC hiA hiB hiC
    (canonicalDiagonalClassFamily_projectionFormula k) hA hB hC hP hQ hR r s x y

omit [IsSeparated sC] [IsOpenImmersion iC] in
/-- `Stacks.WeilCohomology.composition_prodHomPushforward_of_disjoint` for the canonical
diagonal classes. -/
theorem composition_prodHomPushforward_of_disjoint_canonical [IsProper sQ] {B' : Scheme.{u}}
    {sB' : B' ⟶ (fieldChowSituation k).S} [Smooth sB'] [IsSeparated sB'] (iB' : B' ⟶ Q)
    [IsOpenImmersion iB'] [IsProper iB'] (hiB' : iB' ≫ sQ = sB')
    (hdisj : Disjoint (Set.range iB.base) (Set.range iB'.base)) {d e f : ℕ}
    (hA : RelativeDimension sA d) (hB : RelativeDimension sB e)
    (hP : RelativeDimension sP d) (hQ : RelativeDimension sQ e) (hR : RelativeDimension sR f)
    (r s : ℤ) (x : Correspondence (fieldChowSituation k) sA sB e r)
    (y : Correspondence (fieldChowSituation k) sB' sC f s) :
    composition k sP sQ sR (canonicalDiagonalClassFamily k) hP hQ hR r s
        (prodHomPushforward sP sQ sA sB iA iB hiA hiB e r x)
        (prodHomPushforward sQ sR sB' sC iB' iC hiB' hiC f s y) = 0 :=
  composition_prodHomPushforward_of_disjoint iA iB iC hiA hiB hiC
    (canonicalDiagonalClassFamily_projectionFormula k) iB' hiB' hdisj hA hB hP hQ hR r s x y

/-- `Stacks.WeilCohomology.tensorBlock_prodHomPushforward` for the canonical diagonal
classes. -/
theorem tensorBlock_prodHomPushforward_canonical {d d' e e' : ℕ}
    (hA : RelativeDimension sA d) (hA' : RelativeDimension sA' d')
    (hB : RelativeDimension sB e) (hB' : RelativeDimension sB' e')
    (hP : RelativeDimension sP d) (hP' : RelativeDimension sP' d')
    (hQ : RelativeDimension sQ e) (hQ' : RelativeDimension sQ' e') (r r' : ℤ)
    (x : Correspondence (fieldChowSituation k) sA sB e r)
    (x' : Correspondence (fieldChowSituation k) sA' sB' e' r') :
    tensorBlock k sP sP' sQ sQ' (canonicalDiagonalClassFamily k) hP hP' hQ hQ' r r'
        (prodHomPushforward sP sQ sA sB iA iB hiA hiB e r x)
        (prodHomPushforward sP' sQ' sA' sB' iA' iB' hiA' hiB' e' r' x') =
      prodHomPushforward (prodBase sP sP') (prodBase sQ sQ') (prodBase sA sA') (prodBase sB sB')
        (prodHom sP sP' sA sA' iA iA' hiA hiA') (prodHom sQ sQ' sB sB' iB iB' hiB hiB')
        (prodHom_comp_prodBase sP sP' sA sA' iA iA' hiA hiA')
        (prodHom_comp_prodBase sQ sQ' sB sB' iB iB' hiB hiB') ((e + e' : ℕ) : ℤ) (r + r')
        (tensorBlock k sA sA' sB sB' (canonicalDiagonalClassFamily k) hA hA' hB hB' r r' x x') :=
  tensorBlock_prodHomPushforward iA iB hiA hiB iA' iB' hiA' hiB'
    (canonicalDiagonalClassFamily_projectionFormula k) hA hA' hB hB' hP hP' hQ hQ' r r' x x'

end Clopen

end Stacks.WeilCohomology
