module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.UniversalDivisor
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGenericMember
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic

/-!
# The universal divisor is a family of degree `deg L`

The universal divisor `𝒟 ⊆ X ×_k Q` of `Stacks.LinearSystemScheme.universalDivisor`, with
`Q = Proj k[T₀, …, Tₙ]`, pulls back along every `k`-morphism `T ⟶ Q` to a closed subscheme of
`X ×_k T` that is finite locally free of rank `deg L` over `T` and an effective Cartier divisor,
so it is a degree-`deg L` Hilbert family.
Along a morphism landing in a chart `D₊(Tⱼ)`, this pullback is the divisor of the coordinate
section given by the chart coordinates.

## Main definitions

* `Stacks.LinearSystemScheme.familyOf`: the pullback of `𝒟` along a `k`-morphism `T ⟶ Q`.

## Main results

* `Stacks.LinearSystemScheme.isPullback_familyBaseChangeMap`: `X ×_k T` is the base change of
  `X ×_k T'` along `T ⟶ T'`.
* `Stacks.LinearSystemScheme.familyOf_of_chart`: the pullback of `𝒟` along a morphism landing in
  `D₊(Tⱼ)` is the divisor of the coordinate section given by the chart coordinates.
* `Stacks.LinearSystemScheme.isFiniteLocallyFreeOfRank_familyOf`: the pullback of `𝒟` along any
  `k`-morphism `T ⟶ Q` is finite locally free of rank `deg L` over `T`.
* `Stacks.LinearSystemScheme.isEffectiveCartierDivisor_familyOf`: this pullback is an effective
  Cartier divisor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite HomogeneousLocalization
open AlgebraicGeometry.Proj Stacks.AlgebraicGeometry.SectionsBaseChange Stacks.Hilbert

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.LinearSystemScheme

/-- `X ×_S T` is the base change of `X ×_S T'` along `g : T ⟶ T'`. -/
theorem isPullback_familyBaseChangeMap {S : Scheme.{u}} (Y : Over S) {T T' : Over S}
    (g : T ⟶ T') :
    IsPullback (familyBaseChangeMap Y g) (pullback.snd Y.hom T.hom) (pullback.snd Y.hom T'.hom)
      g.left := by
  refine IsPullback.of_right ?_ (familyBaseChangeMap_comp_snd _ _) (IsPullback.of_hasPullback _ _)
  rw [familyBaseChangeMap_comp_fst]
  exact (IsPullback.of_hasPullback Y.hom T.hom).flip.flip |>.of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] {n : ℕ}
  (w : letI := baseModule f L ⊤; Module.Basis (Fin (n + 1)) Γ(Spec (.of k), ⊤) Γ(L, ⊤))

/-- The chart coordinates of the inclusion of the chart `D₊(Tⱼ)` into `Q` are the standard chart
functions `Tᵢ / Tⱼ`. -/
theorem chartCoords_awayι (j : Fin (n + 1)) :
    chartCoords (awayι (coordGrading k n) (MvPolynomial.X j) (X_mem_coordGrading j) one_pos) j
      (awayι_preimage_basicOpen_self one_pos (X_mem_coordGrading j)) = chartFun k j := by
  funext i
  simp only [chartCoords, awayToSection_comp_awayι_appLE one_pos (X_mem_coordGrading j)]
  rfl

/-- The universal divisor pulled back along a `k`-morphism `g : T ⟶ Q`. -/
def familyOf {T : Over (Spec (.of k))} (g : T ⟶ projOver k (n := n)) :
    ((Over.pullback T.hom).obj (curveOver f)).left.IdealSheafData :=
  (universalDivisor k f L w).comap (familyBaseChangeMap (curveOver f) g)

/-- Pulling back the universal divisor along `h ≫ g` is pulling back along `g`, then along the base
change of `h`. -/
theorem familyOf_comp {T T' : Over (Spec (.of k))} (h : T' ⟶ T) (g : T ⟶ projOver k (n := n)) :
    familyOf k f L w (h ≫ g) =
      (familyOf k f L w g).comap (familyBaseChangeMap (curveOver f) h) := by
  rw [familyOf, familyOf, familyBaseChangeMap_comp, Scheme.IdealSheafData.comap_comp]

/-- **The universal divisor along a morphism into a chart.** If `g : T ⟶ Q` lands in `D₊(Tⱼ)`,
its pullback of `𝒟` is the divisor of the coordinate section given by the chart coordinates of
`g`. -/
theorem familyOf_of_chart {T : Over (Spec (.of k))} (g : T ⟶ projOver k (n := n))
    (j : Fin (n + 1)) (hg : g.left ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X j) = ⊤) :
    familyOf k f L w g = coordDivisor k f L w T.hom (chartCoords g.left j hg) := by
  let lam : T ⟶ chartOver k j :=
    Over.homMk (chartLift one_pos (X_mem_coordGrading j) g.left hg) (by
      simp only [Over.mk_hom, chartLift_comp_awayι_assoc]
      exact Over.w g)
  have e : g = lam ≫ chartHom k j := by
    ext
    simp [lam]
  have hc : chartCoords g.left j hg =
      fun i => lam.left.appTop (chartFun k j i) := by
    have hl : lam.left ≫ awayι (coordGrading k n) (MvPolynomial.X j) (X_mem_coordGrading j)
        one_pos = g.left := chartLift_comp_awayι _ _ _ hg
    have hg' : (lam.left ≫ awayι (coordGrading k n) (MvPolynomial.X j) (X_mem_coordGrading j)
        one_pos) ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X j) = ⊤ := by rwa [hl]
    funext i
    rw [chartCoords_congr hl.symm j hg hg', chartCoords_comp lam.left _ j
      (awayι_preimage_basicOpen_self one_pos (X_mem_coordGrading j)) hg', chartCoords_awayι]
  rw [hc, familyOf]
  conv_lhs => rw [e, familyBaseChangeMap_comp, Scheme.IdealSheafData.comap_comp,
    comap_chartMap_universalDivisor, pieceDivisor, coordDivisor]
  refine (comap_zeroScheme_coordSection L w _ _ _ _).trans ?_
  have hs : familyBaseChangeMap (curveOver f) lam ≫ pullback.snd f (chartOver k j).hom =
      pullback.snd f T.hom ≫ lam.left := familyBaseChangeMap_comp_snd _ _
  rw [coordDivisor, hs, coordSection_comp]
  clear hc
  have hf : familyBaseChangeMap (curveOver f) lam ≫ pullback.fst f (chartOver k j).hom =
      pullback.fst f T.hom := familyBaseChangeMap_comp_fst _ _
  revert hf
  generalize familyBaseChangeMap (curveOver f) lam ≫ pullback.fst f (chartOver k j).hom = P
  rintro rfl
  rfl

/-- The preimages of the standard charts cover the source of a morphism into `Q`. -/
theorem iSup_preimage_basicOpen_X {T : Scheme.{u}} (g : T ⟶ Proj (coordGrading k n)) :
    ⨆ i : Fin (n + 1), g ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X i) = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, Stacks.ProjectiveSpace.iSup_basicOpen_X_eq_top]
  simp

/-- The chart open `g⁻¹ D₊(Tᵢ)` as a `k`-scheme mapping to `T`. -/
abbrev chartPreimageHom {T : Over (Spec (.of k))} (g : T ⟶ projOver k (n := n)) (i : Fin (n + 1)) :
    restrictOver (g.left ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X i)).ι ⟶ T :=
  restrictHom (g.left ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X i)).ι

/-- If `V ⊆ g⁻¹ D₊(Tᵢ)`, then the composite of `g` with the inclusion of `V` maps into `D₊(Tᵢ)`. -/
private theorem preimage_restrictHom_eq_top {T : Over (Spec (.of k))}
    (g : T ⟶ projOver k (n := n)) (i : Fin (n + 1)) {V : T.left.Opens}
    (hV : V ≤ g.left ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X i)) :
    (restrictHom V.ι ≫ g).left ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X i) = ⊤ := by
  rw [Over.comp_left, Scheme.Hom.comp_preimage]
  exact eq_top_iff.mpr fun x _ => hV x.2

/-- The composite of `g` with the inclusion of `g⁻¹ D₊(Tᵢ)` maps entirely into `D₊(Tᵢ)`. -/
theorem preimage_chartPreimageHom {T : Over (Spec (.of k))} (g : T ⟶ projOver k (n := n))
    (i : Fin (n + 1)) :
    (chartPreimageHom k g i ≫ g).left ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X i) = ⊤ :=
  preimage_restrictHom_eq_top k g i le_rfl

/-- The universal divisor along `g`, restricted to an open `V` mapping into the chart `D₊(Tᵢ)`, is
the divisor of the coordinate section given by the chart coordinates. -/
private theorem comap_familyOf_restrictHom {T : Over (Spec (.of k))}
    (g : T ⟶ projOver k (n := n)) (i : Fin (n + 1)) {V : T.left.Opens}
    (hpre : (restrictHom V.ι ≫ g).left ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X i) = ⊤) :
    (familyOf k f L w g).comap (familyBaseChangeMap (curveOver f) (restrictHom V.ι)) =
      coordDivisor k f L w (restrictOver V.ι).hom (chartCoords _ i hpre) := by
  rw [← familyOf_comp, familyOf_of_chart k f L w _ i hpre]

/-- The universal divisor along `g`, restricted to the chart open `g⁻¹ D₊(Tᵢ)`, is the divisor of
the coordinate section given by the chart coordinates. -/
theorem comap_familyOf_chartPreimageHom {T : Over (Spec (.of k))} (g : T ⟶ projOver k (n := n))
    (i : Fin (n + 1)) :
    (familyOf k f L w g).comap (familyBaseChangeMap (curveOver f) (chartPreimageHom k g i)) =
      coordDivisor k f L w (restrictOver (g.left ⁻¹ᵁ basicOpen (coordGrading k n)
        (MvPolynomial.X i)).ι).hom
        (chartCoords (chartPreimageHom k g i ≫ g).left i (preimage_chartPreimageHom k g i)) :=
  comap_familyOf_restrictHom k f L w g i _

/-- **An invertible module is the invertible sheaf of the zero scheme of a section cutting out an
effective Cartier divisor.** -/
theorem nonempty_invertibleSheaf_zeroScheme_iso {Y : Scheme.{u}} (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M] (σ : Γ(M, ⊤))
    (hσ : Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme Y M σ)) :
    Nonempty (Stacks.Divisors.invertibleSheaf' (zeroScheme Y M σ) ≅ M) := by
  have hreg := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection Y M
    (Stacks.Divisors.sectionsOfTop M σ)).mp (by
      rwa [Stacks.Divisors.sectionsOfTop_eval_top])
  have e := (invertibleSheafIsoZeroSchemeOfIsRegularSection M _ hreg).symm
  rw [Stacks.Divisors.sectionsOfTop_eval_top] at e
  exact ⟨e⟩

variable [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]

/-- **The universal divisor along any `k`-morphism `T ⟶ Q` is finite locally free of rank
`deg L` over `T`.** -/
theorem isFiniteLocallyFreeOfRank_familyOf {T : Over (Spec (.of k))} (g : T ⟶ projOver k (n := n))
    (hdim : topologicalKrullDim X ≤ 1) {d : ℕ}
    (hd : @invertibleCurveDegree k _ X f _ hdim L
      ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L› = d) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((familyOf k f L w g).subschemeι ≫ pullback.snd f T.hom) d := by
  rw [← Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property_iff]
  let 𝒰 : T.left.OpenCover := T.left.openCoverOfIsOpenCover
    (fun i : Fin (n + 1) => g.left ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X i))
    (iSup_preimage_basicOpen_X k g.left)
  refine IsZariskiLocalAtTarget.of_openCover 𝒰 fun (i : Fin (n + 1)) => ?_
  set U := g.left ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X i)
  have hB := isFiniteLocallyFreeOfRank_coordDivisor k f L w (restrictOver U.ι).hom
    (chartCoords (chartPreimageHom k g i ≫ g).left i (preimage_chartPreimageHom k g i))
    (span_range_chartCoords _ _ _) hdim hd
  have hB' : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (((familyOf k f L w g).comap (familyBaseChangeMap (curveOver f)
        (chartPreimageHom k g i))).subschemeι ≫ pullback.snd f (restrictOver U.ι).hom) d := by
    simp only [U] at hB ⊢
    rwa [comap_familyOf_chartPreimageHom k f L w g i]
  have hsq : IsPullback _ (((familyOf k f L w g).comap (familyBaseChangeMap (curveOver f)
        (chartPreimageHom k g i))).subschemeι ≫ pullback.snd f (restrictOver U.ι).hom)
      ((familyOf k f L w g).subschemeι ≫ pullback.snd f T.hom) U.ι :=
    IsPullback.paste_vert
      (Stacks.Bertini.isPullback_subschemeι_comap (familyOf k f L w g)
        (familyBaseChangeMap (curveOver f) (chartPreimageHom k g i))).flip
      (isPullback_familyBaseChangeMap (curveOver f) (chartPreimageHom k g i))
  show (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property d)
    (pullback.snd ((familyOf k f L w g).subschemeι ≫ pullback.snd f T.hom) U.ι)
  rwa [← (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property d).cancel_left_of_respectsIso
      hsq.isoPullback.hom, hsq.isoPullback_hom_snd]

/-- The universal divisor along any `k`-morphism `T ⟶ Q` is an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_familyOf {T : Over (Spec (.of k))} (g : T ⟶ projOver k (n := n))
    (hdim : topologicalKrullDim X ≤ 1) {d : ℕ}
    (hd : @invertibleCurveDegree k _ X f _ hdim L
      ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L› = d) :
    Stacks.Divisors.IsEffectiveCartierDivisor (familyOf k f L w g) := by
  have := isFiniteLocallyFreeOfRank_familyOf k f L w g hdim hd
  have : Stacks.Morphisms.IsFiniteLocallyFree
      ((familyOf k f L w g).subschemeι ≫ pullback.snd f T.hom) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d
  have : SmoothOfRelativeDimension 1 f := Stacks.Hilbert.smoothOfRelativeDimension_one_of_isCurve f
  have : SmoothOfRelativeDimension 1 (pullback.snd f T.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
      (IsPullback.of_hasPullback f T.hom) ‹_›
  exact (isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree (pullback.snd f T.hom) _).1

/-- **The universal divisor along any `k`-morphism `T ⟶ Q` has invertible sheaf locally
isomorphic to `pr_X^* L`**, on affine opens. -/
theorem isLocallyIso_familyOf {T : Over (Spec (.of k))} (g : T ⟶ projOver k (n := n))
    (hdim : topologicalKrullDim X ≤ 1) {d : ℕ}
    (hd : @invertibleCurveDegree k _ X f _ hdim L
      ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L› = d)
    (t : T.left) :
    ∃ V : T.left.Opens, IsAffineOpen V ∧ t ∈ V ∧
      Nonempty ((Scheme.Modules.pullback
          (familyBaseChangeMap (curveOver f) (restrictHom V.ι))).obj
            (Stacks.Divisors.modulesInvertibleSheaf (familyOf k f L w g)) ≅
        (Scheme.Modules.pullback (pullback.fst f (V.ι ≫ T.hom))).obj L) := by
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1),
      t ∈ g.left ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X i) := by
    have : t ∈ (⊤ : T.left.Opens) := trivial
    rw [← iSup_preimage_basicOpen_X k g.left] at this
    exact TopologicalSpace.Opens.mem_iSup.mp this
  obtain ⟨_, ⟨V₀, hV, rfl⟩, htV, hVle⟩ := T.left.isBasis_affineOpens.exists_subset_of_mem_open hi
    (g.left ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X i)).isOpen
  let V : T.left.Opens := V₀
  refine ⟨V, hV, htV, ?_⟩
  have hpre := preimage_restrictHom_eq_top k g i hVle
  have hΦ := isEffectiveCartierDivisor_familyOf k f L w g hdim hd
  have : IsOpenImmersion (familyBaseChangeMap (curveOver f) (restrictHom V.ι)) :=
    MorphismProperty.of_isPullback (isPullback_familyBaseChangeMap (curveOver f)
      (restrictHom V.ι)).flip (inferInstanceAs (IsOpenImmersion V.ι))
  have hpd : Stacks.Divisors.IsPullbackDefined (familyBaseChangeMap (curveOver f) (restrictHom V.ι))
      (familyOf k f L w g) :=
    Stacks.Divisors.isPullbackDefined_of_flat _ _ hΦ
  have e1 := Stacks.Divisors.invertibleSheafPullbackIso
    (familyBaseChangeMap (curveOver f) (restrictHom V.ι)) (familyOf k f L w g)
  have hc := comap_familyOf_restrictHom k f L w g i hpre
  obtain ⟨e2⟩ := nonempty_invertibleSheaf_zeroScheme_iso _ _
    (isEffectiveCartierDivisor_coordDivisor k f L w (restrictOver V.ι).hom
      (chartCoords _ i hpre) (span_range_chartCoords _ _ _))
  exact ⟨e1 ≪≫ eqToIso (by rw [hc]; rfl) ≪≫ e2⟩

end Stacks.LinearSystemScheme

end
