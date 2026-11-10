module

public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.Dimension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ChowGroupsOfMotives
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CorrespondenceMonoidal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionClassCodimension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Duality
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.BasePoint
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GraphAction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The name of a correspondence under the self-duality of Stacks 0FGI

Let `k` be a field and let `X`, `Y` be smooth projective schemes over `k`, equidimensional of
dimensions `d` and `e`. Stacks 0FGI makes `h(X)(d)` a dual of `h(X)`, with unit
`η = [Δ] ∈ Corr^d(Spec k, X × X)`. Under that duality a correspondence `c ∈ Corrʳ(X, Y)`, a
morphism `X ⟶ Y` of the category of correspondences, has the *name*
`η ≫ (X ◁ c) : 𝟏 ⟶ X ⊗ Y`. This file shows that the name of `c` is `c` itself: the same Chow class
`c ∈ CH_{e-r}(X × Y) ⊗ ℚ`, read as a correspondence from `Spec k` to `X × Y`. This is the
computation behind the proof of Stacks 0FHM.

## Main definitions

* `Stacks.WeilCohomology.pointCorrespondenceEquiv`: a correspondence `c ∈ CH_{e-r}(X × Y) ⊗ ℚ`
  read in `CH_{m-n}(Spec k × (X × Y)) ⊗ ℚ`, along `Spec k × (X × Y) ≅ X × Y`.
* `Stacks.WeilCohomology.correspondenceNameEquiv`: the tautological identification
  `Corrʳ(X, Y) = Corr^{d+r}(Spec k, X × Y)` of smooth projective schemes.
* `Stacks.WeilCohomology.corrToCodimChow`: the identification
  `Corrʳ(X, Y) = CH_{e-r}(X × Y) ⊗ ℚ = CH^{d+r}(X × Y) ⊗ ℚ`, with the codimension grading of
  Section 0FFZ.

## Main results

* `Stacks.WeilCohomology.dualityUnit_comp_whiskerLeft_of`: `η ≫ (X ◁ c)` is the tautological
  point correspondence `correspondenceNameEquiv c` of `c`.
* `Stacks.WeilCohomology.correspondenceNameEquiv_eq_pointCorrEquiv`: the tautological point
  correspondence of `c` is the correspondence which Stacks 0FG0 (3) attaches to the class
  `corrToCodimChow c ∈ CH^{d+r}(X × Y) ⊗ ℚ`.
* `Stacks.WeilCohomology.dualityUnit_comp_whiskerLeft_of_eq_pointCorrEquiv`: hence
  `η ≫ (X ◁ c) = pointCorrEquiv (X ⊗ Y) (d + r) (corrToCodimChow c)`.
* `Stacks.WeilCohomology.corrToCodimChow_tmul`: on an integral class `α ∈ CH_{e-r}(X × Y)`,
  `corrToCodimChow` is the class of `α` read in codimension `d + r`
  (`Stacks.WeilCohomology.chowGroupToCodimension`), through
  `Stacks.WeilCohomology.codimensionToCodimChow`.

## Implementation notes

`η ≫ (X ◁ c)` is the composite `([Δ_X] ⊗ c) ∘ [Δ]` of the class of the diagonal
`x ↦ (⋆, (x, x))` in `Spec k × (X × X)` with the tensor product `[Δ_X] ⊗ c` on
`(X × X) × (X × Y)`. The class `c` is a general rational Chow class, so the computation is reduced,
by linearity and `Stacks.Chow.cycleGroup_addMonoidHom_ext`, to the class `[V]` of an integral
closed subscheme `V ⊆ X × Y`. Then `[Δ_X] ⊗ [V]` is the class of `X ×_k V`
(`Stacks.WeilCohomology.tensorInt_closedSubscheme_of_isIntegral`), and the composition is the proper
intersection `pr₁₂⁻¹(Δ) ∩ pr₂₃⁻¹(X ×_k V) = Δ ×_{X × X} (X ×_k V) ≅ V`
(`Stacks.WeilCohomology.compositionInt_pointDiagonal_diagonalTensorEmbedding`), computed by the
proper-intersection formula of Stacks 0FFD for the canonical diagonal classes: its points of the
expected dimension lie over the generic point of `V`, where all local rings involved are
Cohen–Macaulay.

## References

* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
* [Stacks Project, Tag 0FGI](https://stacks.math.columbia.edu/tag/0FGI)
* [Stacks Project, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0)
* [Stacks Project, Tag 0FFD](https://stacks.math.columbia.edu/tag/0FFD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-- Along a flat morphism `g : P ⟶ T` of relative dimension `r`, the irreducible components of `P`
have delta-dimension `m + r` for any structure morphism `p = g ≫ q`, if those of `T` have `m`. -/
private theorem deltaDimension_irreducibleComponent_of_comp_flat {C : ChowSituation.{u}}
    {P T : Scheme.{u}} (g : P ⟶ T) [LocallyOfFiniteType g] [Flat g] (q : T ⟶ C.S)
    [LocallyOfFiniteType q] (r : ℕ) (hg : RelativeDimension g r) {m : ℤ}
    (hT : ∀ V : irreducibleComponents T,
      deltaDimension C q ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = m)
    {p : P ⟶ C.S} [LocallyOfFiniteType p] (h : p = g ≫ q) (W : irreducibleComponents P) :
    deltaDimension C p ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents _ W.2⟩ = m + r :=
  (deltaDimension_congr h _).trans (deltaDimension_irreducibleComponent_of_flat g q r hg hT W)

section Formula

variable (k : Type u) [Field k] {X X' Y Y' : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sX' : X' ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) (sY' : Y' ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] [LocallyOfFiniteType sY]
  [LocallyOfFiniteType sY'] [Smooth sX] [Smooth sX'] [Smooth sY] [Smooth sY']
  [IsSeparated sX] [IsSeparated sX'] [IsSeparated sY] [IsSeparated sY']

/-- **`[A] ⊗ [V] = [A ×_k V]` for `A` smooth and `V` integral.** Let `a : A ⟶ X × Y` and
`a' : V ⟶ X' × Y'` be closed immersions, with `A` smooth over `k` of constant dimension `e - r` and
`V` integral of dimension `e' - r'`. Then, for the canonical family of diagonal classes, the tensor
product `pr₁₃^*[A] · pr₂₄^*[V]` of their classes is the class of `A ×_k V` embedded in
`(X × X') × (Y × Y')`. The intersection `pr₁₃⁻¹(A) ∩ pr₂₄⁻¹(V) = A ×_k V` is smooth over `V`, so
its points of the expected dimension lie over the generic point of `V`, where all local rings
involved are Cohen–Macaulay. -/
theorem tensorInt_closedSubscheme_of_isIntegral {d d' e e' : ℕ} (hX : RelativeDimension sX d)
    (hX' : RelativeDimension sX' d') (hY : RelativeDimension sY e)
    (hY' : RelativeDimension sY' e') (r r' : ℤ) {A A' : Scheme.{u}}
    (a : A ⟶ Limits.pullback sX sY) [IsClosedImmersion a]
    (a' : A' ⟶ Limits.pullback sX' sY') [IsClosedImmersion a'] [IsIntegral A']
    {qA : A ⟶ (fieldChowSituation k).S} {qA' : A' ⟶ (fieldChowSituation k).S}
    [Smooth qA] [LocallyOfFiniteType qA'] (hqA : a ≫ prodBase sX sY = qA)
    (hqA' : a' ≫ prodBase sX' sY' = qA') {nA : ℕ} (hA : RelativeDimension qA nA)
    (hnA : (nA : ℤ) = e - r)
    (hA' : schemeDeltaDimension (fieldChowSituation k) qA' = (((e' : ℤ) - r' : ℤ) : EInt)) :
    haveI := isClosedImmersion_tensorEmbedding sX sX' sY sY' a a' hqA hqA'
    tensorInt k sX sX' sY sY' (canonicalDiagonalClassFamily k) hX hX' hY hY' r r'
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX sY) a ((e : ℤ) - r)))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX' sY') a' ((e' : ℤ) - r'))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (tensorBase sX sX' sY sY') (tensorEmbedding sX sX' sY sY' a a' hqA hqA')
        (((e + e' : ℕ) : ℤ) - (r + r'))) := by
  have := isClosedImmersion_tensorEmbedding sX sX' sY sY' a a' hqA hqA'
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian qA
  have : IsLocallyNoetherian A' := LocallyOfFiniteType.isLocallyNoetherian qA'
  set i₁ := pullback.fst (tensorPr₁₃ sX sX' sY sY') a
  set i₂ := pullback.fst (tensorPr₂₄ sX sX' sY sY') a'
  have hgen : relativeDimension (fieldChowSituation k).dimensionFunction qA'
      (genericPoint A') = (e' : ℤ) - r' := by
    have h := hA'
    rw [schemeDeltaDimension_eq_genericPoint] at h
    exact WithBotTop.coe_injective h
  have hAc : ∀ T : irreducibleComponents A, deltaDimension (fieldChowSituation k)
      (a ≫ prodBase sX sY) ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ =
        (e : ℤ) - r := fun T ↦ (deltaDimension_congr hqA _).trans
    (deltaDimension_irreducibleComponent_of_relativeDimension_eq k _ hA hnA T)
  have hAc'' : ∀ T : irreducibleComponents A', deltaDimension (fieldChowSituation k) qA'
      ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ = (e' : ℤ) - r' :=
    deltaDimension_irreducibleComponent_of_irreducibleSpace qA' hA'
  have hAc' : ∀ T : irreducibleComponents A', deltaDimension (fieldChowSituation k)
      (a' ≫ prodBase sX' sY') ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ =
        (e' : ℤ) - r' := fun T ↦ (deltaDimension_congr hqA' _).trans (hAc'' T)
  have h₁ : ∀ T : irreducibleComponents (Limits.pullback (tensorPr₁₃ sX sX' sY sY') a :
      Scheme.{u}), deltaDimension (fieldChowSituation k) (i₁ ≫ tensorBase sX sX' sY sY')
        ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ =
          (e : ℤ) - r + ((e' + d' : ℕ) : ℤ) := by
    exact deltaDimension_irreducibleComponent_of_comp_flat _ _ (e' + d')
      (relativeDimension_pullback_snd _ a _ (relativeDimension_tensorPr₁₃ k sX sX' sY sY' hX' hY'))
      hAc (by rw [← pullback.condition_assoc, tensorPr₁₃_comp_prodBase])
  have h₂ : ∀ T : irreducibleComponents (Limits.pullback (tensorPr₂₄ sX sX' sY sY') a' :
      Scheme.{u}), deltaDimension (fieldChowSituation k) (i₂ ≫ tensorBase sX sX' sY sY')
        ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ =
          (e' : ℤ) - r' + ((e + d : ℕ) : ℤ) := by
    exact deltaDimension_irreducibleComponent_of_comp_flat _ _ (e + d)
      (relativeDimension_pullback_snd _ a' _ (relativeDimension_tensorPr₂₄ k sX sX' sY sY' hX hY))
      hAc' (by rw [← pullback.condition_assoc, tensorPr₂₄_comp_prodBase])
  set φ := tensorIntersectionIso sX sX' sY sY' a a' hqA hqA' with hφ
  have hmor : pullback.fst i₁ i₂ ≫ i₁ ≫ tensorBase sX sX' sY sY' =
      φ.hom ≫ prodBase qA qA' := by
    rw [← Category.assoc, ← tensorIntersectionIso_hom_tensorEmbedding, Category.assoc,
      tensorEmbedding_tensorBase]
  have hsnd : prodBase qA qA' = pullback.snd qA qA' ≫ qA' := pullback.condition
  have hrel : RelativeDimension (pullback.snd qA qA') nA := relativeDimension_pullback_snd _ _ _ hA
  have hPc : ∀ T : irreducibleComponents (Limits.pullback qA qA' : Scheme.{u}),
      deltaDimension (fieldChowSituation k) (prodBase qA qA')
        ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ =
          (e' : ℤ) - r' + nA :=
    deltaDimension_irreducibleComponent_of_comp_flat _ qA' nA hrel hAc'' hsnd
  have h₃ : schemeDeltaDimension (fieldChowSituation k)
      (pullback.fst i₁ i₂ ≫ i₁ ≫ tensorBase sX sX' sY sY') ≤
        ((((e + e' : ℕ) : ℤ) - (r + r') : ℤ) : EInt) := by
    rw [schemeDeltaDimension_congr _ hmor, schemeDeltaDimension_comp_iso]
    refine (schemeDeltaDimension_le_of_forall_irreducibleComponent _ hPc).trans_eq ?_
    congr 1
    push_cast
    omega
  have h₄ : Intersection.CohenMacaulayAtIntersection k (tensorBase sX sX' sY sY') i₁ i₂
      (((e + e' : ℕ) : ℤ) - (r + r')) := by
    intro ζ hζ
    have hpt : (pullback.snd (tensorPr₂₄ sX sX' sY sY') a').base
        ((pullback.snd i₁ i₂).base ζ) = (pullback.snd qA qA').base (φ.hom.base ζ) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hφ]
      change _ = (tensorIntersectionHom sX sX' sY sY' a a' hqA hqA' ≫ pullback.snd qA qA').base ζ
      rw [tensorIntersectionHom, pullback.lift_snd]
    have hζ' : relativeDimension (fieldChowSituation k).dimensionFunction
        (pullback.snd qA qA' ≫ qA') (φ.hom.base ζ) = (e : ℤ) - r + ((e' : ℤ) - r') := by
      rw [← relativeDimension_comp_closedImmersion, ← hsnd, ← hmor]
      refine hζ.trans ?_
      push_cast
      ring
    have hle := SectionZeroScheme.relativeDimension_comp_le_add (fieldChowSituation k) qA'
      (pullback.snd qA qA') nA hrel (φ.hom.base ζ)
    have hge := relativeDimension_le_of_schemeDeltaDimension_le' (fieldChowSituation k) qA'
      hA'.le ((pullback.snd qA qA').base (φ.hom.base ζ))
    have hv : relativeDimension (fieldChowSituation k).dimensionFunction qA'
        ((pullback.snd qA qA').base (φ.hom.base ζ)) =
          relativeDimension (fieldChowSituation k).dimensionFunction qA' (genericPoint A') := by
      rw [hgen]
      omega
    refine ⟨isCohenMacaulayLocalRing_stalk_of_smooth_of_isCohenMacaulayLocalRing k
        (pullback.snd (tensorPr₁₃ sX sX' sY sY') a) qA _
        (isCohenMacaulayLocalRing_stalk_of_smooth k qA _),
      isCohenMacaulayLocalRing_stalk_of_smooth_of_isCohenMacaulayLocalRing k
        (pullback.snd (tensorPr₂₄ sX sX' sY sY') a') qA' _ ?_⟩
    rw [hpt]
    exact isCohenMacaulayLocalRing_stalk_of_relativeDimension_eq k qA' hv
  simp only [tensorInt, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
    AddMonoidHom.coe_toIntLinearMap, LinearEquiv.coe_coe, AddEquiv.coe_toIntLinearEquiv]
  rw [flatPullbackChow_mk_cycleAssociatedToClosedSubscheme (tensorBase sX sX' sY sY')
      (prodBase sX sY) (tensorPr₁₃ sX sX' sY sY') (tensorPr₁₃_comp_prodBase sX sX' sY sY')
      (e' + d') (relativeDimension_tensorPr₁₃ k sX sX' sY sY' hX' hY') a _
      (schemeDeltaDimension_le_of_forall_irreducibleComponent _ hAc),
    flatPullbackChow_mk_cycleAssociatedToClosedSubscheme (tensorBase sX sX' sY sY')
      (prodBase sX' sY') (tensorPr₂₄ sX sX' sY sY') (tensorPr₂₄_comp_prodBase sX sX' sY sY')
      (e + d) (relativeDimension_tensorPr₂₄ k sX sX' sY sY' hX hY) a' _
      (schemeDeltaDimension_le_of_forall_irreducibleComponent _ hAc')]
  refine (canonicalDiagonalClassFamily_properIntersectionFormula k (tensorBase sX sX' sY sY') _
    (relativeDimension_tensorBase k sX sX' sY sY' hX hX' hY hY') i₁ i₂ _ _ _ _ h₁ h₂ h₃
    h₄).trans ?_
  rw [cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _ φ
    (tensorIntersectionIso_hom_tensorEmbedding sX sX' sY sY' a a' hqA hqA')]

end Formula

section Unit

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)

/-- The diagonal `x ↦ (⋆, (x, x))` of `X`, as a morphism to `Spec k × (X × X)`. -/
def pointDiagonal : X ⟶ Limits.pullback (𝟙 (fieldChowSituation k).S) (prodBase sX sX) :=
  pullback.lift sX (pullback.diagonal sX) (by
    rw [Category.comp_id, prodBase, pullback.diagonal_fst_assoc])

theorem pointDiagonal_fst :
    pointDiagonal k sX ≫ pullback.fst (𝟙 (fieldChowSituation k).S) (prodBase sX sX) = sX :=
  pullback.lift_fst _ _ _

theorem pointDiagonal_snd :
    pointDiagonal k sX ≫ pullback.snd (𝟙 (fieldChowSituation k).S) (prodBase sX sX) =
      pullback.diagonal sX :=
  pullback.lift_snd _ _ _

theorem pointDiagonal_prodBase :
    pointDiagonal k sX ≫ prodBase (𝟙 (fieldChowSituation k).S) (prodBase sX sX) = sX := by
  change pointDiagonal k sX ≫ pullback.fst _ _ ≫ 𝟙 _ = sX
  rw [← Category.assoc, pointDiagonal_fst, Category.comp_id]

variable {k sX sY} in
/-- A closed subscheme `i : V ⟶ X × Y`, read in `Spec k × (X × Y)`: `v ↦ (⋆, i v)`. -/
def pointLift {V : Scheme.{u}} (i : V ⟶ Limits.pullback sX sY) :
    V ⟶ Limits.pullback (𝟙 (fieldChowSituation k).S) (prodBase sX sY) :=
  pullback.lift (i ≫ prodBase sX sY) i (Category.comp_id _)

variable {k sX sY} in
theorem pointLift_snd {V : Scheme.{u}} (i : V ⟶ Limits.pullback sX sY) :
    pointLift i ≫ pullback.snd (𝟙 (fieldChowSituation k).S) (prodBase sX sY) = i :=
  pullback.lift_snd _ _ _

variable {k sX sY} in
theorem pointLift_prodBase {V : Scheme.{u}} (i : V ⟶ Limits.pullback sX sY) :
    pointLift i ≫ prodBase (𝟙 (fieldChowSituation k).S) (prodBase sX sY) = i ≫ prodBase sX sY := by
  change pointLift i ≫ pullback.fst _ _ ≫ 𝟙 _ = _
  rw [pointLift, pullback.lift_fst_assoc, Category.comp_id]

variable {k sX sY} in
theorem pointLift_eq_comp_inv {V : Scheme.{u}} (i : V ⟶ Limits.pullback sX sY) :
    pointLift i = i ≫ inv (pullback.snd (𝟙 (fieldChowSituation k).S) (prodBase sX sY)) := by
  rw [IsIso.eq_comp_inv, pointLift_snd]

variable {k sX sY} in
instance isClosedImmersion_pointLift {V : Scheme.{u}} (i : V ⟶ Limits.pullback sX sY)
    [IsClosedImmersion i] : IsClosedImmersion (pointLift i) := by
  rw [pointLift_eq_comp_inv]
  infer_instance

instance isClosedImmersion_pointDiagonal [IsSeparated sX] :
    IsClosedImmersion (pointDiagonal k sX) := by
  have : IsClosedImmersion (pointDiagonal k sX ≫
      pullback.snd (𝟙 (fieldChowSituation k).S) (prodBase sX sX)) := by
    rw [pointDiagonal_snd]
    infer_instance
  exact IsClosedImmersion.of_comp _
    (pullback.snd (𝟙 (fieldChowSituation k).S) (prodBase sX sX))

variable {V : Scheme.{u}} (i : V ⟶ Limits.pullback sX sY)

/-- The class of the diagonal in the tensor product `[Δ_X] ⊗ [V]`: the closed subscheme
`X ×_k V ⟶ (X × X) × (X × Y)`, `(x, v) ↦ ((x, pr₁ v), (x, pr₂ v))`. -/
abbrev diagonalTensorEmbedding :=
  tensorEmbedding sX sX sX sY (graphMorphism sX sX (𝟙 X) (Category.id_comp sX)) i
    (show graphMorphism sX sX (𝟙 X) (Category.id_comp sX) ≫ prodBase sX sX = sX by
      rw [prodBase, ← Category.assoc, graphMorphism_fst, Category.id_comp]) rfl

/-- The projection of the fibre product `Δ ×_{X × X} (X ×_k V)` of the composition onto `V`. -/
def unitFibreProj :
    compositionFibre (pointDiagonal k sX) (diagonalTensorEmbedding k sX sY i) ⟶ V :=
  pullback.snd _ _ ≫ pullback.snd _ _

/-- The two components `x₀` and `x` of a point `(x₀, (x, v))` of the fibre product agree. -/
theorem unitFibre_fst_eq :
    pullback.fst (pointDiagonal k sX ≫ pullback.snd _ _)
        (diagonalTensorEmbedding k sX sY i ≫ pullback.fst _ _) =
      pullback.snd (pointDiagonal k sX ≫ pullback.snd _ _)
        (diagonalTensorEmbedding k sX sY i ≫ pullback.fst _ _) ≫ pullback.fst _ _ := by
  have h := pullback.condition (f := pointDiagonal k sX ≫ pullback.snd _ _)
    (g := diagonalTensorEmbedding k sX sY i ≫ pullback.fst _ _)
  calc _ = pullback.fst _ _ ≫ (pointDiagonal k sX ≫ pullback.snd _ _) ≫ pullback.fst sX sX := by
          rw [pointDiagonal_snd, pullback.diagonal_fst, Category.comp_id]
    _ = pullback.snd _ _ ≫ (diagonalTensorEmbedding k sX sY i ≫ pullback.fst _ _) ≫
          pullback.fst sX sX := by
          rw [← Category.assoc _ _ (pullback.fst sX sX), h, Category.assoc]
    _ = _ := by rw [Category.assoc, tensorEmbedding_fst_fst, graphMorphism_fst, Category.comp_id]

/-- The component `x₀` of a point `(x₀, (x, v))` of the fibre product is the first projection
of `v`. -/
theorem unitFibre_fst_eq' :
    pullback.fst (pointDiagonal k sX ≫ pullback.snd _ _)
        (diagonalTensorEmbedding k sX sY i ≫ pullback.fst _ _) =
      unitFibreProj k sX sY i ≫ i ≫ pullback.fst sX sY := by
  have h := pullback.condition (f := pointDiagonal k sX ≫ pullback.snd _ _)
    (g := diagonalTensorEmbedding k sX sY i ≫ pullback.fst _ _)
  calc _ = pullback.fst _ _ ≫ (pointDiagonal k sX ≫ pullback.snd _ _) ≫ pullback.snd sX sX := by
          rw [pointDiagonal_snd, pullback.diagonal_snd, Category.comp_id]
    _ = pullback.snd _ _ ≫ (diagonalTensorEmbedding k sX sY i ≫ pullback.fst _ _) ≫
          pullback.snd sX sX := by
          rw [← Category.assoc _ _ (pullback.snd sX sX), h, Category.assoc]
    _ = _ := by rw [Category.assoc, tensorEmbedding_fst_snd, unitFibreProj, Category.assoc]

/-- The inverse of the projection of the fibre product onto `V`: `v ↦ (pr₁ v, (pr₁ v, v))`. -/
def unitFibreSection :
    V ⟶ compositionFibre (pointDiagonal k sX) (diagonalTensorEmbedding k sX sY i) :=
  pullback.lift (i ≫ pullback.fst sX sY)
    (pullback.lift (i ≫ pullback.fst sX sY) (𝟙 V) (by rw [Category.id_comp, Category.assoc]))
    (by
      apply pullback.hom_ext
      · rw [Category.assoc, pointDiagonal_snd, pullback.diagonal_fst,
          Category.comp_id, Category.assoc, Category.assoc, tensorEmbedding_fst_fst,
          pullback.lift_fst_assoc, graphMorphism_fst, Category.comp_id]
      · rw [Category.assoc, pointDiagonal_snd, pullback.diagonal_snd,
          Category.comp_id, Category.assoc, Category.assoc, tensorEmbedding_fst_snd,
          pullback.lift_snd_assoc, Category.id_comp])

theorem unitFibreSection_proj : unitFibreSection k sX sY i ≫ unitFibreProj k sX sY i = 𝟙 V := by
  rw [unitFibreProj, unitFibreSection, pullback.lift_snd_assoc, pullback.lift_snd]

theorem unitFibreProj_section : unitFibreProj k sX sY i ≫ unitFibreSection k sX sY i = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, unitFibreSection, pullback.lift_fst, Category.id_comp]
    exact (unitFibre_fst_eq' k sX sY i).symm
  · rw [Category.assoc, unitFibreSection, pullback.lift_snd, Category.id_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← unitFibre_fst_eq', unitFibre_fst_eq]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, unitFibreProj]

instance isIso_unitFibreProj : IsIso (unitFibreProj k sX sY i) :=
  ⟨⟨unitFibreSection k sX sY i, unitFibreProj_section k sX sY i, unitFibreSection_proj k sX sY i⟩⟩

/-- The fibre product of the composition, mapped to `Spec k × (X × Y)`, is `V` embedded by
`v ↦ (⋆, i v)`. -/
theorem compositionFibre_toProduct_unit :
    compositionFibre.toProduct (pointDiagonal k sX) (diagonalTensorEmbedding k sX sY i) =
      unitFibreProj k sX sY i ≫ pointLift i := by
  apply pullback.hom_ext
  · rw [compositionFibre.toProduct, pullback.lift_fst, pointDiagonal_fst,
      Category.assoc, pointLift, pullback.lift_fst, unitFibre_fst_eq' k sX sY i, Category.assoc,
      Category.assoc]
  · rw [compositionFibre.toProduct, pullback.lift_snd, Category.assoc, pointLift_snd]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, tensorEmbedding_snd_fst, graphMorphism_snd,
        Category.comp_id, Category.assoc, ← unitFibre_fst_eq', unitFibre_fst_eq]
    · rw [Category.assoc, Category.assoc, tensorEmbedding_snd_snd, unitFibreProj, Category.assoc,
        Category.assoc]

attribute [local instance] isClosedImmersion_graphMorphism in
/-- **`([Δ_X] ⊗ [V]) ∘ [Δ_X] = [V]` on integral Chow groups.** For an integral closed subscheme
`V ⊆ X × Y` of dimension `e - r`, composing the class of the diagonal `x ↦ (⋆, (x, x))` in
`CH_d(Spec k × (X × X))` with the class of `X ×_k V ⊆ (X × X) × (X × Y)` gives the class of `V`,
read in `Spec k × (X × Y)`. The intersection `pr₁₂⁻¹(Δ) ∩ pr₂₃⁻¹(X ×_k V)` is the fibre product
`Δ ×_{X × X} (X ×_k V) ≅ V`, it has the expected dimension, and at its points of that dimension
the local rings of `Δ ≅ X` and of `X ×_k V` are Cohen–Macaulay: the first is smooth, the second is
smooth over `V` and the points lie over the generic point of `V`. -/
theorem compositionInt_pointDiagonal_diagonalTensorEmbedding [Smooth sX] [Smooth sY]
    [IsProper sX] [IsProper sY] [IsClosedImmersion i] {d e : ℕ} (hX : RelativeDimension sX d)
    (hXX : RelativeDimension (prodBase sX sX) (d + d))
    (hXY : RelativeDimension (prodBase sX sY) (d + e)) (r : ℤ) [IsIntegral V]
    (hV : schemeDeltaDimension (fieldChowSituation k) (i ≫ prodBase sX sY) =
      (((e : ℤ) - r : ℤ) : EInt)) :
    haveI := isClosedImmersion_tensorEmbedding sX sX sX sY
      (graphMorphism sX sX (𝟙 X) (Category.id_comp sX)) i
      (show graphMorphism sX sX (𝟙 X) (Category.id_comp sX) ≫ prodBase sX sX = sX by
        rw [prodBase, ← Category.assoc, graphMorphism_fst, Category.id_comp]) rfl
    compositionInt k (𝟙 (fieldChowSituation k).S) (prodBase sX sX) (prodBase sX sY)
        (canonicalDiagonalClassFamily k) (relativeDimension_identity _) hXX hXY (d : ℤ) (0 + r)
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (𝟙 (fieldChowSituation k).S) (prodBase sX sX)) (pointDiagonal k sX)
          (((d + d : ℕ) : ℤ) - d)))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (prodBase sX sX) (prodBase sX sY)) (diagonalTensorEmbedding k sX sY i)
          (((d + e : ℕ) : ℤ) - (0 + r)))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (𝟙 (fieldChowSituation k).S) (prodBase sX sY)) (pointLift i)
        (((d + e : ℕ) : ℤ) - (d + (0 + r)))) := by
  have := isClosedImmersion_tensorEmbedding sX sX sX sY
    (graphMorphism sX sX (𝟙 X) (Category.id_comp sX)) i
    (show graphMorphism sX sX (𝟙 X) (Category.id_comp sX) ≫ prodBase sX sX = sX by
      rw [prodBase, ← Category.assoc, graphMorphism_fst, Category.id_comp]) rfl
  have hκ := compositionFibre_toProduct_unit k sX sY i
  have : IsClosedImmersion (compositionFibre.toProduct (pointDiagonal k sX)
      (diagonalTensorEmbedding k sX sY i)) := by
    rw [hκ]
    infer_instance
  have hκ' : compositionFibre.toProduct (pointDiagonal k sX) (diagonalTensorEmbedding k sX sY i) ≫
      prodBase (𝟙 (fieldChowSituation k).S) (prodBase sX sY) =
        unitFibreProj k sX sY i ≫ i ≫ prodBase sX sY := by
    rw [hκ, Category.assoc, pointLift_prodBase]
  have hgen : relativeDimension (fieldChowSituation k).dimensionFunction (i ≫ prodBase sX sY)
      (genericPoint V) = (e : ℤ) - r := by
    have h := hV
    rw [schemeDeltaDimension_eq_genericPoint] at h
    exact WithBotTop.coe_injective h
  have hVc := deltaDimension_irreducibleComponent_of_irreducibleSpace _ hV
  have hsnd : diagonalTensorEmbedding k sX sY i ≫ prodBase (prodBase sX sX) (prodBase sX sY) =
      pullback.snd sX (i ≫ prodBase sX sY) ≫ i ≫ prodBase sX sY := by
    rw [← pullback.condition]
    exact tensorEmbedding_tensorBase _ _ _ _ _ _ _ _
  rw [DiagonalClassFamily.ProperIntersectionFormula.compositionInt_closedSubscheme k
    (𝟙 _) (prodBase sX sX) (prodBase sX sY)
    (canonicalDiagonalClassFamily_properIntersectionFormula k)
    (relativeDimension_identity _) hXX hXY d (0 + r)
    (pointDiagonal k sX) (diagonalTensorEmbedding k sX sY i)
    (fun T ↦ by
      rw [deltaDimension_congr (pointDiagonal_prodBase k sX),
        deltaDimension_irreducibleComponent_of_relativeDimension k sX d hX T]
      push_cast
      ring)
    (fun T ↦ by
      rw [deltaDimension_irreducibleComponent_of_comp_flat _ _ d
        (relativeDimension_pullback_snd _ _ d hX) hVc hsnd T]
      push_cast
      ring)
    (by
      rw [schemeDeltaDimension_congr _ hκ']
      refine ((schemeDeltaDimension_comp_iso _ (asIso (unitFibreProj k sX sY i)) _).trans
        hV).le.trans_eq ?_
      rw [show ((d + e : ℕ) : ℤ) - (d + (0 + r)) = (e : ℤ) - r by push_cast; ring])
    (fun x hx ↦ ⟨isCohenMacaulayLocalRing_stalk_of_smooth k sX _,
      isCohenMacaulayLocalRing_stalk_of_smooth_of_isCohenMacaulayLocalRing k
        (pullback.snd sX (i ≫ prodBase sX sY)) (i ≫ prodBase sX sY) _
        (isCohenMacaulayLocalRing_stalk_of_relativeDimension_eq k (i ≫ prodBase sX sY) (by
          rw [← Scheme.Hom.comp_apply, ← unitFibreProj, ← relativeDimension_comp_closedImmersion,
            ← hκ', hx, hgen]
          push_cast
          ring))⟩)]
  exact congrArg _ (cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _
    (asIso (unitFibreProj k sX sY i)) hκ.symm _)

end Unit

section Name

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)

/-- **The tautological point correspondence of a correspondence.** A correspondence
`c ∈ Corrʳ(X, Y) = CH_{e-r}(X × Y) ⊗ ℚ`, moved along `Spec k × (X × Y) ≅ X × Y`, is a
correspondence `Spec k ⟶ X × Y` of any degree `n` with `e - r = m - n`, where `m` is the dimension
read on the target: the same Chow class, in `CH_{m-n}(Spec k × (X × Y)) ⊗ ℚ`. -/
def pointCorrespondenceEquiv [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] {e r m n : ℤ}
    (h : e - r = m - n) :
    Correspondence (fieldChowSituation k) sX sY e r ≃ₗ[ℚ]
      Correspondence (fieldChowSituation k) (𝟙 (fieldChowSituation k).S) (prodBase sX sY) m n :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℚ ℚ)
    ((chowGroupDegreeEquiv (fieldChowSituation k) (prodBase sX sY) h).trans
      (chowGroupEquivPullbackUnitLeft (fieldChowSituation k) (prodBase sX sY)
        (m - n))).toIntLinearEquiv

theorem pointCorrespondenceEquiv_tmul [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    {e r m n : ℤ} (h : e - r = m - n) (q : ℚ)
    (α : chowGroup (fieldChowSituation k) (prodBase sX sY) (e - r)) :
    pointCorrespondenceEquiv k sX sY h (q ⊗ₜ[ℤ] α) =
      q ⊗ₜ[ℤ] chowGroupEquivPullbackUnitLeft (fieldChowSituation k) (prodBase sX sY) (m - n)
        (chowGroupDegreeEquiv (fieldChowSituation k) (prodBase sX sY) h α) :=
  rfl

variable {k sX sY} in
/-- On the class of a closed subscheme `V ⊆ X × Y`, the tautological point correspondence is the
class of `V` embedded in `Spec k × (X × Y)` by `v ↦ (⋆, v)`. -/
theorem chowGroupEquivPullbackUnitLeft_mk [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    {V : Scheme.{u}} (i : V ⟶ Limits.pullback sX sY)
    [IsClosedImmersion i] (n : ℤ) :
    chowGroupEquivPullbackUnitLeft (fieldChowSituation k) (prodBase sX sY) n
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX sY) i n)) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (𝟙 (fieldChowSituation k).S) (prodBase sX sY)) (pointLift i) n) := by
  change chowPushforwardOfIso (fieldChowSituation k) _ _ _ _ n
      (QuotientAddGroup.mk' _ (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase sX sY) i n)) = _
  rw [chowPushforwardOfIso_mk,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp,
    cycleAssociatedToClosedSubscheme_congr _ _ _ _ (pointLift_eq_comp_inv i).symm]
  rfl

variable [Smooth sX] [Smooth sY] [IsProper sX] [IsProper sY]

attribute [local instance] isClosedImmersion_graphMorphism

/-- **`([Δ_X] ⊗ c) ∘ [Δ_X]` is the tautological point correspondence of `c`, on integral Chow
groups.** For `c ∈ CH_{e-r}(X × Y)`, composing the class of the diagonal `x ↦ (⋆, (x, x))` in
`CH_d(Spec k × (X × X))` with `[Δ_X] ⊗ c ∈ CH_{(d+e)-r}((X × X) × (X × Y))` gives `c`, read in
`Spec k × (X × Y)`. -/
theorem compositionInt_pointDiagonal_tensorInt {d e : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (hXX : RelativeDimension (prodBase sX sX) (d + d))
    (hXY : RelativeDimension (prodBase sX sY) (d + e)) (r : ℤ)
    (c : chowGroup (fieldChowSituation k) (prodBase sX sY) ((e : ℤ) - r)) :
    compositionInt k (𝟙 (fieldChowSituation k).S) (prodBase sX sX) (prodBase sX sY)
        (canonicalDiagonalClassFamily k) (relativeDimension_identity _) hXX hXY (d : ℤ) (0 + r)
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (𝟙 (fieldChowSituation k).S) (prodBase sX sX)) (pointDiagonal k sX)
          (((d + d : ℕ) : ℤ) - d)))
        (tensorInt k sX sX sX sY (canonicalDiagonalClassFamily k) hX hX hX hY 0 r
          (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
            (prodBase sX sX) (graphMorphism sX sX (𝟙 X) (Category.id_comp sX)) ((d : ℤ) - 0)))
          c) =
      chowGroupEquivPullbackUnitLeft (fieldChowSituation k) (prodBase sX sY) _
        (chowGroupDegreeEquiv (fieldChowSituation k) (prodBase sX sY)
          (show (e : ℤ) - r = ((d + e : ℕ) : ℤ) - (d + (0 + r)) by push_cast; ring) c) := by
  have : CompactSpace (Limits.pullback sX sY : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (prodBase sX sY)
  induction c using QuotientAddGroup.induction_on with
  | H α =>
    have h := cycleGroup_addMonoidHom_ext
      (φ := ((compositionInt k (𝟙 (fieldChowSituation k).S) (prodBase sX sX) (prodBase sX sY)
        (canonicalDiagonalClassFamily k) (relativeDimension_identity _) hXX hXY (d : ℤ) (0 + r)
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (𝟙 (fieldChowSituation k).S) (prodBase sX sX)) (pointDiagonal k sX)
          (((d + d : ℕ) : ℤ) - d)))).toAddMonoidHom.comp
        ((tensorInt k sX sX sX sY (canonicalDiagonalClassFamily k) hX hX hX hY 0 r
          (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
            (prodBase sX sX) (graphMorphism sX sX (𝟙 X) (Category.id_comp sX))
              ((d : ℤ) - 0)))).toAddMonoidHom)).comp (QuotientAddGroup.mk' _))
      (ψ := ((chowGroupEquivPullbackUnitLeft (fieldChowSituation k) (prodBase sX sY)
          _).toAddMonoidHom.comp
        (chowGroupDegreeEquiv (fieldChowSituation k) (prodBase sX sY)
          (show (e : ℤ) - r = ((d + e : ℕ) : ℤ) - (d + (0 + r)) by
            push_cast; ring)).toAddMonoidHom).comp (QuotientAddGroup.mk' _))
      (fun x hx ↦ by
        have := isIntegral_integralComponentAt x
        have hV := schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq _ _ x hx
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, QuotientAddGroup.mk'_apply,
          LinearMap.toAddMonoidHom_coe, AddEquiv.coe_toAddMonoidHom]
        rw [tensorInt_closedSubscheme_of_isIntegral k sX sX sX sY hX hX hX hY 0 r
            (graphMorphism sX sX (𝟙 X) (Category.id_comp sX)) _
            (show graphMorphism sX sX (𝟙 X) (Category.id_comp sX) ≫ prodBase sX sX = sX by
              rw [prodBase, ← Category.assoc, graphMorphism_fst, Category.id_comp]) rfl hX
            (by simp) hV,
          compositionInt_pointDiagonal_diagonalTensorEmbedding k sX sY _ hX hXX hXY r hV,
          chowGroupDegreeEquiv_mk_cycleAssociatedToClosedSubscheme,
          chowGroupEquivPullbackUnitLeft_mk])
    exact DFunLike.congr_fun h α

omit [IsProper sX] [IsProper sY] in
/-- Transport of the tautological point correspondence along an equality of degrees. -/
theorem correspondenceCongr_pointCorrespondenceEquiv {e r m n n' : ℤ} (hn : n = n')
    (h : e - r = m - n) (h' : e - r = m - n')
    (c : Correspondence (fieldChowSituation k) sX sY e r) :
    correspondenceCongr k (𝟙 (fieldChowSituation k).S) (prodBase sX sY) hn
        (pointCorrespondenceEquiv k sX sY h c) = pointCorrespondenceEquiv k sX sY h' c := by
  subst hn
  induction c using TensorProduct.inductionOn with
  | tmul q α => rw [pointCorrespondenceEquiv_tmul, correspondenceCongr_tmul]; rfl
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **`([Δ_X] ⊗ c) ∘ [Δ_X]` is the tautological point correspondence of `c`.** For
`c ∈ Corrʳ(X, Y) = CH_{e-r}(X × Y) ⊗ ℚ`, composing the class of the diagonal
`x ↦ (⋆, (x, x))` in `Corr^d(Spec k, X × X)` with `[Δ_X] ⊗ c ∈ Corr^{0+r}(X × X, X × Y)` gives the
class `c`, read in `Spec k × (X × Y)`. -/
theorem composition_pointDiagonal_tensorBlock {d e : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (hXX : RelativeDimension (prodBase sX sX) (d + d))
    (hXY : RelativeDimension (prodBase sX sY) (d + e)) (r : ℤ)
    (c : Correspondence (fieldChowSituation k) sX sY e r) :
    composition k (𝟙 (fieldChowSituation k).S) (prodBase sX sX) (prodBase sX sY)
        (canonicalDiagonalClassFamily k) (relativeDimension_identity _) hXX hXY (d : ℤ) (0 + r)
        ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (𝟙 (fieldChowSituation k).S) (prodBase sX sX)) (pointDiagonal k sX)
          (((d + d : ℕ) : ℤ) - d)))
        (tensorBlock k sX sX sX sY (canonicalDiagonalClassFamily k) hX hX hX hY 0 r
          ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
            (fieldChowSituation k) (prodBase sX sX)
            (graphMorphism sX sX (𝟙 X) (Category.id_comp sX)) ((d : ℤ) - 0))) c) =
      pointCorrespondenceEquiv k sX sY
        (show (e : ℤ) - r = ((d + e : ℕ) : ℤ) - (d + (0 + r)) by push_cast; ring) c := by
  induction c using TensorProduct.inductionOn with
  | tmul q α =>
    rw [tensorBlock_tmul, composition_tmul, pointCorrespondenceEquiv_tmul,
      compositionInt_pointDiagonal_tensorInt k sX sY hX hY hXX hXY r α, one_mul, one_mul]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

end Name


/-! ### The tautological point correspondence through Stacks 0FG0 (3) -/

section PointBridge

variable (k : Type u) [Field k] {Z : Scheme.{u}} (sZ : Z ⟶ (fieldChowSituation k).S) [Smooth sZ]
  {m : ℕ} (hZ : RelativeDimension sZ m)

/-- For `Z` of constant dimension `m`, pushing forward along the isomorphism `Z_m ≅ Z` undoes
restriction to the part `Z_m`. -/
theorem chowPushforwardOfIso_chowGroupRestrict_dimPart [LocallyOfFiniteType sZ] (n : ℤ)
    (α : chowGroup (fieldChowSituation k) sZ n) :
    haveI := isIso_dimPart_self_ι sZ hZ
    chowPushforwardOfIso (fieldChowSituation k) (partBase sZ m) sZ (dimPart sZ m).ι rfl n
        (chowGroupRestrict (fieldChowSituation k) sZ (partBase sZ m) (dimPart sZ m).ι rfl n α) =
      α := by
  have := isIso_dimPart_self_ι sZ hZ
  have hα : chowPushforwardOfIso (fieldChowSituation k) (partBase sZ m) sZ (dimPart sZ m).ι rfl n
      (chowPushforwardOfIso (fieldChowSituation k) sZ (partBase sZ m) (inv (dimPart sZ m).ι)
        (by rw [IsIso.inv_comp_eq]) n α) = α := by
    rw [chowPushforwardOfIso_comp_apply,
      chowPushforwardOfIso_congr (fieldChowSituation k) _ _ _ (𝟙 Z) (IsIso.inv_hom_id _) _
        (Category.id_comp _), chowPushforwardOfIso_id]
  conv_lhs => rw [← hα]
  rw [chowPushforwardOfIso, chowGroupRestrict_properChowPushforward_opens_self]
  exact hα

/-- Stacks 0FG0 (3) on a class of the part `Z_m`, read in `CH_{m-n}(Spec k × Z) ⊗ ℚ`: the class
pushed into `Z` and moved along `Spec k × Z ≅ Z`. -/
theorem corrEquivCorrespondence_corrFromPointEquiv_lof [IsProper sZ] (n : ℤ) (q : ℚ)
    (β : chowGroup (fieldChowSituation k) (partBase sZ m) ((m : ℤ) - n)) :
    haveI := isIso_dimPart_self_ι sZ hZ
    corrEquivCorrespondence k (𝟙 (fieldChowSituation k).S) sZ (relativeDimension_identity _) hZ n
        (corrFromPointEquiv k sZ n (DirectSum.lof ℚ ℕ _ m (q ⊗ₜ[ℤ] β))) =
      q ⊗ₜ[ℤ] chowGroupEquivPullbackUnitLeft (fieldChowSituation k) sZ ((m : ℤ) - n)
        (chowPushforwardOfIso (fieldChowSituation k) (partBase sZ m) sZ (dimPart sZ m).ι rfl
          ((m : ℤ) - n) β) := by
  have := isIso_dimPart_self_ι sZ hZ
  have := isIso_dimPart_self_ι (𝟙 (fieldChowSituation k).S) (relativeDimension_identity _)
  rw [corrFromPointEquiv_lof, corrEquivCorrespondence_lof_lof]
  simp only [correspondenceFromPointEquivOfIso, LinearEquiv.trans_apply]
  change q ⊗ₜ[ℤ] chowPushforwardOfIso _ _ _ _ _ _ (chowPushforwardOfIso _ _ _ (inv _) _ _
    (chowPushforwardOfIso _ _ _ (inv _) _ _ β)) = q ⊗ₜ[ℤ] chowPushforwardOfIso _ _ _ (inv _) _ _
      (chowPushforwardOfIso _ _ _ _ _ _ β)
  rw [chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_comp_apply]
  congr 1
  congr 2
  rw [← cancel_mono (pullback.snd (𝟙 (fieldChowSituation k).S) sZ)]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, prodHom]
  rw [pullback.lift_snd, IsIso.inv_comp_eq, IsIso.inv_comp_eq]
  simp

/-- Stacks 0FG0 (3) on the class in `CH^n(Z) ⊗ ℚ` of an integral class `α ∈ CH_{m-n}(Z)`, read in
`CH_{m-n}(Spec k × Z) ⊗ ℚ`: the class `α` moved along `Spec k × Z ≅ Z`. -/
theorem corrEquivCorrespondence_corrFromPointEquiv_chowGroupToCodimension [IsProper sZ] (n l : ℤ)
    (h : l = (m : ℤ) - n) (q : ℚ) (α : chowGroup (fieldChowSituation k) sZ l) :
    haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
    corrEquivCorrespondence k (𝟙 (fieldChowSituation k).S) sZ (relativeDimension_identity _) hZ n
        (corrFromPointEquiv k sZ n (rationalCodimensionToCodimChow k sZ n
          (q ⊗ₜ[ℤ] chowGroupToCodimension sZ l n α))) =
      q ⊗ₜ[ℤ] chowGroupEquivPullbackUnitLeft (fieldChowSituation k) sZ ((m : ℤ) - n)
        (chowGroupDegreeEquiv (fieldChowSituation k) sZ h α) := by
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have := isIso_dimPart_self_ι sZ hZ
  rw [rationalCodimensionToCodimChow_tmul, codimensionToCodimChow_of_relativeDimension sZ hZ,
    chowGroupToCodimension_apply_of_eq sZ l n α m h, ← (DirectSum.lof ℚ ℕ _ m).map_smul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    corrEquivCorrespondence_corrFromPointEquiv_lof, ← chowGroupDegreeEquiv_chowPushforwardOfIso,
    chowPushforwardOfIso_chowGroupRestrict_dimPart k sZ hZ]

end PointBridge

section PointBridgeProduct

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  [Smooth sX] [Smooth sY] [IsProper sX] [IsProper sY]

/-- **The tautological point correspondence through Stacks 0FG0 (3).** For `X × Y` of constant
dimension `m` and `c ∈ CH_{e-r}(X × Y) ⊗ ℚ`, the correspondence `Spec k ⟶ X × Y` which Stacks
0FG0 (3) attaches to the class of `c` in `CH^n(X × Y) ⊗ ℚ = ⊕_p CH_{p-n}((X × Y)_p) ⊗ ℚ` is the
tautological point correspondence of `c`. -/
theorem corrEquivCorrespondence_corrFromPointEquiv_rationalCodimensionToCodimChow {e r n : ℤ}
    {m : ℕ} (hXY : RelativeDimension (prodBase sX sY) m) (h : e - r = m - n)
    (c : Correspondence (fieldChowSituation k) sX sY e r) :
    haveI : CompactSpace (Limits.pullback sX sY : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (prodBase sX sY)
    corrEquivCorrespondence k (𝟙 (fieldChowSituation k).S) (prodBase sX sY)
        (relativeDimension_identity _) hXY n
        (corrFromPointEquiv k (prodBase sX sY) n
          (rationalCodimensionToCodimChow k (prodBase sX sY) n
            ((chowGroupToCodimension (prodBase sX sY) (e - r) n).toIntLinearMap.baseChange ℚ
              c))) =
      pointCorrespondenceEquiv k sX sY h c := by
  induction c using TensorProduct.inductionOn with
  | tmul q α =>
    rw [LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
      corrEquivCorrespondence_corrFromPointEquiv_chowGroupToCodimension k (prodBase sX sY) hXY n
        (e - r) h q α, pointCorrespondenceEquiv_tmul]
  | add a b ha hb =>
    rw [LinearMap.map_add, LinearMap.map_add, LinearEquiv.map_add, LinearEquiv.map_add, ha, hb,
      LinearEquiv.map_add]

end PointBridgeProduct

/-! ### The name of a correspondence -/

section SmoothProjective

open MonoidalCategory CorrespondenceCategory

variable {k : Type u} [Field k] {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
  (hX : RelativeDimension X.obj.hom d) (hY : RelativeDimension Y.obj.hom e)

/-- `X × Y` has dimension `d + e`. -/
theorem relativeDimension_tensorObj (hX : RelativeDimension X.obj.hom d)
    (hY : RelativeDimension Y.obj.hom e) : RelativeDimension (X ⊗ Y).obj.hom (d + e) :=
  relativeDimension_of_eq rfl ((Nat.add_comm e d) ▸
    relativeDimension_prodBase k X.obj.hom Y.obj.hom hX hY)

attribute [local instance] isClosedImmersion_graphMorphism in
/-- `1 ⊗ c` is `[Δ_X] ⊗ c` on the products: read in `CH_{(d+e)-r}((X × X) × (X × Y)) ⊗ ℚ`, the
tensor product of the class of the diagonal with the class of `c`. -/
theorem corrEquivCorrespondence_whiskerLeft (r : ℤ) (c : SmoothProjectiveCorr X Y r) :
    corrEquivCorrespondence k _ _ (relativeDimension_tensorSelf X hX)
        (relativeDimension_tensorObj hX hY) (0 + r)
        (SmoothProjectiveCorr.toCorr _ _ _ (tensorCorr 0 r (correspondenceDiagonal k X) c)) =
      tensorBlock k X.obj.hom X.obj.hom X.obj.hom Y.obj.hom (canonicalDiagonalClassFamily k)
        hX hX hX hY 0 r
        ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
          (fieldChowSituation k) (prodBase X.obj.hom X.obj.hom)
          (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _)) ((d : ℤ) - 0)))
        (corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY r
          (SmoothProjectiveCorr.toCorr X Y r c)) := by
  refine (corrEquivCorrespondence_tensor k (canonicalDiagonalClassFamily k) X.obj.hom X.obj.hom
    X.obj.hom Y.obj.hom (canonicalDiagonalClassFamily_isoInvariant k) hX hX hX hY
    (relativeDimension_tensorSelf X hX) (relativeDimension_tensorObj hX hY) 0 r
    (SmoothProjectiveCorr.toCorr _ _ _ (correspondenceDiagonal k X))
    (SmoothProjectiveCorr.toCorr _ _ _ c)).trans ?_
  rw [corrEquivCorrespondence_correspondenceDiagonal X hX]

/-- **The name of a correspondence under the self-duality of Stacks 0FGI.** For `X` and `Y`
smooth projective over `k`, equidimensional of dimensions `d` and `e`, the tautological
identification

  `Corrʳ(X, Y) = CH_{e-r}(X × Y) ⊗ ℚ = CH_{(d+e)-(d+r)}(Spec k × (X × Y)) ⊗ ℚ`
  `= Corr^{d+r}(Spec k, X × Y)`,

the same Chow class moved along `Spec k × (X × Y) ≅ X × Y`. -/
def correspondenceNameEquiv (r : ℤ) :
    SmoothProjectiveCorr X Y r ≃ₗ[ℚ]
      SmoothProjectiveCorr (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) (X ⊗ Y)
        ((d : ℤ) + r) :=
  (SmoothProjectiveCorr.toCorr X Y r).trans
    ((corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY r).trans
      ((pointCorrespondenceEquiv k X.obj.hom Y.obj.hom
          (show (e : ℤ) - r = ((d + e : ℕ) : ℤ) - (d + r) by push_cast; ring)).trans
        ((corrEquivCorrespondence k _ _ (relativeDimension_tensorUnit (k := k))
          (relativeDimension_tensorObj hX hY) ((d : ℤ) + r)).symm.trans
          (SmoothProjectiveCorr.toCorr _ _ _).symm)))

/-- The name of `c`, read in `CH_{(d+e)-(d+r)}(Spec k × (X × Y)) ⊗ ℚ`, is the class of `c` moved
along `Spec k × (X × Y) ≅ X × Y`. -/
theorem corrEquivCorrespondence_correspondenceNameEquiv (r : ℤ) (c : SmoothProjectiveCorr X Y r) :
    corrEquivCorrespondence k _ _ (relativeDimension_tensorUnit (k := k))
        (relativeDimension_tensorObj hX hY) ((d : ℤ) + r)
        (SmoothProjectiveCorr.toCorr _ _ _ (correspondenceNameEquiv hX hY r c)) =
      pointCorrespondenceEquiv k X.obj.hom Y.obj.hom
        (show (e : ℤ) - r = ((d + e : ℕ) : ℤ) - (d + r) by push_cast; ring)
        (corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY r
          (SmoothProjectiveCorr.toCorr X Y r c)) := by
  simp only [correspondenceNameEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

attribute [local instance] isClosedImmersion_unitDiagonal isClosedImmersion_graphMorphism in
/-- `composition_pointDiagonal_tensorBlock` for smooth projective schemes, with `η` the class of
`Stacks.WeilCohomology.unitDiagonal`. -/
theorem composition_unitDiagonal_tensorBlock (r : ℤ)
    (c : Correspondence (fieldChowSituation k) X.obj.hom Y.obj.hom e r) :
    composition k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom (X ⊗ X).obj.hom
        (X ⊗ Y).obj.hom
        (canonicalDiagonalClassFamily k) (relativeDimension_tensorUnit (k := k))
        (relativeDimension_tensorSelf X hX) (relativeDimension_tensorObj hX hY) (d : ℤ) (0 + r)
        ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom (X ⊗ X).obj.hom)
          (unitDiagonal X)
          (((d + d : ℕ) : ℤ) - d)))
        (tensorBlock k X.obj.hom X.obj.hom X.obj.hom Y.obj.hom (canonicalDiagonalClassFamily k)
          hX hX hX hY 0 r
          ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
            (fieldChowSituation k) (prodBase X.obj.hom X.obj.hom)
            (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _)) ((d : ℤ) - 0))) c) =
      pointCorrespondenceEquiv k X.obj.hom Y.obj.hom
        (show (e : ℤ) - r = ((d + e : ℕ) : ℤ) - (d + (0 + r)) by push_cast; ring) c :=
  composition_pointDiagonal_tensorBlock k X.obj.hom Y.obj.hom hX hY _ _ r c

/-- The tautological point correspondence, transported from degree `d + (0 + r)` to `d + r`. -/
theorem correspondenceCongr_pointCorrespondenceEquiv_tensorObj (r : ℤ)
    (c : Correspondence (fieldChowSituation k) X.obj.hom Y.obj.hom e r) :
    correspondenceCongr k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom (X ⊗ Y).obj.hom
        (show (d : ℤ) + (0 + r) = d + r by ring)
        (pointCorrespondenceEquiv k X.obj.hom Y.obj.hom
          (show (e : ℤ) - r = ((d + e : ℕ) : ℤ) - (d + (0 + r)) by push_cast; ring) c) =
      pointCorrespondenceEquiv k X.obj.hom Y.obj.hom
        (show (e : ℤ) - r = ((d + e : ℕ) : ℤ) - (d + r) by push_cast; ring) c :=
  correspondenceCongr_pointCorrespondenceEquiv k X.obj.hom Y.obj.hom _ _ _ c

/-- **The name of a correspondence under the self-duality is its class** (used in Stacks 0FHM).
Let `X` and `Y` be smooth projective over `k`, equidimensional of dimensions `d` and `e`, and let
`η = [Δ] ∈ Corr^d(Spec k, X × X)` be the unit of the self-duality of Stacks 0FGI. For a
correspondence `c ∈ Corrʳ(X, Y)` the composite `η ≫ (X ◁ c) : 𝟏 ⟶ X ⊗ Y` is the class of `c`
itself, read as a correspondence from `Spec k` to `X × Y` along `Spec k × (X × Y) ≅ X × Y`. -/
theorem dualityUnit_comp_whiskerLeft_of (r : ℤ) (c : SmoothProjectiveCorr X Y r) :
    dualityUnit X hX ≫ ((GradedCompositionData.Obj.mk X : CorrespondenceCategory k) ◁
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr X Y i) r c :
          (GradedCompositionData.Obj.mk X : CorrespondenceCategory k) ⟶
            GradedCompositionData.Obj.mk Y)) =
      DirectSum.of
        (fun i ↦ SmoothProjectiveCorr (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) (X ⊗ Y) i)
        ((d : ℤ) + r) (correspondenceNameEquiv hX hY r c) := by
  rw [whiskerLeft_eq, GradedCompositionData.id_eq,
    show (canonicalCorrespondenceCompositionData k).diagonal X = correspondenceDiagonal k X from
      rfl,
    tensorHom_of_of, dualityUnit]
  rw [GradedCompositionData.of_comp_of (canonicalCorrespondenceCompositionData k)
    (X := CorrespondenceCategory.tensorUnit) (Y := GradedCompositionData.Obj.mk (X ⊗ X))
    (Z := GradedCompositionData.Obj.mk (X ⊗ Y))]
  refine of_eq_of_corrEquivCorrespondence (relativeDimension_tensorUnit (k := k))
    (relativeDimension_tensorObj hX hY) (by ring) _ _ ?_
  rw [corrEquivCorrespondence_correspondenceNameEquiv]
  simp only [canonicalCorrespondenceCompositionData, toCorr_correspondenceCompositionData_comp]
  rw [corrEquivCorrespondence_comp k _ _ (canonicalDiagonalClassFamily k)
      (canonicalDiagonalClassFamily_isoInvariant k) _ (relativeDimension_tensorUnit (k := k))
      (relativeDimension_tensorSelf X hX) (relativeDimension_tensorObj hX hY),
    corrEquivCorrespondence_dualityUnitCorr]
  conv_lhs => rw [corrEquivCorrespondence_whiskerLeft hX hY]
  conv_lhs => rw [composition_unitDiagonal_tensorBlock hX hY r]
  exact correspondenceCongr_pointCorrespondenceEquiv_tensorObj r _


/-! ### The name as a rational Chow class of `X × Y` -/

instance compactSpace_tensorObj_left : CompactSpace (X ⊗ Y).obj.left :=
  QuasiCompact.compactSpace_of_compactSpace (X ⊗ Y).obj.hom

/-- **A correspondence as a rational Chow class of the product.** For `X` and `Y` equidimensional of
dimensions `d` and `e`, `X × Y` is equidimensional of dimension `d + e`, and the natural
identification

  `Corrʳ(X, Y) = CH_{e-r}(X × Y) ⊗ ℚ = CH^{d+r}(X × Y) ⊗ ℚ`,

the codimension grading `CH^{d+r}(X × Y) ⊗ ℚ = ⊕_p CH_{p-(d+r)}((X × Y)_p) ⊗ ℚ` of Section 0FFZ
(`Stacks.WeilCohomology.CodimChow`): a class of dimension `e - r` on `X × Y` is read in
codimension `d + r` (`Stacks.WeilCohomology.chowGroupToCodimension`) and then rationally
(`Stacks.WeilCohomology.rationalCodimensionToCodimChow`). -/
def corrToCodimChow (r : ℤ) :
    SmoothProjectiveCorr X Y r →ₗ[ℚ] CodimChow k (X ⊗ Y).obj.hom ((d : ℤ) + r) :=
  rationalCodimensionToCodimChow k (X ⊗ Y).obj.hom ((d : ℤ) + r) ∘ₗ
    (chowGroupToCodimension (X ⊗ Y).obj.hom ((e : ℤ) - r) ((d : ℤ) + r)).toIntLinearMap.baseChange
      ℚ ∘ₗ
    (corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY r).toLinearMap ∘ₗ
    (SmoothProjectiveCorr.toCorr X Y r).toLinearMap

/-- `Stacks.WeilCohomology.corrToCodimChow` unfolded: the class of `c` in
`CH_{e-r}(X × Y) ⊗ ℚ`, read in codimension `d + r`. -/
theorem corrToCodimChow_apply (r : ℤ) (c : SmoothProjectiveCorr X Y r) :
    corrToCodimChow hX hY r c =
      rationalCodimensionToCodimChow k (X ⊗ Y).obj.hom ((d : ℤ) + r)
        ((chowGroupToCodimension (X ⊗ Y).obj.hom ((e : ℤ) - r)
            ((d : ℤ) + r)).toIntLinearMap.baseChange ℚ
          (corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY r
            (SmoothProjectiveCorr.toCorr X Y r c))) :=
  rfl

/-- **`corrToCodimChow` on an integral class.** The correspondence whose class on `X × Y` is
`q ⊗ α`, for an integral class `α ∈ CH_{e-r}(X × Y)`, goes to `q` times the class in
`CH^{d+r}(X × Y) ⊗ ℚ` of `α` read in codimension `d + r`. -/
theorem corrToCodimChow_tmul (r : ℤ) (q : ℚ)
    (α : chowGroup (fieldChowSituation k) (prodBase X.obj.hom Y.obj.hom) ((e : ℤ) - r)) :
    corrToCodimChow hX hY r ((SmoothProjectiveCorr.toCorr X Y r).symm
        ((corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY r).symm (q ⊗ₜ[ℤ] α))) =
      q • codimensionToCodimChow k (X ⊗ Y).obj.hom ((d : ℤ) + r)
        (chowGroupToCodimension (X ⊗ Y).obj.hom ((e : ℤ) - r) ((d : ℤ) + r) α) := by
  rw [corrToCodimChow_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
    rationalCodimensionToCodimChow_tmul]

/-- Stacks 0FG0 (3) on the class of a correspondence, read in
`CH_{(d+e)-(d+r)}(Spec k × (X × Y)) ⊗ ℚ`. -/
theorem corrEquivCorrespondence_pointCorrEquiv_corrToCodimChow (r : ℤ)
    (c : Correspondence (fieldChowSituation k) X.obj.hom Y.obj.hom e r) :
    corrEquivCorrespondence k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
        (X ⊗ Y).obj.hom
        (relativeDimension_tensorUnit (k := k)) (relativeDimension_tensorObj hX hY) ((d : ℤ) + r)
        (corrFromPointEquiv k (X ⊗ Y).obj.hom ((d : ℤ) + r)
          (rationalCodimensionToCodimChow k (X ⊗ Y).obj.hom ((d : ℤ) + r)
            ((chowGroupToCodimension (X ⊗ Y).obj.hom ((e : ℤ) - r)
              ((d : ℤ) + r)).toIntLinearMap.baseChange ℚ c))) =
      pointCorrespondenceEquiv k X.obj.hom Y.obj.hom
        (show (e : ℤ) - r = ((d + e : ℕ) : ℤ) - (d + r) by push_cast; ring) c :=
  corrEquivCorrespondence_corrFromPointEquiv_rationalCodimensionToCodimChow k X.obj.hom Y.obj.hom
    (relativeDimension_tensorObj hX hY) _ c

/-- **The name of a correspondence through Stacks 0FG0 (3).** The name of `c ∈ Corrʳ(X, Y)` is
the correspondence `Spec k ⟶ X × Y` which Stacks 0FG0 (3)
(`Stacks.WeilCohomology.SmoothProjectiveScheme.pointCorrEquiv`) attaches to the class of `c`
in `CH^{d+r}(X × Y) ⊗ ℚ`. -/
theorem correspondenceNameEquiv_eq_pointCorrEquiv (r : ℤ) (c : SmoothProjectiveCorr X Y r) :
    correspondenceNameEquiv hX hY r c =
      SmoothProjectiveScheme.pointCorrEquiv (X ⊗ Y) ((d : ℤ) + r)
        (corrToCodimChow hX hY r c) := by
  apply (SmoothProjectiveCorr.toCorr _ _ _).injective
  apply (corrEquivCorrespondence k _ _ (relativeDimension_tensorUnit (k := k))
    (relativeDimension_tensorObj hX hY) ((d : ℤ) + r)).injective
  rw [corrEquivCorrespondence_correspondenceNameEquiv]
  conv_rhs => rw [SmoothProjectiveScheme.pointCorrEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, corrToCodimChow_apply,
    corrEquivCorrespondence_pointCorrEquiv_corrToCodimChow hX hY]

/-- **The name of a correspondence under the self-duality is its class, through Stacks 0FG0 (3)**
(the form used in Stacks 0FHM). For `c ∈ Corrʳ(X, Y)`, the composite `η ≫ (X ◁ c)` of the unit
of the self-duality of Stacks 0FGI with `X ◁ c` is the correspondence `Spec k ⟶ X × Y` which
Stacks 0FG0 (3) attaches to the class of `c` in `CH^{d+r}(X × Y) ⊗ ℚ`. -/
theorem dualityUnit_comp_whiskerLeft_of_eq_pointCorrEquiv (r : ℤ)
    (c : SmoothProjectiveCorr X Y r) :
    dualityUnit X hX ≫ ((GradedCompositionData.Obj.mk X : CorrespondenceCategory k) ◁
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr X Y i) r c :
          (GradedCompositionData.Obj.mk X : CorrespondenceCategory k) ⟶
            GradedCompositionData.Obj.mk Y)) =
      DirectSum.of
        (fun i ↦ SmoothProjectiveCorr (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) (X ⊗ Y) i)
        ((d : ℤ) + r)
        (SmoothProjectiveScheme.pointCorrEquiv (X ⊗ Y) ((d : ℤ) + r)
          (corrToCodimChow hX hY r c)) := by
  rw [dualityUnit_comp_whiskerLeft_of, correspondenceNameEquiv_eq_pointCorrEquiv]

end SmoothProjective

end Stacks.WeilCohomology

end
