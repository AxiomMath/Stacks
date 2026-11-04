module

public import StacksFrontier.AlgebraicGeometry.Stacks.ClassifyingStackModel
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionChartIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.JacobsonAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PseudoCatenaryAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base

/-!
# The dimension of the classifying stack of a smooth group over a field

Let `k` be a field and let `G` be a group algebraic space over `Spec k`, smooth over `Spec k` and
of dimension `n`. Let `𝒬` be a model of its classifying stack `BG = [Spec k/G]`. This file shows
that `|BG|` is a single point, that `BG` is locally Noetherian, Jacobson and pseudo-catenary, that
it is quasi-compact, and that its dimension of Stacks 0AFN is `-n` at its point (Stacks 0AFR).

## Main results

* `AlgebraicGeometry.Stack.dimensionAtPoint_classifyingModel`: `dim_x(BG) = -n`.
* `AlgebraicGeometry.Stack.dimension_classifyingModel`: `dim(BG) = -n`.

## References

* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0AFR](https://stacks.math.columbia.edu/tag/0AFR)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory

universe u w

namespace AlgebraicGeometry.Stack

variable {k : Type u} [Field k] (C : BigFppfSite.{u}) (hk : C.Contains (Spec (.of k)))

/-- The algebraic space `Spec k` has dimension `0` at its point, and so does any algebraic space
equal to it. -/
theorem dimensionAtPoint_of_eq_terminalSpace {F : (BigFppfOver C (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace C (Spec (.of k)) hk F)
    (h : F = (Space.terminalSpace C (Spec (.of k)) hk).obj)
    (x : Space.points C (Spec (.of k)) hk F) :
    Space.dimensionAtPoint C (Spec (.of k)) hk F hF x = ((0 : ℕ) : WithBot ℕ∞) := by
  subst h
  have hdim' : Space.dimension C (Spec (.of k)) hk
      (yoneda.obj (Space.baseTerminal C (Spec (.of k)) hk))
      (isAlgebraicSpace_yoneda C (Spec (.of k)) hk (Space.baseTerminal C (Spec (.of k)) hk)) =
        0 := by
    rw [Space.dimension_yoneda_eq_topologicalKrullDim]
    show topologicalKrullDim (PrimeSpectrum k) = 0
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
  have hdim : Space.dimension C (Spec (.of k)) hk _ hF = 0 := hdim'
  have hle : Space.dimensionAtPoint C (Spec (.of k)) hk _ hF x ≤ 0 :=
    hdim ▸ le_iSup (fun y => Space.dimensionAtPoint C (Spec (.of k)) hk _ hF y) x
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp
    (Space.dimensionAtPoint_ne_bot C (Spec (.of k)) hk _ hF x)
  rw [← hd] at hle ⊢
  have : d = 0 := le_antisymm (by exact_mod_cast hle) bot_le
  rw [this]
  rfl

/-- **A smooth surjective chart by an algebraic space equal to `Spec k` gives a scheme atlas**
of an algebraic stack whose underlying scheme `Spec k` has a given property: the scheme `Spec k`
maps to the algebraic space it represents by a smooth surjective 1-morphism. -/
theorem hasPropertyOnSomeSchemeAtlas_of_eq_terminalSpace (P : Scheme.{u} → Prop)
    {𝒳 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk}
    {F : (BigFppfOver C (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace C (Spec (.of k)) hk F)
    (h : F = (Space.terminalSpace C (Spec (.of k)) hk).obj)
    (a : algebraicSpaceStack.{u, w} C (Spec (.of k)) hk F hF ⟶ 𝒳)
    (hasm : AlgebraicStacks.IsSmooth C (Spec (.of k)) hk a)
    (hasurj : IsSurjective C (Spec (.of k)) hk a) (hP : P (Spec (.of k))) :
    HasPropertyOnSomeSchemeAtlas C (Spec (.of k)) hk P 𝒳 := by
  subst h
  have hS0 : MorphismProperty.ContainsIdentities
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have hSi : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @AlgebraicGeometry.Surjective.{u})
  have hS' : MorphismProperty.ContainsIdentities
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme C (Spec (.of k)) hk)) :=
    MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme C (Spec (.of k)) hk)
  have hSi' : MorphismProperty.RespectsIso
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme C (Spec (.of k)) hk)) :=
    MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme C (Spec (.of k)) hk)
  obtain ⟨c, hcsm, hcsurj⟩ := exists_schemeStack_hom_of_etaleChart.{u, w} C (Spec (.of k)) hk hF
    (𝟙 (yoneda.obj (Space.baseTerminal C (Spec (.of k)) hk)))
    (Space.presheaf_etale_id C (Spec (.of k)) hk _)
  exact ⟨Space.baseTerminal C (Spec (.of k)) hk, c ≫ a,
    isSurjective_comp C (Spec (.of k)) hk c a
      (hcsurj (MorphismProperty.presheaf_of_isIso _
        (𝟙 (yoneda.obj (Space.baseTerminal C (Spec (.of k)) hk))))) hasurj,
    AlgebraicStacks.isSmooth_comp C (Spec (.of k)) hk c a hcsm hasm, hP⟩

variable (G : Space.GroupAlgebraicSpace C (Spec (.of k)) hk
    (Space.terminalSpace C (Spec (.of k)) hk).obj
    (Space.terminalSpace C (Spec (.of k)) hk).property)
  (hG : Space.IsSmooth C (Spec (.of k)) hk G.obj.X.hom)
  (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
  (e : StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p 𝒬.val.val.p)

include hG e in
/-- A model of the classifying stack has a scheme atlas by `Spec k`. -/
theorem hasPropertyOnSomeSchemeAtlas_classifyingModel (P : Scheme.{u} → Prop)
    (hP : P (Spec (.of k))) : HasPropertyOnSomeSchemeAtlas C (Spec (.of k)) hk P 𝒬 :=
  hasPropertyOnSomeSchemeAtlas_of_eq_terminalSpace C hk P _
    (classifyingGroupoid_objects_obj C hk G) (classifyingChart C hk G 𝒬 e)
    (isSmooth_classifyingChart C hk G 𝒬 e hG) (isSurjective_classifyingChart C hk G 𝒬 e hG) hP

include hG e in
/-- **The classifying stack is locally Noetherian.** -/
theorem isLocallyNoetherianStack_classifyingModel :
    IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬 :=
  hasPropertyOnSomeSchemeAtlas_classifyingModel C hk G hG 𝒬 e _ inferInstance

include hG e in
/-- **The classifying stack is Jacobson.** -/
theorem isJacobson_classifyingModel : AlgebraicStacks.IsJacobson C (Spec (.of k)) hk 𝒬 :=
  hasPropertyOnSomeSchemeAtlas_classifyingModel C hk G hG 𝒬 e _ inferInstance

include hG e in
/-- **The classifying stack is pseudo-catenary.** -/
theorem isPseudoCatenary_classifyingModel :
    AlgebraicStacks.IsPseudoCatenary C (Spec (.of k)) hk 𝒬 :=
  hasPropertyOnSomeSchemeAtlas_classifyingModel C hk G hG 𝒬 e _
    ⟨inferInstance, Scheme.isUniversallyCatenary_spec_of_field k⟩

/-- The points of the stack of an algebraic space equal to `Spec k` form a singleton. -/
theorem unique_stackPoints_of_eq_terminalSpace {F : (BigFppfOver C (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace C (Spec (.of k)) hk F)
    (h : F = (Space.terminalSpace C (Spec (.of k)) hk).obj) :
    Nonempty (points C (Spec (.of k)) hk (fibredCategory C (Spec (.of k)) hk F).val
        (fibredCategory C (Spec (.of k)) hk F).property) ∧
      Subsingleton (points C (Spec (.of k)) hk (fibredCategory C (Spec (.of k)) hk F).val
        (fibredCategory C (Spec (.of k)) hk F).property) := by
  have := subsingleton_points_of_eq_terminalSpace C hk h
  obtain ⟨x⟩ := nonempty_points_of_eq_terminalSpace C hk h
  have hb := spacePointMap_id_bijective C (Spec (.of k)) hk F
  exact ⟨⟨spacePointMap C (Spec (.of k)) hk F (fibredCategory C (Spec (.of k)) hk F)
    (BasedFunctor.id (fibredCategory C (Spec (.of k)) hk F).val) x⟩, hb.2.subsingleton⟩

include hG e in
/-- **The classifying stack has exactly one point**: it is the image of the single point of
`Spec k` under its surjective chart. -/
theorem nonempty_points_classifyingModel :
    Nonempty (points C (Spec (.of k)) hk 𝒬.val.val 𝒬.val.property) := by
  obtain ⟨⟨x⟩, -⟩ := unique_stackPoints_of_eq_terminalSpace C hk
    (classifyingGroupoid C hk G).objects.property (classifyingGroupoid_objects_obj C hk G)
  exact ⟨AlgebraicStacks.pointsMap C (Spec (.of k)) hk (classifyingChart C hk G 𝒬 e) x⟩

include hG e in
/-- **The classifying stack has at most one point.** -/
theorem subsingleton_points_classifyingModel :
    Subsingleton (points C (Spec (.of k)) hk 𝒬.val.val 𝒬.val.property) := by
  obtain ⟨-, hsub⟩ := unique_stackPoints_of_eq_terminalSpace C hk
    (classifyingGroupoid C hk G).objects.property (classifyingGroupoid_objects_obj C hk G)
  exact (isSurjective_classifyingChart C hk G 𝒬 e hG).subsingleton

include hG e in
/-- **Stacks 0AFR at its point: the dimension of the classifying stack of a smooth group of
dimension `n` over a field is `-n`.** The tautological chart `Spec k ⟶ BG` is smooth with relative
dimension `n` (`AlgebraicGeometry.Stack.relativeDimensionAt_classifyingChart`), and
`dim(Spec k) = 0`, so the dimension formula of Stacks 0DRJ gives `0 - n`. -/
theorem dimensionAtPoint_classifyingModel (n : ℕ)
    (hn : Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property = (n : WithBot ℕ∞))
    (x : points C (Spec (.of k)) hk 𝒬.val.val 𝒬.val.property) :
    dimensionAtPoint C (Spec (.of k)) hk 𝒬
        (isLocallyNoetherianStack_classifyingModel C hk G hG 𝒬 e) x = ((-(n : ℤ) : ℤ) : EInt) := by
  have := subsingleton_points_of_eq_terminalSpace C hk (classifyingGroupoid_objects_obj C hk G)
  obtain ⟨s⟩ := nonempty_points_of_eq_terminalSpace C hk (classifyingGroupoid_objects_obj C hk G)
  have := subsingleton_points_classifyingModel C hk G hG 𝒬 e
  rw [dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} C (Spec (.of k)) hk 𝒬
      (isLocallyNoetherianStack_classifyingModel C hk G hG 𝒬 e) x _
      (classifyingChart C hk G 𝒬 e) (isSmooth_classifyingChart C hk G 𝒬 e hG)
      (isLocallyOfFiniteType_classifyingChart C hk G 𝒬 e hG) s (Subsingleton.elim _ _) n
      (relativeDimensionAt_classifyingChart C hk G 𝒬 e hG n hn s),
    dimensionAtPoint_of_eq_terminalSpace C hk _ (classifyingGroupoid_objects_obj C hk G) s]
  have hz : dimensionSubNat ((0 : ℕ) : WithBot ℕ∞) n = (((0 : ℤ) - (n : ℤ) : ℤ) : EInt) := rfl
  rw [hz]
  congr 1
  omega

include hG e in
/-- **Stacks 0AFR: the dimension of the classifying stack of a smooth group of dimension `n` over a
field is `-n`.** -/
theorem dimension_classifyingModel (n : ℕ)
    (hn : Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property = (n : WithBot ℕ∞)) :
    dimension C (Spec (.of k)) hk 𝒬 (isLocallyNoetherianStack_classifyingModel C hk G hG 𝒬 e) =
      ((-(n : ℤ) : ℤ) : EInt) := by
  obtain ⟨x⟩ := nonempty_points_classifyingModel C hk G hG 𝒬 e
  have := subsingleton_points_classifyingModel C hk G hG 𝒬 e
  rw [← dimensionAtPoint_classifyingModel C hk G hG 𝒬 e n hn x]
  exact le_antisymm (iSup_le fun y => (Subsingleton.elim y x) ▸ le_rfl) (le_iSup _ x)

end AlgebraicGeometry.Stack

end
