module

public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImage
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericDominantDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionChartComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImageDense
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionJacobsonPseudoCatenary
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.IrreducibleSchemeChart
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionSubstackFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImageDominant
public import StacksFrontier.AlgebraicGeometry.Stacks.PseudoCatenaryAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImageCounterexample0DS6

/-!
# Properties of the algebraic stack of a scheme

A scheme `U` of the big fppf site of `S` defines an algebraic stack
`AlgebraicGeometry.Stack.schemeStack U`, and a morphism `γ` of the site a 1-morphism
`AlgebraicGeometry.Stack.schemeStackMap γ`. This file reads the stack-level properties that
dimension theory asks for off the scheme: local Noetherianity, the Jacobson property and
pseudo-catenarity of `schemeStack U` (the identity is a smooth surjective scheme atlas),
irreducibility of `|schemeStack U|` (Stacks 04XL identifies it with `U`), local finite type of
`schemeStackMap γ` (Stacks 06FM for represented source and target), quasi-separatedness of the
stack of an affine base (Stacks 050D, part (8)), and the dimensions of Stacks 0AFN, 0AFP and 0DRL
when the local dimensions of `U` and of the fibres of `γ` are constant.

## Main results

* `AlgebraicGeometry.Stack.isLocallyNoetherianStack_schemeStack`,
  `AlgebraicGeometry.Stack.isJacobson_schemeStack`,
  `AlgebraicGeometry.Stack.isPseudoCatenary_schemeStack` and
  `AlgebraicGeometry.Stack.irreducibleSpace_points_schemeStack`.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_schemeStackMap`.
* `AlgebraicGeometry.Stack.isQuasiSeparatedAbs_schemeStack_of_isAffine`.
* `AlgebraicGeometry.Stack.dimension_schemeStack_of_forall` and
  `AlgebraicGeometry.Stack.relativeStackDimensionAt_schemeStackMap_of_forall`.

## References

* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The algebraic stack of a locally Noetherian scheme is locally Noetherian. -/
theorem isLocallyNoetherianStack_schemeStack (U : BigFppfOver B S hS)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)] :
    IsLocallyNoetherianStack.{u, w} B S hS (schemeStack.{u, w} B S hS U) :=
  hasPropertyOnSomeSchemeAtlas_schemeStack B S hS U _ inferInstance

/-- The algebraic stack of a Jacobson scheme is Jacobson. -/
theorem isJacobson_schemeStack (U : BigFppfOver B S hS)
    [JacobsonSpace ((BigFppfOver.toScheme B S hS).obj U)] :
    AlgebraicStacks.IsJacobson.{u, w} B S hS (schemeStack.{u, w} B S hS U) :=
  hasPropertyOnSomeSchemeAtlas_schemeStack B S hS U _ inferInstance

/-- The algebraic stack of a locally Noetherian universally catenary scheme is pseudo-catenary
(Stacks 0DRU). -/
theorem isPseudoCatenary_schemeStack (U : BigFppfOver B S hS)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (hU : Scheme.IsUniversallyCatenary ((BigFppfOver.toScheme B S hS).obj U)) :
    AlgebraicStacks.IsPseudoCatenary.{u, w} B S hS (schemeStack.{u, w} B S hS U) :=
  hasPropertyOnSomeSchemeAtlas_schemeStack B S hS U _ ⟨inferInstance, hU⟩

/-- **A morphism of the site locally of finite type induces a 1-morphism of algebraic stacks
locally of finite type** (Stacks 06FM for represented source and target). -/
theorem isLocallyOfFiniteType_schemeStackMap {U V : BigFppfOver B S hS} (g : U ⟶ V)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g)] :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS (schemeStackMap.{u, w} B S hS g) := by
  have h : Space.IsLocallyOfFiniteType B S hS (yoneda.map g) :=
    (Space.isLocallyOfFiniteType_yoneda_map_iff B S hS g).2 inferInstance
  refine (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      (isAlgebraicStack_schemeFibredCategory.{u, w} B S hS U)
      (isAlgebraicStack_schemeFibredCategory.{u, w} B S hS V) _).2 ?_
  refine (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS
      (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      (isAlgebraicStack_schemeFibredCategory.{u, w} B S hS U)
      (isAlgebraicStack_schemeFibredCategory.{u, w} B S hS V)
      (yoneda.obj U) (yoneda.obj V)
      (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)
      (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (PresheafOfCategories.sliceElementsEquivalenceOver V)
      (schemeFibredCategoryMap B S hS g)).2 ?_
  rwa [representingMap_schemeFibredCategoryMap]

/-- **A 1-morphism of algebraic stacks between represented stacks, induced by a morphism `k` of
the site whose diagonal is quasi-compact and quasi-separated, is quasi-separated** in the sense
of Stacks 04YW. -/
theorem isQuasiSeparated_of_representingMap_eq_yoneda_map {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (V W : BigFppfOver B S hS)
    (eV : StacksRepresentableCFG.EquivalenceOver 𝒳.val.val.p
      (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p)
    (eW : StacksRepresentableCFG.EquivalenceOver 𝒴.val.val.p
      (presheafOfCategories (yoneda.obj W ⋙ typeToCat)).p)
    (k : V ⟶ W)
    (hk : representingMap B S hS 𝒳.val 𝒴.val (yoneda.obj V) (yoneda.obj W) eV eW f.hom =
      yoneda.map k)
    (hqc : Space.IsQuasiCompact B S hS (yoneda.map (pullback.diagonal k)))
    (hqs : Space.IsQuasiSeparated B S hS (yoneda.map (pullback.diagonal k))) :
    AlgebraicStacks.IsQuasiSeparated B S hS f := by
  have _ : (Space.quasiCompactProperty B S hS).IsStableUnderBaseChange :=
    inferInstance
  have _ : (Space.quasiCompactProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have _ : (Space.quasiSeparatedProperty B S hS).IsStableUnderBaseChange :=
    inferInstance
  have ha := isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒴.property
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V, ⟨eV⟩⟩ f.hom
  have hΔ := isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f
  exact ⟨hasRelativeProperty_relativeDiagonal_of_prop_yoneda_diagonal B S hS
      (Space.quasiCompactProperty B S hS) f.hom ha V W eV eW k hk hΔ hqc,
    hasRelativeProperty_relativeDiagonal_of_prop_yoneda_diagonal B S hS
      (Space.quasiSeparatedProperty B S hS) f.hom ha V W eV eW k hk hΔ hqs⟩

/-- **The stack represented by an affine base `S` is quasi-separated** (Stacks 050D, part (8)):
the diagonal of `S ⟶ Spec(ℤ)` is a morphism between affine schemes. -/
theorem isQuasiSeparatedAbs_schemeStack_of_isAffine [IsAffine S] :
    IsQuasiSeparatedAbs.{u, w, w} B S hS (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))) := by
  set k := Over.mkIdTerminal.from (Over.mk (toIntObject B S hS)) with hkdef
  have hS' : IsAffine ((BigFppfOver.toScheme B _ (contains_specULiftZ B)).obj
      (Over.mk (toIntObject B S hS))) := inferInstanceAs (IsAffine S)
  have hZ' : IsAffine ((BigFppfOver.toScheme B _ (contains_specULiftZ B)).obj
      (Over.mk (𝟙 (B.obj (contains_specULiftZ B))))) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (ULift.{u} ℤ))))
  have _ : PreservesLimitsOfShape WalkingCospan
      (BigFppfOver.toScheme B _ (contains_specULiftZ B)) := by
    apply comp_preservesLimitsOfShape
  have hsq := (IsPullback.of_hasPullback k k).map (BigFppfOver.toScheme B _ (contains_specULiftZ B))
  have hP : IsAffine ((BigFppfOver.toScheme B _ (contains_specULiftZ B)).obj (pullback k k)) :=
    IsAffine.of_isIso hsq.isoPullback.hom
  refine isQuasiSeparated_of_representingMap_eq_yoneda_map B _ (contains_specULiftZ B)
    (structureMorphism B _ (contains_specULiftZ B)
      (viewOverInt.{u, w, w} B S hS (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS))))))
    (Over.mk (toIntObject B S hS)) (Over.mk (𝟙 (B.obj (contains_specULiftZ B))))
    (viewOverIntSchemeStackEquivalenceOver.{u, w, w} B S hS)
    (PresheafOfCategories.sliceElementsEquivalenceOver _) k
    ((Over.mkIdTerminal.isTerminalObj yoneda _).hom_ext _ _) ?_ ?_
  · exact Space.isQuasiCompact_yoneda_map_of_compactSpace B _ _ _ inferInstance inferInstance
  · refine (Space.isQuasiSeparated_yoneda_map_iff B _ _ _).2 ?_
    infer_instance

/-- Every point of the algebraic stack of a scheme of the site is named by a point of the
scheme through the chart of Stacks 04SW. -/
theorem exists_eq_representedChartPointMap (U : BigFppfOver B S hS)
    (x : points B S hS (schemeStack.{u, w} B S hS U).val.val
      (schemeStack.{u, w} B S hS U).val.property) :
    ∃ a : (BigFppfOver.toScheme B S hS).obj U,
      x = representedChartPointMap B S hS U ((Space.pointsEquivScheme B S hS U).symm a) := by
  let := pointTopology B S hS (schemeFibredCategory B S hS U)
  refine ⟨pointsHomeomorphScheme B S hS U x, (pointsHomeomorphScheme B S hS U).injective ?_⟩
  rw [pointsHomeomorphScheme_representedChartPointMap_pointsEquivScheme_symm]

/-- If every point of the scheme `U` has local dimension `d`, every point of `schemeStack U` has
dimension `d`. -/
theorem dimensionAtPoint_schemeStack_of_forall (U : BigFppfOver B S hS)
    (hU : IsLocallyNoetherianStack.{u, w} B S hS (schemeStack.{u, w} B S hS U)) (d : WithBot ℕ∞)
    (h : ∀ a, topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U) a = d)
    (x : points B S hS (schemeStack.{u, w} B S hS U).val.val
      (schemeStack.{u, w} B S hS U).val.property) :
    dimensionAtPoint B S hS (schemeStack.{u, w} B S hS U) hU x = dimensionSubNat d 0 := by
  obtain ⟨a, rfl⟩ := exists_eq_representedChartPointMap.{u, w} B S hS U x
  rw [dimensionAtPoint_schemeStack_eq_dimensionSubNat, Space.pointsToScheme_pointsEquivScheme_symm,
    h]

/-- If every point of the nonempty scheme `U` has local dimension `d`, so does `schemeStack U`
have dimension `d`. -/
theorem dimension_schemeStack_of_forall (U : BigFppfOver B S hS)
    [Nonempty ((BigFppfOver.toScheme B S hS).obj U)]
    (hU : IsLocallyNoetherianStack.{u, w} B S hS (schemeStack.{u, w} B S hS U)) (d : WithBot ℕ∞)
    (h : ∀ a, topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U) a = d) :
    dimension B S hS (schemeStack.{u, w} B S hS U) hU = dimensionSubNat d 0 := by
  let := pointTopology B S hS (schemeFibredCategory B S hS U)
  have : Nonempty (points B S hS (schemeStack.{u, w} B S hS U).val.val
      (schemeStack.{u, w} B S hS U).val.property) :=
    ⟨(pointsHomeomorphScheme B S hS U).symm
      (Classical.arbitrary ((BigFppfOver.toScheme B S hS).obj U))⟩
  rw [dimension]
  simp_rw [dimensionAtPoint_schemeStack_of_forall B S hS U hU d h]
  exact ciSup_const

/-- If every fibre of `γ` has local dimension `d` at every point, the relative dimension of
Stacks 0DRL of `schemeStackMap γ` is `d` at every point. -/
theorem relativeStackDimensionAt_schemeStackMap_of_forall {U V : BigFppfOver B S hS} (γ : U ⟶ V)
    (hγ : AlgebraicStacks.IsLocallyOfFiniteType B S hS (schemeStackMap.{u, w} B S hS γ))
    (hU : IsLocallyNoetherianStack.{u, w} B S hS (schemeStack.{u, w} B S hS U))
    (hV : IsLocallyNoetherianStack.{u, w} B S hS (schemeStack.{u, w} B S hS V)) (d : WithBot ℕ∞)
    (h : ∀ a, topologicalKrullDimAt
      (((BigFppfOver.toScheme B S hS).map γ).fiber (((BigFppfOver.toScheme B S hS).map γ) a))
        (((BigFppfOver.toScheme B S hS).map γ).asFiber a) = d)
    (x : points B S hS (schemeStack.{u, w} B S hS U).val.val
      (schemeStack.{u, w} B S hS U).val.property) :
    relativeStackDimensionAt.{u, w} B S hS (schemeStackMap.{u, w} B S hS γ) hγ hU hV x =
      dimensionSubNat d 0 := by
  obtain ⟨a, rfl⟩ := exists_eq_representedChartPointMap.{u, w} B S hS U x
  rw [relativeStackDimensionAt_schemeStackMap_eq_dimensionSubNat, h]

end AlgebraicGeometry.Stack

end
