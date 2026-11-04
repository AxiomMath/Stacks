module

public import StacksFrontier.AlgebraicGeometry.Duality.KoszulHighDegreeOrthogonality
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Cotangent.NaiveComparisonIsIso
public import StacksFrontier.Deformation.RingThickening.CotangentAutomorphisms
public import StacksFrontier.Deformation.SquareZero.NaiveCotangentUlifted
public import StacksFrontier.Homology.DoubleExtend

/-!
# `Ext¹` out of the cotangent complex and out of the naive cotangent complex

Let `A → B` be a ring map and `N` a `B`-module. The identification
`NL_{B/A} = τ_{≥ -1} L_{B/A}` of Tag 08RB gives

`Ext¹_B(L_{B/A}, N) = Ext¹_B(NL_{B/A}, N)`,

because `N[1]` lies in degrees `≥ -1`, so that maps into it only see the truncation
`τ_{≥ -1}`. This is the step of Tag 08SP which turns the statements of Deformation Theory,
phrased with the naive cotangent complex, into statements about the cotangent complex.

## Main definitions

* `Stacks.Deformation.SquareZeroExtensionProblem.cotangentToNaiveCochain`: the map of complexes
  `L_{B/A} → NL_{B/A}` (the chain map of Remark 08UP followed by the identification of the
  degree-zero term of the standard resolution with `A[B]`), with both complexes in the module
  universe in which the `Ext` groups are taken.
* `Stacks.Deformation.SquareZeroExtensionProblem.cotangentExtOneEquiv`:
  `Ext¹_B(NL_{B/A}, N) ≃+ Ext¹_B(L_{B/A}, N)`.

## Main results

* `Stacks.Deformation.SquareZeroExtensionProblem.isIso_truncGE_map_Q_cotangentToNaiveCochain`:
  the map `L_{B/A} → NL_{B/A}` becomes an isomorphism after `τ_{≥ -1}`.
* `Stacks.Deformation.SquareZeroExtensionProblem.cotangentExtOneEquiv_apply`: the identification
  is precomposition with that map.

## Implementation notes

The `Ext` groups of `Stacks.Deformation.naiveCotangentExtOne` are taken out of the two-term
cochain complex `Stacks.Deformation.naiveCotangentCochainComplex`, the differential of
`Algebra.naiveCotangentComplex` placed in degrees `-1` and `0`, while Tag 08RB is about
`Algebra.Extension.naiveComplex` of a presentation, the extension along
`ComplexShape.embeddingDownNat` of the same chain complex. The two are identified by
`HomologicalComplex.doubleExtendIso` and `HomologicalComplex.doubleSelfIso`, after the universe
lift, by `HomologicalComplex.mapHomologicalComplexExtendIso`.

The problem `S` has its algebra `B` in the universe `max u₂ v`, so the universe `v` of the
declarations below is not determined by `S`; a statement mentioning two of them names their
universes explicitly, as `cotangentExtOneEquiv_apply` does, or the two occurrences are solved
independently and no longer unify.

## References

* [Stacks Project, Tag 08SP](https://stacks.math.columbia.edu/tag/08SP)
* [Stacks Project, Tag 08RB](https://stacks.math.columbia.edu/tag/08RB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ u₄ v w

namespace Stacks.Deformation.SquareZeroExtensionProblem

attribute [local instance high] HasDerivedCategory.standard

variable (S : SquareZeroExtensionProblem.{u₁, u₂, max u₂ v, u₄})

/-- The naive cotangent complex of the tautological presentation, as the complex
`Algebra.Extension.naiveComplex` of Tag 08RB, is the extension of `Algebra.naiveCotangentComplex`
along `ComplexShape.embeddingDownNat`. -/
noncomputable def naiveComplexTautologicalIso :
    (Algebra.naiveCotangentComplex S.A S.B).extend ComplexShape.embeddingDownNat ≅
      Algebra.Extension.naiveComplex
        (CommAlgCat.naiveExtension.{u₂, max u₂ v} S.A (CommAlgCat.of S.A S.B)) :=
  Iso.refl _

/-- The two-term cochain complex `Stacks.Deformation.naiveCotangentCochainComplex`, out of which
the `Ext` groups of `Stacks.Deformation.naiveCotangentExtOne` are taken, is the universe lift of
the extension of `Algebra.naiveCotangentComplex` along `ComplexShape.embeddingDownNat`. -/
noncomputable def naiveCochainIso :
    naiveCotangentCochainComplex.{u₂, max u₂ v, u₄} S.A S.B ≅
      (S.liftModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((Algebra.naiveCotangentComplex S.A S.B).extend ComplexShape.embeddingDownNat) :=
  HomologicalComplex.doubleExtendIso
      ((naiveCotangentUliftedChainComplex.{u₂, max u₂ v, u₄} S.A S.B).d 1 0)
      ComplexShape.embeddingDownNat ComplexShape.downNatRelOneZero one_ne_zero ≪≫
    (ComplexShape.embeddingDownNat.extendFunctor _).mapIso
      (HomologicalComplex.doubleSelfIso ComplexShape.downNatRelOneZero one_ne_zero _
        (d_eq_zero_naiveCotangentUliftedChainComplex.{u₂, max u₂ v, u₄} S.A S.B)
        (isZero_naiveCotangentUliftedChainComplex_X.{u₂, max u₂ v, u₄} S.A S.B)) ≪≫
    HomologicalComplex.mapHomologicalComplexExtendIso S.liftModules
      (Algebra.naiveCotangentComplex S.A S.B) ComplexShape.embeddingDownNat

/-- The map of complexes `L_{B/A} → NL_{B/A}`, both lifted to the universe in which the `Ext`
groups are taken: the chain map of Remark 08UP into the naive cotangent complex of the
tautological presentation, followed by the identifications `naiveComplexTautologicalIso` and
`naiveCochainIso`. -/
noncomputable def cotangentToNaiveCochain :
    S.liftedCotangentComplex ⟶ naiveCotangentCochainComplex.{u₂, max u₂ v, u₄} S.A S.B :=
  (S.liftModules.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (Stacks.Cotangent.cotangentComplexToNaive.{u₂, max u₂ v} S.A (CommAlgCat.of S.A S.B)) ≫
    (S.liftModules.mapHomologicalComplex (ComplexShape.up ℤ)).map
      S.naiveComplexTautologicalIso.inv ≫
    S.naiveCochainIso.inv

/-- The map `L_{B/A} → NL_{B/A}` is an isomorphism on cohomology in degrees `-1` and `0`. -/
theorem isIso_homologyMap_cotangentToNaiveCochain (i : ℤ) (hi : i = -1 ∨ i = 0) :
    IsIso (HomologicalComplex.homologyMap S.cotangentToNaiveCochain i) := by
  have := Stacks.Cotangent.isIso_homologyMap_cotangentComplexToNaive.{u₂, max u₂ v} S.A
    (CommAlgCat.of S.A S.B) i hi
  have h : IsIso (HomologicalComplex.homologyMap
      ((S.liftModules.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Stacks.Cotangent.cotangentComplexToNaive.{u₂, max u₂ v} S.A
          (CommAlgCat.of S.A S.B))) i) :=
    (NatIso.isIso_map_iff
      (Functor.mapHomologicalComplexHomologyIso S.liftModules (ComplexShape.up ℤ) i) _).2
      (inferInstance : IsIso (S.liftModules.map (HomologicalComplex.homologyMap
        (Stacks.Cotangent.cotangentComplexToNaive.{u₂, max u₂ v} S.A
          (CommAlgCat.of S.A S.B)) i)))
  have := h
  rw [cotangentToNaiveCochain, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ h ?_
  infer_instance

/-- The map `L_{B/A} → NL_{B/A}` becomes an isomorphism after the truncation `τ_{≥ -1}`: it is
an isomorphism on cohomology in degrees `-1` and `0`, and in positive degrees both complexes
vanish. -/
theorem isIso_truncGE_map_Q_cotangentToNaiveCochain :
    IsIso (((DerivedCategory.TStructure.t (C := ModuleCat.{max u₂ v u₄} S.B)).truncGE (-1)).map
      (DerivedCategory.Q.map S.cotangentToNaiveCochain)) := by
  rw [Stacks.DerivedTruncation.isIso_truncGE_map_iff_forall_isIso_homologyMap]
  intro i hi
  refine (NatIso.isIso_map_iff
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u₂ v u₄} S.B) i) _).2 ?_
  show IsIso (HomologicalComplex.homologyMap S.cotangentToNaiveCochain i)
  by_cases h : i = -1 ∨ i = 0
  · exact S.isIso_homologyMap_cotangentToNaiveCochain i h
  have hpos : 0 < i := by omega
  have hsrc : IsZero (S.liftedCotangentComplex.homology i) :=
    (HomologicalComplex.ExactAt.of_isZero (S.liftModules.map_isZero
      (CommAlgCat.cotangentComplex_isZero_pos S.A (CommAlgCat.of S.A S.B) i
        hpos))).isZero_homology
  have htgt : IsZero ((naiveCotangentCochainComplex.{u₂, max u₂ v, u₄} S.A S.B).homology i) :=
    (HomologicalComplex.ExactAt.of_isZero (HomologicalComplex.isZero_double_X _ _ i
      (by omega) (by omega))).isZero_homology
  exact ⟨⟨htgt.to_ _, hsrc.eq_of_src _ _, htgt.eq_of_src _ _⟩⟩

/-- `N[0]⟦1⟧` lies in degrees `≥ -1`. -/
theorem isGE_liftedKernelSingle_shift_one :
    (DerivedCategory.TStructure.t (C := ModuleCat.{max u₂ v u₄} S.B)).IsGE
      ((S.liftedKernelSingle : DerivedCategory (ModuleCat.{max u₂ v u₄} S.B))⟦(1 : ℤ)⟧) (-1) :=
  DerivedCategory.TStructure.t.isGE_shift _ 0 1 (-1) (by decide)

/-- **`Ext¹_B(NL_{B/A}, N) = Ext¹_B(L_{B/A}, N)`**, the identification of Tag 08SP: maps into
`N[1]` only see the truncation `τ_{≥ -1}`, and `τ_{≥ -1} L_{B/A} = NL_{B/A}` by Tag 08RB. -/
noncomputable def cotangentExtOneEquiv :
    naiveCotangentExtOne S.A S.B S.N ≃+ S.cotangentExt 1 :=
  haveI := S.isIso_truncGE_map_Q_cotangentToNaiveCochain
  haveI := S.isGE_liftedKernelSingle_shift_one
  (truncGEHomAddEquiv (DerivedCategory.TStructure.t (C := ModuleCat.{max u₂ v u₄} S.B)) (-1)
      (DerivedCategory.Q.obj (naiveCotangentCochainComplex.{u₂, max u₂ v, u₄} S.A S.B))
      (S.liftedKernelSingle⟦(1 : ℤ)⟧)).symm.trans
    ((extOneSourceIso (asIso
      (((DerivedCategory.TStructure.t (C := ModuleCat.{max u₂ v u₄} S.B)).truncGE (-1)).map
        (DerivedCategory.Q.map S.cotangentToNaiveCochain))).symm).trans
    (truncGEHomAddEquiv (DerivedCategory.TStructure.t (C := ModuleCat.{max u₂ v u₄} S.B)) (-1)
      (DerivedCategory.Q.obj S.liftedCotangentComplex) (S.liftedKernelSingle⟦(1 : ℤ)⟧)))

/-- The identification `Ext¹_B(NL_{B/A}, N) = Ext¹_B(L_{B/A}, N)` is precomposition with the
map `L_{B/A} → NL_{B/A}`. -/
theorem cotangentExtOneEquiv_apply (x : naiveCotangentExtOne S.A S.B S.N) :
    cotangentExtOneEquiv.{u₁, u₂, u₄, v} S x =
      (ShiftedHom.mk₀ (0 : ℤ) rfl
        (DerivedCategory.Q.map (cotangentToNaiveCochain.{u₁, u₂, u₄, v} S))).comp x
        (add_zero 1) := by
  rw [ShiftedHom.mk₀_comp]
  have := isIso_truncGE_map_Q_cotangentToNaiveCochain.{u₁, u₂, u₄, v} S
  have := isGE_liftedKernelSingle_shift_one.{u₁, u₂, u₄, v} S
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{max u₂ v u₄} S.B)
  let e := truncGEHomAddEquiv t (-1)
    (DerivedCategory.Q.obj (naiveCotangentCochainComplex.{u₂, max u₂ v, u₄} S.A S.B))
    (S.liftedKernelSingle⟦(1 : ℤ)⟧)
  have hy : (t.truncGEπ (-1)).app _ ≫ e.symm x = x := e.apply_symm_apply x
  have key : cotangentExtOneEquiv.{u₁, u₂, u₄, v} S x =
      (t.truncGEπ (-1)).app (DerivedCategory.Q.obj S.liftedCotangentComplex) ≫
        (t.truncGE (-1)).map
          (DerivedCategory.Q.map (cotangentToNaiveCochain.{u₁, u₂, u₄, v} S)) ≫ e.symm x :=
    rfl
  rw [key, ← Category.assoc, t.truncGEπ_naturality, Category.assoc, hy]
  rfl

end Stacks.Deformation.SquareZeroExtensionProblem

end
