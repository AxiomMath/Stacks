module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.CurveDegreeDeterminant
public import
  StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensorTriangulated
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekCohenMacaulayTwistIso
public import
  StacksFrontier.AlgebraicGeometry.Duality.UpperShriekLocalCompleteIntersection.Decomposition
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekLocalCompleteIntersection.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekPullbackComparisonCanonicalMaps
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.AffineLine
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.StandardAffineChart
public import StacksFrontier.CategoryTheory.Shift.TensorRightOfShiftedUnit
public import StacksFrontier.CategoryTheory.Shift.TensorRightOfShiftedUnitWhisker

/-!
# The upper shriek functor of the affine line

Let `S` be a Noetherian scheme, `Y` an object of `FTS S` and `f : 𝔸¹_Y ⟶ Y` the projection. Then
`f^!(-) ≅ Lf^*(-)[1]` as functors on `D⁺_QCoh(𝒪_Y)` ([Stacks, Tag 0AA1]), for every
compactification computing `f^!`.

The morphism `f` is smooth of relative dimension one, hence Cohen–Macaulay and perfect, so
`f^!K ≅ Lf^*K ⊗ᴸ f^!𝒪_Y` naturally on `D⁺_QCoh(𝒪_Y)` ([Stacks, Tag 0B6U] (e)) and `f^!𝒪_Y` is
concentrated in degree `-1`. The standard chart `𝔸¹_Y ⊆ ℙ¹_Y` factors `f` through an open
immersion followed by a smooth proper morphism, so the fundamental class of
[Stacks, Tag 0E9Z] identifies `H^{-1}(f^!𝒪_Y)` with `Ω_{𝔸¹_Y/Y}`, which is free on `dx`. Hence
`f^!𝒪_Y ≅ 𝒪[1]`, and tensoring with `𝒪[1]` is the shift by one.

## Main definitions

* `Stacks.Duality.affineLineFTS`, `Stacks.Duality.affineLineProj`: `𝔸¹_Y` and its projection, in
  `FTS S`.
* `Stacks.Duality.quasiCoherentDerivedTensorFlipObjShiftIso`: `- ⊗ᴸ 𝒪[n] ≅ [n]` on `D_QCoh`.
* `Stacks.Duality.upperShriekPlusCompιIsoPullbackTensor`: `f^! ≅ Lf^*(-) ⊗ᴸ f^!𝒪_Y` on
  `D⁺_QCoh` for perfect `f`.

## Main results

* `Stacks.Duality.nonempty_upperShriekHomology_affineLineProj_iso`: `H^{-1}(f^!𝒪_Y) ≅ 𝒪`.
* `Stacks.Duality.nonempty_upperShriek_structureSheaf_affineLineProj_iso`: `f^!𝒪_Y ≅ 𝒪[1]`.
* `Stacks.Duality.nonempty_upperShriekPlus_affineLineProj_iso`: **[Stacks, Tag 0AA1]**.

## Implementation notes

The source deduces `f^!𝒪_Y ≅ 𝒪_X[1]` from the computation `a(𝒪) = 𝒪(-2)[1]` for `ℙ¹_Y ⟶ Y`
([Stacks, Tag 0A9W]) at the compactification `ℙ¹_Y`; here `f^!` is computed at an arbitrary
compactification, and the comparison with `ℙ¹_Y` is the one built into [Stacks, Tag 0E9Z].

## References

* [Stacks Project, Tag 0AA1](https://stacks.math.columbia.edu/tag/0AA1)
* [Stacks Project, Tag 0B6U](https://stacks.math.columbia.edu/tag/0B6U)
* [Stacks Project, Tag 0E9Z](https://stacks.math.columbia.edu/tag/0E9Z)
* [Stacks Project, Tag 0C10](https://stacks.math.columbia.edu/tag/0C10)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} [IsNoetherian S] (Y : FTS S)

/-- The affine line `𝔸¹_Y` over an object `Y` of `FTS S`, as an object of `FTS S`. -/
abbrev affineLineFTS : FTS S := FTS.mk ((𝔸(PUnit.{u+1}; Y.left) ↘ Y.left) ≫ Y.hom)

/-- The projection `𝔸¹_Y ⟶ Y`, as a morphism of `FTS S`. -/
abbrev affineLineProj : affineLineFTS Y ⟶ Y :=
  MorphismProperty.Over.homMk (𝔸(PUnit.{u+1}; Y.left) ↘ Y.left) rfl

/-- The projection `𝔸¹_Y ⟶ Y` is smooth of relative dimension one. -/
instance smoothOfRelativeDimension_affineLineProj_left :
    SmoothOfRelativeDimension 1 (affineLineProj Y).left :=
  AffineSpace.smoothOfRelativeDimension_line Y.left

/-- The projection `𝔸¹_Y ⟶ Y` is a smooth morphism. -/
instance smooth_affineLineProj_left : Smooth (affineLineProj Y).left :=
  SmoothOfRelativeDimension.smooth 1 _

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The fibres of `𝔸¹_Y ⟶ Y` have dimension one at every point. -/
theorem topologicalKrullDimAt_fiber_affineLineProj (x : (affineLineFTS Y).left) :
    topologicalKrullDimAt ((affineLineProj Y).left.fiber ((affineLineProj Y).left x))
      ((affineLineProj Y).left.asFiber x) = ((1 : ℕ) : WithBot ℕ∞) :=
  fiberDimensionAt_eq_of_smoothOfRelativeDimension _ 1 x

omit [AlgebraicGeometry.IsNoetherian S] in
/-- `𝔸¹_Y ⟶ Y` is a Cohen–Macaulay morphism: it is flat with smooth, hence Cohen–Macaulay,
fibres. -/
theorem isCohenMacaulay_affineLineProj :
    (affineLineProj Y).left.IsCohenMacaulay (isLocallyNoetherian_fiber_left _) :=
  (isCohenMacaulay_iff_flat_and_fibers _ _).2
    ⟨inferInstance, isCohenMacaulay_fiber_of_smooth _⟩

omit [AlgebraicGeometry.IsNoetherian S] in
/-- `𝔸¹_Y ⟶ Y` is a local complete intersection morphism, being smooth. -/
theorem isLocalCompleteIntersectionMorphism_affineLineProj :
    IsLocalCompleteIntersectionMorphism (affineLineProj Y).left := fun x =>
  SmoothLocus.koszulAt_of_smoothAt (InfinitesimalLifting.smoothAt_of_smooth _ x)

/-- The one coordinate of `ℙ¹` other than the zeroth. -/
def lineChartEquiv : PUnit.{u+1} ≃ {j : Fin (1 + 1) // j ≠ 0} where
  toFun _ := ⟨1, by decide⟩
  invFun _ := PUnit.unit
  left_inv _ := rfl
  right_inv j := by
    obtain ⟨j, hj⟩ := j
    fin_cases j
    · exact absurd rfl hj
    · rfl

/-- The standard chart `𝔸¹_Y ⟶ ℙ¹_Y`, an open immersion over `Y`. -/
def affineLineChart : (affineLineFTS Y).left ⟶ projectiveSpaceOver 1 Y.left :=
  projectiveSpaceOver.affineChart 1 0 lineChartEquiv.{u} Y.left

/-- The standard chart `𝔸¹_Y ⟶ ℙ¹_Y` is an open immersion. -/
instance isOpenImmersion_affineLineChart : IsOpenImmersion (affineLineChart Y) :=
  inferInstanceAs (IsOpenImmersion (projectiveSpaceOver.affineChart 1 0 lineChartEquiv.{u} Y.left))

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The standard chart `𝔸¹_Y ⟶ ℙ¹_Y` composed with the structure morphism `ℙ¹_Y ⟶ Y` is the
projection `𝔸¹_Y ⟶ Y`. -/
theorem affineLineChart_over :
    affineLineChart Y ≫ (projectiveSpaceOver 1 Y.left ↘ Y.left) = (affineLineProj Y).left :=
  projectiveSpaceOver.affineChart_over 1 0 lineChartEquiv.{u} Y.left

/-- A sheaf of modules isomorphic to zero has trivial stalks. -/
theorem not_nontrivial_stalk_of_isZero {Z : Scheme.{u}} {M : Z.Modules} (hM : IsZero M) (z : Z) :
    ¬ Nontrivial ↑(M.presheaf.stalk z) := by
  have hs : Subsingleton ↑((Stacks.ConormalSequenceRight.stalkAb Z z).obj M) :=
    AddCommGrpCat.subsingleton_of_isZero
      (@Functor.map_isZero _ _ _ _ _ _ (Stacks.ConormalSequenceRight.stalkAb Z z)
        (AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor_preservesZeroMorphisms _ z)
        _ hM)
  exact @not_nontrivial _ hs

section UpperShriek

open ClosedOpenProperFactorization

variable (j : CompactificationOf (Over.mk (affineLineProj Y).left))

/-- The cohomology sheaves of `f^!𝒪_Y` for `f : 𝔸¹_Y ⟶ Y` vanish outside degree `-1`. -/
theorem isZero_upperShriekHomology_affineLineProj (k : ℤ) (hk : k ≠ -1) :
    IsZero (upperShriekHomology (affineLineProj Y) j k) :=
  isZero_homology_relativeDualizingComplexObj_of_ne _ j (isCohenMacaulay_affineLineProj Y) 1
    (topologicalKrullDimAt_fiber_affineLineProj Y) k (by simpa using hk)

/-- **`H^{-1}(f^!𝒪_Y) ≅ 𝒪_{𝔸¹_Y}`** for the projection `f : 𝔸¹_Y ⟶ Y`. The fundamental class of
[Stacks, Tag 0E9Z], for the factorization of `f` through the open immersion `𝔸¹_Y ⊆ ℙ¹_Y`,
identifies `Ω_{𝔸¹_Y/Y}` with `H^{-1}(f^!𝒪_Y)`, and `Ω_{𝔸¹_Y/Y}` is free on `dx`. -/
theorem nonempty_upperShriekHomology_affineLineProj_iso :
    Nonempty (upperShriekHomology (affineLineProj Y) j (-1) ≅
      SheafOfModules.unit (affineLineFTS Y).left.ringCatSheaf) := by
  have := isProper_projectiveSpaceOver 1 Y.left
  obtain ⟨r, -, hr, A, V, n, -, hdisj, hcov, hn, hφ⟩ :=
    exists_fundamentalClass_of_isLocalCompleteIntersection (affineLineProj Y)
      (affineLineChart Y) (projectiveSpaceOver 1 Y.left ↘ Y.left) (affineLineChart_over Y)
      (isLocalCompleteIntersectionMorphism_affineLineProj Y) j
  have hr1 : ∀ x, r x = 1 := fun x => by
    by_contra h
    exact not_nontrivial_stalk_of_isZero
      (isZero_upperShriekHomology_affineLineProj Y j (-r x) (by omega)) x ((hr x (-r x)).2 rfl)
  have hψ : ∀ a : ULift.{u} A, ∃ ψ : (Scheme.Modules.restrictFunctor (V a.down).ι).obj
          (Scheme.Modules.exteriorPower
            (Scheme.Hom.relativeDifferentials (affineLineProj Y).left) (1 : ℤ)) ⟶
        (Scheme.Modules.restrictFunctor (V a.down).ι).obj
          (upperShriekHomology (affineLineProj Y) j (-1)),
        ∀ y : (V a.down).toScheme,
          IsIso ((Stacks.ConormalSequenceRight.stalkAb (V a.down).toScheme y).map ψ) := by
    rintro ⟨a⟩
    by_cases hne : ∃ x, x ∈ V a
    · obtain ⟨x, hx⟩ := hne
      have hm : n a = 1 := (hn a x hx).symm.trans (hr1 x)
      obtain ⟨φ, hφ'⟩ := hφ a
      generalize n a = m at φ hφ' hm
      subst hm
      exact ⟨φ, fun y => (isIso_stalkMap_iff_isIso_stalkAb y φ).1
        ((hφ' y).2 (InfinitesimalLifting.smoothAt_of_smooth _ _))⟩
    · exact ⟨0, fun y => absurd ⟨y.1, y.2⟩ hne⟩
  choose ψ hψs using hψ
  have hcov' : ⨆ a : ULift.{u} A, V a.down = ⊤ := by
    rw [← hcov]
    exact le_antisymm (iSup_le fun a => le_iSup V a.down)
      (iSup_le fun a => le_iSup (fun b : ULift.{u} A => V b.down) ⟨a⟩)
  have hdisj' : Pairwise (Function.onFun Disjoint fun a : ULift.{u} A => V a.down) :=
    fun a b hab => hdisj (fun h => hab (ULift.ext h))
  obtain ⟨Φ, hΦ⟩ := SmoothLocus.exists_hom_restrict_eq_of_pairwise_disjoint _ hcov' hdisj' ψ
  have hΦs : ∀ x, IsIso ((Stacks.ConormalSequenceRight.stalkAb _ x).map Φ) := by
    intro x
    obtain ⟨a, hxa⟩ : ∃ a : ULift.{u} A, x ∈ V a.down := by
      have hx : x ∈ (⊤ : (affineLineFTS Y).left.Opens) := trivial
      rw [← hcov'] at hx
      exact TopologicalSpace.Opens.mem_iSup.1 hx
    refine (SmoothLocus.isIso_stalkAb_restrictFunctor_map_iff (V a.down) Φ ⟨x, hxa⟩).1 ?_
    rw [hΦ a]
    exact hψs a ⟨x, hxa⟩
  have : IsIso Φ := Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk Φ hΦs
  exact ⟨(asIso Φ).symm ≪≫ Scheme.Modules.exteriorPowerOneIsoSelf _ ≪≫
    AffineSpace.relativeDifferentialsIsoUnit Y.left⟩

end UpperShriek

section Shift

variable (Z : Scheme.{u})

/-- **`- ⊗ᴸ 𝒪_Z[n] ≅ [n]` on `D_QCoh(𝒪_Z)`, naturally.** The derived tensor product commutes with
the shift in both variables compatibly ([Stacks, Tag 06YU]), and `- ⊗ᴸ 𝒪_Z` is the identity. -/
def quasiCoherentDerivedTensorFlipObjShiftIso (n : ℤ) :
    (quasiCoherentDerivedTensor Z).flip.obj
        ((DerivedPushforward.derivedStructureSheaf Z)⟦n⟧) ≅
      shiftFunctor (quasiCoherentDerivedCategory Z) n :=
  let : (derivedTensor Z).CommShift₂Int :=
    (Stacks.Cohomology.TorAmplitude.derTensor Z.toRingedSpace).commShift₂
  let O := DerivedPushforward.derivedStructureSheaf Z
  let ι : quasiCoherentDerivedCategory Z ⥤ DerivedCategory Z.Modules := ObjectProperty.ι _
  let ρ : ι ⋙ (derivedTensor Z).flip.obj O.obj ≅ ι :=
    (quasiCoherentDerivedTensorFlipObjCompιIso Z O).symm ≪≫
      Functor.isoWhiskerRight (quasiCoherentDerivedTensorRightUnitor Z) ι ≪≫ Functor.leftUnitor ι
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (quasiCoherentDerivedTensorFlipObjCompιIso Z (O⟦n⟧) ≪≫
      Functor.isoWhiskerLeft ι ((derivedTensor Z).flip.mapIso ((ι.commShiftIso n).app O)) ≪≫
      Functor.whiskerLeftFlipObjShiftIsoOfUnitor (derivedTensor Z) ι O.obj ρ n ≪≫
      (ι.commShiftIso n).symm)

end Shift

section Main

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f.left))

/-- **`f^! ≅ Lf^*(-) ⊗ᴸ f^!𝒪_Y` on `D⁺_QCoh(𝒪_Y)`, naturally,** for a perfect morphism `f` of
`FTS S`: the maps `μ_{f,K}` of [Stacks, Tag 0B6T] are natural in `K` and invertible for `K`
bounded below by [Stacks, Tag 0B6U] (e). -/
def upperShriekPlusCompιIsoPullbackTensor [Perfect f.left] :
    upperShriekPlus f j ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ quasiCoherentDerivedPullback' f.left ⋙
        (quasiCoherentDerivedTensor X.left).flip.obj
          ((upperShriek f j).obj (DerivedPushforward.derivedStructureSheaf Y.left)) :=
  NatIso.ofComponents
    (fun K => (@asIso _ _ _ _ (upperShriekCompareWithPullbackCanonical f j K.obj)
      (isIso_upperShriekCompareWithPullback f j K.obj K.property)).symm)
    (fun {K K'} h =>
      (@IsIso.comp_inv_eq _ _ _ _ _ _ (isIso_upperShriekCompareWithPullback f j K'.obj K'.property)
        _ _).2 (((Category.assoc _ _ _).trans
        ((congrArg (@inv _ _ _ _ (upperShriekCompareWithPullbackCanonical f j K.obj)
            (isIso_upperShriekCompareWithPullback f j K.obj K.property) ≫ ·)
          (upperShriekCompareWithPullbackCanonical_naturality f j h.hom)).trans
          (@IsIso.inv_hom_id_assoc _ _ _ _ _
            (isIso_upperShriekCompareWithPullback f j K.obj K.property) _ _))).symm))

end Main

variable (j : CompactificationOf (Over.mk (affineLineProj Y).left))

/-- **`f^!𝒪_Y ≅ 𝒪_{𝔸¹_Y}[1]`** in `D_QCoh(𝒪_{𝔸¹_Y})` for the projection `f : 𝔸¹_Y ⟶ Y`. -/
theorem nonempty_upperShriek_structureSheaf_affineLineProj_iso :
    Nonempty ((upperShriek (affineLineProj Y) j).obj
        (DerivedPushforward.derivedStructureSheaf Y.left) ≅
      (DerivedPushforward.derivedStructureSheaf (affineLineFTS Y).left)⟦(1 : ℤ)⟧) := by
  obtain ⟨e₁⟩ := nonempty_relativeDualizingComplexObj_iso_shift _ j
    (isCohenMacaulay_affineLineProj Y) 1 (topologicalKrullDimAt_fiber_affineLineProj Y)
  obtain ⟨e₂⟩ := nonempty_upperShriekHomology_affineLineProj_iso Y j
  exact ⟨ObjectProperty.isoMk _ (e₁ ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso e₂) ≪≫
    (((ObjectProperty.ι _).commShiftIso (1 : ℤ)).app
      (DerivedPushforward.derivedStructureSheaf (affineLineFTS Y).left)).symm)⟩

/-- **Stacks Project, Tag 0AA1 (Lemma 48.17.3).** In Situation 48.16.1 let `Y` be an object of
`FTS S` and let `f : X = 𝔸¹_Y ⟶ Y` be the projection. Then there is a (noncanonical) isomorphism
`f^!(-) ≅ Lf^*(-)[1]` of functors on `D⁺_QCoh(𝒪_Y)`, with `f^!` computed at any compactification
`j` of `f`.

The proof is through the isomorphisms `μ_{f,K} : Lf^*K ⊗ᴸ f^!𝒪_Y ≅ f^!K` of
[Stacks, Tag 0B6U] (e), `f` being smooth, together with `f^!𝒪_Y ≅ 𝒪_X[1]`: the source's
`𝒪_{ℙ¹_Y}(-2)|_X ≅ 𝒪_X` is replaced by the fundamental class of [Stacks, Tag 0E9Z] for
`X ⊆ ℙ¹_Y ⟶ Y` and the triviality of `Ω_{X/Y}`. -/
@[stacks 0AA1]
theorem nonempty_upperShriekPlus_affineLineProj_iso :
    Nonempty (upperShriekPlus (affineLineProj Y) j ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ quasiCoherentDerivedPullback' (affineLineProj Y).left ⋙
        shiftFunctor (quasiCoherentDerivedCategory (affineLineFTS Y).left) (1 : ℤ)) := by
  obtain ⟨e⟩ := nonempty_upperShriek_structureSheaf_affineLineProj_iso Y j
  exact ⟨upperShriekPlusCompιIsoPullbackTensor _ j ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι _ ⋙
      quasiCoherentDerivedPullback' (affineLineProj Y).left)
      ((quasiCoherentDerivedTensor (affineLineFTS Y).left).flip.mapIso e ≪≫
        quasiCoherentDerivedTensorFlipObjShiftIso _ 1)⟩

end Stacks.Duality

end
