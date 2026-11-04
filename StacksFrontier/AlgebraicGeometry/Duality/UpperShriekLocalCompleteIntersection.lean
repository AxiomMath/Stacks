module

public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.CompactPerfect
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.InvertibleLocal
public import StacksFrontier.AlgebraicGeometry.Duality.InternalHom.LocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekPerfectComparison
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekStructureSheafCharts
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Perfect
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.NaiveCotangent
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.CompleteIntersection
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TensorProduct
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
import StacksCore.Tactic.StacksAttribute

/-!
# `f^!` of a local complete intersection morphism

Let `S` be a Noetherian scheme and `f : X ⟶ Y` a local complete intersection morphism of
`AlgebraicGeometry.FTS S`, with `f^!` computed at any compactification. Then `f^!𝒪_Y` is an
invertible object of `D(𝒪_X)`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

section Chart

attribute [local instance 10000] HasDerivedCategory.standard

/-- **On an affine open the sheaf associated to an invertible complex is perfect.** An invertible
object of `D(Γ(X, U))` is perfect ([Stacks, Tag 0FNT]), its associated complex on
`Spec Γ(X, U)` is perfect ([Stacks, Tag 08EB]), and restriction along `U ≅ Spec Γ(X, U)`
preserves perfectness. -/
theorem isPerfect_tilde_restrict_of_isInvertible_standard {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {K : DerivedCategory (ModuleCat.{u} Γ(X, U))}
    (hK : letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
        Γ(X, U)).choose
      MonoidalCategory.IsInvertible K) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := U.toScheme.toRingedSpace)
      ((tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj K) := by
  have hP := ((DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit K).2 hK).1
  have h₀ := (AlgebraicGeometry.isPerfect_tilde_iff K).2 hP
  have h₁ := InternalHom.isPerfect_restrictFunctor_mapDerivedCategory hU.isoSpec.hom _ h₀
  let e := (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso
      (tilde.functor Γ(X, U)) (Scheme.Modules.restrictFunctor hU.isoSpec.hom)).app K
  exact (Stacks.Cohomology.PerfectComplexes.isClosedUnderIsomorphisms_isPerfect
    (X := U.toScheme.toRingedSpace)).of_iso e.symm h₁

end Chart

/-- **On an affine open the sheaf associated to an invertible complex is perfect**, read in
`D(𝒪_U)` at the locally small model. -/
theorem isPerfect_tilde_restrict_of_isInvertible {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U)
    {K : @DerivedCategory (ModuleCat.{u} Γ(X, U)) _ _ (HasDerivedCategory.standard _)}
    (hK : letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
        Γ(X, U)).choose
      MonoidalCategory.IsInvertible K) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := U.toScheme.toRingedSpace)
      (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _ _
        (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) _ _ _ |>.obj
          K) := by
  have h := (PerfectApproximation.isPerfect_standard_iff _).1
    (isPerfect_tilde_restrict_of_isInvertible_standard hU hK)
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    ((Stacks.Injectives.mapDerivedCategoryTargetModelIso U.toScheme.Modules
      (hd₁ := HasDerivedCategory.standard _)
      (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom)).app K) h

variable {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {X Y : AlgebraicGeometry.FTS S}
  (f : X ⟶ Y) (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- **The chart model of `f^!𝒪_Y` is invertible for a local complete intersection.** For affine
opens `U ⊆ f⁻¹(V)` and a polynomial presentation `p` of `Γ(Y, V) → Γ(X, U)`, the algebraic upper
shriek `ω_{Γ(X, U)/Γ(Y, V)}` along `p` of `Γ(Y, V)` is an invertible object of `D(Γ(X, U))`
([Stacks, Tag 0E4B]): the chart ring map is a local complete intersection homomorphism. -/
theorem isInvertible_upperShriekFunctor_structureModel_of_isLocalCompleteIntersection
    (hf : IsLocalCompleteIntersectionMorphism f.left) {V : Y.left.Opens} (hV : IsAffineOpen V)
    {U : X.left.Opens} (hU : IsAffineOpen U) (hUV : U ≤ f.left ⁻¹ᵁ V)
    (p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
      Γ(X.left, U)).choose
    MonoidalCategory.IsInvertible
      (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V)) := by
  have hYn : IsLocallyNoetherian Y.left := by
    have : IsLocallyNoetherian ((Functor.fromPUnit S).obj Y.right) :=
      inferInstanceAs (IsLocallyNoetherian S)
    exact LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hlci := NaiveCotangentLocalCompleteIntersection.isLocalCompleteIntersection_appLE
    f.left hf hV hU hUV
  open Dualizing.PolynomialPresentation in
  have hK := isInvertible_upperShriekFunctor_obj_unit_of_isLocalCompleteIntersection p hlci
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(Y.left, V))
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    Γ(X.left, U)).choose
  let ι : (DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Y.left, V)) 0).obj
        (ModuleCat.of Γ(Y.left, V) (ULift.{u} Γ(Y.left, V))) ≅ structureModel (Y := Y) V :=
    (DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Y.left, V)) 0).mapIso
      (ULift.moduleEquiv.toModuleIso)
  exact MonoidalCategory.isInvertible_of_iso (p.upperShriekFunctor.{u, u}.mapIso ι) hK

/-- **On an affine chart `f^!𝒪_Y` of a local complete intersection morphism is invertible.** For
affine opens `U ⊆ f⁻¹(V)`, the restriction of `f^!𝒪_Y` to `U` is the associated sheaf of
`ω_{Γ(X, U)/Γ(Y, V)}` ([Stacks, Tag 0BV2]), which is invertible ([Stacks, Tag 0E4B]). -/
theorem isInvertible_restrict_relativeDualizingComplexObj_of_isLocalCompleteIntersection
    (hf : IsLocalCompleteIntersectionMorphism f.left) {V : Y.left.Opens} (hV : IsAffineOpen V)
    {U : X.left.Opens} (hU : IsAffineOpen U) (hUV : U ≤ f.left ⁻¹ᵁ V) :
    letI := Scheme.Modules.derivedMonoidal U.toScheme
    MonoidalCategory.IsInvertible
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
        (relativeDualizingComplexObj f j)) := by
  have := locallyOfFiniteType_left f
  obtain ⟨p⟩ := Dualizing.nonempty_polynomialPresentation (f.left.appLE V U hUV).hom
    (f.left.finiteType_appLE hV hU hUV)
  have hT := isInvertible_tilde_restrict_of_isInvertible hU
    (isInvertible_upperShriekFunctor_structureModel_of_isLocalCompleteIntersection f hf hV hU hUV p)
  obtain ⟨e⟩ := upperShriekStructureSheafCharts f j V hV U hU hUV p
  exact @MonoidalCategory.isInvertible_of_iso _ _ (Scheme.Modules.derivedMonoidal U.toScheme) _ _
    e.symm hT

/-- **On an affine chart `f^!𝒪_Y` of a local complete intersection morphism is perfect.** -/
theorem isPerfect_restrict_relativeDualizingComplexObj_of_isLocalCompleteIntersection
    (hf : IsLocalCompleteIntersectionMorphism f.left) {V : Y.left.Opens} (hV : IsAffineOpen V)
    {U : X.left.Opens} (hU : IsAffineOpen U) (hUV : U ≤ f.left ⁻¹ᵁ V) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := U.toScheme.toRingedSpace)
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
        (relativeDualizingComplexObj f j)) := by
  have := locallyOfFiniteType_left f
  obtain ⟨p⟩ := Dualizing.nonempty_polynomialPresentation (f.left.appLE V U hUV).hom
    (f.left.finiteType_appLE hV hU hUV)
  have hT := isPerfect_tilde_restrict_of_isInvertible hU
    (isInvertible_upperShriekFunctor_structureModel_of_isLocalCompleteIntersection f hf hV hU hUV p)
  obtain ⟨e⟩ := upperShriekStructureSheafCharts f j V hV U hU hUV p
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso e.symm hT

omit [AlgebraicGeometry.IsNoetherian S] in
/-- Every point of `X` lies in an affine open of `X` mapping into an affine open of `Y`. -/
theorem exists_affine_chart (x : X.left) :
    ∃ (V : Y.left.Opens) (_ : IsAffineOpen V) (U : X.left.Opens) (_ : IsAffineOpen U)
      (_ : U ≤ f.left ⁻¹ᵁ V), x ∈ U := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.left x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUsub⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((f.left ⁻¹ᵁ V : X.left.Opens) : Set X.left) from hxV) (f.left ⁻¹ᵁ V).isOpen
  exact ⟨V, hV, U, hU, hUsub, hxU⟩

/-- **`f^!𝒪_Y` is invertible for a local complete intersection morphism** `f` of `FTS S`: it is
invertible on the affine charts, which cover `X`, and invertibility is local. -/
theorem isInvertible_relativeDualizingComplexObj_of_isLocalCompleteIntersection
    (hf : IsLocalCompleteIntersectionMorphism f.left) :
    letI := Scheme.Modules.derivedMonoidal X.left
    MonoidalCategory.IsInvertible (relativeDualizingComplexObj f j) := by
  choose V hV U hU hUV hxU using exists_affine_chart f
  refine isInvertible_of_isInvertible_restrictFunctor U ?_ _ fun x =>
    isInvertible_restrict_relativeDualizingComplexObj_of_isLocalCompleteIntersection f j hf
      (hV x) (hU x) (hUV x)
  exact eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩

/-- **`f^!𝒪_Y` is perfect for a local complete intersection morphism** `f` of `FTS S`: it is
perfect on the affine charts, which cover `X`, and perfectness is local. -/
theorem isPerfect_relativeDualizingComplexObj_of_isLocalCompleteIntersection
    (hf : IsLocalCompleteIntersectionMorphism f.left) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace)
      (relativeDualizingComplexObj f j) := by
  refine CompactPerfect.isPerfect_of_isPerfect_derivedRestrict _ fun x => ?_
  obtain ⟨V, hV, U, hU, hUV, hxU⟩ := exists_affine_chart f x
  exact ⟨U, hxU,
    isPerfect_restrict_relativeDualizingComplexObj_of_isLocalCompleteIntersection f j hf hV hU hUV⟩

/-- **`f^!` preserves perfect objects for a local complete intersection morphism.** For `K` a
perfect object of `D_QCoh(𝒪_Y)`, `f^!K ≅ Lf^*K ⊗ᴸ f^!𝒪_Y` ([Stacks, Tag 0B6U] (e), `f` being
perfect by [Stacks, Tag 069H]), and both factors are perfect. -/
theorem isPerfect_upperShriek_of_isLocalCompleteIntersection
    (hf : IsLocalCompleteIntersectionMorphism f.left) (K : quasiCoherentDerivedCategory Y.left)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.left.toRingedSpace) K.obj) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace)
      ((upperShriek f j).obj K).obj := by
  have : Perfect f.left := perfect_of_isLocalCompleteIntersectionMorphism hf
  have : AlgebraicGeometry.IsNoetherian Y.left := ⟨⟩
  have hKb := isBoundedBelow_of_isCompactObject K (isCompactObject_of_isPerfect K hK)
  obtain ⟨e⟩ := nonempty_upperShriek_iso_pullback_tensor f j K hKb
  refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    ((ObjectProperty.ι _).mapIso e) ?_
  exact RingedSpace.isPerfect_derivedTensorProduct X.left.toRingedSpace _ _ _
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
      (hX := Scheme.Modules.hasDerivedCategory X.left)
      (hY := Scheme.Modules.hasDerivedCategory Y.left) f.left.toLRSHom.toShHom K.obj hK)
    (isPerfect_relativeDualizingComplexObj_of_isLocalCompleteIntersection f j hf)

/-- **Stacks Project, Tag 0B6V (Lemma 48.17.11).** In Situation 48.16.1 let `f : X ⟶ Y` be a
local complete intersection morphism of `FTS S`. Then
1. `f^!𝒪_Y` is an invertible object of `D(𝒪_X)`, and
2. `f^!` maps perfect complexes to perfect complexes.

Here `f^!` is computed at an arbitrary compactification `j`. -/
@[stacks 0B6V]
theorem isInvertible_and_isPerfect_upperShriek_of_isLocalCompleteIntersection
    (hf : IsLocalCompleteIntersectionMorphism f.left) :
    (letI := Scheme.Modules.derivedMonoidal X.left;
      MonoidalCategory.IsInvertible (relativeDualizingComplexObj f j)) ∧
    ∀ K : quasiCoherentDerivedCategory Y.left,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.left.toRingedSpace) K.obj →
        Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace)
          ((upperShriek f j).obj K).obj :=
  ⟨isInvertible_relativeDualizingComplexObj_of_isLocalCompleteIntersection f j hf,
    isPerfect_upperShriek_of_isLocalCompleteIntersection f j hf⟩

end Stacks.Duality

end
