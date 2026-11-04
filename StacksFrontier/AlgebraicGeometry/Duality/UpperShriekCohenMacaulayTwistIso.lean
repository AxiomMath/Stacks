module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekCohenMacaulayTwist
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplexOfCharts
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekPerfectComparison
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Flat
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekPullbackComparisonCanonicalMaps

/-!
# `f^!K = Lf^*K ⊗ᴸ ω_{X/Y}[d]` for a Cohen–Macaulay morphism

For a Cohen–Macaulay morphism `f : X ⟶ Y` of `FTS S` of relative dimension `d`, with
`ω_{X/Y} = H^{-d}(f^!𝒪_Y)`, there are isomorphisms `f^!K ≅ Lf^*K ⊗ᴸ ω_{X/Y}[d]` for
`K ∈ D⁺_QCoh(𝒪_Y)`, hence `ω_X^• ≅ Lf^*ω_Y^• ⊗ᴸ ω_{X/Y}[d]` for upper shriek complexes over a
common base, and `ω_X = f^*ω_Y ⊗ ω_{X/Y}` for connected Cohen–Macaulay `Y` and a dualizing complex
on the base ([Stacks, Tag 0C10]).
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

open DerivedPushforward

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f.left))

/-- A Cohen–Macaulay morphism of `FTS S` is perfect. -/
theorem perfect_of_isCohenMacaulay
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f)) : Perfect f.left := by
  have h := (isCohenMacaulay_iff_flat_and_fibers f.left (isLocallyNoetherian_fiber_left f)).mp hCM
  have : Flat f.left := h.1
  have := locallyOfFinitePresentation_left f
  infer_instance

/-- For a Cohen–Macaulay morphism, the canonical comparison `μ_{f,K}` of Tag 0B6U is an
isomorphism for bounded below `K`. -/
private def upperShriekCompareWithPullbackIsoOfCohenMacaulay
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f))
    (K : quasiCoherentDerivedCategory Y.left) (hK : DerivedCategoryB.IsBoundedBelow K.obj) :=
  have := perfect_of_isCohenMacaulay f hCM
  have := isIso_upperShriekCompareWithPullback f j K hK
  asIso (upperShriekCompareWithPullbackCanonical f j K)

/-- **Stacks Project, Tag 0C10, the canonical isomorphism.** For a Cohen–Macaulay morphism
`f : X ⟶ Y` of `FTS S` of relative dimension `d` and `K ∈ D⁺_QCoh(𝒪_Y)`,
`f^!K ≅ Lf^*K ⊗ᴸ ω_{X/Y}[d]`, through `μ_{f,K}` of Tag 0B6U. -/
@[stacks 0C10 "f^!K = Lf^*K (x) omega_{X/Y}[d] for K in D^+_QCoh"]
theorem nonempty_upperShriek_iso_pullback_tensor_shift
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f)) (d : ℕ)
    (hd : ∀ x : X.left,
      topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) = (d : WithBot ℕ∞))
    (K : quasiCoherentDerivedCategory Y.left) (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    Nonempty ((upperShriek f j).obj K ≅
      ((quasiCoherentDerivedTensor X.left).obj
        ((quasiCoherentDerivedPullback' f.left).obj K)).obj
          (relativeDualizingSheafShift f j hCM d hd)) :=
  nonempty_upperShriek_iso_pullback_tensor_shift_of_iso f j hCM d hd K
    (upperShriekCompareWithPullbackIsoOfCohenMacaulay f j hCM K hK)

/-- **Stacks Project, Tag 0C10, "in particular".** For `πY : Y ⟶ T`, `πX = f ≫ πY` and
`ω_T ∈ D⁺_QCoh(𝒪_T)` (for instance a dualizing complex), with `ω_Y = πY^!ω_T` and
`ω_X = πX^!ω_T`: `ω_X ≅ Lf^*ω_Y ⊗ᴸ ω_{X/Y}[d]`. -/
@[stacks 0C10 "omega_X = Lf^* omega_Y (x) omega_{X/Y}[d]"]
theorem nonempty_upperShriek_comp_iso_pullback_tensor_shift
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f)) (d : ℕ)
    (hd : ∀ x : X.left,
      topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) = (d : WithBot ℕ∞))
    {T : FTS S} (πY : Y ⟶ T) (πX : X ⟶ T) (hπ : f ≫ πY = πX)
    (jY : CompactificationOf (Over.mk πY.left)) (jX : CompactificationOf (Over.mk πX.left))
    (ωT : quasiCoherentDerivedCategory T.left) (hωT : DerivedCategoryB.IsBoundedBelow ωT.obj) :
    Nonempty ((upperShriek πX jX).obj ωT ≅
      ((quasiCoherentDerivedTensor X.left).obj
        ((quasiCoherentDerivedPullback' f.left).obj ((upperShriek πY jY).obj ωT))).obj
          (relativeDualizingSheafShift f j hCM d hd)) :=
  nonempty_upperShriek_comp_iso_pullback_tensor_shift_of_iso f j hCM d hd πY πX hπ jY jX ωT hωT
    (upperShriekCompareWithPullbackIsoOfCohenMacaulay f j hCM _
      (isBoundedBelow_upperShriek_obj πY jY ωT hωT))

/-- **Stacks Project, Tag 0C10, the dualizing modules.** If moreover `ω_T` is a dualizing
complex and `Y` is connected and Cohen–Macaulay, then `ω_Y^•` and `ω_X^•` are concentrated in
single degrees `m` and `m - d`, and their cohomology sheaves `ω_Y`, `ω_X` there satisfy
`ω_X ≅ f^*ω_Y ⊗ ω_{X/Y}`. (Connectedness and Cohen–Macaulayness of `X` are not needed.) -/
@[stacks 0C10 "omega_X = f^* omega_Y (x) omega_{X/Y} for connected Cohen-Macaulay schemes"]
theorem exists_homology_upperShriek_comp_iso_pullback_tensor
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f)) (d : ℕ)
    (hd : ∀ x : X.left,
      topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) = (d : WithBot ℕ∞))
    {T : FTS S} (πY : Y ⟶ T) (πX : X ⟶ T) (hπ : f ≫ πY = πX)
    (jY : CompactificationOf (Over.mk πY.left)) (jX : CompactificationOf (Over.mk πX.left))
    (ωT : quasiCoherentDerivedCategory T.left) (hωT : IsDualizingComplex ωT.obj)
    [ConnectedSpace Y.left] (hY : AlgebraicGeometry.IsCohenMacaulay Y.left) :
    ∃ m : ℤ,
      (∀ i : ℤ, i ≠ m → IsZero ((DerivedCategory.homologyFunctor Y.left.Modules i).obj
        ((upperShriek πY jY).obj ωT).obj)) ∧
      (∀ i : ℤ, i ≠ m - d → IsZero ((DerivedCategory.homologyFunctor X.left.Modules i).obj
        ((upperShriek πX jX).obj ωT).obj)) ∧
      Nonempty ((DerivedCategory.homologyFunctor X.left.Modules (m - d)).obj
          ((upperShriek πX jX).obj ωT).obj ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.left.sheaf).obj
          ((Scheme.Modules.pullback f.left).obj
            ((DerivedCategory.homologyFunctor Y.left.Modules m).obj
              ((upperShriek πY jY).obj ωT).obj))).obj (relativeDualizingSheaf f j d)) :=
  have hb := isBoundedBelow_of_isDualizingComplex _ hωT
  exists_homology_upperShriek_comp_iso_pullback_tensor_of_iso f j hCM d hd πY πX hπ jY jX ωT hb
    hY (isDualizingComplex_upperShriek_obj πY jY ωT hωT)
    (upperShriekCompareWithPullbackIsoOfCohenMacaulay f j hCM _
      (isBoundedBelow_upperShriek_obj πY jY ωT hb))

end Stacks.Duality
