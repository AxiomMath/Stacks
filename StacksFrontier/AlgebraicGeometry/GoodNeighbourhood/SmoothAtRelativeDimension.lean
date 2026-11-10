module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.DimensionDrop
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.JacobsonDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent

/-!
# Smoothness at a point with the relative dimension read off the generic points

Let `T` be a closed subscheme of a scheme `X` locally of finite type over a field `k`, and `s` a
point of `T` at which `T` is smooth over `k`. If every generic point of `T` specializing to `s`
has dimension `e` (the `δ`-dimension of `Stacks.Chow.fieldChowSituation`), then `T` is smooth of
relative dimension `e` on a neighbourhood of `s`: a smooth scheme is normal, so `s` has an
integral open neighbourhood, whose dimension is that of its generic point (Tag 02QO) and whose
local dimension is the same everywhere.

## Main results

* `AlgebraicGeometry.GoodNeighbourhood.subschemeSmoothAt_of_smoothAt`: the statement above.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- **Smooth at a point, with the dimension of the generic points through it, is smooth of that
relative dimension near the point.** -/
theorem subschemeSmoothAt_of_smoothAt [LocallyOfFiniteType p] (T : X.IdealSheafData)
    (s : T.subscheme) (hs : InfinitesimalLifting.SmoothAt (T.subschemeι ≫ p) s) (e : ℕ)
    (he : ∀ η : T.subscheme, η ⤳ s → closure ({η} : Set T.subscheme) ∈
        irreducibleComponents T.subscheme →
      relativeDimension (fieldChowSituation k).dimensionFunction p (T.subschemeι η) = e) :
    SubschemeSmoothAt p T e (T.subschemeι s) := by
  have hsub : Subsingleton (Spec (.of k)) := by
    change Subsingleton (PrimeSpectrum k); infer_instance
  have : IsNormal (Spec (.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  obtain ⟨U, hsU, hU⟩ := hs
  have hUsm : Smooth (U.ι ≫ T.subschemeι ≫ p) := by
    rw [← Scheme.Hom.resLE_comp_ι (T.subschemeι ≫ p) (U := ⊤) (V := U) le_top]
    exact MorphismProperty.comp_mem @Smooth _ _ hU inferInstance
  have : IsLocallyNoetherian U.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ T.subschemeι ≫ p)
  have : IsNormal U.toScheme := isNormal_of_smooth (U.ι ≫ T.subschemeι ≫ p)
  obtain ⟨O, hsO, hO⟩ := exists_isIntegral_opens_of_isNormal U.toScheme ⟨s, hsU⟩
  set j : O.toScheme ⟶ T.subscheme := O.ι ≫ U.ι
  set g : O.toScheme ⟶ Spec (.of k) := j ≫ T.subschemeι ≫ p
  have : Smooth g := by
    simp only [g, j, Category.assoc]
    exact MorphismProperty.comp_mem @Smooth _ _ (inferInstance : Smooth O.ι) hUsm
  set s' : O.toScheme := ⟨⟨s, hsU⟩, hsO⟩
  have hjs : j s' = s := rfl
  -- the generic point of `O` is a generic point of `T` through `s`
  have hspec : genericPoint O.toScheme ⤳ s' :=
    (genericPoint_spec O.toScheme).specializes (Set.mem_univ _)
  have hδ : relativeDimension (fieldChowSituation k).dimensionFunction g
      (genericPoint O.toScheme) = e := by
    have h1 : relativeDimension (fieldChowSituation k).dimensionFunction g
        (genericPoint O.toScheme) = relativeDimension (fieldChowSituation k).dimensionFunction
          (T.subschemeι ≫ p) (j (genericPoint O.toScheme)) :=
      relativeDimension_comp_isOpenImmersion _ j (T.subschemeι ≫ p) _
    have h2 : relativeDimension (fieldChowSituation k).dimensionFunction (T.subschemeι ≫ p)
        (j (genericPoint O.toScheme)) = relativeDimension (fieldChowSituation k).dimensionFunction
          p (T.subschemeι (j (genericPoint O.toScheme))) :=
      relativeDimension_comp_closedImmersion _ T.subschemeι p _
    rw [h1, h2]
    exact he _ (hjs ▸ hspec.map j.continuous)
      (closure_singleton_mem_irreducibleComponents_of_isOpenImmersion j)
  have hdimO : topologicalKrullDim O.toScheme = (e : WithBot ℕ∞) := by
    have := topologicalKrullDim_eq_relativeDimension_toNat (fieldChowSituation k)
      (fun _ _ => rfl) (show O.toScheme ⟶ (fieldChowSituation k).S from g) (𝟙 O.toScheme)
      (genericPoint O.toScheme)
      ((IrreducibleSpace.isIrreducible_univ _).isGenericPoint_genericPoint isClosed_univ)
    have hid : (𝟙 O.toScheme : O.toScheme ⟶ O.toScheme) (genericPoint O.toScheme) =
        genericPoint O.toScheme := rfl
    have hδ' : relativeDimension (fieldDimensionFunction k) g (genericPoint O.toScheme) = e := hδ
    rw [this, hid, hδ']
    simp
  have hrel : SmoothOfRelativeDimension e g := by
    refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq _ e fun w => ?_
    rw [topologicalKrullDimAt_fiber_eq_of_subsingleton,
      topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional k O.toScheme g
        (TopologicalSpace.Equidimensional.of_preirreducibleSpace _) w, hdimO]
  refine ⟨s, rfl, j.opensRange, ⟨s', rfl⟩, ?_⟩
  have hiso : j.opensRange.ι = (Scheme.Hom.isoOpensRange j).inv ≫ j := by
    rw [Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]
  rw [hiso, Category.assoc]
  have h0 : SmoothOfRelativeDimension (0 + e) ((Scheme.Hom.isoOpensRange j).inv ≫ g) :=
    inferInstance
  rw [zero_add] at h0
  exact h0

end AlgebraicGeometry.GoodNeighbourhood

end
