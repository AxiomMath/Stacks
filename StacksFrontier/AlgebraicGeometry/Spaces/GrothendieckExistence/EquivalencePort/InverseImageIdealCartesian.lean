module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.InverseImageIdealAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSubmodules
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# The inverse-image ideal of a quasi-coherent ideal is cartesian on affine charts

Let `f : Y ⟶ X` be a representable morphism of algebraic spaces over a scheme `S` and let
`I ⊆ 𝒪_X` be a sheaf of ideals cartesian on affine charts whose sections over the affine charts
are finitely generated ideals (for instance a quasi-coherent sheaf of ideals on a locally
Noetherian algebraic space).  Then the inverse-image ideal `f⁻¹I · 𝒪_Y` is again cartesian on
affine charts: over every affine chart `V` of `Y` lying over the base change `Q ×_X Y` of an
affine chart `Q` of `X` it is spanned by the finitely many restricted pullbacks of generators of
`I(Q)` (`AlgebraicGeometry.Space.C1573.pullbackIdealSubsheaf_obj_of_isAffine`), and such charts
cover `Y`; a family of submodules of `𝒪_Y` locally spanned in this way is cartesian on affine
charts (`AlgebraicGeometry.Space.ChartSubmodule.isCartesianOnAffineCharts_toSubmodule`).

## Main results

* `AlgebraicGeometry.Space.C1573.pullbackIdealChartSubmodule`: the inverse-image ideal as a locally
  spanned family of submodules of `𝒪_Y`.
* `AlgebraicGeometry.Space.C1573.isCartesianOnAffineCharts_pullbackIdealSubsheaf`:
  **the inverse-image ideal is cartesian on affine charts.**

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : yoneda.relativelyRepresentable f.hom)
  (I : (SheafOfModules.unit (smallEtaleRingSheaf B S hS X.1 X.2)).Submodule)

/-- An affine chart of `Y` lying over the base change of an affine chart of `X` is a chart at
which the inverse-image ideal is spanned by finitely many sections, as soon as the ideals of
sections of `I` over the affine charts of `X` are finitely generated. -/
theorem C1573.isSpannedAt_pullbackIdealSubsheaf
    (hI : IsCartesianOnAffineCharts (hF := X.2) I.toSheafOfModules)
    (hfg : ∀ Q : SmallEtale B S hS X.1, IsAffine (chartScheme Q) →
      (chartSectionsIdeal B S hS X I Q).FG)
    (Q : SmallEtale B S hS X.1) (hQ : IsAffine (chartScheme Q))
    (T₁ : SmallEtale B S hS Y.1) (v : T₁ ⟶ (smallBaseChange B S hS f hf).obj Q)
    (hT₁ : IsAffine (chartScheme T₁)) :
    IsSpannedAt (X := Y.1) (hX := Y.2) (SheafOfModules.unit (smallEtaleRingSheaf B S hS Y.1 Y.2))
      (π := 𝟙 Y.1) (fun T _ _ => (pullbackIdealSubsheaf B S hS f hf I).obj (op T))
      T₁ T₁.1.hom (Category.comp_id _) := by
  obtain ⟨g, hg⟩ := hfg Q hQ
  refine ⟨hT₁, (chartSectionsRestrict B S hS Y v ∘ chartIdealPullbackHom B S hS f hf Q) '' g,
    (g.finite_toSet.image _), ?_, fun {T₂} h hT₂ => ?_⟩
  · change chartSectionsIdeal B S hS Y (pullbackIdealSubsheaf B S hS f hf I) T₁ = _
    rw [pullbackIdealSubsheaf_obj_of_isAffine B S hS f hf I hI Q hQ T₁ v hT₁, ← hg,
      Ideal.map_span, Ideal.map_span, Set.image_image]
    rfl
  · change chartSectionsIdeal B S hS Y (pullbackIdealSubsheaf B S hS f hf I) T₂ = _
    rw [pullbackIdealSubsheaf_obj_of_isAffine B S hS f hf I hI Q hQ T₂ (h ≫ v) hT₂, ← hg,
      Ideal.map_span, Ideal.map_span, Set.image_image, Set.image_image]
    refine congrArg (Submodule.span _) (Set.image_congr fun a _ => ?_)
    change ((smallEtaleRingSheaf B S hS Y.1 Y.2).obj.map (h ≫ v).op).hom _ =
      ((smallEtaleRingSheaf B S hS Y.1 Y.2).obj.map h.op).hom
        (((smallEtaleRingSheaf B S hS Y.1 Y.2).obj.map v.op).hom _)
    rw [op_comp, Functor.map_comp]
    rfl

/-- **A sieve on a chart of `Y` containing every affine chart lying over the base change of an
affine chart of `X` is covering.**  The base changes of the affine charts of `X` cover `Y`
(`AlgebraicGeometry.Space.coversTop_smallBaseChange_affineCharts`), and every chart is covered
by affine ones (`AlgebraicGeometry.Space.SmallEtale.exists_affine_etale_ofArrows`). -/
theorem C1573.mem_topology_of_affine_over_smallBaseChange (T : SmallEtale B S hS Y.1) (R : Sieve T)
    (hR : ∀ {T₁ : SmallEtale B S hS Y.1} (g : T₁ ⟶ T), IsAffine (chartScheme T₁) →
      ∀ (Q : SmallEtale B S hS X.1), IsAffine (chartScheme Q) →
        (T₁ ⟶ (smallBaseChange B S hS f hf).obj Q) → R g) :
    R ∈ SmallEtale.topology B S hS Y.1 T := by
  have hcov := (coversTop_smallBaseChange_affineCharts B S hS f hf) T
  refine (SmallEtale.topology B S hS Y.1).transitive hcov R fun {T₂} g hg => ?_
  obtain ⟨⟨Q, hQ⟩, ⟨v⟩⟩ := hg
  obtain ⟨I, Z, a, haff, hZ, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS Y.1 T₂
  refine (SmallEtale.topology B S hS Y.1).superset_covering ?_ hZ
  rintro W k ⟨W', h, g', ⟨j⟩, rfl⟩
  have := R.downward_closed (hR (a j ≫ g) (haff j) Q hQ (a j ≫ v)) h
  rwa [← Category.assoc] at this

/-- **The inverse-image ideal as a locally spanned family of submodules of `𝒪_Y`.** -/
def C1573.pullbackIdealChartSubmodule
    (hI : IsCartesianOnAffineCharts (hF := X.2) I.toSheafOfModules)
    (hfg : ∀ Q : SmallEtale B S hS X.1, IsAffine (chartScheme Q) →
      (chartSectionsIdeal B S hS X I Q).FG) :
    ChartSubmodule (X := Y.1) (hX := Y.2)
      (SheafOfModules.unit (smallEtaleRingSheaf B S hS Y.1 Y.2)) (𝟙 Y.1) where
  obj T _ _ := (pullbackIdealSubsheaf B S hS f hf I).obj (op T)
  map g _ _ _ hσ := (pullbackIdealSubsheaf B S hS f hf I).map_mem g.op hσ
  loc T _ _ σ R hR h := (pullbackIdealSubsheaf B S hS f hf I).isSheaf σ
    ((SmallEtale.topology B S hS Y.1).superset_covering (fun _ g hg => h g hg) hR)
  lfg T a ha := by
    refine mem_topology_of_affine_over_smallBaseChange B S hS f hf T _
      fun {T₁} g hT₁ Q hQ v => ?_
    apply Sieve.le_generate
    have hw : yoneda.map g.hom.left ≫ a = T₁.1.hom := by
      rw [← Category.comp_id a, ha]
      exact CostructuredArrow.w g.hom
    have h := isSpannedAt_pullbackIdealSubsheaf B S hS f hf I hI hfg Q hQ T₁ v hT₁
    exact h.congr hw.symm _

/-- **The inverse-image ideal `f⁻¹I · 𝒪_Y` of a sheaf of ideals cartesian on affine charts, with
finitely generated ideals of sections over the affine charts, is cartesian on affine charts.** -/
theorem C1573.isCartesianOnAffineCharts_pullbackIdealSubsheaf
    (hI : IsCartesianOnAffineCharts (hF := X.2) I.toSheafOfModules)
    (hfg : ∀ Q : SmallEtale B S hS X.1, IsAffine (chartScheme Q) →
      (chartSectionsIdeal B S hS X I Q).FG) :
    IsCartesianOnAffineCharts (hF := Y.2)
      (pullbackIdealSubsheaf B S hS f hf I).toSheafOfModules := by
  have h := (pullbackIdealChartSubmodule B S hS f hf I hI hfg).isCartesianOnAffineCharts_toSubmodule
    (isCartesianOnAffineCharts_unit (hF := Y.2))
  exact h

end AlgebraicGeometry.Space

end
