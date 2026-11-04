module

public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageOverOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.LocallyPrincipal

/-!
# Self-intersection numbers of pullbacks along a morphism of proper varieties of equal dimension

Let `k` be a field and `f : Y ⟶ X` a morphism of integral schemes proper over `k`, both of
dimension `d`, and `𝓛` an invertible `𝒪_X`-module. [Stacks, Tag 0BET] gives

* `(f^*𝓛^d · Y) = deg(f) (𝓛^d · X)` if `f` is dominant, and
* `(f^*𝓛^d · Y) = 0` if `f` is not dominant (and `d ≥ 1`),

with `deg(f) = [R(Y) : R(X)]` the degree of [Stacks, Tag 02NY].

## Main results

* `AlgebraicGeometry.selfIntersectionNumber_pullback_of_isDominant`.
* `AlgebraicGeometry.selfIntersectionNumber_pullback_eq_zero_of_not_isDominant`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {Y X : Scheme.{u}} (pY : Y ⟶ Spec (.of k))
  (pX : X ⟶ Spec (.of k)) [IsProper pY] [IsProper pX] [IsIntegral Y] [IsIntegral X]
  (f : Y ⟶ X) (hf : f ≫ pX = pY) (d : ℕ)

include hf

/-- **[Stacks, Tag 0BET] for a dominant morphism of proper varieties of the same dimension.**
`(f^*𝓛^d · Y) = deg(f) (𝓛^d · X)`. -/
theorem selfIntersectionNumber_pullback_of_isDominant [IsDominant f] [LocallyOfFiniteType f]
    (hY : topologicalKrullDim Y = (d : WithBot ℕ∞)) (hX : topologicalKrullDim X = (d : WithBot ℕ∞))
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    selfIntersectionNumber k pY (𝟙 Y) d hY.le ((Scheme.Modules.pullback f).obj L) =
      (degreeOver f : ℤ) * selfIntersectionNumber k pX (𝟙 X) d hX.le L := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  have hP : IsProper (𝟙 Y ≫ f) := isProper_comp_of_structureMap k pY pX f hf (𝟙 Y)
  have : IsProper f := by
    have : IsProper (f ≫ pX) := by rw [hf]; infer_instance
    exact IsProper.of_comp f pX
  have : Surjective (𝟙 Y ≫ f) := by
    rw [Category.id_comp]
    refine ⟨fun x => ?_⟩
    have hx := (isDominant_iff f).mp ‹IsDominant f› x
    rwa [f.isClosedMap.isClosed_range.closure_eq] at hx
  have : Surjective (𝟙 Y ≫ f).imageι := surjective_imageι (𝟙 Y ≫ f)
  have : IsIso (𝟙 Y ≫ f).imageι :=
    isIso_of_isClosedImmersion_of_surjective (𝟙 Y ≫ f).imageι
  have : IsIntegral (𝟙 Y ≫ f).image := Stacks.Chow.isIntegral_image (𝟙 Y ≫ f)
  have : IsProper (𝟙 Y ≫ f).toImage := Stacks.Chow.isProper_toImage (𝟙 Y ≫ f)
  have hIm : topologicalKrullDim (𝟙 Y ≫ f).image = (d : WithBot ℕ∞) :=
    (IsHomeomorph.topologicalKrullDim_eq (𝟙 Y ≫ f).imageι
      (isHomeomorph_iff_isEmbedding_surjective.mpr
        ⟨(𝟙 Y ≫ f).imageι.isEmbedding, (𝟙 Y ≫ f).imageι.surjective⟩)).trans hX
  have hpull := intersectionNumber_pullback_eq_degreeOver_mul k pY pX f hf (𝟙 Y) d hY
    (fun _ : Fin d => L) hIm
  have : IsDominant (𝟙 Y ≫ f).toImage := by
    refine (isDominant_iff _).mpr (Function.Surjective.denseRange fun y => ?_)
    obtain ⟨a, ha⟩ := (𝟙 Y ≫ f).surjective ((𝟙 Y ≫ f).imageι y)
    refine ⟨a, imageι_injective (𝟙 Y ≫ f) ?_⟩
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι, ha]
  have hdeg : degreeOver f = degreeOver (𝟙 Y ≫ f).toImage :=
    degreeOver_eq_degreeOver_of_isIso f (𝟙 Y ≫ f).toImage (𝟙 Y ≫ f).imageι
      ((𝟙 Y ≫ f).toImage_imageι.trans (Category.id_comp f))
  have hint : intersectionNumber k pX (𝟙 Y ≫ f).imageι d hIm.le (fun _ : Fin d => L) =
      intersectionNumber k pX (𝟙 X) d hX.le (fun _ : Fin d => L) :=
    intersectionNumber_eq_intersectionNumber_id k pX (𝟙 Y ≫ f).imageι d hIm.le hX.le _
  rw [selfIntersectionNumber_eq_intersectionNumber, selfIntersectionNumber_eq_intersectionNumber,
    hpull, hdeg, hint]

/-- **[Stacks, Tag 0BET] for a morphism which is not dominant.** If `X` is integral of dimension
`d ≥ 1` and `f : Y ⟶ X` is not dominant, then `(f^*𝓛^d · Y) = 0`. -/
theorem selfIntersectionNumber_pullback_eq_zero_of_not_isDominant (hf' : ¬ IsDominant f)
    (hd0 : 0 < d) (hY : topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
    (hX : topologicalKrullDim X = (d : WithBot ℕ∞))
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    selfIntersectionNumber k pY (𝟙 Y) d hY ((Scheme.Modules.pullback f).obj L) = 0 := by
  have hP : IsProper (𝟙 Y ≫ f) := isProper_comp_of_structureMap k pY pX f hf (𝟙 Y)
  set V : Set X := Set.range (𝟙 Y ≫ f).imageι with hV
  have hVc : IsClosed V := (𝟙 Y ≫ f).imageι.isClosedEmbedding.isClosed_range
  have hVne : V ≠ Set.univ := by
    intro h
    apply hf'
    refine (isDominant_iff f).mpr ?_
    rw [DenseRange, Dense]
    intro x
    have hx : x ∈ V := h ▸ Set.mem_univ x
    rw [hV, range_imageι_eq_closure_range, Category.id_comp] at hx
    exact hx
  have hdimV : topologicalKrullDim (𝟙 Y ≫ f).image = topologicalKrullDim V :=
    IsHomeomorph.topologicalKrullDim_eq _
      (Topology.IsEmbedding.toHomeomorph (𝟙 Y ≫ f).imageι.isEmbedding).isHomeomorph
  have hlt : topologicalKrullDim (𝟙 Y ≫ f).image < (d : WithBot ℕ∞) := by
    rw [hdimV]
    have huniv : topologicalKrullDim (↥(Set.univ : Set X)) = topologicalKrullDim X :=
      (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq
    have := topologicalKrullDim_le_pred_of_ssubset hVc (IrreducibleSpace.isIrreducible_univ X)
      (lt_of_le_of_ne (Set.subset_univ V) hVne) (n := d) (by rw [huniv, hX])
    refine lt_of_le_of_lt this ?_
    exact_mod_cast Nat.sub_lt hd0 one_pos
  rw [selfIntersectionNumber_eq_intersectionNumber]
  exact intersectionNumber_pullback_eq_zero k pY pX f hf (𝟙 Y) d hY (fun _ => L) hlt

end AlgebraicGeometry
