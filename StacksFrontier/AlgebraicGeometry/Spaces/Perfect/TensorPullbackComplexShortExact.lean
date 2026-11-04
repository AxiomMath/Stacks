module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorPullbackComplexDerived
public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality

/-!
# `ℱ ↦ 𝒢^• ⊗ f^*ℱ` on short exact sequences

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `𝒢^•` a complex of `𝒪_X`-modules flat over
`Y`.  A short exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of `𝒪_Y`-modules gives a short exact
sequence of complexes `0 → 𝒢^• ⊗ f^*ℱ₁ → 𝒢^• ⊗ f^*ℱ₂ → 𝒢^• ⊗ f^*ℱ₃ → 0`: in each degree it is
`0 → 𝒢ⁿ ⊗ f^*ℱ₁ → 𝒢ⁿ ⊗ f^*ℱ₂ → 𝒢ⁿ ⊗ f^*ℱ₃ → 0`, exact as `𝒢ⁿ` is flat over `Y` (the step
"this sequence is exact because `𝒢ⁿ` is flat over `B`" of the proof of Stacks 0A1M).

## Main results

* `AlgebraicGeometry.Space.shortExact_tensorPullbackComplex_map_single`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleRingedTopos

variable (f : X ⟶ Y)
  (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)

/-- The total complex with a module placed in degree `0` is the termwise complex, naturally in
the module. -/
theorem totalSingleIso_hom_f_naturality
    {M M' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)} (g : M ⟶ M') (n : ℤ) :
    (HomologicalComplex.mapBifunctorMap (𝟙 G) ((HomologicalComplex.single _ (ComplexShape.up ℤ)
        0).map g) (tensorPullbackBifunctor f) (ComplexShape.up ℤ)).f n ≫
      (CochainComplex.KFlatBifunctor.totalSingleIso (tensorPullbackBifunctor f) G M').hom.f n =
    (CochainComplex.KFlatBifunctor.totalSingleIso (tensorPullbackBifunctor f) G M).hom.f n ≫
      ((tensorPullbackBifunctor f).obj (G.X n)).map g := by
  have h := CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality_right
    (tensorPullbackBifunctor f) G g
  exact (HomologicalComplex.comp_f _ _ n).symm.trans
    ((congrArg (fun φ => HomologicalComplex.Hom.f φ n) h).trans (HomologicalComplex.comp_f _ _ n))

/-- The inverse of the identification of the total complex with a module placed in degree `0`
with the termwise complex is natural in the module. -/
theorem totalSingleIso_inv_f_naturality
    {M M' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)} (g : M ⟶ M') (n : ℤ) :
    (CochainComplex.KFlatBifunctor.totalSingleIso (tensorPullbackBifunctor f) G M).inv.f n ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 G) ((HomologicalComplex.single _ (ComplexShape.up ℤ)
        0).map g) (tensorPullbackBifunctor f) (ComplexShape.up ℤ)).f n =
    ((tensorPullbackBifunctor f).obj (G.X n)).map g ≫
      (CochainComplex.KFlatBifunctor.totalSingleIso (tensorPullbackBifunctor f) G M').inv.f n := by
  refine (Iso.inv_comp_eq ((HomologicalComplex.eval _ _ n).mapIso
    (CochainComplex.KFlatBifunctor.totalSingleIso (tensorPullbackBifunctor f) G M))).2 ?_
  erw [← Category.assoc]
  exact (Iso.eq_comp_inv ((HomologicalComplex.eval _ _ n).mapIso
    (CochainComplex.KFlatBifunctor.totalSingleIso (tensorPullbackBifunctor f) G M'))).2
    (totalSingleIso_hom_f_naturality f G g n)

variable {f G} in
/-- **`0 → 𝒢^• ⊗ f^*ℱ₁ → 𝒢^• ⊗ f^*ℱ₂ → 𝒢^• ⊗ f^*ℱ₃ → 0` is exact** for a short exact sequence of
`𝒪_Y`-modules, the terms of `𝒢^•` being flat over `Y`. -/
theorem shortExact_tensorPullbackComplex_map_single
    (hG : ∀ n x, IsFlatOverAtGeometricPoint B S hS f (G.X n) x)
    {T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (hT : T.ShortExact) :
    ((T.map (HomologicalComplex.single _ (ComplexShape.up ℤ) 0)).map
      (tensorPullbackComplex f G)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have hE : (T.map ((tensorPullbackBifunctor f).obj (G.X n))).ShortExact := by
    have : PreservesFiniteLimits ((tensorPullbackBifunctor f).obj (G.X n)) :=
      preservesFiniteLimits_tensorPullbackFunctor f (G.X n) (hG n)
    have : PreservesFiniteColimits ((tensorPullbackBifunctor f).obj (G.X n)) :=
      Stacks.Cohomology.DerivedPullbackOfToposHom.preservesFiniteColimits_tensorPullback
        (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS f) (G.X n)
    exact hT.map_of_exact _
  let e : ∀ M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y),
      ((tensorPullbackBifunctor f).obj (G.X n)).obj M ≅
        ((tensorPullbackComplex f G).obj
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M)).X n := fun M =>
    ((HomologicalComplex.eval _ _ n).mapIso
      (CochainComplex.KFlatBifunctor.totalSingleIso (tensorPullbackBifunctor f) G M)).symm
  refine ShortComplex.shortExact_of_iso (ShortComplex.isoMk (e T.X₁) (e T.X₂) (e T.X₃) ?_ ?_) hE
  · exact totalSingleIso_inv_f_naturality f G T.f n
  · exact totalSingleIso_inv_f_naturality f G T.g n


end AlgebraicGeometry.Space

end
