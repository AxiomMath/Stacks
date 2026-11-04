module

public import StacksFrontier.Algebra.Homology.DerivedCategory.UniformProInverse
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulDualProZeroSlice
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulPerfectDualProjections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulTopCohomologySheaf

/-!
# The Koszul chain of Tag 0A0K at ringed-site level, with the pro-vanishing as a hypothesis

`Completion/KoszulAdicCompletionLimit.lean` runs the chain of [Stacks, Tag 0A0K] on a
**scheme**: the dual Koszul tower of [Stacks, Tag 0A0E] is compared with the tower of its top
cohomology sheaves by [Stacks, Tag 0G3D], and those are compared with the adic quotients. Every
link of that chain is stated at `Y : Scheme` —
`Stacks.Algebraization.koszulDualToTopQuotientDerived`,
`Stacks.Algebraization.koszulShiftedDualToAdicQuotient`,
`Stacks.Algebraization.adicQuotientSystem` and `AlgebraicGeometry.Scheme.IdealSheafData` — and the
Artin–Rees input it uses,
`Stacks.KoszulProZero.exists_koszulDualSystemOn_homologyMap_eq_zero_of_coherent`, carries
`[CompactSpace Y]` because it maximises a level over a finite affine cover.

The localization of a ringed site at an object is a `AlgebraicGeometry.RingedSite` and **not** a
scheme, so none of those statements can be read on it. This file states the chain for a ringed
site, with the pro-vanishing of the Koszul cohomology sheaves below the top degree **as a named
hypothesis in place of `[CompactSpace Y]`**. Either of the compactness-free Artin–Rees results

* `Stacks.KoszulProZero.exists_koszulDualSystemOn_homologyMap_eq_zero_of_model` — a ringed site
  with one flat Noetherian model uniform over a basis, and
* `Stacks.KoszulProZero.exists_koszulDualSystemOn_over_homologyMap_eq_zero` — the slice over an
  affine open of a locally Noetherian scheme, where that model is the pair
  `Γ(Y, U)`, `Γ(ℱ, U)`

discharges it.

The tower of top cohomology sheaves and the comparison into it are
`AlgebraicGeometry.RingedSite.koszulTopSingleSystem` and
`AlgebraicGeometry.RingedSite.koszulToTopSingle` of `KoszulDualProZero.lean`, the latter an
isomorphism on cohomology in the top degree at every level by
`AlgebraicGeometry.RingedSite.isIso_homologyMap_koszulToTopSingle`, with no hypothesis at all.
This file proves the three steps the scheme-level chain spends `[CompactSpace Y]`,
`[IsLocallyNoetherian Y]` and `[ℱ.IsCoherent]` on:

* the degreewise pro-invertibility that [Stacks, Tag 0G3D] asks for
  (`AlgebraicGeometry.RingedSite.hasProInverse_homology_koszulToTopSingle`): in the top degree
  `r` the comparison is invertible at every level, below it the Koszul cohomology is pro-zero —
  the hypothesis — and the single side vanishes, above it both sides vanish;
* the per-level pro-inverse of the comparison itself
  (`AlgebraicGeometry.RingedSite.hasEventualInverses_koszulToTopSingleDerived`), which is
  `NoetherianAdicCompletion.HasEventualInverses` of a genuine natural transformation rather than
  an `InverseSequence.ProIso`, and so can be fed to
  `NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses`;
* the composite with [Stacks, Tag 0A0E] *pinned*
  (`AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_koszulTopSingle_completion`): the
  Čech completion `ℱ^∧` is a derived limit of `n ↦ ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ` in degree zero,
  **through named projections**.

The last of those is the shape that
`Stacks.Algebraization.isIso_comparison_of_isDerivedLimitWithProjections` of
`Completion/AdicQuotientCanonicalComparison.lean` takes as input, whose converse makes its
hypothesis equivalent to part (3) of [Stacks, Tag 0A0K]. The tower it is stated over is the
tower of Koszul top cohomology sheaves, which at level `n` is `ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ` by
`AlgebraicGeometry.RingedSite.homologyIsoCokernelKoszulGeneratorsMap`; composing one further
comparison of that tower with the adic quotient tower — the pigeonhole containments
`ℐ^{r(n+1)+1}ℱ ⊆ (f_1^{n+1}, …, f_r^{n+1})ℱ ⊆ ℐⁿℱ`, which at ringed-site level need a site-level
`ℱ/ℐⁿℱ` — turns it into that hypothesis. `comp_of_hasEventualInverses` is again what carries the
projections across, and the statements below are arranged for it: every projection is produced as
a composite `p n ≫ φ.app ⟨n⟩`, never through an existentially bound cone.

## Main results

* `AlgebraicGeometry.RingedSite.hasEventualInverses_koszulToTopSingleDerived` — **[Stacks, Tag
  0G3D] on a ringed site**: the comparison of the dual Koszul tower with the tower of its top
  cohomology sheaves has eventual inverses in `D(𝒪)`, given the pro-vanishing below the top
  degree.
* `AlgebraicGeometry.RingedSite.koszulShiftedDualToTopSingle` — that comparison transported
  across the shift by `r` which [Stacks, Tag 0A0E] carries, landing in the tower of top
  cohomology sheaves placed in degree **zero**.
* `AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_koszulTopSingle_completion` —
  **the Čech completion is a derived limit of that tower through named projections.**
* `AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_koszulTopSingle_completion_of_model`
  — the same at a flat Noetherian model, with the hypothesis discharged and **no compactness**.
* `AlgebraicGeometry.RingedSite.completionUnit_app_comp_koszulTopSingleProjection` — **the cone
  of that presentation along the completion unit**, with neither the Čech complex nor a homotopy
  colimit on the right; this is what pins the projections, a map out of the completion into a
  derived-complete object being determined by its restriction along the unit.
* `AlgebraicGeometry.RingedSite.hasEventualInverses_koszulToTopSingleDerived_over_affineOpen` —
  the 0G3D step on the slice over an affine open of a locally Noetherian scheme, discharged by
  `Stacks.KoszulProZero.exists_koszulDualSystemOn_over_homologyMap_eq_zero`. `[CompactSpace Y]`
  does not appear.

## Implementation notes

The pro-vanishing hypothesis *cannot* be removed on a ringed site: at `r = 1`, `f = x`,
`ℱ = 𝒪` on the disjoint union of the `Spec k[x]/(xⁱ)`, the level needed to kill the cohomology
in degree `0` on the `i`-th chart is `n + i`, so no single level serves all charts. It holds with
no compactness on any site carrying one flat Noetherian model uniform over a basis, and the slice
of a locally Noetherian scheme over an affine open is such a site. So the hypothesis is exactly
what quasi-compactness provides in the scheme-level chain, and the corollaries below discharge it
in both of those situations.

## References

* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0G3D](https://stacks.math.columbia.edu/tag/0G3D)
* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.KoszulCoefficientProIso (rTensorFunctor)

universe u

namespace AlgebraicGeometry.RingedSite

section SiteChain

open scoped IsMulCommutative

attribute [local instance] HasDerivedCategory.standard hasFiniteBiproducts_sheafOfModules
  hasSheafCompose_forget₂_ringCat

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (ℱ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-! ### The hypothesis of [Stacks, Tag 0G3D], degree by degree -/

omit [HasSheafify X.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)]
  [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The Koszul side of the comparison has no cohomology outside the degrees `0, …, r`, read in
the derived category. -/
theorem isZero_homologyFunctor_koszulDualSystemOn_Q (i : ℤ) (hi : i < 0 ∨ (r : ℤ) < i)
    (n : ℕᵒᵖ) :
    IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).obj
      ((koszulDualSystemOn X f ℱ ⋙ DerivedCategory.Q).obj n)) := by
  refine ((DerivedCategory.homologyFunctorFactors
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).app
    ((koszulDualSystemOn X f ℱ).obj n)).isZero_iff.2 ?_
  rcases hi with hi | hi
  · exact isZero_homology_koszulPowerComplexOn_of_neg X f n.unop ℱ hi
  · exact isZero_homology_koszulPowerComplexOn_of_gt X f n.unop ℱ hi

omit [HasSheafify X.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)]
  [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The single-complex side of the comparison has no cohomology outside the top degree, read in
the derived category. -/
theorem isZero_homologyFunctor_koszulTopSingleSystem_Q (i : ℤ) (hi : i ≠ (r : ℤ)) (n : ℕᵒᵖ) :
    IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).obj
      ((koszulTopSingleSystem X f ℱ ⋙ DerivedCategory.Q).obj n)) :=
  ((DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).app
      ((koszulTopSingleSystem X f ℱ).obj n)).isZero_iff.2
    (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) (r : ℤ)
      ((koszulDualSystemOn X f ℱ ⋙
        HomologicalComplex.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) (r : ℤ)).obj n) i hi)

omit [HasSheafify X.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)] in
/-- **The comparison of the dual Koszul tower with the tower of its top cohomology sheaves is a
pro-isomorphism on cohomology in every degree**, which is the hypothesis of [Stacks, Tag 0G3D].

In the top degree `r` the comparison is an isomorphism at every level, with no refinement of the
index, by `AlgebraicGeometry.RingedSite.isIso_homologyMap_koszulToTopSingle`. Below the top
degree the Koszul cohomology is pro-zero — that is the hypothesis `hpz`, the Artin–Rees input —
and the single-complex side vanishes outright, so the zero map is a pro-inverse. Above the top
degree both sides vanish. -/
theorem hasProInverse_homology_koszulToTopSingle
    (hpz : ∀ (n : ℕ) (p : ℤ), p < r → ∃ (m : ℕ) (_ : n ≤ m),
      HomologicalComplex.homologyMap ((koszulDualSystemOn X f ℱ).map (homOfLE ‹n ≤ m›).op) p = 0)
    (i : ℤ) (j : ℕᵒᵖ) :
    ∃ (k : ℕᵒᵖ) (g : k ⟶ j)
      (s : (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).obj
          ((koszulTopSingleSystem X f ℱ ⋙ DerivedCategory.Q).obj k) ⟶
        (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).obj
          ((koszulDualSystemOn X f ℱ ⋙ DerivedCategory.Q).obj j)),
      (DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).map
            ((Functor.whiskerRight (koszulToTopSingle X f ℱ) DerivedCategory.Q).app k) ≫ s =
          (DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).map
            ((koszulDualSystemOn X f ℱ ⋙ DerivedCategory.Q).map g) ∧
        s ≫ (DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).map
              ((Functor.whiskerRight (koszulToTopSingle X f ℱ) DerivedCategory.Q).app j) =
            (DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).map
              ((koszulTopSingleSystem X f ℱ ⋙ DerivedCategory.Q).map g) := by
  rcases lt_trichotomy i (r : ℤ) with hi | hi | hi
  · obtain ⟨m, hnm, hzero⟩ := hpz j.unop i hi
    refine ⟨op m, (homOfLE hnm).op, 0, ?_, ?_⟩
    · rw [comp_zero]
      exact (DerivedCategory.homologyFunctor_map_Q_map_eq_zero
        ((koszulDualSystemOn X f ℱ).map (homOfLE hnm).op) i hzero).symm
    · rw [zero_comp]
      exact ((isZero_homologyFunctor_koszulTopSingleSystem_Q X f ℱ i (by omega)
        (op m)).eq_of_src _ _).symm
  · subst hi
    have : IsIso ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (r : ℤ)).map
        ((Functor.whiskerRight (koszulToTopSingle X f ℱ) DerivedCategory.Q).app j)) := by
      refine (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors _ (r : ℤ))
        ((koszulToTopSingle X f ℱ).app j)).mpr ?_
      rw [show j = op j.unop from rfl]
      exact isIso_homologyMap_koszulToTopSingle X f ℱ j.unop
    refine ⟨j, 𝟙 j, inv ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (r : ℤ)).map
      ((Functor.whiskerRight (koszulToTopSingle X f ℱ) DerivedCategory.Q).app j)), ?_, ?_⟩
    · rw [IsIso.hom_inv_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    · rw [IsIso.inv_hom_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  · refine ⟨j, 𝟙 j, 0, ?_, ?_⟩
    · rw [comp_zero, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      exact ((isZero_homologyFunctor_koszulDualSystemOn_Q X f ℱ i (Or.inr hi) j).eq_of_src
        _ _).symm
    · rw [zero_comp, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      exact ((isZero_homologyFunctor_koszulTopSingleSystem_Q X f ℱ i (by omega) j).eq_of_src
        _ _).symm

omit [HasSheafify X.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)] in
/-- **[Stacks, Tag 0G3D] on a ringed site**: the comparison of the dual Koszul tower with the
tower of its top cohomology sheaves has eventual inverses in `D(𝒪)`, given the pro-vanishing of
the Koszul cohomology sheaves below the top degree.

0G3D turns the degreewise pro-invertibility of
`AlgebraicGeometry.RingedSite.hasProInverse_homology_koszulToTopSingle` into a per-level
pro-inverse of the comparison itself, and that per-level statement *is*
`NoetherianAdicCompletion.HasEventualInverses` of the genuine natural transformation
`AlgebraicGeometry.RingedSite.koszulToTopSingle`. An `InverseSequence.ProIso` would carry only a
zig-zag at a reindexing and could not be fed to
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses`, which is
what carries the projections of a derived-limit presentation along a comparison of towers. -/
theorem hasEventualInverses_koszulToTopSingleDerived
    (hpz : ∀ (n : ℕ) (p : ℤ), p < r → ∃ (m : ℕ) (_ : n ≤ m),
      HomologicalComplex.homologyMap ((koszulDualSystemOn X f ℱ).map (homOfLE ‹n ≤ m›).op) p = 0) :
    NoetherianAdicCompletion.HasEventualInverses
      (Functor.whiskerRight (koszulToTopSingle X f ℱ) DerivedCategory.Q) := by
  intro n
  obtain ⟨k, g, s, hs₁, hs₂⟩ :=
    DerivedCategory.exists_proInverse_of_proInverse_homology
      (Functor.whiskerRight (koszulToTopSingle X f ℱ) DerivedCategory.Q) 0 (r : ℤ)
      (fun i hi => isZero_homologyFunctor_koszulDualSystemOn_Q X f ℱ i (by omega))
      (fun i hi => isZero_homologyFunctor_koszulTopSingleSystem_Q X f ℱ i (by omega))
      (hasProInverse_homology_koszulToTopSingle X f ℱ hpz) (op n)
  have h : n ≤ k.unop := leOfHom g.unop
  have hg : g = (homOfLE h).op := Subsingleton.elim _ _
  exact ⟨k.unop, h, s, by rw [← hg]; exact hs₁, by rw [← hg]; exact hs₂⟩

/-! ### The comparison across the shift by `r` -/

/-- **The tower of the top cohomology sheaves of the dual Koszul tower**, as a tower of sheaves
of modules rather than of single complexes. At level `n` it is
`ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ` by
`AlgebraicGeometry.RingedSite.homologyIsoCokernelKoszulGeneratorsMap`, and its transitions are
the maps induced on cohomology by the downward Koszul transitions, so it is a composite of
functors and needs no construction. -/
def koszulTopHomologySystem :
    ℕᵒᵖ ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  koszulDualSystemOn X f ℱ ⋙
    HomologicalComplex.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
      (r : ℤ)

/-- **The comparison of the shifted dual Koszul tower with the tower of top cohomology sheaves
in degree zero.**

[Stacks, Tag 0A0E] presents the completion as a derived limit of the tower
`n ↦ ℱ ⊗^𝐋_𝒪 (K^n)^∨`, which
`AlgebraicGeometry.RingedSite.koszulTensorDualSystemCoefficientIso` identifies with the `r`-fold
shift of the dual Koszul tower with coefficients. This transformation carries the comparison of
`AlgebraicGeometry.RingedSite.koszulToTopSingle` across that shift: `Q` commutes with the shift,
and the `r`-fold shift of the single functor in degree `r` is the single functor in degree zero,
`CategoryTheory.SingleFunctors.shiftIso`. -/
def koszulShiftedDualToTopSingle :
    (koszulDualSystemOn X f ℱ ⋙
        shiftFunctor (CochainComplex
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (r : ℤ)) ⋙
      DerivedCategory.Q ⟶
      koszulTopHomologySystem X f ℱ ⋙
        DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0 :=
  (Functor.isoWhiskerLeft (koszulDualSystemOn X f ℱ)
        (DerivedCategory.Q.commShiftIso (r : ℤ))).hom ≫
    Functor.whiskerRight (Functor.whiskerRight (koszulToTopSingle X f ℱ) DerivedCategory.Q)
      (shiftFunctor (DerivedCategory
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (r : ℤ)) ≫
    (Functor.isoWhiskerLeft (koszulTopHomologySystem X f ℱ)
      ((DerivedCategory.singleFunctors
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).shiftIso
        (r : ℤ) 0 (r : ℤ) (by ring))).hom

/-- The forward map of a natural isomorphism of towers has eventual inverses. -/
private theorem hasEventualInverses_iso_hom {C : Type*} [Category C] {F G : ℕᵒᵖ ⥤ C}
    (e : F ≅ G) : NoetherianAdicCompletion.HasEventualInverses e.hom :=
  fun n => ⟨n, le_rfl, e.inv.app (op n), by simp, by simp⟩

omit [HasSheafify X.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)] in
/-- **The comparison across the shift has eventual inverses.** The two identifications of
functors are isomorphisms, so they have eventual inverses at the same level; the comparison
itself has them by `AlgebraicGeometry.RingedSite.hasEventualInverses_koszulToTopSingleDerived`,
and eventual inverses are stable under composition and under whiskering by a functor. -/
theorem hasEventualInverses_koszulShiftedDualToTopSingle
    (hpz : ∀ (n : ℕ) (p : ℤ), p < r → ∃ (m : ℕ) (_ : n ≤ m),
      HomologicalComplex.homologyMap ((koszulDualSystemOn X f ℱ).map (homOfLE ‹n ≤ m›).op) p = 0) :
    NoetherianAdicCompletion.HasEventualInverses (koszulShiftedDualToTopSingle X f ℱ) := by
  exact (hasEventualInverses_iso_hom _).comp
    (((hasEventualInverses_koszulToTopSingleDerived X f ℱ hpz).whiskerRight _).comp
      (hasEventualInverses_iso_hom _))

/-! ### The pinned derived-limit presentation over the tower of top cohomology sheaves -/

/-- **The projections of the pinned presentation of the completion over the tower of Koszul top
cohomology sheaves.** They are the projections of
`RingedSite.isDerivedLimitWithProjections_tensorDerivedDualSystem_koszulPowerSystem_completion`
— the maps induced by the canonical Koszul–Čech comparisons of [Stacks, Tag 0913] — followed by
the identification of 0A0E's tower with the shifted dual Koszul tower and by the comparison
`AlgebraicGeometry.RingedSite.koszulShiftedDualToTopSingle`.

The bracketing is the one
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses` produces
when applied twice, so that the theorem below needs no rearrangement. -/
def koszulTopSingleProjection (n : ℕ) :
    (completionFunctor X f).obj
        (DerivedCategory.Q.obj (singleSheafComplex X ℱ)) ⟶
      (koszulTopHomologySystem X f ℱ ⋙
        DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj (op n) :=
  ((((derivedSheafHomBifunctor X).flip.obj
            (DerivedCategory.Q.obj (singleSheafComplex X ℱ))).map
          (DerivedCategory.Q.map (koszulCechComplexMap X f n)).op ≫
        (koszulTensorDualSystemIso X f
          (DerivedCategory.Q.obj (singleSheafComplex X ℱ))).inv.app (op n)) ≫
      (koszulTensorDualSystemCoefficientIso X f ℱ).hom.app (op n)) ≫
    (koszulShiftedDualToTopSingle X f ℱ).app (op n)

/-- **The Čech completion of `ℱ` is a derived limit of the tower of Koszul top cohomology sheaves
in degree zero, through named projections** — on an arbitrary ringed site, with the pro-vanishing
of the Koszul cohomology sheaves below the top degree as the only hypothesis.

At level `n` the tower is `ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ`
(`AlgebraicGeometry.RingedSite.homologyIsoCokernelKoszulGeneratorsMap`), so this is the Koszul
chain of [Stacks, Tag 0A0K] run at ringed-site level, stopping one comparison short of the adic
quotient tower: the pigeonhole containments
`ℐ^{r(n+1)+1}ℱ ⊆ (f_1^{n+1}, …, f_r^{n+1})ℱ ⊆ ℐⁿℱ` need a site-level `ℱ/ℐⁿℱ`, which
`Stacks.Sites.adicQuotientModule` provides only for `ℱ = 𝒪`.

Three inputs compose: [Stacks, Tag 0A0E] with its projections pinned
(`RingedSite.isDerivedLimitWithProjections_tensorDerivedDualSystem_koszulPowerSystem_completion`,
unconditional); the identification of its tower with the shifted dual Koszul tower
(`AlgebraicGeometry.RingedSite.koszulTensorDualSystemCoefficientIso`, an isomorphism of towers
and so with eventual inverses at the same level); and
`AlgebraicGeometry.RingedSite.hasEventualInverses_koszulShiftedDualToTopSingle`, which is where
the hypothesis is spent. `NoetherianAdicCompletion.IsDerivedLimitWithProjections`
`.comp_of_hasEventualInverses` carries the projections across both. -/
theorem isDerivedLimitWithProjections_koszulTopSingle_completion
    [HasCoproduct ((koszulPowerSystem X f ⋙ DerivedCategory.Q).obj)]
    [HasProduct fun n : ℕ ↦ (derivedSheafHomSystem X
      (koszulPowerSystem X f ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj (singleSheafComplex X ℱ))).obj (op n)]
    [HasProduct fun n : ℕ ↦ (tensorDerivedDualSystem X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
      (koszulPowerSystem X f ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj (singleSheafComplex X ℱ))).obj (op n)]
    [HasProduct fun n : ℕ ↦ ((koszulDualSystemOn X f ℱ ⋙
      shiftFunctor (CochainComplex
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (r : ℤ)) ⋙
      DerivedCategory.Q).obj (op n)]
    [HasProduct fun n : ℕ ↦ (koszulTopHomologySystem X f ℱ ⋙
      DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj (op n)]
    (hpz : ∀ (n : ℕ) (p : ℤ), p < r → ∃ (m : ℕ) (_ : n ≤ m),
      HomologicalComplex.homologyMap ((koszulDualSystemOn X f ℱ).map (homOfLE ‹n ≤ m›).op) p = 0) :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (koszulTopHomologySystem X f ℱ ⋙
        DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0)
      ((completionFunctor X f).obj (DerivedCategory.Q.obj (singleSheafComplex X ℱ)))
      (koszulTopSingleProjection X f ℱ) :=
  NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses
    (koszulShiftedDualToTopSingle X f ℱ)
    (hasEventualInverses_koszulShiftedDualToTopSingle X f ℱ hpz)
    (NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses
      (koszulTensorDualSystemCoefficientIso X f ℱ).hom
      (hasEventualInverses_iso_hom _)
      (isDerivedLimitWithProjections_tensorDerivedDualSystem_koszulPowerSystem_completion X f
        (DerivedCategory.Q.obj (singleSheafComplex X ℱ))))

/-- **The pinned derived-limit presentation at a flat Noetherian model, with no compactness.**

`Stacks.KoszulProZero.exists_koszulDualSystemOn_homologyMap_eq_zero_of_model` discharges the
pro-vanishing hypothesis on a ringed site carrying one flat Noetherian model uniform over a
basis: a Noetherian ring `A`, elements `a_1, …, a_r ∈ A` and a finite `A`-module `M` such that
every object is covered by objects `V` over which `𝒪(V)` is an `A`-algebra carrying `a_i` to
`f_i|_V` and `ℱ(V)` is the base change of `M` along a flat `A`-module. No quasi-compactness of
anything enters, the Artin–Rees level being computed once over the model.

The slice of a locally Noetherian scheme over an affine open `U` is such a site, with the model
`A = Γ(Y, U)`, `M = Γ(ℱ, U)` and the basic opens of `U` as the basis; that instance is
`Stacks.KoszulProZero.exists_koszulDualSystemOn_over_homologyMap_eq_zero`, whose conclusion is
*verbatim* the hypothesis `hpz` of
`AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_koszulTopSingle_completion` at that
site, so it can be passed to it directly. The scheme-level chain of
`Completion/KoszulAdicCompletionLimit.lean` cannot be read on a slice, because a slice is a
`AlgebraicGeometry.RingedSite` and not a `AlgebraicGeometry.Scheme`. -/
theorem isDerivedLimitWithProjections_koszulTopSingle_completion_of_model
    [HasCoproduct ((koszulPowerSystem X f ⋙ DerivedCategory.Q).obj)]
    [HasProduct fun n : ℕ ↦ (derivedSheafHomSystem X
      (koszulPowerSystem X f ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj (singleSheafComplex X ℱ))).obj (op n)]
    [HasProduct fun n : ℕ ↦ (tensorDerivedDualSystem X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
      (koszulPowerSystem X f ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj (singleSheafComplex X ℱ))).obj (op n)]
    [HasProduct fun n : ℕ ↦ ((koszulDualSystemOn X f ℱ ⋙
      shiftFunctor (CochainComplex
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (r : ℤ)) ⋙
      DerivedCategory.Q).obj (op n)]
    [HasProduct fun n : ℕ ↦ (koszulTopHomologySystem X f ℱ ⋙
      DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj (op n)]
    (A : Type u) [CommRing A] [IsNoetherianRing A] (a : Fin r → A)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hmodel : ∀ U : X.Cᵒᵖ, ∃ P : Presieve U.unop, Sieve.generate P ∈ X.J U.unop ∧
      ∀ ⦃V : X.C⦄ (g : V ⟶ U.unop), P g →
        ∃ (ρ : A →+* (X.O.obj.obj (op V))) (S : ModuleCat.{u} A),
          (∀ i, ρ (a i) = globalSectionVal (f i) (op V)) ∧ Module.Flat A S ∧
            Nonempty ((Stacks.KoszulProZero.modelSectionsFunctor X (op V) ρ).obj ℱ ≅
              (rTensorFunctor S).obj M)) :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (koszulTopHomologySystem X f ℱ ⋙
        DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0)
      ((completionFunctor X f).obj (DerivedCategory.Q.obj (singleSheafComplex X ℱ)))
      (koszulTopSingleProjection X f ℱ) :=
  isDerivedLimitWithProjections_koszulTopSingle_completion X f ℱ
    (fun n p hp => Stacks.KoszulProZero.exists_koszulDualSystemOn_homologyMap_eq_zero_of_model
      X f ℱ A a M hmodel n p hp)

/-- **The cone of the pinned presentation along the completion unit.** The completion unit
`ℱ[0] ⟶ ℱ^∧` followed by the `n`-th projection of
`AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_koszulTopSingle_completion` is the
identification `ℱ[0] = R𝑆heafHom_𝒪(𝒪, ℱ[0])`, followed by the map which the single map of
complexes `K^n ⟶ 𝒪[0]` — the Koszul–Čech comparison of [Stacks, Tag 0913] composed with the Čech
augmentation — induces on derived internal Hom, followed by the two tower identifications and the
comparison into the top cohomology sheaves. Neither the Čech complex nor a homotopy colimit
survives on the right.

A map out of `ℱ^∧` into a derived-complete object is determined by its restriction along the
unit, so this identity *pins* the projections: it is what an argument identifying them with the
canonical maps onto a quotient tower consumes, and
`AlgebraicGeometry.RingedSite.completionUnit_app_comp_koszulTopSingleProjection_eq` of
`KoszulAdicDualDegreeZero.lean` is that argument carried out — the right-hand side here is
`(-1)^r` times the quotient map `ℱ ⟶ ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ` in degree zero.
`AlgebraicGeometry.RingedSite.completionUnit_app_comp_tensorDerivedDualSystem_π` is the same
statement for the projections of [Stacks, Tag 0A0E] before the two towers are compared, and this
is it carried along both comparisons; nothing but associativity is used. -/
theorem completionUnit_app_comp_koszulTopSingleProjection (n : ℕ) :
    (completionUnit X f).app (DerivedCategory.Q.obj (singleSheafComplex X ℱ)) ≫
        koszulTopSingleProjection X f ℱ n =
      ((derivedStructureSheafHomIso X (DerivedCategory.Q.obj (singleSheafComplex X ℱ))).inv ≫
          ((derivedSheafHomBifunctor X).map
                (DerivedCategory.Q.map
                  (koszulCechComplexMap X f n ≫ cechAugmentation X f)).op).app
              (DerivedCategory.Q.obj (singleSheafComplex X ℱ)) ≫
            (koszulTensorDualSystemIso X f
              (DerivedCategory.Q.obj (singleSheafComplex X ℱ))).inv.app (op n)) ≫
        (koszulTensorDualSystemCoefficientIso X f ℱ).hom.app (op n) ≫
          (koszulShiftedDualToTopSingle X f ℱ).app (op n) := by
  rw [koszulTopSingleProjection, ← Category.assoc, ← Category.assoc,
    completionUnit_app_comp_tensorDerivedDualSystem_π, Category.assoc]

end SiteChain

section Slice

open scoped IsMulCommutative

attribute [local instance] HasDerivedCategory.standard hasFiniteBiproducts_sheafOfModules
  hasSheafCompose_forget₂_ringCat

variable (Y : Scheme.{u}) [IsLocallyNoetherian Y] {r : ℕ}
  (f : Fin r → Presheaf.globalSections
    ((Stacks.SheafOfModules.opensRingedSite Y.sheaf).O.obj ⋙ forget CommRingCat.{u}))
  (ℱ : Y.Modules) [ℱ.IsCoherent] (U : Y.affineOpens)

/-- **[Stacks, Tag 0G3D] on the slice over an affine open, with no compactness hypothesis on the
ambient scheme.**

The hypothesis of `AlgebraicGeometry.RingedSite.hasEventualInverses_koszulToTopSingleDerived` is
*verbatim* the conclusion of
`Stacks.KoszulProZero.exists_koszulDualSystemOn_over_homologyMap_eq_zero`, so the slice result is
passed to it with no bridging. On a scheme the same step is
`Stacks.Algebraization.hasEventualInverses_koszulDualToTopQuotientDerived`, which carries
`[CompactSpace Y]` through the Artin–Rees input and nowhere else; here `Y` is only locally
Noetherian. -/
theorem hasEventualInverses_koszulToTopSingleDerived_over_affineOpen :
    NoetherianAdicCompletion.HasEventualInverses
      (Functor.whiskerRight
        (koszulToTopSingle ((Stacks.SheafOfModules.opensRingedSite Y.sheaf).over U.1)
          (fun i => globalSectionOver (Stacks.SheafOfModules.opensRingedSite Y.sheaf) U.1 (f i))
          ((SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (Stacks.SheafOfModules.opensRingedSite Y.sheaf).O) U.1).obj
            (show SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
                (Stacks.SheafOfModules.opensRingedSite Y.sheaf).O)
              from ℱ)))
        DerivedCategory.Q) :=
  hasEventualInverses_koszulToTopSingleDerived
    ((Stacks.SheafOfModules.opensRingedSite Y.sheaf).over U.1)
    (fun i => globalSectionOver (Stacks.SheafOfModules.opensRingedSite Y.sheaf) U.1 (f i))
    ((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Stacks.SheafOfModules.opensRingedSite Y.sheaf).O) U.1).obj
      (show SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (Stacks.SheafOfModules.opensRingedSite Y.sheaf).O)
        from ℱ))
    (fun n p hp =>
      Stacks.KoszulProZero.exists_koszulDualSystemOn_over_homologyMap_eq_zero Y f ℱ U n p hp)

end Slice

end AlgebraicGeometry.RingedSite

end
