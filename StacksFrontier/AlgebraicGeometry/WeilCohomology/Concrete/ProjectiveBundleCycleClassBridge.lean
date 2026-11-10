module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleRationalChow
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinTransversal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TraceUniqueness
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.TrivialSection
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalPushforwardRational

/-!
# The cycle class map as a ring homomorphism into power series, and the projective bundle

Let `p : P = 𝐏(ℰ) ⟶ X` be the projective bundle of a finite locally free module of rank `r + 1`
on a smooth projective scheme `X` over `k`, nonempty and equidimensional of dimension `d`. The
projection is surjective (over an open on which `ℰ` is free it has a section) and smooth of
relative dimension `r`, so `P` is nonempty and equidimensional of dimension `d + r`. The square

  `1 × p : P × P ⟶ P × X`, `pr₂`, `pr₂`, `p : P ⟶ X`

is cartesian, and `1 × p` carries the diagonal of `P` isomorphically onto the graph `Γ_p` of `p`,
so on Chow groups `(1 × p)_*[Δ_P] = [Γ_p] = (p × 1)^![Δ_X]`.

Given a cohomological Chern character `ch^H` (Tag 0FIE), the cycle class map of Tag 0FIF is the
`𝐐`-algebra homomorphism

  `γ : CH^*(X) ⊗ 𝐐 ⟶ ∏_{i ≥ 0} A^i(X)`, `γ(α) = ch^H(α')` for `ch(α') ∩ [X] = α`,

read as power series over `A(X) = ⨁_{i ≥ 0} H^{2i}(X)`. Its coefficients are the components of
the cycle class map, a class of codimension `i` has only a coefficient in degree `i`, it commutes
with the Gysin maps, and `γ(c₁(ℒ) ∩ [Y]) = c₁^H(ℒ)`.

## Main definitions

* `Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter.cycleClassSeries`:
  `γ : CH^*(X) ⊗ 𝐐 ⟶ A(X)[[t]]` as a homomorphism of `𝐐`-algebras.

## Main results

The results on `γ` are in the namespace
`Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter`.

* `Stacks.WeilCohomology.surjective_chowBundleProj`: the projection of a projective bundle is
  surjective.
* `Stacks.WeilCohomology.isNonemptyEquidimensional_bundle`: `P` is nonempty and equidimensional of
  dimension `d + r`.
* `Stacks.WeilCohomology.isPullback_prodMap_id_bundleProj`: `1 × p` is the base change of `p`.
* `Stacks.WeilCohomology.equidimensionalPushforward_diagonalClass_bundle`:
  `(1 × p)_*[Δ_P] = (p × 1)^![Δ_X]`.
* `Stacks.WeilCohomology.smoothChowEquiv_codimensionToRationalChow_equidimensionalPushforward`:
  proper pushforward on `CH^*` is proper pushforward on `CH^* ⊗ 𝐐`.
* `IsCohomologicalChernCharacter.coe_coeff_cycleClassSeries`,
  `coeff_cycleClassSeries_of_ne`: the coefficients of `γ` on a class of codimension `i`.
* `IsCohomologicalChernCharacter.cycleClassSeries_smoothGysinRingHom`:
  `γ ∘ f^! = f^* ∘ γ`.
* `IsCohomologicalChernCharacter.cycleClassSeries_rationalFirstChernClass`:
  `γ(c₁(ℒ) ∩ [Y]) = c₁^H(ℒ)`.

## References

* [Stacks Project, Tag 0FIE](https://stacks.math.columbia.edu/tag/0FIE)
* [Stacks Project, Tag 0FIF](https://stacks.math.columbia.edu/tag/0FIF)
* [Stacks Project, Tag 0FIN](https://stacks.math.columbia.edu/tag/0FIN)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open scoped TensorProduct

universe u w

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-! ### The parts of an equidimensional scheme -/

/-- A nonempty smooth projective scheme equidimensional of dimension `d` has exactly one nonempty
part, `X_d`. -/
theorem nonemptyDimParts_eq_singleton {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) : nonemptyDimParts k X.obj.hom = {d} := by
  ext e
  rw [mem_nonemptyDimParts, Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx⟩
    by_contra he
    exact (isEmpty_dimPart_of_ne X.obj.hom hX.relativeDimension he).false ⟨x, hx⟩
  · rintro rfl
    obtain ⟨x⟩ := hX.nonempty
    exact ⟨x, by rw [dimPart_self_eq_top X.obj.hom hX.relativeDimension]; trivial⟩

/-- **Pushing forward from the only nonempty part.** If `X_D` is the only nonempty part of `X`,
then pushing forward the restriction of a class to `X_D` along `X_D ⟶ X ⟶ Z` is pushing forward
the class along `X ⟶ Z`. -/
theorem properChowPushforward_dimPart_chowGroupRestrict {X Z : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] [CompactSpace X]
    (sZ : Z ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sZ] (g : X ⟶ Z) [IsProper g]
    (hg : g ≫ sZ = sX) {D : ℕ} (hD : nonemptyDimParts k sX = {D}) (m : ℤ)
    (w : chowGroup (fieldChowSituation k) sX m) :
    haveI := (isClopenDecomposition_dimPart sX).isProper_ι D
    properChowPushforward (fieldChowSituation k) (partBase sX D) sZ ((dimPart sX D).ι ≫ g)
        (by rw [Category.assoc, hg]) m (properPushforwardDescends _ _ _ _ _ _)
        (chowGroupRestrict (fieldChowSituation k) sX (partBase sX D) (dimPart sX D).ι rfl m w) =
      properChowPushforward (fieldChowSituation k) sX sZ g hg m
        (properPushforwardDescends _ _ _ _ _ _) w := by
  have := (isClopenDecomposition_dimPart sX).isProper_ι D
  have hsum := sum_properChowPushforward_chowGroupRestrict_dimPart k sX m w
  rw [hD, Finset.sum_singleton] at hsum
  rw [← DFunLike.congr_fun (properChowPushforward_comp _ _ _ _ _ _ rfl hg m
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)),
    AddMonoidHom.comp_apply, hsum]

/-! ### The projective bundle and the products -/

/-- **The projection of a projective bundle is surjective.** Every point of the base has an open
neighbourhood on which `ℰ` is free of rank `r + 1`, and over it the projection of `𝐏(ℰ)` has a
section. -/
theorem surjective_chowBundleProj {S : Scheme.{u}} (E : S.Modules) (r : ℕ)
    [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)] :
    letI := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
    Function.Surjective (Stacks.Chow.bundleProj E) := by
  let := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  have : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  intro x
  obtain ⟨U, hxU, hiso⟩ :=
    (AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_iff E (r + 1)).mpr hE x
  obtain ⟨σ, hσ⟩ :=
    Stacks.ProjectiveBundleSplitting.exists_section_of_restrict_free E (bundlePieces E) r U hiso
  refine ⟨σ ⟨x, hxU⟩, ?_⟩
  change (σ ≫ Stacks.Chow.bundleProj E) ⟨x, hxU⟩ = x
  rw [show σ ≫ Stacks.Chow.bundleProj E = U.ι from hσ]
  rfl

section Bundle

variable (X : (SmoothProjectiveScheme k).FullSubcategory) (E : X.obj.left.Modules) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]

/-- The projective bundle `P = 𝐏(ℰ)` of a module of rank `r + 1` on a nonempty `X`
equidimensional of dimension `d` is nonempty and equidimensional of dimension `d + r`. -/
theorem isNonemptyEquidimensional_bundle {d : ℕ} (hX : IsNonemptyEquidimensional X d) :
    IsNonemptyEquidimensional (bundle X E r) (d + r) := by
  let := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  have := flat_bundleProj E r
  have := locallyOfFiniteType_bundleProj E r
  refine ⟨?_, ?_⟩
  · obtain ⟨x⟩ := hX.nonempty
    obtain ⟨y, -⟩ := surjective_chowBundleProj E r x
    exact ⟨y⟩
  · have h := RelativeDimension.comp_of_flat (Stacks.Chow.bundleProj E) X.obj.hom
      (relativeDimension_bundleProj E r) hX.relativeDimension
    rwa [add_comm] at h

/-- `P × P ⟶ P × X`, `1 × p`, is the base change of `p : P ⟶ X` along `pr₂ : P × X ⟶ X`. -/
theorem isPullback_prodMap_id_bundleProj :
    letI := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
    IsPullback (prodMap (𝟙 (bundle X E r)) (bundleProj X E r)).hom.left
      (snd (bundle X E r) (bundle X E r)).hom.left (snd (bundle X E r) X).hom.left
      (Stacks.Chow.bundleProj E) := by
  let := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  have hout : IsPullback ((prodMap (𝟙 (bundle X E r)) (bundleProj X E r)).hom.left ≫
      (fst (bundle X E r) X).hom.left) (snd (bundle X E r) (bundle X E r)).hom.left
      (bundle X E r).obj.hom (Stacks.Chow.bundleProj E ≫ X.obj.hom) := by
    have h1 : (prodMap (𝟙 (bundle X E r)) (bundleProj X E r)).hom.left ≫
        (fst (bundle X E r) X).hom.left = (fst (bundle X E r) (bundle X E r)).hom.left := by
      have := congrArg (fun φ ↦ φ.hom.left) (prodMap_fst (𝟙 (bundle X E r)) (bundleProj X E r))
      rwa [Category.comp_id] at this
    rw [h1]
    exact IsPullback.of_hasPullback (bundle X E r).obj.hom (bundle X E r).obj.hom
  exact IsPullback.of_right hout
    (congrArg (fun φ ↦ φ.hom.left) (prodMap_snd (𝟙 (bundle X E r)) (bundleProj X E r)))
    (IsPullback.of_hasPullback (bundle X E r).obj.hom X.obj.hom)

/-- **`(1 × p)_*[Δ_P] = [Γ_p]`**: the pushforward of the class of the diagonal of `P` along
`1 × p : P × P ⟶ P × X` is the class of the graph of `p`, which is `(p × 1)^![Δ_X]`. -/
theorem equidimensionalPushforward_diagonalClass_bundle {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) :
    equidimensionalPushforward (prodMap (𝟙 (bundle X E r)) (bundleProj X E r))
        (2 * (d + r)) (d + r + d) (d + r : ℕ) d (by push_cast; ring)
        (diagonalClass (bundle X E r) (d + r)) =
      codimensionGysin (prod (bundle X E r) X).obj.hom (prod X X).obj.hom
        (Over.w (prodMap (bundleProj X E r) (𝟙 X)).hom) d (diagonalClass X d) := by
  let := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  have hP := isNonemptyEquidimensional_bundle X E r hX
  have hPP : IsNonemptyEquidimensional (prod (bundle X E r) (bundle X E r)) (2 * (d + r)) := by
    rw [two_mul]
    exact isNonemptyEquidimensional_prod hP hP
  have hPX := isNonemptyEquidimensional_prod hP hX
  have hgraph := codimensionGysin_prodHom_id_diagonal (bundle X E r).obj.hom X.obj.hom
    (bundleProj X E r).hom.left (Over.w (bundleProj X E r).hom) hP.relativeDimension
    hX.relativeDimension
  refine Eq.trans ?_ hgraph.symm
  have hΔ : (diag (bundle X E r)).hom.left ≫
      (prodMap (𝟙 (bundle X E r)) (bundleProj X E r)).hom.left =
        graphToProd (bundle X E r).obj.hom X.obj.hom (bundleProj X E r).hom.left
          (Over.w (bundleProj X E r).hom) := by
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans ?_
      change (SmoothProjectiveScheme.diag (bundle X E r)).hom.left ≫
          (prodMap (𝟙 (bundle X E r)) (bundleProj X E r) ≫
            SmoothProjectiveScheme.fst (bundle X E r) X).hom.left = _
      rw [prodMap_fst, Category.comp_id, graphToProd, pullback.lift_fst]
      exact pullback.diagonal_fst _
    · refine (Category.assoc _ _ _).trans ?_
      change (SmoothProjectiveScheme.diag (bundle X E r)).hom.left ≫
          (prodMap (𝟙 (bundle X E r)) (bundleProj X E r) ≫
            SmoothProjectiveScheme.snd (bundle X E r) X).hom.left = _
      rw [prodMap_snd, graphToProd, pullback.lift_snd]
      change pullback.diagonal _ ≫ pullback.snd _ _ ≫ _ = _
      rw [pullback.diagonal_snd_assoc]
  have hgr : IsClosedImmersion (graphToProd (bundle X E r).obj.hom X.obj.hom
      (bundleProj X E r).hom.left (Over.w (bundleProj X E r).hom) :
        (bundle X E r).obj.left ⟶ (prod (bundle X E r) X).obj.left) := inferInstance
  have hΔgr : IsClosedImmersion ((SmoothProjectiveScheme.diag (bundle X E r)).hom.left ≫
      (prodMap (𝟙 (bundle X E r)) (bundleProj X E r)).hom.left) := by
    rw [hΔ]
    exact hgr
  have : IsProper (prodMap (𝟙 (bundle X E r)) (bundleProj X E r)).hom.left := by
    have : IsProper ((prodMap (𝟙 (bundle X E r)) (bundleProj X E r)).hom.left ≫
        (prod (bundle X E r) X).obj.hom) := by
      rw [Over.w (prodMap (𝟙 (bundle X E r)) (bundleProj X E r)).hom]
      infer_instance
    exact IsProper.of_comp _ (prod (bundle X E r) X).obj.hom
  have := (isClopenDecomposition_dimPart (prod (bundle X E r) (bundle X E r)).obj.hom).isProper_ι
    (2 * (d + r))
  funext e'
  by_cases he : e' = d + r + d
  · subst he
    simp only [equidimensionalPushforward, AddMonoidHom.pi_apply, closedSubschemeClass_apply,
      diagonalClass]
    refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans ?_)
    simp only [AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply]
    refine chowGroupRestrict_heq_of_eq _ _ _ rfl rfl rfl _ _ (by push_cast; ring) _ _ ?_
    rw [closedSubschemeClass_apply]
    rw [properChowPushforward_dimPart_chowGroupRestrict _ _ _
      (Over.w (prodMap (𝟙 (bundle X E r)) (bundleProj X E r)).hom)
      (nonemptyDimParts_eq_singleton hPP)]
    have hpush := properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp
      (fieldChowSituation k) _ _ (prodMap (𝟙 (bundle X E r)) (bundleProj X E r)).hom.left
      (Over.w (prodMap (𝟙 (bundle X E r)) (bundleProj X E r)).hom)
      (SmoothProjectiveScheme.diag (bundle X E r)).hom.left
      (((2 * (d + r) : ℕ) : ℤ) - ((d + r : ℕ) : ℤ))
    rw [@cycleAssociatedToClosedSubscheme_congr _ _ _ _ _ _ _ hΔgr hgr hΔ] at hpush
    refine HEq.trans (heq_of_eq ((properChowPushforward_mk _ _ _ _ _ _ _ _).trans
      (congrArg _ hpush))) ?_
    have hm : (((2 * (d + r) : ℕ) : ℤ) - ((d + r : ℕ) : ℤ)) = ((d + r + d : ℕ) : ℤ) - (d : ℤ) := by
      push_cast; ring
    rw [hm]
    rfl
  · have := isEmpty_dimPart_of_ne _ hPX.relativeDimension he
    exact @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty _ _ _) _ _

end Bundle

/-! ### Proper pushforward on codimension classes, rationally -/

/-- **`f_*` on `CH^*` is `f_*` on `CH^* ⊗ 𝐐`.** -/
theorem smoothChowEquiv_codimensionToRationalChow_equidimensionalPushforward
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    {d e : ℕ} (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y e) (p q : ℤ) (h : q = p + e - d)
    (α : codimensionChowGroup k X.obj.hom p) :
    smoothChowEquiv Y.obj.hom (codimensionToRationalChow k Y.obj.hom q
        (equidimensionalPushforward f d e p q h α)) =
      rationalPush f (smoothChowEquiv X.obj.hom (codimensionToRationalChow k X.obj.hom p α)) := by
  simp only [rationalPush, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.symm_apply_apply]
  rw [codimensionToRationalChow_equidimensionalPushforward f hX.relativeDimension
    hY.relativeDimension]

/-! ### The cycle class map as a ring homomorphism -/

namespace FirstChernClassData.IsCohomologicalChernCharacter

variable {F : Type w} [Field F] [CharZero F] {𝔇 : FirstChernClassData k F}
  {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
  (h : 𝔇.IsCohomologicalChernCharacter ch)

/-- **`γ : CH^*(X) ⊗ 𝐐 ⟶ ∏_{i ≥ 0} A^i(X)`** as a homomorphism of `𝐐`-algebras into power series
over `A(X) = ⨁_{i ≥ 0} H^{2i}(X)`: `ch^H` of the class `α'` with `ch(α') ∩ [X] = α`. -/
def cycleClassSeries (X : (SmoothProjectiveScheme k).FullSubcategory) :
    smoothRationalChowRing (k := k) X.obj.hom →ₐ[ℚ] PowerSeries (𝔇.A X) :=
  (h.rationalLift X).comp (rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field X.obj.hom)
    (exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom)).symm.toAlgHom

/-- The coefficients of `cycleClassSeries` are the components of the cycle class map, read in the
coordinates `κ`. -/
theorem κ_cycleClassMap (X : (SmoothProjectiveScheme k).FullSubcategory)
    (α : smoothRationalChowRing (k := k) X.obj.hom) (n : ℕ) :
    𝔇.κ X n (h.cycleClassMap X α n) =
      ((PowerSeries.coeff n (h.cycleClassSeries X α) : 𝔇.A X) : 𝔇.H X) :=
  𝔇.κ_twistRule _ n

/-- The coefficients of `cycleClassSeries` are the components of `γ`, in coordinates. -/
theorem coe_coeff_cycleClassSeries (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ)
    (a : codimensionChowGroup k X.obj.hom i) :
    ((PowerSeries.coeff i (h.cycleClassSeries X
        (smoothChowEquiv X.obj.hom (codimensionToRationalChow k X.obj.hom i a))) : 𝔇.A X) :
        𝔇.H X) = 𝔇.κ X i (h.codimensionCycleClass X i a) := by
  rw [codimensionCycleClass_apply, κ_cycleClassMap]

/-- The class of `α ∈ CH^i(X)` has no coefficients outside degree `i`. -/
theorem coeff_cycleClassSeries_of_ne (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ)
    (a : codimensionChowGroup k X.obj.hom i) {n : ℕ} (hn : n ≠ i) :
    PowerSeries.coeff n (h.cycleClassSeries X
        (smoothChowEquiv X.obj.hom (codimensionToRationalChow k X.obj.hom i a))) = 0 := by
  refine Subtype.ext ?_
  rw [← κ_cycleClassMap, h.cycleClassMap_eq_zero_of_ne hA1 hA3 X i a hn, map_zero,
    ZeroMemClass.coe_zero]

/-- **`γ` commutes with the Gysin maps**, as power series. -/
theorem cycleClassSeries_smoothGysinRingHom {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y)
    (y : smoothRationalChowRing (k := k) Y.obj.hom) :
    h.cycleClassSeries X (smoothGysinRingHom X.obj.hom Y.obj.hom (Over.w f.hom) y) =
      PowerSeries.map (𝔇.pullA f).toRingHom (h.cycleClassSeries Y y) := by
  obtain ⟨x, rfl⟩ := (rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field Y.obj.hom)
    (exists_bounds_relativeDimension_fieldChowSituation k Y.obj.hom)).surjective y
  rw [smoothGysinRingHom_rationalChernCharacterAlgEquiv, cycleClassSeries, cycleClassSeries]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
  exact (h.map_rationalLift f x).symm

/-- **`γ(c₁(ℒ) ∩ [Y]) = c₁^H(ℒ)`**, as a power series concentrated in degree one. -/
theorem cycleClassSeries_rationalFirstChernClass (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (Y : (SmoothProjectiveScheme k).FullSubcategory)
    (L : Y.obj.left.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible ((toScheme k).obj Y).presheaf
      ((toScheme k).obj Y).ringCatSheaf.2 L) :
    h.cycleClassSeries Y (rationalFirstChernClass Y L) =
      PowerSeries.monomial 1 (𝔇.c₁A Y (picardClassOf _ L hL)) := by
  have hmem : (smoothChowEquiv Y.obj.hom).symm (rationalFirstChernClass Y L) ∈
      codimensionChowSubmodule (fieldChowSituation k) Y.obj.hom 1 := by
    rw [rationalFirstChernClass, LinearEquiv.symm_apply_apply,
      rationalChernCharacterComponentCap_apply]
    have H := rationalChowCap_mem_codimensionChowSubmodule_add (fieldChowSituation k)
      Y.obj.hom _ (isCohenMacaulay_of_isRegular (isRegular_of_smooth_over_field Y.obj.hom)) 1
      (rationalChernCharacterVectorBundle (fieldChowSituation k) Y.obj.hom
        (1 ⊗ₜ VectorBundleKZero.classOf _ L) 1)
      (directSumRight_one_tmul_totalFundamentalClass_mem_codimensionChowSubmodule_zero
        (fieldChowSituation k) Y.obj.hom)
    rwa [zero_add] at H
  refine PowerSeries.ext fun n => Subtype.ext ?_
  rw [← κ_cycleClassMap, PowerSeries.coeff_monomial]
  rcases eq_or_ne n 1 with rfl | hn
  · rw [ite_eq_left rfl, coe_c₁A, rationalFirstChernClass,
      h.cycleClassMap_rationalChernCharacterComponentCap hA1 hA3,
      h.cycleClassMap_rationalChernCharacterAlgEquiv]
    exact congrArg (𝔇.κ Y 1) ((congrFun (h.2.2.2.2.2 Y L hL) 1).trans (expTw_one Y _))
  · rw [ite_eq_right hn, (h.cycleClassMap_mem hA1 hA3 Y _ hmem).2 n hn, map_zero,
      ZeroMemClass.coe_zero]

end FirstChernClassData.IsCohomologicalChernCharacter

end Stacks.WeilCohomology

end
