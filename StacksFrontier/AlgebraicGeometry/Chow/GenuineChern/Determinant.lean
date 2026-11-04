module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.Additivity
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExactIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerDegreeOne

/-!
# The first Chern class of a module is the first Chern class of its determinant

For `ℰ` finite locally free of constant rank `r` on `X` locally of finite type over the base of
chapter 42,

  `c₁(ℰ) ∩ α = c₁(⋀ʳ ℰ) ∩ α`,

where on the left `c₁` is the first Chern class of [Stacks, Tag 02U0] (here
`Stacks.Chow.GenuineChern.firstChern`) and on the right that of the invertible module `⋀ʳ ℰ`
([Stacks, Tag 02SO]). This is the first Chern class part of the splitting principle computation
`c₁(ℰ) = ∑ c₁(ℒ_i) = c₁(⊗ ℒ_i)` of [Stacks, Tag 02UJ] together with [Stacks, Tag 0B38].

The proof is by induction on `r`. In rank zero both sides vanish (`⋀⁰ ℰ ≅ 𝒪_X`); in rank one
`⋀¹ ℰ ≅ ℰ`. In rank `n + 2`, on the projective bundle `π : P(ℰ) ⟶ X` the tautological sequence
`0 ⟶ 𝒦 ⟶ π^*ℰ ⟶ 𝒪(1) ⟶ 0` has `𝒦` of rank `n + 1`; additivity
(`Stacks.Chow.GenuineChern.firstChern_add_of_shortExact`), the induction hypothesis for `𝒦`,
Stacks 02SP and `⋀^{n+1} 𝒦 ⊗ 𝒪(1) ≅ ⋀^{n+2} π^*ℰ ≅ π^*⋀^{n+2} ℰ` (Stacks 0B38, 01CI) give the
identity at `π^*α`, and it descends because `π^*` commutes with both sides (the input
`Stacks.Chow.GenuineChern.FlatCompat` and Stacks 02SS) and is injective.

## Main results

* `Stacks.Chow.GenuineChern.firstChern_eq_firstChernClassCapChow_exteriorPower`.

## References

* [Stacks Project, Tag 02UJ](https://stacks.math.columbia.edu/tag/02UJ)
* [Stacks Project, Tag 0B38](https://stacks.math.columbia.edu/tag/0B38)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.GenuineChern

variable {C : ChowSituation.{u}}

/-- The first Chern class cap of an invertible module, at heterogeneously equal arguments in equal
degrees. -/
theorem firstChernClassCapChow_heq {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    {d₁ d₂ : ℤ} (hd : d₁ = d₂) {x : chowGroup C p (d₁ + 1)} {y : chowGroup C p (d₂ + 1)}
    (hxy : x ≍ y) : firstChernClassCapChow C d₁ p L x ≍ firstChernClassCapChow C d₂ p L y :=
  heq_apply_of_degree C p p (fun d => d + 1) (fun d => d)
    (fun d => firstChernClassCapChow C d p L) hd hxy

/-- The top exterior power of a module of constant rank `r` has rank one. -/
theorem isFiniteLocallyFreeOfRank_det {X : Scheme.{u}} (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.exteriorPower E (r : ℤ)) 1 := by
  simpa only [Nat.choose_self] using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower E r r

/-- The top exterior power of a module of constant rank is invertible. -/
theorem isInvertible_det {X : Scheme.{u}} (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.Modules.exteriorPower E (r : ℤ)) :=
  have := isFiniteLocallyFreeOfRank_det E r
  isInvertible_of_isFiniteLocallyFreeOfRank_one _

/-- **Stacks 0B38 on a scheme**: for `0 ⟶ ℱ ⟶ ℰ ⟶ ℒ ⟶ 0` short exact with `ℱ` of rank `m + 1`
and `ℒ` of rank one, `⋀^{m+1} ℱ ⊗ ⋀¹ ℒ ≅ ⋀^{m+2} ℰ`. -/
theorem nonempty_det_tensor_iso {X : Scheme.{u}} {F E L : X.Modules} (i : F ⟶ E) (q : E ⟶ L)
    (w : i ≫ q = 0) (hS : (ShortComplex.mk i q w).ShortExact) (m : ℕ)
    [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (m + 1)]
    [hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] :
    Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          (Scheme.Modules.exteriorPower F ((m + 1 : ℕ) : ℤ))).obj
        (Scheme.Modules.exteriorPower L ((1 : ℕ) : ℤ))) ≅
      Scheme.Modules.exteriorPower E ((m + 2 : ℕ) : ℤ)) :=
  ⟨@asIso _ _ _ _ _ (@Stacks.SheafOfModules.TopWedge.isIso_detComparison _ X.sheaf F E L
    (_root_.SheafOfModules.algebras _ F) (_root_.SheafOfModules.algebras _ E)
    (_root_.SheafOfModules.algebras _ L) i q w hS.exact hS.mono_f hS.epi_g (m + 1) 0 hF hL)⟩

/-- The first Chern class cap of an invertible module agrees with that of its first exterior
power. -/
private theorem firstChernClassCapChow_exteriorPower_one {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (L : X.Modules) (d : ℤ)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.Modules.exteriorPower L ((1 : ℕ) : ℤ))]
    (x : chowGroup C p (d + 1)) :
    firstChernClassCapChow C d p L x =
      firstChernClassCapChow C d p (Scheme.Modules.exteriorPower L ((1 : ℕ) : ℤ)) x :=
  firstChernClassCapChow_congr C p d
    (show L ≅ Scheme.Modules.exteriorPower L ((1 : ℕ) : ℤ) from
      (_root_.SheafOfModules.algebras _ L).exteriorPowerOneIso.symm) x

/-- **The identity at `π^*α`, from a short exact sequence on the projective bundle.**  Let
`0 ⟶ ℱ ⟶ π^*ℰ ⟶ 𝒪(1) ⟶ 0` be short exact on `𝐏(ℰ)` with `ℱ` of rank `m + 1`.  Additivity of the
first Chern class splits `c₁(π^*ℰ) ∩ β` as `c₁(ℱ) ∩ β + c₁(𝒪(1)) ∩ β`; the inductive hypothesis
`ih` rewrites the first summand as the cap with `⋀^{m+1} ℱ`, the rank-one case rewrites the second
as the cap with `𝒪(1)`, and Stacks 02SP joins the two caps into the cap with
`⋀^{m+1} ℱ ⊗ ⋀¹ 𝒪(1) ≅ ⋀^{m+2} π^*ℰ ≅ π^*⋀^{m+2} ℰ` (Stacks 0B38 and 01CI). -/
private theorem firstChern_eq_firstChernClassCapChow_exteriorPower_bundle (H : TopHalf C)
    (HF : FlatCompat C) (HS : SubAdditive C) (m : ℕ)
    (ih : ∀ ⦃X : Scheme.{u}⦄ (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E : X.Modules)
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1)]
      (k : ℤ) (α : chowGroup C sX k),
      haveI := isInvertible_det E (m + 1)
      firstChern E C sX (m + 1) k α =
        firstChernClassCapChow C (k - 1) sX (Scheme.Modules.exteriorPower E ((m + 1 : ℕ) : ℤ))
          (chowGroupCast C sX (by omega) α))
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1 + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] [E.IsQuasicoherent]
    [Flat (bundleProj E)] [LocallyOfFiniteType (bundleProj E)]
    [hπA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (bundleProj E)).obj E) (m + 1 + 1)]
    (F : (bundle E).Modules) (f : F ⟶ (Scheme.Modules.pullback (bundleProj E)).obj E)
    (g : (Scheme.Modules.pullback (bundleProj E)).obj E ⟶ bundleTwist E) (w : f ≫ g = 0)
    (hSE : (ShortComplex.mk f g w).ShortExact)
    [hrF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (m + 1)]
    (d : ℤ) (β : chowGroup C (bundleProj E ≫ sX) d) :
    haveI := isInvertible_det E (m + 1 + 1)
    haveI := isInvertible_pullback (bundleProj E)
      (Scheme.Modules.exteriorPower E ((m + 1 + 1 : ℕ) : ℤ))
    firstChern ((Scheme.Modules.pullback (bundleProj E)).obj E) C (bundleProj E ≫ sX)
        (m + 1 + 1) d β =
      firstChernClassCapChow C (d - 1) (bundleProj E ≫ sX)
        ((Scheme.Modules.pullback (bundleProj E)).obj
          (Scheme.Modules.exteriorPower E ((m + 1 + 1 : ℕ) : ℤ)))
        (chowGroupCast C (bundleProj E ≫ sX) (by omega) β) := by
  have := isInvertible_det E (m + 1 + 1)
  have hL : AlgebraicGeometry.SheafOfModules.IsInvertible (bundle E).presheaf
      (bundle E).ringCatSheaf.2 (bundleTwist E) := isInvertible_bundleTwist E
  have hOi : AlgebraicGeometry.SheafOfModules.IsInvertible (bundle E).sheaf.obj
      (bundle E).ringCatSheaf.property (bundleTwist E) := hL
  have hO : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (bundleTwist E) 1 := isFiniteLocallyFreeOfRank_one_of_isInvertible _
  have := isInvertible_det F (m + 1)
  have := isInvertible_det (bundleTwist E) 1
  have := isInvertible_det ((Scheme.Modules.pullback (bundleProj E)).obj E) (m + 1 + 1)
  have := isInvertible_pullback (bundleProj E)
    (Scheme.Modules.exteriorPower E ((m + 1 + 1 : ℕ) : ℤ))
  let π := bundleProj E
  have hadd := @firstChern_add_of_shortExact _ H HF HS (m + 1) _ (π ≫ sX) _
    (ShortComplex.mk f g w) hSE 1 hrF hπA hO _ β
  have hK' := @ih _ (π ≫ sX) _ F hrF _ β
  have hO' := firstChern_one (π ≫ sX) H (bundleTwist E) _ β
  obtain ⟨t⟩ := @nonempty_det_tensor_iso _ _ _ _ f g w hSE m hrF hO
  have t' : Scheme.Modules.tensorObj (Scheme.Modules.exteriorPower F ((m + 1 : ℕ) : ℤ))
      (Scheme.Modules.exteriorPower (bundleTwist E) ((1 : ℕ) : ℤ)) ≅
      (Scheme.Modules.pullback π).obj (Scheme.Modules.exteriorPower E ((m + 1 + 1 : ℕ) : ℤ)) :=
    t ≪≫ (Scheme.Modules.exteriorPowerPullbackIso π E _).symm
  rw [show firstChern ((Scheme.Modules.pullback π).obj E) C (π ≫ sX) (m + 1 + 1) d β =
      firstChern (ShortComplex.mk f g w).X₂ C (π ≫ sX) (m + 1 + 1) d β from rfl, hadd, hK', hO',
    firstChernClassCapChow_exteriorPower_one (π ≫ sX) (bundleTwist E),
    firstChernClassCapChow_tensorObj,
    firstChernClassCapChow_congr C (π ≫ sX) (d - 1) t']

/-- **The rank `m + 2` step of `c₁(ℰ) = c₁(⋀ʳ ℰ)`.**  On the projective bundle the tautological
sequence splits off an invertible quotient, additivity and the inductive hypothesis for the
kernel give the identity at `π^*α`, and it descends because `π^*` is injective. -/
private theorem firstChern_eq_firstChernClassCapChow_exteriorPower_succ_succ (H : TopHalf C)
    (HF : FlatCompat C) (HS : SubAdditive C) (m : ℕ)
    (ih : ∀ ⦃X : Scheme.{u}⦄ (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E : X.Modules)
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1)]
      (k : ℤ) (α : chowGroup C sX k),
      haveI := isInvertible_det E (m + 1)
      firstChern E C sX (m + 1) k α =
        firstChernClassCapChow C (k - 1) sX (Scheme.Modules.exteriorPower E ((m + 1 : ℕ) : ℤ))
          (chowGroupCast C sX (by omega) α))
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E : X.Modules)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1 + 1)]
    (k : ℤ) (α : chowGroup C sX k) :
    haveI := isInvertible_det E (m + 1 + 1)
    firstChern E C sX (m + 1 + 1) k α =
      firstChernClassCapChow C (k - 1) sX
        (Scheme.Modules.exteriorPower E ((m + 1 + 1 : ℕ) : ℤ))
        (chowGroupCast C sX (by omega) α) := by
  have := isInvertible_det E (m + 1 + 1)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
    isFiniteLocallyFree_of_rank E (m + 1 + 1)
  have := flat_bundleProj E (m + 1)
  have := locallyOfFiniteType_bundleProj E (m + 1)
  have : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  have hd := relativeDimension_bundleProj E (m + 1)
  have hπA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (bundleProj E)).obj E) (m + 1 + 1) :=
    isFiniteLocallyFreeOfRank_pullback _ E _
  let π := bundleProj E
  let τ : (Scheme.Modules.pullback π).obj E ⟶ bundleTwist E :=
    Stacks.ProjectiveBundleSplitting.tautologicalMap E (bundlePieces E)
  have hτ : Epi τ := Stacks.ProjectiveBundleSplitting.epi_tautologicalMap E (bundlePieces E)
  have hL : AlgebraicGeometry.SheafOfModules.IsInvertible (bundle E).presheaf
      (bundle E).ringCatSheaf.2 (bundleTwist E) := isInvertible_bundleTwist E
  have hK : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (kernel τ) (m + 1) :=
    Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred
      τ hτ hL (m + 1) hπA
  have hT1 : (ShortComplex.mk (kernel.ι τ) τ (kernel.condition τ)).ShortExact :=
    { exact := ShortComplex.exact_kernel τ }
  have := isInvertible_pullback π (Scheme.Modules.exteriorPower E ((m + 1 + 1 : ℕ) : ℤ))
  obtain ⟨β, hβ⟩ : ∃ β, β = flatPullbackChow C (π ≫ sX) sX π rfl (m + 1 + 1 - 1) hd k
    (flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ hd k) α := ⟨_, rfl⟩
  have hbundle := firstChern_eq_firstChernClassCapChow_exteriorPower_bundle H HF HS m ih sX E
    (kernel τ) (kernel.ι τ) τ (kernel.condition τ) hT1 _ β (hrF := hK)
  -- descend
  refine pullback_injective sX E H (m + 1) (k - 1) ?_
  simp only [projectiveBundlePullback]
  refine chowGroup_eq_of_heq C _ ((firstChern_flatPullback_heq sX HF (π ≫ sX) π rfl
    (m + 1 + 1 - 1) hd E (m + 1 + 1) ((Scheme.Modules.pullback π).obj E) (Iso.refl _) k
    α).symm.trans ((heq_of_eq (hβ ▸ hbundle)).trans ?_))
  subst hβ
  refine (firstChernClassCapChow_heq (π ≫ sX) _ (by omega)
    (y := chowGroupCast C _ (by omega) (flatPullbackChow C (π ≫ sX) sX π rfl (m + 1 + 1 - 1) hd
      (k - 1 + 1) (flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ hd _)
      (chowGroupCast C sX (by omega) α))) ?_).trans
    (flatPullbackChow_firstChernClassCapChow_heq C (π ≫ sX) sX π rfl (m + 1 + 1 - 1) hd
      (fun k => flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ hd k)
      (Scheme.Modules.exteriorPower E ((m + 1 + 1 : ℕ) : ℤ))
      ((Scheme.Modules.pullback π).obj (Scheme.Modules.exteriorPower E ((m + 1 + 1 : ℕ) : ℤ)))
      (Iso.refl _) (k - 1) (chowGroupCast C sX (by omega) α) _
      (chowGroupCast_heq C _ _ _)).symm
  refine (chowGroupCast_heq C _ _ _).trans (HEq.trans ?_ (chowGroupCast_heq C _ _ _).symm)
  exact flatPullbackChow_heq C (π ≫ sX) sX π rfl (m + 1 + 1 - 1) hd
    (fun k => flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ hd k)
    (by omega) (chowGroupCast_heq C sX _ α).symm

/-- **`c₁(ℰ) = c₁(⋀ʳ ℰ)`**: for `ℰ` finite locally free of constant rank `r`, the first Chern
class of `ℰ` capped with a class `α ∈ CH_k(X)` is the first Chern class of the invertible module
`⋀ʳ ℰ` capped with `α`. -/
theorem firstChern_eq_firstChernClassCapChow_exteriorPower (H : TopHalf C) (HF : FlatCompat C)
    (HS : SubAdditive C) (r : ℕ) : ∀ ⦃X : Scheme.{u}⦄ (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (k : ℤ) (α : chowGroup C sX k),
    haveI := isInvertible_det E r
    firstChern E C sX r k α =
      firstChernClassCapChow C (k - 1) sX (Scheme.Modules.exteriorPower E (r : ℤ))
        (chowGroupCast C sX (by omega) α) := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro X sX _ E hE k α
  have := isInvertible_det E r
  rcases r with _ | _ | m
  · -- rank zero: `⋀⁰ ℰ ≅ 𝒪_X`, whose first Chern class vanishes
    have e0 : Scheme.Modules.exteriorPower E ((0 : ℕ) : ℤ) ≅ SheafOfModules.unit X.ringCatSheaf :=
      (_root_.SheafOfModules.algebras _ E).exteriorPieceIso_zero
    have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
        (SheafOfModules.unit X.ringCatSheaf) := by
      have := SheafOfModules.isFiniteLocallyFreeOfRank_unit X
      exact isInvertible_of_isFiniteLocallyFreeOfRank_one _
    rw [firstChernClassCapChow_congr C sX (k - 1) e0]
    induction (chowGroupCast C sX (show k = k - 1 + 1 by omega) α) using
      QuotientAddGroup.induction_on with
    | H a => exact (firstChernClassCapOfInvertible_unit C sX (k - 1) a).symm
  · -- rank one: `⋀¹ ℰ ≅ ℰ`
    have := isInvertible_of_rank_one E
    rw [firstChern_one sX H E k α]
    exact firstChernClassCapChow_exteriorPower_one sX E (k - 1) _
  · -- rank `m + 2`: split on the projective bundle
    exact firstChern_eq_firstChernClassCapChow_exteriorPower_succ_succ H HF HS m
      (ih (m + 1) (by omega)) sX E k α

end Stacks.Chow.GenuineChern

end
