module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernRelationTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowCohomologyCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackBivariantClass
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaBijective

/-!
# The Chern classes of a finite locally free module

In Situation 0EDT let `X/B` be good, `ℰ` a finite locally free `𝒪_X`-module of rank `r` and
`(π : P → X, 𝒪_P(1))` its projective bundle. For a morphism `g : X' → X` of good algebraic spaces
over `B` let `π' : P' = P ×_X X' → X'` be the base change, with `𝒪_{P'}(1) = (g')^*𝒪_P(1)`.
**Stacks 0ERY**: there are unique maps `c_i(ℰ) ∩ - : CH_k(X') → CH_{k-i}(X')`, `i = 0, …, r`, with
`c₀(ℰ) ∩ α = α` and

`∑_{i=0}^{r} (-1)^i c₁(𝒪_{P'}(1))^i ∩ π'^*(c_{r-i}(ℰ) ∩ α) = 0`,

and they form a bivariant class `c_i(ℰ)` of degree `i`. **Stacks 0ERZ** calls `c_i(ℰ) ∈ A^i(X)` the
`i`-th Chern class of `ℰ` and `c(ℰ) = c₀(ℰ) + … + c_r(ℰ)` its total Chern class.

## Main definitions

* `AlgebraicGeometry.Space.chernClass`: **Stacks 0ERZ**, `c_i(ℰ) ∈ A^i(X)`.
* `AlgebraicGeometry.Space.totalChernClass`: **Stacks 0ERZ**, `c(ℰ) ∈ A^*(X)`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_chernCap_and_bivariant`: **Stacks 0ERY**.

## Implementation notes

The Chow groups are those of Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK
(`AlgebraicGeometry.Space.chowGroupCanonical`), the bivariant classes those of Stacks 0ERJ over
them (`AlgebraicGeometry.Space.BivariantClassCanonical`), and `A^i(X)` is
`AlgebraicGeometry.Space.chowCohomologyComponentCanonical`.

Existence and uniqueness of the maps are the algebra of
`AlgebraicGeometry.Space.ProjectiveBundleRelation` applied to the projective bundle formula
(Stacks 0ERV) on `P' = P ×_X X'`, which is the projective bundle of `g^*ℰ`
(`AlgebraicGeometry.Space.projectiveBundlePullbackIso`). Bivariance is proved by uniqueness, as
the source indicates: each of the three operations a bivariant class commutes with carries the
relation on one base change to the relation on the other
(`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernRelationTransport`), so it carries the family
`c_j ∩ α` to a family satisfying the relation, which is then the family `c_j ∩ (op α)`.

A bivariant class for the identity of `X` caps a class on a test space `g : X' → X` into
`X ×_X X'`, which is `X'` up to the isomorphism `pullback.snd`; the cap operation of `c_i(ℰ)` is
`c_i(ℰ) ∩ -` on `X'` followed by the flat pullback of relative dimension `0` along that
isomorphism, as for the flat pullback class of Stacks 0ERN at `f = 𝟙 X`.

In rank `0` the projective bundle has no points, so the relation lives in the zero group and the
only map is `c₀ = id`; the pullback in the relation is then the zero map into that group.

## References

* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
* [Stacks Project, Tag 0ERJ](https://stacks.math.columbia.edu/tag/0ERJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Flat pullback along an isomorphism -/

section IsoPullback

variable (D : BaseSpaceDimensionSituation.{u})
    {P P' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sP : P ⟶ D.space) (hP : D.IsGood sP) (sP' : P' ⟶ D.space) (hP' : D.IsGood sP')

/-- Flat pullback along `inv φ` undoes flat pullback along an isomorphism `φ`, on cycles. -/
theorem flatPullbackMap_inv_flatPullbackMap_of_isIso (φ : P' ⟶ P) [IsIso φ]
    (hφB : φ ≫ sP = sP') (hψB : inv φ ≫ sP' = sP) (N : ℤ) (ξ : CycleGroup D sP N) :
    flatPullbackMap D sP hP sP' hP' (inv φ) hψB 0
        (isFlat_and_hasRelativeDimension_zero_of_isIso D sP' hP' (inv φ)).1
        (isFlat_and_hasRelativeDimension_zero_of_isIso D sP' hP' (inv φ)).2 N N (by simp)
        (flatPullbackMap D sP' hP' sP hP φ hφB 0
          (isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP φ).1
          (isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP φ).2 N N (by simp) ξ) =
      ξ := by
  have hφ := isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP φ
  have hψ := isFlat_and_hasRelativeDimension_zero_of_isIso D sP' hP' (inv φ)
  have hid := isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP (𝟙 P)
  refine Subtype.ext ?_
  have h1 := congrArg (fun χ => (χ ξ).1)
    (flatPullbackMap_comp D sP hP sP' hP' sP hP (inv φ) φ hψB hφB 0 0 hψ.1 hψ.2 hφ.1 hφ.2 N N
      (by simp))
  refine (Eq.trans ?_ h1.symm).trans ((flatPullbackMap_coe_congr D sP hP sP hP
    (IsIso.inv_hom_id φ) _ (Category.id_comp sP) rfl _ hid.1 _ hid.2 N N N N _ (by simp) _ _
    rfl).trans (flatPullbackMap_id_coe D sP hP (Category.id_comp sP) hid.1 hid.2 N N (by simp) ξ))
  exact coe_flatPullbackMap_congr D sP' hP' sP hP (inv φ) hψB 0 hψ.1 hψ.2 (by simp) rfl (by simp)
    (by simp) _ _
    (coe_flatPullbackMap_congr D sP hP sP' hP' φ hφB 0 hφ.1 hφ.2 rfl (by simp) (by simp)
      (by simp) _ _ rfl)

/-- **Flat pullback along an isomorphism is bijective on Chow groups.** -/
theorem bijective_flatPullbackChowMapCanonical_of_isIso (φ : P' ⟶ P) (hφ : IsIso φ)
    (hφB : φ ≫ sP = sP') (N : ℤ) :
    Function.Bijective (flatPullbackChowMapCanonical.{u + 1} D sP' hP' sP hP φ hφB 0
      (@isFlat_and_hasRelativeDimension_zero_of_isIso D P P' sP hP φ hφ).1
      (@isFlat_and_hasRelativeDimension_zero_of_isIso D P P' sP hP φ hφ).2 N N
      (by simp)) := by
  have hψB : inv φ ≫ sP' = sP := by rw [← hφB, IsIso.inv_hom_id_assoc]
  have hφB' : inv (inv φ) ≫ sP = sP' := by rw [IsIso.inv_inv, hφB]
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · obtain ⟨ξ, rfl⟩ : ∃ ξ, chowClassCanonical.{u + 1} D sP hP N ξ = x :=
      QuotientAddGroup.mk'_surjective _ x
    obtain ⟨η, rfl⟩ : ∃ η, chowClassCanonical.{u + 1} D sP hP N η = y :=
      QuotientAddGroup.mk'_surjective _ y
    have h := congrArg (flatPullbackChowMapCanonical.{u + 1} D sP hP sP' hP' (inv φ) hψB 0
      (isFlat_and_hasRelativeDimension_zero_of_isIso D sP' hP' (inv φ)).1
      (isFlat_and_hasRelativeDimension_zero_of_isIso D sP' hP' (inv φ)).2 N N (by simp)) hxy
    rw [flatPullbackChowMapCanonical_chowClassCanonical,
      flatPullbackChowMapCanonical_chowClassCanonical,
      flatPullbackChowMapCanonical_chowClassCanonical,
      flatPullbackChowMapCanonical_chowClassCanonical,
      flatPullbackMap_inv_flatPullbackMap_of_isIso D sP hP sP' hP' φ hφB hψB,
      flatPullbackMap_inv_flatPullbackMap_of_isIso D sP hP sP' hP' φ hφB hψB] at h
    exact h
  · obtain ⟨η, rfl⟩ : ∃ η, chowClassCanonical.{u + 1} D sP' hP' N η = y :=
      QuotientAddGroup.mk'_surjective _ y
    refine ⟨chowClassCanonical.{u + 1} D sP hP N
      (flatPullbackMap D sP hP sP' hP' (inv φ) hψB 0
        (isFlat_and_hasRelativeDimension_zero_of_isIso D sP' hP' (inv φ)).1
        (isFlat_and_hasRelativeDimension_zero_of_isIso D sP' hP' (inv φ)).2 N N (by simp)
        η), ?_⟩
    rw [flatPullbackChowMapCanonical_chowClassCanonical]
    have h := flatPullbackMap_inv_flatPullbackMap_of_isIso D sP' hP' sP hP (inv φ) hψB hφB' N η
    simp only [IsIso.inv_inv] at h
    exact congrArg _ h

end IsoPullback

/-! ### The relation on the base change of the projective bundle to a test space -/

section Datum

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [E.IsQuasicoherentOnSite] (n : ℕ)
    (hr : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E (n + 1))

/-- The projection `π : P = 𝐏(ℰ) → X` of the projective bundle, as a morphism of presheaves. -/
abbrev chernBundleProj (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E) :
    (projectiveBundle (X := ⟨X, hX.1⟩) E hfree).1 ⟶ X :=
  (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom

local notation "π₀" => chernBundleProj D sX hX E hr.isFiniteLocallyFreeOnSite

/-- `(n : ℤ) = (n + 1) - 1`: the relative dimension of the projection of the projective bundle of
a module of rank `n + 1`, written as in Stacks 0ERY. -/
theorem chernRank_sub_one : (n : ℤ) = ((n + 1 : ℕ) : ℤ) - 1 := by
  push_cast
  ring

/-- **The left-hand side of the relation of Stacks 0ERY on a test space** `g : X' → X`:
`∑_{i=0}^{r} (-1)^i c₁(𝒪_{P'}(1))^i ∩ π'^*(b_{r-i}) ∈ CH_{k-r+(r-1)}(P')` for
`P' = P ×_X X'`, `π' : P' → X'` the base change of `π`, `𝒪_{P'}(1)` the pullback of `𝒪_P(1)`
and `r = n + 1`. -/
abbrev chernRelationSumAt {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (k : ℤ)
    (b : ∀ j : Fin (n + 1 + 1), chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k - ((j : ℕ) : ℤ))) :
    chowGroupCanonical.{u + 1} D (pullback.snd π₀ g ≫ g ≫ sX)
      (isGood_projectiveBundleBaseChangeProj_comp D sX hX E hr.isFiniteLocallyFreeOnSite g hY)
      (k - ((n + 1 : ℕ) : ℤ) + (((n + 1 : ℕ) : ℤ) - 1)) :=
  bundleRelationSumAt D (g ≫ sX) hY _
    (isGood_projectiveBundleBaseChangeProj_comp D sX hX E hr.isFiniteLocallyFreeOnSite g hY)
    (pullback.snd π₀ g) rfl n
    (isFlat_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite g hY n hr)
    (hasRelativeDimension_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite g
      hY n hr)
    (projectiveBundleBaseChangeTwist D sX hX E hr.isFiniteLocallyFreeOnSite g hY)
    (isInvertibleModule_projectiveBundleBaseChangeTwist D sX hX E hr.isFiniteLocallyFreeOnSite g
      hY) _ (chernRank_sub_one n) (n + 1) k b

/-- **Stacks 0ERV on the base change `P' = P ×_X X'`**: the map of the projective bundle formula
for `(π' : P' → X', 𝒪_{P'}(1))` is bijective, in every degree. `P'` is the projective bundle of
`g^*ℰ` (`AlgebraicGeometry.Space.projectiveBundlePullbackIso`), compatibly with the twists
(`AlgebraicGeometry.Space.projectiveBundleFiberProductTwistIso`), and flat pullback along that
isomorphism is bijective. -/
theorem bijective_chernBundleSum {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (N : ℤ)
    (d : Fin (n + 1) → ℤ) (hd : ∀ i, d i + (((n + 1 : ℕ) : ℤ) - 1) = N + (i : ℕ)) :
    Function.Bijective (ProjectiveBundleRelation.bundleSum
      (A := fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m)
      (P := fun m => chowGroupCanonical.{u + 1} D (pullback.snd π₀ g ≫ g ≫ sX)
        (isGood_projectiveBundleBaseChangeProj_comp D sX hX E hr.isFiniteLocallyFreeOnSite g hY)
        m) _
      (bundleRelationPull D (g ≫ sX) hY _
        (isGood_projectiveBundleBaseChangeProj_comp D sX hX E hr.isFiniteLocallyFreeOnSite g hY)
        (pullback.snd π₀ g) rfl n
        (isFlat_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite g hY n hr)
        (hasRelativeDimension_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite
          g hY n hr) _ (chernRank_sub_one n))
      (bundleFormulaCap D _
        (isGood_projectiveBundleBaseChangeProj_comp D sX hX E hr.isFiniteLocallyFreeOnSite g hY)
        (projectiveBundleBaseChangeTwist D sX hX E hr.isFiniteLocallyFreeOnSite g hY)
        (isInvertibleModule_projectiveBundleBaseChangeTwist D sX hX E hr.isFiniteLocallyFreeOnSite
          g hY))
      (n + 1) N d hd) := by
  have hd' : ∀ i, d i + (n : ℤ) = N + (i : ℕ) := fun i => by
    have := hd i
    push_cast at this
    omega
  let gs := goodSpaceHom D sX hX g hY
  have hr' := isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem gs E (n + 1) hr
  have hbijE := bijective_bundleFormulaMap_projectiveBundle_of_twist D (X := ⟨Y, hY.1⟩) (g ≫ sX)
    hY ((modulePullback D.site D.base D.base_mem gs).obj E) n hr'
    (fun U G G' hG hG' v σ hσ hfree hfree' =>
      ⟨@projectiveBundleSplitEpiTwistIso _ _ _ U G G' hG hG' v σ hσ hfree hfree'⟩) N d hd'
  have hiso : IsIso (projectiveBundlePullbackIso gs E hr.isFiniteLocallyFreeOnSite).inv.hom :=
    ⟨⟨(projectiveBundlePullbackIso gs E hr.isFiniteLocallyFreeOnSite).hom.hom,
      congrArg (fun f => f.hom)
        (projectiveBundlePullbackIso gs E hr.isFiniteLocallyFreeOnSite).inv_hom_id,
      congrArg (fun f => f.hom)
        (projectiveBundlePullbackIso gs E hr.isFiniteLocallyFreeOnSite).hom_inv_id⟩⟩
  have hφπ := projectiveBundlePullbackIso_inv_comp_proj D (X := ⟨X, hX.1⟩) E n hr gs
  have hφB : (projectiveBundlePullbackIso gs E hr.isFiniteLocallyFreeOnSite).inv.hom ≫
      ((@projectiveBundleProj D.site D.base D.base_mem ⟨Y, hY.1⟩
        ((modulePullback D.site D.base D.base_mem gs).obj E)
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hY.1 hr')
        hr'.isFiniteLocallyFreeOnSite).hom ≫ g ≫ sX) = pullback.snd π₀ g ≫ g ≫ sX := by
    rw [← Category.assoc, hφπ]
    rfl
  have hfun : ProjectiveBundleRelation.bundleSum
      (A := fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m)
      (P := fun m => chowGroupCanonical.{u + 1} D (pullback.snd π₀ g ≫ g ≫ sX)
        (isGood_projectiveBundleBaseChangeProj_comp D sX hX E hr.isFiniteLocallyFreeOnSite g hY)
        m) _
      (bundleRelationPull D (g ≫ sX) hY _
        (isGood_projectiveBundleBaseChangeProj_comp D sX hX E hr.isFiniteLocallyFreeOnSite g hY)
        (pullback.snd π₀ g) rfl n
        (isFlat_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite g hY n hr)
        (hasRelativeDimension_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite
          g hY n hr) _ (chernRank_sub_one n))
      (bundleFormulaCap D _
        (isGood_projectiveBundleBaseChangeProj_comp D sX hX E hr.isFiniteLocallyFreeOnSite g hY)
        (projectiveBundleBaseChangeTwist D sX hX E hr.isFiniteLocallyFreeOnSite g hY)
        (isInvertibleModule_projectiveBundleBaseChangeTwist D sX hX E hr.isFiniteLocallyFreeOnSite
          g hY))
      (n + 1) N d hd =
      (flatPullbackChowMapCanonical.{u + 1} D _
        (isGood_projectiveBundleBaseChangeProj_comp D sX hX E hr.isFiniteLocallyFreeOnSite g hY) _
        (isGood_projectiveBundleProj_comp_of_rank D (X := ⟨Y, hY.1⟩) (g ≫ sX) hY _ n hr')
        (projectiveBundlePullbackIso gs E hr.isFiniteLocallyFreeOnSite).inv.hom hφB 0
        (@isFlat_and_hasRelativeDimension_zero_of_isIso D _ _ _
          (isGood_projectiveBundleProj_comp_of_rank D (X := ⟨Y, hY.1⟩) (g ≫ sX) hY _ n hr')
          (projectiveBundlePullbackIso gs E hr.isFiniteLocallyFreeOnSite).inv.hom hiso).1
        (@isFlat_and_hasRelativeDimension_zero_of_isIso D _ _ _
          (isGood_projectiveBundleProj_comp_of_rank D (X := ⟨Y, hY.1⟩) (g ≫ sX) hY _ n hr')
          (projectiveBundlePullbackIso gs E hr.isFiniteLocallyFreeOnSite).inv.hom hiso).2 N N
          (by simp)).comp
        (bundleFormulaMap D (X := Y) (g ≫ sX) hY _
          (isGood_projectiveBundleProj_comp_of_rank D (X := ⟨Y, hY.1⟩) (g ≫ sX) hY _ n hr')
          _ rfl n
          (@isFlat_projectiveBundleProj D.site D.base D.base_mem ⟨Y, hY.1⟩ _
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hY.1 hr') n hr'
            hr'.isFiniteLocallyFreeOnSite)
          (@hasRelativeDimension_projectiveBundleProj D.site D.base D.base_mem ⟨Y, hY.1⟩ _
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hY.1 hr') n hr'
            hr'.isFiniteLocallyFreeOnSite)
          (@projectiveBundleTwist D.site D.base D.base_mem ⟨Y, hY.1⟩ _
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hY.1 hr')
            hr'.isFiniteLocallyFreeOnSite).obj
          (@isInvertibleModule_projectiveBundleTwist D.site D.base D.base_mem ⟨Y, hY.1⟩ _
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hY.1 hr')
            hr'.isFiniteLocallyFreeOnSite) N d hd') := by
    refine AddMonoidHom.ext fun a => ?_
    exact @bundleFormulaMap_of_isIso D Y _ _ (g ≫ sX) hY _
      (isGood_projectiveBundleProj_comp_of_rank D (X := ⟨Y, hY.1⟩) (g ≫ sX) hY _ n hr') _
      (isGood_projectiveBundleBaseChangeProj_comp D sX hX E hr.isFiniteLocallyFreeOnSite g hY)
      _ rfl (pullback.snd π₀ g) rfl n _ _
      (isFlat_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite g hY n hr)
      (hasRelativeDimension_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite g
        hY n hr) _ _ _ _ (projectiveBundlePullbackIso gs E hr.isFiniteLocallyFreeOnSite).inv.hom
      hiso
      hφB hφπ (projectiveBundleFiberProductTwistIso D (X := ⟨X, hX.1⟩) E n hr gs)
      N d hd' a
  rw [hfun, AddMonoidHom.coe_comp]
  exact (bijective_flatPullbackChowMapCanonical_of_isIso D _ _ _ _
    (projectiveBundlePullbackIso gs E hr.isFiniteLocallyFreeOnSite).inv.hom hiso hφB N).comp hbijE

/-- **Existence (Stacks 0ERY)**: on every test space `g : X' → X` there are maps
`c_j ∩ - : CH_k(X') → CH_{k-j}(X')`, `j = 0, …, r`, with `c₀ = id` satisfying the relation. -/
theorem exists_chernCapFamily {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) :
    ∃ c : ∀ (j : Fin (n + 1 + 1)) (k : ℤ), chowGroupCanonical.{u + 1} D (g ≫ sX) hY k →+
        chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k - ((j : ℕ) : ℤ)),
      (∀ k α, c 0 k α = ProjectiveBundleRelation.degreeCast
        (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) (by simp) α) ∧
        ∀ k α, chernRelationSumAt D sX hX E n hr g hY k (fun j => c j k α) = 0 :=
  ProjectiveBundleRelation.exists_relationSum_eq_zero _ _ _ (n + 1)
    (fun N d hd => bijective_chernBundleSum D sX hX E n hr g hY N d hd)

/-- **The maps `c_j(ℰ) ∩ -` on a test space** `g : X' → X`, `j = 0, …, r = n + 1`, given by
Stacks 0ERY. -/
def chernCapFamily {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) :
    ∀ (j : Fin (n + 1 + 1)) (k : ℤ), chowGroupCanonical.{u + 1} D (g ≫ sX) hY k →+
      chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k - ((j : ℕ) : ℤ)) :=
  (exists_chernCapFamily D sX hX E n hr g hY).choose

/-- The map `c₀(ℰ) ∩ -` is the identity, up to the degree identification `k - 0 = k`. -/
theorem chernCapFamily_zero {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    chernCapFamily D sX hX E n hr g hY 0 k α = ProjectiveBundleRelation.degreeCast
      (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) (by simp) α :=
  (exists_chernCapFamily D sX hX E n hr g hY).choose_spec.1 k α

/-- The classes `c_j(ℰ) ∩ α` satisfy the projective bundle relation
`∑_{i=0}^{r} (-1)^i c₁(𝒪_{P'}(1))^i ∩ π'^*(c_{r-i}(ℰ) ∩ α) = 0` on `P' = P ×_X X'`. -/
theorem chernRelationSumAt_chernCapFamily {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (k : ℤ) (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    chernRelationSumAt D sX hX E n hr g hY k (fun j => chernCapFamily D sX hX E n hr g hY j k α) =
      0 :=
  (exists_chernCapFamily D sX hX E n hr g hY).choose_spec.2 k α

/-- **Uniqueness, pointwise (Stacks 0ERY)**: two families `b_j ∈ CH_{k-j}(X')` with `b₀ = b'₀`
which both satisfy the relation on `P' = P ×_X X'` agree. -/
theorem eq_of_chernRelationSumAt_eq_zero {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (k : ℤ) (b b' : ∀ j : Fin (n + 1 + 1),
      chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k - ((j : ℕ) : ℤ)))
    (h0 : b 0 = b' 0) (hb : chernRelationSumAt D sX hX E n hr g hY k b = 0)
    (hb' : chernRelationSumAt D sX hX E n hr g hY k b' = 0) : b = b' :=
  ProjectiveBundleRelation.eq_of_relationSumAt_eq_zero _ _ _ (n + 1) k
    (fun d hd a ha => by
      have hinj := (bijective_chernBundleSum D sX hX E n hr g hY _ d hd).1
      intro i
      exact congrFun (hinj (ha.trans (map_zero _).symm)) i)
    b b' h0 hb hb'

/-- The maps `c_j(ℰ) ∩ -` agree with every family satisfying the characterization of
Stacks 0ERY. -/
theorem chernCapFamily_unique {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (c : ∀ (j : Fin (n + 1 + 1)) (k : ℤ), chowGroupCanonical.{u + 1} D (g ≫ sX) hY k →+
        chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k - ((j : ℕ) : ℤ)))
    (h0 : ∀ k α, c 0 k α = ProjectiveBundleRelation.degreeCast
        (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) (by simp) α)
    (hc : ∀ k α, chernRelationSumAt D sX hX E n hr g hY k (fun j => c j k α) = 0) :
    c = chernCapFamily D sX hX E n hr g hY := by
  funext j k
  refine AddMonoidHom.ext fun α => ?_
  exact congrFun (eq_of_chernRelationSumAt_eq_zero D sX hX E n hr g hY k _ _
    ((h0 k α).trans (chernCapFamily_zero D sX hX E n hr g hY k α).symm) (hc k α)
    (chernRelationSumAt_chernCapFamily D sX hX E n hr g hY k α)) j

end Datum

/-! ### Transport along equal degrees -/

/-- The degree bookkeeping of a class of degree `p` under flat pullback of relative dimension
`m`: `(k - p) + m = (k + m) - p`. -/
theorem chernDegree_sub_add (k m p : ℤ) : k - p + m = k + m - p := by
  ring

/-- The degree bookkeeping of a class of degree `p` under a Gysin map:
`(k + 1) - p = (k - p) + 1`. -/
theorem chernDegree_add_one_sub (k p : ℤ) : k + 1 - p = k - p + 1 := by
  ring

section DegreeCast

variable (D : BaseSpaceDimensionSituation.{u})

/-- Proper pushforward commutes with the identification of Chow groups of equal degrees. -/
theorem chowGroupCanonicalProperPushforward_degreeCast
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p) {a b : ℤ} (h : a = b)
    (x : chowGroupCanonical.{u + 1} D sX hX a) :
    chowGroupCanonicalProperPushforward.{u + 1} D sX hX sY hY hpB hp b
        (ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D sX hX m) h x) =
      ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D sY hY m) h
        (chowGroupCanonicalProperPushforward.{u + 1} D sX hX sY hY hpB hp a x) := by
  subst h
  rfl

/-- Flat pullback commutes with the identification of Chow groups of equal degrees. -/
theorem flatPullbackChowMapCanonical_degreeCast
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX)
    (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) {a b a' b' : ℤ} (h : a = b)
    (h' : a' = b') (ha : a + (r : ℤ) = a') (hb : b + (r : ℤ) = b')
    (x : chowGroupCanonical.{u + 1} D sY hY a) :
    flatPullbackChowMapCanonical.{u + 1} D sX hX sY hY f hbase r hflat hr b b' hb
        (ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D sY hY m) h x) =
      ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D sX hX m) h'
        (flatPullbackChowMapCanonical.{u + 1} D sX hX sY hY f hbase r hflat hr a a' ha x) := by
  subst h h'
  rfl

/-- The Gysin map commutes with the identification of Chow groups of equal degrees. -/
theorem sectionGysinChowGroupMap_degreeCast
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (σ : L.sections)
    (hL : IsInvertibleSheaf D p hp L) {a b : ℤ} (h : a = b) (h₁ : a + 1 = b + 1)
    (x : chowGroupCanonical.{u + 1} D p hp (a + 1)) :
    sectionGysinChowGroupMap D p hp L σ hL b
        (ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D p hp m) h₁ x) =
      ProjectiveBundleRelation.degreeCast
        (fun m => chowGroupCanonical.{u + 1} D ((vanishingLocus D p hp L σ).1.ι ≫ p)
          (isGood_vanishingLocus D p hp L σ) m) h
        (sectionGysinChowGroupMap D p hp L σ hL a x) := by
  subst h
  rfl

/-- The class of a cycle, transported along an equality of degrees. -/
theorem degreeCast_chowClassCanonical {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) {a b : ℤ} (h : a = b) (ξ : CycleGroup D sX a) :
    ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D sX hX m) h
        (chowClassCanonical.{u + 1} D sX hX a ξ) =
      chowClassCanonical.{u + 1} D sX hX b (cycleGroupCast D sX h ξ) := by
  subst h
  rfl

end DegreeCast

/-! ### The Chern cap maps commute with the three operations -/

section Naturality

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [E.IsQuasicoherentOnSite] (n : ℕ)
    (hr : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E (n + 1))

local notation "π₀" => chernBundleProj D sX hX E hr.isFiniteLocallyFreeOnSite

/-- The morphism `P ×_X Y₂ ⟶ P ×_X Y₁` over a morphism `h : Y₂ ⟶ Y₁` of test spaces. -/
abbrev chernBaseChangeMap {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X) (h : Y₂ ⟶ Y₁) :
    pullback π₀ (h ≫ g) ⟶ pullback π₀ g :=
  pullback.lift (pullback.fst π₀ (h ≫ g)) (pullback.snd π₀ (h ≫ g) ≫ h)
    (by rw [pullback.condition, Category.assoc])

/-- The square formed by `chernBaseChangeMap` and the projections to `Y₂` and `Y₁` commutes. -/
theorem chernBaseChangeMap_snd {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X) (h : Y₂ ⟶ Y₁) :
    chernBaseChangeMap D sX hX E n hr g h ≫ pullback.snd π₀ g = pullback.snd π₀ (h ≫ g) ≫ h :=
  pullback.lift_snd _ _ _

/-- `chernBaseChangeMap` commutes with the projections to `P`. -/
theorem chernBaseChangeMap_fst {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X) (h : Y₂ ⟶ Y₁) :
    chernBaseChangeMap D sX hX E n hr g h ≫ pullback.fst π₀ g = pullback.fst π₀ (h ≫ g) :=
  pullback.lift_fst _ _ _

/-- `chernBaseChangeMap` commutes with the structure morphisms of `P ×_X Y₂` and `P ×_X Y₁` to
the base. -/
theorem chernBaseChangeMap_base {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X) (h : Y₂ ⟶ Y₁) :
    chernBaseChangeMap D sX hX E n hr g h ≫ (pullback.snd π₀ g ≫ g ≫ sX) =
      pullback.snd π₀ (h ≫ g) ≫ (h ≫ g) ≫ sX := by
  rw [← Category.assoc, chernBaseChangeMap_snd]
  simp only [Category.assoc]

/-- The square formed by `P ×_X Y₂ ⟶ P ×_X Y₁` and `h : Y₂ ⟶ Y₁` is cartesian. -/
theorem isPullback_chernBaseChangeMap {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X) (h : Y₂ ⟶ Y₁) :
    IsPullback (pullback.snd π₀ (h ≫ g)) (chernBaseChangeMap D sX hX E n hr g h) h
      (pullback.snd π₀ g) := by
  have t : IsPullback (chernBaseChangeMap D sX hX E n hr g h ≫ pullback.fst π₀ g)
      (pullback.snd π₀ (h ≫ g)) π₀ (h ≫ g) := by
    rw [chernBaseChangeMap_fst]
    exact IsPullback.of_hasPullback _ _
  exact (IsPullback.of_right t (chernBaseChangeMap_snd D sX hX E n hr g h)
    (IsPullback.of_hasPullback π₀ g)).flip

/-- `𝒪_{P ×_X Y₂}(1)` is the inverse image of `𝒪_{P ×_X Y₁}(1)`. -/
def chernBaseChangeTwistIso {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X) (hY₁ : D.IsGood (g ≫ sX))
    (h : Y₂ ⟶ Y₁) (hY₂ : D.IsGood ((h ≫ g) ≫ sX)) :
    (modulePullback D.site D.base D.base_mem
      (ObjectProperty.homMk (chernBaseChangeMap D sX hX E n hr g h) :
        (⟨pullback π₀ (h ≫ g), (isGood_projectiveBundleBaseChangeProj_comp D sX hX E
          hr.isFiniteLocallyFreeOnSite (h ≫ g) hY₂).1⟩ :
          AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨pullback π₀ g, (isGood_projectiveBundleBaseChangeProj_comp D sX hX E
          hr.isFiniteLocallyFreeOnSite g hY₁).1⟩)).obj
        (projectiveBundleBaseChangeTwist D sX hX E hr.isFiniteLocallyFreeOnSite g hY₁) ≅
      projectiveBundleBaseChangeTwist D sX hX E hr.isFiniteLocallyFreeOnSite (h ≫ g) hY₂ :=
  (modulePullbackCompIsoOfEq D.site D.base D.base_mem
    (ObjectProperty.homMk (chernBaseChangeMap D sX hX E n hr g h) :
        (⟨pullback π₀ (h ≫ g), (isGood_projectiveBundleBaseChangeProj_comp D sX hX E
          hr.isFiniteLocallyFreeOnSite (h ≫ g) hY₂).1⟩ :
          AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨pullback π₀ g, (isGood_projectiveBundleBaseChangeProj_comp D sX hX E
          hr.isFiniteLocallyFreeOnSite g hY₁).1⟩)
    (projectiveBundleBaseChangeMap D sX hX E hr.isFiniteLocallyFreeOnSite g hY₁)
    (h := projectiveBundleBaseChangeMap D sX hX E hr.isFiniteLocallyFreeOnSite (h ≫ g) hY₂)
    (ObjectProperty.hom_ext _ (chernBaseChangeMap_fst D sX hX E n hr g h))).app
      (projectiveBundleTwist (X := ⟨X, hX.1⟩) E hr.isFiniteLocallyFreeOnSite).obj

/-- The maps `c_j(ℰ) ∩ α` agree with any family `b` satisfying the relation with `b₀ = c₀ ∩ α`. -/
private theorem chernCapFamily_apply_eq_of_chernRelationSumAt_eq_zero {Y : D.Ambient}
    (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (k : ℤ) (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k)
    (b : ∀ j : Fin (n + 1 + 1), chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k - ((j : ℕ) : ℤ)))
    (h0 : chernCapFamily D sX hX E n hr g hY 0 k α = b 0)
    (hb : chernRelationSumAt D sX hX E n hr g hY k b = 0) (j : Fin (n + 1 + 1)) :
    chernCapFamily D sX hX E n hr g hY j k α = b j :=
  congrFun (eq_of_chernRelationSumAt_eq_zero D sX hX E n hr g hY k _ b h0
    (chernRelationSumAt_chernCapFamily D sX hX E n hr g hY k α) hb) j

/-- The maps `c_j(ℰ) ∩ α` on `Y₁` agree with any family `b` with `b₀ = c₀ ∩ α` whose relation sum
is the image under an additive map `F` of the relation sum of the family `c_j(ℰ) ∩ α₂` on `Y₂`. -/
private theorem chernCapFamily_apply_eq_of_map_chernRelationSumAt {Y₁ Y₂ : D.Ambient}
    (g₁ : Y₁ ⟶ X) (hY₁ : D.IsGood (g₁ ≫ sX)) (g₂ : Y₂ ⟶ X) (hY₂ : D.IsGood (g₂ ≫ sX))
    (k₁ k₂ : ℤ)
    (F : chowGroupCanonical.{u + 1} D (pullback.snd π₀ g₂ ≫ g₂ ≫ sX)
        (isGood_projectiveBundleBaseChangeProj_comp D sX hX E hr.isFiniteLocallyFreeOnSite g₂ hY₂)
        (k₂ - ((n + 1 : ℕ) : ℤ) + (((n + 1 : ℕ) : ℤ) - 1)) →+
      chowGroupCanonical.{u + 1} D (pullback.snd π₀ g₁ ≫ g₁ ≫ sX)
        (isGood_projectiveBundleBaseChangeProj_comp D sX hX E hr.isFiniteLocallyFreeOnSite g₁ hY₁)
        (k₁ - ((n + 1 : ℕ) : ℤ) + (((n + 1 : ℕ) : ℤ) - 1)))
    (α₁ : chowGroupCanonical.{u + 1} D (g₁ ≫ sX) hY₁ k₁)
    (α₂ : chowGroupCanonical.{u + 1} D (g₂ ≫ sX) hY₂ k₂)
    (b : ∀ j : Fin (n + 1 + 1), chowGroupCanonical.{u + 1} D (g₁ ≫ sX) hY₁ (k₁ - ((j : ℕ) : ℤ)))
    (h0 : chernCapFamily D sX hX E n hr g₁ hY₁ 0 k₁ α₁ = b 0)
    (hrel : F (chernRelationSumAt D sX hX E n hr g₂ hY₂ k₂
      (fun j => chernCapFamily D sX hX E n hr g₂ hY₂ j k₂ α₂)) =
      chernRelationSumAt D sX hX E n hr g₁ hY₁ k₁ b) (j : Fin (n + 1 + 1)) :
    chernCapFamily D sX hX E n hr g₁ hY₁ j k₁ α₁ = b j :=
  chernCapFamily_apply_eq_of_chernRelationSumAt_eq_zero D sX hX E n hr g₁ hY₁ k₁ α₁ b h0
    (hrel.symm.trans (by rw [chernRelationSumAt_chernCapFamily, map_zero])) j

/-- **Stacks 0ERY, proper pushforward**: `c_j(ℰ) ∩ h_*α = h_*(c_j(ℰ) ∩ α)` for a proper morphism
`h : Y₂ ⟶ Y₁` of test spaces. -/
theorem chernCapFamily_properPushforward {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X)
    (hY₁ : D.IsGood (g ≫ sX)) (h : Y₂ ⟶ Y₁) (hY₂ : D.IsGood ((h ≫ g) ≫ sX))
    (hh : IsProper D.site D.base D.base_mem h) (j : Fin (n + 1 + 1)) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D ((h ≫ g) ≫ sX) hY₂ k) :
    chernCapFamily D sX hX E n hr g hY₁ j k
        (chowGroupCanonicalProperPushforward.{u + 1} D _ hY₂ _ hY₁ (Category.assoc h g sX).symm hh
          k α) =
      chowGroupCanonicalProperPushforward.{u + 1} D _ hY₂ _ hY₁ (Category.assoc h g sX).symm hh _
        (chernCapFamily D sX hX E n hr (h ≫ g) hY₂ j k α) := by
  have hP₁ := isGood_projectiveBundleBaseChangeProj_comp D sX hX E hr.isFiniteLocallyFreeOnSite g
    hY₁
  have hP₂ := isGood_projectiveBundleBaseChangeProj_comp D sX hX E hr.isFiniteLocallyFreeOnSite
    (h ≫ g) hY₂
  have sq := isPullback_chernBaseChangeMap D sX hX E n hr g h
  have hPp : IsProper D.site D.base D.base_mem (chernBaseChangeMap D sX hX E n hr g h) :=
    isProper_of_isPullback D.site D.base D.base_mem hP₂.1 hY₂.1 hP₁.1 hY₁.1 sq hh
  have hrel := properPushforward_bundleRelationSumAt D (g ≫ sX) hY₁ ((h ≫ g) ≫ sX) hY₂ _ hP₁ _
    hP₂ (pullback.snd π₀ g) rfl (pullback.snd π₀ (h ≫ g)) rfl n
    (isFlat_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite g hY₁ n hr)
    (hasRelativeDimension_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite g
      hY₁ n hr)
    (isFlat_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite (h ≫ g) hY₂ n
      hr)
    (hasRelativeDimension_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite
      (h ≫ g) hY₂ n hr)
    _ (isInvertibleModule_projectiveBundleBaseChangeTwist D sX hX E hr.isFiniteLocallyFreeOnSite g
      hY₁)
    _ (isInvertibleModule_projectiveBundleBaseChangeTwist D sX hX E hr.isFiniteLocallyFreeOnSite
      (h ≫ g) hY₂)
    h (Category.assoc h g sX).symm hh (chernBaseChangeMap D sX hX E n hr g h)
    (chernBaseChangeMap_base D sX hX E n hr g h) hPp sq
    (chernBaseChangeTwistIso D sX hX E n hr g hY₁ h hY₂) _ (chernRank_sub_one n) (n + 1) k
    (fun j => chernCapFamily D sX hX E n hr (h ≫ g) hY₂ j k α)
  have h0 : chernCapFamily D sX hX E n hr g hY₁ 0 k
        (chowGroupCanonicalProperPushforward.{u + 1} D _ hY₂ _ hY₁ (Category.assoc h g sX).symm hh
          k α) =
      chowGroupCanonicalProperPushforward.{u + 1} D _ hY₂ _ hY₁ (Category.assoc h g sX).symm hh _
        (chernCapFamily D sX hX E n hr (h ≫ g) hY₂ 0 k α) := by
    rw [chernCapFamily_zero, chernCapFamily_zero, chowGroupCanonicalProperPushforward_degreeCast]
  exact chernCapFamily_apply_eq_of_map_chernRelationSumAt D sX hX E n hr g hY₁ (h ≫ g) hY₂ k k _ _
    α _ h0 hrel j

/-- **Stacks 0ERY, flat pullback**: `c_j(ℰ) ∩ h^*α = h^*(c_j(ℰ) ∩ α)` for a flat morphism
`h : Y₂ ⟶ Y₁` of test spaces of relative dimension `m`. -/
theorem chernCapFamily_flatPullback {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X)
    (hY₁ : D.IsGood (g ≫ sX)) (h : Y₂ ⟶ Y₁) (hY₂ : D.IsGood ((h ≫ g) ≫ sX)) (m : ℕ)
    (hhf : IsFlat D.site D.base D.base_mem h)
    (hhr : HasRelativeDimension m D.site D.base D.base_mem h) (j : Fin (n + 1 + 1)) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY₁ k) :
    chernCapFamily D sX hX E n hr (h ≫ g) hY₂ j (k + m)
        (flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h (Category.assoc h g sX).symm m hhf
          hhr k (k + m) rfl α) =
      flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h (Category.assoc h g sX).symm m hhf hhr
        (k - ((j : ℕ) : ℤ)) (k + m - ((j : ℕ) : ℤ)) (chernDegree_sub_add k m _)
        (chernCapFamily D sX hX E n hr g hY₁ j k α) := by
  have hP₁ := isGood_projectiveBundleBaseChangeProj_comp D sX hX E hr.isFiniteLocallyFreeOnSite g
    hY₁
  have hP₂ := isGood_projectiveBundleBaseChangeProj_comp D sX hX E hr.isFiniteLocallyFreeOnSite
    (h ≫ g) hY₂
  have sq := isPullback_chernBaseChangeMap D sX hX E n hr g h
  have hPfr := (isFlat_and_hasRelativeDimension_of_isPullback D _ hP₂ _ hP₁ _ hY₂ _ hY₁
    (chernBaseChangeMap_base D sX hX E n hr g h) (Category.assoc h g sX).symm sq.flip m hhf
    hhr).2
  have hrel := flatPullback_bundleRelationSumAt D (g ≫ sX) hY₁ ((h ≫ g) ≫ sX) hY₂ _ hP₁ _
    hP₂ (pullback.snd π₀ g) rfl (pullback.snd π₀ (h ≫ g)) rfl n
    (isFlat_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite g hY₁ n hr)
    (hasRelativeDimension_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite g
      hY₁ n hr)
    (isFlat_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite (h ≫ g) hY₂ n
      hr)
    (hasRelativeDimension_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite
      (h ≫ g) hY₂ n hr)
    _ (isInvertibleModule_projectiveBundleBaseChangeTwist D sX hX E hr.isFiniteLocallyFreeOnSite g
      hY₁)
    _ (isInvertibleModule_projectiveBundleBaseChangeTwist D sX hX E hr.isFiniteLocallyFreeOnSite
      (h ≫ g) hY₂)
    h (Category.assoc h g sX).symm m hhf hhr (chernBaseChangeMap D sX hX E n hr g h)
    (chernBaseChangeMap_base D sX hX E n hr g h) hPfr.1 hPfr.2
    (chernBaseChangeMap_snd D sX hX E n hr g h)
    (chernBaseChangeTwistIso D sX hX E n hr g hY₁ h hY₂) _ (chernRank_sub_one n) (n + 1) k
    (fun j => chernCapFamily D sX hX E n hr g hY₁ j k α)
  have h0 : chernCapFamily D sX hX E n hr (h ≫ g) hY₂ 0 (k + m)
        (flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h (Category.assoc h g sX).symm m hhf
          hhr k (k + m) rfl α) =
      flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h (Category.assoc h g sX).symm m hhf hhr
        (k - (((0 : Fin (n + 1 + 1)) : ℕ) : ℤ)) (k + m - (((0 : Fin (n + 1 + 1)) : ℕ) : ℤ))
        (by ring) (chernCapFamily D sX hX E n hr g hY₁ 0 k α) := by
    rw [chernCapFamily_zero, chernCapFamily_zero,
      flatPullbackChowMapCanonical_degreeCast D _ hY₂ _ hY₁ h _ m hhf hhr (by simp) (by simp) rfl]
  exact chernCapFamily_apply_eq_of_map_chernRelationSumAt D sX hX E n hr (h ≫ g) hY₂ g hY₁
    (k + m) k _ _ α _ h0 hrel j

/-- **Stacks 0ERY, the Gysin map**: `c_j(ℰ) ∩ i^*α = i^*(c_j(ℰ) ∩ α)` for the Gysin map of a
section `t` of an invertible `ℳ` on a test space `Y`, `i : D' = Z(t) → Y`. -/
theorem chernCapFamily_gysin {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1) (t : M.sections)
    (hM : IsInvertibleSheaf D (g ≫ sX) hY M) (j : Fin (n + 1 + 1)) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k + 1)) :
    chernCapFamily D sX hX E n hr ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g)
        (isGood_vanishingLocus D (g ≫ sX) hY M t) j k
        (sectionGysinChowGroupMap D (g ≫ sX) hY M t hM k α) =
      sectionGysinChowGroupMap D (g ≫ sX) hY M t hM (k - ((j : ℕ) : ℤ))
        (ProjectiveBundleRelation.degreeCast
          (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) (chernDegree_add_one_sub k _)
          (chernCapFamily D sX hX E n hr g hY j (k + 1) α)) := by
  -- the vanishing locus `i : D' → Y`, the test space `i ≫ g`, and the base change of `π` to them
  have hYι : D.IsGood (((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g) ≫ sX) :=
    isGood_vanishingLocus D (g ≫ sX) hY M t
  have hP := isGood_projectiveBundleBaseChangeProj_comp D sX hX E hr.isFiniteLocallyFreeOnSite g hY
  have hPι := isGood_projectiveBundleBaseChangeProj_comp D sX hX E hr.isFiniteLocallyFreeOnSite
    ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g) hYι
  -- `Z = Z(π'^*t) ⊆ P'` and the cartesian square of Stacks 0ER3
  obtain ⟨g₀, hsq⟩ := exists_isPullback_vanishingLocus_pullbackSheaf D (g ≫ sX) hY _ hP
    (ObjectProperty.homMk (pullback.snd π₀ g)) M t hM
  have hrel := gysin_bundleRelationSumAt D (g ≫ sX) hY _ hP (pullback.snd π₀ g) rfl n
    (isFlat_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite g hY n hr)
    (hasRelativeDimension_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite g
      hY n hr)
    _ (isInvertibleModule_projectiveBundleBaseChangeTwist D sX hX E hr.isFiniteLocallyFreeOnSite g
      hY) M t hM hsq _ (chernRank_sub_one n) (n + 1) k
    (fun j => chernCapFamily D sX hX E n hr g hY j (k + 1) α)
  -- the identification `P ×_X D' ≅ Z` over `D'`
  have sqι := isPullback_chernBaseChangeMap D sX hX E n hr g (vanishingLocus D (g ≫ sX) hY M t).1.ι
  let φ := (sqι.isoIsPullback _ _ hsq).hom
  have hφπ : φ ≫ g₀ = pullback.snd π₀ ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g) :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hφι : φ ≫ (vanishingLocus D _ hP (pullbackSheaf D (g ≫ sX) hY _ hP
      (ObjectProperty.homMk (pullback.snd π₀ g)) M)
      (pullbackGlobalSection D (g ≫ sX) hY _ hP (ObjectProperty.homMk (pullback.snd π₀ g)) M
        t)).1.ι = chernBaseChangeMap D sX hX E n hr g (vanishingLocus D (g ≫ sX) hY M t).1.ι :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  have hφB : φ ≫ ((vanishingLocus D _ hP (pullbackSheaf D (g ≫ sX) hY _ hP
      (ObjectProperty.homMk (pullback.snd π₀ g)) M)
      (pullbackGlobalSection D (g ≫ sX) hY _ hP (ObjectProperty.homMk (pullback.snd π₀ g)) M
        t)).1.ι ≫ pullback.snd π₀ g ≫ g ≫ sX) =
      pullback.snd π₀ ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g) ≫
        ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g) ≫ sX := by
    rw [← Category.assoc, hφι, chernBaseChangeMap_base]
  have hZ := isGood_vanishingLocus D _ hP (pullbackSheaf D (g ≫ sX) hY _ hP
      (ObjectProperty.homMk (pullback.snd π₀ g)) M)
      (pullbackGlobalSection D (g ≫ sX) hY _ hP (ObjectProperty.homMk (pullback.snd π₀ g)) M t)
  have eL := (modulePullbackCompIsoOfEq D.site D.base D.base_mem
      (ObjectProperty.homMk φ : (⟨pullback π₀ ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g), hPι.1⟩ :
        AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨_, hZ.1⟩)
      (vanishingLocusInclusion D _ hP (pullbackSheaf D (g ≫ sX) hY _ hP
        (ObjectProperty.homMk (pullback.snd π₀ g)) M)
        (pullbackGlobalSection D (g ≫ sX) hY _ hP (ObjectProperty.homMk (pullback.snd π₀ g)) M t))
      (h := ObjectProperty.homMk
        (chernBaseChangeMap D sX hX E n hr g (vanishingLocus D (g ≫ sX) hY M t).1.ι))
      (ObjectProperty.hom_ext _ hφι)).app
      (projectiveBundleBaseChangeTwist D sX hX E hr.isFiniteLocallyFreeOnSite g hY) ≪≫
    chernBaseChangeTwistIso D sX hX E n hr g hY (vanishingLocus D (g ≫ sX) hY M t).1.ι hYι
  have hgfr := isFlat_and_hasRelativeDimension_gysinPullbackProjection D (g ≫ sX) hY _ hP rfl n
    (isFlat_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite g hY n hr)
    (hasRelativeDimension_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite g
      hY n hr) M t hsq
  have hiso := bundleRelationSumAt_of_isIso D ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g ≫ sX)
    (isGood_vanishingLocus D (g ≫ sX) hY M t)
    _ hZ _ hPι g₀ (comp_structure_of_isPullback D (g ≫ sX) _ rfl hsq)
    (pullback.snd π₀ ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g))
    (by simp only [Category.assoc]) n hgfr.1 hgfr.2
    (isFlat_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite
      ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g) hYι n
      hr)
    (hasRelativeDimension_projectiveBundleBaseChangeProj D sX hX E hr.isFiniteLocallyFreeOnSite
      ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g) hYι n hr)
    _ (modulePullbackInvertible _ _ (isInvertibleModule_projectiveBundleBaseChangeTwist D sX hX E
      hr.isFiniteLocallyFreeOnSite g hY))
    _ (isInvertibleModule_projectiveBundleBaseChangeTwist D sX hX E hr.isFiniteLocallyFreeOnSite
      ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g) hYι) φ hφB hφπ eL _ (chernRank_sub_one n)
    (n + 1) k
    (fun j => sectionGysinChowGroupMap D (g ≫ sX) hY M t hM (k - ((j : ℕ) : ℤ))
      (ProjectiveBundleRelation.degreeCast
        (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) (by ring)
        (chernCapFamily D sX hX E n hr g hY j (k + 1) α)))
  have hzero : chernRelationSumAt D sX hX E n hr ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g) hYι k
      (fun j => sectionGysinChowGroupMap D (g ≫ sX) hY M t hM (k - ((j : ℕ) : ℤ))
        (ProjectiveBundleRelation.degreeCast
          (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) (by ring)
          (chernCapFamily D sX hX E n hr g hY j (k + 1) α))) = 0 := by
    refine hiso.trans ((congrArg (flatPullbackChowMapCanonical.{u + 1} D _ hPι _ hZ φ hφB 0
      (isFlat_and_hasRelativeDimension_zero_of_isIso D _ hZ φ).1
      (isFlat_and_hasRelativeDimension_zero_of_isIso D _ hZ φ).2 _ _ (by simp))
      hrel.symm).trans ?_)
    have h1 := chernRelationSumAt_chernCapFamily D sX hX E n hr g hY (k + 1) α
    refine (congrArg (fun z => flatPullbackChowMapCanonical.{u + 1} D _ hPι _ hZ φ hφB 0
      (isFlat_and_hasRelativeDimension_zero_of_isIso D _ hZ φ).1
      (isFlat_and_hasRelativeDimension_zero_of_isIso D _ hZ φ).2 _ _ (by simp)
      (sectionGysinChowGroupMap D _ hP _ _
        (isInvertibleSheaf_pullbackSheaf D (g ≫ sX) hY _ hP
          (ObjectProperty.homMk (pullback.snd π₀ g)) M hM) _
        (ProjectiveBundleRelation.degreeCast
          (fun m => chowGroupCanonical.{u + 1} D _ hP m) (by ring) z))) h1).trans ?_
    beta_reduce
    refine (congrArg _ ((congrArg _ (AddMonoidHom.map_zero _)).trans
      (AddMonoidHom.map_zero _))).trans (AddMonoidHom.map_zero _)
  have h0 : chernCapFamily D sX hX E n hr ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g) hYι 0 k
        (sectionGysinChowGroupMap D (g ≫ sX) hY M t hM k α) =
      sectionGysinChowGroupMap D (g ≫ sX) hY M t hM (k - (((0 : Fin (n + 1 + 1)) : ℕ) : ℤ))
        (ProjectiveBundleRelation.degreeCast
          (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) (by ring)
          (chernCapFamily D sX hX E n hr g hY 0 (k + 1) α)) := by
    rw [chernCapFamily_zero, chernCapFamily_zero, ProjectiveBundleRelation.degreeCast_degreeCast,
      sectionGysinChowGroupMap_degreeCast D (g ≫ sX) hY M t hM (by simp)]
    rfl
  exact chernCapFamily_apply_eq_of_chernRelationSumAt_eq_zero D sX hX E n hr
    ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g) hYι k _ _ h0 hzero j

end Naturality

/-! ### Bivariant classes for the identity from cap maps on the test spaces -/

section Bivariant

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

include sX hX in
/-- The identity of `X` is flat of relative dimension `0`. -/
theorem isFlat_and_hasRelativeDimension_zero_id :
    IsFlat D.site D.base D.base_mem (𝟙 X) ∧ HasRelativeDimension 0 D.site D.base D.base_mem (𝟙 X) :=
  isFlat_and_hasRelativeDimension_zero_of_isIso D sX hX (𝟙 X)

include hX in
/-- The identification `X ×_X Y ⟶ Y` of a test space `g : Y ⟶ X` with its base change along
`𝟙 X` is flat of relative dimension `0`. -/
theorem isFlat_and_hasRelativeDimension_pullbackSnd_id {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (hXg : D.IsGood (pullback.fst (𝟙 X) g ≫ sX)) :
    IsFlat D.site D.base D.base_mem (pullback.snd (𝟙 X) g) ∧
      HasRelativeDimension 0 D.site D.base D.base_mem (pullback.snd (𝟙 X) g) :=
  isFlat_and_hasRelativeDimension_bivariantPullbackSnd D sX hX sX hX (Category.id_comp sX) 0
    (isFlat_and_hasRelativeDimension_zero_id D sX hX).1
    (isFlat_and_hasRelativeDimension_zero_id D sX hX).2 g hY hXg

/-- The flat pullback `CH_m(Y) ⟶ CH_m(X ×_X Y)` along the identification `X ×_X Y ≅ Y`. -/
abbrev testSpacePullbackChowMap {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (hXg : D.IsGood (pullback.fst (𝟙 X) g ≫ sX)) (m : ℤ) :
    chowGroupCanonical.{u + 1} D (g ≫ sX) hY m →+
      chowGroupCanonical.{u + 1} D (pullback.fst (𝟙 X) g ≫ sX) hXg m :=
  flatPullbackChowMapCanonical.{u + 1} D (pullback.fst (𝟙 X) g ≫ sX) hXg (g ≫ sX) hY
    (pullback.snd (𝟙 X) g) (bivariantPullbackSnd_comp_base D sX sX (Category.id_comp sX) g) 0
    (isFlat_and_hasRelativeDimension_pullbackSnd_id D sX hX g hY hXg).1
    (isFlat_and_hasRelativeDimension_pullbackSnd_id D sX hX g hY hXg).2 m m (by simp)

variable (p : ℤ)
    (c : ∀ {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (k : ℤ),
      chowGroupCanonical.{u + 1} D (g ≫ sX) hY k →+
        chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k - p))
    (hproper : ∀ {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X) (hY₁ : D.IsGood (g ≫ sX)) (h : Y₂ ⟶ Y₁)
      (hY₂ : D.IsGood ((h ≫ g) ≫ sX)) (hh : IsProper D.site D.base D.base_mem h) (k : ℤ)
      (α : chowGroupCanonical.{u + 1} D ((h ≫ g) ≫ sX) hY₂ k),
      c g hY₁ k (chowGroupCanonicalProperPushforward.{u + 1} D _ hY₂ _ hY₁
          (Category.assoc h g sX).symm hh k α) =
        chowGroupCanonicalProperPushforward.{u + 1} D _ hY₂ _ hY₁ (Category.assoc h g sX).symm hh _
          (c (h ≫ g) hY₂ k α))
    (hflat : ∀ {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X) (hY₁ : D.IsGood (g ≫ sX)) (h : Y₂ ⟶ Y₁)
      (hY₂ : D.IsGood ((h ≫ g) ≫ sX)) (m : ℕ) (hhf : IsFlat D.site D.base D.base_mem h)
      (hhr : HasRelativeDimension m D.site D.base D.base_mem h) (k : ℤ)
      (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY₁ k),
      c (h ≫ g) hY₂ (k + m) (flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h
          (Category.assoc h g sX).symm m hhf hhr k (k + m) rfl α) =
        flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h (Category.assoc h g sX).symm m hhf hhr
          (k - p) (k + m - p) (chernDegree_sub_add k m p) (c g hY₁ k α))
    (hgysin : ∀ {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
      (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1) (t : M.sections)
      (hM : IsInvertibleSheaf D (g ≫ sX) hY M) (k : ℤ)
      (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k + 1)),
      c ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g) (isGood_vanishingLocus D (g ≫ sX) hY M t) k
          (sectionGysinChowGroupMap D (g ≫ sX) hY M t hM k α) =
        sectionGysinChowGroupMap D (g ≫ sX) hY M t hM (k - p)
          (ProjectiveBundleRelation.degreeCast
            (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) (chernDegree_add_one_sub k p)
            (c g hY (k + 1) α)))

include hproper hflat hgysin in
/-- **A bivariant class for the identity of `X`** from additive maps
`c ∩ - : CH_k(Y) ⟶ CH_{k-p}(Y)` on every good test space `g : Y ⟶ X` which commute with proper
pushforward, flat pullback and the Gysin maps of sections of invertible sheaves: the cap
operation on `Y` is `c ∩ -` followed by the flat pullback along the identification
`X ×_X Y ≅ Y`. -/
def bivariantClassOfTestCaps : chowCohomologyComponentCanonical.{u + 1} D sX hX p where
  cap g hY hXg k := (testSpacePullbackChowMap D sX hX g hY hXg (k - p)).comp (c g hY k)
  proper_naturality := by
    intro Y' Y'' g hY' hX' h hY'' hX'' hh h' sq hfst hh' k α
    obtain ⟨γ, hγ⟩ : ∃ γ, chowClassCanonical.{u + 1} D _ hY'' (k - p) γ =
        c (h ≫ g) hY'' k (chowClassCanonical.{u + 1} D _ hY'' k α) :=
      QuotientAddGroup.mk'_surjective _ _
    refine ⟨flatPullbackMap D _ hX'' _ hY'' (pullback.snd (𝟙 X) (h ≫ g))
      (bivariantPullbackSnd_comp_base D sX sX (Category.id_comp sX) (h ≫ g)) 0
      (isFlat_and_hasRelativeDimension_pullbackSnd_id D sX hX (h ≫ g) hY'' hX'').1
      (isFlat_and_hasRelativeDimension_pullbackSnd_id D sX hX (h ≫ g) hY'' hX'').2 (k - p) (k - p)
      (by simp) γ, ?_, ?_⟩
    · rw [AddMonoidHom.comp_apply, ← hγ]
      rfl
    · rw [AddMonoidHom.comp_apply, ← chowGroupCanonicalProperPushforward_chowClassCanonical D _
        hY'' _ hY' (Category.assoc h g sX).symm hh, hproper g hY' h hY'' hh k, ← hγ,
        chowGroupCanonicalProperPushforward_chowClassCanonical]
      exact congrArg (chowClassCanonical.{u + 1} D (pullback.fst (𝟙 X) g ≫ sX) hX' (k - p))
        (flatPullback_properPushforward_unconditional D _ hX'' _ hY'' _ hX' _ hY'
          (bivariantPullbackSnd_comp_base D sX sX (Category.id_comp sX) (h ≫ g))
          (by rw [← Category.assoc, hfst]) (Category.assoc h g sX).symm
          (bivariantPullbackSnd_comp_base D sX sX (Category.id_comp sX) g) 0
          (isFlat_and_hasRelativeDimension_pullbackSnd_id D sX hX g hY' hX').1
          (isFlat_and_hasRelativeDimension_pullbackSnd_id D sX hX g hY' hX').2 sq hh (k - p)
          (k - p) (by simp) γ)
  flat_naturality := by
    intro Y' Y'' g hY' hX' h hY'' hX'' hh m hm h' sq hfst hh' hm' k α
    obtain ⟨γ, hγ⟩ : ∃ γ, chowClassCanonical.{u + 1} D _ hY' (k - p) γ =
        c g hY' k (chowClassCanonical.{u + 1} D _ hY' k α) :=
      QuotientAddGroup.mk'_surjective _ _
    refine ⟨flatPullbackMap D _ hX' _ hY' (pullback.snd (𝟙 X) g)
      (bivariantPullbackSnd_comp_base D sX sX (Category.id_comp sX) g) 0
      (isFlat_and_hasRelativeDimension_pullbackSnd_id D sX hX g hY' hX').1
      (isFlat_and_hasRelativeDimension_pullbackSnd_id D sX hX g hY' hX').2 (k - p) (k - p)
      (by simp) γ, ?_, ?_⟩
    · rw [AddMonoidHom.comp_apply, ← hγ]
      rfl
    · rw [AddMonoidHom.comp_apply, ← flatPullbackChowMapCanonical_chowClassCanonical.{u + 1} D _
        hY'' _ hY' h (Category.assoc h g sX).symm m hh hm k (k + m) rfl,
        hflat g hY' h hY'' m hh hm k, ← hγ, flatPullbackChowMapCanonical_chowClassCanonical,
        flatPullbackChowMapCanonical_chowClassCanonical]
      exact congrArg (chowClassCanonical.{u + 1} D _ hX'' (k + m - p))
        (flatPullbackMap_flatPullbackMap_of_comm D (g ≫ sX) hY' ((h ≫ g) ≫ sX) hY'' _ hX' _ hX''
          (pullback.snd (𝟙 X) g) (bivariantPullbackSnd_comp_base D sX sX (Category.id_comp sX) g)
          (pullback.snd (𝟙 X) (h ≫ g))
          (bivariantPullbackSnd_comp_base D sX sX (Category.id_comp sX) (h ≫ g)) 0
          (isFlat_and_hasRelativeDimension_pullbackSnd_id D sX hX g hY' hX').1
          (isFlat_and_hasRelativeDimension_pullbackSnd_id D sX hX g hY' hX').2
          (isFlat_and_hasRelativeDimension_pullbackSnd_id D sX hX (h ≫ g) hY'' hX'').1
          (isFlat_and_hasRelativeDimension_pullbackSnd_id D sX hX (h ≫ g) hY'' hX'').2
          h (Category.assoc h g sX).symm m hh hm h' (by rw [← Category.assoc, hfst]) hh' hm'
          sq.w.symm (k - p) (k + m - p) (k - p) (k + m - p) (by ring) (by ring) (by simp)
          (by simp) γ).symm
  gysin_naturality := by
    intro Y' g hY' hX' L t hL hXd iso hiso hbase hisoProper k α
    have hcongr : ∀ {a b : ℤ} (h : a = b) (x : CycleGroup D (pullback.fst (𝟙 X) g ≫ sX) a),
        (cycleGroupDegreeCongr D _ h x).1 = x.1 := by
      intro a b h x
      subst h
      rfl
    obtain ⟨δ, hδ⟩ : ∃ δ, chowClassCanonical.{u + 1} D _ hY' (k + 1 - p) δ =
        c g hY' (k + 1) (chowClassCanonical.{u + 1} D _ hY' (k + 1) α) :=
      QuotientAddGroup.mk'_surjective _ _
    have hkp : k + 1 - p = k - p + 1 := by ring
    have hf' := isFlat_and_hasRelativeDimension_pullbackSnd_id D sX hX g hY' hX'
    have hf'' := isFlat_and_hasRelativeDimension_pullbackSnd_id D sX hX
      ((vanishingLocus D (g ≫ sX) hY' L t).1.ι ≫ g) (isGood_vanishingLocus D (g ≫ sX) hY' L t) hXd
    refine ⟨flatPullbackMap D _ hX' _ hY' (pullback.snd (𝟙 X) g)
      (bivariantPullbackSnd_comp_base D sX sX (Category.id_comp sX) g) 0 hf'.1 hf'.2 (k - p + 1)
      (k - p + 1) (by simp) (cycleGroupCast D _ hkp δ),
      flatPullbackMap D _ hXd _ (isGood_vanishingLocus D (g ≫ sX) hY' L t)
        (pullback.snd (𝟙 X) ((vanishingLocus D (g ≫ sX) hY' L t).1.ι ≫ g))
        (bivariantPullbackSnd_comp_base D sX sX (Category.id_comp sX) _) 0 hf''.1 hf''.2 (k - p)
        (k - p) (by simp)
        (gysinCycleMap D (g ≫ sX) (vanishingLocus D (g ≫ sX) hY' L t)
          (isGood_vanishingLocus D (g ≫ sX) hY' L t) (k - p)
          (sectionGysinRule D (g ≫ sX) hY' L t (k - p) hL) (cycleGroupCast D _ hkp δ)), ?_, ?_, ?_⟩
    · rw [AddMonoidHom.comp_apply, ← hδ]
      change chowClassCanonical.{u + 1} D _ hX' _ _ = _
      congr 1
      refine Subtype.ext ?_
      rw [hcongr]
      exact coe_flatPullbackMap_congr D (g ≫ sX) hY' (pullback.fst (𝟙 X) g ≫ sX) hX'
        (pullback.snd (𝟙 X) g) _ 0 hf'.1 hf'.2 hkp hkp _ _ _ _ rfl
    · rw [AddMonoidHom.comp_apply, ← sectionGysinChowGroupMap_chowClassCanonical,
        hgysin g hY' L t hL k, ← hδ, degreeCast_chowClassCanonical]
      rfl
    · obtain ⟨g₀, hsq⟩ := exists_isPullback_vanishingLocus_pullbackSheaf D (g ≫ sX) hY'
        (pullback.fst (𝟙 X) g ≫ sX) hX' (ObjectProperty.homMk (pullback.snd (𝟙 X) g)) L t hL
      have hg₀ := isFlat_and_hasRelativeDimension_gysinPullbackProjection D (g ≫ sX) hY'
        (pullback.fst (𝟙 X) g ≫ sX) hX'
        (bivariantPullbackSnd_comp_base D sX sX (Category.id_comp sX) g) 0 hf'.1 hf'.2 L t hsq
      have hab : iso.hom ≫ g₀ =
          pullback.snd (𝟙 X) ((vanishingLocus D (g ≫ sX) hY' L t).1.ι ≫ g) := by
        rw [← cancel_mono (vanishingLocus D (g ≫ sX) hY' L t).1.ι, Category.assoc, hsq.w,
          ← Category.assoc, hiso]
        simp
      have h6 := chowClassCanonical_gysinCycleMap_flatPullbackMap_of_isPullback D (g ≫ sX) hY'
        (pullback.fst (𝟙 X) g ≫ sX) hX'
        (bivariantPullbackSnd_comp_base D sX sX (Category.id_comp sX) g) 0 hf'.1 hf'.2 L t hL
        hsq (k - p) (k - p) (by simp) (by simp) (cycleGroupCast D _ hkp δ)
      have h7 := properCyclePushforward_flatPullbackMap_of_isIso D
        (pullback.fst (𝟙 X) ((vanishingLocus D (g ≫ sX) hY' L t).1.ι ≫ g) ≫ sX) hXd
        _ (isGood_vanishingLocus D (pullback.fst (𝟙 X) g ≫ sX) hX' _ _)
        _ (isGood_vanishingLocus D (g ≫ sX) hY' L t) hab
        (bivariantPullbackSnd_comp_base D sX sX (Category.id_comp sX) _)
        (comp_structure_of_isPullback D (g ≫ sX) (pullback.fst (𝟙 X) g ≫ sX)
          (bivariantPullbackSnd_comp_base D sX sX (Category.id_comp sX) g) hsq) hbase
        hisoProper.2.1.2 0 hf''.1 hf''.2 hg₀.1 hg₀.2 (k - p) (k - p) (by simp)
        (gysinCycleMap D (g ≫ sX) (vanishingLocus D (g ≫ sX) hY' L t)
          (isGood_vanishingLocus D (g ≫ sX) hY' L t) (k - p)
          (sectionGysinRule D (g ≫ sX) hY' L t (k - p) hL) (cycleGroupCast D _ hkp δ))
      exact (congrArg _ h7).trans h6.symm

end Bivariant

/-! ### The Chern classes, in every rank -/

section Chern

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (E : Modules.{u, u} D.site D.base D.base_mem X hX.1) (r : ℕ)
    (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E r)

/-- The projection `π : P = 𝐏(ℰ) → X` of the projective space bundle of `ℰ`. -/
abbrev chernProj :
    (@projectiveBundle D.site D.base D.base_mem ⟨X, hX.1⟩ E
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE)
      hE.isFiniteLocallyFreeOnSite).1 ⟶ X :=
  @chernBundleProj D X sX hX E (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE)
    hE.isFiniteLocallyFreeOnSite

/-- The base change `P' = P ×_X X'` of the projective space bundle to a good test space
`g : X' → X` is good over the base, with structure morphism `π' ≫ g ≫ s_X`. -/
theorem isGood_chernTestBundle {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) :
    D.IsGood (pullback.snd (chernProj D sX hX E r hE) g ≫ g ≫ sX) :=
  @isGood_projectiveBundleBaseChangeProj_comp D X Y sX hX E
    (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE) hE.isFiniteLocallyFreeOnSite g hY

/-- `𝒪_{P'}(1) = (g')^*𝒪_P(1)` on `P' = P ×_X X'`, `g' : P' → P` the projection. -/
abbrev chernTestTwist {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) :
    Modules.{u, u} D.site D.base D.base_mem (pullback (chernProj D sX hX E r hE) g)
      (isGood_chernTestBundle D sX hX E r hE g hY).1 :=
  @projectiveBundleBaseChangeTwist D X Y sX hX E
    (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE) hE.isFiniteLocallyFreeOnSite g hY

/-- The module `𝒪_{P'}(1)` on `P' = P ×_X X'` is invertible. -/
theorem isInvertibleModule_chernTestTwist {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) :
    IsInvertibleModule (⟨pullback (chernProj D sX hX E r hE) g,
      (isGood_chernTestBundle D sX hX E r hE g hY).1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      (chernTestTwist D sX hX E r hE g hY) :=
  @isInvertibleModule_projectiveBundleBaseChangeTwist D X Y sX hX E
    (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE) hE.isFiniteLocallyFreeOnSite g hY

/-- **In rank `0` the base change `P' = P ×_X X'` has no points**, so its Chow groups vanish. -/
theorem subsingleton_chowGroupCanonical_chernTestBundle_of_rank_zero
    (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E 0)
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (N : ℤ) :
    Subsingleton (chowGroupCanonical.{u + 1} D (pullback.snd (chernProj D sX hX E 0 hE) g ≫ g ≫ sX)
      (isGood_chernTestBundle D sX hX E 0 hE g hY) N) := by
  have := isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE
  refine subsingleton_chowGroupCanonical_of_isEmpty_points D _ _ ⟨fun x => ?_⟩ N
  exact (isEmpty_points_projectiveBundle_of_rank_zero (Y := ⟨X, hX.1⟩) E hE).false
    (pointsMap D.site D.base D.base_mem _ (pullback.fst (chernProj D sX hX E 0 hE) g) x)

/-- **The pullback `π'^* : CH_m(X') → CH_N(P')`, `m + (r - 1) = N`, in the relation of
Stacks 0ERY**: for `r = n + 1` the flat pullback along the base change `π' : P' → X'` of `π`,
flat of relative dimension `r - 1 = n`. In rank `0` the space `P'` has no points and
`CH_N(P') = 0`
(`AlgebraicGeometry.Space.subsingleton_chowGroupCanonical_chernTestBundle_of_rank_zero`), and it is
the zero map. -/
def chernTestPull : (r : ℕ) → (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E r) →
    ∀ {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (m N : ℤ), m + ((r : ℤ) - 1) = N →
      chowGroupCanonical.{u + 1} D (g ≫ sX) hY m →+
        chowGroupCanonical.{u + 1} D (pullback.snd (chernProj D sX hX E r hE) g ≫ g ≫ sX)
          (isGood_chernTestBundle D sX hX E r hE g hY) N
  | 0, _, _, _, _, _, _, _ => 0
  | n + 1, hE, _, g, hY, m, N, h =>
    bundleRelationPull D (g ≫ sX) hY _ (isGood_chernTestBundle D sX hX E (n + 1) hE g hY)
      (pullback.snd (chernProj D sX hX E (n + 1) hE) g) rfl n
      (@isFlat_projectiveBundleBaseChangeProj D X _ sX hX E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE) hE.isFiniteLocallyFreeOnSite g
        hY n hE)
      (@hasRelativeDimension_projectiveBundleBaseChangeProj D X _ sX hX E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE) hE.isFiniteLocallyFreeOnSite g
        hY n hE) _ (chernRank_sub_one n) m N h

/-- **The left-hand side of the relation of Stacks 0ERY** for a family of maps
`c_j : CH_k(X') → CH_{k-j}(X')`, `j = 0, …, r`, on a test space `g : X' → X`, at `α ∈ CH_k(X')`:
`∑_{i=0}^{r} (-1)^i c₁(𝒪_{P'}(1))^i ∩ π'^*(c_{r-i}(α)) ∈ CH_{k-r+(r-1)}(P')`, where
`P' = P ×_X X'`, `π' : P' → X'` is the base change of `π`, and `𝒪_{P'}(1)` is the pullback of
`𝒪_P(1)` (`AlgebraicGeometry.Space.chernTestPull`, `AlgebraicGeometry.Space.bundleFormulaCap`). -/
abbrev chernRelationSum {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (c : ∀ (j : Fin (r + 1)) (k : ℤ), chowGroupCanonical.{u + 1} D (g ≫ sX) hY k →+
      chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k - ((j : ℕ) : ℤ))) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    chowGroupCanonical.{u + 1} D (pullback.snd (chernProj D sX hX E r hE) g ≫ g ≫ sX)
      (isGood_chernTestBundle D sX hX E r hE g hY) (k - r + ((r : ℤ) - 1)) :=
  ProjectiveBundleRelation.relationSum (A := fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m)
    (P := fun m => chowGroupCanonical.{u + 1} D (pullback.snd (chernProj D sX hX E r hE) g ≫ g ≫ sX)
      (isGood_chernTestBundle D sX hX E r hE g hY) m) ((r : ℤ) - 1)
    (chernTestPull D sX hX E r hE g hY)
    (bundleFormulaCap D _ (isGood_chernTestBundle D sX hX E r hE g hY)
      (chernTestTwist D sX hX E r hE g hY) (isInvertibleModule_chernTestTwist D sX hX E r hE g hY))
    r c k α

/-- **The maps `c_j(ℰ) ∩ - : CH_k(X') → CH_{k-j}(X')`**, `j = 0, …, r`, on a good test space
`g : X' → X`, characterized by Stacks 0ERY. -/
def chernCap : (r : ℕ) → (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E r) →
    ∀ {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (j : Fin (r + 1)) (k : ℤ),
      chowGroupCanonical.{u + 1} D (g ≫ sX) hY k →+
        chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k - ((j : ℕ) : ℤ))
  | 0, _, _, g, hY, j, k =>
    ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m)
      (by simp)
  | n + 1, hE, _, g, hY, j, k =>
    @chernCapFamily D X sX hX E (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE) n hE
      _ g hY j k

/-- The map `c₀(ℰ) ∩ -` is the identity, up to the degree identification `k - 0 = k`. -/
theorem chernCap_zero {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    chernCap D sX hX E r hE g hY 0 k α = ProjectiveBundleRelation.degreeCast
      (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) (by simp) α := by
  cases r with
  | zero => rfl
  | succ n =>
    have := isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE
    exact chernCapFamily_zero D sX hX E n hE g hY k α

/-- The classes `c_j(ℰ) ∩ α` satisfy the projective bundle relation on `P' = P ×_X X'`. -/
theorem chernRelationSum_chernCap {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    chernRelationSum D sX hX E r hE g hY (chernCap D sX hX E r hE g hY) k α = 0 := by
  cases r with
  | zero =>
    simp [chernRelationSum, ProjectiveBundleRelation.relationSum,
      ProjectiveBundleRelation.relationSumAt, ProjectiveBundleRelation.relationTerm, chernTestPull]
  | succ n =>
    have := isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE
    exact chernRelationSumAt_chernCapFamily D sX hX E n hE g hY k α

/-- A family of maps `c_j : CH_k(X') → CH_{k-j}(X')` with `c₀` the identity which satisfies the
projective bundle relation on `P' = P ×_X X'` is `chernCap`. -/
theorem chernCap_unique {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (c : ∀ (j : Fin (r + 1)) (k : ℤ), chowGroupCanonical.{u + 1} D (g ≫ sX) hY k →+
      chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k - ((j : ℕ) : ℤ)))
    (h0 : ∀ k α, c 0 k α = ProjectiveBundleRelation.degreeCast
      (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) (by simp) α)
    (hc : ∀ k α, chernRelationSum D sX hX E r hE g hY c k α = 0) :
    c = chernCap D sX hX E r hE g hY := by
  cases r with
  | zero =>
    funext j k
    obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) _ _
    exact AddMonoidHom.ext fun α => h0 k α
  | succ n =>
    have := isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE
    exact chernCapFamily_unique D sX hX E n hE g hY c h0 hc

/-- The maps `c_j(ℰ) ∩ -` commute with proper pushforward along a proper morphism
`h : Y₂ → Y₁` of test spaces. -/
theorem chernCap_properPushforward (j : Fin (r + 1)) {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X)
    (hY₁ : D.IsGood (g ≫ sX)) (h : Y₂ ⟶ Y₁) (hY₂ : D.IsGood ((h ≫ g) ≫ sX))
    (hh : IsProper D.site D.base D.base_mem h) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D ((h ≫ g) ≫ sX) hY₂ k) :
    chernCap D sX hX E r hE g hY₁ j k
        (chowGroupCanonicalProperPushforward.{u + 1} D _ hY₂ _ hY₁ (Category.assoc h g sX).symm hh
          k α) =
      chowGroupCanonicalProperPushforward.{u + 1} D _ hY₂ _ hY₁ (Category.assoc h g sX).symm hh _
        (chernCap D sX hX E r hE (h ≫ g) hY₂ j k α) := by
  cases r with
  | zero => exact (chowGroupCanonicalProperPushforward_degreeCast D _ hY₂ _ hY₁ _ hh _ α).symm
  | succ n =>
    have := isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE
    exact chernCapFamily_properPushforward D sX hX E n hE g hY₁ h hY₂ hh j k α

/-- The maps `c_j(ℰ) ∩ -` commute with flat pullback along a flat morphism `h : Y₂ → Y₁` of
relative dimension `m` between test spaces. -/
theorem chernCap_flatPullback (j : Fin (r + 1)) {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X)
    (hY₁ : D.IsGood (g ≫ sX)) (h : Y₂ ⟶ Y₁) (hY₂ : D.IsGood ((h ≫ g) ≫ sX)) (m : ℕ)
    (hhf : IsFlat D.site D.base D.base_mem h)
    (hhr : HasRelativeDimension m D.site D.base D.base_mem h) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY₁ k) :
    chernCap D sX hX E r hE (h ≫ g) hY₂ j (k + m)
        (flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h (Category.assoc h g sX).symm m hhf
          hhr k (k + m) rfl α) =
      flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h (Category.assoc h g sX).symm m hhf hhr
        (k - ((j : ℕ) : ℤ)) (k + m - ((j : ℕ) : ℤ)) (chernDegree_sub_add k m _)
        (chernCap D sX hX E r hE g hY₁ j k α) := by
  cases r with
  | zero =>
    exact (flatPullbackChowMapCanonical_degreeCast D _ hY₂ _ hY₁ h _ m hhf hhr
      (by simp) (by simp) rfl _ α).symm
  | succ n =>
    have := isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE
    exact chernCapFamily_flatPullback D sX hX E n hE g hY₁ h hY₂ m hhf hhr j k α

/-- The maps `c_j(ℰ) ∩ -` commute with the Gysin map `i^*` of the vanishing locus `i : Z → Y`
of a section `t` of an invertible module on `Y`. -/
theorem chernCap_gysin (j : Fin (r + 1)) {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1) (t : M.sections)
    (hM : IsInvertibleSheaf D (g ≫ sX) hY M) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k + 1)) :
    chernCap D sX hX E r hE ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g)
        (isGood_vanishingLocus D (g ≫ sX) hY M t) j k
        (sectionGysinChowGroupMap D (g ≫ sX) hY M t hM k α) =
      sectionGysinChowGroupMap D (g ≫ sX) hY M t hM (k - ((j : ℕ) : ℤ))
        (ProjectiveBundleRelation.degreeCast
          (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) (chernDegree_add_one_sub k _)
          (chernCap D sX hX E r hE g hY j (k + 1) α)) := by
  cases r with
  | zero =>
    change ProjectiveBundleRelation.degreeCast _ _
        (sectionGysinChowGroupMap D (g ≫ sX) hY M t hM k α) =
      sectionGysinChowGroupMap D (g ≫ sX) hY M t hM (k - ((j : ℕ) : ℤ))
        (ProjectiveBundleRelation.degreeCast _ _ (ProjectiveBundleRelation.degreeCast _ _ α))
    rw [ProjectiveBundleRelation.degreeCast_degreeCast,
      sectionGysinChowGroupMap_degreeCast D (g ≫ sX) hY M t hM (by simp)]
  | succ n =>
    have := isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE
    exact chernCapFamily_gysin D sX hX E n hE g hY M t hM j k α

/-- **Stacks 0ERZ: the `j`-th Chern class `c_j(ℰ) ∈ A^j(X)`** of a finite locally free module `ℰ`
of rank `r` on a good algebraic space `X/B`, `j = 0, …, r`: the bivariant class of degree `j` of
Stacks 0ERY (`AlgebraicGeometry.Space.existsUnique_chernCap_and_bivariant`), in
`A^j(X) = A^j(X → X)` (`AlgebraicGeometry.Space.chowCohomologyComponentCanonical`). Its cap
operation on a test space `g : X' → X` is `c_j(ℰ) ∩ -` on `X'`
(`AlgebraicGeometry.Space.chernCap`), read on `X ×_X X' ≅ X'`
(`AlgebraicGeometry.Space.chernClass_cap`). -/
@[stacks 0ERZ "the i-th Chern class c_i(E) ∈ A^i(X), i = 0, ..., r, the bivariant class of degree \
i of Lemma 0ERY, for E finite locally free of rank r on a good X/B; A^i(X) = A^i(X → X) over the \
Chow groups chowGroupCanonical"]
def chernClass (j : Fin (r + 1)) :
    chowCohomologyComponentCanonical.{u + 1} D sX hX ((j : ℕ) : ℤ) :=
  bivariantClassOfTestCaps D sX hX ((j : ℕ) : ℤ)
    (fun g hY k => chernCap D sX hX E r hE g hY j k)
    (fun g hY₁ h hY₂ hh k α => chernCap_properPushforward D sX hX E r hE j g hY₁ h hY₂ hh k α)
    (fun g hY₁ h hY₂ m hhf hhr k α =>
      chernCap_flatPullback D sX hX E r hE j g hY₁ h hY₂ m hhf hhr k α)
    (fun g hY M t hM k α => chernCap_gysin D sX hX E r hE j g hY M t hM k α)

/-- The cap operation of `c_j(ℰ)` on a test space `g : X' → X` is `c_j(ℰ) ∩ -` on `X'`, read on
`X ×_X X' ≅ X'`. -/
theorem chernClass_cap (j : Fin (r + 1)) {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (hXg : D.IsGood (pullback.fst (𝟙 X) g ≫ sX)) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    (chernClass D sX hX E r hE j).cap g hY hXg k α =
      testSpacePullbackChowMap D sX hX g hY hXg _ (chernCap D sX hX E r hE g hY j k α) :=
  rfl

/-- **Stacks 0ERZ: the total Chern class** `c(ℰ) = c₀(ℰ) + c₁(ℰ) + … + c_r(ℰ)`, the formal sum of
the Chern classes of `ℰ` (`AlgebraicGeometry.Space.chernClass`), a nonhomogeneous class in the
Chow cohomology `A^*(X) = ⊕_p A^p(X)` (`AlgebraicGeometry.Space.chowCohomologyCanonical`). -/
@[stacks 0ERZ "the total Chern class c(E) = c_0(E) + c_1(E) + ... + c_r(E), the formal sum of \
the Chern classes as a nonhomogeneous class in A^*(X) = ⊕_p A^p(X)"]
def totalChernClass : chowCohomologyCanonical.{u + 1} D sX hX :=
  ∑ j : Fin (r + 1), DirectSum.of (fun p => chowCohomologyComponentCanonical.{u + 1} D sX hX p)
    ((j : ℕ) : ℤ) (chernClass D sX hX E r hE j)

/-- **Stacks 0ERY.** In Situation 0EDT let `X/B` be good, `ℰ` a finite locally free `𝒪_X`-module
of rank `r` and `(π : P → X, 𝒪_P(1))` its projective space bundle. For every morphism
`g : X' → X` of good algebraic spaces over `B` there are unique maps
`c_j(ℰ) ∩ - : CH_k(X') → CH_{k-j}(X')`, `j = 0, …, r`, such that `c₀(ℰ) ∩ α = α` and

`∑_{i=0}^{r} (-1)^i c₁(𝒪_{P'}(1))^i ∩ π'^*(c_{r-i}(ℰ) ∩ α) = 0`

for every `α ∈ CH_k(X')`, where `π' : P' = P ×_X X' → X'` is the base change of `π` and
`𝒪_{P'}(1)` the pullback of `𝒪_P(1)` (`AlgebraicGeometry.Space.chernRelationSum`). Moreover these
maps define a bivariant class `c_j(ℰ)` of degree `j` on `X`: there is `C ∈ A^j(X → X)` whose cap
operation on every test space `X'` is `c_j(ℰ) ∩ -`, read on `X ×_X X' ≅ X'` along the flat
pullback of relative dimension `0` (`AlgebraicGeometry.Space.testSpacePullbackChowMap`).

The Chow groups are those of Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK
(`AlgebraicGeometry.Space.chowGroupCanonical`), the bivariant classes those of Stacks 0ERJ over
them (`AlgebraicGeometry.Space.BivariantClassCanonical`), `c₀ ∩ α = α` is read through the
identification `CH_k = CH_{k-0}`, and the class is
`AlgebraicGeometry.Space.chernClass` (Stacks 0ERZ). -/
@[stacks 0ERY "existence and uniqueness of c_i(E) ∩ - : CH_k(X') → CH_{k-i}(X'), i = 0..r, with \
c_0 = id and sum_i (-1)^i c_1(O_{P'}(1))^i ∩ π'^*(c_{r-i}(E) ∩ α) = 0 on P' = P ×_X X', for every \
morphism X' → X of good spaces over B, E finite locally free of rank r on a good X/B; and the maps \
c_i(E) ∩ - form a bivariant class of degree i (BivariantClassCanonical, over chowGroupCanonical)"]
theorem existsUnique_chernCap_and_bivariant :
    (∀ {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)),
      ∃! c : ∀ (j : Fin (r + 1)) (k : ℤ), chowGroupCanonical.{u + 1} D (g ≫ sX) hY k →+
          chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k - ((j : ℕ) : ℤ)),
        (∀ k α, c 0 k α = ProjectiveBundleRelation.degreeCast
          (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) (by simp) α) ∧
          ∀ k α, chernRelationSum D sX hX E r hE g hY c k α = 0) ∧
      ∀ j : Fin (r + 1), ∃ C : chowCohomologyComponentCanonical.{u + 1} D sX hX ((j : ℕ) : ℤ),
        ∀ {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
          (hXg : D.IsGood (pullback.fst (𝟙 X) g ≫ sX))
          (c : ∀ (j : Fin (r + 1)) (k : ℤ), chowGroupCanonical.{u + 1} D (g ≫ sX) hY k →+
            chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k - ((j : ℕ) : ℤ))),
          (∀ k α, c 0 k α = ProjectiveBundleRelation.degreeCast
            (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) (by simp) α) →
          (∀ k α, chernRelationSum D sX hX E r hE g hY c k α = 0) →
          ∀ k α, C.cap g hY hXg k α = testSpacePullbackChowMap D sX hX g hY hXg _ (c j k α) := by
  refine ⟨fun g hY => ⟨chernCap D sX hX E r hE g hY,
    ⟨chernCap_zero D sX hX E r hE g hY, chernRelationSum_chernCap D sX hX E r hE g hY⟩,
    fun c hc => chernCap_unique D sX hX E r hE g hY c hc.1 hc.2⟩,
    fun j => ⟨chernClass D sX hX E r hE j,
    fun g hY hXg c h0 hc k α => ?_⟩⟩
  rw [chernCap_unique D sX hX E r hE g hY c h0 hc]
  rfl

end Chern

end AlgebraicGeometry.Space

end
