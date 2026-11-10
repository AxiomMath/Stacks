module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchComapCartier
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchPreimageCycle
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.SupComapSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimension

/-!
# The two branches over `W` are integral of δ-dimension `k+2`, and only the first lies in `D₁`

In the situation of [Stacks, Tag 0F97] let `W ⊆ Y` be an integral closed subscheme of
δ-dimension `k+1` contained in the divisor `D = Z(s)`. The case `W ⊆ D` of [Stacks, Tag 0F98]
splits the fundamental cycle of `p^{-1}(W)` as `[W₁] + [W₂]`, where

  `W_i = D_i ∩ p^{-1}(W)`,  as an ideal sheaf on `L` the join  `D_i ⊔ p^{-1}(W)`,

and then evaluates the Gysin rule of `i₁ : D₁ ⟶ L` on each summand. That evaluation needs three
things which the cycle split itself does not provide: each `W_i` must be an *integral* closed
subscheme of `L`, each must have δ-dimension *exactly* `k+2`, and `D₁` must contain `W₁` but not
`W₂`, so that the Gysin rule takes its contained branch at the first and its uncontained branch
at the second. This file supplies all three.

## Main results

* `Stacks.Chow.TensorZeroScheme.isIntegral_sup_comap_proj_of_le` and
  `…isIntegral_sup_comap_proj₂_of_le` — **the two branches over `W` are integral**, in the join
  presentation `D_i ⊔ p^{-1}(W)`.
* `Stacks.Chow.TensorZeroScheme.schemeDeltaDimension_zeroIdeal_comap_of_le` — the divisor of the
  base-changed diagram over `W` has the δ-dimension of `W`.
* `Stacks.Chow.TensorZeroScheme.schemeDeltaDimension_sup_comap_proj_of_le` and
  `…schemeDeltaDimension_sup_comap_proj₂_of_le` — **the two branches over `W` have δ-dimension
  exactly `k+2`**, in the same join presentation.
* `Stacks.Chow.TensorZeroScheme.not_branch₁_le_branch₂_sup_comap_proj_of_le` — **`D₁` does not
  contain the second branch over `W`.**

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.PullbackTensorIso (pullbackTensorSection)

universe u

namespace Stacks.Chow.TensorZeroScheme


variable {Y : Scheme.{u}} (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (R : Decomposition Y L₁ L₂ s)
  (W : Y.IdealSheafData)

/-! ### The two branches over `W` are integral -/

/-- The join `D ⊔ I` is integral once the pullback of `D` to `I` is. -/
private theorem isIntegral_sup_comap_of_isIntegral_comap {X : Scheme.{u}}
    (I D : X.IdealSheafData) (h : IsIntegral (D.comap I.subschemeι).subscheme) :
    IsIntegral (D ⊔ I).subscheme := by
  rw [sup_comm]
  exact IsIntegral.of_isIso (Scheme.IdealSheafData.supComapSubschemeIso I D).inv

include h₁ h₂ in
/-- **The first branch `D₁ ⊔ p^{-1}(W)` over `W` is an integral closed subscheme of `L`**, for
`W` an integral closed subscheme of `Y` contained in the divisor `D = Z(s)`. -/
theorem isIntegral_sup_comap_proj_of_le (hW : zeroIdeal Y L₁ L₂ s ≤ W)
    [IsIntegral W.subscheme] :
    IsIntegral (R.normalize.D₁ ⊔ W.comap R.normalize.p).subscheme := by
  have : IsIntegral
      (R.normalize.D₁.comap (W.comap R.normalize.p).subschemeι).subscheme := by
    rw [← comap_branch₁_decompositionComap L₁ L₂ s R W]
    exact Decomposition.isIntegral_D₁_subscheme_of_zeroIdeal_le L₁ L₂ s W hW
      (decompositionComap L₁ L₂ s R W)
  exact isIntegral_sup_comap_of_isIntegral_comap _ _ this

include h₁ h₂ in
/-- **The second branch `D₂ ⊔ p^{-1}(W)` over `W` is an integral closed subscheme of `L`**, for
`W` an integral closed subscheme of `Y` contained in the divisor `D = Z(s)`. -/
theorem isIntegral_sup_comap_proj₂_of_le (hW : zeroIdeal Y L₁ L₂ s ≤ W)
    [IsIntegral W.subscheme] :
    IsIntegral (R.normalize.D₂ ⊔ W.comap R.normalize.p).subscheme := by
  have : IsIntegral
      (R.normalize.D₂.comap (W.comap R.normalize.p).subschemeι).subscheme := by
    rw [← comap_branch₂_decompositionComap L₁ L₂ s R W]
    exact Decomposition.isIntegral_D₂_subscheme_of_zeroIdeal_le L₁ L₂ s W hW
      (decompositionComap L₁ L₂ s R W)
  exact isIntegral_sup_comap_of_isIntegral_comap _ _ this

/-! ### The δ-dimension of the two branches over `W` -/

variable (C : Stacks.Chow.ChowSituation.{u}) (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (k : ℤ)

include h₁ h₂ in
/-- **The divisor of the base-changed diagram over `W` has the δ-dimension of `W`**, for `W` a
closed subscheme of `Y` of δ-dimension `k+1` contained in the divisor `D = Z(s)`. -/
theorem schemeDeltaDimension_zeroIdeal_comap_of_le (hW : zeroIdeal Y L₁ L₂ s ≤ W)
    (hDim : Stacks.Chow.schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt)) :
    Stacks.Chow.schemeDeltaDimension C
        ((zeroIdeal W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι ≫ W.subschemeι ≫ sY) =
      ((k + 1 : ℤ) : EInt) := by
  have : IsIso (zeroIdeal W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι := by
    refine IsClosedImmersion.isIso_iff_ker_eq_bot.2 ?_
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact zeroIdeal_pullbackTensorSection_subschemeι_eq_bot L₁ L₂ s W hW
  exact (Stacks.Chow.schemeDeltaDimension_comp_iso C
    (asIso (zeroIdeal W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι)
    (W.subschemeι ≫ sY)).trans hDim

section Bundle

variable (N : W.subscheme.Modules)
  [hN : AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.sheaf.obj
    W.subscheme.ringCatSheaf.property N]

include h₁ h₂ hN in
/-- The structure morphism of the divisor of the base-changed diagram, read as a morphism out of
the *base of the branch bundle*, is locally of finite type. -/
private theorem locallyOfFiniteType_subschemeι_comp_branchSituation_X :
    @LocallyOfFiniteType
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s) N).X C.S
      ((zeroIdeal W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι ≫ W.subschemeι ≫ sY) :=
  inferInstanceAs (LocallyOfFiniteType
    ((zeroIdeal W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι ≫ W.subschemeι ≫ sY))

end Bundle

/-- A closed subscheme `J` of the total space of `R`, isomorphic over `D` to the branch bundle for
`N`, has δ-dimension `k+2` over a `W` of δ-dimension `k+1`. -/
private theorem schemeDeltaDimension_of_iso_branchSituation (hW : zeroIdeal Y L₁ L₂ s ≤ W)
    [IsIntegral W.subscheme]
    (hDim : Stacks.Chow.schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (R : Decomposition W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s))
    (N : W.subscheme.Modules)
    [hN : AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.sheaf.obj
      W.subscheme.ringCatSheaf.property N]
    (J : R.total.IdealSheafData) [LocallyOfFiniteType (J.subschemeι ≫ R.p ≫ W.subschemeι ≫ sY)]
    (p' : J.subscheme ⟶ (zeroIdeal W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)).subscheme)
    (hcomm : J.subschemeι ≫ R.p = p' ≫ (zeroIdeal W.subscheme
      ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι)
    (e : J.subscheme ≅ (branchSituation W.subscheme
      ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s) N).totalSpace)
    (he : e.hom ≫ (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s) N).totalSpaceToBase = p') :
    Stacks.Chow.schemeDeltaDimension C (J.subschemeι ≫ R.p ≫ W.subschemeι ≫ sY) =
      ((k + 2 : ℤ) : EInt) := by
  have := locallyOfFiniteType_subschemeι_comp_branchSituation_X L₁ L₂ s W C sY N
  have hmor : J.subschemeι ≫ R.p ≫ W.subschemeι ≫ sY =
      e.hom ≫ (branchSituation W.subscheme
          ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s) N).totalSpaceToBase ≫
        ((zeroIdeal W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι ≫ W.subschemeι ≫ sY) := by
    rw [← Category.assoc J.subschemeι, hcomm, ← he]
    exact Category.assoc _ _ _
  refine (Stacks.Chow.schemeDeltaDimension_congr C hmor).trans ?_
  refine (Stacks.Chow.schemeDeltaDimension_comp_iso C e _).trans ?_
  refine (schemeDeltaDimension_branchSituation_of_le L₁ L₂ s W N C
    ((zeroIdeal W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι ≫ W.subschemeι ≫ sY) hW
    (schemeDeltaDimension_zeroIdeal_comap_of_le L₁ L₂ s W C sY k hW hDim)).trans ?_
  rw [show (k + 1 + 1 : ℤ) = k + 2 by lia]

include h₁ h₂ in
/-- **The first branch of a decomposition over an integral closed subscheme of `D` of δ-dimension
`k+1` has δ-dimension `k+2`.** Here `q` is the structure morphism `R.p ≫ W.subschemeι ≫ sY` of
the total space and `J` is the first branch `R.D₁`, each given up to an equality. -/
theorem Decomposition.schemeDeltaDimension_D₁_of_zeroIdeal_le (hW : zeroIdeal Y L₁ L₂ s ≤ W)
    [IsIntegral W.subscheme]
    (R : Decomposition W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s))
    (q : R.total ⟶ C.S) [LocallyOfFiniteType q] (hq : q = R.p ≫ W.subschemeι ≫ sY)
    (hDim : Stacks.Chow.schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (J : R.total.IdealSheafData) (hJ : J = R.D₁) :
    Stacks.Chow.schemeDeltaDimension C (J.subschemeι ≫ q) = ((k + 2 : ℤ) : EInt) := by
  subst hJ
  subst hq
  exact schemeDeltaDimension_of_iso_branchSituation L₁ L₂ s W C sY k hW hDim R
    ((Scheme.Modules.pullback W.subschemeι).obj L₂) R.D₁ R.p₁ R.comm₁ R.branch₁
    R.branch₁_toBase

include h₁ h₂ in
/-- **The second branch of a decomposition over an integral closed subscheme of `D` of
δ-dimension `k+1` has δ-dimension `k+2`.** Here `q` is the structure morphism
`R.p ≫ W.subschemeι ≫ sY` of the total space and `J` is the second branch `R.D₂`, each given up
to an equality. -/
theorem Decomposition.schemeDeltaDimension_D₂_of_zeroIdeal_le (hW : zeroIdeal Y L₁ L₂ s ≤ W)
    [IsIntegral W.subscheme]
    (R : Decomposition W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s))
    (q : R.total ⟶ C.S) [LocallyOfFiniteType q] (hq : q = R.p ≫ W.subschemeι ≫ sY)
    (hDim : Stacks.Chow.schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (J : R.total.IdealSheafData) (hJ : J = R.D₂) :
    Stacks.Chow.schemeDeltaDimension C (J.subschemeι ≫ q) = ((k + 2 : ℤ) : EInt) := by
  subst hJ
  subst hq
  exact schemeDeltaDimension_of_iso_branchSituation L₁ L₂ s W C sY k hW hDim R
    ((Scheme.Modules.pullback W.subschemeι).obj L₁) R.D₂ R.p₂ R.comm₂ R.branch₂
    R.branch₂_toBase

omit [LocallyOfFiniteType sY] in
include h₁ h₂ in
/-- The structure morphism of `p^{-1}(W)` over the base factors through `W`, along the projection
of the base-changed diagram `Stacks.Chow.TensorZeroScheme.decompositionComap`. -/
theorem comap_proj_subschemeι_comp_proj_comp :
    (W.comap R.normalize.p).subschemeι ≫ R.normalize.p ≫ sY =
      (decompositionComap L₁ L₂ s R W).p ≫ W.subschemeι ≫ sY := by
  rw [← Category.assoc, (isPullback_comap_proj L₁ L₂ s R W).w, Category.assoc]
  rfl

include h₁ h₂ in
/-- The structure morphism of `p^{-1}(W)` over the base, read as a morphism out of the *total
space of the base-changed diagram*, is locally of finite type. -/
private theorem locallyOfFiniteType_comap_proj_subschemeι_comp :
    @LocallyOfFiniteType (decompositionComap L₁ L₂ s R W).total C.S
      ((W.comap R.normalize.p).subschemeι ≫ R.normalize.p ≫ sY) :=
  inferInstanceAs (LocallyOfFiniteType
    ((W.comap R.normalize.p).subschemeι ≫ R.normalize.p ≫ sY))

/-- Delta-dimension of a join `D ⊔ I` equals that of the pullback of `D` to `I`, viewed in `X`. -/
private theorem schemeDeltaDimension_sup_eq (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}}
    (g : X ⟶ C.S) [LocallyOfFiniteType g] (D I : X.IdealSheafData) :
    Stacks.Chow.schemeDeltaDimension C ((D ⊔ I).subschemeι ≫ g) =
      Stacks.Chow.schemeDeltaDimension C
        ((D.comap I.subschemeι).subschemeι ≫ I.subschemeι ≫ g) := by
  have hrange : Set.range (D ⊔ I).subschemeι = Set.range (I ⊔ D).subschemeι :=
    congrArg (fun J : X.IdealSheafData => Set.range J.subschemeι) (sup_comm _ _)
  refine (Stacks.Chow.schemeDeltaDimension_eq_of_equal_ranges C g _ _ hrange).trans ?_
  have hι : (I ⊔ D).subschemeι = (Scheme.IdealSheafData.supComapSubschemeIso I D).hom ≫
      (D.comap I.subschemeι).subschemeι ≫ I.subschemeι := by
    rw [← Category.assoc, Scheme.IdealSheafData.supComapSubschemeIso_hom_subschemeι,
      Scheme.IdealSheafData.inclusion_subschemeι]
  have hfac : (I ⊔ D).subschemeι ≫ g = (I.supComapSubschemeIso D).hom ≫
      (D.comap I.subschemeι).subschemeι ≫ I.subschemeι ≫ g := by
    simp only [hι, Category.assoc]
  exact (Stacks.Chow.schemeDeltaDimension_congr C hfac).trans
    (Stacks.Chow.schemeDeltaDimension_comp_iso C _ _)

include h₁ h₂ in
/-- **The first branch `D₁ ⊔ p^{-1}(W)` over `W` has δ-dimension exactly `k+2`**, for `W` an
integral closed subscheme of `Y` of δ-dimension `k+1` contained in the divisor `D = Z(s)`. -/
theorem schemeDeltaDimension_sup_comap_proj_of_le (hW : zeroIdeal Y L₁ L₂ s ≤ W)
    [IsIntegral W.subscheme]
    (hDim : Stacks.Chow.schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt)) :
    Stacks.Chow.schemeDeltaDimension C
        ((R.normalize.D₁ ⊔ W.comap R.normalize.p).subschemeι ≫ R.normalize.p ≫ sY) =
      ((k + 2 : ℤ) : EInt) := by
  refine (schemeDeltaDimension_sup_eq C (R.normalize.p ≫ sY) _ _).trans ?_
  have := locallyOfFiniteType_comap_proj_subschemeι_comp L₁ L₂ s R W C sY
  exact Decomposition.schemeDeltaDimension_D₁_of_zeroIdeal_le L₁ L₂ s W C sY k hW
    (decompositionComap L₁ L₂ s R W)
    ((W.comap R.normalize.p).subschemeι ≫ R.normalize.p ≫ sY)
    (comap_proj_subschemeι_comp_proj_comp L₁ L₂ s R W C sY) hDim _
    (comap_branch₁_decompositionComap L₁ L₂ s R W).symm

include h₁ h₂ in
/-- **The second branch `D₂ ⊔ p^{-1}(W)` over `W` has δ-dimension exactly `k+2`**, for `W` an
integral closed subscheme of `Y` of δ-dimension `k+1` contained in the divisor `D = Z(s)`. -/
theorem schemeDeltaDimension_sup_comap_proj₂_of_le (hW : zeroIdeal Y L₁ L₂ s ≤ W)
    [IsIntegral W.subscheme]
    (hDim : Stacks.Chow.schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt)) :
    Stacks.Chow.schemeDeltaDimension C
        ((R.normalize.D₂ ⊔ W.comap R.normalize.p).subschemeι ≫ R.normalize.p ≫ sY) =
      ((k + 2 : ℤ) : EInt) := by
  refine (schemeDeltaDimension_sup_eq C (R.normalize.p ≫ sY) _ _).trans ?_
  have := locallyOfFiniteType_comap_proj_subschemeι_comp L₁ L₂ s R W C sY
  exact Decomposition.schemeDeltaDimension_D₂_of_zeroIdeal_le L₁ L₂ s W C sY k hW
    (decompositionComap L₁ L₂ s R W)
    ((W.comap R.normalize.p).subschemeι ≫ R.normalize.p ≫ sY)
    (comap_proj_subschemeι_comp_proj_comp L₁ L₂ s R W C sY) hDim _
    (comap_branch₂_decompositionComap L₁ L₂ s R W).symm

/-! ### Only the first branch lies in `D₁` -/

include h₁ h₂ in
/-- **`D₁` does not contain the second branch `W₂ = D₂ ⊔ p^{-1}(W)` over `W`**, for `W` an
integral closed subscheme of `Y` of δ-dimension `k+1` contained in the divisor `D = Z(s)`. -/
theorem not_branch₁_le_branch₂_sup_comap_proj_of_le (hW : zeroIdeal Y L₁ L₂ s ≤ W)
    [IsIntegral W.subscheme]
    (hDim : Stacks.Chow.schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt)) :
    ¬ R.normalize.D₁ ≤ R.normalize.D₂ ⊔ W.comap R.normalize.p := by
  intro hcon
  have htriple : (R.normalize.D₁ ⊔ R.normalize.D₂) ⊔ W.comap R.normalize.p =
      R.normalize.D₂ ⊔ W.comap R.normalize.p := by
    rw [sup_assoc]
    exact sup_eq_right.2 hcon
  have hle : Stacks.Chow.schemeDeltaDimension C
      ((R.normalize.D₂ ⊔ W.comap R.normalize.p).subschemeι ≫ R.normalize.p ≫ sY) ≤
      ((k + 1 : ℤ) : EInt) := by
    refine Stacks.Chow.schemeDeltaDimension_le_of_forall_relativeDimension_le C
      (R.normalize.p ≫ sY) _ fun w => ?_
    refine relativeDimension_le_of_mem_support_sup_sup L₁ L₂ s R W C sY k hDim ?_
    rw [htriple, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨w, rfl⟩
  rw [schemeDeltaDimension_sup_comap_proj₂_of_le L₁ L₂ s R W C sY k hW hDim] at hle
  have hnum : (k + 2 : ℤ) ≤ (k + 1 : ℤ) := WithBotTop.coe_le_coe.1 hle
  lia

end Stacks.Chow.TensorZeroScheme

end
