module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FormulaOfRank
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotivesFiniteBiproducts
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The correspondences of the projective space bundle formula

Let `k` be a field, `X` a smooth projective scheme over `k`, `ℰ` a finite locally free
`𝒪_X`-module of rank `r` and `p : P = 𝐏(ℰ) ⟶ X` its projective bundle, with `𝒪_P(1)` normalized
so that `p_*𝒪_P(1) = ℰ`. Section 0FGP of the Stacks Project considers, for `i = 0, …, r - 1`, the
correspondences

  `c_i = c₁(pr₂^*𝒪_P(1))^i ∩ [Γ_p] ∈ Corr^i(X, P)`,

and reads `c_i` as a morphism `h(X)(-i) ⟶ h(P)` of Chow motives. This file defines them.

Correspondences between smooth projective schemes of mixed dimension are
`Corrʳ(X, Y) = ⊕_d ⊕_e CH_{e-r}(X_d × Y_e) ⊗ ℚ` (`Stacks.WeilCohomology.Corr`), and capping
with the first Chern class of the pullback `pr₂^*ℒ` of an invertible module `ℒ` on `Y` is done
block by block: on `X_d × Y_e` the module is the pullback of `ℒ` along the second projection
followed by the inclusion `Y_e ⊆ Y`, and its first Chern class cap (Stacks 02SO) lowers the
dimension by one and so raises the degree of the correspondence by one.

## Main definitions

* `Stacks.WeilCohomology.blockTwist`: the pullback of `ℒ` to the block `X_d × Y_e`.
* `Stacks.WeilCohomology.corrTwistCap`: `c ↦ c₁(pr₂^*ℒ)^i ∩ c`,
  `Corrʳ(X, Y) ⟶ Corr^{r+i}(X, Y)`.
* `Stacks.WeilCohomology.projectiveBundleCorr`: the correspondence
  `c_i = c₁(pr₂^*𝒪_P(1))^i ∩ [Γ_p] ∈ Corr^i(X, P)`.
* `Stacks.WeilCohomology.twistedMotive`: the twisted motive `h(Y)(m) = (Y, 1, m)`.
* `Stacks.WeilCohomology.projectiveBundleHom`: `c_i` as a morphism `h(X)(-i) ⟶ h(P)` of Chow
  motives.

## References

* [Stacks Project, Section 0FGP](https://stacks.math.columbia.edu/tag/0FGP)
* [Stacks Project, Tag 0FGQ](https://stacks.math.columbia.edu/tag/0FGQ)
* [Stacks Project, Tag 0FG1](https://stacks.math.columbia.edu/tag/0FG1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open CategoryTheory.GradedCategory

universe u

namespace Stacks.WeilCohomology

section TwistCap

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY]
  (L : Y.Modules) [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]

/-- The pullback `pr₂^*ℒ` of an invertible module `ℒ` on `Y` to the block `X_d × Y_e`: the
pullback along the second projection followed by the inclusion `Y_e ⊆ Y`. -/
def blockTwist (d e : ℕ) : (Limits.pullback (partBase sX d) (partBase sY e)).Modules :=
  (Scheme.Modules.pullback (pullback.snd (partBase sX d) (partBase sY e) ≫
    (dimPart sY e).ι)).obj L

/-- The pullback `pr₂^*ℒ` of an invertible module to the block `X_d × Y_e` is invertible. -/
instance (d e : ℕ) :
    SheafOfModules.IsInvertible (Limits.pullback (partBase sX d) (partBase sY e)).sheaf.obj
      (Limits.pullback (partBase sX d) (partBase sY e)).ringCatSheaf.property
      (blockTwist k sX sY L d e) :=
  GenuineChern.isInvertible_pullback _ L

/-- `c ↦ c₁(pr₂^*ℒ)^i ∩ c` on the block `X_d × Y_e` of the correspondences, from degree `r` to
degree `r' = r + i`: the `i`-th power of the first Chern class cap of `blockTwist` (Stacks 02SO),
`CH_{e-r}(X_d × Y_e) ⟶ CH_{e-r'}(X_d × Y_e)`, with rational coefficients. -/
def blockTwistCap (i : ℕ) (d e : ℕ) {r r' : ℤ} (h : r' = r + i) :
    Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r →ₗ[ℚ]
      Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r' :=
  ((capPow (fieldChowSituation k) (pullback.fst (partBase sX d) (partBase sY e) ≫ partBase sX d)
      (invCap (fieldChowSituation k) _ (blockTwist k sX sY L d e)) i ((e : ℤ) - r) ((e : ℤ) - r')
      (by omega)).toIntLinearMap).baseChange ℚ

/-- **`c ↦ c₁(pr₂^*ℒ)^i ∩ c`**, `Corrʳ(X, Y) ⟶ Corr^{r'}(X, Y)` for `r' = r + i`: the cap with
the `i`-th power of the first Chern class of the pullback of `ℒ` along the second projection
`X × Y ⟶ Y`, block by block on `X_d × Y_e`. -/
def corrTwistCap (i : ℕ) {r r' : ℤ} (h : r' = r + i) : Corr k sX sY r →ₗ[ℚ] Corr k sX sY r' :=
  DirectSum.lmap fun d ↦ DirectSum.lmap fun e ↦ blockTwistCap k sX sY L i d e h

end TwistCap

section Bundle

variable {k : Type u} [Field k] (X : (SmoothProjectiveScheme k).FullSubcategory)
  (E : X.obj.left.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]

/-- The projective bundle `P = 𝐏(ℰ)` of a finite locally free module of rank `n + 1` on a smooth
projective scheme over `k`, as a smooth projective scheme over `k`. -/
abbrev projectiveBundle : (SmoothProjectiveScheme k).FullSubcategory :=
  SmoothProjectiveScheme.bundle X E n

/-- The twist `𝒪_P(1)` of the projective bundle, normalized so that `p_*𝒪_P(1) = ℰ`. -/
abbrev projectiveBundleTwist : (projectiveBundle X E n).obj.left.Modules :=
  letI := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (n + 1)
  bundleTwist E

/-- The twist `𝒪_P(1)` of the projective bundle is an invertible module. -/
instance : SheafOfModules.IsInvertible (projectiveBundle X E n).obj.left.sheaf.obj
    (projectiveBundle X E n).obj.left.ringCatSheaf.property (projectiveBundleTwist X E n) :=
  letI := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (n + 1)
  isInvertible_bundleTwist E

/-- **The correspondences of Section 0FGP**:
`c_i = c₁(pr₂^*𝒪_P(1))^i ∩ [Γ_p] ∈ Corr^i(X, P)` for the projective bundle `p : P ⟶ X`, with
`[Γ_p] ∈ Corr⁰(X, P)` the graph class of Example 0FG1. The degree `r` is any integer equal to `i`,
so that `c_i` can be read in the degree `0 - (-i)` of a morphism `h(X)(-i) ⟶ h(P)`. -/
def projectiveBundleCorr (i : ℕ) {r : ℤ} (h : r = i) :
    SmoothProjectiveCorr X (projectiveBundle X E n) r :=
  (SmoothProjectiveCorr.toCorr X (projectiveBundle X E n) r).symm
    (corrTwistCap k X.obj.hom (projectiveBundle X E n).obj.hom (projectiveBundleTwist X E n) i
      (by omega : r = 0 + i)
      (SmoothProjectiveCorr.toCorr X (projectiveBundle X E n) 0
        (graphCorrespondenceSP (SmoothProjectiveScheme.bundleProj X E n))))

/-- The twisted motive `h(Y)(m) = (Y, 1, m)` of a smooth projective scheme `Y` over `k`: the scheme
`Y`, the identity correspondence `1 = [Δ_Y]` as projector, and the twist `m`. For `m = 0` it is
`h(Y)` (`Stacks.WeilCohomology.twistedMotive_zero`). -/
abbrev twistedMotive (Y : (SmoothProjectiveScheme k).FullSubcategory) (m : ℤ) :
    ChowMotiveCat k where
  X := GradedCompositionData.Obj.mk Y
  p := 𝟙 _
  p_mem := GradedCategory.id_mem _
  idem := Category.comp_id _
  twist := m

/-- `h(Y)(0) = h(Y)`. -/
theorem twistedMotive_zero (Y : (SmoothProjectiveScheme k).FullSubcategory) :
    twistedMotive Y 0 = (ChowMotiveCat.h k).obj (Opposite.op Y) :=
  rfl

/-- **The morphism `c_i : h(X)(-i) ⟶ h(P)`** of Chow motives of Section 0FGP: the correspondence
`c_i ∈ Corr^i(X, P)` read as a morphism from `h(X)(-i) = (X, 1, -i)` to `h(P) = (P, 1, 0)`, whose
morphisms are `Corr^{0 - (-i)}(X, P)`. -/
def projectiveBundleHom (i : ℕ) :
    twistedMotive X (-(i : ℤ)) ⟶ twistedMotive (projectiveBundle X E n) 0 :=
  TwistedKaroubi.Hom.mk
    (ChowMotiveCat.homOf _
      (projectiveBundleCorr X E n i (by change (0 : ℤ) - -(i : ℤ) = i; omega)))
    ⟨ChowMotiveCat.homOf_mem_grade _, Category.id_comp _, Category.comp_id _⟩

end Bundle

section OfRank

variable {k : Type u} [Field k] (X : (SmoothProjectiveScheme k).FullSubcategory)
  (E : X.obj.left.Modules)

/-- The morphism `c_i : h(X)(-i) ⟶ h(P)` indexed by `i : Fin (n + 1)`. -/
abbrev projectiveBundleFinHom (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
    (i : Fin (n + 1)) :
    twistedMotive X (-((i : ℕ) : ℤ)) ⟶ twistedMotive (projectiveBundle X E n) 0 :=
  projectiveBundleHom X E n i

/-- **The projective bundle `P = 𝐏(ℰ)` of a finite locally free module of rank `r`**, as a smooth
projective scheme over `k`: `Stacks.WeilCohomology.projectiveBundle` for `r = n + 1`, and the
(empty) projective bundle of a module of rank zero for `r = 0`. -/
def projectiveBundleOfRank : (r : ℕ) → [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] →
    (SmoothProjectiveScheme k).FullSubcategory
  | 0, _ =>
    letI := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 0
    haveI := isEmpty_bundle_of_rank_zero E
    SmoothProjectiveScheme.mk (Stacks.Chow.bundleProj E ≫ X.obj.hom) inferInstance
      (IsProjective.comp (SmoothProjectiveScheme.isProjective_bundleProj X E)
        (SmoothProjectiveScheme.isProjective X))
  | n + 1, _ => projectiveBundle X E n

/-- For `r = n + 1` the projective bundle of a module of rank `r` is `projectiveBundle X E n`. -/
theorem twistedMotive_projectiveBundleOfRank_succ (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] :
    twistedMotive (projectiveBundle X E n) 0 =
      twistedMotive (projectiveBundleOfRank X E (n + 1)) 0 :=
  rfl

/-- **The morphisms `c_i : h(X)(-i) ⟶ h(P)`, `i < r`**, of Section 0FGP, for a module of rank
`r`: for `r = n + 1` they are `Stacks.WeilCohomology.projectiveBundleHom`,
`c_i = c₁(pr₂^*𝒪_P(1))^i ∩ [Γ_p]` (read in `projectiveBundleOfRank X E (n + 1)`, which is
`projectiveBundle X E n` by definition), and for `r = 0` there are none. -/
def projectiveBundleOfRankHom : (r : ℕ) → [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] →
    (i : Fin r) →
      (twistedMotive X (-((i : ℕ) : ℤ)) ⟶ twistedMotive (projectiveBundleOfRank X E r) 0)
  | n + 1, _, i => projectiveBundleFinHom X E n i ≫
      eqToHom (twistedMotive_projectiveBundleOfRank_succ X E n)

end OfRank

end Stacks.WeilCohomology

end
