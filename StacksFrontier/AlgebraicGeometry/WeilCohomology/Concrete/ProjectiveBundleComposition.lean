module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.CapPowCommute
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Compat
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.SmoothIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinFunctoriality
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ExteriorProductIntersection
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionRegularImmersionProduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalFlat

/-!
# Composition with a Chern class cap of the graph of a flat morphism

Let `k` be a field and let `Z`, `A`, `B` be smooth and separated over `k`, of constant dimensions
`f`, `d`, `e`, with `A` proper. Let `g : B ⟶ A` be a morphism over `k`, flat of relative
dimension `t`, let `[Γ_g] ∈ CH_e(A × B)` be the class of its graph and let `ℒ` be an invertible
module on `B`. For `u ∈ CH_{d-r}(Z × A)` the composition of correspondences (Section 0FFZ) with
`c₁(pr₂^*ℒ)^s ∩ [Γ_g]` is

  `(c₁(pr₂^*ℒ)^s ∩ [Γ_g]) ∘ u = c₁(pr₂^*ℒ)^s ∩ (1 × g)^* u`   in   `CH_{e-(r+s)}(Z × B)`.

This is the computation behind the proof of Stacks 0FGQ: the source records it as "pushforward
along `c_i` sends `α` to `c₁(𝒪_P(1))^i ∩ p^*α`", via Stacks 0FG5 and 0FF4, for `Z = Spec k`.

## Proof

Write `W = Z × A × B` and `j = (1 × g, pr₂) : Z × B ⟶ W`, the base change of the graph
`Γ_g : B ⟶ A × B` along `pr₂₃ : W ⟶ A × B`; then `pr₁₂ ∘ j = 1 × g` and `pr₁₃ ∘ j = 1`. By
Stacks 0FC2 write `u = a ∩ [Z × A]` with `a ∈ A^*(Z × A)`, so that `pr₁₂^* u = a ∩ [W]` and the
intersection product with `pr₁₂^*u` is capping with `a` (the second clause of Stacks 0FC2). Then

  `pr₂₃^*(ξ^s ∩ Γ_*[B]) = ξ^s ∩ j_*[Z × B] = j_*(ξ^s ∩ [Z × B])`

by Stacks 02SS, 02RG and 02SU, and capping with `a` commutes with `j_*` (the projection formula
for Chow cohomology) and with `ξ^s ∩ -` (Stacks 0B7B). Pushing forward along `pr₁₃` gives
`ξ^s ∩ (res(a) ∩ [Z × B])`, and `res(a) ∩ [Z × B] = (1 × g)^* u` because flat pullback carries
`a ∩ [Z × A]` to `res(a) ∩ [Z × B]`.

## Main results

* `Stacks.WeilCohomology.compositionInt_capPow_graph`: the formula above.

## References

* [Stacks Project, Tag 0FGQ](https://stacks.math.columbia.edu/tag/0FGQ)
* [Stacks Project, Tag 0FC2](https://stacks.math.columbia.edu/tag/0FC2)
* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

section Geometry

variable {S Z A B : Scheme.{u}} (sZ : Z ⟶ S) (sA : A ⟶ S) (sB : B ⟶ S) (g : B ⟶ A)
  (hg : g ≫ sA = sB)

/-- The morphism `1 × g : Z × B ⟶ Z × A`. -/
abbrev prodMapRight : Limits.pullback sZ sB ⟶ Limits.pullback sZ sA :=
  pullback.map sZ sB sZ sA (𝟙 Z) g (𝟙 S) (by simp) (by simp [hg])

/-- The section `j = (1 × g, pr₂) : Z × B ⟶ Z × A × B` of `pr₁₃`, the base change of the graph of
`g` along `pr₂₃`. -/
def graphSection : Limits.pullback sZ sB ⟶ tripleProduct sZ sA sB :=
  pullback.lift (prodMapRight sZ sA sB g hg) (pullback.snd sZ sB)
    (by simp [prodBase, pullback.condition, hg])

/-- The composite `pr₁₂ ∘ j` is `1 × g`. -/
@[reassoc (attr := simp)]
theorem graphSection_pr₁₂ :
    graphSection sZ sA sB g hg ≫ pr₁₂ sZ sA sB = prodMapRight sZ sA sB g hg :=
  pullback.lift_fst _ _ _

/-- The composite of `j` with the projection `Z × A × B ⟶ B` is the projection `Z × B ⟶ B`. -/
@[reassoc (attr := simp)]
theorem graphSection_snd :
    graphSection sZ sA sB g hg ≫ pullback.snd (prodBase sZ sA) sB = pullback.snd sZ sB :=
  pullback.lift_snd _ _ _

/-- The composite `pr₂₃ ∘ j` is the graph of `g` precomposed with `pr₂ : Z × B ⟶ B`. -/
theorem graphSection_pr₂₃ :
    graphSection sZ sA sB g hg ≫ pr₂₃ sZ sA sB =
      pullback.snd sZ sB ≫ graphMorphism sA sB g hg := by
  apply pullback.hom_ext <;> simp [prodMapRight]

/-- The composite `pr₁₃ ∘ j` is the identity of `Z × B`. -/
theorem graphSection_pr₁₃ : graphSection sZ sA sB g hg ≫ pr₁₃ sZ sA sB = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [prodMapRight]

/-- The section `j` is a morphism over the base: its composite with the structure morphism of
`Z × A × B` is the structure morphism of `Z × B`. -/
theorem graphSection_comp_tripleBase :
    graphSection sZ sA sB g hg ≫ tripleBase sZ sA sB = prodBase sZ sB := by
  simp [tripleBase, prodBase, prodMapRight]

/-- `Z × B` is the base change of `Z × A` along `g`. -/
theorem isPullback_prodMapRight :
    IsPullback (prodMapRight sZ sA sB g hg) (pullback.snd sZ sB) (pullback.snd sZ sA) g := by
  refine IsPullback.of_right (h₁₂ := pullback.fst sZ sA) (v₁₃ := sZ) (h₂₂ := sA) ?_
    (by simp [prodMapRight]) (IsPullback.of_hasPullback sZ sA)
  have h1 : prodMapRight sZ sA sB g hg ≫ pullback.fst sZ sA = pullback.fst sZ sB := by
    simp [prodMapRight]
  rw [h1, hg]
  exact IsPullback.of_hasPullback sZ sB

/-- The square exhibiting `j : Z × B ⟶ Z × A × B` as the base change of the graph
`Γ_g : B ⟶ A × B` along `pr₂₃`. -/
theorem isPullback_graphSection :
    IsPullback (pullback.snd sZ sB) (graphSection sZ sA sB g hg) (graphMorphism sA sB g hg)
      (pr₂₃ sZ sA sB) := by
  refine (IsPullback.of_right (h₁₂ := pr₁₂ sZ sA sB) (v₁₃ := pullback.snd sZ sA)
    (h₂₂ := pullback.fst sA sB) ?_ (graphSection_pr₂₃ sZ sA sB g hg)
    (isPullback_pr₁₂_pr₂₃ sZ sA sB)).flip
  rw [graphSection_pr₁₂, graphMorphism_fst]
  exact isPullback_prodMapRight sZ sA sB g hg

end Geometry

section Composition

variable {k : Type u} [Field k] {Z A B : Scheme.{u}}
  (sZ : Z ⟶ (fieldChowSituation k).S) (sA : A ⟶ (fieldChowSituation k).S)
  (sB : B ⟶ (fieldChowSituation k).S) [Smooth sZ] [IsSeparated sZ] [Smooth sA]
  [IsSeparated sA] [Smooth sB] [IsSeparated sB] [IsProper sA] {f d e t : ℕ}
  (hZ : RelativeDimension sZ f) (hA : RelativeDimension sA d) (hB : RelativeDimension sB e)
  (g : B ⟶ A) (hg : g ≫ sA = sB) [Flat g] [LocallyOfFiniteType g]
  (ht : RelativeDimension g t) (L : B.Modules)
  [SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property L]

local notation "𝒞" => fieldChowSituation k

attribute [local instance] isClosedImmersion_graphMorphism

/-- The morphism `1 × g` is flat, as a base change of the flat morphism `g`. -/
instance : Flat (prodMapRight sZ sA sB g hg) :=
  MorphismProperty.of_isPullback (isPullback_prodMapRight sZ sA sB g hg).flip inferInstance

/-- The morphism `1 × g` is locally of finite type, as a base change of `g`. -/
instance : LocallyOfFiniteType (prodMapRight sZ sA sB g hg) :=
  MorphismProperty.of_isPullback (isPullback_prodMapRight sZ sA sB g hg).flip
    inferInstance

omit [Smooth sZ] [IsSeparated sZ] [Smooth sA] [IsSeparated sA] [Smooth sB] [IsSeparated sB]
    [IsProper sA] [Flat g] in
include ht in
/-- If `g` is flat of relative dimension `t`, then so is `1 × g`. -/
theorem relativeDimension_prodMapRight :
    RelativeDimension (prodMapRight sZ sA sB g hg) t :=
  RelativeDimension.of_isPullback (isPullback_prodMapRight sZ sA sB g hg).flip ht

omit [Smooth sZ] [IsSeparated sZ] [Smooth sA] [IsSeparated sA] [Smooth sB] [IsSeparated sB]
    [IsProper sA] [Flat g] [LocallyOfFiniteType g] in
/-- The morphism `1 × g : Z × B ⟶ Z × A` is a morphism over the base. -/
theorem prodMapRight_comp_prodBase :
    prodMapRight sZ sA sB g hg ≫ prodBase sZ sA = prodBase sZ sB := by
  simp [prodMapRight, prodBase]

/-- The pullback `pr₂^*ℒ` of the invertible module `ℒ` to `A × B` is invertible. -/
instance : SheafOfModules.IsInvertible (Limits.pullback sA sB).sheaf.obj
    (Limits.pullback sA sB).ringCatSheaf.property
    ((Scheme.Modules.pullback (pullback.snd sA sB)).obj L) :=
  GenuineChern.isInvertible_pullback _ L

/-- The pullback `pr₂^*ℒ` of the invertible module `ℒ` to `Z × B` is invertible. -/
instance : SheafOfModules.IsInvertible (Limits.pullback sZ sB).sheaf.obj
    (Limits.pullback sZ sB).ringCatSheaf.property
    ((Scheme.Modules.pullback (pullback.snd sZ sB)).obj L) :=
  GenuineChern.isInvertible_pullback _ L

omit [IsSeparated sZ] [IsSeparated sB] in
/-- **Composition with `c₁(pr₂^*ℒ)^s ∩ [Γ_g]`.** For `g : B ⟶ A` flat of relative dimension `t`
with `e = d + t` and `u ∈ CH_{d-r}(Z × A)`,

  `(c₁(pr₂^*ℒ)^s ∩ [Γ_g]) ∘ u = c₁(pr₂^*ℒ)^s ∩ (1 × g)^* u`   in   `CH_{e-(r+s)}(Z × B)`,

the composition being that of the canonical family of diagonal classes. -/
theorem compositionInt_capPow_graph (hdeg : (e : ℤ) = d + t) (r : ℤ) (s : ℕ)
    (u : chowGroup 𝒞 (prodBase sZ sA) ((d : ℤ) - r)) :
    compositionInt k sZ sA sB (canonicalDiagonalClassFamily k) hZ hA hB r s u
        (capPow 𝒞 (prodBase sA sB) (invCap 𝒞 (prodBase sA sB)
            ((Scheme.Modules.pullback (pullback.snd sA sB)).obj L)) s ((e : ℤ) - 0)
          ((e : ℤ) - s) (by omega)
          (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme 𝒞 (prodBase sA sB)
            (graphMorphism sA sB g hg) ((e : ℤ) - 0)))) =
      capPow 𝒞 (prodBase sZ sB) (invCap 𝒞 (prodBase sZ sB)
          ((Scheme.Modules.pullback (pullback.snd sZ sB)).obj L)) s ((d : ℤ) - r + t)
        ((e : ℤ) - (r + s)) (by omega)
        (flatPullbackChowOfRelativeDimension 𝒞 (prodBase sZ sB) (prodBase sZ sA)
          (prodMapRight sZ sA sB g hg) (prodMapRight_comp_prodBase sZ sA sB g hg) t
          (relativeDimension_prodMapRight sZ sA sB g hg ht) ((d : ℤ) - r) u) := by
  have hW := relativeDimension_tripleBase k sZ sA sB hZ hA hB
  set P := flatPullbackChow 𝒞 (tripleBase sZ sA sB) (prodBase sZ sA) (pr₁₂ sZ sA sB)
    (pr₁₂_comp_prodBase sZ sA sB) e (relativeDimension_pr₁₂ k sZ sA sB hB) _
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) u
  have hunf : ∀ c, compositionInt k sZ sA sB (canonicalDiagonalClassFamily k) hZ hA hB r s u c =
      properChowPushforward 𝒞 (tripleBase sZ sA sB) (prodBase sZ sB) (pr₁₃ sZ sA sB)
        (pr₁₃_comp_prodBase sZ sA sB) ((e : ℤ) - (r + s)) (properPushforwardDescends _ _ _ _ _ _)
        (chowGroupDegreeEquiv 𝒞 (tripleBase sZ sA sB) (by push_cast; ring)
          (selfIntersectionProduct 𝒞
            (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
            (fieldGysinSystem k) (tripleBase sZ sA sB) _
            (canonicalDiagonalClassFamily k _ _ hW) (((d : ℤ) - r) + e) (((e : ℤ) - s) + f)
            P
            (flatPullbackChow 𝒞 (tripleBase sZ sA sB) (prodBase sA sB) (pr₂₃ sZ sA sB)
              (pr₂₃_comp_prodBase sZ sA sB) f (relativeDimension_pr₂₃ k sZ sA sB hZ) _
              (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) c))) :=
    fun _ ↦ rfl
  rw [hunf]
  have hgys : (fieldGysinSystem k).IsNaturalUnderBaseChangeIso :=
    gysinSystemOfInvertible_isNaturalUnderBaseChangeIso 𝒞
  have hZA := relativeDimension_prodBase k sZ sA hZ hA
  -- `u = a ∩ [Z × A]` (Stacks 0FC2)
  obtain ⟨a, ha⟩ := capFundamentalClassSurjective k (prodBase sZ sA) (d + f) hZA ((f : ℤ) + r)
    (chowGroupDegreeEquiv 𝒞 (prodBase sZ sA)
      (by push_cast; ring : (d : ℤ) - r = ((d + f : ℕ) : ℤ) - (f + r)) u)
  have hau : chowCohomologyCapFundamentalClass 𝒞 (fieldGysinSystem k) (prodBase sZ sA) (d + f)
      ((f : ℤ) + r) a ≍ u :=
    (heq_of_eq ha).trans (chowGroupDegreeEquiv_heq _ _ _ _)
  set ra := chowCohomologyRestrictionOfEq 𝒞 (tripleBase sZ sA sB) (prodBase sZ sA)
    (pr₁₂_comp_prodBase sZ sA sB) (fieldGysinSystem k) hgys ((f : ℤ) + r) a with hra
  -- `pr₁₂^* u = res(a) ∩ [W]`
  have h12 : P ≍
      chowCohomologyCapFundamentalClass 𝒞 (fieldGysinSystem k) (tripleBase sZ sA sB)
        ((e + (d + f) : ℕ) : ℤ) ((f : ℤ) + r) ra :=
    (flatPullbackChow_heq_of_heq _ _ _ _ _ _ (by ring) _ _ hau.symm).trans
      (flatPullbackChow_chowCohomologyCapFundamentalClass' (prodBase sZ sA)
        (tripleBase sZ sA sB) (pr₁₂ sZ sA sB) (pr₁₂_comp_prodBase sZ sA sB)
        (relativeDimension_pr₁₂ k sZ sA sB hB) hZA ((f : ℤ) + r) a)
  -- the second factor: `pr₂₃^*(ξ^s ∩ Γ_*[B]) = j_*(ξ^s ∩ [Z × B])`
  set Γ := graphMorphism sA sB g hg with hΓ
  set j := graphSection sZ sA sB g hg with hj
  have hΓs : Γ ≫ prodBase sA sB = sB := by
    rw [hΓ, prodBase, ← Category.assoc, graphMorphism_fst, hg]
  have hj₃ : j ≫ tripleBase sZ sA sB = prodBase sZ sB := graphSection_comp_tripleBase sZ sA sB g hg
  have hsnd : pullback.snd sZ sB ≫ Γ ≫ prodBase sA sB = prodBase sZ sB := by
    rw [hΓs, prodBase, pullback.condition]
  have : IsClosedImmersion j :=
    MorphismProperty.of_isPullback (isPullback_graphSection sZ sA sB g hg) inferInstance
  set LAB := (Scheme.Modules.pullback (pullback.snd sA sB)).obj L with hLAB
  set LW := (Scheme.Modules.pullback (pr₂₃ sZ sA sB)).obj LAB with hLW
  have : SheafOfModules.IsInvertible (tripleProduct sZ sA sB).sheaf.obj
      (tripleProduct sZ sA sB).ringCatSheaf.property LW := GenuineChern.isInvertible_pullback _ _
  have : SheafOfModules.IsInvertible (Limits.pullback sZ sB).sheaf.obj
      (Limits.pullback sZ sB).ringCatSheaf.property ((Scheme.Modules.pullback j).obj LW) :=
    GenuineChern.isInvertible_pullback _ _
  have hΓmk : (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme 𝒞 (prodBase sA sB) Γ
      ((e : ℤ) - 0)) : chowGroup 𝒞 (prodBase sA sB) ((e : ℤ) - 0)) =
      properChowPushforward 𝒞 (Γ ≫ prodBase sA sB) (prodBase sA sB) Γ rfl ((e : ℤ) - 0)
        (properPushforwardDescends _ _ _ _ _ _)
        (fundamentalChowClass 𝒞 (Γ ≫ prodBase sA sB) ((e : ℤ) - 0)) :=
    (properChowPushforward_fundamentalChowClass_eq_mk (prodBase sA sB) Γ _).symm
  set β := flatPullbackChow 𝒞 (tripleBase sZ sA sB) (prodBase sA sB) (pr₂₃ sZ sA sB)
      (pr₂₃_comp_prodBase sZ sA sB) f (relativeDimension_pr₂₃ k sZ sA sB hZ) ((e : ℤ) - s)
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
      (capPow 𝒞 (prodBase sA sB) (invCap 𝒞 (prodBase sA sB) LAB) s ((e : ℤ) - 0)
        ((e : ℤ) - s) (by omega)
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme 𝒞 (prodBase sA sB) Γ
          ((e : ℤ) - 0))))
  set Y := capPow 𝒞 (prodBase sZ sB) (invCap 𝒞 (prodBase sZ sB)
    ((Scheme.Modules.pullback j).obj LW)) s ((e : ℤ) - 0 + f) ((e : ℤ) - s + f) (by omega)
    (fundamentalChowClass 𝒞 (prodBase sZ sB) ((e : ℤ) - 0 + f))
  have hsecond : β = properChowPushforward 𝒞 (prodBase sZ sB) (tripleBase sZ sA sB) j hj₃
      ((e : ℤ) - s + f) (properPushforwardDescends _ _ _ _ _ _) Y := by
    have h1 := flatPullbackChowOfRelativeDimension_capPow 𝒞 (tripleBase sZ sA sB)
      (prodBase sA sB) (pr₂₃ sZ sA sB) (pr₂₃_comp_prodBase sZ sA sB) f
      (relativeDimension_pr₂₃ k sZ sA sB hZ) LAB s ((e : ℤ) - 0) ((e : ℤ) - s) (by omega)
      (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme 𝒞 (prodBase sA sB) Γ
        ((e : ℤ) - 0)))
    refine h1.trans ?_
    rw [hΓmk]
    have h2 := flatPullbackChow_properChowPushforward_of_isProper 𝒞 (Γ ≫ prodBase sA sB)
      (prodBase sA sB) (prodBase sZ sB) (tripleBase sZ sA sB) Γ (pr₂₃ sZ sA sB)
      (pullback.snd sZ sB) j (isPullback_graphSection sZ sA sB g hg) rfl
      (pr₂₃_comp_prodBase sZ sA sB) hsnd f (relativeDimension_pr₂₃ k sZ sA sB hZ)
      ((e : ℤ) - 0) (fundamentalChowClass 𝒞 (Γ ≫ prodBase sA sB) ((e : ℤ) - 0))
    have h3 := flatPullbackChowOfRelativeDimension_fundamentalChowClass 𝒞 (prodBase sZ sB)
      (Γ ≫ prodBase sA sB) (pullback.snd sZ sB) hsnd f
      (RelativeDimension.of_isPullback (isPullback_graphSection sZ sA sB g hg).flip
        (relativeDimension_pr₂₃ k sZ sA sB hZ)) ((e : ℤ) - 0)
      (by rw [schemeDeltaDimension_congr 𝒞 hΓs]
          simpa using schemeDeltaDimension_le_of_relativeDimension sB hB)
    refine (congrArg (capPow 𝒞 (tripleBase sZ sA sB) (invCap 𝒞 (tripleBase sZ sA sB) LW) s
      ((e : ℤ) - 0 + f) ((e : ℤ) - s + f) (by omega))
      (h2.trans (congrArg (properChowPushforward 𝒞 (prodBase sZ sB) (tripleBase sZ sA sB) j hj₃
        ((e : ℤ) - 0 + f) (properPushforwardDescends _ _ _ _ _ _)) h3))).trans ?_
    exact (properChowPushforward_capPow 𝒞 (prodBase sZ sB) (tripleBase sZ sA sB) j hj₃ LW s _ _
      _ _).symm
  -- the product with `pr₁₂^* u` is capping with `res(a)` (Stacks 0FC2)
  have hcapeq := canonicalDiagonalClassFamily_capEqProduct k (tripleBase sZ sA sB) (e + (d + f))
    hW ((f : ℤ) + r) ra (((e : ℤ) - s) + f) β
  have hμ : selfIntersectionProduct 𝒞
      (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
      (fieldGysinSystem k) (tripleBase sZ sA sB) _ (canonicalDiagonalClassFamily k _ _ hW)
      (((d : ℤ) - r) + e) (((e : ℤ) - s) + f)
      P β ≍
      chowCohomologyCap 𝒞 (fieldGysinSystem k) (tripleBase sZ sA sB) ((f : ℤ) + r) ra
        (((e : ℤ) - s) + f) β :=
    (selfIntersectionProduct_heq_of_heq _ _ _ (by push_cast; ring) rfl h12 HEq.rfl).trans
      ((heq_of_eq hcapeq).trans (chowGroupDegreeEquiv_heq _ _ _ _)).symm
  -- capping with `res(a)` commutes with `j_*` (the projection formula for Chow cohomology)
  set ra' := chowCohomologyRestrictionOfEq 𝒞 (prodBase sZ sB) (tripleBase sZ sA sB) hj₃
    (fieldGysinSystem k) hgys ((f : ℤ) + r) ra with hra'
  have hproj := chowCohomologyCap_properChowPushforward_restriction 𝒞 (fieldGysinSystem k) hgys
    (prodBase sZ sB) (tripleBase sZ sA sB) hj₃ ((f : ℤ) + r) ra (((e : ℤ) - s) + f) Y
  -- `pr₁₃ ∘ j = 1`
  have hpr : ∀ (m : ℤ) (w : chowGroup 𝒞 (prodBase sZ sB) m),
      properChowPushforward 𝒞 (tripleBase sZ sA sB) (prodBase sZ sB) (pr₁₃ sZ sA sB)
        (pr₁₃_comp_prodBase sZ sA sB) m (properPushforwardDescends _ _ _ _ _ _)
        (properChowPushforward 𝒞 (prodBase sZ sB) (tripleBase sZ sA sB) j hj₃ m
          (properPushforwardDescends _ _ _ _ _ _) w) = w := by
    intro m w
    rw [← properChowPushforward_comp_apply 𝒞 _ _ _ j (pr₁₃ sZ sA sB) (𝟙 _)
      (graphSection_pr₁₃ sZ sA sB g hg) hj₃ (pr₁₃_comp_prodBase sZ sA sB) (Category.id_comp _) m
      _ _ (properPushforwardDescends _ _ _ _ _ _), properChowPushforward_id]
    rfl
  -- capping with `res(a)` commutes with `ξ^s ∩ -` (Stacks 0B7B)
  have hcomm := chowCohomologyCap_capPow 𝒞 (prodBase sZ sB) ((Scheme.Modules.pullback j).obj LW)
    ra' s ((e : ℤ) - 0 + f) ((e : ℤ) - s + f) (by omega)
    (fundamentalChowClass 𝒞 (prodBase sZ sB) ((e : ℤ) - 0 + f))
  rw [chowCohomologyCap_fundamentalChowClass] at hcomm
  -- `res_j(res_{pr₁₂}(a)) = res_{1 × g}(a)`
  have hres : ra' = chowCohomologyRestrictionOfEq 𝒞 (prodBase sZ sB) (prodBase sZ sA)
      (prodMapRight_comp_prodBase sZ sA sB g hg) (fieldGysinSystem k) hgys ((f : ℤ) + r) a := by
    rw [hra', hra, chowCohomologyRestrictionOfEq_restrictionOfEq (prodBase sZ sA)
      (tripleBase sZ sA sB) (prodBase sZ sB) (pr₁₂ sZ sA sB) j (pr₁₂_comp_prodBase sZ sA sB) hj₃
      (by rw [Category.assoc, pr₁₂_comp_prodBase, hj₃])]
    exact Stacks.Chow.chowCohomologyRestrictionOfEq_congr (prodBase sZ sA) (prodBase sZ sB)
      (graphSection_pr₁₂ sZ sA sB g hg) _ _ _ _
  -- `res_{1 × g}(a) ∩ [Z × B] = (1 × g)^* u`
  have hq := flatPullbackChow_chowCohomologyCapFundamentalClass' (prodBase sZ sA)
    (prodBase sZ sB) (prodMapRight sZ sA sB g hg) (prodMapRight_comp_prodBase sZ sA sB g hg)
    (relativeDimension_prodMapRight sZ sA sB g hg ht) hZA ((f : ℤ) + r) a
  -- the module `j^*pr₂₃^*pr₂^*ℒ` is `pr₂^*ℒ`
  have hjs : j ≫ pr₂₃ sZ sA sB ≫ pullback.snd sA sB = pullback.snd sZ sB := by
    rw [← Category.assoc, graphSection_pr₂₃, Category.assoc, graphMorphism_snd, Category.comp_id]
  have eL : (Scheme.Modules.pullback j).obj LW ≅
      (Scheme.Modules.pullback (pullback.snd sZ sB)).obj L :=
    (Scheme.Modules.pullback j).mapIso ((Scheme.Modules.pullbackComp (pr₂₃ sZ sA sB)
        (pullback.snd sA sB)).app L) ≪≫
      (Scheme.Modules.pullbackComp j (pr₂₃ sZ sA sB ≫ pullback.snd sA sB)).app L ≪≫
      (Scheme.Modules.pullbackCongr hjs).app L
  refine eq_of_heq ?_
  refine (properChowPushforward_heq_congr 𝒞 _ _ _ _ (by ring) _
    (properPushforwardDescends _ _ _ _ _ _) _ _
    ((chowGroupDegreeEquiv_heq _ _ _ _).trans hμ)).trans ?_
  rw [hsecond, hproj, hpr, hcomm, GenuineChern.capPow_invCap_congr 𝒞 (prodBase sZ sB) eL]
  refine capPow_heq_of_heq 𝒞 _ _ s _ _ (by omega) (by ring) ?_
  rw [hres]
  exact (chowCohomologyCapFundamentalClass_heq_of_eq _ (by push_cast; omega) _ _).trans
    (hq.symm.trans (flatPullbackChow_heq_of_heq _ _ _ _ _ _ (by push_cast; ring) _ _ hau))

omit [IsSeparated sZ] [IsSeparated sB] in
/-- **Composition with `c₁(pr₂^*ℒ)^s ∩ [V]`** for a closed subscheme `γ : V ⟶ A × B` mapping
isomorphically to `B`: then `V` is the graph of `g = (γ ≫ pr₂)⁻¹ ≫ γ ≫ pr₁ : B ⟶ A`, and for `g`
flat of relative dimension `t` with `e = d + t` and `u ∈ CH_{d-r}(Z × A)`,

  `(c₁(pr₂^*ℒ)^s ∩ [V]) ∘ u = c₁(pr₂^*ℒ)^s ∩ (1 × g)^* u`   in   `CH_{e-(r+s)}(Z × B)`. -/
theorem compositionInt_capPow_closedImmersion (hdeg : (e : ℤ) = d + t) (r : ℤ) (s : ℕ)
    {V : Scheme.{u}} (γ : V ⟶ Limits.pullback sA sB) [IsClosedImmersion γ]
    [IsIso (γ ≫ pullback.snd sA sB)]
    (hγ : γ ≫ pullback.fst sA sB = (γ ≫ pullback.snd sA sB) ≫ g)
    (u : chowGroup 𝒞 (prodBase sZ sA) ((d : ℤ) - r)) :
    compositionInt k sZ sA sB (canonicalDiagonalClassFamily k) hZ hA hB r s u
        (capPow 𝒞 (prodBase sA sB) (invCap 𝒞 (prodBase sA sB)
            ((Scheme.Modules.pullback (pullback.snd sA sB)).obj L)) s ((e : ℤ) - 0)
          ((e : ℤ) - s) (by omega)
          (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme 𝒞 (prodBase sA sB) γ
            ((e : ℤ) - 0)))) =
      capPow 𝒞 (prodBase sZ sB) (invCap 𝒞 (prodBase sZ sB)
          ((Scheme.Modules.pullback (pullback.snd sZ sB)).obj L)) s ((d : ℤ) - r + t)
        ((e : ℤ) - (r + s)) (by omega)
        (flatPullbackChowOfRelativeDimension 𝒞 (prodBase sZ sB) (prodBase sZ sA)
          (prodMapRight sZ sA sB g hg) (prodMapRight_comp_prodBase sZ sA sB g hg) t
          (relativeDimension_prodMapRight sZ sA sB g hg ht) ((d : ℤ) - r) u) := by
  rw [cycleAssociatedToClosedSubscheme_eq_of_iso 𝒞 (prodBase sA sB) γ (graphMorphism sA sB g hg)
    (asIso (γ ≫ pullback.snd sA sB)) (by apply pullback.hom_ext <;> simp [hγ])]
  exact compositionInt_capPow_graph sZ sA sB hZ hA hB g hg ht L hdeg r s u

end Composition

end Stacks.WeilCohomology

end
