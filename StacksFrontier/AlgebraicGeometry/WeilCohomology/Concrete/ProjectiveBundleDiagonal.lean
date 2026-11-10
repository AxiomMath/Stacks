module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.SectionClass
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.CapPowCommute
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection.RestrictedSection
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceComparison
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.GysinChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleProper
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalFlat
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GraphAction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionRegularImmersionProduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The class of the diagonal of a projective bundle

Let `k` be a field, `X` a smooth projective scheme over `k`, `ℰ` a finite locally free
`𝒪_X`-module of rank `r = n + 1` and `p : P = 𝐏(ℰ) ⟶ X` its projective bundle, with `𝒪_P(1)`
normalized so that `p_*𝒪_P(1) = ℰ`. Let `𝒮` be the kernel of the tautological surjection
`p^*ℰ ⟶ 𝒪_P(1)`. [Stacks, Tag 0FGR] asserts that the class of the diagonal of `P` is

  `[Δ_P] = (∑_{i = 0}^{r - 1} c_{r-1-i}(pr₁^*𝒮^∨) ∩ c₁(pr₂^*𝒪_P(1))^i) ∩ (p × p)^*[Δ_X]`

in `CH^*(P × P)`. Here it is proved for every `X` smooth and separated over `k`, in each
dimension: for every `m`, the `(m + n)`-dimensional part `[Δ_P]_{m+n}` of the cycle of the
diagonal is the sum over `i` of `c_{n-i}(pr₁^*𝒮^∨) ∩ c₁(pr₂^*𝒪_P(1))^i ∩ (p × p)^*[Δ_X]_m`, where
`(p × p)^*` is flat pullback, of relative dimension `2n`. The class `[Δ_P] = ∑_m [Δ_P]_m` of the
source is the sum of these.

## The proof

The source's proof: `(p × p)^*[Δ_X] = [P ×_X P]`, and by Stacks 02U9 it suffices to compute the
class of `Δ_P ⊂ P ×_X P`, which is the top Chern class of `q₁^*𝒮^∨ ⊗ q₂^*𝒪_P(1)` (Stacks 0FA9),
expanded by Stacks 02UD. Here the last two steps are replaced by the computation
`Stacks.Chow.GenuineChern.properChowPushforward_section_eq_sum` of the class of a section of a
projective bundle, applied to `q₂ : P ×_X P ⟶ P`, the base change of `p` along `p`, whose
tautological sequence is the pullback along `q₁` of that of `p`, and to the diagonal
`P ⟶ P ×_X P`, a section of `q₂`. The identity `(p × p)^*[Δ_X] = j_*[P ×_X P]` for
`j : P ×_X P ⟶ P × P` is Stacks 02RG for the cartesian square formed by `j`, `Δ_X` and `p × p`
together with `q^*[X]_m = [P ×_X P]_{m+2n}` for `q : P ×_X P ⟶ X`; the latter is Stacks 02RE on
each part of `X` of constant dimension.

## Main results

* `Stacks.WeilCohomology.flatPullbackChow_fundamentalChowClass_of_smooth`: `f^*[X]_m = [Y]_{m+r}`
  for `f : Y ⟶ X` flat of relative dimension `r` and `X` smooth over `k`, with no bound on the
  dimension of `X`.
* `Stacks.WeilCohomology.diagonal_projectiveBundle_eq_sum`: **Stacks 0FGR**.

## References

* [Stacks Project, Tag 0FGR](https://stacks.math.columbia.edu/tag/0FGR)
* [Stacks Project, Tag 0FGQ](https://stacks.math.columbia.edu/tag/0FGQ)
* [Stacks Project, Tag 02U9](https://stacks.math.columbia.edu/tag/02U9)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)

universe u

namespace Stacks.WeilCohomology

/-! ### Flat pullback of the fundamental class of a smooth scheme -/

/-- If `q = f ≫ g` with `f` flat of relative dimension `r` and `g` of relative dimension `s`,
then `q` has relative dimension `r + s`. -/
private theorem relativeDimension_of_eq_comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {q : X ⟶ Z} [LocallyOfFiniteType q] [LocallyOfFiniteType f] [Flat f] [LocallyOfFiniteType g]
    {r s : ℕ} (hf : RelativeDimension f r) (hg : RelativeDimension g s) (e : q = f ≫ g) :
    RelativeDimension q (r + s) := by
  subst e
  exact RelativeDimension.comp_of_flat _ _ hf hg

/-- `f_d : Y_d ⟶ X_d` is locally of finite type, being a base change of `f`. -/
private theorem locallyOfFiniteType_dimPartOverHom {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] (f : Y ⟶ X) [LocallyOfFiniteType f] (d : ℕ) :
    LocallyOfFiniteType (dimPartOverHom sX f d) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict f _).flip inferInstance

/-- `f_d : Y_d ⟶ X_d` is flat, being a base change of `f`. -/
private theorem flat_dimPartOverHom {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] (f : Y ⟶ X) [Flat f] (d : ℕ) :
    Flat (dimPartOverHom sX f d) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict f _).flip inferInstance

/-- `f_d : Y_d ⟶ X_d` has the same relative dimension as `f`. -/
private theorem relativeDimension_dimPartOverHom {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] (f : Y ⟶ X) [LocallyOfFiniteType f]
    {r : ℕ} (hr : RelativeDimension f r) (d : ℕ) [LocallyOfFiniteType (dimPartOverHom sX f d)] :
    RelativeDimension (dimPartOverHom sX f d) r :=
  RelativeDimension.of_isPullback (isPullback_morphismRestrict f _).flip hr

section FundamentalClass

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX]
  (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sY] (f : Y ⟶ X)
  [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sX = sY) (r : ℕ) (hr : RelativeDimension f r)

include hf in
/-- On the part `Y_d = f⁻¹(X_d)` over the part of `X` of dimension `d`, the restriction of `f^*α`
is the flat pullback of the restriction of `α` along `f_d : Y_d ⟶ X_d` (Stacks 02RD). -/
theorem chowGroupRestrict_flatPullbackChow_heq (d : ℕ) (m : ℤ)
    (α : chowGroup (fieldChowSituation k) sX m) :
    letI : LocallyOfFiniteType (dimPartOverHom sX f d) :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict f _).flip inferInstance
    letI : Flat (dimPartOverHom sX f d) :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict f _).flip inferInstance
    chowGroupRestrict (fieldChowSituation k) sY ((dimPartOver sX f d).ι ≫ sY)
        (dimPartOver sX f d).ι rfl (m + r)
        (flatPullbackChowOfRelativeDimension (fieldChowSituation k) sY sX f hf r hr m α) ≍
      flatPullbackChowOfRelativeDimension (fieldChowSituation k) ((dimPartOver sX f d).ι ≫ sY)
        (partBase sX d) (dimPartOverHom sX f d)
        (by rw [dimPartOverHom_comp_partBase, hf]) r
        (RelativeDimension.of_isPullback (isPullback_morphismRestrict f _).flip hr) m
        (chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl m α) := by
  have := locallyOfFiniteType_dimPartOverHom sX f d
  have := flat_dimPartOverHom sX f d
  have hfd := relativeDimension_dimPartOverHom sX f hr d
  have h1 := heq_chowGroupRestrict_flatPullbackChow (fieldChowSituation k) sY
    ((dimPartOver sX f d).ι ≫ sY) (dimPartOver sX f d).ι rfl
    (relativeDimension_of_isOpenImmersion (dimPartOver sX f d).ι) (m + r)
    (flatPullbackDescends _ _ _ _ _ _ _ _)
    (flatPullbackChowOfRelativeDimension (fieldChowSituation k) sY sX f hf r hr m α)
  have h2 := flatPullbackChow_comp (fieldChowSituation k) ((dimPartOver sX f d).ι ≫ sY) sY sX
    (dimPartOver sX f d).ι f rfl hf 0 r
    (relativeDimension_of_isOpenImmersion (dimPartOver sX f d).ι) hr m
    (flatPullbackDescends _ _ _ _ _ _ _ _) (flatPullbackDescends _ _ _ _ _ _ _ _)
    (flatPullbackDescends _ _ _ _ _ _ _ _) α
  have hcomm : (dimPartOver sX f d).ι ≫ f = dimPartOverHom sX f d ≫ (dimPart sX d).ι :=
    (morphismRestrict_ι f _).symm
  have h3 : ∀ (g g' : (dimPartOver sX f d).toScheme ⟶ X) [LocallyOfFiniteType g] [Flat g]
      [LocallyOfFiniteType g'] [Flat g'] (e : g = g') (hg : g ≫ sX = (dimPartOver sX f d).ι ≫ sY)
      (hg' : g' ≫ sX = (dimPartOver sX f d).ι ≫ sY) {s s' : ℕ} (es : s = s')
      (hs : RelativeDimension g s) (hs' : RelativeDimension g' s'),
      flatPullbackChowOfRelativeDimension (fieldChowSituation k) ((dimPartOver sX f d).ι ≫ sY) sX
          g hg s hs m α ≍
        flatPullbackChowOfRelativeDimension (fieldChowSituation k) ((dimPartOver sX f d).ι ≫ sY)
          sX g' hg' s' hs' m α := by
    intro g g' _ _ _ _ e hg hg' s s' es hs hs'
    subst e es
    rfl
  have h4 := flatPullbackChow_comp (fieldChowSituation k) ((dimPartOver sX f d).ι ≫ sY)
    (partBase sX d) sX (dimPartOverHom sX f d) (dimPart sX d).ι
    (by rw [dimPartOverHom_comp_partBase, hf]) rfl r 0 hfd
    (relativeDimension_of_isOpenImmersion _) m (flatPullbackDescends _ _ _ _ _ _ _ _)
    (flatPullbackDescends _ _ _ _ _ _ _ _) (flatPullbackDescends _ _ _ _ _ _ _ _) α
  have h5 := heq_chowGroupRestrict_flatPullbackChow (fieldChowSituation k) sX (partBase sX d)
    (dimPart sX d).ι rfl (relativeDimension_of_isOpenImmersion _) m
    (flatPullbackDescends _ _ _ _ _ _ _ _) α
  refine h1.trans (h2.trans ((h3 _ _ hcomm _ _ (by omega) _ _).trans (h4.symm.trans ?_)))
  have h6 : ∀ {a a' : ℤ} (e : a = a') {x : chowGroup (fieldChowSituation k) (partBase sX d) a}
      {x' : chowGroup (fieldChowSituation k) (partBase sX d) a'}, x ≍ x' →
      flatPullbackChowOfRelativeDimension (fieldChowSituation k) ((dimPartOver sX f d).ι ≫ sY)
          (partBase sX d) (dimPartOverHom sX f d) (by rw [dimPartOverHom_comp_partBase, hf]) r
          hfd a x ≍
        flatPullbackChowOfRelativeDimension (fieldChowSituation k) ((dimPartOver sX f d).ι ≫ sY)
          (partBase sX d) (dimPartOverHom sX f d) (by rw [dimPartOverHom_comp_partBase, hf]) r
          hfd a' x' := by
    intro a a' e x x' hx
    subst e
    cases hx
    rfl
  exact h6 (by simp) h5.symm

include hf in
/-- **Flat pullback of the fundamental class of a smooth scheme over a field.** For `X` smooth
over `k` and `f : Y ⟶ X` flat of relative dimension `r`, `f^*[X]_m = [Y]_{m+r}` in every degree
`m`, with no bound on the dimension of `X`. On the part `Y_d = f⁻¹(X_d)` lying over the part of
`X` of dimension `d` this is Stacks 02RE for `X_d` when `d = m`, and both sides vanish otherwise,
`X_d` and `Y_d` being equidimensional of dimensions `d` and `d + r`. -/
theorem flatPullbackChow_fundamentalChowClass_of_smooth (m : ℤ) :
    flatPullbackChowOfRelativeDimension (fieldChowSituation k) sY sX f hf r hr m
        (fundamentalChowClass (fieldChowSituation k) sX m) =
      fundamentalChowClass (fieldChowSituation k) sY (m + r) := by
  have hdec : IsClopenDecomposition fun d : ULift.{u} ℕ ↦
      (dimPartOver sX f d.down).ι.opensRange := by
    have h := ((isClopenDecomposition_dimPart sX).preimage f).opensRange_ι_equiv Equiv.ulift
    simpa only [Scheme.Opens.opensRange_ι, Equiv.ulift_apply] using h
  apply (chowGroupClopenRestrictEquiv (fieldChowSituation k) sY
    (fun d : ULift.{u} ℕ ↦ (dimPartOver sX f d.down).ι ≫ sY)
    (fun d : ULift.{u} ℕ ↦ (dimPartOver sX f d.down).ι) (fun _ ↦ rfl) hdec (m + r)).injective
  funext ⟨d⟩
  simp only [chowGroupClopenRestrictEquiv_apply]
  rw [chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion]
  have := locallyOfFiniteType_dimPartOverHom sX f d
  have := flat_dimPartOverHom sX f d
  have hfd := relativeDimension_dimPartOverHom sX f hr d
  have hres := chowGroupRestrict_flatPullbackChow_heq sX sY f hf r hr d m
    (fundamentalChowClass (fieldChowSituation k) sX m)
  rw [chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion] at hres
  refine eq_of_heq (hres.trans ?_)
  by_cases hdm : (d : ℤ) = m
  · subst hdm
    exact heq_of_eq (flatPullbackChow_fundamentalChowClass (fieldChowSituation k) _ _ _ _ r hfd _ _
      (schemeDeltaDimension_le_of_relativeDimension (partBase sX d)
        (relativeDimension_partBase sX d)))
  · -- `X_d` is equidimensional of dimension `d ≠ m`, and `Y_d` of dimension `d + r ≠ m + r`
    have hX0 : fundamentalChowClass (fieldChowSituation k) (partBase sX d) m = 0 := by
      have hY : RelativeDimension (𝟙 _ ≫ partBase sX d) d := by
        simpa using relativeDimension_partBase sX d
      rw [fundamentalChowClass, fundamentalCycle,
        cycleAssociatedToClosedSubscheme_eq_zero_of_relativeDimension (k := k) (partBase sX d)
          (𝟙 _) hY (Ne.symm hdm), map_zero]
    have hY0 :
        fundamentalChowClass (fieldChowSituation k) ((dimPartOver sX f d).ι ≫ sY) (m + r) = 0 := by
      have hYd : RelativeDimension (𝟙 _ ≫ (dimPartOver sX f d).ι ≫ sY) (r + d) :=
        relativeDimension_of_eq_comp hfd (relativeDimension_partBase sX d)
          (by rw [Category.id_comp, dimPartOverHom_comp_partBase, hf])
      rw [fundamentalChowClass, fundamentalCycle,
        cycleAssociatedToClosedSubscheme_eq_zero_of_relativeDimension (k := k)
          ((dimPartOver sX f d).ι ≫ sY) (𝟙 _) hYd (by push_cast; omega), map_zero]
    rw [hX0, map_zero, hY0]

end FundamentalClass

/-! ### Chern classes and proper pushforward -/

section ChernPushforward

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sY]

/-- **Stacks 02U9 for the total Chern class.** For `g : X ⟶ Y` proper, `ℰ` of rank `r` on `Y` and
`ℰ' ≅ g^*ℰ`, `c_i(ℰ) ∩ g_*α = g_*(c_i(ℰ') ∩ α)` for every `i`, both sides vanishing above the
rank. -/
theorem chernFamily_properChowPushforward (g : X ⟶ Y) [IsProper g] (hg : g ≫ sY = sX)
    (F : Y.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (F' : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' r]
    (eF : F' ≅ (Scheme.Modules.pullback g).obj F) (a : ℤ) (i : ℕ)
    (α : chowGroup (fieldChowSituation k) sX a) :
    GenuineChern.chernFamily (fieldChowSituation k) sY F r a i
        (properChowPushforward (fieldChowSituation k) sX sY g hg a
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ sX sY g hg a) α) =
      properChowPushforward (fieldChowSituation k) sX sY g hg (a - i)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ sX sY g hg _)
        (GenuineChern.chernFamily (fieldChowSituation k) sX F' r a i α) := by
  by_cases hi : i ≤ r
  · simp only [GenuineChern.chernFamily,
      chernCapFamilyOnChow_of_le (fieldChowSituation k) (GenuineChern.chernCap _) _ _ r a hi]
    exact GenuineChern.chernCap_properPushforward _ sX sY g hg F r F' eF a ⟨i, by omega⟩ _ _ α
  · simp only [GenuineChern.chernFamily,
      chernCapFamilyOnChow_of_gt (fieldChowSituation k) (GenuineChern.chernCap _) _ _ r a hi,
      AddMonoidHom.zero_apply, map_zero]

end ChernPushforward

/-! ### The product `p × p` and the fibre product `P ×_X P` -/

section Products

variable {S X P : Scheme.{u}} (sX : X ⟶ S) (p : P ⟶ X)

/-- The morphism `p × 1 : P × X ⟶ X × X`. -/
abbrev prodMapLeft : Limits.pullback (p ≫ sX) sX ⟶ Limits.pullback sX sX :=
  pullback.map (p ≫ sX) sX sX sX p (𝟙 X) (𝟙 S) (Category.comp_id _) (by simp)

/-- `P × X` is the base change of `X × X` along `p`, through the first projections. -/
theorem isPullback_prodMapLeft :
    IsPullback (prodMapLeft sX p) (pullback.fst (p ≫ sX) sX) (pullback.fst sX sX) p := by
  refine IsPullback.of_right (h₁₂ := pullback.snd sX sX) (v₁₃ := sX) (h₂₂ := sX) ?_
    (by simp [prodMapLeft]) (IsPullback.of_hasPullback sX sX).flip
  have h1 : prodMapLeft sX p ≫ pullback.snd sX sX = pullback.snd (p ≫ sX) sX := by
    simp [prodMapLeft]
  rw [h1]
  exact (IsPullback.of_hasPullback (p ≫ sX) sX).flip

/-- `p × p : P × P ⟶ X × X` is `(1 × p) ≫ (p × 1)`. -/
theorem prodMap_eq_comp :
    pullback.map (p ≫ sX) (p ≫ sX) sX sX p p (𝟙 S) (Category.comp_id _) (Category.comp_id _) =
      prodMapRight (p ≫ sX) sX (p ≫ sX) p rfl ≫ prodMapLeft sX p := by
  apply pullback.hom_ext <;> simp [prodMapLeft]

/-- `1 × p : P × P ⟶ P × X` is flat if `p` is. -/
private theorem flat_prodMapRight [Flat p] : Flat (prodMapRight (p ≫ sX) sX (p ≫ sX) p rfl) :=
  MorphismProperty.of_isPullback (isPullback_prodMapRight _ _ _ _ rfl).flip inferInstance

/-- `1 × p : P × P ⟶ P × X` is locally of finite type if `p` is. -/
private theorem locallyOfFiniteType_prodMapRight [LocallyOfFiniteType p] :
    LocallyOfFiniteType (prodMapRight (p ≫ sX) sX (p ≫ sX) p rfl) :=
  MorphismProperty.of_isPullback (isPullback_prodMapRight _ _ _ _ rfl).flip inferInstance

/-- `p × 1 : P × X ⟶ X × X` is locally of finite type if `p` is. -/
private theorem locallyOfFiniteType_prodMapLeft [LocallyOfFiniteType p] :
    LocallyOfFiniteType (prodMapLeft sX p) :=
  MorphismProperty.of_isPullback (isPullback_prodMapLeft sX _).flip inferInstance

end Products

section Diagonal

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX]
  [IsSeparated sX] (E : X.Modules) (n : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
  [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

attribute [local instance] AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback

/-- The tautological kernel `𝒮 = ker(p^*ℰ ⟶ 𝒪_P(1))` of the bundle of a module of rank `n + 1` has
rank `n`. -/
@[ega "IV 19.4.11"]
instance instIsFiniteLocallyFreeOfRankKernelBundleTautological :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (kernel (bundleTautological E)) n :=
  isFiniteLocallyFreeOfRank_kernel_bundleTautological E n inferInstance

/-- The dual `𝒮^∨` of the tautological kernel has rank `n`. -/
instance isFiniteLocallyFreeOfRank_dualSheaf_kernel_bundleTautological :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualSheaf (kernel (bundleTautological E)))
      n :=
  Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf _ n
    (instIsFiniteLocallyFreeOfRankKernelBundleTautological E n)

omit [Smooth sX] [IsSeparated sX] in
include n in
/-- `p × p : P × P ⟶ X × X` is flat. -/
theorem flat_bundleProdMap :
    Flat (pullback.map (bundleProj E ≫ sX) (bundleProj E ≫ sX) sX sX (bundleProj E) (bundleProj E)
      (𝟙 _) (Category.comp_id _) (Category.comp_id _)) := by
  let := flat_bundleProj E n
  let := locallyOfFiniteType_bundleProj E n
  have := flat_prodMapRight sX (bundleProj E)
  have : Flat (prodMapLeft sX (bundleProj E)) :=
    MorphismProperty.of_isPullback (isPullback_prodMapLeft sX _).flip inferInstance
  rw [prodMap_eq_comp]
  infer_instance

omit [Smooth sX] [IsSeparated sX] in
include n in
/-- `p × p : P × P ⟶ X × X` is locally of finite type. -/
theorem locallyOfFiniteType_bundleProdMap :
    LocallyOfFiniteType (pullback.map (bundleProj E ≫ sX) (bundleProj E ≫ sX) sX sX (bundleProj E)
      (bundleProj E) (𝟙 _) (Category.comp_id _) (Category.comp_id _)) := by
  let := locallyOfFiniteType_bundleProj E n
  have := locallyOfFiniteType_prodMapRight sX (bundleProj E)
  have := locallyOfFiniteType_prodMapLeft sX (bundleProj E)
  rw [prodMap_eq_comp]
  infer_instance

omit [Smooth sX] [IsSeparated sX] in
/-- `p × p` has relative dimension `n + n`. -/
theorem relativeDimension_bundleProdMap :
    letI := locallyOfFiniteType_bundleProdMap sX E n
    RelativeDimension (pullback.map (bundleProj E ≫ sX) (bundleProj E ≫ sX) sX sX (bundleProj E)
      (bundleProj E) (𝟙 _) (Category.comp_id _) (Category.comp_id _)) (n + n) := by
  let := flat_bundleProj E n
  let := locallyOfFiniteType_bundleProj E n
  have := flat_prodMapRight sX (bundleProj E)
  have := locallyOfFiniteType_prodMapRight sX (bundleProj E)
  have := locallyOfFiniteType_prodMapLeft sX (bundleProj E)
  have := locallyOfFiniteType_bundleProdMap sX E n
  exact relativeDimension_of_eq_comp
    (RelativeDimension.of_isPullback (isPullback_prodMapRight _ _ _ _ rfl).flip
      (relativeDimension_bundleProj E n))
    (RelativeDimension.of_isPullback (isPullback_prodMapLeft sX _).flip
      (relativeDimension_bundleProj E n))
    (prodMap_eq_comp sX _)

omit [Smooth sX] [IsSeparated sX] in
/-- `p × p : P × P ⟶ X × X` commutes with the structure morphisms to the base field. -/
theorem bundleProdMap_comp_prodBase :
    pullback.map (bundleProj E ≫ sX) (bundleProj E ≫ sX) sX sX (bundleProj E) (bundleProj E)
        (𝟙 _) (Category.comp_id _) (Category.comp_id _) ≫ prodBase sX sX =
      prodBase (bundleProj E ≫ sX) (bundleProj E ≫ sX) := by
  simp [prodBase]

/-- **Stacks 0FGR.** Let `X` be smooth and separated over a field `k` (for instance smooth
projective, as in Lemma 0FGQ), `ℰ` a finite locally free `𝒪_X`-module of rank `r = n + 1`,
`p : P = 𝐏(ℰ) ⟶ X` its projective bundle with `𝒪_P(1)` normalized so that `p_*𝒪_P(1) = ℰ`
(`Stacks.Chow.bundle`, `Stacks.Chow.bundleTwist`), and `𝒮` the kernel of the canonical surjection
`p^*ℰ ⟶ 𝒪_P(1)`. Then the class of the diagonal of `P` in the Chow groups of `P × P` is

  `[Δ_P] = (∑_{i = 0}^{r - 1} c_{r-1-i}(pr₁^*𝒮^∨) ∩ c₁(pr₂^*𝒪_P(1))^i) ∩ (p × p)^*[Δ_X]`,

with integer coefficients. The identity is stated dimension by dimension, which is the whole of
it since `[Δ_P] = ∑_m [Δ_P]_m`: for every `m`, the part of dimension `m + n` of the cycle of the
diagonal `Δ_P ⊂ P ×_k P` is the sum over `i ≤ n` of `c_{n-i}(pr₁^*𝒮^∨) ∩ c₁(pr₂^*𝒪_P(1))^i ∩
(p × p)^*[Δ_X]_m`, where `[Δ_X]_m` is the part of dimension `m` of the cycle of `Δ_X ⊂ X ×_k X`,
`(p × p)^*` is flat pullback (of relative dimension `2n`), `c₁(-)^i ∩` is the `i`-th power of the
first Chern class cap (Stacks 02SO) and `c_j(-) ∩` the Chern class cap of Stacks 02U6.

The tag as printed weights the `i`-th summand by a binomial coefficient `C(r - 1, i)`. Read
literally that is false: for `X = Spec k` and `r = 3` (so `P = 𝐏²`) it gives
`h₁² + 2h₁h₂ + h₂²` for the diagonal class instead of `h₁² + h₁h₂ + h₂²`. The coefficients are
dropped here, which is the identity the source's proof establishes: the diagonal is the zero
scheme of the section of `pr₁^*𝒮^∨ ⊗ pr₂^*𝒪_P(1)`, whose top Chern class expands without them. -/
@[stacks 0FGR]
theorem diagonal_projectiveBundle_eq_sum (m : ℤ) :
    letI := flat_bundleProdMap sX E n
    letI := locallyOfFiniteType_bundleProdMap sX E n
    QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k)
        (prodBase (bundleProj E ≫ sX) (bundleProj E ≫ sX)) (m + n))
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (bundleProj E ≫ sX) (bundleProj E ≫ sX))
          (pullback.diagonal (bundleProj E ≫ sX)) (m + n)) =
      ∑ i : Fin (n + 1), chowGroupCast (fieldChowSituation k)
        (prodBase (bundleProj E ≫ sX) (bundleProj E ≫ sX)) (by have := i.isLt; omega)
        (GenuineChern.chernFamily (fieldChowSituation k)
          (prodBase (bundleProj E ≫ sX) (bundleProj E ≫ sX))
          ((Scheme.Modules.pullback (pullback.fst (bundleProj E ≫ sX) (bundleProj E ≫ sX))).obj
            (dualSheaf (kernel (bundleTautological E)))) n
          (m + ((n + n : ℕ) : ℤ) - (i : ℕ)) (n - i)
          (capPow (fieldChowSituation k) (prodBase (bundleProj E ≫ sX) (bundleProj E ≫ sX))
            (invCap (fieldChowSituation k) (prodBase (bundleProj E ≫ sX) (bundleProj E ≫ sX))
              ((Scheme.Modules.pullback (pullback.snd (bundleProj E ≫ sX) (bundleProj E ≫ sX))).obj
                (bundleTwist E))) i (m + ((n + n : ℕ) : ℤ)) (m + ((n + n : ℕ) : ℤ) - (i : ℕ))
            (by ring)
            (flatPullbackChowOfRelativeDimension (fieldChowSituation k)
              (prodBase (bundleProj E ≫ sX) (bundleProj E ≫ sX)) (prodBase sX sX)
              (pullback.map (bundleProj E ≫ sX) (bundleProj E ≫ sX) sX sX (bundleProj E)
                (bundleProj E) (𝟙 _) (Category.comp_id _) (Category.comp_id _))
              (bundleProdMap_comp_prodBase sX E) (n + n) (relativeDimension_bundleProdMap sX E n) m
              (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) (prodBase sX sX) m)
                (cycleAssociatedToClosedSubscheme (fieldChowSituation k) (prodBase sX sX)
                  (pullback.diagonal sX) m))))) := by
  let := flat_bundleProdMap sX E n
  let := locallyOfFiniteType_bundleProdMap sX E n
  have := flat_bundleProj E n
  have := locallyOfFiniteType_bundleProj E n
  -- the fibre product `W = P ×_X P`, its projections and the closed immersion `j : W ⟶ P × P`
  have hW := IsPullback.of_hasPullback (bundleProj E) (bundleProj E)
  have : Flat (pullback.snd (bundleProj E) (bundleProj E)) :=
    MorphismProperty.of_isPullback hW inferInstance
  have : LocallyOfFiniteType (pullback.snd (bundleProj E) (bundleProj E)) :=
    MorphismProperty.of_isPullback hW inferInstance
  have : IsProper (pullback.snd (bundleProj E) (bundleProj E)) :=
    MorphismProperty.of_isPullback hW inferInstance
  have hπ : RelativeDimension (pullback.snd (bundleProj E) (bundleProj E)) n :=
    RelativeDimension.of_isPullback hW (relativeDimension_bundleProj E n)
  have hsq := pullback_map_diagonal_isPullback (bundleProj E) (bundleProj E) sX
  have : IsProper (pullback.map (bundleProj E) (bundleProj E) (bundleProj E ≫ sX)
      (bundleProj E ≫ sX) (𝟙 _) (𝟙 _) sX (Category.id_comp _).symm (Category.id_comp _).symm) :=
    MorphismProperty.of_isPullback hsq inferInstance
  have hj : pullback.map (bundleProj E) (bundleProj E) (bundleProj E ≫ sX) (bundleProj E ≫ sX)
      (𝟙 _) (𝟙 _) sX (Category.id_comp _).symm (Category.id_comp _).symm ≫
        prodBase (bundleProj E ≫ sX) (bundleProj E ≫ sX) =
      pullback.snd (bundleProj E) (bundleProj E) ≫ bundleProj E ≫ sX := by
    simp [prodBase, pullback.condition_assoc]
  have hδ : pullback.diagonal (bundleProj E) ≫ pullback.snd (bundleProj E) (bundleProj E) ≫
      bundleProj E ≫ sX = bundleProj E ≫ sX := by simp
  have hΔ : pullback.diagonal (bundleProj E ≫ sX) = pullback.diagonal (bundleProj E) ≫
      pullback.map (bundleProj E) (bundleProj E) (bundleProj E ≫ sX) (bundleProj E ≫ sX)
        (𝟙 _) (𝟙 _) sX (Category.id_comp _).symm (Category.id_comp _).symm := by
    apply pullback.hom_ext <;> simp
  -- the left hand side is `j_* δ_* [P]_{m+n}`
  rw [QuotientAddGroup.mk'_apply, mk_cycleAssociatedToClosedSubscheme_eq_properChowPushforward
    (prodBase (bundleProj E ≫ sX) (bundleProj E ≫ sX)) (bundleProj E ≫ sX)
    (pullback.diagonal (bundleProj E ≫ sX)) (by simp [prodBase]) (m + n)]
  have hcomp := DFunLike.congr_fun (properChowPushforward_comp (fieldChowSituation k)
    (bundleProj E ≫ sX) (pullback.snd (bundleProj E) (bundleProj E) ≫ bundleProj E ≫ sX)
    (prodBase (bundleProj E ≫ sX) (bundleProj E ≫ sX)) (pullback.diagonal (bundleProj E))
    _ hδ hj (m + n) (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _))
    (fundamentalChowClass (fieldChowSituation k) (bundleProj E ≫ sX) (m + n))
  rw [AddMonoidHom.comp_apply] at hcomp
  rw [properChowPushforward_congr _ _ _ _ _ hΔ _ (by rw [← hΔ]; simp [prodBase]) _
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _), ← hcomp]
  -- the class of the diagonal of `W ⟶ P`, a section of `q₂`
  have e₂ : (((bundleTautologicalSequence E).map
      (Scheme.Modules.pullback (pullback.fst (bundleProj E) (bundleProj E)))).X₂ ≅
      (Scheme.Modules.pullback (pullback.snd (bundleProj E) (bundleProj E))).obj
        ((Scheme.Modules.pullback (bundleProj E)).obj E)) :=
    (Scheme.Modules.pullbackComp _ _).app E ≪≫
      (Scheme.Modules.pullbackCongr pullback.condition).app E ≪≫
      ((Scheme.Modules.pullbackComp _ _).app E).symm
  have htower : IsLocallyProjectiveTower n (pullback.snd (bundleProj E) (bundleProj E))
      (((bundleTautologicalSequence E).map
        (Scheme.Modules.pullback (pullback.fst (bundleProj E) (bundleProj E)))).X₃) :=
    (isLocallyProjectiveTower_bundle E n).of_isPullback hW (Iso.refl _)
  have eL : bundleTwist E ≅ (Scheme.Modules.pullback (pullback.diagonal (bundleProj E))).obj
      (((bundleTautologicalSequence E).map
        (Scheme.Modules.pullback (pullback.fst (bundleProj E) (bundleProj E)))).X₃) :=
    ((Scheme.Modules.pullbackId _).app _).symm ≪≫
      (Scheme.Modules.pullbackCongr (pullback.diagonal_fst (bundleProj E))).symm.app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm
  have : SheafOfModules.IsInvertible (Limits.pullback (bundleProj E) (bundleProj E)).sheaf.obj
      (Limits.pullback (bundleProj E) (bundleProj E)).ringCatSheaf.property
      (((bundleTautologicalSequence E).map
        (Scheme.Modules.pullback (pullback.fst (bundleProj E) (bundleProj E)))).X₃) :=
    GenuineChern.isInvertible_pullback _ _
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (bundleTautologicalSequence E).X₁ n :=
    instIsFiniteLocallyFreeOfRankKernelBundleTautological E n
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((bundleTautologicalSequence E).map
        (Scheme.Modules.pullback (pullback.fst (bundleProj E) (bundleProj E)))).X₁) n :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ n
  have hcore := GenuineChern.properChowPushforward_section_eq_sum (fieldChowSituation k)
    (bundleProj E ≫ sX) (pullback.snd (bundleProj E) (bundleProj E) ≫ bundleProj E ≫ sX)
    (pullback.snd (bundleProj E) (bundleProj E)) rfl n hπ
    ((Scheme.Modules.pullback (bundleProj E)).obj E)
    ((bundleTautologicalSequence E).map
      (Scheme.Modules.pullback (pullback.fst (bundleProj E) (bundleProj E))))
    (shortExact_pullback_bundleTautological E _) e₂ htower (pullback.diagonal (bundleProj E))
    (pullback.diagonal_snd _) hδ (bundleTwist E) eL m
    (fundamentalChowClass (fieldChowSituation k) (bundleProj E ≫ sX) (m + n))
  rw [hcore, map_sum]
  -- `(p × p)^*[Δ_X]_m = j_* q^*[X]_m` (Stacks 02RG), with `q = q₁ ≫ p : W ⟶ X`
  have hg' : (pullback.fst (bundleProj E) (bundleProj E) ≫ bundleProj E) ≫ sX =
      pullback.snd (bundleProj E) (bundleProj E) ≫ bundleProj E ≫ sX := by
    rw [Category.assoc, ← Category.assoc, pullback.condition, Category.assoc]
  have hA := flatPullbackChow_properChowPushforward_of_isProper (fieldChowSituation k) sX
    (prodBase sX sX) (pullback.snd (bundleProj E) (bundleProj E) ≫ bundleProj E ≫ sX)
    (prodBase (bundleProj E ≫ sX) (bundleProj E ≫ sX)) (pullback.diagonal sX) _ _ _ hsq
    (by simp [prodBase]) (bundleProdMap_comp_prodBase sX E) hg' (n + n)
    (relativeDimension_bundleProdMap sX E n) m (fundamentalChowClass (fieldChowSituation k) sX m)
  rw [← mk_cycleAssociatedToClosedSubscheme_eq_properChowPushforward,
    ← QuotientAddGroup.mk'_apply] at hA
  -- `q^*[X]_m = q₂^*[P]_{m+n}`
  have hpn := relativeDimension_bundleProj E n
  have hF1 : flatPullbackChow (fieldChowSituation k) (bundleProj E ≫ sX) sX (bundleProj E) rfl n
      hpn m (flatPullbackDescends _ _ _ _ _ _ _ _)
      (fundamentalChowClass (fieldChowSituation k) sX m) =
      fundamentalChowClass (fieldChowSituation k) (bundleProj E ≫ sX) (m + n) :=
    flatPullbackChow_fundamentalChowClass_of_smooth sX _ _ rfl n hpn m
  have hc := flatPullbackChow_comp (fieldChowSituation k)
    (pullback.snd (bundleProj E) (bundleProj E) ≫ bundleProj E ≫ sX) (bundleProj E ≫ sX) sX
    (pullback.snd (bundleProj E) (bundleProj E)) (bundleProj E) rfl rfl n n hπ hpn m
    (flatPullbackDescends _ _ _ _ _ _ _ _) (flatPullbackDescends _ _ _ _ _ _ _ _)
    (flatPullbackDescends _ _ _ _ _ _ _ _) (fundamentalChowClass (fieldChowSituation k) sX m)
  rw [hF1] at hc
  have hhom : ∀ (g g' : Limits.pullback (bundleProj E) (bundleProj E) ⟶ X) [LocallyOfFiniteType g]
      [Flat g] [LocallyOfFiniteType g'] [Flat g'] (e : g = g')
      (hg : g ≫ sX = pullback.snd (bundleProj E) (bundleProj E) ≫ bundleProj E ≫ sX)
      (hg2 : g' ≫ sX = pullback.snd (bundleProj E) (bundleProj E) ≫ bundleProj E ≫ sX)
      (hs : RelativeDimension g (n + n)) (hs' : RelativeDimension g' (n + n)) hfac hfac',
      flatPullbackChow (fieldChowSituation k) _ sX g hg (n + n) hs m hfac
          (fundamentalChowClass (fieldChowSituation k) sX m) ≍
        flatPullbackChow (fieldChowSituation k) _ sX g' hg2 (n + n) hs' m hfac'
          (fundamentalChowClass (fieldChowSituation k) sX m) := by
    intro g g' _ _ _ _ e hg hg2 hs hs' hfac hfac'
    subst e
    rfl
  have hB := (hhom _ _ pullback.condition hg' (Category.assoc _ _ _)
    (RelativeDimension.of_isPullback hsq.flip (relativeDimension_bundleProdMap sX E n))
    (RelativeDimension.comp_of_flat _ _ hπ hpn) (flatPullbackDescends _ _ _ _ _ _ _ _)
    (flatPullbackDescends _ _ _ _ _ _ _ _)).trans hc.symm
  -- the terms, one by one
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi := i.isLt
  have eL₂ : (Scheme.Modules.pullback (pullback.map (bundleProj E) (bundleProj E)
      (bundleProj E ≫ sX) (bundleProj E ≫ sX) (𝟙 _) (𝟙 _) sX (Category.id_comp _).symm
      (Category.id_comp _).symm)).obj ((Scheme.Modules.pullback
        (pullback.snd (bundleProj E ≫ sX) (bundleProj E ≫ sX))).obj (bundleTwist E)) ≅
      (Scheme.Modules.pullback (pullback.snd (bundleProj E) (bundleProj E))).obj
        (bundleTwist E) :=
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr (by simp)).app _
  have := Stacks.Chow.GenuineChern.isFiniteLocallyFree_of_rank (kernel (bundleTautological E)) n
  have eE : dualSheaf (((bundleTautologicalSequence E).map
      (Scheme.Modules.pullback (pullback.fst (bundleProj E) (bundleProj E)))).X₁) ≅
      (Scheme.Modules.pullback (pullback.map (bundleProj E) (bundleProj E)
        (bundleProj E ≫ sX) (bundleProj E ≫ sX) (𝟙 _) (𝟙 _) sX (Category.id_comp _).symm
        (Category.id_comp _).symm)).obj ((Scheme.Modules.pullback
          (pullback.fst (bundleProj E ≫ sX) (bundleProj E ≫ sX))).obj
            (dualSheaf (kernel (bundleTautological E)))) :=
    (@asIso _ _ _ _ (pullbackDualMap (pullback.fst (bundleProj E) (bundleProj E))
      (kernel (bundleTautological E))) (pullbackDualMap_isIso _ _ inferInstance)).symm ≪≫
      (Scheme.Modules.pullbackCongr (by simp)).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm
  have : SheafOfModules.IsInvertible _ _ ((Scheme.Modules.pullback
      (pullback.map (bundleProj E) (bundleProj E) (bundleProj E ≫ sX) (bundleProj E ≫ sX) (𝟙 _)
        (𝟙 _) sX (Category.id_comp _).symm (Category.id_comp _).symm)).obj
      ((Scheme.Modules.pullback (pullback.snd (bundleProj E ≫ sX) (bundleProj E ≫ sX))).obj
        (bundleTwist E))) :=
    GenuineChern.isInvertible_pullback _ _
  change _ = chowGroupCast _ _ _ (GenuineChern.chernFamily _ _ _ n _ _ (capPow _ _ _ _ _ _ _
    (flatPullbackChow _ _ _ _ _ _ _ _ _ _)))
  rw [hA, ← properChowPushforward_capPow, GenuineChern.capPow_invCap_congr _ _ eL₂,
    chernFamily_properChowPushforward _ _ _ hj _ n _ eE, properChowPushforward_chowGroupCast]
  congr 1
  refine eq_of_heq ((chowGroupCast_heq _ _ _ _).trans
    (HEq.trans ?_ (chowGroupCast_heq _ _ _ _).symm))
  refine heq_apply_of_degree _ _ _ (fun d ↦ d) (fun d ↦ d - ((n - (i : ℕ) : ℕ) : ℤ))
    (fun d ↦ GenuineChern.chernFamily (fieldChowSituation k)
      (pullback.snd (bundleProj E) (bundleProj E) ≫ bundleProj E ≫ sX)
      (dualSheaf (((bundleTautologicalSequence E).map
        (Scheme.Modules.pullback (pullback.fst (bundleProj E) (bundleProj E)))).X₁)) n d (n - i))
    (by push_cast; ring) ?_
  refine (heq_of_eq (flatPullbackChowOfRelativeDimension_capPow (fieldChowSituation k) _ _
    (pullback.snd (bundleProj E) (bundleProj E)) rfl n hπ (bundleTwist E) i (m + n)
    (m + n - (i : ℕ)) (by ring) _)).trans ?_
  exact capPow_heq_of_heq _ _ _ _ _ _ (by push_cast; ring) (by push_cast; ring) hB.symm

end Diagonal

end Stacks.WeilCohomology

end
