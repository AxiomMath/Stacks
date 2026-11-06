module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFormalObjectOpenLocus
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFormalObjectAlgebraization

/-!
# Compatibility over complete local bases from algebraization of maps into `X'`

The compatibility over complete local bases in the proof of Stacks 0GI8, deduced from
Grothendieck's algebraization of morphisms into `X'` (Stacks 0A4Z in its form for algebraic
spaces). Let `R` be a Noetherian complete local ring with residue field of finite type over `S`,
`V = Spec R`, `Z ⊆ |V|` closed and containing the closed point, and `x̂ : V_{/Z} ⟶ W` adic. The
base change `V_{/Z} ×_{x̂, W, g} X'_{/T'} ⟶ V_{/Z}` is a formal modification (Stacks 0GDN), hence
the completion of a proper `p : V' ⟶ V` which is an isomorphism over `V ∖ Z` (Stacks 0GDU). If the
projection `V'_{/Z} ⟶ X'_{/T'}` is the completion of a morphism `x' : V' ⟶ X'` (the algebraization
property `AlgebraicGeometry.Artin.ContractionSituation.HasCompletionAlgebraization`, which is
Stacks 0A4Z when `X' ⟶ S` is separated), then `x'` restricted to `V ∖ Z` lands in `U' = X' ∖ T'`
(`AlgebraicGeometry.Artin.ContractionSituation.exists_comp_U'_ι_of_isProper`) and `(V', p, x')`
witnesses the compatibility of `x̂` with that restriction.

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSituation.HasCompletionAlgebraization`.

## Main results

* `ContractionSituation.hasCompatibilityOverCompleteLocalBase_of_hasCompletionAlgebraization`:
  compatibility over complete local bases.
* `ContractionSituation.hasEffectiveFormalObjects_of_hasCompletionAlgebraization`: effectivity of
  formal objects.

## References

* [Stacks Project, Tag 0GI8](https://stacks.math.columbia.edu/tag/0GI8)
* [Stacks Project, Tag 0GDN](https://stacks.math.columbia.edu/tag/0GDN)
* [Stacks Project, Tag 0GDU](https://stacks.math.columbia.edu/tag/0GDU)
* [Stacks Project, Tag 0A4Z](https://stacks.math.columbia.edu/tag/0A4Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing Deformation.Artin

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

variable (c : ContractionSituation B S hS)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of fppf sheaves (instance search times out without this shortcut). -/
local instance hasPullbacks_fppfSheaf_ContractionFormalObjectCompatibility :
    HasPullbacks (FormalSpace.FppfSheaf B S hS) := inferInstance

local instance (priority := high) hasPullback_fppfSheaf_ContractionFormalObjectCompatibility
    {X Y Z : FormalSpace.FppfSheaf B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Algebraization of morphisms from completions of proper spaces over complete local bases
into `X'`.** For every Noetherian complete local `S`-algebra `R` with residue field of finite type
over `S`, every closed `Z ⊆ |Spec R|` containing the closed point, every algebraic space `Y`
proper over `Spec R` and every morphism `μ : Y_{/|p|⁻¹Z} ⟶ X'_{/T'}`, there is `y : Y ⟶ X'`
carrying `|p|⁻¹ Z` into `T'` whose completion is `μ`. This is the input from Grothendieck's
existence theorem (Stacks 0A4Z for the algebraic space `X'`, which is separated and locally of
finite type over `S`). -/
def HasCompletionAlgebraization : Prop :=
  ∀ (A : FormalBase S) (hA : ∀ n, B.Contains (A.truncation n))
    (Z : Set (Space.points B S hS
      (yoneda.obj (baseOver B S hS A (A.contains_spec_of_contains_truncation hA))))),
    IsClosed Z →
    Space.HasImageIn B S hS _ Z (truncationOver B S hS A hA 0)
      (restrictionToBase B S hS A (A.contains_spec_of_contains_truncation hA) hA 0) →
    ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Y →
    ∀ (p : Y ⟶ yoneda.obj (baseOver B S hS A (A.contains_spec_of_contains_truncation hA))),
      Space.IsProper B S hS p →
    ∀ μ : Space.completionSheaf B S hS Y (Space.pointsMap B S hS Y p ⁻¹' Z) ⟶
        Space.completionSheaf B S hS c.X' c.T',
      ∃ (y : Y ⟶ c.X') (hT : Space.pointsMap B S hS Y p ⁻¹' Z ⊆
          Space.pointsMap B S hS Y y ⁻¹' c.T'),
        Space.completionSheafRestrict B S hS y _ c.T' hT = μ

/-- The closed point of a complete local base lies in every `Z` containing the image of the
first truncation. -/
theorem closedPoint_mem_of_hasImageIn (A : FormalBase S) (hA : ∀ n, B.Contains (A.truncation n))
    {Z : Set (Space.points B S hS
      (yoneda.obj (baseOver B S hS A (A.contains_spec_of_contains_truncation hA))))}
    (hZ : Space.HasImageIn B S hS _ Z (truncationOver B S hS A hA 0)
      (restrictionToBase B S hS A (A.contains_spec_of_contains_truncation hA) hA 0)) :
    (Space.pointsEquivScheme B S hS
      (baseOver B S hS A (A.contains_spec_of_contains_truncation hA))).symm
        (IsLocalRing.closedPoint A.R : Spec (.of A.R)) ∈ Z := by
  have : Nontrivial (A.R ⧸ maximalIdeal A.R ^ (0 + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (by simpa using (maximalIdeal.isMaximal A.R).ne_top)
  obtain ⟨a⟩ : Nonempty (PrimeSpectrum (A.R ⧸ maximalIdeal A.R ^ (0 + 1))) := inferInstance
  have ha : PrimeSpectrum.comap (Ideal.Quotient.mk (maximalIdeal A.R ^ (0 + 1))) a =
      IsLocalRing.closedPoint A.R := by
    refine PrimeSpectrum.ext ((maximalIdeal.isMaximal A.R).eq_of_le
      (PrimeSpectrum.comap (Ideal.Quotient.mk _) a).isPrime.ne_top ?_).symm
    intro z hz
    show Ideal.Quotient.mk _ z ∈ a.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using hz)]
    exact a.asIdeal.zero_mem
  have h' := (Space.hasImageIn_yoneda_iff_forall_scheme Z _).1 hZ a
  have hmap : (BigFppfOver.toScheme B S hS).map
      (restrictionToBase B S hS A (A.contains_spec_of_contains_truncation hA) hA 0) a =
      (IsLocalRing.closedPoint A.R : Spec (.of A.R)) := ha
  rwa [hmap] at h'

/-- **Compatibility over complete local bases, from algebraization into `X'`.** -/
theorem hasCompatibilityOverCompleteLocalBase_of_hasCompletionAlgebraization
    (halg : c.HasCompletionAlgebraization) : c.HasCompatibilityOverCompleteLocalBase := by
  intro A hA Z hZ hZ0 xhat hxhat
  let hRS := A.contains_spec_of_contains_truncation hA
  let V := baseOver B S hS A hRS
  have := A.noetherian
  have hVsp := isAlgebraicSpace_yoneda B S hS V
  have hVN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of A.R)))
  have hVN' := Space.isLocallyNoetherian_yoneda B S hS V hVN
  -- the formal modification `V_{/Z} ×_{x̂, W, g} X'_{/T'} ⟶ V_{/Z}` (Stacks 0GDN)
  have h𝔣 : FormalSpace.IsFormalModification B S hS (pullback.snd c.g xhat) :=
    FormalSpace.isFormalModification_pullback_snd_of_isAdicMorphism B S hS c.g xhat
      (FormalSpace.isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian hVsp hVN' Z hZ)
      hxhat c.isFormalModification_g
  -- its dilatation `p : V' ⟶ V` (Stacks 0GDU)
  obtain ⟨V₃, hV₃, p, hp, hpU, ⟨e⟩⟩ :=
    FormalSpace.exists_isProper_completion_iso_of_isFormalModification hVsp hVN' Z hZ h𝔣
  let eL : Space.completionSheaf B S hS V₃ (Space.pointsMap B S hS V₃ p ⁻¹' Z) ≅
      pullback c.g xhat :=
    (Over.forget _).mapIso e
  have hehom : eL.hom ≫ pullback.snd c.g xhat = Space.completionSheafMap B S hS p Z :=
    Over.w e.hom
  -- the morphism `V'_{/Z} ⟶ X'_{/T'}` algebraizes (Stacks 0A4Z)
  obtain ⟨y, hT, hy⟩ := halg A hA Z hZ hZ0 V₃ hV₃ p hp (eL.hom ≫ pullback.fst c.g xhat)
  have hformal : Space.completionSheafRestrict B S hS p (Space.pointsMap B S hS V₃ p ⁻¹' Z) Z
      (fun _ hz => hz) ≫ xhat =
      Space.completionSheafRestrict B S hS y (Space.pointsMap B S hS V₃ p ⁻¹' Z) c.T' hT ≫
        c.g := by
    rw [hy, Space.completionSheafRestrict_self B S hS p Z (fun _ hz => hz), Category.assoc,
      pullback.condition, ← Category.assoc, hehom]
  -- the section of `p` over `V ∖ Z`
  let O := Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ
  let jY : O.toFunctor ⟶ V₃ := inv (pullback.snd p O.ι) ≫ pullback.fst p O.ι
  have hjY : jY ≫ p = O.ι := by
    simp only [jY, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  -- `x'` restricted to `V ∖ Z` lands in `U'`
  obtain ⟨u, hu⟩ := c.exists_comp_U'_ι_of_isProper hRS A.toS
    (closedPoint_mem_of_hasImageIn A hA hZ0) xhat hxhat hV₃ p hp jY hjY y hT hformal
  exact ⟨u, c.nonempty_compatibilityWitness_of_isProper hVN hZ u xhat hxhat hV₃ p hp hpU jY hjY
    y hu hT hformal⟩

/-- **Stacks 0GI8, reduced to the algebraization of morphisms into `X'`.** In the situation of
Stacks 0GH8, if morphisms from completions of proper algebraic spaces over complete local bases
into `X'_{/T'}` algebraize (`HasCompletionAlgebraization`, which is Stacks 0A4Z when `X'` is
separated over `S`), then every formal object of Artin's functor `F` is effective. -/
theorem hasEffectiveFormalObjects_of_hasCompletionAlgebraization
    (halg : c.HasCompletionAlgebraization) :
    LocallyNoetherianOver.HasEffectiveFormalObjects B S hS (contractionFunctor c) :=
  c.hasEffectiveFormalObjects_of_hasCompatibility
    (c.hasCompatibilityOverCompleteLocalBase_of_hasCompletionAlgebraization halg)

end AlgebraicGeometry.Artin.ContractionSituation

end
