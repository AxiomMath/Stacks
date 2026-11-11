module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.NormalPosition.Transverse
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.NormalPosition.TransverseProduct
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.NormalPosition.SurfaceChain
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Defs
import all
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveFamilyResolution
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.NormalCrossingsAfterPointBlowups

/-!
# Embedded resolution of a curve on a regular surface

Let `X` be a regular Noetherian scheme of dimension two and let `Z ⊆ X` be a closed subscheme
containing no irreducible component of `X`, each of whose one-dimensional irreducible components
satisfies the equivalent conditions of [Stacks, Tag 0BI4]. Then a finite sequence of blowups at
closed points `Xₙ → … → X₁ → X` makes the inverse image `Zₙ` of `Z` an effective Cartier divisor
supported on a strict normal crossings divisor: [Stacks, Tag 0BIC].

## Main results

* `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_comap_support_eq_isStrictNormalCrossings` —
  [Stacks, Tag 0BIC].

## The proof

The source's, in four steps.

1. [Stacks, Tag 0BIB] makes `Z` an effective Cartier divisor `D` after blowups at closed points
   with two-dimensional local rings
   (`Stacks.ResolutionOfSurfaces.exists_surfacePointBlowupChain_comap_isEffectiveCartierDivisor`),
   and the condition of Tag 0BI4 passes to the one-dimensional components of the inverse image
   (`Stacks.ResolutionOfSurfaces.resolvable_componentIdeal_comap_of_surfacePointBlowupChain`).
2. The irreducible components of `D`, with their reduced structures, form a finite family of
   configuration curves (`Stacks.ResolutionOfSurfaces.IsConfigCurve`): integral effective Cartier
   divisors, each regular or a resolvable curve. A component which is not a curve is a reduced
   point, and is regular.
3. Finitely many blowups make every member regular
   (`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_forall_isRegular`).
4. Finitely many more make any two members meet transversally and no three meet
   (`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_transverse`), and then the product of the
   members is a strict normal crossings divisor
   (`Stacks.ResolutionOfSurfaces.isStrictNormalCrossingsDivisor_prod_of_transverse`) whose support
   is that of the inverse image of `Z`.

## Implementation notes

The conclusion is that of
`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_comap_isStrictNormalCrossings`, under the
source's hypotheses alone. The source's "proper closed subscheme" is taken as
`IsNowhereDense (Z.support : Set X)`, as for [Stacks, Tag 0BIB]: the literal reading is not enough
when `X` is disconnected, since for `X` a disjoint union of two affine planes and `Z` one of them
the ideal sheaf of `Z` vanishes on that copy and stays zero under every inverse image. `X` is
taken Noetherian rather than only locally Noetherian, again as for [Stacks, Tag 0BIB]: for `X` a
disjoint union of countably many affine planes and `Z` the set of their origins, no finite
sequence of blowups at closed points makes `Zₙ` a Cartier divisor. Both corrections are recorded
in `errata.md`. The
conclusion records that the support of `Zₙ` *equals* the support of the strict normal crossings
divisor, which is what the source's argument gives and is stronger than "supported on".

## References

* [Stacks Project, Tag 0BIC](https://stacks.math.columbia.edu/tag/0BIC)
* [Stacks Project, Tag 0BIB](https://stacks.math.columbia.edu/tag/0BIB)
* [Stacks Project, Tag 0BI4](https://stacks.math.columbia.edu/tag/0BI4)
* [Stacks Project, Tag 0BI7](https://stacks.math.columbia.edu/tag/0BI7)
* [Stacks Project, Tag 0BIA](https://stacks.math.columbia.edu/tag/0BIA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Divisors

universe u

namespace Stacks.ResolutionOfSurfaces

/-- An integral locally Noetherian scheme of dimension at most zero is regular: its only local ring
is a field. -/
public theorem isRegular_of_topologicalKrullDim_le_zero (Y : Scheme.{u}) [IsIntegral Y]
    [IsLocallyNoetherian Y] (h : topologicalKrullDim Y ≤ 0) : AlgebraicGeometry.IsRegular Y := by
  refine (isRegular_iff_regular_stalks Y).mpr ⟨inferInstance, fun y => ?_⟩
  have hle : ringKrullDim (Y.presheaf.stalk y) ≤ 0 :=
    (Stacks.AlgebraicGeometry.NormalizationQuotient.ringKrullDim_stalk_le_topologicalKrullDim
      Y y).trans h
  have : Ring.KrullDimLE 0 (Y.presheaf.stalk y) := ⟨by exact_mod_cast hle⟩
  have hfield : IsField (Y.presheaf.stalk y) := Ring.KrullDimLE.isField_of_isDomain
  let := hfield.toField
  infer_instance

/-- Two closed subschemes meeting at a point with local intersection colength one cut out the
maximal ideal of the local ring there. -/
public theorem sup_stalk_eq_maximalIdeal_of_localIntersectionColength_eq_one {X : Scheme.{u}}
    (I J : X.IdealSheafData) (x : X) (h : localIntersectionColength I J x = 1) :
    IdealSheafData.stalk I x ⊔ IdealSheafData.stalk J x =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  have hlen : Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
      (IdealSheafData.stalk I x ⊔ IdealSheafData.stalk J x)) = 1 := by
    rw [localIntersectionColength] at h
    exact ENat.toNat_eq_iff one_ne_zero |>.mp h
  rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def] at hlen
  exact IsLocalRing.eq_maximalIdeal hlen

/-- **The components of an effective Cartier divisor are configuration curves**, on a regular
Noetherian surface along which the one-dimensional components of the divisor satisfy condition (3)
of [Stacks, Tag 0BI4]. -/
public theorem isConfigCurve_componentIdeal {W : Scheme.{u}} [IsNoetherian W]
    (hW : AlgebraicGeometry.IsRegular W) (hdim : topologicalKrullDim W = 2)
    (D : W.IdealSheafData) (hD : IsEffectiveCartierDivisor D)
    (hres : ∀ C : irreducibleComponents D.subscheme,
      topologicalKrullDim (componentIdeal D C).subscheme = 1 → IsResolvable (componentIdeal D C))
    (C : irreducibleComponents D.subscheme) : IsConfigCurve (componentIdeal D C) := by
  obtain ⟨-, hstalk⟩ : IsLocallyNoetherian W ∧ ∀ x : W, IsRegularLocalRing (W.presheaf.stalk x) :=
    (isRegular_iff_regular_stalks W).mp hW
  have hint := isIntegral_componentIdeal D C
  have hcart := isEffectiveCartierDivisor_componentIdeal hstalk D hD C
  refine ⟨hint, hcart, ?_⟩
  by_cases hd : topologicalKrullDim (componentIdeal D C).subscheme = 1
  · exact Or.inr ⟨hd, hres C hd⟩
  · refine Or.inl ?_
    have : IsLocallyNoetherian (componentIdeal D C).subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (componentIdeal D C).subschemeι
    have hle := topologicalKrullDim_subscheme_le_one hdim (componentIdeal D C) hcart
    refine isRegular_of_topologicalKrullDim_le_zero _ ?_
    have hlt : topologicalKrullDim (componentIdeal D C).subscheme < 1 := lt_of_le_of_ne hle hd
    generalize topologicalKrullDim (componentIdeal D C).subscheme = n at hlt ⊢
    induction n using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe n =>
      have : n < 1 := by exact_mod_cast hlt
      exact_mod_cast (Order.lt_one_iff.mp this).le

/-- The components of a closed subscheme cover its support. -/
public theorem iUnion_support_componentIdeal {W : Scheme.{u}} (D : W.IdealSheafData) :
    ⋃ C : irreducibleComponents D.subscheme, ((componentIdeal D C).support : Set W) =
      (D.support : Set W) := by
  have hcomp : ∀ C : irreducibleComponents D.subscheme,
      ((componentIdeal D C).support : Set W) = D.subschemeι '' (C : Set D.subscheme) := by
    intro C
    rw [componentIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact (D.subschemeι.isClosedEmbedding.isClosedMap _
      (isClosed_of_mem_irreducibleComponents _ C.2)).closure_eq
  simp only [hcomp]
  rw [← Set.image_iUnion, ← D.range_subschemeι, ← Set.image_univ, ← sUnion_irreducibleComponents,
    Set.sUnion_eq_iUnion]

/-- **Stacks Project, Tag 0BIC.** Let `X` be a regular Noetherian scheme of dimension two and let
`Z ⊆ X` be a closed subscheme containing no irreducible component of `X` — the source's "proper
closed subscheme" — each of whose one-dimensional irreducible components satisfies the equivalent
conditions of [Stacks, Tag 0BI4], in the point-blowup form of clause (3) there. Then there is a
sequence `Xₙ → … → X₁ → X` of blowups at closed points such that the inverse image `Zₙ` of `Z` in
`Xₙ` is an effective Cartier divisor whose support is the support of a strict normal crossings
divisor. -/
@[stacks 0BIC]
public theorem exists_pointBlowupChain_comap_support_eq_isStrictNormalCrossings
    (X : Scheme.{u}) [IsNoetherian X] (hX : AlgebraicGeometry.IsRegular X)
    (hdim : topologicalKrullDim X = 2) (Z : X.IdealSheafData)
    (hZ : IsNowhereDense (Z.support : Set X))
    (hres : ∀ C : irreducibleComponents Z.subscheme,
      topologicalKrullDim (componentIdeal Z C).subscheme = 1 →
      ∃ (P : Scheme.{u}) (g : P ⟶ (componentIdeal Z C).subscheme),
        PointBlowupChain (componentIdeal Z C).subscheme Set.univ P g ∧
          AlgebraicGeometry.IsRegular P) :
    ∃ (W : Scheme.{u}) (f : W ⟶ X), PointBlowupChain X Set.univ W f ∧
      IsEffectiveCartierDivisor (Z.comap f) ∧
      ∃ (hW : IsLocallyNoetherian W) (D : W.IdealSheafData),
        @IsStrictNormalCrossingsDivisor W hW D ∧
          ((Z.comap f).support : Set W) = (D.support : Set W) := by
  classical
  obtain ⟨W₁, f₁, hc₁, hcart₁⟩ :=
    exists_surfacePointBlowupChain_comap_isEffectiveCartierDivisor X hX hdim Z hZ
  have : IsNoetherian W₁ := hc₁.isNoetherian
  obtain ⟨hreg₁, hdim₁⟩ := hc₁.isRegular hX hdim
  set D₁ := Z.comap f₁ with hD₁
  have : IsNoetherian D₁.subscheme := isNoetherian_subscheme D₁
  have : Finite (irreducibleComponents D₁.subscheme) :=
    (NoetherianSpace.finite_irreducibleComponents (α := D₁.subscheme)).to_subtype
  set F₀ : Finset W₁.IdealSheafData := (Set.finite_range (componentIdeal D₁)).toFinset with hF₀
  have hF₀c : ∀ Y ∈ F₀, IsConfigCurve Y := by
    intro Y hY
    obtain ⟨C, rfl⟩ := (Set.Finite.mem_toFinset _).mp hY
    exact isConfigCurve_componentIdeal hreg₁ hdim₁ D₁ hcart₁
      (fun C hC => resolvable_componentIdeal_comap_of_surfacePointBlowupChain hX hdim hc₁ Z hres C
        hC) C
  have hU₀ : ⋃ Y ∈ F₀, (Y.support : Set W₁) = (D₁.support : Set W₁) := by
    rw [← iUnion_support_componentIdeal D₁]
    ext x
    simp [hF₀]
  obtain ⟨W₂, f₂, F₂, hc₂, hF₂, hreg₂, hU₂⟩ :=
    exists_pointBlowupChain_forall_isRegular _ W₁ hreg₁ hdim₁ F₀ hF₀c rfl
  have : IsNoetherian W₂ := isNoetherian_of_pointBlowupChain hc₂
  obtain ⟨hW₂reg, hW₂dim⟩ := hc₂.isRegular_and_topologicalKrullDim hreg₁ hdim₁
  obtain ⟨W₃, f₃, F₃, hc₃, hF₃, hreg₃, hU₃, hone₃, htr₃⟩ :=
    exists_pointBlowupChain_transverse _ W₂ hW₂reg hW₂dim F₂ hF₂ hreg₂ rfl
  have : IsNoetherian W₃ := isNoetherian_of_pointBlowupChain hc₃
  obtain ⟨-, hW₃dim⟩ := hc₃.isRegular_and_topologicalKrullDim hW₂reg hW₂dim
  have hLN : IsLocallyNoetherian W₃ := inferInstance
  have hchain : PointBlowupChain X Set.univ W₃ (f₃ ≫ f₂ ≫ f₁) :=
    (hc₁.toPointBlowupChain.comp hc₂ fun _ _ => Set.mem_univ _).comp hc₃
      fun _ _ => Set.mem_univ _
  refine ⟨W₃, f₃ ≫ f₂ ≫ f₁, hchain, ?_, hLN, ∏ A ∈ F₃, A, ?_, ?_⟩
  · rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    exact hc₃.isEffectiveCartierDivisor_comap (hc₂.isEffectiveCartierDivisor_comap hcart₁)
  · refine isStrictNormalCrossingsDivisor_prod_of_transverse F₃ hreg₃
      (fun A hA => (hF₃ A hA).isEffectiveCartierDivisor) ?_ ?_
    · intro x A₁ A₂ A₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hx₁ hx₂ hx₃
      have hmem : x ∈ triplePoints F₃ := by
        change 3 ≤ (F₃.filter fun Y => x ∈ (Y.support : Set W₃)).card
        have hsub : ({A₁, A₂, A₃} : Finset _) ⊆ F₃.filter fun Y => x ∈ (Y.support : Set W₃) := by
          intro A hA
          simp only [Finset.mem_insert, Finset.mem_singleton] at hA
          rcases hA with rfl | rfl | rfl
          · exact Finset.mem_filter.mpr ⟨h₁, hx₁⟩
          · exact Finset.mem_filter.mpr ⟨h₂, hx₂⟩
          · exact Finset.mem_filter.mpr ⟨h₃, hx₃⟩
        refine le_trans ?_ (Finset.card_le_card hsub)
        rw [Finset.card_insert_of_notMem (by simp [h₁₂, h₁₃]),
          Finset.card_insert_of_notMem (by simp [h₂₃]), Finset.card_singleton]
      rwa [htr₃] at hmem
    · intro x A₁ A₂ h₁ h₂ hne hx₁ hx₂
      obtain ⟨-, hxdim⟩ := (hF₃ A₁ h₁).isClosed_and_ringKrullDim_of_mem_inter hW₃dim (hF₃ A₂ h₂)
        hne hx₁ hx₂
      refine ⟨hxdim, ?_⟩
      have := (hF₃ A₁ h₁).isIntegral
      have := (hF₃ A₂ h₂).isIntegral
      have hd₁ := (hF₃ A₁ h₁).topologicalKrullDim_eq_one_of_ringKrullDim_eq_two hW₃dim hxdim hx₁
      have hd₂ := (hF₃ A₂ h₂).topologicalKrullDim_eq_one_of_ringKrullDim_eq_two hW₃dim hxdim hx₂
      have hxsup : x ∈ (A₁ ⊔ A₂).support := by
        rw [Scheme.IdealSheafData.support_sup]; exact ⟨hx₁, hx₂⟩
      have hpos := intersectionLength_pos A₁ A₂ hd₁ hd₂ hne x hxsup
      have hle := hone₃ A₁ h₁ A₂ h₂ hne x
      rw [localIntersectionColength_eq_intersectionLength _ _ x hxsup] at hle
      have hone : localIntersectionColength A₁ A₂ x = 1 := by
        rw [localIntersectionColength_eq_intersectionLength _ _ x hxsup]; lia
      exact sup_stalk_eq_maximalIdeal_of_localIntersectionColength_eq_one A₁ A₂ x hone
  · rw [coe_support_prod, hU₃, hU₂, hU₀, hD₁, Scheme.IdealSheafData.comap_comp,
      Scheme.IdealSheafData.comap_comp]
    simp only [Scheme.IdealSheafData.support_comap, Set.preimage_preimage]
    rfl

end Stacks.ResolutionOfSurfaces

end
