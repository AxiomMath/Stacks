module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.EpiClosedImmersionFactorization
import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.UnitHom
import StacksFrontier.AlgebraicGeometry.SectionProduct.PullbackUnitSection
import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.DegreeTwoGeneration

/-!
# The hyperplane section is invertible off the projective bundle of a split quotient

Let `ℒ` be an invertible module on a scheme `Y` and `x` a global section of `ℒ`, with its
morphism `t : 𝒪_Y ⟶ ℒ`. If a morphism `f : T ⟶ Y` lands in the nonvanishing locus of `x`, then
`f^*t` is an isomorphism, and conversely
(`AlgebraicGeometry.Scheme.Modules.isIso_pullback_map_unitHomEquivTop_iff`). This combines the
inverse image of the nonvanishing locus (Stacks Tag 0H78) with the trivialization of an
invertible module by a nowhere vanishing section (Stacks Tag 01CY).

On the projective bundle `π : 𝐏(F) ⟶ X` of a quasi-coherent module with a split short exact
sequence `0 ⟶ 𝒩 ⟶ F ⟶ G ⟶ 0` (`σ`, `u`, with `τ`, `σ'` splitting it) and `𝒩 = 𝒪_X`, the
composite `λ : π^*𝒪_X ⟶ π^*F ⟶ 𝒪(1)` of `π^*σ` with the tautological quotient is the hyperplane
section, and the closed immersion `i : 𝐏(G) ⟶ 𝐏(F)` of
`Stacks.RelativeProj.projectiveBundleMapOfEpi`
is its zero locus on points (`Stacks.RelativeProj.exists_comp_projectiveBundleMapOfEpi_iff`).
This file shows that the image of `i` is exactly the complement of the nonvanishing locus of the
section of `λ`, and deduces: a morphism `f : T ⟶ 𝐏(F)` has `f^*λ` an isomorphism exactly when
it misses the image of `i`, that is, when it factors through the open complement
`𝐏(F) ∖ i(𝐏(G))`.

## Main definitions

* `Stacks.RelativeProj.hyperplaneSectionOfSplit`: the global section of `𝒪(1)` given by `λ`.
* `Stacks.RelativeProj.splitQuotientComplement`: the open complement `𝐏(F) ∖ i(𝐏(G))`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isIso_pullback_map_unitHomEquivTop_of_range_subset`: **a
  section becomes an isomorphism after pullback along any morphism landing in its nonvanishing
  locus.**
* `Stacks.RelativeProj.nonvanishingLocus_hyperplaneSectionOfSplit`: the nonvanishing locus of
  the hyperplane section is the complement of the image of `i`.
* `Stacks.RelativeProj.isIso_pullback_map_hyperplane_iff`: `f^*λ` is an isomorphism exactly when
  `f` misses the image of `i`.
* `Stacks.RelativeProj.isIso_pullback_map_hyperplane_iff_range_subset`: the same, read as
  factoring through the open complement.

## References

* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {Y T : Scheme.{u}}

/-- The morphism out of the structure sheaf attached to the zero global section is zero. -/
theorem unitHomEquivTop_zero (M : Y.Modules) : Scheme.Modules.unitHomEquivTop M 0 = 0 := by
  rw [← Equiv.eq_symm_apply]
  rfl

/-- **Pulling back the morphism of a global section**: `f^*` of the morphism `𝒪_Y ⟶ M` of a
global section `x` is the comparison `f^*𝒪_Y ≅ 𝒪_T` followed by the morphism of the pulled-back
section `f^*x`. -/
theorem pullback_map_unitHomEquivTop (f : T ⟶ Y) (M : Y.Modules) (x : Γ(M, ⊤)) :
    (Scheme.Modules.pullback f).map (Scheme.Modules.unitHomEquivTop M x) =
      (Scheme.Modules.pullbackUnitIso f).hom ≫
        Scheme.Modules.unitHomEquivTop ((Scheme.Modules.pullback f).obj M)
          (pullbackSectionHom f M ⊤ ⊤ f.preimage_top.ge x) := by
  have h := Scheme.Modules.pullbackUnitIso_sections_naturality f M _ (𝟙 _) x
  rw [Category.comp_id, Adjunction.homEquiv_id] at h
  rw [← h]
  rfl

/-- **Stacks Tag 0H78 for `AlgebraicGeometry.pullbackSectionHom`, pointwise.** A point lies in the
nonvanishing locus of the pullback of a global section exactly when its image lies in the
nonvanishing locus of the section. -/
theorem mem_nonvanishingLocus_pullbackSectionHom_top_iff (f : T ⟶ Y) (M : Y.Modules)
    (x : Γ(M, ⊤)) (p : T) :
    p ∈ Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback f).obj M)
        (pullbackSectionHom f M ⊤ ⊤ f.preimage_top.ge x) ↔
      f.base p ∈ Stacks.Ample.nonvanishingLocus M x := by
  rw [Stacks.PullbackUnitSection.pullbackSectionHom_top_eq]
  exact Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff f M x p

/-- A section whose morphism out of the structure sheaf is an isomorphism vanishes nowhere. -/
theorem nonvanishingLocus_eq_univ_of_isIso (M : Y.Modules) (y : Γ(M, ⊤))
    [IsIso (Scheme.Modules.unitHomEquivTop M y)] :
    Stacks.Ample.nonvanishingLocus M y = Set.univ := by
  have h1 : (Scheme.Modules.unitHomEquivTop M y).app ⊤ (1 : Γ(Y, ⊤)) = y := by
    have h2 : (Scheme.Modules.unitHomEquivTop M y).app ⊤ (1 : Γ(Y, ⊤)) =
        (SheafOfModules.unitHomEquiv M (Scheme.Modules.unitHomEquivTop M y)).val (op ⊤) := rfl
    rw [h2, Scheme.Modules.unitHomEquiv_unitHomEquivTop, Scheme.Modules.sectionsTopEquiv_val,
      show (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op = 𝟙 (op (⊤ : Y.Opens)) from
        Subsingleton.elim _ _, M.presheaf.map_id]
    rfl
  have e := Stacks.Ample.nonvanishingLocus_congr (asIso (Scheme.Modules.unitHomEquivTop M y))
    (1 : Γ(Y, ⊤))
  rw [asIso_hom, h1] at e
  rw [e]
  exact Set.eq_univ_of_forall fun p =>
    Stacks.Ample.Γgerm_notMem_maximalSmul_of_eq_one Y p (1 : Γ(Y, ⊤)) rfl

/-- **A section becomes an isomorphism after pullback along a morphism landing in its
nonvanishing locus.** For `ℒ` invertible on `Y`, `x` a global section and `f : T ⟶ Y` with image
inside the nonvanishing locus of `x`, the pullback along `f` of the morphism `𝒪_Y ⟶ ℒ` of `x` is
an isomorphism: by Stacks Tag 0H78 the pulled-back section vanishes nowhere, so by Stacks Tag 01CY
its morphism is an isomorphism, and the two morphisms differ by the comparison `f^*𝒪_Y ≅ 𝒪_T`. -/
theorem isIso_pullback_map_unitHomEquivTop_of_range_subset (L : Y.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (x : Γ(L, ⊤)) (f : T ⟶ Y) (h : Set.range f.base ⊆ Stacks.Ample.nonvanishingLocus L x) :
    IsIso ((Scheme.Modules.pullback f).map (Scheme.Modules.unitHomEquivTop L x)) := by
  have hL' : AlgebraicGeometry.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2
      ((Scheme.Modules.pullback f).obj L) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      (@Stacks.Modules.isInvertible_pullback _ _ f L
        ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hL))
  have huniv : Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback f).obj L)
      (pullbackSectionHom f L ⊤ ⊤ f.preimage_top.ge x) = Set.univ :=
    Set.eq_univ_of_forall fun p =>
      (mem_nonvanishingLocus_pullbackSectionHom_top_iff f L x p).2 (h ⟨p, rfl⟩)
  have hiso : IsIso (Scheme.Modules.unitHomEquivTop ((Scheme.Modules.pullback f).obj L)
      (pullbackSectionHom f L ⊤ ⊤ f.preimage_top.ge x)) :=
    isIso_unitHomEquiv_symm_of_nonvanishingLocus_eq_univ ((Scheme.Modules.pullback f).obj L) _
      (((Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq T
        ((Scheme.Modules.pullback f).obj L) _).trans
        (congrArg (Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback f).obj L))
          (Stacks.NonvanishingSpelling.sectionsEquiv_sectionsTopEquiv T
            ((Scheme.Modules.pullback f).obj L) _))).trans huniv)
  rw [pullback_map_unitHomEquivTop]
  infer_instance

/-- **Conversely**, a morphism along which the morphism of a section pulls back to an isomorphism
lands in the nonvanishing locus of that section. -/
theorem range_subset_nonvanishingLocus_of_isIso_pullback_map (L : Y.Modules) (x : Γ(L, ⊤))
    (f : T ⟶ Y) [IsIso ((Scheme.Modules.pullback f).map (Scheme.Modules.unitHomEquivTop L x))] :
    Set.range f.base ⊆ Stacks.Ample.nonvanishingLocus L x := by
  have : IsIso (Scheme.Modules.unitHomEquivTop ((Scheme.Modules.pullback f).obj L)
      (pullbackSectionHom f L ⊤ ⊤ f.preimage_top.ge x)) := by
    have : Scheme.Modules.unitHomEquivTop ((Scheme.Modules.pullback f).obj L)
        (pullbackSectionHom f L ⊤ ⊤ f.preimage_top.ge x) =
        (Scheme.Modules.pullbackUnitIso f).inv ≫
          (Scheme.Modules.pullback f).map (Scheme.Modules.unitHomEquivTop L x) := by
      rw [pullback_map_unitHomEquivTop, Iso.inv_hom_id_assoc]
    rw [this]
    infer_instance
  rintro _ ⟨p, rfl⟩
  refine (mem_nonvanishingLocus_pullbackSectionHom_top_iff f L x p).1 ?_
  rw [nonvanishingLocus_eq_univ_of_isIso]
  trivial

/-- **Stacks Tag 0H78 with Tag 01CY, as an equivalence**: for `ℒ` invertible, the morphism of a
global section pulls back to an isomorphism along `f` exactly when `f` lands in the nonvanishing
locus of the section. -/
theorem isIso_pullback_map_unitHomEquivTop_iff (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (x : Γ(L, ⊤)) (f : T ⟶ Y) :
    IsIso ((Scheme.Modules.pullback f).map (Scheme.Modules.unitHomEquivTop L x)) ↔
      Set.range f.base ⊆ Stacks.Ample.nonvanishingLocus L x :=
  ⟨fun _ => range_subset_nonvanishingLocus_of_isIso_pullback_map L x f,
    isIso_pullback_map_unitHomEquivTop_of_range_subset L x f⟩

/-- A section whose morphism pulls back to zero along `f` vanishes on the image of `f`. -/
theorem disjoint_range_nonvanishingLocus_of_pullback_map_eq_zero (L : Y.Modules) (x : Γ(L, ⊤))
    (f : T ⟶ Y)
    (h : (Scheme.Modules.pullback f).map (Scheme.Modules.unitHomEquivTop L x) = 0) :
    Disjoint (Set.range f.base) (Stacks.Ample.nonvanishingLocus L x) := by
  have h0 : pullbackSectionHom f L ⊤ ⊤ f.preimage_top.ge x = 0 := by
    apply (Scheme.Modules.unitHomEquivTop ((Scheme.Modules.pullback f).obj L)).injective
    rw [unitHomEquivTop_zero, ← cancel_epi (Scheme.Modules.pullbackUnitIso f).hom,
      ← pullback_map_unitHomEquivTop, h, comp_zero]
  rw [Set.disjoint_left]
  rintro _ ⟨p, rfl⟩ hp
  have hp' := (mem_nonvanishingLocus_pullbackSectionHom_top_iff f L x p).2 hp
  rwa [h0, Stacks.Ample.nonvanishingLocus_zero] at hp'

/-- **A section not vanishing along the residue field of a point is nonvanishing there**, read on
the morphism of the section: if the morphism `𝒪_Y ⟶ ℒ` of `x` does not pull back to zero on
`Spec κ(y)`, then `y` lies in the nonvanishing locus of `x`. -/
theorem mem_nonvanishingLocus_of_pullback_fromSpecResidueField_ne_zero (L : Y.Modules)
    (x : Γ(L, ⊤)) (y : Y)
    (h : (Scheme.Modules.pullback (Y.fromSpecResidueField y)).map
      (Scheme.Modules.unitHomEquivTop L x) ≠ 0) :
    y ∈ Stacks.Ample.nonvanishingLocus L x := by
  refine mem_nonvanishingLocus_of_not_vanishesAlong L y x fun hv => h ?_
  have hv' : pullbackSectionHom (Y.fromSpecResidueField y) L ⊤ ⊤
      (Y.fromSpecResidueField y).preimage_top.ge x = 0 :=
    (Stacks.PullbackUnitSection.pullbackSectionHom_top_eq _ L _ x).trans hv
  rw [pullback_map_unitHomEquivTop, hv', unitHomEquivTop_zero, comp_zero]

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]

/-- **The hyperplane section attached to `σ : 𝒪_X ⟶ F`, as a morphism `𝒪_{𝐏(F)} ⟶ 𝒪(1)`**: the
comparison `𝒪_{𝐏(F)} ≅ π^*𝒪_X`, then `π^*σ`, then the tautological quotient `π^*F ⟶ 𝒪(1)`. -/
def hyperplaneSectionHom (σ : Scheme.unitModule X ⟶ F) :
    Scheme.unitModule (projectiveBundle X F) ⟶ tautologicalDatumTwist F :=
  (Scheme.Modules.pullbackUnitIso (projectiveBundleToBase X F)).inv ≫
    (Scheme.Modules.pullback (projectiveBundleToBase X F)).map σ ≫ tautologicalDatumUniv F

/-- **The hyperplane section attached to `σ : 𝒪_X ⟶ F`**, the global section of `𝒪_{𝐏(F)}(1)`
of `Stacks.RelativeProj.hyperplaneSectionHom`. -/
def hyperplaneSection (σ : Scheme.unitModule X ⟶ F) : Γ(tautologicalDatumTwist F, ⊤) :=
  (Scheme.Modules.unitHomEquivTop (tautologicalDatumTwist F)).symm (hyperplaneSectionHom σ)

/-- The morphism `𝒪_{𝐏(F)} ⟶ 𝒪(1)` of the hyperplane section of `σ` is
`Stacks.RelativeProj.hyperplaneSectionHom σ`. -/
theorem unitHomEquivTop_hyperplaneSection (σ : Scheme.unitModule X ⟶ F) :
    Scheme.Modules.unitHomEquivTop (tautologicalDatumTwist F) (hyperplaneSection σ) =
      hyperplaneSectionHom σ :=
  (Scheme.Modules.unitHomEquivTop (tautologicalDatumTwist F)).apply_symm_apply _

/-- The pullback of the hyperplane section along `f` is, up to the comparison
`f^*𝒪_{𝐏(F)} ≅ f^*π^*𝒪_X`, the pullback of `π^*σ ≫ (π^*F ⟶ 𝒪(1))`. -/
theorem pullback_map_hyperplaneSectionHom (σ : Scheme.unitModule X ⟶ F) {T : Scheme.{u}}
    (f : T ⟶ projectiveBundle X F) :
    (Scheme.Modules.pullback f).map (hyperplaneSectionHom σ) =
      (Scheme.Modules.pullback f).map
          (Scheme.Modules.pullbackUnitIso (projectiveBundleToBase X F)).inv ≫
        (Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullback (projectiveBundleToBase X F)).map σ ≫
            tautologicalDatumUniv F) := by
  rw [hyperplaneSectionHom, Functor.map_comp]

/-- Pulling back the morphism of the hyperplane section along `f` is, up to an isomorphism, the
pullback of `π^*σ ≫ (π^*F ⟶ 𝒪(1))`. -/
private theorem pullback_map_unitHomEquivTop_hyperplaneSection_eq_comp
    (σ : Scheme.unitModule X ⟶ F) {T : Scheme.{u}} (f : T ⟶ projectiveBundle X F) :
    (Scheme.Modules.pullback f).map
        (Scheme.Modules.unitHomEquivTop (tautologicalDatumTwist F) (hyperplaneSection σ)) =
      (Scheme.Modules.pullback f).map
          (Scheme.Modules.pullbackUnitIso (projectiveBundleToBase X F)).inv ≫
        (Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullback (projectiveBundleToBase X F)).map σ ≫
            tautologicalDatumUniv F) := by
  rw [unitHomEquivTop_hyperplaneSection, pullback_map_hyperplaneSectionHom]

variable (u : F ⟶ G) [Epi u]

/-- **The open complement `𝐏(F) ∖ i(𝐏(G))`** of the closed immersion
`i = Stacks.RelativeProj.projectiveBundleMapOfEpi u`. -/
def splitQuotientComplement : (projectiveBundle X F).Opens :=
  ⟨(Set.range (projectiveBundleMapOfEpi u).base)ᶜ,
    (projectiveBundleMapOfEpi u).isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- A point of `𝐏(F)` lies in the complement of `𝐏(G)` if and only if it is not in the image
of `Stacks.RelativeProj.projectiveBundleMapOfEpi u`. -/
theorem mem_splitQuotientComplement_iff (p : projectiveBundle X F) :
    p ∈ splitQuotientComplement u ↔ p ∉ Set.range (projectiveBundleMapOfEpi u).base :=
  Iff.rfl

/-- The underlying set of the complement of `𝐏(G)` is the complement of the image of
`Stacks.RelativeProj.projectiveBundleMapOfEpi u`. -/
theorem coe_splitQuotientComplement :
    (splitQuotientComplement u : Set (projectiveBundle X F)) =
      (Set.range (projectiveBundleMapOfEpi u).base)ᶜ :=
  rfl

variable (σ : Scheme.unitModule X ⟶ F) (τ : F ⟶ Scheme.unitModule X) (σ' : G ⟶ F)

/-- **The nonvanishing locus of the hyperplane section of a split quotient is the complement of
`𝐏(G)`.** For a split short exact sequence `0 ⟶ 𝒪_X ⟶ F ⟶ G ⟶ 0` the hyperplane section `λ` of
`σ` pulls back to zero on `𝐏(G)`, so it vanishes on the image of `i`; and at a point `y` where it
vanishes, it pulls back to zero on `Spec κ(y)`, so `Spec κ(y) ⟶ 𝐏(F)` factors through `i`
(`Stacks.RelativeProj.exists_comp_projectiveBundleMapOfEpi_iff`) and `y` is in the image of `i`. -/
theorem nonvanishingLocus_hyperplaneSection (hsplit : τ ≫ σ + u ≫ σ' = 𝟙 F) (hσu : σ ≫ u = 0) :
    Stacks.Ample.nonvanishingLocus (tautologicalDatumTwist F) (hyperplaneSection σ) =
      splitQuotientComplement u := by
  apply Set.Subset.antisymm
  · intro y hy hyi
    have h0 : (Scheme.Modules.pullback (projectiveBundleMapOfEpi u)).map
        (Scheme.Modules.unitHomEquivTop (tautologicalDatumTwist F) (hyperplaneSection σ)) = 0 := by
      rw [pullback_map_unitHomEquivTop_hyperplaneSection_eq_comp,
        pullback_map_projectiveBundleMapOfEpi_eq_zero u σ hσu, comp_zero]
    exact Set.disjoint_left.1
      (Scheme.Modules.disjoint_range_nonvanishingLocus_of_pullback_map_eq_zero _ _ _ h0) hyi hy
  · intro y hy
    by_contra hny
    let r := (projectiveBundle X F).fromSpecResidueField y
    have hr : (Scheme.Modules.pullback r).map
        (Scheme.Modules.unitHomEquivTop (tautologicalDatumTwist F) (hyperplaneSection σ)) = 0 := by
      by_contra hne
      exact hny
        (Scheme.Modules.mem_nonvanishingLocus_of_pullback_fromSpecResidueField_ne_zero _ _ y hne)
    rw [pullback_map_unitHomEquivTop_hyperplaneSection_eq_comp,
      Preadditive.IsIso.comp_left_eq_zero] at hr
    obtain ⟨h, hh⟩ := (exists_comp_projectiveBundleMapOfEpi_iff u σ τ σ' hsplit hσu r).2 hr
    exact hy ⟨h.base (IsLocalRing.closedPoint _), (congrArg (fun k => k.base
      (IsLocalRing.closedPoint ((projectiveBundle X F).residueField y))) hh).trans
        ((projectiveBundle X F).fromSpecResidueField_apply y _)⟩

/-- **The hyperplane section of a split quotient pulls back to an isomorphism exactly off
`𝐏(G)`.** For a split short exact sequence `0 ⟶ 𝒪_X ⟶ F ⟶ G ⟶ 0` and `f : T ⟶ 𝐏(F)`, the
pullback along `f` of `λ = π^*σ ≫ (π^*F ⟶ 𝒪(1))` is an isomorphism exactly when `f` misses the
image of the closed immersion `i : 𝐏(G) ⟶ 𝐏(F)`. -/
theorem isIso_pullback_map_hyperplane_iff (hsplit : τ ≫ σ + u ≫ σ' = 𝟙 F) (hσu : σ ≫ u = 0)
    {T : Scheme.{u}} (f : T ⟶ projectiveBundle X F) :
    IsIso ((Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullback (projectiveBundleToBase X F)).map σ ≫
          tautologicalDatumUniv F)) ↔
      Set.range f.base ⊆ splitQuotientComplement u := by
  have := isInvertible_tautologicalDatumTwist F
  rw [← nonvanishingLocus_hyperplaneSection u σ τ σ' hsplit hσu,
    ← Scheme.Modules.isIso_pullback_map_unitHomEquivTop_iff,
    pullback_map_unitHomEquivTop_hyperplaneSection_eq_comp, isIso_comp_left_iff]

/-- **The hyperplane section of a split quotient is an isomorphism after pullback along any
morphism missing `𝐏(G)`** (in particular along any open immersion with image inside
`𝐏(F) ∖ i(𝐏(G))`). -/
theorem isIso_pullback_map_hyperplane_of_range_subset (hsplit : τ ≫ σ + u ≫ σ' = 𝟙 F)
    (hσu : σ ≫ u = 0) {T : Scheme.{u}} (f : T ⟶ projectiveBundle X F)
    (hf : Set.range f.base ⊆ splitQuotientComplement u) :
    IsIso ((Scheme.Modules.pullback f).map
      ((Scheme.Modules.pullback (projectiveBundleToBase X F)).map σ ≫ tautologicalDatumUniv F)) :=
  (isIso_pullback_map_hyperplane_iff u σ τ σ' hsplit hσu f).2 hf

/-- The hyperplane section of a split quotient is an isomorphism on the open complement of
`𝐏(G)`. -/
theorem isIso_pullback_map_hyperplane_splitQuotientComplement_ι
    (hsplit : τ ≫ σ + u ≫ σ' = 𝟙 F) (hσu : σ ≫ u = 0) :
    IsIso ((Scheme.Modules.pullback (splitQuotientComplement u).ι).map
      ((Scheme.Modules.pullback (projectiveBundleToBase X F)).map σ ≫
        tautologicalDatumUniv F)) :=
  isIso_pullback_map_hyperplane_of_range_subset u σ τ σ' hsplit hσu _
    (by rw [Scheme.Opens.range_ι])

end Stacks.RelativeProj

end
