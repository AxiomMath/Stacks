module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.FormalFunctionsSections
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.IdealQuotientPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties

/-!
# The theorem on formal functions for modules with proper support

Let `A` be a Noetherian ring complete with respect to an ideal `I` and let `X` be an algebraic
space over `Spec A`.  Say that an `𝒪_X`-module `M` *satisfies the theorem on formal functions in
degree zero* (`AlgebraicGeometry.Space.C1573.SectionsFormal`) when
`Γ(X, M) ⟶ lim_n Γ(X, M / Iⁿ M)` is bijective.  This holds for coherent modules on proper
spaces (Stacks 08B0), is invariant under isomorphism, and passes to direct images along closed
immersions.

## Main definitions

* `AlgebraicGeometry.Space.C1573.SectionsFormal`: `Γ(X, M) ⟶ lim_n Γ(X, M / Iⁿ M)` is bijective.
* `AlgebraicGeometry.Space.C1573.idealQuotientMapOfHom`: the map `M / J M ⟶ N / J N` induced by
  `M ⟶ N`.

## Main results

* `AlgebraicGeometry.Space.C1573.sectionsFormal_of_isProper`: coherent modules on proper spaces
  satisfy `SectionsFormal`.
* `AlgebraicGeometry.Space.C1573.sectionsFormal_of_iso`: `SectionsFormal` is invariant under
  isomorphism.
* `AlgebraicGeometry.Space.C1573.sectionsFormal_pushforward`: `SectionsFormal` passes to the
  direct image along a closed immersion.
* `AlgebraicGeometry.Space.C1573.sectionsFormal_of_hasProperSupport`: coherent modules with proper
  support over `Spec A` satisfy `SectionsFormal`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space.C1573

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}

/-- **`Γ(X, M) ⟶ lim_n Γ(X, M / Iⁿ M)` is bijective**, spelled as injectivity and surjectivity
onto the compatible families. -/
def SectionsFormal (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (I : Ideal A) : Prop :=
  (∀ s s' : M.sections, (∀ n, SheafOfModules.sectionsMap
      (idealQuotientπ (baseRingHom A B hA X.1 X.2) M (I ^ n)) s =
      SheafOfModules.sectionsMap (idealQuotientπ (baseRingHom A B hA X.1 X.2) M (I ^ n)) s') →
    s = s') ∧
  (∀ t : ∀ n, (idealQuotient (baseRingHom A B hA X.1 X.2) M (I ^ n)).sections,
    (∀ (m n : ℕ) (hmn : m ≤ n), SheafOfModules.sectionsMap
      (idealQuotientMap (baseRingHom A B hA X.1 X.2) M (Ideal.pow_le_pow_right hmn)) (t n) = t m) →
    ∃ s : M.sections, ∀ n, SheafOfModules.sectionsMap
      (idealQuotientπ (baseRingHom A B hA X.1 X.2) M (I ^ n)) s = t n)

/-- **The theorem on formal functions in degree zero for a coherent module on a proper algebraic
space** over the spectrum of an `I`-adically complete Noetherian ring (Stacks 08B0). -/
theorem sectionsFormal_of_isProper [IsNoetherianRing A] {X : AlgebraicSpaces B (Spec (.of A)) hA}
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f.hom)
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) [IsCoherent B (Spec (.of A)) hA X.1 X.2 F]
    (I : Ideal A) [IsAdicComplete I A] : SectionsFormal X F I :=
  ⟨fun _ _ h => eq_of_sectionsMap_idealQuotientπ_eq f hf F I h,
    fun t ht => exists_sectionsMap_idealQuotientπ_eq f hf F I t ht⟩

/-! ### Invariance under isomorphism -/

section Iso

variable {X : AlgebraicSpaces B (Spec (.of A)) hA}

/-- The map `M / J M ⟶ N / J N` induced by `M ⟶ N`. -/
def idealQuotientMapOfHom {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2} (q : M ⟶ N)
    (J : Ideal A) :
    idealQuotient (baseRingHom A B hA X.1 X.2) M J ⟶
      idealQuotient (baseRingHom A B hA X.1 X.2) N J :=
  cokernel.desc _ (q ≫ idealQuotientπ (baseRingHom A B hA X.1 X.2) N J) (by
    refine idealMultiple_hom_ext _ M J fun a ha => ?_
    rw [comp_zero, ← Category.assoc, ← Category.assoc, idealMultipleFactor_ι, ← comp_globalSmul,
      Category.assoc, ← comp_globalSmul, globalSmul_idealQuotient_eq_zero _ N J ha, comp_zero,
      comp_zero])

/-- The quotient map followed by `idealQuotientMapOfHom q` is `q` followed by the quotient map. -/
@[reassoc (attr := simp)]
theorem idealQuotientπ_idealQuotientMapOfHom {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (q : M ⟶ N) (J : Ideal A) :
    idealQuotientπ (baseRingHom A B hA X.1 X.2) M J ≫ idealQuotientMapOfHom q J =
      q ≫ idealQuotientπ (baseRingHom A B hA X.1 X.2) N J :=
  cokernel.π_desc _ _ _

/-- `idealQuotientMapOfHom` is compatible with composition. -/
theorem idealQuotientMapOfHom_comp {M N P : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (q : M ⟶ N) (q' : N ⟶ P) (J : Ideal A) :
    idealQuotientMapOfHom q J ≫ idealQuotientMapOfHom q' J = idealQuotientMapOfHom (q ≫ q') J := by
  refine (cancel_epi (idealQuotientπ (baseRingHom A B hA X.1 X.2) M J)).1 ?_
  simp

/-- `idealQuotientMapOfHom` sends the identity to the identity. -/
theorem idealQuotientMapOfHom_id (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (J : Ideal A) :
    idealQuotientMapOfHom (𝟙 M) J = 𝟙 _ := by
  refine (cancel_epi (idealQuotientπ (baseRingHom A B hA X.1 X.2) M J)).1 ?_
  simp

/-- `idealQuotientMapOfHom q` commutes with the transition maps `M / J M ⟶ M / K M` for
`J ≤ K`. -/
theorem idealQuotientMapOfHom_idealQuotientMap {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (q : M ⟶ N) {J K : Ideal A} (hJK : J ≤ K) :
    idealQuotientMapOfHom q J ≫ idealQuotientMap (baseRingHom A B hA X.1 X.2) N hJK =
      idealQuotientMap (baseRingHom A B hA X.1 X.2) M hJK ≫ idealQuotientMapOfHom q K := by
  refine (cancel_epi (idealQuotientπ (baseRingHom A B hA X.1 X.2) M J)).1 ?_
  simp

/-- Sections of `M / J M` coming from `N` via `q` are computed by `idealQuotientMapOfHom q J`. -/
private theorem sectionsMap_idealQuotientπ_sectionsMap
    {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2} (q : M ⟶ N) (J : Ideal A)
    (s : M.sections) :
    SheafOfModules.sectionsMap (idealQuotientπ (baseRingHom A B hA X.1 X.2) N J)
        (SheafOfModules.sectionsMap q s) =
      SheafOfModules.sectionsMap (idealQuotientMapOfHom q J)
        (SheafOfModules.sectionsMap (idealQuotientπ (baseRingHom A B hA X.1 X.2) M J) s) := by
  rw [← SheafOfModules.sectionsMap_comp, ← SheafOfModules.sectionsMap_comp,
    idealQuotientπ_idealQuotientMapOfHom]

/-- `SectionsFormal` transports along an isomorphism. -/
theorem sectionsFormal_of_iso {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2} (e : M ≅ N)
    (I : Ideal A) (h : SectionsFormal X M I) : SectionsFormal X N I := by
  refine ⟨fun s s' hss => ?_, fun t ht => ?_⟩
  · have hinj : Function.Injective (SheafOfModules.sectionsMap e.inv) :=
      Function.LeftInverse.injective (g := SheafOfModules.sectionsMap e.hom) fun a => by
        rw [← SheafOfModules.sectionsMap_comp, e.inv_hom_id, SheafOfModules.sectionsMap_id]
    refine hinj (h.1 _ _ fun n => ?_)
    rw [sectionsMap_idealQuotientπ_sectionsMap, sectionsMap_idealQuotientπ_sectionsMap, hss n]
  · obtain ⟨s, hs⟩ := h.2 (fun n => SheafOfModules.sectionsMap (idealQuotientMapOfHom e.inv (I ^ n))
      (t n)) fun m n hmn => by
        rw [← SheafOfModules.sectionsMap_comp, idealQuotientMapOfHom_idealQuotientMap,
          SheafOfModules.sectionsMap_comp, ht m n hmn]
    refine ⟨SheafOfModules.sectionsMap e.hom s, fun n => ?_⟩
    rw [sectionsMap_idealQuotientπ_sectionsMap, hs n, ← SheafOfModules.sectionsMap_comp,
      idealQuotientMapOfHom_comp, e.inv_hom_id, idealQuotientMapOfHom_id,
      SheafOfModules.sectionsMap_id]

end Iso

/-! ### Direct images along closed immersions -/

section Pushforward

variable {Z X : AlgebraicSpaces B (Spec (.of A)) hA} (i : Z ⟶ X)
  (hi : IsClosedImmersion B (Spec (.of A)) hA i.hom)

/-- Every power of an ideal of a Noetherian ring is spanned by a finite family. -/
theorem exists_generators_pow [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    ∃ (r : ℕ) (g : Fin r → A), Ideal.span (Set.range g) = I ^ n :=
  Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian _)

include hi in
/-- **`SectionsFormal` passes to the direct image along a closed immersion.** -/
theorem sectionsFormal_pushforward [IsNoetherianRing A]
    (H : Modules.{u, u} B (Spec (.of A)) hA Z.1 Z.2) (I : Ideal A) (h : SectionsFormal Z H I) :
    SectionsFormal X ((modulePushforward B (Spec (.of A)) hA i).obj H) I := by
  choose r g hg using exists_generators_pow (A := A) I
  let κ : ∀ n, _ ≅ _ := fun n => pushforwardIdealQuotientIso i hi H (g n) (hg n)
  have hκ : ∀ n, (modulePushforward B (Spec (.of A)) hA i).map
      (idealQuotientπ (baseRingHom A B hA Z.1 Z.2) H (I ^ n)) =
        idealQuotientπ (baseRingHom A B hA X.1 X.2) _ (I ^ n) ≫ (κ n).inv := fun n => by
    rw [← pushforward_map_idealQuotientπ_pushforwardIdealQuotientIso_hom i hi H (g n) (hg n),
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hκtr : ∀ (m n : ℕ) (hmn : m ≤ n),
      (κ n).inv ≫ (modulePushforward B (Spec (.of A)) hA i).map
        (idealQuotientMap (baseRingHom A B hA Z.1 Z.2) H (Ideal.pow_le_pow_right hmn)) =
      idealQuotientMap (baseRingHom A B hA X.1 X.2) _ (Ideal.pow_le_pow_right hmn) ≫
        (κ m).inv := fun m n hmn => by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact pushforwardIdealQuotientIso_naturality i hi H (g n) (hg n) (g m) (hg m)
      (Ideal.pow_le_pow_right hmn)
  let σ := fun M => modulePushforwardSectionsEquiv B (Spec (.of A)) hA i M
  refine ⟨fun s s' hss => ?_, fun t ht => ?_⟩
  · refine (σ H).injective (h.1 _ _ fun n => ?_)
    rw [← modulePushforwardSectionsEquiv_naturality, ← modulePushforwardSectionsEquiv_naturality,
      hκ n, SheafOfModules.sectionsMap_comp, SheafOfModules.sectionsMap_comp, hss n]
  · obtain ⟨s, hs⟩ := h.2 (fun n => σ _ (SheafOfModules.sectionsMap (κ n).inv (t n)))
      fun m n hmn => by
        rw [← modulePushforwardSectionsEquiv_naturality, ← SheafOfModules.sectionsMap_comp,
          hκtr m n hmn, SheafOfModules.sectionsMap_comp, ht m n hmn]
    refine ⟨(σ H).symm s, fun n => ?_⟩
    rw [← pushforward_map_idealQuotientπ_pushforwardIdealQuotientIso_hom i hi H (g n) (hg n),
      SheafOfModules.sectionsMap_comp, ← modulePushforwardSectionsEquiv_symm_sectionsMap, hs n,
      Equiv.symm_apply_apply, ← SheafOfModules.sectionsMap_comp]
    show SheafOfModules.sectionsMap ((κ n).inv ≫ (κ n).hom) (t n) = t n
    rw [Iso.inv_hom_id, SheafOfModules.sectionsMap_id]

end Pushforward

/-! ### Modules with proper support -/

/-- **The theorem on formal functions in degree zero for a coherent module with proper
support.**  Let `A` be a Noetherian ring complete with respect to an ideal `I`, `X` a locally
Noetherian algebraic space locally of finite type over `Spec A`, and `M` a coherent `𝒪_X`-module
whose support is proper over `Spec A`.  Then `Γ(X, M) = lim_n Γ(X, M / Iⁿ M)`. -/
theorem sectionsFormal_of_hasProperSupport [IsNoetherianRing A]
    (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (hLN : HasEtaleLocalProperty B (Spec (.of A)) hA X.1
      (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (f : X ⟶ schemeSpace (baseObject A B hA))
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)
    (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) [hM : IsCoherent B (Spec (.of A)) hA X.1 X.2 M]
    (hsupp : HasProperSupport B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf
      ((SheafOfModules.toSheaf _).obj M))
    (I : Ideal A) [IsAdicComplete I A] : SectionsFormal X M I := by
  have hFTsite := isFiniteTypeOnSite_of_isCoherentOnSite B (Spec (.of A)) hA X M
  have hFT := Stacks.SheafOfModules.presheafIsFiniteType_of_isFiniteTypeOnSite M hFTsite
  obtain ⟨Z, G, hG, -, hZp, ⟨e⟩⟩ := (hasProperSupport_tfae B (Spec (.of A)) hA X
    (schemeSpace (baseObject A B hA)) f.hom hf M hM.toIsQuasicoherentOnSite hFTsite hFT).out 1 3
    |>.1 hsupp
  have := isCoherent_of_modulePushforward_closedSubspace B (Spec (.of A)) hA X hLN M Z G hG e
  exact sectionsFormal_of_iso e I (sectionsFormal_pushforward _ Z.2.2 G I
    (sectionsFormal_of_isProper (closedSubspaceInclusion B (Spec (.of A)) hA X Z ≫ f) hZp G I))

end AlgebraicGeometry.Space.C1573

end
