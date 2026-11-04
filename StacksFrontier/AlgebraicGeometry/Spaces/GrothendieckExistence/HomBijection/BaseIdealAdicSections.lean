module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.BaseIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.FormalFunctionsProperSupport

/-!
# Global sections and the completion along `I 𝒪_X`

For an algebraic space `X` over `Spec A`, an ideal `I ⊆ A` and an `𝒪_X`-module `M` satisfying
the theorem on formal functions in degree zero (`AlgebraicGeometry.Space.C1573.SectionsFormal`),
the map from `Γ(X, M)` to the inverse limit of the global sections of the completion
`(M / (I 𝒪_X)^(n+1) M)_n` is bijective.

## Main definitions

* `AlgebraicGeometry.Space.C1573.adicSectionsOfSection`: a global section of `M` as a compatible
  family of global sections of the completion of `M` along `I 𝒪_X`.

## Main results

* `AlgebraicGeometry.Space.C1573.bijective_adicSectionsOfSection`: the map
  `Γ(X, M) ⟶ lim_n Γ(X, M / (I 𝒪_X)^(n+1) M)` is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space.C1573

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (X : AlgebraicSpaces B (Spec (.of A)) hA) (I : Ideal A)
  (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)

/-- A global section of `M`, read as a compatible family of global sections of the completion
of `M` along `I 𝒪_X`. -/
def adicSectionsOfSection (s : M.sections) :
    adicSections B (Spec (.of A)) hA X.1 X.2
      (fun n => smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
        (n + 1) M)
      (fun n => smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2
        (baseIdealSubmodule X.1 X.2 I) (n + 1) M) :=
  ⟨fun n => SheafOfModules.sectionsMap
      (smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
        (n + 1) M) s, fun n => by
    rw [← SheafOfModules.sectionsMap_comp, smallEtaleAdicQuotientProjection_comp_transition]⟩

/-- The identification `M / (I 𝒪_X)^k M ≅ M / I^k M` is compatible with the transition maps. -/
theorem baseIdealQuotientIso_transition (n : ℕ) :
    smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
          n M ≫
        (baseIdealQuotientIso M I n).hom =
      (baseIdealQuotientIso M I (n + 1)).hom ≫
        idealQuotientMap (baseRingHom A B hA X.1 X.2) M
          (Ideal.pow_le_pow_right (Nat.le_succ n)) := by
  refine (cancel_epi (smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2
    (baseIdealSubmodule X.1 X.2 I) (n + 1) M)).1 ?_
  rw [← Category.assoc, smallEtaleAdicQuotientProjection_comp_transition,
    smallEtaleAdicQuotientProjection_baseIdealQuotientIso_hom, ← Category.assoc,
    smallEtaleAdicQuotientProjection_baseIdealQuotientIso_hom, idealQuotientπ_idealQuotientMap]

/-- The map on global sections induced by an isomorphism of sheaves of modules is injective. -/
theorem injective_sectionsMap_of_iso {P Q : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (e : P ≅ Q) :
    Function.Injective (SheafOfModules.sectionsMap e.hom) := fun a b hab => by
  have := congrArg (SheafOfModules.sectionsMap e.inv) hab
  rwa [← SheafOfModules.sectionsMap_comp, ← SheafOfModules.sectionsMap_comp, e.hom_inv_id,
    SheafOfModules.sectionsMap_id, SheafOfModules.sectionsMap_id] at this

/-- **`Γ(X, M) ⟶ lim_n Γ(X, M / (I 𝒪_X)^(n+1) M)` is bijective** when `M` satisfies the theorem
on formal functions in degree zero. -/
theorem bijective_adicSectionsOfSection (h : SectionsFormal X M I) :
    Function.Bijective (adicSectionsOfSection X I M) := by
  have hπ : ∀ n (s : M.sections), SheafOfModules.sectionsMap
      (idealQuotientπ (baseRingHom A B hA X.1 X.2) M (I ^ (n + 1))) s =
        SheafOfModules.sectionsMap (baseIdealQuotientIso M I (n + 1)).hom
          ((adicSectionsOfSection X I M s).1 n) := fun n s => by
    rw [← smallEtaleAdicQuotientProjection_baseIdealQuotientIso_hom,
      SheafOfModules.sectionsMap_comp]
    rfl
  have hπ0 : ∀ s : M.sections, SheafOfModules.sectionsMap
      (idealQuotientπ (baseRingHom A B hA X.1 X.2) M (I ^ 0)) s =
        SheafOfModules.sectionsMap (idealQuotientMap (baseRingHom A B hA X.1 X.2) M
          (Ideal.pow_le_pow_right (Nat.zero_le 1)))
          (SheafOfModules.sectionsMap (idealQuotientπ (baseRingHom A B hA X.1 X.2) M (I ^ 1)) s) :=
    fun s => by rw [← SheafOfModules.sectionsMap_comp, idealQuotientπ_idealQuotientMap]
  refine ⟨fun s s' hss => h.1 s s' fun n => ?_, fun a => ?_⟩
  · have hn : ∀ n, SheafOfModules.sectionsMap
        (idealQuotientπ (baseRingHom A B hA X.1 X.2) M (I ^ (n + 1))) s =
        SheafOfModules.sectionsMap
          (idealQuotientπ (baseRingHom A B hA X.1 X.2) M (I ^ (n + 1))) s' := fun n => by
      rw [hπ, hπ, hss]
    cases n with
    | zero => rw [hπ0, hπ0, hn 0]
    | succ n => exact hn n
  · let t : ∀ n, (idealQuotient (baseRingHom A B hA X.1 X.2) M (I ^ n)).sections
      | 0 => SheafOfModules.sectionsMap (idealQuotientMap (baseRingHom A B hA X.1 X.2) M
          (Ideal.pow_le_pow_right (Nat.zero_le 1)))
            (SheafOfModules.sectionsMap (baseIdealQuotientIso M I 1).hom (a.1 0))
      | n + 1 => SheafOfModules.sectionsMap (baseIdealQuotientIso M I (n + 1)).hom (a.1 n)
    have hsucc : ∀ n, SheafOfModules.sectionsMap (idealQuotientMap (baseRingHom A B hA X.1 X.2) M
        (Ideal.pow_le_pow_right (Nat.le_succ n))) (t (n + 1)) = t n := by
      intro n
      cases n with
      | zero => rfl
      | succ n =>
        dsimp only [t]
        rw [← SheafOfModules.sectionsMap_comp, ← baseIdealQuotientIso_transition,
          SheafOfModules.sectionsMap_comp, a.2 n]
    have hall : ∀ (m n : ℕ) (hmn : m ≤ n), SheafOfModules.sectionsMap
        (idealQuotientMap (baseRingHom A B hA X.1 X.2) M (Ideal.pow_le_pow_right hmn)) (t n) =
          t m := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => rw [idealQuotientMap_refl, SheafOfModules.sectionsMap_id]
      | succ n hmn ih =>
        refine Eq.trans ?_ ((congrArg (SheafOfModules.sectionsMap (idealQuotientMap
          (baseRingHom A B hA X.1 X.2) M (Ideal.pow_le_pow_right hmn))) (hsucc n)).trans ih)
        conv_rhs => rw [← SheafOfModules.sectionsMap_comp]
        rw [idealQuotientMap_comp]
    obtain ⟨s, hs⟩ := h.2 t hall
    refine ⟨s, Subtype.ext (funext fun n => ?_)⟩
    refine injective_sectionsMap_of_iso X (baseIdealQuotientIso M I (n + 1)) ?_
    rw [← hπ, hs (n + 1)]

end AlgebraicGeometry.Space.C1573

end
