module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicInternalHom

/-!
# The map from global sections to the limit of the sections of the ideal-power quotients

Let `F` be an algebraic space, `𝓘 ⊆ 𝒪_F` a sheaf of ideals and `K` an `𝒪_F`-module, with
sections in any universe.  The projections `K ⟶ K / 𝓘 ^ (n + 1) K` assemble into the map

`H⁰(F, K) ⟶ limₙ H⁰(F, K / 𝓘 ^ (n + 1) K)`,

whose bijectivity is the theorem on formal functions in degree zero.  The target is
`AlgebraicGeometry.Space.adicSections` of the inverse system of the ideal-power quotients of
`AlgebraicGeometry.Space.smallEtaleAdicQuotient`, which is the left-hand side of Stacks 08B6 when
`K` is an internal hom.  This file defines the map, its functoriality in `K`, and the invariance
of its bijectivity under isomorphisms of `K`; these are the shared vocabulary of the proof of
Stacks 08B9 for algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleAdicQuotientMapOfModuleHom` — the map
  `K / 𝓘 ^ n K ⟶ K' / 𝓘 ^ n K'` induced by `K ⟶ K'`.
* `AlgebraicGeometry.Space.adicSectionsOfSections` — the map
  `H⁰(F, K) ⟶ limₙ H⁰(F, K / 𝓘 ^ (n + 1) K)`.

## Main results

* `AlgebraicGeometry.Space.adicSectionsMap_adicSectionsOfSections` — naturality in `K`.
* `AlgebraicGeometry.Space.bijective_adicSectionsOfSections_of_iso` — bijectivity is
  invariant under isomorphism of `K`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

variable [HasCokernels (Modules.{u, m} B S hS F hF)]

/-- A morphism `g : K ⟶ K'` carries `𝓘 ^ n K` into `𝓘 ^ n K'`, so it induces
`K / 𝓘 ^ n K ⟶ K' / 𝓘 ^ n K'`. -/
def smallEtaleAdicQuotientMapOfModuleHom (n : ℕ) {K K' : Modules.{u, m} B S hS F hF} (g : K ⟶ K') :
    smallEtaleAdicQuotient B S hS F hF 𝓘 n K ⟶ smallEtaleAdicQuotient B S hS F hF 𝓘 n K' :=
  cokernel.desc _ (g ≫ smallEtaleAdicQuotientProjection B S hS F hF 𝓘 n K') (by
    refine (idealPowerSubsheaf_ι_comp_zero_iff B S hS F hF 𝓘 n _).mpr fun U r hr x => ?_
    change (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 n K').val.app (op U)
      (g.val.app (op U) (r • x)) = 0
    rw [map_smul]
    have hz := (idealPowerSubsheaf_ι_comp_zero_iff B S hS F hF 𝓘 n
      (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 n K')).mp (cokernel.condition _) U r hr
      (g.val.app (op U) x)
    exact hz)

/-- The projection `K ⟶ K / 𝓘 ^ n K` followed by the induced map equals `g` followed by the
projection `K' ⟶ K' / 𝓘 ^ n K'`. -/
@[reassoc (attr := simp)]
theorem smallEtaleAdicQuotientProjection_comp_mapOfHom (n : ℕ)
    {K K' : Modules.{u, m} B S hS F hF} (g : K ⟶ K') :
    smallEtaleAdicQuotientProjection B S hS F hF 𝓘 n K ≫
        smallEtaleAdicQuotientMapOfModuleHom B S hS F hF 𝓘 n g =
      g ≫ smallEtaleAdicQuotientProjection B S hS F hF 𝓘 n K' :=
  cokernel.π_desc _ _ _

/-- The map induced by a composite `g ≫ g'` is the composite of the induced maps. -/
theorem smallEtaleAdicQuotientMapOfModuleHom_comp (n : ℕ) {K K' K'' : Modules.{u, m} B S hS F hF}
    (g : K ⟶ K') (g' : K' ⟶ K'') :
    smallEtaleAdicQuotientMapOfModuleHom B S hS F hF 𝓘 n (g ≫ g') =
      smallEtaleAdicQuotientMapOfModuleHom B S hS F hF 𝓘 n g ≫
        smallEtaleAdicQuotientMapOfModuleHom B S hS F hF 𝓘 n g' := by
  refine (cancel_epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 n K)).mp ?_
  simp

/-- The map induced by the identity of `K` is the identity of `K / 𝓘 ^ n K`. -/
theorem smallEtaleAdicQuotientMapOfModuleHom_id (n : ℕ) (K : Modules.{u, m} B S hS F hF) :
    smallEtaleAdicQuotientMapOfModuleHom B S hS F hF 𝓘 n (𝟙 K) = 𝟙 _ := by
  refine (cancel_epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 n K)).mp ?_
  simp

/-- The induced maps commute with the transition maps. -/
theorem smallEtaleAdicQuotientTransition_comp_mapOfHom (n : ℕ)
    {K K' : Modules.{u, m} B S hS F hF} (g : K ⟶ K') :
    smallEtaleAdicQuotientTransition B S hS F hF 𝓘 n K ≫
        smallEtaleAdicQuotientMapOfModuleHom B S hS F hF 𝓘 n g =
      smallEtaleAdicQuotientMapOfModuleHom B S hS F hF 𝓘 (n + 1) g ≫
        smallEtaleAdicQuotientTransition B S hS F hF 𝓘 n K' := by
  refine (cancel_epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) K)).mp ?_
  rw [← Category.assoc, smallEtaleAdicQuotientProjection_comp_transition,
    smallEtaleAdicQuotientProjection_comp_mapOfHom, ← Category.assoc,
    smallEtaleAdicQuotientProjection_comp_mapOfHom, Category.assoc,
    smallEtaleAdicQuotientProjection_comp_transition]

/-- **The map `H⁰(F, K) ⟶ limₙ H⁰(F, K / 𝓘 ^ (n + 1) K)`**, assembled from the projections. -/
def adicSectionsOfSections (K : Modules.{u, m} B S hS F hF) (σ : K.sections) :
    adicSections B S hS F hF (fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) K)
      (fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) K) :=
  ⟨fun n => SheafOfModules.sectionsMap (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) K)
      σ, fun n => by
    rw [← SheafOfModules.sectionsMap_comp, smallEtaleAdicQuotientProjection_comp_transition]⟩

/-- The components of `adicSectionsOfSections`. -/
@[simp]
theorem adicSectionsOfSections_coe (K : Modules.{u, m} B S hS F hF) (σ : K.sections) (n : ℕ) :
    (adicSectionsOfSections B S hS F hF 𝓘 K σ).1 n =
      SheafOfModules.sectionsMap (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) K) σ :=
  rfl

/-- **Naturality** of `adicSectionsOfSections` in the module. -/
theorem adicSectionsMap_adicSectionsOfSections {K K' : Modules.{u, m} B S hS F hF} (g : K ⟶ K')
    (σ : K.sections) :
    adicSectionsMap B S hS F hF _ _ _ _
        (fun n => smallEtaleAdicQuotientMapOfModuleHom B S hS F hF 𝓘 (n + 1) g)
        (fun n => smallEtaleAdicQuotientTransition_comp_mapOfHom B S hS F hF 𝓘 (n + 1) g)
        (adicSectionsOfSections B S hS F hF 𝓘 K σ) =
      adicSectionsOfSections B S hS F hF 𝓘 K' (SheafOfModules.sectionsMap g σ) := by
  refine Subtype.ext (funext fun n => ?_)
  show SheafOfModules.sectionsMap _ (SheafOfModules.sectionsMap _ σ) =
    SheafOfModules.sectionsMap _ (SheafOfModules.sectionsMap _ σ)
  rw [← SheafOfModules.sectionsMap_comp, ← SheafOfModules.sectionsMap_comp,
    smallEtaleAdicQuotientProjection_comp_mapOfHom]

/-- The action on the limits of the sections of the maps induced by `g` and `g'` compose. -/
theorem adicSectionsMap_mapOfHom_comp {K K' K'' : Modules.{u, m} B S hS F hF} (g : K ⟶ K')
    (g' : K' ⟶ K'')
    (s : adicSections B S hS F hF (fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) K)
      (fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) K)) :
    adicSectionsMap B S hS F hF _ _ _ _
        (fun n => smallEtaleAdicQuotientMapOfModuleHom B S hS F hF 𝓘 (n + 1) g')
        (fun n => smallEtaleAdicQuotientTransition_comp_mapOfHom B S hS F hF 𝓘 (n + 1) g')
        (adicSectionsMap B S hS F hF _ _ _ _
          (fun n => smallEtaleAdicQuotientMapOfModuleHom B S hS F hF 𝓘 (n + 1) g)
          (fun n => smallEtaleAdicQuotientTransition_comp_mapOfHom B S hS F hF 𝓘 (n + 1) g) s) =
      adicSectionsMap B S hS F hF _ _ _ _
        (fun n => smallEtaleAdicQuotientMapOfModuleHom B S hS F hF 𝓘 (n + 1) (g ≫ g'))
        (fun n => smallEtaleAdicQuotientTransition_comp_mapOfHom B S hS F hF 𝓘 (n + 1)
          (g ≫ g')) s := by
  refine Subtype.ext (funext fun n => ?_)
  show SheafOfModules.sectionsMap _ (SheafOfModules.sectionsMap _ _) =
    SheafOfModules.sectionsMap _ _
  rw [← SheafOfModules.sectionsMap_comp]
  exact congrArg (fun k => SheafOfModules.sectionsMap k (s.1 n))
    (smallEtaleAdicQuotientMapOfModuleHom_comp B S hS F hF 𝓘 (n + 1) g g').symm

/-- The action on the limits of the sections of the maps induced by the identity of `K` is the
identity. -/
theorem adicSectionsMap_mapOfHom_id (K : Modules.{u, m} B S hS F hF)
    (s : adicSections B S hS F hF (fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) K)
      (fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) K)) :
    adicSectionsMap B S hS F hF _ _ _ _
        (fun n => smallEtaleAdicQuotientMapOfModuleHom B S hS F hF 𝓘 (n + 1) (𝟙 K))
        (fun n => smallEtaleAdicQuotientTransition_comp_mapOfHom B S hS F hF 𝓘 (n + 1) (𝟙 K))
        s = s := by
  refine Subtype.ext (funext fun n => ?_)
  show SheafOfModules.sectionsMap _ _ = _
  exact (congrArg (fun k => SheafOfModules.sectionsMap k (s.1 n))
    (smallEtaleAdicQuotientMapOfModuleHom_id B S hS F hF 𝓘 (n + 1) K)).trans
      (SheafOfModules.sectionsMap_id _)

/-- **Bijectivity of `adicSectionsOfSections` is invariant under isomorphism** of the module. -/
theorem bijective_adicSectionsOfSections_of_iso {K K' : Modules.{u, m} B S hS F hF} (e : K ≅ K')
    (h : Function.Bijective (adicSectionsOfSections B S hS F hF 𝓘 K)) :
    Function.Bijective (adicSectionsOfSections B S hS F hF 𝓘 K') := by
  let Φ := fun {A A' : Modules.{u, m} B S hS F hF} (g : A ⟶ A') s => adicSectionsMap B S hS F hF
    _ _ _ _ (fun n => smallEtaleAdicQuotientMapOfModuleHom B S hS F hF 𝓘 (n + 1) g)
    (fun n => smallEtaleAdicQuotientTransition_comp_mapOfHom B S hS F hF 𝓘 (n + 1) g) s
  have hΦ : ∀ {A A' : Modules.{u, m} B S hS F hF} (g : A ⟶ A') (g' : A' ⟶ A), g ≫ g' = 𝟙 A →
      ∀ s, Φ g' (Φ g s) = s := fun g g' h s => by
    simp only [Φ]
    rw [adicSectionsMap_mapOfHom_comp, h, adicSectionsMap_mapOfHom_id]
  have hsec : ∀ {A A' : Modules.{u, m} B S hS F hF} (g : A ⟶ A') (g' : A' ⟶ A), g ≫ g' = 𝟙 A →
      ∀ σ : A.sections, SheafOfModules.sectionsMap g' (SheafOfModules.sectionsMap g σ) = σ :=
    fun g g' h σ => by
    rw [← SheafOfModules.sectionsMap_comp, h, SheafOfModules.sectionsMap_id]
  have key : ∀ σ : K'.sections, adicSectionsOfSections B S hS F hF 𝓘 K' σ =
      Φ e.hom (adicSectionsOfSections B S hS F hF 𝓘 K (SheafOfModules.sectionsMap e.inv σ)) :=
    fun σ => by
      simp only [Φ]
      rw [adicSectionsMap_adicSectionsOfSections, hsec _ _ e.inv_hom_id]
  refine ⟨fun σ σ' hσ => ?_, fun t => ?_⟩
  · rw [key σ, key σ'] at hσ
    have := h.1 (congrArg (Φ e.inv) hσ |>.symm.trans (hΦ _ _ e.hom_inv_id _) |>.symm.trans
      (hΦ _ _ e.hom_inv_id _))
    rw [← hsec _ _ e.inv_hom_id σ, ← hsec _ _ e.inv_hom_id σ', this]
  · obtain ⟨σ, hσ⟩ := h.2 (Φ e.inv t)
    refine ⟨SheafOfModules.sectionsMap e.hom σ, ?_⟩
    rw [key, hsec _ _ e.hom_inv_id, hσ, hΦ _ _ e.inv_hom_id]

end AlgebraicGeometry.Space

end
