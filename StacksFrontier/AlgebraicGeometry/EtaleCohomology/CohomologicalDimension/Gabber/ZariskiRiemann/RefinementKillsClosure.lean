module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.RefinementKilledSubsheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ProperModelCofiltered

/-!
# Closure properties of the killing relation of refinements of proper models

For a refinement `π : Y' ⟶ Y` of proper models of `η = Spec (Frac B)` and `G = R^q j_* F` on `Y`,
`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.Kills` says that `π` kills a
morphism `ι : K ⟶ G`. This file proves the closure properties used to build the filtered system of
killed subsheaves of `G` of the finite-level limit step in Gabber's Zariski–Riemann proof of
Travaux de Gabber, Exposé XVIII-A, Corollary 1.2 (last remark of §2):

* the morphisms killed by a fixed refinement are closed under precomposition, sums, maps out of
  coproducts, and descend along epimorphisms; in particular `π` kills the image of a killed
  morphism;
* given the two inputs that make the system of models cofiltered — killing is stable under further
  refinement (`AlgebraicGeometry.Scheme.ZariskiRiemann.KillsStableUnderRefinement`, the cocycle of
  the degree `q` base change maps of the squares `𝟙 ≫ j = j' ≫ π`) and two refinements of a model
  have a common refinement (`AlgebraicGeometry.Scheme.ZariskiRiemann.RefinementsCofiltered`) —
  finitely many killed morphisms are killed by one common refinement, and hence so is the image of
  the map out of their coproduct.

## Main definitions

* `AlgebraicGeometry.Scheme.ZariskiRiemann.KillsStableUnderRefinement` — killing is stable under
  further refinement.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.RefinementsCofiltered` — two refinements of a model
  have a common refinement, with equal composites.

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.Kills.image_ι` — a refinement
  killing `f` kills the image of `f`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.Kills.sigmaDesc` — a refinement
  killing every `ε_j` kills the map out of the coproduct.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.exists_refinement_forall_kills` — finitely
  many killed morphisms have a common killing refinement.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.exists_refinement_kills_image_sigmaDesc` —
  the image of finitely many killed morphisms is killed by one refinement.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* SGA 4, Exposé VI, 8.7.4
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

open Stacks.EtaleCohomology

variable {B : Type u} [CommRing B] [IsDomain B]

namespace ProperModel

-- `Refinement.ext` and `Refinement.id` are in `ProperModelCofiltered.lean`.

variable {M' M : ProperModel B} (φ : Refinement M' M)
  (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)

namespace Refinement.Kills

variable {φ F q}

omit [IsDomain B] in
/-- A refinement kills the zero morphism. -/
theorem zero (K : Sheaf M.Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    φ.Kills F q (0 : K ⟶ ((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F) := by
  rw [Refinement.Kills, Functor.map_zero, zero_comp]

omit [IsDomain B] in
/-- The morphisms killed by a refinement are closed under sums. -/
theorem add {K : Sheaf M.Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {ι ι' : K ⟶ ((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F}
    (h : φ.Kills F q ι) (h' : φ.Kills F q ι') : φ.Kills F q (ι + ι') := by
  rw [Refinement.Kills] at h h' ⊢
  rw [Functor.map_add, Preadditive.add_comp, h, h', add_zero]

omit [IsDomain B] in
/-- The morphisms killed by a refinement are closed under precomposition. -/
theorem comp_left {K K' : Sheaf M.Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (a : K' ⟶ K)
    {ι : K ⟶ ((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F}
    (h : φ.Kills F q ι) : φ.Kills F q (a ≫ ι) := by
  rw [Refinement.Kills] at h ⊢
  rw [Functor.map_comp, Category.assoc, h, comp_zero]

omit [IsDomain B] in
/-- Killing descends along epimorphisms: inverse image preserves them, being a left adjoint. -/
theorem of_epi_comp {K K' : Sheaf M.Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (a : K' ⟶ K)
    [Epi a] {ι : K ⟶ ((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F}
    (h : φ.Kills F q (a ≫ ι)) : φ.Kills F q ι := by
  rw [Refinement.Kills] at h ⊢
  rw [Functor.map_comp, Category.assoc] at h
  rw [← cancel_epi ((etaleAbelianInverseImage.{u, 0} φ.π).map a), h, comp_zero]

omit [IsDomain B] in
/-- **A refinement killing `f` kills the image of `f`.** -/
theorem image_ι {K : Sheaf M.Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {f : K ⟶ ((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F}
    (h : φ.Kills F q f) : φ.Kills F q (image.ι f) :=
  of_epi_comp (factorThruImage f) (by rwa [image.fac])

omit [IsDomain B] in
/-- **A refinement killing every `ε_j` kills the map out of the coproduct**: inverse image
preserves coproducts, being a left adjoint. -/
theorem sigmaDesc {J : Type (u + 1)} {K : J → Sheaf M.Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    [HasCoproduct K]
    {ε : ∀ j, K j ⟶ ((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F}
    (h : ∀ j, φ.Kills F q (ε j)) : φ.Kills F q (Sigma.desc ε) := by
  rw [Refinement.Kills]
  have hc := isColimitOfPreserves (etaleAbelianInverseImage.{u, 0} φ.π)
    (coproductIsCoproduct K)
  refine hc.hom_ext fun j ↦ ?_
  have hj := h j.as
  rw [Refinement.Kills] at hj
  simp only [Functor.mapCocone_ι_app, comp_zero]
  rw [← Category.assoc, ← Functor.map_comp]
  simpa using hj

end Refinement.Kills

end ProperModel

/-- **Killing is stable under further refinement.** If `π : Y' ⟶ Y` kills `ι : K ⟶ R^q j_* F`,
so does every composite `Y'' ⟶ Y' ⟶ Y`. This is a consequence of the cocycle condition for the
degree `q` base change maps of the squares `𝟙 ≫ j = j' ≫ π`: the base change map of the
composite is `ψ⁻¹` of that of `π` followed by that of `ψ`, up to the composition isomorphisms of
inverse images (the derived form is
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_comp_app`). -/
def KillsStableUnderRefinement (B : Type u) [CommRing B] [IsDomain B] : Prop :=
  ∀ (M'' M' M : ProperModel B) (ψ : ProperModel.Refinement M'' M')
    (φ : ProperModel.Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (K : Sheaf M.Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (ι : K ⟶ ((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F),
    φ.Kills F q ι → (ψ.comp φ).Kills F q ι

/-- **The models are cofiltered**, in the form used here: two refinements `Y₁ ⟶ Y` and `Y₂ ⟶ Y`
of a model have a common refinement `Y₃` with refinements `Y₃ ⟶ Y₁`, `Y₃ ⟶ Y₂` whose composites
to `Y` agree (in the source, the closure of `η` in `Y₁ ×_Y Y₂`). -/
def RefinementsCofiltered (B : Type u) [CommRing B] [IsDomain B] : Prop :=
  ∀ (M₁ M₂ M : ProperModel B) (φ₁ : ProperModel.Refinement M₁ M)
    (φ₂ : ProperModel.Refinement M₂ M),
    ∃ (M₃ : ProperModel B) (ψ₁ : ProperModel.Refinement M₃ M₁)
      (ψ₂ : ProperModel.Refinement M₃ M₂), ψ₁.π ≫ φ₁.π = ψ₂.π ≫ φ₂.π

namespace ProperModel

variable (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1})
  (q : ℕ)

/-- **Finitely many killed morphisms have a common killing refinement**, given that killing is
stable under refinement and that refinements have common refinements. -/
theorem exists_refinement_forall_kills (hstab : KillsStableUnderRefinement B)
    (hcof : RefinementsCofiltered B) (M : ProperModel B) {J : Type*} [Finite J]
    {K : J → Sheaf M.Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ε : ∀ j, K j ⟶ ((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F)
    (hkill : ∀ j, ∃ (M' : ProperModel B) (φ : Refinement M' M), φ.Kills F q (ε j)) :
    ∃ (M' : ProperModel B) (φ : Refinement M' M), ∀ j, φ.Kills F q (ε j) := by
  classical
  have hfin := Fintype.ofFinite J
  suffices h : ∀ T : Finset J, ∃ (M' : ProperModel B) (φ : Refinement M' M),
      ∀ j ∈ T, φ.Kills F q (ε j) by
    obtain ⟨M', φ, hφ⟩ := h Finset.univ
    exact ⟨M', φ, fun j ↦ hφ j (Finset.mem_univ j)⟩
  intro T
  induction T using Finset.induction_on with
  | empty => exact ⟨M, Refinement.id M, fun j hj ↦ absurd hj (Finset.notMem_empty j)⟩
  | insert j T _ ih =>
    obtain ⟨M₁, φ₁, h₁⟩ := ih
    obtain ⟨M₂, φ₂, h₂⟩ := hkill j
    obtain ⟨M₃, ψ₁, ψ₂, hψ⟩ := hcof M₁ M₂ M φ₁ φ₂
    have heq : ψ₂.comp φ₂ = ψ₁.comp φ₁ := Refinement.ext hψ.symm
    refine ⟨M₃, ψ₁.comp φ₁, fun i hi ↦ ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · rw [← heq]
      exact hstab M₃ M₂ M ψ₂ φ₂ F q _ _ h₂
    · exact hstab M₃ M₁ M ψ₁ φ₁ F q _ _ (h₁ i hi)

/-- **The image of finitely many killed morphisms is killed by one refinement.** -/
theorem exists_refinement_kills_image_sigmaDesc (hstab : KillsStableUnderRefinement B)
    (hcof : RefinementsCofiltered B) (M : ProperModel B) {J : Type (u + 1)} [Finite J]
    {K : J → Sheaf M.Y.smallEtaleTopology AddCommGrpCat.{u + 1}} [HasCoproduct K]
    (ε : ∀ j, K j ⟶ ((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F)
    (hkill : ∀ j, ∃ (M' : ProperModel B) (φ : Refinement M' M), φ.Kills F q (ε j)) :
    ∃ (M' : ProperModel B) (φ : Refinement M' M), φ.Kills F q (image.ι (Sigma.desc ε)) := by
  obtain ⟨M', φ, hφ⟩ := exists_refinement_forall_kills F q hstab hcof M ε hkill
  exact ⟨M', φ, Refinement.Kills.image_ι (Refinement.Kills.sigmaDesc hφ)⟩

end ProperModel

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
