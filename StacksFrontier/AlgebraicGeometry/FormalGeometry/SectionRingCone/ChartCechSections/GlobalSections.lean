module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionRingCone.ChartCechSections.Charts
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonReading

/-!
# Global sections of the tensor powers as Čech cocycles of the section ring

Let `L` be an ample invertible module on `X` with section ring `A = Γ_*(X, L)`, and let
`t₁, …, t_r ∈ A₁` have affine nonvanishing opens covering `X`. For every `m ≥ 0` the sheaf
condition for this cover, read through the chart identifications of
`Stacks.Algebraization.SectionRingCone.singletonChart` and `pairChart`, identifies `Γ(X, L^{⊗ m})`
with the degree-`m` part of the degree-one Čech cocycles of `t` with coefficients in `A`, that is
with the degree-`m` part of `Γ(Spec A ∖ V(t), Ã)`.

## Main definitions

* `Stacks.Algebraization.SectionRingCone.globalCechSection` — the map
  `Γ(X, L^{⊗ m}) → ker(d¹)`.

## Main results

* `Stacks.Algebraization.SectionRingCone.globalCechSection_mem_kerDegree`,
  `globalCechSection_injective`, `exists_globalCechSection_eq` — it is a bijection onto the
  degree-`m` cocycles.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
  TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections sectionRing)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading)

open Stacks.AlgebraicGeometry.TopDegreeBaseChange (presheaf_map_homOfLE_comp)

attribute [local instance] instVAddNatIntGradedLocalizedModule

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

universe u

namespace Stacks.Algebraization.SectionRingCone

/-! ### Generalities -/

/-- **Čech compatibility from the pairs.** A family of degree-one Čech cochains whose images agree
in every `M_{f_a f_b}` is compatible in every further localization. -/
theorem mem_cechCompatible_of_pairs {R : Type*} [CommRing R] {r : ℕ} (f : Fin r → R)
    (M : ModuleCat R) (x : ∀ i : Fin r, Cech.cechMod f (M : Type _) {i})
    (h : ∀ a b : Fin r, a ≠ b →
      Cech.cechι f (M : Type _) (Finset.singleton_subset_iff.2 (Finset.mem_insert_self a {b}))
          (x a) =
        Cech.cechι f (M : Type _)
          (Finset.singleton_subset_iff.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self b)))
          (x b)) :
    x ∈ Stacks.LocalCohomology.cechCompatible f M := by
  intro a b t ha hb
  obtain rfl | hab := eq_or_ne a b
  · rfl
  have hsub : ({a, b} : Finset (Fin r)) ⊆ t :=
    Finset.insert_subset_iff.2 ⟨ha, Finset.singleton_subset_iff.2 hb⟩
  rw [← Cech.cechι_cechι f (M : Type _) (Finset.singleton_subset_iff.2
      (Finset.mem_insert_self a {b})) hsub,
    ← Cech.cechι_cechι f (M : Type _) (Finset.singleton_subset_iff.2
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))) hsub,
    h a b hab]

/-- The degree-`e` part of the degree-one Čech term, coordinatewise. -/
theorem mem_gradedCechTerm_one_iff {R : Type*} [CommRing R] {σ' τ' : Type*} [SetLike σ' R]
    (𝒜 : ℕ → σ') {r : ℕ} (f : Fin r → R) (M : ModuleCat R) [SetLike τ' M] (𝒢 : ℤ → τ') (e : ℤ)
    (z : Cech.cechTerm f (M : Type _) 1) :
    z ∈ Cech.gradedCechTerm 𝒜 𝒢 f e 1 ↔
      ∀ j : Fin r, Stacks.LocalCohomology.cechTermOneEquiv f M z j ∈
        Stacks.GradedLocalization.gradedPiece 𝒜 𝒢 (∏ i ∈ ({j} : Finset (Fin r)), f i) e := by
  constructor
  · intro h j
    exact h ⟨{j}, Finset.card_singleton j⟩
  · rintro h ⟨s, hs⟩
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hs
    exact h j

/-- Two degree-one cocycles with the same coordinates are equal. -/
theorem kerCechDOne_ext {R : Type*} [CommRing R] {r : ℕ} (f : Fin r → R) (M : ModuleCat R)
    {x y : LinearMap.ker (Cech.cechD f (M : Type _) 1)}
    (h : ∀ j, Stacks.LocalCohomology.cechTermOneEquiv f M x.1 j =
      Stacks.LocalCohomology.cechTermOneEquiv f M y.1 j) : x = y :=
  Subtype.ext ((Stacks.LocalCohomology.cechTermOneEquiv f M).injective (funext h))

/-- Restriction along an equality of opens is injective. -/
theorem presheaf_map_homOfLE_injective_of_eq {X : Scheme.{u}} (F : X.Modules) {U V : X.Opens}
    (hUV : V = U) : Function.Injective (F.presheaf.map (homOfLE hUV.le).op) := by
  subst hUV
  intro σ σ' h
  simpa using h

/-! ### The global sections -/

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L) {r : ℕ} (fam : Fin r → powSections L 1)

/-- The coordinates of the Čech cocycle of a global section: its charts. -/
def globalCechCoords (m : ℕ) (σ : Γ(natTensorPow L m, ⊤)) (j : Fin r) :
    Cech.cechMod (famRing L fam) (sectionRing L) {j} :=
  singletonChart L hL fam j m ((natTensorPow L m).presheaf.map (homOfLE le_top).op σ)

/-- The charts of a global section are Čech compatible. -/
theorem globalCechCoords_mem_cechCompatible (m : ℕ) (σ : Γ(natTensorPow L m, ⊤)) :
    globalCechCoords L hL fam m σ ∈
      Stacks.LocalCohomology.cechCompatible (famRing L fam) (sectionRingModule (L := L)) := by
  refine mem_cechCompatible_of_pairs _ _ _ fun a b hab => ?_
  show Cech.cechι _ _ _ (singletonChart L hL fam a m _) =
    Cech.cechι _ _ _ (singletonChart L hL fam b m _)
  rw [cechι_singletonChart_left L hL fam hab, cechι_singletonChart_right L hL fam hab,
    presheaf_map_homOfLE_comp, presheaf_map_homOfLE_comp]

/-- **The Čech cocycle of a global section of `L^{⊗ m}`**: its charts on the `X_{t_j}`. -/
def globalCechSection (m : ℕ) (σ : Γ(natTensorPow L m, ⊤)) :
    LinearMap.ker (Cech.cechD (famRing L fam) ((sectionRingModule (L := L) : ModuleCat _) : Type u)
      1) :=
  (Stacks.LocalCohomology.kerCechDOneEquivCechCompatible (famRing L fam)
    (sectionRingModule (L := L))).symm
    ⟨globalCechCoords L hL fam m σ, globalCechCoords_mem_cechCompatible L hL fam m σ⟩

/-- The coordinates of the Čech cocycle of a global section are its charts. -/
theorem cechTermOneEquiv_globalCechSection (m : ℕ) (σ : Γ(natTensorPow L m, ⊤)) (j : Fin r) :
    Stacks.LocalCohomology.cechTermOneEquiv (famRing L fam) (sectionRingModule (L := L))
        (globalCechSection L hL fam m σ).1 j = globalCechCoords L hL fam m σ j := by
  show Stacks.LocalCohomology.cechTermOneEquiv _ _
      ((Stacks.LocalCohomology.cechTermOneEquiv _ _).symm _) j = _
  rw [LinearEquiv.apply_symm_apply]

/-- The Čech cocycle of a global section of `L^{⊗ m}` has degree `m`. -/
theorem globalCechSection_mem_kerDegree (m : ℕ) (σ : Γ(natTensorPow L m, ⊤)) :
    globalCechSection L hL fam m σ ∈ kerDegree (grading L) (famRing L fam)
      (sectionRingModule (L := L)) (integerGrading (S := sectionRing L) (grading L)) (m : ℤ) := by
  refine (mem_gradedCechTerm_one_iff _ _ _ _ _ _).2 fun j => ?_
  show Stacks.LocalCohomology.cechTermOneEquiv _ _ (globalCechSection L hL fam m σ).1 j ∈ _
  rw [cechTermOneEquiv_globalCechSection]
  exact singletonChart_mem L hL fam j m _

/-- **The Čech cocycle determines the global section**, by the sheaf condition for the cover. -/
theorem globalCechSection_injective (hcov : ⨆ j, nvOpen L (fam j) = ⊤) (m : ℕ) :
    Function.Injective (globalCechSection L hL fam m) := by
  intro σ σ' h
  refine TopCat.Sheaf.eq_of_locally_eq' (F := ⟨(natTensorPow L m).presheaf,
    (natTensorPow L m).isSheaf⟩) (fun j => nvOpen L (fam j)) ⊤ (fun j => homOfLE le_top)
    hcov.ge σ σ' fun j => ?_
  have hj := congrArg (fun x => Stacks.LocalCohomology.cechTermOneEquiv (famRing L fam)
    (sectionRingModule (L := L)) x.1 j) h
  simp only [cechTermOneEquiv_globalCechSection] at hj
  exact singletonChart_injective L hL fam j m hj

/-- **Every degree-`m` Čech cocycle is the cocycle of a global section**, glued from its charts. -/
theorem exists_globalCechSection_eq (hcov : ⨆ j, nvOpen L (fam j) = ⊤) (m : ℕ)
    (x : LinearMap.ker (Cech.cechD (famRing L fam)
      ((sectionRingModule (L := L) : ModuleCat _) : Type u) 1))
    (hx : x ∈ kerDegree (grading L) (famRing L fam) (sectionRingModule (L := L))
      (integerGrading (S := sectionRing L) (grading L)) (m : ℤ)) :
    ∃ σ, globalCechSection L hL fam m σ = x := by
  set e := Stacks.LocalCohomology.cechTermOneEquiv (famRing L fam) (sectionRingModule (L := L))
  replace hx := (mem_gradedCechTerm_one_iff _ _ _ _ _ _).1 hx
  choose σs hσs using fun j => exists_singletonChart_eq L hL fam j m (e x.1 j) (hx j)
  have hcompat := (Stacks.LocalCohomology.mem_ker_cechD_one_iff (famRing L fam)
    (sectionRingModule (L := L)) x.1).1 x.2
  have hglue : TopCat.Presheaf.IsCompatible (natTensorPow L m).presheaf
      (fun j => nvOpen L (fam j)) σs := by
    intro a b
    obtain rfl | hab := eq_or_ne a b
    · rfl
    show (natTensorPow L m).presheaf.map (homOfLE inf_le_left).op (σs a) =
      (natTensorPow L m).presheaf.map (homOfLE inf_le_right).op (σs b)
    apply presheaf_map_homOfLE_injective_of_eq (natTensorPow L m)
      (Stacks.SectionRingChartMap.nvOpen_mul L (fam a) (fam b))
    simp only [presheaf_map_homOfLE_comp]
    apply pairChart_injective L hL fam hab m
    rw [← cechι_singletonChart_left L hL fam hab, ← cechι_singletonChart_right L hL fam hab,
      hσs a, hσs b]
    exact hcompat a b {a, b} (Finset.mem_insert_self a {b})
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := ⟨(natTensorPow L m).presheaf,
    (natTensorPow L m).isSheaf⟩) (fun j => nvOpen L (fam j)) ⊤ (fun j => homOfLE le_top)
    hcov.ge σs hglue
  refine ⟨σ, kerCechDOne_ext _ _ fun j => ?_⟩
  rw [cechTermOneEquiv_globalCechSection, globalCechCoords]
  show singletonChart L hL fam j m ((natTensorPow L m).presheaf.map (homOfLE le_top).op σ) = _
  rw [hσ j, hσs j]

end Stacks.Algebraization.SectionRingCone

end
