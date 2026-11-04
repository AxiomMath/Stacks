module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksFrontier.Homology.DerivedCategory.IsZero

/-!
# A nonzero cohomology class on a bounded-below complex is a nonzero morphism out of a single

Let `𝒜` be an abelian category admitting a derived category and let `K` be an object of `D(𝒜)`.
A morphism `M[-j] ⟶ K` out of an object of `𝒜` placed in degree `j` induces a morphism
`M ⟶ Hʲ(K)`, and the induced morphism is zero as soon as the morphism of `D(𝒜)` is. This file
proves the converse direction in the one case where it is elementary and unconditional: when
`K` lies in `D^{≥ j}(𝒜)`, **every** morphism `M ⟶ Hʲ(K)` is induced by a morphism `M[-j] ⟶ K`,
so a nonzero `M ⟶ Hʲ(K)` produces a nonzero `M[-j] ⟶ K`.

The reason is that `K` is then `Q.obj D` for a cochain complex `D` with `Dⁱ = 0` for `i < j`, so
the differential arriving in degree `j` is zero and `Hʲ(D)` *is* the object of cocycles
`Z^j(D)`. A morphism `M ⟶ Hʲ(D)` is therefore a cocycle `M ⟶ Dʲ`, and a cocycle in degree `j`
is exactly a morphism of complexes out of `M` placed in degree `j`. No extension or lifting
problem has to be solved, which is what fails for an unbounded `K`.

## Main results

* `DerivedCategory.homologyMap_eq_zero_of_Q_map_eq_zero` — a morphism of cochain complexes
  killed by the localization functor induces the zero map on homology in every degree.
* `DerivedCategory.homFromSingleOfCycles` — the morphism `M[-j] ⟶ Q.obj D` of `D(𝒜)` attached
  to a morphism `M ⟶ Z^j(D)`, and `DerivedCategory.homFromSingleOfCycles_ne_zero`: it is
  nonzero as soon as the induced `M ⟶ Hʲ(D)` is.
* `DerivedCategory.exists_hom_singleFunctor_ne_zero_of_isGE` — for `K` in `D^{≥ j}(𝒜)` a
  nonzero `M ⟶ Hʲ(K)` produces a nonzero `M[-j] ⟶ K`.
* `DerivedCategory.isZero_of_isGE_of_forall_hom_singleFunctor_eq_zero` — if the objects
  satisfying `G` detect the nonzero objects satisfying `B`, then the family of all their shifts
  detects the zero object among the objects of `D_B(𝒜)` that are bounded below.

## Implementation notes

The boundedness hypothesis in the last two results is not removable by this argument and is
not cosmetic: for an unbounded `K` a morphism `M ⟶ Hʲ(K)` need not lift, and lifting it is
precisely the step that the proof of [Stacks, Tag 0BQR] performs by hand on an affine chart of
an ample section.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
open HomologicalComplex

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A zero object of the derived category lies in `D^{≥ n}(𝒜)` for every `n`. -/
theorem isGE_of_isZero {X : DerivedCategory C} (hX : IsZero X) (n : ℤ) : X.IsGE n := by
  rw [isGE_iff]
  exact fun i _ => (homologyFunctor C i).map_isZero hX

/-- A morphism of cochain complexes that becomes zero in the derived category induces the zero
morphism on homology in every degree. -/
theorem homologyMap_eq_zero_of_Q_map_eq_zero {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ)
    (hf : Q.map f = 0) : homologyMap f n = 0 := by
  have h := homologyFunctorFactors_hom_naturality f n
  rw [hf, Functor.map_zero, zero_comp] at h
  exact (cancel_epi ((homologyFunctorFactors C n).hom.app K)).1 (h.symm.trans comp_zero.symm)

section

variable {D : CochainComplex C ℤ} {M : C} {j : ℤ} (v : M ⟶ D.cycles j)

/-- A morphism into the cocycles of a cochain complex in degree `j` is a morphism of complexes
out of `M` placed in degree `j`: the composite `M ⟶ Z^j(D) ⟶ Dʲ` is killed by the differential
leaving degree `j`. -/
def cochainHomFromSingleOfCycles :
    (single C (ComplexShape.up ℤ) j).obj M ⟶ D :=
  mkHomFromSingle (v ≫ D.iCycles j) (fun _ _ => by simp)

omit [HasDerivedCategory C] in
/-- The degree-`j` component of `cochainHomFromSingleOfCycles v` is the composite of the
identification `(M[-j])ʲ ≅ M`, the morphism `v` and the inclusion `Z^j(D) ⟶ Dʲ`. -/
@[simp]
theorem cochainHomFromSingleOfCycles_f :
    (cochainHomFromSingleOfCycles v).f j =
      (singleObjXSelf (ComplexShape.up ℤ) j M).hom ≫ v ≫ D.iCycles j := by
  simp [cochainHomFromSingleOfCycles]

/-- The morphism `M[-j] ⟶ Q.obj D` of `D(𝒜)` attached to a cocycle `M ⟶ Z^j(D)`. -/
def homFromSingleOfCycles : (singleFunctor C j).obj M ⟶ Q.obj D :=
  Q.map (cochainHomFromSingleOfCycles v)

omit [HasDerivedCategory C] in
/-- The morphism induced on `Hʲ` by the morphism of complexes attached to a cocycle
`v : M ⟶ Z^j(D)` is, up to the canonical identification `Hʲ(M[-j]) ≅ M`, the composite of `v`
with the projection `Z^j(D) ⟶ Hʲ(D)`. -/
theorem singleObjHomologySelfIso_inv_comp_homologyMap :
    (singleObjHomologySelfIso (ComplexShape.up ℤ) j M).inv ≫
        homologyMap (cochainHomFromSingleOfCycles v) j =
      v ≫ D.homologyπ j := by
  have key : (singleObjCyclesSelfIso (ComplexShape.up ℤ) j M).inv ≫
      cyclesMap (cochainHomFromSingleOfCycles v) j = v := by
    rw [← cancel_mono (D.iCycles j), assoc, cyclesMap_i,
      singleObjCyclesSelfIso_inv_iCycles_assoc, cochainHomFromSingleOfCycles_f,
      Iso.inv_hom_id_assoc]
  rw [← singleObjCyclesSelfIso_inv_homologyπ, assoc, homologyπ_naturality, ← assoc, key]

/-- **A cocycle whose cohomology class is nonzero is a nonzero morphism of `D(𝒜)`.** -/
theorem homFromSingleOfCycles_ne_zero (hv : v ≫ D.homologyπ j ≠ 0) :
    homFromSingleOfCycles v ≠ 0 := by
  intro h
  refine hv ?_
  rw [← singleObjHomologySelfIso_inv_comp_homologyMap v,
    homologyMap_eq_zero_of_Q_map_eq_zero _ j h, comp_zero]

end

/-- **For an object of `D^{≥ j}(𝒜)` every nonzero morphism `M ⟶ Hʲ(K)` comes from a nonzero
morphism `M[-j] ⟶ K`.** -/
theorem exists_hom_singleFunctor_ne_zero_of_isGE (K : DerivedCategory C) (j : ℤ) [K.IsGE j]
    {M : C} (ψ : M ⟶ (homologyFunctor C j).obj K) (hψ : ψ ≠ 0) :
    ∃ φ : (singleFunctor C j).obj M ⟶ K, φ ≠ 0 := by
  obtain ⟨D, hD, ⟨e⟩⟩ := exists_iso_Q_obj_of_isGE K j
  have := hD
  have hd : D.d (j - 1) j = 0 :=
    (D.isZero_of_isStrictlyGE j (j - 1) (by lia)).eq_of_src _ _
  have : IsIso (D.homologyπ j) := D.isIso_homologyπ (j - 1) j (by simp) hd
  obtain ⟨α⟩ : Nonempty ((homologyFunctor C j).obj K ≅ D.homology j) :=
    ⟨(homologyFunctor C j).mapIso e ≪≫ (homologyFunctorFactors C j).app D⟩
  refine ⟨homFromSingleOfCycles (ψ ≫ α.hom ≫ inv (D.homologyπ j)) ≫ e.inv, fun h => ?_⟩
  refine homFromSingleOfCycles_ne_zero _ ?_ (zero_of_comp_mono e.inv h)
  rw [assoc, assoc, IsIso.inv_hom_id, comp_id]
  exact fun hh => hψ (zero_of_comp_mono α.hom hh)

/-- **A family detecting the nonzero objects of `B` detects the zero object among the objects of
`D_B(𝒜)` that are bounded below.**

Here `B` is the property cutting out the subcategory in which the cohomology objects of `K` are
taken to lie — for `𝒜` the `𝒪_X`-modules on a scheme and `B` quasi-coherence this is
`D_QCoh(𝒪_X)` of [Stacks, Tag 06UP] — and `G` is the detecting family: `hG` says that every
nonzero object satisfying `B` receives a nonzero morphism from some object satisfying `G`.

The conclusion is that `K` is zero as soon as every morphism `M[-j] ⟶ K` out of a shift of a
member of the family vanishes. -/
theorem isZero_of_isGE_of_forall_hom_singleFunctor_eq_zero
    (B G : ObjectProperty C) (K : DerivedCategory C) (j₀ : ℤ) (hKge : K.IsGE j₀)
    (hKB : ∀ n : ℤ, B ((homologyFunctor C n).obj K))
    (hG : ∀ F : C, B F → ¬ IsZero F → ∃ M : C, G M ∧ ∃ ψ : M ⟶ F, ψ ≠ 0)
    (hvan : ∀ M : C, G M → ∀ (j : ℤ) (φ : (singleFunctor C j).obj M ⟶ K), φ = 0) :
    IsZero K := by
  classical
  have := hKge
  rw [isZero_iff_forall_isZero_homology]
  by_contra hc
  obtain ⟨n₀, hn₀⟩ := not_forall.1 hc
  have hvanlow : ∀ i : ℤ, i < j₀ → IsZero ((homologyFunctor C i).obj K) := fun i hi =>
    isZero_of_isGE K j₀ i hi
  have hle : j₀ ≤ n₀ := by
    by_contra hlt
    exact hn₀ (hvanlow n₀ (by lia))
  have hk : ∀ i : ℤ, j₀ ≤ i → j₀ + ((i - j₀).toNat : ℤ) = i := fun i hi => by omega
  have hex : ∃ k : ℕ, ¬ IsZero ((homologyFunctor C (j₀ + (k : ℤ))).obj K) :=
    ⟨(n₀ - j₀).toNat, by rwa [hk n₀ hle]⟩
  have hfind := Nat.find_spec hex
  have hge : K.IsGE (j₀ + (Nat.find hex : ℤ)) := by
    rw [isGE_iff]
    intro i hi
    by_cases h : i < j₀
    · exact hvanlow i h
    · have hlt : (i - j₀).toNat < Nat.find hex := by omega
      have h2 := Nat.find_min hex hlt
      rw [hk i (by lia)] at h2
      exact not_not.1 h2
  have := hge
  obtain ⟨M, hM, ψ, hψ⟩ := hG _ (hKB _) hfind
  obtain ⟨φ, hφ⟩ := exists_hom_singleFunctor_ne_zero_of_isGE K _ ψ hψ
  exact hφ (hvan M hM _ φ)

end DerivedCategory

end
