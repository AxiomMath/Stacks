module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.Localization.Finiteness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.CodimensionOne
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.PoleLocus

/-!
# The function field as a localization of the sections away from a codimension-one point

Let `X` be an integral locally Noetherian scheme, `V₀` an affine open of `X`, `z` a point of `V₀`
whose local ring has dimension at most one, and `S` a nonempty open subset of `V₀` not containing
`z`. This file proves that the function field of `X` is the localization of `Γ(X, S)` at the
prime `q` of `Γ(X, V₀)` attached to `z`, and deduces that `Γ(X, S)` is never a finite module over
`Γ(X, V₀)`.

That last statement is the first paragraph of [Stacks, Tag 0AWC] read on an affine chart.

## Main results

* `Stacks.AlgebraicGeometry.CodimensionOneObstruction.exists_mem_primeCompl_mul_eq_germ`: every
  element of the function field becomes a section over `S` after multiplication by a function on
  `V₀` that does not vanish at `z`.
* `Stacks.AlgebraicGeometry.CodimensionOneObstruction.isLocalization_functionField_sections`: the
  function field is the localization of `Γ(X, S)` at the image of the complement of `q`.
* `Stacks.AlgebraicGeometry.CodimensionOneObstruction.moduleFinite_functionField_of_sections`:
  finiteness of `Γ(X, S)` over `Γ(X, V₀)` passes to the function field over `𝒪_{X, z}`.
* `Stacks.AlgebraicGeometry.CodimensionOneObstruction.not_moduleFinite_sections`: hence `Γ(X, S)`
  is not a finite `Γ(X, V₀)`-module.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.CodimensionOneObstruction

/-- Restriction makes the sections over a smaller open an algebra over the sections over a
larger one. -/
@[instance_reducible] noncomputable def resAlgebra {X : Scheme.{u}} {U W : X.Opens} (h : W ≤ U) :
    Algebra Γ(X, U) Γ(X, W) :=
  (X.presheaf.map (homOfLE h).op).hom.toAlgebra

/-- The algebra map of `resAlgebra h` is the restriction map of the structure sheaf. -/
theorem algebraMap_resAlgebra {X : Scheme.{u}} {U W : X.Opens} (h : W ≤ U) (s : Γ(X, U)) :
    letI := resAlgebra h
    algebraMap Γ(X, U) Γ(X, W) s = X.presheaf.map (homOfLE h).op s := rfl

/-- An open subset of an affine open of a locally Noetherian scheme is quasi-compact. -/
theorem isCompact_of_le_isAffineOpen {X : Scheme.{u}} [IsLocallyNoetherian X] {V₀ : X.Opens}
    (hV₀ : IsAffineOpen V₀) {S : X.Opens} (hSV : S ≤ V₀) : IsCompact (S : Set X) := by
  have : IsAffine V₀.toScheme := hV₀
  have : IsNoetherian V₀.toScheme := ⟨⟩
  have h1 : IsCompact ((V₀.ι ⁻¹ᵁ S : V₀.toScheme.Opens) : Set V₀.toScheme) :=
    TopologicalSpace.NoetherianSpace.isCompact _
  have h2 := h1.image V₀.ι.base.hom.continuous
  have hpre : ((V₀.ι ⁻¹ᵁ S : V₀.toScheme.Opens) : Set V₀.toScheme)
      = V₀.ι.base.hom ⁻¹' (S : Set X) := rfl
  rw [hpre, Set.image_preimage_eq_of_subset] at h2
  · exact h2
  · simpa [Scheme.Opens.range_ι] using hSV

/-- The generic point lies in every open subset with nonempty underlying scheme. -/
private theorem genericPoint_mem_of_nonempty {X : Scheme.{u}} [IsIntegral X] (U : X.Opens)
    [Nonempty U.toScheme] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U.toScheme›)

/-- Restricting a section to a smaller open does not change its germ at the function field. -/
private theorem germToFunctionField_res {X : Scheme.{u}} [IsIntegral X] {U W : X.Opens}
    [Nonempty U.toScheme] [Nonempty W.toScheme] (h : W ≤ U) (g : Γ(X, U)) :
    X.germToFunctionField W (X.presheaf.map (homOfLE h).op g) = X.germToFunctionField U g :=
  TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-! ### Clearing denominators in the function field -/

/-- **Every element of the function field is a section over `S` up to a function nonvanishing at
`z`.** -/
theorem exists_mem_primeCompl_mul_eq_germ {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) [Nonempty V₀.toScheme] {z : X} (hz : z ∈ V₀)
    (hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1) {S : X.Opens} [Nonempty S.toScheme]
    (hSV : S ≤ V₀) (hzS : z ∉ S) (k : X.functionField) :
    ∃ g : Γ(X, V₀), ∃ x : Γ(X, S),
      g ∈ (hV₀.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl ∧
        X.germToFunctionField V₀ g * k = X.germToFunctionField S x := by
  classical
  obtain ⟨W, hgenW, t, ht⟩ := X.presheaf.exists_germ_eq (x := genericPoint X) k
  obtain ⟨g, hzg, hle⟩ := exists_basicOpen_inter_le hV₀ hz hdim (S := S) (W := W) hzS hgenW
  set gS : Γ(X, S) := X.presheaf.map (homOfLE hSV).op g with hgS
  have hbas : X.basicOpen gS = S ⊓ X.basicOpen g := by
    rw [hgS]; exact Scheme.basicOpen_res _ _ _
  have : Nonempty (X.basicOpen g).toScheme := ⟨⟨z, hzg⟩⟩
  have hgenbas : genericPoint X ∈ X.basicOpen gS := by
    rw [hbas]; exact ⟨genericPoint_mem_of_nonempty S, genericPoint_mem_of_nonempty _⟩
  have : Nonempty (X.basicOpen gS) := ⟨⟨genericPoint X, hgenbas⟩⟩
  have hsubW : X.basicOpen gS ≤ W := hbas ▸ hle
  set t' : Γ(X, X.basicOpen gS) := X.presheaf.map (homOfLE hsubW).op t with ht'
  have : IsLocalization.Away gS Γ(X, X.basicOpen gS) :=
    isLocalization_basicOpen_of_qcqs (isCompact_of_le_isAffineOpen hV₀ hSV)
      ((isQuasiSeparated_univ (α := X)).of_subset (Set.subset_univ _)) gS
  obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (Submonoid.powers gS) t'
  obtain ⟨n, hn⟩ := s.2
  have hk : X.germToFunctionField (X.basicOpen gS) t' = k := by
    rw [ht', TopCat.Presheaf.germ_res_apply]
    exact ht
  have hgS' : X.germToFunctionField S gS = X.germToFunctionField V₀ g :=
    germToFunctionField_res hSV g
  refine ⟨g ^ n, x, Submonoid.pow_mem _ ?_ n, ?_⟩
  · exact (mem_basicOpen_iff_notMem_primeIdealOf hV₀ hz g).mp hzg
  · have halg : ∀ y : Γ(X, S), (algebraMap Γ(X, S) Γ(X, X.basicOpen gS)) y =
        X.presheaf.map (homOfLE (X.basicOpen_le gS)).op y := fun _ => rfl
    have h0 := congrArg (X.germToFunctionField (X.basicOpen gS)) hxs
    rw [map_mul] at h0
    simp only [halg, germToFunctionField_res, hk] at h0
    rw [← hn, map_pow, hgS'] at h0
    rw [map_pow, mul_comm]
    exact h0

/-! ### The function field as a localization of the sections over `S` -/

/-- **The function field is the localization of `Γ(X, S)` at `q`.** Here `q` is the prime of
`Γ(X, V₀)` attached to a point `z` of the affine open `V₀` outside `S` whose local ring has
dimension at most one. -/
theorem isLocalization_functionField_sections {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) [Nonempty V₀.toScheme] {z : X}
    (hz : z ∈ V₀) (hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1) {S : X.Opens}
    [Nonempty S.toScheme] (hSV : S ≤ V₀) (hzS : z ∉ S) :
    letI := resAlgebra hSV
    IsLocalization
      (Algebra.algebraMapSubmonoid Γ(X, S) (hV₀.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl)
      X.functionField := by
  let := resAlgebra hSV
  set q := (hV₀.primeIdealOf ⟨z, hz⟩).asIdeal with hq
  have halgS : ∀ y : Γ(X, S), algebraMap Γ(X, S) X.functionField y =
    X.germToFunctionField S y := fun _ => rfl
  have hres : ∀ g : Γ(X, V₀), algebraMap Γ(X, V₀) Γ(X, S) g =
    X.presheaf.map (homOfLE hSV).op g := fun _ => rfl
  have himg : ∀ g : Γ(X, V₀), algebraMap Γ(X, S) X.functionField (algebraMap Γ(X, V₀) Γ(X, S) g) =
      X.germToFunctionField V₀ g := by
    intro g
    rw [halgS, hres]
    exact germToFunctionField_res hSV g
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, g, hg, rfl⟩
    rw [himg g]
    refine (Ne.isUnit (fun h0 => hg ?_) : IsUnit (X.germToFunctionField V₀ g))
    have hg0 : g = 0 := X.germToFunctionField_injective V₀ (by rw [h0, map_zero])
    rw [hg0]
    exact Ideal.zero_mem q
  · intro k
    obtain ⟨g, x, hg, hgk⟩ := exists_mem_primeCompl_mul_eq_germ hV₀ hz hdim hSV hzS k
    exact ⟨⟨x, ⟨algebraMap Γ(X, V₀) Γ(X, S) g, ⟨g, hg, rfl⟩⟩⟩, by
      rw [himg g, halgS, mul_comm]; exact hgk⟩
  · intro x y hxy
    refine ⟨1, ?_⟩
    rw [halgS, halgS] at hxy
    rw [X.germToFunctionField_injective S hxy]

/-! ### Finiteness of the sections would make the function field finite over the local ring -/

/-- If the sections over `S` are a finite `Γ(X, V₀)`-module then the function field is a finite
module over the local ring at `z`. -/
theorem moduleFinite_functionField_of_sections {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) [Nonempty V₀.toScheme] {z : X}
    (hz : z ∈ V₀) (hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1) {S : X.Opens}
    [Nonempty S.toScheme] (hSV : S ≤ V₀) (hzS : z ∉ S)
    (h : letI := resAlgebra hSV; Module.Finite Γ(X, V₀) Γ(X, S)) :
    Module.Finite (X.presheaf.stalk z) X.functionField := by
  let := resAlgebra hSV
  let := X.presheaf.algebra_section_stalk (⟨z, hz⟩ : V₀)
  have := h
  have htow : IsScalarTower Γ(X, V₀) Γ(X, S) X.functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    refine RingHom.ext fun g => ?_
    show X.germToFunctionField V₀ g =
      algebraMap Γ(X, S) X.functionField (X.presheaf.map (homOfLE hSV).op g)
    exact (germToFunctionField_res hSV g).symm
  have := AlgebraicGeometry.functionField_isScalarTower X V₀ ⟨z, hz⟩
  have := hV₀.isLocalization_stalk ⟨z, hz⟩
  have := isLocalization_functionField_sections hV₀ hz hdim hSV hzS
  exact Module.Finite.of_isLocalization Γ(X, V₀) Γ(X, S)
    (hV₀.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl

/-- **The sections over `S` are never a finite module over the sections over `V₀`.** -/
theorem not_moduleFinite_sections {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) [Nonempty V₀.toScheme] {z : X} (hz : z ∈ V₀)
    (hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1) {S : X.Opens} [Nonempty S.toScheme]
    (hSV : S ≤ V₀) (hzS : z ∉ S) :
    ¬ (letI := resAlgebra hSV; Module.Finite Γ(X, V₀) Γ(X, S)) := by
  intro h
  exact AlgebraicGeometry.not_module_finite_functionField
    (fun hz' => hzS (by rw [hz']; exact genericPoint_mem_of_nonempty S))
    (moduleFinite_functionField_of_sections hV₀ hz hdim hSV hzS h)

end Stacks.AlgebraicGeometry.CodimensionOneObstruction

end
