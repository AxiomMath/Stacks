module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.RingTheory.Jacobson.Ring
public import StacksFrontier.AlgebraicGeometry.NodalContraction.Basic
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveResidueField

/-!
# An exceptional curve over a closed point is proper

Let `E ⊆ X` be a closed subscheme isomorphic to `𝐏¹_k`, and `φ : X ⟶ Spec R` a morphism whose
restriction to `E` is locally of finite type and carries `E` to a closed point `𝔪` of `Spec R`.
Then `E ⟶ Spec R` is universally closed
(`AlgebraicGeometry.universallyClosed_subschemeι_comp_of_iso_projectiveLineProj`). Consequently
`E` is closed in every scheme separated over `Spec R` into which `X` maps over `Spec R`
(`AlgebraicGeometry.isClosed_range_subschemeι_comp_of_iso_projectiveLineProj`); this is how the
proof of [Stacks, Tag 0C2N] (2) keeps the curve closed in a projective compactification.

`E ⟶ Spec R` factors through `Spec Γ(E, 𝒪_E)`. The first factor is universally closed because
`𝐏¹_k ⟶ Spec k` is proper. For the second, `L = Γ(E, 𝒪_E)` is a field which embeds into the ring
`B` of functions on an affine open of `E`, compatibly with `R`; as `B` is of finite type over
`R / 𝔪`, `L` is finite over `R / 𝔪` by Zariski's lemma ([Stacks, Tag 0CY7]), so `R ⟶ L` is
integral.

## Main results

* `AlgebraicGeometry.universallyClosed_toSpecΓ_of_iso_projectiveLineProj`: `E ⟶ Spec Γ(E, 𝒪_E)`
  is universally closed for `E ≅ 𝐏¹_k`.
* `AlgebraicGeometry.universallyClosed_subschemeι_comp_of_iso_projectiveLineProj`: the statement
  above.
* `AlgebraicGeometry.isClosed_range_subschemeι_comp_of_iso_projectiveLineProj`: the curve is
  closed in a separated scheme over the base.

## References

* [Stacks Project, Tag 0C2N](https://stacks.math.columbia.edu/tag/0C2N)
* [Stacks Project, Tag 0CY7](https://stacks.math.columbia.edu/tag/0CY7)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A morphism to an affine scheme factors through `toSpecΓ`. -/
private theorem eq_toSpecΓ_comp_spec_map {E : Scheme.{u}} {R : CommRingCat.{u}} (f : E ⟶ Spec R) :
    f = E.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop) := by
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- **A scheme isomorphic to `𝐏¹_k` is universally closed over the spectrum of its functions.**
The structure morphism `𝐏¹_k ⟶ Spec k` is proper, and it factors through
`E ⟶ Spec Γ(E, 𝒪_E)` followed by an affine, hence separated, morphism. -/
theorem universallyClosed_toSpecΓ_of_iso_projectiveLineProj {E : Scheme.{u}} {k : Type u}
    [Field k] (e : projectiveLineProj k ≅ E) : UniversallyClosed E.toSpecΓ := by
  have : IsProper (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 1) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k 1
  let g : E ⟶ Spec (.of k) := e.inv ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 1
  have : UniversallyClosed g := inferInstance
  have : UniversallyClosed
      (E.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop)) := by
    rw [← eq_toSpecΓ_comp_spec_map g]
    infer_instance
  exact UniversallyClosed.of_comp_of_isSeparated E.toSpecΓ
    (Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop))

/-- **An exceptional curve over a closed point is universally closed over the base.** Let `D` cut
out a closed subscheme `E ≅ 𝐏¹_k` of `X`, and let `φ : X ⟶ Spec R` restrict to a morphism
`E ⟶ Spec R` locally of finite type carrying `E` to a closed point. Then `E ⟶ Spec R` is
universally closed. -/
theorem universallyClosed_subschemeι_comp_of_iso_projectiveLineProj {X : Scheme.{u}}
    (D : X.IdealSheafData) {k : Type u} [Field k] (e : projectiveLineProj k ≅ D.subscheme)
    {R : CommRingCat.{u}} (φ : X ⟶ Spec R) [LocallyOfFiniteType (D.subschemeι ≫ φ)]
    (m : Spec R) (hm : IsClosed ({m} : Set (Spec R))) (hφ : ∀ z, φ (D.subschemeι z) = m) :
    UniversallyClosed (D.subschemeι ≫ φ) := by
  set E := D.subscheme
  set φ' := D.subschemeι ≫ φ
  have := isIntegral_subscheme_of_iso_projectiveLineProj D k e
  let : Field Γ(E, ⊤) :=
    (Scheme.IdealSheafData.isField_sections_subscheme_of_iso_projectiveLineProj D k e).toField
  have := universallyClosed_toSpecΓ_of_iso_projectiveLineProj e
  let ψ : R ⟶ Γ(E, ⊤) := (Scheme.ΓSpecIso R).inv ≫ φ'.appTop
  have hfac : φ' = E.toSpecΓ ≫ Spec.map ψ := eq_toSpecΓ_comp_spec_map φ'
  suffices hint : ψ.hom.IsIntegral by
    have : IsIntegralHom (Spec.map ψ) := IsIntegralHom.SpecMap_iff.mpr hint
    rw [hfac]
    infer_instance
  -- the kernel of `ψ` is the closed point
  obtain ⟨d₀⟩ : Nonempty E := inferInstance
  have hmax : m.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal m).mp hm
  have hker : RingHom.ker ψ.hom = m.asIdeal := by
    have hpt : (Spec.map ψ).base (E.toSpecΓ d₀) = m := by
      rw [← Scheme.Hom.comp_apply, ← hfac]
      exact hφ d₀
    rw [← hpt, Spec.map_base]
    show RingHom.ker ψ.hom = Ideal.comap ψ.hom (E.toSpecΓ d₀).asIdeal
    rw [Ideal.eq_bot_of_prime (E.toSpecΓ d₀).asIdeal, RingHom.ker_eq_comap_bot]
  -- an affine open of the curve
  obtain ⟨A, hA, hd₀A, -⟩ := exists_isAffineOpen_mem_and_subset (X := E) (U := ⊤) (x := d₀) trivial
  have : Nonempty A := ⟨⟨d₀, hd₀A⟩⟩
  let ρ : Γ(E, ⊤) ⟶ Γ(E, A) := E.presheaf.map (homOfLE le_top).op
  have hft : (ψ ≫ ρ).hom.FiniteType := by
    have hψρ : ψ ≫ ρ = (Scheme.ΓSpecIso R).inv ≫ φ'.appLE ⊤ A le_top := by
      simp only [ψ, ρ, Category.assoc, Scheme.Hom.appLE]
      rfl
    rw [hψρ, CommRingCat.hom_comp]
    exact (HasRingHomProperty.appLE @LocallyOfFiniteType φ' inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨A, hA⟩ le_top).comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).2)
  -- the residue field and Zariski's lemma
  let : Field (R ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  let ψ' := Ideal.Quotient.lift m.asIdeal ψ.hom hker.ge
  have hψ : ψ.hom = ψ'.comp (Ideal.Quotient.mk m.asIdeal) := by
    ext r
    rfl
  rw [CommRingCat.hom_comp, hψ, ← RingHom.comp_assoc] at hft
  rw [hψ]
  exact ((RingHom.finite_of_algHom_finiteType_of_isJacobsonRing ψ' ρ.hom
    (.of_comp_finiteType hft)).comp (.of_surjective _ Ideal.Quotient.mk_surjective)).to_isIntegral

/-- **An exceptional curve over a closed point is closed in every separated scheme over the
base.** With `φ = j ≫ p` for a separated `p : Y ⟶ Spec R`, the image of the curve in `Y` is
closed. -/
theorem isClosed_range_subschemeι_comp_of_iso_projectiveLineProj {X Y : Scheme.{u}}
    (D : X.IdealSheafData) {k : Type u} [Field k] (e : projectiveLineProj k ≅ D.subscheme)
    {R : CommRingCat.{u}} (j : X ⟶ Y) (p : Y ⟶ Spec R) [IsSeparated p]
    [LocallyOfFiniteType (D.subschemeι ≫ j ≫ p)] (m : Spec R)
    (hm : IsClosed ({m} : Set (Spec R))) (hφ : ∀ z, (j ≫ p) (D.subschemeι z) = m) :
    IsClosed (Set.range (D.subschemeι ≫ j).base) := by
  have := universallyClosed_subschemeι_comp_of_iso_projectiveLineProj D e (j ≫ p) m hm hφ
  have : UniversallyClosed ((D.subschemeι ≫ j) ≫ p) := by
    rw [Category.assoc]
    infer_instance
  have := UniversallyClosed.of_comp_of_isSeparated (D.subschemeι ≫ j) p
  exact (D.subschemeι ≫ j).isClosedMap.isClosed_range

end AlgebraicGeometry

end
