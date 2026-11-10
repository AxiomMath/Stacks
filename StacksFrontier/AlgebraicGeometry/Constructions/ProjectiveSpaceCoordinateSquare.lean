module

public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Charts
public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Generation
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartFullGradedGluing
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.MapDomain
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Morphism
public import StacksFrontier.AlgebraicGeometry.SymmetricFree.Basic
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Basic
import StacksFrontier.AlgebraicGeometry.RelativeSpec.Representability

/-!
# Coordinates for the morphism defined by generating sections

Let `k` be a commutative ring, `V` a `k`-module with a basis `v₀, …, vₙ`, `X` a scheme over `k`,
`ℒ` an invertible `𝒪_X`-module and `ψ : V → Γ(X, ℒ)` a `k`-linear map whose image generates `ℒ`.
Two morphisms out of `X` are attached to this datum.

* `φ_{ℒ,ψ} : X ⟶ 𝐏(V) = Proj(Sym_k V)`, the morphism of [Stacks, Tag 0FCY] built from the
  universal property of `Proj` of a graded ring generated in degree one,
  `Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.morphismOfGeneratingSections`.
* `φ_{(ℒ,(s₀,…,sₙ))} : X ⟶ ℙⁿ`, the morphism of [Stacks, Tag 01ND] built by glueing the chart
  morphisms of the ratio families `sₖ/sᵢ`, for `sᵢ = ψ(vᵢ)`,
  `Stacks.ProjectiveFromSections.toProjectiveSpaceOver`.

The two are pinned by *different* chart constructions: the first by the dehomogenization
`a / vᵢ ^ m ↦ ψ(a) / ψ(vᵢ) ^ m` of [Stacks, Tag 01N8], the second by Mathlib's
`AlgebraicGeometry.Proj.fromOfGlobalSections` of the ring map `Tₖ ↦ sₖ/sᵢ`. This file computes
both chart ring maps, identifies them in degree one, and concludes that the coordinate
isomorphism `𝐏(V) ≅ ℙⁿ_k` of the basis carries the first morphism to the second.

**On the numbering.** Tag 0FCY is an unnumbered example and has no numbered clauses; "clause (5)"
and "clause (6)" below are this library's own labels for the assertions about `φ_{ℒ,ψ}` and for
the coordinate square. The convention is set out in
`StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModuleBundle`; the numbers do not
occur in the source.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare.coordHom`: **the graded ring map
  `ℤ[T₀, …, Tₙ] → Sym_k V`, `Tᵢ ↦ vᵢ`**, of which `Proj` is the coordinate comparison; it is the
  integral coefficient map followed by `SymPow.gradedMvPolynomialInv`, the graded half of
  `AlgebraicGeometry.basisProjectiveSpaceOfModuleIso`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare.iSup_nonvanishingOpen_basis_eq_top`
  and `generatesStalks_basisSections`: **the sections `ψ(vᵢ)` attached to a basis already
  generate `ℒ`**, so the datum of [Stacks, Tag 01ND] is available. A vector is a `k`-combination
  of the basis vectors and the scalars act through the structure morphism, so no point is a
  common zero of the `ψ(vᵢ)` if none is a common zero of all the `ψ(v)`.
* `…CoordinateSquare.preimage_basicOpen_toProjectiveSpaceAtUniverse`: the preimage of the
  standard open `D₊(Tᵢ)` under `φ_{(ℒ,(sᵢ))}` is `X_{sᵢ}`.
* `…CoordinateSquare.appLE_awayToSection_morphismOfGeneratingSections`: **the first chart ring
  map**, the dehomogenization of `ψ` at `vᵢ`, over any open on which `ψ(vᵢ)` is nonvanishing.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare.appLE_awayToSection_chartHom`:
  **the second chart ring map**, `a / Tᵢ ^ m ↦ a(s₀/sᵢ, …, sₙ/sᵢ)`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare.ratio_twistOneSection`: **the two
  agree on the degree-one fractions**: the dehomogenization of `ψ` sends `vⱼ / vᵢ` to the ratio
  `sⱼ / sᵢ` out of which the chart morphisms of [Stacks, Tag 01ND] are built. Both are the
  unique function multiplying `sᵢ` to `sⱼ`, so this is the uniqueness of division by a
  nonvanishing section; the left unitor `ℒ ^⊗ 1 ≅ ℒ` moves one side to the other.
* `…CoordinateSquare.away_ringHom_ext_isLocalizationElem`: **a ring map out of the chart ring
  `ℤ[T₀, …, Tₙ]_{(Tᵢ)}` is determined by its values on the degree-one fractions `Tⱼ / Tᵢ`**. The
  chart ring is a polynomial ring on those fractions over its degree-zero part, and the
  degree-zero part is a copy of `ℤ`, out of which there is only one ring map. This is what turns
  the degree-one agreement into agreement in every degree.
* `…CoordinateSquare.map_coordHom_morphismOfGeneratingSections`: **the coordinate square on the
  integral model**, `φ_{ℒ,ψ}` followed by the comparison `𝐏(V) ⟶ ℙⁿ_ℤ` of the basis is
  `φ_{(ℒ,(s₀,…,sₙ))}`. The two morphisms have the same preimage of each `D₊(Tᵢ)`, namely
  `X_{sᵢ}`, those cover `X`, and the two chart ring maps agree; so the generic uniqueness
  statement `eq_of_appLE_eq_on_away` of
  `StacksFrontier/AlgebraicGeometry/Constructions/ProjChartFullGradedGluing.lean` applies.
* `…CoordinateSquare.coordinateProjMap_eq_projMap`: **the repository's coordinate projection to
  the integral model is Mathlib's `AlgebraicGeometry.Proj.map`.** This is what lets the integral
  square be read against the `toIntegral` clause of
  `Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison`, which is stated through the
  partial functoriality `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom`.
* `…CoordinateSquare.basisProjectiveSpaceOfModuleIso_hom_left_comp_toIntegralAtUniverse`: the
  coordinate isomorphism `𝐏(V) ≅ ℙⁿ_k` of a basis, followed by the projection of `ℙⁿ_k` to the
  integral model, is `Proj` of the graded map `Tᵢ ↦ vᵢ`.
* `…CoordinateSquare.morphismOfGeneratingSections_comp_basisIso_toIntegralAtUniverse`: **the
  projection to the integral model of the coordinate square of [Stacks, Tag 0FCY], clause
  (6)** — one of the two legs of that square.
* `…CoordinateSquare.morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec`:
  **`φ_{ℒ,ψ}` is a morphism over `Spec k`** — the other leg, and the clause of
  [Stacks, Tag 0FCY] saying that the morphism attached to generating sections is one of
  `k`-schemes. It mentions no basis: the structure morphism of `𝐏(V)` is the inclusion of the
  degree-zero part of `Sym_k V` into each chart ring, and `φ_{ℒ,ψ}` carries that inclusion to
  the scalars acting on `Γ(X, ℒ)` through the structure morphism of `X`.
* `…CoordinateSquare.morphismOfGeneratingSections_comp_basisProjectiveSpaceOfModuleIso`:
  **the coordinate square of [Stacks, Tag 0FCY], clause (6)**: the coordinate isomorphism
  `𝐏(V) ≅ ℙⁿ_k` of a basis carries `φ_{ℒ,ψ}` to `φ_{(ℒ,(s₀,…,sₙ))}`. Since `ℙⁿ_k` is a fibre
  product, this is the two legs above put together by the universal property.

## Implementation notes

**The `k`-module structure on `Γ(X, ℒ)`** is restriction of scalars along the ring map
`k → Γ(X, 𝒪_X)` of the structure morphism, reintroduced here as a local instance; this is the
convention of
`StacksFrontier/AlgebraicGeometry/Constructions/ProjectiveSpaceGeneratingSections.lean`.

**The two chart ring maps are compared on `A_{(Tᵢ)}` for the integral coordinate ring**, not for
`Sym_k V`: the target `ℙⁿ` of [Stacks, Tag 01ND] is `Proj ℤ[T₀, …, Tₙ]` base changed, so the
comparison crosses the coefficient map `ℤ → k`. That is what `coordHom` is for, and
`AlgebraicGeometry.Proj.awayToSection_comp_appLE` is what transports the first chart ring map
along it.

**The preimage identification is imported, not reproved.**
`Stacks.AmpleImmersionReduction.preimage_standardChart` already computes the preimage of a
standard chart of `ℙⁿ_S` under the pinned morphism; reading it on the integral model is the
lift over the identity of `X`.

**The morphism over the base is checked one chart at a time.** The target `ℙⁿ_k` of
[Stacks, Tag 0FCY] is the fibre product `ℙⁿ_{Spec k}`, so the square is an equality of two
morphisms into a pullback and needs both projections. The projection to `Spec k` is an equality
of morphisms into an affine scheme, hence an equality of two ring maps `k ⟶ Γ(X, 𝒪_X)`
(`AlgebraicGeometry.ext_to_Spec`), and that is checked on the nonvanishing opens of the
degree-one sections of the graded map attached to `ψ`, which cover `X`. On one of them the
structure morphism of `𝐏(V)` is `AlgebraicGeometry.Proj.awayι_toSpecZero`, read on `D₊(f)`
itself rather than on its affine model, and `φ_{ℒ,ψ}` induces the dehomogenization of `ψ` by
clause (c) of `Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.Classifies`; the degree-zero
value is then a scalar multiple of the trivializing section by
`Stacks.SectionRingGeometric.globalSection_unitComp`, and the scalar is the function the element
of `k` names on `X`.

## References

* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
-/

@[expose] public noncomputable section

open CategoryTheory Category Opposite
open AlgebraicGeometry HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjDegreeOneRepresents
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {k V : Type u} [CommRing k] [AddCommGroup V] [Module k V] {n : ℕ}
  (b : Module.Basis (Fin (n + 1)) k V)

/-! ### The graded ring map `ℤ[T₀, …, Tₙ] ⟶ Sym_k V` of a basis -/

/-- **The graded ring map `ℤ[T₀, …, Tₙ] → Sym_k V` sending `Tᵢ` to `vᵢ`.** It is the
coefficient map out of the universe copy of the integers followed by the identification of the
polynomial ring on a basis with the symmetric algebra. -/
def coordHom :
    Stacks.SectionsToProjectiveSpace.coordGrading.{u} n →+*ᵍ
      (fun m : ℕ => SymPow.symmetricPower m k V) :=
  (SymPow.gradedMvPolynomialInv b).comp (ProjPolyChart.integralGradedHom k n)

/-- **The graded ring map of a basis sends the `i`-th variable to the `i`-th basis vector.** -/
@[simp] theorem coordHom_X (j : Fin (n + 1)) :
    coordHom b (MvPolynomial.X j) = SymmetricAlgebra.ι k V (b j) := by
  have h1 : (ProjPolyChart.integralGradedHom k n) (MvPolynomial.X j)
      = MvPolynomial.X j := by
    rw [ProjPolyChart.integralGradedHom_apply, MvPolynomial.map_X]
  have h2 : SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι k V (b j))
      = MvPolynomial.X j := by
    rw [Stacks.SymmetricFree.equivMvPolynomial_ι, Module.Basis.constr_basis]
  change (SymPow.gradedMvPolynomialInv b) ((ProjPolyChart.integralGradedHom k n)
      (MvPolynomial.X j)) = _
  rw [h1, SymPow.gradedMvPolynomialInv_apply, ← h2,
    AlgEquiv.symm_apply_apply]

/-- Mathlib's hypothesis for `AlgebraicGeometry.Proj.map` for the graded ring map of a basis. -/
theorem irrelevant_le_map_coordHom :
    HomogeneousIdeal.irrelevant (fun m : ℕ => SymPow.symmetricPower m k V) ≤
      (HomogeneousIdeal.irrelevant
        (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)).map (coordHom b) :=
  HomogeneousIdeal.irrelevant_le_map_comp
    (ProjPolyChart.irrelevant_le_map_coeffGradedHom (ULift.{u} ℤ) n
      (ProjPolyChart.integralCoeffHom k))
    (AlgebraicGeometry.irrelevant_le_map_gradedMvPolynomialInv b)

/-! ### The sections attached to a basis generate -/

section Generation

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] {L : X.Modules}
  [Stacks.Ample.IsInvertibleModule X L]

/-- The vectors of `V` whose image under `ψ` has germ at `x` inside `𝔪ₓ · ℒₓ`. The scalars of
`Γ(X, ℒ)` act through the structure morphism, so this is a `k`-submodule of `V`. -/
private def vanishingSubmodule (ψ : V →ₗ[k] Γ(L, ⊤)) (x : X) : Submodule k V where
  carrier := {v | (L.presheaf.Γgerm x).hom (ψ v) ∈ Stacks.ModuleStalk.maximalSmul L x}
  add_mem' {v w} hv hw := by
    simp only [Set.mem_ofPred_eq] at hv hw ⊢
    rw [map_add, map_add]
    exact Submodule.add_mem _ hv hw
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [map_zero, map_zero]
    exact Submodule.zero_mem _
  smul_mem' c v hv := by
    simp only [Set.mem_ofPred_eq] at hv ⊢
    have hc : (c • ψ v : Γ(L, ⊤)) =
        Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom k X c • ψ v := rfl
    rw [map_smul, hc, Stacks.ModuleStalk.Γgerm_smul]
    exact Submodule.smul_mem _ _ hv

private theorem notMem_nonvanishingOpen_iff (ψ : V →ₗ[k] Γ(L, ⊤)) (x : X) (v : V) :
    v ∈ vanishingSubmodule ψ x ↔ x ∉ nonvanishingOpen X L (ψ v) := by
  change (L.presheaf.Γgerm x).hom (ψ v) ∈ Stacks.ModuleStalk.maximalSmul L x ↔ _
  rw [Stacks.NonvanishingOpen.mem_nonvanishingOpen, Stacks.Ample.mem_nonvanishingLocus_iff,
    not_not]

/-- **If the sections `ψ(v)`, `v ∈ V`, do not vanish simultaneously anywhere then neither do the
sections attached to a basis.** A vector is a `k`-combination of the basis vectors and the
scalars act through the structure morphism, so the germ of `ψ(v)` lies in `𝔪ₓ · ℒₓ` as soon as
the germs of the `ψ(vᵢ)` do. -/
theorem iSup_nonvanishingOpen_basis_eq_top (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) :
    ⨆ i : Fin (n + 1), nonvanishingOpen X L (ψ (b i)) = ⊤ := by
  refine eq_top_iff.2 (hψ.ge.trans (iSup_le fun v x hx => ?_))
  by_contra hcon
  have hb : ∀ i : Fin (n + 1), b i ∈ vanishingSubmodule ψ x := by
    intro i
    by_contra hi
    exact hcon (TopologicalSpace.Opens.mem_iSup.2
      ⟨i, not_not.1 (fun h => hi ((notMem_nonvanishingOpen_iff ψ x (b i)).2 h))⟩)
  have hv : v ∈ vanishingSubmodule ψ x := by
    have hle : (⊤ : Submodule k V) ≤ vanishingSubmodule ψ x := by
      rw [← b.span_eq, Submodule.span_le]
      rintro - ⟨i, rfl⟩
      exact hb i
    exact hle Submodule.mem_top
  exact (notMem_nonvanishingOpen_iff ψ x v).1 hv hx

/-- The sections attached to a basis, as a family indexed by `Fin (n + 1)`. -/
abbrev basisSections (ψ : V →ₗ[k] Γ(L, ⊤)) (i : Fin (n + 1)) : Γ(L, ⊤) := ψ (b i)

/-- **The sections attached to a basis generate `ℒ`**, in the stalkwise form
`Stacks.ProjectiveFromSections.toProjectiveSpaceOver` consumes. -/
theorem generatesStalks_basisSections (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) :
    Stacks.ProjectiveFromSections.GeneratesStalks (basisSections b ψ) :=
  Stacks.AmpleImmersionReduction.generatesStalks_of_isOpenCover _
    (iSup_nonvanishingOpen_basis_eq_top b ψ hψ)

/-! ### The preimages of the standard opens -/

/-- **The preimage of the standard open `D₊(Tᵢ)` under the glued morphism of [Stacks, Tag 01ND]
is the nonvanishing open `X_{sᵢ}`.** This is
`Stacks.AmpleImmersionReduction.preimage_standardChart` read on the integral model, through the
lift over the identity of `X`. -/
theorem preimage_basicOpen_toProjectiveSpaceAtUniverse
    (s : Fin (n + 1) → Γ(L, ⊤)) (hs : Stacks.ProjectiveFromSections.GeneratesStalks s)
    (i : Fin (n + 1)) :
    Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse s hs ⁻¹ᵁ
        Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
          (MvPolynomial.X i) =
      Stacks.ProjectiveFromSections.nvCover s i := by
  calc Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse s hs ⁻¹ᵁ
        Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n) (MvPolynomial.X i)
      = (Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hs (𝟙 X) ≫
            projectiveSpaceOver.toIntegralAtUniverse n X) ⁻¹ᵁ
          Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
            (MvPolynomial.X i) := by
          rw [Stacks.ProjectiveFromSections.toProjectiveSpaceOver_snd]
    _ = Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hs (𝟙 X) ⁻¹ᵁ
          projectiveSpaceOver.standardChart n X i := rfl
    _ = Stacks.ProjectiveFromSections.nvCover s i :=
          Stacks.AmpleImmersionReduction.preimage_standardChart s hs _
            (fun j => Stacks.ProjectiveFromSections.ι_toProjectiveSpaceOver s hs (𝟙 X) j) i

/-! ### The two spellings of the ratio `sⱼ / sᵢ` -/

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
/-- The nonvanishing open of the degree-one section attached to a basis vector is the
nonvanishing open of the section itself. -/
theorem nonvanishingOpen_pow_degreeOneElement (ψ : V →ₗ[k] Γ(L, ⊤)) (i : Fin (n + 1)) :
    nonvanishingOpen X (natTensorPow L 1)
        ((veroneseOfLinearMap k V L ψ).pow (degreeOneElement k V (b i)).2 1) =
      Stacks.ProjectiveFromSections.nvCover (basisSections b ψ) i := by
  rw [pow_degreeOneElement, nonvanishingOpen_twistOneSection]

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
omit [Ample.IsInvertibleModule X L] in
private theorem unitorPow_inv_app_hom_app (W : X.Opens) (z : Γ(natTensorPow L 1, W)) :
    (MorphismToProjUniversal.unitorPow L).inv.app W
        ((MorphismToProjUniversal.unitorPow L).hom.app W z) = z := by
  have h : (MorphismToProjUniversal.unitorPow L).hom.app W ≫
      (MorphismToProjUniversal.unitorPow L).inv.app W = 𝟙 _ := by
    rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app]
  rw [← CategoryTheory.comp_apply, h]
  rfl

omit [Ample.IsInvertibleModule X L] in
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
/-- The left unitor carries the restriction of a section read in `ℒ ^⊗ 1` to the restriction of
that section. -/
private theorem unitorPow_app_resTop (W : X.Opens) (t : Γ(L, ⊤)) :
    (MorphismToProjUniversal.unitorPow L).hom.app W
        (Stacks.TensorPowerTrivialize.resTop (natTensorPow L 1) (twistOneSection L t) W) =
      Stacks.ProjectiveFromSections.resT W t := by
  rw [← Stacks.AlgebraicGeometry.ProjSectionsUnique.map_app
    (MorphismToProjUniversal.unitorPow L).hom (le_top : W ≤ ⊤) (twistOneSection L t),
    unitorPow_app_twistOneSection]

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
/-- **The degree-one value of the dehomogenization of `ψ` at `vᵢ` is the ratio `sⱼ/sᵢ`.**

The ring map `a / vᵢ ^ m ↦ ψ(a) / ψ(vᵢ) ^ m` of [Stacks, Tag 01N8] attached to the graded map
extending `ψ`, evaluated on the degree-one fraction `vⱼ / vᵢ`, is the ratio `sⱼ / sᵢ` out of
which the chart morphism of [Stacks, Tag 01ND] is built. Both are the unique function
multiplying `sᵢ` to `sⱼ` over an open where `sᵢ` is nonvanishing, so the identity is the
uniqueness of division by a nonvanishing section; the left unitor `ℒ ^⊗ 1 ≅ ℒ` is what moves one
side to the other. -/
theorem ratio_twistOneSection (ψ : V →ₗ[k] Γ(L, ⊤)) (i j : Fin (n + 1)) {W : X.Opens}
    (hW1 : W ≤ nonvanishingOpen X (natTensorPow L 1)
      ((veroneseOfLinearMap k V L ψ).pow (degreeOneElement k V (b i)).2 1))
    (hW2 : W ≤ Stacks.ProjectiveFromSections.nvCover (basisSections b ψ) i) :
    (veroneseOfLinearMap k V L ψ).ratio (degreeOneElement k V (b i)).2 hW1 1
        (twistOneSection L (ψ (b j))) =
      Stacks.ProjectiveFromSections.resO hW2
        (Stacks.ProjectiveFromSections.ratio (basisSections b ψ) i j) := by
  refine (veroneseOfLinearMap k V L ψ).ratio_eq_of_resTop_eq
    (degreeOneElement k V (b i)).2 hW1 ?_
  have hval : (MorphismToProjUniversal.unitorPow L).hom.app W
        (Stacks.TensorPowerTrivialize.resTop (natTensorPow L 1)
          (twistOneSection L (ψ (b j))) W) =
      (MorphismToProjUniversal.unitorPow L).hom.app W
        (Stacks.ProjectiveFromSections.resO hW2
            (Stacks.ProjectiveFromSections.ratio (basisSections b ψ) i j) •
          Stacks.TensorPowerTrivialize.resTop (natTensorPow L 1)
            ((veroneseOfLinearMap k V L ψ).pow (degreeOneElement k V (b i)).2 1) W) := by
    rw [Scheme.Modules.Hom.app_smul, pow_degreeOneElement, unitorPow_app_resTop,
      unitorPow_app_resTop]
    exact (Stacks.ProjectiveFromSections.resO_ratio_smul (basisSections b ψ) hW2 j).symm
  have h := congrArg ((MorphismToProjUniversal.unitorPow L).inv.app W) hval
  rwa [unitorPow_inv_app_hom_app, unitorPow_inv_app_hom_app] at h

/-! ### The chart ring map of `φ_{ℒ,ψ}` -/

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
/-- **The ring map induced by `φ_{ℒ,ψ}` on the standard open of a basis vector is the
dehomogenization of `ψ`**, over any open on which the section `ψ(vᵢ)` is nonvanishing.

This is the third clause of `Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.Classifies`, which
holds over the nonvanishing open itself, pushed to a smaller open: the induced ring map is
compatible with restriction because `Scheme.Hom.appLE` is, and the dehomogenization is by
`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.lift_res`. -/
theorem appLE_awayToSection_morphismOfGeneratingSections (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) (i : Fin (n + 1)) {W : X.Opens}
    (hW1 : W ≤ nonvanishingOpen X (natTensorPow L 1)
      ((veroneseOfLinearMap k V L ψ).pow (degreeOneElement k V (b i)).2 1))
    (hle : W ≤ morphismOfGeneratingSections k V L ψ hψ ⁻¹ᵁ
      Proj.basicOpen (grading k V) (SymmetricAlgebra.ι k V (b i)))
    (u : HomogeneousLocalization.Away (grading k V) (SymmetricAlgebra.ι k V (b i))) :
    (morphismOfGeneratingSections k V L ψ hψ).appLE
        (Proj.basicOpen (grading k V) (SymmetricAlgebra.ι k V (b i))) W hle
        (Proj.awayToSection (grading k V) (SymmetricAlgebra.ι k V (b i)) u) =
      ((veroneseOfLinearMap k V L ψ).homogeneousRatios
        (degreeOneElement k V (b i)).2 hW1).lift Nat.one_pos u := by
  have hc := (classifies_classifyingPair k V L ψ hψ).2.2 (degreeOneElement k V (b i))
    ((classifies_classifyingPair k V L ψ hψ).1 (degreeOneElement k V (b i))).ge u
  have h := congrArg (X.presheaf.map (homOfLE hW1).op) hc
  rw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_map] at h
  rw [show ((veroneseOfLinearMap k V L ψ).homogeneousRatios
        (degreeOneElement k V (b i)).2 hW1).lift Nat.one_pos u =
      X.presheaf.map (homOfLE hW1).op
        (((veroneseOfLinearMap k V L ψ).homogeneousRatios
          (degreeOneElement k V (b i)).2 le_rfl).lift Nat.one_pos u) from
    congrFun (congrArg DFunLike.coe
      ((veroneseOfLinearMap k V L ψ).lift_res (degreeOneElement k V (b i)).2 le_rfl
        Nat.one_pos hW1)) u]
  exact h

/-! ### The chart ring map of `φ_{(ℒ,(s₀,…,sₙ))}` -/

/-- On the `i`-th chart the `i`-th ratio is `1`, so the basic open it cuts out is everything. -/
theorem basicOpen_sectionsHom_chartRatio (s : Fin (n + 1) → Γ(L, ⊤)) (i : Fin (n + 1)) :
    (Stacks.ProjectiveFromSections.nvCover s i).toScheme.basicOpen
        (Stacks.SectionsToProjectiveSpace.sectionsHom
          (Stacks.ProjectiveFromSections.chartRatio s i) (MvPolynomial.X i)) = ⊤ := by
  rw [Stacks.SectionsToProjectiveSpace.sectionsHom_X,
    Stacks.ProjectiveFromSections.chartRatio_self, Scheme.basicOpen_one]

private theorem map_eqToHom_resTop {Y : Scheme.{u}} {W : Y.Opens} (hW : W = ⊤) (a : Γ(Y, ⊤)) :
    Y.presheaf.map (eqToHom hW.symm).op (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op a) = a := by
  subst hW
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  simp

/-- **The ring map induced by the `i`-th chart morphism of [Stacks, Tag 01ND] on the standard
open `D₊(Tᵢ)` sends the fraction `a / Tᵢ ^ m` to `a` evaluated at the ratios `sₖ/sᵢ`.**

The chart morphism is Mathlib's `AlgebraicGeometry.Proj.fromOfGlobalSections` of the ring map
`Tₖ ↦ sₖ/sᵢ`, whose effect on the sections of a standard open is
`Stacks.ProjGlobalSectionsAppTop.projAwayHom`
(`Stacks.TwistPullbackRatio.appLE_awayToSection`); the denominator `Tᵢ` goes to `1`, so no
inverse survives and the value is the evaluation itself. -/
theorem appLE_awayToSection_chartHom (s : Fin (n + 1) → Γ(L, ⊤)) (i : Fin (n + 1))
    (hle : (⊤ : (Stacks.ProjectiveFromSections.nvCover s i).toScheme.Opens) ≤
      Stacks.ProjectiveFromSections.chartHom s i ⁻¹ᵁ
        Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
          (MvPolynomial.X i))
    (m : ℕ) (x : Stacks.SectionsToProjectiveSpace.coordRing.{u} n)
    (hx : x ∈ Stacks.SectionsToProjectiveSpace.coordGrading.{u} n (m • 1)) :
    (Stacks.ProjectiveFromSections.chartHom s i).appLE
        (Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
          (MvPolynomial.X i)) ⊤ hle
        (Proj.awayToSection (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
          (MvPolynomial.X i)
          (HomogeneousLocalization.Away.mk (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
            (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one i) m x hx)) =
      Stacks.SectionsToProjectiveSpace.sectionsHom
        (Stacks.ProjectiveFromSections.chartRatio s i) x := by
  have hb : (Stacks.ProjectiveFromSections.nvCover s i).toScheme.basicOpen
      (Stacks.SectionsToProjectiveSpace.sectionsHom
        (Stacks.ProjectiveFromSections.chartRatio s i) (MvPolynomial.X i)) = ⊤ :=
    basicOpen_sectionsHom_chartRatio s i
  have hone : Stacks.SectionsToProjectiveSpace.sectionsHom
      (Stacks.ProjectiveFromSections.chartRatio s i) (MvPolynomial.X i) = 1 := by
    rw [Stacks.SectionsToProjectiveSpace.sectionsHom_X,
      Stacks.ProjectiveFromSections.chartRatio_self]
  have hv : Stacks.ProjGlobalSectionsAppTop.resTop
        ((Stacks.ProjectiveFromSections.nvCover s i).toScheme.basicOpen
          (Stacks.SectionsToProjectiveSpace.sectionsHom
            (Stacks.ProjectiveFromSections.chartRatio s i) (MvPolynomial.X i)))
        (Stacks.SectionsToProjectiveSpace.sectionsHom
          (Stacks.ProjectiveFromSections.chartRatio s i) (MvPolynomial.X i)) * 1 = 1 := by
    rw [hone, map_one, mul_one]
  have hchart := Stacks.TwistPullbackRatio.appLE_awayToSection
    (Stacks.ProjectiveFromSections.chartRatio s i)
    (Stacks.ProjectiveFromSections.span_range_chartRatio s i) i
    (HomogeneousLocalization.Away.mk (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
      (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one i) m x hx)
  rw [Stacks.ProjGlobalSectionsAppTop.projAwayHom_apply_mk_of_mul_eq_one
    (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
    (Stacks.SectionsToProjectiveSpace.sectionsHom
      (Stacks.ProjectiveFromSections.chartRatio s i))
    (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one i) m x hx hv,
    one_pow, mul_one] at hchart
  have he : (Stacks.ProjectiveFromSections.nvCover s i).toScheme.basicOpen
      (Stacks.SectionsToProjectiveSpace.sectionsHom
        (Stacks.ProjectiveFromSections.chartRatio s i) (MvPolynomial.X i)) ≤
      Stacks.ProjectiveFromSections.chartHom s i ⁻¹ᵁ
        Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
          (MvPolynomial.X i) := hb.le.trans hle
  have hstep := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_map (f := Stacks.ProjectiveFromSections.chartHom s i) he
      ((eqToHom hb.symm).op))
    (Proj.awayToSection (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
      (MvPolynomial.X i)
      (HomogeneousLocalization.Away.mk (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
        (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one i) m x hx))
  exact hstep.symm.trans ((congrArg
    (fun w => (Stacks.ProjectiveFromSections.nvCover s i).toScheme.presheaf.map
      (eqToHom hb.symm).op w) hchart).trans (map_eqToHom_resTop hb _))

/-! ### The chart ring of the integral model, and two ring maps out of it -/

/-- Restriction along the identity inclusion does nothing. -/
private theorem resO_self {W : X.Opens} (a : Γ(X, W)) :
    Stacks.ProjectiveFromSections.resO (le_refl W) a = a := by
  change X.presheaf.map (homOfLE (le_refl W)).op a = a
  rw [show (homOfLE (le_refl W)).op = 𝟙 (op W) from rfl, CategoryTheory.Functor.map_id]
  rfl

/-- The sections of an open subscheme over `⊤` are the sections of the open, through either of
the two canonical identifications. -/
private alias ι_appLE_eq_topIso_inv := Stacks.RelativeSpec.ι_appLE_self

/-- There is only one ring homomorphism out of the degree-zero part of `ℤ[T₀, …, Tₙ]`: that part
is the ring of constants, a copy of `ℤ`, and `ℤ` is the initial ring. -/
private theorem deg0_ringHom_ext {P : Type*} [CommRing P]
    (α β : Stacks.ProjectiveChart.Deg0 (ULift.{u} ℤ) n →+* P) : α = β := by
  let e : Stacks.ProjectiveChart.Deg0 (ULift.{u} ℤ) n ≃+* ℤ :=
    (Stacks.ProjectiveChart.degreeZeroEquiv (ULift.{u} ℤ) n).trans ULift.ringEquiv
  have h : α.comp (e.symm : ℤ →+* _) = β.comp (e.symm : ℤ →+* _) := RingHom.ext_int _ _
  refine RingHom.ext fun r => ?_
  have h2 : α (e.symm (e r)) = β (e.symm (e r)) := RingHom.congr_fun h (e r)
  rwa [e.symm_apply_apply] at h2

/-- **Two ring homomorphisms out of the `i`-th chart ring `ℤ[T₀, …, Tₙ]_{(Tᵢ)}` of the integral
model that agree on the degree-one fractions `Tⱼ / Tᵢ` are equal.**

The chart ring is the polynomial ring on those fractions over its degree-zero part
(`Stacks.ProjectiveChart.chartHom_surjective`, which is Mathlib's
`HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top` for the coordinate variables), and the
degree-zero part is a copy of `ℤ`, out of which there is only one ring homomorphism. So the
degree-one fractions determine a ring map out of the chart ring in every degree. -/
theorem away_ringHom_ext_isLocalizationElem {P : Type*} [CommRing P] (i : Fin (n + 1))
    {α β : HomogeneousLocalization.Away
        (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n) (MvPolynomial.X i) →+* P}
    (h : ∀ j : Fin (n + 1),
      α (HomogeneousLocalization.Away.isLocalizationElem
          (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} i)
          (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} j)) =
        β (HomogeneousLocalization.Away.isLocalizationElem
          (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} i)
          (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} j))) :
    α = β := by
  have hcomp : α.comp (Stacks.ProjectiveChart.chartHom (ULift.{u} ℤ) i).toRingHom =
      β.comp (Stacks.ProjectiveChart.chartHom (ULift.{u} ℤ) i).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · change α (Stacks.ProjectiveChart.chartHom (ULift.{u} ℤ) i (MvPolynomial.C r)) =
        β (Stacks.ProjectiveChart.chartHom (ULift.{u} ℤ) i (MvPolynomial.C r))
      rw [show Stacks.ProjectiveChart.chartHom (ULift.{u} ℤ) i (MvPolynomial.C r) =
          algebraMap (Stacks.ProjectiveChart.Deg0 (ULift.{u} ℤ) n)
            (Stacks.ProjectiveChart.ChartRing (ULift.{u} ℤ) n i) r from
        MvPolynomial.aeval_C _ _]
      exact RingHom.congr_fun (deg0_ringHom_ext
        (α.comp (algebraMap (Stacks.ProjectiveChart.Deg0 (ULift.{u} ℤ) n)
          (Stacks.ProjectiveChart.ChartRing (ULift.{u} ℤ) n i)))
        (β.comp (algebraMap (Stacks.ProjectiveChart.Deg0 (ULift.{u} ℤ) n)
          (Stacks.ProjectiveChart.ChartRing (ULift.{u} ℤ) n i)))) r
    · change α (Stacks.ProjectiveChart.chartHom (ULift.{u} ℤ) i (MvPolynomial.X j)) =
        β (Stacks.ProjectiveChart.chartHom (ULift.{u} ℤ) i (MvPolynomial.X j))
      rw [show Stacks.ProjectiveChart.chartHom (ULift.{u} ℤ) i (MvPolynomial.X j) =
          Stacks.ProjectiveChart.ratio (ULift.{u} ℤ) i (i.succAbove j) from
        MvPolynomial.aeval_X _ _]
      exact h (i.succAbove j)
  refine RingHom.ext fun z => ?_
  obtain ⟨q, rfl⟩ := Stacks.ProjectiveChart.chartHom_surjective (ULift.{u} ℤ) i z
  exact RingHom.congr_fun hcomp q

/-! ### The two chart ring maps on the degree-one fractions -/

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
/-- **The preimage of the standard open of a basis vector under `φ_{ℒ,ψ}` is `X_{sᵢ}`.** This is
clause (a) of [Stacks, Tag 01N8] for the degree-one element `vᵢ`, read through the identification
of the nonvanishing open of `ψ(vᵢ)` in `ℒ ^⊗ 1` with the one in `ℒ`. The element is spelled as
the image of `Tᵢ` under `coordHom`, which is how the comparison with `ℙⁿ` meets it. -/
theorem preimage_basicOpen_morphismOfGeneratingSections (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) (i : Fin (n + 1)) :
    morphismOfGeneratingSections k V L ψ hψ ⁻¹ᵁ
        Proj.basicOpen (grading k V) (coordHom b (MvPolynomial.X i)) =
      Stacks.ProjectiveFromSections.nvCover (basisSections b ψ) i := by
  rw [coordHom_X]
  exact ((classifies_classifyingPair k V L ψ hψ).1 (degreeOneElement k V (b i))).trans
    (nonvanishingOpen_pow_degreeOneElement b ψ i)

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
/-- **The chart ring map of `φ_{ℒ,ψ}` sends the degree-one fraction `vⱼ / vᵢ` to the ratio
`sⱼ / sᵢ`.** This is `ratio_twistOneSection` read through the computation
`appLE_awayToSection_morphismOfGeneratingSections` of the chart ring map, with
`Stacks.MorphismToProj.HomogeneousRatios.lift_mk` naming the value on a fraction.

The two degree-one elements are taken as variables constrained to be the basis vectors: the
fraction `vⱼ / vᵢ` lives in a ring that depends on `vᵢ`, so the comparison with `ℙⁿ`, which meets
`vᵢ` as the image of `Tᵢ`, could not otherwise be stated. -/
private theorem appLE_awayToSection_isLocalizationElem (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) (i j : Fin (n + 1))
    (f g : grading k V 1) (hf : f = degreeOneElement k V (b i))
    (hg : g = degreeOneElement k V (b j))
    (hle : Stacks.ProjectiveFromSections.nvCover (basisSections b ψ) i ≤
      morphismOfGeneratingSections k V L ψ hψ ⁻¹ᵁ
        Proj.basicOpen (grading k V) (f : SymmetricAlgebra k V)) :
    (morphismOfGeneratingSections k V L ψ hψ).appLE
        (Proj.basicOpen (grading k V) (f : SymmetricAlgebra k V))
        (Stacks.ProjectiveFromSections.nvCover (basisSections b ψ) i) hle
        (Proj.awayToSection (grading k V) (f : SymmetricAlgebra k V)
          (HomogeneousLocalization.Away.isLocalizationElem f.2 g.2)) =
      Stacks.ProjectiveFromSections.ratio (basisSections b ψ) i j := by
  subst hf
  subst hg
  have hW1 : Stacks.ProjectiveFromSections.nvCover (basisSections b ψ) i ≤
      nonvanishingOpen X (natTensorPow L 1)
        ((veroneseOfLinearMap k V L ψ).pow (degreeOneElement k V (b i)).2 1) :=
    (nonvanishingOpen_pow_degreeOneElement b ψ i).ge
  have hmem : (SymmetricAlgebra.ι k V (b j)) ^ 1 ∈ grading k V (1 * 1) := by
    simp
  refine (appLE_awayToSection_morphismOfGeneratingSections b ψ hψ i hW1 hle _).trans ?_
  rw [show HomogeneousLocalization.Away.isLocalizationElem
        (degreeOneElement k V (b i)).2 (degreeOneElement k V (b j)).2 =
      HomogeneousLocalization.Away.mk (grading k V) (degreeOneElement k V (b i)).2 1
        ((SymmetricAlgebra.ι k V (b j)) ^ 1) (by simp)
      from rfl,
    ((veroneseOfLinearMap k V L ψ).homogeneousRatios
      (degreeOneElement k V (b i)).2 hW1).lift_mk Nat.one_pos 1
      ((SymmetricAlgebra.ι k V (b j)) ^ 1) _ ⟨_, hmem⟩ rfl]
  change (veroneseOfLinearMap k V L ψ).ratio (degreeOneElement k V (b i)).2 hW1 1
      ((veroneseOfLinearMap k V L ψ).toFun 1 ⟨(SymmetricAlgebra.ι k V (b j)) ^ 1, hmem⟩) = _
  rw [(veroneseOfLinearMap k V L ψ).toFun_eq_pow (degreeOneElement k V (b j)).2 1
      ⟨(SymmetricAlgebra.ι k V (b j)) ^ 1, hmem⟩ rfl,
    pow_degreeOneElement, ratio_twistOneSection b ψ i j hW1 le_rfl]
  exact resO_self _

/-- The sections induced by a composite on an intermediate open are the composite of the induced
section maps. -/
private theorem appLE_comp_appLE_apply {S T R : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ R) (U : R.Opens)
    (V : T.Opens) (W : S.Opens) (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (z : Γ(R, U)) :
    (f ≫ g).appLE U W (e₂.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE e₁)).le) z =
      f.appLE V W e₂ (g.appLE U V e₁ z) :=
  (ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂) z).symm

private theorem appLE_congr_hom {Y Z : Scheme.{u}} {p q : Y ⟶ Z} (hpq : p = q) {U : Z.Opens}
    {W : Y.Opens} (e : W ≤ p ⁻¹ᵁ U) (e' : W ≤ q ⁻¹ᵁ U) (z : Γ(Z, U)) :
    p.appLE U W e z = q.appLE U W e' z := by
  subst hpq
  rfl

/-- **The chart ring map of `φ_{(ℒ,(sᵢ))}` sends the degree-one fraction `Tⱼ / Tᵢ` to the ratio
`sⱼ / sᵢ`.** This is `appLE_awayToSection_chartHom` on the `i`-th chart, carried from the open
subscheme `X_{sᵢ}` to the open `X_{sᵢ}` of `X` by
`AlgebraicGeometry.Scheme.Opens.topIso`; the glued morphism restricted to the chart is the chart
morphism, which is `Stacks.ProjectiveFromSections.ι_toProjectiveSpaceAtUniverse`. -/
private theorem appLE_awayToSection_toProjectiveSpaceAtUniverse_isLocalizationElem
    (s : Fin (n + 1) → Γ(L, ⊤)) (hs : Stacks.ProjectiveFromSections.GeneratesStalks s)
    (i j : Fin (n + 1))
    (hle : Stacks.ProjectiveFromSections.nvCover s i ≤
      Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse s hs ⁻¹ᵁ
        Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
          (MvPolynomial.X i)) :
    (Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse s hs).appLE
        (Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n) (MvPolynomial.X i))
        (Stacks.ProjectiveFromSections.nvCover s i) hle
        (Proj.awayToSection (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
          (MvPolynomial.X i)
          (HomogeneousLocalization.Away.isLocalizationElem
            (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} i)
            (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} j))) =
      Stacks.ProjectiveFromSections.ratio s i j := by
  have hchart : (⊤ : (Stacks.ProjectiveFromSections.nvCover s i).toScheme.Opens) ≤
      Stacks.ProjectiveFromSections.chartHom s i ⁻¹ᵁ
        Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
          (MvPolynomial.X i) := by
    rw [← Stacks.ProjectiveFromSections.ι_toProjectiveSpaceAtUniverse s hs i]
    exact le_trans (Scheme.Opens.ι_preimage_self _).ge
      (show (Stacks.ProjectiveFromSections.nvCover s i).ι ⁻¹ᵁ
            Stacks.ProjectiveFromSections.nvCover s i ≤
          (Stacks.ProjectiveFromSections.nvCover s i).ι ⁻¹ᵁ
            (Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse s hs ⁻¹ᵁ
              Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
                (MvPolynomial.X i)) from fun _ hx => hle hx)
  have hcomp := appLE_comp_appLE_apply (Stacks.ProjectiveFromSections.nvCover s i).ι
      (Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse s hs)
      (Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n) (MvPolynomial.X i))
      (Stacks.ProjectiveFromSections.nvCover s i) ⊤ hle
      (Scheme.Opens.ι_preimage_self _).ge
    (Proj.awayToSection (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
      (MvPolynomial.X i)
      (HomogeneousLocalization.Away.isLocalizationElem
        (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} i)
        (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} j)))
  have hchartval : (Stacks.ProjectiveFromSections.chartHom s i).appLE
        (Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n) (MvPolynomial.X i))
        ⊤ hchart
        (Proj.awayToSection (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
          (MvPolynomial.X i)
          (HomogeneousLocalization.Away.isLocalizationElem
            (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} i)
            (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} j))) =
      Stacks.ProjectiveFromSections.chartRatio s i j := by
    refine Eq.trans (appLE_awayToSection_chartHom s i hchart 1
      ((MvPolynomial.X j : Stacks.SectionsToProjectiveSpace.coordRing.{u} n) ^ 1)
      (by simpa using Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} j)) ?_
    rw [map_pow, Stacks.SectionsToProjectiveSpace.sectionsHom_X, pow_one]
  have hfull := (CategoryTheory.ConcreteCategory.congr_hom
      (ι_appLE_eq_topIso_inv (Stacks.ProjectiveFromSections.nvCover s i))
      ((Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse s hs).appLE
        (Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
          (MvPolynomial.X i))
        (Stacks.ProjectiveFromSections.nvCover s i) hle
        (Proj.awayToSection (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
          (MvPolynomial.X i)
          (HomogeneousLocalization.Away.isLocalizationElem
            (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} i)
            (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} j))))).symm.trans
    (hcomp.symm.trans ((appLE_congr_hom
        (Stacks.ProjectiveFromSections.ι_toProjectiveSpaceAtUniverse s hs i) _ hchart
        _).trans hchartval))
  exact (Iso.inv_hom_id_apply _ _).symm.trans
    ((congrArg (fun y => (Stacks.ProjectiveFromSections.nvCover s i).topIso.hom y) hfull).trans
      (Iso.inv_hom_id_apply _ (Stacks.ProjectiveFromSections.ratio s i j)))

/-! ### Clause (6) of [Stacks, Tag 0FCY] on the integral model -/

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
/-- The two chart ring maps agree, as ring maps out of `ℤ[T₀, …, Tₙ]_{(Tᵢ)}`. Both send the
degree-one fraction `Tⱼ/Tᵢ` to the ratio `sⱼ/sᵢ`, which determines them by
`away_ringHom_ext_isLocalizationElem`. -/
private theorem comp_awayToSection_eq (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) (i : Fin (n + 1))
    (h₁ : Stacks.ProjectiveFromSections.nvCover (basisSections b ψ) i ≤
      (morphismOfGeneratingSections k V L ψ hψ ≫
          AlgebraicGeometry.Proj.map (coordHom b) (irrelevant_le_map_coordHom b)) ⁻¹ᵁ
        Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n) (MvPolynomial.X i))
    (h₂ : Stacks.ProjectiveFromSections.nvCover (basisSections b ψ) i ≤
      Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse (basisSections b ψ)
          (generatesStalks_basisSections b ψ hψ) ⁻¹ᵁ
        Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
          (MvPolynomial.X i)) :
    ((morphismOfGeneratingSections k V L ψ hψ ≫
            AlgebraicGeometry.Proj.map (coordHom b) (irrelevant_le_map_coordHom b)).appLE
          (Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
            (MvPolynomial.X i))
          (Stacks.ProjectiveFromSections.nvCover (basisSections b ψ) i) h₁).hom.comp
        (Proj.awayToSection (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
          (MvPolynomial.X i)).hom =
      ((Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse (basisSections b ψ)
            (generatesStalks_basisSections b ψ hψ)).appLE
          (Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
            (MvPolynomial.X i))
          (Stacks.ProjectiveFromSections.nvCover (basisSections b ψ) i) h₂).hom.comp
        (Proj.awayToSection (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
          (MvPolynomial.X i)).hom := by
  refine away_ringHom_ext_isLocalizationElem i fun j => ?_
  have hpre := preimage_basicOpen_morphismOfGeneratingSections b ψ hψ i
  have haway : (AlgebraicGeometry.Proj.map (coordHom b) (irrelevant_le_map_coordHom b)).appLE
        (Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n) (MvPolynomial.X i))
        (Proj.basicOpen (grading k V) (coordHom b (MvPolynomial.X i)))
        (AlgebraicGeometry.Proj.map_preimage_basicOpen (coordHom b)
          (irrelevant_le_map_coordHom b) (MvPolynomial.X i)).ge
        (Proj.awayToSection (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
          (MvPolynomial.X i)
          (HomogeneousLocalization.Away.isLocalizationElem
            (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} i)
            (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} j))) =
      Proj.awayToSection (grading k V) (coordHom b (MvPolynomial.X i))
        (HomogeneousLocalization.Away.isLocalizationElem
          ((coordHom b).map_mem
            (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} i))
          ((coordHom b).map_mem
            (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} j))) := by
    have h := CategoryTheory.ConcreteCategory.congr_hom
      (AlgebraicGeometry.Proj.awayToSection_comp_appLE (coordHom b)
        (irrelevant_le_map_coordHom b)
        (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} i))
      (HomogeneousLocalization.Away.isLocalizationElem
        (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} i)
        (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} j))
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at h
    refine h.trans (congrArg
      (fun w => Proj.awayToSection (grading k V) (coordHom b (MvPolynomial.X i)) w)
      (Stacks.AlgebraicGeometry.ProjTwistChain.map_isLocalizationElem
        (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n) (grading k V) (coordHom b)
        (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} i)
        (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} j)))
  have hsplit := appLE_comp_appLE_apply (morphismOfGeneratingSections k V L ψ hψ)
      (AlgebraicGeometry.Proj.map (coordHom b) (irrelevant_le_map_coordHom b))
      (Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n) (MvPolynomial.X i))
      (Proj.basicOpen (grading k V) (coordHom b (MvPolynomial.X i)))
      (Stacks.ProjectiveFromSections.nvCover (basisSections b ψ) i)
      (AlgebraicGeometry.Proj.map_preimage_basicOpen (coordHom b)
        (irrelevant_le_map_coordHom b) (MvPolynomial.X i)).ge hpre.ge
    (Proj.awayToSection (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
      (MvPolynomial.X i)
      (HomogeneousLocalization.Away.isLocalizationElem
        (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} i)
        (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} j)))
  rw [haway] at hsplit
  refine Eq.trans hsplit ?_
  refine Eq.trans (appLE_awayToSection_isLocalizationElem b ψ hψ i j
    ⟨coordHom b (MvPolynomial.X i), (coordHom b).map_mem
      (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} i)⟩
    ⟨coordHom b (MvPolynomial.X j), (coordHom b).map_mem
      (Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} j)⟩
    (Subtype.ext (coordHom_X b i)) (Subtype.ext (coordHom_X b j)) hpre.ge) ?_
  exact (appLE_awayToSection_toProjectiveSpaceAtUniverse_isLocalizationElem
    (basisSections b ψ) (generatesStalks_basisSections b ψ hψ) i j h₂).symm

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
/-- **Stacks Project, Tag 0FCY, clause (6), on the integral model.** For a basis `v₀, …, vₙ` of
`V`, the morphism `φ_{ℒ,ψ}` followed by the coordinate comparison `𝐏(V) ⟶ ℙⁿ_ℤ` of the basis is
the morphism `φ_{(ℒ,(s₀,…,sₙ))}` of [Stacks, Tag 01ND] for the sections `sᵢ = ψ(vᵢ)`.

The two morphisms have the same preimage of each standard open `D₊(Tᵢ)`, namely `X_{sᵢ}`
(`preimage_basicOpen_morphismOfGeneratingSections` and
`preimage_basicOpen_toProjectiveSpaceAtUniverse`), the `X_{sᵢ}` cover `X`, and the two induced
ring maps `ℤ[T₀, …, Tₙ]_{(Tᵢ)} ⟶ Γ(X_{sᵢ}, 𝒪_X)` agree: both send `Tⱼ/Tᵢ` to the ratio `sⱼ/sᵢ`,
and the degree-one fractions determine a ring map out of the chart ring. -/
theorem map_coordHom_morphismOfGeneratingSections (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) :
    morphismOfGeneratingSections k V L ψ hψ ≫
        AlgebraicGeometry.Proj.map (coordHom b) (irrelevant_le_map_coordHom b) =
      Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse (basisSections b ψ)
        (generatesStalks_basisSections b ψ hψ) := by
  have hW : ∀ i : Fin (n + 1),
      (morphismOfGeneratingSections k V L ψ hψ ≫
          AlgebraicGeometry.Proj.map (coordHom b) (irrelevant_le_map_coordHom b)) ⁻¹ᵁ
          Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
            (MvPolynomial.X i) =
        Stacks.ProjectiveFromSections.nvCover (basisSections b ψ) i := fun i => by
    rw [Scheme.Hom.comp_preimage, AlgebraicGeometry.Proj.map_preimage_basicOpen]
    exact preimage_basicOpen_morphismOfGeneratingSections b ψ hψ i
  have hW' : ∀ i : Fin (n + 1),
      Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse (basisSections b ψ)
            (generatesStalks_basisSections b ψ hψ) ⁻¹ᵁ
          Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
            (MvPolynomial.X i) =
        Stacks.ProjectiveFromSections.nvCover (basisSections b ψ) i := fun i =>
    preimage_basicOpen_toProjectiveSpaceAtUniverse (basisSections b ψ)
      (generatesStalks_basisSections b ψ hψ) i
  exact Stacks.AlgebraicGeometry.ProjChartFullGraded.eq_of_appLE_eq_on_away
    (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)
    (fun i : Fin (n + 1) => Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one.{u} i)
    (fun _ => Nat.one_pos) hW hW'
    (iSup_nonvanishingOpen_basis_eq_top b ψ hψ)
    (fun i _ _ _ => RingHom.congr_fun
      (comp_awayToSection_eq b ψ hψ i (hW i).ge (hW' i).ge) _)

/-! ### The projection of the coordinate square to the integral model -/

/-- **The repository's coordinate projection to the integral model is Mathlib's `Proj.map`.**
`Stacks.AlgebraicGeometry.ProjPolyChart.coordinateProjMap` is built from the partial `Proj`
functoriality `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom`, which is defined on the Tag 01MY
domain of definition; when that domain is everything the two morphisms agree. -/
theorem coordinateProjMap_eq_projMap
    (φ : Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) n →+*ᵍ
      Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k n)
    (hdom : Stacks.AlgebraicGeometry.ProjShared.mapDomain
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) n)
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k n) φ = ⊤)
    (hφ : HomogeneousIdeal.irrelevant
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k n) ≤
      (HomogeneousIdeal.irrelevant
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) n)).map φ) :
    Stacks.AlgebraicGeometry.ProjPolyChart.coordinateProjMap k n φ hdom =
      AlgebraicGeometry.Proj.map φ hφ :=
  Stacks.AlgebraicGeometry.ProjBaseChange.mapHom_eq_projMap _ _ φ hφ hdom

/-- The underlying morphism of schemes of the coordinate isomorphism `𝐏(V) ≅ ℙⁿ_k` of a basis:
the identification of `𝐏(V)` with the polynomial model followed by the comparison of the
polynomial model with the base-change model. -/
theorem basisProjectiveSpaceOfModuleIso_hom_left :
    (AlgebraicGeometry.basisProjectiveSpaceOfModuleIso b).hom.left =
      (AlgebraicGeometry.projectiveSpaceOfModuleIsoProjMvPolynomial b).hom ≫
        (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k n).iso.inv := rfl

/-- **The coordinate isomorphism `𝐏(V) ≅ ℙⁿ_k` of a basis, followed by the projection of `ℙⁿ_k`
to the integral model, is `Proj` of the graded map `Tᵢ ↦ vᵢ`.** The coordinate comparison is
pinned by its compatibility with that projection, which is the `toIntegral` clause of
`Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison`; the clause is stated through
`Stacks.AlgebraicGeometry.ProjPolyChart.coordinateProjMap`, which `coordinateProjMap_eq_projMap`
turns into Mathlib's `AlgebraicGeometry.Proj.map`, and then the two coefficient maps compose by
`AlgebraicGeometry.Proj.map_comp`. -/
theorem basisProjectiveSpaceOfModuleIso_hom_left_comp_toIntegralAtUniverse :
    ((AlgebraicGeometry.projectiveSpaceOfModuleIsoProjMvPolynomial b).hom ≫
          (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k n).iso.inv) ≫
        AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n
          (Spec (CommRingCat.of k)) =
      AlgebraicGeometry.Proj.map (coordHom b) (irrelevant_le_map_coordHom b) := by
  have hirr : HomogeneousIdeal.irrelevant
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k n) ≤
      (HomogeneousIdeal.irrelevant
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) n)).map
        (Stacks.AlgebraicGeometry.ProjPolyChart.integralGradedHom k n) :=
    Stacks.AlgebraicGeometry.ProjPolyChart.irrelevant_le_map_coeffGradedHom (ULift.{u} ℤ) n
      (Stacks.AlgebraicGeometry.ProjPolyChart.integralCoeffHom k)
  have hmap : Stacks.AlgebraicGeometry.ProjPolyChart.coordinateProjMap k n
        (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k n).coordinateMap
        (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k n).domain_eq_top =
      AlgebraicGeometry.Proj.map
        (Stacks.AlgebraicGeometry.ProjPolyChart.integralGradedHom k n) hirr :=
    coordinateProjMap_eq_projMap _ _ hirr
  rw [← (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k n).toIntegral,
    Category.assoc,
    ← Category.assoc
      (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k n).iso.inv,
    Iso.inv_hom_id, Category.id_comp, hmap,
    AlgebraicGeometry.projectiveSpaceOfModuleIsoProjMvPolynomial_hom]
  exact (AlgebraicGeometry.Proj.map_comp _ _ hirr
    (AlgebraicGeometry.irrelevant_le_map_gradedMvPolynomialInv b)).symm

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
/-- **Stacks Project, Tag 0FCY, clause (6), the projection to the integral model.** For a basis
`v₀, …, vₙ` of `V`, the morphism `φ_{ℒ,ψ}` followed by the coordinate isomorphism
`𝐏(V) ≅ ℙⁿ_k` and the projection of `ℙⁿ_k` to the integral model is the morphism
`φ_{(ℒ,(s₀,…,sₙ))}` of [Stacks, Tag 01ND] for the sections `sᵢ = ψ(vᵢ)`, read on the integral
model.

This is one of the two legs of the coordinate square: `ℙⁿ_k` is the fibre product of `Spec k`
with the integral model, so equating two morphisms into it means equating both projections. -/
theorem morphismOfGeneratingSections_comp_basisIso_toIntegralAtUniverse (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) :
    morphismOfGeneratingSections k V L ψ hψ ≫
        ((AlgebraicGeometry.basisProjectiveSpaceOfModuleIso b).hom.left ≫
          AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n
            (Spec (CommRingCat.of k)) :
          AlgebraicGeometry.projectiveSpaceOfModule k V ⟶
            AlgebraicGeometry.Proj (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)) =
      Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse (basisSections b ψ)
        (generatesStalks_basisSections b ψ hψ) :=
  (congrArg (fun q : AlgebraicGeometry.projectiveSpaceOfModule k V ⟶
      AlgebraicGeometry.Proj (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n) =>
        morphismOfGeneratingSections k V L ψ hψ ≫ q)
    (show ((AlgebraicGeometry.basisProjectiveSpaceOfModuleIso b).hom.left ≫
          AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n
            (Spec (CommRingCat.of k)) :
          AlgebraicGeometry.projectiveSpaceOfModule k V ⟶
            AlgebraicGeometry.Proj (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n)) =
        AlgebraicGeometry.Proj.map (coordHom b) (irrelevant_le_map_coordHom b) from
      basisProjectiveSpaceOfModuleIso_hom_left_comp_toIntegralAtUniverse b)).trans
    (map_coordHom_morphismOfGeneratingSections b ψ hψ)

/-! ### The structure morphism of `Proj` on a standard open -/

/-- **On the standard open of a homogeneous element of positive degree the structure morphism
`Proj A ⟶ Spec A₀` is the inclusion of the degree-zero part into the chart ring**: a degree-zero
element `z` goes to the fraction `z / 1` of `A_{(g)}`. This is Mathlib's
`AlgebraicGeometry.Proj.awayι_toSpecZero`, read on `D₊(g)` itself rather than on its affine model
`Spec A_{(g)}`. -/
private theorem ΓSpecIso_inv_appLE_toSpecZero {σ' : Type*} {A : Type u} [CommRing A]
    [SetLike σ' A] [AddSubgroupClass σ' A] (𝒜 : ℕ → σ') [GradedRing 𝒜] {m : ℕ} {g : A}
    (hg : g ∈ 𝒜 m) (hm : 0 < m)
    (hle : Proj.basicOpen 𝒜 g ≤ AlgebraicGeometry.Proj.toSpecZero 𝒜 ⁻¹ᵁ ⊤) :
    (Scheme.ΓSpecIso (CommRingCat.of ↥(𝒜 0))).inv ≫
        (AlgebraicGeometry.Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 g) hle =
      CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers g)) ≫
        Proj.awayToSection 𝒜 g := by
  have hι : (Proj.basicOpen 𝒜 g).ι ≫ AlgebraicGeometry.Proj.toSpecZero 𝒜 =
      Proj.basicOpenToSpec 𝒜 g ≫ Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers g))) := by
    rw [← AlgebraicGeometry.Proj.awayι_toSpecZero 𝒜 g hg hm,
      ← AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι 𝒜 g hg hm,
      ← AlgebraicGeometry.Proj.basicOpenIsoSpec_hom 𝒜 g hg hm, Category.assoc,
      Iso.hom_inv_id_assoc]
  have h1 : (AlgebraicGeometry.Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 g) hle ≫
        (Proj.basicOpen 𝒜 g).topIso.inv =
      ((Proj.basicOpen 𝒜 g).ι ≫ AlgebraicGeometry.Proj.toSpecZero 𝒜).appTop := by
    rw [← ι_appLE_eq_topIso_inv, Scheme.Hom.appLE_comp_appLE]
    exact Scheme.Hom.appLE_eq_app _
  rw [← cancel_mono (Proj.basicOpen 𝒜 g).topIso.inv]
  simp only [Category.assoc]
  rw [h1, hι, Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc,
    show (Proj.basicOpenToSpec 𝒜 g).appTop = _ from
      AlgebraicGeometry.Proj.basicOpenToSpec_app_top 𝒜 g]
  simp only [Iso.inv_hom_id_assoc]

/-! ### Clause (5) of [Stacks, Tag 0FCY]: the morphism is a morphism over `Spec k` -/

section OverBase

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.sectionAlgebra

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

open MonoidalCategory
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections

/-- Restriction of a global section of an `𝒪_X`-module is semilinear over restriction of
functions. -/
private theorem resTop_smul {Y : Scheme.{u}} (M : Y.Modules) (W : Y.Opens) (c : Γ(Y, ⊤))
    (x : Γ(M, ⊤)) :
    Stacks.TensorPowerTrivialize.resTop M (c • x) W
      = Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op c •
        Stacks.TensorPowerTrivialize.resTop M x W :=
  Scheme.Modules.map_smul M (homOfLE (le_top : W ≤ ⊤)) c x

/-- **The graded map extending `ψ` sends a scalar to the degree-zero element it names.** The
extension is a `k`-algebra map and the `k`-algebra structure on the section ring is the
degree-zero part composed with the structure morphism, so the value on `r` is the endomorphism of
the monoidal unit attached to the function `r` names on `X`. -/
private theorem psiAlg_algebraMap (ψ : V →ₗ[k] Γ(L, ⊤)) (r : k) :
    psiAlg k V L ψ (algebraMap k (SymmetricAlgebra k V) r)
      = DirectSum.of (Stacks.GradedSections.powSections L) 0
        ((Stacks.SectionRingGeometric.unitScalarEquiv X).symm (baseRingHom k X r)) := by
  rw [AlgHom.commutes]
  exact algebraMap_eq k L r

/-- **The ring map induced by `φ_{ℒ,ψ}` followed by `𝐏(V) ⟶ Spec Sym⁰_k V` on `X_{ψ(f)}` is the
dehomogenization of `ψ` at the degree-zero fractions.** The structure morphism of `𝐏(V)`
restricted to `D₊(f)` is the inclusion `z ↦ z / 1` of the degree-zero part into the chart ring
(`ΓSpecIso_inv_appLE_toSpecZero`), and `φ_{ℒ,ψ}` induces the dehomogenization on the chart ring
by clause (c) of `Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.Classifies`. -/
private theorem appLE_toSpecZero_morphismOfGeneratingSections (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) (f : grading k V 1)
    (hle : nvOpen (grading k V) (veroneseOfLinearMap k V L ψ) f ≤
      (morphismOfGeneratingSections k V L ψ hψ ≫
        AlgebraicGeometry.Proj.toSpecZero (grading k V)) ⁻¹ᵁ ⊤)
    (z : ↥(grading k V 0)) :
    (morphismOfGeneratingSections k V L ψ hψ ≫
          AlgebraicGeometry.Proj.toSpecZero (grading k V)).appLE ⊤
        (nvOpen (grading k V) (veroneseOfLinearMap k V L ψ) f) hle
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(grading k V 0))).inv z) =
      ((veroneseOfLinearMap k V L ψ).homogeneousRatios f.2 le_rfl).lift Nat.one_pos
        (HomogeneousLocalization.fromZeroRingHom (grading k V)
          (Submonoid.powers (f : SymmetricAlgebra k V)) z) := by
  have hpre : nvOpen (grading k V) (veroneseOfLinearMap k V L ψ) f ≤
      morphismOfGeneratingSections k V L ψ hψ ⁻¹ᵁ
        Proj.basicOpen (grading k V) (f : SymmetricAlgebra k V) :=
    ((classifies_classifyingPair k V L ψ hψ).1 f).ge
  have htop : Proj.basicOpen (grading k V) (f : SymmetricAlgebra k V) ≤
      AlgebraicGeometry.Proj.toSpecZero (grading k V) ⁻¹ᵁ ⊤ := le_top
  have hsplit := appLE_comp_appLE_apply (morphismOfGeneratingSections k V L ψ hψ)
    (AlgebraicGeometry.Proj.toSpecZero (grading k V)) ⊤
    (Proj.basicOpen (grading k V) (f : SymmetricAlgebra k V))
    (nvOpen (grading k V) (veroneseOfLinearMap k V L ψ) f) htop hpre
    ((Scheme.ΓSpecIso (CommRingCat.of ↥(grading k V 0))).inv z)
  have hzero := CategoryTheory.ConcreteCategory.congr_hom
    (ΓSpecIso_inv_appLE_toSpecZero (grading k V) f.2 Nat.one_pos htop) z
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hzero
  rw [hzero] at hsplit
  rw [hsplit]
  exact (classifies_classifyingPair k V L ψ hψ).2.2 f hpre _

/-- **The dehomogenization of `ψ` at `vᵢ` sends the degree-zero fraction `r / 1` of a scalar to
the function `r` names on `X`.** The extension of `ψ` carries the scalar `r` to the function
`r` names times the degree-zero section `ψ(1)`
(`Stacks.SectionRingGeometric.globalSection_unitComp`), and the ratio of that section by itself
is `1`; so the ratio of the value by `ψ(f) ^ 0` is the restriction of the function. -/
private theorem lift_fromZeroRingHom_algebraMap (ψ : V →ₗ[k] Γ(L, ⊤)) (f : grading k V 1)
    (r : k) :
    ((veroneseOfLinearMap k V L ψ).homogeneousRatios f.2 le_rfl).lift Nat.one_pos
        (HomogeneousLocalization.fromZeroRingHom (grading k V)
          (Submonoid.powers (f : SymmetricAlgebra k V)) (algebraMap k ↥(grading k V 0) r)) =
      X.presheaf.map (homOfLE (le_top :
        nvOpen (grading k V) (veroneseOfLinearMap k V L ψ) f ≤ ⊤)).op (baseRingHom k X r) := by
  have hcoe : ((algebraMap k ↥(grading k V 0) r : ↥(grading k V 0)) : SymmetricAlgebra k V)
      = algebraMap k (SymmetricAlgebra k V) r := rfl
  have h0 : ((algebraMap k ↥(grading k V 0) r : ↥(grading k V 0)) : SymmetricAlgebra k V)
      ∈ grading k V (0 • 1) := by
    simpa only [zero_smul] using (algebraMap k ↥(grading k V 0) r).2
  have h0' : ((algebraMap k ↥(grading k V 0) r : ↥(grading k V 0)) : SymmetricAlgebra k V)
      ∈ grading k V (0 * 1) := by
    simpa only [Nat.zero_mul] using (algebraMap k ↥(grading k V 0) r).2
  have hmk : HomogeneousLocalization.fromZeroRingHom (grading k V)
        (Submonoid.powers (f : SymmetricAlgebra k V)) (algebraMap k ↥(grading k V 0) r)
      = HomogeneousLocalization.Away.mk (grading k V) f.2 0 _ h0 := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk]
    change Localization.mk _ 1 = _
    congr 1
    exact Subtype.ext (pow_zero (f : SymmetricAlgebra k V)).symm
  have hone : (1 : Stacks.GradedSections.sectionRing L) 0 = 𝟙 (𝟙_ X.Modules) := by
    rw [← map_one (Stacks.AlgebraicGeometry.GradedSectionRingMap.degreeZeroHom L),
      Stacks.AlgebraicGeometry.GradedSectionRingMap.degreeZeroHom_apply, DirectSum.of_eq_same]
    exact (Stacks.SectionRingGeometric.unitScalarEquiv X).symm_apply_eq.mpr
      (Stacks.SectionRingGeometric.unitScalar_id X).symm
  have hvalue : ∀ (x : SymmetricAlgebra k V) (hx : x ∈ grading k V (0 * 1)),
      (veroneseOfLinearMap k V L ψ).toFun 0 ⟨x, hx⟩
        = Stacks.SectionProduct.globalSection X (natTensorPow L 0)
          ((psiAlg k V L ψ x) 0) := fun _ _ => rfl
  have hpow : (veroneseOfLinearMap k V L ψ).pow f.2 0
      = Stacks.SectionProduct.globalSection X (natTensorPow L 0) (𝟙 (𝟙_ X.Modules)) := by
    rw [show (veroneseOfLinearMap k V L ψ).pow f.2 0
        = (veroneseOfLinearMap k V L ψ).toFun 0
            ⟨(f : SymmetricAlgebra k V) ^ 0,
              Stacks.MorphismToProj.HomogeneousRatios.pow_mem f.2 0⟩ from rfl,
      hvalue, pow_zero, map_one, hone]
  have htoFun : (veroneseOfLinearMap k V L ψ).toFun 0 ⟨_, h0'⟩
      = Stacks.SectionProduct.globalSection X (natTensorPow L 0)
        ((Stacks.SectionRingGeometric.unitScalarEquiv X).symm (baseRingHom k X r)) := by
    rw [hvalue, hcoe, psiAlg_algebraMap, DirectSum.of_eq_same]
  have hunit : Stacks.SectionProduct.globalSection X (natTensorPow L 0)
        ((Stacks.SectionRingGeometric.unitScalarEquiv X).symm (baseRingHom k X r))
      = baseRingHom k X r • Stacks.SectionProduct.globalSection X (natTensorPow L 0)
        (𝟙 (𝟙_ X.Modules)) := by
    have h := Stacks.SectionRingGeometric.globalSection_unitComp X
      (F := natTensorPow L 0)
      ((Stacks.SectionRingGeometric.unitScalarEquiv X).symm (baseRingHom k X r))
      (𝟙 (𝟙_ X.Modules))
    rwa [Category.comp_id, show Stacks.SectionRingGeometric.unitScalar X
        ((Stacks.SectionRingGeometric.unitScalarEquiv X).symm (baseRingHom k X r))
        = baseRingHom k X r from
      (Stacks.SectionRingGeometric.unitScalarEquiv X).apply_symm_apply _] at h
  rw [hmk, ((veroneseOfLinearMap k V L ψ).homogeneousRatios f.2 le_rfl).lift_mk
    Nat.one_pos 0 _ h0 ⟨_, h0'⟩ rfl]
  change (veroneseOfLinearMap k V L ψ).ratio f.2 le_rfl 0
      ((veroneseOfLinearMap k V L ψ).toFun 0 ⟨_, h0'⟩) = _
  refine (veroneseOfLinearMap k V L ψ).ratio_eq_of_resTop_eq f.2 le_rfl ?_
  rw [htoFun, hunit, hpow, resTop_smul]

/-- **Stacks Project, Tag 0FCY, clause (5): `φ_{ℒ,ψ}` is a morphism over `Spec k`.** The morphism
attached to a `k`-linear map `ψ : V → Γ(X, ℒ)` whose image generates `ℒ`, followed by the
structure morphism of `𝐏(V)`, is the structure morphism of `X`. The statement does not mention a
basis of `V`.

Two morphisms into an affine scheme agree as soon as the two ring maps `k ⟶ Γ(X, 𝒪_X)` do
(`AlgebraicGeometry.ext_to_Spec`), and that is checked on the cover of `X` by the nonvanishing
opens of the degree-one sections of the graded map attached to `ψ`. On `X_{ψ(f)}` the structure
morphism of `𝐏(V)` is the inclusion of the degree-zero part of `Sym_k V` into the chart ring
`(Sym_k V)_{(f)}` and `φ_{ℒ,ψ}` induces the dehomogenization of `ψ` there, so the composite
carries a scalar `r` to the ratio of `ψ(r)` by `ψ(f) ^ 0`. That ratio is the function `r` names
through the structure morphism of `X`, because `ψ(r)` is that function times `ψ(1)`. -/
theorem morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) :
    morphismOfGeneratingSections k V L ψ hψ ≫
        AlgebraicGeometry.projectiveSpaceOfModuleToSpec k V =
      X ↘ Spec (CommRingCat.of k) := by
  have hp : AlgebraicGeometry.projectiveSpaceOfModuleToSpec k V =
      AlgebraicGeometry.Proj.toSpecZero (grading k V) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k ↥(grading k V 0))) := rfl
  refine AlgebraicGeometry.ext_to_Spec (?_ :
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (morphismOfGeneratingSections k V L ψ hψ ≫
          AlgebraicGeometry.projectiveSpaceOfModuleToSpec k V).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appTop)
  rw [hp, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  simp only [Category.assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  have hle : ∀ f : grading k V 1,
      nvOpen (grading k V) (veroneseOfLinearMap k V L ψ) f ≤
        (morphismOfGeneratingSections k V L ψ hψ ≫
          AlgebraicGeometry.Proj.toSpecZero (grading k V)) ⁻¹ᵁ ⊤ := fun _ => le_top
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf
    (fun f : grading k V 1 => nvOpen (grading k V) (veroneseOfLinearMap k V L ψ) f) ⊤
    (fun _ => homOfLE le_top) (iSup_nvOpen_eq_top k V L ψ hψ).ge _ _ fun f => ?_
  exact (appLE_toSpecZero_morphismOfGeneratingSections ψ hψ f (hle f)
    (algebraMap k ↥(grading k V 0) r)).trans
    (lift_fromZeroRingHom_algebraMap ψ f r)

end OverBase

/-! ### Clause (6) of [Stacks, Tag 0FCY]: the coordinate square -/

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
/-- **Stacks Project, Tag 0FCY, clause (6): the coordinate square.** For a basis `v₀, …, vₙ` of
`V` the morphism `φ_{ℒ,ψ} : X ⟶ 𝐏(V)` of [Stacks, Tag 0FCY], followed by the coordinate
isomorphism `𝐏(V) ≅ ℙⁿ_k` of that basis, is the morphism `φ_{(ℒ,(s₀,…,sₙ))} : X ⟶ ℙⁿ_k` of
[Stacks, Tag 01ND] for the sections `sᵢ = ψ(vᵢ)`.

`ℙⁿ_k` is the fibre product of `Spec k` with the integral model `ℙⁿ_ℤ`, so the square is checked
on both projections. Over `Spec k` both sides are the structure morphism of `X`, by
`morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec` and
`Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst`; on the integral model both sides are
the glued morphism of [Stacks, Tag 01ND], by
`morphismOfGeneratingSections_comp_basisIso_toIntegralAtUniverse` and
`Stacks.ProjectiveFromSections.toProjectiveSpaceOver_snd`. -/
theorem morphismOfGeneratingSections_comp_basisProjectiveSpaceOfModuleIso (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) :
    morphismOfGeneratingSections k V L ψ hψ ≫
        (AlgebraicGeometry.basisProjectiveSpaceOfModuleIso b).hom.left =
      Stacks.ProjectiveFromSections.toProjectiveSpaceOver (basisSections b ψ)
        (generatesStalks_basisSections b ψ hψ) (X ↘ Spec (CommRingCat.of k)) := by
  have hfst : (AlgebraicGeometry.basisProjectiveSpaceOfModuleIso b).hom.left ≫
        CategoryTheory.Limits.pullback.fst
          (CategoryTheory.Limits.terminal.from (Spec (CommRingCat.of k)))
          (CategoryTheory.Limits.terminal.from
            (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n)) =
      AlgebraicGeometry.projectiveSpaceOfModuleToSpec k V :=
    CategoryTheory.Over.w (AlgebraicGeometry.basisProjectiveSpaceOfModuleIso b).hom
  refine CategoryTheory.Limits.pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun q : AlgebraicGeometry.projectiveSpaceOfModule k V ⟶
            Spec (CommRingCat.of k) =>
          morphismOfGeneratingSections k V L ψ hψ ≫ q) hfst).trans
        ((morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec ψ hψ).trans
          (Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst (basisSections b ψ)
            (generatesStalks_basisSections b ψ hψ) (X ↘ Spec (CommRingCat.of k))).symm))
  · exact (Category.assoc _ _ _).trans
      ((morphismOfGeneratingSections_comp_basisIso_toIntegralAtUniverse b ψ hψ).trans
        (Stacks.ProjectiveFromSections.toProjectiveSpaceOver_snd (basisSections b ψ)
          (generatesStalks_basisSections b ψ hψ) (X ↘ Spec (CommRingCat.of k))).symm)

end Generation

end Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare

end
