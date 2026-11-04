module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionDualizing.Locality
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportQuasicoherent
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.DerivedCoextensionIsDualizing
public import StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness

/-!
# `R ℰom(𝒪_Z, -)` of a dualizing complex is dualizing, at the standard model

Let `i : Z ⟶ W` be a closed immersion of locally Noetherian schemes and `K` a dualizing complex on
`W` ([Stacks, Tag 0A87]). This file proves that `R ℰom(𝒪_Z, K)` is a dualizing complex on `Z`,
at `CategoryTheory.HasDerivedCategory.standard`.

The route is the source's. Cover `Z` by the affine opens `i⁻¹V`, `V ⊆ W` affine. Over such a `V`
the complex `K` is modelled by a dualizing complex `ω` over `A = Γ(W, V)`; the chart ring map
`A ⟶ B = Γ(Z, i⁻¹V)` is surjective, so finite. Then

* `R ℰom(𝒪_Z, K)|_{i⁻¹V} ≅ R ℰom(𝒪_{i⁻¹V}, K|_V)` by locality
  (`Stacks.Duality.ClosedImmersionDualizing.restrictRhomOpensIso`),
* which, transported to `Spec B ⟶ Spec A`, is the sheaf associated to `RHom_A(B, ω)` by part (2)
  of [Stacks, Tag 0A78]
  (`AlgebraicGeometry.isIso_affineDerivedSheafHomComparison_app_of_noetherian`),
* and `RHom_A(B, ω)` is a dualizing complex over `B` by [Stacks, Tag 0AX0]
  (`Dualizing.isDualizingComplex_derivedHom_of_finite`).

[Stacks, Tag 0A86] (`Stacks.Duality.isDualizingComplex_of_hasDualizingModelOn_cover`) glues.

## Main results

* `Stacks.Duality.ClosedImmersionDualizing.hasDualizingModelOn_rhom` — the chart computation.
* `Stacks.Duality.ClosedImmersionDualizing.isDualizingComplex_rhom` — the theorem at the standard
  model.

## References

* [Stacks Project, Tag 0A78](https://stacks.math.columbia.edu/tag/0A78)
* [Stacks Project, Tag 0AX0](https://stacks.math.columbia.edu/tag/0AX0)
* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Duality.ClosedImmersionDualizing

variable {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]

/-- The ring map `Γ(W, V) ⟶ Γ(Z, i⁻¹V)` along which the chart `i⁻¹V ⟶ V` of a closed immersion is
read. -/
abbrev chartRingHom (V : W.Opens) : Γ(W, V) ⟶ Γ(Z, i ⁻¹ᵁ V) := i.app V

/-- The chart `Spec Γ(Z, i⁻¹V) ⟶ Spec Γ(W, V)` of a closed immersion over an affine open is a
closed immersion: the chart ring map is surjective. -/
theorem isClosedImmersion_specMap_chartRingHom {V : W.Opens} (hV : IsAffineOpen V) :
    IsClosedImmersion (Spec.map (chartRingHom i V)) :=
  IsClosedImmersion.spec_of_surjective _ (i.app_surjective V hV)

/-- The chart square: `i⁻¹V ≅ Spec Γ(Z, i⁻¹V)` and `V ≅ Spec Γ(W, V)` carry `i|_V` to
`Spec` of the chart ring map. -/
theorem isoSpec_hom_specMap_chartRingHom {V : W.Opens} (hV : IsAffineOpen V) :
    (hV.preimage i).isoSpec.hom ≫ Spec.map (chartRingHom i V) =
      (i ∣_ V) ≫ hV.isoSpec.hom := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec i hV (hV.preimage i) le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at h
  refine (cancel_mono (hV.isoSpec.inv ≫ V.ι)).1 ?_
  rw [IsAffineOpen.isoSpec_inv_ι, Category.assoc, h, ← IsAffineOpen.isoSpec_inv_ι,
    ← IsAffineOpen.isoSpec_inv_ι, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id_assoc, morphismRestrict_ι]

section ChartIso

variable {V : W.Opens} (hV : IsAffineOpen V)
  (K : DerivedCategory W.Modules) (ω : DerivedCategory (ModuleCat.{u} Γ(W, V)))

/-- The first half of the chart computation: locality of `R ℰom(𝒪_Z, -)` along `V`, the model of
`K` on `V`, and the factorization of the model through `Spec Γ(W, V)`. -/
def chartIso₁
    (e : (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(W, V) ⋙
        Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj ω) :
    (Scheme.Modules.restrictFunctor (i ⁻¹ᵁ V).ι).mapDerivedCategory.obj ((rhom i).obj K) ≅
      (rhom (i ∣_ V)).obj ((Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj
        ((tilde.functor Γ(W, V)).mapDerivedCategory.obj ω)) :=
  restrictRhomOpensIso V K ≪≫
    (rhom (i ∣_ V)).mapIso e ≪≫
    (rhom (i ∣_ V)).mapIso ((Functor.mapDerivedCategoryCompIso (Iso.refl _)).app ω).symm

/-- The second half of the chart computation: transport along `i⁻¹V ≅ Spec Γ(Z, i⁻¹V)` and
part (2) of [Stacks, Tag 0A78] on `Spec Γ(W, V)`. -/
def chartIso₂ [IsClosedImmersion (Spec.map (chartRingHom i V))]
    [IsIso ((affineDerivedSheafHomComparison Γ(W, V) Γ(Z, i ⁻¹ᵁ V) (chartRingHom i V)).app ω)] :
    (rhom (i ∣_ V)).obj ((Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj
        ((tilde.functor Γ(W, V)).mapDerivedCategory.obj ω)) ≅
      (tilde.functor Γ(Z, i ⁻¹ᵁ V) ⋙
        Scheme.Modules.restrictFunctor (hV.preimage i).isoSpec.hom).mapDerivedCategory.obj
          ((Dualizing.derivedHom.{u, u, u} (chartRingHom i V).hom).obj ω) :=
  (restrictRhomIsoIso (hV.preimage i).isoSpec hV.isoSpec
      (isoSpec_hom_specMap_chartRingHom i hV) _).symm ≪≫
    (Scheme.Modules.restrictFunctor (hV.preimage i).isoSpec.hom).mapDerivedCategory.mapIso
      (asIso ((affineDerivedSheafHomComparison Γ(W, V) Γ(Z, i ⁻¹ᵁ V) (chartRingHom i V)).app
        ω)).symm ≪≫
    (Functor.mapDerivedCategoryCompIso (Iso.refl _)).app _

end ChartIso

/-- **`R ℰom(𝒪_Z, -)` has a dualizing model on the chart over an affine open, at the standard
model.** If `K` carries the dualizing model `ω` on the affine open `V ⊆ W`, then
`R ℰom(𝒪_Z, K)` carries the dualizing model `RHom_{Γ(W, V)}(Γ(Z, i⁻¹V), ω)` on `i⁻¹V`: this is the
locality of `R ℰom(𝒪_Z, -)`, part (2) of [Stacks, Tag 0A78] on the chart, and [Stacks, Tag 0AX0]
for the finite (indeed surjective) chart ring map. -/
theorem hasDualizingModelOn_rhom [IsLocallyNoetherian W] [IsLocallyNoetherian Z]
    (K : DerivedCategory W.Modules) (V : W.Opens) (hV : IsAffineOpen V)
    (hK : HasDualizingModelOn K V hV) :
    HasDualizingModelOn ((rhom i).obj K) (i ⁻¹ᵁ V) (hV.preimage i) := by
  have hA : IsNoetherianRing Γ(W, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hB : IsNoetherianRing Γ(Z, i ⁻¹ᵁ V) :=
    IsLocallyNoetherian.component_noetherian ⟨i ⁻¹ᵁ V, hV.preimage i⟩
  obtain ⟨ω, hω, ⟨e⟩⟩ := hK
  have hsurj : Function.Surjective (chartRingHom i V) := i.app_surjective V hV
  have := isClosedImmersion_specMap_chartRingHom i hV
  have hfin : (chartRingHom i V).hom.Finite := RingHom.Finite.of_surjective _ hsurj
  have hbdd : DerivedCategoryB.IsBoundedBelow ω :=
    Dualizing.isBoundedBelow_of_bounded.{u, u} ω hω.bounded
  have := isIso_affineDerivedSheafHomComparison_app_of_noetherian Γ(W, V) Γ(Z, i ⁻¹ᵁ V)
    (chartRingHom i V) ω hbdd
  exact ⟨(Dualizing.derivedHom.{u, u, u} (chartRingHom i V).hom).obj ω,
    Dualizing.isDualizingComplex_derivedHom_of_finite.{u, u} _ hfin ω hω,
    ⟨chartIso₁ i hV K ω e ≪≫ chartIso₂ i hV ω⟩⟩

/-- **The standard-model form of the theorem.** For a closed immersion `i : Z ⟶ W` of locally
Noetherian schemes and a dualizing complex `K` on `W`, `R ℰom(𝒪_Z, K)` is a dualizing complex on
`Z`. The members `i⁻¹V` of the affine open cover of `Z` by preimages of affine opens of `W` carry
dualizing models by `hasDualizingModelOn_rhom`, and [Stacks, Tag 0A86] concludes. -/
theorem isDualizingComplex_rhom [IsLocallyNoetherian W] [IsLocallyNoetherian Z]
    (K : DerivedCategory W.Modules) (hK : IsDualizingComplex K) :
    IsDualizingComplex ((rhom i).obj K) :=
  isDualizingComplex_of_hasDualizingModelOn_cover (fun V : W.affineOpens => i ⁻¹ᵁ V.1)
    (fun V => V.2.preimage i)
    (by rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top])
    (fun V => hasDualizingModelOn_rhom i K V.1 V.2 (hK V.1 V.2))

end Stacks.Duality.ClosedImmersionDualizing
