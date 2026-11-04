module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSliceConservativity
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.BoundedAboveGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.CoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IntervalDescent
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherent objects on a quasi-compact algebraic space are bounded above

Let `S` be a scheme, `F` an algebraic space over `S` and `E` an object of `D(𝒪_F)`. If `F` is
quasi-compact and `E` is `m`-pseudo-coherent, then `Hⁱ(E) = 0` for `i ≫ 0`. Over a Noetherian
algebraic space this gives the implication (2) ⇒ (1) of [Stacks, Tag 08IK], and that a
pseudo-coherent object of `D(𝒪_F)` lies in `D⁻_Coh(𝒪_F)`.

## Main results

* `Space.exists_isZero_homology_gt_of_isPseudoCoherentFrom`: an `m`-pseudo-coherent object of
  `D(𝒪_F)` over a quasi-compact algebraic space has `Hⁱ(E) = 0` for `i ≫ 0`.
* `Space.isCoherentOnSite_homology_and_isBoundedAbove_of_isPseudoCoherentFrom_of_isNoetherian`:
  over a Noetherian algebraic space, an `m`-pseudo-coherent object `E` of `D_QCoh(𝒪_F)` has
  `Hⁱ(E)` coherent for `i ≥ m` and `Hⁱ(E) = 0` for `i ≫ 0`.
* `Space.isCoherentOnSite_homology_and_isBoundedAbove_of_isPseudoCoherent_of_isNoetherian`:
  a pseudo-coherent object of `D(𝒪_F)` over a Noetherian algebraic space lies in `D⁻_Coh(𝒪_F)`.

## References

* [Stacks Project, Tag 08IK](https://stacks.math.columbia.edu/tag/08IK)
* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

attribute [local instance high] modules_over_abelian

/-- **The cohomology of an `m`-pseudo-coherent object of `D(𝒪_F)` over a quasi-compact algebraic
space vanishes in all sufficiently large degrees.** -/
theorem exists_isZero_homology_gt_of_isPseudoCoherentFrom
    (hqc : IsQuasiCompactSpace B S hS F)
    (E : DerivedCategory (Modules.{u, u} B S hS F hF)) (m : ℤ)
    (hE : (smallEtaleRingedSite B S hS F hF).IsPseudoCoherentFrom E m) :
    ∃ b : ℤ, ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) j).obj E) := by
  classical
  set Y := smallEtaleRingedSite B S hS F hF with hY
  obtain ⟨U, a, hUaff, hasurj, haet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS F hF).mp hqc
  have hid : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (𝟙 U)) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@Etale.{u} : MorphismProperty Scheme.{u}) (𝟙 U)).2
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  have haet' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a := by
    have h := haet U (yoneda.map (𝟙 U)) hid
    rwa [CategoryTheory.Functor.map_id, Category.id_comp] at h
  let Uc : SmallEtale B S hS F := ⟨CostructuredArrow.mk a, haet'⟩
  have hUcsurj : IsSurjective B S hS Uc.obj.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS F hF U a).1 hasurj
  have hcovU : Y.J.CoversTop (fun _ : PUnit.{u + 2} => Uc) :=
    SmallEtale.coversTop_of_isSurjective B S hS F hF Uc hUcsurj
  have hUcaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Uc)) := hUaff
  obtain ⟨Sv, hSv, hdata⟩ :=
    AlgebraicGeometry.RingedSite.exists_local_isZero_homology_gt_general Y E m hE Uc
  obtain ⟨n, z, φ, -, hmem, hzcov, -⟩ :=
    SmallEtale.exists_finite_affine_etale_ofArrows_le B S hS F hUcaff hSv
  have hcovZ : Y.J.CoversTop z := by
    intro X
    refine Y.J.transitive (hcovU X) _ fun Z h hh => ?_
    obtain ⟨-, ⟨p⟩⟩ := (Sieve.mem_ofObjects_iff _ h).1 hh
    refine Y.J.superset_covering ?_ (Y.J.pullback_stable p hzcov)
    exact fun W q hq => Sieve.ofArrows_le_ofObjects z φ _ hq
  have hbound : ∀ k : Fin n, ∃ b : ℤ, ∀ j : ℤ, b < j →
      IsZero (((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS F hF) j).obj E).over (z k)) := by
    intro k
    obtain ⟨W, g, f, hf, -⟩ := hmem k
    obtain ⟨b, hb⟩ := hdata f hf
    exact ⟨b, fun j hj => Stacks.SheafOfModules.isZero_over_of_hom _ g (hb j hj)⟩
  choose b hb using hbound
  obtain ⟨N, hN⟩ := Finite.exists_le b
  exact ⟨N, fun j hj => Stacks.SheafOfModules.isZero_of_coversTop hcovZ _
    fun k => hb k j (lt_of_le_of_lt (hN k) hj)⟩

/-- Let `S` be a scheme, let `F` be a Noetherian algebraic space over `S` and let `E` be an
object of `D_QCoh(𝒪_F)`.  If `E` is `m`-pseudo-coherent then `Hⁱ(E)` is coherent for every
`i ≥ m` and `Hⁱ(E)` vanishes for `i ≫ 0`. -/
@[stacks 08IK "(2) gives (1)"]
theorem isCoherentOnSite_homology_and_isBoundedAbove_of_isPseudoCoherentFrom_of_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) (hFN : IsNoetherian B S hS hZ F)
    (E : DerivedCategory (Modules.{u, u} B S hS F hF)) (m : ℤ)
    (hE : (smallEtaleRingedSite B S hS F hF).IsPseudoCoherentFrom E m)
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS F hF) i).obj E).IsQuasicoherentOnSite) :
    (∀ i : ℤ, m ≤ i → SheafOfModules.IsCoherentOnSite
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj E)) ∧
      DerivedCategoryB.IsBoundedAbove E :=
  ⟨fun i hi =>
      isCoherentOnSite_homology_of_isPseudoCoherentFrom B S hS F hF hFN.2.2 E m i hE hi (hqc i),
    exists_isZero_homology_gt_of_isPseudoCoherentFrom B S hS F hF hFN.1 E m hE⟩

/-- Let `S` be a scheme, let `F` be a Noetherian algebraic space over `S` and let `E` be a
pseudo-coherent object of `D(𝒪_F)`.  Then `E` is an object of `D⁻_Coh(𝒪_F)`: its cohomology
vanishes in all sufficiently large degrees and is coherent in every degree. -/
@[stacks 08IK "pseudo-coherent gives D⁻_Coh"]
theorem isCoherentOnSite_homology_and_isBoundedAbove_of_isPseudoCoherent_of_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) (hFN : IsNoetherian B S hS hZ F)
    (E : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hE : (smallEtaleRingedSite B S hS F hF).IsPseudoCoherent E) :
    DerivedCategoryB.IsBoundedAbove E ∧
      ∀ i : ℤ, SheafOfModules.IsCoherentOnSite
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj E) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  refine ⟨exists_isZero_homology_gt_of_isPseudoCoherentFrom B S hS F hF hFN.1 E 0
      ⟨K, hK 0, ⟨e⟩⟩, fun i => ?_⟩
  exact (isCoherentOnSite_homology_and_isBoundedAbove_of_isPseudoCoherentFrom_of_isNoetherian
    B S hS F hF hZ hFN E i ⟨K, hK i, ⟨e⟩⟩
    (derivedCategoryB_of_isPseudoCoherent_unconditional B S hS F hF E ⟨K, hK, ⟨e⟩⟩)).1 i le_rfl

end AlgebraicGeometry.Space

end
