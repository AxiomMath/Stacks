module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangePseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqs

/-!
# Pseudo-coherence of `Rf_*E` for `E` supported on a closed subset, by approximation

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces with `Y`
affine, let `T ⊆ |X|` be a closed subset whose open complement has quasi-compact inclusion, and
let `E` be a pseudo-coherent object of `D(𝒪_X)` supported on `T`. If `Rf_*P` is pseudo-coherent
for every perfect `P` supported on `T`, then `Rf_*E` is pseudo-coherent.

The proof is the approximation argument of the pseudo-coherence part of Stacks 0CTL: by
Stacks 08HP the pair `(X, T)` has approximation by perfect complexes, so `E` receives, for every
`m`, a map from a perfect `P` supported on `T` whose cone lies in `D^{≤ m - N - 1}`, `N` being
the bound of Stacks 08FA on the cohomological amplitude of `Rf_*` on `D_QCoh`; then `Rf_*P ⟶ Rf_*E`
approximates `Rf_*E` from `m`, so `Rf_*E` is `m`-pseudo-coherent.

This is the reduction, in the generalization of Grothendieck's existence theorem proposed in
Stacks 0DIR, of the pseudo-coherence of `RΓ(Xₙ, Eₙ ⊗^L Kₙ)` to the case of a perfect object with
proper support.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherentFrom_derivedModulePushforward_of_cohomologySupportedOn`
* `AlgebraicGeometry.Space.isPseudoCoherent_derivedModulePushforward_of_cohomologySupportedOn`

## References

* [Stacks Project, Tag 08HP](https://stacks.math.columbia.edu/tag/08HP)
* [Stacks Project, Tag 08FA](https://stacks.math.columbia.edu/tag/08FA)
* [Stacks Project, Tag 0CTL](https://stacks.math.columbia.edu/tag/0CTL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **`Rf_*E` is `m`-pseudo-coherent for `E` pseudo-coherent supported on `T`**, over an affine
base, as soon as `Rf_*P` is pseudo-coherent for every perfect `P` supported on `T`; the open
complement of `T` is assumed to have quasi-compact inclusion, as approximation by perfect
complexes (Stacks 08HP) requires. -/
theorem isPseudoCoherentFrom_derivedModulePushforward_of_cohomologySupportedOn
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsAffineSpace B S hS Y.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E)
    (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι)
    (hET : CohomologySupportedOn B S hS X.1 X.2 T E)
    (hperf : ∀ P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P → CohomologySupportedOn B S hS X.1 X.2 T P →
      (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent
        ((derivedModulePushforward B S hS f).obj P))
    (m : ℤ) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherentFrom
      ((derivedModulePushforward B S hS f).obj E) m := by
  have hXqc : IsQuasiCompactSpace B S hS X.1 :=
    isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f hfqc hY
  have hXqs := isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS
    B.contains_terminal f hfqs hY
  obtain ⟨N, hN⟩ := exists_isZero_homology_derivedModulePushforward B S hS f hfqc hfqs
    hY.isQuasiCompactSpace
  obtain ⟨r, hr⟩ := approximationByPerfectComplexes_of_qcqs B S hS B.contains_terminal X.1 X.2
    hXqc hXqs T hT hTqc
  have hEq : QcohDerived B S hS X E :=
    derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X.1 X.2 E hE
  obtain ⟨K₀, hK₀, ⟨eK₀⟩⟩ := hE
  obtain ⟨P, hP, hPT, α, hα₁, hα₂⟩ :=
    hr ⟨E, hEq⟩ (m - N) ⟨K₀, hK₀ _, ⟨eK₀⟩⟩ fun i _ => hET i
  obtain ⟨C, g, h, hT'⟩ := distinguished_cocone_triangle α
  have hCle : C.IsLE (m - N - 1) :=
    DerivedCategory.ApproximatesFrom.isLE_obj₃ (Triangle.mk α g h) hT' ⟨hα₁, hα₂⟩
  have hCq : QcohDerived B S hS X C := (QcohDerived B S hS X).ext_of_isTriangulatedClosed₃ _ hT'
    (qcohDerived_of_isPerfect_derivedCategoryB X P hP) hEq
  have hRC : ((derivedModulePushforward B S hS f).obj C).IsLE (m - 1) := by
    have := isLE_derivedModulePushforward_of_isLE f N hN C hCq _ hCle
    exact DerivedCategory.TStructure.t.isLE_of_le _ (m - N - 1 + N - 1) _ (by omega)
  have happ : DerivedCategory.ApproximatesFrom ((derivedModulePushforward B S hS f).map α) m :=
    DerivedCategory.approximatesFrom_of_isLE _
      ((derivedModulePushforward B S hS f).map_distinguished _ hT') m hRC
  exact isPseudoCoherentFrom_of_approximatesFrom _ m happ
    ((RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).1 (hperf P hP hPT) m)

/-- **`Rf_*E` is pseudo-coherent for `E` pseudo-coherent supported on `T`**, over an affine base,
as soon as `Rf_*P` is pseudo-coherent for every perfect `P` supported on `T`, the open complement
of `T` having quasi-compact inclusion. -/
theorem isPseudoCoherent_derivedModulePushforward_of_cohomologySupportedOn
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsAffineSpace B S hS Y.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E)
    (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι)
    (hET : CohomologySupportedOn B S hS X.1 X.2 T E)
    (hperf : ∀ P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P → CohomologySupportedOn B S hS X.1 X.2 T P →
      (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent
        ((derivedModulePushforward B S hS f).obj P)) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent
      ((derivedModulePushforward B S hS f).obj E) :=
  (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).2
    (isPseudoCoherentFrom_derivedModulePushforward_of_cohomologySupportedOn f hfqc hfqs hY E hE
      T hT hTqc hET hperf)

end AlgebraicGeometry.Space

end
