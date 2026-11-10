module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorSingleObject
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToTransport
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CohomologySpectralSequenceTagSheaf
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The spectral sequence of a simplicial site which computes the cohomology of a base

Let `S` be a simplicial-site situation (Stacks 09WE), with total site `C_total` and component
sites `C_p`. For an abelian sheaf `F` on `C_total` the spectral sequence of Stacks 09WJ has first
page `E_1^{p,q} = H^q(C_p, F_p)` and abuts to `H^{p+q}(C_total, F)`.

Suppose now given an abelian category `𝒜`, an additive functor `Γ : 𝒜 ⥤ Ab` (global sections on
a base site, say) and an exact functor `G : 𝒜 ⥤ Ab(C_total)` (the inverse image along an
augmentation `a`, say) such that the canonical comparison `RΓ ⟶ RΓ(C_total, -) ∘ RG` of bounded
below derived functors is an isomorphism. This is the situation of a cohomological descent
statement such as Stacks 0DH8 (`RΓ(X, K) = RΓ(U_total, a⁻¹K)`). Then for every object `F` of
`𝒜` the spectral sequence of Stacks 09WJ of `G(F)` has first page `E_1^{p,q} = H^q(C_p, G(F)_p)`
and abuts to `R^{p+q}Γ(F)`. This is the deduction of Stacks 0DHA from Stacks 0DH8 and 09WJ.

## Main results

* `CategoryTheory.SimplicialSiteSituation.isZero_cohomologySpectralSequence_pageOne`: the first
  page of the spectral sequence of Stacks 09WJ vanishes outside the first quadrant.
* `CategoryTheory.SimplicialSiteSituation.cohomologySpectralSequence_abutsTo_of_iso`: the
  spectral sequence of Stacks 09WJ abuts to any family isomorphic to the cohomology of the
  total site, extended by zero to the negative degrees.
* `CategoryTheory.SimplicialSiteSituation.rightDerivedIsoOfDerivedIso`: if the comparison
  `RΓ ⟶ RΓ(C_total, -) ∘ RG` is invertible at `F[0]`, then
  `H^n(C_total, G(F)) ≅ R^nΓ(F)`.
* `CategoryTheory.SimplicialSiteSituation.cohomologySpectralSequence_abutsTo_of_derivedIso`:
  under that hypothesis the spectral sequence of `G(F)` abuts to `R^{p+q}Γ(F)`.

## Implementation notes

The derived categories are arbitrary models (`HasDerivedCategory`), so the statements apply to
whichever model a cohomological descent statement is formulated in. The bounded below derived
functors only enter through the comparison hypothesis; the spectral sequence itself and its
first page are those of `CategoryTheory.SimplicialSiteSituation.cohomologySpectralSequence`,
which is built from injective resolutions.

Exactness of `G` is what identifies `RG(F[0])` with `G(F)[0]`
(`CategoryTheory.Functor.rightDerivedFunctorPlusObjSingleIso`); for an augmentation of topoi the
inverse image is exact.

## References

* [Stacks Project, Tag 09WJ](https://stacks.math.columbia.edu/tag/09WJ)
* [Stacks Project, Tag 0DH8](https://stacks.math.columbia.edu/tag/0DH8)
* [Stacks Project, Tag 0DHA](https://stacks.math.columbia.edu/tag/0DHA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-- **The first page of the spectral sequence of Stacks 09WJ vanishes outside the first
quadrant**: the double complex `A^{q,p} = Γ(C_p, I^q_p)` vanishes in negative simplicial degree
`p`, and in negative degree `q` because the injective resolution does. -/
theorem isZero_cohomologySpectralSequence_pageOne (F : Sheaf S.totalTopology Ab.{u}) (p q : ℤ)
    (h : p < 0 ∨ q < 0) :
    IsZero (((S.cohomologySpectralSequence.obj F).page 1 le_rfl).X (p, q)) := by
  refine (S.pageOneIsoColumnHomology (S.injectiveResolutionZ F) p q).isZero_iff.2 ?_
  refine ((Functor.mapHomologicalComplexHomologyIso
    (HomologicalComplex.eval Ab.{u} (ComplexShape.up ℤ) p) (ComplexShape.up ℤ) q).app
      (S.sectionsDoubleComplex (S.injectiveResolutionZ F))).isZero_iff.1 ?_
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ q).1
    (ShortComplex.exact_of_isZero_X₂ _ ?_)
  exact S.isZero_sectionsDoubleComplex_X_X (S.injectiveResolutionZ F)
    (S.isZero_injectiveResolutionZ_X F) q p h.symm

/-- **The spectral sequence of Stacks 09WJ abuts to any family isomorphic to the cohomology of
the total site**: given isomorphisms `H^n(C_total, F) ≅ H n` for `n : ℕ`, the spectral sequence
of `F` abuts to `H`, extended by zero to the negative degrees. -/
theorem cohomologySpectralSequence_abutsTo_of_iso (F : Sheaf S.totalTopology Ab.{u})
    (H : ℕ → Ab.{u})
    (e : ∀ n : ℕ, ((Sheaf.Γ S.totalTopology Ab.{u}).rightDerived n).obj F ≅ H n) :
    SpectralSequence.AbutsTo (S.cohomologySpectralSequence.obj F)
      (fun n => if 0 ≤ n then H n.toNat else AddCommGrpCat.of PUnit) := by
  refine (S.cohomologySpectralSequence_abutsTo F).of_iso fun n => ?_
  by_cases hn : 0 ≤ n
  · rw [ite_eq_left hn]
    exact eqToIso (by rw [Int.toNat_of_nonneg hn]) ≪≫
      S.totalCohomologyZ_iso_rightDerived F n.toNat ≪≫ e n.toNat
  · rw [ite_eq_right hn]
    exact (S.isZero_totalCohomologyZ_of_neg F n (by omega)).iso
      (AddCommGrpCat.isZero_of_subsingleton _)

section Descent

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
  [HasDerivedCategory 𝒜] [HasDerivedCategory (Sheaf S.totalTopology Ab.{u})]
  [HasDerivedCategory Ab.{u}]
  (Γ : 𝒜 ⥤ Ab.{u}) [Γ.Additive]
  (G : 𝒜 ⥤ Sheaf S.totalTopology Ab.{u}) [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (φ : Γ.rightDerivedFunctorPlus ⟶
    G.rightDerivedFunctorPlus ⋙ (Sheaf.Γ S.totalTopology Ab.{u}).rightDerivedFunctorPlus)

/-- **Cohomological descent identifies the cohomology of the total site with that of the
base.** If the comparison `φ : RΓ ⟶ RΓ(C_total, -) ∘ RG` is invertible at `F[0]` and `G` is
exact, then `H^n(C_total, G(F)) ≅ R^nΓ(F)`: both sides are the `n`-th cohomology of the two ends
of `φ` at `F[0]`, using `RG(F[0]) ≅ G(F)[0]`. -/
def rightDerivedIsoOfDerivedIso (F : 𝒜)
    [IsIso (φ.app ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj F))] (n : ℕ) :
    ((Sheaf.Γ S.totalTopology Ab.{u}).rightDerived n).obj (G.obj F) ≅
      (Γ.rightDerived n).obj F :=
  (Stacks.DerivedIndexing.rightDerivedIso (Sheaf.Γ S.totalTopology Ab.{u}) n).app (G.obj F) ≪≫
    (DerivedCategory.Plus.homologyFunctor Ab.{u} (n : ℤ)).mapIso
      ((Sheaf.Γ S.totalTopology Ab.{u}).rightDerivedFunctorPlus.mapIso
          (G.rightDerivedFunctorPlusObjSingleIso F).symm ≪≫
        (asIso (φ.app ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj F))).symm) ≪≫
    ((Stacks.DerivedIndexing.rightDerivedIso Γ n).app F).symm

/-- **The spectral sequence of a cohomological descent situation.** If the comparison
`φ : RΓ ⟶ RΓ(C_total, -) ∘ RG` is invertible at `F[0]` and `G` is exact, the spectral sequence
of Stacks 09WJ of `G(F)`, whose first page is `E_1^{p,q} = H^q(C_p, G(F)_p)`
(`CategoryTheory.SimplicialSiteSituation.cohomologySpectralSequence_pageOneIso`), abuts to
`R^{p+q}Γ(F)`. -/
theorem cohomologySpectralSequence_abutsTo_of_derivedIso (F : 𝒜)
    [IsIso (φ.app ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj F))] :
    SpectralSequence.AbutsTo (S.cohomologySpectralSequence.obj (G.obj F))
      (fun n => if 0 ≤ n then (Γ.rightDerived n.toNat).obj F else AddCommGrpCat.of PUnit) :=
  S.cohomologySpectralSequence_abutsTo_of_iso (G.obj F) (fun n => (Γ.rightDerived n).obj F)
    (S.rightDerivedIsoOfDerivedIso Γ G φ F)

end Descent

end CategoryTheory.SimplicialSiteSituation

end
