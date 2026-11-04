module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSmoothModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleCohomologyIntComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointsVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Removing a finite boundary does not change `H²`

Let `j : U ⟶ V` be an open immersion whose closed complement `Z` (with its reduced structure) is
an affine scheme all of whose points are closed with separably closed residue fields — for
instance a finite set of closed points of a curve over an algebraically closed field.  For a
sheaf `N` of `Λ`-modules on `V_étale`, the counit `j_! j^{-1} N ⟶ N` induces an isomorphism

`H²(V, j_! j^{-1} N) ≅ H²(V, N)`.

Indeed `0 → j_! j^{-1} N → N → i_* i^{-1} N → 0` is exact (Tag 095L), and the third term has no
cohomology in positive degree: `H^q(V, i_* G) = H^q(Z, G)` for the closed immersion `i`, and on
`Z` the cohomology of the underlying abelian sheaf vanishes in positive degree (Tag 09AY).  The
long exact sequence then makes the map bijective in degree two.

## Main results

* `Stacks.EtaleCohomology.isZero_rightDerivedPlus_directImage_of_finitePoints`.
* `Stacks.EtaleCohomology.isIso_rightDerivedPlus_two_extensionByZero_counit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ]

/-- **Positive-degree cohomology of a direct image from a scheme of closed points vanishes**: for
a closed immersion `i : Z ⟶ V` from an affine scheme all of whose points are closed with
separably closed residue fields, `H^q(V, i_* G) = 0` for `q > 0`. -/
@[sga "4½ Arcata 6.2.1" "more general"]
theorem isZero_rightDerivedPlus_directImage_of_finitePoints {Z V : Scheme.{u}} (i : Z ⟶ V)
    [IsClosedImmersion i] [IsAffine Z] (hclosed : ∀ z : Z, IsClosed ({z} : Set Z))
    (hsep : ∀ z : Z, IsSepClosed ↥(Z.residueField z)) (G : EtaleModules.{u, 0} Λ Z) (q : ℕ)
    (hq : 0 < q) :
    IsZero (((etaleModuleGlobalSections.{u, 0} Λ V).rightDerivedPlus (q : ℤ)).obj
      ((etaleModuleDirectImage.{u, 0} Λ i).obj G)) :=
  IsZero.of_iso (isZero_rightDerivedPlus_of_subsingleton_sheafH Z G q
    (subsingleton_etaleCohomology_of_closed_points' Z hclosed hsep _ q hq))
    (integralDirectImageCohomologyIso Λ i G q)

/-- **`H²(V, j_! j^{-1} N) ≅ H²(V, N)`** through the counit, when the closed complement of the
open immersion `j` is a scheme of closed points with separably closed residue fields. -/
theorem isIso_rightDerivedPlus_two_extensionByZero_counit {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j]
    [IsAffine (Scheme.IdealSheafData.vanishingIdeal
      ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩).subscheme]
    (hclosed : ∀ z : (Scheme.IdealSheafData.vanishingIdeal
        ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩).subscheme,
          IsClosed ({z} : Set _))
    (hsep : ∀ z : (Scheme.IdealSheafData.vanishingIdeal
        ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩).subscheme,
          IsSepClosed ↥(Scheme.residueField _ z))
    (N : EtaleModules.{u, 0} Λ V) :
    IsIso (((etaleModuleGlobalSections.{u, 0} Λ V).rightDerivedPlus 2).map
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app N)) := by
  let ι := (Scheme.IdealSheafData.vanishingIdeal
      ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩).subschemeι
  obtain ⟨_, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage Λ ι j
    (by rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_mk,
        compl_compl]) N
  let D := Stacks.DerivedIndexing.rightDerivedPlusDeltaFunctor
    (etaleModuleGlobalSections.{u, 0} Λ V)
    (Stacks.DerivedIndexing.derivedDeltaFunctorStructure _)
    (Stacks.DerivedIndexing.canonicalδ _) (fun _ _ => rfl)
  have hZ := fun q hq => isZero_rightDerivedPlus_directImage_of_finitePoints Λ ι hclosed hsep
    ((etaleModuleInverseImage.{u, 0} Λ ι).obj N) q hq
  have : Mono (((etaleModuleGlobalSections.{u, 0} Λ V).rightDerivedPlus 2).map
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app N)) :=
    (D.exact_δ₂ hS 1).mono_g ((hZ 1 one_pos).eq_of_src _ _)
  have : Epi (((etaleModuleGlobalSections.{u, 0} Λ V).rightDerivedPlus 2).map
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app N)) :=
    (D.exact_map hS 2).epi_f ((hZ 2 two_pos).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end Stacks.EtaleCohomology

end
