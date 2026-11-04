module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectTensorLocalModels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDerivedInternalHomCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Coherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTensorInstances
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# The cohomology of `E ⊗^L 𝒢` is coherent, for `E` perfect and `𝒢` a complex of coherent modules

Let `X` be an algebraic space, `E` a perfect object of `D(𝒪_X)` and `𝒢` a complex of coherent
`𝒪_X`-modules.  Then every cohomology sheaf of `E ⊗^L_{𝒪_X} 𝒢` is coherent.  This is the
coherence clause of the proof of Stacks 0DKJ: "locally `E` is isomorphic to a finite complex of
finite free `𝒪_X`-modules, hence locally `E ⊗^L 𝒢` is isomorphic to a finite complex whose terms
are finite direct sums of the `𝒢^i`; this immediately implies that the cohomology sheaves are
coherent."

## Main results

* `AlgebraicGeometry.Space.isCoherent_homology_derivedTensor_of_isPerfect`.

## The proof

Coherence is local on the small étale site (Stacks 03DN for coherence), and on the members `V` of
the covering family of `exists_coversTop_restrict_tensor_models` (in the namespace
`Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall`) the restriction of a cohomology
sheaf of `E ⊗^L 𝒢` is a cohomology sheaf of the total complex `Tot(P ⊗ 𝒢|_V)` with `P` strictly
perfect.  The terms of that complex are finite coproducts of the modules `P^p ⊗ 𝒢^q|_V`, each a
retract of a finite direct sum of copies of `𝒢^q|_V`, hence coherent; and the cohomology of a
complex of coherent modules is coherent (Stacks 01BY on a site). A coherent module on a site is
quasi-coherent, which gives the remaining clause of the definition of a coherent module on an
algebraic space (Stacks 07UA).

## References

* [Stacks Project, Tag 0DKJ](https://stacks.math.columbia.edu/tag/0DKJ)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] smallEtaleRingedSite_essentiallySmall
  Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

open Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall
  (restrictTensorComplex exists_coversTop_restrict_tensor_models)
open Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall (restriction restrictionComplex)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The cohomology of `E ⊗^L_{𝒪_X} 𝒢` is coherent** for `E` perfect and `𝒢` a complex of
coherent `𝒪_X`-modules. -/
theorem isCoherent_homology_derivedTensor_of_isPerfect
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS X.1 X.2))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E)
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hG : ∀ q : ℤ, IsCoherent B S hS X.1 X.2 (G.X q)) (i : ℤ) :
    IsCoherent B S hS X.1 X.2 ((DerivedCategory.homologyFunctor _ i).obj
      ((T.tensor.obj E).obj (DerivedCategory.Q.obj G))) := by
  let Xs := smallEtaleRingedSite B S hS X.1 X.2
  have hcoh : SheafOfModules.IsCoherentOnSite ((DerivedCategory.homologyFunctor _ i).obj
      ((T.tensor.obj E).obj (DerivedCategory.Q.obj G))) := by
    obtain ⟨K, V, hV, hmod⟩ := exists_coversTop_restrict_tensor_models Xs T E hE G
    refine (Stacks.SheafOfModules.isCoherentOnSite_iff_exists_cover_isCoherentOnSite Xs _).2
      ⟨K, V, hV, fun k => ?_⟩
    obtain ⟨P, hP, ⟨e⟩⟩ := hmod k
    obtain ⟨a, b, -, hPz⟩ : ∃ a b : ℤ, a ≤ b ∧ ∀ p : ℤ, p ∉ Set.Icc a b → IsZero (P.X p) := by
      classical
      have hs : {p : ℤ | ¬ IsZero (P.X p)}.Finite := hP.bounded
      obtain ⟨a, ha⟩ := hs.bddBelow
      obtain ⟨b, hb⟩ := hs.bddAbove
      refine ⟨min a b, max a b, min_le_max, fun p hp => ?_⟩
      by_contra hz
      have h1 := ha hz
      have h2 := hb hz
      simp only [Set.mem_Icc, not_and_or, not_le] at hp
      omega
    have hterm : ∀ n, SheafOfModules.IsCoherentOnSite
        ((restrictTensorComplex Xs (V k) P G).X n) := by
      intro n
      refine Stacks.TotalComplexTerms.prop_mapBifunctor_X
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} (Xs.O.over (V k)))
        P ((restrictionComplex Xs (V k)).obj G)
        (fun M => SheafOfModules.IsCoherentOnSite M) a b
        (fun p hp => hPz p (by simp only [Set.mem_Icc, not_and_or, not_le]; exact hp))
        n (fun p q _ => ?_)
      refine Stacks.SheafOfModules.prop_sheafTensor_of_isDirectSummandOfFiniteFree
        (Xs.O.over (V k)) (fun M => SheafOfModules.IsCoherentOnSite M)
        (fun i r hir hN => Stacks.SheafOfModules.isCoherentOnSite_of_comp_eq_id i r hir hN)
        (P.X p) _ (hP.termDirectSummand p) ?_
      exact Stacks.SheafOfModules.isCoherentOnSite_over (G.X q) (hG q).toIsCoherentOnSite (V k)
    have hH := Stacks.SheafOfModules.isCoherentOnSite_homology
      (restrictTensorComplex Xs (V k) P G) hterm i
    refine Stacks.SheafOfModules.isCoherentOnSite_of_iso ?_ hH
    have : PreservesFiniteLimits (restriction Xs (V k)) :=
      Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits (V k)
    have : PreservesFiniteColimits (restriction Xs (V k)) :=
      Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits (V k)
    exact ((DerivedCategory.homologyFunctorFactors _ i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso e.symm ≪≫
      (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (restriction Xs (V k)) i).app _
  exact { toIsCoherentOnSite := hcoh }

end AlgebraicGeometry.Space

end
