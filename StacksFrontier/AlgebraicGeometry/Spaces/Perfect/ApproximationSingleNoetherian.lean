module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperExtFiniteComplexes
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage

/-!
# Approximating a module of finite type on a Noetherian algebraic space by a perfect complex

Let `X` be a Noetherian algebraic space and `𝓕` a quasi-coherent `𝒪_X`-module of finite type. For
every integer `m` there is a perfect object `P` of `D(𝒪_X)` with a map `P ⟶ 𝓕[0]` inducing
isomorphisms on cohomology in every degree `> m` and a surjection in degree `m`; that is,
approximation holds for the triple `(X, 𝓕, m)` in the sense of Stacks 08HI.  For `m = -1`,
`H⁰(P) ⟶ 𝓕` is an isomorphism and `Hⁱ(P) = 0` for `i > 0`, as in Stacks 08JY.

## Main results

* `AlgebraicGeometry.Space.exists_perfect_approximation_singleFunctor_of_isNoetherian`:
  approximation by a perfect complex holds for a quasi-coherent module of finite type on a
  Noetherian algebraic space, in every degree.

## References

* [Stacks Project, Tag 08JY](https://stacks.math.columbia.edu/tag/08JY)
* [Stacks Project, Tag 08HP](https://stacks.math.columbia.edu/tag/08HP)
* [Stacks Project, Tag 08HI](https://stacks.math.columbia.edu/tag/08HI)
* [Stacks Project, Tag 08IK](https://stacks.math.columbia.edu/tag/08IK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Approximation of a module of finite type on a Noetherian algebraic space.**  Let `X` be a
Noetherian algebraic space and `𝓕` a quasi-coherent `𝒪_X`-module of finite type.  For every integer
`m` some perfect object `P` of `D(𝒪_X)` maps to `𝓕[0]` by a map inducing isomorphisms on `Hⁱ` for
`i > m` and a surjection on `Hᵐ`. -/
theorem exists_perfect_approximation_singleFunctor_of_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hXN : IsNoetherian B S hS hZ X.1) (F : Modules.{u, u} B S hS X.1 X.2)
    [hFq : F.IsQuasicoherentOnSite] (hFt : SheafOfModules.IsFiniteTypeOnSite F) (m : ℤ) :
    ∃ (P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
      (_ : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P)
      (α : P ⟶ (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj F),
      (∀ i : ℤ, m < i →
        IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).map α)) ∧
      Epi ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) m).map α) := by
  have : Fact (HasEtaleLocalProperty B S hS X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hXN.2.2⟩
  have hFc : IsCoherent B S hS X.1 X.2 F :=
    (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS X.1 X.2 F).2
      ⟨hFq, Stacks.SheafOfModules.presheafIsFiniteType_of_isFiniteTypeOnSite F hFt⟩
  let K := (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj F
  have hle : ∀ i : ℤ, 0 < i →
      IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj K) :=
    (DerivedCategory.isLE_iff K 0).1 inferInstance
  have hge : ∀ i : ℤ, i < 0 →
      IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj K) :=
    (DerivedCategory.isGE_iff K 0).1 inferInstance
  have hcoh : ∀ i : ℤ, IsCoherent B S hS X.1 X.2
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj K) := by
    intro i
    rcases lt_trichotomy i 0 with h | rfl | h
    · exact IsCoherent.of_isZero B S hS X.1 X.2 (hge i h)
    · exact isCoherent_of_iso B S hS X.2
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm hFc
    · exact IsCoherent.of_isZero B S hS X.1 X.2 (hle i h)
  obtain ⟨Kc, hKc, ⟨eK⟩⟩ := isPseudoCoherent_of_isCoherent_homology_of_isNoetherian B S hS X hZ
    hXN K hcoh ⟨0, hle⟩
  obtain ⟨r, hr⟩ := approximationByPerfectComplexes_of_qcqs B S hS hZ X.1 X.2 hXN.1 hXN.2.1
    Set.univ isClosed_univ
    (isQuasiCompact_ι_openSubspace_of_eq_empty B S hS X.1 X.2 _ Set.compl_univ)
  let E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
    ⟨K, fun i => (hcoh i).toIsQuasicoherentOnSite⟩
  obtain ⟨P, hP, -, α, hiso, hepi⟩ := hr E m ⟨Kc, hKc (m - r), ⟨eK⟩⟩
    (fun _ _ => Set.subset_univ _)
  exact ⟨P, hP, α, hiso, hepi⟩

end AlgebraicGeometry.Space

end
