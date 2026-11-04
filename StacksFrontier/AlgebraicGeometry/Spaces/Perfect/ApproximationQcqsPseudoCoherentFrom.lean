module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsLift
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DistinguishedTrianglesGeneral

/-!
# Approximations of objects pseudo-coherent from a degree

On a quasi-compact and quasi-separated algebraic space $X$ there is an integer $r$ such that
every object $E$ of $D_{QCoh}(\mathcal{O}_X)$ which is $(m - r)$-pseudo-coherent is approximated
in degree $m$ by a perfect complex: there is a map $P \to E$ from a perfect $P$ inducing
isomorphisms on $H^i$ for $i > m$ and a surjection on $H^m$.

## Main results

* `exists_approximatesFrom_of_isPseudoCoherentFrom`: Approximation by perfect complexes of
  objects pseudo-coherent from a degree, on a quasi-compact and quasi-separated algebraic space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Lift

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {B S hS} {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}

end Lift

section Square

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat pointTopology

variable {B S hS} {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}

end Square

section Qcqs

attribute [local instance] pointTopology

/-- For a quasi-compact and quasi-separated algebraic space `X` there is an integer `r` such that
for every `E` in the quasi-coherent derived category of `X` and every `m : ℤ` with `E`
pseudo-coherent from degree `m - r`, there are a perfect complex `P` and a map `α : P ⟶ E` with
`H^i(α)` an isomorphism for all `i > m` and `H^m(α)` an epimorphism. -/
theorem exists_approximatesFrom_of_isPseudoCoherentFrom (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1) :
    ∃ r : ℤ, ∀ (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (m : ℤ),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E.obj (m - r) →
      ∃ (P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (α : P ⟶ E.obj),
        (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P ∧
        (∀ i : ℤ, m < i →
          IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).map α)) ∧
        Epi ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) m).map α) := by
  let O := (openSubspacesOrderIso B S hS X.1 X.2).symm
    ⟨(Set.univ : Set (points B S hS X.1))ᶜ, isClosed_univ.isOpen_compl⟩
  have hOqc : IsQuasiCompactSpace B S hS O.1.toFunctor := by
    refine isQuasiCompactSpace_of_isCompact_range B S hS X.2 O.2 ?_
    rw [range_pointsMap_openSubspacesOrderIso_symm _ isClosed_univ, Set.compl_univ]
    exact isCompact_empty
  obtain ⟨r, hr⟩ := approximationByPerfectComplexes_of_qcqs B S hS B.contains_terminal X.1 X.2
    hXqc hXqs Set.univ isClosed_univ
    (isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal X.2 hXqs hOqc O.1.ι)
  refine ⟨r, fun E m hpc => ?_⟩
  obtain ⟨P, hP, -, α, h1, h2⟩ := hr E m hpc fun i _ => Set.subset_univ _
  exact ⟨P, α, hP, h1, h2⟩

end Qcqs

end AlgebraicGeometry.Space

end
