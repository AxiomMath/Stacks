module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
import StacksCore.Tactic.StacksAttribute

/-!
# Approximation by perfect complexes on an algebraic space

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  A *triple*
consists of a subset `T ⊆ |F|`, an object `E` of `D_QCoh(𝒪_F)` and an integer `m`, and
*approximation holds* for it when some perfect object `P` of `D(𝒪_F)` supported on `T` admits a
map `P ⟶ E` which is an isomorphism on cohomology in every degree above `m` and a surjection in
degree `m`.  *Approximation by perfect complexes holds* on `F` when, for every closed `T ⊆ |F|`
whose open complement has quasi-compact inclusion, one integer `r` makes approximation hold for
every triple `(T, E, m)` with `E` being `(m - r)`-pseudo-coherent and with `Hⁱ(E)` supported on
`T` for `i ≥ m - r`.

## Main definitions

* `AlgebraicGeometry.Space.ApproximationHolds` is approximation for one triple.
* `AlgebraicGeometry.Space.ApproximationByPerfectComplexes` is approximation on the space.

## References

* [Stacks Project, Tag 08HI](https://stacks.math.columbia.edu/tag/08HI)
* [Stacks Project, Tag 08HJ](https://stacks.math.columbia.edu/tag/08HJ)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [∀ U : (smallEtaleRingedSite B S hS F hF).C,
      HasSheafify ((smallEtaleRingedSite B S hS F hF).J.over U) AddCommGrpCat.{m}]
    [∀ U : (smallEtaleRingedSite B S hS F hF).C,
      ((smallEtaleRingedSite B S hS F hF).J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
    [∀ U : (smallEtaleRingedSite B S hS F hF).C,
      ((smallEtaleRingedSite B S hS F hF).J.over U).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- *Approximation holds* for the triple `(T, E, m)`: some perfect object of `D(𝒪_F)` supported on
`T` maps to `E` by a map inducing isomorphisms on cohomology in every degree above `m` and a
surjection in degree `m`. -/
@[stacks 08HI]
noncomputable abbrev ApproximationHolds (T : Set (points B S hS F))
    (E : QuasicoherentDerivedCategory.{u, m} B S hS F hF) (m : ℤ) : Prop :=
  ∃ P : DerivedCategory (Modules.{u, m} B S hS F hF),
    (smallEtaleRingedSite B S hS F hF).IsPerfect P ∧
      CohomologySupportedOn B S hS F hF T P ∧
      ∃ α : P ⟶ E.obj,
        (∀ i : ℤ, m < i →
          IsIso ((DerivedCategory.homologyFunctor (Modules.{u, m} B S hS F hF) i).map α)) ∧
        Epi ((DerivedCategory.homologyFunctor (Modules.{u, m} B S hS F hF) m).map α)

/-- *Approximation by perfect complexes holds* on `F`: for every closed `T ⊆ |F|` whose open
complement has quasi-compact inclusion there is an integer `r` such that approximation holds for
every triple `(T, E, m)` in which `E` is `(m - r)`-pseudo-coherent and `Hⁱ(E)` is supported on `T`
for every `i ≥ m - r`. -/
@[stacks 08HJ]
noncomputable abbrev ApproximationByPerfectComplexes : Prop :=
  letI : TopologicalSpace (points B S hS F) := pointTopology B S hS F
  ∀ (T : Set (points B S hS F)) (hT : IsClosed T),
    IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS F hF).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι →
    ∃ r : ℤ, ∀ (E : QuasicoherentDerivedCategory.{u, m} B S hS F hF) (m : ℤ),
      (smallEtaleRingedSite B S hS F hF).IsPseudoCoherentFrom E.obj (m - r) →
      (∀ i : ℤ, m - r ≤ i →
        supportOfSheaf B S hS F
          ((SheafOfModules.toSheaf
              ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).obj
            ((DerivedCategory.homologyFunctor
              (Modules.{u, m} B S hS F hF) i).obj E.obj)) ⊆ T) →
      ApproximationHolds B S hS F hF T E m

end AlgebraicGeometry.Space

end
