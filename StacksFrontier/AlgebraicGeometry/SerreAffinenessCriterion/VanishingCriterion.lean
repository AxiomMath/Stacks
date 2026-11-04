module

public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.ClosedSubschemeSections
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.Serre
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.VanishingTransfer
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Serre's criterion for affineness

A quasi-compact scheme on which the first cohomology of every quasi-coherent sheaf of ideals
vanishes is affine.

The proof assembles the three parts already available: the vanishing hypothesis produces, around
every closed point `x` and inside every open containing it, a global section `r` with
`x ∈ X_r ⊆ U` (`Stacks.SerreCriterion.exists_basicOpen_mem_le`); taking `U` affine makes `X_r`
affine, and the topology of a quasi-compact scheme upgrades this from closed points to all
points. The same hypothesis makes any finite family of global sections whose basic opens cover
`X` generate the unit ideal (`Stacks.SerreCriterion.span_eq_top_of_forall_mem_basicOpen`). Those
are exactly the two inputs of
`Stacks.SerreAffinenessCriterion.isAffine_of_forall_isClosed_singleton_of_span_eq_top`.

## Main results

* `Stacks.SerreCriterion.isAffine_of_forall_isZero_H1_ideal`: Serre's criterion for affineness.

## Implementation notes

A quasi-coherent sheaf of ideals `𝓘 ⊆ 𝒪_X` is a subobject of `SheafOfModules.unit X.ringCatSheaf`
in the abelian category of sheaves of modules whose underlying module sheaf is quasi-coherent,
and `H¹(X, 𝓘)` is the first right derived functor of module-valued sections over `⊤` — so the
hypothesis is a statement about `Γ(X, 𝒪_X)`-modules, as in the source. The internal arguments use
the group-valued cohomology `Hgroup`, and
`Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup` crosses
between the two.

Quasi-compactness is `CompactSpace X`.

## References

* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.SerreCriterion

/-- **Serre's criterion for affineness.** A quasi-compact scheme on which the first cohomology
of every quasi-coherent sheaf of ideals vanishes is affine. -/
@[stacks 01XF,
  ega "II 5.2.1" "(d')⇒(a)",
  ega "IV 1.7.17" "(d') => affine",
  ega "III 1.4.7" "(ii), special case"]
theorem isAffine_of_forall_isZero_H1_ideal (X : Scheme.{u}) [CompactSpace X]
    (hH₁ : ∀ I : Subobject (SheafOfModules.unit X.ringCatSheaf),
      (Subobject.underlying.obj I).IsQuasicoherent →
        IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived 1).obj
          (Subobject.underlying.obj I))) :
    IsAffine X := by
  classical
  have hH : ∀ I : Subobject (SheafOfModules.unit X.ringCatSheaf),
      (Subobject.underlying.obj I).IsQuasicoherent →
        IsZero (Hgroup X.ringCatSheaf ⊤ 1 (Subobject.underlying.obj I)) := fun I hI =>
    (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
      X.ringCatSheaf ⊤ 1 _).1 (hH₁ I hI)
  have H₁ : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ r : Γ(X, ⊤), x ∈ X.basicOpen r ∧ ∃ U : X.Opens, IsAffineOpen U ∧ X.basicOpen r ≤ U := by
    intro x hx
    obtain ⟨U, hxU⟩ : ∃ U : X.affineOpens, x ∈ (U : X.Opens) :=
      Opens.mem_iSup.mp ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
    obtain ⟨r, hxr, hrU⟩ := exists_basicOpen_mem_le hH (U : X.Opens) x hxU hx
    exact ⟨r, hxr, U, U.2, hrU⟩
  refine Stacks.SerreAffinenessCriterion.isAffine_of_forall_isClosed_singleton_of_span_eq_top X
    (fun x _ => Stacks.SerreAffinenessCriterion.exists_isAffineOpen_basicOpen_mem_of_le X H₁ x)
    (fun s _ hcov => ?_)
  · set f : Option {r : Γ(X, ⊤) // r ∈ s} → Γ(X, ⊤) := fun i => i.elim 0 Subtype.val with hf
    have hcover : ∀ x : X, ∃ i, x ∈ X.basicOpen (f i) := by
      intro x
      obtain ⟨r, hr⟩ := Opens.mem_iSup.mp (hcov.ge (show x ∈ (⊤ : X.Opens) from trivial))
      obtain ⟨hrs, hxr⟩ := Opens.mem_iSup.mp hr
      exact ⟨some ⟨r, hrs⟩, hxr⟩
    have hrange : Set.range f = insert 0 (s : Set Γ(X, ⊤)) := by
      refine Set.eq_of_subset_of_subset ?_ ?_
      · rintro _ ⟨i, rfl⟩
        cases i with
        | none => exact Set.mem_insert _ _
        | some j => exact Set.mem_insert_of_mem _ j.2
      · rintro r hr
        rcases hr with rfl | hr
        · exact ⟨none, rfl⟩
        · exact ⟨some ⟨r, hr⟩, rfl⟩
    have hspan := span_eq_top_of_forall_mem_basicOpen hH f hcover
    rwa [hrange, Ideal.span_insert_zero] at hspan

end Stacks.SerreCriterion

end
