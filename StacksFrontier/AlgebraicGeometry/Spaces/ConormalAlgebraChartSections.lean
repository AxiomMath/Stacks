module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraChartSectionsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartSectionsBound
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecChosenAtlas

/-!
# The chart sections of the conormal algebra of an immersion are bounded

Let `i : Z ⟶ X` be an immersion of algebraic spaces over a scheme `S` contained in a big fppf site
`B`.  This file proves that the ungraded conormal algebra `𝒞_{Z/X,*}` of Stacks 09RN has bounded
chart sections in the sense of `AlgebraicGeometry.Space.HasBoundedChartSections`: for every étale
chart `V` of `Z` one cardinal below the cutoff bounds its sections over the étale charts cut out by
all the affine opens of the scheme of `V`.  This is the size condition under which its relative
spectrum — the normal cone of Stacks 09RU — is an algebraic space of the site.

The bound is assembled degree by degree.  In degree `n` the piece is `i^*(𝓘ⁿ)` for the closed
factorisation `i : Z ⟶ X ∖ ∂Z` and `𝓘` the ideal sheaf of its image; `𝓘ⁿ` is a quasi-coherent
sheaf of ideals of `𝒪_{X ∖ ∂Z}`, so its sections over an étale chart are regular functions on the
chart and are fewer than the cutoff, and
`AlgebraicGeometry.Space.exists_mk_modulePullback_openChart_sections_le` turns that into one bound
for the sections of `i^*(𝓘ⁿ)` over all the Zariski opens of `V`.  The degrees are countably many
and the cutoff has uncountable cofinality, so one cardinal bounds every degree; over an affine
chart the sections of the ungraded algebra are the direct sum of those of the pieces
(`AlgebraicGeometry.Space.mk_gradedAlgebraSheaf_sections_le`), bounded by its `ℵ₀`-th power, which
the cutoff absorbs, being a strong limit.

## Main results

* `AlgebraicGeometry.Space.hasCardinalLT_kernelIdealSheafZPow_sections`: the sections of a power
  of the kernel ideal sheaf over an étale chart are fewer than the cutoff.
* `AlgebraicGeometry.Space.hasBoundedChartSections_conormalAlgebraSheafOfImmersion`: **the
  conormal algebra of an immersion has bounded chart sections.**

## References

* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 09RU](https://stacks.math.columbia.edu/tag/09RU)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The sections of a power of the kernel ideal sheaf over an étale chart are fewer than the
cutoff**: they are regular functions on the chart. -/
theorem hasCardinalLT_kernelIdealSheafZPow_sections {X Z : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    HasCardinalLT ((kernelIdealSheafZPow B S hS i n).toSheafOfModules.val.obj U) B.cutoff := by
  refine (hasCardinalLT_iff_cardinal_mk_lt _ _).2 ?_
  refine lt_of_le_of_lt ?_ (mk_sections_structureRingSheaf_lt_cutoff B S hS X U.unop)
  exact Cardinal.mk_le_of_injective (f := fun x => (x.1 :
    ToType ((structureRingSheaf B S hS X).obj.obj U))) fun _ _ h => Subtype.ext h

attribute [local instance] pointTopology

variable {Z₀ X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Each homogeneous piece of the conormal algebra of an immersion has uniformly bounded
sections over the Zariski opens of an étale chart**: the piece of degree `n` is `i^*(𝓘ⁿ)` for
the closed factorisation `i`, and the sections of `𝓘ⁿ` over the étale charts of the ambient space
are regular functions there. -/
theorem exists_mk_conormalAlgebraOfImmersion_piece_openChart_le
    (hX : IsAlgebraicSpace B S hS X₀) (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀)
    (hi : IsImmersion B S hS i) (n : ℕ) (V : SmallEtale B S hS Z₀) :
    ∃ c < B.cutoff, ∀ Ω : (chartScheme V).Opens,
      #(((conormalAlgebraOfImmersion B S hS hX hZ i hi).piece (n : ℤ)).val.obj
        (op ((openChartFunctor B S hS Z₀ V).obj Ω))) ≤ c :=
  exists_mk_modulePullback_openChart_sections_le (immersionClosedFactorization B S hS hX hZ i hi)
    _ (isQuasicoherentOnSite_kernelIdealSheafZPow_natCast B S hS _ (by
        rw [kernelIdealSheaf_immersionClosedFactorization]
        exact isQuasicoherentOnSite_definingIdealSheaf B S hS _ _) n)
    (hasCardinalLT_kernelIdealSheafZPow_sections B S hS _ (n : ℤ)) V

/-- **The conormal algebra `𝒞_{Z/X,*}` of an immersion has bounded chart sections.** -/
theorem hasBoundedChartSections_conormalAlgebraSheafOfImmersion
    (hX : IsAlgebraicSpace B S hS X₀) (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀)
    (hi : IsImmersion B S hS i) :
    HasBoundedChartSections B S hS ⟨Z₀, hZ⟩
      (conormalAlgebraSheafOfImmersion B S hS hX hZ i hi) := by
  intro V
  choose c hc hcΩ using fun n : ℕ =>
    exists_mk_conormalAlgebraOfImmersion_piece_openChart_le B S hS hX hZ i hi n V
  have hsup : (⨆ n : ULift.{u} ℕ, c n.down) < B.cutoff :=
    Cardinal.iSup_lt_of_lt_cof_ord (α := ULift.{u} ℕ)
      ((Cardinal.mk_le_aleph0 :
        Cardinal.mk (ULift.{u} ℕ) ≤ Cardinal.aleph0).trans_lt B.aleph0_lt_cutoff_cof)
      fun n => hc n.down
  refine ⟨(⨆ n : ULift.{u} ℕ, c n.down) ^ ℵ₀,
    power_lt_of_isStrongPrelimit B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hsup
      B.aleph0_lt_cutoff, fun O => ?_⟩
  have hO : IsAffine ((SmallEtale.toOver B S hS Z₀ ⋙ BigFppfOver.toScheme B S hS).obj
      (openChart B S hS Z₀ V (O : (chartScheme V).Opens))) := O.2
  exact mk_gradedAlgebraSheaf_sections_le B S hS _ _ _
    (fun _ hn => isZero_conormalAlgebraOfImmersion_piece_of_neg B S hS hX hZ i hi hn) _ hO
    fun n => (hcΩ n O).trans (le_ciSup Cardinal.bddAbove_of_small (⟨n⟩ : ULift.{u} ℕ))

end AlgebraicGeometry.Space

end
