module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.AffineChartAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CanonicalExtensionCdOneDepthThree
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.MittagLefflerCriterion

/-!
# The conditions of Stacks 0EHH on the affine charts of a scheme

The canonical extensions used in the proof of [Stacks, Tag 0EJK] live on the affine charts of the
blowup, and they are assembled into one object of `Coh(X', I𝒪_{X'})` by
`Stacks.Coherent.exists_coherentAdicSystem_restrict_iso_of_affineCover`, which asks on each chart
for the three conditions of the Mittag-Leffler criterion [Stacks, Tag 0EHH]: the inverse system
of sections is Mittag-Leffler, the kernels of the projections out of its limit `M` are eventually
inside every `Iⁿ⁺¹M`, and the images of `M` in its terms are finite.

This file supplies those conditions in the two cases that occur.

* Under the hypotheses of [Stacks, Tag 0EJI] (a dualizing complex, `cd(A, I) = 1`, and a
  pro-isomorphism to a system with `depth + δ ≥ 3`) they are the three conditions the proof of
  0EJI establishes on the way to the canonical extension
  (`Stacks.Algebraization.zeroEHHConditions_of_cd_one_of_proIso_depthThree`).
* When `I` is the unit ideal every term of the system vanishes, and they hold trivially
  (`Stacks.Algebraization.zeroEHHConditions_of_ideal_eq_top`).

They are then moved from the chart situation of an affine open `V` to the sections over `V` of
the direct images (`Stacks.Algebraization.zeroEHHConditions_chart`).

## Main results

* `Stacks.Algebraization.zeroEHHConditions_of_cd_one_of_proIso_depthThree`
* `Stacks.Algebraization.zeroEHHConditions_of_ideal_eq_top`
* `Stacks.Algebraization.zeroEHHConditions_chart`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Algebraization

/-- The three conditions (a), (b), (c) of [Stacks, Tag 0EHH] for an inverse system `H` of
`A`-modules and an ideal `J`: `H` is Mittag-Leffler, the kernels of the projections out of
`lim H` are eventually inside every `Jⁿ⁺¹ lim H`, and the images of `lim H` in the terms of `H`
are finite. -/
abbrev ZeroEHHConditions {A : Type u} [CommRing A] (H : ℕᵒᵖ ⥤ ModuleCat.{u} A) (J : Ideal A) :
    Prop :=
  IsMittagLefflerCategorical H ∧
    (∀ n : ℕ, ∃ a : ℕ, LinearMap.ker (limit.π H (op a)).hom ≤
      J ^ (n + 1) • (⊤ : Submodule A (limit H : ModuleCat.{u} A))) ∧
    ∀ n : ℕ, Module.Finite A (LinearMap.range (limit.π H (op n)).hom)

/-- The conditions of [Stacks, Tag 0EHH] are invariant under isomorphism of inverse systems: if
`H ≅ H'` and `H` satisfies them for `J`, so does `H'`. -/
theorem ZeroEHHConditions.of_iso {A : Type u} [CommRing A] {H H' : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (e : H ≅ H') {J : Ideal A} (h : ZeroEHHConditions H J) : ZeroEHHConditions H' J :=
  ⟨Stacks.Coherent.isMittagLefflerCategorical_of_iso e h.1,
    Stacks.Coherent.exists_ker_limitπ_le_of_iso e h.2.1,
    fun n => Stacks.Coherent.finite_range_limitπ_of_iso e n (h.2.2 n)⟩

variable (S : AlgebraizationSituation.{u}) (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- **The conditions of [Stacks, Tag 0EHH] under the hypotheses of [Stacks, Tag 0EJI].** If `A`
has a dualizing complex, `cd(A, I) = 1`, and `(ℱₙ)` is pro-isomorphic to an inverse system of
coherent `𝒪_U`-modules with `depth + δ^Y_Z ≥ 3` on `U ∩ Y`, then the sections `H⁰(U, ℱₙ)` satisfy
the three conditions of 0EHH. -/
theorem zeroEHHConditions_of_cd_one_of_proIso_depthThree
    (hdual : ∃ K : @DerivedCategory (ModuleCat.{u} S.A) _ _
      (HasDerivedCategory.standard (ModuleCat.{u} S.A)),
      @Dualizing.IsDualizingComplex S.A _ _ (HasDerivedCategory.standard (ModuleCat.{u} S.A)) K)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) = 1)
    (G : ℕᵒᵖ ⥤ S.U.toScheme.Modules) [∀ n : ℕᵒᵖ, (G.obj n).IsCoherent]
    (e : InverseSequence.ProIso F.obj G)
    (hdepth : ∀ n : ℕ, ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
      3 ≤ depthOfStalkOnOpen S (G.obj (op n)) y + S.distanceToZ z) :
    ZeroEHHConditions (globalSectionsSystem S F) S.I := by
  have hG : ∀ n, HasFiniteTorsionCohomology S (G.obj (op n)) := fun n =>
    hasFiniteTorsionCohomology_of_depthThree S hdual (G.obj (op n)) (hdepth n)
  refine ⟨isMittagLefflerCategorical_globalSectionsSystem_of_cd_one S F hcd fun N =>
      ⟨_, _, finite_range_tr_of_proIso S F G e (openCohomologyFunctor S 1)
        (fun m k => by
          obtain ⟨K, ι, hfac, -, h1⟩ := hG m k
          exact ⟨K, ι, hfac, h1⟩) N⟩,
    exists_projection_ker_le_adicPower S F
      (limitGlobalSections_topology_eq_adicModuleTopology S F hcd),
    finite_range_limitProjection_of_torsionFinite S F G e hG⟩

/-- **The conditions of [Stacks, Tag 0EHH] for the unit ideal.** If `I = A`, every term `ℱₙ` is
killed by `Iⁿ⁺¹ = A`, so its sections vanish and the three conditions hold trivially. -/
theorem zeroEHHConditions_of_ideal_eq_top (hI : S.I = ⊤) :
    ZeroEHHConditions (globalSectionsSystem S F) S.I := by
  have hsub : ∀ n : ℕ, Subsingleton ((globalSectionsSystem S F).obj (op n)) := by
    intro n
    refine ⟨fun x y => ?_⟩
    have h0 := sectionSmul_term_eq_zero S F n (a := 1) (by rw [hI, Ideal.top_pow]; trivial)
    have hx : ∀ m : Γ(F.obj.obj (op n), ⊤), m = 0 := fun m => by
      have := congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤ m) h0
      simpa [sectionSmul_app] using this
    exact (hx x).trans (hx y).symm
  have hlim : Subsingleton (limit (globalSectionsSystem S F) : ModuleCat.{u} S.A) := by
    refine ⟨fun x y => ?_⟩
    refine Concrete.limit_ext _ x y fun n => ?_
    exact Subsingleton.elim (h := hsub n.unop) _ _
  refine ⟨isMittagLefflerCategorical_of_forall_exists_range_eq _
      fun i => ⟨i, le_rfl, fun k _ => ?_⟩,
    fun n => ⟨0, fun x _ => by rw [Subsingleton.elim x 0]; exact Submodule.zero_mem _⟩,
    fun n => ?_⟩
  · have := hsub i
    exact Subsingleton.elim _ _
  · have := hsub n
    infer_instance

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData) (U : X.Opens)
  (V : X.affineOpens) (hU : ((U : Set X))ᶜ ⊆ I.support)

/-- **The conditions of [Stacks, Tag 0EHH] on an affine chart**, moved from the chart situation of
`V` to the sections over `V` of the direct images `j_*ℋₙ`. -/
theorem zeroEHHConditions_chart (H : Stacks.Coherent.CoherentAdicSystems (I.comap U.ι))
    (h : ZeroEHHConditions (globalSectionsSystem (chartSituation I U V hU)
      (chartSystem I U V hU H)) (I.ideal V)) :
    ZeroEHHConditions ((H.obj ⋙ Scheme.Modules.pushforward U.ι) ⋙
      affineSectionFunctor V) (I.ideal V) :=
  h.of_iso (chartSectionsSystemIso I U V hU H)

end Stacks.Algebraization

end
