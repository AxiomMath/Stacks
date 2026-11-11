module

public import StacksFrontier.AlgebraicGeometry.AffineExtend.Induction
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.NonvanishingLocus
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.StalkDepthCriterion
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.SpecializationStableExistence
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.FiberMaximalSpectrum
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.DepthLocusClosed
public import StacksFrontier.Topology.Dimension.DimensionFunctionObstruction
public import StacksCore.Tactic.StacksAttribute

import all StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtensionExistence
import all StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.NestedImprovement

/-!
# The closed subset of a specialization-stable subset, glued from the affine opens

`Stacks.LocalCohomology.exists_isClosed_subset_depth_lt_two_subset` produces, for a Noetherian
ring `A` with a dualizing complex, a specialization-stable `T ⊆ Spec(A)` and a finite `A`-module
`M` whose depth is at least one at the primes outside `T` admitting an immediate specialization
into `T`, a **closed** `Z ⊆ T` containing every `𝔮 ∈ T` with `depth(M_𝔮) < 2`.  That is the datum
`AlgebraicGeometry.exists_isDepthTwoExtension_of_isClosed_of_subset` asks for, over a ring.

This module glues those affine-local closed sets into a closed subset of a scheme, and so proves
the existence half of [Stacks, Tag 0EI3] along a subset stable under specialization, at the
source's two hypotheses.

## Main results

* `StableUnderSpecialization.exists_isClosed_image_subset`: the image of a closed subset of a
  Noetherian sober space under a continuous map into a space with a specialization-stable `T`
  lies in a closed subset of `T`, as soon as the image lies in `T`.
* `AlgebraicGeometry.exists_isClosed_subset_depth_lt_two_of_isAffineOpen`: the low-depth locus of
  `T` inside one affine open lies in a closed subset of `T`.
* `AlgebraicGeometry.exists_isClosed_subset_depth_lt_two`: the low-depth locus of `T` lies in a
  closed subset of `T`.
* `AlgebraicGeometry.exists_isDepthTwoExtension_of_stableUnderSpecialization`:
  **[Stacks, Tag 0EI3], existence** along a specialization-stable `T`, at exactly the source's
  two hypotheses.

## The gluing

Fix an affine open `U` with `A = Γ(X, U)`, Noetherian because `X` is, and with a dualizing
complex because `X` locally has one.  Write `j : Spec(A) → X` for `IsAffineOpen.fromSpec`, an
open embedding with image `U`.  The ring-level input is assembled from:

* `M = Γ(F, U)`, a finite `A`-module by
  `AlgebraicGeometry.moduleFinite_sections_on_affine`, a coherent module being quasi-coherent and
  of finite type;
* `T_A = j⁻¹(T)`, stable under specialization because `j` is continuous;
* the depth hypothesis, carried from `X` to `Spec(A)` by
  `TopologicalSpace.IsImmediateSpecialization.map_of_isOpenEmbedding` on the topological side and
  by `AlgebraicGeometry.depth_stalk_eq_depth_localizedModule` on the module side — the stalk of
  `F` at `j(𝔭)` has the depth of `M_𝔭`, the germ maps identifying the two semilinearly;
* the height bound, from `Dualizing.exists_height_le_of_isDualizingComplex`.

The resulting `Z_A ⊆ Spec(A)` is closed, so it is a finite union of irreducible closed sets, each
of which has a generic point because `Spec(A)` is sober.  Those generic points lie in `T_A`, so
their images lie in `T`, so the finite union of the closures in `X` of their images is a closed
subset of `T`; and it contains `j(Z_A)`, since the image of a point of `Z_A` is a specialization
of the image of the generic point of the component containing it.  That is
`StableUnderSpecialization.exists_isClosed_image_subset`, which needs only continuity of `j`.

Finally `X` is quasi-compact, so finitely many affine opens cover it
(`Stacks.AlgebraicGeometry.Tag01PFAffineExtend.exists_finset_affineOpens_iSup_eq_top`) and the
union of the corresponding closed sets is the global `Z`.

## References

* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)
* [Stacks Project, Tag 0EF8](https://stacks.math.columbia.edu/tag/0EF8)
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### A closed subset of a specialization-stable set from a closed subset upstairs -/

/-- **The image of a closed set lands in a closed subset of a specialization-stable set.** Let
`T ⊆ α` be stable under specialization, let `β` be a Noetherian sober space, let `f : β → α` be
continuous and let `Z ⊆ β` be closed with `f(Z) ⊆ T`.  Then there is a closed `W ⊆ T` with
`f(Z) ⊆ W`.

The closure of `f(Z)` itself need not lie in `T`, `T` being closed under specialization but not
closed.  What works is that `Z` has finitely many irreducible components, each with a generic
point `g`: the component is `closure {g}`, so the closure of its image lies in `closure {f(g)}`,
which lies in `T` because `f(g)` does.  The union of those finitely many closures is `W`. -/
public theorem StableUnderSpecialization.exists_isClosed_image_subset
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [NoetherianSpace β] [QuasiSober β]
    {T : Set α} (hT : StableUnderSpecialization T) {f : β → α} (hf : Continuous f)
    {Z : Set β} (hZ : IsClosed Z) (hZT : ∀ z ∈ Z, f z ∈ T) :
    ∃ W : Set α, IsClosed W ∧ W ⊆ T ∧ ∀ z ∈ Z, f z ∈ W := by
  classical
  obtain ⟨S, hSfin, hSclosed, hSirr, hZS⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine ⟨⋃ C ∈ S, closure (f '' C), hSfin.isClosed_biUnion fun C _ => isClosed_closure, ?_, ?_⟩
  · refine Set.iUnion₂_subset fun C hC => ?_
    obtain ⟨g, hg⟩ := QuasiSober.sober (hSirr C hC) (hSclosed C hC)
    have hgT : f g ∈ T := hZT g (by rw [hZS]; exact Set.mem_sUnion.mpr ⟨C, hC, hg.mem⟩)
    have h1 : closure (f '' C) ⊆ closure ({f g} : Set α) := by
      rw [← hg.def, ← Set.image_singleton (f := f) (a := g), ← closure_closure (s := f '' {g})]
      exact closure_mono (image_closure_subset_closure_image hf)
    intro y hy
    exact hT (specializes_iff_mem_closure.mpr (h1 hy)) hgT
  · intro z hz
    rw [hZS] at hz
    obtain ⟨C, hC, hzC⟩ := Set.mem_sUnion.mp hz
    exact Set.mem_iUnion₂.mpr ⟨C, hC, subset_closure (Set.mem_image_of_mem f hzC)⟩

namespace AlgebraicGeometry

/-! ### The low-depth locus inside one affine open -/

/-- **The low-depth locus of `T` inside an affine open lies in a closed subset of `T`.** Let `X`
be a Noetherian scheme which locally has a dualizing complex, let `T ⊆ X` be stable under
specialization and let `G` be a coherent `𝒪_X`-module whose depth at a point outside `T` is at
least one as soon as some point of `T` is an immediate specialization of it.  Then for every
affine open `U` there is a closed `W ⊆ T` containing every point of `T ∩ U` at which `G` has
depth below two. -/
public theorem exists_isClosed_subset_depth_lt_two_of_isAffineOpen
    (X : Scheme.{u}) [IsNoetherian X] (T : Set X) (hT : StableUnderSpecialization T)
    (G : X.Modules) [G.IsCoherent] (hdual : LocallyHasDualizingComplex X)
    (hdepth : ∀ x z : X, x ∉ T → z ∈ T → TopologicalSpace.IsImmediateSpecialization x z →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x))
    (U : X.affineOpens) :
    ∃ W : Set X, IsClosed W ∧ W ⊆ T ∧ ∀ x : X, x ∈ T → x ∈ (U.1 : Set X) →
      Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) < 2 → x ∈ W := by
  classical
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let : G.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent G
  let : G.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have hMfin : Module.Finite Γ(X, U.1) Γ(G, U.1) :=
    moduleFinite_sections_on_affine G U.1 U.2
  have hemb : Topology.IsOpenEmbedding U.2.fromSpec.base :=
    Scheme.Hom.isOpenEmbedding U.2.fromSpec
  have hmem : ∀ p : PrimeSpectrum Γ(X, U.1), U.2.fromSpec.base p ∈ U.1 := by
    intro p
    have h : U.2.fromSpec.base p ∈ Set.range U.2.fromSpec.base := Set.mem_range_self p
    rw [U.2.range_fromSpec] at h
    exact h
  have hdepthEq : ∀ p : PrimeSpectrum Γ(X, U.1),
      Module.depth (X.presheaf.stalk (U.2.fromSpec.base p))
          (IsLocalRing.maximalIdeal (X.presheaf.stalk (U.2.fromSpec.base p)))
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (U.2.fromSpec.base p)) =
        Module.depth (Localization.AtPrime p.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl Γ(G, U.1)) := by
    intro p
    have h := depth_stalk_eq_depth_localizedModule G U.2 (hmem p)
    rw [U.2.primeIdealOf_fromSpec p (hmem p)] at h
    exact h
  obtain ⟨omega, homega⟩ := hdual U
  obtain ⟨d, hd⟩ := Dualizing.exists_height_le_of_isDualizingComplex homega
  obtain ⟨Z, hZclosed, hZT, hZmem⟩ :=
    Stacks.LocalCohomology.exists_isClosed_subset_depth_lt_two_subset Γ(X, U.1) Γ(G, U.1)
      {p : PrimeSpectrum Γ(X, U.1) | U.2.fromSpec.base p ∈ T}
      (fun _ _ hpq hp => hT (hpq.map hemb.continuous) hp) d hd omega homega
      (fun p q hp hq hpq => by
        rw [← hdepthEq p]
        exact hdepth (U.2.fromSpec.base p) (U.2.fromSpec.base q) hp hq
          (hpq.map_of_isOpenEmbedding hemb))
  obtain ⟨W, hWclosed, hWT, hWmem⟩ :=
    hT.exists_isClosed_image_subset hemb.continuous hZclosed fun p hp => hZT hp
  refine ⟨W, hWclosed, hWT, fun x hx hxU hdep => ?_⟩
  obtain ⟨p, rfl⟩ : ∃ p, U.2.fromSpec.base p = x := ⟨_, U.2.fromSpec_primeIdealOf ⟨x, hxU⟩⟩
  exact hWmem _ (hZmem p hx (by rwa [← hdepthEq p]))

/-! ### The low-depth locus on the scheme -/

/-- **The low-depth locus of a specialization-stable subset lies in a closed subset of it.** Let
`X` be a Noetherian scheme which locally has a dualizing complex, let `T ⊆ X` be stable under
specialization and let `G` be a coherent `𝒪_X`-module whose depth at a point outside `T` is at
least one as soon as some point of `T` is an immediate specialization of it.  Then there is a
closed `Z ⊆ T` containing every point of `T` at which `G` has depth below two. -/
public theorem exists_isClosed_subset_depth_lt_two
    (X : Scheme.{u}) [IsNoetherian X] (T : Set X) (hT : StableUnderSpecialization T)
    (G : X.Modules) [G.IsCoherent] (hdual : LocallyHasDualizingComplex X)
    (hdepth : ∀ x z : X, x ∉ T → z ∈ T → TopologicalSpace.IsImmediateSpecialization x z →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x)) :
    ∃ Z : Set X, IsClosed Z ∧ Z ⊆ T ∧ ∀ x : X, x ∈ T →
      Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) < 2 → x ∈ Z := by
  classical
  obtain ⟨s, hs⟩ :=
    Stacks.AlgebraicGeometry.Tag01PFAffineExtend.exists_finset_affineOpens_iSup_eq_top (X := X)
  choose W hWclosed hWT hWmem using fun V : X.affineOpens =>
    exists_isClosed_subset_depth_lt_two_of_isAffineOpen X T hT G hdual hdepth V
  refine ⟨⋃ V ∈ s, W V, s.finite_toSet.isClosed_biUnion fun V _ => hWclosed V,
    Set.iUnion₂_subset fun V _ => hWT V, fun x hx hdep => ?_⟩
  have hxtop : x ∈ ⨆ V ∈ s, (V : X.Opens) := by
    rw [hs]
    trivial
  obtain ⟨V, hV⟩ := Opens.mem_iSup.mp hxtop
  obtain ⟨hVs, hxV⟩ := Opens.mem_iSup.mp hV
  exact Set.mem_iUnion₂.mpr ⟨V, hVs, hWmem V x hx hxV hdep⟩

/-! ### Tag 0EI3, existence along a specialization-stable subset, with no further datum -/

/-- Let `X` be a Noetherian scheme which locally has a dualizing complex, let `T ⊆ X` be stable
under specialization and let `F` be a coherent `𝒪_X`-module such that `depth(F_x) ≥ 1` whenever
some point of `T` is an immediate specialization of `x ∉ T`.  Then `F` admits a depth-two
extension along `T`. -/
public theorem exists_isDepthTwoExtension_of_stableUnderSpecialization
    (X : Scheme.{u}) [IsNoetherian X] (T : Set X) (hT : StableUnderSpecialization T)
    (F : X.Modules) [F.IsCoherent] (hdual : LocallyHasDualizingComplex X)
    (hdepth : ∀ x z : X, x ∉ T → z ∈ T → TopologicalSpace.IsImmediateSpecialization x z →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsDepthTwoExtension T φ := by
  have hF'coh : (depthOneQuotient X T hT F).IsCoherent := (depthOneQuotient_spec X T hT F).1
  have := hF'coh
  have hdepth' : ∀ x z : X, x ∉ T → z ∈ T → TopologicalSpace.IsImmediateSpecialization x z →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          (depthOneQuotient X T hT F).val.presheaf x) := by
    intro x z hx hz himm
    have heq := depth_stalk_eq_of_isIso_stalkMap (toDepthOneQuotient X T hT F) x
      (isIso_stalkMap_of_isIso_stalkFunctor _ _
        ((depthOneQuotient_spec X T hT F).2.2.1 x hx))
    exact le_trans (hdepth x z hx hz himm) (le_of_eq heq)
  obtain ⟨Z, hZclosed, hZT, hZmem⟩ :=
    exists_isClosed_subset_depth_lt_two X T hT (depthOneQuotient X T hT F) hdual hdepth'
  refine exists_isDepthTwoExtension_of_isClosed_of_subset X T hT F hdual hdepth Z hZclosed hZT
    fun x hx hxZ => ?_
  have hnot : ¬ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        (depthOneQuotient X T hT F).val.presheaf x) < 2 := fun h => hxZ (hZmem x hx h)
  exact not_lt.mp hnot

end AlgebraicGeometry

end
