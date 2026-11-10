module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedApproximation
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.LocalNullHomotopyOverSlices

/-!
# Local strictly perfect approximations concentrated in a range of degrees

Let `X` be a ringed space and let `K` be an object of the derived category of `𝒪_X`-modules
which is `m`-pseudo-coherent and whose cohomology vanishes above a degree `r ≥ m`. Then `K` is
represented by a complex `C` which, locally on `X`, admits a strictly perfect approximation in
degrees `≥ m` with no terms above degree `r`.

The proof takes a local approximation `α : P ⟶ C|_U` coming from `m`-pseudo-coherence and
replaces `P` by its canonical truncation `τ^{≤ r} P`. For that truncation to stay strictly
perfect one needs the degree-`r` cycles of `P` to be a direct summand of a finite free module,
and that holds only after shrinking `U` to some `V`: it follows from a local null homotopy of the
inclusion `σ^{≥ r+1} P ⟶ P` of the stupid truncation, which is Stacks 08C7. Shrinking twice
leaves a statement about an open subspace of an open subspace of `X`, and the last step transports
it back to the corresponding open subspace of `X`.

## Main results

* `AlgebraicGeometry.RingedSpace.exists_strictlyPerfect_approximation_boundedAbove`: the
  approximation statement above.

## Implementation notes

Every ingredient apart from the assembly lives in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/BoundedApproximation.lean` and
`StacksFrontier/Algebra/Homology/StrictlyPerfectApproximation.lean`; this file only puts them
together. All universes coincide, as they must for `StrictlyPerfect.OXMod` to be defined.

## References

* [Stacks Project, Lemma 20.46.9 (08CC)](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Lemma 20.46.5 (08C7)](https://stacks.math.columbia.edu/tag/08C7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u d

variable {X : RingedSpace.{u, u}}

/-- The inclusion of the stupid truncation in degrees `≥ a` is an isomorphism in every degree
at least `a`. -/
theorem isIso_stupidTruncGEInclusion_f
    (E : CochainComplex (OXMod.{u, u} X) ℤ) (a i : ℤ) (hi : a ≤ i) :
    IsIso ((stupidTruncGEInclusion E a).f i) := by
  have hm : (ComplexShape.embeddingUpIntGE a).f ((i - a).toNat) = i := by
    rw [ComplexShape.embeddingUpIntGE_f]
    omega
  have hf : (stupidTruncGEInclusion E a).f i =
      (((E.restriction (ComplexShape.embeddingUpIntGE a)).extendXIso
          (ComplexShape.embeddingUpIntGE a) hm) ≪≫
        (E.restrictionXIso (ComplexShape.embeddingUpIntGE a) hm)).hom := by
    dsimp [stupidTruncGEInclusion]
    rw [dite_eq_left hi]
  rw [hf]
  exact Iso.isIso_hom _

/-- Restriction to an open subspace preserves the vanishing of homology above a degree. -/
private theorem isZero_homology_restrictComplex {Y : RingedSpace.{u, u}} (W : Opens Y.carrier)
    (E : CochainComplex (OXMod.{u, u} Y) ℤ) (r i : ℤ) (hi : r < i)
    (h : ∀ j : ℤ, r < j → IsZero (E.homology j)) :
    IsZero ((restrictComplex E W).homology i) := by
  have := restrictModules_preservesFiniteLimits Y W
  have := restrictModules_preservesFiniteColimits Y W
  exact ((restrictModules Y W).map_isZero (h i hi)).of_iso
    ((E.sc i).mapHomologyIso (restrictModules Y W))

/-- A pseudo-coherent object of the derived category of `𝒪_X`-modules whose cohomology vanishes
above `r` is represented by a complex with local strictly perfect approximations in degrees
`≥ m` concentrated in degrees `≤ r`. -/
theorem exists_strictlyPerfect_approximation_boundedAbove
    [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (K : DerivedCategory (OXMod.{u, u} X)) (m r : ℤ) (hmr : m ≤ r)
    (hK : IsPseudoCoherentFrom K m)
    (hzero : ∀ i : ℤ, r < i →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj K)) :
    ∃ C : CochainComplex (OXMod.{u, u} X) ℤ,
      Nonempty (DerivedCategory.Q.obj C ≅ K) ∧
      ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
        ∃ P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
          IsStrictlyPerfect P ∧ (∀ i : ℤ, r < i → IsZero (P.X i)) ∧
          ∃ α : P ⟶ restrictComplex C U,
            (∀ i : ℤ, m < i → IsIso (HomologicalComplex.homologyMap α i)) ∧
            Epi (HomologicalComplex.homologyMap α m) := by
  obtain ⟨C, hC, hCiso⟩ := hK
  have hCexact (i : ℤ) (hi : r < i) : IsZero (C.homology i) := by
    refine (hzero i hi).of_iso (Iso.trans ?_
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).mapIso (Classical.choice hCiso)))
    exact ((DerivedCategory.homologyFunctorFactors (OXMod.{u, u} X) i).app C).symm
  refine ⟨C, hCiso, fun x => ?_⟩
  obtain ⟨U, hxU, P, hP, α, hαiso, hαepi⟩ := hC x
  have hCUzero (i : ℤ) (hi : r < i) : IsZero ((restrictComplex C U).homology i) :=
    isZero_homology_restrictComplex U C r i hi hCexact
  have hPzero (i : ℤ) (hi : r < i) : IsZero (P.homology i) := by
    have : IsIso (HomologicalComplex.homologyMap α i) := hαiso i (lt_of_le_of_lt hmr hi)
    exact (hCUzero i hi).of_iso (asIso (HomologicalComplex.homologyMap α i))
  -- Shrink `U` so that the inclusion of the stupid truncation `σ^{≥ r+1} P ⟶ P` becomes
  -- null homotopic (Stacks 08C7).
  obtain ⟨V, hxV, hnull⟩ := exists_local_homotopy_zero_of_isZero_homology
    (α := stupidTruncGEInclusion P (r + 1)) (r + 1)
    (isStrictlyPerfect_stupidTruncGE P hP (r + 1))
    (fun i hi => P.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE (r + 1)) i
      (fun n => by rw [ComplexShape.embeddingUpIntGE_f]; omega))
    (fun i hi => hPzero i (by omega)) ⟨x, hxU⟩
  obtain ⟨hnull⟩ := nonempty_homotopy_zero_restrictModules V
    (stupidTruncGEInclusion P (r + 1)) hnull
  have hlim : PreservesFiniteLimits
      (restrictModules (X.restrict U.isOpenEmbedding) V) :=
    restrictModules_preservesFiniteLimits _ V
  have hcolim : PreservesFiniteColimits
      (restrictModules (X.restrict U.isOpenEmbedding) V) :=
    restrictModules_preservesFiniteColimits _ V
  have hiotaiso (j : ℤ) (hj : r + 1 ≤ j) : IsIso
      ((((restrictModules (X.restrict U.isOpenEmbedding) V).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (stupidTruncGEInclusion P (r + 1))).f j) := by
    have h := isIso_stupidTruncGEInclusion_f P (r + 1) j hj
    change IsIso ((restrictModules (X.restrict U.isOpenEmbedding) V).map
      ((stupidTruncGEInclusion P (r + 1)).f j))
    exact Functor.map_isIso _ _
  have hcyc : IsDirectSummandOfFiniteFree ((restrictComplex P V).cycles r) :=
    isDirectSummandOfFiniteFree_of_iso
      (eqToIso (congrArg (fun j : ℤ => (restrictComplex P V).cycles j) (by omega)))
      (isDirectSummandOfFiniteFree_cycles_of_tailHomotopy (restrictComplex P V)
        (isStrictlyPerfect_restrictComplex hP V) (r + 1) _ _
        (hiotaiso (r + 1) le_rfl) (hiotaiso (r + 1 + 1) (by omega)) hnull)
  have hCUVzero (i : ℤ) (hi : r < i) :
      IsZero ((restrictComplex (restrictComplex C U) V).homology i) :=
    isZero_homology_restrictComplex V _ r i hi hCUzero
  obtain ⟨Q, hQ, hQtop, β, hβiso, hβepi⟩ :=
    exists_isStrictlyPerfect_boundedAbove_of_approximation
      (isStrictlyPerfect_restrictComplex hP V) m r hmr hCUVzero
      (((restrictModules (X.restrict U.isOpenEmbedding) V).mapHomologicalComplex
        (ComplexShape.up ℤ)).map α)
      (fun j hj => isIso_homologyMap_map
        (restrictModules (X.restrict U.isOpenEmbedding) V) α j (hαiso j hj))
      (epi_homologyMap_map (restrictModules (X.restrict U.isOpenEmbedding) V)
        α m hαepi) hcyc
  obtain ⟨P', hP', hP'top, γ, hγiso, hγepi⟩ :=
    exists_strictlyPerfect_approximation_of_nested U V C m r Q hQ hQtop β hβiso hβepi
  refine ⟨U.isOpenEmbedding.functor.obj V, ?_, P', hP', hP'top, γ, hγiso, hγepi⟩
  exact ⟨⟨x, hxU⟩, hxV, rfl⟩

end AlgebraicGeometry.RingedSpace

end
