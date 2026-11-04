module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ComponentCriterion
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ComponentPositivity
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.ComponentDegreeDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DualizingAmple
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DualizingSheafDegree
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.DualizingSheafDegree
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.DualizingDegree
public import StacksFrontier.AlgebraicGeometry.Curves.NodalGorensteinReduced
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPrestableOpen
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilies

/-!
# A nodal curve over a field is stable exactly when its dualizing sheaf is ample

Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k` whose
singularities are at worst nodal. Then `X` has genus at least two and neither a rational tail nor
a rational bridge exactly when `ω_X` is ample. This is the equivalence of conditions (b) and (c)
of part (2) of Stacks 0E76, and it is the form in which the openness of the stable locus is used
in the proof of Stacks 0E8A: "since `ω_{Y_0}` is ample, after possibly shrinking `U`, `Y → U` is a
stable family".

## Main results

* `AlgebraicGeometry.forall_not_isRationalTail_and_not_isRationalBridge_of_isAmple`: an ample
  `ω_X` has positive degree on every component (Stacks 0B5Y), while it has negative degree on a
  rational tail (Stacks 0E63) and degree zero on a rational bridge (Stacks 0E64).
* `AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple_of_isConnected`: an ample invertible
  module on a connected proper curve has positive degree (Stacks 0AYW and 0B5Y).
* `AlgebraicGeometry.two_le_genus_of_isAmple_dualizingSheafOverField`: an ample `ω_X` forces
  genus at least two (`deg ω_X = 2g - 2`, Stacks 0C19).
* `AlgebraicGeometry.hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField`
  is the equivalence; the forward direction is Stacks 0E3P.

## Implementation notes

The proofs are those of `StacksFrontier/AlgebraicGeometry/Quot/CurvesStableOpen.lean`, where the
four curve lemmas enter as hypotheses; here they are
the library's Stacks 0E63, 0E64, 0C19 and 0E3P.

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E3P](https://stacks.math.columbia.edu/tag/0E3P)
* [Stacks Project, Tag 0E63](https://stacks.math.columbia.edu/tag/0E63)
* [Stacks Project, Tag 0E64](https://stacks.math.columbia.edu/tag/0E64)
* [Stacks Project, Tag 0C19](https://stacks.math.columbia.edu/tag/0C19)
* [Stacks Project, Tag 0B5Y](https://stacks.math.columbia.edu/tag/0B5Y)
* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.ComponentDegrees

/-- A one-dimensional irreducible component is the closure of a point of `genericPointsOne X`. -/
private theorem exists_genericPointsOne_closure_eq {X : Scheme.{u}} {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hdim : topologicalKrullDim Z = 1) :
    ∃ ζ : genericPointsOne X, closure ({ζ.1} : Set X) = Z := by
  have hcl : closure ({hZ.1.genericPoint} : Set X) = Z :=
    hZ.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  exact ⟨⟨hZ.1.genericPoint, mem_genericPointsOne_iff.2
    ⟨by change closure ({hZ.1.genericPoint} : Set X) ∈ irreducibleComponents X; rw [hcl]; exact hZ,
      by rw [hcl]; exact hdim⟩⟩, hcl⟩

/-- **An integral one-dimensional irreducible component is a reduced component.** A closed
subscheme `C` of `X` whose subscheme is integral, whose support is an irreducible component of
`X`, and which has dimension one, is the reduced induced structure `vanishingIdeal (closure {ζ})`
on the closure of a generic point `ζ` of `X` of dimension one: the indexing of Stacks 0B5Y. -/
theorem exists_genericPointsOne_eq_vanishingIdeal_of_isIntegral {X : Scheme.{u}}
    (C : X.IdealSheafData) [IsIntegral C.subscheme]
    (hirr : (C.support : Set X) ∈ irreducibleComponents X)
    (hCdim : topologicalKrullDim C.subscheme = 1) :
    ∃ ζ : genericPointsOne X, C = Scheme.IdealSheafData.vanishingIdeal
      ⟨closure ({ζ.1} : Set X), isClosed_closure⟩ := by
  obtain ⟨ζ, hcl⟩ := exists_genericPointsOne_closure_eq hirr
    (by rw [← Stacks.Chow.topologicalKrullDim_subscheme]; exact hCdim)
  exact ⟨ζ, Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme C _
    (TopologicalSpace.Closeds.ext hcl.symm)⟩

/-- **A curve with ample dualizing sheaf has neither a rational tail nor a rational bridge.** Let
`X` be proper of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k` and at-worst-nodal
singularities, and suppose `ω_X` is ample. Every irreducible component of dimension one then has
`deg(ω_X|_C) > 0` (Stacks 0B5Y), while a rational tail has `deg(ω_X|_C) < 0` (Stacks 0E63) and a
rational bridge has `deg(ω_X|_C) = 0` (Stacks 0E64). -/
theorem forall_not_isRationalTail_and_not_isRationalBridge_of_isAmple
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hω : ∃ _ : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))),
        Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) :
    (∀ C : X.IdealSheafData, ¬ IsRationalTail k X C) ∧
      ∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C := by
  obtain ⟨hinv, hL⟩ := hω
  have hpos := (isAmple_iff_forall_invertibleCurveDegree_reducedComponent_pos k
    (X ↘ Spec (.of k)) hdim.le (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))).1 hL
  have : ConnectedSpace X :=
    connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  have key : ∀ C : X.IdealSheafData, IsIntegral C.subscheme →
      (C.support : Set X) ∈ irreducibleComponents X →
      ∀ hCdim : topologicalKrullDim C.subscheme = 1,
      ∀ _ : SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))),
      0 < invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim.le
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) := by
    intro C hint hirr hCdim _
    obtain ⟨ζ, rfl⟩ := exists_genericPointsOne_eq_vanishingIdeal_of_isIntegral C hirr hCdim
    exact hpos ζ
  refine ⟨fun C hC => ?_, fun C hC => ?_⟩
  · have : IsIntegral C.subscheme := hC.1
    have h63 := invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail
      (k := k) (X := X) hdim hnodal C hC
    exact absurd h63 (not_lt.2 (key C hC.1 hC.2.1
      (Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalTail k X hdim C hC) _).le)
  · rcases id hC with ⟨hint, hirr, -⟩
    have := hint
    have h64 := invertibleCurveDegree_pullback_dualizingSheafOverField_eq_zero_of_isRationalBridge
      (k := k) (X := X) hdim hnodal C hC
    exact absurd h64 (key C hint hirr
      (Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalBridge k X hdim hC) _).ne'

/-- **The degree of an ample invertible module on a proper curve over a field is positive.** Let
`X` be proper over `k` of dimension one and connected, and `𝓛` an invertible ample
`𝒪_X`-module. Then `deg 𝓛 > 0`: by Stacks 0AYW `deg 𝓛 = ∑ m_i deg(𝓛|_{C_i})` over the
one-dimensional irreducible components, each multiplicity `m_i` is positive, each
`deg(𝓛|_{C_i})` is positive by Stacks 0B5Y, and there is at least one such component. -/
theorem invertibleCurveDegree_pos_of_isAmple_of_isConnected (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [ConnectedSpace X]
    (hdim : topologicalKrullDim X = 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple X L) :
    0 < invertibleCurveDegree k f hdim.le L := by
  classical
  have : IsNoetherian X := isNoetherian_of_isProper_over_field k f
  have : Fintype (genericPointsOne X) := (finite_genericPointsOne X).fintype
  -- a one-dimensional component exists
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨Z, hZ, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible ({x} : Set X)
    isIrreducible_singleton
  obtain ⟨ξ, -⟩ := exists_genericPointsOne_closure_eq hZ
    (topologicalKrullDim_eq_one_of_mem_irreducibleComponents hdim hZ)
  rw [invertibleCurveDegree_eq_curveDegree_one,
    Stacks.AlgebraicGeometry.ComponentDegreeDevissage.curveDegree_eq_finsum_componentDegree k f
      hdim.le L 1, finsum_eq_sum_of_fintype]
  refine Finset.sum_pos (fun η _ => mul_pos ?_ ?_) ⟨ξ, Finset.mem_univ _⟩
  · have hlen := componentMultiplicity_cast k f η
    have hpos : 0 < Module.length (X.presheaf.stalk η.1) (X.presheaf.stalk η.1) :=
      Module.length_pos
    rw [← hlen] at hpos
    exact_mod_cast hpos
  · have := invertibleCurveDegree_reducedComponent_pos_of_isAmple k f hdim.le L hL η
    rwa [invertibleCurveDegree_eq_curveDegree_one] at this

/-- **An ample dualizing sheaf forces genus at least two.** Let `X` be proper over `k` of
dimension one with `H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities, and suppose `ω_X` is
ample. Then `X` is Gorenstein (Stacks 0E37), so `deg ω_X = 2g - 2` (Stacks 0C19), and
`deg ω_X > 0` because `ω_X` is ample
(`AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple_of_isConnected`); hence `g ≥ 2`. -/
theorem two_le_genus_of_isAmple_dualizingSheafOverField
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hω : ∃ _ : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))),
        Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) :
    2 ≤ genus (X ↘ Spec (.of k)) := by
  obtain ⟨hinv, hL⟩ := hω
  have : ConnectedSpace X := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  have hdeg := invertibleCurveDegree_dualizingSheafOverField_of_isInvertible k
    (X ↘ Spec (.of k)) hdim.le
  have hpos := invertibleCurveDegree_pos_of_isAmple_of_isConnected k (X ↘ Spec (.of k)) hdim
    _ hL
  rw [hdeg] at hpos
  omega

/-- **Conditions (b) and (c) of part (2) of Stacks 0E76 agree.** Let `X` be proper over a field
`k` of dimension one with `H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities. Then `X` has genus
at least two and neither a rational tail nor a rational bridge exactly when `ω_X` is invertible
and ample: the forward direction is Stacks 0E3P, the converse
`AlgebraicGeometry.forall_not_isRationalTail_and_not_isRationalBridge_of_isAmple` and
`AlgebraicGeometry.two_le_genus_of_isAmple_dualizingSheafOverField`. -/
theorem hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X = 1)
    (hglob : Function.Bijective f.appTop)
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X) :
    HasGenusTwoNoRationalTailNoRationalBridge k f ↔
      ∃ _ : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          (Stacks.Duality.dualizingSheafOverField f),
        Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField f) := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : IsProper (X ↘ Spec (.of k)) := inferInstanceAs (IsProper f)
  have : IsIso f.appTop := (ConcreteCategory.isIso_iff_bijective f.appTop).2 hglob
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop) :=
    inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop))
  constructor
  · rintro ⟨hg, htail, _hp, hbridge⟩
    exact isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal htail
      hbridge hg
  · intro hω
    obtain ⟨htail, hbridge⟩ :=
      forall_not_isRationalTail_and_not_isRationalBridge_of_isAmple k X hdim hnodal hω
    exact ⟨two_le_genus_of_isAmple_dualizingSheafOverField k X hdim hnodal hω, htail,
      ⟨inferInstance, fun C => hbridge C⟩⟩

end AlgebraicGeometry

end
