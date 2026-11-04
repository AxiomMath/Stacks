module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Devissage
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimensionEq
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.DisjointSections
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDropApplications
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.KeyLemma
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.MovingFamilyChowModel
public import StacksFrontier.AlgebraicGeometry.Intersection.ProjectionFormulaFlat.Basic

/-!
# Moving a subvariety of projective space off finitely many subvarieties

Let `A ⊆ 𝐏^n` be a closed subvariety of dimension `r` of the projective space of a vector space
over an algebraically closed field, and let `T i ⊆ 𝐏^n` be finitely many closed subvarieties.
Then `[A]` is rationally equivalent to an `r`-cycle each of whose components intersects every
`T i` properly.

This is the step of the moving lemma (Tag 0B1U) which takes place in projective space. Tag 0B1T,
applied with `X = 𝐏^n`, moves `A` in a family `C' ⊆ 𝐏^n × 𝐏¹` with `C'_0 = A` and `C'_∞` meeting
every `T i` properly; it is used in the model `Stacks.Chow.projectiveLineProduct` of the Chow
chapter, where it is
`AlgebraicGeometry.ProjectiveLineBridge.exists_movingFamily_projectiveLineProduct`. Then
`[C'_0]_r ∼_rat [C'_∞]_r` by Tag 02S4 part (2), and the components of `[C'_∞]_r` lie in `C'_∞`.

## Main results

* `ProjectiveSpaceOfModule.exists_rationallyEquivalent_pointCycle_forall_intersectProperly`:
  the statement above, for the prime cycle of a point `a` of `𝐏^n`.

## Implementation notes

Tag 02S4 part (2) needs the relative dimension of the family, `dim C' = r + 1`, which Tag 0B1T
does not state. It is read off the zero fibre:
`Stacks.Chow.relativeDimension_genericPoints_eq_of_schemeDeltaDimension_zeroFiber_eq`. That the
family lies in neither section is the dominance of `C' → 𝐏¹`, made into surjectivity by
properness of `𝐏^n`, and the nonemptiness of the zero fibre. The components of `[C'_∞]_r` lie in
`C'_∞`, which has dimension at most `r` (`Stacks.Chow.schemeDeltaDimension_infinityFiber_le`),
so clause (4) of Tag 0B1T gives the dimension bound for each of them.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0B1U](https://stacks.math.columbia.edu/tag/0B1U)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow

universe u

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

/-- The fundamental `k`-cycle of the integral closed subscheme attached to a point `x` of
relative dimension `k` is the prime cycle `[x]`. -/
private theorem cycleAssociatedToClosedSubscheme_integralComponentAt_eq_pointCycle
    (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] {k : ℤ}
    (x : X) (hx : relativeDimension C.dimensionFunction p x = k) :
    cycleAssociatedToClosedSubscheme C p (integralComponentAt x).subschemeι k =
      pointCycle C p k x hx := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  rw [pointCycle_apply]
  split_ifs with hy
  · subst hy
    exact cycleAssociatedToClosedSubscheme_integralComponentAt_self _ p y
      (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq _ p y hx)
  · exact cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne _ p k x hy

/-- An integral closed subscheme `W ⊆ X × ℙ¹` not contained in the zero section, whose zero fibre
is the integral closed subscheme attached to a point `a` of relative dimension `r`, has relative
dimension `r + 1`. -/
private theorem relativeDimension_genericPoints_eq_of_zeroFiber_eq_integralComponentAt
    (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (I : (projectiveLineProduct p).IdealSheafData) [IsIntegral I.subscheme] {r : ℤ} {a : X}
    (ha : relativeDimension C.dimensionFunction p a = r)
    (hA : zeroFiber p I = integralComponentAt a)
    (h₀ : ¬ Set.range I.subschemeι ⊆ Set.range (zeroSection p)) :
    ∀ ξ : genericPoints I.subscheme,
      relativeDimension C.dimensionFunction (familyBase p I) ξ.1 = r + 1 :=
  relativeDimension_genericPoints_eq_of_schemeDeltaDimension_zeroFiber_eq C p I h₀ (by
    rw [hA]
    exact schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq _ p a ha)

/-- If an integral closed subscheme `W ⊆ X × ℙ¹` lies in neither section and its zero fibre is
the integral closed subscheme attached to a point `a` of relative dimension `r`, then the
fundamental `r`-cycle of its infinity fibre is rationally equivalent to `[a]`. -/
private theorem rationallyEquivalent_infinityFiber_pointCycle
    (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (I : (projectiveLineProduct p).IdealSheafData) [IsIntegral I.subscheme] {r : ℤ} {a : X}
    (ha : relativeDimension C.dimensionFunction p a = r)
    (hA : zeroFiber p I = integralComponentAt a)
    (h₀ : ¬ Set.range I.subschemeι ⊆ Set.range (zeroSection p))
    (hInf : ¬ Set.range I.subschemeι ⊆ Set.range (infinitySection p)) :
    RationallyEquivalent C p r
      (cycleAssociatedToClosedSubscheme C p (infinityFiber p I).subschemeι r)
      (pointCycle C p r a ha) := by
  rw [← cycleAssociatedToClosedSubscheme_integralComponentAt_eq_pointCycle C p a ha, ← hA]
  show _ - _ ∈ _
  have h := (rationalEquivalences C p r).neg_mem (fibreCycles_rationallyEquivalent C p r I
    (relativeDimension_genericPoints_eq_of_zeroFiber_eq_integralComponentAt C p I ha hA h₀)
    h₀ hInf)
  rwa [neg_sub] at h

variable (k W : Type u) [Field k] [AddCommGroup W] [Module k W]

/-- A closed subset of `𝐏(W) ×_k ℙ¹` dominating `ℙ¹` is not contained in the zero section. -/
private theorem not_subset_range_zeroSection_of_closure_image_eq_univ
    [FiniteDimensional k W] [Nontrivial W]
    {Z : Set (projectiveLineProduct (projectiveSpaceOfModuleToSpec k W))} (hZ : IsClosed Z)
    (hdom : closure ((pullback.snd (projectiveSpaceOfModuleToSpec k W)
      (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base '' Z) = Set.univ) :
    ¬ Z ⊆ Set.range (zeroSection (projectiveSpaceOfModuleToSpec k W)) := by
  intro h
  rw [(Scheme.Hom.isClosedMap _ _ hZ).closure_eq] at hdom
  obtain ⟨pt⟩ : Nonempty (Spec (.of k)) := inferInstance
  obtain ⟨w, hwC, hw⟩ : (lineInfinitySection (Spec (.of k))).base pt ∈
      (pullback.snd (projectiveSpaceOfModuleToSpec k W)
        (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base '' Z := by
    rw [hdom]
    trivial
  obtain ⟨x, hx⟩ := h hwC
  have hzx : (pullback.snd (projectiveSpaceOfModuleToSpec k W)
      (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base w =
      (lineZeroSection (Spec (.of k))).base ((projectiveSpaceOfModuleToSpec k W).base x) := by
    rw [← hx, ← Scheme.Hom.comp_apply, zeroSection_comp_snd, Scheme.Hom.comp_apply]
  exact Set.disjoint_left.mp (disjoint_range_lineZeroSection_lineInfinitySection _)
    ⟨(projectiveSpaceOfModuleToSpec k W).base x, rfl⟩ ⟨pt, hw.symm.trans hzx⟩

/-- Let `C ⊆ X ×_k ℙ¹` be integral of dimension `r + 1` and not contained in the infinity
section, whose infinity fibre `C_∞` satisfies `dim (C_∞ ∩ T) + d ≤ dim C_∞ + dim T`. Then every
component `Z` of `[C_∞]_r` satisfies `dim (Z ∩ T) + d ≤ dim Z + dim T`. -/
private theorem topologicalKrullDim_closure_inter_add_le_of_infinityFiber {X : Scheme.{u}}
    (p : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType p] [IsLocallyNoetherian X]
    {d : WithBot ℕ∞} {r : ℤ} (I : (projectiveLineProduct p).IdealSheafData)
    [IsIntegral I.subscheme]
    (hDim : ∀ ξ : genericPoints I.subscheme,
      relativeDimension (fieldChowSituation k).dimensionFunction (familyBase p I) ξ.1 = r + 1)
    (hInf : ¬ Set.range I.subschemeι ⊆ Set.range (infinitySection p)) (T : Set X)
    (hT : topologicalKrullDim ↥(((infinityFiber p I).support : Set X) ∩ T) + d ≤
      topologicalKrullDim ↥((infinityFiber p I).support : Set X) + topologicalKrullDim ↥T)
    {x : X}
    (hx : (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
      (infinityFiber p I).subschemeι r).1 x ≠ 0) :
    topologicalKrullDim ↥(closure ({x} : Set X) ∩ T) + d ≤
      topologicalKrullDim ↥(closure ({x} : Set X)) + topologicalKrullDim ↥T := by
  have hFcl := (infinityFiber p I).support.isClosed
  have hxF : x ∈ ((infinityFiber p I).support : Set X) := by
    have h := support_cycleAssociatedToClosedSubscheme_subset _ p
      (infinityFiber p I).subschemeι _ hx
    rwa [Scheme.IdealSheafData.range_subschemeι] at h
  have hxr : relativeDimension (fieldChowSituation k).dimensionFunction p x = r :=
    (mem_cyclesOfDimension_iff_forall_point _ _ _ _).mp
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
        (infinityFiber p I).subschemeι r).2 x hx
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, r = (m : ℤ) := ⟨r.toNat, (Int.toNat_of_nonneg
    (hxr ▸ relativeDimension_nonneg (fieldChowSituation k) (fun _ _ ↦ rfl) p x)).symm⟩
  have hFdim : topologicalKrullDim ↥((infinityFiber p I).support : Set X) ≤
      (m : WithBot ℕ∞) := by
    refine
      Stacks.Intersection.ProjectionFormula.topologicalKrullDim_le_of_forall_relativeDimension_le
        k p _ hFcl m fun y hy ↦ ?_
    rw [← Scheme.IdealSheafData.range_subschemeι] at hy
    obtain ⟨z, rfl⟩ := hy
    exact relativeDimension_le_of_schemeDeltaDimension_le _ p _
      (schemeDeltaDimension_infinityFiber_le (fieldChowSituation k) p I hDim hInf) z
  rw [topologicalKrullDim_closure_eq_of_relativeDimension_eq k p hxr]
  calc topologicalKrullDim ↥(closure ({x} : Set X) ∩ T) + d
      ≤ topologicalKrullDim ↥(((infinityFiber p I).support : Set X) ∩ T) + d :=
        add_le_add (topologicalKrullDim_le_of_subset (Set.inter_subset_inter_left _
          (hFcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hxF)))) le_rfl
    _ ≤ topologicalKrullDim ↥((infinityFiber p I).support : Set X) +
        topologicalKrullDim ↥T := hT
    _ ≤ (m : WithBot ℕ∞) + topologicalKrullDim ↥T := add_le_add hFdim le_rfl

/-- **Moving a prime cycle of `𝐏^n` off finitely many closed subvarieties.** Let `a` be a point of
the projective space `𝐏(W) = 𝐏^n` of a vector space over an algebraically closed field, of
dimension `r`, and let `T i ⊆ 𝐏(W)` be finitely many closed subvarieties. Then the prime cycle
`[a]` is rationally equivalent to an `r`-cycle `γ` every component `Z` of which satisfies
`dim (Z ∩ T i) + n ≤ dim Z + dim (T i)`, that is, intersects every `T i` properly. -/
public theorem exists_rationallyEquivalent_pointCycle_forall_intersectProperly [IsAlgClosed k]
    [FiniteDimensional k W] [Nontrivial W] {n : ℕ} (hW : Module.finrank k W = n + 1)
    (a : projectiveSpaceOfModule k W) {r : ℤ}
    (ha : relativeDimension (fieldChowSituation k).dimensionFunction
      (projectiveSpaceOfModuleToSpec k W) a = r)
    {ι : Type*} [Finite ι] (T : ι → Set (projectiveSpaceOfModule k W))
    (hTcl : ∀ i, IsClosed (T i)) (hTirr : ∀ i, IsIrreducible (T i)) :
    ∃ γ : CycleGroup (fieldChowSituation k) (projectiveSpaceOfModuleToSpec k W) r,
      RationallyEquivalent (fieldChowSituation k) (projectiveSpaceOfModuleToSpec k W) r γ
        (pointCycle (fieldChowSituation k) (projectiveSpaceOfModuleToSpec k W) r a ha) ∧
      ∀ x, γ.1 x ≠ 0 → ∀ i,
        topologicalKrullDim ↥(closure ({x} : Set (projectiveSpaceOfModule k W)) ∩ T i) +
            (n : WithBot ℕ∞) ≤
          topologicalKrullDim ↥(closure ({x} : Set (projectiveSpaceOfModule k W))) +
            topologicalKrullDim ↥(T i) := by
  classical
  set p : projectiveSpaceOfModule k W ⟶ (fieldChowSituation k).S :=
    projectiveSpaceOfModuleToSpec k W
  set A : IrreducibleCloseds (projectiveSpaceOfModule k W) :=
    ⟨closure ({a} : Set (projectiveSpaceOfModule k W)), isIrreducible_singleton.closure,
      isClosed_closure⟩
  -- the moving family of `A`, with `X = 𝐏(W)` itself
  obtain ⟨Cfam, hdom, hzero, -, hinf⟩ :=
    ProjectiveLineBridge.exists_movingFamily_projectiveLineProduct k W A Set.univ
      isClosed_univ.isLocallyClosed (IrreducibleSpace.isIrreducible_univ _)
      (by rw [Set.inter_univ,
        IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph])
      T (fun _ ↦ Set.subset_univ _) (fun i ↦ (hTcl i).preimage continuous_subtype_val) hTirr
  -- the family as an integral closed subscheme of `𝐏(W) ×_k ℙ¹`
  set g := Cfam.isIrreducible.genericPoint
  set I : (projectiveLineProduct p).IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal
      (⟨(Cfam : Set (projectiveLineProduct p)), Cfam.isClosed'⟩ : Closeds _) with hIdef
  have hIeq : I = integralComponentAt g := by
    rw [hIdef, integralComponentAt]
    congr 1
    ext1
    exact (Cfam.isIrreducible.closure_genericPoint Cfam.isClosed').symm
  have : IsIntegral I.subscheme := hIeq ▸ isIntegral_integralComponentAt g
  have hsuppI : (I.support : Set (projectiveLineProduct p)) = Cfam := by
    rw [hIdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  -- its zero fibre is the reduced closure of `a`
  have hA : zeroFiber p I = integralComponentAt a := by
    rw [hIdef, hzero, integralComponentAt]
    rfl
  have hza : (zeroSection p).base a ∈ (Cfam : Set (projectiveLineProduct p)) := by
    have h : a ∈ ((zeroFiber p I).support : Set (projectiveSpaceOfModule k W)) := by
      rw [hA, coe_support_integralComponentAt]
      exact subset_closure (Set.mem_singleton a)
    rwa [coe_support_zeroFiber, hsuppI] at h
  have hInf : ¬ Set.range I.subschemeι ⊆ Set.range (infinitySection p) := by
    intro h
    obtain ⟨y, hy⟩ := h (by rwa [Scheme.IdealSheafData.range_subschemeι, hsuppI])
    exact zeroSection_ne_infinitySection p a y hy.symm
  have h₀ : ¬ Set.range I.subschemeι ⊆ Set.range (zeroSection p) := by
    rw [Scheme.IdealSheafData.range_subschemeι, hsuppI]
    exact not_subset_range_zeroSection_of_closure_image_eq_univ k W Cfam.isClosed' hdom
  refine ⟨_, rationallyEquivalent_infinityFiber_pointCycle _ p I ha hA h₀ hInf,
    fun x hx i ↦ topologicalKrullDim_closure_inter_add_le_of_infinityFiber k p I
      (relativeDimension_genericPoints_eq_of_zeroFiber_eq_integralComponentAt _ p I ha hA h₀)
      hInf (T i) ?_ hx⟩
  have hm := hinf i
  rwa [topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hW, ← hsuppI,
    ← coe_support_infinityFiber] at hm

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
