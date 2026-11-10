module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroCyclesSeparablePoints
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardRationalEquivalence.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf

/-!
# Stacks 0FH5: reduction to an integral scheme with an ample invertible module

Let `X` be smooth, proper and H-projective over a field `k`, and let `x` be a closed point. The
connected component `X₀` of `x` is open and closed in `X` and, as an open subscheme, integral;
it is smooth and proper over `k`, and the pullback of `𝒪(1)` along `X₀ ⟶ X ⟶ ℙⁿ_k` is an ample
invertible module on it. Closed points and residue fields are unchanged along the closed immersion
`X₀ ⟶ X`, and proper pushforward along it respects rational equivalence and carries the class of
`x` in `A_0(X₀)` to the class of `x` in `A_0(X)`. So the per-point statement of the Bertini
argument of Stacks 0FH5 for integral smooth proper schemes with an ample invertible module implies
it for all smooth projective schemes over `k`.

## Main results

* `Stacks.Chow.hasSeparableResidueField_comp_iff` — residue fields, hence separability of them,
  are unchanged along a preimmersion.
* `Stacks.Chow.properPushforward_integralComponentAt_of_isClosedImmersion` — proper pushforward
  along a closed immersion carries the prime cycle of a point to the prime cycle of its image.
* `Stacks.Chow.separablePointComplementaryCycles_of_integralComplementaryCycles` — the reduction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Residue fields along a preimmersion -/

/-- A preimmersion induces an isomorphism on residue fields. -/
theorem bijective_residueFieldMap_of_isPreimmersion {X Z : Scheme.{u}} (g : Z ⟶ X)
    [IsPreimmersion g] (z : Z) : Function.Bijective (g.residueFieldMap z).hom := by
  have h : Function.Surjective (g.stalkMap z ≫ Z.residue z).hom :=
    IsLocalRing.residue_surjective.comp (SurjectiveOnStalks.stalkMap_surjective g z)
  rw [← Scheme.residue_residueFieldMap] at h
  exact ⟨(g.residueFieldMap z).hom.injective,
    Function.Surjective.of_comp (f := (g.residueFieldMap z).hom) (g := (X.residue (g z)).hom) h⟩

/-- **Separable residue fields along a preimmersion.** For a preimmersion `g : Z ⟶ X` of schemes
over `k`, the residue field of `Z` at `z` is separable over `k` exactly when the residue field of
`X` at `g z` is. In particular this applies to open and to closed immersions. -/
theorem hasSeparableResidueField_comp_iff (k : Type u) [Field k] {X Z : Scheme.{u}}
    (g : Z ⟶ X) [IsPreimmersion g] (p : X ⟶ (fieldChowSituation k).S) (z : Z) :
    HasSeparableResidueField k (g ≫ p) z ↔ HasSeparableResidueField k p (g z) := by
  unfold HasSeparableResidueField
  let _ : Algebra k (X.residueField (g z)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation (g z)).hom.toAlgebra
  let _ : Algebra k (Z.residueField z) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (g ≫ p).appTop ≫ Z.Γevaluation z).hom.toAlgebra
  refine (Algebra.IsSeparable.iff_of_equiv_equiv (RingEquiv.refl k)
    (RingEquiv.ofBijective (g.residueFieldMap z).hom
      (bijective_residueFieldMap_of_isPreimmersion g z)) ?_).symm
  ext a
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ (g ≫ p).appTop ≫ Z.Γevaluation z).hom a =
    (g.residueFieldMap z).hom
      (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation (g z)).hom a)
  rw [← CommRingCat.comp_apply, Category.assoc, Category.assoc,
    Scheme.Γevaluation_naturality, Scheme.Hom.comp_appTop]
  rfl

/-! ### The prime cycle of a point along a closed immersion -/

/-- **Proper pushforward of the prime cycle of a point along a closed immersion.** For a closed
immersion `i : Z ⟶ X` over the base, `i_*[z] = [i z]`. -/
theorem properPushforward_integralComponentAt_of_isClosedImmersion (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ) (k : ℤ)
    (z : Z) :
    properPushforward C sZ sX i hi k
        (cycleAssociatedToClosedSubscheme C sZ (integralComponentAt z).subschemeι k) =
      cycleAssociatedToClosedSubscheme C sX (integralComponentAt (i z)).subschemeι k := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  by_cases hy : y ∈ Set.range i.base
  · obtain ⟨w, rfl⟩ := hy
    rw [properPushforward_apply_image_of_isClosedImmersion]
    by_cases hw : w = z
    · subst hw
      have hdim : relativeDimension C.dimensionFunction sZ w =
          relativeDimension C.dimensionFunction sX (i w) := by
        rw [← hi, relativeDimension_comp_closedImmersion]
      by_cases hk : relativeDimension C.dimensionFunction sZ w = k
      · rw [cycleAssociatedToClosedSubscheme_integralComponentAt_self C sZ w
          (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C sZ w hk),
          cycleAssociatedToClosedSubscheme_integralComponentAt_self C sX (i w)
          (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C sX (i w)
            (hdim ▸ hk))]
      · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero C sZ _ k w
          (fun ⟨_, _, h⟩ ↦ hk h),
          cycleAssociatedToClosedSubscheme_apply_eq_zero C sX _ k (i w)
          (fun ⟨_, _, h⟩ ↦ hk (hdim.trans h))]
    · rw [cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C sZ k z hw,
        cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C sX k (i z)
          (fun h ↦ hw (i.isClosedEmbedding.injective h))]
  · rw [properPushforward_apply_of_notMem_range C sZ sX i hi k _ hy,
      cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C sX k (i z)
        (fun h ↦ hy ⟨z, h.symm⟩)]

/-! ### The reduction -/

/-- For every integral scheme `X` smooth and proper over `k` with an ample invertible module and
every closed point `x` of `X`, there are zero cycles `Z` and `Z'` on `X`, supported on closed
points with separable residue field over `k`, with `[x] + [Z] = [Z']` in `A_0(X)`. -/
def IntegralComplementaryCycles (k : Type u) [Field k] : Prop :=
  ∀ {X : Scheme.{u}} (p : X ⟶ (fieldChowSituation k).S) [Smooth p] [IsProper p] [IsIntegral X]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L], Stacks.Ample.IsAmple X L →
    ∀ x : X, IsClosed ({x} : Set X) →
      ∃ Z Z' : CycleGroup (fieldChowSituation k) p 0,
        (∀ y : X, Z.1 y ≠ 0 → IsClosed ({y} : Set X) ∧ HasSeparableResidueField k p y) ∧
        (∀ y : X, Z'.1 y ≠ 0 → IsClosed ({y} : Set X) ∧ HasSeparableResidueField k p y) ∧
        QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) p 0)
              (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
                (integralComponentAt x).subschemeι 0) +
            QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) p 0) Z =
          QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) p 0) Z'

/-- Proper pushforward along a closed immersion of schemes over `k` carries a zero cycle supported
on closed points with separable residue field to another such cycle. -/
theorem properPushforward_supported_of_isClosedImmersion (k : Type u) [Field k]
    {X Y : Scheme.{u}} (p : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType p]
    (g : Y ⟶ X) [IsClosedImmersion g] [LocallyOfFiniteType (g ≫ p)]
    (Z : CycleGroup (fieldChowSituation k) (g ≫ p) 0)
    (hZ : ∀ y : Y, Z.1 y ≠ 0 → IsClosed ({y} : Set Y) ∧ HasSeparableResidueField k (g ≫ p) y)
    (x : X) (hx : (properPushforward (fieldChowSituation k) (g ≫ p) p g rfl 0 Z).1 x ≠ 0) :
    IsClosed ({x} : Set X) ∧ HasSeparableResidueField k p x := by
  by_cases hmem : x ∈ Set.range g.base
  · obtain ⟨y, rfl⟩ := hmem
    rw [properPushforward_apply_image_of_isClosedImmersion] at hx
    obtain ⟨hcl, hsep⟩ := hZ y hx
    refine ⟨?_, (hasSeparableResidueField_comp_iff k g p y).mp hsep⟩
    rw [← Set.image_singleton]
    exact g.isClosedEmbedding.isClosedMap _ hcl
  · exact absurd (properPushforward_apply_of_notMem_range _ _ _ g rfl 0 Z hmem) hx

/-- **Reduction to integral schemes with an ample invertible module.** If
`IntegralComplementaryCycles k` holds, then so does `SeparablePointComplementaryCycles k`: the
statement for integral smooth proper schemes over `k` carrying an ample invertible module implies
it for every smooth projective scheme over `k`. -/
theorem separablePointComplementaryCycles_of_integralComplementaryCycles (k : Type u) [Field k]
    (h : IntegralComplementaryCycles.{u} k) : SeparablePointComplementaryCycles.{u} k := by
  intro X p _ _ hproj x hx
  have hopen : IsOpen (connectedComponent x) := isOpen_connectedComponent_of_smooth p x
  let U : X.Opens := ⟨connectedComponent x, hopen⟩
  have : IsIntegral U.toScheme := isIntegral_connectedComponent_of_smooth p x hopen
  have : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact isClosed_connectedComponent)
  obtain ⟨n, i, hi, -⟩ := hproj
  have : IsClosedImmersion (U.ι ≫ i) := inferInstance
  have hL := Stacks.AmplePullback.isAmple_modulePullback_of_isClosedImmersion (U.ι ≫ i)
    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (fieldChowSituation k).S)
    (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf n _)
  let x₀ : U.toScheme := ⟨x, mem_connectedComponent⟩
  have hcl₀ : IsClosed ({x₀} : Set U.toScheme) :=
    U.ι.isClosedEmbedding.isClosed_iff_image_isClosed.2 (by rwa [Set.image_singleton])
  obtain ⟨Z, Z', hZ, hZ', heq⟩ := h (U.ι ≫ p) _ hL x₀ hcl₀
  refine ⟨properPushforward (fieldChowSituation k) (U.ι ≫ p) p U.ι rfl 0 Z,
    properPushforward (fieldChowSituation k) (U.ι ≫ p) p U.ι rfl 0 Z',
    properPushforward_supported_of_isClosedImmersion k p U.ι Z hZ,
    properPushforward_supported_of_isClosedImmersion k p U.ι Z' hZ', ?_⟩
  have := congrArg (chowPushforwardOfIsClosedImmersion (fieldChowSituation k) (U.ι ≫ p) p U.ι
    rfl 0) heq
  rwa [map_add, chowPushforwardOfIsClosedImmersion_mk, chowPushforwardOfIsClosedImmersion_mk,
    chowPushforwardOfIsClosedImmersion_mk,
    properPushforward_integralComponentAt_of_isClosedImmersion] at this

end Stacks.Chow

end
