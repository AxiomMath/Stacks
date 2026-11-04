module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClasses.FlatPullbackInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackMeromorphicSection
public import StacksCore.Tactic.StacksAttribute

/-!
# The component case of Stacks 02SS for an invertible module

Let `X` and `X'` be schemes locally of finite type over the base scheme `S` of chapter 42 of the
Stacks Project, let `f : X' ⟶ X` be flat of relative dimension `r` and let `L` be an invertible
module on `X`. This file collects the geometry of the inverse image `f^{-1}(W)` of the integral
closed subscheme `W = closure {x}` through a point `x` of relative dimension `k + 1` that the
component case of [Stacks, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS) needs.

## Main results

* `Stacks.Chow.exists_iso_integralComponentAt_comp` — the integral closed subscheme through a
  point of a closed subscheme is isomorphic to the one through its image.
* `Stacks.Chow.base_genericPoint_irreducibleComponents_comap` — the generic point of an
  irreducible component of `f^{-1}(W)` lies over the generic point of `W`.
* `Stacks.Chow.exists_irreducibleComponents_of_flatPullbackWeight_ne_zero` — a point with
  nonzero flat pullback multiplicity over `x` is the generic point of an irreducible component of
  `f^{-1}(closure {x})`.
* `Stacks.Chow.pullbackCompIso` — the two spellings of the restriction of `L` to an irreducible
  component of `f^{-1}(W)`, one through the component of `X'` and one through `f^{-1}(W)`, are
  isomorphic.

## References

* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 02R8](https://stacks.math.columbia.edu/tag/02R8)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The integral component of a point of a closed subscheme -/

/-- The integral closed subscheme through a point of a closed subscheme `Z ⊆ X'` is isomorphic to
the integral closed subscheme through its image, compatibly with the two closed immersions: the
two have the same ideal sheaf, by `Stacks.Chow.map_integralComponentAt`. -/
theorem exists_iso_integralComponentAt_comp {Z X' : Scheme.{u}} (ι : Z ⟶ X')
    [IsClosedImmersion ι] (z : Z) :
    ∃ e : (integralComponentAt z).subscheme ≅ (integralComponentAt (ι.base z)).subscheme,
      e.hom ≫ (integralComponentAt (ι.base z)).subschemeι =
        (integralComponentAt z).subschemeι ≫ ι := by
  refine exists_iso_of_ker_eq ((integralComponentAt z).subschemeι ≫ ι)
    (integralComponentAt (ι.base z)).subschemeι ?_
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.ker_subschemeι, map_integralComponentAt]

/-! ### Generic points of the irreducible components of an inverse image -/

/-- **Stacks 02R8 on the inverse image of an integral closed subscheme.** Along a flat morphism
`f : X' ⟶ X`, the generic point of an irreducible component of the scheme-theoretic inverse image
of an integral closed subscheme `W ⊆ X` lies over the generic point of `W`. -/
theorem base_genericPoint_irreducibleComponents_comap {X' X : Scheme.{u}} (f : X' ⟶ X)
    [LocallyOfFiniteType f] [Flat f] (W : X.IdealSheafData) [IsIntegral W.subscheme]
    (V : irreducibleComponents (W.comap f).subscheme) :
    f.base ((W.comap f).subschemeι.base V.2.1.genericPoint) =
      W.subschemeι.base (genericPoint W.subscheme) := by
  have := flat_comapRestrict W f
  have := isIntegral_integralComponentAt V.2.1.genericPoint
  have := isDominant_subschemeι_integralComponentAt_comp (comapRestrict W f) V
  have h1 : ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ comapRestrict W f).base
      (genericPoint (integralComponentAt V.2.1.genericPoint).subscheme) =
      genericPoint W.subscheme :=
    Stacks.Divisors.base_genericPoint_of_isDominant _
  have h2 : (comapRestrict W f).base V.2.1.genericPoint = genericPoint W.subscheme := by
    rw [← h1, Scheme.Hom.comp_apply]
    exact congrArg (comapRestrict W f).base
      (subschemeι_genericPoint_integralComponentAt V.2.1.genericPoint).symm
  have h3 : f.base ((W.comap f).subschemeι.base V.2.1.genericPoint) =
      W.subschemeι.base ((comapRestrict W f).base V.2.1.genericPoint) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, comapRestrict_subschemeι]
  rw [h3, h2]

/-- A point of `X'` lying over `x` with nonzero flat pullback multiplicity is the image of the
generic point of an irreducible component of `f^{-1}(closure {x})`: the multiplicity is a
coefficient of the fundamental cycle of that inverse image. -/
theorem exists_irreducibleComponents_of_flatPullbackWeight_ne_zero (C : ChowSituation.{u})
    {X' X : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (f : X' ⟶ X) (x : X) (j : ℤ)
    {x' : X'} (hx' : f.base x' = x) (hw : flatPullbackWeight C sX' f j x' ≠ 0) :
    ∃ V : irreducibleComponents ((integralComponentAt x).comap f).subscheme,
      ((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint = x' := by
  classical
  subst hx'
  have hw' : closedSubschemeCycleCoeff C sX'
      ((integralComponentAt (f.base x')).comap f).subschemeι j x' ≠ 0 := hw
  unfold closedSubschemeCycleCoeff at hw'
  split at hw'
  · rename_i h
    obtain ⟨ξ, hξ, -⟩ := h
    refine ⟨genericPoints.component ξ, ?_⟩
    have hgen : (genericPoints.component ξ).2.1.genericPoint = ξ.1 :=
      ((genericPoints.component ξ).2.1.isGenericPoint_genericPoint
        (isClosed_of_mem_irreducibleComponents _ (genericPoints.component ξ).2)).eq
        (genericPoints.isGenericPoint ξ)
    rw [hgen]
    exact hξ
  · exact absurd rfl hw'

/-! ### The two spellings of a restricted module -/

/-- Two factorizations `a ≫ b = c ≫ d` of one morphism to `T` give isomorphic iterated pullbacks
of a module on `T`, by the composition isomorphism of
`AlgebraicGeometry.Scheme.Modules.pullback`. -/
def pullbackCompIso {A Y Z T : Scheme.{u}} (a : A ⟶ Y) (b : Y ⟶ T) (c : A ⟶ Z) (d : Z ⟶ T)
    (h : a ≫ b = c ≫ d) (L : T.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj L) ≅
      (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback d).obj L) :=
  (Scheme.Modules.pullbackComp a b).app L ≪≫ (Scheme.Modules.pullbackCongr h).app L ≪≫
    ((Scheme.Modules.pullbackComp c d).app L).symm

/-! ### The cap product cycle of the flat pullback of a fundamental cycle -/

section Extend

variable (C : ChowSituation.{u}) {X' X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (r : ℕ)
  (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)
  (chern' : FirstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ)))
  (hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1) (x : X)

/-- The cap product cycle of the flat pullback of the fundamental cycle of the integral closed
subscheme through `x`, read at a point of `X'`: it is the sum over the fibre of `f` above `x` of
the component cycles of `X'`, weighted by the flat pullback multiplicities. This is the left hand
side of the component case of Stacks 02SS. -/
theorem extendCycleGroup_flatPullback_cycleAssociatedToClosedSubscheme_apply
    (hx : relativeDimension C.dimensionFunction p x = k + 1) (y' : X') :
    ((firstChernCapRule C (f ≫ p) (k + (r : ℤ)) chern').extendCycleGroup
        (hcast ▸ flatPullback C (f ≫ p) p f rfl r hf (k + 1)
          (cycleAssociatedToClosedSubscheme C p (integralComponentAt x).subschemeι (k + 1)))).1 y'
      = ∑ᶠ x' ∈ f.base ⁻¹' {x},
          flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
            (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ)) chern' x').1 y' := by
  set R' := firstChernCapRule C (f ≫ p) (k + (r : ℤ)) chern' with hR'
  set α₀ := cycleAssociatedToClosedSubscheme C p (integralComponentAt x).subschemeι (k + 1)
    with hα₀
  set γ := flatPullback C (f ≫ p) p f rfl r hf (k + 1) α₀ with hγ
  have hone : α₀.1 x = 1 :=
    cycleAssociatedToClosedSubscheme_integralComponentAt_self C p x
      (schemeDeltaDimension_integralComponentAt_of_eq C p hx)
  have hzero : ∀ z : X, z ≠ x → α₀.1 z = 0 := fun z hz ↦
    cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C p (k + 1) x hz
  have h0 : (R'.extendCycleGroup (hcast ▸ γ)).1 y' =
      ∑ᶠ x' : X', γ.1 x' *
        (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ)) chern' x').1 y' := by
    rw [show (R'.extendCycleGroup (hcast ▸ γ)).1 y' =
        R'.toComponentRule.extendCoeff (hcast ▸ γ : CycleGroup C (f ≫ p) _).1 y' from rfl,
      val_cycleGroup_cast C (f ≫ p) hcast γ]
    rfl
  rw [h0, ← finsum_mem_univ,
    finsum_mem_inter_support_eq' _ Set.univ (f.base ⁻¹' {x}) ?_]
  · refine finsum_mem_congr rfl fun x' hx' ↦ ?_
    have hbase : f.base x' = x := hx'
    rw [hγ, flatPullback_apply, hbase, hone, one_mul]
  · intro x' hx'
    refine ⟨fun _ ↦ ?_, fun _ ↦ Set.mem_univ x'⟩
    by_contra hne
    refine hx' ?_
    have hγ0 : γ.1 x' = 0 := by
      rw [hγ, flatPullback_apply, hzero (f.base x') (by exact hne), zero_mul]
    change γ.1 x' * (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ)) chern' x').1 y' = 0
    rw [hγ0, zero_mul]

/-- The cap product cycle of the component case of Stacks 02SS is supported on the inverse image
`f^{-1}(closure {x})`: a contributing point of `X'` has nonzero flat pullback multiplicity over
`x`, hence specializes from the generic point of an irreducible component of that inverse
image. -/
theorem extendCycleGroup_eq_zero_of_notMem_range
    (hx : relativeDimension C.dimensionFunction p x = k + 1) {y' : X'}
    (hy' : y' ∉ Set.range ((integralComponentAt x).comap f).subschemeι.base) :
    ((firstChernCapRule C (f ≫ p) (k + (r : ℤ)) chern').extendCycleGroup
        (hcast ▸ flatPullback C (f ≫ p) p f rfl r hf (k + 1)
          (cycleAssociatedToClosedSubscheme C p (integralComponentAt x).subschemeι (k + 1)))).1 y'
      = 0 := by
  rw [extendCycleGroup_flatPullback_cycleAssociatedToClosedSubscheme_apply C p f r hf k chern'
    hcast x hx y']
  refine finsum_mem_eq_zero_of_forall_eq_zero fun x' hx' ↦ ?_
  by_contra hne
  obtain ⟨V, hV⟩ := exists_irreducibleComponents_of_flatPullbackWeight_ne_zero C (f ≫ p) f x
    (k + 1 + (r : ℤ)) (by exact hx') (left_ne_zero_of_mul hne)
  refine hy' ?_
  have hmem : y' ∈ closure ({x'} : Set X') :=
    (firstChernCapRule C (f ≫ p) (k + (r : ℤ)) chern').toComponentRule.mem_closure_of_apply_ne_zero
      x' y' (right_ne_zero_of_mul hne)
  have hclosed : IsClosed (Set.range ((integralComponentAt x).comap f).subschemeι.base) :=
    ((integralComponentAt x).comap f).subschemeι.isClosedEmbedding.isClosed_range
  refine hclosed.closure_subset_iff.2 ?_ hmem
  rw [Set.singleton_subset_iff, ← hV]
  exact ⟨V.2.1.genericPoint, rfl⟩

end Extend

/-! ### Local finiteness of the irreducible components -/

/-- On a locally Noetherian scheme only finitely many irreducible components pass through a given
point. -/
@[ega "0 14.2.6" "(i), special case", ega "IV 13.2.6" "more general"]
theorem finite_irreducibleComponents_mem {Z : Scheme.{u}} [IsLocallyNoetherian Z] (z : Z) :
    {V : irreducibleComponents Z | z ∈ (V : Set Z)}.Finite := by
  have hcomp : LocallyFinite fun V : irreducibleComponents Z ↦ (V : Set Z) := by
    simpa using AlgebraicGeometry.locallyFinite_irreducibleComponents_image (𝟙 Z)
  exact hcomp.point_finite z

/-- The support of the integral closed subscheme attached to the generic point of an irreducible
component is that component. -/
theorem coe_support_integralComponentAt_genericPoint {Z : Scheme.{u}}
    (V : irreducibleComponents Z) :
    ((integralComponentAt V.2.1.genericPoint).support : Set Z) = (V : Set Z) := by
  rw [coe_support_integralComponentAt]
  exact (V.2.1.isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents _ V.2)).def

end Stacks.Chow

end
