module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactificationChangeTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.OpenClosedPointReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RationalPointsDegreeOne

/-!
# The trace formula along a proper morphism, from the base and the fibres

Let `π : W' ⟶ W` be a proper morphism of schemes of finite type over a finite field `k`, `Λ` a
finite ring (possibly noncommutative), `C` a bounded below complex on `W'_étale` with perfect
stalks and `C ⟶ T` an injective resolution, so that `π_* T = Rπ_* C`. If the trace formula holds
for `π_* T` on `W` and for the restriction of `C` to every fibre `W'_y` over a rational point
`y ∈ W(k)`, then it holds for `C` on `W'`:

`T''(W', C) = T''(W, Rπ_* C) = ∑_{y ∈ W(k)} Tr(π_y | (Rπ_* C)_ȳ)
  = ∑_{y ∈ W(k)} T''(W'_y, C|_{W'_y}) = ∑_{y ∈ W(k)} ∑_{x ∈ W'_y(k)} Tr(π_x | C_x̄)
  = ∑_{x ∈ W'(k)} Tr(π_x | C_x̄)`.

The first step is the Leray step along `π`
(`perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage_of_isProper`),
the third the comparison of the local term of `Rπ_* C` at `y` with the trace on the fibre, by
proper base change
(`Stacks.EtaleCohomology.perfectDerivedTrace_rationalPointStalkFrobenius_directImage_eq_fibre`),
and the last the decomposition of `W'(k)` along `π`. This is how the proof of
[Stacks, Tag 03V3] reduces the trace formula to the base and to curves.

The standard model `HasDerivedCategory.standard` is used because the traced objects are defined
there.

## Main results

* `Stacks.EtaleCohomology.sum_rationalPoints_rationalFibre`: `W'(k)` is the disjoint union of the
  `W'_y(k)`, `y ∈ W(k)`.
* `Stacks.EtaleCohomology.cohomologicalTraceFormula_of_isProper_of_rationalFibre`.

## References

* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
  Preadditive.preadditiveHasZeroMorphisms

section Reindex

variable {k : Type u} [Field k] {W' W : Over (Spec (.of k))} (π : W' ⟶ W)

open scoped Classical in
/-- **`W'(k)` is the disjoint union of the rational points of the fibres** of `π : W' ⟶ W` over
the rational points of `W`: a function on `W'(k)` sums to the sum over `y ∈ W(k)` of its sums over
the rational points of the fibre `W'_y`, read in `W'` through the first projection. -/
theorem sum_rationalPoints_rationalFibre {M : Type*} [AddCommMonoid M]
    [Fintype (rationalPoints W.hom)] [Fintype (rationalPoints W'.hom)]
    [∀ y : rationalPoints W.hom, Fintype (rationalPoints (rationalFibre π y.1).hom)]
    (φ : (Spec (.of k) ⟶ W'.left) → M) :
    ∑ y : rationalPoints W.hom, ∑ x : rationalPoints (rationalFibre π y.1).hom,
        φ (x.1 ≫ pullback.fst π.left y.1) =
      ∑ x : rationalPoints W'.hom, φ x.1 := by
  let r : rationalPoints W'.hom → rationalPoints W.hom := fun x =>
    ⟨x.1 ≫ π.left, by rw [Category.assoc, Over.w π]; exact x.2⟩
  rw [← Finset.sum_fiberwise Finset.univ r (fun x => φ x.1)]
  refine Fintype.sum_congr _ _ fun y => ?_
  have hs (a : rationalPoints (rationalFibre π y.1).hom) :
      a.1 ≫ pullback.snd π.left y.1 = 𝟙 _ := a.2
  have key (a : rationalPoints (rationalFibre π y.1).hom) :
      a.1 ≫ pullback.fst π.left y.1 ≫ π.left = y.1 := by
    rw [pullback.condition, ← Category.assoc, hs a, Category.id_comp]
  refine Finset.sum_bij'
    (fun a _ => ⟨a.1 ≫ pullback.fst π.left y.1, by
      rw [Category.assoc, ← Over.w π, reassoc_of% key a]; exact y.2⟩)
    (fun b hb => ⟨pullback.lift b.1 (𝟙 _) (by
      rw [Category.id_comp]
      exact congrArg Subtype.val (Finset.mem_filter.1 hb).2), pullback.lift_snd _ _ _⟩)
    (fun a _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, Subtype.ext (by
      show (a.1 ≫ pullback.fst π.left y.1) ≫ π.left = y.1
      rw [Category.assoc]
      exact key a)⟩)
    (fun b _ => Finset.mem_univ _)
    (fun a _ => Subtype.ext (pullback.hom_ext (pullback.lift_fst _ _ _)
      ((pullback.lift_snd _ _ _).trans (hs a).symm)))
    (fun b _ => Subtype.ext (pullback.lift_fst _ _ _))
    (fun a _ => rfl)

end Reindex

section Fibration

variable (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k] (kbar : Type u)
  [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  [CharP kbar p] (hcard : Fintype.card k = p ^ q)
  {W' W : Over (Spec (.of k))} (π : W' ⟶ W) [IsProper π.left]

/-- **The trace formula along a proper morphism, from the base and the fibres.** Let
`π : W' ⟶ W` be proper over `k` with `W` of finite type, `C` a bounded below complex on `W'_étale`
with perfect stalks and `ψ : C ⟶ T` an injective resolution, so that `π_* T = Rπ_* C` (assumed to
have perfect stalks). If the trace formula holds for `π_* T` on `W` and for the restriction of `C`
to the fibre `W'_y` over every rational point `y ∈ W(k)`, it holds for `C` on `W'`. -/
theorem cohomologicalTraceFormula_of_isProper_of_rationalFibre [QuasiCompact W.hom]
    [LocallyOfFiniteType W.hom]
    (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ W'.left)) (hC : HasPerfectStalks Λ C)
    (T : CochainComplex.Plus (EtaleModules.{u, 0} Λ W'.left)) (ψ : C ⟶ T) (hψ : QuasiIso ψ.hom)
    (hT : ∀ n, Injective (T.obj.X n))
    (hD : HasPerfectStalks Λ ((etaleModuleDirectImage.{u, 0} Λ π.left).mapCochainComplexPlus.obj T))
    (hbase : CohomologicalTraceFormula Λ kbar p q hcard W
      ((etaleModuleDirectImage.{u, 0} Λ π.left).mapCochainComplexPlus.obj T) hD)
    (hfib : ∀ y : rationalPoints W.hom, CohomologicalTraceFormula Λ kbar p q hcard
      (rationalFibre π y.1)
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst π.left y.1)).mapCochainComplexPlus.obj C)
      (isPerfect_stalk_inverseImage Λ (pullback.fst π.left y.1) C hC)) :
    CohomologicalTraceFormula Λ kbar p q hcard W' C hC := by
  have : ∀ n, Injective (T.obj.X n) := hT
  obtain ⟨hpB, htB⟩ := hbase
  have hpT := (isPerfect_frobeniusRestriction_directImage_iff_of_isProper Λ kbar π T).1 hpB
  have hpC := isPerfect_frobeniusRestriction_of_quasiIso Λ kbar (Y := W') ψ.hom hψ hpT
  refine ⟨hpC, fun {_} => ?_⟩
  obtain ⟨_, htC⟩ := perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_quasiIso Λ kbar
    p q hcard (Y := W') ψ.hom hψ hpC
  have hL := perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage_of_isProper Λ kbar
    p q hcard π T hpB
  have := finite_rationalPoints W.hom
  have : Fintype (rationalPoints W.hom) := Fintype.ofFinite _
  have : ∀ y : rationalPoints W.hom, Fintype (rationalPoints (rationalFibre π y.1).hom) :=
    fun y =>
      have : LocallyOfFiniteType (rationalFibre π y.1).hom :=
        set_option backward.isDefEq.respectTransparency.types false in
        MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) π.left y.1
          (IsProper.toLocallyOfFiniteType (f := π.left))
      have : QuasiCompact (rationalFibre π y.1).hom :=
        inferInstanceAs (QuasiCompact (pullback.snd π.left y.1))
      have := finite_rationalPoints (rationalFibre π y.1).hom
      Fintype.ofFinite _
  have hy (y : rationalPoints W.hom) :
      perfectDerivedTrace.{0, u + 1} Λ ⟨_, hD (rationalGeometricPoint kbar y.1)⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard y.1
            ((etaleModuleDirectImage.{u, 0} Λ π.left).mapCochainComplexPlus.obj T))) =
        ∑ x : rationalPoints (rationalFibre π y.1).hom,
          perfectDerivedTrace.{0, u + 1} Λ
            ⟨_, hC (rationalGeometricPoint kbar (x.1 ≫ pullback.fst π.left y.1))⟩
            (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard
              (x.1 ≫ pullback.fst π.left y.1) C)) := by
    have := etaleModules_enoughInjectives.{u, 0} Λ W'.left
    obtain ⟨hF, hSF⟩ := perfectDerivedTrace_rationalPointStalkFrobenius_directImage_eq_fibre π
      y.1 Λ kbar p q hcard T hD
    obtain ⟨hpy, hty⟩ := hfib y
    obtain ⟨_, htr⟩ := perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_map_eq_of_rightAcyclic
      Λ kbar p q hcard (Y := rationalFibre π y.1)
      (F := etaleModuleInverseImage.{u, 0} Λ (pullback.fst π.left y.1)) ψ hψ
      (fun n => Functor.rightAcyclic_of_exact _ _) (fun n => Functor.rightAcyclic_of_exact _ _) hF
    refine hSF.trans (htr.symm.trans (hty.trans (Fintype.sum_congr _ _ fun x => ?_)))
    exact perfectDerivedTrace_rationalPointStalkFrobenius_inverseImage Λ (pullback.fst π.left y.1)
      kbar x.1 _ rfl p q hcard C _ _
  exact htC.trans (hL.symm.trans (htB.trans ((Fintype.sum_congr _ _ hy).trans
    (sum_rationalPoints_rationalFibre π (fun x => perfectDerivedTrace.{0, u + 1} Λ
      ⟨_, hC (rationalGeometricPoint kbar x)⟩
      (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard x C)))))))

end Fibration

end Stacks.EtaleCohomology

end
