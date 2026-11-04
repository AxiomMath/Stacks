module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaDimensionOne
public import StacksFrontier.LinearAlgebra.Matrix.PerfectComplexCharSeriesDetection

/-!
# The local term of the trace formula at a free stalk of rank one

Let `G` be a bounded below complex of sheaves of `R`-modules concentrated in degree `0`, and `y` a
rational point at which the stalk of `G` is a free `R`-module of rank one on which the geometric
Frobenius acts by right multiplication by `h`. Then the local term
`Tr(π_y | G_ȳ) ∈ R^♮` of the trace formula is the class of `h`. For the sheaf `𝒫 = π_* R` of a
Galois covering with group `H` and coefficients `R = ℤ/ℓ^M[H]` this computes the local terms of the
trace formula as the classes of the Frobenius elements of the covering, the trace side of the key
lemma of [Stacks, Tag 03UZ].

## Main results

* `Stacks.EtaleCohomology.perfectDerivedTrace_rationalPointStalkFrobenius_eq_q`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.FilteredDerived Stacks.CharSeriesTraceDetection

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (R : Type) [Ring R] {K : Type u} [Field K] [Fintype K] {X : Scheme.{u}}
  (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (p f : ℕ) [Fact p.Prime] [CharP Ω p]
  (hcard : Fintype.card K = p ^ f) (y : Spec (.of K) ⟶ X)

/-- The stalk complex of a complex concentrated in degree `0` is zero in the other degrees. -/
private theorem isZero_rationalPointStalkComplex_X_of_ne_zero {K : Type u} [Field K]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : Spec (.of K) ⟶ X)
    (G : CochainComplex.Plus (EtaleModules.{u, 0} R X)) (hz : ∀ i ≠ 0, IsZero (G.obj.X i))
    {i : ℤ} (hi : i ≠ 0) : IsZero ((rationalPointStalkComplex.{u, 0} R Ω y G).X i) :=
  Functor.map_isZero (rationalPointStalkFunctor.{u, 0} R Ω y) (hz i hi)

omit [Fintype K] in
/-- The stalk complex of a complex concentrated in degree `0` with a free stalk of rank one is a
bounded complex of finite projective modules. -/
theorem finiteProjectiveComplex_rationalPointStalkComplex_of_rankOne
    (G : CochainComplex.Plus (EtaleModules.{u, 0} R X)) (hz : ∀ i ≠ 0, IsZero (G.obj.X i))
    (ε : (rationalPointStalkFunctor.{u, 0} R Ω y).obj (G.obj.X 0) ≃ₗ[R] R) :
    finiteProjectiveComplex R (rationalPointStalkComplex.{u, 0} R Ω y G) := by
  have hzP := fun i (hi : i ≠ 0) => isZero_rationalPointStalkComplex_X_of_ne_zero R Ω y G hz hi
  refine ⟨⟨⟨0, (CochainComplex.isStrictlyGE_iff _ 0).mpr fun i hi => hzP i (by omega)⟩,
    ⟨0, (CochainComplex.isStrictlyLE_iff _ 0).mpr fun i hi => hzP i (by omega)⟩⟩, fun i => ?_⟩
  by_cases hi : i = 0
  · subst hi
    exact ⟨Module.Projective.of_equiv ε.symm, Module.Finite.equiv ε.symm⟩
  · have := ModuleCat.subsingleton_of_isZero (hzP i hi)
    exact ⟨Module.Projective.of_free, inferInstance⟩

/-- **The local term at a free stalk of rank one is the class of the Frobenius.** -/
theorem perfectDerivedTrace_rationalPointStalkFrobenius_eq_q
    (G : CochainComplex.Plus (EtaleModules.{u, 0} R X)) (hz : ∀ i ≠ 0, IsZero (G.obj.X i))
    (ε : (rationalPointStalkFunctor.{u, 0} R Ω y).obj (G.obj.X 0) ≃ₗ[R] R) (h : R)
    (hε : ∀ m, ε (((Stacks.Frobenius.geometricFrobeniusStalkFunctor (ModuleCat.{u + 1} R) Ω p f
      hcard y).app (G.obj.X 0)).hom m) = ε m * h)
    (hperf : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0} R Ω y G))) :
    perfectDerivedTrace R ⟨_, hperf⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} R Ω p f hcard y G)) =
      q R h := by
  have hP := finiteProjectiveComplex_rationalPointStalkComplex_of_rankOne R Ω y G hz ε
  rw [perfectDerivedTrace_eq_alternatingTrace R ⟨_, hperf⟩ _ _ hP (Iso.refl _) _
    (by rw [Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]),
    alternatingTrace_eq_of_isZero hP
      (fun i hi => isZero_rationalPointStalkComplex_X_of_ne_zero R Ω y G hz hi)]
  let : Module.Projective R ((rationalPointStalkFunctor.{u, 0} R Ω y).obj (G.obj.X 0)) :=
    (hP.2 0).1
  let : Module.Finite R ((rationalPointStalkFunctor.{u, 0} R Ω y).obj (G.obj.X 0)) := (hP.2 0).2
  exact projectiveModuleTrace_eq_q_of_linearEquiv ε _ h hε

end Stacks.EtaleCohomology
