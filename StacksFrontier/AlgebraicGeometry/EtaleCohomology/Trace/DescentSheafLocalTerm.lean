module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DescentSheafStalkRationalPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RankOneLocalTerm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SheafFrobeniusMatrices
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit

/-!
# The local terms of the trace formula for the regular descent sheaf of a Galois covering

Let `C` be an étale Galois covering of `X` with group `H`, `R` a ring and `𝒫` a sheaf of
`R`-modules on `X` isomorphic to the descent sheaf of a free `R`-module `N` of rank one on which
`H` acts by right multiplications `x ↦ x ⬝ τ(g)`. Over an extension `k'` of degree `m` of the
finite base field, at a rational point `s` of `X ×_k k'` over a closed point `x` of degree
`d ∣ m`, the local term of the trace formula for the inverse image of `𝒫` is the class of
`τ(g_x ^ (m / d))` in `R^♮`, where `g_x` is the Frobenius element of the covering at `x`. Summed
over the rational points this is `∑_{deg x ∣ m} deg x · [τ(g_x ^ (m / deg x))]`, the trace side of
the key lemma of [Stacks, Tag 03UZ].

## Main results

* `Stacks.EtaleCohomology.perfectDerivedTrace_rationalPointStalkFrobenius_descentSheaf`: the local
  term at a rational point of `X ×_k k'` of the inverse image of `𝒫` is the class of `τ(g_x ^ n)`
  in `R^♮`, where `#k' = #κ(x) ^ n`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius CategoryTheory.FilteredDerived Stacks.CharSeriesTraceDetection

universe u w

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (R : Type) [Ring R] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (k' : Type u) [Field k'] [Fintype k'] [Algebra k k']
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k' kbar] (p qq : ℕ) [Fact p.Prime]
  [CharP kbar p] (hcard' : Fintype.card k' = p ^ qq)
  {H : Type w} [Group H] (C : EtaleGaloisCovering X H) (N : Type (u + 1)) [AddCommGroup N]
  [Module R N] (ρ : H →* Module.End R N) (eN : N ≃ₗ[R] R) (τ : H → R)
  (hτ : ∀ g x, eN (ρ g x) = eN x * τ g)
  (P : EtaleModules.{u, 0} R X) (eP : P ≅ C.descentSheaf.{u, 0, w, 0} R N ρ)

/-- The inverse image to `X ×_k k'` of a sheaf placed in degree `0`. -/
abbrev baseChangeSingle (G : EtaleModules.{u, 0} R X) :
    CochainComplex.Plus (EtaleModules.{u, 0} R (pullback f (specAlgebraMap k k'))) :=
  (etaleModuleInverseImage.{u, 0} R
      (pullback.fst f (specAlgebraMap k k'))).mapCochainComplexPlus.obj
    ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} R X) 0).obj G)

omit [Fintype k] in
include hτ eP in
/-- The local term of the trace formula for the inverse image of `𝒫` at a rational point `s` of
`X ×_k k'`, lying over `x ∈ X` with `#k' = #κ(x) ^ n`, is the class in `R^♮` of `τ(g_x ^ n)`,
where `g_x` is the Frobenius element of the covering `C` at `x`. -/
theorem perfectDerivedTrace_rationalPointStalkFrobenius_descentSheaf
    (s : rationalPoints (pullback.snd f (specAlgebraMap k k')))
    [Finite (X.residueField ((s.1 ≫ pullback.fst f (specAlgebraMap k k'))
      (IsLocalRing.closedPoint k')))] (n : ℕ)
    (hn : Fintype.card k' = Nat.card (X.residueField ((s.1 ≫ pullback.fst f (specAlgebraMap k k'))
      (IsLocalRing.closedPoint k'))) ^ n)
    (a : (geometricPointAt X ((s.1 ≫ pullback.fst f (specAlgebraMap k k'))
      (IsLocalRing.closedPoint k'))).source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = (geometricPointAt X ((s.1 ≫ pullback.fst f (specAlgebraMap k k'))
      (IsLocalRing.closedPoint k'))).hom)
    (hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (rationalPointStalkComplex.{u, 0} R kbar s.1 (baseChangeSingle R f k' P)))) :
    perfectDerivedTrace R ⟨_, hperf⟩ (DerivedCategory.Q.map
        (rationalPointStalkFrobenius.{u, 0} R kbar p qq hcard' s.1
          (baseChangeSingle R f k' P))) =
      q R (τ (C.pointElement a ha (frobeniusPointHom X ((s.1 ≫ pullback.fst f (specAlgebraMap k k'))
        (IsLocalRing.closedPoint k'))) ^ n)) := by
  let g := pullback.fst f (specAlgebraMap k k')
  let e0 : ((HomologicalComplex.single (EtaleModules.{u, 0} R X) (ComplexShape.up ℤ) 0).obj P).X 0 ≅
      C.descentSheaf.{u, 0, w, 0} R N ρ :=
    HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 P ≪≫ eP
  obtain ⟨ε, hε⟩ := C.exists_stalk_inverseImage_geometricFrobenius g s.1 kbar p qq R N ρ hcard' n hn
    e0 a ha
  refine perfectDerivedTrace_rationalPointStalkFrobenius_eq_q R kbar p qq hcard' s.1 _
    (fun i hi => Functor.map_isZero _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi))
    (ε.trans eN) _ (fun m => ?_) hperf
  exact (congrArg eN (hε m)).trans (hτ _ _)

end Stacks.EtaleCohomology
