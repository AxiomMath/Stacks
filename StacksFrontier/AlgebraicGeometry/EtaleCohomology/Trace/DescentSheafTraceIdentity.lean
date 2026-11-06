module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DescentSheafLocalTerm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusPowerTrace

/-!
# The traces of the powers of Frobenius on `RΓ_c` of the regular descent sheaf

Let `C` be an étale Galois covering of a separated scheme `X` of finite type over a finite field
`k`, with group `H`, and `𝒫` a sheaf of `R`-modules isomorphic to the descent sheaf of a free rank
one `R`-module on which `H` acts by right multiplications `x ↦ x ⬝ τ(g)`. Given the trace formula
for `𝒫` over an extension `k'` of degree `m` of `k` (the trace of the Frobenius of `X ×_k k'` on
`RΓ_c` is the sum of the local terms at its rational points), the trace of the `m`-th power of
`π_X^*` on `RΓ_c(X_k̄, 𝒫)` is

`Tr((π_X^*)^m | RΓ_c(X_k̄, 𝒫)) = ∑_{x ∈ |X|, deg x ∣ m} deg x · [τ(g_x ^ (m / deg x))]`

in `R^♮`, where `g_x` is the Frobenius element of the covering at `x`. These are the trace
identities of the key lemma of [Stacks, Tag 03UZ].

## Main results

* `Stacks.EtaleCohomology.perfectDerivedTrace_pow_descentSheaf_eq_sum`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius CategoryTheory.FilteredDerived Stacks.CharSeriesTraceDetection

universe u w

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (R : Type) [Ring R] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
  (hcard : Fintype.card k = p ^ q)
  {H : Type w} [Group H] (C : EtaleGaloisCovering X H) (N : Type (u + 1)) [AddCommGroup N]
  [Module R N] (ρ : H →* Module.End R N) (eN : N ≃ₗ[R] R) (τ : H → R)
  (hτ : ∀ g x, eN (ρ g x) = eN x * τ g)
  (P : EtaleModules.{u, 0} R X) (eP : P ≅ C.descentSheaf.{u, 0, w, 0} R N ρ)
  (a : ∀ x : X, (geometricPointAt X x).source ⟶ C.cover.left)
  (ha : ∀ x : X, a x ≫ C.cover.hom = (geometricPointAt X x).hom)

open Classical in
/-- The value `[τ(g_x ^ (m / deg x))]` at a point with finite residue field, and `0` elsewhere. -/
def descentSheafLocalValue (m : ℕ) (x : X) : AdditiveCommutatorQuotient R :=
  if h : Finite (X.residueField x) then
    Stacks.CharSeriesTraceDetection.q R
      (τ (C.pointElement (a x) (ha x) (@frobeniusPointHom X x h) ^ (m / residueDegree f x)))
  else 0

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- The order of the residue field at a closed point of degree `d` is `#k ^ d`. -/
theorem natCard_residueField_eq_natCard_pow_residueDegree (x : X) [Finite (X.residueField x)] :
    Nat.card (X.residueField x) = Nat.card k ^ residueDegree f x := by
  let : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
  have : Finite k := Finite.of_injective _ (algebraMap k (X.residueField x)).injective
  have : Module.Finite k (X.residueField x) := Module.Finite.of_finite
  exact Module.natCard_eq_pow_finrank

include hτ eP in
/-- **The trace identities for the regular descent sheaf.** Given the trace formula for `𝒫` over
an extension `k'` of degree `m` of `k`, `RΓ_c(X_k̄, 𝒫)` is perfect and the trace of the `m`-th
power of `π_X^*` on it is `∑_{x ∈ |X|, deg x ∣ m} deg x · [τ(g_x ^ (m / deg x))]`. -/
theorem perfectDerivedTrace_pow_descentSheaf_eq_sum (m : ℕ) (hm : 0 < m) (k' : Type u)
    [Field k'] [Fintype k'] [Algebra k k'] [Algebra k' kbar] [IsScalarTower k k' kbar]
    [CharP k' p] (hcard' : Fintype.card k' = p ^ (q * m)) (hdeg : Module.finrank k k' = m)
    (h03 : ∃ (hs : ∀ s : rationalPoints (pullback.snd f (specAlgebraMap k k')),
        StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
          (rationalPointStalkComplex.{u, 0} R kbar s.1 (baseChangeSingle R f k' P))))
      (hperf' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} R (pullback.snd f (specAlgebraMap k k'))
          (compactificationFieldBaseChange f j k') kbar (baseChangeSingle R f k' P)))),
      perfectDerivedTrace R ⟨_, hperf'⟩ (DerivedCategory.Plus.ι.map
          (canonicalCompactSupportFrobenius.{u, 0} R (pullback.snd f (specAlgebraMap k k'))
            (compactificationFieldBaseChange f j k') kbar p (q * m) hcard'
            (baseChangeSingle R f k' P))) =
        ∑ᶠ s : rationalPoints (pullback.snd f (specAlgebraMap k k')),
          perfectDerivedTrace R ⟨_, hs s⟩ (DerivedCategory.Q.map
            (rationalPointStalkFrobenius.{u, 0} R kbar p (q * m) hcard' s.1
              (baseChangeSingle R f k' P)))) :
    ∃ hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} R f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} R X) 0).obj P))),
      perfectDerivedTrace R ⟨_, hperf⟩
          (((End.of (DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0} R f j kbar
            p q hcard ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} R X) 0).obj
              P)))) ^ m : End _).asHom) =
        ∑ x ∈ (closedPointsDegreeLE f m).filter (fun x => residueDegree f x.1 ∣ m),
          residueDegree f x.1 • descentSheafLocalValue R f C τ a ha m x.1 := by
  obtain ⟨hs, hperf', h3⟩ := h03
  obtain ⟨hperf, hpow⟩ := perfectDerivedTrace_pow_canonicalCompactSupportFrobenius_eq R f j k' kbar
    p q hcard m hm hcard' _ hperf'
  refine ⟨hperf, ?_⟩
  have hreg := finsum_rationalPoints_baseChange_eq_sum f k'
    (descentSheafLocalValue R f C τ a ha m)
  rw [hdeg] at hreg
  rw [hpow, h3, ← hreg]
  refine finsum_congr fun s => ?_
  set x := (s.1 ≫ pullback.fst f (specAlgebraMap k k')) (IsLocalRing.closedPoint k')
  let y := rationalPointsBaseChangeEquiv f k' s
  have hy : (fieldValuedPointsEquiv f k' y).1 = x := rfl
  obtain ⟨hclosed, hdvd⟩ := isClosed_and_dvd_of_residueEmbeddings f k' x
    (hy ▸ (fieldValuedPointsEquiv f k' y).2)
  have : Finite (X.residueField x) := finite_residueField f x hclosed
  have hn : Fintype.card k' = Nat.card (X.residueField x) ^ (m / residueDegree f x) := by
    rw [hdeg] at hdvd
    rw [natCard_residueField_eq_natCard_pow_residueDegree f x, Nat.card_eq_fintype_card, hcard,
      ← pow_mul, ← pow_mul, hcard', Nat.mul_div_cancel' hdvd]
  rw [perfectDerivedTrace_rationalPointStalkFrobenius_descentSheaf R f k' kbar p (q * m) hcard' C
    N ρ eN τ hτ P eP s (m / residueDegree f x) hn (a x) (ha x) (hs s), descentSheafLocalValue,
    dif_pos ‹Finite (X.residueField x)›]

end Stacks.EtaleCohomology
