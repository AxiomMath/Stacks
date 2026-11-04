module

public import StacksFrontier.AlgebraicGeometry.ImmersionEvaluationSurjective.JetQuotient
public import StacksFrontier.AlgebraicGeometry.Variety.ClosedPointFinrank
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.RingTheory.LocalRing.MaximalIdealSqQuotient

/-!
# The dimension of the target of the evaluation at a closed point of a smooth scheme

The dimension count of the proof of [Stacks, Tag 0FD6] needs the dimension of the target
`ℒ_x/𝔪_x²ℒ_x` of the evaluation at a closed point `x` of a scheme `X` smooth of dimension `n`
over an algebraically closed field `k`: it is `n + 1`.

The sibling file `JetQuotient.lean` reduces that to the local ring, identifying the target with
the second order jets `𝒪_{X,x}/𝔪_x²`, and this file computes the dimension of those jets. The
exact sequence `0 → 𝔪_x/𝔪_x² → 𝒪_{X,x}/𝔪_x² → κ(x) → 0` of
`Stacks.LocalRing.MaximalIdealSq.finrank_quotient_maximalIdeal_sq` splits the count in two:
the local ring of a smooth scheme is regular, so the cotangent space has dimension the Krull
dimension of the local ring, which at a closed point of a scheme locally of finite type over a
field is the dimension of the scheme there; and the residue field at a closed point over an
algebraically closed field is the base field, so it contributes `1`.

## Main results

* `Stacks.JetFinrank.finrank_jetQuotient_of_isClosed`: **`dim_k 𝒪_{X,x}/𝔪_x² = n + 1`** at a
  closed point of a scheme smooth over an algebraically closed field and of dimension `n`
  there.
* `Stacks.JetFinrank.finrank_evalQuotient_of_isClosed`: the same for the target
  `ℒ_x/𝔪_x²ℒ_x` of the evaluation.
* `Stacks.JetFinrank.finrank_ker_evalCoord_of_smooth`: **`dim ker ev_x = r - (n + 1)`**, the
  fibre dimension of the dimension count, where `r` is the dimension of the linear system.
* `Stacks.JetFinrank.succ_le_of_smooth`: **`n + 1 ≤ r`**, its other numerical input.
* `Stacks.JetFinrank.exists_natCast_eq_topologicalKrullDimAt_of_isClosed`: the dimension `n` of
  the results above **exists** at every closed point of a smooth scheme, the local ring there
  being regular.

## Implementation notes

The dimension `n` of `X` enters as the dimension `AlgebraicGeometry.topologicalKrullDimAt X x`
of `X` at the point, which is all the computation sees and which asks nothing of `X` away from
`x`. For an irreducible `X` that is the dimension of the whole scheme, by
`AlgebraicGeometry.topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible`, so a hypothesis
`topologicalKrullDim X = n` is turned into the one below by composing with that equality.

Three `k`-vector space structures meet here and only two of them are used. The target of the
evaluation and the jet quotient carry restriction of scalars along
`Stacks.ImmersionEvaluationSurjective.baseGerm`, the structure map read in the stalk; the
cotangent space and the residue field carry the structures induced by the `k`-algebra structure
`(Stacks.ImmersionEvaluationSurjective.baseGerm f x).toAlgebra` on the stalk, which is the same
restriction of scalars. The structure used in
`AlgebraicGeometry.finrank_cotangentSpace_base_eq_of_isClosed`, restriction along `k → κ(x)`, is
*not* used: the comparison of the dimension of the cotangent space over `k` with its dimension
over `κ(x)` is redone here for the algebra structure above, from
`AlgebraicGeometry.bijective_algebraMap_residueField_of_isClosed`, whose statement is about a
ring map rather than about a module structure and so transfers with no bookkeeping.

The identification of the jet quotient `𝒪_{X,x}/𝔪_x²` of `JetQuotient.lean`, a quotient by the
submodule `𝔪_x²·𝒪_{X,x}`, with the ring quotient by the ideal `𝔪_x²` is
`Submodule.quotEquivOfEq`; the two agree because `I • ⊤ = I` in the module `R` over itself.

No `@[stacks]` attribute is attached: like its siblings this is a step inside the proof of
Tag 0FD6, not the assertion of a tag.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Stacks.JetFinrank

open Stacks.ImmersionEvaluationSurjective Stacks.StalkJet Stacks.ProjectiveFromSections

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (x : X)

/-- The cotangent space dimension of the local ring at a closed point of a smooth scheme is the
local dimension of the scheme. -/
private theorem finrank_cotangentSpace_eq_topologicalKrullDimAt {K : Type u} [Field K]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of K)) (y : Y) [Smooth g]
    (hy : IsClosed ({y} : Set Y)) :
    (Module.finrank (ResidueField (Y.presheaf.stalk y)) (CotangentSpace (Y.presheaf.stalk y)) :
      WithBot ℕ∞) = topologicalKrullDimAt Y y := by
  have : IsRegularLocalRing (Y.presheaf.stalk y) :=
    isRegularLocalRing_stalk_of_smooth_over_field g y
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsNoetherianRing (Y.presheaf.stalk y) := inferInstance
  have hreg := (IsRegularLocalRing.iff_finrank_cotangentSpace (Y.presheaf.stalk y)).mp inferInstance
  rwa [← topologicalKrullDimAt_eq_krullDimOfRing_stalk K Y g y hy] at hreg

/-- **The second order jets of the local ring at a closed point of a smooth scheme of dimension
`n` there have dimension `n + 1`** over the base field, which is assumed algebraically closed.

The local ring is regular, so its cotangent space has dimension its Krull dimension, which at a
closed point of a scheme locally of finite type over a field is the dimension `n` of the scheme
at that point; the residue field is the base field, contributing the remaining `1`. -/
theorem finrank_jetQuotient_of_isClosed [Smooth f] {n : ℕ}
    (hx : IsClosed ({x} : Set X)) (hdim : topologicalKrullDimAt X x = (n : WithBot ℕ∞)) :
    letI : Module k (jetQuotient X x) := Module.compHom _ (baseGerm f x)
    Module.finrank k (jetQuotient X x) = n + 1 := by
  let : Module k (jetQuotient X x) := Module.compHom _ (baseGerm f x)
  let : Algebra k (X.presheaf.stalk x) := (baseGerm f x).toAlgebra
  let : IsScalarTower k (X.presheaf.stalk x) (jetQuotient X x) :=
    ⟨fun c r m => mul_smul (baseGerm f x c) r m⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
  have hbij : Function.Bijective (algebraMap k (ResidueField (X.presheaf.stalk x))) :=
    bijective_algebraMap_residueField_of_isClosed f x hx
  have ek : k ≃ₐ[k] ResidueField (X.presheaf.stalk x) :=
    AlgEquiv.ofBijective (Algebra.ofId k _) hbij
  have hres : Module.finrank k (ResidueField (X.presheaf.stalk x)) = 1 := by
    rw [← ek.toLinearEquiv.finrank_eq, Module.finrank_self]
  have : Module.Finite k (ResidueField (X.presheaf.stalk x)) :=
    Module.Finite.equiv ek.toLinearEquiv
  have hcot : Module.finrank k (CotangentSpace (X.presheaf.stalk x)) = n := by
    have hmul := Module.finrank_mul_finrank k (ResidueField (X.presheaf.stalk x))
      (CotangentSpace (X.presheaf.stalk x))
    rw [hres, one_mul] at hmul
    have hreg := finrank_cotangentSpace_eq_topologicalKrullDimAt f x hx
    rw [hdim] at hreg
    rw [← hmul]
    exact_mod_cast hreg
  have e : jetQuotient X x ≃ₗ[X.presheaf.stalk x]
      (X.presheaf.stalk x ⧸ maximalIdeal (X.presheaf.stalk x) ^ 2) :=
    Submodule.quotEquivOfEq _ _ (by simp)
  rw [(e.restrictScalars k).finrank_eq,
    Stacks.LocalRing.MaximalIdealSq.finrank_quotient_maximalIdeal_sq k (X.presheaf.stalk x),
    hcot, hres]

omit [IsAlgClosed k] in
/-- **A scheme smooth over a field has a finite dimension at each of its closed points.** The
local ring at a closed point of a smooth scheme is regular, so its Krull dimension is the
dimension of its cotangent space, a natural number; and at a closed point of a scheme locally of
finite type over a field that Krull dimension is the local dimension of the scheme.

This is what makes the dimension `n` in the hypotheses of
`Stacks.JetFinrank.finrank_jetQuotient_of_isClosed` and its consequences *exist* at every closed
point: no bound on the dimension of the scheme has to be assumed to produce it. -/
theorem exists_natCast_eq_topologicalKrullDimAt_of_isClosed [Smooth f]
    (hx : IsClosed ({x} : Set X)) :
    ∃ n : ℕ, topologicalKrullDimAt X x = (n : WithBot ℕ∞) := by
  exact ⟨_, (finrank_cotangentSpace_eq_topologicalKrullDimAt f x hx).symm⟩

variable {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- **The target `ℒ_x/𝔪_x²ℒ_x` of the evaluation at a closed point of a scheme smooth over an
algebraically closed field and of dimension `n` there has dimension `n + 1`.** -/
theorem finrank_evalQuotient_of_isClosed [Smooth f] {n : ℕ}
    (hx : IsClosed ({x} : Set X)) (hdim : topologicalKrullDimAt X x = (n : WithBot ℕ∞)) :
    Module.finrank k (evalQuotient f L x) = n + 1 :=
  (finrank_evalQuotient_eq_finrank_jetQuotient L f x).trans
    (finrank_jetQuotient_of_isClosed f x hx hdim)

variable {m : ℕ} (s : Fin (m + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s)
  {V : Type u} [AddCommGroup V] [Module k V]

/-- **The kernel of the evaluation at a closed point of a smooth scheme has dimension
`r - (n + 1)`**, where `r` is the dimension of the linear system and `n` the dimension of the
scheme at the point: the fibre bound that the dimension count of [Stacks, Tag 0FD6] consumes.

This is `Stacks.ImmersionEvaluationSurjective.finrank_ker_evalCoord_of_isClosed`, whose
right-hand side `r - dim(ℒ_x/𝔪_x²ℒ_x)` is evaluated by
`Stacks.JetFinrank.finrank_evalQuotient_of_isClosed`. -/
theorem finrank_ker_evalCoord_of_smooth [Smooth f] {n : ℕ}
    (b : Module.Basis (Fin (m + 1)) k V)
    [AlgebraicGeometry.IsImmersion (AlgebraicGeometry.toProjectiveSpaceOfModule b s hs f)]
    (hx : IsClosed ({x} : Set X)) (hdim : topologicalKrullDimAt X x = (n : WithBot ℕ∞)) :
    Module.finrank k (LinearMap.ker (evalCoord s f x)) = (m + 1) - (n + 1) := by
  rw [finrank_ker_evalCoord_of_isClosed s f x hs b hx,
    finrank_evalQuotient_of_isClosed f x hx hdim]

/-- **A linear system whose evaluation at a closed point of a smooth scheme of dimension `n`
there is surjective has dimension at least `n + 1`**: the inequality that makes the subtraction of
`Stacks.JetFinrank.finrank_ker_evalCoord_of_smooth` a genuine one. -/
theorem succ_le_of_smooth [Smooth f] {n : ℕ}
    (b : Module.Basis (Fin (m + 1)) k V)
    [AlgebraicGeometry.IsImmersion (AlgebraicGeometry.toProjectiveSpaceOfModule b s hs f)]
    (hx : IsClosed ({x} : Set X)) (hdim : topologicalKrullDimAt X x = (n : WithBot ℕ∞)) :
    n + 1 ≤ m + 1 := by
  have h := finrank_evalQuotient_le_of_isClosed s f x hs b hx
  rwa [finrank_evalQuotient_of_isClosed f x hx hdim] at h

end Stacks.JetFinrank

end
