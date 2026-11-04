module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphismInterleaving
public import StacksFrontier.RingTheory.Koszul.PowBaseTensorBalanceDerived
public import StacksFrontier.RingTheory.Koszul.PowSystemsProIso

/-!
# The two derived tensor products of a Koszul system have the same derived limit

Let `f₁, …, f_r` be elements of a commutative ring `R`, let `K_n` be the Koszul differential
graded algebra on `f₁^n, …, f_r^n` and let `(M_n)` be an inverse system of differential graded
`K_n`-modules carrying a commuting action of a differential graded algebra `B`. This file proves
that for every `t ≥ 1`
$$
R\lim (M_n \otimes_R^{\mathbf L} K_t) = R\lim (M_n \otimes_{K_n}^{\mathbf L} K_t).
$$

## Main results

* `InverseSequence.ProIso.Interleaving.ofIsoRight`: interleaved maps into an inverse system are
  interleaved maps into any inverse system isomorphic to it.
* `Koszul.powBaseTensorTower_eq`: the tower `n ↦ M_n ⊗_{K_n}^𝐋 (K_n ⊗_R K_t)` read through the
  inverse-system machinery of Tag 0GZI is the one read as a tower of derived tensor products
  over a varying algebra.
* `Koszul.nonempty_iso_of_isDerivedLimit_powKoszulTensorBalance`: any derived limit of
  `n ↦ M_n ⊗_{K_n}^𝐋 K_t` is isomorphic to any derived limit of `n ↦ M_n ⊗_R^𝐋 K_t`.

## Implementation notes

*What an object of `D(ℕ, (K_n))` is here.* The source's `(M_n)` is an inverse system of
differential graded `K_n`-modules with a commuting `B`-action and semilinear transition
homomorphisms. The two statements being compared use it in two different ways, so both are asked
for: Tag 0GZI uses it through the comparison maps
`M_m ⊗^𝐋_{K_m} X|_{K_m} ⟶ M_n ⊗^𝐋_{K_n} X` of the derived tensor functors, which is a
`DifferentialGraded.BimoduleSystem`, and the first step uses it through the plain transition
homomorphisms `M_{n+1} ⟶ M_n|_τ` of bimodules. The hypothesis `hcmp` says that the former are the
derived comparisons of the latter, which is what holds for an actual inverse system of
bimodules; it is the hypothesis of
`DifferentialGraded.BimoduleSystem.towerMap_ofSemilinear_towerMap`, the lemma that identifies the
two readings of the middle tower. Nothing is assumed about `(M_n)` beyond being such a system.

*The indexing and `t`.* The towers are indexed by `n ↦ t + n`, so that `K_t → K_{t+n}` exists at
every level; a derived limit is unchanged by passing to a cofinal subsystem, and the source
likewise introduces `{}_nK_t` only for `n ≥ t`. The source's `t ≥ 1` is assumed, since the
comparison maps of Tag 0GZ7 need it.

*The target.* `D(B, d)` for an arbitrary differential graded `R`-algebra `B`; the source's `D(R)`
is the case of `B` concentrated in degree zero with `B^0 = R`, so the statement below is a
generalization of the source's.

*The conclusion is non-canonical.* Tag 0H9L produces an isomorphism of derived limits that is not
canonical, and `CategoryTheory.Pretriangulated.IsDerivedLimit` is a predicate rather than a
construction; the conclusion is accordingly that any derived limit of the one tower is isomorphic
to any derived limit of the other, which is what makes it independent of a choice.

*`hK` and `hK'` are the source's `R lim`.* Tag 0GZJ equates two derived limits, and `R lim` is a
predicate (Tag 08TC) rather than an operation, so the two sides have to be named and asserted to
be derived limits; `hK` and `hK'` do exactly that.

## References

* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ)
* [Stacks Project, Tag 0GZI](https://stacks.math.columbia.edu/tag/0GZI) and
  [Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
* [Stacks Project, Tag 0H9L](https://stacks.math.columbia.edu/tag/0H9L) compares the derived
  limits of pro-isomorphic inverse systems.
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'


universe v u

namespace InverseSequence.ProIso.Interleaving

variable {D : Type u} [Category.{v} D] {X Y Y' : ℕᵒᵖ ⥤ D}

/-- **Interleaved maps are carried along an isomorphism of the second inverse system.** The
forward maps are followed by the isomorphism and the backward maps are preceded by its inverse;
the two composition identities are unchanged, by naturality. -/
def ofIsoRight (a : Interleaving X Y) (e : Y ≅ Y') : Interleaving X Y' where
  idx := a.idx
  idx_strictMono := a.idx_strictMono
  fwd i := a.fwd i ≫ e.hom.app _
  bwd i := e.inv.app _ ≫ a.bwd i
  fwd_bwd i := by
    simp only [Category.assoc]
    rw [← Category.assoc (e.hom.app _) (e.inv.app _) (a.bwd i), e.hom_inv_id_app,
      Category.id_comp, a.fwd_bwd i]
  bwd_fwd i := by
    simp only [Category.assoc]
    rw [← Category.assoc (a.bwd (i + 1)) (a.fwd i), a.bwd_fwd i, tr, tr, e.hom.naturality,
      ← Category.assoc, e.inv_hom_id_app, Category.id_comp]

end InverseSequence.ProIso.Interleaving

namespace Koszul

open DifferentialGraded DifferentialGradedAlgebra DifferentialGradedModule
open DifferentialGraded.Bimodule

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) {t : ℕ} (ht : 1 ≤ t)
  {B : DifferentialGradedAlgebra.{u, u} R}
  (M : BimoduleSystem (powStrictAlgebraSystem f ht).toAlgebraSystem B)
  (bimodTrans : ∀ n : ℕ, M.obj (n + 1) ⟶
    Bimodule.restrictLeft ((powStrictAlgebraSystem f ht).trans (Nat.le_succ n)) (M.obj n))
  (hcmp : ∀ n : ℕ, M.cmp (Nat.le_succ n) =
    Bimodule.derivedTensorRestrictTrans ((powStrictAlgebraSystem f ht).trans (Nat.le_succ n))
      (M.obj (n + 1)) (M.obj n)
      (Bimodule.tensorCompNatTransOfSemilinear
        ((powStrictAlgebraSystem f ht).trans (Nat.le_succ n)) (M.obj (n + 1)) (M.obj n)
        (bimodTrans n)))

include hcmp in
/-- **The two readings of the middle tower agree.** The tower `n ↦ M_n ⊗_{K_n}^𝐋 (K_n ⊗_R K_t)`
obtained by tensoring the system of modules `Koszul.powBaseTensorModuleSystem` with the system of
bimodules `(M_n)` is the Koszul tower of derived tensor products
`Koszul.powBaseTensorDerivedTensorTower`. -/
theorem powBaseTensorTower_eq :
    M.tower (powBaseTensorModuleSystem f ht) =
      (powBaseTensorDerivedTensorTower f t ht M.obj bimodTrans).tower :=
  congrArg Functor.ofOpSequence (funext fun n =>
    BimoduleSystem.towerMap_ofSemilinear_towerMap (powStrictAlgebraSystem f ht) M
      (powBaseTensorStrictModuleSystem f ht) bimodTrans hcmp
      (fun k => leftOrthogonal_acyclic_powBaseTensorRestrictedModule f t (t + k)) n)

include hcmp in
/-- Interleaved maps between the tower `n ↦ M_n ⊗_{K_n}^𝐋 K_t` and the tower `n ↦ M_n ⊗_R^𝐋 K_t`:
those of Tag 0GZI applied to the pro-isomorphism `Koszul.powProIsoDerived` of the two systems of
modules, carried along `Koszul.powBaseTensorTower_eq` and then along the isomorphism
`Koszul.powBaseTensorBalanceTowerIso`. -/
def powKoszulTensorBalanceInterleaving :
    InverseSequence.ProIso.Interleaving (M.tower (powRestrictedModuleSystem f ht))
      (powBaseDegreeZeroDerivedTensorTower f t ht M.obj bimodTrans).tower :=
  ((powProIsoDerived f ht).interleaving M).ofIsoRight
    (eqToIso (powBaseTensorTower_eq f ht M bimodTrans hcmp) ≪≫
      powBaseTensorBalanceTowerIso f t ht M.obj bimodTrans)

include hcmp in
/-- Let `R` be a ring, let `f₁, …, f_r ∈ R` and let `K_n` be the Koszul complex on `f₁^n, …, f_r^n`
viewed as a differential graded `R`-algebra. Let `(M_n)` be an object of `D(ℕ, (K_n))`. Then for
every `t ≥ 1` `R lim (M_n ⊗_R^𝐋 K_t) = R lim (M_n ⊗_{K_n}^𝐋 K_t)`.

The isomorphism is not canonical, so the conclusion is stated for an arbitrary derived limit of
each tower. With `B` concentrated in degree zero with `B^0 = R` the target `D(B, d)` is the
source's `D(R)`. -/
@[stacks 0GZJ "R lim (M_n ⊗^𝐋_R K_t) = R lim (M_n ⊗^𝐋_{K_n} K_t)"]
theorem nonempty_iso_of_isDerivedLimit_powKoszulTensorBalance
    [HasProduct fun n : ℕ => (M.tower (powRestrictedModuleSystem f ht)).obj (op n)]
    [HasProduct fun n : ℕ =>
      (powBaseDegreeZeroDerivedTensorTower f t ht M.obj bimodTrans).tower.obj (op n)]
    (K K' : derivedCategory' B)
    (hK : Pretriangulated.IsDerivedLimit (M.tower (powRestrictedModuleSystem f ht)) K)
    (hK' : Pretriangulated.IsDerivedLimit
      (powBaseDegreeZeroDerivedTensorTower f t ht M.obj bimodTrans).tower K') :
    Nonempty (K ≅ K') :=
  InverseSequence.ProIso.Interleaving.nonempty_iso_of_isDerivedLimit
    (powKoszulTensorBalanceInterleaving f ht M bimodTrans hcmp) K K' hK hK'

end Koszul

end
