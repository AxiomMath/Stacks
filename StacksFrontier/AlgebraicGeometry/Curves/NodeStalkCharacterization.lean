module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Curves.IsNode
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.NodalCharacterization
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.LocalProperty
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.RingTheory.Nagata.Japanese
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Nodes on a curve from the delta invariant and the number of geometric branches

For a point `x` of a scheme `X` locally of finite type over a field `k` and of dimension one, the
local ring `𝒪_{X,x}` is a nodal `k`-algebra exactly when the residue field is separable over `k`,
the local ring is reduced, its delta invariant is one and it has two geometric branches.

The algebraic equivalence is
`Stacks.Curves.isNodalAlgebra_iff_deltaInvariant_eq_one_and_two_geometricBranches`, which asks in
addition that the local ring be Nagata and one-dimensional.  Both of those are supplied here from
the hypotheses on the scheme: the Nagata property because a scheme locally of finite type over a
field is Nagata and the Nagata property passes to localizations, and the dimension because the
dimension of a local ring of `X` is bounded by the dimension of `X` while a reduced local ring of
delta invariant one is not a field.

This file also records the implication from the geometric form of the node condition — every point
of `X_{k̄}` above `x` is an ordinary double point — to the node condition itself, which is an
existential over such points together with closedness of `x`.

## Main results

* `AlgebraicGeometry.isNagataRing_stalk_of_isNagataScheme` — the local rings of a Nagata scheme
  are Nagata rings.
* `AlgebraicGeometry.isNagataRing_stalk_of_locallyOfFiniteType` — the same for a scheme locally of
  finite type over a field.
* `AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim` — a local ring of a scheme has
  dimension at most that of the scheme.
* `Ring.deltaInvariant_eq_zero_of_isField` — a field has delta invariant zero.
* `Stacks.Curves.ringKrullDim_eq_one_of_isReduced_of_deltaInvariant_eq_one` — a reduced local ring
  of dimension at most one and delta invariant one has dimension exactly one.
* `Stacks.Curves.isNodalAlgebra_stalk_iff_deltaInvariant_eq_one_and_two_geometricBranches` — the
  equivalence of the nodal-algebra condition with the delta-invariant and geometric-branch
  condition, at a point of a one-dimensional scheme locally of finite type over a field.
* `Stacks.Curves.isNode_of_forall_isOrdinaryDoublePoint` — a closed point above which every point
  of the base change to the algebraic closure is an ordinary double point is a node.

## Implementation notes

The `k`-algebra structure on `𝒪_{X,x}` is the one induced by the germ of the structure morphism at
`x`, and the `k`-algebra structure on `κ(x)` is induced from it by the residue map; the latter is
definitionally the algebra structure `IsLocalRing.ResidueField.algebra` obtains from the former, so
the separability clause is the same statement in either spelling.

The base change in `Stacks.Curves.isNode_of_forall_isOrdinaryDoublePoint` always has a point above
`x`, because `Spec` of a field is a one-point space and the underlying map of a fibre product of
schemes surjects onto the fibre product of the underlying spaces.

## References

* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 035B](https://stacks.math.columbia.edu/tag/035B)
* [Stacks Project, Tag 032U](https://stacks.math.columbia.edu/tag/032U)
* [Stacks Project, Tag 04MU](https://stacks.math.columbia.edu/tag/04MU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing

universe u v

namespace AlgebraicGeometry

/-- **The local ring at a point of a Nagata scheme is a Nagata ring.**  The point lies in an
affine open whose ring of sections is Nagata, and the local ring is a localization of it. -/
theorem isNagataRing_stalk_of_isNagataScheme
    {X : Scheme.{u}} (hX : IsNagataScheme X) (x : X) :
    IsNagataRing (X.presheaf.stalk x) := by
  obtain ⟨U, hxU, -⟩ := hX x
  let y : U.1 := ⟨x, hxU⟩
  let : Algebra Γ(X, U.1) (X.presheaf.stalk (y : X)) :=
    X.presheaf.algebra_section_stalk y
  have : IsLocalization.AtPrime (X.presheaf.stalk (y : X)) (U.2.primeIdealOf y).asIdeal :=
    U.2.isLocalization_stalk y
  exact isNagata_of_isLocalization Γ(X, U.1) (U.2.primeIdealOf y).asIdeal.primeCompl
    (X.presheaf.stalk (y : X)) (IsNagataScheme.isNagataRing_sections hX U)

/-- **The local ring at a point of a scheme locally of finite type over a field is a Nagata
ring.**  Such a scheme is Nagata by Stacks Tag 035B. -/
theorem isNagataRing_stalk_of_locallyOfFiniteType
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) :
    IsNagataRing (X.presheaf.stalk x) :=
  isNagataRing_stalk_of_isNagataScheme
    (isNagataScheme_of_locallyOfFiniteType_over_field k f) x

/-- **The dimension of a local ring of a scheme is at most the dimension of the scheme.**  The
dimension of the scheme is the supremum of those of its local rings (Stacks Tag 04MU). -/
@[ega "IV 5.1.4" "partial"]
theorem ringKrullDim_stalk_le_topologicalKrullDim {X : Scheme.{u}} (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
  exact le_iSup_of_le x le_rfl

end AlgebraicGeometry

namespace Ring

/-- **A field has delta invariant zero.**  A field is integrally closed in its field of fractions,
so the canonical map to the integral closure is already surjective and the quotient vanishes. -/
theorem deltaInvariant_eq_zero_of_isField {A : Type v} [CommRing A] (h : IsField A) :
    deltaInvariant A = 0 := by
  let : Field A := h.toField
  have hrange :
      LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A))) = ⊤ := by
    refine LinearMap.range_eq_top.mpr fun y => ?_
    obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff (K := FractionRing A)).mp inferInstance y.2
    exact ⟨a, Subtype.ext ha⟩
  exact Module.length_eq_zero_iff.mpr (Submodule.Quotient.subsingleton_iff.mpr hrange)

end Ring

namespace Stacks.Curves

/-- **A reduced local ring of dimension at most one and delta invariant one has dimension exactly
one.**  A reduced local ring of dimension zero is a field, and a field has delta invariant
zero. -/
theorem ringKrullDim_eq_one_of_isReduced_of_deltaInvariant_eq_one
    (A : Type v) [CommRing A] [IsLocalRing A] [IsReduced A]
    (hle : ringKrullDim A ≤ (1 : WithBot ℕ∞)) (hdelta : Ring.deltaInvariant A = 1) :
    ringKrullDim A = 1 := by
  have hne0 : ringKrullDim A ≠ 0 := fun hdim => by
    have : Ring.KrullDimLE 0 A := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim
    exact one_ne_zero (hdelta.symm.trans
      (Ring.deltaInvariant_eq_zero_of_isField Ring.KrullDimLE.isField_of_isReduced))
  have hbot : ringKrullDim A ≠ ⊥ := fun h => by
    simpa [h] using (ringKrullDim_nonneg_of_nontrivial (R := A))
  lift ringKrullDim A to ℕ∞ using hbot with d hd
  have hd1 : d ≤ 1 := by exact_mod_cast hle
  lift d to ℕ using ne_top_of_le_ne_top (by simp) hd1 with n hn
  have hn1 : n ≤ 1 := by exact_mod_cast hd1
  have hn0 : n ≠ 0 := fun he => hne0 (by norm_num [he])
  obtain rfl : n = 1 := by omega
  norm_num

/-- **The local ring at a point of a one-dimensional scheme locally of finite type over a field is
a nodal algebra if and only if the residue field is separable, the local ring is reduced, its
delta invariant is one and it has two geometric branches.**

This is the equivalence of conditions (2) and (6) of Stacks Tag 0C4D.  Its content is the
algebraic equivalence of Stacks Tag 0C4A, whose two further hypotheses are discharged here: the
local ring is Nagata because the scheme is locally of finite type over a field, and it is
one-dimensional because its dimension is at most that of the scheme while a reduced local ring of
delta invariant one is not a field. -/
@[stacks 0C4D "clauses (2) and (6)"]
theorem isNodalAlgebra_stalk_iff_deltaInvariant_eq_one_and_two_geometricBranches
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX : topologicalKrullDim X = 1) (x : X) :
    let kToStalk : k →+* X.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom
    letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
    letI : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
    (IsNodalAlgebra k (X.presheaf.stalk x) ↔
      Algebra.IsSeparableExtension k (X.residueField x) ∧
        IsReduced (X.presheaf.stalk x) ∧
          Ring.deltaInvariant (X.presheaf.stalk x) = 1 ∧
            numberOfGeometricBranches X x = 2) := by
  intro kToStalk
  let : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
  have hNag : IsNagataRing (X.presheaf.stalk x) :=
    isNagataRing_stalk_of_locallyOfFiniteType k (X ↘ Spec (.of k)) x
  have hdimle : ringKrullDim (X.presheaf.stalk x) ≤ (1 : WithBot ℕ∞) :=
    hX ▸ ringKrullDim_stalk_le_topologicalKrullDim x
  constructor
  · intro hnode
    obtain ⟨hsep, hred, -, hdelta, hbr⟩ :=
      (isNodalAlgebra_iff_deltaInvariant_eq_one_and_two_geometricBranches k
        (X.presheaf.stalk x) hNag).mp hnode
    exact ⟨hsep, hred, hdelta, hbr⟩
  · rintro ⟨hsep, hred, hdelta, hbr⟩
    have : IsReduced (X.presheaf.stalk x) := hred
    exact (isNodalAlgebra_iff_deltaInvariant_eq_one_and_two_geometricBranches k
      (X.presheaf.stalk x) hNag).mpr
      ⟨hsep, hred,
        ringKrullDim_eq_one_of_isReduced_of_deltaInvariant_eq_one (X.presheaf.stalk x)
          hdimle hdelta,
        hdelta, hbr⟩

/-- **A closed point above which every point of the base change to the algebraic closure is an
ordinary double point is a node.**

This is the implication from condition (3) to condition (1) of Stacks Tag 0C4D.  The fibre of the
base change over `x` is nonempty because `Spec` of a field is a one-point space, so the universally
quantified hypothesis supplies the point required by the definition of a node. -/
theorem isNode_of_forall_isOrdinaryDoublePoint
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] (x : X)
    (hx : IsClosed ({x} : Set X))
    (h : let K := AlgebraicClosure k
      let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
        Spec.map (CommRingCat.ofHom (algebraMap k K))
      let Y := (pullback (X ↘ Spec (.of k)) g : Scheme.{u})
      let p : Y ⟶ X := pullback.fst (X ↘ Spec (.of k)) g
      let q : Y ⟶ Spec (.of K) := pullback.snd (X ↘ Spec (.of k)) g
      letI : Y.Over (Spec (.of K)) := ⟨q⟩
      ∀ xbar : Y, p.base xbar = x → IsOrdinaryDoublePoint K Y xbar) :
    IsNode k X x := by
  obtain ⟨xbar, hfst, -⟩ :=
    Scheme.Pullback.exists_preimage_pullback
      (f := X ↘ Spec (.of k))
      (g := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
      x (IsLocalRing.closedPoint (AlgebraicClosure k)) (Subsingleton.elim _ _)
  exact ⟨hx, xbar, hfst, h xbar hfst⟩

end Stacks.Curves

end
