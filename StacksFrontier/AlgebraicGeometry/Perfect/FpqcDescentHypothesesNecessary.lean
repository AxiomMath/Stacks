module

public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectOverField
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.Examples.GroupSchemes.PrincipalNotFppf.Scheme

/-!
# Which hypotheses of Stacks 09UG are load-bearing

Stacks 09UG says that for an fpqc covering `{f_i : Y_i ⟶ X}` of schemes and `E ∈ D(𝒪_X)`, the
object `E` is perfect if and only if every derived pullback `Lf_i^*E` is perfect. The implication
from left to right is proved, for an arbitrary family and with no hypothesis on it, by
`Stacks.Cohomology.PerfectComplexes.FpqcDescent.forall_isPerfect_derivedPullback_of_isPerfect`.

This file pins down what that generalization costs in the other direction, and exhibits the
forward implication at data for which nothing is degenerate.

## Main results

* `Stacks.Perfect.FpqcNecessary.not_isPerfect_tildeResidueField`: the residue field of the dual
  numbers `k[ε]`, sheafified onto `Spec k[ε]`, is **not** a perfect object of `D(𝒪_{Spec k[ε]})`.
  This is the first object in the library exhibited as non-perfect on a scheme.
* `Stacks.Perfect.FpqcNecessary.not_forall_isPerfect_of_forall_isPerfect_derivedPullback`: the
  converse implication of Stacks 09UG becomes **false** if the hypothesis that the family be an
  fpqc covering is deleted. So the generalization that the forward implication enjoys — no
  hypothesis on the family at all — is available only in that one direction.
* `Stacks.Perfect.FpqcNecessary.isPerfect_derivedPullback_radicalTower`: the forward implication
  at an fpqc covering which is neither an isomorphism nor an open immersion, with the
  perfectness hypothesis discharged rather than assumed.

## Implementation notes

The non-perfect object is Stacks 08EB, `AlgebraicGeometry.isPerfect_tilde_iff`, applied to
`AlgebraicGeometry.not_isPerfectModule_residueField_dualNumber`: the dual numbers are a local
ring with nilpotent maximal ideal, so a finite projective resolution of the residue field would
make them regular, hence a domain.

What refutes the converse without its fpqc hypothesis is the **empty** family, for which the
hypothesis "every `Lf_i^*E` is perfect" holds vacuously. So the part of the fpqc condition the
converse cannot do without is joint surjectivity; flatness and quasi-compactness of the members
are satisfied by the empty family too.

The covering used for the forward implication is the radical tower
`Stacks.Examples.RadicalTower.proj : Spec ℚ[x₀, x₁, …]/(xᵢ^(i+2) - 2) ⟶ Spec ℚ` of
`StacksFrontier.Examples.GroupSchemes.PrincipalNotFppf.Scheme`. It is faithfully flat and affine,
hence an fpqc covering, and `Stacks.Perfect.FpqcNecessary.not_locallyOfFiniteType_radicalTower`
records that it is not locally of finite type, so it is neither an isomorphism nor an open
immersion. The existing non-vacuity examples of
`StacksFrontier/AlgebraicGeometry/Perfect/FpqcTorAmplitude.lean` use the one-member family of the
identity instead, which is degenerate in the family.

The object carried along it is the structure sheaf in degree zero, which is perfect because it is
finite locally free (`AlgebraicGeometry.isPerfect_singleFunctor_of_isFiniteLocallyFree`). That it
is also nonzero is not proved here: the library has no statement that a structure sheaf is a
nonzero sheaf of modules, and the nearest thing,
`AlgebraicGeometry.Space.exists_not_isZero_quasicoherentSheaves`, takes exactly that as a
hypothesis.

*No `stacks` attribute is placed on anything here.* None of these statements is a clause of
Stacks 09UG: two are refutations of weakenings of it and the rest are an instantiation of a
clause proved elsewhere.

## References

* [Stacks Project, Tag 09UG](https://stacks.math.columbia.edu/tag/09UG)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
* [Stacks Project, Tag 08EB](https://stacks.math.columbia.edu/tag/08EB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Examples.RadicalTower (base total proj)

universe u v

namespace Stacks.Perfect.FpqcNecessary

attribute [local instance 2000] HasDerivedCategory.standard

/-! ### A non-perfect object of `D(𝒪_X)` -/

/-- **The residue field of the dual numbers is not perfect on `Spec k[ε]`.**

Stacks 08EB identifies perfectness of a derived sheafification with perfectness of the object of
`D(k[ε])` it comes from, and the residue field of `k[ε]` is not a perfect module: a finite
projective resolution of it would give `k[ε]` finite projective dimension, hence make it a
regular local ring and so a domain, which `ε² = 0 ≠ ε` forbids. -/
public theorem not_isPerfect_tildeResidueField (k : Type u) [Field k] :
    ¬ IsPerfect (X := (Spec (CommRingCat.of (DualNumber k))).toRingedSpace)
        ((AlgebraicGeometry.tilde.functor
            (CommRingCat.of (DualNumber k))).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (DualNumber k)) 0).obj
            (ModuleCat.of (DualNumber k) (IsLocalRing.ResidueField (DualNumber k))))) :=
  fun h =>
    AlgebraicGeometry.not_isPerfectModule_residueField_dualNumber k
      ((AlgebraicGeometry.isPerfect_tilde_iff _).1 h)

/-! ### The converse of Stacks 09UG needs its fpqc hypothesis -/

/-- **The converse implication of Stacks 09UG is false for an arbitrary family of morphisms.**

The forward implication holds for a family about which nothing is assumed
(`Stacks.Cohomology.PerfectComplexes.FpqcDescent.forall_isPerfect_derivedPullback_of_isPerfect`);
the converse does not. The empty family satisfies "every `Lf_i^*E` is perfect" with nothing to
check, so the deleted hypothesis is what rules it out, and the part of it being used is joint
surjectivity: flatness and quasi-compactness of the members hold for the empty family as
well. -/
public theorem not_forall_isPerfect_of_forall_isPerfect_derivedPullback (k : Type u) [Field k] :
    ¬ ∀ (X : Scheme.{u}) (I : Type v) (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
        (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)),
        (∀ i, IsPerfect (X := (Y i).toRingedSpace)
          ((derivedPullback (f i).toLRSHom.toShHom).obj E)) →
        IsPerfect (X := X.toRingedSpace) E := fun h =>
  not_isPerfect_tildeResidueField k
    (h (Spec (CommRingCat.of (DualNumber k))) PEmpty.{v + 1} (fun i => i.elim)
      (fun i => i.elim) _ (fun i => i.elim))

/-! ### The forward implication at a non-degenerate fpqc covering -/

/-- The structure sheaf of `Spec ℚ` placed in degree zero. -/
public def structureSheafZero : DerivedCategory (OXMod.{0, 0} base.toRingedSpace) :=
  (DerivedCategory.singleFunctor base.Modules 0).obj
    (SheafOfModules.unit base.ringCatSheaf)

/-- The structure sheaf in degree zero is perfect, being finite locally free. -/
public theorem isPerfect_structureSheafZero :
    IsPerfect (X := base.toRingedSpace) structureSheafZero :=
  AlgebraicGeometry.isPerfect_singleFunctor_of_isFiniteLocallyFree base _
    (AlgebraicGeometry.isFiniteLocallyFree_unit base)

/-- The one-member family of the radical tower is an fpqc covering of `Spec ℚ`. -/
public theorem radicalTower_mem_fpqcPrecoverage :
    Presieve.ofArrows (fun _ : PUnit.{1} => total) (fun _ => proj) ∈
      Scheme.fpqcPrecoverage base := by
  rw [Presieve.ofArrows_pUnit]
  exact Stacks.Examples.RadicalTower.singleton_proj_mem_fpqcPrecoverage

/-- **The radical tower is not locally of finite type**, so the fpqc covering used below is
neither an isomorphism nor an open immersion. A scheme locally of finite type over `Spec ℚ` with
a morphism to the radical tower is empty, and the radical tower has points. -/
public theorem not_locallyOfFiniteType_radicalTower : ¬ LocallyOfFiniteType proj := fun _ =>
  (Stacks.Examples.RadicalTower.isEmpty_of_locallyOfFiniteType proj (𝟙 total)).false
    (Classical.arbitrary total)

/-- **The forward implication of Stacks 09UG with every binder filled by named data.** The
family is the fpqc covering `radicalTower_mem_fpqcPrecoverage`, whose single member is not
locally of finite type; the object is the structure sheaf in degree zero and its perfectness is
discharged by `isPerfect_structureSheafZero` rather than assumed. -/
public theorem isPerfect_derivedPullback_radicalTower :
    IsPerfect (X := total.toRingedSpace)
      ((derivedPullback proj.toLRSHom.toShHom).obj structureSheafZero) :=
  Stacks.Cohomology.PerfectComplexes.FpqcDescent.forall_isPerfect_derivedPullback_of_isPerfect
    (fun _ : PUnit.{1} => total) (fun _ => proj) structureSheafZero
    isPerfect_structureSheafZero PUnit.unit

/- **The converse implication of Stacks 09UG at the same data**: the hypothesis of
`Stacks.Cohomology.PerfectComplexes.FpqcDescent.isPerfect_of_forall_isPerfect_derivedPullback`
is discharged at the fpqc covering `radicalTower_mem_fpqcPrecoverage` and the structure sheaf in
degree zero. The conclusion is `isPerfect_structureSheafZero`, so this is an `example`. -/
example : IsPerfect (X := base.toRingedSpace) structureSheafZero :=
  Stacks.Cohomology.PerfectComplexes.FpqcDescent.isPerfect_of_forall_isPerfect_derivedPullback
    (fun _ : PUnit.{1} => total) (fun _ => proj) radicalTower_mem_fpqcPrecoverage
    structureSheafZero fun _ => isPerfect_derivedPullback_radicalTower

end Stacks.Perfect.FpqcNecessary

end
