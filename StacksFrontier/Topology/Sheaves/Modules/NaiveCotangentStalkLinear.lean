module

public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentStalk
public import StacksFrontier.Topology.Sheaves.Modules.ConormalSequenceStalkTargetAction

/-!
# Stacks 0D09 as an isomorphism of two-term complexes of `Bₓ`-modules

Let `a : A ⟶ B` be a morphism of sheaves of commutative rings on a topological space `X` and let
`x` be a point of `X`.  `StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentStalk` identifies the
two terms of the stalk at `x` of `NL_{B/A}` with the two terms of `NL_{Bₓ/Aₓ}` as additive
equivalences which are *semilinear* over the stalk `(A[B])ₓ → Bₓ` of the canonical presentation,
and shows that they carry the stalk of the differential to the cotangent complex of `Aₓ → Bₓ`.

This file upgrades those two additive equivalences to linear equivalences over the stalk of the
structure sheaf of `B`, and records the resulting isomorphism of two-term complexes.  The input
that makes the upgrade possible is the compatibility of the two scalar actions on the stalk of a
term of the conormal sequence (`Stacks.Sites.Conormal.conormalSheafStalk_ringCat_smul_eq` and
`Stacks.Sites.Conormal.tensorDifferentialsSheafStalk_ringCat_smul_eq`): the `(A[B])ₓ`-action over
which the semilinearity is stated is the action of the stalk of `B` along the stalk of the
presentation, and that stalk is surjective
(`Stacks.Sites.Conormal.stalkMap_surjective`), so every scalar is such an image and
semilinearity becomes linearity.

## The scalar ring

The scalar ring used here is the `RingCat`-valued stalk
`(Stacks.SheafOfModules.Tensor.ringSheaf B).obj` at `x`, and not the
`CommRingCat`-valued stalk `Bₓ`.  The two are the same ring up to the canonical isomorphism
`SemilinearStalk.commStalkRingEquiv`, along which the module structures of the targets are
transported here (`Stacks.SheafOfModules.moduleRingStalkCotangent` and
`Stacks.SheafOfModules.moduleRingStalkCotangentSpace`), so the statements below say exactly that
the identifications are `Bₓ`-linear.

Two reasons for the choice, and the second is what forces it.  The `RingCat`-valued stalk is the
ring over which `AlgebraicGeometry.SheafOfModules.stalkFunctor` is a functor to modules, so it is
the ring a stalkwise argument about a complex of sheaves of `B`-modules is conducted over.  And
an action of `Bₓ` on the stalk of a term of `NL_{B/A}` cannot be elaborated at all: instance
search for it reaches `Stacks.Sites.Conormal.moduleStalkConormalSheaf`, the action of the stalk
of the *source* sheaf of rings on the same stalk, and then has to decide whether `B` is the
source — here `A[B]`, a sheafification — which exceeds the heartbeat ceiling.  Indeed, the
plain statement `b • ξ = b • ξ` for `b : Bₓ` and `ξ` in the stalk of the degree `-1` term of
`NL_{B/A}` exceeds `synthInstance.maxHeartbeats`, and still does when the correct instance is
supplied as a local instance by `letI`.  With the scalar in the `RingCat`-valued stalk the two
candidate instances differ in the category the stalk is taken in, so the comparison fails
immediately and the action elaborates instantly.

## Main definitions

* `Stacks.SheafOfModules.moduleRingStalkCotangent` and
  `Stacks.SheafOfModules.moduleRingStalkCotangentSpace`: the conormal module and the cotangent
  space of `Algebra.Generators.self Aₓ Bₓ`, as modules over the `RingCat`-valued stalk of the
  sheaf of rings underlying `B`.
* `Stacks.SheafOfModules.naiveCotangentStalkCotangentLinearEquiv` and
  `Stacks.SheafOfModules.naiveCotangentStalkCotangentSpaceLinearEquiv`: the identifications
  `Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv` and
  `Stacks.SheafOfModules.naiveCotangentStalkCotangentSpaceEquiv`, as linear equivalences.
* `Stacks.SheafOfModules.naiveCotangentStalkDifferential`: the stalk at `x` of the differential
  of `NL_{B/A}`, as a linear map.

## Main results

* `Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv_linear` and
  `Stacks.SheafOfModules.naiveCotangentStalkCotangentSpaceEquiv_linear`: the two identifications
  are linear.
* `Stacks.SheafOfModules.conormalSequenceStalkMapF_smul`: the stalk of the differential of
  `NL_{B/A}` is linear, which is what makes
  `Stacks.SheafOfModules.naiveCotangentStalkDifferential` a linear map.
* `Stacks.SheafOfModules.naiveCotangentStalk_eq_naiveCotangentComplexStalk_linear`: **Stacks
  0D09 as an isomorphism of two-term complexes of `Bₓ`-modules.**  The stalk of the differential
  of `NL_{B/A}` is, read through the two linear identifications, the cotangent complex of
  `Algebra.Generators.self Aₓ Bₓ`, which is the differential of `NL_{Bₓ/Aₓ}`.  All four maps of
  the square are linear, so the pair of identifications is an isomorphism of complexes and not
  merely a degreewise bijection.

## Implementation notes

The module structure on the stalk of a term of `NL_{B/A}` is the one
`Mathlib.Algebra.Category.ModuleCat.Stalk` puts on the stalk of a presheaf of modules over a
presheaf of rings.  It is *not* transported along either identification, so the linearity
statements below have content.

`Stacks.SheafOfModules.naiveCotangentStalkDifferential` is proved linear from the equality with
the cotangent complex rather than directly: the cotangent complex is linear and the two
identifications are, by the time the differential is reached, already known to be.

## References

* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), of which this is the
  linear form; the additive form, with the semilinearity clauses, is
  `Stacks.SheafOfModules.naiveCotangentStalk_eq_naiveCotangentComplexStalk`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct

universe u

noncomputable section

namespace Stacks.SheafOfModules

open TopCat.Presheaf Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open Stacks.RelativeDifferentialStalk (algebraStalk)

section Linear

variable {X : TopCat.{u}}
  (A B : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (a : A ⟶ B) (x : X)

/-! ### The scalar ring -/

/-- The conormal module of `Aₓ → Bₓ`, as a module over the `RingCat`-valued stalk of the sheaf of
rings underlying `B`, along `SemilinearStalk.commStalkRingEquiv`. -/
@[instance_reducible]
def moduleRingStalkCotangent :
    letI := algebraStalk a.hom x
    Module (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x))
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
        (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension.Cotangent :=
  letI := algebraStalk a.hom x
  Module.compHom _ (SemilinearStalk.commStalkRingEquiv B.obj x).toRingHom

/-- The cotangent space of `Aₓ → Bₓ`, as a module over the `RingCat`-valued stalk of the sheaf of
rings underlying `B`, along `SemilinearStalk.commStalkRingEquiv`. -/
@[instance_reducible]
def moduleRingStalkCotangentSpace :
    letI := algebraStalk a.hom x
    Module (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x))
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
        (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension.CotangentSpace :=
  letI := algebraStalk a.hom x
  Module.compHom _ (SemilinearStalk.commStalkRingEquiv B.obj x).toRingHom

/-! ### The degree `-1` term -/

/-- Every scalar `s` in the `RingCat`-valued stalk of `B` is the image of some `r` in the stalk of
the canonical presentation, both through `SemilinearStalk.commStalkRingEquiv` and its inverse. -/
private theorem exists_stalkMap_presentation_eq
    (s : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x)) :
    ∃ r, ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom).hom r =
        SemilinearStalk.commStalkRingEquiv B.obj x s ∧
      (SemilinearStalk.commStalkRingEquiv B.obj x).symm
      (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom).hom r) = s := by
  obtain ⟨r, hr⟩ := stalkMap_surjective (presentation (Opens.grothendieckTopology X) A B a
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom x
    (SemilinearStalk.commStalkRingEquiv B.obj x s)
  exact ⟨r, hr, Eq.trans (congrArg (SemilinearStalk.commStalkRingEquiv B.obj x).symm hr)
    ((SemilinearStalk.commStalkRingEquiv B.obj x).symm_apply_apply s)⟩

/-- **The identification of the degree `-1` terms is linear** over the stalk of the sheaf of
rings underlying `B`.  Its semilinearity over the stalk `(A[B])ₓ → Bₓ` of the canonical
presentation is `Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv_semilinear`; that stalk
is surjective, so a scalar `s` is the image of some `r` of `(A[B])ₓ`, and the action of `s` on
the stalk of the conormal sheaf is the `(A[B])ₓ`-action of `r`
(`Stacks.Sites.Conormal.conormalSheafStalk_ringCat_smul_eq`). -/
theorem naiveCotangentStalkCotangentEquiv_linear
    (s : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x))
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (conormalSheaf (Opens.grothendieckTopology X)
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))).val.presheaf x)) :
    letI := algebraStalk a.hom x
    letI := moduleRingStalkCotangent A B a x
    naiveCotangentStalkCotangentEquiv A B a x (s • ξ) =
      s • naiveCotangentStalkCotangentEquiv A B a x ξ := by
  let := algebraStalk a.hom x
  let := moduleRingStalkCotangent A B a x
  obtain ⟨r, hr, hs⟩ := exists_stalkMap_presentation_eq A B a x s
  refine Eq.trans (congrArg (naiveCotangentStalkCotangentEquiv A B a x)
    (Eq.trans (congrArg (fun t : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x) => t • ξ) hs.symm)
      (conormalSheafStalk_ringCat_smul_eq (freeAlgebraSheaf (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x r ξ).symm)) ?_
  refine Eq.trans (naiveCotangentStalkCotangentEquiv_semilinear A B a x r ξ) ?_
  exact congrArg (fun c : ToType (TopCat.Presheaf.stalk B.obj x) =>
    c • naiveCotangentStalkCotangentEquiv A B a x ξ) hr

/-- **The degree `-1` terms agree as modules over the stalk of `B`.**  This is
`Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv` with its linearity. -/
def naiveCotangentStalkCotangentLinearEquiv :
    letI := algebraStalk a.hom x
    letI := moduleRingStalkCotangent A B a x
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (conormalSheaf (Opens.grothendieckTopology X)
          (freeAlgebraSheaf (Opens.grothendieckTopology X) A
            (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
          (presentation (Opens.grothendieckTopology X) A B a
            (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))).val.presheaf x)
      ≃ₗ[ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x)]
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
        (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension.Cotangent :=
  letI := algebraStalk a.hom x
  letI := moduleRingStalkCotangent A B a x
  (naiveCotangentStalkCotangentEquiv A B a x).toLinearEquiv
    (naiveCotangentStalkCotangentEquiv_linear A B a x)

/-- The linear equivalence `naiveCotangentStalkCotangentLinearEquiv` agrees on elements with
`naiveCotangentStalkCotangentEquiv`. -/
theorem naiveCotangentStalkCotangentLinearEquiv_apply
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (conormalSheaf (Opens.grothendieckTopology X)
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))).val.presheaf x)) :
    letI := algebraStalk a.hom x
    naiveCotangentStalkCotangentLinearEquiv A B a x ξ =
      naiveCotangentStalkCotangentEquiv A B a x ξ := rfl

/-! ### The degree `0` term -/

/-- **The identification of the degree `0` terms is linear**, for the same reason as in degree
`-1`. -/
theorem naiveCotangentStalkCotangentSpaceEquiv_linear
    (s : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x))
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (tensorDifferentialsSheaf (Opens.grothendieckTopology X) A
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B))
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))).val.presheaf x)) :
    letI := algebraStalk a.hom x
    letI := moduleRingStalkCotangentSpace A B a x
    naiveCotangentStalkCotangentSpaceEquiv A B a x (s • ξ) =
      s • naiveCotangentStalkCotangentSpaceEquiv A B a x ξ := by
  let := algebraStalk a.hom x
  let := moduleRingStalkCotangentSpace A B a x
  obtain ⟨r, hr, hs⟩ := exists_stalkMap_presentation_eq A B a x s
  refine Eq.trans (congrArg (naiveCotangentStalkCotangentSpaceEquiv A B a x)
    (Eq.trans (congrArg (fun t : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x) => t • ξ) hs.symm)
      (tensorDifferentialsSheafStalk_ringCat_smul_eq A
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B))
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x r ξ).symm)) ?_
  refine Eq.trans (naiveCotangentStalkCotangentSpaceEquiv_semilinear A B a x r ξ) ?_
  exact congrArg (fun c : ToType (TopCat.Presheaf.stalk B.obj x) =>
    c • naiveCotangentStalkCotangentSpaceEquiv A B a x ξ) hr

/-- **The degree `0` terms agree as modules over the stalk of `B`.** -/
def naiveCotangentStalkCotangentSpaceLinearEquiv :
    letI := algebraStalk a.hom x
    letI := moduleRingStalkCotangentSpace A B a x
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) A
          (freeAlgebraSheaf (Opens.grothendieckTopology X) A
            (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
            (underlyingPresheaf (Opens.grothendieckTopology X) B))
          (presentation (Opens.grothendieckTopology X) A B a
            (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))).val.presheaf x)
      ≃ₗ[ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x)]
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
        (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension.CotangentSpace :=
  letI := algebraStalk a.hom x
  letI := moduleRingStalkCotangentSpace A B a x
  (naiveCotangentStalkCotangentSpaceEquiv A B a x).toLinearEquiv
    (naiveCotangentStalkCotangentSpaceEquiv_linear A B a x)

/-- The linear equivalence `naiveCotangentStalkCotangentSpaceLinearEquiv` agrees on elements
with `naiveCotangentStalkCotangentSpaceEquiv`. -/
theorem naiveCotangentStalkCotangentSpaceLinearEquiv_apply
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (tensorDifferentialsSheaf (Opens.grothendieckTopology X) A
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B))
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))).val.presheaf x)) :
    letI := algebraStalk a.hom x
    naiveCotangentStalkCotangentSpaceLinearEquiv A B a x ξ =
      naiveCotangentStalkCotangentSpaceEquiv A B a x ξ := rfl

/-! ### The differential -/

/-- **The stalk of the differential of `NL_{B/A}` is linear** over the stalk of the sheaf of
rings underlying `B`.  It is the stalk of a morphism of sheaves of `B`-modules, and this is read
off the identification with the cotangent complex of `Aₓ → Bₓ`, which is linear. -/
theorem conormalSequenceStalkMapF_smul
    (s : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x))
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (conormalSheaf (Opens.grothendieckTopology X)
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))).val.presheaf x)) :
    conormalSequenceStalkMapF A (freeAlgebraSheaf (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B))
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x (s • ξ) =
      s • conormalSequenceStalkMapF A (freeAlgebraSheaf (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B))
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x ξ := by
  let := algebraStalk a.hom x
  let := moduleRingStalkCotangent A B a x
  let := moduleRingStalkCotangentSpace A B a x
  refine (naiveCotangentStalkCotangentSpaceEquiv A B a x).injective ?_
  refine Eq.trans (naiveCotangentStalk_d_eq_cotangentComplex A B a x (s • ξ)) ?_
  refine Eq.trans (congrArg (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
      (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension.cotangentComplex
    (naiveCotangentStalkCotangentEquiv_linear A B a x s ξ)) ?_
  refine Eq.trans (map_smul (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
      (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension.cotangentComplex
    (SemilinearStalk.commStalkRingEquiv B.obj x s) _) ?_
  refine Eq.trans ?_ (naiveCotangentStalkCotangentSpaceEquiv_linear A B a x s _).symm
  exact congrArg (fun y : (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
      (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension.CotangentSpace =>
    (SemilinearStalk.commStalkRingEquiv B.obj x s) • y)
    (naiveCotangentStalk_d_eq_cotangentComplex A B a x ξ).symm

/-- The stalk at `x` of the differential of `NL_{B/A}`, as a linear map over the stalk of the
sheaf of rings underlying `B`.  The underlying function is
`Stacks.Sites.Conormal.conormalSequenceStalkMapF`. -/
def naiveCotangentStalkDifferential :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (conormalSheaf (Opens.grothendieckTopology X)
          (freeAlgebraSheaf (Opens.grothendieckTopology X) A
            (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
          (presentation (Opens.grothendieckTopology X) A B a
            (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))).val.presheaf x)
      →ₗ[ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x)]
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) A
          (freeAlgebraSheaf (Opens.grothendieckTopology X) A
            (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
            (underlyingPresheaf (Opens.grothendieckTopology X) B))
          (presentation (Opens.grothendieckTopology X) A B a
            (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))).val.presheaf x) where
  toFun := conormalSequenceStalkMapF A (freeAlgebraSheaf (Opens.grothendieckTopology X) A
    (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B))
    (presentation (Opens.grothendieckTopology X) A B a
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x
  map_add' := map_add _
  map_smul' := conormalSequenceStalkMapF_smul A B a x

/-- The linear map `naiveCotangentStalkDifferential` agrees on elements with the stalk map
`conormalSequenceStalkMapF` of the conormal sequence. -/
theorem naiveCotangentStalkDifferential_apply
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (conormalSheaf (Opens.grothendieckTopology X)
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))).val.presheaf x)) :
    naiveCotangentStalkDifferential A B a x ξ =
      conormalSequenceStalkMapF A (freeAlgebraSheaf (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B))
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x ξ := rfl

/-- **Stacks 0D09 as an isomorphism of two-term complexes of `Bₓ`-modules.**
`NL_{B/A, x} = NL_{Bₓ/Aₓ}`: the stalk at `x` of the differential of `NL_{B/A}`, conjugated by the
two linear identifications of terms, is the cotangent complex of
`Algebra.Generators.self Aₓ Bₓ`, which is the differential of `NL_{Bₓ/Aₓ}`.

All four maps in the square are linear over the stalk of the sheaf of rings underlying `B`: the
two identifications by
`Stacks.SheafOfModules.naiveCotangentStalkCotangentLinearEquiv` and
`Stacks.SheafOfModules.naiveCotangentStalkCotangentSpaceLinearEquiv`, the stalk of the
differential by `Stacks.SheafOfModules.naiveCotangentStalkDifferential`, and the cotangent
complex because it is `Bₓ`-linear and the action of the stalk of the sheaf of rings is that of
`Bₓ` along `SemilinearStalk.commStalkRingEquiv`
(`Stacks.SheafOfModules.moduleRingStalkCotangent`).  So this commuting square is an isomorphism
of two-term complexes of modules over the stalk of `B`, which is the form in which the tag is
consumed.  The additive form, with semilinearity over the stalk `(A[B])ₓ → Bₓ` of the canonical
presentation in place of linearity, is
`Stacks.SheafOfModules.naiveCotangentStalk_eq_naiveCotangentComplexStalk`.

No hypothesis is imposed on `X`, on `a` or on `x`. -/
theorem naiveCotangentStalk_eq_naiveCotangentComplexStalk_linear
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (conormalSheaf (Opens.grothendieckTopology X)
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))).val.presheaf x)) :
    letI := algebraStalk a.hom x
    letI := moduleRingStalkCotangent A B a x
    letI := moduleRingStalkCotangentSpace A B a x
    naiveCotangentStalkCotangentSpaceLinearEquiv A B a x
        (naiveCotangentStalkDifferential A B a x ξ) =
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
          (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension.cotangentComplex
        (naiveCotangentStalkCotangentLinearEquiv A B a x ξ) :=
  naiveCotangentStalk_d_eq_cotangentComplex A B a x ξ

end Linear

end Stacks.SheafOfModules

end

end
