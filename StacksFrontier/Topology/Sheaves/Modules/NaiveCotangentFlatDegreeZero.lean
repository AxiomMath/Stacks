module

public import StacksFrontier.AlgebraicGeometry.RingedSpace.NaiveCotangentComplex
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineStalkLegsLinear
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFreeRetract

/-!
# The degree-zero term of the naive cotangent complex is flat

For a morphism `a : A ⟶ B` of sheaves of commutative rings on a topological space, the degree
`0` term of `NL_{B/A}` is the scalar extension to `B` of the relative differentials of the
canonical polynomial presentation of `B` over `A`.  Its stalk at a point `x` is the cotangent
space of the canonical presentation of `B_x` over `A_x`
(`Stacks.NaiveCotangentAffineStalkLegs.stalkLegZeroLinear`), which is free on the underlying
set of `B_x`.  Flatness of a sheaf of modules is a stalkwise condition (Stacks 05NE), so the
degree `0` term is a flat `B`-module.

## Main results

* `Stacks.SheafOfModules.isFlat_naiveCotangentComplex_X_zero`: the degree `0` term of
  `NL_{B/A}` is a flat `B`-module.

## Implementation notes

Three scalar rings are in play at a point `x`: the `CommRingCat`-valued stalk `B_x`, over which
the cotangent space of `Algebra.Generators.self A_x B_x` has its basis; the `RingCat`-valued
stalk of the sheaf of rings underlying `B`, over which
`Stacks.NaiveCotangentAffineStalkLegs.stalkLegZeroLinear` is linear; and again the
`CommRingCat`-valued stalk, which is the one
`AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat` asks about.  The two are exchanged by
`SemilinearStalk.commStalkRingEquiv`, whose compatibility with
both scalar actions is `AlgebraicGeometry.SheafOfModules.commStalkRingEquiv_smul_eq'` on the
module stalk and definitional on the cotangent space, whose `RingCat`-action is
`Module.compHom` along that very equivalence.  `Module.Basis.mapCoeffs` carries the basis across
each exchange.

The flatness predicate is written out as `AlgebraicGeometry.SheafOfModules.IsFlat`, the one
taking a sheaf of modules over `Stacks.SheafOfModules.Tensor.ringSheaf` — the ring sheaf that
`naiveCotangentComplex` produces and that `isFlat_iff_stalk_flat` is stated for.  The bare name
`IsFlat` cannot be used: inside `namespace Stacks.SheafOfModules` it resolves to
`Stacks.SheafOfModules.IsFlat`, which takes its argument over
`Stacks.commRingSheafToRingSheaf` instead, and although the two ring sheaves are definitionally
equal, the argument of `Stacks.SheafOfModules.IsFlat` leaves its sheaf of commutative rings to
be recovered from `Stacks.commRingSheafToRingSheaf ?O`, which unification cannot do.

## References

* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW), the naive cotangent
  complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE), flatness of a sheaf of
  modules is a stalkwise condition.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.SheafOfModules (isFlat_iff_stalk_flat commStalkRingEquiv_smul_eq')
open Stacks.RelativeDifferentialStalk (algebraStalk)
open Stacks.NaiveCotangentAffineStalkLegs (stalkLegZeroLinear)

universe u

noncomputable section

namespace Stacks.SheafOfModules

variable {T : TopCat.{u}}
  (A B : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}) (a : A ⟶ B)

/-- **The degree `0` term of `NL_{B/A}` is a flat `B`-module.**  Flatness is stalkwise
(Stacks 05NE), and the stalk at `x` is the cotangent space of the canonical presentation of
`B_x` over `A_x` by `Stacks.NaiveCotangentAffineStalkLegs.stalkLegZeroLinear`, which is free on
the underlying set of `B_x` by `Algebra.Generators.cotangentSpaceBasis`. -/
theorem isFlat_naiveCotangentComplex_X_zero :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X 0) := by
  refine (isFlat_iff_stalk_flat B _).2 fun x => ?_
  let : Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) B.obj x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := T)
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
          0).val.presheaf x) :=
    inferInstanceAs (Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) B.obj x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := T)
        ((id ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
          0).val : _root_.PresheafOfModules.{u}
            (B.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})).presheaf) x))
  let := algebraStalk a.hom x
  let := moduleRingStalkCotangentSpace A B a x
  let e : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x) ≃+*
      ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) B.obj x) :=
    SemilinearStalk.commStalkRingEquiv B.obj x
  have hsmul : ∀ (c : ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) B.obj x))
      (y : (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
        (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension.CotangentSpace),
      e.symm c • y = c • y := fun c y => by
    show e (e.symm c) • y = c • y
    rw [e.apply_symm_apply]
  exact @Module.Flat.of_free _ _ _ _ _
    (Module.Free.of_basis
      ((((Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
        (ToType (TopCat.Presheaf.stalk B.obj x))).cotangentSpaceBasis.mapCoeffs
          e.symm hsmul).map (stalkLegZeroLinear A B a x).symm).mapCoeffs e
            (commStalkRingEquiv_smul_eq' B x _)))

/-- **The degree `0` term of `NL_{X/Y}` is flat**, for a morphism of ringed spaces. -/
theorem isFlat_ringedSpace_naiveCotangentComplex_X_zero {S T : AlgebraicGeometry.RingedSpace.{u, u}}
    (h : S ⟶ T) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      ((AlgebraicGeometry.RingedSpace.naiveCotangentComplex h).X 0) :=
  isFlat_naiveCotangentComplex_X_zero _ _ _

end Stacks.SheafOfModules

end

end
