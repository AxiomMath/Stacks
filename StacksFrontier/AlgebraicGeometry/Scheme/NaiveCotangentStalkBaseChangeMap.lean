module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineStalkLegsSquare
public import StacksFrontier.CategoryTheory.Sites.Point.OpensPointSheafStalkCounitApply
public import StacksFrontier.LinearAlgebra.TensorProduct.BaseRingAddEquiv
public import StacksFrontier.RingTheory.NaiveCotangent.LocalizationBaseAndTarget

/-!
# The stalk of the base change of the naive cotangent complex of a tower

Let `a : A ⟶ B` and `b : B ⟶ C` be morphisms of sheaves of commutative rings on a topological
space `T` and let `z` be a point of `T`.  `Stacks.SheafOfModules.baseChangeNaiveCotangentComplex`
is the complex `NL_{B/A} ⊗_B C` of sheaves of `C`-modules, the source of the canonical map of
Stacks 0E1Y.  This file identifies its stalk at `z`, degreewise, with the base change to `C_z` of
the naive cotangent complex of the canonical presentation of `B_z` over `A_z`:

`(NL_{B/A} ⊗_B C)_z ≅ C_z ⊗_{B_z} I/I²` in degree `-1`, and
`(NL_{B/A} ⊗_B C)_z ≅ C_z ⊗_{B_z} (Ω_{A_z[B_z]} ⊗ B_z)` in degree `0`,

which are the two terms of `NaiveCotangent.nlExtensionBaseChange` for the extension
`Algebra.Generators.self A_z B_z`.

Two different rings compute the stalk of a sheaf of commutative rings at `z`, and the two halves
of the identification are stated over different ones.  The interchange
`Opens.stalkTowerExtendScalarsXIso` of extension of scalars with taking topological stalks is
stated over the `CommRingCat`-valued *fibre* at the point of the site of opens attached to `z`,
because that is the ring extension of scalars of sheaves of modules becomes extension of scalars
of modules over; the two legs of Stacks 0D09
(`Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOneLinear` and `stalkLegZeroLinear`) are
stated over the `RingCat`-valued *stalk*, and the extension `Algebra.Generators.self A_z B_z`
lives over the `CommRingCat`-valued stalk.  So the base of the tensor product has to be moved,
and `TensorProduct.addEquivOfRingEquiv` is what moves it: the fibre and the
`CommRingCat`-valued stalk are isomorphic by `Opens.pointFiberStalkIso`, and the two
comparisons out of the fibre — `Opens.commRingFiberStalkHom` into the `RingCat`-valued stalk and
`Opens.pointFiberStalkIso` into the `CommRingCat`-valued one — agree
(`Stacks.NaiveCotangentStalkBaseChange.commStalkRingEquiv_commRingFiberStalkHom`), which is what
makes the two factors semilinear along that isomorphism.

## Main definitions

* `Stacks.NaiveCotangentStalkBaseChange.fiberStalkRingEquiv`: the fibre of a sheaf of commutative
  rings at the point of the site of opens attached to `z`, identified with its stalk at `z`.
* `Stacks.NaiveCotangentStalkBaseChange.stalkBaseChangeAddEquivNegOne` and
  `stalkBaseChangeAddEquivZero`: **the two degreewise identifications.**

## Main results

* `Stacks.NaiveCotangentStalkBaseChange.fiberStalkRingEquiv_stalkRingHom`: the identification of
  the fibre with the stalk carries the fibre of a morphism to its stalk.
* `Stacks.NaiveCotangentStalkBaseChange.commStalkRingEquiv_commRingFiberStalkHom`: the two
  comparison maps out of the fibre agree.
* `Stacks.NaiveCotangentStalkBaseChange.fiberStalkRingEquiv_smul_fiber`,
  `stalkLegNegOneLinear_smul_fiber` and `stalkLegZeroLinear_smul_fiber`: the semilinearity of the
  two factors of the tensor product along that identification, which is the input
  `TensorProduct.addEquivOfRingEquiv` consumes.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the base-change map of
  naive cotangent complexes of a tower of sheaves of rings.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 04EH](https://stacks.math.columbia.edu/tag/04EH), stalks at a point of a
  site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules
open scoped ChangeOfRings

universe u

noncomputable section

namespace Stacks.NaiveCotangentStalkBaseChange

open Stacks.SheafOfModules Stacks.NaiveCotangentAffineStalkLegs
open Stacks.RelativeDifferentialStalk (algebraStalk)

variable {T : TopCat.{u}}
  (A B C : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (a : A ⟶ B) (b : B ⟶ C) (z : T)

/-! ### The fibre of a sheaf of commutative rings and its stalk -/

/-- The fibre at the point of the site of opens attached to `z` of a sheaf of commutative rings,
identified with its stalk at `z`, as a ring isomorphism.  This is
`Opens.pointFiberStalkIso`. -/
abbrev fiberStalkRingEquiv :
    ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) B.obj) ≃+*
      ToType (TopCat.Presheaf.stalk B.obj z) :=
  (Opens.pointFiberStalkIso z B.obj).commRingCatIsoToRingEquiv

/-- **The identification of the fibre with the stalk is natural**: it carries the fibre of a
morphism of sheaves of commutative rings to its stalk. -/
theorem fiberStalkRingEquiv_stalkRingHom
    (r : ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) B.obj)) :
    fiberStalkRingEquiv C z
        (Stacks.SitePointBaseChange.stalkRingHom b.hom
          (Opens.pointGrothendieckTopology z) r) =
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map b.hom).hom
        (fiberStalkRingEquiv B z r) :=
  DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (Opens.stalkRingHom_comp_pointFiberStalkHom z b.hom)) r

/-- **The two comparison maps out of the fibre of a sheaf of commutative rings agree**: the
comparison `Opens.commRingFiberStalkHom` with the `RingCat`-valued stalk, followed by the
identification of that stalk with the `CommRingCat`-valued one, is the identification
`Opens.pointFiberStalkIso` of the fibre with the `CommRingCat`-valued stalk. -/
theorem commStalkRingEquiv_commRingFiberStalkHom
    (r : ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) B.obj)) :
    SemilinearStalk.commStalkRingEquiv B.obj z
        ((Opens.commRingFiberStalkHom z B).hom r) =
      fiberStalkRingEquiv B z r :=
  DFunLike.congr_fun (congrArg RingCat.Hom.hom
    (Opens.commRingFiberStalkHom_comp_commStalkIso z B)) r

/-- **The identification of the fibre with the stalk is semilinear for the action of the fibre of
`B` on the fibre of `C`**: a scalar of the fibre of `B` acts through the fibre of `b`, and the
identification carries that action to the action of the stalk of `B` on the stalk of `C` through
the stalk of `b`. -/
theorem fiberStalkRingEquiv_smul_fiber
    (r : ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) B.obj))
    (n : ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) C.obj)) :
    letI : Module (ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) B.obj))
        (ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) C.obj)) :=
      Module.compHom _ (Stacks.SitePointBaseChange.stalkRingHom b.hom
        (Opens.pointGrothendieckTopology z))
    letI := algebraStalk b.hom z
    fiberStalkRingEquiv C z (r • n) =
      fiberStalkRingEquiv B z r • fiberStalkRingEquiv C z n := by
  let _ : Module (ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) B.obj))
      (ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) C.obj)) :=
    Module.compHom _ (Stacks.SitePointBaseChange.stalkRingHom b.hom
      (Opens.pointGrothendieckTopology z))
  let _ := algebraStalk b.hom z
  change fiberStalkRingEquiv C z
      (Stacks.SitePointBaseChange.stalkRingHom b.hom
        (Opens.pointGrothendieckTopology z) r * n) = _
  refine Eq.trans (map_mul (fiberStalkRingEquiv C z) _ _) ?_
  refine Eq.trans (congrArg (fun t => t * fiberStalkRingEquiv C z n)
    (fiberStalkRingEquiv_stalkRingHom B C b z r)) ?_
  rfl

/-- **The degree `-1` leg is semilinear for the action of the fibre of `B`**: a scalar of the
fibre acts on the stalk of the term through `Opens.commRingFiberStalkHom`, and the leg carries
that action to the action of the stalk of `B` on the conormal module through the identification
of the fibre with the stalk. -/
theorem stalkLegNegOneLinear_smul_fiber
    (r : ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) B.obj))
    (m : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
        (-1)).val.presheaf z)) :
    letI := algebraStalk a.hom z
    stalkLegNegOneLinear A B a z
        (@SMul.smul (ToType (TopCat.Presheaf.stalk (Tensor.ringSheaf B).obj z)) _
          inferInstance ((Opens.commRingFiberStalkHom z B).hom r) m) =
      fiberStalkRingEquiv B z r • stalkLegNegOneLinear A B a z m := by
  let _ := algebraStalk a.hom z
  refine Eq.trans (stalkLegNegOne_smul A B a z ((Opens.commRingFiberStalkHom z B).hom r) m) ?_
  exact congrArg (fun t : ToType (TopCat.Presheaf.stalk B.obj z) =>
      t • stalkLegNegOneLinear A B a z m)
    (commStalkRingEquiv_commRingFiberStalkHom B z r)

/-- **The degree `0` leg is semilinear for the action of the fibre of `B`.**  The degree `0`
analogue of `stalkLegNegOneLinear_smul_fiber`. -/
theorem stalkLegZeroLinear_smul_fiber
    (r : ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) B.obj))
    (m : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
        0).val.presheaf z)) :
    letI := algebraStalk a.hom z
    stalkLegZeroLinear A B a z
        (@SMul.smul (ToType (TopCat.Presheaf.stalk (Tensor.ringSheaf B).obj z)) _
          inferInstance ((Opens.commRingFiberStalkHom z B).hom r) m) =
      fiberStalkRingEquiv B z r • stalkLegZeroLinear A B a z m := by
  let _ := algebraStalk a.hom z
  refine Eq.trans (stalkLegZero_smul A B a z ((Opens.commRingFiberStalkHom z B).hom r) m) ?_
  exact congrArg (fun t : ToType (TopCat.Presheaf.stalk B.obj z) =>
      t • stalkLegZeroLinear A B a z m)
    (commStalkRingEquiv_commRingFiberStalkHom B z r)

/-! ### The stalk of the base change of the naive cotangent complex -/

/-- **The stalk at `z` of the degree `-1` term of `NL_{B/A} ⊗_B C`.**  It is
`C_z ⊗_{B_z} I/I²`, for `I/I²` the conormal module of the canonical presentation of `B_z` over
`A_z`: the interchange `Opens.stalkTowerExtendScalarsXIso` computes it as the base change along
the *fibre* of `b` of the stalk of the degree `-1` term of `NL_{B/A}`, and
`TensorProduct.addEquivOfRingEquiv` moves that base change to the stalk of `b` along the
identification of the fibres with the stalks and the degree `-1` leg of Stacks 0D09. -/
def stalkBaseChangeAddEquivNegOne :
    letI := algebraStalk a.hom z
    letI := algebraStalk b.hom z
    ToType ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z ⋙
          ModuleCat.restrictScalars.{u} (Opens.commRingFiberStalkHom z C).hom).obj
        (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
            (Opens.grothendieckTopology T) B C b).obj
          (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a)).X
            (-1))) ≃+
      TensorProduct (ToType (TopCat.Presheaf.stalk B.obj z))
        (ToType (TopCat.Presheaf.stalk C.obj z))
        (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
          (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.Cotangent :=
  letI := algebraStalk a.hom z
  letI := algebraStalk b.hom z
  letI := moduleRingStalkCotangent A B a z
  (Opens.stalkTowerExtendScalarsXAddEquiv z B C b
      (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a) (-1)).trans
    (TensorProduct.addEquivOfRingEquiv (fiberStalkRingEquiv B z)
      (fiberStalkRingEquiv C z).toAddEquiv (stalkLegNegOneLinear A B a z).toAddEquiv
      (fiberStalkRingEquiv_smul_fiber B C b z) (stalkLegNegOneLinear_smul_fiber A B a z))

/-- **The stalk at `z` of the degree `0` term of `NL_{B/A} ⊗_B C`.**  It is
`C_z ⊗_{B_z} (Ω_{A_z[B_z]} ⊗ B_z)`; the degree `0` analogue of
`stalkBaseChangeAddEquivNegOne`. -/
def stalkBaseChangeAddEquivZero :
    letI := algebraStalk a.hom z
    letI := algebraStalk b.hom z
    ToType ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z ⋙
          ModuleCat.restrictScalars.{u} (Opens.commRingFiberStalkHom z C).hom).obj
        (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
            (Opens.grothendieckTopology T) B C b).obj
          (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a)).X 0)) ≃+
      TensorProduct (ToType (TopCat.Presheaf.stalk B.obj z))
        (ToType (TopCat.Presheaf.stalk C.obj z))
        (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
          (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.CotangentSpace :=
  letI := algebraStalk a.hom z
  letI := algebraStalk b.hom z
  letI := moduleRingStalkCotangentSpace A B a z
  (Opens.stalkTowerExtendScalarsXAddEquiv z B C b
      (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a) 0).trans
    (TensorProduct.addEquivOfRingEquiv (fiberStalkRingEquiv B z)
      (fiberStalkRingEquiv C z).toAddEquiv (stalkLegZeroLinear A B a z).toAddEquiv
      (fiberStalkRingEquiv_smul_fiber B C b z) (stalkLegZeroLinear_smul_fiber A B a z))

end Stacks.NaiveCotangentStalkBaseChange

end

end
