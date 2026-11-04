module

public import StacksFrontier.AlgebraicGeometry.FiberCotangentAssembly.Transport
public import StacksFrontier.AlgebraicGeometry.FiberCotangentIdentification.Fiber

/-!
# The two scalar structures on the local ring of a scheme-theoretic fibre

Let `f : X ⟶ S` be a morphism of schemes, `x ∈ X`, `s = f x`, and let `𝒪_{X_s,x}` be the local
ring of the fibre `X_s` at the canonical point over `x`. Each of the residue fields `κ(x)` and
`κ(s)` relates to `𝒪_{X_s,x}` in two ways, and this file identifies them.

Over `κ(x)`: the composite `𝒪_{X,x} → 𝒪_{X_s,x} → κ(x)` of the map induced by the inclusion of
the fibre with the one induced by the canonical residue-field point is the residue map of `x`.
Over `κ(s)`: the structure obtained from the fibre's structural morphism `X_s ⟶ Spec κ(s)`,
whose source is the stalk of `Spec κ(s)`, agrees with the structure obtained from `𝒪_{X,x}` by
`Stacks.FiberCotangentIdentification.quotientEquivFiberStalk`.

## Main definitions

* `Stacks.FiberCotangentAssembly.specResidueStalkIso`: the stalk of `Spec κ(s)` at the image of
  the canonical point of the fibre, identified with `κ(s)`.
* `Stacks.FiberCotangentAssembly.algebraSpecResidueStalk`: `κ(s)` acting on that stalk through
  the identification.

## Main results

* `Stacks.FiberCotangentAssembly.stalkClosedPointTo_asFiberHom_comp`: the composite
  `𝒪_{X,x} → 𝒪_{X_s,x} → κ(x)` is `AlgebraicGeometry.Scheme.residue`.
* `Stacks.FiberCotangentAssembly.isScalarTower_residueField`: the same statement as a scalar
  tower.
* `Stacks.FiberCotangentAssembly.residue_specResidueStalkIso_inv_stalkMap`: the two `κ(s)`-algebra
  structures on `𝒪_{X_s,x}` agree after the residue map of `s`.
* `Stacks.FiberCotangentAssembly.isScalarTower_specResidueStalk`: the two agree, as a scalar
  tower.
* `Stacks.FiberCotangentAssembly.surjective_algebraMap_specResidueStalk`: `κ(s)` surjects onto
  the stalk of `Spec κ(s)`.

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open Stacks.FiberCotangentIdentification
open Stacks.RelativeDifferentialStalkMap

universe u

namespace Stacks.FiberCotangentAssembly

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-! ### The residue field of `x` -/

/-- **The composite `𝒪_{X,x} → 𝒪_{X_s,x} → κ(x)` is the residue map of `x`.**  The first map is
induced by the inclusion of the scheme-theoretic fibre, the second by the canonical
residue-field point of the fibre. -/
public theorem stalkClosedPointTo_asFiberHom_comp :
    (X.presheaf.stalkCongr (Inseparable.of_eq (fiberι_fiberPoint f x).symm)).hom ≫
        Scheme.Hom.stalkMap (f.fiberι (f x)) (fiberPoint f x) ≫
          Scheme.stalkClosedPointTo (f.asFiberHom x) =
      X.residue x := by
  have hcomp := Scheme.stalkClosedPointTo_comp (f.asFiberHom x) (f.fiberι (f x))
  have htr := stalkClosedPointTo_eq_of_eq (X := X) (Scheme.Hom.asFiberHom_fiberι f x)
    (Inseparable.of_eq (by rw [Scheme.Hom.asFiberHom_fiberι]))
  rw [← hcomp, htr, stalkClosedPointTo_fromSpecResidueField]
  exact stalkCongr_hom_comp_three _ _ _ _ _

/-- **The scalar tower `𝒪_{X,x} → 𝒪_{X_s,x} → κ(x)`**, the first map induced by the inclusion
of the fibre, the second by the canonical residue-field point of the fibre, and the composite
the residue map of `x`. -/
public theorem isScalarTower_residueField :
    letI := algebraStalkFiberStalk f x
    letI : Algebra (ToType ((f.fiber (f x)).presheaf.stalk (fiberPoint f x)))
        (ToType (X.residueField x)) :=
      (Scheme.stalkClosedPointTo (f.asFiberHom x)).hom.toAlgebra
    letI : Algebra (ToType (X.sheaf.presheaf.stalk x)) (ToType (X.residueField x)) :=
      (X.residue x).hom.toAlgebra
    IsScalarTower (ToType (X.sheaf.presheaf.stalk x))
      (ToType ((f.fiber (f x)).presheaf.stalk (fiberPoint f x)))
      (ToType (X.residueField x)) := by
  let := algebraStalkFiberStalk f x
  let _ : Algebra (ToType ((f.fiber (f x)).presheaf.stalk (fiberPoint f x)))
      (ToType (X.residueField x)) :=
    (Scheme.stalkClosedPointTo (f.asFiberHom x)).hom.toAlgebra
  let _ : Algebra (ToType (X.sheaf.presheaf.stalk x)) (ToType (X.residueField x)) :=
    (X.residue x).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  simp only [RingHom.algebraMap_toAlgebra]
  exact congrArg CommRingCat.Hom.hom (stalkClosedPointTo_asFiberHom_comp f x).symm

/-! ### The residue field of `s = f x` -/

/-- The stalk of `Spec κ(s)` at the image of the canonical point of the fibre, identified with
`κ(s)`: the comparison of stalks with the stalk at the closed point, followed by
`AlgebraicGeometry.stalkClosedPointIso`. -/
public noncomputable abbrev specResidueStalkIso :
    (Spec (S.residueField (f x))).presheaf.stalk
        ((f.fiberToSpecResidueField (f x)) (fiberPoint f x)) ≅ S.residueField (f x) :=
  (Spec (S.residueField (f x))).presheaf.stalkCongr
      (Inseparable.of_eq
        (Scheme.Hom.fiberToSpecResidueField_apply f (f x) (fiberPoint f x))) ≪≫
    stalkClosedPointIso (S.residueField (f x))

/-- **The stalk map of `AlgebraicGeometry.Scheme.fromSpecResidueField` is the residue map**,
read through `AlgebraicGeometry.stalkClosedPointIso`. -/
public theorem stalkMap_fromSpecResidueField (s : S) :
    Scheme.Hom.stalkMap (S.fromSpecResidueField s)
        (IsLocalRing.closedPoint (S.residueField s)) =
      (S.presheaf.stalkCongr
          (.of_eq (S.fromSpecResidueField_apply s _))).hom ≫
        S.residue s ≫ (stalkClosedPointIso (S.residueField s)).inv := by
  have h0 : Scheme.stalkClosedPointTo (S.fromSpecResidueField s) =
      Scheme.Hom.stalkMap (S.fromSpecResidueField s)
          (IsLocalRing.closedPoint (S.residueField s)) ≫
        (stalkClosedPointIso (S.residueField s)).hom := rfl
  have h := h0 ▸ stalkClosedPointTo_fromSpecResidueField (X := S) s
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The two `κ(s)`-algebra structures on the local ring of the fibre agree after the residue
map of `s`.**  On the left, `κ(s)` acts through the stalk of the fibre's structural morphism to
`Spec κ(s)`; on the right, `𝒪_{S,s}` acts through `𝒪_{X,x}` and the inclusion of the fibre. -/
public theorem residue_specResidueStalkIso_inv_stalkMap :
    S.residue (f x) ≫ (specResidueStalkIso f x).inv ≫
        Scheme.Hom.stalkMap (f.fiberToSpecResidueField (f x)) (fiberPoint f x) =
      Scheme.Hom.stalkMap f x ≫
        (X.presheaf.stalkCongr (Inseparable.of_eq (fiberι_fiberPoint f x).symm)).hom ≫
          Scheme.Hom.stalkMap (f.fiberι (f x)) (fiberPoint f x) := by
  have htr := stalkMap_eq_of_eq (Scheme.Hom.fiber_fac f (f x)) (fiberPoint f x)
    (Inseparable.of_eq (by rw [Scheme.Hom.fiber_fac]))
  have hsrc := Scheme.Hom.stalkMap_comp (f.fiberι (f x)) f (fiberPoint f x)
  have htgt := Scheme.Hom.stalkMap_comp (f.fiberToSpecResidueField (f x))
    (S.fromSpecResidueField (f x)) (fiberPoint f x)
  have hpt := stalkMap_eq_of_point_eq (S.fromSpecResidueField (f x))
    (Scheme.Hom.fiberToSpecResidueField_apply f (f x) (fiberPoint f x))
    (Inseparable.of_eq (Scheme.Hom.fiberToSpecResidueField_apply f (f x)
      (fiberPoint f x)).symm)
    (Inseparable.of_eq (by rw [Scheme.Hom.fiberToSpecResidueField_apply]))
  have hF := stalkMap_fromSpecResidueField (S := S) (f x)
  have hfpt := stalkMap_eq_of_point_eq f (fiberι_fiberPoint f x)
    (Inseparable.of_eq (fiberι_fiberPoint f x).symm)
    (Inseparable.of_eq (by rw [fiberι_fiberPoint]))
  have hA : f ((f.fiberι (f x)) (fiberPoint f x)) = f x := by rw [fiberι_fiberPoint]
  refine (cancel_epi (S.presheaf.stalkCongr (Inseparable.of_eq hA)).hom).mp ?_
  rw [hfpt] at hsrc
  simp only [Category.assoc] at hsrc
  rw [← hsrc, htr, htgt, hpt, hF]
  simp only [Category.assoc, Iso.trans_inv, stalkCongr_hom_comp_assoc]
  exact stalkCongr_hom_eq_comp _ _ _ _ _

/-- `κ(s)` acting on the stalk of `Spec κ(s)` at the image of the canonical point of the fibre,
through `Stacks.FiberCotangentAssembly.specResidueStalkIso`. -/
public noncomputable abbrev algebraSpecResidueStalk :
    Algebra (targetResidue f x)
      (ToType ((Spec (S.residueField (f x))).presheaf.stalk
        ((f.fiberToSpecResidueField (f x)) (fiberPoint f x)))) :=
  (specResidueStalkIso f x).inv.hom.toAlgebra

/-- **`κ(s)` surjects onto the stalk of `Spec κ(s)`**, the comparison being an isomorphism. -/
public theorem surjective_algebraMap_specResidueStalk :
    letI := algebraSpecResidueStalk f x
    Function.Surjective (algebraMap (targetResidue f x)
      (ToType ((Spec (S.residueField (f x))).presheaf.stalk
        ((f.fiberToSpecResidueField (f x)) (fiberPoint f x))))) := by
  let := algebraSpecResidueStalk f x
  exact fun b => ⟨(specResidueStalkIso f x).hom.hom b,
    congrArg (fun z => CommRingCat.Hom.hom z b) (specResidueStalkIso f x).hom_inv_id⟩

/-- **The scalar tower `κ(s) → 𝒪_{Spec κ(s), g x} → 𝒪_{X_s,x}`**, where `g : X_s ⟶ Spec κ(s)`
is the structural morphism of the fibre and `κ(s)` acts on `𝒪_{X_s,x}` through `𝒪_{X,x}`. -/
public theorem isScalarTower_specResidueStalk :
    letI := algebraStalkMap f x
    letI := algebraSpecResidueStalk f x
    letI : Algebra (ToType ((Spec (S.residueField (f x))).presheaf.stalk
        ((f.fiberToSpecResidueField (f x)) (fiberPoint f x))))
        (ToType ((f.fiber (f x)).presheaf.stalk (fiberPoint f x))) :=
      (Scheme.Hom.stalkMap (f.fiberToSpecResidueField (f x))
        (fiberPoint f x)).hom.toAlgebra
    letI := algebraResidueFiberStalk f x
    IsScalarTower (targetResidue f x)
      (ToType ((Spec (S.residueField (f x))).presheaf.stalk
        ((f.fiberToSpecResidueField (f x)) (fiberPoint f x))))
      (ToType ((f.fiber (f x)).presheaf.stalk (fiberPoint f x))) := by
  let := algebraStalkMap f x
  let := algebraSpecResidueStalk f x
  let _ : Algebra (ToType ((Spec (S.residueField (f x))).presheaf.stalk
      ((f.fiberToSpecResidueField (f x)) (fiberPoint f x))))
      (ToType ((f.fiber (f x)).presheaf.stalk (fiberPoint f x))) :=
    (Scheme.Hom.stalkMap (f.fiberToSpecResidueField (f x))
      (fiberPoint f x)).hom.toAlgebra
  let := algebraResidueFiberStalk f x
  refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun y => ?_)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hgoal := congrArg (fun z => CommRingCat.Hom.hom z a)
    (residue_specResidueStalkIso_inv_stalkMap f x)
  simp +zetaDelta only [RingHom.algebraMap_toAlgebra]
  exact (quotientEquivFiberStalk_mk f x ((f.stalkMap x).hom a)).trans hgoal.symm

end Stacks.FiberCotangentAssembly

end
