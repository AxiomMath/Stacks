module

public import StacksFrontier.AlgebraicGeometry.FiberCotangentIdentification.Kaehler
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Scheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local ring of a scheme-theoretic fibre is a base change

For a morphism of schemes `f : X ⟶ S` and a point `x` of `X`, **the local ring of the
scheme-theoretic fibre through `x`, at the canonical point of that fibre, is the base change of
`𝒪_{X,x}` along the residue field of `f x`**:

```
𝒪_{X_s, x}  =  𝒪_{X,x} ⊗[𝒪_{S,f x}] κ(f x),      s = f x.
```

## Main definitions

* `Stacks.FiberCotangentIdentification.fiberPoint`: the canonical point of the fibre through `x`,
  the image of the closed point of `Spec κ(x)` under `AlgebraicGeometry.Scheme.Hom.asFiberHom`.
* `Stacks.FiberCotangentIdentification.stalkToFiberStalk`: the map `𝒪_{X,x} → 𝒪_{X_s,x}` induced
  by the inclusion of the fibre.
* `Stacks.FiberCotangentIdentification.quotientEquivFiberStalk`: the local ring of the fibre as
  the quotient of `𝒪_{X,x}` by the extended maximal ideal of `𝒪_{S,f x}`.

## Main results

* `Stacks.FiberCotangentIdentification.isPushout_of_ringEquiv`: a square that a ring isomorphism
  identifies with a quotient square is a pushout square.
* `Stacks.FiberCotangentIdentification.fiberι_fiberPoint`: the canonical point of the fibre lies
  over `x`.
* `Stacks.FiberCotangentIdentification.quotientEquivFiberStalk_mk`: the identification of the
  local ring of the fibre with the quotient is induced by
  `Stacks.FiberCotangentIdentification.stalkToFiberStalk`.
* `Stacks.FiberCotangentIdentification.isPushout_fiberStalk`: the base-change statement above.

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
* [Stacks Project, Tag 0C0X](https://stacks.math.columbia.edu/tag/0C0X)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open Stacks.RelativeDifferentialStalkMap

universe u

namespace Stacks.FiberCotangentIdentification

/-- **A square identified with a quotient square by a ring isomorphism is a pushout square.**
If `e` identifies `B ⧸ IB` with `B'` compatibly with the maps out of `B`, then `A → A ⧸ I`,
`A → B`, `B'` is a pushout square. -/
public theorem isPushout_of_ringEquiv {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B']
    [Algebra A B] (I : Ideal A) [Algebra (A ⧸ I) B'] [Algebra B B'] [Algebra A B']
    [IsScalarTower A B B'] [IsScalarTower A (A ⧸ I) B']
    (e : (B ⧸ I.map (algebraMap A B)) ≃+* B')
    (he : ∀ b : B, e (Ideal.Quotient.mk (I.map (algebraMap A B)) b) = algebraMap B B' b) :
    Algebra.IsPushout A (A ⧸ I) B B' := by
  have hcomm : ∀ r : A ⧸ I, e (algebraMap (A ⧸ I) (B ⧸ I.map (algebraMap A B)) r) =
      algebraMap (A ⧸ I) B' r := by
    intro r
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    have h1 : algebraMap (A ⧸ I) (B ⧸ I.map (algebraMap A B)) (Ideal.Quotient.mk I a) =
        Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B a) := rfl
    rw [h1, he, ← IsScalarTower.algebraMap_apply A B B']
    exact IsScalarTower.algebraMap_apply A (A ⧸ I) B' a
  exact Algebra.IsPushout.of_equiv (h := isPushout_quotient I)
    (AlgEquiv.ofRingEquiv (f := e) hcomm) (RingHom.ext he)

/-- **The map to the residue field induced by `AlgebraicGeometry.Scheme.fromSpecResidueField` is
the residue map**, after the comparison of the stalks at the image of the closed point and
at `x`. -/
public theorem stalkClosedPointTo_fromSpecResidueField {X : Scheme.{u}} (x : X) :
    Scheme.stalkClosedPointTo (X.fromSpecResidueField x) =
      (X.presheaf.stalkCongr (.of_eq (X.fromSpecResidueField_apply x _))).hom ≫ X.residue x := by
  have : IsLocalHom (X.residue x).hom := inferInstanceAs (IsLocalHom (IsLocalRing.residue _))
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU ↦ ?_
  have h : X.fromSpecResidueField x = Spec.map (X.residue x) ≫ X.fromSpecStalk x := rfl
  exact (Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (X.residue x) U
      (h ▸ hxU : (Spec.map (X.residue x) ≫ X.fromSpecStalk x)
        (IsLocalRing.closedPoint (ToType (X.residueField x))) ∈ U)).trans
    (TopCat.Presheaf.germ_stalkSpecializes_assoc X.presheaf hxU
      (Specializes.of_eq (X.fromSpecResidueField_apply x _).symm) (X.residue x)).symm

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- The canonical point of the scheme-theoretic fibre through `x`: the image of the closed point
of `Spec κ(x)` under `AlgebraicGeometry.Scheme.Hom.asFiberHom`. -/
public noncomputable abbrev fiberPoint : f.fiber (f x) :=
  f.asFiberHom x (IsLocalRing.closedPoint (ToType (X.residueField x)))

/-- The canonical point of the fibre is the point `AlgebraicGeometry.Scheme.Hom.asFiber`. -/
public theorem fiberPoint_eq : fiberPoint f x = f.asFiber x :=
  Scheme.Hom.asFiberHom_apply f x _

/-- The canonical point of the fibre lies over `x`. -/
public theorem fiberι_fiberPoint : (f.fiberι (f x)) (fiberPoint f x) = x := by
  change (f.asFiberHom x ≫ f.fiberι (f x)) _ = x
  rw [Scheme.Hom.asFiberHom_fiberι]
  exact Scheme.fromSpecResidueField_apply x _

/-- The map `𝒪_{X,x} → 𝒪_{X_s,y}` induced by the inclusion of the fibre, at a point `y` of the
fibre lying over `x`. -/
public noncomputable abbrev stalkToFiberStalkAt (y : f.fiber (f x))
    (hy : (f.fiberι (f x)) y = x) :
    ToType (X.presheaf.stalk x) →+* ToType ((f.fiber (f x)).presheaf.stalk y) :=
  ((X.presheaf.stalkCongr (Inseparable.of_eq hy.symm)).hom ≫
    (f.fiberι (f x)).stalkMap y).hom

/-- The map `𝒪_{X,x} → 𝒪_{X_s,x}` induced by the inclusion of the fibre. -/
public noncomputable abbrev stalkToFiberStalk :
    ToType (X.presheaf.stalk x) →+* ToType ((f.fiber (f x)).presheaf.stalk (fiberPoint f x)) :=
  stalkToFiberStalkAt f x (fiberPoint f x) (fiberι_fiberPoint f x)

/-- The local ring of the fibre, at a point `y` equal to
`AlgebraicGeometry.Scheme.Hom.asFiber`, as the quotient of `𝒪_{X,x}` by the extended maximal
ideal of `𝒪_{S,f x}`. -/
@[ega "IV 16.5.13" "Identification O_{X_s"]
public noncomputable def quotientEquivFiberStalkAt (y : f.fiber (f x)) (hy : y = f.asFiber x) :
    letI := algebraStalkMap f x
    (ToType (X.sheaf.presheaf.stalk x) ⧸
        (IsLocalRing.maximalIdeal (ToType (S.presheaf.stalk (f x)))).map
          (algebraMap (ToType (S.presheaf.stalk (f x))) (ToType (X.sheaf.presheaf.stalk x))))
      ≃+* ToType ((f.fiber (f x)).presheaf.stalk y) := by
  subst hy
  exact quotientStalkEquivFiberStalk f x

/-- The local ring of the fibre as the quotient of `𝒪_{X,x}` by the extended maximal ideal of
`𝒪_{S,f x}`, at the canonical point `Stacks.FiberCotangentIdentification.fiberPoint`. -/
public noncomputable def quotientEquivFiberStalk :
    letI := algebraStalkMap f x
    (ToType (X.sheaf.presheaf.stalk x) ⧸
        (IsLocalRing.maximalIdeal (ToType (S.presheaf.stalk (f x)))).map
          (algebraMap (ToType (S.presheaf.stalk (f x))) (ToType (X.sheaf.presheaf.stalk x))))
      ≃+* ToType ((f.fiber (f x)).presheaf.stalk (fiberPoint f x)) :=
  quotientEquivFiberStalkAt f x (fiberPoint f x) (fiberPoint_eq f x)

/-- **The identification of the local ring of the fibre with the quotient is induced by the
inclusion of the fibre.** -/
public theorem quotientEquivFiberStalkAt_mk (y : f.fiber (f x)) (hy : y = f.asFiber x)
    (hy' : (f.fiberι (f x)) y = x) (b : ToType (X.presheaf.stalk x)) :
    letI := algebraStalkMap f x
    quotientEquivFiberStalkAt f x y hy
        (Ideal.Quotient.mk _ b) = stalkToFiberStalkAt f x y hy' b := by
  subst hy
  exact quotientStalkEquivFiberStalk_mk f x b

/-- **The identification of the local ring of the fibre with the quotient is induced by
`Stacks.FiberCotangentIdentification.stalkToFiberStalk`.** -/
public theorem quotientEquivFiberStalk_mk (b : ToType (X.presheaf.stalk x)) :
    letI := algebraStalkMap f x
    quotientEquivFiberStalk f x (Ideal.Quotient.mk _ b) = stalkToFiberStalk f x b :=
  quotientEquivFiberStalkAt_mk f x (fiberPoint f x) (fiberPoint_eq f x)
    (fiberι_fiberPoint f x) b

/-- The structure of `𝒪_{X,x}`-algebra on the local ring of the fibre, through the inclusion of
the fibre. -/
public noncomputable abbrev algebraStalkFiberStalk :
    Algebra (ToType (X.sheaf.presheaf.stalk x))
      (ToType ((f.fiber (f x)).presheaf.stalk (fiberPoint f x))) :=
  (stalkToFiberStalk f x).toAlgebra

/-- The residue field of `f x`, as the quotient of `𝒪_{S,f x}` by its maximal ideal. -/
public noncomputable abbrev targetResidue : Type u :=
  ToType (S.presheaf.stalk (f x)) ⧸ IsLocalRing.maximalIdeal (ToType (S.presheaf.stalk (f x)))

/-- The structure of `κ(f x)`-algebra on the local ring of the fibre, transported along
`Stacks.FiberCotangentIdentification.quotientEquivFiberStalk` from the quotient. -/
public noncomputable abbrev algebraResidueFiberStalk :
    letI := algebraStalkMap f x
    Algebra (targetResidue f x)
      (ToType ((f.fiber (f x)).presheaf.stalk (fiberPoint f x))) := by
  letI := algebraStalkMap f x
  exact ((quotientEquivFiberStalk f x).toRingHom.comp
    (algebraMap (targetResidue f x) _)).toAlgebra

/-- The structure of `𝒪_{S,f x}`-algebra on the local ring of the fibre, through `𝒪_{X,x}`. -/
public noncomputable abbrev algebraTargetFiberStalk :
    Algebra (ToType (S.presheaf.stalk (f x)))
      (ToType ((f.fiber (f x)).presheaf.stalk (fiberPoint f x))) :=
  ((stalkToFiberStalk f x).comp (f.stalkMap x).hom).toAlgebra

/-- **The local ring of the scheme-theoretic fibre is the base change of `𝒪_{X,x}` along the
residue field of `f x`**: the square of `𝒪_{S,f x} → κ(f x)`, `𝒪_{S,f x} → 𝒪_{X,x}` and the two
maps into `𝒪_{X_s,x}` is a pushout square. -/
public theorem isPushout_fiberStalk :
    letI := algebraStalkMap f x
    letI := algebraStalkFiberStalk f x
    letI := algebraResidueFiberStalk f x
    letI := algebraTargetFiberStalk f x
    letI : IsScalarTower (ToType (S.presheaf.stalk (f x)))
      (ToType (X.sheaf.presheaf.stalk x))
      (ToType ((f.fiber (f x)).presheaf.stalk (fiberPoint f x))) :=
        IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower (ToType (S.presheaf.stalk (f x))) (targetResidue f x)
      (ToType ((f.fiber (f x)).presheaf.stalk (fiberPoint f x))) :=
        IsScalarTower.of_algebraMap_eq fun a =>
          (quotientEquivFiberStalk_mk f x ((f.stalkMap x).hom a)).symm
    Algebra.IsPushout (ToType (S.presheaf.stalk (f x))) (targetResidue f x)
      (ToType (X.sheaf.presheaf.stalk x))
      (ToType ((f.fiber (f x)).presheaf.stalk (fiberPoint f x))) := by
  let := algebraStalkMap f x
  let := algebraStalkFiberStalk f x
  let := algebraResidueFiberStalk f x
  let := algebraTargetFiberStalk f x
  let : IsScalarTower (ToType (S.presheaf.stalk (f x)))
      (ToType (X.sheaf.presheaf.stalk x))
      (ToType ((f.fiber (f x)).presheaf.stalk (fiberPoint f x))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (ToType (S.presheaf.stalk (f x))) (targetResidue f x)
      (ToType ((f.fiber (f x)).presheaf.stalk (fiberPoint f x))) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (quotientEquivFiberStalk_mk f x ((f.stalkMap x).hom a)).symm
  exact isPushout_of_ringEquiv _ (quotientEquivFiberStalk f x) (quotientEquivFiberStalk_mk f x)

end Stacks.FiberCotangentIdentification

end
