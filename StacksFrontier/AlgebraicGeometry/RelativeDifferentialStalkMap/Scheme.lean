module

public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.Scheme
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Kaehler
public import StacksFrontier.AlgebraicGeometry.SheafifyStalk.StalkMap

/-!
# The stalk of the relative differentials, over the local ring of the target

For a morphism of schemes `f : X ⟶ S` and a point `x` of `X`, **the stalk at `x` of the sheaf of
relative differentials of `f` is `Ω[𝒪_{X,x}⁄𝒪_{S,f x}]`**, the module of Kähler differentials of
`AlgebraicGeometry.Scheme.Hom.stalkMap`, compatibly with universal differentials.

This is Stacks Tag 01V0 read at a point, in the spelling that conditions (3) and (4) of Stacks
Tag 01V9 are stated in.

`Stacks.RelativeDifferentialStalk.relativeDifferentialsStalkLinearEquiv` already identifies that
stalk with Kähler differentials, but over the stalk `(f⁻¹𝒪_S)_x` of the *inverse image* of the
structure sheaf of `S`, which is where the structural map
`AlgebraicGeometry.inverseImageStructureMap` of `f` lives.  This file changes the base ring to
`𝒪_{S,f x}`.

## Main definitions

* `Stacks.RelativeDifferentialStalkMap.algebraStalkMap`: `𝒪_{X,x}` as an algebra over
  `𝒪_{S,f x}`, through `AlgebraicGeometry.Scheme.Hom.stalkMap`.
* `Stacks.RelativeDifferentialStalkMap.algebraStalkInverseImage`: `(f⁻¹𝒪_S)_x` as an algebra over
  `𝒪_{S,f x}`, through `Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso`.
* `Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv`: the
  identification of the stalk of the sheaf of relative differentials with
  `Ω[𝒪_{X,x}⁄𝒪_{S,f x}]`.

## Main results

* `Stacks.RelativeDifferentialStalkMap.isScalarTower_stalk` and
  `Stacks.RelativeDifferentialStalkMap.surjective_algebraMap_stalkInverseImage`: the two
  hypotheses that the change of base ring needs, namely that `𝒪_{S,f x} → (f⁻¹𝒪_S)_x → 𝒪_{X,x}`
  composes to `f`'s stalk map and that its first leg is surjective.
* `Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv_germ_d`: the
  identification carries the germ at `x` of the universal relative differential of a local
  section of `𝒪_X` to the universal `𝒪_{S,f x}`-differential of the germ of that section.

## Implementation notes

The change of base ring is `Stacks.RelativeDifferentialStalkMap.kaehlerMapEquivOfSurjective`,
which asks for `𝒪_{S,f x} → (f⁻¹𝒪_S)_x` to be surjective; here it is in fact an isomorphism,
being the inverse of `Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso`, and surjectivity
is read off from `CategoryTheory.Iso.hom_inv_id`.  That the two legs compose to `f`'s stalk map
is `Stacks.SheafifyStalk.stalkMap_hom_eq_comp`.

Every algebra and module structure appearing below has to be named.  None of them is found by
instance search: `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` is a definition that
synthesis will not unfold, and the three algebra structures are induced by ring homomorphisms
through `RingHom.toAlgebra`.

## References

* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0)
* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.SheafOfModules
open Stacks.RelativeDifferentialStalk

universe u

namespace Stacks.RelativeDifferentialStalkMap

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- The stalk `(f⁻¹𝒪_S)_x` of the inverse image of the structure sheaf of `S`, which is the base
ring of `Stacks.RelativeDifferentialStalk.relativeDifferentialsStalkLinearEquiv`. -/
public noncomputable abbrev inverseImageStalk : Type u :=
  ToType (((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).presheaf.stalk x)

/-- **`𝒪_{X,x}` as an algebra over `𝒪_{S,f x}`**, through
`AlgebraicGeometry.Scheme.Hom.stalkMap`.  This is the base ring that conditions (3) and (4) of
Stacks Tag 01V9 read the relative differentials over. -/
public noncomputable abbrev algebraStalkMap :
    Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.sheaf.presheaf.stalk x)) :=
  (f.stalkMap x).hom.toAlgebra

/-- **`(f⁻¹𝒪_S)_x` as an algebra over `𝒪_{S,f x}`**, through the inverse of
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso`. -/
public noncomputable abbrev algebraStalkInverseImage :
    Algebra (ToType (S.presheaf.stalk (f x))) (inverseImageStalk f x) :=
  (SheafifyStalk.stalkInverseImageStructureSheafIso f x).inv.hom.toAlgebra

/-- **The two algebra structures on `𝒪_{X,x}` are compatible.**  The composite
`𝒪_{S,f x} → (f⁻¹𝒪_S)_x → 𝒪_{X,x}` of the comparison of base rings with the stalk of the
structural map of `f` is `f`'s stalk map.  This is
`Stacks.SheafifyStalk.stalkMap_hom_eq_comp` read as a scalar tower. -/
public theorem isScalarTower_stalk :
    letI := algebraStalkMap f x
    letI := algebraStalkInverseImage f x
    letI := algebraStalk (inverseImageStructureMap f).hom x
    IsScalarTower (ToType (S.presheaf.stalk (f x))) (inverseImageStalk f x)
      (ToType (X.sheaf.presheaf.stalk x)) := by
  let := algebraStalkMap f x
  let := algebraStalkInverseImage f x
  let := algebraStalk (inverseImageStructureMap f).hom x
  refine IsScalarTower.of_algebraMap_eq' ?_
  simp only [RingHom.algebraMap_toAlgebra]
  exact SheafifyStalk.stalkMap_hom_eq_comp f x

/-- **The comparison of base rings `𝒪_{S,f x} → (f⁻¹𝒪_S)_x` is surjective.**  It is the inverse
of the isomorphism `Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso`, so a section is
given by that isomorphism itself. -/
public theorem surjective_algebraMap_stalkInverseImage :
    letI := algebraStalkInverseImage f x
    Function.Surjective
      (algebraMap (ToType (S.presheaf.stalk (f x))) (inverseImageStalk f x)) := by
  let := algebraStalkInverseImage f x
  intro b
  refine ⟨(SheafifyStalk.stalkInverseImageStructureSheafIso f x).hom.hom b, ?_⟩
  exact congrArg (fun z => CommRingCat.Hom.hom z b)
    (SheafifyStalk.stalkInverseImageStructureSheafIso f x).hom_inv_id

/-- **The relative differentials of `f` at `x` have the same Kähler differentials over
`𝒪_{S,f x}` as over `(f⁻¹𝒪_S)_x`.**  The change of base ring along the comparison of the two,
which is surjective. -/
public noncomputable def kaehlerStalkBaseEquiv :
    letI := algebraStalkMap f x
    letI := algebraStalkInverseImage f x
    letI := algebraStalk (inverseImageStructureMap f).hom x
    KaehlerDifferential (ToType (S.presheaf.stalk (f x))) (ToType (X.sheaf.presheaf.stalk x))
      ≃ₗ[ToType (X.sheaf.presheaf.stalk x)]
      KaehlerDifferential (inverseImageStalk f x) (ToType (X.sheaf.presheaf.stalk x)) := by
  letI := algebraStalkMap f x
  letI := algebraStalkInverseImage f x
  letI := algebraStalk (inverseImageStructureMap f).hom x
  letI := isScalarTower_stalk f x
  exact kaehlerMapEquivOfSurjective _ _ _ (surjective_algebraMap_stalkInverseImage f x)

variable [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]

/-- **The stalk at `x` of the sheaf of relative differentials of `f : X ⟶ S` is
`Ω[𝒪_{X,x}⁄𝒪_{S,f x}]`**, the module of Kähler differentials of `f`'s stalk map.

This is Stacks Tag 01V0 at a point, in the spelling that conditions (3) and (4) of Stacks Tag
01V9 use: `Stacks.RelativeDifferentialStalk.relativeDifferentialsStalkLinearEquiv` followed by
the change of base ring `Stacks.RelativeDifferentialStalkMap.kaehlerStalkBaseEquiv`. -/
public noncomputable def relativeDifferentialsStalkKaehlerEquiv :
    letI := algebraStalkMap f x
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (Scheme.Hom.relativeDifferentials f).val.presheaf x)
      ≃ₗ[ToType (X.sheaf.presheaf.stalk x)]
      KaehlerDifferential (ToType (S.presheaf.stalk (f x)))
        (ToType (X.sheaf.presheaf.stalk x)) := by
  letI := algebraStalkMap f x
  letI := algebraStalkInverseImage f x
  letI := algebraStalk (inverseImageStructureMap f).hom x
  exact (relativeDifferentialsStalkLinearEquiv f x).trans (kaehlerStalkBaseEquiv f x).symm

/-- `Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv` is the composite
of its two constituents. -/
public theorem relativeDifferentialsStalkKaehlerEquiv_apply
    (m : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (Scheme.Hom.relativeDifferentials f).val.presheaf x)) :
    letI := algebraStalkMap f x
    letI := algebraStalkInverseImage f x
    letI := algebraStalk (inverseImageStructureMap f).hom x
    relativeDifferentialsStalkKaehlerEquiv f x m =
      (kaehlerStalkBaseEquiv f x).symm (relativeDifferentialsStalkLinearEquiv f x m) :=
  rfl

/-- **The identification carries universal differentials to universal differentials.**  The germ
at `x` of the universal relative differential of a section of `𝒪_X` over a neighbourhood of `x`
goes to the universal `𝒪_{S,f x}`-differential of the germ of that section. -/
public theorem relativeDifferentialsStalkKaehlerEquiv_germ_d
    (i : OrderDual (TopologicalSpace.OpenNhds x)) (a : nhdRing X.sheaf.presheaf i) :
    letI := algebraStalkMap f x
    relativeDifferentialsStalkKaehlerEquiv f x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (Scheme.Hom.relativeDifferentials f).val.presheaf (nhdOpen i) x (mem_nhdOpen i)
          ((Scheme.Hom.universalRelativeDerivation f).d a)) =
      KaehlerDifferential.D (ToType (S.presheaf.stalk (f x)))
        (ToType (X.sheaf.presheaf.stalk x))
        (X.sheaf.presheaf.germ (nhdOpen i) x (mem_nhdOpen i) a) := by
  let := algebraStalkMap f x
  let := algebraStalkInverseImage f x
  let := algebraStalk (inverseImageStructureMap f).hom x
  let := isScalarTower_stalk f x
  rw [relativeDifferentialsStalkKaehlerEquiv_apply,
    relativeDifferentialsStalkLinearEquiv_germ_d]
  exact kaehlerMapEquivOfSurjective_symm_D _ _ _
    (surjective_algebraMap_stalkInverseImage f x) _

end Stacks.RelativeDifferentialStalkMap

end
