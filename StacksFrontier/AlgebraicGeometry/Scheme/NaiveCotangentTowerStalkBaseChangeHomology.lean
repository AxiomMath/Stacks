module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentBaseChangeHomology
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentTowerStalkQuasiIso
public import StacksFrontier.RingTheory.NaiveCotangent.BaseChangeLocalizedTarget

/-!
# The stalk of the comparison map of two towers: the two cohomological conclusions

Let `R ⟶ A ⟶ C` and `R ⟶ B ⟶ C` be two towers of sheaves of commutative rings on a topological
space `T` with the same composite, say `p ≫ q = bc ≫ s`.  The map

`NL_{A/R} ⊗_A C ⟶ NL_{C/B}`

of `Stacks.NaiveCotangentTowerStalk.towerComposite` is the base-change map of the first tower
followed by the relative map of the second.  This file computes what its stalk at a point does
in degrees `0` and `-1` when the ring-level comparison of the stalk rings is only an isomorphism
on `H₀` and a surjection on `H₁`, which is what an arbitrary base change supplies
(Stacks 0FUZ).

It is the exact counterpart of
`Stacks.NaiveCotangentTowerStalk.quasiIso_stalkFunctor_map_towerComposite`, which asks the
ring-level comparison to be a quasi-isomorphism and concludes that the stalk of the map is one;
the two statements share every degreewise identification of the stalks, and differ only in which
of the four elementary conditions is available and therefore in what is concluded.

## Main results

* `Stacks.NaiveCotangentTowerStalk.isBijectiveOnCokernel_stalkFunctor_map_towerComposite`: the
  stalk of the map is bijective on the cokernel of its differential, hence an isomorphism on
  `H^0`.
* `Stacks.NaiveCotangentTowerStalk.isSurjectiveOnKernel_stalkFunctor_map_towerComposite`: the
  stalk of the map is surjective on the kernel of its differential, hence a surjection on
  `H^{-1}`.  Nothing is claimed about injectivity there: that is the half an arbitrary base
  change does not give, and the half `H^{-1}` of Stacks 0FV5 does not assert.

## Implementation notes

The four stalk identifications, the two differentials and the two components of the stalk of the
map are exactly the ones
`Stacks.NaiveCotangentTowerStalk.quasiIso_stalkFunctor_map_towerComposite` feeds to
`CochainComplex.quasiIso_of_isZero_X_of_addEquiv`: the source is identified by
`Stacks.NaiveCotangentStalkBaseChange.stalkBaseChangeAddEquivNegOne` and its degree-`0`
companion, the target by `Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOneLinear` and
`stalkLegZeroLinear` (Stacks 0D09), and the stalk of the map is
`stalkLegNegOneLinear_towerComposite` and `stalkLegZeroLinear_towerComposite`.  What changes is
the criterion they are fed to: `CochainComplex.isBijectiveOnCokernel_of_addEquiv` and
`CochainComplex.isSurjectiveOnKernel_of_addEquiv`, whose hypotheses are stated in the
non-inverted direction the degreewise identifications are proved in, so no
`AddEquiv.eq_symm_apply` is needed here.

Unlike the quasi-isomorphism statement these conclusions are not `QuasiIso` and so carry no
`IsZero` hypotheses on the terms outside degrees `-1` and `0`: bijectivity on the cokernel and
surjectivity on the kernel are conditions on the single differential alone.  The passage from
them to `H^0` and `H^{-1}` is `CochainComplex.isIso_homologyMap_zero_of_isBijectiveOnCokernel`
and `CochainComplex.epi_homologyMap_negOne_of_isSurjectiveOnKernel`, which is where the
vanishing is used, and happens at the point of use.

The ring-level hypothesis is asked for in the form "*every* morphism of extensions
`Rₓ[Aₓ] ⟶ Bₓ[Cₓ]` induces a comparison with these properties", for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentTowerStalkQuasiIso`: it is no stronger than
asking it for the one morphism the geometry produces, since any two morphisms of extensions
induce homotopic chain maps, and it spares the consumer the identification of *which* morphism
of extensions the stalk of the map of sheaves is.

The `attribute [local instance 1]` block demoting the three sheafification instances is the one
of `StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentTowerStalkQuasiIso`, for the same
reason: those instances reach sheafification through a choice of left adjoint, and reducing a
term that mentions them unfolds `Classical.indefiniteDescription`.

## References

* [Stacks Project, Tag 0FUZ](https://stacks.math.columbia.edu/tag/0FUZ), the naive cotangent
  complex and arbitrary base change, whose conclusion is the shape of the hypothesis carried
  here.
* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the base-change and
  relative maps of naive cotangent complexes of a tower of sheaves of rings.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 0FV5](https://stacks.math.columbia.edu/tag/0FV5), base change for the
  naive cotangent complex of a morphism of schemes, which consumes these statements at every
  point of a cartesian square.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules
open Stacks.NaiveCotangentAffineStalkLegs
open Stacks.NaiveCotangentStalkBaseChange
open Stacks.RelativeDifferentialStalk (algebraStalk)
open AlgebraicGeometry.SheafOfModules (stalkFunctor)
open Stacks.Sites.Conormal (stalkIsScalarTowerSquareBase stalkIsScalarTowerSquareTarget)

universe u

noncomputable section

namespace Stacks.NaiveCotangentTowerStalk

attribute [local instance 1]
  Sheaf.hasWeakSheafifyCommRingCat
  Sheaf.hasSheafifyAddCommGrpCat
  Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

variable {T : TopCat.{u}}
  (R A B C : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (p : R ⟶ A) (q : A ⟶ C) (bc : R ⟶ B) (s : B ⟶ C) (z : T) (hbc : p ≫ q = bc ≫ s)

include hbc in
/-- **The stalk of the tower composite is bijective on the cokernel of its differential** as
soon as every comparison map of the stalk extensions is an isomorphism on `H₀`.  The four
nonzero stalks are identified with the four terms of the ring-level comparison and the stalk of
the map is that comparison, exactly as in
`Stacks.NaiveCotangentTowerStalk.quasiIso_stalkFunctor_map_towerComposite`. -/
theorem isBijectiveOnCokernel_stalkFunctor_map_towerComposite
    (hring : letI := algebraStalk p.hom z
      letI := algebraStalk (p ≫ q).hom z
      letI := algebraStalk q.hom z
      letI := algebraStalk bc.hom z
      letI := algebraStalk s.hom z
      letI := stalkIsScalarTowerSquareBase R B C s (p ≫ q) bc z hbc.symm
      letI := stalkIsScalarTowerSquareTarget R A C p (p ≫ q) q z rfl
      ∀ h : (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk R.obj z))
            (ToType (TopCat.Presheaf.stalk A.obj z))).toExtension.Hom
          (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk B.obj z))
            (ToType (TopCat.Presheaf.stalk C.obj z))).toExtension,
        NaiveCotangent.IsH₀IsoH₁Surj
          (NaiveCotangent.nlExtensionBaseChangeMap
            (T := ToType (TopCat.Presheaf.stalk C.obj z)) h)) :
    CochainComplex.IsBijectiveOnCokernel
      (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (towerComposite R A B C p q bc s hbc)) := by
  let := algebraStalk p.hom z
  let := algebraStalk (p ≫ q).hom z
  let := algebraStalk q.hom z
  let := algebraStalk bc.hom z
  let := algebraStalk s.hom z
  let := stalkIsScalarTowerSquareBase R B C s (p ≫ q) bc z hbc.symm
  let := stalkIsScalarTowerSquareTarget R A C p (p ≫ q) q z rfl
  let := moduleRingStalkCotangent B C s z
  let := moduleRingStalkCotangentSpace B C s z
  exact CochainComplex.isBijectiveOnCokernel_of_addEquiv _
    (stalkBaseChangeAddEquivNegOne R A C p q z) (stalkBaseChangeAddEquivZero R A C p q z)
    (stalkLegNegOneLinear B C s z).toAddEquiv (stalkLegZeroLinear B C s z).toAddEquiv
    (NaiveCotangent.nlExtensionBaseChange
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk R.obj z))
        (ToType (TopCat.Presheaf.stalk A.obj z))).toExtension
      (ToType (TopCat.Presheaf.stalk C.obj z))).d
    (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk B.obj z))
      (ToType (TopCat.Presheaf.stalk C.obj z))).toExtension.cotangentComplex
    (NaiveCotangent.nlExtensionBaseChangeMap
      (T := ToType (TopCat.Presheaf.stalk C.obj z))
      (stalkTowerHom R A B C p q bc s z hbc)).f₀
    (stalkBaseChangeAddEquiv_d R A C p q z) (stalkLegLinear_d B C s z)
    (stalkLegZeroLinear_towerComposite R A B C p q bc s z hbc)
    (NaiveCotangent.IsH₀IsoH₁Surj.exists_d_eq (hring _))
    (NaiveCotangent.IsH₀IsoH₁Surj.exists_add_d_eq (hring _))

include hbc in
/-- **The stalk of the tower composite is surjective on the kernel of its differential** as soon
as every comparison map of the stalk extensions is a surjection on `H₁`.  Nothing is assumed
about injectivity on that kernel, and nothing is concluded about it. -/
theorem isSurjectiveOnKernel_stalkFunctor_map_towerComposite
    (hring : letI := algebraStalk p.hom z
      letI := algebraStalk (p ≫ q).hom z
      letI := algebraStalk q.hom z
      letI := algebraStalk bc.hom z
      letI := algebraStalk s.hom z
      letI := stalkIsScalarTowerSquareBase R B C s (p ≫ q) bc z hbc.symm
      letI := stalkIsScalarTowerSquareTarget R A C p (p ≫ q) q z rfl
      ∀ h : (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk R.obj z))
            (ToType (TopCat.Presheaf.stalk A.obj z))).toExtension.Hom
          (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk B.obj z))
            (ToType (TopCat.Presheaf.stalk C.obj z))).toExtension,
        NaiveCotangent.IsH₀IsoH₁Surj
          (NaiveCotangent.nlExtensionBaseChangeMap
            (T := ToType (TopCat.Presheaf.stalk C.obj z)) h)) :
    CochainComplex.IsSurjectiveOnKernel
      (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (towerComposite R A B C p q bc s hbc)) := by
  let := algebraStalk p.hom z
  let := algebraStalk (p ≫ q).hom z
  let := algebraStalk q.hom z
  let := algebraStalk bc.hom z
  let := algebraStalk s.hom z
  let := stalkIsScalarTowerSquareBase R B C s (p ≫ q) bc z hbc.symm
  let := stalkIsScalarTowerSquareTarget R A C p (p ≫ q) q z rfl
  let := moduleRingStalkCotangent B C s z
  let := moduleRingStalkCotangentSpace B C s z
  exact CochainComplex.isSurjectiveOnKernel_of_addEquiv _
    (stalkBaseChangeAddEquivNegOne R A C p q z) (stalkBaseChangeAddEquivZero R A C p q z)
    (stalkLegNegOneLinear B C s z).toAddEquiv (stalkLegZeroLinear B C s z).toAddEquiv
    (NaiveCotangent.nlExtensionBaseChange
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk R.obj z))
        (ToType (TopCat.Presheaf.stalk A.obj z))).toExtension
      (ToType (TopCat.Presheaf.stalk C.obj z))).d
    (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk B.obj z))
      (ToType (TopCat.Presheaf.stalk C.obj z))).toExtension.cotangentComplex
    (NaiveCotangent.nlExtensionBaseChangeMap
      (T := ToType (TopCat.Presheaf.stalk C.obj z))
      (stalkTowerHom R A B C p q bc s z hbc)).f₁
    (stalkBaseChangeAddEquiv_d R A C p q z) (stalkLegLinear_d B C s z)
    (stalkLegNegOneLinear_towerComposite R A B C p q bc s z hbc)
    (NaiveCotangent.IsH₀IsoH₁Surj.exists_of_d_eq_zero (hring _))

end Stacks.NaiveCotangentTowerStalk

end

end
