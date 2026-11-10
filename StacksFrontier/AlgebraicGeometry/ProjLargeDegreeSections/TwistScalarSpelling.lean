module

public import StacksFrontier.AlgebraicGeometry.ProjLargeDegreeSections.KernelData
public import StacksFrontier.AlgebraicGeometry.ThetaMultiplicative.ScalarTwistProduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The shift spelling and the twisting-sheaf spelling agree for the regular module

[Stacks, Tag 0AG7] — `Stacks.AlgebraicGeometry.ProjLargeDegreeSections`
`.exists_bijective_degreeNToGlobalSections_regular` — is stated through the *shift* apparatus of
`StacksFrontier/AlgebraicGeometry/Constructions/ProjShiftedSectionModule.lean`: its sections live in
`Stacks.AlgebraicGeometry.ProjShiftedSections.shiftedSectionsComponent 𝒮 𝒨 n`, the global
sections of the sheaf associated to the shift `M(n)`, and a homogeneous scalar acts on them by
`Stacks.AlgebraicGeometry.ProjShiftedSections.homogeneousScalarGlobalSections`. The finiteness
and comparison results for the twists are stated through the *twist* apparatus: sections of
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf 𝒮 n`, with a homogeneous scalar acting
by `Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap`.

The module docstring of
`StacksFrontier/AlgebraicGeometry/Blowup/ProjectivePushforwardFiniteness.lean` records that the two
apparatuses "are only canonically isomorphic, not definitionally equal, and for a general graded
ring/sheaf no bridge between the two is available in this repository". That is accurate for a
*general sheaf* `ℱ`, where the twist is the sheafified tensor product `ℱ ⊗ 𝒪(n)` and nothing
identifies it with an associated sheaf. **For the regular module it is not the situation**: the
twist grading `fun i => integerGrading 𝒮 (i + n)` and the shift of `integerGrading 𝒮` by `n` are
the same function, so

* `twistingSheaf 𝒮 n` and the associated sheaf of the shift are the same sheaf, and
* `shiftedSectionsComponent 𝒮 (integerGrading 𝒮) n` and `Γ(Proj 𝒮, 𝒪(n))` are the same type,

both by `rfl`. The repository already relies on this once, in
`Stacks.AlgebraicGeometry.ProjLargeDegreeSections.degreeNToGlobalSections_eq_zero_iff`, which is
proved by `Iff.rfl`.

What is *not* `rfl` is the scalar action, because the two are built differently — one as
`a • ·` on the module fibres, the other as the associated-sheaf morphism of `LinearMap.mul S S a`
— and that is what this file proves. With it, the product formula for the adjoint form of
[Stacks, Tag 01MY]'s comparison `θ`, and the multiplicativity square
`Stacks.AlgebraicGeometry.ThetaMultiplicative.twistPushforwardMap_twistScalarSheafMap` built from
it, can be read as statements about the action [Stacks, Tag 0AG7] is stated with.

## Main results

* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.smul_eq_mkOne_mul`: in one module fibre,
  scaling by `c` is multiplication by the fraction `c / 1`.
* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.twistGrading_eq_shiftedGrading_integerGrading`
  and `twistingSheaf_eq_associatedModuleSheaf_shiftedGrading`: the two gradings, and hence the
  two sheaves, are the same.
* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.shiftedSectionsComponent_eq_twistSections`:
  the two spellings of `Γ(Proj 𝒮, 𝒪(n))` are the same type.
* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections`
  `.homogeneousScalarGlobalSections_eq_twistScalarSheafMap`: **the two homogeneous scalar actions
  agree**.
* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections`
  `.homogeneousScalarGlobalSections_eq_absoluteTwistProduct`: the shift-spelling action, written
  as the canonical twist product against the homogeneous section — the spelling the product
  formula for `θ` is stated at.

## References

* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 0AG7](https://stacks.math.columbia.edu/tag/0AG7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShiftedSections
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap
  localizedModule_map_mul_eq_mkOne_mul twistScalarSheafMap_app_eq_absoluteTwistProduct)
open Stacks.AlgebraicGeometry.RelativeProjTwists (absoluteTwistProduct)
open Stacks.AlgebraicGeometry.TwistRigidity (degreeSectionOn degreeSectionOn_apply)

namespace Stacks.AlgebraicGeometry.ProjLargeDegreeSections

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-! ### One fibre -/

omit [SetLike σ S] [AddSubgroupClass σ S] [GradedRing 𝒮] in
/-- **Scaling by `c` in a module fibre is multiplication by the fraction `c / 1`.** The fibres of
the twisting sheaves are `LocalizedModule P S`, which at this pin is `Localization P` with the
module action being ring multiplication, so both sides send `m / t` to `c * m / t`. -/
@[ega "0 1.2.2" "partial"]
public theorem smul_eq_mkOne_mul (P : Submonoid S) (c : S) (v : LocalizedModule P S) :
    c • v = LocalizedModule.mk c (1 : P) * v := by
  induction v using LocalizedModule.induction_on with
  | _ m t =>
    rw [LocalizedModule.smul'_mk]
    change Localization.mk (c • m) t = Localization.mk c (1 : P) * Localization.mk m t
    rw [Localization.mk_mul, smul_eq_mul, one_mul]

/-! ### The two gradings, and the two sheaves -/

omit [GradedRing 𝒮] in
/-- **The twist grading is the shift of the integer grading.** Both are
`fun i => integerGrading 𝒮 (i + n)`. -/
public theorem twistGrading_eq_shiftedGrading_integerGrading (n : ℤ) :
    twistGrading (S := S) 𝒮 n =
      Stacks.GradedModule.shiftedGrading (integerGrading (S := S) 𝒮) n := rfl

/-- **The `n`-th twisting sheaf is the sheaf associated to the shift of the regular module.**
An immediate consequence of the previous identity, the twisting sheaf being by definition the
associated sheaf of the twist grading. -/
@[ega "II 2.5.10"]
public theorem twistingSheaf_eq_associatedModuleSheaf_shiftedGrading (n : ℤ) :
    twistingSheaf 𝒮 n =
      associatedModuleSheaf 𝒮
        (Stacks.GradedModule.shiftedGrading (integerGrading (S := S) 𝒮) n) := rfl

/-- **The two spellings of `Γ(Proj 𝒮, 𝒪(n))` are the same type**: the degree-`n` component of
the shifted global sections of the regular module, and the global sections of the `n`-th
twisting sheaf. -/
public theorem shiftedSectionsComponent_eq_twistSections (n : ℤ) :
    shiftedSectionsComponent 𝒮 (integerGrading (S := S) 𝒮) n =
      (twistingSheaf 𝒮 n).val.obj (op ⊤) := rfl

/-! ### The two scalar actions -/

/-- **The homogeneous scalar action of the shift apparatus is the one of the twist apparatus.**
The left side is `a • ·` on the module fibres; the right side is the associated-sheaf morphism of
`LinearMap.mul S S a`, which localizes to multiplication by the fraction `a / 1` in each fibre.
The two agree because scaling by `a` *is* multiplication by `a / 1`
(`smul_eq_mkOne_mul`). -/
public theorem homogeneousScalarGlobalSections_eq_twistScalarSheafMap (i : ℕ) (n : ℤ) (a : 𝒮 i)
    (s : (twistingSheaf 𝒮 n).val.obj (op ⊤)) :
    homogeneousScalarGlobalSections 𝒮 (integerGrading (S := S) 𝒮) i n a s =
      ((twistScalarSheafMap 𝒮 i n ((i : ℤ) + n) rfl a).val.app (op ⊤)).hom s := by
  refine Subtype.ext (funext fun x => ?_)
  change (a : S) • s.1 x =
    LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl
      (LinearMap.mul S S (a : S)) (s.1 x)
  exact (smul_eq_mkOne_mul _ (a : S) (s.1 x)).trans
    (localizedModule_map_mul_eq_mkOne_mul _ (a : S) (s.1 x)).symm

/-- **The homogeneous section of `𝒪(i)` restricted to `⊤` is the homogeneous section itself.**
The restriction map of a sheaf along `⊤ ≤ ⊤` changes no value. -/
public theorem degreeSectionOn_top (i : ℕ) (a : 𝒮 i) :
    degreeSectionOn 𝒮 i a.2 ⊤ = degreeSection 𝒮 i a :=
  Subtype.ext (funext fun x => (degreeSectionOn_apply 𝒮 i a.2 ⊤ x).trans
    (ProjTwistSections.degreeSection_apply 𝒮 i a x).symm)

/-- **The shift-spelling homogeneous scalar action, written as the canonical twist product
against the homogeneous section of the scalar.** This is the spelling the product formula for the
adjoint form of [Stacks, Tag 01MY]'s comparison is stated at, so with this identity that formula
applies to the action [Stacks, Tag 0AG7] is stated with. -/
public theorem homogeneousScalarGlobalSections_eq_absoluteTwistProduct (i : ℕ) (n : ℤ) (a : 𝒮 i)
    (s : (twistingSheaf 𝒮 n).val.obj (op ⊤)) :
    homogeneousScalarGlobalSections 𝒮 (integerGrading (S := S) 𝒮) i n a s =
      absoluteTwistProduct 𝒮 (i : ℤ) n ⊤ (degreeSection 𝒮 i a) s :=
  (homogeneousScalarGlobalSections_eq_twistScalarSheafMap 𝒮 i n a s).trans
    ((twistScalarSheafMap_app_eq_absoluteTwistProduct 𝒮 i n a ⊤ s).trans
      (congrArg (fun t => absoluteTwistProduct 𝒮 (i : ℤ) n ⊤ t s)
        (degreeSectionOn_top 𝒮 i a)))

end Stacks.AlgebraicGeometry.ProjLargeDegreeSections

end
