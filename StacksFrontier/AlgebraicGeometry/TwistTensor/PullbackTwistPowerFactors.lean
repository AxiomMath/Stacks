module

public import StacksFrontier.AlgebraicGeometry.TensorPowerCongrMul.Basic
public import StacksFrontier.AlgebraicGeometry.TwistTensor.PullbackTwistPower

/-!
# The factors of `pullbackTwistPowIso`, read on sections and across degrees

`Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackTwistPowIso` is the identification
`φ^*𝒪(dn) ≅ L^{⊗ n}` attached by [Stacks, Tag 01N8] to a morphism `φ : Y ⟶ U_d` together with
an isomorphism `α : φ^*𝒪(d) ≅ L`. It is a composite of five isomorphisms, and the implementation
notes of `StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/ChartDegreewiseFamily.lean` call it
"the wall": what property (1) of [Stacks, Tag 01O7] needs of it is its behaviour across degrees,
and no statement about any of its factors was available.

This file supplies the per-factor statements. Of the five factors,

1. `pullbackTwistRestrictIso` — the contraction of the pullback along `Y ⟶ U_d ⟶ Proj 𝒮`;
2. `Stacks.PowerFamilyBridge.tensorPowerModuleIso` — the comparison of the repository's two
   integral power families;
3. `Stacks.AlgebraicGeometry.ThetaMul.thetaInt` — the comparison `𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(dn)`
   of [Stacks, Tag 01MU];
4. `Stacks.TensorPowerPullback.pullbackIntPowIso` — the compatibility of the powers with
   pullback;
5. `tensorPowerModuleCongr` — the replacement of `φ^*𝒪(d)` by `L` in every power at once,

the third and fourth already have multiplicativity, as
`Stacks.AlgebraicGeometry.ThetaMul.thetaInt_mul` and
`Stacks.TensorPowerPullback.pullbackIntPowIso_coherentMulIso`. The fifth is supplied here. The
first is given a section-level reading, which is all it can have: it is a transport along the
unit of a pullback adjunction and carries no degree. The second is the one that remains; see
"Not done here".

## Main results

* `...PullbackTwistPower.pullbackTwistRestrictIso_hom` and `pullbackTwistRestrictIso_inv`: the
  contraction is the comparison `AlgebraicGeometry.Scheme.Modules.pullbackComp` of the pullbacks
  along a composite, read backwards.
* `...PullbackTwistPower.pullbackTwistRestrictIso_hom_unit`: **the contraction on sections.**
  It carries the pullback-unit image along `Y ⟶ Proj 𝒮` of a section of `𝒪(c)` to the iterated
  pullback-unit image along `Y ⟶ U_d` and `U_d ⟶ Proj 𝒮`.
* `...PullbackTwistPower.tensorPowerModuleCongr_zero` and `tensorPowerModuleCongr_one`: the
  degree-zero and degree-one values of the congruence factor.
* `...PullbackTwistPower.tensorPowerModuleCongr_coherentMulIso`: **the congruence factor is
  multiplicative in every integral bidegree.** It intertwines the coherent multiplication of
  [Stacks, Tag 01CU] on `A` with the one on `B`, in the spelling
  `Stacks.TensorPowerPullback.pullbackIntPowIso_coherentMulIso` is stated in, so the two compose.
* `...PullbackTwistPower.pullbackTwistPowIso_hom`: the composite written out, so that a consumer
  can attack it factor by factor.

## Not done here

**The multiplicativity of `pullbackTwistPowIso` itself is not proved**, and exactly two of its
five factors are missing for it.

`Stacks.PowerFamilyBridge.tensorPowerModuleIso` has no multiplicativity. The implementation
notes of `StacksFrontier/AlgebraicGeometry/PowerFamilyBridge/Recursion.lean` attribute this to a
missing dictionary between the monoidal structure `Stacks.SheafInternalHom.monoidalCategory`,
which `AlgebraicGeometry.SheafOfModules.tensorPow` and its addition law are stated in, and the
tensor-product-sheaf constraints that
`Stacks.SheafOfModules.TensorPower.coherentMulIso`'s coherence laws are stated in. That reading
is not the obstruction for the *other* factor treated here — see the implementation notes below —
but it is untouched for this one: what `StacksFrontier/AlgebraicGeometry/PowerFamilyBridge/Recursion.lean` does supply, `natIso_succ` and
`negIso_succ`, are the two recursion steps, and an induction over the degree out of them would
additionally consume the associativity constraint of each family in a common language.

`pullbackTwistRestrictIso` has no multiplicativity either. What would be wanted is that the
contraction commutes with the multiplication of the pulled-back twists, which is the
compatibility of `AlgebraicGeometry.Scheme.Modules.pullbackComp` with
`Stacks.PullbackTensorCoherence.pullbackTensorComparison`; the ingredient for it is
`Stacks.PullbackTensorCoherence.pullbackCompIso`, and the statement is not formed anywhere.

No evaluation on sections of `pullbackTwistPowIso` is proved, and none is possible factor by
factor past the first: `Stacks.SheafOfModules.TensorPower.tensorPower` is the image of the
structure sheaf under an iterate of an abstract autoequivalence and has no sectionwise
description, as the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPowerCongr.lean` record.

No Stacks tag is carried: none of the statements below is a clause of any tag.

## Implementation notes

**The multiplicativity of the congruence factor is not blocked on a monoidal dictionary.** It is
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrCmpTP_mul`, which rests on the
successor law `Stacks.SheafOfModules.TensorPower.tensorPowerCongr_succIso`; the dictionary
between the tensor product sheaf's constraints and the monoidal ones that it crosses is
`...LaurentPullback.bridge_tensorIso` and its companions, and those are proved.

`tensorPowerModuleCongr` is `Stacks.SheafOfModules.TensorPower.tensorPowerCongr` by definition —
the `have`s in its body supply the two equivalence instances and are erased by `rfl` — which is
why the degree-zero and degree-one values below are `rfl` against `tensorPowerCongr_zero` and
`tensorPowerCongr_one` rather than needing a bridge.

The one crossing that `rw` cannot make is between `tensorSheafMapIso` and the monoidal `⊗ₘ`. The
two are equal by `...LaurentPullback.bridge_tensorIso`, but the objects
`Y.Modules`, `SheafOfModules (structureRingSheaf Y.toRingedSpace)` and
`SheafOfModules (TensorSheafification.structureSheaf Y.presheaf _)` are equal only by definition,
so the rewrite is stated as a `have` at the spelling it has to match and applied there.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.MorphismsIntoProj (pullbackTwist toProj)
open Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen (twist)
open Stacks.AlgebraicGeometry.ThetaMul (thetaInt)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.SheafOfModules.TensorPower (coherentMulIso tensorSheafMapIso tensorPowerCongr)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)

universe u

namespace Stacks.AlgebraicGeometry.PullbackTwistPower

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (d : ℕ)
  {Y : Scheme.{u}} (φ : Y ⟶ (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme)

/-! ### The contraction of the pullback along `Y ⟶ U_d ⟶ Proj 𝒮` -/

/-- The contraction is the comparison of the pullbacks along a composite, read backwards. -/
theorem pullbackTwistRestrictIso_hom (c : ℤ) :
    (pullbackTwistRestrictIso 𝒮 d φ c).hom =
      ((Scheme.Modules.pullbackComp φ (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι).app
        (twistingSheaf 𝒮 c)).inv :=
  rfl

/-- The contraction, read forwards: its inverse is the comparison of the pullbacks along the
composite. -/
theorem pullbackTwistRestrictIso_inv (c : ℤ) :
    (pullbackTwistRestrictIso 𝒮 d φ c).inv =
      ((Scheme.Modules.pullbackComp φ (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι).app
        (twistingSheaf 𝒮 c)).hom :=
  rfl

/-- **The contraction on sections.** A section `a` of `𝒪(c)` over an open `U` of `Proj 𝒮` has a
pullback-unit image in `φ^*𝒪(c)` over the preimage of `U` along the composite `Y ⟶ U_d ⟶ Proj 𝒮`;
the contraction carries it to the pullback-unit image along `φ` of the pullback-unit image along
the open immersion `U_d ⟶ Proj 𝒮`.

This is the whole section-level content of this factor: it is a transport along the unit of a
pullback adjunction and carries no degree, so there is nothing else to say about it on sections.
It is `AlgebraicGeometry.Scheme.Modules.pullbackComp_inv_unit` at the factorisation
`toProj 𝒮 φ = φ ≫ (Proj.degreeOpen 𝒮 d).ι`. -/
theorem pullbackTwistRestrictIso_hom_unit (c : ℤ)
    (U : (AlgebraicGeometry.Proj 𝒮).Opens) (a : (twistingSheaf 𝒮 c).val.obj (op U)) :
    ((pullbackTwistRestrictIso 𝒮 d φ c).hom).val.app (op (toProj 𝒮 φ ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction (toProj 𝒮 φ)).unit.app
          (twistingSheaf 𝒮 c)).val.app (op U) a) =
      ((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app (twist 𝒮 d c)).val.app
        (op ((AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι).unit.app
            (twistingSheaf 𝒮 c)).val.app (op U) a) :=
  Scheme.Modules.pullbackComp_inv_unit φ (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι
    (twistingSheaf 𝒮 c) U a

/-! ### The congruence of the integral tensor powers in the module -/

/-- In the degree zero the congruence is the identity: both powers are the structure sheaf. -/
theorem tensorPowerModuleCongr_zero {A B : Y.Modules} [Stacks.Ample.IsInvertibleModule Y A]
    [Stacks.Ample.IsInvertibleModule Y B] (e : A ≅ B) :
    tensorPowerModuleCongr (Y := Y) e 0 = Iso.refl _ :=
  rfl

/-- In the degree one the congruence is the isomorphism itself, tensored into the structure
sheaf: `tensorPowerCongr`'s degree-one value, which is the comparison of `𝒪_Y ⊗ A` with
`𝒪_Y ⊗ B`. -/
theorem tensorPowerModuleCongr_one {A B : Y.Modules} [Stacks.Ample.IsInvertibleModule Y A]
    [Stacks.Ample.IsInvertibleModule Y B] (e : A ≅ B) :
    tensorPowerModuleCongr (Y := Y) e 1 =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf (forget₂ CommRingCat RingCat)
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y)⟩).obj
        (_root_.SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf Y.presheaf
            (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y)))).mapIso e :=
  rfl

/-- **The congruence factor of `pullbackTwistPowIso` is multiplicative in every integral
bidegree.** The coherent multiplication of [Stacks, Tag 01CU] for `A` in the bidegree `(n, m)`,
followed by the congruence in the degree `n + m`, is the congruences in the degrees `n` and `m`
on the two factors, followed by the coherent multiplication for `B`. Both degrees are arbitrary
integers.

The tensor product of the two congruences is spelled by
`Stacks.SheafOfModules.TensorPower.tensorSheafMapIso`, which is the spelling
`Stacks.TensorPowerPullback.pullbackIntPowIso_coherentMulIso` uses, so the two statements compose
along the composite `pullbackTwistPowIso`.

This is `...LaurentCongr.congrCmpTP_mul` with the invertibility hypothesis converted from the
ampleness theory's to [Stacks, Tag 01CS]'s and the monoidal tensor product of morphisms rewritten
as a tensor product sheaf. -/
theorem tensorPowerModuleCongr_coherentMulIso {A B : Y.Modules}
    [Stacks.Ample.IsInvertibleModule Y A] [Stacks.Ample.IsInvertibleModule Y B]
    (e : A ≅ B) (n m : ℤ) :
    (coherentMulIso Y.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y)
            A n m).hom ≫
        (tensorPowerModuleCongr (Y := Y) e (n + m)).hom =
      (tensorSheafMapIso Y.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y)
          (tensorPowerModuleCongr (Y := Y) e n) (tensorPowerModuleCongr (Y := Y) e m)).hom ≫
        (coherentMulIso Y.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y)
          B n m).hom := by
  have h := Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrCmpTP_mul
    (T := Y) (L := A) (L' := B) e n m
  have hconv : MonoidalCategory.tensorHom
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrCmpTP
          (T := Y) e n).hom
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrCmpTP
          (T := Y) e m).hom =
      (tensorSheafMapIso Y.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y)
        (tensorPowerModuleCongr (Y := Y) e n) (tensorPowerModuleCongr (Y := Y) e m)).hom :=
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback.bridge_tensorIso
      Y.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y)
      (tensorPowerModuleCongr (Y := Y) e n) (tensorPowerModuleCongr (Y := Y) e m)).symm
  rw [hconv] at h
  exact h

/-! ### The composite -/

variable {L : Y.Modules} [Stacks.Ample.IsInvertibleModule Y L]

/-- **`pullbackTwistPowIso` written out.** The five factors in order: the contraction of the
pullback along `Y ⟶ U_d ⟶ Proj 𝒮`; the pullback along `φ` of the inverse of the comparison of the
two power families composed with [Stacks, Tag 01MU]'s `𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(dn)`; the
compatibility of the powers with pullback; and the replacement of `φ^*𝒪(d)` by `L` in every
power at once. -/
theorem pullbackTwistPowIso_hom (α : pullbackTwist 𝒮 φ (d : ℤ) ≅ L) (n : ℤ) :
    (pullbackTwistPowIso 𝒮 d φ α n).hom =
      (pullbackTwistRestrictIso 𝒮 d φ ((d : ℤ) * n)).hom ≫
        (Scheme.Modules.pullback φ).map
          ((Stacks.PowerFamilyBridge.tensorPowerModuleIso
            (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ)) n ≪≫
            thetaInt 𝒮 d n).inv) ≫
        (Stacks.TensorPowerPullback.pullbackIntPowIso φ.toLRSHom.toShHom
          (twist 𝒮 d (d : ℤ)) n).hom ≫
        (tensorPowerModuleCongr ((pullbackTwistRestrictIso 𝒮 d φ (d : ℤ)).symm ≪≫ α) n).hom :=
  rfl

end Stacks.AlgebraicGeometry.PullbackTwistPower

end
