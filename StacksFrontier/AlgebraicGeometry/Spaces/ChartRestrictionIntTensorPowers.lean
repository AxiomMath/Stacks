module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionTensorPowers
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.TensorPowers.Basic
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject

/-!
# The restriction to an étale chart of the integer tensor powers of an invertible module

Let `X` be an algebraic space and `L` an invertible `𝒪_X`-module on its small étale site.  Its
integer tensor powers `L^{⊗ k}`, `k : ℤ`, are Stacks 01CU at the structure sheaf of `X`, that is
`AlgebraicGeometry.SheafOfModules.tensorPow`.  This file identifies the restriction of `L^{⊗ k}`
to the scheme of an étale chart `V` with the `k`-th tensor power of the restriction `L|_V`:

`(L^{⊗ k})|_V ≅ (L|_V)^{⊗ k}` for every `k : ℤ`,

the powers on the right being `Stacks.Ample.tensorPowModule`, the powers of Stacks 01CU on a
scheme.  `AlgebraicGeometry.Space.chartRestrictionSchemeModuleNatTensorPowIso` is the same
statement for the natural-number powers `Stacks.TensorPowers.natTensorPow`.

## Main results

* `AlgebraicGeometry.Space.chartRestrictionSchemeModuleSheafTensorIso`: the restriction of a
  tensor product of quasi-coherent modules is the tensor product of the restrictions, in the
  `Stacks.SheafOfModules.Tensor.sheafTensor` spelling.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_intTensorPowModule`: **every** integer tensor
  power of an invertible module is quasi-coherent — including the negative ones, which are
  powers of its inverse.
* `AlgebraicGeometry.Space.isInvertibleModule_chartRestrictionSchemeModule`: the restriction of
  an invertible module to the chart's scheme is invertible.
* `AlgebraicGeometry.Space.chartRestrictionSchemeModuleIntTensorPowIsoOfNat`: the identification
  in nonnegative degree, by induction on the exponent.
* `AlgebraicGeometry.Space.chartRestrictionSchemeModuleIntTensorPowIso`: **the identification in
  every integer degree.**
* `AlgebraicGeometry.Space.chartRestrictionSchemeModuleTensorIntTensorPowIso`: the same for a
  twist `ℱ ⊗ L^{⊗ k}` of a quasi-coherent module.

## Implementation notes

**Why the negative range is not a corollary of the nonnegative one.**  A negative power
`L^{⊗ -m}` is the `m`-th power of the chosen tensor inverse of `L`
(`AlgebraicGeometry.SheafOfModules.tensorPow_neg_natCast_succ`), and the inverse is produced from
the universal property of tensoring rather than by a formula, so there is nothing to induct on.
What is used instead is that the restriction functor carries the pairing
`L^{⊗ k} ⊗ L^{⊗ -k} ≅ 𝒪_X` to a pairing on the chart, so that `(L^{⊗ k})|_V` and `(L|_V)^{⊗ k}`
are two tensor inverses of one and the same module `(L|_V)^{⊗ -k}`, and tensor inverses are
unique up to isomorphism: `CategoryTheory.MonoidalCategory.HasInverse.inv_iso`.  The exponent
`-k` is nonnegative there, so the nonnegative case supplies the comparison it needs.

**Quasi-coherence of the negative powers.**  Monoidality of the restriction
(`AlgebraicGeometry.Space.restrictToChartTensorIso`) is available only on quasi-coherent
modules, the Zariski restriction being a right adjoint and so only lax monoidal in general, so
the negative powers must be known quasi-coherent before they can be restricted.  They are, with
no local argument: every integer tensor power of an invertible module is invertible
(`AlgebraicGeometry.SheafOfModules.isInvertible_tensorPow`), and an invertible module on the
small étale site of an algebraic space is quasi-coherent, being finite locally free of rank one
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isInvertible`, Stacks 0B8Q).

**The two tensor products on `Modules`.**  `AlgebraicGeometry.Space.modulesMonoidalCategory` and
the monoidal structure `Stacks.SheafInternalHom.monoidalCategory` that
`AlgebraicGeometry.SheafOfModules.tensorPow` is defined by are two localizations of the tensor
product of presheaves of modules along sheafification, and are not the same term; their tensor
products are compared only through the common provider
`Stacks.SheafOfModules.Tensor.sheafTensor`, by
`AlgebraicGeometry.Space.modulesTensorObjIso` on the one side and
`AlgebraicGeometry.SheafOfModules.tensorIso` on the other.  Everything below is therefore stated
in the `sheafTensor` spelling, which needs no monoidal instance at all; the powers themselves
and their addition law `AlgebraicGeometry.SheafOfModules.tensorPowAddIsoSheaf` are already
available in it.  The one place a monoidal structure is needed is the uniqueness of tensor
inverses, and there it is introduced on the *chart*, where both the pairing isomorphisms and
`Stacks.Ample.tensorPowModule` live.

For the same reason this file does not go through
`AlgebraicGeometry.Space.chartRestrictionSchemeModuleNatTensorPowIso`: that statement is about
`Stacks.TensorPowers.natTensorPow` for `AlgebraicGeometry.Space.modulesMonoidalCategory`, which
is isomorphic to but not the same object as `AlgebraicGeometry.SheafOfModules.tensorPow` at a
natural number, and the comparison of the two would have to be built first.  The nonnegative
case is instead re-run by induction directly on the integer powers, out of the addition law.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 0GUT](https://stacks.math.columbia.edu/tag/0GUT)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The restriction to an étale chart of an isomorphism of `𝒪_X`-modules.**  Restriction to
the scheme of a chart is the functor `AlgebraicGeometry.Space.restrictToChartSchemeFunctor`, by
`AlgebraicGeometry.Space.restrictToChart_eq_restrictToChartScheme`. -/
noncomputable def chartRestrictionSchemeModuleMapIso (A : SmallEtale B S hS X.1)
    {F G : Modules.{u, u} B S hS X.1 X.2} (e : F ≅ G) :
    chartRestrictionSchemeModule B S hS X F A ≅ chartRestrictionSchemeModule B S hS X G A :=
  eqToIso (restrictToChart_eq_restrictToChartScheme B S hS X.2 F A) ≪≫
    (restrictToChartSchemeFunctor B S hS X.1 X.2 A).mapIso e ≪≫
    eqToIso (restrictToChart_eq_restrictToChartScheme B S hS X.2 G A).symm

section Monoidality

attribute [local instance] modulesMonoidalCategory

/-- **The restriction to an étale chart of a tensor product of quasi-coherent modules is the
tensor product of the restrictions**, with both tensor products written in the
`Stacks.SheafOfModules.Tensor.sheafTensor` spelling, which needs no monoidal instance to state.
This is `AlgebraicGeometry.Space.restrictToChartTensorIso` with its source read through
`AlgebraicGeometry.Space.modulesTensorObjIso`. -/
noncomputable def chartRestrictionSchemeModuleSheafTensorIso (A : SmallEtale B S hS X.1)
    (F G : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] [G.IsQuasicoherentOnSite] :
    chartRestrictionSchemeModule B S hS X
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS X.1 X.2)).obj F).obj G) A ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(chartScheme A).toRingedSpace.presheaf, (chartScheme A).toRingedSpace.IsSheaf⟩).obj
          (chartRestrictionSchemeModule B S hS X F A)).obj
          (chartRestrictionSchemeModule B S hS X G A) :=
  chartRestrictionSchemeModuleMapIso B S hS X A
      (modulesTensorObjIso B S hS X.1 X.2 F G).symm ≪≫
    restrictToChartTensorIso B S hS X A F G

end Monoidality

section IntegerPowers

variable (L : Modules.{u, u} B S hS X.1 X.2) [IsInvertibleModule X L]

/-- **The integer tensor powers of an invertible `𝒪_X`-module on an algebraic space**, Stacks
01CU at the structure sheaf of the small étale site of `X`. -/
noncomputable abbrev intTensorPowModule (k : ℤ) : Modules.{u, u} B S hS X.1 X.2 :=
  AlgebraicGeometry.SheafOfModules.tensorPow (structureSheaf B S hS X.1 X.2).obj
    (structureRingPresheaf_isSheaf B S hS X.1 X.2) L k

/-- **Every integer tensor power of an invertible `𝒪_X`-module is quasi-coherent**, the negative
ones included. -/
instance isQuasicoherentOnSite_intTensorPowModule (k : ℤ) :
    (intTensorPowModule B S hS X L k).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isInvertible B S hS X _
    (AlgebraicGeometry.SheafOfModules.isInvertible_tensorPow
      (structureSheaf B S hS X.1 X.2).obj (structureRingPresheaf_isSheaf B S hS X.1 X.2) L k)

/-- **The addition law for the restrictions of the integer tensor powers**: the tensor product of
the restrictions of `L^{⊗ a}` and `L^{⊗ b}` is the restriction of `L^{⊗ (a + b)}`.  Monoidality of
the restriction composed with the addition law of Stacks 01CU on `X`. -/
noncomputable def chartRestrictionSchemeModuleIntTensorPowAddIso (A : SmallEtale B S hS X.1)
    (a b : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(chartScheme A).toRingedSpace.presheaf, (chartScheme A).toRingedSpace.IsSheaf⟩).obj
        (chartRestrictionSchemeModule B S hS X (intTensorPowModule B S hS X L a) A)).obj
        (chartRestrictionSchemeModule B S hS X (intTensorPowModule B S hS X L b) A) ≅
      chartRestrictionSchemeModule B S hS X (intTensorPowModule B S hS X L (a + b)) A :=
  (chartRestrictionSchemeModuleSheafTensorIso B S hS X A (intTensorPowModule B S hS X L a)
      (intTensorPowModule B S hS X L b)).symm ≪≫
    chartRestrictionSchemeModuleMapIso B S hS X A
      (AlgebraicGeometry.SheafOfModules.tensorPowAddIsoSheaf
        (structureSheaf B S hS X.1 X.2).obj (structureRingPresheaf_isSheaf B S hS X.1 X.2) L a b)

/-- **The restriction of the zeroth tensor power is the structure sheaf of the chart's scheme.**
-/
noncomputable def chartRestrictionSchemeModuleIntTensorPowZeroIso (A : SmallEtale B S hS X.1) :
    chartRestrictionSchemeModule B S hS X (intTensorPowModule B S hS X L 0) A ≅
      SheafOfModules.unit (chartScheme A).ringCatSheaf :=
  chartRestrictionSchemeModuleMapIso B S hS X A
      (AlgebraicGeometry.SheafOfModules.tensorPowZeroIso (structureSheaf B S hS X.1 X.2).obj
        (structureRingPresheaf_isSheaf B S hS X.1 X.2) L) ≪≫
    eqToIso (restrictToChart_eq_restrictToChartScheme B S hS X.2 _ A) ≪≫
    restrictToChartSchemeUnitIso B S hS X.1 X.2 A

/-- **The pairing of the restrictions of two tensor powers of opposite exponents**:
`(L^{⊗ a})|_V ⊗ (L^{⊗ b})|_V ≅ 𝒪_V` when `a + b = 0`.  This is the restriction of the pairing
`L^{⊗ a} ⊗ L^{⊗ b} ≅ 𝒪_X` of Stacks 01CU on `X`. -/
noncomputable def chartRestrictionSchemeModuleIntTensorPowPairingIso (A : SmallEtale B S hS X.1)
    (a b : ℤ) (hab : a + b = 0) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(chartScheme A).toRingedSpace.presheaf, (chartScheme A).toRingedSpace.IsSheaf⟩).obj
        (chartRestrictionSchemeModule B S hS X (intTensorPowModule B S hS X L a) A)).obj
        (chartRestrictionSchemeModule B S hS X (intTensorPowModule B S hS X L b) A) ≅
      SheafOfModules.unit (chartScheme A).ringCatSheaf :=
  chartRestrictionSchemeModuleIntTensorPowAddIso B S hS X L A a b ≪≫
    chartRestrictionSchemeModuleMapIso B S hS X A
      (eqToIso (congrArg (intTensorPowModule B S hS X L) hab)) ≪≫
    chartRestrictionSchemeModuleIntTensorPowZeroIso B S hS X L A

/-- **The restriction to an étale chart of an invertible `𝒪_X`-module is invertible**, in the
sense of Stacks 01CS. -/
instance isInvertibleModule_chartRestrictionSchemeModule (A : SmallEtale B S hS X.1) :
    Stacks.Ample.IsInvertibleModule (chartScheme A)
      (chartRestrictionSchemeModule B S hS X L A) := by
  let _ : MonoidalCategory ((chartScheme A).Modules) :=
    Stacks.SheafInternalHom.monoidalCategory (chartScheme A).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (chartScheme A))
  let tI : ∀ F G : (chartScheme A).Modules, F ⊗ G ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(chartScheme A).toRingedSpace.presheaf, (chartScheme A).toRingedSpace.IsSheaf⟩).obj
          F).obj G := fun F G =>
    AlgebraicGeometry.SheafOfModules.tensorIso (chartScheme A).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (chartScheme A)) F G
  let uI : 𝟙_ ((chartScheme A).Modules) ≅ SheafOfModules.unit (chartScheme A).ringCatSheaf :=
    AlgebraicGeometry.SheafOfModules.unitIso (chartScheme A).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (chartScheme A))
  let e : chartRestrictionSchemeModule B S hS X (intTensorPowModule B S hS X L 1) A ≅
      chartRestrictionSchemeModule B S hS X L A :=
    chartRestrictionSchemeModuleMapIso B S hS X A
      (AlgebraicGeometry.SheafOfModules.tensorPowOneIso (structureSheaf B S hS X.1 X.2).obj
        (structureRingPresheaf_isSheaf B S hS X.1 X.2) L)
  let h : MonoidalCategory.HasInverse (chartRestrictionSchemeModule B S hS X L A) :=
    { inv := chartRestrictionSchemeModule B S hS X (intTensorPowModule B S hS X L (-1)) A
      isoLeft := whiskerRightIso e.symm _ ≪≫ tI _ _ ≪≫
        chartRestrictionSchemeModuleIntTensorPowPairingIso B S hS X L A 1 (-1) (by ring) ≪≫ uI.symm
      isoRight := whiskerLeftIso _ e.symm ≪≫ tI _ _ ≪≫
        chartRestrictionSchemeModuleIntTensorPowPairingIso B S hS X L A (-1) 1 (by ring) ≪≫
          uI.symm }
  exact (AlgebraicGeometry.SheafOfModules.isInvertible_iff_isEquivalence_tensorLeft
      (chartScheme A).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (chartScheme A)) _).mpr
    (CategoryTheory.Equivalence.isEquivalence_functor h.tensorLeftEquivalence)

/-- **The restriction of the first tensor power is the restriction of `L`,** read as the first
tensor power of the restriction. -/
noncomputable def chartRestrictionSchemeModuleIntTensorPowOneIso (A : SmallEtale B S hS X.1) :
    chartRestrictionSchemeModule B S hS X (intTensorPowModule B S hS X L 1) A ≅
      Stacks.Ample.tensorPowModule (chartScheme A)
        (chartRestrictionSchemeModule B S hS X L A) 1 :=
  chartRestrictionSchemeModuleMapIso B S hS X A
      (AlgebraicGeometry.SheafOfModules.tensorPowOneIso (structureSheaf B S hS X.1 X.2).obj
        (structureRingPresheaf_isSheaf B S hS X.1 X.2) L) ≪≫
    (Stacks.Ample.tensorPowModuleOneIso (chartScheme A)
      (chartRestrictionSchemeModule B S hS X L A)).symm

/-- **The restriction to an étale chart of the `n`-th tensor power of an invertible module is the
`n`-th tensor power of the restriction**, for a natural number `n`.  Induction on `n` out of the
addition law `AlgebraicGeometry.Space.chartRestrictionSchemeModuleIntTensorPowAddIso` on the
chart and `Stacks.Ample.tensorPowModuleAddIso` on the chart's scheme. -/
noncomputable def chartRestrictionSchemeModuleIntTensorPowIsoOfNat (A : SmallEtale B S hS X.1) :
    ∀ n : ℕ, chartRestrictionSchemeModule B S hS X (intTensorPowModule B S hS X L (n : ℤ)) A ≅
      Stacks.Ample.tensorPowModule (chartScheme A)
        (chartRestrictionSchemeModule B S hS X L A) (n : ℤ)
  | 0 =>
    chartRestrictionSchemeModuleIntTensorPowZeroIso B S hS X L A ≪≫
      (Stacks.Ample.tensorPowModuleZeroIso (chartScheme A)
        (chartRestrictionSchemeModule B S hS X L A)).symm
  | n + 1 => by
    let T := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(chartScheme A).toRingedSpace.presheaf, (chartScheme A).toRingedSpace.IsSheaf⟩
    exact chartRestrictionSchemeModuleMapIso B S hS X A
        (eqToIso (congrArg (intTensorPowModule B S hS X L)
          (show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring))) ≪≫
      (chartRestrictionSchemeModuleIntTensorPowAddIso B S hS X L A (n : ℤ) 1).symm ≪≫
      (T.mapIso (chartRestrictionSchemeModuleIntTensorPowIsoOfNat A n)).app
        (chartRestrictionSchemeModule B S hS X (intTensorPowModule B S hS X L 1) A) ≪≫
      (T.obj (Stacks.Ample.tensorPowModule (chartScheme A)
          (chartRestrictionSchemeModule B S hS X L A) (n : ℤ))).mapIso
        (chartRestrictionSchemeModuleIntTensorPowOneIso B S hS X L A) ≪≫
      Stacks.Ample.tensorPowModuleAddIso (chartScheme A)
        (chartRestrictionSchemeModule B S hS X L A) (n : ℤ) 1 ≪≫
      eqToIso (congrArg (Stacks.Ample.tensorPowModule (chartScheme A)
        (chartRestrictionSchemeModule B S hS X L A))
        (show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring))

/-- **The restriction to an étale chart of a tensor power of negative exponent.**  For `k` with
`-k` the natural number `m`, the restriction of `L^{⊗ k}` and the `k`-th power of the restriction
are both tensor inverses of `(L|_V)^{⊗ -k}`: the first because the restriction carries the
pairings `L^{⊗ k} ⊗ L^{⊗ -k} ≅ 𝒪_X` of Stacks 01CU to pairings on the chart, and `(L^{⊗ -k})|_V`
is `(L|_V)^{⊗ -k}` by the nonnegative case; the second by Stacks 01CU on the chart's scheme.
Tensor inverses are unique up to isomorphism. -/
noncomputable def chartRestrictionSchemeModuleIntTensorPowIsoOfNeg (A : SmallEtale B S hS X.1)
    (k : ℤ) (m : ℕ) (hm : -k = (m : ℤ)) :
    chartRestrictionSchemeModule B S hS X (intTensorPowModule B S hS X L k) A ≅
      Stacks.Ample.tensorPowModule (chartScheme A)
        (chartRestrictionSchemeModule B S hS X L A) k := by
  letI : MonoidalCategory ((chartScheme A).Modules) :=
    Stacks.SheafInternalHom.monoidalCategory (chartScheme A).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (chartScheme A))
  let tI : ∀ F G : (chartScheme A).Modules, F ⊗ G ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(chartScheme A).toRingedSpace.presheaf, (chartScheme A).toRingedSpace.IsSheaf⟩).obj
          F).obj G := fun F G =>
    AlgebraicGeometry.SheafOfModules.tensorIso (chartScheme A).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (chartScheme A)) F G
  let uI : 𝟙_ ((chartScheme A).Modules) ≅ SheafOfModules.unit (chartScheme A).ringCatSheaf :=
    AlgebraicGeometry.SheafOfModules.unitIso (chartScheme A).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (chartScheme A))
  let e : chartRestrictionSchemeModule B S hS X (intTensorPowModule B S hS X L (-k)) A ≅
      Stacks.Ample.tensorPowModule (chartScheme A)
        (chartRestrictionSchemeModule B S hS X L A) (-k) :=
    chartRestrictionSchemeModuleMapIso B S hS X A
        (eqToIso (congrArg (intTensorPowModule B S hS X L) hm)) ≪≫
      chartRestrictionSchemeModuleIntTensorPowIsoOfNat B S hS X L A m ≪≫
      eqToIso (congrArg (Stacks.Ample.tensorPowModule (chartScheme A)
        (chartRestrictionSchemeModule B S hS X L A)) hm.symm)
  let pair : ∀ a b : ℤ, a + b = 0 →
      (chartRestrictionSchemeModule B S hS X (intTensorPowModule B S hS X L a) A ⊗
        chartRestrictionSchemeModule B S hS X (intTensorPowModule B S hS X L b) A ≅
          𝟙_ ((chartScheme A).Modules)) := fun a b hab =>
    tI _ _ ≪≫ chartRestrictionSchemeModuleIntTensorPowPairingIso B S hS X L A a b hab ≪≫ uI.symm
  let pair' : ∀ a b : ℤ, a + b = 0 →
      (Stacks.Ample.tensorPowModule (chartScheme A)
          (chartRestrictionSchemeModule B S hS X L A) a ⊗
        Stacks.Ample.tensorPowModule (chartScheme A)
          (chartRestrictionSchemeModule B S hS X L A) b ≅
          𝟙_ ((chartScheme A).Modules)) := fun a b hab =>
    tI _ _ ≪≫ Stacks.Ample.tensorPowModuleAddIso (chartScheme A)
        (chartRestrictionSchemeModule B S hS X L A) a b ≪≫
      eqToIso (congrArg (Stacks.Ample.tensorPowModule (chartScheme A)
        (chartRestrictionSchemeModule B S hS X L A)) hab) ≪≫
      Stacks.Ample.tensorPowModuleZeroIso (chartScheme A)
        (chartRestrictionSchemeModule B S hS X L A) ≪≫ uI.symm
  let h₁ : MonoidalCategory.HasInverse (Stacks.Ample.tensorPowModule (chartScheme A)
      (chartRestrictionSchemeModule B S hS X L A) (-k)) :=
    { inv := chartRestrictionSchemeModule B S hS X (intTensorPowModule B S hS X L k) A
      isoLeft := whiskerRightIso e.symm _ ≪≫ pair (-k) k (by ring)
      isoRight := whiskerLeftIso _ e.symm ≪≫ pair k (-k) (by ring) }
  let h₂ : MonoidalCategory.HasInverse (Stacks.Ample.tensorPowModule (chartScheme A)
      (chartRestrictionSchemeModule B S hS X L A) (-k)) :=
    { inv := Stacks.Ample.tensorPowModule (chartScheme A)
        (chartRestrictionSchemeModule B S hS X L A) k
      isoLeft := pair' (-k) k (by ring)
      isoRight := pair' k (-k) (by ring) }
  exact MonoidalCategory.HasInverse.inv_iso h₁ h₂

/-- **The restriction to an étale chart of the `k`-th tensor power of an invertible module is the
`k`-th tensor power of the restriction, for every integer `k`.**  This is the ℤ-indexed analogue
of `AlgebraicGeometry.Space.chartRestrictionSchemeModuleNatTensorPowIso`; in nonnegative degree
it is an induction on the exponent, and in negative degree it is the uniqueness of tensor
inverses. -/
noncomputable def chartRestrictionSchemeModuleIntTensorPowIso (A : SmallEtale B S hS X.1) :
    ∀ k : ℤ, chartRestrictionSchemeModule B S hS X (intTensorPowModule B S hS X L k) A ≅
      Stacks.Ample.tensorPowModule (chartScheme A)
        (chartRestrictionSchemeModule B S hS X L A) k
  | .ofNat n => chartRestrictionSchemeModuleIntTensorPowIsoOfNat B S hS X L A n
  | .negSucc n =>
    chartRestrictionSchemeModuleIntTensorPowIsoOfNeg B S hS X L A (.negSucc n) (n + 1) (by lia)

/-- **The restriction to an étale chart of a twist `ℱ ⊗ L^{⊗ k}` of a quasi-coherent module, for
every integer `k`**, is the corresponding twist of the restriction of `ℱ` by the `k`-th power of
`L|_V`. -/
noncomputable def chartRestrictionSchemeModuleTensorIntTensorPowIso (A : SmallEtale B S hS X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (k : ℤ) :
    chartRestrictionSchemeModule B S hS X
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS X.1 X.2)).obj F).obj (intTensorPowModule B S hS X L k)) A ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(chartScheme A).toRingedSpace.presheaf, (chartScheme A).toRingedSpace.IsSheaf⟩).obj
          (chartRestrictionSchemeModule B S hS X F A)).obj
          (Stacks.Ample.tensorPowModule (chartScheme A)
            (chartRestrictionSchemeModule B S hS X L A) k) :=
  chartRestrictionSchemeModuleSheafTensorIso B S hS X A F (intTensorPowModule B S hS X L k) ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(chartScheme A).toRingedSpace.presheaf, (chartScheme A).toRingedSpace.IsSheaf⟩).obj
        (chartRestrictionSchemeModule B S hS X F A)).mapIso
      (chartRestrictionSchemeModuleIntTensorPowIso B S hS X L A k)

end IntegerPowers

end AlgebraicGeometry.Space

end
