module

public import StacksFrontier.AlgebraicGeometry.IdealPowerHomColimit.Basic
public import StacksFrontier.AlgebraicGeometry.Locality.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTwistProduct
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.RestrictTensorSection

/-!
# A trivialisation on the unit section, and the chart pairing `hpair` of Tag 0B3V clause 3

This file computes two families of section formulas and combines them into the chart pairing
`hpair`: on a chart, the frame section `q s` and the section `w` of `𝓛^{⊗ -1}` named by the
chart's trivialisation pair to `1`. This is the hypothesis `hpair` of
`exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app_pinned`, which pins the section `w₀`
of `𝒪(-1)` in the source half of [Stacks, Tag 0B3V] clause 3.

* **The value of a trivialisation on the unit section.** The trivialisation
  `Stacks.SheafOfModules.isoUnitOver` is `c ↦ c · a` on sections, and the trivialisation
  `Stacks.AlgebraicGeometry.TwistMapsInvertible.restrictIsoUnitOfOverIsoUnit` built from it
  carries the unit section to the generating section, using
  `Stacks.AlgebraicGeometry.IdealPowerHomColimit.restrictUnitIso_inv_val_app_one`.
* **The pairing of a trivialisation of `𝓛` against the trivialisation of `𝓛^{⊗ -1}` it
  induces.** The pairing of `τ⁻¹ 1` with
  `(Stacks.ProjectiveBundleConormal.restrictInverseTwistIso L U τ)⁻¹ 1` is `1`; it is the
  composite of five section formulas, one of which is the left unitor formula
  `leftUnitor_inv_tensorSectionsAt`.

## Main results

* `Stacks.SheafOfModules.isoUnitOver_inv_val_app` and `isoUnitOver_inv_val_app_one`: **the
  trivialisation a generating section defines, on a section.** Over an object of the slice site it
  is `c ↦ c · a`, so at `c = 1` it is `a` restricted.
* `Stacks.ProjectiveBundleConormal.restrictIsoUnitOfSpanEqTop_inv_val_app_one`: **the first
  missing formula.** The trivialisation that a spanning section `t` of an invertible module
  defines on an affine open carries the unit section to `t`.
* `Stacks.ProjectiveBundleConormal.chartTrivialisation_inv_val_app_one`: the same at the chart's
  own trivialisation, where `t` is the frame section `q s`.
* `Stacks.ProjectiveBundleConormal.leftUnitor_inv_tensorSectionsAt`: **the inverse of the left
  unitor inserts the unit section on the left**, the companion of
  `Stacks.ProjectiveBundleConormal.rightUnitor_inv_tensorSectionsAt`.
* `Stacks.ProjectiveBundleConormal.restrictInverseTwistIso_hom_val_app`: **the trivialisation of
  the inverse twist, read on a section**, as the pairing against `τ⁻¹ 1`.
* `Stacks.ProjectiveBundleConormal.sectionMulNegOne_restrictInverseTwistIso_inv_one`: **the second
  missing formula.** `pairing(τ⁻¹ 1, (restrictInverseTwistIso L U τ)⁻¹ 1) = 1`.
* `Stacks.SheafOfModules.tensorPairing_eq_hom_tensorSectionsAt`,
  `Stacks.ProjectiveBundleConormal.negOneMulPairingIso'_hom_tensorSectionsAt` and
  `tensorPairing_negOneMulPairingIso'`: **the crossing from
  `Stacks.SheafOfModules.Invertible.sectionMulNegOne` to `Stacks.SheafOfModules.tensorPairing`
  against `Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'`**, which is the spelling
  `hpair` is stated in.
* `Stacks.ProjectiveBundleConormal.tensorPairing_chartTrivialisation_eq_unitSection`: **`hpair`,
  discharged on a chart.** For the chart data the cover
  `Stacks.ProjectiveBundleConormal.exists_affine_open_chartData` returns, the frame section `q s`
  and the generator of `𝓛^{⊗ -1}` that the induced trivialisation names pair to `1`.

## Implementation notes

**`ψ` must stay a variable where `Stacks.SheafOfModules.tensorPairing` is unfolded.** Reading
`tensorPairing ψ V a b` as `ψ.hom.val.app (op V) (tensorSectionsAt … a b)` is a `rfl` when `ψ` is
a variable and a `(deterministic) timeout at whnf` after 200000 heartbeats when `ψ` is the
composite `Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'` written out. Hence
`Stacks.SheafOfModules.tensorPairing_eq_hom_tensorSectionsAt` is stated with `ψ` abstract and
applied.

**`Stacks.SheafOfModules.tensorObjIso` and `AlgebraicGeometry.SheafOfModules.tensorIso` cannot be
crossed on a section by `rfl`.** Only their `hom` fields are definitionally equal, as
`Stacks.ProjectiveBundleConormal.tensorObjIso_eq_tensorIso` records; the crossing here is in the
`inv` direction, and forcing it as a `rfl` is a `(deterministic) timeout at isDefEq`.
`PresheafOfModules.hom_congr_apply` of that equation is what crosses it, the same device
`Stacks.ProjectiveBundleConormal.sectionMulNegOne_eq_negOneMulIso` uses.

**The generation hypothesis of `Stacks.SheafOfModules.isoUnitOver` is bound existentially.**
`Stacks.ProjectiveBundleConormal.restrictIsoUnitOfSpanEqTop` is a tactic definition with two
`haveI`s and a `have` in front of it, and the trivialisation it returns is
`restrictIsoUnitOfOverIsoUnit` of `isoUnitOver` at a generation proof built inside. Naming that
proof's *type* in the scheme spelling does not elaborate — `HSMul` fails to synthesise, because
`L.val.map` lands in a `ModuleCat.restrictScalars` and the instance is found only at the
`structureSheafRing` spelling of a ringed space. Binding it existentially, as
`∃ hgen, restrictIsoUnitOfSpanEqTop … = restrictIsoUnitOfOverIsoUnit L U (isoUnitOver … hgen)`
with proof `⟨_, rfl⟩`, lets Lean infer the type from `isoUnitOver`'s own signature; the equation is
a `rfl` because the prefix affects only a proof term. Same reason puts
`Stacks.SheafOfModules.isoUnitOver_inv_val_app` in the ringed-space namespace rather than restating
it on a scheme.

**Nothing is rewritten on a module**; the one `rw` below is of an equation between two
isomorphisms, not on a section.

## Not done here

**No `@[stacks 0B3V]` attribute is attached.** `hpair` is one hypothesis of one of the two inputs
of clause 3's chart computation. What the clause still owes is the coordinate computation `hxκ`
and the assembly against the target identification; see the "What is not done" of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartMeeting`, which this file updates.

**`hpair` is discharged only for the chart data the cover returns.** It is false for an arbitrary
trivialisation: there the pairing is a unit and nothing determines it. The equation
`τ = Stacks.ProjectiveBundleConormal.chartTrivialisation …` that
`Stacks.ProjectiveBundleConormal.exists_affine_open_chartData` now carries is exactly what makes
the value `1` available, and
`tensorPairing_chartTrivialisation_eq_unitSection` consumes it by being stated at
`chartTrivialisation` itself.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory TopologicalSpace
open Opposite
open Stacks.SheafOfModules (tensorSectionsAt)
open Stacks.SheafOfModules.Invertible (sectionMulNegOne tensorPower)

universe u

namespace Stacks.SheafOfModules

variable {Y : RingedSpace.{u, u}} (N : _root_.SheafOfModules.{u} (structureSheafRing Y))

/-- **The trivialisation a generating section defines, read on a section.** Over an object `A` of
the slice site `Over W`, the inverse of `Stacks.SheafOfModules.isoUnitOver` at `a` sends a function
`c` to `c · a|_{A.left}`: that is what `LinearMap.toSpanSingleton` is, so this is a `rfl`.

`isoUnitOver` carried no `_app`, `_val_app` or `_apply` lemma of any kind, and no consumer stated
an equation about it, which is what made the value of a trivialisation on the unit section
unavailable all the way up to the chart computation of [Stacks, Tag 0B3V] clause 3. The scalar
action is written in the ringed-space spelling because that is the only one whose `HSMul` instance
synthesises here; see this module's implementation notes. -/
theorem isoUnitOver_inv_val_app (W : Opens Y.carrier) (a : N.val.obj (op W))
    (ha : ∀ (V : Opens Y.carrier) (hVW : V ≤ W),
      Function.Bijective fun c : Y.presheaf.obj (op V) => c • (N.val.map (homOfLE hVW).op a))
    (A : (Over W)ᵒᵖ) (c : Y.presheaf.obj (op A.unop.left)) :
    (isoUnitOver N W a ha).inv.val.app A c =
      c • (N.val.map (homOfLE (leOfHom A.unop.hom)).op a) := rfl

/-- **The trivialisation a generating section defines carries the unit section to that section**,
restricted to the open the slice object names. This is
`Stacks.SheafOfModules.isoUnitOver_inv_val_app` at `c = 1` and `one_smul`; the `change` is what
re-elaborates the scalar action so that the instance is found, the statement itself being read at
the section module of `N.over W`. -/
theorem isoUnitOver_inv_val_app_one (W : Opens Y.carrier) (a : N.val.obj (op W))
    (ha : ∀ (V : Opens Y.carrier) (hVW : V ≤ W),
      Function.Bijective fun c : Y.presheaf.obj (op V) => c • (N.val.map (homOfLE hVW).op a))
    (A : (Over W)ᵒᵖ) :
    (isoUnitOver N W a ha).inv.val.app A (1 : Y.presheaf.obj (op A.unop.left)) =
      N.val.map (homOfLE (leOfHom A.unop.hom)).op a := by
  refine Eq.trans (isoUnitOver_inv_val_app N W a ha A 1) ?_
  show (1 : Y.presheaf.obj (op A.unop.left)) •
    (N.val.map (homOfLE (leOfHom A.unop.hom)).op a) = _
  exact one_smul _ _

/-- **The pairing determined by a trivialisation of a tensor product sheaf, read as the
trivialisation on a product section.** A `rfl`: `Stacks.SheafOfModules.tensorPairing` is `ψ`
applied to the image of the pure tensor, and that image is
`Stacks.SheafOfModules.tensorSectionsAt`.

**`ψ` is a variable and must stay one.** With `ψ` abstract this identification costs nothing;
with `ψ` replaced by a composite — `Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'`, the
one `hpair` is stated at — the kernel unfolds the composite as well and the same `rfl` is a
deterministic timeout at `whnf`. A consumer therefore applies this lemma and splits the
composite separately. -/
theorem tensorPairing_eq_hom_tensorSectionsAt
    {M P : _root_.SheafOfModules.{u} (structureSheafRing Y)}
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(Y).presheaf, (Y).IsSheaf⟩).obj (M)).obj
        (P)) ≅
      _root_.SheafOfModules.unit (structureSheafRing Y))
    (V : Opens Y.carrier) (a : M.val.obj (op V)) (b : P.val.obj (op V)) :
    tensorPairing ψ V a b =
      ψ.hom.val.app (op V)
        (tensorSectionsAt Y.presheaf (structureSheafRing Y).property (op V) M P a b) := rfl

end Stacks.SheafOfModules

namespace Stacks.ProjectiveBundleConormal

attribute [local instance] monoidalSheafTensor

variable {X : Scheme.{u}}

/-! ### A trivialisation built from a spanning section, on the unit section -/

/-- **The equivalence of `AlgebraicGeometry.Scheme.Modules.overEquiv` acts on a morphism by
re-indexing the open.** The functor is a pushforward along
`TopologicalSpace.Opens.overEquivalence` inverse, so on sections over `V` it is the morphism read
at the slice object that inverse names; a `rfl`. -/
theorem overEquiv_functor_map_val_app (U : X.Opens)
    {M N : _root_.SheafOfModules.{u} (X.ringCatSheaf.over U)} (ψ : M ⟶ N)
    (V : (↑U : Scheme.{u}).Opens)
    (y : ((Scheme.Modules.overEquiv U).functor.obj M).val.obj (op V)) :
    ((Scheme.Modules.overEquiv U).functor.map ψ).val.app (op V) y =
      ψ.val.app (op ((Opens.overEquivalence U).inverse.obj V)) y := rfl

/-- **Triviality on the slice site transported to the open subscheme, read on a section.** The
inverse of `Stacks.AlgebraicGeometry.TwistMapsInvertible.restrictIsoUnitOfOverIsoUnit` is the unit
comparison `Stacks.AlgebraicGeometry.CoherentFinite.overFunctorUnitIso` followed by `e.inv`
transported along `AlgebraicGeometry.Scheme.Modules.overEquiv`; the third factor,
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`, is the **identity** on sections, so it does
not appear. A `rfl`. -/
theorem restrictIsoUnitOfOverIsoUnit_inv_val_app (L : X.Modules) (U : X.Opens)
    (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : (↑U : Scheme.{u}).Opens) (z : Γ((↑U : Scheme.{u}), V)) :
    (Stacks.AlgebraicGeometry.TwistMapsInvertible.restrictIsoUnitOfOverIsoUnit L U e).inv.val.app
        (op V) z =
      ((Scheme.Modules.overEquiv U).functor.map e.inv).val.app (op V)
        ((Stacks.AlgebraicGeometry.CoherentFinite.overFunctorUnitIso U).hom.val.app (op V) z) :=
  rfl

/-- **A trivialisation built from a spanning section carries the unit section to that section.**
If `t : Γ(L, U)` spans the sections of an invertible `L` on an affine open `U`, the trivialisation
`Stacks.ProjectiveBundleConormal.restrictIsoUnitOfSpanEqTop` it defines has
`θ⁻¹(1) = t`, restricted to `U.ι ''ᵁ V`.

**This is the first of the two section formulas that item 2 of the "What is not done" of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartMeeting` recorded as missing from the
whole development**, and with it the obstruction `hpair` of clause 3's chart computation becomes
an identity rather than an unknown unit. The chain is
`Stacks.ProjectiveBundleConormal.restrictIsoUnitOfOverIsoUnit_inv_val_app`, the unit comparison
(`Stacks.AlgebraicGeometry.IdealPowerHomColimit.restrictUnitIso_inv_val_app_one`, the one link the
record named as available), `overEquiv_functor_map_val_app`, and
`Stacks.SheafOfModules.isoUnitOver_inv_val_app_one`; every step but the first and the last is a
`rfl`.

The generation hypothesis of `Stacks.SheafOfModules.isoUnitOver` is bound existentially rather
than named: see this module's implementation notes. -/
theorem restrictIsoUnitOfSpanEqTop_inv_val_app_one (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (U : X.Opens) (hU : IsAffineOpen U) (t : Γ(L, U))
    (ht : Submodule.span Γ(X, U) {t} = ⊤)
    (V : (↑U : Scheme.{u}).Opens) (h : U.ι ''ᵁ V ≤ U) :
    (restrictIsoUnitOfSpanEqTop L U hU t ht).inv.val.app (op V)
        (1 : Γ((↑U : Scheme.{u}), V)) = L.val.map (homOfLE h).op t := by
  obtain ⟨hgen, heq⟩ :
      ∃ hgen, restrictIsoUnitOfSpanEqTop L U hU t ht =
        Stacks.AlgebraicGeometry.TwistMapsInvertible.restrictIsoUnitOfOverIsoUnit L U
          (Stacks.SheafOfModules.isoUnitOver (X := X.toRingedSpace) L U t hgen) := ⟨_, rfl⟩
  rw [heq]
  refine Eq.trans (restrictIsoUnitOfOverIsoUnit_inv_val_app L U
    (Stacks.SheafOfModules.isoUnitOver (X := X.toRingedSpace) L U t hgen) V 1) ?_
  refine Eq.trans (congrArg
    (fun y : Γ(SheafOfModules.unit X.ringCatSheaf, U.ι ''ᵁ V) =>
      ((Scheme.Modules.overEquiv U).functor.map
        (Stacks.SheafOfModules.isoUnitOver (X := X.toRingedSpace) L U t hgen).inv).val.app
        (op V) y)
    (Stacks.AlgebraicGeometry.IdealPowerHomColimit.restrictUnitIso_inv_val_app_one U V)) ?_
  refine Eq.trans (overEquiv_functor_map_val_app U
    (Stacks.SheafOfModules.isoUnitOver (X := X.toRingedSpace) L U t hgen).inv V _) ?_
  exact Stacks.SheafOfModules.isoUnitOver_inv_val_app_one (Y := X.toRingedSpace) L U t hgen _

/-! ### The inverse twist trivialisation on the unit section -/

/-- **The inverse of the left unitor inserts the unit section on the left.** The companion of
`Stacks.ProjectiveBundleConormal.rightUnitor_inv_tensorSectionsAt`, and the one factor of
`Stacks.ProjectiveBundleConormal.restrictInverseTwistIso` whose section formula the development did
not have. As there, `monoidalSheafTensor` re-seats its constraints, so
`SheafOfModules.leftUnitor_sheafTensor_eq_iso` is what identifies `λ_` with the unitor of the
tensor product sheaf and `Stacks.SheafOfModules.tensorSheafUnitLeftIso_inv_app` is the formula on
the far side. -/
theorem leftUnitor_inv_tensorSectionsAt (M : X.Modules) (V : X.Opens) (t : M.val.obj (op V)) :
    (λ_ M).inv.val.app (op V) t =
      tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op V) (𝟙_ X.Modules) M (1 : Γ(X, V)) t :=
  (congrArg (fun i : 𝟙_ X.Modules ⊗ M ≅ M => i.inv.val.app (op V) t)
      (_root_.SheafOfModules.leftUnitor_sheafTensor_eq_iso X.toRingedSpace.sheaf M)).trans
    (Stacks.SheafOfModules.tensorSheafUnitLeftIso_inv_app _ _ M (op V) t)

section Inverse

variable (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]

/-- **The trivialisation of the inverse twist induced by a trivialisation of `L`, read on a
section.** Its value at `w` is the pairing of `τ⁻¹(1)` with `w`, crossed to the open subscheme.

`Stacks.ProjectiveBundleConormal.restrictInverseTwistIso` is a five-fold composite and each factor
contributes exactly one section formula: the left unitor is
`Stacks.ProjectiveBundleConormal.leftUnitor_inv_tensorSectionsAt`, the whiskered `τ⁻¹` is
`Stacks.ProjectiveBundleConormal.tensorSectionsAt_whiskerRight`, Tag 01CD along `U.ι` is
`Stacks.ProjectiveBundleConormal.restrictTensorIso_inv_tensorSectionsAt`, and the last two are
left as they stand so that the consumer may cancel them. Composites are split on sections by
`AlgebraicGeometry.SheafOfModules.comp_val_app_apply`, which is `rfl`. -/
theorem restrictInverseTwistIso_hom_val_app (U : X.Opens)
    (τ : (Scheme.Modules.restrictFunctor U.ι).obj L ≅ 𝟙_ (↑U : Scheme.{u}).Modules)
    (V : (↑U : Scheme.{u}).Opens) (h : V ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V))
    (w : ((Scheme.Modules.restrictFunctor U.ι).obj
      (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))).val.obj (op V)) :
    (restrictInverseTwistIso L U τ).hom.val.app (op V) w =
      (restrictUnitMonoidalIso U).hom.val.app (op V)
        ((invertibleEvaluation L).hom.val.app (op (U.ι ''ᵁ V))
          (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op (U.ι ''ᵁ V)) L
            (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))
            (τ.inv.val.app (op V) (1 : Γ((↑U : Scheme.{u}), V))) w)) := by
  refine Eq.trans (congrArg
    (fun φ : (Scheme.Modules.restrictFunctor U.ι).obj
          (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) ⟶
        𝟙_ (↑U : Scheme.{u}).Modules => φ.val.app (op V) w)
    (congrArg Iso.hom
      (rfl : restrictInverseTwistIso L U τ =
        (λ_ ((Scheme.Modules.restrictFunctor U.ι).obj
            (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)))).symm ≪≫
          whiskerRightIso τ.symm _ ≪≫
          (restrictTensorIso U L
            (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))).symm ≪≫
          (Scheme.Modules.restrictFunctor U.ι).mapIso (invertibleEvaluation L) ≪≫
          restrictUnitMonoidalIso U))) ?_
  refine Eq.trans (congrArg
    (fun y : (𝟙_ (↑U : Scheme.{u}).Modules ⊗ (Scheme.Modules.restrictFunctor U.ι).obj
        (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))).val.obj (op V) =>
      (restrictUnitMonoidalIso U).hom.val.app (op V)
        (((Scheme.Modules.restrictFunctor U.ι).map (invertibleEvaluation L).hom).val.app (op V)
          ((restrictTensorIso U L
              (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))).inv.val.app (op V)
            ((τ.inv ▷ (Scheme.Modules.restrictFunctor U.ι).obj
                (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))).val.app (op V) y))))
    (leftUnitor_inv_tensorSectionsAt
      ((Scheme.Modules.restrictFunctor U.ι).obj
        (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))) V w)) ?_
  refine Eq.trans (congrArg
    (fun y : ((Scheme.Modules.restrictFunctor U.ι).obj L ⊗
        (Scheme.Modules.restrictFunctor U.ι).obj
          (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))).val.obj (op V) =>
      (restrictUnitMonoidalIso U).hom.val.app (op V)
        (((Scheme.Modules.restrictFunctor U.ι).map (invertibleEvaluation L).hom).val.app (op V)
          ((restrictTensorIso U L
              (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))).inv.val.app (op V) y)))
    (tensorSectionsAt_whiskerRight τ.inv
      ((Scheme.Modules.restrictFunctor U.ι).obj
        (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))) V
      (1 : Γ((↑U : Scheme.{u}), V)) w)) ?_
  exact congrArg
    (fun y : ((Scheme.Modules.restrictFunctor U.ι).obj
        (L ⊗ tensorPower X.presheaf X.ringCatSheaf.2 L (-1))).val.obj (op V) =>
      (restrictUnitMonoidalIso U).hom.val.app (op V)
        (((Scheme.Modules.restrictFunctor U.ι).map (invertibleEvaluation L).hom).val.app (op V) y))
    (restrictTensorIso_inv_tensorSectionsAt U L
      (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) V h
      (τ.inv.val.app (op V) (1 : Γ((↑U : Scheme.{u}), V))) w)

/-- **A trivialisation of `L` and the trivialisation of `L^{⊗ -1}` it induces name a pairing
inverse pair.** The two sections `τ⁻¹(1)` and `(restrictInverseTwistIso L U τ)⁻¹(1)` multiply to
`1`.

**This is the second of the two section formulas that item 2 of the "What is not done" of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartMeeting` recorded as missing.** It is
`Stacks.ProjectiveBundleConormal.restrictInverseTwistIso_hom_val_app` read at
`(restrictInverseTwistIso L U τ).inv (1)` — where the left-hand side is `1` because an isomorphism
undoes its inverse — followed by
`Stacks.ProjectiveBundleConormal.invertibleEvaluation_tensorSectionsAt`, with the restriction of
the structure sheaf cancelled by
`Stacks.AlgebraicGeometry.IdealPowerHomColimit.restrictUnitIso_inv_val_app_one`. No invertibility
input beyond that `restrictInverseTwistIso` exists is used: the identity holds *because* the
inverse trivialisation is built out of the evaluation pairing. -/
theorem sectionMulNegOne_restrictInverseTwistIso_inv_one (U : X.Opens)
    (τ : (Scheme.Modules.restrictFunctor U.ι).obj L ≅ 𝟙_ (↑U : Scheme.{u}).Modules)
    (V : (↑U : Scheme.{u}).Opens) (h : V ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V)) :
    sectionMulNegOne X.presheaf X.ringCatSheaf.2 L (op (U.ι ''ᵁ V))
        (τ.inv.val.app (op V) (1 : Γ((↑U : Scheme.{u}), V)))
        ((restrictInverseTwistIso L U τ).inv.val.app (op V)
          (1 : Γ((↑U : Scheme.{u}), V))) = (1 : Γ(X, U.ι ''ᵁ V)) := by
  have key : (restrictUnitMonoidalIso U).hom.val.app (op V)
      (sectionMulNegOne X.presheaf X.ringCatSheaf.2 L (op (U.ι ''ᵁ V))
        (τ.inv.val.app (op V) (1 : Γ((↑U : Scheme.{u}), V)))
        ((restrictInverseTwistIso L U τ).inv.val.app (op V)
          (1 : Γ((↑U : Scheme.{u}), V)))) = (1 : Γ((↑U : Scheme.{u}), V)) := by
    refine Eq.trans (congrArg
      (fun z : Γ((Scheme.Modules.restrictFunctor U.ι).obj (𝟙_ X.Modules), V) =>
        (restrictUnitMonoidalIso U).hom.val.app (op V) z)
      (invertibleEvaluation_tensorSectionsAt L (U.ι ''ᵁ V)
        (τ.inv.val.app (op V) (1 : Γ((↑U : Scheme.{u}), V)))
        ((restrictInverseTwistIso L U τ).inv.val.app (op V)
          (1 : Γ((↑U : Scheme.{u}), V))))).symm ?_
    refine Eq.trans (restrictInverseTwistIso_hom_val_app L U τ V h
      ((restrictInverseTwistIso L U τ).inv.val.app (op V)
        (1 : Γ((↑U : Scheme.{u}), V)))).symm ?_
    exact Stacks.SheafOfModules.hom_val_app_inv_val_app (restrictInverseTwistIso L U τ) (op V)
      (1 : Γ((↑U : Scheme.{u}), V))
  refine Eq.trans (Stacks.SheafOfModules.inv_val_app_hom_val_app (restrictUnitMonoidalIso U)
    (op V) _).symm ?_
  refine Eq.trans (congrArg
    (fun z : Γ(𝟙_ (↑U : Scheme.{u}).Modules, V) =>
      (restrictUnitMonoidalIso U).inv.val.app (op V) z) key) ?_
  exact Stacks.AlgebraicGeometry.IdealPowerHomColimit.restrictUnitIso_inv_val_app_one U V

/-! ### The pairing crossing -/

/-- **`Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'` on a product section is
`Stacks.SheafOfModules.Invertible.sectionMulNegOne`.** The left trivialisation of the tensor
product sheaf and the multiplication of a section of `L` with a section of `L^{⊗ -1}` are the same
function of the two sections.

The composite splits by `rfl` at the morphism level; the crossing of
`Stacks.SheafOfModules.tensorObjIso` with `AlgebraicGeometry.SheafOfModules.tensorIso` is
`Stacks.ProjectiveBundleConormal.tensorObjIso_eq_tensorIso` applied through
`PresheafOfModules.hom_congr_apply` — **not** by `rfl`, whose cost is recorded in this module's
implementation notes — and the two sides then meet at the successor comparison of
[Stacks, Tag 01CU], through
`Stacks.ProjBundleInverseBaseChange.negOneMulIso'_hom_tensorSectionsAt` on one side and
`Stacks.ProjectiveBundleConormal.sectionMulNegOne_eq_negOneMulIso_tensorIso` together with
`Stacks.ProjBundleInverseBaseChange.negOneMulIso_hom_tensorSectionsAt` on the other. -/
theorem negOneMulPairingIso'_hom_tensorSectionsAt (V : X.Opens) (a : Γ(L, V))
    (b : Γ(tensorPower X.presheaf X.ringCatSheaf.2 L (-1), V)) :
    (Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'
          (X := X.toRingedSpace) L).hom.val.app (op V)
        (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op V) L
          (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) a b) =
      sectionMulNegOne X.presheaf X.ringCatSheaf.2 L (op V) a b := by
  refine Eq.trans (congrArg
    (fun φ : (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).obj (L)).obj
          (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))) ⟶
        _root_.SheafOfModules.unit (_root_.structureSheafRing X.toRingedSpace) =>
      φ.val.app (op V)
        (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op V) L
          (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) a b))
    (congrArg Iso.hom
      (rfl : Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'
            (X := X.toRingedSpace) L =
        (Stacks.SheafOfModules.tensorObjIso X.presheaf X.ringCatSheaf.2 L
            (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))).symm ≪≫
          Stacks.ProjBundleInverseBaseChange.negOneMulIso' X.presheaf X.ringCatSheaf.2 L ≪≫
          Stacks.SheafOfModules.sheafifyUnitIso X.presheaf X.ringCatSheaf.2))) ?_
  refine Eq.trans (congrArg
    (fun z =>
      (Stacks.SheafOfModules.sheafifyUnitIso X.presheaf X.ringCatSheaf.2).hom.val.app (op V) z)
    (((congrArg
        (fun z => (Stacks.ProjBundleInverseBaseChange.negOneMulIso' X.presheaf
          X.ringCatSheaf.2 L).hom.val.app (op V) z)
        (PresheafOfModules.hom_congr_apply
          (congrArg SheafOfModules.Hom.val
            (congrArg Iso.inv
              (tensorObjIso_eq_tensorIso L (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)))))
          (op V)
          (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op V) L
            (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) a b))).trans
      (Stacks.ProjBundleInverseBaseChange.negOneMulIso'_hom_tensorSectionsAt X.presheaf
        X.ringCatSheaf.2 L (op V) a b)).trans
      (Stacks.ProjBundleInverseBaseChange.negOneMulIso_hom_tensorSectionsAt X.presheaf
        X.ringCatSheaf.2 L (op V) b a).symm)) ?_
  exact (sectionMulNegOne_eq_negOneMulIso_tensorIso L V a b).symm

/-- **The crossing from `Stacks.SheafOfModules.Invertible.sectionMulNegOne` to
`Stacks.SheafOfModules.tensorPairing` against
`Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'`**: the pairing
`Stacks.SheafOfModules.tensorPairing` of `a` and `b` against `negOneMulPairingIso'` is
`Stacks.SheafOfModules.Invertible.sectionMulNegOne` of `a` and `b`. -/
theorem tensorPairing_negOneMulPairingIso' (V : X.Opens) (a : Γ(L, V))
    (b : Γ(tensorPower X.presheaf X.ringCatSheaf.2 L (-1), V)) :
    Stacks.SheafOfModules.tensorPairing
        (Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'
          (X := X.toRingedSpace) L) V a b =
      sectionMulNegOne X.presheaf X.ringCatSheaf.2 L (op V) a b :=
  (Stacks.SheafOfModules.tensorPairing_eq_hom_tensorSectionsAt
      (Y := X.toRingedSpace)
      (Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'
        (X := X.toRingedSpace) L) V a b).trans
    (negOneMulPairingIso'_hom_tensorSectionsAt L V a b)

/-- `Stacks.ProjectiveBundleConormal.sectionMulNegOne_restrictInverseTwistIso_inv_one` in the
`Stacks.SheafOfModules.tensorPairing` spelling, which is what `hpair` asks for. The unit section
of the structure sheaf read as a section of the monoidal unit is `1` by definition, so no
comparison appears. -/
theorem tensorPairing_restrictInverseTwistIso_inv_one (U : X.Opens)
    (τ : (Scheme.Modules.restrictFunctor U.ι).obj L ≅ 𝟙_ (↑U : Scheme.{u}).Modules)
    (V : (↑U : Scheme.{u}).Opens) (h : V ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V)) :
    Stacks.SheafOfModules.tensorPairing
        (Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'
          (X := X.toRingedSpace) L) (U.ι ''ᵁ V)
        (τ.inv.val.app (op V) (1 : Γ((↑U : Scheme.{u}), V)))
        ((restrictInverseTwistIso L U τ).inv.val.app (op V)
          (1 : Γ((↑U : Scheme.{u}), V))) =
      Stacks.SheafOfModules.unitSection X.toRingedSpace (U.ι ''ᵁ V) :=
  (tensorPairing_negOneMulPairingIso' L (U.ι ''ᵁ V) _ _).trans
    (sectionMulNegOne_restrictInverseTwistIso_inv_one L U τ V h)

end Inverse

/-! ### `hpair` on a chart -/

section Pair

variable {E : X.Modules} (Q : Stacks.Divisors.InvertibleQuotient X E)

/-- **The chart's own trivialisation carries the unit section to the frame section.** The
trivialisation `Stacks.ProjectiveBundleConormal.chartTrivialisation` is
`Stacks.ProjectiveBundleConormal.restrictIsoUnitOfSpanEqTop` at the spanning section `q s`, so
this is `restrictIsoUnitOfSpanEqTop_inv_val_app_one` with
`Stacks.ProjectiveBundleConormal.span_singleton_app_eq_top_of_chartLinearForm_eq_one` for the span
hypothesis — the frame condition and nothing more. -/
theorem chartTrivialisation_inv_val_app_one {W : X.Opens} (hW : IsAffineOpen W)
    (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) (s : Γ(E, W))
    (hs : chartLinearForm Q W eL s = 1)
    (V : (↑W : Scheme.{u}).Opens) (h : W.ι ''ᵁ V ≤ W) :
    (chartTrivialisation Q hW eL s hs).inv.val.app (op V)
        (1 : Γ((↑W : Scheme.{u}), V)) =
      Q.L.val.map (homOfLE h).op (Q.q.app W s) :=
  restrictIsoUnitOfSpanEqTop_inv_val_app_one Q.L W hW (Q.q.app W s)
    (span_singleton_app_eq_top_of_chartLinearForm_eq_one Q W eL hs) V h

/-- **`hpair`, discharged on a chart.** For the chart data that
`Stacks.ProjectiveBundleConormal.exists_affine_open_chartData` returns — an affine open `W`, a
frame `eL`, a section `s` of `ℰ` with `chartLinearForm Q W eL s = 1`, and the trivialisation
`Stacks.ProjectiveBundleConormal.chartTrivialisation` that data induces — the frame section `q s`
and the generator `w` of `𝓛^{⊗ -1}` that the induced trivialisation of the inverse twist names
pair to `1`.

The generator `w` lives over `W.ι ''ᵁ ⊤`, which is `W` up to
`AlgebraicGeometry.Scheme.Opens.ι_image_top`; the inequalities `hUW` and `hWU` between `W` and
`W.ι ''ᵁ ⊤` are parameters, and `w` is specified by `hw`. -/
theorem tensorPairing_chartTrivialisation_eq_unitSection {W : X.Opens} (hW : IsAffineOpen W)
    (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) (s : Γ(E, W))
    (hs : chartLinearForm Q W eL s = 1)
    (hUW : W ≤ W.ι ''ᵁ (⊤ : (↑W : Scheme.{u}).Opens))
    (hWU : W.ι ''ᵁ (⊤ : (↑W : Scheme.{u}).Opens) ≤ W)
    (h : (⊤ : (↑W : Scheme.{u}).Opens) ≤
      W.ι ⁻¹ᵁ (W.ι ''ᵁ (⊤ : (↑W : Scheme.{u}).Opens)))
    (w : Γ(tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1), W))
    (hw : w = (show X.Modules from
          tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)).val.map (homOfLE hUW).op
        ((restrictInverseTwistIso Q.L W (chartTrivialisation Q hW eL s hs)).inv.val.app
          (op (⊤ : (↑W : Scheme.{u}).Opens))
          (1 : Γ((↑W : Scheme.{u}), (⊤ : (↑W : Scheme.{u}).Opens))))) :
    Stacks.SheafOfModules.tensorPairing
        (Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'
          (X := X.toRingedSpace) Q.L) W (Q.q.app W s) w =
      Stacks.SheafOfModules.unitSection X.toRingedSpace W := by
  have htop := tensorPairing_restrictInverseTwistIso_inv_one Q.L W
    (chartTrivialisation Q hW eL s hs) (⊤ : (↑W : Scheme.{u}).Opens) h
  have hres := Stacks.SheafOfModules.tensorPairing_res
    (X := X.toRingedSpace)
    (Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso' (X := X.toRingedSpace) Q.L)
    (homOfLE hUW)
    ((chartTrivialisation Q hW eL s hs).inv.val.app
      (op (⊤ : (↑W : Scheme.{u}).Opens))
      (1 : Γ((↑W : Scheme.{u}), (⊤ : (↑W : Scheme.{u}).Opens))))
    ((restrictInverseTwistIso Q.L W (chartTrivialisation Q hW eL s hs)).inv.val.app
      (op (⊤ : (↑W : Scheme.{u}).Opens))
      (1 : Γ((↑W : Scheme.{u}), (⊤ : (↑W : Scheme.{u}).Opens))))
  have hA : Q.L.val.map (homOfLE hUW).op
      ((chartTrivialisation Q hW eL s hs).inv.val.app
        (op (⊤ : (↑W : Scheme.{u}).Opens))
        (1 : Γ((↑W : Scheme.{u}), (⊤ : (↑W : Scheme.{u}).Opens)))) = Q.q.app W s :=
    (congrArg (fun z : Γ(Q.L, W.ι ''ᵁ (⊤ : (↑W : Scheme.{u}).Opens)) =>
          Q.L.val.map (homOfLE hUW).op z)
        (chartTrivialisation_inv_val_app_one Q hW eL s hs
          (⊤ : (↑W : Scheme.{u}).Opens) hWU)).trans
      ((Stacks.Tag08S2Locality.map_map Q.L (homOfLE hUW) (homOfLE hWU) (Q.q.app W s)).trans
        (Stacks.Tag08S2Locality.map_self Q.L _ (Q.q.app W s)))
  refine Eq.trans (congrArg (fun z : Γ(Q.L, W) =>
      Stacks.SheafOfModules.tensorPairing
        (Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'
          (X := X.toRingedSpace) Q.L) W z w) hA.symm) ?_
  refine Eq.trans (congrArg (fun z : Γ(tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1), W) =>
      Stacks.SheafOfModules.tensorPairing
        (Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'
          (X := X.toRingedSpace) Q.L) W
        (Q.L.val.map (homOfLE hUW).op
          ((chartTrivialisation Q hW eL s hs).inv.val.app
            (op (⊤ : (↑W : Scheme.{u}).Opens))
            (1 : Γ((↑W : Scheme.{u}), (⊤ : (↑W : Scheme.{u}).Opens))))) z) hw) ?_
  refine Eq.trans hres.symm ?_
  refine Eq.trans (congrArg
    (fun z : (_root_.SheafOfModules.unit
          (_root_.structureSheafRing X.toRingedSpace)).val.obj
        (op (W.ι ''ᵁ (⊤ : (↑W : Scheme.{u}).Opens))) =>
      (_root_.SheafOfModules.unit
        (_root_.structureSheafRing X.toRingedSpace)).val.map (homOfLE hUW).op z) htop) ?_
  exact map_one ((_root_.structureSheafRing X.toRingedSpace).obj.map (homOfLE hUW).op).hom

end Pair

end Stacks.ProjectiveBundleConormal

end
