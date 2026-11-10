module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OperatorOrderPullbackOpenImmersion
public import StacksFrontier.LinearAlgebra.TensorProduct.PushoutAction
public import StacksFrontier.RingTheory.DifferentialOperator.BaseChange

/-!
# Base change of a differential operator along an affine chart of a fibre product

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, let `F`, `F'` be quasi-coherent
`𝒪_X`-modules, let `G` be a quasi-coherent `𝒪_Y`-module and let `D : F ⟶ F'` be a differential
operator of order at most `k` on `X/S`. On an affine chart
`Spec (A ⊗_R B) ⟶ X ×_S Y` of the fibre product, with `R = Γ(S, W)`, `A = Γ(X, U)`,
`B = Γ(Y, V)`, the sections of the box product `F ⊠ G` are the tensor product over `R` of the
sections of `F` on `Spec A` and of `G` on `Spec B`, and the differential operators of order at
most `k` on `X ×_S Y / Y` over the opens of the chart are the differential operators of order at
most `k` relative to `B ⟶ A ⊗_R B` on those sections. So the base change `D ⊗ id` of Tag 0G37
transports to a differential operator of order at most `k` on `X ×_S Y / Y` over the opens of the
chart, and it is the only one carrying the section corresponding to `s ⊗ t` to the one
corresponding to `D s ⊗ t`. This is a statement about one chart: the chart-wise operators are not
glued here.

## Main definitions

* `Stacks.DifferentialOperator.conj` and `Stacks.DifferentialOperator.orderEquivConj`: an
  operator conjugated by two linear equivalences over the ring of scalars of the order predicate,
  and the resulting bijection of the operators of order at most `k`.
* `Stacks.FibreProductAffineChart.Chart.leftDiffOpEquiv`: the differential operators of order at
  most `k` on `X/S` over the opens of the first factor of a chart, identified with the
  differential operators of order at most `k` relative to `R ⟶ A` on the sections of the modules
  on `Spec A`.
* `Stacks.FibreProductAffineChart.Chart.boxDiffOpEquiv`: the differential operators of order at
  most `k` on `X ×_S Y / Y` over the opens of a chart, identified with the differential operators
  of order at most `k` relative to `B ⟶ A ⊗_R B` on the sections of the inverse images of the
  modules on the chart. This is the inverse-image spelling of
  `Stacks.FibreProductAffineChart.Chart.diffOpEquiv`.
* `Stacks.FibreProductAffineChart.Chart.boxSectionsEquiv`: the sections of `F ⊠ G` on a chart,
  identified `A ⊗_R B`-linearly with `Γ(Spec A, F) ⊗_R Γ(Spec B, G)`.
* `Stacks.FibreProductAffineChart.Chart.boxDiffOpTensorEquiv`: the two combined, so that a
  differential operator of order at most `k` on `X ×_S Y / Y` over the opens of a chart is a
  differential operator of order at most `k` relative to `B ⟶ A ⊗_R B` on
  `Γ(Spec A, F) ⊗_R Γ(Spec B, G)`.

## Main results

* `Stacks.DifferentialOperator.order_conj`: conjugating by linear equivalences over the ring of
  scalars does not change the order of a differential operator.
* `Stacks.FibreProductAffineChart.Chart.existsUnique_boxDiffOp`: **the affine-chart base change
  of a differential operator.** There is a unique differential operator of order at most `k` on
  `X ×_S Y / Y`, over the opens of a chart, carrying the section of `F ⊠ G` corresponding to
  `s ⊗ t` to the section of `F' ⊠ G` corresponding to `D s ⊗ t`.

## Implementation notes

The chart identification is taken in the inverse-image spelling, so that the modules of sections
are the ones `Stacks.FibreProductAffineChart.chartExternalTensorSectionsIso` describes; the
restriction spelling of `Stacks.FibreProductAffineChart.Chart.diffOpEquiv` would have to be
bridged by `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` at every use. Both are
built the same way: the comparison across the open immersion of the chart, then Tag 0G44 on the
affine chart, the relative base being shrunk from `Y` to the affine open `Spec B` by
`AlgebraicGeometry.isGlobalDiffOpOfOrder_comp_isOpenImmersion_iff`.

`Stacks.FibreProductAffineChart.Chart.boxSectionsEquiv` upgrades
`Stacks.FibreProductAffineChart.chartExternalTensorSectionsBaseIso` from `R`-linear to
`A ⊗_R B`-linear, which is what the order predicate needs: it is the same underlying map, with
`Stacks.TensorProductPushout.cancelBaseChangePushout` in place of the `R`-linear cancellation.
None of the scalar structures involved is a global Mathlib instance, and they are installed with
`attribute [local instance]`.

The scalar actions on the modules of sections are named `def`s rather than `letI`s inside each
statement, so that the same actions are in scope in a statement and in its proof.

## References

* [Stacks Project, Tag 0G37](https://stacks.math.columbia.edu/tag/0G37)
* [Stacks Project, Tag 0G44](https://stacks.math.columbia.edu/tag/0G44)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct TopologicalSpace
open CommRingCat

universe u

namespace Stacks.DifferentialOperator

variable {R S M M' N N' : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup M'] [Module R M'] [Module S M'] [IsScalarTower R S M']
  [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommGroup N'] [Module R N'] [Module S N'] [IsScalarTower R S N']

/-- An `R`-linear operator `D : M → M'` conjugated by `S`-linear equivalences of its source and
target: the operator `n ↦ e' (D (e⁻¹ n))`. -/
def conj (e : M ≃ₗ[S] N) (e' : M' ≃ₗ[S] N') (D : M →ₗ[R] M') : N →ₗ[R] N' :=
  e'.toLinearMap.restrictScalars R ∘ₗ D ∘ₗ e.symm.toLinearMap.restrictScalars R

/-- The conjugated operator `conj e e' D` sends `n` to `e' (D (e⁻¹ n))`. -/
@[simp]
theorem conj_apply (e : M ≃ₗ[S] N) (e' : M' ≃ₗ[S] N') (D : M →ₗ[R] M') (n : N) :
    conj e e' D n = e' (D (e.symm n)) := rfl

/-- **Conjugating by linear equivalences over the ring of scalars preserves the order of a
differential operator.** -/
theorem order_conj (e : M ≃ₗ[S] N) (e' : M' ≃ₗ[S] N') :
    ∀ (k : ℕ) (D : M →ₗ[R] M'), D.IsDifferentialOperatorOfOrderLE S k →
      (conj e e' D).IsDifferentialOperatorOfOrderLE S k := by
  intro k
  induction k with
  | zero =>
    intro D hD g n
    change e' (D (e.symm (g • n))) = g • e' (D (e.symm n))
    rw [map_smul, hD g, map_smul]
  | succ k ih =>
    intro D hD g
    have key : conj e e' D ∘ₗ Algebra.lsmul R R N g - Algebra.lsmul R R N' g ∘ₗ conj e e' D
        = conj e e' (D ∘ₗ Algebra.lsmul R R M g - Algebra.lsmul R R M' g ∘ₗ D) :=
      LinearMap.ext fun n => by
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, conj_apply, Algebra.lsmul_coe,
          map_smul, map_sub]
    rw [key]
    exact ih _ (hD g)

/-- Conjugating an operator by two linear equivalences is a bijection on operators. -/
def conjEquiv (e : M ≃ₗ[S] N) (e' : M' ≃ₗ[S] N') : (M →ₗ[R] M') ≃ (N →ₗ[R] N') where
  toFun := conj e e'
  invFun := conj e.symm e'.symm
  left_inv D := LinearMap.ext fun m => by
    simp only [conj_apply, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]
  right_inv D := LinearMap.ext fun n => by
    simp only [conj_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]

/-- The differential operators of order at most `k` between two modules are those between any two
pairs of modules linearly equivalent to them over the ring of scalars. -/
def orderEquivConj (e : M ≃ₗ[S] N) (e' : M' ≃ₗ[S] N') (k : ℕ) :
    {D : M →ₗ[R] M' // D.IsDifferentialOperatorOfOrderLE S k} ≃
      {D : N →ₗ[R] N' // D.IsDifferentialOperatorOfOrderLE S k} :=
  Equiv.subtypeEquiv (conjEquiv e e') fun D =>
    ⟨order_conj e e' k D,
      fun h => (conjEquiv e e').left_inv D ▸ order_conj e.symm e'.symm k _ h⟩

end Stacks.DifferentialOperator

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback

namespace Stacks.FibreProductAffineChart

open _root_.AlgebraicGeometry RingHomClass

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A global operator has the same order relative to a morphism that factors through an open
immersion as relative to the first factor of the factorisation. -/
private theorem isGlobalDiffOpOfOrder_iff_of_eq_comp {W Z Y : Scheme.{u}} {f : W ⟶ Y}
    {M M' : W.Modules} (g : W ⟶ Z) (h : Z ⟶ Y) [IsOpenImmersion h] (e : f = g ≫ h) (k : ℕ)
    (E : DiffOp.GlobalOp M M') :
    DiffOp.IsGlobalDiffOpOfOrder f.relativeStructureSheafMap k E ↔
      DiffOp.IsGlobalDiffOpOfOrder g.relativeStructureSheafMap k E :=
  e ▸ isGlobalDiffOpOfOrder_comp_isOpenImmersion_iff g h k E

namespace Chart

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S} (c : Chart a b)

/-! ### Differential operators on the first factor of a chart -/

section Left

variable [Algebra Γ(S, c.base) Γ(X, c.left)]
  (hl : ofHom (algebraMap Γ(S, c.base) Γ(X, c.left)) = c.leftHom)
variable (F : X.Modules)

/-- The action of `Γ(X, U)` on the sections of the inverse image of an `𝒪_X`-module on the first
factor `Spec Γ(X, U)` of a chart. -/
@[instance_reducible]
noncomputable def leftModuleAlg :
    Module Γ(X, c.left) Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F, ⊤) :=
  Module.compHom _ (Scheme.ΓSpecIso (.of Γ(X, c.left))).inv.hom

attribute [local instance] leftModuleAlg

/-- The action of `Γ(S, W)` on the sections of the inverse image of an `𝒪_X`-module on the first
factor `Spec Γ(X, U)` of a chart. -/
@[instance_reducible]
noncomputable def leftModuleBase :
    Module Γ(S, c.base) Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F, ⊤) :=
  Module.compHom _ (algebraMap Γ(S, c.base) Γ(X, c.left))

attribute [local instance] leftModuleBase

/-- The action of `Γ(S, W)` on the sections over the first factor of a chart is the restriction of
the action of `Γ(X, U)`. -/
theorem leftTower :
    IsScalarTower Γ(S, c.base) Γ(X, c.left)
      Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F, ⊤) :=
  IsScalarTower.of_compHom _ _ _

attribute [local instance] leftTower

variable (F' : X.Modules) [F.IsQuasicoherent] (k : ℕ)

include hl in
/-- The structure morphism of the first factor of a chart is `Spec` of the chart's first
structure map, followed by the open immersion of the chart's base. -/
theorem fromSpecLeft_comp_eq :
    c.fromSpecLeft ≫ a =
      Spec.map (ofHom (algebraMap Γ(S, c.base) Γ(X, c.left))) ≫ c.fromSpecBase := by
  rw [hl]; exact c.specMap_leftHom_fromSpec.symm

omit [F.IsQuasicoherent] in
include hl in
/-- The order of an operator on the inverse images along the first factor of a chart may be read
relative to `Γ(S, W) ⟶ Γ(X, U)` instead of relative to `S`. -/
theorem leftOrder_iff
    (E : DiffOp.GlobalOp ((Scheme.Modules.pullback c.fromSpecLeft).obj F)
      ((Scheme.Modules.pullback c.fromSpecLeft).obj F')) :
    DiffOp.IsGlobalDiffOpOfOrder (c.fromSpecLeft ≫ a).relativeStructureSheafMap k E ↔
      DiffOp.IsGlobalDiffOpOfOrder
        (Spec.map (ofHom (algebraMap Γ(S, c.base) Γ(X, c.left)))).relativeStructureSheafMap k E :=
  have : IsOpenImmersion c.fromSpecBase := c.isAffineOpen_base.isOpenImmersion_fromSpec
  isGlobalDiffOpOfOrder_iff_of_eq_comp _ c.fromSpecBase (c.fromSpecLeft_comp_eq hl) k E

include hl in
/-- **Differential operators on the first factor of an affine chart.** The differential operators
of order at most `k` on `X/S` between two modules on `X`, defined over the opens contained in the
first factor of a chart, are the differential operators of order at most `k` relative to
`Γ(S, W) ⟶ Γ(X, U)` between the two modules of sections on `Spec Γ(X, U)`. -/
noncomputable def leftDiffOpEquiv :
    {D : DiffOp.RawOp F F' c.fromSpecLeft.opensRange //
        DiffOp.IsDiffOpOfOrder a.relativeStructureSheafMap k D} ≃
      {D : Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F, ⊤) →ₗ[Γ(S, c.base)]
          Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F', ⊤) //
        D.IsDifferentialOperatorOfOrderLE Γ(X, c.left) k} :=
  (diffOpEquivGlobalDiffOpPullback c.fromSpecLeft a F F' k).trans
    ((Equiv.subtypeEquivRight (c.leftOrder_iff hl F F' k)).trans
      (AffineDiffOp.globalDiffOpEquiv (R := Γ(S, c.base))
        ((Scheme.Modules.pullback c.fromSpecLeft).obj F)
        ((Scheme.Modules.pullback c.fromSpecLeft).obj F') k).1)

include hl in
/-- The operator on the sections over the first factor of a chart attached to a differential
operator on `X/S` is the operator's action on those sections, read through the comparison of the
restriction with the inverse image. -/
theorem leftDiffOpEquiv_apply
    (D : {D : DiffOp.RawOp F F' c.fromSpecLeft.opensRange //
        DiffOp.IsDiffOpOfOrder a.relativeStructureSheafMap k D})
    (x : Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F, ⊤)) :
    (leftDiffOpEquiv c hl F F' k D).1 x =
      Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorIsoPullback c.fromSpecLeft).app F').hom ⊤
        (D.1 (AlgebraicGeometry.imageOver c.fromSpecLeft ⊤)
          (Scheme.Modules.Hom.app
            ((Scheme.Modules.restrictFunctorIsoPullback c.fromSpecLeft).app F).inv ⊤ x)) :=
  ((AffineDiffOp.globalDiffOpEquiv (R := Γ(S, c.base))
      ((Scheme.Modules.pullback c.fromSpecLeft).obj F)
      ((Scheme.Modules.pullback c.fromSpecLeft).obj F') k).2
    (Equiv.subtypeEquivRight (c.leftOrder_iff hl F F' k)
      (diffOpEquivGlobalDiffOpPullback c.fromSpecLeft a F F' k D)) x).trans
    (diffOpEquivGlobalDiffOpPullback_coe_apply c.fromSpecLeft a F F' k D ⊤ x)

end Left

/-! ### Differential operators on the second factor of a chart -/

section Right

variable [Algebra Γ(S, c.base) Γ(Y, c.right)] (G : Y.Modules)

/-- The action of `Γ(Y, V)` on the sections of the inverse image of an `𝒪_Y`-module on the second
factor `Spec Γ(Y, V)` of a chart. -/
@[instance_reducible]
noncomputable def rightModuleAlg :
    Module Γ(Y, c.right) Γ((Scheme.Modules.pullback c.fromSpecRight).obj G, ⊤) :=
  Module.compHom _ (Scheme.ΓSpecIso (.of Γ(Y, c.right))).inv.hom

attribute [local instance] rightModuleAlg

/-- The action of `Γ(S, W)` on the sections of the inverse image of an `𝒪_Y`-module on the second
factor `Spec Γ(Y, V)` of a chart. -/
@[instance_reducible]
noncomputable def rightModuleBase :
    Module Γ(S, c.base) Γ((Scheme.Modules.pullback c.fromSpecRight).obj G, ⊤) :=
  Module.compHom _ (algebraMap Γ(S, c.base) Γ(Y, c.right))

attribute [local instance] rightModuleBase

/-- The action of `Γ(S, W)` on the sections over the second factor of a chart is the restriction
of the action of `Γ(Y, V)`. -/
theorem rightTower :
    IsScalarTower Γ(S, c.base) Γ(Y, c.right)
      Γ((Scheme.Modules.pullback c.fromSpecRight).obj G, ⊤) :=
  IsScalarTower.of_compHom _ _ _

attribute [local instance] rightModuleAlg rightModuleBase rightTower

variable (hr : ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right)) = c.rightHom)

include hr in
/-- The structure morphism of the second factor of a chart is `Spec` of the chart's second
structure map, followed by the open immersion of the chart's base. -/
theorem fromSpecRight_comp_eq :
    c.fromSpecRight ≫ b =
      Spec.map (ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right))) ≫ c.fromSpecBase := by
  rw [hr]; exact c.specMap_rightHom_fromSpec.symm

end Right

/-! ### Differential operators on a chart, in the inverse-image spelling -/

section Box

attribute [local instance] leftModuleAlg leftModuleBase leftTower
attribute [local instance] rightModuleAlg rightModuleBase rightTower
attribute [local instance] Stacks.TensorProductPushout.rightModule
  Stacks.TensorProductPushout.rightModule_isScalarTower
  Stacks.TensorProductPushout.smulCommClass_right
  Stacks.TensorProductPushout.pushoutModule
  Stacks.TensorProductPushout.pushoutModule_isScalarTower

variable [Algebra Γ(S, c.base) Γ(X, c.left)] [Algebra Γ(S, c.base) Γ(Y, c.right)]
  (hl : ofHom (algebraMap Γ(S, c.base) Γ(X, c.left)) = c.leftHom)
  (hr : ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right)) = c.rightHom)

/-- The affine chart attached to a chart of a fibre product, as
`Stacks.FibreProductAffineChart.affineChart` of the chart's three structure maps. -/
noncomputable abbrev chartAffine :
    Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))) ⟶ pullback a b :=
  affineChart a b Γ(S, c.base) Γ(X, c.left) Γ(Y, c.right)
    c.fromSpecLeft c.fromSpecRight c.fromSpecBase
    (c.fromSpecLeft_comp_eq hl).symm (c.fromSpecRight_comp_eq hr).symm

/-- A chart, read through `Stacks.FibreProductAffineChart.Chart.specIso` as the spectrum of a
tensor product, is its affine chart. -/
theorem specIso_inv_ι_eq : (c.specIso hl hr).inv ≫ c.ι = c.chartAffine hl hr :=
  specIso_inv_ι c hl hr

/-- The action of `Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V)` on the sections over a chart of the inverse image
of a module on the fibre product. -/
@[instance_reducible]
noncomputable def boxModuleAlg (M : (pullback a b).Modules) :
    Module (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))
      Γ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj M, ⊤) :=
  Module.compHom _
    (Scheme.ΓSpecIso (.of (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))).inv.hom

attribute [local instance] boxModuleAlg

/-- The action of `Γ(Y, V)` on the sections over a chart of the inverse image of a module on the
fibre product. -/
@[instance_reducible]
noncomputable def boxModuleBase (M : (pullback a b).Modules) :
    Module Γ(Y, c.right)
      Γ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj M, ⊤) :=
  Module.compHom _
    (algebraMap Γ(Y, c.right) (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))

attribute [local instance] boxModuleBase

/-- The action of `Γ(Y, V)` on the sections over a chart is the restriction of the action of
`Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V)`. -/
theorem boxTower (M : (pullback a b).Modules) :
    IsScalarTower Γ(Y, c.right) (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))
      Γ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj M, ⊤) :=
  IsScalarTower.of_compHom _ _ _

attribute [local instance] boxTower

/-- The order of an operator on the inverse images along a chart may be read relative to
`Γ(Y, V) ⟶ Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V)` instead of relative to `Y`. -/
theorem boxOrder_iff (M M' : (pullback a b).Modules) (k : ℕ)
    (E : DiffOp.GlobalOp ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj M)
      ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj M')) :
    DiffOp.IsGlobalDiffOpOfOrder
        (((c.specIso hl hr).inv ≫ c.ι) ≫ pullback.snd a b).relativeStructureSheafMap k E ↔
      DiffOp.IsGlobalDiffOpOfOrder
        (Spec.map (ofHom (algebraMap Γ(Y, c.right)
          (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))))).relativeStructureSheafMap k E :=
  have : IsOpenImmersion c.fromSpecRight := c.isAffineOpen_right.isOpenImmersion_fromSpec
  isGlobalDiffOpOfOrder_iff_of_eq_comp _ c.fromSpecRight (specIso_inv_ι_comp_snd c hl hr) k E

/-- **Differential operators on an affine chart of a fibre product, in the inverse-image
spelling.** The differential operators of order at most `k` on `X ×_S Y / Y` between two modules
on `X ×_S Y`, defined over the opens contained in a chart, are the differential operators of order
at most `k` relative to `Γ(Y, V) ⟶ Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V)` between the two modules of
sections of the inverse images on the chart. -/
noncomputable def boxDiffOpEquiv (M M' : (pullback a b).Modules) [M.IsQuasicoherent] (k : ℕ) :
    {D : DiffOp.RawOp M M' c.ι.opensRange //
        DiffOp.IsDiffOpOfOrder (pullback.snd a b).relativeStructureSheafMap k D} ≃
      {D : Γ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj M, ⊤) →ₗ[Γ(Y, c.right)]
          Γ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj M', ⊤) //
        D.IsDifferentialOperatorOfOrderLE
          (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)) k} :=
  ((Equiv.subtypeEquiv
        (DiffOp.RawOp.congrBase
          (Scheme.Hom.opensRange_comp_of_isIso (c.specIso hl hr).inv c.ι).symm)
        fun D ↦ (DiffOp.RawOp.isDiffOpOfOrder_congrBase _ k _ D).symm).trans
      (diffOpEquivGlobalDiffOpPullback ((c.specIso hl hr).inv ≫ c.ι)
        (pullback.snd a b) M M' k)).trans
    ((Equiv.subtypeEquivRight (c.boxOrder_iff hl hr M M' k)).trans
      (AffineDiffOp.globalDiffOpEquiv (R := Γ(Y, c.right))
        ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj M)
        ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj M') k).1)

/-! ### The sections of a box product on a chart, over the ring of the chart -/

variable (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]

/-- The sections of `F ⊠ G` on a chart, identified with the tensor product over
`Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V)` of the two base-changed modules of sections. This is
`Stacks.FibreProductAffineChart.chartExternalTensorSectionsIso` read at the chart morphism in its
`Stacks.FibreProductAffineChart.Chart.specIso` form. -/
noncomputable def boxSectionsIso :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj
        (externalTensorProduct a b F G)) ≅
      MonoidalCategory.tensorObj
        ((ModuleCat.extendScalars
          (chartInclLeft Γ(S, c.base) Γ(X, c.left) Γ(Y, c.right)).hom).obj
          (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback c.fromSpecLeft).obj F)))
        ((ModuleCat.extendScalars
          (chartInclRight Γ(S, c.base) Γ(X, c.left) Γ(Y, c.right)).hom).obj
          (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback c.fromSpecRight).obj G))) :=
  moduleSpecΓFunctor.mapIso
      ((Scheme.Modules.pullbackCongr (c.specIso_inv_ι_eq hl hr)).app
        (externalTensorProduct a b F G)) ≪≫
    chartExternalTensorSectionsIso a b Γ(S, c.base) Γ(X, c.left) Γ(Y, c.right)
      c.fromSpecLeft c.fromSpecRight c.fromSpecBase
      (c.fromSpecLeft_comp_eq hl).symm (c.fromSpecRight_comp_eq hr).symm F G

/-- **The sections of a box product on a chart.** The module of sections of `F ⊠ G` on a chart is
the tensor product over `Γ(S, W)` of the sections of `F` on `Spec Γ(X, U)` and of `G` on
`Spec Γ(Y, V)`, linearly over `Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V)`, which acts on the tensor product by
`(f ⊗ g) • (s ⊗ t) = (f • s) ⊗ (g • t)`. -/
@[stacks 0G46 "the OBJECT half of the affine description of the remark: on an affine chart of \
`X ×_S Y`, and so in particular for `X = Spec A`, `Y = Spec B`, `S = Spec R` and the chart whose \
three opens are everything, the module of sections of `F ⊠ G` is `M ⊗_R N`, linearly over the \
ring `A ⊗_R B` of the chart. NOT the morphism half `(D, D') ↦ D ⊗ D'`, which is \
`Chart.boxHom_boxSectionOfTensor`"]
noncomputable def boxSectionsEquiv :
    Γ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj
        (externalTensorProduct a b F G), ⊤)
      ≃ₗ[Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)]
      (Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F, ⊤) ⊗[Γ(S, c.base)]
        Γ((Scheme.Modules.pullback c.fromSpecRight).obj G, ⊤)) :=
  (((c.boxSectionsIso hl hr F G) ≪≫
      MonoidalCategory.tensorIso
        (Stacks.TensorProductPushout.extendScalarsObjIso
          (S := Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))
          (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback c.fromSpecLeft).obj F)))
        (Stacks.TensorProductPushout.extendScalarsObjIso
          (S := Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))
          (moduleSpecΓFunctor.obj
            ((Scheme.Modules.pullback c.fromSpecRight).obj G)))).toLinearEquiv).trans
    (Stacks.TensorProductPushout.cancelBaseChangePushout Γ(S, c.base) Γ(X, c.left) Γ(Y, c.right)
      Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F, ⊤)
      Γ((Scheme.Modules.pullback c.fromSpecRight).obj G, ⊤))

/-! ### The base change of a differential operator on a chart -/

/-- The differential operators of order at most `k` on `X ×_S Y / Y` over the opens of a chart,
identified with the differential operators of order at most `k` relative to
`Γ(Y, V) ⟶ Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V)` on `Γ(Spec Γ(X, U), F) ⊗_{Γ(S, W)} Γ(Spec Γ(Y, V), G)`. -/
noncomputable def boxDiffOpTensorEquiv (F' : X.Modules) [F'.IsQuasicoherent] (k : ℕ) :
    {E : DiffOp.RawOp (externalTensorProduct a b F G) (externalTensorProduct a b F' G)
        c.ι.opensRange //
      DiffOp.IsDiffOpOfOrder (pullback.snd a b).relativeStructureSheafMap k E} ≃
      {D : (Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F, ⊤) ⊗[Γ(S, c.base)]
            Γ((Scheme.Modules.pullback c.fromSpecRight).obj G, ⊤)) →ₗ[Γ(Y, c.right)]
          (Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F', ⊤) ⊗[Γ(S, c.base)]
            Γ((Scheme.Modules.pullback c.fromSpecRight).obj G, ⊤)) //
        D.IsDifferentialOperatorOfOrderLE (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)) k} :=
  (c.boxDiffOpEquiv hl hr (externalTensorProduct a b F G)
      (externalTensorProduct a b F' G) k).trans
    (Stacks.DifferentialOperator.orderEquivConj (c.boxSectionsEquiv hl hr F G)
      (c.boxSectionsEquiv hl hr F' G) k)

/-- **The affine-chart base change of a differential operator (Tag 0G45 on a chart).** Let
`D : F ⟶ F'` be a differential operator of order at most `k` on `X/S` between quasi-coherent
modules and let `G` be a quasi-coherent `𝒪_Y`-module. Over the opens of an affine chart of
`X ×_S Y` there is exactly one differential operator of order at most `k` on `X ×_S Y / Y` from
`F ⊠ G` to `F' ⊠ G` which, read through the identification of the sections of a box product on the
chart with `Γ(Spec Γ(X, U), F) ⊗_{Γ(S, W)} Γ(Spec Γ(Y, V), G)`, carries `s ⊗ t` to `D s ⊗ t`. -/
@[stacks 0G45 "the affine-chart step of the construction of `D'`: over ONE affine chart of \
`X ×_S Y` this gives the existence of `D'`, its order bound, its characterisation on pure \
tensors and its uniqueness, all read through the identification of the sections of `F ⊠ G` on \
the chart with `Γ(Spec A, F) ⊗_R Γ(Spec B, G)`. The global operator on `X ×_S Y` is NOT \
constructed: the chart-wise operators are not glued, and the characterisation is not expressed \
on the sections of `F ⊠ G` attached to a pair of local sections of `F` and of `G`"]
theorem existsUnique_boxDiffOp (F' : X.Modules) [F'.IsQuasicoherent] (k : ℕ)
    (D : DiffOp.GlobalOp F F')
    (hD : DiffOp.IsGlobalDiffOpOfOrder a.relativeStructureSheafMap k D) :
    ∃! E : {E : DiffOp.RawOp (externalTensorProduct a b F G) (externalTensorProduct a b F' G)
          c.ι.opensRange //
        DiffOp.IsDiffOpOfOrder (pullback.snd a b).relativeStructureSheafMap k E},
      ∀ (s : Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F, ⊤))
        (t : Γ((Scheme.Modules.pullback c.fromSpecRight).obj G, ⊤)),
        (c.boxDiffOpTensorEquiv hl hr F G F' k E).1 (s ⊗ₜ[Γ(S, c.base)] t) =
          (c.leftDiffOpEquiv hl F F' k
              ⟨D.restrict c.fromSpecLeft.opensRange, hD c.fromSpecLeft.opensRange⟩).1 s
            ⊗ₜ[Γ(S, c.base)] t := by
  obtain ⟨D₀, ⟨hD₀tmul, hD₀ord⟩, huniq⟩ :=
    LinearMap.IsDifferentialOperatorOfOrderLE.existsUnique_rTensor
      (B := ↑Γ(Y, c.right)) (N := Γ((Scheme.Modules.pullback c.fromSpecRight).obj G, ⊤))
      (c.leftDiffOpEquiv hl F F' k
        ⟨D.restrict c.fromSpecLeft.opensRange, hD c.fromSpecLeft.opensRange⟩).2
      (Stacks.TensorProductPushout.pushoutModule_algebraMap_apply ↑Γ(S, c.base) ↑Γ(X, c.left)
        ↑Γ(Y, c.right))
      (Stacks.TensorProductPushout.pushoutModule_smul_tmul_tmul ↑Γ(S, c.base) ↑Γ(X, c.left)
        ↑Γ(Y, c.right) _ _)
      (Stacks.TensorProductPushout.pushoutModule_smul_tmul_tmul ↑Γ(S, c.base) ↑Γ(X, c.left)
        ↑Γ(Y, c.right) _ _)
  refine ⟨(c.boxDiffOpTensorEquiv hl hr F G F' k).symm ⟨D₀, hD₀ord⟩, ?_, ?_⟩
  · intro s t
    rw [show ((c.boxDiffOpTensorEquiv hl hr F G F' k)
        ((c.boxDiffOpTensorEquiv hl hr F G F' k).symm ⟨D₀, hD₀ord⟩)).1 = D₀ from
      congrArg Subtype.val ((c.boxDiffOpTensorEquiv hl hr F G F' k).apply_symm_apply _)]
    exact hD₀tmul s t
  · intro E hE
    exact ((c.boxDiffOpTensorEquiv hl hr F G F' k).eq_symm_apply).2
      (Subtype.ext (huniq _ ⟨fun s t ↦ hE s t,
        (c.boxDiffOpTensorEquiv hl hr F G F' k E).2⟩))

end Box

end Chart

end Stacks.FibreProductAffineChart

end
