module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparison

/-!
# The comparison map of Stacks 0E5P as a mate

Let `f : X ⟶ Y` be a quasi-compact quasi-separated morphism of algebraic spaces, with the data
of `AlgebraicGeometry.Space.PullbackComparisonData`, and let `a` be a right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. For fixed `K`, the two-variable map
`Lf^*K ⊗^L a(L) ⟶ a(K ⊗^L L)` of Stacks 0E5P is, as a transformation in `L`, the mate for
`Rf_* ⊣ a` of the inverse projection formula `Rf_*(Lf^*K ⊗^L -) ⟶ K ⊗^L Rf_*(-)`. If that inverse
is in turn the mate, for tensor adjunctions `(Lf^*K' ⊗^L -) ⊣ (Lf^*K ⊗^L -)` and
`(K' ⊗^L -) ⊣ (K ⊗^L -)`, of the projection formula for some `K'`, the iterated mate is a
conjugate (`CategoryTheory.iterated_mateEquiv_conjugateEquiv`), and the comparison map is
invertible. This is the Yoneda argument of Stacks 0E5Q, `K'` being the dual of a perfect `K`.

## Main definitions

* `AlgebraicGeometry.Space.PullbackComparisonData.projectionFormulaTwoSquare`,
  `projectionFormulaInvTwoSquare`, `compareWithPullbackTensorTwoSquare`.

## Main results

* `AlgebraicGeometry.Space.PullbackComparisonData.compareWithPullbackTensorTwoSquare_eq_mateEquiv`.
* `AlgebraicGeometry.Space.PullbackComparisonData.isIso_compareWithPullbackTensor_of_mateEquiv`.

## References

* [Stacks Project, Tag 0E5Q](https://stacks.math.columbia.edu/tag/0E5Q)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.PullbackComparisonData

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  [HasSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedSite B S hS Y.1 Y.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS Y.1 Y.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (D : PullbackComparisonData B S hS f)

/-- The projection-formula map `K ⊗^L Rf_*E ⟶ Rf_*(Lf^*K ⊗^L E)`, natural in `E`, as a 2-square
`Rf_* ⋙ (K ⊗^L -) ⟶ (Lf^*K ⊗^L -) ⋙ Rf_*`. -/
def projectionFormulaTwoSquare (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    TwoSquare D.pushforward (D.tensorX.obj (D.pullback.obj K)) (D.tensorY.obj K)
      D.pushforward :=
  TwoSquare.mk _ _ _ _
    { app := fun E => D.projectionFormulaMap E K
      naturality := fun _ _ φ => D.projectionFormulaMap_naturality_right φ K }

/-- The component at `E` of `projectionFormulaTwoSquare K` is `projectionFormulaMap E K`. -/
@[simp]
theorem projectionFormulaTwoSquare_natTrans_app
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    (D.projectionFormulaTwoSquare K).app E = D.projectionFormulaMap E K :=
  rfl

variable [∀ (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2),
    IsIso (D.projectionFormulaMap E K)]

/-- The projection-formula 2-square is invertible when each projection-formula map is. -/
instance isIso_projectionFormulaTwoSquare_natTrans
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    IsIso (D.projectionFormulaTwoSquare K) := by
  have : ∀ E, IsIso ((D.projectionFormulaTwoSquare K).app E) := fun E =>
    inferInstanceAs (IsIso (D.projectionFormulaMap E K))
  exact NatIso.isIso_of_isIso_app _

/-- The inverse projection formula as a 2-square `(Lf^*K ⊗^L -) ⋙ Rf_* ⟶ Rf_* ⋙ (K ⊗^L -)`. -/
def projectionFormulaInvTwoSquare (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    TwoSquare (D.tensorX.obj (D.pullback.obj K)) D.pushforward D.pushforward
      (D.tensorY.obj K) :=
  TwoSquare.mk _ _ _ _ (inv (D.projectionFormulaTwoSquare K))

variable {a : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 ⥤
    QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2}
  (adja : D.pushforward ⊣ a)

/-- The two-variable map of Stacks 0E5P as a 2-square `a ⋙ (Lf^*K ⊗^L -) ⟶ (K ⊗^L -) ⋙ a`. -/
def compareWithPullbackTensorTwoSquare
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    TwoSquare a (D.tensorY.obj K) (D.tensorX.obj (D.pullback.obj K)) a :=
  TwoSquare.mk _ _ _ _
    { app := fun L => D.compareWithPullbackTensor adja K L
      naturality := fun _ _ g => D.compareWithPullbackTensor_naturality_right adja K g }

/-- The component at `L` of `compareWithPullbackTensorTwoSquare adja K` is
`compareWithPullbackTensor adja K L`. -/
@[simp]
theorem compareWithPullbackTensorTwoSquare_natTrans_app
    (K L : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    (D.compareWithPullbackTensorTwoSquare adja K).app L =
      D.compareWithPullbackTensor adja K L :=
  rfl

/-- The two-variable map of Stacks 0E5P is the mate, for `Rf_* ⊣ a` on both sides, of the
inverse projection formula. -/
theorem compareWithPullbackTensorTwoSquare_eq_mateEquiv
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    D.compareWithPullbackTensorTwoSquare adja K =
      mateEquiv adja adja (D.projectionFormulaInvTwoSquare K) := by
  ext L
  simp [compareWithPullbackTensorTwoSquare, projectionFormulaInvTwoSquare,
    compareWithPullbackTensor, Adjunction.homEquiv_unit]

/-- **The Yoneda argument of Stacks 0E5Q.** If tensoring with `K'` is left adjoint to tensoring
with `K` on `D_QCoh(𝒪_Y)` and, after `Lf^*`, on `D_QCoh(𝒪_X)`, in such a way that the projection
formula for `K'` is the mate of the inverse projection formula for `K`, then the two-variable
map `Lf^*K ⊗^L a(L) ⟶ a(K ⊗^L L)` is invertible for every `L`: it is the conjugate of the
projection formula for `K'`. -/
theorem isIso_compareWithPullbackTensor_of_mateEquiv
    {K K' : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2}
    (adjX : D.tensorX.obj (D.pullback.obj K') ⊣ D.tensorX.obj (D.pullback.obj K))
    (adjY : D.tensorY.obj K' ⊣ D.tensorY.obj K)
    (hmate : mateEquiv adjX adjY (D.projectionFormulaTwoSquare K') =
      D.projectionFormulaInvTwoSquare K)
    (L : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    IsIso (D.compareWithPullbackTensor adja K L) := by
  have key := iterated_mateEquiv_conjugateEquiv adjX adjY adja adja
    (D.projectionFormulaTwoSquare K')
  rw [hmate] at key
  have hconj : IsIso (conjugateEquiv (adjX.comp adja) (adja.comp adjY)
      (D.projectionFormulaTwoSquare K')) := inferInstance
  have h : IsIso (D.compareWithPullbackTensorTwoSquare adja K) := by
    rw [D.compareWithPullbackTensorTwoSquare_eq_mateEquiv adja, key]
    exact hconj
  exact NatIso.isIso_app_of_isIso (D.compareWithPullbackTensorTwoSquare adja K) L

end AlgebraicGeometry.Space.PullbackComparisonData

end
