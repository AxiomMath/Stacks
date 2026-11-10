module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraDegreeZeroIso
import StacksCore.Tactic.StacksAttribute

/-!
# The determinant pairing of a right-exact presentation of sheaves of modules

Let `(X, O_X)` be a ringed space and let

`E₁ --α--> E₀ --π--> F ⟶ 0`

be a right-exact sequence of sheaves of `O_X`-modules with `E₁` finite locally free of rank
`r₁`. For every `r ≥ 0` there is a pairing

`⋀^{r₁} E₁ ⊗_{O_X} ⋀^{r} F ⟶ ⋀^{r₁ + r} E₀`,
`(t₁ ∧ ⋯ ∧ t_{r₁}) ⊗ (s₁ ∧ ⋯ ∧ s_r) ↦ α(t₁) ∧ ⋯ ∧ α(t_{r₁}) ∧ s̃₁ ∧ ⋯ ∧ s̃_r`,

for arbitrary local lifts `s̃ᵢ` of the `sᵢ`; in particular the right-hand side does not depend on
the lifts ([Stacks, Tag 0E9Y]).

## Main definitions

* `Stacks.Duality.detSheafPairing`: the pairing. In positive degree `r = k + 1` it is
  `Stacks.SheafOfModules.TopWedge.detComparison`, the comparison of [Stacks, Tag 0B38]; in degree
  zero it is the wedge map `⋀^{r₁} E₁ ⊗ ⋀^0 E₀ ⟶ ⋀^{r₁} E₀` read through the isomorphism
  `⋀^0 E₀ ≅ ⋀^0 F` (`Stacks.Duality.isIso_extHom_app_zero`).

## Main results

* `Stacks.Duality.detSheafPairing_wedge`: the local formula, with an arbitrary family of local
  lifts of the given local sections of `F`.
* `Stacks.Duality.detSheafPairing_wedge_congr_lift`: the value of the formula does not depend on
  the chosen local lifts.
* `Stacks.Duality.eq_detSheafPairing`: in positive degree the local formula determines the map.
* `Stacks.Duality.ringedSpaceDetSheafPairing` and
  `Stacks.Duality.ringedSpaceDetSheafPairing_wedge`: the same map and formula for the exterior
  powers that `SheafOfModules.ringedSpaceAlgebras` attaches to a sheaf of modules on a ringed
  space.

## References

* [Stacks Project, Tag 0E9Y](https://stacks.math.columbia.edu/tag/0E9Y)
* [Stacks Project, Tag 0B38](https://stacks.math.columbia.edu/tag/0B38)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Sheaf
open Stacks.SheafOfModules.TopWedge
open scoped TensorProduct

universe u

attribute [local implicit_reducible] structureSheafRing AlgebraicGeometry.SheafedSpace.sheaf

namespace Stacks.Duality

section Space

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {E₁ E₀ F : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

variable (A₁ : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E₁)
  (A₀ : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E₀)
  (AF : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) F)
  (α : E₁ ⟶ E₀) (π : E₀ ⟶ F) (hαπ : α ≫ π = 0)
  (hS : (ShortComplex.mk α π hαπ).Exact) (r₁ r k : ℕ)

/-- In degree zero the exterior power of an epimorphism is an isomorphism. -/
theorem isIso_extHom_app_zero : IsIso ((extHom A₀ AF π).app 0) :=
  _root_.SheafOfModules.GradedAlgebra.isIso_unitalHom_app_zero A₀.exteriorPieceZeroIsoUnit
    A₀.exteriorPieceZeroIsoUnit_one AF.exteriorPieceZeroIsoUnit AF.exteriorPieceZeroIsoUnit_one
    (extHom A₀ AF π)

/-- **The pairing of [Stacks, Tag 0E9Y].** For a right-exact sequence

`E₁ --α--> E₀ --π--> F ⟶ 0`

of sheaves of modules on a ringed space with `E₁` finite locally free of rank `r₁`, the map

`⋀^{r₁} E₁ ⊗ ⋀^{r} F ⟶ ⋀^{r₁ + r} E₀`

sending `(t₁ ∧ ⋯ ∧ t_{r₁}) ⊗ (s₁ ∧ ⋯ ∧ s_r)` to `α(t₁) ∧ ⋯ ∧ α(t_{r₁}) ∧ s̃₁ ∧ ⋯ ∧ s̃_r` for
arbitrary local lifts `s̃ᵢ` of `sᵢ` (`Stacks.Duality.detSheafPairing_wedge`). -/
noncomputable def detSheafPairing [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁] :
    (r : ℕ) → (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (A₁.exteriorPower r₁)).obj
      (AF.exteriorPower r) ⟶
      A₀.exteriorPower (r₁ + r))
  | 0 =>
    haveI := isIso_extHom_app_zero A₀ AF π
    haveI : IsIso (C := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) ((extHom A₀ AF π).app 0) :=
      isIso_extHom_app_zero A₀ AF π
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (A₁.exteriorPower r₁)).map
        (inv ((extHom A₀ AF π).app 0)) ≫ wedgeHom A₁ A₀ α r₁ 0
  | k + 1 => detComparison A₁ A₀ AF α π hαπ hS r₁ k

/-- **The local formula of the pairing of [Stacks, Tag 0E9Y].** On an open `V`, local sections
`t₁, …, t_{r₁}` of `E₁` and `s₁, …, s_r` of `F`, and **any** family of local lifts
`s̃₁, …, s̃_r` of the `sᵢ` along `π`, the pairing sends
`(t₁ ∧ ⋯ ∧ t_{r₁}) ⊗ (s₁ ∧ ⋯ ∧ s_r)` to `α(t₁) ∧ ⋯ ∧ α(t_{r₁}) ∧ s̃₁ ∧ ⋯ ∧ s̃_r`. -/
theorem detSheafPairing_wedge [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    (V : (Opens ↥X)ᵒᵖ) (t : Fin r₁ → E₁.val.obj V) (s : Fin r → F.val.obj V)
    (l : Fin r → E₀.val.obj V) (hl : ∀ i, π.val.app V (l i) = s i) :
    (detSheafPairing A₁ A₀ AF α π hαπ hS r₁ r).val.app V
        ((PresheafOfModules.tensorSheafUnit (A₁.exteriorPower r₁)
            (AF.exteriorPower r)).app V
          (wedgeSec A₁ V r₁ t ⊗ₜ wedgeSec AF V r s)) =
      wedgeSec A₀ V (r₁ + r) (Fin.append (fun i => α.val.app V (t i)) l) := by
  have hs : s = fun i => π.val.app V (l i) := (funext hl).symm
  subst hs
  cases r with
  | succ k => exact detComparison_wedge A₁ A₀ AF α π hαπ hS r₁ k V t l
  | zero =>
    have := isIso_extHom_app_zero A₀ AF π
    have : IsIso (C := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) ((extHom A₀ AF π).app 0) :=
      isIso_extHom_app_zero A₀ AF π
    have hpi : ((extHom A₀ AF π).app ((0 : ℕ) : ℤ)).val.app V (wedgeSec A₀ V 0 l) =
        wedgeSec AF V 0 fun i => π.val.app V (l i) := extHom_wedgeSec A₀ AF π V 0 l
    have hinv : (inv ((extHom A₀ AF π).app 0)).val.app V
        (wedgeSec AF V 0 fun i => π.val.app V (l i)) = wedgeSec A₀ V 0 l := by
      rw [← hpi]
      exact congrArg (fun m : A₀.exterior.piece 0 ⟶ A₀.exterior.piece 0 =>
        m.val.app V (wedgeSec A₀ V 0 l)) (IsIso.hom_inv_id ((extHom A₀ AF π).app 0))
    change (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
          (A₁.exteriorPower r₁)).map (inv ((extHom A₀ AF π).app 0)) ≫
        wedgeHom A₁ A₀ α r₁ 0).val.app V _ = _
    refine Eq.trans (_root_.SheafOfModules.comp_val_app_apply _ _ V _) ?_
    have mapUnit := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
      Osharp _ _
      (@CategoryStruct.id (_root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) _ (A₁.exteriorPower r₁))
      (inv ((extHom A₀ AF π).app 0)) V (wedgeSec A₁ V r₁ t)
      (wedgeSec AF V 0 fun i => π.val.app V (l i))
    rw [(Stacks.SheafOfModules.Tensor.sheafTensor Osharp).map_id (A₁.exteriorPower r₁),
      NatTrans.id_app ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
        (A₁.exteriorPower r₁)) (AF.exterior.piece 0), Category.id_comp] at mapUnit
    refine Eq.trans (congrArg ((wedgeHom A₁ A₀ α r₁ 0).val.app V) mapUnit) ?_
    refine Eq.trans (wedgeHom_unit A₁ A₀ α r₁ 0 V _ _) ?_
    refine Eq.trans (congrArg (fun z => (A₀.exterior.mul (r₁ : ℤ) ((0 : ℕ) : ℤ)).app V
        (((extHom A₁ A₀ α).app (r₁ : ℤ)).val.app V (wedgeSec A₁ V r₁ t)) z) hinv) ?_
    refine Eq.trans (congrArg (fun z => (A₀.exterior.mul (r₁ : ℤ) ((0 : ℕ) : ℤ)).app V z
        (wedgeSec A₀ V 0 l)) (extHom_wedgeSec A₁ A₀ α V r₁ t)) ?_
    refine Eq.trans
      (homogeneousProd_append A₀.exterior.toPresheafGradedAlgebra V r₁ 0 _ _) ?_
    exact congrArg (wedgeProd A₀.exterior V (r₁ + 0))
      (fin_append_comp (A₀.exteriorGenerator.val.app V) (fun i => α.val.app V (t i)) l).symm

include A₁ AF hαπ hS in
/-- **The well-definedness of the formula of [Stacks, Tag 0E9Y]**: the wedge of the images of
local sections of `E₁` with local lifts of local sections of `F` does not depend on the chosen
lifts. -/
theorem detSheafPairing_wedge_congr_lift [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    (V : (Opens ↥X)ᵒᵖ) (t : Fin r₁ → E₁.val.obj V) (s : Fin r → F.val.obj V)
    (l l' : Fin r → E₀.val.obj V) (hl : ∀ i, π.val.app V (l i) = s i)
    (hl' : ∀ i, π.val.app V (l' i) = s i) :
    wedgeSec A₀ V (r₁ + r) (Fin.append (fun i => α.val.app V (t i)) l) =
      wedgeSec A₀ V (r₁ + r) (Fin.append (fun i => α.val.app V (t i)) l') :=
  ((detSheafPairing_wedge A₁ A₀ AF α π hαπ hS r₁ r V t s l hl).symm).trans
    (detSheafPairing_wedge A₁ A₀ AF α π hαπ hS r₁ r V t s l' hl')

/-- **The local formula determines the pairing of [Stacks, Tag 0E9Y]** in positive degree
`k + 1`: a morphism `⋀^{r₁} E₁ ⊗ ⋀^{k+1} F ⟶ ⋀^{r₁+k+1} E₀` whose composite with
`⋀^{r₁} E₁ ⊗ ⋀^{k+1}(π)` is the wedge map is the pairing. -/
theorem eq_detSheafPairing [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    (ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (A₁.exteriorPower r₁)).obj
      (AF.exteriorPower (k + 1)) ⟶
      A₀.exteriorPower (r₁ + (k + 1)))
    (hψ : ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (A₁.exteriorPower r₁)).map
          ((extHom A₀ AF π).app ((k + 1 : ℕ) : ℤ)) ≫ ψ =
      wedgeHom A₁ A₀ α r₁ (k + 1)) :
    ψ = detSheafPairing A₁ A₀ AF α π hαπ hS r₁ (k + 1) :=
  eq_detComparison A₁ A₀ AF α π hαπ hS r₁ k ψ hψ

end Space

/-! ### The map for the canonical exterior powers on a ringed space -/

section RingedSpace

open _root_.Stacks.AlgebraicGeometry RingedSpaceModuleAdjunction

variable (Y : AlgebraicGeometry.RingedSpace.{u, u})
  {E₁ E₀ F : _root_.SheafOfModules.{u}
    (toRingCat (Opens.grothendieckTopology ↥Y.carrier) Y.sheaf)}
  (α : E₁ ⟶ E₀) (π : E₀ ⟶ F) (hαπ : α ≫ π = 0)
  (hS : (ShortComplex.mk α π hαπ).Exact) (r₁ r : ℕ)

/-- **The pairing of [Stacks, Tag 0E9Y] for the canonical exterior powers on a ringed
space.** This is `Stacks.Duality.detSheafPairing` for the package
`SheafOfModules.ringedSpaceAlgebras` of the three algebras that Section 17.21 attaches to a
sheaf of modules on a ringed space. -/
noncomputable def ringedSpaceDetSheafPairing [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(Y).presheaf, (Y).IsSheaf⟩).obj
      ((_root_.SheafOfModules.ringedSpaceAlgebras Y E₁).exteriorPower r₁)).obj
      ((_root_.SheafOfModules.ringedSpaceAlgebras Y F).exteriorPower r) ⟶
      (_root_.SheafOfModules.ringedSpaceAlgebras Y E₀).exteriorPower (r₁ + r) :=
  detSheafPairing (_root_.SheafOfModules.ringedSpaceAlgebras Y E₁)
    (_root_.SheafOfModules.ringedSpaceAlgebras Y E₀)
    (_root_.SheafOfModules.ringedSpaceAlgebras Y F) α π hαπ hS r₁ r

/-- **The local formula of [Stacks, Tag 0E9Y] for the canonical exterior powers on a ringed
space.** On an open `V`, local sections `t₁, …, t_{r₁}` of `E₁` and `s₁, …, s_r` of `F`, and
any local lifts `s̃ᵢ` of the `sᵢ` along `π`, the pairing sends
`(t₁ ∧ ⋯ ∧ t_{r₁}) ⊗ (s₁ ∧ ⋯ ∧ s_r)` to `α(t₁) ∧ ⋯ ∧ α(t_{r₁}) ∧ s̃₁ ∧ ⋯ ∧ s̃_r`. -/
theorem ringedSpaceDetSheafPairing_wedge [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    (V : (Opens ↥Y.carrier)ᵒᵖ) (t : Fin r₁ → E₁.val.obj V) (s : Fin r → F.val.obj V)
    (l : Fin r → E₀.val.obj V) (hl : ∀ i, π.val.app V (l i) = s i) :
    (ringedSpaceDetSheafPairing Y α π hαπ hS r₁ r).val.app V
        ((PresheafOfModules.tensorSheafUnit
            ((_root_.SheafOfModules.ringedSpaceAlgebras Y E₁).exteriorPower r₁)
            ((_root_.SheafOfModules.ringedSpaceAlgebras Y F).exteriorPower r)).app V
          (wedgeSec (_root_.SheafOfModules.ringedSpaceAlgebras Y E₁) V r₁ t ⊗ₜ
            wedgeSec (_root_.SheafOfModules.ringedSpaceAlgebras Y F) V r s)) =
      wedgeSec (_root_.SheafOfModules.ringedSpaceAlgebras Y E₀) V (r₁ + r)
        (Fin.append (fun i => α.val.app V (t i)) l) :=
  detSheafPairing_wedge (_root_.SheafOfModules.ringedSpaceAlgebras Y E₁)
    (_root_.SheafOfModules.ringedSpaceAlgebras Y E₀)
    (_root_.SheafOfModules.ringedSpaceAlgebras Y F) α π hαπ hS r₁ r V t s l hl

end RingedSpace

end Stacks.Duality

end
