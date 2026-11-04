module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Affine
public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtVanishingAffine
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde

/-!
# The affine base change morphism on associated sheaves

Let `R → A`, `R → R'`, `A → A'`, `R' → A'` be a commutative square of rings and consider the
commutative square of their spectra.  For an `R`-module `P`, an `A`-module `M`, an `A'`-module `N`,
an `R`-linear `p : P ⟶ M` and an `A'`-linear `χ : A' ⊗_A M ⟶ N`, the composite

`(R' ⊗_R P)~ ≅ (Spec b)^*P̃ ⟶ (Spec b)^*(Spec a)_*M̃ ⟶ (Spec d)_*(Spec c)^*M̃`
`  ≅ (Spec d)_*(A' ⊗_A M)~ ⟶ (Spec d)_*Ñ`

through the base change morphism of Stacks 02KG is the sheaf associated to the `R'`-linear map
`R' ⊗_R P ⟶ N` extending `x ↦ χ(1 ⊗ p x)`.

## Main results

* `AlgebraicGeometry.tilde_baseChange_comp`.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry

variable {R A R' A' : CommRingCat.{u}} {a : R ⟶ A} {b : R ⟶ R'} {c : A ⟶ A'} {d : R' ⟶ A'}

/-- **The affine base change morphism on associated sheaves.** The composite of the inverse of the
affine pullback comparison, the pullback of `p` followed by the affine pushforward comparison, the
base change morphism `Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w`, and the
pushforward of the affine pullback comparison followed by `χ`, is the sheaf associated to an
`R'`-linear `v` with `v (1 ⊗ x) = χ (1 ⊗ p x)`, followed by the affine pushforward comparison. -/
theorem tilde_baseChange_comp (w : Spec.map c ≫ Spec.map a = Spec.map d ≫ Spec.map b)
    (P : ModuleCat.{u} R) (M : ModuleCat.{u} A) (N : ModuleCat.{u} A')
    (p : P ⟶ (ModuleCat.restrictScalars a.hom).obj M)
    (χ : (ModuleCat.extendScalars c.hom).obj M ⟶ N)
    (v : (ModuleCat.extendScalars b.hom).obj P ⟶ (ModuleCat.restrictScalars d.hom).obj N)
    (hv : ∀ x : P, v.hom ((1 : R') ⊗ₜ[R, b.hom] x) = χ.hom ((1 : A') ⊗ₜ[A, c.hom] p.hom x)) :
    (pullbackTildeIso R R' b).inv.app P ≫
        (Scheme.Modules.pullback (Spec.map b)).map
          ((tilde.functor R).map p ≫ (pushforwardTildeNatTrans R A a).app M) ≫
        (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app (tilde M) ≫
        (Scheme.Modules.pushforward (Spec.map d)).map
          ((pullbackTildeIso A A' c).hom.app M ≫ (tilde.functor A').map χ) =
      (tilde.functor R').map v ≫ (pushforwardTildeNatTrans R' A' d).app N := by
  refine Stacks.RegularSequence.tilde_hom_ext _ _ ?_
  refine (cancel_epi (tilde.toOpen _ ⊤)).mp ?_
  refine ModuleCat.ExtendScalars.hom_ext fun x => ?_
  have h₁ := congrArg (fun g => ((pushforwardTildeNatTrans R' A' d).app N).val.app
      (Opposite.op ⊤) (g.hom ((1 : R') ⊗ₜ[R, b.hom] x))) (tilde.toOpen_map_app v ⊤)
  have h₂ := pushforwardTildeNatTrans_app_toOpen R' A' d N (v.hom ((1 : R') ⊗ₜ[R, b.hom] x))
  have hR : (tilde.toOpen ((ModuleCat.extendScalars b.hom).obj P) ⊤ ≫
      moduleSpecΓFunctor.map ((tilde.functor R').map v ≫
        (pushforwardTildeNatTrans R' A' d).app N)).hom ((1 : R') ⊗ₜ[R, b.hom] x) =
      tilde.toOpen N ⊤ (χ.hom ((1 : A') ⊗ₜ[A, c.hom] p.hom x)) := by
    rw [← hv]
    exact h₁.trans h₂
  refine Eq.trans ?_ hR.symm
  have hi : ((pullbackTildeIso R R' b).inv.app P).val.app (Opposite.op ⊤)
      (tilde.toOpen ((ModuleCat.extendScalars b.hom).obj P) ⊤ ((1 : R') ⊗ₜ[R, b.hom] x)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map b)).unit.app
        (tilde P)).val.app (Opposite.op ⊤) (tilde.toOpen P ⊤ x) := by
    rw [← pullbackTildeIso_hom_app_unit_toOpen R R' b P x]
    exact congrArg (fun g => (g.val.app (Opposite.op (⊤ : (Spec R').Opens))).hom
      (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map b)).unit.app
        (tilde P)).val.app (Opposite.op ⊤) (tilde.toOpen P ⊤ x)))
      ((pullbackTildeIso R R' b).hom_inv_id_app P)
  have hn := congrArg (fun g => (g.val.app (Opposite.op (⊤ : (Spec R).Opens))).hom
      (tilde.toOpen P ⊤ x))
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map b)).unit.naturality
      ((tilde.functor R).map p ≫ (pushforwardTildeNatTrans R A a).app M))
  have hh : ((tilde.functor R).map p ≫ (pushforwardTildeNatTrans R A a).app M).val.app
      (Opposite.op ⊤) (tilde.toOpen P ⊤ x) = tilde.toOpen M ⊤ (p.hom x) :=
    (congrArg (fun g => ((pushforwardTildeNatTrans R A a).app M).val.app
      (Opposite.op ⊤) (g.hom x)) (tilde.toOpen_map_app p ⊤)).trans
        (pushforwardTildeNatTrans_app_toOpen R A a M (p.hom x))
  have hbc := congrArg (fun g => g.hom (tilde.toOpen M ⊤ (p.hom x)))
    (Stacks.AlgebraicGeometry.AffineBaseChangeIso.baseChangeNatTrans_app_app_top w (tilde M))
  have hk : ((pullbackTildeIso A A' c).hom.app M ≫ (tilde.functor A').map χ).val.app
      (Opposite.op ⊤) (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map c)).unit.app
        (tilde M)).val.app (Opposite.op ⊤) (tilde.toOpen M ⊤ (p.hom x))) =
      tilde.toOpen N ⊤ (χ.hom ((1 : A') ⊗ₜ[A, c.hom] p.hom x)) :=
    (congrArg (fun z => ((tilde.functor A').map χ).val.app (Opposite.op ⊤) z)
      (pullbackTildeIso_hom_app_unit_toOpen A A' c M (p.hom x))).trans
        (congrArg (fun g => g.hom ((1 : A') ⊗ₜ[A, c.hom] p.hom x)) (tilde.toOpen_map_app χ ⊤))
  let G := (pullbackTildeIso A A' c).hom.app M ≫ (tilde.functor A').map χ
  let F := (tilde.functor R).map p ≫ (pushforwardTildeNatTrans R A a).app M
  let β := (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app (tilde M)
  calc _ = ((Scheme.Modules.pushforward (Spec.map d)).map G).val.app (Opposite.op ⊤)
          (β.val.app (Opposite.op ⊤) (((Scheme.Modules.pullback (Spec.map b)).map F).val.app
            (Opposite.op ⊤) (((pullbackTildeIso R R' b).inv.app P).val.app (Opposite.op ⊤)
              (tilde.toOpen ((ModuleCat.extendScalars b.hom).obj P) ⊤
                ((1 : R') ⊗ₜ[R, b.hom] x))))) := rfl
    _ = ((Scheme.Modules.pushforward (Spec.map d)).map G).val.app (Opposite.op ⊤)
          (β.val.app (Opposite.op ⊤) (((Scheme.Modules.pullbackPushforwardAdjunction
            (Spec.map b)).unit.app ((Scheme.Modules.pushforward (Spec.map a)).obj
              (tilde M))).val.app (Opposite.op ⊤) (F.val.app (Opposite.op ⊤)
                (tilde.toOpen P ⊤ x)))) := by rw [hi]; exact congrArg _ (congrArg _ hn.symm)
    _ = _ := by rw [hh]; exact (congrArg _ hbc).trans hk

end AlgebraicGeometry
