module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SetAbelianBaseChangeTransfer

/-!
# The base change map of sheaves of sets, from Mathlib's small étale site to the bounded one

Let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a commutative square of the underlying category of a big étale site `B`. Each of its schemes
carries two small étale sites, Mathlib's site `AlgebraicGeometry.Scheme.Etale` of all schemes
étale over it and the size-bounded site `AlgebraicGeometry.SmallEtale` of Stacks 021B, with the
same sheaves. Each carries a base change map `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of sheaves of sets:
`Stacks.EtaleCohomology.smallEtaleSetBaseChange` on Mathlib's sites, in which the proper base
change development is written, and `AlgebraicGeometry.smallEtaleBaseChangeNatTrans` on the
bounded sites, in which descent of small étale sheaves is written.

`AlgebraicGeometry.SmallEtale.isIso_mateEquiv_symm_unboundedBaseChangeMate` moves invertibility
from the bounded site to Mathlib's site. This file moves it the other way, which is the direction
in which a base change theorem proved on Mathlib's site — the proper base change theorem in degree
zero, Stacks 0A3U — reaches a descent statement written on the bounded site. The device is
the transfer of invertibility of a mate along an essentially surjective change of categories,
applied to the same cube identity
`AlgebraicGeometry.SmallEtale.baseChangeMate_cube_eq`; the functor that has to be essentially
surjective is restriction from Mathlib's site of `X` to the bounded site, half of the equivalence
`AlgebraicGeometry.SmallEtale.sheafEquiv`.

## Main results

* `SmallEtale.isIso_smallEtaleBaseChangeNatTrans_of_isIso_smallEtaleSetBaseChange`: the
  bounded base change map of sheaves of sets is invertible if the one on Mathlib's site is.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
-/

@[expose] public noncomputable section

open CategoryTheory.TwoSquare
open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u})
variable {X X' Y Y' : B.Scheme} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')

/-- Transfer of invertibility of a mate along the cube identity, when `ΦC` is essentially
surjective. -/
private theorem isIso_mateEquiv_symm_of_essSurj_cube_eq
    {C D E F C' D' E' F' : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
    [Category.{u + 1} E] [Category.{u + 1} F] [Category.{u + 1} C'] [Category.{u + 1} D']
    [Category.{u + 1} E'] [Category.{u + 1} F']
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {L₁' : C' ⥤ D'} {R₁' : D' ⥤ C'} {L₂' : E' ⥤ F'} {R₂' : F' ⥤ E'}
    {G : C ⥤ E} {H : D ⥤ F} {G' : C' ⥤ E'} {H' : D' ⥤ F'}
    {ΦC : C ⥤ C'} {ΦD : D ⥤ D'} {ΦE : E ⥤ E'} {ΦF : F ⥤ F'}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
    (τ₁ : TwoSquare ΦC L₁ L₁' ΦD) (τ₂ : TwoSquare ΦE L₂ L₂' ΦF)
    (σG : G ⋙ ΦE ⟶ ΦC ⋙ G') (σH : ΦD ⋙ H' ⟶ H ⋙ ΦF)
    (β : TwoSquare R₁ H G R₂) (β' : TwoSquare R₁' H' G' R₂') [ΦC.EssSurj]
    [IsIso τ₁] [IsIso τ₂] [IsIso σG] [IsIso σH]
    (hβ : IsIso ((mateEquiv adj₁ adj₂).symm β))
    (h : ((mateEquiv adj₁ adj₁' τ₁ ≫ᵥ β').whiskerRight σG).whiskerLeft σH =
      β ≫ᵥ mateEquiv adj₂ adj₂' τ₂) :
    IsIso ((mateEquiv adj₁' adj₂').symm β') := by
  -- the transfer of invertibility from the front face of the cube to the back face, with `ΦC`
  -- essentially surjective: the cube identity gives invertibility at the objects `ΦC c`, and
  -- naturality spreads it to the essential image
  have hl : IsIso ((mateEquiv adj₁ adj₂).symm β ≫ₕ τ₂) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro c
    have e : ((mateEquiv adj₁ adj₂).symm β ≫ₕ τ₂).app c =
        τ₂.app (G.obj c) ≫ ΦF.map (((mateEquiv adj₁ adj₂).symm β).app c) := by
      simp [TwoSquare.hComp]
    rw [e]
    infer_instance
  rw [Stacks.CategoryTheory.mateEquiv_symm_hComp_eq adj₁ adj₂ adj₁' adj₂' τ₁ τ₂ σG σH β β' h]
    at hl
  have hw : IsIso (τ₁ ≫ₕ (mateEquiv adj₁' adj₂').symm β') := by
    generalize τ₁ ≫ₕ (mateEquiv adj₁' adj₂').symm β' = w at hl ⊢
    have e : w = inv (Functor.whiskerRight σG L₂') ≫
        ((Functor.whiskerRight σG L₂' ≫ w) ≫ Functor.whiskerLeft L₁ σH) ≫
          inv (Functor.whiskerLeft L₁ σH) := by
      rw [Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
        IsIso.inv_hom_id_assoc]
    rw [e]
    have : IsIso ((Functor.whiskerRight σG L₂' ≫ w) ≫ Functor.whiskerLeft L₁ σH) := hl
    infer_instance
  rw [NatTrans.isIso_iff_isIso_app]
  intro d
  obtain ⟨c, ⟨e⟩⟩ : ∃ c, Nonempty (ΦC.obj c ≅ d) :=
    ⟨ΦC.objPreimage d, ⟨ΦC.objObjPreimageIso d⟩⟩
  have hc : IsIso (((mateEquiv adj₁' adj₂').symm β').app (ΦC.obj c)) := by
    have := NatIso.isIso_app_of_isIso (τ₁ ≫ₕ (mateEquiv adj₁' adj₂').symm β') c
    have e' : (τ₁ ≫ₕ (mateEquiv adj₁' adj₂').symm β').app c =
        ((mateEquiv adj₁' adj₂').symm β').app (ΦC.obj c) ≫
          H'.map (τ₁.app c) := by
      simp [TwoSquare.hComp]
    rw [e'] at this
    exact IsIso.of_isIso_comp_right _ (H'.map (τ₁.app c))
  have nat := ((mateEquiv adj₁' adj₂').symm β').naturality e.hom
  have h₂ : ((mateEquiv adj₁' adj₂').symm β').app d =
      inv ((G' ⋙ L₂').map e.hom) ≫ ((mateEquiv adj₁' adj₂').symm β').app (ΦC.obj c) ≫
        (L₁' ⋙ H').map e.hom := by
    rw [← nat]
    simp
  rw [h₂]
  infer_instance

/-- **The base change map of sheaves of sets on the bounded small étale sites is invertible if the
one on Mathlib's small étale sites is.** For a commutative square `g' ≫ f = f' ≫ g` of a big étale
site, if `Stacks.EtaleCohomology.smallEtaleSetBaseChange` is an isomorphism at the coefficient
universe `u + 1` of the site, so is `AlgebraicGeometry.smallEtaleBaseChangeNatTrans`. -/
public theorem isIso_smallEtaleBaseChangeNatTrans_of_isIso_smallEtaleSetBaseChange
    (h : g' ≫ f = f' ≫ g)
    (hset : IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} (B.inclusion.map g')
      (B.inclusion.map f') (B.inclusion.map f) (B.inclusion.map g)
      (by rw [← B.inclusion.map_comp, ← B.inclusion.map_comp, h]))) :
    IsIso (smallEtaleBaseChangeNatTrans.{u} B g' f' f g h) := by
  let adjUg := Stacks.EtaleCohomology.smallEtaleInverseImageAdjunction.{u, 0} (B.inclusion.map g)
  let adjUg' :=
    Stacks.EtaleCohomology.smallEtaleInverseImageAdjunction.{u, 0} (B.inclusion.map g')
  have hun : IsIso ((mateEquiv adjUg' adjUg).symm
      (unboundedBaseChangeMate B (Type (u + 1)) f g g' f' (g' ≫ f) rfl h.symm)) := by
    rw [Stacks.EtaleCohomology.smallEtaleSetBaseChange_eq_mateEquiv_symm
      (B.inclusion.map f) (B.inclusion.map g) (B.inclusion.map g') (B.inclusion.map f')] at hset
    exact hset
  have hEq : ((toEtaleSite B X.obj X.property).sheafPushforwardContinuous (Type (u + 1))
      (topology B X.obj X.property) X.obj.smallEtaleTopology).EssSurj :=
    (sheafEquiv B X.obj X.property (Type (u + 1))).isEquivalence_inverse.essSurj
  have := isIso_restrictionPullbackBaseChange B (Type (u + 1)) g' adjUg'
    (B.smallPullbackAdjunction g' (Type (u + 1)))
  have := isIso_restrictionPullbackBaseChange B (Type (u + 1)) g adjUg
    (B.smallPullbackAdjunction g (Type (u + 1)))
  have hb := isIso_mateEquiv_symm_of_essSurj_cube_eq
    adjUg' adjUg (B.smallPullbackAdjunction g' (Type (u + 1)))
    (B.smallPullbackAdjunction g (Type (u + 1)))
    (restrictionPullbackBaseChange B (Type (u + 1)) g' adjUg' _)
    (restrictionPullbackBaseChange B (Type (u + 1)) g adjUg _)
    (toEtaleSitePushforwardBaseChangeIso B f (Type (u + 1))).hom
    (toEtaleSitePushforwardBaseChangeIso B f' (Type (u + 1))).inv
    (unboundedBaseChangeMate B (Type (u + 1)) f g g' f' (g' ≫ f) rfl h.symm)
    (boundedBaseChangeMate B (Type (u + 1)) f g g' f' (g' ≫ f) rfl h.symm)
    hun (baseChangeMate_cube_eq B (Type (u + 1)) f g g' f' (g' ≫ f) rfl h.symm adjUg _ adjUg' _)
  rw [← smallEtaleBaseChangeMate_eq_boundedBaseChangeMate.{u} B f g g' f' h (g' ≫ f) rfl
    h.symm] at hb
  exact hb

/-- **The base change map of abelian sheaves on the bounded small étale sites is invertible if the
one on Mathlib's small étale sites is.** For a commutative square `g' ≫ f = f' ≫ g` of a big
étale site, if `Stacks.EtaleCohomology.etaleAbelianBaseChange` is an isomorphism for abelian
sheaves on Mathlib's small étale sites at the coefficient universe `u + 1` of the site, so is the
base change map `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of abelian sheaves on the bounded small étale sites, the
mate of `AlgebraicGeometry.SmallEtale.boundedBaseChangeMate`. The argument is that of
`AlgebraicGeometry.SmallEtale.isIso_smallEtaleBaseChangeNatTrans_of_isIso_smallEtaleSetBaseChange`
at abelian coefficients. -/
public theorem isIso_mateEquiv_symm_boundedBaseChangeMate_of_isIso_etaleAbelianBaseChange
    (h : g' ≫ f = f' ≫ g)
    (hab : IsIso (Stacks.EtaleCohomology.etaleAbelianBaseChange.{u, 0} (B.inclusion.map f)
      (B.inclusion.map g) (B.inclusion.map g') (B.inclusion.map f')
      (by rw [← B.inclusion.map_comp, ← B.inclusion.map_comp, h]))) :
    IsIso ((mateEquiv (B.smallPullbackAdjunction g' AddCommGrpCat.{u + 1})
      (B.smallPullbackAdjunction g AddCommGrpCat.{u + 1})).symm
        (boundedBaseChangeMate B AddCommGrpCat.{u + 1} f g g' f' (g' ≫ f) rfl
          h.symm)) := by
  let adjUg := Stacks.EtaleCohomology.etaleAbelianInverseImageDirectImageAdj.{u, 0}
    (B.inclusion.map g)
  let adjUg' := Stacks.EtaleCohomology.etaleAbelianInverseImageDirectImageAdj.{u, 0}
    (B.inclusion.map g')
  have hun : IsIso ((mateEquiv adjUg' adjUg).symm
      (unboundedBaseChangeMate B AddCommGrpCat.{u + 1} f g g' f' (g' ≫ f) rfl
        h.symm)) := by
    rw [Stacks.EtaleCohomology.etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso.{u, 0}
      (B.inclusion.map f) (B.inclusion.map g) (B.inclusion.map g') (B.inclusion.map f') _
      (B.inclusion.map (g' ≫ f)) (B.inclusion.map_comp g' f)
      ((congrArg B.inclusion.map h).trans (B.inclusion.map_comp f' g))] at hab
    exact hab
  have hEq : ((toEtaleSite B X.obj X.property).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (topology B X.obj X.property) X.obj.smallEtaleTopology).EssSurj :=
    (sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).isEquivalence_inverse.essSurj
  have := isIso_restrictionPullbackBaseChange B AddCommGrpCat.{u + 1} g' adjUg'
    (B.smallPullbackAdjunction g' AddCommGrpCat.{u + 1})
  have := isIso_restrictionPullbackBaseChange B AddCommGrpCat.{u + 1} g adjUg
    (B.smallPullbackAdjunction g AddCommGrpCat.{u + 1})
  exact isIso_mateEquiv_symm_of_essSurj_cube_eq
    adjUg' adjUg (B.smallPullbackAdjunction g' AddCommGrpCat.{u + 1})
    (B.smallPullbackAdjunction g AddCommGrpCat.{u + 1})
    (restrictionPullbackBaseChange B AddCommGrpCat.{u + 1} g' adjUg' _)
    (restrictionPullbackBaseChange B AddCommGrpCat.{u + 1} g adjUg _)
    (toEtaleSitePushforwardBaseChangeIso B f AddCommGrpCat.{u + 1}).hom
    (toEtaleSitePushforwardBaseChangeIso B f' AddCommGrpCat.{u + 1}).inv
    (unboundedBaseChangeMate B AddCommGrpCat.{u + 1} f g g' f' (g' ≫ f) rfl h.symm)
    (boundedBaseChangeMate B AddCommGrpCat.{u + 1} f g g' f' (g' ≫ f) rfl h.symm)
    hun (baseChangeMate_cube_eq B AddCommGrpCat.{u + 1} f g g' f' (g' ≫ f) rfl h.symm adjUg _
      adjUg' _)

/-- **Stacks 0959 for abelian sheaves on the bounded small étale sites.** For a cartesian square
`g' ≫ f = f' ≫ g` of a big étale site with `f` finite, the base change map
`g⁻¹ f_* ⟶ f'_* (g')⁻¹` of abelian sheaves on the size-bounded small étale sites — the mate of
`AlgebraicGeometry.SmallEtale.boundedBaseChangeMate` — is an isomorphism. It is transported from
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite`, the same statement on
Mathlib's small étale sites. -/
public theorem isIso_mateEquiv_symm_boundedBaseChangeMate_of_isFinite
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    [IsFinite (B.inclusion.map f)] (h : g' ≫ f = f' ≫ g) :
    IsIso ((mateEquiv (B.smallPullbackAdjunction g' AddCommGrpCat.{u + 1})
      (B.smallPullbackAdjunction g AddCommGrpCat.{u + 1})).symm
        (boundedBaseChangeMate B AddCommGrpCat.{u + 1} f g g' f' (g' ≫ f) rfl h.symm)) :=
  isIso_mateEquiv_symm_boundedBaseChangeMate_of_isIso_etaleAbelianBaseChange B f g g' f' h
    (Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite B f g g' f' sq)

end AlgebraicGeometry.SmallEtale

end
