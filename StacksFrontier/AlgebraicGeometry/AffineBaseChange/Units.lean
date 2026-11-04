module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange
public import StacksFrontier.AlgebraicGeometry.SectionsColimit.Basic

/-!
# The base-change morphism on sections, and the unit that determines it

For a commutative square of schemes
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
the base-change morphism `g^* f_* ⟶ f'_* (g')^*` of
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` is the mate of
`Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso`, so it is *characterised* by
one equation: its direct image along `g`, precomposed with the unit of the
pullback--pushforward adjunction along `g`, is the direct image along `f` of the unit along
`g'`.  This file records that equation, reads it on sections over the whole space, and computes
the affine input needed to evaluate the resulting map: the unit of the pullback--pushforward
adjunction along `Spec.map φ` is `m ↦ 1 ⊗ m` on global sections.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChange.unit_comp_pushforward_baseChangeNatTrans` is the
  characterising equation.
* `Stacks.AlgebraicGeometry.AffineBaseChange.pushforwardSquareIso_hom_app_app_top`: on sections
  over the whole space the identification of the two composite direct images around the square
  is the identity.
* `Stacks.AlgebraicGeometry.AffineBaseChange.app_top_unit_comp_baseChangeNatTrans`: on sections
  over the whole space, the base-change morphism carries the canonical map
  `Γ(X, 𝓕) ⟶ Γ(S', g^* f_* 𝓕)` to the canonical map `Γ(X, 𝓕) ⟶ Γ(X', (g')^* 𝓕)`.
* `Stacks.AlgebraicGeometry.AffineBaseChange.tildePullbackIso_unit`: on global sections, and
  under the identification `Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso` of the
  inverse image of `M^~` along `Spec.map φ` with `(T ⊗_R M)^~`, the unit of the
  pullback--pushforward adjunction along `Spec.map φ` is `m ↦ 1 ⊗ m`.

## Implementation notes

The characterising equation is Mathlib's `CategoryTheory.unit_mateEquiv_symm` read through
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans_eq`; the components of the mate
live over the *inverse image* `(g')^* 𝓕`, which is where `pushforwardSquareIso` is evaluated.

`pushforwardSquareIso_hom_app_app_top` is not an instance of
`AlgebraicGeometry.Scheme.Modules.pushforwardComp_hom_app_app` alone: the middle factor of
`pushforwardSquareIso` is `pushforwardCongr`, whose components are the restriction maps of the
module along an equality of opens.  Over the whole space the two opens are
`(g')^{-1} f^{-1} ⊤` and `(f' ≫ g)^{-1} ⊤`, which are definitionally `⊤`, so the restriction
map is the identity by functoriality.

`tildePullbackIso_unit` is the uniqueness of left adjoints: both
`tilde.functor R ⋙ pullback (Spec.map φ)` and `ModuleCat.extendScalars φ ⋙ tilde.functor T`
are left adjoint to `Stacks.AlgebraicGeometry.SectionsColimit.pullbackSections φ`, and
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` identifies the comparison with the
two units.  The unit of the second adjunction is `m ↦ 1 ⊗ m` followed by
`AlgebraicGeometry.tilde.toTildeΓNatIso`, and that identification holds by `rfl`: the
comparison of the two `R`-module structures on `Γ(N, ⊤)` supplied by
`Stacks.AlgebraicGeometry.SectionsColimit.pullbackSectionsIso` is the identity map.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChange

/-! ### The characterising equation -/

section Mate

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- The defining property of the base-change morphism as a mate: the unit of the
pullback--pushforward adjunction along `g`, followed by the direct image along `g` of the
base-change morphism, is the direct image along `f` of the unit along `g'`, followed by the
canonical identification of the two composite direct images around the square. -/
theorem unit_comp_pushforward_baseChangeNatTrans (w : g' ≫ f = f' ≫ g) (F : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((Scheme.Modules.pushforward f).obj F) ≫
        (Scheme.Modules.pushforward g).map
          ((AffinePushforward.baseChangeNatTrans w).app F) =
      (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F) ≫
        (AffinePushforward.pushforwardSquareIso w).hom.app
          ((Scheme.Modules.pullback g').obj F) :=
  (unit_mateEquiv_symm (Scheme.Modules.pullbackPushforwardAdjunction g')
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    (TwoSquare.mk _ _ _ _ (AffinePushforward.pushforwardSquareIso w).hom) F).symm

/-- On sections over the whole space, the canonical identification of the two composite direct
images around a commutative square is the identity. -/
@[simp]
theorem pushforwardSquareIso_hom_app_app_top (w : g' ≫ f = f' ≫ g) (F : X'.Modules) :
    ((AffinePushforward.pushforwardSquareIso w).hom.app F).app ⊤ = 𝟙 _ := by
  simp only [Functor.comp_obj, Scheme.Modules.pushforward_obj_obj,
    TopologicalSpace.Opens.map_top, AffinePushforward.pushforwardSquareIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Scheme.Modules.Hom.comp_app, Scheme.Hom.comp_base,
    TopologicalSpace.Opens.map_comp_obj, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app, Scheme.Modules.pushforwardComp_inv_app_app,
    Category.comp_id, Category.id_comp]
  exact F.presheaf.map_id _

/-- On sections over the whole space the base-change morphism carries the canonical map
`Γ(X, 𝓕) ⟶ Γ(S', g^* f_* 𝓕)` to the canonical map `Γ(X, 𝓕) ⟶ Γ(X', (g')^* 𝓕)`.  Since
`Γ(S, f_* 𝓕) = Γ(X, 𝓕)` and `Γ(S', f'_* (g')^* 𝓕) = Γ(X', (g')^* 𝓕)`, this determines the
base-change morphism on global sections. -/
theorem app_top_unit_comp_baseChangeNatTrans (w : g' ≫ f = f' ≫ g) (F : X.Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
            ((Scheme.Modules.pushforward f).obj F) ≫
          (Scheme.Modules.pushforward g).map
            ((AffinePushforward.baseChangeNatTrans w).app F)).app ⊤ =
      ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F).app ⊤ := by
  rw [unit_comp_pushforward_baseChangeNatTrans]
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    TopologicalSpace.Opens.map_top, pushforwardSquareIso_hom_app_app_top]
  exact Category.comp_id _

end Mate

/-! ### The affine input -/

variable {R T : CommRingCat.{u}} (φ : R ⟶ T)

open SectionsColimit in
/-- On global sections, and under the identification of the inverse image of `M^~` along
`Spec.map φ` with `(T ⊗_R M)^~`, the unit of the pullback--pushforward adjunction along
`Spec.map φ` is `m ↦ 1 ⊗ m`. -/
theorem tildePullbackIso_unit (M : ModuleCat.{u} R) (m : M) :
    (moduleSpecΓFunctor.map ((tildePullbackIso φ).hom.app M)).hom
        ((moduleSpecΓFunctor.map
            ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
              ((tilde.functor R).obj M))).hom
          ((tilde.toTildeΓNatIso.hom.app M).hom m)) =
      (tilde.toTildeΓNatIso.hom.app ((ModuleCat.extendScalars φ.hom).obj M)).hom
        ((1 : T) ⊗ₜ[R,φ.hom] m) := by
  have key := Adjunction.unit_leftAdjointUniq_hom_app
    (tildePullbackAdjunction φ) (extendScalarsTildeAdjunction φ) M
  have hl : (tildePullbackAdjunction φ).unit.app M =
      tilde.toTildeΓNatIso.hom.app M ≫ moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
          ((tilde.functor R).obj M)) := by
    rw [tildePullbackAdjunction, Adjunction.comp_unit_app]
    rfl
  rw [hl] at key
  exact congr(ModuleCat.Hom.hom $(key) m)

end Stacks.AlgebraicGeometry.AffineBaseChange

end
