module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleHigherBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralSurjectiveCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.StalksTestMaps

/-!
# Étale localisation of the base change map on higher direct images

The pasting law for the base change maps `f⁻¹ R^q g_* ⟶ R^q h_* e⁻¹` of two horizontally
composable squares (`Stacks.EtaleCohomology.higherBaseChangeMapAb_paste_app`, Stacks 0EZS) is
read here backwards: if the rectangle and one of the two squares have invertible base change
maps, so has the other (`Stacks.EtaleCohomology.isIso_map_higherBaseChangeMapAb_app_of_paste`,
`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_paste_left`).

Applied around a commutative cube this localises the base change map: if the base change maps
along étale (or smooth) `e : Ũ ⟶ U` and `e' : Ũ' ⟶ U'` are invertible (smooth base change), and
that of the base-changed square over `ũ : Ũ' ⟶ Ũ` is, then the inverse image along `e'` of the
base change map over `u' : U' ⟶ U` is invertible
(`Stacks.EtaleCohomology.isIso_map_higherBaseChangeMapAb_app_of_cube`). Isomorphisms of abelian
étale sheaves being étale local
(`Stacks.EtaleCohomology.isIso_of_forall_exists_isIso_smallEtalePullbackAb`), the base change map
can be checked on étale neighbourhoods, in which the coefficients may be trivialised.

## Main results

* `Stacks.EtaleCohomology.isIso_map_higherBaseChangeMapAb_app_of_paste`.
* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_paste_left`.
* `Stacks.EtaleCohomology.isIso_map_higherBaseChangeMapAb_app_of_cube`.
* `Stacks.EtaleCohomology.isIso_of_forall_exists_isIso_smallEtalePullbackAb`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Paste

variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}} (g₀ : X₀ ⟶ S₀) (g₁ : X₁ ⟶ S₁) (g₂ : X₂ ⟶ S₂)
  (u₁ : S₁ ⟶ S₀) (u₂ : S₂ ⟶ S₁) (v₁ : X₁ ⟶ X₀) (v₂ : X₂ ⟶ X₁)
  (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀) (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁) (q : ℕ)
  (F : Sheaf (smallEtaleTopology X₀) Ab.{u + 1})

/-- The composite of the three base change maps appearing in the pasting law is invertible as soon
as the base change map of the outer rectangle is. -/
private theorem isIso_comp_of_isIso_rectangle
    (hrect : IsIso ((higherBaseChangeMapAb (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
      (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂) q).app F)) :
    IsIso ((smallEtalePullbackAb u₂).map ((higherBaseChangeMapAb u₁ g₀ g₁ v₁ w₁ q).app F) ≫
      (higherBaseChangeMapAb u₂ g₁ g₂ v₂ w₂ q).app ((smallEtalePullbackAb v₁).obj F) ≫
      ((smallEtalePushforwardAb g₂).rightDerived q).map
        ((smallEtalePullbackAbCompIso v₂ v₁).hom.app F)) := by
  rw [higherBaseChangeMapAb_paste_app g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ q F] at hrect
  exact IsIso.of_isIso_comp_left ((smallEtalePullbackAbCompIso u₂ u₁).inv.app
    (((smallEtalePushforwardAb g₀).rightDerived q).obj F)) _

/-- **Cancellation in the pasting law, on the right square.** If the base change map of the
outer rectangle and that of the left square are invertible, so is the inverse image along `u₂`
of the base change map of the right square. -/
theorem isIso_map_higherBaseChangeMapAb_app_of_paste
    (hrect : IsIso ((higherBaseChangeMapAb (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
      (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂) q).app F))
    (h₂ : IsIso ((higherBaseChangeMapAb u₂ g₁ g₂ v₂ w₂ q).app ((smallEtalePullbackAb v₁).obj F))) :
    IsIso ((smallEtalePullbackAb u₂).map ((higherBaseChangeMapAb u₁ g₀ g₁ v₁ w₁ q).app F)) := by
  have h1 := isIso_comp_of_isIso_rectangle g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ q F hrect
  exact IsIso.of_isIso_comp_right _
    ((higherBaseChangeMapAb u₂ g₁ g₂ v₂ w₂ q).app ((smallEtalePullbackAb v₁).obj F) ≫
      ((smallEtalePushforwardAb g₂).rightDerived q).map
        ((smallEtalePullbackAbCompIso v₂ v₁).hom.app F))

/-- **Cancellation in the pasting law, on the left square.** If the base change map of the
outer rectangle and the inverse image along `u₂` of that of the right square are invertible, so
is the base change map of the left square. -/
theorem isIso_higherBaseChangeMapAb_app_of_paste_left
    (hrect : IsIso ((higherBaseChangeMapAb (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
      (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂) q).app F))
    (h₁ : IsIso ((smallEtalePullbackAb u₂).map ((higherBaseChangeMapAb u₁ g₀ g₁ v₁ w₁ q).app F))) :
    IsIso ((higherBaseChangeMapAb u₂ g₁ g₂ v₂ w₂ q).app ((smallEtalePullbackAb v₁).obj F)) := by
  have h1 := isIso_comp_of_isIso_rectangle g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ q F hrect
  have h2 : IsIso ((higherBaseChangeMapAb u₂ g₁ g₂ v₂ w₂ q).app ((smallEtalePullbackAb v₁).obj F) ≫
      ((smallEtalePushforwardAb g₂).rightDerived q).map
        ((smallEtalePullbackAbCompIso v₂ v₁).hom.app F)) :=
    IsIso.of_isIso_comp_left
      ((smallEtalePullbackAb u₂).map ((higherBaseChangeMapAb u₁ g₀ g₁ v₁ w₁ q).app F)) _
  exact IsIso.of_isIso_comp_right _
    (((smallEtalePushforwardAb g₂).rightDerived q).map
      ((smallEtalePullbackAbCompIso v₂ v₁).hom.app F))

end Paste


/-- **Localisation of the base change map along a cube.** Consider the base change square of
`u' : U' ⟶ U` (with `j : U₀ ⟶ U`, `j' : U₀' ⟶ U'`), a square over `e : Ũ ⟶ U` (with
`j̃ : Ũ₀ ⟶ Ũ`), a square over `e' : Ũ' ⟶ U'` (with `j̃' : Ũ₀' ⟶ Ũ'`) and a square over
`ũ : Ũ' ⟶ Ũ`, forming a commutative cube. If the base change maps of the squares over `e`, `e'`
and `ũ` are invertible in degree `q` (at `F`, `u₀⁻¹ F` and `e₀⁻¹ F`), then so is the inverse
image along `e'` of the base change map of `u'` at `F`: both ways around the cube give the base
change map of the outer rectangle (Stacks 0EZS, `isIso_higherBaseChangeMapAb_app_of_paste`). -/
theorem isIso_map_higherBaseChangeMapAb_app_of_cube {U U₀ U' U₀' Ũ Ũ₀ Ũ' Ũ₀' : Scheme.{u}}
    (j : U₀ ⟶ U) (j' : U₀' ⟶ U') (jt : Ũ₀ ⟶ Ũ) (jt' : Ũ₀' ⟶ Ũ')
    (u' : U' ⟶ U) (u₀ : U₀' ⟶ U₀) (w : j' ≫ u' = u₀ ≫ j)
    (e : Ũ ⟶ U) (e₀ : Ũ₀ ⟶ U₀) (we : jt ≫ e = e₀ ≫ j)
    (e' : Ũ' ⟶ U') (e₀' : Ũ₀' ⟶ U₀') (we' : jt' ≫ e' = e₀' ≫ j')
    (ũ : Ũ' ⟶ Ũ) (ũ₀ : Ũ₀' ⟶ Ũ₀) (wũ : jt' ≫ ũ = ũ₀ ≫ jt)
    (hu : e' ≫ u' = ũ ≫ e) (hv : e₀' ≫ u₀ = ũ₀ ≫ e₀) (q : ℕ)
    (F : Sheaf (smallEtaleTopology U₀) Ab.{u + 1})
    (hB : IsIso ((higherBaseChangeMapAb e j jt e₀ we q).app F))
    (hA : IsIso ((higherBaseChangeMapAb e' j' jt' e₀' we' q).app ((smallEtalePullbackAb u₀).obj F)))
    (hC : IsIso ((higherBaseChangeMapAb ũ jt jt' ũ₀ wũ q).app ((smallEtalePullbackAb e₀).obj F))) :
    IsIso ((smallEtalePullbackAb e').map ((higherBaseChangeMapAb u' j j' u₀ w q).app F)) := by
  have hrectB := isIso_higherBaseChangeMapAb_app_of_paste j jt jt' e ũ e₀ ũ₀ we wũ q F hB hC
  have hrectA := (isIso_higherBaseChangeMapAb_app_congr j jt' hu.symm hv.symm _
    (smallEtaleRectangle_comm j j' jt' u' e' u₀ e₀' w we') q F).1 hrectB
  exact isIso_map_higherBaseChangeMapAb_app_of_paste j j' jt' u' e' u₀ e₀' w we' q F hrectA hA

/-- **Isomorphisms of abelian étale sheaves are étale local.** If every point of `X` lies in the
image of some `e : V ⟶ X` along which the inverse image of `φ` is an isomorphism, then `φ` is
an isomorphism. -/
theorem isIso_of_forall_exists_isIso_smallEtalePullbackAb {X : Scheme.{u}}
    {F G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (φ : F ⟶ G)
    (h : ∀ p : X, ∃ (V : Scheme.{u}) (e : V ⟶ X), p ∈ Set.range e.base ∧
      IsIso ((smallEtalePullbackAb e).map φ)) : IsIso φ := by
  choose V e hp hφ using h
  choose v hv using hp
  refine isIso_of_geometricStalkAb_family (fun p => (V p).algClosedPointHom (v p) ≫ e p) ?_ φ ?_
  · refine Set.eq_univ_of_forall fun p => Set.mem_iUnion.2 ⟨p, default, ?_⟩
    rw [Scheme.Hom.comp_apply, Scheme.algClosedPointHom_apply, hv]
  · intro p
    have := hφ p
    have hnat :=
      (smallEtalePullbackStalkAbIso (e p) ((V p).algClosedPointHom (v p))).hom.naturality φ
    have : IsIso ((smallEtalePullbackAb (e p) ⋙
        smallEtaleStalkAb ((V p).algClosedPointHom (v p))).map φ ≫
        (smallEtalePullbackStalkAbIso (e p) ((V p).algClosedPointHom (v p))).hom.app G) := by
      dsimp only [Functor.comp_map]
      infer_instance
    rw [hnat] at this
    exact IsIso.of_isIso_comp_left
      ((smallEtalePullbackStalkAbIso (e p) ((V p).algClosedPointHom (v p))).hom.app F) _

end Stacks.EtaleCohomology

end
