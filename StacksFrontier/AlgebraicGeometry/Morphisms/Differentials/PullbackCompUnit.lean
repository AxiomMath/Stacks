module

public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.CoborderDifferentialsStalk
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections

/-!
# Composing the canonical maps on relative differentials along the source

For a composable pair `Z --j--> W --ι--> X` of schemes over a base `S`, the sheaf of relative
differentials of `W` and of `Z` are compared with that of `X` by the canonical maps of Stacks
01UV.  This module records that the two comparisons compose to the comparison of the composite,
once the iterated pullback `j^*ι^*` is identified with `(j ≫ ι)^*` by
`AlgebraicGeometry.Scheme.Modules.pullbackComp`.

This is the composition law in the *source* direction.  The composition law in the *base*
direction is `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_comp`, which stacks a square
against one whose source morphism is the identity and therefore needs no comparison of iterated
pullbacks.

## Main results

* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_app_pullbackComp_inv_unit`: the
  composition law read on the universal differential of a local section of `𝒪_X`.
* `AlgebraicGeometry.Scheme.Hom.pullbackComp_inv_comp_relativeDifferentialsMap` and
  `AlgebraicGeometry.Scheme.Hom.pullbackComp_hom_comp_relativeDifferentialsMap`: the composition
  law as an equality of morphisms of sheaves of modules, obtained from the previous statement by
  the uniqueness of Stacks 01UV.
* `AlgebraicGeometry.pullbackSectionsMap_apply`: the map on global sections of Stacks 03DS is
  the unit of the pullback--pushforward adjunction followed by the comparison of iterated
  pullbacks.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_app_top_pullbackSectionsMap`: the
  composition law on global sections.  A global section of `T.hom^*Ω_{X/S}` whose canonical image
  is the universal differential of a global function `a` on `T` restricts, along a morphism
  `g : T' ⟶ T` of schemes over `X`, to a global section of `T'.hom^*Ω_{X/S}` whose canonical
  image is the universal differential of the pullback of `a`.

## Implementation notes

The intermediate and outer structure morphisms `qW` and `qZ` are taken as data together with the
equations they satisfy, as in
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_comp`, so that a consumer holding those
equations up to the commutativity of another square can apply the lemmas without transporting
along associativity.

No hypothesis is placed on `j` or `ι`: the statement is the pseudofunctoriality of the pullback
read on relative differentials, not an étale-invariance statement.

## References

* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV), the canonical map on
  relative differentials of a commutative square and its uniqueness.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Hom

open Stacks.ConormalSequenceRight

variable {Z W X S : Scheme.{u}}

/-- The unit of the pullback--pushforward adjunction is natural, read on sections. -/
private theorem pullback_map_unit_app_apply (j : Z ⟶ W) {F G : W.Modules} (φ : F ⟶ G)
    (V : W.Opens) (x : Γ(F, V)) :
    ((Scheme.Modules.pullback j).map φ).app (j ⁻¹ᵁ V)
        (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app F).app V x) =
      ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app G).app V (φ.app V x) := by
  have h := congrArg (fun ψ => Scheme.Modules.Hom.app ψ V)
    ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.naturality φ)
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app] at h
  exact (ConcreteCategory.congr_hom h x).symm

/-- **The canonical maps on relative differentials of two squares stacked along the source
compose to the canonical map of the outer square**, read on the universal differential of a
local section of `𝒪_X` pulled back to `Z`.  The iterated pullback is identified with the
pullback along the composite by `AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
theorem relativeDifferentialsMap_app_pullbackComp_inv_unit (j : Z ⟶ W) (ι : W ⟶ X) (p : X ⟶ S)
    (qW : W ⟶ S) (qZ : Z ⟶ S) (hcommW : ι ≫ p = qW ≫ 𝟙 S) (hcommZ : j ≫ qW = qZ ≫ 𝟙 S)
    (U : X.Opens) (s : Γ(X, U)) :
    (relativeDifferentialsMap j qW qZ (𝟙 S) hcommZ).app ((j ≫ ι) ⁻¹ᵁ U)
      (((Scheme.Modules.pullback j).map
          (relativeDifferentialsMap ι p qW (𝟙 S) hcommW)).app ((j ≫ ι) ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackComp j ι).inv.app (relativeDifferentials p)).app
          ((j ≫ ι) ⁻¹ᵁ U)
          ((((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ ι)).unit.app
              (relativeDifferentials p)).app U)
            ((universalRelativeDerivation p).d s)))) =
      (universalRelativeDerivation qZ).d (((j ≫ ι).app U).hom s) := by
  have h := congrArg (fun ψ => Scheme.Modules.Hom.app ψ U)
    (unit_comp_pullbackComp_inv j ι (relativeDifferentials p))
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app] at h
  have hm : ((Scheme.Modules.pullbackComp j ι).inv.app (relativeDifferentials p)).app
        ((j ≫ ι) ⁻¹ᵁ U)
      ((((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ ι)).unit.app
          (relativeDifferentials p)).app U) ((universalRelativeDerivation p).d s)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
          ((Scheme.Modules.pullback ι).obj (relativeDifferentials p))).app (ι ⁻¹ᵁ U)
        ((((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app
            (relativeDifferentials p)).app U) ((universalRelativeDerivation p).d s)) := by
    have h2 := ConcreteCategory.congr_hom h ((universalRelativeDerivation p).d s)
    exact h2
  have hA := relativeDifferentialsMap_app_d (f := ι) (p := p) (p' := qW) (𝟙 S) hcommW U s
  rw [Adjunction.homEquiv_unit] at hA
  have hC := relativeDifferentialsMap_app_d (f := j) (p := qW) (p' := qZ) (𝟙 S) hcommZ
    (ι ⁻¹ᵁ U) ((ι.app U).hom s)
  rw [Adjunction.homEquiv_unit] at hC
  refine Eq.trans (congrArg
    (fun y => (relativeDifferentialsMap j qW qZ (𝟙 S) hcommZ).app ((j ≫ ι) ⁻¹ᵁ U)
      (((Scheme.Modules.pullback j).map
          (relativeDifferentialsMap ι p qW (𝟙 S) hcommW)).app ((j ≫ ι) ⁻¹ᵁ U) y)) hm) ?_
  refine Eq.trans (congrArg
    (fun y => (relativeDifferentialsMap j qW qZ (𝟙 S) hcommZ).app ((j ≫ ι) ⁻¹ᵁ U) y)
    (pullback_map_unit_app_apply j
      (relativeDifferentialsMap ι p qW (𝟙 S) hcommW) (ι ⁻¹ᵁ U) _)) ?_
  refine Eq.trans (congrArg
    (fun y => (relativeDifferentialsMap j qW qZ (𝟙 S) hcommZ).app ((j ≫ ι) ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
          (relativeDifferentials qW)).app (ι ⁻¹ᵁ U) y)) hA) ?_
  exact Eq.trans hC rfl

/-- **The canonical maps on relative differentials of two squares stacked along the source
compose to the canonical map of the outer square**, as an equality of morphisms of sheaves of
modules.  The uniqueness of Stacks 01UV turns the identity on universal differentials into this
one. -/
theorem pullbackComp_inv_comp_relativeDifferentialsMap (j : Z ⟶ W) (ι : W ⟶ X) (p : X ⟶ S)
    (qW : W ⟶ S) (qZ : Z ⟶ S) (hcommW : ι ≫ p = qW ≫ 𝟙 S) (hcommZ : j ≫ qW = qZ ≫ 𝟙 S)
    (hcomm : (j ≫ ι) ≫ p = qZ ≫ 𝟙 S) :
    (Scheme.Modules.pullbackComp j ι).inv.app (relativeDifferentials p) ≫
        ((Scheme.Modules.pullback j).map
            (relativeDifferentialsMap ι p qW (𝟙 S) hcommW) ≫
          relativeDifferentialsMap j qW qZ (𝟙 S) hcommZ) =
      relativeDifferentialsMap (j ≫ ι) p qZ (𝟙 S) hcomm := by
  refine (isRelativeDifferentialsMap_iff_eq (j ≫ ι) p qZ (𝟙 S) hcomm _).mp ?_
  intro U s
  rw [Adjunction.homEquiv_unit]
  exact relativeDifferentialsMap_app_pullbackComp_inv_unit j ι p qW qZ hcommW hcommZ U s

/-- **The composition law in the form the sections map of Stacks 03DS uses it**: the comparison
of iterated pullbacks followed by the canonical map of the outer square is the pullback of the
canonical map of the inner square followed by the canonical map of the remaining one.  The outer
source morphism is given as data with the equation `j ≫ ι = i` it satisfies, which is the shape
`AlgebraicGeometry.pullbackSectionsMap` is built in. -/
theorem pullbackComp_hom_comp_relativeDifferentialsMap (j : Z ⟶ W) (ι : W ⟶ X) (i : Z ⟶ X)
    (hi : j ≫ ι = i) (p : X ⟶ S) (qW : W ⟶ S) (qZ : Z ⟶ S)
    (hcommW : ι ≫ p = qW ≫ 𝟙 S) (hcommZ : j ≫ qW = qZ ≫ 𝟙 S)
    (hcomm : i ≫ p = qZ ≫ 𝟙 S) :
    (Scheme.Modules.pullbackComp j ι).hom.app (relativeDifferentials p) ≫
        (Scheme.Modules.pullbackCongr hi).hom.app (relativeDifferentials p) ≫
          relativeDifferentialsMap i p qZ (𝟙 S) hcomm =
      (Scheme.Modules.pullback j).map
          (relativeDifferentialsMap ι p qW (𝟙 S) hcommW) ≫
        relativeDifferentialsMap j qW qZ (𝟙 S) hcommZ := by
  subst hi
  rw [pullbackCongr_rfl_hom_app, Category.id_comp,
    ← pullbackComp_inv_comp_relativeDifferentialsMap j ι p qW qZ hcommW hcommZ hcomm,
    ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- **The composition law read on global sections of the iterated pullback.**  This is
`AlgebraicGeometry.Scheme.Hom.pullbackComp_hom_comp_relativeDifferentialsMap` applied to the
image of a global section under the unit of the pullback--pushforward adjunction, combined with
the defining property of the canonical map on the universal differential. -/
theorem relativeDifferentialsMap_app_top_pullbackComp (j : Z ⟶ W) (ι : W ⟶ X) (i : Z ⟶ X)
    (hi : j ≫ ι = i) (p : X ⟶ S)
    (z : Γ((Scheme.Modules.pullback ι).obj (relativeDifferentials p), ⊤)) (a : Γ(W, ⊤))
    (hz : (relativeDifferentialsMap ι p (ι ≫ p) (𝟙 S) (Category.comp_id _).symm).app ⊤ z =
      (universalRelativeDerivation (ι ≫ p)).d (X := op (⊤ : W.Opens)) a) :
    (relativeDifferentialsMap i p (i ≫ p) (𝟙 S) (Category.comp_id _).symm).app ⊤
        (((Scheme.Modules.pullbackComp j ι).hom.app (relativeDifferentials p) ≫
            (Scheme.Modules.pullbackCongr hi).hom.app (relativeDifferentials p)).app ⊤
          (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
              ((Scheme.Modules.pullback ι).obj (relativeDifferentials p))).app ⊤ z)) =
      (universalRelativeDerivation (i ≫ p)).d (X := op (⊤ : Z.Opens)) (j.appTop a) := by
  have hcommZ : j ≫ (ι ≫ p) = (i ≫ p) ≫ 𝟙 S := by
    rw [Category.comp_id, ← Category.assoc, hi]
  have hstep : ∀ w, (relativeDifferentialsMap i p (i ≫ p) (𝟙 S)
          (Category.comp_id _).symm).app ⊤
        (((Scheme.Modules.pullbackComp j ι).hom.app (relativeDifferentials p) ≫
            (Scheme.Modules.pullbackCongr hi).hom.app (relativeDifferentials p)).app ⊤ w) =
      (relativeDifferentialsMap j (ι ≫ p) (i ≫ p) (𝟙 S) hcommZ).app ⊤
        (((Scheme.Modules.pullback j).map
            (relativeDifferentialsMap ι p (ι ≫ p) (𝟙 S)
              (Category.comp_id _).symm)).app ⊤ w) := by
    intro w
    have h := congrArg (fun ψ => Scheme.Modules.Hom.app ψ (⊤ : Z.Opens))
      (pullbackComp_hom_comp_relativeDifferentialsMap j ι i hi p (ι ≫ p) (i ≫ p)
        (Category.comp_id _).symm hcommZ (Category.comp_id _).symm)
    simp only [Scheme.Modules.Hom.comp_app] at h
    have h2 := ConcreteCategory.congr_hom h w
    exact h2
  have hd := relativeDifferentialsMap_app_d (f := j) (p := ι ≫ p) (p' := i ≫ p) (𝟙 S)
    hcommZ ⊤ a
  rw [Adjunction.homEquiv_unit] at hd
  refine Eq.trans (hstep _) ?_
  refine Eq.trans (congrArg
    (fun y => (relativeDifferentialsMap j (ι ≫ p) (i ≫ p) (𝟙 S) hcommZ).app ⊤ y)
    (pullback_map_unit_app_apply j _ _ z)) ?_
  refine Eq.trans (congrArg
    (fun y => (relativeDifferentialsMap j (ι ≫ p) (i ≫ p) (𝟙 S) hcommZ).app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
          (relativeDifferentials (ι ≫ p))).app ⊤ y)) hz) ?_
  exact hd

/-! ### The map on global sections -/

/-- The map on global sections of Stacks 03DS, unfolded: the unit of the pullback--pushforward
adjunction, the comparison of iterated pullbacks, and the restriction to the top open. -/
theorem _root_.AlgebraicGeometry.pullbackSectionsMap_apply_eqToHom {S : Scheme.{u}}
    (F : S.Modules) {T T' : Over S} (g : T' ⟶ T)
    (htop : (⊤ : T'.left.Opens) = g.left ⁻¹ᵁ ⊤)
    (z : Γ((Scheme.Modules.pullback T.hom).obj F, ⊤)) :
    pullbackSectionsMap F g z =
      ((Scheme.Modules.pullback T'.hom).obj F).presheaf.map (eqToHom htop).op
        ((((Scheme.Modules.pullbackComp g.left T.hom).hom.app F ≫
            (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F).app (g.left ⁻¹ᵁ ⊤))
          (((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
            ((Scheme.Modules.pullback T.hom).obj F)).app ⊤ z)) := rfl

/-- The map on global sections of Stacks 03DS is the unit of the pullback--pushforward
adjunction followed by the comparison of iterated pullbacks.  The restriction to the top open
that `AlgebraicGeometry.pullbackSectionsMap` carries is the identity, the preimage of the top
open being the top open. -/
theorem _root_.AlgebraicGeometry.pullbackSectionsMap_apply {S : Scheme.{u}} (F : S.Modules)
    {T T' : Over S} (g : T' ⟶ T)
    (z : Γ((Scheme.Modules.pullback T.hom).obj F, ⊤)) :
    pullbackSectionsMap F g z =
      (((Scheme.Modules.pullbackComp g.left T.hom).hom.app F ≫
          (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F).app ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
          ((Scheme.Modules.pullback T.hom).obj F)).app ⊤ z) := by
  rw [AlgebraicGeometry.pullbackSectionsMap_apply_eqToHom F g rfl z]
  have hid : ((Scheme.Modules.pullback T'.hom).obj F).presheaf.map
      (eqToHom (rfl : (⊤ : T'.left.Opens) = g.left ⁻¹ᵁ ⊤)).op = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  exact Eq.trans (ConcreteCategory.congr_hom hid _) rfl

/-- **The composition law on global sections.**  Let `z` be a global section of `T.hom^*Ω_{X/S}`
whose image under the canonical map of Stacks 01UV is the universal differential of a global
function `a` on `T`.  Then the restriction of `z` along a morphism `g : T' ⟶ T` of schemes over
`X`, taken by the map on global sections of Stacks 03DS, has canonical image the universal
differential of the pullback of `a` to `T'`.

This is the compatibility a derivation valued in the sections of a pullback of `Ω_{X/S}` needs
in order to be natural. -/
theorem relativeDifferentialsMap_app_top_pullbackSectionsMap (p : X ⟶ S) {T T' : Over X}
    (g : T' ⟶ T) (z : Γ((Scheme.Modules.pullback T.hom).obj (relativeDifferentials p), ⊤))
    (a : Γ(T.left, ⊤))
    (hz : (relativeDifferentialsMap T.hom p (T.hom ≫ p) (𝟙 S)
          (Category.comp_id _).symm).app ⊤ z =
      (universalRelativeDerivation (T.hom ≫ p)).d (X := op (⊤ : T.left.Opens)) a) :
    (relativeDifferentialsMap T'.hom p (T'.hom ≫ p) (𝟙 S) (Category.comp_id _).symm).app ⊤
        (pullbackSectionsMap (relativeDifferentials p) g z) =
      (universalRelativeDerivation (T'.hom ≫ p)).d (X := op (⊤ : T'.left.Opens))
        (g.left.appTop a) := by
  rw [AlgebraicGeometry.pullbackSectionsMap_apply (relativeDifferentials p) g z]
  exact relativeDifferentialsMap_app_top_pullbackComp g.left T.hom T'.hom (Over.w g) p z a hz

end AlgebraicGeometry.Scheme.Hom

end
