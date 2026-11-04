module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.NatIsoCoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RefinedDatumAssembly

/-!
# Pseudonaturality of the associated-module comparison from a cocycle and a square

`AlgebraicGeometry.BigFppfOver.LocalComparisonPseudonatural` says that the comparison isomorphism
`AlgebraicGeometry.BigFppfOver.localAssociatedModuleComparison` is compatible with composition in
the big fppf site. This file derives it from two coherences between functors:

* the cocycle condition among the three instances of
  `AlgebraicGeometry.BigFppfOver.objRestrictComp`, which is
  `AlgebraicGeometry.BigFppfOver.objRestrictComp_cocycle`; and
* the square relating `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` at a
  morphism, at a second morphism and at their composite,
  `AlgebraicGeometry.BigFppfOver.NatIsoCompSquare`, which is taken as a hypothesis.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.NatIsoCompSquare`: the square for
  `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` at one morphism of the big
  fppf site over a base, as a proposition.

## Main results

* `Stacks.comparison_comp_of_cocycle_of_square`: for functors and comparison isomorphisms
  between abstract categories satisfying a cocycle condition and a square, the two-step
  comparison of a module with a restriction agrees with the one-step comparison.
* `AlgebraicGeometry.pullModComp_symm_app`: the comparison of iterated pullbacks of modules on
  schemes supplied by `AlgebraicGeometry.modulePullbackPseudofunctor` is the component of
  `AlgebraicGeometry.Scheme.Modules.pullbackComp` followed by the congruence at the
  factorization.
* `AlgebraicGeometry.BigFppfOver.natIsoCompSquare_of_conjugate`:
  `AlgebraicGeometry.BigFppfOver.NatIsoCompSquare` holds as soon as the corresponding identity
  between the mates does.
* `AlgebraicGeometry.BigFppfOver.localComparisonPseudonatural_of_natIsoCompSquare`: if
  `AlgebraicGeometry.BigFppfOver.NatIsoCompSquare` holds at every morphism over every base, then
  `AlgebraicGeometry.BigFppfOver.LocalComparisonPseudonatural` holds.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u

namespace Stacks

/-- A two-step comparison assembled out of a cocycle and a square. Let `p₀`, `p` and `p₁` be
functors with `μ : p₀ ⋙ p ≅ p₁`, let `aX`, `aZ` and `aZ'` be three further functors, and let `P`,
`A`, `D`, `Q`, `L`, `C` be functors with comparison isomorphisms `α : P ⋙ Q ≅ A`, `β : A ⋙ L ≅ D`,
`γ : Q ⋙ L ≅ C` and `δ : P ⋙ C ≅ D` and `N₀ : p₀ ⋙ aZ ≅ aX ⋙ Q`, `N : p ⋙ aZ' ≅ aZ ⋙ L`,
`N₁ : p₁ ⋙ aZ' ≅ aX ⋙ C`. Suppose the four comparisons `α`, `β`, `γ`, `δ` satisfy the cocycle
identity, and suppose the square holds: contracting `μ`, then comparing with `N` and with `N₀` and
contracting by `γ`, is `N₁`. Then for every `F`, every `G` and every `e : aX.obj F ≅ P.obj G`,
transporting `e` twice — first to a comparison for `aZ.obj (p₀.obj F)` and then to one for
`aZ'.obj (p.obj (p₀.obj F))` — gives the comparison obtained by transporting it once along the
contracted data. -/
public theorem comparison_comp_of_cocycle_of_square
    {𝔛 : Type u₁} [Category.{v₁} 𝔛] {𝔷 : Type u₂} [Category.{v₂} 𝔷]
    {𝔷' : Type u₃} [Category.{v₃} 𝔷'] {𝔄 : Type u₄} [Category.{v₄} 𝔄]
    {𝔅 : Type u₅} [Category.{v₅} 𝔅] {ℭ : Type u₆} [Category.{v₆} ℭ]
    {𝔇 : Type u₇} [Category.{v₇} 𝔇]
    {p₀ : 𝔛 ⥤ 𝔷} {p : 𝔷 ⥤ 𝔷'} {p₁ : 𝔛 ⥤ 𝔷'}
    {aX : 𝔛 ⥤ 𝔅} {aZ : 𝔷 ⥤ ℭ} {aZ' : 𝔷' ⥤ 𝔇}
    {P : 𝔄 ⥤ 𝔅} {A : 𝔄 ⥤ ℭ} {D : 𝔄 ⥤ 𝔇} {Q : 𝔅 ⥤ ℭ} {L : ℭ ⥤ 𝔇} {C : 𝔅 ⥤ 𝔇}
    (μ : p₀ ⋙ p ≅ p₁) (α : P ⋙ Q ≅ A) (β : A ⋙ L ≅ D) (γ : Q ⋙ L ≅ C) (δ : P ⋙ C ≅ D)
    (N₀ : p₀ ⋙ aZ ≅ aX ⋙ Q) (N : p ⋙ aZ' ≅ aZ ⋙ L) (N₁ : p₁ ⋙ aZ' ≅ aX ⋙ C)
    (hcoc : (Functor.associator P Q L).symm ≪≫ Functor.isoWhiskerRight α L ≪≫ β =
      Functor.isoWhiskerLeft P γ ≪≫ δ)
    (hsq : (Functor.isoWhiskerRight μ aZ').symm ≪≫ Functor.associator p₀ p aZ' ≪≫
        Functor.isoWhiskerLeft p₀ N ≪≫ (Functor.associator p₀ aZ L).symm ≪≫
        Functor.isoWhiskerRight N₀ L ≪≫ Functor.associator aX Q L ≪≫
        Functor.isoWhiskerLeft aX γ = N₁)
    (F : 𝔛) (G : 𝔄) (e : aX.obj F ≅ P.obj G) :
    N.app (p₀.obj F) ≪≫ L.mapIso (N₀.app F ≪≫ Q.mapIso e ≪≫ α.app G) ≪≫ β.app G =
      aZ'.mapIso (μ.app F) ≪≫ N₁.app F ≪≫ C.mapIso e ≪≫ δ.app G := by
  have hc := NatTrans.congr_app (congrArg Iso.hom hcoc) G
  have hs := NatTrans.congr_app (congrArg Iso.hom hsq) F
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.id_comp] at hc hs
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [hc, ← Functor.comp_map, γ.hom.naturality_assoc e.hom, ← hs]
  simp [← Functor.map_comp_assoc]

end Stacks

namespace AlgebraicGeometry

/-- The comparison of iterated pullbacks of the pullback pseudofunctor, read on the pullback
functors: for `a ≫ b = ab` morphisms of schemes, the inverse of
`AlgebraicGeometry.pullModComp` at a sheaf of modules `M` is the component at `M` of
`AlgebraicGeometry.Scheme.Modules.pullbackComp` followed by the congruence isomorphism of the
factorization. -/
public theorem pullModComp_symm_app {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (ab : X ⟶ Z)
    (hab : a ≫ b = ab) (M : Z.Modules) :
    (pullModComp a b ab hab M).symm =
      (Scheme.Modules.pullbackComp a b ≪≫ Scheme.Modules.pullbackCongr hab).app M := by
  subst hab
  rfl

end AlgebraicGeometry

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The square, as a proposition -/

/-- The comparison `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` is compatible
with composition of objects of the big fppf site, as a proposition, at one morphism `g : W' ⟶ W` of
the big fppf category over a base `X`. An `𝒪_X`-module can be compared with the restriction of its
associated module to the big fppf site of the scheme of `W'` in two ways: in one step, by
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` at `W'`, or in two, by that
comparison at `W` and then at `CategoryTheory.Over.mk g.left`, the iterated pullback of modules on
schemes being contracted by `AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`AlgebraicGeometry.BigFppfOver.objHom_comp` and the iterated restriction by
`AlgebraicGeometry.BigFppfOver.objRestrictComp`. This says the two agree. -/
public abbrev NatIsoCompSquare {X : Scheme.{u}} (hX : B.Contains X)
    {W W' : BigFppfOver B X hX} (g : W' ⟶ W) : Prop :=
  (Functor.isoWhiskerRight
        (Scheme.Modules.pullbackComp
            (objHom B (objScheme B X hX W) (contains_objScheme B X hX W) (Over.mk g.left))
            (objHom B X hX W) ≪≫
          Scheme.Modules.pullbackCongr (objHom_comp B X hX g))
        (associatedModule B (objScheme B X hX W') (contains_objScheme B X hX W'))).symm ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
            (associatedModuleObjRestrictNatIso B (objScheme B X hX W)
              (contains_objScheme B X hX W) (Over.mk g.left)) ≪≫
          (Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight (associatedModuleObjRestrictNatIso B X hX W) _ ≪≫
              Functor.associator _ _ _ ≪≫
                Functor.isoWhiskerLeft _ (objRestrictComp B X hX g) =
    associatedModuleObjRestrictNatIso B X hX W'

/-- `AlgebraicGeometry.BigFppfOver.NatIsoCompSquare B hX g` holds as soon as the identity between
the mates of its two sides, with respect to an adjunction `adj` for restriction to `W'`, does. -/
public theorem natIsoCompSquare_of_conjugate {X : Scheme.{u}} (hX : B.Contains X)
    {W W' : BigFppfOver B X hX} (g : W' ⟶ W)
    {R : SheafOfModules.{u}
        (structureSheaf B (objScheme B X hX W') (contains_objScheme B X hX W')) ⥤
      SheafOfModules.{u} (structureSheaf B X hX)} (adj : objRestrict B X hX W' ⊣ R)
    (h : conjugateIsoEquiv ((associatedModuleAdjunction B X hX).comp adj)
          ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B X hX W')).comp
            (associatedModuleAdjunction B (objScheme B X hX W')
              (contains_objScheme B X hX W')))
          ((Functor.isoWhiskerRight
                (Scheme.Modules.pullbackComp
                    (objHom B (objScheme B X hX W) (contains_objScheme B X hX W)
                      (Over.mk g.left))
                    (objHom B X hX W) ≪≫
                  Scheme.Modules.pullbackCongr (objHom_comp B X hX g))
                (associatedModule B (objScheme B X hX W')
                  (contains_objScheme B X hX W'))).symm ≪≫
            Functor.associator _ _ _ ≪≫
              Functor.isoWhiskerLeft _
                  (associatedModuleObjRestrictNatIso B (objScheme B X hX W)
                    (contains_objScheme B X hX W) (Over.mk g.left)) ≪≫
                (Functor.associator _ _ _).symm ≪≫
                  Functor.isoWhiskerRight (associatedModuleObjRestrictNatIso B X hX W) _ ≪≫
                    Functor.associator _ _ _ ≪≫
                      Functor.isoWhiskerLeft _ (objRestrictComp B X hX g)) =
        conjugateIsoEquiv ((associatedModuleAdjunction B X hX).comp adj)
          ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B X hX W')).comp
            (associatedModuleAdjunction B (objScheme B X hX W')
              (contains_objScheme B X hX W')))
          (associatedModuleObjRestrictNatIso B X hX W')) :
    NatIsoCompSquare B hX g :=
  associatedModuleObjRestrictNatIso_comp_of_conjugate B X hX g adj h

/-! ### Pseudonaturality of the comparison -/

/-- If the square `AlgebraicGeometry.BigFppfOver.NatIsoCompSquare` holds at every morphism of
the big fppf site over every base (the hypothesis `hsq`), then the comparison isomorphism
`AlgebraicGeometry.BigFppfOver.localAssociatedModuleComparison` is pseudonatural:
`AlgebraicGeometry.BigFppfOver.LocalComparisonPseudonatural B S hS G` holds for every module
`G`. -/
public theorem localComparisonPseudonatural_of_natIsoCompSquare
    (hsq : ∀ {X : Scheme.{u}} (hX : B.Contains X) {W W' : BigFppfOver B X hX} (g : W' ⟶ W),
      NatIsoCompSquare B hX g)
    (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    LocalComparisonPseudonatural B S hS G := by
  intro T Z Z' g g₀ F e
  rw [pullModComp_symm_app]
  exact Stacks.comparison_comp_of_cocycle_of_square
    (Scheme.Modules.pullbackComp
        (objHom B (objScheme B S hS Z) (contains_objScheme B S hS Z) (Over.mk g.left))
        (objHom B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g₀.left)) ≪≫
      Scheme.Modules.pullbackCongr (objHom_comp B (objScheme B S hS T)
        (contains_objScheme B S hS T) (Over.homMk (U := Over.mk (g ≫ g₀).left)
          (V := Over.mk g₀.left) g.left rfl)))
    (objRestrictComp B S hS g₀) (objRestrictComp B S hS g)
    (objRestrictComp B (objScheme B S hS T) (contains_objScheme B S hS T)
      (Over.homMk (U := Over.mk (g ≫ g₀).left) (V := Over.mk g₀.left) g.left rfl))
    (objRestrictComp B S hS (g ≫ g₀))
    (associatedModuleObjRestrictNatIso B (objScheme B S hS T) (contains_objScheme B S hS T)
      (Over.mk g₀.left))
    (associatedModuleObjRestrictNatIso B (objScheme B S hS Z) (contains_objScheme B S hS Z)
      (Over.mk g.left))
    (associatedModuleObjRestrictNatIso B (objScheme B S hS T) (contains_objScheme B S hS T)
      (Over.mk (g ≫ g₀).left))
    (objRestrictComp_cocycle B S hS g₀ g)
    (hsq (contains_objScheme B S hS T) (Over.homMk (U := Over.mk (g ≫ g₀).left)
      (V := Over.mk g₀.left) g.left rfl))
    F G e

end AlgebraicGeometry.BigFppfOver

end
