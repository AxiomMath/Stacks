module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentPullback

/-!
# Naturality of the comparison of inverse images on a representable algebraic space

Let `B` be a big fppf site containing a scheme `S` and let `g : T' ⟶ T` be a morphism of the big
fppf category over `S`.  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`
identifies the inverse image of Stacks 03LU, along the morphism of representable algebraic spaces
represented by `g`, of the `𝒪`-module that a Zariski module on the scheme underlying `T` becomes
with the `𝒪`-module that its Zariski pullback becomes.  This file shows that this identification
is **natural in the module**.

## Main results

* `AlgebraicGeometry.Space.conjugateComparison_naturality`: for equivalences `E`, `E'`, functors
  `P`, `Q` and a comparison `ρ : P ⋙ E'.inverse ≅ E.inverse ⋙ Q`, the morphisms
  `P(E M) ⟶ E'(Q M)` obtained by conjugating `ρ` with the unit of `E` and the counit of `E'` are
  natural in `M`.
* `AlgebraicGeometry.Space.conjugateComparison_comp_inv_naturality`: the same composed with a
  second comparison, read on the inverses.
* `AlgebraicGeometry.Space.representedModuleObjPullbackIso_hom_naturality`:
  `AlgebraicGeometry.Space.representedModuleObjPullbackIso` is natural in the module.
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_inv_naturality`: the inverse of
  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` is natural in the Zariski
  module.

## Implementation notes

The general lemmas take the family of isomorphisms as a parameter `θ` and its defining equation,
an equation of isomorphisms, as a hypothesis.  At a representable morphism these equations are
`AlgebraicGeometry.Space.representedModuleObjPullbackIso_eq` and
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_eq_yoneda`, both `rfl`; stated
between the forward morphisms instead, they exhaust the heartbeat budget at `whnf`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 06CB](https://stacks.math.columbia.edu/tag/06CB)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-! ### The content, at arbitrary equivalences and functors -/

/-- **Conjugating a comparison of two functors by the unit of one equivalence and the counit of
another is natural.**  Let `E : A ≌ B` and `E' : A' ≌ B'` be equivalences, let `P : B ⥤ B'` and
`Q : A ⥤ A'`, and let `ρ : P ⋙ E'.inverse ≅ E.inverse ⋙ Q`.  A family `θ` of isomorphisms
`P(E M) ≅ E'(Q M)` which is the composite

```
P(E M) ⟶ E'(E'⁻¹(P(E M))) --ρ--> E'(Q(E⁻¹(E M))) ⟶ E'(Q M)
```

is natural in `M`. -/
theorem conjugateComparison_naturality {A B A' B' : Type*}
    [Category A] [Category B] [Category A'] [Category B']
    (E : A ≌ B) (E' : A' ≌ B') (P : B ⥤ B') (Q : A ⥤ A')
    (ρ : P ⋙ E'.inverse ≅ E.inverse ⋙ Q)
    (θ : ∀ M : A, P.obj (E.functor.obj M) ≅ E'.functor.obj (Q.obj M))
    (hθ : ∀ M : A, θ M =
      (E'.counitIso.app (P.obj (E.functor.obj M))).symm ≪≫
        E'.functor.mapIso (ρ.app (E.functor.obj M) ≪≫ Q.mapIso (E.unitIso.app M).symm))
    {M N : A} (φ : M ⟶ N) :
    P.map (E.functor.map φ) ≫ (θ N).hom = (θ M).hom ≫ E'.functor.map (Q.map φ) := by
  have h1 : P.map (E.functor.map φ) ≫ (E'.counitIso.app (P.obj (E.functor.obj N))).inv =
      (E'.counitIso.app (P.obj (E.functor.obj M))).inv ≫
        E'.functor.map (E'.inverse.map (P.map (E.functor.map φ))) :=
    E'.counitIso.inv.naturality (P.map (E.functor.map φ))
  have h2 : E'.inverse.map (P.map (E.functor.map φ)) ≫ (ρ.app (E.functor.obj N)).hom =
      (ρ.app (E.functor.obj M)).hom ≫ Q.map (E.inverse.map (E.functor.map φ)) :=
    ρ.hom.naturality (E.functor.map φ)
  have h3 : E.inverse.map (E.functor.map φ) ≫ (E.unitIso.app N).inv =
      (E.unitIso.app M).inv ≫ φ :=
    E.unitIso.inv.naturality φ
  rw [hθ N, hθ M]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, h1, Category.assoc, ← E'.functor.map_comp, ← Category.assoc, h2,
    Category.assoc, ← Q.map_comp, h3, Q.map_comp, ← Category.assoc, E'.functor.map_comp,
    ← Category.assoc]

/-- **The conjugated comparison composed with a second comparison, read on the inverses, is
natural.**  To the data of `AlgebraicGeometry.Space.conjugateComparison_naturality` add functors
`F : C ⥤ A`, `F' : C' ⥤ A'`, `R : C ⥤ C'` and a comparison `τ : R ⋙ F' ≅ F ⋙ Q`.  A family `Θ`
of isomorphisms `P(E(F X)) ≅ E'(F'(R X))` which is `θ` at `F X` followed by `E'` of the inverse
of `τ`, read on the inverses, makes the square with `E'(F'(R φ))` and `P(E(F φ))` commute. -/
theorem conjugateComparison_comp_inv_naturality {A B A' B' C C' : Type*}
    [Category A] [Category B] [Category A'] [Category B'] [Category C] [Category C']
    (E : A ≌ B) (E' : A' ≌ B') (P : B ⥤ B') (Q : A ⥤ A')
    (ρ : P ⋙ E'.inverse ≅ E.inverse ⋙ Q)
    (θ : ∀ M : A, P.obj (E.functor.obj M) ≅ E'.functor.obj (Q.obj M))
    (hθ : ∀ M : A, θ M =
      (E'.counitIso.app (P.obj (E.functor.obj M))).symm ≪≫
        E'.functor.mapIso (ρ.app (E.functor.obj M) ≪≫ Q.mapIso (E.unitIso.app M).symm))
    (F : C ⥤ A) (F' : C' ⥤ A') (R : C ⥤ C') (τ : R ⋙ F' ≅ F ⋙ Q)
    (Θ : ∀ X : C, P.obj (E.functor.obj (F.obj X)) ≅ E'.functor.obj (F'.obj (R.obj X)))
    (hΘ : ∀ X : C, Θ X = θ (F.obj X) ≪≫ E'.functor.mapIso (τ.app X).symm)
    {X Y : C} (φ : X ⟶ Y) :
    E'.functor.map (F'.map (R.map φ)) ≫ (Θ Y).inv =
      (Θ X).inv ≫ P.map (E.functor.map (F.map φ)) := by
  have h4 : Q.map (F.map φ) ≫ (τ.app Y).inv = (τ.app X).inv ≫ F'.map (R.map φ) :=
    τ.inv.naturality φ
  have hom : P.map (E.functor.map (F.map φ)) ≫ (Θ Y).hom =
      (Θ X).hom ≫ E'.functor.map (F'.map (R.map φ)) := by
    rw [hΘ X, hΘ Y]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [← Category.assoc, conjugateComparison_naturality E E' P Q ρ θ hθ (F.map φ),
      Category.assoc, ← E'.functor.map_comp, h4, E'.functor.map_comp, ← Category.assoc]
  rw [Iso.comp_inv_eq, Category.assoc, hom, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-! ### The comparison at a representable morphism -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

/-- **The defining equation of `AlgebraicGeometry.Space.representedModuleObjPullbackIso`**: it is
the counit of the identification of module categories at `T'`, the component of
`AlgebraicGeometry.Space.representedModulePullbackIso` and the unit of the identification at `T`,
conjugated. -/
theorem representedModuleObjPullbackIso_eq
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS T)) :
    representedModuleObjPullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g) M =
      ((representedSmallEtaleModuleEquivalence B S hS T').counitIso.app
            ((modulePullback B S hS (representedSpaceMap B S hS g)).obj
              ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj M))).symm ≪≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.mapIso
          ((representedModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)).app
              ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj M) ≪≫
            (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)).mapIso
              ((representedSmallEtaleModuleEquivalence B S hS T).unitIso.app M).symm) :=
  rfl

/-- **The inverse image of modules along a morphism of representable algebraic spaces is compared
with the small étale pullback of the underlying morphism of schemes naturally in the module.**
This is the naturality of `AlgebraicGeometry.Space.representedModuleObjPullbackIso` in the
module. -/
theorem representedModuleObjPullbackIso_hom_naturality
    {M N : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS T)} (φ : M ⟶ N) :
    (modulePullback B S hS (representedSpaceMap B S hS g)).map
          ((representedSmallEtaleModuleEquivalence B S hS T).functor.map φ) ≫
        (representedModuleObjPullbackIso B S hS g
            (relativelyRepresentable_yoneda_map B S hS g) N).hom =
      (representedModuleObjPullbackIso B S hS g
          (relativelyRepresentable_yoneda_map B S hS g) M).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.map
          ((SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)).map φ) :=
  conjugateComparison_naturality (representedSmallEtaleModuleEquivalence B S hS T)
    (representedSmallEtaleModuleEquivalence B S hS T')
    (modulePullback B S hS (representedSpaceMap B S hS g))
    (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g))
    (representedModulePullbackIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g)) (representedModuleObjPullbackIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g))
    (representedModuleObjPullbackIso_eq B S hS g) φ

/-- **The defining equation of
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`**: it is
`AlgebraicGeometry.Space.representedModuleObjPullbackIso` at the associated module followed by
the inverse of the component of
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`, whose components are the
`AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso`. -/
theorem representedAssociatedModulePullbackIso_eq_yoneda
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T).Modules) :
    representedAssociatedModulePullbackIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g) 𝓕 =
      representedModuleObjPullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj 𝓕) ≪≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.mapIso
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso
            (associatedBigEtaleSite B) g.left).app 𝓕).symm :=
  rfl

/-- **The identification of the inverse image along a morphism of representable algebraic spaces
with the Zariski pullback is natural in the module**, read on the inverses of
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`. -/
theorem representedAssociatedModulePullbackIso_inv_naturality
    {𝓕 𝓖 : ((BigFppfOver.toScheme B S hS).obj T).Modules} (φ : 𝓕 ⟶ 𝓖) :
    (representedSmallEtaleModuleEquivalence B S hS T').functor.map
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
            ((Scheme.Modules.pullback (B.inclusion.map g.left)).map φ)) ≫
        (representedAssociatedModulePullbackIso B S hS g
            (relativelyRepresentable_yoneda_map B S hS g) 𝓖).inv =
      (representedAssociatedModulePullbackIso B S hS g
          (relativelyRepresentable_yoneda_map B S hS g) 𝓕).inv ≫
        (modulePullback B S hS (representedSpaceMap B S hS g)).map
          ((representedSmallEtaleModuleEquivalence B S hS T).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map φ)) :=
  conjugateComparison_comp_inv_naturality (representedSmallEtaleModuleEquivalence B S hS T)
    (representedSmallEtaleModuleEquivalence B S hS T')
    (modulePullback B S hS (representedSpaceMap B S hS g))
    (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g))
    (representedModulePullbackIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g)) (representedModuleObjPullbackIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g))
    (representedModuleObjPullbackIso_eq B S hS g)
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property)
    (Scheme.Modules.pullback (B.inclusion.map g.left))
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso
      (associatedBigEtaleSite B) g.left)
    (representedAssociatedModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g))
    (representedAssociatedModulePullbackIso_eq_yoneda B S hS g) φ

end AlgebraicGeometry.Space

end
