module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ExtendScalarsBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackExtendScalarsModel

/-!
# The base change of two objectwise extensions of scalars, read on abelian sheaves

Let `A` be a presheaf of not necessarily commutative rings, let `ν : A ⟶ R₀` and
`ρ : R₀ ⟶ R₀'` be morphisms of presheaves of rings, let `α : R₀ ⟶ R` and `α' : R₀' ⟶ R'` be
locally bijective morphisms onto the underlying presheaves of sheaves of rings `R` and `R'`,
and let `M` be a presheaf of `A`-modules. Suppose given sheaves of modules `Z` over `R` and `Z'`
over `R'` identified with the sheafifications of `R₀ ⊗_{ν,A} M` and `R₀' ⊗_{ν ≫ ρ,A} M`, and a
morphism `m` of the underlying abelian sheaves of `Z` and `Z'`.

The module structures of `Z` and `Z'` are over different sheaves of rings, so `m` cannot be
compared with any morphism of sheaves of modules; what *can* be said is that `m` agrees with the
sheafification of the base change
`Stacks.NoncommChangeOfRings.Presheaf.baseChangeTranspose`, and this file says exactly when: as
soon as `m` comes from a `ρ`-semilinear morphism `g` of presheaves of `R₀`-modules which carries
the unit of extension of scalars along `ν` to the unit of extension of scalars along `ν ≫ ρ`.

That is the shape in which the legs and the transition morphisms of the cocone of Stacks Tag
0EXB are compared with the objectwise base changes: in both cases `m` is `SheafOfModules.toSheaf`
of a restriction of scalars, hence semilinear for free, and the condition on the units is the
compatibility of the cocone with the units, which the adjunctions provide.

## Main results

* `Stacks.SheafOfModules.toSheaf_map_inv_comp_eq_baseChangeTranspose`: the comparison with the
  two identifications read as morphisms *out of* the sheafifications.
* `Stacks.SheafOfModules.toSheaf_comp_baseChangeTranspose`: **the same identity as a commuting
  square**, which is the form a morphism of diagrams is assembled from.
* `Stacks.SheafOfModules.toSheaf_comp_baseChangeTo`: that square with the target of the base
  change read along a morphism which is merely *equal* to the composite `ν ≫ ρ`, which is how a
  consumer whose composite is a theorem rather than a definition uses it.

## Implementation notes

The proof is three reductions, each one adjunction. Morphisms out of `presheafToSheaf P` are
determined by their restriction along `CategoryTheory.toSheafify`, which brings the identity
down to presheaves of abelian groups; there every restriction of scalars and every forgetful
functor is the identity on the underlying data, so the identity is the image under
`PresheafOfModules.toPresheaf` of an identity between morphisms of presheaves of `R₀`-modules.
That one is `Stacks.NoncommChangeOfRings.Presheaf.comp_eq_baseChangeTranspose_comp`, which is
the extension-of-scalars adjunction, applied to the morphisms the sheafification adjunction
produces out of the two identifications.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ u v₂ u₂

namespace CategoryTheory

variable {D : Type u₂} [Category.{v₂} D]

/-- **Associativity bookkeeping for a comparison of two factorisations.** The hypotheses say
that `T ≫ a` followed by `b` factors as `u` followed by `T' ≫ d`, and that `u ≫ T'` is `T ≫ c`;
the conclusion is that `a ≫ b` and `c ≫ d` agree after `T`. It exists because the categories
this is used in have objects which agree only up to unfolding, so `rw` cannot be used on the
goal, while an abstract category poses no such problem. -/
lemma comp_comp_eq_comp_comp_of_comp_eq {P X Y W X' Q : D} (T : P ⟶ X) (a : X ⟶ Y) (b : Y ⟶ W)
    (c : X ⟶ X') (d : X' ⟶ W) (u : P ⟶ Q) (T' : Q ⟶ X')
    (h₁ : (T ≫ a) ≫ b = u ≫ T' ≫ d) (h₂ : u ≫ T' = T ≫ c) :
    T ≫ a ≫ b = T ≫ c ≫ d := by
  rw [← Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc]

/-- **A commuting square read with the two isomorphisms on the other side.** -/
lemma Iso.comp_hom_eq_hom_comp_of_inv_comp {X Y X' Y' : D} (i : X ≅ Y) (j : X' ≅ Y')
    (m : X ⟶ X') (w : Y ⟶ Y') (h : i.inv ≫ m = w ≫ j.inv) :
    m ≫ j.hom = i.hom ≫ w := by
  refine (Iso.inv_comp_eq i).mp ?_
  rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CategoryTheory

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {A : Cᵒᵖ ⥤ RingCat.{u}} {R R' : Sheaf J RingCat.{u}}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  {R₀' : Cᵒᵖ ⥤ RingCat.{u}} (α' : R₀' ⟶ R'.obj)
  [Presheaf.IsLocallyInjective J α'] [Presheaf.IsLocallySurjective J α']
  (ν : A ⟶ R₀) (ρ : R₀ ⟶ R₀') (M : PresheafOfModules.{u} A)

section Composite

variable (Z : _root_.SheafOfModules.{u} R) (Z' : _root_.SheafOfModules.{u} R')
  (κ : Z ≅ (PresheafOfModules.sheafification α).obj
    ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} ν).obj M))
  (κ' : Z' ≅ (PresheafOfModules.sheafification α').obj
    ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} (ν ≫ ρ)).obj M))
  (m : (_root_.SheafOfModules.toSheaf R).obj Z ⟶ (_root_.SheafOfModules.toSheaf R').obj Z')
  (g : (_root_.SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α).obj Z ⟶
    (PresheafOfModules.restrictScalars ρ).obj
      ((_root_.SheafOfModules.forget R' ⋙ PresheafOfModules.restrictScalars α').obj Z'))
  (hm : (PresheafOfModules.toPresheaf R₀).map g = m.hom)
  (hu : (Stacks.NoncommChangeOfRings.Presheaf.extendScalarsAdjunction.{u} ν).unit.app M ≫
      (PresheafOfModules.restrictScalars ν).map
        (PresheafOfModules.sheafificationHomEquiv α κ.inv ≫ g) =
    (Stacks.NoncommChangeOfRings.Presheaf.extendScalarsAdjunction.{u} (ν ≫ ρ)).unit.app M ≫
      (PresheafOfModules.restrictScalars (ν ≫ ρ)).map
        (PresheafOfModules.sheafificationHomEquiv α' κ'.inv))

include hm hu

/-- **The comparison of a morphism of the underlying abelian sheaves with the sheafification of
the base change**, read as an identity between morphisms out of the two sheafifications. -/
theorem toSheaf_map_inv_comp_eq_baseChangeTranspose :
    (_root_.SheafOfModules.toSheaf R).map κ.inv ≫ m =
      (presheafToSheaf J AddCommGrpCat.{u}).map
          ((PresheafOfModules.toPresheaf R₀).map
            (Stacks.NoncommChangeOfRings.Presheaf.baseChangeTranspose ν ρ M)) ≫
        (_root_.SheafOfModules.toSheaf R').map κ'.inv := by
  have hB := Stacks.NoncommChangeOfRings.Presheaf.comp_eq_baseChangeTranspose_comp ν ρ M
    (PresheafOfModules.sheafificationHomEquiv α κ.inv) g
    (PresheafOfModules.sheafificationHomEquiv α' κ'.inv) hu
  have hnat : (PresheafOfModules.toPresheaf R₀).map
          (Stacks.NoncommChangeOfRings.Presheaf.baseChangeTranspose ν ρ M) ≫
        CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf R₀').obj
          ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} (ν ≫ ρ)).obj M)) =
      CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf R₀).obj
          ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} ν).obj M)) ≫
        ((presheafToSheaf J AddCommGrpCat.{u}).map ((PresheafOfModules.toPresheaf R₀).map
          (Stacks.NoncommChangeOfRings.Presheaf.baseChangeTranspose ν ρ M))).hom :=
    (CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{u}).unit.naturality _
  refine ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv
    ((PresheafOfModules.toPresheaf R₀).obj
      ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} ν).obj M))
    ((_root_.SheafOfModules.toSheaf R').obj Z')).injective ?_
  change CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf R₀).obj
        ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} ν).obj M)) ≫
      (((_root_.SheafOfModules.toSheaf R).map κ.inv).hom ≫ m.hom) =
    CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf R₀).obj
        ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} ν).obj M)) ≫
      (((presheafToSheaf J AddCommGrpCat.{u}).map ((PresheafOfModules.toPresheaf R₀).map
          (Stacks.NoncommChangeOfRings.Presheaf.baseChangeTranspose ν ρ M))).hom ≫
        ((_root_.SheafOfModules.toSheaf R').map κ'.inv).hom)
  have hgoal : (CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf R₀).obj
            ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} ν).obj M)) ≫
          ((_root_.SheafOfModules.toSheaf R).map κ.inv).hom) ≫
        (PresheafOfModules.toPresheaf R₀).map g =
      (PresheafOfModules.toPresheaf R₀).map
          (Stacks.NoncommChangeOfRings.Presheaf.baseChangeTranspose ν ρ M) ≫
        CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf R₀').obj
            ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} (ν ≫ ρ)).obj M)) ≫
          ((_root_.SheafOfModules.toSheaf R').map κ'.inv).hom :=
    congrArg (PresheafOfModules.toPresheaf R₀).map hB
  exact CategoryTheory.comp_comp_eq_comp_comp_of_comp_eq _ _ _ _ _ _ _
    ((congrArg (fun q ↦ _ ≫ q) hm).symm.trans hgoal) hnat

/-- **The comparison of a morphism of the underlying abelian sheaves with the sheafification of
the base change, as a commuting square.** -/
theorem toSheaf_comp_baseChangeTranspose :
    m ≫ (_root_.SheafOfModules.toSheaf R').map κ'.hom =
      (_root_.SheafOfModules.toSheaf R).map κ.hom ≫
        (presheafToSheaf J AddCommGrpCat.{u}).map
          ((PresheafOfModules.toPresheaf R₀).map
            (Stacks.NoncommChangeOfRings.Presheaf.baseChangeTranspose ν ρ M)) :=
  Iso.comp_hom_eq_hom_comp_of_inv_comp ((_root_.SheafOfModules.toSheaf R).mapIso κ)
    ((_root_.SheafOfModules.toSheaf R').mapIso κ') m _
    (toSheaf_map_inv_comp_eq_baseChangeTranspose α α' ν ρ M Z Z' κ κ' m g hm hu)

end Composite

section Target

variable (δ : A ⟶ R₀') (hδ : ν ≫ ρ = δ)
  (Z : _root_.SheafOfModules.{u} R) (Z' : _root_.SheafOfModules.{u} R')
  (κ : Z ≅ (PresheafOfModules.sheafification α).obj
    ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} ν).obj M))
  (κ' : Z' ≅ (PresheafOfModules.sheafification α').obj
    ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} δ).obj M))
  (m : (_root_.SheafOfModules.toSheaf R).obj Z ⟶ (_root_.SheafOfModules.toSheaf R').obj Z')
  (g : (_root_.SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α).obj Z ⟶
    (PresheafOfModules.restrictScalars ρ).obj
      ((_root_.SheafOfModules.forget R' ⋙ PresheafOfModules.restrictScalars α').obj Z'))
  (hm : (PresheafOfModules.toPresheaf R₀).map g = m.hom)
  (hu : (Stacks.NoncommChangeOfRings.Presheaf.extendScalarsAdjunction.{u} ν).unit.app M ≫
      (PresheafOfModules.restrictScalars ν).map
        (PresheafOfModules.sheafificationHomEquiv α κ.inv ≫ g) =
    ((Stacks.NoncommChangeOfRings.Presheaf.extendScalarsAdjunction.{u} δ).unit.app M ≫
        (PresheafOfModules.restrictScalars δ).map
          (PresheafOfModules.sheafificationHomEquiv α' κ'.inv)) ≫
      eqToHom (congrArg (fun f ↦ (PresheafOfModules.restrictScalars f).obj
        ((_root_.SheafOfModules.forget R' ⋙
          PresheafOfModules.restrictScalars α').obj Z')) hδ.symm))

include hδ hm hu

/-- **The comparison of a morphism of the underlying abelian sheaves with the sheafification of
the base change**, with the target of the base change read along a morphism `δ` which is merely
*equal* to the composite `ν ≫ ρ`. This is the form the cocone of Stacks Tag 0EXB consumes, and
the equality is removed by `subst`. -/
theorem toSheaf_comp_baseChangeTo :
    m ≫ (_root_.SheafOfModules.toSheaf R').map κ'.hom =
      (_root_.SheafOfModules.toSheaf R).map κ.hom ≫
        (presheafToSheaf J AddCommGrpCat.{u}).map
          ((PresheafOfModules.toPresheaf A).map
            (Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo ν ρ M δ hδ)) := by
  subst hδ
  have h₀ : Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo ν ρ M (ν ≫ ρ) rfl =
      Stacks.NoncommChangeOfRings.Presheaf.baseChange ν ρ M := by
    rw [Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo]
    exact Category.comp_id _
  refine Eq.trans (toSheaf_comp_baseChangeTranspose α α' ν ρ M Z Z' κ κ' m g hm
    (hu.trans (Category.comp_id _))) ?_
  exact congrArg (fun q ↦ (_root_.SheafOfModules.toSheaf R).map κ.hom ≫
    (presheafToSheaf J AddCommGrpCat.{u}).map q)
    (congrArg (PresheafOfModules.toPresheaf A).map h₀).symm

end Target

end Stacks.SheafOfModules

end
