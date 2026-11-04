module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceTargetComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleSourceComparisonMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsChartMonoReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMapTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftSimpleTransitivity
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMapEtale

/-!
# The action of a derivation on lifts is compatible with étale localization

This file proves [Stacks Project, Tag 0CK8] for the action of Remark
[Stacks Project, Tag 0CK6] read at one object: for a morphism of first order thickenings
`(a, a') : (T ⊂ T') ⟶ (X ⊂ X')` over `B` and an `𝒪_T`-linear `θ : a^*Ω_{X/B} ⟶ 𝒞_{T/T'}`, the
morphism `θ · a'` is the unique morphism `T' ⟶ X'` restricting to `a`, agreeing with `a'` over
`B` and on the defining ideal of `X`, whose difference from `a'` is `θ`
(`AlgebraicGeometry.Space.restrictedLiftAction`, by [Stacks Project, Tag 04D0]).

## Main results

* `AlgebraicGeometry.Space.restrictedLiftAction`: the action `θ · a'` of
  [Stacks Project, Tag 0CK6].
* `AlgebraicGeometry.Space.restrictedLiftAction_comp_etaleLocalization`: **[Stacks Project,
  Tag 0CK8]**.

## Implementation notes

**The map of conormal modules.**  The last map `h^*𝒞_{T₁/T₁'} ⟶ 𝒞_{T₂/T₂'}` of `θ₂` is the
canonical map induced by the comorphism of `h'` on the defining ideals, in its kernel-side
reading: the transpose of `AlgebraicGeometry.Space.conormalComorphism`, which is the
comorphism of `h'` restricted to the kernels of the two reductions `i^{-1}𝒪 ⟶ 𝒪`.  This is the
map of the proof of [Stacks Project, Tag 04CP] (`g^{-1}𝓘' ⟶ 𝓘` read on conormal modules).

## References

* [Stacks Project, Tag 0CK8](https://stacks.math.columbia.edu/tag/0CK8)
* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6), the action.
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0), existence and
  uniqueness of the action.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), the equality sign.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map.
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP), the map of conormal
  modules.
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618) and
  [Tag 0619](https://stacks.math.columbia.edu/tag/0619), the difference of two lifts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₁ v₂ u₁ u₂

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Cancelling an isomorphism and a comparison isomorphism in a composite. -/
theorem map_comp_map_inv_comp_cancel {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    {Y Z : D} (c : Y ⟶ Z) (c' : Z ⟶ Y) (hc : c ≫ c' = 𝟙 Y) {W P : E} (i : W ⟶ F.obj Y)
    (j : F.obj Y ⟶ W) (hij : i ≫ j = 𝟙 W) (R : W ⟶ P) :
    i ≫ F.map c ≫ F.map c' ≫ j ≫ R = R := by
  rw [← F.map_comp_assoc, hc, F.map_id, Category.id_comp, reassoc_of% hij]

/-- Cancelling an isomorphism inside a comparison `G ⋙ F ≅ H` of functors. -/
theorem compIso_inv_app_map_map_hom_app_cancel {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂]
    [Category C₃] (G : C₁ ⥤ C₂) (F : C₂ ⥤ C₃) (H : C₁ ⥤ C₃) (φ : G ⋙ F ≅ H) {M : C₁}
    {N : C₂} {c : G.obj M ⟶ N} {c' : N ⟶ G.obj M} (hc : c ≫ c' = 𝟙 _) {P : C₃}
    (R : H.obj M ⟶ P) :
    φ.inv.app M ≫ F.map c ≫ F.map c' ≫ φ.hom.app M ≫ R = R := by
  rw [← F.map_comp_assoc, hc, F.map_id, Category.id_comp]
  exact φ.inv_hom_id_app_assoc M R

/-- Two mutually inverse `eqToHom`s cancel in front of a morphism. -/
theorem eqToHom_comp_eqToHom_comp {C₁ : Type*} [Category C₁] {X Y Z : C₁} (p : X = Y)
    (q : Y = X) (R : X ⟶ Z) : eqToHom p ≫ eqToHom q ≫ R = R := by
  subst p
  simp

/-- Two mutually inverse `eqToHom`s of functors cancel in front of a morphism. -/
theorem eqToHom_app_comp_eqToHom_app_comp {C₁ : Type u₁} {C₂ : Type u₂} [Category.{v₁} C₁]
    [Category.{v₂} C₂]
    {F G : C₁ ⥤ C₂} (p : G = F) (q : F = G) (M : C₁) {Z : C₂} (R : G.obj M ⟶ Z) :
    (eqToHom p).app M ≫ (eqToHom q).app M ≫ R = R := by
  subst p
  simp

/-- Pasting two commutative squares: `i ≫ u = u₀ ≫ i'` and `i' ≫ g = g₀ ≫ j` give
`i ≫ u ≫ g = (u₀ ≫ g₀) ≫ j`. -/
private theorem comp_comp_eq_of_comm {C₁ : Type*} [Category C₁] {A A' B D E F : C₁}
    {i : A ⟶ B} {u : B ⟶ D} {u₀ : A ⟶ A'} {i' : A' ⟶ D} {g : D ⟶ E} {g₀ : A' ⟶ F} {j : F ⟶ E}
    (hu : i ≫ u = u₀ ≫ i') (hg : i' ≫ g = g₀ ≫ j) : i ≫ u ≫ g = (u₀ ≫ g₀) ≫ j := by
  rw [← Category.assoc, hu, Category.assoc, hg, Category.assoc]

section Congr

variable {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1)

/-- Hypothesis (2) of [Stacks Project, Tag 0618] for a pair of morphisms transports along
equalities of the two morphisms and of their common restriction. -/
theorem restrictedSharpThroughThickening_app_eq_congr {c₀ c₀' c c' : X ⟶ W}
    {e e' : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS)}
    (hc₀ : c₀ = c₀') (hc : c = c') (he : e = e')
    {h₀ : subspaceInclusion B S hS X Z ≫ c₀ = e ≫ subspaceInclusion B S hS W W₀}
    {h : subspaceInclusion B S hS X Z ≫ c = e ≫ subspaceInclusion B S hS W W₀}
    (hker : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c₀ e h₀).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c e h).hom.app V x)
    (h₀' : subspaceInclusion B S hS X Z ≫ c₀' = e' ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e' ≫ subspaceInclusion B S hS W W₀)
    (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀)).obj.obj V)
    (hx : (structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS W W₀)).hom.app V x = 0) :
    (restrictedSharpThroughThickening B S hS Z W₀ c₀' e' h₀').hom.app V x =
      (restrictedSharpThroughThickening B S hS Z W₀ c' e' h').hom.app V x := by
  subst hc₀ hc he
  exact hker V x hx

variable (hZ : IsFirstOrderThickening B S hS X Z.1)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  {Bas : AlgebraicSpaces B S hS} (qb : W ⟶ Bas)

/-- The difference of [Stacks Project, Tag 0618] depends on the first morphism only through its
value. -/
theorem restrictedLiftDifferenceHom_congr_left {c₀ c₀' : X ⟶ W} (c : X ⟶ W) (hc₀ : c₀ = c₀')
    (h₀ : subspaceInclusion B S hS X Z ≫ c₀ = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h₀' : subspaceInclusion B S hS X Z ≫ c₀' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hker : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c₀ e₀ h₀).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h).hom.app V x)
    (hker' : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c₀' e₀ h₀').hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h).hom.app V x)
    (hcc : c₀ ≫ qb = c ≫ qb) (hcc' : c₀' ≫ qb = c ≫ qb) :
    restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c₀ c h₀ h hker hcc =
      restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c₀' c h₀' h hker' hcc' := by
  subst hc₀
  rfl

/-- The difference of [Stacks Project, Tag 0618] along an equality of the common restriction:
read through the identification of the two inverse images of the differentials. -/
theorem restrictedLiftDifferenceHom_congr_restriction {e e' :
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS)} (he : e = e') (c₀ c : X ⟶ W)
    (h₀ : subspaceInclusion B S hS X Z ≫ c₀ = e ≫ subspaceInclusion B S hS W W₀)
    (h : subspaceInclusion B S hS X Z ≫ c = e ≫ subspaceInclusion B S hS W W₀)
    (h₀' : subspaceInclusion B S hS X Z ≫ c₀ = e' ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X Z ≫ c = e' ≫ subspaceInclusion B S hS W W₀)
    (hker : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c₀ e h₀).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c e h).hom.app V x)
    (hker' : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c₀ e' h₀').hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c e' h').hom.app V x)
    (hcc : c₀ ≫ qb = c ≫ qb) :
    restrictedLiftDifferenceHom B S hS Z W₀ hZ e' qb c₀ c h₀' h' hker' hcc =
      (eqToHom (congrArg (modulePullback B S hS) he.symm)).app
          (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ qb)) ≫
        restrictedLiftDifferenceHom B S hS Z W₀ hZ e qb c₀ c h₀ h hker hcc := by
  subst he
  rw [eqToHom_refl, NatTrans.id_app, Category.id_comp]

end Congr

section Action

variable {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1) (hZ : IsFirstOrderThickening B S hS X Z.1)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  {Bas : AlgebraicSpaces B S hS} (qb : W ⟶ Bas) (c₀ : X ⟶ W)
  (h₀ : subspaceInclusion B S hS X Z ≫ c₀ = e₀ ≫ subspaceInclusion B S hS W W₀)
  (θ : (modulePullback B S hS e₀).obj
      (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ qb)) ⟶
    conormalModule B S hS X Z)

/-- **The action `θ · c₀` of a linear map on a morphism of thickenings**, Remark
[Stacks Project, Tag 0CK6]: the unique morphism `X ⟶ W` which restricts on `Z` to `e₀`, agrees
with `c₀` over `Bas` and on the kernel of `j^♯`, and whose difference from `c₀`
([Stacks Project, Tag 0618] with Equation (0619)) is `θ`.  It exists and is unique by
[Stacks Project, Tag 04D0],
`AlgebraicGeometry.Space.existsUnique_hom_restrictedLiftDifferenceHom_eq`. -/
def restrictedLiftAction : X ⟶ W :=
  (existsUnique_hom_restrictedLiftDifferenceHom_eq B S hS Z W₀ hZ e₀ qb c₀ h₀ θ).exists.choose

/-- **The characterizing property of `θ · c₀`**: it restricts on `Z` to `e₀`, agrees with `c₀`
over `Bas` and on the kernel of `j^♯`, and its difference from `c₀` is `θ`. -/
theorem restrictedLiftAction_spec :
    ∃ (h : subspaceInclusion B S hS X Z ≫ restrictedLiftAction B S hS Z W₀ hZ e₀ qb c₀ h₀ θ =
        e₀ ≫ subspaceInclusion B S hS W W₀)
      (hker : ∀ (V : (SmallEtale B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
        (x : (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).obj.obj V),
        (structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
          (restrictedSharpThroughThickening B S hS Z W₀ c₀ e₀ h₀).hom.app V x =
            (restrictedSharpThroughThickening B S hS Z W₀
              (restrictedLiftAction B S hS Z W₀ hZ e₀ qb c₀ h₀ θ) e₀ h).hom.app V x)
      (hcc : c₀ ≫ qb = restrictedLiftAction B S hS Z W₀ hZ e₀ qb c₀ h₀ θ ≫ qb),
      restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c₀
        (restrictedLiftAction B S hS Z W₀ hZ e₀ qb c₀ h₀ θ) h₀ h hker hcc = θ :=
  (existsUnique_hom_restrictedLiftDifferenceHom_eq B S hS Z W₀ hZ e₀ qb c₀ h₀ θ).exists.choose_spec

end Action

section Localization

variable {T₁' T₂' X₁' X₂' B₁ B₂ : AlgebraicSpaces B S hS}
  (T₁ : ClosedSubspaces B S hS T₁'.1) (T₂ : ClosedSubspaces B S hS T₂'.1)
  (X₁ : ClosedSubspaces B S hS X₁'.1) (X₂ : ClosedSubspaces B S hS X₂'.1)
  (hT₁ : IsFirstOrderThickening B S hS T₁' T₁.1) (hT₂ : IsFirstOrderThickening B S hS T₂' T₂.1)
  (h' : T₂' ⟶ T₁')
  (h : (⟨T₂.1.toFunctor, T₂.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨T₁.1.toFunctor, T₁.2.1⟩ : AlgebraicSpaces B S hS))
  (hh : subspaceInclusion B S hS T₂' T₂ ≫ h' = h ≫ subspaceInclusion B S hS T₁' T₁)
  (f' : X₂' ⟶ X₁')
  (f : (⟨X₂.1.toFunctor, X₂.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨X₁.1.toFunctor, X₁.2.1⟩ : AlgebraicSpaces B S hS))
  (hf : subspaceInclusion B S hS X₂' X₂ ≫ f' = f ≫ subspaceInclusion B S hS X₁' X₁)
  (a₁' : T₁' ⟶ X₁')
  (a₁ : (⟨T₁.1.toFunctor, T₁.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨X₁.1.toFunctor, X₁.2.1⟩ : AlgebraicSpaces B S hS))
  (ha₁ : subspaceInclusion B S hS T₁' T₁ ≫ a₁' = a₁ ≫ subspaceInclusion B S hS X₁' X₁)
  (a₂' : T₂' ⟶ X₂')
  (a₂ : (⟨T₂.1.toFunctor, T₂.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨X₂.1.toFunctor, X₂.2.1⟩ : AlgebraicSpaces B S hS))
  (ha₂ : subspaceInclusion B S hS T₂' T₂ ≫ a₂' = a₂ ≫ subspaceInclusion B S hS X₂' X₂)
  (hsq' : a₂' ≫ f' = h' ≫ a₁') (hsq : a₂ ≫ f = h ≫ a₁)
  (q₁ : X₁' ⟶ B₁) (q₂ : X₂' ⟶ B₂) (ε : B₂ ⟶ B₁) (hq : f' ≫ q₁ = q₂ ≫ ε)

include hf hq in
/-- The square of structure morphisms of the reduced spaces, `f ≫ j₁ ≫ q₁ = (j₂ ≫ q₂) ≫ ε`, read
off the square of thickenings and the square of bases. -/
theorem localization_comm :
    f ≫ subspaceInclusion B S hS X₁' X₁ ≫ q₁ = (subspaceInclusion B S hS X₂' X₂ ≫ q₂) ≫ ε := by
  rw [← Category.assoc, ← hf, Category.assoc, hq, Category.assoc]

variable (hfet : IsEtale B S hS f.hom) (hεet : IsEtale B S hS ε.hom)
  (cm : (modulePullback B S hS h).obj (conormalModule B S hS T₁' T₁) ⟶
    conormalModule B S hS T₂' T₂)

include hfet hεet in
/-- **The identification `f^*Ω_{X₁/B₁} ≅ Ω_{X₂/B₂}` of [Stacks Project, Tag 04CU]**, as the
comparison map of [Stacks Project, Tag 04CX], which is invertible for the étale `f` and `ε` by
`AlgebraicGeometry.Space.isIso_sheafOfDifferentialsMap_of_isEtale`. -/
def localizationDifferentialsIso :
    (modulePullback B S hS f).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' X₁ ≫ q₁)) ≅
      sheafOfDifferentials B S hS (subspaceInclusion B S hS X₂' X₂ ≫ q₂) :=
  @asIso _ _ _ _ (sheafOfDifferentialsMap B S hS f
      (subspaceInclusion B S hS X₁' X₁ ≫ q₁) (subspaceInclusion B S hS X₂' X₂ ≫ q₂) ε
      (localization_comm B S hS X₁ X₂ f' f hf q₁ q₂ ε hq))
    (isIso_sheafOfDifferentialsMap_of_isEtale B S hS
      (subspaceInclusion B S hS X₁' X₁ ≫ q₁) f (subspaceInclusion B S hS X₂' X₂ ≫ q₂) ε hfet hεet
      (localization_comm B S hS X₁ X₂ f' f hf q₁ q₂ ε hq))

include hfet hεet in
/-- The forward map of `AlgebraicGeometry.Space.localizationDifferentialsIso` is the comparison
map of [Stacks Project, Tag 04CX]. -/
theorem localizationDifferentialsIso_hom :
    (localizationDifferentialsIso B S hS X₁ X₂ f' f hf q₁ q₂ ε hq hfet hεet).hom =
      sheafOfDifferentialsMap B S hS f
        (subspaceInclusion B S hS X₁' X₁ ≫ q₁) (subspaceInclusion B S hS X₂' X₂ ≫ q₂) ε
        (localization_comm B S hS X₁ X₂ f' f hf q₁ q₂ ε hq) := by
  unfold localizationDifferentialsIso
  exact @asIso_hom _ _ _ _ _ (isIso_sheafOfDifferentialsMap_of_isEtale B S hS
      (subspaceInclusion B S hS X₁' X₁ ≫ q₁) f (subspaceInclusion B S hS X₂' X₂ ≫ q₂) ε hfet hεet
      (localization_comm B S hS X₁ X₂ f' f hf q₁ q₂ ε hq))

include hfet hεet in
/-- The forward map of `AlgebraicGeometry.Space.localizationDifferentialsIso` has the
characterizing property of the comparison map of [Stacks Project, Tag 04CX]. -/
theorem isSheafOfDifferentialsMap_localizationDifferentialsIso_hom :
    IsSheafOfDifferentialsMap B S hS f (subspaceInclusion B S hS X₁' X₁ ≫ q₁)
      (subspaceInclusion B S hS X₂' X₂ ≫ q₂)
      (localizationDifferentialsIso B S hS X₁ X₂ f' f hf q₁ q₂ ε hq hfet hεet).hom := by
  rw [localizationDifferentialsIso_hom]
  exact isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS f _ _ ε
    (localization_comm B S hS X₁ X₂ f' f hf q₁ q₂ ε hq)


include hh hfet hεet hsq' in
/-- **[Stacks Project, Tag 0CK8] with the map of conormal modules read on the kernels.**  The
action of `θ₂` on `a₂'` followed by `f'` is `h'` followed by the action of `θ₁` on `a₁'`, where the
map `h^*𝒞_{T₁/T₁'} ⟶ 𝒞_{T₂/T₂'}` in `θ₂` is the transpose of the comorphism of `h'` on the
kernels of the two reductions, `AlgebraicGeometry.Space.conormalComorphism`.  The two actions
are given by their characterizing property: `c₁` and `c₂` are morphisms of thickenings over `B₁`
and `B₂` with differences `θ₁` and `θ₂` from `a₁'` and `a₂'`. -/
theorem comp_eq_of_restrictedLiftDifferenceHom_conormalComorphism
    (θ₁ : (modulePullback B S hS a₁).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' X₁ ≫ q₁)) ⟶
      conormalModule B S hS T₁' T₁)
    (c₁ : T₁' ⟶ X₁')
    (hc₁ : subspaceInclusion B S hS T₁' T₁ ≫ c₁ = a₁ ≫ subspaceInclusion B S hS X₁' X₁)
    (hker₁ : ∀ (V : (SmallEtale B S hS
        (⟨X₁.1.toFunctor, X₁.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS X₁' X₁)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS X₁' X₁)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS T₁ X₁ a₁' a₁ ha₁).hom.app V x =
          (restrictedSharpThroughThickening B S hS T₁ X₁ c₁ a₁ hc₁).hom.app V x)
    (hcc₁ : a₁' ≫ q₁ = c₁ ≫ q₁)
    (hθ₁ : restrictedLiftDifferenceHom B S hS T₁ X₁ hT₁ a₁ q₁ a₁' c₁ ha₁ hc₁ hker₁ hcc₁ = θ₁)
    (c₂ : T₂' ⟶ X₂')
    (hc₂ : subspaceInclusion B S hS T₂' T₂ ≫ c₂ = a₂ ≫ subspaceInclusion B S hS X₂' X₂)
    (hker₂ : ∀ (V : (SmallEtale B S hS
        (⟨X₂.1.toFunctor, X₂.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS X₂' X₂)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS X₂' X₂)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS T₂ X₂ a₂' a₂ ha₂).hom.app V x =
          (restrictedSharpThroughThickening B S hS T₂ X₂ c₂ a₂ hc₂).hom.app V x)
    (hcc₂ : a₂' ≫ q₂ = c₂ ≫ q₂)
    (hθ₂ : restrictedLiftDifferenceHom B S hS T₂ X₂ hT₂ a₂ q₂ a₂' c₂ ha₂ hc₂ hker₂ hcc₂ =
      (modulePullback B S hS a₂).map
          (localizationDifferentialsIso B S hS X₁ X₂ f' f hf q₁ q₂ ε hq hfet hεet).inv ≫
        (modulePullbackCompIso B S hS a₂ f).hom.app
          (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' X₁ ≫ q₁)) ≫
        (eqToHom (congrArg (modulePullback B S hS)
          (show @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ a₂ f =
          @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h a₁ from hsq))).app
          (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' X₁ ≫ q₁)) ≫
        (modulePullbackCompIso B S hS h a₁).inv.app
          (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' X₁ ≫ q₁)) ≫
        (modulePullback B S hS h).map θ₁ ≫
        ((modulePullbackAdjunction B S hS h).homEquiv _ _).symm
          (conormalComorphism B S hS T₁ T₂ hT₁ hT₂ h' h hh)) :
    c₂ ≫ f' = h' ≫ c₁ := by
  have hm₀ := comp_comp_eq_of_comm ha₂ hf
  have hm₂ := comp_comp_eq_of_comm hc₂ hf
  have hn₁0 := comp_comp_eq_of_comm hh ha₁
  have hm₁0 := comp_comp_eq_of_comm hh hc₁
  have hm₁ : subspaceInclusion B S hS T₂' T₂ ≫ h' ≫ c₁ =
      (a₂ ≫ f) ≫ subspaceInclusion B S hS X₁' X₁ := by
    rw [hm₁0, hsq]
  have hn₁ : subspaceInclusion B S hS T₂' T₂ ≫ h' ≫ a₁' =
      (a₂ ≫ f) ≫ subspaceInclusion B S hS X₁' X₁ := by
    rw [hn₁0, hsq]
  have hkerT := restrictedSharpThroughThickening_comp_target_app_eq B S hS T₂ X₂ X₁ a₂ f' f hf
    a₂' c₂ ha₂ hc₂ hm₀ hm₂ hker₂
  have hccT : (a₂' ≫ f') ≫ q₁ = (c₂ ≫ f') ≫ q₁ := by
    rw [Category.assoc, Category.assoc, hq, ← Category.assoc, hcc₂, Category.assoc]
  have hkerS0 := restrictedSharpThroughThickening_comp_app_eq B S hS T₁ T₂ h' h hh X₁ a₁' c₁ a₁
    ha₁ hc₁ hn₁0 hm₁0 hker₁
  have hkerS := restrictedSharpThroughThickening_app_eq_congr B S hS T₂ X₁ rfl rfl hsq.symm
    hkerS0 hn₁ hm₁
  have hkerS' := restrictedSharpThroughThickening_app_eq_congr B S hS T₂ X₁ hsq'.symm rfl rfl
    hkerS hm₀ hm₁
  have hccS : (h' ≫ a₁') ≫ q₁ = (h' ≫ c₁) ≫ q₁ := by
    rw [Category.assoc, Category.assoc, hcc₁]
  have hccS' : (a₂' ≫ f') ≫ q₁ = (h' ≫ c₁) ≫ q₁ := by
    rw [hsq', hccS]
  have hm₀S : subspaceInclusion B S hS T₂' T₂ ≫ a₂' ≫ f' =
      (h ≫ a₁) ≫ subspaceInclusion B S hS X₁' X₁ := by
    rw [hm₀, hsq]
  have hm₂S : subspaceInclusion B S hS T₂' T₂ ≫ c₂ ≫ f' =
      (h ≫ a₁) ≫ subspaceInclusion B S hS X₁' X₁ := by
    rw [hm₂, hsq]
  have hkerTS := restrictedSharpThroughThickening_app_eq_congr B S hS T₂ X₁ rfl rfl hsq
    hkerT hm₀S hm₂S
  have hkerSS := restrictedSharpThroughThickening_app_eq_congr B S hS T₂ X₁ hsq'.symm rfl rfl
    hkerS0 hm₀S hm₁0
  refine eq_of_restrictedLiftDifferenceHom_eq B S hS T₂ X₁ hT₂ (h ≫ a₁) q₁ (a₂' ≫ f') (c₂ ≫ f')
    (h' ≫ c₁) hm₀S hm₂S hm₁0 hkerTS hkerSS hccT hccS' ?_
  rw [restrictedLiftDifferenceHom_congr_restriction B S hS T₂ X₁ hT₂ q₁
      (show @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ a₂ f =
        @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h a₁ from hsq) (a₂' ≫ f') (c₂ ≫ f')
      hm₀ hm₂ hm₀S hm₂S hkerT hkerTS hccT,
    restrictedLiftDifferenceHom_comp_target B S hS T₂ X₂ X₁ a₂ f' f hf hT₂ a₂' c₂ ha₂ hc₂ hker₂
      hm₀ hm₂ q₂ q₁ hcc₂ _
      (isSheafOfDifferentialsMap_localizationDifferentialsIso_hom B S hS X₁ X₂ f' f hf q₁ q₂ ε hq
        hfet hεet) hkerT hccT, hθ₂,
    restrictedLiftDifferenceHom_congr_left B S hS T₂ X₁ hT₂ (h ≫ a₁) q₁ (h' ≫ c₁) hsq' hm₀S
      hn₁0 hm₁0 hkerSS hkerS0 hccS' hccS,
    restrictedLiftDifferenceHom_comp B S hS T₁ T₂ X₁ hT₁ hT₂ h' h hh a₁ q₁ a₁' c₁ ha₁ hc₁
      hker₁ hcc₁ hn₁0 hm₁0 hkerS0 hccS, hθ₁,
    compIso_inv_app_map_map_hom_app_cancel _ _ _ _
      (localizationDifferentialsIso B S hS X₁ X₂ f' f hf q₁ q₂ ε hq hfet hεet).hom_inv_id]
  exact eqToHom_app_comp_eqToHom_app_comp _ _ _ _

include hh hfet hεet hsq' in
/-- **The action of a derivation on lifts is compatible with étale localization.**  Let `S` be
a scheme and consider a commutative diagram of first order thickenings of algebraic spaces over
`S`
```
(T₂ ⊂ T₂') --(a₂, a₂')--> (X₂ ⊂ X₂')        X₂' --q₂--> B₂
   |                          |               |          |
 (h, h')                   (f, f')            f'         ε
   v                          v               v          v
(T₁ ⊂ T₁') --(a₁, a₁')--> (X₁ ⊂ X₁')        X₁' --q₁--> B₁
```
together with the commutative square on the right, with `f : X₂ ⟶ X₁` and `ε : B₂ ⟶ B₁` étale.
For an `𝒪_{T₁}`-linear map `θ₁ : a₁^*Ω_{X₁/B₁} ⟶ 𝒞_{T₁/T₁'}` let `θ₂` be the composite
```
a₂^*Ω_{X₂/B₂} = h^*a₁^*Ω_{X₁/B₁} --h^*θ₁--> h^*𝒞_{T₁/T₁'} ⟶ 𝒞_{T₂/T₂'},
```
whose equality sign is the inverse image along `a₂` of the identification
`f^*Ω_{X₁/B₁} ≅ Ω_{X₂/B₂}` of [Stacks Project, Tag 04CU]
(`AlgebraicGeometry.Space.localizationDifferentialsIso`) followed by the comparisons
`a₂^*f^* ≅ (a₂ ≫ f)^* = (h ≫ a₁)^* ≅ h^*a₁^*` of [Stacks Project, Tag 03LU], and whose last map
is the canonical map of conormal modules induced by the comorphism of `h'` on the defining ideals
(`AlgebraicGeometry.Space.conormalComorphism`, transposed).  Then
```
(θ₂ · a₂') ≫ f' = h' ≫ (θ₁ · a₁'),
```
the actions being those of Remark [Stacks Project, Tag 0CK6],
`AlgebraicGeometry.Space.restrictedLiftAction`: `θ · a'` is the unique morphism of thickenings
over the base whose difference from `a'` ([Stacks Project, Tag 0618], Equation (0619)) is `θ`,
which exists by [Stacks Project, Tag 04D0]. -/
@[stacks 0CK8]
theorem restrictedLiftAction_comp_etaleLocalization
    (_hX₁ : IsFirstOrderThickening B S hS X₁' X₁.1)
    (_hX₂ : IsFirstOrderThickening B S hS X₂' X₂.1)
    (θ₁ : (modulePullback B S hS a₁).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' X₁ ≫ q₁)) ⟶
      conormalModule B S hS T₁' T₁) :
    restrictedLiftAction B S hS T₂ X₂ hT₂ a₂ q₂ a₂' ha₂
        ((modulePullback B S hS a₂).map
            (localizationDifferentialsIso B S hS X₁ X₂ f' f hf q₁ q₂ ε hq hfet hεet).inv ≫
          (modulePullbackCompIso B S hS a₂ f).hom.app
            (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' X₁ ≫ q₁)) ≫
          (eqToHom (congrArg (modulePullback B S hS)
            (show @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ a₂ f =
            @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h a₁ from hsq))).app
            (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' X₁ ≫ q₁)) ≫
          (modulePullbackCompIso B S hS h a₁).inv.app
            (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' X₁ ≫ q₁)) ≫
          (modulePullback B S hS h).map θ₁ ≫
          ((modulePullbackAdjunction B S hS h).homEquiv _ _).symm
            (conormalComorphism B S hS T₁ T₂ hT₁ hT₂ h' h hh)) ≫ f' =
      h' ≫ restrictedLiftAction B S hS T₁ X₁ hT₁ a₁ q₁ a₁' ha₁ θ₁ := by
  obtain ⟨hc₁, hker₁, hcc₁, hθ₁⟩ := restrictedLiftAction_spec B S hS T₁ X₁ hT₁ a₁ q₁ a₁' ha₁ θ₁
  obtain ⟨hc₂, hker₂, hcc₂, hθ₂⟩ := restrictedLiftAction_spec B S hS T₂ X₂ hT₂ a₂ q₂ a₂' ha₂
    ((modulePullback B S hS a₂).map
        (localizationDifferentialsIso B S hS X₁ X₂ f' f hf q₁ q₂ ε hq hfet hεet).inv ≫
      (modulePullbackCompIso B S hS a₂ f).hom.app
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' X₁ ≫ q₁)) ≫
      (eqToHom (congrArg (modulePullback B S hS)
        (show @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ a₂ f =
            @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h a₁ from hsq))).app
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' X₁ ≫ q₁)) ≫
      (modulePullbackCompIso B S hS h a₁).inv.app
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' X₁ ≫ q₁)) ≫
      (modulePullback B S hS h).map θ₁ ≫
      ((modulePullbackAdjunction B S hS h).homEquiv _ _).symm
        (conormalComorphism B S hS T₁ T₂ hT₁ hT₂ h' h hh))
  exact comp_eq_of_restrictedLiftDifferenceHom_conormalComorphism B S hS T₁ T₂ X₁ X₂ hT₁ hT₂
    h' h hh f' f hf a₁' a₁ ha₁ a₂' a₂ ha₂ hsq' hsq q₁ q₂ ε hq hfet hεet θ₁ _ hc₁ hker₁ hcc₁ hθ₁
    _ hc₂ hker₂ hcc₂ hθ₂

end Localization

end AlgebraicGeometry.Space

end
