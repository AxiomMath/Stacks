module

public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.StableModel
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSemistableGenus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStable

/-!
# The stable model of a prestable family of curves: definitions and base change

This file sets up the statement of Stacks 0E8A. Let `f : X ⟶ S` be a prestable family of curves of
genus `g ≥ 2`. A *stable model* of `X` is a stable family `Y ⟶ S` of genus `g` together with a
morphism `c : X ⟶ Y` over `S` such that

1. `𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0`, and this remains true after every base change `S' ⟶ S`;
2. for every point `s` of `S` the morphism of fibres `c_s : X_s ⟶ Y_s` is the contraction of
   rational tails and bridges of Stacks 0E7N, characterized by Stacks 0E7Q.

Both conditions are stable under base change. That is the input the stabilization morphism of
Stacks 0E8B needs.

## Main definitions

* `AlgebraicGeometry.C1590Private.IsUniversallyAcyclicContraction`: condition (1).
* `AlgebraicGeometry.C1590Private.IsFibrewiseStableContraction`: condition (2).
* `AlgebraicGeometry.C1590Private.IsStableModel`: a stable model of genus `g`.

## Main results

* `AlgebraicGeometry.C1590Private.IsUniversallyAcyclicContraction.of_isPullback` and
  `AlgebraicGeometry.C1590Private.IsFibrewiseStableContraction.of_isPullback`: conditions (1) and
  (2) pass to base changes.
* `AlgebraicGeometry.C1590Private.IsStableModel.of_hom`: a stable model pulls back to a stable
  model along morphisms of families of curves.

## Implementation notes

The base changes in (1) are not taken by a chosen fibre product. They are quantified over all
cartesian squares of algebraic spaces over a morphism of schemes `V ⟶ S`. Fibre products of
algebraic spaces exist (`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct`), so this form
is not vacuous, and with it base change of (1) is a matter of pasting squares. The direct image of
the structure sheaf is the comparison map `AlgebraicGeometry.Space.structureSharp` of sheaves of
rings on the small étale site, and `R¹c_*𝒪_X` is the first right derived functor of
`AlgebraicGeometry.Space.modulePushforward` on the structure sheaf, as for the genus in
`StacksFrontier/AlgebraicGeometry/Quot/CurvesStable.lean`.

Condition (2) is imposed at every field-valued point of the base, not only at the residue fields
of points. This is the same device as `AlgebraicGeometry.IsStableCurveFamily` (Stacks 0E75). The
fibres are presented by schemes of the site through cartesian squares of presheaves, and the
condition asks that a presentation of the fibre of `X` exists and that every pair of presentations,
with the morphism of schemes induced by `c`, satisfies the conditions
`Stacks.Curves.StableModel.IsStableContraction` of Stacks 0E7Q. By the uniqueness in Stacks 0E7Q,
these conditions determine `c_s` up to unique isomorphism as the contraction of rational tails and
bridges. The genus is the genus of the fibres (`AlgebraicGeometry.CurveFamily.HasFibresOfGenus`),
which is unconditionally stable under base change.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E8B](https://stacks.math.columbia.edu/tag/0E8B)
* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

namespace AlgebraicGeometry.C1590Private

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- `R¹a_*𝒪_A` for a morphism `a : A ⟶ D` of algebraic spaces, as a module on the small étale site
of `D`. -/
noncomputable def firstDirectImage {A D : AlgebraicSpaces B integerBase hZ} (a : A ⟶ D) :
    Space.Modules.{u, u} B integerBase hZ D.1 D.2 :=
  have := Space.hasInjectiveResolutions_modules B integerBase hZ A.1 A.2
  ((Space.modulePushforward B integerBase hZ a).rightDerived 1).obj
    (Space.structureSheafModule B integerBase hZ A)

/-- **Condition (1) of Stacks 0E8A.** A morphism `a : A ⟶ D` of algebraic spaces over a scheme `U`
satisfies `𝒪_D = a_*𝒪_A` and `R¹a_*𝒪_A = 0`, and this stays true after base change along every
morphism of schemes `V ⟶ U`. -/
def IsUniversallyAcyclicContraction {A D : AlgebraicSpaces B integerBase hZ}
    {U : BigFppfOver B integerBase hZ} (a : A ⟶ D) (p : D ⟶ schemeSpace U) : Prop :=
  ∀ ⦃V : BigFppfOver B integerBase hZ⦄ (v : V ⟶ U) ⦃A' D' : AlgebraicSpaces B integerBase hZ⦄
    (a' : A' ⟶ D') (iA : A' ⟶ A) (iD : D' ⟶ D) (p' : D' ⟶ schemeSpace V),
    IsPullback iD p' p (schemeSpaceMap v) → IsPullback iA (a' ≫ p') (a ≫ p) (schemeSpaceMap v) →
      a' ≫ iD = iA ≫ a →
        IsIso (Space.structureSharp B integerBase hZ a') ∧ IsZero (firstDirectImage B hZ a')

/-- **Condition (2) of Stacks 0E8A.** A morphism `a : A ⟶ D` of algebraic spaces over a scheme `U`
induces on every fibre the stable contraction of Stacks 0E7Q. At every field-valued point of `U`
the fibre of `A` is presented by a scheme. For all presentations of the fibres of `A` and `D` by
schemes, the morphism of schemes induced by `a` satisfies the conditions of Stacks 0E7Q. -/
def IsFibrewiseStableContraction {A D : AlgebraicSpaces B integerBase hZ}
    {U : BigFppfOver B integerBase hZ} (a : A ⟶ D) (p : D ⟶ schemeSpace U) : Prop :=
  ∀ P : Space.FieldValuedPoint B integerBase hZ (schemeSpace U).obj,
    (∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ A.obj),
      IsPullback q (yoneda.map v) (a ≫ p).hom (yonedaEquiv.symm P.value)) ∧
    ∀ ⦃V W : BigFppfOver B integerBase hZ⦄ (v : V ⟶ P.siteObject) (w : W ⟶ P.siteObject)
      (q : yoneda.obj V ⟶ A.obj) (r : yoneda.obj W ⟶ D.obj) (m : V ⟶ W),
      IsPullback q (yoneda.map v) (a ≫ p).hom (yonedaEquiv.symm P.value) →
      IsPullback r (yoneda.map w) p.hom (yonedaEquiv.symm P.value) →
      m ≫ w = v → yoneda.map m ≫ r = q ≫ a.hom →
        Stacks.Curves.StableModel.IsStableContraction
          ((BigFppfOver.toScheme B integerBase hZ).map v)
          ((BigFppfOver.toScheme B integerBase hZ).map w)
          ((BigFppfOver.toScheme B integerBase hZ).map m)

/-- **A stable model of genus `g`** (Stacks 0E8A). A morphism `c : X ⟶ Y` of total spaces of
families of curves lies over an isomorphism of bases `b`. The target `Y` is stable with fibres of
genus `g`, and `c` satisfies conditions (1) and (2) of Stacks 0E8A over the base of `Y`. -/
structure IsStableModel (g : ℕ) {X Y : CurveFamily B hZ} (b : X.base ⟶ Y.base)
    (c : X.total ⟶ Y.total) : Prop where
  isIso_base : IsIso b
  comp_toBase : c ≫ Y.toBase = X.toBase ≫ schemeSpaceMap b
  isStable : IsStableCurveFamily B hZ Y
  hasFibresOfGenus : Y.HasFibresOfGenus g
  universallyAcyclic : IsUniversallyAcyclicContraction B hZ c Y.toBase
  fibrewiseStable : IsFibrewiseStableContraction B hZ c Y.toBase

variable {B hZ}

/-- **Condition (1) of Stacks 0E8A is stable under base change.** If `a₀ : A₀ ⟶ D₀` over `U₀`
satisfies it and `a : A ⟶ D` over `U` is its base change along `u : U ⟶ U₀`, then `a` satisfies
it. -/
theorem IsUniversallyAcyclicContraction.of_isPullback {A D A₀ D₀ : AlgebraicSpaces B integerBase hZ}
    {U U₀ : BigFppfOver B integerBase hZ} {a : A ⟶ D} {p : D ⟶ schemeSpace U} {a₀ : A₀ ⟶ D₀}
    {p₀ : D₀ ⟶ schemeSpace U₀} (h : IsUniversallyAcyclicContraction B hZ a₀ p₀) (u : U ⟶ U₀)
    (jA : A ⟶ A₀) (jD : D ⟶ D₀) (hD : IsPullback jD p p₀ (schemeSpaceMap u))
    (hA : IsPullback jA (a ≫ p) (a₀ ≫ p₀) (schemeSpaceMap u)) (hc : a ≫ jD = jA ≫ a₀) :
    IsUniversallyAcyclicContraction B hZ a p := by
  intro V v A' D' a' iA iD p' hD' hA' hc'
  refine h (v ≫ u) a' (iA ≫ jA) (iD ≫ jD) p' ?_ ?_ ?_
  · rw [schemeSpaceMap_comp]
    exact hD'.paste_horiz hD
  · rw [schemeSpaceMap_comp]
    exact hA'.paste_horiz hA
  · rw [← Category.assoc, hc', Category.assoc, hc, Category.assoc]

/-- **Condition (2) of Stacks 0E8A is stable under base change.** If `a₀ : A₀ ⟶ D₀` over `U₀`
satisfies it and `a : A ⟶ D` over `U` is its base change along `u : U ⟶ U₀`, then `a` satisfies
it. A field-valued point of `U` is one of `U₀`, and the fibres there are the same. -/
theorem IsFibrewiseStableContraction.of_isPullback {A D A₀ D₀ : AlgebraicSpaces B integerBase hZ}
    {U U₀ : BigFppfOver B integerBase hZ} {a : A ⟶ D} {p : D ⟶ schemeSpace U} {a₀ : A₀ ⟶ D₀}
    {p₀ : D₀ ⟶ schemeSpace U₀} (h : IsFibrewiseStableContraction B hZ a₀ p₀) (u : U ⟶ U₀)
    (jA : A ⟶ A₀) (jD : D ⟶ D₀) (hD : IsPullback jD p p₀ (schemeSpaceMap u))
    (hA : IsPullback jA (a ≫ p) (a₀ ≫ p₀) (schemeSpaceMap u)) (hc : a ≫ jD = jA ≫ a₀) :
    IsFibrewiseStableContraction B hZ a p := by
  intro P
  let P₀ := Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap u).hom P
  have hval : yonedaEquiv.symm P₀.value = yonedaEquiv.symm P.value ≫ (schemeSpaceMap u).hom :=
    (yonedaEquiv_symm_naturality_right _ _ _).symm
  have hsqA := AlgebraicSpaces.isPullback_hom B integerBase hZ hA
  have hc' : a.hom ≫ jD.hom = jA.hom ≫ a₀.hom := congrArg (fun k => k.hom) hc
  obtain ⟨hex, huniv⟩ := h P₀
  refine ⟨?_, fun V W v w q r m hq hr hmw hmr => ?_⟩
  · obtain ⟨V, v, q₀, hq₀⟩ := hex
    rw [hval] at hq₀
    have hw : q₀ ≫ (a₀ ≫ p₀).hom =
        (yoneda.map v ≫ yonedaEquiv.symm P.value) ≫ (schemeSpaceMap u).hom := by
      rw [Category.assoc]
      exact hq₀.w
    refine ⟨V, v, hsqA.lift q₀ (yoneda.map v ≫ yonedaEquiv.symm P.value) hw,
      IsPullback.of_right ?_ (hsqA.lift_snd _ _ _) hsqA⟩
    rwa [hsqA.lift_fst]
  · refine huniv v w (q ≫ jA.hom) (r ≫ jD.hom) m ?_ ?_ hmw ?_
    · rw [hval]
      exact hq.paste_horiz hsqA
    · rw [hval]
      exact hr.paste_horiz (AlgebraicSpaces.isPullback_hom B integerBase hZ hD)
    · rw [← Category.assoc, hmr, Category.assoc, hc', Category.assoc]

/-- The square of total spaces of a morphism of families of curves `φ : X' ⟶ X`, read over the
bases of two families `Y'`, `Y` through isomorphisms `b'`, `b` of bases, is cartesian. -/
theorem isPullback_totalMap_of_isIso {X Y X' Y' : CurveFamily B hZ} (φ : X' ⟶ X) (ψ : Y' ⟶ Y)
    (b : X.base ⟶ Y.base) (b' : X'.base ⟶ Y'.base) [IsIso b] [IsIso b']
    (hb : b' ≫ ψ.baseMap = φ.baseMap ≫ b) :
    IsPullback φ.totalMap (X'.toBase ≫ schemeSpaceMap b') (X.toBase ≫ schemeSpaceMap b)
      (schemeSpaceMap ψ.baseMap) := by
  have : IsIso (schemeSpaceMap b) := Functor.map_isIso (schemeSpaceFunctor B integerBase hZ) b
  have : IsIso (schemeSpaceMap b') := Functor.map_isIso (schemeSpaceFunctor B integerBase hZ) b'
  refine φ.cartesian.paste_vert (IsPullback.of_vert_isIso ⟨?_⟩)
  rw [← schemeSpaceMap_comp, ← schemeSpaceMap_comp, hb]

/-- **Stable models are stable under base change** (the input of Stacks 0E8B). Let `c : X ⟶ Y` be
a stable model of genus `g` over `b`, and let `φ : X' ⟶ X` and `ψ : Y' ⟶ Y` be morphisms of
families of curves. Let `c' : X' ⟶ Y'` lie over an isomorphism `b'` of bases and be compatible with
`c` through `φ` and `ψ`. Then `c'` is a stable model of genus `g`. -/
theorem IsStableModel.of_hom {g : ℕ} {X Y X' Y' : CurveFamily B hZ} {b : X.base ⟶ Y.base}
    {c : X.total ⟶ Y.total} (h : IsStableModel B hZ g b c) (φ : X' ⟶ X) (ψ : Y' ⟶ Y)
    (b' : X'.base ⟶ Y'.base) [IsIso b'] (c' : X'.total ⟶ Y'.total)
    (hb : b' ≫ ψ.baseMap = φ.baseMap ≫ b) (hc : c' ≫ ψ.totalMap = φ.totalMap ≫ c)
    (hc' : c' ≫ Y'.toBase = X'.toBase ≫ schemeSpaceMap b') :
    IsStableModel B hZ g b' c' := by
  have := h.isIso_base
  have hA : IsPullback φ.totalMap (c' ≫ Y'.toBase) (c ≫ Y.toBase)
      (schemeSpaceMap ψ.baseMap) := by
    rw [hc', h.comp_toBase]
    exact isPullback_totalMap_of_isIso φ ψ b b' hb
  exact
    { isIso_base := inferInstance
      comp_toBase := hc'
      isStable := CurveFamily.isStableCurveFamily_of_hom ψ h.isStable
      hasFibresOfGenus := h.hasFibresOfGenus.of_hom ψ
      universallyAcyclic :=
        h.universallyAcyclic.of_isPullback ψ.baseMap φ.totalMap ψ.totalMap ψ.cartesian hA hc
      fibrewiseStable :=
        h.fibrewiseStable.of_isPullback ψ.baseMap φ.totalMap ψ.totalMap ψ.cartesian hA hc }

end AlgebraicGeometry.C1590Private

end
