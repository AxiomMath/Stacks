module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.SpreadingOut
public import StacksFrontier.RingTheory.SpreadingOut.LocalIsomorphism
import all StacksFrontier.RingTheory.SpreadingOut.LocalIsomorphism.AwayIsomorphism

/-!
# Spreading out morphisms into a target locally of finite presentation

Let `X` and `Y` be schemes over a base `S`, let `x : X` and `y : Y` be points lying over the same
point of `S`, and suppose we are given a map of local rings `φ : 𝒪_{Y, y} ⟶ 𝒪_{X, x}` compatible
with the structure maps to `𝒪_{S, s}`. Spreading out asks for an open neighbourhood `U` of `x` and
an `S`-morphism `f : U ⟶ Y` inducing `φ` on stalks.

Mathlib proves this when `Y ⟶ S` is locally of finite type and the germ map of `X` at `x` is
injective (`AlgebraicGeometry.spread_out_of_isGermInjective`). Here `Y ⟶ S` is locally of finite
presentation instead, and no hypothesis on `X` is needed.

## Main results

* `AlgebraicGeometry.exists_lift_of_finitePresentation`: a map `A ⟶ 𝒪_{X, x}` out of a finitely
  presented `R`-algebra, compatible with a map `R ⟶ Γ(X, U)`, lifts to `A ⟶ Γ(X, V)` on some
  affine `V` with `x ∈ V ≤ U`.
* `AlgebraicGeometry.spread_out_of_locallyOfFinitePresentation`: spreading out a map on stalks
  when `Y ⟶ S` is locally of finite presentation, with no hypothesis on `X`.
* `AlgebraicGeometry.spread_out_of_locallyOfFinitePresentation'`: the same, phrased for a morphism
  `Spec 𝒪_{X, x} ⟶ Y`.

## References

* [Stacks Project, Tag 0BX6](https://stacks.math.columbia.edu/tag/0BX6)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/--
Suppose `X` is a scheme, `x : X` a point, and `U` a neighbourhood of `x`.
Given a commutative diagram of `CommRingCat`
```
R ⟶ Γ(X, U)
↓    ↓
A ⟶ 𝒪_{X, x}
```
such that `A` is of finite presentation over `R`, we may lift `A ⟶ 𝒪_{X, x}` to some
`A ⟶ Γ(X, V)` on an affine neighbourhood `V ≤ U` of `x`.

No injectivity assumption on the germ maps of `X` is needed, unlike in
`AlgebraicGeometry.exists_lift_of_germInjective`.
-/
public theorem exists_lift_of_finitePresentation {R A : CommRingCat.{u}} {X : Scheme.{u}} {x : X}
    {U : X.Opens} (hxU : x ∈ U) (φ : A ⟶ X.presheaf.stalk x) (φRA : R ⟶ A) (φRX : R ⟶ Γ(X, U))
    (hφRA : RingHom.FinitePresentation φRA.hom)
    (e : φRA ≫ φ = φRX ≫ X.presheaf.germ U x hxU) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (φ' : A ⟶ Γ(X, V)) (i : V ≤ U), IsAffineOpen V ∧
      φ = φ' ≫ X.presheaf.germ V x hxV ∧ φRX ≫ X.presheaf.map i.hom.op = φRA ≫ φ' := by
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hxU₀, hU₀U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.2
  have iU₀U : U₀ ≤ U := hU₀U
  let : Algebra R Γ(X, U₀) := (φRX ≫ X.presheaf.map (homOfLE iU₀U).op).hom.toAlgebra
  let : Algebra R A := φRA.hom.toAlgebra
  let : Algebra R (X.presheaf.stalk x) := (φRA ≫ φ).hom.toAlgebra
  let : Algebra Γ(X, U₀) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxU₀⟩
  have : Algebra.FinitePresentation R A := hφRA
  have htower : IsScalarTower R Γ(X, U₀) (X.presheaf.stalk x) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    change (φRA ≫ φ).hom r = X.presheaf.germ U₀ x hxU₀ (X.presheaf.map (homOfLE iU₀U).op (φRX r))
    rw [e]
    simp [TopCat.Presheaf.germ_res_apply]
  have hloc : IsLocalization (hU₀.primeIdealOf ⟨x, hxU₀⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) := hU₀.isLocalization_stalk ⟨x, hxU₀⟩
  obtain ⟨t, ht, ψ, g, hgT, hgψ⟩ :=
    Stacks.SpreadingOut.LocalIsoSplitting.exists_mem_algHom_localizationAway_of_finitePresentation
      (R := R) (S := A) (T := Γ(X, U₀)) (Tm := X.presheaf.stalk x)
      (M := (hU₀.primeIdealOf ⟨x, hxU₀⟩).asIdeal.primeCompl)
      { φ.hom with commutes' := fun _ => rfl }
  have hxV : x ∈ X.basicOpen t := by
    rw [X.mem_basicOpen t x hxU₀]
    exact IsLocalization.map_units (X.presheaf.stalk x) (⟨t, ht⟩ :
      (hU₀.primeIdealOf ⟨x, hxU₀⟩).asIdeal.primeCompl)
  have := hU₀.isLocalization_basicOpen t
  let α : Localization.Away t ≃ₐ[Γ(X, U₀)] Γ(X, X.basicOpen t) :=
    IsLocalization.algEquiv (Submonoid.powers t) _ _
  have hres : ∀ s : Γ(X, U₀),
      X.presheaf.germ (X.basicOpen t) x hxV
        (X.presheaf.map (homOfLE (X.basicOpen_le t)).op s) =
      X.presheaf.germ U₀ x hxU₀ s := fun s => by
    rw [TopCat.Presheaf.germ_res_apply]
  have hmap : ∀ s : Γ(X, U),
      X.presheaf.map (homOfLE (X.basicOpen_le t)).op (X.presheaf.map (homOfLE iU₀U).op s) =
      X.presheaf.map (homOfLE ((X.basicOpen_le t).trans iU₀U)).op s := fun s => by
    rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
    rfl
  have hα : ∀ z : Localization.Away t,
      X.presheaf.germ (X.basicOpen t) x hxV (α z) = g z := by
    have key : ((X.presheaf.germ (X.basicOpen t) x hxV).hom.comp
        (α : Localization.Away t →+* Γ(X, X.basicOpen t))) = (g : Localization.Away t →+* _) := by
      refine IsLocalization.ringHom_ext (Submonoid.powers t) ?_
      ext s
      change X.presheaf.germ (X.basicOpen t) x hxV
          (α (algebraMap Γ(X, U₀) (Localization.Away t) s)) =
        g (algebraMap Γ(X, U₀) (Localization.Away t) s)
      rw [α.commutes s, hgT s]
      exact hres s
    exact fun z => congrFun (congrArg (fun h : Localization.Away t →+* _ => h.toFun) key) z
  refine ⟨X.basicOpen t, hxV,
    CommRingCat.ofHom ((α : Localization.Away t →+* Γ(X, X.basicOpen t)).comp
      (ψ : A →+* Localization.Away t)),
    (X.basicOpen_le t).trans iU₀U, hU₀.basicOpen t, ?_, ?_⟩
  · ext a
    change φ a = X.presheaf.germ (X.basicOpen t) x hxV (α (ψ a))
    rw [hα (ψ a)]
    exact (congrArg (fun h : A →ₐ[R] X.presheaf.stalk x => h a) hgψ).symm
  · ext r
    change X.presheaf.map (homOfLE ((X.basicOpen_le t).trans iU₀U)).op (φRX r) = α (ψ (φRA r))
    have : ψ (φRA r) = algebraMap Γ(X, U₀) (Localization.Away t) (algebraMap R Γ(X, U₀) r) := by
      rw [← IsScalarTower.algebraMap_apply]
      exact ψ.commutes r
    rw [this, α.commutes]
    change _ = X.presheaf.map (homOfLE (X.basicOpen_le t)).op
      (X.presheaf.map (homOfLE iU₀U).op (φRX r))
    exact (hmap _).symm

/--
Given `S`-schemes `X Y` and points `x : X`, `y : Y` over the same point of `S`, and a diagram of
`S`-schemes
```
Spec 𝒪_{X, x} ⟶ X
    |
  Spec(φ)
    ↓
Spec 𝒪_{Y, y} ⟶ Y
```
the map `Spec(φ)` spreads out to an `S`-morphism on an open subscheme `U ⊆ X`,
```
Spec 𝒪_{X, x} ⟶ U ⊆ X
    |             |
  Spec(φ)         |
    ↓             ↓
Spec 𝒪_{Y, y} ⟶ Y
```
provided that `Y` is locally of finite presentation over `S`. No hypothesis on `X` is needed,
unlike in `AlgebraicGeometry.spread_out_of_isGermInjective`.
-/
public theorem spread_out_of_locallyOfFinitePresentation
    {X Y S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) [LocallyOfFinitePresentation sY]
    {x : X} {y : Y} (e : sX x = sY y) (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x)
    (h : sY.stalkMap y ≫ φ =
      S.presheaf.stalkSpecializes (Inseparable.of_eq e).specializes ≫ sX.stalkMap x) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (f : U.toScheme ⟶ Y),
      Spec.map φ ≫ Y.fromSpecStalk y = U.fromSpecStalkOfMem x hxU ≫ f ∧
      f ≫ sY = U.ι ≫ sX := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU₀, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (sX x)) isOpen_univ
  have hxU : sX x ∈ U := hxU₀
  have hyU : sY y ∈ U := e ▸ hxU
  obtain ⟨_, ⟨V : Y.Opens, hV, rfl⟩, hyV₀, iVU₀⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyU (sY ⁻¹ᵁ U).2
  have hyV : y ∈ V := hyV₀
  have iVU : V ≤ sY ⁻¹ᵁ U := iVU₀
  have hcomm : sY.appLE U V iVU ≫ Y.presheaf.germ V y hyV ≫ φ =
      sX.app U ≫ X.presheaf.germ (sX ⁻¹ᵁ U) x hxU :=
    calc sY.appLE U V iVU ≫ Y.presheaf.germ V y hyV ≫ φ
        = sY.app U ≫ (Y.presheaf.map (homOfLE iVU).op ≫ Y.presheaf.germ V y hyV) ≫ φ := by
          rw [Scheme.Hom.appLE]; simp only [Category.assoc]
      _ = sY.app U ≫ Y.presheaf.germ (sY ⁻¹ᵁ U) y hyU ≫ φ := by
          rw [TopCat.Presheaf.germ_res]
      _ = (S.presheaf.germ U (sY y) hyU ≫ sY.stalkMap y) ≫ φ := by
          rw [Scheme.Hom.germ_stalkMap sY U y hyU]; simp only [Category.assoc]
      _ = S.presheaf.germ U (sY y) hyU ≫
            S.presheaf.stalkSpecializes (Inseparable.of_eq e).specializes ≫ sX.stalkMap x := by
          rw [Category.assoc, h]
      _ = S.presheaf.germ U (sX x) hxU ≫ sX.stalkMap x := by
          rw [← Category.assoc,
            S.presheaf.germ_stalkSpecializes hyU (Inseparable.of_eq e).specializes]
      _ = sX.app U ≫ X.presheaf.germ (sX ⁻¹ᵁ U) x hxU := Scheme.Hom.germ_stalkMap sX U x hxU
  obtain ⟨W, hxW, φ', i, hW, h₁, h₂⟩ :=
    exists_lift_of_finitePresentation (R := Γ(S, U)) (A := Γ(Y, V)) (U := sX ⁻¹ᵁ U) (x := x) hxU
      (Y.presheaf.germ _ y hyV ≫ φ) (sY.appLE U V iVU) (sX.app U)
      (sY.finitePresentation_appLE hU hV _) hcomm
  have hfsV : Spec.map (Y.presheaf.germ V y hyV) ≫ hV.fromSpec = Y.fromSpecStalk y :=
    (rfl : hV.fromSpecStalk hyV = Spec.map (Y.presheaf.germ V y hyV) ≫ hV.fromSpec).symm.trans
      (hV.fromSpecStalk_eq_fromSpecStalk hyV)
  refine ⟨W, hxW, W.toSpecΓ ≫ Spec.map φ' ≫ hV.fromSpec, ?_, ?_⟩
  · rw [W.fromSpecStalkOfMem_toSpecΓ_assoc x hxW, ← Spec.map_comp_assoc, ← h₁,
      Spec.map_comp, Category.assoc, hfsV]
  · simp only [Category.assoc]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec sY hU hV iVU, ← Spec.map_comp_assoc, ← h₂,
      ← Scheme.Hom.appLE, ← hW.isoSpec_hom, IsAffineOpen.SpecMap_appLE_fromSpec sX hU hW i,
      ← Iso.eq_inv_comp, IsAffineOpen.isoSpec_inv_ι_assoc]

/--
Given `S`-schemes `X Y`, a point `x : X`, and an `S`-morphism `φ : Spec 𝒪_{X, x} ⟶ Y`, we may
spread it out to an `S`-morphism `f : U ⟶ Y` on an open neighbourhood `U` of `x`, provided that
`Y` is locally of finite presentation over `S`. No hypothesis on `X` is needed, unlike in
`AlgebraicGeometry.spread_out_of_isGermInjective'`.
-/
public theorem spread_out_of_locallyOfFinitePresentation'
    {X Y S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) [LocallyOfFinitePresentation sY]
    {x : X} (φ : Spec (X.presheaf.stalk x) ⟶ Y)
    (h : φ ≫ sY = X.fromSpecStalk x ≫ sX) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (f : U.toScheme ⟶ Y),
      φ = U.fromSpecStalkOfMem x hxU ≫ f ∧ f ≫ sY = U.ι ≫ sX := by
  have := spread_out_of_locallyOfFinitePresentation sX sY ?_ (Scheme.stalkClosedPointTo φ) ?_
  · simpa only [Scheme.Spec_stalkClosedPointTo_fromSpecStalk] using this
  · refine .trans ?_
      (Scheme.Hom.comp_apply φ sY (IsLocalRing.closedPoint (X.presheaf.stalk x)))
    rw [h, Scheme.Hom.comp_apply (X.fromSpecStalk x) sX
      (IsLocalRing.closedPoint (X.presheaf.stalk x)), Scheme.fromSpecStalk_closedPoint]
  · apply Spec.map_injective
    rw [← cancel_mono (S.fromSpecStalk _)]
    simpa only [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

end AlgebraicGeometry

end
