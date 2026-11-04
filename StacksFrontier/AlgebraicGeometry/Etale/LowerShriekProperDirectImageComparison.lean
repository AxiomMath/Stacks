module

public import StacksFrontier.AlgebraicGeometry.Etale.ModuleSheafDirectImageAcyclic
public import StacksFrontier.AlgebraicGeometry.Etale.ProperLowerShriekBaseChange
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompProperSupportIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompRightDerivedMap
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompRightDerivedBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Etale.ModuleSheafDirectImageAcyclicComplexes
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

import StacksCore.Tactic.StacksAttribute

/-!
# The map `g_! K ⟶ Rh_*(f_! K)` for `g = h ∘ f`, `f`, `g` locally quasi-finite, `h` proper

Consider a commutative triangle `f ≫ h = g` of morphisms of a big étale site, with `f` and `g`
locally quasi-finite and `h` proper, and a ring `Λ`. The direct images with compact support
`f_!` and `g_!` of [Stacks, Tag 0F6R] are exact ([Stacks, Tag 0F5F]), and Stacks 0F79 and 0F51
identify `g_! = h_! ∘ f_! = h_* ∘ f_!` on sheaves of `Λ`-modules. Functorially in
`K ∈ D(X_étale, Λ)` this gives the canonical map of [Stacks, Tag 0F7G]

`g_! K ⟶ Rh_*(f_! K)`,

which on a complex `K` is `g_! K = h_*(f_! K) ⟶ Rh_*(f_! K)`, the unit of `Rh_*`. It is an
isomorphism if (a) `K` is bounded below with torsion cohomology sheaves, or (b) `Λ` is a torsion
ring.

## Main definitions

* `AlgebraicGeometry.SmallEtale.fShriekCompPushforwardIso`: `g_! ≅ f_! ⋙ h_*` on abelian étale
  sheaves (Stacks 0F79 and 0F51).
* `AlgebraicGeometry.SmallEtale.fShriekModCompPushforwardIso`: its `Λ`-linear lift.
* `AlgebraicGeometry.SmallEtale.lowerShriekProperDirectImageMap`: the map `g_! ⟶ Rh_* ∘ f_!` of
  [Stacks, Tag 0F7G].

## Main results

* `AlgebraicGeometry.SmallEtale.isIso_lowerShriekProperDirectImageMap_app_of_isGE`: case (a).
* `AlgebraicGeometry.SmallEtale.isIso_lowerShriekProperDirectImageMap_of_natCast_eq_zero`:
  case (b).
* `AlgebraicGeometry.SmallEtale.isIso_lowerShriekProperDirectImageMap_app`: **[Stacks, Tag 0F7G]**.

## Implementation notes

The derived direct image `Rh_*` is an arbitrary right derived functor of the degreewise direct
image on the unbounded homotopy categories, with its unit, as in
`AlgebraicGeometry.SmallEtale.properBaseChangeMap` (the map of [Stacks, Tag 0F7B]); the lower
shrieks are taken on derived categories by `Functor.mapDerivedCategory`, being exact.

## References

* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
* [Stacks Project, Tag 0F79](https://stacks.math.columbia.edu/tag/0F79)
* [Stacks Project, Tag 0F51](https://stacks.math.columbia.edu/tag/0F51)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.SmallEtale

attribute [local instance] SmallEtale.isGrothendieckAbelian_sheaf_succ

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ] {X Y Z : B.Scheme}

/-- **`g_! ≅ h_* ∘ f_!` on abelian étale sheaves**, for `f ≫ h = g` with `f` and `g` locally
quasi-finite and `h` proper: Stacks 0F79, `g_! ≅ h_! ∘ f_!` with `h_!` the proper-support direct
image, followed by Stacks 0F51, `h_! = h_*`. -/
def fShriekCompPushforwardIso (f : X ⟶ Y) (h : Y ⟶ Z) (g : X ⟶ Z) (w : f ≫ h = g)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
    [IsProper (B.inclusion.map h)] :
    fShriekFunctor.{u, u} B g ≅ fShriekFunctor.{u, u} B f ⋙ etalePushforward.{u, u + 1} B h := by
  subst w
  exact fShriekCompProperIso B f h ≪≫
    Functor.isoWhiskerLeft _ (properSupportIsoPushforward.{u, u + 1} B h)

/-- **`g_! ≅ h_* ∘ f_!` on sheaves of `Λ`-modules**: the `Λ`-linear lift of
`AlgebraicGeometry.SmallEtale.fShriekCompPushforwardIso`. -/
def fShriekModCompPushforwardIso (f : X ⟶ Y) (h : Y ⟶ Z) (g : X ⟶ Z) (w : f ≫ h = g)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
    [IsProper (B.inclusion.map h)] :
    etaleModuleLift B Λ (fShriekFunctor.{u, u} B g) ≅
      etaleModuleLift B Λ (fShriekFunctor.{u, u} B f) ⋙ etalePushforwardMod B Λ h :=
  (etaleModuleLiftCompIso B Λ (fShriekFunctor.{u, u} B f) (etalePushforward.{u, u + 1} B h)
    (fShriekFunctor.{u, u} B g) (fShriekCompPushforwardIso B f h g w).symm).symm

/-- If `m • 1 = 0` in `Λ` with `m > 0`, every sheaf of `Λ`-modules is torsion: its underlying
abelian sheaf is annihilated by `m`. -/
theorem moduleTorsionSheafProperty_of_natCast_eq_zero (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    {S : B.Scheme} (M : ModuleSheaf.{u, u, u} B S Λ) :
    moduleTorsionSheafProperty.{u, u, u} B S Λ M := by
  unfold moduleTorsionSheafProperty
  intro U x
  refine ⟨⊤, (SmallEtale.topology B S.obj S.property).top_mem U, fun V g _ => ⟨m, hm, ?_⟩⟩
  change m • (M.obj.map g.op x : M.obj.obj (Opposite.op V)) = 0
  rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]

section Derived

variable (f : X ⟶ Y) (h : Y ⟶ Z) (g : X ⟶ Z) (w : f ≫ h = g)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  [IsProper (B.inclusion.map h)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Z Λ)]
  (RH : DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ) ⥤
    DerivedCategory (ModuleSheaf.{u, u, u} B Z Λ))
  (αH : (etalePushforwardMod B Λ h).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)

/-- **The map `g_! K ⟶ Rh_*(f_! K)` of [Stacks, Tag 0F7G]**, functorially in
`K ∈ D(X_étale, Λ)`, for a commutative triangle `f ≫ h = g` of morphisms of a big étale site with
`f` and `g` locally quasi-finite and `h` proper, a ring `Λ`, and a right derived functor `Rh_*`
(with unit `αH`) of the direct image on the unbounded homotopy categories of étale sheaves of
`Λ`-modules. On a complex `K` it is the identification `g_! K = h_*(f_! K)` of
`AlgebraicGeometry.SmallEtale.fShriekModCompPushforwardIso` (Stacks 0F79 and 0F51) followed by
the unit of `Rh_*` at `f_! K`; this is the map of complexes `g_! K = h_* f_! K ⟶ h_* I` of the
source, for `f_! K ⟶ I` a K-injective resolution. -/
def lowerShriekProperDirectImageMap :
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B g)).mapDerivedCategory ⟶
      (etaleModuleLift B Λ (fShriekFunctor.{u, u} B f)).mapDerivedCategory ⋙ RH :=
  Stacks.ExactCompDerived.map (etaleModuleLift B Λ (fShriekFunctor.{u, u} B f))
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B g)) (etalePushforwardMod B Λ h)
    (fShriekModCompPushforwardIso B Λ f h g w) RH αH

variable [RH.IsRightDerivedFunctor αH
  (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B Y Λ) (ComplexShape.up ℤ))]

/-- The map of [Stacks, Tag 0F7G] is invertible at a complex `M` as soon as the direct image
carries some K-injective resolution of `f_! M` to a quasi-isomorphism. -/
theorem isIso_lowerShriekProperDirectImageMap_app_Q_of_quasiIso
    (M : CochainComplex (ModuleSheaf.{u, u, u} B X Λ) ℤ)
    (hM : ∃ (J : CochainComplex (ModuleSheaf.{u, u, u} B Y Λ) ℤ)
      (s : ((etaleModuleLift B Λ (fShriekFunctor.{u, u} B f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M ⟶ J), QuasiIso s ∧ J.IsKInjective ∧
        QuasiIso (((etalePushforwardMod B Λ h).mapHomologicalComplex (ComplexShape.up ℤ)).map s)) :
    IsIso ((lowerShriekProperDirectImageMap B Λ f h g w RH αH).app (DerivedCategory.Q.obj M)) := by
  obtain ⟨J, s, _, hJ, hHs⟩ := hM
  have hu := Stacks.ExactCompDerived.isIso_unit_app_of_quasiIso_map.{u + 1}
    (etalePushforwardMod B Λ h) RH αH s hJ hHs
  have h₁ := (Stacks.ExactCompDerived.isIso_map_app_Qh_iff
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B f))
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B g)) (etalePushforwardMod B Λ h)
    (fShriekModCompPushforwardIso B Λ f h g w) RH αH
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)).2 hu
  exact (NatTrans.isIso_app_iff_of_iso _
    ((DerivedCategory.quotientCompQhIso (ModuleSheaf.{u, u, u} B X Λ)).app M)).1 h₁

/-- **[Stacks, Tag 0F7G], case (a)**: the map `g_! K ⟶ Rh_*(f_! K)` is invertible when `K` is
bounded below with torsion cohomology sheaves. Representing `K` by a bounded below complex `M`,
the cohomology sheaves `H^q(M)` are torsion, so `h_*` is acyclic on `f_!(H^q(M))`
(`AlgebraicGeometry.SmallEtale.isZero_rightDerived_etalePushforwardMod_fShriekMod`, proper base
change), and the composition comparison of bounded below derived functors gives a K-injective
resolution of `f_! M` which `h_*` carries to a quasi-isomorphism
(`Stacks.ExactCompDerived.exists_quasiIso_isKInjective_quasiIso_map_of_isStrictlyGE`). -/
theorem isIso_lowerShriekProperDirectImageMap_app_of_isGE
    [LocallyQuasiFinite (B.inclusion.map (f ≫ h))]
    (K : DerivedCategory (ModuleSheaf.{u, u, u} B X Λ)) (n : ℤ) [K.IsGE n]
    (hK : moduleTorsionCohomologyProperty.{u, u, w, u} B X Λ K) :
    IsIso ((lowerShriekProperDirectImageMap B Λ f h g w RH αH).app K) := by
  obtain ⟨M, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K n
  refine (NatTrans.isIso_app_iff_of_iso _ e).2
    (isIso_lowerShriekProperDirectImageMap_app_Q_of_quasiIso B Λ f h g w RH αH M ?_)
  refine Stacks.ExactCompDerived.exists_quasiIso_isKInjective_quasiIso_map_of_isStrictlyGE
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B f))
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B g)) (etalePushforwardMod B Λ h)
    (fShriekModCompPushforwardIso B Λ f h g w) M n fun q p hp => ?_
  have ht : moduleTorsionSheafProperty.{u, u, u} B X Λ (M.homology q) := by
    unfold moduleTorsionSheafProperty
    exact (Stacks.Torsion.torsionSheafProperty.{u + 1, u, u + 1}
      (SmallEtale.topology B X.obj X.property)).prop_of_iso
      ((forgetModuleSheaf.{u, u, u} B X Λ).mapIso
        ((DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
          (DerivedCategory.homologyFunctorFactors _ q).app M)) (hK q)
  exact isZero_rightDerived_etalePushforwardMod_fShriekMod B Λ f h (M.homology q) ht p hp

/-- **[Stacks, Tag 0F7G], case (b)**: over a torsion ring `Λ` the map `g_! K ⟶ Rh_*(f_! K)` is
invertible for every `K ∈ D(X_étale, Λ)`. Every sheaf of `Λ`-modules is torsion, so the terms of
`f_! M` are `h_*`-acyclic for every complex `M`
(`AlgebraicGeometry.SmallEtale.isZero_rightDerived_etalePushforwardMod_fShriekMod`), and such a
complex computes `Rh_*` on the unbounded derived category: locally on `Z` the fibres of `h` have
bounded dimension, so `Rh_*` has finite cohomological dimension there
(`AlgebraicGeometry.SmallEtale.quasiIso_etalePushforwardMod_map_of_rightAcyclic`, [Stacks, Tag
095U] and [Stacks, Tag 07K7]). -/
theorem isIso_lowerShriekProperDirectImageMap_of_natCast_eq_zero
    [LocallyQuasiFinite (B.inclusion.map (f ≫ h))] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0) :
    IsIso (lowerShriekProperDirectImageMap B Λ f h g w RH αH) := by
  refine Stacks.ExactCompDerived.isIso_map_of_forall _ _ _ _ RH αH fun P => ?_
  obtain ⟨M⟩ := P
  let F := etaleModuleLift B Λ (fShriekFunctor.{u, u} B f)
  obtain ⟨J, s, hJ, _⟩ :=
    Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian.{u + 1} _
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
  have hP : ∀ (i : ℤ) (p : ℕ), 0 < p → IsZero (((etalePushforwardMod B Λ h).rightDerived p).obj
      (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M).X i)) := fun i p hp =>
    isZero_rightDerived_etalePushforwardMod_fShriekMod B Λ f h (M.X i)
      (moduleTorsionSheafProperty_of_natCast_eq_zero B Λ m hm hΛ (M.X i)) p hp
  exact Stacks.ExactCompDerived.isIso_unit_app_of_quasiIso_map.{u + 1}
    (etalePushforwardMod B Λ h) RH αH s hJ
    (quasiIso_etalePushforwardMod_map_of_rightAcyclic B Λ h m hm hΛ hP s hJ)

/-- **[Stacks, Tag 0F7G].** Consider a commutative diagram of schemes `f ≫ h = g` (that is,
`g = h ∘ f`, with `f : X ⟶ Y`, `h : Y ⟶ Z` and `g : X ⟶ Z`) with `f` and `g` locally
quasi-finite and `h` proper. Let `Λ` be a ring. Functorially in `K ∈ D(X_étale, Λ)` there is a
canonical map `g_! K ⟶ Rh_*(f_! K)` in `D(Z_étale, Λ)`, namely
`AlgebraicGeometry.SmallEtale.lowerShriekProperDirectImageMap` (a natural transformation, for
any right derived functor `Rh_*` of the direct image). This map is an isomorphism if

* (a) `K` is bounded below and has torsion cohomology sheaves, or
* (b) `Λ` is a torsion ring.

Case (a) is `isIso_lowerShriekProperDirectImageMap_app_of_isGE`, case (b)
`isIso_lowerShriekProperDirectImageMap_of_natCast_eq_zero`. -/
@[stacks 0F7G]
theorem isIso_lowerShriekProperDirectImageMap_app
    (K : DerivedCategory (ModuleSheaf.{u, u, u} B X Λ))
    (hK : (∃ n : ℤ, K.IsGE n ∧ moduleTorsionCohomologyProperty.{u, u, w, u} B X Λ K) ∨
      ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) :
    IsIso ((lowerShriekProperDirectImageMap B Λ f h g w RH αH).app K) := by
  have : LocallyQuasiFinite (B.inclusion.map (f ≫ h)) := by rwa [w]
  rcases hK with ⟨n, hn, hK⟩ | ⟨m, hm, hΛ⟩
  · exact isIso_lowerShriekProperDirectImageMap_app_of_isGE B Λ f h g w RH αH K n hK
  · have := isIso_lowerShriekProperDirectImageMap_of_natCast_eq_zero B Λ f h g w RH αH m hm hΛ
    infer_instance

end Derived

end AlgebraicGeometry.SmallEtale

end
