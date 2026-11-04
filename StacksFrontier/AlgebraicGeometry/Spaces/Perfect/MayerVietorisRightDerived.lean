module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExactVanishing
public import StacksFrontier.Algebra.Homology.RightDerivedBiprod
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforwardTag
public import StacksFrontier.CategoryTheory.Abelian.PointwiseBiproductFunctor
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Homology.CompositeCollapse

/-!
# Mayer–Vietoris for the right derived functors of global sections

Let `(U ⊆ W, j_V : V ⟶ W)` be an elementary distinguished square of algebraic spaces over a
scheme `S` and let `P = U ×_W V`.  For a sheaf of `𝒪_W`-modules `F` the cohomology groups
`Hⁿ(W, F)`, `Hⁿ(U, F|_U)`, `Hⁿ(V, F|_V)` and `Hⁿ(P, F|_P)` — the right derived functors of
global sections — sit in the Mayer–Vietoris long exact sequence

`⋯ ⟶ Hⁿ(U, F) ⊕ Hⁿ(V, F) ⟶ Hⁿ(P, F) ⟶ Hⁿ⁺¹(W, F) ⟶ Hⁿ⁺¹(U, F) ⊕ Hⁿ⁺¹(V, F) ⟶ ⋯`

of [Stacks, Tag 0CRS].  In particular `Hⁿ⁺¹(W, F) = 0` as soon as `Hⁿ⁺¹(U, F|_U)`,
`Hⁿ⁺¹(V, F|_V)` and `Hⁿ(P, F|_P)` vanish.

The sequence is obtained directly in the language of `CategoryTheory.Functor.rightDerived`.  For
an additive functor `Γ` and a natural short exact sequence

`0 ⟶ M ⟶ Φ_U M ⊕ Φ_V M ⟶ Φ_P M ⟶ 0`

of endofunctors of an abelian category, the sequence stays short exact after applying `Γ` at an
injective `M`, because it splits there; so the long exact sequence of right derived functors of
a short complex of functors that is short exact on injectives applies to
`Γ ⟶ (Φ_U ⊞ Φ_V) ⋙ Γ ⟶ Φ_P ⋙ Γ`.  For an elementary distinguished square the natural sequence
is part (1) of [Stacks, Tag 08GW] with `Φ_Y = j_{Y,*}((-)|_Y)`, and the right derived functors of
`F ↦ Γ(W, j_{Y,*}F|_Y)` are those of `Γ(Y, -)` at `F|_Y`, because restriction along an étale
morphism is exact and preserves injectives ([Stacks, Tag 03F3]) and `Γ(W, j_{Y,*} -) = Γ(Y, -)`.

## Main definitions

* `AlgebraicGeometry.Space.rightDerivedGlobalSectionsAbRestrictPushIso`: for `j : Y ⟶ W` étale,
  the isomorphism `Rⁿ(Γ(W, j_* (-)|_Y))(F) ≅ Hⁿ(Y, F|_Y)`.

## Main results

* `CategoryTheory.PushforwardMayerVietoris.isZero_rightDerived_succ_of_natural_shortExact`:
  for a natural short exact sequence `0 ⟶ M ⟶ Φ_U M ⊕ Φ_V M ⟶ Φ_P M ⟶ 0`, `Rⁿ⁺¹Γ(X) = 0` as
  soon as `Rⁿ⁺¹(Φ_U ⋙ Γ)(X)`, `Rⁿ⁺¹(Φ_V ⋙ Γ)(X)` and `Rⁿ(Φ_P ⋙ Γ)(X)` vanish.
* `AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsAb_succ_of_eds`: for an elementary
  distinguished square, `Hⁿ⁺¹(W, F) = 0` as soon as `Hⁿ⁺¹(U, F|_U)`, `Hⁿ⁺¹(V, F|_V)` and
  `Hⁿ(P, F|_P)` vanish.

## References

* [Stacks Project, Tag 0CRS](https://stacks.math.columbia.edu/tag/0CRS)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂ u w

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

namespace PushforwardMayerVietoris

section Abstract

variable [Abelian A] [Abelian B] {ΦU ΦV ΦP : A ⥤ A}
  (ηU : 𝟭 A ⟶ ΦU) (ηV : 𝟭 A ⟶ ΦV) (cU : ΦU ⟶ ΦP) (cV : ΦV ⟶ ΦP)

/-- The composite of `(τ, σ) : E ⟶ Φ_U ⊞ Φ_V` with `(τ', σ') : Φ_U ⊞ Φ_V ⟶ E'` is
`τ ≫ τ' + σ ≫ σ'`. -/
private theorem pointwiseBiprod_lift_comp_desc {E E' : A ⥤ A} (τ : E ⟶ ΦU) (σ : E ⟶ ΦV)
    (τ' : ΦU ⟶ E') (σ' : ΦV ⟶ E') :
    Functor.pointwiseBiprod.lift ΦU ΦV τ σ ≫ Functor.pointwiseBiprod.desc ΦU ΦV τ' σ' =
      τ ≫ τ' + σ ≫ σ' := by
  ext X
  exact biprod.lift_desc

/-- The composite of `-(0, 𝟙) : Φ_V ⟶ Φ_U ⊞ Φ_V` with `(c_U, -c_V) : Φ_U ⊞ Φ_V ⟶ Φ_P` is
`c_V`. -/
theorem neg_lift_zero_id_comp_desc :
    (-(Functor.pointwiseBiprod.lift ΦU ΦV (0 : ΦV ⟶ ΦU) (𝟙 ΦV))) ≫
      Functor.pointwiseBiprod.desc ΦU ΦV cU (-cV) = cV := by
  rw [Preadditive.neg_comp, pointwiseBiprod_lift_comp_desc]
  simp

variable [HasInjectiveResolutions A] (Γ : A ⥤ B) [Γ.Additive] [ΦU.Additive] [ΦV.Additive]
  [ΦP.Additive]
  (hzero : ∀ X, biprod.lift (ηU.app X) (ηV.app X) ≫ biprod.desc (cU.app X) (-(cV.app X)) = 0)
  (hSES : ∀ X, (ShortComplex.mk _ _ (hzero X)).ShortExact)

omit [HasInjectiveResolutions A] [ΦU.Additive] [ΦV.Additive] [ΦP.Additive] in
include hzero in
/-- After whiskering by `Γ`, the composite of `(η_U, η_V) : 𝟭 ⟶ Φ_U ⊞ Φ_V` with
`(c_U, -c_V) : Φ_U ⊞ Φ_V ⟶ Φ_P` is zero. -/
theorem whiskerRight_biprodLift_comp_biprodDiff :
    Functor.whiskerRight (Functor.pointwiseBiprod.lift ΦU ΦV ηU ηV) Γ ≫
      Functor.whiskerRight (Functor.pointwiseBiprod.desc ΦU ΦV cU (-cV)) Γ = 0 := by
  ext X
  show Γ.map (biprod.lift (ηU.app X) (ηV.app X)) ≫ Γ.map (biprod.desc (cU.app X) (-cV.app X))
    = 0
  rw [← Γ.map_comp, hzero X, Γ.map_zero]

omit [HasInjectiveResolutions A] [ΦU.Additive] [ΦV.Additive] [ΦP.Additive] in
include hSES in
/-- At an injective object the Mayer–Vietoris sequence splits, so it stays short exact after
applying any additive functor. -/
theorem shortExact_whiskerRight_of_injective (X : A) [Injective X] :
    (NatTrans.appShortComplex (Functor.whiskerRight (Functor.pointwiseBiprod.lift ΦU ΦV ηU ηV) Γ)
      (Functor.whiskerRight (Functor.pointwiseBiprod.desc ΦU ΦV cU (-cV)) Γ)
      (whiskerRight_biprodLift_comp_biprodDiff ηU ηV cU cV Γ hzero) X).ShortExact :=
  ((hSES X).splittingOfInjective.map Γ).shortExact

/-- The higher right derived functors of `(Φ_U ⊞ Φ_V) ⋙ Γ` vanish where those of `Φ_U ⋙ Γ` and
of `Φ_V ⋙ Γ` do. -/
theorem isZero_rightDerived_pointwiseBiprod_comp (X : A) (n : ℕ)
    (hU : IsZero (((ΦU ⋙ Γ).rightDerived n).obj X))
    (hV : IsZero (((ΦV ⋙ Γ).rightDerived n).obj X)) :
    IsZero (((Functor.pointwiseBiprod ΦU ΦV ⋙ Γ).rightDerived n).obj X) := by
  have hz : Functor.whiskerRight (Functor.pointwiseBiprod.lift ΦU ΦV (𝟙 ΦU) (0 : ΦU ⟶ ΦV)) Γ ≫
      Functor.whiskerRight (Functor.pointwiseBiprod.desc ΦU ΦV (0 : ΦU ⟶ ΦV) (𝟙 ΦV)) Γ = 0 := by
    rw [← Functor.whiskerRight_comp, pointwiseBiprod_lift_comp_desc]
    simp
  refine isZero_rightDerived_of_isZero_of_isZero _ _ hz (fun Y _ => ?_) X n hU hV
  let s : (ShortComplex.mk (biprod.lift (𝟙 (ΦU.obj Y)) 0 : ΦU.obj Y ⟶ ΦU.obj Y ⊞ ΦV.obj Y)
      (biprod.desc 0 (𝟙 (ΦV.obj Y))) (by simp)).Splitting :=
    { r := biprod.fst
      s := biprod.inr
      f_r := by simp
      s_g := by simp
      id := by ext <;> simp }
  exact (s.map Γ).shortExact

/-- `Rⁿ` of the whiskering by `Γ` is functorial in the natural transformation. -/
private theorem rightDerived_whiskerRight_comp {F G H : A ⥤ A} [F.Additive] [G.Additive]
    [H.Additive] (a : F ⟶ G) (b : G ⟶ H) (n : ℕ) :
    NatTrans.rightDerived (Functor.whiskerRight (a ≫ b) Γ) n =
      NatTrans.rightDerived (Functor.whiskerRight a Γ) n ≫
        NatTrans.rightDerived (Functor.whiskerRight b Γ) n := by
  rw [Functor.whiskerRight_comp, NatTrans.rightDerived_comp]

include hSES in
/-- **Mayer–Vietoris vanishing.**  For a natural short exact sequence
`0 ⟶ M ⟶ Φ_U M ⊕ Φ_V M ⟶ Φ_P M ⟶ 0` and an additive functor `Γ`, `Rⁿ⁺¹Γ(X) = 0` as soon as
`Rⁿ⁺¹(Φ_U ⋙ Γ)(X)` and `Rⁿ⁺¹(Φ_V ⋙ Γ)(X)` vanish and `Rⁿ(Φ_V ⋙ Γ)(X) ⟶ Rⁿ(Φ_P ⋙ Γ)(X)` is
onto. -/
theorem isZero_rightDerived_succ_of_natural_shortExact_of_epi (X : A) (n : ℕ)
    (hU : IsZero (((ΦU ⋙ Γ).rightDerived (n + 1)).obj X))
    (hV : IsZero (((ΦV ⋙ Γ).rightDerived (n + 1)).obj X))
    (hP : Epi ((NatTrans.rightDerived (Functor.whiskerRight cV Γ) n).app X)) :
    IsZero ((Γ.rightDerived (n + 1)).obj X) := by
  have h := isZero_rightDerived_succ_of_epi (F := 𝟭 A ⋙ Γ)
    (Functor.whiskerRight (Functor.pointwiseBiprod.lift ΦU ΦV ηU ηV) Γ)
    (Functor.whiskerRight (Functor.pointwiseBiprod.desc ΦU ΦV cU (-cV)) Γ)
    (whiskerRight_biprodLift_comp_biprodDiff ηU ηV cU cV Γ hzero)
    (fun Y _ => shortExact_whiskerRight_of_injective ηU ηV cU cV Γ hzero hSES Y) X n
    (isZero_rightDerived_pointwiseBiprod_comp Γ X (n + 1) hU hV) (by
      have hc : NatTrans.rightDerived (Functor.whiskerRight cV Γ) n =
          NatTrans.rightDerived (Functor.whiskerRight
            (-(Functor.pointwiseBiprod.lift ΦU ΦV (0 : ΦV ⟶ ΦU) (𝟙 ΦV))) Γ) n ≫
            NatTrans.rightDerived
              (Functor.whiskerRight (Functor.pointwiseBiprod.desc ΦU ΦV cU (-cV)) Γ) n := by
        rw [← rightDerived_whiskerRight_comp, neg_lift_zero_id_comp_desc]
      rw [hc, NatTrans.comp_app] at hP
      exact epi_of_epi
        ((NatTrans.rightDerived (Functor.whiskerRight
          (-(Functor.pointwiseBiprod.lift ΦU ΦV (0 : ΦV ⟶ ΦU) (𝟙 ΦV))) Γ) n).app X) _)
  exact h

include hSES in
/-- **Mayer–Vietoris vanishing, vanishing form.**  `Rⁿ⁺¹Γ(X) = 0` as soon as
`Rⁿ⁺¹(Φ_U ⋙ Γ)(X)`, `Rⁿ⁺¹(Φ_V ⋙ Γ)(X)` and `Rⁿ(Φ_P ⋙ Γ)(X)` vanish. -/
theorem isZero_rightDerived_succ_of_natural_shortExact (X : A) (n : ℕ)
    (hU : IsZero (((ΦU ⋙ Γ).rightDerived (n + 1)).obj X))
    (hV : IsZero (((ΦV ⋙ Γ).rightDerived (n + 1)).obj X))
    (hP : IsZero (((ΦP ⋙ Γ).rightDerived n).obj X)) :
    IsZero ((Γ.rightDerived (n + 1)).obj X) :=
  isZero_rightDerived_succ_of_natural_shortExact_of_epi ηU ηV cU cV Γ hzero hSES X n hU hV
    ⟨fun _ _ _ => hP.eq_of_src _ _⟩

end Abstract

section AddCommGrp

variable [Abelian A] {ΦU ΦV ΦP : A ⥤ A}
  (ηU : 𝟭 A ⟶ ΦU) (ηV : 𝟭 A ⟶ ΦV) (cU : ΦU ⟶ ΦP) (cV : ΦV ⟶ ΦP)
  [HasInjectiveResolutions A] (Γ : A ⥤ AddCommGrpCat.{w}) [Γ.Additive] [ΦU.Additive]
  [ΦV.Additive] [ΦP.Additive]
  (hzero : ∀ X, biprod.lift (ηU.app X) (ηV.app X) ≫ biprod.desc (cU.app X) (-(cV.app X)) = 0)
  (hSES : ∀ X, (ShortComplex.mk _ _ (hzero X)).ShortExact)

include hSES in
/-- **Surjectivity on the first summand of a Mayer–Vietoris sequence.**  For a natural short
exact sequence `0 ⟶ M ⟶ Φ_U M ⊕ Φ_V M ⟶ Φ_P M ⟶ 0` with maps `(η_U, η_V)` and
`c_U - c_V`, and an additive functor `Γ` to abelian groups, the map
`Rⁿ(Γ)(X) ⟶ Rⁿ(Φ_U ⋙ Γ)(X)` induced by `η_U` is onto as soon as
`Rⁿ(Φ_V ⋙ Γ)(X) ⟶ Rⁿ(Φ_P ⋙ Γ)(X)` induced by `c_V` is. -/
theorem epi_rightDerived_whiskerRight_of_natural_shortExact (X : A) (n : ℕ)
    (hV : Epi ((NatTrans.rightDerived (Functor.whiskerRight cV Γ) n).app X)) :
    Epi ((NatTrans.rightDerived (Functor.whiskerRight ηU Γ) n).app X) := by
  have hE := exact_rightDerived_composableArrows₅
    (Functor.whiskerRight (Functor.pointwiseBiprod.lift ΦU ΦV ηU ηV) Γ)
    (Functor.whiskerRight (Functor.pointwiseBiprod.desc ΦU ΦV cU (-cV)) Γ)
    (whiskerRight_biprodLift_comp_biprodDiff ηU ηV cU cV Γ hzero)
    (fun Y _ => shortExact_whiskerRight_of_injective ηU ηV cU cV Γ hzero hSES Y)
    (injectiveResolution X) n
  have hex := (ShortComplex.ab_exact_iff _).1 (hE.exact 0)
  let inU := Functor.pointwiseBiprod.lift ΦU ΦV (𝟙 ΦU) (0 : ΦU ⟶ ΦV)
  let inV := -(Functor.pointwiseBiprod.lift ΦU ΦV (0 : ΦV ⟶ ΦU) (𝟙 ΦV))
  let pU := Functor.pointwiseBiprod.desc ΦU ΦV (𝟙 ΦU) (0 : ΦV ⟶ ΦU)
  have h1 : Functor.pointwiseBiprod.lift ΦU ΦV ηU ηV ≫ pU = ηU := by
    simp [pU, pointwiseBiprod_lift_comp_desc]
  have h2 : inU ≫ pU = 𝟙 ΦU := by
    simp [inU, pU, pointwiseBiprod_lift_comp_desc]
  have h3 : inV ≫ pU = 0 := by
    simp [inV, pU, Preadditive.neg_comp, pointwiseBiprod_lift_comp_desc]
  have h4 : inU ≫ Functor.pointwiseBiprod.desc ΦU ΦV cU (-cV) = cU := by
    simp [inU, pointwiseBiprod_lift_comp_desc]
  have h5 : inV ≫ Functor.pointwiseBiprod.desc ΦU ΦV cU (-cV) = cV :=
    neg_lift_zero_id_comp_desc cU cV
  have R : ∀ {F G H : A ⥤ A} [F.Additive] [G.Additive] [H.Additive] (a : F ⟶ G) (b : G ⟶ H)
      (y : ((F ⋙ Γ).rightDerived n).obj X),
      (NatTrans.rightDerived (Functor.whiskerRight b Γ) n).app X
          ((NatTrans.rightDerived (Functor.whiskerRight a Γ) n).app X y) =
        (NatTrans.rightDerived (Functor.whiskerRight (a ≫ b) Γ) n).app X y := by
    intro F G H _ _ _ a b y
    rw [rightDerived_whiskerRight_comp, NatTrans.comp_app, ConcreteCategory.comp_apply]
  rw [AddCommGrpCat.epi_iff_surjective] at hV ⊢
  intro x
  obtain ⟨y, hy⟩ := hV ((NatTrans.rightDerived (Functor.whiskerRight cU Γ) n).app X x)
  obtain ⟨w, hw⟩ := hex ((NatTrans.rightDerived (Functor.whiskerRight inU Γ) n).app X x -
      (NatTrans.rightDerived (Functor.whiskerRight inV Γ) n).app X y) (by
    show (NatTrans.rightDerived (Functor.whiskerRight
      (Functor.pointwiseBiprod.desc ΦU ΦV cU (-cV)) Γ) n).app X _ = 0
    rw [map_sub, R, R, h4, h5, hy, sub_self])
  refine ⟨w, ?_⟩
  change (NatTrans.rightDerived (Functor.whiskerRight
    (Functor.pointwiseBiprod.lift ΦU ΦV ηU ηV) Γ) n).app X w = _ at hw
  have hz : Functor.whiskerRight (0 : ΦV ⟶ ΦU) Γ = 0 :=
    NatTrans.ext (funext fun Y => Γ.map_zero _ _)
  rw [← h1, ← R, hw, map_sub, R, R, h2, h3, hz, NatTrans.rightDerived_zero,
    Functor.whiskerRight_id', NatTrans.rightDerived_id]
  simp

end AddCommGrp

end PushforwardMayerVietoris

end CategoryTheory

namespace AlgebraicGeometry.Space

open CategoryTheory.PushforwardMayerVietoris

-- Instance search otherwise tries the abelian structure of module sheaves at a module universe
-- `max (u + 1) ?w` first and gets stuck on the universe constraint.
attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  HasDerivedCategory.standard
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Cohomology of a restriction, read on the ambient space -/

section Restriction

variable {Y W : AlgebraicSpaces B S hS} (j : Y ⟶ W) (hj : IsEtale B S hS j.hom)

/-- **Cohomology of a restriction, read on the ambient space.**  For an étale morphism
`j : Y ⟶ W` the right derived functors of `F ↦ Γ(W, j_*(F|_Y))` are the cohomology of the
restriction: `Rⁿ(Γ(W, j_*(-)|_Y))(F) ≅ Hⁿ(Y, F|_Y)`. -/
def rightDerivedGlobalSectionsAbRestrictPushIso (F : Modules.{u, u} B S hS W.1 W.2) (n : ℕ) :
    (((etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j) ⋙
        globalSectionsAb B S hS W).rightDerived n).obj F ≅
      ((globalSectionsAb B S hS Y).rightDerived n).obj
        ((etaleModulePullback.{u, u} B S hS j hj).obj F) :=
  have := preservesInjectiveObjects_etaleModulePullback B S hS j hj
  (Functor.rightDerivedIsoOfNatIso
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
        (globalSectionsModulePushforwardIso B S hS j)) n).app F ≪≫
    Stacks.RightDerivedComp.objIso (etaleModulePullback.{u, u} B S hS j hj)
      (injectiveResolution F)
      (fun m hm => Functor.isZero_rightDerived_of_exact _ F m hm) (globalSectionsAb B S hS Y) n

end Restriction

/-! ### Mayer–Vietoris vanishing for an elementary distinguished square -/

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **Mayer–Vietoris vanishing for an elementary distinguished square.**  Let
`(U ⊆ W, j_V : V ⟶ W)` be an elementary distinguished square with intersection
`P = U ×_W V` and let `F` be an `𝒪_W`-module.  Then `Hⁿ⁺¹(W, F) = 0` as soon as the right
derived functors of `Γ(W, j_{Y,*}(-)|_Y)` vanish at `F` in degree `n + 1` for `Y = U, V` and in
degree `n` for `Y = P`. -/
theorem isZero_rightDerived_globalSectionsAb_succ_of_eds (F : Modules.{u, u} B S hS W.1 W.2)
    (n : ℕ)
    (hU : IsZero (((edsRestrictPushOpen B S hS hsq ⋙ globalSectionsAb B S hS W).rightDerived
        (n + 1)).obj F))
    (hV : IsZero (((edsRestrictPushEtale B S hS hsq ⋙ globalSectionsAb B S hS W).rightDerived
        (n + 1)).obj F))
    (hP : IsZero (((edsRestrictPushInter B S hS hsq ⋙ globalSectionsAb B S hS W).rightDerived
        n).obj F)) :
    IsZero (((globalSectionsAb B S hS W).rightDerived (n + 1)).obj F) :=
  isZero_rightDerived_succ_of_natural_shortExact (edsAdjOpen B S hS hsq).unit
    (edsAdjEtale B S hS hsq).unit
    (conjugateEquiv ((edsAdjOpen B S hS hsq).comp (edsLowerShriekAdjOpen B S hS hsq))
      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
      (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
        (edsLowerShriekAdjInter B S hS hsq)))
    (conjugateEquiv ((edsAdjEtale B S hS hsq).comp (edsLowerShriekAdjEtale B S hS hsq))
      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
      (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
        (edsLowerShriekAdjInter B S hS hsq)))
    (globalSectionsAb B S hS W) (zero_edsRestrictPushMayerVietorisLowerShriek B S hS hsq)
    (shortExact_edsRestrictPushMayerVietorisLowerShriek B S hS hsq) F n hU hV hP

end Square

end AlgebraicGeometry.Space

