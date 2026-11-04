module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackModulesIsoDerivedPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.TwoIsoCoherenceOfToposHom

/-!
# Composites of derived pullback isomorphisms along an augmented simplicial ringed topos

This file proves three normalizations of composites of the composition isomorphisms of
Stacks 0D6D and of the derived pullback isomorphisms of 2-isomorphisms (Stacks 04IC), for
arbitrary morphisms of ringed topoi: each composite is the composition isomorphism along a fixed
bracketing followed by the derived pullback isomorphism of one explicit 2-isomorphism.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.TwoIso.degreeAugmentationTwoIso`: `b ∘ (g ∘ r) ≅ a_k` from
  `e ∘ d ≅ g ∘ r`, `b ∘ e ≅ a` and `a ∘ d ≅ a_k`.
* `AlgebraicGeometry.RingedToposHom.TwoIso.appendedTransitionTwoIso`: `(b ∘ (g' ∘ f)) ∘ r ≅ a_n`
  from `σ : b ∘ g ≅ b ∘ (g' ∘ f)` and `θ : b ∘ (g ∘ r) ≅ a_n`.
* `AlgebraicGeometry.RingedToposHom.TwoIso.realizedTransitionTwoIso`: `(b ∘ (g' ∘ f)) ∘ r ≅ a_n`
  from `τ : f ∘ r ≅ r' ∘ x`, `θ' : b ∘ (g' ∘ r') ≅ a_m` and `κ : a_m ∘ x ≅ a_n`.

## Main results

In the namespace `Stacks.Cohomology.DerivedBaseChangeOfToposHom`:

* `derivedPullbackCompComparison_comp_degreeAugmentationTwoIso`,
  `derivedPullbackCompComparison_comp_appendedTransitionTwoIso`,
  `derivedPullbackCompComparison_comp_realizedTransitionTwoIso`: each composite of composition
  isomorphisms and derived pullback isomorphisms is the composition isomorphism along one
  bracketing followed by the derived pullback isomorphism of the corresponding 2-isomorphism.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe vE uE wE vE' uE' wE' vC uC wC vC' uC' wC' vT uT wT vR uR wR
  vW uW wW

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

noncomputable section

namespace AlgebraicGeometry.RingedToposHom.TwoIso

variable {E : RingedTopos.{vE, uE, wE}} {E' : RingedTopos.{vE', uE', wE'}}
  {C : RingedTopos.{vC, uC, wC}} {C' : RingedTopos.{vC', uC', wC'}}
  {T : RingedTopos.{vT, uT, wT}} {R : RingedTopos.{vR, uR, wR}} {W : RingedTopos.{vW, uW, wW}}
  [E.J.HasSheafCompose (forget RingCat.{wE})] [E'.J.HasSheafCompose (forget RingCat.{wE'})]
  [C.J.HasSheafCompose (forget RingCat.{wC})] [C'.J.HasSheafCompose (forget RingCat.{wC'})]
  [T.J.HasSheafCompose (forget RingCat.{wT})] [R.J.HasSheafCompose (forget RingCat.{wR})]
  [W.J.HasSheafCompose (forget RingCat.{wW})]
  [E.J.HasSheafCompose (forget₂ CommRingCat.{wE} RingCat.{wE})]
  [E'.J.HasSheafCompose (forget₂ CommRingCat.{wE'} RingCat.{wE'})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
  [C'.J.HasSheafCompose (forget₂ CommRingCat.{wC'} RingCat.{wC'})]
  [T.J.HasSheafCompose (forget₂ CommRingCat.{wT} RingCat.{wT})]
  [R.J.HasSheafCompose (forget₂ CommRingCat.{wR} RingCat.{wR})]
  [W.J.HasSheafCompose (forget₂ CommRingCat.{wW} RingCat.{wW})]

/-- `b ∘ (g ∘ r) ≅ a_k`, from `s_D : e ∘ d ≅ g ∘ r`, `s_A : b ∘ e ≅ a` and `s_a : a ∘ d ≅ a_k`:
`b s_D⁻¹`, reassociation, `s_A d` and `s_a`. -/
def degreeAugmentationTwoIso {r : RingedToposHom E C} {g : RingedToposHom C T}
    {d : RingedToposHom E R} {e : RingedToposHom R T} {b : RingedToposHom T W}
    {a : RingedToposHom R W} {ak : RingedToposHom E W} (sD : TwoIso (e.comp d) (g.comp r))
    (sA : TwoIso (b.comp e) a) (aD : TwoIso (a.comp d) ak) :
    TwoIso (b.comp (g.comp r)) ak :=
  (sD.symm.whiskerRight b).trans ((associator d e b).trans ((sA.whiskerLeft d).trans aD))

/-- `(b ∘ (g' ∘ f)) ∘ r ≅ a_n`, from `σ : b ∘ g ≅ b ∘ (g' ∘ f)` and `θ : b ∘ (g ∘ r) ≅ a_n`:
`σ⁻¹ r`, reassociation and `θ`. -/
def appendedTransitionTwoIso {r : RingedToposHom E C} {f : RingedToposHom C C'}
    {g : RingedToposHom C T} {g' : RingedToposHom C' T} {b : RingedToposHom T W}
    {an : RingedToposHom E W} (σ : TwoIso (b.comp g) (b.comp (g'.comp f)))
    (θ : TwoIso (b.comp (g.comp r)) an) :
    TwoIso ((b.comp (g'.comp f)).comp r) an :=
  (σ.symm.whiskerLeft r).trans ((associator r g b).symm.trans θ)

/-- `(b ∘ (g' ∘ f)) ∘ r ≅ a_n`, from `τ : f ∘ r ≅ r' ∘ x`, `θ' : b ∘ (g' ∘ r') ≅ a_m` and
`κ : a_m ∘ x ≅ a_n`, through reassociations. -/
def realizedTransitionTwoIso {r : RingedToposHom E C} {r' : RingedToposHom E' C'}
    {f : RingedToposHom C C'} {x : RingedToposHom E E'} {g' : RingedToposHom C' T}
    {b : RingedToposHom T W} {am : RingedToposHom E' W} {an : RingedToposHom E W}
    (τ : TwoIso (f.comp r) (r'.comp x)) (θ' : TwoIso (b.comp (g'.comp r')) am)
    (κ : TwoIso (am.comp x) an) :
    TwoIso ((b.comp (g'.comp f)).comp r) an :=
  (associator r (g'.comp f) b).symm.trans
    (((associator r f g').symm.whiskerRight b).trans
      (((τ.whiskerRight g').whiskerRight b).trans
        (((associator x r' g').whiskerRight b).trans
          ((associator x (g'.comp r') b).trans ((θ'.whiskerLeft x).trans κ)))))

/-- The pullback isomorphism of the inverse of a 2-isomorphism is the inverse of its pullback
isomorphism. -/
theorem pullbackModulesIso_symm_of_hasWeakSheafify [E.J.HasSheafCompose (forget AddCommGrpCat.{wE})]
    [W.J.HasSheafCompose (forget AddCommGrpCat.{wW})]
    [HasWeakSheafify E.J AddCommGrpCat.{wE}] [E.J.WEqualsLocallyBijective AddCommGrpCat.{wE}]
    [HasWeakSheafify W.J AddCommGrpCat.{wW}] [W.J.WEqualsLocallyBijective AddCommGrpCat.{wW}]
    {f g : RingedToposHom E W} (s : TwoIso f g) :
    s.symm.pullbackModulesIso = s.pullbackModulesIso.symm := by
  have h := pullbackModulesIso_trans s s.symm
  rw [trans_symm_self, pullbackModulesIso_refl] at h
  have h' := congrArg Iso.hom h
  rw [Iso.refl_hom, Iso.trans_hom] at h'
  exact Iso.ext ((Iso.hom_comp_eq_id _).1 h'.symm)

/-- For `ω = A⁻¹ ≫ θ ≫ R⁻¹`, the composite `ω⁻¹ ≫ A⁻¹ ≫ θ` is `R`. -/
theorem symm_trans_symm_trans_eq {f g h k : RingedToposHom E W} (A : TwoIso k f) (θ : TwoIso k h)
    (R : TwoIso g h) : (A.symm.trans (θ.trans R.symm)).symm.trans (A.symm.trans θ) = R :=
  TwoIso.ext (by ext1; simp [TwoIso.trans, TwoIso.symm])

end AlgebraicGeometry.RingedToposHom.TwoIso

namespace Stacks.Cohomology.DerivedBaseChangeOfToposHom

open AlgebraicGeometry.RingedToposHom

variable {E : RingedTopos.{vE, uE, wE}} {E' : RingedTopos.{vE', uE', wE'}}
  {C : RingedTopos.{vC, uC, wC}} {C' : RingedTopos.{vC', uC', wC'}}
  {T : RingedTopos.{vT, uT, wT}} {R : RingedTopos.{vR, uR, wR}} {W : RingedTopos.{vW, uW, wW}}
  [E.J.HasSheafCompose (forget RingCat.{wE})] [E'.J.HasSheafCompose (forget RingCat.{wE'})]
  [C.J.HasSheafCompose (forget RingCat.{wC})] [C'.J.HasSheafCompose (forget RingCat.{wC'})]
  [T.J.HasSheafCompose (forget RingCat.{wT})] [R.J.HasSheafCompose (forget RingCat.{wR})]
  [W.J.HasSheafCompose (forget RingCat.{wW})]
  [E.J.HasSheafCompose (forget₂ CommRingCat.{wE} RingCat.{wE})]
  [E'.J.HasSheafCompose (forget₂ CommRingCat.{wE'} RingCat.{wE'})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
  [C'.J.HasSheafCompose (forget₂ CommRingCat.{wC'} RingCat.{wC'})]
  [T.J.HasSheafCompose (forget₂ CommRingCat.{wT} RingCat.{wT})]
  [R.J.HasSheafCompose (forget₂ CommRingCat.{wR} RingCat.{wR})]
  [W.J.HasSheafCompose (forget₂ CommRingCat.{wW} RingCat.{wW})]
  [E.J.HasSheafCompose (forget AddCommGrpCat.{wE})]
  [E'.J.HasSheafCompose (forget AddCommGrpCat.{wE'})]
  [C.J.HasSheafCompose (forget AddCommGrpCat.{wC})]
  [C'.J.HasSheafCompose (forget AddCommGrpCat.{wC'})]
  [T.J.HasSheafCompose (forget AddCommGrpCat.{wT})]
  [R.J.HasSheafCompose (forget AddCommGrpCat.{wR})]
  [W.J.HasSheafCompose (forget AddCommGrpCat.{wW})]
  [HasSheafify E.J AddCommGrpCat.{wE}] [E.J.WEqualsLocallyBijective AddCommGrpCat.{wE}]
  [HasSheafify E'.J AddCommGrpCat.{wE'}] [E'.J.WEqualsLocallyBijective AddCommGrpCat.{wE'}]
  [HasSheafify C.J AddCommGrpCat.{wC}] [C.J.WEqualsLocallyBijective AddCommGrpCat.{wC}]
  [HasSheafify C'.J AddCommGrpCat.{wC'}] [C'.J.WEqualsLocallyBijective AddCommGrpCat.{wC'}]
  [HasSheafify T.J AddCommGrpCat.{wT}] [T.J.WEqualsLocallyBijective AddCommGrpCat.{wT}]
  [HasSheafify R.J AddCommGrpCat.{wR}] [R.J.WEqualsLocallyBijective AddCommGrpCat.{wR}]
  [HasSheafify W.J AddCommGrpCat.{wW}] [W.J.WEqualsLocallyBijective AddCommGrpCat.{wW}]
  [HasSheafify E.J (Type wE)] [HasSheafify E'.J (Type wE')] [HasSheafify C.J (Type wC)]
  [HasSheafify C'.J (Type wC')] [HasSheafify T.J (Type wT)] [HasSheafify R.J (Type wR)]
  [HasSheafify W.J (Type wW)]

/-- **The degree-`k` comparison of a pullback along an augmentation, normalized.** The composite
`Lr^* Lg^* Lb^* ⟶ L(g ∘ r)^* Lb^* ⟶ L(e ∘ d)^* Lb^* ⟶ Ld^* Le^* Lb^* ⟶ Ld^* L(b ∘ e)^* ⟶ Ld^* La^*
⟶ L(a ∘ d)^* ⟶ La_k^*` of composition isomorphisms and derived pullback isomorphisms of
2-isomorphisms is the composition isomorphism along `b ∘ (g ∘ r)` followed by the derived pullback
isomorphism of `degreeAugmentationTwoIso`. -/
theorem derivedPullbackCompComparison_comp_degreeAugmentationTwoIso {r : RingedToposHom E C}
    {g : RingedToposHom C T} {d : RingedToposHom E R} {e : RingedToposHom R T}
    {b : RingedToposHom T W} {a : RingedToposHom R W} {ak : RingedToposHom E W}
    (sD : TwoIso (e.comp d) (g.comp r)) (sA : TwoIso (b.comp e) a) (aD : TwoIso (a.comp d) ak)
    (M : DerivedCategory (SheafOfModules.{wW} (SheafOfModules.Tensor.ringSheaf W.O))) :
    (derivedPullbackCompComparison r g).app ((derivedPullback b).obj M) ≫
        (derivedPullbackIsoOfTwoIso sD).inv.app ((derivedPullback b).obj M) ≫
        (derivedPullbackCompIso d e).inv.app ((derivedPullback b).obj M) ≫
        (derivedPullback d).map ((derivedPullbackCompComparison e b).app M) ≫
        (derivedPullback d).map ((derivedPullbackIsoOfTwoIso sA).hom.app M) ≫
        (derivedPullbackCompComparison d a).app M ≫ (derivedPullbackIsoOfTwoIso aD).hom.app M =
      (derivedPullbackCompComparison r g).app ((derivedPullback b).obj M) ≫
        (derivedPullbackCompComparison (g.comp r) b).app M ≫
        (derivedPullbackIsoOfTwoIso (TwoIso.degreeAugmentationTwoIso sD sA aD)).hom.app M := by
  have w₁ := derivedPullbackCompComparison_whiskerRight sD.symm b M
  have w₂ := derivedPullbackCompComparison_assoc_associator d e b M
  have w₃ := derivedPullbackCompComparison_whiskerLeft d sA M
  rw [derivedPullbackIsoOfTwoIso_symm] at w₁
  simp only [TwoIso.degreeAugmentationTwoIso, derivedPullbackIsoOfTwoIso_trans, Iso.trans_hom,
    NatTrans.comp_app]
  rw [reassoc_of% w₁, ← reassoc_of% w₃, ← reassoc_of% w₂, ← derivedPullbackCompIso_hom d e,
    Iso.inv_hom_id_app_assoc, Iso.symm_hom]

/-- **The derived transition along an appended 2-isomorphism, normalized.** `Lr^*` of the composite
`Lf^* Lg'^* Lb^* ⟶ L(g' ∘ f)^* Lb^* ⟶ L(b ∘ (g' ∘ f))^* ⟶ L(b ∘ g)^* ⟶ Lg^* Lb^*`, followed by
`Lr^* Lg^* Lb^* ⟶ L(b ∘ (g ∘ r))^* ⟶ La_n^*`, is the composition isomorphism along
`(b ∘ (g' ∘ f)) ∘ r` followed by the derived pullback isomorphism of
`appendedTransitionTwoIso`. -/
theorem derivedPullbackCompComparison_comp_appendedTransitionTwoIso {r : RingedToposHom E C}
    {f : RingedToposHom C C'} {g : RingedToposHom C T} {g' : RingedToposHom C' T}
    {b : RingedToposHom T W} {an : RingedToposHom E W}
    (σ : TwoIso (b.comp g) (b.comp (g'.comp f))) (θ : TwoIso (b.comp (g.comp r)) an)
    (M : DerivedCategory (SheafOfModules.{wW} (SheafOfModules.Tensor.ringSheaf W.O))) :
    (derivedPullback r).map ((derivedPullbackCompComparison f g').app ((derivedPullback b).obj M) ≫
          (derivedPullbackCompComparison (g'.comp f) b).app M ≫
          (derivedPullbackIsoOfTwoIso σ).inv.app M ≫ (derivedPullbackCompIso g b).inv.app M) ≫
        (derivedPullbackCompComparison r g).app ((derivedPullback b).obj M) ≫
        (derivedPullbackCompComparison (g.comp r) b).app M ≫
        (derivedPullbackIsoOfTwoIso θ).hom.app M =
      (derivedPullback r).map
          ((derivedPullbackCompComparison f g').app ((derivedPullback b).obj M)) ≫
        (derivedPullback r).map ((derivedPullbackCompComparison (g'.comp f) b).app M) ≫
        (derivedPullbackCompComparison r (b.comp (g'.comp f))).app M ≫
        (derivedPullbackIsoOfTwoIso (TwoIso.appendedTransitionTwoIso σ θ)).hom.app M := by
  have a₁ := derivedPullbackCompComparison_assoc_associator r g b M
  have w₁ := derivedPullbackCompComparison_whiskerLeft r σ.symm M
  rw [derivedPullbackIsoOfTwoIso_symm] at w₁
  have a₁' : (derivedPullbackCompComparison r (b.comp g)).app M ≫
      (derivedPullbackIsoOfTwoIso (TwoIso.associator r g b)).inv.app M =
        (derivedPullback r).map ((derivedPullbackCompIso g b).inv.app M) ≫
          (derivedPullbackCompComparison r g).app ((derivedPullback b).obj M) ≫
          (derivedPullbackCompComparison (g.comp r) b).app M := by
    have hc : (derivedPullbackCompComparison g b).app M ≫ (derivedPullbackCompIso g b).inv.app M =
        𝟙 _ := (derivedPullbackCompIso g b).hom_inv_id_app M
    rw [← cancel_epi ((derivedPullback r).map ((derivedPullbackCompIso g b).hom.app M))]
    simp only [derivedPullbackCompIso_hom]
    rw [← reassoc_of% a₁, ← Functor.map_comp_assoc, hc, CategoryTheory.Functor.map_id,
      Category.id_comp]
    simp only [Iso.hom_inv_id_app, Category.comp_id]
  simp only [TwoIso.appendedTransitionTwoIso, derivedPullbackIsoOfTwoIso_trans,
    derivedPullbackIsoOfTwoIso_symm, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% w₁, reassoc_of% a₁']
  simp only [Iso.symm_hom]

/-- **The realized derived transition, normalized.** The composite
`Lr^* Lf^* Lg'^* Lb^* ⟶ L(f ∘ r)^* ⟶ L(r' ∘ x)^* ⟶ Lx^* Lr'^*`, followed by `Lx^*` of
`Lr'^* Lg'^* Lb^* ⟶ L(b ∘ (g' ∘ r'))^* ⟶ La_m^*` and by `Lx^* La_m^* ⟶ L(a_m ∘ x)^* ⟶ La_n^*`, is
the composition isomorphism along `(b ∘ (g' ∘ f)) ∘ r` followed by the derived pullback
isomorphism of `realizedTransitionTwoIso`. -/
theorem derivedPullbackCompComparison_comp_realizedTransitionTwoIso {r : RingedToposHom E C}
    {r' : RingedToposHom E' C'} {f : RingedToposHom C C'} {x : RingedToposHom E E'}
    {g' : RingedToposHom C' T} {b : RingedToposHom T W} {am : RingedToposHom E' W}
    {an : RingedToposHom E W} (τ : TwoIso (f.comp r) (r'.comp x))
    (θ' : TwoIso (b.comp (g'.comp r')) am) (κ : TwoIso (am.comp x) an)
    (M : DerivedCategory (SheafOfModules.{wW} (SheafOfModules.Tensor.ringSheaf W.O))) :
    (derivedPullbackCompComparison r f).app ((derivedPullback g').obj ((derivedPullback b).obj M)) ≫
        (derivedPullbackIsoOfTwoIso τ).hom.app
          ((derivedPullback g').obj ((derivedPullback b).obj M)) ≫
        (derivedPullbackCompIso x r').inv.app
          ((derivedPullback g').obj ((derivedPullback b).obj M)) ≫
        (derivedPullback x).map
          ((derivedPullbackCompComparison r' g').app ((derivedPullback b).obj M) ≫
            (derivedPullbackCompComparison (g'.comp r') b).app M ≫
            (derivedPullbackIsoOfTwoIso θ').hom.app M) ≫
        (derivedPullbackCompComparison x am).app M ≫ (derivedPullbackIsoOfTwoIso κ).hom.app M =
      (derivedPullback r).map
          ((derivedPullbackCompComparison f g').app ((derivedPullback b).obj M)) ≫
        (derivedPullback r).map ((derivedPullbackCompComparison (g'.comp f) b).app M) ≫
        (derivedPullbackCompComparison r (b.comp (g'.comp f))).app M ≫
        (derivedPullbackIsoOfTwoIso (TwoIso.realizedTransitionTwoIso τ θ' κ)).hom.app M := by
  have R₁ := derivedPullbackCompComparison_assoc_associator x r' g' ((derivedPullback b).obj M)
  have R₂ := derivedPullbackCompComparison_assoc_associator x (g'.comp r') b M
  have R₃ := derivedPullbackCompComparison_whiskerLeft x θ' M
  have R₄ := derivedPullbackCompComparison_whiskerRight τ g' ((derivedPullback b).obj M)
  have R₅ := derivedPullbackCompComparison_whiskerRight (τ.whiskerRight g') b M
  have R₆ := derivedPullbackCompComparison_whiskerRight (TwoIso.associator x r' g') b M
  have R₇ := derivedPullbackCompComparison_assoc_associator r f g' ((derivedPullback b).obj M)
  have R₈ := derivedPullbackCompComparison_assoc_associator r (g'.comp f) b M
  have R₉ := derivedPullbackCompComparison_whiskerRight (TwoIso.associator r f g') b M
  have hw : (TwoIso.associator r f g').symm.whiskerRight b =
      ((TwoIso.associator r f g').whiskerRight b).symm := TwoIso.ext rfl
  simp only [TwoIso.realizedTransitionTwoIso, hw, derivedPullbackIsoOfTwoIso_trans,
    derivedPullbackIsoOfTwoIso_symm, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [← reassoc_of% R₃, ← reassoc_of% R₂, ← reassoc_of% R₁,
    ← derivedPullbackCompIso_hom x r', Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% R₈, Iso.hom_inv_id_app_assoc, ← reassoc_of% R₇, ← reassoc_of% R₉,
    Iso.hom_inv_id_app_assoc, reassoc_of% R₅, reassoc_of% R₄, reassoc_of% R₆]

/-- The derived pullback isomorphism of the inverse of a 2-isomorphism, in the form induced by the
inverse of its pullback isomorphism. -/
theorem derivedPullbackIsoOfTwoIso_symm_eq {f g : RingedToposHom E W} (s : TwoIso f g)
    [(pullbackOnHomotopy f).HasLeftDerivedFunctor (quasiIsoTarget (Y := W))]
    [(pullbackOnHomotopy g).HasLeftDerivedFunctor (quasiIsoTarget (Y := W))] :
    derivedPullbackIsoOfTwoIso s.symm =
      derivedPullbackIsoOfPullbackModulesIso s.pullbackModulesIso.symm := by
  rw [← TwoIso.pullbackModulesIso_symm_of_hasWeakSheafify]
  rfl

end Stacks.Cohomology.DerivedBaseChangeOfToposHom

end
