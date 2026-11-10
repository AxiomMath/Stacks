module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftFirstCohomology

/-!
# The class of a torsor under a change of the coefficient universe

`Stacks.Sheaves.UniverseLift.sheafHOneAddEquiv` identifies `H¹(C, F)` with `H¹(C, F ⋙ ULift)`.
This file computes that identification on classes of torsors ([Stacks, Tag 03AJ]): **a torsor
under `F` and a torsor under the universe lift of `F` with the same sections, up to `ULift`,
and the same action have corresponding classes.**

## Main results

* `Stacks.Cohomology.Torsors.homEquiv_uliftConstantSheafIso_inv`: the identification of the
  lifted constant sheaf `ℤ` with the constant sheaf `ℤ` in the larger universe is the
  sheafification of the map `n ↦ (the section n of ℤ_C)`, lifted.
* `Stacks.Cohomology.Torsors.sheafHOneAddEquiv_torsorClass`: the main statement.

## Implementation notes

The proof is the one of `Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_eq_boundary_iff`
applied twice, as for restriction along a continuous functor: the class of a torsor `T` is the
boundary of the constant section `1` in its own extension, the universe lift is exact, so it
carries that extension to an extension of the lifted constant sheaf by the lifted coefficients,
and the lifted torsor embeds equivariantly into the lifted middle term as the fiber of `1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sheaves.UniverseLift

universe w w' s t v u

namespace Stacks.Cohomology.Torsors

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{max t s}]
  [HasSheafify J AddCommGrpCat.{t}] [HasSheafify J AddCommGrpCat.{max t s}]

attribute [local instance] preservesFiniteColimits_uliftSheafFunctor

/-- The constant presheaf `ℤ` in the larger universe, mapped to the universe lift of `ℤ_C`:
`n ↦ (the section n of ℤ_C)`, lifted. -/
def constantIntUliftUnit :
    (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{max t s} ℤ)) ⟶
      ((uliftSheafFunctor.{s, t} J).obj
        ((constantSheaf J AddCommGrpCat.{t}).obj (AddCommGrpCat.of (ULift.{t} ℤ)))).obj :=
  (Functor.const Cᵒᵖ).map (AddEquiv.toAddCommGrpIso (AddEquiv.ulift.trans
      (AddEquiv.ulift.trans AddEquiv.ulift.symm))).inv ≫
    (Functor.constComp Cᵒᵖ (AddCommGrpCat.of (ULift.{t} ℤ)) AddCommGrpCat.uliftFunctor.{s, t}).inv ≫
    Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ))))
      AddCommGrpCat.uliftFunctor.{s, t}

omit [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max t s}] [HasSheafify J AddCommGrpCat.{max t s}] in
/-- `Stacks.Cohomology.Torsors.constantIntUliftUnit` sends `1` to the lift of the section `1` of
`ℤ_C`. -/
theorem constantIntUliftUnit_app_one (U : Cᵒᵖ) :
    (constantIntUliftUnit.{s, t} J).app U ⟨1⟩ =
      ULift.up ((toSheafify J ((Functor.const Cᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{t} ℤ)))).app U ⟨1⟩) :=
  rfl

/-- The inverse of `Stacks.Sheaves.UniverseLift.uliftConstantSheafIso` is the sheafification of
`Stacks.Cohomology.Torsors.constantIntUliftUnit`. -/
theorem homEquiv_uliftConstantSheafIso_inv :
    (sheafificationAdjunction J AddCommGrpCat.{max t s}).homEquiv _ _
        (uliftConstantSheafIso.{s, t, v, u} J).inv = constantIntUliftUnit.{s, t} J := by
  have := preservesSheafification_uliftFunctor.{u, v, t, s} (J := J)
  have key : toSheafify J ((Functor.const Cᵒᵖ).obj
      (AddCommGrpCat.uliftFunctor.{s, t}.obj (AddCommGrpCat.of (ULift.{t} ℤ)))) =
      (Functor.constComp Cᵒᵖ (AddCommGrpCat.of (ULift.{t} ℤ))
          AddCommGrpCat.uliftFunctor.{s, t}).inv ≫
        Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{t} ℤ)))) AddCommGrpCat.uliftFunctor.{s, t} ≫
          ((constantCommuteCompose J AddCommGrpCat.uliftFunctor.{s, t}).hom.app
            (AddCommGrpCat.of (ULift.{t} ℤ))).hom := by
    calc toSheafify J ((Functor.const Cᵒᵖ).obj
          (AddCommGrpCat.uliftFunctor.{s, t}.obj (AddCommGrpCat.of (ULift.{t} ℤ))))
        = (Functor.constComp Cᵒᵖ (AddCommGrpCat.of (ULift.{t} ℤ))
              AddCommGrpCat.uliftFunctor.{s, t}).inv ≫
            (Functor.constComp Cᵒᵖ (AddCommGrpCat.of (ULift.{t} ℤ))
              AddCommGrpCat.uliftFunctor.{s, t}).hom ≫ toSheafify J _ := by
          rw [Iso.inv_hom_id_assoc]
      _ = (Functor.constComp Cᵒᵖ (AddCommGrpCat.of (ULift.{t} ℤ))
              AddCommGrpCat.uliftFunctor.{s, t}).inv ≫
            toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⋙
              AddCommGrpCat.uliftFunctor.{s, t}) ≫
            sheafifyMap J (Functor.constComp Cᵒᵖ (AddCommGrpCat.of (ULift.{t} ℤ))
              AddCommGrpCat.uliftFunctor.{s, t}).hom := by
          rw [toSheafify_naturality]
      _ = (Functor.constComp Cᵒᵖ (AddCommGrpCat.of (ULift.{t} ℤ))
              AddCommGrpCat.uliftFunctor.{s, t}).inv ≫
            (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj
                (AddCommGrpCat.of (ULift.{t} ℤ)))) AddCommGrpCat.uliftFunctor.{s, t} ≫
              (sheafifyComposeIso J AddCommGrpCat.uliftFunctor.{s, t}
                ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)))).inv) ≫
            sheafifyMap J (Functor.constComp Cᵒᵖ (AddCommGrpCat.of (ULift.{t} ℤ))
              AddCommGrpCat.uliftFunctor.{s, t}).hom := by
          rw [sheafComposeIso_inv_fac]
      _ = _ := by
        simp only [Category.assoc]
        rfl
  have hinv : ((constantCommuteCompose J AddCommGrpCat.uliftFunctor.{s, t}).hom.app
      (AddCommGrpCat.of (ULift.{t} ℤ))).hom ≫
      ((constantCommuteCompose J AddCommGrpCat.uliftFunctor.{s, t}).inv.app
        (AddCommGrpCat.of (ULift.{t} ℤ))).hom = 𝟙 _ := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id_app,
      ObjectProperty.FullSubcategory.id_hom]
  change toSheafify J _ ≫ sheafifyMap J ((Functor.const Cᵒᵖ).map _) ≫
    ((constantCommuteCompose J AddCommGrpCat.uliftFunctor.{s, t}).inv.app
      (AddCommGrpCat.of (ULift.{t} ℤ))).hom = _
  refine (toSheafify_naturality_assoc J _ _).symm.trans ?_
  rw [key]
  erw [Category.assoc, Category.assoc, hinv, Category.comp_id]
  rfl

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] [HasExt.{w'} (Sheaf J AddCommGrpCat.{max t s})]

/-- **The universe-lift identification of `H¹` on torsor classes.** Let `T` be a torsor under an
abelian sheaf `H` and `T'` a torsor under its universe lift, together with an equivariant
bijection from the sections of `T'` to the lifted sections of `T`. Then
`Stacks.Sheaves.UniverseLift.sheafHOneAddEquiv` carries the class of `T` to the class of `T'`. -/
theorem sheafHOneAddEquiv_torsorClass (H : Sheaf J AddCommGrpCat.{t}) (T : AbelianTorsor H)
    (T' : AbelianTorsor ((uliftSheafFunctor.{s, t} J).obj H))
    (β : T'.1.presheaf ⟶ T.1.presheaf ⋙ uliftFunctor.{s, t})
    (hβ : ∀ U, Function.Bijective (β.app U))
    (hact : ∀ (U : Cᵒᵖ) (h : H.obj.obj U) (x : T'.1.presheaf.obj U),
      β.app U (T'.1.act U (Multiplicative.ofAdd (ULift.up h)) x) =
        ULift.up (T.1.act U (Multiplicative.ofAdd h) (β.app U x).down)) :
    sheafHOneAddEquiv.{w, w', s, t, v, u} J H (torsorIsoClassesEquivH1 H (Quotient.mk _ T)) =
      torsorIsoClassesEquivH1 _ (Quotient.mk _ T') := by
  rw [sheafHOneAddEquiv_apply, Functor.mapExtAddHom_apply]
  let R := uliftSheafFunctor.{s, t} J
  let S := torsorPushoutComplex H T
  have hS : S.ShortExact := torsorPushoutComplex_shortExact H T
  have h0 : torsorIsoClassesEquivH1 H (Quotient.mk _ T) =
      (Abelian.Ext.mk₀ (((sheafificationAdjunction J AddCommGrpCat.{t}).homEquiv _ _).symm
        (constantUnit.{t, v, u} (J := J) (C := C)))).comp hS.extClass (zero_add 1) := by
    rw [constantUnit_adj_inverse, Abelian.Ext.mk₀_id_comp]
    rfl
  obtain ⟨i₀, hi₀, hinj₀, hfib₀⟩ :=
    (torsorIsoClassesEquivH1_eq_boundary_iff.{w, t, v, u} S hS
      (constantUnit.{t, v, u} (J := J) (C := C)) T).1 h0
  have key := (torsorIsoClassesEquivH1_eq_boundary_iff.{w', max t s, v, u} (S.map R)
    (hS.map_of_exact R)
    (constantIntUliftUnit.{s, t} J) T').2
    ⟨β ≫ Functor.whiskerRight i₀ uliftFunctor.{s, t}, fun U h x => ULift.down_injective <|
        (congrArg (fun z : ULift.{s} (T.1.presheaf.obj U) => i₀.app U z.down)
          (hact U h.down x)).trans (hi₀ U h.down (β.app U x).down),
      fun U => ULift.up_injective.comp ((hinj₀ U).comp
        (ULift.down_injective.comp (hβ U).injective)),
      fun U y => by
        have h1 := hfib₀ U y.down
        rw [constantUnit_app_one] at h1
        change ULift.up (S.g.hom.app U y.down) = ULift.up ((toSheafify J ((Functor.const Cᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{t} ℤ)))).app U ⟨1⟩) ↔
            ∃ x, ULift.up (i₀.app U (β.app U x).down) = y
        rw [ULift.up_inj, h1]
        refine ⟨fun ⟨s₀, hs₀⟩ => ?_, fun ⟨x, hx⟩ => ⟨(β.app U x).down, congrArg ULift.down hx⟩⟩
        obtain ⟨x, hx⟩ := (hβ U).surjective (ULift.up s₀)
        refine ⟨x, ?_⟩
        rw [hx]
        exact congrArg ULift.up hs₀⟩
  rw [show (uliftConstantSheafIso.{s, t, v, u} J).inv =
      ((sheafificationAdjunction J AddCommGrpCat.{max t s}).homEquiv _ _).symm
        (constantIntUliftUnit.{s, t} J) by
    rw [← homEquiv_uliftConstantSheafIso_inv]
    exact (Equiv.symm_apply_apply _ _).symm, h0,
    constantUnit_adj_inverse, Abelian.Ext.mk₀_id_comp]
  exact (congrArg (fun z => (Abelian.Ext.mk₀ _).comp z (zero_add 1))
    (Abelian.Ext.mapExactFunctor_extClass R hS)).trans key.symm

end Stacks.Cohomology.Torsors

end
