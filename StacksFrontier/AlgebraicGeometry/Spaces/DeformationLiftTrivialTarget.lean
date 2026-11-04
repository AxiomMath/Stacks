module

public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftActionSheaf

/-!
# Infinitesimal deformations of maps into a trivial thickening

[Stacks Project, Tag 061D] is the special case `Y = Y'` of Lemmas 0618, 04D0, 061A and 061C:
the target thickening is the trivial thickening `Y ⊂ Y`.  Then

* the map `A : a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` is always zero, since `𝒞_{Y/Y}` vanishes
  (`AlgebraicGeometry.Space.isZero_conormalModule_top`);
* the sheaf of Lemma 061A is the rule `U' ↦ {a' : U' ⟶ Y over B with a'|_U = a|_U}`, condition
  (3) being vacuous (`AlgebraicGeometry.Space.conormalLiftSubfunctor_eq_liftSubfunctor_of_eq_top`);
* the sheaf `SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` acts on it, by the action of Lemma 061C
  carried along that equality.  The trivial thickening is a first order thickening
  (`AlgebraicGeometry.Space.isFirstOrderThickening_of_eq_top`), so the action of 061C is
  available with no hypothesis on the target.

The trivial thickening `Y ⊂ Y'` with `Y = Y'` is the top closed subspace `H = ⊤` of `Y'`; it is
carried as the hypothesis `H = ⊤` on an arbitrary thickening `H` of `Y'`.

## Main definitions

* `AlgebraicGeometry.Space.liftSubfunctorEquivOfEqTop`: for `H = ⊤`, the sections of the sheaf of
  lifts over `U'` are the sections of the sheaf 061B over `U'`.
* `AlgebraicGeometry.Space.liftSheafAddActionOfEqTop`: the action of the sections of
  `SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` over `U'` on the sections of the sheaf of lifts.

## Main results

* `AlgebraicGeometry.Space.liftSubfunctor_remark_of_eq_top`: **[Stacks Project, Tag 061D]**.

## References

* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 061A](https://stacks.math.columbia.edu/tag/061A)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

/-- **The trivial thickening is a first order thickening.**  The top closed subspace `H = ⊤` of
`Y'` is a first order thickening of `Y'`. -/
theorem isFirstOrderThickening_of_eq_top {Y' : AlgebraicSpaces C S hS} {H : Subfunctor Y'.obj}
    (hH : IsThickening C S hS Y' H) (hHtop : H = ⊤) : IsFirstOrderThickening C S hS Y' H := by
  subst hHtop
  refine ⟨hH, fun U => ?_⟩
  have hret : (ObjectProperty.homMk (inv (⊤ : Subfunctor Y'.1).ι) :
      Y' ⟶ (⟨(⊤ : Subfunctor Y'.1).toFunctor, hH.1.1⟩ : AlgebraicSpaces C S hS)) ≫
        ObjectProperty.homMk (⊤ : Subfunctor Y'.1).ι = 𝟙 Y' :=
    ObjectProperty.hom_ext _ (IsIso.inv_hom_id _)
  rw [definingIdealAt_eq_bot_of_retraction C S hS Y' ⟨⊤, hH.1⟩ _ hret (op U)]
  exact zero_pow (M₀ := Ideal ((smallEtaleRingedTopos C S hS Y').O.obj.obj (op U))) two_ne_zero

variable {X' Y' T : AlgebraicSpaces C S hS} {G : Subfunctor X'.obj} {H : Subfunctor Y'.obj}
  (hG : IsThickening C S hS X' G) (hH : IsThickening C S hS Y' H)
  (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
  (a : IsThickening.space C S hS hG ⟶ IsThickening.space C S hS hH)
  (A : (modulePullback C S hS a).obj (conormalModule C S hS Y' ⟨H, hH.1⟩) ⟶
    conormalModule C S hS X' ⟨G, hG.1⟩)

/-- **For `Y = Y'` the map `A` is always zero.** -/
theorem eq_zero_of_eq_top (hHtop : H = ⊤) :
    letI := Preadditive.homGroup (C := Modules.{u, u} C S hS (IsThickening.space C S hS hG).1
      (IsThickening.space C S hS hG).2)
      ((modulePullback C S hS a).obj (conormalModule C S hS Y' ⟨H, hH.1⟩))
      (conormalModule C S hS X' ⟨G, hG.1⟩)
    A = 0 := by
  subst hHtop
  have hadd := modulePullback_additive a
  exact (@Functor.map_isZero _ _ _ _ _ _ _
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ hadd) _
    (isZero_conormalModule_top C S hS Y')).eq_of_src _ _

/-- For `Y = Y'` the sections over `U'` of the sheaf of lifts
(`U' ↦ {a' : U' ⟶ Y over B with a'|_U = a|_U}`) are the sections over `U'` of the sheaf of
[Stacks Project, Tag 061B]. -/
def liftSubfunctorEquivOfEqTop (hHtop : H = ⊤) (U' : SpacesEtale C S hS X') :
    (liftSubfunctor C S hS hG hH pX' pY' a).obj (op U') ≃
      (conormalLiftSubfunctor C S hS hG hH pX' pY' a A).obj (op U') :=
  Equiv.subtypeEquivRight fun x => Iff.of_eq (congrArg (fun F => x ∈ F.obj (op U'))
    (conormalLiftSubfunctor_eq_liftSubfunctor_of_eq_top C S hS hG hH pX' pY' a A hHtop).symm)

/-- The equivalence `AlgebraicGeometry.Space.liftSubfunctorEquivOfEqTop` does not change the
underlying morphism `U' ⟶ Y'`. -/
@[simp]
theorem coe_liftSubfunctorEquivOfEqTop (hHtop : H = ⊤) (U' : SpacesEtale C S hS X')
    (s : (liftSubfunctor C S hS hG hH pX' pY' a).obj (op U')) :
    (liftSubfunctorEquivOfEqTop C S hS hG hH pX' pY' a A hHtop U' s).1 = s.1 :=
  rfl

variable {hG hH} (hG₁ : IsFirstOrderThickening C S hS X' G)

/-- **The action of [Stacks Project, Tag 061D].**  For `Y = Y'`, the sections over `U'` of the
sheaf `SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` (read as maps `a|_U^*Ω_{Y/B} ⟶ 𝒞_{U/U'}`) act on
the sections over `U'` of the sheaf of lifts `U' ↦ {a' : U' ⟶ Y over B with a'|_U = a|_U}`: the
action of [Stacks Project, Tag 061C] (`AlgebraicGeometry.Space.conormalLiftSheafAddAction`)
carried along `AlgebraicGeometry.Space.liftSubfunctorEquivOfEqTop`. -/
@[instance_reducible]
def liftSheafAddActionOfEqTop (hHtop : H = ⊤) (U' : SpacesEtale C S hS X') :
    AddAction (conormalLiftActionHom C S hS hG hH pY' a U')
      ((liftSubfunctor C S hS hG hH pX' pY' a).obj (op U')) :=
  letI := conormalLiftSheafAddAction C S hS pX' pY' a A hG₁
    (isFirstOrderThickening_of_eq_top C S hS hH hHtop) U'
  (liftSubfunctorEquivOfEqTop C S hS hG hH pX' pY' a A hHtop U').addAction
    (conormalLiftActionHom C S hS hG hH pY' a U')

/-- The action of [Stacks Project, Tag 061D] is the action `θ · a'` of
[Stacks Project, Tag 0CK6] used by Lemma 061C. -/
theorem coe_liftSheafAddActionOfEqTop_vadd (hHtop : H = ⊤) (U' : SpacesEtale C S hS X')
    (θ : conormalLiftActionHom C S hS hG hH pY' a U')
    (s : (liftSubfunctor C S hS hG hH pX' pY' a).obj (op U')) :
    letI := liftSheafAddActionOfEqTop C S hS pX' pY' a A hG₁ hHtop U'
    (θ +ᵥ s).1 = (conormalLiftAction C S hS pX' pY' a A hG₁
        (isFirstOrderThickening_of_eq_top C S hS hH hHtop) U' θ
        (liftSubfunctorEquivOfEqTop C S hS hG hH pX' pY' a A hHtop U' s)).1 :=
  rfl

/-- **Deformations of maps into a trivial thickening.**  The special case `Y = Y'` of Lemmas
0618, 04D0, 061A and 061C (the target thickening is the trivial one, `H = ⊤`):
1. the map `A : a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` is always zero;
2. the sheaf of Lemma 061A is the rule `U' ↦ {a' : U' ⟶ Y over B with a'|_U = a|_U}`
   (`AlgebraicGeometry.Space.liftSubfunctor`);
3. the sheaf `SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` acts on it
   (`AlgebraicGeometry.Space.liftSheafAddActionOfEqTop`, the action of Lemma 061C), simply
   transitively over every `U'` over which it has a section.

Here `B` is the base `T`, `X ⊂ X'` is a first order thickening and `a : X ⟶ Y` is arbitrary; the
target `Y ⊂ Y'` is first order because it is trivial. -/
@[stacks 061D "the special case Y = Y': A = 0, the sheaf of 061A is the rule U' ↦ {a' : U' → Y \
over B with a'|_U = a|_U}, and SheafHom_{O_X}(a^*Ω_{Y/B}, C_{X/X'}) acts on it (the action of \
061C), simply transitively"]
theorem liftSubfunctor_remark_of_eq_top (hHtop : H = ⊤) :
    (letI := Preadditive.homGroup (C := Modules.{u, u} C S hS (IsThickening.space C S hS hG).1
       (IsThickening.space C S hS hG).2)
       ((modulePullback C S hS a).obj (conormalModule C S hS Y' ⟨H, hH.1⟩))
       (conormalModule C S hS X' ⟨G, hG.1⟩)
     ∀ A' : (modulePullback C S hS a).obj (conormalModule C S hS Y' ⟨H, hH.1⟩) ⟶
        conormalModule C S hS X' ⟨G, hG.1⟩, A' = 0) ∧
    conormalLiftSubfunctor C S hS hG hH pX' pY' a A = liftSubfunctor C S hS hG hH pX' pY' a ∧
    ∀ (U' : SpacesEtale C S hS X') (s : (liftSubfunctor C S hS hG hH pX' pY' a).obj (op U')),
      letI := liftSheafAddActionOfEqTop C S hS pX' pY' a A hG₁ hHtop U'
      Function.Bijective (fun θ : conormalLiftActionHom C S hS hG hH pY' a U' => θ +ᵥ s) := by
  refine ⟨fun A' => eq_zero_of_eq_top C S hS hG hH a A' hHtop,
    conormalLiftSubfunctor_eq_liftSubfunctor_of_eq_top C S hS hG hH pX' pY' a A hHtop,
    fun U' s => ?_⟩
  have h := conormalLiftSheafAddAction_bijective C S hS pX' pY' a A hG₁
    (isFirstOrderThickening_of_eq_top C S hS hH hHtop) U'
    (liftSubfunctorEquivOfEqTop C S hS hG hH pX' pY' a A hHtop U' s)
  exact (liftSubfunctorEquivOfEqTop C S hS hG hH pX' pY' a A hHtop U').symm.bijective.comp h

end AlgebraicGeometry.Space

end
