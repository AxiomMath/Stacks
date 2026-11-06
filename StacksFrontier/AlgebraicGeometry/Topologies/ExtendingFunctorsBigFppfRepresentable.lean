module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatChartDescent
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Transport
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsBigFppfExistence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Representability of the diagonal from locally Noetherian test objects

Let `S` be a locally Noetherian scheme contained in a big fppf site `B`, and let `F'` be a functor
on the big fppf site of `S` which is a sheaf for the Zariski coverings and limit preserving. If the
restriction of `F'` to the locally Noetherian site of `S` has representable diagonal, so does
`F'`. This is the implication (2) ⇒ (1) of **Stacks 0GE5** for the diagonal `F' ⟶ F' × F'`.

## Main definitions

* `CategoryTheory.Presheaf.RepresentsEqualizer`: a morphism represents the equalizer of two
  sections of a presheaf.
* `CategoryTheory.Presheaf.sectionEqualizer`, `CategoryTheory.Presheaf.sectionEqualizerYoneda`:
  the equalizer of two sections, as a subfunctor of the (lifted) representable presheaf.
* `AlgebraicGeometry.ExtendingFunctors.DiagRepresentableOnAffineLfp`: the diagonal of a functor on
  the locally Noetherian site is representable over the affine test objects of finite
  presentation over `S`.

## Main results

* `CategoryTheory.Presheaf.uliftYoneda_relativelyRepresentable_diag_iff`: the diagonal of a
  presheaf is representable exactly when the equalizer of any two sections over a representable
  object is representable.
* `AlgebraicGeometry.ExtendingFunctors.representsEqualizer_of_locallyNoetherian`: over a locally
  Noetherian test object of finite presentation over `S`, an equalizer represented among locally
  Noetherian objects is represented among all objects.
* `AlgebraicGeometry.ExtendingFunctors.exists_representsEqualizer_lft_of_affineLfp`: the equalizer
  of any two sections of `F'` is represented by a morphism locally of finite type.
* `AlgebraicGeometry.ExtendingFunctors.relativelyRepresentable_diag_of_restriction`: Stacks 0GE5,
  (2) ⇒ (1), for the diagonal.

## References

* [Stacks Project, Tag 0GE3](https://stacks.math.columbia.edu/tag/0GE3)
* [Stacks Project, Tag 0GE4](https://stacks.math.columbia.edu/tag/0GE4)
* [Stacks Project, Tag 0GE5](https://stacks.math.columbia.edu/tag/0GE5)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v v₁ u₁ u

namespace CategoryTheory.Presheaf

variable {C : Type u₁} [Category.{v₁} C] (P : Cᵒᵖ ⥤ Type (max w v₁))

/-- The morphism `snd : X ⟶ Y` represents the equalizer of two sections `a` and `b` of `P` over
`Y`: it is a monomorphism, and a morphism `φ : Z ⟶ Y` factors through it exactly when `a` and `b`
have the same restriction along `φ`. -/
def RepresentsEqualizer {X Y : C} (snd : X ⟶ Y) (a b : P.obj (op Y)) : Prop :=
  (∀ (Z : C) (ψ ψ' : Z ⟶ X), ψ ≫ snd = ψ' ≫ snd → ψ = ψ') ∧
    ∀ (Z : C) (φ : Z ⟶ Y), P.map φ.op a = P.map φ.op b ↔ ∃ ψ : Z ⟶ X, ψ ≫ snd = φ

variable {P}

/-- A section of the product of two presheaves is determined by its two projections. -/
lemma prod_section_ext {Z : C} {x y : (P ⨯ P).obj (op Z)}
    (h₁ : (prod.fst : P ⨯ P ⟶ P).app _ x = (prod.fst : P ⨯ P ⟶ P).app _ y)
    (h₂ : (prod.snd : P ⨯ P ⟶ P).app _ x = (prod.snd : P ⨯ P ⟶ P).app _ y) : x = y := by
  apply uliftYonedaEquiv.{w}.symm.injective
  apply prod.hom_ext
  · rw [uliftYonedaEquiv_symm_comp, uliftYonedaEquiv_symm_comp, h₁]
  · rw [uliftYonedaEquiv_symm_comp, uliftYonedaEquiv_symm_comp, h₂]

/-- A square of presheaves of sets which is a pullback at every object is a pullback. -/
lemma isPullback_of_forall_app {F₁ F₂ F₃ F₄ : Cᵒᵖ ⥤ Type v} {t : F₁ ⟶ F₂}
    {l : F₁ ⟶ F₃} {r : F₂ ⟶ F₄} {b : F₃ ⟶ F₄} (w : t ≫ r = l ≫ b)
    (h : ∀ Z, IsPullback (t.app Z) (l.app Z) (r.app Z) (b.app Z)) : IsPullback t l r b :=
  ⟨⟨w⟩, ⟨evaluationJointlyReflectsLimits _ fun Z =>
    (isLimitMapConePullbackConeEquiv ((evaluation _ _).obj Z) w).symm (h Z).isLimit⟩⟩

/-- Two sections with the same restriction along `φ` have the same restriction along `g ≫ φ`. -/
private lemma map_comp_op_eq_of_map_eq {Z W Y : C} {R : Cᵒᵖ ⥤ Type*} {a b : R.obj (op Y)}
    (g : W ⟶ Z) {φ : Z ⟶ Y} (h : R.map φ.op a = R.map φ.op b) :
    R.map (g ≫ φ).op a = R.map (g ≫ φ).op b := by
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, h]

/-- **The diagonal of a presheaf of sets is representable exactly when the equalizers of pairs of
sections over representable objects are representable.** -/
theorem uliftYoneda_relativelyRepresentable_diag_iff :
    (uliftYoneda.{w} (C := C)).relativelyRepresentable (diag P) ↔
      ∀ (Y : C) (a b : P.obj (op Y)), ∃ (X : C) (snd : X ⟶ Y), RepresentsEqualizer P snd a b := by
  constructor
  · intro h Y a b
    obtain ⟨X, snd, fst, hpb⟩ := h (prod.lift (uliftYonedaEquiv.symm a) (uliftYonedaEquiv.symm b))
    refine ⟨X, snd, fun Z ψ ψ' hψ => ?_, fun Z φ => ⟨fun hφ => ?_, ?_⟩⟩
    · have hl : uliftYoneda.map ψ ≫ uliftYoneda.map snd =
          uliftYoneda.map ψ' ≫ uliftYoneda.map snd := by
        rw [← Functor.map_comp, ← Functor.map_comp, hψ]
      have ht : uliftYoneda.map ψ ≫ fst = uliftYoneda.map ψ' ≫ fst := by
        have := congrArg (· ≫ prod.fst) (congrArg (fun k => k ≫ prod.lift (uliftYonedaEquiv.symm a)
          (uliftYonedaEquiv.symm b)) hl)
        simp only [Category.assoc, ← hpb.w] at this
        simpa using this
      exact uliftYoneda.map_injective (hpb.hom_ext ht hl)
    · have hc : uliftYonedaEquiv.symm (P.map φ.op a) ≫ diag P = uliftYoneda.map φ ≫
          prod.lift (uliftYonedaEquiv.symm a) (uliftYonedaEquiv.symm b) := by
        apply prod.hom_ext
        · simp [uliftYonedaEquiv_symm_map φ.op]
        · simp [uliftYonedaEquiv_symm_map φ.op, hφ]
      refine ⟨uliftYoneda.preimage (hpb.lift _ _ hc), uliftYoneda.map_injective ?_⟩
      rw [Functor.map_comp, Functor.map_preimage, hpb.lift_snd]
    · rintro ⟨ψ, rfl⟩
      apply uliftYonedaEquiv.{w}.symm.injective
      have h₁ := congrArg (fun k => uliftYoneda.map ψ ≫ k ≫ prod.fst) hpb.w
      have h₂ := congrArg (fun k => uliftYoneda.map ψ ≫ k ≫ prod.snd) hpb.w
      simp only [Category.assoc, diag, prod.lift_fst, prod.lift_snd, Category.comp_id] at h₁ h₂
      rw [uliftYonedaEquiv_symm_map, uliftYonedaEquiv_symm_map, Quiver.Hom.unop_op,
        Functor.map_comp, Category.assoc, Category.assoc, ← h₁, ← h₂]
  · intro h Y g
    obtain ⟨X, snd, hmono, heq⟩ :=
      h Y (uliftYonedaEquiv (g ≫ prod.fst)) (uliftYonedaEquiv (g ≫ prod.snd))
    have hab := (heq X snd).2 ⟨𝟙 _, Category.id_comp _⟩
    have hga : g ≫ prod.fst = uliftYonedaEquiv.symm (uliftYonedaEquiv (g ≫ prod.fst)) :=
      (Equiv.symm_apply_apply _ _).symm
    have hgb : g ≫ prod.snd = uliftYonedaEquiv.symm (uliftYonedaEquiv (g ≫ prod.snd)) :=
      (Equiv.symm_apply_apply _ _).symm
    have hw : (uliftYoneda.map snd ≫ g ≫ prod.fst) ≫ diag P = uliftYoneda.map snd ≫ g := by
      apply prod.hom_ext
      · simp
      · simp only [Category.assoc, diag, prod.lift_snd, Category.comp_id]
        rw [hga, hgb, ← Quiver.Hom.unop_op snd, ← uliftYonedaEquiv_symm_map,
          ← uliftYonedaEquiv_symm_map, hab]
    refine ⟨X, snd, uliftYoneda.map snd ≫ g ≫ prod.fst, isPullback_of_forall_app hw fun Z => ?_⟩
    rw [Types.isPullback_iff]
    refine ⟨congrArg (fun k => k.app Z) hw, fun x₁ y₁ hxy => ?_, fun x₂ x₃ hx => ?_⟩
    · have := hmono _ x₁.down y₁.down (congrArg ULift.down hxy.2)
      exact congrArg ULift.up this
    · have e1 : (g ≫ prod.fst).app Z x₃ = x₂ := by
        have := congrArg ((prod.fst : P ⨯ P ⟶ P).app Z) hx
        simp only [← NatTrans.comp_app_apply, diag, prod.lift_fst, NatTrans.id_app] at this
        exact this.symm
      have e2 : (g ≫ prod.snd).app Z x₃ = x₂ := by
        have := congrArg ((prod.snd : P ⨯ P ⟶ P).app Z) hx
        simp only [← NatTrans.comp_app_apply, diag, prod.lift_snd, NatTrans.id_app] at this
        exact this.symm
      rw [hga] at e1
      rw [hgb] at e2
      simp only [uliftYonedaEquiv_symm_apply_app] at e1 e2
      obtain ⟨ψ, hψ⟩ := (heq _ x₃.down).1 (e1.trans e2.symm)
      refine ⟨ULift.up ψ, ?_, ?_⟩
      · rw [← e1]
        obtain ⟨φ⟩ := x₃
        dsimp only at hψ
        subst hψ
        rw [hga]
        simp only [Equiv.apply_symm_apply]
        rfl
      · exact congrArg ULift.up hψ

end CategoryTheory.Presheaf

namespace CategoryTheory.Presheaf

variable {C : Type u₁} [Category.{v₁} C] (P : Cᵒᵖ ⥤ Type (max w v₁))

/-- The subfunctor of `uliftYoneda.obj Y` of the morphisms along which two sections `a` and `b`
of `P` over `Y` have the same restriction. -/
@[sga "3 I 1.2" "special case"]
def sectionEqualizer {Y : C} (a b : P.obj (op Y)) : Subfunctor (uliftYoneda.{w}.obj Y) where
  obj Z := {φ | P.map φ.down.op a = P.map φ.down.op b}
  map {Z Z'} g φ hφ := by
    have hd : ((uliftYoneda.{w}.obj Y).map g φ).down = g.unop ≫ φ.down := rfl
    have hφ' : P.map φ.down.op a = P.map φ.down.op b := hφ
    change P.map ((uliftYoneda.{w}.obj Y).map g φ).down.op a =
      P.map ((uliftYoneda.{w}.obj Y).map g φ).down.op b
    rw [hd, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hφ']

variable {P}

/-- A morphism lies in `sectionEqualizer P a b` exactly when `a` and `b` have the same restriction
along it. -/
@[simp]
lemma mem_sectionEqualizer {Y : C} (a b : P.obj (op Y)) {Z : Cᵒᵖ}
    (φ : (uliftYoneda.{w}.obj Y).obj Z) :
    φ ∈ (sectionEqualizer P a b).obj Z ↔ P.map φ.down.op a = P.map φ.down.op b :=
  Iff.rfl

/-- A morphism to `Y` represents the equalizer of `a` and `b` as soon as the induced morphism of
presheaves into the subfunctor `sectionEqualizer P a b` is an isomorphism. -/
lemma representsEqualizer_of_isIso {X Y : C} (snd : X ⟶ Y) (a b : P.obj (op Y))
    (c : uliftYoneda.{w}.obj X ⟶ (sectionEqualizer P a b).toFunctor)
    (hc : c ≫ (sectionEqualizer P a b).ι = uliftYoneda.map snd) [IsIso c] :
    RepresentsEqualizer P snd a b := by
  have happ : ∀ (Z : C) (ψ : Z ⟶ X), ((c.app (op Z)) (ULift.up ψ)).1 = ULift.up (ψ ≫ snd) :=
    fun Z ψ => congrArg (fun k => k.app (op Z) (ULift.up ψ)) hc
  refine ⟨fun Z ψ ψ' h => ?_, fun Z φ => ⟨fun hφ => ?_, ?_⟩⟩
  · have hinj : Function.Injective (c.app (op Z)) :=
      (isIso_iff_bijective (c.app (op Z))).1 inferInstance |>.1
    have := hinj (Subtype.ext ((happ Z ψ).trans ((congrArg ULift.up h).trans (happ Z ψ').symm)))
    exact congrArg ULift.down this
  · obtain ⟨⟨ψ⟩, hψ⟩ := ((isIso_iff_bijective (c.app (op Z))).1 inferInstance).2
      ⟨ULift.up φ, hφ⟩
    exact ⟨ψ, congrArg ULift.down ((happ Z ψ).symm.trans (congrArg Subtype.val hψ))⟩
  · rintro ⟨ψ, rfl⟩
    have := ((c.app (op Z)) (ULift.up ψ)).2
    rw [happ] at this
    exact this

/-- **The equalizer of restricted sections is the pullback of the equalizer.** -/
lemma representsEqualizer_pullback {X Y W : C} {snd : X ⟶ Y} {a b : P.obj (op Y)}
    (h : RepresentsEqualizer P snd a b) (π : W ⟶ Y) [HasPullback snd π] :
    RepresentsEqualizer P (pullback.snd snd π) (P.map π.op a) (P.map π.op b) := by
  refine ⟨fun Z ψ ψ' hψ => ?_, fun Z φ => ?_⟩
  · refine pullback.hom_ext (h.1 _ _ _ ?_) hψ
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, hψ,
      Category.assoc]
  · rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
      h.2 Z (φ ≫ π)]
    constructor
    · rintro ⟨χ, hχ⟩
      exact ⟨pullback.lift χ φ hχ, pullback.lift_snd _ _ _⟩
    · rintro ⟨ψ, rfl⟩
      exact ⟨ψ ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, Category.assoc]⟩

variable (P) in
/-- The subfunctor of `yoneda.obj Y` of the morphisms along which two sections `a` and `b` of `P`
over `Y` have the same restriction. -/
@[sga "3 I 1.2" "representable domain"]
def sectionEqualizerYoneda {Y : C} (a b : P.obj (op Y)) : Subfunctor (yoneda.obj Y) where
  obj Z := {φ | P.map φ.op a = P.map φ.op b}
  map {Z Z'} g φ hφ := by
    have hφ' : P.map φ.op a = P.map φ.op b := hφ
    change P.map (g.unop ≫ φ).op a = P.map (g.unop ≫ φ).op b
    rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hφ']

/-- The image of a morphism through which the equalizer of restricted sections is represented
lies in the equalizer subfunctor. -/
lemma range_le_sectionEqualizerYoneda {X Y W : C} {snd : X ⟶ W} (q : W ⟶ Y)
    {a b : P.obj (op Y)} (h : RepresentsEqualizer P snd (P.map q.op a) (P.map q.op b)) :
    Subfunctor.range (yoneda.map (snd ≫ q)) ≤ sectionEqualizerYoneda P a b := by
  rintro Z _ ⟨ψ, rfl⟩
  show P.map (ψ ≫ snd ≫ q).op a = P.map (ψ ≫ snd ≫ q).op b
  rw [← Category.assoc, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
  exact (h.2 _ _).2 ⟨ψ, rfl⟩

/-- **The pullback of the equalizer subfunctor along a representable point is represented by the
equalizer of the restricted sections.** -/
lemma isPullback_sectionEqualizerYoneda {X Y W : C} {snd : X ⟶ W} (q : W ⟶ Y)
    {a b : P.obj (op Y)} (h : RepresentsEqualizer P snd (P.map q.op a) (P.map q.op b)) :
    IsPullback ((sectionEqualizerYoneda P a b).lift (yoneda.map (snd ≫ q))
        (range_le_sectionEqualizerYoneda q h))
      (yoneda.map snd) (sectionEqualizerYoneda P a b).ι (yoneda.map q) := by
  have hw : (sectionEqualizerYoneda P a b).lift (yoneda.map (snd ≫ q))
      (range_le_sectionEqualizerYoneda q h) ≫
      (sectionEqualizerYoneda P a b).ι = yoneda.map snd ≫ yoneda.map q := by
    ext Z ψ
    exact (Category.assoc ψ snd q).symm
  refine isPullback_of_forall_app hw fun Z => ?_
  rw [Types.isPullback_iff]
  refine ⟨congrArg (fun k => k.app Z) hw, fun x₁ y₁ hxy => h.1 _ x₁ y₁ hxy.2,
    fun x₂ x₃ hx => ?_⟩
  · have hx' : x₂.1 = x₃ ≫ q := hx
    have hmem : P.map x₂.1.op a = P.map x₂.1.op b := x₂.2
    rw [hx', op_comp, Functor.map_comp_apply, Functor.map_comp_apply] at hmem
    obtain ⟨ψ, hψ⟩ := (h.2 _ x₃).1 hmem
    refine ⟨ψ, Subtype.ext ?_, hψ⟩
    show ψ ≫ snd ≫ q = x₂.1
    rw [hx', ← hψ, Category.assoc]

/-- **A representing pullback of the equalizer subfunctor along the identity represents the
equalizer.** -/
lemma representsEqualizer_of_isPullback {X Y : C} {snd : X ⟶ Y} {a b : P.obj (op Y)}
    {fst : yoneda.obj X ⟶ (sectionEqualizerYoneda P a b).toFunctor}
    (h : IsPullback fst (yoneda.map snd) (sectionEqualizerYoneda P a b).ι (𝟙 _)) :
    RepresentsEqualizer P snd a b := by
  refine ⟨fun Z ψ ψ' hψ => yoneda.map_injective ?_, fun Z φ => ⟨fun hφ => ?_, ?_⟩⟩
  · refine h.hom_ext ?_ (by rw [← Functor.map_comp, ← Functor.map_comp, hψ])
    rw [← cancel_mono (sectionEqualizerYoneda P a b).ι, Category.assoc, Category.assoc, h.w,
      ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hψ]
  · let s : yoneda.obj Z ⟶ (sectionEqualizerYoneda P a b).toFunctor :=
      (sectionEqualizerYoneda P a b).lift (yoneda.map φ) (by
        rintro W _ ⟨g, rfl⟩
        show P.map (g ≫ φ).op a = P.map (g ≫ φ).op b
        exact map_comp_op_eq_of_map_eq _ hφ)
    refine ⟨yoneda.preimage (h.lift s (yoneda.map φ)
      (by rw [Category.comp_id]; exact Subfunctor.lift_ι _ _)), yoneda.map_injective ?_⟩
    rw [Functor.map_comp, Functor.map_preimage, h.lift_snd]
  · rintro ⟨ψ, rfl⟩
    have := congrArg (fun k => (k.app (op Z) ψ)) h.w
    have hmem := ((fst.app (op Z)) ψ).2
    change P.map (((fst.app (op Z)) ψ).1).op a = P.map (((fst.app (op Z)) ψ).1).op b at hmem
    have e : ((fst.app (op Z)) ψ).1 = ψ ≫ snd := by simpa using this
    rwa [e] at hmem

/-- **On a subcanonical site, two sections whose equalizer is representable and covering are
equal.** -/
lemma eq_of_representsEqualizer {J : GrothendieckTopology C} [J.Subcanonical] {X W : C}
    {snd : X ⟶ W} {a b : P.obj (op W)} (h : RepresentsEqualizer P snd a b)
    (hR : (sectionEqualizerYoneda P a b).sieveOfSection (𝟙 W : (yoneda.obj W).obj (op W)) ∈
      J W) : a = b := by
  let E := sectionEqualizerYoneda P a b
  have hrange : Subfunctor.range (yoneda.map snd) ≤ E := by
    rintro Z _ ⟨ψ, rfl⟩
    exact (h.2 _ _).2 ⟨ψ, rfl⟩
  let c : yoneda.obj X ⟶ E.toFunctor := E.lift (yoneda.map snd) hrange
  have hc : IsIso c := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Z
    rw [isIso_iff_bijective]
    refine ⟨fun ψ ψ' hψ => h.1 _ ψ ψ' (congrArg Subtype.val hψ), fun φ => ?_⟩
    obtain ⟨ψ, hψ⟩ := (h.2 _ φ.1).1 φ.2
    exact ⟨ψ, Subtype.ext hψ⟩
  have hsheaf : Presieve.IsSheaf J E.toFunctor :=
    Presieve.isSheaf_iso J (asIso c) ((isSheaf_iff_isSheaf_of_type J _).1 (J.yoneda.obj X).property)
  have hmem := (Subfunctor.isSheaf_iff E
    ((isSheaf_iff_isSheaf_of_type J _).1 (J.yoneda.obj W).property)).1 hsheaf (op W) (𝟙 W) hR
  have hmem' : P.map (𝟙 W).op a = P.map (𝟙 W).op b := hmem
  simpa using hmem'

end CategoryTheory.Presheaf

namespace CategoryTheory.Presieve

/-- **The sheaf condition passes to an equalizer.** If `ι : E ⟶ Q` exhibits `E` as the equalizer
of `b₁, b₂ : Q ⟶ P` objectwise, `Q` satisfies the sheaf condition for `R` and `P` is separated for
`R`, then `E` satisfies the sheaf condition for `R`. -/
theorem isSheafFor_of_isEqualizer {C : Type*} [Category C] {X : C} {R : Presieve X}
    {E Q P : Cᵒᵖ ⥤ Type w} (ι : E ⟶ Q) (b₁ b₂ : Q ⟶ P) (hinj : ∀ Z, Function.Injective (ι.app Z))
    (hlift : ∀ Z (q : Q.obj Z), b₁.app Z q = b₂.app Z q → ∃ e, ι.app Z e = q)
    (hcomp : ι ≫ b₁ = ι ≫ b₂) (hQ : R.IsSheafFor Q) (hP : R.IsSeparatedFor P) :
    R.IsSheafFor E := by
  intro x hx
  obtain ⟨t, ht, -⟩ := hQ (x.map ι) (hx.map ι)
  have hb : b₁.app _ t = b₂.app _ t := by
    refine hP (x.map (ι ≫ b₁)) _ _ ?_ ?_
    · exact ht.map b₁
    · rw [hcomp]
      exact ht.map b₂
  obtain ⟨e, rfl⟩ := hlift _ t hb
  refine ⟨e, fun Y f hf => hinj _ ?_, fun e' he' => hinj _ ?_⟩
  · rw [NatTrans.naturality_apply]
    exact ht f hf
  · exact hQ.isSeparatedFor (x.map ι) _ _ (he'.map ι) ht

end CategoryTheory.Presieve

namespace AlgebraicGeometry.ExtendingFunctors

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)

/-- **Limit preservation passes to the locally Noetherian site.** -/
theorem limitPreserving_restriction_locallyNoetherian {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}
    (hP : LimitPreserving.{u, w, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) P) :
    LimitPreserving.{u, w, u, u, u + 1, u} (LocallyNoetherianOver.toScheme B S hS)
      ((LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ P) := by
  intro I _ _ D c hc haff hpt
  obtain ⟨h⟩ := hP I (D ⋙ LocallyNoetherianOver.toBigFppfOver B S hS)
    ((LocallyNoetherianOver.toBigFppfOver B S hS).mapCone c) hc haff hpt
  exact ⟨h⟩

/-- The functor from the big fppf site of `S` to `Sch/S` is fully faithful. -/
def fullyFaithfulBigFppfOverToOver : (bigFppfOverToOver B hS).FullyFaithful :=
  (bigFppfOverEquivalence B hS).fullyFaithfulFunctor.comp (ObjectProperty.fullyFaithfulι _)

/-- **A representable presheaf on the big fppf site of `S` of an object locally of finite
presentation over `S` is limit preserving.** -/
theorem limitPreserving_uliftYoneda_of_locallyOfFinitePresentation (X : BigFppfOver B S hS)
    (hX : LocallyOfFinitePresentation ((bigFppfOverToOver B hS).obj X).hom) :
    LimitPreserving.{u, max w u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS)
      (uliftYoneda.{w}.obj X) := by
  have h₁ : Scheme.IsLimitPreserving S (uliftYoneda.{w}.obj ((bigFppfOverToOver B hS).obj X)) := by
    intro I _ _ D hD
    have := Scheme.isLimitPreserving_yoneda_of_locallyOfFinitePresentation
      ((bigFppfOverToOver B hS).obj X) I D hD
    exact inferInstanceAs (PreservesColimit D.op (yoneda.obj _ ⋙ uliftFunctor.{w}))
  have h₂ := limitPreserving_restriction_of_preservesAffineLimits B hS
    (ExtendingFunctors.preservesAffineLimits_of_isLimitPreserving h₁)
  let hK := fullyFaithfulBigFppfOverToOver B hS
  refine limitPreserving_of_natIso (NatIso.ofComponents (fun Z => Equiv.toIso
    (Equiv.ulift.trans (hK.homEquiv.symm.trans Equiv.ulift.symm))) ?_) h₂
  intro Z Z' g
  ext ⟨φ⟩
  apply ULift.ext
  show hK.preimage ((bigFppfOverToOver B hS).map g.unop ≫ φ) = g.unop ≫ hK.preimage φ
  apply hK.map_injective
  rw [hK.map_preimage, Functor.map_comp, hK.map_preimage]

/-- **Condition (b) of Stacks 0EUW for a limit preserving functor on the big fppf site of `S`**,
for a functor whose values already lie in `Type (max w (u + 1))`. -/
theorem preservesAffineLimitsOnSubcategory_isContainedOver_of_limitPreserving
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}
    (hF : LimitPreserving.{u, w, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F) :
    PreservesAffineLimitsOnSubcategory (IsContainedOver B (S := S))
      ((toBigFppfOver B hS).op ⋙ F) := by
  intro Λ _ _ _ D haff c hc
  have hlim : IsLimit ((BigFppfOver.toScheme B S hS).mapCone
      ((toBigFppfOver B hS).mapCone c)) :=
    isLimitOfPreserves (Over.forget S) hc
  have : ∀ i : Λᵒᵖ, IsAffine (((D ⋙ (IsContainedOver B).ι) ⋙ Over.forget S).obj i) := haff
  have hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj ((toBigFppfOver B hS).mapCone c).pt) :=
    Scheme.isAffine_of_isLimit _ (isLimitOfPreserves (Over.forget S) hc)
  obtain ⟨hcol⟩ := hF Λᵒᵖ (D ⋙ toBigFppfOver B hS) ((toBigFppfOver B hS).mapCone c) hlim
    haff hpt
  exact ⟨hcol⟩

/-- **Stacks 0GE3, full faithfulness, for Zariski sheaves on the big fppf site of `S`.** Let `F`
and `G` be functors on the big fppf site of `S` satisfying the sheaf condition for the Zariski
coverings by objects of the site and limit preserving in the sense of Stacks 049J. Every
transformation between their restrictions to the locally Noetherian objects is the restriction of
exactly one transformation `F ⟶ G`. -/
theorem existsUnique_hom_whiskerLeft_eq_of_isCoveringSheafOnSubcategory [IsLocallyNoetherian S]
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w (u + 1))}
    (hFs : IsCoveringSheafOnSubcategory.{max w (u + 1), u, u} .zariski
      (IsContainedOver B (S := S)) ((toBigFppfOver B hS).op ⋙ F))
    (hFl : LimitPreserving.{u, max w (u + 1), u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F)
    (hGs : IsCoveringSheafOnSubcategory.{max w (u + 1), u, u} .zariski
      (IsContainedOver B (S := S)) ((toBigFppfOver B hS).op ⋙ G))
    (hGl : LimitPreserving.{u, max w (u + 1), u, u, u + 1, u} (BigFppfOver.toScheme B S hS) G)
    (σ : (LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F ⟶
      (LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ G) :
    ∃! θ : F ⟶ G, Functor.whiskerLeft (LocallyNoetherianOver.toBigFppfOver B S hS).op θ = σ := by
  let R := (Functor.whiskeringLeft _ _ (Type (max w (u + 1)))).obj (toBigFppfOver B hS).op
  let hR : R.FullyFaithful :=
    ((bigFppfOverEquivalence B hS).op.congrLeft (E := Type (max w (u + 1)))).fullyFaithfulFunctor
  let R₂ := (Functor.whiskeringLeft _ _ (Type (max w (u + 1)))).obj
    (toLocallyNoetherianOver B hS).op
  let hR₂ : R₂.FullyFaithful := ((locallyNoetherianOverEquivalence B hS).op.congrLeft
    (E := Type (max w (u + 1)))).fullyFaithfulFunctor
  let h := isContainedLocallyNoetherianOver_le B (S := S)
  have hcomm : ∀ {F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w (u + 1))} (θ : F' ⟶ G'),
      R₂.map (Functor.whiskerLeft (LocallyNoetherianOver.toBigFppfOver B S hS).op θ) =
        Functor.whiskerLeft (ObjectProperty.ιOfLE h).op (R.map θ) := fun _ => rfl
  obtain ⟨θ₁, hθ₁, huniq₁⟩ := existsUnique_hom_whiskerLeft_ιOfLE_eq.{w} h
    (hasAffineOpens_isContainedOver B) (hasFinitePresentationAffines_isContainedOver B hS)
    (hasAffineOpens_isContainedLocallyNoetherianOver B)
    (hasFinitePresentationAffines_isContainedLocallyNoetherianOver B hS)
    (isZariskiSheafOnSubcategory_of_isCoveringSheafOnSubcategory .zariski
      (hasAffineOpens_isContainedOver B) hFs)
    (preservesAffineLimitsOnSubcategory_isContainedOver_of_limitPreserving B hS hFl)
    (isZariskiSheafOnSubcategory_of_isCoveringSheafOnSubcategory .zariski
      (hasAffineOpens_isContainedOver B) hGs)
    (preservesAffineLimitsOnSubcategory_isContainedOver_of_limitPreserving B hS hGl)
    (F := R.obj F) (G := R.obj G) (R₂.map σ)
  refine ⟨hR.preimage θ₁, hR₂.map_injective ?_, fun θ hθ => hR.map_injective ?_⟩
  · exact (hcomm _).trans ((congrArg (Functor.whiskerLeft (ObjectProperty.ιOfLE h).op)
      (hR.map_preimage θ₁)).trans hθ₁)
  · exact (huniq₁ _ ((hcomm θ).symm.trans (congrArg R₂.map hθ))).trans
      (hR.map_preimage θ₁).symm

/-- The functor from the big fppf site of `S` to schemes preserves pullbacks. -/
private theorem preservesLimitsOfShape_walkingCospan_toScheme :
    PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
  dsimp only [BigFppfOver.toScheme]
  infer_instance

section Diagonal

open Presheaf

variable [IsLocallyNoetherian S] {F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w (u + 1))}

omit [IsLocallyNoetherian S] in
/-- A representable presheaf on the big fppf site of `S` is a sheaf for the Zariski coverings by
objects of the site. -/
theorem isCoveringSheafOnSubcategory_uliftYoneda (T : BigFppfOver B S hS) :
    IsCoveringSheafOnSubcategory.{max w (u + 1), u, u} .zariski (IsContainedOver B (S := S))
      ((toBigFppfOver B hS).op ⋙ uliftYoneda.{max w (u + 1)}.obj T) :=
  isCoveringSheafOnSubcategory_of_isSheaf B hS
    ((BigFppfOver.topology B S hS).uliftYoneda.{max w (u + 1)}.obj T).property

omit [IsLocallyNoetherian S] in
include hS in
/-- The equalizer of two sections of a Zariski sheaf on the big fppf site of `S` is a Zariski
sheaf. -/
theorem isCoveringSheafOnSubcategory_sectionEqualizer
    (hFs : IsCoveringSheafOnSubcategory.{max w (u + 1), u, u} .zariski (IsContainedOver B (S := S))
      ((toBigFppfOver B hS).op ⋙ F'))
    {T : BigFppfOver B S hS} (a b : F'.obj (op T)) :
    IsCoveringSheafOnSubcategory.{max w (u + 1), u, u} .zariski (IsContainedOver B (S := S))
      ((toBigFppfOver B hS).op ⋙ (sectionEqualizer.{max w (u + 1)} F' a b).toFunctor) := by
  intro ι X Y f hcov
  refine Presieve.isSheafFor_of_isEqualizer
    (Functor.whiskerLeft (toBigFppfOver B hS).op (sectionEqualizer F' a b).ι)
    (Functor.whiskerLeft (toBigFppfOver B hS).op (uliftYonedaEquiv.symm a))
    (Functor.whiskerLeft (toBigFppfOver B hS).op (uliftYonedaEquiv.symm b))
    (fun Z => Subtype.val_injective) (fun Z q hq => ⟨⟨q, by simpa using hq⟩, rfl⟩) ?_
    (isCoveringSheafOnSubcategory_uliftYoneda B hS T X Y f hcov)
    (hFs X Y f hcov).isSeparatedFor
  ext Z ⟨q, hq⟩
  exact hq

omit [IsLocallyNoetherian S] in
/-- The equalizer of two sections of a limit preserving functor over a limit preserving
representable object is limit preserving. -/
theorem limitPreserving_sectionEqualizer
    (hFl : LimitPreserving.{u, max w (u + 1), u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F')
    {T : BigFppfOver B S hS}
    (hT : LimitPreserving.{u, max w (u + 1), u, u, u + 1, u} (BigFppfOver.toScheme B S hS)
      (uliftYoneda.{max w (u + 1)}.obj T))
    (a b : F'.obj (op T)) :
    LimitPreserving.{u, max w (u + 1), u, u, u + 1, u} (BigFppfOver.toScheme B S hS)
      (sectionEqualizer.{max w (u + 1)} F' a b).toFunctor :=
  limitPreserving_of_isEqualizer _ (sectionEqualizer F' a b).ι (uliftYonedaEquiv.symm a)
    (uliftYonedaEquiv.symm b) (fun Z => Subtype.val_injective)
    (fun Z e => e.2) (fun Z q hq => ⟨⟨q, by simpa using hq⟩, rfl⟩) hT hFl

omit [IsLocallyNoetherian S] in
/-- Limit preservation of a functor follows from that of its lift to a larger universe. -/
theorem limitPreserving_of_comp_uliftFunctor {C : Type*} [Category C] {toScheme : C ⥤ Scheme.{u}}
    {P : Cᵒᵖ ⥤ Type u} (h : LimitPreserving.{u, max u w, u, u} toScheme (P ⋙ uliftFunctor.{w})) :
    LimitPreserving.{u, u, u, u} toScheme P := by
  intro I _ _ D c hc haff hpt
  obtain ⟨h'⟩ := h I D c hc haff hpt
  exact ⟨isColimitOfReflects uliftFunctor.{w} h'⟩

/-- The representable presheaves of the locally Noetherian site are the restrictions of the
representable presheaves of the big fppf site. -/
noncomputable def uliftYonedaRestrictionIso (X : LocallyNoetherianOver B S hS) :
    (LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙
        uliftYoneda.{w}.obj ((LocallyNoetherianOver.toBigFppfOver B S hS).obj X) ≅
      uliftYoneda.{w}.obj X :=
  let hι : (LocallyNoetherianOver.toBigFppfOver B S hS).FullyFaithful :=
    ObjectProperty.fullyFaithfulι _
  NatIso.ofComponents (fun Z => Equiv.toIso
    (Equiv.ulift.trans (hι.homEquiv.symm.trans Equiv.ulift.symm))) (by
      intro Z Z' g
      ext ⟨φ⟩
      apply ULift.ext
      change hι.preimage ((LocallyNoetherianOver.toBigFppfOver B S hS).map g.unop ≫ φ) =
        g.unop ≫ hι.preimage φ
      apply hι.map_injective
      rw [hι.map_preimage, Functor.map_comp, hι.map_preimage])

/-- **Step (2) ⇒ (1) of Stacks 0GE5 at a locally Noetherian test object of finite presentation,
for the diagonal.** Let `F'` be a Zariski sheaf on the big fppf site of `S` which is limit
preserving, let `V` be a locally Noetherian object locally of finite presentation over `S`, and
let `a, b` be sections of `F'` over `V`. If a morphism `snd : X ⟶ V` of the locally Noetherian
site represents the equalizer of `a` and `b` among locally Noetherian objects, then it represents
it among all objects of the site. -/
theorem representsEqualizer_of_locallyNoetherian
    (hFs : IsCoveringSheafOnSubcategory.{max w (u + 1), u, u} .zariski (IsContainedOver B (S := S))
      ((toBigFppfOver B hS).op ⋙ F'))
    (hFl : LimitPreserving.{u, max w (u + 1), u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F')
    {V X : LocallyNoetherianOver B S hS} (snd : X ⟶ V)
    (hV : LocallyOfFinitePresentation ((bigFppfOverToOver B hS).obj
      ((LocallyNoetherianOver.toBigFppfOver B S hS).obj V)).hom)
    (a b : F'.obj (op ((LocallyNoetherianOver.toBigFppfOver B S hS).obj V)))
    (h : RepresentsEqualizer.{max w (u + 1)}
      ((LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F') snd a b) :
    RepresentsEqualizer.{max w (u + 1)} F'
        ((LocallyNoetherianOver.toBigFppfOver B S hS).map snd) a b ∧
      LocallyOfFinitePresentation (B.inclusion.map X.1.hom) := by
  let ι := LocallyNoetherianOver.toBigFppfOver B S hS
  have hι : ι.FullyFaithful := ObjectProperty.fullyFaithfulι _
  let E := sectionEqualizer.{max w (u + 1)} F' a b
  have hab : F'.map (ι.map snd).op a = F'.map (ι.map snd).op b :=
    (h.2 X snd).2 ⟨𝟙 _, Category.id_comp _⟩
  let c : uliftYoneda.{max w (u + 1)}.obj (ι.obj X) ⟶ E.toFunctor :=
    E.lift (uliftYoneda.map (ι.map snd)) (by
      rintro Z _ ⟨⟨ψ⟩, rfl⟩
      show F'.map (ψ ≫ ι.map snd).op a = F'.map (ψ ≫ ι.map snd).op b
      exact map_comp_op_eq_of_map_eq _ hab)
  have hc : c ≫ E.ι = uliftYoneda.map (ι.map snd) := E.lift_ι _ _
  have hcN : IsIso (Functor.whiskerLeft ι.op c) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Z
    rw [isIso_iff_bijective]
    constructor
    · rintro ⟨ψ⟩ ⟨ψ'⟩ hψ
      have h1 : ψ ≫ ι.map snd = ψ' ≫ ι.map snd :=
        congrArg ULift.down (congrArg Subtype.val hψ)
      have h2 : hι.preimage ψ ≫ snd = hι.preimage ψ' ≫ snd :=
        hι.map_injective (by simpa using h1)
      have h3 := congrArg ι.map (h.1 _ _ _ h2)
      rw [hι.map_preimage, hι.map_preimage] at h3
      exact congrArg ULift.up h3
    · rintro ⟨⟨φ⟩, hφ⟩
      have hφ' : ((LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F').map
          (hι.preimage φ).op a = ((LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F').map
          (hι.preimage φ).op b := by
        show F'.map (ι.map (hι.preimage φ)).op a = F'.map (ι.map (hι.preimage φ)).op b
        rw [hι.map_preimage]
        exact hφ
      obtain ⟨ψ, hψ⟩ := (h.2 Z.unop (hι.preimage φ)).1 hφ'
      refine ⟨ULift.up (ι.map ψ), Subtype.ext (congrArg ULift.up ?_)⟩
      show ι.map ψ ≫ ι.map snd = φ
      rw [← Functor.map_comp, hψ, hι.map_preimage]
  have hEs : IsCoveringSheafOnSubcategory.{max w (u + 1), u, u} .zariski
      (IsContainedOver B (S := S)) ((toBigFppfOver B hS).op ⋙ E.toFunctor) :=
    isCoveringSheafOnSubcategory_sectionEqualizer B hS hFs a b
  have hEl := limitPreserving_sectionEqualizer B hS hFl
    (limitPreserving_uliftYoneda_of_locallyOfFinitePresentation B hS _ hV) a b
  have hXN : LimitPreserving.{u, u, u, u, u + 1, u} (LocallyNoetherianOver.toScheme B S hS)
      (yoneda.obj X) := by
    have h1 : LimitPreserving.{u, max w (u + 1), u, u, u + 1, u}
        (LocallyNoetherianOver.toScheme B S hS) (yoneda.obj X ⋙ uliftFunctor.{max w (u + 1)}) :=
      limitPreserving_of_natIso (uliftYonedaRestrictionIso.{max w (u + 1)} B hS X)
        (limitPreserving_of_natIso (asIso (Functor.whiskerLeft ι.op c)).symm
          (limitPreserving_restriction_locallyNoetherian B hS hEl))
    exact limitPreserving_of_comp_uliftFunctor h1
  have hXlfp := locallyOfFinitePresentation_of_limitPreserving_yoneda B S hS X hXN
  have hXl := limitPreserving_uliftYoneda_of_locallyOfFinitePresentation.{max w (u + 1)} B hS
    (ι.obj X) hXlfp
  have hXs : IsCoveringSheafOnSubcategory.{max w (u + 1), u, u} .zariski
      (IsContainedOver B (S := S))
      ((toBigFppfOver B hS).op ⋙ uliftYoneda.{max w (u + 1)}.obj (ι.obj X)) :=
    isCoveringSheafOnSubcategory_uliftYoneda.{w} B hS (ι.obj X)
  obtain ⟨d, hd, -⟩ := existsUnique_hom_whiskerLeft_eq_of_isCoveringSheafOnSubcategory B hS
    hEs hEl hXs hXl (inv (Functor.whiskerLeft ι.op c))
  obtain ⟨_, -, huX⟩ := existsUnique_hom_whiskerLeft_eq_of_isCoveringSheafOnSubcategory B hS
    hXs hXl hXs hXl (𝟙 _)
  obtain ⟨_, -, huE⟩ := existsUnique_hom_whiskerLeft_eq_of_isCoveringSheafOnSubcategory B hS
    hEs hEl hEs hEl (𝟙 _)
  have h₁ : c ≫ d = 𝟙 _ :=
    (huX _ (by beta_reduce; rw [Functor.whiskerLeft_comp, hd, IsIso.hom_inv_id])).trans
      (huX _ (Functor.whiskerLeft_id' _)).symm
  have h₂ : d ≫ c = 𝟙 _ :=
    (huE _ (by beta_reduce; rw [Functor.whiskerLeft_comp, hd, IsIso.inv_hom_id])).trans
      (huE _ (Functor.whiskerLeft_id' _)).symm
  have : IsIso c := ⟨d, h₁, h₂⟩
  exact ⟨representsEqualizer_of_isIso _ a b c hc, hXlfp⟩

omit [IsLocallyNoetherian S] in
/-- **The diagonal of `G` is representable over the affine test objects of finite presentation
over `S`**, criterion (3) of Stacks 0GE5 for the diagonal of a functor `G` on the locally
Noetherian site of `S`: for every locally Noetherian object `V` which is affine and locally of
finite presentation over `S`, the equalizer of any two sections of `G` over `V` is represented by a
morphism `X ⟶ V` of the locally Noetherian site. -/
def DiagRepresentableOnAffineLfp
    (G : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type (max w (u + 1))) : Prop :=
  ∀ V : LocallyNoetherianOver B S hS,
    IsAffine ((bigFppfOverToOver B hS).obj
      ((LocallyNoetherianOver.toBigFppfOver B S hS).obj V)).left →
    LocallyOfFinitePresentation ((bigFppfOverToOver B hS).obj
      ((LocallyNoetherianOver.toBigFppfOver B S hS).obj V)).hom →
    ∀ a b : G.obj (op V), ∃ (X : LocallyNoetherianOver B S hS) (snd : X ⟶ V),
      RepresentsEqualizer.{max w (u + 1)} G snd a b

omit [IsLocallyNoetherian S] in
/-- A representable diagonal is representable over the affine test objects of finite
presentation. -/
theorem diagRepresentableOnAffineLfp_of_relativelyRepresentable
    {G : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type (max w (u + 1))}
    (hdiag : (uliftYoneda.{max w (u + 1)}
      (C := LocallyNoetherianOver B S hS)).relativelyRepresentable (diag G)) :
    DiagRepresentableOnAffineLfp B hS G :=
  fun V _ _ a b => (uliftYoneda_relativelyRepresentable_diag_iff.mp hdiag) V a b

/-- **Step (3) ⇒ (1) of Stacks 0GE5 for the diagonal, at an affine test object over an affine
open of `S`.** Let `F'` be a Zariski sheaf on the big fppf site of `S` which is limit preserving
and whose restriction to the locally Noetherian site has diagonal representable over the affine
test objects of finite presentation over `S`. For an affine object `W` of the site whose structure
morphism factors through an affine open of `S`, the equalizer of any two sections of `F'` over `W`
is represented by a morphism locally of finite type. -/
theorem exists_representsEqualizer_of_isAffineOverAffineOpen_of_affineLfp
    (hFs : IsCoveringSheafOnSubcategory.{max w (u + 1), u, u} .zariski (IsContainedOver B (S := S))
      ((toBigFppfOver B hS).op ⋙ F'))
    (hFl : LimitPreserving.{u, max w (u + 1), u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F')
    (hdiag : DiagRepresentableOnAffineLfp B hS
      ((LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F'))
    (W : BigFppfOver B S hS) (hW : IsAffineOverAffineOpen ((bigFppfOverToOver B hS).obj W))
    (a b : F'.obj (op W)) :
    ∃ (X : BigFppfOver B S hS) (snd : X ⟶ W), RepresentsEqualizer.{max w (u + 1)} F' snd a b ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map snd) := by
  let P := IsContainedLocallyNoetherianOver B (S := S)
  obtain ⟨Λ, _, _, _, D, c, hc, ci, haff⟩ :=
    exists_lfpPresentation (hasFinitePresentationAffines_isContainedLocallyNoetherianOver B hS) _ hW
  let ι := LocallyNoetherianOver.toBigFppfOver B S hS
  let G : (lfpPart P).FullSubcategory ⥤ LocallyNoetherianOver B S hS :=
    ObjectProperty.ιOfLE (lfpPart_le P) ⋙ toLocallyNoetherianOver B hS
  let D' : Λᵒᵖ ⥤ BigFppfOver B S hS := D ⋙ G ⋙ ι
  let hK := fullyFaithfulBigFppfOverToOver B hS
  let c' : Cone D' :=
    { pt := W
      π :=
        { app := fun l => hK.preimage (ci.inv ≫ c.π.app l)
          naturality := by
            intro l l' f
            apply hK.map_injective
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Functor.map_comp, Functor.FullyFaithful.map_preimage]
            exact congrArg (ci.inv ≫ ·) (c.w f).symm } }
  have hKc : IsLimit ((bigFppfOverToOver B hS).mapCone c') :=
    IsLimit.ofIsoLimit hc (Cone.ext ci (fun l => by
      show c.π.app l = ci.hom ≫ (bigFppfOverToOver B hS).map (c'.π.app l)
      exact (by rw [hK.map_preimage]; exact (Iso.hom_inv_id_assoc ci (c.π.app l)).symm :
        c.π.app l = ci.hom ≫ (bigFppfOverToOver B hS).map
          (hK.preimage (Y := D'.obj l) (ci.inv ≫ c.π.app l)))))
  have : IsConnected Λᵒᵖ := IsCofiltered.isConnected _
  have hc' : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c') :=
    isLimitOfPreserves (Over.forget S) hKc
  obtain ⟨hcol⟩ := hFl Λᵒᵖ D' c' hc' haff hW.1
  obtain ⟨l₁, a₁, ha₁⟩ := exists_eq_map_of_isColimit_mapCocone F' D' c' hcol a
  obtain ⟨l₂, b₂, hb₂⟩ := exists_eq_map_of_isColimit_mapCocone F' D' c' hcol b
  let l := IsCofiltered.min l₁ l₂
  let a' := F'.map (D'.map (IsCofiltered.minToLeft l₁ l₂)).op a₁
  let b' := F'.map (D'.map (IsCofiltered.minToRight l₁ l₂)).op b₂
  have ha : F'.map (c'.π.app l).op a' = a := by
    rw [← Functor.map_comp_apply, ← op_comp, c'.w]
    exact ha₁
  have hb : F'.map (c'.π.app l).op b' = b := by
    rw [← Functor.map_comp_apply, ← op_comp, c'.w]
    exact hb₂
  obtain ⟨X₀, snd₀, hrep⟩ := hdiag (G.obj (D.obj l)) (haff l) (D.obj l).property.2 a' b'
  obtain ⟨h₁, hX₀⟩ := representsEqualizer_of_locallyNoetherian B hS hFs hFl snd₀
    (D.obj l).property.2 a' b' hrep
  refine ⟨pullback (ι.map snd₀) (c'.π.app l), pullback.snd _ _, ?_, ?_⟩
  · have := representsEqualizer_pullback h₁ (c'.π.app l)
    rwa [ha, hb] at this
  · let A := BigFppfOver.toScheme B S hS
    have := preservesLimitsOfShape_walkingCospan_toScheme B hS
    have hpb := (IsPullback.of_hasPullback (ι.map snd₀) (c'.π.app l)).map A
    have hV : LocallyOfFinitePresentation (B.inclusion.map (G.obj (D.obj l)).1.hom) :=
      (D.obj l).property.2
    have hw : A.map (ι.map snd₀) ≫ B.inclusion.map (G.obj (D.obj l)).1.hom =
        B.inclusion.map X₀.1.hom := by
      rw [← Over.w snd₀.hom]
      exact (B.inclusion.map_comp _ _).symm
    have hft : LocallyOfFiniteType (A.map (ι.map snd₀)) := by
      have : LocallyOfFiniteType
          (A.map (ι.map snd₀) ≫ B.inclusion.map (G.obj (D.obj l)).1.hom) := by
        rw [hw]
        infer_instance
      exact LocallyOfFiniteType.of_comp this
    exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb hft

/-- **Step (3) ⇒ (1) of Stacks 0GE5 for the diagonal, at an affine test object over an affine
open of `S`**, for a functor whose restriction to the locally Noetherian site has representable
diagonal. -/
theorem exists_representsEqualizer_of_isAffineOverAffineOpen
    (hFs : IsCoveringSheafOnSubcategory.{max w (u + 1), u, u} .zariski (IsContainedOver B (S := S))
      ((toBigFppfOver B hS).op ⋙ F'))
    (hFl : LimitPreserving.{u, max w (u + 1), u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F')
    (hdiag : (uliftYoneda.{max w (u + 1)}
      (C := LocallyNoetherianOver B S hS)).relativelyRepresentable
        (diag ((LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F')))
    (W : BigFppfOver B S hS) (hW : IsAffineOverAffineOpen ((bigFppfOverToOver B hS).obj W))
    (a b : F'.obj (op W)) :
    ∃ (X : BigFppfOver B S hS) (snd : X ⟶ W), RepresentsEqualizer.{max w (u + 1)} F' snd a b ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map snd) :=
  exists_representsEqualizer_of_isAffineOverAffineOpen_of_affineLfp B hS hFs hFl
    (diagRepresentableOnAffineLfp_of_relativelyRepresentable B hS hdiag) W hW a b

omit [IsLocallyNoetherian S] in
/-- **The affine opens lying over affine opens of `S` cover every object of the site**, and a
Zariski sheaf is separated for this covering. -/
theorem exists_isAffineOverAffineOpen_bigFppfOver_cover (Z : BigFppfOver B S hS) :
    ∃ (ι : Type u) (W : ι → BigFppfOver B S hS) (j : ∀ i, W i ⟶ Z),
      (∀ i, IsAffineOverAffineOpen ((bigFppfOverToOver B hS).obj (W i))) ∧
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j i))) ∧
      (∀ z : (BigFppfOver.toScheme B S hS).obj Z, ∃ i,
        z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (j i))) ∧
      ∀ {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v},
        IsCoveringSheafOnSubcategory.{v, u, u} .zariski (IsContainedOver B (S := S))
          ((toBigFppfOver B hS).op ⋙ G) →
        ∀ x y : G.obj (op Z), (∀ i, G.map (j i).op x = G.map (j i).op y) → x = y := by
  let Zc := (fromBigFppfOver B hS).obj Z
  let X := Zc.obj
  let ι := {V : X.left.Opens // IsAffineOverAffineOpen (overOpen X V)}
  let Yc : ι → (IsContainedOver B (S := S)).FullSubcategory := fun i =>
    ⟨overOpen X i.1, (Scheme.size_coe_opens_le X.left i.1).trans_lt Zc.property⟩
  let fc : ∀ i, Yc i ⟶ Zc := fun i => ObjectProperty.homMk (overOpenι X i.1)
  have hsurj : ∀ z : X.left, ∃ i : ι, z ∈ Set.range ((overOpenι X i.1).left) := by
    intro z
    obtain ⟨V, -, hzV, -, hV⟩ := exists_isAffineOverAffineOpen_nbhd X z ⊤ trivial
    exact ⟨⟨V, hV⟩, ⟨⟨z, hzV⟩, rfl⟩⟩
  refine ⟨ι, fun i => (toBigFppfOver B hS).obj (Yc i), fun i => (toBigFppfOver B hS).map (fc i),
    fun i => i.2, fun i => ?_, hsurj, fun {G} hG x y hxy => ?_⟩
  · show IsOpenImmersion i.1.ι
    infer_instance
  · have hcov : Presieve.ofArrows (fun i => (Yc i).obj)
        (fun i => (IsContainedOver B (S := S)).ι.map (fc i)) ∈
        coveringPrecoverage S .zariski Zc.obj := by
      rw [ofArrows_mem_coveringPrecoverage_iff]
      exact ⟨hsurj, fun i => (inferInstance : IsOpenImmersion i.1.ι)⟩
    exact (hG Zc Yc fc hcov).isSeparatedFor.ext fun _ _ ⟨i⟩ => hxy i

omit [IsLocallyNoetherian S] in
/-- **A morphism of the site representing an equalizer is a monomorphism of schemes.** -/
theorem mono_toScheme_map_of_representsEqualizer {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    {X T : BigFppfOver B S hS} {snd : X ⟶ T} {a b : P.obj (op T)}
    (h : RepresentsEqualizer.{w} P snd a b) : Mono ((BigFppfOver.toScheme B S hS).map snd) := by
  let A := BigFppfOver.toScheme B S hS
  have := preservesLimitsOfShape_walkingCospan_toScheme B hS
  have hpb := (IsPullback.of_hasPullback snd snd).map A
  have heq : pullback.fst snd snd = pullback.snd snd snd := h.1 _ _ _ pullback.condition
  refine ⟨fun g g' hg => ?_⟩
  exact (hpb.lift_fst g g' hg).symm.trans
    ((congrArg (fun k => hpb.lift g g' hg ≫ A.map k) heq).trans (hpb.lift_snd g g' hg))

variable
    (hFs : IsCoveringSheafOnSubcategory.{max w (u + 1), u, u} .zariski (IsContainedOver B (S := S))
      ((toBigFppfOver B hS).op ⋙ F'))
    (hFl : LimitPreserving.{u, max w (u + 1), u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F')
    (hdiag : (uliftYoneda.{max w (u + 1)}
      (C := LocallyNoetherianOver B S hS)).relativelyRepresentable
        (diag ((LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F')))
    (hdiagLfp : DiagRepresentableOnAffineLfp B hS
      ((LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F'))

include hFs hFl hdiagLfp in
/-- **The equalizer of two sections of `F'` is an fppf sheaf**, for a functor whose restriction to
the locally Noetherian site has diagonal representable over the affine test objects of finite
presentation over `S`. -/
theorem isSheaf_sectionEqualizerYoneda_of_affineLfp {T : BigFppfOver B S hS}
    (a b : F'.obj (op T)) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (sectionEqualizerYoneda.{max w (u + 1)} F' a b).toFunctor := by
  let J := BigFppfOver.topology B S hS
  rw [isSheaf_iff_isSheaf_of_type, Subfunctor.isSheaf_iff _
    ((isSheaf_iff_isSheaf_of_type J _).1 (J.yoneda.obj T).property)]
  intro U s hs
  obtain ⟨ι, W, j, haff, -, -, hsep⟩ := exists_isAffineOverAffineOpen_bigFppfOver_cover B hS U.unop
  show F'.map s.op a = F'.map s.op b
  refine hsep hFs _ _ fun i => ?_
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp]
  obtain ⟨X, snd, hrep, -⟩ := exists_representsEqualizer_of_isAffineOverAffineOpen_of_affineLfp B
    hS hFs hFl hdiagLfp (W i) (haff i) (F'.map (j i ≫ s).op a) (F'.map (j i ≫ s).op b)
  refine eq_of_representsEqualizer (J := J) hrep ?_
  refine J.superset_covering ?_ (J.pullback_stable (j i) hs)
  intro Z g hg
  have hg' : F'.map ((g ≫ j i) ≫ s).op a = F'.map ((g ≫ j i) ≫ s).op b := hg
  show F'.map (g ≫ 𝟙 _).op (F'.map (j i ≫ s).op a) =
    F'.map (g ≫ 𝟙 _).op (F'.map (j i ≫ s).op b)
  rw [Category.comp_id, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
    ← op_comp, ← Category.assoc]
  exact hg'

include hFs hFl hdiag in
/-- **The equalizer of two sections of `F'` is an fppf sheaf**, for a functor whose restriction to
the locally Noetherian site has representable diagonal. -/
theorem isSheaf_sectionEqualizerYoneda {T : BigFppfOver B S hS} (a b : F'.obj (op T)) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (sectionEqualizerYoneda.{max w (u + 1)} F' a b).toFunctor :=
  isSheaf_sectionEqualizerYoneda_of_affineLfp B hS hFs hFl
    (diagRepresentableOnAffineLfp_of_relativelyRepresentable B hS hdiag) a b

include hFs hFl hdiagLfp in
/-- **Stacks 0GE5, (3) ⇒ (1), for the diagonal.** Let `F'` be a functor on the big fppf site of a
locally Noetherian scheme `S` which is a Zariski sheaf and limit preserving, and whose restriction
to the locally Noetherian site has diagonal representable over the affine test objects of finite
presentation over `S`. Then the equalizer of any two sections of `F'` is represented by a morphism
locally of finite type. -/
theorem exists_representsEqualizer_lft_of_affineLfp (T : BigFppfOver B S hS)
    (a b : F'.obj (op T)) :
    ∃ (X : BigFppfOver B S hS) (snd : X ⟶ T), RepresentsEqualizer.{max w (u + 1)} F' snd a b ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map snd) := by
  let J := BigFppfOver.topology B S hS
  let A := BigFppfOver.toScheme B S hS
  have := preservesLimitsOfShape_walkingCospan_toScheme B hS
  let E := sectionEqualizerYoneda.{max w (u + 1)} F' a b
  have : MorphismProperty.RespectsIso (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType).RespectsIso :=
    MorphismProperty.RespectsIso.inf _ _
  have : ((MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType).inverseImage
      (BigFppfOver.toScheme B S hS)).RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  let R : Sieve T :=
    Sieve.generate fun Y _ => IsAffineOverAffineOpen ((bigFppfOverToOver B hS).obj Y)
  have hR : R ∈ J T := by
    obtain ⟨ι, W, j, haff, hopen, hsurj, -⟩ :=
      exists_isAffineOverAffineOpen_bigFppfOver_cover.{max w (u + 1)} B hS T
    refine J.superset_covering ?_
      (BigFppfOver.sieve_ofArrows_mem_topology_of_jointlySurjective B S hS W T j hopen hsurj)
    rintro Y _ ⟨Z, g, _, ⟨i⟩, rfl⟩
    exact ⟨_, g, j i, haff i, rfl⟩
  have hdesc := Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS E.ι
    (isSheaf_sectionEqualizerYoneda_of_affineLfp B hS hFs hFl hdiagLfp a b)
    (J.yoneda.obj T).property (𝟙 (yoneda.obj T)) R hR (by
      rintro Y _ ⟨Y₀, g, q₀, hq₀, rfl⟩
      obtain ⟨X₀, snd₀, hrep₀, hlft₀⟩ :=
        exists_representsEqualizer_of_isAffineOverAffineOpen_of_affineLfp B hS hFs hFl hdiagLfp Y₀
          hq₀ (F'.map q₀.op a) (F'.map q₀.op b)
      refine MorphismProperty.relative.of_exists fun Z g' => ?_
      let φ : Z ⟶ Y := yoneda.preimage g'
      let π := φ ≫ g
      have hrep := representsEqualizer_pullback hrep₀ π
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp] at hrep
      have hrepφ' : RepresentsEqualizer.{max w (u + 1)} F' (pullback.snd snd₀ π)
          (F'.map (φ ≫ g ≫ q₀).op a) (F'.map (φ ≫ g ≫ q₀).op b) := by
        simpa only [π, Category.assoc] using hrep
      have hout := isPullback_sectionEqualizerYoneda (φ ≫ g ≫ q₀) hrepφ'
      have hbot := IsPullback.of_hasPullback E.ι (yoneda.map (g ≫ q₀) ≫ 𝟙 _)
      have hg' : g' = yoneda.map φ := (Functor.map_preimage yoneda g').symm
      let top : yoneda.obj (pullback snd₀ π) ⟶ E.toFunctor :=
        E.lift (yoneda.map (pullback.snd snd₀ π ≫ φ ≫ g ≫ q₀))
          (range_le_sectionEqualizerYoneda _ hrepφ')
      have hcond : top ≫ E.ι = (yoneda.map (pullback.snd snd₀ π) ≫ g') ≫
          (yoneda.map (g ≫ q₀) ≫ 𝟙 _) := by
        rw [hout.w, hg', Category.comp_id, ← Functor.map_comp, ← Functor.map_comp,
          ← Functor.map_comp, Category.assoc]
      refine ⟨pullback snd₀ π, pullback.lift top (yoneda.map (pullback.snd snd₀ π) ≫ g') hcond,
        pullback.snd snd₀ π, ?_, ?_, ?_⟩
      · refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hbot
        rw [pullback.lift_fst, hg', Category.comp_id, ← Functor.map_comp]
        exact hout
      · exact mono_toScheme_map_of_representsEqualizer B hS hrepφ'
      · have hpb := (IsPullback.of_hasPullback snd₀ π).map A
        exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb hlft₀)
  obtain ⟨X, snd, fst, hpb⟩ := hdesc.rep (𝟙 (yoneda.obj T))
  have h := hpb.paste_horiz (IsPullback.of_hasPullback E.ι (𝟙 (yoneda.obj T)))
  rw [Category.comp_id] at h
  exact ⟨X, snd, representsEqualizer_of_isPullback h, (hdesc.2 _ fst snd hpb).2⟩

include hFs hFl hdiagLfp in
/-- **Stacks 0GE5, (3) ⇒ (1), for the diagonal**, in the form of a representable diagonal: if the
restriction of `F'` to the locally Noetherian site has diagonal representable over the affine test
objects of finite presentation over `S`, then the diagonal of `F'` is representable. -/
theorem relativelyRepresentable_diag_of_affineLfp :
    (uliftYoneda.{max w (u + 1)} (C := BigFppfOver B S hS)).relativelyRepresentable (diag F') := by
  rw [uliftYoneda_relativelyRepresentable_diag_iff]
  intro T a b
  obtain ⟨X, snd, h, -⟩ := exists_representsEqualizer_lft_of_affineLfp B hS hFs hFl hdiagLfp T a b
  exact ⟨X, snd, h⟩

include hFs hFl hdiag in
/-- **Stacks 0GE5, (2) ⇒ (1), for the diagonal.** Let `F'` be a functor on the big fppf site of a
locally Noetherian scheme `S` which is a Zariski sheaf and limit preserving, and whose restriction
to the locally Noetherian site has representable diagonal. Then the diagonal of `F'` is
representable. -/
theorem relativelyRepresentable_diag_of_restriction :
    (uliftYoneda.{max w (u + 1)} (C := BigFppfOver B S hS)).relativelyRepresentable (diag F') :=
  relativelyRepresentable_diag_of_affineLfp B hS hFs hFl
    (diagRepresentableOnAffineLfp_of_relativelyRepresentable B hS hdiag)

end Diagonal

end AlgebraicGeometry.ExtendingFunctors
