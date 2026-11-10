module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The hypothesis and the universal direct image of a proper flat family

Tag 0E62 concerns a proper, flat, finitely presented `f : X ⟶ S` all of whose fibres have
only constant functions, and asserts (a) that `f_* 𝒪_X = 𝒪_S` universally and (b) a local
splitting of `Rf_* 𝒪_X` in the derived category.

This file does not prove (a) or (b).  It establishes the identifications on which any proof
of them rests, and it settles the direction of (a) that needs no cohomology at all.

Two different spellings occur in the statement of 0E62: the fibre hypothesis is phrased with
the comparison `𝒪 ⟶ f_* 𝒪` of **sheaves of modules**, while the conclusion of (a) is phrased
with the comparison `f.c` of **sheaves of rings**.  `isIso_c_iff_isIso_unitToPushforwardObjUnit`
shows the two are the same assertion, so hypothesis and conclusion are one predicate applied
to two morphisms: to the fibre morphisms, and to the base changes.

Once that is available, `forall_isIso_fiber_unit_of_baseChange` observes that the fibre over
`s` *is* the base change along `S.fromSpecResidueField s`, so (a) **implies** the hypothesis of
0E62.  Hence (a) is an equivalence, not an implication, and its hypothesis cannot be weakened.

## Main results

* `isIso_unitToPushforwardObjUnit_iff`: for a morphism of ringed sites, the comparison
  `𝒪 ⟶ f_* 𝒪` of sheaves of modules is invertible exactly when the morphism of sheaves of
  rings is bijective on every object.
* `isIso_c_iff`, `isIso_c_iff_isIso_app`: `f.c` is invertible exactly when it is bijective,
  respectively invertible, on the sections over every open.
* `isIso_c_iff_isIso_unitToPushforwardObjUnit`: the two spellings of `f_* 𝒪_X = 𝒪_Y` for a
  morphism of schemes agree.
* `isIso_c_iff_bijective_appTop`: over a base whose space is a subsingleton -- the spectrum of
  a field -- the assertion is bijectivity on global sections alone.
* `isIso_fiberToSpecResidueField_unit_iff`: the fibre hypothesis of 0E62 at `s` is exactly the
  source's clause `κ(s) = H⁰(X_s, 𝒪_{X_s})`, as bijectivity of a map of rings.
* `isIso_c_of_isPullback`: the conclusion of (a) transfers from the chosen pullback to every
  cartesian square, so the statement does not depend on Mathlib's choice of pullback.
* `forall_isIso_fiber_unit_of_baseChange` and `baseChange_iff_forall_fiber_unit`: (a) implies
  the hypothesis of 0E62, so (a) is equivalent to it.

## Implementation notes

`isIso_c_iff_isIso_unitToPushforwardObjUnit` is proved in term mode.  Rewriting fails here:
`Scheme.ringCatSheaf` is stated over `↑Y.toPresheafedSpace` while the site lemma is stated over
`Opens.grothendieckTopology ↥Y`, and the two are not identified at the transparency `rw` uses.

A one-directional form of `isIso_unitToPushforwardObjUnit_iff` already exists in this tree as
`Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit`; it carries two `HasSheafCompose` hypotheses
and
only the implication from invertibility of the whole morphism of sheaves of rings.  The version
here is an equivalence, is componentwise, and needs no extra instances.

Properness, flatness and local finite presentation of `pullback.snd f g` are already instances
in Mathlib and are not restated.  `baseChange_of_absolute_of_fiber_stable` records that they are
the only standing assumptions the base change inherits for free.

## References

* [Stacks Project, Tag 0E62](https://stacks.math.columbia.edu/tag/0E62)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.AlgebraicGeometry.ProperFlatFamilyUnit

universe v₁ v₂ u₁ u₂ u

section Sites

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} [Functor.IsContinuous F J K]

/-- The canonical morphism `𝒪 ⟶ f_* 𝒪` of sheaves of modules attached to a morphism of
ringed sites is invertible exactly when the underlying morphism of sheaves of rings is
bijective on every object. -/
theorem isIso_unitToPushforwardObjUnit_iff
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit φ) ↔
      ∀ X : Cᵒᵖ, Function.Bijective (φ.hom.app X) := by
  rw [← isIso_iff_of_reflects_iso _
    (SheafOfModules.forget.{u} S ⋙ PresheafOfModules.toPresheaf S.obj),
    NatTrans.isIso_iff_isIso_app]
  refine forall_congr' fun X ↦ ?_
  rw [← isIso_iff_of_reflects_iso _ (forget AddCommGrpCat.{u}), isIso_iff_bijective]
  rfl

end Sites

section Schemes

open _root_.AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The comparison `𝒪_Y ⟶ f_* 𝒪_X` of sheaves of rings is invertible exactly when it is
invertible on the sections over every open of `Y`. -/
theorem isIso_c_iff_isIso_app (f : X ⟶ Y) :
    IsIso f.c ↔ ∀ U : Y.Opens, IsIso (f.app U) := by
  rw [NatTrans.isIso_iff_isIso_app, Opposite.op_surjective.forall]

/-- The comparison `𝒪_Y ⟶ f_* 𝒪_X` of sheaves of rings is invertible exactly when it is
bijective on the sections over every open of `Y`. -/
theorem isIso_c_iff (f : X ⟶ Y) :
    IsIso f.c ↔ ∀ U : Y.Opens, Function.Bijective (f.app U) := by
  rw [isIso_c_iff_isIso_app]
  exact forall_congr' fun U ↦ ConcreteCategory.isIso_iff_bijective _

/-- The two spellings of `f_* 𝒪_X = 𝒪_Y` agree: the comparison of sheaves of rings is
invertible exactly when the comparison `𝒪_Y ⟶ f_* 𝒪_X` of sheaves of modules is. -/
theorem isIso_c_iff_isIso_unitToPushforwardObjUnit (f : X ⟶ Y) :
    IsIso f.c ↔
      IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) :=
  (isIso_c_iff f).trans
    (((isIso_unitToPushforwardObjUnit_iff f.toRingCatSheafHom).trans
      Opposite.op_surjective.forall).symm)

/-- On a scheme whose underlying space is a subsingleton, the only opens are `⊥` and `⊤`. -/
theorem opens_eq_bot_or_eq_top [Subsingleton (X : Type u)] (U : X.Opens) :
    U = ⊥ ∨ U = ⊤ := by
  rcases Set.eq_empty_or_nonempty (U : Set X) with hU | ⟨x, hx⟩
  · exact Or.inl (Opens.ext hU)
  · refine Or.inr (Opens.ext (Set.eq_univ_of_forall fun y ↦ ?_))
    rwa [Subsingleton.elim y x]

/-- The comparison is bijective on sections over the empty open, for any morphism of
schemes: both rings of sections are terminal. -/
theorem isIso_app_of_eq_bot (f : X ⟶ Y) {U : Y.Opens} (hU : U = ⊥) :
    IsIso (f.app U) := by
  have h₁ : IsTerminal Γ(Y, U) := Y.sheaf.isTerminalOfEqEmpty hU
  have h₂ : IsTerminal Γ(X, f ⁻¹ᵁ U) :=
    X.sheaf.isTerminalOfEqEmpty (by rw [hU]; exact Opens.ext (by simp))
  exact ⟨h₁.from _, h₁.hom_ext _ _, h₂.hom_ext _ _⟩

/-- If the target's space is a subsingleton -- as for the spectrum of a field -- then
`f_* 𝒪_X = 𝒪_Y` is exactly the statement that `f` is bijective on global sections. -/
theorem isIso_c_iff_bijective_appTop [Subsingleton (Y : Type u)] (f : X ⟶ Y) :
    IsIso f.c ↔ Function.Bijective f.appTop := by
  rw [isIso_c_iff]
  refine ⟨fun h ↦ h ⊤, fun h U ↦ ?_⟩
  rcases opens_eq_bot_or_eq_top U with hU | hU
  · have := isIso_app_of_eq_bot f hU
    exact ConcreteCategory.bijective_of_isIso _
  · subst hU; exact h

/-- `f_* 𝒪_X = 𝒪_Y` is unchanged by precomposition with an isomorphism of schemes. -/
theorem isIso_c_comp {Z : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (p : Y ⟶ Z) (h : IsIso p.c) :
    IsIso (e ≫ p).c := by
  rw [isIso_c_iff_isIso_app] at h ⊢
  intro U
  rw [Scheme.Hom.comp_app]
  have h2 : IsIso (e.app (p ⁻¹ᵁ U)) := by infer_instance
  exact IsIso.comp_isIso' (h U) h2

/-- The conclusion `f'_* 𝒪_{X'} = 𝒪_{S'}` holds for every cartesian square over `g` as soon
as it holds for the chosen pullback: the statement does not depend on the choice. -/
theorem isIso_c_of_isPullback {S X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} (sq : IsPullback g' f' f g)
    (h : IsIso (pullback.snd f g).c) : IsIso f'.c := by
  have he : sq.isoPullback.hom ≫ pullback.snd f g = f' := sq.isoPullback_hom_snd
  rw [← he]
  exact isIso_c_comp _ _ h

/-- Bijectivity of a ring map is unaffected by precomposition with an isomorphism. -/
theorem bijective_inv_comp_iff {R₁ R₂ R₃ : CommRingCat.{u}} (e : R₁ ≅ R₂) (φ : R₁ ⟶ R₃) :
    Function.Bijective (e.inv ≫ φ) ↔ Function.Bijective φ := by
  rw [← ConcreteCategory.isIso_iff_bijective, ← ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := h; exact IsIso.of_isIso_comp_left e.inv φ
  · exact IsIso.comp_isIso' inferInstance h

end Schemes

section Fiber

open _root_.AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The fibre hypothesis at `s`, in the form the tagged statement uses, is invertibility of the
comparison
of sheaves of rings for the fibre morphism. -/
theorem isIso_fiberToSpecResidueField_unit_iff_isIso_c (f : X ⟶ S) (s : S) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit
        (f.fiberToSpecResidueField s).toRingCatSheafHom) ↔
      IsIso (f.fiberToSpecResidueField s).c :=
  (isIso_c_iff_isIso_unitToPushforwardObjUnit _).symm

/-- The fibre hypothesis at `s` is exactly the source's degree-zero condition
`κ(s) = H⁰(X_s, 𝒪_{X_s})`: the canonical ring map from the residue field to the global
functions on the scheme-theoretic fibre is bijective. -/
theorem isIso_fiberToSpecResidueField_unit_iff (f : X ⟶ S) (s : S) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit
        (f.fiberToSpecResidueField s).toRingCatSheafHom) ↔
      Function.Bijective ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
        (f.fiberToSpecResidueField s).appTop) :=
  ((isIso_fiberToSpecResidueField_unit_iff_isIso_c f s).trans
    (isIso_c_iff_bijective_appTop _)).trans
      (bijective_inv_comp_iff _ _).symm

/-- The standing hypothesis of the statement, clause (2) of the source, with every fibre condition
replaced by the bijectivity of `κ(s) ⟶ H⁰(X_s, 𝒪_{X_s})`. -/
theorem forall_isIso_fiberToSpecResidueField_unit_iff (f : X ⟶ S) :
    (∀ s : S, IsIso (SheafOfModules.unitToPushforwardObjUnit
        (f.fiberToSpecResidueField s).toRingCatSheafHom)) ↔
      ∀ s : S, Function.Bijective ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
        (f.fiberToSpecResidueField s).appTop) :=
  forall_congr' fun s ↦ isIso_fiberToSpecResidueField_unit_iff f s

end Fiber

section BaseChange

open _root_.AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- Part (a) of the statement, restated in the vocabulary of its own hypothesis: the universal
direct-image assertion says that for each base change the comparison `𝒪_{S'} ⟶ f'_* 𝒪_{X'}`
of sheaves of modules is invertible. -/
theorem baseChange_isIso_c_iff_unit (f : X ⟶ S) :
    (∀ {S' : Scheme.{u}} (g : S' ⟶ S), IsIso (pullback.snd f g).toLRSHom.toHom.c) ↔
      ∀ {S' : Scheme.{u}} (g : S' ⟶ S), IsIso (SheafOfModules.unitToPushforwardObjUnit
        (pullback.snd f g).toRingCatSheafHom) :=
  ⟨fun h _ g ↦ (isIso_c_iff_isIso_unitToPushforwardObjUnit _).1 (h g),
    fun h _ g ↦ (isIso_c_iff_isIso_unitToPushforwardObjUnit _).2 (h g)⟩

/-- Part (a) of the statement, restated on sections. -/
theorem baseChange_isIso_c_iff_bijective (f : X ⟶ S) :
    (∀ {S' : Scheme.{u}} (g : S' ⟶ S), IsIso (pullback.snd f g).toLRSHom.toHom.c) ↔
      ∀ {S' : Scheme.{u}} (g : S' ⟶ S) (V : S'.Opens),
        Function.Bijective ((pullback.snd f g).app V) :=
  ⟨fun h _ g ↦ (isIso_c_iff _).1 (h g), fun h _ g ↦ (isIso_c_iff _).2 (h g)⟩

/-- Part (a) of the statement gives the assertion for every cartesian square over the base change,
not only for the chosen pullback. -/
theorem isIso_c_of_isPullback_of_baseChange (f : X ⟶ S)
    (h : ∀ {S' : Scheme.{u}} (g : S' ⟶ S), IsIso (pullback.snd f g).toLRSHom.toHom.c)
    {X' S' : Scheme.{u}} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) : IsIso f'.c :=
  isIso_c_of_isPullback sq (h g)

/-- Part (a) of the statement contains its standing hypothesis.  The fibre over `s` is by
definition the base change of `f` along `S.fromSpecResidueField s`, and
`f.fiberToSpecResidueField s` is by definition the corresponding `pullback.snd`; so the
universal direct-image assertion, applied to that one base change, is exactly the hypothesis
`κ(s) = H⁰(X_s, 𝒪_{X_s})` at `s`.  No properness, flatness or finiteness is used. -/
theorem forall_isIso_fiber_unit_of_baseChange (f : X ⟶ S)
    (h : ∀ {S' : Scheme.{u}} (g : S' ⟶ S), IsIso (pullback.snd f g).toLRSHom.toHom.c) (s : S) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit
      (f.fiberToSpecResidueField s).toRingCatSheafHom) :=
  (isIso_c_iff_isIso_unitToPushforwardObjUnit _).1 (h (S.fromSpecResidueField s))

/-- Consequently part (a) of the statement is an equivalence: its hypothesis is implied by its
conclusion.  Here the hard implication is supplied as `hard`; it is the content of Tag 0E62
and is not proved in this file. -/
theorem baseChange_iff_forall_fiber_unit (f : X ⟶ S)
    (hard : (∀ s : S, IsIso (SheafOfModules.unitToPushforwardObjUnit
        (f.fiberToSpecResidueField s).toRingCatSheafHom)) →
      ∀ {S' : Scheme.{u}} (g : S' ⟶ S), IsIso (pullback.snd f g).toLRSHom.toHom.c) :
    (∀ {S' : Scheme.{u}} (g : S' ⟶ S), IsIso (pullback.snd f g).toLRSHom.toHom.c) ↔
      ∀ s : S, IsIso (SheafOfModules.unitToPushforwardObjUnit
        (f.fiberToSpecResidueField s).toRingCatSheafHom) :=
  ⟨forall_isIso_fiber_unit_of_baseChange f, fun h _ g ↦ hard h g⟩

/-- What the words "and this holds after any base change" add to part (a), and nothing more.
Properness, flatness and local finite presentation are already stable under base change in
Mathlib, so the base-changed morphism satisfies the standing assumptions of the statement
automatically;
the only further input is that the fibre condition is inherited by the base change.  The proof
is bookkeeping: its whole content is that the three instances fire for `pullback.snd f g`. -/
theorem baseChange_of_absolute_of_fiber_stable (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (habs : ∀ {X₀ S₀ : Scheme.{u}} (f₀ : X₀ ⟶ S₀), IsProper f₀ → Flat f₀ →
      LocallyOfFinitePresentation f₀ →
      (∀ s : S₀, IsIso (SheafOfModules.unitToPushforwardObjUnit
        (f₀.fiberToSpecResidueField s).toRingCatSheafHom)) → IsIso f₀.c)
    (hstab : ∀ {S' : Scheme.{u}} (g : S' ⟶ S) (s' : S'),
      IsIso (SheafOfModules.unitToPushforwardObjUnit
        ((pullback.snd f g).fiberToSpecResidueField s').toRingCatSheafHom))
    {S' : Scheme.{u}} (g : S' ⟶ S) :
    IsIso (pullback.snd f g).toLRSHom.toHom.c :=
  habs (pullback.snd f g) inferInstance inferInstance inferInstance (hstab g)

end BaseChange

end Stacks.AlgebraicGeometry.ProperFlatFamilyUnit
