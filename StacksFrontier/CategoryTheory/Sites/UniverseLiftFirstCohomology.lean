module

public import Mathlib.Algebra.Group.Shrink
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.MapBijectiveOne
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftColimits
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftInjective

/-!
# First cohomology is unchanged by raising the universe of the coefficients

Let `(C, J)` be a site and `F` a sheaf of abelian groups on it with sections in `Type t`. Raising
the universe of all sections, `Stacks.Sheaves.UniverseLift.uliftSheafFunctor`, does not change
`H¹(C, F)`.

The reason is that `H¹` classifies extensions of the constant sheaf `ℤ` by `F`, and an extension
of two universe lifts is again a universe lift: in a short exact sequence of sheaves
`0 → F' → E → G' → 0` the sections of `E` over an object are an extension of a subgroup of the
sections of `G'` by the sections of `F'`, so they are as small as those of `F'` and `G'` are, and
`E` is the universe lift of the sheaf of shrunk sections. The comparison of `Ext¹` along a fully
faithful exact functor whose image is closed under extensions,
`CategoryTheory.Functor.mapExtAddHom_one_bijective`, then applies.

## Main definitions

* `Stacks.Sheaves.UniverseLift.shrinkSheaf`: a sheaf of abelian groups whose sections are
  `t`-small, as a sheaf with sections in `Type t`.
* `Stacks.Sheaves.UniverseLift.sheafHOneAddEquiv`: `H¹(C, F) ≃+ H¹(C, F ⋙ ULift)`.

## Main results

* `Stacks.Sheaves.UniverseLift.small_sections_of_shortExact`: the middle term of an extension
  of two universe lifts has small sections.
* `Stacks.Sheaves.UniverseLift.mapExtAddHom_one_bijective`: the universe lift is bijective on
  `Ext¹`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' s t v u

namespace Stacks.Sheaves.UniverseLift

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section Shrink

/-- An abelian group which is an extension of a `t`-small group by a `t`-small group is
`t`-small. -/
theorem small_of_injective_of_ker_le {K M N : Type*} [AddCommGroup K] [AddCommGroup M]
    [AddCommGroup N] [Small.{t} K] [Small.{t} N] (i : K →+ M) (hi : Function.Injective i)
    (g : M →+ N) (hker : ∀ m, g m = 0 → ∃ k, i k = m) : Small.{t} M := by
  have hk : ∀ m, ∃ k, i k = m - Function.invFun g (g m) := fun m =>
    hker _ (by rw [map_sub, Function.invFun_eq (f := g) ⟨m, rfl⟩, sub_self])
  refine small_of_injective (f := fun m => ((hk m).choose, g m)) ?_
  intro m m' h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have e1 := (hk m).choose_spec
  rw [h1, (hk m').choose_spec, h2] at e1
  exact (sub_left_inj.1 e1).symm

variable {J} (E : Sheaf J AddCommGrpCat.{max t s}) [hE : ∀ U, Small.{t} (E.obj.obj U)]

/-- The sections of `E` shrunk to `Type t`, as a presheaf of abelian groups. -/
noncomputable def shrinkPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{t} where
  obj U := AddCommGrpCat.of (Shrink.{t} (E.obj.obj U))
  map f := AddCommGrpCat.ofHom (Shrink.addEquiv.symm.toAddMonoidHom.comp
    ((E.obj.map f).hom.comp Shrink.addEquiv.toAddMonoidHom))
  map_id U := by
    ext x
    simp
  map_comp f g := by
    ext x
    simp

/-- The universe lift of `shrinkPresheaf E` is the presheaf underlying `E`. -/
noncomputable def shrinkPresheafIso :
    shrinkPresheaf E ⋙ AddCommGrpCat.uliftFunctor.{s, t} ≅ E.obj :=
  NatIso.ofComponents
    (fun U => (AddEquiv.ulift.trans (Shrink.addEquiv (α := E.obj.obj U))).toAddCommGrpIso)
    (fun f => by
      ext x
      change Shrink.addEquiv (Shrink.addEquiv.symm (E.obj.map f (Shrink.addEquiv x.down))) =
        E.obj.map f (Shrink.addEquiv x.down)
      exact AddEquiv.apply_symm_apply _ _)

/-- `shrinkPresheaf E` is a sheaf. -/
theorem isSheaf_shrinkPresheaf : Presheaf.IsSheaf J (shrinkPresheaf E) :=
  Presheaf.isSheaf_of_isSheaf_comp J _ AddCommGrpCat.uliftFunctor.{s, t}
    ((Presheaf.isSheaf_of_iso_iff (shrinkPresheafIso E)).2 E.property)

/-- A sheaf of abelian groups with `t`-small sections, as a sheaf with sections in `Type t`. -/
noncomputable def shrinkSheaf : Sheaf J AddCommGrpCat.{t} :=
  ⟨shrinkPresheaf E, isSheaf_shrinkPresheaf E⟩

/-- The universe lift of `shrinkSheaf E` is `E`. -/
noncomputable def uliftShrinkSheafIso : (uliftSheafFunctor.{s, t} J).obj (shrinkSheaf E) ≅ E :=
  (fullyFaithfulSheafToPresheaf J AddCommGrpCat.{max t s}).preimageIso (shrinkPresheafIso E)

end Shrink

section Extensions

variable [HasSheafify J AddCommGrpCat.{t}] [HasSheafify J AddCommGrpCat.{max t s}]

/-- In a short exact sequence of abelian sheaves, the sections of the middle term over an object
form an extension of a subgroup of the sections of the third term by those of the first. -/
theorem sections_exact {S : ShortComplex (Sheaf J AddCommGrpCat.{max t s})} (hS : S.ShortExact)
    (U : Cᵒᵖ) :
    Function.Injective (S.f.hom.app U) ∧
      ∀ x, S.g.hom.app U x = 0 → ∃ y, S.f.hom.app U y = x := by
  have := hS.mono_f
  have hmono : Mono S.f.hom :=
    inferInstanceAs (Mono ((sheafToPresheaf J AddCommGrpCat.{max t s}).map S.f))
  refine ⟨(AddCommGrpCat.mono_iff_injective _).1
    ((NatTrans.mono_iff_mono_app _).1 hmono U), ?_⟩
  let G := sheafToPresheaf J AddCommGrpCat.{max t s} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{max t s}).obj U
  exact (ShortComplex.ab_exact_iff _).1
    (hS.exact.map_of_mono_of_preservesKernel G hS.mono_f inferInstance)

omit [HasSheafify J AddCommGrpCat.{t}] in
/-- **The middle term of an extension of two universe lifts has `t`-small sections.** -/
theorem small_sections_of_shortExact {A B : Sheaf J AddCommGrpCat.{t}}
    {E : Sheaf J AddCommGrpCat.{max t s}} (i : (uliftSheafFunctor.{s, t} J).obj A ⟶ E)
    (p : E ⟶ (uliftSheafFunctor.{s, t} J).obj B) (w : i ≫ p = 0)
    (h : (ShortComplex.mk i p w).ShortExact) (U : Cᵒᵖ) : Small.{t} (E.obj.obj U) := by
  obtain ⟨hinj, hex⟩ := sections_exact J h U
  have (X : Sheaf J AddCommGrpCat.{t}) :
      Small.{t} (((uliftSheafFunctor.{s, t} J).obj X).obj.obj U) :=
    inferInstanceAs (Small.{t} (ULift (X.obj.obj U)))
  exact small_of_injective_of_ker_le (i.hom.app U).hom hinj (p.hom.app U).hom hex

section Ext

variable [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max t s}]

/-- The universe lift of abelian sheaves preserves finite colimits. -/
theorem preservesFiniteColimits_uliftSheafFunctor :
    PreservesFiniteColimits (uliftSheafFunctor.{s, t} J) := by
  have := sheafCompose_uliftFunctor_preservesColimits.{u, v, t, s} (J := J)
  exact PreservesColimitsOfSize.preservesFiniteColimits _

/-- The universe lift of abelian sheaves preserves finite limits, limits of sheaves being
computed as limits of presheaves. -/
instance preservesFiniteLimits_uliftSheafFunctor :
    PreservesFiniteLimits (uliftSheafFunctor.{s, t} J) := by
  have : PreservesFiniteLimits
      ((Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{t} AddCommGrpCat.{max t s}).obj
        AddCommGrpCat.uliftFunctor.{s, t}) :=
    ⟨fun _ _ _ => inferInstance⟩
  have : PreservesFiniteLimits
      (uliftSheafFunctor.{s, t} J ⋙ sheafToPresheaf J AddCommGrpCat.{max t s}) := by
    change PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{t} ⋙
      (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{t} AddCommGrpCat.{max t s}).obj
        AddCommGrpCat.uliftFunctor.{s, t})
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J _)

attribute [local instance] preservesFiniteColimits_uliftSheafFunctor

/-- The universe lift of abelian sheaves is additive. -/
instance additive_uliftSheafFunctor : (uliftSheafFunctor.{s, t} J).Additive where
  map_add {X Y f g} := by
    ext U x
    rfl

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] [HasExt.{w'} (Sheaf J AddCommGrpCat.{max t s})]

/-- **The universe lift of abelian sheaves is bijective on `Ext¹`.** -/
theorem mapExtAddHom_one_bijective (A B : Sheaf J AddCommGrpCat.{t}) :
    Function.Bijective ((uliftSheafFunctor.{s, t} J).mapExtAddHom B A 1) := by
  have := (fullyFaithfulUliftSheafFunctor.{s, t} J).full
  have := (fullyFaithfulUliftSheafFunctor.{s, t} J).faithful
  refine (uliftSheafFunctor.{s, t} J).mapExtAddHom_one_bijective A B
    fun E i p w h => ?_
  have := small_sections_of_shortExact.{s, t, v, u} J i p w h
  exact ⟨shrinkSheaf E, ⟨uliftShrinkSheafIso E⟩⟩

variable [HasSheafify J AddCommGrpCat.{t}] [HasSheafify J AddCommGrpCat.{max t s}]

/-- The universe lift of the constant sheaf `ℤ` is the constant sheaf `ℤ`. -/
noncomputable def uliftConstantSheafIso :
    (uliftSheafFunctor.{s, t} J).obj
        ((constantSheaf J AddCommGrpCat.{t}).obj (AddCommGrpCat.of (ULift ℤ))) ≅
      (constantSheaf J AddCommGrpCat.{max t s}).obj (AddCommGrpCat.of (ULift ℤ)) := by
  have := preservesSheafification_uliftFunctor.{u, v, t, s} (J := J)
  exact (constantCommuteCompose J AddCommGrpCat.uliftFunctor.{s, t}).app _ ≪≫
    (constantSheaf J AddCommGrpCat.{max t s}).mapIso
      (AddEquiv.toAddCommGrpIso (AddEquiv.ulift.trans
        (AddEquiv.ulift.trans AddEquiv.ulift.symm)))

/-- Precomposition with an isomorphism, as an additive equivalence of `Ext` groups. -/
noncomputable def extPrecompIsoAddEquiv {D : Type*} [Category D] [Abelian D] [HasExt.{w'} D]
    {X X' Y : D} (e : X ≅ X') (n : ℕ) : Abelian.Ext.{w'} X' Y n ≃+ Abelian.Ext.{w'} X Y n where
  toFun y := (Abelian.Ext.mk₀ e.hom).comp y (zero_add n)
  invFun z := (Abelian.Ext.mk₀ e.inv).comp z (zero_add n)
  left_inv y := by
    simp only
    rw [← Abelian.Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (zero_add n),
      Abelian.Ext.mk₀_comp_mk₀, e.inv_hom_id, Abelian.Ext.mk₀_id_comp]
  right_inv z := by
    simp only
    rw [← Abelian.Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (zero_add n),
      Abelian.Ext.mk₀_comp_mk₀, e.hom_inv_id, Abelian.Ext.mk₀_id_comp]
  map_add' y₁ y₂ := Abelian.Ext.comp_add _ _ _ _

/-- **First cohomology is unchanged by raising the universe of the coefficients.** -/
noncomputable def sheafHOneAddEquiv (F : Sheaf J AddCommGrpCat.{t}) :
    Sheaf.H.{w} F 1 ≃+ Sheaf.H.{w'} ((uliftSheafFunctor.{s, t} J).obj F) 1 :=
  (AddEquiv.ofBijective _ (mapExtAddHom_one_bijective.{w, w', s, t, v, u} J F _)).trans
    (extPrecompIsoAddEquiv (uliftConstantSheafIso.{s, t, v, u} J).symm 1)

/-- The comparison of `sheafHOneAddEquiv` is the universe lift on `Ext`, followed by the
identification of the lifted constant sheaf with the constant sheaf. -/
theorem sheafHOneAddEquiv_apply (F : Sheaf J AddCommGrpCat.{t}) (x : Sheaf.H.{w} F 1) :
    sheafHOneAddEquiv.{w, w', s, t, v, u} J F x =
      (Abelian.Ext.mk₀ (uliftConstantSheafIso.{s, t, v, u} J).inv).comp
        ((uliftSheafFunctor.{s, t} J).mapExtAddHom _ F 1 x) (zero_add 1) :=
  rfl

end Ext

end Extensions

end Stacks.Sheaves.UniverseLift
