module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange

/-!
# Base change of the restriction `M ⟶ i_* i^* M` along an open immersion

Let `i : Z ⟶ X` be a morphism of schemes, `V` an open of `X` and `i ∣_ V : i ⁻¹ᵁ V ⟶ V` the
base change of `i` along the inclusion of `V`. For an `𝒪_X`-module `M` there are two
restrictions of `M` to the data over `V`: the unit `M ⟶ i_* i^* M` of `i^* ⊣ i_*`, read over
opens of `V`, and the unit `M|_V ⟶ (i ∣_ V)_* (i ∣_ V)^* (M|_V)` of the base-changed morphism.
This file proves that the two agree.

## Main results

* `Stacks.AlgebraicGeometry.RestrictUnit.unit_pullbackRestrictIso`: **the comparison, as an
  equality of morphisms of `𝒪_X`-modules.** The unit of
  `Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictAdjunction`, followed by the
  direct image of `Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso`, is the unit
  of `Stacks.AlgebraicGeometry.AffinePushforward.restrictPullbackAdjunction`.
* `Stacks.AlgebraicGeometry.RestrictUnit.app_unit_eq_zero_iff`: **the form a consumer uses.** A
  local section of `M` over an open `W ≤ V` restricts to zero on `Z` if and only if its
  restriction to `V` restricts to zero on `i ⁻¹ᵁ V`.

## Implementation notes

The two sides of `unit_pullbackRestrictIso` are the units of two adjunctions with the *same*
right adjoint `((i ⁻¹ᵁ V).ι ≫ i)_*`, and `pullbackRestrictIso` is by definition the comparison
`CategoryTheory.Adjunction.leftAdjointUniq` of their left adjoints, so the comparison is
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` and costs nothing. All the work is in
reading it on sections.

Four factors separate the two units from the two statements about sections, and each is
invertible over an open `W ≤ V`:

* the unit of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` at an open immersion `f` is,
  on sections over `U`, the restriction map of the module along `f ''ᵁ f ⁻¹ᵁ U ≤ U`
  (`AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app`), and those two opens are
  *equal* when `U` lies inside the range of `f` — which is where the hypothesis `W ≤ V` is
  spent, through `i ⁻¹ᵁ W ≤ i ⁻¹ᵁ V`;
* `AlgebraicGeometry.Scheme.Modules.pushforwardComp`,
  `AlgebraicGeometry.Scheme.Modules.pushforwardCongr` and `pullbackRestrictIso` are
  isomorphisms, hence invertible on sections.

The opens of a scheme form a thin category, so a morphism between two opens that are equal is
invertible; that is `Stacks.AlgebraicGeometry.RestrictUnit.isIso_presheaf_map_of_eq` below, and
it is what turns the first item into an isomorphism on sections.

**Two elaboration frictions.**

First, sections of a sheaf of modules live in `AddCommGrp`, and the source of each composite
below has two spellings there — `Γ((i^* ⋙ i_*).obj M, W)` as the target of a morphism of
modules and `(i^* M).presheaf.obj (op (i ⁻¹ᵁ W))` as the source of the next factor. The two are
definitionally equal and not syntactically equal, so a composite written out by hand elaborates
but is *not* type-correct at `instance` transparency, and every later `rw` inside it fails with
`did not find an occurrence of the pattern`. So each decomposition is reached once, as a named
equation, and then used only through `ConcreteCategory.congr_hom` and
`CategoryTheory.ConcreteCategory.comp_apply` applied as *terms*.

Second, an `IsIso` hypothesis in the local context is not found by instance synthesis here, so
`CategoryTheory.ConcreteCategory.bijective_of_isIso` cannot be used directly. Everything goes
through `Stacks.AlgebraicGeometry.RestrictUnit.apply_eq_zero_iff_of_isIso`, which takes the
`IsIso` as an explicit argument.

No `@[stacks]` attribute is attached: this is a base-change compatibility of the adjunction
unit, not a numbered result of the Stacks project.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry Stacks.AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.RestrictUnit

/-! ### Invertibility helpers -/

/-- An invertible map of abelian groups kills only zero.  The invertibility is an explicit
argument: an `IsIso` hypothesis in the local context is not found by instance synthesis at the
spellings this file produces. -/
theorem apply_eq_zero_iff_of_isIso {A B : AddCommGrpCat.{u}} (f : A ⟶ B) (hf : IsIso f) (x : A) :
    f x = 0 ↔ x = 0 := by
  have := hf
  exact ⟨fun h => (ConcreteCategory.bijective_of_isIso f).injective (h.trans (map_zero _).symm),
    fun h => by rw [h]; exact map_zero _⟩

/-- Postcomposing with an invertible map of abelian groups does not change which elements are
sent to zero. -/
private theorem comp_apply_eq_zero_iff_of_isIso {A B C : AddCommGrpCat.{u}} (g : A ⟶ B)
    (k : B ⟶ C) (hk : IsIso k) (a : A) : (g ≫ k) a = 0 ↔ g a = 0 :=
  (ConcreteCategory.comp_apply g k a ▸ apply_eq_zero_iff_of_isIso k hk (g a) :)

/-- Postcomposing with an invertible map of abelian groups does not change which elements are
sent to zero, for a composite of three maps. -/
private theorem comp_comp_apply_eq_zero_iff_of_isIso {A B C D : AddCommGrpCat.{u}} (g : A ⟶ B)
    (h : B ⟶ C) (k : C ⟶ D) (hk : IsIso k) (a : A) : (g ≫ h ≫ k) a = 0 ↔ h (g a) = 0 :=
  (ConcreteCategory.comp_apply g (h ≫ k) a ▸ ConcreteCategory.comp_apply h k (g a) ▸
    apply_eq_zero_iff_of_isIso k hk (h (g a)) :)

/-- A morphism of sheaves of modules that is invertible is invertible on sections over every
open. -/
theorem isIso_iso_hom_app {Y : Scheme.{u}} {A B : Y.Modules} (e : A ≅ B) (W : Y.Opens) :
    IsIso (e.hom.app W) :=
  ⟨e.inv.app W, by rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app],
    by rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]⟩

/-- The restriction map of a sheaf of modules between two opens that are equal is invertible:
the opens of a scheme form a thin category, so that morphism is the transport along the
equality. -/
theorem isIso_presheaf_map_of_eq {Y : Scheme.{u}} (N : Y.Modules) {A B : (Y.Opens)ᵒᵖ}
    (f : A ⟶ B) (h : A = B) : IsIso (N.presheaf.map f) := by
  subst h
  rw [show f = 𝟙 A from Subsingleton.elim _ _, N.presheaf.map_id]
  infer_instance

/-- **The unit of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` is invertible on
sections over an open inside the range of the immersion.**  On sections it is the restriction
map along `f ''ᵁ f ⁻¹ᵁ U ≤ U`, and the two opens are equal there. -/
theorem isIso_restrictAdjunction_unit_app_app {A B : Scheme.{u}} (f : A ⟶ B)
    [IsOpenImmersion f] (N : B.Modules) {U : B.Opens} (hU : U ≤ f.opensRange) :
    IsIso (((Scheme.Modules.restrictAdjunction f).unit.app N).app U) := by
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  refine isIso_presheaf_map_of_eq _ _ (congrArg op ?_)
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hU]

/-! ### The comparison -/

variable {Z X : Scheme.{u}} (i : Z ⟶ X) (V : X.Opens)

/-- **The unit `M ⟶ i_* i^* M`, read over the opens of `V`, is the unit of the base change
`i ∣_ V`.** Both sides are morphisms `M ⟶ ((i ⁻¹ᵁ V).ι ≫ i)_* N`: on the left `N` is the
restriction of `i^* M` to `i ⁻¹ᵁ V`, on the right it is the inverse image along `i ∣_ V` of the
restriction of `M` to `V`, and
`Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso` identifies the two.

The two adjunctions have the same right adjoint and `pullbackRestrictIso` is the comparison of
their left adjoints, so this is
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`. -/
theorem unit_pullbackRestrictIso (M : X.Modules) :
    (AffinePushforward.pullbackRestrictAdjunction i V).unit.app M ≫
        (Scheme.Modules.pushforward ((i ⁻¹ᵁ V).ι ≫ i)).map
          ((AffinePushforward.pullbackRestrictIso i V).hom.app M) =
      ((AffinePushforward.restrictPullbackAdjunction i V).ofNatIsoRight
        (Scheme.Modules.pushforwardCongr (morphismRestrict_ι i V))).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ M

/-- The unit of
`Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictAdjunction` on sections: the unit of
`i^* ⊣ i_*`, the unit of the restriction adjunction at `(i ⁻¹ᵁ V).ι`, and the composition law
for direct images. -/
theorem pullbackRestrictAdjunction_unit_app_app (M : X.Modules) (W : X.Opens) :
    ((AffinePushforward.pullbackRestrictAdjunction i V).unit.app M).app W =
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app W ≫
        ((Scheme.Modules.restrictAdjunction (i ⁻¹ᵁ V).ι).unit.app
          ((Scheme.Modules.pullback i).obj M)).app (i ⁻¹ᵁ W) ≫
        ((Scheme.Modules.pushforwardComp (i ⁻¹ᵁ V).ι i).hom.app
          ((Scheme.Modules.restrictFunctor (i ⁻¹ᵁ V).ι).obj
            ((Scheme.Modules.pullback i).obj M))).app W := by
  rw [AffinePushforward.pullbackRestrictAdjunction, Adjunction.ofNatIsoRight_unit]
  simp only [Adjunction.comp_unit_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app, Functor.comp_obj,
    Category.assoc]
  rfl

/-- The unit of
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPullbackAdjunction`, corrected by
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr`, on sections: restriction of the section to
`V`, the unit of `(i ∣_ V)^* ⊣ (i ∣_ V)_*`, and a transport along an equality of opens. -/
theorem restrictPullbackAdjunction_unit_app_app (M : X.Modules) (W : X.Opens) :
    (((AffinePushforward.restrictPullbackAdjunction i V).ofNatIsoRight
        (Scheme.Modules.pushforwardCongr (morphismRestrict_ι i V))).unit.app M).app W =
      ((Scheme.Modules.restrictAdjunction V.ι).unit.app M).app W ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction (i ∣_ V)).unit.app
          ((Scheme.Modules.restrictFunctor V.ι).obj M)).app (V.ι ⁻¹ᵁ W) ≫
        ((Scheme.Modules.pushforwardCongr (morphismRestrict_ι i V)).hom.app
          ((Scheme.Modules.pullback (i ∣_ V)).obj
            ((Scheme.Modules.restrictFunctor V.ι).obj M))).app W := by
  rw [AffinePushforward.restrictPullbackAdjunction, Adjunction.ofNatIsoRight_unit,
    Adjunction.ofNatIsoRight_unit]
  simp [Adjunction.comp_unit_app]

/-! ### The comparison on sections -/

/-- A local section is killed by the unit of
`Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictAdjunction` over an open `W ≤ V`
exactly when it is killed by the unit of `i^* ⊣ i_*`. -/
theorem app_pullbackRestrictAdjunction_unit_eq_zero_iff (M : X.Modules) {W : X.Opens}
    (hW : W ≤ V) (a : Γ(M, W)) :
    ((AffinePushforward.pullbackRestrictAdjunction i V).unit.app M).app W a = 0 ↔
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app W a = 0 := by
  have hη : IsIso (((Scheme.Modules.restrictAdjunction (i ⁻¹ᵁ V).ι).unit.app
      ((Scheme.Modules.pullback i).obj M)).app (i ⁻¹ᵁ W)) :=
    isIso_restrictAdjunction_unit_app_app (i ⁻¹ᵁ V).ι _
      (by rw [Scheme.Opens.opensRange_ι]; exact fun x hx => hW hx)
  have hpc : IsIso (((Scheme.Modules.pushforwardComp (i ⁻¹ᵁ V).ι i).hom.app
      ((Scheme.Modules.restrictFunctor (i ⁻¹ᵁ V).ι).obj
        ((Scheme.Modules.pullback i).obj M))).app W) :=
    isIso_iso_hom_app ((Scheme.Modules.pushforwardComp (i ⁻¹ᵁ V).ι i).app _) W
  rw [ConcreteCategory.congr_hom (pullbackRestrictAdjunction_unit_app_app i V M W) a]
  exact (comp_comp_apply_eq_zero_iff_of_isIso _ _ _ hpc a).trans
    (apply_eq_zero_iff_of_isIso _ hη _)

/-- A local section is killed by the corrected unit of
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPullbackAdjunction` exactly when its
restriction to `V` is killed by the unit of `(i ∣_ V)^* ⊣ (i ∣_ V)_*`. -/
theorem app_restrictPullbackAdjunction_unit_eq_zero_iff (M : X.Modules) (W : X.Opens)
    (a : Γ(M, W)) :
    (((AffinePushforward.restrictPullbackAdjunction i V).ofNatIsoRight
        (Scheme.Modules.pushforwardCongr (morphismRestrict_ι i V))).unit.app M).app W a = 0 ↔
      ((Scheme.Modules.pullbackPushforwardAdjunction (i ∣_ V)).unit.app
          ((Scheme.Modules.restrictFunctor V.ι).obj M)).app (V.ι ⁻¹ᵁ W)
        (((Scheme.Modules.restrictAdjunction V.ι).unit.app M).app W a) = 0 := by
  have hτ : IsIso (((Scheme.Modules.pushforwardCongr (morphismRestrict_ι i V)).hom.app
      ((Scheme.Modules.pullback (i ∣_ V)).obj
        ((Scheme.Modules.restrictFunctor V.ι).obj M))).app W) :=
    isIso_iso_hom_app ((Scheme.Modules.pushforwardCongr (morphismRestrict_ι i V)).app _) W
  rw [ConcreteCategory.congr_hom (restrictPullbackAdjunction_unit_app_app i V M W) a]
  exact comp_comp_apply_eq_zero_iff_of_isIso _ _ _ hτ a

/-- Postcomposing with the direct image of
`Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso` does not change which local
sections are killed. -/
theorem app_comp_pullbackRestrictIso_eq_zero_iff (M : X.Modules) (W : X.Opens) (a : Γ(M, W)) :
    ((AffinePushforward.pullbackRestrictAdjunction i V).unit.app M ≫
          (Scheme.Modules.pushforward ((i ⁻¹ᵁ V).ι ≫ i)).map
            ((AffinePushforward.pullbackRestrictIso i V).hom.app M)).app W a = 0 ↔
      ((AffinePushforward.pullbackRestrictAdjunction i V).unit.app M).app W a = 0 := by
  have hθ : IsIso (((Scheme.Modules.pushforward ((i ⁻¹ᵁ V).ι ≫ i)).map
      ((AffinePushforward.pullbackRestrictIso i V).hom.app M)).app W) :=
    isIso_iso_hom_app ((Scheme.Modules.pushforward ((i ⁻¹ᵁ V).ι ≫ i)).mapIso
      ((AffinePushforward.pullbackRestrictIso i V).app M)) W
  rw [ConcreteCategory.congr_hom (Scheme.Modules.Hom.comp_app _ _ (U := W)) a]
  exact comp_apply_eq_zero_iff_of_isIso _ _ hθ a

/-- **The vanishing comparison: a local section of `M` over an open `W ≤ V` restricts to zero on
`Z` exactly when its restriction to `V` restricts to zero on `i ⁻¹ᵁ V`.**

This is `Stacks.AlgebraicGeometry.RestrictUnit.unit_pullbackRestrictIso` read on sections over
`W`, the four factors separating the two units from the two statements being invertible. -/
theorem app_unit_eq_zero_iff (M : X.Modules) {W : X.Opens} (hW : W ≤ V) (a : Γ(M, W)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (i ∣_ V)).unit.app
          ((Scheme.Modules.restrictFunctor V.ι).obj M)).app (V.ι ⁻¹ᵁ W)
        (((Scheme.Modules.restrictAdjunction V.ι).unit.app M).app W a) = 0 ↔
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app W a = 0 := by
  rw [← app_restrictPullbackAdjunction_unit_eq_zero_iff i V M W a,
    ← unit_pullbackRestrictIso i V M, app_comp_pullbackRestrictIso_eq_zero_iff i V M W a,
    app_pullbackRestrictAdjunction_unit_eq_zero_iff i V M hW a]

end Stacks.AlgebraicGeometry.RestrictUnit

end
