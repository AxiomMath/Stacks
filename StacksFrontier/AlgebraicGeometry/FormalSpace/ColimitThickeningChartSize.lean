module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceSize
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitThickeningCharts
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SchemeSizeBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds

/-!
# The size of the base changes of a transported chart

Let `E : Λ ⥤ FppfSheaf B S hS` be a diagram of algebraic spaces over `S` indexed by a preorder
with least element `o`, whose transition morphisms are representable thickenings, and let
`u₀ : h_{U₀} ⟶ E o` be étale, representably by schemes. The transported charts
`AlgebraicGeometry.FormalSpace.thickeningChart` are étale over the stages, so the base change of
the `j`-th one along a point `ξ : h_X ⟶ E j` is represented by an object `W` of the site étale
over `X`. This file proves the bound `size W ≤ 2 ^ 2 ^ max (size U₀) (size X)`, uniform in the
stage `j`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isPullback_thickeningChartπ_app_size_le`: the base change
  of a transported chart along any point `h_X ⟶ E j` is represented by an object of the site
  étale over `X` of size at most `2 ^ 2 ^ max (size U₀) (size X)`.
* `AlgebraicGeometry.FormalSpace.monotone_two_pow_two_pow_max` and
  `AlgebraicGeometry.FormalSpace.two_pow_two_pow_max_lt_cutoff`: that bound is monotone in
  `size X` and sends cardinals below the cutoff of the site below the cutoff.

## References

* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The function `s ↦ 2 ^ 2 ^ max κ s` on cardinals is monotone. -/
theorem monotone_two_pow_two_pow_max (κ : Cardinal.{u}) :
    Monotone fun s : Cardinal.{u} ↦ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ max κ s :=
  fun _ _ h ↦ power_le_power_left two_ne_zero
    (power_le_power_left two_ne_zero (max_le_max le_rfl h))

/-- For `κ` below the cutoff of the site, `s ↦ 2 ^ 2 ^ max κ s` sends cardinals below the cutoff
to cardinals below the cutoff. -/
theorem two_pow_two_pow_max_lt_cutoff {κ : Cardinal.{u}} (hκ : κ < B.cutoff) :
    ∀ s < B.cutoff, (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ max κ s < B.cutoff :=
  fun _ hs ↦ B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit (max_lt hκ hs))

variable {Λ : Type*} [Preorder Λ] (E : Λ ⥤ FppfSheaf B S hS)
  (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
    Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
  (o : Λ) (ho : ∀ j, o ≤ j)

/-- Let `E` be a diagram of
algebraic spaces with least index `o` whose transitions are representable thickenings, and
`u₀ : h_{U₀} ⟶ E o` étale, representably by schemes. Then the base change of the transported
chart `thickeningChart … j ⟶ E j` along any point `ξ : h_X ⟶ E j` is represented by an object
`W` of the site, étale over `X`, with `size W ≤ 2 ^ 2 ^ max (size U₀) (size X)`. -/
theorem exists_isPullback_thickeningChartπ_app_size_le
    (halg : ∀ i, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj)
    {U₀ : BigFppfOver B S hS} (u₀ : uliftYoneda.{u + 1}.obj U₀ ⟶ (E.obj o).obj)
    (hu₀ : Space.HasSchemePropertyULift.{u + 1} B S hS (@Etale) u₀) (j : Λ)
    (X : BigFppfOver B S hS)
    (ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj X ⟶ E.obj j) :
    ∃ (W : BigFppfOver B S hS) (pr : W ⟶ X)
      (c : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶
        (thickeningChart B S hS E hthick o ho u₀ halg hu₀).obj j),
      IsPullback c ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map pr)
        ((thickeningChartπ B S hS E hthick o ho u₀ halg hu₀).app j) ξ ∧
      Etale ((BigFppfOver.toScheme B S hS).map pr) ∧
      ((BigFppfOver.toScheme B S hS).obj W).size ≤
        (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
          max ((BigFppfOver.toScheme B S hS).obj U₀).size
            ((BigFppfOver.toScheme B S hS).obj X).size := by
  classical
  have _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  have := mono_map_hom_of_isRepresentableThickeningULift B S hS E hthick (homOfLE (ho j))
  have hπ := hasSchemePropertyULift_etale_thickeningChartπ_app B S hS E hthick o ho u₀
    halg hu₀ j
  have hi : Space.IsRepresentableThickeningULift.{u + 1} B S hS
      (E.map (homOfLE (ho j))).hom := hthick _
  obtain ⟨W, pr, c₀, hpb, hpr_et⟩ : ∃ (W : BigFppfOver B S hS) (pr : W ⟶ X)
      (c₀ : uliftYoneda.{u + 1}.obj W ⟶
        ((thickeningChart B S hS E hthick o ho u₀ halg hu₀).obj j).obj),
      IsPullback c₀ (uliftYoneda.{u + 1}.map pr)
        ((thickeningChartπ B S hS E hthick o ho u₀ halg hu₀).app j).hom ξ.hom ∧
      Etale ((BigFppfOver.toScheme B S hS).map pr) :=
    ⟨_, _, _, hπ.rep.isPullback ξ.hom, hπ.property_snd ξ.hom⟩
  obtain ⟨W₀, b, e₀, hpb₀, hb⟩ : ∃ (W₀ : BigFppfOver B S hS) (b : W₀ ⟶ W)
      (e₀ : uliftYoneda.{u + 1}.obj W₀ ⟶ (E.obj o).obj),
      IsPullback e₀ (uliftYoneda.{u + 1}.map b) (E.map (homOfLE (ho j))).hom
        (c₀ ≫ ((thickeningChartπ B S hS E hthick o ho u₀ halg hu₀).app j).hom) ∧
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map b) :=
    ⟨_, _, _, hi.rep.isPullback _, hi.property_snd _⟩
  obtain ⟨ν, hunit⟩ : ∃ ν : uliftYoneda.{u + 1}.obj U₀ ⟶
      ((thickeningChart B S hS E hthick o ho u₀ halg hu₀).obj j).obj,
      IsPullback ν u₀ ((thickeningChartπ B S hS E hthick o ho u₀ halg hu₀).app j).hom
        (E.map (homOfLE (ho j))).hom :=
    have := mono_comp_sheafToPresheaf_map B S hS E hthick (homOfLE (ho j))
    ⟨_, isPullback_monoPushforward_unit _ u₀⟩
  have hw : (uliftYoneda.{u + 1}.map b ≫ c₀) ≫
      ((thickeningChartπ B S hS E hthick o ho u₀ halg hu₀).app j).hom =
        e₀ ≫ (E.map (homOfLE (ho j))).hom := by
    rw [Category.assoc]
    exact hpb₀.w.symm
  obtain ⟨p₁, hp₁unit, hp₁u⟩ : ∃ p₁ : W₀ ⟶ U₀,
      uliftYoneda.{u + 1}.map p₁ ≫ ν = uliftYoneda.{u + 1}.map b ≫ c₀ ∧
      uliftYoneda.{u + 1}.map p₁ ≫ u₀ = e₀ :=
    ⟨uliftYoneda.{u + 1}.preimage (hunit.lift _ _ hw),
      by rw [Functor.map_preimage]; exact hunit.lift_fst _ _ _,
      by rw [Functor.map_preimage]; exact hunit.lift_snd _ _ _⟩
  let m : W₀ ⟶ pullback (terminal.from U₀) (terminal.from X) :=
    pullback.lift p₁ (b ≫ pr) (terminal.hom_ext _ _)
  have hmono : Mono m := by
    refine ⟨fun {Z} a a' h ↦ ?_⟩
    have h₁ : a ≫ p₁ = a' ≫ p₁ := by
      have := h =≫ pullback.fst (terminal.from U₀) (terminal.from X)
      simpa only [m, Category.assoc, pullback.lift_fst] using this
    have h₂ : a ≫ b ≫ pr = a' ≫ b ≫ pr := by
      have := h =≫ pullback.snd (terminal.from U₀) (terminal.from X)
      simpa only [m, Category.assoc, pullback.lift_snd] using this
    have key : ∀ x : Z ⟶ W₀, uliftYoneda.{u + 1}.map (x ≫ b) ≫ c₀ =
        uliftYoneda.{u + 1}.map (x ≫ p₁) ≫ ν := fun x ↦ by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hp₁unit]
    have hsnd : a ≫ b = a' ≫ b := by
      refine uliftYoneda.{u + 1}.map_injective (hpb.hom_ext ?_ ?_)
      · rw [key, key, h₁]
      · rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, Category.assoc, h₂]
    refine uliftYoneda.{u + 1}.map_injective (hpb₀.hom_ext ?_ ?_)
    · rw [← hp₁u, ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
        h₁]
    · rw [← Functor.map_comp, ← Functor.map_comp, hsnd]
  have : Mono ((BigFppfOver.toScheme B S hS).map m) :=
    CategoryTheory.preserves_mono_of_preservesLimit (BigFppfOver.toScheme B S hS) m
  have hW₀size : ((BigFppfOver.toScheme B S hS).obj W₀).size ≤
      (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
        max ((BigFppfOver.toScheme B S hS).obj U₀).size
          ((BigFppfOver.toScheme B S hS).obj X).size :=
    (size_le_of_mono_double_power ((BigFppfOver.toScheme B S hS).map m)).trans
      (power_le_power_left two_ne_zero (power_le_power_left two_ne_zero
        (Space.size_pullback_le B S hS (terminal.from U₀) (terminal.from X))))
  have hθ : IsHomeomorph ((hb.isHomeomorph).homeomorph _).symm :=
    ((hb.isHomeomorph).homeomorph _).symm.isHomeomorph
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map pr) := inferInstance
  have hWsize := Scheme.size_le_max_of_locallyOfFiniteType_of_isHomeomorph
    ((BigFppfOver.toScheme B S hS).map pr) _ hθ
  refine ⟨W, pr, ObjectProperty.homMk c₀, ?_, hpr_et, hWsize.trans (max_le hW₀size ?_)⟩
  · exact IsPullback.of_map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
      (ObjectProperty.hom_ext _ hpb.w) hpb
  · exact (le_max_right _ _).trans
      ((cantor _).le.trans (power_le_power_left two_ne_zero (cantor _).le))

end AlgebraicGeometry.FormalSpace

end
