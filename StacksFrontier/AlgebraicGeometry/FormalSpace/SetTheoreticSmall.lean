module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStackSmall

/-!
# A sheaf satisfying the set-theoretic condition is small

Let `S` be a scheme contained in a big fppf site `B`. The sheaves carrying formal algebraic
spaces over `S` take values in `Type (u + 1)`, one universe above the universe of the schemes,
because they are colimits of representables. The set-theoretic condition of Stacks 0AIS says
that such a sheaf is a coequalizer of two maps between representables, and that forces its
sections to be *small*: a section is determined by the object of a small model of the site on
which it lifts along the given surjection together with the lift. Consequently such a sheaf is
the universe lift of a sheaf with values in the universe of the schemes.

## Main results

* `AlgebraicGeometry.FormalSpace.small_sections_of_locallySurjective`: a sheaf admitting a
  locally surjective morphism from a pointwise `u`-small presheaf on an essentially small site
  has pointwise `u`-small sections.
* `AlgebraicGeometry.FormalSpace.small_of_satisfiesSetTheoreticCondition`: a sheaf satisfying
  the set-theoretic condition of **Stacks 0AIS** has pointwise `u`-small sections.
* `AlgebraicGeometry.FormalSpace.small_of_isFormalAlgebraicSpace`,
  `AlgebraicGeometry.FormalSpace.small_of_isAffineFormalAlgebraicSpace`: the same for a formal
  algebraic space and for an affine formal algebraic space, both of which satisfy that
  condition by definition.
* `AlgebraicGeometry.FormalSpace.exists_comp_uliftFunctor_iso_of_small`: an fppf sheaf with
  pointwise `u`-small sections is the universe lift of a sheaf of `Type u`.
* `AlgebraicGeometry.FormalSpace.exists_comp_uliftFunctor_iso_of_satisfiesSetTheoreticCondition`:
  such a sheaf is the universe lift of a sheaf of `Type u`.

## References

* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-- A sheaf admitting a locally surjective morphism from a pointwise small presheaf on an
essentially small site has pointwise small sections. -/
lemma small_sections_of_locallySurjective
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u} C]
    (J : GrothendieckTopology C) {F H : Cᵒᵖ ⥤ Type (u + 1)}
    (hF : Presheaf.IsSheaf J F) (a : H ⟶ F)
    [Presheaf.IsLocallySurjective J a] [FunctorToTypes.Small.{u} H]
    (T : C) : Small.{u} (F.obj (Opposite.op T)) := by
  classical
  let E := equivSmallModel.{u} C
  let encode : F.obj (Opposite.op T) →
      (V : SmallModel.{u} C) → (E.inverse.obj V ⟶ T) →
        Shrink.{u} (H.obj (Opposite.op (E.inverse.obj V))) → Prop :=
    fun x V g t ↦ a.app _ ((equivShrink.{u} _).symm t) = F.map g.op x
  apply small_of_injective (f := encode)
  intro x y h
  apply hF.isSeparated _ _ (Presheaf.imageSieve_mem J a x) x y
  intro V g hg
  obtain ⟨t, ht⟩ := hg
  let e := E.unitIso.app V
  let t' := (equivShrink.{u} _) (H.map e.inv.op t)
  have hx : encode x (E.functor.obj V) (e.inv ≫ g) t' := by
    dsimp [encode, t']
    rw [Equiv.symm_apply_apply, a.naturality_apply, ht, F.map_comp]
    rfl
  have hy : encode y (E.functor.obj V) (e.inv ≫ g) t' := by rwa [← h]
  exact (CategoryTheory.injective_of_mono (F.map e.inv.op))
    (by simpa only [encode, op_comp, F.map_comp, types_comp_apply] using hx.symm.trans hy)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An fppf sheaf on the big fppf site of `S` which satisfies the set-theoretic condition of
[Stacks, Tag 0AIS] has pointwise `u`-small sections, `u` being the universe of the schemes. -/
theorem small_of_satisfiesSetTheoreticCondition {X : FppfSheaf B S hS}
    (hX : SatisfiesSetTheoreticCondition B S hS X) : FunctorToTypes.Small.{u} X.obj := by
  classical
  obtain ⟨U, R, hU, hR, ⟨eU⟩, -, a, ha, -⟩ := hX
  have _ : EssentiallySmall.{u} (BigFppfOver B S hS) := essentiallySmall_bigFppfOver B S hS
  have _ : FunctorToTypes.Small.{u} hU.obj := fun T ↦ by
    have _ : Small.{u} (((uliftYoneda.{u + 1}).obj U).obj T) :=
      inferInstanceAs (Small.{u} (ULift.{u + 1} (T.unop ⟶ U)))
    exact small_of_injective (CategoryTheory.injective_of_mono (eU.hom.app T))
  have _ : Sheaf.IsLocallySurjective a := (Sheaf.isLocallySurjective_iff_epi a).mpr ha
  intro T
  exact small_sections_of_locallySurjective _ X.property a.hom T.unop

/-- A formal algebraic space over `S` has pointwise `u`-small sections. -/
theorem small_of_isFormalAlgebraicSpace {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) : FunctorToTypes.Small.{u} X.obj :=
  small_of_satisfiesSetTheoreticCondition B S hS hX.1

/-- An affine formal algebraic space over `S` has pointwise `u`-small sections. -/
theorem small_of_isAffineFormalAlgebraicSpace {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) : FunctorToTypes.Small.{u} X.obj :=
  small_of_satisfiesSetTheoreticCondition B S hS hX.1

/-- An fppf sheaf with pointwise `u`-small sections is the universe lift of a sheaf with
values in the universe of the schemes. -/
theorem exists_comp_uliftFunctor_iso_of_small {X : FppfSheaf B S hS}
    (hX : FunctorToTypes.Small.{u} X.obj) :
    ∃ X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u,
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X' ∧
        Nonempty (X' ⋙ uliftFunctor.{u + 1} ≅ X.obj) := by
  have _ := hX
  let hiso : FunctorToTypes.shrink.{u} X.obj ⋙ uliftFunctor.{u + 1} ≅ X.obj :=
    Space.shrinkCompUliftFunctorIso _
  refine ⟨FunctorToTypes.shrink.{u} X.obj, ?_, ⟨hiso⟩⟩
  have h1 : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (FunctorToTypes.shrink.{u} X.obj ⋙ uliftFunctor.{u + 1}) :=
    (Presheaf.isSheaf_of_iso_iff hiso).mpr X.property
  rw [isSheaf_iff_isSheaf_of_type] at h1 ⊢
  rwa [Presieve.isSheaf_comp_uliftFunctor_iff] at h1

/-- A sheaf satisfying the set-theoretic condition is the universe lift of a sheaf with values
in the universe of the schemes. -/
theorem exists_comp_uliftFunctor_iso_of_satisfiesSetTheoreticCondition
    {X : FppfSheaf B S hS} (hX : SatisfiesSetTheoreticCondition B S hS X) :
    ∃ X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u,
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X' ∧
        Nonempty (X' ⋙ uliftFunctor.{u + 1} ≅ X.obj) :=
  exists_comp_uliftFunctor_iso_of_small B S hS
    (small_of_satisfiesSetTheoreticCondition B S hS hX)

end AlgebraicGeometry.FormalSpace

end
