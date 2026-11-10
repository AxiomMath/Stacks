module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent

/-!
# Effective descent of a morphism property along a surjective étale chart

Let `P` be a property of morphisms of schemes and let `f : X ⟶ Y` be a morphism of
presheaves on the big fppf site of a scheme `S`, with `X` a sheaf and `Y` an algebraic
space. If some surjective étale chart `yoneda.obj U ⟶ Y` of the target makes the base change
of `f` a scheme morphism with `P`, and morphisms with `P` descend effectively along
surjective étale morphisms of the site, then `X` is an algebraic space and `f` is
representable with `P` (Stacks 03I2).

## Main definitions

* `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`: morphisms with property
  `P` descend effectively along surjective étale morphisms of the big fppf site of `S`.

## Main results

* `AlgebraicGeometry.Space.presheaf_of_surjectiveEtaleChart`: a morphism from a sheaf to a
  sheaf which becomes representable with `P` over one surjective étale chart of its target is
  representable with `P`.
* `AlgebraicGeometry.Space.relativelyRepresentable_diag_of_diagonal`: the absolute diagonal
  of the source is representable when the relative diagonal of the morphism is.
* `AlgebraicGeometry.IsAlgebraicSpace.of_relativelyRepresentable` (Stacks 02WY): a sheaf
  carrying a representable morphism to an algebraic space is an algebraic space.
* `CategoryTheory.Functor.relativelyRepresentable.mono_of_mono_snd` and
  `AlgebraicGeometry.Space.mono_of_presheaf`: a representable morphism of presheaves all of
  whose represented base changes are monomorphisms is a monomorphism.
* `AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent`:
  Stacks 03I2 under effective descent for `P`: the source is an algebraic space and the
  morphism is representable with `P`.

## References

* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 02W2](https://stacks.math.columbia.edu/tag/02W2)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02WY](https://stacks.math.columbia.edu/tag/02WY)
* [Stacks Project, Tag 05L9](https://stacks.math.columbia.edu/tag/05L9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Functor.relativelyRepresentable

/-- A representable morphism of presheaves whose chosen represented base changes are all
monomorphisms is a monomorphism. -/
theorem mono_of_mono_snd {C : Type u} [Category.{v} C] {X Y : Cᵒᵖ ⥤ Type v} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (hm : ∀ ⦃a : C⦄ (g : yoneda.obj a ⟶ Y), Mono (hf.snd g)) : Mono f := by
  refine (NatTrans.mono_iff_mono_app _).2 fun b ↦ (mono_iff_injective _).2 fun x y hxy ↦ ?_
  have key : ∀ x' y' : yoneda.obj b.unop ⟶ X, x' ≫ f = y' ≫ f → x' = y' := by
    intro x' y' h
    have h₁ : y' ≫ f = yoneda.map (𝟙 b.unop) ≫ x' ≫ f := by simp [h]
    have h₂ : x' ≫ f = yoneda.map (𝟙 b.unop) ≫ x' ≫ f := by simp
    have := (hm (x' ≫ f)).right_cancellation
      (hf.lift x' (𝟙 b.unop) h₂) (hf.lift y' (𝟙 b.unop) h₁) (by simp)
    calc x' = yoneda.map (hf.lift x' (𝟙 b.unop) h₂) ≫ hf.fst (x' ≫ f) := by simp
      _ = yoneda.map (hf.lift y' (𝟙 b.unop) h₁) ≫ hf.fst (x' ≫ f) := by rw [this]
      _ = y' := by simp
  refine yonedaEquiv.symm.injective (key _ _ ?_)
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp]
  simpa using hxy

end CategoryTheory.Functor.relativelyRepresentable

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u})

/-- Morphisms with property `P` *descend effectively along surjective étale morphisms* of the
big fppf site of `S`: let `f : X ⟶ Y` be a morphism of sheaves, `h : yoneda.obj a ⟶ Y` a
morphism from a representable presheaf, and `q : c ⟶ a` a morphism of the site whose
underlying morphism of schemes is surjective and étale. If the base change of `f` along
`yoneda.map q ≫ h` is representable with `P`, then so is the base change of `f` along `h`. -/
def IsEffectiveDescentAlongSurjectiveEtale : Prop :=
  ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
    ∀ ⦃a c : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (q : c ⟶ a),
      Surjective ((BigFppfOver.toScheme B S hS).map q) →
      Etale ((BigFppfOver.toScheme B S hS).map q) →
      ∀ ⦃A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (m : A ⟶ X) (r : A ⟶ yoneda.obj c),
        IsPullback m r f (yoneda.map q ≫ h) →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h)

variable {B S hS P}

/-- A morphism from a sheaf to a sheaf on the big fppf site of `S` whose base change along one
surjective étale chart of its target is representable with `P` is representable with `P`,
provided morphisms with `P` descend effectively along surjective étale morphisms. -/
theorem presheaf_of_surjectiveEtaleChart [P.RespectsIso]
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS P)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hYs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y) {f : X ⟶ Y}
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ Y}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hV : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f := by
  have : MorphismProperty.RespectsIso (P.inverseImage (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine (MorphismProperty.presheaf_iff_forall_presheaf_pullback_snd _ f).2 fun a h ↦ ?_
  obtain ⟨c, q, A, m, r, hqs, hqe, sq, hr⟩ :=
    exists_etale_isPullback_presheaf_of_chart B S hS P hs he hV a h
  exact hdesc f hX hYs h q hqs hqe m r sq hr

/-- A representable morphism of presheaves on the big fppf site of `S` all of whose
represented base changes have a property contained in the monomorphisms is a monomorphism. -/
theorem mono_of_presheaf {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hP : P ≤ MorphismProperty.monomorphisms Scheme.{u})
    (hf : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f) : Mono f :=
  hf.rep.mono_of_mono_snd fun _ g ↦
    (BigFppfOver.toScheme B S hS).mono_of_mono_map (hP _ (hf.property_snd g))

section Diagonal

/-- The comparison of the fibre product of a morphism to the terminal object with itself and
the product is an isomorphism. -/
private theorem isIso_prodLift_pullback_terminal {C : Type*} [Category C] [HasTerminal C]
    [HasBinaryProducts C] {Z : C} (k : Z ⟶ ⊤_ C) [HasPullback k k] :
    IsIso (prod.lift (pullback.fst k k) (pullback.snd k k)) := by
  refine ⟨pullback.lift prod.fst prod.snd (Subsingleton.elim _ _), ?_, ?_⟩
  · apply pullback.hom_ext <;> simp
  · apply prod.hom_ext <;> simp

/-- The absolute diagonal of the source of a morphism into an algebraic space over `S` is
representable as soon as the relative diagonal of the morphism is. -/
theorem relativelyRepresentable_diag_of_diagonal
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hd : yoneda.relativelyRepresentable (pullback.diagonal f)) :
    yoneda.relativelyRepresentable (diag X) := by
  set t : Y ⟶ ⊤_ _ := terminal.from Y
  have he : IsIso (prod.lift (pullback.fst (f ≫ t) (f ≫ t))
      (pullback.snd (f ≫ t) (f ≫ t))) := isIso_prodLift_pullback_terminal (f ≫ t)
  have key : diag X = pullback.diagonal f ≫ pullback.mapDesc f f t ≫
      prod.lift (pullback.fst (f ≫ t) (f ≫ t)) (pullback.snd (f ≫ t) (f ≫ t)) := by
    apply prod.hom_ext <;> simp
  exact key ▸ MorphismProperty.comp_mem _ _ _ hd
    (MorphismProperty.comp_mem _ _ _
      (relativelyRepresentable_mapDesc B S hS f f t hY)
      (Functor.relativelyRepresentable.of_isIso _ _))

end Diagonal

end Space

/-- **Stacks 02WY**: a sheaf on the big fppf site of `S` admitting a representable morphism to
an algebraic space over `S` is an algebraic space over `S`. -/
theorem IsAlgebraicSpace.of_relativelyRepresentable {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    IsAlgebraicSpace B S hS X where
  isSheaf := hX
  diagonal_representable := Space.relativelyRepresentable_diag_of_diagonal hY
    (Space.relativelyRepresentable_diagonal_of_representable B S hS f hf)
  exists_atlas := by
    have h₁ := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))
    have h₂ := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))
    obtain ⟨U, g, hs, he⟩ := hY.exists_atlas
    exact ⟨hf.pullback g, hf.fst g,
      MorphismProperty.of_isPullback (hf.isPullback g).flip hs,
      MorphismProperty.of_isPullback (hf.isPullback g).flip he⟩

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {P : MorphismProperty Scheme.{u}}

/-- **Stacks 03I2** under effective descent for `P` along surjective étale morphisms of the
site. Let `f : X ⟶ Y` be a morphism of presheaves on the big fppf site of `S` with `X` a sheaf
and `Y` an algebraic space over `S`. If some surjective étale chart `g` of `Y` makes the base
change of `f` representable with `P`, then `X` is an algebraic space over `S` and `f` is
representable with `P`. -/
theorem isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent [P.RespectsIso]
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS P)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ Y}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hV : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g)) :
    IsAlgebraicSpace B S hS X ∧
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f :=
  have hfP := presheaf_of_surjectiveEtaleChart hdesc hX hY.isSheaf hs he hV
  ⟨IsAlgebraicSpace.of_relativelyRepresentable hX hY hfP.rep, hfP⟩

end Space

end AlgebraicGeometry

end
