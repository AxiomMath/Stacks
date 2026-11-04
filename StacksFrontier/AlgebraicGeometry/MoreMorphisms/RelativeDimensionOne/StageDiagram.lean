module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeDimensionOne.LimitStages
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.SmoothStratification
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.ModuleSupport
import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.EventualFibreDimension

/-!
# Descending a diagram of smooth curves to a stage of a limit

Let `S = lim Sᵢ` be a cofiltered limit of affine schemes with affine transition morphisms, and let
`X₀` be of finite presentation over a stage `S₀`. Suppose that over `S` the base change `X` of
`X₀` carries the diagram produced over a field by [Stacks, Tag 0GK5]: a finite étale `T ⟶ S`,
a smooth proper `Ȳ ⟶ T` with geometrically connected fibres of dimension at most one, an open
`Y ⊆ Ȳ`, a finite surjective `ν : Y ⟶ X`, and an open `W ⊆ X` over which `ν` is a closed
immersion, with `ν⁻¹(W)` surjecting onto `T`. Then the whole diagram, with all these
properties, already exists over some stage `Sᵢ` for the base change of `X₀` to `Sᵢ`.

This is the descent step "we can descend the diagram above to a corresponding diagram over
`Spec(A_a)`" in the proof of [Stacks, Tag 0GK7].

## Main results

* `AlgebraicGeometry.exists_stage_curveDiagram`: the descent of the diagram.

## Implementation notes

All objects are objects of over categories and all base changes are `CategoryTheory.Over.pullback`.
The objects are first modelled at one stage ([Stacks, Tag 01ZM] (1)), the morphisms at later
stages in the canonical form `AlgebraicGeometry.LimitStages.exists_hom_limitIso`
([Stacks, Tag 01ZM] (2)), and every property is then pushed to a common stage. The open `W` is
carried as an open immersion `w : W ⟶ X`, and the condition that `ν` be a closed immersion over
`W` as the condition that the base change of `ν` along `w` be one; both are conditions on
morphisms between objects of finite presentation and descend as such. Geometric connectedness
and the dimension of the fibres descend by `AlgebraicGeometry.LimitStages`, the target of the
smooth proper morphism being affine once the finite morphism to the base has been descended.

## References

* [Stacks Project, Tag 0GK7](https://stacks.math.columbia.edu/tag/0GK7)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

open LimitStages

section Helpers

variable {S : Scheme.{u}}

/-- A bound on the dimension of all fibres passes from a morphism locally of finite type to any
base change of it. -/
theorem forall_topologicalKrullDim_fiber_le_of_isPullback {X' Y' X Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (h : IsPullback g' f' f g)
    [LocallyOfFiniteType f] {d : WithBot ℕ∞} (hd : ∀ s, topologicalKrullDim (f.fiber s) ≤ d)
    (s : Y') : topologicalKrullDim (f'.fiber s) ≤ d :=
  EventualFibreDimension.fiber_dimension_le_of_isPullback g' f' f g h d hd s

/-- A bound on the dimension of all fibres passes along a commutative square of over objects
whose horizontal sides are isomorphisms. -/
theorem forall_topologicalKrullDim_fiber_le_of_comm {A A' B B' : Over S} (α : A ≅ A')
    (β : B ≅ B') (m : A' ⟶ B') (n : A ⟶ B) (h : α.hom ≫ m = n ≫ β.hom)
    [LocallyOfFiniteType m.left] {d : WithBot ℕ∞}
    (hd : ∀ s, topologicalKrullDim (m.left.fiber s) ≤ d) (s : B.left) :
    topologicalKrullDim (n.left.fiber s) ≤ d := by
  have : IsIso α.hom.left := (Over.forget S).map_isIso α.hom
  have : IsIso β.hom.left := (Over.forget S).map_isIso β.hom
  have hsq : IsPullback α.hom.left n.left m.left β.hom.left :=
    IsPullback.of_horiz_isIso ⟨by rw [← Over.comp_left, h, Over.comp_left]⟩
  exact forall_topologicalKrullDim_fiber_le_of_isPullback hsq hd s

/-- A morphism of over objects whose source is of finite presentation and whose target is
quasi-separated and locally of finite type is of finite presentation. -/
theorem finitePresentation_left {A B : Over S} (f : A ⟶ B) (hA : FinitePresentation A.hom)
    [QuasiSeparated B.hom] [LocallyOfFiniteType B.hom] : FinitePresentation f.left :=
  finitePresentation_of_comp f.left B.hom (by rw [Over.w]; exact hA)

/-- **Base change along an open immersion and restriction.** Given a pullback square of `f`
along an open immersion `w`, a property respecting isomorphisms holds for the projection to the
source of `w` exactly when it holds for the restriction of `f` over the image of `w`. -/
theorem prop_snd_iff_morphismRestrict (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {Pb Y X W : Scheme.{u}} {a : Pb ⟶ Y} {b : Pb ⟶ W} {f : Y ⟶ X} {w : W ⟶ X}
    [IsOpenImmersion w] (h : IsPullback a b f w) : P b ↔ P (f ∣_ w.opensRange) := by
  have h' : IsPullback a (b ≫ w.isoOpensRange.hom) f w.opensRange.ι :=
    IsPullback.of_iso h (Iso.refl _) (Iso.refl _) w.isoOpensRange (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp [Scheme.Hom.isoOpensRange_hom_ι])
  have hr := (isPullback_morphismRestrict f w.opensRange).flip
  rw [← MorphismProperty.cancel_right_of_respectsIso P b w.isoOpensRange.hom,
    ← h'.isoIsPullback_hom_snd _ _ hr, MorphismProperty.cancel_left_of_respectsIso P]

/-- A bound on the dimension of all fibres passes to a morphism of over objects conjugated by
isomorphisms. -/
theorem forall_topologicalKrullDim_fiber_le_conj {A A' B B' : Over S} (eA : A' ≅ A) (f : A ⟶ B)
    (eB : B ≅ B') [LocallyOfFiniteType f.left] {d : WithBot ℕ∞}
    (hd : ∀ s, topologicalKrullDim (f.left.fiber s) ≤ d) (s : B'.left) :
    topologicalKrullDim ((eA.hom ≫ f ≫ eB.hom).left.fiber s) ≤ d :=
  forall_topologicalKrullDim_fiber_le_of_comm eA eB.symm f _ (by simp) hd s

/-- A commutative square between a morphism of base changes and a conjugate of a morphism by
isomorphisms gives a commutative square with the composite isomorphisms. -/
theorem comm_trans_symm {A A' A'' B B' B'' : Over S} (lA : A ≅ A') (eA : A'' ≅ A')
    (lB : B ≅ B') (eB : B'' ≅ B') (f : A'' ⟶ B'') (n : A ⟶ B)
    (h : lA.hom ≫ (eA.inv ≫ f ≫ eB.hom) = n ≫ lB.hom) :
    (lA ≪≫ eA.symm).hom ≫ f = n ≫ (lB ≪≫ eB.symm).hom := by
  rw [← cancel_mono eB.hom]
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    using h

/-- An object of finite presentation over a quasi-compact quasi-separated scheme has quasi-compact
quasi-separated source. -/
theorem compactSpace_left_of_finitePresentation [CompactSpace S] [QuasiSeparatedSpace S]
    (A : Over S) (hA : FinitePresentation A.hom) :
    CompactSpace A.left ∧ QuasiSeparatedSpace A.left := by
  have := hA.2.1
  have := hA.2.2
  exact ⟨QuasiCompact.compactSpace_of_compactSpace A.hom,
    quasiSeparatedSpace_of_quasiSeparated A.hom⟩

/-- Composing the cospan of a pullback with an isomorphism of the base keeps it a pullback. -/
theorem isPullback_pullback_comp_iso {Y W X X' : Scheme.{u}} (f : Y ⟶ X) (g : W ⟶ X)
    (e : X ≅ X') : IsPullback (pullback.fst f g) (pullback.snd f g) (f ≫ e.hom) (g ≫ e.hom) :=
  IsPullback.of_iso (IsPullback.of_hasPullback f g) (Iso.refl _) (Iso.refl _) (Iso.refl _) e
    (by simp) (by simp) (by simp) (by simp)

end Helpers

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, IsAffine (D.obj i)]

/-- **Descent of a smooth proper morphism from the limit to a stage.** A smooth proper morphism
between the base changes to the limit of two schemes of finite presentation over a stage `k` is,
over a later stage `j`, the base change of a morphism `G` in canonical form, and the base change
of `G` to every sufficiently late stage is smooth and proper.

A further condition `P` holds there as well as soon as it holds at all sufficiently late stages
for every such model `G` (hypothesis `hP`). -/
theorem exists_stage_smooth_proper (hc : IsLimit c) (k : I) (A B : Over (D.obj k))
    (hA : FinitePresentation A.hom) (hB : FinitePresentation B.hom)
    (m : (Over.pullback (c.π.app k)).obj A ⟶ (Over.pullback (c.π.app k)).obj B)
    (hs : Smooth m.left) (hp : IsProper m.left) (P : MorphismProperty Scheme.{u})
    (hP : ∀ (j : I) (e : j ⟶ k)
      (G : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj B),
      (limitIso D c e A).hom ≫ m = (Over.pullback (c.π.app j)).map G ≫ (limitIso D c e B).hom →
      ∃ (j' : I) (g' : j' ⟶ j), ∀ (k' : I) (g'' : k' ⟶ j'),
        P ((Over.pullback (D.map (g'' ≫ g'))).map G).left) :
    ∃ (j : I) (e : j ⟶ k)
      (G : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj B),
      (limitIso D c e A).hom ≫ m = (Over.pullback (c.π.app j)).map G ≫ (limitIso D c e B).hom ∧
      ∃ (j' : I) (g' : j' ⟶ j), ∀ (k' : I) (g'' : k' ⟶ j'),
        Smooth ((Over.pullback (D.map (g'' ≫ g'))).map G).left ∧
        IsProper ((Over.pullback (D.map (g'' ≫ g'))).map G).left ∧
        P ((Over.pullback (D.map (g'' ≫ g'))).map G).left := by
  have : QuasiSeparated B.hom := hB.2.2
  have : LocallyOfFiniteType B.hom := by have := hB.1; infer_instance
  obtain ⟨j, e, G, hG⟩ := exists_hom_limitIso D c hc k A B hA hB m
  refine ⟨j, e, G, hG, ?_⟩
  have hsmRI : MorphismProperty.RespectsIso (@Smooth.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hprRI : MorphismProperty.RespectsIso (@IsProper.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let A' := (Over.pullback (D.map e)).obj A
  let B' := (Over.pullback (D.map e)).obj B
  have hA' : FinitePresentation A'.hom := Stacks.GenericFlatness.finitePresentation_pullback _ _ hA
  have hB' : FinitePresentation B'.hom := Stacks.GenericFlatness.finitePresentation_pullback _ _ hB
  obtain ⟨_, _⟩ := compactSpace_left_of_finitePresentation A' hA'
  obtain ⟨_, _⟩ := compactSpace_left_of_finitePresentation B' hB'
  have : QuasiSeparated B'.hom := hB'.2.2
  have : LocallyOfFiniteType B'.hom := by have := hB'.1; infer_instance
  have hGfp : FinitePresentation G.left := finitePresentation_left G hA'
  have : LocallyOfFinitePresentation G.left := hGfp.1
  have hlim (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (hP : P m.left) :
      P ((Over.pullback (c.π.app j)).map G).left :=
    (prop_left_iff_of_comm P _ _ _ _ hG).mpr hP
  have hev₁ := eventually_of_exists D (@Smooth.{u}) G (by
    have := hlim _ hs
    exact exists_smooth_baseChange_of_smooth_limitBaseChange D c j A' B' G hc)
  have hev₂ := eventually_of_exists D (@IsProper.{u}) G (by
    have := hlim _ hp
    exact exists_isProper_baseChange_of_isLimit D c j hc A' B' G)
  exact eventually_and
    (Q₁ := fun _ g => Smooth ((Over.pullback (D.map g)).map G).left)
    (Q₂ := fun _ g => IsProper ((Over.pullback (D.map g)).map G).left ∧
      P ((Over.pullback (D.map g)).map G).left)
    hev₁ (eventually_and
      (Q₁ := fun _ g => IsProper ((Over.pullback (D.map g)).map G).left)
      (Q₂ := fun _ g => P ((Over.pullback (D.map g)).map G).left) hev₂ (hP j e G hG))

/-- **Geometric connectedness of the fibres and a bound on their dimension descend to a stage.**
Let `m` be a smooth morphism between the base changes to the limit of two schemes of finite
presentation over a stage `k`, the target affine over `k`, with geometrically connected fibres of
dimension at most one. For every model `G` of `m` over a later stage `j`, in canonical form, the
base change of `G` to every sufficiently late stage is locally of finite type with geometrically
connected fibres of dimension at most one. -/
theorem exists_stage_geometricallyConnected_fiber_le (hc : IsLimit c) (k : I)
    (A B : Over (D.obj k)) (hA : FinitePresentation A.hom) (hB : FinitePresentation B.hom)
    [IsAffineHom B.hom]
    (m : (Over.pullback (c.π.app k)).obj A ⟶ (Over.pullback (c.π.app k)).obj B)
    (hs : Smooth m.left) (hgc : GeometricallyConnected m.left)
    (hd : ∀ s, topologicalKrullDim (m.left.fiber s) ≤ 1) (j : I) (e : j ⟶ k)
    (G : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj B)
    (hG : (limitIso D c e A).hom ≫ m = (Over.pullback (c.π.app j)).map G ≫
      (limitIso D c e B).hom) :
    ∃ (j' : I) (g' : j' ⟶ j), ∀ (k' : I) (g'' : k' ⟶ j'),
      LocallyOfFiniteType ((Over.pullback (D.map (g'' ≫ g'))).map G).left ∧
      GeometricallyConnected ((Over.pullback (D.map (g'' ≫ g'))).map G).left ∧
      ∀ s, topologicalKrullDim (((Over.pullback (D.map (g'' ≫ g'))).map G).left.fiber s) ≤ 1 := by
  have : QuasiSeparated B.hom := hB.2.2
  have : LocallyOfFiniteType B.hom := by have := hB.1; infer_instance
  have hgcRI : MorphismProperty.RespectsIso (@GeometricallyConnected.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let A' := (Over.pullback (D.map e)).obj A
  let B' := (Over.pullback (D.map e)).obj B
  have hA' : FinitePresentation A'.hom := Stacks.GenericFlatness.finitePresentation_pullback _ _ hA
  have hB' : FinitePresentation B'.hom := Stacks.GenericFlatness.finitePresentation_pullback _ _ hB
  obtain ⟨_, _⟩ := compactSpace_left_of_finitePresentation A' hA'
  obtain ⟨_, _⟩ := compactSpace_left_of_finitePresentation B' hB'
  have : QuasiSeparated B'.hom := hB'.2.2
  have : LocallyOfFiniteType B'.hom := by have := hB'.1; infer_instance
  have hGfp : FinitePresentation G.left := finitePresentation_left G hA'
  have : LocallyOfFinitePresentation G.left := hGfp.1
  have : IsAffineHom (pullback.snd B.hom (D.map e)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback B.hom (D.map e))
      (‹IsAffineHom B.hom›)
  have : IsAffine B'.left := isAffine_of_isAffineHom (pullback.snd B.hom (D.map e))
  have hev₃ := exists_geometricallyConnected_stage D c hc j G hGfp
    ((prop_left_iff_of_comm _ _ _ _ _ hG).mpr hgc)
  have : LocallyOfFiniteType m.left := by have := hs; infer_instance
  have hev₄ := exists_topologicalKrullDim_fiber_le_stage D c hc j G 1
    (fun s => by
      have := forall_topologicalKrullDim_fiber_le_of_comm _ _ m _ hG hd s
      simpa using this)
  obtain ⟨j', g', hev⟩ := eventually_and
    (Q₁ := fun _ g => GeometricallyConnected ((Over.pullback (D.map g)).map G).left)
    (Q₂ := fun _ g => ∀ s, topologicalKrullDim (((Over.pullback (D.map g)).map G).left.fiber s) ≤
          ((1 : ℕ) : WithBot ℕ∞)) hev₃ hev₄
  exact ⟨j', g', fun k' g'' => ⟨prop_overPullback_map (@LocallyOfFiniteType.{u}) _ G inferInstance,
    (hev k' g'').1, fun s => by simpa using (hev k' g'').2 s⟩⟩

/-- Descent of an open immersion from the limit to a stage. -/
theorem exists_stage_isOpenImmersion (hc : IsLimit c) (k : I) (A B : Over (D.obj k))
    (hA : FinitePresentation A.hom) (hB : FinitePresentation B.hom)
    (m : (Over.pullback (c.π.app k)).obj A ⟶ (Over.pullback (c.π.app k)).obj B)
    (hm : IsOpenImmersion m.left) :
    ∃ (j : I) (e : j ⟶ k)
      (G : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj B),
      (limitIso D c e A).hom ≫ m = (Over.pullback (c.π.app j)).map G ≫ (limitIso D c e B).hom ∧
      ∃ (j' : I) (g' : j' ⟶ j), ∀ (k' : I) (g'' : k' ⟶ j'),
        IsOpenImmersion ((Over.pullback (D.map (g'' ≫ g'))).map G).left := by
  have : QuasiSeparated B.hom := hB.2.2
  have : LocallyOfFiniteType B.hom := by have := hB.1; infer_instance
  obtain ⟨j, e, G, hG⟩ := exists_hom_limitIso D c hc k A B hA hB m
  refine ⟨j, e, G, hG, ?_⟩
  have hoiRI : MorphismProperty.RespectsIso (@IsOpenImmersion.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let A' := (Over.pullback (D.map e)).obj A
  let B' := (Over.pullback (D.map e)).obj B
  have hA' : FinitePresentation A'.hom := Stacks.GenericFlatness.finitePresentation_pullback _ _ hA
  have hB' : FinitePresentation B'.hom := Stacks.GenericFlatness.finitePresentation_pullback _ _ hB
  obtain ⟨_, _⟩ := compactSpace_left_of_finitePresentation A' hA'
  obtain ⟨_, _⟩ := compactSpace_left_of_finitePresentation B' hB'
  have : QuasiSeparated B'.hom := hB'.2.2
  have : LocallyOfFiniteType B'.hom := by have := hB'.1; infer_instance
  have : LocallyOfFinitePresentation G.left := (finitePresentation_left G hA').1
  exact eventually_of_exists D (@IsOpenImmersion.{u}) G
    (exists_isOpenImmersion_pullback D c hc j A' B' G ((prop_left_iff_of_comm _ _ _ _ _ hG).mpr hm))

/-- Descent of a finite surjective morphism from the limit to a stage. -/
theorem exists_stage_isFinite_surjective (hc : IsLimit c) (k : I) (A B : Over (D.obj k))
    (hA : FinitePresentation A.hom) (hB : FinitePresentation B.hom)
    (m : (Over.pullback (c.π.app k)).obj A ⟶ (Over.pullback (c.π.app k)).obj B)
    (hf : IsFinite m.left) (hs : Surjective m.left) :
    ∃ (j : I) (e : j ⟶ k)
      (G : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj B),
      (limitIso D c e A).hom ≫ m = (Over.pullback (c.π.app j)).map G ≫ (limitIso D c e B).hom ∧
      ∃ (j' : I) (g' : j' ⟶ j), ∀ (k' : I) (g'' : k' ⟶ j'),
        IsFinite ((Over.pullback (D.map (g'' ≫ g'))).map G).left ∧
        Surjective ((Over.pullback (D.map (g'' ≫ g'))).map G).left := by
  have : QuasiSeparated B.hom := hB.2.2
  have : LocallyOfFiniteType B.hom := by have := hB.1; infer_instance
  obtain ⟨j, e, G, hG⟩ := exists_hom_limitIso D c hc k A B hA hB m
  refine ⟨j, e, G, hG, ?_⟩
  have hfinRI : MorphismProperty.RespectsIso (@IsFinite.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hsuRI : MorphismProperty.RespectsIso (@Surjective.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let A' := (Over.pullback (D.map e)).obj A
  let B' := (Over.pullback (D.map e)).obj B
  have hA' : FinitePresentation A'.hom := Stacks.GenericFlatness.finitePresentation_pullback _ _ hA
  have hB' : FinitePresentation B'.hom := Stacks.GenericFlatness.finitePresentation_pullback _ _ hB
  obtain ⟨_, _⟩ := compactSpace_left_of_finitePresentation A' hA'
  obtain ⟨_, _⟩ := compactSpace_left_of_finitePresentation B' hB'
  have : QuasiSeparated B'.hom := hB'.2.2
  have : LocallyOfFiniteType B'.hom := by have := hB'.1; infer_instance
  have : LocallyOfFinitePresentation G.left := (finitePresentation_left G hA').1
  have hev₁ := eventually_of_exists D (@IsFinite.{u}) G (by
    have := (prop_left_iff_of_comm _ _ _ _ _ hG).mpr hf
    exact exists_isFinite_baseChange_of_isLimit D c hc j A' B' G)
  have hev₂ := eventually_of_exists D (@Surjective.{u}) G (by
    have := (prop_left_iff_of_comm _ _ _ _ _ hG).mpr hs
    exact exists_surjective_baseChange_of_surjective_limitBaseChange D c hc j A' B' G)
  exact eventually_and
    (Q₁ := fun _ g => IsFinite ((Over.pullback (D.map g)).map G).left)
    (Q₂ := fun _ g => Surjective ((Over.pullback (D.map g)).map G).left) hev₁ hev₂

/-- Descent of the condition that a morphism `ν` be a closed immersion over an open immersion
`w`, and that the preimage of the open surject onto `T`, from the limit to a stage. -/
theorem exists_stage_closedImmersion_surjective (hc : IsLimit c) (J : I)
    {YJ YbJ TJ WJ XJ : Over (D.obj J)} (hYJ : FinitePresentation YJ.hom)
    (hYbJ : FinitePresentation YbJ.hom) (hTJ : FinitePresentation TJ.hom)
    (hWJ : FinitePresentation WJ.hom) (hXJ : FinitePresentation XJ.hom)
    (νJ : YJ ⟶ XJ) (wJ : WJ ⟶ XJ) (jJ : YJ ⟶ YbJ) (qJ : YbJ ⟶ TJ)
    {Y Ybar T WL XL : Over c.pt} (ν : Y ⟶ XL) (w : WL ⟶ XL) (jY : Y ⟶ Ybar)
    (qbar : Ybar ⟶ T)
    (ΦY : (Over.pullback (c.π.app J)).obj YJ ≅ Y)
    (ΦYb : (Over.pullback (c.π.app J)).obj YbJ ≅ Ybar)
    (ΦT : (Over.pullback (c.π.app J)).obj TJ ≅ T)
    (ΦW : (Over.pullback (c.π.app J)).obj WJ ≅ WL)
    (ΦX : (Over.pullback (c.π.app J)).obj XJ ≅ XL)
    (hν : ΦY.hom ≫ ν = (Over.pullback (c.π.app J)).map νJ ≫ ΦX.hom)
    (hw : ΦW.hom ≫ w = (Over.pullback (c.π.app J)).map wJ ≫ ΦX.hom)
    (hj : ΦY.hom ≫ jY = (Over.pullback (c.π.app J)).map jJ ≫ ΦYb.hom)
    (hq : ΦYb.hom ≫ qbar = (Over.pullback (c.π.app J)).map qJ ≫ ΦT.hom)
    (hW : IsClosedImmersion (pullback.snd ν.left w.left))
    (hWs : Surjective (pullback.fst ν.left w.left ≫ jY.left ≫ qbar.left)) :
    ∃ (j' : I) (g' : j' ⟶ J),
      IsClosedImmersion (pullback.snd ((Over.pullback (D.map g')).map νJ).left
        ((Over.pullback (D.map g')).map wJ).left) ∧
      Surjective (pullback.fst ((Over.pullback (D.map g')).map νJ).left
          ((Over.pullback (D.map g')).map wJ).left ≫
        ((Over.pullback (D.map g')).map jJ).left ≫ ((Over.pullback (D.map g')).map qJ).left) := by
  have hsuRI : MorphismProperty.RespectsIso (@Surjective.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hciRI : MorphismProperty.RespectsIso (@IsClosedImmersion.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : QuasiSeparated XJ.hom := hXJ.2.2
  have : LocallyOfFiniteType XJ.hom := by have := hXJ.1; infer_instance
  have : QuasiSeparated YbJ.hom := hYbJ.2.2
  have : LocallyOfFiniteType YbJ.hom := by have := hYbJ.1; infer_instance
  have : QuasiSeparated TJ.hom := hTJ.2.2
  have : LocallyOfFiniteType TJ.hom := by have := hTJ.1; infer_instance
  have hνfp := finitePresentation_left νJ hYJ
  have hwfp := finitePresentation_left wJ hWJ
  have hjfp := finitePresentation_left jJ hYJ
  have hqfp := finitePresentation_left qJ hYbJ
  let PJ : Over (D.obj J) := Over.mk (pullback.fst νJ.left wJ.left ≫ YJ.hom)
  let pa : PJ ⟶ YJ := Over.homMk (pullback.fst νJ.left wJ.left) rfl
  let pb : PJ ⟶ WJ := Over.homMk (pullback.snd νJ.left wJ.left) (by
    show pullback.snd _ _ ≫ WJ.hom = pullback.fst _ _ ≫ YJ.hom
    rw [← Over.w wJ, ← Over.w νJ, pullback.condition_assoc])
  have hsq : IsPullback pa.left pb.left νJ.left wJ.left := IsPullback.of_hasPullback _ _
  have hpafp : FinitePresentation pa.left :=
    FinitePresentation.of_isPullback (IsPullback.of_hasPullback νJ.left wJ.left).flip hwfp
  have hpbfp : FinitePresentation pb.left :=
    FinitePresentation.of_isPullback (IsPullback.of_hasPullback νJ.left wJ.left) hνfp
  have hPfp : FinitePresentation PJ.hom := by
    have := hpafp.1; have := hpafp.2.1; have := hpafp.2.2
    have := hYJ.1; have := hYJ.2.1; have := hYJ.2.2
    exact ⟨inferInstanceAs (LocallyOfFinitePresentation (pa.left ≫ YJ.hom)),
      inferInstanceAs (QuasiCompact (pa.left ≫ YJ.hom)),
      inferInstanceAs (QuasiSeparated (pa.left ≫ YJ.hom))⟩
  obtain ⟨_, _⟩ := compactSpace_left_of_finitePresentation PJ hPfp
  obtain ⟨_, _⟩ := compactSpace_left_of_finitePresentation WJ hWJ
  obtain ⟨_, _⟩ := compactSpace_left_of_finitePresentation TJ hTJ
  have hL := isPullback_overPullback_map (c.π.app J) pa pb νJ wJ hsq
  have hL' : IsPullback (((Over.pullback (c.π.app J)).map pa).left ≫ ΦY.hom.left)
      (((Over.pullback (c.π.app J)).map pb).left ≫ ΦW.hom.left) ν.left w.left :=
    IsPullback.of_iso hL (Iso.refl _) ((Over.forget _).mapIso ΦY) ((Over.forget _).mapIso ΦW)
      ((Over.forget _).mapIso ΦX) (by simp) (by simp)
      (by simp only [Functor.mapIso_hom, Over.forget_map]
          rw [← Over.comp_left, ← hν, Over.comp_left])
      (by simp only [Functor.mapIso_hom, Over.forget_map]
          rw [← Over.comp_left, ← hw, Over.comp_left])
  have hLsnd := hL'.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback ν.left w.left)
  have hLfst := hL'.isoIsPullback_hom_fst _ _ (IsPullback.of_hasPullback ν.left w.left)
  have hlim₁ : IsClosedImmersion ((Over.pullback (c.π.app J)).map pb).left := by
    have : IsIso ΦW.hom.left := (Over.forget _).map_isIso ΦW.hom
    rw [← MorphismProperty.cancel_right_of_respectsIso (@IsClosedImmersion.{u}) _ ΦW.hom.left,
      ← hLsnd]
    infer_instance
  have hlim₂ : Surjective ((Over.pullback (c.π.app J)).map (pa ≫ jJ ≫ qJ)).left := by
    have : IsIso ΦT.hom.left := (Over.forget _).map_isIso ΦT.hom
    rw [← MorphismProperty.cancel_right_of_respectsIso (@Surjective.{u}) _ ΦT.hom.left]
    have he : ((Over.pullback (c.π.app J)).map (pa ≫ jJ ≫ qJ)).left ≫ ΦT.hom.left =
        (hL'.isoIsPullback _ _ (IsPullback.of_hasPullback ν.left w.left)).hom ≫
          pullback.fst ν.left w.left ≫ jY.left ≫ qbar.left := by
      have hq' : ((Over.pullback (c.π.app J)).map qJ).left ≫ ΦT.hom.left =
          ΦYb.hom.left ≫ qbar.left := by
        simpa only [Over.comp_left] using (congrArg Over.Hom.left hq).symm
      have hj' : ((Over.pullback (c.π.app J)).map jJ).left ≫ ΦYb.hom.left =
          ΦY.hom.left ≫ jY.left := by
        simpa only [Over.comp_left] using (congrArg Over.Hom.left hj).symm
      rw [reassoc_of% hLfst]
      simp only [Functor.map_comp, Over.comp_left, Category.assoc]
      rw [hq', reassoc_of% hj']
    rw [he]
    infer_instance
  have : LocallyOfFiniteType pb.left := by have := hpbfp.1; infer_instance
  have : LocallyOfFinitePresentation (pa ≫ jJ ≫ qJ).left := by
    have := hpafp.1; have := hjfp.1; have := hqfp.1
    exact inferInstanceAs (LocallyOfFinitePresentation (pa.left ≫ jJ.left ≫ qJ.left))
  have he₁ := eventually_of_exists D (@IsClosedImmersion.{u}) pb (by
    have := hlim₁
    exact exists_isClosedImmersion_baseChange_of_isLimit D c hc J PJ WJ pb)
  have he₂ := eventually_of_exists D (@Surjective.{u}) (pa ≫ jJ ≫ qJ) (by
    have := hlim₂
    exact exists_surjective_baseChange_of_surjective_limitBaseChange D c hc J PJ TJ _)
  obtain ⟨j', g', H⟩ := eventually_and
    (Q₁ := fun _ g => IsClosedImmersion ((Over.pullback (D.map g)).map pb).left)
    (Q₂ := fun _ g => Surjective ((Over.pullback (D.map g)).map (pa ≫ jJ ≫ qJ)).left) he₁ he₂
  obtain ⟨H₁, H₂⟩ := H j' (𝟙 j')
  rw [Category.id_comp] at H₁ H₂
  refine ⟨j', g', ?_, ?_⟩
  · have hsq' := isPullback_overPullback_map (D.map g') pa pb νJ wJ hsq
    rw [← hsq'.isoIsPullback_inv_snd _ _ (IsPullback.of_hasPullback _ _)]
    infer_instance
  · have hsq' := isPullback_overPullback_map (D.map g') pa pb νJ wJ hsq
    rw [← reassoc_of% (hsq'.isoIsPullback_inv_fst _ _ (IsPullback.of_hasPullback _ _))]
    simp only [Functor.map_comp, Over.comp_left] at H₂
    infer_instance

/-- The objects of the diagram have models at one stage, the model of `T` being finite and
étale over the stage. -/
theorem exists_stage_models (hc : IsLimit c) (i₀ : I) (T Ybar Y WL : Over c.pt)
    (hT : FinitePresentation T.hom) (hYbar : FinitePresentation Ybar.hom)
    (hY : FinitePresentation Y.hom) (hWL : FinitePresentation WL.hom)
    (hTf : IsFinite T.hom) (hTe : Etale T.hom) :
    ∃ (k : I) (_ : k ⟶ i₀) (Tk Ybk Yk Wk : Over (D.obj k)),
      FinitePresentation Tk.hom ∧ FinitePresentation Ybk.hom ∧ FinitePresentation Yk.hom ∧
      FinitePresentation Wk.hom ∧ IsFinite Tk.hom ∧ Etale Tk.hom ∧
      Nonempty (T ≅ (Over.pullback (c.π.app k)).obj Tk) ∧
      Nonempty (Ybar ≅ (Over.pullback (c.π.app k)).obj Ybk) ∧
      Nonempty (Y ≅ (Over.pullback (c.π.app k)).obj Yk) ∧
      Nonempty (WL ≅ (Over.pullback (c.π.app k)).obj Wk) := by
  classical
  have : EssentiallySmall.{u} I := essentiallySmallSelf.{u} I
  have hfinRI : MorphismProperty.RespectsIso (@IsFinite.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hetRI : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨k₁, g₁, T₁, hT₁, ⟨eT₁⟩⟩ := exists_model_below D c hc i₀ T hT
  obtain ⟨k₂, g₂, Yb₂, hYb₂, ⟨eYb₂⟩⟩ := exists_model_below D c hc k₁ Ybar hYbar
  obtain ⟨k₃, g₃, Y₃, hY₃, ⟨eY₃⟩⟩ := exists_model_below D c hc k₂ Y hY
  obtain ⟨k₄, g₄, W₄, hW₄, ⟨eW₄⟩⟩ := exists_model_below D c hc k₃ WL hWL
  let T₄ := (Over.pullback (D.map (g₄ ≫ g₃ ≫ g₂))).obj T₁
  have hT₄ : FinitePresentation T₄.hom :=
    Stacks.GenericFlatness.finitePresentation_pullback _ T₁ hT₁
  let eT₄ : T ≅ (Over.pullback (c.π.app k₄)).obj T₄ :=
    eT₁ ≪≫ (limitIso D c (g₄ ≫ g₃ ≫ g₂) T₁).symm
  obtain ⟨cT₄, qT₄⟩ := compactSpace_left_of_finitePresentation T₄ hT₄
  let τ : T₄ ⟶ Over.mk (𝟙 (D.obj k₄)) := Over.homMk T₄.hom
  have : LocallyOfFinitePresentation τ.left := hT₄.1
  have : CompactSpace (Over.mk (𝟙 (D.obj k₄))).left := inferInstanceAs (CompactSpace (D.obj k₄))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj k₄))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj k₄))
  have hTL (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (hP : P T.hom) :
      P ((Over.pullback (c.π.app k₄)).map τ).left := by
    rw [Stacks.SmoothStrata.property_overPullback_terminal_iff P T₄]
    have : IsIso eT₄.hom.left := (Over.forget _).map_isIso eT₄.hom
    rw [← MorphismProperty.cancel_left_of_respectsIso P eT₄.hom.left, Over.w]
    exact hP
  have hevTf := eventually_of_exists D (@IsFinite.{u}) τ (by
    have := hTL _ hTf
    exact exists_isFinite_baseChange_of_isLimit D c hc k₄ T₄ _ τ)
  have hevTe := eventually_of_exists D (@Etale.{u}) τ (by
    have := hTL _ hTe
    obtain ⟨i, hi⟩ := exists_etale_pullback_of_isLimit D c hc k₄ T₄ _ τ
    exact ⟨i.left, i.hom, hi⟩)
  obtain ⟨k, g₅, hTk⟩ := eventually_and
    (Q₁ := fun _ g => IsFinite ((Over.pullback (D.map g)).map τ).left)
    (Q₂ := fun _ g => Etale ((Over.pullback (D.map g)).map τ).left) hevTf hevTe
  let hk : k ⟶ i₀ := g₅ ≫ g₄ ≫ g₃ ≫ g₂ ≫ g₁
  let Tk := (Over.pullback (D.map g₅)).obj T₄
  let Ybk := (Over.pullback (D.map (g₅ ≫ g₄ ≫ g₃))).obj Yb₂
  let Yk := (Over.pullback (D.map (g₅ ≫ g₄))).obj Y₃
  let Wk := (Over.pullback (D.map g₅)).obj W₄
  have hTk' : FinitePresentation Tk.hom :=
    Stacks.GenericFlatness.finitePresentation_pullback _ T₄ hT₄
  have hYbk : FinitePresentation Ybk.hom :=
    Stacks.GenericFlatness.finitePresentation_pullback _ Yb₂ hYb₂
  have hYk : FinitePresentation Yk.hom :=
    Stacks.GenericFlatness.finitePresentation_pullback _ Y₃ hY₃
  have hWk : FinitePresentation Wk.hom :=
    Stacks.GenericFlatness.finitePresentation_pullback _ W₄ hW₄
  let eT : T ≅ (Over.pullback (c.π.app k)).obj Tk := eT₄ ≪≫ (limitIso D c g₅ T₄).symm
  let eYb : Ybar ≅ (Over.pullback (c.π.app k)).obj Ybk :=
    eYb₂ ≪≫ (limitIso D c (g₅ ≫ g₄ ≫ g₃) Yb₂).symm
  let eY : Y ≅ (Over.pullback (c.π.app k)).obj Yk := eY₃ ≪≫ (limitIso D c (g₅ ≫ g₄) Y₃).symm
  let eW : WL ≅ (Over.pullback (c.π.app k)).obj Wk := eW₄ ≪≫ (limitIso D c g₅ W₄).symm
  obtain ⟨hTkf₀, hTke₀⟩ := hTk k (𝟙 k)
  rw [Category.id_comp] at hTkf₀ hTke₀
  have hTkf : IsFinite Tk.hom :=
    (Stacks.SmoothStrata.property_overPullback_terminal_iff (@IsFinite.{u}) T₄ (D.map g₅)).mp hTkf₀
  have hTke : Etale Tk.hom :=
    (Stacks.SmoothStrata.property_overPullback_terminal_iff (@Etale.{u}) T₄ (D.map g₅)).mp hTke₀
  exact ⟨k, hk, Tk, Ybk, Yk, Wk, hTk', hYbk, hYk, hWk, hTkf, hTke, ⟨eT⟩, ⟨eYb⟩, ⟨eY⟩, ⟨eW⟩⟩

omit [IsCofiltered I] [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
  [∀ i, IsAffine (D.obj i)] in
/-- Transport of a descended smooth proper morphism to a later stage. -/
theorem transport_smooth_proper {k j j' J : I} (e : j ⟶ k) (g' : j' ⟶ j) (v : J ⟶ j')
    (h : J ⟶ k) (hh : (v ≫ g') ≫ e = h) {A B : Over (D.obj k)}
    (m : (Over.pullback (c.π.app k)).obj A ⟶ (Over.pullback (c.π.app k)).obj B)
    (G : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj B)
    (hG : (limitIso D c e A).hom ≫ m = (Over.pullback (c.π.app j)).map G ≫
      (limitIso D c e B).hom)
    (H : Smooth ((Over.pullback (D.map (v ≫ g'))).map G).left ∧
      IsProper ((Over.pullback (D.map (v ≫ g'))).map G).left ∧
      GeometricallyConnected ((Over.pullback (D.map (v ≫ g'))).map G).left ∧
      ∀ s, topologicalKrullDim (((Over.pullback (D.map (v ≫ g'))).map G).left.fiber s) ≤ 1) :
    ∃ G' : (Over.pullback (D.map h)).obj A ⟶ (Over.pullback (D.map h)).obj B,
      (limitIso D c h A).hom ≫ m = (Over.pullback (c.π.app J)).map G' ≫
        (limitIso D c h B).hom ∧
      Smooth G'.left ∧ IsProper G'.left ∧ GeometricallyConnected G'.left ∧
      ∀ s, topologicalKrullDim (G'.left.fiber s) ≤ 1 := by
  have hsmRI : MorphismProperty.RespectsIso (@Smooth.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hprRI : MorphismProperty.RespectsIso (@IsProper.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hgcRI : MorphismProperty.RespectsIso (@GeometricallyConnected.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨H₁, H₂, H₃, H₄⟩ := H
  have : LocallyOfFiniteType ((Over.pullback (D.map (v ≫ g'))).map G).left := by
    have := H₁; infer_instance
  exact ⟨transportHom D e (v ≫ g') h hh G, limitIso_transportHom D c e (v ≫ g') h hh m G hG,
    (prop_transportHom_iff D (@Smooth.{u}) e (v ≫ g') h hh G).mpr H₁,
    (prop_transportHom_iff D (@IsProper.{u}) e (v ≫ g') h hh G).mpr H₂,
    (prop_transportHom_iff D (@GeometricallyConnected.{u}) e (v ≫ g') h hh G).mpr H₃,
    forall_topologicalKrullDim_fiber_le_conj
      (overPullbackCompIso (D.map e) (D.map (v ≫ g')) (D.map h)
        (by rw [← hh, D.map_comp (v ≫ g') e]) A).symm
      ((Over.pullback (D.map (v ≫ g'))).map G)
      (overPullbackCompIso (D.map e) (D.map (v ≫ g')) (D.map h)
        (by rw [← hh, D.map_comp (v ≫ g') e]) B)
      H₄⟩

omit [IsCofiltered I] [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
  [∀ i, IsAffine (D.obj i)] in
/-- Transport of a descended morphism with two properties to a later stage. -/
theorem transport_prop₂ (P Q : MorphismProperty Scheme.{u}) [P.RespectsIso] [Q.RespectsIso]
    {k j j' J : I} (e : j ⟶ k) (g' : j' ⟶ j) (v : J ⟶ j')
    (h : J ⟶ k) (hh : (v ≫ g') ≫ e = h) {A B : Over (D.obj k)}
    (m : (Over.pullback (c.π.app k)).obj A ⟶ (Over.pullback (c.π.app k)).obj B)
    (G : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj B)
    (hG : (limitIso D c e A).hom ≫ m = (Over.pullback (c.π.app j)).map G ≫
      (limitIso D c e B).hom)
    (H : P ((Over.pullback (D.map (v ≫ g'))).map G).left ∧
      Q ((Over.pullback (D.map (v ≫ g'))).map G).left) :
    ∃ G' : (Over.pullback (D.map h)).obj A ⟶ (Over.pullback (D.map h)).obj B,
      (limitIso D c h A).hom ≫ m = (Over.pullback (c.π.app J)).map G' ≫
        (limitIso D c h B).hom ∧ P G'.left ∧ Q G'.left :=
  ⟨transportHom D e (v ≫ g') h hh G, limitIso_transportHom D c e (v ≫ g') h hh m G hG,
    (prop_transportHom_iff D P e (v ≫ g') h hh G).mpr H.1,
    (prop_transportHom_iff D Q e (v ≫ g') h hh G).mpr H.2⟩

/-- Four morphisms into a stage are dominated by one stage, compatibly. -/
theorem exists_cone₄ {k a b c' d : I} (fa : a ⟶ k) (fb : b ⟶ k) (fc : c' ⟶ k) (fd : d ⟶ k) :
    ∃ (J : I) (h : J ⟶ k) (va : J ⟶ a) (vb : J ⟶ b) (vc : J ⟶ c') (vd : J ⟶ d),
      va ≫ fa = h ∧ vb ≫ fb = h ∧ vc ≫ fc = h ∧ vd ≫ fd = h := by
  obtain ⟨J₁, a₁, b₁, h₁⟩ := IsCofiltered.cospan fa fb
  obtain ⟨J₂, a₂, b₂, h₂⟩ := IsCofiltered.cospan (a₁ ≫ fa) fc
  obtain ⟨J, a₃, b₃, h₃⟩ := IsCofiltered.cospan (a₂ ≫ a₁ ≫ fa) fd
  refine ⟨J, a₃ ≫ a₂ ≫ a₁ ≫ fa, a₃ ≫ a₂ ≫ a₁, a₃ ≫ a₂ ≫ b₁, a₃ ≫ b₂, b₃, ?_, ?_, ?_, ?_⟩
  · simp only [Category.assoc]
  · simp only [Category.assoc]; rw [h₁]
  · simp only [Category.assoc]; rw [← h₂]
  · exact h₃.symm

/-- The four morphisms of the diagram descend, with their properties, to one common stage, in
canonical form. -/
theorem exists_stage_morphisms (hc : IsLimit c) (k : I) (Tk Ybk Yk Wk Xk : Over (D.obj k))
    (hTk' : FinitePresentation Tk.hom) (hYbk : FinitePresentation Ybk.hom)
    (hYk : FinitePresentation Yk.hom) (hWk : FinitePresentation Wk.hom)
    (hXk : FinitePresentation Xk.hom) [IsAffineHom Tk.hom]
    (mq : (Over.pullback (c.π.app k)).obj Ybk ⟶ (Over.pullback (c.π.app k)).obj Tk)
    (mj : (Over.pullback (c.π.app k)).obj Yk ⟶ (Over.pullback (c.π.app k)).obj Ybk)
    (mν : (Over.pullback (c.π.app k)).obj Yk ⟶ (Over.pullback (c.π.app k)).obj Xk)
    (mw : (Over.pullback (c.π.app k)).obj Wk ⟶ (Over.pullback (c.π.app k)).obj Xk)
    (hqs : Smooth mq.left) (hqp : IsProper mq.left) (hqc : GeometricallyConnected mq.left)
    (hqd : ∀ s, topologicalKrullDim (mq.left.fiber s) ≤ 1) (hj : IsOpenImmersion mj.left)
    (hνf : IsFinite mν.left) (hνs : Surjective mν.left) (hw : IsOpenImmersion mw.left) :
    ∃ (J : I) (h : J ⟶ k)
      (qJ : (Over.pullback (D.map h)).obj Ybk ⟶ (Over.pullback (D.map h)).obj Tk)
      (jJ : (Over.pullback (D.map h)).obj Yk ⟶ (Over.pullback (D.map h)).obj Ybk)
      (νJ : (Over.pullback (D.map h)).obj Yk ⟶ (Over.pullback (D.map h)).obj Xk)
      (wJ : (Over.pullback (D.map h)).obj Wk ⟶ (Over.pullback (D.map h)).obj Xk),
      (limitIso D c h Ybk).hom ≫ mq = (Over.pullback (c.π.app J)).map qJ ≫
        (limitIso D c h Tk).hom ∧
      (limitIso D c h Yk).hom ≫ mj = (Over.pullback (c.π.app J)).map jJ ≫
        (limitIso D c h Ybk).hom ∧
      (limitIso D c h Yk).hom ≫ mν = (Over.pullback (c.π.app J)).map νJ ≫
        (limitIso D c h Xk).hom ∧
      (limitIso D c h Wk).hom ≫ mw = (Over.pullback (c.π.app J)).map wJ ≫
        (limitIso D c h Xk).hom ∧
      Smooth qJ.left ∧ IsProper qJ.left ∧ GeometricallyConnected qJ.left ∧
      (∀ s, topologicalKrullDim (qJ.left.fiber s) ≤ 1) ∧ IsOpenImmersion jJ.left ∧
      IsFinite νJ.left ∧ Surjective νJ.left ∧ IsOpenImmersion wJ.left := by
  have hfinRI : MorphismProperty.RespectsIso (@IsFinite.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hoiRI : MorphismProperty.RespectsIso (@IsOpenImmersion.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hsuRI : MorphismProperty.RespectsIso (@Surjective.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨jq, eq, Gq, hGq, jq', gq', hevq⟩ := exists_stage_smooth_proper D c hc k Ybk Tk hYbk hTk'
    mq hqs hqp (fun _ _ q => LocallyOfFiniteType q ∧ GeometricallyConnected q ∧
      ∀ s, topologicalKrullDim (q.fiber s) ≤ 1)
    (exists_stage_geometricallyConnected_fiber_le D c hc k Ybk Tk hYbk hTk' mq hqs hqc hqd)
  obtain ⟨jj, ej, Gj, hGj, jj', gj', hevj⟩ := exists_stage_isOpenImmersion D c hc k Yk Ybk hYk
    hYbk mj hj
  obtain ⟨jν, eν, Gν, hGν, jν', gν', hevν⟩ := exists_stage_isFinite_surjective D c hc k Yk Xk
    hYk hXk mν hνf hνs
  obtain ⟨jw, ew, Gw, hGw, jw', gw', hevw⟩ := exists_stage_isOpenImmersion D c hc k Wk Xk hWk
    hXk mw hw
  obtain ⟨J, h, vq, vj, vν, vw, hhq, hhj, hhν, hhw⟩ :=
    exists_cone₄ (gq' ≫ eq) (gj' ≫ ej) (gν' ≫ eν) (gw' ≫ ew)
  obtain ⟨qJ, hcq, hqJs, hqJp, hqJc, hqJd⟩ := transport_smooth_proper D c eq gq' vq h
    (by rw [Category.assoc, hhq]) mq Gq hGq
    ⟨(hevq J vq).1, (hevq J vq).2.1, (hevq J vq).2.2.2⟩
  obtain ⟨jJ, hcj, hjJ, -⟩ := transport_prop₂ D c (@IsOpenImmersion.{u}) (@IsOpenImmersion.{u})
    ej gj' vj h (by rw [Category.assoc, hhj]) mj Gj hGj ⟨hevj J vj, hevj J vj⟩
  obtain ⟨νJ, hcν, hνJf, hνJs⟩ := transport_prop₂ D c (@IsFinite.{u}) (@Surjective.{u})
    eν gν' vν h (by rw [Category.assoc, hhν]) mν Gν hGν (hevν J vν)
  obtain ⟨wJ, hcw, hwJ, -⟩ := transport_prop₂ D c (@IsOpenImmersion.{u}) (@IsOpenImmersion.{u})
    ew gw' vw h (by rw [Category.assoc, hhw]) mw Gw hGw ⟨hevw J vw, hevw J vw⟩
  exact ⟨J, h, qJ, jJ, νJ, wJ, hcq, hcj, hcν, hcw, hqJs, hqJp, hqJc, hqJd, hjJ, hνJf, hνJs, hwJ⟩

/-- **Stacks Project, Tag 0GK7, the descent step.** A diagram of the shape produced over a field
by [Stacks, Tag 0GK5], over the base change to the limit of a scheme of finite presentation over
a stage, descends with all its properties to the base change to a later stage: a finite étale
`T'`, a smooth proper `q̄'` with geometrically connected fibres of dimension at most one, an open
immersion `j'`, a finite surjective `ν'`, and an open immersion `w'` such that the base change of
`ν'` along `w'` is a closed immersion and the preimage of `w'` surjects onto `T'`. -/
theorem exists_stage_curveDiagram (hc : IsLimit c) (i₀ : I) (X₀ : Over (D.obj i₀))
    (hX₀ : FinitePresentation X₀.hom) (T Ybar Y WL : Over c.pt)
    (hT : FinitePresentation T.hom) (hYbar : FinitePresentation Ybar.hom)
    (hY : FinitePresentation Y.hom) (hWL : FinitePresentation WL.hom)
    (qbar : Ybar ⟶ T) (jY : Y ⟶ Ybar) (ν : Y ⟶ (Over.pullback (c.π.app i₀)).obj X₀)
    (w : WL ⟶ (Over.pullback (c.π.app i₀)).obj X₀)
    (hTf : IsFinite T.hom) (hTe : Etale T.hom) (hqs : Smooth qbar.left)
    (hqp : IsProper qbar.left) (hqc : GeometricallyConnected qbar.left)
    (hqd : ∀ s, topologicalKrullDim (qbar.left.fiber s) ≤ 1)
    (hj : IsOpenImmersion jY.left) (hνf : IsFinite ν.left) (hνs : Surjective ν.left)
    (hw : IsOpenImmersion w.left) (hW : IsClosedImmersion (pullback.snd ν.left w.left))
    (hWs : Surjective (pullback.fst ν.left w.left ≫ jY.left ≫ qbar.left)) :
    ∃ (j : I) (g : j ⟶ i₀) (T' Ybar' Y' WL' : Over (D.obj j)) (qbar' : Ybar' ⟶ T')
      (jY' : Y' ⟶ Ybar') (ν' : Y' ⟶ (Over.pullback (D.map g)).obj X₀)
      (w' : WL' ⟶ (Over.pullback (D.map g)).obj X₀),
      IsFinite T'.hom ∧ Etale T'.hom ∧ Smooth qbar'.left ∧ IsProper qbar'.left ∧
      GeometricallyConnected qbar'.left ∧
      (∀ s, topologicalKrullDim (qbar'.left.fiber s) ≤ 1) ∧ IsOpenImmersion jY'.left ∧
      IsFinite ν'.left ∧ Surjective ν'.left ∧ IsOpenImmersion w'.left ∧
      IsClosedImmersion (pullback.snd ν'.left w'.left) ∧
      Surjective (pullback.fst ν'.left w'.left ≫ jY'.left ≫ qbar'.left) := by
  classical
  have hsmRI : MorphismProperty.RespectsIso (@Smooth.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hfinRI : MorphismProperty.RespectsIso (@IsFinite.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hprRI : MorphismProperty.RespectsIso (@IsProper.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hgcRI : MorphismProperty.RespectsIso (@GeometricallyConnected.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hoiRI : MorphismProperty.RespectsIso (@IsOpenImmersion.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hsuRI : MorphismProperty.RespectsIso (@Surjective.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨k, g₀, Tk, Ybk, Yk, Wk, hTk', hYbk, hYk, hWk, hTkf, hTke, ⟨eT⟩, ⟨eYb⟩, ⟨eY⟩, ⟨eW⟩⟩ :=
    exists_stage_models D c hc i₀ T Ybar Y WL hT hYbar hY hWL hTf hTe
  let hk : k ⟶ i₀ := g₀
  let Xk := (Over.pullback (D.map hk)).obj X₀
  have hXk : FinitePresentation Xk.hom :=
    Stacks.GenericFlatness.finitePresentation_pullback _ X₀ hX₀
  let eX : (Over.pullback (c.π.app i₀)).obj X₀ ≅ (Over.pullback (c.π.app k)).obj Xk :=
    (limitIso D c hk X₀).symm
  have : LocallyOfFiniteType qbar.left := inferInstance
  obtain ⟨J, h, qJ, jJ, νJ, wJ, hGq, hGj, hGν, hGw, hqJs, hqJp, hqJc, hqJd, hjJ, hνJf, hνJs,
      hwJ⟩ := exists_stage_morphisms D c hc k Tk Ybk Yk Wk Xk hTk' hYbk hYk hWk hXk
    (eYb.inv ≫ qbar ≫ eT.hom) (eY.inv ≫ jY ≫ eYb.hom) (eY.inv ≫ ν ≫ eX.hom)
    (eW.inv ≫ w ≫ eX.hom)
    ((prop_left_conj_iff _ eYb.symm qbar eT).mpr hqs)
    ((prop_left_conj_iff _ eYb.symm qbar eT).mpr hqp)
    ((prop_left_conj_iff _ eYb.symm qbar eT).mpr hqc)
    (forall_topologicalKrullDim_fiber_le_conj eYb.symm qbar eT hqd)
    ((prop_left_conj_iff _ eY.symm jY eYb).mpr hj)
    ((prop_left_conj_iff _ eY.symm ν eX).mpr hνf)
    ((prop_left_conj_iff _ eY.symm ν eX).mpr hνs)
    ((prop_left_conj_iff _ eW.symm w eX).mpr hw)
  have hcq := comm_trans_symm _ eYb _ eT qbar _ hGq
  have hcj := comm_trans_symm _ eY _ eYb jY _ hGj
  have hcν := comm_trans_symm _ eY _ eX ν _ hGν
  have hcw := comm_trans_symm _ eW _ eX w _ hGw
  have hTJ : FinitePresentation ((Over.pullback (D.map h)).obj Tk).hom :=
    Stacks.GenericFlatness.finitePresentation_pullback _ _ hTk'
  have hYbJ : FinitePresentation ((Over.pullback (D.map h)).obj Ybk).hom :=
    Stacks.GenericFlatness.finitePresentation_pullback _ _ hYbk
  have hYJ : FinitePresentation ((Over.pullback (D.map h)).obj Yk).hom :=
    Stacks.GenericFlatness.finitePresentation_pullback _ _ hYk
  have hWJ : FinitePresentation ((Over.pullback (D.map h)).obj Wk).hom :=
    Stacks.GenericFlatness.finitePresentation_pullback _ _ hWk
  have hXJ : FinitePresentation ((Over.pullback (D.map h)).obj Xk).hom :=
    Stacks.GenericFlatness.finitePresentation_pullback _ _ hXk
  obtain ⟨J', g', hcl, hsu⟩ := exists_stage_closedImmersion_surjective D c hc J hYJ hYbJ hTJ hWJ
    hXJ νJ wJ jJ qJ ν w jY qbar _ _ _ _ _ hcν hcw hcj hcq hW hWs
  let isoX : (Over.pullback (D.map g')).obj ((Over.pullback (D.map h)).obj Xk) ≅
      (Over.pullback (D.map (g' ≫ h ≫ hk))).obj X₀ :=
    (Over.pullback (D.map g')).mapIso
        (overPullbackCompIso (D.map hk) (D.map h) (D.map (h ≫ hk)) (D.map_comp _ _).symm X₀) ≪≫
      overPullbackCompIso (D.map (h ≫ hk)) (D.map g') (D.map (g' ≫ h ≫ hk))
        (D.map_comp _ _).symm X₀
  have : IsIso isoX.hom.left := (Over.forget _).map_isIso isoX.hom
  refine ⟨J', g' ≫ h ≫ hk, (Over.pullback (D.map g')).obj ((Over.pullback (D.map h)).obj Tk),
    (Over.pullback (D.map g')).obj ((Over.pullback (D.map h)).obj Ybk),
    (Over.pullback (D.map g')).obj ((Over.pullback (D.map h)).obj Yk),
    (Over.pullback (D.map g')).obj ((Over.pullback (D.map h)).obj Wk),
    (Over.pullback (D.map g')).map qJ, (Over.pullback (D.map g')).map jJ,
    (Over.pullback (D.map g')).map νJ ≫ isoX.hom, (Over.pullback (D.map g')).map wJ ≫ isoX.hom,
    ?_, ?_, prop_overPullback_map _ _ _ hqJs, prop_overPullback_map _ _ _ hqJp,
    prop_overPullback_map _ _ _ hqJc,
    forall_topologicalKrullDim_fiber_le_of_isPullback (overPullback_isPullback _ _ _ qJ) hqJd,
    prop_overPullback_map _ _ _ hjJ, ?_, ?_, ?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _)
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) hTkf)
  · exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _)
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) hTke)
  · have := prop_overPullback_map _ (D.map g') _ hνJf
    rw [Over.comp_left]
    infer_instance
  · have := prop_overPullback_map _ (D.map g') _ hνJs
    rw [Over.comp_left]
    infer_instance
  · have := prop_overPullback_map _ (D.map g') _ hwJ
    rw [Over.comp_left]
    infer_instance
  · have hsq := isPullback_pullback_comp_iso ((Over.pullback (D.map g')).map νJ).left
      ((Over.pullback (D.map g')).map wJ).left ((Over.forget _).mapIso isoX)
    simp only [Functor.mapIso_hom, Over.forget_map] at hsq
    rw [Over.comp_left, Over.comp_left,
      ← hsq.isoIsPullback_inv_snd _ _ (IsPullback.of_hasPullback _ _)]
    infer_instance
  · have hsq := isPullback_pullback_comp_iso ((Over.pullback (D.map g')).map νJ).left
      ((Over.pullback (D.map g')).map wJ).left ((Over.forget _).mapIso isoX)
    simp only [Functor.mapIso_hom, Over.forget_map] at hsq
    rw [Over.comp_left, Over.comp_left,
      ← reassoc_of% (hsq.isoIsPullback_inv_fst _ _ (IsPullback.of_hasPullback _ _))]
    infer_instance

end AlgebraicGeometry

end
