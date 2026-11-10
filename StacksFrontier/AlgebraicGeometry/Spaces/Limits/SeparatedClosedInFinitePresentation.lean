module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedImmersionIntoFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFilteredColimitOfApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFinitePresentationOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedSubspaceApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SeparatedAndClosed

/-!
# Separated morphisms of finite type are closed in separated morphisms of finite presentation

Let `f : X ⟶ Y` be a separated morphism of finite type of algebraic spaces over a scheme `S`,
with `Y` quasi-compact and quasi-separated. Stacks 0873 asserts that `f` factors as a closed
immersion `X ⟶ X'` followed by a separated morphism of finite presentation `X' ⟶ Y`.

This file proves the statement from two results that enter as arguments: Stacks 07SU over
`Spec ℤ`, the absolute Noetherian approximation, and Stacks 0A0T. From the first, Stacks 0872
gives a closed immersion `X ⟶ Z` into some `Z` of finite presentation over `Y`, and Stacks 0A0U
writes the closed subspace `X ⊆ Z` as the intersection of a directed family of closed subspaces
of finite presentation `X_a ⊆ Z`.

## Main results

* `AlgebraicGeometry.Space.exists_isSeparated_isFinitePresentation_closedImmersion_of_steps`:
  the factorization of Stacks 0873, from Stacks 07SU and 0A0T.

## Implementation notes

The source concludes with Stacks 086X: since `X = lim X_a` is separated over `Y`, so is some
`X_a`. This library's Stacks 086X asks the index of the system to be smaller than the cofinality
of the site's size cutoff, and the index here, the finite type quasi-coherent subideals of an
ideal sheaf, admits no such bound. The step is therefore read through the diagonal instead:
`X_a ⟶ Y` is separated as soon as `X_a ⟶ Z ⟶ Z ×_Y Z` is a closed immersion, since the
comparison `X_a ×_Y X_a ⟶ Z ×_Y Z` is a closed immersion; the system `X_a ⟶ Z ×_Y Z` has
closed immersions as transition morphisms, locally of finite type structure morphisms, and
limit `X ⟶ X ×_Y X ⟶ Z ×_Y Z`, a closed immersion because `f` is separated, so Stacks 0A0T
applies. Stacks 0A0T is taken in the form of the source, with no bound on the size of the index.

## References

* [Stacks Project, Tag 0873](https://stacks.math.columbia.edu/tag/0873)
* [Stacks Project, Tag 0872](https://stacks.math.columbia.edu/tag/0872)
* [Stacks Project, Tag 0A0U](https://stacks.math.columbia.edu/tag/0A0U)
* [Stacks Project, Tag 0A0T](https://stacks.math.columbia.edu/tag/0A0T)
* [Stacks Project, Tag 086X](https://stacks.math.columbia.edu/tag/086X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Filter

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- For a closed immersion `j : X ⟶ Z` and `g : Z ⟶ Y`, the comparison map
`X ×_Y X ⟶ Z ×_Y Z` is a closed immersion and `j ≫ Δ_g = Δ_{f'} ≫ (j ×_Y j)`. -/
private theorem isClosedImmersion_pullbackMap_and_comp_diagonal
    {X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f' : X ⟶ Y) (j : X ⟶ Z) (g : Z ⟶ Y)
    (hj : IsClosedImmersion B S hS j) (hsq : f' ≫ 𝟙 Y = j ≫ g) :
    IsClosedImmersion B S hS (pullback.map f' f' g g j j (𝟙 Y) hsq hsq) ∧
      j ≫ pullback.diagonal g =
        pullback.diagonal f' ≫ pullback.map f' f' g g j j (𝟙 Y) hsq hsq :=
  ⟨isClosedImmersion_pullbackMap B S hS hj (isClosedImmersion_of_isIso B S hS (𝟙 Y)) hsq,
    by apply pullback.hom_ext <;> simp⟩

/-- Let `f : X ⟶ Y` be a separated morphism of finite type of algebraic spaces over `S` with `Y`
quasi-compact and quasi-separated. Assume `h07SU`, that every quasi-compact and quasi-separated
algebraic space over `Spec ℤ` has a Noetherian approximation, and `h0A0T`, that for a directed
inverse system of quasi-compact and quasi-separated algebraic spaces `D_i` over `Y` with closed
immersions as transition morphisms and locally of finite type structure morphisms, whose limit
maps to `Y` by a closed immersion, some `D_i ⟶ Y` is a closed immersion. Then there are an
algebraic space `X'`, a separated morphism of finite presentation `f' : X' ⟶ Y` and a closed
immersion `i : X ⟶ X'` with `i ≫ f' = f`. -/
theorem exists_isSeparated_isFinitePresentation_closedImmersion_of_steps
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsFiniteType B S hS f) (hsep : IsSeparated B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Z → IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Z →
        IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ Z)
    (h0A0T : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
      {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
      (c : Cone D) (_ : IsLimit c) (f : c.pt ⟶ Y)
      (_ : c.π ≫ t = (Functor.const Iᵒᵖ).map f),
      IsAlgebraicSpace B S hS Y → IsAlgebraicSpace B S hS c.pt →
      (∀ i, IsAlgebraicSpace B S hS (D.obj (op i))) →
      IsQuasiCompactSpace B S hS Y →
      IsAbsolutelyQuasiSeparated B S hS hZ Y →
      (∀ i, IsQuasiCompactSpace B S hS (D.obj (op i))) →
      (∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj (op i))) →
      (∀ {a b : Iᵒᵖ} (φ : a ⟶ b), IsClosedImmersion B S hS (D.map φ)) →
      (∀ i, IsLocallyOfFiniteType B S hS (t.app (op i))) →
      IsClosedImmersion B S hS f →
      ∀ᶠ i in atTop, IsClosedImmersion B S hS (t.app (op i))) :
    ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f' : X' ⟶ Y) (i : X ⟶ X'),
      IsAlgebraicSpace B S hS X' ∧ IsSeparated B S hS f' ∧ IsFinitePresentation B S hS f' ∧
        IsClosedImmersion B S hS i ∧ i ≫ f' = f := by
  classical
  have hXqc : IsQuasiCompactSpace B S hS X :=
    isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd (𝟙 Y) f)) (hf.2 Y hY hYqc (𝟙 Y))
  have hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hX hYqs
      (isQuasiSeparated_of_isSeparated B S hS hsep)
  obtain ⟨Z, g, i, hZalg, hgfp, hi, hig⟩ :=
    exists_isFinitePresentation_isClosedImmersion_of_isLocallyOfFiniteType_of_noetherian
      B S hS f hX hY hf.1 hXqc hXqs hYqc hYqs h07SU
  have hZqc : IsQuasiCompactSpace B S hS Z :=
    isQuasiCompactSpace_of_isFinitePresentation B S hS g hY hYqc hgfp
  have hZqs : IsAbsolutelyQuasiSeparated B S hS hZ Z :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hZalg hYqs hgfp.2.2
  let Xc : ClosedSubspaces B S hS Z :=
    ⟨Subfunctor.range i, isClosedSubspace_range_of_isClosedImmersion B S hS i hX hi⟩
  have : Mono i := mono_of_isClosedImmersion B S hS i hi
  let e : X ≅ (Subfunctor.range i).toFunctor := asIso (Subfunctor.toRange i)
  have he : e.hom ≫ (Subfunctor.range i).ι = i := Subfunctor.toRange_ι i
  obtain ⟨A⟩ := hasClosedSubspaceApproximation_of_noetherianApproximation B S hS hZ h07SU
    ⟨Z, hZalg⟩ hZqc hZqs Xc
  let := A.indexPreorder
  let := A.indexDirected
  have : Nonempty A.index := ⟨A.point⟩
  let δ : Z ⟶ pullback g g := pullback.diagonal g
  let D := closedSubspaceDiagram B S hS (fun a => (A.stage a).1) A.stage_antitone
  let t : D ⟶ (Functor.const A.indexᵒᵖ).obj (pullback g g) :=
    { app := fun a => (A.stage a.unop).1.ι ≫ δ
      naturality := fun a b φ => by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, D,
          closedSubspaceDiagram]
        rw [← Category.assoc, Subfunctor.homOfLe_ι] }
  let c := closedSubspaceCone B S hS (fun a => (A.stage a).1) A.stage_antitone Xc.1 A.le_stage
  have hcomm : c.π ≫ t = (Functor.const A.indexᵒᵖ).map ((Subfunctor.range i).ι ≫ δ) := by
    ext a : 2
    simp only [NatTrans.comp_app, Functor.const_map_app, t, c, closedSubspaceCone]
    rw [← Category.assoc, Subfunctor.homOfLe_ι]
  have hP : IsAlgebraicSpace B S hS (pullback g g) :=
    isAlgebraicSpace_pullback B S hS g g hZalg hZalg hY
  have hPqc : IsQuasiCompactSpace B S hS (pullback g g) :=
    isQuasiCompactSpace_pullback B S hS hZ g g hZalg hY hZqc hZqc hYqs
  have hPqs : IsAbsolutelyQuasiSeparated B S hS hZ (pullback g g) :=
    isAbsolutelyQuasiSeparated_pullback B S hS hZ g g hZalg hZalg hY hZqs hZqs
  have hstageqs : ∀ a, IsAbsolutelyQuasiSeparated B S hS hZ (A.stage a).1.toFunctor := fun a =>
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ (A.stage a).2.1 hZqs
      (isQuasiSeparated_of_isSeparated B S hS
        (isSeparated_of_isClosedImmersion B S hS _ (A.stage a).2.2))
  have hsq : f ≫ 𝟙 Y = i ≫ g := by rw [Category.comp_id, hig]
  obtain ⟨hmap, hδi⟩ := isClosedImmersion_pullbackMap_and_comp_diagonal B S hS f i g hi hsq
  have hlim : IsClosedImmersion B S hS ((Subfunctor.range i).ι ≫ δ) := by
    rw [show (Subfunctor.range i).ι = e.inv ≫ i by rw [Iso.eq_inv_comp, he], Category.assoc, hδi]
    exact isClosedImmersion_comp B S hS _ _ (isClosedImmersion_of_isIso B S hS e.inv)
      (isClosedImmersion_comp B S hS _ _ hsep hmap)
  obtain ⟨a, ha⟩ := (h0A0T D t c A.isLimit ((Subfunctor.range i).ι ≫ δ) hcomm hP Xc.2.1
    (fun a => (A.stage a).2.1) hPqc hPqs
    (fun a => isQuasiCompactSpace_of_isClosedImmersion B S hS hZqc _ (A.stage a).2.2)
    hstageqs
    (fun φ => isClosedImmersion_closedSubspaceDiagram_map B S hS A.stage A.stage_antitone φ)
    (fun a => isLocallyOfFiniteType_comp B S hS (A.stage a).2.1 hZalg hP _ _
      (isLocallyOfFiniteType_of_isClosedImmersion B S hS _ (A.stage a).2.2)
      (isLocallyOfFiniteType_pullback_diagonal B S hS hZalg g))
    hlim).exists
  let ι := (A.stage a).1.ι
  have hιc : IsClosedImmersion B S hS ι := (A.stage a).2.2
  refine ⟨(A.stage a).1.toFunctor, ι ≫ g, e.hom ≫ Subfunctor.homOfLe (A.le_stage a),
    (A.stage a).2.1, ?_, ?_, ?_, ?_⟩
  · have hsq' : (ι ≫ g) ≫ 𝟙 Y = ι ≫ g := Category.comp_id _
    obtain ⟨hmap', hδι⟩ := isClosedImmersion_pullbackMap_and_comp_diagonal B S hS (ι ≫ g) ι g hιc
      hsq'
    exact isClosedImmersion_of_comp_of_isSeparated B S hS _ _ (hδι ▸ ha)
      (isSeparated_of_isClosedImmersion B S hS _ hmap')
  · exact (isFinitePresentation_comp_iff_of_isClosedImmersion B S hS (A.stage a).2.1 hZalg hY
      ι g hιc hgfp).mpr (A.stage_isFinitePresentation a)
  · refine isClosedImmersion_of_comp_of_isSeparated B S hS _ ι ?_
      (isSeparated_of_isClosedImmersion B S hS _ hιc)
    rwa [Category.assoc, Subfunctor.homOfLe_ι, he]
  · rw [Category.assoc, ← Category.assoc (Subfunctor.homOfLe _), Subfunctor.homOfLe_ι,
      ← Category.assoc, he, hig]

end AlgebraicGeometry.Space

end
