module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescentOfCutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedSubspaceSystemIndexBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperFinitePresentationApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SeparatedFinitePresentationEmbedding

/-!
# Stacks 0873 and Stacks 0A0W from Stacks 0872 and Stacks 0A0U

Let `f : X ⟶ Y` be a morphism of algebraic spaces with `Y` quasi-compact and quasi-separated.
Taking Stacks 0872 and Stacks 0A0U as explicit hypotheses `h0872` and `h0A0U`, this file proves
that a separated `f` of finite type factors as a closed immersion followed by a separated morphism
of finite presentation (Stacks 0873), and that if `f` is proper then `X` is a directed limit, along
closed immersions, of algebraic spaces proper and of finite presentation over `Y` (Stacks 0A0W).

## Main results

In the namespace `AlgebraicGeometry.Space`:

* `exists_isClosedImmersion_isSeparated_isFinitePresentation_of_comp_of_closedSubspaceLimits`:
  a separated composite `j ≫ g` of a closed immersion and a morphism of finite presentation
  factors as a closed immersion followed by a separated morphism of finite presentation.
* `exists_isClosedImmersion_isSeparated_isFinitePresentation_of_embedding_of_closedSubspaceLimits`:
  Stacks 0873, given Stacks 0872 and Stacks 0A0U.
* `exists_isLimit_isProper_isFinitePresentation_of_embedding_of_closedSubspaceLimits`:
  Stacks 0A0W, given Stacks 0872 and Stacks 0A0U.

## References

* [Stacks Project, Tag 0873](https://stacks.math.columbia.edu/tag/0873)
* [Stacks Project, Tag 0A0W](https://stacks.math.columbia.edu/tag/0A0W)
* [Stacks Project, Tag 0872](https://stacks.math.columbia.edu/tag/0872)
* [Stacks Project, Tag 0A0U](https://stacks.math.columbia.edu/tag/0A0U)
* [Stacks Project, Tag 086X](https://stacks.math.columbia.edu/tag/086X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `j : X ⟶ Z` be a closed immersion and `g : Z ⟶ Y` a morphism of finite presentation of
algebraic spaces over `S`, with `Y` quasi-compact and quasi-separated and `j ≫ g` separated. Then
`j ≫ g` factors as a closed immersion `X ⟶ X'` followed by a separated morphism of finite
presentation `X' ⟶ Y`. -/
theorem exists_isClosedImmersion_isSeparated_isFinitePresentation_of_comp_of_closedSubspaceLimits
    (h0A0U : ∀ (Y : AlgebraicSpaces B S hS), IsQuasiCompactSpace B S hS Y.1 →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1 →
      ∀ {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS X → ∀ (f : X ⟶ Y.1),
      IsClosedImmersion B S hS f →
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (Z : I → ClosedSubspaces B S hS Y.1) (hZ : ∀ ⦃i j : I⦄, i ≤ j → (Z j).1 ≤ (Z i).1)
        (hle : ∀ i, Subfunctor.range f ≤ (Z i).1),
        (∀ ⦃i j : Iᵒᵖ⦄ (g : i ⟶ j), IsClosedImmersion B S hS
          ((closedSubspaceDiagram B S hS (fun i => (Z i).1) hZ).map g)) ∧
        (∀ i, IsClosedImmersion B S hS (Z i).1.ι ∧ IsFinitePresentation B S hS (Z i).1.ι) ∧
        (∀ i, ((closedSubspaceCone B S hS (fun i => (Z i).1) hZ (Subfunctor.range f)
          hle).extend (Subfunctor.toRange f)).π.app (op i) ≫ (Z i).1.ι = f) ∧
        Nonempty (IsLimit ((closedSubspaceCone B S hS (fun i => (Z i).1) hZ
          (Subfunctor.range f) hle).extend (Subfunctor.toRange f))))
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZsp : IsAlgebraicSpace B S hS Z)
    (j : X ⟶ Z) (g : Z ⟶ Y) (hj : IsClosedImmersion B S hS j)
    (hg : IsFinitePresentation B S hS g) (hsep : IsSeparated B S hS (j ≫ g))
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i : X ⟶ X') (f' : X' ⟶ Y),
      IsAlgebraicSpace B S hS X' ∧ IsClosedImmersion B S hS i ∧ IsSeparated B S hS f' ∧
        IsFinitePresentation B S hS f' ∧ i ≫ f' = j ≫ g := by
  have hZqc : IsQuasiCompactSpace B S hS Z :=
    isQuasiCompactSpace_of_isFinitePresentation B S hS g hY hYqc hg
  have hZqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Z :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hZsp hYqs hg.2.2
  obtain ⟨I, _, _, ⟨i₀⟩, T, hT, hle, hI, hTci, hTfp, hfac, ⟨hlim⟩⟩ :=
    exists_mk_lt_cutoff_isLimit_closedSubspaces B S hS ⟨Z, hZsp⟩ j hj
      (h0A0U ⟨Z, hZsp⟩ hZqc hZqs hX j hj)
  let c := (closedSubspaceCone B S hS (fun i => (T i).1) hT (Subfunctor.range j) hle).extend
    (Subfunctor.toRange j)
  let E := closedSubspaceDiagram B S hS (fun i => (T i).1) hT
  have hstage : ∀ i, IsAlgebraicSpace B S hS (E.obj (op i)) := fun i => (T i).2.1
  let D : DescentSituation B S hS B.contains_terminal I :=
    { system := E
      algebraicSpace := hstage
      transition_affine := fun g => isAffineHom_of_isClosedImmersion B S hS _ (hTci g)
      quasiCompact := fun i => isQuasiCompactSpace_of_isFinitePresentation B S hS (T i).1.ι hZsp
        hZqc (hTfp i).2
      quasiSeparated := fun i => isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS
        B.contains_terminal (hstage i) hZqs (hTfp i).2.2.2
      limitCone := c
      isLimit := hlim
      limitAlgebraicSpace := hX
      base := i₀ }
  let t : D.system ⟶ (Functor.const Iᵒᵖ).obj Y :=
    { app := fun i => (T i.unop).1.ι ≫ g
      naturality := fun a b φ => by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        rw [← Category.assoc]
        change (Subfunctor.homOfLe (hT (leOfHom φ.unop)) ≫ (T b.unop).1.ι) ≫ g = _
        rw [Subfunctor.homOfLe_ι] }
  have ht : ∀ a, D.limitCone.π.app a ≫ t.app a = j ≫ g := fun a => by
    change c.π.app a ≫ (T a.unop).1.ι ≫ g = j ≫ g
    rw [← Category.assoc, hfac a.unop]
  obtain ⟨a, -, ha⟩ := D.exists_isSeparated_system_app_of_isClosedImmersion B S hS
    B.contains_terminal hI hTci hY hYqs t (j ≫ g) ht hsep
  refine ⟨(T a).1.toFunctor, c.π.app (op a), (T a).1.ι ≫ g, hstage a, ?_, ha a le_rfl,
    isFinitePresentation_comp B S hS (hstage a) hZsp hY _ g (hTfp a).2 hg, ?_⟩
  · exact isClosedImmersion_of_comp_mono B S hS _ (T a).1.ι (by rw [hfac a]; exact hj)
  · rw [← Category.assoc, hfac a]

/-- **Stacks 0873, from Stacks 0872 and Stacks 0A0U.** Let `f : X ⟶ Y` be a separated morphism of
finite type of algebraic spaces over `S`, with `Y` quasi-compact and quasi-separated. Then there
are a separated morphism of finite presentation `f' : X' ⟶ Y` and a closed immersion
`i : X ⟶ X'` with `i ≫ f' = f`. -/
theorem
    exists_isClosedImmersion_isSeparated_isFinitePresentation_of_embedding_of_closedSubspaceLimits
    (h0872 : ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS X →
      IsAlgebraicSpace B S hS Y → ∀ (f : X ⟶ Y), IsLocallyOfFiniteType B S hS f →
      IsQuasiCompactSpace B S hS X → IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X →
      IsQuasiCompactSpace B S hS Y → IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i : X ⟶ X') (f' : X' ⟶ Y),
        IsAlgebraicSpace B S hS X' ∧ IsClosedImmersion B S hS i ∧
          IsFinitePresentation B S hS f' ∧ i ≫ f' = f)
    (h0A0U : ∀ (Y : AlgebraicSpaces B S hS), IsQuasiCompactSpace B S hS Y.1 →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1 →
      ∀ {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS X → ∀ (f : X ⟶ Y.1),
      IsClosedImmersion B S hS f →
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (Z : I → ClosedSubspaces B S hS Y.1) (hZ : ∀ ⦃i j : I⦄, i ≤ j → (Z j).1 ≤ (Z i).1)
        (hle : ∀ i, Subfunctor.range f ≤ (Z i).1),
        (∀ ⦃i j : Iᵒᵖ⦄ (g : i ⟶ j), IsClosedImmersion B S hS
          ((closedSubspaceDiagram B S hS (fun i => (Z i).1) hZ).map g)) ∧
        (∀ i, IsClosedImmersion B S hS (Z i).1.ι ∧ IsFinitePresentation B S hS (Z i).1.ι) ∧
        (∀ i, ((closedSubspaceCone B S hS (fun i => (Z i).1) hZ (Subfunctor.range f)
          hle).extend (Subfunctor.toRange f)).π.app (op i) ≫ (Z i).1.ι = f) ∧
        Nonempty (IsLimit ((closedSubspaceCone B S hS (fun i => (Z i).1) hZ
          (Subfunctor.range f) hle).extend (Subfunctor.toRange f))))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hft : IsFiniteType B S hS f)
    (hsep : IsSeparated B S hS f) (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i : X ⟶ X') (f' : X' ⟶ Y),
      IsAlgebraicSpace B S hS X' ∧ IsClosedImmersion B S hS i ∧ IsSeparated B S hS f' ∧
        IsFinitePresentation B S hS f' ∧ i ≫ f' = f := by
  have hXqc : IsQuasiCompactSpace B S hS X :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY hYqc hft.2
  have hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hX hYqs
      (isQuasiSeparated_of_isSeparated B S hS hsep)
  obtain ⟨Z, j, g, hZsp, hj, hg, rfl⟩ := h0872 hX hY f hft.1 hXqc hXqs hYqc hYqs
  exact exists_isClosedImmersion_isSeparated_isFinitePresentation_of_comp_of_closedSubspaceLimits
    B S hS h0A0U hX hY hZsp j g hj hg hsep hYqc hYqs

/-- **Stacks 0A0W, from Stacks 0872 and Stacks 0A0U.** Let `f : X ⟶ Y` be a proper morphism of
algebraic spaces over `S`, with `Y` quasi-compact and quasi-separated. Then `X` is the directed
limit, along closed immersions and over `Y`, of algebraic spaces proper and of finite
presentation over `Y`, the projections from `X` being closed immersions. -/
theorem exists_isLimit_isProper_isFinitePresentation_of_embedding_of_closedSubspaceLimits
    (h0872 : ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS X →
      IsAlgebraicSpace B S hS Y → ∀ (f : X ⟶ Y), IsLocallyOfFiniteType B S hS f →
      IsQuasiCompactSpace B S hS X → IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X →
      IsQuasiCompactSpace B S hS Y → IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i : X ⟶ X') (f' : X' ⟶ Y),
        IsAlgebraicSpace B S hS X' ∧ IsClosedImmersion B S hS i ∧
          IsFinitePresentation B S hS f' ∧ i ≫ f' = f)
    (h0A0U : ∀ (Y : AlgebraicSpaces B S hS), IsQuasiCompactSpace B S hS Y.1 →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1 →
      ∀ {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS X → ∀ (f : X ⟶ Y.1),
      IsClosedImmersion B S hS f →
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (Z : I → ClosedSubspaces B S hS Y.1) (hZ : ∀ ⦃i j : I⦄, i ≤ j → (Z j).1 ≤ (Z i).1)
        (hle : ∀ i, Subfunctor.range f ≤ (Z i).1),
        (∀ ⦃i j : Iᵒᵖ⦄ (g : i ⟶ j), IsClosedImmersion B S hS
          ((closedSubspaceDiagram B S hS (fun i => (Z i).1) hZ).map g)) ∧
        (∀ i, IsClosedImmersion B S hS (Z i).1.ι ∧ IsFinitePresentation B S hS (Z i).1.ι) ∧
        (∀ i, ((closedSubspaceCone B S hS (fun i => (Z i).1) hZ (Subfunctor.range f)
          hle).extend (Subfunctor.toRange f)).π.app (op i) ≫ (Z i).1.ι = f) ∧
        Nonempty (IsLimit ((closedSubspaceCone B S hS (fun i => (Z i).1) hZ
          (Subfunctor.range f) hle).extend (Subfunctor.toRange f))))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsProper B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
      (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
      (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
      (∀ i, IsAlgebraicSpace B S hS (D.obj i)) ∧
      (∀ i, IsProper B S hS (t.app i) ∧ IsFinitePresentation B S hS (t.app i)) ∧
      (∀ ⦃i j : Iᵒᵖ⦄ (e : i ⟶ j), IsClosedImmersion B S hS (D.map e)) ∧
      (∀ i, IsClosedImmersion B S hS (π.app i)) ∧
      π ≫ t = (Functor.const Iᵒᵖ).map f ∧
      Nonempty (IsLimit (Cone.mk X π)) :=
  exists_isLimit_isProper_isFinitePresentation_of_factorization B S hS hX hY f hf hYqc hYqs
    (exists_isClosedImmersion_isSeparated_isFinitePresentation_of_embedding_of_closedSubspaceLimits
      B S hS h0872 h0A0U hX hY f hf.2.1 hf.1 hYqc hYqs) h0A0U

end AlgebraicGeometry.Space

end
