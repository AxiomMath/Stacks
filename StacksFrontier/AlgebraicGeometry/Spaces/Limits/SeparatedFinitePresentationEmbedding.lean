module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedSubspaceApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# Embedding a separated finite type algebraic space in a separated one of finite presentation

Let `f : X ⟶ Y` be a separated morphism of finite type of algebraic spaces over `S`, with `Y`
quasi-compact and quasi-separated. Stacks 0873 produces a separated morphism of finite
presentation `f' : X' ⟶ Y` and a closed immersion `X ⟶ X'` over `Y`. This file carries out the
proof of the source from three inputs of other parts of the project, each taken as an explicit
hypothesis in the exact form of the corresponding result:

* `h0872`: Stacks 0872, a locally finite type morphism of quasi-compact quasi-separated
  algebraic spaces factors as a closed immersion followed by a morphism of finite presentation;
* `h0A0U`: Stacks 0A0U, a closed subspace of a quasi-compact quasi-separated algebraic space is
  the directed inverse limit of closed subspaces of finite presentation (the form of
  `AlgebraicGeometry.Space.exists_isLimit_closedSubspaces_of_isClosedImmersion`);
* `h086X`: Stacks 086X for an inverse system with monomorphic transition morphisms, with no
  bound on the index (the form of
  `AlgebraicGeometry.Space.DescentSituation.exists_isSeparated_system_app_of_isSiteSmall`
  for a system which is small for the site by monomorphy).

None of the three declarations carries the tag; the tagged statement is the instantiation of
`exists_isClosedImmersion_isSeparated_isFinitePresentation_of_approximations` at the three
results once they are available unconditionally.

## Main results

All names are in the namespace `AlgebraicGeometry.Space`.

* `exists_isClosedImmersion_isSeparated_isFinitePresentation_of_comp`:
  the second half of the proof of Stacks 0873. A separated composite `j ≫ g` of a closed
  immersion `j : X ⟶ Z` and a morphism of finite presentation `g : Z ⟶ Y`, with `Y`
  quasi-compact and quasi-separated, factors as a closed immersion followed by a separated
  morphism of finite presentation, the intermediate space being a closed subspace of `Z`.
* `exists_isClosedImmersion_isSeparated_isFinitePresentation_of_approximations`:
  the full statement of Stacks 0873 from the three inputs.

## Implementation notes

The source writes the ideal sheaf of `X` in `Z` as the directed colimit of its finite type
quasi-coherent subsheaves (Stacks 0829) and takes the closed subspaces `X_a ⊆ Z` they cut out;
that construction is exactly Stacks 0A0U for the closed immersion `X ⟶ Z`, which is the form
used here. The stages are closed subspaces of `Z`, so the transition morphisms are closed
immersions, hence affine and monomorphisms. Monomorphy is what makes Stacks 086X available
whatever the size of the index: the index of Stacks 0A0U is the set of finite families of
finite type ideals on a chart of `Z`, which in general is not smaller than the cofinality of
the cutoff of the site (`AlgebraicGeometry.BigFppfSite` only asks the cutoff to be a strong
limit cardinal of uncountable cofinality), so the bounded form
`AlgebraicGeometry.Space.DescentSituation.exists_isSeparated_system_app` does not apply.

## References

* [Stacks Project, Tag 0873](https://stacks.math.columbia.edu/tag/0873)
* [Stacks Project, Tag 0872](https://stacks.math.columbia.edu/tag/0872)
* [Stacks Project, Tag 0A0U](https://stacks.math.columbia.edu/tag/0A0U)
* [Stacks Project, Tag 086X](https://stacks.math.columbia.edu/tag/086X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The second half of the proof of Stacks 0873.** Let `j : X ⟶ Z` be a closed immersion and
`g : Z ⟶ Y` a morphism of finite presentation of algebraic spaces over `S`, with `Y`
quasi-compact and quasi-separated and `j ≫ g` separated. Then `j ≫ g` factors as a closed
immersion `X ⟶ X'` followed by a separated morphism of finite presentation `X' ⟶ Y`.

Stacks 0A0U (`h0A0U`) writes `X` as the directed limit of closed subspaces `X_a ⊆ Z` of finite
presentation over `Z`; these are quasi-compact and quasi-separated because `Z` is, and their
transition morphisms are closed immersions, hence affine monomorphisms. Each `X_a ⟶ Y` is of
finite presentation as a composite of two such morphisms, and Stacks 086X for a monomorphic
system (`h086X`) makes it separated for `a` large enough, `X ⟶ Y` being separated. -/
theorem exists_isClosedImmersion_isSeparated_isFinitePresentation_of_comp
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
    (h086X : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      (∀ ⦃i j : Iᵒᵖ⦄ (g : i ⟶ j), Mono (D.system.map g)) →
      ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS Y →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      ∀ (t : D.system ⟶ (Functor.const Iᵒᵖ).obj Y) (f : D.limitCone.pt ⟶ Y),
      (∀ j, D.limitCone.π.app j ≫ t.app j = f) → IsSeparated B S hS f →
      ∃ i, D.base ≤ i ∧ ∀ k, i ≤ k → IsSeparated B S hS (t.app (op k)))
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
  obtain ⟨I, _, _, ⟨i₀⟩, T, hT, hle, hTci, hTfp, hfac, ⟨hlim⟩⟩ :=
    h0A0U ⟨Z, hZsp⟩ hZqc hZqs hX j hj
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
  have hmono : ∀ ⦃a b : Iᵒᵖ⦄ (φ : a ⟶ b), Mono (D.system.map φ) := fun a b φ =>
    mono_of_isClosedImmersion B S hS _ (hTci φ)
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
  obtain ⟨a, -, ha⟩ := h086X D hmono hY hYqs t (j ≫ g) ht hsep
  refine ⟨(T a).1.toFunctor, c.π.app (op a), (T a).1.ι ≫ g, hstage a, ?_, ha a le_rfl,
    isFinitePresentation_comp B S hS (hstage a) hZsp hY _ g (hTfp a).2 hg, ?_⟩
  · exact isClosedImmersion_of_comp_mono B S hS _ (T a).1.ι (by rw [hfac a]; exact hj)
  · rw [← Category.assoc, hfac a]

/-- **Stacks 0873, from Stacks 0872, Stacks 0A0U and Stacks 086X.** Let `f : X ⟶ Y` be a
separated morphism of finite type of algebraic spaces over `S`, with `Y` quasi-compact and
quasi-separated. Then there are a separated morphism of finite presentation `f' : X' ⟶ Y` and a
closed immersion `i : X ⟶ X'` with `i ≫ f' = f`.

`X` is quasi-compact, `f` being quasi-compact, and quasi-separated, `f` being separated. So
Stacks 0872 (`h0872`) gives a closed immersion `X ⟶ Z` with `Z ⟶ Y` of finite presentation,
and `exists_isClosedImmersion_isSeparated_isFinitePresentation_of_comp` replaces `Z` by a
closed subspace separated over `Y`. -/
theorem exists_isClosedImmersion_isSeparated_isFinitePresentation_of_approximations
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
    (h086X : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      (∀ ⦃i j : Iᵒᵖ⦄ (g : i ⟶ j), Mono (D.system.map g)) →
      ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS Y →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      ∀ (t : D.system ⟶ (Functor.const Iᵒᵖ).obj Y) (f : D.limitCone.pt ⟶ Y),
      (∀ j, D.limitCone.π.app j ≫ t.app j = f) → IsSeparated B S hS f →
      ∃ i, D.base ≤ i ∧ ∀ k, i ≤ k → IsSeparated B S hS (t.app (op k)))
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
  exact exists_isClosedImmersion_isSeparated_isFinitePresentation_of_comp B S hS h0A0U h086X
    hX hY hZsp j g hj hg hsep hYqc hYqs

end AlgebraicGeometry.Space

end
