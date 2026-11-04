module

public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmooth

/-!
# Finite presentation of the sections of `a^*Ω_{X/S}`, and standard coverings of an affine scheme

This file collects the two remaining algebraic inputs of the correction step (II) of
[Stacks Project, Tag 02H6].

The first is finite presentation. For `a : T ⟶ X` a morphism from an affine scheme mapping into an
affine open `W` of `X` lying over an affine open `V` of `S`, the affine computation
`Stacks.Smooth.cotangentComparisonEquiv` identifies `Γ(a^*Ω_{X/S}, ⊤)` with
`Γ(T, ⊤) ⊗[Γ(X, W)] Ω[Γ(X, W)⁄Γ(S, V)]`. If `f` is locally of finite presentation then
`Γ(X, W)` is a finitely presented `Γ(S, V)`-algebra, so `Ω[Γ(X, W)⁄Γ(S, V)]` is a finitely
presented `Γ(X, W)`-module and the base change is a finitely presented `Γ(T, ⊤)`-module. Finite
presentation is what makes `Module.FinitePresentation.isLocalizedModule_map` available, i.e. what
turns the local differences of two lifts into a Čech cochain.

The second is the translation between coverings of an affine scheme by basic opens and families
of sections generating the unit ideal, in the indexed and finite form that the Čech argument
needs, together with the refinement of `Stacks.Smooth.exists_isAffineOpen_lift` to such a
covering.

## Main results

* `Stacks.Smooth.finitePresentation_pullbackCotangentSheaf`:
  `Module.FinitePresentation Γ(T, ⊤) Γ(a^*Ω_{X/S}, ⊤)`, assuming the comparison hypotheses of
  `Stacks.Smooth.cotangentComparisonEquiv` and finite presentation of `f.appLE V W`.
* `Stacks.Smooth.finitePresentation_pullbackCotangentSheaf_of_locallyOfFinitePresentation`: the
  same, with the hypothesis on `f.appLE V W` replaced by
  `AlgebraicGeometry.LocallyOfFinitePresentation f`.
* `Stacks.Smooth.iSup_basicOpen_eq_top_iff_span_range_eq_top`: an indexed family of global
  sections of an affine scheme has basic opens covering the scheme if and only if it generates
  the unit ideal.
* `Stacks.Smooth.exists_finset_basicOpen_le`: a family of opens of an affine scheme with
  `t ∈ U t` for every point `t` can be shrunk to basic opens, finitely many of which already
  generate the unit ideal.
* `Stacks.Smooth.exists_finset_basicOpen_lift`: the combination with
  `Stacks.Smooth.exists_isAffineOpen_lift` — for `f` smooth and `T'` affine, the local solutions
  of the lifting problem may be taken over *basic* opens of `T'`, finitely many of which
  correspond to sections generating the unit ideal of `Γ(T', ⊤)`.

## Implementation notes

The covering translation is Mathlib's `AlgebraicGeometry.IsAffineOpen.iSup_basicOpen_eq_self_iff`
specialized to the affine open `⊤`; the only work is the passage from a supremum over a subtype
of a set to a supremum over an index type, which is `iSup_range'`. The finite subcover comes from
`TopologicalSpace.IsOpenCover.exists_finite_of_compactSpace`, the scheme being affine and hence
quasi-compact.

The refinement of the local lifts is immediate from
`Stacks.Smooth.morphismRestrict_comp_homOfLE`: a solution over an open restricts to a solution
over any smaller open, and the shrinking only needs that each affine open produced by
`Stacks.Smooth.exists_isAffineOpen_lift` contains the point it was produced for.

Note that no affineness hypothesis is needed on the basic opens produced: a basic open of an
affine scheme is automatically affine (`AlgebraicGeometry.IsAffineOpen.basicOpen`), and
`Stacks.Smooth.isLocalizedModule_restrictₗ_pullbackCotangentSheaf` is stated for all of them at
once.

## References

* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct

universe u

namespace Stacks.Smooth

/-! ### Finite presentation of the global sections -/

variable {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) {V : S.Opens} {W : X.Opens}

/-- **The global sections of `a^*Ω_{X/S}` are a finitely presented module.** Let `f : X ⟶ S` be a
morphism of schemes, let `V` be an affine open of `S` and `W` an affine open of `X` with
`W ≤ f ⁻¹ᵁ V` such that `Γ(S, V) ⟶ Γ(X, W)` is of finite presentation, and let `a : T ⟶ X` be a
morphism from an affine scheme `T` mapping into `W`. Then `Γ(a^*Ω_{X/S}, ⊤)` is a finitely
presented `Γ(T, ⊤)`-module.

By `Stacks.Smooth.cotangentComparisonEquiv` it is `Γ(T, ⊤) ⊗[Γ(X, W)] Ω[Γ(X, W)⁄Γ(S, V)]`, and
`Ω[Γ(X, W)⁄Γ(S, V)]` is a finitely presented `Γ(X, W)`-module because `Γ(X, W)` is a finitely
presented `Γ(S, V)`-algebra. -/
theorem finitePresentation_pullbackCotangentSheaf [IsAffine T] (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V) (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W)
    (hfp : (f.appLE V W hWV).hom.FinitePresentation) :
    Module.FinitePresentation Γ(T, ⊤) Γ(pullbackCotangentSheaf f a, (⊤ : T.Opens)) := by
  let := algebraAppLE f hWV
  let := algebraAppLE a hUW
  have halg : Algebra.FinitePresentation Γ(S, V) Γ(X, W) := hfp
  have hbase : Module.FinitePresentation Γ(T, ⊤) (Γ(T, ⊤) ⊗[Γ(X, W)] Ω[Γ(X, W)⁄Γ(S, V)]) :=
    inferInstance
  exact (LinearEquiv.finitePresentation_iff (cotangentComparisonEquiv f a hV hW hWV hUW)).mp hbase

/-- **The global sections of `a^*Ω_{X/S}` are a finitely presented module**, for `f` locally of
finite presentation. This is
`Stacks.Smooth.finitePresentation_pullbackCotangentSheaf` with the hypothesis on `f.appLE V W`
supplied by `AlgebraicGeometry.LocallyOfFinitePresentation.finitePresentation_appLE`. -/
theorem finitePresentation_pullbackCotangentSheaf_of_locallyOfFinitePresentation [IsAffine T]
    [LocallyOfFinitePresentation f] (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hWV : W ≤ f ⁻¹ᵁ V) (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) :
    Module.FinitePresentation Γ(T, ⊤) Γ(pullbackCotangentSheaf f a, (⊤ : T.Opens)) :=
  finitePresentation_pullbackCotangentSheaf f a hV hW hWV hUW
    (f.finitePresentation_appLE hV hW hWV)

/-! ### Standard coverings of an affine scheme -/

/-- **A family of basic opens covers an affine scheme if and only if the sections generate the
unit ideal.** This is `AlgebraicGeometry.IsAffineOpen.iSup_basicOpen_eq_self_iff` for the affine
open `⊤`, restated for an indexed family rather than a set of sections. -/
theorem iSup_basicOpen_eq_top_iff_span_range_eq_top {T : Scheme.{u}} [IsAffine T] {ι : Type*}
    (g : ι → Γ(T, ⊤)) : (⨆ j, T.basicOpen (g j)) = ⊤ ↔ Ideal.span (Set.range g) = ⊤ := by
  rw [← (isAffineOpen_top T).iSup_basicOpen_eq_self_iff, iSup_range']

/-- **Shrinking a pointwise cover of an affine scheme to finitely many basic opens.** Let `T` be
an affine scheme and let `U` assign to every point `t` of `T` an open containing `t`. Then there
are sections `g t` of `𝒪_T` with `T.basicOpen (g t) ≤ U t` for every `t`, and a *finite* set `s`
of points such that the `g t` for `t ∈ s` already generate the unit ideal of `Γ(T, ⊤)` — that is,
such that the basic opens `T.basicOpen (g t)` for `t ∈ s` already cover `T`.

The sections are produced by `AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le` and the finite
subfamily by quasi-compactness of `T`. -/
theorem exists_finset_basicOpen_le {T : Scheme.{u}} [IsAffine T] (U : ↥T → T.Opens)
    (hU : ∀ t, t ∈ U t) :
    ∃ (g : ↥T → Γ(T, ⊤)) (s : Finset ↥T),
      (∀ t, T.basicOpen (g t) ≤ U t) ∧ Ideal.span (Set.range fun t : s ↦ g t) = ⊤ := by
  have hbas : ∀ t : ↥T, ∃ g : Γ(T, ⊤), T.basicOpen g ≤ U t ∧ t ∈ T.basicOpen g := fun t ↦
    (isAffineOpen_top T).exists_basicOpen_le (V := U t) ⟨t, hU t⟩ trivial
  choose g hg₁ hg₂ using hbas
  have hcov : TopologicalSpace.IsOpenCover (fun t : ↥T ↦ T.basicOpen (g t)) :=
    top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hg₂ x⟩
  obtain ⟨s, hs⟩ := hcov.exists_finite_of_compactSpace
  exact ⟨g, s, hg₁, (iSup_basicOpen_eq_top_iff_span_range_eq_top _).mp hs.iSup_eq_top⟩

/-- **The local lifts may be taken over basic opens, finitely many of which generate the unit
ideal.** Let `f : X ⟶ S` be smooth, let `i : T ⟶ T'` be a first-order thickening with `T'`
affine, and let `a : T ⟶ X` and `h : T' ⟶ S` present a lifting problem. Then there are sections
`g t` of `𝒪_{T'}` and a finite set `s` of points of `T'` with the `g t` for `t ∈ s` generating
the unit ideal of `Γ(T', ⊤)`, such that the lifting problem has a solution over
`T'.basicOpen (g t)` for **every** point `t`.

This is `Stacks.Smooth.exists_isAffineOpen_lift` refined by
`Stacks.Smooth.exists_finset_basicOpen_le`; the solutions restrict along
`Stacks.Smooth.morphismRestrict_comp_homOfLE`. It is the form of step (I) of the proof of
[Stacks Project, Tag 02H6] that the Čech argument of step (II) consumes, the covering being the
standard covering attached to a family of sections generating the unit ideal. -/
theorem exists_finset_basicOpen_lift {X S T T' : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.Smooth f] [IsAffine T'] {i : T ⟶ T'}
    (hi : Thickenings.IsFirstOrderThickening i) (a : T ⟶ X) (h : T' ⟶ S)
    (hcomm : a ≫ f = i ≫ h) :
    ∃ (g : ↥T' → Γ(T', ⊤)) (s : Finset ↥T'), Ideal.span (Set.range fun t : s ↦ g t) = ⊤ ∧
      ∀ t : ↥T', ∃ b : (T'.basicOpen (g t) : Scheme.{u}) ⟶ X,
        b ≫ f = (T'.basicOpen (g t)).ι ≫ h ∧
        (i ∣_ T'.basicOpen (g t)) ≫ b = (i ⁻¹ᵁ T'.basicOpen (g t)).ι ≫ a := by
  choose V' _ htV' b hbf hba using exists_isAffineOpen_lift f hi a h hcomm
  obtain ⟨g, s, hg, hspan⟩ := exists_finset_basicOpen_le V' htV'
  refine ⟨g, s, hspan, fun t ↦ ⟨T'.homOfLE (hg t) ≫ b t, ?_, ?_⟩⟩
  · rw [Category.assoc, hbf t, ← Category.assoc, Scheme.homOfLE_ι]
  · rw [← Category.assoc, morphismRestrict_comp_homOfLE, Category.assoc, hba t, ← Category.assoc,
      Scheme.homOfLE_ι]

end Stacks.Smooth

end
