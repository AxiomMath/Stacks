module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.DescendUnconditional
public import StacksFrontier.AlgebraicGeometry.Cohomology.ColimitsQuasiCompact.SectionsColimit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Properties.QuasicoherentAlgebra
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Sections of a colimit of module sheaves over a quasi-compact open

A filtered colimit of sheaves of modules on a scheme is computed on sections over a
quasi-compact open: every section of the colimit comes from a stage, and two sections of a
stage with the same image in the colimit already agree at a later stage. Combined with
[Stacks, Tag 01PK] this makes the presentation of a quasi-coherent module as a directed colimit
of modules of finite presentation *usable on sections*, which is how a construction gets hold of
a finitely presented approximation of a prescribed local section.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.hasBasisOfCompactOpens_scheme` and
  `interCompactOpenIsCompact_of_quasiSeparatedSpace`: hypotheses (H1) and (H2) of
  [Stacks, Tag 0069] hold on a scheme, resp. on a quasi-separated scheme.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_section_of_isColimit`: **a section of the vertex
  of a colimiting cocone of module sheaves over a quasi-compact open comes from a stage.**
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_map_eq_of_isColimit`: **two sections of a stage
  with the same image in the vertex agree after a map of the index category.**
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_directed_system_sections`:
  **[Stacks, Tag 01PK] with its colimit read on sections** — a quasi-coherent module on a
  quasi-compact quasi-separated scheme is the colimit of a directed system of modules of finite
  presentation which is jointly surjective, and eventually injective, on sections over every
  quasi-compact open.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_hom_section`: the form a
  construction consumes — for a prescribed section of a quasi-coherent module over a
  quasi-compact open there are a quasi-coherent module of finite presentation, a map to the given
  module, and a section of it hitting the prescribed one.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_hom_section_algebra`: the
  same for the underlying module of a quasi-coherent algebra, which is the input to the
  symmetric-algebra step of [Stacks, Tag 05JS].

## Implementation notes

The content is [Stacks, Tag 009F] for sheaves of modules, which is proved as
`Stacks.Cohomology.CompactSections.preservesColimitsOfShape_secF` under the two hypotheses
(H1) and (H2) of [Stacks, Tag 0069] on the underlying space. Both hold on a scheme — (H1)
because the affine opens form a basis and are quasi-compact, (H2) because a quasi-separated
space has quasi-compact binary intersections of quasi-compact opens — and the two lemmas
discharging them were previously available only as `private` declarations inside
`StacksFrontier.AlgebraicGeometry.Cohomology.ColimitsHigherDirect.HigherDirectImage`, so they are
restated here.

`Stacks.Cohomology.CompactSections.secF` is the composite of the underlying-abelian-sheaf
functor with evaluation at the open, so its value on a module sheaf is the group of sections of
that sheaf, and `CategoryTheory.Limits.Concrete.isColimit_exists_rep` and
`...Concrete.isColimit_exists_of_rep_eq` read the preserved colimit on elements. No
identification has to be transported: `Γ(M, W)` *is* the carrier of `(secF R W).obj M`, and the
component of the mapped cocone *is* the map on sections, both by definition. In particular the
`AlgebraicGeometry.Scheme.Modules`/`SheafOfModules X.ringCatSheaf` distinction costs nothing
here, the two categories being the same by definition.

The index of [Stacks, Tag 01PK] is a nonempty directed partial order, so its homs are
proof-carrying and a hom `i ⟶ k` produced by the elementwise criterion is the one coming from
`i ≤ k`; that is why `exists_directed_system_sections` can state eventual injectivity in the
order-theoretic form, with `CategoryTheory.homOfLE`, which is what the colimit criteria for
algebra sheaves consume.

## References

* [Stacks Project, Tag 01PK](https://stacks.math.columbia.edu/tag/01PK)
* [Stacks Project, Tag 009F](https://stacks.math.columbia.edu/tag/009F)
* [Stacks Project, Tag 0069](https://stacks.math.columbia.edu/tag/0069)
* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-! ### The two hypotheses of [Stacks, Tag 0069] on a scheme -/

/-- **Hypothesis (H1) of [Stacks, Tag 0069] on a scheme**, i.e. `PrespectralSpace`: the
quasi-compact opens form a basis of the topology, since the affine opens do and an affine open is
quasi-compact. -/
theorem hasBasisOfCompactOpens_scheme (X : Scheme.{u}) : PrespectralSpace ↥X := by
  refine PrespectralSpace.of_isTopologicalBasis (B := (↑) '' X.affineOpens) ?_ ?_
  · exact X.isBasis_affineOpens
  · rintro _ ⟨U, hU, rfl⟩
    exact hU.isCompact

/-- **Hypothesis (H2) of [Stacks, Tag 0069] on a quasi-separated space**, i.e.
`QuasiSeparatedSpace`: the intersection of two quasi-compact opens is quasi-compact. -/
theorem interCompactOpenIsCompact_of_quasiSeparatedSpace (T : Type u) [TopologicalSpace T]
    [QuasiSeparatedSpace T] : QuasiSeparatedSpace T :=
  ⟨fun _ _ hUopen hUcompact hVopen hVcompact =>
    hUcompact.inter_of_isOpen hVcompact hUopen hVopen⟩

/-! ### [Stacks, Tag 009F] for sheaves of modules on a scheme, on elements -/

variable {X : Scheme.{u}}

/-- The cocone on sections over a quasi-compact open of a colimit cocone of `𝒪_X`-modules is
again a colimit cocone. -/
private theorem nonempty_isColimit_mapCocone_secF [QuasiSeparatedSpace ↥X]
    {I : Type u} [SmallCategory I] [IsFiltered I] {D : I ⥤ X.Modules} {c : Cocone D}
    (hc : IsColimit c) (W : X.Opens) (hW : IsCompact (W : Set ↥X)) :
    Nonempty (IsColimit ((secF.{u, u, u} X.ringCatSheaf W).mapCocone c)) :=
  (Stacks.Cohomology.CompactSections.preservesColimitsOfShape_secF (Idx := I) X.ringCatSheaf
    (hasBasisOfCompactOpens_scheme X)
    (interCompactOpenIsCompact_of_quasiSeparatedSpace ↥X) W hW).preservesColimit.preserves hc

/-- **A section of the vertex of a colimiting cocone of `𝒪_X`-modules over a quasi-compact open
comes from a stage.**

This is [Stacks, Tag 009F] for sheaves of modules, read on elements. No quasi-compactness of `X`
itself is used: only that `W` is quasi-compact and that `X` is quasi-separated, the latter
through hypothesis (H2) of [Stacks, Tag 0069]. -/
theorem exists_section_of_isColimit [QuasiSeparatedSpace ↥X]
    {I : Type u} [SmallCategory I] [IsFiltered I] {D : I ⥤ X.Modules} {c : Cocone D}
    (hc : IsColimit c) (W : X.Opens) (hW : IsCompact (W : Set ↥X)) (s : Γ(c.pt, W)) :
    ∃ (i : I) (t : Γ(D.obj i, W)), (c.ι.app i).app W t = s := by
  obtain ⟨hcol⟩ := nonempty_isColimit_mapCocone_secF hc W hW
  exact Concrete.isColimit_exists_rep (D ⋙ secF.{u, u, u} X.ringCatSheaf W) hcol s

/-- **Two sections of a stage with the same image in the vertex of a colimiting cocone of
`𝒪_X`-modules agree after a map of the index category.**

This is the injectivity half of [Stacks, Tag 009F] for sheaves of modules, read on elements. -/
theorem exists_map_eq_of_isColimit [QuasiSeparatedSpace ↥X]
    {I : Type u} [SmallCategory I] [IsFiltered I] {D : I ⥤ X.Modules} {c : Cocone D}
    (hc : IsColimit c) (W : X.Opens) (hW : IsCompact (W : Set ↥X)) {i j : I}
    (t : Γ(D.obj i, W)) (t' : Γ(D.obj j, W))
    (h : (c.ι.app i).app W t = (c.ι.app j).app W t') :
    ∃ (k : I) (f : i ⟶ k) (g : j ⟶ k), (D.map f).app W t = (D.map g).app W t' := by
  obtain ⟨hcol⟩ := nonempty_isColimit_mapCocone_secF hc W hW
  exact Concrete.isColimit_exists_of_rep_eq (D ⋙ secF.{u, u, u} X.ringCatSheaf W) hcol t t' h

/-! ### [Stacks, Tag 01PK] with its colimit read on sections -/

/-- **[Stacks, Tag 01PK], with the colimit read on sections over the quasi-compact opens.**

A quasi-coherent `𝒪_X`-module on a quasi-compact and quasi-separated scheme is the colimit of a
directed system of `𝒪_X`-modules of finite presentation, and over every quasi-compact open the
sections of the system exhaust those of the module and separate no more than the module does:
every section of `F` over such an open comes from a member of the system, and two sections of a
member with the same image in `F` agree at a later index.

The colimit clause alone is `exists_directed_system_of_isFinitePresentation`; the two sectionwise
clauses are [Stacks, Tag 009F] for sheaves of modules applied to it.

No `@[stacks]` attribute is attached. [Stacks, Tag 01PK] is closed and tagged at
`AlgebraicGeometry.exists_directed_system_of_isFinitePresentation`, and what
this adds over it is [Stacks, Tag 009F] content, which is itself already tagged in
`StacksFrontier.Topology.Sheaves.Limits.FilteredColimitSections`. -/
theorem exists_directed_system_sections
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ (I : Type u) (_ : PartialOrder I) (_ : Nonempty I)
      (_ : IsDirected I (· ≤ ·)) (D : I ⥤ X.Modules)
      (φ : D ⟶ (Functor.const I).obj F),
      (∀ i, (D.obj i).IsFinitePresentation) ∧
        Nonempty (IsColimit (Cocone.mk F φ)) ∧
        (∀ W : X.Opens, IsCompact (W : Set ↥X) → ∀ s : Γ(F, W),
          ∃ (i : I) (t : Γ(D.obj i, W)), (φ.app i).app W t = s) ∧
        (∀ W : X.Opens, IsCompact (W : Set ↥X) → ∀ (i : I) (t t' : Γ(D.obj i, W)),
          (φ.app i).app W t = (φ.app i).app W t' →
            ∃ (j : I) (hij : i ≤ j),
              (D.map (homOfLE hij)).app W t = (D.map (homOfLE hij)).app W t') := by
  obtain ⟨I, _, _, _, D, φ, hfp, ⟨hc⟩⟩ :=
    _root_.AlgebraicGeometry.exists_directed_system_of_isFinitePresentation X F
  refine ⟨I, inferInstance, inferInstance, inferInstance, D, φ, hfp, ⟨hc⟩,
    fun W hW s => exists_section_of_isColimit hc W hW s, fun W hW i t t' h => ?_⟩
  obtain ⟨k, f, g, hfg⟩ := exists_map_eq_of_isColimit hc W hW t t' h
  obtain rfl : f = g := Subsingleton.elim _ _
  exact ⟨k, leOfHom f, hfg⟩

/-! ### The form a construction consumes -/

/-- **A section of a quasi-coherent module over a quasi-compact open is hit by a quasi-coherent
module of finite presentation mapping to it.**

This is the input to the symmetric-algebra step of [Stacks, Tag 05JS]: there, a section of a
quasi-coherent algebra `𝒜` over an affine open has to be realised in `Sym(ℱ)` for a quasi-coherent
`ℱ` of finite presentation mapping to `𝒜`, and `ℱ` is produced here. -/
theorem exists_isFinitePresentation_hom_section
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent]
    (W : X.Opens) (hW : IsCompact (W : Set ↥X)) (s : Γ(F, W)) :
    ∃ (G : X.Modules) (_ : G.IsFinitePresentation) (_ : G.IsQuasicoherent) (ψ : G ⟶ F)
      (t : Γ(G, W)), ψ.app W t = s := by
  obtain ⟨I, _, _, _, D, φ, hfp, -, hsurj, -⟩ := exists_directed_system_sections X F
  obtain ⟨i, t, ht⟩ := hsurj W hW s
  exact ⟨D.obj i, hfp i, _root_.isQuasicoherent_of_isFinitePresentation _, φ.app i, t, ht⟩

/-- **The same for the underlying module of a quasi-coherent algebra.**

Let `𝒜` be a quasi-coherent sheaf of commutative `𝒪_X`-algebras on a quasi-compact and
quasi-separated scheme and `a` a section of `𝒜` over a quasi-compact open. Then there are a
quasi-coherent `𝒪_X`-module `ℱ` of finite presentation, a morphism of `𝒪_X`-modules
`ℱ ⟶ 𝒜`, and a section of `ℱ` mapping to `a`.

This is the first step of the proof of [Stacks, Tag 05JS], which continues by passing to
`Sym(ℱ)`; the symmetric algebra of a quasi-coherent module is **not** available in this library
as a quasi-coherent algebra of finite presentation, so no part of [Stacks, Tag 05JS] is claimed
here and no attribute for it is attached. -/
theorem exists_isFinitePresentation_hom_section_algebra
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (A : X.QuasicoherentAlgebra) (hA : Scheme.QuasicoherentAlgebra.IsQuasicoherent A)
    (W : X.Opens) (hW : IsCompact (W : Set ↥X))
    (a : Γ(Scheme.QuasicoherentAlgebra.underlyingModule A, W)) :
    ∃ (G : X.Modules) (_ : G.IsFinitePresentation) (_ : G.IsQuasicoherent)
      (ψ : G ⟶ Scheme.QuasicoherentAlgebra.underlyingModule A) (t : Γ(G, W)),
      ψ.app W t = a :=
  let := hA
  exists_isFinitePresentation_hom_section X _ W hW a

end Stacks.AlgebraicGeometry.ModuleLimits

end
