module

public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.HigherVanishing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.ZeroDimensionalTestModules
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Functoriality

/-!
# Degree zero is the only degree in which a zero-dimensionally supported module has cohomology

Let `X` be a locally Noetherian scheme and let `ℱ` be a coherent `𝒪_X`-module whose support has
dimension at most zero. [Stacks, Tag 0B3J] says `Hⁱ(X, ℱ) = 0` for `i > 0`. This file proves the
complementary statement: as soon as the support is nonempty, `H⁰(X, ℱ) ≠ 0`. So the degree
restriction `i > 0` in the source statement is not slack, and the vanishing it asserts is not the
vanishing of `ℱ` itself.

Along the way the global sections are shown to separate such a module from zero: a coherent module
with nonempty zero-dimensional support carries a nonzero *global* section, not merely a nonzero
stalk.

## Main results

* `AlgebraicGeometry.exists_ne_zero_section_of_support_dim_le_zero`: a coherent module whose
  support is nonempty and of dimension at most zero has a nonzero global section.
* `AlgebraicGeometry.not_isZero_hgroup_top_zero_of_support_dim_le_zero`: for such a module
  `H⁰(X, ℱ) ≠ 0`.
* `AlgebraicGeometry.not_isZero_pointTestModule`: `𝒪_X/𝔪_x^t` at a closed point `x` and `t ≠ 0`
  is not the zero module; together with
  `AlgebraicGeometry.isCoherent_pointTestModule` and
  `AlgebraicGeometry.topologicalKrullDim_supp_pointTestModule` this is a module satisfying every
  hypothesis of [Stacks, Tag 0B3J] on a scheme of any dimension.
* `AlgebraicGeometry.isZero_hgroup_top_pointTestModule` and
  `AlgebraicGeometry.not_isZero_hgroup_top_zero_pointTestModule`: the cohomology of that module
  vanishes in every positive degree and does not vanish in degree zero.

## Implementation notes

The nonzero global section is produced from flasqueness rather than from global generation. A
point of the support carries a nonzero germ; the germ comes from a section over some open
neighbourhood (`TopCat.Presheaf.germ_exist`), and
`AlgebraicGeometry.exists_restrict_eq_of_support_dim_le_zero` extends that section to all of `X`
without changing its germ, so the extension is nonzero.

Passing from a nonzero global section to `H⁰(X, ℱ) ≠ 0` uses that `Γ(X, -)` is left exact, so it
agrees with its own zeroth right derived functor
(`CategoryTheory.Functor.rightDerivedZeroIsoSelf`); a zero `H⁰` would force the group of global
sections to be a subsingleton.

None of the statements here is a clause of [Stacks, Tag 0B3J], so none carries its tag: the tag's
two clauses are global generation
(`AlgebraicGeometry.nonempty_generatingSections_of_support_dim_le_zero`) and the vanishing in
positive degrees (`AlgebraicGeometry.isZero_hgroup_top_of_support_dim_le_zero`).

## References

* [Stacks Project, Tag 0B3J](https://stacks.math.columbia.edu/tag/0B3J)
* [Stacks Project, Tag 0FZ9](https://stacks.math.columbia.edu/tag/0FZ9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A coherent module with nonempty zero-dimensional support has a nonzero global section.**
A point of the support has a nonzero germ, that germ is the germ of a section over some open
neighbourhood, and flasqueness extends the section to `X` without altering the germ. -/
theorem exists_ne_zero_section_of_support_dim_le_zero
    {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (hF : topologicalKrullDim (SheafOfModules.supp F) ≤ 0)
    (hne : (SheafOfModules.supp F).Nonempty) :
    ∃ s : F.presheaf.obj (op (⊤ : X.Opens)), s ≠ 0 := by
  obtain ⟨x, a, ha⟩ := hne
  obtain ⟨U, hxU, s, hs⟩ := F.presheaf.exists_germ_eq (x := x) a
  obtain ⟨t, ht⟩ := exists_restrict_eq_of_support_dim_le_zero F hF (le_top (a := U)) s
  refine ⟨t, fun h => ha ?_⟩
  rw [← hs, ← ht, F.presheaf.germ_res_apply, h]
  exact map_zero _

/-- **A nonzero global section obstructs the vanishing of `H⁰`.** Global sections are left exact,
hence agree with their own zeroth right derived functor, so a zero `H⁰(X, ℱ)` would make the
group of global sections a subsingleton. -/
theorem not_isZero_hgroup_top_zero_of_ne_zero_section
    {X : Scheme.{u}} (F : X.Modules) (s : F.presheaf.obj (op (⊤ : X.Opens))) (hs : s ≠ 0) :
    ¬ IsZero (Hgroup X.ringCatSheaf ⊤ 0 F) := by
  intro h
  let RT : RingedSpace.{u} := X.toLocallyRingedSpace.toRingedSpace
  let E := SheafOfModules.evaluation (ringCatSheaf RT) (op (⊤ : X.Opens))
  let G := forget₂ (ModuleCat ((ringCatSheaf RT).obj.obj (op (⊤ : X.Opens)))) AddCommGrpCat
  have : PreservesFiniteLimits (secF X.ringCatSheaf ⊤) := by
    show PreservesFiniteLimits (E ⋙ G)
    infer_instance
  have h' : IsZero (((secF X.ringCatSheaf ⊤).rightDerived 0).obj F) := h
  exact hs ((AddCommGrpCat.subsingleton_of_isZero
    (IsZero.of_iso h' ((secF X.ringCatSheaf ⊤).rightDerivedZeroIsoSelf.app F).symm)).elim s 0)

/-- **The degree restriction in [Stacks, Tag 0B3J] is sharp.** Under the hypotheses of that tag,
and provided the support is nonempty, `H⁰(X, ℱ) ≠ 0`. The tag's vanishing in positive degrees is
therefore not the vanishing of `ℱ`. -/
theorem not_isZero_hgroup_top_zero_of_support_dim_le_zero
    {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (hF : topologicalKrullDim (SheafOfModules.supp F) ≤ 0)
    (hne : (SheafOfModules.supp F).Nonempty) :
    ¬ IsZero (Hgroup X.ringCatSheaf ⊤ 0 F) :=
  let ⟨s, hs⟩ := exists_ne_zero_section_of_support_dim_le_zero F hF hne
  not_isZero_hgroup_top_zero_of_ne_zero_section F s hs

/-! ### `𝒪_X/𝔪_x^t` at a closed point -/

/-- **`𝒪_X/𝔪_x^t` is not the zero module** for `t ≠ 0` and `x` a closed point: its support is
`{x}`, and a zero module has empty support. -/
theorem not_isZero_pointTestModule {X : Scheme.{u}} [IsLocallyNoetherian X] (x : X)
    (hx : IsClosed ({x} : Set X)) {t : ℕ} (ht : t ≠ 0) :
    ¬ IsZero (pointTestModule x t) := fun h =>
  Set.singleton_ne_empty x <|
    (supp_pointTestModule x hx ht).symm.trans (SheafOfModules.supp_eq_empty_of_isZero h)

/-- **[Stacks, Tag 0B3J] applied to `𝒪_X/𝔪_x^t`.** That module is coherent with support `{x}`, so
its cohomology vanishes in every positive degree, on a scheme `X` of any dimension. -/
theorem isZero_hgroup_top_pointTestModule {X : Scheme.{u}} [IsLocallyNoetherian X] (x : X)
    (hx : IsClosed ({x} : Set X)) {t : ℕ} (ht : t ≠ 0) (i : ℕ) (hi : 0 < i) :
    IsZero (Hgroup X.ringCatSheaf ⊤ i (pointTestModule x t)) :=
  have : (pointTestModule x t).IsCoherent := isCoherent_pointTestModule x t
  isZero_hgroup_top_of_support_dim_le_zero (pointTestModule x t)
    (topologicalKrullDim_supp_pointTestModule x hx ht).le i hi

/-- **The cohomology of `𝒪_X/𝔪_x^t` does not vanish in degree zero.** Its support is the nonempty
set `{x}`, so it has a nonzero global section. -/
theorem not_isZero_hgroup_top_zero_pointTestModule {X : Scheme.{u}} [IsLocallyNoetherian X]
    (x : X) (hx : IsClosed ({x} : Set X)) {t : ℕ} (ht : t ≠ 0) :
    ¬ IsZero (Hgroup X.ringCatSheaf ⊤ 0 (pointTestModule x t)) :=
  have : (pointTestModule x t).IsCoherent := isCoherent_pointTestModule x t
  not_isZero_hgroup_top_zero_of_support_dim_le_zero (pointTestModule x t)
    (topologicalKrullDim_supp_pointTestModule x hx ht).le
    ((supp_pointTestModule x hx ht).symm ▸ Set.singleton_nonempty x)

end AlgebraicGeometry

end
