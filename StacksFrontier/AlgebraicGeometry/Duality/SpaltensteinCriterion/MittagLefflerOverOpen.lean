module

public import StacksFrontier.AlgebraicGeometry.Duality.SpaltensteinCriterion.DerivedSectionsLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MonoHomologyProjection

/-!
# The Mittag-Leffler injectivity criterion over an open of a ringed space

Let `(X, 𝒪_X)` be a ringed space, let `U ⊆ X` be open and let `(Kₙ)` be an inverse system in
the unbounded derived category `D(𝒪_X)` with derived limit `L`, presented by its defining
distinguished triangle.  Fix a degree `m` and an index `n₀`.  If

* `R¹\lim Hᵐ⁻¹(U, Kₙ)` vanishes, and
* `Hᵐ(U, Kₙ) ⟶ Hᵐ(U, K_{n₀})` is injective for every `n ≥ n₀`,

then `Hᵐ(U, L) ⟶ Hᵐ(U, K_{n₀})` is injective.

This is the cohomology-over-an-open half of Stacks 0D61, and it is the direct ringed-space
counterpart of `mono_cohomologyPresheaf_projection_of_eventually_iso` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedLimit/SectionsInjectivityOverAnObject.lean`,
which does the same thing over an object of a ringed site.  The proof is two lines of the Milnor
short exact sequence of Stacks 0D60: with
`R¹\lim` vanishing the sequence exhibits `Hᵐ(U, L) ⟶ \lim Hᵐ(U, Kₙ)` as an isomorphism, hence a
monomorphism, and the limit projection at `n₀` is a monomorphism because the transition maps
beyond `n₀` are.

## Main results

* `Stacks.Cohomology.DerivedLimitMittagLeffler.mono_cohomology_derivedLimit_projection` — the
  statement above, in the categorical `Mono` form.
* `Stacks.Cohomology.DerivedLimitMittagLeffler.injective_cohomology_derivedLimit_projection` —
  the same in the `Function.Injective` form, which is the form the statement of Stacks 0D61
  takes.

## Implementation notes

**This file proves only the cohomology-over-an-open half of Stacks 0D61**, which is why no tag
attribute is placed here.  Stacks 0D61 concludes injectivity on the *stalk* at a point `x` of
the map of cohomology sheaves `Hᵐ(L) ⟶ Hᵐ(K_{n₀})`, given the hypotheses below on a fundamental
system of neighbourhoods of `x`; the statement over a single open, proved here, is the input to
that passage.  The stalk statement, at a *free* `HasDerivedCategory` instance as here, is
`Stacks.Cohomology.DerivedLimitStalk.cohomology_derivedLimit_projection_mono_on_stalk` in
`StacksFrontier/Topology/Sheaves/Cohomology/MayerVietorisAndLimits/DerivedLimitStalkInjectivity.lean`,
which carries `@[stacks 0D61]`.

Passing from cohomology over the opens of a fundamental system to the stalk of the cohomology
sheaf is the ringed-space form of Stacks 0BKJ, namely
`Stacks.Cohomology.CohomologyPresheaf.sheafificationCohomologyPresheafIso` in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedCategory/CohomologyPresheafSheafification.lean`.
That declaration does **not** bake `HasDerivedCategory.standard` into its type: its file installs
no model as a file-level instance, and takes each of the three derived categories occurring in it
at an independently chosen instance, deliberately — as its own implementation notes record — so
that a consumer working at the locally small model of Tag 079Q can use it.

Derived sections are not constructed: as in `DerivedSectionsLimit.lean` they are taken as an
arbitrary total right derived functor `RΓ(U, -)` of the sections functor over `U`, presented by
its complex-level comparison map, in the `DerivedCategory.Q` form.  A caller holding any model
of `RΓ(U, -)` can therefore use this.

`R¹\lim` is spelled as the cokernel of the difference map `1 - shift` on the product of the
groups `Hᵐ⁻¹(U, Kₙ)`, which is the spelling the Milnor sequence of Stacks 0D60 produces and the
spelling the statement of Stacks 0D61 uses.

The derived limit is presented by its defining distinguished triangle with the structural map
`p` given, rather than through `CategoryTheory.Pretriangulated.IsDerivedLimit`, because the
conclusion is about the composite `p ≫ πₙ₀`, which is the canonical map `L ⟶ K_{n₀}`, and that
map is lost if `p` is existentially quantified.

**Universe narrowing.**  `RingedSpace.{u, u}` collapses the space and ring-sections universes and
the sheaves of modules are `SheafOfModules.{u}`, inherited from the Stacks 0D60 statements this
is built on; Stacks 0D61 states the same content with those three universes independent.  The
two derived categories are at free, independently chosen instances, as there.

## References

* [Stacks Project, Tag 0D61](https://stacks.math.columbia.edu/tag/0D61)
* [Stacks Project, Tag 0D60](https://stacks.math.columbia.edu/tag/0D60)
* [Stacks Project, Tag 0D6L](https://stacks.math.columbia.edu/tag/0D6L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  TopologicalSpace

universe u

namespace Stacks.Cohomology.DerivedLimitMittagLeffler

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)
  [HasDerivedCategory.{u} (SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{u} AddCommGrpCat.{u}]

/-- **The Mittag-Leffler injectivity criterion over an open (Stacks 0D61, over a single open).**
Let `L` be a derived limit of the inverse system `K` in `D(𝒪_X)`, presented by its defining
distinguished triangle.  If `R¹\lim Hᵐ⁻¹(U, Kₙ)` vanishes and the transition maps
`Hᵐ(U, Kₙ) ⟶ Hᵐ(U, K_{n₀})` are monomorphisms for `n ≥ n₀`, then the canonical map
`Hᵐ(U, L) ⟶ Hᵐ(U, K_{n₀})` is a monomorphism. -/
theorem mono_cohomology_derivedLimit_projection
    (RGamma : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory AddCommGrpCat.{u})
    (comparison : (DerivedLimitSections.sections X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RGamma)
    (hRGamma : RGamma.IsRightDerivedFunctor comparison
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)))
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))))
    (m : ℤ) (n₀ : ℕ)
    (hlimOne : IsZero (cokernel (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ (K ⋙ RGamma ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1)).obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ (K ⋙ RGamma ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1)).obj ⟨n⟩) (n + 1) ≫
          (K ⋙ RGamma ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1)).map
              (homOfLE (Nat.le_succ n)).op)))
    (hmono : ∀ (n : ℕ) (hn : n₀ ≤ n),
      Mono ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
        (RGamma.map (K.map (homOfLE hn).op)))) :
    Mono ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
      (RGamma.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n₀))) := by
  obtain ⟨i, q, hiq, hShortExact, hProjection⟩ :=
    DerivedLimitSections.exists_shortExact_limOne_cohomology_derivedLimit
      X U RGamma comparison hRGamma K L p hL m
  have hq : Mono q :=
    (ShortComplex.exact_iff_mono _ (hlimOne.eq_of_src i 0)).1 hShortExact.exact
  have hπ : Mono (limit.π
      (K ⋙ RGamma ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} m) ⟨n₀⟩) :=
    mono_limit_projection_of_monos_ge n₀ hmono
  rw [← hProjection n₀]
  exact mono_comp q _

/-- **The Mittag-Leffler injectivity criterion over an open (Stacks 0D61, over a single open),
in the form of injectivity of the underlying map of abelian groups.**  This is the shape in
which the statement of Stacks 0D61 takes its hypotheses and conclusion. -/
theorem injective_cohomology_derivedLimit_projection
    (RGamma : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory AddCommGrpCat.{u})
    (comparison : (DerivedLimitSections.sections X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RGamma)
    (hRGamma : RGamma.IsRightDerivedFunctor comparison
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)))
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))))
    (m : ℤ) (n₀ : ℕ)
    (hlimOne : IsZero (cokernel (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ (K ⋙ RGamma ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1)).obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ (K ⋙ RGamma ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1)).obj ⟨n⟩) (n + 1) ≫
          (K ⋙ RGamma ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1)).map
              (homOfLE (Nat.le_succ n)).op)))
    (hinj : ∀ (n : ℕ) (hn : n₀ ≤ n),
      Function.Injective (ConcreteCategory.hom
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
          (RGamma.map (K.map (homOfLE hn).op))))) :
    Function.Injective (ConcreteCategory.hom
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
        (RGamma.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n₀)))) :=
  (AddCommGrpCat.mono_iff_injective _).1
    (mono_cohomology_derivedLimit_projection X U RGamma comparison hRGamma K L p hL m n₀
      hlimOne fun n hn => (AddCommGrpCat.mono_iff_injective _).2 (hinj n hn))

end Stacks.Cohomology.DerivedLimitMittagLeffler

end
