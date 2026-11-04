module

public import StacksFrontier.AlgebraicGeometry.Duality.C1590Private.RelativeDualizingSheafModel
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.ProperDualizingInvertible
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Fibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayRelativeDimensionOpen
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersion

/-!
# The shape of the relative dualizing complex of a family of Gorenstein curves

Let `f : X ⟶ S` be a proper, flat morphism of finite presentation over an affine `S` with
Gorenstein fibres equidimensional of dimension one. This file proves that the relative dualizing
complex `ω^•_{X/S} = a(𝒪_S)` is the derived pullback of a module placed in degree `-1`: there are
a cartesian square `X ⟶ V` over `S ⟶ T`, with `V ⟶ T` locally of finite presentation, and a
finitely presented `𝒪_V`-module `ω_V` flat over `T`, such that
`ω^•_{X/S} ≅ L(g_V)^*(ω_V[1])`. Consequently `ω^•_{X/S}` has no cohomology above degree `-1` and
`ω_{X/S} = H^{-1}(ω^•_{X/S}) ≅ (g_V)^*ω_V` (Stacks 0E6P).

The square comes from the Gorenstein Noetherian model `f₀ : X₀ ⟶ S₀` of
`AlgebraicGeometry.C1590Private.exists_gorensteinNoetherianModel`. There `f₀` is a
Cohen–Macaulay morphism of the category `FTS S₀` (Stacks 0C06), so by Stacks 0BV8
`f₀^!𝒪_{S₀} = ω₀[d]` on the open `V ⊆ X₀` of relative dimension `d`, with `ω₀` coherent and flat
over `S₀`; `X` maps into `V` for `d = 1` because its fibres are curves (Stacks 02FY), and
`f₀^!𝒪_{S₀}` computed at the compactification `X₀` itself is `a(𝒪_{S₀})`. Formation of `a(𝒪)`
commutes with base change (Stacks 0E6N).

## Main results

* `AlgebraicGeometry.C1590Private.exists_relativeDualizingComplex_iso_derivedPullback`: the
  description of `ω^•_{X/S}` above.
* `AlgebraicGeometry.C1590Private.isLE_relativeDualizingComplex`: `ω^•_{X/S} ∈ D^{≤ -1}`.

## References

* [Stacks Project, Tag 0E6P](https://stacks.math.columbia.edu/tag/0E6P)
* [Stacks Project, Tag 0BV8](https://stacks.math.columbia.edu/tag/0BV8)
* [Stacks Project, Tag 0C06](https://stacks.math.columbia.edu/tag/0C06)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Duality Stacks.Duality.DerivedPushforward

universe u

namespace AlgebraicGeometry.C1590Private

/-- A morphism `g` landing in an open `V` with `g ≫ V.ι` the top edge of a cartesian square is
itself the top edge of a cartesian square over the restriction of the right edge to `V`. -/
theorem isPullback_of_comp_ι {X X₀ S T : Scheme.{u}} {g : X ⟶ X₀} {f : X ⟶ S} {f₀ : X₀ ⟶ T}
    {π : S ⟶ T} (sq : IsPullback g f f₀ π) (V : X₀.Opens) (gV : X ⟶ V.toScheme)
    (hgV : gV ≫ V.ι = g) : IsPullback gV f (V.ι ≫ f₀) π := by
  refine ⟨⟨by rw [← Category.assoc, hgV, sq.w]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => sq.lift (s.fst ≫ V.ι) s.snd (by rw [Category.assoc, s.condition]))
    (fun s => ?_) (fun s => sq.lift_snd _ _ _) (fun s m h₁ h₂ => ?_)⟩⟩
  · rw [← cancel_mono V.ι]
    simp only [Category.assoc, hgV]
    exact sq.lift_fst _ _ _
  · apply sq.hom_ext
    · rw [sq.lift_fst, ← hgV, ← Category.assoc, h₁]
    · rw [sq.lift_snd, h₂]

/-- **The relative dualizing complex of a family of Gorenstein curves** (Stacks 0E6P). Let
`f : X ⟶ S` be proper, flat and of finite presentation over an affine `S`, with Gorenstein fibres
equidimensional of dimension one. There are a cartesian square `X ⟶ V` over `S ⟶ T` with `V ⟶ T`
locally of finite presentation, and a finitely presented `𝒪_V`-module `ω_V` flat over `T`, such
that `ω^•_{X/S} ≅ L(g_V)^*(ω_V[1])`. -/
theorem exists_relativeDualizingComplex_iso_derivedPullback {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : HasGorensteinCurveFibres f) :
    ∃ (T V : Scheme.{u}) (π : S ⟶ T) (fV : V ⟶ T) (gV : X ⟶ V) (M : V.Modules)
      (_ : LocallyOfFinitePresentation fV),
      IsPullback gV f fV π ∧ M.IsFinitePresentation ∧
        IsFlatOver fV.toLRSHom.toShHom M ∧
        Nonempty ((relativeDualizingComplex f).obj ≅
          (Stacks.Duality.derivedPullback gV).obj
            (((DerivedCategory.singleFunctor V.Modules 0).obj M)⟦(1 : ℤ)⟧)) := by
  obtain ⟨S₀, π, hS₀, X₀, f₀, g, hp, hfl, hfp, sq, hG, hdim⟩ :=
    exists_gorensteinNoetherianModel f h
  -- `f₀` as a morphism of `FTS S₀`, compactified by `X₀` itself
  let Ŷ : FTS S₀ := FTS.mk f₀
  let Ŝ : FTS S₀ := FTS.mk (𝟙 S₀)
  let ĝ : Ŷ ⟶ Ŝ := MorphismProperty.Over.homMk f₀ (Category.comp_id f₀)
  let j : CompactificationOf (Over.mk ĝ.left) :=
    ⟨StructuredArrow.mk (Y := Over.mk f₀)
      (Over.homMk (U := Over.mk ĝ.left) (V := Over.mk f₀) (𝟙 X₀) (Category.id_comp f₀)),
      ⟨(inferInstance : IsOpenImmersion (𝟙 X₀)), (inferInstance : IsProper f₀)⟩⟩
  have : Flat ĝ.left := hfl
  have hCM : ĝ.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left ĝ) := fun x₀ =>
    Scheme.Hom.isCohenMacaulayAt_of_isGorensteinAt _ _ (hG x₀)
  obtain ⟨ω₀, hcoh, hflat, hiso⟩ := exists_isCoherent_isFlatOver_iso_shift_upperShriek ĝ j hCM
  have hCMf := (isCohenMacaulay_iff_flat_and_fibers ĝ.left
    (isLocallyNoetherian_fiber_left ĝ)).mp hCM
  -- the open of relative dimension one, through which `g` factors
  let V : X₀.Opens := @relativeDimensionOpen _ _ f₀ hfl hfp hCMf.2 1
  have hgV : Set.range g.base ⊆ Set.range V.ι.base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have h₁ := @relativeDimensionFunction_apply _ _ f₀ hfl hfp hCMf.2 (g x)
    rw [hdim x] at h₁
    exact (@mem_relativeDimensionOpen _ _ f₀ hfl hfp hCMf.2 1 (g x)).2
      (by exact_mod_cast h₁.symm)
  let gV : X ⟶ V.toScheme := IsOpenImmersion.lift V.ι g hgV
  have hgVι : gV ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
  let M : V.toScheme.Modules := (Scheme.Modules.restrictFunctor V.ι).obj ω₀
  have : ω₀.IsCoherent := hcoh
  refine ⟨S₀, V.toScheme, π, V.ι ≫ f₀, gV, M, inferInstance, isPullback_of_comp_ι sq V gV hgVι,
    @Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_restrict _ _ V.ι _ ω₀
      (Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_of_isCoherent' ω₀),
    fun y => (isFlatOverAt_restrict_iff V.ι f₀ ω₀ y).mpr (hflat _), ?_⟩
  obtain ⟨e⟩ := hiso 1
  -- `f₀^!𝒪_{S₀}` at the compactification `X₀` is `a(𝒪_{S₀})`
  let eR : relativeDualizingComplexObj ĝ j ≅ (relativeDualizingComplex f₀).obj :=
    (derivedPullbackIdIso X₀).app _
  exact ⟨(relativeDualizingComplexBaseChangeIso sq).symm ≪≫
    (Stacks.Duality.derivedPullback g).mapIso eR.symm ≪≫
    eqToIso (by rw [← hgVι]) ≪≫
    ((Stacks.Duality.derivedPullbackCompIso gV V.ι).app _).symm ≪≫
    (Stacks.Duality.derivedPullback gV).mapIso
      ((derivedRestrictIsoDerivedPullback V.ι).app _).symm ≪≫
    (Stacks.Duality.derivedPullback gV).mapIso e⟩

end AlgebraicGeometry.C1590Private

end
