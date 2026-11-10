module

public import StacksFrontier.AlgebraicGeometry.Duality.C1590Private.RelativeDualizingSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.NoetherianModelContraction
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.OpenLocus
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Basic
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Components

/-!
# A Gorenstein Noetherian model of a family of curves with Gorenstein fibres

Let `f : X ⟶ S` be a proper, flat morphism of finite presentation over an affine scheme `S`
whose fibres are Gorenstein, equidimensional of dimension one. This file produces the reduction
"we may assume `S` Noetherian" of the proofs of Stacks 0E6P and 0E6R: `f` is the base change,
along a morphism `S ⟶ S₀` to a Noetherian scheme, of a proper flat morphism `f₀ : X₀ ⟶ S₀` of
finite presentation which is Gorenstein at *every* point of `X₀`, and whose fibres have dimension
one at the points coming from `X`.

The model is obtained in two steps. First, `S` is a cofiltered limit of Noetherian affine schemes
and `f` descends to one of them (Stacks 01ZM, 04AI; `exists_properFlat_stageModel`). Second, the
points of `X₀` at which the model is Gorenstein and has fibre dimension at most one form an open
set (Stacks 0C09, 02FZ); its complement has closed image in `S₀`, the model being proper, and the
complement `U₀` of that image is an open neighbourhood of the image of `S`: a point of `X₀` over
the image of `S` comes from a point of `X`, and both conditions descend from `X` along the base
change (Stacks 0C07, 02FY). The model is then restricted to `U₀`.

## Main definitions

* `AlgebraicGeometry.C1590Private.HasGorensteinCurveFibres`: every nonempty fibre of `f` is a
  Gorenstein scheme, equidimensional of dimension one.

## Main results

* `AlgebraicGeometry.C1590Private.HasGorensteinCurveFibres.isGorensteinAt`: such an `f` is a
  Gorenstein morphism.
* `AlgebraicGeometry.C1590Private.HasGorensteinCurveFibres.topologicalKrullDimAt_eq_one`: its
  fibres have dimension one at every point.
* `AlgebraicGeometry.C1590Private.exists_gorensteinNoetherianModel`: the model.

## References

* [Stacks Project, Tag 0E6P](https://stacks.math.columbia.edu/tag/0E6P)
* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
* [Stacks Project, Tag 0C07](https://stacks.math.columbia.edu/tag/0C07)
* [Stacks Project, Tag 0C09](https://stacks.math.columbia.edu/tag/0C09)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 02FZ](https://stacks.math.columbia.edu/tag/02FZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.C1590Private

section Fibres

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Gorenstein fibres, equidimensional of dimension one** (the hypothesis of Stacks 0E6R): the
fibre of `f` through every point of `X` is a Gorenstein scheme, equidimensional of dimension
one. Empty fibres are not constrained. -/
def HasGorensteinCurveFibres : Prop :=
  ∀ x : X, IsGorenstein (f.fiber (f x)) ∧ Equidimensional (f.fiber (f x)) ∧
    topologicalKrullDim (f.fiber (f x)) = 1

variable {f}

/-- With Gorenstein fibres, a flat morphism locally of finite presentation is Gorenstein at every
point. -/
theorem HasGorensteinCurveFibres.isGorensteinAt [Flat f] [LocallyOfFinitePresentation f]
    (h : HasGorensteinCurveFibres f) (x : X) :
    f.IsGorensteinAt (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f) x :=
  have := (h x).1
  ⟨Flat.stalkMap f x, IsGorenstein.isGorensteinLocalRing (f.asFiber x)⟩

/-- With fibres equidimensional of dimension one, the fibre of a morphism locally of finite type
has dimension one at every point. -/
theorem HasGorensteinCurveFibres.topologicalKrullDimAt_eq_one [LocallyOfFiniteType f]
    (h : HasGorensteinCurveFibres f) (x : X) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = 1 :=
  Stacks.Curves.topologicalKrullDimAt_eq_one_of_equidimensional (k := S.residueField (f x))
    (f.fiber (f x)) (f.fiberToSpecResidueField (f x)) (h x).2.1 (h x).2.2 (f.asFiber x)

end Fibres

section Model

/-- **A Noetherian model of a proper flat morphism over an affine base** (Stacks 01ZM, 04AI): `f`
is the base change, along a morphism to a Noetherian affine scheme, of a proper flat morphism of
finite presentation. -/
theorem exists_noetherianModel_properFlat {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] :
    ∃ (S₀ : Scheme.{u}) (π : S ⟶ S₀), IsNoetherian S₀ ∧ IsAffine S₀ ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ S₀) (g : X ⟶ X₀),
        IsProper f₀ ∧ Flat f₀ ∧ LocallyOfFinitePresentation f₀ ∧ IsPullback g f f₀ π := by
  let c := (specAdjoinFinsetCone Γ(S, ⊤)).extend S.isoSpec.hom
  have hc : IsLimit c := IsLimit.ofIsoLimit (isLimit_specAdjoinFinsetCone Γ(S, ⊤))
    (Cone.extendIso (specAdjoinFinsetCone Γ(S, ⊤))
      (S.isoSpec.symm : (specAdjoinFinsetCone Γ(S, ⊤)).pt ≅ S))
  obtain ⟨i, X₀, f₀, g, h₁, h₂, h₃, h₄⟩ :=
    exists_properFlat_stageModel (specAdjoinFinsetDiagram Γ(S, ⊤)) c hc f
  exact ⟨_, c.π.app i, isNoetherian_specAdjoinFinsetDiagram_obj _ i,
    isAffine_specAdjoinFinsetDiagram_obj _ i, X₀, f₀, g, h₁, h₂, h₃, h₄⟩

/-- Gorensteinness at a point descends along a cartesian square whose right edge is flat and
locally of finite type, read at an arbitrary pullback square rather than the chosen one. -/
theorem isGorensteinAt_of_isPullback {X X₀ S S₀ : Scheme.{u}} {g : X ⟶ X₀} {f : X ⟶ S}
    {f₀ : X₀ ⟶ S₀} {π : S ⟶ S₀} (sq : IsPullback g f f₀ π) [Flat f₀]
    [LocallyOfFinitePresentation f₀]
    (hf₀ : ∀ y : S₀, IsLocallyNoetherian (f₀.fiber y))
    (hf : ∀ y : S, IsLocallyNoetherian (f.fiber y)) (x : X)
    (hx : f.IsGorensteinAt hf x) : f₀.IsGorensteinAt hf₀ (g x) := by
  let e := sq.isoPullback
  have hsnd : ∀ y : S, IsLocallyNoetherian ((pullback.snd f₀ π).fiber y) :=
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation _
  have hef : ∀ y : S, IsLocallyNoetherian ((e.hom ≫ pullback.snd f₀ π).fiber y) := by
    rw [sq.isoPullback_hom_snd]; exact hf
  have h₁ : (pullback.snd f₀ π).IsGorensteinAt hsnd (e.hom x) :=
    (Scheme.Hom.isGorensteinAt_comp_iff_of_isOpenImmersion_left e.hom (pullback.snd f₀ π)
      hsnd hef x).mp
      ((Scheme.Hom.isGorensteinAt_congr (sq.isoPullback_hom_snd).symm hf hef x).mp hx)
  have h₂ := (Set.ext_iff.mp (Scheme.Hom.setOf_isGorensteinAt_pullback_eq_preimage f₀ π hf₀ hsnd)
    (e.hom x)).mp h₁
  have hg : (pullback.fst f₀ π) (e.hom x) = g x := by
    rw [← Scheme.Hom.comp_apply, sq.isoPullback_hom_fst]
  simpa only [Set.mem_preimage, Set.mem_ofPred_eq, hg] using h₂

/-- If `f` has fibres of dimension one, so does any morphism `f₀` it is a base change of. -/
private theorem topologicalKrullDimAt_fiber_eq_one_of_isPullback {X X₀ S S₀ : Scheme.{u}}
    {g : X ⟶ X₀} {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {π : S ⟶ S₀} (sq : IsPullback g f f₀ π)
    [LocallyOfFiniteType f] [LocallyOfFiniteType f₀] (h : HasGorensteinCurveFibres f) (x : X) :
    topologicalKrullDimAt (f₀.fiber (f₀ (g x))) (f₀.asFiber (g x)) = 1 := by
  rw [← topologicalKrullDimAt_fiber_eq_of_isPullback sq x, h.topologicalKrullDimAt_eq_one x]

/-- **A Gorenstein Noetherian model** (the reduction of Stacks 0E6P, 0E6R to a Noetherian base).
Let `f : X ⟶ S` be proper, flat and of finite presentation over an affine `S`, with Gorenstein
fibres equidimensional of dimension one. Then `f` is the base change, along a morphism `S ⟶ S₀`
to a Noetherian scheme, of a proper flat morphism `f₀ : X₀ ⟶ S₀` of finite presentation which is
Gorenstein at every point of `X₀`, and whose fibre has dimension one at every point coming from
`X`. -/
theorem exists_gorensteinNoetherianModel {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] (h : HasGorensteinCurveFibres f) :
    ∃ (S₀ : Scheme.{u}) (π : S ⟶ S₀) (_ : IsNoetherian S₀) (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ S₀)
      (g : X ⟶ X₀) (_ : IsProper f₀) (_ : Flat f₀) (_ : LocallyOfFinitePresentation f₀),
      IsPullback g f f₀ π ∧
        (∀ x₀ : X₀, f₀.IsGorensteinAt
          (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f₀) x₀) ∧
        ∀ x : X, topologicalKrullDimAt (f₀.fiber (f₀ (g x))) (f₀.asFiber (g x)) = 1 := by
  obtain ⟨S₁, π₁, hS₁, -, X₁, f₁, g₁, hp, hfl, hfp, sq₁⟩ := exists_noetherianModel_properFlat f
  let hf₁ := isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f₁
  -- the good locus of the model
  let G : Set X₁ := {x₁ | f₁.IsGorensteinAt hf₁ x₁} ∩
    {x₁ | topologicalKrullDimAt (f₁.fiber (f₁ x₁)) (f₁.asFiber x₁) ≤ ((1 : ℕ) : WithBot ℕ∞)}
  have hG : IsOpen G :=
    (Scheme.Hom.isOpen_setOf_isGorensteinAt f₁).inter (isOpen_setOf_fiberDimensionAt_le f₁ 1)
  have hgood : ∀ x : X, g₁ x ∈ G := fun x =>
    ⟨isGorensteinAt_of_isPullback sq₁ hf₁ _ x (h.isGorensteinAt x),
      (topologicalKrullDimAt_fiber_eq_one_of_isPullback sq₁ h x).le⟩
  let U₀ : S₁.Opens := ⟨(f₁.base '' Gᶜ)ᶜ, (f₁.isClosedMap _ hG.isClosed_compl).isOpen_compl⟩
  have hU₀ : ∀ y : X₁, f₁ y ∈ U₀ → y ∈ G := fun y hy => by
    by_contra hyG
    exact hy ⟨y, hyG, rfl⟩
  have hπ : Set.range π₁.base ⊆ (U₀ : Set S₁) := by
    rintro _ ⟨s, rfl⟩ ⟨x₁, hx₁, hxs⟩
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x₁ s hxs
    apply hx₁
    have : g₁ (sq₁.isoPullback.inv z) = x₁ := by
      rw [← Scheme.Hom.comp_apply, sq₁.isoPullback_inv_fst, hz₁]
    rw [← this]
    exact hgood _
  -- the restriction of the model to `U₀`
  let X₀ := (f₁ ⁻¹ᵁ U₀).toScheme
  let f₀ : X₀ ⟶ U₀.toScheme := f₁ ∣_ U₀
  have sqU : IsPullback (f₁ ⁻¹ᵁ U₀).ι f₀ f₁ U₀.ι := (isPullback_morphismRestrict f₁ U₀).flip
  have : IsProper f₀ := MorphismProperty.of_isPullback sqU inferInstance
  have : Flat f₀ := MorphismProperty.of_isPullback sqU inferInstance
  have : LocallyOfFinitePresentation f₀ := MorphismProperty.of_isPullback sqU inferInstance
  let π : S ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι π₁ (by simpa using hπ)
  have hgU : Set.range g₁.base ⊆ Set.range (f₁ ⁻¹ᵁ U₀).ι.base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f₁ (g₁ x) ∈ U₀
    rw [← Scheme.Hom.comp_apply, sq₁.w, Scheme.Hom.comp_apply]
    exact hπ ⟨_, rfl⟩
  let g : X ⟶ X₀ := IsOpenImmersion.lift (f₁ ⁻¹ᵁ U₀).ι g₁ hgU
  have hgι : g ≫ (f₁ ⁻¹ᵁ U₀).ι = g₁ := IsOpenImmersion.lift_fac _ _ _
  have hπι : π ≫ U₀.ι = π₁ := IsOpenImmersion.lift_fac _ _ _
  have sq : IsPullback g f f₀ π := by
    refine IsPullback.of_right ?_ ?_ sqU
    · rw [hgι, hπι]; exact sq₁
    · rw [← cancel_mono U₀.ι, Category.assoc, Category.assoc, ← sqU.w, hπι, reassoc_of% hgι,
        sq₁.w]
  have hU₀N : IsNoetherian U₀.toScheme :=
    have : CompactSpace U₀.toScheme :=
      isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (U₀ : Set S₁))
    ⟨⟩
  refine ⟨U₀.toScheme, π, hU₀N, X₀, f₀, g, inferInstance, inferInstance,
    inferInstance, sq, fun y => ?_, fun x => ?_⟩
  · have hy := (hU₀ ((f₁ ⁻¹ᵁ U₀).ι y) (by
      exact ((f₁ ⁻¹ᵁ U₀).ι_apply y ▸ y.2 : _))).1
    exact (Scheme.Hom.isGorensteinAt_iff_of_comp_eq (f₁ ⁻¹ᵁ U₀).ι U₀.ι f₁ f₀ sqU.w hf₁
      (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f₀)
      (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation _) y).mp hy
  · exact topologicalKrullDimAt_fiber_eq_one_of_isPullback sq h x

end Model

end AlgebraicGeometry.C1590Private

end
