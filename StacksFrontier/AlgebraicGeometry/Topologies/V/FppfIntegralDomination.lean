module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.InfiniteProductsIntegral
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.InfiniteProductsSurjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.ExtensionChart
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.LocallyQuasiFiniteRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.V.FppfFiniteDomination

/-!
# Integral domination of an fppf covering of a quasi-separated scheme

Stacks 0CNZ states that an fppf covering of a scheme is dominated by a single surjective
*integral* morphism which, on a Zariski covering of its source, factors through members of the
given covering. This file proves it for a **quasi-separated** base, which is all that its only
consumer in this library needs:
`AlgebraicGeometry.exists_finite_surjective_refinement_of_mem_fppfPrecoverage` (Stacks 0CP0)
applies it at a quasi-compact and quasi-separated base.

The restriction is **not** needed for the tag: it is lifted in
`StacksFrontier.AlgebraicGeometry.Topologies.V.FppfIntegralDominationGeneral`, which proves the
same refinement for an arbitrary base and is what carries [Stacks, Tag 0CNZ]. What is proved
here is the quasi-separated case by the route the source takes, through Tag 0CNX; it is kept
because `AlgebraicGeometry.exists_finite_surjective_refinement_of_hasQuasiFiniteSlices` and the
affine-domination chain are stated against it at a quasi-separated base anyway. The two should
be collapsed onto the general one by a dedup sweep.

The restriction is forced along this route, and the reason is a defect in the statement of Stacks
0CNX rather than a weakness of this library. The Stacks proof of 0CNZ applies Tag 0CNX — extension
of a surjective integral morphism from an open subscheme — at *arbitrary* opens, while the proof of
Tag 0CNX goes through the relative normalization of the base, which Stacks (Tag 0BAK) and Mathlib
both define only for a quasi-compact and quasi-separated morphism. The library's form of 0CNX,
`AlgebraicGeometry.exists_integral_surjective_extension`, therefore carries `[QuasiCompact U.ι]`;
see the module documentation of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.FppfApplication.IntegralSurjectiveExtension`. On a
quasi-separated base every point of every open has an *affine* neighbourhood inside it whose
inclusion is quasi-compact, so the argument can be run with every chart shrunk to such a
neighbourhood, and that is what is done here.

## Main results

* `AlgebraicGeometry.exists_integralChart_of_finiteLocallyFreeRefinement` is the per-point
  heart of the construction: at a point of a quasi-separated base, the chart data produced by
  Stacks 05WN is shrunk to an affine neighbourhood and extended by Tag 0CNX, twice.
* `AlgebraicGeometry.exists_integral_surjective_refinement_of_mem_fppfPrecoverage` is
  **Stacks 0CNZ for a quasi-separated base**, granted `AlgebraicGeometry.HasQuasiFiniteSlices`
  (Stacks 0570), which is the only hypothesis that Stacks 05WN still needs in this library.
* `AlgebraicGeometry.fppfHasFiniteDomination_of_hasQuasiFiniteSlices` discharges
  `AlgebraicGeometry.FppfHasFiniteDomination` — the input of
  `AlgebraicGeometry.isPHCovering_of_mem_fppfPrecoverage` — from Stacks 0570 and Stacks 09YZ,
  removing Stacks 0CNZ from the list of hypotheses that result rests on.

## Implementation notes

Nothing in this file is tagged. Every result is conditional on
`AlgebraicGeometry.HasQuasiFiniteSlices`, which is Stacks 0570 and is not proved in this
library, and the main result is in any case only the quasi-separated case of its tag.

The construction follows the Stacks proof. At a point `x` of the base `S`, Stacks 05WN
supplies an open `𝒰.X j` around `x`, a surjective finite locally free `g₁ j : W j ⟶ 𝒰.X j`, an
open cover `𝒲 j` of `W j`, and surjective finite locally free morphisms `h j k` onto its
members, each of which factors through a member of the given fppf covering. The chart is
shrunk to an affine open `Ω ∋ x` of `S` contained in the range of `𝒰.f j` and `g₁ j` is
replaced by its base change along `Ω ⟶ 𝒰.X j`; Tag 0CNX then extends that base change to an
integral surjective `a : A ⟶ S` containing `Z` — the base change — as the open subscheme
`a ⁻¹ᵁ Ω`. Inside `Z` the members of `𝒲 j` are shrunk to affine opens, whose images in `A` are
quasi-compact because `A` is quasi-separated (the integral morphism `a` is quasi-separated), so
Tag 0CNX applies a second time, now over `A`, to the base changes of the `h j k`.

The `[Small.{u} I]` hypothesis that [Stacks, Tag 0CNZ] and
`AlgebraicGeometry.FppfHasIntegralDomination` carry on the index type of the covering turns out
not to be needed: Stacks 05WN accepts a covering family indexed in any universe, and the
products taken here are indexed by the points of schemes, hence by types in the scheme
universe. Dropping it is a generalisation, not a weakening.

Two devices keep the elaboration cheap, both standard in this library. Every intermediate
object is introduced by `obtain` against an existential statement rather than by `let`, so
that it is an opaque local constant with no competing instances; and the factorizations
through the members of the fppf covering are recorded as plain equations of morphisms, so that
the lifting of a morphism through an open immersion is done by
`AlgebraicGeometry.IsOpenImmersion.lift` instead of through a chosen pullback. In particular
the comparison isomorphisms that Tag 0CNX produces in `CategoryTheory.Over` are never used
directly: `AlgebraicGeometry.exists_integral_surjective_extension_isOpenImmersion` has already
unwound them into an open immersion together with the computation of its image.

## References

* [Stacks Project, Tag 0CNZ](https://stacks.math.columbia.edu/tag/0CNZ)
* [Stacks Project, Tag 0CNX](https://stacks.math.columbia.edu/tag/0CNX)
* [Stacks Project, Tag 05WN](https://stacks.math.columbia.edu/tag/05WN)
* [Stacks Project, Tag 0CP0](https://stacks.math.columbia.edu/tag/0CP0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v w

namespace AlgebraicGeometry

/-- A morphism whose range lies in the range of an open immersion factors through it. -/
private theorem exists_comp_eq_of_range_subset {X Y Z : Scheme.{u}} (f : X ⟶ Z)
    [IsOpenImmersion f] (g : Y ⟶ Z) (hg : Set.range g.base ⊆ Set.range f.base) :
    ∃ l : Y ⟶ X, l ≫ f = g :=
  ⟨IsOpenImmersion.lift f g hg, IsOpenImmersion.lift_fac _ _ _⟩

/-- A finite surjective morphism has a finite surjective base change along any morphism. -/
private theorem exists_finite_surjective_comm {X Y Z : Scheme.{u}} (g : X ⟶ Z) (k : Y ⟶ Z)
    [IsFinite g] [Surjective g] :
    ∃ (P : Scheme.{u}) (e : P ⟶ X) (m : P ⟶ Y), e ≫ g = m ≫ k ∧ IsFinite m ∧ Surjective m :=
  ⟨pullback g k, pullback.fst _ _, pullback.snd _ _, pullback.condition, inferInstance,
    inferInstance⟩

/-- The per-point heart of the quasi-separated case of [Stacks, Tag 0CNZ].

Given the data that [Stacks, Tag 05WN] produces for an fppf covering `{f i}` of a
quasi-separated scheme `S` — an open cover `𝒰`, surjective finite morphisms `g₁ j : W j ⟶ 𝒰.X j`,
open covers `𝒲 j` of the `W j`, surjective finite morphisms `h j k` onto their members, and a
factorization of each `T j k ⟶ S` through a member of the covering — every point `x` of `S`
has a surjective integral `a : A ⟶ S` such that

* the part of `A` lying over a neighbourhood of `x` is an open subscheme `Z` of `A`, so in
  particular every point of `A` above `x` lies in `Z`; and
* every point of `Z` lies in a quasi-compact open `V` of `A` carrying a surjective integral
  morphism from a scheme that still maps to a member of the given covering, compatibly over
  `S`.

Both bullets come from [Stacks, Tag 0CNX] in the form
`AlgebraicGeometry.exists_integral_surjective_extension_isOpenImmersion`, applied first over
`S` and then over `A`. The quasi-compactness of the opens it requires is what forces the
charts to be shrunk to affine neighbourhoods, and hence the base to be quasi-separated. -/
theorem exists_integralChart_of_finiteLocallyFreeRefinement
    {I : Type v} {S : Scheme.{u}} [QuasiSeparatedSpace S]
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    {𝒰 : S.OpenCover.{w}} {W : 𝒰.I₀ → Scheme.{u}} {g₁ : ∀ j, W j ⟶ 𝒰.X j}
    {𝒲 : ∀ j, (W j).OpenCover.{w}} {T : ∀ j, (𝒲 j).I₀ → Scheme.{u}}
    {h : ∀ j k, T j k ⟶ (𝒲 j).X k}
    (hg₁ : ∀ j, Surjective (g₁ j)) (hg₂ : ∀ j, IsFinite (g₁ j))
    (hh₁ : ∀ j k, Surjective (h j k)) (hh₂ : ∀ j k, IsFinite (h j k))
    (hfac : ∀ j k, ∃ i, ∃ l : T j k ⟶ X i,
      l ≫ f i = h j k ≫ (𝒲 j).f k ≫ g₁ j ≫ 𝒰.f j)
    (x : S) :
    ∃ (A : Scheme.{u}) (a : A ⟶ S), IsIntegralHom a ∧ Surjective a ∧
      ∃ (Z : Scheme.{u}) (d : Z ⟶ A), IsOpenImmersion d ∧
        (∀ p : A, a.base p = x → p ∈ Set.range d.base) ∧
        ∀ ζ : Z, ∃ V : A.Opens, d.base ζ ∈ V ∧ QuasiCompact V.ι ∧
          ∃ (T' : Scheme.{u}) (q : T' ⟶ V.toScheme), IsIntegralHom q ∧ Surjective q ∧
            ∃ i, ∃ l : T' ⟶ X i, l ≫ f i = q ≫ V.ι ≫ a := by
  classical
  set j := 𝒰.idx x
  have hxU : x ∈ (𝒰.f j).opensRange := 𝒰.covers x
  obtain ⟨Ω, hΩaff, hxΩ, hΩle, hΩqc⟩ :=
    exists_isAffineOpen_quasiCompact_ι_mem_le (𝒰.f j).opensRange hxU
  obtain ⟨ι', hι'⟩ := exists_comp_eq_of_range_subset (𝒰.f j) Ω.ι
    (by rw [Scheme.Opens.range_ι]; exact hΩle)
  have : IsFinite (g₁ j) := hg₂ j
  have : Surjective (g₁ j) := hg₁ j
  obtain ⟨Z, e, m, hZcomm, hmfin, hmsurj⟩ := exists_finite_surjective_comm (g₁ j) ι'
  have : QuasiCompact Ω.ι := hΩqc
  have : IsFinite m := hmfin
  have : Surjective m := hmsurj
  obtain ⟨A, a, haint, hasurj, d, hdopen, hdcomp, hdrange⟩ :=
    exists_integral_surjective_extension_isOpenImmersion Ω m
  have : IsIntegralHom a := haint
  have : IsOpenImmersion d := hdopen
  have : QuasiSeparatedSpace A := quasiSeparatedSpace_of_quasiSeparated a
  -- The composite `Z ⟶ S` through the shrunken chart is the one the extension records.
  have hed : e ≫ g₁ j ≫ 𝒰.f j = d ≫ a := by
    rw [← Category.assoc, hZcomm, Category.assoc, hι', hdcomp]
  refine ⟨A, a, haint, hasurj, Z, d, hdopen, ?_, ?_⟩
  · intro p hp
    rw [hdrange]
    change a.base p ∈ Ω
    rw [hp]
    exact hxΩ
  · intro ζ
    set k := (𝒲 j).idx (e.base ζ)
    have hζopen : ζ ∈ (e ⁻¹ᵁ ((𝒲 j).f k).opensRange : Set Z) := (𝒲 j).covers (e.base ζ)
    obtain ⟨Θ, hΘaff, hζΘ, hΘle⟩ : ∃ Θ : Z.Opens, IsAffineOpen Θ ∧ ζ ∈ Θ ∧
        (Θ : Set Z) ⊆ (e ⁻¹ᵁ ((𝒲 j).f k).opensRange : Set Z) := by
      obtain ⟨_, ⟨Θ₀, hΘ₀, rfl⟩, h₁, h₂⟩ :=
        Z.isBasis_affineOpens.exists_subset_of_mem_open hζopen
          (e ⁻¹ᵁ ((𝒲 j).f k).opensRange).2
      exact ⟨Θ₀, hΘ₀, h₁, h₂⟩
    obtain ⟨θk, hθk⟩ := exists_comp_eq_of_range_subset ((𝒲 j).f k) (Θ.ι ≫ e) (by
      rintro _ ⟨p, rfl⟩
      exact hΘle p.2)
    have hΘaffine : IsAffine Θ.toScheme := hΘaff
    refine ⟨(Θ.ι ≫ d).opensRange, ⟨⟨ζ, hζΘ⟩, rfl⟩,
      quasiCompact_ι_of_isCompact (Θ.ι ≫ d).opensRange
        (isAffineOpen_opensRange (Θ.ι ≫ d)).isCompact, ?_⟩
    have : IsFinite (h j k) := hh₂ j k
    have : Surjective (h j k) := hh₁ j k
    obtain ⟨T', pr, q₀, hprcomm, hq₀fin, hq₀surj⟩ := exists_finite_surjective_comm (h j k) θk
    have : IsFinite q₀ := hq₀fin
    have : Surjective q₀ := hq₀surj
    refine ⟨T', q₀ ≫ (Θ.ι ≫ d).isoOpensRange.hom, inferInstance, inferInstance, ?_⟩
    obtain ⟨i, l, hl⟩ := hfac j k
    refine ⟨i, pr ≫ l, ?_⟩
    simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc]
    rw [hl, reassoc_of% hprcomm, reassoc_of% hθk, hed]

/-- The factorization step of the quasi-separated case of [Stacks, Tag 0CNZ], with every object
behind a variable.

Suppose `g : S' ⟶ S` factors through an integral `a : A ⟶ S` by `pA`, and `pA` factors in turn
through an integral `b : B ⟶ A` by `pB`; suppose further that the part of `B` lying over an
open `V` of `A` is an open subscheme `T'` of `B` — which is what [Stacks, Tag 0CNX] produces —
and that `T'` maps to a member `X i` of a covering of `S`, compatibly over `S`. Then the open
`pA ⁻¹ᵁ V` of `S'` maps to `X i`, compatibly over `S`.

The morphism is produced by `AlgebraicGeometry.IsOpenImmersion.lift`: the chart `pA ⁻¹ᵁ V` maps
into the part of `B` lying over `V`, which is exactly the image of the open immersion. -/
theorem exists_factorization_of_integralChart {I : Type v} {S : Scheme.{u}}
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    {A B T' S' : Scheme.{u}} {a : A ⟶ S} {b : B ⟶ A} {V : A.Opens}
    {q : T' ⟶ V.toScheme} {dd : T' ⟶ B} [IsOpenImmersion dd]
    (hddcomp : dd ≫ b = q ≫ V.ι) (hddrange : Set.range dd.base = (b ⁻¹ᵁ V : Set B))
    {pA : S' ⟶ A} {pB : S' ⟶ B} {g : S' ⟶ S}
    (hpA : pA ≫ a = g) (hpB : pB ≫ b = pA)
    {i : I} {l : T' ⟶ X i} (hl : l ≫ f i = q ≫ V.ι ≫ a) :
    ∃ t : (pA ⁻¹ᵁ V).toScheme ⟶ X i, (pA ⁻¹ᵁ V).ι ≫ g = t ≫ f i := by
  have hrange : Set.range ((pA ⁻¹ᵁ V).ι ≫ pB).base ⊆ Set.range dd.base := by
    rw [hddrange]
    rintro _ ⟨p, rfl⟩
    have hb : b (((pA ⁻¹ᵁ V).ι ≫ pB) p) = pA ((pA ⁻¹ᵁ V).ι p) := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, hpB, Scheme.Hom.comp_apply]
    change b (((pA ⁻¹ᵁ V).ι ≫ pB) p) ∈ V
    rw [hb]
    exact p.2
  obtain ⟨loc, hloc⟩ := exists_comp_eq_of_range_subset dd _ hrange
  refine ⟨loc ≫ l, ?_⟩
  rw [Category.assoc, hl, ← reassoc_of% hddcomp, reassoc_of% hloc, reassoc_of% hpB, hpA]

/-- **[Stacks, Tag 0CNZ] for a quasi-separated base**, granted [Stacks, Tag 0570] in the form
`AlgebraicGeometry.HasQuasiFiniteSlices`: an fppf covering of a quasi-separated scheme is
dominated by a surjective integral morphism which, on a Zariski covering of its source, factors
through members of the given covering.

This is not tagged. It is conditional on `AlgebraicGeometry.HasQuasiFiniteSlices`, which is
Stacks 0570 and is not proved in this library and is the only remaining gap under
[Stacks, Tag 05WN]; and it is the quasi-separated case of its tag rather than the tag, for the
reason explained in the module documentation.

The index type of the given covering is left at an arbitrary universe: no smallness is needed,
because the construction takes no coproduct over it. The Zariski covering produced is indexed
by the points of the dominating scheme, hence by a type in the scheme universe. -/
theorem exists_integral_surjective_refinement_of_mem_fppfPrecoverage
    (h0570 : HasQuasiFiniteSlices.{u})
    {I : Type v} {S : Scheme.{u}} [QuasiSeparatedSpace S]
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage S) :
    ∃ (S' : Scheme.{u}) (g : S' ⟶ S), IsIntegralHom g ∧ Surjective g ∧
      ∃ (J : Type u) (U : J → Scheme.{u}) (ι : ∀ c, U c ⟶ S'),
        Presieve.ofArrows U ι ∈ Scheme.zariskiPrecoverage S' ∧
          ∀ c, ∃ i, ∃ t : U c ⟶ X i, ι c ≫ g = t ≫ f i := by
  classical
  obtain ⟨𝒰, W, g₁, 𝒲, T, h, hg, hh, -, hfac⟩ :=
    Stacks.Topologies.Fppf.exists_openCover_finiteLocallyFree_refinement_of_hasQuasiFiniteSlices
      h0570 S { I₀ := I, X := X, f := f, mem₀ := hf }
  have hg₂ : ∀ j, IsFinite (g₁ j) := fun j =>
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (g₁ j)).mp (hg j).2).1
  have hh₂ : ∀ j k, IsFinite (h j k) := fun j k =>
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (h j k)).mp (hh j k).2).1
  choose A a haint hasurj Z d hdopen hdover hV using
    exists_integralChart_of_finiteLocallyFreeRefinement (f := f)
      (fun j => (hg j).1) hg₂ (fun j k => (hh j k).1) hh₂ hfac
  choose V hVmem hVqc T' q hqint hqsurj iIdx lMap hlMap using hV
  -- Extend each of the quasi-compact charts of `A x` to the whole of `A x`, by Tag 0CNX again.
  have hBex : ∀ (x : S) (ζ : Z x), ∃ (B : Scheme.{u}) (b : B ⟶ A x),
      IsIntegralHom b ∧ Surjective b ∧ ∃ dd : T' x ζ ⟶ B, IsOpenImmersion dd ∧
        dd ≫ b = q x ζ ≫ (V x ζ).ι ∧ Set.range dd.base = (b ⁻¹ᵁ V x ζ : Set B) := by
    intro x ζ
    have : QuasiCompact (V x ζ).ι := hVqc x ζ
    have : IsIntegralHom (q x ζ) := hqint x ζ
    have : Surjective (q x ζ) := hqsurj x ζ
    exact exists_integral_surjective_extension_isOpenImmersion (V x ζ) (q x ζ)
  choose B b hbint hbsurj dd hddopen hddcomp hddrange using hBex
  have hprod : ∀ {J : Type u} {A : Scheme.{u}} {B : J → Scheme.{u}} (b : ∀ j, B j ⟶ A)
      [∀ j, IsIntegralHom (b j)] [∀ j, Surjective (b j)],
      ∃ (C : Scheme.{u}) (c : C ⟶ A), IsIntegralHom c ∧ Surjective c ∧
        ∃ p : ∀ j, C ⟶ B j, ∀ j, p j ≫ b j = c := by
    intro J A B b _ _
    have := hasProduct_of_isAffineHom A B b
    exact ⟨(∏ᶜ fun j => Over.mk (b j)).left, (∏ᶜ fun j => Over.mk (b j)).hom,
      isIntegralHom_product A B b, surjective_product_hom A B b,
      fun j => (Pi.π (fun j => Over.mk (b j)) j).left,
      fun j => by simpa using Over.w (Pi.π (fun j => Over.mk (b j)) j)⟩
  choose C c hcint hcsurj pB hpB using fun x : S => @hprod _ _ _ (b x) (hbint x) (hbsurj x)
  obtain ⟨S', g, hgint, hgsurj, pC, hpC⟩ :
      ∃ (S' : Scheme.{u}) (g : S' ⟶ S), IsIntegralHom g ∧ Surjective g ∧
        ∃ pC : ∀ x : S, S' ⟶ C x, ∀ x, pC x ≫ c x ≫ a x = g := by
    have := hcint
    have := hcsurj
    have := haint
    have : ∀ x : S, IsIntegralHom (c x ≫ a x) := fun _ => inferInstance
    exact hprod (fun x => c x ≫ a x)
  have hpA : ∀ x : S, (pC x ≫ c x) ≫ a x = g := fun x => (Category.assoc _ _ _).trans (hpC x)
  have hpB' : ∀ (x : S) (ζ : Z x), (pC x ≫ pB x ζ) ≫ b x ζ = pC x ≫ c x := fun x ζ => by
    rw [Category.assoc, hpB x ζ]
  -- Each point of `S'` lies over a point of the chart `Z` of its own fibre.
  have hζex : ∀ z : S', ∃ ζ : Z (g.base z),
      (d (g.base z)).base ζ = (pC (g.base z) ≫ c (g.base z)).base z := by
    intro z
    refine hdover (g.base z) _ ?_
    rw [← Scheme.Hom.comp_apply, hpA (g.base z)]
  choose ζPick hζPick using hζex
  refine ⟨S', g, hgint, hgsurj, S',
    fun z => ((pC (g.base z) ≫ c (g.base z)) ⁻¹ᵁ V (g.base z) (ζPick z)).toScheme,
    fun z => ((pC (g.base z) ≫ c (g.base z)) ⁻¹ᵁ V (g.base z) (ζPick z)).ι, ?_, ?_⟩
  · rw [Scheme.ofArrows_mem_precoverage_iff (P := @IsOpenImmersion)]
    refine ⟨fun z => ⟨z, ?_⟩, fun z => inferInstance⟩
    rw [Scheme.Opens.range_ι]
    change (pC (g.base z) ≫ c (g.base z)) z ∈ V (g.base z) (ζPick z)
    rw [← hζPick z]
    exact hVmem _ _
  · intro z
    have : IsOpenImmersion (dd (g.base z) (ζPick z)) := hddopen _ _
    obtain ⟨t, ht⟩ := exists_factorization_of_integralChart (f := f)
      (hddcomp (g.base z) (ζPick z)) (hddrange (g.base z) (ζPick z))
      (hpA (g.base z)) (hpB' (g.base z) (ζPick z)) (hlMap (g.base z) (ζPick z))
    exact ⟨iIdx (g.base z) (ζPick z), t, ht⟩

/-- Granted [Stacks, Tag 0570] in the form `AlgebraicGeometry.HasQuasiFiniteSlices` and
[Stacks, Tag 09YZ] in the form `AlgebraicGeometry.IntegralHasFinitePresentationLimit`,
**[Stacks, Tag 0CP0]** holds: an fppf covering of a quasi-compact and quasi-separated scheme is
dominated by a finite surjective morphism of finite presentation which, on a Zariski covering
of its source, factors through members of the given covering.

This is `AlgebraicGeometry.exists_finite_surjective_refinement_of_isLimit` fed with the
quasi-separated case of [Stacks, Tag 0CNZ] proved above, rather than with the unrestricted
hypothesis `AlgebraicGeometry.FppfHasIntegralDomination`; the restriction is harmless because
the base is quasi-separated here.

No tag is attached, since the result is conditional on the two hypotheses. -/
theorem exists_finite_surjective_refinement_of_hasQuasiFiniteSlices
    (h0570 : HasQuasiFiniteSlices.{u}) (H₂ : IntegralHasFinitePresentationLimit.{u})
    {I : Type v} {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage S) :
    ∃ (S' : Scheme.{u}) (g : S' ⟶ S),
      IsFinite g ∧ Surjective g ∧ FinitePresentation g ∧
        ∃ (J : Type u) (U : J → Scheme.{u}) (ι : ∀ c, U c ⟶ S'),
          Presieve.ofArrows U ι ∈ Scheme.zariskiPrecoverage S' ∧
            ∀ c, ∃ i, ∃ t : U c ⟶ X i, ι c ≫ g = t ≫ f i := by
  have hfp : ∀ i, LocallyOfFinitePresentation (f i) := fun i =>
    (((Scheme.ofArrows_mem_precoverage_iff
      (P := @Flat ⊓ @LocallyOfFinitePresentation)).mp hf).2 i).2
  obtain ⟨Y, g, hgint, hgsurj, J, U, ι, hιcover, hιfac⟩ :=
    exists_integral_surjective_refinement_of_mem_fppfPrecoverage h0570 X f hf
  obtain ⟨p⟩ := H₂ Y S g hgint inferInstance inferInstance
  exact @exists_finite_surjective_refinement_of_isLimit I S inferInstance inferInstance X f hfp
    Y g hgint hgsurj J U ι hιcover hιfac p.indexType p.indexPreorder p.indexNonempty
    p.indexDirected p.diagram p.structureMap p.limitCone p.compatible p.isLimit p.stageFinite
    p.stageFinitePresentation

/-- Granted [Stacks, Tag 0570] in the form `AlgebraicGeometry.HasQuasiFiniteSlices` and
[Stacks, Tag 09YZ] in the form `AlgebraicGeometry.IntegralHasFinitePresentationLimit`, the
input that `AlgebraicGeometry.isPHCovering_of_mem_fppfPrecoverage` carries holds.

This is `AlgebraicGeometry.fppfHasFiniteDomination` with its Stacks 0CNZ hypothesis discharged:
composing with `AlgebraicGeometry.isPHCovering_of_mem_fppfPrecoverage` gives
[Stacks, Tag 0DBT], and composing further with
`AlgebraicGeometry.standardVCoveringHasPHRefinement_of_flat` gives the flat case of
[Stacks, Tag 0ETR], both from Stacks 0570 and Stacks 09YZ alone. -/
theorem fppfHasFiniteDomination_of_hasQuasiFiniteSlices
    (h0570 : HasQuasiFiniteSlices.{u}) (H₂ : IntegralHasFinitePresentationLimit.{u}) :
    FppfHasFiniteDomination.{u, v} := by
  intro I _ S hS hS' X f hf
  obtain ⟨S', g, hfin, hsurj, -, J, U, ι, hι, hfac⟩ :=
    @exists_finite_surjective_refinement_of_hasQuasiFiniteSlices h0570 H₂ I S hS hS' X f hf
  exact ⟨S', g, hfin, hsurj, J, U, ι, hι, hfac⟩

end AlgebraicGeometry

end
