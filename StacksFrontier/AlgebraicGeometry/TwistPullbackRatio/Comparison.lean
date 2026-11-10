module

public import StacksFrontier.AlgebraicGeometry.CommonDegreeTwist.AffineSectionBasis
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSections
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Basic
public import StacksFrontier.AlgebraicGeometry.TwistInvertibleOverBase.Basic
public import StacksFrontier.AlgebraicGeometry.TwistPullbackChart.Basic
public import StacksFrontier.AlgebraicGeometry.TwistPullbackChart.Chart

/-!
# The pullback comparison for `𝒪(1)`, pinned on sections

[Stacks, Tag 01NE] identifies morphisms `X ⟶ ℙʳ_ℤ` with pairs `(M, (s₀, …, sᵣ))` of an
invertible `𝒪_X`-module and a generating family of global sections. The direction with geometric
content — the morphism `g` attached to such a pair — is formalized as
`Stacks.ProjectiveFromSections.exists_hom_projectiveSpaceAtUniverse_of_generatesStalks`, and what
the bijection still needs is the identification of `M` with `g ^* 𝒪(1)` **carrying `g ^* Tᵢ` to
`sᵢ`**. This file proves that comparison, as a morphism

`α : g ^* 𝒪(1) ⟶ M`  with  `α(g ^* Tᵢ) = sᵢ` for every `i`.

The pinning is the whole point: a bare isomorphism `M ≅ g ^* 𝒪(1)` says nothing about the
sections and does not give the bijection of the tag.

## The construction

`Tᵢ` is a free generator of `𝒪(1)` over the standard chart `D₊(Tᵢ)` ([Stacks, Tag 01MV]), and the
pinning of `g` puts `X_{sᵢ}` inside `g ⁻¹ᵁ D₊(Tᵢ)`; since the nonvanishing locus of a pulled-back
section is the preimage of the nonvanishing locus ([Stacks, Tag 01CY], [Stacks, Tag 0H78]), the
pulled-back coordinate `g ^* Tᵢ` is a free generator of `g ^* 𝒪(1)` over `X_{sᵢ}`. So over an
open inside `X_{sᵢ}` every section of `g ^* 𝒪(1)` is uniquely `a · g ^* Tᵢ`, and the chart
component of the comparison sends it to `a · sᵢ`.

The chart components agree on overlaps because the two trivializations differ by the *same* unit
on both sides: on `X_{sᵢ}` one has `g ^* Tⱼ = (sⱼ/sᵢ) · g ^* Tᵢ`, matching
`sⱼ = (sⱼ/sᵢ) · sᵢ`. That is the transition identity
`Stacks.TwistPullbackPinned.resT_pullbackCoordSection`, and it is the only arithmetic input: it
comes from `Tⱼ = (Tⱼ/Tᵢ) · Tᵢ` on `D₊(Tᵢ)` pushed along `g` by semilinearity of the unit of the
pullback--pushforward adjunction, the resulting scalar being computed by
`Stacks.TwistPullbackPinned.appLE_coordFrac_chart`. The components then glue by
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover_app`, and the section identity,
checked on the cover, moves to `⊤` by the separation half of the sheaf axiom.

## Main definitions

* `Stacks.TwistPullbackPinned.coordGlobalSection`: `Tᵢ` as a global section of `𝒪(1)` on `ℙʳ_ℤ`.
* `Stacks.TwistPullbackPinned.pullbackCoordSection`: its pullback `g ^* Tᵢ`, a global section of
  `g ^* 𝒪(1)`.
* `Stacks.TwistPullbackPinned.coordFrac`: the degree-zero fraction `Tⱼ/Tᵢ`.
* `Stacks.TwistPullbackPinned.pullbackSectionOn`: a section over an open, pulled back to the
  preimage of that open.
* `Stacks.TwistPullbackPinned.chartApp`: the chart component of the comparison.

## Main results

* `Stacks.TwistPullbackPinned.mem_nonvanishingLocus_coordGlobalSection`: `Tᵢ` does not vanish
  anywhere on `D₊(Tᵢ)`.
* `Stacks.TwistPullbackPinned.nvCover_le_nonvanishingOpen_pullbackCoordSection`: **`g ^* Tᵢ` does
  not vanish anywhere on the chart `X_{sᵢ}`**, hence is a free generator of `g ^* 𝒪(1)` there.
* `Stacks.TwistPullbackPinned.appLE_coordFrac_chart`: **the pullback of `Tⱼ/Tᵢ` along a pinned
  morphism is `sⱼ/sᵢ`.**
* `Stacks.TwistPullbackPinned.resT_pullbackCoordSection`: **the transition identity**
  `g ^* Tⱼ = (sⱼ/sᵢ) · g ^* Tᵢ` on `X_{sᵢ}`.
* `Stacks.TwistPullbackPinned.exists_iso_pullback_twistingSheafAtUniverse`: **the pinned
  comparison, and it is an isomorphism.**
* `Stacks.TwistPullbackPinned.exists_hom_pullback_twistingSheafAtUniverse` and
  `exists_hom_pullback_twistingSheafAtUniverse_of_generatesStalks`: **the pinned comparison**,
  from the nonvanishing-cover hypothesis and from the generation hypothesis respectively.
* `Stacks.TwistPullbackPinned.bijective_chartApp`: the chart component is bijective on sections,
  which is what makes the comparison invertible.
* `Stacks.TwistPullbackPinned.nonempty_iso_pullback_twistingSheafAtUniverse` and
  `Stacks.TwistPullbackPinned.twistPullbackAtUniverse`: **the unpinned form**, i.e.
  `Stacks.TwistPullbackChart.TwistPullbackAtUniverse`, which
  `Stacks.TwistPullbackChart.twistPullback_of_atUniverse` turns into
  `Stacks.AmpleImmersionReduction.TwistPullback f` for every `f : X ⟶ S`.
* `Stacks.TwistPullbackPinned.div_add`, `div_smul_scalar`, `resO_div`, `div_smul_self`: the
  arithmetic of division by a nonvanishing section, which makes the chart component additive,
  linear and compatible with restriction.

## Implementation notes

**Two chart identities are reproved rather than imported.**
`Stacks.TwistPullbackRatio.appLE_awayToSection`, `projAwayHom_coordFraction` and
`degreeSection_res_eq` are the same statements as
`Stacks.TwistPullbackPinned.appLE_awayToSection'`, `projAwayHom_coordFrac` and
`coordGlobalSection_res_eq` (the last specialised to the homogeneous coordinate ring), with the
same proofs. They are restated because the sibling file's import closure reaches modules that do
not elaborate inside the memory budget of the machine this was developed on, while every input
those three proofs use — `Stacks.ProjGlobalSectionsAppTop.toBasicOpenOfGlobalSections_appTop`,
`projAwayHom_apply_mk_of_mul_eq_one`, `topIso_inv_resLE_appTop` and
`Stacks.AlgebraicGeometry.ProjTwistSections.degreeSection_apply` — is reachable without them.

**The index type of the cover.**
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover_app` indexes its cover by a
`Type u`, while the sections are indexed by `Fin (r + 1) : Type 0`, so the cover is reindexed by
`ULift (Fin (r + 1))`.

**Transparency.** `AlgebraicGeometry.projectiveSpaceAtUniverse` is declared
`implicit_reducible` locally: without it `rw` refuses the goals that mention both
`ℙʳ_ℤ` and `Proj (coordGrading r)`, the motive failing to be type-correct at `implicit`
transparency although the two schemes are the same term.

**No `@[stacks ...]` attribute is attached.** Tag 01NE is a representability statement and nothing
below is one of its assertions; the inverse construction and the bijection are not here. Tag 01MV
already carries its attribute at
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.nonvanishingLocus_degreeSection_inter` and Tag 0H78
at `Stacks.NonvanishingPullback.preimage_nonvanishingLocus`, and nothing below restates either.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01MV](https://stacks.math.columbia.edu/tag/01MV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open HomogeneousLocalization
open Stacks.ProjGlobalSectionsAppTop
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AmpleProjectiveImmersion Stacks.ProjectiveFromSections
open Stacks.SectionsToProjectiveSpace

universe u

namespace Stacks.TwistPullbackPinned

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse

/-! ### The homogeneous coordinates as global sections of `𝒪(1)` -/

/-- The `i`-th homogeneous coordinate `Tᵢ`, as a global section of `𝒪(1)` on `ℙⁿ_ℤ`. -/
def coordGlobalSection (n : ℕ) (i : Fin (n + 1)) : Γ(twistingSheafAtUniverse.{u} n, ⊤) :=
  degreeSection (coordGrading.{u} n) 1 ⟨MvPolynomial.X i, X_mem_coordGrading_one i⟩

/-- **Every twist is invertible at every point of `ℙⁿ_ℤ`**: the homogeneous coordinate ring is
generated in degree one, so the open `W₁` of [Stacks, Tag 01MU] is everything. -/
theorem whereInvertible_coordGrading_eq_top (n : ℕ) :
    Stacks.AlgebraicGeometry.ProjInvertibleLocus.whereInvertible (coordGrading.{u} n) 1 = ⊤ :=
  (Stacks.AlgebraicGeometry.GoodOpenClose.whereInvertible_eq_ratioLocus (coordGrading.{u} n)
    1).trans
    (Stacks.AlgebraicGeometry.ProjShared.ratioLocus_eq_top_of_adjoin_degree_one
      (coordGrading.{u} n)
      (Stacks.AlgebraicGeometry.TwistFlatness.adjoin_degree_one_homogeneousSubmodule
        (Fin (n + 1)) (ULift.{u} ℤ)) 1)

/-- **`Tᵢ` does not vanish anywhere on the standard chart `D₊(Tᵢ)`.** This is [Stacks, Tag 01MV]
at `d = n = 1`, available over all of `ℙⁿ_ℤ` because the coordinate ring is generated in degree
one. -/
theorem mem_nonvanishingLocus_coordGlobalSection {n : ℕ} (i : Fin (n + 1))
    {y : projectiveSpaceAtUniverse.{u} n}
    (hy : y ∈ AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) :
    y ∈ Stacks.Ample.nonvanishingLocus (twistingSheafAtUniverse.{u} n)
      (coordGlobalSection.{u} n i) :=
  (Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'
    (coordGrading.{u} n) 1 1 ⟨MvPolynomial.X i, X_mem_coordGrading_one i⟩
    (by rw [whereInvertible_coordGrading_eq_top]; trivial)).mpr hy

/-! ### The pulled-back coordinate sections -/

/-- **`g ^* 𝒪(1)` is invertible**, for every morphism `g` to the integral model of projective
space. This is the absolute companion of
`Stacks.TwistInvertibleOverBase.isInvertibleModule_pullback_projectiveSpaceTwistingSheaf`. -/
instance isInvertibleModule_pullback_twistingSheafAtUniverse {X : Scheme.{u}} {n : ℕ}
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) :
    Stacks.Ample.IsInvertibleModule X
      ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n)) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback g (twistingSheafAtUniverse.{u} n)

/-- The pullback along `g : X ⟶ ℙⁿ_ℤ` of the `i`-th homogeneous coordinate, a global section of
`g ^* 𝒪(1)`. -/
def pullbackCoordSection {X : Scheme.{u}} {n : ℕ} (g : X ⟶ projectiveSpaceAtUniverse.{u} n)
    (i : Fin (n + 1)) :
    Γ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n), ⊤) :=
  pullbackGlobalSections g (twistingSheafAtUniverse.{u} n) (coordGlobalSection.{u} n i)

/-- **The pullback of a global section does not vanish where the section does not vanish.** This
is [Stacks, Tag 0H78] with the pullback written at the `AlgebraicGeometry.Scheme.Modules`
spelling and the section as `AlgebraicGeometry.pullbackGlobalSections`. -/
theorem mem_nonvanishingLocus_pullbackGlobalSections {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (s : Γ(M, ⊤)) {x : X}
    (hx : f.base x ∈ Stacks.Ample.nonvanishingLocus M s) :
    x ∈ Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback f).obj M)
      (pullbackGlobalSections f M s) := by
  have hsec : pullbackGlobalSections f M s =
      Stacks.NonvanishingPullback.pullbackGlobalSection f M s := by
    change ((Scheme.Modules.pullback f).obj M).presheaf.map
        (eqToHom (show f ⁻¹ᵁ (⊤ : Y.Opens) = ⊤ from rfl)).op
        (Stacks.NonvanishingPullback.pullbackGlobalSection f M s) = _
    exact Functor.map_id_apply _ _ _
  rw [hsec]
  exact (Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff f M s x).mpr hx

/-- **A pinned chart maps into the matching standard chart of `ℙⁿ_ℤ`.** The restriction of `g` to
`X_{sᵢ}` is the morphism of the ratio family out of `sᵢ`, whose `i`-th member is `1`, so its
image misses no `Tᵢ`. -/
theorem nvCover_le_preimage_basicOpen {X : Scheme.{u}} {n : ℕ} {M : X.Modules}
    [Stacks.Ample.IsInvertibleModule X M] (s : Fin (n + 1) → Γ(M, ⊤))
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) (i : Fin (n + 1))
    (hpin : (nvCover s i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i)) :
    nvCover s i ≤
      g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) := by
  intro x hx
  obtain ⟨y, rfl⟩ : x ∈ Set.range (nvCover s i).ι.base :=
    (Scheme.Opens.range_ι (U := nvCover s i)).ge hx
  have hmem : g.base ((nvCover s i).ι.base y) ∈
      Set.range (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)).ι.base :=
    Stacks.TwistPullbackChart.range_comp_subset_chart g (nvCover s i) (chartRatio s i)
      (span_range_chartRatio s i) i (chartRatio_self s i) hpin ⟨y, rfl⟩
  exact (Scheme.Opens.range_ι
    (U := AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))).le hmem

/-- **The pulled-back coordinate `g ^* Tᵢ` does not vanish anywhere on the chart `X_{sᵢ}`.**

This is the step that consumes the pinning: the chart maps into `D₊(Tᵢ)`, where `Tᵢ` is a local
frame of `𝒪(1)`, and the nonvanishing locus of a pulled-back section is the preimage of the
nonvanishing locus. -/
theorem nvCover_le_nonvanishingOpen_pullbackCoordSection {X : Scheme.{u}} {n : ℕ}
    {M : X.Modules} [Stacks.Ample.IsInvertibleModule X M] (s : Fin (n + 1) → Γ(M, ⊤))
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) (i : Fin (n + 1))
    (hpin : (nvCover s i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i)) :
    nvCover s i ≤ nvOpen ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n))
      (pullbackCoordSection.{u} g i) := by
  intro x hx
  exact mem_nonvanishingLocus_pullbackGlobalSections g (twistingSheafAtUniverse.{u} n)
    (coordGlobalSection.{u} n i)
    (mem_nonvanishingLocus_coordGlobalSection i (nvCover_le_preimage_basicOpen s g i hpin hx))

/-! ### The degree-zero coordinate fractions on a chart -/

section Fractions

variable {V : Scheme.{u}} {n : ℕ}

/-- The degree-zero fraction `Tⱼ / Tᵢ`. -/
def coordFrac (i j : Fin (n + 1)) : Away (coordGrading.{u} n) (MvPolynomial.X i) :=
  Away.mk (coordGrading.{u} n) (X_mem_coordGrading_one i) 1 (MvPolynomial.X j)
    (by simpa using X_mem_coordGrading_one j)

/-- On the basic open of `Tᵢ`, the map induced by `toProjectiveSpaceAtUniverse t ht` sends a
degree-zero fraction `z` of the localization at `Tᵢ` to its image under `projAwayHom`, i.e. to the
fraction obtained by substituting `t` for the coordinates. -/
theorem appLE_awayToSection' (t : Fin (n + 1) → Γ(V, ⊤))
    (ht : Ideal.span (Set.range t) = ⊤) (i : Fin (n + 1))
    (z : Away (coordGrading.{u} n) (MvPolynomial.X i)) :
    (toProjectiveSpaceAtUniverse t ht).appLE
          (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
          (V.basicOpen (sectionsHom t (MvPolynomial.X i)))
          (Proj.fromOfGlobalSections_preimage_basicOpen (coordGrading.{u} n) (sectionsHom t)
            (map_irrelevant_eq_top t ht) Nat.one_pos (X_mem_coordGrading_one i)).ge
        ((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)).hom z) =
      projAwayHom (coordGrading.{u} n) (sectionsHom t) z := by
  have h1 := topIso_inv_resLE_appTop (toProjectiveSpaceAtUniverse t ht)
    (U := AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
    (V := V.basicOpen (sectionsHom t (MvPolynomial.X i)))
    (Proj.fromOfGlobalSections_preimage_basicOpen (coordGrading.{u} n) (sectionsHom t)
      (map_irrelevant_eq_top t ht) Nat.one_pos (X_mem_coordGrading_one i)).ge
  rw [resLE_toProjectiveSpaceAtUniverse t ht i] at h1
  have h2 := toBasicOpenOfGlobalSections_appTop (coordGrading.{u} n) (sectionsHom t)
    Nat.one_pos (X_mem_coordGrading_one i)
  have h3 := (congrArg (fun k => (AlgebraicGeometry.Proj.basicOpenIsoAway (coordGrading.{u} n)
      (MvPolynomial.X i) (X_mem_coordGrading_one i) Nat.one_pos).hom ≫ k) h1).symm.trans h2
  have h5 := (cancel_mono
    ((V.basicOpen (sectionsHom t (MvPolynomial.X i))).topIso.inv)).mp
      ((Category.assoc _ _ _).trans h3)
  exact CategoryTheory.ConcreteCategory.congr_hom h5 z

/-- When `t i = 1`, substituting `t` into the fraction `Tⱼ / Tᵢ` gives the restriction of `t j`
to the basic open of `t i`. -/
theorem projAwayHom_coordFrac (t : Fin (n + 1) → Γ(V, ⊤)) (i j : Fin (n + 1))
    (hti : t i = 1) :
    projAwayHom (coordGrading.{u} n) (sectionsHom t) (coordFrac.{u} i j) =
      resTop (V.basicOpen (sectionsHom t (MvPolynomial.X i))) (t j) := by
  have h1 : sectionsHom t (MvPolynomial.X i) = 1 := by rw [sectionsHom_X, hti]
  have hv : resTop (V.basicOpen (sectionsHom t (MvPolynomial.X i)))
      (sectionsHom t (MvPolynomial.X i)) * 1 = 1 := by rw [h1, map_one, mul_one]
  rw [coordFrac, projAwayHom_apply_mk_of_mul_eq_one (coordGrading.{u} n) (sectionsHom t)
    (X_mem_coordGrading_one i) 1 (MvPolynomial.X j) _ hv, one_pow, mul_one]
  simp only [sectionsHom_X]

/-- When `t i = 1`, the morphism `toProjectiveSpaceAtUniverse t ht` pulls the section `Tⱼ / Tᵢ`
of the basic open of `Tᵢ` back to the global section `t j`. -/
theorem appLE_top_coordFrac (t : Fin (n + 1) → Γ(V, ⊤)) (ht : Ideal.span (Set.range t) = ⊤)
    (i j : Fin (n + 1)) (hti : t i = 1)
    (e : (⊤ : V.Opens) ≤ toProjectiveSpaceAtUniverse t ht ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) :
    (toProjectiveSpaceAtUniverse t ht).appLE
        (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) ⊤ e
        ((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)).hom
          (coordFrac.{u} i j)) = t j := by
  have hb : V.basicOpen (sectionsHom t (MvPolynomial.X i)) = ⊤ := by
    rw [sectionsHom_X, hti]; exact Scheme.basicOpen_one V
  have hmap := Scheme.Hom.appLE_map (f := toProjectiveSpaceAtUniverse t ht)
    (U := AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
    (V := V.basicOpen (sectionsHom t (MvPolynomial.X i))) (V' := ⊤)
    (Proj.fromOfGlobalSections_preimage_basicOpen (coordGrading.{u} n) (sectionsHom t)
      (map_irrelevant_eq_top t ht) Nat.one_pos (X_mem_coordGrading_one i)).ge
    (homOfLE hb.ge).op
  have hz := CategoryTheory.ConcreteCategory.congr_hom hmap
    ((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)).hom
      (coordFrac.{u} i j))
  rw [← hz]
  rw [CategoryTheory.ConcreteCategory.comp_apply, appLE_awayToSection' t ht i,
    projAwayHom_coordFrac t i j hti]
  change V.presheaf.map (homOfLE hb.ge).op
      (V.presheaf.map (homOfLE (le_top (a := V.basicOpen (sectionsHom t (MvPolynomial.X i))))).op
        (t j)) = t j
  rw [← CategoryTheory.Functor.map_comp_apply]
  exact Functor.map_id_apply _ _ _


end Fractions

/-! ### Pulled-back sections over an open -/

section PullbackSections

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules)

/-- **A section of `F` over an open `T`, pulled back to `f ^* F` over the preimage of `T`**: its
image under the unit of the pullback--pushforward adjunction. -/
def pullbackSectionOn (T : Y.Opens) (t : Γ(F, T)) :
    Γ((Scheme.Modules.pullback f).obj F, f ⁻¹ᵁ T) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app T t

/-- **The unit of the pullback--pushforward adjunction is semilinear on sections**: a pulled-back
scalar multiple is the pullback of the scalar times the pulled-back section. -/
theorem pullbackSectionOn_smul (T : Y.Opens) (r : Γ(Y, T)) (t : Γ(F, T)) :
    pullbackSectionOn f F T (r • t) = f.app T r • pullbackSectionOn f F T t :=
  Scheme.Modules.Hom.app_smul _ r t

/-- **Pulling back a section commutes with restriction to a smaller open.** -/
theorem pullbackSectionOn_res {T T' : Y.Opens} (h : T' ≤ T) (t : Γ(F, T)) :
    pullbackSectionOn f F T' (F.presheaf.map (homOfLE h).op t) =
      ((Scheme.Modules.pullback f).obj F).presheaf.map
        (homOfLE (show f ⁻¹ᵁ T' ≤ f ⁻¹ᵁ T from ((Opens.map f.base).map (homOfLE h)).le)).op
        (pullbackSectionOn f F T t) :=
  PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val (homOfLE h).op t

/-- Pulling back a *global* section is `AlgebraicGeometry.pullbackGlobalSections`. -/
theorem pullbackSectionOn_top (t : Γ(F, ⊤)) :
    pullbackSectionOn f F ⊤ t = pullbackGlobalSections f F t := by
  refine Eq.symm ?_
  change ((Scheme.Modules.pullback f).obj F).presheaf.map
      (eqToHom (show f ⁻¹ᵁ (⊤ : Y.Opens) = ⊤ from rfl)).op (pullbackSectionOn f F ⊤ t) = _
  exact Functor.map_id_apply _ _ _

/-- **Restricting a pulled-back global section** is pulling back its restriction. -/
theorem pullbackGlobalSections_res (T' : Y.Opens) (t : Γ(F, ⊤)) :
    pullbackSectionOn f F T' (F.presheaf.map (homOfLE (le_top : T' ≤ ⊤)).op t) =
      ((Scheme.Modules.pullback f).obj F).presheaf.map
        (homOfLE (le_top : f ⁻¹ᵁ T' ≤ ⊤)).op (pullbackGlobalSections f F t) := by
  rw [← pullbackSectionOn_top]
  exact pullbackSectionOn_res f F le_top t

end PullbackSections

/-! ### The coordinate sections on a chart -/

section Res

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- **On the standard chart `D₊(Tᵢ)` the coordinate section `Tⱼ` of `𝒪(1)` is the degree-zero
fraction `Tⱼ/Tᵢ` times the coordinate section `Tᵢ`.**

Both sides are compared pointwise: the value of a degree-one section at a point is the fraction
`Tₖ/1`, the value of the fraction is itself, and the scalar action on the twisting sheaf is
multiplication of values, so what is left is `Tⱼ/1 = (Tⱼ/Tᵢ) · (Tᵢ/1)` in the local ring. -/
theorem coordGlobalSection_res_eq (n : ℕ) (i j : Fin (n + 1)) :
    (twistingSheafAtUniverse.{u} n).presheaf.map
        (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n)
          (MvPolynomial.X i)))).op (coordGlobalSection.{u} n j) =
      (AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)).hom
          (coordFrac.{u} i j) •
        (twistingSheafAtUniverse.{u} n).presheaf.map
          (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n)
            (MvPolynomial.X i)))).op (coordGlobalSection.{u} n i) := by
  refine Subtype.ext (funext fun x => ?_)
  have hx := x.1.isPrime
  have hk : ∀ k : Fin (n + 1), ((twistingSheafAtUniverse.{u} n).presheaf.map
        (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n)
          (MvPolynomial.X i)))).op (coordGlobalSection.{u} n k)).1 x =
      Localization.mk (MvPolynomial.X k : coordRing.{u} n) 1 := fun k =>
    degreeSection_apply (coordGrading.{u} n) 1 ⟨MvPolynomial.X k, X_mem_coordGrading_one k⟩ _
  have hR : ((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n)
            (MvPolynomial.X i)).hom (coordFrac.{u} i j) •
        (twistingSheafAtUniverse.{u} n).presheaf.map
          (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n)
            (MvPolynomial.X i)))).op (coordGlobalSection.{u} n i)).1 x =
      HomogeneousLocalization.val
          (((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n)
            (MvPolynomial.X i)).hom (coordFrac.{u} i j)).1 x) *
        ((twistingSheafAtUniverse.{u} n).presheaf.map
          (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n)
            (MvPolynomial.X i)))).op (coordGlobalSection.{u} n i)).1 x := rfl
  have hval : HomogeneousLocalization.val
      (((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n)
        (MvPolynomial.X i)).hom (coordFrac.{u} i j)).1 x) =
      Localization.mk (MvPolynomial.X j : coordRing.{u} n)
        ⟨(MvPolynomial.X i : coordRing.{u} n) ^ 1, _⟩ := rfl
  rw [hk j, hR, hval, hk i, Localization.mk_mul]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp; ring))

end Res

/-! ### Sections of the structure sheaf over a chart -/

/-- **The restriction to an open subscheme of a pulled-back section of the structure sheaf.**
Composing `g ^♯ : Γ(Z, D) ⟶ Γ(X, U)` with the identification `Γ(X, U) ≅ Γ(U, ⊤)` gives the
structure map of the composite `U ⟶ X ⟶ Z`. -/
theorem appLE_comp_topIso_inv {X Z : Scheme.{u}} (g : X ⟶ Z) (U : X.Opens) (D : Z.Opens)
    (e : U ≤ g ⁻¹ᵁ D) :
    g.appLE D U e ≫ U.topIso.inv =
      (U.ι ≫ g).appLE D ⊤
        (le_trans (Stacks.AlgebraicGeometry.ProjTwistMono.preimage_self_eq_top U).ge
          ((Opens.map U.ι.base).map (homOfLE e)).le) := by
  have hι : U.ι.appLE U ⊤ (Stacks.AlgebraicGeometry.ProjTwistMono.preimage_self_eq_top U).ge =
      U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE]; rfl
  rw [← hι]
  exact Scheme.Hom.appLE_comp_appLE U.ι g D U ⊤ e
    (Stacks.AlgebraicGeometry.ProjTwistMono.preimage_self_eq_top U).ge

/-- Two morphisms that are equal have the same effect on sections over an open. -/
theorem appLE_congr_hom {X Z : Scheme.{u}} {f f' : X ⟶ Z} (h : f = f') (D : Z.Opens)
    (W : X.Opens) (e : W ≤ f ⁻¹ᵁ D) (e' : W ≤ f' ⁻¹ᵁ D) : f.appLE D W e = f'.appLE D W e' := by
  subst h; rfl

/-- The identification of the sections of `𝒪_X` over an open with the global sections of the open
subscheme is injective. -/
theorem topIso_inv_injective {X : Scheme.{u}} (U : X.Opens) :
    Function.Injective (CategoryTheory.ConcreteCategory.hom U.topIso.inv) := by
  intro a b h
  have h2 := congrArg (CategoryTheory.ConcreteCategory.hom U.topIso.hom) h
  rwa [← CategoryTheory.ConcreteCategory.comp_apply, ← CategoryTheory.ConcreteCategory.comp_apply,
    U.topIso.inv_hom_id, CategoryTheory.ConcreteCategory.id_apply,
    CategoryTheory.ConcreteCategory.id_apply] at h2

/-- **The pullback along a pinned morphism of the degree-zero fraction `Tⱼ/Tᵢ` is the ratio
`sⱼ/sᵢ`.**

This is the arithmetic heart of the comparison: on the chart `X_{sᵢ}` the morphism `g` is the
morphism of the ratio family out of `sᵢ`, whose `i`-th member is `1`, so the chart's ring
homomorphism sends `Tⱼ/Tᵢ` to `sⱼ/sᵢ`. -/
theorem appLE_coordFrac_chart {X : Scheme.{u}} {n : ℕ} {M : X.Modules}
    [Stacks.Ample.IsInvertibleModule X M] (s : Fin (n + 1) → Γ(M, ⊤))
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) (i j : Fin (n + 1))
    (hpin : (nvCover s i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i)) :
    g.appLE (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
        (nvCover s i) (nvCover_le_preimage_basicOpen s g i hpin)
        ((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)).hom
          (coordFrac.{u} i j)) = ratio s i j := by
  refine topIso_inv_injective (nvCover s i) ?_
  have h1 := CategoryTheory.ConcreteCategory.congr_hom
    (appLE_comp_topIso_inv g (nvCover s i)
      (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
      (nvCover_le_preimage_basicOpen s g i hpin))
    ((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)).hom
      (coordFrac.{u} i j))
  rw [CategoryTheory.ConcreteCategory.comp_apply] at h1
  refine h1.trans ?_
  have e' : (⊤ : (nvCover s i).toScheme.Opens) ≤
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) := by
    rw [preimage_basicOpen (chartRatio s i) (span_range_chartRatio s i) i, chartRatio_self,
      Scheme.basicOpen_one (nvCover s i).toScheme]
  rw [appLE_congr_hom hpin
    (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) ⊤ _ e']
  exact appLE_top_coordFrac (chartRatio s i) (span_range_chartRatio s i) i j
    (chartRatio_self s i) _

/-! ### The transition identity between the pulled-back coordinates -/


/-- `AlgebraicGeometry.Scheme.Hom.appLE` is the structure map followed by restriction. -/
theorem appLE_apply {X Z : Scheme.{u}} (g : X ⟶ Z) (D : Z.Opens) (W : X.Opens)
    (e : W ≤ g ⁻¹ᵁ D) (z : Γ(Z, D)) :
    g.appLE D W e z = X.presheaf.map (homOfLE e).op (g.app D z) :=
  CategoryTheory.ConcreteCategory.comp_apply _ _ z

/-- A relation `t = a • u` between restrictions of global sections restricts to a smaller open. -/
private theorem resT_eq_smul_of_le {X : Scheme.{u}} {L : X.Modules} {W W' : X.Opens} (h : W' ≤ W)
    {a : Γ(X, W)} {t u : Γ(L, ⊤)} (H : resT W t = a • resT W u) :
    resT W' t = resO h a • resT W' u := by
  have h2 := congrArg (resM h) H
  rwa [resM_smul, resM_resT, resM_resT] at h2

/-- **The transition identity for the pulled-back coordinates.** On the chart `X_{sᵢ}` the
pulled-back coordinate `g ^* Tⱼ` is the ratio `sⱼ/sᵢ` times `g ^* Tᵢ`.

This is the cocycle identification the comparison is glued from: it is the identity
`Tⱼ = (Tⱼ/Tᵢ) · Tᵢ` on `D₊(Tᵢ)`, pushed along `g` by semilinearity of the unit of the
pullback--pushforward adjunction, with the resulting scalar computed by
`Stacks.TwistPullbackPinned.appLE_coordFrac_chart`. -/
theorem resT_pullbackCoordSection {X : Scheme.{u}} {n : ℕ} {M : X.Modules}
    [Stacks.Ample.IsInvertibleModule X M] (s : Fin (n + 1) → Γ(M, ⊤))
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) (i j : Fin (n + 1))
    (hpin : (nvCover s i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i)) :
    resT (nvCover s i) (pullbackCoordSection.{u} g j) =
      ratio s i j • resT (nvCover s i) (pullbackCoordSection.{u} g i) := by
  have hle := nvCover_le_preimage_basicOpen s g i hpin
  have key := congrArg (pullbackSectionOn g (twistingSheafAtUniverse.{u} n)
    (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)))
    (coordGlobalSection_res_eq.{u} n i j)
  rw [pullbackSectionOn_smul, pullbackGlobalSections_res, pullbackGlobalSections_res] at key
  have h2 := resT_eq_smul_of_le hle key
  have hs : resO hle
      ((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n)
        (MvPolynomial.X i)).hom (coordFrac.{u} i j) |>
          (g.app (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n)
            (MvPolynomial.X i)))) = ratio s i j :=
    (appLE_apply g _ _ hle _).symm.trans (appLE_coordFrac_chart s g i j hpin)
  rw [hs] at h2
  exact h2

/-! ### Division by a nonvanishing section, on sections -/

section Div

variable {X : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- Division by a nonvanishing section is additive. -/
theorem div_add (t : Γ(L, ⊤)) {W : X.Opens} (hW : W ≤ nvOpen L t) (a b : Γ(L, W)) :
    div t hW (a + b) = div t hW a + div t hW b :=
  (eq_div t hW (by rw [add_smul, div_smul, div_smul])).symm

/-- Division by a nonvanishing section is linear. -/
theorem div_smul_scalar (t : Γ(L, ⊤)) {W : X.Opens} (hW : W ≤ nvOpen L t) (r : Γ(X, W))
    (a : Γ(L, W)) : div t hW (r • a) = r * div t hW a :=
  (eq_div t hW (by rw [mul_smul, div_smul])).symm

/-- Division by a nonvanishing section commutes with restriction. -/
theorem resO_div (t : Γ(L, ⊤)) {W W' : X.Opens} (hW : W ≤ nvOpen L t) (h : W' ≤ W)
    (a : Γ(L, W)) : resO h (div t hW a) = div t (h.trans hW) (resM h a) :=
  eq_div t (h.trans hW) (by rw [← resM_resT h t, ← resM_smul, div_smul])

/-- The ratio of a multiple of the divisor is the multiplier. -/
@[simp] theorem div_smul_self (t : Γ(L, ⊤)) {W : X.Opens} (hW : W ≤ nvOpen L t) (r : Γ(X, W)) :
    div t hW (r • resT W t) = r := (eq_div t hW rfl).symm

/-- **Division by a nonvanishing section is a bijection on sections**: it is the inverse of
multiplication by that section. -/
theorem bijective_div (t : Γ(L, ⊤)) {W : X.Opens} (hW : W ≤ nvOpen L t) :
    Function.Bijective (div t hW) :=
  ⟨fun a b h => by rw [← div_smul t hW a, ← div_smul t hW b, h],
    fun c => ⟨c • resT W t, (eq_div t hW rfl).symm⟩⟩

end Div

/-! ### The pinned comparison -/

section Comparison

variable {X : Scheme.{u}} {n : ℕ} {M : X.Modules} [Stacks.Ample.IsInvertibleModule X M]
  (s : Fin (n + 1) → Γ(M, ⊤)) (g : X ⟶ projectiveSpaceAtUniverse.{u} n)

/-- **The chart component of the comparison.** Over an open inside `X_{sᵢ}` every section of
`g ^* 𝒪(1)` is a unique multiple of `g ^* Tᵢ`, and the comparison sends it to the same multiple
of `sᵢ`. -/
def chartApp (i : Fin (n + 1))
    (hpi : (nvCover s i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i))
    (V : X.Opens) (hV : V ≤ nvCover s i) :
    Γ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n), V) ⟶ Γ(M, V) :=
  CategoryTheory.ConcreteCategory.ofHom
    (AddMonoidHom.mk'
      (fun x => div (pullbackCoordSection.{u} g i)
        (hV.trans (nvCover_le_nonvanishingOpen_pullbackCoordSection s g i hpi)) x • resT V (s i))
      fun x y => by rw [div_add, add_smul])

/-- `chartApp` sends a section `x` to `x / g ^* Tᵢ` times the restriction of `sᵢ`. -/
@[simp] theorem chartApp_apply (i : Fin (n + 1))
    (hpi : (nvCover s i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i))
    (V : X.Opens) (hV : V ≤ nvCover s i)
    (x : Γ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n), V)) :
    chartApp s g i hpi V hV x =
      div (pullbackCoordSection.{u} g i)
        (hV.trans (nvCover_le_nonvanishingOpen_pullbackCoordSection s g i hpi)) x •
          resT V (s i) := by simp [chartApp]

/-- **The ratio of two pulled-back coordinates on an overlap.** Over an open inside both
`X_{sᵢ}` and `X_{sⱼ}`, dividing by `g ^* Tᵢ` and dividing by `g ^* Tⱼ` differ by `sᵢ/sⱼ`. -/
theorem div_pullbackCoordSection_eq {i j : Fin (n + 1)}
    (hpj : (nvCover s j).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s j) (span_range_chartRatio s j))
    {V : X.Opens} (hVj : V ≤ nvCover s j)
    (hi : V ≤ nvOpen ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n))
      (pullbackCoordSection.{u} g i))
    (hj : V ≤ nvOpen ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n))
      (pullbackCoordSection.{u} g j))
    (x : Γ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n), V)) :
    div (pullbackCoordSection.{u} g j) hj x =
      div (pullbackCoordSection.{u} g i) hi x * resO hVj (ratio s j i) := by
  have hE : resT V (pullbackCoordSection.{u} g i) =
      resO hVj (ratio s j i) • resT V (pullbackCoordSection.{u} g j) :=
    resT_eq_smul_of_le hVj (resT_pullbackCoordSection s g j i hpj)
  refine (eq_div _ _ ?_).symm
  rw [mul_smul, ← hE, div_smul]

/-- The chart components agree on overlaps: the two comparisons differ by the unit `sⱼ/sᵢ` on
one side and by `g ^* (Tⱼ/Tᵢ)` on the other, and these cancel. -/
theorem chartApp_smul (i : Fin (n + 1))
    (hpi : (nvCover s i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i))
    (V : X.Opens) (hV : V ≤ nvCover s i) (r : Γ(X, V))
    (x : Γ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n), V)) :
    chartApp s g i hpi V hV (r • x) = r • chartApp s g i hpi V hV x := by
  rw [chartApp_apply, chartApp_apply, div_smul_scalar, mul_smul]

/-- The chart components commute with restriction. -/
theorem chartApp_res (i : Fin (n + 1))
    (hpi : (nvCover s i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i))
    (V W : X.Opens) (hV : V ≤ nvCover s i) (hWV : W ≤ V)
    (x : Γ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n), V)) :
    chartApp s g i hpi W (hWV.trans hV) (resM hWV x) = resM hWV (chartApp s g i hpi V hV x) := by
  rw [chartApp_apply, chartApp_apply, resM_smul, resO_div, resM_resT]

/-- The chart components agree on overlaps. -/
theorem chartApp_agree (i j : Fin (n + 1))
    (hpi : (nvCover s i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i))
    (hpj : (nvCover s j).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s j) (span_range_chartRatio s j))
    (V : X.Opens) (hVi : V ≤ nvCover s i) (hVj : V ≤ nvCover s j) :
    chartApp s g i hpi V hVi = chartApp s g j hpj V hVj := by
  refine CategoryTheory.ConcreteCategory.hom_ext _ _ fun x => ?_
  rw [chartApp_apply, chartApp_apply,
    div_pullbackCoordSection_eq s g hpj hVj
      (hVi.trans (nvCover_le_nonvanishingOpen_pullbackCoordSection s g i hpi))
      (hVj.trans (nvCover_le_nonvanishingOpen_pullbackCoordSection s g j hpj)) x,
    mul_smul, resO_ratio_smul s hVj i]

/-- **The chart component is bijective on sections**: it is division by `g ^* Tᵢ` followed by
multiplication by `sᵢ`, and both are bijections over an open inside `X_{sᵢ}`. -/
theorem bijective_chartApp (i : Fin (n + 1))
    (hpi : (nvCover s i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i))
    (V : X.Opens) (hV : V ≤ nvCover s i) :
    Function.Bijective
      (CategoryTheory.ConcreteCategory.hom (chartApp s g i hpi V hV)) := by
  have hfun : (CategoryTheory.ConcreteCategory.hom (chartApp s g i hpi V hV)) =
      (fun a : Γ(X, V) => a • resT V (s i)) ∘
        div (pullbackCoordSection.{u} g i)
          (hV.trans (nvCover_le_nonvanishingOpen_pullbackCoordSection s g i hpi)) :=
    funext fun x => chartApp_apply s g i hpi V hV x
  rw [hfun]
  exact (Stacks.NonvanishingSpelling.bijective_smul X M (s i) hV).comp (bijective_div _ _)

/-- **The twist half of [Stacks, Tag 01NE], pinned on sections.** Let `M` be an invertible
`𝒪_X`-module, `s₀, …, sᵣ` global sections whose nonvanishing opens cover `X`, and let
`g : X ⟶ ℙʳ_ℤ` restrict on each chart `X_{sᵢ}` to the morphism of the ratio family `sₖ/sᵢ`. Then
there is a morphism `g ^* 𝒪(1) ⟶ M` carrying the pullback of the `i`-th homogeneous coordinate
to `sᵢ`, for every `i`.

The morphism is glued from the chart components `Stacks.TwistPullbackPinned.chartApp`, which
agree on overlaps by the transition identity
`Stacks.TwistPullbackPinned.resT_pullbackCoordSection`; the section identity is checked on the
cover and transferred to `⊤` by the separation half of the sheaf axiom. -/
theorem exists_iso_pullback_twistingSheafAtUniverse (hcov : IsOpenCover (nvCover s))
    (hpin : ∀ i, (nvCover s i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i)) :
    ∃ α : (Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n) ⟶ M,
      IsIso α ∧ ∀ i, α.app ⊤ (pullbackCoordSection.{u} g i) = s i := by
  classical
  have hU : ⨆ k : ULift.{u} (Fin (n + 1)), nvCover s k.down = ⊤ :=
    top_le_iff.mp (hcov.ge.trans
      (iSup_le fun i =>
        le_iSup (fun k : ULift.{u} (Fin (n + 1)) => nvCover s k.down) (ULift.up i)))
  obtain ⟨α, hα, -⟩ := Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover_app hU
    (fun k V hV => chartApp s g k.down (hpin k.down) V hV)
    (fun k V hV r x => chartApp_smul s g k.down (hpin k.down) V hV r x)
    (fun k V W hV hWV x => chartApp_res s g k.down (hpin k.down) V W hV hWV x)
    (fun k l V hVk hVl =>
      chartApp_agree s g k.down l.down (hpin k.down) (hpin l.down) V hVk hVl)
  have hmem : ∀ x : ↥X, ∃ i, x ∈ nvCover s i := fun x =>
    TopologicalSpace.Opens.mem_iSup.mp (by rw [hcov]; trivial)
  choose idx hidx using hmem
  refine ⟨α, ?_, fun i => ?_⟩
  · refine Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun U =>
      (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr ?_
    refine Stacks.AlgebraicGeometry.ProjTwistMono.bijective_app_of_locally α
      (fun x => nvCover s (idx x)) hidx (fun x W hW => ?_) U
    rw [hα (ULift.up (idx x)) W hW]
    exact bijective_chartApp s g (idx x) (hpin (idx x)) W hW
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf M.isSheaf
    (fun k : ULift.{u} (Fin (n + 1)) => nvCover s k.down) (fun _ => le_top) hU.ge fun k => ?_
  have hnat : resM (le_top : nvCover s k.down ≤ ⊤)
      (α.app ⊤ (pullbackCoordSection.{u} g i)) =
      α.app (nvCover s k.down) (resT (nvCover s k.down) (pullbackCoordSection.{u} g i)) :=
    (PresheafOfModules.app_resLE α.val le_top _).symm
  have happ := CategoryTheory.ConcreteCategory.congr_hom (hα k (nvCover s k.down) le_rfl)
    (resT (nvCover s k.down) (pullbackCoordSection.{u} g i))
  change resM (le_top : nvCover s k.down ≤ ⊤) (α.app ⊤ (pullbackCoordSection.{u} g i)) =
    resT (nvCover s k.down) (s i)
  rw [hnat, happ, chartApp_apply, resT_pullbackCoordSection s g k.down i (hpin k.down),
    div_smul_self, ratio_smul]

/-- **The twist half of [Stacks, Tag 01NE], pinned on sections**, with the invertibility of the
comparison dropped. -/
theorem exists_hom_pullback_twistingSheafAtUniverse (hcov : IsOpenCover (nvCover s))
    (hpin : ∀ i, (nvCover s i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i)) :
    ∃ α : (Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n) ⟶ M,
      ∀ i, α.app ⊤ (pullbackCoordSection.{u} g i) = s i :=
  let ⟨α, _, hα⟩ := exists_iso_pullback_twistingSheafAtUniverse s g hcov hpin
  ⟨α, hα⟩

/-- **The unpinned form of the twist half of [Stacks, Tag 01NE] at the integral model**:
`M ≅ g ^* 𝒪(1)`, with no statement about sections. This is the conclusion of
`Stacks.TwistPullbackChart.TwistPullbackAtUniverse`, and it is the pinned comparison with its
pinning forgotten. -/
theorem nonempty_iso_pullback_twistingSheafAtUniverse (hcov : IsOpenCover (nvCover s))
    (hpin : ∀ i, (nvCover s i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i)) :
    Nonempty (M ≅ (Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n)) :=
  let ⟨α, hiso, _⟩ := exists_iso_pullback_twistingSheafAtUniverse s g hcov hpin
  ⟨(@asIso _ _ _ _ α hiso).symm⟩

/-- **The twist half of [Stacks, Tag 01NE] for a generating family**, pinned on sections: the
previous statement with the nonvanishing cover replaced by the hypothesis that the germs of the
`sᵢ` generate every stalk of `M`. -/
theorem exists_hom_pullback_twistingSheafAtUniverse_of_generatesStalks
    (hs : GeneratesStalks s)
    (hpin : ∀ i, (nvCover s i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i)) :
    ∃ α : (Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n) ⟶ M,
      ∀ i, α.app ⊤ (pullbackGlobalSections g (twistingSheafAtUniverse.{u} n)
        (coordGlobalSection.{u} n i)) = s i :=
  exists_hom_pullback_twistingSheafAtUniverse s g
    (isOpenCover_nvCover_of_generatesStalks s hs) hpin

end Comparison

/-! ### The absolute twist half of Tag 01NE -/

/-- **`Stacks.TwistPullbackChart.TwistPullbackAtUniverse`**: the twist half of
[Stacks, Tag 01NE] at the integral model of projective space, which
`Stacks.TwistPullbackChart.twistPullback_of_atUniverse` turns into
`Stacks.AmpleImmersionReduction.TwistPullback f` for every `f : X ⟶ S`. -/
theorem twistPullbackAtUniverse : Stacks.TwistPullbackChart.TwistPullbackAtUniverse.{u} :=
  fun _M _ _n s hs g hpin =>
    nonempty_iso_pullback_twistingSheafAtUniverse s g
      (isOpenCover_nvCover_of_generatesStalks s hs) hpin

end Stacks.TwistPullbackPinned

end
