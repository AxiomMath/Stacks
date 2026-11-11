module

public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericStalkCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.DominateRationalMap
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ProperBirationalPointBlowups

/-!
# Factorization of a birational map of regular surfaces by blowups at closed points

Let `S` be a Noetherian scheme and let `X` and `Y` be proper integral schemes over `S` which are
regular of dimension two. The assertion of
[Stacks, Tag 0C5S](https://stacks.math.columbia.edu/tag/0C5S) is that `X` and `Y` are
`S`-birational exactly when there is a diagram of `S`-morphisms

`X = X₀ ← X₁ ← … ← Xₙ = Y_m → … → Y₁ → Y₀ = Y`

in which every morphism is the blowup of its target at a closed point. Both branches of such a
diagram are `Stacks.ResolutionOfSurfaces.FactorsAsPointBlowups` with unrestricted centres, so the
diagram is a single scheme `Z` carrying two morphisms `f : Z ⟶ X` and `g : Z ⟶ Y`, each a finite
sequence of blowups at closed points, with `f ≫ (X ↘ S) = g ≫ (Y ↘ S)`. `S`-birationality is
`AlgebraicGeometry.Scheme.BirationalOver`, which is part (2) of
[Stacks, Tag 0A20](https://stacks.math.columbia.edu/tag/0A20).

## Main definitions

* `Stacks.ResolutionOfSurfaces.PointBlowupColengthDescent` — the local splitting of
  [Stacks, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT) at the level of sheaves of
  ideals, in the shape the library's forms of [Stacks, Tag 0AHH] and [Stacks, Tag 0C5H] consume.

## Main results

* `Stacks.ResolutionOfSurfaces.birationalOver_blowUpToBase` — the blowup of an integral
  Noetherian scheme regular of dimension two at a closed point is birational to it over any base.
* `Stacks.ResolutionOfSurfaces.isIntegralRegularSurface_and_isProper_of_pointBlowupChain` — the
  source of a chain of blowups at closed points of an integral Noetherian scheme regular of
  dimension two is again such a scheme, and the chain is proper.
* `Stacks.ResolutionOfSurfaces.birationalOver_comp_of_factorsAsPointBlowups` — a morphism which
  is a finite sequence of blowups at closed points of such a scheme makes its source birational
  to the target over any base; this is the converse direction of Tag 0C5S, whose proof the source
  omits.
* `Stacks.ResolutionOfSurfaces.exists_factorsAsPointBlowups_of_birationalOver` — the forward
  direction of Tag 0C5S: two `S`-birational proper integral surfaces regular of dimension two are
  joined by two sequences of blowups at closed points out of a common scheme.
* The two directions combined, which is the statement of Tag 0C5S, are
  `birationalOver_iff_exists_factorsAsPointBlowups_of_isIntegralRegularSurface`
  of `PointBlowupFactorizationStep.lean`.

## Implementation notes

The forward direction is the argument of the source: the `S`-rational map witnessing
birationality is resolved by a sequence of blowups at closed points by
[Stacks, Tag 0C5H](https://stacks.math.columbia.edu/tag/0C5H), the resulting morphism to `Y` is
proper because its source is proper over `S` and `Y` is separated over `S`, it is birational
because it agrees with an invertible rational map over a dense open, and
[Stacks, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R) then exhibits it as a sequence of
blowups at closed points.

Tag 0C5H is proved in this library, with every input discharged, as
`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_resolving_partialMap_of_dim_two`, but that
file depends on this one through its imports. What is used here is the argument
`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_resolving_partialMap`, which takes three
inputs as arguments, and two of them are threaded through here as explicit hypotheses:
`descent`, the local splitting of [Stacks, Tag 0AGT], and `reduction`, the enlargement of the
domain of the rational map to a cofinite open resting on
[Stacks, Tag 0BX7](https://stacks.math.columbia.edu/tag/0BX7) bundled with the dominating
admissible blowup of [Stacks, Tag 081T](https://stacks.math.columbia.edu/tag/081T). Its third
input is discharged here from
`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_factorization`, which is
[Stacks, Tag 0AHI](https://stacks.math.columbia.edu/tag/0AHI).

Two further results are carried as explicit hypotheses because the library does not have them:

* `h0C5R`, which is [Stacks, Tag 0C5R] itself: a proper birational morphism between integral
  Noetherian schemes regular of dimension two is a sequence of blowups at closed points. The
  library proves the induction of that tag only from the source's one-blowup step, as
  `Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_pointBlowupStep`, and that step is not
  available, so no declaration in the library carries the tag.
* `blowUpSurface`, the globalization of
  [Stacks, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR):
  the blowup of an integral Noetherian scheme regular of dimension two at a closed point is again
  such a scheme. The library has Tag 0AGR only for the blowup of `Spec A` at the closed point of
  a two-dimensional regular local ring.

The converse direction, whose proof the source omits, is proved here from `blowUpSurface`
together with Tag 02OS, `AlgebraicGeometry.isIso_blowUp_restrict_compl_support`: a blowup is an
isomorphism away from its centre, the complement of a closed point of such a scheme is a nonempty
open because the ideal sheaf of that point is nonzero, and birationality over the base is then
read off by [Stacks, Tag 0BAD](https://stacks.math.columbia.edu/tag/0BAD),
`AlgebraicGeometry.birationalOver_iff_exists_nonempty_open_iso`.

## References

* [Stacks Project, Tag 0C5S](https://stacks.math.columbia.edu/tag/0C5S)
* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 0C5H](https://stacks.math.columbia.edu/tag/0C5H)
* [Stacks Project, Tag 0AHI](https://stacks.math.columbia.edu/tag/0AHI)
* [Stacks Project, Tag 0AHH](https://stacks.math.columbia.edu/tag/0AHH)
* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
* [Stacks Project, Tag 0BX7](https://stacks.math.columbia.edu/tag/0BX7)
* [Stacks Project, Tag 081T](https://stacks.math.columbia.edu/tag/081T)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0BAD](https://stacks.math.columbia.edu/tag/0BAD)
* [Stacks Project, Tag 0A20](https://stacks.math.columbia.edu/tag/0A20)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-! ### The local splitting consumed by Tag 0C5H -/

/-- The local splitting of [Stacks, Tag 0AGT] at the level of sheaves of ideals: at every point
of the support of a sheaf of ideals supported on finitely many closed points with regular
two-dimensional local rings, the inverse image of the ideal along the blowup at that point is a
power of the exceptional divisor times an ideal of strictly smaller total colength. -/
public abbrev PointBlowupColengthDescent : Prop :=
  ∀ (A : Scheme.{u}) (W : Finset A) (J : A.IdealSheafData),
    (∀ y ∈ W, IsClosed ({y} : Set A)) →
    (∀ y ∈ W, IsRegularLocalRing (A.presheaf.stalk y)) →
    (∀ y ∈ W, ringKrullDim (A.presheaf.stalk y) = 2) →
    (J.support : Set A) ⊆ (W : Set A) →
    ∀ y ∈ (J.support : Set A), ∀ hy : IsClosed ({y} : Set A),
    ∀ M : A.IdealSheafData, M = Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩ →
      ∃ (d : ℕ) (W' : Finset (blowUp M)) (J' : (blowUp M).IdealSheafData),
        exceptionalIdeal M ^ d * J' = J.comap (blowUpToBase M) ∧
        (∀ z ∈ W', IsClosed ({z} : Set (blowUp M))) ∧
        (∀ z ∈ W', IsRegularLocalRing ((blowUp M).presheaf.stalk z)) ∧
        (∀ z ∈ W', ringKrullDim ((blowUp M).presheaf.stalk z) = 2) ∧
        (J'.support : Set (blowUp M)) ⊆ (W' : Set (blowUp M)) ∧
        (∀ z ∈ W', (blowUpToBase M).base z ∈ W) ∧
        totalColength J' W' < totalColength J W

/-- The dominating chain of blowups that [Stacks, Tag 0C5H] consumes, supplied by the library's
form of [Stacks, Tag 0AHI]. -/
private theorem domination_of_exists_pointBlowupChain_factorization
    (descent : PointBlowupColengthDescent.{u}) :
    ∀ {A B : Scheme.{u}} [AlgebraicGeometry.IsNoetherian A] (T : Finset A)
      (V : A.Opens), (V : Set A) = (T : Set A)ᶜ →
      (∀ x ∈ T, IsClosed ({x} : Set A)) →
      (∀ x ∈ T, IsRegularLocalRing (A.presheaf.stalk x)) →
      (∀ x ∈ T, ringKrullDim (A.presheaf.stalk x) = 2) →
      ∀ (q : B ⟶ A) [IsProper q] [IsIso (q ∣_ V)],
      (∃ (A' : Scheme.{u}) (b : A' ⟶ A), Stacks.Blowup.IsAdmissibleBlowup V b ∧
          ∃ h : A' ⟶ B, h ≫ q = b) →
        ∃ (Z : Scheme.{u}) (r : Z ⟶ A), PointBlowupChain A (T : Set A) Z r ∧
          ∃ s : Z ⟶ B, s ≫ q = r := by
  intro A B _ T V hVT hclosed hregular hdim q _ _ dominated
  exact exists_pointBlowupChain_factorization descent T V hVT hclosed hregular hdim q dominated

/-! ### The ideal sheaf of a closed point of a surface -/

/-! ### A single blowup at a closed point is birational -/

/-- The blowup of an integral Noetherian scheme regular of dimension two at a closed point is
birational to it over any base: the blowup is an isomorphism away from the point, and the
complement of the point is a nonempty open. -/
public theorem birationalOver_blowUpToBase {S W : Scheme.{u}}
    (hW : IsIntegralRegularSurface W) (w : W) (hw : IsClosed ({w} : Set W)) (sW : W ⟶ S) :
    Scheme.BirationalOver
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)) ≫ sW) sW := by
  have hint := hW.isIntegral
  set M : W.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)
  have hMbot : M ≠ ⊥ := vanishingIdeal_singleton_ne_bot hW.topologicalKrullDim_eq w hw
  have hblow : AlgebraicGeometry.IsIntegral (blowUp M) := isIntegral_blowUp M hMbot
  set V : W.Opens := ⟨(M.support : Set W)ᶜ, M.support.isClosed.isOpen_compl⟩
  have hiso : IsIso (blowUpToBase M ∣_ V) := isIso_blowUp_restrict_compl_support M
  have hVne : (V : Set W).Nonempty :=
    ⟨genericPoint W, genericPoint_notMem_supportSet M hMbot⟩
  have hUne : ((blowUpToBase M ⁻¹ᵁ V : (blowUp M).Opens) : Set (blowUp M)).Nonempty := by
    obtain ⟨v, hv⟩ := hVne
    obtain ⟨z, hz⟩ := (asIso (blowUpToBase M ∣_ V)).hom.surjective ⟨v, hv⟩
    exact ⟨z.1, z.2⟩
  refine (birationalOver_iff_exists_nonempty_open_iso (blowUpToBase M ≫ sW) sW).mpr
    ⟨blowUpToBase M ⁻¹ᵁ V, V, hUne, hVne, asIso (blowUpToBase M ∣_ V), ?_⟩
  simp only [asIso_hom]
  rw [← Category.assoc, morphismRestrict_ι (blowUpToBase M) V, Category.assoc]

/-! ### Chains of blowups at closed points of a surface -/

/-- The source of a chain of blowups at closed points of an integral Noetherian scheme regular of
dimension two is again such a scheme, and the composite morphism is proper. The hypothesis
`blowUpSurface` is the globalization of [Stacks, Tag 0AGR]. -/
public theorem isIntegralRegularSurface_and_isProper_of_pointBlowupChain
    (blowUpSurface : ∀ (A : Scheme.{u}) (a : A) (ha : IsClosed ({a} : Set A)),
      IsIntegralRegularSurface A →
        IsIntegralRegularSurface
          (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))))
    {X Z : Scheme.{u}} {T : Set X} {p : Z ⟶ X} (hp : PointBlowupChain X T Z p)
    (hX : IsIntegralRegularSurface X) : IsIntegralRegularSurface Z ∧ IsProper p := by
  induction hp with
  | refl => exact ⟨hX, inferInstance⟩
  | step hh w hw hwT ih =>
    obtain ⟨hWsurface, hWproper⟩ := ih
    have hWnoetherian := hWsurface.isNoetherian
    refine ⟨blowUpSurface _ w hw hWsurface, ?_⟩
    have hblow : IsProper (blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds _))) := inferInstance
    exact MorphismProperty.comp_mem _ _ _ hblow hWproper

/-- Enlarging the set in which the centres of a chain of blowups at closed points may lie. -/
private theorem pointBlowupChain_univ {X Z : Scheme.{u}} {T : Set X} {p : Z ⟶ X}
    (hp : PointBlowupChain X T Z p) : PointBlowupChain X Set.univ Z p := by
  induction hp with
  | refl => exact .refl
  | step hh w hw hwT ih => exact ih.step w hw trivial

/-- A chain of blowups at closed points of an integral Noetherian scheme regular of dimension two
makes its source birational to the target over any base. -/
public theorem birationalOver_comp_of_pointBlowupChain
    (blowUpSurface : ∀ (A : Scheme.{u}) (a : A) (ha : IsClosed ({a} : Set A)),
      IsIntegralRegularSurface A →
        IsIntegralRegularSurface
          (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))))
    {S X Z : Scheme.{u}} (sX : X ⟶ S) {T : Set X} {p : Z ⟶ X}
    (hp : PointBlowupChain X T Z p) (hX : IsIntegralRegularSurface X) :
    Scheme.BirationalOver (p ≫ sX) sX := by
  induction hp with
  | refl => simpa using Scheme.BirationalOver.refl sX
  | step hh w hw hwT ih =>
    rw [Category.assoc]
    exact (birationalOver_blowUpToBase
      (isIntegralRegularSurface_and_isProper_of_pointBlowupChain blowUpSurface hh hX).1
      w hw _).trans ih

/-- **The converse direction of [Stacks, Tag 0C5S], whose proof the source omits.** A morphism
which is a finite sequence of blowups at closed points of an integral Noetherian scheme regular
of dimension two makes its source birational to the target over any base. -/
@[stacks 0C5S "the converse direction, which the source states without proof: a two-sided
chain of blowups in closed points makes `X` and `Y` birational over the base. Unconditional
apart from blowUpSurface (the globalization of Tag 0AGR); the route is Tag 02OS, nonvanishing
of the point's ideal sheaf, and Tag 0BAD"]
public theorem birationalOver_comp_of_factorsAsPointBlowups
    (blowUpSurface : ∀ (A : Scheme.{u}) (a : A) (ha : IsClosed ({a} : Set A)),
      IsIntegralRegularSurface A →
        IsIntegralRegularSurface
          (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))))
    {S X Z : Scheme.{u}} (sX : X ⟶ S) (hX : IsIntegralRegularSurface X) {f : Z ⟶ X}
    (hf : FactorsAsPointBlowups X Set.univ Z f) :
    Scheme.BirationalOver (f ≫ sX) sX := by
  obtain ⟨W, q, hchain, e, he⟩ := hf
  have hq : Scheme.BirationalOver (q ≫ sX) sX :=
    birationalOver_comp_of_pointBlowupChain blowUpSurface sX hchain hX
  have hrw : f ≫ sX = e.hom ≫ q ≫ sX := by rw [← he, Category.assoc]
  rw [hrw]
  exact (e.hom.birationalOver (q ≫ sX) (e.hom ≫ q ≫ sX) rfl).trans hq

/-! ### Birationality of a morphism of integral schemes -/

/-- The source of a partial isomorphism out of an integral scheme is integral. -/
private theorem isIntegral_source_of_partialIso {X Y : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] (p : X.PartialIso Y) :
    AlgebraicGeometry.IsIntegral p.source.toScheme :=
  have : Nonempty p.source.toScheme := Set.nonempty_coe_sort.mpr p.dense_source.nonempty
  isIntegral_of_isOpenImmersion p.source.ι

/-- Birationality of a morphism of integral schemes, read at the generic point. -/
private theorem isBirational_iff_genericPoint {X Y : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y] (f : X ⟶ Y) :
    IsBirational f ↔
      f (genericPoint X) = genericPoint Y ∧ IsIso (f.stalkMap (genericPoint X)) := by
  simp [IsBirational, genericPoints_eq_singleton, Set.bijOn_singleton]

/-- An open immersion of integral schemes is birational. -/
private theorem isBirational_of_isOpenImmersion {X Y : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y] (f : X ⟶ Y)
    [IsOpenImmersion f] : IsBirational f :=
  (isBirational_iff_genericPoint f).mpr ⟨genericPoint_eq_of_isOpenImmersion f, inferInstance⟩

/-- Birationality cancels on the left: if `f` and `f ≫ g` are birational so is `g`. -/
private theorem isBirational_of_comp_left {X Y Z : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    [AlgebraicGeometry.IsIntegral Z] (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsBirational f)
    (hfg : IsBirational (f ≫ g)) : IsBirational g := by
  obtain ⟨hfη, hfiso⟩ := (isBirational_iff_genericPoint f).mp hf
  obtain ⟨hfgη, hfgiso⟩ := (isBirational_iff_genericPoint _).mp hfg
  refine (isBirational_iff_genericPoint _).mpr
    ⟨by simpa [Scheme.Hom.comp_apply, hfη] using hfgη, ?_⟩
  have := hfiso
  rw [Scheme.Hom.stalkMap_comp] at hfgiso
  have := hfgiso
  exact hfη ▸ (isIso_comp_right_iff _ (f.stalkMap (genericPoint X))).mp hfgiso

/-- Birationality cancels on the right along an open immersion: if `f ≫ g` is birational and `g`
is an open immersion then `f` is birational. -/
private theorem isBirational_of_comp_isOpenImmersion_right {X Y Z : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    [AlgebraicGeometry.IsIntegral Z] (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g]
    (hfg : IsBirational (f ≫ g)) : IsBirational f := by
  obtain ⟨hfgη, hfgiso⟩ := (isBirational_iff_genericPoint _).mp hfg
  refine (isBirational_iff_genericPoint _).mpr ⟨?_, ?_⟩
  · exact g.isOpenEmbedding.injective
      (by rw [genericPoint_eq_of_isOpenImmersion g]; exact hfgη)
  · rw [Scheme.Hom.stalkMap_comp] at hfgiso
    exact (isIso_comp_left_iff (g.stalkMap (f (genericPoint X)))
      (f.stalkMap (genericPoint X))).mp hfgiso

/-- A morphism of integral schemes whose source is birational to its target over the target
itself is a birational morphism. -/
private theorem isBirational_of_birationalOver_id {X Y : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y] (f : X ⟶ Y)
    (h : Scheme.BirationalOver f (𝟙 Y)) : IsBirational f := by
  set p := h.partialIso f (𝟙 Y)
  have hint := isIntegral_source_of_partialIso p
  have hover : p.source.ι ≫ f = p.iso.hom ≫ p.target.ι := by
    have hIsOver := h.partialIso_isOver f (𝟙 Y)
    simp only [Scheme.PartialIso.IsOver, Category.comp_id] at hIsOver
    exact hIsOver.symm
  have hoi : IsOpenImmersion (p.source.ι ≫ f) := by rw [hover]; infer_instance
  exact isBirational_of_comp_left p.source.ι f (isBirational_of_isOpenImmersion _)
    (isBirational_of_isOpenImmersion _)

/-- A morphism agreeing over the source of a partial isomorphism with an invertible rational map,
whose companion to the source of that rational map is birational, is itself birational. -/
private theorem isBirational_of_resolves_partialIso {X Y Z : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    [AlgebraicGeometry.IsIntegral Z] (p : X.PartialIso Y) (f : Z ⟶ X) (g : Z ⟶ Y)
    (hf : IsBirational f)
    (hagree : pullback.fst f p.source.ι ≫ g =
      pullback.snd f p.source.ι ≫ p.toPartialMap.hom) : IsBirational g := by
  have hint := isIntegral_source_of_partialIso p
  have hη : genericPoint X ∈ p.source :=
    (genericPoint_specializes p.dense_source.nonempty.choose).mem_open
      p.source.2 p.dense_source.nonempty.choose_spec
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := p.source.ι) (genericPoint Z) ⟨genericPoint X, hη⟩
    ((isBirational_iff_genericPoint f).mp hf).1
  have hne2 : Nonempty (pullback f p.source.ι : Scheme) := ⟨z⟩
  have hint2 : AlgebraicGeometry.IsIntegral (pullback f p.source.ι) :=
    isIntegral_of_isOpenImmersion (pullback.fst f p.source.ι)
  have hfst := isBirational_of_isOpenImmersion (pullback.fst f p.source.ι)
  have hsnd : IsBirational (pullback.snd f p.source.ι) := by
    refine isBirational_of_comp_isOpenImmersion_right _ p.source.ι ?_
    rw [← pullback.condition]
    exact hfst.comp hf
  refine isBirational_of_comp_left _ _ hfst ?_
  rw [hagree, Scheme.PartialIso.toPartialMap_hom]
  exact hsnd.comp (isBirational_of_isOpenImmersion (p.iso.hom ≫ p.target.ι))

/-! ### Tag 0C5S -/

/-- **The forward direction of [Stacks, Tag 0C5S].** Let `S` be a Noetherian scheme and let `X`
and `Y` be proper integral schemes over `S` which are regular of dimension two. If `X` and `Y`
are `S`-birational then there is a scheme `Z` with `S`-morphisms `f : Z ⟶ X` and `g : Z ⟶ Y`,
each a finite sequence of blowups at closed points.

Four inputs are carried as hypotheses: `descent`, the local splitting of [Stacks, Tag 0AGT], and
`reduction`, the enlargement of the domain of an `S`-rational map resting on
[Stacks, Tag 0BX7] and [Stacks, Tag 081T], which are what the library's form of
[Stacks, Tag 0C5H] consumes; `blowUpSurface`, the globalization of [Stacks, Tag 0AGR]; and
`h0C5R`, which is [Stacks, Tag 0C5R]. -/
public theorem exists_factorsAsPointBlowups_of_birationalOver
    (descent : PointBlowupColengthDescent.{u})
    (blowUpSurface : ∀ (A : Scheme.{u}) (a : A) (ha : IsClosed ({a} : Set A)),
      IsIntegralRegularSurface A →
        IsIntegralRegularSurface
          (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))))
    (h0C5R : ∀ (A B : Scheme.{u}) (g : B ⟶ A), IsIntegralRegularSurface A →
      IsIntegralRegularSurface B → IsProper g → IsBirational g →
        FactorsAsPointBlowups A Set.univ B g)
    {S X Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] [X.Over S] [Y.Over S]
    [IsProper (X ↘ S)] [IsProper (Y ↘ S)]
    (reduction : ∀ f : X.PartialMap Y, f.IsOver S →
      ∃ (T : Finset X) (V : X.Opens) (hle : f.domain ≤ V) (g : (V : Scheme.{u}) ⟶ Y),
        (V : Set X) = (T : Set X)ᶜ ∧
        (∀ x ∈ T, IsClosed ({x} : Set X)) ∧
        (∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) = 2) ∧
        g ≫ (Y ↘ S) = V.ι ≫ (X ↘ S) ∧
        X.homOfLE hle ≫ g = f.hom ∧
        ∀ {B : Scheme.{u}} (q : B ⟶ X) [IsProper q] [IsIso (q ∣_ V)],
          ∃ (A' : Scheme.{u}) (b : A' ⟶ X), Stacks.Blowup.IsAdmissibleBlowup V b ∧
            ∃ h : A' ⟶ B, h ≫ q = b)
    (hX : IsIntegralRegularSurface X) (hY : IsIntegralRegularSurface Y)
    (hbirational : Scheme.BirationalOver (X ↘ S) (Y ↘ S)) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (g : Z ⟶ Y),
      f ≫ (X ↘ S) = g ≫ (Y ↘ S) ∧
        FactorsAsPointBlowups X Set.univ Z f ∧ FactorsAsPointBlowups Y Set.univ Z g := by
  have hXint := hX.isIntegral
  have hYint := hY.isIntegral
  have hXnoetherian := hX.isNoetherian
  have hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := by
    have hstalks : IsLocallyNoetherian X ∧ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
      ((isRegular_tfae X).out 1 2).mp hX.isRegular
    exact hstalks.2
  set pIso := hbirational.partialIso (X ↘ S) (Y ↘ S)
  have hover := hbirational.partialIso_isOver (X ↘ S) (Y ↘ S)
  have hpmOver : pIso.toPartialMap.IsOver S := by
    refine ⟨?_⟩
    change (pIso.iso.hom ≫ pIso.target.ι) ≫ (Y ↘ S) = pIso.source.ι ≫ (X ↘ S)
    rw [Category.assoc]
    exact hover
  obtain ⟨Z, p, q, hchain, hqS, hagree⟩ :=
    exists_pointBlowupChain_resolving_partialMap descent
      (fun d => domination_of_exists_pointBlowupChain_factorization d) hreg
      pIso.toPartialMap (reduction pIso.toPartialMap hpmOver)
  obtain ⟨hZsurface, hZproper⟩ :=
    isIntegralRegularSurface_and_isProper_of_pointBlowupChain blowUpSurface hchain hX
  have hZint := hZsurface.isIntegral
  have hpbirational : IsBirational p :=
    isBirational_of_birationalOver_id p
      (by simpa using birationalOver_comp_of_pointBlowupChain blowUpSurface (𝟙 X) hchain hX)
  have hqbirational : IsBirational q :=
    isBirational_of_resolves_partialIso pIso p q hpbirational hagree
  have hqproper : IsProper q := by
    have hcomp : IsProper (p ≫ (X ↘ S)) := inferInstance
    rw [← hqS] at hcomp
    exact IsProper.of_comp q (Y ↘ S)
  exact ⟨Z, p, q, hqS.symm,
    ⟨Z, p, pointBlowupChain_univ hchain, Iso.refl Z, by simp⟩,
    h0C5R Y Z q hY hZsurface hqproper hqbirational⟩

end Stacks.ResolutionOfSurfaces

end
