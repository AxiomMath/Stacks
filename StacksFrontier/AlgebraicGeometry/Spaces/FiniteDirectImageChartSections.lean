module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence

/-!
# Coherence of a direct image from finiteness of its sections over the affine charts

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` with `Y` locally Noetherian,
and let `𝓕` be an `𝒪_X`-module on the small étale site of `X`.  The coherence assertion of
Stacks 07UH is that `f_*𝓕` is coherent when `f` is finite and `𝓕` is coherent.  This file proves
that conclusion from two hypotheses about `f_*𝓕` itself: that it is quasi-coherent, and that its
sections over every *affine* étale chart of `Y` form a finite module over the functions on that
chart.  Finiteness of `f` and coherence of `𝓕` are then not used at all.

The mathematical content of the file is an affine-chart criterion for finite type, the exact
converse of `AlgebraicGeometry.Space.moduleFinite_sections_of_isFiniteType`: a module which is
cartesian on affine charts and whose sections over every affine chart form a finite module is of
finite type on the small étale site.  Together with Stacks 07UB (1) ⇔ (2) this says that on a
locally Noetherian algebraic space *coherence of a quasi-coherent module is finiteness of its
sections over the affine charts*, in both directions.

## Main results

* `AlgebraicGeometry.Space.isFiniteType_of_coversTop_affine_moduleFinite`: a module cartesian on
  affine charts whose sections over the members of a covering family of affine étale charts form
  finite modules is of finite type, and
  `AlgebraicGeometry.Space.isFiniteType_of_forall_affine_moduleFinite`, the case of the family
  of all affine charts.
* `AlgebraicGeometry.Space.isCoherent_of_isQuasicoherentOnSite_of_forall_affine_moduleFinite`: on
  a locally Noetherian algebraic space a quasi-coherent module with finite sections over every
  affine étale chart is coherent.
* `AlgebraicGeometry.Space.isCoherentOnSite_chartLocalizedModulePushforward_of_isCoherentOnSite`
  and its companion
  `...isCoherentOnSite_chartLocalizedModulePushforward_of_forall_affine_moduleFinite`:
  the localized direct image of Stacks 04CF is coherent on the slice at **every** étale chart of
  `Y`.  This is the conclusion of the three `hchart` hypotheses listed below, so it discharges
  all three.
* The coherence assertion of Stacks 07UH itself, for `f` finite and `𝓕` coherent, is
  `AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite'`; granted quasi-coherence of
  `f_*𝓕` and finiteness of its sections over the affine charts, coherence of `f_*𝓕` is the
  criterion above applied to it.

## Implementation notes

**The three chart hypotheses this discharges.**  Three theorems of the library carry a hypothesis
`hchart` with the same conclusion, namely coherence on the slice at a chart `V` of the localized
direct image `((chartLocalizedModulePushforward f V).obj ((moduleChartBaseChangeRestriction f
V).obj 𝓕))`.  They differ only in the premises `hchart` is allowed to assume, all of which the
caller already supplies:

* `AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite` takes the chart `V` from the
  caller and lets `hchart` assume finiteness of the chart base change of `f`, local
  Noetherianity of `V` and coherence of `𝓕`;
* `AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite_of_chartCase` quantifies
  `hchart` over all charts `V` and adds surjectivity of `V` to those premises;
* `AlgebraicGeometry.Space.isCoherent_modulePushforward_structureSheaf_preimage` is the first
  shape with `𝓕` the structure sheaf of a closed subspace.

The second of the two chart-case results listed above proves that common conclusion for an
arbitrary `f`, an arbitrary chart and an arbitrary module, so each of the three hypotheses is
obtained from it by discarding the premises.

**What is still carried, and by what name.**  The two hypotheses `hqc` and `hfin` of the chart
case above are *not* available in this development for a finite morphism.

* Quasi-coherence of `f_*𝓕` on the small étale site is Stacks 03M9.  The tree has it only in the
  reduced form `AlgebraicGeometry.Space.pushforward_isQuasicoherentOnSite_of_forall_affine`,
  whose affine-base case is itself a hypothesis, and — for a closed immersion — as the field
  `pushforward_isQuasicoherentOnSite` of
  `AlgebraicGeometry.Space.QuasicoherentDirectImageEquivalence`, which is part (3) of
  Stacks 04CJ.
* Finiteness of the sections `(f_*𝓕)(A)` over an affine étale chart `A` of `Y` is the étale-site
  form of Cohomology of Schemes, Lemma 01Y6.  For a finite `f` the mathematics is a two-step
  composition: `A` affine and `f` affine make the chart base change `U = A ×_Y X` an affine étale
  chart of `X` by `AlgebraicGeometry.Space.isAffine_smallBaseChange_obj`, over which
  `AlgebraicGeometry.Space.moduleFinite_sections_of_isCoherent` makes `𝓕(U)` a finite
  `𝒪_X(U)`-module; `𝒪_X(U)` is a finite `𝒪_Y(A)`-module because `f` is finite; and
  `Module.Finite.trans` concludes.  Two links of that chain are missing.  The identification
  `(f_*𝓕)(A) = 𝓕(U)` holds by `rfl` for
  `AlgebraicGeometry.Space.smallBaseChangeModulePushforward` — this is
  `AlgebraicGeometry.Space.smallBaseChangeModulePushforward_obj_val_obj` — but the comparison of
  that functor with `AlgebraicGeometry.Space.modulePushforward`,
  `AlgebraicGeometry.Space.smallBaseChangeModulePushforwardIso`, is proved by uniqueness of right
  adjoints and needs `f` *étale*, which a finite morphism is not; and no declaration in this tree
  derives `Module.Finite (𝒪_Y(A)) (𝒪_X(U))` from `AlgebraicGeometry.Space.IsFinite f`, the route
  being `AlgebraicGeometry.Space.isFinite_iff_representable` and
  `AlgebraicGeometry.Space.presheaf_isFinite_of_isFinite` to the scheme-level finiteness of the
  chart morphism, then `AlgebraicGeometry.Scheme.Hom.finite_appTop`, and finally an
  identification of that ring map with the chart-level structure map.

**Stacks 03DW is not what any of this is owed from.**  The three theorems above describe their
`hchart` as "the étale-site form of Stacks 01Y6, that is Stacks 03DW".  Stacks 03DW is Descent,
Proposition *Cohomology of quasi-coherent modules is the same in every topology*; the comparison
that would carry coherence from the Zariski site of a scheme to its small étale site is Descent,
Proposition 03DX (2), equivalently Étale Cohomology, Theorem 03OJ, and 03DW is a consumer of that
area rather than an input to it.  The same correction is recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSections`.  Nothing here carries a `@[stacks 03DW]`
attribute.

**Why the criterion is stated with no affineness on the smaller chart.**  The generation step
runs over an affine covering family of an arbitrary chart,
`AlgebraicGeometry.Space.SmallEtale.exists_affine_etale_ofArrows`, and the resulting covering
sieve also contains the arrows that factor through a member of that family through a chart which
need not be affine.  So the base change property of the sections, which
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts` provides only between affine charts, is used
at the affine members and the conclusion is then transported along the factoring morphism by
semilinearity of restriction.

## References

* [Stacks Project, Tag 07UH](https://stacks.math.columbia.edu/tag/07UH)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
-/

@[expose] public section

open CategoryTheory Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Generators of the sections over an affine chart restrict to generators over any smaller
affine chart**, for a module cartesian on affine charts.

The sections over the larger chart whose restriction lies in the span of the restricted
generators form a submodule, by semilinearity of restriction; it contains the generators, hence
is everything, so the whole image of restriction lies in that span.  Surjectivity of the base
change comparison of Stacks 03DX(2), which is what being cartesian on affine charts gives,
says that image already spans the sections over the smaller chart. -/
theorem span_range_chartRestrict_generators_eq_top {M : Modules.{u, m} B S hS F hF}
    (hMcart : IsCartesianOnAffineCharts M)
    {A Z : SmallEtale B S hS F} (hA : IsAffine (chartScheme A)) (hZ : IsAffine (chartScheme Z))
    (ψ : Z ⟶ A) {n : ℕ} {s : Fin n → M.val.obj (op A)}
    (hs : Submodule.span (chartRing B S hS F hF A) (Set.range s) = ⊤) :
    Submodule.span (chartRing B S hS F hF Z)
        (Set.range fun i ↦ chartRestrictLinear M ψ (s i)) = ⊤ := by
  classical
  set N : Submodule (chartRing B S hS F hF Z) (M.val.obj (op Z)) :=
    Submodule.span (chartRing B S hS F hF Z)
      (Set.range fun i ↦ chartRestrictLinear M ψ (s i)) with hN
  have hrange : Submodule.span (chartRing B S hS F hF Z)
      (Set.range fun x : M.val.obj (op A) ↦ chartRestrictLinear M ψ x) ≤ N := by
    rw [Submodule.span_le]
    rintro y ⟨x, rfl⟩
    let P : Submodule (chartRing B S hS F hF A) (M.val.obj (op A)) :=
      { carrier := {x | chartRestrictLinear M ψ x ∈ N}
        zero_mem' := by
          simp only [Set.mem_ofPred_eq, map_zero]
          exact N.zero_mem
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq, map_add]
          exact N.add_mem ha hb
        smul_mem' := fun c a ha => by
          simp only [Set.mem_ofPred_eq, chartRestrictLinear_smul]
          exact N.smul_mem _ ha }
    have hP : (⊤ : Submodule (chartRing B S hS F hF A) (M.val.obj (op A))) ≤ P := by
      rw [← hs, Submodule.span_le]
      rintro y ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    exact hP (Submodule.mem_top (x := x))
  refine top_unique ?_
  rw [← (chartBaseChange_surjective_iff_span_eq_top M ψ).1 (hMcart A Z hA hZ ψ).2]
  exact hrange

/-- **A module cartesian on affine charts whose sections over the members of a covering family
of affine étale charts form finite modules is of finite type on the small étale site.**

A finite generating family of the sections over an affine chart `A` of the family generates the
module in the sense of `CategoryTheory.PresheafOfModules.Generates`: a section over a chart `W`
above `A` is tested on the affine covering family of `W` of
`AlgebraicGeometry.Space.SmallEtale.exists_affine_etale_ofArrows`, where
`AlgebraicGeometry.Space.span_range_chartRestrict_generators_eq_top` applies, and the resulting
linear combination is carried to an arbitrary member of the covering sieve along the morphism
through which that member factors.  The module universe is free. -/
theorem isFiniteType_of_coversTop_affine_moduleFinite (M : Modules.{u, m} B S hS F hF)
    (hMcart : IsCartesianOnAffineCharts M) {I : Type (u + 1)} (W : I → SmallEtale B S hS F)
    (hWaff : ∀ a, IsAffine (chartScheme (W a)))
    (hWcov : (smallEtaleRingedSite B S hS F hF).J.CoversTop W)
    (hfin : ∀ a, Module.Finite (chartRing B S hS F hF (W a)) (M.val.obj (op (W a)))) :
    PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS F hF).J M.val := by
  classical
  refine ⟨I, W, hWcov, fun a ↦ ?_⟩
  obtain ⟨n, s, hs⟩ := (hfin a).exists_fin
  refine ⟨n, s, ?_⟩
  intro W' ρ t
  obtain ⟨I', V', ι', hV'aff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS F W'
  refine ⟨Sieve.ofArrows V' ι', hcov, ?_⟩
  intro Zc g hg
  obtain ⟨j, α, rfl⟩ := Sieve.ofArrows.exists hg
  have hspan := span_range_chartRestrict_generators_eq_top B S hS F hF hMcart (hWaff a)
    (hV'aff j) (ι' j ≫ ρ) hs
  have hmem : chartRestrictLinear M (ι' j) t ∈
      Submodule.span (chartRing B S hS F hF (V' j))
        (Set.range fun i ↦ chartRestrictLinear M (ι' j ≫ ρ) (s i)) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
  refine ⟨fun i ↦ chartRestrict (hF := hF) α (d i), ?_⟩
  have hstep : ∀ i, chartRestrict (hF := hF) α (d i) •
      chartRestrictLinear M ((α ≫ ι' j) ≫ ρ) (s i) =
      chartRestrictLinear M α (d i • chartRestrictLinear M (ι' j ≫ ρ) (s i)) := by
    intro i
    have hassoc : (α ≫ ι' j) ≫ ρ = α ≫ (ι' j ≫ ρ) := Category.assoc _ _ _
    have h1 : chartRestrictLinear M ((α ≫ ι' j) ≫ ρ) (s i) =
        chartRestrictLinear M α (chartRestrictLinear M (ι' j ≫ ρ) (s i)) :=
      (congrArg (fun ψ ↦ chartRestrictLinear M ψ (s i)) hassoc).trans
        (chartRestrictLinear_comp M (ι' j ≫ ρ) α (s i))
    rw [h1]
    exact (chartRestrictLinear_smul M α (d i) _).symm
  calc ∑ i, chartRestrict (hF := hF) α (d i) •
        chartRestrictLinear M ((α ≫ ι' j) ≫ ρ) (s i)
      = ∑ i, chartRestrictLinear M α (d i • chartRestrictLinear M (ι' j ≫ ρ) (s i)) :=
        Finset.sum_congr rfl fun i _ ↦ hstep i
    _ = chartRestrictLinear M α (∑ i, d i • chartRestrictLinear M (ι' j ≫ ρ) (s i)) :=
        (map_sum (chartRestrictLinear M α) _ _).symm
    _ = chartRestrictLinear M α (chartRestrictLinear M (ι' j) t) := congrArg _ hd
    _ = chartRestrictLinear M (α ≫ ι' j) t := (chartRestrictLinear_comp M (ι' j) α t).symm

/-- **A module cartesian on affine charts whose sections over every affine étale chart form a
finite module is of finite type on the small étale site.**  This is the converse of
`AlgebraicGeometry.Space.moduleFinite_sections_of_isFiniteType`.

The affine charts cover the site, by
`AlgebraicGeometry.Space.SmallEtale.coversTop_affineCharts`, so this is the case of the family
of all of them in
`AlgebraicGeometry.Space.isFiniteType_of_coversTop_affine_moduleFinite`. -/
theorem isFiniteType_of_forall_affine_moduleFinite (M : Modules.{u, m} B S hS F hF)
    (hMcart : IsCartesianOnAffineCharts M)
    (hfin : ∀ A : SmallEtale B S hS F, IsAffine (chartScheme A) →
      Module.Finite (chartRing B S hS F hF A) (M.val.obj (op A))) :
    PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS F hF).J M.val :=
  isFiniteType_of_coversTop_affine_moduleFinite B S hS F hF M hMcart
    (fun A : {A : SmallEtale B S hS F // IsAffine (chartScheme A)} ↦ A.1) (fun A ↦ A.2)
    (SmallEtale.coversTop_affineCharts B S hS F) fun A ↦ hfin A.1 A.2

/-- **A quasi-coherent module with finite sections over the affine charts of a locally
Noetherian algebraic space is coherent.**

Quasi-coherence supplies the base change property of the sections, Descent, Proposition 03DX(2),
through `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`;
`AlgebraicGeometry.Space.isFiniteType_of_forall_affine_moduleFinite` then gives finite type, and
Stacks 07UB (1) ⇔ (2) gives coherence.  This is the exact converse of
`AlgebraicGeometry.Space.moduleFinite_sections_of_isCoherent`, so on a locally Noetherian
algebraic space coherence of a quasi-coherent module *is* finiteness of its sections over the
affine charts. -/
theorem isCoherent_of_isQuasicoherentOnSite_of_forall_affine_moduleFinite
    (hN : HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (M : Modules.{u, u} B S hS F hF) (hqc : M.IsQuasicoherentOnSite)
    (hfin : ∀ A : SmallEtale B S hS F, IsAffine (chartScheme A) →
      Module.Finite (chartRing B S hS F hF A) (M.val.obj (op A))) :
    IsCoherent B S hS F hF M := by
  have : Fact (HasEtaleLocalProperty B S hS F
    (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) := ⟨hN⟩
  exact (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS F hF M).2
    ⟨hqc, isFiniteType_of_forall_affine_moduleFinite B S hS F hF M
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF M hqc) hfin⟩

/-! ### The chart case of the coherence assertion of Stacks 07UH -/

variable {X Y : AlgebraicSpaces B S hS}

/-- **The chart case of the coherence assertion of Stacks 07UH, from coherence on the site.**
If the direct image `f_*𝓕` is coherent on the small étale site of `Y` then, at *every* étale
chart `V` of `Y`, the localized direct image `f'_*(𝓕|_U)` of Stacks 04CF is coherent on the
slice at `V`.

Coherence restricts to a slice by `Stacks.SheafOfModules.isCoherentOnSite_over`, and the
restriction of `f_*𝓕` to the slice at `V` is the localized direct image by Stacks 04CF,
`AlgebraicGeometry.Space.modulePushforward_comp_overFunctorIso`; coherence on a site is
invariant under isomorphism.  No hypothesis on `f`, on `𝓕` or on `V` is used. -/
theorem isCoherentOnSite_chartLocalizedModulePushforward_of_isCoherentOnSite (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS X.1 X.2)
    (h : SheafOfModules.IsCoherentOnSite ((modulePushforward B S hS f).obj G))
    (V : SmallEtale B S hS Y.1) :
    ((chartLocalizedModulePushforward B S hS f V).obj
      ((moduleChartBaseChangeRestriction B S hS f V).obj G)).IsCoherentOnSite :=
  Stacks.SheafOfModules.isCoherentOnSite_of_iso
    ((modulePushforward_comp_overFunctorIso B S hS f V).app G)
    (Stacks.SheafOfModules.isCoherentOnSite_over _ h V)

/-- **The chart case of the coherence assertion of Stacks 07UH, from finiteness of the sections
of the direct image over the affine charts.**

Let `f : X ⟶ Y` be a morphism of algebraic spaces with `Y` locally Noetherian and let `𝓕` be an
`𝒪_X`-module whose direct image `f_*𝓕` is quasi-coherent and has finite sections over every
affine étale chart of `Y`.  Then, at every étale chart `V` of `Y`, the localized direct image
`f'_*(𝓕|_U)` of Stacks 04CF is coherent on the slice at `V`.

This is the conclusion of the `hchart` hypotheses carried by
`AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite`, by
`AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite_of_chartCase` and by
`AlgebraicGeometry.Space.isCoherent_modulePushforward_structureSheaf_preimage`, proved for an
arbitrary chart and an arbitrary module, so it discharges all three of them; see the
implementation notes for what those hypotheses carry that this does not need, and for what is
left to prove. -/
theorem isCoherentOnSite_chartLocalizedModulePushforward_of_forall_affine_moduleFinite
    (f : X ⟶ Y)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (G : Modules.{u, u} B S hS X.1 X.2)
    (hqc : ((modulePushforward B S hS f).obj G).IsQuasicoherentOnSite)
    (hfin : ∀ A : SmallEtale B S hS Y.1, IsAffine (chartScheme A) →
      Module.Finite (chartRing B S hS Y.1 Y.2 A)
        (((modulePushforward B S hS f).obj G).val.obj (op A)))
    (V : SmallEtale B S hS Y.1) :
    ((chartLocalizedModulePushforward B S hS f V).obj
      ((moduleChartBaseChangeRestriction B S hS f V).obj G)).IsCoherentOnSite :=
  isCoherentOnSite_chartLocalizedModulePushforward_of_isCoherentOnSite B S hS f G
    (isCoherent_of_isQuasicoherentOnSite_of_forall_affine_moduleFinite B S hS Y.1 Y.2 hY
      ((modulePushforward B S hS f).obj G) hqc hfin).toIsCoherentOnSite V

end AlgebraicGeometry.Space

end
