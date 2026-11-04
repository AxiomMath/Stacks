module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.AffineChartFlatteningFromInduction
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.BlowupIntegralFibres0811

/-!
# The input of the Raynaud–Gruson induction, from Stacks 0811

`AlgebraicGeometry.FinitePresentationHasGenericFibreFreeBlowup` is the conclusion of
[Stacks, Tag 0811] in the form the induction of [Stacks, Tag 0815] consumes it. This file proves
it with nothing granted, from
`AlgebraicGeometry.exists_isAdmissibleBlowup_opens_finitelyLocallyFree_surjective`, which is
[Stacks, Tag 0811] under exactly the source's hypotheses. The flatness assertion of
[Stacks, Tag 0815] for a module, its reading on the affine charts of the base, and the morphism
form of that tag therefore become unconditional too.

## Main results

* `AlgebraicGeometry.finitePresentationHasGenericFibreFreeBlowup`: **the input of the
  Raynaud–Gruson induction**, unconditionally.
* `AlgebraicGeometry.finitePresentationHasAffineChartFlatteningCentre`: the affine case of the
  flatness assertion of [Stacks, Tag 0815], unconditionally.
* `AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses.of_compactSpace`: the same
  affine case for an arbitrary quasi-coherent module in place of the structure sheaf,
  unconditionally. This is the form the flattening statements for a morphism locally of finite
  *type* consume.
* `AlgebraicGeometry.finitePresentationHasFlatteningBlowup`: the morphism form of
  [Stacks, Tag 0815], unconditionally.

## Implementation notes

Three things separate the two statements, and all three run in the direction that costs nothing.

**The hypotheses differ by the two readings of "restricted to the preimage of `W`".** The
induction's interface spells the restriction of the module as
`Scheme.Modules.pullback (f ⁻¹ᵁ W).ι`, [Stacks, Tag 0811] as
`AlgebraicGeometry.Scheme.Modules.restrict (f ⁻¹ᵁ W).ι`. These are different functors — the
first is a sheafified left adjoint, the second a pushforward along the open map, kept because it
has better definitional behaviour — related by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, along which finite presentation
transports.

**The flatness hypotheses differ by a localisation, and the interface's is the stronger.** The
interface asks for flatness over all of `W`, [Stacks, Tag 0811] only for flatness at the generic
point of each fibre over a point of `W`; `AlgebraicGeometry.isFlatOverAt_of_open_restriction`
makes the passage, and the genericity hypothesis is simply not used.

**The conclusions differ by the two readings of "free on an open of the base change", which are
not interchangeable.** [Stacks, Tag 0811] trivialises `G.restrict W.ι`, an object of
`SheafOfModules (W : Scheme).ringCatSheaf`; the interface trivialises `G.over W`, an object of
`SheafOfModules (R.over W)` for `R` the sheaf of rings of the ambient scheme. Those are
different categories, so neither statement is the other read differently, and
`Stacks.AlgebraicGeometry.IrreducibleDevissage.overIsoOfRestrictIso` — which descends the
trivialisation through the equivalence `AlgebraicGeometry.Scheme.Modules.overEquiv` between them
— is what carries the one to the other.

The `Stacks.Blowup.IsAdmissibleBlowup` conjunct that [Stacks, Tag 0811] concludes is discarded:
the interface does not ask for it.

## References

* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The input of the Raynaud–Gruson induction of [Stacks, Tag 0815], with nothing granted.**
This is `AlgebraicGeometry.exists_isAdmissibleBlowup_opens_finitelyLocallyFree_surjective` — the
whole of [Stacks, Tag 0811] — restated in the shape the induction applies it in; see the
implementation notes for the three passages involved. -/
theorem finitePresentationHasGenericFibreFreeBlowup :
    FinitePresentationHasGenericFibreFreeBlowup.{u} := by
  intro S X _ _ f _ _ _ hf F _ _ W hWc hfp hflat
  -- The finite presentation hypothesis, transported to the `restrict` spelling.
  have hFW : (F.restrict (f ⁻¹ᵁ W).ι).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation.{u, u, u} _).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ W).ι).app F).symm hfp
  -- Flatness over `W` localises to flatness at each point above `W`, in particular at the
  -- generic point of a fibre.
  have hpt : ∀ x : X, f.base x ∈ W → f.base ⁻¹' {f.base x} ⊆ closure {x} →
      IsFlatOverAt f.toLRSHom.toShHom F x := fun x hx _ ↦
    isFlatOverAt_of_open_restriction f F W x hx hflat
  obtain ⟨I, hIfp, hIdisj, -, V, hVfree, hVsurj⟩ :=
    exists_isAdmissibleBlowup_opens_finitelyLocallyFree_surjective f hf F W hWc hFW hpt
  refine ⟨I, hIfp, hIdisj, V, fun z hz ↦ ?_, hVsurj⟩
  obtain ⟨O, n, hzO, hOV, ⟨e⟩⟩ := hVfree z hz
  exact ⟨O, n, hzO, hOV,
    ⟨Stacks.AlgebraicGeometry.IrreducibleDevissage.overIsoOfRestrictIso O
      (ULift.{u} (Fin n)) _ e⟩⟩

/-- **The affine case of the flatness assertion of [Stacks, Tag 0815], with nothing granted.**
For every datum to which that tag applies and every pair of an affine open `V` of the base and
an affine open `W` of its preimage, a flattening centre on `V` for `𝒪_W` avoiding `V ∩ U`.

The Raynaud–Gruson induction
(`AlgebraicGeometry.finitePresentationHasAffineChartFlatteningCentre_of_genericFibreFreeBlowup`)
reduces this to `AlgebraicGeometry.FinitePresentationHasGenericFibreFreeBlowup`, which
`AlgebraicGeometry.finitePresentationHasGenericFibreFreeBlowup` supplies. -/
theorem finitePresentationHasAffineChartFlatteningCentre :
    FinitePresentationHasAffineChartFlatteningCentre.{u} :=
  finitePresentationHasAffineChartFlatteningCentre_of_genericFibreFreeBlowup
    finitePresentationHasGenericFibreFreeBlowup.{u}

/-- **The affine case of the flatness assertion of [Stacks, Tag 0815] for an arbitrary
quasi-coherent module, with nothing granted.** Let `T` be quasi-compact and quasi-separated, let
`p : Y ⟶ T` have quasi-compact source and let `A ⊆ T` be a quasi-compact open. Then the affine
case holds for `p`, every quasi-coherent module `G` on `Y` and `A`, under the source's own
hypotheses (2)-(5) on the datum, which is what
`AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses` carries.

This is `AlgebraicGeometry.finitePresentationHasAffineChartFlatteningCentre` with the structure
sheaf replaced by an arbitrary quasi-coherent module. The flattening statements for a morphism
locally of finite *type* — [Stacks, Tags 081R, 081S, 081T, 0B49, 0CP1, 0EVC, 0F3W, 0F3Z] — need
exactly that generality, since they reach the affine case through a scheme of finite presentation
over the base containing a chart as a closed subscheme, and so through the direct image of the
chart's structure sheaf rather than through a structure sheaf. The quasi-compactness of `A` is
needed and cannot be dropped: see
`AlgebraicGeometry.not_affineCaseFlatteningCentreNoCompact`. -/
theorem AffineChartFlatteningCentreUnderSourceHypotheses.of_compactSpace {T Y : Scheme.{u}}
    [CompactSpace T] [QuasiSeparatedSpace T] [CompactSpace Y] (p : Y ⟶ T) (G : Y.Modules)
    [G.IsQuasicoherent]
    (A : T.Opens) (hA : IsCompact (A : Set T)) :
    AffineChartFlatteningCentreUnderSourceHypotheses p G A :=
  affineChartFlatteningCentreUnderSourceHypotheses_of_genericFibreFreeBlowup
    finitePresentationHasGenericFibreFreeBlowup.{u} p G A hA

/-- **The morphism form of the flattening assertion of [Stacks, Tag 0815], with nothing
granted**: for a morphism locally of finite presentation from a quasi-compact source to a
quasi-compact, quasi-separated base which is flat over a quasi-compact open `U`, a
`U`-admissible blowup after which the strict transform is flat.

This is the flatness assertion of [Stacks, Tag 0815] for the structure sheaf, read as flatness of
a morphism; the tag in full is
`AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_affineCharts`. -/
theorem finitePresentationHasFlatteningBlowup : FinitePresentationHasFlatteningBlowup.{u} :=
  finitePresentationHasFlatteningBlowup_of_affineChartFlatteningCentre
    finitePresentationHasAffineChartFlatteningCentre.{u}

end AlgebraicGeometry

end
