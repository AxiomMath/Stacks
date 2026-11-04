module

public import StacksFrontier.AlgebraicGeometry.Spaces.LargestQuasicoherentSubmodule
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentColimitClosure
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDirectSums

/-!
# Global presentations on the affine étale charts of an algebraic space

Stacks 03DX asserts that a quasi-coherent module on the small étale site of an affine scheme is
the module associated with a module over the coordinate ring, hence *globally* presented.  On the
small étale site of an algebraic space `X` the corresponding statement is about the slice at an
étale chart `V` whose underlying scheme is affine: for a quasi-coherent `𝒪_X`-module `M`, the
restriction `M|_V` has a global presentation.  That statement is named here
`AlgebraicGeometry.Space.HasAffineChartPresentations`, and this file shows that the direct-sum
clause of Stacks 03M1 for an algebraic space follows from it with no further geometry, and that
the cokernel and colimit clauses follow from it together with Stacks 03DW.

The affine étale charts cover the final object of the small étale site
(`AlgebraicGeometry.Space.SmallEtale.coversTop_affineCharts`, the geometric input of
Stacks 03M0(4)), and a direct sum of modules which are globally presented on each member of a
family covering the final object is quasi-coherent, which is
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_isColimit_cofan`.  Composing the two
discharges the direct-sum hypothesis of the construction of Stacks 04CK in
`StacksFrontier.AlgebraicGeometry.Spaces.LargestQuasicoherentSubmodule`; composing the covering with
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_isColimit_cokernelCofork` discharges
that construction's cokernel hypothesis from the same affine input together with the surjectivity
of Stacks 03DW.

## Main definitions

* `AlgebraicGeometry.Space.HasAffineChartPresentations` is Stacks 03DX for the small étale ringed
  site of an algebraic space, in the enlarged module universe that the construction of
  Stacks 04CK works in: every quasi-coherent `𝒪_X`-module is globally presented after restriction
  to an étale chart with affine underlying scheme.
* `AlgebraicGeometry.Space.HasAffineSlicePresentations` is the same statement for the modules on
  the slice at such a chart, which is the shape the faithfully-flat-descent engine produces.
* `AlgebraicGeometry.Space.HasAffineChartSurjectivePresentations` is Stacks 03DW for the small
  étale ringed site: on the slice at an étale chart with affine underlying scheme, a presenting
  morphism of a global presentation is surjective on the sections over the chart.

## Main results

* `AlgebraicGeometry.Space.hasAffineChartPresentations_of_hasAffineSlicePresentations`: the slice
  form of Stacks 03DX implies the restriction form.
* `AlgebraicGeometry.Space.hasGlobalPresentation_over_of_isColimit_cofan`: a direct sum of
  quasi-coherent `𝒪_X`-modules is globally presented on every affine étale chart.
* `AlgebraicGeometry.Space.isClosedUnderDirectSumsQuasicoherent_of_hasAffineChartPresentations`:
  **the direct-sum clause of Stacks 03M1 for an algebraic space, reduced to Stacks 03DX.**
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isColimit_cokernelCofork` and
  `AlgebraicGeometry.Space.isClosedUnderCokernels_of_hasAffineChartPresentations`: **the cokernel
  clause of Stacks 03M1 for an algebraic space, reduced to Stacks 03DX together with
  Stacks 03DW.**
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isColimit` and
  `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_of_hasAffineChartPresentations`: **the
  colimit clause of Stacks 03M1 for an algebraic space, reduced to the same two inputs.**

## Implementation notes

Quasi-coherence is `SheafOfModules.IsQuasicoherentOnSite`, Stacks 03DL(6), and a global
presentation is `SheafOfModules.HasGlobalPresentation`, Stacks 03DE(6); nothing is restated.
The direct sum is given by a cofan together with the assertion that it is a colimit, exactly as
in `AlgebraicGeometry.Space.IsClosedUnderDirectSumsQuasicoherent`, so no cocompleteness instance
is assumed.

The direct-sum clause rests on Stacks 03DX alone, because a coproduct of globally presented
modules is globally presented with no hypothesis.  The cokernel clause needs a second affine
input: a presentation of the cokernel of `f : M ⟶ N` is assembled from presentations of `M` and
`N` only after the generators of `M` lift along the presentation of `N`, and that lift comes from
surjectivity of the presenting morphism on the sections over the chart, which is the vanishing of
Stacks 03DW.  It is not a consequence of Stacks 03DX, and bootstrapping it from quasi-coherence of
the cokernel is circular, so it is carried here as
`AlgebraicGeometry.Space.HasAffineChartSurjectivePresentations`.  The kernel clause needs, beyond
both of those, flat base change of a kernel along an étale morphism of affine charts — the
geometric wrapper of `Module.Descent.isBaseChange_ker` — and is not proved here.

No `@[stacks 03M1]` tag, no `@[stacks 03DX]` tag and no `@[stacks 03DW]` tag is carried.
Stacks 03M1 has six clauses — direct sums, arbitrary colimits, kernels and cokernels,
two-out-of-three in a short exact sequence, tensor products and internal homs — so a bare tag
would be wrong even for the clauses proved here; and the clauses proved here still carry
`AlgebraicGeometry.Space.HasAffineChartPresentations`, and for cokernels
`AlgebraicGeometry.Space.HasAffineChartSurjectivePresentations`, as hypotheses, which the source
does not assume.  For the fppf site associated with a category fibred in groupoids the
corresponding affine statement is a theorem of this development with nothing assumed,
`AlgebraicGeometry.FibredSite.isAffineLocallySpanned_of_isQuasicoherentOnSite` together with
`AlgebraicGeometry.FibredSite.hasAffineColimitPresentations`; what is missing for the small étale
site of an algebraic space is the faithfully-flat-descent plumbing those rest on, which is stated
throughout `StacksDraft.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits` for the slices of
`AlgebraicGeometry.BigFppfOver` and has no small-étale counterpart.

The affine input is stated twice on purpose.  The reduction consumes
`AlgebraicGeometry.Space.HasAffineChartPresentations`, which speaks only of the restrictions of
the modules on the whole site and is therefore the weakest hypothesis that supports the
conclusion; `AlgebraicGeometry.Space.HasAffineSlicePresentations` is the faithful form of
Stacks 03DX and the form a transport of the descent engine will produce, and it implies the
first.  Keeping both leaves the conditional statement at its strongest while making the eventual
discharge a one-liner.

The module universe is `max (u + 1) m` rather than `m`, because that is the universe in which the
construction of Stacks 04CK takes its direct sums: it quantifies over the subobject lattice of a
module, which is only small in a universe containing the small étale site.  The two universes of
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_isColimit_cofan` are independent, which
is what makes it applicable there, and the index type of the direct sum is accordingly
`Type (max (u + 1) m)`.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 04CK](https://stacks.math.columbia.edu/tag/04CK)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-- **Stacks 03DX for the small étale ringed site of an algebraic space**, in the module universe
enlarged to contain the site: a quasi-coherent `𝒪_X`-module has a global presentation after
restriction to an étale chart whose underlying scheme is affine.

The source statement is the equivalence, for an affine scheme, between quasi-coherent modules on
its small étale site and modules over its coordinate ring; a module coming from a module over a
ring is presented by a family of generators and a family of relations, which is a global
presentation in the sense of Stacks 03DE(6).  The restriction is restriction to the slice of the
small étale site at the chart, as in
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_forall_affine_over`. -/
def HasAffineChartPresentations : Prop :=
  ∀ M : Modules.{u, max (u + 1) m} B S hS X hX, M.IsQuasicoherentOnSite →
    ∀ V : (smallEtaleRingedSite B S hS X hX).C,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X).obj V)) →
      (M.over V).HasGlobalPresentation

/-- **Stacks 03DX in the shape the faithfully-flat-descent engine delivers it in**: every
quasi-coherent module on the *slice* of the small étale site at an étale chart with affine
underlying scheme is globally presented, the module being arbitrary on the slice rather than the
restriction of a module on the whole site.

This is the small étale counterpart of
`AlgebraicGeometry.FibredSite.IsAffineLocallySpanned`, which quantifies over the modules on the
slice at an affine object in the same way. -/
def HasAffineSlicePresentations : Prop :=
  ∀ V : (smallEtaleRingedSite B S hS X hX).C,
    IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X).obj V)) →
    ∀ N : SheafOfModules.{max (u + 1) m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).over V),
      N.IsQuasicoherentOnSite → N.HasGlobalPresentation

/-- Stacks 03DX on the slices gives Stacks 03DX for the restrictions of the modules on the whole
site: the restriction of a quasi-coherent module to a chart is quasi-coherent on the slice at
that chart, by `Stacks.SheafOfModules.isQuasicoherent_over`.

The two universes of that statement are independent, which is what lets it be used here: the
modules of the construction of Stacks 04CK have their sections in `max (u + 1) m` while the
structure sheaf of the small étale site stays `CommRingCat.{u}`-valued. -/
theorem hasAffineChartPresentations_of_hasAffineSlicePresentations
    (h : HasAffineSlicePresentations.{u, m} B S hS X hX) :
    HasAffineChartPresentations.{u, m} B S hS X hX := fun M hM V hV ↦
  h V hV (M.over V) (Stacks.SheafOfModules.isQuasicoherent_over M hM V)

/-- A direct sum of quasi-coherent `𝒪_X`-modules has a global presentation after restriction to
an étale chart whose underlying scheme is affine, granted Stacks 03DX for that chart.

Restriction to the slice at the chart preserves colimits, and a coproduct of globally presented
modules is globally presented; see
`Stacks.SheafOfModules.hasGlobalPresentation_over_of_isColimit_cofan`. -/
theorem hasGlobalPresentation_over_of_isColimit_cofan
    (h : HasAffineChartPresentations.{u, m} B S hS X hX)
    {I : Type (max (u + 1) m)} {F : I → Modules.{u, max (u + 1) m} B S hS X hX}
    {c : Cofan F} (hc : IsColimit c) (hF : ∀ i, (F i).IsQuasicoherentOnSite)
    (V : (smallEtaleRingedSite B S hS X hX).C)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X).obj V))) :
    (c.pt.over V).HasGlobalPresentation :=
  Stacks.SheafOfModules.hasGlobalPresentation_over_of_isColimit_cofan.{u + 1, u, u, m} V hc
    fun i ↦ h (F i) (hF i) V hV

/-- **The direct-sum clause of Stacks 03M1 for an algebraic space, reduced to Stacks 03DX.**  A
direct sum of quasi-coherent `𝒪_X`-modules is quasi-coherent, granted that a quasi-coherent
`𝒪_X`-module is globally presented on every étale chart with affine underlying scheme.

The affine étale charts cover the final object of the small étale site, so quasi-coherence of the
direct sum is the clause of Stacks 03DN for quasi-coherence applied to the global presentations
of `AlgebraicGeometry.Space.hasGlobalPresentation_over_of_isColimit_cofan`.

This discharges the hypothesis `hsum` of
`AlgebraicGeometry.Space.existsUnique_quasicoherentSubobject_of_closure` and of
`AlgebraicGeometry.Space.exists_greatest_quasicoherentSubobject_of_closure`, the construction of
Stacks 04CK. -/
theorem isClosedUnderDirectSumsQuasicoherent_of_hasAffineChartPresentations
    (h : HasAffineChartPresentations.{u, m} B S hS X hX) :
    IsClosedUnderDirectSumsQuasicoherent.{u, m} B S hS X hX := fun _ F _c hc hF ↦
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_isColimit_cofan.{u + 1, u, u, m}
    (SmallEtale.coversTop_affineCharts B S hS X) hc
    fun V i ↦ h (F i) (hF i) V.1 V.2

/-- **Stacks 03DW for the small étale ringed site of an algebraic space**, in the module universe
enlarged to contain the site: on the slice of the small étale site at an étale chart whose
underlying scheme is affine, the presenting morphism of a global presentation is surjective on the
sections over the chart.

The source statement is the vanishing of the first Čech cohomology of a quasi-coherent module over
an affine base; surjectivity on sections of a presenting morphism, which is an epimorphism and
hence only locally surjective, is the form that vanishing takes here.  It is what supplies the
lift of `SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_lift`, and so the
second affine input of the cokernel clause of Stacks 03M1, beyond Stacks 03DX. -/
def HasAffineChartSurjectivePresentations : Prop :=
  ∀ V : (smallEtaleRingedSite B S hS X hX).C,
    IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X).obj V)) →
    Stacks.SheafOfModules.HasSurjectivePresentations.{u + 1, u, u, m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).over V)
      (Over.mk (𝟙 V))

/-- **The cokernel clause of Stacks 03M1 for an algebraic space, reduced to Stacks 03DX together
with Stacks 03DW.**  A cokernel of a morphism of quasi-coherent `𝒪_X`-modules is quasi-coherent,
granted that a quasi-coherent `𝒪_X`-module is globally presented on every étale chart with affine
underlying scheme and that a presenting morphism there is surjective on the sections over the
chart.

The affine étale charts cover the final object of the small étale site, both modules are globally
presented on each of them, and
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_isColimit_cokernelCofork` turns that
into a global presentation of the cokernel on each chart and hence into quasi-coherence. -/
theorem isQuasicoherentOnSite_of_isColimit_cokernelCofork
    (h : HasAffineChartPresentations.{u, m} B S hS X hX)
    (hsurj : HasAffineChartSurjectivePresentations.{u, m} B S hS X hX)
    {M N T : Modules.{u, max (u + 1) m} B S hS X hX} {f : M ⟶ N} {π : N ⟶ T}
    (hfπ : f ≫ π = 0) (hπ : IsColimit (CokernelCofork.ofπ π hfπ))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    T.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_isColimit_cokernelCofork.{u + 1,
      u, u, m}
    (SmallEtale.coversTop_affineCharts B S hS X) (fun V ↦ hsurj V.1 V.2) hfπ hπ
    (fun V ↦ h M hM V.1 V.2) fun V ↦ h N hN V.1 V.2

/-- **The cokernel clause of Stacks 03M1 for an algebraic space**, in the form of the
`CategoryTheory.ObjectProperty.IsClosedUnderCokernels` class that the construction of Stacks 04CK
in `StacksFrontier.AlgebraicGeometry.Spaces.LargestQuasicoherentSubmodule` consumes, reduced to
Stacks 03DX together with Stacks 03DW.

This discharges the instance hypothesis
`CategoryTheory.ObjectProperty.IsClosedUnderCokernels` of
`AlgebraicGeometry.Space.existsUnique_quasicoherentSubobject_of_closure`; what remains there is
the kernel clause and the two affine inputs. -/
theorem isClosedUnderCokernels_of_hasAffineChartPresentations
    (h : HasAffineChartPresentations.{u, m} B S hS X hX)
    (hsurj : HasAffineChartSurjectivePresentations.{u, m} B S hS X hX) :
    ObjectProperty.IsClosedUnderCokernels
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))) := by
  refine ⟨?_⟩
  rintro _ ⟨f, k, hk, hf⟩
  exact isQuasicoherentOnSite_of_isColimit_cokernelCofork B S hS X hX h hsurj
    (π := k.π) (by simp)
    (IsColimit.ofIsoColimit hk (Cofork.isoCoforkOfπ k)) hf.1 hf.2

/-- **The colimit clause of Stacks 03M1 for an algebraic space, reduced to Stacks 03DX together
with Stacks 03DW.**  A colimit of quasi-coherent `𝒪_X`-modules, over any shape inside the module
universe, is quasi-coherent.

The two affine inputs are the same as for the cokernel clause, which this subsumes; the
direct-sum clause is the special case of a discrete shape and needs only the first of them, so
`AlgebraicGeometry.Space.isClosedUnderDirectSumsQuasicoherent_of_hasAffineChartPresentations` is
not an instance of this statement. -/
theorem isQuasicoherentOnSite_of_isColimit
    (h : HasAffineChartPresentations.{u, m} B S hS X hX)
    (hsurj : HasAffineChartSurjectivePresentations.{u, m} B S hS X hX)
    {K : Type (max (u + 1) m)} [Category.{max (u + 1) m} K]
    {D : K ⥤ Modules.{u, max (u + 1) m} B S hS X hX} {c : Cocone D} (hc : IsColimit c)
    (hD : ∀ k, (D.obj k).IsQuasicoherentOnSite) :
    c.pt.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_isColimit.{u + 1, u, u, m}
    (SmallEtale.coversTop_affineCharts B S hS X) (fun V ↦ hsurj V.1 V.2) hc
    fun V k ↦ h (D.obj k) (hD k) V.1 V.2

/-- **The colimit clause of Stacks 03M1 for an algebraic space**, in the form of the
`CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape` class that Mathlib's full-subcategory
API consumes, reduced to Stacks 03DX together with Stacks 03DW.

With it the quasi-coherent `𝒪_X`-modules of `AlgebraicGeometry.Space.QuasicoherentSheaves` have
the colimits of that shape and the inclusion into all `𝒪_X`-modules preserves them. -/
theorem isClosedUnderColimitsOfShape_of_hasAffineChartPresentations
    (h : HasAffineChartPresentations.{u, m} B S hS X hX)
    (hsurj : HasAffineChartSurjectivePresentations.{u, m} B S hS X hX)
    (K : Type (max (u + 1) m)) [Category.{max (u + 1) m} K] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))) K := by
  refine ⟨?_⟩
  rintro _ ⟨p⟩
  exact isQuasicoherentOnSite_of_isColimit B S hS X hX h hsurj p.isColimit p.prop_diag_obj

end AlgebraicGeometry.Space

end
