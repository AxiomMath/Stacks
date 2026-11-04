module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechVanishingCriteria.OnABasisForAbelianSheaves
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralLimitVertex.VertexAsAColimit

/-!
# Positive-degree vanishing of `Sheaf.H'` from Čech acyclicity

The colimit-comparison clauses of Stacks 0A37 are reduced by
`Stacks.Cohomology.SpectralLimit.CohomologyCocone.isIso_comparison_iff` to the assertion that a
presentation of the cohomology cocone is a colimit cocone, and the Stacks proof of that runs a
degree induction whose inductive step needs two vanishing statements in degree `n + 1`: one for
an injective abelian sheaf on a stage, and one for the sheaf on the vertex of the limiting cone.
This file supplies the first outright and reduces the second to a statement about **Čech**
cohomology.

Both come from the same engine.  `Stacks.Cohomology.AbelianBasis.cechToCohomologyOnBasis` —
Stacks 01EW for abelian sheaves, which holds for every space with no hypotheses — turns Čech
vanishing on a cofinal collection of covers into vanishing of `Sheaf.H'`.  Instantiated at the
basis of quasi-compact opens and the finite covers by quasi-compact opens, whose cofinality is
Stacks 0069 (`Stacks.Cohomology.Vanishing.exists_compactCover_refines`), it says that an abelian
sheaf with vanishing positive-degree Čech cohomology for every such cover has vanishing
positive-degree `Sheaf.H'` over every quasi-compact open.

That is the shape in which the vanishing on the limit side is reachable at all.  The limit side
asks for `Hⁿ⁺¹(pᵢ⁻¹U, colimⱼ pⱼ⁻¹𝒢ⱼ) = 0` for a system `𝒢` of *injective* abelian sheaves on
the stages, and the known vanishing for a filtered colimit of injectives,
`Stacks.Cohomology.AbelianBasis.isZero_H'_succ_colimit_of_injective'`, does **not** apply to it:
that lemma wants the system to consist of injective sheaves on the one space it works over, and
`pⱼ⁻¹` does not preserve injectives.  Reducing to Čech is what sidesteps the obstruction,
because the Čech complex of a cover by quasi-compact opens is a *finite* product of sections over
quasi-compact opens, and sections over a quasi-compact open of the limit are computed stagewise
by abelian Stacks 0A33.

## Main results

* `Stacks.Cohomology.AbelianBasis.isZero_H'_succ_of_injective`: **the positive-degree cohomology
  of an injective abelian sheaf vanishes over every open.**  This is the `hinj` input of the
  degree induction `CategoryTheory.DeltaFunctor.isIso_colimit_post_of_isIso_zero`, in the
  `Sheaf.H'` spelling; it carries no hypothesis on the space or the open.
* `Stacks.Cohomology.AbelianBasis.isZero_H'_of_cechAcyclic`: **positive-degree `Sheaf.H'`
  vanishes over every quasi-compact open for a Čech-acyclic abelian sheaf**, on a space with a
  basis of quasi-compact opens closed under binary intersection.  Unconditional.
* `SpectralAbelianSheafSystem.isZero_H'_succ_conePoint_of_cechAcyclic`, in the namespace
  `Stacks.Cohomology.SpectralLimit`:
  the same on the vertex of a limiting cone of abelian spectral sheafed spaces, over the open
  `pᵢ⁻¹U` carried by the open cone of the quasi-compact-open clause of Stacks 0A37.  **This is the
  vanishing needed on the limit side, reduced to one Čech statement about the sheaf on the
  vertex.**

## Implementation notes

### Why the colimit on the limit side is not a `colimit.post`

The Stacks factorization of the comparison of Tag 0A37 splits the `k`-th leg as base change to
the vertex followed by the map induced by the colimit cocone,
`Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem.spaceCohomologyMap_leg_eq`.  The
second factor is the `k`-th leg of a cocone whose comparison *is* a `Limits.colimit.post`, of the
single functor `Sheaf.H'(pᵢ⁻¹U, -)` on the sheaves of the pullback system; that is why step 2 is
available in every degree from abelian Stacks 01FF alone.

The first factor is not of that form, and no degree of index polymorphism makes it so.  Its
source `Hᑫ(f_a⁻¹U, 𝒜ⱼ)` and its target `Hᑫ(pᵢ⁻¹U, pⱼ⁻¹𝒜ⱼ)` are cohomology groups **on different
spaces**, so the family is a natural transformation between two functors on the index category
and not the image of one functor under a fixed cohomology functor.  Nor is it an isomorphism
index by index: already in degree zero `(pⱼ⁻¹𝒜ⱼ)(pⱼ⁻¹V)` is a colimit over the stages below `j`
and not `𝒜ⱼ(V)`, so only the colimit over the index category can be an isomorphism.  A
`Limits.colimit.post` is by construction the comparison for one functor applied to one diagram,
and `CategoryTheory.DeltaFunctor.isIso_colimit_post_of_isIso_zero` concludes about exactly that;
it therefore cannot reach the first factor however its universes are chosen.  Running a degree
induction on the first factor instead needs the two long exact sequences compared by hand, which
is what makes the vanishing statements of this file necessary rather than incidental.

### Spelling

The general statements are at `X : Type u` carrying a topology with coefficients
`Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}`, which is the spelling of
`cechToCohomologyOnBasis` and of the `HasExt` and `HasSheafify` instances behind `Sheaf.H'`.  A
consumer holding a `SheafedSpace` applies them to the underlying `Type u`, as the cone-point
statement here does: `TopCat.Sheaf` is a semireducible `def` over the same category, so the
crossing is definitional, but instances found at one spelling are not found at the other and the
space has to be presented as `((c.pt : TopCat.{u}) : Type u)` for them to be.

`Injective` is taken as an explicit argument rather than an instance binder, and seated with a
`have`, for the same reason: at the `TopCat.Sheaf` spelling instance search does not find an
`Injective` hypothesis stated at the site spelling.

Everything is at `SpectralAbelianSheafSystem.{u, u, u}` with `J : Type u` a small category.  The
only available form of abelian Stacks 01FF, `isIso_colimit_post_H'functor_of_isCompact'`, has a
single universe parameter serving as space, coefficient, index-object and index-hom universe at
once, and the space and coefficient universes are pinned to `u` inside
`SpectralAbelianSheafSystem` and `CohomologyCocone`; so the index universes collapse to `u` too.

## References

* [Stacks Project, Tag 0069](https://stacks.math.columbia.edu/tag/0069)
* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
* [Stacks Project, Tag 0A33](https://stacks.math.columbia.edu/tag/0A33)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.Basis (OpenCover compactOpens)
open Stacks.Cohomology.Vanishing (compactCovers isBasis_compactOpens
  compactCovers_mem_compactOpens exists_compactCover_refines)
open Stacks.Cohomology.AbelianColimit (abSections nonempty_H'functor_iso_rightDerived)

universe u

namespace Stacks.Cohomology.AbelianBasis

variable {X : Type u} [TopologicalSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-! ### Injective abelian sheaves -/

/-- **The positive-degree cohomology of an injective abelian sheaf vanishes**, over every open of
every space.

In the right-derived spelling this is automatic — a right-derived functor kills injectives in
positive degree, `CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ` — and
`Stacks.Cohomology.AbelianColimit.nonempty_H'functor_iso_rightDerived` moves it to native
cohomology.  It is the hypothesis `hinj` of the degree induction
`CategoryTheory.DeltaFunctor.isIso_colimit_post_of_isIso_zero`, which is what makes it worth
stating in the `Sheaf.H'` spelling: the existing vanishing statements in that spelling are all
about a filtered *colimit* of injectives over a quasi-compact open, and the induction needs the
single-sheaf form over an arbitrary open. -/
theorem isZero_H'_succ_of_injective
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (hF : Injective F)
    (V : Opens X) (n : ℕ) :
    IsZero (Sheaf.H'.{u, u, u} F (n + 1) V) :=
  have := hF
  ((abSections V).isZero_rightDerived_obj_injective_succ n F).of_iso
    ((nonempty_H'functor_iso_rightDerived V (n + 1)).some.app F)

/-! ### Čech-acyclic abelian sheaves -/

/-- **Positive-degree `Sheaf.H'` vanishes over every quasi-compact open for a Čech-acyclic
abelian sheaf.**  Let `X` have a basis of quasi-compact opens whose binary intersections are
quasi-compact, and let `F` be an abelian sheaf whose positive-degree Čech cohomology vanishes for
every finite cover of a quasi-compact open by quasi-compact opens.  Then `Hⁿ(U, F) = 0` for every
quasi-compact open `U` and every `n > 0`.

This is `cechToCohomologyOnBasis` — abelian Stacks 01EW, which holds for every space — applied to
the basis of all quasi-compact opens and the collection `Stacks.Cohomology.Vanishing.compactCovers`
of finite covers by quasi-compact opens: those covers are cofinal by Stacks 0069
(`Stacks.Cohomology.Vanishing.exists_compactCover_refines`) and only quasi-compact opens occur in
their Čech complexes (`Stacks.Cohomology.Vanishing.compactCovers_mem_compactOpens`).

Taking the Čech hypothesis as an argument rather than deriving it from injectivity of a system is
what makes this usable on the vertex of a limit of spectral spaces, where the sheaf is a filtered
colimit of inverse images of injective sheaves and is **not** a colimit of injective sheaves. -/
theorem isZero_H'_of_cechAcyclic (hBasis : PrespectralSpace X)
    (hInter : QuasiSeparatedSpace X)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hCech : ∀ W ∈ compactCovers X, ∀ n : ℕ, 0 < n →
      IsZero (((cechComplexFunctor W.obj).obj F.obj).homology n))
    (U : Opens X) (hU : IsCompact (U : Set X)) (n : ℕ) (hn : 0 < n) :
    IsZero (Sheaf.H'.{u, u, u} F n U) :=
  cechToCohomologyOnBasis F (compactOpens X) (isBasis_compactOpens hBasis) (compactCovers X)
    (compactCovers_mem_compactOpens hInter)
    (fun V hV => exists_compactCover_refines hBasis hInter V hV) hCech U hU n hn

end Stacks.Cohomology.AbelianBasis

namespace Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem

open Stacks.Cohomology Stacks.Cohomology.SpectralLimit

variable {J : Type u} [SmallCategory J] [IsCofiltered J]
  (S : SpectralAbelianSheafSystem.{u, u, u} J)

/-- **The vanishing needed on the limit side of Stacks 0A37, reduced to Čech acyclicity of the
sheaf on the vertex.**  Over the open `pᵢ⁻¹U` carried by the open cone of the quasi-compact-open
clause, `Hⁿ⁺¹(pᵢ⁻¹U, c.pt.sheaf) = 0` as soon as the positive-degree Čech cohomology of
`c.pt.sheaf` vanishes for every finite cover of a quasi-compact open of the vertex by
quasi-compact opens.

The two hypotheses of `Stacks.Cohomology.AbelianBasis.isZero_H'_of_cechAcyclic` hold on the
vertex because it is a spectral space — `spectralSpace_conePoint`, Stacks 0A2Z transported along
`conePointIso` — and `pᵢ⁻¹U` is quasi-compact because the cone projections are spectral maps
(`isCompact_legPreimage`). -/
theorem isZero_H'_succ_conePoint_of_cechAcyclic (c : Cone S.E) (hc : IsLimit c) (i : J)
    (U : Opens (S.E.obj i)) (hU : IsCompact (U : Set (S.E.obj i)))
    (hCech : ∀ W ∈ compactCovers ((c.pt : TopCat.{u}) : Type u), ∀ n : ℕ, 0 < n →
      IsZero (((cechComplexFunctor W.obj).obj c.pt.sheaf.obj).homology n))
    (n : ℕ) :
    IsZero (Sheaf.H'.{u, u, u} c.pt.sheaf (n + 1) (S.stageOpenCone c i U).pt) :=
  have hspec : SpectralSpace ((c.pt : TopCat.{u}) : Type u) := spectralSpace_conePoint S c hc
  AbelianBasis.isZero_H'_of_cechAcyclic hspec.toPrespectralSpace hspec.toQuasiSeparatedSpace
    c.pt.sheaf hCech _
    (isCompact_legPreimage S c hc i U hU) (n + 1) (Nat.succ_pos n)

end Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem

end
