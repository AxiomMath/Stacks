module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCompletedLocalRing
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.NodalStandardFamilyFibreCompletion
public import StacksFrontier.AlgebraicGeometry.Curves.NodalUnramifiedSingularSubscheme
public import StacksFrontier.AlgebraicGeometry.Curves.NodeFittingIdealClosedPoint
public import StacksFrontier.AlgebraicGeometry.Curves.NodeSplitAfterEtaleBase
public import StacksFrontier.AlgebraicGeometry.Curves.StandardNodalDiagramNoetherianApproximation
public import StacksFrontier.RingTheory.GRing.EssFiniteType

/-!
# The étale local structure of an at-worst-nodal family: Tag 0CBY

This file proves [Stacks, Tag 0CBY]: a morphism `f : X ⟶ S` which is at-worst-nodal of relative
dimension one is, étale locally on source and target around a singular point `x` of a fibre, a
base change of the standard nodal family `Spec ℤ[u, v, a]/(uv - a) ⟶ Spec ℤ[a]`. The tag's
diagram — étale `X ← U`, `S ← V` and `U ⟶ W`, a cartesian square exhibiting `W` as that base
change, and a point of `U` over `x` — is the structure
`Stacks.NodalEtaleLocalStructure.StandardNodalDiagram`, and the whole statement is
`Stacks.NodalEtaleLocalStructure.nonempty_standardNodalDiagram_of_isAtWorstNodal`, which carries
`@[stacks 0CBY]`.

The tagged statement spells the singular point of the fibre as the failure of smoothness of
`X_s` over `κ(s)` at `x`, which is the source's own wording. The whole argument is assembled
instead for the equivalent spelling "`x` lies in the relative singular subscheme `Sing(f) ⊆ X`",
the closed subscheme cut out by the first Fitting ideal of `Ω_{X/S}`: that is the form the
source's first step carries, because `Sing(f)` is compatible with base change
([Stacks, Tag 0C3I]). The two agree by `mem_relativeSingular_iff_not_smoothAt_fiber`, which is
[Stacks, Tag 0C3K] on a fibre.

## The five steps of the proof, and where each lives

* **Absolute Noetherian approximation.** `nonempty_standardNodalDiagram_of_finiteTypeOverInt` in
  `StacksFrontier.AlgebraicGeometry.Curves.StandardNodalDiagramNoetherianApproximation` reduces the
  statement to the case of an *affine* base which is Noetherian, locally Noetherian, of finite
  type over the integers and has G-ring local rings. The limit presentation of the base is
  *supplied* there, not hypothesised, and nothing further is owed for this step. Inside the
  hypothesis `H` of that reduction those five properties are handed to the argument, so the
  étale neighbourhood of the base that the next step produces and the Noetherian-stalk
  requirement of Tag 0CBX are both free; neither has to be re-derived.
* **A singular point of a fibre is a node.** `isNode_asFiber_of_mem_relativeSingular` below is
  the implication (2) ⟹ (1) of [Stacks, Tag 0C4E] on a fibre, closed by the implication
  (5) ⟹ (1) of [Stacks, Tag 0C4D]
  (`Stacks.Curves.smoothAt_or_isSeparable_and_depth_eq_one_and_fittingIdeal_eq_maximalIdeal` and
  `Stacks.Curves.isNode_tfae_of_isClosed`).
* **Reduction to a split node.** `Stacks.Curves.exists_etale_isSplitNode_fiber_baseChange` gives
  an étale `W ⟶ S` over which the node of the fibre becomes *split*. Its dimension hypothesis is
  not an extra hypothesis: it is read off the at-worst-nodal assumption through
  `AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_iff_fibres` ([Stacks, Tag 0C59]), which
  also supplies flatness and local finite presentation.
* **The formal local structure.** At a split node the completed local ring is a nodal smoothing
  `A⟦u, v⟧/(uv - h)` over the completed local ring `A` of the base, with `h` in the maximal ideal
  of `A`: [Stacks, Tag 0CBX],
  `Stacks.Curves.exists_algEquiv_adicCompletion_quotient_mvPowerSeries_of_isSplitNode`. That
  formal datum is turned into the tag's diagram by
  `nonempty_standardNodalDiagram_of_exists_algEquiv_adicCompletion`, which is [Stacks, Tag 0GDX]
  applied to the standard nodal family. The part of Tag 0GDX that is scoped out there — that its
  `y_τ` and `y_σ` are the same point of the common fibre — is not needed: the diagram uses only
  the étale morphisms and the commutativity.
* **Descent along the étale base change.** `StandardNodalDiagram.compEtale` below composes the
  two étale legs of the diagram with the two projections of the base change, which returns the
  diagram for the original family.

## Main results

* `Stacks.NodalEtaleLocalStructure.StandardNodalDiagram.compEtale` — the diagram of Tag 0CBY
  transports along étale morphisms of the source and of the base.
* `Stacks.NodalEtaleLocalStructure.mem_relativeSingular_iff_not_smoothAt_fiber` — the relative
  singular subscheme is the locus of the singular points of the fibres.
* `Stacks.NodalEtaleLocalStructure.isNode_asFiber_of_mem_relativeSingular` — a point of the
  relative singular subscheme of an at-worst-nodal family of relative dimension one is a node of
  its fibre.
* `Stacks.NodalEtaleLocalStructure.nonempty_standardNodalDiagram_of_isNode_of_isGRing` — the
  diagram of Tag 0CBY at a node of a fibre, over a locally Noetherian base whose local ring at
  the image point is a G-ring. This is the step that the Noetherian approximation consumes.
* `Stacks.NodalEtaleLocalStructure.nonempty_standardNodalDiagram_of_mem_relativeSingular` — the
  tag with the singular point read on the relative singular subscheme, which is where the whole
  argument is assembled.
* `Stacks.NodalEtaleLocalStructure.nonempty_standardNodalDiagram_of_isAtWorstNodal` — **Tag
  0CBY**, with no hypothesis beyond the tag's own: the singular point of the fibre spelled as
  the failure of smoothness of `X_s` over `κ(s)` at `x`.

## References

* [Stacks Project, Tag 0CBY](https://stacks.math.columbia.edu/tag/0CBY)
* [Stacks Project, Tag 0CBX](https://stacks.math.columbia.edu/tag/0CBX)
* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C4E](https://stacks.math.columbia.edu/tag/0C4E)
* [Stacks Project, Tag 0C3I](https://stacks.math.columbia.edu/tag/0C3I)
* [Stacks Project, Tag 0C3K](https://stacks.math.columbia.edu/tag/0C3K)
* [Stacks Project, Tag 0C59](https://stacks.math.columbia.edu/tag/0C59)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.NodalEtaleLocalStructure

/-- **The diagram of Tag 0CBY transports along étale morphisms of the source and the base.**
Let `g : Y ⟶ T` and `f : X ⟶ S` be morphisms fitting in a commutative square with étale
`eX : Y ⟶ X` and `eT : T ⟶ S`. A diagram for `g` at a point `y` of `Y` is a diagram for `f` at
the image of `y`: the étale neighbourhood of `y` in `Y` is an étale neighbourhood of `eX y` in
`X` and the étale neighbourhood of its image in `T` is one of its image in `S`, while the
right-hand cartesian square and the local model are unchanged. -/
public def StandardNodalDiagram.compEtale {X S Y T : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ T}
    {eX : Y ⟶ X} [Etale eX] {eT : T ⟶ S} [Etale eT] (hcomm : eX ≫ f = g ≫ eT) {y : Y}
    (d : StandardNodalDiagram g y) : StandardNodalDiagram f (eX.base y) where
  U := d.U
  V := d.V
  W := d.W
  toSource := d.toSource ≫ eX
  toBase := d.toBase ≫ eT
  familyU := d.familyU
  familyW := d.familyW
  toModel := d.toModel
  classifyW := d.classifyW
  classifyV := d.classifyV
  pt := d.pt
  etale_toSource := by
    have := d.etale_toSource
    infer_instance
  etale_toBase := by
    have := d.etale_toBase
    infer_instance
  etale_toModel := d.etale_toModel
  pt_mem := by rw [Scheme.Hom.comp_apply, d.pt_mem]
  comm_left := by
    rw [Category.assoc, hcomm, ← Category.assoc, d.comm_left, Category.assoc]
  comm_model := d.comm_model
  isPullback_model := d.isPullback_model

/-- **A point lies in the relative singular subscheme exactly when its fibre is singular there.**
For `f` at-worst-nodal of relative dimension one the relative singular subscheme `Sing(f) ⊆ X`,
cut out by the first Fitting ideal of `Ω_{X/S}`, is the locus of the singular points of the
fibres of `f`.

The relative singular subscheme of a fibre is the inverse image of `Sing(f)`
([Stacks, Tag 0C3I], `AlgebraicGeometry.relativeSingularIdeal_comap_fiberι`), and on a fibre —
a scheme over a field, flat and locally of finite presentation, equidimensional of dimension one
— that subscheme cuts out the nonsmooth locus ([Stacks, Tag 0C3K]). -/
public theorem mem_relativeSingular_iff_not_smoothAt_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) (x : X) :
    x ∈ Set.range (relativeSingularIdeal f).subschemeι.base ↔
      ¬ InfinitesimalLifting.SmoothAt (f.fiberToSpecResidueField (f x)) (f.asFiber x) := by
  obtain ⟨hflat, hlfp, hrd, -⟩ := (isAtWorstNodalOfRelativeDimensionOne_iff_fibres f).mp hf
  have : Flat f := hflat
  have : LocallyOfFinitePresentation f := hlfp
  have : LocallyOfFiniteType f := inferInstance
  obtain ⟨hequi, hdim⟩ := hrd (f x) ⟨f.asFiber x⟩
  have hLOFT : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
    dsimp only [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
    infer_instance
  have := hLOFT
  have hRD : RelativeDimension (f.fiberToSpecResidueField (f x)) 1 :=
    Stacks.Curves.relativeDimension_one_of_equidimensional ↥(S.residueField (f x))
      (f.fiberToSpecResidueField (f x)) hequi hdim
  have hfibmem : f.asFiber x ∈
        Set.range (relativeSingularIdeal (f.fiberToSpecResidueField (f x))).subschemeι.base ↔
      x ∈ Set.range (relativeSingularIdeal f).subschemeι.base := by
    have hrange : Set.range ((relativeSingularIdeal f).comap (f.fiberι (f x))).subschemeι.base =
        (f.fiberι (f x)).base ⁻¹' Set.range (relativeSingularIdeal f).subschemeι.base := by
      simp only [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap,
        TopologicalSpace.Closeds.coe_preimage]
    rw [← relativeSingularIdeal_comap_fiberι f (f x), hrange, Set.mem_preimage,
      show (f.fiberι (f x)).base (f.asFiber x) = x from by simp]
  rw [← hfibmem]
  exact mem_fittingIdeal_relativeDifferentials_iff_not_smoothAt
    (f.fiberToSpecResidueField (f x)) 1 hRD (f.asFiber x)

/-- **A singular point of a fibre of an at-worst-nodal family of relative dimension one is a
node of that fibre.** The singular points of the fibres of `f` are the points of the relative
singular subscheme `Sing(f) ⊆ X`, so this is the implication (2) ⟹ (1) of [Stacks, Tag 0C4E]
read on a fibre of the family, together with the implication (5) ⟹ (1) of [Stacks, Tag 0C4D].

Three things are needed at the point. It is a *closed* point of its fibre, because `Sing(f)` is
unramified over `S` and so the residue field extension there is separable algebraic
([Stacks, Tag 02G8]) — this is `AlgebraicGeometry.isClosed_asFiber_of_isAlgebraic_residueField`.
The fibre is not smooth there, because the relative singular subscheme of the fibre is the
inverse image of `Sing(f)` ([Stacks, Tag 0C3I]) and cuts out the nonsmooth locus
([Stacks, Tag 0C3K]). And the residue field extension of the fibre at the point is separable,
which is the same separability carried to the fibre's own residue field by
`AlgebraicGeometry.nonempty_fiberResidueFieldAlgEquiv`. Tag 0C4E then gives depth one and the
Fitting-ideal condition, which is condition (5) of Tag 0C4D. -/
public theorem isNode_asFiber_of_mem_relativeSingular {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) {x : X}
    (hx : x ∈ Set.range (relativeSingularIdeal f).subschemeι.base) :
    letI := f.fiberOverSpecResidueField (f x)
    Stacks.Curves.IsNode (S.residueField (f x)) (f.fiber (f x)) (f.asFiber x) := by
  obtain ⟨hflat, hlfp, hrd, hfib⟩ := (isAtWorstNodalOfRelativeDimensionOne_iff_fibres f).mp hf
  have : Flat f := hflat
  have : LocallyOfFinitePresentation f := hlfp
  have : LocallyOfFiniteType f := inferInstance
  have : Unramified ((relativeSingularIdeal f).subschemeι ≫ f) := hf.2
  obtain ⟨z, hz⟩ := hx
  subst hz
  set x : X := (relativeSingularIdeal f).subschemeι.base z
  let := f.fiberOverSpecResidueField (f x)
  let : Algebra ↥(S.residueField (f x)) ↥(X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  -- the residue field extension at `x` is separable: `Sing(f)` is unramified over `S`
  have hsepX : Algebra.IsSeparable ↥(S.residueField (f x)) ↥(X.residueField x) :=
    Stacks.Curves.isSeparable_residueField_of_unramified_comp f
      (relativeSingularIdeal f).subschemeι z
  -- hence `x` is a closed point of its fibre
  have hcl : IsClosed ({f.asFiber x} : Set (f.fiber (f x))) :=
    isClosed_asFiber_of_isAlgebraic_residueField f x inferInstance
  obtain ⟨hequi, hdim⟩ := hrd (f x) ⟨f.asFiber x⟩
  obtain ⟨hlci, hZfib⟩ := hfib (f x)
  have hLOFT : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
    dsimp only [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
    infer_instance
  have := hLOFT
  have : LocallyOfFiniteType ((f.fiber (f x)) ↘ Spec (.of ↥(S.residueField (f x)))) := hLOFT
  -- the fibre is not smooth there, Tags 0C3I and 0C3K
  have hns : ¬ InfinitesimalLifting.SmoothAt (f.fiberToSpecResidueField (f x)) (f.asFiber x) :=
    (mem_relativeSingular_iff_not_smoothAt_fiber f hf x).mp ⟨z, rfl⟩
  -- Tag 0C4E at the closed point: depth one and the Fitting-ideal condition
  obtain ⟨-, -, hdepth, hfitt⟩ :=
    (Stacks.Curves.smoothAt_or_isSeparable_and_depth_eq_one_and_fittingIdeal_eq_maximalIdeal
      ↥(S.residueField (f x)) (f.fiberToSpecResidueField (f x)) hequi hdim hlci hZfib
      (f.asFiber x) hcl).resolve_left hns
  -- the separability of the residue field extension, read on the fibre
  let : Algebra ↥(S.residueField (f x)) ↥((f.fiber (f x)).residueField (f.asFiber x)) :=
    ((Scheme.ΓSpecIso (.of ↥(S.residueField (f x)))).inv ≫
      (f.fiberToSpecResidueField (f x)).appTop ≫
        (f.fiber (f x)).Γevaluation (f.asFiber x)).hom.toAlgebra
  obtain ⟨e⟩ := nonempty_fiberResidueFieldAlgEquiv f x
  have hsepF : Algebra.IsSeparable ↥(S.residueField (f x))
      ↥((f.fiber (f x)).residueField (f.asFiber x)) := AlgEquiv.Algebra.isSeparable e.symm
  -- Tag 0C4D, condition (5) implies condition (1)
  have htfae := Stacks.Curves.isNode_tfae_of_isClosed ↥(S.residueField (f x)) (f.fiber (f x))
    hdim (f.asFiber x) hcl
  have h51 := (htfae.out 5 1).mp
  exact h51 ⟨@Algebra.IsSeparableExtension.of_isSeparable _ _ _ _ _ hsepF, hdepth, hfitt⟩

/-- **Tag 0CBY at a node of a fibre, over a locally Noetherian base with a G-ring local ring.**
Let `f : X ⟶ S` be at-worst-nodal of relative dimension one over a locally Noetherian base and
let `x` be a point of `X` which is a node of the fibre through it — that is, a singular point of
that fibre, nodality of the singularities of the fibres being part of the at-worst-nodal
hypothesis. If the local ring of `S` at the image of `x` is a G-ring, the diagram of
[Stacks, Tag 0CBY] exists at `x`.

The two hypotheses beyond the tag's own — local Noetherianness of `S` and the G-ring property —
are what the source's first step, absolute Noetherian approximation, provides by replacing `S`
by a base of finite type over the integers; that reduction is
`Stacks.NodalEtaleLocalStructure.nonempty_standardNodalDiagram_of_finiteTypeOverInt`, and
`Stacks.NodalEtaleLocalStructure.nonempty_standardNodalDiagram_of_mem_relativeSingular` is this
statement with both discharged through it. -/
public theorem nonempty_standardNodalDiagram_of_isNode_of_isGRing {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] (hf : IsAtWorstNodalOfRelativeDimensionOne f) (x : X)
    (hG : IsGRing (S.presheaf.stalk (f x)))
    (hnode : letI := f.fiberOverSpecResidueField (f x)
      Stacks.Curves.IsNode (S.residueField (f x)) (f.fiber (f x)) (f.asFiber x)) :
    Nonempty (StandardNodalDiagram f x) := by
  obtain ⟨hflat, hlfp, hrd, -⟩ := (isAtWorstNodalOfRelativeDimensionOne_iff_fibres f).mp hf
  have : Flat f := hflat
  have : LocallyOfFinitePresentation f := hlfp
  have : LocallyOfFiniteType f := inferInstance
  have hdim : topologicalKrullDim (f.fiber (f x)) = (1 : WithBot ℕ∞) :=
    (hrd (f x) ⟨f.asFiber x⟩).2
  obtain ⟨W, eW, hEt, t', ht', hsplit⟩ :=
    Stacks.Curves.exists_etale_isSplitNode_fiber_baseChange f x hdim hnode
  have := hEt
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian eW
  have hpt : eW.base ((pullback.snd f eW).base t') = f.base x := by
    have hc := congrArg (fun φ : (pullback f eW : Scheme.{u}) ⟶ S => φ.base t')
      (pullback.condition (f := f) (g := eW))
    simp only [Scheme.Hom.comp_apply] at hc
    rw [← hc, ht']
  have hGW : IsGRing (W.presheaf.stalk ((pullback.snd f eW).base t')) := by
    have hGS : IsGRing ↥(S.presheaf.stalk (eW.base ((pullback.snd f eW).base t'))) := by
      rw [hpt]; exact hG
    let : Algebra ↥(S.presheaf.stalk (eW.base ((pullback.snd f eW).base t')))
        ↥(W.presheaf.stalk ((pullback.snd f eW).base t')) :=
      (eW.stalkMap ((pullback.snd f eW).base t')).hom.toAlgebra
    have : Algebra.EssFiniteType ↥(S.presheaf.stalk (eW.base ((pullback.snd f eW).base t')))
        ↥(W.presheaf.stalk ((pullback.snd f eW).base t')) :=
      LocallyOfFiniteType.stalkMap eW ((pullback.snd f eW).base t')
    exact isGRing_of_essFiniteType hGS
  have hCBX := Stacks.Curves.exists_algEquiv_adicCompletion_quotient_mvPowerSeries_of_isSplitNode
    (pullback.snd f eW) t' (Flat.stalkMap (pullback.snd f eW) t') hsplit
  obtain ⟨d⟩ := nonempty_standardNodalDiagram_of_exists_algEquiv_adicCompletion
    (pullback.snd f eW) t' hGW hCBX
  exact ⟨ht' ▸ d.compEtale (f := f) (pullback.condition (f := f) (g := eW))⟩

/-- **Tag 0CBY, with the singular point of the fibre read on the relative singular subscheme.**
Let `f : X ⟶ S` be at-worst-nodal of relative dimension one and let `x` be a point of the
relative singular subscheme `Sing(f) ⊆ X`. Then the diagram of the tag exists at `x`.

This is the spelling the source's own proof uses, because `Sing(f)` is what the first step
carries along the Noetherian approximation; `Sing(f)` is the locus of the singular points of the
fibres by `mem_relativeSingular_iff_not_smoothAt_fiber`, and
`nonempty_standardNodalDiagram_of_isAtWorstNodal` is this statement written with that
singularity instead.

The proof is the first proof of the tag, in four steps. Absolute Noetherian approximation
reduces the base to an affine Noetherian scheme of finite type over the integers, where the local
rings are G-rings (`nonempty_standardNodalDiagram_of_finiteTypeOverInt`). There the singular
point of the fibre is a node (`isNode_asFiber_of_mem_relativeSingular`), which becomes a *split*
node after an étale base change of the base
(`Stacks.Curves.exists_etale_isSplitNode_fiber_baseChange`). At a split node the completed local
ring is `A⟦u, v⟧/(uv - h)` over the completed local ring `A` of the base ([Stacks, Tag 0CBX]),
and Artin approximation for the standard nodal family turns that formal datum into the diagram
([Stacks, Tag 0GDX], through
`nonempty_standardNodalDiagram_of_exists_algEquiv_adicCompletion`); the diagram then descends
along the étale base change by `StandardNodalDiagram.compEtale`. -/
public theorem nonempty_standardNodalDiagram_of_mem_relativeSingular {X S : Scheme.{u}}
    (f : X ⟶ S) (hf : IsAtWorstNodalOfRelativeDimensionOne f) {x : X}
    (hxsing : x ∈ Set.range (relativeSingularIdeal f).subschemeι.base) :
    Nonempty (StandardNodalDiagram f x) := by
  refine nonempty_standardNodalDiagram_of_finiteTypeOverInt ?_ f hf hxsing
  intro S' X' f' x' _ _ hLN _ hG hf' hx'
  have := hLN
  exact nonempty_standardNodalDiagram_of_isNode_of_isGRing f' hf' x' (hG (f' x'))
    (isNode_asFiber_of_mem_relativeSingular f' hf' hx')

/-- **Stacks Project, Tag 0CBY.** Let `f : X ⟶ S` be at-worst-nodal of relative dimension one
and let `x` be a point of `X` at which the fibre `X_s` through it is *singular*. Then there is a
commutative diagram
```
X ←—— U ——→ W ——→ Spec ℤ[u, v, a]/(uv - a)
↓     ↓     ↓                ↓
S ←———————— V ——————————→ Spec ℤ[a]
```
in which `U ⟶ X`, `V ⟶ S` and `U ⟶ W` are étale, the right-hand square is cartesian, and some
point of `U` maps to `x`. The diagram is packaged as
`Stacks.NodalEtaleLocalStructure.StandardNodalDiagram`.

The whole content is `nonempty_standardNodalDiagram_of_mem_relativeSingular`, which is the same
statement with the singular point read on the relative singular subscheme `Sing(f)`; the two
spellings agree by `mem_relativeSingular_iff_not_smoothAt_fiber`, which is [Stacks, Tag 0C3K]
on a fibre. -/
@[stacks 0CBY "the whole statement.  The diagram is the structure \
`Stacks.NodalEtaleLocalStructure.StandardNodalDiagram`, whose fields are the tag's four \
morphisms with the three etaleness assertions, the commutativity of the left and the middle \
square, the cartesianness of the right-hand square over the standard nodal family \
`Spec Z[u,v,a]/(uv-a) -> Spec Z[a]`, and the point of `U` over `x`.  The singular point of the \
fibre is spelled as the failure of smoothness of the fibre `X_s` over `kappa(s)` at `x`; the \
equivalent spelling as a point of the relative singular subscheme `Sing(f)`, which is the one \
the source's own first step carries, is \
`nonempty_standardNodalDiagram_of_mem_relativeSingular`, and the two agree by \
`mem_relativeSingular_iff_not_smoothAt_fiber` ([Stacks, Tags 0C3I and 0C3K])"]
public theorem nonempty_standardNodalDiagram_of_isAtWorstNodal {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) {x : X}
    (hxsing : ¬ InfinitesimalLifting.SmoothAt (f.fiberToSpecResidueField (f x))
      (f.asFiber x)) :
    Nonempty (StandardNodalDiagram f x) :=
  nonempty_standardNodalDiagram_of_mem_relativeSingular f hf
    ((mem_relativeSingular_iff_not_smoothAt_fiber f hf x).mpr hxsing)

end Stacks.NodalEtaleLocalStructure

end
