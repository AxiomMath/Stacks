module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Topology.Constructible
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.FibreDimensionLimit.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.ConstructibleImage
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components

/-!
# Relative dimension descends to a finite stage

Let a scheme `S` be the limit of a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms, and let `f₀ : X₀ ⟶ Y₀` be a morphism of quasi-compact
and quasi-separated schemes over one stage `S₀` of the system. If `f₀` is locally of finite
presentation and its base change to `S` has relative dimension `d`, then its base change to some
later stage already has relative dimension `d`.
If instead `f₀` is only locally of finite type and the base change of `f₀` to `S` has relative
dimension at most `d`, then the base change of `f₀` to some later stage already has relative
dimension at most `d`.

## Main results

* `AlgebraicGeometry.exists_relativeDimension_baseChange_of_relativeDimension_limitBaseChange`
  descends relative dimension from the limit to a finite stage.
* `AlgebraicGeometry.exists_relativeDimensionLE_baseChange_of_limitBaseChange` descends a bound
  on the relative dimension from the limit to a finite stage.

## Implementation notes

The inverse system, its chosen limit cone and its chosen index are bundled in
`AlgebraicGeometry.DescentSituation`, the directed-set form of the standing situation; the
morphism `f₀` and the schemes over the stage are given as objects and a morphism of
`CategoryTheory.Over`. The base change of `f₀` to a stage is written
`AlgebraicGeometry.baseChangeMap`, the morphism `S_i ×_{S₀} X₀ ⟶ S_i ×_{S₀} Y₀`, rather than the
isomorphic `CategoryTheory.Over.pullback` form: relative dimension is not a
`CategoryTheory.MorphismProperty`, so there is no transfer along an isomorphism of arrows to be
had for free, and this spelling makes the base-change square of Tag 02FY literally available.

The argument is the source's. Relative dimension `d` bounds the dimensions of the fibres of the
limit morphism by `d`, so Tag 05M5 provides a stage at which every fibre of `f_i` has dimension
at most `d`; the index category of Tag 05M5 is instantiated at the slice
`CategoryTheory.Over (op D.base)`, with the diagram, cone and comparison squares supplied by
`AlgebraicGeometry.baseChangeDiagram`, `AlgebraicGeometry.baseChangeConeIsLimit` and
`AlgebraicGeometry.baseChangeDiagramMap_isPullback`. For the matching lower bound, the locus in
`X₀` where the fibre of `f₀` has local dimension at most `d - 1` is open by Tag 02FZ and
retrocompact by Tag 02G0, hence quasi-compact because `X₀` is; so it is the range of an open
immersion from a quasi-compact scheme, and Tag 05F3 applies to it directly. This replaces the
source's appeal to constructibility and Tag 05F4: no Chevalley-type image theorem for the
structure morphism of `X₀` is needed, which matters because `X₀ ⟶ S₀` is not assumed to be of
finite presentation. The two stages are then merged by directedness, and the pointwise equality
of the local fibre dimension with `d` is turned back into relative dimension `d` through
Tag 0A21: the local dimension of a scheme locally of finite type over a field is the largest
dimension of an irreducible component through the point.

The case `d = 0` carries no lower-bound content and is handled by the nonnegativity of the local
dimension at a point.

Two general instances are declared here, that the base change of a morphism locally of finite
type (respectively quasi-compact) along `AlgebraicGeometry.baseChangeMap` is again such. They
are what lets the statement of the theorem be written at all, the definition of relative
dimension taking the local finite-type condition as an instance argument.

The quasi-separatedness of `X₀` is unused by this proof, but it is part of the standing
situation and is kept.
Tags 0EY2 and 0H3V are different statements and neither subsumes the other, so neither is a
duplicate of the other. Tag 0EY2 descends relative dimension exactly `d`
(`AlgebraicGeometry.RelativeDimension`) and assumes `f₀` locally of finite presentation: its
lower bound on the fibre dimensions needs the locus where the fibre dimension drops to be
retrocompact. Tag 0H3V descends the weaker property of having relative dimension at most `d`
(`AlgebraicGeometry.RelativeDimensionLE`) and assumes only that `f₀` is locally of finite type,
because only the upper bound is at stake; it is therefore the upper half of the 0EY2 argument on
its own, proved from the same Tag 05M5 step, with the bound carried between the pointwise form of
`AlgebraicGeometry.RelativeDimensionLE` and the fibrewise form
`AlgebraicGeometry.Scheme.Hom.fiberDimension` of Tag 05F8.

Tag 0H3V is phrased on `AlgebraicGeometry.DescentSituation` and `AlgebraicGeometry.baseChangeMap`
exactly as Tag 0EY2 is, rather than on a bare cofiltered cone. Situation 081D is a directed
system, so this is the faithful reading; the directed index set is small, which makes the
essential smallness that Tag 05M5 requires of its index category automatic; and the instance
`AlgebraicGeometry.locallyOfFiniteType_baseChangeMap` declared below supplies the local
finite-type instance that `AlgebraicGeometry.RelativeDimensionLE` takes as an argument, so the
statement needs no `letI`.

## References

* [Stacks Project, Tag 0EY2](https://stacks.math.columbia.edu/tag/0EY2)
* [Stacks Project, Tag 081D](https://stacks.math.columbia.edu/tag/081D)
* [Stacks Project, Tag 0H3V](https://stacks.math.columbia.edu/tag/0H3V)
* [Stacks Project, Tag 05M5](https://stacks.math.columbia.edu/tag/05M5)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- For a scheme locally of finite type over a field whose local dimension is the constant `d`
at every point, the local dimension at a point is the dimension of any irreducible component
through it; so the space is equidimensional of dimension `d`. -/
private theorem equidimensional_and_topologicalKrullDim_of_localDim_eq
    (k : Type u) [Field k] {X : Scheme.{u}} (q : X ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [Nonempty X] {d : ℕ}
    (hpoint : ∀ x : X, topologicalKrullDimAt X x = (d : WithBot ℕ∞)) :
    TopologicalSpace.Equidimensional X ∧ topologicalKrullDim X = (d : WithBot ℕ∞) := by
  classical
  have hcomponent : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (d : WithBot ℕ∞) := by
    intro Z hZ
    let η := hZ.1.genericPoint
    have hη : IsGenericPoint η Z :=
      hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
    have hindex : {W ∈ irreducibleComponents X | η ∈ W} = {Z} := by
      ext W
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      refine ⟨fun ⟨hW, hηW⟩ => ?_, fun hW => hW ▸ ⟨hZ, hη.mem⟩⟩
      have hZW : Z ⊆ W :=
        (hη.mem_closed_set_iff (isClosed_of_mem_irreducibleComponents W hW)).mp hηW
      exact Set.Subset.antisymm (hZ.2 hW.1 hZW) hZW
    rw [← hpoint η, topologicalKrullDimAt_eq_iSup_irreducibleComponents k X q η, hindex]
    simp
  refine ⟨fun Z hZ W hW => by rw [hcomponent Z hZ, hcomponent W hW], ?_⟩
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  simp_rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim, hpoint]
  simp

/-- A morphism locally of finite type whose fibre has local dimension `d` at every point of its
source has relative dimension `d`. -/
private theorem relativeDimension_of_forall_topologicalKrullDimAt_eq
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] {d : ℕ}
    (hpoint : ∀ x : X,
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞)) :
    RelativeDimension f d := by
  rw [relativeDimension_iff]
  intro s hs
  let k := S.residueField s
  let q := f.fiberToSpecResidueField s
  let : LocallyOfFiniteType q := Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField f s
  let : Nonempty (f.fiber s) := hs
  apply equidimensional_and_topologicalKrullDim_of_localDim_eq k q (d := d)
  intro z
  let x := f.fiberι s z
  have hfx : f x = s := by simpa [x] using (f.fiberHomeo s z).2
  have hpre : f ⁻¹' {f x} = f ⁻¹' {s} := by rw [hfx]
  let e : f.fiber (f x) ≃ₜ f.fiber s :=
    (f.fiberHomeo (f x)).trans ((Homeomorph.setCongr hpre).trans (f.fiberHomeo s).symm)
  have hhomeo : f.fiberHomeo (f x) (f.asFiber x) = ⟨x, rfl⟩ :=
    Subtype.ext (f.fiberι_asFiber x)
  have he : e (f.asFiber x) = z := by
    apply (f.fiberHomeo s).injective
    apply Subtype.ext
    simp [e, hhomeo, x, Homeomorph.setCongr]
  rw [← hpoint x]
  simpa [he] using (topologicalKrullDimAt_eq_of_homeomorph e (f.asFiber x)).symm

/-- A morphism of relative dimension `d` has fibre of local dimension `d` at every point of its
source. -/
private theorem topologicalKrullDimAt_eq_of_relativeDimension
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] {d : ℕ}
    (hf : RelativeDimension f d) (x : X) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞) := by
  obtain ⟨heq, hdim⟩ := hf (f x) ⟨f.asFiber x⟩
  let k := S.residueField (f x)
  let q := f.fiberToSpecResidueField (f x)
  let : LocallyOfFiniteType q := Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField f (f x)
  obtain ⟨Z, hZ, _, hZdim⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt
      k (f.fiber (f x)) q (f.asFiber x)
  have hconstant : ∀ y : f.fiber (f x),
      topologicalKrullDimAt (f.fiber (f x)) y = topologicalKrullDim Z := by
    intro y
    obtain ⟨W, hW, _, hWdim⟩ :=
      exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt
        k (f.fiber (f x)) q y
    exact hWdim.symm.trans (heq W hW Z hZ)
  have hglobal : topologicalKrullDim (f.fiber (f x)) = topologicalKrullDim Z := by
    rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    simp_rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim, hconstant]
    exact le_antisymm (iSup_le fun _ => le_rfl) (le_iSup_of_le (f.asFiber x) le_rfl)
  exact (hconstant (f.asFiber x)).trans (hglobal.symm.trans hdim)

/-- A morphism of relative dimension `d` has all its fibres of dimension at most `d`. -/
private theorem topologicalKrullDim_fiber_le_of_relativeDimension
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] {d : ℕ}
    (hf : RelativeDimension f d) (s : S) :
    topologicalKrullDim (f.fiber s) ≤ (d : WithBot ℕ∞) := by
  by_cases hs : Nonempty (f.fiber s)
  · exact (hf s hs).2 ▸ le_rfl
  · rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).mpr (not_nonempty_iff.mp hs)]
    exact bot_le

/-- A morphism locally of finite type has relative dimension at most `d` exactly when every one
of its fibres has dimension at most `d`: the relative dimension at a point is the local dimension
of the fibre through it, and the dimension of a fibre is the supremum of its local dimensions. -/
lemma relativeDimensionLE_iff_forall_fiberDimension_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (d : ℕ) :
    RelativeDimensionLE f d ↔ ∀ y : Y, f.fiberDimension y ≤ (d : WithBot ℕ∞) := by
  refine ⟨fun h y ↦ (Scheme.Hom.fiberDimension_le_iff f y _).mpr fun x _ ↦ h x, fun h x ↦ ?_⟩
  exact (Scheme.Hom.fiberDimension_le_iff f (f x) _).mp (h (f x)) x rfl

/-- The base change of a morphism locally of finite type is locally of finite type. -/
instance locallyOfFiniteType_baseChangeMap {S T : Scheme.{u}} (g : T ⟶ S)
    (X Y : Over S) (f : X ⟶ Y) [LocallyOfFiniteType f.left] :
    LocallyOfFiniteType (baseChangeMap g X Y f) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
    (baseChangeMap_isPullback g X Y f).flip inferInstance

/-- The base change of a quasi-compact morphism is quasi-compact. -/
instance quasiCompact_baseChangeMap {S T : Scheme.{u}} (g : T ⟶ S)
    (X Y : Over S) (f : X ⟶ Y) [QuasiCompact f.left] :
    QuasiCompact (baseChangeMap g X Y f) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact)
    (baseChangeMap_isPullback g X Y f).flip inferInstance

/-- A bound on the dimensions of the fibres of the base change of `f₀` to the limit of a
cofiltered system of schemes with affine transition morphisms is attained at some stage.  This is
Tag 05M5 instantiated at the slice `CategoryTheory.Over i₀`. -/
private lemma exists_stage_topologicalKrullDim_fiber_le_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀) [CompactSpace Y₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] (d : ℕ)
    (hdim : ∀ s, topologicalKrullDim ((baseChangeMap (c.π.app i₀) X₀ Y₀ f₀).fiber s) ≤
      (d : WithBot ℕ∞)) :
    ∃ j : Over i₀, ∀ s,
      topologicalKrullDim (((baseChangeDiagramMap D i₀ f₀).app j).fiber s) ≤
        (d : WithBot ℕ∞) := by
  let : ∀ {a b : Over i₀} (g : a ⟶ b),
      IsAffineHom ((baseChangeDiagram D i₀ Y₀).map g) := fun g =>
    isAffineHom_baseChangeDiagram_map D i₀ Y₀ g
  let : ∀ a : Over i₀, CompactSpace ((baseChangeDiagram D i₀ Y₀).obj a) := fun a =>
    compactSpace_baseChangeDiagram_obj D i₀ Y₀ a
  let : ∀ a : Over i₀,
      LocallyOfFiniteType ((baseChangeDiagramMap D i₀ f₀).app a) := fun a =>
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (baseChangeMap_isPullback (D.map a.hom) X₀ Y₀ f₀).flip inferInstance
  let : ∀ a : Over i₀, QuasiCompact ((baseChangeDiagramMap D i₀ f₀).app a) := fun a =>
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (baseChangeMap_isPullback (D.map a.hom) X₀ Y₀ f₀).flip inferInstance
  let : ∀ {a b : Over i₀} (g : a ⟶ b),
      IsClosedImmersion (pullback.lift ((baseChangeDiagram D i₀ X₀).map g)
        ((baseChangeDiagramMap D i₀ f₀).app a)
        ((baseChangeDiagramMap D i₀ f₀).naturality g)) := by
    intro a b g
    have := isIso_pullback_lift_of_isPullback (baseChangeDiagramMap_isPullback D i₀ f₀ g)
    infer_instance
  have hf : ∀ a : Over i₀, (baseChangeCone D c i₀ X₀).π.app a ≫
      (baseChangeDiagramMap D i₀ f₀).app a =
      baseChangeMap (c.π.app i₀) X₀ Y₀ f₀ ≫ (baseChangeCone D c i₀ Y₀).π.app a := fun a =>
    (baseChangeCone_π_isPullback D i₀ f₀ c a).w
  have hlim : ∀ a : Over i₀, IsClosedImmersion
      (pullback.lift ((baseChangeCone D c i₀ X₀).π.app a)
        (baseChangeMap (c.π.app i₀) X₀ Y₀ f₀) (hf a)) := by
    intro a
    have := isIso_pullback_lift_of_isPullback (baseChangeCone_π_isPullback D i₀ f₀ c a)
    infer_instance
  exact exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_cofiltered
    (I := Over i₀) (baseChangeDiagramMap D i₀ f₀)
    (baseChangeConeIsLimit D hc i₀ X₀) (baseChangeConeIsLimit D hc i₀ Y₀) hf hlim d hdim

section Descent

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

/-- The upper half of the descent: a stage at which every fibre of the base change of `f₀` has
dimension at most `d`, given that every fibre of the base change to the limit does.  This is
Tag 05M5 transported into the situation of Tag 081D. -/
private lemma exists_stage_topologicalKrullDim_fiber_le
    (D : DescentSituation.{u, u} I)
    (X₀ Y₀ : Over (D.system.obj (op D.base))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left] (d : ℕ)
    (hdim : ∀ s, topologicalKrullDim
        ((baseChangeMap (D.limitCone.π.app (op D.base)) X₀ Y₀ f₀).fiber s) ≤
      (d : WithBot ℕ∞)) :
    ∃ j : Over (op D.base), ∀ s,
      topologicalKrullDim
        (((baseChangeDiagramMap D.system (op D.base) f₀).app j).fiber s) ≤ (d : WithBot ℕ∞) := by
  have : Nonempty I := ⟨D.base⟩
  have : ∀ {a b : Iᵒᵖ} (g : a ⟶ b), IsAffineHom (D.system.map g) := fun g =>
    D.transition_affine g
  have : CompactSpace (D.system.obj (op D.base)) := D.quasiCompact D.base
  have : QuasiSeparatedSpace (D.system.obj (op D.base)) := D.quasiSeparated D.base
  exact exists_stage_topologicalKrullDim_fiber_le_of_isLimit D.system D.limitCone D.isLimit
    (op D.base) X₀ Y₀ f₀ d hdim

/-- A quasi-compact open of a scheme over the stage `S₀` of a directed inverse system whose
image in `S₀` misses the image of the limit also misses the image of every sufficiently late
stage.  This is Tag 05F3 applied to the open subscheme. -/
private lemma eventually_notMem_range_of_isCompact_isOpen
    (D : DescentSituation.{u, u} I)
    (X₀ : Over (D.system.obj (op D.base))) (V : Set X₀.left)
    (hV : IsOpen V) (hVc : IsCompact V)
    (hlim : ∀ x ∈ V,
      X₀.hom.base x ∉ Set.range (D.limitCone.π.app (op D.base)).base) :
    ∀ᶠ i in Filter.atTop, ∀ h : D.base ≤ i,
      ∀ x ∈ V, X₀.hom.base x ∉ Set.range (D.system.map (homOfLE h).op).base := by
  let U : X₀.left.Opens := ⟨V, hV⟩
  have : CompactSpace (U : Scheme.{u}) := by
    change CompactSpace ↥(U : Set X₀.left)
    exact isCompact_iff_compactSpace.mp hVc
  have hrange : Set.range (U.ι ≫ X₀.hom).base = X₀.hom.base '' V := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    congr 1
    exact U.range_ι
  have hempty : IsEmpty (pullback (U.ι ≫ X₀.hom)
      (D.limitCone.π.app (op D.base)) : Scheme.{u}) := by
    rw [Scheme.isEmpty_pullback_iff, Set.disjoint_left]
    intro y hy hy'
    rw [hrange] at hy
    obtain ⟨x, hxV, rfl⟩ := hy
    exact hlim x hxV hy'
  filter_upwards [eventually_isEmpty_pullback D (U : Scheme.{u}) (U.ι ≫ X₀.hom) hempty]
    with i hi h x hxV hmem
  have hdisj := Scheme.isEmpty_pullback_iff.mp (hi h)
  refine Set.disjoint_left.mp hdisj ?_ hmem
  rw [hrange]
  exact ⟨x, hxV, rfl⟩


/-- The local dimension of the fibre of a base change of `f` at a point is the local dimension
of the fibre of `f` at the image point.  This is Tag 02FY part (1) for
`AlgebraicGeometry.baseChangeMap`. -/
private lemma topologicalKrullDimAt_baseChangeMap_eq {S T : Scheme.{u}} (g : T ⟶ S)
    (X Y : Over S) (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (p : (pullback g X.hom : Scheme.{u})) :
    topologicalKrullDimAt ((baseChangeMap g X Y f).fiber ((baseChangeMap g X Y f) p))
        ((baseChangeMap g X Y f).asFiber p) =
      topologicalKrullDimAt (f.left.fiber (f.left ((pullback.snd g X.hom) p)))
        (f.left.asFiber ((pullback.snd g X.hom) p)) :=
  topologicalKrullDimAt_fiber_eq_of_isPullback (baseChangeMap_isPullback g X Y f).flip p

/-- In the situation of Tag 081D, if the base change of `f₀` to the limit has relative
dimension `d` and `f₀` is locally of finite presentation, then the base change of `f₀` to some
later stage has relative dimension `d`. -/
@[stacks 0EY2]
theorem exists_relativeDimension_baseChange_of_relativeDimension_limitBaseChange
    (D : DescentSituation.{u, u} I)
    (X₀ Y₀ : Over (D.system.obj (op D.base))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left] (d : ℕ)
    (h : RelativeDimension (baseChangeMap (D.limitCone.π.app (op D.base)) X₀ Y₀ f₀) d) :
    ∃ (i : I) (hi : D.base ≤ i),
      RelativeDimension (baseChangeMap (D.system.map (homOfLE hi).op) X₀ Y₀ f₀) d := by
  have : Nonempty I := ⟨D.base⟩
  obtain ⟨jU, hjU⟩ := exists_stage_topologicalKrullDim_fiber_le D X₀ Y₀ f₀ d
    (topologicalKrullDim_fiber_le_of_relativeDimension _ h)
  have hlower : ∀ᶠ i in Filter.atTop, ∀ hh : D.base ≤ i,
      ∀ x : (pullback (D.system.map (homOfLE hh).op) X₀.hom : Scheme.{u}),
        (d : WithBot ℕ∞) ≤ topologicalKrullDimAt
          (f₀.left.fiber (f₀.left ((pullback.snd (D.system.map (homOfLE hh).op) X₀.hom) x)))
          (f₀.left.asFiber ((pullback.snd (D.system.map (homOfLE hh).op) X₀.hom) x)) := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · filter_upwards with i hh x
      simpa using topologicalKrullDimAt_nonneg _
    · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      set V : Set X₀.left := {x | topologicalKrullDimAt (f₀.left.fiber (f₀.left x))
        (f₀.left.asFiber x) ≤ (e : WithBot ℕ∞)} with hVdef
      have hVopen : IsOpen V := isOpen_setOf_fiberDimensionAt_le f₀.left e
      have hVcpt : IsCompact V := by
        simpa using isRetrocompact_setOf_fiberDimensionAt_le f₀.left e
          isCompact_univ isOpen_univ
      have hVlim : ∀ x ∈ V,
          X₀.hom.base x ∉ Set.range (D.limitCone.π.app (op D.base)).base := by
        rintro x hxV ⟨z, hz⟩
        obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback
          (f := D.limitCone.π.app (op D.base)) (g := X₀.hom) z x hz
        have hbc := topologicalKrullDimAt_baseChangeMap_eq
          (D.limitCone.π.app (op D.base)) X₀ Y₀ f₀ p
        rw [hp] at hbc
        have hdp := topologicalKrullDimAt_eq_of_relativeDimension _ h p
        have hxd : topologicalKrullDimAt (f₀.left.fiber (f₀.left x)) (f₀.left.asFiber x) =
            ((e + 1 : ℕ) : WithBot ℕ∞) := hbc.symm.trans hdp
        rw [hVdef, Set.mem_ofPred_eq, hxd] at hxV
        exact absurd hxV (by
          simp only [not_le, Nat.cast_add, Nat.cast_one]
          exact_mod_cast WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by omega)))
      filter_upwards [eventually_notMem_range_of_isCompact_isOpen D X₀ V hVopen hVcpt hVlim]
        with i hi hh x
      have hmem : X₀.hom.base ((pullback.snd (D.system.map (homOfLE hh).op) X₀.hom) x) ∈
          Set.range (D.system.map (homOfLE hh).op).base := by
        refine ⟨(pullback.fst (D.system.map (homOfLE hh).op) X₀.hom) x, ?_⟩
        simpa only [Scheme.Hom.comp_apply] using
          congrArg (fun q : (pullback (D.system.map (homOfLE hh).op) X₀.hom : Scheme.{u}) ⟶ _ =>
            q.base x) (pullback.condition (f := D.system.map (homOfLE hh).op) (g := X₀.hom))
      have hnot := fun hx => hi hh _ hx hmem
      rw [Nat.cast_add, Nat.cast_one, ENat.WithBot.add_one_le_iff]
      exact lt_of_not_ge (by simpa [hVdef] using hnot)
  let iU : I := jU.left.unop
  have hbaseU : D.base ≤ iU := leOfHom jU.hom.unop
  obtain ⟨iS, hL0, hUS, hbaseS⟩ :=
    (hlower.and ((Filter.eventually_ge_atTop iU).and
      (Filter.eventually_ge_atTop D.base))).exists
  have hL := hL0 hbaseS
  refine ⟨iS, hbaseS, ?_⟩
  let jS : Over (op D.base) := Over.mk (homOfLE hbaseS).op
  let α : jS ⟶ jU := Over.homMk (homOfLE hUS).op (by subsingleton)
  have hftU : LocallyOfFiniteType ((baseChangeDiagramMap D.system (op D.base) f₀).app jU) :=
    inferInstanceAs (LocallyOfFiniteType (baseChangeMap (D.system.map jU.hom) X₀ Y₀ f₀))
  have key : ∀ x : (pullback (D.system.map (homOfLE hbaseS).op) X₀.hom : Scheme.{u}),
      topologicalKrullDimAt
          ((baseChangeMap (D.system.map (homOfLE hbaseS).op) X₀ Y₀ f₀).fiber
            ((baseChangeMap (D.system.map (homOfLE hbaseS).op) X₀ Y₀ f₀) x))
          ((baseChangeMap (D.system.map (homOfLE hbaseS).op) X₀ Y₀ f₀).asFiber x) =
        (d : WithBot ℕ∞) := by
    intro x
    refine le_antisymm ?_ ?_
    · refine le_trans (le_of_eq (topologicalKrullDimAt_fiber_eq_of_isPullback
        (baseChangeDiagramMap_isPullback D.system (op D.base) f₀ α) x)) ?_
      exact (topologicalKrullDimAt_le_topologicalKrullDim _).trans (hjU _)
    · rw [topologicalKrullDimAt_baseChangeMap_eq (D.system.map (homOfLE hbaseS).op) X₀ Y₀ f₀ x]
      exact hL x
  exact relativeDimension_of_forall_topologicalKrullDimAt_eq _ key

/-- In the situation of Tag 081D, if the base change of `f₀` to the limit has relative
dimension at most `d` and `f₀` is locally of finite type, then the base change of `f₀` to some
later stage has relative dimension at most `d`. -/
@[stacks 0H3V]
theorem exists_relativeDimensionLE_baseChange_of_limitBaseChange
    (D : DescentSituation.{u, u} I)
    (X₀ Y₀ : Over (D.system.obj (op D.base))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left] (d : ℕ)
    (h : RelativeDimensionLE (baseChangeMap (D.limitCone.π.app (op D.base)) X₀ Y₀ f₀) d) :
    ∃ (i : I) (hi : D.base ≤ i),
      RelativeDimensionLE (baseChangeMap (D.system.map (homOfLE hi).op) X₀ Y₀ f₀) d := by
  obtain ⟨j, hj⟩ := exists_stage_topologicalKrullDim_fiber_le D X₀ Y₀ f₀ d
    ((relativeDimensionLE_iff_forall_fiberDimension_le _ d).mp h)
  exact ⟨j.left.unop, leOfHom j.hom.unop,
    (relativeDimensionLE_iff_forall_fiberDimension_le _ d).mpr hj⟩


end Descent


/-! ### The bound on the relative dimension over a cofiltered limit -/

section Cofiltered

/-- **A bound on the relative dimension descends to a finite stage, for a cofiltered system.**
Let `D` be a cofiltered inverse system of schemes with affine transition morphisms and limit cone
`c`, and let `f₀ : X₀ ⟶ Y₀` be a quasi-compact morphism locally of finite type between schemes
over the stage `D.obj i₀`, with `Y₀` quasi-compact. If the base change of `f₀` to the limit has
relative dimension at most `d`, then so has its base change to some later stage.

This is the statement of Tag 0H3V for a cofiltered index category in the universe of the
schemes, rather than a directed set; the argument is the same appeal to Tag 05M5, instantiated at
the slice `CategoryTheory.Over i₀` exactly as in
`AlgebraicGeometry.exists_quasiFinite_baseChange_of_quasiFinite_limitBaseChange`. -/
theorem exists_relativeDimensionLE_baseChangeMap_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀) [CompactSpace Y₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] (d : ℕ)
    (h : RelativeDimensionLE (baseChangeMap (c.π.app i₀) X₀ Y₀ f₀) d) :
    ∃ (i : I) (g : i ⟶ i₀), RelativeDimensionLE (baseChangeMap (D.map g) X₀ Y₀ f₀) d := by
  obtain ⟨j, hj⟩ := exists_stage_topologicalKrullDim_fiber_le_of_isLimit D c hc i₀ X₀ Y₀ f₀ d
    ((relativeDimensionLE_iff_forall_fiberDimension_le _ d).mp h)
  exact ⟨j.left, j.hom, (relativeDimensionLE_iff_forall_fiberDimension_le
    (baseChangeMap (D.map j.hom) X₀ Y₀ f₀) d).mpr hj⟩

end Cofiltered

end AlgebraicGeometry

end
