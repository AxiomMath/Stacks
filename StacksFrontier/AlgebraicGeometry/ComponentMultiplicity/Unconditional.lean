module

public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IdealFiltration
public import StacksFrontier.AlgebraicGeometry.ComponentDegreeReduction.FiniteFamily
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Devissage
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.StalkLengthBridge
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Devissage
public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Unconditional
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree
public import StacksCore.Tactic.StacksAttribute

/-!
# The component formula with no hypothesis

Let `k` be a field, let `f : X ⟶ Spec k` be proper with `topologicalKrullDim X ≤ 1` and let `ℰ`
be a finite locally free `𝒪_X`-module of constant rank `n`. [Stacks, Tag 0AYW] asserts

  `deg(ℰ) = ∑ᶠ ξ, m(ξ) · deg(ℰ|_{C(ξ)})`,

the sum running over the generic points of the one-dimensional irreducible components of `X`,
with `C(ξ)` the component with its reduced induced structure and `m(ξ)` its multiplicity, the
length of the local ring of `X` at `ξ`. This file proves that equation outright.

The route is a dévissage of `𝒪_X` by [Stacks, Tag 01YF] rather than the source's reduction to
the irreducible case, which needs the scheme-theoretic closures of the complements of the other
components; `ComponentMultiplicity/Devissage.lean` carries out the source's two paragraphs with
their geometric inputs as hypotheses, and its implementation notes set out the four steps used
here. Writing `D(𝒫) = χ(X, 𝒫 ⊗ ℰ) − n·χ(X, 𝒫)` for the quantity of [Stacks, Tag 0AYU]:

1. `D(𝒪_X) = deg(ℰ)`, which is the definition of the degree after
   `AlgebraicGeometry.eulerCharacteristic_unit_tensorSheaf`;
2. `D` is additive along a filtration, so `D(𝒪_X)` is the sum of its values on the successive
   quotients of the dévissage;
3. at a layer `(iⱼ : Zⱼ ⟶ X, ℐⱼ)` of [Stacks, Tag 01YF] the value `D((iⱼ)_*ℐⱼ)` is the
   multiplicity-weighted sum of the component degrees, with weights the lengths of `(iⱼ)_*ℐⱼ`
   at the generic points;
4. those weights add up to the multiplicities, which is
   `componentMultiplicity_eq_sum_stalkLength_of_filtration` of
   `ComponentMultiplicity/StalkLengthBridge.lean`.

## Main results

The elided prefix is `Stacks.AlgebraicGeometry.ComponentDegrees`.

* `curveDegree_pullback_eq_componentDegree` — the degree on an integral closed subscheme of
  dimension one is the component degree at the image of its generic point.
* `eulerCharacteristicTensorSheafSub_pushforward_eq_finsum` — **step 3**, the value of the
  quantity of [Stacks, Tag 0AYU] at a dévissage layer.
* `eulerCharacteristicTensorSheafSub_eq_sum_of_subobject_filtration` — **step 2**, additivity
  along a finite monotone chain of subobjects from `⊥` to `⊤`.
* `curveDegree_eq_finsum_componentDegree_of_isProper` — **[Stacks, Tag 0AYW]**, with no
  hypothesis the tag does not have.
* `exists_curveDegree_eq_finsum_of_isProper` — the same in the existential form the source
  states, the three proof obligations the conclusion carries being supplied.

## Implementation notes

**Step 3 splits exactly as the source's case distinction.** A layer `iⱼ : Zⱼ ⟶ X` of
[Stacks, Tag 01YF] is a closed immersion with `Zⱼ` integral, so `Zⱼ` has dimension at most zero
or exactly one (`topologicalKrullDim_le_zero_or_eq_one`). At dimension at most zero both sides
vanish: the support of `(iⱼ)_*ℐⱼ` lies in the image of `iⱼ`, which is homeomorphic to `Zⱼ`, so
clause (5) of [Stacks, Tag 0AYT] makes the left side zero, and no generic point of a
one-dimensional component lies in that image, so
`stalkLength_eq_zero_of_notMem_range` makes every term on the right zero. At dimension one `Zⱼ`
is a proper integral curve over `k`; the projection formula moves both Euler characteristics
onto `Zⱼ`, the hypothesis-free [Stacks, Tag 0AYV] evaluates their difference as
`r·deg(ℰ|_{Zⱼ})` with `r` the fibre rank of `ℐⱼ` at the generic point, and the locally finite
sum on the right collapses to its single term at `ξ = iⱼ(generic point)`, whose weight is that
same `r` by `stalkLength_pushforward` and `stalkLength_eq_fiberRank_genericPoint`.

**Identifying a layer with a component.** `exists_isIso_hom_to_reducedComponent` gives an
isomorphism `ψ : Zⱼ ⟶ C(ξ)` over `X`, and the two degrees are compared by
`AlgebraicGeometry.curveDegree_pullback` along `ψ`. Two mismatches have to be absorbed first:
the structure morphism, where `ψ ≫ (ι_ξ ≫ f)` and `iⱼ ≫ f` are equal but not syntactically so,
and the module, where `ψ^*ι_ξ^*ℰ` and `iⱼ^*ℰ` are isomorphic by
`AlgebraicGeometry.Scheme.Modules.pullbackComp`. The first is `curveDegree_congr_hom`, which
substitutes the equation and closes the goal by `rfl`: properness is a `Prop`, so the two
instance arguments are definitionally equal once the morphisms are.

**The filtration is carried by a variable module.** Step 2 is stated for an arbitrary `ℱ`
carrying the chain and is applied at `ℱ = 𝒪_X`, as
`componentMultiplicity_eq_sum_stalkLength_of_filtration` already is: at the literal
`SheafOfModules.unit X.ringCatSheaf` instance search does not find the lattice structure on
`CategoryTheory.Subobject` that `⊥` and `⊤` need, while a chain produced by [Stacks, Tag 01YF]
carries both as hypotheses.

**The weights are truncated to `ℕ` before being summed.** `stalkLength` takes values in `ℕ∞`
and `componentMultiplicity` is already a natural number, so the exchange of the finite sum over
the layers with the locally finite sum over the components is done in `ℤ`;
`sum_toNat_of_sum_eq_coe` is what makes `ENat.toNat` additive here, the hypothesis that the
total is a natural number forcing every term to be finite.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 0AYU](https://stacks.math.columbia.edu/tag/0AYU)
* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.ComponentDegrees

/-! ### The image of a closed immersion -/

/-- **The image of a closed immersion has the dimension of its source**, the immersion being a
homeomorphism onto its range. -/
theorem topologicalKrullDim_range_eq {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    topologicalKrullDim (Set.range i.base) = topologicalKrullDim Z :=
  (IsHomeomorph.topologicalKrullDim_eq _
    (IsClosedImmersion.isClosedEmbedding i).isEmbedding.toHomeomorph.isHomeomorph).symm

/-- **A subspace has dimension at most that of a subspace containing it.** -/
theorem topologicalKrullDim_le_of_subset {α : Type*} [TopologicalSpace α] {s t : Set α}
    (h : s ⊆ t) : topologicalKrullDim s ≤ topologicalKrullDim t :=
  (Topology.IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le

/-- If the generic point of a one-dimensional component lies in the image of a closed immersion
with integral source, that image is the component. -/
theorem range_eq_closure_genericPointsOne {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] (ξ : genericPointsOne X)
    (hmem : ξ.1 ∈ Set.range i.base) : Set.range i.base = closure ({ξ.1} : Set X) := by
  rw [← Stacks.AffineClosedUnion.support_ker_eq_range i,
    support_ker_eq_closure_genericPoint i,
    genericPoint_eq_of_mem_range i ξ.1 (mem_genericPointsOne_iff.mp ξ.2).1 hmem]

/-- **An integral closed subscheme of dimension at most zero misses every generic point of a
one-dimensional component**: it would otherwise be that component, which has dimension one. -/
theorem notMem_range_of_topologicalKrullDim_le_zero {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] (hZ : topologicalKrullDim Z ≤ 0)
    (ξ : genericPointsOne X) : ξ.1 ∉ Set.range i.base := by
  intro hmem
  have hone : topologicalKrullDim (closure ({ξ.1} : Set X)) = 1 :=
    (mem_genericPointsOne_iff.mp ξ.2).2
  rw [← range_eq_closure_genericPointsOne i ξ hmem, topologicalKrullDim_range_eq i] at hone
  rw [hone] at hZ
  exact absurd hZ (by decide)

/-! ### A layer of the dévissage is a component -/

/-- **The degree does not depend on which structure morphism to `Spec k` is named**, when two
are equal. Properness is a `Prop`, so the two instance arguments are definitionally equal as
soon as the two morphisms are. -/
theorem curveDegree_congr_hom (k : Type u) [Field k] {X : Scheme.{u}}
    {g g' : X ⟶ Spec (.of k)} (h : g = g') [IsProper g] [IsProper g']
    (hg : topologicalKrullDim X ≤ 1) (hg' : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank] :
    @curveDegree k _ X g ‹_› hg E rank ‹_› = @curveDegree k _ X g' ‹_› hg' E rank ‹_› := by
  subst h; rfl

/-- **The degree on an integral closed subscheme of dimension one is the component degree at the
image of its generic point.** The subscheme is isomorphic over `X` to the reduced component
indexed by that point, by
`Stacks.AlgebraicGeometry.ComponentDegrees.exists_isIso_hom_to_reducedComponent`, and the degree
is carried across the isomorphism by `AlgebraicGeometry.curveDegree_pullback`. -/
theorem curveDegree_pullback_eq_componentDegree (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hX : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (hZ : topologicalKrullDim Z = 1) :
    @curveDegree k _ Z (i ≫ f) inferInstance (le_of_eq hZ)
        ((Scheme.Modules.pullback i).obj E) rank
        (_root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback i E rank) =
      componentDegree k f hX E rank ⟨i (genericPoint (Z : Type u)),
        genericPoint_mem_genericPointsOne i hX hZ⟩ := by
  set ξ : genericPointsOne X :=
    ⟨i (genericPoint (Z : Type u)), genericPoint_mem_genericPointsOne i hX hZ⟩ with hξdef
  obtain ⟨ψ, hψ, hfac⟩ := exists_isIso_hom_to_reducedComponent i ξ rfl
  have := hψ
  let : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback i).obj E) rank :=
    _root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback i E rank
  have : IsProper (reducedComponentι X ξ ≫ f) := isProper_reducedComponentι_comp k f ξ
  have hmorph : i ≫ f = ψ ≫ (reducedComponentι X ξ ≫ f) := by rw [← Category.assoc, hfac]
  have : IsProper (ψ ≫ (reducedComponentι X ξ ≫ f)) := hmorph ▸ inferInstance
  have hC : topologicalKrullDim (reducedComponent X ξ) ≤ 1 :=
    topologicalKrullDim_reducedComponent_le X hX ξ
  let : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) rank :=
    isFiniteLocallyFreeOfRank_pullback_reducedComponentι ξ E rank
  let : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback ψ).obj
        ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E)) rank :=
    _root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback ψ _ rank
  have e : (Scheme.Modules.pullback ψ).obj
        ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) ≅
      (Scheme.Modules.pullback i).obj E :=
    (Scheme.Modules.pullbackComp ψ (reducedComponentι X ξ)).app E ≪≫
      eqToIso (congrArg (fun m => (Scheme.Modules.pullback m).obj E) hfac)
  have h1 : @curveDegree k _ Z (i ≫ f) inferInstance (le_of_eq hZ)
        ((Scheme.Modules.pullback i).obj E) rank
        (_root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback i E rank) =
      @curveDegree k _ Z (ψ ≫ (reducedComponentι X ξ ≫ f)) ‹_› (le_of_eq hZ)
        ((Scheme.Modules.pullback i).obj E) rank
        (_root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback i E rank) :=
    curveDegree_congr_hom k hmorph _ _ _ _
  rw [h1, ← curveDegree_eq_of_iso k (ψ ≫ (reducedComponentι X ξ ≫ f)) (le_of_eq hZ) rank e]
  exact curveDegree_pullback k ψ (reducedComponentι X ξ ≫ f) (le_of_eq hZ) hC _ rank

/-! ### Step 3: the quantity of [Stacks, Tag 0AYU] at a layer -/

/-- A weight `(stalkLength (i_*ℐ) x).toNat` vanishes, with its multiplier, when `x` is off the
image of `i`. -/
private theorem toNat_stalkLength_pushforward_mul_eq_zero {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (I : Z.Modules) {x : X} (hx : x ∉ Set.range i.base) (c : ℤ) :
    ((stalkLength ((Scheme.Modules.pushforward i).obj I) x).toNat : ℤ) * c = 0 := by
  rw [stalkLength_eq_zero_of_notMem_range i I x hx]; simp

/-- **Step 3 at a zero-dimensional layer: both sides vanish.** The support of `i_*ℐ` lies in the
image of `i`, which has the dimension of `Z`, so clause (5) of [Stacks, Tag 0AYT] computes
`χ(i_*ℐ ⊗ ℰ)` as `n·χ(i_*ℐ)` and the left side is zero; no generic point of a one-dimensional
component lies in that image, so every weight on the right is zero. -/
theorem eulerCharacteristicTensorSheafSub_pushforward_eq_finsum_of_le_zero
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hX : topologicalKrullDim X ≤ 1) (E : X.Modules)
    (hE : _root_.SheafOfModules.IsCoherent E) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (hZ : topologicalKrullDim Z ≤ 0) (I : Z.Modules)
    (hpush : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward i).obj I)) :
    _root_.AlgebraicGeometry.eulerCharacteristicTensorSheafSub k f E hE rank
        ((Scheme.Modules.pushforward i).obj I) hpush =
      ∑ᶠ ξ : genericPointsOne X,
        ((stalkLength ((Scheme.Modules.pushforward i).obj I) ξ.1).toNat : ℤ) *
          componentDegree k f hX E rank ξ := by
  have : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward i).obj I) := hpush
  have hsupp : topologicalKrullDim
      (_root_.SheafOfModules.supp ((Scheme.Modules.pushforward i).obj I)) ≤ 0 := by
    refine le_trans (topologicalKrullDim_le_of_subset (t := Set.range i.base) ?_) ?_
    · exact (Stacks.AlgebraicGeometry.CoherentDevissageGlue.supp_pushforward_subset_support_ker
        i I).trans (Stacks.AffineClosedUnion.support_ker_eq_range i).subset
    · rw [topologicalKrullDim_range_eq i]; exact hZ
  obtain ⟨hT, hχ⟩ := _root_.AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_rank_mul
    k f ((Scheme.Modules.pushforward i).obj I) hsupp E rank
  rw [_root_.AlgebraicGeometry.eulerCharacteristicTensorSheafSub, hχ, sub_self]
  exact (finsum_eq_zero_of_forall_eq_zero fun ξ => toNat_stalkLength_pushforward_mul_eq_zero i I
    (notMem_range_of_topologicalKrullDim_le_zero i hZ ξ) _).symm

/-- **Step 3 at a one-dimensional layer.** `Z` is then a proper integral curve over `k`. The
projection formula and the cohomology comparison along the closed immersion read both Euler
characteristics on `Z`, where the hypothesis-free [Stacks, Tag 0AYV] evaluates their difference
as `r · deg(ℰ|_Z)` for `r` the fibre rank of `ℐ` at the generic point of `Z`; on the right the
locally finite sum has the single term at `ξ = i(generic point)`, whose weight is that same
`r`. -/
@[sga "6 X 4.4" "special case"]
theorem eulerCharacteristicTensorSheafSub_pushforward_eq_finsum_of_eq_one
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hX : topologicalKrullDim X ≤ 1) (E : X.Modules)
    (hE : _root_.SheafOfModules.IsCoherent E) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (hZ : topologicalKrullDim Z = 1) (I : Z.Modules)
    (hI : _root_.SheafOfModules.IsCoherent I)
    (hpush : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward i).obj I)) :
    _root_.AlgebraicGeometry.eulerCharacteristicTensorSheafSub k f E hE rank
        ((Scheme.Modules.pushforward i).obj I) hpush =
      ∑ᶠ ξ : genericPointsOne X,
        ((stalkLength ((Scheme.Modules.pushforward i).obj I) ξ.1).toNat : ℤ) *
          componentDegree k f hX E rank ξ := by
  have : _root_.SheafOfModules.IsCoherent I := hI
  have : I.IsFiniteType := hI.isFiniteType
  have : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward i).obj I) := hpush
  have : IsLocallyNoetherian X :=
    _root_.AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian Z :=
    _root_.AlgebraicGeometry.isLocallyNoetherian_of_isClosedImmersion i
  have hEZflf : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback i).obj E) rank :=
    _root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback i E rank
  have hEZ : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pullback i).obj E) :=
    _root_.AlgebraicGeometry.isCoherent_of_isFiniteLocallyFreeOfRank _ rank
  have : IsProper (i ≫ f) := inferInstance
  have hcurve : _root_.AlgebraicGeometry.IsCurve k (i ≫ f) :=
    _root_.AlgebraicGeometry.isCurve_of_topologicalKrullDim_eq_one k (i ≫ f) hZ
  set ξ₀ : genericPointsOne X :=
    ⟨i (genericPoint (Z : Type u)), genericPoint_mem_genericPointsOne i hX hZ⟩ with hξ₀
  have hweight : stalkLength ((Scheme.Modules.pushforward i).obj I) ξ₀.1 =
      (Scheme.Modules.fiberRank I (genericPoint (Z : Type u)) : ℕ∞) :=
    (stalkLength_pushforward i I (genericPoint (Z : Type u))).trans
      (stalkLength_eq_fiberRank_genericPoint I)
  have hsingle : (∑ᶠ ξ : genericPointsOne X,
        ((stalkLength ((Scheme.Modules.pushforward i).obj I) ξ.1).toNat : ℤ) *
          componentDegree k f hX E rank ξ) =
      ((stalkLength ((Scheme.Modules.pushforward i).obj I) ξ₀.1).toNat : ℤ) *
        componentDegree k f hX E rank ξ₀ := by
    refine finsum_eq_single _ ξ₀ fun ξ hξ => ?_
    refine toNat_stalkLength_pushforward_mul_eq_zero i I (fun hmem => hξ (Subtype.ext ?_)) _
    exact (genericPoint_eq_of_mem_range i ξ.1 (mem_genericPointsOne_iff.mp ξ.2).1 hmem).symm
  rw [hsingle, hweight, ENat.toNat_coe,
    ← curveDegree_pullback_eq_componentDegree k f hX E rank i hZ]
  obtain ⟨hT, hv⟩ :=
    exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_isCurve
      k (i ≫ f) ((Scheme.Modules.pullback i).obj E) rank I
  have htens : @_root_.AlgebraicGeometry.eulerCharacteristic k _ X f _
        (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
              ((Scheme.Modules.pushforward i).obj I)).obj E)
        (@_root_.AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ E
          hpush hE) =
      @_root_.AlgebraicGeometry.eulerCharacteristic k _ Z (i ≫ f) _
        (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩).obj
              ((Scheme.Modules.pullback i).obj E)).obj I) hT :=
    (_root_.AlgebraicGeometry.eulerCharacteristic_tensorSheaf_pushforward_of_isClosedImmersion
        k i f I E hI hE hpush hEZ).trans
      (@_root_.AlgebraicGeometry.eulerCharacteristic_tensorSheaf_comm k _ Z (i ≫ f) _ I
        ((Scheme.Modules.pullback i).obj E) hI hEZ)
  have hbase : @_root_.AlgebraicGeometry.eulerCharacteristic k _ X f _
        ((Scheme.Modules.pushforward i).obj I) hpush =
      @_root_.AlgebraicGeometry.eulerCharacteristic k _ Z (i ≫ f) _ I hI :=
    _root_.AlgebraicGeometry.eulerCharacteristic_pushforward_of_isClosedImmersion k i f I hI hpush
  rw [_root_.AlgebraicGeometry.eulerCharacteristicTensorSheafSub, htens, hbase, hv]
  ring

/-- **Step 3 of the dévissage.** At a layer `(i : Z ⟶ X, ℐ)` of [Stacks, Tag 01YF] the quantity
of [Stacks, Tag 0AYU] is the sum, over the generic points of the one-dimensional components, of
the length of `i_*ℐ` there times the degree of `ℰ` on that component. A closed subscheme of a
scheme of dimension at most one has dimension at most zero or exactly one, and the two cases are
the two statements above. -/
theorem eulerCharacteristicTensorSheafSub_pushforward_eq_finsum
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hX : topologicalKrullDim X ≤ 1) (E : X.Modules)
    (hE : _root_.SheafOfModules.IsCoherent E) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (I : Z.Modules) (hI : _root_.SheafOfModules.IsCoherent I)
    (hpush : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward i).obj I)) :
    _root_.AlgebraicGeometry.eulerCharacteristicTensorSheafSub k f E hE rank
        ((Scheme.Modules.pushforward i).obj I) hpush =
      ∑ᶠ ξ : genericPointsOne X,
        ((stalkLength ((Scheme.Modules.pushforward i).obj I) ξ.1).toNat : ℤ) *
          componentDegree k f hX E rank ξ := by
  rcases topologicalKrullDim_le_zero_or_eq_one i hX with h | h
  · exact eulerCharacteristicTensorSheafSub_pushforward_eq_finsum_of_le_zero
      k f hX E hE rank i h I hpush
  · exact eulerCharacteristicTensorSheafSub_pushforward_eq_finsum_of_eq_one
      k f hX E hE rank i h I hI hpush

/-! ### Step 2: additivity along the filtration -/

/-- **A telescoping sum in a commutative monoid.** If `v (j + 1) = v j + w j` for every `j`,
then `v (last n) = v 0 + ∑ j, w j`. -/
theorem fin_sum_telescope_add' {M : Type*} [AddCommMonoid M] {n : ℕ}
    (v : Fin (n + 1) → M) (w : Fin n → M)
    (h : ∀ j, v j.succ = v j.castSucc + w j) :
    v (Fin.last n) = v 0 + ∑ j : Fin n, w j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have ht := ih (fun i => v i.succ) (fun i => w i.succ) (by
      intro i
      simpa [Fin.castSucc_succ] using h i.succ)
    have hend : v (Fin.last n).succ = v (Fin.last (n + 1)) := by simp [Fin.succ_last]
    have h0 := h (0 : Fin (n + 1))
    simp only [Fin.castSucc_zero] at h0
    rw [← hend, ht, h0, add_assoc]

/-- **The quantity of [Stacks, Tag 0AYU] is an isomorphism invariant.** -/
theorem eulerCharacteristicTensorSheafSub_eq_of_iso (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (E : X.Modules)
    (hE : _root_.SheafOfModules.IsCoherent E) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    {P Q : X.Modules} (hP : _root_.SheafOfModules.IsCoherent P)
    (hQ : _root_.SheafOfModules.IsCoherent Q) (e : P ≅ Q) :
    _root_.AlgebraicGeometry.eulerCharacteristicTensorSheafSub k f E hE rank P hP =
      _root_.AlgebraicGeometry.eulerCharacteristicTensorSheafSub k f E hE rank Q hQ := by
  rw [_root_.AlgebraicGeometry.eulerCharacteristicTensorSheafSub,
    _root_.AlgebraicGeometry.eulerCharacteristicTensorSheafSub]
  congr 1
  · exact @_root_.AlgebraicGeometry.eulerCharacteristic_eq_of_iso k _ X f _ _ _
      (@_root_.AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ E hP hE)
      (@_root_.AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ E hQ hE)
      (Stacks.Tag01VSPullbackTensor.tensorSheafMapIso e (Iso.refl E))
  · exact congrArg (fun z : ℤ => (rank : ℤ) * z)
      (@_root_.AlgebraicGeometry.eulerCharacteristic_eq_of_iso k _ X f _ _ _ hP hQ e)

/-- **Step 2 of the dévissage**: the quantity of [Stacks, Tag 0AYU] at `ℱ` is the sum of its
values on the successive quotients of a finite monotone chain of subobjects of `ℱ` from `⊥` to
`⊤`. Only additivity along a short exact sequence is used, so nothing is assumed about the
quotients beyond coherence. -/
theorem eulerCharacteristicTensorSheafSub_eq_sum_of_subobject_filtration
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (E : X.Modules) (hE : _root_.SheafOfModules.IsCoherent E) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    (h02O6 : ∀ G : X.Modules, _root_.SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (_root_.AlgebraicGeometry.cohomologyOverField k f G m))
    (F : X.Modules) (hF : _root_.SheafOfModules.IsCoherent F) {n : ℕ}
    (G : Fin (n + 1) → CategoryTheory.Subobject F) (hG : Monotone G)
    (hbot : G 0 = ⊥) (htop : G (Fin.last n) = ⊤)
    (hcoh : ∀ j, _root_.SheafOfModules.IsCoherent (G j : X.Modules))
    (hq : ∀ j : Fin n, _root_.SheafOfModules.IsCoherent (filtrationQuotient G hG j)) :
    _root_.AlgebraicGeometry.eulerCharacteristicTensorSheafSub k f E hE rank F hF =
      ∑ j : Fin n, _root_.AlgebraicGeometry.eulerCharacteristicTensorSheafSub k f E hE rank
        (filtrationQuotient G hG j) (hq j) := by
  have hlast : ((G (Fin.last n) : CategoryTheory.Subobject F) : X.Modules) ≅ F :=
    CategoryTheory.Subobject.isoOfEq _ _ htop ≪≫
      asIso (⊤ : CategoryTheory.Subobject F).arrow
  have hzero : _root_.AlgebraicGeometry.eulerCharacteristicTensorSheafSub k f E hE rank
      ((G 0 : CategoryTheory.Subobject F) : X.Modules) (hcoh 0) = 0 := by
    refine _root_.AlgebraicGeometry.eulerCharacteristicTensorSheafSub_eq_zero_of_isZero
      k f E hE rank _ (hcoh 0) ?_ h02O6
    rw [hbot]
    exact (CategoryTheory.Limits.isZero_zero X.Modules).of_iso
      CategoryTheory.Subobject.botCoeIsoZero
  have hadd := fin_sum_telescope_add'
    (fun j => _root_.AlgebraicGeometry.eulerCharacteristicTensorSheafSub k f E hE rank
      ((G j : CategoryTheory.Subobject F) : X.Modules) (hcoh j))
    (fun j => _root_.AlgebraicGeometry.eulerCharacteristicTensorSheafSub k f E hE rank
      (filtrationQuotient G hG j) (hq j))
    (fun j => _root_.AlgebraicGeometry.eulerCharacteristicTensorSheafSub_add_of_shortExact
      k f E hE rank (shortExact_filtrationStep G hG j) (hcoh j.castSucc) (hcoh j.succ) (hq j)
      h02O6)
  rw [eulerCharacteristicTensorSheafSub_eq_of_iso k f E hE rank hF (hcoh (Fin.last n))
    hlast.symm]
  simpa [hzero] using hadd

/-! ### The component formula -/

/-- **Truncation is additive on a finite family of extended naturals with natural total.** If
`∑ a j` is the natural number `m`, then `m = ∑ (a j).toNat`: no term can be `⊤`, since it is
bounded by the total. -/
theorem sum_toNat_of_sum_eq_coe {ι : Type*} [Fintype ι] (a : ι → ℕ∞) (m : ℕ)
    (h : (m : ℕ∞) = ∑ j, a j) : (m : ℤ) = ∑ j, ((a j).toNat : ℤ) := by
  have hne : ∀ j, a j ≠ ⊤ := by
    intro j hj
    have hle : a j ≤ ∑ j, a j :=
      Finset.single_le_sum (f := a) (fun _ _ => zero_le) (Finset.mem_univ j)
    rw [← h, hj] at hle
    simp at hle
  have hcast : (m : ℕ∞) = ((∑ j, (a j).toNat : ℕ) : ℕ∞) := by
    rw [h, Nat.cast_sum]
    exact Finset.sum_congr rfl fun j _ => (ENat.coe_toNat (hne j)).symm
  have hm : m = ∑ j, (a j).toNat := by exact_mod_cast hcast
  rw [hm, Nat.cast_sum]

/-- **[Stacks, Tag 0AYW].** The degree of a finite locally free module of constant rank on a
proper scheme of dimension at most one over a field is the multiplicity-weighted sum of its
degrees on the reduced one-dimensional components.

The four steps are: the degree is the quantity `D(𝒫) = χ(𝒫 ⊗ ℰ) − n·χ(𝒫)` of
[Stacks, Tag 0AYU] at `𝒫 = 𝒪_X`; `D` is additive along the dévissage of [Stacks, Tag 01YF]
applied to `𝒪_X`; at each layer `D` is the weighted sum of the component degrees, the weights
being the lengths of the layer at the generic points; and those lengths add up to the
multiplicities. -/
@[stacks 0AYW]
theorem curveDegree_eq_finsum_componentDegree_of_isProper (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (hX : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank] :
    _root_.AlgebraicGeometry.curveDegree k f hX E rank =
      ∑ᶠ ξ : genericPointsOne X,
        (componentMultiplicity X ξ : ℤ) * componentDegree k f hX E rank ξ := by
  classical
  have : IsNoetherian X := isNoetherian_of_isProper_over_field k f
  have : IsLocallyNoetherian X :=
    _root_.AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f
  have hE : _root_.SheafOfModules.IsCoherent E :=
    _root_.AlgebraicGeometry.isCoherent_of_isFiniteLocallyFreeOfRank E rank
  have hunit : _root_.SheafOfModules.IsCoherent (_root_.SheafOfModules.unit X.ringCatSheaf) :=
    inferInstance
  have h02O6 :=
    _root_.AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper k f
  obtain ⟨n, G, hG, hbot, htop, hcoh, hquot⟩ :=
    Stacks.AlgebraicGeometry.CoherentDevissage.exists_filtration_by_integral_ideal_pushforwards X
      (_root_.SheafOfModules.unit X.ringCatSheaf)
  have hq : ∀ j : Fin n,
      _root_.SheafOfModules.IsCoherent (filtrationQuotient G hG j) := by
    intro j
    have := hcoh j.castSucc
    have := hcoh j.succ
    exact _root_.SheafOfModules.cokernel_isCoherent _
  have hstep1 : _root_.AlgebraicGeometry.eulerCharacteristicTensorSheafSub k f E hE rank
      (_root_.SheafOfModules.unit X.ringCatSheaf) hunit =
      _root_.AlgebraicGeometry.curveDegree k f hX E rank :=
    (congrArg (fun z : ℤ => z - (rank : ℤ) * @_root_.AlgebraicGeometry.eulerCharacteristic k _ X
        f _ (_root_.SheafOfModules.unit X.ringCatSheaf) hunit)
      (_root_.AlgebraicGeometry.eulerCharacteristic_unit_tensorSheaf k f E hE hunit)).trans
      (@_root_.AlgebraicGeometry.curveDegree_eq_eulerCharacteristic_sub k _ X f _ hX E rank
        _ hE hunit).symm
  have hstep2 := eulerCharacteristicTensorSheafSub_eq_sum_of_subobject_filtration
    k f E hE rank h02O6 (_root_.SheafOfModules.unit X.ringCatSheaf) hunit G hG hbot htop hcoh hq
  have hlayer : ∀ j : Fin n,
      _root_.AlgebraicGeometry.eulerCharacteristicTensorSheafSub k f E hE rank
          (filtrationQuotient G hG j) (hq j) =
        ∑ᶠ ξ : genericPointsOne X,
          ((stalkLength (filtrationQuotient G hG j) ξ.1).toNat : ℤ) *
            componentDegree k f hX E rank ξ := by
    intro j
    obtain ⟨Z, i, hi, hZint, I, hIcoh, _, ⟨e⟩⟩ := hquot j
    have := hi
    have := hZint
    have := hIcoh
    have hpush : _root_.SheafOfModules.IsCoherent
        ((Scheme.Modules.pushforward i).obj I.toSheafOfModules) :=
      _root_.AlgebraicGeometry.isCoherent_pushforward_of_isClosedImmersion i _
    rw [eulerCharacteristicTensorSheafSub_eq_of_iso k f E hE rank (hq j) hpush e,
      eulerCharacteristicTensorSheafSub_pushforward_eq_finsum k f hX E hE rank i
        I.toSheafOfModules hIcoh hpush]
    exact finsum_congr fun ξ => by rw [stalkLength_of_iso e ξ.1]
  have : Finite (genericPointsOne X) := (finite_genericPointsOne X).to_subtype
  let : Fintype (genericPointsOne X) := Fintype.ofFinite _
  rw [← hstep1, hstep2]
  simp only [hlayer, finsum_eq_sum_of_fintype]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  exact (sum_toNat_of_sum_eq_coe _ _
    (componentMultiplicity_eq_sum_stalkLength_of_filtration k f ξ (Iso.refl _) G hG hbot
      htop)).symm

/-- **[Stacks, Tag 0AYW]**, in the existential form the source states: each reduced
one-dimensional component is proper over the base, has dimension at most one and carries a
restriction of `ℰ` that is again finite locally free of the same rank, and the component formula
holds with respect to those three proofs. -/
@[stacks 0AYW "the existential form the source states, with no hypothesis"]
theorem exists_curveDegree_eq_finsum_of_isProper (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (hX : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank] :
    ∃ (hproperC : ∀ ξ : genericPointsOne X, IsProper (reducedComponentι X ξ ≫ f))
      (hdimC : ∀ ξ : genericPointsOne X, topologicalKrullDim (reducedComponent X ξ) ≤ 1)
      (hrank : ∀ ξ : genericPointsOne X,
        _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) rank),
      _root_.AlgebraicGeometry.curveDegree k f hX E rank =
        ∑ᶠ ξ : genericPointsOne X,
          (componentMultiplicity X ξ : ℤ) *
            @curveDegree k _ (reducedComponent X ξ) (reducedComponentι X ξ ≫ f)
              (hproperC ξ) (hdimC ξ)
              ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) rank (hrank ξ) :=
  (exists_curveDegree_eq_finsum_iff k f hX E rank).2
    (curveDegree_eq_finsum_componentDegree_of_isProper k f hX E rank)

end Stacks.AlgebraicGeometry.ComponentDegrees

end
