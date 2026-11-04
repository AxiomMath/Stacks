module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Support
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.Topology.Dimension.Equidimensional
public import StacksFrontier.Topology.Dimension.LocalKrullDim
import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ExtendedIntegers
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ActionOnCycles
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Delta-dimension of an inverse image under a flat morphism of relative dimension `r`

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project — a locally Noetherian,
universally catenary scheme with a dimension function (Stacks 02QL, here
`Stacks.Chow.ChowSituation`) — let `X` and `Y` be locally of finite type over `S`, and let
`f : X ⟶ Y` be flat of relative dimension `r` in the sense of Stacks 02NJ
(`AlgebraicGeometry.RelativeDimension`). This file proves the two dimension assertions of
Stacks 02RE:

* if a closed subscheme `Z ⊆ Y` has `dim_δ Z ≤ k`, then `dim_δ (f⁻¹ Z) ≤ k + r`;
* if a coherent sheaf `F` on `Y` has `dim_δ (Supp F) ≤ k`, then `dim_δ (Supp (f^* F)) ≤ k + r`.

Together with the coherence of `f^* F` — Stacks 0EBF, `AlgebraicGeometry.isCoherent_pullback`,
which is what makes `[f^* F]_{k+r}` well formed and is attributed to Stacks 02RE below — these
are exactly the statements the source deduces from Stacks 02R8 before turning to the two cycle
identities.

The argument is the one of Stacks 02R8 read componentwise. The scheme-theoretic inverse image of
`Z` is the pullback `X ×_Y Z`, and `pullback.snd : X ×_Y Z ⟶ Z` is again flat of relative
dimension `r` by Stacks 02NK. For an irreducible component `W` of `X ×_Y Z`, flatness makes
`pullback.snd` a generalizing map, so the generic point of `W` is carried to the generic point of
an irreducible component `V` of `Z`; since the generic point of `W` is a maximal point of the
fibre through it, the local ring of that fibre there has Krull dimension zero, and the local
dimension formula for a fibre of a locally finite type morphism turns the relative dimension `r`
into the transcendence degree `r` of the residue field extension. Additivity of transcendence
degree in a tower then gives `δ W = δ V + r`, and the bound follows by taking suprema over the
components. The coherent case is reduced to the closed-subscheme case because the support of
`f^* F` is the preimage of the support of `F` (Stacks 056J), and the delta-dimension of a reduced
closed subscheme depends only on its underlying closed set.

## Main results

* `Stacks.Chow.schemeDeltaDimension_pullback_le` — **Stacks 02RE, part (1)**, the dimension
  bound `dim_δ (f⁻¹ Z) ≤ k + r`.
* `Stacks.Chow.schemeDeltaDimension_support_pullback_le` — **Stacks 02RE, part (2)**, the
  dimension bound `dim_δ (Supp (f^* F)) ≤ k + r`.
* `Stacks.Chow.schemeDeltaDimension_eq_of_equal_ranges` — delta-dimension depends only on the
  underlying closed set: two closed subschemes of one scheme with the same range have the same
  delta-dimension. This is the step the coherent case is reduced through.

## Implementation notes

The inverse image of the closed subscheme `i : Z ⟶ Y` is taken as the categorical pullback, with
`pullback.fst f i : X ×_Y Z ⟶ X` the closed immersion into `X`; this is the same representation
as in `StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Cycles`. The support of a coherent sheaf is
represented by the reduced closed subscheme `Stacks.Chow.reducedSupport` carried by it, so that
`Stacks.Chow.schemeDeltaDimension` applies; the delta-dimension of a whole scheme is valued in
`EInt`, hence the coercions.

The statement about the pullback sheaf has to name the coherence instance of
`(Scheme.Modules.pullback f).obj F` in order to form its reduced support, and that instance comes
from `AlgebraicGeometry.isCoherent_pullback`, which needs `IsLocallyNoetherian X`; the latter is
derived from `LocallyOfFiniteType sX` rather than assumed, so the instance is supplied explicitly
with `@`. `SheafOfModules.IsCoherent` is a `Prop`-valued class, so no generality is lost.

### Where the two cycle identities of Stacks 02RE are

Both **cycle identities** of the tag are proved elsewhere, each taking the dimension bounds
below as an input, so no declaration here claims one and the `@[stacks 02RE]` attributes below
are scoped to the dimension clauses.

The cycle identity of part (2), `f^*[F]_k = [f^* F]_{k+r}`, is
`Stacks.Chow.flatPullback_cycleAssociatedToCoherentSheaf` in
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.CoherentSheafCycle`. Its proof is the length
identity of Stacks 02M1,
`AlgebraicGeometry.length_baseChange_eq_length_mul_length_quotient`, applied to the stalks,
together with `Stacks.Chow.flatPullbackWeight_eq_length_quotient_extendedMaximalIdeal` for the
flat-pullback multiplicity.

The cycle identity of part (1), `[f⁻¹ Z]_{k+r} = f^*[Z]_k` for an arbitrary closed subscheme
`Z ⊆ Y`, is `Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme_of_le` in
`StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity`, in the same presentation
`pullback.fst f i` of the inverse image as the dimension bound below. As in the source it is
deduced from part (2) applied to the direct image `i_* 𝒪_Z`, through the identification of
`f^* (i_* 𝒪_Z)` with `(pullback.fst f i)_* 𝒪_{X ×_Y Z}` — the flat base change of a direct
image along a closed immersion, which is the identity `f^* 𝒪_Z = 𝒪_{f^{-1}(Z)}` of the source.
The presentation `pullback.snd i f` of the same identity is
`Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme_snd` in
`StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ClosedSubschemeCycleRules`. The special
case of an *integral* `Z` of delta-dimension exactly `k` is
`Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme` in
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Cycles`, which carries `@[stacks 02RB]`.

## References

* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK)
* [Stacks Project, Tag 02R8](https://stacks.math.columbia.edu/tag/02R8)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Casts -/

/-- The two coercions of a natural number into `EInt`, through `ℤ` and directly, agree. -/
private theorem eint_natCast_eq_intCast (n : ℕ) :
    (n : EInt) = ((n : ℤ) : EInt) := by
  norm_cast

/-! ### Local dimension of an equidimensional scheme over a field -/

/-- On an equidimensional scheme locally of finite type over a field, the local dimension at
every point is the dimension of the whole scheme: by Stacks 0A21 the local dimension at a point
is attained by an irreducible component through it, and all components have the same dimension. -/
private theorem dimensionAt_eq_of_equidimensional {k : Type u} [Field k]
    (T : Scheme.{u}) (q : T ⟶ Spec (.of k)) (hq : LocallyOfFiniteType q)
    (n : ℕ) (heq : Equidimensional T)
    (hdim : topologicalKrullDim T = (n : WithBot ℕ∞)) (x : T) :
    topologicalKrullDimAt T x = (n : WithBot ℕ∞) := by
  let _ : LocallyOfFiniteType q := hq
  have attained (y : T) : ∃ W ∈ irreducibleComponents T,
      y ∈ W ∧ topologicalKrullDim W = topologicalKrullDimAt T y :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k T q y
  obtain ⟨Z, hZ, _, hZdim⟩ := attained x
  have hconstant (y : T) : topologicalKrullDimAt T y = topologicalKrullDim Z := by
    obtain ⟨W, hW, _, hWdim⟩ := attained y
    exact hWdim.symm.trans (heq W hW Z hZ)
  have hglobal : topologicalKrullDim T = topologicalKrullDim Z := by
    rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    simp_rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
    simp_rw [hconstant]
    exact le_antisymm (iSup_le fun _ => le_rfl) (le_iSup_of_le x le_rfl)
  exact (hconstant x).trans (hglobal.symm.trans hdim)

/-! ### Generic points of components under a flat morphism -/

/-- A point specializing to the generic point of an irreducible component of a scheme is that
generic point: its closure is an irreducible set containing the component, hence equal to it. -/
private theorem eq_genericPoint_of_specializes {P : Scheme.{u}} (W : irreducibleComponents P)
    {x : P} (h : x ⤳ W.2.1.genericPoint) : x = W.2.1.genericPoint := by
  have hξW : IsGenericPoint W.2.1.genericPoint (W : Set P) :=
    W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents (W : Set P) W.2)
  have hWsub : (W : Set P) ⊆ closure ({x} : Set P) := by
    rw [← hξW]
    exact closure_minimal (Set.singleton_subset_iff.mpr h.mem_closure) isClosed_closure
  have hx : IsGenericPoint x (W : Set P) :=
    Set.Subset.antisymm (W.2.2 isIrreducible_singleton.closure hWsub) hWsub
  exact hx.eq hξW

/-- A flat morphism carries the generic point of an irreducible component of its source to the
generic point of an irreducible component of its target. Flatness enters as the going-down
property: a generalization of the image lifts, and maximality of the component forces the lift to
be the generic point itself. -/
@[ega "IV 2.3.5" "(ii), special case"]
public theorem component_genericPoint_maps_to_component_genericPoint
    {P Z : Scheme.{u}} (p : P ⟶ Z) [Flat p]
    (W : irreducibleComponents P) :
    ∃ V : irreducibleComponents Z,
      p W.2.1.genericPoint = genericPoints.ofComponent V := by
  let ξ : P := W.2.1.genericPoint
  let V : irreducibleComponents Z :=
    ⟨irreducibleComponent (p ξ), irreducibleComponent_mem_irreducibleComponents (p ξ)⟩
  let η : Z := genericPoints.ofComponent V
  have hηx : η ⤳ p ξ :=
    (genericPoints.isGenericPoint_ofComponent V).specializes mem_irreducibleComponent
  obtain ⟨ξ', hξ'ξ, hξ'η⟩ := (Flat.generalizingMap p) hηx
  have heq : ξ' = ξ := eq_genericPoint_of_specializes W hξ'ξ
  exact ⟨V, by simpa [ξ, η, heq] using hξ'η⟩

/-- At the generic point of an irreducible component of the source, the local ring of the fibre
through that point has Krull dimension zero: the point is maximal in its fibre, because any
specialization to it inside the fibre is already a generic point of the same component. -/
private theorem fiber_stalk_krullDim_eq_zero_of_generic_component
    {P Z : Scheme.{u}} (p : P ⟶ Z) (W : irreducibleComponents P) :
    ringKrullDim ((p.fiber (p W.2.1.genericPoint)).presheaf.stalk
      (p.asFiber W.2.1.genericPoint)) = 0 := by
  let ξ : P := W.2.1.genericPoint
  let y : p.fiber (p ξ) := p.asFiber ξ
  have hmax : IsMax y := by
    intro y' hy'
    have hspec : (p.fiberι (p ξ)) y' ⤳ ξ := by
      have h' : y' ⤳ y := hy'
      simpa [y, ξ] using h'.map (p.fiberι (p ξ)).continuous
    have heq : (p.fiberι (p ξ)) y' = ξ := eq_genericPoint_of_specializes W hspec
    have heqfib : y' = y := by
      apply (p.fiberι (p ξ)).isEmbedding.injective
      rw [heq]
      exact (Scheme.Hom.fiberι_asFiber p ξ).symm
    exact heqfib.le
  rw [ringKrullDim_stalk_eq_coheight (p.asFiber ξ)]
  exact_mod_cast (Order.coheight_eq_zero.mpr hmax)

/-- At the generic point of an irreducible component of the source of a morphism of relative
dimension `r`, the residue field extension has transcendence degree `r`. The fibre is
equidimensional of dimension `r`, so its local dimension at the point is `r`; the local dimension
formula splits that as the Krull dimension of the stalk, which is zero, plus the transcendence
degree. -/
@[ega "IV 5.6.5" "special case"]
private theorem toNat_trdeg_generic_component
    {P Z : Scheme.{u}} (p : P ⟶ Z) [LocallyOfFiniteType p]
    (W : irreducibleComponents P) (r : ℕ)
    (hrel : AlgebraicGeometry.RelativeDimension p r) :
    letI : Algebra (Z.residueField (p W.2.1.genericPoint))
      (P.residueField W.2.1.genericPoint) :=
        (p.residueFieldMap W.2.1.genericPoint).hom.toAlgebra
    Cardinal.toNat
      (Algebra.trdeg (Z.residueField (p W.2.1.genericPoint))
        (P.residueField W.2.1.genericPoint)) = r := by
  let ξ : P := W.2.1.genericPoint
  let η : Z := p ξ
  let F := p.fiber η
  let x : F := p.asFiber ξ
  let k : Type u := Z.residueField η
  let q := p.fiberToSpecResidueField η
  have hq : LocallyOfFiniteType q := by
    change LocallyOfFiniteType (pullback.snd p (Z.fromSpecResidueField η))
    infer_instance
  let _ : LocallyOfFiniteType q := hq
  let _ : Algebra k (P.residueField ξ) := (p.residueFieldMap ξ).hom.toAlgebra
  have hrelη := hrel η ⟨x⟩
  have hAt := dimensionAt_eq_of_equidimensional F q hq r hrelη.1 hrelη.2 x
  have hzero := fiber_stalk_krullDim_eq_zero_of_generic_component p W
  have hfx := AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg p ξ
  change topologicalKrullDimAt F x =
      ringKrullDim (F.presheaf.stalk x) +
        (Cardinal.toENat (Algebra.trdeg k (P.residueField ξ)) : WithBot ℕ∞) at hfx
  rw [hAt, hzero, zero_add] at hfx
  have hENat : Cardinal.toENat (Algebra.trdeg k (P.residueField ξ)) = r :=
    (WithBot.coe_eq_coe.mp hfx).symm
  simpa [Cardinal.toNat_toENat] using congrArg ENat.toNat hENat

private theorem deltaDimension_component_eq_of_genericPoint_map
    (C : ChowSituation.{u}) {P Z : Scheme.{u}}
    (p : P ⟶ Z) [LocallyOfFiniteType p] (q : Z ⟶ C.S) [LocallyOfFiniteType q]
    (r : ℕ) (hrel : AlgebraicGeometry.RelativeDimension p r)
    (W : irreducibleComponents P) (V : irreducibleComponents Z)
    (hη : p W.2.1.genericPoint = genericPoints.ofComponent V) :
    deltaDimension C (p ≫ q)
      ⟨(W : Set P), W.2.1, isClosed_of_mem_irreducibleComponents (W : Set P) W.2⟩ =
    deltaDimension C q
      ⟨(V : Set Z), V.2.1, isClosed_of_mem_irreducibleComponents (V : Set Z) V.2⟩ + (r : ℤ) := by
  let ξ : P := W.2.1.genericPoint
  let η : Z := genericPoints.ofComponent V
  have hξW : IsGenericPoint ξ (W : Set P) :=
    W.2.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents (W : Set P) W.2)
  have hηV : IsGenericPoint η (V : Set Z) := genericPoints.isGenericPoint_ofComponent V
  have htrdeg := toNat_trdeg_generic_component p W r hrel
  have hδ := relativeDimension_comp_add_of_trdeg C.dimensionFunction p q ξ r htrdeg
  rw [hη] at hδ
  rw [deltaDimension_eq_of_isGenericPoint C _ _ ξ hξW,
    deltaDimension_eq_of_isGenericPoint C _ _ η hηV]
  simpa [ξ, η, Category.assoc] using hδ

/-! ### Delta-dimension depends only on the underlying closed set -/

/-- Two closed subschemes of one scheme with the same underlying closed subset have the same
delta-dimension: the homeomorphism between them matches up irreducible components and their
generic points, and the relative dimension of a point of a closed subscheme is that of its
image. -/
theorem schemeDeltaDimension_eq_of_equal_ranges
    (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (i : Y ⟶ X) [IsClosedImmersion i]
    (j : Z ⟶ X) [IsClosedImmersion j]
    (hrange : Set.range i = Set.range j) :
    schemeDeltaDimension C (i ≫ p) = schemeDeltaDimension C (j ≫ p) := by
  let hi : Y ≃ₜ Set.range i := i.isClosedEmbedding.isEmbedding.toHomeomorph
  let hj : Z ≃ₜ Set.range j := j.isClosedEmbedding.isEmbedding.toHomeomorph
  let e : Y ≃ₜ Z := hi.trans ((Homeomorph.setCongr hrange).trans hj.symm)
  have he (y : Y) : i y = j (e y) := by
    have hval : Homeomorph.setCongr hrange (hi y) = hj (e y) := by simp [e, hi, hj]
    calc
      i y = (hi y : X) := rfl
      _ = (Homeomorph.setCongr hrange (hi y) : X) := rfl
      _ = (hj (e y) : X) := congrArg Subtype.val hval
      _ = j (e y) := rfl
  let ce := irreducibleComponentsEquivOfIsPreirreducibleFiber e e.continuous
    e.isOpenMap (fun z => (Set.subsingleton_singleton.preimage e.injective).isPreirreducible)
    e.surjective
  rw [schemeDeltaDimension_eq_iSup, schemeDeltaDimension_eq_iSup]
  refine (ce.symm).iSup_congr ?_
  intro W
  let V : irreducibleComponents Z := ce.symm W
  have hV : (V : Set Z) = e '' (W : Set Y) := rfl
  have hVclosed : IsClosed (e '' (W : Set Y)) := by
    rw [← hV]
    exact isClosed_of_mem_irreducibleComponents (V : Set Z) V.2
  have hgen : e (genericPoints.ofComponent W).1 = (genericPoints.ofComponent V).1 := by
    have himg := (genericPoints.isGenericPoint_ofComponent W).image e.continuous
    have himg' : IsGenericPoint (e (genericPoints.ofComponent W).1) (V : Set Z) := by
      simpa [hV, hVclosed] using himg
    exact himg'.eq (genericPoints.isGenericPoint_ofComponent V)
  let TV : IrreducibleCloseds Z :=
    ⟨(V : Set Z), V.2.1, isClosed_of_mem_irreducibleComponents (V : Set Z) V.2⟩
  let TW : IrreducibleCloseds Y :=
    ⟨(W : Set Y), W.2.1, isClosed_of_mem_irreducibleComponents (W : Set Y) W.2⟩
  have hdimV := deltaDimension_eq_of_isGenericPoint C (j ≫ p) TV
    (genericPoints.ofComponent V).1 (genericPoints.isGenericPoint_ofComponent V)
  have hdimW := deltaDimension_eq_of_isGenericPoint C (i ≫ p) TW
    (genericPoints.ofComponent W).1 (genericPoints.isGenericPoint_ofComponent W)
  change (deltaDimension C (j ≫ p) TV : EInt) = (deltaDimension C (i ≫ p) TW : EInt)
  rw [hdimV, hdimW]
  apply congrArg (fun n : ℤ => (n : EInt))
  rw [relativeDimension_comp_closedImmersion C.dimensionFunction j p
      (genericPoints.ofComponent V).1,
    relativeDimension_comp_closedImmersion C.dimensionFunction i p
      (genericPoints.ofComponent W).1]
  rw [← hgen, ← he]


/-! ### The dimension bounds of Stacks 02RE -/

add_to_stacks 02RE "part (2): pullback coherence" AlgebraicGeometry.isCoherent_pullback

/-- **Stacks 02RE, part (1), dimension bound.** The scheme-theoretic inverse image of a closed
subscheme of delta-dimension at most `k` under a flat morphism of relative dimension `r` has
delta-dimension at most `k + r`. -/
@[stacks 02RE "part (1): dimension bound"]
theorem schemeDeltaDimension_pullback_le
    (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
    (hbase : f ≫ sY = sX) (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
    (i : Z ⟶ Y) [IsClosedImmersion i] (k : ℤ)
    (hZ : schemeDeltaDimension C (i ≫ sY) ≤ (k : EInt)) :
    schemeDeltaDimension C (pullback.fst f i ≫ sX) ≤ ((k + (r : ℤ) : ℤ) : EInt) := by
  classical
  let P := pullback f i
  let p : P ⟶ Z := pullback.snd f i
  let q : Z ⟶ C.S := i ≫ sY
  let _ : Flat p :=
    (Flat.isStableUnderBaseChange).of_isPullback (IsPullback.of_hasPullback f i) inferInstance
  let _ : LocallyOfFiniteType p := by infer_instance
  have hrelp : AlgebraicGeometry.RelativeDimension p r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback (IsPullback.of_hasPullback f i) hf
  have hmap : p ≫ q = pullback.fst f i ≫ sX := by
    dsimp [p, q]
    calc
      _ = (pullback.snd f i ≫ i) ≫ sY := by simp [Category.assoc]
      _ = (pullback.fst f i ≫ f) ≫ sY := by rw [pullback.condition]
      _ = pullback.fst f i ≫ sX := by rw [Category.assoc, hbase]
  let α : irreducibleComponents P → EInt := fun W =>
    (deltaDimension C (p ≫ q)
      ⟨(W : Set P), W.2.1, isClosed_of_mem_irreducibleComponents (W : Set P) W.2⟩ : EInt)
  let β : irreducibleComponents Z → EInt := fun V =>
    (deltaDimension C q
      ⟨(V : Set Z), V.2.1, isClosed_of_mem_irreducibleComponents (V : Set Z) V.2⟩ : EInt)
  have hbound (V : irreducibleComponents Z) : β V ≤ (k : EInt) := by
    have hz := hZ
    rw [schemeDeltaDimension_eq_iSup] at hz
    exact le_trans (le_iSup (fun V : irreducibleComponents Z =>
      (deltaDimension C q
        ⟨(V : Set Z), V.2.1,
          isClosed_of_mem_irreducibleComponents (V : Set Z) V.2⟩ : EInt)) V) hz
  have hdimMap :
      schemeDeltaDimension C (pullback.fst f i ≫ sX) = schemeDeltaDimension C (p ≫ q) := by
    rw [schemeDeltaDimension_eq_iSup, schemeDeltaDimension_eq_iSup]
    refine iSup_congr fun W => ?_
    apply congrArg (fun n : ℤ => (n : EInt))
    unfold deltaDimension
    rw [← hmap]
  have hpullbackBound : schemeDeltaDimension C (p ≫ q) ≤ ((k + (r : ℤ) : ℤ) : EInt) := by
    rw [schemeDeltaDimension_eq_iSup]
    change (⨆ W : irreducibleComponents P, α W) ≤ ((k + (r : ℤ) : ℤ) : EInt)
    refine iSup_le fun W => ?_
    obtain ⟨V, hη⟩ := component_genericPoint_maps_to_component_genericPoint p W
    have hdim := deltaDimension_component_eq_of_genericPoint_map C p q r hrelp W V hη
    have hdimE : α W = β V + (r : EInt) := by
      simpa [α, β, Category.assoc, coe_add_coe_eq_coe_add, eint_natCast_eq_intCast] using
        congrArg (fun n : ℤ => (n : EInt)) hdim
    rw [hdimE]
    simpa only [coe_add_coe_eq_coe_add, eint_natCast_eq_intCast] using
      add_le_add_left (hbound V) (r : EInt)
  exact hdimMap.trans_le hpullbackBound

/-- **Stacks 02RE, part (2), dimension bound.** If a coherent sheaf on `Y` has support of
delta-dimension at most `k`, then the support of its pullback along a flat morphism of relative
dimension `r` has delta-dimension at most `k + r`. -/
@[stacks 02RE "part (2): support dimension bound"]
theorem schemeDeltaDimension_support_pullback_le
    (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
    (hbase : f ≫ sY = sX) (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
    (F : Y.Modules) [hF : F.IsCoherent] (k : ℤ)
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ sY) ≤ (k : EInt)) :
    schemeDeltaDimension C
        ((@reducedSupport X ((Scheme.Modules.pullback f).obj F)
          (@AlgebraicGeometry.isCoherent_pullback X Y
            (LocallyOfFiniteType.isLocallyNoetherian sX) f F hF)).subschemeι ≫ sX) ≤
      ((k + (r : ℤ) : ℤ) : EInt) := by
  let I := reducedSupport F
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let _ : ((Scheme.Modules.pullback f).obj F).IsCoherent :=
    AlgebraicGeometry.isCoherent_pullback f F
  let F' := (Scheme.Modules.pullback f).obj F
  let J := reducedSupport F'
  let _ : F.IsFiniteType := isFiniteType_of_isCoherent F
  have hIrange : Set.range I.subschemeι = (SheafOfModules.supp F : Set Y) := by
    rw [I.range_subschemeι]
    simp [I, reducedSupport, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hJrange : Set.range J.subschemeι = (SheafOfModules.supp F' : Set X) := by
    rw [J.range_subschemeι]
    simp [J, F', reducedSupport, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hpull : SheafOfModules.supp F' = f ⁻¹' SheafOfModules.supp F :=
    Stacks.Modules.supp_pullback f F
  have hrange : Set.range J.subschemeι = Set.range (pullback.fst f I.subschemeι) := by
    rw [hJrange, hpull, ← hIrange, Scheme.Pullback.range_fst]
  have hdim := schemeDeltaDimension_pullback_le C sX sY f hbase r hf I.subschemeι k
    (by simpa [I] using hFk)
  have hdimEq := schemeDeltaDimension_eq_of_equal_ranges C sX
    J.subschemeι (pullback.fst f I.subschemeι) hrange
  rw [show (@reducedSupport X ((Scheme.Modules.pullback f).obj F)
      (@AlgebraicGeometry.isCoherent_pullback X Y
        (LocallyOfFiniteType.isLocallyNoetherian sX) f F hF)) = J from rfl, hdimEq]
  exact hdim

end Stacks.Chow

end
