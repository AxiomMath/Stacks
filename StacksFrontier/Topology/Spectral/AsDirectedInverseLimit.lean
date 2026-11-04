module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Category.Profinite.Product
public import StacksFrontier.Topology.Spectral.SierpinskiEmbedding
public import StacksFrontier.Topology.Spectral.InverseLimits

/-!
# Spectral spaces as directed inverse limits of finite sober spaces

A topological space is spectral if and only if it is a directed inverse limit of finite sober
topological spaces. A constructibly closed embedding into a product of Sierpinski spaces
expresses a spectral space as the limit of its finite coordinate images. Conversely,
finite sober spaces and their continuous maps are spectral, so their cofiltered limits
are spectral.

## Main definitions

* `IsDirectedInverseLimitOfFiniteSober`: `X` is homeomorphic to the limit in `TopCat` of a functor
  out of a small cofiltered category all of whose values are finite and sober.

## Main results

* `IsDirectedInverseLimitOfFiniteSober.of_homeomorph`: being a directed inverse limit of finite
  sober spaces transports along a homeomorphism.
* `SpectralSpace.of_homeomorph`: being a spectral space transports along a homeomorphism.
* `spectralSpace_iff_isDirectedInverseLimitOfFiniteSober`: the characterization of spectral
  spaces as directed inverse limits of finite sober spaces.
* `spectral_iff_directed_inverse_limit_finite_sober_homeomorph_invariant`: the biconditional holds
  for `X` exactly when it holds for a space homeomorphic to `X`.

## Implementation notes

The index category of the presentation of a spectral space `X` is `(Finset I)ᵒᵖ`, where the
index type `I` produced by `exists_isClosed_withConstructibleTopology_of_spectralSpace` is the
type of quasi-compact opens of `X`. It lives in the universe of `X`, so
`IsDirectedInverseLimitOfFiniteSober` is stated in a single universe.

## References

* [Stacks Project, Tag 09XX](https://stacks.math.columbia.edu/tag/09XX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

/-- A topological space `X` is a *directed inverse limit of finite sober
topological spaces* if there exist a small cofiltered category `J` and a
functor `F : J ⥤ TopCat.{u}` such that each `F.obj j` is finite and sober
(i.e. both `QuasiSober` and `T0Space`), together with a homeomorphism between
`X` and the limit of `F` in `TopCat`. -/
def IsDirectedInverseLimitOfFiniteSober (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J) (F : J ⥤ TopCat.{u}),
    (∀ j, Finite (F.obj j)) ∧
    (∀ j, QuasiSober (F.obj j)) ∧
    (∀ j, T0Space (F.obj j)) ∧
    Nonempty (X ≃ₜ (TopCat.limitCone F).pt)

/-- If `X ≃ₜ Y` and `Y` is a directed inverse limit of finite sober topological spaces, then so
is `X`. -/
lemma IsDirectedInverseLimitOfFiniteSober.of_homeomorph
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (hY : IsDirectedInverseLimitOfFiniteSober Y) :
    IsDirectedInverseLimitOfFiniteSober X := by
  obtain ⟨J, instJ, instCof, F, hfin, hqs, ht0, ⟨φ⟩⟩ := hY
  exact ⟨J, instJ, instCof, F, hfin, hqs, ht0, ⟨e.trans φ⟩⟩

/-- A topological space homeomorphic to a spectral space is spectral. -/
lemma SpectralSpace.of_homeomorph
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) [SpectralSpace Y] : SpectralSpace X := by
  have : T0Space X := e.isEmbedding.t0Space
  have : CompactSpace X := Homeomorph.compactSpace e.symm
  have : QuasiSober X := IsClosedEmbedding.quasiSober e.isClosedEmbedding
  have : QuasiSeparatedSpace X := (quasiSeparatedSpace_congr e.symm).mp inferInstance
  have : PrespectralSpace X := IsOpenEmbedding.prespectralSpace e.isOpenEmbedding
  exact ⟨⟩

/-- The biconditional "`X` is spectral iff `X` is a directed inverse limit of finite sober
topological spaces" is invariant under homeomorphism: for `e : X ≃ₜ Y` it holds for `X` exactly
when it holds for `Y`. -/
theorem spectral_iff_directed_inverse_limit_finite_sober_homeomorph_invariant
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    (SpectralSpace X ↔ IsDirectedInverseLimitOfFiniteSober X) ↔
      (SpectralSpace Y ↔ IsDirectedInverseLimitOfFiniteSober Y) :=
  iff_congr
    ⟨fun h => @SpectralSpace.of_homeomorph Y X _ _ e.symm h,
      fun h => @SpectralSpace.of_homeomorph X Y _ _ e h⟩
    ⟨IsDirectedInverseLimitOfFiniteSober.of_homeomorph e.symm,
      IsDirectedInverseLimitOfFiniteSober.of_homeomorph e⟩

/-- Finite coordinate images of a constructibly closed Sierpinski subspace form a
cofiltered presentation of that subspace. -/
private theorem isDirectedInverseLimitOfFiniteSober_of_isClosed
    {I : Type u} (S : Set (SierpinskiProduct I))
    (hS : IsClosed[constructibleTopology (SierpinskiProduct I)] S) :
    IsDirectedInverseLimitOfFiniteSober S := by
  classical
  let F : (Finset I)ᵒᵖ ⥤ TopCat.{u} :=
    { obj J := TopCat.of (Profinite.IndexFunctor.obj S (· ∈ J.unop))
      map f := TopCat.ofHom (Profinite.IndexFunctor.map S (leOfHom f.unop)) }
  let p (J : Finset I) := Profinite.IndexFunctor.π_app S (· ∈ J)
  let L := (TopCat.limitCone F).pt
  let g (a : L) : SierpinskiProduct I := fun i =>
    (a.1 (Opposite.op {i})).1 ⟨i, Finset.mem_singleton_self i⟩
  have hg (a : L) (J : Finset I) :
      (fun i : J => g a i) = (a.1 (Opposite.op J)).1 := by
    funext i
    have h := a.2 (homOfLE (Finset.singleton_subset_iff.mpr i.2)).op
    exact (congrArg (fun z => z.1 ⟨i.1, Finset.mem_singleton_self i.1⟩) h).symm
  have hgS (a : L) : g a ∈ S := by
    rw [constructibleTopology_sierpinskiProduct] at hS
    apply @closure_minimal _ (piDiscreteTopology I) S S Set.Subset.rfl hS
    rw [@mem_closure_iff _ (piDiscreteTopology I)]
    intro U hU haU
    obtain ⟨J, v, hv, hJv⟩ :=
      (@isOpen_pi_iff I (fun _ => Prop) (fun _ => ⊥) U).mp hU (g a) haU
    obtain ⟨x, hxS, hx⟩ := (a.1 (Opposite.op J)).2
    refine ⟨x, hJv fun i hi => ?_, hxS⟩
    have hxi : x i = g a i := congrFun (hx.trans (hg a J).symm) ⟨i, hi⟩
    exact hxi ▸ (hv i hi).2
  let e : S ≃ₜ L :=
    { toFun x := ⟨fun J => p J.unop x, fun _ => rfl⟩
      invFun a := ⟨g a, hgS a⟩
      left_inv _ := rfl
      right_inv a := Subtype.ext <| funext fun J => Subtype.ext (hg a J.unop)
      continuous_toFun :=
        (continuous_pi fun J => (p J.unop).continuous).subtype_mk _
      continuous_invFun := Continuous.subtype_mk (continuous_pi fun i =>
        (continuous_apply (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset I))).comp
          (continuous_subtype_val.comp
            ((TopCat.limitCone F).π.app (Opposite.op {i})).hom.continuous)) _ }
  refine ⟨(Finset I)ᵒᵖ, inferInstance, inferInstance, F,
    fun J => inferInstanceAs (Finite (Profinite.IndexFunctor.obj S (· ∈ J.unop))),
    fun J => Topology.quasiSober_of_finite _,
    fun J => inferInstanceAs (T0Space (Profinite.IndexFunctor.obj S (· ∈ J.unop))), ⟨e⟩⟩

/-- A topological space is spectral if and only if it is a directed inverse limit of finite
sober topological spaces. -/
@[stacks 09XX]
theorem spectralSpace_iff_isDirectedInverseLimitOfFiniteSober
    (X : Type u) [TopologicalSpace X] :
    SpectralSpace X ↔ IsDirectedInverseLimitOfFiniteSober X := by
  constructor
  · intro hX
    obtain ⟨I, S, hS, ⟨e⟩⟩ := exists_isClosed_withConstructibleTopology_of_spectralSpace X
    exact IsDirectedInverseLimitOfFiniteSober.of_homeomorph e
      (isDirectedInverseLimitOfFiniteSober_of_isClosed S hS)
  · rintro ⟨J, instJ, instCof, F, hfin, hqs, ht0, ⟨e⟩⟩
    let := hfin
    let := hqs
    let := ht0
    let D : SpectralDiagram.{u, u} J :=
      { F := F
        isSpectralSpace := fun _ => ⟨⟩
        isSpectralMap := fun f =>
          ⟨(F.map f).hom.continuous, fun _ _ _ => (Set.toFinite _).isCompact⟩ }
    exact @SpectralSpace.of_homeomorph X _ _ _
      (e.trans (TopCat.homeoOfIso
        ((TopCat.limitConeIsLimit F).conePointUniqueUpToIso (limit.isLimit F))))
      (spectralDiagram_invLimit_spectralSpace D)

end
