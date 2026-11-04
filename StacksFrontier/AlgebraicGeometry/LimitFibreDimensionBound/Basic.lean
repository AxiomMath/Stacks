module

public import StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.ProperFibreDimensionNeighbourhood.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute

/-!
# Fibre dimension in an inverse limit of schemes: the limit-theoretic skeleton

Stacks Tag 05M5 says that for a cofiltered inverse system of morphisms `f i : X i ⟶ S i` with
affine transitions downstairs, quasi-compact and quasi-separated bases, finite-type component
morphisms and source transitions that are closed immersions into the base change, a bound `d` on
the dimensions of the fibres of the limit morphism already holds at some finite stage.

This file proves everything in that statement which is limit theory, and states the two
remaining inputs as hypotheses. Nothing here needs the bases to be quasi-separated.

## Main results

* `topologicalKrullDimAt_le_of_isInducing`: the local Krull dimension of a subspace at a point is
  at most that of the ambient space at its image. Purely topological, and the half of
  `Topology.IsOpenEmbedding.topologicalKrullDimAt_eq` that survives without openness.
* `fiberDimensionAt_le_of_isClosedImmersion`: for a closed immersion `h` over a base, the local
  dimension of the fibre of `h ≫ q` at `z` is at most that of the fibre of `q` at `h z`.
* `isAffineHom_map` and `compactSpace_obj`: the source transitions of a Tag 05M5 system are
  affine, and each `X i` is quasi-compact. These are what let the affine-transition limit
  machinery be applied upstairs as well as downstairs.
* `boundedFibreDimension`: the open subset of `X i` where the local fibre dimension is at most
  `d`, from Tag 02FZ.
* `map_preimage_boundedFibreDimension_le`: that family of opens is monotone along the
  transitions — **given** `FibreDimensionBaseChangeLE`.
* `topologicalKrullDimAt_limit_le`: the hypothesis of Tag 05M5 bounds the local fibre dimension
  at every point of the limit. This is what feeds `AttainedAtSomeStage` its hypothesis.
* `exists_forall_topologicalKrullDim_fiber_le_of_isLimit`: Tag 05M5's conclusion, from the
  tag's own dimension hypothesis together with `FibreDimensionBaseChangeLE`,
  `AttainedAtSomeStage`, and smallness of the index category.

## Implementation notes

**The two inputs, stated as hypotheses.**

* `FibreDimensionBaseChangeLE` is the inequality half of Stacks Tag 02FY (1): the local
  dimension of a fibre is unchanged by base change. Its ring-level input is Stacks Tag 00QI
  (`Algebra.IsPushout.relativeDimensionAt_comap_eq`), and the chart dictionary transporting it
  to schemes is `Stacks.Tag01V9NumericalCriterion.fiberDimensionAt_eq_relativeDimensionAt` and
  `AlgebraicGeometry.fiberDimensionAt_eq_of_open_square`.
* `AttainedAtSomeStage` is the mathematical heart of Tag 05M5: a point of the limit whose local
  fibre dimension is at most `d` already has local fibre dimension at most `d` at some stage.
  The source proves it by contradiction, forming the reduced closed subschemes where the bound
  fails and applying Tag 01Z2 to that system.

  **Its body includes that dimension hypothesis**; without it the predicate is false. `hdim` is
  a hypothesis of the theorem below, which is what `topologicalKrullDimAt_limit_le` exists to
  connect; the refutation of the predicate without the hypothesis is
  `Stacks.AlgebraicGeometry.Refute05M5Heart.not_attained_of_forall_exists`.

**Why the index category carries smallness hypotheses here and not in the source.** The
descent step is `AlgebraicGeometry.exists_map_eq_top`, which Mathlib states only for
`I : Type u` with `[Category.{u} I]`, the scheme universe. The free-universe form,
`AlgebraicGeometry.exists_map_eq_top_of_initiallySmall`, buys the independence of the index
universes at the price of `CategoryTheory.LocallySmall.{u} I` and
`CategoryTheory.InitiallySmall.{u} I`, and those cannot be dropped by that route: see the
implementation notes of `StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit`
and the `Ordinal.{u}` witness in `StacksFrontier.AlgebraicGeometry.LimitConeSmallness.Basic`. Both
hold by instance search whenever the index category is the opposite of a `u`-small preorder,
which is the situation the source's "directed set" describes.

## References

* [Stacks Project, Tag 05M5](https://stacks.math.columbia.edu/tag/05M5)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 02FZ](https://stacks.math.columbia.edu/tag/02FZ)
* [Stacks Project, Tag 01Z2](https://stacks.math.columbia.edu/tag/01Z2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe v w u

namespace Stacks.AlgebraicGeometry.LimitFibreDimensionBound

/-! ### Local Krull dimension along an inducing map -/

/-- The local Krull dimension of a subspace at a point is at most the local Krull dimension of
the ambient space at its image. Each open neighbourhood `V` of `e a` pulls back to an open
neighbourhood of `a` whose dimension is at most that of `V`, because `e` restricts to an
inducing map of the preimage into `V`. -/
public theorem topologicalKrullDimAt_le_of_isInducing {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {e : A → B} (he : Topology.IsInducing e) (a : A) :
    topologicalKrullDimAt A a ≤ topologicalKrullDimAt B (e a) := by
  refine le_iInf fun V ↦ ?_
  refine iInf_le_of_le ⟨e ⁻¹' V.1, V.2.1, V.2.2.preimage he.continuous⟩ ?_
  exact (he.restrictPreimage V.1).topologicalKrullDim_le

/-! ### Fibre dimension along a closed immersion over a base -/

section ClosedImmersion

variable {P Q T : Scheme.{u}}

/-- For a closed immersion `h : P ⟶ Q` and a morphism `q : Q ⟶ T`, the local dimension of the
fibre of `h ≫ q` at a point `z` is at most the local dimension of the fibre of `q` at `h z`;
here `p` is any morphism equal to `h ≫ q`. -/
public theorem fiberDimensionAt_le_of_isClosedImmersion (h : P ⟶ Q) (q : Q ⟶ T)
    [IsClosedImmersion h] (p : P ⟶ T) (hcomp : h ≫ q = p) (z : P) :
    topologicalKrullDimAt (p.fiber (p z)) (p.asFiber z) ≤
      topologicalKrullDimAt (q.fiber (q (h z))) (q.asFiber (h z)) := by
  subst hcomp
  have hset : (h ≫ q) ⁻¹' {(h ≫ q) z} = h ⁻¹' (q ⁻¹' {q (h z)}) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.comp_apply]
  have hz : z ∈ h ⁻¹' (q ⁻¹' {q (h z)}) := rfl
  calc topologicalKrullDimAt ((h ≫ q).fiber ((h ≫ q) z)) ((h ≫ q).asFiber z)
      = topologicalKrullDimAt ↥((h ≫ q) ⁻¹' {(h ≫ q) z}) ⟨z, rfl⟩ := by
        refine (topologicalKrullDimAt_eq_of_homeomorph
          ((h ≫ q).fiberHomeo ((h ≫ q) z)) ((h ≫ q).asFiber z)).trans ?_
        congr 1
        exact Subtype.ext ((h ≫ q).fiberι_asFiber z)
    _ = topologicalKrullDimAt ↥(h ⁻¹' (q ⁻¹' {q (h z)})) ⟨z, hz⟩ := by
        refine (topologicalKrullDimAt_eq_of_homeomorph (Homeomorph.setCongr hset)
          ⟨z, rfl⟩).trans ?_
        congr 1
    _ ≤ topologicalKrullDimAt ↥(q ⁻¹' {q (h z)}) ⟨h z, rfl⟩ := by
        refine le_trans (topologicalKrullDimAt_le_of_isInducing
          (h.isClosedEmbedding.isInducing.restrictPreimage (q ⁻¹' {q (h z)})) ⟨z, hz⟩)
          (le_of_eq ?_)
        congr 1
    _ = topologicalKrullDimAt (q.fiber (q (h z))) (q.asFiber (h z)) := by
        refine Eq.symm ?_
        refine (topologicalKrullDimAt_eq_of_homeomorph (q.fiberHomeo (q (h z)))
          (q.asFiber (h z))).trans ?_
        congr 1
        exact Subtype.ext (q.fiberι_asFiber (h z))

end ClosedImmersion

/-! ### The Tag 05M5 system -/

variable {I : Type v} [Category.{w} I] (X S : I ⥤ Scheme.{u}) (f : X ⟶ S)

/-- The comparison morphism `X i ⟶ (X j) ×_{S j} (S i)` of Tag 05M5's hypothesis (4), for a
transition `g : i ⟶ j` of the index category. -/
public noncomputable def baseChangeLift {i j : I} (g : i ⟶ j) :
    X.obj i ⟶ pullback (f.app j) (S.map g) :=
  pullback.lift (X.map g) (f.app i) (f.naturality g)

/-- The comparison morphism `baseChangeLift` followed by the first projection is the transition
`X.map g`. -/
public theorem baseChangeLift_fst {i j : I} (g : i ⟶ j) :
    baseChangeLift X S f g ≫ pullback.fst (f.app j) (S.map g) = X.map g :=
  pullback.lift_fst _ _ _

/-- The comparison morphism `baseChangeLift` followed by the second projection is `f.app i`. -/
public theorem baseChangeLift_snd {i j : I} (g : i ⟶ j) :
    baseChangeLift X S f g ≫ pullback.snd (f.app j) (S.map g) = f.app i :=
  pullback.lift_snd _ _ _

/-- The source transitions of a Tag 05M5 system are affine: `X i ⟶ X j` factors as the closed
immersion of hypothesis (4) followed by the base change of the affine morphism `S i ⟶ S j`. -/
public theorem isAffineHom_map
    (hS : ∀ {i j : I} (g : i ⟶ j), IsAffineHom (S.map g))
    (hcl : ∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (baseChangeLift X S f g))
    {i j : I} (g : i ⟶ j) : IsAffineHom (X.map g) := by
  have h₁ := hcl g
  have h₂ := hS g
  have hfst : IsAffineHom (pullback.fst (f.app j) (S.map g)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback (f.app j) (S.map g)).flip h₂
  have he : X.map g = baseChangeLift X S f g ≫ pullback.fst (f.app j) (S.map g) :=
    (baseChangeLift_fst X S f g).symm
  rw [he]
  infer_instance

/-- Each `X i` of a Tag 05M5 system is quasi-compact, since `f i` is quasi-compact and `S i` is.
-/
public theorem compactSpace_obj (hqc : ∀ i : I, QuasiCompact (f.app i))
    (hcs : ∀ i : I, CompactSpace (S.obj i)) (i : I) : CompactSpace (X.obj i) := by
  have := hqc i
  have := hcs i
  exact QuasiCompact.compactSpace_of_compactSpace (f.app i)

/-! ### The bounded fibre-dimension locus -/

/-- **Stacks Tag 02FZ at a stage.** The open subset of `X i` on which the local dimension of the
fibre of `f i` is at most `d`. -/
public noncomputable def boundedFibreDimension [∀ i : I, LocallyOfFiniteType (f.app i)] (d : ℕ)
    (i : I) : (X.obj i).Opens :=
  ⟨{x : X.obj i |
      topologicalKrullDimAt ((f.app i).fiber ((f.app i) x)) ((f.app i).asFiber x) ≤
        (d : WithBot ℕ∞)},
    isOpen_setOf_fiberDimensionAt_le (f.app i) d⟩

/-- A point of `X i` lies in `boundedFibreDimension X S f d i` if and only if the local dimension
of the fibre of `f i` at it is at most `d`. -/
public theorem mem_boundedFibreDimension_iff [∀ i : I, LocallyOfFiniteType (f.app i)] (d : ℕ)
    (i : I) (x : X.obj i) :
    x ∈ boundedFibreDimension X S f d i ↔
      topologicalKrullDimAt ((f.app i).fiber ((f.app i) x)) ((f.app i).asFiber x) ≤
        (d : WithBot ℕ∞) :=
  Iff.rfl

/-! ### The two remaining inputs -/

/-- **The inequality half of Stacks Tag 02FY (1)**: in a fibre square, the local dimension of the
fibre of the base-changed morphism is at most the local dimension of the fibre of the original
morphism at the image point. -/
public def FibreDimensionBaseChangeLE : Prop :=
  ∀ {Y T T' : Scheme.{u}} (p : Y ⟶ T) (r : T' ⟶ T) [LocallyOfFiniteType p]
    (w : ↥(pullback p r)),
    topologicalKrullDimAt ((pullback.snd p r).fiber ((pullback.snd p r) w))
        ((pullback.snd p r).asFiber w) ≤
      topologicalKrullDimAt (p.fiber (p (pullback.fst p r w))) (p.asFiber (pullback.fst p r w))

/-- **The mathematical heart of Stacks Tag 05M5**: a point of the limit at which the local fibre
dimension is at most `d` already has local fibre dimension at most `d` at some stage.

`F` is the morphism out of the cone point whose fibres the hypothesis is about — for Tag 05M5
the morphism `hcS.lift ((Cone.postcompose f).obj cX)` between the limits. It is a parameter
rather than being built from a limit cone on `S` because `CategoryTheory.Limits.IsLimit` is
data, so a predicate mentioning it would not be determined by `X`, `S`, `f`, `cX` and `d`.

The source proves this by contradiction, forming the reduced closed subscheme of each `X i`
where the bound fails and applying Tag 01Z2 to the resulting system.

**The dimension hypothesis on `z` is not decoration.** Without it the predicate asserts that
*every* point of the cone point has local fibre dimension at most `d` at some stage, which is
false: see
`Stacks.AlgebraicGeometry.Refute05M5Heart.not_attained_of_forall_exists`, which refutes the
predicate without it for the one-object system `𝔸¹_ℚ ⟶ Spec ℚ` at `d = 0` — a system satisfying
every hypothesis Tag 05M5 states. -/
public def AttainedAtSomeStage [∀ i : I, LocallyOfFiniteType (f.app i)] {T : Scheme.{u}}
    (cX : Cone X) (F : cX.pt ⟶ T) (d : ℕ) : Prop :=
  ∀ z : ↥cX.pt,
    topologicalKrullDimAt (F.fiber (F z)) (F.asFiber z) ≤ (d : WithBot ℕ∞) →
      ∃ i : I, cX.π.app i z ∈ boundedFibreDimension X S f d i

/-! ### Monotonicity of the locus along the transitions -/

/-- The bounded fibre-dimension loci are monotone along the transitions of a Tag 05M5 system:
the preimage in `X i` of the locus in `X j` is contained in the locus in `X i`. The fibre of
`f i` sits as a closed subscheme of the base change of the fibre of `f j`, which has the same
local dimension by Tag 02FY (1). -/
public theorem map_preimage_boundedFibreDimension_le
    [∀ i : I, LocallyOfFiniteType (f.app i)]
    (hcl : ∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (baseChangeLift X S f g))
    (hbc : FibreDimensionBaseChangeLE.{u}) (d : ℕ) {i j : I} (g : i ⟶ j) :
    X.map g ⁻¹ᵁ boundedFibreDimension X S f d j ≤ boundedFibreDimension X S f d i := by
  intro x hx
  have hxj : topologicalKrullDimAt ((f.app j).fiber ((f.app j) (X.map g x)))
      ((f.app j).asFiber (X.map g x)) ≤ (d : WithBot ℕ∞) := hx
  rw [mem_boundedFibreDimension_iff]
  have hcli := hcl g
  have hstep₁ := fiberDimensionAt_le_of_isClosedImmersion (baseChangeLift X S f g)
    (pullback.snd (f.app j) (S.map g)) (f.app i) (baseChangeLift_snd X S f g) x
  have hstep₂ := hbc (f.app j) (S.map g) (baseChangeLift X S f g x)
  have hfst : pullback.fst (f.app j) (S.map g) (baseChangeLift X S f g x) = X.map g x := by
    have h := congrArg (fun k : X.obj i ⟶ X.obj j ↦ k x) (baseChangeLift_fst X S f g)
    simpa only [Scheme.Hom.comp_apply] using h
  rw [hfst] at hstep₂
  exact le_trans hstep₁ (le_trans hstep₂ hxj)

/-! ### The hypothesis of Tag 05M5 at a point of the limit -/

/-- Tag 05M5's hypothesis — every fibre of the limit morphism has dimension at most `d` — bounds
the *local* fibre dimension at every point of the limit. -/
public theorem topologicalKrullDimAt_limit_le {L T : Scheme.{u}} (F : L ⟶ T) (d : ℕ)
    (hdim : ∀ t : ↥T, topologicalKrullDim (F.fiber t) ≤ (d : WithBot ℕ∞)) (z : ↥L) :
    topologicalKrullDimAt (F.fiber (F z)) (F.asFiber z) ≤ (d : WithBot ℕ∞) :=
  ProperFibreDimension.topologicalKrullDimAt_asFiber_le F rfl d (hdim (F z))

/-! ### Tag 05M5, modulo the two inputs -/

/-- **Stacks Tag 05M5, with its two missing inputs as hypotheses and with the index category
assumed `u`-small in the two senses the free-universe limit machinery needs.**

Given `FibreDimensionBaseChangeLE` (Tag 02FY (1)) and `AttainedAtSomeStage`, the tag's own
hypothesis `hdim` — a bound `d` on the dimensions of the fibres of a morphism `F` out of the
cone point — descends to a stage at which *every* fibre has dimension at most `d`. `hdim`
reaches `AttainedAtSomeStage`'s hypothesis through `topologicalKrullDimAt_limit_le`.

The proof is the descent half of the source's argument, run forwards: the loci
`boundedFibreDimension` are open by Tag 02FZ and monotone along the transitions, their preimages
in the limit cover the quasi-compact space `cX.pt`, cofilteredness picks one stage `k` whose
preimage is everything, `exists_map_eq_top_of_initiallySmall` descends that to a transition
`m ⟶ k`, and monotonicity turns it into `boundedFibreDimension m = ⊤`. -/
public theorem exists_forall_topologicalKrullDim_fiber_le_of_isLimit
    [IsCofiltered I] [CategoryTheory.LocallySmall.{u} I] [CategoryTheory.InitiallySmall.{u} I]
    [∀ i : I, LocallyOfFiniteType (f.app i)]
    (hS : ∀ {i j : I} (g : i ⟶ j), IsAffineHom (S.map g))
    (hcl : ∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (baseChangeLift X S f g))
    (hqc : ∀ i : I, QuasiCompact (f.app i)) (hcs : ∀ i : I, CompactSpace (S.obj i))
    (hbc : FibreDimensionBaseChangeLE.{u})
    (cX : Cone X) (hcX : IsLimit cX) {T : Scheme.{u}} (F : cX.pt ⟶ T) (d : ℕ)
    (hdim : ∀ t : ↥T, topologicalKrullDim (F.fiber t) ≤ (d : WithBot ℕ∞))
    (hattained : AttainedAtSomeStage X S f cX F d) :
    ∃ i : I, ∀ s : ↥(S.obj i),
      topologicalKrullDim ((f.app i).fiber s) ≤ (d : WithBot ℕ∞) := by
  classical
  have haff : ∀ {i j : I} (g : i ⟶ j), IsAffineHom (X.map g) := fun g ↦
    isAffineHom_map X S f hS hcl g
  have hcpt : ∀ i : I, CompactSpace (X.obj i) := fun i ↦ compactSpace_obj X S f hqc hcs i
  have hmono : ∀ {i j : I} (g : i ⟶ j),
      X.map g ⁻¹ᵁ boundedFibreDimension X S f d j ≤ boundedFibreDimension X S f d i :=
    fun g ↦ map_preimage_boundedFibreDimension_le X S f hcl hbc d g
  have hlimcpt : CompactSpace ↥cX.pt :=
    Scheme.compactSpace_of_isLimit_of_initiallySmall X cX hcX
  -- The preimages of the loci cover the limit.
  have hopen : ∀ i : I,
      IsOpen ((cX.π.app i ⁻¹ᵁ boundedFibreDimension X S f d i : (cX.pt).Opens) :
        Set ↥cX.pt) :=
    fun i ↦ (cX.π.app i ⁻¹ᵁ boundedFibreDimension X S f d i).2
  have hcover : (Set.univ : Set ↥cX.pt) ⊆
      ⋃ i : I, ((cX.π.app i ⁻¹ᵁ boundedFibreDimension X S f d i : (cX.pt).Opens) :
        Set ↥cX.pt) := by
    intro z _
    obtain ⟨i, hi⟩ := hattained z (topologicalKrullDimAt_limit_le F d hdim z)
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen hcover
  -- Cofilteredness gives one stage below every member of the finite subcover.
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (C := I) t
  have hktop : cX.π.app k ⁻¹ᵁ boundedFibreDimension X S f d k = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨i, hit, hzi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ z))
    obtain ⟨g⟩ := hk hit
    have hw : cX.π.app k ≫ X.map g = cX.π.app i := cX.w g
    have hle : cX.π.app i ⁻¹ᵁ boundedFibreDimension X S f d i ≤
        cX.π.app k ⁻¹ᵁ boundedFibreDimension X S f d k := by
      rw [← hw, Scheme.Hom.comp_preimage]
      exact Scheme.Hom.preimage_mono _ (hmono g)
    exact hle hzi
  -- Descend the stage.
  obtain ⟨m, gmk, hm⟩ := exists_map_eq_top_of_initiallySmall X cX hcX
    (boundedFibreDimension X S f d k) hktop
  refine ⟨m, fun s ↦ ?_⟩
  refine ProperFibreDimension.topologicalKrullDim_fiber_le_of_forall (f.app m) s d
    fun x _ ↦ ?_
  have hx : x ∈ X.map gmk ⁻¹ᵁ boundedFibreDimension X S f d k := by
    rw [hm]; trivial
  exact hmono gmk hx

end Stacks.AlgebraicGeometry.LimitFibreDimensionBound

end
