module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.Rank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Defs
public import StacksFrontier.AlgebraicGeometry.SyntomicBaseChange.Basic

/-!
# The universal finite syntomic locus

The universal finite free family `pi_d : Y_d ⟶ X_d` of rank `d` (Tag 0FKZ) has an open locus in
its base `X_d` over which it is syntomic, and a morphism `g : T ⟶ X_d` factors through that open
subscheme exactly when the base change of the family along `g` is syntomic. This is Tag 0FL0.

## Main definitions

* `AlgebraicGeometry.universalSyntomicOpen` is the open subscheme of `X_d` in question.

## Main results

* `AlgebraicGeometry.isOpen_setOf_syntomicAt`: the locus where a morphism is syntomic is open.
* `AlgebraicGeometry.factorsThrough_universalSyntomicOpen_iff`: the universal property.

## Implementation notes

The locus is defined as the interior of the set of points of `X_d` over which every point of the
fibre is syntomic; the universal property shows a posteriori that no interior needs to be taken,
because the family is finite and hence closed, so that set is already open — this is
`AlgebraicGeometry.universalSyntomicOpen_coe_eq`. Taking the interior makes the definition
manifestly produce an open subscheme without first proving properness.

The base change of the family along `g` is expressed by the canonical pullback projection
`pullback.snd`.

`AlgebraicGeometry.IsSyntomicAt` and `AlgebraicGeometry.SyntomicAt` are two names in this library
for the same predicate; `AlgebraicGeometry.isSyntomicAt_iff_syntomicAt` records that, and is used
to feed the base-change statement of Tag 02V3, which is phrased with the former, into statements
about `AlgebraicGeometry.Syntomic`, which is defined through the latter.

## References

* [Stacks Project, Tag 0FL0](https://stacks.math.columbia.edu/tag/0FL0)
* [Stacks Project, Tag 0FKZ](https://stacks.math.columbia.edu/tag/0FKZ)
* [Stacks Project, Tag 01UC](https://stacks.math.columbia.edu/tag/01UC)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 02V3](https://stacks.math.columbia.edu/tag/02V3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
  AlgebraicGeometry.FiniteFreeAlgebra

universe u

namespace AlgebraicGeometry

/-- The two names this library carries for the predicate "`f` is syntomic at `x`" agree. -/
theorem isSyntomicAt_iff_syntomicAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsSyntomicAt f x ↔ SyntomicAt f x := Iff.rfl

/-- The locus where a morphism of schemes is syntomic is open: syntomicity at a point is
witnessed by an affine open neighbourhood, and the same witness serves every point of that
neighbourhood. -/
theorem isOpen_setOf_syntomicAt {X S : Scheme.{u}} (f : X ⟶ S) :
    IsOpen {x : X | SyntomicAt f x} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hxU, V, hUV, hsyn⟩ := (syntomicAt_iff f x).mp hx
  exact ⟨U.1, fun z hz ↦ (syntomicAt_iff f z).mpr ⟨U, hz, V, hUV, hsyn⟩, U.1.isOpen, hxU⟩

variable (d : ℕ) [NeZero d]

/-- The set of points of `X_d` over which the universal finite free family of rank `d` is
syntomic at every point of the fibre. -/
def universalSyntomicLocus : Set (scheme.{u} d) :=
  {x | ∀ y : universalTotalScheme.{u} d (universalAlgebraStructure d),
    universalFamily.{u} d (universalAlgebraStructure d) y = x →
      SyntomicAt (universalFamily.{u} d (universalAlgebraStructure d)) y}

/-- **Stacks Project, Tag 0FL0.** The open subscheme of the base `X_d` of the universal finite
free family of rank `d` over which the family is syntomic.

It is the interior of `AlgebraicGeometry.universalSyntomicLocus`; that set is already open, by
`AlgebraicGeometry.universalSyntomicLocus_isOpen`. -/
@[stacks 0FL0 "the open subscheme"]
def universalSyntomicOpen : (scheme.{u} d).Opens :=
  ⟨interior (universalSyntomicLocus.{u} d), isOpen_interior⟩

/-- The locus of `AlgebraicGeometry.universalSyntomicLocus` is open: its complement is the image
of the closed non-syntomic locus under the universal family, which is a closed map because the
family is finite. -/
theorem universalSyntomicLocus_isOpen : IsOpen (universalSyntomicLocus.{u} d) := by
  let π := universalFamily.{u} d (universalAlgebraStructure d)
  have hprops := universalFamily_isFinite_flat_locallyOfFinitePresentation.{u} d
  have : IsIntegralHom π := ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType π).mp hprops.1).1
  have : UniversallyClosed π :=
    (IsIntegralHom.iff_universallyClosed_and_isAffineHom).mp inferInstance |>.1
  have hEq : universalSyntomicLocus.{u} d = (π '' {y | SyntomicAt π y}ᶜ)ᶜ :=
    Set.ext fun _ ↦ ⟨fun hb ⟨y, hy, hyb⟩ ↦ hy (hb y hyb),
      fun hb y hyb ↦ of_not_not fun hyW ↦ hb ⟨y, hyW, hyb⟩⟩
  rw [hEq]
  exact (π.isClosedMap _ (isOpen_setOf_syntomicAt π).isClosed_compl).isOpen_compl

/-- The open subscheme of Tag 0FL0 is the whole locus where the universal family is syntomic on
the fibre: no interior needs to be taken. -/
theorem universalSyntomicOpen_coe_eq :
    ((universalSyntomicOpen.{u} d : (scheme.{u} d).Opens) :
      Set (scheme.{u} d)) = universalSyntomicLocus.{u} d :=
  interior_eq_iff_isOpen.mpr (universalSyntomicLocus_isOpen.{u} d)

/-- **Stacks Project, Tag 0FL0.** A morphism `g : T ⟶ X_d` to the base of the universal finite
free family of rank `d` factors through the open subscheme
`AlgebraicGeometry.universalSyntomicOpen` exactly when the base change of the family along `g` is
syntomic. -/
@[stacks 0FL0 "universal property"]
theorem factorsThrough_universalSyntomicOpen_iff (T : Scheme.{u})
    (g : T ⟶ scheme.{u} d) :
    (∃ ĝ : T ⟶ (universalSyntomicOpen.{u} d).toScheme,
        ĝ ≫ (universalSyntomicOpen.{u} d).ι = g) ↔
      Syntomic (pullback.snd (universalFamily.{u} d (universalAlgebraStructure d)) g) := by
  let π := universalFamily.{u} d (universalAlgebraStructure d)
  let U := universalSyntomicOpen.{u} d
  let p := pullback.snd π g
  have hprops := universalFamily_isFinite_flat_locallyOfFinitePresentation.{u} d
  have : Flat π := hprops.2.1
  have : LocallyOfFinitePresentation π := hprops.2.2
  have hbase := syntomicLocus_eq_preimage (pullback.fst π g) p π g (IsPullback.of_hasPullback π g)
  have hFactor : (∃ ĝ : T ⟶ U.toScheme, ĝ ≫ U.ι = g) ↔ Set.range g.base ⊆ (U : Set _) := by
    refine ⟨?_, fun hg ↦ ⟨IsOpenImmersion.lift U.ι g
      (by simpa only [Scheme.Opens.range_ι] using hg), IsOpenImmersion.lift_fac _ _ _⟩⟩
    rintro ⟨ĝ, hĝ⟩ _ ⟨t, rfl⟩
    have ht : g.base t ∈ Set.range U.ι :=
      ⟨ĝ.base t, by simpa using congrArg (fun k : T ⟶ _ ↦ k.base t) hĝ⟩
    simpa only [Scheme.Opens.range_ι] using ht
  have hRange : Set.range g.base ⊆ (U : Set _) ↔ Syntomic p := by
    rw [Set.range_subset_iff]
    change (∀ t : T, g t ∈ (U : Set _)) ↔ ∀ z : (pullback π g : Scheme), SyntomicAt p z
    rw [universalSyntomicOpen_coe_eq.{u} d]
    have hbaseAt (z : (pullback π g : Scheme)) :
        SyntomicAt p z ↔ SyntomicAt π ((pullback.fst π g).base z) := by
      rw [← isSyntomicAt_iff_syntomicAt, ← isSyntomicAt_iff_syntomicAt]
      simpa using congrArg (fun W : Set (pullback π g : Scheme) ↦ z ∈ W) hbase
    refine ⟨fun hg z ↦ ?_, fun hz t y hy ↦ ?_⟩
    · have hz : π ((pullback.fst π g).base z) = g ((pullback.snd π g).base z) := by
        simpa using congrArg (fun k : pullback π g ⟶ scheme.{u} d ↦ k.base z)
          (pullback.condition (f := π) (g := g))
      exact (hbaseAt z).mpr (hg ((pullback.snd π g).base z) ((pullback.fst π g).base z) hz)
    · obtain ⟨z, hzfst, _⟩ :=
        Scheme.Pullback.exists_preimage_pullback (f := π) (g := g) y t hy
      simpa only [hzfst] using (hbaseAt z).mp (hz z)
  exact hFactor.trans hRange

end AlgebraicGeometry

end
