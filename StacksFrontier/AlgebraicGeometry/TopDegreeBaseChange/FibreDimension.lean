module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness

/-!
# Fibre dimension near a point, and the reduction of top-degree vanishing to an affine base

[Stacks, Tag 0E7D] bounds the higher direct images of a proper morphism `f : X ⟶ Y` above the
dimension of a single fibre `X_y`. Its proof opens by replacing `Y` with an affine open
neighbourhood `V` of `y` over which *every* fibre has dimension at most `d`: the locus of points
of `X` where the fibre has local dimension at most `d` is open ([Stacks, Tag 02FZ]), its
complement is closed, and `f` being proper is a closed map, so the image of that complement is a
closed set avoiding `y`.

This file proves that opening move, together with the transport statement it needs — the fibres
of `f ∣_ V` are the fibres of `f` over points of `V` — and assembles them into the reduction of
part (2) of the tag to the case of an affine base over which all fibres are bounded. That
remaining case is the substance
of the tag's proof (a limit argument reducing to a Noetherian base, then Grothendieck vanishing
for coherent modules) and is not proved here; it enters as the hypothesis `hvan`.

## Main results

* `AlgebraicGeometry.exists_isOpen_forall_topologicalKrullDim_fiber_le`: a bound on one fibre of
  a closed morphism locally of finite type propagates to an open neighbourhood of the image
  point.
* `AlgebraicGeometry.exists_isAffineOpen_forall_topologicalKrullDim_fiber_le`: the same with the
  neighbourhood affine.
* `AlgebraicGeometry.topologicalKrullDim_fiber_morphismRestrict_le`: the fibres of `f ∣_ V` are
  bounded by the fibres of `f` over points of `V`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.exists_isAffineOpen_vanishing_of_affine_base`:
  part (2) of [Stacks, Tag 0E7D], granted the vanishing over an affine base with all fibres
  bounded.

## Implementation notes

The dimension of the fibre of `f` through a point `x` is
`topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)`, as in
`AlgebraicGeometry.isOpen_setOf_fiberDimensionAt_le`, while the hypothesis and conclusion of the
tag are about the dimension `topologicalKrullDim (f.fiber y)` of a whole fibre. The two are
related by `TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim`, which is why the
pointwise statement has to be converted at both ends.

The source's equality `dim(X_y) = d` is recorded as the upper bound `≤ d`, which is all the
proof uses and is the weaker hypothesis. The degree `d` is a natural number, which is how the
source's hypothesis `d ≥ 0` is recorded; it is coerced to `WithBot ℕ∞` to compare with a
dimension and to `ℤ` to index `CategoryTheory.Functor.rightDerivedPlus`.

`exists_isOpen_forall_topologicalKrullDim_fiber_le` asks for `IsClosedMap f.base` and
`LocallyOfFiniteType f` rather than `IsProper f`: those are the only two consequences of
properness the argument uses.

## References

* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 02FZ](https://stacks.math.columbia.edu/tag/02FZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The fibre of `f` at a point of its source, transported to the fibre over any point with the
same image. -/
private noncomputable def fiberHomeoOfEq {X Y : Scheme.{u}} (f : X ⟶ Y) {s : Y} {x : X}
    (hx : f x = s) : f.fiber (f x) ≃ₜ f.fiber s :=
  (f.fiberHomeo (f x)).trans <|
    (Homeomorph.setCongr (by rw [hx])).trans (f.fiberHomeo s).symm

private lemma fiberHomeoOfEq_asFiber {X Y : Scheme.{u}} (f : X ⟶ Y) {s : Y} {x : X}
    (hx : f x = s) (z : f.fiber s) (hz : (f.fiberHomeo s z).1 = x) :
    fiberHomeoOfEq f hx (f.asFiber x) = z := by
  apply (f.fiberHomeo s).injective
  apply Subtype.ext
  show f.fiberι s ((f.fiberHomeo s).symm ((Homeomorph.setCongr (by rw [hx]))
    (f.fiberHomeo (f x) (f.asFiber x)))) = f.fiberι s z
  rw [Scheme.Hom.fiberι_fiberHomeo_symm]
  show ((Set.equivOfEq (by rw [hx])) (f.fiberHomeo (f x) (f.asFiber x))).1 =
    (f.fiberHomeo s z).1
  simp only [Set.equivOfEq_apply, Scheme.Hom.fiberHomeo_apply, Scheme.Hom.fiberι_asFiber]
  exact hz.symm

/-- A fibre of `f` has dimension at most `d` as soon as every one of its points `x` satisfies
`dim_x X_{f x} ≤ d`. -/
private lemma topologicalKrullDim_fiber_le_of_forall_fiberDimensionAt_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y) (d : ℕ)
    (h : ∀ x : X, f x = s →
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (d : WithBot ℕ∞)) :
    topologicalKrullDim (f.fiber s) ≤ (d : WithBot ℕ∞) := by
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun z ↦ ?_
  rw [← topologicalKrullDimAt_eq_localKrullDim]
  have hx : f (f.fiberHomeo s z).1 = s := Set.mem_singleton_iff.mp (f.fiberHomeo s z).2
  have he := topologicalKrullDimAt_eq_of_homeomorph (fiberHomeoOfEq f hx)
    (f.asFiber (f.fiberHomeo s z).1)
  rw [fiberHomeoOfEq_asFiber f hx z rfl] at he
  exact he ▸ h _ hx

/-- **The opening move of the proof of [Stacks, Tag 0E7D].** If `f` is locally of finite type and
closed and one fibre of `f` has dimension at most `d`, then all the fibres over an open
neighbourhood of that point have dimension at most `d`.

The locus in `X` where the fibre has local dimension at most `d` is open ([Stacks, Tag 02FZ]);
its complement is closed, hence has closed image, and that image misses `y` precisely because
`X_y` has dimension at most `d`. -/
theorem exists_isOpen_forall_topologicalKrullDim_fiber_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsClosedMap f.base)
    (y : Y) (d : ℕ) (hdim : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) :
    ∃ W : Y.Opens, y ∈ W ∧
      ∀ s : Y, s ∈ W → topologicalKrullDim (f.fiber s) ≤ (d : WithBot ℕ∞) := by
  set U : Set X :=
    {x | topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (d : WithBot ℕ∞)} with hU
  have hUopen : IsOpen U := isOpen_setOf_fiberDimensionAt_le f d
  have hy : y ∉ f.base '' Uᶜ := by
    rintro ⟨x, hx, hxy⟩
    subst hxy
    exact hx ((topologicalKrullDimAt_le_topologicalKrullDim (f.asFiber x)).trans hdim)
  refine ⟨⟨(f.base '' Uᶜ)ᶜ, (hf Uᶜ hUopen.isClosed_compl).isOpen_compl⟩, hy, fun s hs ↦ ?_⟩
  refine topologicalKrullDim_fiber_le_of_forall_fiberDimensionAt_le f s d fun x hx ↦ ?_
  by_contra hxU
  exact hs ⟨x, hxU, hx⟩

/-- **[Stacks, Tag 0E7D]**, the opening move with the neighbourhood taken affine: the affine opens
form a basis, so the open neighbourhood produced by
`exists_isOpen_forall_topologicalKrullDim_fiber_le` can be shrunk to an affine one. -/
theorem exists_isAffineOpen_forall_topologicalKrullDim_fiber_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsClosedMap f.base)
    (y : Y) (d : ℕ) (hdim : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) :
    ∃ V : Y.Opens, y ∈ V ∧ IsAffineOpen V ∧
      ∀ s : Y, s ∈ V → topologicalKrullDim (f.fiber s) ≤ (d : WithBot ℕ∞) := by
  obtain ⟨W, hyW, hW⟩ := exists_isOpen_forall_topologicalKrullDim_fiber_le f hf y d hdim
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVW⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyW W.isOpen
  exact ⟨V, hyV, hV, fun s hs ↦ hW s (hVW hs)⟩

/-- The fibres of the restriction `f ∣_ V` are the fibres of `f` over the points of `V`, so a
bound on the latter bounds the former. The restriction square is cartesian
(`AlgebraicGeometry.isPullback_morphismRestrict`), so this is [Stacks, Tag 02FY] part (1). -/
theorem topologicalKrullDim_fiber_morphismRestrict_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (V : Y.Opens) (d : ℕ)
    (hdim : ∀ y : Y, y ∈ V → topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (s : V.toScheme) :
    topologicalKrullDim ((f ∣_ V).fiber s) ≤ (d : WithBot ℕ∞) := by
  refine topologicalKrullDim_fiber_le_of_forall_fiberDimensionAt_le (f ∣_ V) s d fun x _ ↦ ?_
  rw [topologicalKrullDimAt_fiber_eq_of_isPullback (isPullback_morphismRestrict f V).flip x]
  exact (topologicalKrullDimAt_le_topologicalKrullDim _).trans (hdim _ x.2)

end AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- **[Stacks, Tag 0E7D] part (2), reduced to an affine base.** Granted that a proper morphism
onto an affine scheme all of whose fibres have dimension at most `d` has vanishing higher direct
images of quasi-coherent modules above `d` — the hypothesis `hvan`, which is the substance of
the tag's proof — a proper morphism with one fibre of dimension at most `d` has an affine open
neighbourhood `V` of the image point over which `f ∣_ V` satisfies the four finiteness
hypotheses and the universal vanishing hypothesis of the top-degree base-change situation
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation`.

This is the whole of part (2) except for `hvan`; the statement of the tag is obtained from it by
discharging `hvan`. -/
theorem exists_isAffineOpen_vanishing_of_affine_base
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (hvan : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ F : X₀.Modules, F.IsQuasicoherent →
        IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus i).obj F)) :
    ∃ V : Y.Opens,
      y ∈ V ∧ IsAffineOpen V ∧
      CompactSpace (f ⁻¹ᵁ V).toScheme ∧
      QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme ∧
      CompactSpace V.toScheme ∧ QuasiSeparatedSpace V.toScheme ∧
      (∀ (i : ℤ), (d : ℤ) < i →
        ∀ (F : (f ⁻¹ᵁ V).toScheme.Modules), F.IsQuasicoherent →
          IsZero (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus i).obj F)) := by
  obtain ⟨V, hyV, hVaff, hVdim⟩ :=
    exists_isAffineOpen_forall_topologicalKrullDim_fiber_le f f.isClosedMap y d hdim
  have hVcompact : IsCompact (V : Set Y) := hVaff.isCompact
  let _ : IsAffine V.toScheme := hVaff
  refine ⟨V, hyV, hVaff,
    isCompact_iff_compactSpace.mp (f.isCompact_preimage hVcompact),
    quasiSeparatedSpace_of_quasiSeparated (f ∣_ V),
    isCompact_iff_compactSpace.mp hVcompact, inferInstance, fun i hi F hF ↦ ?_⟩
  exact hvan (f ∣_ V) inferInstance inferInstance
    (topologicalKrullDim_fiber_morphismRestrict_le f V d hVdim) i hi F hF

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange
