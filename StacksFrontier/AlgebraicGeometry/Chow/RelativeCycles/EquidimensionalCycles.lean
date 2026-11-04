module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ProperRelativeCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.RestrictionSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.Topology.Dimension.ClosedSubsetDimension
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksCore.Tactic.StacksAttribute

/-!
# Equidimensional families of cycles on the fibres of a morphism

Let `f : X ⟶ S` be a morphism locally of finite type onto a locally Noetherian base and let
`r ≥ 0`. A family of `r`-cycles on the fibres of `f` is *equidimensional* when its support is
contained in a closed subset of `X` whose relative dimension over `S` is at most `r`. The
support of such a family is in general not closed, so this is a genuine restriction: it asks
that the fibrewise supports be bounded uniformly, by one closed subset of the total space whose
fibres all have dimension at most `r`. The equidimensional relative `r`-cycles form a subgroup
`z_equi(X/S, r)` of the group `z(X/S, r)` of all relative `r`-cycles.

Equidimensionality is a condition on the support alone, and the support of the restriction of a
family to open subschemes `U ⊆ X` and `V ⊆ S` is the part of the original support lying in `U`;
restriction preserves equidimensionality, and equidimensionality may be checked on an open cover.

## Main definitions

* `Stacks.Chow.IsEquidimensional` — the support of a family of `r`-cycles is contained in a
  closed subset of relative dimension at most `r` over the base.
* `Stacks.Chow.equidimensionalRelativeCycles` — the group `z_equi(X/S, r)` of equidimensional
  relative `r`-cycles.
* `Stacks.Chow.RelativeDimensionLEOn` — a subset of `X` has relative dimension at most `r`
  over `S`: at each of its points the part of it lying in the fibre through that point has
  local Krull dimension at most `r`.

## Main results

* `Stacks.Chow.isEquidimensional_iff` — the defining condition on the support.
* `Stacks.Chow.isEquidimensional_restrictedFamily` — restricting to compatible open subschemes
  of the source and the base preserves equidimensionality.
* `Stacks.Chow.isEquidimensional_iff_relativeDimensionLEOn_closure` — a family is
  equidimensional exactly when the closure of its support has relative dimension at most `r`.
* `Stacks.Chow.isEquidimensional_iff_forall_restrictedFamily` — equidimensionality may be
  checked on any family of compatible open subschemes of the source and the base whose members
  in the source cover it.
* `Stacks.Chow.relativeDimensionLEOn_iff_forall_topologicalKrullDim` — relative dimension at
  most `r` is the bound `dim ≤ r` on each intersection with a fibre.
* `Stacks.Chow.RelativeDimensionLEOn.union` — a union of two closed subsets of relative
  dimension at most `r` has relative dimension at most `r`.
* `Stacks.Chow.mem_equidimensionalRelativeCycles` — membership in `z_equi(X/S, r)` is the
  conjunction of the relative-cycle condition and equidimensionality.
* `Stacks.Chow.equidimensionalRelativeCycles_le_relativeCycles` — the inclusion
  `z_equi(X/S, r) ⊆ z(X/S, r)`.

## Implementation notes

A closed subset of `X` is presented as the support of an ideal sheaf `W : X.IdealSheafData`,
and the dimension bound is `AlgebraicGeometry.RelativeDimensionLE` for the composite
`W.subscheme ⟶ X ⟶ S`. Relative dimension is a topological invariant of the fibres, so the
bound depends only on the closed subset `W.support` and not on the chosen ideal sheaf
presenting it; every closed subset arises this way, from its vanishing ideal.

`Stacks.Chow.IsEquidimensional` is a condition on a family of cycles alone, with no
relative-cycle hypothesis; the group `z_equi(X/S, r)` is cut out of the families of `r`-cycles on
the fibres by that condition together with the valuative condition of Definition 0H50, so its
members are relative `r`-cycles.

## References

* [Stacks Project, Tag 0H5I](https://stacks.math.columbia.edu/tag/0H5I)
* [Stacks Project, Tag 0H5K](https://stacks.math.columbia.edu/tag/0H5K)
* [Stacks Project, Tag 0H5L](https://stacks.math.columbia.edu/tag/0H5L)
* [Stacks Project, Definition 0H50](https://stacks.math.columbia.edu/tag/0H50)
* [Stacks Project, Remark 0H4U](https://stacks.math.columbia.edu/tag/0H4U)
* [Stacks Project, Tag 0B7I](https://stacks.math.columbia.edu/tag/0B7I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- A family of `r`-cycles on the fibres of `f` is *equidimensional* when its support is
contained in a closed subset of `X` whose relative dimension over `S` is at most `r`. -/
@[stacks 0H5I "the equidimensionality condition"]
def IsEquidimensional {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r) : Prop :=
  ∃ W : X.IdealSheafData,
    supportOfFamily f α ⊆ (W.support : Set X) ∧ RelativeDimensionLE (W.subschemeι ≫ f) r

/-- A family of cycles is equidimensional exactly when a closed subscheme of relative dimension
at most `r` over the base contains its support. -/
theorem isEquidimensional_iff {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r) :
    IsEquidimensional f r α ↔
      ∃ W : X.IdealSheafData,
        supportOfFamily f α ⊆ (W.support : Set X) ∧
          RelativeDimensionLE (W.subschemeι ≫ f) r :=
  Iff.rfl

/-- A morphism of open subschemes `U ⟶ V` compatible with open immersions into `X ⟶ S` is locally
of finite type when `X ⟶ S` is. -/
private theorem locallyOfFiniteType_of_openSquare {X S U V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ V) (j : U ⟶ X) [IsOpenImmersion j] (i : V ⟶ S)
    [IsOpenImmersion i] (h : j ≫ f = fU ≫ i) : LocallyOfFiniteType fU := by
  let : LocallyOfFiniteType (fU ≫ i) := h ▸ inferInstance
  exact locallyOfFiniteType_of_comp fU i

/-- Restriction to compatible open subschemes of the source and the base preserves
equidimensionality of a family of cycles on the fibres. -/
@[stacks 0H5K "restriction"]
theorem isEquidimensional_restrictedFamily {X S U V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (fU : U ⟶ V) (j : U ⟶ X) [IsOpenImmersion j]
    (i : V ⟶ S) [IsOpenImmersion i] (h : j ≫ f = fU ≫ i) (r : ℕ) (α : FamilyOfCycles f r)
    (hα : IsEquidimensional f r α) :
    letI : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion i
    letI : LocallyOfFiniteType fU := by
      let : LocallyOfFiniteType (fU ≫ i) := h ▸ inferInstance
      exact locallyOfFiniteType_of_comp fU i
    IsEquidimensional fU r (restrictedFamily f fU j i h r α).1 := by
  have : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion i
  have : LocallyOfFiniteType fU := locallyOfFiniteType_of_openSquare f fU j i h
  obtain ⟨W, hsupport, hdim⟩ := hα
  refine ⟨W.comap j, ?_, ?_⟩
  · intro z hz
    have hz' : j z ∈ j '' supportOfFamily fU (restrictedFamily f fU j i h r α).1 := ⟨z, hz, rfl⟩
    rw [image_supportOfFamily_restrictedFamily f fU j i h r α] at hz'
    rw [Scheme.IdealSheafData.support_comap]
    exact hsupport hz'.2
  · set g : W.subscheme ⟶ S := W.subschemeι ≫ f with hg
    have hqcomm : (W.comapIso j).hom ≫ pullback.snd j W.subschemeι ≫ g =
        (W.comap j).subschemeι ≫ fU ≫ i := by
      calc
        (W.comapIso j).hom ≫ pullback.snd j W.subschemeι ≫ g =
            (W.comapIso j).hom ≫ (pullback.snd j W.subschemeι ≫ W.subschemeι) ≫ f := by
          simp [hg, Category.assoc]
        _ = (W.comapIso j).hom ≫ (pullback.fst j W.subschemeι ≫ j) ≫ f := by
          rw [pullback.condition]
        _ = (W.comap j).subschemeι ≫ j ≫ f := by
          simpa only [Category.assoc] using
            congrArg (fun k : (W.comap j).subscheme ⟶ U => k ≫ j ≫ f)
              (Scheme.IdealSheafData.comapIso_hom_fst W j)
        _ = (W.comap j).subschemeι ≫ fU ≫ i := by rw [h]
    set q : (W.comap j).subscheme ⟶ pullback g i :=
      pullback.lift ((W.comapIso j).hom ≫ pullback.snd j W.subschemeι)
        ((W.comap j).subschemeι ≫ fU) (by simpa only [Category.assoc] using hqcomm) with hq
    have hqfst : q ≫ pullback.fst g i = (W.comapIso j).hom ≫ pullback.snd j W.subschemeι :=
      pullback.lift_fst _ _ _
    have hqsnd : q ≫ pullback.snd g i = (W.comap j).subschemeι ≫ fU :=
      pullback.lift_snd _ _ _
    have : IsOpenImmersion q := by
      have : IsOpenImmersion (q ≫ pullback.fst g i) := by
        rw [hqfst]; infer_instance
      exact IsOpenImmersion.of_comp q (pullback.fst g i)
    have hdimT : RelativeDimensionLE (pullback.snd g i) r :=
      AlgebraicGeometry.RelativeDimensionLE.of_isPullback (IsPullback.of_hasPullback g i) hdim
    intro z
    rw [relativeDimensionLEAt_iff, ← hqsnd,
      AlgebraicGeometry.fiberDimensionAt_comp_openImmersion q _ z]
    exact hdimT (q z)

/-- The Krull dimension at a point of a subspace does not increase when the subspace is
enlarged. -/
private theorem topologicalKrullDimAt_le_of_subset {T : Type*} [TopologicalSpace T]
    {D D' : Set T} (hD : D' ⊆ D) (x : D') :
    topologicalKrullDimAt ↥D' x ≤ topologicalKrullDimAt ↥D ⟨x.1, hD x.2⟩ :=
  topologicalKrullDimAt_le_of_isEmbedding (Topology.IsEmbedding.inclusion hD) x

/-- A subset `D` of `X` has *relative dimension at most `r`* over `S` along `f : X ⟶ S` if at
each point `x` of `D` the part of `D` lying in the fibre of `f` through `x` has local Krull
dimension at most `r` at `x`. -/
def RelativeDimensionLEOn {X S : Scheme.{u}} (f : X ⟶ S) (D : Set X) (r : ℕ) : Prop :=
  ∀ (x : X) (hx : x ∈ D),
    topologicalKrullDimAt ↥(D ∩ f ⁻¹' {f x}) ⟨x, hx, rfl⟩ ≤ (r : WithBot ℕ∞)

/-- A subset of a subset of relative dimension at most `r` again has relative dimension at
most `r`. -/
theorem RelativeDimensionLEOn.mono {X S : Scheme.{u}} {f : X ⟶ S} {D D' : Set X} {r : ℕ}
    (hD : RelativeDimensionLEOn f D r) (hsub : D' ⊆ D) : RelativeDimensionLEOn f D' r :=
  fun x hx => le_trans
    (topologicalKrullDimAt_le_of_subset
      (Set.inter_subset_inter_left (f ⁻¹' {f x}) hsub) ⟨x, hx, rfl⟩)
    (hD x (hsub hx))

/-- A point of a closed subscheme maps into the closed subset it carries. -/
private theorem subschemeι_mem_support {X : Scheme.{u}} (I : X.IdealSheafData)
    (z : I.subscheme) : I.subschemeι z ∈ (I.support : Set X) := by
  rw [← I.range_subschemeι]; exact ⟨z, rfl⟩

/-- The fibre of a closed subscheme of `X` over the base, at a point of the subscheme, is the
part of the closed subset lying in the fibre of `f` through the image of that point. -/
private theorem topologicalKrullDimAt_fiber_subschemeι {X S : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) (z : I.subscheme) :
    topologicalKrullDimAt ((I.subschemeι ≫ f).fiber ((I.subschemeι ≫ f) z))
        ((I.subschemeι ≫ f).asFiber z) =
      topologicalKrullDimAt ↥((I.support : Set X) ∩ f ⁻¹' {f (I.subschemeι z)})
        ⟨I.subschemeι z, subschemeι_mem_support I z, rfl⟩ := by
  have hEmb : Topology.IsEmbedding (I.subschemeι).base :=
    (IsPreimmersion.isEmbedding I.subschemeι)
  set E : Set X := (I.support : Set X) ∩ f ⁻¹' {f (I.subschemeι z)} with hE
  have hsub : E ⊆ Set.range (I.subschemeι).base := by
    rw [I.range_subschemeι]
    exact Set.inter_subset_left
  have hpre : ((I.subschemeι ≫ f) ⁻¹' {(I.subschemeι ≫ f) z} : Set I.subscheme) =
      (I.subschemeι).base ⁻¹' E := by
    ext w
    simp only [hE, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
      Scheme.Hom.comp_apply]
    exact ⟨fun hw => ⟨subschemeι_mem_support I w, hw⟩, fun hw => hw.2⟩
  let e : (I.subschemeι ≫ f).fiber ((I.subschemeι ≫ f) z) ≃ₜ ↥E :=
    ((I.subschemeι ≫ f).fiberHomeo _).trans
      ((Homeomorph.setCongr hpre).trans (hEmb.homeomorphOfSubsetRange hsub))
  have hpt : e ((I.subschemeι ≫ f).asFiber z) =
      ⟨I.subschemeι z, subschemeι_mem_support I z, rfl⟩ := by
    apply Subtype.ext
    change (I.subschemeι).base ((I.subschemeι ≫ f).fiberι _ ((I.subschemeι ≫ f).asFiber z)) = _
    rw [(I.subschemeι ≫ f).fiberι_asFiber]
  rw [topologicalKrullDimAt_eq_of_homeomorph e ((I.subschemeι ≫ f).asFiber z), hpt]

/-- The relative dimension of a closed subscheme of `X` over `S` depends only on the closed
subset it carries: it is at most `r` exactly when that subset has relative dimension at most
`r` over `S`. -/
theorem relativeDimensionLE_subschemeι_iff {X S : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) [LocallyOfFiniteType (I.subschemeι ≫ f)] (r : ℕ) :
    RelativeDimensionLE (I.subschemeι ≫ f) r ↔
      RelativeDimensionLEOn f (I.support : Set X) r := by
  constructor
  · intro hI x hx
    obtain ⟨z, rfl⟩ : ∃ z : I.subscheme, I.subschemeι z = x := by
      rwa [← Set.mem_range, I.range_subschemeι]
    exact (topologicalKrullDimAt_fiber_subschemeι f I z) ▸ hI z
  · exact fun hD z => (topologicalKrullDimAt_fiber_subschemeι f I z).trans_le
      (hD (I.subschemeι z) (subschemeι_mem_support I z))

/-- Relative dimension at a point is unchanged by restriction to an open subscheme `U` of `X`
lying over an open subscheme `V` of `S`. -/
private theorem topologicalKrullDimAt_inter_fiber_of_openSquare {X S U V : Scheme.{u}}
    (f : X ⟶ S) (fU : U ⟶ V) (j : U ⟶ X) [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i]
    (h : j ≫ f = fU ≫ i) (D : Set X) (u : U) (hu : j u ∈ D) :
    topologicalKrullDimAt ↥((j.base ⁻¹' D) ∩ fU ⁻¹' {fU u}) ⟨u, hu, rfl⟩ =
      topologicalKrullDimAt ↥(D ∩ f ⁻¹' {f (j u)}) ⟨j u, hu, rfl⟩ := by
  have hji : ∀ w : U, f (j w) = i (fU w) := fun w => by
    simpa using congrArg (fun q : U ⟶ S => q w) h
  have hsets : ((j.base ⁻¹' D) ∩ fU ⁻¹' {fU u} : Set U) =
      j.base ⁻¹' (D ∩ f ⁻¹' {f (j u)}) := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    refine and_congr_right fun _ => ?_
    rw [hji w, hji u]
    exact ⟨fun hw => congrArg i.base hw, fun hw => i.isOpenEmbedding.injective hw⟩
  rw [topologicalKrullDimAt_eq_of_homeomorph (Homeomorph.setCongr hsets) ⟨u, hu, rfl⟩]
  exact ((j.isOpenEmbedding.restrictPreimage (D ∩ f ⁻¹' {f (j u)})).topologicalKrullDimAt_eq
    ⟨u, hu, rfl⟩).symm

/-- A family of cycles is equidimensional exactly when the closure of its support has relative
dimension at most `r` over the base. -/
theorem isEquidimensional_iff_relativeDimensionLEOn_closure {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r) :
    IsEquidimensional f r α ↔
      RelativeDimensionLEOn f (closure (supportOfFamily f α)) r := by
  constructor
  · rintro ⟨W, hWsupport, hWdim⟩
    exact ((relativeDimensionLE_subschemeι_iff f W r).mp hWdim).mono
      (closure_minimal hWsupport W.support.isClosed)
  · intro hD
    refine ⟨Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (supportOfFamily f α)), ?_, ?_⟩
    · rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact subset_closure
    · rwa [relativeDimensionLE_subschemeι_iff,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- The support of a restricted family of cycles is the inverse image of the support of the
original family. -/
@[ega "IV 21.6.3" "special case"]
private theorem supportOfFamily_restrictedFamily_eq_preimage {X S U V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ V) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i] (h : j ≫ f = fU ≫ i) (r : ℕ)
    (α : FamilyOfCycles f r) :
    supportOfFamily fU (restrictedFamily f fU j i h r α).1 =
      j.base ⁻¹' supportOfFamily f α := by
  ext u
  rw [Set.mem_preimage, ← j.isOpenEmbedding.injective.mem_set_image,
    image_supportOfFamily_restrictedFamily f fU j i h r α]
  exact and_iff_right ⟨u, rfl⟩

/-- Equidimensionality of a family of cycles may be checked Zariski locally on `X` and on `S`:
given open subschemes `U t ⊆ X` lying over open subschemes `V t ⊆ S` whose members cover `X`,
the family is equidimensional exactly when each of its restrictions is. -/
@[stacks 0H5L]
theorem isEquidimensional_iff_forall_restrictedFamily {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r)
    {ι : Type*} (U V : ι → Scheme.{u})
    (fU : ∀ t, U t ⟶ V t) (j : ∀ t, U t ⟶ X) (hj : ∀ t, IsOpenImmersion (j t))
    (i : ∀ t, V t ⟶ S) (hi : ∀ t, IsOpenImmersion (i t))
    (h : ∀ t, j t ≫ f = fU t ≫ i t)
    (hcover : ∀ x : X, ∃ (t : ι) (y : U t), j t y = x) :
    IsEquidimensional f r α ↔
      ∀ t : ι,
        letI : IsOpenImmersion (j t) := hj t
        letI : IsOpenImmersion (i t) := hi t
        letI : IsLocallyNoetherian (V t) := isLocallyNoetherian_of_isOpenImmersion (i t)
        letI : LocallyOfFiniteType (fU t) := by
          let : LocallyOfFiniteType (fU t ≫ i t) := h t ▸ inferInstance
          exact locallyOfFiniteType_of_comp (fU t) (i t)
        IsEquidimensional (fU t) r (restrictedFamily f (fU t) (j t) (i t) (h t) r α).1 := by
  have hnoeth : ∀ t, IsLocallyNoetherian (V t) := fun t => by
    let : IsOpenImmersion (i t) := hi t
    exact isLocallyNoetherian_of_isOpenImmersion (i t)
  have hinst : ∀ t, LocallyOfFiniteType (fU t) := fun t => by
    let : IsOpenImmersion (i t) := hi t
    let : IsOpenImmersion (j t) := hj t
    exact locallyOfFiniteType_of_openSquare f (fU t) (j t) (i t) (h t)
  have key : ∀ t,
      letI := hj t; letI := hi t; letI := hnoeth t; letI := hinst t
      IsEquidimensional (fU t) r (restrictedFamily f (fU t) (j t) (i t) (h t) r α).1 ↔
        RelativeDimensionLEOn (fU t) ((j t).base ⁻¹' closure (supportOfFamily f α)) r := by
    intro t
    let : IsOpenImmersion (j t) := hj t
    let : IsOpenImmersion (i t) := hi t
    let : IsLocallyNoetherian (V t) := hnoeth t
    let : LocallyOfFiniteType (fU t) := hinst t
    rw [isEquidimensional_iff_relativeDimensionLEOn_closure,
      supportOfFamily_restrictedFamily_eq_preimage f (fU t) (j t) (i t) (h t) r α,
      ((j t).isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
        (j t).continuous (supportOfFamily f α)).symm]
  rw [isEquidimensional_iff_relativeDimensionLEOn_closure]
  constructor
  · intro hglob t
    rw [key t]
    intro y hy
    rw [topologicalKrullDimAt_inter_fiber_of_openSquare f (fU t) (j t) (i t) (h t)
      (closure (supportOfFamily f α)) y hy]
    exact hglob (j t y) hy
  · intro hlocal x hx
    obtain ⟨t, y, rfl⟩ := hcover x
    rw [← topologicalKrullDimAt_inter_fiber_of_openSquare f (fU t) (j t) (i t) (h t)
      (closure (supportOfFamily f α)) y hx]
    exact (key t).mp (hlocal t) y hx

/-! ### Unions of closed subsets of bounded relative dimension -/

section KrullDimensionOfUnion

open Order

/-- A chain of irreducible closed subsets of a space all of whose members lie in a subset `C` has
length at most the Krull dimension of `C`. -/
private theorem length_le_topologicalKrullDim_of_subset {T : Type*} [TopologicalSpace T]
    (p : LTSeries (IrreducibleCloseds T)) {C : Set T}
    (hC : ∀ i, (p.toFun i : Set T) ⊆ C) :
    (p.length : WithBot ℕ∞) ≤ topologicalKrullDim ↥C := by
  have hpre : ∀ {D₁ D₂ : Set T}, D₁ ⊆ C → D₂ ⊆ C →
      (Subtype.val ⁻¹' D₁ : Set ↥C) = Subtype.val ⁻¹' D₂ → D₁ = D₂ := by
    intro D₁ D₂ h₁ h₂ hEq
    rwa [Subtype.preimage_coe_eq_preimage_coe_iff, Set.inter_eq_right.2 h₁,
      Set.inter_eq_right.2 h₂] at hEq
  let F : Fin (p.length + 1) → IrreducibleCloseds ↥C := fun i =>
    ⟨Subtype.val ⁻¹' (p.toFun i : Set T),
      isIrreducible_preimage_subtypeVal (p.toFun i).isIrreducible (hC i),
      (p.toFun i).isClosed.preimage continuous_subtype_val⟩
  have hFmono : StrictMono F := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    have hlt : p.toFun i.castSucc < p.toFun i.succ := p.step i
    have hsub : (p.toFun i.castSucc : Set T) ⊆ (p.toFun i.succ : Set T) :=
      SetLike.coe_subset_coe.2 hlt.le
    refine lt_of_le_of_ne (fun z hz => hsub hz) fun hEq => ?_
    exact hlt.ne (SetLike.coe_injective
      (hpre (hC i.castSucc) (hC i.succ) (SetLike.coe_set_eq.2 hEq)))
  rw [topologicalKrullDim, Order.krullDim]
  exact le_iSup_of_le (LTSeries.mk p.length F hFmono) le_rfl

/-- The Krull dimension of a space covered by two closed subsets is at most the larger of their
two Krull dimensions. -/
private theorem topologicalKrullDim_le_max_of_union_eq_univ {T : Type*} [TopologicalSpace T]
    {A B : Set T} (hA : IsClosed A) (hB : IsClosed B) (hcover : A ∪ B = Set.univ) :
    topologicalKrullDim T ≤ max (topologicalKrullDim ↥A) (topologicalKrullDim ↥B) := by
  rw [topologicalKrullDim, Order.krullDim]
  refine iSup_le fun p => ?_
  have hsub : (p.toFun (Fin.last p.length) : Set T) ⊆ A ∪ B := hcover ▸ Set.subset_univ _
  have hmono : ∀ i, (p.toFun i : Set T) ⊆ (p.toFun (Fin.last p.length) : Set T) := fun i =>
    SetLike.coe_subset_coe.2 (LTSeries.monotone p (Fin.le_last i))
  rcases (isPreirreducible_iff_isClosed_union_isClosed.mp
      (p.toFun (Fin.last p.length)).isIrreducible.isPreirreducible) A B hA hB hsub with h | h <;>
    refine (length_le_topologicalKrullDim_of_subset p fun i => (hmono i).trans h).trans ?_
  exacts [le_max_left _ _, le_max_right _ _]

end KrullDimensionOfUnion

/-- A subset has relative dimension at most `r` over the base exactly when each of its
intersections with a fibre has Krull dimension at most `r`. -/
theorem relativeDimensionLEOn_iff_forall_topologicalKrullDim {X S : Scheme.{u}} (f : X ⟶ S)
    (D : Set X) (r : ℕ) :
    RelativeDimensionLEOn f D r ↔
      ∀ s : S, topologicalKrullDim ↥(D ∩ f ⁻¹' {s}) ≤ (r : WithBot ℕ∞) := by
  constructor
  · intro hD s
    rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    refine iSup_le fun z => ?_
    rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
    obtain ⟨x, hxD, hxs⟩ := z
    cases hxs
    exact hD x hxD
  · intro hD x hx
    exact (topologicalKrullDimAt_le_topologicalKrullDim ⟨x, hx, rfl⟩).trans (hD (f x))

/-- A union of two closed subsets of relative dimension at most `r` over the base again has
relative dimension at most `r`. -/
theorem RelativeDimensionLEOn.union {X S : Scheme.{u}} {f : X ⟶ S} {D₁ D₂ : Set X} {r : ℕ}
    (h₁ : RelativeDimensionLEOn f D₁ r) (h₂ : RelativeDimensionLEOn f D₂ r)
    (hc₁ : IsClosed D₁) (hc₂ : IsClosed D₂) :
    RelativeDimensionLEOn f (D₁ ∪ D₂) r := by
  rw [relativeDimensionLEOn_iff_forall_topologicalKrullDim] at h₁ h₂ ⊢
  intro s
  set E : Set X := (D₁ ∪ D₂) ∩ f ⁻¹' {s} with hE
  have hcover : (Subtype.val : ↥E → X) ⁻¹' D₁ ∪ (Subtype.val : ↥E → X) ⁻¹' D₂ = Set.univ := by
    ext z
    simpa only [Set.mem_union, Set.mem_preimage, Set.mem_univ, iff_true] using z.2.1
  have hdim : ∀ D : Set X, D ⊆ D₁ ∪ D₂ → topologicalKrullDim ((Subtype.val : ↥E → X) ⁻¹' D) =
      topologicalKrullDim ↥(D ∩ f ⁻¹' {s}) := fun D hD => by
    rw [show (Subtype.val : ↥E → X) ⁻¹' D = (Subtype.val : ↥E → X) ⁻¹' (D ∩ f ⁻¹' {s}) from
      Set.ext fun z => ⟨fun hz => ⟨hz, z.2.2⟩, fun hz => hz.1⟩]
    exact topologicalKrullDim_preimage_val E _ (Set.inter_subset_inter_left _ hD)
  refine (topologicalKrullDim_le_max_of_union_eq_univ (hc₁.preimage continuous_subtype_val)
    (hc₂.preimage continuous_subtype_val) hcover).trans (max_le ?_ ?_)
  · rw [hdim D₁ Set.subset_union_left]
    exact h₁ s
  · rw [hdim D₂ Set.subset_union_right]
    exact h₂ s

/-! ### The group of equidimensional relative cycles -/

/-- The zero family is equidimensional. -/
theorem isEquidimensional_zero {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) : IsEquidimensional f r (0 : FamilyOfCycles f r) := by
  rw [isEquidimensional_iff_relativeDimensionLEOn_closure, supportOfFamily_zero, closure_empty]
  exact fun x hx => hx.elim

/-- A sum of two equidimensional families is equidimensional. -/
theorem isEquidimensional_add {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) {α β : FamilyOfCycles f r} (hα : IsEquidimensional f r α)
    (hβ : IsEquidimensional f r β) : IsEquidimensional f r (α + β) := by
  rw [isEquidimensional_iff_relativeDimensionLEOn_closure] at hα hβ ⊢
  refine (hα.union hβ isClosed_closure isClosed_closure).mono ?_
  exact (closure_mono (supportOfFamily_add_subset f α β)).trans closure_union.subset

/-- The negative of an equidimensional family is equidimensional. -/
theorem isEquidimensional_neg {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) {α : FamilyOfCycles f r} (hα : IsEquidimensional f r α) :
    IsEquidimensional f r (-α) := by
  obtain ⟨W, hW, hdim⟩ := hα
  exact ⟨W, by rwa [supportOfFamily_neg], hdim⟩

/-- The group `z_equi(X/S, r)` of equidimensional relative `r`-cycles on `X/S`: the subgroup of
the group of families of `r`-cycles on the fibres of `X/S` whose members are the relative
`r`-cycles whose support is contained in a closed subset of `X` of relative dimension at most `r`
over `S`. -/
@[stacks 0H5I "the group z_equi(X/S, r) of equidimensional relative r-cycles"]
def equidimensionalRelativeCycles {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) : AddSubgroup (FamilyOfCycles f r) where
  carrier := {α | IsRelativeCycle f r α ∧ IsEquidimensional f r α}
  zero_mem' := ⟨isRelativeCycle_zero f r, isEquidimensional_zero f r⟩
  add_mem' := fun hα hβ ↦
    ⟨isRelativeCycle_add f r hα.1 hβ.1, isEquidimensional_add f r hα.2 hβ.2⟩
  neg_mem' := fun hα ↦ ⟨isRelativeCycle_neg f r hα.1, isEquidimensional_neg f r hα.2⟩

/-- Membership in the group of equidimensional relative `r`-cycles is the conjunction of the
valuative condition defining a relative `r`-cycle and of equidimensionality. -/
@[simp]
theorem mem_equidimensionalRelativeCycles {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r) :
    α ∈ equidimensionalRelativeCycles f r ↔ IsRelativeCycle f r α ∧ IsEquidimensional f r α :=
  Iff.rfl

/-- The group of equidimensional relative `r`-cycles is a subgroup of the group `z(X/S, r)` of
relative `r`-cycles. -/
theorem equidimensionalRelativeCycles_le_relativeCycles {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r : ℕ) :
    equidimensionalRelativeCycles f r ≤ relativeCycles f r :=
  fun _ hα ↦ hα.1

end Stacks.Chow

end
