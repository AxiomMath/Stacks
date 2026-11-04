module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety
public import
  StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyEquivalentDefinitions
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Separated
public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.Immersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Properness and connectedness of an open subgroup scheme off an Abel-type map

Let `G` be a group scheme over an algebraically closed field `k`, let `H ⊆ G` be an open subgroup
scheme locally of finite type over `k`, and let `a : A ⟶ G` be a morphism over `k` out of a scheme
`A` proper over `k`. Suppose that `a` carries every closed point of `A` into `H`, and that every
closed point of `H` is hit by `a`. Then `a` factors through `H` by a *surjective* morphism, so that
`H` is proper over `k` and connected when `A` is.

This is the shape of the argument of [Stacks, Tag 0BA0] for the properness of the components of
the Picard scheme of a curve: there `A` is the Hilbert scheme of points `Hilb^g_{X/k}`, `a` is the
Abel map followed by a translation into the degree-zero component, and the two hypotheses are the
facts that `𝒪(D)` has degree `g` for an effective divisor `D` of degree `g`, and that every
invertible module of degree `g` has a nonzero section.

The proof only uses that `k`-points are closed points (`AlgebraicGeometry.pointEquivClosedPoint`)
and that a scheme locally of finite type over a field is a Jacobson space, in which an open set
containing every closed point, or a closed set containing every closed point, is everything.

## Main results

* `AlgebraicGeometry.isSeparated_hom_of_groupScheme_over_field`: the structure morphism of a group
  scheme over a field is separated.
* `AlgebraicGeometry.OpenSubgroupScheme.exists_lift_surjective_of_isProper`: the factorization of
  `a` through `H`, surjective.
* `AlgebraicGeometry.OpenSubgroupScheme.isProper_carrier_of_isProper_of_closedPoints` and
  `AlgebraicGeometry.OpenSubgroupScheme.connectedSpace_carrier_of_closedPoints`: `H` is proper
  over `k` and connected.
* `AlgebraicGeometry.OpenSubgroupScheme.isAbelianVariety_carrier`: Remark 0H2U for the carrier
  of an open subgroup scheme.
* `AlgebraicGeometry.OpenSubgroupScheme.isAbelianVariety_carrier_of_closedPoints`: if moreover `H`
  is smooth of relative dimension `n` and `A` is connected, `H` is an abelian variety of
  dimension `n`.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 047L](https://stacks.math.columbia.edu/tag/047L)
* [Stacks Project, Tag 005U](https://stacks.math.columbia.edu/tag/005U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 047L, the relative form.** The structure morphism of a group scheme
over a field is separated: its identity section is a closed immersion, because a section of a
morphism to the spectrum of a field always is. -/
@[sga "3 VIA 0.2" "special case",
  sga "3 VIA 0.3" "special case",
  sga "3 VIB 1.1" "(2), special case",
  sga "3 VIB 6.2.4",
  sga "3 VIII 6.5" "partial"]
theorem isSeparated_hom_of_groupScheme_over_field {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k)))) : IsSeparated G.X.hom := by
  let : GrpObj (Over.mk G.X.hom) :=
    GrpObj.ofIso (show G.X ≅ Over.mk G.X.hom from Over.isoMk (Iso.refl _))
  exact (isSeparated_iff_isClosedImmersion_one G.X.hom).2 inferInstance

/-- In a Jacobson space, an open set containing every closed point is the whole space. -/
theorem eq_univ_of_isOpen_of_closedPoints_subset {Y : Type*} [TopologicalSpace Y]
    [JacobsonSpace Y] {U : Set Y} (hU : IsOpen U) (h : ∀ y : Y, IsClosed {y} → y ∈ U) :
    U = Set.univ := by
  by_contra hne
  obtain ⟨y, hyU, hy⟩ := nonempty_inter_closedPoints
    (Set.nonempty_compl.2 hne) hU.isClosed_compl.isLocallyClosed
  exact hyU (h y hy)

/-- In a Jacobson space, a closed set containing every closed point is the whole space. -/
theorem eq_univ_of_isClosed_of_closedPoints_subset {Y : Type*} [TopologicalSpace Y]
    [JacobsonSpace Y] {Z : Set Y} (hZ : IsClosed Z) (h : ∀ y : Y, IsClosed {y} → y ∈ Z) :
    Z = Set.univ := by
  by_contra hne
  obtain ⟨y, hyZ, hy⟩ := nonempty_inter_closedPoints
    (Set.nonempty_compl.2 hne) hZ.isOpen_compl.isLocallyClosed
  exact hyZ (h y hy)

namespace OpenSubgroupScheme

/-- An open subgroup scheme of a group scheme over a field is closed (Tag 047T: an immersion of
group schemes over a field is a closed immersion). -/
@[sga "3 VIB 1.4.2" "special case",
  sga "3 VIB 6.2.5" "(iii), special case",
  sga "3 VIII 6.7" "special case"]
theorem isClosed_range_ι {k : Type u} [Field k] {G : Grp (Over (Spec (.of k)))}
    (H : OpenSubgroupScheme G) : IsClosed (Set.range H.ι.hom.hom.left) := by
  have : IsOpenImmersion H.ι.hom.hom.left := H.isOpenImmersion
  have : IsClosedImmersion H.ι.hom.hom.left := isClosedImmersion_of_isImmersion H.ι
  exact H.ι.hom.hom.left.isClosedEmbedding.isClosed_range

/-- A morphism from a connected scheme which sends one point into an open subgroup scheme sends
every point into it, the open subgroup scheme being open and closed. -/
theorem range_subset_range_ι_of_connectedSpace {k : Type u} [Field k]
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G) {A : Scheme.{u}}
    [ConnectedSpace A] (a : A ⟶ G.X.left) (a₀ : A) (ha₀ : a a₀ ∈ Set.range H.ι.hom.hom.left) :
    Set.range a ⊆ Set.range H.ι.hom.hom.left := by
  have : IsOpenImmersion H.ι.hom.hom.left := H.isOpenImmersion
  have hcl : IsClopen (a ⁻¹' Set.range H.ι.hom.hom.left) :=
    ⟨H.isClosed_range_ι.preimage a.continuous,
      H.ι.hom.hom.left.isOpenEmbedding.isOpen_range.preimage a.continuous⟩
  exact Set.preimage_eq_univ_iff.1 (hcl.eq_univ ⟨a₀, ha₀⟩)

/-- **Remark 0H2U applied to an open subgroup scheme**: an
open subgroup scheme whose carrier is proper, smooth and connected over `k` is an abelian
variety, by the weakest of the sixteen choices of the remark. -/
theorem isAbelianVariety_carrier {k : Type u} [Field k]
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G)
    (hproper : IsProper H.carrier.X.hom) (hsmooth : Smooth H.carrier.X.hom)
    (hconn : ConnectedSpace H.carrier.X.left) :
    IsAbelianVariety k H.carrier.X :=
  isAbelianVariety_of_choices k H.carrier.X (Or.inr hproper)
    (Or.inr (Or.inr (Or.inr hconn))) (Or.inl hsmooth)

/-- The carrier of an open subgroup scheme of a group scheme smooth of relative dimension `n` is
smooth of relative dimension `n`. -/
theorem smoothOfRelativeDimension_carrier {k : Type u} [Field k]
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G) (n : ℕ)
    [SmoothOfRelativeDimension n G.X.hom] : SmoothOfRelativeDimension n H.carrier.X.hom := by
  have : IsOpenImmersion H.ι.hom.hom.left := H.isOpenImmersion
  rw [← H.ι.hom.hom.w]
  simpa using (inferInstance :
    SmoothOfRelativeDimension (0 + n) (H.ι.hom.hom.left ≫ G.X.hom))

/-- The dimension of an open subgroup scheme which is smooth of relative dimension `n` over a
field is `n` (it is nonempty, containing the identity). -/
theorem abelianVarietyDimension_carrier_of_smoothOfRelativeDimension {k : Type u} [Field k]
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G) (n : ℕ)
    [SmoothOfRelativeDimension n H.carrier.X.hom] :
    Stacks.Groupoids.abelianVarietyDimension H.carrier.X = n := by
  have : Nonempty H.carrier.X.left :=
    ⟨(η[H.carrier.X] : 𝟙_ (Over (Spec (.of k))) ⟶ H.carrier.X).left
      (IsLocalRing.closedPoint k)⟩
  rw [Stacks.Groupoids.abelianVarietyDimension,
    topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field n H.carrier.X.hom]
  rfl

/-- The dimension of a nonempty open subgroup scheme of a group scheme smooth of relative
dimension `n` over a field is `n`. -/
theorem abelianVarietyDimension_carrier {k : Type u} [Field k]
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G) (n : ℕ)
    [SmoothOfRelativeDimension n G.X.hom] :
    Stacks.Groupoids.abelianVarietyDimension H.carrier.X = n :=
  have := H.smoothOfRelativeDimension_carrier n
  H.abelianVarietyDimension_carrier_of_smoothOfRelativeDimension n


variable {k : Type u} [Field k] [IsAlgClosed k] {G : Grp (Over (Spec (.of k)))}
  (H : OpenSubgroupScheme G)

omit [IsAlgClosed k] in
/-- The carrier of an open subgroup scheme of a group scheme locally of finite type is locally of
finite type. -/
theorem locallyOfFiniteType_carrier [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType H.carrier.X.hom := by
  have : IsOpenImmersion H.ι.hom.hom.left := H.isOpenImmersion
  rw [← H.ι.hom.hom.w]
  infer_instance

omit [IsAlgClosed k] in
/-- **The Abel-type map factors surjectively through the open subgroup scheme.** Let `a : A ⟶ G`
be a morphism over `k` out of a scheme proper over `k`, carrying every closed point of `A` into
`H` and hitting every closed point of `H`. Then `a` factors through `H` by a surjective
morphism. -/
theorem exists_lift_surjective_of_isProper [LocallyOfFiniteType H.carrier.X.hom] {A : Scheme.{u}}
    (sA : A ⟶ Spec (.of k)) [IsProper sA] (a : A ⟶ G.X.left) (ha : a ≫ G.X.hom = sA)
    (hin : ∀ x : A, IsClosed {x} → a x ∈ Set.range H.ι.hom.hom.left)
    (hsurj : ∀ y : H.carrier.X.left, IsClosed {y} → H.ι.hom.hom.left y ∈ Set.range a) :
    ∃ a' : A ⟶ H.carrier.X.left, a' ≫ H.ι.hom.hom.left = a ∧ a' ≫ H.carrier.X.hom = sA ∧
      Surjective a' := by
  have : IsOpenImmersion H.ι.hom.hom.left := H.isOpenImmersion
  have : JacobsonSpace A := LocallyOfFiniteType.jacobsonSpace sA
  have : JacobsonSpace H.carrier.X.left := LocallyOfFiniteType.jacobsonSpace H.carrier.X.hom
  have : IsSeparated H.carrier.X.hom := isSeparated_hom_of_groupScheme_over_field H.carrier
  set i := H.ι.hom.hom.left
  have hι : i ≫ G.X.hom = H.carrier.X.hom := H.ι.hom.hom.w
  -- every point of `A` lands in `H`
  have hrange : Set.range a ⊆ Set.range i := by
    have hopen : IsOpen (a ⁻¹' Set.range i) := i.isOpenEmbedding.isOpen_range.preimage a.continuous
    exact Set.preimage_eq_univ_iff.1 (eq_univ_of_isOpen_of_closedPoints_subset hopen hin)
  set a' := IsOpenImmersion.lift i a hrange
  have hfac : a' ≫ i = a := IsOpenImmersion.lift_fac i a hrange
  have hover : a' ≫ H.carrier.X.hom = sA := by rw [← hι, ← Category.assoc, hfac, ha]
  refine ⟨a', hfac, hover, ?_⟩
  -- the lift is closed, and its range contains every closed point of `H`
  have : IsProper (a' ≫ H.carrier.X.hom) := by rw [hover]; infer_instance
  have : IsProper a' := IsProper.of_comp a' H.carrier.X.hom
  have hclosed : IsClosed (Set.range a') := a'.isClosedMap.isClosed_range
  have huniv := eq_univ_of_isClosed_of_closedPoints_subset hclosed (fun y hy => by
    obtain ⟨x, hx⟩ := hsurj y hy
    refine ⟨x, i.isOpenEmbedding.injective ?_⟩
    rw [← hx, ← hfac]
    rfl)
  exact ⟨fun y => (Set.eq_univ_iff_forall.1 huniv y : _)⟩

omit [IsAlgClosed k] in
/-- **Stacks Project, Tag 0BA0, properness of a degree component, off an Abel-type map.** With
`a : A ⟶ G` as in `AlgebraicGeometry.OpenSubgroupScheme.exists_lift_surjective_of_isProper`, the
open subgroup scheme `H` is proper over `k`: universal closedness descends along the surjective
factorization, separatedness holds for every group scheme over a field, and `H` is locally of
finite type as an open of `G`. -/
theorem isProper_carrier_of_isProper_of_closedPoints [LocallyOfFiniteType H.carrier.X.hom]
    {A : Scheme.{u}} (sA : A ⟶ Spec (.of k)) [IsProper sA] (a : A ⟶ G.X.left)
    (ha : a ≫ G.X.hom = sA)
    (hin : ∀ x : A, IsClosed {x} → a x ∈ Set.range H.ι.hom.hom.left)
    (hsurj : ∀ y : H.carrier.X.left, IsClosed {y} → H.ι.hom.hom.left y ∈ Set.range a) :
    IsProper H.carrier.X.hom := by
  obtain ⟨a', -, hover, hs⟩ := H.exists_lift_surjective_of_isProper sA a ha hin hsurj
  have := hs
  have : IsSeparated H.carrier.X.hom := isSeparated_hom_of_groupScheme_over_field H.carrier
  have : UniversallyClosed (a' ≫ H.carrier.X.hom) := by rw [hover]; infer_instance
  have : UniversallyClosed H.carrier.X.hom := UniversallyClosed.of_comp_surjective a' _
  exact ⟨⟩

omit [IsAlgClosed k] in
/-- **Stacks Project, Tag 0BA0, connectedness of a degree component, off an Abel-type map.** With
`a : A ⟶ G` as in `AlgebraicGeometry.OpenSubgroupScheme.exists_lift_surjective_of_isProper` and
`A` connected, the open subgroup scheme `H` is connected, being the image of `A`. -/
theorem connectedSpace_carrier_of_closedPoints [LocallyOfFiniteType H.carrier.X.hom]
    {A : Scheme.{u}} [ConnectedSpace A] (sA : A ⟶ Spec (.of k)) [IsProper sA]
    (a : A ⟶ G.X.left) (ha : a ≫ G.X.hom = sA)
    (hin : ∀ x : A, IsClosed {x} → a x ∈ Set.range H.ι.hom.hom.left)
    (hsurj : ∀ y : H.carrier.X.left, IsClosed {y} → H.ι.hom.hom.left y ∈ Set.range a) :
    ConnectedSpace H.carrier.X.left := by
  obtain ⟨a', -, -, hs⟩ := H.exists_lift_surjective_of_isProper sA a ha hin hsurj
  have := hs
  exact a'.surjective.connectedSpace a'.continuous

/-- **Stacks Project, Tag 0BA0, for the degree-zero component: an abelian variety of dimension
`n`, off an Abel-type map.** Let `G` be a group scheme over an algebraically closed field `k`,
`H ⊆ G` an open subgroup scheme smooth of relative dimension `n` over `k`, and `a : A ⟶ G` a
morphism over `k` out of a scheme `A` proper and connected over `k`, sending one point of `A` into
`H` and hitting every closed point of `H`. Then `H` is an abelian variety of dimension `n`. -/
theorem isAbelianVariety_carrier_of_closedPoints (n : ℕ)
    [SmoothOfRelativeDimension n H.carrier.X.hom]
    {A : Scheme.{u}} [ConnectedSpace A] (sA : A ⟶ Spec (.of k)) [IsProper sA]
    (a : A ⟶ G.X.left) (ha : a ≫ G.X.hom = sA) (a₀ : A)
    (ha₀ : a a₀ ∈ Set.range H.ι.hom.hom.left)
    (hsurj : ∀ y : H.carrier.X.left, IsClosed {y} → H.ι.hom.hom.left y ∈ Set.range a) :
    IsAbelianVariety k H.carrier.X ∧
      Stacks.Groupoids.abelianVarietyDimension H.carrier.X = n := by
  have : Smooth H.carrier.X.hom := SmoothOfRelativeDimension.smooth n _
  have hin : ∀ x : A, IsClosed {x} → a x ∈ Set.range H.ι.hom.hom.left := fun x _ =>
    H.range_subset_range_ι_of_connectedSpace a a₀ ha₀ ⟨x, rfl⟩
  exact ⟨H.isAbelianVariety_carrier
      (H.isProper_carrier_of_isProper_of_closedPoints sA a ha hin hsurj)
      (SmoothOfRelativeDimension.smooth n _)
      (H.connectedSpace_carrier_of_closedPoints sA a ha hin hsurj),
    H.abelianVarietyDimension_carrier_of_smoothOfRelativeDimension n⟩

end OpenSubgroupScheme

end AlgebraicGeometry

end
