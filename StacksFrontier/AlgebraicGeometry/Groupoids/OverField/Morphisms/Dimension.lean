module

public import Mathlib.Data.ENat.Monoid
public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.RingTheory.KrullDimension.Field
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberDimension
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionFiber
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.Topology.Dimension.Equidimensional

/-!
# Dimension of the arrow scheme of a groupoid scheme over a field

Let a groupoid scheme have object scheme the spectrum of a field and source and target
morphisms locally of finite type. Then its arrow scheme has the same local dimension at every
point: any two points become, after one field extension, points of two base changes of the
arrow scheme along the source which an isomorphism over that extension carries to one another,
and the local dimension of a scheme over a one-point scheme is the local dimension of the
fibre, which is insensitive to base change. Consequently the arrow scheme is equidimensional,
its dimension is its local dimension at every point, and at a closed point that dimension is
the Krull dimension of the local ring.

The transcendence degree of the residue field at a point of the arrow scheme is likewise the
same over the residue field of the source and over that of the target. This is a statement
about an arbitrary pair of morphisms locally of finite type into the spectrum of a field, and
is proved in that generality: the dimension formula for a fibre expresses the local dimension
of the fibre as the Krull dimension of its local ring plus that transcendence degree, and over
a one-point base the fibre is the whole scheme, so the two transcendence degrees satisfy the
same equation with the same finite left-hand side.

## Main results

* `AlgebraicGeometry.trdeg_residueField_eq_of_target_isSpec_field`: the transcendence degree of
  the residue field at a point over the residue field of its image does not depend on which
  morphism to the spectrum of a field is used.
* `AlgebraicGeometry.GroupoidScheme.topologicalKrullDimAt_arrows_eq`: the local dimension of
  the arrow scheme is independent of the point.
* `AlgebraicGeometry.GroupoidScheme.topologicalKrullDim_arrows_eq_topologicalKrullDimAt`: the
  dimension of the arrow scheme is its local dimension at every point.
* `AlgebraicGeometry.GroupoidScheme.topologicalKrullDim_arrows_eq_ringKrullDim_stalk`: at a
  closed point it is the Krull dimension of the local ring.
* `AlgebraicGeometry.GroupoidScheme.equidimensional_arrows`: the arrow scheme is
  equidimensional.

## Implementation notes

That the object scheme is the spectrum of a field is expressed by an isomorphism of schemes,
and the finite type hypotheses are imposed on the underlying morphisms of the source and target
of the groupoid scheme rather than on their images in the slice category.

## References

* [Stacks Project, Tag 04LU](https://stacks.math.columbia.edu/tag/04LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-! ### Dimension over a one-point base -/

/-- Over a one-point target the fibre of a morphism is the whole source, so the local
dimension of the source at a point is the local dimension of the fibre there. -/
theorem topologicalKrullDimAt_eq_fiber_of_subsingleton {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Subsingleton Y] (x : X) :
    topologicalKrullDimAt X x =
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := by
  have h : (f : X → Y) ⁻¹' {f x} = Set.univ :=
    Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
  let e := (f.fiberHomeo (f x)).trans ((Homeomorph.setCongr h).trans (Homeomorph.Set.univ X))
  have he : e (f.asFiber x) = x := f.fiberι_asFiber x
  refine ((topologicalKrullDimAt_eq_of_homeomorph e (f.asFiber x)).trans ?_).symm
  exact congrArg (fun z => topologicalKrullDimAt X z) he

/-- Base change along a morphism of one-point schemes does not change the local dimension: over
a one-point base both the source and its base change are their own fibres, and the local
dimension of a fibre is unchanged by base change. -/
theorem topologicalKrullDimAt_eq_of_isPullback_of_subsingleton {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (hsq : IsPullback g' f' f g)
    [LocallyOfFiniteType f] [Subsingleton S] [Subsingleton S'] (x' : X') :
    topologicalKrullDimAt X (g' x') = topologicalKrullDimAt X' x' :=
  (topologicalKrullDimAt_eq_fiber_of_subsingleton f (g' x')).trans
    ((topologicalKrullDimAt_fiber_eq_of_isPullback hsq x').symm.trans
      (topologicalKrullDimAt_eq_fiber_of_subsingleton f' x').symm)

/-! ### Transcendence degrees over the spectrum of a field -/

/-- A scheme isomorphic to the spectrum of a field is the spectrum of the residue field at any
of its points. -/
private theorem isIso_fromSpecResidueField {Y : Scheme.{u}} {k : Type u} [Field k]
    (e : Y ≅ Spec (.of k)) (y : Y) : IsIso (Y.fromSpecResidueField y) := by
  have : Subsingleton Y := ⟨fun _ _ => e.hom.homeomorph.injective (Subsingleton.elim _ _)⟩
  have hclosed : IsClosed (Set.range (Y.fromSpecResidueField y)) := by
    rw [Scheme.range_fromSpecResidueField, (Set.singleton_nonempty y).eq_univ]
    exact isClosed_univ
  have : IsClosedImmersion (Y.fromSpecResidueField y) :=
    IsClosedImmersion.of_isPreimmersion _ hclosed
  have : Surjective (Y.fromSpecResidueField y) :=
    ⟨fun z => ⟨IsLocalRing.closedPoint (Y.residueField y), Subsingleton.elim _ z⟩⟩
  have : IsReduced Y := ObjectProperty.prop_of_iso IsReduced e.symm inferInstance
  exact isIso_of_isClosedImmersion_of_surjective _

/-- For a morphism into a scheme isomorphic to the spectrum of a field, the fibre inclusion at
any point is an isomorphism. -/
private theorem isIso_fiberι_of_target_isSpec_field {X Y : Scheme.{u}} {k : Type u} [Field k]
    (e : Y ≅ Spec (.of k)) (f : X ⟶ Y) (x : X) : IsIso (f.fiberι (f x)) := by
  have : IsIso (Y.fromSpecResidueField (f x)) := isIso_fromSpecResidueField e (f x)
  change IsIso (pullback.fst f (Y.fromSpecResidueField (f x)))
  infer_instance

/-- For a morphism into a scheme isomorphic to the spectrum of a field, the fibre inclusion is
an isomorphism, so the local dimension of the fibre is the local dimension of the source. -/
private theorem topologicalKrullDimAt_fiber_eq_of_target_isSpec_field {X Y : Scheme.{u}}
    {k : Type u} [Field k] (e : Y ≅ Spec (.of k)) (f : X ⟶ Y) (x : X) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = topologicalKrullDimAt X x := by
  have := isIso_fiberι_of_target_isSpec_field e f x
  refine (topologicalKrullDimAt_eq_of_homeomorph
    (Scheme.homeoOfIso (asIso (f.fiberι (f x)))) (f.asFiber x)).trans ?_
  exact congrArg (fun z => topologicalKrullDimAt X z) (f.fiberι_asFiber x)

/-- For a morphism into a scheme isomorphic to the spectrum of a field, the local ring of the
fibre at a point is the local ring of the source there. -/
private theorem ringKrullDim_stalk_fiber_eq_of_target_isSpec_field {X Y : Scheme.{u}}
    {k : Type u} [Field k] (e : Y ≅ Spec (.of k)) (f : X ⟶ Y) (x : X) :
    ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) =
      ringKrullDim (X.presheaf.stalk x) := by
  have := isIso_fiberι_of_target_isSpec_field e f x
  have hd := (ringKrullDim_eq_of_ringEquiv
    (asIso ((f.fiberι (f x)).stalkMap (f.asFiber x))).commRingCatIsoToRingEquiv).symm
  rw [f.fiberι_asFiber] at hd
  exact hd

/-- The residue field extension at a point of a morphism locally of finite type has finite
transcendence degree. -/
private theorem trdeg_residueField_lt_aleph0 {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X) :
    letI : Algebra (Y.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Algebra.trdeg (Y.residueField (f x)) (X.residueField x) < Cardinal.aleph0 := by
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have : Algebra.EssFiniteType (Y.residueField (f x)) (X.residueField x) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap (f := f) x)
  exact trdeg_lt_aleph0 _ _

/-- **Stacks Project, Tag 04LU.** The transcendence degree of the residue field at a point of a
scheme over the residue field of its image does not depend on which morphism locally of finite
type to the spectrum of a field is used. -/
@[stacks 04LU "transcendence_degrees"]
theorem trdeg_residueField_eq_of_target_isSpec_field {X Y : Scheme.{u}} {k : Type u} [Field k]
    (e : Y ≅ Spec (.of k)) (f g : X ⟶ Y) [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (x : X) :
    letI : Algebra (Y.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    letI : Algebra (Y.residueField (g x)) (X.residueField x) :=
      (g.residueFieldMap x).hom.toAlgebra
    Algebra.trdeg (Y.residueField (f x)) (X.residueField x) =
      Algebra.trdeg (Y.residueField (g x)) (X.residueField x) := by
  have hf := by
    let := (f.residueFieldMap x).hom.toAlgebra
    exact topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg f x
  have hg := by
    let := (g.residueFieldMap x).hom.toAlgebra
    exact topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg g x
  rw [topologicalKrullDimAt_fiber_eq_of_target_isSpec_field e f x,
    ringKrullDim_stalk_fiber_eq_of_target_isSpec_field e f x] at hf
  rw [topologicalKrullDimAt_fiber_eq_of_target_isSpec_field e g x,
    ringKrullDim_stalk_fiber_eq_of_target_isSpec_field e g x] at hg
  have hsum := hf.symm.trans hg
  generalize hd : ringKrullDim (X.presheaf.stalk x) = d at hsum
  have hdTop : d ≠ ⊤ := by
    have : IsLocallyNoetherian Y := isLocallyNoetherian_of_isOpenImmersion e.hom
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    exact hd ▸ ringKrullDim_ne_top (R := X.presheaf.stalk x)
  have hdBot : d ≠ ⊥ := fun hdbot =>
    (zero_ne_one : (0 : X.presheaf.stalk x) ≠ 1)
      ((ringKrullDim_eq_bot_iff_subsingleton.mp (hd.trans hdbot)).elim _ _)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d = m := by
    cases d with
    | bot => exact (hdBot rfl).elim
    | coe a =>
      have ha : a ≠ ⊤ := fun ha =>
        hdTop (congrArg (fun z : ℕ∞ => (z : WithBot ℕ∞)) ha)
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp ha
      exact ⟨m, congrArg (fun z : ℕ∞ => (z : WithBot ℕ∞)) hm.symm⟩
  rw [hm] at hsum
  exact (Cardinal.toENat_eq_iff_of_le_aleph0
    (le_of_lt (trdeg_residueField_lt_aleph0 f x))
    (le_of_lt (trdeg_residueField_lt_aleph0 g x))).mp
    (WithBot.coe_injective (ENat.WithBot.natCast_add_cancel.mp hsum))

namespace GroupoidScheme

/-! ### Dimension of the arrow scheme -/

/-- The local dimension of the arrow scheme of a groupoid scheme whose object scheme is the
spectrum of a field is independent of the point, provided both structure morphisms are locally
of finite type. -/
theorem topologicalKrullDimAt_arrows_eq {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u}
    [Field k] (e : G.objects.left ≅ Spec (.of k)) [LocallyOfFiniteType G.source.left]
    [LocallyOfFiniteType G.target.left] (r r' : G.arrows.left) :
    topologicalKrullDimAt G.arrows.left r = topologicalKrullDimAt G.arrows.left r' := by
  have hex := G.exists_fieldExtension_sourceFiber_iso_mapping_points k e r r'
  dsimp only at hex
  obtain ⟨k', _, α, β, r₁, r₂, φ, hφ, hr₁, hr₂⟩ := hex
  have h₁ := topologicalKrullDimAt_eq_of_isPullback_of_subsingleton
    (IsPullback.of_hasPullback (G.source.left ≫ e.hom)
      (Spec.map (CommRingCat.ofHom (@algebraMap k k' _ _ α)))) r₁
  have h₂ := topologicalKrullDimAt_eq_of_isPullback_of_subsingleton
    (IsPullback.of_hasPullback (G.source.left ≫ e.hom)
      (Spec.map (CommRingCat.ofHom (@algebraMap k k' _ _ β)))) r₂
  rw [← hr₁, ← hr₂, h₁, h₂]
  refine (topologicalKrullDimAt_eq_of_homeomorph
    (Scheme.homeoOfIso ((Over.forget (Spec (.of k'))).mapIso φ)) r₁).trans ?_
  exact congrArg (fun z => topologicalKrullDimAt _ z) hφ

/-- **Stacks Project, Tag 04LU.** The dimension of the arrow scheme of a groupoid scheme whose
object scheme is the spectrum of a field is its local dimension at every point, provided both
structure morphisms are locally of finite type. -/
@[stacks 04LU "dimension_at_every_point"]
theorem topologicalKrullDim_arrows_eq_topologicalKrullDimAt {S : Scheme.{u}}
    (G : GroupoidScheme S) {k : Type u} [Field k] (e : G.objects.left ≅ Spec (.of k))
    [LocallyOfFiniteType G.source.left] [LocallyOfFiniteType G.target.left]
    (r : G.arrows.left) :
    topologicalKrullDim G.arrows.left = topologicalKrullDimAt G.arrows.left r := by
  have : Nonempty G.arrows.left := ⟨r⟩
  simp_rw [topologicalKrullDim_eq_iSup_localKrullDim,
    ← topologicalKrullDimAt_eq_localKrullDim, topologicalKrullDimAt_arrows_eq G e _ r,
    iSup_const]

/-- **Stacks Project, Tag 04LU.** At a closed point of the arrow scheme of a groupoid scheme
whose object scheme is the spectrum of a field, the dimension of the arrow scheme is the Krull
dimension of the local ring. -/
@[stacks 04LU "dimension_at_closed_point"]
theorem topologicalKrullDim_arrows_eq_ringKrullDim_stalk {S : Scheme.{u}}
    (G : GroupoidScheme S) {k : Type u} [Field k] (e : G.objects.left ≅ Spec (.of k))
    [LocallyOfFiniteType G.source.left] [LocallyOfFiniteType G.target.left]
    (r : G.arrows.left) (hr : IsClosed ({r} : Set G.arrows.left)) :
    topologicalKrullDim G.arrows.left = ringKrullDim (G.arrows.left.presheaf.stalk r) :=
  (topologicalKrullDim_arrows_eq_topologicalKrullDimAt G e r).trans
    (topologicalKrullDimAt_eq_krullDimOfRing_stalk k G.arrows.left
      (G.source.left ≫ e.hom) r hr)

/-- **Stacks Project, Tag 04LU.** The arrow scheme of a groupoid scheme whose object scheme is
the spectrum of a field is equidimensional, provided both structure morphisms are locally of
finite type. -/
@[stacks 04LU "equidimensional"]
theorem equidimensional_arrows {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k]
    (e : G.objects.left ≅ Spec (.of k)) [LocallyOfFiniteType G.source.left]
    [LocallyOfFiniteType G.target.left] :
    Equidimensional G.arrows.left := by
  have dim (Z : Set G.arrows.left) (hZ : Z ∈ irreducibleComponents G.arrows.left) :
      topologicalKrullDim Z = topologicalKrullDimAt G.arrows.left hZ.1.genericPoint := by
    obtain ⟨C, hC, hmem, hdim⟩ :=
      exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k
        G.arrows.left (G.source.left ≫ e.hom) hZ.1.genericPoint
    have hsub : Z ⊆ C :=
      ((hZ.1.isGenericPoint_genericPoint
        (isClosed_of_mem_irreducibleComponents Z hZ)).mem_closed_set_iff
          (isClosed_of_mem_irreducibleComponents C hC)).mp hmem
    exact (Set.Subset.antisymm hsub (hZ.2 hC.1 hsub)) ▸ hdim
  intro Z hZ W hW
  simpa only [dim Z hZ, dim W hW] using topologicalKrullDimAt_arrows_eq G e _ _

end GroupoidScheme

end AlgebraicGeometry

end
