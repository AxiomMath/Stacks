module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RestrictionProperties
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.StabilizerDimension
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionStabilizer

/-!
# Charts and dimensions at a finite type point of a groupoid scheme

Fix a groupoid scheme `(U, R, s, t, c, e, i)` over a base and a finite type point `u` of `U`.
This file provides the two local pieces of data that the slicing construction starts from: a
pair of affine charts adapted to `u`, and the dimension of the restriction of the groupoid to
the residue field at `u`.

The charts are an affine open `Spec(A) ⊆ U` containing `u` as a closed point, together with an
affine open `Spec(B) ⊆ R` containing the identity arrow `e(u)` and carried by both `s` and `t`
into `Spec(A)`; the latter condition says exactly that `j = (t, s)` maps `Spec(B)` into the open
`Spec(A) × Spec(A)` of `U × U` over the base.

The dimension statement concerns the restriction `R''` of `R` along
`Spec(κ(u)) ⟶ U`. Its arrow scheme, and the local ring of that arrow scheme at the identity
arrow, both have the dimension of the stabilizer fibre `G_u`.

Finally, cutting an affine chart by a section produces the slice: for any section `f` over
`Spec(A)` vanishing at `u`, the scheme `Spec(A/fA)` maps to `U` by an immersion locally of
finite presentation whose image contains `u`.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_affineOpens_of_isFiniteTypePoint`: the pair of
  affine charts.
* `AlgebraicGeometry.GroupoidScheme.topologicalKrullDim_restrictedArrows_eq_stabilizerFiber`:
  the arrow scheme of the restriction to the residue field has the dimension of `G_u`.
* `AlgebraicGeometry.GroupoidScheme.ringKrullDim_stalk_restrictedArrows_eq_stabilizerFiber`:
  the local ring of that arrow scheme at the identity arrow has the dimension of `G_u`.
* `AlgebraicGeometry.GroupoidScheme.exists_slice_of_mem_primeIdealOf`: cutting an affine chart
  by a section vanishing at the point gives an immersion locally of finite presentation.

## Implementation notes

The restriction to the residue field is taken along `Scheme.fromSpecResidueField`, viewed as a
morphism to the object scheme over the base through `Over.homMk`; this is the shape in which the
restriction lemmas for locally finite type morphisms and for the stabilizer are stated, so the
two `let` bindings in the statements below name exactly their arguments.

## References

* [Stacks Project, Tag 0461](https://stacks.math.columbia.edu/tag/0461)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- At a finite type point `u` of the object scheme of a groupoid scheme there is an affine open
`A` containing `u` as a closed point, together with an affine open `B` of the arrow scheme
containing the identity arrow at `u` and carried into `A` by both the source and the target.

The last two conditions say that `(t, s)` maps `B` into the open `A × A` of the fibre square of
the object scheme over the base. -/
public theorem exists_affineOpens_of_isFiniteTypePoint {S : Scheme.{u}} (G : GroupoidScheme S)
    {u : G.objects.left} (hu : IsFiniteTypePoint u) :
    ∃ (A : G.objects.left.affineOpens) (B : G.arrows.left.affineOpens) (huA : u ∈ A.1),
      IsClosed ({⟨u, huA⟩} : Set (A.1 : Set G.objects.left)) ∧
        G.identity.left u ∈ B.1 ∧
        B.1 ≤ G.source.left ⁻¹ᵁ A.1 ∧ B.1 ≤ G.target.left ⁻¹ᵁ A.1 := by
  classical
  have hmem : u ∈ G.objects.left.finiteTypePoints := hu
  rw [G.objects.left.finiteTypePoints_eq_iUnion_affineOpens] at hmem
  obtain ⟨A, hA⟩ := Set.mem_iUnion.mp hmem
  obtain ⟨x, hxc, hxu⟩ := hA
  have huA : u ∈ A.1 := hxu ▸ x.2
  have hxeq : (⟨u, huA⟩ : (A.1 : Set G.objects.left)) = x := Subtype.ext hxu.symm
  have hsrc : G.source.left (G.identity.left u) = u := by
    simpa using congrArg (fun f : G.objects.left ⟶ G.objects.left => f u)
      (identity_left_comp_source_left G)
  have htgt : G.target.left (G.identity.left u) = u := by
    simpa using congrArg (fun f : G.objects.left ⟶ G.objects.left => f u)
      (identity_left_comp_target_left G)
  obtain ⟨W, hW, heW, hWV⟩ := exists_isAffineOpen_mem_and_subset
    (x := G.identity.left u)
    (U := G.source.left ⁻¹ᵁ A.1 ⊓ G.target.left ⁻¹ᵁ A.1)
    ⟨by simpa [hsrc] using huA, by simpa [htgt] using huA⟩
  refine ⟨A, ⟨W, hW⟩, huA, ?_, heW, ?_, ?_⟩
  · rw [hxeq]
    exact mem_closedPoints_iff.mp hxc
  · exact le_trans hWV inf_le_left
  · exact le_trans hWV inf_le_right

/-- The object scheme of the restriction of a groupoid scheme to the residue field at a finite
type point is that spectrum, and the restricted source and target are locally of finite type. -/
private theorem exists_iso_spec_residueField_restrict {S : Scheme.{u}} (G : GroupoidScheme S)
    [LocallyOfFiniteType G.source.left] [LocallyOfFiniteType G.target.left]
    {u : G.objects.left} (hu : IsFiniteTypePoint u) :
    let g : Spec (G.objects.left.residueField u) ⟶ G.objects.left :=
      G.objects.left.fromSpecResidueField u
    let g' : Over.mk (g ≫ G.objects.hom) ⟶ G.objects := Over.homMk g
    ∃ _ : (GroupoidScheme.restrict G g').groupoid.objects.left ≅
        Spec (.of (G.objects.left.residueField u)),
      LocallyOfFiniteType (GroupoidScheme.restrict G g').groupoid.source.left ∧
        LocallyOfFiniteType (GroupoidScheme.restrict G g').groupoid.target.left := by
  intro g g'
  have : LocallyOfFiniteType g := hu.1
  exact ⟨eqToIso (congrArg Over.left (GroupoidScheme.restrict G g').objects_eq),
    restrictionSource_locallyOfFiniteType G g, restrictionTarget_locallyOfFiniteType G g⟩

/-- The arrow scheme of the restriction of a groupoid scheme to the residue field at a finite
type point has the dimension of the stabilizer fibre at that point.

The restricted groupoid lives over the spectrum of a field, so its arrow scheme and its
stabilizer have the same dimension; and the stabilizer of a restriction is the base change of
the original stabilizer, which over the residue field at `u` is the fibre `G_u`. -/
public theorem topologicalKrullDim_restrictedArrows_eq_stabilizerFiber {S : Scheme.{u}}
    (G : GroupoidScheme S) [LocallyOfFiniteType G.source.left]
    [LocallyOfFiniteType G.target.left] {u : G.objects.left} (hu : IsFiniteTypePoint u) :
    let g : Spec (G.objects.left.residueField u) ⟶ G.objects.left :=
      G.objects.left.fromSpecResidueField u
    let g' : Over.mk (g ≫ G.objects.hom) ⟶ G.objects := Over.homMk g
    topologicalKrullDim (GroupoidScheme.restrict G g').groupoid.arrows.left =
      topologicalKrullDim ((stabilizer G).hom.fiber u) := by
  intro g g'
  obtain ⟨e, _, _⟩ := exists_iso_spec_residueField_restrict G hu
  rw [topologicalKrullDim_arrows_eq_stabilizer (GroupoidScheme.restrict G g').groupoid
    e]
  let e₁ := (Over.forget _).mapIso (restrictStabilizerIso G g)
  let e₂ := pullbackSymmetry g (stabilizer G).hom
  exact IsHomeomorph.topologicalKrullDim_eq _ (e₁.trans e₂).hom.homeomorph.isHomeomorph

/-- The local ring of the arrow scheme of the restriction of a groupoid scheme to the residue
field at a finite type point, taken at the identity arrow, has the dimension of the stabilizer
fibre at that point.

The object scheme of the restriction has one point, so the identity section is a closed
immersion and the identity arrow is a closed point of the restricted arrow scheme; over the
spectrum of a field the dimension of the arrow scheme is the dimension of the local ring at any
closed point. -/
public theorem ringKrullDim_stalk_restrictedArrows_eq_stabilizerFiber {S : Scheme.{u}}
    (G : GroupoidScheme S) [LocallyOfFiniteType G.source.left]
    [LocallyOfFiniteType G.target.left] {u : G.objects.left} (hu : IsFiniteTypePoint u) :
    let g : Spec (G.objects.left.residueField u) ⟶ G.objects.left :=
      G.objects.left.fromSpecResidueField u
    let g' : Over.mk (g ≫ G.objects.hom) ⟶ G.objects := Over.homMk g
    ∀ w : (GroupoidScheme.restrict G g').groupoid.objects.left,
      ringKrullDim ((GroupoidScheme.restrict G g').groupoid.arrows.left.presheaf.stalk
          ((GroupoidScheme.restrict G g').groupoid.identity.left w)) =
        topologicalKrullDim ((stabilizer G).hom.fiber u) := by
  intro g g' w
  obtain ⟨e, _, _⟩ := exists_iso_spec_residueField_restrict G hu
  have hsub : Subsingleton (GroupoidScheme.restrict G g').groupoid.objects.left :=
    ⟨fun a b => e.hom.homeomorph.injective (Subsingleton.elim _ _)⟩
  have hid : IsClosedImmersion
      (GroupoidScheme.restrict G g').groupoid.identity.left :=
    isClosedImmersion_of_comp_eq_id _ _
      (identity_left_comp_source_left (GroupoidScheme.restrict G g').groupoid)
  have hrange : Set.range (GroupoidScheme.restrict G g').groupoid.identity.left =
      ({(GroupoidScheme.restrict G g').groupoid.identity.left w} : Set _) := by
    refine Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr ⟨w, rfl⟩)
    rintro _ ⟨z, rfl⟩
    exact congrArg (fun y => (GroupoidScheme.restrict G g').groupoid.identity.left y)
      (Subsingleton.elim z w)
  have hclosed : IsClosed
      ({(GroupoidScheme.restrict G g').groupoid.identity.left w} : Set _) :=
    hrange ▸ (GroupoidScheme.restrict G g').groupoid.identity.left.isClosedEmbedding.isClosed_range
  rw [← topologicalKrullDim_arrows_eq_ringKrullDim_stalk
    (GroupoidScheme.restrict G g').groupoid e _ hclosed]
  exact topologicalKrullDim_restrictedArrows_eq_stabilizerFiber G hu

/-- Let `A` be an affine open of the object scheme of a groupoid scheme, let `u` be a point of
`A`, and let `f` be a section over `A` vanishing at `u`. Then the vanishing locus of `f` in `A`
is an affine scheme over the base mapping to the object scheme by an immersion locally of finite
presentation, and `u` is in its image.

These are the first three conclusions of the slicing lemma, for an arbitrary choice of `f`; the
slicing lemma itself chooses `f` so that the fibre dimension drops by one. -/
public theorem exists_slice_of_mem_primeIdealOf {S : Scheme.{u}} (G : GroupoidScheme S)
    (A : G.objects.left.affineOpens) {u : G.objects.left} (huA : u ∈ A.1)
    (f : Γ(G.objects.left, A.1))
    (hf : f ∈ (A.2.primeIdealOf ⟨u, huA⟩ : PrimeSpectrum Γ(G.objects.left, A.1)).asIdeal) :
    ∃ (U' : Over S) (g : U' ⟶ G.objects) (u' : U'.left),
      IsAffine U'.left ∧ IsImmersion g.left ∧ LocallyOfFinitePresentation g.left ∧
        g.left u' = u := by
  classical
  have hA : IsAffineOpen A.1 := A.2
  let I : Ideal Γ(G.objects.left, A.1) := Ideal.span {f}
  let q : Γ(G.objects.left, A.1) ⟶ CommRingCat.of (Γ(G.objects.left, A.1) ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let gL : Spec (CommRingCat.of (Γ(G.objects.left, A.1) ⧸ I)) ⟶ G.objects.left :=
    Spec.map q ≫ hA.fromSpec
  have : IsClosedImmersion (Spec.map q) := IsClosedImmersion.spec_of_quotient_mk I
  have himm : IsImmersion gL :=
    inferInstanceAs (IsImmersion (Spec.map q ≫ hA.fromSpec))
  have hfp : (q.hom).FinitePresentation := by
    have hfg : Ideal.FG I := Submodule.fg_span_singleton f
    have : Algebra.FinitePresentation Γ(G.objects.left, A.1)
        (Γ(G.objects.left, A.1) ⧸ I) := Algebra.FinitePresentation.quotient hfg
    exact RingHom.finitePresentation_algebraMap.mpr this
  have : LocallyOfFinitePresentation (Spec.map q) :=
    (LocallyOfFinitePresentation.SpecMap_iff q).mpr hfp
  have hlfp : LocallyOfFinitePresentation gL :=
    inferInstanceAs (LocallyOfFinitePresentation (Spec.map q ≫ hA.fromSpec))
  have hmem : hA.primeIdealOf ⟨u, huA⟩ ∈
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
    intro z hz
    exact (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hf))
      (by simpa [I, Ideal.mk_ker] using hz)
  obtain ⟨u', hu'⟩ := hmem
  refine ⟨Over.mk (gL ≫ G.objects.hom), Over.homMk gL, u',
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (Γ(G.objects.left, A.1) ⧸ I)))),
    himm, hlfp, ?_⟩
  have hcomp : (Over.homMk gL : Over.mk (gL ≫ G.objects.hom) ⟶ G.objects).left u' =
      hA.fromSpec (Spec.map q u') := Scheme.Hom.comp_apply _ _ _
  rw [hcomp, show (Spec.map q u' : Spec Γ(G.objects.left, A.1)) =
    hA.primeIdealOf ⟨u, huA⟩ from hu']
  exact hA.fromSpec_primeIdealOf ⟨u, huA⟩

end AlgebraicGeometry.GroupoidScheme

end
