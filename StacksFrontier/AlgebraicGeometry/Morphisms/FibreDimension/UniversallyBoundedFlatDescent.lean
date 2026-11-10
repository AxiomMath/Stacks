module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Artinian
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBounded

/-!
# Bounds on fibre degrees descend along a flat surjection

Let `f : X ⟶ Y` and `h : Y ⟶ Z` be morphisms of schemes with `f` flat and surjective. An integer
which bounds the degrees of the fibres of the composite `f ≫ h` bounds the degrees of the fibres
of `h`, and consequently universally bounded fibres descend from `f ≫ h` to `h`. This is Stacks
Tag 03JB.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.boundsFiberDegrees_of_comp_of_surjective_flat` is the precise form of the
  tag: the bound itself descends.
* `AlgebraicGeometry.hasUniversallyBoundedFibers_of_comp_of_surjective_flat` is its universally
  bounded consequence.

## Implementation notes

The commutative triangle of the source is expressed by taking its diagonal to be the composite
`f ≫ h`, so that no separate commutativity hypothesis is needed.

Over a point `z` of `Z` the two fibres are compared by
`CategoryTheory.Limits.pullbackRightPullbackFstIso`, which exhibits the fibre of `f ≫ h` as a
fibre product of the fibre of `h` with `f`; the resulting morphism of fibres is therefore flat
and surjective. The descent of the bound along such a morphism of schemes over a field is
isolated as `AlgebraicGeometry.exists_rank_le_of_flat_surjective_of_field`, whose argument is
the one of the source: the source of the morphism is affine with global sections a finite
dimensional algebra over the field, hence Artinian, hence a finite discrete scheme, so the
morphism is affine by Tag 01SI and its target is affine as the quotient of a finite discrete
space. On global sections the morphism is then faithfully flat, in particular injective, so the
sections of the target are a subspace of those of the source and their dimension is the required
rank.

The two passages between the rank of a finite locally free morphism and the dimension of its
module of global sections are the library's, used in opposite directions:
`AlgebraicGeometry.finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank` consumes the given
rank of the source, and `Stacks.Morphisms.isFiniteLocallyFreeOfRank_of_basis` produces the rank
of the target from a basis of its sections. No sheaf-level rank datum has to be transported by
hand, which is what keeps the argument inside the default heartbeat limit.

## References

* [Stacks Project, Tag 01SI](https://stacks.math.columbia.edu/tag/01SI)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 03J4](https://stacks.math.columbia.edu/tag/03J4)
* [Stacks Project, Tag 03JB](https://stacks.math.columbia.edu/tag/03JB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A scheme which receives a flat, surjective and quasi-compact morphism from a finite discrete
scheme is affine: the morphism is a quotient map, so the target is finite and discrete as well,
and a finite discrete scheme is affine. -/
private theorem isAffine_of_flat_surjective_of_finite_discrete {A B : Scheme.{u}} (p : A ⟶ B)
    [Flat p] [Surjective p] [QuasiCompact p] [Finite A] [DiscreteTopology A] : IsAffine B := by
  have : Finite B := .of_surjective p p.surjective
  have hq : Topology.IsQuotientMap p := Flat.isQuotientMap_of_surjective p
  have : DiscreteTopology B :=
    discreteTopology_iff_forall_isOpen.mpr fun s ↦
      hq.isCoinducing.isOpen_preimage.mp (isOpen_discrete _)
  infer_instance

/-- The degree of a finite locally free morphism to the spectrum of a field does not increase
along a flat surjection of its source.

This is the one-fibre form of Stacks Tag 03JB: `gA` is the structure morphism of the fibre of
the composite, `gB` that of the fibre of the second morphism, and `p` the comparison between
them. -/
private theorem exists_rank_le_of_flat_surjective_of_field {K : Type u} [Field K]
    {A B : Scheme.{u}} (gA : A ⟶ Spec (.of K)) (gB : B ⟶ Spec (.of K)) (p : A ⟶ B)
    (hpg : p ≫ gB = gA) [Flat p] [Surjective p] (r : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank gA r] :
    ∃ t : ℕ, t ≤ r ∧ Stacks.Morphisms.IsFiniteLocallyFreeOfRank gB t := by
  have : IsAffine A := isAffine_of_isAffineHom gA
  let _ : Algebra K Γ(A, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ gA.appTop).hom.toAlgebra
  obtain ⟨hAfin, hAdim⟩ := finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank (k := K) gA r
  -- The source of `p` is a finite discrete affine scheme, so `p` is an affine morphism.
  have : IsArtinianRing Γ(A, ⊤) := IsArtinianRing.of_finite K _
  have : IsLocallyArtinian A := IsLocallyArtinian.of_isImmersion A.isoSpec.hom
  have : IsArtinianScheme A :=
    { toIsLocallyArtinian := inferInstance, toCompactSpace := inferInstance }
  have : IsAffineHom p := by
    have : IsAffineHom (A.isoSpec.inv ≫ p) := isAffineHom_of_isArtinianRing (A.isoSpec.inv ≫ p)
    have hid : A.isoSpec.hom ≫ A.isoSpec.inv ≫ p = p := by simp
    exact hid ▸ (inferInstance : IsAffineHom (A.isoSpec.hom ≫ A.isoSpec.inv ≫ p))
  have : IsAffine B := isAffine_of_flat_surjective_of_finite_discrete p
  -- On global sections `p` is faithfully flat, hence injective.
  have hcomm : gB.appTop ≫ p.appTop = gA.appTop := by rw [← Scheme.Hom.comp_appTop, hpg]
  let _ : Algebra K Γ(B, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ gB.appTop).hom.toAlgebra
  let sect : Γ(B, ⊤) →ₗ[K] Γ(A, ⊤) :=
    { toFun := p.appTop.hom
      map_add' := fun x y ↦ map_add _ x y
      map_smul' := fun k x ↦ by
        change p.appTop.hom (((Scheme.ΓSpecIso (.of K)).inv ≫ gB.appTop).hom k * x) =
          ((Scheme.ΓSpecIso (.of K)).inv ≫ gA.appTop).hom k * p.appTop.hom x
        rw [map_mul, ← hcomm]
        rfl }
  have hinj : Function.Injective sect :=
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (f := p)).mp
      ⟨inferInstance, inferInstance⟩).injective
  have : Module.Finite K Γ(B, ⊤) := Module.Finite.of_injective sect hinj
  exact ⟨Module.finrank K Γ(B, ⊤), hAdim ▸ LinearMap.finrank_le_finrank_of_injective hinj,
    Stacks.Morphisms.isFiniteLocallyFreeOfRank_of_basis gB _
      ⟨Module.finBasisOfFinrankEq K Γ(B, ⊤) rfl⟩⟩

/-- **Stacks Project, Tag 03JB**, the precise form. If `f` is surjective and flat, then an
integer bounding the degrees of the fibres of `f ≫ h` also bounds the degrees of the fibres
of `h`. -/
@[stacks 03JB "specified bound"]
public theorem boundsFiberDegrees_of_comp_of_surjective_flat {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Y ⟶ Z) [Surjective f] [Flat f] (n : ℤ)
    (hbound : BoundsFiberDegrees (f ≫ h) n) :
    BoundsFiberDegrees h n := by
  intro z
  obtain ⟨r, hr, hsource⟩ := hbound z
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
    ((f ≫ h).fiberToSpecResidueField z) r := hsource
  -- The fibre of `f ≫ h` over `z` is the base change of `f` along the fibre of `h` over `z`.
  let e := pullbackRightPullbackFstIso h (Z.fromSpecResidueField z) f
  let bc := pullback.snd f (pullback.fst h (Z.fromSpecResidueField z))
  let p : (f ≫ h).fiber z ⟶ h.fiber z := e.inv ≫ bc
  have hsq : IsPullback (pullback.fst f (pullback.fst h (Z.fromSpecResidueField z))) bc f
      (pullback.fst h (Z.fromSpecResidueField z)) :=
    IsPullback.of_hasPullback f (pullback.fst h (Z.fromSpecResidueField z))
  have hflate : Flat e.inv :=
    HasRingHomProperty.of_isOpenImmersion RingHom.Flat.containsIdentities
  have hflatbc : Flat bc := Flat.isStableUnderBaseChange.of_isPullback hsq inferInstance
  have hsurjbc : Surjective bc :=
    Surjective.instIsStableUnderBaseChangeScheme.of_isPullback hsq inferInstance
  have hflatp : Flat p := Flat.comp e.inv bc (hf := hflate) (hg := hflatbc)
  have hsurjp : Surjective p := ⟨bc.surjective.comp e.inv.surjective⟩
  have hpg : p ≫ h.fiberToSpecResidueField z = (f ≫ h).fiberToSpecResidueField z := by
    simpa only [p, e, bc, Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber,
      Category.assoc] using
      pullbackRightPullbackFstIso_inv_snd_snd h (Z.fromSpecResidueField z) f
  obtain ⟨t, ht, hrank⟩ := exists_rank_le_of_flat_surjective_of_field
    (K := ↑(Z.residueField z)) ((f ≫ h).fiberToSpecResidueField z)
    (h.fiberToSpecResidueField z) p hpg r
  exact ⟨t, by omega, hrank⟩

/-- **Stacks Project, Tag 03JB.** If `f` is surjective and flat and the fibres of `f ≫ h` are
universally bounded, then so are the fibres of `h`. -/
@[stacks 03JB "universally bounded fibres"]
public theorem hasUniversallyBoundedFibers_of_comp_of_surjective_flat {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Y ⟶ Z) [Surjective f] [Flat f]
    (hbound : HasUniversallyBoundedFibers (f ≫ h)) :
    HasUniversallyBoundedFibers h :=
  let ⟨n, hn⟩ := hbound
  ⟨n, boundsFiberDegrees_of_comp_of_surjective_flat f h n hn⟩

end AlgebraicGeometry

end
