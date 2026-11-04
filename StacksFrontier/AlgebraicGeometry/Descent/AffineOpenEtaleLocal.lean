module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcAffine
public import StacksFrontier.AlgebraicGeometry.SigmaPoints

/-!
# An open subscheme which is a basic open on a finite étale cover is affine

Let `V` be an affine scheme and let `O ⊆ V` be an open subscheme whose preimage under each
member of a finite, jointly surjective family of étale morphisms `cᵢ : Wᵢ ⟶ V` from affine
schemes is a basic open `D(aᵢ)` of `Wᵢ`. Then `O` is an affine open of `V`.

## Main results

* `Stacks.Descent.isAffineOpen_of_finite_etale_cover_preimage_eq_basicOpen`: the statement
  above.

## References

* [Stacks Project, Tag 02L5](https://stacks.math.columbia.edu/tag/02L5)
* [Stacks Project, Tag 07ZT](https://stacks.math.columbia.edu/tag/07ZT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MorphismProperty

universe u

namespace Stacks.Descent

/-- The image of a morphism out of a disjoint union of schemes is the union of the images of
its components. -/
private theorem range_sigmaDesc {σ : Type u} {g : σ → Scheme.{u}} {X : Scheme.{u}}
    (α : ∀ i, g i ⟶ X) :
    Set.range (Sigma.desc α) = ⋃ i, Set.range (α i) := by
  refine Set.Subset.antisymm ?_ (Set.iUnion_subset fun i => ?_)
  · rintro _ ⟨z, rfl⟩
    obtain ⟨i, y, rfl⟩ := exists_sigmaι_eq g z
    refine Set.mem_iUnion.mpr ⟨i, y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
  · rintro _ ⟨y, rfl⟩
    exact ⟨Sigma.ι g i y, by rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]⟩

/-- **An open subscheme that becomes a basic open on a finite étale cover is affine.** Let `V`
be an affine scheme, let `cᵢ : Wᵢ ⟶ V` be a finite jointly surjective family of étale morphisms
from affine schemes, and let `O ⊆ V` be an open whose preimage in `Wᵢ` is the basic open of a
single global regular function `aᵢ`. Then `O` is an affine open of `V`. -/
theorem isAffineOpen_of_finite_etale_cover_preimage_eq_basicOpen
    {V : Scheme.{u}} (hV : IsAffine V) {O : V.Opens} {ι : Type u} [Finite ι]
    {W : ι → Scheme.{u}} (c : ∀ i, W i ⟶ V) (hWaff : ∀ i, IsAffine (W i))
    (hce : ∀ i, Etale (c i)) (hcsurj : ⋃ i, Set.range (c i) = Set.univ)
    (a : ∀ i, Γ(W i, ⊤)) (ha : ∀ i, c i ⁻¹ᵁ O = (W i).basicOpen (a i)) :
    IsAffineOpen O := by
  have _ := hV
  have _ := hWaff
  have _ := hce
  have _ : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  have hdsurj : Surjective (Sigma.desc c) :=
    Surjective.sigmaDesc_of_union_range_eq_univ hcsurj
  have hdetale : Etale (Sigma.desc c) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @Etale) hce
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Sigma.desc c) := ⟨⟨hdsurj, inferInstance⟩, inferInstance⟩
  have hDaff : ∀ i, IsAffineOpen ((W i).basicOpen (a i)) := fun i =>
    (isAffineOpen_top (W i)).basicOpen (a i)
  have _ : ∀ i, IsAffine (((W i).basicOpen (a i)).toScheme) := hDaff
  have _ : IsAffine (∐ fun i => ((W i).basicOpen (a i)).toScheme) := inferInstance
  have hid : ∀ i, Sigma.ι W i ≫ Sigma.desc c = c i := fun i => Sigma.ι_desc c i
  have hrange : Set.range (Sigma.desc fun i =>
      ((W i).basicOpen (a i)).ι ≫ Sigma.ι W i) =
      Set.range (Sigma.desc c ⁻¹ᵁ O).ι := by
    rw [range_sigmaDesc, Scheme.Opens.range_ι]
    refine Set.Subset.antisymm (Set.iUnion_subset fun i => ?_) fun z hz => ?_
    · rintro _ ⟨y, rfl⟩
      have hy : ((W i).basicOpen (a i)).ι y ∈ c i ⁻¹ᵁ O := by
        rw [ha i]
        exact y.2
      show ((((W i).basicOpen (a i)).ι ≫ Sigma.ι W i) ≫ Sigma.desc c) y ∈ (O : Set V)
      rwa [Category.assoc, hid i]
    · obtain ⟨i, y, rfl⟩ := exists_sigmaι_eq W z
      have hy : y ∈ c i ⁻¹ᵁ O := by
        have : (Sigma.ι W i ≫ Sigma.desc c) y ∈ (O : Set V) := hz
        rwa [hid i] at this
      rw [ha i] at hy
      exact Set.mem_iUnion.mpr ⟨i, ⟨y, hy⟩, rfl⟩
  have _ : IsOpenImmersion (Sigma.desc fun i =>
      ((W i).basicOpen (a i)).ι ≫ Sigma.ι W i) := by
    refine isOpenImmersion_sigmaDesc _ _ fun i j hij => ?_
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨y, rfl⟩ ⟨y', hy'⟩
    have heq : Sigma.ι W j (((W j).basicOpen (a j)).ι y') =
        Sigma.ι W i (((W i).basicOpen (a i)).ι y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact hy'
    exact hij (congrArg Sigma.fst ((sigmaι_eq_iff W j i _ _).mp heq)).symm
  have hiso := IsOpenImmersion.isoOfRangeEq
    (Sigma.desc fun i => ((W i).basicOpen (a i)).ι ≫ Sigma.ι W i)
    (Sigma.desc c ⁻¹ᵁ O).ι hrange
  have _ : IsAffine ((Sigma.desc c ⁻¹ᵁ O).toScheme) := IsAffine.of_isIso hiso.inv
  have _ : IsAffineHom (Sigma.desc c ⁻¹ᵁ O).ι := inferInstance
  have _ : IsAffineHom O.ι := of_isPullback_of_descendsAlong
    (isPullback_morphismRestrict (Sigma.desc c) O).flip hQ inferInstance
  exact isAffine_of_isAffineHom O.ι

end Stacks.Descent

end
