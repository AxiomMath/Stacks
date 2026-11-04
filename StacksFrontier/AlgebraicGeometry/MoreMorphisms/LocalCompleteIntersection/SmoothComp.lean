module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Composition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Defs
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Perfect
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SyntomicIntoSmooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.AffineSpaceImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularImmersionComposition

/-!
# A smooth morphism followed by a local complete intersection morphism

The composite of a smooth morphism with a local complete intersection morphism is a local
complete intersection morphism. This is the case of Stacks 069J — closure of the Koszul property
under composition — in which the first morphism is smooth; it is the case needed to compare the
two étale-chart formulations of the Koszul property for algebraic spaces, and it is cheaper than
the general statement because a smooth source immerses into affine space *Koszul-regularly* for
free, by Stacks 067U, with no appeal to Stacks 069G.

## Main results

* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_comp_of_smooth`: a smooth morphism
  followed by a local complete intersection morphism is a local complete intersection morphism.

## Implementation notes

Fix a point `x` of the source of the smooth `f : X ⟶ Y`, and let `g : Y ⟶ S` be Koszul. The
Koszul property of `g` at `f x` supplies an open `V ∋ f x`, a scheme `P` smooth over `S` through
`π` and a Koszul-regular immersion `i : V ⟶ P` factoring `g|_V`. Choose an affine open `U ∋ x`
inside `f ⁻¹ᵁ V`. Then:

* `U` is quasi-affine and `f.resLE V U : U ⟶ V` is smooth, hence locally of finite type, so
  Stacks 04II (`AlgebraicGeometry.exists_immersion_affineSpace`) gives an immersion
  `j : U ⟶ 𝔸ⁿ_V` over `V`;
* `j` is an immersion between two schemes smooth over `V`, so it is a regular immersion by
  Stacks 067U, hence Koszul-regular by Stacks 063K;
* `𝔸ⁿ_V ⟶ 𝔸ⁿ_P` is a base change of `i` along the smooth, hence flat, projection
  `𝔸ⁿ_P ⟶ P`, so it is Koszul-regular by Stacks 067P;
* the composite `U ⟶ 𝔸ⁿ_V ⟶ 𝔸ⁿ_P` is therefore Koszul-regular by Stacks 067Q, and
  `𝔸ⁿ_P ⟶ P ⟶ S` is smooth.

That is a Koszul factorization of `f ≫ g` near `x`. Smoothness of affine space over its base is
obtained by base change from affine space over `Spec ℤ`, where it is the smooth ring map
`ℤ ⟶ ℤ[xᵢ]`.

The statement is deliberately *not* tagged `@[stacks 069J]`: it is a special case of that lemma,
not the lemma itself, which also covers a first morphism that is merely Koszul.

## References

* [The Stacks Project, Lemma 37.62.8 (069J)](https://stacks.math.columbia.edu/tag/069J)
* [The Stacks Project, Lemma 31.22.7 (067U)](https://stacks.math.columbia.edu/tag/067U)
* [The Stacks Project, Lemma 31.21.4 (067P)](https://stacks.math.columbia.edu/tag/067P)
* [The Stacks Project, Lemma 31.21.6 (067Q)](https://stacks.math.columbia.edu/tag/067Q)
* [The Stacks Project, Lemma 29.39.2 (04II)](https://stacks.math.columbia.edu/tag/04II)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace AlgebraicGeometry

/-- The composite of a smooth morphism with a local complete intersection morphism is a local
complete intersection morphism. This is the smooth case of Stacks 069J. -/
theorem isLocalCompleteIntersectionMorphism_comp_of_smooth {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [Smooth f] (hg : IsLocalCompleteIntersectionMorphism g) :
    IsLocalCompleteIntersectionMorphism (f ≫ g) := by
  have : LocallyOfFiniteType g :=
    locallyOfFiniteType_of_isLocalCompleteIntersectionMorphism hg
  intro x
  obtain ⟨-, V, hfxV, P, i, π, hi, hireg, hπ, hfac⟩ := hg (f.base x)
  let _ : IsImmersion i := hi
  let _ : Smooth π := hπ
  obtain ⟨U, hxU, hUV⟩ : ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ f ⁻¹ᵁ V := by
    obtain ⟨-, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ (f ⁻¹ᵁ V : X.Opens) from hfxV) (f ⁻¹ᵁ V).2
    exact ⟨⟨U, hU⟩, hxU, hUV⟩
  have : IsAffine U.1.toScheme := U.2
  obtain ⟨n, j, hjimm, hjfac⟩ := exists_immersion_affineSpace (f.resLE V U.1 hUV)
  let _ : IsImmersion j := hjimm
  have : Smooth (AffineSpace (ULift.{u} (Fin n)) V.toScheme ↘ V.toScheme) :=
    smooth_affineSpace_over _ _
  have : Smooth (AffineSpace (ULift.{u} (Fin n)) P ↘ P) := smooth_affineSpace_over _ _
  have : Smooth (j ≫ (AffineSpace (ULift.{u} (Fin n)) V.toScheme ↘ V.toScheme)) := by
    rw [hjfac]; infer_instance
  have hjreg : IsKoszulRegularImmersion j :=
    isKoszulRegularImmersion_of_isRegularImmersion j
      (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth j
        (AffineSpace (ULift.{u} (Fin n)) V.toScheme ↘ V.toScheme))
  have : IsImmersion (AffineSpace.map (ULift.{u} (Fin n)) i) :=
    MorphismProperty.of_isPullback
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin n)) i).flip hi
  have hmapreg : IsKoszulRegularImmersion (AffineSpace.map (ULift.{u} (Fin n)) i) :=
    Stacks.AlgebraicGeometry.isKoszulRegularImmersion_of_isPullback_of_flat
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin n)) i) hireg
  have hcompreg :
      IsKoszulRegularImmersion (j ≫ AffineSpace.map (ULift.{u} (Fin n)) i) :=
    Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp j
      (AffineSpace.map (ULift.{u} (Fin n)) i) hjreg hmapreg
  refine ⟨finiteTypeAt_of_locallyOfFiniteType (f ≫ g) x, U.1, hxU,
    AffineSpace (ULift.{u} (Fin n)) P, j ≫ AffineSpace.map (ULift.{u} (Fin n)) i,
    (AffineSpace (ULift.{u} (Fin n)) P ↘ P) ≫ π, inferInstance, hcompreg, inferInstance, ?_⟩
  calc U.1.ι ≫ f ≫ g = (f.resLE V U.1 hUV ≫ V.ι) ≫ g := by
        rw [Scheme.Hom.resLE_comp_ι f hUV, Category.assoc]
    _ = f.resLE V U.1 hUV ≫ i ≫ π := by rw [Category.assoc, hfac]
    _ = (j ≫ AffineSpace.map (ULift.{u} (Fin n)) i) ≫
          (AffineSpace (ULift.{u} (Fin n)) P ↘ P) ≫ π := by
        rw [← hjfac]
        simp only [Category.assoc, AffineSpace.map_over_assoc]

end AlgebraicGeometry

end
