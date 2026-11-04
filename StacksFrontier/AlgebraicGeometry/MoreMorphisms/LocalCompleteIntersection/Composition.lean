module

public import Mathlib.RingTheory.RingHom.Smooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Defs
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.ImmersionIntoSmooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.SmoothTarget
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.KoszulRegularSmoothCover
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SyntomicIntoSmooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.AffineSpaceImmersion
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Independence
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularImmersionComposition
import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypeAtLocally

/-!
# Composition of local complete intersection morphisms

A composition of local complete intersection morphisms of schemes is a local complete
intersection morphism: this is **Stacks 069J**.

## Main results

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_comp_iso`:
  Koszul-regularity of an immersion is unchanged by an isomorphism of its source.
* `AlgebraicGeometry.smooth_affineSpace_over`: relative affine space on a finite index type is
  smooth over its base.
* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_comp`: Stacks 069J.
* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_isOpenImmersion`: an open immersion
  is a local complete intersection morphism.
* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_resLE`: a local complete intersection
  morphism restricts to one over an open of the target and an open of the source above it.

## Implementation notes

Fix a point `x` of the source of `f : X ⟶ Y`, put `y = f x`, and take the two factorizations the
hypotheses provide: a Koszul-regular immersion `i' : U₀ ⟶ A` with `ρ : A ⟶ Y` smooth, and a
Koszul-regular immersion `i : V ⟶ P` with `π : P ⟶ S` smooth, where `V` is a neighbourhood of
`y`. Shrinking `A` to an affine open `A'` inside `ρ⁻¹ V` and the neighbourhood of `x` to
`W = i'⁻¹ A'` makes `A'` quasi-affine and smooth over `V`, so Stacks 04II immerses it over `V`
into a relative affine space `𝔸ⁿ_V`, and that immersion is regular by Stacks 067U because both
`A'` and `𝔸ⁿ_V` are smooth over `V`. Since `𝔸ⁿ_V` is the base change of `𝔸ⁿ_P` along `i`, and
`𝔸ⁿ_P` is flat over `P`, the induced map `𝔸ⁿ_V ⟶ 𝔸ⁿ_P` is Koszul-regular by Stacks 067P. The
three Koszul-regular immersions `W ⟶ A' ⟶ 𝔸ⁿ_V ⟶ 𝔸ⁿ_P` compose to one by Stacks 067Q, and
`𝔸ⁿ_P` is smooth over `S`, which is the factorization the definition asks for.

Stacks 067U is used in place of the independence of the chosen factorization (Stacks 069G):
the Koszul-regular immersion of `W` into `𝔸ⁿ_V` is the composite of the given Koszul-regular
immersion `W ⟶ A'` with the regular immersion `A' ⟶ 𝔸ⁿ_V`.

The neighbourhood `W` is an open of `U₀.toScheme`, while the conclusion asks for an open of `X`;
the two are identified by `AlgebraicGeometry.Scheme.Hom.isoOpensRange` of the open immersion
`W.ι ≫ U₀.ι`, and Koszul-regularity is carried across that isomorphism by
`Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_comp_iso`.

Smoothness of `𝔸ⁿ_S ⟶ S` is proved by base change from `𝔸ⁿ_{Spec ℤ}`, whose smoothness is the
smoothness of the polynomial algebra `ℤ ⟶ ℤ[x₁, …, xₙ]`.

## References

* [The Stacks Project, Lemma 37.62.6 (069J)](https://stacks.math.columbia.edu/tag/069J)
* [The Stacks Project, Definition 37.62.1 (069F)](https://stacks.math.columbia.edu/tag/069F)
* [The Stacks Project, Lemma 29.40.2 (04II)](https://stacks.math.columbia.edu/tag/04II)
* [The Stacks Project, Lemma 31.23.11 (067U)](https://stacks.math.columbia.edu/tag/067U)
* [The Stacks Project, Lemma 31.22.7 (067Q)](https://stacks.math.columbia.edu/tag/067Q)
* [The Stacks Project, Lemma 31.22.3 (067P)](https://stacks.math.columbia.edu/tag/067P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

/-- Precomposing with an isomorphism of the source preserves Koszul-regularity of an
immersion. -/
theorem isKoszulRegularImmersion_comp_iso {Z Z' X : Scheme.{u}} (e : Z' ≅ Z) (i : Z ⟶ X)
    [IsImmersion i] (hi : IsKoszulRegularImmersion i) :
    IsKoszulRegularImmersion (e.hom ≫ i) := by
  refine (isKoszulRegularImmersion_iff_of_open (e.hom ≫ i) i.coborderRange
    (e.hom ≫ i.liftCoborder) (by simp)).mpr ?_
  rw [Stacks.AlgebraicGeometry.definingIdealOfHom_comp_iso]
  exact (isKoszulRegularImmersion_iff_of_open i i.coborderRange i.liftCoborder
    i.liftCoborder_ι).mp hi

end Stacks.AlgebraicGeometry.RegularIdealSheaf

open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace AlgebraicGeometry

/-- Relative affine space on a finite index type is smooth over its base. -/
theorem smooth_affineSpace_over (n : Type u) [Finite n] (S : Scheme.{u}) :
    Smooth (AffineSpace n S ↘ S) := by
  let T : Scheme.{u} := Spec (.of (ULift.{u} ℤ))
  let f : S ⟶ T :=
    S.toSpecΓ ≫ Spec.map
      (CommRingCat.ofHom ((algebraMap ℤ Γ(S, ⊤)).comp ULift.ringEquiv.toRingHom))
  let e := AffineSpace.SpecIso n (.of (ULift.{u} ℤ))
  have hpoly : RingHom.Smooth
      (MvPolynomial.C : ULift.{u} ℤ →+* MvPolynomial n (ULift.{u} ℤ)) := by
    simpa only [MvPolynomial.algebraMap_eq] using
      (RingHom.smooth_algebraMap.mpr (show Algebra.Smooth (ULift.{u} ℤ)
        (MvPolynomial n (ULift.{u} ℤ)) from ⟨inferInstance, inferInstance⟩))
  have hspec : Smooth (Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : ULift.{u} ℤ →+* MvPolynomial n (ULift.{u} ℤ)))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).2 hpoly
  have hT : Smooth (AffineSpace n T ↘ T) := by
    have he : e.inv ≫ (AffineSpace n T ↘ T) =
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : ULift.{u} ℤ →+* MvPolynomial n (ULift.{u} ℤ))) :=
      AffineSpace.SpecIso_inv_over (n := n) (.of (ULift.{u} ℤ))
    have hcomp : Smooth (e.hom ≫ Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : ULift.{u} ℤ →+* MvPolynomial n (ULift.{u} ℤ)))) := inferInstance
    rw [← he] at hcomp
    simpa only [← Category.assoc, e.hom_inv_id, Category.id_comp] using hcomp
  exact MorphismProperty.of_isPullback (AffineSpace.isPullback_map (n := n) f) hT

/-- **Stacks 069J.** A composition of local complete intersection morphisms is a local complete
intersection morphism. -/
@[stacks 069J]
theorem isLocalCompleteIntersectionMorphism_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (hf : IsLocalCompleteIntersectionMorphism f)
    (hg : IsLocalCompleteIntersectionMorphism g) :
    IsLocalCompleteIntersectionMorphism (f ≫ g) := by
  have : LocallyOfFiniteType f :=
    LocallyOfFiniteType.of_forall_finiteTypeAt f fun x => (hf x).1
  have : LocallyOfFiniteType g :=
    LocallyOfFiniteType.of_forall_finiteTypeAt g fun y => (hg y).1
  intro x
  refine ⟨finiteTypeAt_of_locallyOfFiniteType (f ≫ g) x, ?_⟩
  obtain ⟨-, U₀, hxU₀, A, i', ρ, _, hregi', _, hfact⟩ := hf x
  obtain ⟨-, V, hyV, P, i, π, hi, hregi, _, hVg⟩ := hg (f.base x)
  -- the given factorization of `f` sends the point `⟨x, hxU₀⟩` of `U₀` into `ρ ⁻¹ᵁ V`
  have hmem : i'.base (⟨x, hxU₀⟩ : U₀.toScheme) ∈ ρ ⁻¹ᵁ V := by
    have h₁ : (i' ≫ ρ).base (⟨x, hxU₀⟩ : U₀.toScheme) ∈ V := by rw [← hfact]; exact hyV
    exact h₁
  -- an affine open of `A` lying over `V` around the image of that point
  obtain ⟨-, ⟨A'', hA'', rfl⟩, hmemA', hA'V⟩ :=
    A.isBasis_affineOpens.exists_subset_of_mem_open hmem (ρ ⁻¹ᵁ V).2
  let Aaff : A.affineOpens := ⟨A'', hA''⟩
  have hAle : Aaff.1 ≤ ρ ⁻¹ᵁ V := hA'V
  have : IsAffine Aaff.1.toScheme := Aaff.2
  -- the Koszul-regular immersion of a neighbourhood of `x` into that affine open
  set W : U₀.toScheme.Opens := i' ⁻¹ᵁ Aaff.1 with hW
  set j₁ : W.toScheme ⟶ Aaff.1.toScheme := i'.resLE Aaff.1 W le_rfl with hj₁
  have hregj₁ : IsKoszulRegularImmersion j₁ := isKoszulRegularImmersion_resLE i' hregi' Aaff.1
  -- the affine open is quasi-affine and smooth over `V`, hence immerses regularly into `𝔸ⁿ_V`
  set ρ' : Aaff.1.toScheme ⟶ V.toScheme := ρ.resLE V Aaff.1 hAle with hρ'
  have : Smooth ρ' := by rw [hρ']; infer_instance
  obtain ⟨n, h, _, hhρ⟩ := exists_immersion_affineSpace ρ'
  have : Smooth (AffineSpace (ULift.{u} (Fin n)) V.toScheme ↘ V.toScheme) :=
    smooth_affineSpace_over _ _
  have : Smooth (h ≫ (AffineSpace (ULift.{u} (Fin n)) V.toScheme ↘ V.toScheme)) := by
    rw [hhρ]; infer_instance
  have hregh : IsKoszulRegularImmersion h :=
    isKoszulRegularImmersion_of_isRegularImmersion h
      (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth h
        (AffineSpace (ULift.{u} (Fin n)) V.toScheme ↘ V.toScheme))
  -- `𝔸ⁿ_V ⟶ 𝔸ⁿ_P` is a flat base change of `i`
  have : Smooth (AffineSpace (ULift.{u} (Fin n)) P ↘ P) := smooth_affineSpace_over _ _
  set m : AffineSpace (ULift.{u} (Fin n)) V.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) P :=
    AffineSpace.map (ULift.{u} (Fin n)) i with hm
  have : IsImmersion m :=
    MorphismProperty.of_isPullback (AffineSpace.isPullback_map (n := ULift.{u} (Fin n)) i).flip hi
  have hregm : IsKoszulRegularImmersion m :=
    Stacks.AlgebraicGeometry.isKoszulRegularImmersion_of_isPullback_of_flat
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin n)) i) hregi
  -- transport the source from an open of `U₀` to an open of `X`
  have hx₀W : (⟨x, hxU₀⟩ : U₀.toScheme) ∈ W := by rw [hW]; exact hmemA'
  set q : W.toScheme ⟶ X := W.ι ≫ U₀.ι with hq
  set U : X.Opens := q.opensRange with hU
  set e : W.toScheme ≅ U.toScheme := q.isoOpensRange with he
  have hqι : e.hom ≫ U.ι = q := q.isoOpensRange_hom_ι
  have hιU : U.ι = e.inv ≫ W.ι ≫ U₀.ι := by
    rw [← hq, ← hqι, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  refine ⟨U, ?_, AffineSpace (ULift.{u} (Fin n)) P, e.inv ≫ j₁ ≫ h ≫ m,
    (AffineSpace (ULift.{u} (Fin n)) P ↘ P) ≫ π, inferInstance, ?_, inferInstance, ?_⟩
  · rw [hU]
    exact ⟨⟨⟨x, hxU₀⟩, hx₀W⟩, rfl⟩
  · exact isKoszulRegularImmersion_comp_iso e.symm _
      (Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp j₁ (h ≫ m) hregj₁
        (Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp h m hregh hregm))
  · have hA'ι : j₁ ≫ Aaff.1.ι = W.ι ≫ i' := by rw [hj₁]; exact Scheme.Hom.resLE_comp_ι i' le_rfl
    have hVι : ρ' ≫ V.ι = Aaff.1.ι ≫ ρ := by rw [hρ']; exact Scheme.Hom.resLE_comp_ι ρ hAle
    have hmap : m ≫ (AffineSpace (ULift.{u} (Fin n)) P ↘ P) =
        (AffineSpace (ULift.{u} (Fin n)) V.toScheme ↘ V.toScheme) ≫ i := by
      rw [hm]; exact AffineSpace.map_over (n := ULift.{u} (Fin n)) i
    simp only [hιU, Category.assoc]
    rw [reassoc_of% hfact, ← reassoc_of% hA'ι, ← reassoc_of% hVι, hVg, ← hhρ, reassoc_of% hmap,
      Category.assoc]

/-- An open immersion of schemes is a local complete intersection morphism: it is a
Koszul-regular immersion, and a Koszul-regular immersion is Koszul by Stacks 069L. -/
theorem isLocalCompleteIntersectionMorphism_of_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsLocalCompleteIntersectionMorphism j :=
  isLocalCompleteIntersectionMorphism_of_isKoszulRegularImmersion j
    (isKoszulRegularImmersion_of_isOpenImmersion j)

/-- The restriction of a local complete intersection morphism to an open of its source lying over
an open of its target is a local complete intersection morphism: the restriction composed with
the inclusion of the open of the target is the inclusion of the open of the source composed with
the morphism, which is Koszul by Stacks 069J and Stacks 069L, and Stacks 069M cancels the smooth
inclusion. -/
theorem isLocalCompleteIntersectionMorphism_resLE {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : IsLocalCompleteIntersectionMorphism f) (V : S.Opens) (U : X.Opens)
    (hUV : U ≤ f ⁻¹ᵁ V) : IsLocalCompleteIntersectionMorphism (f.resLE V U hUV) :=
  isLocalCompleteIntersectionMorphism_of_comp_of_smooth (f.resLE V U hUV) V.ι
    (by
      rw [Scheme.Hom.resLE_comp_ι f hUV]
      exact isLocalCompleteIntersectionMorphism_comp U.ι f
        (isLocalCompleteIntersectionMorphism_of_isOpenImmersion U.ι) hf)

end AlgebraicGeometry

end
