module

public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmooth

/-!
# Local sections of a morphism smooth at a point, through a first-order thickening

Let `p : Z ⟶ U'` be a morphism of schemes, let `ι : U ⟶ U'` be a first-order thickening and let
`i : U ⟶ Z` be a section of `p` over `U`, that is `i ≫ p = ι`. If `p` is smooth at `i u₀`, then
the section extends to a section of `p` over an open neighbourhood of `ι u₀` in `U'`: there are an
open immersion `j : W ⟶ U'` whose image contains `ι u₀` and a morphism `s : W ⟶ Z` with
`s ≫ p = j`, which agrees with `i` on the part of `U` lying over `W`: for every scheme `P` with
morphisms `a : P ⟶ U` and `b : P ⟶ W` agreeing in `U'`, one has `a ≫ i = b ≫ s`.

This is the lifting step in the proofs of Stacks 0G2K and 0CXU, where `Z` represents a 2-fibre
product `(Sch/U) ×_𝒳 (Sch/U')`: there the source extends `i` over all of `U'` by Stacks 04AM,
after shrinking `U` to an affine on which `Z ⟶ U'` is smooth. The contradiction those proofs
derive only needs the extension over a neighbourhood of one point, which is what is proved here,
directly from the local form of the lifting property of a smooth morphism of schemes.

## Main results

* `AlgebraicGeometry.exists_openImmersion_section_of_smoothAt`: a section of `p` over `U` extends
  to a section over an open neighbourhood of `ι u₀` in `U'`, compatibly with every commutative
  square over that neighbourhood and `ι`.

## Implementation notes

The open neighbourhood is returned as an open immersion `j : W ⟶ U'` together with a point of `W`
over `ι u₀`, and the compatibility with `i` is stated for every commutative square over `j` and
`ι`, not only for the pullback square: every such square factors through the pullback, which is
an open subscheme of `U`. In this form the compatibility applies directly to the smaller open
neighbourhoods over which Stacks 0G2J and 0G2S express the absence of a local retraction.

## References

* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 0G2K](https://stacks.math.columbia.edu/tag/0G2K)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism smooth at the image of a point of `U` under a section over a first-order
thickening `ι : U ⟶ U'` has a section over an open neighbourhood `j : W ⟶ U'` of `ι u₀`
extending the given one: `s ≫ p = j`, and `a ≫ i = b ≫ s` for all `a : P ⟶ U`, `b : P ⟶ W`
with `a ≫ ι = b ≫ j`. -/
theorem exists_openImmersion_section_of_smoothAt {Z U U' : Scheme.{u}} (p : Z ⟶ U')
    {ι : U ⟶ U'} (hι : Stacks.Thickenings.IsFirstOrderThickening ι) (i : U ⟶ Z)
    (hi : i ≫ p = ι) (u₀ : U) (hsmooth : InfinitesimalLifting.SmoothAt p (i.base u₀)) :
    ∃ (W : Scheme.{u}) (j : W ⟶ U') (_ : IsOpenImmersion j) (w : W), j.base w = ι.base u₀ ∧
      ∃ s : W ⟶ Z, s ≫ p = j ∧
        ∀ (P : Scheme.{u}) (a : P ⟶ U) (b : P ⟶ W), a ≫ ι = b ≫ j → a ≫ i = b ≫ s := by
  obtain ⟨O, hO, hsm⟩ := hsmooth
  have he : O ≤ p ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have : Smooth (O.ι ≫ p) := by
    rw [← Scheme.Hom.resLE_comp_ι p he]
    infer_instance
  have : IsClosedImmersion ι := hι.1
  have homeo : IsHomeomorph ι.base :=
    isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨ι.isClosedEmbedding.isEmbedding, hι.isThickening.2⟩
  let Ω : U'.Opens := ⟨ι.base '' (i ⁻¹ᵁ O : Set U), homeo.isOpenMap _ (i ⁻¹ᵁ O).isOpen⟩
  have hpre : ι ⁻¹ᵁ Ω ≤ i ⁻¹ᵁ O := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact homeo.injective hxy ▸ hy
  let a : (ι ⁻¹ᵁ Ω : Scheme.{u}) ⟶ O := i.resLE O (ι ⁻¹ᵁ Ω) hpre
  have ha : a ≫ O.ι = (ι ⁻¹ᵁ Ω).ι ≫ i := Scheme.Hom.resLE_comp_ι i hpre
  have hcomm : a ≫ (O.ι ≫ p) = (ι ∣_ Ω) ≫ Ω.ι := by
    rw [← Category.assoc, ha, Category.assoc, hi, morphismRestrict_ι]
  have hu₀ : ι.base u₀ ∈ Ω := ⟨u₀, hO, rfl⟩
  obtain ⟨V', -, hV', b, hb₁, hb₂⟩ := Stacks.Smooth.exists_isAffineOpen_lift (O.ι ≫ p)
    (Stacks.Smooth.isFirstOrderThickening_morphismRestrict hι Ω) a Ω.ι hcomm ⟨_, hu₀⟩
  refine ⟨V', V'.ι ≫ Ω.ι, inferInstance, ⟨_, hV'⟩, rfl, b ≫ O.ι, by rw [Category.assoc, hb₁], ?_⟩
  have hcan : IsPullback (((ι ∣_ Ω) ⁻¹ᵁ V').ι ≫ (ι ⁻¹ᵁ Ω).ι) ((ι ∣_ Ω) ∣_ V') ι
      (V'.ι ≫ Ω.ι) :=
    (IsPullback.paste_horiz (isPullback_morphismRestrict (ι ∣_ Ω) V').flip
      (isPullback_morphismRestrict ι Ω).flip)
  have hcaneq : (((ι ∣_ Ω) ⁻¹ᵁ V').ι ≫ (ι ⁻¹ᵁ Ω).ι) ≫ i = ((ι ∣_ Ω) ∣_ V') ≫ b ≫ O.ι := by
    rw [reassoc_of% hb₂, ha, Category.assoc]
  intro P a' b' hP
  rw [← hcan.lift_fst a' b' hP, Category.assoc, hcaneq, reassoc_of% hcan.lift_snd a' b' hP]

end AlgebraicGeometry

end
