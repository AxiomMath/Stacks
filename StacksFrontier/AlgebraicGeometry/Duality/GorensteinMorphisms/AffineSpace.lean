module

public import Mathlib.Data.List.TFAE
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.OpenLocus

/-!
# Gorenstein morphisms and quasi-finite maps to affine space

Let `f : X ⟶ S` be flat and locally of finite presentation, let `x` be a point of `X` and let `d`
be the dimension at `x` of the fibre of `f` through `x`. Then `f` is Gorenstein at `x` if and only
if some open neighbourhood of `x` carries a locally quasi-finite `S`-morphism to `𝔸ᵈ_S` which is
Gorenstein at `x`, if and only if some open neighbourhood carries a locally quasi-finite
Gorenstein such morphism, if and only if every `S`-morphism from an open neighbourhood of `x` to
`𝔸ᵈ_S` which is quasi-finite at `x` is Gorenstein at `x`. In particular the set of points at which
`f` is Gorenstein is open.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isGorensteinAt_tfae`: the four equivalent conditions.
* `AlgebraicGeometry.Scheme.Hom.isOpen_setOf_isGorensteinAt`: openness of the Gorenstein locus,
  in `StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.OpenLocus`.

## Implementation notes

Gorensteinness is the fibrewise notion `AlgebraicGeometry.Scheme.Hom.IsGorensteinAt`, so no upper
shriek functor enters. For `g : U ⟶ 𝔸ᵈ_S` over `S` flat at `x`, Gorensteinness of `g` at `x` and
of `f` at `x` agree by [Stacks, Tag 0C11], affine space being smooth over `S`; and a quasi-finite
`g` is flat at a point where `f` is Cohen–Macaulay, by [Stacks, Tag 0BUU], which applies since a
Gorenstein point is Cohen–Macaulay [Stacks, Tag 0C06]. The existence of a locally quasi-finite
`g` near `x` is [Stacks, Tag 00QE]. For condition (3) the neighbourhood given by Tag 0BUU, on which
`g` is flat, is intersected with the open Gorenstein locus of `f`.

The dimension `d` is supplied as a natural number together with the equation
`dim_x(X_s) = d`; it is a natural number by
`AlgebraicGeometry.exists_nat_topologicalKrullDimAt_fiber`. The locally Noetherian fibres
demanded by `AlgebraicGeometry.Scheme.Hom.IsGorensteinAt` are produced from local finiteness, by
`AlgebraicGeometry.Scheme.Hom.isLocallyNoetherian_fiber_of_comp_eq` for the morphisms to affine
space.

## References

* [Stacks Project, Tag 0C09](https://stacks.math.columbia.edu/tag/0C09)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The fibres of a morphism `g` whose composite with some `p` is locally of finite type are
locally Noetherian. -/
theorem isLocallyNoetherian_fiber_of_comp_eq {U P S : Scheme.{u}} {g : U ⟶ P} {p : P ⟶ S}
    {h : U ⟶ S} [LocallyOfFiniteType h] (w : g ≫ p = h) (y : P) :
    IsLocallyNoetherian (g.fiber y) := by
  have : LocallyOfFiniteType (g ≫ p) := w ▸ inferInstance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g p
  exact isLocallyNoetherian_fiber_of_locallyOfFiniteType g y

/-- **Stacks Project, Tag 0C09.** Let `f : X ⟶ S` be flat and locally of finite presentation,
let `x ∈ X` and let `d = dim_x(X_{f x})`. The following are equivalent:
1. `f` is Gorenstein at `x`;
2. there are an open neighbourhood `U` of `x` and a locally quasi-finite morphism
   `U ⟶ 𝔸ᵈ_S` over `S` which is Gorenstein at `x`;
3. there are an open neighbourhood `U` of `x` and a locally quasi-finite Gorenstein morphism
   `U ⟶ 𝔸ᵈ_S` over `S`;
4. every `S`-morphism `g : U ⟶ 𝔸ᵈ_S` from an open neighbourhood `U` of `x` which is
   quasi-finite at `x` is Gorenstein at `x`. -/
@[stacks 0C09 "the equivalence of (1), (2), (3) and (4)"]
theorem isGorensteinAt_tfae {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (x : X) (d : ℕ)
    (hd : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞)) :
    List.TFAE [
      f.IsGorensteinAt (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f) x,
      ∃ (U : X.Opens) (hx : x ∈ U) (g : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) S)
          (hg : g ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = U.ι ≫ f),
        (LocallyOfFiniteType g ∧ LocallyQuasiFinite g) ∧
          g.IsGorensteinAt (isLocallyNoetherian_fiber_of_comp_eq hg) ⟨x, hx⟩,
      ∃ (U : X.Opens) (_ : x ∈ U) (g : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) S)
          (hg : g ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = U.ι ≫ f),
        (LocallyOfFiniteType g ∧ LocallyQuasiFinite g) ∧
          g.IsGorenstein (isLocallyNoetherian_fiber_of_comp_eq hg),
      ∀ (U : X.Opens) (hx : x ∈ U) (g : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) S)
          (hg : g ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = U.ι ≫ f),
        AlgebraicGeometry.quasiFiniteAt g ⟨x, hx⟩ →
          g.IsGorensteinAt (isLocallyNoetherian_fiber_of_comp_eq hg) ⟨x, hx⟩] := by
  let P := AffineSpace (ULift.{u} (Fin d)) S
  have : Smooth (P ↘ S) := smooth_affineSpace_over _ S
  have hf := isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f
  -- for a morphism to affine space flat at a point, its Gorensteinness is that of `f`
  have hcrit (U : X.Opens) (g : U.toScheme ⟶ P) (hg : g ≫ (P ↘ S) = U.ι ≫ f) (z : U.toScheme)
      (hflat : IsFlatAt g.toLRSHom.toShHom z) :
      g.IsGorensteinAt (isLocallyNoetherian_fiber_of_comp_eq hg) z ↔ f.IsGorensteinAt hf z.1 :=
    (isGorensteinAt_iff_of_flat_of_comp_eq g (P ↘ S) (U.ι ≫ f) hg _
        (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation _) z hflat).trans
      (isGorensteinAt_comp_iff_of_isOpenImmersion_left U.ι f hf _ z)
  have hcm := isCohenMacaulayAt_tfae f x d hd
  tfae_have 1 → 4 := by
    intro hG U hx g hg hq
    have h4 := (hcm.out 1 4).mp (isCohenMacaulayAt_of_isGorensteinAt f hf hG)
    exact (hcrit U g hg ⟨x, hx⟩ (h4 U hx g hg hq)).mpr hG
  tfae_have 4 → 2 := by
    intro h4
    obtain ⟨U, hx, g, hg, hlft, hlqf⟩ := exists_locallyQuasiFinite_affineSpace f x d hd
    exact ⟨U, hx, g, hg, ⟨hlft, hlqf⟩,
      h4 U hx g hg ((AlgebraicGeometry.forall_quasiFiniteAt_iff g).mpr ⟨hlft, hlqf⟩ ⟨x, hx⟩)⟩
  tfae_have 2 → 1 := by
    rintro ⟨U, hx, g, hg, -, hG⟩
    exact (hcrit U g hg ⟨x, hx⟩ hG.1).mp hG
  tfae_have 1 → 3 := by
    intro hG
    obtain ⟨U, hx, g, hg, ⟨hlft, hlqf⟩, hflat⟩ :=
      (hcm.out 1 3).mp (isCohenMacaulayAt_of_isGorensteinAt f hf hG)
    let W : X.Opens := ⟨{y | f.IsGorensteinAt hf y}, isOpen_setOf_isGorensteinAt f⟩
    let U' : X.Opens := U ⊓ W
    let i : U'.toScheme ⟶ U.toScheme := X.homOfLE inf_le_left
    have hi : i ≫ U.ι = U'.ι := X.homOfLE_ι inf_le_left
    let g' : U'.toScheme ⟶ P := i ≫ g
    have hg' : g' ≫ (P ↘ S) = U'.ι ≫ f := by
      rw [Category.assoc, hg, ← Category.assoc, hi]
    have : LocallyOfFiniteType g' := inferInstanceAs (LocallyOfFiniteType (i ≫ g))
    have : LocallyQuasiFinite g' := inferInstanceAs (LocallyQuasiFinite (i ≫ g))
    have : Flat g' := inferInstanceAs (Flat (i ≫ g))
    exact ⟨U', ⟨hx, hG⟩, g', hg', ⟨inferInstance, inferInstance⟩,
      fun z => (hcrit U' g' hg' z (Flat.stalkMap g' z)).mpr z.2.2⟩
  tfae_have 3 → 2 := by
    rintro ⟨U, hx, g, hg, hprops, hG⟩
    exact ⟨U, hx, g, hg, hprops, hG ⟨x, hx⟩⟩
  tfae_finish

end AlgebraicGeometry.Scheme.Hom
