module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.AtPoint
public import StacksFrontier.RingTheory.Smooth.SmoothAt

/-!
# Smoothness at a point of the spectrum of an algebra

For an `R`-algebra `A` and a prime `q` of `A`, the morphism `Spec A ⟶ Spec R` is smooth at the
point `q` (smooth on an open neighbourhood, `InfinitesimalLifting.SmoothAt`) exactly when `R → A`
is smooth at `q` in the sense of Definition 00TB (`Algebra.SmoothAt`): some `A_g` with `g ∉ q` is
smooth over `R`. The basic opens `D(g) ≅ Spec A_g` form a basis of neighbourhoods of `q`.

## Main results

* `InfinitesimalLifting.smoothAt_specMap_iff`: the equivalence.

## References

* [Stacks Project, Tag 00TB](https://stacks.math.columbia.edu/tag/00TB)
* [Stacks Project, Tag 01V5](https://stacks.math.columbia.edu/tag/01V5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace InfinitesimalLifting

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

private instance respectsIso_smooth : MorphismProperty.RespectsIso (@Smooth.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- The composite of `D(g) ⟶ Spec A ⟶ Spec R` is smooth exactly when `A_g` is smooth over
`R`. -/
theorem smooth_basicOpen_ι_comp_iff (g : A) :
    Smooth (Scheme.Opens.ι (X := Spec (.of A)) (PrimeSpectrum.basicOpen g) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A))) ↔
      Algebra.Smooth R (Localization.Away g) := by
  rw [← basicOpenIsoSpecAway_hom_SpecMap (R := .of A) g, Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso (P := @Smooth.{u}), ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq,
    HasRingHomProperty.Spec_iff (P := @Smooth), CommRingCat.hom_ofHom,
    RingHom.smooth_algebraMap]

/-- A morphism restricted to an open of the source is smooth exactly when its composite with the
inclusion of that open is. -/
theorem smooth_resLE_top_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) :
    Smooth (f.resLE ⊤ U le_top) ↔ Smooth (U.ι ≫ f) := by
  have : IsIso (⊤ : Y.Opens).ι := inferInstanceAs (IsIso (Scheme.topIso Y).hom)
  rw [← MorphismProperty.cancel_right_of_respectsIso (P := @Smooth.{u}) _ (⊤ : Y.Opens).ι,
    show f.resLE ⊤ U le_top ≫ (⊤ : Y.Opens).ι = U.ι ≫ f from Scheme.Hom.resLE_comp_ι f _]

/-- **Smoothness at a point of a spectrum.** `Spec A ⟶ Spec R` is smooth at the point `q` exactly
when `R → A` is smooth at `q` in the sense of Definition 00TB. -/
theorem smoothAt_specMap_iff (q : PrimeSpectrum A) :
    InfinitesimalLifting.SmoothAt (Spec.map (CommRingCat.ofHom (algebraMap R A))) q ↔
      Algebra.SmoothAt R A q.asIdeal := by
  constructor
  · rintro ⟨U, hqU, hU⟩
    obtain ⟨_, ⟨g, rfl⟩, hqg, hgU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqU U.2
    refine ⟨g, hqg, (smooth_basicOpen_ι_comp_iff g).mp ?_⟩
    rw [smooth_resLE_top_iff] at hU
    obtain ⟨V, hV⟩ : ∃ V : (Spec (.of A)).Opens, V = PrimeSpectrum.basicOpen g := ⟨_, rfl⟩
    have hle' : V ≤ U := hV ▸ hgU
    rw [← hV, ← Scheme.homOfLE_ι _ hle', Category.assoc]
    exact MorphismProperty.comp_mem (W := @Smooth.{u}) _ _ inferInstance hU
  · rintro ⟨g, hqg, hg⟩
    exact ⟨PrimeSpectrum.basicOpen g, hqg, (smooth_resLE_top_iff _ _).mpr
      ((smooth_basicOpen_ι_comp_iff g).mpr hg)⟩

end InfinitesimalLifting
