module

public import StacksFrontier.Algebra.Homology.MayerVietorisSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietoris

/-!
# The image of a Mayer–Vietoris short complex under an additive functor

An additive functor carries a binary biproduct to a binary biproduct, so it carries a
Mayer–Vietoris short complex `M ⟶ N ⊞ V ⟶ A` to one of the same shape on the images, read
through `CategoryTheory.Functor.biprodIsoOfAdditive`.  The two splitting criteria of
`StacksFrontier.Algebra.Homology.MayerVietorisSplitting` therefore apply to the image, with their
hypotheses tested on the images of the maps rather than on the maps themselves.

This is what lets a stalk functor be applied to the Mayer–Vietoris short complex of an
elementary distinguished square: the hypotheses then become statements about stalks, which is
where the geometry of the square lives.

## Main definitions

* `CategoryTheory.ShortComplex.mapMayerVietorisIso`: the image of a Mayer–Vietoris short complex
  is isomorphic to the Mayer–Vietoris short complex of the images.

## Main results

* `CategoryTheory.ShortComplex.shortExact_map_of_isIso` and
  `CategoryTheory.ShortComplex.shortExact_map_of_isZero`: the image is short exact under the
  images of the two degeneracy hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {M N V A : C} (a : M ⟶ N) (b : M ⟶ V) (g : N ⟶ A) (d : V ⟶ A)
  {C' : Type u'} [Category.{v'} C'] [Preadditive C'] [HasBinaryBiproducts C']
  (Φ : C ⥤ C') [Φ.Additive]

omit [Φ.Additive] in
/-- The alternating composite of the images of the four maps of a Mayer–Vietoris short complex
vanishes. -/
theorem zero_map_mayerVietoris (h : biprod.lift a (-b) ≫ biprod.desc g d = 0) :
    biprod.lift (Φ.map a) (-(Φ.map b)) ≫ biprod.desc (Φ.map g) (Φ.map d) = 0 := by
  have hab : a ≫ g = b ≫ d := comp_eq_comp_of_mayerVietoris a b g d h
  rw [biprod.lift_desc, Preadditive.neg_comp, ← Φ.map_comp, ← Φ.map_comp, hab, add_neg_cancel]

/-- **The image of a Mayer–Vietoris short complex under an additive functor is the Mayer–Vietoris
short complex of the images**, read through the biproduct comparison. -/
def mapMayerVietorisIso (h : biprod.lift a (-b) ≫ biprod.desc g d = 0) :
    (mayerVietoris a b g d h).map Φ ≅
      mayerVietoris (Φ.map a) (Φ.map b) (Φ.map g) (Φ.map d)
        (zero_map_mayerVietoris a b g d Φ h) :=
  ShortComplex.isoMk (Iso.refl _) (Φ.biprodIsoOfAdditive N V) (Iso.refl _)
    (by
      dsimp [mayerVietoris]
      rw [Category.id_comp, Functor.biprodIsoOfAdditive_hom_map_lift, Φ.map_neg])
    (by
      dsimp [mayerVietoris]
      rw [Category.comp_id, ← Functor.biprodIsoOfAdditive_inv_map_desc Φ N V,
        Iso.hom_inv_id_assoc])

variable [HasZeroObject C']

/-- **An additive functor carries a Mayer–Vietoris short complex to a short exact one as soon as
it inverts the edge to `V` and the map out of `N`.** -/
theorem shortExact_map_of_isIso (h : biprod.lift a (-b) ≫ biprod.desc g d = 0)
    (hb : IsIso (Φ.map b)) (hg : IsIso (Φ.map g)) :
    ((mayerVietoris a b g d h).map Φ).ShortExact :=
  have := hb
  have := hg
  ShortComplex.shortExact_of_iso (mapMayerVietorisIso a b g d Φ h).symm
    (mayerVietoris_shortExact_of_isIso (Φ.map a) (Φ.map b) (Φ.map g) (Φ.map d)
      (zero_map_mayerVietoris a b g d Φ h))

/-- **An additive functor carries a Mayer–Vietoris short complex to a short exact one as soon as
it kills the outer source and the summand `N` and inverts the edge `d`.** -/
theorem shortExact_map_of_isZero (h : biprod.lift a (-b) ≫ biprod.desc g d = 0)
    (hM : IsZero (Φ.obj M)) (hN : IsZero (Φ.obj N)) (hd : IsIso (Φ.map d)) :
    ((mayerVietoris a b g d h).map Φ).ShortExact :=
  have := hd
  ShortComplex.shortExact_of_iso (mapMayerVietorisIso a b g d Φ h).symm
    (mayerVietoris_shortExact_of_isZero (Φ.map a) (Φ.map b) (Φ.map g) (Φ.map d)
      (zero_map_mayerVietoris a b g d Φ h) hM hN)

end CategoryTheory.ShortComplex

end
