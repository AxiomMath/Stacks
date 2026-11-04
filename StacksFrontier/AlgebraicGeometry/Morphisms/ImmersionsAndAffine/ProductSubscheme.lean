module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.ClosedImmersionIdealSheaves
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibre product of two closed subschemes

Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes, let `I` be a quasi-coherent sheaf of
ideals on `X` and `J` one on `Y`, and write `V = I.subscheme` and `W = J.subscheme` for the closed
subschemes they cut out. Inside `X ×_S Y` the two inverse image ideal sheaves `pr₁^* I` and
`pr₂^* J` cut out `V ×_S Y` and `X ×_S W`, so their supremum cuts out the scheme theoretic
intersection of those two, which is `V ×_S W`. This file proves that the closed subscheme of
`X ×_S Y` cut out by `pr₁^* I ⊔ pr₂^* J` is the fibre product `V ×_S W`, as a cartesian square and
as an isomorphism, together with the compatibility of that isomorphism with the two projections.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_comap_subschemeι`: the square exhibiting
  the subscheme cut out by an inverse image ideal sheaf `I.comap f` as the fibre product
  `X ×_Y I.subscheme`.
* `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subscheme_sup_comap`: the square
  exhibiting `(pr₁^* I ⊔ pr₂^* J).subscheme` as the fibre product `I.subscheme ×_S J.subscheme`.
* `AlgebraicGeometry.Scheme.IdealSheafData.productSubschemeIso`: the same statement as an
  isomorphism onto the chosen fibre product, with `productSubschemeIso_hom_fst_subschemeι` and
  `productSubschemeIso_hom_snd_subschemeι` identifying its two projections with the two
  projections of `X ×_S Y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y S : Scheme.{u}}

/-- **An inverse image ideal sheaf cuts out a fibre product.** For `f : X ⟶ Y` and an ideal sheaf
`I` on `Y`, the square with corners `(I.comap f).subscheme`, `X`, `I.subscheme` and `Y` is
cartesian: the closed subscheme of `X` cut out by `f^* I` is `X ×_Y I.subscheme`. -/
@[ega "III 2.6.2.3" "partial"]
theorem isPullback_comap_subschemeι (I : Y.IdealSheafData) (f : X ⟶ Y) :
    IsPullback (I.comap f).subschemeι
      (subschemeMap (I.comap f) I f (I.le_map_comap f)) f I.subschemeι :=
  .of_iso_pullback ⟨by simp⟩ (I.comapIso f) (by simp) (by simp)

/-- **The fibre product of two closed subschemes is cut out by the sum of the two inverse image
ideal sheaves.** For `f : X ⟶ S`, `g : Y ⟶ S`, an ideal sheaf `I` on `X` and an ideal sheaf `J` on
`Y`, the closed subscheme of `X ×_S Y` cut out by `pr₁^* I ⊔ pr₂^* J` is the fibre product
`I.subscheme ×_S J.subscheme`, the two projections being the restrictions of the two projections
of `X ×_S Y`. -/
theorem isPullback_subscheme_sup_comap (f : X ⟶ S) (g : Y ⟶ S)
    (I : X.IdealSheafData) (J : Y.IdealSheafData) :
    IsPullback
      (inclusion (le_sup_left :
            I.comap (pullback.fst f g) ≤
              I.comap (pullback.fst f g) ⊔ J.comap (pullback.snd f g)) ≫
          subschemeMap _ I (pullback.fst f g) (I.le_map_comap (pullback.fst f g)))
      (inclusion (le_sup_right :
            J.comap (pullback.snd f g) ≤
              I.comap (pullback.fst f g) ⊔ J.comap (pullback.snd f g)) ≫
          subschemeMap _ J (pullback.snd f g) (J.le_map_comap (pullback.snd f g)))
      (I.subschemeι ≫ f) (J.subschemeι ≫ g) :=
  ((isPullback_subscheme_sup (pullback f g) _ _).paste_horiz
      (isPullback_comap_subschemeι I (pullback.fst f g)).flip).paste_vert
    ((isPullback_comap_subschemeι J (pullback.snd f g)).paste_horiz
      (IsPullback.of_hasPullback f g))

/-- **The fibre product of two closed subschemes, as an isomorphism.** The closed subscheme of
`X ×_S Y` cut out by `pr₁^* I ⊔ pr₂^* J` is isomorphic to the fibre product of `I.subscheme` and
`J.subscheme` over `S`.

The two projections of this isomorphism are the restrictions of the two projections of
`X ×_S Y`: see `productSubschemeIso_hom_fst_subschemeι` and
`productSubschemeIso_hom_snd_subschemeι`. -/
noncomputable def productSubschemeIso (f : X ⟶ S) (g : Y ⟶ S)
    (I : X.IdealSheafData) (J : Y.IdealSheafData) :
    (I.comap (pullback.fst f g) ⊔ J.comap (pullback.snd f g)).subscheme ≅
      pullback (I.subschemeι ≫ f) (J.subschemeι ≫ g) :=
  (isPullback_subscheme_sup_comap f g I J).isoPullback

/-- The first projection of `productSubschemeIso`, followed by the closed immersion of
`I.subscheme`, is the first projection of `X ×_S Y` restricted to the subscheme. -/
@[reassoc]
theorem productSubschemeIso_hom_fst_subschemeι (f : X ⟶ S) (g : Y ⟶ S)
    (I : X.IdealSheafData) (J : Y.IdealSheafData) :
    (productSubschemeIso f g I J).hom ≫
        pullback.fst (I.subschemeι ≫ f) (J.subschemeι ≫ g) ≫ I.subschemeι =
      (I.comap (pullback.fst f g) ⊔ J.comap (pullback.snd f g)).subschemeι ≫
        pullback.fst f g := by
  rw [← Category.assoc, productSubschemeIso, IsPullback.isoPullback_hom_fst, Category.assoc,
    subschemeMap_subschemeι, ← Category.assoc, inclusion_subschemeι]

/-- The second projection of `productSubschemeIso`, followed by the closed immersion of
`J.subscheme`, is the second projection of `X ×_S Y` restricted to the subscheme. -/
@[reassoc]
theorem productSubschemeIso_hom_snd_subschemeι (f : X ⟶ S) (g : Y ⟶ S)
    (I : X.IdealSheafData) (J : Y.IdealSheafData) :
    (productSubschemeIso f g I J).hom ≫
        pullback.snd (I.subschemeι ≫ f) (J.subschemeι ≫ g) ≫ J.subschemeι =
      (I.comap (pullback.fst f g) ⊔ J.comap (pullback.snd f g)).subschemeι ≫
        pullback.snd f g := by
  rw [← Category.assoc, productSubschemeIso, IsPullback.isoPullback_hom_snd, Category.assoc,
    subschemeMap_subschemeι, ← Category.assoc, inclusion_subschemeι]

end AlgebraicGeometry.Scheme.IdealSheafData

end
