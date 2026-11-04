module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.DecompositionBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two presentations of a scheme-theoretic intersection

Let `I`, `J` be quasi-coherent ideal sheaves on a scheme `X`, cutting out `D₁` and `D₂`. The
scheme-theoretic intersection `D₁ ∩ D₂` has two presentations: as the closed subscheme of `X` cut
out by `I ⊔ J`, and as the closed subscheme of `D₁` cut out by the inverse image
`J.comap I.subschemeι`. Both are closed subschemes of `D₁` with the same ideal, by
`AlgebraicGeometry.Scheme.IdealSheafData.ker_inclusion_le_sup_left`, so they are isomorphic over
`D₁`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.supComapSubschemeIso`: the two presentations of
  `D₁ ∩ D₂` are isomorphic over `D₁`.
* `AlgebraicGeometry.Scheme.IdealSheafData.map_comap_subschemeι`: pushing
  `J.comap I.subschemeι` forward along the closed immersion of `I` gives `I ⊔ J`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- **The two presentations of a scheme-theoretic intersection of closed subschemes agree.** The
intersection `D₁ ∩ D₂` may be read either as the closed subscheme of `X` cut out by `I ⊔ J` or as
the closed subscheme of `D₁` cut out by the inverse image `J.comap I.subschemeι`; the two are
isomorphic over `D₁`. -/
def supComapSubschemeIso (I J : X.IdealSheafData) :
    (I ⊔ J).subscheme ≅ (J.comap I.subschemeι).subscheme :=
  haveI : IsIso (IsClosedImmersion.lift (J.comap I.subschemeι).subschemeι
      (inclusion (le_sup_left : I ≤ I ⊔ J))
      (((J.comap I.subschemeι).ker_subschemeι.trans
        (ker_inclusion_le_sup_left I J).symm).le)) :=
    IsClosedImmersion.isIso_lift _ _
      ((J.comap I.subschemeι).ker_subschemeι.trans (ker_inclusion_le_sup_left I J).symm)
  asIso (IsClosedImmersion.lift (J.comap I.subschemeι).subschemeι
    (inclusion (le_sup_left : I ≤ I ⊔ J))
    (((J.comap I.subschemeι).ker_subschemeι.trans
      (ker_inclusion_le_sup_left I J).symm).le))

/-- The isomorphism `AlgebraicGeometry.Scheme.IdealSheafData.supComapSubschemeIso` is one of
closed subschemes of `D₁`: it carries the inclusion of the second presentation to the inclusion
of the first. -/
@[reassoc]
theorem supComapSubschemeIso_hom_subschemeι (I J : X.IdealSheafData) :
    (supComapSubschemeIso I J).hom ≫ (J.comap I.subschemeι).subschemeι =
      inclusion (le_sup_left : I ≤ I ⊔ J) :=
  IsClosedImmersion.lift_fac _ _ _

/-- **Restricting an ideal to a closed subscheme and pushing the result back out gives the
join.** For ideal sheaves `I`, `J` on `X`, the pushforward along the closed immersion of `I` of
the inverse image `J.comap I.subschemeι` is `I ⊔ J`. -/
@[ega "I 4.4.5" "special case"]
theorem map_comap_subschemeι (I J : X.IdealSheafData) :
    (J.comap I.subschemeι).map I.subschemeι = I ⊔ J := by
  calc (J.comap I.subschemeι).map I.subschemeι
      = ((J.comap I.subschemeι).subschemeι ≫ I.subschemeι).ker := rfl
    _ = ((supComapSubschemeIso I J).hom ≫
          (J.comap I.subschemeι).subschemeι ≫ I.subschemeι).ker :=
        (Scheme.Hom.ker_comp_of_isIso _ _).symm
    _ = (I ⊔ J).subschemeι.ker := by
        rw [← Category.assoc, supComapSubschemeIso_hom_subschemeι, inclusion_subschemeι]
    _ = I ⊔ J := (I ⊔ J).ker_subschemeι

end AlgebraicGeometry.Scheme.IdealSheafData

end
