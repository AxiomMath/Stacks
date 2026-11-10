module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleHigherBaseChangePasting

/-!
# The base change map does not depend on the choice of the upper corners

Let `h ≫ f' = e ≫ g` be a commutative square of schemes
```
X' <--h-- Y
|f'       |e
S  <--g-- T
```
and let `φ : X'₂ ≅ X'`, `ψ : Y₂ ≅ Y` be isomorphisms with `h₂ ≫ φ = ψ ≫ h`. Then the degree-`q`
base change map `(φ ≫ f')⁻¹R^q g_*F ⟶ R^q h₂_*(ψ ≫ e)⁻¹F` of the square with upper corners `X'₂`,
`Y₂` is an isomorphism exactly when the one of the original square is
(`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_iff_of_iso`).

This is how the proof of [Stacks, Tag 0F1H] identifies squares built from different choices of
fibre products: the square `Y ×_K X_i ⟵ Y ×_K U_i` over `X_i ⟵ U_i`, to which [Stacks, Tag 0EZT]
is applied, "is equal to" the square `Y_L ×_L X_i ⟵ Y_L ×_L U_i` over the field `L`, to which the
induction hypothesis is applied; the two have the same bottom row and isomorphic upper corners.

The square of `φ` and `ψ` is cartesian with an isomorphism, hence an open immersion, as its
inverse-image leg, so its base change map is an isomorphism in every degree
(`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_isOpenImmersion`); the two directions
are the vertical pastings ([Stacks, Tag 0E46]) of the given square with this square and with its
inverse (`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_paste`).

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 0E46](https://stacks.math.columbia.edu/tag/0E46)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section Iso

variable {X' X'₂ Y Y₂ S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- One direction of `isIso_higherBaseChangeMapAb_app_iff_of_iso`: an isomorphism of the upper
corners carries an invertible base change map to an invertible one. -/
private theorem isIso_higherBaseChangeMapAb_app_of_iso (φ : X'₂ ≅ X') (ψ : Y₂ ≅ Y)
    (h₂ : Y₂ ⟶ X'₂) (hφψ : h₂ ≫ φ.hom = ψ.hom ≫ h) (f'₂ : X'₂ ⟶ S) (hf : f'₂ = φ.hom ≫ f')
    (e₂ : Y₂ ⟶ T) (he : e₂ = ψ.hom ≫ e) (w₂ : h₂ ≫ f'₂ = e₂ ≫ g) (q : ℕ)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hF : IsIso ((higherBaseChangeMapAb f' g h e w q).app F)) :
    IsIso ((higherBaseChangeMapAb f'₂ g h₂ e₂ w₂ q).app F) := by
  have sq : IsPullback h₂ ψ.hom φ.hom h := IsPullback.of_vert_isIso ⟨hφψ⟩
  have hup := isIso_higherBaseChangeMapAb_app_of_isOpenImmersion sq q
    ((smallEtalePullbackAb e).obj F)
  have hout := isIso_higherBaseChangeMapAb_app_of_paste g h h₂ f' φ.hom e ψ.hom w sq.w q F hF hup
  exact (isIso_higherBaseChangeMapAb_app_congr g h₂ hf.symm he.symm _ w₂ q F).1 hout

/-- **Invertibility of a base change map does not depend on the choice of the upper corners.**
Let `h ≫ f' = e ≫ g` be a commutative square and let `φ : X'₂ ≅ X'`, `ψ : Y₂ ≅ Y` be
isomorphisms with `h₂ ≫ φ = ψ ≫ h`. Then the degree-`q` base change map of the square
`h₂ ≫ (φ ≫ f') = (ψ ≫ e) ≫ g` is an isomorphism at `F` exactly when the one of the original
square is.

The square of `φ` and `ψ` is cartesian with an open immersion as its inverse-image leg, so its
base change map is an isomorphism (`isIso_higherBaseChangeMapAb_app_of_isOpenImmersion`), and the
two directions are pastings with it and with its inverse
(`isIso_higherBaseChangeMapAb_app_of_paste`). -/
theorem isIso_higherBaseChangeMapAb_app_iff_of_iso (φ : X'₂ ≅ X') (ψ : Y₂ ≅ Y)
    (h₂ : Y₂ ⟶ X'₂) (hφψ : h₂ ≫ φ.hom = ψ.hom ≫ h) (f'₂ : X'₂ ⟶ S) (hf : f'₂ = φ.hom ≫ f')
    (e₂ : Y₂ ⟶ T) (he : e₂ = ψ.hom ≫ e) (w₂ : h₂ ≫ f'₂ = e₂ ≫ g) (q : ℕ)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    IsIso ((higherBaseChangeMapAb f'₂ g h₂ e₂ w₂ q).app F) ↔
      IsIso ((higherBaseChangeMapAb f' g h e w q).app F) := by
  refine ⟨fun hF => ?_, isIso_higherBaseChangeMapAb_app_of_iso f' g h e w φ ψ h₂ hφψ f'₂ hf e₂ he
    w₂ q F⟩
  refine isIso_higherBaseChangeMapAb_app_of_iso f'₂ g h₂ e₂ w₂ φ.symm ψ.symm h ?_ f' ?_ e ?_ w q
    F hF
  · rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, ← hφψ, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  · rw [hf, Iso.symm_hom, Iso.inv_hom_id_assoc]
  · rw [he, Iso.symm_hom, Iso.inv_hom_id_assoc]

end Iso

end Stacks.EtaleCohomology

end
