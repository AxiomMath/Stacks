module

public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.FlatFibers
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularSchemes
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
import StacksCore.Tactic.StacksAttribute

/-!
# Permanence properties of étale morphisms

Étaleness of a morphism of schemes is detected by flatness together with étaleness of all
fibres, it is preserved by base change and by composition, and consequently by the formation of
fibre products and of products of morphisms.

## Main results

* `AlgebraicGeometry.etale_iff_locallyOfFinitePresentation_and_flat_and_fibers_etale`
  characterizes étaleness by local finite presentation, flatness and étaleness of every fibre.
* `AlgebraicGeometry.etale_pullback_map`: the fibre product over a base of two étale morphisms
  is étale.
* `AlgebraicGeometry.etale_prod_map`: the product of two étale morphisms is étale.

## Implementation notes

The fibre of `f` over `s` is Mathlib's `AlgebraicGeometry.Scheme.Hom.fiber`, and "the fibre is
étale" means that its structure morphism
`AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField` to the spectrum of the residue field of
`s` is étale. That morphism is by definition a base change of `f`, which gives one direction of
the characterization outright; the other direction converts étaleness of a fibre into the
decomposition of a scheme étale over a field and feeds it to
`AlgebraicGeometry.etale_of_flat_of_fibers_finite_separable`.

Stability under base change and under composition are Mathlib instances, recorded here by
annotation rather than restated. Both halves of clause (6) are derived from them: the fibre
product of morphisms is `CategoryTheory.MorphismProperty.pullbackMap` for the étale property,
and the product of morphisms factors as two base changes along the projections of a product,
conjugated by the braiding.

## References

* [Stacks Project, Tag 03PC](https://stacks.math.columbia.edu/tag/03PC)
* [Stacks Project, Tag 02GM](https://stacks.math.columbia.edu/tag/02GM)
* [Stacks Project, Tag 02GN](https://stacks.math.columbia.edu/tag/02GN)
* [Stacks Project, Tag 02GO](https://stacks.math.columbia.edu/tag/02GO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Flatness and the fibres -/

/-- **Stacks Project, Tag 03PC, part (2), (a) ⟺ (b).** A morphism of schemes is étale if and
only if it is locally of finite presentation, flat, and all of its fibres are étale. -/
@[stacks 03PC "flat_fibres"]
public theorem etale_iff_locallyOfFinitePresentation_and_flat_and_fibers_etale
    {X S : Scheme.{u}} (f : X ⟶ S) :
    Etale f ↔ LocallyOfFinitePresentation f ∧ Flat f ∧
      ∀ s : S, Etale (f.fiberToSpecResidueField s) := by
  constructor
  · intro _
    exact ⟨inferInstance, inferInstance, fun s ↦
      inferInstanceAs (Etale (pullback.snd f (S.fromSpecResidueField s)))⟩
  · rintro ⟨_, _, hfib⟩
    exact etale_of_flat_of_fibers_finite_separable f fun s ↦
      (etale_iff_iso_coproduct_spectra_finite_separable (S.residueField s)
        (f.fiberToSpecResidueField s)).mp (hfib s)

add_to_stacks 03PC "flat_unramified_finite_presentation"
  AlgebraicGeometry.etale_iff_flat_and_locallyOfFinitePresentation_and_unramified

/-! ### Base change and composition -/

add_to_stacks 03PC "base_change" AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
add_to_sga "1 I 4.6" AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
add_to_sga "1 IX 1.3" AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
add_to_sga "1 IX 4.2" "Étaleness of X₁' → S₁'" AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
add_to_sga "3 VIB 10.1" "partial" AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
add_to_sga "3 VIB 2.1.2" "partial" AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
add_to_sga "3 VIIB 1.6.C" "special case" AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
add_to_sga "4 VII 1.4" "partial" AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
add_to_sga "4½ Arcata 2.1.3" AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
add_to_ega "IV 17.3.3" "(iii), étale case" AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
add_to_ega "IV 17.7.3" "(ii)" AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
add_to_stacks 03PC "composition" AlgebraicGeometry.Etale.etale_comp
add_to_sga "1 I 4.6" AlgebraicGeometry.Etale.etale_comp
add_to_sga "1 V 3.3" "special case" AlgebraicGeometry.Etale.etale_comp
add_to_ega "IV 17.3.3" "(ii), étale case" AlgebraicGeometry.Etale.etale_comp
add_to_ega "IV 17.3.5" "étale clause" AlgebraicGeometry.Etale.etale_comp

/-! ### Fibre products and products -/

/-- **Stacks Project, Tag 03PC, part (6), fibre products.** Let `i₁ : X ⟶ X'` and
`i₂ : Y ⟶ Y'` be morphisms of schemes over a base `S`. If both are étale, then so is the
induced morphism `X ×_S Y ⟶ X' ×_S Y'`. -/
@[stacks 03PC "fibre_product"]
public theorem etale_pullback_map {S X X' Y Y' : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : X' ⟶ S} {g' : Y' ⟶ S} {i₁ : X ⟶ X'} {i₂ : Y ⟶ Y'} [Etale i₁] [Etale i₂]
    (e₁ : f = i₁ ≫ f') (e₂ : g = i₂ ≫ g') :
    Etale (pullback.map f g f' g' i₁ i₂ (𝟙 S) ((Category.comp_id _).trans e₁)
      ((Category.comp_id _).trans e₂)) :=
  have : MorphismProperty.IsStableUnderComposition (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  MorphismProperty.pullbackMap (P := @Etale) ‹Etale i₁› ‹Etale i₂› e₁ e₂

/-- The product of an étale morphism with an identity is étale: it is the base change of that
morphism along a projection of a product. -/
public theorem etale_prod_map_id {X X' : Scheme.{u}} (f : X ⟶ X') [Etale f] (Y : Scheme.{u}) :
    Etale (prod.map f (𝟙 Y)) :=
  MorphismProperty.of_isPullback (IsPullback.of_prod_fst_with_id f Y) ‹Etale f›

/-- The product of an identity with an étale morphism is étale. -/
public theorem etale_prod_id_map (X : Scheme.{u}) {Y Y' : Scheme.{u}} (g : Y ⟶ Y') [Etale g] :
    Etale (prod.map (𝟙 X) g) := by
  rw [show prod.map (𝟙 X) g
      = (prod.braiding X Y).hom ≫ prod.map g (𝟙 X) ≫ (prod.braiding Y' X).hom by ext <;> simp]
  have := etale_prod_map_id g X
  infer_instance

/-- **Stacks Project, Tag 03PC, part (6), products.** The product of two étale morphisms of
schemes is étale. -/
@[stacks 03PC "product"]
public theorem etale_prod_map {X X' Y Y' : Scheme.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    [Etale f] [Etale g] : Etale (prod.map f g) := by
  rw [show prod.map f g = prod.map f (𝟙 Y) ≫ prod.map (𝟙 X') g by simp]
  have := etale_prod_map_id f Y
  have := etale_prod_id_map X' g
  infer_instance

/-! ### Relative dimension -/

/-- **Stacks Project, Tag 03PC, part (7).** An étale morphism of schemes has relative
dimension `0`: it is locally quasi-finite, and a locally quasi-finite morphism is exactly one
of relative dimension `0`. -/
@[stacks 03PC "relative_dimension_zero"]
public theorem relativeDimension_zero_of_etale {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] :
    RelativeDimension f 0 :=
  (locallyQuasiFinite_iff_relativeDimension_zero f).mp (locallyQuasiFinite_of_etale f).2

/-! ### Reducedness and regularity of the source -/

add_to_stacks 03PC "reduced" AlgebraicGeometry.isReduced_of_etale

/-- **Stacks Project, Tag 03PC, part (8), the regular case.** The source of an étale morphism
with regular target is regular, an étale morphism being smooth. -/
@[stacks 03PC "regular"]
public theorem isRegular_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (hY : IsRegular Y) :
    IsRegular X :=
  isRegular_of_smooth f inferInstance hY

end AlgebraicGeometry
