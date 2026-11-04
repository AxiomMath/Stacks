module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BlowUpSquare.FiniteTypeCentre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BlowUpSquare.Gluing

/-!
# Gluing objects of the derived category along a blowup square

Let `X` be a scheme and `Z ⊆ X` the closed subscheme cut out by a quasi-coherent ideal `I` of
finite type, with blowup square
```
E --j--> X'
|π       |b
v        v
Z --i--> X
```
Given `K' ∈ D⁺(X'_étale)` with torsion cohomology sheaves, `L ∈ D⁺(Z_étale)` and an isomorphism
`γ : K'|_E ≅ L|_E`, there is `K ∈ D⁺(X_étale)` with isomorphisms `f : K|_{X'} ≅ K'` and
`g : K|_Z ≅ L` such that `γ = g|_E ∘ f⁻¹|_E`; and compatible morphisms `K' ⟶ M|_{X'}`,
`L ⟶ M|_Z` glue to a morphism `K ⟶ M`. This is Stacks Tag 0EW6.

## Main results

* `AlgebraicGeometry.exists_gluing_blowUp`: the gluing statement (Stacks 0EW6).

## Implementation notes

This is `Stacks.EtaleCohomology.exists_gluing_of_isPullback_of_cohomologyCommutesWithBaseChange`
(gluing along a cartesian square that is an isomorphism off a closed subscheme, for a morphism
along which cohomology commutes with base change; its proof follows the source: `K` is the fibre
of `Ri_* L ⊕ Rb_* K' ⟶ Rc_*(L|_E)`, the derived proper base change theorem, Stacks 0DDE, makes
`g` invertible, and the morphism `K ⟶ M` comes from a morphism of distinguished triangles into
the Mayer–Vietoris triangle of `M`, Stacks 0EW5) applied to the blowup square: it is cartesian
(`AlgebraicGeometry.isPullback_exceptionalDivisor`), the blowup morphism is an isomorphism over
`X \ Z` (Stacks 02OS), whose preimage is the complement of the exceptional divisor, and since
`I` is of finite type the blowup morphism is proper, so cohomology of torsion sheaves commutes
with base change along it (`AlgebraicGeometry.cohomologyCommutesWithBaseChange_blowUpToBase_of_fg`,
Stacks 0A3U).

## References

* [Stacks Project, Tag 0EW6](https://stacks.math.columbia.edu/tag/0EW6)
* [Stacks Project, Tag 0EW5](https://stacks.math.columbia.edu/tag/0EW5)
* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- The complement of the exceptional divisor is the image of the open immersion of the preimage
of the complement of the centre. -/
public theorem range_preimage_compl_support_ι_eq_compl {X : Scheme.{u}} (I : X.IdealSheafData) :
    Set.range (blowUpToBase I ⁻¹ᵁ I.support.compl).ι.base =
      (Set.range (exceptionalIdeal I).subschemeι.base)ᶜ := by
  rw [Scheme.Opens.range_ι, Scheme.IdealSheafData.range_subschemeι, exceptionalIdeal,
    Scheme.IdealSheafData.support_comap]
  rfl

/-- **Stacks Project, Tag 0EW6.** Let `X` be a scheme and `Z ⊆ X` the closed subscheme cut out by
a quasi-coherent ideal `I` of finite type (finitely generated on every affine open), with blowup
square
```
E --j--> X'
|π       |b
v        v
Z --i--> X
```
(`X'` the blowup of `X` in `I`, `E = b⁻¹(Z)` the exceptional divisor, `c = i ∘ π = b ∘ j`).
Let `K'` be an object of `D⁺(X'_étale)` (bounded below: `K'.IsGE n₁`) with torsion cohomology
sheaves, `L` an object of `D⁺(Z_étale)` (`L.IsGE n₂`), and `γ : K'|_E ≅ L|_E` an isomorphism,
where `N|_Y` is the derived inverse image. Then there are an object `K` of `D⁺(X_étale)` and
isomorphisms `f : K|_{X'} ≅ K'`, `g : K|_Z ≅ L` such that `γ = g|_E ∘ f⁻¹|_E` (both sides read
through the canonical identifications `(K|_{X'})|_E ≅ K|_E ≅ (K|_Z)|_E`). Moreover, given an
object `M` of `D⁺(X_étale)` with torsion cohomology sheaves and morphisms `α : K' ⟶ M|_{X'}`,
`β : L ⟶ M|_Z` with `α|_E = β|_E ∘ γ` (read through `(M|_{X'})|_E ≅ M|_E ≅ (M|_Z)|_E`), there is a
morphism `K ⟶ M` in `D(X_étale)` whose restriction to `X'` is `α ∘ f` and whose restriction to
`Z` is `β ∘ g`.

The source writes the last morphism as `M ⟶ K` with restrictions `a ∘ f`, `b ∘ g`; these are
typos for `α ∘ f : K|_{X'} ⟶ M|_{X'}` and `β ∘ g : K|_Z ⟶ M|_Z`, which forces the direction
`K ⟶ M`, the direction of the morphism of triangles in the source's proof. The source's
hypothesis that `L` has torsion cohomology sheaves is not needed and is omitted. -/
@[stacks 0EW6]
public theorem exists_gluing_blowUp {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens, (I.ideal U).FG)
    (K' : DerivedCategory (Sheaf (blowUp I).smallEtaleTopology AddCommGrpCat.{u + 1})) (n₁ : ℤ)
    (hK' : K'.IsGE n₁)
    (hK'T : Stacks.Torsion.torsionCohomologyProperty.{u + 1} (blowUp I).smallEtaleTopology K')
    (L : DerivedCategory (Sheaf I.subscheme.smallEtaleTopology AddCommGrpCat.{u + 1})) (n₂ : ℤ)
    (hL : L.IsGE n₂)
    (γ : (etaleAbelianDerivedInverseImage.{u, 0} (exceptionalIdeal I).subschemeι).obj K' ≅
      (etaleAbelianDerivedInverseImage.{u, 0} (exceptionalDivisorToCenter I)).obj L) :
    ∃ (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (_ : K.IsGE (min n₁ n₂))
      (f : (etaleAbelianDerivedInverseImage.{u, 0} (blowUpToBase I)).obj K ≅ K')
      (g : (etaleAbelianDerivedInverseImage.{u, 0} I.subschemeι).obj K ≅ L),
      γ.hom = (etaleAbelianDerivedInverseImage.{u, 0} (exceptionalIdeal I).subschemeι).map f.inv ≫
          (etaleAbelianDerivedInverseImageCompIso'.{u, 0} (exceptionalIdeal I).subschemeι
            (blowUpToBase I) _ rfl).inv.app K ≫
          (etaleAbelianDerivedInverseImageCompIso'.{u, 0} (exceptionalDivisorToCenter I)
            I.subschemeι _ (isPullback_exceptionalDivisor I).w).hom.app K ≫
          (etaleAbelianDerivedInverseImage.{u, 0} (exceptionalDivisorToCenter I)).map g.hom ∧
      ∀ (M : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) (m : ℤ),
        M.IsGE m →
        Stacks.Torsion.torsionCohomologyProperty.{u + 1} X.smallEtaleTopology M →
        ∀ (α : K' ⟶ (etaleAbelianDerivedInverseImage.{u, 0} (blowUpToBase I)).obj M)
          (β : L ⟶ (etaleAbelianDerivedInverseImage.{u, 0} I.subschemeι).obj M),
          (etaleAbelianDerivedInverseImage.{u, 0} (exceptionalIdeal I).subschemeι).map α ≫
              (etaleAbelianDerivedInverseImageCompIso'.{u, 0} (exceptionalIdeal I).subschemeι
                (blowUpToBase I) _ rfl).inv.app M ≫
              (etaleAbelianDerivedInverseImageCompIso'.{u, 0} (exceptionalDivisorToCenter I)
                I.subschemeι _ (isPullback_exceptionalDivisor I).w).hom.app M =
            γ.hom ≫ (etaleAbelianDerivedInverseImage.{u, 0} (exceptionalDivisorToCenter I)).map β →
          ∃ φ : K ⟶ M, (etaleAbelianDerivedInverseImage.{u, 0} (blowUpToBase I)).map φ = f.hom ≫ α ∧
            (etaleAbelianDerivedInverseImage.{u, 0} I.subschemeι).map φ = g.hom ≫ β := by
  have : K'.IsGE n₁ := hK'
  have : L.IsGE n₂ := hL
  exact exists_gluing_of_isPullback_of_cohomologyCommutesWithBaseChange.{u, 0}
    I.subschemeι (blowUpToBase I) (exceptionalIdeal I).subschemeι (exceptionalDivisorToCenter I)
    _ (isPullback_exceptionalDivisor I).w rfl (Scheme.Opens.ι I.support.compl)
    (range_subschemeι_compl_eq I) (isPullback_exceptionalDivisor I)
    _ (range_preimage_compl_support_ι_eq_compl I) _
    (isPullback_blowUpToBase_restrict_compl_support I)
    (cohomologyCommutesWithBaseChange_blowUpToBase_of_fg I hI) K' L (min n₁ n₂)
    (DerivedCategory.TStructure.t.isGE_of_ge K' (min n₁ n₂) n₁ (min_le_left _ _))
    (DerivedCategory.TStructure.t.isGE_of_ge L (min n₁ n₂) n₂ (min_le_right _ _)) hK'T γ

end AlgebraicGeometry

end
