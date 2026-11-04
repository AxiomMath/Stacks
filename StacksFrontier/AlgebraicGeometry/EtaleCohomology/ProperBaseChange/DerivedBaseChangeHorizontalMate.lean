module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CompositeMorphismBaseChange

/-!
# The derived étale base change map as a mate along the horizontal adjunctions

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes. `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange`, the
base change map `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` on unbounded derived categories of abelian
sheaves on the small étale sites, is described by
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_eq_mateEquiv` as the mate, along the two
**vertical** derived adjunctions `f^{-1} ⊣ Rf_*` and `(f')^{-1} ⊣ Rf'_*`, of the comparison of
the two composite derived *inverse* images around the square. This file rewrites it as the
inverse mate, along the two **horizontal** derived adjunctions `g^{-1} ⊣ Rg_*` and
`(g')^{-1} ⊣ Rg'_*`, of the comparison `Rg'_* ⋙ Rf_* ≅ RP_* ≅ Rf'_* ⋙ Rg_*` of the two composite
derived *direct* images, and records the resulting compatibility of the base change map with the
units of the horizontal adjunctions.

This is the derived analogue of
`Stacks.EtaleCohomology.etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso`, and the
argument is the same formal one: iterating the vertical and the horizontal mate operations gives
the conjugate (`CategoryTheory.iterated_mateEquiv_conjugateEquiv`), the conjugate of a composite
is the composite of the conjugates (`CategoryTheory.conjugateEquiv_comp`), and the derived
direct-image composition comparison
`Stacks.EtaleCohomology.etaleAbelianDerivedDirectImageCompIso'` is by definition the conjugate
of the derived inverse-image one.

## Main results

* `etaleAbelianDerivedBaseChange_eq_mateEquiv_symm_derivedDirectImageCompIso`
  — **the derived base change map is the inverse horizontal mate of the comparison of the two
  composite derived direct images around the square.**
* `etaleAbelianDerivedAdjunction_unit_app_comp_map_etaleAbelianDerivedBaseChange`
  — the unit of `g^{-1} ⊣ Rg_*` followed by `Rg_*` of the base change map equals `Rf_*` of the
  unit of `(g')^{-1} ⊣ Rg'_*` followed by the comparison of composite direct images.

## Implementation notes

As in `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_eq_mateEquiv`, the common composite
`X' ⟶ Y` around the square is carried as a named morphism `P` with the two equations naming it,
so that the two derived direct-image composition comparisons both land on `RP_*` and compose
without an intervening `eqToIso`; the adjunction for `P` is the middle one in the factorization
of the conjugate given by `CategoryTheory.conjugateEquiv_comp`.

## References

* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

/-- **The derived étale base change map is the inverse mate, along the two horizontal derived
adjunctions, of the comparison of the two composite derived direct images around the square.**
For a commutative square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
and a named morphism `P : X' ⟶ Y` presenting the common composite, the base change map
`g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` of `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange`
corresponds, under `(g')^{-1} ⊣ Rg'_*` and `g^{-1} ⊣ Rg_*`, to the isomorphism
`Rg'_* ⋙ Rf_* ≅ RP_* ≅ Rf'_* ⋙ Rg_*`.

The proof starts from the vertical mate description
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_eq_mateEquiv`, takes the horizontal mate
by `CategoryTheory.iterated_mateEquiv_conjugateEquiv`, and splits the resulting conjugate at the
adjunction for `P` by `CategoryTheory.conjugateEquiv_comp`; the two factors are, by definition,
the two derived direct-image composition comparisons. -/
public theorem etaleAbelianDerivedBaseChange_eq_mateEquiv_symm_derivedDirectImageCompIso
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hyp : g' ≫ f = f' ≫ g) (P : X' ⟶ Y) (hP₁ : P = g' ≫ f) (hP₂ : P = f' ≫ g) :
    etaleAbelianDerivedBaseChange.{u, v} f g g' f' hyp =
      ((mateEquiv (etaleAbelianDerivedAdjunction.{u, v} g')
          (etaleAbelianDerivedAdjunction.{u, v} g)).symm
        (TwoSquare.mk _ _ _ _
          ((etaleAbelianDerivedDirectImageCompIso'.{u, v} g' f P hP₁).inv ≫
            (etaleAbelianDerivedDirectImageCompIso'.{u, v} f' g P hP₂).hom))).natTrans := by
  rw [etaleAbelianDerivedBaseChange_eq_mateEquiv.{u, v} f g g' f' P hP₁ hP₂]
  refine congrArg TwoSquare.natTrans ((Equiv.eq_symm_apply _).2 ?_)
  refine (iterated_mateEquiv_conjugateEquiv
    (etaleAbelianDerivedAdjunction.{u, v} f)
    (etaleAbelianDerivedAdjunction.{u, v} f')
    (etaleAbelianDerivedAdjunction.{u, v} g)
    (etaleAbelianDerivedAdjunction.{u, v} g') _).trans ?_
  rw [etaleAbelianDerivedSquare, TwoSquare.mk,
    ← conjugateEquiv_comp (adj₂ := etaleAbelianDerivedAdjunction.{u, v} P)]
  rfl

/-- **Compatibility of the derived base change map with the horizontal units.** For a
commutative square as in
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_eq_mateEquiv_symm_derivedDirectImageCompIso`
and `M` in the derived category of abelian sheaves on `X`, the unit `η^g_{Rf_* M}` followed by
`Rg_*(β_M)`, with `β` the derived base change map, equals `Rf_*(η^{g'}_M)` followed by the
comparison `Rf_* Rg'_* ≅ RP_* ≅ Rg_* Rf'_*` at `(g')^{-1} M`.

This is `CategoryTheory.unit_mateEquiv_symm` applied to the horizontal mate description of the
base change map. -/
public theorem etaleAbelianDerivedAdjunction_unit_app_comp_map_etaleAbelianDerivedBaseChange
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hyp : g' ≫ f = f' ≫ g) (P : X' ⟶ Y) (hP₁ : P = g' ≫ f) (hP₂ : P = f' ≫ g)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    (etaleAbelianDerivedAdjunction.{u, v} g).unit.app
        ((etaleAbelianDerivedDirectImage.{u, v} f).obj M) ≫
      (etaleAbelianDerivedDirectImage.{u, v} g).map
        ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' hyp).app M) =
    (etaleAbelianDerivedDirectImage.{u, v} f).map
        ((etaleAbelianDerivedAdjunction.{u, v} g').unit.app M) ≫
      (etaleAbelianDerivedDirectImageCompIso'.{u, v} g' f P hP₁).inv.app
        ((etaleAbelianDerivedInverseImage.{u, v} g').obj M) ≫
      (etaleAbelianDerivedDirectImageCompIso'.{u, v} f' g P hP₂).hom.app
        ((etaleAbelianDerivedInverseImage.{u, v} g').obj M) := by
  rw [etaleAbelianDerivedBaseChange_eq_mateEquiv_symm_derivedDirectImageCompIso.{u, v}
    f g g' f' hyp P hP₁ hP₂]
  exact (unit_mateEquiv_symm (etaleAbelianDerivedAdjunction.{u, v} g')
    (etaleAbelianDerivedAdjunction.{u, v} g)
    (TwoSquare.mk _ _ _ _
      ((etaleAbelianDerivedDirectImageCompIso'.{u, v} g' f P hP₁).inv ≫
        (etaleAbelianDerivedDirectImageCompIso'.{u, v} f' g P hP₂).hom)) M).symm

end Stacks.EtaleCohomology

end
