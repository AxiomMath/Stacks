module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageCompositionUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.ProjectionFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedBaseChangeUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.ProjectionMap

/-!
# The Künneth map of a commutative square, through projection formulas and base change

Let `Λ` be a commutative ring and let
```
P --q--> Y
|p       |g
v        v
X --f--> S
```
be a commutative square of schemes, `p ≫ f = q ≫ g`, with diagonal `c = q ≫ g`. For `E` in
`D(X_étale, Λ)` and `K` in `D(Y_étale, Λ)` this file builds the map

`Rf_*E ⊗^L_Λ Rg_*K ⟶ Rc_*(p^{-1}E ⊗^L_Λ q^{-1}K)`

of [Stacks, Tag 0F1E] as the composite which the proof of [Stacks, Tag 0F14] runs through:

`Rf_*E ⊗ Rg_*K ≅ Rg_*K ⊗ Rf_*E` (symmetry of `⊗^L_Λ`)
`⟶ Rg_*(K ⊗ g^{-1}Rf_*E)` (the projection map of [Stacks, Tag 0943] for `g`)
`⟶ Rg_*(K ⊗ Rq_*p^{-1}E)` (`Rg_*(K ⊗ -)` of the base change map of [Stacks, Tag 0A2A])
`≅ Rg_*(Rq_*p^{-1}E ⊗ K)` (symmetry)
`⟶ Rg_*Rq_*(p^{-1}E ⊗ q^{-1}K)` (`Rg_*` of the projection map for `q`)
`≅ Rc_*(p^{-1}E ⊗ q^{-1}K)` (Leray, `Rc_* = Rg_* ∘ Rq_*`).

Over `S = Spec(k)` with `k` separably closed, `Rf_*`, `Rg_*` and `Rc_*` are `RΓ(X, -)`,
`RΓ(Y, -)` and `RΓ(X ×_k Y, -)`, and this is the map of the statement of Tag 0F14.

## Main definitions

* `Stacks.EtaleCohomology.etaleKunnethCompositeMap`: the composite above.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleKunnethCompositeMap`: it is invertible as soon as the base
  change map at `E` and the two projection maps are.

## References

* [Stacks Project, Tag 0F14](https://stacks.math.columbia.edu/tag/0F14)
* [Stacks Project, Tag 0F1E](https://stacks.math.columbia.edu/tag/0F1E)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] {S X Y P : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  (p : P ⟶ X) (q : P ⟶ Y) (h : p ≫ f = q ≫ g)

/-- **The Künneth map** `Rf_*E ⊗^L_Λ Rg_*K ⟶ R(q ≫ g)_*(p^{-1}E ⊗^L_Λ q^{-1}K)` of a commutative
square `p ≫ f = q ≫ g` of schemes, as the composite of the symmetry of `⊗^L_Λ`, the projection
map for `g`, the base change map `g^{-1}Rf_* ⟶ Rq_*p^{-1}`, the projection map for `q` and the
Leray isomorphism `R(q ≫ g)_* ≅ Rg_* ∘ Rq_*`. -/
def etaleKunnethCompositeMap (E : DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    ((etaleDerivedTensor.{u, r} Λ S).obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj E)).obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).obj K) ⟶
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ (q ≫ g)).obj
        (((etaleDerivedTensor.{u, r} Λ P).obj
          ((etaleModuleDerivedInverseImage.{u, r} Λ p).obj E)).obj
          ((etaleModuleDerivedInverseImage.{u, r} Λ q).obj K)) :=
  (etaleDerivedTensorBraidingIso.{u, r} Λ S _ _).hom ≫
    etalePushforwardProjectionMap.{u, r} Λ g K
      ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj E) ≫
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map
      (((etaleDerivedTensor.{u, r} Λ Y).obj K).map
        ((etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ f g p q h).app E)) ≫
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map
      (etaleDerivedTensorBraidingIso.{u, r} Λ Y _ _).hom ≫
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map
      (etalePushforwardProjectionMap.{u, r} Λ q
        ((etaleModuleDerivedInverseImage.{u, r} Λ p).obj E) K) ≫
    ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ q g (q ≫ g) rfl).app _).inv

/-- **The Künneth map is invertible once its three non-trivial factors are**: the base change
map `g^{-1}Rf_*E ⟶ Rq_*p^{-1}E`, the projection map for `g` at `(K, Rf_*E)`, and the projection
map for `q` at `(p^{-1}E, K)`. -/
theorem isIso_etaleKunnethCompositeMap (E : DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y))
    (hbc : IsIso ((etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ f g p q h).app E))
    (hg : IsIso (etalePushforwardProjectionMap.{u, r} Λ g K
      ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj E)))
    (hq : IsIso (etalePushforwardProjectionMap.{u, r} Λ q
      ((etaleModuleDerivedInverseImage.{u, r} Λ p).obj E) K)) :
    IsIso (etaleKunnethCompositeMap.{u, r} Λ f g p q h E K) := by
  dsimp only [etaleKunnethCompositeMap]
  infer_instance

end Stacks.EtaleCohomology

end
