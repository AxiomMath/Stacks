module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Effective
public import StacksFrontier.CategoryTheory.Sites.Descent.SingletonCoalgebra

/-!
# Descent of morphisms along one faithfully flat morphism of affine schemes

For a faithfully flat morphism `φ : R ⟶ S` of commutative rings, the Eilenberg–Moore comparison
functor of the adjunction `Stacks.Descent.pullbackQcohAdjunction` between pullback and
pushforward of quasi-coherent modules along `Spec.map φ` is an equivalence, hence bijective on
hom-sets. After forgetting quasi-coherence, the functors and the unit of this adjunction are those
of `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`.

## Main results

* `Stacks.Descent.isEquivalence_comparison_pullbackQcohAdjunction`: the comparison functor of
  `Stacks.Descent.pullbackQcohAdjunction` is an equivalence for a faithfully flat morphism.
* `Stacks.Descent.bijective_comparison_map_pullbackQcoh`: the comparison functor of
  `Stacks.Descent.pullbackQcohAdjunction` is bijective on hom-sets.
* `Stacks.Descent.pullbackQcoh_map_hom`, `Stacks.Descent.pushforwardQcoh_map_hom` and
  `Stacks.Descent.unit_pullbackQcohAdjunction_app_hom`: the functors and the unit of
  `Stacks.Descent.pullbackQcohAdjunction` are those of
  `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` on underlying sheaves of
  modules.

## Implementation notes

`Stacks.Descent.isEquivalence_comparison_pullbackQcohAdjunction` is stated for the named
adjunction `Stacks.Descent.pullbackQcohAdjunction`, not for `CategoryTheory.comonadicAdjunction`,
whose right adjoint is chosen by `CategoryTheory.Functor.rightAdjoint`: the Eilenberg–Moore
coalgebra condition depends on the unit of the adjunction it is read over.

## References

* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe t u

namespace Stacks.Descent

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The Eilenberg–Moore comparison functor of `Stacks.Descent.pullbackQcohAdjunction` along a
faithfully flat morphism of affine schemes is an equivalence. -/
lemma isEquivalence_comparison_pullbackQcohAdjunction (hφ : φ.hom.FaithfullyFlat) :
    (Comonad.comparison (pullbackQcohAdjunction φ)).IsEquivalence :=
  (comonadicPullbackQcoh φ hφ).eqv

/-- For a faithfully flat `φ : R ⟶ S`, a morphism of quasi-coherent modules on `Spec R` is the same
thing as a morphism of their pullbacks to `Spec S` compatible with the coalgebra structure of the
comonad of `Stacks.Descent.pullbackQcohAdjunction`. -/
lemma bijective_comparison_map_pullbackQcoh (hφ : φ.hom.FaithfullyFlat)
    (M N : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory) :
    Function.Bijective ((Comonad.comparison (pullbackQcohAdjunction φ)).map : (M ⟶ N) → _) := by
  have := isEquivalence_comparison_pullbackQcohAdjunction φ hφ
  exact (Functor.FullyFaithful.ofFullyFaithful _).map_bijective M N

/-- Pullback of quasi-coherent modules is pullback of sheaves of modules on morphisms. -/
@[simp]
lemma pullbackQcoh_map_hom
    {M N : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory} (g : M ⟶ N) :
    ((pullbackQcoh φ).map g).hom = (Scheme.Modules.pullback (Spec.map φ)).map g.hom :=
  rfl

/-- Pushforward of quasi-coherent modules is pushforward of sheaves of modules on morphisms. -/
@[simp]
lemma pushforwardQcoh_map_hom
    {M N : (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).FullSubcategory} (g : M ⟶ N) :
    ((pushforwardQcoh φ).map g).hom = (Scheme.Modules.pushforward (Spec.map φ)).map g.hom :=
  rfl

/-- After forgetting quasi-coherence, the unit of the adjunction on quasi-coherent modules is
the unit of the adjunction on all sheaves of modules. -/
@[simp]
lemma unit_pullbackQcohAdjunction_app_hom
    (M : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory) :
    ((pullbackQcohAdjunction φ).unit.app M).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M.obj := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    (L := pullbackQcoh φ) (R := pushforwardQcoh φ)
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
    (Functor.FullyFaithful.ofFullyFaithful
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι)
    (Functor.FullyFaithful.ofFullyFaithful
      (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).ι)
    (Iso.refl _) (Iso.refl _) M
  simp only [ObjectProperty.ι_map, Iso.refl_hom, NatTrans.id_app] at h
  exact h

end Stacks.Descent

end
