module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamColumnZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamZigzag07Q9

/-!
# A morphism of cosimplicial pairs on the column zero

A morphism `F : W ⟶ W'` of cosimplicial pairs over a morphism `g : E ⟶ E'` of cosimplicial
divided power algebras induces a morphism `F.columnMap 0` of the columns zero
`M(b) ⊗̂_{D(b)} Ω^0_{D(b)}` of the two double complexes.  When the modules are `p`-adically
complete, `Crystalline.CosimplicialCompletedModule.columnZeroIso` identifies each column zero
with the cosimplicial module `M(•)` itself.  This file shows that through these identifications
`F.columnMap 0` is the morphism `M(•) ⟶ M'(•)` given by the components of `F`, and so the induced
morphism of the Moore complexes of the columns zero is the Moore complex of that morphism.  This
is used in the proof of [Stacks, Lemma 60.22.4, Tag 07Q9].

## Main definitions

* `Crystalline.CosimplicialCompletedPair.Hom.carrierMap07Q9` — the morphism of cosimplicial
  abelian groups `M(•) ⟶ M'(•)` given by the components of `F`.

## Main results

* `Crystalline.CosimplicialDPAlgebra.Hom.formsZeroEquiv_formsMap07Q9` — in exterior degree zero
  the forms map of `g` is `g` itself.
* `Crystalline.CosimplicialCompletedPair.Hom.columnZeroEquiv_tensorApp07Q9` — the induced map of
  the columns zero is the component of `F`, through the identifications.
* `Crystalline.CosimplicialCompletedPair.Hom.columnMap_zero_columnZeroIso07Q9` and
  `...columnZeroMooreMap_columnZeroIso07Q9` — the same on cosimplicial objects and on Moore
  complexes.

## References

* [Stacks Project, Lemma 60.22.4, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory AlgebraicTopology
open DividedPowers
open scoped TensorProduct

namespace Crystalline

namespace CosimplicialDPAlgebra.Hom

variable {A : Type u} [CommRing A] {E E' : CosimplicialDPAlgebra.{u, v} A} (g : E.Hom E')
  (p : ℕ)

/-- **In exterior degree zero the forms map of a morphism of cosimplicial divided power algebras
is the morphism itself**, through the identifications `Ω^0_{D(b)} ≅ D(b)`, for every element of
the completed forms.  Both sides are composites of completions of maps of the uncompleted
objects, which agree by `Crystalline.mapDifferentialFormsOfDPMorphism_zero`. -/
theorem formsZeroEquiv_formsMap07Q9 (b : ℕ) (omega : E.forms p 0 b) :
    E'.formsZeroEquiv p b (g.formsMap p b 0 omega) =
      g.completedRingMap p b (E.formsZeroEquiv p b omega) := by
  have hleft := adicCompletionMapₛₗ_comp_apply
    (mapDifferentialFormsOfDPMorphism (A := A) (J := E.ideal b)
      (delta := E.dividedPowers b) (E'.dividedPowers b) (g.app b) (g.isDPMorphism b) 0)
    (exteriorPower.zeroEquiv (E'.carrier b)
      (dividedPowerDifferentials (A := A) (E'.dividedPowers b))).toLinearMap
    ((ringHomₛₗ (g.app b).toRingHom).comp
      (exteriorPower.zeroEquiv (E.carrier b)
        (dividedPowerDifferentials (A := A) (E.dividedPowers b))).toLinearMap)
    (map_pAdicIdeal_le p (g.app b).toRingHom) (le_of_eq (Ideal.map_id _))
    (map_pAdicIdeal_le p (g.app b).toRingHom)
    (fun y => (mapDifferentialFormsOfDPMorphism_zero A (E.dividedPowers b)
      (E'.dividedPowers b) (g.app b) (g.isDPMorphism b) y).symm) omega
  have hright := adicCompletionMapₛₗ_comp_apply
    (exteriorPower.zeroEquiv (E.carrier b)
      (dividedPowerDifferentials (A := A) (E.dividedPowers b))).toLinearMap
    (ringHomₛₗ (g.app b).toRingHom)
    ((ringHomₛₗ (g.app b).toRingHom).comp
      (exteriorPower.zeroEquiv (E.carrier b)
        (dividedPowerDifferentials (A := A) (E.dividedPowers b))).toLinearMap)
    (le_of_eq (Ideal.map_id _)) (map_pAdicIdeal_le p (g.app b).toRingHom)
    (map_pAdicIdeal_le p (g.app b).toRingHom) (fun _ => rfl) omega
  have e : ∀ (D : CosimplicialDPAlgebra.{u, v} A) (x : D.forms p 0 b),
      D.formsZeroEquiv p b x =
        adicCompletionMapₛₗ
          (exteriorPower.zeroEquiv (D.carrier b)
            (dividedPowerDifferentials (A := A) (D.dividedPowers b))).toLinearMap
          (le_of_eq (Ideal.map_id (pAdicIdeal (A := D.carrier b) p))) x :=
    fun _ _ => adicCompletionMap_eq_mapₛₗ _ _ _
  rw [e E', e E]
  exact hleft.symm.trans hright

end CosimplicialDPAlgebra.Hom

namespace CosimplicialCompletedPair.Hom

variable {A : Type u} [CommRing A] {E E' : CosimplicialDPAlgebra.{u, v} A} {p : ℕ}
  {g : E.Hom E'} {W : CosimplicialCompletedPair.{u, v, w} E p}
  {W' : CosimplicialCompletedPair.{u, v, w} E' p} (F : Hom g W W')

/-- The morphism of cosimplicial abelian groups `M(•) ⟶ M'(•)` given by the components of a
morphism of cosimplicial pairs, in the universe of the modules. -/
def carrierMapSmall07Q9 :
    W.toCosimplicialCompletedModule.carrierCosimplicialSmall ⟶
      W'.toCosimplicialCompletedModule.carrierCosimplicialSmall where
  app n := AddCommGrpCat.ofHom (F.app n.len).toAddMonoidHom
  naturality _ _ φ := AddCommGrpCat.ext fun x => F.naturality φ x

/-- **The morphism of cosimplicial abelian groups `M(•) ⟶ M'(•)` given by the components of a
morphism of cosimplicial pairs**, in the universe of the double complexes. -/
def carrierMap07Q9 :
    W.toCosimplicialCompletedModule.carrierCosimplicial ⟶
      W'.toCosimplicialCompletedModule.carrierCosimplicial :=
  Functor.whiskerRight F.carrierMapSmall07Q9 AddCommGrpCat.uliftFunctor

/-- The morphism `M(•) ⟶ M'(•)` on elements. -/
theorem carrierMap07Q9_app_down (n : SimplexCategory)
    (x : W.toCosimplicialCompletedModule.carrierCosimplicial.obj n) :
    (F.carrierMap07Q9.app n x).down = F.app n.len x.down :=
  rfl

variable [∀ b, IsAdicComplete (pAdicIdeal (A := E.completedRing p b) p) (W.carrier b)]
  [∀ b, IsAdicComplete (pAdicIdeal (A := E'.completedRing p b) p) (W'.carrier b)]

/-- **Through the identifications of the columns zero with the modules, the induced map of the
columns zero is the component of the morphism.**  This is
`Crystalline.CompletedDeRham.comparisonValues_unitEquiv`, the compatibility of the forms it asks
for being `Crystalline.CosimplicialDPAlgebra.Hom.formsZeroEquiv_formsMap07Q9`. -/
theorem columnZeroEquiv_tensorApp07Q9 (b : ℕ) (x : W.toCosimplicialCompletedModule.obj 0 b) :
    W'.toCosimplicialCompletedModule.columnZeroEquiv b (F.tensorApp 0 b x) =
      F.app b (W.toCosimplicialCompletedModule.columnZeroEquiv b x) :=
  CompletedDeRham.comparisonValues_unitEquiv p (E.completedRing p b) (E'.completedRing p b)
    (g.completedRingMap p b) (W.carrier b) (W'.carrier b) (F.app b) (E.forms p 0 b)
    (E'.forms p 0 b) (g.formsMap p b 0) (E.formsZeroEquiv p b) (E'.formsZeroEquiv p b)
    (F.tensorApp 0 b) (fun _ => rfl) (fun omega => g.formsZeroEquiv_formsMap07Q9 p b omega) x

/-- **On the columns zero, identified with the cosimplicial modules, the morphism of double
complexes induced by `F` is the morphism `M(•) ⟶ M'(•)` given by the components of `F`.** -/
theorem columnMap_zero_columnZeroIso07Q9 :
    F.columnMap 0 ≫ W'.toCosimplicialCompletedModule.columnZeroIso.hom =
      W.toCosimplicialCompletedModule.columnZeroIso.hom ≫ F.carrierMap07Q9 :=
  NatTrans.ext (funext fun n => AddCommGrpCat.ext fun x =>
    ULift.ext _ _ (F.columnZeroEquiv_tensorApp07Q9 n.len x))

/-- **The morphism of the Moore complexes of the columns zero induced by `F` is, through the
identifications of the columns zero with the cosimplicial modules, the Moore complex of the
morphism `M(•) ⟶ M'(•)` given by the components of `F`.** -/
theorem columnZeroMooreMap_columnZeroIso07Q9 :
    F.columnZeroMooreMap ≫ (alternatingCofaceMapComplex AddCommGrpCat.{max v w}).map
        W'.toCosimplicialCompletedModule.columnZeroIso.hom =
      (alternatingCofaceMapComplex AddCommGrpCat.{max v w}).map
          W.toCosimplicialCompletedModule.columnZeroIso.hom ≫
        (alternatingCofaceMapComplex AddCommGrpCat.{max v w}).map F.carrierMap07Q9 :=
  ((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).map_comp (F.columnMap 0)
      W'.toCosimplicialCompletedModule.columnZeroIso.hom).symm.trans
    ((congrArg (alternatingCofaceMapComplex AddCommGrpCat.{max v w}).map
        F.columnMap_zero_columnZeroIso07Q9).trans
      ((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).map_comp _ _))

end CosimplicialCompletedPair.Hom

end Crystalline

end
