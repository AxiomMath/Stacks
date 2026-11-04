module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentSquareIso
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentCanonicalExtZero
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposTransitivityTriangleDerived

/-!
# The naive cotangent complex under an isomorphism of the base ring

For a homomorphism `a : A ⟶ B` of sheaves of commutative rings and an isomorphism `e : A ≅ A'`
with `a = e ≫ a'`, the naive cotangent complexes `NL_{B/A}` and `NL_{B/A'}` are isomorphic as
complexes of `B`-modules (the square of [Stacks Project, Tag 08TX] with the identity of `B` on
the right), and hence so are the groups `Ext^n_B(NL_{B/A}, 𝒢)` and `Ext^n_B(NL_{B/A'}, 𝒢)`.

## Main definitions

* `Stacks.SheafOfModules.naiveCotangentComplexIsoOfBaseIso`: `NL_{B/A} ≅ NL_{B/A'}`.
* `Stacks.SheafOfModules.naiveCotangentExtAddEquivOfBaseIso`:
  `Ext^n_B(NL_{B/A}, 𝒢) ≃+ Ext^n_B(NL_{B/A'}, 𝒢)`.

## References

* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u w z t

namespace Stacks.SheafOfModules

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]
  {A A' B : Sheaf J CommRingCat.{w}} (e : A ≅ A') (a : A ⟶ B) (a' : A' ⟶ B)
  (h : a = e.hom ≫ a')

/-- **`NL_{B/A} ≅ NL_{B/A'}` for an isomorphism `e : A ≅ A'` over `B`**: the identification of
Stacks 08TX for the square with `e` on the left and the identity of `B` on the right, read over
`B` along the identity. -/
def naiveCotangentComplexIsoOfBaseIso :
    naiveCotangentComplex.{v, u, w, z} J A B a ≅ naiveCotangentComplex.{v, u, w, z} J A' B a' :=
  naiveCotangentComplexIsoOfSquare.{v, u, w, z} J A B a A' B a' e (Iso.refl B)
      (by rw [h, Iso.refl_hom, Category.comp_id]) ≪≫
    _root_.SheafOfModules.restrictScalarsIdComplexIso _
      (by rw [Iso.refl_hom]; exact (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map_id B)
      _

variable [HasDerivedCategory.{t}
  (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))]
  (G : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))

/-- **`Ext^n_B(NL_{B/A}, 𝒢) ≃+ Ext^n_B(NL_{B/A'}, 𝒢)` for an isomorphism `e : A ≅ A'` over
`B`**, induced by `Stacks.SheafOfModules.naiveCotangentComplexIsoOfBaseIso`. -/
def naiveCotangentExtAddEquivOfBaseIso (n : ℤ) :
    naiveCotangentExt.{v, u, w, z, t} J A B a G n ≃+
      naiveCotangentExt.{v, u, w, z, t} J A' B a' G n :=
  (Linear.homCongr ℤ (DerivedCategory.Q.mapIso
      (naiveCotangentComplexIsoOfBaseIso.{v, u, w, z} J e a a' h)) (Iso.refl _)).toAddEquiv

end Stacks.SheafOfModules

end
