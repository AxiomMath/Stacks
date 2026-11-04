module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInComparison

/-!
# Étale base change for the direct-image algebra, at the level of algebra sheaves

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `g` étale. Then `f'_*𝒪_{X'} ≅ g^*(f_*𝒪_X)` as sheaves of commutative `𝒪_{Y'}`-algebras,
i.e. as `AlgebraicGeometry.Space.AlgebraSheaf`, compatibly with the structure-algebra maps `f♯` of
Stacks 03G8. This is Stacks 03LX for the structure sheaf read as algebras.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardAlgebraEtaleBaseChangeRingIso`: the comparison of
  commutative-ring sheaves underlying the two direct-image algebras.
* `AlgebraicGeometry.Space.pushforwardAlgebraEtaleBaseChangeIso`: étale base change of the
  direct-image algebra, `f'_*𝒪_{X'} ≅ (f_*𝒪_X)|_{Y'}` as sheaves of commutative
  `𝒪_{Y'}`-algebras.
* `AlgebraicGeometry.Space.etaleAlgebraRestrictionPushforwardAlgebraIso`: its inverse,
  `(f_*𝒪_X)|_{Y'} ≅ f'_*𝒪_{X'}`.

## Main results

* `AlgebraicGeometry.Space.structureSharp_comp_directImageAlgebraEtaleBaseChangeRingIso`: the
  ring-level comparison carries `f'♯` to the étale restriction of `f♯`.
* `AlgebraicGeometry.Space.hom_comp_pushforwardAlgebraEtaleBaseChangeRingIso` and
  `AlgebraicGeometry.Space.pushforwardAlgebraEtaleBaseChangeRingIso_algebraMap`: the same
  identity on sheaves of commutative rings, and on sections over an étale chart of `Y'`.

## References

* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y Y' : AlgebraicSpaces B S hS}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-! ### The structure maps, at the level of sheaves of rings -/

/-- The ring-level étale base change of the direct image carries `f'♯` to the étale restriction
of `f♯`. -/
theorem structureSharp_comp_directImageAlgebraEtaleBaseChangeRingIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    structureSharp B S hS f' ≫
        (directImageAlgebraEtaleBaseChangeRingIso B S hS i f' f g sq hg).hom =
      (smallEtaleRingRestriction B S hS g hg).map (structureSharp B S hS f) := by
  rw [← baseChangeStructureSharp_comp_baseChangeRingMap B S hS i f' f g sq hg]
  simp only [directImageAlgebraEtaleBaseChangeRingIso, baseChangeStructureSharp,
    Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rfl

/-- Forgetting commutativity in the structure-algebra map of an étale restriction is the étale
restriction of the structure-algebra map. -/
theorem forgetCommRingSheaf_map_etaleAlgebraRestriction_hom
    (A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (hg : IsEtale B S hS g.hom) :
    (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((etaleAlgebraRestriction.{u, u} B S hS g hg).obj A).hom =
      (smallEtaleRingRestriction B S hS g hg).map
        ((sheafCompose (SmallEtale.topology B S hS Y.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map A.hom) :=
  rfl

/-- The étale restriction of the direct-image algebra has `f♯` for its structure-algebra map,
after forgetting commutativity. -/
theorem forgetCommRingSheaf_map_etaleAlgebraRestriction_pushforwardAlgebra_hom
    (hg : IsEtale B S hS g.hom) :
    (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((etaleAlgebraRestriction.{u, u} B S hS g hg).obj
          (pushforwardAlgebra B S hS (Over.mk f))).hom =
      (smallEtaleRingRestriction B S hS g hg).map (structureSharp B S hS f) :=
  (forgetCommRingSheaf_map_etaleAlgebraRestriction_hom B S hS g
      (pushforwardAlgebra B S hS (Over.mk f)) hg).trans
    (congrArg (fun m : structureRingSheaf B S hS Y ⟶ structureRingSheafDirectImage B S hS f ↦
        (smallEtaleRingRestriction B S hS g hg).map m)
      (forgetCommRingSheaf_map_fSharp B S hS f))

/-! ### The comparison of sheaves of commutative rings -/

/-- Étale base change of the direct-image algebra, at the level of sheaves of commutative
rings: the underlying sheaf of commutative rings of `f'_*𝒪_{X'}` is the étale restriction to
`Y'` of that of `f_*𝒪_X`. -/
def pushforwardAlgebraEtaleBaseChangeRingIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    (pushforwardAlgebra B S hS (Over.mk f')).right ≅
      ((etaleAlgebraRestriction.{u, u} B S hS g hg).obj
        (pushforwardAlgebra B S hS (Over.mk f))).right :=
  (fullyFaithfulForgetCommRingSheaf.{u, u, u + 1}
    (SmallEtale.topology B S hS Y'.1)).preimageIso
      (directImageAlgebraEtaleBaseChangeRingIso B S hS i f' f g sq hg)

/-- The comparison `AlgebraicGeometry.Space.pushforwardAlgebraEtaleBaseChangeRingIso` carries the
structure-algebra map of `f'_*𝒪_{X'}` to that of the étale restriction of `f_*𝒪_X`. -/
theorem hom_comp_pushforwardAlgebraEtaleBaseChangeRingIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    (pushforwardAlgebra B S hS (Over.mk f')).hom ≫
        (pushforwardAlgebraEtaleBaseChangeRingIso B S hS i f' f g sq hg).hom =
      ((etaleAlgebraRestriction.{u, u} B S hS g hg).obj
        (pushforwardAlgebra B S hS (Over.mk f))).hom := by
  let hF := fullyFaithfulForgetCommRingSheaf.{u, u, u + 1} (SmallEtale.topology B S hS Y'.1)
  refine hF.map_injective ?_
  rw [Functor.map_comp]
  erw [forgetCommRingSheaf_map_fSharp B S hS f']
  rw [show ((sheafCompose (SmallEtale.topology B S hS Y'.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).map
      (pushforwardAlgebraEtaleBaseChangeRingIso B S hS i f' f g sq hg).hom) =
      (directImageAlgebraEtaleBaseChangeRingIso B S hS i f' f g sq hg).hom from
    hF.map_preimage _]
  exact (structureSharp_comp_directImageAlgebraEtaleBaseChangeRingIso B S hS i f' f g sq hg).trans
    (forgetCommRingSheaf_map_etaleAlgebraRestriction_pushforwardAlgebra_hom B S hS f g hg).symm

/-- The structure-algebra identity of
`AlgebraicGeometry.Space.hom_comp_pushforwardAlgebraEtaleBaseChangeRingIso`, read on sections
over an étale chart of `Y'`. -/
theorem pushforwardAlgebraEtaleBaseChangeRingIso_algebraMap (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (U : (SmallEtale B S hS Y'.1)ᵒᵖ)
    (r : (structureSheaf B S hS Y'.1 Y'.2).obj.obj U) :
    ((pushforwardAlgebraEtaleBaseChangeRingIso B S hS i f' f g sq hg).hom.hom.app U).hom
        ((pushforwardAlgebra B S hS (Over.mk f')).algebraMap U r) =
      ((etaleAlgebraRestriction.{u, u} B S hS g hg).obj
        (pushforwardAlgebra B S hS (Over.mk f))).algebraMap U r :=
  ConcreteCategory.congr_hom
    (congrArg (fun m : structureSheaf B S hS Y'.1 Y'.2 ⟶
        ((etaleAlgebraRestriction.{u, u} B S hS g hg).obj
          (pushforwardAlgebra B S hS (Over.mk f))).right ↦ m.hom.app U)
      (hom_comp_pushforwardAlgebraEtaleBaseChangeRingIso B S hS i f' f g sq hg)) r

/-! ### The isomorphism of algebra sheaves -/

/-- Étale base change for the direct-image algebra of Stacks 03G8, as an isomorphism of
algebra sheaves: for a cartesian square

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

of algebraic spaces over a scheme `S` contained in a big fppf site `B`, with `g` étale,

`f'_*𝒪_{X'} ≅ (f_*𝒪_X)|_{Y'}`

as sheaves of commutative `𝒪_{Y'}`-algebras on the small étale site of `Y'`. This is Stacks 03LX
for the structure sheaf read as algebras. -/
def pushforwardAlgebraEtaleBaseChangeIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    pushforwardAlgebra B S hS (Over.mk f') ≅
      (etaleAlgebraRestriction.{u, u} B S hS g hg).obj
        (pushforwardAlgebra B S hS (Over.mk f)) where
  hom :=
    { right := (pushforwardAlgebraEtaleBaseChangeRingIso B S hS i f' f g sq hg).hom
      comm := pushforwardAlgebraEtaleBaseChangeRingIso_algebraMap B S hS i f' f g sq hg }
  inv :=
    { right := (pushforwardAlgebraEtaleBaseChangeRingIso B S hS i f' f g sq hg).inv
      comm := fun U r ↦ by
        rw [← pushforwardAlgebraEtaleBaseChangeRingIso_algebraMap B S hS i f' f g sq hg U r]
        exact ConcreteCategory.congr_hom
          (congrArg (fun m : (pushforwardAlgebra B S hS (Over.mk f')).right ⟶
              (pushforwardAlgebra B S hS (Over.mk f')).right ↦ m.hom.app U)
            (pushforwardAlgebraEtaleBaseChangeRingIso B S hS i f' f g sq hg).hom_inv_id)
          ((pushforwardAlgebra B S hS (Over.mk f')).algebraMap U r) }
  hom_inv_id :=
    AlgebraSheaf.Hom.ext (pushforwardAlgebraEtaleBaseChangeRingIso B S hS i f' f g sq hg).hom_inv_id
  inv_hom_id :=
    AlgebraSheaf.Hom.ext (pushforwardAlgebraEtaleBaseChangeRingIso B S hS i f' f g sq hg).inv_hom_id

/-- The étale restriction of `f_*𝒪_X` to `Y'` is the direct image `f'_*𝒪_{X'}` of the structure
sheaf of the base change: the inverse of
`AlgebraicGeometry.Space.pushforwardAlgebraEtaleBaseChangeIso`. -/
def etaleAlgebraRestrictionPushforwardAlgebraIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    (etaleAlgebraRestriction.{u, u} B S hS g hg).obj
        (pushforwardAlgebra B S hS (Over.mk f)) ≅
      pushforwardAlgebra B S hS (Over.mk f') :=
  (pushforwardAlgebraEtaleBaseChangeIso B S hS i f' f g sq hg).symm

end AlgebraicGeometry.Space

end
