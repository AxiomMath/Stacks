module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoid
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectEssSurj
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectExplicit

/-!
# The quasi-compact quasi-separated fibre of Stacks Tag 0EXE, in groupoids

Stacks Tag 0EXE closes with: *if `U` is quasi-compact and quasi-separated, then `𝒮_U` is
`colim_F Vect(U)`*. Its `𝒮` is a category fibred **in groupoids**, the structure functor
`AlgebraicGeometry.frobeniusVectorBundleGroupoidFibration`, so its fibre `𝒮_U` is a groupoid,
while `colim_F Vect(U)` is not one (already `Hom((𝒪_U, 0), (𝒪_U, 0))` is the perfection of
`Γ(U, 𝒪_U)`, in which `0` is not invertible as soon as `U` is nonempty). The faithful reading of
the clause for a category fibred in groupoids is therefore that `𝒮_U` is the **maximal
subgroupoid** of `colim_F Vect(U)`, and that is what this file proves, with the actual colimit
`AlgebraicGeometry.frobeniusColimitVect` in `Cat` of Stacks Tag 0EXA on the right.

The proof is the one the tag gives ("the final assertion is the content of Lemma 0EXB"):

* the fibre is the groupoid of finite locally free modules over `bigHFrobeniusColimitRingSheaf U`,
  which is `AlgebraicGeometry.frobeniusVectorBundleGroupoidFiberEquiv`; that ring sheaf *is*
  `AlgebraicGeometry.frobeniusColimitRingSheaf U` (it is an `abbrev` for it);
* the finite locally free objects of a core are the core of the finite locally free objects,
  `CategoryTheory.ObjectProperty.coreFullSubcategoryEquiv`;
* Stacks Tag 0EXB, `AlgebraicGeometry.frobeniusColimitVectEquivalence`, identifies the finite
  locally free `colim_F 𝒪_U`-modules with the explicit category of pairs `(ℰ, n)`, and Stacks Tag
  0EXA, `AlgebraicGeometry.frobeniusColimitVectModelEquivalence`, identifies that with the
  colimit in `Cat`; an equivalence passes to cores, `CategoryTheory.Equivalence.core`.

## Main definitions

* `CategoryTheory.ObjectProperty.coreFullSubcategoryEquiv`: for a property `P` of objects of `C`,
  the objects of `Core C` whose underlying object satisfies `P` form the core of
  `P.FullSubcategory`.
* `AlgebraicGeometry.frobeniusVectorBundleGroupoidFiberEquivCoreColimitVect`: **Stacks Tag 0EXE,
  the "moreover" clause, for the category fibred in groupoids**: for `U` quasi-compact and
  quasi-separated, the fibre over `U` is the maximal subgroupoid of `colim_F Vect(U)`.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Frobenius

namespace CategoryTheory.ObjectProperty

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] (P : ObjectProperty C)

/-- **The full subcategory of a core is the core of the full subcategory.** For a property `P` of
objects of `C`, the objects of `Core C` whose underlying object satisfies `P`, with the
isomorphisms of `C` between them, are the core of `P.FullSubcategory`: both have the objects of
`C` satisfying `P` as objects and the isomorphisms of `C` between them as morphisms. -/
def coreFullSubcategoryEquiv :
    ObjectProperty.FullSubcategory (fun X : Core C => P X.of) ≌ Core P.FullSubcategory where
  functor :=
    { obj X := ⟨⟨X.obj.of, X.property⟩⟩
      map f := ⟨P.isoMk f.hom.iso⟩ }
  inverse :=
    { obj X := ⟨⟨X.of.obj⟩, X.of.property⟩
      map f := homMk ⟨P.ι.mapIso f.iso⟩ }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry

universe u

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (p : ℕ) [Fact p.Prime]
  (hpS : IsInCharacteristic S p)

include hpS

/-- **Stacks Tag 0EXE, the "moreover" clause.** Let `S` be a scheme in characteristic `p` and let
`U` be an object of `(Sch/S)_h` whose underlying scheme is quasi-compact and quasi-separated.
Then the fibre `𝒮_U` over `U` of the category fibred in groupoids `𝒮 ⟶ (Sch/S)_h` of finite
locally free `colim_F 𝒪`-modules is `colim_F Vect(U)`, read as a groupoid: it is equivalent to the
maximal subgroupoid of the colimit `colim_F Vect(U)` in `Cat` of Stacks Tag 0EXA.

The fibre is the groupoid of finite locally free modules over `colim_F 𝒪_U`
(`AlgebraicGeometry.frobeniusVectorBundleGroupoidFiberEquiv`), which is the core of the category
of such modules (`CategoryTheory.ObjectProperty.coreFullSubcategoryEquiv`); Stacks Tag 0EXB
(`AlgebraicGeometry.frobeniusColimitVectEquivalence`) and Stacks Tag 0EXA
(`AlgebraicGeometry.frobeniusColimitVectModelEquivalence`) identify that category with
`colim_F Vect(U)`, and the identification passes to cores. -/
@[stacks 0EXE "moreover: if U is quasi-compact and quasi-separated, then the fibre S_U of the \
category fibred in groupoids S over (Sch/S)_h is colim_F Vect(U), as its maximal subgroupoid"]
def frobeniusVectorBundleGroupoidFiberEquivCoreColimitVect (U : BigHOver B S hS)
    [CompactSpace ((BigHOver.toScheme B S hS).obj U)]
    [QuasiSeparatedSpace ((BigHOver.toScheme B S hS).obj U)] :
    (frobeniusVectorBundleGroupoidFibration B S hS p hpS).Fiber U ≌
      Core (frobeniusColimitVect ((BigHOver.toScheme B S hS).obj U) p
        (isInCharacteristic_bigHOver B S hS p hpS U)) :=
  (frobeniusVectorBundleGroupoidFiberEquiv B S hS p hpS U).trans <|
    (ObjectProperty.coreFullSubcategoryEquiv _).trans <|
      ((frobeniusColimitVectEquivalence ((BigHOver.toScheme B S hS).obj U) p
          (isInCharacteristic_bigHOver B S hS p hpS U)).symm.trans
        (frobeniusColimitVectModelEquivalence ((BigHOver.toScheme B S hS).obj U) p
          (isInCharacteristic_bigHOver B S hS p hpS U))).core

end AlgebraicGeometry

end
