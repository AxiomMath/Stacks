module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerPresheafModel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise

/-!
# The presheaf-model comparison on a product of degree-one generators

`SheafOfModules.presheafModelSymmetricPowerIso` compares the sheafification of the sectionwise
degree-`n` symmetric power of a presheaf model `P` of a sheaf of modules `F` with the degree-`n`
symmetric power `Symⁿ F` of a bundle of algebras on `F`. This file computes that comparison on
the local sections that determine it: the elements `∏ i, ι (s i)` of the sectionwise symmetric
power, for local sections `s i` of `P`.

Those products span (`SymmetricAlgebra.symmetricPower_eq_span_prod_ι`), so the equation here
determines the comparison.

## Main results

* `SheafOfModules.sheafifyUnit_homogeneousProd_model`: the sheafification unit carries the
  ordered product of degree-one local sections of the sectionwise symmetric algebra of `P` to
  the ordered product of their images.
* `SheafOfModules.presheafModelSymmetricPowerIso_gen_unit`: the degree-one comparison on the
  unit-image of a sectionwise degree-one generator.
* `SheafOfModules.presheafModelSymmetricPowerIso_prod_ι`: **the comparison carries the
  unit-image of `∏ i, ι (s i)` to the ordered product of the degree-one generators of `Symⁿ F`
  at the sections of `F` corresponding to the `s i`.**

## Implementation notes

The section of `F` attached to a local section `p` of `P` is
`e.inv` applied to the unit-image of `p` — the presheaf model is only given up to the
isomorphism `e`, so the generator of `Symⁿ F` has to be evaluated there.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite

universe v u w

namespace SheafOfModules

open PresheafOfModules Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (P : PresheafOfModules.{w} (toRingCat J Osharp).obj)

/-- **The sheafification unit on an ordered product of degree-one local sections** of the
sectionwise symmetric algebra of an arbitrary presheaf of modules. -/
theorem sheafifyUnit_homogeneousProd_model (n : ℕ) (X : Cᵒᵖ)
    (z : Fin n → (symPowInt (1 : ℤ) P).obj X) :
    Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (symPowInt (n : ℤ) P)) X
        ((symPowIntGradedAlgebra P).homogeneousProd X n z) =
      ((symPowIntGradedAlgebra P).sheafify
          (𝟙 (toRingCat J Osharp).obj)).toPresheafGradedAlgebra.homogeneousProd X n
        (fun i => Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (symPowInt (1 : ℤ) P)) X (z i)) :=
  (symPowIntGradedAlgebra P).homogeneousProd_map
    ((symPowIntGradedAlgebra P).sheafify
      (𝟙 (toRingCat J Osharp).obj)).toPresheafGradedAlgebra X
    (fun m y => Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
      (symPowInt m P)) X y)
    ((symPowIntGradedAlgebra P).sheafify_one_eval
      (𝟙 (toRingCat J Osharp).obj) X).symm
    (fun i j x y => ((symPowIntGradedAlgebra P).sheafify_mul_unit
      (𝟙 (toRingCat J Osharp).obj) i j X x y).symm)
    n z

variable {F : SheafOfModules.{w} (toRingCat J Osharp)}
  (A : TensorExteriorSymmetricAlgebras J F) (e : F ≅ sheafifyModulePresheaf J P)

/-- **The degree-one presheaf-model comparison on a sectionwise generator.** It carries the
unit-image of the sectionwise degree-one generator at a local section `p` of `P` to the
degree-one generator of `Sym(F)` at the section of `F` that `p` represents. -/
theorem presheafModelSymmetricPowerIso_gen_unit (X : Cᵒᵖ) (p : P.obj X) :
    (presheafModelSymmetricPowerIso J P A e 1).hom.val.app X
        (Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (symPowInt (1 : ℤ) P)) X (Hom.app (symPowIntGen P) X p)) =
      A.symmetricGenerator.val.app X
        (e.inv.val.app X
          (Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj) P) X p)) := by
  set t : F.val.obj X :=
    e.inv.val.app X
      (Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj) P) X p) with ht
  have hgen := congrArg
    (fun k : F ⟶ A.symmetric.piece 1 => k.val.app X t)
    (presheafModelSymmetricPowerIso_generator J P A e)
  have he : e.hom.val.app X t =
      Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj) P) X p :=
    congrArg (fun k : sheafifyModulePresheaf J P ⟶ sheafifyModulePresheaf J P =>
      k.val.app X (Hom.app (PresheafOfModules.sheafifyUnit
        (𝟙 (toRingCat J Osharp).obj) P) X p)) e.inv_hom_id
  refine Eq.trans ?_ hgen
  refine congrArg ((presheafModelSymmetricPowerIso J P A e 1).hom.val.app X) ?_
  exact Eq.trans
    (((symPowIntGradedAlgebra P).sheafifyGen_unit (𝟙 (toRingCat J Osharp).obj)
      (symPowIntGen P) X p).symm)
    (congrArg (((symPowIntGradedAlgebra P).sheafifyGen
      (𝟙 (toRingCat J Osharp).obj) (symPowIntGen P)).val.app X) he.symm)

/-- **The presheaf-model comparison on a product of degree-one generators.** For local sections
`s i` of a presheaf model `P` of `F`, the comparison carries the unit-image of
`∏ i, ι (s i)` to the ordered product, in `Sym(F)`, of the degree-one generators at the
sections of `F` that the `s i` represent. -/
theorem presheafModelSymmetricPowerIso_prod_ι (n : ℕ) (X : Cᵒᵖ) (s : Fin n → P.obj X) :
    (presheafModelSymmetricPowerIso J P A e (n : ℤ)).hom.val.app X
        (Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
            (symPowInt (n : ℤ) P)) X
          (⟨∏ i : Fin n, SymmetricAlgebra.ι
              ((Osharp.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X) (P.obj X) (s i),
            SymmetricAlgebra.prod_ι_mem _ s⟩ :
              SymPow.symmetricPower n
                ((Osharp.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X) (P.obj X))) =
      A.symmetric.toPresheafGradedAlgebra.homogeneousProd X n
        (fun i => A.symmetricGenerator.val.app X
          (e.inv.val.app X (Hom.app (PresheafOfModules.sheafifyUnit
            (𝟙 (toRingCat J Osharp).obj) P) X (s i)))) := by
  refine Eq.trans (congrArg ((presheafModelSymmetricPowerIso J P A e (n : ℤ)).hom.val.app X)
    (Eq.trans (congrArg (Hom.app (PresheafOfModules.sheafifyUnit
        (𝟙 (toRingCat J Osharp).obj) (symPowInt (n : ℤ) P)) X)
      (homogeneousProd_symmetricAlgebraGen P X n s).symm)
      (sheafifyUnit_homogeneousProd_model J P n X
        fun i => Hom.app (symPowIntGen P) X (s i)))) ?_
  refine Eq.trans
    (((symPowIntGradedAlgebra P).sheafify
        (𝟙 (toRingCat J Osharp).obj)).toPresheafGradedAlgebra.homogeneousProd_map
      A.symmetric.toPresheafGradedAlgebra X
      (fun m y => (presheafModelSymmetricPowerIso J P A e m).hom.val.app X y)
      (presheafModelSymmetricPowerIso_one J P A e X)
      (fun i j x y => presheafModelSymmetricPowerIso_mul J P A e i j X x y) n _) ?_
  exact congrArg (A.symmetric.toPresheafGradedAlgebra.homogeneousProd X n)
    (funext fun i => presheafModelSymmetricPowerIso_gen_unit J P A e X (s i))

end SheafOfModules

end
