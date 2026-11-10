module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorBilinEquivApply

/-!
# The base change of bilinear pairings of Tag 03EL, on a pair of local sections

`Stacks.SheafOfModules.pullbackTensorBilinEquiv` is the third link of the regrouped chain of
Tag 03EL: the base change of bilinear pairings
`Bilin_{O_D}(F × G, f_*N) ≃ Bilin_{O_C}(f^*F × f^*G, N)` along a morphism of ringed topoi.
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorBilinEquivApply` evaluates it at
*morphism* level, in two forms: up to the two units of Tag 03CZ with no hypothesis on `f`
(`Stacks.SheafOfModules.prodMap_unit_comp_pullbackTensorBilinEquiv_apply_coe`), and solved for the
base change when the structure map of `f` is invertible
(`Stacks.SheafOfModules.pullbackTensorBilinEquiv_apply_coe`).

This file reads the second of those on *sections*: it says what the base change of a pairing does
to a pure pair of local sections of the two pullbacks, which is the form in which the pairing
enters a computation of the comparison of Tag 03EL on a local section.

## Main results

* `Stacks.SheafOfModules.pairingApp_eq_map_prodObjMk_of_eq_prodMap_comp`: the abstract step. A
  pairing of underlying sheaves of sets which factors as a product of two morphisms followed by a
  third pairs two local sections by carrying each through its own leg and the resulting pair
  through the third morphism.
* `Stacks.SheafOfModules.pairingApp_pullbackTensorBilinEquiv`: **the base change of an arbitrary
  bilinear pairing on a pure pair of local sections.** For a morphism of ringed topoi with
  invertible structure map, the base change of `b` pairs local sections `a` of `f^*F` and `b'` of
  `f^*G` over an object `W` by carrying each through the inverse of its unit of Tag 03CZ and then
  the resulting pair of sections of `f⁻¹F` and `f⁻¹G` through the inverse product comparison of
  `f⁻¹`, the inverse image of `b`, and the counit of `f⁻¹ ⊣ f_*`.

## Implementation notes

Nothing here carries a `stacks` attribute: these are value formulas for the links of a chain of
bijections, and the Stacks Project states none of them. This follows the policy of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearValueFormulas`, whose
`Stacks.SheafOfModules.pairingApp_inverseImageBilinearEquiv` is the same transport of a
morphism-level formula through `CategoryTheory.Sheaf.sectionsFunctor` for the bijection of
Tag 03D3.

The statement is at variables — the morphism of ringed topoi, the two modules over `O_D`, the
module over `O_C`, the pairing, the object and the two sections are all bound. Substituting a
link characterization into a goal about a *concrete* morphism of ringed topoi instead makes `rw`
report "did not find the pattern", because the instance arguments of the two spellings of a
binary product agree only at default transparency; forcing the rewrite with explicit arguments
then exhausts the kernel.

The decomposition of the pairing is done by the abstract lemma
`Stacks.SheafOfModules.pairingApp_eq_map_prodObjMk_of_eq_prodMap_comp`, which takes the two legs
and the third morphism as explicit arguments. That is what keeps the one spelling crossing of this
file — the source of the product comparison of `f⁻¹` is
`f⁻¹(F) ⨯ f⁻¹(G)` there and `moduleSheaf _ ((inverseImageModules f O).obj F) ⨯ …` in the two
units, and the two agree only at default transparency — inside a single application of a lemma
about a bare binary product, rather than inside a rewrite.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPushforward
open Stacks.PresheafOfModules.ChangeOfRings

namespace Stacks.SheafOfModules

section Abstract

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w}) {A B N : SheafOfModules.{w} R}

omit [J.HasSheafCompose (forget RingCat)] in
/-- **A pairing which factors through a product of two morphisms, read on a pair of local
sections.** If a pairing `q` of the underlying sheaves of sets is `prod.map u v ≫ m`, then its
value on local sections `a` and `b` is obtained by carrying `a` through `u`, carrying `b` through
`v`, and carrying the resulting pair through `m`.

The two legs and the third morphism are explicit arguments of a statement about a bare binary
product, so that a caller whose legs and whose `m` spell the intermediate product two ways never
has to rewrite inside a goal. -/
theorem pairingApp_eq_map_prodObjMk_of_eq_prodMap_comp {A' B' : Sheaf J (Type w)}
    [HasBinaryProduct A' B'] (u : moduleSheaf R A ⟶ A') (v : moduleSheaf R B ⟶ B')
    (m : A' ⨯ B' ⟶ moduleSheaf R N)
    {q : moduleSheaf R A ⨯ moduleSheaf R B ⟶ moduleSheaf R N} (hq : q = prod.map u v ≫ m)
    (U : Cᵒᵖ) (a : (sectionsFunctor J U).obj (moduleSheaf R A))
    (b : (sectionsFunctor J U).obj (moduleSheaf R B)) :
    pairingApp R q U a b =
      (sectionsFunctor J U).map m
        (Functor.prodObjMk ((sectionsFunctor J U).map u a)
          ((sectionsFunctor J U).map v b)) := by
  rw [pairingApp, hq, Functor.map_comp_apply, Functor.map_prodMap_apply,
    Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk]

end Abstract

section Value

universe w w' v u v' u'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The base change of an arbitrary bilinear pairing of Tag 03EL on a pure pair of local
sections.** Along a morphism of ringed topoi whose structure map is invertible — the case of a
localization morphism — the base change of a pairing `b` over `O_D` into `f_*N` takes local
sections `a` of `f^*F` and `b'` of `f^*G` over an object `W` to the value obtained by carrying `a`
and `b'` each through the inverse of its unit `ε : f⁻¹F ⟶ (f^*F)|` of Tag 03CZ, and then carrying
the resulting pair of sections of `f⁻¹F` and `f⁻¹G` through the inverse product comparison of
`f⁻¹`, the inverse image of `b`, and the counit of `f⁻¹ ⊣ f_*`.

This is `Stacks.SheafOfModules.pullbackTensorBilinEquiv_apply_coe` transported through
`CategoryTheory.Sheaf.sectionsFunctor` by
`Stacks.SheafOfModules.pairingApp_eq_map_prodObjMk_of_eq_prodMap_comp`. The counit is where it
stops: for a `CategoryTheory.Sheaf.MorphismOfTopoi` the inverse image has no description on
sections, so neither has the base change of `b`. -/
theorem pairingApp_pullbackTensorBilinEquiv [IsIso f.fSharpInverseImage]
    (b : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G ⟶
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ((pushforwardModules f).obj N) //
        IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) q })
    (W : X.Cᵒᵖ)
    (a : (sectionsFunctor X.J W).obj
      (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj F)))
    (b' : (sectionsFunctor X.J W).obj
      (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj G))) :
    pairingApp (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (pullbackTensorBilinEquiv f F G N b).1 W a b' =
      (sectionsFunctor X.J W).map
          ((PreservesLimitPair.iso f.toToposHom.inverseImage
                (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
                (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)).inv ≫
            f.toToposHom.inverseImage.map b.1 ≫
              f.toToposHom.adj.counit.app
                (moduleSheaf (inverseImageRingSheaf f.toToposHom
                    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
                  ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N)))
        (Functor.prodObjMk
          ((sectionsFunctor X.J W).map
            (inv ((moduleSheafFunctor
                (commRingSheaf X.J (inverseImageStructureCommRing f)
                  (isSheaf_inverseImageStructureCommRing f))).map
              ((pullbackExtendAdj f).unit.app
                ((inverseImageModules f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)))) a)
          ((sectionsFunctor X.J W).map
            (inv ((moduleSheafFunctor
                (commRingSheaf X.J (inverseImageStructureCommRing f)
                  (isSheaf_inverseImageStructureCommRing f))).map
              ((pullbackExtendAdj f).unit.app
                ((inverseImageModules f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)))) b')) :=
  pairingApp_eq_map_prodObjMk_of_eq_prodMap_comp
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) _ _ _
    (pullbackTensorBilinEquiv_apply_coe f F G N b) W a b'

end Value

end Stacks.SheafOfModules

end
