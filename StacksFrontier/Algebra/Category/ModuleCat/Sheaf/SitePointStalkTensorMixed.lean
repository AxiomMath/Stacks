module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensorSheafifyLocallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkSheafExact
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk of a tensor product of sheaves of modules, at a site whose objects are larger than
its sections

Let `(C, J)` be a site, `Φ` a point of it and `O` a sheaf of commutative rings on `C`. The
tensor product of two sheaves of `O`-modules is the sheafification of the objectwise tensor
product of the underlying presheaves, and taking the stalk at `Φ` does not see that
sheafification, so the presheaf-level comparison
`Stacks.moduleFiberTensorIso` upgrades to a sheaf-level one

`(M ⊗_O N)_Φ ≅ M_Φ ⊗_{O_Φ} N_Φ`.

This file states it with the three universes free: the objects of `C` in `Type u`,
its morphisms in `Type v`, the sections and the point in `Type w`, tied together only by
`[LocallySmall.{w} C]`.

That is the shape a *small étale site* has. `AlgebraicGeometry.Space.smallEtaleRingedSite` is a
`CategoryTheory.RingedSite.{u + 1, u, u}`: its objects live in `Type (u + 1)` while its
structure sheaf is `CommRingCat.{u}`-valued, so `[Category.{u} C]` with `C : Type u` cannot be
instantiated there.

The isomorphism itself is
`Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.stalkSheafTensorIso`, already stated
at free universes; this file records how it acts on germs.

## Main definitions

* `Stacks.tensorSheafModuleFiberIso`: **the stalk of a tensor product of sheaves of modules is
  the tensor product of the stalks**, at free universes.

## Main results

* `Stacks.tensorSheafModuleFiberIso_hom_germ`: the comparison carries the germ of the
  sheafification of a local pure tensor to the pure tensor of the germs.

## Implementation notes

The coefficient sheaf is the canonical `Stacks.SheafOfModules.Tensor.ringSheaf O`.
Its underlying presheaf is `O.obj ⋙ forget₂ CommRingCat RingCat`; the structured ringed-topos
accessor uses the same provider. The tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor`, the one
`Stacks.SheafOfModules.pushforwardTensorMap` builds its canonical map out of, so the statement
applies to that map's source and target without transport.

`Stacks.SheafOfModules.SitePointStalkSheafify` routes the same composite through
`PresheafOfModules.sheafification` and `Stacks.SheafOfModules.Tensor.ringSheaf`, and
its implementation notes record the cost of identifying that spelling of the presheaf of rings
with `O.obj ⋙ forget₂ CommRingCat RingCat` at the level of morphisms. No such identification is
needed here: every statement below is an isomorphism between objects, and the sheafification
functor is taken in the spelling the tensor bifunctor is defined from, so the two sides meet by
unfolding `Stacks.SheafOfModules.Tensor.sheafTensor` and
`Stacks.sheafModuleFiber` and nothing else.

Deliberately untagged. The clauses of Stacks 03EL are about an arbitrary morphism of ringed
topoi; a point of a site is one particular such morphism, so this covers neither clause, exactly
as `Stacks.SheafOfModules.SitePointStalkSheafify` records for its own statements.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry.SheafOfModules

universe w v u

namespace Stacks

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (Φ : J.Point.{w}) (O : Sheaf J CommRingCat.{w})

/-- **The stalk of a tensor product of sheaves of modules is the tensor product of the stalks,
at free universes.** For two sheaves of `O`-modules `M` and `N` on a site `(C, J)` and a point
`Φ` of that site, the stalk at `Φ` of `M ⊗_O N` is `M_Φ ⊗_{O_Φ} N_Φ`.

The objects of `C`, its morphisms, and the sections are at three independent universes, tied
only by `[LocallySmall.{w} C]`, so this applies to a small étale site, whose objects live one
universe above its sections.

This is `Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.stalkSheafTensorIso`. -/
@[ega "0 4.1.5" "partial", sga "4 IV 13.5" "special case", sga "4 V 1.6.2" "special case"]
noncomputable def tensorSheafModuleFiberIso
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (sheafModuleFiberOfCommRing Φ O).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj M).obj N) ≅
      ((curriedTensor (ModuleCat.{w} (ringFiber Φ O.obj))).obj
          ((sheafModuleFiberOfCommRing Φ O).obj M)).obj
        ((sheafModuleFiberOfCommRing Φ O).obj N) :=
  SheafOfModules.SitePointStalkSheafify.LocallySmall.stalkSheafTensorIso Φ O M N

/-- **The stalk of a tensor product sheaf on a germ of a pure tensor**: the comparison
`(M ⊗_O N)_Φ ≅ M_Φ ⊗_{O_Φ} N_Φ` carries the germ of the sheafification of a local pure tensor
`m ⊗ n` to the pure tensor of the germs. -/
lemma tensorSheafModuleFiberIso_hom_germ
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (U : C) (x : Φ.fiber.obj U) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (tensorSheafModuleFiberIso Φ O M N).hom
        (toPresheafModuleFiber Φ
          (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj M).obj N).val U x
          (((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
              (PresheafOfModules.tensorObj M.val N.val)).app (op U)
            (m ⊗ₜ[(O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op U)] n))) =
      germ Φ O.obj M.val U x m ⊗ₜ[ringFiber Φ O.obj] germ Φ O.obj N.val U x n := by
  let e := (SheafOfModules.SitePointStalkSheafify.LocallySmall.fiberSheafifyNatIso Φ
    (Stacks.SheafOfModules.Tensor.ringSheaf O)).app (M.val ⊗ N.val)
  have h : e.hom
      (germ Φ O.obj (M.val ⊗ N.val) U x
        (m ⊗ₜ[(O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op U)] n)) =
      toPresheafModuleFiber Φ (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj M).obj N).val U x
          (((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
              (PresheafOfModules.tensorObj M.val N.val)).app (op U)
            (m ⊗ₜ[(O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op U)] n)) :=
    toPresheafModuleFiber_naturality Φ _ U x _
  change (moduleFiberTensorIso Φ O.obj M.val N.val).hom
    (e.inv _) = _
  rw [← h]
  exact (congrArg (moduleFiberTensorIso Φ O.obj M.val N.val).hom
    (ConcreteCategory.congr_hom e.hom_inv_id _)).trans
    (presheafModuleFiberTensorEquiv_germ_tmul Φ O.obj M.val N.val U x m n)

end Stacks

end
