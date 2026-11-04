module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerMultiplication
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Equivalence
public import StacksFrontier.Topology.Sheaves.Modules.Invertible

/-!
# Twisting by an invertible module, and what it does to `Ext`

Let `O` be a sheaf of commutative rings on a site and let `ℒ` be an invertible `O`-module. The
inverse tensor power `ℒ^{⊗ -1}` undoes tensoring by `ℒ`:

`(ℳ ⊗_O ℒ) ⊗_O ℒ^{⊗ -1} ≅ ℳ`

for an **arbitrary** `O`-module `ℳ`, naturally in `ℳ`. Tensoring by `ℒ` is moreover an
equivalence of the category of `O`-modules, so for a scheme `X` it identifies extension groups:

`Ext^i_{𝒪_X}(ℱ, 𝒢) ≅ Ext^i_{𝒪_X}(ℱ ⊗ ℒ, 𝒢 ⊗ ℒ)`,

and composing the two, `Ext^i_{𝒪_X}(ℒ^{⊗ -1}, 𝒢) ≅ Ext^i_{𝒪_X}(𝒪_X, 𝒢 ⊗ ℒ)`.

## Main definitions

* `Stacks.SheafOfModules.Invertible.inverseTensorSelfIso`: `ℒ^{⊗ -1} ⊗_O ℒ ≅ O`.
* `Stacks.SheafOfModules.Invertible.tensorInverseCancelNatIso`: **the cancellation**, as an
  isomorphism of endofunctors `(- ⊗_O ℒ) ⊗_O ℒ^{⊗ -1} ≅ 𝟭`; this is the naturality in `ℳ`.
* `Stacks.SheafOfModules.Invertible.tensorInverseCancelIso`: the cancellation at a module,
  `(ℳ ⊗_O ℒ) ⊗_O ℒ^{⊗ -1} ≅ ℳ`.
* `Stacks.SheafOfModules.Invertible.tensorModuleFunctor`: tensoring by `ℒ`, as an endofunctor of
  `X.Modules` for a scheme `X`; it is an equivalence and it is additive.
* `AlgebraicGeometry.extTensorInvertibleAddEquiv`: `Ext^i(K, K') ≅ Ext^i(K ⊗ ℒ, K' ⊗ ℒ)` for
  objects of the derived category of `X.Modules`.
* `AlgebraicGeometry.zExtTensorInvertibleAddEquiv`: `Ext^i(ℱ, 𝒢) ≅ Ext^i(ℱ ⊗ ℒ, 𝒢 ⊗ ℒ)` for
  modules placed in a single degree.
* `AlgebraicGeometry.zExtInverseTensorAddEquiv`: the composite
  `Ext^i(ℒ^{⊗ -1}, 𝒢) ≅ Ext^i(𝒪_X, 𝒢 ⊗ ℒ)`.

## Implementation notes

**Which of the parallel tensor spellings.** The tensor product is
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` and the inverse power is
`Stacks.SheafOfModules.Invertible.tensorPower`, which at a scheme is
`Stacks.SheafOfModules.Invertible.tensorPowerModule ℒ (-1)`. That is the pair the consumers in
`StacksFrontier/AlgebraicGeometry/Curves/VanishingResults/` use — `StacksFrontier/AlgebraicGeometry/Curves/VanishingResults/DualizingTwist.lean` states
[Stacks, Tag 0B62] with exactly these two symbols — and no other spelling appears in a statement
here. The library carries several parallel tensor-power constructions;
`Stacks.SheafOfModules.TensorPower.tensorPower` is the one the multiplication isomorphisms of
Tag 01CU are built for, and it is *definitionally* the power used in the statements
(`Stacks.SheafOfModules.Invertible.tensorPower_eq_tensorPower`), so the proofs below use that
API with no comparison lemma and the statements still read in the consumers' spelling.

**The hypothesis is invertibility, not "tensoring is an equivalence".** Every statement here
assumes `AlgebraicGeometry.SheafOfModules.IsInvertible O hO ℒ`, which is what a consumer has.
The Tag 01CU API instead assumes `(tensorRightFunctor O hO ℒ).IsEquivalence`, and that instance
is *not* found by instance search at a scheme: it needs the type of `X.ringCatSheaf.property` to
be recognised as `Presheaf.IsSheaf _ (structureRingPresheaf X.presheaf)`, which is a
definitional unfolding that instance resolution does not perform. Stating the hypothesis as
invertibility and discharging the equivalence instance by the explicit term
`Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence` is what makes these usable at
a scheme at all.

**The cancellation is a composition of isomorphisms and nothing else.** The three inputs are the
multiplication isomorphism `ℒ^{⊗ -1} ⊗ ℒ^{⊗ 1} ≅ ℒ^{⊗ 0}` of Tag 01CU
(`Stacks.SheafOfModules.TensorPower.tensorPowerMulIso`), the identification of tensoring by a
tensor product with the composite of the two tensor functors
(`Stacks.SheafOfModules.TensorPower.tensorRightFunctorObjIso`), and the right unit constraint
(`Stacks.SheafOfModules.TensorPower.tensorRightUnitIso`). So nothing below rewrites a morphism
equation, and no transparency option is set.

Neither half of the cancellation was available before. `tensorPowerMulIso` multiplies two
*powers* of `ℒ` and says nothing about a general `ℳ`; the monoidal-category-generic
`Stacks.Duality.tensorLeftInvTensorRightIso` is stated for the monoidal structure of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Monoidal.lean` and for a two-sided inverse in that
structure, so instantiating it at `X.Modules` would need both a proof that `ℒ^{⊗ -1}` is such an
inverse and the comparison between that `⊗` and `tensorSheaf` — strictly more work than the
three-line composition used here, and it would land in the wrong spelling.

**`Ext` at a scheme.** The identifications of `Ext` groups are stated for `X.Modules` with a free
`[HasDerivedCategory X.Modules]` instance binder, so they hold at whichever model of the derived
category the caller has chosen — checked at both: at the locally small
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is what plain instance search picks,
and at `HasDerivedCategory.standard` raised to priority `10000`, which is what it takes to
displace it. They are instances of
`CategoryTheory.Abelian.zExt.mapAddEquiv` and `CategoryTheory.DerivedCategory.Ext.mapAddEquiv`,
which hold for an arbitrary equivalence of abelian categories; the only scheme-specific input is
that tensoring by an invertible module *is* such an equivalence, which is Tag 01CS.

The endofunctor `tensorModuleFunctor` is `Stacks.SheafOfModules.TensorPower.tensorRightFunctor`
ascribed at `X.Modules`, the consumers' spelling — the same device as
`Stacks.SheafOfModules.Invertible.tensorPowerModule`, and for the same reason: the unascribed
functor has type `SheafOfModules (structureSheaf X.presheaf _) ⥤ …`, which is only
definitionally `X.Modules ⥤ X.Modules`, and the `Abelian` and `HasDerivedCategory` instances
needed to even state an `Ext` group are not found at the unascribed spelling.
`tensorModuleFunctor_obj` records that its value is the tensor product sheaf, by `rfl`.

For the same reason the `Ext` statements name the category explicitly, as
`Abelian.zExt (C := X.Modules)`: a type ascription on the *argument* does not change the type
Lean infers for it, so without `C := X.Modules` the category is read off
`tensorSheaf X.presheaf _ ℳ ℒ` as `SheafOfModules (structureSheaf X.presheaf _)` and the
`HasDerivedCategory` instance is not found. The isomorphism fed to
`CategoryTheory.Abelian.zExt.congrAddEquiv` inside `zExtInverseTensorAddEquiv` is likewise bound
as an `@Iso X.Modules _ _ _`: passing the category as a named argument there is not enough,
because the universe of its `Category` instance is then still a metavariable when `Abelian` is
synthesized.

## References

* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)
open Stacks.SheafOfModules.TensorSheafification (structureSheaf)

universe w v u

namespace Stacks.SheafOfModules.Invertible

/-! ### Cancelling an invertible factor against its inverse -/

section Site

open Stacks.SheafOfModules.TensorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : _root_.SheafOfModules.{w} (structureSheaf O hO)) [IsInvertible O hO L]

/-- **`ℒ^{⊗ -1} ⊗_O ℒ ≅ O`.** The multiplication isomorphism of [Stacks, Tag 01CU] at the
exponents `(-1, 1)`, after replacing the second factor `ℒ` by `ℒ^{⊗ 1}` and reindexing
`-1 + 1 = 0`; the zeroth tensor power *is* the structure sheaf. -/
def inverseTensorSelfIso :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          (tensorPower O hO L (-1))).obj L ≅
      _root_.SheafOfModules.unit (structureSheaf O hO) :=
  tensorSheafMapIso O hO (Iso.refl (tensorPower O hO L (-1))) (tensorPowerOneIso O hO L).symm ≪≫
    tensorPowerMulIso O hO L (-1) 1 ≪≫
    tensorPowerReindex O hO L (show (-1 : ℤ) + 1 = 0 by ring)

/-- **Tensoring by an invertible module and then by its inverse is the identity**, as an
isomorphism of endofunctors of `O`-modules: `(- ⊗_O ℒ) ⊗_O ℒ^{⊗ -1} ≅ 𝟭`. This is the
cancellation `(ℳ ⊗_O ℒ) ⊗_O ℒ^{⊗ -1} ≅ ℳ` of `tensorInverseCancelIso` together with its
naturality in `ℳ`.

Tensoring by the tensor product `ℒ^{⊗ -1} ⊗_O ℒ` is the composite of the two tensor functors
([Stacks, Tag 01CT]), that tensor product is the structure sheaf by `inverseTensorSelfIso`, and
tensoring by the structure sheaf is the identity. -/
def tensorInverseCancelNatIso :
    (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
          (tensorPower O hO L (-1)) ≅ 𝟭 _ :=
  (tensorRightFunctorObjIso O hO (tensorPower O hO L (-1)) L).symm ≪≫
    (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.mapIso
          (inverseTensorSelfIso O hO L) ≪≫
      tensorRightUnitIso O hO

/-- **`(ℳ ⊗_O ℒ) ⊗_O ℒ^{⊗ -1} ≅ ℳ` for an arbitrary `O`-module `ℳ`.** The value at `ℳ` of
`tensorInverseCancelNatIso`, which is the same isomorphism together with its naturality. -/
def tensorInverseCancelIso (M : _root_.SheafOfModules.{w} (structureSheaf O hO)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj
              L)).obj
        (tensorPower O hO L (-1)) ≅ M :=
  (tensorInverseCancelNatIso O hO L).app M

end Site

/-! ### Tensoring by an invertible module on a scheme, as an equivalence -/

section Scheme

open AlgebraicGeometry

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertible X.presheaf X.ringCatSheaf.property L]

/-- **Tensoring by an invertible `𝒪_X`-module `ℒ`, as an endofunctor of `X.Modules`.** This is
`Stacks.SheafOfModules.TensorPower.tensorRightFunctor` ascribed at the spelling `X.Modules` of
the category of `𝒪_X`-modules, at which the `Abelian` and `HasDerivedCategory` instances needed
to speak of `Ext` are found; its value at `ℳ` is the tensor product sheaf `ℳ ⊗ ℒ`, by
`tensorModuleFunctor_obj`. -/
def tensorModuleFunctor : X.Modules ⥤ X.Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
      (forget₂ CommRingCat RingCat) X.ringCatSheaf.property⟩).flip.obj L

omit [IsInvertible X.presheaf X.ringCatSheaf.property L] in
/-- Tensoring by `ℒ` sends `ℳ` to the tensor product sheaf `ℳ ⊗ ℒ`. -/
theorem tensorModuleFunctor_obj (M : X.Modules) :
    (tensorModuleFunctor L).obj M =
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.property⟩).obj M).obj L := rfl

/-- Tensoring by an invertible `𝒪_X`-module is an equivalence of the category of `𝒪_X`-modules.
This is the content of [Stacks, Tag 01CS], which is registered on the class
`Stacks.SheafOfModules.IsInvertible`; here it is rebound at the `X.Modules` spelling of the
functor, where instance search does not find it. -/
instance tensorModuleFunctor_isEquivalence : (tensorModuleFunctor L).IsEquivalence :=
  Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence
    X.presheaf X.ringCatSheaf.property L

/-- Tensoring by an invertible `𝒪_X`-module is additive, being an equivalence. -/
instance tensorModuleFunctor_additive : (tensorModuleFunctor L).Additive :=
  Functor.additive_of_isEquivalence _

end Scheme

end Stacks.SheafOfModules.Invertible

namespace AlgebraicGeometry

open Stacks.SheafOfModules.Invertible (tensorModuleFunctor tensorPower inverseTensorSelfIso)

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertible X.presheaf X.ringCatSheaf.property L]
  [HasDerivedCategory.{w} X.Modules]

/-- **`Ext^i(K, K') ≅ Ext^i(K ⊗ ℒ, K' ⊗ ℒ)` in the derived category of `𝒪_X`-modules**, for an
invertible `ℒ`. Tensoring by `ℒ` is an equivalence of `X.Modules`, so it acts on the derived
category by an equivalence, and an equivalence is bijective on the Hom groups which are the
`Ext` groups. -/
def extTensorInvertibleAddEquiv (K K' : DerivedCategory X.Modules) (i : ℤ) :
    DerivedCategory.Ext K K' i ≃+
      DerivedCategory.Ext ((tensorModuleFunctor L).mapDerivedCategory.obj K)
        ((tensorModuleFunctor L).mapDerivedCategory.obj K') i :=
  DerivedCategory.Ext.mapAddEquiv (tensorModuleFunctor L) K K' i

/-- **`Ext^i(ℱ, 𝒢) ≅ Ext^i(ℱ ⊗ ℒ, 𝒢 ⊗ ℒ)` for `𝒪_X`-modules placed in a single degree**, for an
invertible `ℒ`. This is `extTensorInvertibleAddEquiv` at the degree-zero objects, with the
degreewise action of the tensor functor on a complex concentrated in degree zero identified with
the degree-zero complex of the twisted module. -/
def zExtTensorInvertibleAddEquiv (F G : X.Modules) (i : ℤ) :
    Abelian.zExt F G i ≃+
      Abelian.zExt (C := X.Modules)
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
            (forget₂ CommRingCat RingCat) X.ringCatSheaf.property⟩).obj F).obj L)
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
            (forget₂ CommRingCat RingCat) X.ringCatSheaf.property⟩).obj G).obj L) i :=
  Abelian.zExt.mapAddEquiv (tensorModuleFunctor L) F G i

/-- **`Ext^i(ℒ^{⊗ -1}, 𝒢) ≅ Ext^i(𝒪_X, 𝒢 ⊗ ℒ)`**, for an invertible `𝒪_X`-module `ℒ` and an
arbitrary `𝒪_X`-module `𝒢`: tensoring by `ℒ` identifies the two groups, and it carries
`ℒ^{⊗ -1}` to the structure sheaf.

This is the identification by which a vanishing statement about `Ext^i(ℒ^{⊗ -1}, 𝒢)` becomes one
about `Ext^i(𝒪_X, 𝒢 ⊗ ℒ)`, which is the cohomology `H^i(X, 𝒢 ⊗ ℒ)`. -/
def zExtInverseTensorAddEquiv (G : X.Modules) (i : ℤ) :
    Abelian.zExt (C := X.Modules)
        (tensorPower X.presheaf X.ringCatSheaf.property L (-1)) G i ≃+
      Abelian.zExt (C := X.Modules)
        (SheafOfModules.unit (structureSheaf X.presheaf X.ringCatSheaf.property))
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
            (forget₂ CommRingCat RingCat) X.ringCatSheaf.property⟩).obj G).obj L) i :=
  letI e : @Iso X.Modules _
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
            (forget₂ CommRingCat RingCat) X.ringCatSheaf.property⟩).obj
              (tensorPower X.presheaf X.ringCatSheaf.property L (-1))).obj L)
      (SheafOfModules.unit (structureSheaf X.presheaf X.ringCatSheaf.property)) :=
    inverseTensorSelfIso X.presheaf X.ringCatSheaf.property L
  (zExtTensorInvertibleAddEquiv L _ G i).trans
    (Abelian.zExt.congrAddEquiv e (Iso.refl _) i)

end AlgebraicGeometry

end
