module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorTensorIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.SheafificationAndRestrictionOfScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne

/-!
# Restriction of scalars along the projection of a product presentation is monoidal

Let `R ≅ ∏_i factor i` be a sheaf of commutative rings presented as a product
(`Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation`) and let
`projRing hp n : Tensor.ringSheaf R ⟶ Tensor.ringSheaf (factor n)` be the `n`-th projection.
For two sheaves of modules `A` and `B` over the factor `factor n`,

`(A as an R-module) ⊗_R (B as an R-module) ≅ (A ⊗_{factor n} B) as an R-module`,

i.e. restriction of scalars along the projection is a monoidal functor for the tensor product of
[Stacks, Tag 01CA].  This is the content of the invertibility of the lax comparison
`Stacks.SheafOfModules.TensorRestrictScalars.laxComparison` at the projection, but it is not that
statement: `laxComparison` is spelled over a topological space with its topology of opens and at a
single universe, whereas everything here is over an arbitrary site with the ring and module
sections in `max u v`.  No declaration asserts the invertibility of `laxComparison` itself, and
closing this did not need one.

This generalises `Stacks.SheafOfModules.RingSheafProductFactor.tensorObjIsoRestrictScalars`, which
is the case `A = factor n`, to an arbitrary `A`.

## Main definitions

* `Stacks.SheafOfModules.RingSheafProductFactor.tensorObjIsoSheafTensorRight`: the tensor product
  of the monoidal structure `SheafOfModules.monoidalCategorySheafTensor` is the tensor
  endofunctor `Stacks.sheafTensorRight` that the change-of-rings material is phrased with.
* `Stacks.SheafOfModules.RingSheafProductFactor.tensorObjIsoRestrictScalars₂`: **restriction of
  scalars along the `n`-th projection commutes with the tensor product**, for two modules over
  the factor.
* `Stacks.SheafOfModules.RingSheafProductFactor.tensorObjIsoFactorModule`: the shape the diagonal
  terms of the implication `(2) ⟹ (1)` of Stacks 0FPG consume — if `A ⊗_{factor n} B` is the unit
  module of the factor, then `(A as an R-module) ⊗_R (B as an R-module)` is `factorModule hp n`,
  that is `factor n` read as an `R`-module.

## Main results

* `Stacks.SheafOfModules.RingSheafProductFactor`
  `.exists_tensorObj_iso_factorModule_of_isInvertibleModule`: the two put together — **an
  invertible module over the factor has a partner whose tensor product with it over `R`, both
  read as `R`-modules, is `factor n` read as an `R`-module**.  Tag 0B8K
  supplies the partner at the `Stacks.SheafOfModules.tensorLeftFunctor` spelling of the tensor
  product; that is the same object as `SheafOfModules.monoidalCategorySheafTensor`'s `⊗`, and the
  crossing costs one `exact`.

## Implementation notes

**The proof is the projection formula plus the counit of Stacks 03CZ, and nothing else.**  Write
`F` for restriction of scalars along the projection and `E` for extension of scalars along it, so
that `E ⊣ F`.  Cancellation of a base change
(`Stacks.Cohomology.MixedDerivedTensor.tensorBaseChangeLinearIso`, the `O₁`-linear form of Stacks
05V4's comparison, unconditional since
`Stacks.Cohomology.MixedDerivedTensor.sheafifyCommutesRestrictScalars`) gives

`F A ⊗_R G ≅ F (A ⊗_{factor n} E G)`

for every `R`-module `G`, naturally in `A`.  At `G = F B` the counit `E (F B) ≅ B` is an
isomorphism — that is
`Stacks.SheafOfModules.RingSheafProductFactor.extendScalarsRestrictScalarsProjRingIso`, which
holds because the projection is surjective on sections, hence locally surjective, hence `F` is
fully faithful (Stacks 0930).  So the only input beyond the formal projection formula is the local
surjectivity of the projection, and that is where the product presentation is used: for a general
morphism of sheaves of commutative rings the counit is not invertible and the statement is false.

**Three spellings of the tensor product are crossed, each by an ascription.**  The monoidal
structure `SheafOfModules.monoidalCategorySheafTensor` has
`Stacks.SheafOfModules.Tensor.sheafTensor` as its tensor product on the nose; the flatness
material uses `AlgebraicGeometry.SheafOfModules.sheafTensorRight`, and the change-of-rings
material `Stacks.sheafTensorRight`.  The first two are identified by
`Stacks.SheafOfModules.FlatCoproduct.sheafTensorRightIso` and the last two have literally the same
definition, so `tensorObjIsoSheafTensorRight` crosses all three at once with its declared type;
after that the composite below never leaves the `Stacks.sheafTensorRight` spelling.  Likewise
`projRing` is the `sheafCompose`-image of `hp.π n`, which is
`Stacks.FlatChangeOfRings.ringSheafMap (hp.π n)`; the two are crossed once, by the declared type
of `tensorObjIsoRestrictScalars₂`.

Nothing here is a clause of Stacks 0FPG; everything is a step of the proof of its implication
`(2) ⟹ (1)`, so no declaration carries the project tag.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ) — extension of scalars is
  left adjoint to restriction of scalars.
* [Stacks Project, Tag 0930](https://stacks.math.columbia.edu/tag/0930) — restriction of scalars
  along a surjection of sheaves of rings is fully faithful.
* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4) — cancellation of a base
  change in a tensor product.
* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG) — the implication
  `(2) ⟹ (1)`, whose diagonal terms are the consumer.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite

universe v u t

namespace Stacks.SheafOfModules.RingSheafProductFactor

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable {ι : Type t} {factor : ι → Sheaf J CommRingCat.{max u v}}
  {R : Sheaf J CommRingCat.{max u v}} (hp : ProductPresentation R factor)

/-- **Restriction of scalars along the `n`-th projection of a product presentation commutes with
the tensor product of two modules over the factor**:

`(A as an R-module) ⊗_R (B as an R-module) ≅ (A ⊗_{factor n} B) as an R-module`.

This is the general case of
`Stacks.SheafOfModules.RingSheafProductFactor.tensorObjIsoRestrictScalars`, which does `A = factor
n`, and it is the content of the invertibility of
`Stacks.SheafOfModules.TensorRestrictScalars.laxComparison` at the projection — though not that
statement, which is spelled over a topological space; see the module docstring.

The composite is: cancellation of a base change at `G = B` read as an `R`-module, which gives
`A|_R ⊗_R B|_R ≅ (A ⊗_{factor n} (factor n ⊗_R B|_R))|_R`; and then the counit of Stacks 03CZ,
which collapses `factor n ⊗_R B|_R` back to `B` because the projection is locally surjective.  The
restriction of scalars is load-bearing in both arguments: for a module over `R` that is not a
module over the factor the statement is false, as the module docstring of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorTensorIso` records. -/
public def tensorObjIsoRestrictScalars₂ (n : ι)
    (A B : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf (factor n))) :
    letI := _root_.SheafOfModules.monoidalCategorySheafTensor R
    letI := _root_.SheafOfModules.monoidalCategorySheafTensor (factor n)
    (((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj A) ⊗
        ((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj B)) ≅
      (_root_.SheafOfModules.restrictScalars (projRing hp n)).obj (A ⊗ B) := by
  letI := _root_.SheafOfModules.monoidalCategorySheafTensor R
  letI := _root_.SheafOfModules.monoidalCategorySheafTensor (factor n)
  exact (Stacks.Cohomology.MixedDerivedTensor.tensorBaseChangeLinearIso (hp.π n)
      ((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj B)).app A ≪≫
    (_root_.SheafOfModules.restrictScalars (projRing hp n)).mapIso
      (MonoidalCategory.whiskerLeftIso A (extendScalarsRestrictScalarsProjRingIso hp n B))

/-- **The shape the diagonal terms of the implication `(2) ⟹ (1)` of Stacks 0FPG consume.**  If
two modules over the `n`-th factor have the unit module of that factor as their tensor product —
which is what invertibility over the factor supplies — then their tensor product over `R`, both
read as `R`-modules, is `factorModule hp n`, the factor read as an `R`-module.

This is `tensorObjIsoRestrictScalars₂` followed by the restriction of scalars of `e`, using
`factorModule_eq_restrictScalars_unit`.  What separates it from the tag's implication is only the
passage from this tensor product of sheaves of modules to the derived tensor product. -/
public def tensorObjIsoFactorModule (n : ι)
    (A B : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf (factor n)))
    (e : letI := _root_.SheafOfModules.monoidalCategorySheafTensor (factor n)
      (A ⊗ B) ≅ _root_.SheafOfModules.unit (Tensor.ringSheaf (factor n))) :
    letI := _root_.SheafOfModules.monoidalCategorySheafTensor R
    (((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj A) ⊗
        ((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj B)) ≅
      factorModule hp n := by
  letI := _root_.SheafOfModules.monoidalCategorySheafTensor R
  letI := _root_.SheafOfModules.monoidalCategorySheafTensor (factor n)
  exact tensorObjIsoRestrictScalars₂ hp n A B ≪≫
    (_root_.SheafOfModules.restrictScalars (projRing hp n)).mapIso e


/-- **An invertible module over the `n`-th factor has a partner whose tensor product with it over
`R`, both read as `R`-modules, is `factor n` read as an `R`-module.**

Invertibility over the factor supplies the partner, by Tag 0B8K
(`Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit`), and
`tensorObjIsoFactorModule` carries the resulting identification down to `R`.

Tag 0B8K states the tensor product as `Stacks.SheafOfModules.tensorLeftFunctor` applied to the
partner, over the `Stacks.SheafOfModules.TensorSheafification.structureSheaf` spelling of the
sheaf of rings, whereas `tensorObjIsoFactorModule` wants
`SheafOfModules.monoidalCategorySheafTensor`'s `⊗` over the `Tensor.ringSheaf` spelling.  Both are
the sheafification of the objectwise tensor product of the two underlying presheaves, so the
crossing is a single definitional unification and `exact` performs it. -/
public theorem exists_tensorObj_iso_factorModule_of_isInvertibleModule (n : ι)
    (H : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf (factor n)))
    (hH : Tensor.IsInvertibleModule (factor n) H) :
    letI := _root_.SheafOfModules.monoidalCategorySheafTensor R
    ∃ H' : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf (factor n)),
      Nonempty ((((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj H) ⊗
          ((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj H')) ≅
        factorModule hp n) := by
  let := _root_.SheafOfModules.monoidalCategorySheafTensor R
  let := _root_.SheafOfModules.monoidalCategorySheafTensor (factor n)
  obtain ⟨H', ⟨e⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := (factor n).obj) (hO := (Tensor.ringSheaf (factor n)).property) H).mp hH
  exact ⟨H', ⟨tensorObjIsoFactorModule hp n H H' e⟩⟩

end Stacks.SheafOfModules.RingSheafProductFactor

end
