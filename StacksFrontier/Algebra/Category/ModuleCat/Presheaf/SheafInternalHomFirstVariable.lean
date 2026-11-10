module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorHomAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Internal Hom of sheaves of modules is continuous in its first variable

Let `O` be a sheaf of commutative rings on a site `(C, J)` and let `H` be a sheaf of
`O`-modules.  [Stacks, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN) asserts that the
internal Hom is continuous in each variable separately; this file supplies the clause that the
library lacked, continuity in the **first** variable at sheaf level: the contravariant functor
`A ↦ Hom_O(A, H)` carries colimits of sheaves of `O`-modules to limits.

The proof is formal.  `Mod(O)` is symmetric monoidal closed — the monoidal structure is
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Monoidal.lean`'s, closedness is Day's reflection
theorem as recorded in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MonoidalSheafTensor.lean` —
and in a *braided* monoidal closed category
the first-variable internal hom `MonoidalClosed.internalHom.flip.obj H : Mod(O)ᵒᵖ ⥤ Mod(O)` is
the right adjoint of a parametrized adjunction, hence preserves limits.  That last step is
Mathlib's `CategoryTheory.ihom.instPreservesLimitsOfShape`, which needs no input from this
development; what this file adds is the two consequences in the shape the Stacks Project uses
them, and the identification with Stacks 03EM's internal Hom sheaf
(`ihomIsoInternalHom`) is what makes them statements about `Hom_O(-, H)`.

Nothing here assumes `H` or the modules of the colimit are of finite type, quasi-coherent or
coherent, and no hypothesis is placed on the site beyond the sheafification instances that the
category of sheaves of modules needs in order to be abelian.

## Main results

* `Stacks.SheafOfModules.InternalHom.ihomCokernelIsoKernel`: **left exactness in the first
  variable.** If `A ⟶ B ⟶ N ⟶ 0` is exact — `N` the cokernel of `g : A ⟶ B` — then
  `Hom_O(N, H)` is the kernel of `Hom_O(B, H) ⟶ Hom_O(A, H)`.  This is the step with which the
  Stacks Project proves the first assertion of
  [Stacks, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ).
* `Stacks.SheafOfModules.InternalHom.ihomCoproductIsoProduct`: the dual of a coproduct is the
  product of the duals.
* `Stacks.SheafOfModules.InternalHom.ihomUnitIso`: `Hom_O(O, H) ≅ H`.
* `Stacks.SheafOfModules.InternalHom.ihomFreeIsoProduct`: the dual of a free module on an index
  type `ι` is the `ι`-fold product of `H`.  For a finite `ι` that product is a finite direct
  sum, which is the form Tag 01CQ states; the passage is a biproduct comparison and is made at
  the point of use, because the index type there comes from a presentation of a module and the
  direct sum has to be produced in the spelling the consumer states it in.

## Implementation notes

The statements are phrased with `MonoidalClosed.internalHom.flip.obj H` rather than with a
named first-variable functor built from Tag 03EM's `internalHomMapLeft`.  The two are
isomorphic objectwise by `ihomIsoInternalHom`, but an isomorphism of *functors* would need the
compatibility of that identification with the first variable, which is not a formal consequence
of the one-variable adjunctions the library has; and nothing below needs it, because the
morphism between the finite direct sums in Tag 01CQ is existentially quantified — any morphism
whose kernel is the dual will do.  `ihomIsoInternalHom` is therefore applied at objects only.

The monoidal structure used is the localized one of
`SheafOfModules.monoidalCategory`, the one for which `ihomIsoInternalHom` is stated;
its unit is the structure sheaf only up to the isomorphism `SheafOfModules.unitIso`, which is
why `ihomUnitIso` is not `MonoidalClosed.unitNatIso` on the nose.  All three structures are
`def`s rather than instances in this development, so they are introduced here as local
instances.  They are stated at three independent universes `max u v w` for the sections, and
nothing in a goal below determines `w`; the local instances therefore pin it, rather than
leaving instance search a universe metavariable it cannot solve.

## References

* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

noncomputable section

universe v u

namespace Stacks.SheafOfModules.InternalHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

attribute [local instance] _root_.SheafOfModules.monoidalCategory
  _root_.SheafOfModules.symmetricCategory _root_.SheafOfModules.monoidalClosed

variable (H : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R))

/-- **Left exactness of the internal Hom in its first variable.**  If `N` is the cokernel of
`g : A ⟶ B`, then `Hom_O(N, H)` is the kernel of the dual `Hom_O(B, H) ⟶ Hom_O(A, H)` of `g`.

This is the first step of the Stacks Project's proof of the first assertion of Tag 01CQ:
applying `Hom_O(-, H)` to a presentation `A ⟶ B ⟶ N ⟶ 0` exhibits the dual of `N` as a kernel.
The cokernel is read as a limit in the opposite category by `kernelOpOp`, and the first-variable
internal hom preserves limits.

The cokernel data is implicit, read off the colimit witness: the consumer of this lemma has that
witness — `SheafOfModules.Presentation.isColimit` — and nothing else. -/
@[sga "4 IV 12.2" "partial, special case"]
public def ihomCokernelIsoKernel
    {A B N : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)}
    {g : A ⟶ B} {p : B ⟶ N} {hp : g ≫ p = 0} (hc : IsColimit (CokernelCofork.ofπ p hp)) :
    (MonoidalClosed.internalHom.flip.obj H).obj (op N) ≅
      kernel ((MonoidalClosed.internalHom.flip.obj H).map g.op) :=
  (MonoidalClosed.internalHom.flip.obj H).mapIso
      ((IsColimit.coconePointUniqueUpToIso hc (colimit.isColimit _)).op.symm ≪≫
        (kernelOpOp g).symm) ≪≫
    PreservesKernel.iso _ g.op

/-- **The dual of a coproduct is the product of the duals**, the first-variable internal hom
being continuous. -/
public def ihomCoproductIsoProduct {α : Type (max u v)}
    (Z : α → _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    (MonoidalClosed.internalHom.flip.obj H).obj (op (∐ Z)) ≅
      ∏ᶜ fun a => (MonoidalClosed.internalHom.flip.obj H).obj (op (Z a)) :=
  (MonoidalClosed.internalHom.flip.obj H).mapIso (opCoproductIsoProduct Z) ≪≫
    PreservesProduct.iso _ _

/-- **The dual of the structure sheaf is `H`**: a local map `O|_U ⟶ H|_U` is its value at the
unit section.  Here that is the unit isomorphism of the monoidal closed structure, transported
along `SheafOfModules.unitIso`, which identifies the monoidal unit with the structure sheaf. -/
public def ihomUnitIso :
    (MonoidalClosed.internalHom.flip.obj H).obj
      (op (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))) ≅ H :=
  (MonoidalClosed.internalHom.flip.obj H).mapIso (_root_.SheafOfModules.unitIso R).op ≪≫
    (MonoidalClosed.unitNatIso.app H).symm

/-- **The dual of a free module is a product of copies of `H`.**  Combining
`ihomCoproductIsoProduct` with `ihomUnitIso`, since `SheafOfModules.free ι` is the coproduct of
`ι` copies of the structure sheaf. -/
public def ihomFreeIsoProduct (ι : Type (max u v)) :
    (MonoidalClosed.internalHom.flip.obj H).obj (op (_root_.SheafOfModules.free (R :=
        Stacks.SheafOfModules.Tensor.ringSheaf R) ι)) ≅ ∏ᶜ fun _ : ι => H :=
  ihomCoproductIsoProduct R H (fun _ : ι => _root_.SheafOfModules.unit _) ≪≫
    Pi.whiskerEquiv (Equiv.refl ι) (fun _ => (ihomUnitIso R H).symm)

end Stacks.SheafOfModules.InternalHom

end

end
