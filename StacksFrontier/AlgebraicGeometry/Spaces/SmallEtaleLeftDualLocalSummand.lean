module

public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesMonoidal
import StacksCore.Tactic.StacksAttribute

/-!
# A left-dual `𝒪_F`-module on an algebraic space is locally a direct summand of a finite free one

Let `F` be an algebraic space over a scheme `S` and let `M` be an `𝒪_F`-module which has a left
dual in the monoidal category `AlgebraicGeometry.Space.modulesMonoidalCategory` of
`𝒪_F`-modules.  [Stacks, Tag 0FNZ](https://stacks.math.columbia.edu/tag/0FNZ) (1) asserts that
then every object `U` of the small étale site has a covering on whose members `M` restricts to a
direct summand of a finite free module.  This file is that statement for an algebraic space.

## Main results

* `AlgebraicGeometry.Space.exists_cover_retract_finiteFree_of_exactPairing`: **Stacks 0FNZ (1)
  for the `𝒪_F`-modules of an algebraic space.**

## Implementation notes

**Where the content comes from.**  Nothing is proved here beyond the instantiation:
`Stacks.SheafOfModules.exists_cover_retract_finiteFree_of_exactPairing_tensorSheaf` is Tag
0FNZ (1) on an arbitrary ringed site, at a module universe independent of the universes of the
objects and the arrows of the site, and that independence is what makes it applicable to the
small étale site of an algebraic space, whose objects live in `Type (u + 1)` while its structure
sheaf and its modules live in `u`.

**The two monoidal structures.**  The imported statement is stated for
`Stacks.SheafOfModules.Strict.monoidalCategory`, whose tensor product *is* the tensor product
sheaf of Tag 01CA on the nose — which is what lets its proof read the coevaluation on local
sections — whereas the `𝒪_F`-modules of an algebraic space carry
`AlgebraicGeometry.Space.modulesMonoidalCategory`, the structure obtained by localizing the
monoidal structure of presheaves of modules along sheafification.  The two are not the same
structure: the tensor products are isomorphic by
`AlgebraicGeometry.Space.modulesTensorObjIso` and not equal.  The passage between them is
`CategoryTheory.ExactPairing.ofFullyFaithful` along
`Stacks.SheafOfModules.Strict.toLocalizedMonoidal`, the identity functor viewed as a functor into
the nominally distinct type carrying the localized structure: it is fully faithful because it is
the identity, and monoidal because the strict structure is `CategoryTheory.Monoidal.induced`
along it.  So a left dual for the localized structure gives one for the strict structure, with
the same two objects, and the imported statement applies.

**This does not give the converse, Tag 0FNY, at these universes.**  Tag 0FNY — that the dual
`𝓗om(M, 𝒪_F)` together with the evaluation and a coevaluation *is* a left dual of a module
locally a direct summand of a finite free one — is not available for an algebraic space, and this
file does not make it so.  Its dual object is the internal Hom of Tag 03EM, whose sections over
`U` are morphisms of modules on the slice site at `U`; the whole cluster carrying it
(`Stacks.SheafOfModules.dualSheaf`, `tensorDualToEndomorphism`,
`isIso_tensorDualToEndomorphism`, `coevaluation`, `exactPairingDualSheafOfRetract`) is therefore
stated for a structure sheaf of rings in `CommRingCat.{max u v}`, `u` and `v` being the universes
of the objects and the arrows of the site, while the module universe is pinned to that ring
universe by Mathlib's monoidal structure on presheaves of modules.  On the small étale site
`max u v = u + 1` and the structure sheaf has its sections in `u`, so the cluster applies at
neither universe; see the implementation notes of
`AlgebraicGeometry.RingedSite.modulesMonoidalClosed`.  Tag 0FNZ is free of that constraint for
exactly one reason: it never mentions the internal Hom, taking the dual object as given.

## References

* [Stacks Project, Tag 0FNZ](https://stacks.math.columbia.edu/tag/0FNZ)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY) — the converse.
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP) — left duals in a
  monoidal category.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the monoidal structure.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

attribute [local instance] modulesMonoidalCategory

/-- **Stacks 0FNZ (1) for the `𝒪_F`-modules of an algebraic space.**  If an `𝒪_F`-module `M` has
a left dual `N` in the monoidal category of `𝒪_F`-modules, then every object `U` of the small
étale site of `F` has a covering on whose members `M` restricts to a direct summand of a free
module on a finite index type. -/
@[stacks 0FNZ "(1), for the modules of an algebraic space"]
theorem exists_cover_retract_finiteFree_of_exactPairing
    (M N : Modules.{u, u} B S hS F hF) (p : ExactPairing M N)
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    ∃ T : Sieve U, T ∈ (smallEtaleRingedSite B S hS F hF).J U ∧
      ∀ (V : (smallEtaleRingedSite B S hS F hF).C) (i : V ⟶ U), T i →
        ∃ I : Type u, Finite I ∧
          Nonempty (Retract (M.over V)
            (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS F hF).O).over V) I)) := by
  let := Stacks.SheafOfModules.Strict.monoidalCategoryStruct
    (structureSheaf B S hS F hF).obj (structureRingPresheaf_isSheaf B S hS F hF)
  let := Stacks.SheafOfModules.Strict.monoidalCategory
    (structureSheaf B S hS F hF).obj (structureRingPresheaf_isSheaf B S hS F hF)
  let : (Stacks.SheafOfModules.Strict.toLocalizedMonoidal
      (structureSheaf B S hS F hF).obj (structureRingPresheaf_isSheaf B S hS F hF)).Full :=
    ⟨fun f => ⟨f, rfl⟩⟩
  let : (Stacks.SheafOfModules.Strict.toLocalizedMonoidal
      (structureSheaf B S hS F hF).obj (structureRingPresheaf_isSheaf B S hS F hF)).Monoidal :=
    (CategoryTheory.Monoidal.fromInducedCoreMonoidal
      (Stacks.SheafOfModules.Strict.toLocalizedMonoidal
        (structureSheaf B S hS F hF).obj (structureRingPresheaf_isSheaf B S hS F hF))
      (Stacks.SheafOfModules.Strict.inducingFunctorData
        (structureSheaf B S hS F hF).obj
          (structureRingPresheaf_isSheaf B S hS F hF))).toMonoidal
  let : ExactPairing
      ((Stacks.SheafOfModules.Strict.toLocalizedMonoidal (structureSheaf B S hS F hF).obj
        (structureRingPresheaf_isSheaf B S hS F hF)).obj M)
      ((Stacks.SheafOfModules.Strict.toLocalizedMonoidal (structureSheaf B S hS F hF).obj
        (structureRingPresheaf_isSheaf B S hS F hF)).obj N) := p
  let := ExactPairing.ofFullyFaithful
    (Stacks.SheafOfModules.Strict.toLocalizedMonoidal (structureSheaf B S hS F hF).obj
      (structureRingPresheaf_isSheaf B S hS F hF)) M N
  exact Stacks.SheafOfModules.exists_cover_retract_finiteFree_of_exactPairing_tensorSheaf
    (structureSheaf B S hS F hF).obj (structureRingPresheaf_isSheaf B S hS F hF) M N
    inferInstance U

end AlgebraicGeometry.Space

end
