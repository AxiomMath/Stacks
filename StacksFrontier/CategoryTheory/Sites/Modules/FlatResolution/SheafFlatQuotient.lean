module

public import StacksFrontier.CategoryTheory.Sites.Modules.FlatResolution.PresheafFlatQuotient
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
import StacksCore.Tactic.StacksAttribute

/-!
# Every sheaf of modules is a quotient of a flat one

Let `O` be a sheaf of commutative rings on a site and `F` a sheaf of `O`-modules. The
underlying presheaf of `F` is a quotient of a flat presheaf of modules (Stacks 03EW part (2)),
and sheafification is exact and carries flat presheaves of modules to flat sheaves of modules
(Stacks 03ET), so `F` itself is a quotient of a flat sheaf of modules.

This is part (4) of Stacks 03EW.

## Main results

* `Stacks.SheafOfModules.FlatResolution.exists_epi_from_flat`: part (4), the flat cover of a
  sheaf of modules.

## Implementation notes

The proof is the source's, and it goes through the *presheaf* statement rather than through
part (3): the sheaf produced is the sheafification of the flat presheaf covering the underlying
presheaf of `F`, and the covering map is the sheafification of the presheaf covering map
followed by the counit of the sheafification adjunction, which is an isomorphism on a sheaf.
Part (3), the presentation by a direct sum of extensions by zero of structure sheaves, is a
different and sharper statement, available on this branch as
`Stacks.SheafOfModules.exists_epi_from_sum_extensionByZero`; it is not used here, because its
summands `j_{U!} O_U` have their module carriers in the universe of the ring's sections, which
in general is strictly smaller than the ambient module universe required here.

Quotients are expressed as epimorphisms, and all four universes are independent.

## References

* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 03ET](https://stacks.math.columbia.edu/tag/03ET)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w z

namespace Stacks.SheafOfModules.FlatResolution

open AlgebraicGeometry.SheafOfModules (ringPresheaf)

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w z}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w z}]

/-- **Stacks 03EW, part (4).** Every sheaf of modules over a sheaf of commutative rings is a
quotient of a flat sheaf of modules. -/
@[stacks 03EW "part (4)"]
theorem exists_epi_from_flat (O : Sheaf J CommRingCat.{w})
    (F : _root_.SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    ∃ P : _root_.SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf O),
      AlgebraicGeometry.SheafOfModules.IsFlat P ∧ ∃ (p : P ⟶ F), Epi p := by
  obtain ⟨P, hP, p, hp⟩ := exists_epi_from_flat_presheaf.{v, u, w, z} O.obj F.val
  let a : ringPresheaf O.obj ⟶ (Stacks.SheafOfModules.Tensor.ringSheaf O).obj :=
    𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
  have : Presheaf.IsLocallyInjective J a :=
    Presheaf.isLocallyInjective_of_injective J a fun _ _ _ h => h
  have : Presheaf.IsLocallySurjective J a :=
    Presheaf.isLocallySurjective_of_surjective J a fun _ x => ⟨x, rfl⟩
  let S := _root_.PresheafOfModules.sheafification.{max u v w z}
    (R := Stacks.SheafOfModules.Tensor.ringSheaf O) a
  let A := _root_.PresheafOfModules.sheafificationAdjunction.{max u v w z}
    (R := Stacks.SheafOfModules.Tensor.ringSheaf O) a
  exact ⟨S.obj P, Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification J a P hP,
    S.map p ≫ A.counit.app F,
    epi_comp' ((Functor.preservesEpimorphisms_of_adjunction A).preserves p)
      (IsIso.epi_of_iso (A.counit.app F))⟩

end Stacks.SheafOfModules.FlatResolution

end
