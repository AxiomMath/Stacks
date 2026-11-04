module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.FlatFreeYoneda

/-!
# Every presheaf of modules is a quotient of a direct sum of flat generators

Every presheaf of `O`-modules on a site is a quotient of a direct sum of extensions by
zero `j_{U!}O_U` of rank-one modules from slices, and hence a quotient of a flat presheaf
of `O`-modules.

## Main results

* `Stacks.PresheafOfModules.FlatCover.exists_epi_from_coproduct_freeYoneda`: every presheaf of
  modules is a
  quotient of a direct sum of copies of `j_{U!}O_U`.
* `Stacks.PresheafOfModules.FlatCover.isFlat_freeYonedaCoproduct`: that direct sum is flat.
* `Stacks.PresheafOfModules.FlatCover.exists_epi_from_flat`: every presheaf of modules is a
  quotient of a flat
  presheaf of modules.

## Implementation notes

Quotients are expressed as epimorphisms, as in the source. The direct sum is indexed by
`PresheafOfModules.Elements M`, the pairs `(U, s)` with `s` a section of `M` over `U`, and
the generator attached to `(U, s)` is `j_{U!}O_U = PresheafOfModules.freeObj (yoneda.obj U)`
— the identification of Stacks Tag 03EV, as in
`Stacks.PresheafOfModules.FlatFreeYoneda.isFlat_freeYoneda`. The epimorphism is
Mathlib's `PresheafOfModules.fromFreeYonedaCoproduct`, which sends the canonical generator
of the summand at `(U, s)` to `s`; surjectivity is immediate from that, and is Mathlib's
`instance : Epi M.fromFreeYonedaCoproduct`.

Flatness of the direct sum does *not* go through "a direct sum of flat modules is flat".
It is cheaper and more direct: `PresheafOfModules.free` is a left adjoint
(`PresheafOfModules.freeAdjunction`), so it preserves coproducts, and therefore the direct
sum of the `j_{U!}O_U` is itself free — it is the free presheaf of modules on the direct
sum of the representable presheaves of types.
  `Stacks.PresheafOfModules.FlatFreeYoneda.isFlat_freeObj` then applies
to it directly.

The site is small and the ring universe is its object universe, which is where Mathlib
states the `Elements` presentation. Parts (1) and (2) of Stacks 03EW at the source's
generality — an arbitrary category, a presheaf of rings in its own universe, and a module
universe independent of both — are
`Stacks.SheafOfModules.FlatResolution.exists_epi_from_coproduct_extension` and
`Stacks.SheafOfModules.FlatResolution.exists_epi_from_flat_presheaf`; the statements here are
the special case that Mathlib's `freeYonedaCoproduct` covers directly.

## References

* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.PresheafOfModules.FlatCover

open AlgebraicGeometry.SheafOfModules

variable {C : Type u} [SmallCategory.{u} C] (O : Cᵒᵖ ⥤ CommRingCat.{u})
  (M : PresheafOfModules.{u} (ringPresheaf O))

/-! The next two are seated as named declarations rather than left to instance synthesis;
both report `failed to synthesize` when nested in the searches below. -/

/-- The free presheaf of modules functor preserves direct sums, being a left adjoint. -/
instance preservesColimitsOfSize_free :
    PreservesColimitsOfSize.{u, u} (_root_.PresheafOfModules.free (ringPresheaf O)) :=
  (_root_.PresheafOfModules.freeAdjunction (ringPresheaf O)).leftAdjoint_preservesColimits

/-- The canonical map onto `M` from the direct sum of its generators is an epimorphism. -/
instance epi_fromFreeYonedaCoproduct : Epi M.fromFreeYonedaCoproduct :=
  inferInstanceAs (Epi (_root_.PresheafOfModules.fromFreeYonedaCoproduct M))

/-- The direct sum of the generators `j_{U!}O_U`, one for each section of `M`, is the free
presheaf of modules on the direct sum of the corresponding representable presheaves of
types: `PresheafOfModules.free` is a left adjoint, so it preserves direct sums. -/
def freeYonedaCoproductIso :
    M.freeYonedaCoproduct ≅
      _root_.PresheafOfModules.freeObj (R := ringPresheaf O)
        (∐ fun m : M.Elements ↦ yoneda.obj m.1.unop) :=
  (HasColimit.isoOfNatIso
      (NatIso.ofComponents (fun _ ↦ Iso.refl _)
        (by rintro ⟨i⟩ ⟨j⟩ f; obtain rfl : i = j := f.1; simp) :
      Discrete.functor (_root_.PresheafOfModules.Elements.freeYoneda (M := M)) ≅
        Discrete.functor (fun m : M.Elements ↦ yoneda.obj m.1.unop) ⋙
          _root_.PresheafOfModules.free (ringPresheaf O))) ≪≫
    (preservesColimitIso (_root_.PresheafOfModules.free (ringPresheaf O))
      (Discrete.functor fun m : M.Elements ↦ yoneda.obj m.1.unop)).symm

/-- **The direct sum of the generators `j_{U!}O_U` is a flat presheaf of `O`-modules.** It
is itself free, by `freeYonedaCoproductIso`. -/
lemma isFlat_freeYonedaCoproduct :
    PresheafOfModules.IsFlat M.freeYonedaCoproduct :=
  Stacks.PresheafOfModules.FlatFreeYoneda.isFlat_of_iso O (freeYonedaCoproductIso O M).symm
    (Stacks.PresheafOfModules.FlatFreeYoneda.isFlat_freeObj O _)

/-- **Every presheaf of `O`-modules is a quotient of a direct sum of extensions by zero
`j_{U!}O_U` of rank-one modules from slices.** The sum is indexed by the sections of `M`,
the summand attached to a section over `U` being `j_{U!}O_U`, and the map sends the
canonical generator of that summand to the section. -/
theorem exists_epi_from_coproduct_freeYoneda :
    ∃ (ι : Type u) (U : ι → C)
      (π : (∐ fun i ↦ _root_.PresheafOfModules.freeObj (R := ringPresheaf O)
        (yoneda.obj (U i))) ⟶ M), Epi π :=
  ⟨M.Elements, fun m ↦ m.1.unop, M.fromFreeYonedaCoproduct,
    epi_fromFreeYonedaCoproduct O M⟩

/-- **Every presheaf of `O`-modules is a quotient of a flat presheaf of `O`-modules.** -/
theorem exists_epi_from_flat :
    ∃ (P : PresheafOfModules.{u} (ringPresheaf O)) (π : P ⟶ M),
      PresheafOfModules.IsFlat P ∧ Epi π :=
  ⟨M.freeYonedaCoproduct, M.fromFreeYonedaCoproduct,
    isFlat_freeYonedaCoproduct O M, inferInstance⟩

end Stacks.PresheafOfModules.FlatCover
