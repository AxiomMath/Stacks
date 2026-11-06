module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ModuleAlgebraData
public import StacksFrontier.AlgebraicGeometry.EtaleAlgebra.FlatBaseChange.AlgebraComparison
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafMultiplication
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionEquivalenceOfCompletion

/-!
# A module structure from an algebra sheaf

Let `E` be a module on a scheme `X` and `C` an algebra sheaf on `X` whose underlying module is
isomorphic to `E`. Then `E` carries a `Stacks.FundamentalGroup.ModuleAlgebraData` (a
multiplication `E ⊗ E ⟶ E` and a unit, subject to commutativity, associativity and the unit law)
whose associated algebra sheaf is isomorphic to `C`. In particular, if the pullbacks of `C` along
a family of morphisms `v n : Y n ⟶ X` realize a family of algebra sheaves `B n`, so do the
pullbacks of the algebra sheaf of this data. This is the shape of the input `hdata` of
`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_moduleAlgebraData`.

A `ModuleAlgebraData E` is, field for field, a sheaf-of-commutative-rings structure on the
presheaf `E.val` together with an `𝒪_X`-algebra structure map: that is what
`Stacks.FundamentalGroup.PresheafAlgebraData.ringPresheaf` and
`Stacks.FundamentalGroup.algebraSheafOfModule` make of it. This file shows that the passage is
reversible up to isomorphism (`Stacks.FundamentalGroup.algebraSheafOfModuleAlgebraIso`), and that
the reverse passage needs no descent, no coherence and no proper support, only the algebra sheaf
itself.

## Implementation notes

The multiplication is built on sections, from
`Stacks.RelativeSpec.AlgebraSheaf.multiplicationPresheaf`, the multiplication of an algebra sheaf
on the *pointwise* tensor square. `ModuleAlgebraData.mul` is a morphism of presheaves of modules,
the pointwise tensor square is Mathlib's monoidal product of presheaves of modules on the nose,
and the three laws are stated on local sections, where the commutative-ring laws of `C` compute.
Nothing is sheafified.

Everything is stated in the `AlgebraicGeometry.Scheme.ringCatSheaf` spelling of the structure
sheaf:

* Mathlib's monoidal structure on presheaves of modules is keyed on the syntactic shape
  `R ⋙ forget₂ CommRingCat RingCat`, which `X.ringCatSheaf.obj` does not match, because
  `CategoryTheory.sheafCompose` is a plain `def`. `presheafOfModulesMonoidalOfScheme` re-seats it
  at `R := X.presheaf`; this is the local instance with which the `mul` field of
  `Stacks.FundamentalGroup.ModuleAlgebraData` is stated, so the `⊗` below is that field's `⊗`.
* `Stacks.FundamentalGroup.sectionsModuleForgetPresheaf`, made a local instance here, is the
  companion for the module structure on sections at the ring-presheaf spelling.
* `Stacks.RelativeSpec.AlgebraSheaf.multiplicationPresheaf` is typed over
  `Stacks.SheafOfModules.TensorStalkRingedSpace.presheafTensor`, which is Mathlib's `⊗` by `rfl`
  (`Stacks.TensorSheafDedup.presheafTensor_eq_monoidalTensorObj`), so `mulOfAlgebraSheaf` is the
  composite written out and `mulOfAlgebraSheaf_tmul` is `rfl`.

## Main results

* `Stacks.FundamentalGroup.mulOfAlgebraSheaf` — the multiplication on a module identified with the
  module underlying an algebra sheaf, as a morphism of presheaves of modules out of the monoidal
  tensor square, with `mulOfAlgebraSheaf_tmul` computing it on pure tensors.
* `Stacks.FundamentalGroup.moduleAlgebraDataOfAlgebraSheaf` — the multiplication, the unit and
  the three laws. The unit is the structure morphism of the algebra sheaf read through the
  identification.
* `Stacks.FundamentalGroup.algebraSheafOfModuleAlgebraIso` — the algebra sheaf built from that
  data is isomorphic, as an algebra sheaf, to the one it came from.
* `Stacks.FundamentalGroup.exists_moduleAlgebraData_of_algebraPullback_iso` — the two together:
  an algebra sheaf whose pullbacks realize a family `(B n)` yields a `ModuleAlgebraData` whose
  algebra sheaf has the same pullbacks.

## References

* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 0A42](https://stacks.math.columbia.edu/tag/0A42)
* [Stacks Project, Tag 0899](https://stacks.math.columbia.edu/tag/0899)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry
open Stacks.RelativeSpec (AlgebraSheaf)

universe u

namespace Stacks.FundamentalGroup

/-! ### The two spellings of the ring of sections -/

/-- Mathlib's monoidal structure on presheaves of modules, re-seated at
`AlgebraicGeometry.Scheme.ringCatSheaf`. Instance search is keyed syntactically on
`R ⋙ forget₂ CommRingCat RingCat` and `CategoryTheory.sheafCompose` is not reducible, so the
instance is not found at `X.ringCatSheaf.obj` on its own. The `mul` field of
`Stacks.FundamentalGroup.ModuleAlgebraData` is stated with the same local instance. -/
local instance presheafOfModulesMonoidalOfScheme (X : Scheme.{u}) :
    MonoidalCategory (PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

attribute [local instance] sectionsModuleForgetPresheaf

/-- The module structure on sections at the `X.presheaf ⋙ forget₂ _ _` spelling of the ring of
sections: `Stacks.FundamentalGroup.sectionsModuleForgetPresheaf`. -/
alias moduleOnSectionsAtRingPresheaf := sectionsModuleForgetPresheaf

/-! ### The ring laws on sections of an algebra sheaf, at the module spelling -/

variable {X : Scheme.{u}}

/-- Commutativity of the product of sections of an algebra sheaf. This is
`Stacks.RelativeSpec.AlgebraSheaf.mulSection`'s own commutativity; it is named because
`mulSection` is a `def`, so the elaborator does not find `mul_comm` at a goal stated with it. -/
theorem algebraMulSection_comm (C : AlgebraSheaf X) (U : X.Opensᵒᵖ) (a b : C.right.obj.obj U) :
    AlgebraSheaf.mulSection C U a b = AlgebraSheaf.mulSection C U b a :=
  mul_comm a b

/-- Associativity of the product of sections of an algebra sheaf, both factorisations written
with `Stacks.RelativeSpec.AlgebraSheaf.mulSection`. -/
theorem algebraMulSection_assoc (C : AlgebraSheaf X) (U : X.Opensᵒᵖ)
    (a b c : C.right.obj.obj U) :
    AlgebraSheaf.mulSection C U (AlgebraSheaf.mulSection C U a b) c =
      AlgebraSheaf.mulSection C U a (AlgebraSheaf.mulSection C U b c) :=
  mul_assoc a b c

/-- The unit section of an algebra sheaf is a left unit for the product of sections. -/
theorem algebraOneSection_mul (C : AlgebraSheaf X) (U : X.Opensᵒᵖ) (a : C.right.obj.obj U) :
    AlgebraSheaf.mulSection C U (AlgebraSheaf.oneSection C U) a = a :=
  one_mul a

/-! ### The multiplication, the unit and the three laws -/

section Data

variable (E : X.Modules) (C : AlgebraSheaf X) (ι : AlgebraSheaf.underlyingModule C ≅ E)

/-- **The multiplication a module inherits from an algebra sheaf it is identified with**, as a
morphism of presheaves of modules out of the monoidal tensor square — the shape
`Stacks.FundamentalGroup.ModuleAlgebraData.mul` asks for.

It is the multiplication of `C` on the *pointwise* tensor square,
`Stacks.RelativeSpec.AlgebraSheaf.multiplicationPresheaf`, conjugated by `ι`. Nothing is
sheafified: the pointwise tensor square is Mathlib's monoidal product of presheaves of modules on
the nose (`Stacks.TensorSheafDedup.presheafTensor_eq_monoidalTensorObj`), so the composite is
written out and needs no comparison map. -/
def mulOfAlgebraSheaf : E.val ⊗ E.val ⟶ E.val :=
  (ι.inv.val ⊗ₘ ι.inv.val) ≫ AlgebraSheaf.multiplicationPresheaf C ≫ ι.hom.val

/-- The inherited multiplication, on a pure tensor of local sections: it is the product in `C`,
taken after and undone before the identification. -/
theorem mulOfAlgebraSheaf_tmul (U : X.Opensᵒᵖ) (x y : E.val.obj U) :
    (mulOfAlgebraSheaf E C ι).app U (x ⊗ₜ[Γ(X, U.unop)] y) =
      (ι.hom.val.app U).hom
        (AlgebraSheaf.mulSection C U ((ι.inv.val.app U).hom x) ((ι.inv.val.app U).hom y)) :=
  rfl

/-- The identification, undone on sections, in one direction. -/
theorem underlyingModuleIso_inv_hom_apply (U : X.Opensᵒᵖ)
    (a : (AlgebraSheaf.underlyingModule C).val.obj U) :
    (ι.inv.val.app U).hom ((ι.hom.val.app U).hom a) = a :=
  congrArg (fun k : AlgebraSheaf.underlyingModule C ⟶ AlgebraSheaf.underlyingModule C =>
    (k.val.app U).hom a) ι.hom_inv_id

/-- The identification, undone on sections, in the other direction. -/
theorem underlyingModuleIso_hom_inv_apply (U : X.Opensᵒᵖ) (x : E.val.obj U) :
    (ι.hom.val.app U).hom ((ι.inv.val.app U).hom x) = x :=
  congrArg (fun k : E ⟶ E => (k.val.app U).hom x) ι.inv_hom_id

/-- **The multiplication, the unit and the three algebra laws on a module, from an algebra sheaf
the module is identified with.**

The unit is the structure morphism of `C` as a morphism of modules
(`Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap`) read through `ι`, the multiplication is
`Stacks.FundamentalGroup.mulOfAlgebraSheaf`, and each of `mul_comm`, `mul_assoc` and `one_mul`
is the corresponding law of the commutative ring of sections of `C`, transported along `ι`. -/
def moduleAlgebraDataOfAlgebraSheaf : ModuleAlgebraData E where
  unit := AlgebraSheaf.unitModuleMap C ≫ ι.hom
  mul := mulOfAlgebraSheaf E C ι
  mul_comm U x y := by
    rw [mulOfAlgebraSheaf_tmul, mulOfAlgebraSheaf_tmul]
    exact congrArg (ι.hom.val.app U).hom (algebraMulSection_comm C U _ _)
  mul_assoc U x y z := by
    rw [mulOfAlgebraSheaf_tmul, mulOfAlgebraSheaf_tmul, mulOfAlgebraSheaf_tmul,
      mulOfAlgebraSheaf_tmul, underlyingModuleIso_inv_hom_apply,
      underlyingModuleIso_inv_hom_apply]
    exact congrArg (ι.hom.val.app U).hom (algebraMulSection_assoc C U _ _ _)
  one_mul U x := by
    rw [mulOfAlgebraSheaf_tmul]
    change (ι.hom.val.app U).hom (AlgebraSheaf.mulSection C U
      ((ι.inv.val.app U).hom ((ι.hom.val.app U).hom
        (AlgebraSheaf.structSection C U (1 : Γ(X, U.unop))))) _) = x
    rw [underlyingModuleIso_inv_hom_apply, AlgebraSheaf.structSection_one]
    exact (congrArg (ι.hom.val.app U).hom
      (algebraOneSection_mul C U ((ι.inv.val.app U).hom x))).trans
      (underlyingModuleIso_hom_inv_apply E C ι U x)

/-! ### The algebra sheaf it builds is the one it came from -/

/-- The comparison of underlying modules: the algebra sheaf built from
`Stacks.FundamentalGroup.moduleAlgebraDataOfAlgebraSheaf` has the sections of `E` as its sections,
and `Stacks.FundamentalGroup.algebraSheafOfModuleIso` identifies its underlying module with `E`,
so composing with `ι.inv` lands in the underlying module of `C`. It is an isomorphism of modules
by construction; `Stacks.FundamentalGroup.algebraSheafOfModuleAlgebraIso` is where it is promoted
to an isomorphism of algebra sheaves. -/
def algebraSheafOfModuleCompare :
    AlgebraSheaf.underlyingModule
        (algebraSheafOfModule E (moduleAlgebraDataOfAlgebraSheaf E C ι)) ⟶
      AlgebraSheaf.underlyingModule C :=
  (algebraSheafOfModuleIso E (moduleAlgebraDataOfAlgebraSheaf E C ι)).hom ≫ ι.inv

/-- The comparison of underlying modules is `ι.inv` on sections: the identification of the
sections of the constructed algebra sheaf with those of `E` is the identity on carriers. -/
theorem algebraSheafOfModuleCompare_app (U : X.Opensᵒᵖ)
    (a : (algebraSheafOfModule E (moduleAlgebraDataOfAlgebraSheaf E C ι)).right.obj.obj U) :
    ((algebraSheafOfModuleCompare E C ι).val.app U).hom a =
      (ι.inv.val.app U).hom (show E.val.obj U from a) :=
  rfl

/-- The comparison is unital on sections: the unit of the constructed algebra sheaf is the image
of the unit section of `C`. -/
theorem algebraSheafOfModuleCompare_oneSection (U : X.Opensᵒᵖ) :
    ((algebraSheafOfModuleCompare E C ι).val.app U).hom
        (AlgebraSheaf.oneSection
          (algebraSheafOfModule E (moduleAlgebraDataOfAlgebraSheaf E C ι)) U) =
      AlgebraSheaf.oneSection C U := by
  refine Eq.trans (algebraSheafOfModuleCompare_app E C ι U _) ?_
  show (ι.inv.val.app U).hom ((ι.hom.val.app U).hom
    (AlgebraSheaf.structSection C U (1 : Γ(X, U.unop)))) = _
  exact (underlyingModuleIso_inv_hom_apply E C ι U _).trans (AlgebraSheaf.structSection_one C U)

/-- The comparison is multiplicative on sections: the product of the constructed algebra sheaf is
the product of `C`, conjugated by `ι`, so conjugating back is a ring homomorphism. -/
theorem algebraSheafOfModuleCompare_mulSection (U : X.Opensᵒᵖ)
    (a b : (algebraSheafOfModule E (moduleAlgebraDataOfAlgebraSheaf E C ι)).right.obj.obj U) :
    ((algebraSheafOfModuleCompare E C ι).val.app U).hom
        (AlgebraSheaf.mulSection
          (algebraSheafOfModule E (moduleAlgebraDataOfAlgebraSheaf E C ι)) U a b) =
      AlgebraSheaf.mulSection C U
        (((algebraSheafOfModuleCompare E C ι).val.app U).hom a)
        (((algebraSheafOfModuleCompare E C ι).val.app U).hom b) := by
  refine Eq.trans (algebraSheafOfModuleCompare_app E C ι U _) ?_
  show (ι.inv.val.app U).hom ((ι.hom.val.app U).hom
    (AlgebraSheaf.mulSection C U ((ι.inv.val.app U).hom (show E.val.obj U from a))
      ((ι.inv.val.app U).hom (show E.val.obj U from b)))) = _
  exact underlyingModuleIso_inv_hom_apply E C ι U _

/-- **The algebra sheaf of the constructed data is the algebra sheaf it was constructed from.**
The comparison of underlying modules is multiplicative and unital on sections, so
`Stacks.RelativeSpec.AlgebraSheaf.homOfMultiplicative` promotes it to a morphism of algebra
sheaves; its morphism of underlying modules is the comparison itself
(`Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap_homOfMultiplicative`), which is an
isomorphism, and `Stacks.FundamentalGroup.isIso_of_isIso_underlyingModuleMap` reflects that. -/
def algebraSheafOfModuleAlgebraIso :
    algebraSheafOfModule E (moduleAlgebraDataOfAlgebraSheaf E C ι) ≅ C := by
  refine @asIso _ _ _ _ (AlgebraSheaf.homOfMultiplicative
    (algebraSheafOfModuleCompare E C ι) (algebraSheafOfModuleCompare_oneSection E C ι)
    (algebraSheafOfModuleCompare_mulSection E C ι)) (isIso_of_isIso_underlyingModuleMap _ ?_)
  rw [AlgebraSheaf.underlyingModuleMap_homOfMultiplicative]
  exact inferInstanceAs (IsIso ((algebraSheafOfModuleIso E
    (moduleAlgebraDataOfAlgebraSheaf E C ι)).hom ≫ ι.inv))

/-- **A module identified with the module underlying an algebra sheaf carries a
`Stacks.FundamentalGroup.ModuleAlgebraData` whose algebra sheaf is that algebra sheaf.** -/
theorem exists_moduleAlgebraData_of_algebraSheaf
    (E : X.Modules) (C : AlgebraSheaf X) (ι : AlgebraSheaf.underlyingModule C ≅ E) :
    ∃ d : ModuleAlgebraData E, Nonempty (algebraSheafOfModule E d ≅ C) :=
  ⟨moduleAlgebraDataOfAlgebraSheaf E C ι, ⟨algebraSheafOfModuleAlgebraIso E C ι⟩⟩

end Data

/-! ### Realizing a family of pullbacks -/

/-- **A module identified with an algebra sheaf whose pullbacks realize a family `(B n)` carries
a `Stacks.FundamentalGroup.ModuleAlgebraData` whose algebra sheaf has the same pullbacks.** Let
`E` be a module on `X`, `v n : Y n ⟶ X` a family of morphisms and `B n` a family of algebra
sheaves on the `Y n`. If an algebra sheaf `C` on `X` has underlying module isomorphic to `E` and
`(algebraPullback (v n)).obj C ≅ B n` for every `n`, then the data
`Stacks.FundamentalGroup.moduleAlgebraDataOfAlgebraSheaf` has an algebra sheaf with the same
pullbacks.

Conversely, by `AlgebraicGeometry.nonempty_algebraTransition_of_algebraPullback_iso`, an algebra
sheaf whose pullbacks realize `(B n)` forces the family to be cartesian. -/
theorem exists_moduleAlgebraData_of_algebraPullback_iso {X : Scheme.{u}} (E : X.Modules)
    {Y : ℕ → Scheme.{u}} (v : ∀ n, Y n ⟶ X) (B : ∀ n, AlgebraSheaf (Y n))
    (C : AlgebraSheaf X) (ι : AlgebraSheaf.underlyingModule C ≅ E)
    (hC : ∀ n, Nonempty ((Stacks.AffineAlgebraEquivalence.algebraPullback (v n)).obj C ≅ B n)) :
    ∃ d : ModuleAlgebraData E, ∀ n, Nonempty
      ((Stacks.AffineAlgebraEquivalence.algebraPullback (v n)).obj
        (algebraSheafOfModule E d) ≅ B n) :=
  ⟨moduleAlgebraDataOfAlgebraSheaf E C ι, fun n => (hC n).map fun e =>
    (Stacks.AffineAlgebraEquivalence.algebraPullback (v n)).mapIso
      (algebraSheafOfModuleAlgebraIso E C ι) ≪≫ e⟩

end Stacks.FundamentalGroup

end
