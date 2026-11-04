module

public import StacksFrontier.CategoryTheory.Sites.Modules.SectionsOverObjectCorepresentable

/-!
# `j_{⊤!} O = O`: at a terminal object the extension by zero of the structure sheaf is the
structure sheaf

Let `(C, O)` be a ringed site and let `U` be a *terminal* object of `C`.  Then the extension by
zero `j_{U!} O_U` of the structure sheaf of the slice site over `U` is the structure sheaf itself,
read as a module over itself: `j_{U!} O_U ≅ O`.

The reason is that both objects corepresent the same functor.  Stacks 0G1V says that
`Hom(j_{U!} O_U, -)` is the sections functor `Γ(U, -)`
(`Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv`), and morphisms out of the unit sheaf
of modules are its global sections (`CategoryTheory.SheafOfModules.unitHomEquiv`), which at a
terminal object *are* the sections there
(`Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal`).  Corepresenting objects agree,
`CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso`.

Consequently the free module `O^{⊕ι}` is a coproduct of copies of `j_{U!} O_U`: the tautological
presentation `CategoryTheory.SheafOfModules.isColimitFreeCofan` of `O^{⊕ι}` as a coproduct of
copies of the unit is read through the isomorphism above.  That is what lets a local free
surjection be fed to machinery stated in terms of extension-by-zero units, which is how the
lifting step of Stacks 08HE (2) ⇒ (1) is applied on an affine scheme with `U = ⊤`: there nothing
is shrunk and the surjection is global.

## Main definitions

* `Stacks.Sites.ExtensionByZero.unitHomEquivObjOfIsTerminal`: morphisms out of the structure
  sheaf are the sections at a terminal object.
* `Stacks.Sites.ExtensionByZero.corepresentableByUnit` and
  `Stacks.Sites.ExtensionByZero.corepresentableByExtensionByZeroUnit`: the two corepresentations
  of the sections functor at a terminal object.
* `Stacks.Sites.ExtensionByZero.extensionByZeroUnitObjIsoUnit`: **`j_{U!} O_U ≅ O`** at a
  terminal `U`.
* `Stacks.Sites.ExtensionByZero.freeCofanExtensionByZeroUnit`: the cofan of `ι` copies of
  `j_{U!} O_U` with point `O^{⊕ι}`.

## Main results

* `Stacks.Sites.ExtensionByZero.isColimitFreeCofanExtensionByZeroUnit`: that cofan is
  colimiting, i.e. **`O^{⊕ι}` is a coproduct of copies of `j_{U!} O_U`** at a terminal `U`.

## Implementation notes

The corepresentation by the unit is stated at independent universes for the site and the module
sections, since neither the extension-by-zero functor nor its existence hypothesis enters it; the
isomorphism itself is stated at the collapsed universes of
`Stacks.Sites.ExtensionByZero.extensionByZeroUnitObj`, which is what the ringed sites of the
derived development provide.

The identification is through the *type*-valued coyoneda embedding and not the preadditive one:
`CategoryTheory.Functor.CorepresentableBy` asks only for a bijection, so neither the additivity
of `Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomAddEquiv` nor a collapse of the site's
universes is needed. Note that `CategoryTheory.Functor.CorepresentableBy F X` does not force the
universe of the values of `F` to be the universe of the morphisms of the ambient category: the
bijection it carries is heterogeneous, so the sections functor valued in `Type w` corepresents
in a category whose morphisms lie in `Type (max u₁ w)`.

No `@[stacks]` attribute is carried: this is infrastructure for the induction of Stacks 08HE
(2) ⇒ (1), and the tag of the corepresentation it rests on stays on
`Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv`.

## References

* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero

section Unit

universe w v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{w}) (U : C)

/-- Morphisms out of the structure sheaf, read as a module over itself, are the sections at a
terminal object of the site: such a morphism is a global section
(`CategoryTheory.SheafOfModules.unitHomEquiv`), and a global section is its value at a terminal
object (`Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal`). -/
noncomputable def unitHomEquivObjOfIsTerminal (hU : IsTerminal U) (M : SheafOfModules.{w} R) :
    (SheafOfModules.unit R ⟶ M) ≃ (M.val.obj (op U) : Type w) :=
  M.unitHomEquiv.trans (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M hU)

/-- **Sections at a terminal object are corepresented by the structure sheaf.** -/
noncomputable def corepresentableByUnit (hU : IsTerminal U) :
    (SheafOfModules.evaluation.{w} R (op U) ⋙
        forget (ModuleCat.{w} (R.obj.obj (op U)))).CorepresentableBy
      (SheafOfModules.unit R) where
  homEquiv {M} := unitHomEquivObjOfIsTerminal R U hU M
  homEquiv_comp _ _ := rfl

end Unit

section Terminal

universe u

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{u}) (U : C)
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 0G1V as a corepresentation**: sections over `U` are corepresented by
`j_{U!} O_U`. -/
noncomputable def corepresentableByExtensionByZeroUnit :
    (SheafOfModules.evaluation.{u} R (op U) ⋙
        forget (ModuleCat.{u} (R.obj.obj (op U)))).CorepresentableBy
      (extensionByZeroUnitObj J R U) where
  homEquiv {M} := extensionByZeroUnitHomEquiv J R U M
  homEquiv_comp g f := extensionByZeroUnitHomEquiv_naturality J R U f g

/-- **`j_{U!} O_U ≅ O` at a terminal object.**  At the terminal object of the site the extension
by zero of the structure sheaf of the slice site is the structure sheaf itself: both corepresent
the sections functor there. -/
noncomputable def extensionByZeroUnitObjIsoUnit (hU : IsTerminal U) :
    extensionByZeroUnitObj J R U ≅ SheafOfModules.unit R :=
  (corepresentableByExtensionByZeroUnit J R U).uniqueUpToIso (corepresentableByUnit R U hU)

/-- The cofan of `ι` copies of `j_{U!} O_U` whose point is the free module `O^{⊕ι}`: the
injections are those of `CategoryTheory.SheafOfModules.free` read through
`Stacks.Sites.ExtensionByZero.extensionByZeroUnitObjIsoUnit`. -/
noncomputable abbrev freeCofanExtensionByZeroUnit (hU : IsTerminal U) (ι : Type u) :
    Cofan (fun _ : ι => extensionByZeroUnitObj J R U) :=
  Cofan.mk (SheafOfModules.free (R := R) ι)
    (fun i => (extensionByZeroUnitObjIsoUnit J R U hU).hom ≫ SheafOfModules.ιFree i)

/-- **The free module `O^{⊕ι}` is a coproduct of copies of `j_{U!} O_U`** at a terminal `U`.
This is the tautological presentation of `O^{⊕ι}` as a coproduct of copies of the unit,
`CategoryTheory.SheafOfModules.isColimitFreeCofan`, read through
`Stacks.Sites.ExtensionByZero.extensionByZeroUnitObjIsoUnit`. -/
noncomputable def isColimitFreeCofanExtensionByZeroUnit (hU : IsTerminal U) (ι : Type u) :
    IsColimit (freeCofanExtensionByZeroUnit J R U hU ι) :=
  IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv
        (Discrete.natIso fun _ => extensionByZeroUnitObjIsoUnit J R U hU)
        (SheafOfModules.freeCofan (R := R) ι)).symm (SheafOfModules.isColimitFreeCofan ι))
    (Cocones.ext (Iso.refl _) (fun j => by cases j; simp [SheafOfModules.freeCofan]))

end Terminal

end Stacks.Sites.ExtensionByZero

end
