module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# Sheaf cohomology over a terminal object is global sheaf cohomology

Mathlib carries two models of the sheaf cohomology of an abelian sheaf `F` on a site `(C, J)`.
`CategoryTheory.Sheaf.H F n` is the `Ext`-group out of the constant abelian sheaf with value
`ULift ℤ`, and `CategoryTheory.Sheaf.H' F n U` is the `Ext`-group out of the sheafification of
the free abelian presheaf on `yoneda.obj U`, the value at `U` of the cohomology presheaf. The
two are the same thing when `U` is a terminal object of `C`, and this file proves it; the
statement is a `TODO` of `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.

The argument is that the two corepresenting sheaves agree. For `U` terminal the presheaf
`yoneda.obj U` is terminal in presheaves of types — every `V ⟶ U` is the unique such map — hence
constant with value `PUnit`; the free abelian group on `PUnit` is `ℤ`; and sheafification of a
constant presheaf is the constant sheaf by the very definition of
`CategoryTheory.constantSheaf`. Transporting `Ext` along the resulting isomorphism of sheaves is
then functoriality of `CategoryTheory.Abelian.extFunctor` in its first variable.

## Main definitions

* `Stacks.Cohomology.TerminalCohomology.freeOfTerminalIsoConstantSheaf`: the free abelian sheaf
  on `yoneda.obj U` for terminal `U` is the constant sheaf with value `ULift ℤ`. This is the
  whole content; everything after it is transport.
* `Stacks.Cohomology.TerminalCohomology.h'IsoH` and `h'AddEquivH`: **the comparison**
  `H^n(U, F) ≅ H^n(F)` for terminal `U`, as an isomorphism of `AddCommGrpCat` and as an
  additive equivalence of the underlying groups.

## Main results

* `Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'`: the vanishing of
  the one is the vanishing of the other. This is the form in which the comparison is consumed by
  a vanishing theorem stated over quasi-compact opens, such as Stacks 0A3G, whose conclusion is
  about `Sheaf.H'` while its consumers ask for `Sheaf.H`.
* `Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top`: the same for
  the site of opens of a topological space, whose terminal object is `⊤`
  (`Stacks.Cohomology.TerminalCohomology.topIsTerminal`).

## Implementation notes

No `@[stacks]` attribute is placed: this is a comparison of two of Mathlib's definitions and not
a statement of the Stacks project.

The isomorphism of presheaves of types is proved by `NatIso.ofComponents` with naturality
`rfl`: the target is constant with value `PUnit`, so both sides of every naturality square are
maps into a subsingleton. The free-abelian-group step is Mathlib's
`FreeAbelianGroup.uniqueEquiv` composed with `AddEquiv.ulift.symm`, since the coefficient group
of `Sheaf.H` is `ULift ℤ` and not `ℤ`.

`Sheaf.H` is stated for coefficients in `AddCommGrpCat.{w}` and `Sheaf.H'` for coefficients in
`AddCommGrpCat.{v}` with `v` the universe of the homs of `C`; the comparison therefore exists
only at `w = v`, which is how both are instantiated throughout this repository.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace

universe w' v u

namespace Stacks.Cohomology.TerminalCohomology

variable {C : Type u} [Category.{v} C]

/-! ### The two corepresenting sheaves agree -/

/-- For a terminal object `U` the presheaf of types `yoneda.obj U` is constant with value
`PUnit`: there is exactly one morphism `V ⟶ U` for every `V`. Naturality is `rfl`, both sides of
every square being maps into a subsingleton. -/
def yonedaObjIsoConstPUnit (U : C) (hU : IsTerminal U) :
    yoneda.obj U ≅ (Functor.const Cᵒᵖ).obj (PUnit.{v + 1}) :=
  NatIso.ofComponents
    (fun V => Equiv.toIso
      (@Equiv.equivPUnit _ ⟨⟨hU.from V.unop⟩, fun _ => hU.hom_ext _ _⟩))
    (fun _ => rfl)

/-- The free abelian group on `PUnit` is `ULift ℤ`, the coefficient group of
`CategoryTheory.Sheaf.H`. -/
def freeObjPUnitIsoULiftInt :
    AddCommGrpCat.free.obj (PUnit.{v + 1}) ≅ AddCommGrpCat.of (ULift.{v} ℤ) :=
  ((FreeAbelianGroup.uniqueEquiv PUnit.{v + 1}).trans AddEquiv.ulift.symm).toAddCommGrpIso

/-- For a terminal object `U` the free abelian presheaf on `yoneda.obj U` is the constant
presheaf with value `ULift ℤ`. -/
def freeYonedaIsoConstULiftInt (U : C) (hU : IsTerminal U) :
    yoneda.obj U ⋙ AddCommGrpCat.free ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  Functor.isoWhiskerRight (yonedaObjIsoConstPUnit U hU) AddCommGrpCat.free ≪≫
    Functor.constComp _ _ _ ≪≫ (Functor.const Cᵒᵖ).mapIso freeObjPUnitIsoULiftInt

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]

/-- **The comparison of corepresenting sheaves.** For a terminal object `U` the sheaf
corepresenting `CategoryTheory.Sheaf.H' · n U` — the sheafification of the free abelian presheaf
on `yoneda.obj U` — is the constant sheaf with value `ULift ℤ`, which corepresents
`CategoryTheory.Sheaf.H · n`.

This is the whole content of the comparison. `CategoryTheory.constantSheaf` is by definition the
constant presheaf followed by sheafification, so the right-hand side needs no rewriting. -/
def freeOfTerminalIsoConstantSheaf (U : C) (hU : IsTerminal U) :
    (presheafToSheaf J AddCommGrpCat.{v}).obj (yoneda.obj U ⋙ AddCommGrpCat.free) ≅
      (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  (presheafToSheaf J AddCommGrpCat.{v}).mapIso (freeYonedaIsoConstULiftInt U hU)

/-! ### The comparison on cohomology -/

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

/-- **Sheaf cohomology over a terminal object is global sheaf cohomology.** For an abelian sheaf
`F` on a site `(C, J)`, a degree `n` and a terminal object `U` of `C`,
`H^n(U, F) ≅ H^n(F)`.

Both groups are `Ext`-groups out of the two sheaves compared by
`freeOfTerminalIsoConstantSheaf`, and both identifications are definitional, so this is that
isomorphism transported along `CategoryTheory.Abelian.extFunctor` in its first variable. -/
def h'IsoH (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (U : C) (hU : IsTerminal U) :
    Sheaf.H' F n U ≅ AddCommGrpCat.of (Sheaf.H.{w'} F n) :=
  ((extFunctor n).mapIso (freeOfTerminalIsoConstantSheaf J U hU).symm.op).app F

/-- The comparison `H^n(U, F) ≅ H^n(F)` of `h'IsoH`, read as an additive equivalence of the
underlying groups. -/
def h'AddEquivH (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (U : C) (hU : IsTerminal U) :
    Sheaf.H' F n U ≃+ Sheaf.H.{w'} F n :=
  (h'IsoH J F n U hU).addCommGroupIsoToAddEquiv

/-- **The comparison of `h'IsoH`, as functors of the abelian sheaf.** For a terminal object `U`
of `C`, evaluating the degree-`n` cohomology presheaf at `U` is the degree-`n` global cohomology
functor `CategoryTheory.Sheaf.functorH`.

This is `h'IsoH` before it is applied to a sheaf — see `functorHIso_app` — and is what makes the
comparison natural in the abelian sheaf for free. -/
def functorHIso (U : C) (hU : IsTerminal U) (n : ℕ) :
    Sheaf.cohomologyPresheafFunctor J n ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{w'}).obj (op U) ≅
      (Sheaf.functorH J n : Sheaf J AddCommGrpCat.{v} ⥤ AddCommGrpCat.{w'}) :=
  (extFunctor n).mapIso (freeOfTerminalIsoConstantSheaf J U hU).symm.op

/-- `functorHIso` is `h'IsoH` before it is applied to a sheaf. -/
theorem functorHIso_app (U : C) (hU : IsTerminal U) (n : ℕ) (F : Sheaf J AddCommGrpCat.{v}) :
    (functorHIso J U hU n).app F = h'IsoH J F n U hU := rfl

/-- **Vanishing over a terminal object is global vanishing.** A vanishing theorem whose
conclusion is about `CategoryTheory.Sheaf.H'` over quasi-compact opens, such as clause (1) of
Stacks 0A3G, is therefore a vanishing theorem about `CategoryTheory.Sheaf.H` once it is applied
at a terminal object. -/
theorem subsingleton_H_iff_subsingleton_H' (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (U : C)
    (hU : IsTerminal U) :
    Subsingleton (Sheaf.H.{w'} F n) ↔ Subsingleton (Sheaf.H' F n U) :=
  ⟨fun _ => (h'AddEquivH J F n U hU).toEquiv.subsingleton,
   fun _ => (h'AddEquivH J F n U hU).toEquiv.symm.subsingleton⟩

/-! ### The site of opens of a topological space -/

section Opens

variable {X : Type u} [TopologicalSpace X]

/-- The whole space is a terminal open: every open is contained in it, and the opens form a
poset, so the inclusion is the only morphism. This is data, not a proposition: `IsTerminal` is
an `IsLimit`. -/
def topIsTerminal : IsTerminal (⊤ : Opens X) :=
  IsTerminal.ofUniqueHom (fun _ => homOfLE le_top) (fun _ _ => Subsingleton.elim _ _)

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- **Vanishing of the cohomology presheaf at `⊤` is vanishing of global cohomology**, for an
abelian sheaf on a topological space. -/
theorem subsingleton_H_iff_subsingleton_H'_top
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Subsingleton (Sheaf.H.{w'} F n) ↔
      Subsingleton ((F.cohomologyPresheaf n).obj (op (⊤ : Opens X))) :=
  subsingleton_H_iff_subsingleton_H' (Opens.grothendieckTopology X) F n ⊤ topIsTerminal

end Opens

end Stacks.Cohomology.TerminalCohomology

end
