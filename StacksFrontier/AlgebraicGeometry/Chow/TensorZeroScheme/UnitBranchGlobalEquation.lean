module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.FunctionFieldDivisor
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence

/-!
# The first branch of Tag 0F97 is cut out by a global function when `L₁` is the structure sheaf

Instantiate the construction of [Stacks, Tag 0F97] at `L₁ = 𝒪_Y`. The first branch `D₁` is by
condition (3) of that tag the zero scheme of the section `s₁` of `p^*L₁ = p^*𝒪_Y`, and the
pullback of the structure sheaf is the structure sheaf, so `s₁` *is* a global function on the
ambient scheme `L` and `D₁ ⊆ L` is cut out by one equation globally — not merely locally.

This is the assertion of clause (3) of [Stacks, Tag 0F99], and it is the reason that tag
instantiates [Stacks, Tag 0F97] at `L₁ = 𝒪_Y` in the first place: the restricted condition (3)
of [Stacks, Tag 0F9A] applies to a divisor with trivial normal bundle, and a divisor cut out by
a global section of the structure sheaf has one.

Everything is proved first for an `L₁` merely *isomorphic* to `𝒪_Y`, because that is what the
closing base-change clause of [Stacks, Tag 0F99] needs: base change along `g : Y' ⟶ Y` turns
`L₁ = 𝒪_Y` into `g^*𝒪_Y`, which is isomorphic to `𝒪_{Y'}` and not equal to it.

## Main definitions

* `Stacks.Chow.TensorZeroScheme.unitBranchIso` — the identification `p^*L₁ ≅ 𝒪_L` attached to a
  trivialization of `L₁`.
* `Stacks.Chow.TensorZeroScheme.unitBranchEquationOfIso` and
  `Stacks.Chow.TensorZeroScheme.unitBranchEquation` — **the global function `s'` cutting out
  `D₁`**, the section `s₁` read through that identification, for a trivializable `L₁` and for
  `L₁ = 𝒪_Y` respectively.

## Main results

* `Stacks.Chow.TensorZeroScheme.branch₁_eq_zeroScheme_unitModule_of_iso` and
  `Stacks.Chow.TensorZeroScheme.branch₁_unit_eq_zeroScheme_unitModule` — `D₁` is the zero scheme
  of that global function.
* `Stacks.Chow.TensorZeroScheme.exists_globalSection_branch₁_of_iso` and
  `Stacks.Chow.TensorZeroScheme.exists_globalSection_branch₁_unit` — the same, as the existence
  statement clause (3) of [Stacks, Tag 0F99] asserts, with the section exhibited as an element
  of `Γ(L, ⊤)`.

## Implementation notes

Two spelling crossings are discharged here, both by type ascription and neither by a rewrite.

*The unit module and invertibility.* `AlgebraicGeometry.Scheme.unitModule` is a `def`, so the
instance `AlgebraicGeometry.isInvertible_unitModule` — stated at the reducible `abbrev`
`Stacks.Ample.unitModule` — is not found at this spelling by instance search, which matches at
reducible transparency. `AlgebraicGeometry.Scheme.Modules.isInvertible_unitModule` below is that
same instance re-registered at the `Scheme.unitModule` spelling, which is the one
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` is stated at and the one the rest of
`StacksDraft.AlgebraicGeometry.Chow.TensorZeroScheme` uses. It is not a second proof: its body
is the existing instance.

*Sections of the structure sheaf.* `Γ(Scheme.unitModule X, ⊤)` and `Γ(X, ⊤)` are the same type,
and the second is what "a global section of `𝒪_X`" means. The existence statement is therefore
quantified over `Γ(L, ⊤)` with a `show` ascription at the use site, the idiom of
`Stacks.Ample.smul_eq_mul_unitModule` and `Stacks.AlgebraicGeometry.ReflexiveModules.oneSection`.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F99](https://stacks.math.columbia.edu/tag/0F99)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- **The structure sheaf is invertible as a module over itself**, at the `Scheme.unitModule`
spelling. This is `AlgebraicGeometry.isInvertible_unitModule`, which is stated at the reducible
`Stacks.Ample.unitModule`; the two are definitionally equal, but instance search matches at
reducible transparency and so does not see through the `def` `Scheme.unitModule`. -/
instance isInvertible_unitModule (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.unitModule X) :=
  AlgebraicGeometry.isInvertible_unitModule X

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Chow.TensorZeroScheme

section OfIso

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.sheaf.obj,
    Presheaf.isSheaf_of_isSheaf_comp _ Y.sheaf.obj (forget₂ CommRingCat RingCat)
      Y.ringCatSheaf.property⟩).obj L₁).obj L₂, ⊤))

include h₁ h₂ in
/-- **The identification `p^*L₁ ≅ 𝒪_L` attached to a trivialization of `L₁`.** -/
def unitBranchIso (ε : L₁ ≅ Scheme.unitModule Y) :
    (Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₁ ≅
      Scheme.unitModule (spaceIdeal Y L₁ L₂ s).subscheme :=
  ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).mapIso ε).trans
    (Scheme.Modules.pullbackUnitIso (proj Y L₁ L₂ s))

include h₁ h₂ in
/-- **The global function cutting out the first branch, given a trivialization of `L₁`.** It is
the section `s₁` of `p^*L₁` read through
`Stacks.Chow.TensorZeroScheme.unitBranchIso`. -/
def unitBranchEquationOfIso (ε : L₁ ≅ Scheme.unitModule Y) :
    Γ(Scheme.unitModule (spaceIdeal Y L₁ L₂ s).subscheme, ⊤) :=
  Scheme.Modules.Hom.app (unitBranchIso Y L₁ L₂ s ε).hom ⊤ (section₁ Y L₁ L₂ s)

include h₁ h₂ in
/-- **Clause (3) of [Stacks, Tag 0F99], for a first module merely *isomorphic* to the structure
sheaf.** If `L₁ ≅ 𝒪_Y`, the first branch `D₁` of [Stacks, Tag 0F97] is the zero scheme of a
global section of `𝒪_L`.

This generality is what makes the closing base-change clause of [Stacks, Tag 0F99] available:
base change along `g : Y' ⟶ Y` replaces `L₁ = 𝒪_Y` by `g^*𝒪_Y`, which is *isomorphic* to
`𝒪_{Y'}` — by `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` — and not equal to it. -/
theorem branch₁_eq_zeroScheme_unitModule_of_iso (ε : L₁ ≅ Scheme.unitModule Y) :
    branch₁ Y L₁ L₂ s =
      AlgebraicGeometry.zeroScheme (spaceIdeal Y L₁ L₂ s).subscheme
        (Scheme.unitModule (spaceIdeal Y L₁ L₂ s).subscheme)
        (unitBranchEquationOfIso Y L₁ L₂ s ε) :=
  AlgebraicGeometry.zeroScheme_eq_of_iso (unitBranchIso Y L₁ L₂ s ε) rfl

include h₁ h₂ in
/-- **Clause (3) of [Stacks, Tag 0F99] for a trivializable first module, as the existence
statement the source asserts**: the first branch is the zero scheme of a global section of
`𝒪_L`. -/
theorem exists_globalSection_branch₁_of_iso (ε : L₁ ≅ Scheme.unitModule Y) :
    ∃ s' : Γ((spaceIdeal Y L₁ L₂ s).subscheme, ⊤),
      branch₁ Y L₁ L₂ s =
        AlgebraicGeometry.zeroScheme (spaceIdeal Y L₁ L₂ s).subscheme
          (Scheme.unitModule (spaceIdeal Y L₁ L₂ s).subscheme)
          (show Γ(Scheme.unitModule
            (spaceIdeal Y L₁ L₂ s).subscheme, ⊤) from s') :=
  ⟨unitBranchEquationOfIso Y L₁ L₂ s ε, branch₁_eq_zeroScheme_unitModule_of_iso Y L₁ L₂ s ε⟩

end OfIso

variable (Y : Scheme.{u}) (L₂ : Y.Modules)
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.sheaf.obj,
    Presheaf.isSheaf_of_isSheaf_comp _ Y.sheaf.obj (forget₂ CommRingCat RingCat)
      Y.ringCatSheaf.property⟩).obj (Scheme.unitModule Y)).obj L₂, ⊤))

include h₂ in
/-- **The global function cutting out the first branch**, when the first of the two invertible
modules of [Stacks, Tag 0F97] is the structure sheaf. It is the section `s₁` of `p^*𝒪_Y` read
through the identification `p^*𝒪_Y ≅ 𝒪_L` of
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`. -/
def unitBranchEquation :
    Γ(Scheme.unitModule (spaceIdeal Y (Scheme.unitModule Y) L₂ s).subscheme, ⊤) :=
  Scheme.Modules.Hom.app
    (Scheme.Modules.pullbackUnitIso (proj Y (Scheme.unitModule Y) L₂ s)).hom ⊤
    (section₁ Y (Scheme.unitModule Y) L₂ s)

include h₂ in
/-- **Clause (3) of [Stacks, Tag 0F99].** With `L₁ = 𝒪_Y`, the first branch `D₁` of [Stacks,
Tag 0F97] is the zero scheme of a global section of the structure sheaf of the ambient scheme
`L`, namely of `Stacks.Chow.TensorZeroScheme.unitBranchEquation`.

Condition (3) of [Stacks, Tag 0F97] presents `D₁` as the zero scheme of the section `s₁` of
`p^*L₁`; here `L₁ = 𝒪_Y` and the pullback of the structure sheaf is the structure sheaf, so
`AlgebraicGeometry.zeroScheme_eq_of_iso` — [Stacks, Tag 02OQ], the zero scheme depends only on
the isomorphism class of the pair — carries that presentation to one by a global function. -/
theorem branch₁_unit_eq_zeroScheme_unitModule :
    branch₁ Y (Scheme.unitModule Y) L₂ s =
      AlgebraicGeometry.zeroScheme (spaceIdeal Y (Scheme.unitModule Y) L₂ s).subscheme
        (Scheme.unitModule (spaceIdeal Y (Scheme.unitModule Y) L₂ s).subscheme)
        (unitBranchEquation Y L₂ s) :=
  AlgebraicGeometry.zeroScheme_eq_of_iso
    (Scheme.Modules.pullbackUnitIso (proj Y (Scheme.unitModule Y) L₂ s)) rfl

include h₂ in
/-- **Clause (3) of [Stacks, Tag 0F99], as the existence statement the source asserts.** With
`L₁ = 𝒪_Y`, the first branch `D₁` of [Stacks, Tag 0F97] is the zero scheme of a global section
of `𝒪_L`.

The witness is `Stacks.Chow.TensorZeroScheme.unitBranchEquation`, and the quantifier runs over
`Γ(L, ⊤)` — the sections of the structure sheaf as a sheaf of rings, which is the same type as
the sections of the structure sheaf as a module over itself. -/
theorem exists_globalSection_branch₁_unit :
    ∃ s' : Γ((spaceIdeal Y (Scheme.unitModule Y) L₂ s).subscheme, ⊤),
      branch₁ Y (Scheme.unitModule Y) L₂ s =
        AlgebraicGeometry.zeroScheme (spaceIdeal Y (Scheme.unitModule Y) L₂ s).subscheme
          (Scheme.unitModule (spaceIdeal Y (Scheme.unitModule Y) L₂ s).subscheme)
          (show Γ(Scheme.unitModule
            (spaceIdeal Y (Scheme.unitModule Y) L₂ s).subscheme, ⊤) from s') :=
  ⟨unitBranchEquation Y L₂ s, branch₁_unit_eq_zeroScheme_unitModule Y L₂ s⟩

end Stacks.Chow.TensorZeroScheme

end
