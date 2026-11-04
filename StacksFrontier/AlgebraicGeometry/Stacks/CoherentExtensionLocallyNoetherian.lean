module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentExtensionOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationExtensionOnSite

/-!
# Extensions of coherent modules on a locally Noetherian algebraic stack (Stacks 0GRA)

Let `𝒳` be a locally Noetherian algebraic stack and let

  `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0`

be a short exact sequence in `Mod(𝒪_𝒳)` with `ℱ₁` and `ℱ₃` coherent.  Stacks 0GRA says that
`ℱ₂` is coherent: coherence has the "2 out of 3" property in the middle.

## Main results

* `AlgebraicGeometry.Stack.isCoherent_X₂_of_kernel_cokernel`: **Stacks 0GRA**, with coherence the
  notion of Stacks 0GR6, `AlgebraicGeometry.Stack.IsCoherent`.  The exactness is given by a
  kernel fork on the left and a cokernel cofork on the right, which is the hypothesis-free
  rendering of a short exact sequence of `𝒪_𝒳`-modules.
* `AlgebraicGeometry.Stack.isCoherent_X₂_of_shortExact`: the same for a
  `CategoryTheory.ShortComplex.ShortExact`, which needs the ambient category balanced.

`AlgebraicGeometry.Stack.isCoherentModule_X₂_of_shortExact` is retained at the end of the file,
with its statement unchanged, for compatibility with the base.  It carries no Stacks attribute
and is not a main result: its comparison hypothesis `hfp` cannot hold, for the reason recorded in
the note on Stacks 03DL(8) below, so it asserts nothing about coherence.

## Implementation notes

**Which reading of "coherent" is used.**  Stacks 0GR6 calls an `𝒪_𝒳`-module coherent when it
satisfies the equivalent conditions of Stacks 0GR5, and the notion this library registers against
that tag is `AlgebraicGeometry.Stack.IsCoherent` of
`StacksFrontier.AlgebraicGeometry.Stacks.CoherentModules`, the conjunction of the two conditions of
Stacks 0GR5 it states.  That is the notion used here.  On a locally Noetherian algebraic stack it
agrees with condition (2) alone, finite presentation on the big fppf site, by
`AlgebraicGeometry.Stack.isCoherent_iff_isCoherentModule`, and **local Noetherianity of `𝒳` is
used through that equivalence**, in the direction that recovers condition (1) from condition (2).

The mathematical content is therefore that finite presentation of modules on a ringed site is
closed under extensions, which is
`Stacks.SheafOfModules.isFinitePresentationOnSite_X₂_of_kernel_cokernel` of
`StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationExtensionOnSite`.  Like the whole
family of statements around Stacks 03DL on this site it is proved sectionwise, so it needs no
sheafification instance and no hypothesis on the category of `𝒪_𝒳`-modules.

**The module universe.**  The sections of the modules are taken in the universe of the
coefficient rings, as they are in the structure-sheaf clause of Stacks 0GR7
(`AlgebraicGeometry.Stack.isCoherentModule_unit`).  This is the universe at which a finite global
presentation is read off sections: `SheafOfModules.hasFiniteGlobalPresentation_of_sections` and
its converse `Stacks.SheafOfModules.exists_sections_relations_of_hasFiniteGlobalPresentation`,
on which the proof rests, both live there.

**The two statements about Stacks 03DL(8).**  `AlgebraicGeometry.Stack.isCoherentOnSite_middle`
and `AlgebraicGeometry.Stack.isCoherentOnSite_X₂_of_shortExact` below are the same closure
property for `SheafOfModules.IsCoherentOnSite`, the *sectionwise* coherence condition of
Stacks 03DL(8) on the big fppf ringed site of `𝒳`.  They are true statements about that
condition, and the second is used by
`StacksFrontier.AlgebraicGeometry.Stacks.CoherentKernelCokernelLocallyNoetherian`, but they carry no
Stacks attribute: 03DL(8) on the big fppf site is not the notion of Stacks 0GR5 and 0GR6, that
site containing non-Noetherian test objects over which even `𝒪_𝒳` fails the condition.

**The exactness hypothesis, and why there are two forms.**  The kernel-fork and cokernel-cofork
form assumes nothing about the ambient category; the `ShortComplex.ShortExact` form needs it
balanced, which is what identifies the first term with the kernel of the second map, and holds as
soon as that category is abelian.  The category of modules on the fppf site of an algebraic stack
is not known to be abelian here — Mathlib's `Abelian (SheafOfModules R)` needs sheafification on
every slice and the module sections in the universe of the coefficient rings, and the fppf site of
a stack has neither, its objects lying one universe above its schemes — so `Balanced` is carried
as an instance hypothesis on the short exact form only, and the tag is registered on the form free
of it.  Local surjectivity of the second map is not assumed: a cokernel projection of sheaves of
modules is locally surjective, by
`Stacks.SheafOfModules.isLocallySurjective_of_isColimit`.

## References

* [Stacks Project, Tag 0GRA](https://stacks.math.columbia.edu/tag/0GRA)
* [Stacks Project, Tag 0GR5](https://stacks.math.columbia.edu/tag/0GR5)
* [Stacks Project, Tag 0GR6](https://stacks.math.columbia.edu/tag/0GR6)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 07UC](https://stacks.math.columbia.edu/tag/07UC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u m t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : AlgebraicStacks.{u, t} B S hS)

/-- **Stacks 01BY (4) on the big fppf site of an algebraic stack.**  Let `φ : ℱ₁ ⟶ ℱ₂` be a
kernel of `ψ : ℱ₂ ⟶ ℱ₃` and let `ℱ₃` be a cokernel of `φ` along `ψ`.  If `ℱ₁` and `ℱ₃` satisfy
the sectionwise coherence condition of Stacks 03DL(8) then so does `ℱ₂`.

Local surjectivity of `ψ` comes from its being a cokernel projection, so no hypothesis beyond
the exactness is needed, and in particular nothing is assumed about the category of
`𝒪_𝒳`-modules.  This carries no Stacks attribute, and is not Stacks 0GRA: the condition of
Stacks 03DL(8) on the big fppf site is not the coherence of Stacks 0GR5 and 0GR6; see the module
documentation and `AlgebraicGeometry.Stack.isCoherent_X₂_of_kernel_cokernel`.  Local
Noetherianity is the hypothesis of the source and is not used by this statement. -/
public theorem isCoherentOnSite_X₂_of_kernel_cokernel
    (_h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F₁ F₂ F₃ : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)}
    {φ : F₁ ⟶ F₂} {ψ : F₂ ⟶ F₃} (hz : φ ≫ ψ = 0)
    (hφ : IsLimit (KernelFork.ofι φ hz)) (hψ : IsColimit (CokernelCofork.ofπ ψ hz))
    (h₁ : SheafOfModules.IsCoherentOnSite F₁)
    (h₃ : SheafOfModules.IsCoherentOnSite F₃) :
    SheafOfModules.IsCoherentOnSite F₂ :=
  _root_.Stacks.SheafOfModules.isCoherentOnSite_middle hz hφ
    (_root_.Stacks.SheafOfModules.isLocallySurjective_of_isColimit hz hψ) h₁ h₃

/-- **Stacks 01BY (4) on the big fppf site of an algebraic stack, for a short exact sequence.**
The middle term of a short exact sequence of `𝒪_𝒳`-modules whose outer terms satisfy the
sectionwise coherence condition of Stacks 03DL(8) satisfies it too.

The category of `𝒪_𝒳`-modules is assumed balanced, which is what makes `ℱ₁` a kernel of
`ℱ₂ ⟶ ℱ₃` and `ℱ₃` a cokernel of `ℱ₁ ⟶ ℱ₂`; the hypothesis-free form is
`AlgebraicGeometry.Stack.isCoherentOnSite_X₂_of_kernel_cokernel`.  This carries no Stacks
attribute, for the reason recorded there.  Local Noetherianity is the hypothesis of the source
and is not used by this statement. -/
public theorem isCoherentOnSite_X₂_of_shortExact
    (_h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    [Balanced (SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))]
    {T : ShortComplex (SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))}
    (hT : T.ShortExact) (h₁ : SheafOfModules.IsCoherentOnSite T.X₁)
    (h₃ : SheafOfModules.IsCoherentOnSite T.X₃) :
    SheafOfModules.IsCoherentOnSite T.X₂ :=
  isCoherentOnSite_X₂_of_kernel_cokernel B S hS 𝒳 _h𝒳 T.zero hT.fIsKernel hT.gIsCokernel h₁ h₃

/-- **Stacks 0GRA.**  Let `𝒳` be a locally Noetherian algebraic stack, let `φ : ℱ₁ ⟶ ℱ₂` be a
kernel of `ψ : ℱ₂ ⟶ ℱ₃` and let `ℱ₃` be a cokernel of `φ` along `ψ`.  If `ℱ₁` and `ℱ₃` are
coherent then so is `ℱ₂`.

Coherence is `AlgebraicGeometry.Stack.IsCoherent`, the notion of Stacks 0GR6.  On a locally
Noetherian algebraic stack it is finite presentation on the big fppf site, condition (2) of
Stacks 0GR5, by `AlgebraicGeometry.Stack.isCoherent_iff_isCoherentModule`, which is where local
Noetherianity of `𝒳` enters; the content is then that finite presentation on a ringed site is
closed under extensions.  The exactness is given as a kernel fork and a cokernel cofork, so
nothing is assumed about the category of `𝒪_𝒳`-modules. -/
@[stacks 0GRA "extensions of coherent modules, exactness as a kernel fork and a cokernel cofork"]
public theorem isCoherent_X₂_of_kernel_cokernel
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F₁ F₂ F₃ : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)}
    {φ : F₁ ⟶ F₂} {ψ : F₂ ⟶ F₃} (hz : φ ≫ ψ = 0)
    (hφ : IsLimit (KernelFork.ofι φ hz)) (hψ : IsColimit (CokernelCofork.ofπ ψ hz))
    (h₁ : IsCoherent B S hS 𝒳 F₁) (h₃ : IsCoherent B S hS 𝒳 F₃) :
    IsCoherent B S hS 𝒳 F₂ :=
  (isCoherent_iff_isCoherentModule B S hS 𝒳 h𝒳 F₂).mpr
    (_root_.Stacks.SheafOfModules.isFinitePresentationOnSite_X₂_of_kernel_cokernel hz hφ hψ
      ((isCoherent_iff_isCoherentModule B S hS 𝒳 h𝒳 F₁).mp h₁)
      ((isCoherent_iff_isCoherentModule B S hS 𝒳 h𝒳 F₃).mp h₃))

/-- **Stacks 0GRA for a short exact sequence.**  Let `𝒳` be a locally Noetherian algebraic stack.
The middle term of a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of `𝒪_𝒳`-modules whose outer
terms are coherent is coherent.

The category of `𝒪_𝒳`-modules is assumed balanced, which is what makes `ℱ₁` a kernel of
`ℱ₂ ⟶ ℱ₃` and `ℱ₃` a cokernel of `ℱ₁ ⟶ ℱ₂`; this is an extra hypothesis on the ambient category
and not one of the source, so the tag is registered on the form free of it,
`AlgebraicGeometry.Stack.isCoherent_X₂_of_kernel_cokernel`. -/
public theorem isCoherent_X₂_of_shortExact
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    [Balanced (SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))]
    {T : ShortComplex (SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))}
    (hT : T.ShortExact) (h₁ : IsCoherent B S hS 𝒳 T.X₁) (h₃ : IsCoherent B S hS 𝒳 T.X₃) :
    IsCoherent B S hS 𝒳 T.X₂ :=
  isCoherent_X₂_of_kernel_cokernel B S hS 𝒳 h𝒳 T.zero hT.fIsKernel hT.gIsCokernel h₁ h₃

/-- **Stacks 0GRA with coherence read as Stacks 0GR5(2).**  Let `𝒳` be a locally Noetherian
algebraic stack on which `AlgebraicGeometry.Stack.IsCoherentModule`, finite presentation on the
big fppf site, agrees with the sectionwise coherence condition of Stacks 03DL(8).  Then the
middle term of a short exact sequence of `𝒪_𝒳`-modules whose outer terms are coherent in the
sense of `IsCoherentModule` is coherent in that sense.

The two implications comparing the readings are hypotheses, named `hfp` and `hcoh`; they hold on
a locally Noetherian algebraic stack but are not proved in this library, which lacks the part of
Stacks 0GR5 that identifies the conditions of Stacks 0GR6.  The content beyond them is
Stacks 01BY (4), through
`AlgebraicGeometry.Stack.isCoherentOnSite_X₂_of_shortExact`.  Local Noetherianity is the
hypothesis of the source and is not used.

This declaration is retained, with its statement unchanged, for compatibility with the base, and
it carries **no** Stacks attribute.  Its hypothesis `hfp` cannot hold: the big fppf site contains
non-Noetherian test objects over which even `𝒪_𝒳` fails the condition of Stacks 03DL(8), so the
statement is vacuous and asserts nothing about coherence.  The carrier of Stacks 0GRA in this
library is `AlgebraicGeometry.Stack.isCoherent_X₂_of_kernel_cokernel` above, which uses the
notion of Stacks 0GR6 and carries no comparison hypothesis. -/
public theorem isCoherentModule_X₂_of_shortExact
    (_h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    [Balanced (SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))]
    (hfp : ∀ M : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl),
      IsCoherentModule B S hS 𝒳 M → SheafOfModules.IsCoherentOnSite M)
    (hcoh : ∀ M : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl),
      SheafOfModules.IsCoherentOnSite M → IsCoherentModule B S hS 𝒳 M)
    {T : ShortComplex (SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))}
    (hT : T.ShortExact) (h₁ : IsCoherentModule B S hS 𝒳 T.X₁)
    (h₃ : IsCoherentModule B S hS 𝒳 T.X₃) :
    IsCoherentModule B S hS 𝒳 T.X₂ :=
  hcoh T.X₂ (isCoherentOnSite_X₂_of_shortExact B S hS 𝒳 _h𝒳 hT (hfp T.X₁ h₁) (hfp T.X₃ h₃))

end AlgebraicGeometry.Stack

end
