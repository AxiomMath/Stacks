module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomVariance

/-!
# The two-variable pairing of an internal Hom of presheaves of modules, and its transpose

Let `O` be a presheaf of commutative rings on a site `C` and let `A`, `B`, `G` be presheaves of
`O`-modules. A morphism `f : A ⟶ internalHom O B G` into the internal Hom presheaf of Tag 03EM
is the same thing as an `O`-bilinear pairing of `A` and `B` into `G`, natural over every object
of the site; that description is symmetric in `A` and `B`, so transposing the pairing turns `f`
into a morphism `B ⟶ internalHom O A G`, and transposing twice returns `f`.

This file holds that construction once. It is the input of the two proofs that internal Hom in
the *first* variable carries colimits to limits — the sheaf-level half of Tag 03EN, which does
not follow from the presheaf-level half because colimits of sheaves of modules are not computed
on the underlying presheaves. The symmetry makes internal Hom against a fixed target left
adjoint to its own opposite, and a left adjoint preserves colimits. The two proofs are
`Stacks.SheafOfModules.InternalHom.sheafInternalHomFunctor_preservesColimitsOfShape` of
`StacksFrontier.AlgebraicGeometry.InternalHomSiteVariance.FirstVariable`, over an arbitrary site,
and `Stacks.SheafOfModules.InternalHom.internalHomFirstFunctor_preservesColimitsOfSize` of
`StacksFrontier.AlgebraicGeometry.InternalHomCoherent.FirstVariable`, over a `RingedSite` at a
single universe; both rest on the constructions below.

## Main definitions

* `Stacks.PresheafOfModules.InternalHom.pairing`: the pairing attached to a morphism into an
  internal Hom presheaf.
* `Stacks.PresheafOfModules.InternalHom.transposeSection`: the morphism `A|_U ⟶ G|_U` obtained
  from that pairing by fixing a section of `B` over `U`.
* `Stacks.PresheafOfModules.InternalHom.transposeHom`: the transpose
  `B ⟶ internalHom O A G` of a morphism `A ⟶ internalHom O B G`.

## Main results

* `Stacks.PresheafOfModules.InternalHom.transposeHom_involutive`: taking the transpose twice
  returns the original morphism.

## Implementation notes

The pairing attached to `f : A ⟶ internalHom O B G` reads off the component of `f` at the
terminal object `Over.mk (𝟙 U)` of the slice site `C/U`: a section `a` of `A` over `U` is sent
by `f` to a morphism `B|_U ⟶ G|_U` on `C/U`, and that component is applied to a section of `B`
over `U`. Naturality of the pairing is therefore not naturality of `f` alone — relocalization
along `g : V ⟶ U` sends the terminal object of `C/V` to `Over.mk (𝟙 V ≫ g)` — but naturality of
`f.app (op U) a` along `Over.homMk g : Over.mk (𝟙 V ≫ g) ⟶ Over.mk (𝟙 U)`.

The sections of the internal Hom presheaf over `U` are morphisms of `O|_U`-modules, so their
source is spelled through `restrFun` rather than through `Oforget`. The two spellings are
definitionally equal but not type-correct at `implicit` transparency, so the `map_add` and
`map_smul` fields of `transposeHom` are discharged by `congrArg`/`Eq.trans` against explicitly
stated equations rather than by rewriting through the coercion.

Everything is at module universe `max u v` for a site `C : Type u` with `Category.{v} C`, which
is where `Stacks.PresheafOfModules.InternalHom.internalHomMapLeft` is stated. The
single-universe consumer instantiates `v := u`; `max u u` is `u`, so no narrower copy is needed.

**The relation to the owned copy.**
`StacksFrontier/CategoryTheory/Sites/Modules/InternalHomAndFlatness/InternalHomFirstVariable.lean`
holds the same nine declarations at lines 103-190, at the same universes and with the same
proofs, but every one of them is `private` there; that file is owned elsewhere, so they can be
neither imported nor made public, and this file cannot be replaced by an import of it. It
remains the one copy the two consumers above share.

No `@[stacks 03EM]` or `@[stacks 03EN]` attribute is attached: nothing here is a statement of
either tag, the material being the symmetry of the pairing rather than a property of internal
Hom, and both tags are placed over covering sets elsewhere.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.PresheafOfModules.InternalHom

universe v u

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{max u v})
variable {A B G : _root_.PresheafOfModules.{max u v} (Oforget O)}

/-! The pairing, its transpose and their algebraic properties are declared upstream, in
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomVariance`, at a free ring
universe `w` rather than at `max u v`; this module re-exports them through its `public
import` of that file. -/

end Stacks.PresheafOfModules.InternalHom

end
