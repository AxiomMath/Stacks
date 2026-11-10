module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtaleAlgebra
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat base change for the direct image of a structure sheaf

Let
```
W' --g'--> W
|f'        |f
X' --g-->  X
```
be a cartesian square of schemes with `g` flat and `f` quasi-compact and quasi-separated.  This
file proves that the canonical base-change morphism is an isomorphism at the structure sheaf of
`W`, so that `g^* f_* 𝒪_W ≅ f'_* 𝒪_{W'}`, and restates that isomorphism for the `𝒪_X`-module
underlying the algebra `f_* 𝒪_W`.

This is the module-level content of the base-change clause of [Stacks, Tag 0EY6]: that clause
asks for the *algebra* `f'_* 𝒪_{W'}` to be the extension of scalars
`g⁻¹(f_* 𝒪_W) ⊗_{g⁻¹𝒪_X} 𝒪_{X'}`, and what is proved here is the corresponding statement about
the underlying modules.

## What this leaves

`Stacks.FundamentalGroup.isPushout_pushforwardBaseChangeMap_iff_isIso` reduces the whole of the
base-change clause of Tag 0EY6 — and, through
`Stacks.FundamentalGroup.isQuasicoherent_algebraPullback_of_flatBaseChange`, the
`algebraPullback_isQuasicoherent` clause of [Stacks, Tag 01SA] on which four of the six
declarations formalizing that tag depend for their *statements* — to invertibility of
`Stacks.AffineAlgebraEquivalence.baseChangeAlgebraHom`.

`underlyingModuleFlatBaseChangeIso` below discharges the part of that invertibility which needs
flatness, quasi-compactness and quasi-separatedness, i.e. everything that is a theorem about
schemes:  the `𝒪_{X'}`-module `g^*(f_* 𝒪_W)` *is* the `𝒪_{X'}`-module underlying
`f'_* 𝒪_{W ×_X X'}`, by the canonical comparison.  Three inputs remain, and none of them
mentions a scheme morphism's flatness or finiteness — they are identifications of functors on
sheaves of modules over a site, and they hold for every morphism:

1. invertibility of `Stacks.SheafOfModules.AlgebraPushout.extendScalarsComparison`, the
   identification of the module underlying a pushout of algebra sheaves with an extension of
   scalars (stated and reduced, but not proved, in
   `StacksFrontier/AlgebraicGeometry/FlatBaseChangeCohomology/AffineDegreeZero/AlgebraPushout.lean`
   of `StacksDraft/AlgebraicGeometry/F3/FlatBaseChangeCohomology/AffineDegreeZero/`);
2. the identification of the module underlying the inverse image `g⁻¹A` of an algebra sheaf with
   the inverse image of the module underlying `A`, together with the factorization of
   `Scheme.Modules.pullback g` as that inverse image followed by extension of scalars along
   `Stacks.AffineAlgebraEquivalence.inverseImageStructureMap g` (recorded as the remaining input
   of `Stacks.SheafOfModules.AlgebraPushout.algebraPullbackComparison`);
3. the agreement of the two canonical comparisons:  that the morphism of underlying modules
   induced by `baseChangeAlgebraHom g W` is, across (1) and (2), the base-change morphism
   `Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` whose invertibility is proved
   below.  With that, invertibility of `baseChangeAlgebraHom g W` follows by reflecting
   isomorphisms:  the morphism of underlying modules has, on sections, literally the map on
   sections of `Under.Hom.right`, so `Under.forget` and
   `CategoryTheory.isIso_of_reflects_iso` carry it back to the algebra.

## Main results

* `Stacks.FundamentalGroup.isIso_baseChangeNatTrans_unit` — the canonical base-change morphism of
  a cartesian square with flat base and quasi-compact quasi-separated top is an isomorphism at
  the structure sheaf.
* `Stacks.FundamentalGroup.flatBaseChangeUnitIso` — the resulting isomorphism
  `g^* f_* 𝒪_W ≅ f'_* 𝒪_{W'}`, together with `flatBaseChangeUnitIso_hom`, which identifies its
  underlying morphism.
* `Stacks.FundamentalGroup.underlyingModuleFlatBaseChangeIso` — the same isomorphism for the
  module underlying the direct image algebra of a quasi-compact quasi-separated scheme over `X`,
  base-changed along a flat `g`, in the spelling the base-change clause of Tag 0EY6 uses.

## Implementation notes

The content is `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat`
— part (1) of [Stacks, Tag 02KH] at `i = 0` for sheaves of modules — instantiated at the unit
module, whose quasi-coherence is an instance, together with
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`, which says that the inverse image of a
structure sheaf is a structure sheaf.  Both are in the library; neither mentions the other, and the
composite below is the identification the base-change clause of Tag 0EY6 consumes.

`underlyingModuleFlatBaseChangeIso` needs no glue beyond `flatBaseChangeUnitIso`:
`Stacks.FundamentalGroup.underlyingModule_pushforwardAlgebra_eq` holds by `rfl`, the structure
morphism of `(Over.pullback g).obj W` is `CategoryTheory.Limits.pullback.snd W.hom g` by `rfl`,
and the Cartesian square is `CategoryTheory.IsPullback.of_hasPullback`.  So the statement about
the algebra's underlying module is literally the statement about the structure sheaf, and the
two `_hom` lemmas record that the isomorphisms are the canonical comparisons rather than
unspecified isomorphisms — without which these would be strictly weaker than Tag 02KH asserts.

**No `@[stacks]` attribute is placed in this file.** Tag 02KH is formalized by two statements
whose remaining parts are unproved, and the base-change clause of Tag 0EY6 is not proved here, only
reduced further; a tag on a fraction of a covering set makes the whole tag render as formalized.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open Stacks.AlgebraicGeometry Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

universe u

namespace Stacks.FundamentalGroup

section Square

variable {W W' X X' : Scheme.{u}} {f : W ⟶ X} {f' : W' ⟶ X'} {g : X' ⟶ X} {g' : W' ⟶ W}

/-- **Flat base change for the direct image of a structure sheaf.**  For a cartesian square
whose base change `g` is flat and whose top morphism `f` is quasi-compact and quasi-separated,
the canonical base-change morphism `g^* f_* ⟶ f'_* (g')^*` is an isomorphism at the structure
sheaf of `W`.  This is part (1) of [Stacks, Tag 02KH] at `i = 0`, applied to `𝒪_W`. -/
theorem isIso_baseChangeNatTrans_unit (H : IsPullback g' f' f g)
    [Flat g] [QuasiCompact f] [QuasiSeparated f] :
    IsIso ((AffinePushforward.baseChangeNatTrans H.w).app
      (SheafOfModules.unit W.ringCatSheaf)) :=
  FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat H
    (SheafOfModules.unit W.ringCatSheaf)

/-- **`g^* f_* 𝒪_W ≅ f'_* 𝒪_{W'}`.**  The isomorphism of `𝒪_{X'}`-modules obtained from
`isIso_baseChangeNatTrans_unit` by identifying the inverse image `(g')^* 𝒪_W` of the structure
sheaf with the structure sheaf `𝒪_{W'}`. -/
def flatBaseChangeUnitIso (H : IsPullback g' f' f g)
    [Flat g] [QuasiCompact f] [QuasiSeparated f] :
    (Scheme.Modules.pullback g).obj
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit W.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward f').obj (SheafOfModules.unit W'.ringCatSheaf) :=
  haveI := isIso_baseChangeNatTrans_unit H
  asIso ((AffinePushforward.baseChangeNatTrans H.w).app (SheafOfModules.unit W.ringCatSheaf)) ≪≫
    (Scheme.Modules.pushforward f').mapIso (Scheme.Modules.pullbackUnitIso g')

/-- The isomorphism of `flatBaseChangeUnitIso` is the canonical base-change morphism, followed by
the direct image of the identification of `(g')^* 𝒪_W` with `𝒪_{W'}`.  Without this the
construction above would assert only that the two modules are isomorphic, which is strictly
weaker than [Stacks, Tag 02KH]. -/
theorem flatBaseChangeUnitIso_hom (H : IsPullback g' f' f g)
    [Flat g] [QuasiCompact f] [QuasiSeparated f] :
    (flatBaseChangeUnitIso H).hom =
      (AffinePushforward.baseChangeNatTrans H.w).app (SheafOfModules.unit W.ringCatSheaf) ≫
        (Scheme.Modules.pushforward f').map (Scheme.Modules.pullbackUnitIso g').hom :=
  rfl

end Square

section Over

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (W : Over X)

/-- **The module-level base-change clause of [Stacks, Tag 0EY6].**  Let `W` be a quasi-compact
quasi-separated scheme over `X` and let `g : X' ⟶ X` be flat.  The inverse image along `g` of
the `𝒪_X`-module underlying the algebra `f_* 𝒪_W` is the `𝒪_{X'}`-module underlying the algebra
of the base-changed scheme `W ×_X X'` over `X'`.

The base-change clause of Tag 0EY6 asks for the corresponding statement one level up, about the
algebras rather than their underlying modules:  that `f'_* 𝒪_{W ×_X X'}` is the extension of
scalars `g⁻¹(f_* 𝒪_W) ⊗_{g⁻¹𝒪_X} 𝒪_{X'}`.  What separates the two is no longer geometric; see
the module docstring. -/
@[sga "7 VII 1.3.8"]
def underlyingModuleFlatBaseChangeIso [Flat g] [QuasiCompact W.hom] [QuasiSeparated W.hom] :
    (Scheme.Modules.pullback g).obj
        (AlgebraSheaf.underlyingModule (pushforwardAlgebra W.hom)) ≅
      AlgebraSheaf.underlyingModule (pushforwardAlgebra ((Over.pullback g).obj W).hom) :=
  flatBaseChangeUnitIso (IsPullback.of_hasPullback W.hom g)

/-- The isomorphism of `underlyingModuleFlatBaseChangeIso` is the canonical base-change morphism
of the Cartesian square of the fibre product, followed by the direct image of the identification
of the inverse image of `𝒪_W` with `𝒪_{W ×_X X'}`. -/
theorem underlyingModuleFlatBaseChangeIso_hom
    [Flat g] [QuasiCompact W.hom] [QuasiSeparated W.hom] :
    (underlyingModuleFlatBaseChangeIso g W).hom =
      (AffinePushforward.baseChangeNatTrans
          (IsPullback.of_hasPullback W.hom g).w).app
          (SheafOfModules.unit W.left.ringCatSheaf) ≫
        (Scheme.Modules.pushforward (pullback.snd W.hom g)).map
          (Scheme.Modules.pullbackUnitIso (pullback.fst W.hom g)).hom :=
  rfl

end Over

end Stacks.FundamentalGroup

end
