module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.IdealSheafComparison
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheaf
public import StacksFrontier.AlgebraicGeometry.Thickenings.Existence
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormal
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal sheaf of a formally unramified morphism (Stacks 04F4, 04F6)

Let `h : Z ⟶ X` be a formally unramified morphism of schemes. By [Stacks Project, Tag 04F3] it
has a universal first-order thickening `Z ⊂ Z'` over `X`, chosen by
`Stacks.Thickenings.universalFirstOrderThickening`. Following [Stacks Project, Tag 04F4], the
**conormal sheaf `𝒞_{Z/X}` of `Z` over `X`** is the conormal sheaf of the inclusion `Z ⟶ Z'` in
the sense of [Stacks Project, Tag 01R2], the conormal sheaf of an *immersion*.

The conormal sheaf of an immersion `i : Z ⟶ X` is, by [Stacks Project, Tag 01R2] and the
description of [Stacks Project, Tag 01R3] part (1), the pullback along the closed-immersion
factorization of `i` of the defining ideal sheaf of that factorization. The open subscheme
through which `i` becomes a closed immersion is `X ∖ ∂Z` for `∂Z = closure(Z) ∖ Z`, which is
exactly `AlgebraicGeometry.Scheme.Hom.coborderRange`; the factorization is
`AlgebraicGeometry.Scheme.Hom.liftCoborder`.

The file also records [Stacks Project, Tag 04F6]: the ambient scheme of a universal first-order
thickening is formally unramified over the base.

## Main definitions

* `Stacks.Thickenings.immersionConormalSheaf` is the conormal sheaf `𝒞_{Z/X}` of an immersion of
  schemes, [Stacks Project, Tag 01R2].
* `Stacks.Thickenings.universalConormalSheaf` is the conormal sheaf `𝒞_{Z/X}` of a formally
  unramified morphism `h : Z ⟶ X`, [Stacks Project, Tag 04F4] part (2).

## Main results

* `Stacks.Thickenings.UniversalFirstOrderThickening.formallyUnramified_toBase`: the ambient
  scheme of *any* universal first-order thickening of a formally unramified `h : Z ⟶ X` is
  formally unramified over `X`. This is [Stacks Project, Tag 04F6].
* `Stacks.Thickenings.formallyUnramified_universalFirstOrderThickening_toBase` is the same
  statement at the chosen thickening, as an instance.

## Implementation notes

Part (1) of [Stacks Project, Tag 04F4] — that *the* universal first-order thickening of `Z` over
`X` is the one whose existence [Stacks Project, Tag 04F3] proves — is not a new declaration: it
is the choice already made by `Stacks.Thickenings.universalFirstOrderThickening`, so the tag is
attached to that definition by `add_to_stacks` rather than to a duplicate of it.

`Stacks.Thickenings.immersionConormalSheaf` is the conormal sheaf of an immersion only as a
*construction*. [Stacks Project, Tag 01R2] also asserts that it is quasi-coherent, and that
assertion is **not** proved here: deducing it from
`AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent` ([Stacks Project, Tag 01BG])
needs quasi-coherence of the defining ideal sheaf, hence the ringed-space closed-immersion
property `Stacks.ClosedImmersion.IsClosedImmersion i.liftCoborder.toLRSHom.toShHom`, and nothing
in the library yet derives that from the scheme-level `AlgebraicGeometry.IsClosedImmersion`. The
`01R2` attribute therefore carries the clause comment `construction`, and the quasi-coherence
clause of that tag is deliberately left unplaced.

For an immersion `i` the factorization `i.liftCoborder` is `i` itself up to the open immersion
`i.coborderRange.ι`, so `Stacks.Thickenings.immersionConormalSheaf i` and
`Stacks.Thickenings.schemeConormalSheaf i` describe the same sheaf. They are *not* the same
term, and no comparison between them is proved **in this file**, which does not import the file
that proves it. The comparison itself *is* in the library, for every immersion and not only for a
closed one: it is `Stacks.Immersion.conormalSheafSelfIso` of
`StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorization`, whose type is exactly
`Stacks.Thickenings.schemeConormalSheaf i ≅ Stacks.Thickenings.immersionConormalSheaf i`. It does
not go through the pullback functor `RingedSpaceModuleAdjunction.modulePullback` along an
isomorphism of ringed spaces: by `StacksFrontier.AlgebraicGeometry.Conormal.OpenFactorization` it
conjugates the structure-sheaf map of `i.liftCoborder ≫ i.coborderRange.ι` by the two
isomorphisms an *open* immersion supplies, after which the two kernels agree with no statement
about pullback preserving kernels needed.

`Stacks.Thickenings.universalConormalSheafMap`, the morphism of conormal sheaves of
[Stacks Project, Tag 04F7], is therefore stated in terms of
`Stacks.Thickenings.schemeConormalSheaf` only because it is defined before
`Stacks.Immersion.conormalSheafSelfIso` is available, not because the two cannot be connected;
composing with that isomorphism moves it to `Stacks.Thickenings.universalConormalSheaf`. Whether
anything else of that tag is still owed is not decided here.

[Stacks Project, Tag 04F6] is proved for an arbitrary universal first-order thickening rather
than only for the chosen one. The gluing construction of [Stacks Project, Tag 04F3] produces a
thickening whose structure morphism is formally unramified — formal unramifiedness is
Zariski-local at the source and the construction glues affine charts whose structure morphisms
are formally unramified — and that is recorded by
`Stacks.Thickenings.exists_universalFirstOrderThickening_formallyUnramified_toBase`. Any other
universal first-order thickening of the same morphism differs from it by the isomorphism
`Stacks.Thickenings.UniversalFirstOrderThickening.canonicalIso` over `X`, and formal
unramifiedness is invariant under composition with an isomorphism. This is the first proof
offered by the source, run once at the level of the construction instead of affine-locally
through `Ω_{Z'/X} = 0`.

## References

* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3)
* [Stacks Project, Tag 04F4](https://stacks.math.columbia.edu/tag/04F4)
* [Stacks Project, Tag 04F6](https://stacks.math.columbia.edu/tag/04F6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction

universe u

namespace Stacks.Thickenings

/-! ### The conormal sheaf of an immersion -/

/-- **Stacks Project, Tag 01R2.** The conormal sheaf `𝒞_{Z/X} = I/I²` of an immersion
`i : Z ⟶ X` of schemes: the pullback along the closed immersion
`AlgebraicGeometry.Scheme.Hom.liftCoborder` of `i` into the canonical open neighbourhood
`AlgebraicGeometry.Scheme.Hom.coborderRange` of its image of the defining ideal sheaf of that
closed immersion.

By [Stacks Project, Tag 01R3] part (1) this pullback *is* the conormal sheaf: its pushforward
along the closed immersion is `I/I²`. Only the construction is provided; the quasi-coherence
asserted by [Stacks Project, Tag 01R2] is not proved here.

This is the same construction as `Stacks.Conormal.conormalSheaf`, and is defined as that
declaration: `schemeConormalSheaf i.liftCoborder` unfolds, by two abbreviations, to its body. -/
@[stacks 01R2 "construction", sga "3 I 6.8.5", sga "3 III 4.5.0", sga "6 VII 1.6"]
noncomputable abbrev immersionConormalSheaf {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace) :=
  Stacks.Conormal.conormalSheaf i

/-! ### The conormal sheaf of a formally unramified morphism -/

add_to_stacks 04F4 "part (1): universal first-order thickening"
  Stacks.Thickenings.universalFirstOrderThickening

/-- **Stacks Project, Tag 04F4, part (2).** The conormal sheaf `𝒞_{Z/X}` of a formally
unramified morphism `h : Z ⟶ X`: the conormal sheaf, in the sense of
`Stacks.Thickenings.immersionConormalSheaf` ([Stacks Project, Tag 01R2]), of the inclusion of
`Z` into the universal first-order thickening of `Z` over `X` chosen by
`Stacks.Thickenings.universalFirstOrderThickening`.

The inclusion is a closed immersion, hence an immersion, by
`Stacks.Thickenings.UniversalFirstOrderThickening.isClosedImmersion_inclusion`. -/
@[stacks 04F4 "part (2): conormal sheaf"]
noncomputable abbrev universalConormalSheaf {Z X : Scheme.{u}} (h : Z ⟶ X)
    [FormallyUnramified h] :
    SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace) :=
  immersionConormalSheaf (universalFirstOrderThickening h).inclusion

/-! ### Formal unramifiedness of the universal first-order thickening -/

/-- **Stacks Project, Tag 04F6.** The ambient scheme of a universal first-order thickening of a
formally unramified morphism `h : Z ⟶ X` is formally unramified over `X`.

The thickening produced by the gluing construction of [Stacks Project, Tag 04F3] has this
property, by
`Stacks.Thickenings.exists_universalFirstOrderThickening_formallyUnramified_toBase`, and any
other universal first-order thickening of `h` is isomorphic to it over `X` by
`Stacks.Thickenings.UniversalFirstOrderThickening.canonicalIso`. -/
@[stacks 04F6]
theorem UniversalFirstOrderThickening.formallyUnramified_toBase {Z X : Scheme.{u}} {h : Z ⟶ X}
    [FormallyUnramified h] (t : UniversalFirstOrderThickening h) :
    FormallyUnramified t.toBase := by
  obtain ⟨t₀, h₀⟩ := exists_universalFirstOrderThickening_formallyUnramified_toBase h
  have : IsIso (UniversalFirstOrderThickening.canonicalMap t t₀) :=
    UniversalFirstOrderThickening.isIso_of_inclusion_of_toBase t t₀ _
      (UniversalFirstOrderThickening.canonicalMap_inclusion t t₀)
      (UniversalFirstOrderThickening.canonicalMap_toBase t t₀)
  rw [← UniversalFirstOrderThickening.canonicalMap_toBase t t₀]
  exact MorphismProperty.comp_mem (@FormallyUnramified)
    (UniversalFirstOrderThickening.canonicalMap t t₀) t₀.toBase inferInstance h₀

/-- The universal first-order thickening of `h : Z ⟶ X` chosen by
`Stacks.Thickenings.universalFirstOrderThickening` is formally unramified over `X`. This is
[Stacks Project, Tag 04F6] at the chosen thickening, which is the form the conormal-sheaf
results consume. -/
instance formallyUnramified_universalFirstOrderThickening_toBase {Z X : Scheme.{u}} (h : Z ⟶ X)
    [FormallyUnramified h] : FormallyUnramified (universalFirstOrderThickening h).toBase :=
  (universalFirstOrderThickening h).formallyUnramified_toBase

end Stacks.Thickenings

end
