module

public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.NormalizationMono.GenericPoints

/-!
# The structure sheaf of a reduced scheme injects into its normalization

Let `X` be a reduced scheme whose quasi-compact opens have finitely many irreducible
components, and let `ν : X^ν ⟶ X` be its normalization.  This file proves that the induced
morphism of sheaves of rings `𝒪_X ⟶ ν_* 𝒪_{X^ν}` is a monomorphism, which is the inclusion
`𝒪_X ⊂ ν_*𝒪_{X^ν}` of [Stacks, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)(2).

The argument is a factorization, not a local computation.  Writing `f` for the canonical
morphism from the spectra of the residue fields at the generic points of `X`, Mathlib's
relative normalization factors `f = f.toNormalization ≫ f.fromNormalization` with
`ν = f.fromNormalization`.  Since `f` is dominant — its range is the set of generic points of
`X`, which is dense — so is `ν`, and a dominant morphism with reduced target has trivial
kernel: a section of `𝒪_X` killed by `ν` vanishes on the dense image of `ν`, hence is
nilpotent, hence zero.  That is Mathlib's `IsSchemeTheoreticallyDominant.of_isDominant`, whose
companion `Scheme.Hom.app_injective` upgrades the triviality of the kernel from affine opens to
all opens.  Injectivity on every open is then turned into a monomorphism of sheaves of rings:
the inclusion of sheaves into presheaves is faithful, so it reflects monomorphisms, a
monomorphism of presheaves follows from monomorphisms of all its components, and in `RingCat` a
monomorphism follows from injectivity.

## Main results

* `mono_toRingCatSheafHom_of_app_injective`: a morphism of schemes injective on sections over
  every open induces a monomorphism `𝒪_Y ⟶ f_* 𝒪_X` of sheaves of rings.
* `mono_toRingCatSheafHom_fromNormalization`: for a dominant qcqs morphism `f` with reduced
  target, `𝒪_Y ⟶ (f.fromNormalization)_* 𝒪_{f.normalization}` is a monomorphism.
* `mono_toRingCatSheafHom_normalization` and
  `mono_toRingCatSheafHom_normalization_of_isNagataScheme` are Tag 0C1R(2): the structure sheaf
  of a reduced scheme injects into the pushforward of the structure sheaf of its normalization.

## Implementation notes

The dimension-one hypothesis of the source is not used: reducedness alone gives the inclusion
`𝒪_X ⊂ ν_*𝒪_{X^ν}`, and the general lemma `mono_toRingCatSheafHom_fromNormalization` drops the
Nagata hypothesis too — monomorphicity holds for any quasi-compact, quasi-separated dominant
morphism with reduced target. The Nagata hypothesis is used only to form the normalization at
all, by way of `finite_irreducibleComponents_of_isNagataScheme`, which supplies the
finitely-many-irreducible-components input of the relative-normalization construction; the
statement taking the finiteness hypothesis directly is the more general one.

Mathlib's `Scheme.Hom.toRingCatSheafHom` is the morphism of sheaves of *rings* (not of
commutative rings) attached to a morphism of schemes, because presheaves of modules are
defined over presheaves of rings.  Monomorphy there is what the quotient
`ν_*𝒪_{X^ν}/𝒪_X` of the source is formed from.

No stacks attribute for Tag 0C1R is carried here. The tag labels three assertions: this
injectivity, the identification of the normalization quotient with a direct sum of skyscrapers,
and the characterization of its nonvanishing by the singular locus. Only the first is proved
here; the other two need the dimension-one hypothesis, the density of the regular locus
(Tag 07PJ) and the singular-locus vocabulary.

## References

* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
* [Stacks Project, Tag 035M](https://stacks.math.columbia.edu/tag/035M) — the morphism from the
  spectra of the residue fields at the generic points, constructed as
  `fromGenericPointResidueFields`.
* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N) — the normalization of a
  scheme, constructed as `normalization`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Normalization

/-- A morphism of schemes that is injective on sections over every open induces a monomorphism
`𝒪_Y ⟶ g_* 𝒪_X` of sheaves of rings.

The inclusion of sheaves into presheaves is faithful, hence reflects monomorphisms; a
natural transformation with monomorphic components is a monomorphism; and a monomorphism in
`RingCat` follows from injectivity. -/
public theorem mono_toRingCatSheafHom_of_app_injective {X Y : Scheme.{u}} (g : X ⟶ Y)
    (hg : ∀ U : Y.Opens, Function.Injective (g.app U)) :
    Mono (Scheme.Hom.toRingCatSheafHom g) := by
  apply (TopCat.Sheaf.forget RingCat.{u} Y).mono_of_mono_map
  have : ∀ U : Y.Opensᵒᵖ,
      Mono (((TopCat.Sheaf.forget RingCat.{u} Y).map
        (Scheme.Hom.toRingCatSheafHom g)).app U) := fun U ↦
    ConcreteCategory.mono_of_injective _ (hg U.unop)
  exact NatTrans.mono_of_mono_app _

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- The morphism from the relative normalization is dominant when `f` is, because `f` factors
through it. -/
public theorem isDominant_fromNormalization [IsDominant f] :
    IsDominant f.fromNormalization := by
  have : IsDominant (f.toNormalization ≫ f.fromNormalization) := by
    rw [Scheme.Hom.toNormalization_fromNormalization]
    infer_instance
  exact IsDominant.of_comp f.toNormalization f.fromNormalization

/-- The morphism from the relative normalization of a dominant morphism with reduced target is
injective on sections over every open. -/
public theorem injective_fromNormalization_app [IsReduced Y] [IsDominant f] (U : Y.Opens) :
    Function.Injective (f.fromNormalization.app U) := by
  have : IsDominant f.fromNormalization := isDominant_fromNormalization f
  have : IsSchemeTheoreticallyDominant f.fromNormalization :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  exact Scheme.Hom.app_injective _ U

/-- For a dominant qcqs morphism `f` with reduced target `Y`, the structure sheaf of `Y`
injects into the pushforward of the structure sheaf of the relative normalization. -/
public theorem mono_toRingCatSheafHom_fromNormalization [IsReduced Y] [IsDominant f] :
    Mono (Scheme.Hom.toRingCatSheafHom f.fromNormalization) :=
  mono_toRingCatSheafHom_of_app_injective _ (injective_fromNormalization_app f)

/-- **Stacks Project, Tag 0C1R(2).** The structure sheaf of a reduced scheme injects into the
pushforward of the structure sheaf of its normalization: the morphism of sheaves of rings
`𝒪_X ⟶ ν_* 𝒪_{X^ν}` is a monomorphism.

Only reducedness of `X` is used; the finiteness hypothesis on irreducible components serves
only to form the normalization. -/
public theorem mono_toRingCatSheafHom_normalization (X : Scheme.{u}) [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    Mono (Scheme.Hom.toRingCatSheafHom (normalization X hX)) := by
  let _ := quasiCompact_fromGenericPointResidueFields X hX
  exact mono_toRingCatSheafHom_fromNormalization (fromGenericPointResidueFields X)

/-- **Stacks Project, Tag 0C1R(2)** for a reduced Nagata scheme: the structure sheaf injects
into the pushforward of the structure sheaf of the normalization.

The source states this for a reduced Nagata scheme *of dimension one*; the dimension hypothesis
is not needed for this part of the statement. -/
public theorem mono_toRingCatSheafHom_normalization_of_isNagataScheme (X : Scheme.{u})
    [IsReduced X] (hX : IsNagataScheme X) :
    Mono (Scheme.Hom.toRingCatSheafHom
      (normalization X (finite_irreducibleComponents_of_isNagataScheme X hX))) :=
  mono_toRingCatSheafHom_normalization X _

end Stacks.AlgebraicGeometry.Normalization
