module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.HilbertCoverPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.SiteMembership

/-!
# The universal family of degree-`d` covers, and the 1-morphism it defines into `ℋ_d`

Let `B` be a big fppf site, `S` a scheme contained in it and `d` a positive natural number. The
scheme `X` of free `d`-dimensional algebra structures of **Stacks 05YM** carries the universal
structure `AlgebraicGeometry.FiniteFreeAlgebra.universalStructure`, and the spectrum of the
algebra of that structure is a degree-`d` finite locally free cover of `X` by
`AlgebraicGeometry.FiniteFreeAlgebra.isFiniteLocallyFreeOfRank_specCover`.

Base changing both to `S` gives an object of the big fppf site of `S` carrying a degree-`d`
finite locally free cover, and therefore — by
`AlgebraicGeometry.Stack.finiteCoverPointHom` — a 1-morphism from the category represented by
that object into the category `ℋ_d` of degree-`d` finite locally free covers. This is the atlas
candidate of the presentation clause of **Stacks 026O** for `ℋ_d`, which is how the source proves
**Stacks 05YQ**: `ℋ_d` is the quotient of `X` by change of basis, and `X ⟶ ℋ_d` is its
presentation.

## Main definitions

* `AlgebraicGeometry.Stack.structureConstantsOver`: the scheme of structure constants base
  changed to `S`, as an object of the big fppf site of `S`.
* `AlgebraicGeometry.Stack.universalFiniteCoverOver` and
  `AlgebraicGeometry.Stack.universalFiniteCoverMapOver`: the universal degree-`d` cover base
  changed to `S`, and its structure morphism, in the big fppf site of `S`.
* `AlgebraicGeometry.Stack.finiteCoverUniversalAtlas`: the resulting 1-morphism into `ℋ_d`.

## Main results

* `AlgebraicGeometry.Stack.isFiniteLocallyFreeOfRank_universalFiniteCoverMapOver`: the base
  changed universal cover is still finite locally free of degree `d`, by **Stacks 02KA**.

## Implementation notes

Both base changes are taken over the terminal scheme `Spec ℤ`, exactly as
`AlgebraicGeometry.generalLinearBaseChange` does for the general linear group scheme: the scheme
of structure constants is defined over the integers, so its base change to `S` is the fibre
product with `S` over the terminal object, and site membership of both fibre products is
`AlgebraicGeometry.Scheme.size_pullback_lt`.

The base of the universal cover is `Spec Γ(X, 𝒪_X)` rather than `X` itself. This is not a choice:
`AlgebraicGeometry.FiniteFreeAlgebra.specCover` builds the cover of a structure over a ring as a
scheme over the spectrum of that ring, and the universal structure's ring of definition is the
global sections of `X`. The two schemes are canonically isomorphic, `X` being affine, and nothing
below depends on which of them is used.

Positivity of `d` enters as the `NeZero d` instance that
`AlgebraicGeometry.FiniteFreeAlgebra` carries: a free module of rank `0` has no multiplicative
unit, so there is no structure to parametrise, and the source's presentation of `ℋ_d` is likewise
stated for `d ≥ 1`.

The presentation clause of Stacks 026O asks three things of the 1-morphism beyond its existence:
representability by algebraic spaces, surjectivity and smoothness. Representability is
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_finiteCoverUniversalAtlas`, which reads
it off the diagonal of `ℋ_d` through Stacks 045G and so holds of every scheme-valued point of
`ℋ_d`. Surjectivity rests on
`AlgebraicGeometry.FiniteFreeAlgebra.exists_point_isPullback_universalFiniteCoverMap_of_field`,
which exhibits every degree-`d` cover of the spectrum of a field as a base change of the
universal cover.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Stack

open AlgebraicGeometry.FiniteFreeAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (d : ℕ) [NeZero d]

/-! ### The universal family over the integers -/

/-- The spectrum of the ring of global sections of the scheme of free `d`-dimensional algebra
structures. This is the base over which
`AlgebraicGeometry.FiniteFreeAlgebra.universalStructure` has its cover, and it is canonically
isomorphic to `AlgebraicGeometry.FiniteFreeAlgebra.scheme` itself. -/
noncomputable abbrev structureConstantsSpec : Scheme.{u} :=
  Spec (.of Γ(FiniteFreeAlgebra.scheme.{u} d, ⊤))

/-- The spectrum of the ring of global sections of the scheme of structure constants lies in
every big fppf site: it has the same ring of global sections as that scheme, which lies in every
big fppf site by `AlgebraicGeometry.FiniteFreeAlgebra.contains_scheme`. -/
theorem contains_structureConstantsSpec : B.Contains (structureConstantsSpec.{u} d) :=
  Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (AlgebraicGeometry.Space.contains_specULiftZ B)
    (le_trans (le_of_eq (Cardinal.mk_congr
        (Scheme.ΓSpecIso
          (.of (ULift.{u} (universalRing d)))).commRingCatIsoToRingEquiv.toEquiv))
      (le_trans (by
          rw [Cardinal.mk_uLift]
          exact Cardinal.lift_le_aleph0.2
            ((Cardinal.mk_le_of_algebra_finiteType ℤ (universalRing d)).trans (by simp)))
        (le_max_left _ _)))

/-- The universal degree-`d` cover over the integers: the spectrum of the algebra of the
universal structure, with its structure morphism to
`AlgebraicGeometry.Stack.structureConstantsSpec`. -/
noncomputable abbrev universalFiniteCoverMap :
    (specCover (universalStructure.{u} d)).left ⟶ structureConstantsSpec.{u} d :=
  (specCover (universalStructure.{u} d)).hom

/-! ### Base change to `S` -/

/-- The projection of the base change to `S` of the scheme of structure constants onto the
scheme of structure constants. -/
noncomputable abbrev structureConstantsBaseChangeFst :
    pullback (specULiftZIsTerminal.from (structureConstantsSpec.{u} d))
      (specULiftZIsTerminal.from S) ⟶ structureConstantsSpec.{u} d :=
  pullback.fst _ _

/-- The structure morphism to `S` of the base change to `S` of the scheme of structure
constants. -/
noncomputable abbrev structureConstantsBaseChangeSnd :
    pullback (specULiftZIsTerminal.from (structureConstantsSpec.{u} d))
      (specULiftZIsTerminal.from S) ⟶ S :=
  pullback.snd _ _

/-- The structure morphism of the base change to `S` of the universal degree-`d` cover. -/
noncomputable abbrev universalFiniteCoverBaseChangeSnd :
    pullback (universalFiniteCoverMap.{u} d) (structureConstantsBaseChangeFst.{u} S d) ⟶
      pullback (specULiftZIsTerminal.from (structureConstantsSpec.{u} d))
        (specULiftZIsTerminal.from S) :=
  pullback.snd _ _

include hS in
/-- The base change to `S` of the scheme of structure constants lies in the big fppf site. -/
theorem contains_structureConstantsBaseChange :
    B.Contains (pullback (specULiftZIsTerminal.from (structureConstantsSpec.{u} d))
      (specULiftZIsTerminal.from S)) :=
  Scheme.size_pullback_lt _ _ (contains_structureConstantsSpec B d) hS

include hS in
/-- The base change to `S` of the universal degree-`d` cover lies in the big fppf site. -/
theorem contains_universalFiniteCoverBaseChange :
    B.Contains (pullback (universalFiniteCoverMap.{u} d)
      (structureConstantsBaseChangeFst.{u} S d)) :=
  Scheme.size_pullback_lt _ _
    (FiniteFreeAlgebra.contains_specCover_universalStructure B)
    (contains_structureConstantsBaseChange B S hS d)

/-- **The scheme of structure constants over `S`**, as an object of the big fppf site of `S`. -/
noncomputable abbrev structureConstantsOver : BigFppfOver B S hS :=
  siteObject B S hS (contains_structureConstantsBaseChange B S hS d)
    (structureConstantsBaseChangeSnd.{u} S d)

/-- **The universal degree-`d` cover over `S`**, as an object of the big fppf site of `S`. -/
noncomputable abbrev universalFiniteCoverOver : BigFppfOver B S hS :=
  siteObject B S hS (contains_universalFiniteCoverBaseChange B S hS d)
    (universalFiniteCoverBaseChangeSnd.{u} S d ≫ structureConstantsBaseChangeSnd.{u} S d)

/-- The structure morphism of the universal degree-`d` cover over `S`, as a morphism of the big
fppf site of `S`. -/
noncomputable abbrev universalFiniteCoverMapOver :
    universalFiniteCoverOver B S hS d ⟶ structureConstantsOver B S hS d :=
  Over.homMk (ObjectProperty.homMk (universalFiniteCoverBaseChangeSnd.{u} S d)) rfl

/-- **Stacks 02KA.** The universal degree-`d` cover over `S` is finite locally free of degree
`d`: it is a base change of the universal cover over the integers, which is finite locally free
of degree `d` by
`AlgebraicGeometry.FiniteFreeAlgebra.isFiniteLocallyFreeOfRank_specCover`. -/
theorem isFiniteLocallyFreeOfRank_universalFiniteCoverMapOver :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map (universalFiniteCoverMapOver B S hS d)) d :=
  let : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (universalFiniteCoverMap.{u} d) d :=
    isFiniteLocallyFreeOfRank_specCover _
  Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
    (IsPullback.of_hasPullback (universalFiniteCoverMap.{u} d)
      (structureConstantsBaseChangeFst.{u} S d))

/-! ### The 1-morphism into `ℋ_d` -/

/-- **The atlas candidate of `ℋ_d`.** The 1-morphism from the category represented by the scheme
of structure constants over `S` into the category `ℋ_d` of degree-`d` finite locally free covers,
sending a point of the scheme of structure constants to the cover its structure constants define.

This is the 1-morphism the source's proof of **Stacks 05YQ** uses for the presentation clause of
Stacks 026O. It is representable by algebraic spaces, by
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_finiteCoverUniversalAtlas`. -/
noncomputable def finiteCoverUniversalAtlas :
    schemeFibredCategory B S hS (structureConstantsOver B S hS d) ⟶
      finiteCoverFibered B S hS d :=
  finiteCoverPointHom (universalFiniteCoverMapOver B S hS d)
    (isFiniteLocallyFreeOfRank_universalFiniteCoverMapOver B S hS d)

end AlgebraicGeometry.Stack

end
