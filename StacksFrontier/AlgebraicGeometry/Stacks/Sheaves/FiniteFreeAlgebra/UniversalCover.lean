module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.Spectrum
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.StructureConstantsSpace

/-!
# The universal degree-`d` cover

The scheme `X` of structure constants of **Stacks 05YM** carries a tautological free
`d`-dimensional algebra structure over its own global sections, namely the one classified by the
identity morphism `X ⟶ X`. Its spectrum is a scheme `Z` which is finite locally free of degree
`d` over `X`, and every point `x : T ⟶ X` recovers the structure it classifies by extending the
scalars of the tautological one along `x`. This is the universal degree-`d` cover.

The universal cover also lies in every big fppf site, because its coordinate ring is `d` copies
of the countable coordinate ring of `X`; so after base change to a scheme `S` it is an object of
the big fppf site over `S`, finite locally free of degree `d` over `X_S`.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.universalStructure`: the tautological free
  `d`-dimensional algebra structure over `Γ(X, 𝒪_X)`.
* `AlgebraicGeometry.FiniteFreeAlgebra.universalCoverHom`: its spectrum, as a scheme over `X`
  rather than over `Spec Γ(X, 𝒪_X)`.
* `AlgebraicGeometry.FiniteFreeAlgebra.universalCoverBaseChange`: the base change of that
  spectrum to the scheme `X_S` of structure constants over `S`.
* `AlgebraicGeometry.Space.universalCoverSiteObject` and
  `AlgebraicGeometry.Space.universalCoverSiteHom`: the base change read as an object of the big
  fppf site over `S`, together with its structure morphism to
  `AlgebraicGeometry.Space.structureConstantsSiteObject`.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.map_universalStructure`: extending the scalars of the
  tautological structure along a point `x : T ⟶ X` gives the structure that `x` classifies.
* `AlgebraicGeometry.FiniteFreeAlgebra.isFiniteLocallyFreeOfRank_universalCoverHom`: the
  universal cover is finite locally free of degree `d` over `X`.
* `AlgebraicGeometry.Space.contains_universalCover` and
  `AlgebraicGeometry.Space.contains_universalCoverBaseChange`: the universal cover and its base
  change lie in every big fppf site.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_universalCoverSiteHom`: the structure
  morphism of the site object is finite locally free of degree `d`.

## References

* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable (d : ℕ) [NeZero d]

/-- The tautological free `d`-dimensional algebra structure over the global sections of the
scheme `X` of structure constants: the one classified by the identity morphism of `X`. -/
noncomputable def universalStructure : FiniteFreeAlgebra Γ(scheme.{u} d, ⊤) d :=
  (representation.{u} d).equiv (scheme.{u} d) (𝟙 _)

/-- Extending the scalars of the tautological structure along a point `x : T ⟶ X` gives the free
`d`-dimensional algebra structure over `Γ(T, 𝒪_T)` that `x` classifies. -/
theorem map_universalStructure {T : Scheme.{u}} (x : T ⟶ scheme.{u} d) :
    FiniteFreeAlgebra.map x.appTop.hom (universalStructure.{u} d) =
      (representation.{u} d).equiv T x := by
  rw [universalStructure, (representation.{u} d).naturality x (𝟙 _), Category.comp_id]

/-- The universal degree-`d` cover: the spectrum of the algebra of the tautological structure,
as a scheme over the scheme `X` of structure constants. -/
noncomputable def universalCoverHom :
    (specCover (universalStructure.{u} d)).left ⟶ scheme.{u} d :=
  (specCover (universalStructure.{u} d)).hom ≫ (scheme.{u} d).isoSpec.inv

/-- The universal degree-`d` cover is finite locally free of degree `d` over the scheme of
structure constants. -/
theorem isFiniteLocallyFreeOfRank_universalCoverHom :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (universalCoverHom.{u} d) d :=
  Stacks.Morphisms.isFiniteLocallyFreeOfRank_postcomp (scheme.{u} d).isoSpec.symm _
    (isFiniteLocallyFreeOfRank_specCover _)

/-- The global sections of the scheme of structure constants form a countable ring. -/
instance countable_universalSections : Countable ↥Γ(scheme.{u} d, ⊤) := by
  have hpoly : Countable (MvPolynomial (CoeffIndex d) ℤ) := by
    refine Cardinal.mk_le_aleph0_iff.mp ?_
    refine (MvPolynomial.cardinalMk_le_max (σ := CoeffIndex d) (R := ℤ)).trans ?_
    exact max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl
  have huniv : Countable (universalRing d) := Ideal.Quotient.mk_surjective.countable
  exact Countable.of_equiv _
    (Scheme.ΓSpecIso
      (CommRingCat.of (ULift.{u} (universalRing d)))).commRingCatIsoToRingEquiv.symm.toEquiv

/-- The projection of the scheme `X_S` of structure constants over `S` to the scheme `X` of
structure constants over the integers. -/
noncomputable abbrev structureConstantsProj (S : Scheme.{u}) :
    (structureConstantsBaseChange.{u} d S).left ⟶ scheme.{u} d :=
  pullback.fst (specULiftZIsTerminal.from (scheme.{u} d)) (specULiftZIsTerminal.from S)

/-- The base change of the universal degree-`d` cover to the scheme `X_S` of structure constants
over a scheme `S`. -/
noncomputable abbrev universalCoverBaseChange (S : Scheme.{u}) : Scheme.{u} :=
  pullback (universalCoverHom.{u} d) (structureConstantsProj.{u} d S)

end AlgebraicGeometry.FiniteFreeAlgebra

namespace AlgebraicGeometry.Space

open AlgebraicGeometry.FiniteFreeAlgebra

/-- The universal degree-`d` cover belongs to every big fppf site. -/
theorem contains_universalCover (𝒞 : BigFppfSite.{u}) (d : ℕ) [NeZero d] :
    𝒞.Contains (specCover (universalStructure.{u} d)).left := by
  have : Countable (Carrier (universalStructure.{u} d)) :=
    Countable.of_equiv _ (Carrier.coordLinearEquiv (universalStructure.{u} d)).toEquiv.symm
  change (Spec (CommRingCat.of (Carrier (universalStructure.{u} d)))).size < 𝒞.cutoff
  rw [Scheme.size_Spec]
  exact max_lt 𝒞.aleph0_lt_cutoff (Cardinal.mk_le_aleph0.trans_lt 𝒞.aleph0_lt_cutoff)

/-- The base change of the universal degree-`d` cover to `X_S` belongs to the big fppf site of
`S`. -/
theorem contains_universalCoverBaseChange (𝒞 : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : 𝒞.Contains S) (d : ℕ) [NeZero d] :
    𝒞.Contains (universalCoverBaseChange.{u} d S) :=
  Scheme.size_pullback_lt _ _ (contains_universalCover 𝒞 d)
    (contains_structureConstantsBaseChange 𝒞 S d hS)

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S) (d : ℕ) [NeZero d]

/-- The base change of the universal degree-`d` cover to `X_S`, read as an object of the big
fppf site over `S`. -/
noncomputable def universalCoverSiteObject : BigFppfOver 𝒞 S hS :=
  siteObject 𝒞 S hS (contains_universalCoverBaseChange 𝒞 S hS d)
    (pullback.snd (universalCoverHom.{u} d) (structureConstantsProj.{u} d S) ≫
      (structureConstantsBaseChange.{u} d S).hom)

/-- The structure morphism of the universal degree-`d` cover over the scheme of structure
constants, as a morphism of the big fppf site over `S`. -/
noncomputable def universalCoverSiteHom :
    universalCoverSiteObject 𝒞 S hS d ⟶ structureConstantsSiteObject 𝒞 S hS d :=
  Over.homMk (ObjectProperty.homMk
    (pullback.snd (universalCoverHom.{u} d) (structureConstantsProj.{u} d S))) rfl

/-- The morphism of schemes underlying
`AlgebraicGeometry.Space.universalCoverSiteHom` is the base-change projection. -/
theorem toScheme_map_universalCoverSiteHom :
    (BigFppfOver.toScheme 𝒞 S hS).map (universalCoverSiteHom 𝒞 S hS d) =
      pullback.snd (universalCoverHom.{u} d) (structureConstantsProj.{u} d S) := rfl

/-- The universal degree-`d` cover is finite locally free of degree `d` over the scheme of
structure constants, as a morphism of the big fppf site over `S`. -/
theorem isFiniteLocallyFreeOfRank_universalCoverSiteHom :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme 𝒞 S hS).map (universalCoverSiteHom 𝒞 S hS d)) d :=
  have := isFiniteLocallyFreeOfRank_universalCoverHom.{u} d
  Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
    (IsPullback.of_hasPullback (universalCoverHom.{u} d) (structureConstantsProj.{u} d S))

end AlgebraicGeometry.Space

end
