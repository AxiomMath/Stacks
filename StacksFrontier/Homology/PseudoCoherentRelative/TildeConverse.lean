module

public import StacksFrontier.Homology.PseudoCoherent.Local
public import StacksFrontier.Homology.PseudoCoherentRelative.StrictlyPerfectRestrict
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeReflect
public import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherence on an affine scheme: from sheaves to modules

Let `R` be a commutative ring and `M^•` a complex of `R`-modules. This file proves the direction
of Stacks 08E7 which goes from sheaves to modules: if the object `\widetilde{M^•}` of
`D(𝒪_{Spec R})` is `m`-pseudo-coherent (resp. pseudo-coherent) in the sense of Stacks 08CB, then
`M^•` is `m`-pseudo-coherent (resp. pseudo-coherent) as a complex of `R`-modules in the sense of
Stacks 064Q. Together with `Stacks.AffineTilde.isPseudoCoherentFrom_tildeComplex` and
`Stacks.AffineTilde.isPseudoCoherent_tildeComplex` this completes Stacks 08E7.

## Main definitions

* `Stacks.AffineTilde.standardOpen` is `D(g)` as an open subscheme of `Spec R`.
* `Stacks.AffineTilde.localizationAwayHom` is `R ⟶ R_g` as a morphism of `CommRingCat`.
* `Stacks.AffineTilde.localizationAwayQIso` identifies the derived localization of a complex
  with the complex of its localizations.

## Main results

* `Stacks.AffineTilde.isPseudoCoherentFrom_localizationAway_of_approximation`: a strictly perfect
  approximation of `\widetilde{M^•}` over the standard open `D(g)` makes `M^•_g` an
  `m`-pseudo-coherent complex of `R_g`-modules.
* `Stacks.AffineTilde.exists_basicOpen_isPseudoCoherentFrom_localizationAway`: every point of
  `Spec R` has a standard open neighbourhood `D(g)` over which the localization of `M^•` is
  `m`-pseudo-coherent.
* `Stacks.AffineTilde.isPseudoCoherentFrom_of_isPseudoCoherentFrom_tildeComplex` and
  `Stacks.AffineTilde.isPseudoCoherent_of_isPseudoCoherent_tildeComplex`: the two clauses of the
  direction of Stacks 08E7 from sheaves to modules.

## Implementation notes

The source argument is: refine the covering by opens carrying a strictly perfect approximation to
a covering by standard opens, read each approximation on `Spec R_g`, deduce that `M^•_g` is
`m`-pseudo-coherent over `R_g`, and descend by Stacks 066D. Every step but the second is
bookkeeping; the second is where the two formalizations of "the standard open `D(g)`" have to be
matched.

An approximation produced by `AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplexFrom` lives
over the *restricted ringed space* `Spec R | D(g)`, while the affine dictionary
`Stacks.AffineTilde.tildeRestrictIso` speaks about restriction along the open immersion
`Spec (R ⟶ R_g)`, whose source is literally `Spec R_g`. The bridge is Mathlib's
`AlgebraicGeometry.basicOpenIsoSpecAway`, an *isomorphism of schemes* `D(g) ≅ Spec R_g`, and
transporting a strictly perfect approximation along `restrictFunctor` of that isomorphism is
`AlgebraicGeometry.Scheme.Modules.exists_approximation_restrictFunctor`. The composite
identification of complexes is assembled with `have`, never as a named `def` with its type
written out: writing out the instantiated conclusion in this area is what the elaboration time
is spent on, not constructing the term. Split into two `def`s with their types written out, the
same composite takes 43 s over the import baseline; assembled by `have` with its type
inferred, 8 s.

For the same reason the two cohomological conditions are not produced by a `refine` against the
written-out goals of `Stacks.AffineTilde.isPseudoCoherentFrom_of_strictlyPerfect_approximation`,
which exhausts the heartbeat budget, but by
`AlgebraicGeometry.Scheme.Modules.exists_approximation_restrictFunctor`, whose statement keeps
every complex behind a variable.

The ring is `Localization.Away g` rather than `Γ(Spec R, D(g))`, which is what makes the
dictionary's target literally the module `R_g ⊗_R M` that
`StacksDraft.PseudoCoherence.localizationAwayFunctorAux` is built from, so Stacks 066D consumes the
result with no further comparison. The open immersion instance for
`Spec (R ⟶ R_g)` is Mathlib's `AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway`.

Both rings are objects of `CommRingCat`, not types with a `CommRing` instance passed through
`CommRingCat.of`: the typeclasses of `AlgebraicGeometry.tilde.functor` are stated for a variable
`R : CommRingCat`, where the coercion `↑R` has head `CommRingCat.carrier`, while
`↑(CommRingCat.of A)` reduces to `A`, so the discrimination tree reports *no instances* in the
latter spelling.

The refinement of an arbitrary open neighbourhood to a standard one is
`PrimeSpectrum.isBasis_basic_opens`. No quasi-compactness argument is needed to get from the
covering to a finite family generating the unit ideal: were the set of all good `g` to generate a
proper ideal, that ideal would be contained in a maximal one, which as a point of `Spec R` lies
in no `D(g)` with `g` in the set; `Ideal.span_eq_top_iff_finite` then extracts a finite
subfamily, which is what Stacks 066D
(`StacksDraft.PseudoCoherence.isPseudoCoherentFrom_and_isPseudoCoherent_of_localization`) asks
for.

## References

* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 064Q](https://stacks.math.columbia.edu/tag/064Q)
* [Stacks Project, Tag 064U](https://stacks.math.columbia.edu/tag/064U)
* [Stacks Project, Tag 066D](https://stacks.math.columbia.edu/tag/066D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.AffineTilde

open StacksDraft.PseudoCoherence

variable {R : CommRingCat.{u}}

/-! ### The standard open `D(g)` and the localization `R_g` -/

/-- The standard open `D(g)`, as an open subscheme of `Spec R`. The bare
`PrimeSpectrum.basicOpen g` elaborates at `Opens (PrimeSpectrum R)`, which does not carry the
scheme structure that `AlgebraicGeometry.Scheme.Opens.ι` and
`AlgebraicGeometry.RingedSpace.restrictComplex` need. -/
abbrev standardOpen (g : R) : (Spec R).Opens := PrimeSpectrum.basicOpen g

/-- The localization map `R ⟶ R_g`, as a morphism of `CommRingCat`. -/
abbrev localizationAwayHom (g : R) : R ⟶ CommRingCat.of (Localization.Away g) :=
  CommRingCat.ofHom (algebraMap R (Localization.Away g))

/-- The isomorphism `Spec R_g ≅ D(g)` of Mathlib's `AlgebraicGeometry.basicOpenIsoSpecAway`, read
as a factorization of the open immersion `Spec (R ⟶ R_g)` through `D(g)`. -/
theorem basicOpenIsoSpecAway_inv_ι (g : R) :
    (basicOpenIsoSpecAway g).inv ≫ (standardOpen g).ι =
      Spec.map (localizationAwayHom g) := by
  rw [← basicOpenIsoSpecAway_hom_SpecMap g, Iso.inv_hom_id_assoc]

/-- **The derived localization of a complex is the complex of its localizations.** Localization
away from `g` is flat, hence exact, so `StacksDraft.PseudoCoherence.localizationAwayFunctorAux` is
the derived functor of termwise extension of scalars and commutes with the localization functor
`DerivedCategory.Q`.

The four exactness instances are re-established exactly as in the definition of
`StacksDraft.PseudoCoherence.localizationAwayFunctorAux`, so that
`CategoryTheory.Functor.mapDerivedCategoryFactors` applies to the same functor. -/
def localizationAwayQIso (g : R) (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (localizationAwayFunctorAux.{u, u} g).obj (DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u}
        (algebraMap R (Localization.Away g))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap R (Localization.Away g))
  let : F.Additive := extendScalars_additive.{u, u} _
  let : PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.Away g) (Submonoid.powers g)))
  let : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap R (Localization.Away g))).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  exact F.mapDerivedCategoryFactors.app M

/-! ### Reading an approximation over `D(g)` on `Spec R_g` -/

variable (M : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ)

/-- **A strictly perfect approximation over a standard open, read at the level of modules.** If
the restriction of `\widetilde{M^•}` to `D(g)` receives a morphism from a strictly perfect complex
which is an isomorphism on cohomology above `m` and an epimorphism in degree `m`, then the
localization `M^•_g` is an `m`-pseudo-coherent complex of `R_g`-modules.

The approximation is carried along `restrictFunctor` of the isomorphism `Spec R_g ≅ D(g)`, where
it becomes an approximation of the complex associated to `R_g ⊗_R M^•`, and then read back to
modules by `Stacks.AffineTilde.isPseudoCoherentFrom_of_strictlyPerfect_approximation`. -/
theorem isPseudoCoherentFrom_localizationAway_of_approximation (g : R)
    (P : CochainComplex (StrictlyPerfect.OXMod.{u, u}
      ((Spec R).toRingedSpace.restrict (standardOpen g).isOpenEmbedding)) ℤ)
    (hP : StrictlyPerfect.IsStrictlyPerfect P)
    (β : P ⟶ AlgebraicGeometry.RingedSpace.restrictComplex
      (X := (Spec R).toRingedSpace) (tildeComplex M) (standardOpen g))
    (hβ : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j))
    (hβ₀ : Epi (HomologicalComplex.homologyMap β m)) :
    IsPseudoCoherentFrom (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars (localizationAwayHom g).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)) m := by
  have hcomp := AlgebraicGeometry.RingedSpace.restrictComplexIsoRestrictFunctor
      (standardOpen g) (basicOpenIsoSpecAway g).inv (tildeComplex M) ≪≫
    (NatIso.mapHomologicalComplex
      (Scheme.Modules.restrictFunctorCongr (basicOpenIsoSpecAway_inv_ι g))
      (ComplexShape.up ℤ)).app (tildeComplex M) ≪≫
    restrictTildeComplexIso (localizationAwayHom g) M
  obtain ⟨Q, hQ, γ, hγ, hγ₀⟩ := Scheme.Modules.exists_approximation_restrictFunctor
    (basicOpenIsoSpecAway g).inv hcomp m hP β hβ hβ₀
  exact isPseudoCoherentFrom_of_strictlyPerfect_approximation _ m Q hQ γ hγ hγ₀

/-- **Every point of `Spec R` has a standard open neighbourhood over which `M^•` is
`m`-pseudo-coherent.** The definition of `m`-pseudo-coherence of the complex `\widetilde{M^•}`
supplies some open neighbourhood carrying a strictly perfect approximation; shrink it to a
standard open with `PrimeSpectrum.isBasis_basic_opens`, restrict the approximation there with
`AlgebraicGeometry.RingedSpace.exists_restricted_approximation`, and read it at the level of
modules. -/
theorem exists_basicOpen_isPseudoCoherentFrom_localizationAway
    (h : AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplexFrom
      (X := (Spec R).toRingedSpace) (tildeComplex M) m) (x : PrimeSpectrum R) :
    ∃ g : R, x ∈ PrimeSpectrum.basicOpen g ∧
      IsPseudoCoherentFrom ((localizationAwayFunctorAux.{u, u} g).obj
        (DerivedCategory.Q.obj M)) m := by
  obtain ⟨U, hxU, P, hP, α, hα, hα₀⟩ := h x
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hg, hgU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
  obtain ⟨Q, hQ, β, hβ, hβ₀⟩ := AlgebraicGeometry.RingedSpace.exists_restricted_approximation
    (show (standardOpen g) ≤ U from hgU) (tildeComplex M) m P hP α hα hα₀
  exact ⟨g, hg, (isPseudoCoherentFrom_localizationAway_of_approximation M m g Q hQ β hβ hβ₀).ofIso
    (localizationAwayQIso g M).symm⟩

/-! ### Stacks 08E7, the direction from sheaves to modules -/

/-- **Stacks 08E7, the direction from sheaves to modules.** If the object of `D(𝒪_{Spec R})`
determined by a complex `M^•` of `R`-modules is `m`-pseudo-coherent (Stacks 08CB (3)), then `M^•`
is `m`-pseudo-coherent as a complex of `R`-modules (Stacks 064Q (1)).

The standard opens over which the localization of `M^•` is `m`-pseudo-coherent generate the unit
ideal, because every point of `Spec R` lies in one of them; a finite subfamily still does, and
Stacks 066D descends `m`-pseudo-coherence along it. -/
@[stacks 08E7 "m-pseudo-coherent, the direction from sheaves to modules"]
theorem isPseudoCoherentFrom_of_isPseudoCoherentFrom_tildeComplex
    (h : AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom
      (X := (Spec R).toRingedSpace) (DerivedCategory.Q.obj (tildeComplex M)) m) :
    IsPseudoCoherentFrom (DerivedCategory.Q.obj M) m := by
  have key := exists_basicOpen_isPseudoCoherentFrom_localizationAway M m
    (isPseudoCoherentComplexFrom_tildeComplex_of_isPseudoCoherentFrom M m h)
  have hspan : Ideal.span {g : R | IsPseudoCoherentFrom
      ((localizationAwayFunctorAux.{u, u} g).obj (DerivedCategory.Q.obj M)) m} = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨g, hg, hPC⟩ := key ⟨p, hp.isPrime⟩
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hg (hle (Ideal.subset_span hPC))
  obtain ⟨s, hs, hspan'⟩ := (Ideal.span_eq_top_iff_finite _).mp hspan
  exact (isPseudoCoherentFrom_and_isPseudoCoherent_of_localization.{u, u}
    (fun i : s => (i : R)) (by simpa using hspan') (DerivedCategory.Q.obj M) m).1
    fun i => hs i.2

/-- **Stacks 08E7, the direction from sheaves to modules, all degrees at once.** If the object of
`D(𝒪_{Spec R})` determined by a complex `M^•` of `R`-modules is pseudo-coherent (Stacks 08CB (3)),
then `M^•` is pseudo-coherent as a complex of `R`-modules (Stacks 064Q (2)).

Both notions are `m`-pseudo-coherence for every `m` — at the level of sheaves by definition, at
the level of modules by Stacks 064U
(`StacksDraft.PseudoCoherence.pseudoCoherent_iff_all`) — so this is the previous result applied
degree by degree, with the representative the hypothesis supplies serving for all degrees. -/
@[stacks 08E7 "pseudo-coherent, the direction from sheaves to modules"]
theorem isPseudoCoherent_of_isPseudoCoherent_tildeComplex
    (h : AlgebraicGeometry.RingedSpace.IsPseudoCoherent
      (X := (Spec R).toRingedSpace) (DerivedCategory.Q.obj (tildeComplex M))) :
    IsPseudoCoherent (DerivedCategory.Q.obj M) := by
  obtain ⟨K, hK, hKiso⟩ := h
  exact (pseudoCoherent_iff_all (DerivedCategory.Q.obj M)).2 fun n =>
    isPseudoCoherentFrom_of_isPseudoCoherentFrom_tildeComplex M n ⟨K, hK n, hKiso⟩

end Stacks.AffineTilde

end
